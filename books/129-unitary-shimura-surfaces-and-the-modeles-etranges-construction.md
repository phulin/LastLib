# Unitary Shimura Surfaces and the Modèles Étranges Construction

## Contents

- [1. Why a surface enters a rank-two problem](#1-why-a-surface-enters-a-rank-two-problem)
  - [1.1 The parity obstruction](#11-the-parity-obstruction)
  - [1.2 What “strange” means](#12-what-strange-means)
  - [1.3 Conventions and inherited results](#13-conventions-and-inherited-results)
- [2. The global unitary datum](#2-the-global-unitary-datum)
  - [2.1 CM extensions and Hermitian planes](#21-cm-extensions-and-hermitian-planes)
  - [2.2 Signatures and the two active places](#22-signatures-and-the-two-active-places)
  - [2.3 Local invariants and globalization](#23-local-invariants-and-globalization)
  - [2.4 Anisotropy and compactness](#24-anisotropy-and-compactness)
- [3. The similitude group and its Shimura datum](#3-the-similitude-group-and-its-shimura-datum)
  - [3.1 The common rational multiplier](#31-the-common-rational-multiplier)
  - [3.2 The Hodge homomorphism](#32-the-hodge-homomorphism)
  - [3.3 Verification of the Shimura axioms](#33-verification-of-the-shimura-axioms)
  - [3.4 Dimension, reflex field, and compactness](#34-dimension-reflex-field-and-compactness)
- [4. The strange algebra with involution](#4-the-strange-algebra-with-involution)
  - [4.1 From a quaternion algebra to a unitary algebra](#41-from-a-quaternion-algebra-to-a-unitary-algebra)
  - [4.2 Twisting the involution](#42-twisting-the-involution)
  - [4.3 Recovering the required inner form](#43-recovering-the-required-inner-form)
  - [4.4 The exact matching hypothesis](#44-the-exact-matching-hypothesis)
- [5. A polarized weight-one realization](#5-a-polarized-weight-one-realization)
  - [5.1 The alternating trace form](#51-the-alternating-trace-form)
  - [5.2 Positivity and Hodge type](#52-positivity-and-hodge-type)
  - [5.3 Parity repair and auxiliary factors](#53-parity-repair-and-auxiliary-factors)
  - [5.4 PEL realizability](#54-pel-realizability)
- [6. Integral PEL data and the moduli problem](#6-integral-pel-data-and-the-moduli-problem)
  - [6.1 Orders, lattices, and the good base](#61-orders-lattices-and-the-good-base)
  - [6.2 Objects and arrows](#62-objects-and-arrows)
  - [6.3 Polarizations and Rosati compatibility](#63-polarizations-and-rosati-compatibility)
  - [6.4 Prime-to-bad level](#64-prime-to-bad-level)
- [7. The determinant and signature conditions](#7-the-determinant-and-signature-conditions)
  - [7.1 The universal polynomial law](#71-the-universal-polynomial-law)
  - [7.2 The rank-two formula](#72-the-rank-two-formula)
  - [7.3 Closedness and base change](#73-closedness-and-base-change)
  - [7.4 Orientation and failure at bad primes](#74-orientation-and-failure-at-bad-primes)
- [8. Descent, inertia, and representability](#8-descent-inertia-and-representability)
  - [8.1 Why the moduli problem is a stack](#81-why-the-moduli-problem-is-a-stack)
  - [8.2 Finiteness of isomorphisms](#82-finiteness-of-isomorphisms)
  - [8.3 Killing automorphisms](#83-killing-automorphisms)
  - [8.4 The fine moduli scheme](#84-the-fine-moduli-scheme)
- [9. The local model of the surface](#9-the-local-model-of-the-surface)
  - [9.1 Lifting the Hodge filtration](#91-lifting-the-hodge-filtration)
  - [9.2 Two moving lines](#92-two-moving-lines)
  - [9.3 Smoothness and dimension two](#93-smoothness-and-dimension-two)
  - [9.4 Cotangent and determinant lines](#94-cotangent-and-determinant-lines)
- [10. Complex uniformization and the canonical surface](#10-complex-uniformization-and-the-canonical-surface)
  - [10.1 From PEL objects to lattices](#101-from-pel-objects-to-lattices)
  - [10.2 The double quotient](#102-the-double-quotient)
  - [10.3 Comparison with the canonical model](#103-comparison-with-the-canonical-model)
  - [10.4 Projectivity](#104-projectivity)
- [11. The modèles étranges comparison](#11-the-modeles-etranges-comparison)
  - [11.1 Finite-adelic matching](#111-finite-adelic-matching)
  - [11.2 Central quotients and finite fibers](#112-central-quotients-and-finite-fibers)
  - [11.3 Why the auxiliary abelian variety is not the automorphic object](#113-why-the-auxiliary-abelian-variety-is-not-the-automorphic-object)
  - [11.4 Independence of auxiliary choices](#114-independence-of-auxiliary-choices)
- [12. Connected components and canonical descent](#12-connected-components-and-canonical-descent)
  - [12.1 The exact component set](#121-the-exact-component-set)
  - [12.2 Reciprocity on components](#122-reciprocity-on-components)
  - [12.3 Fields of definition of individual components](#123-fields-of-definition-of-individual-components)
  - [12.4 Selecting the required union](#124-selecting-the-required-union)
- [13. Levels, universal families, and Hecke maps](#13-levels-universal-families-and-hecke-maps)
  - [13.1 Fine and coarse levels](#131-fine-and-coarse-levels)
  - [13.2 The universal abelian scheme](#132-the-universal-abelian-scheme)
  - [13.3 Hecke isogenies](#133-hecke-isogenies)
  - [13.4 Descent of correspondences](#134-descent-of-correspondences)
- [14. The cohomological role of the surface](#14-the-cohomological-role-of-the-surface)
  - [14.1 Why degree two is the middle degree](#141-why-degree-two-is-the-middle-degree)
  - [14.2 The Künneth sign and automorphic parity](#142-the-kunneth-sign-and-automorphic-parity)
  - [14.3 What geometry supplies and what remains](#143-what-geometry-supplies-and-what-remains)
- [15. Construction theorem and hypothesis ledger](#15-construction-theorem-and-hypothesis-ledger)
  - [15.1 The complete construction theorem](#151-the-complete-construction-theorem)
  - [15.2 Exact hypotheses and failure modes](#152-exact-hypotheses-and-failure-modes)
  - [15.3 Conclusion](#153-conclusion)

## 1. Why a surface enters a rank-two problem

The automorphic representations that motivate this book are rank two, but the algebraic variety on which they are most naturally realized need not be a curve. The dimension of a Shimura variety is controlled by its noncompact real factors, whereas the parity and rationality of a symplectic realization are controlled by a different calculation. When those two calculations disagree, insisting on a curve obscures the arithmetic. The remedy is a compact unitary surface together with an auxiliary abelian scheme whose endomorphisms and polarization encode the desired group.

### 1.1 The parity obstruction

Let $F$ be totally real. A quaternionic datum is specified at infinity by the set of real places where its adjoint group is split. One split place gives a curve. Tensor induction of the standard two-dimensional representations, however, carries the tensor product of alternating forms. If $d$ factors occur, interchanging its arguments contributes $(-1)^d$. Thus the tensor form is alternating for odd $d$ and symmetric for even $d$.

This sign cannot be corrected by terminology. A polarized abelian variety requires an alternating rational form. One may enlarge the representation hyperbolically, change the central group, or pass to a unitary PEL datum. The last alternative has an additional advantage: two real places of signature $(1,1)$ produce a surface, and its middle cohomology has even degree. The geometric degree then matches the automorphic parity that a curve fails to accommodate.

### 1.2 What “strange” means

The **modèles étranges construction** is not a claim that two visibly different moduli problems are identical. It is a controlled replacement of a quaternionic inner form by an auxiliary algebra with an involution of the second kind. The replacement has four features:

1. its derived group has the prescribed rank-one local inner forms at the finite places relevant to Hecke theory;
2. its archimedean signatures have exactly two noncompact factors;
3. its rational representation is of polarized weight one and hence admits a PEL moduli interpretation;
4. central kernels, component classes, and auxiliary torus characters are retained rather than suppressed.

The adjective “strange” records the fact that the abelian variety in the moduli problem is an auxiliary linearizing device. Its dimension can be much larger than two and is not the dimension of the Shimura variety. The desired rank-two automorphic system is recovered through the acting group and its Hecke algebra, not by pretending that the universal abelian variety itself is a surface.

### 1.3 Conventions and inherited results

All fields have characteristic zero. Let $F$ be a totally real field and let $K/F$ be a CM quadratic extension with conjugation $c$. We use arithmetic Artin reciprocity, so a uniformizer maps to arithmetic Frobenius. Our complex double quotient is

$$
G(mathbf Q)\backslash\bigl(X\times G(\mathbf A_f)/C\bigr),       \tag{1.1}
$$

and reciprocity acts by left multiplication on the finite adelic coordinate. We write $C$ for a compact open level, reserving $K$ for the CM field.

The dependency boundary is precise. Book 14 supplies stacks, PEL determinant conditions, rigid level, and coarse quotients. Book 17 supplies cotangent-complex and determinant-line criteria. Book 38 supplies abelian quotients, polarizations, Weil pairings, and isotropic descent. Book 123 supplies inner forms, corestriction, involutions, tensor parity, and symplectic repair. Book 126 supplies the unitary Shimura datum, reflex field, canonical model, reciprocity normalization, and the corrected full-torus component convention. Book 127 supplies the PEL stack, fine representability, Hodge-filtration deformation theorem, and universal family. We use those results with their stated hypotheses and recall their operative forms where they enter. We do not assume that a proposed unitary PEL functor has the desired group; that is the centralizer calculation of Chapters 4 and 5. Nor do we assume that the multiplier alone computes components; Chapter 12 uses the full maximal torus quotient.

## 2. The global unitary datum

The first task is arithmetic rather than moduli-theoretic. We must choose a Hermitian plane whose signatures give two complex directions, whose finite invariants match the desired inner form, and which is anisotropic over $F$. These requirements interact through a global product formula.

### 2.1 CM extensions and Hermitian planes

A Hermitian plane is a two-dimensional $K$-vector space $W$ with a nondegenerate form

$$
\langle ax,by\rangle=a\langle x,y\rangle c(b).                    \tag{2.1}
$$

At a real place $v$ of $F$, $K\otimes_{F,v}\mathbf R\simeq\mathbf C$, and (2.1) has a signature $(p_v,q_v)$ with $p_v+q_v=2$. At a finite place, isomorphism classes are distinguished by dimension, determinant modulo norms, and, at the exceptional dyadic places, the corresponding local Hermitian invariant. In dimension two it is convenient to retain the invariant abstractly rather than force a diagonal formula that changes normalization at $2$.

The determinant class is

$$
\det(W_v)\in F_v^\times/N_{K_v/F_v}(K_v^\times).                 \tag{2.2}
$$

Scaling the form by $a\in F^\times$ does not change its unitary group, but it multiplies the determinant by $a^2$, hence leaves (2.2) unchanged. This explains why the group remembers less than a chosen matrix of the form.

### 2.2 Signatures and the two active places

Choose two distinct real places $v_1,v_2$ and impose

$$
(p_v,q_v)=
\begin{cases}
(1,1),&v=v_1,v_2,\\
(2,0)\text{ or }(0,2),&v\ne v_1,v_2.
\end{cases}                                                        \tag{2.3}
$$

The two indefinite factors will each contribute a complex one-ball. Definite places contribute no tangent direction, but their orientations remain part of the Hodge cocharacter. In particular, changing $(2,0)$ to $(0,2)$ can change the reflex field even though it does not change the dimension.

For each embedding $\varphi:K\hookrightarrow\mathbf C$ above $v$, set

$$
r_\varphi=p_v,\qquad r_{c\varphi}=q_v.                            \tag{2.4}
$$

The entire function $r$, not merely the set $\{v_1,v_2\}$, is part of the datum.

### 2.3 Local invariants and globalization

Prescribing (2.3) and arbitrary finite invariants independently may be impossible. Hermitian local invariants satisfy one product relation. We use the following form of the local-global classification.

**Theorem 2.1 (globalization of a Hermitian plane).** Suppose a nondegenerate two-dimensional Hermitian space $W_v$ over $K_v/F_v$ is specified for every place $v$ of $F$, with the standard split choice at all but finitely many finite places. A global Hermitian plane $W$ inducing these local spaces exists if and only if the determinant classes come from one global class in

$$
F^\times/N_{K/F}(K^\times)
$$

and the local signs satisfy the single product relation. When it exists, $W$ is unique up to $K$-linear isometry.

**Proof strategy.** Diagonalize locally, reduce the first coefficient to $1$, and interpret the second as a norm-class. Approximation globalizes the class; the product relation is exactly the obstruction to simultaneously choosing all local norm representatives.

**Proof.** Every local Hermitian plane is diagonalizable, so after scaling it is represented by $\operatorname{diag}(1,-a_v)$ with $a_v\in F_v^\times$. Replacing the second basis vector multiplies $a_v$ by a local norm. Thus its isometry class is the norm-class of $a_v$, together with the real signature convention. Necessity follows from a global diagonalization: a global coefficient has compatible local images, and the product formula for the quadratic norm character makes the product of local signs equal to one.

Conversely, choose a finite set containing the nonsplit specifications and all archimedean places. Weak approximation gives $a\in F^\times$ with prescribed square and sign neighborhoods. The quotient between $a$ and $a_v$ is a local norm at the chosen places. Away from them, the obstruction is a finite collection of values of the quadratic norm character. The product relation makes the last value dependent on the others, so multiplication by a further global element chosen by approximation kills all remaining discrepancies. Then $\operatorname{diag}(1,-a)$ has the prescribed localizations. Two global spaces with the same localizations have quotient determinant a local norm everywhere; the norm theorem for the cyclic extension $K/F$ makes it a global norm, giving an isometry. $\square$

The theorem is a construction protocol. After fixing (2.3), we are free to alter one finite invariant to satisfy the product relation. That place must then be included in the bad set of the integral datum.

For a concrete model choose $a\in F^\times$ and put

$$
W=K^2,\qquad
\langle x,y\rangle=x_1c(y_1)-a x_2c(y_2).                         \tag{2.5}
$$

At a real place this form is indefinite exactly when $a$ is positive. Approximation can therefore impose (2.3). At an inert finite place it is isotropic exactly when $a$ is a local norm. Requiring $a$ to be a non-norm at one such place forces global anisotropy: an isotropic vector with $x_2\ne0$ would give $a=N_{K/F}(x_1/x_2)$, and $x_2=0$ forces $x_1=0$. Thus real isotropy at two places and global anisotropy coexist naturally.

If $K_v\simeq F_v\times F_v$, every class is a norm and this device cannot create anisotropy. At dyadic places the rational classification remains valid, but integral self-dual lattices may have several genera. This affects the integral datum, not the rational surface, and explains why dyadic places belong to the bad set.

### 2.4 Anisotropy and compactness

The surface is compact only when $W$ has no nonzero isotropic vector over $K$. Real indefiniteness does not contradict global anisotropy: a vector may exist over each of two completions without existing over $F$.

**Proposition 2.2.** The following are equivalent:

1. $W$ is isotropic over $F$;
2. the special unitary group $\operatorname{SU}(W)$ has a proper $F$-parabolic subgroup;
3. the projective unitary group has a rational boundary component.

**Proof.** An isotropic line $L\subset W$ is stabilized by a proper parabolic. Conversely, a proper parabolic of a rank-one unitary group stabilizes a flag, necessarily an isotropic line. Rational boundary components of the associated Hermitian domain are precisely rational parabolics. $\square$

Thus choosing one finite localization anisotropic can force global anisotropy. Proposition 2.2 will later turn this algebraic condition into projectivity of the Shimura surface.

## 3. The similitude group and its Shimura datum

The Hermitian plane produces several groups: the unitary group, the special unitary group, and a rational similitude group. The last is the correct group for polarized abelian varieties because a polarization is allowed one common rational multiplier.

### 3.1 The common rational multiplier

Define the $\mathbf Q$-group $G$ by

$$
G(R)=\left\{g\in\operatorname{GL}_{K\otimes R}(W\otimes R):
\langle gx,gy\rangle=\nu(g)\langle x,y\rangle,
\ \nu(g)\in R^\times\right\}.                                  \tag{3.1}
$$

The word “rational” is essential: allowing a multiplier in $(F\otimes R)^\times$ defines a larger restriction-of-scalars group. Taking determinants over $K$ gives

$$
N_{K/F}(\det_Kg)=\nu(g)^2.                                       \tag{3.2}
$$

Consequently neither $\nu$ nor $\det_K$ alone records the abelianization.

After base change to an algebraic closure, $G$ becomes a product of general linear groups subject to one common multiplier relation. Hence it is connected and reductive. Its derived group is

$$
G^{\mathrm{der}}=\operatorname{Res}_{F/\mathbf Q}\operatorname{SU}(W), \tag{3.3}
$$

which is simply connected of type $A_1$.

### 3.2 The Hodge homomorphism

At each real place, choose a negative $q_v$-plane $L_v\subset W_v\otimes\mathbf C$. Let $z\in\mathbf C^\times=\mathbb S(\mathbf R)$ act by $z$ on $L_v$ and by $\bar z$ on its orthogonal complement, with the common central normalization chosen so that the weight is $-1$. This defines

$$
h:\mathbb S\longrightarrow G_{\mathbf R}.                        \tag{3.4}
$$

The conjugacy class $X$ consists of all such choices. Its connected component is

$$
X^+=\mathcal D_{v_1}\times\mathcal D_{v_2},                       \tag{3.5}
$$

where each $\mathcal D_{v_i}$ is the unit disk, equivalently the upper half-plane. Definite factors contribute a point.

### 3.3 Verification of the Shimura axioms

**Proposition 3.1.** If every rational simple adjoint factor is nontrivial at one of $v_1,v_2$, then $(G,X)$ is a Shimura datum.

**Proof.** On $W_{\mathbf C}$, (3.4) has only Hodge types $(-1,0)$ and $(0,-1)$. On $\operatorname{Lie}G_{\mathbf C}\subset\operatorname{End}(W_{\mathbf C})$, maps preserving the two summands have type $(0,0)$ and maps between them have types $(-1,1)$ and $(1,-1)$. This proves the allowed adjoint types.

Conjugation by $h(i)$ fixes the block-diagonal maximal compact subgroup and negates the noncompact tangent directions. It is therefore a Cartan involution on the adjoint real group. Finally, the hypothesis excludes a rational simple factor on which $h$ is central. These are exactly the three Shimura axioms. $\square$

The holomorphic tangent space at $h$ is

$$
\bigoplus_v\operatorname{Hom}(L_v,L_v^\perp),                    \tag{3.6}
$$

so its dimension is $\sum_vp_vq_v=2$.

### 3.4 Dimension, reflex field, and compactness

Let $E$ be the fixed field of

$$
\{\sigma\in\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q):
r_{\sigma\varphi}=r_\varphi\text{ for all }\varphi\}.          \tag{3.7}
$$

**Proposition 3.2.** The reflex field of $(G,X)$ is $E$, the domain has complex dimension two, and if $W$ is anisotropic over $F$, every arithmetic quotient at finite level is compact.

**Proof.** Over $\mathbf C$, the Hodge cocharacter on the factor indexed by $\varphi$ has $r_\varphi$ entries of weight one and $2-r_\varphi$ of weight zero. Two cocharacters are conjugate precisely when all multiplicities agree, proving (3.7). Formula (3.6) proves the dimension. If the quotient were noncompact, reduction theory would produce a rational boundary component and hence a proper rational parabolic. Proposition 2.2 excludes one. $\square$

Notice that $E$ need not be $\mathbf Q$ and need not equal $K$. Definite orientations can enlarge it. Any descent statement that names a smaller field without checking (3.7) is false.

## 4. The strange algebra with involution

We now connect the unitary surface to quaternionic automorphic data. The connection is local and group-theoretic before it is cohomological. It is built from a quaternion algebra and a CM scalar extension equipped with an involution of the second kind.

### 4.1 From a quaternion algebra to a unitary algebra

Let $B/F$ be a quaternion algebra representing the desired rank-one inner form. Put

$$
D=B\otimes_FK.                                                     \tag{4.1}
$$

Let $b\mapsto\bar b$ be canonical quaternion conjugation. The map

$$
b\otimes a\longmapsto\bar b\otimes c(a)                          \tag{4.2}
$$

is an involution of the second kind: it reverses multiplication and induces $c$ on the center $K$. Depending on the desired real signatures, (4.2) may not be positive in the required sense. We therefore allow an inner twist.

### 4.2 Twisting the involution

Choose $\delta\in D^\times$ with $\delta^{\dagger}=\delta$, where $\dagger$ denotes (4.2), and define

$$
x^*=\delta^{-1}x^{\dagger}\delta.                                \tag{4.3}
$$

Then $*$ is again an involution precisely when $\delta^\dagger=\lambda\delta$ for a central scalar $\lambda$ with $\lambda c(\lambda)=1$; Hilbert 90 permits rescaling to the displayed self-adjoint normalization. Locally, diagonalizing $\delta$ changes the signature of the corresponding Hermitian form. Thus (4.3) is the mechanism that arranges (2.3).

An involution is not determined by its signatures alone. Its finite discriminants must match the local invariants selected in Chapter 2. The product relation for involutions is the same global compatibility already enforced there.

### 4.3 Recovering the required inner form

Let $V$ be a faithful left $D$-module and let $H$ be the connected group of $D$-linear similitudes of a nondegenerate $*$-Hermitian or $*$-skew-Hermitian form on $V$. Over a splitting field, the double-centralizer theorem writes

$$
\operatorname{End}_K(V)\simeq D\otimes_KD',                     \tag{4.4}
$$

where $D'$ is the commuting central simple algebra. The derived group of $H$ is the norm-one group attached to $D'$. Therefore it is the commutant, not the prescribed endomorphism algebra itself, that supplies the automorphic group.

In degree two, all simply connected inner forms of $\operatorname{SL}_2$ arise as norm-one groups of quaternion algebras. At a finite place $v$, equality of the local Brauer invariants of $D'_v$ and $B_v$ gives

$$
H^{\mathrm{der}}(F_v)\simeq B_v^1.                               \tag{4.5}
$$

Modulo centers this identifies their adjoint groups. Equation (4.5) is the finite-place heart of the strange construction.

### 4.4 The exact matching hypothesis

It is unsafe to claim that (4.1) automatically gives (4.5). We isolate the necessary condition.

**Definition 4.1.** A **strange realization** of the quaternionic datum $B/F$ is a tuple

$$
\mathfrak S=(K,D,*,V,\Phi,h)
$$

such that:

1. $K/F$ is CM and $D$ is a semisimple $K$-algebra with positive involution $*$ of the second kind;
2. $V$ is a faithful left $D$-module and $\Phi$ is a nondegenerate $*$-compatible form;
3. the connected rational similitude group $H$ has the Hodge map and signatures (2.3);
4. for every finite place in the prescribed Hecke set, an explicit central isogeny identifies $H^{\mathrm{der}}_{F_v}$ with $B_v^1$;
5. outside a finite set the identifications carry the chosen hyperspecial subgroups to one another;
6. the rational multiplier and the finite central kernel are specified.

This is an auditable hypothesis, not a tautology. Corestriction and local invariant calculations provide such tuples in the FLT cases: transferred Brauer classes determine the commutant, and one adjustable finite invariant enforces the global product relation.

**Proposition 4.2.** Given prescribed local rank-one inner forms at finitely many places and signatures (2.3), a strange realization exists whenever their Brauer and Hermitian invariants satisfy the two global product relations and the intended symplectic representation has been made alternating.

**Proof strategy.** Globalize the algebra, globalize the involution, then construct its module and form. The two product relations are the only reciprocity obstructions.

**Proof.** The local quaternion invariants, each $0$ or $1/2$, sum to zero exactly when they define a global quaternion Brauer class. Corestriction transfers this class to the desired commutant class. Theorem 2.1 globalizes the involution with its real signatures after one finite invariant is adjusted. A central simple algebra is a matrix algebra over its division representative, so it has a minimal module; Morita theory transfers the involution to a Hermitian or skew-Hermitian form on that module. If the resulting rational bilinear form is symmetric, the hyperbolic construction of Section 5.3 makes it alternating without changing the derived adjoint group. The local double-centralizer calculation then gives the specified groups and integral hyperspecials away from the finite discriminant set. $\square$

The local calculation is explicit. If $D_v\simeq M_2(K_v)$, write

$$
x^*=J^{-1}c(x)^{\mathsf t}J                                      \tag{4.6}
$$

for a Hermitian matrix $J$. Morita equivalence transfers this involution to a binary Hermitian form $H$ on the multiplicity space. Its adjoint similitudes satisfy

$$
g^{\star}Hg=\nu(g)H.                                              \tag{4.7}
$$

If $H$ is isotropic, the derived group is $\operatorname{SL}_2(F_v)$; if $H$ is anisotropic, it is the norm-one group of the quaternion division algebra over $F_v$. Indeed its adjoint algebra acts on its three-dimensional trace-zero subspace, whose norm quadratic form is split exactly when $H$ has an isotropic line. Thus local matching reduces to checking that $H$ is isotropic precisely where $B_v$ is split.

Corestriction makes the parity visible. For $F/F_0$ and $v$ a place of $F_0$,

$$
\operatorname{inv}_v\operatorname{Cor}_{F/F_0}(B)
=\sum_{w\mid v}\operatorname{inv}_w(B).                           \tag{4.8}
$$

The transferred algebra is split exactly when an even number of ramified $w$ lie above $v$. If exactly one lies above some $v$, a claimed split tensor module cannot exist there; one must use a module over the division representative or enlarge the realization. This obstruction changes the auxiliary endomorphism algebra and cannot be removed by notation.

## 5. A polarized weight-one realization

A PEL moduli problem requires more than a unitary group. It requires an alternating form, an adjoint involution, positivity, and a weight-one Hodge structure. This chapter constructs those tensors and records the parity repair explicitly.

### 5.1 The alternating trace form

Suppose first that $V$ carries a $K/F$-Hermitian form $\Phi$. Choose $\alpha\in K^\times$ with $c(\alpha)=-\alpha$ and define on the underlying $\mathbf Q$-space

$$
\psi(x,y)=\operatorname{Tr}_{K/\mathbf Q}\bigl(\alpha\Phi(x,y)\bigr). \tag{5.1}
$$

**Proposition 5.1.** The form $\psi$ is alternating and nondegenerate. If $d\in D$, then

$$
\psi(dx,y)=\psi(x,d^*y).                                         \tag{5.2}
$$

A similitude of $\Phi$ with rational multiplier $\nu$ is a symplectic similitude of $\psi$ with the same multiplier.

**Proof.** Hermitian symmetry gives $\Phi(y,x)=c(\Phi(x,y))$. Since $c(\alpha)=-\alpha$ and the field trace is invariant under $c$,

$$
\psi(y,x)=\operatorname{Tr}(\alpha c(\Phi(x,y)))
=\operatorname{Tr}(c(\alpha)\Phi(x,y))=-\psi(x,y).
$$

Characteristic zero turns skew-symmetry into alternation. If $x$ pairs to zero with every $y$, nondegeneracy of the trace pairing and of $\Phi$ forces $x=0$. Equation (5.2) follows from $*$-compatibility of $\Phi$. Finally, a rational scalar pulls through the trace, proving the multiplier assertion. $\square$

The rationality of $\nu$ is essential. An $F$-valued multiplier cannot in general be extracted from $\operatorname{Tr}_{K/\mathbf Q}$ as a single rational scalar.

### 5.2 Positivity and Hodge type

For $h\in X$, set

$$
(x,y)_h=\psi(x,h(i)y).                                            \tag{5.3}
$$

The signs of $\alpha$ at the CM embeddings and the orientations in (2.3) are chosen so that (5.3) is symmetric positive definite. Then $h$ makes $V$ a polarized rational Hodge structure of types $(-1,0)$ and $(0,-1)$. The quotient

$$
A_h=V_{\mathbf R}/(h(i)-i)V_{\mathbf R}+\Lambda                 \tag{5.4}
$$

for a compatible lattice $\Lambda$ is a complex abelian variety. More invariantly, the Hodge filtration and lattice define the complex torus, while positivity of (5.3) supplies an ample Riemann form.

The complex dimension of $A_h$ is $\frac12\dim_{\mathbf Q}V$. It has no necessary relation to the surface dimension $2$.

### 5.3 Parity repair and auxiliary factors

If a tensor-corestriction module $U$ carries a symmetric form $q$ rather than an alternating form, put

$$
\mathbb H(U)=U\oplus U^\vee,qquad
\Psi((x,f),(y,g))=g(x)-f(y).                                     \tag{5.5}
$$

If $\rho(g)$ acts on $U$ with intended multiplier $\nu(g)$, define

$$
g(x,f)=\bigl(\rho(g)x,\nu(g)f\circ\rho(g)^{-1}\bigr).           \tag{5.6}
$$

Then direct substitution gives

$$
\Psi(gu,gv)=\nu(g)\Psi(u,v).                                    \tag{5.7}
$$

The form (5.5) is perfect and alternating in every characteristic. Thus hyperbolic enlargement repairs the parity without changing the adjoint group. It may, however, enlarge the commutant and leave a central kernel in the action. The kernel must be divided out or detected by an auxiliary faithful summand. We include that choice in the strange realization.

### 5.4 PEL realizability

**Definition 5.2.** A strange realization is **PEL-exact** if the identity component of

$$
\{g\in\operatorname{GL}_D(V):\psi(gx,gy)=\nu(g)\psi(x,y),
\ \nu(g)\in\mathbf G_m\}                                      \tag{5.8}
$$

is precisely the chosen central modification of $G$, and not a larger group.

This condition rules out missing tensors. It is checked after algebraic closure by double centralizers: the centralizer of the prescribed semisimple algebra in $\operatorname{End}(V)$ must be exactly the algebra generating the intended group, and the adjoint equation must impose exactly its unitary involution. Because equality of closed subgroup schemes can be checked faithfully flatly, the split calculation descends.

**Theorem 5.3.** A PEL-exact strange realization gives a faithful morphism of Shimura data

$$
(G,X)\longrightarrow(\operatorname{GSp}(V,\psi),\mathfrak H_V), \tag{5.9}
$$

whose Hodge structures are polarized of weight one.

**Proof.** Equations (5.1)--(5.3) give the symplectic representation, Hodge types, and positivity. PEL-exactness identifies its tensor stabilizer with $G$. Therefore conjugating $h$ in $G(\mathbf R)$ produces exactly the intended subdomain of Siegel space, proving that (5.9) is a morphism of Shimura data. Faithfulness is part of the realization, after treatment of the finite central kernel. $\square$

## 6. Integral PEL data and the moduli problem

The rational construction produces the generic Shimura datum. To obtain a moduli scheme we choose integral tensors. These choices are auxiliary but cannot be omitted: they determine polarization degree, level, and the set of primes at which the naive local model is trustworthy.

### 6.1 Orders, lattices, and the good base

Choose a $*$-stable order $\mathcal O_D\subset D$, an $\mathcal O_D$-stable lattice $\Lambda\subset V$, and a positive integer $c$ for which $c\psi$ is integral on $\Lambda$. Let $\Lambda^\#$ be the dual lattice. Fix the finite group type $\Lambda^\#/\Lambda$ that the polarization kernel is to model.

Let $S_{\mathrm{bad}}$ contain:

- $2$ and every prime ramified in $K$, $D$, or $\mathcal O_D$;
- primes where $\Lambda$ is not of the prescribed self-dual type;
- primes dividing $c$ or the polarization degree;
- primes at which the compact open level is not hyperspecial.

With $R=\mathcal O_E[S_{\mathrm{bad}}^{-1}]$, all relevant modules are finite locally free and the polarization pairing is perfect. This is a spread-out PEL model, not a claim of optimal integral extension.

### 6.2 Objects and arrows

For an $R$-scheme $S$, an object is a quadruple

$$
(A,\iota,\lambda,\eta),                                          \tag{6.1}
$$

where:

1. $A/S$ is an abelian scheme of relative dimension $g=\frac12\dim_\mathbf QV$;
2. $\iota:\mathcal O_D\to\operatorname{End}_S(A)$ is a unital action;
3. $\lambda:A\to A^\vee$ is a polarization of the fixed finite-flat kernel type;
4. $\eta$ is a prime-to-$S_{\mathrm{bad}}$ level structure modulo $C$;
5. the Rosati, determinant, and orientation conditions below hold.

An arrow is an isomorphism of abelian schemes preserving the action, polarization, and level. If similitude level is used, preservation of $\lambda$ and the level multiplier is imposed with the same fixed scalar convention. Quasi-isogenies are not arrows in this moduli category; they enter Hecke correspondences later.

### 6.3 Polarizations and Rosati compatibility

The action and polarization satisfy

$$
\lambda^{-1}\iota(d)^\vee\lambda=\iota(d^*)                    \tag{6.2}
$$

in $\operatorname{End}^0(A)$. Since $*$ reverses multiplication, checking (6.2) on ring generators suffices. Positivity means that $\lambda$ is locally induced by a relatively ample line bundle, not merely that it is a symmetric isogeny.

Equation (6.2) implies on prime-to-bad torsion that

$$
e_n^\lambda(\iota(d)x,y)=e_n^\lambda(x,\iota(d^*)y).             \tag{6.3}
$$

The pairing is perfect when $(n,\deg\lambda)=1$. This is why the level integer must avoid the polarization degree.

### 6.4 Prime-to-bad level

For a principal level $N\ge3$ invertible on $R$, a full level structure is an $\mathcal O_D$-linear similitude

$$
\eta_N:\Lambda/N\Lambda\xrightarrow{\sim}A[N]                  \tag{6.4}
$$

between $c\psi$ and $e_N^\lambda$. General compact open level is the orbit of a prime-to-bad adelic trivialization under $C$. The multiplier of (6.4) must agree with the polarization convention; dropping it would replace $G$ by an isometry subgroup.

## 7. The determinant and signature conditions

The abelian dimension and the algebra action do not determine the Hodge cocharacter. The determinant law records the multiplicities of every complex embedding, including the definite orientations that contribute no tangent direction.

### 7.1 The universal polynomial law

Let

$$
V_{\mathbf C}=V^{-1,0}\oplus V^{0,-1}
$$

be the Hodge decomposition. With the homology convention, let $W_h$ be the quotient modeling $\operatorname{Lie}A$. Choose a $\mathbf Z$-basis $e_1,\ldots,e_m$ of $\mathcal O_D$ and define

$$
P_h(T;X_1,\ldots,X_m)=
\det\left(T-\sum_iX_ie_i\mid W_h\right).                          \tag{7.1}
$$

Its coefficients lie in the reflex field $E$ and, after enlarging $S_{\mathrm{bad}}$, in $R$. The determinant condition on (6.1) is

$$
\det\left(T-\sum_iX_i\iota(e_i)\mid\operatorname{Lie}A\right)
=P_h(T;X_1,\ldots,X_m).                                           \tag{7.2}
$$

Using the universal element is essential: characteristic polynomials of a generating set do not determine the characteristic polynomial of every noncommutative expression.

### 7.2 The rank-two formula

For $a\in K$, (7.2) specializes over $\mathbf C$ to

$$
\det(T-a\mid\operatorname{Lie}A)
=\prod_{\varphi:K\hookrightarrow\mathbf C}(T-\varphi(a))^{r_\varphi m}, \tag{7.3}
$$

where $m$ is the Morita multiplicity of the chosen $D$-module. At $v_1,v_2$, both conjugate embeddings occur with equal moving multiplicity. At a definite place, all multiplicity lies on one member of the pair. Thus (7.3) remembers the full function (2.4).

The factor $m$ must not be guessed from the surface dimension. It is computed from $V$ as a $D\otimes\mathbf C$-module. Hyperbolic enlargement doubles it.

For example, if $D=M_2(K)$ and $V$ contains $m$ copies of its standard module, Morita equivalence gives $\mathbf C^2\otimes\mathbf C^m$ at each embedding. Signature $(1,1)$ gives exponent $m$ at each member of a conjugate pair; $(2,0)$ gives exponents $(2m,0)$ and $(0,2)$ gives $(0,2m)$. Every pair contributes total degree $2m$, so the abelian dimension remains constant while the number of moving factors changes. This is a useful flatness check on (7.3).

### 7.3 Closedness and base change

**Proposition 7.1.** The determinant condition is independent of the chosen basis of $\mathcal O_D$, is closed in families, and commutes with arbitrary base change.

**Proof.** A basis change makes an invertible linear substitution in the variables $X_i$, so equality of the two polynomial laws is invariant. Locally trivialize $\operatorname{Lie}A$. The coefficients of its characteristic polynomial are polynomial expressions in the matrix entries of the finitely many $\iota(e_i)$; equality with (7.1) is therefore finitely many closed equations. Determinants and exterior powers of finite locally free modules commute with base change, proving the last assertion. $\square$

### 7.4 Orientation and failure at bad primes

At characteristic zero, semisimplicity makes the determinant law equivalent to the desired multiplicities. It need not distinguish two orientation components in every central modification. When it does not, we impose the component selected by $h$ as an open-and-closed condition.

At primes where $\mathcal O_D$ is not semisimple, modules with identical characteristic-polynomial law can have different nilpotent extensions. The determinant locus can be nonflat or nonreduced. Wedge, spin, or lattice-chain conditions may be necessary. We make no good-model claim there; those primes were deliberately excluded from $R$.

## 8. Descent, inertia, and representability

The moduli problem is naturally a groupoid because abelian schemes have automorphisms. Descent is effective for each constituent, polarization controls the diagonal, and sufficiently deep level removes inertia. This yields a genuine fine scheme.

### 8.1 Why the moduli problem is a stack

**Proposition 8.1.** The category of objects (6.1) is an fpqc stack.

**Proof.** Abelian schemes and their group laws descend effectively under fpqc covers. Homomorphisms descend because their graphs are compatible closed subschemes. Hence the action $\iota$ and polarization $\lambda$ descend, and equality (6.2) descends as equality of morphisms. Relative ampleness is fpqc local, so the descended symmetric isogeny remains a polarization. Finite étale torsion and its trivializations descend. Finally, (7.2) is an equality of polynomial laws on a vector bundle and descends coefficientwise. Uniqueness follows from descent of morphisms. $\square$

### 8.2 Finiteness of isomorphisms

For two polarized abelian schemes, the isomorphism functor preserving the polarizations is finite and unramified. Indeed rigidity makes the Hom functor unramified, while the Rosati-positive quadratic degree bounds the possible homomorphisms in each geometric fiber. The equations requiring compatibility with $\iota$ and $\eta$ are closed. Thus the diagonal of the PEL stack is finite, separated, and unramified.

The polarization is indispensable. Without it, units in a positive-rank endomorphism order can produce infinitely many automorphisms.

### 8.3 Killing automorphisms

**Proposition 8.2.** Full level $N\ge3$ kills every automorphism of a PEL object.

**Proof.** Let $u$ act trivially on $A[N]$. Then $u-1$ is divisible by $N$ in $\operatorname{End}(A)$, say $u=1+Nv$. Since $u$ preserves a polarization, it has finite order. If $u$ has prime order $\ell$, the relation

$$
0=1+u+\cdots+u^{\ell-1}
$$

after subtracting $\ell$ and expanding in $Nv$ shows successively that $v$ is divisible by every power of $N$ unless $u=1$; the torsion-free abelian group $\operatorname{End}(A)$ has zero intersection of these powers. Applying this to each prime divisor of the order gives $u=1$. The exclusion $N=2$ is necessary because $-1$ acts trivially on $A[2]$. $\square$

A neat adelic level gives the same conclusion provided it detects the center. Adjoint neatness alone can leave central torsion.

### 8.4 The fine moduli scheme

**Theorem 8.3.** At full level $N\ge3$, or at a center-detecting neat level, the PEL functor is represented by a quasi-projective $R$-scheme $M_C$ carrying a universal object.

**Proof strategy.** Use a canonical ample power to enter a Hilbert scheme, impose the extra structures by locally closed equations, and divide by projective frames.

**Proof.** A fixed polarization type bounds the Hilbert polynomial of a sufficiently high canonical symmetric power. A projective frame embeds every object in one fixed projective space, giving a finite-type Hilbert parameter scheme. The group law, zero section, $\mathcal O_D$-action, polarization, and level are represented by morphisms and finite schemes; their identities are closed conditions. Smoothness and geometric connectedness of the fibers are open, as is relative ampleness. Proposition 7.1 cuts out the determinant locus, and the orientation condition selects an open-and-closed part.

Changing the frame is a free action of a general linear group. The quotient is an algebraic space. The forgetful map to fine Siegel moduli is finite because a fixed polarized abelian scheme admits only finitely many compatible order actions and finite level structures. A finite algebraic space over a quasi-projective scheme is a scheme and is quasi-projective. Proposition 8.2 supplies trivial inertia, so this quotient represents the set-valued functor. The identity morphism then gives the universal object. $\square$

## 9. The local model of the surface

Representability does not yet show that the generic fiber is a surface. Its dimension comes from lifting the Hodge filtration. Semisimplicity separates the real labels, and exactly two rank-one lines move.

### 9.1 Lifting the Hodge filtration

Let $S_0\hookrightarrow S$ be a square-zero thickening of $E$-schemes and let $A_0/S_0$ be a PEL object. Write

$$
0\longrightarrow F_0\longrightarrow H_{1,\mathrm{dR}}(A_0/S_0)
\longrightarrow\operatorname{Lie}A_0\longrightarrow0.            \tag{9.1}
$$

Deformations of $A_0$ correspond to locally direct-summand lifts $F\subset H$ of $F_0$. The action lifts exactly when $F$ is $\mathcal O_D$-stable; the polarization lifts exactly when $F$ is isotropic; the prime-to-characteristic level lifts uniquely; and (7.2) fixes the ranks of the quotient $H/F$.

This theorem follows from the universal vector extension of an abelian scheme: its Lie algebra is de Rham homology, and lifting the abelian scheme is equivalent to lifting the Hodge subbundle. Endomorphisms and polarizations lift precisely when their induced linear maps preserve that subbundle and pairing. Characteristic zero is used to keep $D$ semisimple and the multiplicity summands split.

### 9.2 Two moving lines

After extension to $\mathbf C$ and Morita equivalence, the piece at an active place is

$$
S\otimes U_i,
$$

where $S$ is the fixed simple module for the matrix algebra and $U_i$ is two-dimensional. An admissible Hodge submodule is $S\otimes L_i$ for a line $L_i\subset U_i$. Therefore the local model at $v_i$ is

$$
\operatorname{Gr}(1,U_i)\simeq\mathbf P^1.                       \tag{9.2}
$$

At every definite place, the determinant condition fixes the filtration; there is no moving line. Hence the geometric generic local model is

$$
\mathcal M_{\mathbf C}\simeq\mathbf P^1\times\mathbf P^1.       \tag{9.3}
$$

Its tangent space at $(L_1,L_2)$ is

$$
\operatorname{Hom}(L_1,U_1/L_1)\oplus
\operatorname{Hom}(L_2,U_2/L_2).                                 \tag{9.4}
$$

This computation is also a diagnostic. An extra moving factor means that the centralizer or determinant law describes a larger group than intended.

Polarization explains why no further equation cuts down (9.3). On an active block it pairs the $\varphi$-part perfectly with the $c\varphi$-part. Choosing $L_i$ determines the conjugate Hodge summand as its annihilator. At a definite block, determinant multiplicity is full or zero, so the filtration is forced. Thus the model is a product of projective lines rather than a quadric or a larger Grassmannian.

In affine coordinates $z_1,z_2$ around $(L_1,L_2)$, its completed local ring is

$$
\mathbf C[[z_1,z_2]].                                             \tag{9.8}
$$

The framed deformation space adds smooth trivialization coordinates and quotienting removes the same coordinates. Hence, after a finite residue-field extension, the completed local ring of $M_{C,E}$ is $E'[[z_1,z_2]]$. Making one active place definite removes one variable; making a third place indefinite adds one. These variations verify the dimension formula directly.

### 9.3 Smoothness and dimension two

**Theorem 9.1.** The generic fiber $M_{C,E}$ is smooth of pure dimension two.

**Proof.** The framed de Rham torsor maps smoothly to both $M_{C,E}$ and the local model $G_E/P_\mu$. Over $\mathbf C$, the latter is (9.3), hence smooth of dimension two. Smoothness descends through the smooth surjective framed torsor, and relative dimensions cancel. Equivalently, every infinitesimal deformation is the independent lifting of the two lines in (9.4); line Grassmannians are smooth, so all square-zero obstructions vanish and the tangent rank is two. Finite presentation converts formal smoothness to smoothness. $\square$

Pure dimension holds on every component. Smoothness gives regularity and normality.

### 9.4 Cotangent and determinant lines

Let $\mathcal L_i\subset\mathcal U_i$ be the two universal active lines. On the local model,

$$
\Omega^1_i\simeq
\mathcal L_i\otimes(\mathcal U_i/\mathcal L_i)^\vee
\simeq\mathcal L_i^{\otimes2}\otimes(\det\mathcal U_i)^{-1}.    \tag{9.5}
$$

Thus

$$
\Omega^1_{M_{C,E}/E}\simeq\Omega^1_1\oplus\Omega^1_2,           \tag{9.6}
$$

and

$$
\det\Omega^1_{M_{C,E}/E}\simeq
\mathcal L_1^{\otimes2}\otimes\mathcal L_2^{\otimes2}
\otimes(\det\mathcal U_1\det\mathcal U_2)^{-1}.                 \tag{9.7}
$$

The determinant factors are multiplier lines; they may be trivialized only if the level has actually reduced the corresponding similitude. On an lci integral locus, (9.7) must be interpreted through $\operatorname{Det}(L_{M_C/R})$, not through a possibly non-locally-free top exterior power of differentials.

## 10. Complex uniformization and the canonical surface

The fine PEL scheme and the canonical Shimura variety were constructed by different routes. Complex uniformization identifies them on the exact union of components selected by the lattice genus and orientation.

### 10.1 From PEL objects to lattices

For a complex PEL object, choose an $\mathcal O_D$-linear symplectic identification of rational homology with $V$. Its Hodge structure gives a point $h\in X$, and its prime-to-bad lattice gives $gC\in G(\mathbf A_f)/C$. Changing the identification by $q\in G(\mathbf Q)$ replaces $(h,g)$ by $(qh,qg)$. Thus one obtains a point of (1.1).

Conversely, $(h,gC)$ gives a lattice in $V(\mathbf A_f)$, hence a rational lattice up to commensurability. The polarized weight-one Hodge structure of Theorem 5.3 produces a complex abelian variety with $D$-action, polarization, determinant law, and level. The two constructions are inverse on the lattice-genus and orientation classes admitted by the integral datum.

### 10.2 The double quotient

**Theorem 10.1.** There is a natural analytic isomorphism

$$
M_C^{\mathrm{req}}(\mathbf C)^{\mathrm{an}}
\simeq G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/C)^{\mathrm{req}}, \tag{10.1}
$$

where “required” denotes the open-and-closed union determined by polarization type, lattice genus, multiplier, and orientation.

**Proof.** The preceding two constructions are inverse on points. Neatness makes stabilizers trivial. In families, the Hodge filtration varies holomorphically, and the period construction gives local analytic charts modeled on $X$. Both maps are local biholomorphisms and inverse on points, hence inverse analytic isomorphisms. $\square$

### 10.3 Comparison with the canonical model

Let $S_C/E$ be the canonical model of $(G,X)$ with the Artin and adelic conventions of Section 1.3.

**Proposition 10.2.** The required generic PEL union $M_{C,E}^{\mathrm{req}}$ is canonically isomorphic to the corresponding union in $S_C$.

**Proof.** The symplectic morphism (5.9) algebraizes the analytic map. By (10.1) it is bijective and induces the same function field on each selected component. The PEL scheme is normal by Theorem 9.1; the canonical model is normal by construction. The map is finite because both spaces are finite over the same fine Siegel PEL locus. A finite birational map to a normal scheme is an isomorphism.

The isomorphism respects descent: at a special point $[h,g]$, CM reciprocity sends

$$
[h,g]^{\operatorname{Art}_{E(h)}(s)}=[h,r_h(s_f)g],              \tag{10.2}
$$

which is the lattice action on the PEL abelian variety. Density of special points makes the descended isomorphism unique. $\square$

### 10.4 Projectivity

**Corollary 10.3.** If $W$ is anisotropic over $F$, every neat required component is a smooth projective surface over its field of definition.

**Proof.** It is smooth of dimension two by Theorem 9.1. Proposition 3.2 makes its complex analytification compact. A compact analytic space underlying a quasi-projective complex variety is proper: in a projective closure, any missing boundary point has a punctured analytic neighborhood that is noncompact. Properness descends along field extensions. A proper quasi-projective variety is projective. $\square$

## 11. The modèles étranges comparison

The construction is now geometric. We next state precisely how it retains quaternionic automorphic information. The comparison is between finite-adelic derived groups and their Hecke algebras; it is not an identification of universal abelian varieties.

### 11.1 Finite-adelic matching

Let $G_B$ be the chosen quaternionic central modification and $G$ the strange unitary group. Fix a finite set $\Sigma$ containing every place where either group, algebra, level, or central map is ramified. A strange realization gives, for $v\notin\Sigma$, isomorphisms

$$
G_B^{\mathrm{der}}(F_v)\simeq G^{\mathrm{der}}(F_v)             \tag{11.1}
$$

carrying hyperspecial subgroups to hyperspecial subgroups. At places in $\Sigma$, the realization records the intended inner-form identification or deliberately leaves the place outside the comparison.

For $v\notin\Sigma$, (11.1) identifies spherical double-coset algebras. Convolution is preserved because Haar measure is normalized by volume one for the corresponding hyperspecial subgroup. Thus the same abstract good-place Hecke operators act on both towers.

### 11.2 Central quotients and finite fibers

Usually the comparison fits into a central diagram

$$
\begin{array}{ccc}
G_B^{\mathrm{der}} & \longrightarrow & G^{\mathrm{der}}\\
\downarrow && \downarrow\\
G_B & \dashrightarrow & G,
\end{array}                                                        \tag{11.2}
$$

where the lower arrow may require adjoining a torus and dividing by a finite central subgroup. The dashed arrow is not silently treated as an isomorphism. Its kernel affects levels, stabilizers, and connected components; its torus cokernel affects central characters.

**Proposition 11.1.** Let $f:H\to G$ be a central isogeny compatible with Shimura data, and let $C_H=f^{-1}(C)$. At neat level the induced map of Shimura varieties is finite étale onto an open-and-closed union, with geometric fiber a quotient of

$$
\ker f(\mathbf A_f)/\bigl(\ker f(\mathbf Q)\,\ker f(\mathbf A_f)\cap C_H\bigr). \tag{11.3}
$$

**Proof.** The domains agree because a central isogeny induces an isomorphism on adjoint groups. The map on adelic quotients has finite fibers measured by the central kernel. Neatness removes fixed points, so the finite action is free and the map is étale. Its image is open and closed because the component sets are finite and the map is locally an isomorphism. $\square$

### 11.3 Why the auxiliary abelian variety is not the automorphic object

The universal abelian scheme has first cohomology equal to the chosen symplectic representation $V$. The surface itself has middle cohomology arising from the two active tangent directions and from automorphic representations of $G$. These are different representations. Tensor, Morita, and central modifications can place the desired rank-two system inside a summand of a larger cohomology representation, but extracting that summand requires idempotents and automorphic multiplicity arguments.

This book therefore proves only the geometric carrier: a compact surface, its Hecke correspondences, and its auxiliary universal PEL family. The automorphic decomposition of $H^2$ is a later theorem and is not used here.

### 11.4 Independence of auxiliary choices

Changing $\alpha$ in (5.1), the lattice within its genus, a Morita module, or a sufficiently deep level changes the PEL presentation. It does not automatically give an isomorphic fine moduli scheme. What is invariant is the canonical Shimura tower after passage to common level and selection of matching components.

**Proposition 11.2.** Two PEL-exact strange realizations inducing isomorphic rational Shimura data have canonically isomorphic canonical-model towers after restriction to a common compact open subgroup. Their PEL universal abelian schemes need not be isomorphic.

**Proof.** The rational isomorphism identifies $X$ and the adelic double quotients at common level. It respects Hodge cocharacters, hence reflex fields and reciprocity morphisms. The uniqueness of canonical models, characterized by (10.2), descends the analytic identification. Universal abelian schemes depend on the chosen symplectic representation and thus are not covered by that uniqueness assertion. $\square$

## 12. Connected components and canonical descent

Component bookkeeping is the place where a seemingly harmless abbreviation produces a wrong field of definition. The multiplier is not enough for a unitary similitude group. We retain the full abelianized torus and the image of adelic points.

### 12.1 The exact component set

Fix $X^+\subset X$ and put

$$
G(\mathbf Q)_+=\{q\in G(\mathbf Q):qX^+=X^+\}.
$$

Let $T=G/G^{\mathrm{der}}$ and let $\nu_T:G\to T$. Strong approximation for the simply connected group $G^{\mathrm{der}}$, which has the two noncompact real factors, gives

$$
\pi_0(S_C(\mathbf C))\simeq
T(\mathbf Q)^\dagger\backslash
\nu_T(G(\mathbf A_f))/\nu_T(C),                                  \tag{12.1}
$$

where $T(\mathbf Q)^\dagger=\nu_T(G(\mathbf Q)_+)$. The middle term is the image $\nu_T(G(\mathbf A_f))$, not automatically all of $T(\mathbf A_f)$.

**Proof.** First, connected components are $G(\mathbf Q)_+\backslash G(\mathbf A_f)/C$. If two adelic elements have the same image in the right side of (12.1), after multiplying by a rational positive element and a level element their quotient lies in $G^{\mathrm{der}}(\mathbf A_f)$. Strong approximation writes it as a rational derived element times a level element. The rational derived group preserves $X^+$, proving injectivity. Surjectivity onto the displayed image is tautological. $\square$

The determinant and multiplier satisfy (3.2), so both contribute to $T$. Replacing (12.1) by a quotient of $\mathbf A_f^\times$ through $\nu$ can merge genuine components. Replacing the image by all of $T(\mathbf A_f)$ can add nonexistent ones when a central kernel has nontrivial local cohomology.

### 12.2 Reciprocity on components

The Hodge cocharacter induces an ambient reflex morphism

$$
r_{(G,X)}:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m\to T.      \tag{12.2}
$$

For $s\in\mathbf A_E^\times$, arithmetic reciprocity acts on (12.1) by

$$
[t]^{\operatorname{Art}_E(s)}=[r_{(G,X)}(s_f)t].                  \tag{12.3}
$$

At a special point with reflex field $E(h)$, functoriality of cocharacters gives

$$
\nu_T\circ r_h=r_{(G,X)}\circ N_{E(h)/E}.                        \tag{12.4}
$$

Hence special-point and component descent agree. There is no independent inverse: arithmetic Artin and the left adelic convention have already fixed the direction in (12.3).

### 12.3 Fields of definition of individual components

Let $C_0$ be a geometric connected component. Its stabilizer corresponds under Artin reciprocity to

$$
E^\times\backslash
r_{(G,X)}^{-1}\bigl(T(\mathbf Q)^\dagger\nu_T(C)\bigr)
\subset\mathbf A_E^\times/E^\times.                              \tag{12.5}
$$

This subgroup is open: a sufficiently small compact open in $\mathbf A_{E,f}^\times$ maps into $\nu_T(C)$. Its fixed field $E_{C_0}$ is therefore a finite abelian extension of $E$.

**Proposition 12.1.** The component $C_0$ descends to $E_{C_0}$, and $E_{C_0}$ is its minimal field inside $\overline{\mathbf Q}$ relative to the action (12.3).

**Proof.** Formula (12.3) says that a Galois element fixes $C_0$ exactly when its idele class lies in (12.5). The component is open and closed, so its idempotent in the finite étale algebra of components descends exactly under its stabilizer. Galois descent gives a variety over the fixed field, and minimality follows from the equality of stabilizers. $\square$

The whole canonical surface is defined over $E$ even when none of its geometric components is individually defined over $E$.

### 12.4 Selecting the required union

Polarization type, lattice genus, determinant orientation, and central multiplier define subsets of (12.1). A PEL model over $E$ must select a Galois-stable union under (12.3), not an arbitrary geometric component. A single component becomes legitimate after base change to its field (12.5). Because the fine moduli functor is preserved by the corresponding idempotent, the universal abelian scheme restricts and descends over the same field.

## 13. Levels, universal families, and Hecke maps

The strange construction is useful only as a tower. Fine levels carry universal objects, arbitrary levels are finite quotients, and rational adelic elements produce isogeny correspondences compatible with canonical descent.

### 13.1 Fine and coarse levels

If $C'\triangleleft C$ is neat and normal, put $\Delta=C/C'$. Then

$$
\mathscr M_C\simeq[M_{C'}/\Delta],                               \tag{13.1}
$$

and the coarse space is the finite quotient $M_{C'}/\Delta$. At a non-neat level, stabilizers can produce quotient singularities. The universal family descends to the coarse quotient only when every stabilizer acts trivially on the entire PEL object. A power of a Hodge line can descend even when the family does not.

### 13.2 The universal abelian scheme

At fine level, representability gives a universal tuple

$$
(\mathcal A,\iota^{\mathrm{univ}},\lambda^{\mathrm{univ}},
\eta^{\mathrm{univ}})\longrightarrow M_C.                        \tag{13.2}
$$

Its Hodge bundle

$$
\omega_{\mathcal A}=e^*\Omega^1_{\mathcal A/M_C}                \tag{13.3}
$$

is locally free, carries the determinant law (7.2), and decomposes over $E$ into the active and definite multiplicity pieces. The active lines in that decomposition are the $\mathcal L_i$ of Section 9.4.

### 13.3 Hecke isogenies

For $a\in G(\mathbf A_f)$, put $C_a=C\cap aCa^{-1}$. The two maps

$$
M_{C_a}\rightrightarrows M_C                                    \tag{13.4}
$$

forget level directly and after translating it by $a$. If $a$ is integral away from a finite set, the lattices $\widehat\Lambda$ and $a\widehat\Lambda$ have finite-index intersection. The associated finite subgroup of the universal abelian scheme gives an isogeny between the pullbacks along (13.4). Quotients by finite locally free subgroup schemes exist and commute with base change, so this construction is algebraic.

The polarization on the quotient is determined by its pullback. When a principal polarization is to remain principal, the kernel must be Lagrangian for the induced Weil pairing; isotropy, not merely its numerical order, is the correct hypothesis.

### 13.4 Descent of correspondences

**Proposition 13.1.** The generic Hecke correspondence (13.4) and its universal isogeny descend over the reflex field, or over the common component field after selecting individual components.

**Proof.** At a special point, the reciprocity multiplier acts on the left, whereas Hecke translation acts on the right:

$$
r_h(s_f)(ga)=(r_h(s_f)g)a.
$$

Thus the correspondence commutes with Galois on the dense set of special points. Canonical-model uniqueness descends its two maps. At fine level the universal isogeny is characterized by its finite lattice kernel, which is preserved by the same action, so descent of morphisms gives the isogeny. Restricting to components uses (12.5). $\square$

Extension across omitted primes is not asserted. It requires good or semistable integral models.

## 14. The cohomological role of the surface

The construction was motivated by degree-two cohomology. We now explain the geometric reason without importing the later automorphic decomposition theorem.

### 14.1 Why degree two is the middle degree

A smooth projective surface has cohomology in degrees $0$ through $4$, and Poincaré duality pairs $H^i$ with $H^{4-i}$. Thus $H^2$ is the self-dual middle degree. The two independent active directions in (9.4) give the holomorphic tangent bidegrees whose exterior product lies in degree two.

For the compact dual $\mathbf P^1\times\mathbf P^1$, the two degree-one tangent roots add to the middle cohomological degree. This is the geometric shadow of taking two rank-one archimedean factors.

### 14.2 The Künneth sign and automorphic parity

On a product of two one-dimensional symmetric domains, interchanging the two degree-one factors contributes a minus sign in cohomology. Their cup product therefore lies in even degree and is symmetric under the combined graded convention. This matches the fact that a tensor product of two alternating rank-two forms is symmetric. The surface does not erase the sign; it places it in the correct cohomological degree.

More generally, the parity of the number of active real factors determines the middle degree of the associated locally symmetric space. The strange construction chooses two active factors precisely when the desired global packet has even archimedean parity.

### 14.3 What geometry supplies and what remains

This book supplies:

- a smooth projective canonical surface at neat level;
- a PEL universal abelian scheme on its fine cover;
- good-place Hecke correspondences and their canonical descent;
- an exact finite-adelic comparison with the prescribed quaternionic derived group;
- component fields and central-character bookkeeping.

It does not prove a Matsushima formula, multiplicity one, an automorphic decomposition of $H^2$, construction of Galois representations, integral comparison, or local-global compatibility. Those conclusions require harmonic analysis and integral geometry beyond the construction itself. Nothing in Chapters 1--13 depends on them.

## 15. Construction theorem and hypothesis ledger

We finish by assembling the argument into one reusable theorem. Its detailed hypotheses prevent the common errors: confusing moduli and abelian dimensions, forgetting the determinant orientation, replacing the abelianization by the multiplier, and descending a component over too small a field.

### 15.1 The complete construction theorem

**Theorem 15.1 (unitary surface and modèles étranges package).** Let $F$ be totally real, $K/F$ CM, and let $B/F$ be a quaternion algebra prescribing rank-one finite local inner forms. Assume:

1. a Hermitian plane has signature $(1,1)$ at exactly two real places and definite oriented signature elsewhere;
2. its local invariants satisfy the global product relation and it is anisotropic over $F$;
3. a PEL-exact strange realization $\mathfrak S=(K,D,*,V,\Phi,h)$ matches $B^1$ at the prescribed finite places, with its finite central kernel and rational multiplier specified;
4. the associated rational form is alternating, either directly or after the explicit hyperbolic repair;
5. $\mathcal O_D$, $\Lambda$, polarization type, determinant law, orientation, and a center-detecting neat compact open $C$ are fixed away from a finite bad set.

Then:

1. $(G,X)$ is a Shimura datum of dimension two, with reflex field equal to the stabilizer field of the full signature function $r_\varphi$.
2. The PEL groupoid is an fpqc algebraic stack with finite unramified separated diagonal. At the stated fine level it is represented by a quasi-projective scheme $M_C$ with a universal PEL abelian scheme.
3. The generic required union $M_{C,E}^{\mathrm{req}}$ is smooth of pure dimension two. Its geometric local model is $\mathbf P^1\times\mathbf P^1$, and its cotangent determinant is (9.7).
4. This union is canonically isomorphic to the corresponding canonical model of

   $$
   G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/C).
   $$

   It is projective because the Hermitian plane is anisotropic.
5. Its connected components are exactly

   $$
   T(\mathbf Q)^\dagger\backslash
   \nu_T(G(\mathbf A_f))/\nu_T(C),
   $$

   and arithmetic reciprocity acts by (12.3). An individual component descends over the finite abelian field defined by (12.5), not necessarily over $E$.
6. At matching finite places, the derived group and spherical Hecke algebra agree with those of $B^1$. Central kernels and torus characters are retained through (11.2)--(11.3).
7. Level maps and generic Hecke correspondences descend canonically. Fine levels carry universal isogenies; arbitrary levels are finite quotient stacks and coarse schemes, on which the universal family need not descend.

**Proof.** Theorem 2.1 and Proposition 2.2 construct the global anisotropic Hermitian input. Propositions 3.1 and 3.2 give the Shimura datum, dimension, reflex field, and compactness. Chapters 4 and 5 construct and verify the PEL-exact symplectic realization. Proposition 8.1, Proposition 8.2, and Theorem 8.3 give the stack and fine scheme. The Hodge-lifting calculation and (9.3) prove generic smoothness and the cotangent formulas. Theorems 10.1 and Proposition 10.2 identify the PEL scheme with the canonical model, while Corollary 10.3 proves projectivity. Chapter 11 proves finite-adelic matching. Formula (12.1), reciprocity (12.3), and Proposition 12.1 establish the component and descent statements. Chapter 13 treats levels and Hecke maps. $\square$

### 15.2 Exact hypotheses and failure modes

| Claim | Required input | Failure without it |
|---|---|---|
| two-dimensional domain | exactly two signatures $(1,1)$ | abelian dimension does not determine Shimura dimension |
| stated reflex field | full function $r_\varphi$, including definite orientations | remembering only active places can give a field that is too small |
| global Hermitian plane | determinant compatibility and product relation | prescribed local spaces need not globalize |
| compact surface | anisotropy over $F$ | isotropic lines produce parabolics and cusps |
| quaternionic comparison | explicit local Brauer matching of the commutant | tensoring $B$ with $K$ alone need not give the desired group |
| PEL interpretation | PEL-exact centralizer and positive involution | endomorphisms and a pairing can define a larger Shimura variety |
| symplectic representation | alternating form and rational common multiplier | even tensor parity gives an orthogonal form; an $F$-multiplier is not rational |
| correct Hodge locus | universal determinant polynomial plus orientation when needed | dimension or generatorwise characteristic polynomials allow wrong multiplicities |
| fine scheme | full level $N\ge3$ or center-detecting neatness | finite central inertia survives, especially at level two |
| smooth generic surface | characteristic zero semisimplicity and local model $G/P_\mu$ | ramified determinant models may be nonflat or nonreduced |
| component formula | strong approximation and the full torus image $\nu_T(G(\mathbf A_f))$ | multiplier-only formulas merge components; torus surjectivity can fail |
| component over its field | reciprocity stabilizer (12.5) | a geometric component need not descend over the ambient reflex field |
| universal family on quotient | trivial stabilizer action | coarse moduli forgets the descent datum of the family |
| Hecke extension at bad primes | a separately constructed integral model | generic correspondences do not automatically extend |

### 15.3 Conclusion

The parity problem has been converted into geometry without losing its arithmetic content. A CM extension and a carefully globalized Hermitian plane provide two indefinite real factors and hence a two-dimensional domain. Anisotropy removes rational boundary components. The full signature function determines the reflex field, including orientations at definite places that contribute no tangent dimension.

The modèles étranges construction then supplies the bridge to quaternionic automorphic data. A central simple algebra with involution of the second kind, its Morita module, and a positive alternating trace form produce a PEL-exact symplectic realization. Finite local Brauer calculations identify its derived group with the desired quaternionic inner form. Hyperbolic enlargement repairs an even tensor sign when necessary, while central kernels and auxiliary torus characters remain visible.

The resulting PEL stack has finite diagonal; deep level makes it a fine quasi-projective scheme with a universal abelian family. Its Hodge filtration has exactly two moving lines, so the local model is $\mathbf P^1\times\mathbf P^1$ and the generic fiber is a smooth surface. Complex uniformization identifies the required PEL union with the canonical model, and anisotropy makes it projective.

Finally, descent is controlled by the entire abelianized torus. Components form the quotient (12.1), arithmetic reciprocity acts by left multiplication, and an individual component lives over the finite abelian field cut out by its stabilizer. Fine-level Hecke isogenies and all generic correspondences descend compatibly. The output is therefore the precise geometric carrier needed for degree-two realization: compact unitary surfaces, exact auxiliary PEL varieties, quaternionic finite-place matching, universal families at fine level, and component-correct canonical descent.
