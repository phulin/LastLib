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
G(\mathbf Q)\backslash\bigl(X\times G(\mathbf A_f)/C\bigr),       \tag{1.1}
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

At a real place $v$ of $F$, $K\otimes_{F,v}\mathbf R\simeq\mathbf C$, and (2.1) has a signature $(p_v,q_v)$ with $p_v+q_v=2$. At a finite place, a Hermitian space is classified by its dimension and determinant modulo norms. This remains true at dyadic places, although integral self-dual lattices can have several genera there. We keep the rational determinant class separate from those later integral lattice choices.

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

**Theorem 2.1 (globalization of a Hermitian plane).** Suppose a nondegenerate two-dimensional Hermitian space $W_v$ over $K_v/F_v$ is specified for every place $v$ of $F$, with the standard split choice at all but finitely many finite places. A global Hermitian plane $W$ inducing these local spaces exists if and only if their determinant classes satisfy the global norm-character reciprocity relation; equivalently, they are the localizations of one class in

$$
F^\times/N_{K/F}(K^\times)
$$

with the stated real signatures. When it exists, $W$ is unique up to $K$-linear isometry.

**Proof strategy.** Diagonalize locally and translate isometry into the quadratic norm character. The only local-to-global obstruction is then the reciprocity relation for that character.

**Proof.** A binary Hermitian form over a field is diagonal. After scaling its first coefficient, write it as

$$
b_v\langle1,-a_v\rangle,\qquad a_v,b_v\in F_v^\times.
$$

Changing the second basis vector multiplies $a_v$ by an element of
$N_{K_v/F_v}(K_v^\times)$, while changing $b_v$ changes only the ordered definite signature.
The determinant is $-a_vb_v^2$, and $b_v^2=N_{K_v/F_v}(b_v)$; translating all determinant
classes by the localization of the one global element $-1$ therefore identifies them with the
norm-classes of the $a_v$. Thus the rational local isometry class is the norm-class of $a_v$
together with its ordered real signature. Let
$\chi_v:F_v^\times\to\{\pm1\}$ be the quadratic character with kernel the local
norm group. Global reciprocity for the quadratic extension says that a finitely supported tuple
of local norm-classes comes from $a\in F^\times$ exactly when its characters satisfy the single
product relation. This is the norm-class exactness proved by global class field theory in the
dependency chain. Choose such an $a$.

At a real place the sign of $a$ decides whether $\langle1,-a\rangle$ is indefinite or definite.
When it is definite, multiplication by a scalar $b\in F^\times$ with a prescribed real sign
chooses between $(2,0)$ and $(0,2)$ without changing the determinant norm-class, because the
determinant is multiplied by $b^2=N_{K/F}(b)$. Weak approximation chooses one $b$ with all the
required real signs. The global form $b\langle1,-a\rangle$ now has every prescribed localization.

If two global binary forms have the same localizations, their determinant quotient is a norm
from every $K_v/F_v$. The cyclic norm theorem makes it a global norm, and diagonalization then
gives a global isometry. $\square$

The theorem is a construction protocol. After fixing (2.3), we are free to alter one finite invariant to satisfy the product relation. That place must then be included in the bad set of the integral datum.

For a concrete model choose $a,b\in F^\times$ and put

$$
W=K^2,\qquad
\langle x,y\rangle=b\bigl(x_1c(y_1)-a x_2c(y_2)\bigr).             \tag{2.5}
$$

At a real place this form is indefinite exactly when $a$ is positive; when $a$ is negative, the
sign of $b$ selects $(2,0)$ or $(0,2)$. Approximation can therefore impose (2.3). At a finite
place where $K_v/F_v$ is a field, the plane is isotropic exactly when $a$ is a local norm.
Requiring $a$ to be a non-norm at one such place forces global anisotropy: an isotropic vector
with $x_2\ne0$ would give $a=N_{K/F}(x_1/x_2)$, and $x_2=0$ forces $x_1=0$. Thus real isotropy at
two places and global anisotropy coexist naturally.

If $K_v\simeq F_v\times F_v$, every class is a norm and this device cannot create anisotropy. At dyadic places the rational classification remains valid, but integral self-dual lattices may have several genera. This affects the integral datum, not the rational surface, and explains why dyadic places belong to the bad set.

### 2.4 Anisotropy and compactness

The surface is compact only when $W$ has no nonzero isotropic vector over $K$. Real indefiniteness does not contradict global anisotropy: a vector may exist over each of two completions without existing over $F$.

**Proposition 2.2.** The following are equivalent:

1. $W$ contains a nonzero isotropic vector over $K$;
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

For the Hermitian plane constructed here,
$\operatorname{Res}_{F/\mathbf Q}\operatorname{SU}(W)$ is $\mathbf Q$-simple and is noncompact
at $v_1,v_2$, so the hypothesis of Proposition 3.1 is automatic.

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

We now connect the unitary surface to quaternionic automorphic data. The connection is
group-theoretic before it is cohomological. For rank one it can be written down without an
appeal to an unspecified commutant: a binary Hermitian plane has an associated cyclic quaternion
algebra, and their simply connected groups are the same.

### 4.1 From a quaternion algebra to a unitary algebra

Let $S$ contain every finite place at which the prescribed quaternion algebra $B/F$ is ramified,
as well as every place at which Hecke operators will be compared. Choose the CM extension $K/F$
so that $K_v$ is a field whenever $B_v$ is division. This condition is necessary: if
$K_v\simeq F_v\times F_v$, every element of $F_v^\times$ is a norm and the construction below
can produce only the split inner form.

For $a\in F^\times$ define the cyclic quaternion algebra

$$
Q_a=(K/F,a)=K\oplus Kj,
\qquad j^2=a,
\qquad jx=c(x)j\quad(x\in K).                                    \tag{4.1}
$$

Its reduced norm is

$$
\operatorname{Nrd}(x+yj)=N_{K/F}(x)-aN_{K/F}(y).                 \tag{4.2}
$$

Consequently $Q_{a,v}$ is split precisely when $a$ is a norm from $K_v$; at a split place of
$K/F$ this always occurs. The same scalar $a$ defines the Hermitian plane

$$
W_a=\langle1,-a\rangle.                                          \tag{4.3}
$$

Thus $W_{a,v}$ is isotropic precisely when $Q_{a,v}$ is split. A further scalar
$b\in F^\times$ changes the orientation of a definite Hermitian form but changes neither its
unitary group nor $Q_a$.

### 4.2 Twisting the involution

There is an explicit embedding

$$
\iota:Q_a\hookrightarrow M_2(K),\qquad
x+yj\longmapsto
\begin{pmatrix}x&ay\\ c(y)&c(x)\end{pmatrix}.                   \tag{4.4}
$$

Put $H=\operatorname{diag}(1,-a)$. Direct multiplication gives

$$
\iota(z)^{c,\mathsf t}H\iota(z)=\operatorname{Nrd}(z)H.          \tag{4.5}
$$

In particular, the adjoint involution

$$
M^\star=H^{-1}c(M)^{\mathsf t}H                                 \tag{4.6}
$$

on $M_2(K)$ restricts to canonical quaternion conjugation on $Q_a$. This is the concrete
second-kind involution behind the construction. Replacing $H$ by a general Hermitian matrix is
the same operation after a change of basis; the often-used description
$M\mapsto\delta^{-1}M^\star\delta$ is just its inner-twist form. Signatures alone do not
determine that twist: the determinant norm-classes of Chapter 2 remain part of the datum.

### 4.3 Recovering the required inner form

Taking reduced norm one in (4.5) defines a closed immersion

$$
\operatorname{SL}_1(Q_a)\longrightarrow\operatorname{SU}(W_a). \tag{4.7}
$$

Both sides are connected simply connected $F$-groups of dimension three. After extending to
$K$ the map is the standard isomorphism with $\operatorname{SL}_2$, so (4.7) is an isomorphism
over $F$. Hence

$$
\operatorname{SU}(W_a)(F_v)\simeq Q_{a,v}^1.                    \tag{4.8}
$$

Thus choosing the norm-class of $a$ chooses the local rank-one inner form. This calculation also
shows exactly what may and may not be changed by a PEL representation: adding a central torus or
a hyperbolic symplectic summand can change the similitude group and its center, but it does not
change the adjoint group in (4.8).

### 4.4 The exact matching hypothesis

We now globalize the calculation, including the compactness requirement.

**Definition 4.1.** A **strange realization** of the quaternionic datum $B/F$ is a tuple

$$
\mathfrak S=(K,D,*,V,\Phi,h)
$$

such that:

1. $K/F$ is CM, $W=b\langle1,-a\rangle$ has signatures (2.3), and the standard PEL tensors
   are $D=K$, $*=c$, $V=W$, and $\Phi=\langle\ ,\ \rangle$;
2. the rational similitude group is exactly the group $G$ of (3.1), represented faithfully on
   $W$;
3. $Q_{a,v}$ is identified with $B_v$ at every place in the prescribed Hecke set, and (4.7)
   supplies the resulting derived-group identification;
4. outside a recorded finite bad set these identifications carry the chosen hyperspecial
   subgroups to one another;
5. $W$ is anisotropic, and the rational multiplier and every finite central quotient used later
   are specified.

The definition deliberately distinguishes exact group matching from matching only after passing
to adjoint groups. In the construction just given the derived groups themselves are isomorphic;
there is no hidden finite kernel in (4.7).

**Proposition 4.2.** Let $B/F$ be split at exactly the real places $v_1,v_2$, and let $S$
contain its finite ramification and the finite Hecke comparison set. There are a CM extension
$K/F$, scalars $a,b\in F^\times$, and a finite auxiliary set $T$ disjoint from $S$ such that
$W=b\langle1,-a\rangle$ has signatures (2.3), is anisotropic, and

$$
\operatorname{SU}(W)_{F_v}\simeq\operatorname{SL}_1(B_v)
\quad(v\in S).                                                    \tag{4.9}
$$

At every finite $v\notin S\cup T$, both sides are split and the isomorphism identifies their
hyperspecial conjugacy classes.

**Proof strategy.** Prescribe the local norm-classes of $B$, use two auxiliary places only when
they are needed for anisotropy, and then apply the explicit isomorphism (4.7).

**Proof.** Choose two auxiliary finite places $t_1,t_2$ outside $S$. Weak approximation applied to
a square-class parameter constructs a totally imaginary quadratic extension $K/F$ which is a
field at $t_1,t_2$ and at every $v\in S$ for which $B_v$ is division. Prescribe the local class
of $a$ to be a norm when $B_v$ is split and a non-norm when $B_v$ is division. At a real place
prescribe $a>0$ at $v_1,v_2$ and $a<0$ elsewhere. These classes have character product $1$
because they are exactly the local split/division invariants of the global quaternion algebra
$B$. If one of them is already a non-norm, prescribe norms at $t_1,t_2$. If all are norms, then
$B$ is everywhere split and $F$ has only the two active real places; prescribe non-norms at both
$t_1,t_2$. In either case the product remains $1$ and at least one localization is anisotropic.

The norm-character reciprocity exact sequence used in Theorem 2.1 now gives $a\in F^\times$
with exactly these prescribed local classes and the trivial class elsewhere. Weak approximation
chooses $b$ with the signs selecting the required definite orientations. The prescribed
non-norm localization, auxiliary only in the everywhere-split case, makes $W$ anisotropic by
the calculation following (2.5). Equations (4.7) and
(4.8) give (4.9). Away from the finite ramification of $K$, $a$, the chosen lattices, and $2$,
both reductive groups are unramified; the same split root datum identifies their hyperspecial
conjugacy classes. Enlarge $T$ by all such exceptional places outside $S$; the exceptional
places in $S$ are already recorded there. $\square$

For the PEL realization one may now take the endomorphism algebra to be simply $D=K$ with
$*=c$, the module $V=W$, and the Hermitian form $\Phi=\langle\ ,\ \rangle$. Its connected
rational similitude group is exactly $G$, not merely a group mapping to $G$ with finite central
kernel. Morita or corestriction realizations can be substituted, but then their commutant and
central kernel must be recalculated and recorded; they are not consequences of the present
rank-one calculation.

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

The required signs of $\alpha$ exist. Start with one nonzero $\alpha_0$ satisfying
$c(\alpha_0)=-\alpha_0$; every element of the anti-invariant line is $u\alpha_0$ with
$u\in F$. Weak approximation chooses the signs of $u$ independently at the real places. Choose
them, together with the orientations in (2.3), so that (5.3) is symmetric positive definite.
Then $h$ makes $V$ a polarized rational Hodge structure of types $(-1,0)$ and $(0,-1)$.
Writing $J_h=h(i)$, form the quotient

$$
A_h=(V_{\mathbf R},J_h)/\Lambda                                  \tag{5.4}
$$

for a compatible full lattice $\Lambda$. It is a complex abelian variety. More
invariantly, the Hodge filtration and lattice define the complex torus, while positivity of
(5.3) supplies an ample Riemann form.

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

The form (5.5) is perfect and alternating in every characteristic. Thus hyperbolic enlargement
repairs the parity without changing the adjoint group. It may, however, enlarge the commutant
and leave a central kernel in the action. In any realization using this variant, the kernel must
be divided out or detected by an auxiliary faithful summand and recorded explicitly.

### 5.4 PEL realizability

**Definition 5.2.** A strange realization is **PEL-exact** if the identity component of

$$
\{g\in\operatorname{GL}_D(V):\psi(gx,gy)=\nu(g)\psi(x,y),
\ \nu(g)\in\mathbf G_m\}                                      \tag{5.8}
$$

is precisely the chosen central modification of $G$, and not a larger group.

This condition rules out missing tensors. It is checked after algebraic closure by double centralizers: the centralizer of the prescribed semisimple algebra in $\operatorname{End}(V)$ must be exactly the algebra generating the intended group, and the adjoint equation must impose exactly its unitary involution. Because equality of closed subgroup schemes can be checked faithfully flatly, the split calculation descends.

For the standard realization of Definition 4.1 this exactness is immediate but worth verifying.
Here $\operatorname{GL}_D(V)=\operatorname{GL}_K(W)$. If a $K$-linear $g$ satisfies
$\psi(gx,gy)=\nu\psi(x,y)$ with $\nu\in\mathbf Q^\times$, replace $y$ successively by $ky$ for
$k\in K$. Nondegeneracy of the trace pairing then forces

$$
\Phi(gx,gy)=\nu\Phi(x,y)
$$

for all $x,y$. Thus the tensor stabilizer is exactly $G$ of (3.1), and its action on $W$ is
faithful. A hyperbolic or Morita variant still requires the separate centralizer calculation in
the definition.

**Theorem 5.3.** A PEL-exact strange realization gives a faithful morphism of Shimura data

$$
(G,X)\longrightarrow(\operatorname{GSp}(V,\psi),\mathfrak H_V), \tag{5.9}
$$

whose Hodge structures are polarized of weight one.

**Proof.** Equations (5.1)--(5.3) give the symplectic representation, Hodge types, and positivity. PEL-exactness identifies its tensor stabilizer with $G$. Therefore conjugating $h$ in $G(\mathbf R)$ produces exactly the intended subdomain of Siegel space, proving that (5.9) is a morphism of Shimura data. Faithfulness is part of the realization, after treatment of the finite central kernel. $\square$

## 6. Integral PEL data and the moduli problem

The rational construction produces the generic Shimura datum. To obtain a moduli scheme we choose integral tensors. These choices are auxiliary but cannot be omitted: they determine polarization degree, level, and the set of primes at which the naive local model is trustworthy.

### 6.1 Orders, lattices, and the good base

Choose a $*$-stable order $\mathcal O_D\subset D$, an $\mathcal O_D$-stable lattice
$\Lambda\subset V$, and a positive integer $m_\psi$ for which $m_\psi\psi$ is integral on
$\Lambda$. Let $\Lambda^\#$ be the dual lattice. Fix the finite group type
$\Lambda^\#/\Lambda$ that the polarization kernel is to model.

Let $S_{\mathrm{bad}}$ contain:

- $2$ and every prime ramified in $K$, $D$, or $\mathcal O_D$;
- primes where $\Lambda$ is not of the prescribed self-dual type;
- primes dividing $m_\psi$ or the polarization degree;
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

between $m_\psi\psi$ and $e_N^\lambda$. General compact open level is the orbit of a
prime-to-bad adelic trivialization under $C$. The multiplier of (6.4) must agree with the
polarization convention; dropping it would replace $G$ by an isometry subgroup.

## 7. The determinant and signature conditions

The abelian dimension and the algebra action do not determine the Hodge cocharacter. The determinant law records the multiplicities of every complex embedding, including the definite orientations that contribute no tangent direction.

### 7.1 The universal polynomial law

Let

$$
V_{\mathbf C}=V^{-1,0}\oplus V^{0,-1}
$$

be the Hodge decomposition. With the homology convention, let $W_h$ be the quotient modeling
$\operatorname{Lie}A$. Choose a $\mathbf Z$-basis $e_1,\ldots,e_s$ of $\mathcal O_D$ and define

$$
P_h(T;X_1,\ldots,X_s)=
\det\left(T-\sum_iX_ie_i\mid W_h\right).                          \tag{7.1}
$$

Its coefficients lie in the reflex field $E$ and, after enlarging $S_{\mathrm{bad}}$, in $R$. The determinant condition on (6.1) is

$$
\det\left(T-\sum_iX_i\iota(e_i)\mid\operatorname{Lie}A\right)
=P_h(T;X_1,\ldots,X_s).                                           \tag{7.2}
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

**Proof.** It is enough to work on a geometric fiber. By Section 8.2 the group of
polarization-preserving automorphisms is finite, so $u$ has finite order. Choose an odd prime
$p\mid N$, if one exists; otherwise $4\mid N$. On the $p$-adic Tate module, $u$ is congruent to
$1$ modulo $p$ in the first case and modulo $4$ in the second.

We recall the torsion-congruence lemma. If a finite-order matrix
$\gamma\in\operatorname{GL}_n(\mathbf Z_p)$ is congruent to $1$ modulo $p$ for odd $p$, or
modulo $4$ for $p=2$, then $\gamma=1$. Indeed, after taking a power one may suppose that
$\gamma$ has prime order $q$. Write $\gamma=1+p^eM$ with $M\not\equiv0\pmod p$, where $e\ge1$
and $e\ge2$ if $p=2$. If $q\ne p$, the first nonzero term in
$(1+p^eM)^q-1$ has valuation $e$; if $q=p$, it has valuation $e+1$. All remaining terms have
larger valuation, also for $p=2$ because $e\ge2$, a contradiction.

Thus $u$ is the identity on one Tate module. The action of $\operatorname{End}(A)$ on that Tate
module is faithful, so $u=1$. The exclusion of level $2$ is sharp: $-1$ acts trivially on
$A[2]$. $\square$

A neat adelic level gives the same conclusion provided it detects the center. Adjoint neatness alone can leave central torsion.

### 8.4 The fine moduli scheme

**Theorem 8.3.** At full level $N\ge3$, or at a center-detecting neat level, the PEL functor is represented by a quasi-projective $R$-scheme $M_C$ carrying a universal object.

**Proof strategy.** Use a canonical ample power to enter a Hilbert scheme, impose the extra
structures by locally closed equations, pass through the framed quotient stack, and then use
trivial inertia and the finite map to fine Siegel moduli.

**Proof.** A fixed polarization type bounds the Hilbert polynomial of a sufficiently high canonical symmetric power. A projective frame embeds every object in one fixed projective space, giving a finite-type Hilbert parameter scheme. The group law, zero section, $\mathcal O_D$-action, polarization, and level are represented by morphisms and finite schemes; their identities are closed conditions. Smoothness and geometric connectedness of the fibers are open, as is relative ampleness. Proposition 7.1 cuts out the determinant locus, and the orientation condition selects an open-and-closed part.

Changing the frame gives an algebraic quotient stack. Proposition 8.2 makes its geometric
inertia trivial, hence it is an algebraic space. The forgetful morphism to fine Siegel moduli is
finite: in a fixed polarized Hom lattice, Rosati positivity bounds the images of a fixed set of
generators of $\mathcal O_D$, the ring relations are closed, and the compatible finite level
structures form a finite scheme. A finite algebraic space over a quasi-projective scheme is a
scheme and is quasi-projective. It represents the set-valued functor, and the identity morphism
therefore supplies the universal object. $\square$

## 9. The local model of the surface

Representability does not yet show that the generic fiber is a surface. Its dimension comes from lifting the Hodge filtration. Semisimplicity separates the real labels, and exactly two rank-one lines move.

### 9.1 Lifting the Hodge filtration

Let $S_0\hookrightarrow S$ be a square-zero thickening of $E$-schemes and let $A_0/S_0$ be a PEL object. Write

$$
0\longrightarrow F_0\longrightarrow H_{1,\mathrm{dR}}(A_0/S_0)
\longrightarrow\operatorname{Lie}A_0\longrightarrow0.            \tag{9.1}
$$

Let $H$ denote the canonical vector bundle over $S$ in the characteristic-zero Hodge chart of
Book 127; its restriction to $S_0$ is the middle term of (9.1), with its action and pairing. The
Hodge-filtration deformation theorem there gives a functorial bijection between deformations of
the PEL object and locally direct-summand lifts $F\subset H$ of $F_0$ satisfying
the tensor conditions. Concretely, the action lifts exactly when $F$ is
$\mathcal O_D$-stable, the polarization lifts exactly when $F$ is isotropic, the
prime-to-characteristic level lifts uniquely, and (7.2) fixes the ranks of $H/F$. These are the
precise hypotheses of the inherited theorem; the existence of the abelian deformation is not
being inferred merely from a lift of vector bundles. Characteristic zero makes $D$ semisimple
and splits the multiplicity summands used below.

### 9.2 Two moving lines

After extension to $\mathbf C$ and Morita equivalence, the piece at an active place is

$$
P\otimes U_i,
$$

where $P$ is the fixed simple module for the matrix algebra and $U_i$ is two-dimensional. An
admissible Hodge submodule is $P\otimes L_i$ for a line $L_i\subset U_i$. Therefore the local
model at $v_i$ is

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
\mathbf C[[z_1,z_2]].                                             \tag{9.5}
$$

The framed deformation space adds smooth trivialization coordinates and quotienting removes the same coordinates. Hence, after a finite residue-field extension, the completed local ring of $M_{C,E}$ is $E'[[z_1,z_2]]$. Making one active place definite removes one variable; making a third place indefinite adds one. These variations verify the dimension formula directly.

### 9.3 Smoothness and dimension two

**Theorem 9.1.** The generic fiber $M_{C,E}$ is smooth of pure dimension two.

**Proof.** The framed de Rham torsor maps smoothly to both $M_{C,E}$ and the local model $G_E/P_\mu$. Over $\mathbf C$, the latter is (9.3), hence smooth of dimension two. Smoothness descends through the smooth surjective framed torsor, and relative dimensions cancel. Equivalently, every infinitesimal deformation is the independent lifting of the two lines in (9.4); line Grassmannians are smooth, so all square-zero obstructions vanish and the tangent rank is two. Finite presentation converts formal smoothness to smoothness. $\square$

Pure dimension holds on every component. Smoothness gives regularity and normality.

### 9.4 Cotangent and determinant lines

After a finite splitting extension $E'/E$, let
$\mathcal L_i\subset\mathcal U_i$ be the two universal active lines. On the local model,

$$
\Omega^1_i\simeq
\mathcal L_i\otimes(\mathcal U_i/\mathcal L_i)^\vee
\simeq\mathcal L_i^{\otimes2}\otimes(\det\mathcal U_i)^{-1}.    \tag{9.6}
$$

Thus over $E'$,

$$
\Omega^1_{M_{C,E'}/E'}\simeq\Omega^1_1\oplus\Omega^1_2,         \tag{9.7}
$$

and

$$
\det\Omega^1_{M_{C,E'}/E'}\simeq
\mathcal L_1^{\otimes2}\otimes\mathcal L_2^{\otimes2}
\otimes(\det\mathcal U_1\det\mathcal U_2)^{-1}.                 \tag{9.8}
$$

The two summands can be permuted by $\operatorname{Gal}(E'/E)$, so neither $\mathcal L_i$ need
descend separately. Their direct sum in (9.7) and the product in (9.8) are Galois invariant and
descend to $E$; intrinsically they are $\Omega^1_{M_{C,E}/E}$ and its determinant. The
determinant factors are multiplier lines and may be trivialized only if the level has actually
reduced the corresponding similitude. On an lci integral locus, (9.8) must be interpreted
through $\operatorname{Det}(L_{M_C/R})$, not through a possibly non-locally-free top exterior
power of differentials.

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

**Proof.** The symplectic morphism (5.9) gives finite morphisms from both the PEL model and the
canonical Shimura model to the same fine Siegel moduli scheme. The analytic identification
(10.1) gives a graph inside their fiber product over Siegel space. Its reduced algebraic closure is a
closed subscheme of that fiber product, and each projection is finite because the opposite
factor is finite over Siegel space. On every selected component the projections are birational.
Both models are normal, the PEL scheme by Theorem 9.1 and the canonical model by construction,
so both finite birational projections are isomorphisms. This identifies the two models
canonically.

The isomorphism respects descent: at a special point $[h,g]$, CM reciprocity sends

$$
[h,g]^{\operatorname{Art}_{E(h)}(s)}=[h,r_h(s_f)g],              \tag{10.2}
$$

which is the lattice action on the PEL abelian variety. Density of special points makes the descended isomorphism unique. $\square$

### 10.4 Projectivity

**Corollary 10.3.** If $W$ is anisotropic over $F$, every neat required component is a smooth projective surface over its field of definition.

**Proof.** It is smooth of dimension two by Theorem 9.1. Proposition 3.2 makes its complex
analytification compact. Embed the quasi-projective variety as an open dense subvariety of a
projective closure. Its compact analytic image is closed in that Hausdorff analytic closure;
being also dense, it is the whole closure. The variety is therefore proper over $\mathbf C$.
Properness descends along field extensions, and a proper quasi-projective variety is projective.
$\square$

## 11. The modèles étranges comparison

The construction is now geometric. We next state precisely how it retains quaternionic automorphic information. The comparison is between finite-adelic derived groups and their Hecke algebras; it is not an identification of universal abelian varieties.

### 11.1 Finite-adelic matching

Let $H_B=\operatorname{SL}_1(B)$ and $H_U=\operatorname{SU}(W)$ be $F$-groups, and let $G_B$
and $G$ denote the quaternionic and unitary central modifications over $\mathbf Q$. Their
derived groups are the restrictions of scalars of $H_B$ and $H_U$.
Fix a finite set $\Sigma$ containing every place where either group, algebra, level, or central
map is ramified. A strange realization gives, for $v\notin\Sigma$, isomorphisms

$$
H_B(F_v)\simeq H_U(F_v)                                         \tag{11.1}
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

**Proposition 11.1.** Let $f:H\to G$ be a central isogeny compatible with Shimura data and put
$Z=\ker f$. For compatible sufficiently small neat levels $C_H$ and $C$, the induced map of
Shimura varieties is finite étale onto an open-and-closed union. Its image and fibers are
computed from the adelic double-coset map; failure of a rational or adelic point to lift is
measured by the corresponding $H^1$ of $Z$.

If a target point has a chosen adelic lift and every rational identification between two such
lifts itself lifts to $H(\mathbf Q)$, its fiber is

$$
Z(\mathbf Q)\backslash Z(\mathbf A_f)/(Z(\mathbf A_f)\cap C_H). \tag{11.3}
$$

In particular, when $C_H=f^{-1}(C)$, the set (11.3) is a singleton. Any non-surjectivity then
occurs through missing image components, not through a fictitious extra kernel fiber.

**Proof.** A central isogeny identifies adjoint symmetric domains and is a local isomorphism.
The induced map of arithmetic quotients has finite fibers and an image which is a union of
components; at sufficiently small compatible neat levels no nontrivial finite stabilizer remains,
so it is étale. Canonical-model functoriality algebraizes this finite covering. Once one lift is
fixed, all other adelic lifts differ by $Z(\mathbf A_f)$; rational equivalence and level
equivalence give the two quotients in (11.3). Without the stated lifting hypotheses, the exact
sequence in nonabelian cohomology supplies an obstruction in $H^1(\mathbf Q,Z)$ or
$H^1(\mathbf A_f,Z)$, so the kernel quotient alone is not an exact fiber formula. $\square$

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

For the present unitary datum, the determinant--multiplier torus calculation and weak
approximation from Book 126 show that $G(\mathbf Q)$ acts transitively on $\pi_0(X)$. Fix
$X^+\subset X$ and put

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

Let $C_0$ be a geometric connected component and let $E_\infty^{\times,0}$ be the identity
component of $E_\infty^\times$. Its stabilizer in the idele class group is

$$
U_{C_0}=
\frac{E^\times\bigl(E_\infty^{\times,0}\times
r_{(G,X),f}^{-1}(T(\mathbf Q)^\dagger\nu_T(C))\bigr)}{E^\times}
\subset\mathbf A_E^\times/E^\times.                             \tag{12.5}
$$

Here the inverse image is taken in $\mathbf A_{E,f}^\times$, and the archimedean identity
component is included because global Artin reciprocity kills it. This subgroup is open: a
sufficiently small compact open in $\mathbf A_{E,f}^\times$ maps into $\nu_T(C)$. Its fixed
field $E_{C_0}$ is therefore a finite abelian extension of $E$.

**Proposition 12.1.** The component $C_0$ descends to $E_{C_0}$, and $E_{C_0}$ is its minimal field inside $\overline{\mathbf Q}$ relative to the action (12.3).

**Proof.** Formula (12.3) says that a Galois element fixes $C_0$ exactly when its idele class lies in (12.5). The component is open and closed, so its idempotent in the finite étale algebra of components descends exactly under its stabilizer. Galois descent gives a variety over the fixed field, and minimality follows from the equality of stabilizers. $\square$

The whole canonical surface is defined over $E$ even when none of its geometric components is individually defined over $E$.

### 12.4 Selecting the required union

Polarization type, lattice genus, determinant orientation, and central multiplier define subsets of (12.1). A PEL model over $E$ must select a Galois-stable union under (12.3), not an arbitrary geometric component. A single component becomes legitimate after base change to its field (12.5). Because the fine moduli functor is preserved by the corresponding idempotent, the universal abelian scheme restricts and descends over the same field.

## 13. Levels, universal families, and Hecke maps

The strange construction is useful only as a tower. Fine levels carry universal objects,
arbitrary levels are finite quotients, and rational adelic elements produce quasi-isogeny
correspondences compatible with canonical descent.

### 13.1 Fine and coarse levels

If $C'\triangleleft C$ is neat and normal, put $\Delta=C/C'$ and let
$\Delta_{\mathrm{eff}}$ be its image in $\operatorname{Aut}(M_{C'})$. Rational central
elements can lie in the kernel, and that ineffective kernel remains as inertia in the stack.
Thus

$$
\mathscr M_C\simeq[M_{C'}/\Delta],                               \tag{13.1}
$$

and the coarse space is the finite quotient $M_{C'}/\Delta_{\mathrm{eff}}$. At a non-neat level,
stabilizers can produce quotient singularities. The universal family descends to the coarse
quotient only when every stabilizer acts trivially on the entire PEL object. A power of a Hodge
line can descend even when the family does not.

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

is locally free and carries the determinant law (7.2). After a finite splitting extension of
$E$, it decomposes into the active and definite multiplicity pieces. The active lines there are
the $\mathcal L_i$ of Section 9.4; only their Galois-invariant combinations are asserted to
descend to $E$.

### 13.3 Hecke isogenies

For $a\in G(\mathbf A_f)$, put $C_a=C\cap aCa^{-1}$. The two maps

$$
M_{C_a}\rightrightarrows M_C                                    \tag{13.4}
$$

forget level directly and after translating it by $a$. The lattice
$\widehat\Lambda\cap a\widehat\Lambda$ has finite index in both lattices. Passing to the fine
level which remembers this common lattice produces two finite isogenies to the two pullbacks in
(13.4), and hence a universal quasi-isogeny between them. Equivalently, after multiplying the
quasi-isogeny by a positive central integer, it becomes an isogeny whose kernel is finite locally
free. Quotients by such subgroup schemes exist and commute with base change, so the construction
is algebraic on the generic tower.

The polarization on the quotient is determined by its pullback. When a principal polarization is to remain principal, the kernel must be Lagrangian for the induced Weil pairing; isotropy, not merely its numerical order, is the correct hypothesis.

### 13.4 Descent of correspondences

**Proposition 13.1.** The generic Hecke correspondence (13.4) and its universal quasi-isogeny
descend over the reflex field, or over the common component field after selecting individual
components. After a central integral scaling, the resulting universal isogeny descends as well.

**Proof.** At a special point, the reciprocity multiplier acts on the left, whereas Hecke translation acts on the right:

$$
r_h(s_f)(ga)=(r_h(s_f)g)a.
$$

Thus the correspondence commutes with Galois on the dense set of special points.
Canonical-model uniqueness descends its two maps. At the common fine level, the two finite
lattice kernels are preserved by the same action, so descent of morphisms gives both isogenies
and hence their intervening quasi-isogeny. A central scaling is Galois invariant. Restricting to
components uses (12.5). $\square$

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
- an exact good-place finite-adelic comparison with the prescribed quaternionic derived group;
- component fields and central-character bookkeeping.

It does not prove a Matsushima formula, multiplicity one, an automorphic decomposition of $H^2$, construction of Galois representations, integral comparison, or local-global compatibility. Those conclusions require harmonic analysis and integral geometry beyond the construction itself. Nothing in Chapters 1--13 depends on them.

## 15. Construction theorem and hypothesis ledger

We finish by assembling the argument into one reusable theorem. Its detailed hypotheses prevent the common errors: confusing moduli and abelian dimensions, forgetting the determinant orientation, replacing the abelianization by the multiplier, and descending a component over too small a field.

### 15.1 The complete construction theorem

**Theorem 15.1 (unitary surface and modèles étranges package).** Let $F$ be totally real and let
$B/F$ be a quaternion algebra prescribing rank-one finite local inner forms. Choose the CM
extension $K/F$ and the scalars of Proposition 4.2. Assume:

1. a Hermitian plane has signature $(1,1)$ at exactly two real places and definite oriented signature elsewhere;
2. its local invariants satisfy the global product relation and it is anisotropic over $F$;
3. the explicit strange realization of Proposition 4.2 matches $B^1$ at the prescribed finite
   places; if a Morita or corestriction variant replaces it, that variant is separately proved
   PEL-exact and its finite central kernel and rational multiplier are specified;
4. the associated rational form is alternating, either directly or after the explicit hyperbolic repair;
5. $\mathcal O_D$, $\Lambda$, polarization type, determinant law, orientation, and a center-detecting neat compact open $C$ are fixed away from a finite bad set.

Then:

1. $(G,X)$ is a Shimura datum of dimension two, with reflex field equal to the stabilizer field of the full signature function $r_\varphi$.
2. The PEL groupoid is an fpqc algebraic stack with finite unramified separated diagonal. At the stated fine level it is represented by a quasi-projective scheme $M_C$ with a universal PEL abelian scheme.
3. The generic required union $M_{C,E}^{\mathrm{req}}$ is smooth of pure dimension two. Its geometric local model is $\mathbf P^1\times\mathbf P^1$, and its cotangent determinant is (9.8).
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
6. At matching finite places, the derived group and spherical Hecke algebra agree with those of
   $B^1$. Central kernels, lifting obstructions, and torus characters are retained through
   (11.2)--(11.3).
7. Level maps and generic Hecke correspondences descend canonically. At a common fine level the
   two lattice inclusions give universal isogenies and hence the Hecke quasi-isogeny; arbitrary
   levels are finite quotient stacks and coarse schemes, on which the universal family need not
   descend.

**Proof.** Proposition 4.2, using Theorem 2.1, constructs the global anisotropic Hermitian
input, and Proposition 2.2 supplies the compactness criterion. Propositions 3.1 and 3.2 give the
Shimura datum, dimension, reflex field, and compactness. Chapters 4 and 5 construct and verify
the PEL-exact symplectic realization. Proposition 8.1, Proposition 8.2, and Theorem 8.3 give the
stack and fine scheme. The Hodge-lifting calculation and (9.3) prove generic smoothness and the
cotangent formulas. Theorem 10.1 and Proposition 10.2 identify the PEL scheme with the canonical
model, while Corollary 10.3 proves projectivity. Chapter 11 proves finite-adelic matching.
Formula (12.1), reciprocity (12.3), and Proposition 12.1 establish the component and descent
statements. Chapter 13 treats levels and Hecke maps. $\square$

### 15.2 Exact hypotheses and failure modes

| Claim | Required input | Failure without it |
|---|---|---|
| two-dimensional domain | exactly two signatures $(1,1)$ | abelian dimension does not determine Shimura dimension |
| stated reflex field | full function $r_\varphi$, including definite orientations | remembering only active places can give a field that is too small |
| global Hermitian plane | determinant compatibility and product relation | prescribed local spaces need not globalize |
| compact surface | anisotropy over $F$ | isotropic lines produce parabolics and cusps |
| quaternionic comparison | cyclic-algebra norm classes and the explicit isomorphism (4.7) | a CM scalar extension alone does not determine the desired group |
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

The modèles étranges construction then supplies the bridge to quaternionic automorphic data.
The cyclic quaternion algebra $(K/F,a)$ and the binary Hermitian plane
$b\langle1,-a\rangle$ have isomorphic norm-one and special-unitary groups by the explicit matrix
calculation (4.5). The alternating trace form gives a PEL-exact symplectic realization. A Morita
or corestriction variant is legitimate only after its centralizer and kernel are recalculated.
Hyperbolic enlargement repairs an even tensor sign when necessary, while central kernels and
auxiliary torus characters remain visible.

The resulting PEL stack has finite diagonal; deep level makes it a fine quasi-projective scheme with a universal abelian family. Its Hodge filtration has exactly two moving lines, so the local model is $\mathbf P^1\times\mathbf P^1$ and the generic fiber is a smooth surface. Complex uniformization identifies the required PEL union with the canonical model, and anisotropy makes it projective.

Finally, descent is controlled by the entire abelianized torus. Components form the quotient (12.1), arithmetic reciprocity acts by left multiplication, and an individual component lives over the finite abelian field cut out by its stabilizer. Fine-level Hecke isogenies and all generic correspondences descend compatibly. The output is therefore the precise geometric carrier needed for degree-two realization: compact unitary surfaces, exact auxiliary PEL varieties, quaternionic finite-place matching, universal families at fine level, and component-correct canonical descent.
