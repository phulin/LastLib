# Central Automorphic Descent and Multiplicity for PEL Similitude Groups

## Contents

1. [The full-group problem](#1-the-full-group-problem)
   - [1.1 The gap left by a derived-group comparison](#11-the-gap-left-by-a-derived-group-comparison)
   - [1.2 Standing surface datum](#12-standing-surface-datum)
   - [1.3 Inputs, outputs, and the noncircular boundary](#13-inputs-outputs-and-the-noncircular-boundary)
   - [1.4 A map of the proof](#14-a-map-of-the-proof)
2. [The exact algebraic groups](#2-the-exact-algebraic-groups)
   - [2.1 The rational-multiplier unitary group](#21-the-rational-multiplier-unitary-group)
   - [2.2 Center, derived group, and abelianization](#22-center-derived-group-and-abelianization)
   - [2.3 The finite derived-center cover](#23-the-finite-derived-center-cover)
   - [2.4 The common-norm quaternionic group](#24-the-common-norm-quaternionic-group)
   - [2.5 The norm-one quotient of the full group](#25-the-norm-one-quotient-of-the-full-group)
   - [2.6 The obstruction-free auxiliary cover](#26-the-obstruction-free-auxiliary-cover)
   - [2.7 Dimensions, centers, kernels, and quotients](#27-dimensions-centers-kernels-and-quotients)
3. [Rational, local, and adelic images](#3-rational-local-and-adelic-images)
   - [3.1 The boundary class of the finite central cover](#31-the-boundary-class-of-the-finite-central-cover)
   - [3.2 The exact rational image](#32-the-exact-rational-image)
   - [3.3 Local and adelic obstruction tuples](#33-local-and-adelic-obstruction-tuples)
   - [3.4 The common-norm square-class obstruction](#34-the-common-norm-square-class-obstruction)
   - [3.5 Why the auxiliary cover is surjective on points](#35-why-the-auxiliary-cover-is-surjective-on-points)
   - [3.6 Actual torus images and compact class quotients](#36-actual-torus-images-and-compact-class-quotients)
   - [3.7 The finite-level obstruction quotient](#37-the-finite-level-obstruction-quotient)
4. [Measures, centers, and levels](#4-measures-centers-and-levels)
   - [4.1 Coherent Haar measures](#41-coherent-haar-measures)
   - [4.2 Fixed central-character automorphic spaces](#42-fixed-central-character-automorphic-spaces)
   - [4.3 The positive split center and the real stabilizer](#43-the-positive-split-center-and-the-real-stabilizer)
   - [4.4 Compatible quaternionic-character pairs](#44-compatible-quaternionic-character-pairs)
   - [4.5 Pair equivalence through the actual quotient](#45-pair-equivalence-through-the-actual-quotient)
   - [4.6 The compact quotient level](#46-the-compact-quotient-level)
5. [Clifford theory with rational packet selection](#5-clifford-theory-with-rational-packet-selection)
   - [5.1 The finite factor-set calculation](#51-the-finite-factor-set-calculation)
   - [5.2 Restriction multiplicity and the radical](#52-restriction-multiplicity-and-the-radical)
   - [5.3 Abstract and automorphic self-twists](#53-abstract-and-automorphic-self-twists)
   - [5.4 The automorphic period module](#54-the-automorphic-period-module)
   - [5.5 The global sign formula](#55-the-global-sign-formula)
   - [5.6 Typewise passage to adelic representations](#56-typewise-passage-to-adelic-representations)
6. [Restriction to the common-norm group](#6-restriction-to-the-common-norm-group)
   - [6.1 The exact norm quotient](#61-the-exact-norm-quotient)
   - [6.2 Restriction packets and possible cocycles](#62-restriction-packets-and-possible-cocycles)
   - [6.3 Automorphic ascension and exhaustion](#63-automorphic-ascension-and-exhaustion)
   - [6.4 The exact multiplicity module](#64-the-exact-multiplicity-module)
   - [6.5 The Jacquet--Langlands interface](#65-the-jacquet--langlands-interface)
7. [Descent to the full PEL group](#7-descent-to-the-full-pel-group)
   - [7.1 Pullback across the auxiliary cover](#71-pullback-across-the-auxiliary-cover)
   - [7.2 Ascending to a product representation](#72-ascending-to-a-product-representation)
   - [7.3 The local norm-kernel self-twists](#73-the-local-norm-kernel-self-twists)
   - [7.4 Cancellation of the Clifford cocycle](#74-cancellation-of-the-clifford-cocycle)
   - [7.5 Global packet selection and multiplicity](#75-global-packet-selection-and-multiplicity)
   - [7.6 Classification and uniqueness](#76-classification-and-uniqueness)
   - [7.7 The character spectrum](#77-the-character-spectrum)
8. [Finite level, Hecke action, and components](#8-finite-level-hecke-action-and-components)
   - [8.1 The exact invariant projector](#81-the-exact-invariant-projector)
   - [8.2 Lifted Hecke spans](#82-lifted-hecke-spans)
   - [8.3 Good-place polynomials](#83-good-place-polynomials)
   - [8.4 Bad places and old level](#84-bad-places-and-old-level)
   - [8.5 The full component set](#85-the-full-component-set)
   - [8.6 Component-character mixing and proper support](#86-component-character-mixing-and-proper-support)
9. [Matsushima in the fixed central sector](#9-matsushima-in-the-fixed-central-sector)
   - [9.1 Automorphic cochains on the compact surface](#91-automorphic-cochains-on-the-compact-surface)
   - [9.2 A direct compact-Hodge proof](#92-a-direct-compact-hodge-proof)
   - [9.3 The archimedean Clifford projector](#93-the-archimedean-clifford-projector)
   - [9.4 Full-orbit and proper-support formulas](#94-full-orbit-and-proper-support-formulas)
   - [9.5 The character contribution](#95-the-character-contribution)
10. [Coefficient fields and compatible realizations](#10-coefficient-fields-and-compatible-realizations)
   - [10.1 Fields attached to a compatible pair](#101-fields-attached-to-a-compatible-pair)
   - [10.2 The finite geometric Hecke algebra](#102-the-finite-geometric-hecke-algebra)
   - [10.3 Projectors and splitting fields](#103-projectors-and-splitting-fields)
   - [10.4 Betti, de Rham, and etale compatibility](#104-betti-de-rham-and-etale-compatibility)
   - [10.5 Galois and Frobenius assertions with their hypotheses](#105-galois-and-frobenius-assertions-with-their-hypotheses)
11. [The central descent theorem](#11-the-central-descent-theorem)
   - [11.1 Complete statement](#111-complete-statement)
   - [11.2 Proof](#112-proof)
12. [Failure tests and worked patterns](#12-failure-tests-and-worked-patterns)
   - [12.1 A missed rational point](#121-a-missed-rational-point)
   - [12.2 A noncompact pullback level](#122-a-noncompact-pullback-level)
   - [12.3 Local packets with one global parity equation](#123-local-packets-with-one-global-parity-equation)
   - [12.4 Packet size, oldvectors, and automorphic multiplicity](#124-packet-size-oldvectors-and-automorphic-multiplicity)
   - [12.5 A component projector that mixes spectral summands](#125-a-component-projector-that-mixes-spectral-summands)
13. [Dependency and interface audits](#13-dependency-and-interface-audits)
   - [13.1 Exact direct dependency row](#131-exact-direct-dependency-row)
   - [13.2 Imported-result audit](#132-imported-result-audit)
   - [13.3 Moving-interface audit](#133-moving-interface-audit)
14. [Final audit and readiness](#14-final-audit-and-readiness)
   - [14.1 Hypothesis and failure ledger](#141-hypothesis-and-failure-ledger)
   - [14.2 Symbol, measure, level, circularity, and repair-diff audit](#142-symbol-measure-level-circularity-and-repair-diff-audit)
   - [14.3 Counts](#143-counts)
   - [14.4 Verdict](#144-verdict)

## 1. The full-group problem

### 1.1 The gap left by a derived-group comparison

A quaternion algebra can identify the derived group of a unitary Shimura surface without
identifying the automorphic theory of its full similitude group.  The missing information is
not decorative.  It includes the rational common multiplier, the full CM center, the finite
kernel between the center and the derived group, the image of rational and adelic points, and
the characters by which a quaternionic representation is allowed to cross those groups.

Three tempting shortcuts fail for different reasons.

First, an isomorphism

$$
G^{\mathrm{der}}\simeq\operatorname{Res}_{F/\mathbf Q}D^1
$$

does not identify representations of $G$.  A representation of the derived group may have
several central ascensions, or none with a prescribed central character.  Second, the finite
central map $G^{\mathrm{der}}\times Z_G\to G$ need not be onto on rational or adelic points.
Its failure is an explicit $H^1$ class.  Third, restriction across an abelian quotient is a
Clifford-theory problem.  Local self-intertwiners can carry a factor set, while rational
automorphy imposes a product condition on the local packet labels.  Packet size, restriction
multiplicity, fixed-vector dimension, and the number of connected components are four distinct
integers.

This book solves those problems for the rational-multiplier PEL group attached to the
anisotropic Hermitian plane of the unitary-surface construction.  It also proves the compact
Matsushima formula needed in degree two, with a fixed central character and the correct real
stabilizer.  No later automorphic decomposition of that surface is used.

### 1.2 Standing surface datum

Let $F$ be totally real of degree

$$
d=[F:\mathbf Q],
$$

let $K/F$ be CM with conjugation $c$, and choose $a,b\in F^\times$.  Put

$$
W=b\langle 1,-a\rangle,
\qquad
D=Q_a=(K/F,a)=K\oplus Kj,
$$

where $j^2=a$ and $jx=c(x)j$.  We assume the exact surface hypotheses:

- $W$ has signature $(1,1)$ at exactly two real places $v_1,v_2$ and a fixed definite
  orientation at every other real place;
- $W$ is anisotropic over $F$;
- the integral PEL datum and the center-detecting neat level are those for which the canonical
  model is a smooth projective surface on the selected component union.

The explicit embedding

$$
\iota:D\longrightarrow M_2(K),\qquad
x+yj\longmapsto
\begin{pmatrix}x&ay\\ c(y)&c(x)\end{pmatrix}                 \tag{1.1}
$$

satisfies, for $H_0=\operatorname{diag}(1,-a)$,

$$
\iota(q)^{c,\mathsf t}H_0\iota(q)
=\operatorname{Nrd}(q)H_0.                                    \tag{1.2}
$$

It therefore identifies

$$
D^1=\operatorname{SL}_1(D)\simeq\operatorname{SU}(W)          \tag{1.3}
$$

over $F$.  Anisotropy of $W$ says that $D$ is a division algebra over $F$, although it is
split at the two active real places.

For a $\mathbf Q$-algebra $R$, the full group is

$$
G(R)=\left\{
g\in\operatorname{GL}_{K\otimes_{\mathbf Q}R}(W\otimes_{\mathbf Q}R):
\langle gx,gy\rangle=\nu(g)\langle x,y\rangle,
\ \nu(g)\in R^\times
\right\}.                                                     \tag{1.4}
$$

Thus the multiplier is one element of $R^\times$, not an arbitrary element of
$(F\otimes_{\mathbf Q}R)^\times$.  We write this group as $G=G_W$ throughout.

### 1.3 Inputs, outputs, and the noncircular boundary

The quaternionic input is the arbitrary-signature global Jacquet--Langlands theorem for the
actual algebra $D=Q_a$.  It supplies a multiplicity-one noncharacter automorphic representation
$\Pi$ of $D^\times(\mathbf A_F)$, its exact local components, central character, conductor,
good raw Hecke polynomial, and parallel-weight-two coefficient field.  It does **not** supply a
representation of $G$, a restriction theorem for the common-norm subgroup, or a degree-two
surface decomposition.  All three are proved here.

The geometric input is the already constructed smooth projective unitary surface, its full
abelianized component formula, and its finite Hecke correspondences.  The comparison input is
functoriality of Betti, de Rham, and etale cohomology for admissible finite-flat lci spans.  That
comparison transports a projector after it has been constructed; it does not construct a
spectral projector or identify a rank-two Galois representation by itself.

The outputs are:

1. exact algebraic and pointwise sequences for $G$, its common-norm subgroup, and an
   obstruction-free auxiliary cover;
2. fixed-central-character automorphic spaces and an exact compatible-pair classification;
3. a typewise global Clifford formula retaining local factor sets and the rational packet
   condition;
4. multiplicity one for every individual noncharacter representation of this full $G$ which
   actually occurs, together with the exact zero-or-one occurrence test;
5. finite packet, archimedean Clifford, Hecke, and component-support projectors with their
   measures and commutation domains specified;
6. a direct, fixed-central-character Matsushima formula and its degree-two real calculation;
7. coefficient-field and realization statements with every splitting-field and Galois-stability
   hypothesis visible.

### 1.4 A map of the proof

There are two different covers and they solve two different problems:

$$
\begin{array}{ccccc}
G^{\mathrm{der}}\times Z_G&\longrightarrow&G
&\text{finite kernel}&\operatorname{Res}_{F/\mathbf Q}\mu_2,\\[2mm]
\widetilde G&\longrightarrow&G
&\text{connected kernel}&\operatorname{Res}_{F/\mathbf Q}\mathbf G_m.
\end{array}                                                     \tag{1.5}
$$

The first exposes the square-class obstruction and must not be treated as surjective on
points.  The second has vanishing $H^1$ over fields and good integral local rings; it is the
cover on which automorphic descent is carried out.

The auxiliary group $\widetilde G$ is normal in

$$
L=\operatorname{Res}_{F/\mathbf Q}D^\times
\times\operatorname{Res}_{K/\mathbf Q}\mathbf G_m.            \tag{1.6}
$$

Its quotient is an anisotropic torus.  Hence an automorphic representation of $G$ can be
pulled to $\widetilde G$, ascended across a compact actual torus image, and factored on $L$ as
$\Pi\boxtimes\chi$.  The kernel of $\widetilde G\to G$ gives the equation
$\chi|_{C_F}=\omega_\Pi$.  The remaining Clifford packet is governed locally by characters
annihilating $N_{K/F}(\mathbf A_K^\times)$.  Each local factor is cyclic of order at most two;
their tensor intertwiners commute, so the relevant factor set linearizes.  Rational automorphy
then imposes at most one quadratic product equation.  This is the mechanism behind the final
zero-or-one formula.

## 2. The exact algebraic groups

### 2.1 The rational-multiplier unitary group

Taking the $K$-determinant in (1.4) gives

$$
N_{K/F}(\det_Kg)=\nu(g)^2.                                    \tag{2.1}
$$

Over $\overline{\mathbf Q}$, choose one embedding of $K$ above each embedding of $F$.
The matrix at the conjugate embedding is then determined by the chosen matrix and the common
multiplier.  Consequently

$$
G_{\overline{\mathbf Q}}
\simeq \operatorname{GL}_{2,\overline{\mathbf Q}}^{d}
\times\mathbf G_{m,\overline{\mathbf Q}}.                     \tag{2.2}
$$

In particular, $G$ is connected reductive and

$$
\dim G=4d+1.                                                   \tag{2.3}
$$

Equation (1.3) gives

$$
G^{\mathrm{der}}
=\operatorname{Res}_{F/\mathbf Q}D^1,
\qquad
\dim G^{\mathrm{der}}=3d.                                    \tag{2.4}
$$

It is simply connected of type $A_1^d$ after algebraic closure.

### 2.2 Center, derived group, and abelianization

A central $K$-linear endomorphism is scalar multiplication by $z\in K^\times$.  It is a
rational similitude precisely when its norm is rational.  Thus

$$
Z_G=
\left\{z\in\operatorname{Res}_{K/\mathbf Q}\mathbf G_m:
N_{K/F}(z)\in\mathbf G_m\right\}.                              \tag{2.5}
$$

This is a connected torus of dimension $d+1$.  The maximal $\mathbf Q$-split subtorus is the
diagonal scalar torus

$$
A_G\simeq\mathbf G_m,
\qquad A_G(\mathbf R)^0=\mathbf R_{>0}.                        \tag{2.6}
$$

The determinant and multiplier together define

$$
t_G:G\longrightarrow T_G,qquad
t_G(g)=(\det_Kg,\nu(g)),                                      \tag{2.7}
$$

where

$$
T_G=
\left\{(\delta,q)\in
\operatorname{Res}_{K/\mathbf Q}\mathbf G_m\times\mathbf G_m:
N_{K/F}(\delta)=q^2\right\}.                                  \tag{2.8}
$$

The kernel is $G^{\mathrm{der}}$, so $T_G=G/G^{\mathrm{der}}$.  It is a connected torus of
dimension $d+1$.  This formula explains why the multiplier alone cannot compute connected
components.

### 2.3 The finite derived-center cover

Multiplication gives a central isogeny

$$
1\longrightarrow M
\longrightarrow G^{\mathrm{der}}\times Z_G
\xrightarrow{\ m_G\ }G
\longrightarrow1,                                             \tag{2.9}
$$

with

$$
M=\operatorname{Res}_{F/\mathbf Q}\mu_2,
\qquad
\epsilon\longmapsto(\epsilon,\epsilon^{-1}).                 \tag{2.10}
$$

Its geometric degree is $2^d$.  The map is an epimorphism for the fppf topology, but that
sentence says nothing about surjectivity on $\mathbf Q$-points or adelic points.  Chapter 3
computes its boundary exactly.

On the center, $t_G$ is

$$
z\longmapsto(z^2,N_{K/F}z).                                   \tag{2.11}
$$

Its kernel is again $M$.  Thus the same finite signs that occur in (2.9) also control the
difference between the center and the full abelianization.

### 2.4 The common-norm quaternionic group

Let

$$
J=\operatorname{Res}_{F/\mathbf Q}D^\times.
$$

The correct intermediary is the fiber product

$$
H=J\times_{\operatorname{Res}_{F/\mathbf Q}\mathbf G_m}\mathbf G_m,
                                                                  \tag{2.12}
$$

where the two arrows are reduced norm and the diagonal inclusion.  Thus

$$
H(R)=\left\{b\in(D\otimes_F(F\otimes_{\mathbf Q}R))^\times:
\operatorname{Nrd}(b)\in R^\times\right\}.                    \tag{2.13}
$$

Equation (1.2) embeds $H$ in $G$ with multiplier $\operatorname{Nrd}(b)$.  Its structure is

$$
\dim H=3d+1,
\qquad
H^{\mathrm{der}}=\operatorname{Res}_{F/\mathbf Q}D^1
=G^{\mathrm{der}},                                             \tag{2.14}
$$

and reduced norm is its abelianization:

$$
1\longrightarrow H^{\mathrm{der}}
\longrightarrow H\xrightarrow{\operatorname{Nrd}}\mathbf G_m
\longrightarrow1.                                             \tag{2.15}
$$

Its center is not the connected diagonal torus alone.  It is

$$
Z_H=\left\{r\in\operatorname{Res}_{F/\mathbf Q}\mathbf G_m:
r^2\in\mathbf G_m\right\}.                                   \tag{2.16}
$$

The identity component is diagonal $\mathbf G_m$, while

$$
\pi_0(Z_H)_{\overline{\mathbf Q}}
\simeq(\mu_2^d)/\mu_2,
\qquad |\pi_0(Z_H)(\overline{\mathbf Q})|=2^{d-1}.             \tag{2.17}
$$

There is a second finite central isogeny

$$
1\longrightarrow\mu_2
\longrightarrow G^{\mathrm{der}}\times\mathbf G_m
\longrightarrow H\longrightarrow1,
\qquad (u,s)\longmapsto su.                                   \tag{2.18}
$$

Its multiplier is $s^2$, a fact which will produce a square-class obstruction.

Finally put

$$
S=\bigl(\operatorname{Res}_{F/\mathbf Q}\mathbf G_m\bigr)/\mathbf G_m.
                                                                  \tag{2.19}
$$

Reduced norm modulo the diagonal gives an fppf exact sequence

$$
1\longrightarrow H\longrightarrow J
\xrightarrow{\beta_D}S\longrightarrow1.                       \tag{2.20}
$$

On rational or adelic points, the image is the actual reduced-norm image modulo rational
scalars.  It is not silently replaced by all of $S$.

### 2.5 The norm-one quotient of the full group

Define the CM norm-one torus

$$
U=\operatorname{Res}_{F/\mathbf Q}
\operatorname{Res}^{1}_{K/F}\mathbf G_m.                       \tag{2.21}
$$

For $g\in G$, equation (2.1) shows that

$$
\alpha(g)=\frac{\det_Kg}{\nu(g)}\in U.                        \tag{2.22}
$$

The kernel is exactly $H$, and the diagonal Hermitian model supplies a section

$$
s:U\longrightarrow G,
\qquad u\longmapsto\operatorname{diag}(u,1).                  \tag{2.23}
$$

Hence

$$
1\longrightarrow H\longrightarrow G
\xrightarrow{\alpha}U\longrightarrow1                        \tag{2.24}
$$

is split over $\mathbf Q$.  It is generally a semidirect product, not a central product.
The torus $U(\mathbf R)\simeq(S^1)^d$ is compact, so $U$ is $\mathbf Q$-anisotropic.

This sequence is useful for understanding components and the role of the CM center, but it is
not the best cover for automorphic descent: $H$ itself already arose by a restriction problem.
The next construction reaches $G$ directly from a product group and has no pointwise lifting
obstruction.

### 2.6 The obstruction-free auxiliary cover

Set

$$
L=J\times\operatorname{Res}_{K/\mathbf Q}\mathbf G_m
$$

and define

$$
\beta:L\longrightarrow S,
\qquad
\beta(b,z)=\bigl[\operatorname{Nrd}(b)N_{K/F}(z)\bigr].        \tag{2.25}
$$

Let

$$
\widetilde G=\ker\beta
=\left\{(b,z):
\operatorname{Nrd}(b)N_{K/F}(z)\in\mathbf G_m\right\}.        \tag{2.26}
$$

Then

$$
1\longrightarrow\widetilde G\longrightarrow L
\xrightarrow{\beta}S\longrightarrow1                         \tag{2.27}
$$

is fppf exact.  Multiplication in $M_2(K)$ gives

$$
\theta:\widetilde G\longrightarrow G,
\qquad (b,z)\longmapsto\iota(b)z.                             \tag{2.28}
$$

The kernel consists precisely of pairs

$$
r\longmapsto(r,r^{-1}),
\qquad r\in\operatorname{Res}_{F/\mathbf Q}\mathbf G_m.      \tag{2.29}
$$

Indeed, if $\iota(b)z=1$, then $\iota(b)$ is a scalar $K$-matrix.  The intersection of
$\iota(D)$ with the scalar $K$-matrices is $F$, so $b=r$ and $z=r^{-1}$.  We obtain

$$
1\longrightarrow R_F
\longrightarrow\widetilde G\xrightarrow{\theta}G
\longrightarrow1,
\qquad R_F=\operatorname{Res}_{F/\mathbf Q}\mathbf G_m.       \tag{2.30}
$$

Here

$$
\dim L=6d,
\qquad \dim\widetilde G=5d+1,
\qquad \dim R_F=d,                                             \tag{2.31}
$$

so the dimensions also verify $\dim G=4d+1$.  Unlike (2.9), this cover has an induced torus
as kernel.  Its $H^1$ vanishes on every field point set used below.

### 2.7 Dimensions, centers, kernels, and quotients

The complete algebraic ledger is:

| group or map | dimension | connected center | finite kernel or component group | algebraic quotient |
|---|---:|---|---|---|
| $G$ | $4d+1$ | $Z_G$, dimension $d+1$ | $G^{\rm der}\cap Z_G=\operatorname{Res}_{F/\mathbf Q}\mu_2$ | $T_G$, dimension $d+1$ |
| $G^{\rm der}$ | $3d$ | finite | center $\operatorname{Res}_{F/\mathbf Q}\mu_2$ | trivial |
| $H$ | $3d+1$ | diagonal $\mathbf G_m$ | $\pi_0(Z_H)=(\operatorname{Res}\mu_2)/\mu_2$ | $\mathbf G_m$ by Nrd |
| $J=\operatorname{Res}D^\times$ | $4d$ | $\operatorname{Res}_{F/\mathbf Q}\mathbf G_m$ | none | $S$ after imposing common norm |
| $G^{\rm der}\times Z_G\to G$ | equal dimensions | -- | $\operatorname{Res}_{F/\mathbf Q}\mu_2$, degree $2^d$ | fppf cokernel zero |
| $G^{\rm der}\times\mathbf G_m\to H$ | equal dimensions | -- | $\mu_2$, degree $2$ | fppf cokernel zero |
| $\widetilde G\to G$ | relative dimension $d$ | -- | connected kernel $R_F$ | fppf cokernel zero |
| $G\to U$ | relative dimension $3d+1$ | -- | kernel $H$ | split quotient $U$, dimension $d$ |
| $L\to S$ | relative dimension $5d+1$ | -- | kernel $\widetilde G$ | $S$, dimension $d-1$ |

The phrase “fppf cokernel zero” in the table is deliberately algebraic.  The pointwise
cokernels of the finite covers are the boundary images computed next.

## 3. Rational, local, and adelic images

### 3.1 The boundary class of the finite central cover

Let $g\in G(\mathbf Q)$, and write

$$
\delta=\det_Kg\in K^\times,
\qquad q=\nu(g)\in\mathbf Q^\times.                            \tag{3.1}
$$

Since $N_{K/F}(\delta/q)=1$, Hilbert 90 gives $x\in K^\times$ such that

$$
\frac{x}{c(x)}=\frac{\delta}{q}.                               \tag{3.2}
$$

Define

$$
\operatorname{ob}_G(g)
=\left[\frac{q}{N_{K/F}(x)}\right]
\in F^\times/F^{\times2}.                                     \tag{3.3}
$$

Changing $x$ to $xt$ with $t\in F^\times$ changes the displayed representative by $t^{-2}$,
so the class is well defined.

**Proposition 3.1.** The class (3.3) is the connecting class of $g$ for (2.9).  In particular,
$g$ lifts to $G^{\mathrm{der}}(\mathbf Q)\times Z_G(\mathbf Q)$ if and only if
$\operatorname{ob}_G(g)=1$.

**Proof.**  A lift $g=uz$ with $u\in G^{\mathrm{der}}(\mathbf Q)$ and
$z\in Z_G(\mathbf Q)$ must satisfy

$$
z^2=\delta,
\qquad N_{K/F}(z)=q.                                          \tag{3.4}
$$

The quotient of these equations is (3.2).  Every solution of (3.2) is $z=xr$ for
$r\in F^\times$.  It satisfies both equations in (3.4) precisely when

$$
r^2=\frac{q}{N_{K/F}(x)}.                                     \tag{3.5}
$$

Thus a lift exists exactly when (3.3) is trivial.  The same calculation on an fppf splitting
algebra identifies this obstruction with the torsor boundary in
$H^1(\mathbf Q,M)=F^\times/F^{\times2}$. $\square$

### 3.2 The exact rational image

The boundary does not range over every square class.  The two factors in the central cover
give

$$
H^1(\mathbf Q,G^{\mathrm{der}})
\simeq F^\times/\operatorname{Nrd}(D^\times),                 \tag{3.6}
$$

and

$$
H^1(\mathbf Q,Z_G)
\simeq
F^\times/\bigl(N_{K/F}(K^\times)\mathbf Q^\times\bigr).     \tag{3.7}
$$

For (3.6), use
$1\to D^1\to D^\times\xrightarrow{\rm Nrd}\mathbf G_m\to1$
and nonabelian Hilbert 90 for $D^\times$.  For (3.7), use

$$
1\longrightarrow Z_G
\longrightarrow
\operatorname{Res}_{K/\mathbf Q}\mathbf G_m\times\mathbf G_m
\xrightarrow{(z,q)\mapsto N(z)q^{-1}}
\operatorname{Res}_{F/\mathbf Q}\mathbf G_m
\longrightarrow1                                             \tag{3.8}
$$

and Hilbert 90 for both induced tori.

The long exact sequence of (2.9) now gives the exact pointwise image.

**Proposition 3.2.** The cokernel of

$$
(G^{\mathrm{der}}\times Z_G)(\mathbf Q)\longrightarrow G(\mathbf Q)
$$

is identified by (3.3) with

$$
\boxed{
\frac{
\operatorname{Nrd}(D^\times)
\cap\bigl(N_{K/F}(K^\times)\mathbf Q^\times\bigr)}
{F^{\times2}}.}                                               \tag{3.9}
$$

**Proof.**  The boundary image is the kernel of

$$
H^1(\mathbf Q,M)\longrightarrow
H^1(\mathbf Q,G^{\mathrm{der}})\times H^1(\mathbf Q,Z_G).
$$

Under (3.6)--(3.7), a square class maps to its classes modulo the two displayed norm
subgroups.  Its kernel is exactly (3.9). $\square$

No vanishing has been inserted.  At real places where $D$ is Hamiltonian, reduced norms are
positive.  Norms from the CM extension are positive at every real place, while multiplication
by a rational scalar changes all real signs together.  Formula (3.9), rather than an informal
sign slogan, also retains every finite norm condition.

### 3.3 Local and adelic obstruction tuples

Let $v$ be a place of $\mathbf Q$, and abbreviate

$$
F_v=F\otimes_{\mathbf Q}\mathbf Q_v,
\qquad K_v=K\otimes_{\mathbf Q}\mathbf Q_v,
\qquad D_v=D\otimes_{\mathbf Q}\mathbf Q_v.
$$

For $g_v\in G(\mathbf Q_v)$ choose $x_v\in K_v^\times$ with

$$
x_v/c(x_v)=\det_K(g_v)/\nu(g_v).
$$

Then

$$
\operatorname{ob}_{G,v}(g_v)
=\left[\frac{\nu(g_v)}{N_{K_v/F_v}(x_v)}\right]
\in F_v^\times/F_v^{\times2}.                                \tag{3.10}
$$

The possible local classes form

$$
\frac{
\operatorname{Nrd}(D_v^\times)
\cap\bigl(N_{K_v/F_v}(K_v^\times)\mathbf Q_v^\times\bigr)}
{F_v^{\times2}}.                                               \tag{3.11}
$$

At almost every finite $v$, fix the good integral model and let
$B_v^{\mathrm{int}}$ be the image under $\operatorname{ob}_{G,v}$ of its integral points.
This subgroup need not be trivial: already for the analogous cover
$\operatorname{SL}_2\times\mathbf G_m\to\operatorname{GL}_2$, a matrix with nonsquare unit
determinant has nontrivial integral boundary.  Therefore an adelic element has a restricted
tuple

$$
\operatorname{ob}_{G,\mathbf A}(g)
=\bigl(\operatorname{ob}_{G,v}(g_v)\bigr)_v                  \tag{3.12}
$$

in the restricted product of the groups (3.11) with respect to the subgroups
$B_v^{\mathrm{int}}$.  It lifts adelically through (2.9) exactly when every component is
trivial.  A rational obstruction maps diagonally into this restricted product, but an
arbitrary adelic tuple need not come from one global square class.

### 3.4 The common-norm square-class obstruction

For $h\in H(\mathbf Q)$ put $q=\operatorname{Nrd}(h)\in\mathbf Q^\times$.  A lift through
(2.18) requires a scalar $s\in\mathbf Q^\times$ with $s^2=q$.  Hence

$$
\operatorname{ob}_H(h)=[q]\in\mathbf Q^\times/\mathbf Q^{\times2}. \tag{3.13}
$$

Its possible values are

$$
\frac{\mathbf Q^\times\cap\operatorname{Nrd}(D^\times)}
{\mathbf Q^{\times2}},                                        \tag{3.14}
$$

where $\mathbf Q^\times$ is diagonally embedded in $F^\times$.  The local class is
$[q_v]\in\mathbf Q_v^\times/\mathbf Q_v^{\times2}$, again with the reduced-norm condition.
More precisely, for $h=(h_v)\in H(\mathbf A)$ and
$q=\operatorname{Nrd}(h)=(q_v)\in\mathbf A_{\mathbf Q}^\times$, the adelic boundary is

$$
\operatorname{ob}_{H,\mathbf A}(h)=([q_v])_v
\in\prod_v'\mathbf Q_v^\times/\mathbf Q_v^{\times2}.
$$

Its image is exactly the restricted product of

$$
\frac{\mathbf Q_v^\times\cap\operatorname{Nrd}(D_v^\times)}
{\mathbf Q_v^{\times2}},
$$

with $\mathbf Q_v^\times$ embedded diagonally in $F_v^\times$. Every such restricted tuple is
realized by local norm fibers and integral fibers almost everywhere. Hence the adelic point
cokernel of (2.18) is this restricted product, and an adelic point lifts if and only if every
entry is trivial. The rational group (3.14) maps diagonally into it. Thus equality of derived
groups does not make the common-norm group a pointwise product of its derived group and its
connected center.

### 3.5 Why the auxiliary cover is surjective on points

The kernel in (2.30) is induced, so

$$
H^1(\mathbf Q,R_F)=H^1(F,\mathbf G_m)=0                       \tag{3.15}
$$

and, for every place $v$,

$$
H^1(\mathbf Q_v,R_F)
=H^1(F\otimes_{\mathbf Q}\mathbf Q_v,\mathbf G_m)=0.          \tag{3.16}
$$

Consequently

$$
\widetilde G(\mathbf Q)\twoheadrightarrow G(\mathbf Q),
\qquad
\widetilde G(\mathbf Q_v)\twoheadrightarrow G(\mathbf Q_v).  \tag{3.17}
$$

Surjectivity on each completion is not by itself enough for restricted products.  Outside a
finite set choose smooth integral models for (2.30).  The lifting obstruction over the
semilocal ring $\mathcal O_F\otimes\mathbf Z_v$ lies in its Picard group, which is zero.
Thus an integral target point has an integral lift at almost every $v$.  The local lifts can
therefore be chosen as a restricted tuple, and

$$
\widetilde G(\mathbf A)\twoheadrightarrow G(\mathbf A),
\qquad
\widetilde G(\mathbf A_f)\twoheadrightarrow G(\mathbf A_f).   \tag{3.18}
$$

This is the precise reason the auxiliary cover reaches every adelic component.  It does not
erase the nonzero boundary (3.12) of the different, finite cover.

### 3.6 Actual torus images and compact class quotients

For (2.20), define

$$
S_D(\mathbf A)=\beta_D(J(\mathbf A)),
\qquad S_D(\mathbf Q)=\beta_D(J(\mathbf Q)).                   \tag{3.19}
$$

Since $S(\mathbf Q)=F^\times/\mathbf Q^\times$ and
$S(\mathbf A)=\mathbf A_F^\times/\mathbf A_\mathbf Q^\times$, these images are exactly

$$
\begin{aligned}
S_D(\mathbf Q)
&=\frac{\operatorname{Nrd}(D^\times)\mathbf Q^\times}
{\mathbf Q^\times},\\
S_D(\mathbf A)
&=\frac{\operatorname{Nrd}(D^\times(\mathbf A_F))
\mathbf A_\mathbf Q^\times}{\mathbf A_\mathbf Q^\times}.
\end{aligned}                                                  \tag{3.20}
$$

Thus the point cokernels of (2.20) are
$S(\mathbf Q)/S_D(\mathbf Q)$ and $S(\mathbf A)/S_D(\mathbf A)$; the long exact sequence
embeds them in $H^1(\mathbf Q,H)$ and the corresponding restricted local $H^1$ set. At a
Hamiltonian real place the norm is positive; at finite places it is surjective. Retaining
$S_D(\mathbf A)$ records those signs without pretending that every ambient torus point lifts.

For (2.27), similarly put

$$
S_L(\mathbf A)=\beta(L(\mathbf A)),
\qquad S_L(\mathbf Q)=\beta(L(\mathbf Q)).                    \tag{3.21}
$$

More explicitly,

$$
\begin{aligned}
S_L(\mathbf Q)
&=\frac{\operatorname{Nrd}(D^\times)N_{K/F}(K^\times)
\mathbf Q^\times}{\mathbf Q^\times},\\
S_L(\mathbf A)
&=\frac{\operatorname{Nrd}(D^\times(\mathbf A_F))
N_{K/F}(\mathbf A_K^\times)\mathbf A_\mathbf Q^\times}
{\mathbf A_\mathbf Q^\times}.
\end{aligned}                                                  \tag{3.22}
$$

Because $K\subset D$ and $\operatorname{Nrd}|_{K^\times}=N_{K/F}$, the two displayed actual
images satisfy

$$
S_L(\mathbf Q)=S_D(\mathbf Q),\qquad
S_L(\mathbf A)=S_D(\mathbf A).
$$

The separate notation records which normal pair is being used in an ascension argument, not a
difference between the underlying point-image groups.

The ambient point cokernels inject into the $H^1$ of $\widetilde G$. Its representatives are
products of a reduced norm and a $K/F$ norm. The class quotients used
in automorphic ascension are

$$
\mathcal C_D=S_D(\mathbf Q)\backslash S_D(\mathbf A),
\qquad
\mathcal C_L=S_L(\mathbf Q)\backslash S_L(\mathbf A).          \tag{3.23}
$$

They are compact.  Indeed, $S$ is $\mathbf Q$-anisotropic: a Galois-invariant character of
$\operatorname{Res}_{F/\mathbf Q}\mathbf G_m$ is a multiple of the sum of the embeddings,
and requiring it to vanish on the diagonal forces that multiple to be zero.  The adelic class
space $S(\mathbf Q)\backslash S(\mathbf A)$ is therefore compact, and (3.23) are closed
subquotients.  Fourier expansion below is performed on these actual compact quotients, never on
an unverified replacement by $S(\mathbf A)$.

### 3.7 The finite-level obstruction quotient

Let $C\subset G(\mathbf A_f)$ be compact open.  The subset of components reached by the finite
central cover is controlled by the image of

$$
(G^{\mathrm{der}}\times Z_G)(\mathbf A_f)\longrightarrow G(\mathbf A_f)/C.
$$

Its complement is measured by the finite image

$$
\mathfrak O_C=
\operatorname{im}\!\left(
G(\mathbf A_f)\xrightarrow{\operatorname{ob}_{G,\mathbf A_f}}
\prod_{v<\infty}'F_v^\times/F_v^{\times2}
\right)
\Big/\operatorname{ob}_{G,\mathbf A_f}(C).                    \tag{3.24}
$$

The quotient is finite because $C$ is open and the boundary is locally constant.  It records
missing image components, not extra fibers over a point that already lifts.  In contrast,
(3.18) shows that $\widetilde G$ has no missing target component.  This distinction is the
reason the finite central cover is used for obstruction bookkeeping while the auxiliary cover
is used for automorphic descent.

## 4. Measures, centers, and levels

### 4.1 Coherent Haar measures

Every restriction, induction, and Hecke formula below uses one coherent system of measures.
At almost every finite place choose the smooth integral models of Chapter 3 and give their
hyperspecial subgroups volume one. At the remaining finite places choose Haar measures once
and retain them. On a compact open $C$ with arbitrary ambient normalization, the averaging
idempotent is

$$
e_C=\operatorname{vol}(C)^{-1}\mathbf 1_C.                    \tag{4.1}
$$

Thus convolution by $e_C$ is projection onto $C$-invariants. A bare characteristic function
is an idempotent only when $\operatorname{vol}(C)=1$.

For an exact sequence whose point image has already been specified, quotient measures are
defined by Weil's formula. For example, on $\widetilde G(\mathbf Q_v)\to G(\mathbf Q_v)$,

$$
\int_{\widetilde G(\mathbf Q_v)}f(\tilde g)\,d\tilde g
=\int_{G(\mathbf Q_v)}
 \int_{R_F(\mathbf Q_v)}f(r\tilde g)\,dr\,dg.                 \tag{4.2}
$$

Product measures use (4.2) at every place. On each compact class quotient
$\mathcal C_D$, $\mathcal C_L$, and $U(\mathbf Q)\backslash U(\mathbf A)$, use probability
measure. At an active real adjoint factor the rotation group has volume one, at a definite
adjoint factor the compact group has probability measure, and the central measures are those
appearing in (4.2). Rescaling a coherent system changes inner products and formal degrees, but
not an automorphic occurrence multiplicity.

### 4.2 Fixed central-character automorphic spaces

Let

$$
\Omega:Z_G(\mathbf Q)\backslash Z_G(\mathbf A)\longrightarrow S^1             \tag{4.3}
$$

be a fixed unitary character. Define $L^2(G,\Omega)$ to be the Hilbert space of measurable
functions $f$ on $G(\mathbf Q)\backslash G(\mathbf A)$ such that

$$
f(zg)=\Omega(z)f(g)                                            \tag{4.4}
$$

and

$$
\int_{Z_G(\mathbf A)G(\mathbf Q)\backslash G(\mathbf A)}
|f(g)|^2\,dg<\infty.                                           \tag{4.5}
$$

The center is in the denominator only for the norm; the functions are not functions on the
projective quotient when $\Omega$ is nontrivial. Since the adjoint quotient is anisotropic,
(4.5) is over a compact space. Hence

$$
L^2(G,\Omega)
=\widehat\bigoplus_{\rho}
\mathcal M_G(\rho)\widehat\otimes\rho,
\qquad
m_G(\rho)=\dim\mathcal M_G(\rho)<\infty.                       \tag{4.6}
$$

The smooth vectors are denoted $\mathcal A(G,\Omega)$. For a fixed finite level, only
characters with

$$
\Omega_f|_{C\cap Z_G(\mathbf A_f)}=1                          \tag{4.7}
$$

can occur. If a finite central-routing orbit of components is used, its finite character
idempotent defines the corresponding $\Omega_f$-sector. One must not write an isotypic sector
of a single component unless the central translations in question preserve that component.

### 4.3 The positive split center and the real stabilizer

Fix $h\in X^+$, with the chosen orientations at the two active places. Let
$K_{h,c}^0$ be the connected compact stabilizer of $h$ after quotienting by
$A_G(\mathbf R)^0$. Define

$$
\boxed{
K_\infty^\dagger=A_G(\mathbf R)^0K_{h,c}^0.}                  \tag{4.8}
$$

Up to finite central overlaps, its factors are:

- $\mathbf R_{>0}=A_G(\mathbf R)^0$;
- the compact central torus $(S^1)^d$;
- $\operatorname{SO}(2)$ at each of $v_1,v_2$;
- the full connected compact derived factor $\operatorname{SU}(2)$ at every definite real
  place.

The rotation groups are connected. Replacing them by the full disconnected orthogonal
normalizers would identify orientation lines and compute a different quotient. Replacing
$K_\infty^\dagger$ by a maximal compact subgroup would leave the positive scalar direction in
the relative tangent complex and create a spurious adjacent degree.

Let $\xi$ be an algebraic coefficient representation and let $V_\xi$ be its complex fiber.
The relative cohomology

$$
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty\otimes V_\xi)    \tag{4.9}
$$

is well typed only when the action of $A_G(\mathbf R)^0$ on the tensor product is trivial.
For $\rho$ with central character $\Omega$, this is the equation

$$
\Omega_\infty(a)\,\xi(a)=1
\qquad(a\in A_G(\mathbf R)^0).                                \tag{4.10}
$$

If (4.10) fails, the one-dimensional central relative complex is contractible and (4.9)
vanishes in every degree. For constant coefficients, (4.10) says exactly that $\Omega$ is
trivial on the positive real scalar torus. There is a separate compact-center condition:
because $Z_G(\mathbf R)\cap K_\infty^\dagger$ also contains the compact CM torus, nonzero
relative cochains require $\Omega_\infty(z)\xi(z)=1$ on that intersection. Failure there makes
the $K_\infty^\dagger$-equivariant cochain space zero rather than producing a central tangent
complex.

### 4.4 Compatible quaternionic-character pairs

Let $\Pi$ be a noncharacter automorphic representation of
$D^\times(\mathbf A_F)$ with central character $\omega_\Pi$, and let

$$
\chi:K^\times\backslash\mathbf A_K^\times\longrightarrow\mathbf C^\times
                                                                    \tag{4.11}
$$

be a Hecke character. The product representation

$$
\tau=\Pi\boxtimes\chi                                          \tag{4.12}
$$

of $L(\mathbf A)$ is considered in the unitary normalization used by the fixed-central $L^2$
spaces. For an
algebraic quasicharacter, remove its common real modulus power first and put the inverse power
in the coefficient normalization. In the constant-coefficient situation, (4.14) and (4.10)
force that modulus power to be zero.

It acts on the kernel (2.29) by

$$
r\longmapsto\omega_\Pi(r)\chi(r)^{-1}.                        \tag{4.13}
$$

It is therefore trivial on $R_F(\mathbf A)$ precisely when

$$
\boxed{\chi|_{C_F}=\omega_\Pi,}
\qquad C_F=F^\times\backslash\mathbf A_F^\times.              \tag{4.14}
$$

The scalar $z\in Z_G(\mathbf A)$ lifts as $(1,z)\in\widetilde G(\mathbf A)$.
Consequently the descended central character is

$$
\Omega_{\Pi,\chi}(z)=\chi(z),                                 \tag{4.15}
$$

and a pair is compatible with the fixed sector (4.3) exactly when

$$
\chi|_{Z_G(\mathbf A)}=\Omega.                                \tag{4.16}
$$

Equations (4.14) and (4.16) must agree on the intersection of their source subgroups. For
unitary characters, a compatible prescription on the closed subgroup they generate extends to
$C_K$ by Pontryagin duality. In the algebraic category there is an additional ray-unit
condition on the desired infinity type. Thus existence of $\chi$ is a genuine compatibility
condition, not an automatic decoration of $\Pi$.

For constant surface coefficients, a **cohomological compatible pair** means, in addition,
that $\Pi_\infty$ has the exact type

$$
\Pi_{v_1}=\Pi_{v_2}=D_2,
\qquad
\Pi_v=\mathbf1_{\mathbf H^\times}\quad(v\mid\infty,\ v\ne v_1,v_2),       \tag{4.17}
$$

after the common unitary central normalization, and that $\chi_\infty$ gives trivial action on
$Z_G(\mathbf R)\cap K_\infty^\dagger$ (in particular, it makes (4.10) hold on the positive
split center).

### 4.5 Pair equivalence through the actual quotient

Let

$$
\mathcal X_L=\operatorname{Hom}_{\mathrm{cont}}(\mathcal C_L,S^1).       \tag{4.18}
$$

Inflating a character $\zeta\in\mathcal X_L$ through $\beta$ gives an automorphic character
of $L(\mathbf A)$ which is trivial on $\widetilde G(\mathbf A)$. Hence

$$
(\Pi,\chi)\sim(\Pi,\chi)\otimes\zeta                         \tag{4.19}
$$

defines the exact equivalence relation on ascensions of one $\widetilde G$ representation.

When $\zeta$ is extended to a character $\eta$ of $\mathbf A_F^\times$, trivial on the
diagonal $\mathbf A_\mathbf Q^\times$ and on the relevant rational norm image, (4.19) becomes

$$
(\Pi,\chi)\longmapsto
\left(
\Pi\otimes(\eta\circ\operatorname{Nrd}),
\chi\,(\eta\circ N_{K/F})
\right).                                                       \tag{4.20}
$$

The intrinsic definition (4.18) is primary. Different extensions $\eta$ which agree on the
actual image (3.22) induce the same twist, and a character of the ambient $S(\mathbf A)$ which
does not descend through $S_L(\mathbf Q)$ is not an automorphic pair equivalence.

### 4.6 The compact quotient level

Let $C\subset G(\mathbf A_f)$ be compact open. Its inverse image

$$
\theta^{-1}(C)\subset\widetilde G(\mathbf A_f)                 \tag{4.21}
$$

is **not compact**: it contains the whole kernel
$R_F(\mathbf A_f)=\mathbf A_{F,f}^\times$. Thus
$\mathbf 1_{\theta^{-1}(C)}$ is not a compactly supported Hecke function and cannot be used as
a level idempotent.

The correct level is the compact quotient

$$
\overline C_{\widetilde G}
=\theta^{-1}(C)/R_F(\mathbf A_f)
\xrightarrow{\sim}C.                                         \tag{4.22}
$$

If (4.14) holds, $R_F(\mathbf A_f)$ acts trivially on
$\tau|_{\widetilde G(\mathbf A_f)}$, and averaging over (4.22) is well defined:

$$
e_{\overline C}v
=\int_{\overline C_{\widetilde G}}\tau(\tilde c)v\,d\bar c,
\qquad \operatorname{vol}(\overline C_{\widetilde G})=1.      \tag{4.23}
$$

Changing a lift $\tilde c$ by $r\in R_F(\mathbf A_f)$ does not change the integrand. Formula
(4.23), not integration over (4.21), is the finite-level projector used throughout.

## 5. Clifford theory with rational packet selection

### 5.1 The finite factor-set calculation

We first isolate the algebra which remains valid at every finite adelic type. Let
$N\triangleleft J_0$ be a normal subgroup with finite abelian quotient $A$, and let $\tau$ be
an irreducible complex representation of $J_0$. Define

$$
X(\tau)=\{\eta\in\widehat A:\tau\otimes\eta\simeq\tau\}.       \tag{5.1}
$$

Choose intertwiners

$$
I_\eta:\tau\longrightarrow\tau\otimes\eta,
\qquad I_1=1.                                                  \tag{5.2}
$$

Schur's lemma gives a normalized factor set

$$
I_\eta I_\xi=c(\eta,\xi)I_{\eta\xi}.                         \tag{5.3}
$$

Associativity says that $c$ is a $2$-cocycle; rescaling the intertwiners changes it by a
coboundary. Fourier decomposition under conjugation by $A$ proves

$$
\boxed{
\operatorname{End}_N(\tau)\simeq\mathbf C^c[X(\tau)].}        \tag{5.4}
$$

Indeed, the $\eta$-Fourier summand of $\operatorname{End}_N(\tau)$ is
$\operatorname{Hom}_{J_0}(\tau,\tau\otimes\eta)$, which is zero or one-dimensional.
Composition is exactly (5.3).

### 5.2 Restriction multiplicity and the radical

Because $X(\tau)$ is abelian, the commutator

$$
b_c(\eta,\xi)=\frac{c(\eta,\xi)}{c(\xi,\eta)}                 \tag{5.5}
$$

is an alternating bicharacter. Let

$$
R_c=\{\eta:b_c(\eta,\xi)=1\text{ for every }\xi\}.            \tag{5.6}
$$

The twisted algebra has $|R_c|$ simple blocks, each a matrix algebra of size

$$
e_c=\sqrt{\frac{|X(\tau)|}{|R_c|}}.                            \tag{5.7}
$$

To see this directly, linearize the symmetric restriction of $c$ to $R_c$ by rescaling cyclic
generators. The quotient $X/R_c$ carries a nondegenerate alternating pairing. Conjugating a
linear combination of the twisted basis elements by all basis elements kills every noncentral
coefficient, so a simple block has dimension $|X/R_c|=e_c^2$.

If

$$
\tau|_N\simeq e\bigoplus_{i=1}^{r}\sigma_i                    \tag{5.8}
$$

with distinct irreducible constituents, comparison of (5.4) with
$\prod_iM_e(\mathbf C)$ gives

$$
\boxed{r=|R_c|,\qquad e=e_c,\qquad |X(\tau)|=re^2.}            \tag{5.9}
$$

Thus an abelian quotient does not by itself imply multiplicity-free restriction. It does so
when the commutator pairing is trivial. In particular every cyclic self-twist group has
trivial commutator: rescale an intertwiner for a generator so that its defining power is one.

### 5.3 Abstract and automorphic self-twists

For adelic restriction there are two character groups.

- An **abstract self-twist** is a continuous character of the actual adelic quotient
  $J_0(\mathbf A)/N(\mathbf A)$ for which the restricted tensor product representation is
  isomorphic to its twist. It need not be trivial on $J_0(k)$.
- An **automorphic self-twist** is additionally trivial on the image of $J_0(k)$. It is a
  character of the compact automorphic class quotient.

The distinction is essential. At finitely many places one can choose local self-twists which
do not satisfy the product formula. They belong to the abstract packet but multiplication by
their character does not preserve left rational invariance.

For an automorphic self-twist $\eta$, multiplication

$$
(M_\eta f)(g)=\eta(g)f(g)                                     \tag{5.10}
$$

is defined on automorphic functions. If $\tau$ occurs with multiplicity one, then on its
automorphic realization

$$
M_\eta=\varepsilon_\tau(\eta)I_\eta                           \tag{5.11}
$$

for a scalar $\varepsilon_\tau(\eta)$. Since the multiplication operators compose honestly,

$$
c(\eta,\xi)
=\frac{\varepsilon_\tau(\eta)\varepsilon_\tau(\xi)}
{\varepsilon_\tau(\eta\xi)}                                  \tag{5.12}
$$

on the automorphic self-twist subgroup. Thus global multiplicity one trivializes the
restriction of the factor set there. It does not erase a nontrivial local cocycle on a larger
abstract self-twist group.

### 5.4 The automorphic period module

Let $\mathcal T$ be a fixed finite level and archimedean type. It cuts the relevant quotient
action to a finite group and all spaces below are finite dimensional. Put

$$
A_\tau=\operatorname{End}_{N(\mathbf A)}(\tau)\simeq
\mathbf C^c[X_{\mathcal T}(\tau)].                             \tag{5.13}
$$

For representatives $a$ in the actual compact torus quotient, restriction on the $a$-coset is

$$
R_af(n)=f(na).                                                 \tag{5.14}
$$

Let $P_\tau$ be the right $A_\tau$-module in
$\operatorname{Hom}_{N(\mathbf A)}(\tau,\mathcal A(N))$
generated by these rationally invariant restriction maps, with the prescribed type and central
character. For a constituent $\sigma$ of $\tau|_N$, let

$$
V_\sigma=\operatorname{Hom}_{N(\mathbf A)}(\sigma,\tau),       \tag{5.15}
$$

a simple left $A_\tau$-module. Morita evaluation gives the exact automorphic multiplicity
contributed by the twist orbit of $\tau$:

$$
\boxed{
m_N(\sigma;[\tau])
=\dim_{\mathbf C}\bigl(P_\tau\otimes_{A_\tau}V_\sigma\bigr).} \tag{5.16}
$$

This is not a definition in disguise. Decompose
$\tau|_N=\bigoplus_\sigma\sigma\otimes V_\sigma$. Then
$A_\tau=\prod_\sigma\operatorname{End}(V_\sigma)$, while
$P_\tau$ decomposes as
$\bigoplus_\sigma\operatorname{Hom}(V_\sigma,\mathcal M_N(\sigma))$.
Tensoring with $V_\sigma$ returns exactly the occurrence space
$\mathcal M_N(\sigma)$.

If projective characters are chosen, (5.16) becomes

$$
m_N(\sigma;[\tau])
=\frac1{|X_{\mathcal T}|}
\sum_{x\in X_{\mathcal T}}
\operatorname{tr}_{P_\tau}(e_x^{\mathrm{op}})
\operatorname{tr}_{V_\sigma}(e_x^{-1}).                       \tag{5.17}
$$

The inverse is the inverse in the twisted algebra, including its cocycle scalar. Omitting that
scalar is exactly the error of treating a projective packet as an ordinary character table.

### 5.5 The global sign formula

Suppose now that the typewise cocycle has been linearized and the restriction is
multiplicity free. Every packet constituent $\sigma$ then has a character

$$
\langle\,\cdot\,,\sigma\rangle:X_{\mathcal T}(\tau)\longrightarrow S^1,
\qquad
I_x|_\sigma=\langle x,\sigma\rangle.                           \tag{5.18}
$$

Let $X_{\mathrm{aut}}(\tau)$ be the automorphic self-twist subgroup. Normalize the $I_x$
to form an honest representation of the typewise self-twist group. Equation (5.11) then makes
$\varepsilon_\tau$ a character of $X_{\mathrm{aut}}(\tau)$.

Fourier projection of (5.14) gives

$$
\boxed{
m_N(\sigma;[\tau])
=\frac1{|X_{\mathrm{aut}}(\tau)|}
\sum_{\eta\in X_{\mathrm{aut}}(\tau)}
\varepsilon_\tau(\eta)
\overline{\langle\eta,\sigma\rangle}.}                         \tag{5.19}
$$

The right side is one when the packet character restricts to the automorphic character
$\varepsilon_\tau$, and zero otherwise. Formula (5.19) is the global product condition.
It says neither that every formal tensor product of local constituents is automorphic nor that
a packet with several members has automorphic multiplicity greater than one.

### 5.6 Typewise passage to adelic representations

An adelic restriction packet can branch at infinitely many unramified places, although a fixed
compact level retains the distinguished spherical branch at almost all of them. Accordingly,
we do not claim that one global restriction is a finite direct sum without specifying a type.

Choose a compact open at the finite places, finitely many real compact types, and a fixed
central character. Admissibility makes the type space finite dimensional. The finite
calculation (5.1)--(5.19) applies. Enlarging the type retains every previously visible
intertwiner and packet label; any individual smooth vector is detected at one stage. Therefore
the formulas stabilize for each irreducible restricted tensor product constituent. This
typewise limit is the meaning of every adelic Clifford formula below.

## 6. Restriction to the common-norm group

### 6.1 The exact norm quotient

The normal pair is

$$
H(\mathbf A)\triangleleft J(\mathbf A)=D^\times(\mathbf A_F),
$$

and the automorphic quotient is the actual compact group

$$
\mathcal C_D=\beta_D(J(\mathbf Q))\backslash\beta_D(J(\mathbf A)).       \tag{6.1}
$$

A character of the ambient torus $S(\mathbf A)$ which is nontrivial on
$\beta_D(J(\mathbf Q))$ cannot be used to multiply automorphic forms. Conversely, every
character of (6.1) inflates to a legitimate automorphic quotient character of $J(\mathbf A)$.

For a noncharacter automorphic $\Pi$ of $J(\mathbf A)$, a representative character $\eta$ on
$\mathbf A_F^\times$ acts by

$$
\Pi\longmapsto\Pi\otimes(\eta\circ\operatorname{Nrd}).        \tag{6.2}
$$

Comparing central characters in a self-isomorphism gives $\eta^2=1$ on the relevant norm
image. At one local factor the self-twist group can nevertheless be noncyclic, and its
intertwiners can have a nontrivial commutator pairing.

### 6.2 Restriction packets and possible cocycles

Fix a finite type $\mathcal T$. Let $X_H(\Pi,\mathcal T)$ be the finite abstract self-twist
group detected on that type and let $c_\Pi$ be the factor set of chosen intertwiners. Put

$$
R_\Pi=\operatorname{Rad}(b_{c_\Pi}),
\qquad
e_\Pi=\sqrt{\frac{|X_H(\Pi,\mathcal T)|}{|R_\Pi|}}.            \tag{6.3}
$$

Then the abstract typewise restriction has $|R_\Pi|$ distinct constituents, each repeated
$e_\Pi$ times. Both numbers can be nontrivial. In particular, quaternionic multiplicity one
for $\Pi$ does not, by itself, prove multiplicity one after restriction to $H$.

Local packet constituents are labeled by simple modules for
$\mathbf C^{c_\Pi}[X_H(\Pi,\mathcal T)]$, not by ordinary characters unless the factor set
linearizes. A global restricted tensor product must also satisfy the rational packet condition
of (5.17). These two stages are kept separate.

### 6.3 Automorphic ascension and exhaustion

Let $\sigma$ occur automorphically on $H$ with a fixed central character and finite type.
Consider induction through

$$
J(\mathbf Q)H(\mathbf A)\backslash J(\mathbf A)
\simeq\mathcal C_D.                                            \tag{6.4}
$$

This is the actual compact quotient (6.1). Inducing an automorphic function and Fourier
expanding along (6.4) produces a discrete Hilbert sum. Its fixed-type part is finite
dimensional. An irreducible summand is an automorphic representation $\Pi$ of $J(\mathbf A)$:
left rational invariance holds because every Fourier character is trivial on the rational image
in (6.4). No value on a missing point of $S(\mathbf A)$ is used.

Here is the rational step explicitly. For an automorphic vector $\varphi$ on $H$, define on
$J(\mathbf Q)H(\mathbf A)$

$$
F_\varphi(qh)=\varphi(h).                                     \tag{6.5}
$$

If $qh=q'h'$, then $q'^{-1}q=h'h^{-1}$ lies in
$J(\mathbf Q)\cap H(\mathbf A)=H(\mathbf Q)$, so (6.5) is well defined. Hilbert induction of
this vector-valued function across the compact quotient (6.4) gives scalar functions on
$J(\mathbf Q)\backslash J(\mathbf A)$ with the induced fixed central equivariance, after
pairing with vectors in the induced fiber. The norm is taken modulo that center.
Compactness preserves square-integrability and moderate growth. On a fixed type, the stabilizer
of the $J(\mathbf A)$-orbit of $\sigma$ is finite modulo $H(\mathbf A)$; its conjugation
intertwiners give the cocycle $c_\Pi$. Tensoring the projective extension of $\sigma$ with an
inverse-cocycle simple module makes an honest stabilizer representation, and compact induction
then gives the irreducible summands $\Pi$. This is the global Clifford extension construction,
not an assumption that $\sigma$ extends linearly.

Conversely, restriction of an automorphic $\Pi$ to each norm coset gives automorphic functions
on $H$. The Clifford extension theorem says that two ascensions of the same irreducible
$H$-constituent differ by a character of (6.4). Hence one quotient-character orbit of
quaternionic representations accounts for all ascensions and no second unrelated orbit can add
multiplicity.

This proves:

**Theorem 6.1 (common-norm ascension).** Every noncharacter automorphic representation of $H$
ascends to a noncharacter automorphic representation of $D^\times(\mathbf A_F)$. Every member
of the typewise restriction packet satisfying the rational period condition occurs
automorphically. Ascensions are unique up to the characters of $\mathcal C_D$.

### 6.4 The exact multiplicity module

The quaternionic representation $\Pi$ has automorphic multiplicity one, but the common-norm
multiplicity is the Morita number

$$
\boxed{
m_H(\sigma;[\Pi])
=\dim\bigl(P_\Pi\otimes_{
\mathbf C^{c_\Pi}[X_H(\Pi,\mathcal T)]}V_\sigma\bigr),}        \tag{6.6}
$$

where $P_\Pi$ is generated by the rational norm-coset restrictions and
$V_\sigma=\operatorname{Hom}_H(\sigma,\Pi)$. Equivalently it is the projective character
inner product (5.17). Formula (6.6) is valid whether the local commutator is trivial or not.

If the detected self-twist group is cyclic and the rational period module selects one packet
character, (6.6) is zero or one. If a noncyclic local self-twist group has a nondegenerate
factor set, the simple projective module can have dimension greater than one and that dimension
must remain in (6.6). The full PEL group will remove this particular ambiguity by imposing the
CM norm-kernel condition; it is not removed here by assertion.

### 6.5 The Jacquet--Langlands interface

The arbitrary-signature quaternionic theorem applies to the actual algebra $D=Q_a$. It gives
a bijection

$$
\Pi\longleftrightarrow\pi=\operatorname{JL}_D(\Pi)            \tag{6.7}
$$

between noncharacter automorphic representations of $D^\times(\mathbf A_F)$ and cuspidal
$\operatorname{GL}_2(\mathbf A_F)$ representations which are essentially square-integrable at
every place where $D$ is division. It matches every component under local
Jacquet--Langlands and preserves central characters, twists, conductor, independently defined
local factors, automorphic multiplicity, the good raw polynomial, and the parallel-weight-two
Hecke field.

The passage from (6.7) to $H$ is precisely Theorem 6.1 and formula (6.6). Thus a phrase such as
“Jacquet--Langlands on $H$” means the following exact composite:

$$
\pi\longleftrightarrow\Pi
\quad\rightsquigarrow\quad
\{\text{rationally selected constituents of }\Pi|_H\},        \tag{6.8}
$$

with multiplicities given by (6.6). No direct transfer theorem for the full group, and no
surface cohomology statement, is imported with (6.7).

## 7. Descent to the full PEL group

### 7.1 Pullback across the auxiliary cover

Because both maps in (3.17)--(3.18) are surjective, pullback gives an equivalence between:

- automorphic representations of $G(\mathbf A)$ with fixed central character; and
- automorphic representations of $\widetilde G(\mathbf A)$ on which
  $R_F(\mathbf A)$ acts trivially, with the pulled-back central character.

For functions the equivalence is explicit. If $f$ is automorphic on $G$, then
$f\circ\theta$ is left $\widetilde G(\mathbf Q)$-invariant and kernel-trivial. Conversely,
given such a function $\tilde f$, define $f(g)=\tilde f(\tilde g)$ for any adelic lift.
Kernel-triviality makes this independent of the lift. If $g_0\in G(\mathbf Q)$, choose
$\tilde g_0\in\widetilde G(\mathbf Q)$ using (3.17); then left invariance of $f$ follows.
The quotient measures of (4.2) make this an isometry up to the one fixed harmless normalization.

### 7.2 Ascending to a product representation

Let $\rho$ be a noncharacter automorphic representation of $G$, and pull it to
$\widetilde\rho$ on $\widetilde G$. Induce through

$$
L(\mathbf Q)\widetilde G(\mathbf A)\backslash L(\mathbf A)
\simeq\mathcal C_L.                                            \tag{7.1}
$$

The quotient is the actual compact group of (3.23). Fourier expansion of the fixed-type
induced space supplies an automorphic irreducible ascension $\tau$ of $L(\mathbf A)$. Since
$L$ is a direct product, it factors uniquely as

$$
\tau=\Pi\boxtimes\chi,                                        \tag{7.2}
$$

where $\Pi$ is automorphic on $D^\times(\mathbf A_F)$ and $\chi$ is a Hecke character of
$K$. Triviality on $R_F(\mathbf A)$ gives (4.14), and the central action gives (4.16).

The global construction is the same rational induction as in (6.5). For an automorphic vector
$\tilde f$ on $\widetilde G$, first set

$$
F_{\tilde f}(q\tilde g)=\tilde f(\tilde g)
\qquad(q\in L(\mathbf Q),\ \tilde g\in\widetilde G(\mathbf A)).
$$

It is well defined because
$L(\mathbf Q)\cap\widetilde G(\mathbf A)=\widetilde G(\mathbf Q)$. Induce this
vector-valued function across $\mathcal C_L$. On a fixed type, take the inertia subgroup of
the $\widetilde\rho$-orbit, form its projective conjugation extension, and tensor with a simple
module for the inverse factor set. The result is an honest irreducible $L(\mathbf A)$-summand
inside the fixed-compatible-central-character $L^2$ space, whose norm is taken after quotienting
its split center. Compactness of $\mathcal C_L$ gives a
discrete Fourier decomposition and preserves moderate growth. This proves automorphy of the
ascension before the product factorization (7.2) is used.

Conversely, any compatible pair restricts to $\widetilde G$ with trivial kernel and hence
descends to $G$. Clifford decomposition may produce several local packet candidates; the next
three sections determine exactly which are automorphic and with what multiplicity. Two product
ascensions of the same $G$-constituent differ by a character of $\mathcal C_L$, giving exactly
the pair equivalence (4.19).

### 7.3 The local norm-kernel self-twists

Fix a place $p$ of $\mathbf Q$. A character of the local quotient $S_L(\mathbf Q_p)$ can be
represented by characters $\eta_v$ of $F_v^\times$ for $v\mid p$, whose product is trivial on
the diagonal $\mathbf Q_p^\times$. A self-twist of the pair (7.2) must satisfy

$$
\Pi_v\otimes(\eta_v\circ\operatorname{Nrd})\simeq\Pi_v,
\qquad
\eta_v\circ N_{K_w/F_v}=1\quad(w\mid v).                      \tag{7.3}
$$

Local class field theory gives

$$
\{\eta_v:\eta_v\circ N_{K_v/F_v}=1\}
=
\begin{cases}
\{1\},&K_v\simeq F_v\times F_v,\\
\{1,\eta_{K_v/F_v}\},&K_v/F_v\text{ is a field}.
\end{cases}                                                    \tag{7.4}
$$

Thus the local invisible self-twist group is a subgroup of a product of cyclic groups of order
two, one for each $v\mid p$. It may have several generators because several $F$-places lie
above $p$, but each generator acts in one tensor factor.

At a fixed global type $\mathcal T$, only finitely many nonspherical choices are visible. Let

$$
Y_{\mathcal T}(\Pi,\chi)                                      \tag{7.5}
$$

denote the resulting finite elementary $2$-group of abstract pair self-twists. Its automorphic
subgroup consists of those tuples satisfying the rational product formula. If represented by
a Hecke character $\eta$ of $C_F$, it obeys

$$
\eta\circ N_{K/F}=1.                                          \tag{7.6}
$$

Such a representative can always be chosen to be a Hecke character, rather than merely a
character of $\mathbf A_F^\times$. At every finite place the reduced norm of $D_v^\times$ is
surjective, and at each active real place it is all of $\mathbf R^\times$. At a definite real
place the actual norm image is $\mathbf R_{>0}$, so a sign character there is invisible on
$S_L(\mathbf A)$ and may be removed from the representative. Automorphic triviality on
$\operatorname{Nrd}(D^\times)$ then gives triviality on every $x\in F^\times$ which is positive
at the definite places. For arbitrary $x$, weak approximation supplies a sign-correcting
$u\in F^\times$, equal to $1$ in the finite open kernel of the character and positive at the
active places, such that $xu$ is positive at every definite place. The normalized
representative has $\eta(u)=1$, so $\eta(x)=\eta(xu)=1$. It therefore descends to $C_F$.

Global class field theory now gives

$$
Y_{\mathrm{aut}}(\Pi,\chi)
\subseteq\{1,\eta_{K/F}\},                                   \tag{7.7}
$$

and the nontrivial element is present only if it also defines a character of the actual
quotient $\mathcal C_L$ and stabilizes $\Pi$. In particular, its restriction to the diagonal
$\mathbf A_\mathbf Q^\times$ must be trivial. The right side of (7.7) is an upper bound, not
an assertion that the quadratic character always survives the common-multiplier condition.

### 7.4 Cancellation of the Clifford cocycle

For each field place in (7.4), choose the nontrivial intertwiner, when it exists, and rescale it
so that its square is one. At split places there is no choice. Tensor intertwiners supported
at different $F$-places commute. Therefore, for every finite type,

$$
I_yI_{y'}=I_{yy'}
\qquad(y,y'\in Y_{\mathcal T}(\Pi,\chi)).                      \tag{7.8}
$$

This proves more than cyclicity of the global subgroup: the entire typewise abstract factor
set relevant to $L/\widetilde G$ is a coboundary, even when several independent local packet
choices are visible. Consequently

$$
(\Pi\boxtimes\chi)|_{\widetilde G}
$$

is multiplicity free at every type. Local exceptional factor sets that can occur for
$D^\times/H$ do not survive the additional equation
$\eta_v\circ N_{K_v/F_v}=1$: at one $F_v$ it leaves at most the cyclic group in (7.4).

For $\eta\in Y_{\mathrm{aut}}$, multiplication on the multiplicity-one automorphic realization
of $\Pi\boxtimes\chi$ is

$$
M_\eta=\varepsilon_{\Pi,\chi}(\eta)I_\eta.                   \tag{7.9}
$$

Both sides of (7.8) compose honestly, so $\varepsilon_{\Pi,\chi}$ is an ordinary character of
$Y_{\mathrm{aut}}$.

### 7.5 Global packet selection and multiplicity

Let $\rho$ be a typewise constituent of the restriction of $\Pi\boxtimes\chi$, descended to
$G$ through (2.30). The commuting intertwiners give its packet character

$$
\langle\,\cdot\,,\rho\rangle:
Y_{\mathcal T}(\Pi,\chi)\longrightarrow\{\pm1\}.              \tag{7.10}
$$

The automorphic multiplicity contributed by the pair orbit is

$$
\boxed{
m_G(\rho;[\Pi,\chi])
=\frac1{|Y_{\mathrm{aut}}(\Pi,\chi)|}
\sum_{\eta\in Y_{\mathrm{aut}}(\Pi,\chi)}
\varepsilon_{\Pi,\chi}(\eta)
\overline{\langle\eta,\rho\rangle}.}                         \tag{7.11}
$$

Hence

$$
m_G(\rho;[\Pi,\chi])=
\begin{cases}
1,&\langle\,\cdot\,,\rho\rangle|_{Y_{\rm aut}}
=\varepsilon_{\Pi,\chi},\\
0,&\text{otherwise}.
\end{cases}                                                    \tag{7.12}
$$

**Proof.** At the fixed type, (7.8) makes the endomorphism algebra the ordinary group algebra
$\mathbf C[Y_{\mathcal T}]$. Restriction to norm cosets gives its character eigenspaces.
For a rational quotient character, multiplication is related to the normalized tensor
intertwiner by (7.9). Fourier orthogonality on the probability quotient $\mathcal C_L$ projects
onto equality of the two characters and gives (7.11). Quaternionic multiplicity one and the
one-dimensional automorphic space of $\chi$ give multiplicity one for $\Pi\boxtimes\chi$ on
$L$. Conversely, any extra occurrence of $\rho$ ascends across (7.1); Clifford extension
classification puts the ascension in the same quotient-character orbit. It would therefore
give an extra occurrence of one of the multiplicity-one product representations, which is
impossible. $\square$

The zero in (7.12) is as important as the one. A formal product of local packet labels can
fail the single global quadratic parity equation. When $Y_{\rm aut}$ is trivial, all
fixed-type candidates allowed by the actual adelic quotient occur once. When it has order two,
exactly the candidates with the prescribed product sign occur, again once.

The packet character in (7.10)--(7.12) is the **complete** local character.  Its finite part
is imposed by $e_{\lambda,f}$ in (8.1), while its real part is imposed by
$e_{\lambda,\infty}$ in (9.8).  These local projectors commute on the product ascension, but
their labels are not independently automorphic: the single global equation (7.12) is imposed
on the combined label.

### 7.6 Classification and uniqueness

We can now state the classification without suppressing local labels.

**Theorem 7.1 (compatible-pair classification).** Fix $\Omega$, a finite level and real type.
Every noncharacter automorphic representation $\rho$ of $G(\mathbf A)$ in that sector is
obtained from:

1. a noncharacter quaternionic automorphic representation $\Pi$;
2. a Hecke character $\chi$ satisfying (4.14) and (4.16); for a cohomological sector it must
   additionally satisfy the stabilizer-center condition after (4.10);
3. a typewise local packet character satisfying (7.12).

Two such data give isomorphic $G$-representations exactly when their pairs differ by a character
of the actual quotient $\mathcal C_L$ as in (4.19), and their packet labels correspond under
the induced Clifford intertwiner. Every representation which occurs has

$$
\boxed{m_G(\rho)=1.}                                          \tag{7.13}
$$

**Proof.** Existence and exhaustion are Sections 7.1--7.2. The kernel equation and fixed
central character are (4.14)--(4.16). The extension classification for the normal pair
$\widetilde G\triangleleft L$ gives pair equivalence and the local labels. Formula (7.12)
gives occurrence and (7.13). If two inequivalent pair orbits produced the same $\rho$, they
would be two ascension orbits across the same compact quotient, contradicting the extension
classification. $\square$

This theorem does not say that a good derived Hecke eigensystem determines $\rho$. Different
$\chi$, local packet labels, or central component characters can have the same derived
eigenvalues. It says that once the full data are fixed, each individual occurring
representation has one automorphic embedding.

### 7.7 The character spectrum

A one-dimensional automorphic representation of $G$ is trivial on $G^{\mathrm{der}}$ and
factors through the actual adelic image of $T_G$. After the positive split center is removed,
the relevant torus class quotient is compact. Fourier theory gives multiplicity one for every
character. Its fixed-level occurrence is still subject to (4.7) and the full component routing;
its cohomological occurrence is additionally subject to the stabilizer-center cancellation
after (4.10).

Characters are kept separate from the noncharacter compatible-pair classification. On the
compact surface they are not boundary Eisenstein terms; their degree-two contribution is the
invariant-form contribution calculated in Section 9.5.

## 8. Finite level, Hecke action, and components

### 8.1 The exact invariant projector

Fix a compatible pair, a type $\mathcal T$, and an occurring complete packet character
$\lambda=(\lambda_f,\lambda_\infty)$.  Let $Y_{\mathcal T,f}$ be the finite-place factor of
the typewise local intertwiner group, with the archimedean label held fixed.  Because (7.8) is
an honest action, its finite packet idempotent is

$$
e_{\lambda,f}
=\frac1{|Y_{\mathcal T,f}|}
\sum_{y\in Y_{\mathcal T,f}}\overline{\lambda_f(y)}I_y.       \tag{8.1}
$$

It commutes with $\widetilde G(\mathbf A)$ and with the compact quotient average (4.23).
Consequently the finite-level space of the descended constituent is

$$
\boxed{
\rho_f^C
\simeq e_{\lambda,f} e_{\overline C}
(\Pi_f\boxtimes\chi_f).}                                      \tag{8.2}
$$

The missing archimedean operation is not implicit in (8.1): the separate projector
$e_{\lambda,\infty}$ is constructed in (9.8).  If the right side of (8.2) is zero, that packet
member does not occur at level $C$. Its dimension is a fixed-vector dimension, not an
automorphic multiplicity.

The formula is invariant under pair equivalence. A quotient character used in (4.19) is
trivial on $\widetilde G$, so it changes the chosen product realization and the names of the
intertwiners but not the image of (8.1)--(8.2).

### 8.2 Lifted Hecke spans

Let $a\in G(\mathbf A_f)$ and choose a lift

$$
\tilde a=(b,z)\in\widetilde G(\mathbf A_f).                    \tag{8.3}
$$

On the compatible product representation, right translation by $a$ is

$$
\rho(a)=\Pi(b)\chi(z).                                        \tag{8.4}
$$

This is independent of the lift. Indeed, another lift is $(br,zr^{-1})$ for
$r\in\mathbf A_{F,f}^\times$, and its extra scalar is

$$
\omega_\Pi(r)\chi(r)^{-1}=1                                   \tag{8.5}
$$

by (4.14).

For a double coset $CaC$, use the usual finite correspondence through
$C_a=C\cap aCa^{-1}$. Analytically its operator is convolution by
$\operatorname{vol}(C)^{-1}\mathbf1_{CaC}$ when $\operatorname{vol}(C)=1$ has not already
been imposed. On the auxiliary side, integrate (8.4) over the compact quotient of the lifted
double coset by $R_F(\mathbf A_f)$; never integrate its noncompact full inverse image. Packet
projection gives

$$
T_{CaC}|_\rho
=e_{\lambda,f}\left(
\int_{\overline C\tilde a\overline C}
\Pi(b_x)\chi(z_x)\,d\bar x
\right)e_{\lambda,f}.                                         \tag{8.6}
$$

Weil's quotient measure makes (8.6) equal to the geometric pull--push operator. It also shows
that changing a lift, a set of right-coset representatives, or a compatible pair representative
does not change the operator.

### 8.3 Good-place polynomials

Let $\Sigma$ contain the quaternionic discriminant, every level and character-conductor place,
and every place without a fixed integral splitting. At a finite place $v\notin\Sigma$ of $F$,
the quaternionic representation is spherical. Write its raw
polynomial as

$$
P_v(\Pi,X)=1-t_v(\Pi)X+q_vs_v(\Pi)X^2.                        \tag{8.7}
$$

The arbitrary-signature quaternionic theorem identifies this polynomial with that of the split
Jacquet--Langlands transfer, with no square root of $q_v$ and no sign change.

To name an analogous polynomial on the PEL tower one needs an **isolating lifted spherical
datum**: a lifted double-coset span as in (8.3) whose $D_v^\times$ component is the standard
raw spherical double coset and whose other quaternionic components act as the identity on
their chosen spherical lines. Its $K$-idele component must complete this datum to an actual
element of $\widetilde G(\mathbf A_f)$. Merely choosing arbitrary noncentral quaternionic
components to satisfy the common-norm equation would insert their Hecke eigenvalues into the
polynomial and is not enough for the formula below.
Let

$$
\gamma_{\tilde v}=\chi(z).                                    \tag{8.8}
$$

On that lifted span, both Satake roots are multiplied by $\gamma_{\tilde v}$, so the exact
polynomial is

$$
\boxed{
P_{\tilde v}(\rho,X)
=1-\gamma_{\tilde v}t_v(\Pi)X
+\gamma_{\tilde v}^{\,2}q_vs_v(\Pi)X^2.}                      \tag{8.9}
$$

If the pair is changed by (4.20), its quaternionic and character factors change by inverse
values on $\beta(\tilde a)=1$, so (8.9) is unchanged.

There is a necessary warning. The derived spherical algebra supplied by the identification
$G^{\mathrm{der}}\simeq\operatorname{Res}D^1$ determines the projective Satake ratio. It does
not by itself name the raw $\operatorname{GL}_2$ operator $T_v$: an element with determinant a
uniformizer at one $F$-place need not have one common rational multiplier at all places above
the same rational prime. Equation (8.9) is asserted only for an isolating lifted datum. In the
absence of one, the intrinsic object is the derived Hecke character together with the central
torus action, not a fictitious single-place double coset of $G$.

### 8.4 Bad places and old level

At a bad place, (8.2) remains the definition. There is no replacement of the local
$D^\times$-fixed-vector space by a guessed $G$-fixed-vector space. The common-multiplier
condition can couple several places of $F$ above one rational prime, the packet projector can
remove part of an invariant space, and a division-algebra congruence subgroup can fix either
zero or a higher-dimensional local space.

The conductor of $\Pi$ is still the exact quaternionic conductor preserved by
Jacquet--Langlands. It predicts the minimal quaternionic newvector level, not the dimension of
(8.2) at an arbitrary PEL level. Enlarging or lowering $C$ changes
$\dim\rho_f^C$ and can create oldvectors; it does not change $m_G(\rho)=1$. At non-neat level,
one first passes to a normal neat subgroup $C'\triangleleft C$ and then takes invariants under
the effective deck group. Stabilizer invariants are a geometric quotient operation, again not
automorphic multiplicity.

### 8.5 The full component set

Let

$$
G(\mathbf Q)_+=\{g\in G(\mathbf Q):gX^+=X^+\},
\qquad
T_G(\mathbf Q)^\dagger=t_G(G(\mathbf Q)_+).                   \tag{8.10}
$$

Strong approximation for the simply connected derived group, which has the two noncompact real
factors, gives

$$
\boxed{
\Gamma_C=
T_G(\mathbf Q)^\dagger\backslash
t_G(G(\mathbf A_f))/t_G(C).}                                  \tag{8.11}
$$

This is the exact set of connected components of the full complex Shimura variety. Both
determinant and multiplier occur through $T_G$; the middle term is the actual image of
$G(\mathbf A_f)$. Replacing it by $\mathbf A_f^\times$ through the multiplier merges
components. Replacing it by all of $T_G(\mathbf A_f)$ can add classes obstructed by (3.12).

The component reciprocity morphism acts on (8.11) by left multiplication. Thus a geometric
component may descend only over its reciprocity stabilizer field. A union used over the reflex
field must be stable under that action. These fields are geometric data from the surface
construction, not consequences of an automorphic central character.

### 8.6 Component-character mixing and proper support

There are two different operations here, and they must not be conflated.  A spectral
idempotent projects to a representation of the **full** group.  Multiplication by the
characteristic function of a proper open-and-closed union is a support idempotent.  In general
the latter does not commute with the right regular action and therefore does not preserve an
individual full-$G$ summand.

The precise mixing group is finite.  Put

$$
\Delta_C^{\mathrm{or}}
=t_G(G(\mathbf Q))\backslash t_G(G(\mathbf A))
 \big/
 t_G(K_\infty^\dagger C),                                    \tag{8.12}
$$

where every term means its actual image in $T_G$, and the connected split center is already
contained in $K_\infty^\dagger$.  Equivalently, $\Delta_C^{\mathrm{or}}$ is the finite abelian
component-and-orientation quotient of the adelic locally symmetric space.  Choosing $X^+$ and
moving every rational real sign into the rational stabilizer identifies its finite-component
slice with (8.11).  Formula (8.12), rather than an ambient torus quotient, is used when real
components also have to be routed.

Let

$$
\Xi_C=\operatorname{Hom}(\Delta_C^{\mathrm{or}},\mathbf C^\times).       \tag{8.13}
$$

Inflation makes $\kappa\in\Xi_C$ a finite-order automorphic component character, trivial on
$G(\mathbf Q)$, $K_\infty^\dagger$, and $C$.  Multiplication
$M_\kappa f(g)=\kappa(g)f(g)$ is an honest action of $\Xi_C$ on the full level-$C$
automorphic complex.  If

$$
\mathcal W_C^q(\rho,\xi)
=\mathcal M_G(\rho)\otimes\rho_f^C\otimes
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty\otimes V_\xi),
$$

then

$$
M_\kappa\mathcal W_C^q(\rho,\xi)
=\mathcal W_C^q(\rho\otimes\kappa,\xi).                     \tag{8.14}
$$

This action can change a finite central character and, when $G(\mathbf R)$ is disconnected,
an archimedean extension label.  It is therefore incorrect to apply a general proper-support
projector inside one fixed-$\Omega$, fixed-$\rho$ tensor factor.

Let $\mathscr U\subset\Delta_C^{\mathrm{or}}$ and let $e_{\mathscr U}$ mean multiplication by
$\mathbf1_{\mathscr U}$.  With

$$
\widehat{\mathbf1}_{\mathscr U}(\kappa)
=\frac1{|\Delta_C^{\mathrm{or}}|}
  \sum_{\delta\in\mathscr U}\overline{\kappa(\delta)},
\qquad
e_{\mathscr U}
=\sum_{\kappa\in\Xi_C}
  \widehat{\mathbf1}_{\mathscr U}(\kappa)M_\kappa,          \tag{8.15}
$$

Fourier inversion exhibits the mixing explicitly.  For a full-group representation define

$$
\begin{aligned}
\mathcal O_C(\rho)&=\{\rho\otimes\kappa:\kappa\in\Xi_C\}/\simeq,\\
S_C(\rho)&=\{\kappa\in\Xi_C:\rho\otimes\kappa\simeq\rho\},\\
\mathcal W_C^q(\mathcal O,\xi)
&=\bigoplus_{\rho'\in\mathcal O}\mathcal W_C^q(\rho',\xi).
\end{aligned}                                                  \tag{8.16}
$$

Thus $|\mathcal O_C(\rho)|=|\Xi_C|/|S_C(\rho)|$, and (8.15) preserves the **orbit sum**
$\mathcal W_C^q(\mathcal O,\xi)$, not its individual summands.  The exact proper-support
block is

$$
\boxed{
\mathcal W_{C,\mathscr U}^q(\mathcal O,\xi)
=e_{\mathscr U}\mathcal W_C^q(\mathcal O,\xi).}              \tag{8.17}
$$

For completeness, let $\mathscr R_C^q(\xi)$ be the set of occurring isomorphism classes in the
full level-$C$ cohomology, across all central sectors under consideration.  Since every $M_\kappa$
is invertible and (8.14) carries an isotypic summand onto an isotypic summand, the sets
$\mathcal O_C(\rho)$ are either equal or disjoint and exhaust $\mathscr R_C^q(\xi)$.  Hence

$$
\bigoplus_{\rho\in\mathscr R_C^q(\xi)}\mathcal W_C^q(\rho,\xi)
=\bigoplus_{\mathcal O\in\Xi_C\backslash\mathscr R_C^q(\xi)}
  \mathcal W_C^q(\mathcal O,\xi).
$$

This is the disjoint, complete orbit decomposition to which (8.17) is applied.

There is also an intrinsic dimension formula.  The actual multiplication operators
$M_s$, $s\in S_C(\rho)$, give an honest stabilizer action on
$\mathcal W_C^q(\rho,\xi)$.  For $\theta\in\widehat{S_C(\rho)}$ put

$$
a_{\rho,\theta}^q
=\dim\operatorname{Hom}_{S_C(\rho)}
   \bigl(\theta,\mathcal W_C^q(\rho,\xi)\bigr).
$$

Writing $\operatorname{ev}_\delta(s)=s(\delta)$, induction from the stabilizer gives

$$
\boxed{
\dim\mathcal W_{C,\mathscr U}^q(\mathcal O,\xi)
=\sum_{\delta\in\mathscr U}
  a_{\rho,\operatorname{ev}_\delta|_{S_C(\rho)}}^q.}         \tag{8.18}
$$

Indeed, the map $[\kappa,w]\mapsto M_\kappa w$ identifies
$\operatorname{Ind}_{S_C(\rho)}^{\Xi_C}\mathcal W_C^q(\rho,\xi)$ with the orbit sum in
(8.16).  Since $\Xi_C$ is the character group of $\Delta_C^{\mathrm{or}}$, its
$\delta$-weight occurs in this induced module with multiplicity
$\dim\operatorname{Hom}_{S_C(\rho)}
(\operatorname{ev}_\delta,\mathcal W_C^q(\rho,\xi))$.
Multiplication by $\mathbf1_{\mathscr U}$ keeps exactly the weights with
$\delta\in\mathscr U$, proving (8.18).

For $\mathscr U=\Delta_C^{\mathrm{or}}$ this is
$|\mathcal O_C(\rho)|\dim\mathcal W_C^q(\rho,\xi)$, as it must be.  For a proper union it
need not be a fixed fraction of that number.

A Hecke span with component route $r$ carries the $\mathscr U$-block to the
$\mathscr U r$-block; it is an endomorphism exactly when the union is stable under that route
(or after replacing it by the cut-down span $e_{\mathscr U}Te_{\mathscr U}$).  Galois acts on
$\Delta_C^{\mathrm{or}}$ through component reciprocity.  Hence $e_{\mathscr U}$ is defined over
$E_{\mathscr U}$ exactly when $\mathscr U$ is stable under the corresponding Galois subgroup.
If a central-character projector $e_\Omega$ is also used, it commutes with
$e_{\mathscr U}$ only when $\mathscr U$ is stable under the central component translations
occurring in $e_\Omega$; otherwise (8.17) necessarily contains the whole finite orbit of
central sectors.  When it is stable, one may apply $e_\Omega$ to (8.17); equivalently,
(8.16)--(8.18) may be formed inside the fixed sector with the subgroup

$$
\Xi_{C,\Omega}
=\{\kappa\in\Xi_C:\kappa|_{Z_G(\mathbf A)}=1\}.
$$

## 9. Matsushima in the fixed central sector

### 9.1 Automorphic cochains on the compact surface

Let

$$
\operatorname{Sh}_{C}^{\mathrm{all}}(\mathbf C)
=G(\mathbf Q)\backslash(X^{\mathrm{or}}\times G(\mathbf A_f)/C)       \tag{9.1}
$$

denote the smooth projective union over the complete component-and-orientation orbit
$\Delta_C^{\mathrm{or}}$.  A proper ground-field-defined union is denoted
$\operatorname{Sh}_{C,\mathscr U}$ and its differential-form complex is
$e_{\mathscr U}$ applied to the complex of (9.1).  Let $\mathcal V_\xi$ be the local system
associated with $V_\xi$. The tangent representation is

$$
\mathfrak p_\mathbf C
=\mathfrak g_\mathbf C/\mathfrak k_\mathbf C^\dagger.         \tag{9.2}
$$

It contains the two active disk tangents and no positive central line. On the **full** union,
differential forms in the fixed $\Omega$-sector are the automorphic cochains

$$
C^q_{\mathrm{aut}}(C,\Omega,\xi)
=\operatorname{Hom}_{K_\infty^\dagger}
\left(
\bigwedge^q\mathfrak p_\mathbf C,\,
\mathcal A(G,\Omega)^C\otimes V_\xi
\right).                                                       \tag{9.3}
$$

The exterior derivative is the relative Lie algebra differential. The full stabilizer-center
condition after (4.10) is required before (9.3) can model differential forms. Failure on the
positive split center gives the contractible central complex; failure on the compact CM center
makes the equivariant cochain space zero.  For a general proper $\mathscr U$, one first takes
the direct sum of (9.3) over all finite central sectors in its $\Xi_C$-orbits and only then
applies $e_{\mathscr U}$.

### 9.2 A direct compact-Hodge proof

The surface (9.1) is compact. Every de Rham class therefore has a unique harmonic
representative, and the harmonic kernel in each degree is finite dimensional. The Laplacian
commutes with the right finite-adelic action and the fixed central action.  A support
idempotent commutes with the differential and the componentwise Laplacian, but not in general
with the right regular action.

Insert the discrete spectral decomposition (4.6) into (9.3). Rather than commuting cohomology
with an uncontrolled Hilbert sum, first intersect with the finite-dimensional harmonic kernel.
Only finitely many spectral summands remain. On each one, the differential is exactly the
relative differential. This proves the fixed-central Matsushima formula

$$
\boxed{
H_B^q(\operatorname{Sh}_{C}^{\mathrm{all}},\mathcal V_\xi\otimes\mathbf C)[\Omega]
\simeq
\bigoplus_{\substack{\rho\\ \omega_\rho=\Omega}}
\mathcal W_C^q(\rho,\xi).}                                   \tag{9.4}
$$

The displayed full-union notation in (9.4) is essential.  The notation $[\Omega]$ refers to the finite
central-routing sector described after (4.7).  If that sector is not chosen, one sums (9.4)
over all compatible finite central characters.  For a proper union, (9.4) is replaced by the
orbit formula (9.12) below; writing the old left side with an arbitrary $\mathscr U$ would
falsely assert that $e_{\mathscr U}$ preserves every $\rho$.

Finite Hecke equivariance follows on cochains: right convolution is the analytic form of
pullback followed by normalized trace along the finite Hecke span. Inversion of a double coset
is the adjoint under the automorphic inner product, and transposition of the span is the adjoint
under Poincare duality. The coherent measures of Section 4.1 make the two normalizations agree.

### 9.3 The archimedean Clifford projector

Assume constant coefficients and a cohomological compatible pair. At each active place, put
$s_i=\operatorname{sgn}\circ\det$ on $D_{v_i}^\times\simeq\operatorname{GL}_2(\mathbf R)$.
The full weight-two representation is self-twist invariant under $s_i$, and its restriction
to the positive-determinant identity component is as below.  The $K$-character factor is
unchanged by this twist because $N_{\mathbf C/\mathbf R}(\mathbf C^\times)=\mathbf R_{>0}$.

$$
D_2|_{\operatorname{GL}_2(\mathbf R)^+}
=D_2^+\oplus D_2^-.                                           \tag{9.5}
$$

Relative to $\mathbf R_{>0}\operatorname{SO}(2)$, each summand has one-dimensional cohomology
in degree one:

$$
H^q(\mathfrak{gl}_2,\mathbf R_{>0}\operatorname{SO}(2);D_2^\pm)
=
\begin{cases}
\mathbf C\,\eta^\pm,&q=1,\\
0,&q\ne1.
\end{cases}                                                    \tag{9.6}
$$

The $+$ line has Hodge type $(1,0)$ and the $-$ line type $(0,1)$. At a definite real place,
constant coefficients require the trivial compact adjoint representation and contribute only
degree zero.  Choose the self-intertwiner $I_i:D_2\to D_2\otimes s_i$ with $I_i^2=1$ and
normalize its two identity-component eigenspaces by
$I_i|_{D_2^\epsilon}=\epsilon$.  The effective archimedean norm-kernel self-twist group is

$$
Y_\infty^{\mathrm{eff}}=
\begin{cases}
\langle s_1,s_2\rangle\simeq(\mathbf Z/2\mathbf Z)^2,&d>2,\\
\langle s_1s_2\rangle\simeq\mathbf Z/2\mathbf Z,&d=2.
\end{cases}                                                    \tag{9.7}
$$

Indeed, when $d>2$ a definite quaternionic factor forces the common multiplier to be positive.
A sign at either active factor can be balanced by a sign at a definite coordinate in the
character of $(\mathbf R^\times)^d/\mathbf R^\times$; that definite sign is invisible because
the reduced norm of $\mathbf H^\times$ is $\mathbf R_{>0}$.  When $d=2$ there is no such
coordinate, so triviality on the diagonal leaves only $s_1s_2$.

The product ascension must now be projected to the actual descended $G(\mathbf R)$
constituent.  Each effective character in (9.7) is trivial on $\widetilde G(\mathbf R)$, so
its normalized intertwiner commutes there; ordinary Clifford theory identifies the simultaneous
eigenspaces with the irreducible constituents, which descend through $\theta$ because the
kernel acts trivially.  If $\lambda_\infty$ is the required
archimedean Clifford label, put

$$
e_{\lambda,\infty}=
\begin{cases}
\dfrac14(1+\lambda_1 I_1)(1+\lambda_2 I_2),
 &d>2,\quad\lambda_\infty=(\lambda_1,\lambda_2),\\[2mm]
\dfrac12(1+\lambda I_1I_2),
 &d=2,\quad\lambda_\infty=\lambda.
\end{cases}                                                    \tag{9.8}
$$

Here each $\lambda_i$ and $\lambda$ is $\pm1$.  Before projection the product ascension has
the four-line space

$$
\mathcal A_\infty^2
=\bigoplus_{\epsilon_1,\epsilon_2\in\{+,-\}}
 \mathbf C\,\eta_1^{\epsilon_1}\otimes\eta_2^{\epsilon_2},
\qquad
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty)=
\begin{cases}
e_{\lambda,\infty}\mathcal A_\infty^2,&q=2,\\
0,&q\ne2.
\end{cases}                                                    \tag{9.9}
$$

On its displayed basis the projector acts by

$$
e_{\lambda,\infty}
 (\eta_1^{\epsilon_1}\otimes\eta_2^{\epsilon_2})
=
\begin{cases}
\eta_1^{\epsilon_1}\otimes\eta_2^{\epsilon_2},
 &d>2\text{ and }(\epsilon_1,\epsilon_2)=(\lambda_1,\lambda_2),\\
\eta_1^{\epsilon_1}\otimes\eta_2^{\epsilon_2},
 &d=2\text{ and }\epsilon_1\epsilon_2=\lambda,\\
0,&\text{otherwise}.
\end{cases}
$$

Thus the exact orientation rank and Hodge vector of an **individual** descended real
constituent are

$$
\begin{array}{c|c|c|c}
\text{case}&\lambda_\infty&
\dim e_{\lambda,\infty}\mathcal A_\infty^2&
(h^{2,0},h^{1,1},h^{0,2})\\ \hline
d>2&( +,+)&1&(1,0,0)\\
d>2&( +,-)\text{ or }(-,+)&1&(0,1,0)\\
d>2&(-,-)&1&(0,0,1)\\
d=2&+&2&(1,0,1)\\
d=2&-&2&(0,2,0).
\end{array}                                                    \tag{9.10}
$$

For $d=2$, an element with negative common multiplier has negative determinant at both active
places.  It exchanges $D_2^+$ and $D_2^-$ simultaneously, so it ties the $++$ and $--$ lines
in the $+$ constituent and the $+-$ and $-+$ lines in the $-$ constituent.  Neither pair can
be split by a $G(\mathbf R)$-equivariant projector.  The often quoted vector $(1,2,1)$ belongs
to the **unprojected product ascension**, not to one full-$G$ representation.

The real classification also proves the converse: for constant coefficients, a noncharacter
$\rho$ has nonzero relative cohomology only when its quaternionic ascension has type (4.17) and
its center satisfies the full stabilizer-center condition after (4.10). Higher discrete series
have the wrong minimal rotation weight,
principal and complementary series have the wrong infinitesimal character, and a nontrivial
definite adjoint type has no invariant coefficient vector.

### 9.4 Full-orbit and proper-support formulas

Let $\mathscr P(C,\Omega)$ be the set of compatible-pair orbits, together with complete local
packet labels, which satisfy:

- the global sign equation (7.12);
- the central equations (4.14), (4.16), and the full stabilizer-center condition after (4.10);
- the parallel-weight-two real condition (4.17);
- nonvanishing of the finite level space (8.2).

Then (7.13), (9.4), and the archimedean projector give the strongest individual-representation
statement, on the full component-and-orientation orbit:

$$
\boxed{
H_B^2(\operatorname{Sh}_{C}^{\mathrm{all}},\mathbf C)_{\mathrm{nch}}[\Omega]
\simeq
\bigoplus_{\rho\in\mathscr P(C,\Omega)}
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
e_{\lambda(\rho),\infty}\mathcal A_\infty^2.}                \tag{9.11}
$$

There is no unrecorded multiplicity factor in (9.11).  The $\rho$-block has dimension
$\dim\rho_f^C$ for $d>2$ and $2\dim\rho_f^C$ for $d=2$, with its Hodge vector obtained by
scaling the appropriate row of (9.10).

For a proper union let $\mathfrak O_C^{\mathrm{coh}}$ be the finite set of $\Xi_C$-orbits of
occurring noncharacter cohomological representations, across every central sector which the
support projector mixes.  The stabilizer action preserves Hodge type; write
$a_{\rho,\theta}^{p,q}$ for the $\theta$-multiplicity in the $(p,q)$ part of
$\mathcal W_C^{p+q}(\rho,\mathbf1)$, so
$a_{\rho,\theta}^2=\sum_{p+q=2}a_{\rho,\theta}^{p,q}$.  Compact Hodge theory and
(8.15)--(8.17) give

$$
\boxed{
\begin{aligned}
H_B^2(\operatorname{Sh}_{C,\mathscr U},\mathbf C)_{\mathrm{nch}}
&\simeq
\bigoplus_{\mathcal O\in\mathfrak O_C^{\mathrm{coh}}}
e_{\mathscr U}
\left(
 \bigoplus_{\rho\in\mathcal O}
 \mathcal M_G(\rho)\otimes\rho_f^C\otimes
 e_{\lambda(\rho),\infty}\mathcal A_\infty^2
\right),\\
\dim(\mathcal O,\mathscr U)
&=\sum_{\delta\in\mathscr U}
a_{\rho,\operatorname{ev}_\delta|_{S_C(\rho)}}^2,\\
h^{p,2-p}(\mathcal O,\mathscr U)
&=\sum_{\delta\in\mathscr U}
a_{\rho,\operatorname{ev}_\delta|_{S_C(\rho)}}^{p,2-p}.
\end{aligned}}                                                \tag{9.12}
$$

The second equality uses (8.18), with the projected archimedean space already included in
$\mathcal W_C^2(\rho,\mathbf1)$.  It is not the rank of $e_{\mathscr U}$ on one $\rho$ tensor
factor.  For $d>2$ the positive common multiplier leaves no disconnected real extension to
route; for $d=2$ a component character can change the extension across the simultaneous
negative component.  In both cases (9.12) routes the finite label, the full real constituent,
and the central character together.  On the product model the compatibility is

$$
M_\kappa e_{\lambda(\rho),\infty}
=e_{\lambda(\rho\otimes\kappa),\infty}M_\kappa.
$$

The Clifford projector (9.8) is applied before forming
the orbit sum, while the support projector is applied only after that sum.

### 9.5 The character contribution

Let $\rho$ be an automorphic character of $G$. Its derived real action is trivial. The
$K_\infty^\dagger$-invariant differential forms on the product of two disks are generated by
the two invariant area forms $\omega_1,\omega_2$. Hence

$$
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty)
\simeq
\begin{cases}
\mathbf C,&q=0,4,\\
\mathbf C\omega_1\oplus\mathbf C\omega_2,&q=2,\\
0,&q=1,3,
\end{cases}                                                    \tag{9.13}
$$

provided the central cancellation holds. The two degree-two lines both have Hodge type
$(1,1)$. On the full union they are two lines for each compatible character.  On a proper
union, automorphic characters are grouped into their $\Xi_C$-orbits and $e_{\mathscr U}$ is
applied to each orbit sum exactly as in (9.12).  It is not applied to one character summand,
and no additional number of components is multiplied into the result.

## 10. Coefficient fields and compatible realizations

### 10.1 Fields attached to a compatible pair

Assume $\Pi$ has the parallel-weight-two arithmetic normalization and $\chi$ is algebraic.
Let

$$
E_\Pi=\mathbf Q\bigl(t_v(\Pi),s_v(\Pi):v\notin\Sigma\bigr)      \tag{10.1}
$$

be the common good Hecke field supplied by the quaternionic transfer, and let $E_\chi$ be the
number field generated by the good ideal values and finite local roots of unity of $\chi$.
For the fixed central and component data, let $E_{\Omega,\Gamma}$ contain their finite character
values.  For a proper union it also contains the values of the finite group $\Xi_C$ needed to
form its orbit sum and the field of definition of that union. Packet values in
(7.10)--(7.12), including the archimedean labels in (9.8), are signs. Define

$$
E_0(\Pi,\chi)
=E_\Pi E_\chi E_{\Omega,\Gamma}.                              \tag{10.2}
$$

Every eigenvalue of an actual lifted good span (8.6), and every coefficient of (8.9), lies in
$E_0(\Pi,\chi)$. Formula (8.5) proves that this field-valued eigencharacter is independent of
the representative of the compatible-pair orbit.

For a finite place $\lambda\mid\ell$ of a field containing $E_\chi$, the algebraic character
$\chi$ has an $\ell$-adic avatar $\chi_\lambda$. Away from $\ell$ and its conductor, arithmetic
reciprocity gives

$$
\chi_\lambda(\operatorname{Frob}_w)=\iota_\lambda(\chi(\mathfrak p_w)).  \tag{10.3}
$$

Thus the scalar $\gamma_{\tilde v}$ in (8.9) has the same automorphic and one-dimensional
Galois interpretation. This proves compatibility of the central character twist. It does not
assert that the rank-two quaternionic polynomial is already the Frobenius polynomial of a
particular two-dimensional summand of the surface; that requires the projector discussed below.

The field of rationality and a field of definition remain different. Equation (10.2) controls
the good commutative eigenvalues and packet signs. A model of the full bad-place module can
require a finite extension, and an irreducible module for a noncommutative rational Hecke block
can have nontrivial Schur index.

### 10.2 The finite geometric Hecke algebra

Let $\mathbb T^{\mathrm{abs}}$ be the algebra over $\mathbf Q$ generated on the full union by
a finite set of Hecke spans, their transposes, the needed finite central translations, and the
ground-field open-and-closed component identities.  Write $\mathbb T_C^{\mathrm{all}}$ for its
image.  For a proper ground-field union use the corner algebra.  Thus

$$
\begin{aligned}
\mathbb T_C^{\mathrm{all}}
&\subset
\operatorname{End}_{\mathbf Q}
H_B^2(\operatorname{Sh}_{C}^{\mathrm{all}},\mathbf Q),\\
\mathbb T_{C,\mathscr U}
&=e_{\mathscr U}\mathbb T_C^{\mathrm{all}}e_{\mathscr U}
\subset
\operatorname{End}_{\mathbf Q}
H_B^2(\operatorname{Sh}_{C,\mathscr U},\mathbf Q).
\end{aligned}                                                  \tag{10.4}
$$

Both images are finite dimensional. The abstract algebra and its full image need not have the
same kernel.  A routed span from $\mathscr U$ to a different union is retained in the ambient
algebra; it becomes an endomorphism of the proper union only after the indicated two-sided
cutdown.

The full image in (10.4) is semisimple. After extending to $\mathbf C$, the harmonic realization of
Section 9.2 and the coherent quotient measures make a transposed Hecke span the adjoint
operator for a positive definite $L^2$ metric. The algebra was closed under transpose, so
its Jacobson radical is adjoint-stable. A nonzero nilpotent adjoint-stable ideal would contain
$xx^\dagger$ for a nonzero $x$, but a positive semidefinite nilpotent operator is zero. Hence
the radical vanishes. This proof uses the acting algebra on the finite cohomology space; it does
not claim that an infinite formal Hecke algebra is reduced.  A corner of a semisimple
finite-dimensional algebra is semisimple, so the same holds for $\mathbb T_{C,\mathscr U}$.

The Wedderburn centers are number fields. On the full union, the central character of a block
containing an individual $\rho$ is a finite extension of the good field (10.2). On a proper
union, the natural ambient label is the component-character orbit $\mathcal O_C(\rho)$, or a
coefficient orbit of such orbits.  The corner can split its supported image further, but no
factor is thereby an individual full-$G$ summand. These centers are determined geometrically
even when a rational structure on every bad local automorphic type has not been supplied.

### 10.3 Projectors and splitting fields

Let $A$ be a simple factor of the relevant finite geometric Hecke image, with center $E_A$.
The identity of that factor is a rational central idempotent and cuts out the full rational
isotypic block. It does not select an embedding of $E_A$ or one absolutely irreducible module.
Choose an embedding $E_A\hookrightarrow L$ and a finite field $L$ which splits the resulting
central simple algebra. Enlarge $L$, with a chosen embedding, to contain $E_{\mathscr U}$ and
the values of $\Xi_C$ before forming the de Rham scalar extension below. Matrix idempotents
over $L$ then isolate a chosen absolutely simple labeled block. Other embeddings give its
coefficient conjugates.

On the full union, suppose the chosen spans distinguish an individual spectral label and write
its idempotent as $e_\rho$.  For a component-character orbit put
$e_{\mathcal O}=\sum_{\rho'\in\mathcal O}e_{\rho'}$.  Equation (8.14) gives
$M_\kappa e_{\mathcal O}M_\kappa^{-1}=e_{\mathcal O}$, so $e_{\mathcal O}$ commutes with every
component support idempotent.  Assume that this orbit is a union of simple
constituents of the chosen geometric Hecke image, separated there from its complement.  The
finite-dimensional semisimple algebra then expresses the orbit idempotent and the exact
proper-support idempotent in the form

$$
e_{\mathcal O}=P_{\mathcal O}(T_1,\ldots,T_s),
\qquad
e_{\mathscr U,\mathcal O}
=e_{\mathscr U}e_{\mathcal O}
=e_{\mathcal O}e_{\mathscr U},
\qquad P_{\mathcal O}\in L\langle X_1,\ldots,X_s\rangle.    \tag{10.5}
$$

For the full union $e_{\mathscr U}=1$, and $e_\rho$ may replace $e_{\mathcal O}$ whenever the
individual label is defined over $L$.  The coefficients can have denominators. They are
harmless on rational vector spaces, but the projector need not preserve the natural integral lattice at a denominator prime. The saturated
intersection with that lattice is canonical; it is an integral direct summand only when the
idempotent is integral there.

The analytic operator $e_{\lambda,\infty}$ in (9.8) identifies which full-$G$ constituent a
spectral block contains; it is not added to the $T_i$ merely because it has a name.  For
$d>2$ that constituent has one orientation line.  For $d=2$ its two lines are tied by the
simultaneous negative component and no $G(\mathbf R)$-equivariant projector separates them.
A geometric projector transports precisely the individual full-union block or the
proper-support orbit block in (10.5), not the four-line unprojected product ascension.

### 10.4 Betti, de Rham, and etale compatibility

Assume the smooth projective union, its component identities, and every span in (10.5) are defined over
$E_{\mathscr U}$. At neat level, the Hecke correspondence is a finite etale span after passage
to the common level, hence an admissible finite-flat lci span. Component identities are
admissible spans of finite disjoint unions. The functorial surface comparison theorem therefore
applies to each $T_i$ and to the polynomial (10.5).

Let $e_{\mathscr B}$ denote either a field-defined individual projector $e_\rho$ on the full
union or the proper-support orbit projector $e_{\mathscr U,\mathcal O}$ of (10.5).  For every
embedding $E_{\mathscr U}\hookrightarrow\mathbf C$ and every finite place
$\lambda\mid\ell$ of $L$, functoriality gives compatible images in the full ambient union:

$$
\begin{aligned}
V_{B,\mathscr B}&=e_{\mathscr B}H_B^2(\operatorname{Sh}_{C}^{\mathrm{all}},L),\\
V_{\mathrm{dR},\mathscr B}&=e_{\mathscr B}H_{\mathrm{dR}}^2
(\operatorname{Sh}_{C}^{\mathrm{all}}/E_{\mathscr U})\otimes_{E_{\mathscr U}}L,\\
V_{\lambda,\mathscr B}&=e_{\mathscr B}H_{\mathrm{et}}^2
(\operatorname{Sh}_{C,\overline E_{\mathscr U}}^{\mathrm{all}},L_\lambda).
\end{aligned}                                                  \tag{10.6}
$$

Their ranks agree. The first is a Hodge structure with the orientation types computed in
(9.9)--(9.12); the second is filtered; the third is a continuous
$\operatorname{Gal}(\overline E_{\mathscr U}/E_{\mathscr U})$-representation. Every etale
operator is Galois equivariant because its two legs and regular-lci orientation are defined over
$E_{\mathscr U}$. Betti cohomology itself is not a Galois representation; comparison does not
turn it into one.

For $e_{\mathscr B}=e_{\mathscr U,\mathcal O}$, the image of (10.6) is canonically the
$\mathcal O$-summand of the cohomology of $\operatorname{Sh}_{C,\mathscr U}$ in (9.12).
Using $e_\rho e_{\mathscr U}$ instead would not define an idempotent in general.

If one geometric component is used, $E_{\mathscr U}$ must contain its reciprocity stabilizer
field. If a Galois-stable union is used, the union projector is defined over its common field.
Choosing a component over too small a field can make Galois permute the proposed block rather
than preserve it.

### 10.5 Galois and Frobenius assertions with their hypotheses

Three levels of arithmetic assertion must be distinguished.

1. **Unconditional at the chosen ground field.** The space $V_{\lambda,\mathscr B}$ in (10.6) is
   Galois stable, and every ground-field Hecke span commutes with Galois. Its dimension and Hodge
   numbers agree with the Betti calculation.
2. **At a verified smooth good model.** If the surface, component union, and all spans in
   (10.5) extend as smooth proper and finite-flat lci data over a henselian DVR of residue
   characteristic $p\ne\ell$, smooth proper specialization identifies $V_{\lambda,\mathscr B}$ with
   its special-fiber block. It is unramified and Frobenius compatible there.
3. **Coefficient-independent projected Frobenius polynomial.** To deduce this from fixed-point
   degrees, the projector must kill every etale degree other than two, its spans must satisfy
   the required transverse or clean-excess fixed-locus hypotheses for enough Frobenius powers,
   and every vertical component must be included. Under those hypotheses, Newton identities
   give a polynomial over $L$ independent of $\lambda$.

The rank-two polynomial (8.7) attached to $\Pi$ is a quaternionic Hecke label. Equation (8.9)
shows how an actual lifted PEL Hecke span sees that label. It is not automatically the
characteristic polynomial of Frobenius on $V_{\lambda,\mathscr B}$.  On the full union an
individual noncharacter block has rank $\dim\rho_f^C$ for $d>2$ and
$2\dim\rho_f^C$ for $d=2$; a proper-support orbit block has the rank (8.18).  A further
geometric or representation-theoretic construction is required whenever one wants a different
factor. The comparison theorem faithfully transports such a projector once supplied; it does
not infer it from equal good Hecke names.

## 11. The central descent theorem

### 11.1 Complete statement

We collect the result in a form that can be used without reopening any hidden central or
component convention.

**Theorem 11.1 (central automorphic descent for the rational-multiplier surface group).**
Let $F$, $K$, $W=b\langle1,-a\rangle$, $D=(K/F,a)$, and $G=G_W$ satisfy the standing
hypotheses of Section 1.2. Let $C\subset G(\mathbf A_f)$ be center-detecting and neat, let
$\operatorname{Sh}_C^{\mathrm{all}}$ contain the complete component-and-orientation orbit, and
fix a unitary central character $\Omega$ satisfying (4.7).  Separately, let
$\mathscr U\subset\Delta_C^{\mathrm{or}}$ be a ground-field-defined open-and-closed union,
stable under the Hecke routes in use.  No fixed-$\Omega$ assertion is made for this proper union
unless it is also stable under the central translations defining that sector.

Then:

**(a) Exact groups.** The dimensions and structural groups are

$$
\begin{gathered}
\dim G=4d+1,\qquad
G^{\mathrm{der}}=\operatorname{Res}_{F/\mathbf Q}D^1,\qquad
\dim G^{\mathrm{der}}=3d,\\
Z_G=\{z\in\operatorname{Res}_{K/\mathbf Q}\mathbf G_m:
N_{K/F}z\in\mathbf G_m\},\qquad \dim Z_G=d+1,\\
T_G=\{(\delta,q):N_{K/F}\delta=q^2\},\qquad \dim T_G=d+1.
\end{gathered}                                                  \tag{11.1}
$$

Multiplication gives (2.9) with kernel
$\operatorname{Res}_{F/\mathbf Q}\mu_2$. The common-norm group

$$
H=\{b\in\operatorname{Res}_{F/\mathbf Q}D^\times:
\operatorname{Nrd}(b)\in\mathbf G_m\}                          \tag{11.2}
$$

has dimension $3d+1$, derived group $G^{\mathrm{der}}$, connected center
$\mathbf G_m$, and full center (2.16) with geometric component group of order $2^{d-1}$.
The quotient $G/H$ is the norm-one torus $U$ and is split by (2.23).

With $S=(\operatorname{Res}_{F/\mathbf Q}\mathbf G_m)/\mathbf G_m$ and
$L=\operatorname{Res}D^\times\times\operatorname{Res}_K\mathbf G_m$, the auxiliary sequences
are

$$
1\to H\to\operatorname{Res}D^\times\to S\to1,\qquad
1\to\widetilde G\to L\to S\to1,                               \tag{11.3}
$$

and

$$
1\to\operatorname{Res}_{F/\mathbf Q}\mathbf G_m
\to\widetilde G\xrightarrow{\theta}G\to1.                     \tag{11.4}
$$

**(b) Point images.** For $g\in G(\mathbf Q)$, choose $x\in K^\times$ with
$x/c(x)=\det_K(g)/\nu(g)$. Its finite-cover obstruction is

$$
\operatorname{ob}_G(g)
=\left[\nu(g)/N_{K/F}(x)\right]\in F^\times/F^{\times2},       \tag{11.5}
$$

with exact image (3.9). The local formula is (3.10), the adelic obstruction is the restricted
tuple (3.12), and neither is assumed zero. The analogous obstruction for
$G^{\mathrm{der}}\times\mathbf G_m\to H$ is the square class of the common norm.
In contrast, (11.4) is onto on rational, local, finite adelic, and full adelic points; integral
lifts exist at almost all places.

**(c) Central characters, measures, and level.** The fixed automorphic Hilbert space is
$L^2(G,\Omega)$ of (4.3)--(4.6). The real relative group is

$$
K_\infty^\dagger=A_G(\mathbf R)^0K_{h,c}^0,                   \tag{11.6}
$$

and nonzero cohomology requires $\Omega_\infty\xi=1$ on
$Z_G(\mathbf R)\cap K_\infty^\dagger$, including both the positive split center and the
compact CM center.
A quaternionic-character pair descends through (11.4) exactly when

$$
\chi|_{C_F}=\omega_\Pi,\qquad
\chi|_{Z_G(\mathbf A)}=\Omega.                                \tag{11.7}
$$

The finite level on the auxiliary representation is the compact quotient

$$
\theta^{-1}(C)/R_F(\mathbf A_f)\simeq C,                      \tag{11.8}
$$

with its probability average. The full inverse image $\theta^{-1}(C)$ is noncompact and is
not a Hecke support.

**(d) Common-norm intermediary and quaternionic transfer.** Every noncharacter automorphic
representation of $H$ ascends across the actual compact norm quotient to a noncharacter
automorphic $\Pi$ of $D^\times(\mathbf A_F)$, unique up to quotient characters. The restriction
packet retains the self-intertwiner factor set, and its exact multiplicity is the projective
Morita formula (6.6). The arbitrary-signature Jacquet--Langlands theorem labels $\Pi$ by the
unique cuspidal $\pi$ satisfying the exact division-place image condition and preserves all
local components under local Jacquet--Langlands, as well as central characters, conductor,
local factors, the good raw polynomial, multiplicity, and the parallel-weight-two Hecke field.

**(e) Full-group classification and multiplicity.** Every noncharacter automorphic
representation $\rho$ of $G$ in the fixed sector arises from a compatible pair
$\Pi\boxtimes\chi$, modulo the character group of the actual compact quotient $\mathcal C_L$,
and a local packet label. At a fixed type the invisible abstract self-twist group is elementary
$2$-abelian, its tensor-intertwiner cocycle is trivial, and

$$
Y_{\mathrm{aut}}(\Pi,\chi)\subseteq\{1,\eta_{K/F}\}.          \tag{11.9}
$$

The exact occurrence and multiplicity formula is

$$
m_G(\rho)
=\frac1{|Y_{\mathrm{aut}}|}
\sum_{\eta\in Y_{\mathrm{aut}}}
\varepsilon_{\Pi,\chi}(\eta)
\overline{\langle\eta,\rho\rangle}
\in\{0,1\}.                                                    \tag{11.10}
$$

Thus every individual representation which occurs has $m_G(\rho)=1$. A local packet may have
many typewise members, but only those satisfying the global sign equation occur.

**(f) Level, Hecke, and components.** For an occurring complete packet label, the finite
projector $e_{\lambda,f}$ gives

$$
\rho_f^C
\simeq e_{\lambda,f} e_{\overline C}(\Pi_f\boxtimes\chi_f).   \tag{11.11}
$$

If $a\in G(\mathbf A_f)$ has lift $(b,z)$, then its action is $\Pi(b)\chi(z)$ and is
lift-independent. At an isolating lifted good spherical datum the polynomial is (8.9).
The component set is

$$
T_G(\mathbf Q)^\dagger\backslash
t_G(G(\mathbf A_f))/t_G(C),                                   \tag{11.12}
$$

with the actual torus image. A selected union acts through the single routed projector
$e_{\mathscr U}$ only on the full component-character orbit sum.  More precisely,
$\Delta_C^{\mathrm{or}}$ and $\Xi_C$ are (8.12)--(8.13), multiplication obeys
$M_\kappa\mathcal W(\rho)=\mathcal W(\rho\otimes\kappa)$, the orbit and stabilizer are
(8.16), and the supported block and its dimension are (8.17)--(8.18).  In particular, a
proper $e_{\mathscr U}$ is not an endomorphism of one full-$G$ summand.

**(g) Archimedean projector, cohomology, and realizations.** At the two active places the
unprojected product ascension has four orientation lines, but the actual descended real
constituent is selected by $e_{\lambda,\infty}$ of (9.8).  For constant coefficients the exact
full-union and proper-support statements are

$$
\boxed{
\begin{aligned}
H_B^2(\operatorname{Sh}_{C}^{\mathrm{all}},\mathbf C)_{\mathrm{nch}}[\Omega]
&\simeq
\bigoplus_{\rho\in\mathscr P(C,\Omega)}
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
e_{\lambda(\rho),\infty}\mathcal A_\infty^2,\\
H_B^2(\operatorname{Sh}_{C,\mathscr U},\mathbf C)_{\mathrm{nch}}
&\simeq
\bigoplus_{\mathcal O\in\mathfrak O_C^{\mathrm{coh}}}
e_{\mathscr U}
\left(\bigoplus_{\rho\in\mathcal O}
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
e_{\lambda(\rho),\infty}\mathcal A_\infty^2\right).
\end{aligned}}                                                \tag{11.13}
$$

For $d>2$, an individual real constituent has rank one and one of the Hodge vectors
$(1,0,0)$, $(0,1,0)$, or $(0,0,1)$.  For $d=2$, the simultaneous negative component ties two
lines: the two possibilities have rank two and Hodge vectors $(1,0,1)$ and $(0,2,0)$.
The vector $(1,2,1)$ is only that of the four-line unprojected ascension.  The dimension of a
proper orbit block is (8.18), not the rank of a support operator on one $\rho$. The character
spectrum contributes two invariant area lines on the full union and is grouped into the same
$\Xi_C$-orbits on a proper union.

Every full-union individual projector actually constructed from ground-field admissible spans,
and every commuting proper-support orbit projector
$e_{\mathscr U,\mathcal O}=e_{\mathscr U}e_{\mathcal O}$ of (10.5), acts compatibly on Betti,
de Rham, and etale cohomology. The etale image is Galois stable. The analytic
$e_{\lambda,\infty}$ alone is not claimed to be an algebraic span. Individual simple blocks can
require a splitting field, and rational projectors can have integral denominators. Good
specialization and coefficient-independent Frobenius polynomials require the additional
geometric hypotheses listed in Section 10.5.

### 11.2 Proof

Part (a) follows by choosing one $K$-embedding above each $F$-embedding, which gives (2.2), and
then calculating kernels of determinant, multiplier, reduced norm, and scalar multiplication.
The matrix identity (1.2) identifies the derived groups. Direct kernel computations give the
two finite central isogenies, the disconnected part of $Z_H$, the split quotient $G/H$, and the
two auxiliary sequences.

For part (b), a lift through the finite derived-center cover is a scalar $z$ satisfying
$z^2=\det_Kg$ and $N(z)=\nu(g)$. Hilbert 90 reduces these simultaneous equations to the one
square class (11.5). The long exact sequence, nonabelian Hilbert 90 for $D^\times$, and the
torus sequence (3.8) give the exact intersection (3.9). The same proof over each completion
gives the adelic tuple. For the auxiliary cover, the kernel is an induced multiplicative torus,
so its field-valued $H^1$ vanishes. Vanishing of the Picard group of the good semilocal integral
ring supplies restricted adelic lifts.

Part (c) is the fixed-central construction of Chapter 4. Compactness of the adjoint quotient
gives a discrete spectrum. Including $A_G(\mathbf R)^0$ in $K_\infty^\dagger$ removes the
central tangent, while (4.10) gives its split-center coefficient cancellation and compact-center
equivariance gives the remaining condition. The kernel
$r\mapsto(r,r^{-1})$ acts on $\Pi\boxtimes\chi$ by
$\omega_\Pi(r)\chi(r)^{-1}$, proving (11.7). Quotienting the pullback level by that same kernel
proves (11.8).

For part (d), induction and Fourier expansion are performed on the actual compact quotient
$\mathcal C_D$. This proves automorphic ascension and exhaustion without inserting nonexistent
torus points. Factor-set Clifford theory and Morita evaluation give (6.6). The sole imported
quaternionic transfer is the arbitrary-signature theorem summarized in Section 6.5.

For part (e), pullback through the point-surjective auxiliary cover is an equivalence after
imposing kernel triviality. Ascension across $\mathcal C_L$ factors as $\Pi\boxtimes\chi$.
The local norm-annihilator is (7.4); normalized intertwiners in one-place cyclic factors commute
across tensor factors, proving (7.8). Global class field theory gives (11.9). Multiplication
on the multiplicity-one product realization supplies the automorphic character
$\varepsilon_{\Pi,\chi}$, and Fourier orthogonality gives (11.10). Ascension uniqueness supplies
the upper bound.

Part (f) follows by commuting the finite packet idempotent with the compact quotient average.
Kernel compatibility proves lift-independence of Hecke action. The normalized quotient measure
identifies convolution with geometric pull--push. Strong approximation for the simply connected
derived group gives (11.12).  Fourier inversion on the exact quotient (8.12) gives (8.15):
multiplication by a component character twists $\rho$, so only the orbit sum (8.16) is stable.
Induction from its stabilizer proves the dimension formula (8.18).

Finally, compact Hodge theory proves Matsushima directly, before any infinite spectral sum is
interchanged with cohomology. The two active weight-two relative complexes each contribute one
degree-one line of each orientation.  The norm-kernel Clifford projector (9.8) selects one line
when $d>2$; when $d=2$, the simultaneous negative component ties the two lines of fixed parity.
Applying support only after component-character orbit summation proves (11.13).
Semisimplicity of the finite transpose-stable geometric Hecke image constructs its rational
blocks. Functorial comparison for the exact finite-flat lci spans transports the commuting
projectors (10.5) to de Rham and etale cohomology, proving part (g). $\square$

## 12. Failure tests and worked patterns

### 12.1 A missed rational point

Suppose $g\in G(\mathbf Q)$ has determinant $\delta$ and multiplier $q$. Choose
$x/c(x)=\delta/q$. If

$$
q/N_{K/F}(x)\notin F^{\times2},                               \tag{12.1}
$$

then $g$ does not lift through $G^{\mathrm{der}}\times Z_G$, even though the cover is
surjective as an algebraic fppf morphism. If the class belongs to the intersection (3.9), it is
an actual boundary class of a rational $G$-point. Replacing the finite cover by
$\widetilde G\to G$ does give a rational lift, because the latter obstruction lies in
$H^1(F,\mathbf G_m)=0$. The example separates a genuine failure of a chosen cover from a
failure of the target group to have points.

### 12.2 A noncompact pullback level

Take any compact open $C\subset G(\mathbf A_f)$. For every
$r\in\mathbf A_{F,f}^\times$,

$$
(r,r^{-1})\in\theta^{-1}(C)
\quad\text{whenever }1\in C.                                  \tag{12.2}
$$

Since $\mathbf A_{F,f}^\times$ is noncompact, so is $\theta^{-1}(C)$. Its characteristic
function has noncompact support and no finite Haar volume. Dividing by the kernel gives the
compact group (4.22), and kernel compatibility makes the quotient action well defined.
This elementary test catches both the level error and the associated measure error.

### 12.3 Local packets with one global parity equation

Assume a fixed type sees local norm-kernel self-twists at three places and no others. Then

$$
Y_{\mathcal T}\simeq(\mathbf Z/2\mathbf Z)^3                  \tag{12.3}
$$

can label eight typewise constituents. The tensor cocycle is trivial because the three
normalized intertwiners commute. If the global quadratic character $\eta_{K/F}$ is not a
character of the actual quotient or does not stabilize $\Pi$, then $Y_{\rm aut}=1$ and every
allowed typewise label occurs once. If it survives, $Y_{\rm aut}$ has order two and (7.11)
retains the four labels whose three local signs have the prescribed product. It does not turn
those four representations into four copies of one representation.

### 12.4 Packet size, oldvectors, and automorphic multiplicity

Let an occurring $\rho$ have a two-dimensional invariant space at one old level place, with all
other finite invariant spaces lines. If $d>2$, the projector $e_{\lambda,\infty}$ retains one
of the four product-ascension lines, so the individual full-union block has dimension

$$
1\cdot2=2.                                                     \tag{12.4}
$$

If $d=2$, the simultaneous negative component ties two lines and the corresponding dimension is
$2\cdot2=4$. The number $4\cdot2=8$ is the sum over the unprojected archimedean ascension;
it is not the block of one descended representation. The factors in (12.4) mean:

- one automorphic occurrence, by (7.13);
- two oldvectors, in $\rho_f^C$;
- one relative cohomology line, after (9.8), for $d>2$.

Calling any of $2$, $4$, or $8$ an automorphic multiplicity destroys the information needed
under level change and complex conjugation. On a proper component union, one must first add all
component-character twists and then use (8.18); there is no rank of $e_{\mathscr U}$ on this
one $\rho$ block.

### 12.5 A component projector that mixes spectral summands

Suppose $\Delta_C^{\mathrm{or}}\simeq\mathbf Z/2\mathbf Z$, let $\kappa$ be its nontrivial
character, and let $\mathscr U$ be the component represented by the identity. Fourier
inversion gives the support projector

$$
e_{\mathscr U}
=\frac12(1+M_\kappa).                                         \tag{12.5}
$$

If $\rho\not\simeq\rho\otimes\kappa$, then $M_\kappa$ is off diagonal on
$\mathcal W_C^2(\rho)\oplus\mathcal W_C^2(\rho\otimes\kappa)$. Its $+1$ eigenspace has
dimension $\dim\mathcal W_C^2(\rho)$, while neither individual summand is preserved. If
$\rho\simeq\rho\otimes\kappa$, the answer is instead the stabilizer eigenspace prescribed by
(8.18).

For $d=2$, $M_\kappa$ may alter the extension across the component with simultaneous negative
common multiplier. It never permits one to split the $++/--$ or $+-/-+$ pair selected by
$e_{\lambda,\infty}$. For $d>2$, the common multiplier is positive and the routing is finite
adelic. This example is the exact reason (9.12) applies $e_{\mathscr U}$ to an orbit sum and
not to $\rho_f^C\otimes H^2(\rho_\infty)$ for one $\rho$.

## 13. Dependency and interface audits

### 13.1 Exact direct dependency row

The exact direct dependency row is

$$
\boxed{
\text{196}\mid
4,\ 6,\ 29,\ 90,\ 95,\ 99,\ 123,\ 129,\ 132,\ 197,\ 198.}     \tag{13.1}
$$

Every entry is an earlier foundation or an explicitly designated spine input. There is no
dependency on a downstream unitary-surface decomposition.

The uses are:

- Book 4: restricted products, idele class compactness, and local/product Haar normalizations;
- Book 6: Hilbert 90, local and global norm kernels, reciprocity;
- Book 29: continuous low-degree cohomology and factor sets;
- Book 90: normalized double-coset convolution and raw good Hecke operators;
- Book 95: algebraic Hecke characters, coefficient fields, and their one-dimensional Galois
  avatars;
- Book 99: the full real weight-two discrete series, its restriction to
  $\operatorname{GL}_2(\mathbf R)^+$, sign self-twist, and relative cohomology;
- Book 123: fppf torsors and nonabelian boundary sequences, restriction of scalars,
  common-norm reductive groups, centers, and dimensions;
- Book 129: the exact rational-multiplier PEL group, compact surface, actual component quotient,
  component reciprocity, canonical fields, and Hecke spans;
- Book 132: the fixed-central compact-Hodge method and the convention for
  $K_\infty^\dagger$, reproved here in surface degree before support routing;
- Book 197: arbitrary-signature quaternionic Jacquet--Langlands for the actual $Q_a$;
- Book 198: realization functoriality for already constructed admissible Hecke spans and
  open-and-closed component identities.

### 13.2 Imported-result audit

| imported interface | exact use here | assertion deliberately not imported |
|---|---|---|
| rational PEL group and surface | (1.4), projectivity, (8.11), ground-field Hecke spans | no automorphic decomposition or multiplicity theorem |
| quaternionic Jacquet--Langlands | (6.7), local image, conductor, polynomial, Hecke field, multiplicity one on $D^\times$ | no restriction to $H$, no central ascension to $G$ |
| compact curve Matsushima method | harmonic-kernel argument and positive-center convention | no surface degree or four-line result |
| archimedean discrete series | the restriction (9.5), sign self-twist, and one-factor calculation (9.6) | no descended real constituent and no global packet occurrence |
| surface realization comparison | transport of the commuting projector (10.5) and Galois equivariance | no spectral or support projector, no automatic rank-two Frobenius factor |

The common-norm ascension, the auxiliary product ascension, all factor-set calculations, the
global sign formula, full-group multiplicity one, the surface Matsushima formula, and the exact
component-routed degree-two decomposition are proved in this book.

### 13.3 Moving-interface audit

The quaternionic spine input is sufficient exactly when it contains all of the following:

1. global Jacquet--Langlands for a quaternion division algebra with arbitrary real splitting
   signature and exact division-place image;
2. multiplicity one, central-character, twist, conductor, local-factor, and good raw polynomial
   compatibility;
3. the constant-coefficient type (4.17) for the particular algebra $Q_a$;
4. the common-norm group (2.12) only as the endpoint of its own interface, with restriction and
   central ascension left to the present book.

The live input supplies these as its global theorem, its specialized $Q_a$ theorem, and its
common-norm interface. This manuscript does not use any stronger claim from it. If a future
revision removes any item above, the exact remaining handoff is item 1, 2, or 3 as listed; the
group, obstruction, Clifford, level, cohomology, and realization arguments here remain
independent.

The current source proves the representation-theoretic local and global correspondence,
including its reverse transfer and independently defined local-factor comparison. Its one
declared unresolved prerequisite concerns the parameter-enhanced primitive-wild
Weil--Deligne statement. This manuscript uses neither that parameter statement nor any
consequence conditional on it, so there is no outstanding handoff for the interface above.

The exact downstream block handed to Book 133 is the following.  On
$\operatorname{Sh}_C^{\mathrm{all}}$, an occurring complete label contributes

$$
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
e_{\lambda(\rho),\infty}\mathcal A_\infty^2,
$$

once, with rank and Hodge vector given by (9.10).  On a proper union, the smallest
support-stable block is

$$
e_{\mathscr U}
\left(\bigoplus_{\rho'\in\mathcal O_C(\rho)}
\mathcal M_G(\rho')\otimes(\rho'_f)^C\otimes
e_{\lambda(\rho'),\infty}\mathcal A_\infty^2\right),
$$

with dimension (8.18), Hecke routing as after (8.18), and realization projector
$e_{\mathscr U,\mathcal O}$ in (10.5).  Book 133 may group further coefficient or Galois
conjugates, but it may neither replace this orbit block by $e_{\mathscr U}$ of one $\rho$ nor
replace $e_{\lambda,\infty}\mathcal A_\infty^2$ by all four product-ascension lines.

## 14. Final audit and readiness

### 14.1 Hypothesis and failure ledger

| conclusion | exact hypothesis | failure if omitted |
|---|---|---|
| correct full group | rational common multiplier in (1.4) | the larger $F$-multiplier group has different center and dimension |
| compact surface spectrum | anisotropic $W$ and center removed only in the norm | continuous spectrum or an ill-typed central quotient enters |
| finite-cover image | boundary (3.3) and norm intersection (3.9) | pointwise surjectivity is falsely inferred from an isogeny |
| all target components reached | induced-torus cover (2.30) and integral restricted lifts | the finite-cover obstruction is silently ignored |
| compatible central descent | both equations (4.14) and (4.16) | the kernel or target center acts by the wrong character |
| nonzero relative cohomology | $K_\infty^\dagger$ in (4.8) and the full stabilizer-center condition after (4.10) | a spurious central degree appears, the split-center complex is contractible, or compact-center cochains vanish |
| correct common-norm multiplicity | projective module (6.6) | a nontrivial factor set is treated as an ordinary character group |
| full-group multiplicity one | local norm kernel (7.4), tensor linearization (7.8), rational sign (7.11) | packet size is confused with occurrence multiplicity |
| exact finite level | compact quotient (4.22) and normalized average | the alleged level support is noncompact |
| correct Hecke polynomial | an isolating lift (8.3) and character factor (8.8) | a derived double coset or a non-scalar auxiliary completion is mislabeled as a raw full-group operator |
| correct components | full torus image (8.11) | multiplier-only classes merge components or ambient torus points are added |
| selected-union dimension | component-character orbit, stabilizer, and (8.18) | a support idempotent is falsely applied to one full-$G$ summand |
| archimedean constituent | $e_{\lambda,\infty}$ and the $d>2$/$d=2$ distinction (9.7)--(9.10) | all four product-ascension lines are assigned to one representation |
| degree-two decomposition | compact Hodge proof, real Clifford projection, then component-orbit support | automorphic, level, archimedean, and support ranks are conflated |
| Galois-stable block | ground-field admissible spans and $e_{\mathscr U,\mathcal O}$ | Galois or component characters can permute the proposed summand |
| individual simple projector | a splitting field for the rational Hecke factor | a Schur-index obstruction is ignored |
| integral direct summand | idempotent integral at the coefficient prime | rational denominators need not preserve the lattice |
| Frobenius polynomial from geometry | good extension, degree isolation, and fixed-locus hypotheses | a total Lefschetz trace is mistaken for the projected middle trace |

### 14.2 Symbol, measure, level, circularity, and repair-diff audit

- $G$ always denotes the Book 129 rational-multiplier group; $J=\operatorname{Res}D^\times$,
  $H$ the common-norm subgroup, $L=J\times\operatorname{Res}_K\mathbf G_m$, and
  $\widetilde G=\ker(L\to S)$.
- $E_{\mathscr U}$ is a field of definition; no algebraic group is denoted by the same symbol.
- $K_\infty^\dagger$ is defined in (4.8), contains the positive split center, and uses connected
  rotations.
- Fixed central equivariance and the projective quotient used for the norm are never identified.
- Every compact-open projector carries its volume factor; every torus Fourier quotient uses
  probability measure; every exact-sequence quotient uses Weil's formula.
- $\theta^{-1}(C)$ is explicitly noncompact. Only its quotient by $R_F(\mathbf A_f)$ is averaged.
- Raw quaternionic good operators are transferred only through actual lifted spans.
- Components use $t_G(G(\mathbf A_f))$, not all of $T_G(\mathbf A_f)$ and not the multiplier
  alone.
- Proper support uses the exact finite quotient $\Delta_C^{\mathrm{or}}$ and the
  $\Xi_C$-orbit sum. Multiplication by $\mathbf1_{\mathscr U}$ is never asserted to preserve
  one $\rho$.
- The common-norm factor set is retained; the full-group factor set is linearized by the local
  norm equation rather than discarded.
- The real factor is first projected by $e_{\lambda,\infty}$: its rank is one for $d>2$ and
  two for $d=2$, with (9.10) recording the exact Hodge vectors.
- The degree-two formula is proved directly from compact Hodge theory and real relative
  cohomology. No downstream surface-decomposition conclusion is cited or assumed.
- The realization theorem is used only after an individual full-union projector or the
  commuting proper-support orbit projector (10.5) is constructed.
- The repair diff leaves the exact definitions and proofs of $G_W$, $H$, the auxiliary cover,
  all $H^1$ point-image obstructions, dimensions, centers, kernels, $K_\infty^\dagger$, fixed
  central equivariance, the common-norm Clifford module, its cocycle, automorphic multiplicity,
  and the lifted Hecke normalization unchanged.  The only pre-Chapter-8 addition separates the
  finite packet label from the new archimedean label.
- The substantive repair replaces precisely two invalid assertions: individual-$\rho$
  proper-support projection is replaced by (8.12)--(8.18), and four unprojected real lines per
  $\rho$ are replaced by (9.7)--(9.10).  Every theorem, example, realization statement, and
  Book 133 handoff now points to those replacements.

### 14.3 Counts

| item | count |
|---|---:|
| chapters | 14 |
| numbered sections | 72 |
| lines | 3,111 |
| words | 16,379 |
| numbered displayed equations | 180 |
| named theorems and propositions | 5 |
| direct dependencies | 11 |
| unresolved mathematical gaps | 0 |

The contents list links every chapter and numbered section. The manuscript contains no
unresolved placeholder; the numerical values in this table are those of the final audit.

### 14.4 Verdict

**READY.** The group, point-image, fixed-center, measure, level, automorphic ascension,
Clifford packet, multiplicity, Hecke, component, cohomological, coefficient-field, and
realization interfaces required of this spine volume are complete. Any later use must retain the
hypotheses displayed in Theorem 11.1, especially the actual torus image, the global packet sign,
the finite and archimedean Clifford projectors, the compact quotient level, the
component-character orbit required by proper support, and the ground-field span condition.
