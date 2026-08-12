# Automorphic Decomposition of Unitary-Surface $H^2$

## Contents

- [1. The exact realization problem](#1-the-exact-realization-problem)
  - [1.1 The catalog promise](#11-the-catalog-promise)
  - [1.2 The standard surface datum](#12-the-standard-surface-datum)
  - [1.3 Actions and normalizations](#13-actions-and-normalizations)
  - [1.4 The proof architecture](#14-the-proof-architecture)
- [2. The full group and central automorphic descent](#2-the-full-group-and-central-automorphic-descent)
  - [2.1 The PEL group is not the common-norm group](#21-the-pel-group-is-not-the-common-norm-group)
  - [2.2 The obstruction-free auxiliary cover](#22-the-obstruction-free-auxiliary-cover)
  - [2.3 Measures, fixed center, and the real stabilizer](#23-measures-fixed-center-and-the-real-stabilizer)
  - [2.4 Compatible pairs, occurrence, and level](#24-compatible-pairs-occurrence-and-level)
- [3. Right-convolution Hecke correspondences](#3-right-convolution-hecke-correspondences)
  - [3.1 The two legs and their variance](#31-the-two-legs-and-their-variance)
  - [3.2 Composition, transpose, and adjoint](#32-composition-transpose-and-adjoint)
  - [3.3 Lifted operators and good Hecke labels](#33-lifted-operators-and-good-hecke-labels)
  - [3.4 Components and routed operators](#34-components-and-routed-operators)
- [4. Fixed-central Matsushima and the real projector](#4-fixed-central-matsushima-and-the-real-projector)
  - [4.1 Automorphic cochains on the full union](#41-automorphic-cochains-on-the-full-union)
  - [4.2 The compact Matsushima formula](#42-the-compact-matsushima-formula)
  - [4.3 The archimedean Clifford calculation](#43-the-archimedean-clifford-calculation)
  - [4.4 Character cohomology](#44-character-cohomology)
- [5. Exact complex blocks and ranks](#5-exact-complex-blocks-and-ranks)
  - [5.1 Full-union decomposition](#51-full-union-decomposition)
  - [5.2 Individual ranks and Hodge numbers](#52-individual-ranks-and-hodge-numbers)
  - [5.3 Proper-support orbit blocks](#53-proper-support-orbit-blocks)
  - [5.4 Exhaustion and multiplicity audit](#54-exhaustion-and-multiplicity-audit)
- [6. Rational Hecke blocks and degree isolation](#6-rational-hecke-blocks-and-degree-isolation)
  - [6.1 The finite geometric image on total cohomology](#61-the-finite-geometric-image-on-total-cohomology)
  - [6.2 The middle-degree projector](#62-the-middle-degree-projector)
  - [6.3 Coefficient fields and Schur indices](#63-coefficient-fields-and-schur-indices)
  - [6.4 Absolute labels and rational orbit blocks](#64-absolute-labels-and-rational-orbit-blocks)
- [7. Betti, de Rham, and etale realizations](#7-betti-de-rham-and-etale-realizations)
  - [7.1 Admissible surface spans](#71-admissible-surface-spans)
  - [7.2 Compatible realization spaces](#72-compatible-realization-spaces)
  - [7.3 Galois action and duality](#73-galois-action-and-duality)
  - [7.4 Integral, fine-level, and coarse-level boundaries](#74-integral-fine-level-and-coarse-level-boundaries)
- [8. Good reduction, Lefschetz traces, and purity](#8-good-reduction-lefschetz-traces-and-purity)
  - [8.1 The verified good-model range](#81-the-verified-good-model-range)
  - [8.2 Projected low-dimensional Lefschetz formula](#82-projected-low-dimensional-lefschetz-formula)
  - [8.3 Purity and coefficient-prime independence](#83-purity-and-coefficient-prime-independence)
  - [8.4 The rank-two Hecke polynomial boundary](#84-the-rank-two-hecke-polynomial-boundary)
- [9. Semistable boundary and monodromy](#9-semistable-boundary-and-monodromy)
  - [9.1 The two verified parahoric geometries](#91-the-two-verified-parahoric-geometries)
  - [9.2 Projected nearby cycles](#92-projected-nearby-cycles)
  - [9.3 Exact rank and conductor formulas](#93-exact-rank-and-conductor-formulas)
  - [9.4 The boundary of the semistable assertion](#94-the-boundary-of-the-semistable-assertion)
- [10. Comparison with Shimura-curve $H^1$](#10-comparison-with-shimura-curve-h1)
  - [10.1 The common split Jacquet--Langlands label](#101-the-common-split-jacquet--langlands-label)
  - [10.2 Rational and Hecke comparison](#102-rational-and-hecke-comparison)
  - [10.3 Realization and Galois comparison](#103-realization-and-galois-comparison)
  - [10.4 Why there is no Tate-twist isomorphism](#104-why-there-is-no-tate-twist-isomorphism)
- [11. The unitary-surface realization theorem](#11-the-unitary-surface-realization-theorem)
  - [11.1 Complete statement](#111-complete-statement)
  - [11.2 Proof](#112-proof)
  - [11.3 Hypothesis and failure ledger](#113-hypothesis-and-failure-ledger)
- [12. Dependency and readiness audit](#12-dependency-and-readiness-audit)
  - [12.1 Exact direct dependency row](#121-exact-direct-dependency-row)
  - [12.2 Imported-interface audit](#122-imported-interface-audit)
  - [12.3 Symbol, action, and mechanics audit](#123-symbol-action-and-mechanics-audit)
  - [12.4 Readiness verdict](#124-readiness-verdict)

## 1. The exact realization problem

### 1.1 The catalog promise

The auxiliary compact unitary surface is the geometric carrier for a quaternionic packet whose
archimedean cohomology uses two active real places. This book establishes its
constant-coefficient degree-two realization. It does four things at once:

1. it identifies the representations of the actual rational-multiplier PEL group, including
   their central descent and exact multiplicities;
2. it realizes right finite-adelic convolution by algebraic surface correspondences and
   isolates the resulting finite geometric blocks on total cohomology;
3. it transports those blocks to rational Betti, filtered de Rham, and continuous etale
   realizations, with exact ranks and Hodge numbers; and
4. it uses the surface Lefschetz formula, purity, good specialization, and the verified
   semistable models only under the hypotheses which make those operations available.

The comparison with Shimura curves is deliberately typed. A curve block and a surface block
can have the same split Jacquet--Langlands label and the same good quaternionic Hecke field.
They nevertheless have different weights, pairing twists, archimedean factors, component
groups, and often different dimensions. No equality of good labels is turned into a Galois
isomorphism.

### 1.2 The standard surface datum

Let $F$ be totally real of degree $d$, let $K/F$ be CM with conjugation $c$, and choose
$a,b\in F^\times$. Put

$$
W=b\langle 1,-a\rangle,
\qquad
D=Q_a=(K/F,a)=K\oplus Kj.                                    \tag{1.1}
$$

The exact surface hypotheses are these:

- $W$ has signature $(1,1)$ at exactly two real places $v_1,v_2$ and a fixed definite
  orientation at every other real place;
- $W$ is anisotropic over $F$, equivalently $D$ is a division algebra, although $D$ is split
  at $v_1$ and $v_2$;
- the standard PEL datum, determinant law, polarization type, integral orientation data, and
  center-detecting level are those of the constructed unitary surface.

For a $\mathbf Q$-algebra $R$, the full rational-multiplier group is

$$
G(R)=G_W(R)=
\left\{
g\in\operatorname{GL}_{K\otimes R}(W\otimes R):
\langle gx,gy\rangle=\nu(g)\langle x,y\rangle,
\ \nu(g)\in R^\times
\right\}.                                                     \tag{1.2}
$$

The multiplier in (1.2) is one rational scalar. It is not an arbitrary element of
$(F\otimes_{\mathbf Q}R)^\times$. Let $C\subset G(\mathbf A_f)$ be center-detecting and neat.
Write

$$
\operatorname{Sh}^{\mathrm{all}}_C/ E
$$

for the smooth projective canonical union containing the complete component-and-orientation
orbit, and write $\operatorname{Sh}_{C,\mathscr U}/E_{\mathscr U}$ for a ground-field-defined
open-and-closed union selected by a subset $\mathscr U$ of the actual finite component quotient.
The latter field contains the reciprocity field needed to define that union. The geometry is a
surface; it is not the cohomology of the universal PEL abelian scheme.

### 1.3 Actions and normalizations

The rational group acts on the left of the double quotient and the finite adelic group acts by
right translation. Haar measures are coherent with quotient measures. At an unramified
hyperspecial place the hyperspecial subgroup has volume one, and for any compact open $C$ the
normalized identity is

$$
e_C=\operatorname{vol}(C)^{-1}\mathbf 1_C.                   \tag{1.3}
$$

Compact class quotients used in central descent carry probability measure. These choices make
geometric trace maps agree with unnormalized right-double-coset convolution. At each active
real adjoint factor the rotation group has volume one; each definite adjoint factor has
probability measure; and central measures are the Weil quotient measures compatible with the
cover (2.8).

For a finite field $\mathbf F_q$, $F_q$ denotes cohomological geometric Frobenius. The Tate
twist convention is

$$
F_q\mid L_\lambda(1)=q^{-1}.                                 \tag{1.4}
$$

Thus a pure weight-two eigenvalue has complex absolute value $q$, and the middle pairing of a
smooth proper surface has target $L_\lambda(-2)$. Betti, de Rham, and etale cohomology always
refer to the base surface or its stated component union.

### 1.4 The proof architecture

There are three layers, and none substitutes for another:

$$
\begin{array}{c}
\text{central automorphic descent and fixed-central Matsushima}\\[1mm]
\Downarrow\quad\text{exact complex full-group blocks}\\[1mm]
\text{finite algebraic span algebra on total surface cohomology}\\[1mm]
\Downarrow\quad\text{rational projectors and degree isolation}\\[1mm]
\text{Betti--de Rham--etale realizations and arithmetic specialization}.
\end{array}                                                    \tag{1.5}
$$

The first layer supplies labels, occurrence, multiplicity, component routing, and the real
cohomology projector. The second supplies an actual algebraic idempotent, possibly only after
grouping component or coefficient conjugates. The third transports that idempotent and applies
trace and purity. In particular, the analytic real projector is never declared algebraic merely
because it has an explicit formula.

## 2. The full group and central automorphic descent

### 2.1 The PEL group is not the common-norm group

Taking the $K$-determinant in (1.2) gives

$$
N_{K/F}(\det_Kg)=\nu(g)^2.
$$

The structural groups are

$$
\begin{aligned}
G^{\mathrm{der}}&=\operatorname{Res}_{F/\mathbf Q}D^1,
&\dim G^{\mathrm{der}}&=3d,\\
Z_G&=\{z\in\operatorname{Res}_{K/\mathbf Q}\mathbf G_m:
N_{K/F}z\in\mathbf G_m\},
&\dim Z_G&=d+1,\\
T_G&=\{(\delta,q):N_{K/F}\delta=q^2\},
&\dim T_G&=d+1,\\
&&\dim G&=4d+1.
\end{aligned}                                                  \tag{2.1}
$$

Both $Z_G$ and $T_G$ are connected tori. The maximal split central torus is
$A_G\simeq\mathbf G_m$.

The abelianization map is

$$
t_G(g)=(\det_Kg,\nu(g)):G\longrightarrow T_G.                \tag{2.2}
$$

Multiplication gives a finite central isogeny

$$
1\longrightarrow\operatorname{Res}_{F/\mathbf Q}\mu_2
\longrightarrow G^{\mathrm{der}}\times Z_G
\longrightarrow G\longrightarrow1.                          \tag{2.3}
$$

It is fppf-surjective but need not be surjective on rational, local, or adelic points. If
$g\in G(\mathbf Q)$ and $x\in K^\times$ satisfies
$x/c(x)=\det_K(g)/\nu(g)$, its obstruction is the well-defined square class

$$
\operatorname{ob}_G(g)
=\left[\frac{\nu(g)}{N_{K/F}(x)}\right]
\in F^\times/F^{\times2}.                                    \tag{2.4}
$$

This is why a central-isogeny slogan cannot perform the required automorphic descent.

Let $J=\operatorname{Res}_{F/\mathbf Q}D^\times$. The common-norm quaternionic group is

$$
H=J\times_{\operatorname{Res}_{F/\mathbf Q}\mathbf G_m}\mathbf G_m
=\{b\in J:\operatorname{Nrd}(b)\in\mathbf G_m\}.            \tag{2.5}
$$

It has dimension $3d+1$ and the same derived group as $G$, but it is not $G$. Its center is

$$
Z_H=\{r\in\operatorname{Res}_{F/\mathbf Q}\mathbf G_m:r^2\in\mathbf G_m\};
$$

its identity component is the diagonal $\mathbf G_m$ and its geometric component group is
$(\mu_2^d)/\mu_2$. Moreover

$$
1\longrightarrow H\longrightarrow G
\longrightarrow
\operatorname{Res}_{F/\mathbf Q}\operatorname{Res}^{1}_{K/F}\mathbf G_m
\longrightarrow1                                             \tag{2.6}
$$

is split and generally semidirect: the quotient map is
$\alpha(g)=\det_K(g)/\nu(g)$ and the diagonal Hermitian model supplies
$u\mapsto\operatorname{diag}(u,1)$. The auxiliary CM torus in (2.6) is part of the full PEL
group and cannot be discarded when central characters or components are counted.

### 2.2 The obstruction-free auxiliary cover

Put

$$
S=(\operatorname{Res}_{F/\mathbf Q}\mathbf G_m)/\mathbf G_m,
\qquad
L=J\times\operatorname{Res}_{K/\mathbf Q}\mathbf G_m,
$$

and define

$$
\beta:L\longrightarrow S,
\qquad
\beta(b,z)=\left[\operatorname{Nrd}(b)N_{K/F}(z)\right].
$$

Then

$$
\widetilde G
=\ker\beta
=\left\{(b,z)\in L:
\operatorname{Nrd}(b)N_{K/F}(z)\in\mathbf G_m\right\}.       \tag{2.7}
$$

Multiplication in $M_2(K)$ gives

$$
1\longrightarrow R_F
\longrightarrow\widetilde G\xrightarrow{\theta}G
\longrightarrow1,
\qquad
R_F=\operatorname{Res}_{F/\mathbf Q}\mathbf G_m,             \tag{2.8}
$$

where $r\in R_F$ maps to $(r,r^{-1})$. The induced-torus kernel has vanishing first cohomology
on every field point set used here, so $\theta$ is onto on rational, local, finite adelic, and
full adelic points. Integral lifts exist at almost every finite place. This, rather than (2.3),
is the cover used for automorphic descent.

$$
\dim L=6d,
\qquad
\dim\widetilde G=5d+1,
\qquad
\dim R_F=d,
$$

so (2.8) also recovers $\dim G=4d+1$.

The pulled-back level itself is not compact. The correct finite-level object is

$$
\overline C_{\widetilde G}
=\theta^{-1}(C)/R_F(\mathbf A_f)\simeq C,                    \tag{2.9}
$$

with probability average. Write $e_{\overline C}$ for its averaging idempotent. Neither a
level projector nor a Hecke integral is taken over the noncompact space
$\theta^{-1}(C)$.

### 2.3 Measures, fixed center, and the real stabilizer

Fix a unitary character

$$
\Omega:Z_G(\mathbf Q)\backslash Z_G(\mathbf A)\longrightarrow S^1. \tag{2.10}
$$

The Hilbert space $L^2(G,\Omega)$ consists of functions satisfying

$$
f(zg)=\Omega(z)f(g),
\qquad
\int_{Z_G(\mathbf A)G(\mathbf Q)\backslash G(\mathbf A)}
|f(g)|^2\,dg<\infty.                                         \tag{2.11}
$$

The quotient in the norm is compact because the adjoint datum is anisotropic. Its discrete
decomposition is

$$
L^2(G,\Omega)=\widehat\bigoplus_\rho
\mathcal M_G(\rho)\widehat\otimes\rho.                       \tag{2.12}
$$

At finite level one must have
$\Omega_f|_{C\cap Z_G(\mathbf A_f)}=1$. A central sector on components is formed only after
including the whole finite routing orbit on which its idempotent acts.

Choose a point $h$ with the two active orientations. Let $K_{h,c}^0$ be the connected compact
stabilizer after removal of the split center, and set

$$
\boxed{K_\infty^\dagger=A_G(\mathbf R)^0K_{h,c}^0.}          \tag{2.13}
$$

Up to finite central overlap, (2.13) contains

$$
\mathbf R_{>0},\qquad (S^1)^d,\qquad
\operatorname{SO}(2)_{v_1}\times\operatorname{SO}(2)_{v_2},
\qquad\prod_{v\ne v_1,v_2}\operatorname{SU}(2)_v.           \tag{2.14}
$$

The positive split factor in (2.14) removes the central tangent direction. For an algebraic
coefficient representation $V_\xi$, nonzero relative cohomology requires

$$
\Omega_\infty(a)\xi(a)=1
\quad(a\in A_G(\mathbf R)^0),                                \tag{2.15}
$$

and also trivial action of $\Omega_\infty\xi$ on the compact central torus in
$Z_G(\mathbf R)\cap K_\infty^\dagger$. With constant coefficients, $\Omega_\infty$ must be
trivial on both pieces. Omitting the positive split center creates a spurious adjacent degree;
using disconnected orthogonal normalizers identifies orientation lines which the Shimura datum
keeps distinct.

### 2.4 Compatible pairs, occurrence, and level

Let $\Pi$ be a noncharacter automorphic representation of $D^\times(\mathbf A_F)$ with central
character $\omega_\Pi$, and let

$$
\chi:K^\times\backslash\mathbf A_K^\times\longrightarrow\mathbf C^\times
$$

be a Hecke character. The product $\Pi\boxtimes\chi$ descends through (2.8) exactly when

$$
\boxed{
\chi|_{C_F}=\omega_\Pi,
\qquad
\chi|_{Z_G(\mathbf A)}=\Omega,}
\qquad C_F=F^\times\backslash\mathbf A_F^\times.             \tag{2.16}
$$

For constant surface cohomology its infinity type must additionally satisfy

$$
\Pi_{v_1}=\Pi_{v_2}=D_2,
\qquad
\Pi_v=\mathbf1_{\mathbf H^\times}
\quad(v\mid\infty,\ v\ne v_1,v_2),                         \tag{2.17}
$$

with $\chi_\infty$ enforcing the entire stabilizer-center condition following (2.15).
Compatible pairs are identified only by characters of the actual compact quotient of
$L/\widetilde G$, namely

$$
\mathcal C_L=S_L(\mathbf Q)\backslash S_L(\mathbf A),
$$

Here $S_L(\mathbf Q)$ and $S_L(\mathbf A)$ are the actual point images of $\beta$. The torus
$S$ is $\mathbf Q$-anisotropic, so this class quotient is compact. No arbitrary character of
an ambient torus is substituted for a character of $\mathcal C_L$.

At a fixed type, let $Y_{\mathcal T}(\Pi,\chi)$ be the elementary $2$-group of invisible pair
self-twists, and let $Y_{\mathrm{aut}}(\Pi,\chi)$ be its automorphic subgroup. The latter obeys

$$
Y_{\mathrm{aut}}(\Pi,\chi)\subseteq\{1,\eta_{K/F}\}.        \tag{2.18}
$$

Normalized tensor intertwiners $I_y$ linearize the factor set. If $\rho$ is a typewise
constituent with packet character $\langle\,\cdot\,,\rho\rangle$, its exact occurrence is

$$
\boxed{
m_G(\rho;[\Pi,\chi])
=\frac1{|Y_{\mathrm{aut}}|}
\sum_{\eta\in Y_{\mathrm{aut}}}
\varepsilon_{\Pi,\chi}(\eta)
\overline{\langle\eta,\rho\rangle}
\in\{0,1\}.}                                                 \tag{2.19}
$$

Every label satisfying the global sign equation occurs once; a formally possible local label
which fails it does not occur. If $Y_{\mathcal T,f}$ is the finite-place factor and
$\lambda_f$ is the finite packet character, then

$$
e_{\lambda,f}
=\frac1{|Y_{\mathcal T,f}|}
\sum_{y\in Y_{\mathcal T,f}}
\overline{\lambda_f(y)}I_y,
\qquad
\rho_f^C\simeq
e_{\lambda,f}e_{\overline C}(\Pi_f\boxtimes\chi_f).         \tag{2.20}
$$

Thus automorphic multiplicity, packet size, fixed-vector dimension, and the number of surface
components remain four different integers.

## 3. Right-convolution Hecke correspondences

### 3.1 The two legs and their variance

For $a\in G(\mathbf A_f)$ put

$$
C_a=C\cap aCa^{-1}.
$$

Let $p_1$ be the forgetful map and let $p_2$ be right translation by $a$ followed by forgetting
level. To make the source leg visible, draw the endospan in the order

$$
\operatorname{Sh}_C
\xleftarrow{\ p_2\ }
\operatorname{Sh}_{C_a}
\xrightarrow{\ p_1\ }
\operatorname{Sh}_C.                                        \tag{3.1}
$$

The Book 198 convention for a span $X\xleftarrow{u}Z\xrightarrow{v}Y$ is $v_*u^*$.
Consequently the right-double-coset operator is

$$
\boxed{T(a)=(p_1)_*p_2^*.}                                  \tag{3.2}
$$

The order in (3.1) is intentional. If $a$ normalizes $C$, then $p_1$ is the identity and
$p_2=r_a$, so (3.2) is $r_a^*$, the right action $f(g)\mapsto f(ga)$. If
$CaC=\coprod_i a_iC$ and $\operatorname{vol}(C)=1$, its action on automorphic functions is

$$
T(a)f(g)=\sum_i f(ga_i).                                     \tag{3.3}
$$

Swapping the pullback and trace in (3.2) would implement the opposite variance and is not
done. The finite degree of the trace is already present in (3.2); no averaging by the number
of right cosets is inserted.

At neat generic level both legs are finite etale. On an integral model they are used only when
they extend as finite flat lci maps with the orientation required for the surface trace.

### 3.2 Composition, transpose, and adjoint

With the right-convolution convention,

$$
T(a)T(b)=T(\mathbf1_{CaC}*\mathbf1_{CbC})
=\sum_c m(a,b;c)T(c),                                       \tag{3.4}
$$

where the structure constants use the coherent Haar measure. Every operator composition in
(3.4) exists on cohomology. A single fiber-product carrier represents it geometrically only
when that carrier is smooth and the middle square is Tor-independent. In the one allowed
nontransverse replacement, every component must be regular, the excess bundle must be locally
free of rank at most two, and the proved Euler class must be inserted. An ordered
noncommutative polynomial is retained when the operators do not commute.

Transposing (3.1) swaps its legs. For constant coefficients,

$$
T(a)^t=T(a^{-1}),
\qquad
\langle T(a)x,y\rangle=\langle x,T(a^{-1})y\rangle.          \tag{3.5}
$$

The coefficient-system adjoint includes the recorded adjoint of the universal isogeny. The
coefficient involution must also be specified. If $\iota$ is an involution of the coefficient
field, then

$$
(\alpha T(a_1)\cdots T(a_r))^{\dagger,\iota}
=\iota(\alpha)\,T(a_r^{-1})\cdots T(a_1^{-1}).              \tag{3.6}
$$

The identity coefficient involution is the default for Poincare duality. Complex conjugation
is used for the positive analytic Hermitian adjoint, and any nontrivial involution used after
completion is required to preserve that completion. In every case the anti-involution reverses
products.

The identity span acts as the identity. Pullback, trace, transpose, and (3.4) preserve
cohomological degree and Hodge type.

### 3.3 Lifted operators and good Hecke labels

Choose a lift $\widetilde a=(b,z)\in\widetilde G(\mathbf A_f)$ of $a$. On a compatible pair,

$$
\rho(a)=\Pi(b)\chi(z).                                       \tag{3.7}
$$

Replacing $(b,z)$ by $(br,zr^{-1})$ multiplies (3.7) by
$\omega_\Pi(r)\chi(r)^{-1}=1$, so the action is independent of the lift. The lifted double
coset is integrated over its compact quotient by $R_F(\mathbf A_f)$, never over the full
inverse image.

$$
T_{CaC}|_\rho
=e_{\lambda,f}
\left(
\int_{\overline C\widetilde a\overline C}
\Pi(b_x)\chi(z_x)\,d\overline x
\right)e_{\lambda,f}.
$$

Weil quotient measure makes this operator agree with (3.2).

Book 197 supplies global Jacquet--Langlands for the actual arbitrary-signature algebra $D$.
For every good place $v$ of $F$, write

$$
P_v(\Pi,X)=1-t_v(\Pi)X+q_vs_v(\Pi)X^2.                      \tag{3.8}
$$

It is the same raw polynomial for the split transfer. To name a raw operator on the PEL tower,
one must choose an isolating lifted spherical datum: its $D_v^\times$ coordinate is the
standard spherical double coset, all other quaternionic coordinates act as the identity on the
selected spherical lines, and its $K$-idele coordinate completes an actual point of
$\widetilde G$. If $\gamma_{\widetilde v}=\chi(z)$, the resulting label is

$$
\boxed{
P_{\widetilde v}(\rho,X)
=1-\gamma_{\widetilde v}t_v(\Pi)X
+\gamma_{\widetilde v}^{2}q_vs_v(\Pi)X^2.}                 \tag{3.9}
$$

The derived spherical algebra by itself knows only the projective Satake ratio. It cannot name
an arbitrary single-$F$-place raw $\operatorname{GL}_2$ operator inside the common rational
multiplier group. Formula (3.9) is asserted only for the isolating lift just described.

### 3.4 Components and routed operators

Strong approximation for the simply connected derived group gives the exact finite component
set

$$
\Gamma_C
=T_G(\mathbf Q)^\dagger\backslash
t_G(G(\mathbf A_f))/t_G(C),                                  \tag{3.10}
$$

where every term is its actual image and
$T_G(\mathbf Q)^\dagger=t_G(G(\mathbf Q)_+)$. The multiplier alone is insufficient, and the
middle term is not enlarged to all of $T_G(\mathbf A_f)$.

For simultaneous component and real-orientation routing use the finite abelian quotient

$$
\Delta_C^{\mathrm{or}}
=t_G(G(\mathbf Q))\backslash t_G(G(\mathbf A))
/t_G(K_\infty^\dagger C),
\qquad
\Xi_C=\operatorname{Hom}(\Delta_C^{\mathrm{or}},\mathbf C^\times). \tag{3.11}
$$

A Hecke span with route $r$ maps the $\mathscr U$-supported cohomology to the
$\mathscr U r$-supported cohomology. It is an endomorphism only if $\mathscr U r=\mathscr U$;
otherwise the endomorphism retained on that union is the corner

$$
e_{\mathscr U}T(a)e_{\mathscr U}.                            \tag{3.12}
$$

The same statement applies over the field of definition: component reciprocity must stabilize
$\mathscr U$ before $e_{\mathscr U}$ or its corner is Galois equivariant.

## 4. Fixed-central Matsushima and the real projector

### 4.1 Automorphic cochains on the full union

For an algebraic coefficient representation $V_\xi$, put

$$
\mathfrak p_\mathbf C
=\mathfrak g_\mathbf C/\mathfrak k_\mathbf C^\dagger.
$$

Because $K_\infty^\dagger$ contains $A_G(\mathbf R)^0$, this tangent representation contains
the two disk tangents and no positive central line. On the full union and in the fixed sector
$\Omega$, the automorphic cochain complex is

$$
C^q_{\mathrm{aut}}(C,\Omega,\xi)
=\operatorname{Hom}_{K_\infty^\dagger}
\left(
\bigwedge^q\mathfrak p_\mathbf C,
\mathcal A(G,\Omega)^C\otimes V_\xi
\right).                                                       \tag{4.1}
$$

The differential is the relative Lie algebra differential. The whole stabilizer-center
condition in Section 2.3 is required before (4.1) models differential forms. For a proper
union, one first sums the finite central sectors in its $\Xi_C$-orbit and only then applies
$e_{\mathscr U}$.

### 4.2 The compact Matsushima formula

Compact Hodge theory gives a finite-dimensional harmonic kernel in every degree. Intersecting
the discrete spectrum (2.12) with that kernel before taking cohomology avoids any interchange
with an uncontrolled Hilbert direct sum. The result is

$$
\boxed{
H_B^q(\operatorname{Sh}^{\mathrm{all}}_C,
\mathcal V_\xi\otimes\mathbf C)[\Omega]
\simeq
\bigoplus_{\substack{\rho\\\omega_\rho=\Omega}}
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
H^q(\mathfrak g,K_\infty^\dagger;
\rho_\infty\otimes V_\xi).}                                \tag{4.2}
$$

The formula is Hecke equivariant for (3.2). The transpose relation in (3.5) agrees with the
automorphic adjoint because both use the coherent quotient measures. Formula (4.2) is a
full-union statement; applying it termwise to one proper component would incorrectly assert
that support preserves every full-$G$ representation.

### 4.3 The archimedean Clifford calculation

For constant coefficients, the weight-two representation at each active place restricts as

$$
D_2|_{\operatorname{GL}_2(\mathbf R)^+}=D_2^+\oplus D_2^-.
$$

Each summand has one relative degree-one line,

$$
H^q(\mathfrak{gl}_2,
\mathbf R_{>0}\operatorname{SO}(2);D_2^\epsilon)
=
\begin{cases}
\mathbf C\eta^\epsilon,&q=1,\\
0,&q\ne1,
\end{cases}                                                   \tag{4.3}
$$

where $\eta^+$ has Hodge type $(1,0)$ and $\eta^-$ has type $(0,1)$. Before descent the product
ascension has four lines

$$
\mathcal A_\infty^2
=\bigoplus_{\epsilon_1,\epsilon_2\in\{+,-\}}
\mathbf C\eta_1^{\epsilon_1}\otimes\eta_2^{\epsilon_2}.     \tag{4.4}
$$

Put $s_i=\operatorname{sgn}\circ\det$ on
$D_{v_i}^\times\simeq\operatorname{GL}_2(\mathbf R)$. Let $I_i$ be the normalized
self-intertwiner $D_2\simeq D_2\otimes s_i$, with $I_i^2=1$ and eigenvalue $\epsilon$ on
$D_2^\epsilon$. The effective real self-twist group and the actual constituent projector are

$$
Y_\infty^{\mathrm{eff}}=
\begin{cases}
\langle s_1,s_2\rangle\simeq(\mathbf Z/2\mathbf Z)^2,&d>2,\\
\langle s_1s_2\rangle\simeq\mathbf Z/2\mathbf Z,&d=2,
\end{cases}                                                   \tag{4.5}
$$

and

$$
e_{\lambda,\infty}=
\begin{cases}
\dfrac14(1+\lambda_1I_1)(1+\lambda_2I_2),
&d>2,\\[2mm]
\dfrac12(1+\lambda I_1I_2),
&d=2.
\end{cases}                                                   \tag{4.6}
$$

For an occurring descended constituent,

$$
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty)
=
\begin{cases}
e_{\lambda,\infty}\mathcal A_\infty^2,&q=2,\\
0,&q\ne2.
\end{cases}                                                   \tag{4.7}
$$

The exact ranks and Hodge vectors are

$$
\begin{array}{c|c|c|c}
\text{case}&\lambda_\infty&
\dim e_{\lambda,\infty}\mathcal A_\infty^2&
(h^{2,0},h^{1,1},h^{0,2})\\ \hline
d>2 &(+,+)&1&(1,0,0)\\
d>2 &(+,-)\text{ or }(-,+)&1&(0,1,0)\\
d>2 &(-,-)&1&(0,0,1)\\
d=2 &+&2&(1,0,1)\\
d=2 &-&2&(0,2,0).
\end{array}                                                    \tag{4.8}
$$

When $d=2$, negative common multiplier exchanges both active signs simultaneously, so the
$++/--$ pair and the $+-/-+$ pair cannot be split by a $G(\mathbf R)$-equivariant projector.
The vector $(1,2,1)$ belongs to the unprojected space (4.4), not to an individual full-$G$
representation. The operator (4.6) is an analytic Clifford projector; a finite geometric
projector transports the constituent it identifies but is not obtained by simply adjoining
(4.6) to the correspondence algebra.

### 4.4 Character cohomology

An automorphic character is trivial on the derived real group. Subject to the same central
cancellation, its relative cohomology is

$$
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty)
\simeq
\begin{cases}
\mathbf C,&q=0,4,\\
\mathbf C\omega_1\oplus\mathbf C\omega_2,&q=2,\\
0,&q=1,3,
\end{cases}                                                   \tag{4.9}
$$

where the two area lines have Hodge type $(1,1)$. These are discrete character terms, not
boundary or Eisenstein cohomology. Automorphic characters have multiplicity one, so on the
full union their exact contribution is

$$
H_B^q(\operatorname{Sh}^{\mathrm{all}}_C,\mathbf C)_{\mathrm{char}}[\Omega]
\simeq
\bigoplus_{\substack{\rho\ \mathrm{character}\\\omega_\rho=\Omega}}
\rho_f^C\otimes
H^q(\mathfrak g,K_\infty^\dagger;\rho_\infty).               \tag{4.10}
$$

On a proper union these characters too must be grouped into $\Xi_C$-orbits before support is
imposed; the Fourier and stabilizer formulas (5.5)--(5.7) apply to those character orbit sums.

## 5. Exact complex blocks and ranks

### 5.1 Full-union decomposition

Let $\mathscr P(C,\Omega)$ be the set of compatible-pair orbits and complete local packet
labels which satisfy all of the following:

- the descent and central equations (2.16);
- the stabilizer-center cancellation of Section 2.3;
- the real condition (2.17);
- the global occurrence equation (2.19); and
- nonvanishing of the fixed-level space (2.20).

Then the noncharacter middle cohomology of the complete union is

$$
\boxed{
H_B^2(\operatorname{Sh}^{\mathrm{all}}_C,\mathbf C)_{\mathrm{nch}}[\Omega]
\simeq
\bigoplus_{\rho\in\mathscr P(C,\Omega)}
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
e_{\lambda(\rho),\infty}\mathcal A_\infty^2.}              \tag{5.1}
$$

For every displayed summand, $\dim\mathcal M_G(\rho)=1$. Formula (5.1), together with the
character contribution (4.9)--(4.10), exhausts constant-coefficient $H^2$. There is no boundary term
because the surface is projective.

### 5.2 Individual ranks and Hodge numbers

Put $n_C(\rho)=\dim_\mathbf C\rho_f^C$. The rank of an individual full-union block is

$$
r_C(\rho)=
\begin{cases}
n_C(\rho),&d>2,\\
2n_C(\rho),&d=2.
\end{cases}                                                   \tag{5.2}
$$

Its Hodge vector is $n_C(\rho)$ times the appropriate row of (4.8). In particular, oldvectors
scale every Hodge number but do not change automorphic multiplicity. Suppose a splitting field
$L$ and an individual geometric idempotent $e_\rho$ exist. Let $A_L$ be the split finite Hecke
image on that factor and choose a simple left $A_L$-module $P_\rho$ modeling $\rho_f^C$. The
cohomological multiplicity space and evaluation isomorphism are

$$
\begin{aligned}
W_{\rho,B}
&=\operatorname{Hom}_{A_L}
(P_\rho,e_\rho H_B^2(\operatorname{Sh}^{\mathrm{all}}_C,L)),\\
P_\rho\otimes_LW_{\rho,B}
&\xrightarrow{\ \sim\ }
e_\rho H_B^2(\operatorname{Sh}^{\mathrm{all}}_C,L).
\end{aligned}                                                  \tag{5.3}
$$

The space $W_{\rho,B}$ has dimension one for $d>2$ and two for $d=2$, with the Hodge vector in
(4.8). Formula (5.3) is not formed when finite geometry does not separate the archimedean label;
in that case the exact block is the sum of all labels carried by the same simple geometric
factor.

### 5.3 Proper-support orbit blocks

For $\kappa\in\Xi_C$, the operator $M_\kappa f(g)=\kappa(g)f(g)$ carries the full summand for
$\rho$ to that for $\rho\otimes\kappa$. Define

$$
\begin{aligned}
\mathcal W_C^2(\rho)&=
\mathcal M_G(\rho)\otimes\rho_f^C\otimes
e_{\lambda(\rho),\infty}\mathcal A_\infty^2,\\
\mathcal O_C(\rho)&=\{\rho\otimes\kappa:\kappa\in\Xi_C\}/\simeq,\\
S_C(\rho)&=\{\kappa\in\Xi_C:\rho\otimes\kappa\simeq\rho\},\\
\mathcal W_C^2(\mathcal O)&=
\bigoplus_{\rho'\in\mathcal O}\mathcal W_C^2(\rho').
\end{aligned}                                                  \tag{5.4}
$$

On the product ascension the finite and real labels route together:

$$
M_\kappa e_{\lambda(\rho),\infty}
=e_{\lambda(\rho\otimes\kappa),\infty}M_\kappa.
$$

For $\mathscr U\subset\Delta_C^{\mathrm{or}}$, Fourier inversion gives the support idempotent

$$
e_{\mathscr U}
=\sum_{\kappa\in\Xi_C}
\left(
\frac1{|\Delta_C^{\mathrm{or}}|}
\sum_{\delta\in\mathscr U}\overline{\kappa(\delta)}
\right)M_\kappa.                                             \tag{5.5}
$$

It preserves the orbit sum in (5.4), not generally one $\rho$-summand. The exact supported
block and decomposition are as follows. Here $\mathfrak O_C^{\mathrm{coh}}$ is the finite set
of $\Xi_C$-orbits of occurring noncharacter cohomological representations across every central
sector mixed by support:

$$
\boxed{
\begin{aligned}
\mathcal W_{C,\mathscr U}^2(\mathcal O)
&=e_{\mathscr U}\mathcal W_C^2(\mathcal O),\\
H_B^2(\operatorname{Sh}_{C,\mathscr U},\mathbf C)_{\mathrm{nch}}
&\simeq
\bigoplus_{\mathcal O\in\mathfrak O_C^{\mathrm{coh}}}
\mathcal W_{C,\mathscr U}^2(\mathcal O).
\end{aligned}}                                                \tag{5.6}
$$

The actual multiplication operators of $S_C(\rho)$ act on
$\mathcal W_C^2(\rho)$. Let $a_{\rho,\theta}^{p,q}$ be the multiplicity of
$\theta\in\widehat{S_C(\rho)}$ in its $(p,q)$-part, and put
$a_{\rho,\theta}^2=\sum_{p+q=2}a_{\rho,\theta}^{p,q}$. If
$\operatorname{ev}_\delta(s)=s(\delta)$, induction from the stabilizer gives the exact formulas

$$
\boxed{
\begin{aligned}
\dim\mathcal W_{C,\mathscr U}^2(\mathcal O)
&=\sum_{\delta\in\mathscr U}
a_{\rho,\operatorname{ev}_\delta|_{S_C(\rho)}}^2,\\
h^{p,2-p}(\mathcal O,\mathscr U)
&=\sum_{\delta\in\mathscr U}
a_{\rho,\operatorname{ev}_\delta|_{S_C(\rho)}}^{p,2-p}.
\end{aligned}}                                                \tag{5.7}
$$

These are intrinsic ranks. A proper union need not retain a fixed fraction of a full orbit,
and $e_{\mathscr U}$ is never applied to one summand in order to guess that fraction. For
$d>2$, a definite real factor forces the common multiplier to be positive. For $d=2$, a
component character can change the extension across the simultaneous negative component; the
covariance preceding (5.5) routes that real label together with the finite and central labels.

### 5.4 Exhaustion and multiplicity audit

The factors in (5.1)--(5.7) have distinct roles:

| datum | what it counts |
|---|---|
| $m_G(\rho)$ | zero-or-one global automorphic occurrence |
| $\dim\rho_f^C$ | fixed vectors and oldvectors at finite level |
| $e_{\lambda,\infty}\mathcal A_\infty^2$ | the one- or two-line real cohomology of one descended constituent |
| $\mathcal O_C(\rho)$ | representations mixed by component-character translation |
| $e_{\mathscr U}$ | support on the selected open-and-closed union |
| coefficient conjugacy | descent from absolute labels to a rational block |

The arbitrary-signature correspondence of Book 197 proves that (2.17) is the actual
two-active quaternionic type. It is not obtained from a theorem restricted to a totally
definite algebra. Book 196 proves the descent from that quaternionic type to the full $G$ and
the exact formulas above; no multiplicity is inferred merely from a common derived group.

## 6. Rational Hecke blocks and degree isolation

### 6.1 The finite geometric image on total cohomology

Set

$$
H_{B,\mathrm{tot}}
=\bigoplus_{i=0}^4
H_B^i(\operatorname{Sh}^{\mathrm{all}}_C,\mathbf Q).          \tag{6.1}
$$

Let $\mathbb T_C^{\mathrm{tot}}$ be the image on (6.1) of the rational algebra generated by
finitely many admissible Hecke spans, their transposes, required finite central translations,
and ground-field component identities. Enlarge this finite family, when necessary, by a finite
set separating the cohomological modules used in Section 6.2. This image is finite dimensional
and stable under adjoint. In each degree, combine the Poincare polarization with the Weil
operator to obtain a positive Hodge Hermitian form. Because every generator has Hodge type
$(0,0)$, it commutes with the Weil operator, so transpose is also its Hilbert adjoint for this
positive form after conjugating scalar coefficients. If the Jacobson radical contained
$x\ne0$, then $xx^*$ would be both
positive semidefinite and nilpotent, which is impossible. Hence

$$
\mathbb T_C^{\mathrm{tot}}
\text{ is a finite-dimensional semisimple }\mathbf Q\text{-algebra}. \tag{6.2}
$$

Every generator is of Hodge type $(0,0)$. Hence every rational central idempotent cuts a
rational Hodge substructure in each degree; as a rational sub-Hodge structure of a polarizable
smooth-projective cohomology group, its image is polarizable.

The proper-union image is the semisimple corner

$$
\mathbb T_{C,\mathscr U}^{\mathrm{tot}}
=e_{\mathscr U}\mathbb T_C^{\mathrm{tot}}e_{\mathscr U}.    \tag{6.3}
$$

The abstract convolution algebra may have a kernel on cohomology; semisimplicity is asserted
for the finite image in (6.2), not for an infinite formal algebra.

### 6.2 The middle-degree projector

At fixed level only finitely many cohomological finite modules occur. The full $C$-Hecke
algebra separates distinct representations generated by their $C$-fixed vectors. Book 197
strong determination separates a noncharacter quaternionic packet from automorphic characters,
while the central and component operators retain the full lifted data. If two real extension
labels have the same finite geometric module, they remain grouped; this is precisely the
geometric equivalence relation rather than a defect in the construction.

Let $\mathscr B$ be a coefficient- and component-stable geometric block which contains the
chosen compatible-pair label and all labels inseparable from it by
$\mathbb T_C^{\mathrm{tot}}$. It consists entirely of noncharacter cohomological labels. The
identity of its simple rational factor, or the sum of the required simple-factor identities,
is a rational central idempotent $e_{\mathscr B}$. After a splitting field is chosen it has an
ordered polynomial expression

$$
e_{\mathscr B}=P_{\mathscr B}(T_1,\ldots,T_s),
\qquad
P_{\mathscr B}\in L\langle X_1,\ldots,X_s\rangle.            \tag{6.4}
$$

On a proper union the corresponding exact idempotent is

$$
e_{\mathscr U,\mathcal O}
=e_{\mathscr U}e_{\mathcal O}
=e_{\mathcal O}e_{\mathscr U},                               \tag{6.5}
$$

where $e_{\mathcal O}$ is the full component-character orbit idempotent. The commutation in
(6.5) follows because $e_{\mathcal O}$ is invariant under every $M_\kappa$. In general
$e_\rho e_{\mathscr U}$ is not an idempotent.

The crucial point is that (6.4) acts on total cohomology. Fixed-central Matsushima and the real
calculation say that every noncharacter label in $\mathscr B$ contributes only in degree two.
The character labels in degrees zero and four are separated from $\mathscr B$. Therefore

$$
\boxed{
e_{\mathscr B}H_B^i=0\quad(i\ne2),
\qquad
e_{\mathscr B}H_{B,\mathrm{tot}}
=e_{\mathscr B}H_B^2.}                                      \tag{6.6}
$$

This is total-cohomology degree isolation. Constructing a projector only on $H^2$ and then
assuming (6.6) would be circular; here (6.6) is proved from the full Matsushima calculation.
No algebraic Kunneth projector is required.

### 6.3 Coefficient fields and Schur indices

Assume $\Pi$ is in the parallel-weight-two arithmetic normalization and $\chi$ is algebraic.
For such a compatible pair define

$$
E_\Pi=\mathbf Q(t_v(\Pi),s_v(\Pi):v\notin\Sigma),
$$

let $E_\chi$ contain the algebraic values and finite roots of unity of $\chi$, and let
$E_{\Omega,\Gamma}$ contain the central, component, and support values. Then

$$
E_0(\Pi,\chi)=E_\Pi E_\chi E_{\Omega,\Gamma}.                \tag{6.7}
$$

Every actual lifted good eigenvalue in (3.9) lies in (6.7). The signs in the finite and real
Clifford projectors introduce no further transcendental values. The field $E_0$ controls the
good commutative eigensystem, but it need not define the full bad-level module.

Let $A$ be a simple rational factor of (6.2). Wedderburn theory writes

$$
A\simeq M_n(D_A),
\qquad Z(D_A)=E_A,                                            \tag{6.8}
$$

where $D_A$ may be a nontrivial central division algebra. After choosing the embedding
corresponding to an absolute label, $E_A$ is a finite extension of the relevant image of
$E_0$; on a proper union one first takes the orbit-invariant subfield. A model of an absolutely
simple module can still require a further field $L$ which splits $D_A$. This is the Schur-index
obstruction. The identity of $A$ is rational and canonical; a primitive matrix idempotent is
defined only after choosing an embedding $E_A\hookrightarrow L$ and a splitting.

### 6.4 Absolute labels and rational orbit blocks

Over a common splitting field $L$, let $\operatorname{Lab}(A,L)$ be the complete multiset of
absolute simple spectral summands in the rational factor, counted with their module
multiplicities and including coefficient conjugates and, for a proper union, the
component-character orbit required by (5.6). Then the exact rational rank is

$$
\dim_\mathbf Q(e_AH_B^2)
=\dim_L(e_AH_B^2\otimes_\mathbf Q L)
=\sum_{\tau\in\operatorname{Lab}(A,L)}r_\tau,                \tag{6.9}
$$

where $r_\tau$ is given by (5.2) on the full union or by (5.7) on proper support. The Hodge
numbers are the same sum of the corresponding rows. Formula (6.9), rather than a guessed
multiple by a Hecke-field degree, remains valid in the presence of Schur index or unequal
component stabilizers. Complex conjugation exchanges $++$ with $--$ and $+-$ with $-+$,
together with the corresponding coefficient embeddings, so every rational orbit sum has Hodge
symmetry even though one complex full-$G$ label in the $d>2$ table need not.

If the finite spans distinguish one full-union label, a matrix idempotent $e_\rho$ over $L$
cuts it out. Otherwise the smallest honest output is the whole simple geometric block. All
these projectors are finite ordered polynomials in actual spans. The analytic
$e_{\lambda,\infty}$ tells which Hodge row occurs inside them; it is not an extra algebraic
factor in (6.4).

## 7. Betti, de Rham, and etale realizations

### 7.1 Admissible surface spans

An admissible span between smooth proper surfaces is a diagram

$$
X\xleftarrow{u}Z\xrightarrow{v}Y                              \tag{7.1}
$$

with $Z$ a smooth proper surface and both legs finite flat lci of constant degree, equipped
with their regular graph orientations. It acts in every realization by

$$
T_{(u,v)}=v_*u^*.                                             \tag{7.2}
$$

Finite disjoint unions, characteristic-zero linear combinations, ordered polynomials, and
transposes are allowed. The operator preserves cohomological degree, is of Hodge type $(0,0)$,
and has no residual Tate twist. The kernel construction and (7.2) agree exactly: the two
codimension-two comparison factors cancel. This is the surface comparison interface; a
curve-only comparison theorem cannot replace it.

At neat generic level, (3.1) is admissible with $(u,v)=(p_2,p_1)$, so (7.2) is exactly
$(p_1)_*p_2^*$. An open-and-closed component identity is an admissible identity span on a finite
disjoint union.

### 7.2 Compatible realization spaces

Assume the surface union, component identities, and every span in (6.4) or (6.5) are defined
over $E_{\mathscr U}$. Let $e$ denote either a full-union block projector or a proper-support
orbit projector. Put $R_L=E_{\mathscr U}\otimes_\mathbf Q L$. The compatible images are

$$
\begin{aligned}
V_{B,e}&=eH_B^2(\operatorname{Sh}^{\mathrm{all}}_C,L),\\
V_{\mathrm{dR},e}&=
e\left(
H_{\mathrm{dR}}^2(\operatorname{Sh}^{\mathrm{all}}_C/E_{\mathscr U})
\otimes_\mathbf Q L
\right),\\
V_{\lambda,e}&=
eH_{\mathrm{et}}^2
(\operatorname{Sh}^{\mathrm{all}}_{C,\overline E_{\mathscr U}},L_\lambda).
\end{aligned}                                                  \tag{7.3}
$$

The middle line is an $R_L$-module; no unchosen embedding
$E_{\mathscr U}\hookrightarrow L$ is implicit. After passage to a field factor of $R_L$, its
rank agrees with the corresponding Betti and etale rank. The Hodge filtration is

$$
F^2=H^{2,0},
\qquad
F^1=H^{2,0}\oplus H^{1,1},
\qquad
F^0=H^2,                                                       \tag{7.4}
$$

with dimensions given by (5.7) or (6.9). Comparison intertwines every span, polynomial,
transpose, and component identity exactly. Since $e$ is idempotent on total Betti cohomology,
faithful scalar extension makes it idempotent in de Rham and etale cohomology. Equation (6.6)
transports as well, so these are genuine degree-two summands.

### 7.3 Galois action and duality

Every defining span is over $E_{\mathscr U}$, hence $V_{\lambda,e}$ is a continuous
$G_{E_{\mathscr U}}$-representation and all ground-field Hecke operators commute with Galois.
Betti cohomology itself is not a Galois representation.

Let $e^\dagger$ be formed by transposing spans, reversing products, and using the identity
coefficient involution, unless a nontrivial involution preserving $L_\lambda$ has explicitly
been fixed. Poincare duality, or the corresponding sesquilinear pairing in the latter case,
restricts to a perfect pairing

$$
V_{\lambda,e}\times V_{\lambda,e^\dagger}
\longrightarrow L_\lambda(-2),
\qquad
V_{\lambda,e}^\vee\simeq V_{\lambda,e^\dagger}(2).           \tag{7.5}
$$

A self-pairing is asserted only when $e=e^\dagger$ with the required coefficient
identification. At a good finite field, eigenvalues in adjoint blocks are paired so their
products are $q^2$. No alternating pairing is inferred merely because a chosen block happens
to have rank two.

When an individual split finite module $P_\rho$ is geometrically separated, the etale
multiplicity space

$$
W_{\rho,\lambda}
=\operatorname{Hom}_{A_{L_\lambda}}
(P_{\rho,\lambda},V_{\lambda,e_\rho})                        \tag{7.6}
$$

inherits Galois action because Galois commutes with the finite Hecke algebra. Its dimension is
the real rank in (4.8). Before splitting, the invariant object is a module for the opposite
division algebra in (6.8), not a prematurely chosen vector space.

### 7.4 Integral, fine-level, and coarse-level boundaries

Let

$$
\Lambda_\lambda
=\left(H^2_{\mathrm{et}}
(\operatorname{Sh}^{\mathrm{all}}_{C,\overline E_{\mathscr U}},
\mathbf Z_\ell)/\mathrm{tors}\right)
\otimes_{\mathbf Z_\ell}\mathcal O_{L_\lambda}.              \tag{7.7}
$$

Let $N_e>0$ clear the coefficients of the chosen polynomial expression for $e$. The
always-defined lattice in the rational block is the saturated intersection

$$
\Lambda_{\lambda,e}
=V_{\lambda,e}\cap\Lambda_\lambda.                           \tag{7.8}
$$

When every defining span is integral at $\lambda$ and $\lambda\nmid N_e$,

$$
\Lambda_\lambda
=e\Lambda_\lambda\oplus(1-e)\Lambda_\lambda.                \tag{7.9}
$$

At a denominator prime, (7.8) remains a Galois- and Hecke-stable lattice but need not be a
direct summand. A rational projector has no automatic action on torsion. Integral torsion is
governed by complementary-degree linking, not by a perfect raw self-pairing on $H^2$.

All preceding geometric comparison statements apply directly to smooth proper fine schemes and
finite disjoint unions. At non-neat level one may pass to a normal fine cover and take
characteristic-zero invariants under the effective deck group. If the action is free, the
scheme quotient is again smooth. With stabilizers, the quotient stack can be smooth proper
while the coarse scheme has quotient singularities; the smooth-surface comparison theorem is
not silently applied to that coarse scheme. Integral invariant descent additionally requires
the deck-group order to be a unit and retains projector denominators.

## 8. Good reduction, Lefschetz traces, and purity

### 8.1 The verified good-model range

At a good odd PEL place, all hypotheses of the PEL-exact standard Book 129 surface must be
present: the center is unramified, the order is maximal and involution-stable, the alternating
lattice is self-dual, the polarization degree is prime to the residue characteristic, the
stabilizer is reductive and hyperspecial, the two determinant-and-orientation packets are
integral, the level is neat away from the place, the chosen component union extends, and the
prime lies below no recorded exceptional place, including the anisotropic localization. Book
130 then gives a unique smooth projective fine model

$$
\mathscr S_C/\mathcal O_{E,u}                                \tag{8.1}
$$

for the fixed PEL presentation. Prime-to-$p$ Hecke spans extend with finite etale, hence finite
flat lci, legs. A routed span is a self-correspondence only when its route preserves the
selected integral union.

Book 130 names the operator attached to its displayed integral legs as
$(p_2)_*p_1^*$. Only its extension and specialization of the two legs are imported here. For
constant coefficients the transposed integral span extends as well, and it is this transpose
which is named by the right-convolution convention of Section 3 as $(p_1)_*p_2^*$.

For $\ell\ne p$, smooth proper specialization is Hecke equivariant. If every span in $e$
extends over (8.1), then

$$
V_{\lambda,e}\xrightarrow{\sim}
eH^2_{\mathrm{et}}(\mathscr S_{C,\overline{\mathbf F}_q},L_\lambda) \tag{8.2}
$$

is Frobenius compatible, and the generic representation is unramified. There is no assertion
here for $\ell=p$.

### 8.2 Projected low-dimensional Lefschetz formula

Let $F$ be geometric Frobenius on the special fiber. Because $e$ is defined over
$\mathbf F_q$, it commutes with $F$. Its cohomological Lefschetz number is always

$$
L(F^m e)
=\sum_{i=0}^4(-1)^i
\operatorname{Tr}(F^m e\mid H^i_{\mathrm{et}}).              \tag{8.3}
$$

Degree isolation (6.6), transported by (8.2), gives

$$
\boxed{
L(F^m e)=\operatorname{Tr}(F^m\mid V_{\lambda,e}).}          \tag{8.4}
$$

To turn (8.4) into an intersection degree, expand the chosen polynomial for $e$ as a finite
$L$-linear combination of admissible endospans with smooth carriers. Every composition used in
that expansion must satisfy the smooth Tor-independent rule of Section 3.2. For each required
$m$, assume the Frobenius-twisted fixed locus of every carrier is either finite and transverse,
or proper and covered by the clean regular-excess calculation with every component, including
vertical ones, present. Then

$$
\operatorname{Tr}(F^m\mid V_{\lambda,e})=I_m(e)\in L,        \tag{8.5}
$$

where $I_m(e)$ is the weighted sum of the resulting local lengths or Euler-class degrees.
Without these hypotheses, (8.3) remains a valid cohomological trace, but it is not renamed an
unproved geometric intersection degree.

### 8.3 Purity and coefficient-prime independence

The ambient smooth proper surface cohomology is pure of weight two. Hence every eigenvalue
$\alpha$ of $F$ on $V_{\lambda,e}$ satisfies

$$
|\iota(\alpha)|=q                                            \tag{8.6}
$$

for every complex embedding. If $r=\dim_{L_\lambda}V_{\lambda,e}$ and the fixed-locus
hypotheses of Section 8.2 hold for $1\le m\le r$ at every coefficient prime being compared,
then the power sums

$$
s_m=I_m(e)=\sum_{j=1}^r\alpha_j^m
$$

determine

$$
Q_{u,e}(X)=\det(1-FX\mid V_{\lambda,e})                      \tag{8.7}
$$

by Newton identities. Thus $Q_{u,e}(X)\in L[X]$ is independent of $\lambda\ne p$. No
semisimplicity of Frobenius is needed. If the fixed-locus hypotheses fail, purity and
unramifiedness remain valid, but this argument does not prove coefficient-prime independence
of (8.7).

### 8.4 The rank-two Hecke polynomial boundary

The polynomial (3.8) is the rank-two split or quaternionic Satake label. The lifted PEL
polynomial (3.9) includes the necessary $\chi$-scalar. In contrast, the degree of (8.7) is the
geometric rank (5.2), (5.7), or (6.9). Therefore

$$
P_{\widetilde v}(\rho,X)
\quad\text{is not automatically}\quad
Q_{u,e}(X).                                                    \tag{8.8}
$$

Even when $Q_{u,e}$ has degree two, equality requires a proved specialization relation or an
additional geometric construction; a common Hecke name is not enough. The surface Lefschetz
argument computes the actual projected Frobenius polynomial through (8.5), not by substituting
Satake symbols into a polynomial of the wrong rank.

## 9. Semistable boundary and monodromy

### 9.1 The two verified parahoric geometries

Book 131 treats the catalogued rank-two Iwahori cases at the completely split odd places
selected in its prerequisite ledger. With one bad direction, the local model is étale locally

$$
xy=\pi                                                        \tag{9.1}
$$

times a smooth direction; the total space is regular and strictly semistable with two
components and no triple points. With two bad directions, the raw product of two nodes is not
strictly semistable. The proved small regularization replaces it by charts of the form

$$
xyz=\pi,                                                      \tag{9.2}
$$

with component surfaces, double curves, and triple points. These statements apply only to the
specified integral PEL tensors, lattice chains, selected component unions, and finite
regularizations of that construction. They are not a theorem for arbitrary ramified
parahoric level.

### 9.2 Projected nearby cycles

Let strict semistability be reached after a finite extension. The surface nearby-cycle complex
has contributions from component surfaces, double curves, and triple points. Its monodromy
operator satisfies

$$
N^3=0\quad\text{on }H^2.                                     \tag{9.3}
$$

Suppose every span in the polynomial $e$ extends as finite flat lci maps of semistable models
and meets every ordered stratum transversely. If not, require a separately supplied proper
cohomological correspondence satisfying the clean regular-excess hypotheses on every relevant
square, with all vertical components included. Under exactly these conditions the spans act on
nearby cycles and commute with inertia, Frobenius, duality, and $N$. Hence

$$
eN=Ne,
\qquad
N^3=0\quad\text{on }V_{\lambda,e},
\qquad
FNF^{-1}=q^{-1}N.                                             \tag{9.4}
$$

Finite descent remains part of the Weil--Deligne representation; it is not discarded after a
strict semistable extension is chosen.

### 9.3 Exact rank and conductor formulas

For the one-direction model, let $Z_1$ be the Hasse double curve, let $s_1$ be the rank of the
restriction map from the endpoint surface cohomology, and let $g_1$ be the rank of the induced
cup-product Gram form on its image. Then

$$
N^2=0,
\qquad
\operatorname{rank}N=b_1(Z_1)-2s_1+g_1.                     \tag{9.5}
$$

For several endpoint components, the symbols in (9.5) mean the full signed restriction and
Gram matrices, not a componentwise sum.

For the two-direction model, let $Z_1,Z_2$ be the two Hasse-curve families, $P$ their
intersection set, and $B$ their bipartite incidence graph. With the restriction and Gram ranks
$s_1,s_2,s_{12},g_{12}$ of the proved stratum complex,

$$
\begin{aligned}
R_2=\operatorname{rank}N^2
&=|P|-|\pi_0(Z_1)|-|\pi_0(Z_2)|+c(B),\\
n_2&=2b_1(Z_1)+2b_1(Z_2)
-2(s_1+s_2+s_{12})+g_{12},\\
R_1=\operatorname{rank}N&=n_2+2R_2.
\end{aligned}                                                  \tag{9.6}
$$

For a projector satisfying Section 9.2, apply it to the explicit restriction--Gysin and
incidence matrices. If $e=e^\dagger$, apply it on both paired sides; otherwise use the paired
$e$- and $e^\dagger$-pieces as in Poincare adjunction. If the resulting projected numerical
invariants are denoted
$b_e,r_e,g_e,h_e$, then the exact projected formula is

$$
n_{2,e}=b_e-2r_e+g_e,
\qquad
\operatorname{rank}N^2|_{V_{\lambda,e}}=h_e,
\qquad
\operatorname{rank}N|_{V_{\lambda,e}}=n_{2,e}+2h_e.         \tag{9.7}
$$

At split strict semistable level the Artin conductor is $\operatorname{rank}N$. After finite
descent it is instead

$$
a(V_{\lambda,e})
=\dim V_{\lambda,e}-\dim(\ker N)^{r(I)}+\operatorname{Sw}(r), \tag{9.8}
$$

and the local Euler factor uses $F$ on $(\ker N)^{r(I)}$. Neither the conductor nor
$\operatorname{rank}N$ alone determines the Weil--Deligne type.

### 9.4 The boundary of the semistable assertion

Prime-to-bad Hecke correspondences in the verified models preserve the Hasse and exceptional
strata, so projectors made from those spans meet the functorial input when their component
routes also extend. No action on the stratum spectral sequence is claimed from the mere fact
that two generic-fiber legs extend as finite maps. Singular stratum intersections, a non-locally
free excess quotient, omitted vertical components, deeper lattice chains, wild local models,
and coarse quotient singularities all lie outside the assertion.

Book 131, like Book 130, writes $(p_2)_*p_1^*$ for the operator attached to its displayed
integral legs. This book imports the extension, stratum preservation, and nearby-cycle
functoriality of those legs and uses their transpose. Thus the operator acting here remains
$(p_1)_*p_2^*$, and no opposite-convolution convention enters the projector.

There is again no $\ell=p$ comparison. The rational projector acts on monodromy even at a
denominator prime, but its integral direct-summand statement remains limited by Section 7.4.

## 10. Comparison with Shimura-curve $H^1$

### 10.1 The common split Jacquet--Langlands label

Let $D_s=D$ be the two-active surface algebra and let $D_c$ be a quaternion division algebra
defining a compact Shimura curve and split at exactly one real place. A surface representation
$\Pi_s$ and a curve representation $\Pi_c$ have a common label only when there is a cuspidal
representation $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ such that

$$
\operatorname{JL}_{D_s}(\Pi_s)=\pi
=\operatorname{JL}_{D_c}(\Pi_c),                             \tag{10.1}
$$

and $\pi_v$ is essentially square-integrable at every place at which the relevant quaternion
algebra is nonsplit. Book 197 proves this arbitrary-signature transfer and its reverse under
exactly that local-image condition. A comparison through a totally definite or one-active
inner form uses the common split intermediary (10.1); it is not obtained from a theorem whose
scope is only the totally definite case.

### 10.2 Rational and Hecke comparison

At every place good for both inner forms, (10.1) gives

$$
t_v(\Pi_s)=t_v(\pi)=t_v(\Pi_c),
\qquad
s_v(\Pi_s)=s_v(\pi)=s_v(\Pi_c).                              \tag{10.2}
$$

Thus the common quaternionic field is

$$
E_\pi=\mathbf Q(t_v(\pi),s_v(\pi):v\notin\Sigma).            \tag{10.3}
$$

Book 132 constructs the curve rational Hecke block and, after a splitting field, factors it as

$$
e_cH_B^1\simeq P_{\Pi_c}\otimes W_{\Pi_c,B},
\qquad
\dim W_{\Pi_c,B}=2,                                          \tag{10.4}
$$

with Hodge types $(1,0)$ and $(0,1)$. The surface rational block is (6.8)--(6.9). Its good
eigensystem starts over $E_\pi$; the full coefficient package adjoins $\chi$, fixed-center
values, component routing, and bad local data, and a field of definition can further require a
Schur splitting field. Likewise the curve block can have its own central or component
extension. Equality (10.2) therefore compares the common derived eigensystem; it does not
identify the two full rational Hecke algebras or their projectors.

For an actual lifted surface operator, (10.2) appears with the scalar
$\gamma_{\widetilde v}$ in (3.9). A full curve and surface eigencharacter agrees only after
their respective central lifts have also been matched.

### 10.3 Realization and Galois comparison

Both constructions have the same formal realization pattern:

$$
\begin{array}{ccccc}
e_cH_B^1&\longleftrightarrow&e_cH_{\mathrm{dR}}^1
&\longleftrightarrow&e_cH_{\mathrm{et}}^1,\\[1mm]
e_sH_B^2&\longleftrightarrow&e_sH_{\mathrm{dR}}^2
&\longleftrightarrow&e_sH_{\mathrm{et}}^2.
\end{array}                                                    \tag{10.5}
$$

Their projectors are algebraic, their etale images are stable under the Galois group of the
appropriate component field, and their integral lattices are saturated rather than
automatically split at denominator primes. These are structural comparisons. The varieties
have different reflex or component fields, and after restriction to a common overfield there
is still no natural map between the two rows of (10.5).

At good places the curve theorem gives its rank-two Frobenius relation under its own integral
hypotheses. The surface theorem gives purity and, under Sections 8.2--8.3, its projected
polynomial (8.7). Equation (10.2) alone does not identify those Frobenius polynomials. At bad
places the curve graph complex and the surface component--double-curve--triple-point complex
are different geometric objects, even when their prime-to-bad Hecke labels agree.

### 10.4 Why there is no Tate-twist isomorphism

The curve multiplicity space in (10.4) is pure of weight one and pairs into
$L_\lambda(-1)$. The surface block is pure of weight two and pairs with its adjoint into
$L_\lambda(-2)$. A Tate twist changes weight by an even integer. There is no integer $n$ with

$$
2-2n=1.                                                       \tag{10.6}
$$

Consequently no Tate twist of the surface block is the curve block. This remains true if a
surface block happens to have dimension two. A cross-variety Galois isomorphism would require
an additional algebraic correspondence or a separately proved representation-theoretic
construction; neither is manufactured here.

## 11. The unitary-surface realization theorem

### 11.1 Complete statement

**Theorem 11.1 (automorphic realization on the auxiliary unitary surface).** Let the datum
$(F,K,W,D,G)$ satisfy Section 1.2, let $C$ be center-detecting and neat, and let
$\operatorname{Sh}^{\mathrm{all}}_C$ be the complete component-and-orientation union. Fix a
unitary central character $\Omega$ satisfying the finite-level and full
$K_\infty^\dagger$-center cancellation. Let
$\operatorname{Sh}_{C,\mathscr U}/E_{\mathscr U}$ be a ground-field-defined open-and-closed
union stable under the routes used below. A fixed-$\Omega$ assertion on this proper union is
made only if $\mathscr U$ is also stable under the central translations defining that sector;
otherwise its formulas range over every central sector in the $\Xi_C$-orbit. Then:

1. Every noncharacter cohomological representation of $G$ arises from a compatible pair
   $(\Pi,\chi)$ satisfying (2.16)--(2.17), modulo the actual compact quotient character group,
   and a complete Clifford label satisfying (2.19). Every occurring individual representation
   has multiplicity one. Its finite level is (2.20).

2. In a fixed central sector, the full-union noncharacter decomposition is (5.1). An individual
   block has rank and Hodge vector (5.2) and (4.8). The full character contribution is
   (4.9)--(4.10).
   On a proper union, the canonical decomposition is the component-character orbit formula
   (5.6), with exact rank and Hodge numbers (5.7).

3. A finite Hecke double coset acts by the right-convolution span
   $(p_1)_*p_2^*$ of (3.1)--(3.3). Lifted actions are (3.7), and an isolating lifted spherical
   datum has polynomial (3.9). Transpose, ordered composition, and component corners are
   (3.4)--(3.6) and (3.12).

4. The adjoint-stable finite geometric image on total cohomology is semisimple. Its rational
   central idempotents isolate the minimal geometric noncharacter blocks and kill every degree
   other than two as in (6.6). An individual absolute label needs a splitting field and actual
   separation by finite spans; a proper union needs $e_{\mathscr U,\mathcal O}$, not
   $e_\rho e_{\mathscr U}$. For arithmetic $\Pi$ and algebraic $\chi$, coefficient fields and
   Schur indices are exactly (6.7)--(6.9).

5. Every projector expressed in ground-field admissible spans defines the compatible spaces
   (7.3), with ranks and Hodge filtration already computed over $\mathbf C$. Its etale image is
   a continuous $G_{E_{\mathscr U}}$-representation and pairs with its adjoint as in (7.5).
   Integral splitting holds under (7.9), while saturation (7.8) is the unconditional lattice
   statement.

6. Under the full good-model and extension hypotheses of Section 8.1 and for $\ell\ne p$, the
   block is unramified and pure of weight two. If degree isolation and all transverse or clean
   regular-excess fixed-locus hypotheses hold for the required Frobenius powers, the
   low-dimensional Lefschetz formula (8.5) and Newton identities give the
   coefficient-prime-independent polynomial (8.7). The raw rank-two label (3.9) is not
   automatically that polynomial.

7. In the verified one- and two-direction semistable models, a projector acts on nearby cycles
   only under Section 9.2. It then retains finite descent, commutes with $N$ and $F$, satisfies
   (9.4), and has the rank and conductor formulas (9.5)--(9.8). No assertion is extended to an
   unverified ramified local model.

8. If a curve packet and a surface packet have the common split transfer (10.1), their
   quaternionic good field and eigenvalues agree as in (10.2)--(10.3). Their rational blocks,
   projectors, and realization functoriality are comparable as in Sections 10.2--10.3, but
   their weights and pairing twists differ. They are not asserted to be Galois-isomorphic.

At non-neat level, rational statements may be descended from a normal fine cover through the
effective finite deck action. Smooth coarse geometry and integral splitting retain all
qualifications of Section 7.4.

### 11.2 Proof

The group calculation in Section 2.1 identifies the actual PEL group, its center and
abelianization, and the smaller common-norm subgroup. The point obstruction (2.4) rules out a
false descent across the finite central isogeny. The induced-torus cover (2.8), the compact
quotient level (2.9), and the two character equations (2.16) instead give the exact descent of
$\Pi\boxtimes\chi$. Clifford linearization and Fourier orthogonality on the actual quotient
give (2.19), hence zero-or-one occurrence and multiplicity one for every occurring $\rho$.

Compactness gives the discrete spectrum. The positive split center and compact center in
$K_\infty^\dagger$ make the relative complex correctly typed. Compact harmonic theory then
proves (4.2). The two one-factor calculations (4.3) and Kunneth give the four product lines;
real Clifford descent applies (4.6) and yields the individual rows (4.8), rather than assigning
all four lines to one representation. This proves (5.1)--(5.2). Fourier inversion on the exact
quotient (3.11) proves the orbit-support formula (5.6) and the stabilizer rank formula (5.7).

The leg declaration in (3.1) and the admissible-span rule $v_*u^*$ prove the right-convolution
formula (3.2). Quotient measures identify it with (3.3). Lift independence follows from
$\omega_\Pi=\chi|_{C_F}$, and arbitrary-signature Jacquet--Langlands gives (3.8)--(3.9).
Surface span theory proves comparison, transpose, and the carefully limited composition rules.

The finite total-cohomology image is adjoint stable, so the radical argument proves (6.2).
Full Hecke-module separation and strong determination isolate the minimal noncharacter
geometric factor from character cohomology. The complete Matsushima calculation places every
label in that factor only in degree two, proving (6.6) without a Kunneth projector. Wedderburn
theory then gives the rational central block, its Schur obstruction, and the exact rank sum
(6.9).

The comparison theorem for smooth proper surfaces evaluates the same ordered polynomial in
Betti, de Rham, and etale cohomology. Faithful scalar extension transports idempotence and
degree vanishing, giving (7.3), while transpose and Poincare duality give (7.5). Its integral
statement gives saturation and splitting exactly as in Section 7.4.

At a verified good place, the integral surface theorem and smooth proper base change give
(8.2), unramifiedness, and Frobenius compatibility. Surface purity gives (8.6). The
low-dimensional Lefschetz calculation identifies projected power traces with geometric degrees
only under Section 8.2, and Newton identities then prove (8.7). At the verified semistable
places, the explicit local models and surface nearby cycles give (9.3); functoriality of the
extending spans gives (9.4), and the restriction--Gysin matrices give (9.5)--(9.8).

Finally, arbitrary-signature Jacquet--Langlands gives the conditional common split label
(10.1), while the already established curve decomposition gives (10.4). The coefficient-field,
weight, pairing, and Galois audits in Chapter 10 prove exactly the comparison claimed in part 8
and no cross-variety isomorphism. $\square$

### 11.3 Hypothesis and failure ledger

| conclusion | exact hypothesis | failure if omitted |
|---|---|---|
| correct automorphic group | rational-multiplier $G_W$ of (1.2) | the common-norm subgroup loses the CM quotient and has the wrong dimension and center |
| central descent | induced-torus cover and both equations (2.16) | a finite-cover obstruction or wrong kernel character is ignored |
| fixed-central Matsushima | $K_\infty^\dagger$ and full center cancellation | a spurious central degree appears or all equivariant cochains vanish |
| occurrence multiplicity | complete Clifford label and global sign (2.19) | local packet size is confused with automorphic multiplicity |
| right Hecke action | translated source leg and $(p_1)_*p_2^*$ | the opposite convolution convention is represented |
| raw PEL good polynomial | isolating lift and $\chi$-scalar | a derived ratio is mislabeled as a full raw operator |
| individual real rank | $e_{\lambda,\infty}$ with the $d>2$/$d=2$ split | four product lines are assigned to one full-$G$ representation |
| proper-union rank | full $\Xi_C$-orbit and stabilizer formula | support is falsely applied to one representation |
| rational absolute projector | simple geometric factor and a Schur splitting field | a good eigenvalue field is mistaken for a field of definition |
| degree isolation | projector constructed on total cohomology and full Matsushima | an $H^2$ interpolation is assumed to kill other degrees |
| compatible realizations | ground-field admissible surface spans | a curve comparison theorem is used outside its dimension |
| Galois-stable summand | field-defined union and spans | Galois permutes the proposed support or operator |
| integral direct summand | integral spans and denominator prime avoided | saturation need not split the lattice |
| good Frobenius trace | smooth proper model, degree isolation, and fixed-locus hypotheses | a total trace is mistaken for a projected middle trace |
| semistable action | transverse strata or complete clean-excess datum | generic finite legs do not act on nearby-cycle strata |
| curve comparison | common split transfer with local-image conditions | similar good names are treated as the same global packet |

## 12. Dependency and readiness audit

### 12.1 Exact direct dependency row

The exact noncircular direct dependency row is

$$
\boxed{
\text{133}\mid 129,\ 130,\ 131,\ 132,\ 196,\ 197,\ 198.}    \tag{12.1}
$$

There are exactly seven direct dependencies.

- Book 129 supplies the PEL-exact standard rational-multiplier unitary datum, its anisotropic
  compact surface, canonical component fields, actual abelianized component formula, and
  generic Hecke spans.
- Book 130 supplies the smooth projective good integral model of this standard surface and the
  extension and specialization of prime-to-residue-characteristic Hecke spans, with its exact
  fine, stack, and coarse qualifications.
- Book 131 supplies only the verified one- and two-direction parahoric surface models at its
  selected completely split odd places, their strata, nearby cycles, monodromy matrices,
  conductor formulas, and prime-to-bad Hecke functoriality.
- Book 132 supplies the already established Shimura-curve $H^1$ rational Hecke block,
  rank-two multiplicity space, and its Betti, de Rham, and etale realizations. Its transfer
  restriction is not used for the surface algebra.
- Book 196 supplies the exact $G_W/H/\widetilde G$ central descent, fixed-center spaces,
  measures and compact quotient level, Clifford packets, occurrence formula, component
  character orbit sums, $e_{\lambda,\infty}$, Matsushima decomposition, multiplicities, and
  Hodge ranks used verbatim in Chapters 2, 4, and 5.
- Book 197 supplies global Jacquet--Langlands for the actual arbitrary-signature quaternion
  algebra, its reverse local-image criterion, good raw polynomial, conductor and field
  compatibility, and the common-split comparison in Chapter 10.
- Book 198 supplies comparison for smooth proper surfaces and admissible finite-flat lci spans,
  ordered composition, transpose, total-degree projectors, duality, integral denominators,
  low-dimensional Lefschetz traces, purity, good specialization, and the exact semistable
  functoriality boundary.

Books 94 and 27 are not direct dependencies. Book 94 is not used to transfer the two-active
algebra; Book 197 supplies that theorem. Book 27 is not used as a surface comparison theorem;
Book 198 uses it internally only on actual curves in its Lefschetz-pencil proof. Books 196,
197, and 198 are explicitly designated spine inputs. Book 196 proves that it does not depend on
Book 133, Book 197 excludes Books 133 and 196 from its inputs, and Book 198 has no dependence on
this decomposition, so (12.1) is noncircular.

### 12.2 Imported-interface audit

| input | exact interface consumed here | stronger claim not imported |
|---|---|---|
| Book 129 | standard surface, $G_W$, components, canonical fields, generic spans | no automorphic decomposition or central multiplicity |
| Book 130 | good fine model and extending prime-to-$p$ spans | no smooth coarse quotient with stabilizers and no $\ell=p$ comparison |
| Book 131 | two catalogued semistable geometries at its selected completely split odd places and their explicit matrices | no arbitrary parahoric or wild local-model theorem |
| Book 132 | curve $H^1$ block and rank-two multiplicity realization | no surface comparison and no automatic cross-variety Galois map |
| Book 196 | exact full-group block handed off after central, real, and component projection | no permission to replace a proper orbit by one $\rho$ or four real lines |
| Book 197 | arbitrary-signature representation-theoretic Jacquet--Langlands | no central ascension to $G$ and no use of its unresolved enhanced wild-parameter statement |
| Book 198 | functorial surface realizations for already constructed admissible spans | no spectral projector, no arbitrary singular cycle, and no automatic Frobenius polynomial |

### 12.3 Symbol, action, and mechanics audit

- $G$ always means the full rational-multiplier PEL group; $J=\operatorname{Res}D^\times$,
  $H$ is the common-norm subgroup, and $\widetilde G$ is the induced-torus cover.
- $K$ denotes the CM field and never the real stabilizer; the latter is
  $K_\infty^\dagger$. The finite level is $C$.
- $\Omega$ is a fixed central character; $\chi$ is the auxiliary CM Hecke character; $\Pi$ is
  quaternionic; $\rho$ is a descended full-$G$ representation.
- The Hecke span is displayed with $p_2$ as source leg and $p_1$ as target leg, and every use is
  $(p_1)_*p_2^*$. Its transpose is inversion and its anti-involution reverses products.
- The coefficient involution in the adjoint is the identity by default; complex conjugation is
  used only for the positive analytic Hermitian adjoint, and a nontrivial completed involution
  must preserve the chosen completion.
- $e_{\lambda,f}$ and $e_{\lambda,\infty}$ are distinct Clifford projectors;
  $e_{\mathscr U}$ is support; $e_{\mathcal O}$ is a component-orbit spectral projector; and
  $e_A$ is a rational central Hecke-factor idempotent.
- Every proper-support formula uses an orbit sum before $e_{\mathscr U}$. Every realization
  projector is a polynomial in admissible finite spans and acts on total cohomology before
  degree two is selected.
- Geometric Frobenius, the twist $L_\lambda(1)$, pairing target $L_\lambda(-2)$, purity radius
  $q$, and the relation $FNF^{-1}=q^{-1}N$ use one convention throughout.
- All displayed references point to existing numbered equations or sections. The contents links
  match the chapter and section headings. Mathematics uses dollar delimiters, and every result
  belongs to the main theorem sequence.

### 12.4 Readiness verdict

The catalog promise is met: the relevant two-active quaternionic packets are identified in the
actual full PEL group, their exact middle-degree complex blocks and Hodge ranks are computed,
right-convolution Hecke spans isolate rational total-cohomology blocks, surface comparison
transports those blocks to de Rham and Galois realizations, and low-dimensional Lefschetz,
purity, good reduction, semistable monodromy, and curve comparison are stated exactly at their
proved boundaries.

The repair audit has seven direct dependencies, zero direct uses of Books 94 or 27, one Hecke
variance convention, one fixed real stabilizer containing the positive split center, and no
unprojected four-line assignment to an individual representation.

The word ``ready'' is relative to the dependency row (12.1). In particular, the good-model and
good-specialization conclusions in part 6 of Theorem 11.1 remain contingent on the current Book
130 theorem, while the semistable models, stratum matrices, and rank formulas in part 7 remain
contingent on the current Book 131 theorem and, through its endpoint models, on Book 130. This
book neither reproves nor strengthens either of those geometric inputs.

$$
\boxed{\text{READY}}                                         \tag{12.2}
$$
