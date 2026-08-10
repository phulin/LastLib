# Automorphic Decomposition of Unitary-Surface $H^2$

## Contents

- [1. The middle-degree realization problem](#1-the-middle-degree-realization-problem)
  - [1.1 Why degree two is unavoidable](#11-why-degree-two-is-unavoidable)
  - [1.2 The geometric and automorphic data](#12-the-geometric-and-automorphic-data)
  - [1.3 Coefficients, Frobenius, and actions](#13-coefficients-frobenius-and-actions)
  - [1.4 The logical boundary](#14-the-logical-boundary)
- [2. The compact surface and its cohomology](#2-the-compact-surface-and-its-cohomology)
  - [2.1 Compactness removes the boundary](#21-compactness-removes-the-boundary)
  - [2.2 The five cohomological degrees](#22-the-five-cohomological-degrees)
  - [2.3 Lefschetz classes and the character part](#23-lefschetz-classes-and-the-character-part)
  - [2.4 Components and finite quotients](#24-components-and-finite-quotients)
- [3. Hecke correspondences in middle degree](#3-hecke-correspondences-in-middle-degree)
  - [3.1 Pull--push and variance](#31-pull-push-and-variance)
  - [3.2 Composition and adjoints](#32-composition-and-adjoints)
  - [3.3 The common spherical algebra](#33-the-common-spherical-algebra)
  - [3.4 Galois and specialization compatibility](#34-galois-and-specialization-compatibility)
- [4. The compact Matsushima decomposition](#4-the-compact-matsushima-decomposition)
  - [4.1 From differential forms to the discrete spectrum](#41-from-differential-forms-to-the-discrete-spectrum)
  - [4.2 Relative Lie algebra cohomology](#42-relative-lie-algebra-cohomology)
  - [4.3 Proof of the decomposition](#43-proof-of-the-decomposition)
  - [4.4 Fixed level and finiteness](#44-fixed-level-and-finiteness)
- [5. The archimedean degree-two calculation](#5-the-archimedean-degree-two-calculation)
  - [5.1 One active rank-one factor](#51-one-active-rank-one-factor)
  - [5.2 Two active factors and Kunneth](#52-two-active-factors-and-kunneth)
  - [5.3 Hodge types and orientation packets](#53-hodge-types-and-orientation-packets)
  - [5.4 Exclusion of other infinity types](#54-exclusion-of-other-infinity-types)
- [6. Quaternionic packets and exact multiplicities](#6-quaternionic-packets-and-exact-multiplicities)
  - [6.1 Finite-adelic matching](#61-finite-adelic-matching)
  - [6.2 Central extensions and auxiliary characters](#62-central-extensions-and-auxiliary-characters)
  - [6.3 Multiplicity one versus cohomological dimension](#63-multiplicity-one-versus-cohomological-dimension)
  - [6.4 The complex decomposition theorem](#64-the-complex-decomposition-theorem)
- [7. Isolating a packet by Hecke operators](#7-isolating-a-packet-by-hecke-operators)
  - [7.1 Simultaneous eigenspaces](#71-simultaneous-eigenspaces)
  - [7.2 Finite separating sets and projectors](#72-finite-separating-sets-and-projectors)
  - [7.3 Character packets and noncharacter packets](#73-character-packets-and-noncharacter-packets)
  - [7.4 Denominators and integral warnings](#74-denominators-and-integral-warnings)
- [8. Rational and Hodge structures](#8-rational-and-hodge-structures)
  - [8.1 The rational Betti decomposition](#81-the-rational-betti-decomposition)
  - [8.2 Hecke fields and conjugation](#82-hecke-fields-and-conjugation)
  - [8.3 Polarizations and duality](#83-polarizations-and-duality)
  - [8.4 De Rham realization](#84-de-rham-realization)
- [9. The etale Galois realization](#9-the-etale-galois-realization)
  - [9.1 Comparison and descent](#91-comparison-and-descent)
  - [9.2 The packet representation](#92-the-packet-representation)
  - [9.3 Dimensions and scalar extension](#93-dimensions-and-scalar-extension)
  - [9.4 What has and has not been extracted](#94-what-has-and-has-not-been-extracted)
- [10. Frobenius traces, purity, and independence](#10-frobenius-traces-purity-and-independence)
  - [10.1 Good reduction](#101-good-reduction)
  - [10.2 Projected Lefschetz traces](#102-projected-lefschetz-traces)
  - [10.3 Purity and reciprocal roots](#103-purity-and-reciprocal-roots)
  - [10.4 Coefficient and auxiliary-prime independence](#104-coefficient-and-auxiliary-prime-independence)
- [11. Bad primes and monodromy](#11-bad-primes-and-monodromy)
  - [11.1 Semistable surface cohomology](#111-semistable-surface-cohomology)
  - [11.2 Hecke isolation of monodromy](#112-hecke-isolation-of-monodromy)
  - [11.3 Conductors and the limits of degree two](#113-conductors-and-the-limits-of-degree-two)
  - [11.4 Descent from a semistable extension](#114-descent-from-a-semistable-extension)
- [12. Comparison with Shimura-curve $H^1$](#12-comparison-with-shimura-curve-h1)
  - [12.1 The common quaternionic eigensystem](#121-the-common-quaternionic-eigensystem)
  - [12.2 Rational and Hecke comparison](#122-rational-and-hecke-comparison)
  - [12.3 Weight and Tate-twist audit](#123-weight-and-tate-twist-audit)
  - [12.4 Galois comparison without a false isomorphism](#124-galois-comparison-without-a-false-isomorphism)
- [13. The degree-two automorphic decomposition theorem](#13-the-degree-two-automorphic-decomposition-theorem)
  - [13.1 Complete statement](#131-complete-statement)
  - [13.2 Proof](#132-proof)
  - [13.3 Hypothesis and failure ledger](#133-hypothesis-and-failure-ledger)
  - [13.4 Conclusion](#134-conclusion)

## 1. The middle-degree realization problem

The compact unitary surfaces constructed from the modèles étranges datum exist for a precise arithmetic reason. A rank-two quaternionic packet may have the wrong parity to be carried by a Shimura curve with all the desired finite local forms. Two noncompact real factors repair the parity, but they also change the geometry: the symmetric domain becomes two-dimensional, and the cohomological packet moves from degree one to degree two. The purpose of this book is to identify that packet inside the middle cohomology without confusing the dimension of the automorphic representation, the dimension of its level invariants, and the dimension of its archimedean cohomology.

### 1.1 Why degree two is unavoidable

For one real rank-one factor, the weight-two discrete series contributes relative Lie algebra cohomology in degree one. With two independent factors, the Kunneth rule adds the degrees:

$$
1+1=2.
$$

This equality is more than a dimension count. The two degree-one classes are odd, so their interchange carries the graded sign $-1$. Their tensor product nevertheless lies in even total degree, exactly where the tensor product of two alternating rank-two pairings becomes symmetric. The surface construction and the automorphic sign calculation are therefore two forms of the same parity repair.

A smooth projective surface has a self-dual middle group $H^2$. This is the only degree capable of containing the product of the two active discrete-series classes. Degrees $0$ and $4$ contain component and orientation classes; degrees $1$ and $3$ would require only one active cohomological factor. The archimedean calculation below will turn this intuition into a vanishing theorem.

### 1.2 The geometric and automorphic data

Let $F$ be totally real and $K/F$ a CM extension. Fix the PEL-exact strange datum of the preceding construction. Its rational similitude group is denoted by $G$, its Shimura conjugacy class by $X$, and its reflex field by $E$. The adjoint group has exactly two noncompact real rank-one factors, indexed by $v_1$ and $v_2$, and is compact at the other real places. The defining Hermitian plane is anisotropic over $F$.

Let $C=C^\Sigma C_\Sigma\subset G(\mathbf A_f)$ be a neat compact open. Here $\Sigma$ contains every finite place at which the group, level, chosen order, central matching, or coefficient normalization is ramified. Let

$$
S_C/E
$$

be a Galois-stable union of the required connected components of the canonical unitary surface. It is smooth and projective of dimension two. Selecting a Galois-stable union is essential: a single geometric component can be defined only over its component field.

A useful mental model is a compact quotient of $\mathfrak h\times\mathfrak h$. It is not generally a product of curves, because the arithmetic lattice can be irreducible in the two real factors. Nevertheless the tangent representation splits into the two complex lines coming from those factors. All archimedean computations below are local to that splitting and therefore do not assume a global product decomposition.

The finite derived group of $G$ matches, up to the specified finite central kernel, the finite adelic points of a quaternion algebra $D/F$. At infinity one uses the inner form having exactly the two active split factors; comparison with a totally definite quaternionic model, when required, passes through their common split Jacquet--Langlands transfer. We write $\Pi$ for a noncharacter automorphic representation in this selected quaternionic packet and $\pi=\operatorname{JL}(\Pi)$ for its split transfer when that description is useful. The good spherical eigenvalues are written

$$
T_w\mapsto t_w(\Pi),\qquad S_w\mapsto s_w(\Pi),
$$

with raw Hecke polynomial

$$
P_w(X,\Pi)=1-t_w(\Pi)X+q_ws_w(\Pi)X^2. \tag{1.1}
$$

Equation (1.1) names the rank-two automorphic eigensystem. It is not, by itself, the characteristic polynomial of Frobenius on surface $H^2$; the latter has weight two and generally has degree four on the full orientation packet.

### 1.3 Coefficients, Frobenius, and actions

Betti cohomology is singular cohomology of $S_C(\mathbf C)$. For a prime $\ell$ and an embedding $\iota_\ell:\overline{\mathbf Q}\hookrightarrow\overline{\mathbf Q}_\ell$, étale cohomology means

$$
H^i_{\mathrm{et}}(S_{C,\bar E},\mathbf Q_\ell).
$$

At a finite residue field $\mathbf F_q$, $F_q$ denotes geometric Frobenius. Our Tate twist is normalized by

$$
F_q\mid\mathbf Q_\ell(1)=q^{-1}.
$$

Thus a pure weight-$m$ eigenvalue has complex absolute value $q^{m/2}$. The middle pairing has target

$$
H^2\times H^2\longrightarrow\mathbf Q_\ell(-2), \tag{1.2}
$$

so reciprocal middle eigenvalues multiply to $q^2$.

A finite Hecke correspondence

$$
S_C\xleftarrow{p_1}S_{C\cap gCg^{-1}}\xrightarrow{p_2}S_C
$$

acts by $(p_2)_*p_1^*$. Galois acts on the left on étale cohomology and Hecke acts on the right through these pull--push maps; the two actions commute because the correspondence is defined over the relevant canonical field. We always keep the selected component union large enough for both maps to land in it.

### 1.4 The logical boundary

The goal is an automorphic decomposition of $H^2$, rational projectors onto its quaternionic packets, and the resulting Hecke-stable Galois representations. We prove purity, good-prime compatibility, and the inherited monodromy structure. We do not manufacture a weight-one, two-dimensional Galois representation from a weight-two surface block. That extraction needs an additional descent argument and belongs after the present decomposition.

Nor do we identify the cohomology of the parameter surface with the cohomology of its auxiliary universal abelian scheme. The latter supplied the PEL moduli interpretation; the former carries the automorphic decomposition. Confusing them would replace an action of $G$ on a locally symmetric space by an unrelated exterior algebra in the fibers.

## 2. The compact surface and its cohomology

Before decomposing cohomology, we must identify which cohomology is being decomposed. Compactness is the decisive simplification. It makes ordinary, compactly supported, and interior cohomology equal, eliminates Eisenstein and boundary terms, and lets the discrete automorphic spectrum account for every differential form.

### 2.1 Compactness removes the boundary

The Hermitian plane defining $G$ is anisotropic over $F$. A rational boundary component of the Hermitian domain would determine a proper rational parabolic of $G^{\mathrm{ad}}$, hence an isotropic $K$-line in that plane. Anisotropy excludes such a line. Therefore the complex double quotient

$$
G(\mathbf Q)\backslash\bigl(X\times G(\mathbf A_f)/C\bigr)
$$

is compact. Its canonical model $S_C$ is projective.

Consequently

$$
H_c^i(S_{C,\bar E},L)=H^i(S_{C,\bar E},L)=H_!^i(S_{C,\bar E},L) \tag{2.1}
$$

for $L=\mathbf Q_\ell$, and similarly in Betti cohomology. There is no boundary long exact sequence and no Eisenstein cohomology. This does not mean that every automorphic constituent is cuspidal in a split-group sense: one-dimensional norm characters remain in the discrete spectrum of the compact quotient. They must be separated internally rather than mislabeled as boundary classes.

### 2.2 The five cohomological degrees

For a geometrically connected component of a smooth projective surface,

$$
H^0\simeq\mathbf Q,\qquad H^4\simeq\mathbf Q(-2),
$$

and Poincaré duality pairs $H^i$ with $H^{4-i}$. Hard Lefschetz for an ample class $\eta\in H^2(1)$ gives

$$
\eta:H^0\xrightarrow{\sim}H^2(1)_{\mathrm{Lef}},
\qquad
\eta:H^1\xrightarrow{\sim}H^3(1). \tag{2.2}
$$

The first map singles out the chosen Lefschetz line, not all algebraic classes. The middle group may also contain a primitive algebraic part and the noncharacter automorphic packets. In particular, “primitive” and “cuspidal” are not synonyms.

The literal product $C_1\times C_2$ of two smooth projective curves provides a sanity check. Kunneth gives

$$
H^2(C_1\times C_2)
=H^2(C_1)\otimes H^0(C_2)
\oplus H^1(C_1)\otimes H^1(C_2)
\oplus H^0(C_1)\otimes H^2(C_2). \tag{2.3}
$$

The outer terms are the two factor classes. For a pair of two-dimensional weight-one eigensystems, the middle term has Hodge types $(2,0)$, two copies of $(1,1)$, and $(0,2)$. The arithmetic surface need not be a product, but its relative Lie algebra calculation will reproduce exactly this pattern.

For a union of $r$ geometric components, $H^0$ and $H^4$ have dimension $r$. Galois permutes their standard bases through the component reciprocity action. The same permutation can appear inside $H^2$ on componentwise Kähler classes, so component bookkeeping cannot be discarded before taking a Hecke projector.

### 2.3 Lefschetz classes and the character part

Over the symmetric domain $\mathfrak h_1\times\mathfrak h_2$, let $\omega_1$ and $\omega_2$ be the invariant $(1,1)$-forms from the two factors. They descend to the quotient and span the degree-two invariant differential forms. Their sum is represented by an ample automorphic line bundle; their difference can be primitive for that polarization.

The trivial representation of each noncompact derived factor has relative cohomology generated by $1$ and its invariant area form. Kunneth therefore gives, in total degree two,

$$
\mathbf C\omega_1\oplus\mathbf C\omega_2. \tag{2.4}
$$

Allowable global norm characters have the same derived archimedean representation and can attach (2.4) to different component characters. These are the **character part** $H^2_{\mathrm{char}}$. It is algebraic after a finite extension: the two forms are first Chern classes of the two automorphic Hodge lines, and finite component characters are isolated by algebraic zero-dimensional projectors.

The orthogonal Hecke complement will be denoted $H^2_{\mathrm{nch}}$. Defining it by the character spectrum, rather than by the kernel of one Lefschetz operator, avoids losing the primitive class $\omega_1-\omega_2$ or admitting an unwanted character twist.

### 2.4 Components and finite quotients

At neat level the quotient is a manifold. At a coarser level choose a neat normal subgroup $C'\triangleleft C$ and put $\Delta=C/C'$. In characteristic zero the transfer identities give

$$
H^i(S_C,L)\simeq H^i(S_{C'},L)^\Delta. \tag{2.5}
$$

Indeed, pullback followed by trace is multiplication by $|\Delta|$, while trace followed by pullback is the sum over $\Delta$. Division by $|\Delta|$ makes invariants exact. Thus all rational decompositions descend from a neat cover. Formula (2.5) does not assert an integral equality when $\ell\mid|\Delta|$.

If a single geometric component is not defined over $E$, replacing $S_C$ by it destroys the $\operatorname{Gal}(\bar E/E)$-action. We instead take the orbit under component reciprocity. Automorphic decompositions may then contain a finite permutation multiplicity. This multiplicity is separate from automorphic multiplicity and will be recorded by the orientation-component factor.

## 3. Hecke correspondences in middle degree

Automorphic representations become visible in geometry through correspondences. The action convention matters: reversing the two maps changes an operator to its adjoint, while omitting a degree changes its integral normalization. We therefore establish the correspondence algebra before using eigenvalues.

### 3.1 Pull--push and variance

For $g\in G(\mathbf A_f)$ set $C_g=C\cap gCg^{-1}$. Right translation by $g$ gives the second map in

$$
S_C\xleftarrow{p_1}S_{C_g}\xrightarrow{p_2}S_C.
$$

Both maps are finite étale at neat level. Define

$$
[CgC]=(p_2)_*p_1^*. \tag{3.1}
$$

Pullback is contravariant and trace is covariant, so (3.1) acts in the same order as right convolution on automorphic forms. The identity double coset acts as the identity. If $g$ normalizes $C$, (3.1) is the pullback by the inverse of right translation, again agreeing with right-regular conventions.

The projection formula proves that (3.1) respects cup products in the usual module sense. It preserves degree and every rational coefficient structure over which the correspondence is defined.

As a normalization check, take $g$ with $CgC=Cg$ and suppose the induced map $r_g:S_C\to S_C$ is an automorphism. Then $p_1$ is the identity and $p_2=r_g$, so (3.1) is $(r_g)_*=(r_g^{-1})^*$ on cohomology. This is exactly the operator obtained by right translating automorphic functions by $g$. If instead $p_2$ is a finite cover of degree $d$ and $p_1=p_2$, then $(p_2)_*p_2^*=d$; counting distinct geometric sheets would give the wrong answer in a ramified specialization.

### 3.2 Composition and adjoints

Fiber products of the two correspondence diagrams decompose into double cosets. Proper base change and the projection formula then give

$$
[CgC][ChC]=\sum_x m_x[C x C], \tag{3.2}
$$

where $m_x$ is the scheme-theoretic multiplicity in the double-coset convolution. Thus the geometric action is a representation of the unnormalized Hecke algebra.

Transpose interchanges $p_1$ and $p_2$. Poincaré duality gives

$$
\langle [CgC]x,y\rangle
=\langle x,[Cg^{-1}C]y\rangle, \tag{3.3}
$$

after the Haar and degree normalizations implicit in (3.1). For moduli correspondences, dualizing the universal isogeny can add the central similitude involution; it is included in the notation $g\mapsto g^\dagger$. The correct general formula is $T_g^*=T_{g^\dagger}$.

Because the Hecke algebra contains its adjoints, its image on a finite-dimensional polarized complex cohomology space is semisimple: a commuting family of normal operators is simultaneously diagonalizable. This is the linear-algebra reason that rational eigenspace projectors exist.

### 3.3 The common spherical algebra

Outside $\Sigma$, the strange construction identifies the derived finite local group with the split quaternionic group and preserves the chosen hyperspecial compact. We use the common algebra

$$
\mathbb T^\Sigma
=\mathbf Z[T_w,S_w,S_w^{-1}:w\notin\Sigma]. \tag{3.4}
$$

The operators are unnormalized, so the polynomial is exactly (1.1). Global Jacquet--Langlands gives

$$
t_w(\Pi)=t_w(\pi),\qquad s_w(\Pi)=s_w(\pi) \tag{3.5}
$$

at every good $w$. There is no sign in (3.5). Signs in local character transfer at division places do not alter spherical Hecke operators at split places.

The central generator $S_w$ is indispensable. The eigenvalue of $T_w$ alone does not determine the unordered Satake pair when the central character varies. Likewise, the derived-group Hecke algebra alone cannot distinguish auxiliary torus characters that agree on the derived subgroup.

### 3.4 Galois and specialization compatibility

Canonical descent of Hecke correspondences implies

$$
\sigma T=T\sigma
\quad
(\sigma\in\operatorname{Gal}(\bar E/E),\ T\in\mathbb T^\Sigma). \tag{3.6}
$$

At a good integral place $u$ of $E$ above residue characteristic $p$, every prime-to-$p$ correspondence extends to the smooth projective model. Smooth proper base change intertwines its generic and special-fiber actions. Therefore geometric Frobenius $F_u$, specialization, and $\mathbb T^{\Sigma\cup\{p\}}$ commute.

At a parahoric prime, prime-to-$p$ correspondences extend to the semistable model and act on nearby cycles. They commute with inertia and the monodromy operator. A correspondence involving the bad prime itself requires its explicit integral moduli diagram; nothing here infers such an extension from the generic double coset.

## 4. The compact Matsushima decomposition

We now connect differential forms to automorphic representations. Compactness makes the proof transparent: the regular spectrum is discrete, the Hodge Laplacian has discrete spectrum, and there are no continuous or residual integrals. The only subtlety is to retain the multiplicity space rather than silently replacing it by a scalar.

### 4.1 From differential forms to the discrete spectrum

Choose a connected component $X^+$ of $X$ and let $K_\infty^0$ be its stabilizer in $G(\mathbf R)^0$. For each finite double coset representative $g_j$ the corresponding connected quotient is

$$
\Gamma_j\backslash X^+,\qquad
\Gamma_j=G(\mathbf Q)^+\cap g_jCg_j^{-1}. \tag{4.1}
$$

Neatness makes $\Gamma_j$ torsion-free. Differential $q$-forms on (4.1) identify with functions

$$
f:G(\mathbf R)^0\longrightarrow
\bigwedge^q\mathfrak p^*
$$

satisfying left $\Gamma_j$-invariance and right $K_\infty^0$-equivariance. Here

$$
\mathfrak g_\mathbf C=\mathfrak k_\mathbf C\oplus\mathfrak p_\mathbf C
$$

is the Cartan decomposition. Summing over $j$ rewrites the de Rham complex as the $C$-fixed part of the automorphic complex.

The quotient is compact, so the right regular representation on its $L^2$-space is a Hilbert direct sum

$$
L^2_{\mathrm{disc}}
=\widehat{\bigoplus}_{\rho}
\mathcal M(\rho)\widehat\otimes\rho. \tag{4.2}
$$

Each multiplicity space $\mathcal M(\rho)$ is finite-dimensional. Smooth vectors and a fixed $K_\infty$-type turn (4.2) into an algebraic direct sum with only finitely many summands contributing to a fixed Laplace eigenspace.

### 4.2 Relative Lie algebra cohomology

For an admissible representation $V$ of $G(\mathbf R)^0$, its relative cochain complex is

$$
C^q(\mathfrak g,K_\infty^0;V)
=\operatorname{Hom}_{K_\infty^0}
(\bigwedge^q\mathfrak p_\mathbf C,V). \tag{4.3}
$$

The differential is induced by the infinitesimal action and the Lie bracket. Under the identification of the preceding section, the exterior derivative on automorphic forms is exactly this differential. Hence one automorphic representation contributes

$$
H^q(\mathfrak g,K_\infty^0;\rho_\infty)
\otimes\rho_f^C
$$

at level $C$.

Hodge theory justifies passage from the Hilbert sum to cohomology. On a compact quotient every de Rham class has a unique harmonic representative. The Laplacian is the action of a central elliptic operator plus a scalar on each $K_\infty$-type. Its kernel is finite-dimensional. Therefore only finitely many summands of (4.2) meet the harmonic kernel, and kernels and direct sums commute there.

### 4.3 Proof of the decomposition

Combining the automorphic complex with harmonic representatives gives the Hecke-equivariant isomorphism

$$
H^q_B(S_C(\mathbf C),\mathbf C)
\simeq
\bigoplus_\rho
\mathcal M(\rho)\otimes
\rho_f^C\otimes
H^q(\mathfrak g,K_\infty;\rho_\infty). \tag{4.4}
$$

If the selected surface is an orientation or component union rather than the full double quotient, the last factor is replaced by its allowed orientation-component subspace. We denote it by $A^q_C(\rho_\infty)$.

To prove (4.4) directly, decompose the smooth automorphic forms by (4.2), insert the decomposition into (4.3), and apply the differential componentwise. The harmonic projection preserves every irreducible summand because the Laplacian commutes with the right regular action. Its finite-dimensional kernel is the direct sum of the component kernels. These kernels calculate both de Rham cohomology and relative Lie algebra cohomology. Finally, the finite adelic right action on $C$-fixed vectors agrees with the pull--push action (3.1), so the isomorphism is Hecke-equivariant.

There is no term from a parabolic induction: such a term would arise from the continuous spectrum of a noncompact quotient, which compactness has removed. One-dimensional automorphic representations do occur in (4.4), and Section 2.3 already identified their degree-two classes.

### 4.4 Fixed level and finiteness

At fixed $C$ only representations with $\rho_f^C\ne0$ contribute. The harmonic space in degree $q$ is finite-dimensional, hence only finitely many cohomological $\rho$ occur. Formula (4.4) gives the exact dimension identity

$$
\dim H^q[\rho]
=m(\rho)\,\dim\rho_f^C\,
\dim A_C^q(\rho_\infty). \tag{4.5}
$$

The three factors have different meanings. The first counts automorphic occurrences, the second level vectors, and the third cohomological orientations. A four-dimensional surface eigenspace can arise from the last factor even when the first two factors are one.

## 5. The archimedean degree-two calculation

Formula (4.4) becomes useful only after its archimedean term is computed. The two active factors are rank one, so the calculation reduces to the weight decomposition of the tangent plane and a Kunneth argument.

### 5.1 One active rank-one factor

For an oriented upper half-plane let $K^0\simeq\mathrm{SO}(2)$. The complexified cotangent representation splits into weights $2$ and $-2$:

$$
\mathfrak p_\mathbf C^*=\mathfrak p^{1,0,*}\oplus\mathfrak p^{0,1,*}. \tag{5.1}
$$

Let $D_2^+$ and $D_2^-$ be the two discrete-series representations on the identity component with minimal $K^0$-types $2$ and $-2$. In (4.3), $K^0$-equivariance permits one cochain in degree one and none in degrees zero or two. The neighboring $K$-types in a discrete series differ by two and occur only on one side of the minimal type; the relative differential into and out of the minimal cochain is therefore zero. Thus

$$
H^q(\mathfrak g_1,K^0;D_2^\pm)
=
\begin{cases}
\mathbf C,&q=1,\\
0,&q\ne1.
\end{cases} \tag{5.2}
$$

The $+$ class has Hodge type $(1,0)$ and the $-$ class type $(0,1)$. For the full disconnected real group, the cohomological representation joins the two orientations; its degree-one cohomology is their two-dimensional sum. On a fixed oriented component, one retains the sign selected by that component.

The trivial representation has invariant cohomology in degrees $0$ and $2$, represented by $1$ and the area form, and no degree-one cohomology. A principal series or a discrete series of weight other than two has no constant-coefficient cohomology: its infinitesimal character differs from that of the trivial coefficient system, so the Casimir acts by a nonzero scalar on the relative complex. Harmonic cochains must have Casimir eigenvalue zero.

### 5.2 Two active factors and Kunneth

At the two active places the relative complex is the tensor product of the two rank-one complexes. For a weight-two representation at both places, Kunneth and (5.2) give

$$
H^q(\mathfrak g_1\oplus\mathfrak g_2,
K_1^0\times K_2^0;D_2^{\epsilon_1}\boxtimes D_2^{\epsilon_2})
=
\begin{cases}
\mathbf C,&q=2,\\
0,&q\ne2.
\end{cases} \tag{5.3}
$$

Compact real factors contribute only their prescribed algebraic type. For constant coefficients that type is trivial. Thus a noncharacter automorphic representation contributes to constant cohomology precisely when it has weight two at both active places and the trivial finite-dimensional type at every compact real place.

For the trivial derived representation, Kunneth yields degree-two invariant forms from

$$
H^2_1\otimes H^0_2
\quad\text{and}\quad
H^0_1\otimes H^2_2,
$$

recovering $\omega_1$ and $\omega_2$. There is no mixed $H^1_1\otimes H^1_2$ term because the trivial rank-one representation has no $H^1$.

### 5.3 Hodge types and orientation packets

The sign pair $(\epsilon_1,\epsilon_2)$ determines Hodge type:

$$
(+,+)\mapsto(2,0),\quad
(+,-),(-,+)\mapsto(1,1),\quad
(-,-)\mapsto(0,2). \tag{5.4}
$$

Let $\Omega_C(\Pi)$ be the set of sign pairs and component characters admitted by the chosen canonical component union. Put

$$
d_\infty(\Pi,C)=|\Omega_C(\Pi)|. \tag{5.5}
$$

For a full union stable under both orientation involutions, $d_\infty=4$ and the packet Hodge numbers are

$$
h^{2,0}=1,\qquad h^{1,1}=2,\qquad h^{0,2}=1. \tag{5.6}
$$

For a connected oriented component, only the compatible sign pairs occur. Formula (5.5), rather than the unconditional number four, is the correct multiplicity in general. Complex conjugation interchanges $(2,0)$ with $(0,2)$ and the two mixed orientations with one another, so every union defined over a real subfield contains signs in conjugate pairs.

### 5.4 Exclusion of other infinity types

Suppose an irreducible automorphic $\rho$ contributes to $H^2$. At a compact real place, the coefficient and representation types must pair. At an active place, the Casimir argument leaves either the trivial representation in degrees $0,2$ or weight-two discrete series in degree $1$. Total degree two therefore has only three possibilities:

1. discrete series in both active factors, contributing the noncharacter packet (5.3);
2. trivial derived type in both factors, contributing (2.4);
3. a degree-two trivial class at one factor and degree zero at the other, which is already the second case.

There is no constituent with discrete series at exactly one active factor: it would contribute in odd total degree. There is no higher-weight constituent with constant coefficients. This proves that the character and selected parallel-weight-two packets exhaust $H^2$.

## 6. Quaternionic packets and exact multiplicities

The strange surface is unitary, whereas the eigensystems of interest are described quaternionically. The bridge is finite-adelic matching plus central bookkeeping. The derived groups alone do not determine a representation of the full similitude group, so auxiliary characters must remain visible.

### 6.1 Finite-adelic matching

The strange datum supplies a homomorphism from a group built from $D^\times$ and an auxiliary torus to $G$ with finite central kernel. At every finite place outside $\Sigma$, it identifies the derived groups, hyperspecial compact subgroups, and spherical double cosets. There are two directions to the comparison, and they must be distinguished.

Starting with an automorphic representation $\rho$ of $G$, pullback through the central homomorphism decomposes into tensor products $\Pi\boxtimes\chi$. Automorphy is preserved because an automorphic function is simply being pulled back along a homomorphism carrying rational points to rational points. Conversely, suppose $\Pi\boxtimes\chi$ is automorphic, is trivial on the finite central kernel, and satisfies the rational and component equations. Its automorphic functions are constant on kernel fibers and therefore descend to $G$. This produces $\rho(\Pi,\chi)$.

Thus finite local matching alone is not being used to infer automorphy. It identifies local factors after an actual global pullback or descent. When $\Pi$ begins on a different quaternionic inner form with the same finite factors, global Jacquet--Langlands first transfers it to the split group and then to the surface inner form, under the stated local image condition. Changing two archimedean invariants preserves the global parity relation, while the finite components and their good Hecke characters remain unchanged.

The central equation has the form

$$
\omega_\Pi(z)\chi(z) =1
\quad(z\in Z_{\mathrm{ker}}(\mathbf A)), \tag{6.1}
$$

together with triviality on rational points and compatibility with the level. Only finitely many $\chi$ occur at fixed level and infinity type. Different choices can have the same derived Hecke eigenvalues, which is why the center and component action are included in $\Omega_C(\Pi)$.

Global Jacquet--Langlands identifies $\Pi$ with a unique selected cuspidal $\pi$ on $\mathrm{GL}_2(\mathbf A_F)$ and preserves the good polynomial (1.1), algebraic weight, central character, and field of rationality. At a definite real factor, parallel weight two is represented by the trivial algebraic quaternionic type; at an active split factor it is represented by the weight-two discrete series of Chapter 5. This supplies a second name for the same good eigensystem without identifying the underlying infinite-dimensional representation spaces.

### 6.2 Central extensions and auxiliary characters

We record the multiplicity argument for the central modification. Let $H\to G^{\mathrm{der}}$ be the finite central cover arising from the quaternionic group, and fix an admissible $\chi$. Restriction of a $G$-automorphic occurrence to $H$ lands in the $\Pi$-isotypic automorphic space. The latter has a one-dimensional multiplicity space by quaternionic multiplicity one.

Let $\mathcal M_G(\rho)$ be the occurrence space of $\rho$ and $\mathcal M_H(\Pi)$ that of $\Pi$. Restriction followed by projection to the chosen central character defines an injection from $\mathcal M_G(\rho)$ into the $\chi$-eigenspace of

$$
\mathcal M_H(\Pi)\otimes \operatorname{Fun}(A,\mathbf C),
$$

where $A$ is the finite abelian component fiber of the central map. Injectivity follows because an automorphic embedding that vanishes after pullback vanishes on the selected quotient. The regular representation of $A$ contains each character once, and $\mathcal M_H(\Pi)$ is a line. Thus the target eigenspace has dimension one. If $\rho(\Pi,\chi)$ occurs, its occurrence space is nonzero and hence

$$
m_G(\rho(\Pi,\chi))=1. \tag{6.2}
$$

This proof uses the full central equation. Without fixing $\chi$, several distinct one-dimensional eigenspaces may be grouped under one derived packet and look like higher automorphic multiplicity.

### 6.3 Multiplicity one versus cohomological dimension

Insert (6.2) into (4.5). For a selected lift $\rho=\rho(\Pi,\chi)$,

$$
\dim_\mathbf C H^2[\rho]
=\dim\rho_f^C\cdot d_\infty(\rho,C). \tag{6.3}
$$

At a minimal level where every selected local invariant space is a line, a full orientation packet therefore has dimension four. This does not contradict multiplicity one: there is one global occurrence, one finite level vector, and four archimedean cohomology lines.

At deeper level, $\dim\rho_f^C$ can exceed one. At a division place a normal congruence subgroup can fix either none or an entire finite-dimensional local representation. At split old level several oldvectors can occur. Formula (6.3) records these effects without treating them as repeated automorphic occurrences.

### 6.4 The complex decomposition theorem

Let $\mathcal P_C$ be the finite set of pairs $(\Pi,\chi)$ satisfying:

- $\Pi$ is a selected noncharacter quaternionic automorphic representation;
- its algebraic weight is parallel two, so its surface lift is discrete series at the two active places and has the required trivial algebraic type at compact places;
- the central equation (6.1), component condition, and $C$-invariance hold.

Then

$$
H^2_B(S_C,\mathbf C)
=H^2_{\mathrm{char}}
\oplus
\bigoplus_{(\Pi,\chi)\in\mathcal P_C}
\rho(\Pi,\chi)_f^C\otimes A_C^2(\Pi,\chi). \tag{6.4}
$$

Every sum is direct and Hecke-stable. Each $A_C^2$ has the sign basis (5.4); each automorphic multiplicity is one. The proof is now complete: Matsushima gives (4.4), Section 5 classifies all nonzero archimedean terms, the character calculation gives the first summand, and (6.2) removes multiplicity spaces from the noncharacter terms without choosing a basis for their canonical lines.

## 7. Isolating a packet by Hecke operators

The direct sum (6.4) is complex analytic. Arithmetic applications require algebraic projectors defined from correspondences. Fixed level finiteness and strong determination allow one to construct them from finitely many good Hecke operators.

### 7.1 Simultaneous eigenspaces

The image of $\mathbb T^\Sigma$ on $H^2_B(S_C,\mathbf Q)$ is a finite-dimensional commutative algebra. After extending to $\mathbf C$ and adjoining adjoints, it acts semisimply by Section 3.2. Hence

$$
H^2_B(S_C,\mathbf C)=\bigoplus_\lambda H^2[\lambda], \tag{7.1}
$$

where $\lambda$ ranges over simultaneous characters, including the central and component operators needed to distinguish lifts.

For a noncharacter packet, $\lambda=\lambda_{\Pi,\chi}$ has values $t_w(\Pi),s_w(\Pi)$ at good places. Strong multiplicity one after global Jacquet--Langlands shows that equality of these values for almost all $w$, together with the central character, identifies $\Pi$. The auxiliary character is then identified by the torus and component operators.

### 7.2 Finite separating sets and projectors

Only finitely many characters occur in (7.1). For a fixed $\lambda$, choose for every $\mu\ne\lambda$ an operator $T_\mu$ with $\lambda(T_\mu)\ne\mu(T_\mu)$. The product

$$
e_\lambda
=\prod_{\mu\ne\lambda}
\frac{T_\mu-\mu(T_\mu)}
{\lambda(T_\mu)-\mu(T_\mu)} \tag{7.2}
$$

acts as identity on $H^2[\lambda]$ and zero on every other simultaneous eigenspace. Thus it is an idempotent correspondence with coefficients in a finite extension containing the eigenvalues.

If $\lambda$ is replaced by its orbit under $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, summing the conjugates of (7.2) gives a rational projector

$$
e_{[\lambda]}\in\mathbb T^\Sigma\otimes\mathbf Q. \tag{7.3}
$$

The individual projector is defined over the Hecke field $L_\lambda$. Formula (7.2) also proves that a finite set of good places separates the packets at this fixed level; no infinite limiting projector is involved.

For example, if exactly two packets occur and one operator $T$ has eigenvalues $a\ne b$, then

$$
e_a=\frac{T-b}{a-b},\qquad e_b=\frac{T-a}{b-a}.
$$

One checks immediately that $e_a^2=e_a$, $e_ae_b=0$, and $e_a+e_b=1$ on the cohomology space. If $a\equiv b$ modulo a prime above $\ell$, the denominator explains exactly why this rational splitting can fail on the integral lattice.

### 7.3 Character packets and noncharacter packets

The set of character eigensystems at fixed level is finite. Applying the same interpolation gives $e_{\mathrm{char}}$ and

$$
e_{\mathrm{nch}}=1-e_{\mathrm{char}}. \tag{7.4}
$$

This is the precise boundary exclusion. Since $S_C$ is projective, there is no geometric boundary contribution. Equation (7.4) removes only global norm-character classes, including both invariant Kähler lines and their component twists.

It would be incorrect to quotient merely by the ample Lefschetz line. The second invariant class can be primitive. It would also be incorrect to call the full $H^{1,1}$ algebraic or character-valued: mixed-orientation noncharacter packets contribute to $H^{1,1}$ by (5.4).

### 7.4 Denominators and integral warnings

The denominators in (7.2) are differences of eigenvalues. They need not be units at a chosen prime $\lambda\mid\ell$. Consequently $e_\lambda$ always splits rational $\ell$-adic cohomology but need not preserve or split the natural $\mathbf Z_\ell$-lattice.

One may define the saturated lattice

$$
\Lambda_\lambda
=H^2(S_{C,\bar E},\mathbf Z_\ell)
\cap e_\lambda H^2(S_{C,\bar E},L_{\lambda}) \tag{7.5}
$$

inside rational cohomology. It is Galois and Hecke stable, but (7.5) is not asserted to be a direct summand. Congruent packets can meet modulo $\ell$, and semisimplicity over characteristic zero does not prevent that intersection.

## 8. Rational and Hodge structures

Automorphic decomposition over $\mathbf C$ must be reconciled with the rational structure coming from topology. Hecke correspondences do this: their characteristic polynomials are rational, conjugation permutes eigenspaces, and the sum over a conjugacy orbit descends.

### 8.1 The rational Betti decomposition

For a Galois orbit $[\lambda]$, put

$$
H^2_B[\lambda]_{\mathbf Q}=e_{[\lambda]}H^2_B(S_C,\mathbf Q). \tag{8.1}
$$

Then

$$
H^2_B(S_C,\mathbf Q)
=H^2_{\mathrm{char},\mathbf Q}
\oplus\bigoplus_{[\lambda]}H^2_B[\lambda]_{\mathbf Q}. \tag{8.2}
$$

Tensoring (8.2) with $\mathbf C$ recovers (6.4), grouped by algebraic conjugacy. The equality follows because (7.3) consists of rational algebraic correspondences and the mutually orthogonal idempotents sum to one.

An individual eigenspace is naturally a vector space over its Hecke field $L_\lambda$. If $L_\lambda$ acts faithfully, its $L_\lambda$-dimension is the common complex dimension of one embedding component, namely

$$
\dim_{L_\lambda}H^2_B[\lambda]
=\dim\rho_f^C\,d_\infty(\rho,C). \tag{8.3}
$$

If several auxiliary lifts have identical chosen spherical eigenvalues, the torus operators must be adjoined before (8.3) is applied.

### 8.2 Hecke fields and conjugation

Define

$$
L_\Pi=\mathbf Q(t_w(\Pi),s_w(\Pi):w\notin\Sigma), \tag{8.4}
$$

including the central and auxiliary character values. Algebraicity of the cohomological Hecke action makes $L_\Pi$ a number field. Global Jacquet--Langlands and (3.5) show that the quaternionic, split, and surface eigensystems have the same field.

For $\sigma\in\operatorname{Aut}(\mathbf C)$,

$$
\sigma(H^2[\Pi,\chi])=H^2[\Pi^\sigma,\chi^\sigma]. \tag{8.5}
$$

Indeed, apply $\sigma$ to every eigenvalue equation. Conversely, if $\sigma$ fixes the good eigenvalues and central data, strong determination fixes the automorphic packet. Thus the stabilizer of the eigensystem is exactly the stabilizer of its Hecke field.

### 8.3 Polarizations and duality

Choose an ample Hecke-equivariant polarization and average it over the finite adjoint algebra if necessary. Poincaré duality and (3.3) restrict to a perfect pairing between a packet and its adjoint packet:

$$
H^2_B[\lambda]\times H^2_B[\lambda^\dagger]
\longrightarrow L_\lambda(-2). \tag{8.6}
$$

When the packet is self-dual after the prescribed central twist, (8.6) is nondegenerate on it. In degree two the cup product is symmetric, consistent with the tensor product of the two alternating rank-one orientation pairings.

Complex conjugation interchanges the Hodge pieces in (5.4). Hence the full orientation packet is a polarizable Hodge structure of weight two. A smaller component packet is paired with its conjugate component if it is not itself conjugation-stable.

### 8.4 De Rham realization

Over an embedding $E\hookrightarrow\mathbf C$, algebraic de Rham comparison gives

$$
H^2_{\mathrm{dR}}(S_C/E)\otimes_E\mathbf C
\simeq H^2_B(S_C,\mathbf Q)\otimes\mathbf C. \tag{8.7}
$$

Algebraic correspondences commute with (8.7), so every $e_{[\lambda]}$ cuts out a de Rham block with the same characteristic polynomials. The Hodge filtration on a full minimal packet has graded dimensions $1,2,1$ in degrees $2,1,0$, as in (5.6).

The comparison is rational, not integral. Torsion in coherent surface cohomology can obstruct an ordinary integral Hodge decomposition even though the derived de Rham complex base-changes correctly. No integral period lattice is inferred from (8.7).

## 9. The etale Galois realization

The canonical model gives arithmetic meaning to a Betti packet. Étale comparison transports its projector, while canonical descent makes the resulting subspace stable under Galois. This produces the degree-two representation promised by the surface construction.

### 9.1 Comparison and descent

Fix an embedding $\bar E\hookrightarrow\mathbf C$ and a prime $\ell$. Betti--étale comparison for smooth proper varieties gives a functorial isomorphism

$$
H^2_B(S_C(\mathbf C),\mathbf Q_\ell)
\simeq H^2_{\mathrm{et}}(S_{C,\bar E},\mathbf Q_\ell). \tag{9.1}
$$

Functoriality for finite pullback and trace makes (9.1) Hecke-equivariant. The left side supplies the dimension and rational projector; the right side supplies a continuous action of $G_E=\operatorname{Gal}(\bar E/E)$.

Because the correspondences defining $e_{[\lambda]}$ descend to $E$, (3.6) implies that their images are $G_E$-stable. If an individual $e_\lambda$ is defined over $L_\lambda$ and $\iota_\ell:L_\lambda\hookrightarrow\overline{\mathbf Q}_\ell$, it also cuts out a stable block after scalar extension.

### 9.2 The packet representation

Define

$$
V_{\lambda,\ell}
=e_\lambda
H^2_{\mathrm{et}}(S_{C,\bar E},
L_{\lambda,\ell}), \tag{9.2}
$$

where $L_{\lambda,\ell}$ is the completion determined by $\iota_\ell$. Then $V_{\lambda,\ell}$ is a continuous $L_{\lambda,\ell}$-representation of $G_E$, commuting with the Hecke action. Its formation commutes with finite coefficient extension.

The cup-product pairing has the typed form

$$
V_{\lambda,\ell}\times V_{\lambda^\dagger,\ell}
\longrightarrow L_{\lambda,\ell}(-2). \tag{9.3}
$$

Thus

$$
V_{\lambda,\ell}^\vee\simeq
V_{\lambda^\dagger,\ell}(2). \tag{9.4}
$$

Equation (9.4) fixes both the sign and the twist: geometric Frobenius eigenvalues on paired blocks multiply to $q^2$.

### 9.3 Dimensions and scalar extension

Comparison with (6.3) yields

$$
\dim_{L_{\lambda,\ell}}V_{\lambda,\ell}
=\dim\rho_f^C\,d_\infty(\rho,C). \tag{9.5}
$$

In particular, a full minimal orientation packet has dimension four. If the level-invariant dimension is greater than one, the Galois action may mix those level vectors only through endomorphisms commuting with the common Hecke character; the automorphic decomposition alone does not canonically split them further.

Changing $\iota_\ell$ conjugates $\lambda$ and gives the conjugate packet. Changing $\ell$ changes the coefficient topology but not (9.5), the Betti source, or the algebraic Hecke character.

### 9.4 What has and has not been extracted

The representation (9.2) is the complete degree-two surface realization. It is not automatically irreducible or two-dimensional. A four-dimensional full packet can encode a tensor or descent pattern, but discovering a rank-two factor requires information not contained in a semisimple Hecke eigencharacter alone.

In particular, one may not choose a two-dimensional Hodge subspace such as $(2,0)\oplus(0,2)$ and declare it Galois-stable. Hodge decomposition is defined after an archimedean embedding and is generally not preserved by arithmetic Galois. Nor may one divide Frobenius weights by taking a formal half Tate twist. The extraction problem begins only after the honest weight-two representation has been constructed.

## 10. Frobenius traces, purity, and independence

At a good finite place, geometry supplies more than unramifiedness. The Lefschetz formula computes traces of Frobenius combined with Hecke correspondences, and purity constrains every root. Projectors then transfer both statements to a single packet.

### 10.1 Good reduction

Let $u$ be a finite place of $E$ above $p$, with residue field $k_u$ of size $q_u$. Assume the PEL algebra is unramified at $p$, the lattice is self-dual, the level is hyperspecial, the determinant local model is smooth, and $u\notin\Sigma$. The unitary surface has a smooth projective model $\mathscr S_C/\mathcal O_{E,u}$, and smooth proper base change gives

$$
H^2_{\mathrm{et}}(S_{C,\bar E},\mathbf Q_\ell)
\simeq H^2_{\mathrm{et}}(\mathscr S_{C,\bar k_u},\mathbf Q_\ell)
\quad(\ell\ne p). \tag{10.1}
$$

The left representation is unramified at $u$. Under (10.1), a geometric Frobenius element acts as geometric Frobenius on the special fiber. Every prime-to-$p$ Hecke correspondence extends and commutes with this identification.

### 10.2 Projected Lefschetz traces

Let $T$ be a finite linear combination of good Hecke correspondences. The Lefschetz--Verdier formula gives

$$
\sum_{i=0}^4(-1)^i
\operatorname{Tr}(TF_u^n\mid H^i)
=\sum_{z\in\operatorname{Fix}(T\circ F_u^n)}
\operatorname{LT}_z(T,F_u^n), \tag{10.2}
$$

with positive-dimensional fixed loci interpreted by their local trace classes. For a finite étale transverse correspondence and constant coefficients, every isolated local term is its scheme-theoretic intersection multiplicity, equal to one in the transverse case.

Apply (10.2) to every monomial appearing in (7.2). Since the projector commutes with Frobenius,

$$
\operatorname{Tr}(e_\lambda F_u^n\mid H^2)
=\operatorname{Tr}(F_u^n\mid V_{\lambda,\ell}). \tag{10.3}
$$

For a noncharacter $\lambda$, the archimedean calculation proves

$$
e_\lambda H^i=0\qquad(i\ne2). \tag{10.4}
$$

Therefore the entire alternating trace of $e_\lambda F_u^n$ is its degree-two trace; no algebraic projector onto cohomological degree is required. Applying (10.2) to the polynomial expression for $e_\lambda$ computes (10.3) from algebraic intersections. For a character projector, the known invariant classes in degrees $0,2,4$ are instead subtracted explicitly. This is the promised use of the low-dimensional Lefschetz formula: it isolates the packet without presupposing a Galois factorization.

### 10.3 Purity and reciprocal roots

The special fiber in (10.1) is smooth and projective of dimension two. Hence its $H^2$ is pure of weight two. A Frobenius-compatible idempotent preserves purity, so every eigenvalue $\alpha$ of $F_u$ on $V_{\lambda,\ell}$ satisfies

$$
|\iota(\alpha)|=q_u \tag{10.5}
$$

for every complex embedding $\iota$. If $\lambda$ is self-adjoint, (9.3) pairs roots as

$$
\alpha\longleftrightarrow q_u^2/\alpha. \tag{10.6}
$$

For a four-dimensional full minimal packet the characteristic polynomial has degree four, all roots have modulus $q_u$, and its constant term has modulus $q_u^4$. This cannot equal the quadratic raw Hecke polynomial (1.1), whose rank-two roots have weight one in the cohomological normalization. The surface trace formula determines a weight-two polynomial attached to the packet; extracting a weight-one quadratic factor is a later theorem.

### 10.4 Coefficient and auxiliary-prime independence

Write

$$
Q_{u,\lambda}(X)
=\det(1-XF_u\mid V_{\lambda,\ell}). \tag{10.7}
$$

For all $n\ge1$, (10.3) expresses the power sum of the reciprocal roots as a finite $L_\lambda$-linear combination of intersection numbers of algebraic correspondences. It is therefore independent of $\ell$. Newton identities recover the coefficients of (10.7) from the first $d=\dim V_{\lambda,\ell}$ power sums. Hence

$$
Q_{u,\lambda}(X)\in L_\lambda[X]
$$

and is independent of the auxiliary prime and embedding, up to applying the corresponding embedding of $L_\lambda$.

More explicitly, if $p_n=\operatorname{Tr}(F_u^n\mid V_{\lambda,\ell})$ and

$$
Q_{u,\lambda}(X)=1+c_1X+\cdots+c_dX^d,
$$

then

$$
mc_m+\sum_{i=1}^m c_{m-i}p_i=0
\qquad(1\le m\le d),\qquad c_0=1.
$$

Induction on $m$ places every $c_m$ in $L_\lambda$ and proves its independence. The denominators $m$ occur inside a characteristic-zero number field and create no ambiguity; they say nothing about integrality at primes dividing $m$.

This proof requires the correspondences and their projector coefficients to be defined over the stated field. It proves rational compatibility, not an integral common lattice. It also does not say that $Q_{u,\lambda}$ is determined by the single pair $t_w,s_w$ at one place; the projected fixed-point traces are the geometric input.

## 11. Bad primes and monodromy

Good reduction sees only unramified Frobenius. At a parahoric prime the same packet projector acts on nearby cycles, so the semistable geometry restricts to the automorphic block. This gives a precise Galois structure even before it is compared with a local Langlands parameter.

### 11.1 Semistable surface cohomology

Let $u\mid p$ be a place at which one or two active rank-two directions are Iwahori. After the verified regularization, the model is strictly semistable, locally of the form

$$
xy=\varpi
\quad\text{or}\quad
xyz=\varpi.
$$

The nearby-cycle weight complex is built from component surfaces, double curves, and triple points with alternating restriction and Gysin maps. On $H^2$ the logarithm of tame inertia has typed form

$$
N:H^2\longrightarrow H^2(-1),\qquad N^3=0, \tag{11.1}
$$

and geometric Frobenius satisfies

$$
FNF^{-1}=q_u^{-1}N. \tag{11.2}
$$

Double-curve cohomology controls length-two Jordan blocks; surviving two-cycles in the dual complex control $N^2$. The number of triple points alone determines neither quantity.

### 11.2 Hecke isolation of monodromy

Prime-to-$p$ Hecke correspondences act on every stratum and commute with the restriction--Gysin differentials. Hence

$$
e_\lambda N=Ne_\lambda,\qquad
e_\lambda F=Fe_\lambda. \tag{11.3}
$$

The Weil--Deligne structure therefore restricts to

$$
(r_{\lambda,u},N_{\lambda,u})
\quad\text{on }V_{\lambda,\ell}. \tag{11.4}
$$

Its ranks can be computed by applying $e_\lambda$ to the cohomology of the strata before taking the weight-complex cohomology. Exactness over the coefficient field makes this equivalent to projecting afterward. Integral exactness is not asserted if the projector has denominators.

### 11.3 Conductors and the limits of degree two

The Artin conductor is

$$
a(V)=\dim V-\dim V^{I_u}+\operatorname{Swan}(V), \tag{11.5}
$$

or, after separating finite inertia from the unipotent part, the equivalent Weil--Deligne formula including $\operatorname{rank}N$ on inertia invariants. At split strictly semistable level with trivial finite inertia and no wild part,

$$
a(V_{\lambda,\ell})=\operatorname{rank}N_{\lambda,u}. \tag{11.6}
$$

The conductor does not record $\operatorname{rank}N^2$, the Frobenius eigenvalues on $\ker N$, or finite descent. A full four-dimensional packet can have length-three blocks. If a genuine two-dimensional subquotient is later isolated, dimensional reasons force $N^2=0$ on it; that conclusion cannot be imposed on the full surface block in advance.

Two elementary Jordan calculations illustrate the loss of information. On a four-dimensional space, two blocks of length two have

$$
\operatorname{rank}N=2,\qquad \operatorname{rank}N^2=0.
$$

A block of length three together with a trivial block also has $\operatorname{rank}N=2$, but now $\operatorname{rank}N^2=1$. Formula (11.6) gives the same conductor in the split semistable case, although the two Weil--Deligne representations are not isomorphic. Moreover, changing Frobenius on the trivial block preserves both ranks and can change the local Euler factor. This is why the nearby-cycle package retains $(r,N)$ rather than only its conductor.

### 11.4 Descent from a semistable extension

If strict semistability is achieved only after a finite extension $E'_u/E_u$, the model computes the unipotent part of inertia over $E'_u$. Descent retains a finite action of $\operatorname{Gal}(E'_u/E_u)$ on the strata and on their incidence complex. Combining it with $N$ recovers the full inertial representation over $E_u$.

Dropping that finite action can change $\dim V^{I_u}$ and the conductor. Likewise, a nonsplit node carries a signed Galois permutation on its branches. The packet projector commutes with this descent action because it is defined by correspondences over the original canonical field.

## 12. Comparison with Shimura-curve $H^1$

The surface was introduced because a curve realization is not always available with the required parity. Where both descriptions can be formed, they should nevertheless be compared. The correct comparison preserves quaternionic eigensystems and rationality fields while respecting the one-degree shift in geometry.

### 12.1 The common quaternionic eigensystem

Let $C_U$ be a compact quaternionic Shimura curve whose finite derived datum admits the same selected $\Pi$ and good spherical algebra. Matsushima in dimension one gives a weight-two packet in

$$
H^1_B(C_U,\mathbf C)
$$

with the same eigenvalues $t_w(\Pi),s_w(\Pi)$ and automorphic multiplicity one. At minimal level its full orientation space has dimension two, of Hodge types $(1,0)$ and $(0,1)$.

The surface packet and curve packet are therefore indexed by the same finite quaternionic representation, and global Jacquet--Langlands identifies both with the same split $\mathrm{GL}_2$ representation. This is a statement about automorphic labels and finite Hecke actions, not about an isomorphism of varieties.

### 12.2 Rational and Hecke comparison

Let $W_{\Pi,\ell}\subset H^1_{\mathrm{et}}(C_{U,\bar E},L_{\Pi,\ell})$ be the curve block and $V_{\Pi,\ell}\subset H^2_{\mathrm{et}}(S_{C,\bar E},L_{\Pi,\ell})$ the surface block, after a common field of definition has been chosen. Then:

$$
L(W_\Pi)=L(V_\Pi)=L_\Pi, \tag{12.1}
$$

and every good Hecke operator acts through the same character on the two blocks. Algebraic conjugation sends both blocks to those indexed by $\Pi^\sigma$. Their Betti, de Rham, and étale projectors are polynomials in the same abstract good Hecke operators, interpreted on the two varieties.

The dimensions differ:

$$
\dim W_\Pi=2\dim\pi_f^U,\qquad
\dim V_\Pi=4\dim\rho_f^C \tag{12.2}
$$

for full orientation unions. Local fixed-vector dimensions may also differ. Thus equality of Hecke characters never justifies equality of total vector spaces.

### 12.3 Weight and Tate-twist audit

At a common good place $u$, curve $H^1$ is pure of weight one and surface $H^2$ is pure of weight two:

$$
|\alpha(W_\Pi)|=q_u^{1/2},
\qquad
|\alpha(V_\Pi)|=q_u. \tag{12.3}
$$

An integral Tate twist changes weight by an even integer:

$$
\operatorname{wt}(V(n))=\operatorname{wt}(V)-2n. \tag{12.4}
$$

There is no integer $n$ with $2-2n=1$. Therefore $V_\Pi(n)$ cannot be isomorphic to $W_\Pi$ for any Tate twist. Their pairings also have different targets:

$$
W_\Pi\times W_{\Pi^\dagger}\to L_\Pi(-1),
\qquad
V_\Pi\times V_{\Pi^\dagger}\to L_\Pi(-2). \tag{12.5}
$$

This normalization check rules out one of the most tempting but serious errors in using the surface construction.

### 12.4 Galois comparison without a false isomorphism

Both $W_{\Pi,\ell}$ and $V_{\Pi,\ell}$ are continuous Galois representations, unramified at common good primes, with Hecke-compatible Frobenius traces and packet fields $L_\Pi$. At bad primes their monodromy operators are obtained from the respective curve graph and surface incidence complexes, and both commute with the same prime-to-bad Hecke projector.

The comparison is therefore the commutative pattern

$$
\begin{array}{ccc}
\Pi&\longleftrightarrow&W_{\Pi,\ell}\subset H^1(C_U)\\
\Vert&&\quad\text{same Hecke field and eigencharacter}\\
\Pi&\longleftrightarrow&V_{\Pi,\ell}\subset H^2(S_C),
\end{array} \tag{12.6}
$$

not a vertical Galois isomorphism. The surface block contains the degree-two arithmetic object from which a later descent theorem may recover rank-two data. The present comparison supplies the common labels, rationality, duality conventions, and local geometric operators needed for that theorem.

## 13. The degree-two automorphic decomposition theorem

We conclude by assembling the analytic, geometric, and arithmetic arguments into one theorem. Its hypotheses deliberately retain compactness, component stability, central characters, and projector denominators, since each prevents a distinct false conclusion.

### 13.1 Complete statement

**Theorem 13.1 (automorphic decomposition of unitary-surface $H^2$).** Let $F$ be totally real, $K/F$ CM, and let $(G,X)$ be a PEL-exact compact unitary modèles étranges datum with exactly two signature-$(1,1)$ real places. Assume:

1. the defining Hermitian plane is anisotropic over $F$;
2. its finite derived group matches the selected quaternion algebra $D/F$, with finite central kernel, auxiliary torus, and central equation specified;
3. $C\subset G(\mathbf A_f)$ is neat, and $S_C/E$ is a Galois- and Hecke-stable union of canonical components;
4. $\Sigma$ contains every ramified group, level, central, and integral place;
5. all quaternionic packets under consideration lie in the established global Jacquet--Langlands range and have parallel algebraic weight two, so the associated surface representation is weight-two discrete series at the two active real places and has the required trivial types elsewhere.

Then the following hold.

**(a) Complex decomposition.** There is a Hecke-equivariant direct sum

$$
H^2_B(S_C,\mathbf C)
=H^2_{\mathrm{char}}
\oplus
\bigoplus_{(\Pi,\chi)\in\mathcal P_C}
\rho(\Pi,\chi)_f^C\otimes A_C^2(\Pi,\chi).
$$

Every noncharacter automorphic multiplicity is one, and

$$
\dim A_C^2(\Pi,\chi)=d_\infty(\Pi,\chi;C).
$$

For the full orientation union this dimension is four with Hodge numbers $(1,2,1)$. The character part is generated by the two invariant degree-two classes and their allowable component-character twists. No boundary or Eisenstein term occurs.

**(b) Hecke and rational structures.** Finitely many operators in $\mathbb T^\Sigma$, together with central and component operators, separate the occurring packets. Each packet has a projector over its Hecke field $L_\Pi$; the sum over its conjugacy orbit is rational. The quaternionic, split Jacquet--Langlands, surface, and available curve realizations have the same good Hecke field and conjugation action.

**(c) Galois realization.** For every $\ell$ and embedding $L_\Pi\hookrightarrow\overline{\mathbf Q}_\ell$, the projector cuts out a continuous $G_E$-representation

$$
V_{\Pi,\chi,\ell}\subset
H^2_{\mathrm{et}}(S_{C,\bar E},L_{\Pi,\ell})
$$

of dimension $\dim\rho_f^C\,d_\infty$. It is paired with its adjoint into $L_{\Pi,\ell}(-2)$. The natural integral lattice need not split if the projector has $\ell$-adic denominators.

**(d) Good primes.** At every good PEL place $u\nmid\ell$ outside $\Sigma$, this representation is unramified and pure of weight two. Its Frobenius polynomial lies in $L_\Pi[X]$, is independent of $\ell$, and is computed by projected Lefschetz traces. Reciprocal roots in adjoint packets multiply to $q_u^2$.

**(e) Bad primes.** At the verified semistable parahoric places, nearby-cycle monodromy, finite inertia, Frobenius, and the conductor restrict to every rational Hecke packet. On the full surface block $N^3=0$; no stronger nilpotence is inferred without a smaller Galois-stable constituent.

**(f) Curve comparison.** When the same quaternionic packet occurs in Shimura-curve $H^1$, the curve and surface blocks share $L_\Pi$, the good Hecke eigencharacter, algebraic conjugation, and compatible projector formalism. The curve block has weight one and pairing twist $(-1)$; the surface block has weight two and pairing twist $(-2)$. They are not related by an integral Tate twist and are not asserted to be Galois-isomorphic.

### 13.2 Proof

Anisotropy implies projectivity and (2.1), so the compact discrete spectrum accounts for all cohomology. The automorphic de Rham complex and harmonic decomposition prove the Matsushima formula (4.4). The rank-one relative Lie algebra calculation (5.2) and Kunneth prove that noncharacter constant-coefficient cohomology occurs exactly in degree two for parallel-weight-two packets at both active places, with signs and Hodge types given by (5.4). The trivial derived representation gives exactly the two invariant degree-two forms. This proves exhaustion and boundary exclusion.

Finite-adelic matching attaches the quaternionic labels. Quaternionic multiplicity one, followed by the finite central-character eigenspace argument of Section 6.2, proves unit multiplicity for every specified lift to $G$. Formula (4.5) then gives the exact level and orientation dimensions. This proves part (a).

At fixed level only finitely many packets occur. Strong determination through global Jacquet--Langlands separates their good eigensystems once central and component data are retained. Lagrange interpolation (7.2) constructs individual projectors, and summing conjugates constructs rational ones. Algebraicity and conjugation compatibility give the common Hecke field. This proves part (b).

Betti--étale comparison is functorial for every correspondence. Canonical descent makes the idempotent image Galois-stable; complex comparison gives its dimension, and Poincaré duality gives the twist in (9.3). This proves part (c).

At a good place, the smooth projective integral model and Hecke-equivariant smooth proper base change identify generic and special cohomology. The surface purity theorem passes to every Frobenius-compatible idempotent. The Lefschetz formula applied to the polynomial projector computes all Frobenius power traces; Newton identities prove coefficient and auxiliary-prime independence. This proves part (d).

At a semistable place, prime-to-bad Hecke correspondences act on the restriction--Gysin complex and commute with nearby cycles, $N$, finite descent, and Frobenius. Applying the projector gives part (e). Finally, the one-factor archimedean calculation, the common quaternionic Hecke character, and the explicit weight and pairing audit of Chapter 12 prove part (f). $\square$

### 13.3 Hypothesis and failure ledger

| Conclusion | Necessary input | Failure if omitted |
|---|---|---|
| ordinary cohomology has no boundary term | anisotropy and projectivity | Eisenstein and boundary cohomology can enter |
| a genuine Galois action on the selected space | Galois-stable component union | one geometric component may live over a larger field |
| correct packet label | full central equation and auxiliary character | distinct lifts are merged |
| automorphic multiplicity one | quaternionic multiplicity one plus central eigenspaces | compactness alone gives only finite multiplicity |
| exact cohomological dimension | level invariants and orientation factor retained | multiplicity, oldvectors, and Hodge signs are conflated |
| exhaustion of constant $H^2$ | both active archimedean calculations | higher weights or one-active-factor terms are falsely admitted |
| rational packet projector | fixed-level finiteness and separating Hecke data | an infinite or nonalgebraic projector is used |
| integral splitting | denominators prime to $\ell$ and saturation | a rational summand need not split the lattice |
| unramified pure realization | good PEL integral model and $u\nmid\ell$ | nearby cycles or ramification replace smooth specialization |
| Frobenius polynomial independent of $\ell$ | algebraic correspondences and projected trace formula | dimension alone gives no compatible polynomial |
| correct duality | geometric Frobenius and $\mathbf Q_\ell(1)$ conventions | the reciprocal factor becomes $q^{-2}$ instead of $q^2$ |
| semistable local type | verified local model, regularization, and finite descent | incidence data or inertia can be wrong |
| comparison with curve cohomology | common quaternionic packet only | equal Hecke eigenvalues are mistaken for equal Galois spaces |

### 13.4 Conclusion

The auxiliary unitary surface now performs the task for which it was constructed. Its two noncompact real directions each contribute one rank-one cohomological degree; their product lands in the self-dual middle degree. Compactness removes geometric boundary terms, while the compact Matsushima formula turns every harmonic middle class into either an invariant character class or a parallel-weight-two automorphic packet. The archimedean sign calculation explains the four lines of a full packet and their Hodge numbers $1,2,1$.

Finite-adelic matching labels these packets by quaternionic representations. Multiplicity one counts one automorphic occurrence; level invariants and orientation signs account separately for the actual dimension. Good Hecke operators, central data, and component operators isolate each packet by an algebraic correspondence. Their projectors descend the complex decomposition to rational Betti, de Rham, and étale structures, and the canonical model turns the étale block into a continuous Galois representation.

At good primes, smooth proper base change identifies this representation with special-fiber cohomology. Projected Lefschetz traces determine its Frobenius polynomial, and surface purity places every root on the circle of radius $q$. At semistable primes, the same projector carries the restriction--Gysin complex, finite inertia, and monodromy into the packet. Thus Hecke, Galois, Frobenius, duality, and monodromy act on one and the same degree-two object.

The comparison with curves is now exact in its proper sense. Curve $H^1$ and surface $H^2$ share the quaternionic label, Hecke field, eigencharacter, and conjugation law, but their weights, pairing twists, dimensions, and local incidence geometries differ. The surface block is not disguised curve cohomology and admits no half Tate twist. It is the honest weight-two cohomological carrier from which subsequent descent may extract rank-two arithmetic data.
