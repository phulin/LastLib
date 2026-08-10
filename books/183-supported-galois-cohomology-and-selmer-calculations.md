# Supported Galois Cohomology and Selmer Calculations

## Contents

- [1. The supported global problem](#1-the-supported-global-problem)
  - [1.1 Why ordinary global cohomology is too large](#11-why-ordinary-global-cohomology-is-too-large)
  - [1.2 The hardly-ramified residual representation](#12-the-hardly-ramified-residual-representation)
  - [1.3 Coefficients, duals, and conventions](#13-coefficients-duals-and-conventions)
  - [1.4 The three local conditions](#14-the-three-local-conditions)
  - [1.5 The calculation to be proved](#15-the-calculation-to-be-proved)
- [2. Finite local cohomology at the distinguished places](#2-finite-local-cohomology-at-the-distinguished-places)
  - [2.1 Why every local term must be recalculated](#21-why-every-local-term-must-be-recalculated)
  - [2.2 The tame-quadratic place at $2$](#22-the-tame-quadratic-place-at-2)
  - [2.3 The coefficient-prime place](#23-the-coefficient-prime-place)
  - [2.4 The real place](#24-the-real-place)
  - [2.5 Global invariant groups](#25-global-invariant-groups)
- [3. Finite and singular local conditions](#3-finite-and-singular-local-conditions)
  - [3.1 The problem solved by finite local cohomology](#31-the-problem-solved-by-finite-local-cohomology)
  - [3.2 The primal finite subspaces](#32-the-primal-finite-subspaces)
  - [3.3 Exact orthogonals and dual finite subspaces](#33-exact-orthogonals-and-dual-finite-subspaces)
  - [3.4 Local dimension ledgers](#34-local-dimension-ledgers)
  - [3.5 Why unramified and finite-flat are different](#35-why-unramified-and-finite-flat-are-different)
- [4. Cochain models for local conditions](#4-cochain-models-for-local-conditions)
  - [4.1 Why a subspace of $H^1$ is not yet a complex](#41-why-a-subspace-of-h1-is-not-yet-a-complex)
  - [4.2 The positive local-condition complex](#42-the-positive-local-condition-complex)
  - [4.3 The local quotient complex](#43-the-local-quotient-complex)
  - [4.4 Independence of representatives](#44-independence-of-representatives)
  - [4.5 Orthogonal local complexes](#45-orthogonal-local-complexes)
- [5. The supported global cochain complex](#5-the-supported-global-cochain-complex)
  - [5.1 Mapping fibers impose support](#51-mapping-fibers-impose-support)
  - [5.2 Definition and differential](#52-definition-and-differential)
  - [5.3 The localization long exact sequence](#53-the-localization-long-exact-sequence)
  - [5.4 Degree one is the hardly-ramified Selmer group](#54-degree-one-is-the-hardly-ramified-selmer-group)
  - [5.5 Degree two is the supported obstruction group](#55-degree-two-is-the-supported-obstruction-group)
- [6. Comparison with compact support](#6-comparison-with-compact-support)
  - [6.1 Compact support as zero boundary data](#61-compact-support-as-zero-boundary-data)
  - [6.2 The comparison triangle](#62-the-comparison-triangle)
  - [6.3 Low-degree consequences](#63-low-degree-consequences)
  - [6.4 Enlarging the controlling set](#64-enlarging-the-controlling-set)
- [7. Duality for supported cohomology](#7-duality-for-supported-cohomology)
  - [7.1 The dual Selmer structure](#71-the-dual-selmer-structure)
  - [7.2 Construction of the global pairing](#72-construction-of-the-global-pairing)
  - [7.3 Perfectness](#73-perfectness)
  - [7.4 The decisive degrees](#74-the-decisive-degrees)
  - [7.5 What duality does not assert](#75-what-duality-does-not-assert)
- [8. Exact sequences for supported Selmer groups](#8-exact-sequences-for-supported-selmer-groups)
  - [8.1 The supported Poitou--Tate sequence](#81-the-supported-poitou--tate-sequence)
  - [8.2 Localization defects](#82-localization-defects)
  - [8.3 Changing local conditions](#83-changing-local-conditions)
  - [8.4 Strict and relaxed structures](#84-strict-and-relaxed-structures)
- [9. The Greenberg--Wiles identity](#9-the-greenberg--wiles-identity)
  - [9.1 Statement with all archimedean terms](#91-statement-with-all-archimedean-terms)
  - [9.2 Proof from the exact sequence](#92-proof-from-the-exact-sequence)
  - [9.3 The supported Euler identity and inequality](#93-the-supported-euler-identity-and-inequality)
  - [9.4 A bookkeeping table](#94-a-bookkeeping-table)
- [10. The hardly-ramified Selmer calculation](#10-the-hardly-ramified-selmer-calculation)
  - [10.1 The Selmer structures](#101-the-selmer-structures)
  - [10.2 The prime $2$](#102-the-prime-2)
  - [10.3 The coefficient prime](#103-the-coefficient-prime)
  - [10.4 The real place and global invariants](#104-the-real-place-and-global-invariants)
  - [10.5 Exact balance](#105-exact-balance)
- [11. Consequences and exceptional cases](#11-consequences-and-exceptional-cases)
  - [11.1 Tangents, supported obstructions, and relation bounds](#111-tangents-supported-obstructions-and-relation-bounds)
  - [11.2 Local smoothness does not imply global smoothness](#112-local-smoothness-does-not-imply-global-smoothness)
  - [11.3 Scalar and reducible local restrictions](#113-scalar-and-reducible-local-restrictions)
  - [11.4 The exceptional primes $2$, $3$, and $5$](#114-the-exceptional-primes-2-3-and-5)
  - [11.5 Changes of coefficients and controlling sets](#115-changes-of-coefficients-and-controlling-sets)
- [12. The supported-cohomology theorem package](#12-the-supported-cohomology-theorem-package)
  - [12.1 Main theorem](#121-main-theorem)
  - [12.2 Dependency and hypothesis ledger](#122-dependency-and-hypothesis-ledger)
  - [12.3 A reusable calculation protocol](#123-a-reusable-calculation-protocol)
  - [12.4 Conclusion](#124-conclusion)

## 1. The supported global problem

The local conditions of the hardly-ramified deformation problem have already been constructed as honest deformation conditions. The next question is global and linear: how many global first-order classes survive those local restrictions, and how large is the cohomological space in which their global lifting obstructions live? This chapter fixes the data and explains why both questions are answered by one supported complex.

### 1.1 Why ordinary global cohomology is too large

Let $S$ be a finite set of places of a number field and let $M$ be a finite Galois module. The group $H^1(G_{K,S},M)$ permits every first-order class unramified outside $S$. A deformation problem almost never permits all those classes at the places inside $S$. It may require a class to vanish at one place, to arise from a finite-flat self-extension at another, and to preserve a real conjugacy class at infinity.

A kernel imposes those degree-one restrictions:

$$
H^1_{\mathcal L}(K,M)
=\ker\left(
H^1(G_{K,S},M)\longrightarrow
\bigoplus_{v\in S}H^1(K_v,M)/L_v
\right). \tag{1.1}
$$

But the kernel alone is not enough for obstruction theory. A global degree-two class can vanish locally while a family of admissible local lifts still fails to glue, and a global lift can exist while its local restrictions fail to lie in the required local torsors. Those two defects occupy adjacent positions in a localization sequence. A cochain complex, rather than a single kernel, is needed to retain both.

The word **supported** will mean that a global cochain is equipped with local data placing it inside the chosen local conditions. Strict compact support is the special case in which no local direction is allowed. General supported cohomology enlarges compact support by precisely the permitted local directions.

This distinction is easy to see in degree one. A strictly supported class is locally trivial. A hardly-ramified class need not be locally trivial at $\ell$; it may move through the finite-flat tangent subspace. Treating the finite-flat subspace as zero would remove genuine deformations, while treating it as the whole local group would admit the valuation direction that finite flatness excludes.

### 1.2 The hardly-ramified residual representation

Fix a prime

$$
\ell\geq 7,
$$

a finite extension $E/\mathbf Q_\ell$ with ring of integers $\mathcal O$, uniformizer $\varpi$, and residue field $k$. Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k) \tag{1.2}
$$

be continuous and satisfy the following hypotheses.

1. The determinant is the residual cyclotomic character:
   $$
   \det\bar\rho=\bar\chi_\ell.
   $$
2. The representation is absolutely irreducible.
3. It is odd.
4. It is unramified outside $\{2,\ell\}$.
5. Its restriction at $2$ has the tame-quadratic order-three type.
6. Its restriction at $\ell$ is the generic fiber of a coefficient-linear finite-flat group over $\mathbf Z_\ell$.

Put

$$
S=\{2,\ell,\infty\},
\qquad
G_{\mathbf Q,S}=\operatorname{Gal}(\mathbf Q_S/\mathbf Q), \tag{1.3}
$$

where $\mathbf Q_S$ is the maximal extension unramified at every finite prime outside $S$. The coefficient module for fixed-determinant deformations is

$$
M=\operatorname{ad}^0\bar\rho. \tag{1.4}
$$

Because $\ell$ is odd, trace splits the full adjoint:

$$
\operatorname{ad}\bar\rho=kI\oplus M. \tag{1.5}
$$

The trace form $(X,Y)\mapsto\operatorname{tr}(XY)$ is perfect on $M$. Consequently the Tate dual is

$$
M'=M^*(1)\simeq M(1). \tag{1.6}
$$

Every simplified formula below uses both the oddness of $\ell$ and the rank-two trace splitting. In characteristic two, the identity matrix is trace zero and (1.5)--(1.6) do not have this form.

### 1.3 Coefficients, duals, and conventions

All cohomology groups with coefficient $M$ or $M'$ are continuous cohomology of finite discrete $k$-modules. We write

$$
h^i_v(N)=\dim_kH^i(\mathbf Q_v,N),
\qquad
h^i(N)=\dim_kH^i(G_{\mathbf Q,S},N). \tag{1.7}
$$

At a finite place, local Tate duality gives a perfect pairing

$$
H^i(\mathbf Q_v,M)\times H^{2-i}(\mathbf Q_v,M')
\longrightarrow k. \tag{1.8}
$$

One obtains a $k$-valued pairing by composing the canonical invariant-valued pairing with a fixed nonzero trace character of $k$. Orthogonal subspaces do not depend on that choice.

Arithmetic Frobenius is used throughout. At $p\ne\ell$ it acts on the residual cyclotomic line by multiplication by $p$. Thus at $2$ the twist in (1.6) multiplies a Frobenius eigenvalue by $2$, not by $2^{-1}$.

At the real place, degree-one cohomology is ordinary cohomology. Since $\ell$ is odd, all positive-degree cohomology of $G_{\mathbf R}\simeq C_2$ vanishes. Compactly supported and global duality statements nevertheless retain the real place: modified local cohomology uses the complete Tate complex, and the Greenberg--Wiles formula contains the ordinary invariant group $H^0(\mathbf R,M)$.

We use two related dualities and keep their degree shifts distinct:

$$
H^i(\mathbf Q_v,M)
\quad\text{pairs with}\quad
H^{2-i}(\mathbf Q_v,M'), \tag{1.9}
$$

while

$$
H_c^i(G_{\mathbf Q,S},M)
\quad\text{pairs with}\quad
H^{3-i}(G_{\mathbf Q,S},M'). \tag{1.10}
$$

The extra shift in (1.10) is produced by the mapping cone of localization.

### 1.4 The three local conditions

At $2$, let

$$
L_2=0\subseteq H^1(\mathbf Q_2,M). \tag{1.11}
$$

This is the tangent of the fixed-determinant tame-quadratic condition. In fact the ambient group $H^1(\mathbf Q_2,M)$ is already zero, but retaining the notation $L_2$ records which local deformation condition is being imposed.

At $\ell$, let

$$
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)
\subseteq H^1(\mathbf Q_\ell,M). \tag{1.12}
$$

This is the space of self-extension classes that arise from coefficient-linear finite-flat models with fixed cyclotomic determinant. It is not the unramified subgroup.

At infinity, oddness is rigid for odd $\ell$, so

$$
L_\infty=0=H^1(\mathbf R,M). \tag{1.13}
$$

The resulting Selmer structure is denoted $\mathcal L^{\mathrm{hr}}$. Its degree-one group is

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\left(
H^1(G_{\mathbf Q,S},M)
\longrightarrow
H^1(\mathbf Q_2,M)
\oplus
\frac{H^1(\mathbf Q_\ell,M)}{H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)}
\right). \tag{1.14}
$$

The real quotient is zero in degree one, but infinity remains part of the structure and of every global formula.

For each place, define the exact Tate orthogonal

$$
L_v^\perp
=\{y\in H^1(\mathbf Q_v,M'):
\langle x,y\rangle_v=0\text{ for every }x\in L_v\}. \tag{1.15}
$$

The dual Selmer group is

$$
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=H^1_{(\mathcal L^{\mathrm{hr}})^\perp}(\mathbf Q,M'). \tag{1.16}
$$

The notation does not claim that (1.14) and (1.16) pair directly. Global reciprocity makes the evident sum of local pairings on two global classes zero. Their relation is instead mediated by supported degree two.

### 1.5 The calculation to be proved

The local and global inputs predict a cancellation:

$$
\begin{array}{c|c}
\text{place}&\dim L_v-h^0_v(M)\\ \hline
2&0\\
\ell&+1\\
\infty&-1.
\end{array} \tag{1.17}
$$

Absolute irreducibility gives $H^0(\mathbf Q,M)=0$. The local calculation at $2$ gives $H^0(\mathbf Q_2,M')=0$, so restriction forces $H^0(\mathbf Q,M')=0$. The Greenberg--Wiles identity should therefore give

$$
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M'). \tag{1.18}
$$

Supported duality will identify the right side with the dual of a supported degree-two group:

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*. \tag{1.19}
$$

Combining (1.18) and (1.19) gives

$$
\boxed{
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M).} \tag{1.20}
$$

In particular, either side is no larger than the other. The equality is stronger than the dimension inequality needed in a balanced presentation. The rest of the book constructs the group on the right and proves every step leading to (1.20).

## 2. Finite local cohomology at the distinguished places

Before constructing global complexes, we calculate the local vector spaces that will enter them. This order is essential: local conditions are not interchangeable labels, and the final global cancellation depends on one exact dimension at each of three very different places.

### 2.1 Why every local term must be recalculated

The expression

$$
\dim L_v-h^0_v(M) \tag{2.1}
$$

is the normalized local correction in the Greenberg--Wiles formula. Its two terms answer different questions. The dimension of $L_v$ counts permitted first-order deformations. The invariant dimension counts infinitesimal automorphisms visible locally. A condition can be formally smooth and still have a nonzero correction, and a rigid condition can have a nonzero invariant correction.

The three places in $S$ illustrate all possibilities. At $2$, both terms vanish. At $\ell$, the finite-flat tangent has one more dimension than the trace-zero local centralizer. At infinity, there is no tangent but there is a one-dimensional invariant line. The coefficient-prime and real contributions cancel only because the determinant, weight, and oddness hypotheses have exactly the forms stated in Chapter 1.

### 2.2 The tame-quadratic place at $2$

Let $T$ be the residual order-three inertia operator. Its characteristic polynomial is

$$
X^2+X+1,
$$

and arithmetic Frobenius interchanges its two nontrivial characters. The trace-zero inertia centralizer is a line $kH$, on which Frobenius acts by $-1$.

Here is the matrix calculation. After extending scalars if necessary, choose a primitive cube root $\zeta$ and a basis in which

$$
T=\begin{pmatrix}\zeta&0\\0&\zeta^{-1}\end{pmatrix},
\qquad
\Phi=\begin{pmatrix}0&a\\b&0\end{pmatrix}, \tag{2.2a}
$$

with $a,b\ne0$. The relation $\Phi T\Phi^{-1}=T^{-1}$ expresses the arithmetic-Frobenius action on tame inertia. In the usual basis

$$
H=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
E=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
F=\begin{pmatrix}0&0\\1&0\end{pmatrix} \tag{2.2b}
$$

of trace-zero endomorphisms, conjugation by $T$ fixes $H$ and multiplies $E$ and $F$ by $\zeta^2$ and $\zeta$, respectively. Thus the inertia invariants are exactly the line spanned by $H$. Direct multiplication gives $\Phi H\Phi^{-1}=-H$. Both the invariant line and the eigenvalue descend to $k$, so the conclusion does not require $\zeta\in k$.

It follows first that

$$
H^0(\mathbf Q_2,M)=0. \tag{2.2}
$$

Indeed a decomposition-group invariant must lie in $kH$ and be fixed by Frobenius, but $-1\ne1$ because $\ell$ is odd.

The tangent to a fixed prime-to-$\ell$ inertial type is unramified cohomology:

$$
H^1_{\mathrm{ur}}(\mathbf Q_2,M)
\simeq M^{I_2}/(\phi-1)M^{I_2}. \tag{2.3}
$$

On $kH$, the endomorphism $\phi-1$ is multiplication by $-2$, hence invertible. Thus

$$
L_2=H^1_{\mathrm{ur}}(\mathbf Q_2,M)=0. \tag{2.4}
$$

We also need the ambient local group, not just the tangent subspace. Local duality gives

$$
h^2_2(M)=h^0_2(M'). \tag{2.5}
$$

The twist multiplies the Frobenius eigenvalue $-1$ on $kH$ by $2$, so Frobenius acts on $M'^{I_2}$ by $-2$. An invariant would require $-2=1$ in $k$, which occurs only in characteristic $3$. Since $\ell\ge7$,

$$
H^0(\mathbf Q_2,M')=0,
\qquad
H^2(\mathbf Q_2,M)=0. \tag{2.6}
$$

The local Euler characteristic is zero because $2\ne\ell$:

$$
h^0_2(M)-h^1_2(M)+h^2_2(M)=0. \tag{2.7}
$$

Equations (2.2), (2.6), and (2.7) give

$$
H^1(\mathbf Q_2,M)=0. \tag{2.8}
$$

Applying middle-degree local duality also gives

$$
H^1(\mathbf Q_2,M')=0. \tag{2.9}
$$

Therefore the strict, relaxed, and tame-quadratic degree-one conditions all have the same zero underlying space at $2$. They remain conceptually different deformation conditions, but finite local cohomology cannot distinguish them in this residual range.

The normalized correction is

$$
\dim L_2-h^0_2(M)=0. \tag{2.10}
$$

### 2.3 The coefficient-prime place

Let

$$
h_\ell=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V). \tag{2.11}
$$

Because $2$ is invertible, the local endomorphism algebra splits into scalars and trace zero. Hence

$$
h^0_\ell(M)=h_\ell-1. \tag{2.12}
$$

The finite-flat tangent calculation over the unramified field $\mathbf Q_\ell$ has local degree $f=1$. It gives

$$
\dim_kL_\ell
=\dim_kH^1_{\mathrm{fl}}(\mathbf Q_\ell,M)
=h_\ell. \tag{2.13}
$$

Subtracting (2.12) from (2.13) yields the stable correction

$$
\dim_kL_\ell-h^0_\ell(M)=1. \tag{2.14}
$$

This remains true when the local residual representation splits. In the local Schur case $h_\ell=1$, both sides of (2.13) and (2.12) are $1$ and $0$. For a split sum of distinct characters, $h_\ell=2$, and both dimensions rise by one. The difference remains one. Thus no scalar-centralizer hypothesis at $\ell$ is needed for the global numerical calculation.

The ambient local group is larger than $L_\ell$. The mixed-characteristic local Euler formula gives

$$
h^1_\ell(M)
=h^0_\ell(M)+h^0_\ell(M')+\dim_kM. \tag{2.15}
$$

Since $\dim_kM=3$,

$$
h^1_\ell(M)=h_\ell+2+h^0_\ell(M'). \tag{2.16}
$$

The quotient by the finite-flat condition therefore has dimension

$$
\dim_k\frac{H^1(\mathbf Q_\ell,M)}{L_\ell}
=h^0_\ell(M')+2. \tag{2.17}
$$

Equation (2.17) will be the dimension of the exact orthogonal $L_\ell^\perp$. It is not generally one. The two permanent extra directions are the part of the three-dimensional $\ell$-adic bulk not used by the one normalized finite-flat correction.

### 2.4 The real place

Oddness means that complex conjugation has eigenvalues $1$ and $-1$ on the residual two-dimensional space. On trace-zero endomorphisms, conjugation fixes the diagonal trace-zero line and negates the two off-diagonal lines. Therefore

$$
h^0_\infty(M)=1. \tag{2.18}
$$

Because $\ell$ is odd, averaging by the group $C_2$ makes its positive-degree cohomology vanish:

$$
H^i(\mathbf R,M)=0
\qquad(i>0). \tag{2.19}
$$

In particular,

$$
L_\infty=0
\quad\text{and}\quad
\dim L_\infty-h^0_\infty(M)=-1. \tag{2.20}
$$

The vanishing of real $H^1$ does not make the real place irrelevant. The negative term in (2.20) is the exact counterpart of the positive finite-flat term (2.14). Omitting infinity changes a balanced calculation into a false one-dimensional excess.

The same averaging argument gives vanishing of all modified real groups, because the complete Tate complex of a finite group is acyclic when its order is invertible on the coefficient module. Thus the real place contributes nothing to the local packages in the Poitou--Tate sequence, while still contributing ordinary $H^0$ to the Euler formula. Those two statements are compatible, not contradictory.

### 2.5 Global invariant groups

Absolute irreducibility gives

$$
\operatorname{End}_{k[G_{\mathbf Q}]}(\bar V)=kI.
$$

Taking trace zero and using $\ell\ne2$ yields

$$
H^0(G_{\mathbf Q,S},M)=0. \tag{2.21}
$$

The dual invariant group also vanishes, for a different reason. Restriction of invariants is injective:

$$
H^0(G_{\mathbf Q,S},M')
\hookrightarrow H^0(\mathbf Q_2,M'). \tag{2.22}
$$

The target is zero by (2.6). Hence

$$
H^0(G_{\mathbf Q,S},M')=0. \tag{2.23}
$$

This proof is stronger than imposing a separate no-self-twist hypothesis. The distinguished local type at $2$ itself excludes a global cyclotomic adjoint invariant in characteristic at least $7$. The same argument would fail in characteristic $3$, exactly where the local Frobenius eigenvalue $-2$ becomes $1$.

Combining the calculations gives the complete normalized ledger:

$$
\begin{array}{c|c|c|c}
v&\dim L_v&h^0_v(M)&\dim L_v-h^0_v(M)\\ \hline
2&0&0&0\\
\ell&h_\ell&h_\ell-1&1\\
\infty&0&1&-1.
\end{array} \tag{2.24}
$$

Both global invariant dimensions are zero. No other term will survive in the Greenberg--Wiles formula.

## 3. Finite and singular local conditions

The local calculations now have to be organized into dual pairs. The terminology “finite” and “singular” is useful because it separates permitted local classes from the quotient that measures failure of the local condition. At the coefficient prime, however, the finite condition is integral rather than unramified, and its dual must be defined by exact orthogonality.

### 3.1 The problem solved by finite local cohomology

For a finite place $v$, a local condition is a subspace

$$
L_v\subseteq H^1(\mathbf Q_v,M).
$$

Define

$$
H^1_f(\mathbf Q_v,M)=L_v,
\qquad
H^1_s(\mathbf Q_v,M)=H^1(\mathbf Q_v,M)/L_v. \tag{3.1}
$$

The subscripts stand for **finite** and **singular**. They do not refer to cardinality; every group here is already finite. The finite group contains locally permitted classes, while the singular quotient records the local defect of an arbitrary class.

For the hardly-ramified structure,

$$
H^1_f(\mathbf Q_2,M)=0,
\qquad
H^1_f(\mathbf Q_\ell,M)=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M). \tag{3.2}
$$

At primes outside $S$, the built-in condition is unramified:

$$
H^1_f(\mathbf Q_p,M)=H^1_{\mathrm{ur}}(\mathbf Q_p,M)
\qquad(p\notin S). \tag{3.3}
$$

At infinity, the degree-one group is zero and hence so are its finite and singular parts.

The point of (3.1) is global. Localization followed by the singular quotient is the map whose kernel is the Selmer group. A supported cochain complex must realize this quotient in degree one while retaining degree-two local obstructions in the next degree.

### 3.2 The primal finite subspaces

At a finite prime $p\notin S$, the representation is unramified and $p\ne\ell$. Inflation from the residue quotient gives

$$
H^1_f(\mathbf Q_p,M)
=M/(\operatorname{Frob}_p-1)M. \tag{3.4}
$$

Kernel--cokernel equality for the Frobenius endomorphism gives

$$
\dim H^1_f(\mathbf Q_p,M)=h^0_p(M). \tag{3.5}
$$

Thus an unramified condition contributes zero to the normalized local sum. This is why adding a harmless prime to the controlling set does not change the final formula.

At $2$, the coefficient module is ramified, so formula (3.4) must use inertia invariants. The resulting group nevertheless vanishes by (2.3)--(2.4). It would be wrong to justify that vanishing by calling the coefficient unramified; the coefficient is not unramified.

At $\ell$, the finite subspace is defined through exact finite-flat self-extensions. Its construction remembers a marked integral model and a Hodge line. It has dimension $h_\ell$ by (2.13). No inertia-kernel description is asserted.

### 3.3 Exact orthogonals and dual finite subspaces

Local Tate duality gives a perfect pairing

$$
H^1(\mathbf Q_v,M)\times H^1(\mathbf Q_v,M')\longrightarrow k. \tag{3.6}
$$

Define the dual finite condition by

$$
H^1_f(\mathbf Q_v,M')=L_v^\perp. \tag{3.7}
$$

This definition is canonical. It does not guess a geometric condition on $M'$ and it does not rely on a dimension count. Perfectness gives

$$
\dim L_v^\perp
=h^1_v(M)-\dim L_v. \tag{3.8}
$$

It also produces perfect quotient--subspace pairings

$$
H^1_s(\mathbf Q_v,M)\times H^1_f(\mathbf Q_v,M')
\longrightarrow k, \tag{3.9}
$$

and

$$
H^1_f(\mathbf Q_v,M)\times H^1_s(\mathbf Q_v,M')
\longrightarrow k. \tag{3.10}
$$

To prove (3.9), pair a representative of a singular class with an element of $L_v^\perp$. Changing the representative by $L_v$ changes the value by zero. If a singular class pairs trivially with all of $L_v^\perp$, biduality puts its representative in $(L_v^\perp)^\perp=L_v$, so the singular class is zero. Equality of dimensions proves perfectness. The proof of (3.10) is identical with the variables exchanged.

At a prime $p\notin S$, the unramified conditions on $M$ and $M'$ are exact orthogonals. Containment follows because the cup product of two unramified degree-one classes inflates from the residue-field Galois group, whose cohomological dimension is one. Equality follows from (3.5), local Euler characteristic zero, and local duality.

At $\ell$, we use (3.7) as the definition of the dual finite condition. Finite-flat self-extensions on the primal side are known integrally, but the abstract module $M'$ need not carry a finite-flat deformation interpretation of the same form. Calling the orthogonal “finite flat” without constructing the corresponding integral models would add an unproved assertion.

### 3.4 Local dimension ledgers

At $2$, (2.8)--(2.9) imply

$$
L_2=0,
\qquad
L_2^\perp=0. \tag{3.11}
$$

The strict and relaxed orthogonal identities are still correct: the full ambient group happens to be zero.

At $\ell$, equations (2.16), (2.13), and (3.8) give

$$
\dim L_\ell^\perp
=h^0_\ell(M')+2. \tag{3.12}
$$

The normalized dual local correction is therefore

$$
\dim L_\ell^\perp-h^0_\ell(M')=2. \tag{3.13}
$$

The primal and dual corrections add to the full local $\ell$-adic bulk:

$$
\bigl(\dim L_\ell-h^0_\ell(M)\bigr)
+\bigl(\dim L_\ell^\perp-h^0_\ell(M')\bigr)
=3. \tag{3.14}
$$

This is the rank-three instance of the local correction identity. It is an exact check on every dimension: the finite-flat condition uses one normalized direction and its orthogonal uses the remaining two.

At infinity, both degree-one groups vanish, so

$$
L_\infty=L_\infty^\perp=0. \tag{3.15}
$$

The ordinary invariant dimensions need not agree, but modified local duality is acyclic because $2$ is invertible.

The complete degree-one ledger is

$$
\begin{array}{c|c|c|c}
v&h^1_v(M)&\dim L_v&\dim L_v^\perp\\ \hline
2&0&0&0\\
\ell&h_\ell+2+h^0_\ell(M')&h_\ell&h^0_\ell(M')+2\\
\infty&0&0&0.
\end{array} \tag{3.16}
$$

### 3.5 Why unramified and finite-flat are different

The distinction is visible in the simplest ordinary extension. Suppose locally at $\ell$ that the residual representation contains an extension

$$
0\longrightarrow k(1)\longrightarrow V\longrightarrow k\longrightarrow0.
$$

Kummer theory identifies the ambient extension group with

$$
H^1(\mathbf Q_\ell,k(1))
\simeq \mathbf Q_\ell^\times/\mathbf Q_\ell^{\times\ell}\otimes_{\mathbf F_\ell}k. \tag{3.17}
$$

The valuation of $\ell$ gives one class, while units give the finite-flat classes. Principal units generally define ramified field extensions, so finite flat does not mean unramified. What finite flatness excludes is the valuation direction.

This example also explains the size of the dual orthogonal. The local Tate pairing is a perfect pairing on the whole Kummer and character groups. Annihilating the unit subspace imposes a condition on the dual character, but it does not force the dual character to be unramified in every coefficient module arising inside $M'$. The exact orthogonal, not a slogan, is the stable object.

The global hardly-ramified calculation consequently uses three distinct ideas:

$$
\begin{array}{c|c}
2&\text{a fixed tame type with zero tangent},\\
\ell&\text{an integral finite-flat subspace},\\
p\notin S&\text{the unramified subspace}.
\end{array}
$$

They fit one Selmer formalism because each is a subspace of local $H^1$, not because their arithmetic meanings coincide.

## 4. Cochain models for local conditions

A Selmer group can be defined from subspaces of cohomology, but supported duality acts on complexes. We therefore replace each $L_v\subseteq H^1(\mathbf Q_v,M)$ by a small cochain complex whose first cohomology is exactly $L_v$. Over the coefficient field $k$ this can be done directly and transparently.

### 4.1 Why a subspace of $H^1$ is not yet a complex

Let

$$
C_v^\bullet(M)=C^\bullet(G_{\mathbf Q_v},M)
$$

be the continuous inhomogeneous cochain complex at a finite place. A class in $L_v$ is an equivalence class of cocycles, not a specified cocycle. If one arbitrarily chooses one representative for each class, the resulting set need not be closed under differentials or coefficient changes. A mapping cone built from such representatives would depend on those choices.

The correct construction takes every cocycle whose class lies in $L_v$. Write

$$
Z^1_v(M)=\ker\bigl(d:C_v^1(M)\to C_v^2(M)\bigr),
$$

$$
B^1_v(M)=dC_v^0(M),
$$

and let

$$
Z^1_{L_v}(M)
=\{z\in Z^1_v(M):[z]\in L_v\}. \tag{4.1}
$$

Because $L_v$ is a vector subspace and contains zero,

$$
B^1_v(M)\subseteq Z^1_{L_v}(M). \tag{4.2}
$$

This inclusion is exactly what makes the next two-term complex possible.

### 4.2 The positive local-condition complex

For a finite place $v$, define

$$
U_v^+(M):
\quad
C_v^0(M)\xrightarrow{d}Z^1_{L_v}(M), \tag{4.3}
$$

placed in degrees $0$ and $1$. There are no terms in other degrees. The inclusion of degree zero and degree one gives a cochain map

$$
i_v:U_v^+(M)\longrightarrow C_v^\bullet(M). \tag{4.4}
$$

The cohomology is immediate:

$$
H^0(U_v^+(M))=H^0(\mathbf Q_v,M), \tag{4.5}
$$

$$
H^1(U_v^+(M))=Z^1_{L_v}(M)/B^1_v(M)=L_v, \tag{4.6}
$$

and

$$
H^i(U_v^+(M))=0
\qquad(i\ne0,1). \tag{4.7}
$$

Thus $U_v^+$ remembers local automorphisms in degree zero and allowed tangent classes in degree one, but it asserts no local obstruction group of its own. That is appropriate here: the conditions at $2$ and $\ell$ have already been proved liftable, so their constrained obstruction maps vanish. The ambient local $H^2$ remains in the quotient complex.

At a real place, use the complete Tate cochain complex $\widetilde C_v^\bullet(M)$. In the present odd-coefficient problem it is acyclic. We may take $U_\infty^+(M)=0$ without changing any supported cohomology group. This convention encodes the rigid degree-one condition and leaves the ordinary invariant correction to the global Euler formula. At a complex place both complexes are zero.

One may instead choose an acyclic positive complex at infinity. Any two such choices are quasi-isomorphic, and the supported complex below is unchanged up to quasi-isomorphism. The zero choice is the simplest in the present range.

### 4.3 The local quotient complex

Define the local singular or quotient complex by

$$
U_v^-(M)=\operatorname{Cone}
\bigl(U_v^+(M)\xrightarrow{i_v}C_v^\bullet(M)\bigr). \tag{4.8}
$$

We do not shift this cone. With the convention

$$
\operatorname{Cone}(i_v)^q=C_v^q(M)\oplus U_v^{+,q+1}(M),
$$

the associated triangle is

$$
U_v^+(M)\longrightarrow C_v^\bullet(M)
\longrightarrow U_v^-(M)
\longrightarrow U_v^+(M)[1]. \tag{4.9}
$$

The long exact sequence and (4.5)--(4.7) give

$$
H^0(U_v^-(M))=0, \tag{4.10}
$$

$$
H^1(U_v^-(M))
\simeq H^1(\mathbf Q_v,M)/L_v
=H^1_s(\mathbf Q_v,M), \tag{4.11}
$$

and

$$
H^2(U_v^-(M))
\simeq H^2(\mathbf Q_v,M). \tag{4.12}
$$

For $i\ge3$, the quotient cohomology agrees with local cohomology, hence vanishes for finite coefficients over a nonarchimedean local field. Therefore $U_v^-$ contains exactly the local information needed by a constrained global obstruction problem: the forbidden quotient in degree one and the ambient local obstruction in degree two.

The calculation of (4.11) deserves one explicit check. The relevant long exact segment is

$$
H^1(U_v^+)\longrightarrow H^1(C_v)
\longrightarrow H^1(U_v^-)
\longrightarrow H^2(U_v^+)=0.
$$

The first arrow is the inclusion $L_v\hookrightarrow H^1(\mathbf Q_v,M)$, so its cokernel is precisely the singular quotient.

### 4.4 Independence of representatives

The definition (4.1) is canonical, but later one may want a smaller finite-dimensional model quasi-isomorphic to $U_v^+$. Such a model requires choosing a linear section

$$
s_v:L_v\longrightarrow Z^1_{L_v}(M)
$$

of the quotient map. Then

$$
C_v^0(M)\xrightarrow{d}B^1_v(M)\oplus s_v(L_v)
$$

is a subcomplex quasi-isomorphic to $U_v^+$. A different section has the form

$$
s_v'(x)=s_v(x)+d a_v(x)
$$

for a linear map $a_v:L_v\to C_v^0(M)$ after choosing a complement to invariants. The map

$$
(m,s_v(x))\longmapsto(m-a_v(x),s_v'(x))
$$

is a cochain isomorphism up to the evident adjustment on the degree-zero complement. More invariantly, the two inclusions are cochain homotopic because their difference factors through boundaries.

It follows that every finite-dimensional replacement has the same mapping cone up to quasi-isomorphism. We will use the canonical possibly large complex (4.3) for definitions and finite-dimensional cohomology for all calculations. This keeps continuity and representative choices separate.

### 4.5 Orthogonal local complexes

Apply the same construction to $M'$ and the exact orthogonal $L_v^\perp$. Write

$$
U_v^+(M'):
C_v^0(M')\longrightarrow Z^1_{L_v^\perp}(M'). \tag{4.13}
$$

Local Tate duality and (3.9)--(3.10) imply that the quotient triangle for $M$ is dual to the positive triangle for $M'$ with complementary local degree two. On cohomology the essential perfect pairings are

$$
H^1(U_v^-(M))\times H^1(U_v^+(M'))\longrightarrow k, \tag{4.14}
$$

and

$$
H^2(U_v^-(M))\times H^0(U_v^+(M'))\longrightarrow k. \tag{4.15}
$$

The first is (3.9). The second is degree-two local duality. Degree zero of $U_v^-(M)$ vanishes, so there is no remaining term.

Consequently there is a quasi-isomorphism in the derived category of $k$-vector spaces,

$$
U_v^-(M)
\simeq
\operatorname{Hom}_k\bigl(U_v^+(M'),k\bigr)[-2]. \tag{4.16}
$$

Here $[-2]$ expresses local complementary degree two. To prove (4.16) without invoking a classification of complexes, use cup product on local cochains to define the map to the dual complex. The induced maps on $H^1$ and $H^2$ are (4.14)--(4.15), hence are isomorphisms. All other cohomology groups vanish. A cochain map inducing isomorphisms on every cohomology group is a quasi-isomorphism.

Equation (4.16) is the local mechanism behind supported duality. Exact orthogonality in degree one is not merely a numerical input; it makes the whole quotient complex dual to the permitted dual complex.

## 5. The supported global cochain complex

We now assemble the global cochains and the local quotient complexes. The construction is a mapping fiber, so its long exact sequence records both the Selmer kernel and the supported obstruction group. This is the precise cohomological object suggested by the tangent kernel of the hardly-ramified universal deformation problem.

### 5.1 Mapping fibers impose support

Let

$$
C_S^\bullet(M)=C^\bullet(G_{\mathbf Q,S},M). \tag{5.1}
$$

Localization and the quotient maps $C_v^\bullet(M)\to U_v^-(M)$ give a cochain map

$$
\lambda_{\mathcal L}:
C_S^\bullet(M)\longrightarrow
\bigoplus_{v\in S}U_v^-(M). \tag{5.2}
$$

At infinity the target is acyclic in the present odd-coefficient setting. We retain it formally so that the construction has the same set of places as global reciprocity.

A class should be supported by $\mathcal L$ when its image in every quotient complex is trivialized. Thus we take the mapping fiber of (5.2), not its cone without a shift.

### 5.2 Definition and differential

Define

$$
C_{\mathcal L}^\bullet(\mathbf Q,M)
=\operatorname{Cone}(\lambda_{\mathcal L})[-1]. \tag{5.3}
$$

If

$$
Q_{\mathcal L}^\bullet(M)
=\bigoplus_{v\in S}U_v^-(M),
$$

then explicitly

$$
C_{\mathcal L}^q(\mathbf Q,M)
=C_S^q(M)\oplus Q_{\mathcal L}^{q-1}(M), \tag{5.4}
$$

with differential

$$
d_{\mathcal L}(x,y)
=(dx,\lambda_{\mathcal L}(x)-dy). \tag{5.5}
$$

A direct calculation gives

$$
d_{\mathcal L}^2(x,y)
=(0,\lambda_{\mathcal L}(dx)-d\lambda_{\mathcal L}(x))=(0,0),
$$

because localization and the quotient maps are cochain maps.

Put

$$
H^i_{\mathcal L}(\mathbf Q,M)
=H^i\bigl(C_{\mathcal L}^\bullet(\mathbf Q,M)\bigr). \tag{5.6}
$$

For $\mathcal L=\mathcal L^{\mathrm{hr}}$ we abbreviate this to

$$
H^i_{\mathrm{hr}}(\mathbf Q,M). \tag{5.7}
$$

The definition is independent of geometric places: changing one conjugates the localization map, and conjugation on continuous cochains is cochain homotopic to the identity after transporting coefficients. Homotopic maps have canonically isomorphic mapping cones in cohomology.

### 5.3 The localization long exact sequence

The triangle

$$
C_{\mathcal L}^\bullet(\mathbf Q,M)
\longrightarrow C_S^\bullet(M)
\xrightarrow{\lambda_{\mathcal L}}Q_{\mathcal L}^\bullet(M)
\longrightarrow C_{\mathcal L}^\bullet(\mathbf Q,M)[1] \tag{5.8}
$$

gives the long exact sequence

$$
\cdots\longrightarrow
H^i_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^i(G_{\mathbf Q,S},M)
\longrightarrow H^i(Q_{\mathcal L}^\bullet(M))
\longrightarrow H^{i+1}_{\mathcal L}(\mathbf Q,M)
\longrightarrow\cdots. \tag{5.9}
$$

Using (4.10)--(4.12), the central part becomes

$$
\begin{aligned}
0\longrightarrow{}&H^1_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^1(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v\\
\longrightarrow{}&H^2_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M).
\end{aligned} \tag{5.10}
$$

The tilde records the real Tate modification, which is zero here. There is no zero asserted after the local degree-one quotient. Its cokernel maps into supported degree two. Likewise, supported degree two need not inject into global $H^2$; its kernel is the localization defect in degree one.

### 5.4 Degree one is the hardly-ramified Selmer group

Since $H^0(Q_{\mathcal L}^\bullet(M))=0$, exactness gives an injection

$$
H^1_{\mathcal L}(\mathbf Q,M)
\hookrightarrow H^1(G_{\mathbf Q,S},M). \tag{5.11}
$$

Its image is the kernel of the quotient localization map. Therefore

$$
H^1_{\mathcal L}(\mathbf Q,M)
=H^1_{\mathcal L}(\mathbf Q,M)_{\mathrm{Selmer}} \tag{5.12}
$$

with the right side understood in the kernel sense of (1.1). In particular,

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\left(
H^1(G_{\mathbf Q,S},M)
\longrightarrow
H^1(\mathbf Q_2,M)
\oplus
\frac{H^1(\mathbf Q_\ell,M)}{H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)}
\right). \tag{5.13}
$$

Thus supported degree one is canonically the tangent space of the hardly-ramified minimal global deformation functor. The complex has not changed the tangent problem; it has extended it into adjacent degrees.

### 5.5 Degree two is the supported obstruction group

Let

$$
\operatorname{loc}_{s}:
H^1(G_{\mathbf Q,S},M)
\longrightarrow
\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v \tag{5.14}
$$

be singular localization. From (5.10) there is a short exact sequence

$$
0\longrightarrow\operatorname{coker}(\operatorname{loc}_{s})
\longrightarrow H^2_{\mathcal L}(\mathbf Q,M)
\longrightarrow
\ker\left(
H^2(G_{\mathbf Q,S},M)
\to\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)
\right)
\longrightarrow0. \tag{5.15}
$$

The first term measures locally prescribed first-order corrections that do not arise from a global cohomology class. The last term measures global degree-two obstructions that vanish in every local ambient obstruction group. The supported group is an extension of these two terms, not a canonical direct sum.

This is exactly the shape of a constrained lifting problem. Suppose local admissible lifts exist over a small extension. Their differences from the restrictions of a provisional global lift define a family of local degree-one quotient classes. If that family is not globally adjustable, it contributes to the first term of (5.15). If it is adjustable, a remaining global factor-set obstruction can lie in the last term. Both defects vanish precisely when the supported obstruction class vanishes, provided the local lifting theories are complete and compatible.

At $2$ the local ambient $H^2$ is zero. At $\ell$ the finite-flat obstruction map is zero even though ambient $H^2$ may be nonzero. Thus (5.15) should not be simplified by deleting the $\ell$-adic ambient group. The supported complex keeps the ambient localization map while the positive local complex records that the constrained local condition itself is liftable.

## 6. Comparison with compact support

Compact support is the global localization cone with zero boundary data. Supported cohomology differs by the insertion of the permitted local complexes $U_v^+$. Comparing the two constructions explains both the terminology and the passage from Poitou--Tate duality to Selmer duality. Degree-zero local automorphisms make this comparison slightly subtler than simply setting every degree-one subspace equal to zero.

### 6.1 Compact support as zero boundary data

Let

$$
\widetilde C_{\mathrm{loc}}^\bullet(M)
=\bigoplus_{v\in S}\widetilde C^\bullet(\mathbf Q_v,M), \tag{6.1}
$$

where finite places use ordinary continuous cochains, the real place uses a complete Tate complex, and a complex place uses zero. Compactly supported cochains are

$$
C_c^\bullet(G_{\mathbf Q,S},M)
=\operatorname{Cone}\left(
C_S^\bullet(M)\to\widetilde C_{\mathrm{loc}}^\bullet(M)
\right)[-1]. \tag{6.2}
$$

This is the mapping fiber obtained when the entire positive boundary complex is zero. General $C_{\mathcal L}$ permits a local trivialization modulo the image of $U_v^+$, hence permits precisely $L_v$ in degree-one cohomology.

There is an important distinction between a zero positive complex and the canonical positive complex representing the zero subspace of $H^1$. The latter is

$$
C_v^0(M)\longrightarrow B_v^1(M), \tag{6.3}
$$

and has $H^0=H^0(\mathbf Q_v,M)$. It remembers local automorphisms so that supported degree one is exactly the strict Selmer kernel. The zero positive complex forgets those automorphisms and gives compact support. Thus compact support and strict Selmer cohomology agree only when the intervening degree-zero terms cause no discrepancy.

### 6.2 The comparison triangle

There is a natural triangle

$$
C_c^\bullet(G_{\mathbf Q,S},M)
\longrightarrow C_{\mathcal L}^\bullet(\mathbf Q,M)
\longrightarrow\bigoplus_{v\in S}U_v^+(M)
\longrightarrow C_c^\bullet(G_{\mathbf Q,S},M)[1]. \tag{6.4}
$$

To construct it, use the two descriptions

$$
C_{\mathcal L}^\bullet
=\operatorname{Cone}\left(
C_S^\bullet\oplus\bigoplus_vU_v^+
\xrightarrow{\operatorname{loc}-i}
\widetilde C_{\mathrm{loc}}^\bullet
\right)[-1] \tag{6.5}
$$

and (6.2). Setting the $U_v^+$ coordinate equal to zero embeds the compactly supported mapping fiber into (6.5). The quotient complex is the direct sum of the $U_v^+$. Taking the triangle associated with this short exact sequence gives (6.4).

The triangle makes the phrase “compact support plus permitted boundary values” exact. It also shows that supported cohomology is independent of a chosen presentation of the local condition complex: replacing $U_v^+$ by a quasi-isomorphic complex replaces every term in (6.4) by a quasi-isomorphic one.

### 6.3 Low-degree consequences

The long exact sequence of (6.4) contains

$$
\begin{aligned}
H^0(G_{\mathbf Q,S},M)&\longrightarrow
\bigoplus_vH^0(U_v^+(M))
\longrightarrow H_c^1(G_{\mathbf Q,S},M)\\
&\longrightarrow H^1_{\mathcal L}(\mathbf Q,M)
\longrightarrow\bigoplus_vL_v
\longrightarrow H_c^2(G_{\mathbf Q,S},M)\\
&\longrightarrow H^2_{\mathcal L}(\mathbf Q,M)
\longrightarrow0.
\end{aligned} \tag{6.6}
$$

The real term in the first direct sum must be interpreted through the chosen positive complex. In the odd-coefficient hardly-ramified problem that complex is zero at infinity, and the real invariant correction enters later through the global Euler determinant.

Sequence (6.6) is not usually the best way to compute $H^1_{\mathcal L}$, because the cone sequence (5.10) gives the kernel directly. Its value is conceptual: it compares the supported obstruction group with compactly supported cohomology, the object already known to have perfect global duality.

At the strict structure $L_v=0$ for all $v$, (6.6) becomes

$$
\operatorname{coker}\left(H^0(G_{\mathbf Q,S},M)\to
\bigoplus_vH^0(U_v^+(M))\right)
\longrightarrow H_c^1\longrightarrow H^1_{\mathcal L}\longrightarrow0. \tag{6.7}
$$

Thus strict supported degree one is compactly supported degree one modulo the local-automorphism boundary. If all the positive complexes are literally zero, then and only then the comparison triangle immediately identifies supported cohomology with compactly supported cohomology.

At the relaxed structure $L_v=H^1(\mathbf Q_v,M)$, the degree-one quotient in (5.10) vanishes, but degree-two local terms remain. Supported degree one is then full global $H^1$, while supported degree two maps into the kernel of global degree-two localization. Relaxing degree one does not erase local obstruction groups.

### 6.4 Enlarging the controlling set

Let $S'=S\cup\{p\}$ with $p\notin S$, and assume $M$ is unramified at $p$. The larger group $G_{\mathbf Q,S'}$ permits ramification at $p$. Give the new place the unramified condition

$$
L_p=H^1_{\mathrm{ur}}(\mathbf Q_p,M). \tag{6.8}
$$

Inflation identifies $H^1(G_{\mathbf Q,S},M)$ with the classes in $H^1(G_{\mathbf Q,S'},M)$ whose localization at $p$ lies in (6.8). Thus degree-one supported cohomology is unchanged.

The complex statement is stronger. The relative local complex at $p$ is the cone of unramified cochains

$$
C^\bullet(G_{\mathbf F_p},M)
\longrightarrow C^\bullet(\mathbf Q_p,M). \tag{6.9}
$$

It fits into the exact triangle comparing the two global restricted-ramification complexes. The positive unramified local complex cancels precisely this relative term. Therefore

$$
C_{\mathcal L,S}^\bullet(\mathbf Q,M)
\simeq C_{\mathcal L',S'}^\bullet(\mathbf Q,M) \tag{6.10}
$$

up to canonical quasi-isomorphism. All supported cohomology groups, not only the Selmer group, are independent of harmless enlargement.

On the dual side, unramified subspaces are exact orthogonals because $p\ne\ell$. Hence the same comparison holds for $M'$. This compatibility is necessary for supported duality to be independent of the chosen controlling set.

## 7. Duality for supported cohomology

Supported cohomology was designed so that a local condition and its exact orthogonal fit into global duality. This chapter proves that design principle. The result is stronger than a numerical equality: every supported cohomology group is paired perfectly with a complementary supported group for the Tate dual representation. The degree-two group on the deformation side is therefore the dual of the degree-one Selmer group on the dual side.

### 7.1 The dual Selmer structure

Recall that $M'=M^*(1)$. For each finite $v\in S$, local Tate duality gives a perfect pairing

$$
H^1(\mathbf Q_v,M)\times H^1(\mathbf Q_v,M')
\longrightarrow k. \tag{7.1}
$$

The orthogonal local condition is

$$
L_v^\perp=\{y\in H^1(\mathbf Q_v,M'): \langle x,y\rangle_v=0
\text{ for every }x\in L_v\}. \tag{7.2}
$$

At the real place we use complete cohomology. Because $\ell$ is odd, the order of the decomposition group is invertible in $k$, so every complete cohomology group is zero. Thus the zero complex is simultaneously the positive complex for the condition and its orthogonal. This is the reason infinity creates an Euler correction but no nonzero term in the supported localization cone.

Write

$$
\mathcal L^\perp=(L_v^\perp)_{v\in S}. \tag{7.3}
$$

The elementary dimension consequence of (7.1) is

$$
\dim L_v^\perp=h^1(\mathbf Q_v,M)-\dim L_v. \tag{7.4}
$$

This identity is useful but is not a substitute for orthogonality. The position of a subspace, not merely its dimension, determines the dual Selmer group.

**Lemma 7.1.** For every finite $v\in S$, the local quotient complex $U_v^-(M)$ is perfectly dual, with complementary degree $2$, to the positive complex $U_v^+(M')$ for $L_v^\perp$.

**Proof.** In degree one, the pairing induced by (7.1) is

$$
\frac{H^1(\mathbf Q_v,M)}{L_v}\times L_v^\perp\longrightarrow k. \tag{7.5}
$$

It is perfect. Indeed, the right kernel is zero by definition of the exact orthogonal. If a class $x$ on the left pairs trivially with $L_v^\perp$, then $x$ lies in $(L_v^\perp)^\perp=L_v$, since (7.1) is perfect and the spaces are finite-dimensional. Thus the left kernel is also zero. In complementary degrees, local Tate duality gives perfect pairings

$$
H^2(\mathbf Q_v,M)\times H^0(\mathbf Q_v,M')\longrightarrow k. \tag{7.6}
$$

The quotient complex has no degree-zero cohomology, while the positive complex has no degree-two cohomology. Equations (7.5) and (7.6) therefore pair all of their nonzero cohomology groups in complementary degrees. The cochain-level local invariant map realizes these pairings, and finite-dimensionality promotes the cohomological perfect pairing to the asserted dual quasi-isomorphism. $\square$

The last sentence uses a standard elementary fact: a morphism between bounded complexes of finite-dimensional vector spaces is a quasi-isomorphism exactly when it is an isomorphism on cohomology. Continuous cochain complexes may first be replaced by finite-dimensional complexes representing their finite cohomology, so no finiteness issue is hidden here.

### 7.2 Construction of the global pairing

Take representatives $a$ and $b$ in the two supported mapping fibers. Their global coordinates cup to a degree-three cochain with values in $k(1)$. Their local coordinates supply the boundary correction needed to make the sum of local invariants closed. The resulting pairing of complexes has the form

$$
C_{\mathcal L}^\bullet(\mathbf Q,M)\otimes
C_{\mathcal L^\perp}^\bullet(\mathbf Q,M')
\longrightarrow k[-3]. \tag{7.7}
$$

Why is there a shift by $3$ rather than $2$? Local Tate duality has complementary degree $2$. Compact support is the mapping fiber of global localization and therefore contributes one further degree. Equivalently, a global field has duality dimension $3$ with compact support.

There are two points to check in (7.7). First, the differential must be compatible with the pairing. The Leibniz rule for cup products reduces this to the compatibility of restriction with cup products and to the signs in the mapping-fiber differential. Second, the putative value must be independent of representatives. Changing a local positive representative changes the local cup product by a pairing between $L_v$ and $L_v^\perp$, which is zero. Changing a global representative adds the sum of local invariants of a global cup product, and global reciprocity makes that sum zero. Hence (7.7) descends to cohomology.

We obtain pairings

$$
H^i_{\mathcal L}(\mathbf Q,M)\times
H^{3-i}_{\mathcal L^\perp}(\mathbf Q,M')
\longrightarrow k. \tag{7.8}
$$

The construction also explains why an arbitrary subspace of local cohomology cannot be paired with an arbitrary dual subspace. Exact annihilators are needed for the local boundary correction to disappear.

### 7.3 Perfectness

**Theorem 7.2 (supported global duality).** Let $M$ be a finite-dimensional $k$-representation of $G_{\mathbf Q,S}$, with $\ell$ odd, and let $M'=M^*(1)$. Suppose each finite local condition is represented by a positive complex as in Chapter 4 and the dual condition is its exact local orthogonal. Then (7.8) is perfect for every $i$. Equivalently,

$$
H^i_{\mathcal L}(\mathbf Q,M)
\cong H^{3-i}_{\mathcal L^\perp}(\mathbf Q,M')^*. \tag{7.9}
$$

**Proof.** We compare two exact triangles. For $M$, the defining triangle is

$$
C_{\mathcal L}^\bullet(\mathbf Q,M)\longrightarrow
C^\bullet(G_{\mathbf Q,S},M)\longrightarrow
\bigoplus_{v\in S}U_v^-(M)\longrightarrow. \tag{7.10}
$$

For $M'$, use the corrected comparison of supported and compactly supported cochains:

$$
C_c^\bullet(G_{\mathbf Q,S},M')\longrightarrow
C_{\mathcal L^\perp}^\bullet(\mathbf Q,M')\longrightarrow
\bigoplus_{v\in S}U_v^+(M')\longrightarrow. \tag{7.11}
$$

Dualize (7.11) and shift complementary degree to $3$. Because duality reverses arrows, the resulting triangle, after one rotation, is

$$
\operatorname{Hom}_k(C_{\mathcal L^\perp}^\bullet,k)[-3]
\longrightarrow \operatorname{Hom}_k(C_c^\bullet(M'),k)[-3]
\longrightarrow \operatorname{Hom}_k\left(\bigoplus_vU_v^+(M'),k\right)[-2]
\longrightarrow. \tag{7.11a}
$$

Compactly supported global duality identifies the middle term of (7.11a) with $C^\bullet(G_{\mathbf Q,S},M)$. Lemma 7.1 identifies its third term with $\bigoplus_vU_v^-(M)$. The cup-product construction gives a morphism from the defining triangle (7.10) to (7.11a), and the middle and third vertical maps are quasi-isomorphisms.

Pass to the long exact cohomology sequences. The five lemma, applied successively from the vanishing ends of the bounded cohomological range, shows that the remaining vertical map is an isomorphism in every degree. It identifies $C_{\mathcal L}^\bullet(\mathbf Q,M)$ with the shifted dual of $C_{\mathcal L^\perp}^\bullet(\mathbf Q,M')$, which is precisely (7.9). $\square$

The proof is insensitive to replacing any positive complex by a quasi-isomorphic one. Thus supported duality depends only on the local subspaces and their cochain-realizability, not on auxiliary choices of cocycle representatives.

### 7.4 The decisive degrees

The cases $i=1$ and $i=2$ of Theorem 7.2 are

$$
H^1_{\mathcal L}(\mathbf Q,M)
\cong H^2_{\mathcal L^\perp}(\mathbf Q,M')^*, \tag{7.12}
$$

and

$$
H^2_{\mathcal L}(\mathbf Q,M)
\cong H^1_{\mathcal L^\perp}(\mathbf Q,M')^*. \tag{7.13}
$$

Because supported degree one is the Selmer group, (7.13) becomes

$$
H^2_{\mathcal L}(\mathbf Q,M)
\cong H^1_{\mathcal L^\perp}(\mathbf Q,M')^*. \tag{7.14}
$$

This is the structural statement behind every dimension calculation later in the book. The group on the right is a kernel cut out by explicit local conditions. The group on the left records failure of a global class to meet those local conditions together with any residual global degree-two kernel. Duality says these two descriptions encode exactly the same finite-dimensional vector space.

In degree zero and three, duality gives

$$
H^0_{\mathcal L}(\mathbf Q,M)
\cong H^3_{\mathcal L^\perp}(\mathbf Q,M')^*. \tag{7.15}
$$

For the positive complexes used here, $H^0_{\mathcal L}$ is the global invariant space subject to the degree-zero local boundary convention. Absolute irreducibility will force the relevant invariant spaces to vanish in the hardly-ramified calculation.

### 7.5 What duality does not assert

It is tempting to pair the two Selmer groups directly. That is generally wrong. Formula (7.12) pairs a Selmer group with supported degree two for the dual structure; formula (7.14) pairs supported degree two with the dual Selmer group. There is no natural perfect pairing

$$
H^1_{\mathcal L}(\mathbf Q,M)\times
H^1_{\mathcal L^\perp}(\mathbf Q,M')\longrightarrow k \tag{7.16}
$$

unless extra self-duality and degree-shifting data are present.

Nor does equality of the two Selmer dimensions follow from duality alone. Theorem 7.2 compares each one with a different degree-two group. To compare the two degree-one dimensions, one must compute an Euler characteristic. That computation is the content of the Greenberg--Wiles identity.

## 8. Exact sequences for supported Selmer groups

Duality becomes computationally effective when combined with the long exact sequence of the supported cone. The result is the Selmer form of the Poitou--Tate sequence. It identifies every localization defect and shows exactly where the dual Selmer group occurs.

### 8.1 The supported Poitou--Tate sequence

For brevity set

$$
Q_{\mathcal L}(M)=
\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v. \tag{8.1}
$$

**Theorem 8.1.** Under the hypotheses of Theorem 7.2, there is a natural exact sequence

$$
\begin{aligned}
0&\longrightarrow H^1_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^1(G_{\mathbf Q,S},M)
\longrightarrow Q_{\mathcal L}(M)\\
&\longrightarrow H^1_{\mathcal L^\perp}(\mathbf Q,M')^*
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow \bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)\\
&\longrightarrow H^0(G_{\mathbf Q,S},M')^*
\longrightarrow 0.
\end{aligned} \tag{8.2}
$$

At a finite place, the tilde in degree two is harmless. At infinity it denotes complete cohomology; for odd $\ell$ that term is zero.

**Proof.** The supported cone sequence (5.10) gives the first three arrows and continues as

$$
Q_{\mathcal L}(M)\longrightarrow H^2_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_v\widetilde H^2(\mathbf Q_v,M). \tag{8.3}
$$

Supported duality (7.14) identifies the middle supported group with
$H^1_{\mathcal L^\perp}(\mathbf Q,M')^*$. The cone sequence then continues into supported degree three. By (7.15), that degree-three group is dual to the appropriate degree-zero group for $M'$. Since a global invariant localizes into every local invariant space, the positive degree-zero convention leaves precisely $H^0(G_{\mathbf Q,S},M')$ in the terminal dual position. Cohomological dimension and complete real cohomology give zero beyond it. These identifications turn the long exact cone sequence into (8.2). $\square$

The arrow

$$
Q_{\mathcal L}(M)\longrightarrow
H^1_{\mathcal L^\perp}(\mathbf Q,M')^* \tag{8.4}
$$

has a concrete description. If $(c_v)_v$ represents local quotient classes and $y$ is a dual Selmer class, then

$$
(c_v)_v\longmapsto
\left(y\longmapsto\sum_{v\in S}\langle c_v,\operatorname{loc}_v(y)\rangle_v\right). \tag{8.5}
$$

The expression is well-defined because changing $c_v$ by an element of $L_v$ pairs trivially with $L_v^\perp$. Exactness at $Q_{\mathcal L}(M)$ says that a collection of permitted local quotient data comes from a global class exactly when it annihilates every dual Selmer class.

### 8.2 Localization defects

Let

$$
\lambda_{\mathcal L}:H^1(G_{\mathbf Q,S},M)\longrightarrow Q_{\mathcal L}(M) \tag{8.6}
$$

be localization modulo the local conditions. Its kernel is the Selmer group. Its cokernel is not, in general, the entire dual Selmer dual; by (8.2), it is the kernel of the following map to global degree two. Thus there is a short exact sequence

$$
0\longrightarrow\operatorname{coker}(\lambda_{\mathcal L})
\longrightarrow H^1_{\mathcal L^\perp}(\mathbf Q,M')^*
\longrightarrow \Sha_S^2(M)\longrightarrow0, \tag{8.7}
$$

where

$$
\Sha_S^2(M)=
\ker\left(H^2(G_{\mathbf Q,S},M)\longrightarrow
\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)\right). \tag{8.8}
$$

Combining (8.7) with the cone calculation (5.13) recovers

$$
H^2_{\mathcal L}(\mathbf Q,M)
\cong H^1_{\mathcal L^\perp}(\mathbf Q,M')^*. \tag{8.9}
$$

This comparison prevents a common error. Surjectivity of localization is equivalent to the vanishing of the kernel of the map from the dual Selmer dual to $H^2$, not automatically to vanishing of the whole dual Selmer group. If $\Sha_S^2(M)=0$, then the two vanishing statements become equivalent.

### 8.3 Changing local conditions

Suppose $\mathcal L=(L_v)$ and $\mathcal L'=(L'_v)$ satisfy $L_v\subseteq L'_v$ for every $v$. Enlarging a local condition weakens the Selmer restriction. The quotient maps induce a morphism of supported complexes and an exact sequence

$$
\begin{aligned}
0&\longrightarrow H^1_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^1_{\mathcal L'}(\mathbf Q,M)
\longrightarrow\bigoplus_{v\in S}L'_v/L_v\\
&\longrightarrow H^2_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^2_{\mathcal L'}(\mathbf Q,M)
\longrightarrow0
\end{aligned} \tag{8.10}
$$

whenever the positive local complexes are concentrated in degrees zero and one as in Chapter 4. If degree-two terms occur in a more general local theory, the sequence continues rather than ending at zero.

**Proof.** The quotient of the positive local complex for $\mathcal L'$ by that for $\mathcal L$ has cohomology $L'_v/L_v$ in degree one and zero elsewhere. The induced triangle of supported mapping fibers has this direct sum as its third term, with the shift fixed by the fiber convention. Its long exact cohomology sequence is (8.10). $\square$

Orthogonality reverses inclusions:

$$
L_v\subseteq L'_v
\quad\Longrightarrow\quad
(L'_v)^\perp\subseteq L_v^\perp. \tag{8.11}
$$

Dualizing (8.10) therefore gives the corresponding change-of-structure sequence for the dual representation in the opposite direction. This is another expression of supported duality.

### 8.4 Strict and relaxed structures

At a chosen finite place $w$, three useful conditions are

$$
0\subseteq L_w\subseteq H^1(\mathbf Q_w,M). \tag{8.12}
$$

They are called strict, prescribed, and relaxed. Their exact orthogonals on $M'$ are, respectively,

$$
H^1(\mathbf Q_w,M')\supseteq L_w^\perp\supseteq0. \tag{8.13}
$$

Keeping all other places fixed, (8.10) measures the change from strict to prescribed by a map through $L_w$, and from prescribed to relaxed by a map through $H^1(\mathbf Q_w,M)/L_w$. Consequently the Selmer dimension can rise by at most the dimension of the added local space. The supported degree-two dimension changes by the complementary amount measured by the connecting map.

These sequences are especially effective in auxiliary-prime arguments. One adds a place with a controlled one-dimensional local quotient, observes whether the connecting map is zero or injective, and thereby changes either the Selmer group or its supported dual obstruction by exactly one dimension. The present book needs no auxiliary primes, but the exact mechanism clarifies why supported cohomology, rather than only a Selmer kernel, is the stable object.

## 9. The Greenberg--Wiles identity

The exact sequence of Chapter 8 turns a global comparison into a finite sum of local corrections. This is the Greenberg--Wiles identity. Its usefulness comes from cancellation: complicated ambient local cohomology disappears, leaving only the dimension of the chosen tangent condition relative to local invariants.

### 9.1 Statement with all archimedean terms

For a finite place $v$, write

$$
h_v^i(M)=\dim_kH^i(\mathbf Q_v,M), \qquad
h_S^i(M)=\dim_kH^i(G_{\mathbf Q,S},M). \tag{9.1}
$$

At $v=\infty$, put

$$
h_\infty^0(M)=\dim_k H^0(\mathbf R,M), \qquad L_\infty=0. \tag{9.2}
$$

The ordinary invariant space appears in (9.2), even though complete cohomology at infinity vanishes. This distinction is essential.

**Theorem 9.1 (Greenberg--Wiles).** Let $S$ contain $\ell$ and $\infty$, and let $M$ and $M'=M^*(1)$ be as above. For finite-dimensional local conditions $L_v\subseteq H^1(\mathbf Q_v,M)$ and their exact orthogonals, one has

$$
\begin{aligned}
&\dim H^1_{\mathcal L}(\mathbf Q,M)
-\dim H^1_{\mathcal L^\perp}(\mathbf Q,M')\\
&\qquad =h_S^0(M)-h_S^0(M')
+\sum_{v\in S}\bigl(\dim L_v-h_v^0(M)\bigr).
\end{aligned} \tag{9.3}
$$

At infinity, the summand means $0-h_\infty^0(M)$. Every term is therefore explicit: two global invariant dimensions and one correction at each controlled place.

### 9.2 Proof from the exact sequence

**Proof of Theorem 9.1.** Take the alternating sum of dimensions in (8.2). Since the sequence is exact and finite, that alternating sum is zero. With

$$
q_{\mathcal L}(M)=
\sum_{v\in S,\,v<\infty}\bigl(h_v^1(M)-\dim L_v\bigr), \tag{9.4}
$$

we obtain

$$
\begin{aligned}
\dim H^1_{\mathcal L}(\mathbf Q,M)
-\dim H^1_{\mathcal L^\perp}(\mathbf Q,M')
={}&h_S^1(M)-q_{\mathcal L}(M)-h_S^2(M)\\
&+\sum_{v<\infty}h_v^2(M)-h_S^0(M').
\end{aligned} \tag{9.5}
$$

For $\mathbf Q$ and odd coefficients, the global Euler characteristic formula is

$$
h_S^0(M)-h_S^1(M)+h_S^2(M)
=-\dim M+h_\infty^0(M). \tag{9.6}
$$

Rearranging gives

$$
h_S^1(M)-h_S^2(M)
=h_S^0(M)+\dim M-h_\infty^0(M). \tag{9.7}
$$

The finite local Euler characteristic formulas are

$$
h_v^1(M)=h_v^0(M)+h_v^2(M) \qquad(v\ne\ell), \tag{9.8}
$$

and

$$
h_\ell^1(M)=h_\ell^0(M)+h_\ell^2(M)+\dim M. \tag{9.9}
$$

Insert (9.7)--(9.9) into (9.5). For every finite $v$, $h_v^2(M)$ cancels. The single $\dim M$ in (9.7) cancels the additional $\dim M$ at $v=\ell$ in (9.9). What remains is

$$
h_S^0(M)-h_S^0(M')
+\sum_{v<\infty}\bigl(\dim L_v-h_v^0(M)\bigr)
-h_\infty^0(M), \tag{9.10}
$$

which is (9.3) under convention (9.2). $\square$

The proof shows why one must not use the away-from-$\ell$ local Euler formula at $\ell$. Doing so would leave a spurious $\dim M$ in the answer. It also shows why deleting infinity from the sum would leave a spurious $h_\infty^0(M)$.

### 9.3 The supported Euler identity and inequality

Supported duality identifies

$$
\dim H^2_{\mathcal L}(\mathbf Q,M)
=\dim H^1_{\mathcal L^\perp}(\mathbf Q,M'). \tag{9.11}
$$

Consequently (9.3) is equivalently the exact supported Euler identity

$$
\begin{aligned}
\dim H^1_{\mathcal L}(\mathbf Q,M)
-\dim H^2_{\mathcal L}(\mathbf Q,M)
={}&h_S^0(M)-h_S^0(M')\\
&+\sum_{v\in S}\bigl(\dim L_v-h_v^0(M)\bigr).
\end{aligned} \tag{9.12}
$$

Set the right side equal to $\delta(\mathcal L,M)$. Then

$$
\dim H^1_{\mathcal L}(\mathbf Q,M)
=\dim H^2_{\mathcal L}(\mathbf Q,M)+\delta(\mathcal L,M). \tag{9.13}
$$

Thus, if $\delta(\mathcal L,M)\ge0$,

$$
\dim H^2_{\mathcal L}(\mathbf Q,M)
\le \dim H^1_{\mathcal L}(\mathbf Q,M), \tag{9.14}
$$

with equality exactly when $\delta(\mathcal L,M)=0$. If the correction is negative, the inequality reverses. The inequality is therefore not an independent estimate: it is the sign consequence of an exact formula.

In deformation theory, supported degree one is the tangent space and supported degree two is the natural obstruction receptacle. Formula (9.14) is the exact Greenberg--Wiles dimension inequality for any deformation problem whose local conditions give a nonnegative correction. The hardly-ramified problem is balanced, so its inequality sharpens to equality.

### 9.4 A bookkeeping table

The following table isolates the source of every term in (9.3).

| source | contribution after cancellation |
|---|---:|
| global degree zero for $M$ | $+h_S^0(M)$ |
| global terminal dual term | $-h_S^0(M')$ |
| finite local condition at $v$ | $+\dim L_v$ |
| finite local invariants at $v$ | $-h_v^0(M)$ |
| real ordinary invariants | $-h_\infty^0(M)$ |
| local degree two | $0$ |
| coefficient-prime volume term | $0$ |

The two zero rows are genuine cancellations, not absent phenomena. Local degree-two cohomology is needed to complete Poitou--Tate exactness. The coefficient-prime volume term is needed in both the global and local Euler formulas. Omitting either before cancellation gives the wrong result.

There is also a useful diagnostic. If a proposed calculation produces an uncancelled $\dim M$ over $\mathbf Q$, the coefficient-prime Euler term has almost certainly been mishandled. If it produces a discrepancy of $h_\infty^0(M)$, ordinary and complete real cohomology have probably been confused.

## 10. The hardly-ramified Selmer calculation

We now apply the general theory to the representation fixed in Chapter 1. Every term in (9.3) is calculated locally or by absolute irreducibility. The entire global balance is then the cancellation of one positive contribution at $\ell$ against one negative contribution at infinity.

### 10.1 The Selmer structures

Let

$$
M=\operatorname{ad}^0(\bar\rho),\qquad M'=M(1),\qquad
S=\{2,\ell,\infty\}. \tag{10.1}
$$

The hardly-ramified local structure is

$$
\mathcal L_{\mathrm{hr}}=(L_2,L_\ell,L_\infty), \tag{10.2}
$$

where

$$
L_2=0,qquad
L_\ell=L_{\mathrm{fl}},qquad
L_\infty=0. \tag{10.3}
$$

Here $L_{\mathrm{fl}}$ is the fixed-determinant finite-flat tangent space at $\ell$. Its dual structure is

$$
\mathcal L_{\mathrm{hr}}^\perp
=(H^1(\mathbf Q_2,M'),L_{\mathrm{fl}}^\perp,0), \tag{10.4}
$$

because the orthogonal of zero at $2$ is the full local cohomology group. In fact that full group vanishes under our hypotheses, but (10.4) records the structural reason before using the calculation.

The associated Selmer groups are

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\left(
H^1(G_{\mathbf Q,S},M)longrightarrow
H^1(\mathbf Q_2,M)\oplus
\frac{H^1(\mathbf Q_\ell,M)}{L_{\mathrm{fl}}}
\right), \tag{10.5}
$$

and

$$
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=\ker\left(
H^1(G_{\mathbf Q,S},M')longrightarrow
\frac{H^1(\mathbf Q_\ell,M')}{L_{\mathrm{fl}}^\perp}
\right). \tag{10.6}
$$

There is no nonzero complete real term in either map.

### 10.2 The prime $2$

The tame quadratic local type at $2$ has two distinct inertia characters. The explicit matrix calculation of Chapter 2 gives

$$
H^0(\mathbf Q_2,M)=0. \tag{10.7}
$$

Because $2\ne\ell$, local Euler characteristic and local duality give

$$
h_2^1(M)=h_2^0(M)+h_2^0(M')=0. \tag{10.8}
$$

Thus the strict local condition is not discarding any tangent directions: there are none. Its local correction is

$$
\dim L_2-h_2^0(M)=0-0=0. \tag{10.9}
$$

The twisted invariant calculation is equally important. On the unique inertia-invariant line of the full adjoint representation, arithmetic Frobenius acts by $-1$ before twisting and by $-2$ after twisting. Since $\ell\ge7$, $-2\ne1$ in $k$, so

$$
H^0(\mathbf Q_2,M')=0. \tag{10.10}
$$

Local duality then gives $H^2(\mathbf Q_2,M)=0$, confirming (10.8) directly. The prime $2$ contributes neither a tangent dimension nor a hidden degree-two term.

### 10.3 The coefficient prime

Put

$$
h_\ell=\dim_k\operatorname{End}_{G_{\mathbf Q_\ell}}(V). \tag{10.11}
$$

The scalar endomorphisms form a one-dimensional direct summand because $\ell$ is odd and $\dim V=2$. Hence

$$
h_\ell^0(M)=h_\ell-1. \tag{10.12}
$$

The finite-flat local analysis gives

$$
\dim L_{\mathrm{fl}}=h_\ell. \tag{10.13}
$$

Therefore the local correction at $\ell$ is exactly

$$
\dim L_{\mathrm{fl}}-h_\ell^0(M)
=h_\ell-(h_\ell-1)=1. \tag{10.14}
$$

This computation works uniformly whether the local representation is absolutely irreducible, in which case $h_\ell=1$, or has a larger local endomorphism algebra. Both the tangent dimension and the invariant dimension rise together; their difference stays equal to one.

For completeness, local Euler characteristic yields the ambient dimension

$$
h_\ell^1(M)
=h_\ell^0(M)+h_\ell^0(M')+\dim M
=h_\ell^0(M')+h_\ell+2, \tag{10.15}
$$

because $\dim M=3$. Exact orthogonality then gives

$$
\begin{aligned}
\dim L_{\mathrm{fl}}^\perp
&=h_\ell^1(M)-\dim L_{\mathrm{fl}}\\
&=h_\ell^0(M')+2.
\end{aligned} \tag{10.16}
$$

No assumption that $H^0(\mathbf Q_\ell,M')$ vanishes is needed. This is one of the main reasons for keeping the local calculation symbolic until the final cancellation.

### 10.4 The real place and global invariants

Oddness means complex conjugation acts on $V$ with two distinct eigenvalues $1$ and $-1$. Its conjugation action on $M$ fixes the traceless diagonal line and negates the two off-diagonal lines. Therefore

$$
h_\infty^0(M)=1. \tag{10.17}
$$

The local condition at infinity is zero, so its correction is

$$
\dim L_\infty-h_\infty^0(M)=0-1=-1. \tag{10.18}
$$

This is an ordinary invariant calculation. Complete cohomology still vanishes because $2$ is invertible in $k$.

Globally, absolute irreducibility gives

$$
\operatorname{End}_{G_{\mathbf Q,S}}(V)=k. \tag{10.19}
$$

Splitting endomorphisms into scalars and trace-zero endomorphisms gives

$$
H^0(G_{\mathbf Q,S},M)=0. \tag{10.20}
$$

A global invariant in $M'$ restricts to a local invariant at $2$. Restriction of a vector is just the same vector viewed under a subgroup, so the map

$$
H^0(G_{\mathbf Q,S},M')\longrightarrow H^0(\mathbf Q_2,M') \tag{10.21}
$$

is injective. Equation (10.10) therefore implies

$$
H^0(G_{\mathbf Q,S},M')=0. \tag{10.22}
$$

This argument uses the distinguished local type at $2$ to eliminate the global twisted invariants. Absolute irreducibility alone would not suffice for the twisted module.

### 10.5 Exact balance

All terms of the Greenberg--Wiles identity are now known:

$$
\begin{array}{c|c}
\text{term}&\text{value}\\ \hline
h_S^0(M)&0\\
-h_S^0(M')&0\\
\dim L_2-h_2^0(M)&0\\
\dim L_\ell-h_\ell^0(M)&+1\\
\dim L_\infty-h_\infty^0(M)&-1.
\end{array} \tag{10.23}
$$

The sum is zero. Theorem 9.1 gives

$$
\boxed{
\dim H^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim H^1_{\mathrm{hr}^\perp}(\mathbf Q,M').
} \tag{10.24}
$$

Supported duality gives

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\cong H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*, \tag{10.25}
$$

and hence the exact supported balance

$$
\boxed{
\dim H^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim H^1_{\mathrm{hr}}(\mathbf Q,M).
} \tag{10.26}
$$

In particular,

$$
\dim H^2_{\mathrm{hr}}(\mathbf Q,M)
\le \dim H^1_{\mathrm{hr}}(\mathbf Q,M), \tag{10.27}
$$

and equality always holds under the stated hypotheses. This is the exact Greenberg--Wiles dimension inequality for the hardly-ramified deformation problem. The word “exact” matters: the inequality is not merely bounded by a chain of estimates; both sides are forced to coincide.

## 11. Consequences and exceptional cases

The balance theorem is strongest when its scope is stated precisely. It controls tangent and supported obstruction dimensions; it does not by itself force either group to vanish, nor does it silently extend to coefficient characteristics excluded from the local analysis. This chapter records the valid consequences and the boundary cases.

### 11.1 Tangents, supported obstructions, and relation bounds

Let $D_{\mathrm{hr}}$ denote the fixed-determinant global deformation problem with the three local conditions of Chapter 10. A first-order deformation over $k[\epsilon]/(\epsilon^2)$ has the form

$$
g\longmapsto (1+\epsilon c(g))\bar\rho(g), \tag{11.1}
$$

where $c$ is a $1$-cocycle with values in $M$. Strict equivalence changes $c$ by a coboundary. The local deformation requirements say exactly that the localization of $[c]$ lies in $L_v$. Therefore

$$
t_{D_{\mathrm{hr}}}
\cong H^1_{\mathrm{hr}}(\mathbf Q,M). \tag{11.2}
$$

The determinant is fixed because the infinitesimal determinant of $1+\epsilon X$ is $1+\epsilon\operatorname{tr}(X)$, so trace-zero endomorphisms are precisely the fixed-determinant tangent coefficients.

For a small extension of coefficient rings

$$
0\longrightarrow I\longrightarrow A'\longrightarrow A\longrightarrow0,
\qquad \mathfrak m_{A'}I=0, \tag{11.3}
$$

choose set-theoretic lifts of a deformation over $A$. Failure of multiplication defines a $2$-cocycle with values in $M\otimes_k I$. Local admissible lifts give local nullhomotopies lying in the positive local complexes. The global cocycle together with those local nullhomotopies is therefore a supported degree-two class

$$
\operatorname{ob}(\rho_A,A')
\in H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes_k I. \tag{11.4}
$$

Changing the chosen lifts changes this class by a supported coboundary. If the class vanishes, its trivialization corrects the lifts and produces a global admissible lift. Thus supported degree two is a complete obstruction space for the global problem once the local conditions themselves have the stated lifting theory.

Suppose the global deformation ring has a minimal presentation

$$
R_{\mathrm{hr}}
\simeq \mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r), \tag{11.5}
$$

where minimal means that $t$ is the relative tangent dimension and that the images of the $f_i$ minimally generate the relation ideal. Standard obstruction theory associates to a minimal relation an independent obstruction functional. Consequently there is an injection from the dual of the minimal relation space into a complete obstruction space, and hence

$$
t=\dim H^1_{\mathrm{hr}}(\mathbf Q,M),
\qquad
r\le \dim H^2_{\mathrm{hr}}(\mathbf Q,M). \tag{11.6}
$$

Combining (11.6) with (10.26) gives the exact relation bound

$$
r\le t. \tag{11.7}
$$

It follows from (11.5) that

$$
\dim R_{\mathrm{hr}}\ge 1+t-r\ge1, \tag{11.8}
$$

when $R_{\mathrm{hr}}$ is nonzero and dimension is measured over the one-dimensional coefficient ring $\mathcal O$. Equation (11.7) is an upper bound for minimal relations, not a claim that every supported cohomology class occurs as a relation.

### 11.2 Local smoothness does not imply global smoothness

Each local deformation condition in the hardly-ramified problem is formally smooth under the hypotheses used here. At $2$, the prescribed tame type is rigid in degree one. At $\ell$, the finite-flat condition has a smooth tangent theory of dimension $h_\ell$. At infinity, oddness fixes the conjugacy class with no positive-degree cohomology.

It does not follow that the global deformation problem is smooth. Local smoothness removes local obstruction classes internal to each condition; it does not guarantee that admissible local lifts glue globally. The gluing defect is exactly what the mapping fiber retains. By (10.25), it is measured by the dual Selmer group:

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)=0
\quad\Longleftrightarrow\quad
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')=0. \tag{11.9}
$$

Balance then gives

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)=0
\quad\Longleftrightarrow\quad
H^1_{\mathrm{hr}}(\mathbf Q,M)=0. \tag{11.10}
$$

Thus, in this special balanced problem, unobstructedness forces tangent rigidity and conversely. This equivalence uses both supported duality and the zero Euler correction; it is not a general property of deformation problems.

If the common dimension in (10.26) is positive, the calculation still gives valuable information. It says the natural obstruction allowance is no larger than the number of tangent variables and yields the presentation bound (11.7), even though it does not determine the individual dimension.

### 11.3 Scalar and reducible local restrictions

Global absolute irreducibility does not imply local absolute irreducibility at $\ell$. The local restriction may be irreducible, a nonsplit extension, or a split sum of characters. The calculation was deliberately expressed through

$$
h_\ell=\dim\operatorname{End}_{G_{\mathbf Q_\ell}}(V). \tag{11.11}
$$

If the local centralizer consists only of scalars, then

$$
h_\ell=1,qquad h_\ell^0(M)=0,qquad \dim L_\ell=1. \tag{11.12}
$$

If the restriction is a split sum of two distinct characters, then diagonal endomorphisms give

$$
h_\ell=2,qquad h_\ell^0(M)=1,qquad \dim L_\ell=2. \tag{11.13}
$$

In both cases the correction is one. A nonsplit extension generally has a one-dimensional or larger centralizer depending on whether the two characters coincide; the only quantity used globally is again the difference

$$
\dim L_\ell-(h_\ell-1)=1. \tag{11.14}
$$

A scalar local restriction would have an even larger centralizer. It must not be inserted into (11.14) unless it still lies in the finite-flat class for which the tangent formula $\dim L_\ell=h_\ell$ was proved. The invariant identity (10.12) is formal, but the tangent identity (10.13) has geometric hypotheses. This separates a harmless increase of centralizer from a genuine failure of the local deformation calculation.

At $2$, the local representation is not scalar: its inertia has characteristic polynomial $X^2+X+1$ and arithmetic Frobenius exchanges the two inertia characters. Both features are used to make the trace-zero invariant space vanish. Replacing that type by an unramified or scalar type changes the $2$-adic correction and may also permit global twisted invariants.

### 11.4 The exceptional primes $2$, $3$, and $5$

The theorem assumes $\ell\ge7$. The smaller primes fail for different reasons and should not be grouped under a single vague warning.

In characteristic $2$, trace does not split the full adjoint representation:

$$
\operatorname{tr}(I)=2=0. \tag{11.15}
$$

Thus $I\in\operatorname{ad}^0(V)$, the trace pairing on the expected three-dimensional fixed-determinant module is not used in the same way, and real complete cohomology need not vanish because $|C_2|$ is not invertible. The coefficient module, the duality conventions, and the infinite-place contribution all require a separate treatment.

In characteristic $3$, the local calculation at $2$ fails sharply. The twisted Frobenius eigenvalue is

$$
-2=1\pmod3, \tag{11.16}
$$

so $H^0(\mathbf Q_2,M')$ can be nonzero. Then $H^2(\mathbf Q_2,M)$ and the ambient $H^1(\mathbf Q_2,M)$ can be nonzero, and restriction at $2$ no longer proves the vanishing of global twisted invariants. The zero contribution asserted in (10.9) is no longer the entire story.

In characteristic $5$, neither (11.15) nor (11.16) occurs: $2$ is invertible and $-2\ne1$. The individual finite-flat smoothness theorem is available more widely under its unramified low-weight hypotheses, but the unified hardly-ramified global package used here is stated for $\ell\ge7$. The present argument therefore makes no claim for $\ell=5$. Extending the full theorem would require rechecking every remaining global-range and small-weight hypothesis; the favorable calculations at the two finite distinguished places are not, by themselves, such an extension.

This yields a useful rule. A numerical formula may remain meaningful at an excluded prime, but it becomes a theorem only after every structural input used to derive it has been verified in that characteristic.

### 11.5 Changes of coefficients and controlling sets

Let $k'/k$ be a finite extension and put $M_{k'}=M\otimes_k k'$. Flat base change commutes with kernels, cokernels, and cohomology of finite-dimensional complexes. Consequently

$$
H^i_{\mathcal L}(\mathbf Q,M)\otimes_k k'
\cong H^i_{\mathcal L\otimes k'}(\mathbf Q,M_{k'}), \tag{11.17}
$$

provided the local conditions themselves base-change to the indicated subspaces. Dimensions over $k'$ equal the original dimensions over $k$, and the Greenberg--Wiles correction is unchanged.

This statement does not apply blindly to reduction from a characteristic-zero lattice or to changing the residue characteristic. Such operations can change invariant dimensions, local endomorphism algebras, and the finite-flat tangent space. Equation (11.17) concerns only extension of the fixed residual coefficient field.

If a new finite prime $p\notin S$ is added to the controlling set, with $M$ unramified at $p$, assign the unramified condition. Chapter 6 then gives a quasi-isomorphism of supported complexes. Numerically, its Greenberg--Wiles correction is zero because away from $\ell$ the unramified condition has dimension $h_p^0(M)$ whenever the usual unramified local complex applies:

$$
\dim H^1_{\mathrm{ur}}(\mathbf Q_p,M)-h_p^0(M)=0. \tag{11.18}
$$

If instead one assigns the strict or relaxed condition at $p$, the problem has genuinely changed and so has its correction. Independence of the controlling set is always paired with the unramified condition at newly admitted harmless places.

## 12. The supported-cohomology theorem package

The preceding chapters can now be compressed into one theorem with a transparent hypothesis ledger. The purpose of this final chapter is not to repeat the proofs, but to show exactly how the local, global, duality, and deformation-theoretic statements fit together and how the calculation can be reused without losing an exceptional term.

### 12.1 Main theorem

**Theorem 12.1 (supported hardly-ramified balance).** Let $\ell\ge7$, let $k$ be a finite field of characteristic $\ell$, and let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k) \tag{12.1}
$$

be continuous, absolutely irreducible, odd, of determinant $\bar\chi_\ell$, unramified outside $\{2,\ell\}$, of tame-quadratic order-three type at $2$, and finite flat of the stated coefficient-linear type at $\ell$. Set

$$
M=\operatorname{ad}^0(\bar\rho),\qquad M'=M(1),\qquad
S=\{2,\ell,\infty\}. \tag{12.2}
$$

Give $M$ the strict condition at $2$, the fixed-determinant finite-flat tangent condition at $\ell$, and the odd condition at infinity. Let $\mathcal L_{\mathrm{hr}}^\perp$ be the exact local Tate orthogonal structure on $M'$.

Then the following statements hold.

1. The supported mapping fiber $C^\bullet_{\mathrm{hr}}(\mathbf Q,M)$ has
   $$
   H^1(C^\bullet_{\mathrm{hr}})=H^1_{\mathrm{hr}}(\mathbf Q,M).
   $$
2. Supported duality is perfect:
   $$
   H^i_{\mathrm{hr}}(\mathbf Q,M)
   \cong H^{3-i}_{\mathrm{hr}^\perp}(\mathbf Q,M')^*.
   $$
3. In particular,
   $$
   H^2_{\mathrm{hr}}(\mathbf Q,M)
   \cong H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*.
   $$
4. The Greenberg--Wiles correction is zero:
   $$
   \dim H^1_{\mathrm{hr}}(\mathbf Q,M)
   -\dim H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')=0.
   $$
5. Hence
   $$
   \dim H^2_{\mathrm{hr}}(\mathbf Q,M)
   =\dim H^1_{\mathrm{hr}}(\mathbf Q,M).
   $$
6. For a minimally presented global deformation ring with $t$ tangent variables and $r$ relations,
   $$
   r\le \dim H^2_{\mathrm{hr}}=\dim H^1_{\mathrm{hr}}=t.
   $$

**Proof.** Statement 1 is (5.12). Statement 2 is Theorem 7.2, and Statement 3 is its degree-two case. The local ledger (2.24) has contributions $0$, $1$, and $-1$, while (2.21) and (2.23) make both global invariant terms zero. Theorem 9.1 therefore proves Statement 4. Combining Statements 3 and 4 proves Statement 5. Finally, the complete supported obstruction construction of (11.4) bounds the minimal relation space as in (11.6), proving Statement 6. $\square$

The conclusion is a balance theorem, not a vanishing theorem. It is uniform in the local centralizer dimension $h_\ell$ because that dimension cancels inside the coefficient-prime correction.

### 12.2 Dependency and hypothesis ledger

Every substantial input used above has a precise role and a matching hypothesis.

| prior foundation | role here | hypotheses checked here |
|---|---|---|
| Book 30, *Local Galois Cohomology* | cohomological dimension, local Euler formulas, unramified cohomology | finite residual modules; $v\ne\ell$ for zero local Euler characteristic; mixed-characteristic correction at $v=\ell$ |
| Book 31, *Tate Local Duality* | $H^2(M)=H^0(M')^*$ and exact orthogonals in $H^1$ | finite modules over local fields; Tate twist included |
| Book 32, *Global Galois Cohomology and Selmer Groups* | restricted-ramification cohomology, localization kernels, tangent interpretation | $S$ contains all ramified places, $\ell$, and infinity |
| Book 33, *Poitou--Tate Duality* | compact-support duality and the global exact sequence | complete cohomology at real places; $M'=M^*(1)$ |
| Book 68, *Global Deformation Problems* | tangent and obstruction interpretation; presentation bound | absolute irreducibility and fixed determinant; local conditions represented cohomologically; $\ell\nmid2$ for the trace-zero simplification |
| Book 182, *Local Conditions for Hardly-Ramified Minimal Deformations* | $L_2=0$, $\dim L_\ell=h_\ell$, local smoothness | $\ell\ge7$; tame-quadratic type at $2$; coefficient-linear finite flatness at $\ell$ |

The hypotheses cannot be freely redistributed among the rows. For example, local Tate duality alone does not identify the finite-flat tangent subspace; the hardly-ramified local theory does. Conversely, the finite-flat calculation gives a local dimension but not the global duality sequence; Poitou--Tate duality does.

The use of the earlier foundations can be displayed as a dependency diagram:

```text
finite local cohomology -----> local dimensions -----------+
             |                                           |
             v                                           v
local Tate duality ---------> exact orthogonals     Greenberg--Wiles
             |                                           ^
             v                                           |
Poitou--Tate duality -------> supported duality ----------+
             ^                                           |
             |                                           |
global Selmer theory -------> supported mapping fiber ----+
             ^
             |
hardly-ramified local theory + global deformation theory
```

Every arrow preserves the hypotheses required at its source. In particular, infinity is treated by complete cohomology in the duality row and by ordinary invariants in the Euler row; the coefficient prime uses the mixed-characteristic Euler formula; and fixed determinant uses the trace-zero adjoint only because $\ell$ is odd.

### 12.3 A reusable calculation protocol

For another supported deformation problem over $\mathbf Q$, the calculation can be reproduced in the following order.

1. Fix $M$, its Tate dual $M^*(1)$, and a controlling set containing the coefficient prime and infinity.
2. Compute both global invariant spaces. Do not infer the twisted invariant vanishing from untwisted absolute irreducibility.
3. At every finite place, calculate $h_v^0(M)$ and describe the actual tangent subspace $L_v$.
4. At the coefficient prime, use the mixed-characteristic local Euler formula, including $[K_v:\mathbf Q_\ell]\dim M$.
5. At real places, separate ordinary invariants from complete cohomology.
6. Define dual local conditions as exact Tate orthogonals, rather than by copying names from the primal side.
7. Realize the local conditions by positive complexes and form the supported mapping fiber.
8. Identify supported degree one with the desired Selmer kernel and supported degree two with the dual Selmer dual.
9. Insert the normalized local corrections and global invariants into (9.3).
10. Only after the exact identity is known, deduce an inequality or a presentation bound.

The order matters. Starting with a desired inequality can conceal a missing real correction. Starting with a guessed dual local condition can conceal a failure of exact orthogonality. Starting with global dimensions can conceal the coefficient-prime bulk term. The protocol forces every possible discrepancy to appear in a named ledger entry.

There are three final consistency tests. First, harmless enlargement of $S$ with an unramified condition should not alter the supported complex. Second, the dimensions of $L_v$ and $L_v^\perp$ should add to $h_v^1(M)$ at every finite place. Third, the Greenberg--Wiles difference should agree with $\dim H^1_{\mathcal L}-\dim H^2_{\mathcal L}$ through supported duality.

### 12.4 Conclusion

The hardly-ramified problem is balanced for a precise arithmetic reason. Rigidity at $2$ eliminates both local adjoint invariants and global twisted invariants. Finite flatness at $\ell$ contributes one more tangent direction than local trace-zero automorphisms. Oddness contributes one real invariant and no real tangent direction. The last two corrections cancel.

Supported cohomology retains this numerical balance as a structural duality. Its degree-one group is the admissible global tangent space. Its degree-two group is the dual of the orthogonal Selmer group and the natural receptacle for global lifting obstructions. Compact support is recovered when the entire positive boundary complex is zero; a strict degree-one condition can still retain local automorphisms in degree zero. Poitou--Tate duality supplies the perfect complementary-degree pairing.

Thus the final equality

$$
\dim H^2_{\mathrm{hr}}(\mathbf Q,\operatorname{ad}^0\bar\rho)
=\dim H^1_{\mathrm{hr}}(\mathbf Q,\operatorname{ad}^0\bar\rho) \tag{12.3}
$$

is simultaneously a local calculation, a global Euler identity, and a supported duality statement. Each hypothesis has a visible task, every exceptional term is accounted for, and the resulting relation bound is exactly as strong as the cohomology permits.
