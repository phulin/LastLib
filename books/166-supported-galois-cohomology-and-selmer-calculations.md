# Supported Galois Cohomology and Selmer Calculations

## Contents

- [1. The exact problem and its output](#1-the-exact-problem-and-its-output)
  - [1.1 Standing hardly-ramified data](#11-standing-hardly-ramified-data)
  - [1.2 Coefficients and local conditions](#12-coefficients-and-local-conditions)
  - [1.3 What this book proves](#13-what-this-book-proves)
- [2. The complete local ledger](#2-the-complete-local-ledger)
  - [2.1 The dyadic Frey-special profile](#21-the-dyadic-frey-special-profile)
  - [2.2 The coefficient prime](#22-the-coefficient-prime)
  - [2.3 The real place and global invariants](#23-the-real-place-and-global-invariants)
  - [2.4 Local conditions and exact orthogonals](#24-local-conditions-and-exact-orthogonals)
- [3. Cochain models for support](#3-cochain-models-for-support)
  - [3.1 Positive local complexes](#31-positive-local-complexes)
  - [3.2 Quotient local complexes](#32-quotient-local-complexes)
  - [3.3 The local duality check](#33-the-local-duality-check)
- [4. The supported global complex](#4-the-supported-global-complex)
  - [4.1 Definition and signs](#41-definition-and-signs)
  - [4.2 Its low-degree exact sequence](#42-its-low-degree-exact-sequence)
  - [4.3 What supported degree two contains](#43-what-supported-degree-two-contains)
- [5. Poitou--Tate and supported duality](#5-poitou--tate-and-supported-duality)
  - [5.1 The exact sequence with its endpoint](#51-the-exact-sequence-with-its-endpoint)
  - [5.2 Perfect supported duality](#52-perfect-supported-duality)
  - [5.3 The specialized hardly-ramified sequence](#53-the-specialized-hardly-ramified-sequence)
- [6. Euler characteristics and exact balance](#6-euler-characteristics-and-exact-balance)
  - [6.1 Euler formulas with every exceptional term](#61-euler-formulas-with-every-exceptional-term)
  - [6.2 Greenberg--Wiles calculation](#62-greenberg--wiles-calculation)
  - [6.3 An independent exact-sequence check](#63-an-independent-exact-sequence-check)
- [7. The theorem and the downstream contract](#7-the-theorem-and-the-downstream-contract)
  - [7.1 Supported hardly-ramified balance](#71-supported-hardly-ramified-balance)
  - [7.2 Interface to Books 167 and 181](#72-interface-to-books-167-and-181)
  - [7.3 Scope boundary](#73-scope-boundary)
- [8. Source-closure audit](#8-source-closure-audit)
  - [8.1 Direct dependency ledger](#81-direct-dependency-ledger)
  - [8.2 Closure and hypothesis flow](#82-closure-and-hypothesis-flow)

## 1. The exact problem and its output

This book has one task. It constructs the supported cochain complex for the
hardly-ramified fixed-determinant deformation problem over $\mathbf Q$,
identifies its degree-one and degree-two groups, and proves their dimensions
are equal. The construction is the cohomological input used by Books 167 and 181. No presentation theorem, automorphy argument, finiteness theorem, or
characteristic-zero lifting theorem is proved here.

### 1.1 Standing hardly-ramified data

Let $\ell\geq 7$, let $k$ be a finite field of characteristic $\ell$,
and let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k) \tag{1.1}
$$

be continuous and satisfy all of the following conditions.

1. $\det\bar\rho=\bar\chi_\ell$.
2. $\bar\rho$ is absolutely irreducible and odd.
3. $\bar\rho$ is unramified outside $\{2,\ell\}$.
4. At $2$, the Frey-special datum from Book 165 is fixed: the
   nonzero-monodromy minimal-special profile with its intrinsic line and
   named sign (SP).
5. At $\ell$, the restriction is the generic fibre of a
   coefficient-linear finite-flat model over $\mathbf Z_\ell$, of weights
   $\{0,1\}$ and cyclotomic determinant.

Set

$$
S=\{2,\ell,\infty\},
\qquad
G_{\mathbf Q,S}=\operatorname{Gal}(\mathbf Q_S/\mathbf Q). \tag{1.2}
$$

All finite ramification is therefore already controlled by $G_{\mathbf Q,S}$.
At finite primes outside $S$, the implicit condition on both
modules is unramified; these prime-to-$\ell$ subspaces are exact local Tate
orthogonals. There is no auxiliary-prime branch in this book.

### 1.2 Coefficients and local conditions

Put

$$
M=\operatorname{ad}^0\bar\rho. \tag{1.3}
$$

Because $2\in k^\times$, trace splits the full adjoint and the trace
pairing is perfect on $M$:

$$
\operatorname{ad}\bar\rho=kI\oplus M,
\qquad
(X,Y)\longmapsto\operatorname{tr}(XY). \tag{1.4}
$$

Thus the Tate dual is

$$
M'=M^*(1)\simeq M(1). \tag{1.5}
$$

At finite places local Tate duality supplies perfect pairings

$$
H^i(\mathbf Q_v,M)\times H^{2-i}(\mathbf Q_v,M')
\longrightarrow k. \tag{1.6}
$$

For vector spaces, $(-)^*$ denotes $\operatorname{Hom}_k(-,k)$. The
finite-group Pontryagin duals in Poitou--Tate are identified with these
$k$-linear duals through the finite-field trace; rescaling the resulting
local invariant does not change an orthogonal subspace. Arithmetic
Frobenius is used. At $2$, therefore, a Tate twist multiplies a Frobenius
eigenvalue by $2$.

The hardly-ramified tangent conditions are

$$
L_2=0,
\qquad
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),
\qquad
L_\infty=0. \tag{1.7}
$$

The coefficient-prime condition in (1.7) is the subspace of exact
coefficient-linear finite-flat self-extensions. It is not the unramified
subspace. For every finite $v$, define the dual condition by the exact
annihilator

$$
L_v^\perp
=\{y\in H^1(\mathbf Q_v,M'):
\langle x,y\rangle_v=0\text{ for all }x\in L_v\}. \tag{1.8}
$$

At infinity ordinary $H^1$ and modified $H^1$ are both zero, so the
orthogonal degree-one condition is also zero.

The two Selmer groups are

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\left(
H^1(G_{\mathbf Q,S},M)\longrightarrow
\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v
\right), \tag{1.9}
$$

and

$$
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=\ker\left(
H^1(G_{\mathbf Q,S},M')\longrightarrow
\bigoplus_{v\in S}H^1(\mathbf Q_v,M')/L_v^\perp
\right). \tag{1.10}
$$

Book 165, Theorem 4.1 and Section 4.3, prove that (1.9) is the tangent space
of the represented global hardly-ramified fixed-determinant functor. The
supported complex below does not replace that tangent calculation; it
extends the same kernel into adjacent cohomological degrees.

### 1.3 What this book proves

The two structural outputs are

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*, \tag{1.11}
$$

and

$$
\dim_k H^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim_k H^1_{\mathrm{hr}^\perp}(\mathbf Q,M'). \tag{1.12}
$$

Consequently

$$
\boxed{
\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M).} \tag{1.13}
$$

The group on the left is defined by a mapping fibre in Chapter 4. Equation
(1.11), rather than a premature identification with ordinary global
$H^2$, is the reason it has the correct size.

## 2. The complete local ledger

Write

$$
h_v^i(N)=\dim_kH^i(\mathbf Q_v,N),
\qquad
h_S^i(N)=\dim_kH^i(G_{\mathbf Q,S},N). \tag{2.1}
$$

Every local dimension used later is calculated in this chapter. In
particular, the ambient group at $\ell$ is not assumed unobstructed.

### 2.1 The dyadic Frey-special profile

The residual inertial representation in the SP condition of Book 165,
Sections 2.1--2.2, has the form

$$
\bar\rho(\sigma)=1+\overline t_\ell(\sigma)\bar N,
\qquad
\bar N^2=0,
\qquad
\bar N\ne0. \tag{2.3}
$$

Its intrinsic line in the two-dimensional representation is

$$
\bar L=\ker\bar N=\operatorname{im}\bar N. \tag{2.4}
$$

The named SP datum retains this line and the split/nonsplit unramified sign.
The tame Frobenius relation is

$$
\bar F\bar N\bar F^{-1}=2\bar N. \tag{2.5}
$$

A trace-zero endomorphism commuting with a nonzero rank-one nilpotent is a
multiple of that nilpotent. Hence the line (2.4) in $\bar V$ and the
adjoint inertia-invariant line are distinct objects, with

$$
M^{I_2}=k\bar N,
\qquad
\phi(\bar N)=2\bar N. \tag{2.6}
$$

After the Tate twist, Frobenius acts by $4$ on $(M')^{I_2}$. Thus the
two relevant eigenvalues are

$$
\begin{array}{c|cc}
&M^{I_2}&(M')^{I_2}\\ \hline
\mathrm{SP}&2&4.
\end{array} \tag{2.7}
$$

For $\ell\ge7$, neither is $1$. It follows that

$$
H^0(\mathbf Q_2,M)=H^0(\mathbf Q_2,M')=0. \tag{2.8}
$$

The nonzero-monodromy normal form of Book 165 gives the fixed-determinant
unframed SP tangent directly, and it is zero. Thus

$$
L_2=0 \tag{2.10}
$$

The tangent calculation retains the nonlinear SP condition: nonzero
rank-one monodromy, the intrinsic line (2.4), the named sign, and the
Frobenius equation (2.5).

Local duality and (2.8) give

$$
H^2(\mathbf Q_2,M)=H^2(\mathbf Q_2,M')=0. \tag{2.11}
$$

Since $2\ne\ell$, the prime-to-coefficient local Euler formula is

$$
h_2^0(N)-h_2^1(N)+h_2^2(N)=0. \tag{2.12}
$$

Apply it to $M$ and $M'$. Equations (2.8) and (2.11) yield the complete
dyadic vanishing

$$
\boxed{
H^i(\mathbf Q_2,M)=H^i(\mathbf Q_2,M')=0
\quad(0\le i\le2).} \tag{2.13}
$$

In particular, the ambient and SP degree-one spaces have the same underlying
zero vector space at $2$; the SP deformation condition still retains its
full nonlinear data.

### 2.2 The coefficient prime

Let

$$
h_\ell=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V). \tag{2.14}
$$

The scalar/trace-zero splitting gives

$$
h_\ell^0(M)=h_\ell-1. \tag{2.15}
$$

Book 165, Theorem 3.1 and its tangent calculation in Section 3.3, proves that
the fixed-determinant coefficient-linear finite-flat tangent over
$\mathbf Z_\ell$ satisfies

$$
\dim_kL_\ell
=\dim_kH^1_{\mathrm{fl}}(\mathbf Q_\ell,M)
=h_\ell. \tag{2.16}
$$

Therefore its normalized contribution is always

$$
\dim_kL_\ell-h_\ell^0(M)=1. \tag{2.17}
$$

This identity retains the local centralizer parameter instead of silently
assuming local absolute irreducibility.

The mixed-characteristic local Euler formula is

$$
h_\ell^0(M)-h_\ell^1(M)+h_\ell^2(M)=-\dim_kM=-3. \tag{2.18}
$$

Local duality gives

$$
h_\ell^2(M)=h_\ell^0(M'). \tag{2.19}
$$

Combining (2.15), (2.18), and (2.19) gives

$$
h_\ell^1(M)=h_\ell+2+h_\ell^0(M'). \tag{2.20}
$$

Hence

$$
\dim_k\frac{H^1(\mathbf Q_\ell,M)}{L_\ell}
=h_\ell^0(M')+2. \tag{2.21}
$$

The right side is also $\dim_kL_\ell^\perp$, by perfect middle-degree
local duality. Equivalently,

$$
\dim_kL_\ell^\perp-h_\ell^0(M')=2. \tag{2.22}
$$

The primal and dual normalized corrections add to the three-dimensional
coefficient-prime bulk:

$$
\bigl(\dim L_\ell-h_\ell^0(M)\bigr)
+\bigl(\dim L_\ell^\perp-h_\ell^0(M')\bigr)=3. \tag{2.23}
$$

No vanishing of $H^2(\mathbf Q_\ell,M)$ has been used or proved. The exact
statement is (2.19). Book 165, Section 3.4, proves instead that the
obstruction map for the constrained finite-flat local functor is zero: every
admissible object lifts through a small extension. This distinction is
required by Book 167.

### 2.3 The real place and global invariants

Oddness gives eigenvalues $1$ and $-1$ for complex conjugation on
$\bar V$. Conjugation on $M$ fixes the traceless diagonal line and
negates the two off-diagonal lines. Consequently

$$
h_\infty^0(M)=1. \tag{2.24}
$$

The cyclotomic twist reverses these signs, so, for completeness,

$$
h_\infty^0(M')=2. \tag{2.25}
$$

Because $2\in k^\times$, averaging contracts every positive-degree
ordinary cochain and the complete Tate complex of $G_{\mathbf R}\simeq C_2$.
Thus

$$
H^i(\mathbf R,M)=H^i(\mathbf R,M')=0\quad(i>0),
\qquad
\widetilde H^i(\mathbf R,M)=\widetilde H^i(\mathbf R,M')=0
\quad(i\in\mathbf Z). \tag{2.26}
$$

The real degree-one condition is zero, but the ordinary invariant in (2.24)
still contributes

$$
\dim L_\infty-h_\infty^0(M)=-1 \tag{2.27}
$$

to Greenberg--Wiles. Complete real cohomology and ordinary real invariants
serve different terms and must not be interchanged.

Globally, absolute irreducibility and (1.4) give

$$
H^0(G_{\mathbf Q,S},M)=0. \tag{2.28}
$$

Restriction of a fixed vector is injective, and the dyadic target vanishes
by (2.8):

$$
H^0(G_{\mathbf Q,S},M')
\hookrightarrow H^0(\mathbf Q_2,M')=0. \tag{2.29}
$$

Therefore

$$
H^0(G_{\mathbf Q,S},M')=0. \tag{2.30}
$$

Absolute irreducibility alone proves (2.28), not (2.30); the latter uses the
Frey-special dyadic profile.

### 2.4 Local conditions and exact orthogonals

The complete normalized primal ledger is

$$
\begin{array}{c|c|c|c}
v&\dim L_v&h_v^0(M)&\dim L_v-h_v^0(M)\\ \hline
2&0&0&0\\
\ell&h_\ell&h_\ell-1&1\\
\infty&0&1&-1.
\end{array} \tag{2.31}
$$

As a dual consistency check, the corresponding corrections for $M'$ are
$0$, $+2$, and $-2$: use (2.22) at $\ell$ and (2.25) at infinity.
They also sum to zero, as they must after interchanging the two Selmer
structures.

The finite-place degree-one ledger is

$$
\begin{array}{c|c|c|c}
v&h_v^1(M)&\dim L_v&\dim L_v^\perp\\ \hline
2&0&0&0\\
\ell&h_\ell+2+h_\ell^0(M')&h_\ell&h_\ell^0(M')+2.
\end{array} \tag{2.32}
$$

At infinity both degree-one spaces are zero. The quotient--subspace
pairings

$$
\frac{H^1(\mathbf Q_v,M)}{L_v}\times L_v^\perp
\longrightarrow k \tag{2.33}
$$

are perfect. In particular, the dual coefficient-prime condition is the
exact annihilator in (1.8), not a condition guessed from the phrase
“finite flat.”

Since the ambient degree-one groups at $2$ and infinity vanish, the two
structures reduce explicitly to

$$
L_2=L_2^\perp=0,
\qquad
L_\infty=L_\infty^\perp=0,
\qquad
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),
\quad L_\ell^\perp=(L_\ell)^\perp. \tag{2.34}
$$

Consequently

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\left(H^1(G_{\mathbf Q,S},M)\to
H^1(\mathbf Q_\ell,M)/L_\ell\right), \tag{2.35}
$$

$$
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=\ker\left(H^1(G_{\mathbf Q,S},M')\to
H^1(\mathbf Q_\ell,M')/L_\ell^\perp\right). \tag{2.36}
$$

## 3. Cochain models for support

The Selmer kernel uses subspaces of $H^1$, whereas an obstruction class
needs cochains and local nullhomotopies. We now give the precise complexes
used in Books 167 and 181.

### 3.1 Positive local complexes

For a finite $v\in S$, let

$$
C_v^\bullet(M)=C^\bullet(G_{\mathbf Q_v},M) \tag{3.1}
$$

be the continuous inhomogeneous cochain complex. Write

$$
Z_v^1(M)=\ker(d:C_v^1(M)\to C_v^2(M)),
\qquad
B_v^1(M)=dC_v^0(M), \tag{3.2}
$$

and define

$$
Z_{L_v}^1(M)=\{z\in Z_v^1(M):[z]\in L_v\}. \tag{3.3}
$$

Since $B_v^1(M)\subseteq Z_{L_v}^1(M)$, there is a canonical two-term
positive complex

$$
U_v^+(M):
C_v^0(M)\xrightarrow{d}Z_{L_v}^1(M), \tag{3.4}
$$

in degrees $0$ and $1$, mapping to $C_v^\bullet(M)$. Its cohomology is

$$
H^0(U_v^+(M))=H^0(\mathbf Q_v,M),
\qquad
H^1(U_v^+(M))=L_v,
\qquad
H^i(U_v^+(M))=0\ (i\ne0,1). \tag{3.5}
$$

Retaining degree zero is essential: it records changes of local
rigidification. Choosing one cocycle representative of each class in
$L_v$ would not give a canonical subcomplex.

At infinity use the complete Tate complex
$\widetilde C_\infty^\bullet(M)$. It is acyclic by (2.26), and we take

$$
U_\infty^+(M)=0. \tag{3.6}
$$

This loses no supported cohomology. The ordinary invariant correction
$-h_\infty^0(M)$ belongs to the Euler formula, not to the acyclic complete
local complex.

### 3.2 Quotient local complexes

For finite $v$, define

$$
U_v^-(M)=\operatorname{Cone}
\bigl(U_v^+(M)\longrightarrow C_v^\bullet(M)\bigr), \tag{3.7}
$$

without a shift. The triangle

$$
U_v^+(M)\longrightarrow C_v^\bullet(M)
\longrightarrow U_v^-(M)\longrightarrow U_v^+(M)[1] \tag{3.8}
$$

and (3.5) give

$$
H^i(U_v^-(M))=0\qquad(i\leq0), \tag{3.9}
$$

$$
H^1(U_v^-(M))
\simeq H^1(\mathbf Q_v,M)/L_v, \tag{3.10}
$$

and

$$
H^2(U_v^-(M))
\simeq H^2(\mathbf Q_v,M). \tag{3.11}
$$

There is no higher cohomology at a finite place. At infinity put

$$
U_\infty^-(M)=\widetilde C_\infty^\bullet(M), \tag{3.12}
$$

which is acyclic here.

Equations (3.10) and (3.11) are the two required local coordinates. Degree
one detects failure of the tangent condition; degree two retains the
ambient local obstruction group. In particular, (3.11) does not delete the
possibly nonzero coefficient-prime group in (2.19).

### 3.3 The local duality check

Apply (3.4) to $M'$ and $L_v^\perp$. Exact orthogonality and local Tate
duality give perfect pairings

$$
H^1(U_v^-(M))\times H^1(U_v^+(M'))\longrightarrow k, \tag{3.13}
$$

$$
H^2(U_v^-(M))\times H^0(U_v^+(M'))\longrightarrow k. \tag{3.14}
$$

These pair every nonzero cohomology group in complementary local degree
two. Equivalently, in the derived category of $k$-vector spaces,

$$
U_v^-(M)
\simeq R\!\operatorname{Hom}_k(U_v^+(M'),k)[-2]. \tag{3.15}
$$

To justify the descent of the cup product, the composite pairing on the two
positive complexes is null in the derived category: its only possible
middle cohomology pairing is $L_v\times L_v^\perp$, which is zero by
definition. Over a field, the complexes split into their cohomology and
contractible summands, so the nullhomotopy and (3.15) exist without an
additional local theorem. The induced perfect pairings (3.13)--(3.14), which
are the only data used below, are independent of the splitting.

At infinity both complete complexes are acyclic, so the same assertion is
vacuous. This verifies the local hypothesis needed for supported duality.

## 4. The supported global complex

Book 69 isolates the two adjacent defects in a constrained global lifting
problem: an ambient global degree-two defect and a degree-one mismatch
modulo the allowed local tangents. The mapping fibre below realizes that
general shape for the exact hardly-ramified local complexes.

### 4.1 Definition and signs

Let

$$
C_S^\bullet(M)=C^\bullet(G_{\mathbf Q,S},M),
\qquad
Q_{\mathcal L}^\bullet(M)=\bigoplus_{v\in S}U_v^-(M). \tag{4.1}
$$

Localization followed by the quotient maps defines

$$
\lambda_{\mathcal L}:
C_S^\bullet(M)\longrightarrow Q_{\mathcal L}^\bullet(M). \tag{4.2}
$$

The supported complex is the mapping fibre

$$
C_{\mathcal L}^\bullet(\mathbf Q,M)
=\operatorname{Cone}(\lambda_{\mathcal L})[-1]. \tag{4.3}
$$

Thus

$$
C_{\mathcal L}^q(\mathbf Q,M)
=C_S^q(M)\oplus Q_{\mathcal L}^{q-1}(M), \tag{4.4}
$$

with differential

$$
d_{\mathcal L}(x,y)
=(dx,\lambda_{\mathcal L}(x)-dy). \tag{4.5}
$$

The sign is fixed by

$$
d_{\mathcal L}^2(x,y)
=(0,\lambda_{\mathcal L}(dx)-d\lambda_{\mathcal L}(x))=0. \tag{4.6}
$$

Define

$$
H^i_{\mathcal L}(\mathbf Q,M)
=H^i(C_{\mathcal L}^\bullet(\mathbf Q,M)), \tag{4.7}
$$

and use the subscript $\mathrm{hr}$ when $\mathcal L$ is the structure
in (1.7).

The equivalent single-cone form is

$$
\operatorname{Cone}\left(
C_S^\bullet(M)\oplus\bigoplus_{v\in S}U_v^+(M)
\xrightarrow{\operatorname{loc}-i}
\bigoplus_{v\in S}\widetilde C_v^\bullet(M)
\right)[-1]. \tag{4.8}
$$

Here finite places use ordinary cochains and infinity uses complete Tate
cochains. Formula (4.8) makes the phrase “global cochains with permitted
local boundary values” literal.

For comparison, compactly supported cochains are

$$
C_c^\bullet(G_{\mathbf Q,S},M)
=\operatorname{Cone}\left(
C_S^\bullet(M)\longrightarrow
\bigoplus_{v\in S}\widetilde C_v^\bullet(M)
\right)[-1]. \tag{4.8a}
$$

Setting every positive boundary coordinate to zero in (4.8) gives the
comparison triangle

$$
C_c^\bullet(G_{\mathbf Q,S},M)
\longrightarrow C_{\mathcal L}^\bullet(\mathbf Q,M)
\longrightarrow\bigoplus_{v\in S}U_v^+(M)
\longrightarrow C_c^\bullet(G_{\mathbf Q,S},M)[1]. \tag{4.8b}
$$

Thus supported cohomology is compact support with precisely the permitted
local boundary values restored. A literal zero positive complex means
compact support; it is not the same cochain model as a strict degree-one
condition at a finite place, whose positive complex still retains local
degree-zero automorphisms.

### 4.2 Its low-degree exact sequence

The defining triangle gives

$$
\cdots\longrightarrow H^i_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^i(G_{\mathbf Q,S},M)
\longrightarrow H^i(Q_{\mathcal L}^\bullet(M))
\longrightarrow H^{i+1}_{\mathcal L}(\mathbf Q,M)
\longrightarrow\cdots. \tag{4.9}
$$

Because every local quotient complex has zero cohomology in degrees at most
zero,

$$
H^0_{\mathcal L}(\mathbf Q,M)
\simeq H^0(G_{\mathbf Q,S},M)=0. \tag{4.10}
$$

Global cohomology above degree two vanishes for these odd-primary
coefficients, finite local cohomology vanishes above degree two, and the real
complete complex is acyclic. The central segment is therefore

$$
\begin{aligned}
0\longrightarrow{}&H^1_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^1(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v\\
\longrightarrow{}&H^2_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)\\
\longrightarrow{}&H^3_{\mathcal L}(\mathbf Q,M)
\longrightarrow0.
\end{aligned} \tag{4.11}
$$

For $\mathcal L=\mathcal L_{\mathrm{hr}}$, the first kernel in (4.11) is
exactly (1.9), so supported degree one is the hardly-ramified Selmer group.
Using the dyadic and real vanishings, (4.11) specializes to

$$
\begin{aligned}
0\longrightarrow{}&H^1_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow H^1(G_{\mathbf Q,S},M)
\longrightarrow H^1(\mathbf Q_\ell,M)/L_\ell\\
\longrightarrow{}&H^2_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow H^2(\mathbf Q_\ell,M)\\
\longrightarrow{}&H^3_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow0.
\end{aligned} \tag{4.12}
$$

No zero has been inserted after the local degree-one quotient, and the
coefficient-prime degree-two group has not been discarded.

### 4.3 What supported degree two contains

Return to $\mathcal L=\mathcal L_{\mathrm{hr}}$, and let

$$
\operatorname{loc}_s:
H^1(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v \tag{4.13}
$$

be singular localization, and put

$$
\Sha_S^2(M)=\ker\left(
H^2(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)
\right). \tag{4.14}
$$

Exactness gives

$$
0\longrightarrow\operatorname{coker}(\operatorname{loc}_s)
\longrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow\Sha_S^2(M)
\longrightarrow0. \tag{4.15}
$$

The first term is the failure of prescribed local degree-one corrections to
come from a global class. The last term is an ordinary global degree-two
class that dies locally. Supported degree two retains both defects and is
not canonically their direct sum.

Equation (4.15) is a cohomological statement. The assertion that actual
deformation-lifting factor sets define complete obstruction classes in this
group requires the affine local lift-torsor argument of Book 167 and is not
assumed here.

## 5. Poitou--Tate and supported duality

### 5.1 The exact sequence with its endpoint

For any finite local structure $\mathcal L=(L_v)$ of the present form,
Poitou--Tate gives

$$
\begin{aligned}
0\longrightarrow{}&H^1_{\mathcal L}(\mathbf Q,M)
\longrightarrow H^1(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}H^1(\mathbf Q_v,M)/L_v\\
\longrightarrow{}&H^1_{\mathcal L^\perp}(\mathbf Q,M')^*
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)\\
\longrightarrow{}&H^0(G_{\mathbf Q,S},M')^*
\longrightarrow0.
\end{aligned} \tag{5.1}
$$

The map from the local quotient to the dual Selmer dual is explicit. For
$(c_v)_v$ in the quotient and $y$ in the dual Selmer group, it is

$$
(c_v)_v\longmapsto
\left(y\longmapsto
\sum_{v\in S}\langle c_v,\operatorname{loc}_v(y)\rangle_v
\right). \tag{5.2}
$$

Changing $c_v$ by an element of $L_v$ does not change (5.2), precisely
because $\operatorname{loc}_v(y)\in L_v^\perp$. Global reciprocity kills
the image of a global class, and Poitou--Tate perfectness says that there is
no additional kernel.

The terminal group in (5.1) must be retained before using (2.30). It is the
endpoint that controls whether global degree-two localization is
surjective.

### 5.2 Perfect supported duality

Here is the comparison with all shifts visible. For $M'$ and the exact
orthogonal structure, (4.8b) is

$$
C_c^\bullet(M')\longrightarrow
C_{\mathcal L^\perp}^\bullet(M')\longrightarrow
\bigoplus_{v\in S}U_v^+(M')\longrightarrow.
$$

Apply $R\!\operatorname{Hom}_k(-,k)$, shift by $-3$, and rotate once.
The resulting triangle begins

$$
R\!\operatorname{Hom}_k(C_{\mathcal L^\perp}^\bullet(M'),k)[-3]
\longrightarrow
R\!\operatorname{Hom}_k(C_c^\bullet(M'),k)[-3]
\longrightarrow
R\!\operatorname{Hom}_k\left(\bigoplus_vU_v^+(M'),k\right)[-2]
\longrightarrow.
$$

Compactly supported global duality identifies the middle term with
$C_S^\bullet(M)$. The local comparison (3.15) identifies the third term
with $Q_{\mathcal L}^\bullet(M)$. These identifications give a morphism
from the defining triangle

$$
C_{\mathcal L}^\bullet(M)\longrightarrow
C_S^\bullet(M)\longrightarrow
Q_{\mathcal L}^\bullet(M)\longrightarrow
$$

to the dual triangle, with quasi-isomorphisms on the second and third
terms. The long exact cohomology sequences and the five lemma give a
quasi-isomorphism on the first terms. Taking cohomology gives perfect
pairings

$$
H^i_{\mathcal L}(\mathbf Q,M)\times
H^{3-i}_{\mathcal L^\perp}(\mathbf Q,M')
\longrightarrow k, \tag{5.3}
$$

or equivalently

$$
H^i_{\mathcal L}(\mathbf Q,M)
\simeq H^{3-i}_{\mathcal L^\perp}(\mathbf Q,M')^*. \tag{5.4}
$$

The degree shift is $3$: local Tate duality has complementary degree $2$,
and the global localization fibre contributes one more degree.

In the decisive degree,

$$
\boxed{
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*.} \tag{5.5}
$$

This does not pair the two degree-one Selmer groups directly. It pairs
supported degree two for the primal structure with degree one for the exact
orthogonal structure.

The endpoint degrees give

$$
H^0_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^3_{\mathrm{hr}^\perp}(\mathbf Q,M')^*,
\qquad
H^3_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^0_{\mathrm{hr}^\perp}(\mathbf Q,M')^*. \tag{5.6}
$$

By (2.28)--(2.30), all four groups in (5.6) vanish.

### 5.3 The specialized hardly-ramified sequence

Substitute (2.13), (2.26), and (2.30) into (5.1). The exact sequence becomes

$$
\begin{aligned}
0\longrightarrow{}&H^1_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow H^1(G_{\mathbf Q,S},M)
\longrightarrow H^1(\mathbf Q_\ell,M)/L_\ell\\
\longrightarrow{}&H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*
\longrightarrow H^2(G_{\mathbf Q,S},M)
\longrightarrow H^2(\mathbf Q_\ell,M)
\longrightarrow0.
\end{aligned} \tag{5.7}
$$

Comparing (4.12), with $H^3_{\mathrm{hr}}=0$, and (5.7) identifies their
middle extensions and recovers (5.5). It also gives the two compatible
short exact sequences

$$
0\longrightarrow\operatorname{coker}(\operatorname{loc}_s)
\longrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow\Sha_S^2(M)
\longrightarrow0, \tag{5.8}
$$

$$
0\longrightarrow\operatorname{coker}(\operatorname{loc}_s)
\longrightarrow H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*
\longrightarrow\Sha_S^2(M)
\longrightarrow0. \tag{5.9}
$$

Thus the cokernel of degree-one localization need not be the whole dual
Selmer dual. The possible $\Sha_S^2(M)$ quotient is exactly the additional
piece retained by supported degree two.

## 6. Euler characteristics and exact balance

### 6.1 Euler formulas with every exceptional term

For a finite $k[G_{\mathbf Q_p}]$-module $N$, the local Euler formulas
needed here are

$$
h_p^0(N)-h_p^1(N)+h_p^2(N)=0
\qquad(p\ne\ell), \tag{6.1}
$$

and

$$
h_\ell^0(N)-h_\ell^1(N)+h_\ell^2(N)
=-\dim_kN. \tag{6.2}
$$

For $M$ over $\mathbf Q$, the global formula is

$$
h_S^0(M)-h_S^1(M)+h_S^2(M)
=-\dim_kM+h_\infty^0(M). \tag{6.3}
$$

Equations (2.24), (2.28), and $\dim M=3$ reduce this to

$$
h_S^1(M)-h_S^2(M)=2. \tag{6.4}
$$

The $+h_\infty^0(M)$ in (6.3) and the $-\dim M$ in (6.2) are both
essential. Omitting the first loses the real correction; using (6.1) at the
coefficient prime loses the three-dimensional mixed-characteristic bulk.

### 6.2 Greenberg--Wiles calculation

Taking alternating dimensions in (5.1), then applying (6.1)--(6.3) and
local duality, gives the Greenberg--Wiles identity

$$
\begin{aligned}
&\dim_kH^1_{\mathcal L}(\mathbf Q,M)
-\dim_kH^1_{\mathcal L^\perp}(\mathbf Q,M')\\
&\qquad=
h_S^0(M)-h_S^0(M')
+\sum_{v\in S}\bigl(\dim_kL_v-h_v^0(M)\bigr).
\end{aligned} \tag{6.5}
$$

At infinity the summand in (6.5) uses ordinary $H^0(\mathbf R,M)$, even
though the complete local complex is acyclic.

For the hardly-ramified structure, (2.28), (2.30), and (2.31) give

$$
0-0+0+1-1=0. \tag{6.6}
$$

Therefore

$$
\boxed{
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M').} \tag{6.7}
$$

The cancellation is independent of the local centralizer dimension
$h_\ell$: (2.16) and (2.15) increase together.

### 6.3 An independent exact-sequence check

The specialized sequence (5.7) gives the same result without first
simplifying to (6.5). Its alternating dimension is

$$
\begin{aligned}
&\dim H^1_{\mathrm{hr}}-\dim H^1_{\mathrm{hr}^\perp}\\
&\quad=(h_S^1(M)-h_S^2(M))
-\dim\bigl(H^1(\mathbf Q_\ell,M)/L_\ell\bigr)
+h_\ell^2(M).
\end{aligned} \tag{6.8}
$$

Use (6.4), (2.21), and (2.19):

$$
2-\bigl(h_\ell^0(M')+2\bigr)+h_\ell^0(M')=0. \tag{6.9}
$$

This second computation checks simultaneously that the coefficient-prime
quotient has the correct dimension, the ambient $H^2$ term has not been
discarded, and the global real correction has already been included in
(6.4).

Finally, combine (5.5) and (6.7):

$$
\boxed{
\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M).} \tag{6.10}
$$

This is an equality of dimensions, not a vanishing statement.
In particular, the exact Greenberg--Wiles inequality needed downstream is

$$
\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
\leq\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M), \tag{6.11}
$$

and equality holds under every hypothesis of this book.

## 7. The theorem and the downstream contract

### 7.1 Supported hardly-ramified balance

**Theorem 7.1.** Under the hypotheses of Section 1.1, let $M$, $M'$,
and $\mathcal L_{\mathrm{hr}}$ be given by (1.3)--(1.8). Then:

1. the mapping fibre (4.3) is defined with differential (4.5);
2. its degree-one cohomology is the Selmer kernel (1.9);
3. its degree-two cohomology fits into (4.15);
4. supported duality gives the perfect duality (5.5);
5. $H^0_{\mathrm{hr}}=H^3_{\mathrm{hr}}=0$; and
6. the exact balance (6.10) holds.

**Proof.** Statements 1--3 are (4.3)--(4.15). Statement 4 is (5.5), and
Statement 5 follows from (2.28)--(2.30) and (5.6). The local ledger (2.31)
and Greenberg--Wiles prove (6.7); combining it with (5.5) proves Statement
6. $\square$

### 7.2 Interface to Books 167 and 181

Book 167 may use exactly the following outputs, with no additional
cohomological hypothesis.

1. The positive local complex is (3.4), including its degree-zero
   automorphisms.
2. The quotient complex is the unshifted cone (3.7).
3. The supported mapping fibre and its sign are (4.3)--(4.5).
4. The coefficient-prime ambient $H^2$ is retained as in (2.19) and
   (3.11); only the constrained finite-flat obstruction map is known to
   vanish.
5. Supported degree two is dual to the exact-orthogonal Selmer group by
   (5.5), and its dimension equals the tangent dimension by (6.10).

Book 167 supplies what is deliberately not proved here: it constructs the
factor-set plus local-nullhomotopy class, proves that its vanishing is
equivalent to an admissible global lift, and injects the dual minimal
relation space into supported degree two.

Book 181 may then combine the relation injection from Book 167 with (6.10)
to obtain a balanced presentation. Its later finiteness, flatness,
complete-intersection, horizontal-component, and characteristic-zero-point
arguments are logically downstream and are not inputs to this book.

For the Frey application, the SP condition in Section 1.1 is fixed.
Equations (2.3)--(2.6) show explicitly that the retained representation line,
adjoint line, Frobenius return, and twist eigenvalue are the SP data consumed
downstream.

### 7.3 Scope boundary

The following branches are intentionally absent because they are not used
in the Books 167 and 181 hardly-ramified lift:

- auxiliary-prime changes of Selmer structure;
- strict/relaxed comparison sequences unrelated to $\{2,\ell,\infty\}$;
- coefficient-field and controlling-set variation protocols;
- small-characteristic extensions of the theorem;
- scalar or local-shape case catalogues beyond the symbolic parameter
  $h_\ell$;
- relation bounds, deformation-ring dimension estimates, automorphy, and
  lift extraction.

The sole warning about excluded characteristics needed in the proof is
already visible in (2.7): the dyadic invariant calculation excludes
characteristics $2$ and $3$. The stated Frey range $\ell\ge7$ is
therefore more than sufficient for this calculation.

## 8. Source-closure audit

### 8.1 Direct dependency ledger

Every non-elementary input has an earlier source and its hypotheses are
matched below.

| source                                                                                                                        | exact input used here                                                                                                                                          | hypotheses matched here                                                                                                                                                  |
| ----------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Book 24, _Continuous Cohomology of Profinite Groups_, Chapters 2, 3, and 7                                                    | continuous cochains, low-degree cocycles, cup products, and signs                                                                                              | finite discrete continuous $k$-modules                                                                                                                                   |
| Book 30, _Local Galois Cohomology_, Sections 4, 6, and 8                                                                      | Frobenius description of unramified classes, local cohomological dimension, and both local Euler formulas                                                      | $2\ne\ell$ for (2.12); mixed characteristic at $\ell$ for (2.18)                                                                                                         |
| Book 31, _Tate Local Duality_, Sections 5, 8, and 10                                                                          | perfect pairings, $H^2(M)\simeq H^0(M')^*$, and quotient--orthogonal duality                                                                                   | finite local modules and $M'=M^*(1)$                                                                                                                                     |
| Book 32, _Global Galois Cohomology and Selmer Groups_, Sections 1, 3, 6, 9, and 13.3                                          | $G_{\mathbf Q,S}$, finiteness, Selmer kernels, exact orthogonal structures, and the adjoint-tangent dictionary                                                 | $S$ contains infinity, $\ell$, and every ramified finite place; fixed determinant uses $M=\operatorname{ad}^0\bar\rho$                                                   |
| Book 33, _Poitou--Tate Duality_, Sections 5, 6, 8, and 9                                                                      | complete real convention, compactly supported duality, (5.1), global Euler characteristic, and Greenberg--Wiles                                                | finite coefficients; exact local annihilators; complete Tate cochains at real places                                                                                     |
| Book 69, _Global Deformation Problems_, Sections 7--9                                                                         | fixed-determinant adjoint tangents, the mapping-fibre shape of constrained obstruction theory, and the distinction between ambient and constrained local $H^2$ | global Schur representation; $\ell\nmid2$; locally liftable conditions with their actual tangent subspaces                                                               |
| Book 165, _Local Conditions for Hardly-Ramified Minimal Deformations_, Theorems 2.2, 3.1, 4.1, and 6.1, and Sections 5.1--5.2 | SP line and Frobenius eigenvalues, $L_2=0$, $\dim L_\ell=h_\ell$, local liftability, and the global tangent kernel                                             | $\ell\ge7$; nonzero SP monodromy with intrinsic line and named sign; coefficient-linear finite flatness over $\mathbf Z_\ell$, weights $\{0,1\}$, cyclotomic determinant |

Cone calculations, the differential check (4.6), and the passage from an
exact sequence to an alternating dimension identity are proved explicitly
here and require no external theorem.

### 8.2 Closure and hypothesis flow

The dependency graph is

```text
Books 24 and 30--33 --- cochains, Euler formulas, local/global duality ---+
Book 69 -------- deformation tangent and obstruction shape --------+--> Theorem 7.1
Book 165 ------- local conditions and the dimension ledger --------+         |
                                                                           v
                                                                 Books 167 and 181
```

Every incoming edge comes from a book numbered below 166. Books 167 and 181
occur only as consumers in Section 7.2; no result from either is used to
prove Theorem 7.1. The SP local deformation theorem's own earlier
dependencies are discharged inside Book 165, so this book uses Book 165 as
its direct source rather than reopening its transitive local inputs.

The hypotheses also close under every use:

- $\ell\ge7$ makes $2$ invertible, excludes both eigenvalues in (2.7)
  from $1$, and makes the real complete complex acyclic.
- Absolute irreducibility is used only for the global invariant (2.28) and
  the fixed-determinant global problem.
- The Frey-special dyadic profile proves (2.8), hence the separate global
  twisted-invariant vanishing (2.30).
- Coefficient-linear finite flatness supplies (2.16) and constrained local
  liftability, but is never used to assert ambient $H^2=0$.
- Oddness supplies exactly the real invariant dimension (2.24).
- Exact local orthogonality, not equality of dimensions alone, supplies
  (3.13), (5.1), and (5.5).

Thus the proof of (6.10) is source-closed, noncircular, and contains every
local, global, real, and coefficient-prime term on which Books 167 and 181
depend.
