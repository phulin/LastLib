# Local--Global Compatibility for Weight-Two Galois Representations

## Contents

1. [The local information carried by a global representation](#1-the-local-information-carried-by-a-global-representation)
   - [1.1 The comparison problem](#11-the-comparison-problem)
   - [1.2 Standing fields and Frobenius conventions](#12-standing-fields-and-frobenius-conventions)
   - [1.3 The geometric carrier](#13-the-geometric-carrier)
   - [1.4 Scope and logical boundary](#14-scope-and-logical-boundary)
2. [The rank-two Weil--Deligne dictionary](#2-the-rank-two-weil--deligne-dictionary)
   - [2.1 From quasi-unipotent inertia to a pair](#21-from-quasi-unipotent-inertia-to-a-pair)
   - [2.2 Frobenius semisimplification](#22-frobenius-semisimplification)
   - [2.3 Unramified and special parameters](#23-unramified-and-special-parameters)
   - [2.4 Principal and tame dihedral parameters](#24-principal-and-tame-dihedral-parameters)
   - [2.5 Twists, duals, and determinants](#25-twists-duals-and-determinants)
3. [What a compatibility theorem must compare](#3-what-a-compatibility-theorem-must-compare)
   - [3.1 The automorphic local datum](#31-the-automorphic-local-datum)
   - [3.2 The geometric local datum](#32-the-geometric-local-datum)
   - [3.3 A rigidity criterion](#33-a-rigidity-criterion)
   - [3.4 Hecke isolation and exactness](#34-hecke-isolation-and-exactness)
4. [Good primes](#4-good-primes)
   - [4.1 The complete good-place ledger](#41-the-complete-good-place-ledger)
   - [4.2 Smooth proper specialization](#42-smooth-proper-specialization)
   - [4.3 The Frobenius polynomial](#43-the-frobenius-polynomial)
   - [4.4 Unramified local--global compatibility](#44-unramified-local--global-compatibility)
5. [Semistable curves and their packet parts](#5-semistable-curves-and-their-packet-parts)
   - [5.1 The weight complex of a nodal fiber](#51-the-weight-complex-of-a-nodal-fiber)
   - [5.2 Restricting monodromy to a multiplicity space](#52-restricting-monodromy-to-a-multiplicity-space)
   - [5.3 The zero-monodromy branch](#53-the-zero-monodromy-branch)
   - [5.4 The nonzero-monodromy branch](#54-the-nonzero-monodromy-branch)
6. [Steinberg compatibility](#6-steinberg-compatibility)
   - [6.1 The special parameter without square roots](#61-the-special-parameter-without-square-roots)
   - [6.2 Bad-prime Eichler--Shimura on the graph line](#62-bad-prime-eichler--shimura-on-the-graph-line)
   - [6.3 The split-Iwahori Steinberg theorem](#63-the-split-iwahori-steinberg-theorem)
   - [6.4 Split and nonsplit multiplicative signs](#64-split-and-nonsplit-multiplicative-signs)
7. [Tame descent and principal or special type](#7-tame-descent-and-principal-or-special-type)
   - [7.1 Restoring the descent action](#71-restoring-the-descent-action)
   - [7.2 Type projectors on the stratum complex](#72-type-projectors-on-the-stratum-complex)
   - [7.3 Principal and special recognition](#73-principal-and-special-recognition)
   - [7.4 The wild boundary](#74-the-wild-boundary)
8. [Tame dihedral types](#8-tame-dihedral-types)
   - [8.1 Quadratic induction](#81-quadratic-induction)
   - [8.2 The unramified quadratic case](#82-the-unramified-quadratic-case)
   - [8.3 The ramified quadratic case](#83-the-ramified-quadratic-case)
   - [8.4 The tame dihedral comparison criterion](#84-the-tame-dihedral-comparison-criterion)
9. [Raw cohomology and global semisimplification](#9-raw-cohomology-and-global-semisimplification)
   - [9.1 The two global representations](#91-the-two-global-representations)
   - [9.2 A sufficient passage criterion](#92-a-sufficient-passage-criterion)
   - [9.3 What the prior construction does not prove](#93-what-the-prior-construction-does-not-prove)
10. [Local factors, conductors, and epsilon factors](#10-local-factors-conductors-and-epsilon-factors)
    - [10.1 Euler factors](#101-euler-factors)
    - [10.2 Artin, Swan, and monodromy conductors](#102-artin-swan-and-monodromy-conductors)
    - [10.3 The basic rank-two calculations](#103-the-basic-rank-two-calculations)
    - [10.4 Epsilon factors](#104-epsilon-factors)
11. [Coefficient changes and the coefficient-prime boundary](#11-coefficient-changes-and-the-coefficient-prime-boundary)
    - [11.1 Extension of the coefficient field](#111-extension-of-the-coefficient-field)
    - [11.2 Rational projectors](#112-rational-projectors)
    - [11.3 The coefficient prime](#113-the-coefficient-prime)
12. [The geometric theorem and comparison criteria](#12-the-geometric-theorem-and-comparison-criteria)
    - [12.1 Complete statement](#121-complete-statement)
    - [12.2 Proof](#122-proof)
    - [12.3 Consequences](#123-consequences)
13. [Diagnostic calculations and false inferences](#13-diagnostic-calculations-and-false-inferences)
    - [13.1 A good prime](#131-a-good-prime)
    - [13.2 One loop and a separating node](#132-one-loop-and-a-separating-node)
    - [13.3 A tame dihedral parameter](#133-a-tame-dihedral-parameter)
    - [13.4 Equal conductors and unequal types](#134-equal-conductors-and-unequal-types)
14. [Dependency and hypothesis audit](#14-dependency-and-hypothesis-audit)
    - [14.1 Imported geometric results](#141-imported-geometric-results)
    - [14.2 Exact hypothesis ledger](#142-exact-hypothesis-ledger)
    - [14.3 Final synthesis](#143-final-synthesis)

## 1. The local information carried by a global representation

A global Galois representation is constructed from the cohomology of a variety, but its restriction at a finite place is controlled by the geometry of one integral fiber. Local--global compatibility is the assertion that this geometric restriction is the same local parameter that the automorphic packet prescribes. At a smooth fiber the assertion is a Frobenius polynomial. At a singular fiber it is much richer: one must compare finite inertia, nilpotent monodromy, Frobenius on the surviving invariant space, and the conductor.

There is a further distinction at bad reduction. Nearby cycles act on the **raw** cohomological multiplicity space. The global construction subsequently replaces that space by its semisimplification. Those operations do not automatically commute: global semisimplification can erase the unipotent extension from which local monodromy is recovered. This book will therefore state first what geometry proves for the raw carrier and will pass to the stated global representation only under the criterion of Chapter 9.

### 1.1 The comparison problem

Let $E$ be the field over which a selected Shimura curve is defined, let $u$
be a finite place of $E$, and let $v$ be the corresponding automorphic place.
Put $K=E_u$. A comparison with $\Pi_v$ is made only after the curve datum
supplies an identification

$$
K\xrightarrow{\sim}F_v
\tag{1.1}
$$

compatible with local reciprocity and geometric Frobenius. Without (1.1), the
two parameters live on different Weil groups; a residue-degree formula alone
does not make them comparable. A parallel-weight-two packet $\Pi$ gives, by
the cohomological extraction already established, a continuous raw
multiplicity representation

$$
W^{\mathrm{raw}}_{\Pi,\lambda}:G_E\longrightarrow
\operatorname{GL}_2(L_\lambda)
\tag{1.2}
$$

Here $L$ is a finite splitting field for the relevant Hecke algebra and
$\lambda\mid\ell$. The representation exported by the global construction is

$$
\rho_{\Pi,\lambda}
=\left(W^{\mathrm{raw}}_{\Pi,\lambda}\right)^{\mathrm{ss}}.
\tag{1.3}
$$

Restrict the raw carrier to $G_K$, with $u\nmid\ell$. The local monodromy theorem packages this restriction into a Weil--Deligne representation

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})
=(r^{\mathrm{raw}}_{u,\lambda},N^{\mathrm{raw}}_{u,\lambda}).
\tag{1.4}
$$

The automorphic local factor $\Pi_v$ supplies a centered parameter
$D_{\mathrm{LL}}(\Pi_v)$ in Book 76. Untwisted weight-two curve cohomology
uses the cohomological shift

$$
D^{\mathrm{coh}}(\Pi_v)
=D_{\mathrm{LL}}(\Pi_v)\otimes|\cdot|^{-1/2}.
\tag{1.5a}
$$

The half-power in (1.5a) is normalization bookkeeping; when a centered label
is displayed, the coefficient field is enlarged once to contain the needed
values. The split-Iwahori special formula itself is expressed by the algebraic
raw scalar $u_v$ and does not depend on a choice of $q^{1/2}$. We abbreviate
$D^{\mathrm{coh}}(\Pi_v)$ to $D(\Pi_v)$. Via (1.1), the comparison sought on
the raw carrier is

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq D(\Pi_v)\otimes_{L,\iota_\lambda}L_\lambda.
\tag{1.5}
$$

Frobenius semisimplification is essential. Good characteristic polynomials
cannot detect a unipotent extension in the Frobenius direction, while
monodromy must not be discarded. Equality (1.5) gives the same assertion for
$\rho_{\Pi,\lambda}$ only after the raw-to-global condition of Section 9.2
has been verified.

### 1.2 Standing fields and Frobenius conventions

Let $K$ be a nonarchimedean local field with residue field $k$ of cardinality $q$ and residue characteristic $p$. Write $G_K$, $I_K$, and $P_K$ for its absolute Galois group, inertia, and wild inertia. The Weil group fits into

$$
1\longrightarrow I_K\longrightarrow W_K
\xrightarrow{\nu}\mathbf Z\longrightarrow0.
\tag{1.6}
$$

We choose a lift $\Phi$ of **geometric Frobenius**, the inverse of $x\mapsto x^q$, and normalize

$$
\nu(\Phi)=1,
\qquad |w|=q^{-\nu(w)},
\qquad |\Phi|=q^{-1}.
\tag{1.7}
$$

Local reciprocity sends a uniformizer to geometric Frobenius. The Tate twist is fixed by

$$
\Phi\mid L_\lambda(1)=q^{-1}.
\tag{1.8}
$$

Thus a monodromy operator has the typed form

$$
N:V\longrightarrow V(-1),
\tag{1.9}
$$

and, after suppressing the target twist,

$$
r(\Phi)Nr(\Phi)^{-1}=q^{-1}N.
\tag{1.10}
$$

Arithmetic Frobenius is $\Phi^{-1}$. Its eigenvalues are the inverses of the geometric eigenvalues. Every polynomial and local factor below uses geometric Frobenius unless the word arithmetic is written explicitly.

For the extracted weight-two representation, the determinant is

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi,
\tag{1.11}
$$

where $\eta_\Pi$ is the finite central-component character. Write
$r^{\mathrm{glob}}_{u,\lambda}$ for the Weil part attached to
$\rho_{\Pi,\lambda}|_{G_K}$. Semisimplification preserves determinant.
Consequently, at a place where $\eta_\Pi$ is unramified and has geometric
Frobenius value $s_v(\Pi)$,

$$
\det r^{\mathrm{raw}}_{u,\lambda}(\Phi)
=\det r^{\mathrm{glob}}_{u,\lambda}(\Phi)
=q_us_v(\Pi).
\tag{1.12}
$$

### 1.3 The geometric carrier

A compact quaternionic Shimura curve contributes a packet block

$$
P_{\Pi,\lambda}\otimes W^{\mathrm{raw}}_{\Pi,\lambda},
\qquad \dim W^{\mathrm{raw}}_{\Pi,\lambda}=2,
\tag{1.13}
$$

and Galois acts on the raw multiplicity space
$W^{\mathrm{raw}}_{\Pi,\lambda}$.

For the FLT route, existence of this carrier is a theorem only in the exact
one-split range already established. Let $F$ be totally real of even degree,
fix the active real place, and let $\pi$ be a cuspidal full-group
parallel-weight-two packet. If there is an odd nonempty set $W$ of finite
places at which $\pi_w$ is selected special or selected tame dihedral, Book
104 constructs the packet on the quaternion algebra ramified at every other
real place and exactly at $W$. Book 125 realizes that packet in the $H^1$ of
the compact one-split curve, and Book 126 extracts (1.13). Principal-series,
primitive-wild, and excluded dyadic factors are not made eligible as members
of $W$ by this construction.

To study a particular finite place $v$ by the split-Iwahori geometry of Book
122 one must moreover choose this carrier with $v\notin W$, so that the
quaternion algebra is split at $v$, and impose the exact local tensor ledger
of Section 6.2. Thus the existence of some eligible carrier is not by itself
the existence of a split-Iwahori carrier at every desired $v$. In the
square-free FLT specialization a Steinberg place is eligible for $W$, whereas
a tame principal-series place is not. These qualifications are the carrier
boundary used below. In particular, if the desired split-Iwahori place $v$ is
the only eligible finite place, every nonempty eligible $W$ contains $v$ and
Book 104 supplies no one-split carrier that is split at $v$. The existence of
the curve carrier used for good-prime attachment does not close that bad-place
gap.

At a good place, the curve has a smooth proper integral model and ordinary specialization suffices. At a bad parahoric place, a verified rank-two lattice-chain local model gives a strict semistable curve after the explicit regularization. Nearby cycles then replace ordinary specialization. Prime-to-$p$ Hecke correspondences extend to these models and commute with inertia, Frobenius, restriction, Gysin, and monodromy.

### 1.4 Scope and logical boundary

The local results in this book require $u\nmid\ell$. They cover:

- good hyperspecial places;
- the completely split odd and dyadically tensor-split one-step rank-two
  Iwahori places of Book 122, including the Steinberg branch;
- recognition criteria for tame principal and tame scalar-special descent when
  its action on the geometric strata is retained;
- a recognition criterion for tame dihedral types whose quadratic cover,
  inducing character, and type projector occur in that descent complex.

No claim at $u\mid\ell$ follows from nearby cycles with $\ell$-adic coefficients. Primitive wild parameters and finite wild descent are outside the selected local correspondence. No general local Langlands theorem is asserted. No integral direct summand follows from a rational Hecke projector. Finally, bad-place assertions for $\rho_{\Pi,\lambda}$ require the raw-to-global passage of Chapter 9. These are theorem boundaries, not omissions to be filled by a change of notation.

## 2. The rank-two Weil--Deligne dictionary

Before comparing geometry and automorphic data, we need a recognition theorem for the possible rank-two parameters. The point is to know exactly which pieces of evidence determine the pair $(r,N)$.

### 2.1 From quasi-unipotent inertia to a pair

Let $V$ be a finite-dimensional $L_\lambda$-representation of $G_K$, with $\ell\ne p$. On an open subgroup $J\subset I_K$, inertia is unipotent. Choose the tame coordinate

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell(1)
$$

with

$$
t_\ell(w\sigma w^{-1})=|w|t_\ell(\sigma).
\tag{2.1}
$$

There is a unique nilpotent $N$ such that

$$
\rho(\sigma)=\exp(t_\ell(\sigma)N)
\qquad(\sigma\in J).
\tag{2.2}
$$

Removing this exponential by the crossed-homomorphism construction gives a representation $r$ of $W_K$ with finite inertial image and

$$
r(w)Nr(w)^{-1}=|w|N.
\tag{2.3}
$$

The isomorphism class is independent of the auxiliary extension of the tame coordinate. Scaling the coordinate rescales $N$ by a nonzero scalar, so its vanishing, rank, Jordan lengths, conductor, and local factors are unchanged.

For dimension two, $N^2=0$. Thus $N$ has rank zero or one. At split strict
semistable level, where the finite inertial part is trivial, this elementary
dichotomy leads exactly to an unramified or a special local parameter.

### 2.2 Frobenius semisimplification

The Weil representation $r$ need not be semisimple in the Frobenius direction. Write

$$
r(\Phi)=su=us
$$

for its multiplicative Jordan decomposition. The unipotent part $u$ commutes with the finite inertial image and with $N$. Define

$$
r^{\mathrm{F\!-\!ss}}(w)=r(w)u^{-\nu(w)}.
\tag{2.4}
$$

Then $r^{\mathrm{F\!-\!ss}}$ agrees with $r$ on inertia, sends $\Phi$ to $s$, and leaves $N$ unchanged. The construction is independent of the Frobenius lift up to isomorphism.

This operation is deliberately narrower than ordinary semisimplification. It retains finite inertia and nonzero monodromy. In particular, a special parameter remains indecomposable as a Weil--Deligne object.

### 2.3 Unramified and special parameters

An **unramified rank-two parameter** has $N=0$ and $r|_{I_K}=1$. It is determined, after Frobenius semisimplification, by

$$
\det(X-r(\Phi))=X^2-aX+b.
\tag{2.5}
$$

For $\beta\in\overline L^\times$, define the **special parameter** $\operatorname{St}(\beta)$ on a basis $e_0,e_1$ by

$$
Ne_1=e_0,\qquad Ne_0=0,
\tag{2.6}
$$

$$
r(i)=1\quad(i\in I_K),
\qquad
r(\Phi)e_0=\beta e_0,
\qquad
r(\Phi)e_1=q\beta e_1.
\tag{2.7}
$$

Equation (1.10) is immediate. This is the special block in an uncentered notation that avoids choosing $q^{1/2}$. Book 76 uses the centered block

$$
\operatorname{Sp}_2(\mu)
=\left(\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2},N\right),
\tag{2.8}
$$

with the same arrow $Ne_1=e_0$. Since geometric Frobenius acts on $\ker N$ by

$$
\mu(\Phi)q^{-1/2},
$$

the centered block by itself is $\operatorname{St}(\beta_{\mathrm{cen}})$
with

$$
\beta_{\mathrm{cen}}=\mu(\Phi)q^{-1/2}.
\tag{2.9}
$$

The cohomological shift (1.5a) multiplies both geometric-Frobenius roots by
$q^{1/2}$. Consequently the weight-two parameter used in this book is

$$
D(\operatorname{St}\otimes\mu)
=\operatorname{St}(\beta),
\qquad \beta=\mu(\Phi).
\tag{2.9a}
$$

Thus $\operatorname{St}(\beta)$ is notation for the shifted cohomological
parameter, whereas $\operatorname{St}\otimes\mu$ is the automorphic special
representation. Its determinant and Euler polynomial are

$$
\det r(\Phi)=q\beta^2,
\qquad
P(T)=1-\beta T.
\tag{2.10}
$$

**Proposition 2.1 (rank-two special recognition).** Let $(r,N)$ be a two-dimensional Frobenius-semisimple parameter with trivial finite inertia and $N\ne0$. If $\beta$ is the eigenvalue of $r(\Phi)$ on $\ker N$, then

$$
(r,N)\simeq\operatorname{St}(\beta).
\tag{2.11}
$$

**Proof.** Choose $e_0$ spanning $\ker N$ and choose $e_1$ with $Ne_1=e_0$. Since $N$ commutes with inertia and inertia is trivial, only Frobenius remains. Write $r(\Phi)e_0=\beta e_0$. From $r(\Phi)N=q^{-1}Nr(\Phi)$ we get

$$
N(r(\Phi)e_1)=q\,r(\Phi)Ne_1=q\beta e_0.
$$

Hence $r(\Phi)e_1=q\beta e_1+ce_0$. Frobenius semisimplicity and the distinct eigenvalues $\beta$ and $q\beta$ allow $e_1$ to be replaced by $e_1+c((q-1)\beta)^{-1}e_0$, killing the off-diagonal term. This gives (2.7). $\square$

Thus a special parameter is determined by nonzero monodromy and Frobenius on its one-dimensional kernel. Its determinant forces $\beta^2=b/q$.

Tame finite descent can coexist with special monodromy. Let
$\xi:I_K/P_K\to\overline L^\times$ be a finite character invariant under
Frobenius conjugation, and let $\delta\ne0$. Define
$\operatorname{St}(\xi,\delta)$ by

$$
r(i)=\xi(i)I,
\qquad
r(\Phi)e_0=\delta e_0,
\qquad
r(\Phi)e_1=q\delta e_1,
\tag{2.12}
$$

with $N$ as in (2.6). The Frobenius-invariance of $\xi$ is precisely what makes these formulas respect conjugation in $W_K$. An unramified extension of $\xi$ may be absorbed into $\delta$, so the notation records only the finite inertial character and the actual Frobenius eigenvalue on $\ker N$.

**Proposition 2.2 (special recognition with tame descent).** Let $(r,N)$ be a
two-dimensional Frobenius-semisimple parameter with $N\ne0$ and with
$P_K$ acting trivially. Then the finite inertia representation is scalar,
say $r(i)=\xi(i)I$ for a tame character $\xi$, and

$$
(r,N)\simeq\operatorname{St}(\xi,\delta),
\tag{2.13}
$$

where $\delta$ is Frobenius on $\ker N$.

**Proof.** The finite inertial image commutes with $N$. In a basis with $Ne_1=e_0$, the centralizer of $N$ consists of matrices

$$
\begin{pmatrix}a&b\\0&a\end{pmatrix}.
$$

Every element of a finite characteristic-zero matrix group is semisimple. Such a matrix is semisimple only when $b=0$, so inertia acts through a scalar character $\xi$. Frobenius conjugation preserves that character. The argument of Proposition 2.1 then puts Frobenius into the displayed diagonal form. $\square$

### 2.4 Principal and tame dihedral parameters

A **cohomologically normalized principal parameter** in the selected range is

$$
D(\chi_1,\chi_2)
=\left(\chi_1\oplus\chi_2,0\right).
\tag{2.14}
$$

The characters $\chi_i$ here already include the common shift (1.5a). The
unordered pair of Weil characters is the complete datum. Its inertial type
$\chi_1|_{I_K}\oplus\chi_2|_{I_K}$ is not complete because it forgets both unramified
parts. The common shift does not change their ratio. When that ratio is not
$|\cdot|^{\pm1}$, Book 76 matches the corresponding centered pair with the
normalized principal series. At the reducibility wall the shifted pair is

$$
\{\chi_1,\chi_2\}
=\{\mu,\mu|\cdot|^{-1}\},
\tag{2.15}
$$

where $\mu$ is the automorphic twisting character. The zero-monodromy
parameter is the cohomological shift of the character constituent
$\mu\circ\det$, while the shift of the special constituent
$\operatorname{St}\otimes\mu$ has the same two Weil characters joined by
nonzero $N$. This is why neither
inertial type nor semisimple Weil characters distinguish the principal boundary
from the special case.

Let $L/K$ be quadratic and let
$\theta^{\mathrm{cen}}:W_L\to\overline L^\times$ be the centered character
in Book 76's admissible pair. Put

$$
\theta=\theta^{\mathrm{cen}}|\cdot|_L^{-1/2}.
$$

The cohomologically normalized induced representation

$$
D(L/K,\theta)=\operatorname{Ind}_{W_L}^{W_K}\theta
\tag{2.16}
$$

has $N=0$ and is irreducible precisely when $\theta\ne\theta^\sigma$, where $\sigma$ is the nontrivial $K$-automorphism. We call it **dihedral** in that case. It is in the selected tame range only when $P_K$ acts trivially and the quadratic extension and character satisfy the tame hypotheses of Book 76. On the automorphic side the matching representation is the rectified induction

$$
\operatorname{AI}_{L/K}(\theta^{\mathrm{cen}}),
\tag{2.17}
$$

not the uncorrected compact type. The rectifier is already built into the
automorphic notation, and the selected correspondence gives

$$
D(\operatorname{AI}_{L/K}(\theta^{\mathrm{cen}}))
=\operatorname{Ind}_{W_L}^{W_K}\theta.
\tag{2.18}
$$

The restriction of $|\cdot|_K$ to $W_L$ is $|\cdot|_L$, so (2.18) is
exactly the shift (1.5a). The tame rectifier is already part of
$\operatorname{AI}$; it is not multiplied into $\theta^{\mathrm{cen}}$ or
$\theta$ a second time.

If $L/K$ is unramified, then $I_L=I_K$ and

$$
D(L/K,\theta)|_{I_K}\simeq
\theta|_{I_K}\oplus\theta^\sigma|_{I_K}.
\tag{2.19}
$$

If $L/K$ is ramified, then $I_L$ has index two in $I_K$ and the restriction is induced from $I_L$. These two cases must not be conflated: the same dimension and conductor can conceal different inertial structures.

The three displays (2.14), (2.13), and (2.18) are the entire selected local
correspondence used below. Primitive wild supercuspidals, ramified quadratic
extensions in residue characteristic two, and arbitrary finite-image parameters
are not included.

### 2.5 Twists, duals, and determinants

For a character $\mu$ of $W_K$,

$$
(r,N)\otimes\mu=(r\otimes\mu,N\otimes1).
\tag{2.20}
$$

An unramified twist changes Frobenius eigenvalues but neither type nor conductor. A Tate twist by $n$ is the unramified twist by $|\cdot|^n$:

$$
\operatorname{WD}(V(n))=\operatorname{WD}(V)\otimes|\cdot|^n.
\tag{2.21}
$$

Thus geometric Frobenius eigenvalues are multiplied by $q^{-n}$. The local Euler factor satisfies

$$
L(s,V(n))=L(s+n,V).
\tag{2.22}
$$

The dual is $(r^\vee,-{}^tN)$. The minus sign comes from differentiating the invariant evaluation pairing. The determinant has zero monodromy because $\operatorname{tr}N=0$. These formulas are sensitive checks that the cohomological representation has not accidentally been replaced by a covariant Tate module or by its dual.

## 3. What a compatibility theorem must compare

Naming both sides is not enough. We need a finite set of data which provably determines each parameter, and we need geometric correspondences that transport those data to the packet multiplicity space.

### 3.1 The automorphic local datum

In the selected weight-two range, the automorphic local datum is obtained from
Book 76 and then shifted as in (1.5a). It consists of one of the following
packages.

1. **Principal package:** an unordered pair of Weil characters
   $\{\chi_{1,v},\chi_{2,v}\}$ and $N=0$. In the spherical subcase both
   characters are unramified and are determined by the polynomial

   $$
   X^2-t_v(\Pi)X+q_vs_v(\Pi).
   \tag{3.1}
   $$

   At a ramified tame principal place, the two inertial characters and both
   Frobenius return scalars must be retained. At the reducibility wall, $N=0$
   selects the character constituent rather than the special constituent.

2. **Special package:** scalar finite inertia, a nonzero $N$, and the
   geometric-Frobenius scalar $\beta_v$ on the kernel line. In the unramified
   scalar case it satisfies

   $$
   \beta_v^2=s_v(\Pi).
   \tag{3.2}
   $$

   The associated parameter is $\operatorname{St}(\beta_v)$ in the uncentered
   notation of Section 2.3.

   More generally, the selected ramified special package includes a
   Frobenius-stable tame character $\xi_v$ of inertia and the kernel eigenvalue
   $\delta_v$; its parameter is $\operatorname{St}(\xi_v,\delta_v)$.

3. **Tame dihedral package:** a tame quadratic extension $L/K$, an admissible
   centered tame character $\theta_v^{\mathrm{cen}}$, its cohomological shift
   $\theta_v=\theta_v^{\mathrm{cen}}|\cdot|_L^{-1/2}$ with
   $\theta_v\ne\theta_v^\sigma$, and the
   rectified automorphic representation
   $\operatorname{AI}_{L/K}(\theta_v^{\mathrm{cen}})$. Its parameter is
   (2.18), including the
   value of $\theta_v$ on every required Frobenius return element.

The scalars and characters are part of the packet data over its coefficient
field. Although centered notation may require adjoining $q^{1/2}$, the
cohomological Frobenius roots, the unnormalized $U_v$ scalar used below, and
the induced cohomological parameter are algebraic packet data. An embedding
of the coefficient field into $L_\lambda$ transports every entry together; it
does not alter the identities among them.

This list is not shorthand for the general local Langlands correspondence.
It excludes primitive wild supercuspidals and any representation whose type is
not one of the three explicit rows above.

### 3.2 The geometric local datum

The geometric datum is extracted from a model. At a good place it consists of smooth proper specialization and the extended Hecke correspondence relation. At a semistable place it consists of:

$$
\left(
r|_{I_K},\ N,\
r(\Phi)\text{ on }(\ker N)^{I_K},\
\operatorname{Sw}(r)
\right).
\tag{3.3}
$$

The stratum complex supplies these data in the following order: finite descent acts on components and incidence orientations; restriction and Gysin maps determine the surviving subquotients; monodromy joins matching subquotients; Frobenius acts on their cohomology.

Only after this construction may a Hecke projector be applied. Counting nodes before taking graph cohomology can give a wrong rank for $N$.

### 3.3 A rigidity criterion

The following elementary lemma will close the tame principal and dihedral
comparisons once their actual return maps have been computed.

**Lemma 3.1 (finite-inertia rigidity).** Let $r_1,r_2$ be Frobenius-semisimple representations of $W_K$ over an algebraically closed characteristic-zero field. Suppose:

- $r_1|_{I_K}\simeq r_2|_{I_K}=\tau$;
- after choosing such an identification, the return maps induced by the appropriate power of Frobenius are conjugate on the multiplicity space of one representative of every Frobenius orbit of irreducible $I_K$-types.

Then $r_1\simeq r_2$.

**Proof.** Decompose $\tau$ into isotypic components. Frobenius permutes them because it normalizes inertia. On one orbit, choose a component $U$. A representation of the semidirect product generated by inertia and Frobenius is determined by the inertial action on the orbit and by the return map $\Phi^m:U\to U$, where $m$ is the orbit length. By Schur's lemma, on each irreducible multiplicity-one component this return map is a scalar; with multiplicity, it is a semisimple endomorphism of the multiplicity space. The stated agreement identifies these return maps. Inducing around every orbit gives an intertwiner, and their direct sum is an isomorphism. $\square$

For an irreducible dihedral representation the orbit is determined by $\theta$ and $\theta^\sigma$; one return scalar, equivalently the specified inducing character on a Frobenius lift in $W_L$, completes the parameter. In the unramified case, inertial type alone leaves an unramified-twist ambiguity.

### 3.4 Hecke isolation and exactness

Let $H$ be a cohomology group or the total cohomology of a stratum complex, and let a finite semisimple Hecke algebra $A$ commute with $W_K$ and $N$. For a simple module $P$ define the raw multiplicity space

$$
W^{\mathrm{raw}}=\operatorname{Hom}_A(P,H).
\tag{3.4}
$$

Evaluation gives $P\otimes W^{\mathrm{raw}}\simeq H[P]$. Because the Hom functor for a semisimple algebra is exact, kernels, images, and cohomology of the restriction--Gysin complex pass through (3.4). Moreover

$$
(N_{\mathrm{raw}}f)(p)=N_H(f(p))
\tag{3.5}
$$

defines the monodromy on $W^{\mathrm{raw}}$ when Galois acts trivially on $P$. Thus

$$
\ker N_{\mathrm{raw}}=\operatorname{Hom}_A(P,\ker N_H),
\tag{3.6}
$$

and similarly for images and invariant subspaces.

This argument is rational and computes the local parameter of the raw Hom
space. It says nothing by itself about the global semisimplification (1.3).
For an integral Hecke order, Hom need not be exact, and a rational projector
need not preserve the ambient lattice. Section 11.2 keeps that distinction
visible.

## 4. Good primes

Good-prime compatibility is the cleanest case, but even here the phrase “good prime” abbreviates several independent integral conditions.

### 4.1 The complete good-place ledger

Let $u$ and $v$ be identified as in (1.1), and let $p$ be their common
residue characteristic. We assume:

- $p$ is odd and the complete good-place ledger of Book 121 holds;
- the acting PEL algebra and its center are unramified at $p$;
- the relevant order is maximal and the involution is unramified;
- the alternating lattice is self-dual and the polarization degree is a unit;
- the local group scheme is reductive and the $p$-level is hyperspecial;
- the actual determinant local model is the required smooth projective line;
- the selected component union descends and is stable under the Hecke correspondences used;
- the prime-to-$p$ level is fine, or the argument is made rationally through a fine cover;
- the Shimura datum is in the compact anisotropic range, so the model is proper;
- $u\nmid\ell$.

Under exactly these hypotheses, the good integral-model theorem supplies a
smooth projective model $\mathscr X/\mathcal O_K$, all prime-to-$p$ Hecke
correspondences extend, and the chosen coefficient system extends lisse. This
good-place assertion makes no dyadic claim; the verified dyadic result in
this book is the bad one-step Iwahori theorem of Chapter 6.

### 4.2 Smooth proper specialization

**Proposition 4.1.** Under the good-place ledger, inertia acts trivially on
$W^{\mathrm{raw}}_{\Pi,\lambda}$ and on $\rho_{\Pi,\lambda}$, and both have
$N=0$.

**Proof.** Smooth proper base change gives a canonical, Hecke-equivariant isomorphism

$$
H^m(\mathscr X_{\bar k},L_\lambda)
\xrightarrow{\sim}
H^m(\mathscr X_{\bar K},L_\lambda).
\tag{4.1}
$$

The left side is acted on through the residue-field Galois group, so inertia is
trivial on the right side. The packet projector and multiplicity Hom commute
with (4.1), hence inertia is trivial on the raw extraction. It remains trivial
on every global subquotient, so it is also trivial on the semisimplification
(1.3). In the Weil--Deligne dictionary, a representation with trivial inertia
has trivial finite part and $N=0$. $\square$

The proof uses smoothness and properness. Proper base change without smoothness computes nearby cycles but does not make them constant.

### 4.3 The Frobenius polynomial

On untwisted curve $H^1$, the extended special-fiber correspondence gives

$$
\Phi_u^2-T_v\Phi_u+q_vS_v=0.
\tag{4.2}
$$

On the raw multiplicity space this becomes

$$
\Phi_u^2-t_v(\Pi)\Phi_u+q_vs_v(\Pi)=0.
\tag{4.3}
$$

The determinant theorem from the alternating cohomological pairing gives the
same determinant on the raw carrier and its semisimplification:

$$
\det(\Phi_u)=q_us_v(\Pi).
\tag{4.4}
$$

Semisimplification preserves characteristic polynomials. When $q_u=q_v$,
(4.3) and (4.4) therefore imply

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_vs_v(\Pi).
\tag{4.5}
$$

Indeed, subtracting (4.3) from Cayley--Hamilton yields $(\operatorname{Tr}\Phi_u-t_v)\Phi_u=0$; Frobenius is invertible, so its trace is $t_v$. This proof includes scalar Frobenius.

No formula is asserted here without the local identification (1.1). If only a
residue extension is given, one must first base change the automorphic
parameter and then compute the appropriate power of Frobenius; merely
replacing $q_v$ by $q_u$ in (4.5) is not valid.

### 4.4 Unramified local--global compatibility

**Theorem 4.2.** Under the good-place ledger and the local identification
(1.1),

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
$$

is the unramified parameter with Frobenius polynomial (4.5). Hence it equals
the unramified principal parameter $D(\Pi_v)$.

**Proof.** Proposition 4.1 gives trivial inertia and $N=0$. Frobenius
semisimplification preserves its characteristic polynomial. Equation (4.5)
determines a semisimple unramified representation of $W_K$, since $W_K/I_K$
is generated by $\Phi$. This is precisely the spherical subcase of the
principal package in Section 3.1. $\square$

The corresponding arithmetic-Frobenius polynomial is obtained by reciprocating the two roots. It is not (4.5) with $q$ merely replaced by $q^{-1}$; the middle coefficient is divided by the determinant as well.

## 5. Semistable curves and their packet parts

At a bad rank-two parahoric place, the integral model is no longer smooth. Its nodes create local vanishing cycles, but global monodromy is controlled by cycles in the dual graph rather than by the raw number of nodes.

### 5.1 The weight complex of a nodal fiber

Let $\mathscr C/\mathcal O_K$ be a proper strictly semistable curve with geometric special fiber

$$
Y=\bigcup_{a\in A}Y_a
$$

and dual graph $\Gamma$. The weight spectral sequence in degree one has three graded pieces

$$
H^1(\Gamma,L_\lambda),
\qquad
\bigoplus_a H^1(Y_a,L_\lambda),
\qquad
H_1(\Gamma,L_\lambda)(-1).
\tag{5.1}
$$

It degenerates at the second page by dimension. Monodromy is zero on the middle piece and identifies the two outer pieces through the graph pairing. Consequently

$$
N^2=0,
\qquad
\operatorname{rank}N=b_1(\Gamma).
\tag{5.2}
$$

The invariant-cycle map identifies

$$
H^1(Y,L_\lambda)\simeq
H^1(C_{\bar K},L_\lambda)^{I_K}=\ker N
\tag{5.3}
$$

at split strict level.

To see why nodes cannot simply be counted, take two components meeting at one point. The graph is an interval, so $b_1(\Gamma)=0$ and $N=0$. Two components meeting at $m$ points give $b_1=m-1$. The global restriction map removes one linear combination of the $m$ local vanishing generators.

### 5.2 Restricting monodromy to a multiplicity space

Prime-to-$p$ Hecke correspondences extend over the parahoric model and act on vertices, edges, component cohomology, restriction, and Gysin. Hence they commute with $N$. Let $P_\Pi$ be the finite Hecke module and let

$$
W^{\mathrm{raw}}_\Pi
=\operatorname{Hom}_A(P_\Pi,H^1(C_{\bar K},L_\lambda)).
\tag{5.4}
$$

Then (3.5) defines $N^{\mathrm{raw}}_\Pi$ and exactness gives

$$
\operatorname{rank}N^{\mathrm{raw}}_\Pi
=\dim\operatorname{Hom}_A
\left(P_\Pi,\operatorname{im}N\right).
\tag{5.5}
$$

Since $\dim W^{\mathrm{raw}}_\Pi=2$, the rank is zero or one. Formula (5.5),
rather than the total Betti number of $\Gamma$, decides which branch the raw
packet occupies. The phrase **raw packet graph multiplicity one** below means
that the right side of (5.5) has dimension one.

**Proposition 5.1.** At split strict semistable level, the raw packet
restriction is unramified if $N^{\mathrm{raw}}_\Pi=0$ and has special
Weil--Deligne form if $N^{\mathrm{raw}}_\Pi\ne0$.

**Proof.** Strict semistability makes wild inertia trivial and all inertia
unipotent. Thus the finite inertial representation $r|_I$ is trivial. If
$N^{\mathrm{raw}}_\Pi=0$, the exponential formula makes inertia trivial. If
$N^{\mathrm{raw}}_\Pi\ne0$, it has rank one and Proposition 2.1 applies.
$\square$

### 5.3 The zero-monodromy branch

The implication $N^{\mathrm{raw}}_\Pi=0\Rightarrow$ unramified is a statement
about the representation, not about smoothness of the model. A compact-type
singular curve can have a reducible special fiber and $N=0$ on all of $H^1$.
More commonly, the full curve has graph cycles but a selected packet projector
kills their Hecke-isotypic part.

At split strict level, zero monodromy means

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_\Pi)=(r,0),
\qquad r|_I=1.
\tag{5.6}
$$

The unramified parameter is then determined by Frobenius on the packet part of
$H^1(Y)$. Comparing it with a spherical principal parameter still requires a
verified Frobenius polynomial, obtained for example from a separately supplied
good carrier and a compatible level-change map. The singularity alone neither
provides that map nor forces the automorphic packet to be Steinberg.

### 5.4 The nonzero-monodromy branch

Assume $N^{\mathrm{raw}}_\Pi\ne0$. Put

$$
L_{\Pi,\mathrm{raw}}^{\mathrm{inv}}
=(\ker N^{\mathrm{raw}}_\Pi)^{I_K}.
\tag{5.7}
$$

At split strict level this is a line. Frobenius preserves it, so let $\beta_u$ be its eigenvalue. Proposition 2.1 gives

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_\Pi)^{\mathrm{F\!-\!ss}}
\simeq\operatorname{St}(\beta_u).
\tag{5.8}
$$

Assume the central-component character at $u$ has the value $s_v(\Pi)$ in the
common geometric-Frobenius normalization of (1.12). The global determinant
then supplies a valuable consistency check:

$$
q_u\beta_u^2
=\det r^{\mathrm{raw}}_{u,\lambda}(\Phi_u)
=q_us_v(\Pi),
$$

so

$$
\beta_u^2=s_v(\Pi).
\tag{5.9}
$$

Thus the only remaining automorphic comparison is the sign, or more generally
the finite central scalar, on the invariant line. For the exact split
one-step Iwahori ledger, Book 122 now supplies that equality by its
bad-prime Eichler--Shimura theorem; Chapter 6 records the normalization and
uses it. Outside that ledger the scalar remains additional local data. A
separate issue is whether this raw monodromy survives in
$\rho_{\Pi,\lambda}$, which Chapter 9 resolves in the residually absolutely
irreducible FLT range.

## 6. Steinberg compatibility

The word “Steinberg” summarizes a precise pair: one nonzero nilpotent arrow
and one Frobenius scalar on its kernel. The semistable geometry identifies the
nilpotent arrow. The Frobenius scalar requires the separate comparison
isolated below.

### 6.1 The special parameter without square roots

The parameter $\operatorname{St}(\beta)$ from (2.6)--(2.7) has one invariant line and one monodromy partner. Its semisimple Frobenius eigenvalues are

$$
\beta,\qquad q\beta.
\tag{6.1}
$$

They have weights $0$ and $2$ when $\beta$ has finite order, while their nonsplit monodromy extension is pure of weight one in the monodromy sense. This is not a contradiction: purity for a semistable representation is read on monodromy-graded pieces with shifted weights, not by demanding equal absolute values for the two eigenvalues of $r(\Phi)$.

The Euler polynomial and conductor are

$$
P(T)=1-\beta T,
\qquad a(\operatorname{St}(\beta))=1.
\tag{6.2}
$$

The determinant is $q\beta^2$. Hence a weight-two packet with central scalar $s_v$ can have special parameter only when $\beta^2=s_v$, exactly as (5.9) requires.

### 6.2 Bad-prime Eichler--Shimura on the graph line

The scalar comparison is now a theorem in the exact one-step Iwahori range.
Assume the direct quaternion-trace curve and decomposition-stable component
union of Book 122. At $v$, assume either its completely split odd ledger or
its dyadically tensor-split ledger; in the latter case $K\simeq\mathbf Q_2$.
Impose the oriented one-step Iwahori chain and the characteristic-zero packet
factorization

$$
H^1(C_{I,\bar K},L_\lambda)[\Pi]
\simeq P_{\Pi,I}\otimes W^{\mathrm{raw}}_{\Pi,\lambda},
\qquad \dim W^{\mathrm{raw}}_{\Pi,\lambda}=2,
\tag{6.3}
$$

with automorphic multiplicity one and the good-level support condition on the
two normalization components. Suppose
$\Pi_v=\operatorname{St}\otimes\mu_v$ with $\mu_v$ unramified.

Let

$$
U_v=(\pi_h)_*r_h^*=[IhI]
$$

be Book 122's incoming right-coset operator. It is the raw, unnormalized
operator: its generic degree is $q$, there is no inverse in the right action,
and there is no division by $q$ or $q^{1/2}$. Write $u_v$ for its eigenvalue
on the one-dimensional Iwahori new line and $s_v$ for the central $S_v$
eigenvalue. The local calculation gives

$$
u_v=\mu_v(\Phi),
\qquad u_v^2=s_v.
\tag{6.4}
$$

The transpose identity is $U_v^t=S_v^{-1}U_v$, so on the new line
$u_v^t=s_v^{-1}u_v=u_v^{-1}$. This checks pull--push variance without
altering the Frobenius scalar.

The centered Book 76 kernel root is $q^{-1/2}u_v$; after the weight-two shift
(1.5a), the cohomological kernel root is
$\beta_v=u_v$. Thus the phrase **geometric-normalized bad scalar** refers to
the comparison with geometric Frobenius on untwisted $H^1$, not to a
degree-normalized Hecke operator.

Book 122's bad-prime Eichler--Shimura theorem proves, after away-from-$v$
packet extraction, that the normalization-component term vanishes, both graph
multiplicities are one, $N$ has rank one, and

$$
\boxed{(\mathrm B_v)\qquad
\Phi_u\mid L_{\Pi,\mathrm{raw}}^{\mathrm{inv}}
=u_v=\beta_v.}
\tag{6.5}
$$

This is precisely the formerly missing scalar comparison. Its proof uses the
oriented-edge action of the actual $U_v$ correspondence, including
pull--push variance, component routing, and the identity/Frobenius versus
Frobenius/identity branch matrices. The determinant alone would give only
$\beta_u^2=\beta_v^2$ and would not choose the sign. Within the ledger above,
however, $(\mathrm B_v)$ is a proved conclusion, not an extra hypothesis.

### 6.3 The split-Iwahori Steinberg theorem

**Theorem 6.1 (split-Iwahori Steinberg compatibility).** Let $u\nmid\ell$
and assume the complete odd or dyadic split one-step Iwahori packet ledger of
Section 6.2. Then

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq\operatorname{St}(\beta_v).
\tag{6.6}
$$

In particular,

$$
N\ne0,\quad \operatorname{rank}N=1,\quad
a_u(W^{\mathrm{raw}}_{\Pi,\lambda})=1,
\tag{6.7}
$$

and

$$
L_u(s,W^{\mathrm{raw}}_{\Pi,\lambda})
=(1-\beta_vq_u^{-s})^{-1}.
\tag{6.8}
$$

In a basis $Ne_1=e_0$, geometric Frobenius is

$$
\Phi_ue_0=u_ve_0,
\qquad \Phi_ue_1=q_uu_ve_1,
\qquad \det(\Phi_u)=q_uu_v^2=q_us_v.
\tag{6.9}
$$

If the raw-to-global condition $(\mathrm R_u)$ of Section 9.2 also holds, the
same conclusions hold with $\rho_{\Pi,\lambda}$ in place of the raw carrier.
In the residually absolutely irreducible FLT situation of Corollary 9.3 this
passage is automatic.

**Proof.** Book 122 gives graph multiplicity one and rank-one raw monodromy.
Split strict semistability makes finite inertia trivial. Proposition 2.1
identifies the raw parameter as $\operatorname{St}(\beta_u)$, and the proved
identity (6.5) gives $\beta_u=u_v=\beta_v$. Equations (6.2), (6.4), and the
monodromy relation give (6.7)--(6.9). Condition $(\mathrm R_u)$ is exactly the
isomorphism needed to transfer the result to $\rho_{\Pi,\lambda}$. $\square$

This proof shows why “conductor one” is not by itself a Steinberg theorem. A nontrivial tame character with $N=0$ also has conductor one.

### 6.4 Split and nonsplit multiplicative signs

In the basic trivial-central-character case, (6.4) gives
$u_v^2=s_v=1$, so $\beta_v=u_v=\pm1$. The sign $+1$ is the split
multiplicative parameter, and $-1$ is its unramified quadratic twist. This is
the eigenvalue of the raw unnormalized $U_v$, not of $q^{-1}U_v$. The
nilpotent operator is nonzero and the conductor exponent is one in both
cases; the distinction lies in residue Frobenius on the graph orientation
line.

Thus nonsplit multiplicative reduction does not introduce ramified inertia. Its torus splits over an unramified quadratic extension, so inertia remains unipotent with trivial finite part, while Frobenius reverses the graph orientation. This is the model example showing that monodromy and Frobenius must be reported separately.

## 7. Tame descent and principal or special type

Strict semistability may appear only after a finite extension. The extension simplifies geometry, but its descent action contains genuine local type information and must be restored before compatibility is asserted over the original field.

### 7.1 Restoring the descent action

Let $K'/K$ be a finite Galois extension over which a strict semistable model exists. The geometric special fiber over $K'$ carries an action of the finite descent group. This action can:

- permute components and double intersections;
- reverse the orientation of graph edges;
- act on component cohomology;
- act on a coefficient system;
- in general, contribute a finite wild image.

Form the stratum complex equivariantly before taking invariants. The resulting local representation over $K$ separates as

$$
\text{finite inertia }r|_{I_K}
\quad\text{and}\quad
\text{nilpotent monodromy }N.
\tag{7.1}
$$

The two commute on inertia, but Frobenius scales $N$ by $q^{-1}$. Passing
first to a quotient graph can erase stabilizers and orientation characters and
therefore produce the wrong type. In this book the selected packet summand is
required to be trivial on $P_K$; the possible wild part of a general descent
action is retained by the geometry but is not identified with an automorphic
parameter here.

### 7.2 Type projectors on the stratum complex

Suppose a finite quotient $J$ of inertia acts on the semistable descent complex and $L$ splits $J$. For an irreducible character $\vartheta$ of $J$, the idempotent

$$
e_\vartheta=
\frac{\dim\vartheta}{|J|}
\sum_{g\in J}\operatorname{Tr}(\vartheta(g^{-1}))g
\tag{7.2}
$$

cuts out its isotypic part over $L$. Because the $J$-action commutes with restriction, Gysin, and prime-to-$p$ Hecke correspondences, the projector acts on the entire complex and its cohomology.

Integrally, the denominator $|J|$ matters. Rationally, however, (7.2) proves
that the finite inertia on a packet part is exactly the inertia representation
selected from the descent action. For the results below $J$ is a quotient of
tame inertia. If an automorphic type idempotent is identified with the same
$e_\vartheta$ under the model-level correspondence, the two inertial types
agree.

### 7.3 Principal and special recognition

**Theorem 7.1 (tame principal comparison criterion).** Let $u\nmid\ell$.
Assume a finite semistable extension and an equivariant strict semistable model
have been fixed. Let the packet projector and a local type projector extend to
the full stratum complex. Fix the principal parameter
$D(\chi_{1,v},\chi_{2,v})$ of (2.14), and suppose:

1. wild inertia acts trivially on the selected raw packet part;
2. the geometric type projector cuts out the sum of the two prescribed tame
   inertial characters; when they are distinct their inertial idempotents give
   the two lines, and when they coincide a separately supplied ordered
   Frobenius-stable line decomposition does so;
3. the restriction--Gysin monodromy vanishes on that part;
4. the normalized Frobenius return map on each character line is the value
   prescribed by $\chi_{1,v}$ or $\chi_{2,v}$.

Then

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq
\left(\chi_{1,v}\oplus\chi_{2,v},0\right),
\tag{7.3}
$$

after the chosen coefficient embedding. If $(\mathrm R_u)$ holds, the same
comparison holds for $\rho_{\Pi,\lambda}$.

**Proof.** The first two hypotheses identify the restrictions of the two Weil
representations to inertia. The third gives $N=0$. The fourth identifies the
Frobenius return maps. Lemma 3.1 then gives an isomorphism of
Frobenius-semisimple Weil representations. Condition $(\mathrm R_u)$ transfers
it to the global semisimplification. $\square$

If monodromy does not vanish, rank two makes the selected scalar-special case
equally rigid.

**Corollary 7.2 (tame descent with special monodromy).** Assume that wild
inertia is trivial on the selected raw packet part and that
$N^{\mathrm{raw}}_\Pi\ne0$. Then finite inertia acts through a
Frobenius-stable tame scalar character $\xi_u$. If the type projector
identifies it with the automorphic character $\xi_v$ and the normalized
geometric Frobenius action on $\ker N^{\mathrm{raw}}_\Pi$ is $\delta_v$, then

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq\operatorname{St}(\xi_v,\delta_v).
\tag{7.4}
$$

If $(\mathrm R_u)$ holds, the same comparison holds for
$\rho_{\Pi,\lambda}$.

**Proof.** Proposition 2.2 gives the scalar character and the special form.
The type projector identifies the character, while the kernel eigenvalue
identifies the remaining Frobenius scalar. Condition $(\mathrm R_u)$ gives
the last assertion. $\square$

Thus type alone never detects $N$, but type, monodromy, and kernel Frobenius
determine the selected tame special parameter completely.

### 7.4 The wild boundary

Strict semistability over $K'$ kills wild inertia on the unipotent factor, but
wild inertia over $K$ can survive in finite descent. Its identification would
require the entire finite wild action, its ramification filtration, and an
automorphic correspondence beyond the selected theorem of Book 76. None of
those is inferred from the tame type projector.

Accordingly Theorem 7.1 and Corollary 7.2 have no wild variant in this book.
If $P_K$ acts nontrivially on the selected packet part, the geometric descent
complex may still compute a candidate Weil--Deligne object, but no
local--global comparison is asserted. In particular, the results here do not
cover a primitive wild supercuspidal or a ramified quadratic induction in
residue characteristic two.

## 8. Tame dihedral types

Tame dihedral parameters are the irreducible quadratic-induced rank-two types
in the selected range. For Book 76's centered admissible-pair character
$\theta^{\mathrm{cen}}$, put
$\theta=\theta^{\mathrm{cen}}|\cdot|_L^{-1/2}$. Equation (2.18) matches the
cohomological parameter $\operatorname{Ind}_{W_L}^{W_K}\theta$ with the
rectified automorphic induction
$\operatorname{AI}_{L/K}(\theta^{\mathrm{cen}})$. The rectifier belongs in
the automorphic construction; inserting it again into either Weil character
would change the parameter. Recognition is an induction calculation, not a
conductor calculation.

### 8.1 Quadratic induction

Let $L/K$ be quadratic and choose $j\in W_K\setminus W_L$. On the induced space with coset basis $e,je$, an element $w\in W_L$ acts diagonally by

$$
r(w)=
\begin{pmatrix}
\theta(w)&0\\
0&\theta^\sigma(w)
\end{pmatrix}.
\tag{8.1}
$$

The element $j$ exchanges the two lines, with a return scalar determined by $\theta(j^2)$. Consequently the representation is irreducible exactly when the two characters differ. Its determinant is the product character on $W_L$, extended with the sign of the two-coset permutation.

Book 76's rectifier is normalized precisely so that the determinant of the
**centered** induction is the automorphic central character. The common
cohomological twist (1.5a) multiplies a rank-two determinant by
$|\cdot|^{-1}$. Therefore, when the central component is unramified with
geometric-Frobenius value $s_v$,

$$
\det D(\Pi_v)(\Phi)=q s_v,
\tag{8.1a}
$$

in agreement with (1.12). Adding a rectifier to the Weil character again
would generally destroy this determinant check.

This matrix description proves that the inducing character, including its value on a Frobenius return element, determines the entire parameter. It also displays why the unordered pair of inertial characters may not suffice.

### 8.2 The unramified quadratic case

If $L/K$ is unramified quadratic, then $I_L=I_K$ and geometric Frobenius $\Phi$ exchanges the two inertial characters. Its square is geometric Frobenius over $L$. In a suitable basis,

$$
r(\Phi)=
\begin{pmatrix}
0&\theta(\Phi_L)\\
1&0
\end{pmatrix},
\tag{8.2}
$$

up to exchanging the basis vectors. Hence

$$
\operatorname{Tr}r(\Phi)=0,
\qquad
\det r(\Phi)=-\theta(\Phi_L).
\tag{8.3}
$$

If the inertia characters are nontrivial, then $V^{I_K}=0$ and the Euler factor is $1$. The tame conductor is the codimension of invariants, usually $2$. If both inertia characters are trivial, the induced representation is reducible and belongs to the unramified principal range rather than the irreducible dihedral range.

### 8.3 The ramified quadratic case

If $L/K$ is ramified quadratic, $I_L$ has index two in $I_K$. The inertial representation is

$$
\operatorname{Ind}_{I_L}^{I_K}\theta|_{I_L}.
\tag{8.4}
$$

For a tame ramified quadratic extension, this is possible only when the ramification degree is prime to $p$; in residue characteristic two a ramified quadratic extension is not tame. The unramified quadratic extension remains available in every residue characteristic.

Geometric Frobenius can be chosen in $W_L$ because the residue degree is one. Its action on the two inducing lines has eigenvalues $\theta(\Phi_L)$ and $\theta^\sigma(\Phi_L)$, subject to the conjugation relation with inertia. Thus its trace and determinant need not have the form (8.3). This is a second reason the two quadratic cases require separate bookkeeping.

### 8.4 The tame dihedral comparison criterion

**Theorem 8.1 (tame dihedral comparison criterion).** Let $u\nmid\ell$, and
let the automorphic factor be
$\Pi_v=\operatorname{AI}_{L/K}(\theta_v^{\mathrm{cen}})$ in the selected
range of Book 76, and put
$\theta_v=\theta_v^{\mathrm{cen}}|\cdot|_L^{-1/2}$.
Assume the finite descent complex of the selected Shimura model contains the
quadratic cover $L/K$ and suppose:

- wild inertia acts trivially on the selected raw packet part;
- after restriction to $I_L$, the packet and type projectors cut out two
  rank-one lines on which $I_L$ acts through
  $\theta_v|_{I_L}$ and $\theta_v^\sigma|_{I_L}$;
- $\theta_v\ne\theta_v^\sigma$, and the descent element
  $j\in W_K\setminus W_L$ exchanges the two lines;
- monodromy vanishes on this packet summand;
- the return map $j^2$ and, when separate, geometric Frobenius in $W_L$, act
  by the values prescribed by $\theta_v$.

Then

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq
\operatorname{Ind}_{W_L}^{W_K}\theta_v.
\tag{8.5}
$$

If $(\mathrm R_u)$ holds, the same comparison holds for
$\rho_{\Pi,\lambda}$ and hence equals $D(\Pi_v)$.

**Proof.** The equivariant descent module gives the restriction to inertia, in
the form (2.19) or (8.4). Vanishing monodromy gives $N=0$. The exchange and
return maps supply the remaining entries in the induced matrices. Lemma 3.1,
or directly (8.1), identifies the Weil representations. Equation (2.18)
identifies this shifted induced parameter with the rectified automorphic
induction. Condition
$(\mathrm R_u)$ gives the assertion for the global semisimplification.
$\square$

The theorem is unchanged after extending the coefficient field enough to
contain the values of $\theta_v$. Its conductor and epsilon factor then agree
automatically because they are invariants of the same Weil--Deligne
representation. The theorem does not assert that every quadratic cover or
every two-dimensional finite inertia action is dihedral automorphic data; the
specified character lines, exchange, and return maps are load-bearing.

## 9. Raw cohomology and global semisimplification

Nearby cycles compute the local action on the raw cohomological Hom space.
The global representation named in the preceding book is its
semisimplification. This chapter records the exact bridge between those two
objects.

### 9.1 The two global representations

The cohomological extraction gives

$$
W^{\mathrm{raw}}_{\Pi,\lambda}
=\operatorname{Hom}_A(P_\Pi,H^1),
\qquad
\rho_{\Pi,\lambda}
=\left(W^{\mathrm{raw}}_{\Pi,\lambda}\right)^{\mathrm{ss}}.
\tag{9.1}
$$

Nearby cycles, the restriction--Gysin maps, and the logarithm of inertia are
functorial on the first representation. They therefore produce
$N^{\mathrm{raw}}_\Pi$. Global semisimplification is taken in the category of
$G_E$-representations, not in the category of representations of the local
decomposition group. It need not preserve a locally nonsplit extension.

The elementary warning is already visible in a two-dimensional unipotent
representation: a nonzero extension of the trivial character by itself has
nonzero logarithmic monodromy, while its semisimplification is the direct sum
of two trivial characters and has zero monodromy. Consequently equality of
global traces, determinants, or good Frobenius polynomials does not justify
replacing the raw carrier by (9.1) in a bad-place calculation.

### 9.2 A sufficient passage criterion

For a fixed $u\nmid\ell$, write

$$
\boxed{(\mathrm R_u)\qquad
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}.}
\tag{9.2}
$$

This is the exact hypothesis needed to transfer any bad-place computation in
Chapters 5--8 to the globally stated representation.

**Lemma 9.1 (safe raw-to-global passage).** Condition $(\mathrm R_u)$ holds
for every $u\nmid\ell$ if $W^{\mathrm{raw}}_{\Pi,\lambda}$ is globally
semisimple. In particular, it holds if
$\rho_{\Pi,\lambda}$ is absolutely irreducible.

**Proof.** In the first case the two representations in (9.1) are isomorphic.
For the second, a proper nonzero $G_E$-stable subspace of the two-dimensional
raw carrier would give at least two nonzero Jordan--Hölder factors in its
semisimplification. That contradicts irreducibility of
$\rho_{\Pi,\lambda}$. Hence the raw carrier is already irreducible and is
isomorphic to its semisimplification. Restriction to $G_{E_u}$ and formation
of the Weil--Deligne pair preserve an isomorphism. $\square$

The irreducibility used here must be proved independently of the bad-place
comparison. Using nonzero local monodromy to prove global irreducibility and
then invoking Lemma 9.1 to justify that same monodromy would be circular.

The FLT input provides a different, elementary route to irreducibility.

**Lemma 9.2 (absolute residual irreducibility lifts).** Let $V$ be a
two-dimensional representation of $G_E$ over a finite extension of
$\mathbf Q_\ell$, and let $\mathcal V\subset V$ be a stable full lattice. If
$\mathcal V/\mathfrak m\mathcal V$ is absolutely irreducible, then $V$ is
absolutely irreducible. Consequently:

1. if $V=\rho_{\Pi,\lambda}$, then
   $W^{\mathrm{raw}}_{\Pi,\lambda}$ is absolutely irreducible and
   $W^{\mathrm{raw}}_{\Pi,\lambda}\simeq\rho_{\Pi,\lambda}$;
2. if $V=W^{\mathrm{raw}}_{\Pi,\lambda}$, the same identification follows
   directly.

**Proof.** Suppose $V$ became reducible over an algebraic closure. After a
finite coefficient extension it would contain a $G_E$-stable line $D$.
Extend the lattice and intersect it with $D$. The intersection is a rank-one
stable saturated sublattice: if a uniformizer multiple of a lattice vector
lies in $D$, then the vector itself lies in the rational line $D$. Its
reduction is therefore a nonzero proper stable line in the scalar extension
of $\mathcal V/\mathfrak m\mathcal V$, contradicting absolute
irreducibility. Hence $V$ is absolutely irreducible.

For part 1, Lemma 9.1 shows that an absolutely irreducible
$\rho_{\Pi,\lambda}$ forces the raw carrier to be irreducible; a
two-dimensional irreducible characteristic-zero representation is
semisimple and equals its semisimplification. Part 2 is the same last
sentence applied directly. $\square$

**Corollary 9.3 (the FLT raw-to-global bridge).** Work at one coefficient
place in the selected FLT one-split curve range of Section 1.3. Suppose the
stable lattice in the attached representation reduces to the absolutely
irreducible residual representation specified by the FLT input. Then

$$
W^{\mathrm{raw}}_{\Pi,\lambda}
\simeq\rho_{\Pi,\lambda},
\tag{9.3}
$$

so $(\mathrm R_u)$ holds at every $u\nmid\ell$. The same conclusion follows
if absolute residual irreducibility is stated for the covariant Tate
realization used in the FLT normalization: Tate twist and duality preserve
absolute irreducibility.

**Proof.** Lemma 9.2 makes the characteristic-zero raw carrier absolutely
irreducible. Lemma 9.1 then identifies it with its global semisimplification,
so its restriction at every $u\nmid\ell$ satisfies $(\mathrm R_u)$. Duality
and Tate twist preserve absolute irreducibility, giving the covariant
formulation. $\square$

This is a coefficient-place-by-coefficient-place assertion. It does not say
that every residual member of a compatible family is absolutely irreducible,
and it does not remove the carrier and local-model hypotheses of Sections
1.3 and 6.2.

At a good place Theorem 4.2 does not require $(\mathrm R_u)$: smooth proper
base change makes inertia trivial on the entire raw carrier, and the
Frobenius characteristic polynomial survives semisimplification. This
argument does not extend to a singular fiber because the nilpotent operator is
not a characteristic-polynomial invariant.

### 9.3 What the prior construction does not prove

Book 126 defines $\rho_{\Pi,\lambda}$ by global semisimplification and
explicitly restricts its bad-place nearby-cycle calculation to the raw
multiplicity space. It does not prove $(\mathrm R_u)$ for every packet.
Books 22, 61, 75, and 121--122 are local or geometric inputs and do not
supply global irreducibility either.

In the FLT situation of Corollary 9.3, absolute residual irreducibility closes
the passage without using any local monodromy and hence without circularity.
For a packet or coefficient place outside that situation, an application at
a bad place must still provide one of the hypotheses in Lemma 9.1 or prove
(9.2) directly. No general semisimplicity statement is imported from Faltings
without its hypotheses and a proved route from the selected multiplicity Hom
space. Equality of conductors cannot fill this boundary. By contrast, the
former special-line scalar $(\mathrm B_v)$ is now proved by Book 122 under
the complete split one-step Iwahori ledger of Section 6.2.

## 10. Local factors, conductors, and epsilon factors

Once the full Weil--Deligne pair is identified, its standard local invariants agree formally. It is nevertheless useful to calculate them explicitly, both for applications and as a normalization audit.

### 10.1 Euler factors

For $D=(r,N)$ define

$$
V_N^I=(\ker N)^{I_K}
$$

and

$$
P(D,T)=\det(1-r(\Phi)T\mid V_N^I),
\qquad
L(s,D)=P(D,q^{-s})^{-1}.
\tag{10.1}
$$

The operator on $V_N^I$ is independent of the Frobenius lift. The kernel of $N$ is essential: using all inertia invariants would give the wrong Euler factor for a special parameter.

For an unramified parameter with Frobenius roots $\alpha,\beta$,

$$
P(T)=(1-\alpha T)(1-\beta T).
\tag{10.2}
$$

For $\operatorname{St}(\beta)$,

$$
P(T)=1-\beta T.
\tag{10.3}
$$

For a ramified tame dihedral parameter with no inertia invariants, $P(T)=1$.
These three degrees, two, one, and zero, offer a quick test that finite inertia
and monodromy have not been confused.

### 10.2 Artin, Swan, and monodromy conductors

For the finite-inertia representation $r$, let

$$
a(r)=\operatorname{codim}V^{I_K}+\operatorname{Sw}(r).
$$

The Weil--Deligne conductor is

$$
a(D)=a(r)+\dim V^{I_K}-\dim(\ker N)^{I_K},
\tag{10.4}
$$

equivalently

$$
a(D)=\operatorname{Sw}(r)+\dim V-
\dim(\ker N)^{I_K}.
\tag{10.5}
$$

At split strict semistable level, finite inertia and Swan vanish, so

$$
a(D)=\operatorname{rank}N.
\tag{10.6}
$$

After tame finite descent, (10.6) is generally false because the finite part
can remove additional invariants. A Swan term would also occur outside the
selected tame range, but no wild compatibility statement is made here.

### 10.3 The basic rank-two calculations

The cases used in the main theorem are:

$$
\begin{array}{c|c|c|c}
D&\dim V_N^I&N&a(D)\\ \hline
\text{unramified rank two}&2&0&0\\
\operatorname{St}(\beta)&1&\operatorname{rank}1&1\\
\chi_{\mathrm{tame}}\oplus\mu_{\mathrm{unr}}&1&0&1\\
\text{tame irreducible dihedral, }V^I=0&0&0&2
\end{array}
\tag{10.7}
$$

Here $\chi_{\mathrm{tame}}$ is nontrivial on inertia and $\mu_{\mathrm{unr}}$ is unramified.

The third and fourth rows show why conductor one does not imply Steinberg and conductor two does not identify a dihedral type. The full inertia representation is necessary.

For a ramified special parameter $\operatorname{St}(\xi,\delta)$ with nontrivial finite inertial character $\xi$,

$$
a(\operatorname{St}(\xi,\delta))=2a(\xi).
\tag{10.8}
$$

Indeed, the underlying Weil representation is the direct sum of two unramified twists of $\xi$, so its conductor is $2a(\xi)$. Both $V^I$ and $(\ker N)^I$ vanish, so the monodromy correction in (10.4) is zero. This calculation explains why a ramified twist of a special parameter need not have conductor one.

For $D(L/K,\theta)$, the induction formula gives

$$
a_K(D(L/K,\theta))
=f(L/K)\bigl(a_L(\theta)+d(L/K)\bigr),
\tag{10.9}
$$

where $d(L/K)$ is the exponent of the different measured over $L$. In an unramified quadratic extension, $d=0$ and the conductor is transported from $\theta$. In a tame ramified quadratic extension, $d=1$ and the extension itself contributes.

### 10.4 Epsilon factors

Fix a nontrivial additive character $\psi$ and its self-dual Haar measure. The epsilon factor is

$$
\epsilon(s,D,\psi)
=\epsilon(s,r,\psi)
\det\left(-q^{-s}r(\Phi)\mid
V^{I_K}/V_N^I\right).
\tag{10.10}
$$

Thus a full isomorphism of Weil--Deligne parameters implies equality of epsilon factors for the same $\psi$ and measure. No separate sign argument is needed. Conversely, equality of conductor and epsilon factor does not imply equality of parameters.

For $\operatorname{St}(\beta)$ and an additive character of conductor zero, (10.10) is the determinant of $-q^{-s}r(\Phi)$ on the line spanned by $e_1$. Since that eigenvalue is $q\beta$,

$$
\epsilon(s,\operatorname{St}(\beta),\psi)
=-\beta\,q^{1-s}.
\tag{10.11}
$$

For an induced dihedral parameter, the induction formula includes the
quadratic lambda constant. Omitting it can preserve the conductor exponent
while changing the root number. Therefore equality of parameters is the clean
statement from which equality of the Euler, conductor, and epsilon invariants
defined above follows.

## 11. Coefficient changes and the coefficient-prime boundary

The comparison in this book is rational and away from the coefficient prime.
Only the two coefficient operations needed to state it correctly are recorded
here. Integral packet lattices and finite-flat quotients belong to Book 129.

### 11.1 Extension of the coefficient field

Let $L'/L$ be a finite extension and $\lambda'\mid\lambda$. For either
$V_{\Pi,\lambda}=W^{\mathrm{raw}}_{\Pi,\lambda}$ or
$V_{\Pi,\lambda}=\rho_{\Pi,\lambda}$, scalar extension gives

$$
\operatorname{WD}_u(V_{\Pi,\lambda})
\otimes_{L_\lambda}L'_{\lambda'}
\simeq
\operatorname{WD}_u
\left(V_{\Pi,\lambda}\otimes_{L_\lambda}L'_{\lambda'}\right).
\tag{11.1}
$$

Formation of the Weil--Deligne pair, kernels of $N$, inertia invariants, and
Frobenius semisimplification commutes with this scalar extension. It may be
used to split the two principal characters or to adjoin values of a tame
dihedral character without changing conductor, monodromy rank, or the truth
of compatibility.

Coefficient conjugation is a semilinear version of the same operation. If
$\sigma:L\hookrightarrow L'$ and $\Pi^\sigma$ is the conjugate packet, then
the conjugate block carries

$$
t_v\mapsto\sigma(t_v),\quad
s_v\mapsto\sigma(s_v),\quad
u_v=\beta_v\mapsto\sigma(u_v)=\sigma(\beta_v),
\tag{11.2}
$$

and similarly for $\chi_i$, $\xi$, $\delta$, and every value of
$\theta^{\mathrm{cen}}$ and $\theta$. In a centered presentation the chosen
half-power of $q$ is transported as part of the label. If one recenters using
a different square root after conjugation, the resulting unramified quadratic
factor must be absorbed into the centered character; the conjugated
cohomological character is still $\sigma(\theta)$, not a separately chosen
root. The graph boundary and monodromy maps are transported semilinearly with
the packet block, so their ranks are unchanged. In the special row,
conjugating $u_v^2=s_v$ gives
$\sigma(u_v)^2=\sigma(s_v)$ and
$\det\Phi=q\sigma(s_v)$. In the dihedral row, induction commutes with
coefficient change, while the functorial rectifier remains in
$\operatorname{AI}(\theta^{\mathrm{cen},\sigma})$; it is not inserted on the
Weil side. Hence every local pair used by Book 168 is transported as one
algebraic pair, rather than by separately choosing its Frobenius roots.

Coefficient extension or conjugation does not replace the geometric proof of
$(\mathrm B_v)$ in Book 122 and does not prove $(\mathrm R_u)$ outside the
criteria of Chapter 9.

### 11.2 Rational projectors

The packet and type projectors used in Chapters 3 and 7 act over
characteristic zero. The denominator $|J|$ in (7.2), a coarse-level
stabilizer order, or a denominator in the Hecke idempotent can prevent the
same projector from preserving an integral cohomology lattice. Nothing in the
rational Weil--Deligne comparison removes those denominators or produces an
integral direct summand. This observation is the only integral boundary needed
here.

### 11.3 The coefficient prime

All preceding local monodromy arguments assume $u\nmid\ell$. When $u\mid\ell$, the coefficient prime equals the residue characteristic and the tame logarithm construction used here no longer controls the representation. Smooth proper cohomology still exists, but crystalline, semistable, de Rham, or finite-flat conclusions require comparison theorems with their own integral hypotheses.

In particular, neither the good polynomial at places away from $\ell$ nor the
bad-prime Weil--Deligne calculation proves finite-flatness of a quotient at
$\ell$. That is a separate geometric or $p$-adic Hodge-theoretic input.

## 12. The geometric theorem and comparison criteria

We can now state the result in a form that separates unconditional geometric output from the extra local identifications needed in each automorphic case.

### 12.1 Complete statement

**Theorem 12.1 (selected weight-two local--global compatibility).**
Let $\Pi$ be a noncharacter parallel-weight-two packet occurring in the
selected compact quaternionic Shimura-curve cohomology. Let

$$
W^{\mathrm{raw}}_{\Pi,\lambda}:G_E\to
\operatorname{GL}_2(L_\lambda),
\qquad
\rho_{\Pi,\lambda}
=\left(W^{\mathrm{raw}}_{\Pi,\lambda}\right)^{\mathrm{ss}},
$$

with

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi.
$$

Let $u\nmid\ell$ be a finite place of $E$, put $K=E_u$, and let
$v$ be the corresponding automorphic place. Fix the local identification
(1.1), and assume the selected component union and every correspondence
actually invoked below descend over $K$. Every automorphic scalar, character,
and parameter below is transported to $L_\lambda$ through the fixed
coefficient embedding. Then:

1. **Good place.** If the complete ledger of Section 4.1 holds, then
   $\rho_{\Pi,\lambda}$ is unramified and

   $$
   \det(X-\rho_{\Pi,\lambda}(\Phi_u))
   =X^2-t_v(\Pi)X+q_us_v(\Pi).
   $$

   Hence it is compatible with the unramified principal parameter.

2. **Split semistable geometric output.** If the verified parahoric model is
   strict semistable over $K$, then the finite inertia of the raw carrier is
   trivial, $(N^{\mathrm{raw}}_\Pi)^2=0$, and
   $N^{\mathrm{raw}}_\Pi$ is the packet part of the graph
   restriction--Gysin map. If it vanishes, the raw carrier is unramified. If
   it is nonzero, it has rank one and

   $$
   \operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
   \simeq\operatorname{St}(\beta_u),
   $$

   where $\beta_u$ is geometric Frobenius on
   $L_{\Pi,\mathrm{raw}}^{\mathrm{inv}}$.

3. **Odd or dyadic split-Iwahori special comparison.** Suppose the complete
   packet and local-model ledger of Section 6.2 holds. Then Book 122 proves
   graph multiplicity one, rank-one $N$, and $(\mathrm B_v)$ for the raw
   unnormalized $U_v$. The raw parameter is
   $D(\Pi_v)=\operatorname{St}(\beta_v)$. Its conductor is one and its Euler
   factor is (6.8). If $(\mathrm R_u)$ also holds, the same compatibility and
   invariants hold for $\rho_{\Pi,\lambda}$.

4. **Tame principal comparison.** Under the ordered-character,
   type-projector, zero-monodromy, and Frobenius-return hypotheses of
   Theorem 7.1, the raw parameter is
   $(\chi_{1,v}\oplus\chi_{2,v},0)=D(\Pi_v)$. If
   $(\mathrm R_u)$ holds, the same is true for $\rho_{\Pi,\lambda}$.

5. **Tame scalar-special descent.** Under the hypotheses of Corollary 7.2,
   the raw parameter is $\operatorname{St}(\xi_v,\delta_v)=D(\Pi_v)$. If
   $(\mathrm R_u)$ holds, the same is true for $\rho_{\Pi,\lambda}$.

6. **Tame dihedral comparison.** Under the quadratic-character-line,
   exchange, zero-monodromy, and return-map hypotheses of Theorem 8.1, the raw
   parameter is
   $\operatorname{Ind}_{W_L}^{W_K}\theta_v=D(\Pi_v)$ for
   $\Pi_v=\operatorname{AI}_{L/K}(\theta_v^{\mathrm{cen}})$ and
   $\theta_v=\theta_v^{\mathrm{cen}}|\cdot|_L^{-1/2}$. If $(\mathrm R_u)$
   holds, the same is true for $\rho_{\Pi,\lambda}$.

7. **Raw-to-global passage.** In the selected FLT one-split carrier range,
   if the stable lattice has the absolutely irreducible residual reduction
   specified by the FLT input, Corollary 9.3 proves
   $W^{\mathrm{raw}}_{\Pi,\lambda}\simeq\rho_{\Pi,\lambda}$. Thus every bad
   comparison in parts 3--6 whose stated geometric package is available is a
   comparison for $\rho_{\Pi,\lambda}$ with no additional $(\mathrm R_u)$
   assumption. Outside that residual-irreducible situation, the displayed
   raw comparisons remain valid, but their transfer to
   $\rho_{\Pi,\lambda}$ requires exactly $(\mathrm R_u)$.

In every case where equality with $D(\Pi_v)$ has been obtained, Euler factors,
Artin and Swan conductors, monodromy ranks, and epsilon factors for a fixed
additive character and self-dual measure agree on the two sides. No assertion
is made for primitive wild or other local parameters outside these rows.

### 12.2 Proof

At a good place, the good integral-model theorem gives a smooth projective
model with extended Hecke correspondences. Smooth proper base change kills
inertia. The correspondence relation and the independently known determinant
give the characteristic polynomial, including the scalar case. This proves
part 1 without a raw-to-global hypothesis.

At a strict semistable curve place, nearby cycles give the three graded pieces
(5.1), and monodromy is the graph restriction--Gysin pairing. Hecke
functoriality lets the raw multiplicity Hom construction pass through that
complex. Since the raw space is two-dimensional, its monodromy has rank zero
or one. Strictness over $K$ makes finite inertia trivial. Proposition 5.1 and
Proposition 2.1 prove part 2.

Part 3 is Theorem 6.1: Book 122's oriented-edge calculation proves the former
scalar condition $(\mathrm B_v)$ with $\beta_v=u_v$, where $U_v$ is raw and
unnormalized. After tame
descent, the type projectors commute with every differential and with
monodromy. The prescribed inertial characters and Frobenius return maps
identify the whole Weil representation by Lemma 3.1, proving parts 4--5. The
quadratic character-line and exchange calculation of Chapter 8 proves part 6.
In every bad case, $(\mathrm R_u)$ is precisely the passage from the computed
raw parameter to the stated global semisimplification. Lemma 9.2 and
Corollary 9.3 prove this passage in part 7 from absolute residual
irreducibility, without using the local comparison itself.

Finally, the formulas of Chapter 10 depend only on the isomorphism class of
the Weil--Deligne parameter. Equality of parameters therefore gives equality
of all the listed local invariants. $\square$

### 12.3 Consequences

The theorem provides several useful equivalences, with the carrier always
specified.

At a split strict semistable curve place,

$$
\operatorname{WD}_u(W^{\mathrm{raw}}_{\Pi,\lambda})
\text{ is unramified}
\quad\Longleftrightarrow\quad
N^{\mathrm{raw}}_\Pi=0.
\tag{12.1}
$$

It does not follow that the model is smooth. The same equivalence for
$\rho_{\Pi,\lambda}$ requires $(\mathrm R_u)$, which is automatic under
Corollary 9.3. Under the special hypotheses,

$$
N^{\mathrm{raw}}_\Pi\ne0
\quad\Longleftrightarrow\quad
a_u(W^{\mathrm{raw}}_{\Pi,\lambda})=1
\tag{12.2}
$$

because finite inertia is trivial there. With $(\mathrm R_u)$, in particular
under Corollary 9.3, the same formula holds for $\rho_{\Pi,\lambda}$. Without trivial finite inertia, conductor one
can also arise from a tame principal character.

Compatibility is stable under unramified twists and coefficient extension. It
is also compatible with duality and Tate twists, provided both sides use the
same geometric-Frobenius convention. A Tate twist by $n$ multiplies every
geometric Frobenius eigenvalue by $q^{-n}$ and shifts the Euler variable as in
(2.22); it does not alter the conductor.

## 13. Diagnostic calculations and false inferences

Short calculations expose most normalization or hypothesis errors more effectively than slogans.

### 13.1 A good prime

Suppose $s_v=1$ and the good polynomial is

$$
X^2-a_vX+q.
$$

Then the geometric Frobenius roots have product $q$. Arithmetic Frobenius
has reciprocal roots, product $q^{-1}$, and trace $a_v/q$. Writing the same
polynomial for arithmetic Frobenius would violate the determinant formula.

Twisting by $(1)$ changes the geometric polynomial to

$$
X^2-q^{-1}a_vX+q^{-1}.
$$

This is the cohomological twist calculation. A covariant Tate-module convention introduces a dual as well; it cannot be reproduced by changing only the constant term.

### 13.2 One loop and a separating node

An irreducible rational special fiber with one self-node has dual graph with one loop. Its $H^1$ has one length-two monodromy block, so $N$ has rank one and the conductor is one at split strict level.

Two smooth components meeting at one separating node have a tree as dual graph. The special fiber is singular, but $N=0$ on $H^1$. If the component genera sum to the generic genus, all cohomology comes from the middle component term in (5.1). Thus “one node gives conductor one” is false.

Two components meeting at two nodes have $b_1=1$. Only one linear combination of the two local vanishing cycles survives globally. Again the conductor is one, not two.

### 13.3 A tame dihedral parameter

Let $L/K$ be unramified quadratic and choose a tame character $\theta$ such that $\theta|_I\ne\theta^\sigma|_I$ and neither is trivial. Then

$$
D=\operatorname{Ind}_{W_L}^{W_K}\theta
$$

is irreducible, $N=0$, and $D^I=0$. Hence $L(s,D)=1$ and $a(D)=2$. Geometric Frobenius has trace zero and determinant $-\theta(\Phi_L)$.

Changing $\theta(\Phi_L)$ by an unramified scalar leaves the inertial type and conductor unchanged but changes the determinant and parameter. This explicitly demonstrates why type plus conductor is not local--global compatibility.

### 13.4 Equal conductors and unequal types

The following pairs have equal conductor but different parameters:

- $\operatorname{St}(1)$ and a nontrivial tame character direct-summed with an unramified line can both have conductor one, but only the first has $N\ne0$;
- split and nonsplit multiplicative special parameters both have conductor one, but their invariant Frobenius eigenvalues are $1$ and $-1$;
- two tame dihedral parameters with the same inertial characters and different unramified twists have the same conductor and type but different Frobenius return scalars.

These examples justify the full comparison target $(r,N)$ and the insistence on Frobenius data.

## 14. Dependency and hypothesis audit

A claimed comparison is closed only if every imported statement is used within
its actual hypotheses and every transition between carriers is justified.
This chapter records that boundary explicitly.

### 14.1 Imported geometric results

The following prior results are used.

**Nearby cycles and monodromy (Book 22).** The low-dimensional nearby-cycle
theory supplies the semistable inertia formula, $N^2=0$ for curves, the
restriction--Gysin weight complex, the graph description, the conductor
formula, and equivariant finite descent. Its hypotheses are proper strict
semistability and coefficients prime to the residue characteristic. The
present book uses only its rational form.

**Semistable abelian varieties (Book 61).** The semistable
abelian-variety theory supplies the split versus nonsplit multiplicative
example used in Section 6.4: the unramified quadratic sign changes Frobenius
on the toric graph line without removing nonzero monodromy. It is used only
for an abelian or Jacobian realization, with $\ell\ne p$ and semistability
over the stated field.

**Weil--Deligne representations (Book 75).** The local parameter theory
supplies the Weil group convention, extraction and reconstruction of $(r,N)$,
Frobenius semisimplification, centered special blocks, inertial types,
conductor formulas, induction, Euler factors, and epsilon factors. Every
formula here uses its geometric-Frobenius and reciprocity normalization.

**Selected local correspondence (Book 76).** This is the source of the three
automorphic rows used here: principal parameters, centered special parameters,
and tame quadratic induction with the rectifier on the automorphic side. It
also supplies the reducibility-wall distinction. It explicitly excludes
primitive wild supercuspidals and ramified quadratic induction in residue
characteristic two. This dependency is indispensable; Book 75 alone names
parameters but does not identify them with automorphic representations.

**Good integral models (Book 121).** The good-model theorem supplies smooth
projective curve models at the verified odd places, extension of prime-to-$p$
Hecke correspondences, and smooth proper specialization. It is invoked only
under the unramified-order,
self-dual-lattice, hyperspecial-level, smooth-local-model, component-descent,
neatness, and anisotropy hypotheses listed in Section 4.1.

**Semistable Shimura models (Book 122).** The parahoric model theorem supplies
both the completely split odd and the dyadically tensor-split one-step
rank-two Iwahori curves, their two branches, graph complex, monodromy, and
exact degeneracy routes. Under its characteristic-zero multiplicity-one
packet and normalization-component support hypotheses, its bad-prime
Eichler--Shimura theorem proves that both graph multiplicities are one, $N$
has rank one, and geometric Frobenius on the invariant graph line is the raw
unnormalized $U_v$ scalar. This is exactly $(\mathrm B_v)$. It does not prove
an Ihara lemma or raw-to-global semisimplicity. Arbitrary parahoric,
merely rationally split dyadic, ramified-order, and wild local models are not
included.

**One-split carrier (Books 104 and 125).** Book 104's compact one-split inverse
theorem constructs the quaternionic packet only from an odd nonempty set of
selected special or selected tame-dihedral finite places. Book 125 realizes
that packet on the compact curve, proves multiplicity one and the rank-two
packet factorization, and supplies the good-level support used in Book 122.
For a split-Iwahori calculation at $v$, the chosen ramification set must avoid
$v$. This is the exact carrier qualification in Section 1.3.

**Cohomological extraction (Book 126).** The weight-two extraction theorem
supplies the raw rank-two multiplicity space, its global semisimplification,
the determinant datum, and the good Frobenius polynomial. It explicitly warns
that bad-place monodromy is computed on the raw space and may be lost under
global semisimplification. It does not prove $(\mathrm R_u)$.

No downstream FLT assembly theorem is a proof input here. The carrier is
supplied directly by Books 104 and 125, the raw extraction and determinant by
Book 126, and the cohomological normalization is fixed in Sections 1.1 and
2.3 above. The additional absolutely irreducible residual representation in
Corollary 9.3 is an explicit application hypothesis, not an output of the
carrier construction.

Thus the exact recommended direct dependency row is

$$
\boxed{128\mid22,61,75,76,104,121,122,125,126}.
$$

Book 76 is direct because it supplies the automorphic labels and their
centered normalization; Books 104 and 125 are direct because they supply the
eligible one-split packet, its curve realization, its multiplicities, and the
normalization-component support used in the bad-prime proof. None of these
three inputs is supplied by the other books in the displayed row.

### 14.2 Exact hypothesis ledger

| Conclusion | Required hypotheses | What fails without them |
|---|---|---|
| good-prime unramifiedness | verified odd Book 121 smooth proper PEL model, $u\nmid\ell$ | nearby cycles can be nonconstant; no dyadic good theorem is imported |
| good Frobenius polynomial | extended normalized correspondences, component stability, determinant formula | an operator relation may fail or remain only an annihilator |
| raw curve $N^2=0$ | proper strict semistable curve, rational packet Hom | the local model may have a different nearby-cycle complex |
| conductor equals rank $N$ | split strict semistability over $K$ | finite inertia and Swan terms are missing |
| odd or dyadic split-Iwahori special identification | complete Book 122 tensor, packet, support, and raw $U_v$ ledger; $(\mathrm B_v)$ is then a theorem | determinant gives only the square of the kernel scalar |
| split-Iwahori carrier at $v$ | eligible odd nonempty $W$ for Book 104 with $v\notin W$, then the Book 125 curve packet | an eligible carrier ramified at $v$ does not supply split-Iwahori geometry there |
| split-Iwahori carrier when $v$ is the only eligible place | impossible in the present one-split construction | every nonempty eligible $W$ contains $v$, so the carrier is ramified rather than split at the target place |
| any bad parameter for $\rho_{\Pi,\lambda}$ in the residual-irreducible FLT range | stable lattice with absolutely irreducible residual reduction | without irreducibility, global semisimplification can erase local monodromy |
| any bad parameter for $\rho_{\Pi,\lambda}$ outside that range | $(\mathrm R_u)$, for example independently proved global semisimplicity | no general Faltings semisimplicity input has been proved for the raw multiplicity Hom |
| tame principal parameter | two character lines, ordering where needed, $N=0$, and both return scalars | inertia alone forgets unramified characters and the boundary constituent |
| tame scalar-special parameter | scalar tame type, $N\ne0$, and kernel Frobenius | type alone does not distinguish $N=0$ from $N\ne0$ |
| tame dihedral parameter | tame quadratic cover, two character lines, exchange, return maps, $N=0$ | inertial characters leave an unramified ambiguity |
| cohomological special normalization | centered kernel root $q^{-1/2}u_v$, shift $\lvert\cdot\rvert^{-1/2}$, raw unnormalized $U_v$ eigenvalue $u_v$ | dividing $U_v$ by $q$ or $q^{1/2}$ breaks the Frobenius and determinant identities |
| coefficient conjugation | conjugate the packet block, all scalars and characters, and the rectified automorphic label together | separately choosing roots can break determinant and return-map identities |
| any selected automorphic label | the matching row of Book 76 | parameter recognition alone is not an automorphic correspondence |
| coefficient-prime statement | a residue-characteristic comparison theorem | prime-to-$p$ nearby-cycle arguments do not apply |

There is no circular use of a compatible-system theorem or a finite-flat
quotient theorem. The good-place theorem and the raw semistable computation
are closed under the dependencies above. Book 122 closes the former
$(\mathrm B_v)$ gap in its complete odd and dyadic split-Iwahori range.
Absolute residual irreducibility closes $(\mathrm R_u)$ in the stated FLT
range by elementary lattice theory. Outside that range $(\mathrm R_u)$ is
retained exactly. For tame principal, scalar-special, and dihedral places,
Chapters 7--8 are recognition criteria; they require the stated geometric
type and return-map data and do not construct those data for an arbitrary
packet.

### 14.3 Final synthesis

At a good place, smooth proper specialization kills inertia, and the Hecke
correspondence plus the determinant gives the full quadratic Frobenius
polynomial on $\rho_{\Pi,\lambda}$. This part of local--global compatibility
is unconditional under the good-place ledger.

At a semistable curve place, the dual graph and its restriction--Gysin pairing
compute monodromy on $W^{\mathrm{raw}}_{\Pi,\lambda}$. A surviving graph line
gives one nonzero nilpotent arrow. At an eligible odd or dyadic split
one-step Iwahori place, Book 122 proves graph multiplicity one and identifies
geometric Frobenius on its kernel with the raw unnormalized $U_v$ eigenvalue.
The centered kernel root is $q^{-1/2}u_v$, the weight-two cohomological root
is $u_v$, the partner is $qu_v$, and the determinant is $qu_v^2=qs_v$.

In the FLT range with absolutely irreducible residual reduction, the
characteristic-zero rank-two carrier is absolutely irreducible, hence already
semisimple. The raw and globally named representations are therefore the
same, so the special comparison just obtained survives unchanged. Outside
that range, $(\mathrm R_u)$ remains the exact conditional boundary. Tame
descent recognizes principal, scalar-special, and dihedral parameters only
after the exact character lines, exchange maps, and Frobenius returns have
been supplied; no wild or general local-correspondence claim is added.

Throughout, geometric Frobenius acts on a Tate twist by $q^{-1}$, monodromy
satisfies $FNF^{-1}=q^{-1}N$, and local Euler factors use $(\ker N)^I$.
Conductors and local constants follow from an identified parameter; they never
replace the scalar, carrier, or raw-to-global comparison. Coefficient
conjugation transports $t_v,s_v,u_v$, every tame character, and the dihedral
rectified label together, giving exactly the algebraic local pairs consumed
by Book 168. This is the proved good and split-Iwahori special comparison,
together with the stated principal, scalar-special, and tame-dihedral
recognition criteria, with every remaining boundary stated at the first
unsupported step.
