# The Eisenstein Ideal

## Contents

1. [The prime-level collision](#1-the-prime-level-collision)
   - [Boundary eigenvalues and cuspidal congruences](#11-boundary-eigenvalues-and-cuspidal-congruences)
   - [Conventions and exact scope](#12-conventions-and-exact-scope)
   - [The integer that governs the theory](#13-the-integer-that-governs-the-theory)
   - [The logical architecture](#14-the-logical-architecture)
2. [The integral Hecke algebra and the exact index](#2-the-integral-hecke-algebra-and-the-exact-index)
   - [The acting algebra](#21-the-acting-algebra)
   - [The Eisenstein series](#22-the-eisenstein-series)
   - [The Hecke--Fourier pairing](#23-the-hecke--fourier-pairing)
   - [The exact congruence theorem](#24-the-exact-congruence-theorem)
   - [Index and congruence ideal](#25-index-and-congruence-ideal)
3. [Cusps, components, and the multiplicative boundary](#3-cusps-components-and-the-multiplicative-boundary)
   - [The cuspidal divisor](#31-the-cuspidal-divisor)
   - [The weighted special fiber](#32-the-weighted-special-fiber)
   - [Exact specialization](#33-exact-specialization)
   - [The Shimura subgroup](#34-the-shimura-subgroup)
   - [What equal orders do not imply](#35-what-equal-orders-do-not-imply)
4. [Eisenstein primes and local completion](#4-eisenstein-primes-and-local-completion)
   - [Local factors of a finite Hecke algebra](#41-local-factors-of-a-finite-hecke-algebra)
   - [Rational support and the optimal quotient](#42-rational-support-and-the-optimal-quotient)
   - [Why the two projectors differ](#43-why-the-two-projectors-differ)
   - [The exact local congruence depth](#44-the-exact-local-congruence-depth)
5. [The selected finite-flat tower](#5-the-selected-finite-flat-tower)
   - [Construction by integral idempotents](#51-construction-by-integral-idempotents)
   - [Exact transition maps](#52-exact-transition-maps)
   - [Comparison with the selected quotient](#53-comparison-with-the-selected-quotient)
   - [Faithfulness and finite-level annihilators](#54-faithfulness-and-finite-level-annihilators)
6. [Admissible Eisenstein group schemes](#6-admissible-eisenstein-group-schemes)
   - [The two atoms](#61-the-two-atoms)
   - [From a residual flag to a flat filtration](#62-from-a-residual-flag-to-a-flat-filtration)
   - [Mixed extensions](#63-mixed-extensions)
   - [The dyadic boundary](#64-the-dyadic-boundary)
7. [The completed divisible group](#7-the-completed-divisible-group)
   - [Connected, etale, and multiplicative pieces](#71-connected-etale-and-multiplicative-pieces)
   - [Cuspidal and Shimura directions](#72-cuspidal-and-shimura-directions)
   - [Duality and height](#73-duality-and-height)
   - [Multiplicity one and Gorenstein boundaries](#74-multiplicity-one-and-gorenstein-boundaries)
8. [Eisenstein descent](#8-eisenstein-descent)
   - [Strict local conditions](#81-strict-local-conditions)
   - [Atomic vanishing](#82-atomic-vanishing)
   - [Devissage and component defects](#83-devissage-and-component-defects)
   - [Rank zero and finiteness](#84-rank-zero-and-finiteness)
   - [The exact torsion boundary](#85-the-exact-torsion-boundary)
9. [The cotangent lattice](#9-the-cotangent-lattice)
   - [Invariant differentials of an optimal quotient](#91-invariant-differentials-of-an-optimal-quotient)
   - [The saturated support ideal](#92-the-saturated-support-ideal)
   - [The completed comparison](#93-the-completed-comparison)
   - [Support operators as cotangent coordinates](#94-support-operators-as-cotangent-coordinates)
10. [Formal immersion at an oriented cusp](#10-formal-immersion-at-an-oriented-cusp)
    - [Why the cusp must be oriented](#101-why-the-cusp-must-be-oriented)
    - [The cotangent calculation](#102-the-cotangent-calculation)
    - [Separation in an odd cusp disk](#103-separation-in-an-odd-cusp-disk)
    - [Limits of the argument](#104-limits-of-the-argument)
11. [Exceptional primes and diagnostic levels](#11-exceptional-primes-and-diagnostic-levels)
    - [Trivial Eisenstein levels](#111-trivial-eisenstein-levels)
    - [Levels eleven, seventeen, and nineteen](#112-levels-eleven-seventeen-and-nineteen)
    - [The level prime and the coefficient prime](#113-the-level-prime-and-the-coefficient-prime)
    - [A normalization ledger](#114-a-normalization-ledger)
12. [The selected Eisenstein theorem](#12-the-selected-eisenstein-theorem)
    - [The theorem](#121-the-theorem)
    - [Proof](#122-proof)
    - [Dependency and hypothesis audit](#123-dependency-and-hypothesis-audit)
    - [Excluded strengthenings](#124-excluded-strengthenings)
13. [Conclusion](#13-conclusion)

## 1. The prime-level collision

### 1.1 Boundary eigenvalues and cuspidal congruences

Let $N$ be prime. The modular curve $X_0(N)$ has two rational cusps, denoted $0$ and $\infty$. A Hecke correspondence $T_q$ with $q\ne N$ has $q+1$ branches at the boundary, while the incoming level operator $U_N$ preserves the oriented difference of the cusps. The boundary therefore carries a one-dimensional system of eigenvalues

$$
T_q\longmapsto 1+q,
\qquad
U_N\longmapsto1.
\tag{1.1}
$$

A cusp form, by definition, vanishes at the boundary. Over a field of characteristic zero, a cuspidal eigenform cannot literally be the boundary eigenform. Integrally, however, the two systems can meet. If their Fourier coefficients agree modulo a positive integer $m$, the cuspidal and boundary branches have failed to separate over $\mathbf Z/m\mathbf Z$. The Eisenstein ideal is the algebraic record of that failure.

This collision has several geometric shadows. The cusp difference gives a rational torsion point on $J_0(N)$. The bad fiber at $N$ gives a component group. The covering $X_1(N)\to X_0(N)$ gives a diagonalizable kernel in the Jacobian. Completion at a prime dividing the congruence modulus selects a finite-flat torsion tower. Yet these objects are not interchangeable. A component is not a point of the identity component, a constant group is not a multiplicative group, and a local idempotent on an $\ell$-adic module need not be a rational projector on an abelian variety.

The aim of this book is to assemble the exact prime-level theorem while preserving those distinctions. We calculate the index of the Eisenstein ideal, relate the cusp to the component group, construct the selected optimal quotient and its completed torsion, carry out Eisenstein descent, and prove the cotangent statement that yields formal immersion at the outward point-level cusp. The entire discussion concerns this selected quotient. It does not establish complete multiplicity one, a full cuspidal--Shimura intersection theorem, or an exact description of all rational torsion on $J_0(N)$.

### 1.2 Conventions and exact scope

Put

$$
X=X_0(N),\qquad J=J_0(N),\qquad
c=[0]-[\infty]\in J(\mathbf Q).
\tag{1.2}
$$

The Hecke correspondence convention is source-to-quotient. Thus, for

$$
X\xleftarrow{\pi_1}Y\xrightarrow{\pi_2}X,
$$

the covariant action on divisor classes and on $J$ is $(\pi_2)_*\pi_1^*$. The operator at the level is the incoming $U_N$ for which

$$
U_Nc=c.
\tag{1.3}
$$

Arithmetic Frobenius is used on covariant Tate modules. At a good prime $q$ the Eichler--Shimura polynomial consequently has the form

$$
F_q^2-T_qF_q+q=0.
\tag{1.4}
$$

The integral cusp-form lattice is

$$
S=S_2(\Gamma_0(N);\mathbf Z),
\tag{1.5}
$$

interpreted as regular dualizing differentials on the compactified modular object. This interpretation is essential at $2$ and $3$: a single coarse $q$-expansion does not by itself remember stabilizer descent or saturation.

The faithful Hecke algebra $\mathbb T$ means the image of the operators on $S$, equivalently on the corresponding faithful Jacobian realization. We never confuse this image with the polynomial algebra on formal symbols. The ideal studied throughout is

$$
I=(T_q-(1+q):q\ne N)+(U_N-1)\subseteq\mathbb T.
\tag{1.6}
$$

Primes indexing Hecke operators are denoted $q$; a prime dividing the Eisenstein index is denoted $\ell$; a residue characteristic used for formal immersion is denoted $p$. This separation prevents the level prime, coefficient prime, and specialization prime from being silently identified. Indices $r,s$ on finite-flat groups record torsion exponents, not residue characteristics.

### 1.3 The integer that governs the theory

Define

$$
n_N=\operatorname{num}\left(\frac{N-1}{12}\right)
=\frac{N-1}{\gcd(N-1,12)}.
\tag{1.7}
$$

For every prime $\ell$,

$$
v_\ell(n_N)=\max\{0,v_\ell(N-1)-v_\ell(12)\}.
\tag{1.8}
$$

Thus $2$ is an Eisenstein prime exactly when $N\equiv1\pmod8$, while $3$ is an Eisenstein prime exactly when $N\equiv1\pmod9$. Every Eisenstein prime divides $N-1$, so

$$
\ell\mid n_N\quad\Longrightarrow\quad \ell\ne N.
\tag{1.9}
$$

The same integer will occur as a congruence modulus, the order of the cusp class, and the order of the component group. These agreements are theorems, not definitions. Their proofs come from different sources: two-cusp integral modular forms, an eta multiplier, and a weighted monodromy graph. Keeping those proofs independent prevents the desired index from being smuggled into its own calculation.

The five levels

$$
N\in\{2,3,5,7,13\}
\tag{1.10}
$$

have $n_N=1$. At these levels the prime-level Jacobian in question is zero. There is no Eisenstein maximal ideal and no selected quotient. All statements involving a choice $\ell\mid n_N$ are therefore empty, not exceptional counterexamples.

### 1.4 The logical architecture

The proof proceeds in a strict order.

First, the weight-two Eisenstein series and the integral two-cusp lattice determine the exact quotient $\mathbb T/I$. This calculation uses no rational torsion on $J$. Second, the modular unit and the weighted bad fiber compute the cusp and component groups and prove that specialization identifies them. The Shimura subgroup supplies a multiplicative constituent of the same order, but no intersection theorem is inferred.

Third, for each $\ell\mid n_N$, the complete local factor of $\mathbb T\otimes\mathbf Z_\ell$ gives an integral idempotent. Its rational support, a different construction, gives an optimal quotient $A_{\mathfrak m}$. The idempotent is applied separately to the torsion of $J$ and to the torsion of $A_{\mathfrak m}$, producing two honest finite-flat towers. Generic exactness gives a saturated comparison of their Tate lattices. Admissibility and ordinary-tower rigidity, not smoothness of an integral optimal kernel, identify the two towers level by level.

Fourth, the Eichler--Shimura polynomial and a radical filtration produce actual residual constant and cyclotomic factors. Schematic closure turns them into admissible finite-flat atoms. Strict Selmer vanishing, followed by a finite component correction, forces the selected Mordell--Weil rank to vanish. Finite generation then gives finiteness.

Finally, no primitivity assertion is made for the whole Néron cotangent lattice of the quotient. Instead, the saturated integral ideal supported on $E_{\mathfrak m}$ contains, at every residue prime $p$, an operator nonzero modulo $p$. Perfect Hecke--Fourier duality detects that operator by a form whose first coefficient is a unit, and the operator factors through the optimal quotient. This supplies exactly one primitive quotient cotangent direction and proves that the original oriented quotient map is a formal immersion. At an odd good prime, injectivity of torsion specialization combines with finiteness to separate rational sections in that cusp disk.

## 2. The integral Hecke algebra and the exact index

### 2.1 The acting algebra

Because $S$ is finite free over $\mathbf Z$, its faithful Hecke image $\mathbb T$ is a finite torsion-free commutative $\mathbf Z$-algebra. It is therefore finite free as a $\mathbf Z$-module. The distinction between an abstract operator algebra and its image matters: an index is meaningful only after the integral lattice and faithful image have been fixed.

For $m\ge1$, write $T_m$ for the usual operator, with the level convention

$$
T_{N^a u}=U_N^aT_u,
\qquad (u,N)=1.
\tag{2.1}
$$

If $f=\sum_{m\ge1}a_m(f)q^m\in S$, then

$$
a_1(T_mf)=a_m(f).
\tag{2.2}
$$

This formula is more than a convenient normalization. It says that all Fourier coefficients arise by translating one linear functional through the Hecke algebra. It is the bridge from a congruence of forms to a quotient of rings.

The ideal $I$ is generated by an infinite displayed family, but it is finitely generated because $\mathbb T$ is noetherian. Hecke relations also show that one may replace the good-prime generators by $T_m-\sigma_1^{(N)}(m)$, where

$$
\sigma_1^{(N)}(m)=\sum_{\substack{d\mid m\\N\nmid d}}d.
\tag{2.3}
$$

We retain the prime generators because they display the boundary character most clearly.

### 2.2 The Eisenstein series

The quasimodular defect of the level-one weight-two series cancels in the prime-level combination

$$
E_N(z)=G_2(z)-NG_2(Nz).
\tag{2.4}
$$

With the coefficient-one normalization,

$$
E_N(q)=\frac{N-1}{24}
+\sum_{m\ge1}\sigma_1^{(N)}(m)q^m.
\tag{2.5}
$$

Its constant terms at $\infty$ and $0$, in compatible Fricke frames, are $(N-1)/24$ and its negative. Moreover,

$$
T_qE_N=(1+q)E_N\quad(q\ne N),
\qquad U_NE_N=E_N.
\tag{2.6}
$$

The first identity follows by sorting divisors of an integer according to divisibility by $q$. The second follows directly from (2.5): deleting one power of $N$ from the index exactly matches the divisor sum with the $N$-part omitted. The Fricke relation $E_N|W_N=-E_N$ checks the opposite cusp constants and the incoming sign.

The rational constant term suggests a modulus dividing the numerator of $(N-1)/24$, but that guess loses one factor of $2$. In characteristic $2$, opposite residues coincide and one divided Hasse correction descends through the stabilizer. The exact obstruction is therefore the numerator of $(N-1)/12$. This is the first place where the genuine integral modular object, rather than a rational Fourier series, changes the answer.

### 2.3 The Hecke--Fourier pairing

Consider

$$
\langle t,f\rangle=a_1(tf),
\qquad t\in\mathbb T,\quad f\in S.
\tag{2.7}
$$

**Proposition 2.1.** The pairing (2.7) is perfect over $\mathbf Z$.

**Proof.** If $t$ pairs to zero with every $f$, then (2.2) applied after every Hecke translate shows that every Fourier coefficient of $tf$ is zero for every $f$. The $q$-expansion principle gives $tf=0$, and faithfulness gives $t=0$. Thus the map

$$
\mathbb T\longrightarrow\operatorname{Hom}_{\mathbf Z}(S,\mathbf Z)
$$

is injective.

It remains to rule out a finite index in the integral dual. Let

$$
L=\sum_{m\ge1}\mathbf Z a_m\subseteq S^\vee.
$$

The Hecke recurrences and (2.2) identify the image of $\mathbb T$ in $S^\vee$ with $L$. Compute the dual lattice of $L$ inside $S\otimes\mathbf Q$:

$$
L^\sharp
=\{f\in S\otimes\mathbf Q:a_m(f)\in\mathbf Z
\text{ for every }m\ge1\}.
$$

The integral $q$-expansion theorem identifies this set with $S$ itself: a rational cusp form with integral expansion lies in the saturated lattice of regular dualizing cusp forms. The dual lattice of $S^\vee$ is also $S$, by double duality. Two full lattices in one rational vector space with the same dual lattice are equal, so $L=S^\vee$. Thus the displayed injection is surjective and the pairing is perfect. $\square$

The saturation clause is decisive. Perfectness over $\mathbf Q$ would determine only the rank of $\mathbb T$; it would not calculate an integral index. At residue characteristics $2$ and $3$, saturation uses the stacky cusp charts and the dualizing lattice.

### 2.4 The exact congruence theorem

For an integer $m\ge1$, call a class $f_m\in S/mS$ an Eisenstein cusp class if it is normalized by $a_1(f_m)=1$ and

$$
a_k(f_m)\equiv\sigma_1^{(N)}(k)\pmod m
\qquad(k\ge1).
\tag{2.8}
$$

**Theorem 2.2.** An Eisenstein cusp class modulo $m$ exists if and only if $m\mid n_N$. When it exists, it is unique.

**Proof.** The integral two-cusp congruence theorem says that the nonconstant expansion of $E_N$ becomes the expansion of a regular cusp form modulo $m$ exactly when both boundary residues vanish in the integral dualizing lattice. At primes at least $5$, this is precisely the divisibility of $(N-1)/12$ after accounting for the width and residue normalization. At $3$, the Hasse filtration removes exactly $v_3(12)=1$ from $v_3(N-1)$. At $2$, stabilizer descent removes exactly $v_2(12)=2$, rather than $v_2(24)=3$. Thus the largest possible exponent at every prime is (1.8), so existence is equivalent to $m\mid n_N$.

If $f_m$ and $g_m$ are two such classes, all their coefficients agree. The integral $q$-expansion principle gives $f_m=g_m$. $\square$

The theorem is an all-coefficient statement. A Sturm bound can certify a proposed class, but finite checking alone does not prove that the class exists at the maximal modulus. The two-cusp calculation supplies existence and maximality.

### 2.5 Index and congruence ideal

**Theorem 2.3.** There is a canonical ring isomorphism

$$
\boxed{\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z.}
\tag{2.9}
$$

**Proof.** Take the Pontryagin dual of $\mathbb T/I$. By Proposition 2.1, a homomorphism $\mathbb T/I\to\mathbf Q/\mathbf Z$ corresponds to a rational class of cusp forms whose coefficient functional is killed by every generator of $I$. Formula (2.2) says exactly that its positive coefficients have the form

$$
a_m=\sigma_1^{(N)}(m)x,
\qquad x\in\mathbf Q/\mathbf Z.
$$

If $x$ has order $d$, write $x=a/d+\mathbf Z$ with $(a,d)=1$. Multiplication by the inverse of $a$ modulo $d$ converts the class into a normalized Eisenstein cusp class modulo $d$; conversely, scalar multiples of that normalized class realize every parameter of order dividing $d$. Theorem 2.2 therefore says that the allowed parameters are precisely

$$
x\in(\tfrac1{n_N}\mathbf Z)/\mathbf Z.
$$

Thus the dual of $\mathbb T/I$ is cyclic of order $n_N$, so $\mathbb T/I$ is finite of that order. Hecke relations make every operator congruent modulo $I$ to an integer, and hence the image of $1$ generates the quotient additively. The unique unital cyclic quotient of order $n_N$ is $\mathbf Z/n_N\mathbf Z$. $\square$

Thus the exact index is

$$
[\mathbb T:I]=n_N.
\tag{2.10}
$$

There are two related objects worth distinguishing. The ideal $I\subset\mathbb T$ is the Eisenstein ideal. The scalar congruence ideal on the boundary branch is the annihilator of the congruence module $\mathbb T/I$ inside $\mathbf Z$:

$$
\eta_E=\operatorname{Ann}_{\mathbf Z}(\mathbb T/I)=(n_N).
\tag{2.11}
$$

There is also a literal branch-crossing description. Let $\mathcal H$ be the abstract algebra generated by the Hecke correspondences, let $\mathcal H\to\mathbb T$ be its cuspidal action, and let $\epsilon:\mathcal H\to\mathbf Z$ be the boundary character (1.1). Its image in $\mathbb T\times\mathbf Z$ is the augmented algebra

$$
\mathbb T^{\mathrm{aug}}
=\mathbb T\times_{\mathbf Z/n_N\mathbf Z}\mathbf Z.
\tag{2.12}
$$

Every abstract operator gives a pair satisfying the displayed congruence. Conversely, the maximality in Theorem 2.2 says that two boundary scalars can accompany the same cuspidal operator exactly when their difference is a multiple of $n_N$. This proves (2.12). The intersection of the boundary branch with the complementary cuspidal branch therefore has scalar annihilator $(n_N)$, recovering (2.11).

After completion at $\ell\mid n_N$, its local length is

$$
\operatorname{length}_{\mathbf Z_\ell}
(\mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m})
=v_\ell(n_N),
\qquad \mathfrak m=(\ell,I).
\tag{2.13}
$$

Neither (2.9) nor (2.13) says that $I\mathbb T_{\mathfrak m}$ is principal, that $\mathbb T_{\mathfrak m}$ is a complete intersection, or that it is Gorenstein. The scalar congruence depth measures contact with the boundary character; it does not count generators of the cotangent space or branches of the local algebra.

## 3. Cusps, components, and the multiplicative boundary

### 3.1 The cuspidal divisor

The eta quotient

$$
u(z)=\left(\frac{\eta(z)}{\eta(Nz)}\right)^{24/\gcd(N-1,12)}
\tag{3.1}
$$

has trivial multiplier at level $N$ and divisor

$$
\operatorname{div}(u)=n_N([0]-[\infty]).
\tag{3.2}
$$

Hence $n_Nc=0$. This proves an upper bound for the order of $c$, but not exactness. Exactness comes from specialization at the level prime.

The boundary correspondence calculation gives

$$
T_qc=(1+q)c\quad(q\ne N),
\qquad U_Nc=c,
\qquad w_Nc=-c.
\tag{3.3}
$$

Thus $I$ annihilates the cyclic subgroup $C_N=\langle c\rangle$. Once its exact order is known, the map

$$
\mathbb T/I\longrightarrow C_N,
\qquad1\longmapsto c,
\tag{3.4}
$$

will be an isomorphism.

### 3.2 The weighted special fiber

For $N\ge5$, the stable coarse fiber of $X_0(N)$ at $N$ consists of two principal components meeting at supersingular points. Resolving a node attached to a supersingular elliptic curve $E$ produces a path of length

$$
e(E)\in\{1,2,3\}.
\tag{3.5}
$$

The values $2$ and $3$ occur at $j=1728$ and $j=0$ when those invariants are supersingular. These lengths encode the effective automorphisms of the corresponding stacky point; inserting them unconditionally would give the wrong component group.

The weighted mass formula and exceptional product are

$$
\sum_E\frac1{e(E)}=\frac{N-1}{12},
\qquad
\prod_Ee(E)=\frac{12}{\gcd(N-1,12)}.
\tag{3.6}
$$

The dual graph is a weighted theta graph. Its degree-zero vertex lattice maps to its dual by the weighted Laplacian. The discriminant group is the cokernel of that map. Effective resistance between the two principal vertices equals

$$
\left(\sum_E\frac1{e(E)}\right)^{-1}
=\frac{12}{N-1}.
\tag{3.7}
$$

The weighted spanning-tree formula gives

$$
\#\Phi_N
=\left(\prod_Ee(E)\right)
\left(\sum_E\frac1{e(E)}\right)
=n_N.
$$

In lowest terms, the denominator of (3.7) is also $n_N$. The monodromy pairing therefore shows that the endpoint difference has exact order $n_N$. Since this equals the whole discriminant order, the endpoint difference generates the discriminant group, which is cyclic. By the monodromy description of the Néron model, this is the geometric component group $\Phi_N$ of $J$ at $N$.

### 3.3 Exact specialization

The cusps $0$ and $\infty$ specialize to the two principal components. Consequently the specialization of $c$ is the endpoint difference $\delta$. The preceding calculation shows that $\delta$ has order $n_N$. Since (3.2) shows that the order of $c$ divides $n_N$, specialization forces equality.

**Theorem 3.1.** The maps

$$
\mathbb T/I\xrightarrow{1\mapsto c}C_N
\xrightarrow{\operatorname{sp}_N}\Phi_N(\mathbf F_N)
\tag{3.8}
$$

are Hecke-equivariant isomorphisms of cyclic groups of order $n_N$.

**Proof.** The first map is surjective by definition of $C_N$ and has source of order $n_N$ by Theorem 2.3. The second sends $c$ to the generator $\delta$, so its image has order $n_N$. Formula (3.2) bounds the source by the same order. Hence both maps are isomorphisms. Hecke equivariance follows from extension of correspondences to the Néron model and (3.3). $\square$

Notice the direction of the proof. The component calculation establishes the lower bound for the cusp order; the cusp class is not used to guess the graph discriminant.

### 3.4 The Shimura subgroup

The covering that forgets a generator of a cyclic subgroup,

$$
\rho:X_1(N)\longrightarrow X_0(N),
\tag{3.9}
$$

induces the pullback homomorphism

$$
\rho^*:J_0(N)\longrightarrow J_1(N).
$$

Its kernel is the canonical diagonalizable prime-level Shimura subgroup $\Sigma_N$. Put

$$
\Delta_N=(\mathbf Z/N\mathbf Z)^\times/\{\pm1\},
$$

and let $H_N\subseteq\Delta_N$ be generated by the inertia groups at the elliptic ramification points of the cover. Descent characters give the canonical description

$$
\Sigma_N\simeq D(\Delta_N/H_N),
\tag{3.10}
$$

where $\Delta_N/H_N$ is cyclic of order $n_N$. After choosing a generator of this character group, one obtains noncanonically

$$
\Sigma_N\simeq D(\mathbf Z/n_N\mathbf Z)
\simeq\mu_{n_N}.
\tag{3.11}
$$

The Hecke action is Eisenstein, so $I\Sigma_N=0$. Changing the character generator changes the displayed identification (3.11). Arguments about order or Cartier type are canonical; an equation for a Kummer extension requires an orientation.

Writing a subscript $\ell$ for the $\ell$-primary part, the cusp and Shimura groups thus provide the two basic shapes:

$$
C_{N,\ell}\text{ is generically constant},
\qquad
\Sigma_{N,\ell}\text{ is generically multiplicative}.
\tag{3.12}
$$

For odd $\ell$, their schematic closures over $\mathbf Z[1/N]$ admit filtrations by $\underline{\mathbf Z/\ell}$ and $\mu_\ell$, respectively. At $2$, the generic characters coincide, so the integral endpoint must be read from connectedness after closure.

### 3.5 What equal orders do not imply

We have three cyclic objects of order $n_N$:

$$
C_N,\qquad \Phi_N,\qquad \Sigma_N.
\tag{3.13}
$$

Only the first two are identified by (3.8). The Shimura group lies in the generic fiber of $J$ and is Cartier-dual in nature; the component group is a quotient of the special fiber of the Néron model. Equality of their orders supplies no canonical isomorphism.

Nor does it determine $C_N\cap\Sigma_N$. At odd primes the two generic characters are distinct, so the intersection of their generic fibers is trivial. This does not make the literal scheme-theoretic intersection of their integral closures trivial: that intersection can acquire vertical nonflat structure invisible on the generic fiber. At $2$ even the generic-character distinction disappears. A complete scheme-theoretic intersection formula at every prime therefore needs additional geometry and is outside the present scope.

The same warning applies to rational torsion. The inclusion

$$
C_N\subseteq J(\mathbf Q)_{\mathrm{tors}}
\tag{3.14}
$$

is established. Equality is not. The results below prove finiteness for a selected quotient, not an exact classification of $J(\mathbf Q)_{\mathrm{tors}}$.

## 4. Eisenstein primes and local completion

### 4.1 Local factors of a finite Hecke algebra

Fix a prime $\ell\mid n_N$ and put

$$
\mathfrak m=(\ell,I).
\tag{4.1}
$$

Because $\mathbb T$ is finite over $\mathbf Z$, the algebra $\mathbb T\otimes\mathbf Z_\ell$ is semilocal and decomposes as a product of complete local rings. There is a unique idempotent

$$
e_{\mathfrak m}\in\mathbb T\otimes\mathbf Z_\ell
\tag{4.2}
$$

which is $1$ on the $\mathfrak m$-factor and $0$ on every other factor. Thus

$$
e_{\mathfrak m}(\mathbb T\otimes\mathbf Z_\ell)
=\mathbb T_{\mathfrak m}.
\tag{4.3}
$$

Idempotents lift uniquely through nilpotent quotients, so $e_{\mathfrak m}$ acts compatibly on every finite $\ell$-power torsion level. This is the integral selection used below.

### 4.2 Rational support and the optimal quotient

An idempotent in an $\ell$-adic algebra need not lie in $\mathbb T\otimes\mathbf Q$. To construct an abelian quotient over $\mathbf Q$, collect all characteristic-zero simple Hecke factors whose coefficient rings have a prime above $\mathfrak m$. Their sum defines a rational central projector

$$
E_{\mathfrak m}\in\mathbb T\otimes\mathbf Q.
\tag{4.4}
$$

Choose a positive integer $a$ with $aE_{\mathfrak m}\in\mathbb T$. The connected kernel

$$
K_{\mathfrak m}=(\ker(aE_{\mathfrak m}:J\to J))^0
\tag{4.5}
$$

is independent of the choice of $a$, because changing the denominator changes only a finite subgroup of the same rational image and therefore not the connected kernel. Define the selected optimal quotient

$$
A_{\mathfrak m}=J/K_{\mathfrak m}.
\tag{4.6}
$$

The quotient is nonzero. Indeed, the $\ell$-primary cusp class is a nonzero $I$-torsion class by (3.8), so its Hecke support contains $\mathfrak m$ and the rational support above $\mathfrak m$ cannot be empty. The kernel is connected, so (4.6) is optimal. Over the generic field there is an exact sequence of abelian varieties

$$
0\longrightarrow K_{\mathfrak m}
\longrightarrow J
\xrightarrow{\pi}A_{\mathfrak m}
\longrightarrow0.
\tag{4.7}
$$

Both $J$ and $A_{\mathfrak m}$ have good reduction over $S_N=\operatorname{Spec}\mathbf Z[1/N]$, and $\pi$ extends uniquely to a homomorphism

$$
\pi:\mathcal J\longrightarrow\mathcal A_{\mathfrak m}.
\tag{4.8}
$$

If $M E_{\mathfrak m}\in\mathbb T$, the endomorphism $M E_{\mathfrak m}$ factors over $\mathbf Q$ as $s\pi$ with $s:A_{\mathfrak m}\to J$, and $\pi s=[M]$ on $A_{\mathfrak m}$. The map $s$ also extends over $S_N$. These identities make $\pi$ faithfully flat, but they do not make its scheme-theoretic kernel smooth. In particular, we do not assert an exact sequence over $S_N$ whose left term is an abelian scheme. The integral constructions below use direct factors of the torsion of the two ambient abelian schemes and never use exactness for a positive-dimensional integral kernel.

### 4.3 Why the two projectors differ

The rational projector $E_{\mathfrak m}$ must retain an entire Galois orbit of newform factors in order to define a quotient over $\mathbf Q$. The local idempotent $e_{\mathfrak m}$ selects one completion above $\ell$. If a coefficient field has several primes above $\ell$, the rational quotient retains all companions while the completed torsion retains only the chosen one.

Symbolically,

$$
\begin{array}{ccc}
\text{characteristic-zero factors}&\xrightarrow{E_{\mathfrak m}}&A_{\mathfrak m}\text{ over }\mathbf Q,\\
\text{$\ell$-adic local factors}&\xrightarrow{e_{\mathfrak m}}&G_{\mathfrak m}\text{ over }\mathbf Z[1/N].
\end{array}
\tag{4.9}
$$

No equality $E_{\mathfrak m}=e_{\mathfrak m}$ is asserted. Their first compatibility is a theorem about the selected generic Tate lattice; the stronger equality of finite-flat towers requires the ordinary rigidity argument of Section 7.3.

There is also a useful denominator-free integral object:

$$
\mathfrak a_{E}
=E_{\mathfrak m}(\mathbb T\otimes\mathbf Q)\cap\mathbb T
=\{t\in\mathbb T:t=E_{\mathfrak m}t\}.
\tag{4.10}
$$

This is the saturated **support ideal** of the rational quotient. It is not the winding ideal, which is defined by annihilating the winding modular symbol. Accordingly, $A_{\mathfrak m}$ is not identified with the winding quotient, and no special-value or analytic-rank theorem is used to prove its finiteness. Section 9 will use $\mathfrak a_E$ only as a source of integral endomorphisms that factor through $\pi$.

### 4.4 The exact local congruence depth

Tensoring (2.9) with $\mathbf Z_\ell$ and projecting to the unique Eisenstein local factor gives

$$
\boxed{
\mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m}
\simeq
\mathbf Z_\ell/\ell^e\mathbf Z_\ell,
\qquad e=v_\ell(n_N).}
\tag{4.11}
$$

Thus the scalar boundary congruence has exact depth $e$. It follows that an Eisenstein maximal ideal exists precisely for $\ell\mid n_N$.

What does not follow is equally important. The vector space $\mathfrak m/(\mathfrak m^2,\ell)$ can have dimension greater than one even when (4.11) is cyclic. Several characteristic-zero branches can meet the Eisenstein point. The localized Tate module can require more than two generators. The algebra can fail to be Gorenstein. Formula (4.11) controls the quotient by $I$, not the whole local singularity.

## 5. The selected finite-flat tower

### 5.1 Construction by integral idempotents

Let $\mathcal J$ and $\mathcal A=\mathcal A_{\mathfrak m}$ be the good abelian-scheme models over $S_N=\operatorname{Spec}\mathbf Z[1/N]$. Since $\ell\ne N$, multiplication by $\ell^r$ is faithfully flat on each model and both $\ell^r$-torsion groups are finite flat. Define two towers, not one:

$$
P_r=e_{\mathfrak m}\mathcal J[\ell^r],
\qquad
G_r=e_{\mathfrak m}\mathcal A[\ell^r].
\tag{5.1}
$$

Because the image of an idempotent is a direct factor,

$$
\begin{aligned}
\mathcal J[\ell^r]
&=P_r\times(1-e_{\mathfrak m})\mathcal J[\ell^r],\\
\mathcal A[\ell^r]
&=G_r\times(1-e_{\mathfrak m})\mathcal A[\ell^r].
\end{aligned}
\tag{5.2}
$$

Thus $P_r$ and $G_r$ are finite flat without any separate flatness theorem for a kernel of Hecke operators. This is why completion precedes torsion: the schematic kernel of the generators of $I$ could acquire vertical nonflat structure, whereas an idempotent image is automatically a direct factor. It is equally important that the two direct factors have different ambient abelian schemes. Their eventual equality is a theorem, not part of the definition.

Both constructions are compatible with base change. Over $\mathbf Q$, they select the generalized $\mathfrak m$-summands of the two generic torsion groups. Over $\mathbf Z_\ell$, they retain connected as well as etale structure. At a prime away from $N\ell$, they are finite etale and carry the usual unramified Frobenius action.

### 5.2 Exact transition maps

The full torsion towers of the two ambient abelian schemes have faithfully flat exact sequences. Applying the corresponding idempotent decompositions gives, separately,

$$
0\longrightarrow P_r
\longrightarrow P_{r+s}
\xrightarrow{\ell^r}P_s
\longrightarrow0.
\tag{5.3}
$$

$$
0\longrightarrow G_r
\longrightarrow G_{r+s}
\xrightarrow{\ell^r}G_s
\longrightarrow0.
\tag{5.4}
$$

Exactness here means exactness for the faithfully flat topology: each last arrow is faithfully flat and its displayed left term is its scheme-theoretic kernel. These facts follow within each ambient torsion tower. No torsion exact sequence relating $\mathcal J$ and $\mathcal A$ has been used.

Consequently

$$
P_{\mathfrak m}=\varinjlim_rP_r,
\qquad
G_{\mathfrak m}=\varinjlim_rG_r
\tag{5.5}
$$

are $\ell$-divisible groups over $S_N$. They are not merely compatible families of generic Galois modules. The flat exactness of (5.3)--(5.4) records integral divisibility at the coefficient prime.

### 5.3 Comparison with the selected quotient

The generic optimal sequence (4.7) gives an exact sequence on covariant Tate modules

$$
0\longrightarrow T_\ell K_{\mathfrak m}
\longrightarrow T_\ell J
\longrightarrow T_\ell A_{\mathfrak m}
\longrightarrow0.
\tag{5.6}
$$

Surjectivity here is a generic fppf statement: every $\ell^r$-torsion point of the quotient lifts after correcting a lift by an $\ell^r$-division point in the connected generic kernel. Thus the quotient Tate lattice is saturated. The rational support of $K_{\mathfrak m}$ is complementary to $E_{\mathfrak m}$, so $e_{\mathfrak m}$ acts as zero on $T_\ell K_{\mathfrak m}$. Applying it to (5.6) gives

$$
\boxed{
e_{\mathfrak m}T_\ell J
\xrightarrow{\sim}
e_{\mathfrak m}T_\ell A_{\mathfrak m}.}
\tag{5.7}
$$

The extended quotient map and the auxiliary map of Section 4.2 induce compatible morphisms

$$
\pi_r:P_r\longrightarrow G_r,
\qquad
s_r:G_r\longrightarrow P_r.
\tag{5.8}
$$

If $M=\ell^cM'$ with $M'$ an $\ell$-adic unit, rescaling $s_r$ by $M'^{-1}$ shows that the fppf kernel and cokernel defects of $\pi_r$ are killed by $\ell^c$. The map is an isomorphism generically and over $S_N[1/\ell]$. This does **not** yet prove that it is an isomorphism over $\mathbf Z_\ell$: a generic isomorphism between finite-flat groups can exchange distinct integral models. Nor does (5.7) make the positive-dimensional integral kernel of $\pi$ smooth.

We therefore retain $P_r$ and $G_r$ separately. Admissibility will make the quotient tower ordinary in Sections 6--7. The ordinary-tower rigidity theorem in Section 7.3 then uses the saturated middle Tate map (5.7), the compatible system (5.8), and the canonical endpoints to prove $\pi_r$ is an isomorphism at every level. Descent meanwhile uses $G_r$ directly, whose exactness already follows from its own ambient abelian scheme.

### 5.4 Faithfulness and finite-level annihilators

The complete local algebra acts continuously on $G_{\mathfrak m}$. If $t\in\mathbb T_{\mathfrak m}$ acts trivially on every $G_r$, it acts trivially on the Tate module. The Hecke action on the selected Tate summand is faithful, so $t=0$. Thus

$$
\mathbb T_{\mathfrak m}\hookrightarrow
\operatorname{End}(G_{\mathfrak m})
\tag{5.9}
$$

is injective, and

$$
\bigcap_{r\ge1}\operatorname{Ann}_{\mathbb T_{\mathfrak m}}(G_r)=0.
\tag{5.10}
$$

Faithfulness at infinite level does not mean that every $G_r$ is faithful. Nor does it imply that $G_{\mathfrak m}$ has height two or is free of rank two over $\mathbb T_{\mathfrak m}$. Those are multiplicity statements, not consequences of separation.

## 6. Admissible Eisenstein group schemes

### 6.1 The two atoms

Over $S_N$, the two basic order-$\ell$ finite-flat groups are

$$
\underline{\mathbf Z/\ell\mathbf Z}
\quad\text{and}\quad
\mu_\ell.
\tag{6.1}
$$

Their generic Galois characters are $1$ and the mod-$\ell$ cyclotomic character $\bar\chi_\ell$. Cartier duality exchanges them. A finite-flat $\ell$-primary group is **Eisenstein-admissible** if it has a finite filtration by finite-flat subgroup schemes whose successive quotients are the two groups in (6.1).

Admissibility is weaker than splitting. An object may contain a nonsplit extension of a constant quotient by a multiplicative subgroup. It is also weaker than a canonical global connected--etale decomposition: such a decomposition exists over $\mathbf Z_\ell$, but need not globalize over $S_N$ in a prescribed order.

The number of constant and multiplicative factors is nevertheless intrinsic. After base change to $\mathbf Z_\ell$, the former contribute to the etale rank and the latter to the connected multiplicative rank. These ranks are independent of a chosen filtration.

### 6.2 From a residual flag to a flat filtration

Reducing the selected Hecke algebra modulo its radical yields successive modules on which every Hecke operator acts through the Eisenstein character. At a prime $q\nmid N\ell$, (1.4) becomes

$$
(F_q-1)(F_q-q)=0
\tag{6.2}
$$

on each semisimple radical layer. A density argument applied to the finite Galois quotient generated by that layer and $\bar\chi_\ell$ shows that every simple constituent is either trivial or cyclotomic. Refining the radical filtration therefore gives a Galois- and Hecke-stable composition series of

$$
G_1(\overline{\mathbf Q})
\tag{6.3}
$$

with factors $\mathbf F_\ell$ and $\mathbf F_\ell(1)$.

Here is the decisive finite-group argument. On a simple constituent $W$, let $H$ be the joint finite image of Galois on $W$ and through $\bar\chi_\ell$, and put $P=\ker(\bar\chi_\ell:H\to\mathbf F_\ell^\times)$. Density transports (6.2) from good Frobenius elements to every $g\in H$. Hence

$$
(u-1)^2=0\qquad(u\in P).
$$

The image of $P$ is therefore an $\ell$-group. It is normal in $H$, so its fixed space in the simple module $W$ is nonzero and $H$-stable; simplicity forces $P$ to act trivially. The action on $W$ factors through the cyclic group $\operatorname{im}\bar\chi_\ell\subseteq\mathbf F_\ell^\times$. It is then one-dimensional, and (6.2) leaves only the characters $1$ and $\bar\chi_\ell$. This proves the assertion about every simple constituent without assuming semisimplicity of the original layer.

The decisive point is that a composition series, not merely a semisimplification, has been produced. Trace $1+\bar\chi_\ell$ would determine the semisimplification but would not supply a stable line to close.

Close each term of the generic flag schematically inside the preceding finite-flat quotient of $G_1$. Schematic closure over the Dedekind base is finite flat, and the represented quotient is finite flat. For odd $\ell$, low-ramification rigidity over $\mathbf Z_\ell$ identifies an order-$\ell$ closure with the endpoint determined by its generic character. At higher level, pull the flag through (5.4) and refine.

**Theorem 6.1.** Every $G_r$ is Eisenstein-admissible. For odd $\ell$, its successive generic trivial and cyclotomic characters close to $\underline{\mathbf Z/\ell}$ and $\mu_\ell$, respectively. At $\ell=2$, every closure is still one of these two endpoints, but its label is determined integrally after closure.

**Proof.** The radical filtration and (6.2) give an actual stable generic composition series with the two stated characters. Schematic closure of the first line in $G_1$, followed by closure in each successive finite-flat quotient, gives a finite-flat filtration. When $\ell$ is odd, the ramification index of $\mathbf Z_\ell$ is $1<\ell-1$, so height-one rigidity identifies each closure from its generic character. When $\ell=2$, the unramified order-two classification has only the constant and multiplicative endpoints; inspecting the connected special fiber distinguishes them after closure. Pulling this filtration back through the faithfully flat maps $G_r\to G_1$ and refining the kernels with (5.4) proves the same statement for every $r$. $\square$

### 6.3 Mixed extensions

Suppose $\ell$ is odd and a separated height-two subquotient has the form

$$
0\longrightarrow\mu_\ell
\longrightarrow H
\longrightarrow\underline{\mathbf Z/\ell}
\longrightarrow0.
\tag{6.4}
$$

The fiber over $1$ is a $\mu_\ell$-torsor. Since

$$
\mathbf Z[1/N]^\times=\{\pm N^a:a\in\mathbf Z\}
\tag{6.5}
$$

and the Picard group of $\mathbf Z[1/N]$ is zero, the fppf Kummer sequence gives

$$
H^1(S_N,\mu_\ell)
\simeq \mathbf Z[1/N]^\times/\mathbf Z[1/N]^{\times\ell}.
\tag{6.6}
$$

For odd $\ell$, the sign is an $\ell$th power, while valuation at $N$ gives one free class. Compatibility with the group law identifies

$$
\operatorname{Ext}^1_{S_N}
(\underline{\mathbf Z/\ell},\mu_\ell)
\simeq\langle[N]\rangle\simeq\mathbf F_\ell.
\tag{6.7}
$$

After choosing endpoint generators, the extension indexed by $j\in\mathbf F_\ell$ has fiber equation

$$
T^\ell=N^j.
\tag{6.8}
$$

It splits exactly when $j=0$. Changing a generator rescales every nonzero $j$, so without orientations there are only split and nonsplit types.

This calculation does not classify same-type extensions, nor prove that an arbitrary admissible object has a global multiplicative subgroup with constant quotient. Such a separation must be constructed geometrically or from the local connected--etale sequence.

### 6.4 The dyadic boundary

At $\ell=2$,

$$
1=\bar\chi_2,
\tag{6.9}
$$

so the generic representations of $\underline{\mathbf Z/2}$ and $\mu_2$ are indistinguishable. The integral groups differ: over $\mathbf Z_2$, one is etale and the other connected. The unramified order-two classification says that these are the only two finite-flat endpoints. Thus each closure in Theorem 6.1 is an atom, but character theory cannot orient it.

Mixed extensions carry more information. There is an exact sequence

$$
0\longrightarrow\mu_2(S_N)
\longrightarrow
\operatorname{Ext}^1_{S_N}
(\underline{\mathbf Z/2},\mu_2)
\longrightarrow
S_N^\times/S_N^{\times2}
\longrightarrow0.
\tag{6.10}
$$

The right side is generated by the sign and level-unit classes $[-1]$ and $[N]$; the left side supplies a carry class. Any dyadic descent that records only the generic trivial character loses all three pieces of information.

The numerical condition for a dyadic Eisenstein factor is

$$
v_2(n_N)=v_2(N-1)-2>0.
\tag{6.11}
$$

At such a level, the integral endpoint check is part of the theorem, not a cosmetic refinement.

## 7. The completed divisible group

### 7.1 Connected, etale, and multiplicative pieces

Base change $G_{\mathfrak m}$ to $\mathbf Z_\ell$. Every $\ell$-divisible group over this complete local base has a canonical connected--etale sequence. Admissibility excludes local-local simple factors and identifies the connected part as multiplicative. Hence

$$
0\longrightarrow G_{\mathfrak m}^{\mathrm{mult}}
\longrightarrow G_{\mathfrak m}
\longrightarrow G_{\mathfrak m}^{\mathrm{et}}
\longrightarrow0.
\tag{7.1}
$$

At finite level this gives

$$
0\longrightarrow G_r^{\mathrm{mult}}
\longrightarrow G_r
\longrightarrow G_r^{\mathrm{et}}
\longrightarrow0
\tag{7.2}
$$

after base change to $\mathbf Z_\ell$. The sequence need not split. Its endpoint heights equal the multiplicative and constant lengths in any admissible filtration of $G_1$. This is the correct ordinary statement here: it supplies no chosen basis and no rank-two theorem over the Hecke algebra.

### 7.2 Cuspidal and Shimura directions

Let $e=v_\ell(n_N)$. The $\ell$-primary cusp and Shimura groups both have order $\ell^e$. Their generic fibers lie in the selected rational support, and the local idempotent acts as the identity on them. Taking schematic closures in the Jacobian tower gives finite-flat subgroups

$$
\mathcal C_{N,\ell},\ \mathcal\Sigma_{N,\ell}\subseteq P_e.
\tag{7.3}
$$

For odd $\ell$, their canonical cyclic filtrations have quotients

$$
\mathcal C_i/\mathcal C_{i-1}\simeq
\underline{\mathbf Z/\ell},
\qquad
\mathcal\Sigma_i/\mathcal\Sigma_{i-1}\simeq\mu_\ell.
\tag{7.4}
$$

They give named constant and multiplicative directions, but need not exhaust the etale and multiplicative heights. Additional congruent characteristic-zero branches can enlarge the completed piece without changing (4.11). Theorem 7.1 below transports these closures isomorphically from $P_e$ to $G_e$; before that theorem, they must not simply be declared equal as integral subgroup schemes of the quotient tower.

At $2$, the closures remain admissible but their generic labels do not determine every integral endpoint. No formula for their full intersection is used.

### 7.3 Duality and height

The principal polarization of $J$ gives perfect Weil pairings on its finite torsion. The Rosati involution carries a selected local factor to its adjoint factor. In the present prime-level normalization, every generator of the commutative Hecke algebra is Rosati self-adjoint, so

$$
e_{\mathfrak m}^{\dagger}=e_{\mathfrak m},
\qquad
P_{\mathfrak m}^D\simeq P_{\mathfrak m}
$$

integrally. This restriction is perfect because the $e_{\mathfrak m}$- and $(1-e_{\mathfrak m})$-summands are orthogonal complements. It does not initially give a perfect pairing on $G_{\mathfrak m}$: a polarization induced on an optimal quotient can have degree divisible by $\ell$.

The comparison maps of Section 5.3 make $P_{\mathfrak m}$ and $G_{\mathfrak m}$ quasi-isogenous, so their rational Dieudonne modules agree. Since $P_{\mathfrak m}$ is self-dual, the slopes of the ordinary group (7.1) are symmetric. If its etale and multiplicative heights are $a$ and $b$, respectively, then

$$
a=b.
\tag{7.5}
$$

This is so far only quasi-self-duality. The following rigidity result supplies the integral conclusion.

**Theorem 7.1 (ordinary-tower rigidity).** The quotient map induces isomorphisms

$$
\pi_r:P_r\xrightarrow{\sim}G_r
\qquad(r\ge1)
\tag{7.6}
$$

over $S_N$, compatible with the Hecke action, base change, inclusions, and multiplication by $\ell$. Consequently

$$
P_{\mathfrak m}\xrightarrow{\sim}G_{\mathfrak m},
\qquad
G_{\mathfrak m}^D\simeq G_{\mathfrak m}
\tag{7.7}
$$

integrally, with perfect pairings on every $G_r$.

**Proof.** Work first over $\mathbf Z_\ell$. The quotient tower is ordinary by Sections 7.1 and 6. The quasi-isogenous tower $P_{\mathfrak m}$ has the same slopes; its canonical connected--etale sequence is therefore ordinary as well. The comparison map gives a diagram between their multiplicative and etale endpoint sequences. On generic Tate modules the middle vertical map is the saturated isomorphism (5.7). In bases adapted to the two exact endpoint sequences, its matrix is block upper triangular. Its determinant is an $\ell$-adic unit and is the product of the two integral endpoint determinants. Their valuations are nonnegative and sum to zero, so both endpoint maps are integral isomorphisms on Tate modules.

Finite etale group schemes over the normal henselian DVR $\mathbf Z_\ell$ are determined fully faithfully by their generic fibers. Hence the etale endpoint maps are isomorphisms at every finite level; Cartier duality gives the same conclusion for the multiplicative endpoints. The short five lemma for the two exact endpoint sequences then makes $\pi_r$ an isomorphism over $\mathbf Z_\ell$. Away from $\ell$ it was already an isomorphism by the prime-to-$\ell$ comparison in Section 5.3. On coordinate Hopf algebras, the finite cokernel of $\pi_r^*$ therefore vanishes after localization at every prime of $S_N$, and hence vanishes globally. This proves (7.6).

Finally, transport the perfect Cartier pairing on $P_{\mathfrak m}$ across (7.6). This proves (7.7). Notice what the proof used: compatible divisible towers, ordinary canonical endpoints, and the saturated Tate map. It does not prove that the positive-dimensional kernel of $\mathcal J\to\mathcal A$ is smooth. $\square$

Thus (7.1) is integrally dual to itself with endpoints reversed, and (7.5) holds at the level of perfect finite-flat pairings. It determines only equality of heights, not that each is one. The selected ordinary group can have height $2d$ with $d>1$.

### 7.4 Multiplicity one and Gorenstein boundaries

**Proposition 7.2.** Let $R=\mathbb T_{\mathfrak m}$. Suppose that the selected Tate module is finite free of rank $2$ over $R$, and suppose an integral polarization and primitive endpoint comparison identify

$$
R^\vee=\operatorname{Hom}_{\mathbf Z_\ell}(R,\mathbf Z_\ell)
$$

with a free rank-one $R$-module. Then $R$ is Gorenstein and the residual selected representation has dimension two.

**Proof.** For a finite flat local $\mathbf Z_\ell$-algebra, freeness of $R^\vee$ of rank one over $R$ is exactly the Gorenstein self-duality criterion. The Tate-module hypothesis gives $M\simeq R^2$; reducing modulo the maximal ideal gives a two-dimensional residual module. $\square$

These hypotheses are not proved for every Eisenstein maximal ideal here. In particular, (4.11) does not imply rank-two freeness or the displayed dual identification. Therefore no unconditional complete multiplicity-one or Gorenstein assertion is made.

## 8. Eisenstein descent

### 8.1 Strict local conditions

Fix $A=A_{\mathfrak m}$ and $G_r=e_{\mathfrak m}\mathcal A[\ell^r]$. Kummer theory gives a selected image in $H^1(\mathbf Q,G_r)$. At a finite prime $v\ne N$, impose the finite-flat local condition. At $v=\ell$, this is genuine flat cohomology, not merely the unramified subgroup of generic Galois cohomology.

At $N$, strictness means that the local point lies in the identity component of the Néron model before applying Kummer. The relaxed condition allows all local points; their difference is measured by the actual component image. At the real place there is no correction for odd $\ell$. For $\ell=2$, retain the positive identity-component condition.

Denote the resulting strict Selmer group by $\operatorname{Sel}^{\mathrm{str}}(G_r)$.

### 8.2 Atomic vanishing

For $\mu_\ell$, Kummer theory identifies global classes over $S_N$ with units modulo $\ell$th powers. Strictness removes the valuation at $N$; for odd $\ell$ the sign is an $\ell$th power, and for $\ell=2$ positivity removes it. Hence the strict multiplicative atomic group is zero.

For $\underline{\mathbf Z/\ell}$, a class is a cyclic etale cover of $S_N$. Strictness at $N$ removes its only allowed ramification, while the other local conditions make it everywhere unramified over $\mathbf Q$. There is no nontrivial everywhere-unramified extension of $\mathbf Q$. Thus

$$
\operatorname{Sel}^{\mathrm{str}}
(\underline{\mathbf Z/\ell})=0,
\qquad
\operatorname{Sel}^{\mathrm{str}}(\mu_\ell)=0.
\tag{8.1}
$$

### 8.3 Devissage and component defects

For an admissible exact sequence $0\to H'\to H\to H''\to0$, propagate the local condition on $H$ to $H'$ by inverse image and to $H''$ by direct image. The resulting sequence

$$
\operatorname{Sel}^{\mathrm{str}}(H')
\longrightarrow\operatorname{Sel}^{\mathrm{str}}(H)
\longrightarrow\operatorname{Sel}^{\mathrm{str}}(H'').
\tag{8.2}
$$

is exact at the middle term; injectivity on the left is neither needed nor asserted. Moreover, the quotient local condition is contained in the standard strict atomic condition. If the latter atomic Selmer group vanishes, every strict class with coefficients in $H$ therefore lifts to one with coefficients in $H'$. Repeating this left-exact lifting along an admissible filtration eventually moves the class into the zero subgroup and proves

$$
\boxed{\operatorname{Sel}^{\mathrm{str}}(G_r)=0
\quad(r\ge1).}
\tag{8.3}
$$

This preserves nonsplit extensions; it never replaces $G_r$ by its semisimplification.

Let $D_{\mathfrak m,N}$ be the selected image of the level-prime component map and $D_{\mathfrak m,\infty}$ the selected real component group when $\ell=2$, zero otherwise. Strict--relaxed comparison yields

$$
\frac{e_{\mathfrak m}(A(\mathbf Q)\otimes\mathbf Z_\ell)}{\ell^r}
\hookrightarrow
\frac{D_{\mathfrak m,N}}{\ell^rD_{\mathfrak m,N}}
\oplus
\frac{D_{\mathfrak m,\infty}}{\ell^rD_{\mathfrak m,\infty}}.
\tag{8.4}
$$

The groups on the right are fixed and finite. We do not replace $D_{\mathfrak m,N}$ by the whole component group unless surjectivity has separately been proved.

### 8.4 Rank zero and finiteness

If the selected completion of $A(\mathbf Q)$ had positive $\mathbf Z_\ell$-rank $d$, the left side of (8.4) would contain $(\mathbf Z_\ell/\ell^r)^d$ for arbitrarily large $r$. Its order would be unbounded, contradicting the fixed right side. Thus the selected rank is zero. Rational support and Galois conjugacy carry this vanishing across all companion factors, so

$$
\operatorname{rank}A(\mathbf Q)=0.
\tag{8.5}
$$

Mordell--Weil finite generation now gives

$$
\boxed{A_{\mathfrak m}(\mathbf Q)\text{ is finite}.}
\tag{8.6}
$$

The uniformity in $r$, rather than finite-level Selmer finiteness by itself, is what forces rank zero.

### 8.5 The exact torsion boundary

Good-prime Frobenius, finite-flat endpoint recognition at the coefficient prime, and the level sign show that every maximal ideal in the Hecke support of the finite group $A(\mathbf Q)$ is

$$
(p,I)\qquad(p\mid n_N).
\tag{8.7}
$$

If $s_p$ is the Loewy length of the $p$-primary part, then

$$
\sqrt{\operatorname{Ann}_{\mathbb T}A(\mathbf Q)}
=\bigcap_{p\mid\#A(\mathbf Q)}(p,I),
\tag{8.8}
$$

and

$$
\prod_{p\mid\#A(\mathbf Q)}(p,I)^{s_p}
\subseteq\operatorname{Ann}_{\mathbb T}A(\mathbf Q).
\tag{8.9}
$$

One cannot replace the power in (8.9) by $I$: an operator may map a quotient constituent into a subconstituent. Nor have we proved that $A(\mathbf Q)$ equals the image of $C_N$, or calculated its order. A quotient torsion point need not lift to a rational torsion point on $J$ because its connecting class in $H^1(\mathbf Q,K_{\mathfrak m})$ may be nonzero. The exact rational torsion of the full Jacobian and of the selected quotient lies beyond this package.

## 9. The cotangent lattice

### 9.1 Invariant differentials of an optimal quotient

Let $p\ne N$ be a prime. Over $\mathbf Z_p$, both $J$ and $A=A_{\mathfrak m}$ have good reduction. Write $\mathcal J_p$ and $\mathcal A_p$ for their abelian schemes and define their invariant cotangent modules

$$
\omega_J=e_J^*\Omega^1_{\mathcal J_p/\mathbf Z_p},
\qquad
\omega_A=e_A^*\Omega^1_{\mathcal A_p/\mathbf Z_p}.
\tag{9.1}
$$

The generic pullback along the optimal quotient is injective. Its extension between the good models therefore induces an injection of finite free $\mathbf Z_p$-modules

$$
\pi^*:\omega_A\hookrightarrow\omega_J;
\tag{9.2}
$$

the kernel would be torsion and $\omega_A$ is torsion free. This argument says nothing about torsion in the cokernel. The Abel--Jacobi identification and the weight-two Kodaira--Spencer theorem identify

$$
\omega_J\simeq S_2(\Gamma_0(N);\mathbf Z_p).
\tag{9.3}
$$

Define the selected cotangent lattice

$$
\Omega_{\mathfrak m,p}
=\operatorname{im}(\omega_A\to\omega_J)
\subseteq S_2(\Gamma_0(N);\mathbf Z_p).
\tag{9.4}
$$

It is Hecke stable because the quotient is defined by rational Hecke support and the endomorphisms extend to the good Néron models. Its rational span is the sum of precisely those newform factors retained by $E_{\mathfrak m}$.

This definition uses invariant differentials of the actual optimal quotient. Taking the intersection of a rational newform subspace with a convenient $q$-expansion lattice could give the wrong answer at a prime dividing a congruence degree.

There is deliberately no claim that the cokernel of (9.2) is torsion free, that (9.4) is primitive for every $p$, or that it commutes with arbitrary base change. Such assertions would follow from a smooth integral kernel, and no such kernel theorem is available or needed.

### 9.2 The saturated support ideal

Recall the support ideal $\mathfrak a_E$ from (4.10). It replaces the nonexistent integral kernel sequence in the formal-immersion argument.

**Lemma 9.1 (integral support operators).** The ideal $\mathfrak a_E$ is a nonzero saturated $\mathbf Z$-submodule of $\mathbb T$. For every prime $p$ there is an element

$$
t_p\in\mathfrak a_E\setminus p\mathbb T.
\tag{9.5}
$$

Every $t\in\mathfrak a_E$ factors uniquely over $\mathbf Q$ as

$$
t=s_t\pi,
\qquad s_t:A_{\mathfrak m}\longrightarrow J,
\tag{9.6}
$$

and $s_t$ extends over every good base $\mathbf Z_p$, $p\ne N$.

**Proof.** If $nx\in\mathfrak a_E$ for a nonzero integer $n$ and $x\in\mathbb T$, then $E(nx)=nx$ in $\mathbb T\otimes\mathbf Q$, hence $Ex=x$ and $x\in\mathfrak a_E$. Thus $\mathbb T/\mathfrak a_E$ is torsion free. The ideal is nonzero because a cleared denominator $ME$ lies in it. Tensoring the injection $\mathfrak a_E\hookrightarrow\mathbb T$ with $\mathbf F_p$ remains injective, so a nonzero class in $\mathfrak a_E/p\mathfrak a_E$ gives (9.5).

For the factorization, $t=Et$ vanishes on the complementary rational support $K_{\mathfrak m}$. The universal property of the generic quotient (4.7) gives the unique $s_t$ in (9.6). Homomorphisms between the good Néron models extend uniquely, and equality with $t$ can be checked on the generic fiber. $\square$

The ideal $\mathfrak a_E$ should not be renamed a winding ideal. Its definition uses characteristic-zero Hecke support, not the annihilator of a modular symbol. The distinction is what allows the next argument to be purely integral and algebraic.

### 9.3 The completed comparison

At $p=\ell$, a statement only about rational Tate spaces would not control the integral cotangent index. Here Theorem 7.1 gives the finite-flat isomorphisms $\pi_n:P_n\simeq G_n$. For any abelian scheme $B/\mathbf Z_\ell$, the conormal sequence for multiplication by $\ell^n$ gives a functorial identity

$$
\omega_{B[\ell^n]}
\simeq\omega_B/\ell^n\omega_B.
\tag{9.7}
$$

Applying (9.7) to the idempotent direct factors and using $\pi_n^*$ gives compatible isomorphisms

$$
e_{\mathfrak m}\omega_A/\ell^n
\xrightarrow{\sim}
e_{\mathfrak m}\omega_J/\ell^n.
\tag{9.8}
$$

Taking inverse limits gives

$$
e_{\mathfrak m}\omega_A
\xrightarrow{\sim}
e_{\mathfrak m}\omega_J.
\tag{9.9}
$$

This equality is on completed selected lattices and follows contravariantly from an actual isomorphism of finite-flat towers. It is not obtained by applying $e_{\mathfrak m}$ to a Lie sequence for an integral kernel. In particular, (9.9) neither asserts that the whole image (9.4) is primitive at every prime nor manufactures a smooth model of $K_{\mathfrak m}$.

The completed equality does not claim rank one over $\mathbb T_{\mathfrak m}$. Several branches may occur. Formal immersion needs only one quotient differential whose pullback is primitive, and the support ideal supplies it at every good residue prime, not merely at $\ell$.

### 9.4 Support operators as cotangent coordinates

Fix $p\ne N$ and choose $t_p$ as in (9.5). Perfectness of the Hecke--Fourier pairing (2.7) identifies $\mathbb T$ with $S^\vee$ by

$$
t\longmapsto\bigl(f\longmapsto a_1(tf)\bigr).
$$

The image of $t_p$ is nonzero modulo $p$: otherwise $t_p$ would belong to $p\mathbb T$. Hence there is an integral cusp form $f_p\in S$ such that

$$
a_1(t_pf_p)\in\mathbf Z_p^\times.
\tag{9.10}
$$

Factor $t_p=s_{t_p}\pi$ by Lemma 9.1 and put

$$
\eta_p=s_{t_p}^*f_p\in\omega_A.
\tag{9.11}
$$

Then

$$
\pi^*\eta_p=t_p^*f_p=t_pf_p,
\qquad
a_1(\pi^*\eta_p)\in\mathbf Z_p^\times.
\tag{9.12}
$$

Thus the actual quotient cotangent lattice contains a vector whose image in the ambient cusp-form lattice is primitive at $p$. This is an existence statement for one vector, exactly what a map from a curve needs. It does not imply that the entire cokernel of (9.2) is torsion free.

At $p=2$ or $3$, perfectness in (2.7) and (9.10) use the regular dualizing lattice on the compactified modular object. Stabilizer descent is already built into that lattice, so the argument does not reduce a naive coarse differential.

## 10. Formal immersion at an oriented cusp

### 10.1 Why the cusp must be oriented

Formal immersion is needed on the point-level curve $X_1(N)$, not merely on $X_0(N)$. A cusp of $X_1(N)$ remembers how the chosen point of order $N$ sits in the degenerate fiber. Write

$$
\rho:X_1(N)\longrightarrow X_0(N)
\tag{10.1}
$$

for the map forgetting the generator. An **outward cusp** is one at which the point of order $N$ generates the component group of the limiting polygon. The map $\rho$ is unramified there but sends the cusp to $0$, not to the standard Fourier-expansion cusp $\infty$. The Atkin--Lehner involution corrects this orientation: put

$$
\sigma=w_N\circ\rho:X_1(N)\longrightarrow X_0(N).
\tag{10.2}
$$

Then $\sigma$ sends every outward cusp to $\infty$ and preserves the smoothing parameter up to a unit. This is the map for which the first Fourier coefficient at $\infty$ measures the point-level cotangent direction.

Fix an outward rational cusp $c_1$. Point the Abel--Jacobi map at the standard cusp:

$$
\iota_\infty:X_0(N)\longrightarrow J,
\qquad x\longmapsto[x]-[\infty].
\tag{10.3}
$$

Compose it with the selected quotient:

$$
h:X_1(N)\xrightarrow{\sigma}X_0(N)
\xrightarrow{\iota_\infty}J
\xrightarrow{\pi}A.
\tag{10.4}
$$

Then $h(c_1)=0$.

For every $p\ne N$, the modular maps extend over the good integral models, the pointed Abel--Jacobi map extends to the Néron model, and $\pi$ extends by (4.8). Thus $h$ is an actual morphism in a neighborhood of the integral cusp section over $\mathbf Z_p$, so its special-fiber cotangent map and completed local-ring map are defined.

### 10.2 The cotangent calculation

Fix a prime $p\ne N$ and take $t_p,f_p,$ and $\eta_p$ from Section 9.4. Let $q$ be the standard parameter at $\infty$ and let $z$ be an outward point-level parameter at $c_1$. Compatible frames give

$$
\sigma^*q=uz+O(z^2),
\qquad u\in\mathbf Z_p^\times.
\tag{10.5}
$$

Because $\pi^*\eta_p=t_p^*f_p$, the pullback of $\eta_p$ along the fixed map $h$ is the pullback along $\sigma$ and $\iota_\infty$ of the cusp form $t_pf_p$. At $\infty$ its first-order expansion is

$$
(t_pf_p)(q)\frac{dq}{q}
=\bigl(a_1(t_pf_p)+O(q)\bigr)dq.
$$

By (9.10) and (10.5), the image of $h^*\eta_p$ in the cotangent line at $c_1$ is

$$
u\,a_1(t_pf_p)\,dz,
\tag{10.6}
$$

which is a basis modulo $p$. Hence the map on cotangent spaces is surjective. Notice that $s_{t_p}$ was used to manufacture a cotangent vector on $A$; no endomorphism was appended to the target map $h$.

**Theorem 10.1.** For every prime $p\ne N$ and every outward rational cusp of $X_1(N)$, the map $h$ in (10.4) itself is a formal immersion at that cusp modulo $p$.

**Proof.** A morphism from a relative curve to a smooth group scheme is a formal immersion at a section if the induced map on cotangent spaces is surjective. Equation (10.6) proves precisely that condition. The outward orientation and the use of $\sigma=w_N\rho$ ensure that the standard parameter $q$ pulls back to a unit times the point-level parameter. $\square$

The support operator changes only the cotangent coordinate used to test $h$. This distinction matters in the rational-point step: the map whose image is known to vanish is exactly the map proved formally immersive.

### 10.3 Separation in an odd cusp disk

Formal immersion separates two sections once their images in the finite quotient agree. Let $p$ be odd, $p\ne N$, and let $x\in X_1(N)(\mathbf Q)$ reduce to the same outward cusp $c_1$ modulo $p$. By (8.6), $A(\mathbf Q)$ is finite. The difference

$$
h(x)-h(c_1)=h(x)
\tag{10.7}
$$

is torsion and specializes to zero.

At an odd good prime, rational torsion on an abelian variety specializes injectively. Indeed, prime-to-$p$ torsion is etale and hence injects under reduction. A $p$-power torsion point in the kernel lies in the formal group over the unramified field $\mathbf Q_p$; the formal logarithm on a sufficiently deep subgroup and the torsion-freeness of its additive lattice show that this kernel has no nonzero rational $p$-power torsion. Therefore $h(x)=0$.

Thus $h(x)=h(c_1)$. A formal immersion separates two sections with the same special point and the same image: surjectivity on completed cotangent spaces makes the induced map of completed local rings surjective, so equality after composition forces equality of the two local homomorphisms. Hence

$$
\boxed{x\equiv c_1\pmod p, p\text{ odd}, p\ne N
\quad\Longrightarrow\quad x=c_1.}
\tag{10.8}
$$

This is the cusp-disk rigidity exported by the selected quotient.

### 10.4 Limits of the argument

Three boundaries are essential.

First, at $p=2$ the formal-immersion theorem remains true, but the torsion-specialization argument used in (10.8) is not asserted. The rational formal group can contain subtler two-primary behavior. One needs a quotient-specific specialization-kernel theorem before deriving dyadic cusp-disk rigidity.

Second, an inward cusp is not covered by this coefficient calculation. The forgetful map sends it to $\infty$, but the oriented map $\sigma=w_N\rho$ sends it to the other cyclic-level cusp, where the standard parameter at $\infty$ no longer measures the point-level cotangent. One must change the oriented map and recheck rationality or perform a separate cotangent calculation.

Third, the theorem concerns $A_{\mathfrak m}$. The equality $C_N\simeq\Phi_N$ for the full Jacobian does not determine the component map or torsion kernel for $A_{\mathfrak m}$. The descent and formal-immersion arguments use only the actual selected component images and the finite group (8.6).

## 11. Exceptional primes and diagnostic levels

### 11.1 Trivial Eisenstein levels

For

$$
N=2,3,5,7,13,
\tag{11.1}
$$

one has $n_N=1$ and $J_0(N)=0$. The quotient $\mathbb T/I$ is the zero ring, written $\mathbf Z/1\mathbf Z$, and there is no prime $\ell\mid n_N$. The selected quotient, its divisible group, and its cotangent direction do not exist.

The level $13$ case is an important boundary: the modular curve relevant to point-level questions can have positive genus even though the cyclic-level Jacobian $J_0(13)$ has no Eisenstein factor. Formal immersion through a selected Eisenstein quotient therefore supplies no conclusion there.

The levels $2$ and $3$ are settled by direct genus-zero geometry. We do not force the tame weighted-node argument into wild level characteristic.

### 11.2 Levels eleven, seventeen, and nineteen

The first three nontrivial values are

$$
n_{11}=5,
\qquad n_{17}=4,
\qquad n_{19}=3.
\tag{11.2}
$$

At level $11$, the sole Eisenstein prime is $5$. The cusp class and the component group both have order $5$, while the selected quotient is the elliptic Jacobian itself. The completed $5$-divisible tower is governed by distinct constant and cyclotomic characters.

At level $17$, the entire Eisenstein index is dyadic. Formula (1.8) gives $v_2(n_{17})=2$. This level tests both the extra factor of $2$ in the exact congruence modulus and the impossibility of labeling order-two integral closures by generic characters. Any proof based only on the rational constant term $(17-1)/24$ would see too little.

At level $19$, the sole Eisenstein prime is $3$. Although $3$ divides the automorphism denominator $12$, the coefficient-prime finite-flat theory is in the odd low-ramification range and distinguishes $1$ from $\bar\chi_3$. The exact correction has already occurred numerically in $n_{19}=3$.

Two larger checks are

$$
n_{41}=10,
\qquad n_{73}=6.
\tag{11.3}
$$

They show that different primary completions of the same global quotient must be treated separately. Chinese remaindering reconstructs the cyclic scalar quotient, but it does not identify the associated completed group schemes or extension parameters.

### 11.3 The level prime and the coefficient prime

The level prime $N$ and coefficient prime $\ell$ play opposite roles. The Jacobian has semistable bad reduction at $N$, and its component group measures the failure of strict local points to fill the Néron fiber. At $\ell$, the Jacobian has good reduction because $\ell\ne N$, but connected finite-flat torsion makes ordinary unramified cohomology insufficient.

The operator distinction mirrors the geometry. At $q\ne N$ one has the good-prime polynomial (1.4). At $N$ one uses the incoming $U_N$ and the direct correspondence calculation $U_Nc=c$. Substituting $q=N$ into (1.4) would be invalid.

The formal-immersion prime $p$ is allowed to equal $\ell$. At that prime the tower isomorphism gives the completed cotangent equality (9.9), while the support-operator construction (9.10)--(9.12) supplies the unit first coefficient used in the immersion proof. The prime $p$ must differ from $N$, where the quotient does not have good abelian reduction, and it is taken odd for the cusp-disk consequence.

### 11.4 A normalization ledger

The principal conventions and their consequences are:

| Object | Convention | Consequence |
|---|---|---|
| Exact integer | $n_N=(N-1)/\gcd(N-1,12)$ | correct $2$- and $3$-primary depth |
| Hecke ideal | $T_q-(1+q)$ and incoming $U_N-1$ | boundary and cusp have the same character |
| Correspondence | $(\pi_2)_*\pi_1^*$ | covariance agrees on divisors and Jacobians |
| Frobenius | arithmetic on covariant Tate modules | $F_q^2-T_qF_q+q=0$ |
| Local selection | $e_{\mathfrak m}$ | integral direct factor of torsion |
| Rational selection | $E_{\mathfrak m}$ | optimal quotient over $\mathbf Q$ |
| Support ideal | $E_{\mathfrak m}\mathbb T_{\mathbf Q}\cap\mathbb T$ | integral operators factor through the quotient |
| Coefficient-prime condition | finite flat | connected classes are retained |
| Level-prime condition | identity-component strict | component error is isolated |
| Point-level cusp | outward orientation and $\sigma=w_N\rho$ | standard cusp parameter pulls back by a unit |
| Cotangent test | one support-operator direction | unit first coefficient without a smooth kernel |

A change in any row changes a theorem rather than its notation. For example, replacing $U_N-1$ by the opposite sign selects a different local factor, while replacing finite-flat cohomology by unramified cohomology discards the multiplicative atom at $\ell$.

## 12. The selected Eisenstein theorem

### 12.1 The theorem

We can now state the entire package in one place.

**Theorem 12.1 (prime-level selected Eisenstein package).** Let $N$ be prime, put

$$
n_N=\frac{N-1}{\gcd(N-1,12)},
\qquad
I=(T_q-(1+q):q\ne N)+(U_N-1),
\tag{12.1}
$$

and use the acting Hecke algebra on $S_2(\Gamma_0(N);\mathbf Z)$ with the incoming level operator. In items 4--9, fix any prime $\ell\mid n_N$, put $\mathfrak m=(\ell,I)$, and use the selected quotient and finite-flat tower attached to this choice.

1. The exact Eisenstein quotient, index, and scalar congruence ideal are

   $$
   \mathbb T/I\simeq\mathbf Z/n_N\mathbf Z,
   \qquad[\mathbb T:I]=n_N,
   \qquad\eta_E=(n_N).
   \tag{12.2}
   $$

2. The cuspidal subgroup $C_N=\langle[0]-[\infty]\rangle$ and the component group at $N$ are cyclic of order $n_N$, and specialization gives

   $$
   \mathbb T/I\xrightarrow{\sim}C_N
   \xrightarrow{\sim}\Phi_N(\mathbf F_N).
   \tag{12.3}
   $$

3. The auxiliary Shimura subgroup is diagonalizable cyclic of order $n_N$, noncanonically isomorphic to $\mu_{n_N}$, and annihilated by $I$. No full intersection formula with $C_N$ is included.

4. For every such $\ell$ and $\mathfrak m$,

   $$
   \mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m}
   \simeq\mathbf Z_\ell/\ell^{v_\ell(n_N)}.
   \tag{12.4}
   $$

   The rational support defines an optimal quotient $A_{\mathfrak m}$. Its generic connected-kernel sequence is exact, and the quotient map extends between the good abelian-scheme models over $S_N$; no smooth integral model of the positive-dimensional kernel is asserted.

5. The local idempotent defines two finite-flat direct-factor towers

   $$
   P_r=e_{\mathfrak m}\mathcal J[\ell^r],
   \qquad
   G_r=e_{\mathfrak m}\mathcal A_{\mathfrak m}[\ell^r],
   \tag{12.5}
   $$

   each with exact transition maps. Generic exactness gives the saturated Tate isomorphism

   $$
   e_{\mathfrak m}T_\ell J\xrightarrow{\sim}
   e_{\mathfrak m}T_\ell A_{\mathfrak m}.
   $$

   After admissibility supplies the ordinary endpoint sequences, ordinary-tower rigidity proves that the actual quotient maps $\pi_r:P_r\to G_r$ are isomorphisms over $S_N$ for every $r$.

6. Every $G_r$ is Eisenstein-admissible, filtered by $\underline{\mathbf Z/\ell}$ and $\mu_\ell$. Over $\mathbf Z_\ell$, the direct limit has the canonical sequence

   $$
   0\to G_{\mathfrak m}^{\mathrm{mult}}
   \to G_{\mathfrak m}
   \to G_{\mathfrak m}^{\mathrm{et}}
   \to0.
   \tag{12.6}
   $$

   The principal polarization first makes the Jacobian tower $P_{\mathfrak m}$ perfectly self-dual. Quasi-isogeny gives equality of the two endpoint heights of $G_{\mathfrak m}$; the isomorphisms $P_r\simeq G_r$ then transport perfect integral self-duality to the quotient tower. At $2$, endpoint labels are integral data and extensions retain sign and carry classes.

7. Strict Eisenstein descent gives

   $$
   \operatorname{Sel}^{\mathrm{str}}(G_r)=0
   \quad(r\ge1),
   \qquad
   A_{\mathfrak m}(\mathbf Q)\text{ finite}.
   \tag{12.7}
   $$

   The finite group has Eisenstein residual support and is annihilated by a product of powers as in (8.9); it is not identified exactly.

8. For every prime $p\ne N$, pullback gives an injective Hecke-stable cotangent lattice

   $$
   \pi^*\omega_{A_{\mathfrak m}}
   \hookrightarrow S_2(\Gamma_0(N);\mathbf Z_p)
   $$

   with the correct rational support; its whole cokernel is not asserted to be torsion free. The saturated support ideal $\mathfrak a_E$ supplies $t_p\notin p\mathbb T$, a form $f_p$, and a factorization $t_p=s_{t_p}\pi$ such that $a_1(t_pf_p)$ is a $p$-adic unit. Thus $s_{t_p}^*f_p$ is one quotient cotangent direction primitive in the ambient cusp lattice. At $p=\ell$, the finite-flat tower isomorphisms also give the completed integral equality

   $$
   e_{\mathfrak m}\omega_A\xrightarrow{\sim}
   e_{\mathfrak m}\omega_J.
   $$

9. At every outward rational cusp of $X_1(N)$ and every $p\ne N$, the fixed map

   $$
   X_1(N)\xrightarrow{\ w_N\rho\ }X_0(N)
   \to J_0(N)\to A_{\mathfrak m}
   \tag{12.8}
   $$

   is a formal immersion modulo $p$. If $p$ is odd, a rational point in the same cusp disk is the cusp itself.

For $N\in\{2,3,5,7,13\}$, $n_N=1$ and the assertions requiring $\ell\mid n_N$ are vacuous.

### 12.2 Proof

**Proof.** The Eisenstein series (2.4), the integral two-cusp congruence theorem, and the perfect Hecke--Fourier pairing prove (12.2). The eta quotient gives the upper bound for the cusp order. The weighted monodromy graph gives a cyclic component group of order $n_N$ and shows that the specialized cusp is its generator; this proves (12.3). Descent characters for $X_1(N)\to X_0(N)$ give the diagonalizable subgroup in item 3.

Semilocal decomposition of the finite Hecke algebra gives $e_{\mathfrak m}$ and (12.4). Rational characteristic-zero support gives $E_{\mathfrak m}$ and the generic connected-kernel quotient. The idempotent decompositions of the two ambient torsion groups independently give $P_r$, $G_r$, and their exact transition maps. Generic fppf exactness gives the saturated Tate comparison, but not equality of finite-flat models.

On the residual radical layers, Eichler--Shimura factors as $(F_q-1)(F_q-q)$. Density forces trivial or cyclotomic simple constituents. Closing an actual stable flag gives admissible finite-flat filtrations; the unramified order-two classification supplies the dyadic endpoints. The connected--etale sequence then yields (12.6).

The prime-level Rosati involution fixes the Hecke generators and hence the local idempotent. The principal polarization therefore restricts perfectly to $P_{\mathfrak m}$. Its quasi-isogeny with the ordinary quotient tower first equates the endpoint heights. The determinant argument on the canonical endpoints, followed by full faithfulness for finite etale groups, Cartier duality, and the short five lemma, proves $P_r\simeq G_r$. Only then is the perfect pairing transported to $G_r$.

Kummer theory kills the strict Selmer groups of both atoms. Cartesian devissage preserves this vanishing through every admissible extension. The difference between strict and relaxed Kummer images lies in fixed finite component groups. Uniform boundedness through all $\ell^r$ forces zero rank, and finite generation gives (12.7).

Finally, $\mathfrak a_E=E\mathbb T_{\mathbf Q}\cap\mathbb T$ is nonzero and saturated. For each $p$, perfect Hecke--Fourier duality detects an element $t_p\notin p\mathbb T$ by a form $f_p$ with unit first coefficient. Because $t_p$ vanishes on the generic optimal kernel, it factors as $s_{t_p}\pi$; extension of $s_{t_p}$ over $\mathbf Z_p$ turns $s_{t_p}^*f_p$ into an actual quotient cotangent vector. Its pullback along the fixed oriented map spans the cusp cotangent line, proving formal immersion without a Lie sequence or a target Hecke translate. Finiteness of the selected rational group and injectivity of torsion specialization at an odd good prime give cusp-disk separation. $\square$

### 12.3 Dependency and hypothesis audit

The algebraic language of faithful image algebras, localization, completion, congruence modules, and the limits of Gorenstein criteria comes from Book 85. We use it only for the finite torsion-free algebra acting on the stated integral lattice.

Book 113 supplies the integral modular-form lattice, all-cusp $q$-expansion, regular dualizing interpretation in weight two, coefficient formula, and base change. Its stack conditions are retained at $2$ and $3$.

Book 114 supplies the integral correspondence action on Jacobians and Néron models, covariance and Rosati adjunction, the good-prime Eichler--Shimura polynomial, and the Néron cotangent lattice. The polynomial is used only at $q\nmid N\ell$.

Book 167 supplies the finite Chebotarev statement used in Section 6.2: every conjugacy class in the finite quotient cut out by a radical layer and $\bar\chi_\ell$ occurs as arithmetic Frobenius at some $q\nmid N\ell$. Density transports an operator identity to that finite quotient; it is not used to infer a stable flag from traces.

Book 131 supplies the pointed Albanese map, optimal quotient formalism, prime-level Néron geometry, and the distinction between finite subgroup schemes, rational points, and components. Its selected-quotient statements have the same incoming $U_N$ convention. We also retain its distinction between the rational-support quotient and the winding quotient; no winding-ideal finiteness theorem is imported.

Book 132 proves the exact two-cusp congruence and index, including the distinct $2$- and $3$-primary corrections. It asserts no multiplicity one, Gorenstein property, or rational torsion theorem, and none is inferred here.

Book 133 supplies the exact cusp order, weighted component calculation, specialization isomorphism, Hecke action, and the auxiliary diagonalizable subgroup. It explicitly leaves the full cusp--Shimura intersection and full rational torsion open.

Book 134 supplies schematic-closure devissage, admissible atoms, odd mixed-extension classes, and the dyadic sign and carry. We apply its closure theorem only after Book 146's actual stable generic flag has been produced.

Book 146 supplies the local idempotent, rational-support quotient, the two independently exact towers $P_r$ and $G_r$, the saturated generic Tate comparison, an actual Eisenstein flag, admissibility at all powers, and the connected--etale sequence. Its Theorem 8.1 proves $P_r\simeq G_r$ only after the ordinary endpoint sequences are available and then transports perfect self-duality to $G_r$. We use that theorem in Sections 7.3 and 9.3. We also retain its explicit negative conclusion: it does not make the positive-dimensional integral kernel smooth and does not give an exact sequence of abelian schemes with that kernel.

Book 147 supplies the strict local conditions, atomic calculations, cartesian devissage, uniform component bound, rank-zero argument, residual support, and power annihilator. We preserve its exact conclusion: finiteness, not identification of the selected rational group.

Book 148 supplies the outward-cusp orientation $\sigma=w_N\rho$, the unit relation between its point-level parameter and the standard parameter at $\infty$, and the completed-local-ring criterion separating sections under a formal immersion. We do **not** import an exact-kernel Lie argument or a whole-lattice primitivity assertion from it. Lemma 9.1 and Section 9.4 prove the required quotient cotangent direction inside this book, and Section 10 applies the general criterion only at odd good primes for rational section separation.

Books 132--134 and 146--148 are the specialist proof volumes feeding this capstone. None imports Book 169: their dependency chain runs $132\to133\to134\to146\to147\to148$ (with additional earlier prerequisites), and Book 169 only assembles their established outputs. Book 167 is an additional independent input. All these sources precede Book 169, so the current numerical order is topological. Thus no conclusion in this book is imported through a path that returns to Book 169.

All hypotheses match. The level is prime and the character is trivial. The coefficient prime satisfies $\ell\mid n_N$, hence $\ell\ne N$. Torsion group schemes are considered over $\mathbf Z[1/N]$, where the two ambient Néron models are abelian schemes. Formal immersion is taken at $p\ne N$, and rational section separation at odd $p$. No assertion depends on a smooth model for the generic optimal kernel.

### 12.4 Excluded strengthenings

The following statements are not part of Theorem 12.1:

- $J_0(N)(\mathbf Q)_{\mathrm{tors}}=C_N$;

- $A_{\mathfrak m}(\mathbf Q)$ equals the image of $C_N$;

- $I$ annihilates $A_{\mathfrak m}(\mathbf Q)$ rather than a power determined by its Loewy filtration;

- $C_N\cap\Sigma_N$ has a specified full scheme-theoretic form;

- $J[\mathfrak m]$ has dimension two for every Eisenstein maximal ideal;

- $T_\ell J_{\mathfrak m}$ is free of rank two over $\mathbb T_{\mathfrak m}$;

- $\mathbb T_{\mathfrak m}$ is Gorenstein or a complete intersection;

- the connected--etale sequence (12.6) splits;

- the generic optimal sequence extends to an exact sequence of abelian schemes with smooth kernel;

- a generic or Tate-module isomorphism alone identifies two finite-flat models;

- the whole quotient cotangent lattice is primitive with arbitrary base change at every good prime;

- the selected rational-support quotient is the winding quotient;

- rational torsion specializes injectively on $A_{\mathfrak m}$ at $2$; or

- formal immersion at an outward cusp automatically gives formal immersion at every cusp orientation.

Each omitted assertion requires information not contained in the exact index, admissible filtration, or selected descent. Stating the boundary is part of the theorem: it prevents equal cardinalities, semisimplifications, and rational projectors from being substituted for the integral maps actually proved.

## 13. Conclusion

The Eisenstein ideal begins with the boundary eigenvalues $1+q$ and $1$, but its arithmetic meaning appears only after several integral realizations are compared. The two-cusp modular-form calculation gives the exact scalar collision

$$
\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z.
$$

The eta multiplier produces a cusp class of bounded order, while the weighted monodromy graph proves that its specialization is a primitive component of exact order $n_N$. The Shimura covering supplies the Cartier-dual multiplicative direction without being confused with either the cusp or the component group.

At an Eisenstein prime, local completion and rational support solve different problems. The local idempotent creates integral direct factors in the torsion of both $J$ and the optimal quotient. Generic exactness makes their selected Tate lattices agree, but does not identify their finite-flat models. Admissibility makes the compatible towers ordinary; endpoint rigidity then proves their levelwise equality and only then transports perfect self-duality. The quotient tower has admissible constant and multiplicative constituents, including the full dyadic endpoint, sign, and carry data.

Descent then proceeds through actual extensions rather than a semisimplification. The strict Selmer groups of the two atoms vanish; cartesian devissage carries that vanishing through the tower; the remaining level and real component defects are uniformly finite. The selected quotient therefore has rank zero and finite rational points, with precisely Eisenstein residual support but without an unsupported exact torsion formula.

Finally, the saturated support ideal provides, at every good prime, an integral Hecke operator that is nonzero modulo that prime and factors through the optimal quotient. Perfect Hecke--Fourier duality turns it into one actual quotient differential with unit first coefficient. This proves that the fixed outward oriented map itself is a formal immersion, without claiming that the entire quotient cotangent lattice is primitive. Finiteness and odd good-prime specialization then turn first-order nondegeneracy into rational cusp-disk rigidity.

The completed package is therefore

$$
\text{exact congruence}
\longrightarrow
\text{cuspidal specialization}
\longrightarrow
\text{selected finite-flat tower}
\longrightarrow
\text{Eisenstein descent}
\longrightarrow
\text{support cotangents and formal immersion}.
$$

Its strength comes from the precision of each arrow. The exact index is not multiplicity one; equal orders are not an intersection theorem; ordinary constituents are not a split group; residual support is not annihilation by $I$; and a rational quotient is not an integral local projector. With those boundaries fixed, the selected Eisenstein quotient provides the complete algebraic and geometric engine needed for the prime-level rational-point argument.
