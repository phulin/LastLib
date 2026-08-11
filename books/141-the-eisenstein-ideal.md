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
   - [Primitivity and base change](#92-primitivity-and-base-change)
   - [The completed comparison](#93-the-completed-comparison)
   - [Fourier coefficients as cotangent coordinates](#94-fourier-coefficients-as-cotangent-coordinates)
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

Primes indexing Hecke operators are denoted $q$; a prime dividing the Eisenstein index is denoted $\ell$; a residue characteristic used for formal immersion is denoted $r$. This separation prevents the level prime, coefficient prime, and specialization prime from being silently identified.

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

Third, for each $\ell\mid n_N$, the complete local factor of $\mathbb T\otimes\mathbf Z_\ell$ gives an integral idempotent. Its rational support, a different construction, gives an optimal quotient $A_{\mathfrak m}$. Exactness for the connected kernel proves that the two selections agree on the selected Tate lattice. Only then is there an honest finite-flat tower on which descent may operate.

Fourth, the Eichler--Shimura polynomial and a radical filtration produce actual residual constant and cyclotomic factors. Schematic closure turns them into admissible finite-flat atoms. Strict Selmer vanishing, followed by a finite component correction, forces the selected Mordell--Weil rank to vanish. Finite generation then gives finiteness.

Finally, the connected optimal quotient makes its Néron cotangent lattice primitive. The first-coefficient identity converts a nonzero reduced differential into a unit cotangent at an outward cusp of $X_1(N)$. This proves formal immersion. At an odd good prime, injectivity of torsion specialization combines with finiteness to separate rational sections in that cusp disk.

## 2. The integral Hecke algebra and the exact index

### 2.1 The acting algebra

Because $S$ is finite free over $\mathbf Z$, its faithful Hecke image $\mathbb T$ is a finite torsion-free commutative $\mathbf Z$-algebra. It is therefore finite free as a $\mathbf Z$-module. The distinction between an abstract operator algebra and its image matters: an index is meaningful only after the integral lattice and faithful image have been fixed.

For $m\ge1$, write $T_m$ for the usual operator, with the level convention

$$
T_{N^au}=U_N^aT_u,
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

The quotient is nonzero. Indeed, the $\ell$-primary cusp class is a nonzero $I$-torsion class by (3.8), so its Hecke support contains $\mathfrak m$ and the rational support above $\mathfrak m$ cannot be empty. The kernel is connected, so (4.6) is optimal. Over $S_N=\operatorname{Spec}\mathbf Z[1/N]$, where $J$ has good reduction, it extends to an exact sequence of abelian schemes

$$
0\longrightarrow\mathcal K_{\mathfrak m}
\longrightarrow\mathcal J
\longrightarrow\mathcal A_{\mathfrak m}
\longrightarrow0.
\tag{4.7}
$$

### 4.3 Why the two projectors differ

The rational projector $E_{\mathfrak m}$ must retain an entire Galois orbit of newform factors in order to define a quotient over $\mathbf Q$. The local idempotent $e_{\mathfrak m}$ selects one completion above $\ell$. If a coefficient field has several primes above $\ell$, the rational quotient retains all companions while the completed torsion retains only the chosen one.

Symbolically,

$$
\begin{array}{ccc}
\text{characteristic-zero factors}&\xrightarrow{E_{\mathfrak m}}&A_{\mathfrak m}\text{ over }\mathbf Q,\\
\text{$\ell$-adic local factors}&\xrightarrow{e_{\mathfrak m}}&G_{\mathfrak m}\text{ over }\mathbf Z[1/N].
\end{array}
\tag{4.8}
$$

No equality $E_{\mathfrak m}=e_{\mathfrak m}$ is asserted. Their compatibility is instead a theorem about the selected Tate lattice, proved from exactness of the optimal quotient.

### 4.4 The exact local congruence depth

Tensoring (2.9) with $\mathbf Z_\ell$ and projecting to the unique Eisenstein local factor gives

$$
\boxed{
\mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m}
\simeq
\mathbf Z_\ell/\ell^e\mathbf Z_\ell,
\qquad e=v_\ell(n_N).}
\tag{4.9}
$$

Thus the scalar boundary congruence has exact depth $e$. It follows that an Eisenstein maximal ideal exists precisely for $\ell\mid n_N$.

What does not follow is equally important. The vector space $\mathfrak m/(\mathfrak m^2,\ell)$ can have dimension greater than one even when (4.9) is cyclic. Several characteristic-zero branches can meet the Eisenstein point. The localized Tate module can require more than two generators. The algebra can fail to be Gorenstein. Formula (4.9) controls the quotient by $I$, not the whole local singularity.

## 5. The selected finite-flat tower

### 5.1 Construction by integral idempotents

Let $\mathcal J$ be the abelian scheme over $S_N=\operatorname{Spec}\mathbf Z[1/N]$ obtained from the Néron model of $J$. Since $\ell\ne N$, multiplication by $\ell^r$ is faithfully flat and $\mathcal J[\ell^r]$ is finite flat over $S_N$ for every $r\ge1$. Define

$$
G_r=e_{\mathfrak m}\mathcal J[\ell^r].
\tag{5.1}
$$

Because the image of an idempotent is a direct factor,

$$
\mathcal J[\ell^r]
=G_r\times(1-e_{\mathfrak m})\mathcal J[\ell^r].
\tag{5.2}
$$

Thus $G_r$ is finite flat without any separate flatness theorem for a kernel of Hecke operators. This is why completion precedes torsion: the schematic kernel of the generators of $I$ could acquire vertical nonflat structure, whereas an idempotent image is automatically a direct factor.

The construction is compatible with base change. Over $\mathbf Q$, it selects the generalized $\mathfrak m$-summand of $J[\ell^r]$. Over $\mathbf Z_\ell$, it retains its connected and etale parts. At a prime away from $N\ell$, it is finite etale and carries the usual unramified Frobenius action.

### 5.2 Exact transition maps

The full torsion tower has exact sequences

$$
0\longrightarrow\mathcal J[\ell^r]
\longrightarrow\mathcal J[\ell^{r+s}]
\xrightarrow{\ell^r}\mathcal J[\ell^s]
\longrightarrow0.
\tag{5.3}
$$

The maps commute with $e_{\mathfrak m}$. Applying the direct-factor functor gives

$$
0\longrightarrow G_r
\longrightarrow G_{r+s}
\xrightarrow{\ell^r}G_s
\longrightarrow0.
\tag{5.4}
$$

Exactness here means exactness for the faithfully flat topology: the last arrow is faithfully flat and its kernel is $G_r$. One verifies this by applying the decomposition (5.2) throughout (5.3).

Consequently

$$
G_{\mathfrak m}=\varinjlim_rG_r
\tag{5.5}
$$

is an $\ell$-divisible group over $S_N$. It is not merely a compatible family of generic Galois modules. The flat exactness of (5.4) records integral divisibility at the coefficient prime.

### 5.3 Comparison with the selected quotient

The optimal sequence (4.7) gives, on covariant Tate modules,

$$
0\longrightarrow T_\ell K_{\mathfrak m}
\longrightarrow T_\ell J
\longrightarrow T_\ell A_{\mathfrak m}
\longrightarrow0.
\tag{5.6}
$$

The rational support of $K_{\mathfrak m}$ is complementary to $E_{\mathfrak m}$. Hence $e_{\mathfrak m}$ acts as zero on $T_\ell K_{\mathfrak m}$. Applying it to (5.6) gives

$$
\boxed{
e_{\mathfrak m}T_\ell J
\xrightarrow{\sim}
e_{\mathfrak m}T_\ell A_{\mathfrak m}.}
\tag{5.7}
$$

The same argument at finite level, using exactness of multiplication on the connected kernel, yields

$$
G_r\xrightarrow{\sim}
e_{\mathfrak m}\mathcal A_{\mathfrak m}[\ell^r]
\quad(r\ge1).
\tag{5.8}
$$

This is the promised compatibility of the rational and local selections. It is a saturated integral statement, not an identification of projectors. In particular, no quotient of lattices in (5.7) has hidden $\ell$-torsion.

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

Let $e=v_\ell(n_N)$. The $\ell$-primary cusp and Shimura groups both have order $\ell^e$. Their generic fibers lie in the selected rational support, hence in $G_e$ after (5.8). Taking schematic closures gives finite-flat subgroups

$$
\mathcal C_{N,\ell},\ \mathcal\Sigma_{N,\ell}\subseteq G_e.
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

They give named constant and multiplicative directions, but need not exhaust the etale and multiplicative heights. Additional congruent characteristic-zero branches can enlarge the completed piece without changing (4.9).

At $2$, the closures remain admissible but their generic labels do not determine every integral endpoint. No formula for their full intersection is used.

### 7.3 Duality and height

The principal polarization of $J$ gives a perfect Weil pairing, with its Tate twist. The Rosati involution carries a selected local factor to its adjoint factor. In the present prime-level normalization, every generator of the commutative Hecke algebra is Rosati self-adjoint. Hence

$$
e_{\mathfrak m}^{\dagger}=e_{\mathfrak m},
\qquad
G_{\mathfrak m}^D\simeq G_{\mathfrak m}.
$$

Thus (7.1) is dual to itself with endpoints reversed, and

$$
\operatorname{ht}(G_{\mathfrak m}^{\mathrm{mult}})
=\operatorname{ht}(G_{\mathfrak m}^{\mathrm{et}}).
\tag{7.5}
$$

This determines only the equality of the heights, not that each is one. The selected ordinary group can have height $2d$ with $d>1$.

### 7.4 Multiplicity one and Gorenstein boundaries

**Proposition 7.1.** Let $R=\mathbb T_{\mathfrak m}$. Suppose that the selected Tate module is finite free of rank $2$ over $R$, and suppose an integral polarization and primitive endpoint comparison identify

$$
R^\vee=\operatorname{Hom}_{\mathbf Z_\ell}(R,\mathbf Z_\ell)
$$

with a free rank-one $R$-module. Then $R$ is Gorenstein and the residual selected representation has dimension two.

**Proof.** For a finite flat local $\mathbf Z_\ell$-algebra, freeness of $R^\vee$ of rank one over $R$ is exactly the Gorenstein self-duality criterion. The Tate-module hypothesis gives $M\simeq R^2$; reducing modulo the maximal ideal gives a two-dimensional residual module. $\square$

These hypotheses are not proved for every Eisenstein maximal ideal here. In particular, (4.9) does not imply rank-two freeness or the displayed dual identification. Therefore no unconditional complete multiplicity-one or Gorenstein assertion is made.

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

Let $r\ne N$ be a prime. Over $\mathbf Z_r$, both $J$ and $A=A_{\mathfrak m}$ have good reduction. Write $\mathcal J_r$ and $\mathcal A_r$ for their abelian schemes and define their invariant cotangent modules

$$
\omega_J=e_J^*\Omega^1_{\mathcal J_r/\mathbf Z_r},
\qquad
\omega_A=e_A^*\Omega^1_{\mathcal A_r/\mathbf Z_r}.
\tag{9.1}
$$

Pullback along the optimal quotient embeds $\omega_A$ into $\omega_J$. The Abel--Jacobi identification and the weight-two Kodaira--Spencer theorem identify

$$
\omega_J\simeq S_2(\Gamma_0(N);\mathbf Z_r).
\tag{9.2}
$$

Define the selected cotangent lattice

$$
\Omega_{\mathfrak m,r}
=\operatorname{im}(\omega_A\to\omega_J)
\subseteq S_2(\Gamma_0(N);\mathbf Z_r).
\tag{9.3}
$$

It is Hecke stable because the quotient is defined by rational Hecke support and the endomorphisms extend to the good Néron models. Its rational span is the sum of precisely those newform factors retained by $E_{\mathfrak m}$.

This definition uses invariant differentials of the actual optimal quotient. Taking the intersection of a rational newform subspace with a convenient $q$-expansion lattice could give the wrong answer at a prime dividing a congruence degree.

### 9.2 Primitivity and base change

Dualizing the exact sequence (4.7) over $\mathbf Z_r$ gives an exact sequence of Lie algebras and hence an exact cotangent sequence

$$
0\longrightarrow\omega_A
\longrightarrow\omega_J
\longrightarrow\omega_K
\longrightarrow0.
\tag{9.4}
$$

All three terms are finite free over $\mathbf Z_r$. It follows that $\omega_J/\Omega_{\mathfrak m,r}$ is finite free, so $\Omega_{\mathfrak m,r}$ is primitive. Tensoring (9.4) with any $\mathbf Z_r$-algebra remains exact. Therefore the inclusion (9.3) and its quotient commute with arbitrary base change.

**Theorem 9.1.** For every $r\ne N$, the Néron cotangent lattice $\Omega_{\mathfrak m,r}$ is a primitive Hecke-stable sublattice of $S_2(\Gamma_0(N);\mathbf Z_r)$, and

$$
\Omega_{\mathfrak m,r}\otimes R
\hookrightarrow S_2(\Gamma_0(N);\mathbf Z_r)\otimes R
\tag{9.5}
$$

is injective with finite free quotient for every $\mathbf Z_r$-algebra $R$.

**Proof.** The quotient map extends to the exact abelian-scheme sequence (4.7) after base change to $\mathbf Z_r$. Smoothness makes the associated Lie sequence exact and locally split. Dualizing gives (9.4), whose cokernel $\omega_K$ is finite free. The identification (9.2) places the first term inside the integral cusp lattice. Hecke stability follows because every selected Hecke endomorphism extends over good reduction and preserves the connected kernel. Tensoring a split exact sequence of finite free modules with $R$ preserves exactness, proving base change and primitivity. $\square$

Primitivity ensures that a nonzero invariant differential on $A$ does not disappear when viewed on $J$ modulo $r$. This is exactly the integral information needed for formal immersion.

### 9.3 The completed comparison

At $r=\ell$, a statement only about rational Tate spaces would not control the integral cotangent index. Instead use the finite-flat comparison (5.8). For any abelian scheme $B/\mathbf Z_\ell$, the conormal sequence for multiplication by $\ell^n$ gives a functorial identity

$$
\omega_{B[\ell^n]}
\simeq\omega_B/\ell^n\omega_B.
$$

Apply this identity to the selected finite-flat towers of $J$ and $A$, which (5.8) identifies at every $n$. Contravariance of invariant differentials gives isomorphisms of their selected cotangent modules modulo $\ell^n$, compatible in $n$. Taking inverse limits gives

$$
e_{\mathfrak m}\omega_A
\xrightarrow{\sim}
e_{\mathfrak m}\omega_J.
\tag{9.6}
$$

This equality is on integral lattices. Equivalently, apply $e_{\mathfrak m}$ to (9.4): the selected part of $\mathcal K_{\mathfrak m}[\ell^n]$ vanishes for every $n$, so the same conormal identity gives $e_{\mathfrak m}\omega_K/\ell^n=0$ for every $n$, and completeness gives $e_{\mathfrak m}\omega_K=0$. It is the finite-flat tower, connectedness of the optimal kernel, exactness of the abelian-scheme sequence, and the direct-summand nature of $e_{\mathfrak m}$ that remove the possible $\ell$-power index.

The cotangent theorem does not claim that $\Omega_{\mathfrak m,\ell}$ is free of rank one over $\mathbb T_{\mathfrak m}$. It may have larger Hecke rank when several branches occur. Formal immersion needs only a nonzero reduced differential and a Fourier coefficient that detects it.

### 9.4 Fourier coefficients as cotangent coordinates

Let $0\ne\bar f\in\Omega_{\mathfrak m,r}/r\Omega_{\mathfrak m,r}$. Since the inclusion is primitive, $\bar f$ is nonzero as a regular dualizing cusp form modulo $r$. The integral $q$-expansion principle gives some $m\ge1$ with

$$
a_m(\bar f)\ne0.
\tag{9.7}
$$

Using $T_m$, including the incoming $U_N$ in the $N$-power part, the coefficient identity gives

$$
a_1(T_mf)=a_m(f).
\tag{9.8}
$$

Thus a suitable Hecke translate moves a nonzero Fourier coefficient into the cotangent coordinate at the cusp. The integer $m$ may depend on $r$ and on the chosen differential. No uniform first coefficient is required.

At $r=2$ or $3$, (9.7) refers to the regular dualizing lattice on the compactified modular object. Stabilizer descent is already built into the lattice, so reduction does not use a naive coarse differential.

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

### 10.2 The cotangent calculation

Choose a primitive $f\in\Omega_{\mathfrak m,r}$ with nonzero reduction. By (9.7), choose $m$ such that $a_m(f)$ is a unit modulo $r$, and replace $h$ by the Hecke translate

$$
h_m=T_m\circ h.
\tag{10.5}
$$

The target endomorphism $T_m$ is normalized so that its pullback on cotangents is the weight-two operator in (2.2); for the level part this uses $U_N=-w_N$ on weight-two cusp forms. Let $q$ be the standard parameter at $\infty$ and $t$ an outward point-level parameter. Compatible frames give

$$
\sigma^*q=ut+O(t^2),
\qquad u\in\mathbf Z_r^\times.
\tag{10.6}
$$

Downstairs, the pullback of the invariant differential corresponding to $f$ has first-order expansion

$$
(T_mf)(q)\frac{dq}{q}
=\bigl(a_1(T_mf)+O(q)\bigr)dq.
$$

By (9.8) and (10.6), its pullback has image in the cotangent line at $c_1$

$$
u\,a_m(f)\,dt,
\tag{10.7}
$$

which is a basis modulo $r$. Hence the map on cotangent spaces is surjective.

**Theorem 10.1.** For every prime $r\ne N$ and every outward rational cusp of $X_1(N)$, some Hecke translate of (10.4) is a formal immersion at that cusp modulo $r$.

**Proof.** A morphism from a relative curve to a smooth group scheme is a formal immersion at a section if the induced map on cotangent spaces is surjective. Equations (10.6)--(10.7) prove precisely that condition. The outward orientation and the use of $\sigma=w_N\rho$ ensure that the standard parameter $q$ remains a uniformizer after pullback from $X_0(N)$. $\square$

The Hecke translate is not an artificial modification of the geometry. It merely chooses a cotangent coordinate in which the nonzero selected differential has unit first coefficient.

### 10.3 Separation in an odd cusp disk

Formal immersion separates two sections once their images in the finite quotient agree. Let $r$ be odd, $r\ne N$, and let $x\in X_1(N)(\mathbf Q)$ reduce to the same outward cusp $c_1$ modulo $r$. By (8.6), $A(\mathbf Q)$ is finite. The difference

$$
h(x)-h(c_1)=h(x)
\tag{10.8}
$$

is torsion and specializes to zero.

At an odd good prime, rational torsion on an abelian variety specializes injectively. Indeed, prime-to-$r$ torsion is etale and hence injects under reduction. An $r$-power torsion point in the kernel lies in the formal group over the unramified field $\mathbf Q_r$; the formal logarithm on a sufficiently deep subgroup and the torsion-freeness of its additive lattice show that this kernel has no nonzero rational $r$-power torsion. Therefore $h(x)=0$.

It follows that $h_m(x)=h_m(c_1)$. A formal immersion separates two sections with the same special point and the same image: surjectivity on completed cotangent spaces makes the induced map of completed local rings surjective, so equality after composition forces equality of the two local homomorphisms. Hence

$$
\boxed{x\equiv c_1\pmod r, r\text{ odd}, r\ne N
\quad\Longrightarrow\quad x=c_1.}
\tag{10.9}
$$

This is the cusp-disk rigidity exported by the selected quotient.

### 10.4 Limits of the argument

Three boundaries are essential.

First, at $r=2$ the formal-immersion theorem remains true, but the torsion-specialization argument used in (10.9) is not asserted. The rational formal group can contain subtler two-primary behavior. One needs a quotient-specific specialization-kernel theorem before deriving dyadic cusp-disk rigidity.

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

The formal-immersion prime $r$ is allowed to equal $\ell$, because the primitive cotangent comparison (9.6) prevents the selected differential from vanishing modulo $\ell$. It must differ from $N$, where the quotient does not have good abelian reduction, and it is taken odd for the cusp-disk consequence.

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
| Coefficient-prime condition | finite flat | connected classes are retained |
| Level-prime condition | identity-component strict | component error is isolated |
| Point-level cusp | outward orientation and $\sigma=w_N\rho$ | standard cusp parameter pulls back by a unit |
| Cotangent lattice | Néron dualizing lattice | reduction remains primitive |

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

   The rational support defines an optimal quotient $A_{\mathfrak m}$, while the local idempotent defines finite-flat groups $G_r$ with exact transition maps.

5. The rational and integral selections agree on the selected tower:

   $$
   e_{\mathfrak m}T_\ell J\simeq
   e_{\mathfrak m}T_\ell A_{\mathfrak m},
   \qquad
   G_r\simeq e_{\mathfrak m}\mathcal A_{\mathfrak m}[\ell^r].
   \tag{12.5}
   $$

6. Every $G_r$ is Eisenstein-admissible, filtered by $\underline{\mathbf Z/\ell}$ and $\mu_\ell$. Over $\mathbf Z_\ell$, the direct limit has the canonical sequence

   $$
   0\to G_{\mathfrak m}^{\mathrm{mult}}
   \to G_{\mathfrak m}
   \to G_{\mathfrak m}^{\mathrm{et}}
   \to0.
   \tag{12.6}
   $$

   The prime-level polarization makes this selected divisible group self-dual, so the two endpoint heights are equal. At $2$, endpoint labels are integral data and extensions retain sign and carry classes.

7. Strict Eisenstein descent gives

   $$
   \operatorname{Sel}^{\mathrm{str}}(G_r)=0
   \quad(r\ge1),
   \qquad
   A_{\mathfrak m}(\mathbf Q)\text{ finite}.
   \tag{12.7}
   $$

   The finite group has Eisenstein residual support and is annihilated by a product of powers as in (8.9); it is not identified exactly.

8. For every prime $r\ne N$, the cotangent lattice of $A_{\mathfrak m}$ is a primitive Hecke-stable sublattice of $S_2(\Gamma_0(N);\mathbf Z_r)$, compatible with base change. At $r=\ell$ it agrees with the completed selected cotangent summand.

9. At every outward rational cusp of $X_1(N)$ and every $r\ne N$, a Hecke translate of

   $$
   X_1(N)\xrightarrow{\ w_N\rho\ }X_0(N)
   \to J_0(N)\to A_{\mathfrak m}
   \tag{12.8}
   $$

   is a formal immersion modulo $r$. If $r$ is odd, a rational point in the same cusp disk is the cusp itself.

For $N\in\{2,3,5,7,13\}$, $n_N=1$ and the assertions requiring $\ell\mid n_N$ are vacuous.

### 12.2 Proof

**Proof.** The Eisenstein series (2.4), the integral two-cusp congruence theorem, and the perfect Hecke--Fourier pairing prove (12.2). The eta quotient gives the upper bound for the cusp order. The weighted monodromy graph gives a cyclic component group of order $n_N$ and shows that the specialized cusp is its generator; this proves (12.3). Descent characters for $X_1(N)\to X_0(N)$ give the diagonalizable subgroup in item 3.

Semilocal decomposition of the finite Hecke algebra gives $e_{\mathfrak m}$ and (12.4). Rational characteristic-zero support gives $E_{\mathfrak m}$ and the connected-kernel quotient. Applying the local idempotent to the exact Tate sequence proves (12.5). Applying it to the full finite-flat torsion tower gives exact transition maps.

On the residual radical layers, Eichler--Shimura factors as $(F_q-1)(F_q-q)$. Density forces trivial or cyclotomic simple constituents. Closing an actual stable flag gives admissible finite-flat filtrations; the unramified order-two classification supplies the dyadic endpoints. The connected--etale sequence then yields (12.6).

The prime-level Rosati involution fixes the Hecke generators and hence the local idempotent. The principal polarization therefore restricts to a perfect self-duality of the selected divisible group, which exchanges the multiplicative and etale endpoints and proves their heights equal.

Kummer theory kills the strict Selmer groups of both atoms. Cartesian devissage preserves this vanishing through every admissible extension. The difference between strict and relaxed Kummer images lies in fixed finite component groups. Uniform boundedness through all $\ell^r$ forces zero rank, and finite generation gives (12.7).

Finally, exactness of the optimal quotient over every good base gives a primitive cotangent sequence. The $q$-expansion principle finds a nonzero coefficient modulo $r$, and a Hecke translate moves it to $a_1$. At an outward cusp this coefficient spans the cotangent line, proving formal immersion. Finiteness of the selected rational group and injectivity of torsion specialization at an odd good prime give cusp-disk separation. $\square$

### 12.3 Dependency and hypothesis audit

The algebraic language of faithful image algebras, localization, completion, congruence modules, and the limits of Gorenstein criteria comes from Book 91. We use it only for the finite torsion-free algebra acting on the stated integral lattice.

Book 119 supplies the integral modular-form lattice, all-cusp $q$-expansion, regular dualizing interpretation in weight two, coefficient formula, and base change. Its stack conditions are retained at $2$ and $3$.

Book 121 supplies the integral correspondence action on Jacobians and Néron models, covariance and Rosati adjunction, the good-prime Eichler--Shimura polynomial, and the Néron cotangent lattice. The polynomial is used only at $q\nmid N\ell$.

The companion Chebotarev development supplies the finite density statement used in Section 6.2: every conjugacy class in the finite quotient cut out by a radical layer and $\bar\chi_\ell$ occurs as arithmetic Frobenius at some $q\nmid N\ell$. Density transports an operator identity to that finite quotient; it is not used to infer a stable flag from traces.

Book 140 supplies the pointed Albanese map, optimal quotient formalism, prime-level Néron geometry, and the distinction between finite subgroup schemes, rational points, and components. Its selected-quotient statements have the same incoming $U_N$ convention.

Book 142 proves the exact two-cusp congruence and index, including the distinct $2$- and $3$-primary corrections. It asserts no multiplicity one, Gorenstein property, or rational torsion theorem, and none is inferred here.

Book 143 supplies the exact cusp order, weighted component calculation, specialization isomorphism, Hecke action, and the auxiliary diagonalizable subgroup. It explicitly leaves the full cusp--Shimura intersection and full rational torsion open.

Book 144 supplies schematic-closure devissage, admissible atoms, odd mixed-extension classes, and the dyadic sign and carry. We apply its closure theorem only after Book 145's actual stable generic flag has been produced.

Book 145 supplies the local idempotent, rational-support quotient, saturated Tate comparison, exact finite-flat tower, actual Eisenstein flag, admissibility at all powers, and connected--etale sequence. Its conclusion explicitly excludes complete multiplicity one and freeness over the local Hecke algebra.

Book 146 supplies the strict local conditions, atomic calculations, cartesian devissage, uniform component bound, rank-zero argument, residual support, and power annihilator. We preserve its exact conclusion: finiteness, not identification of the selected rational group.

Book 147 supplies the primitive cotangent comparison and formal immersion at an outward rational cusp of $X_1(N)$. Its oriented map is $\sigma=w_N\rho$, so that the outward cusp maps to the standard Fourier-expansion cusp $\infty$ with unit cotangent. We use its cusp-disk theorem only at odd good primes and do not promote it to an inward or dyadic statement.

Books 142--147 are the specialist proof volumes feeding this capstone, despite their later topical numbers. None imports Book 141: their dependency chain runs $142\to143\to144\to145\to146\to147$ (with additional earlier prerequisites), and Book 141 only assembles their established outputs. Thus no conclusion in this book is imported through a path that returns to Book 141.

All hypotheses match. The level is prime and the character is trivial. The coefficient prime satisfies $\ell\mid n_N$, hence $\ell\ne N$. Torsion group schemes are considered over $\mathbf Z[1/N]$, where the Néron models are abelian schemes. Formal immersion is taken at $r\ne N$, and rational section separation at odd $r$. No later classification theorem enters the proof.

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

- rational torsion specializes injectively on $A_{\mathfrak m}$ at $2$; or

- formal immersion at an outward cusp automatically gives formal immersion at every cusp orientation.

Each omitted assertion requires information not contained in the exact index, admissible filtration, or selected descent. Stating the boundary is part of the theorem: it prevents equal cardinalities, semisimplifications, and rational projectors from being substituted for the integral maps actually proved.

## 13. Conclusion

The Eisenstein ideal begins with the boundary eigenvalues $1+q$ and $1$, but its arithmetic meaning appears only after several integral realizations are compared. The two-cusp modular-form calculation gives the exact scalar collision

$$
\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z.
$$

The eta multiplier produces a cusp class of bounded order, while the weighted monodromy graph proves that its specialization is a primitive component of exact order $n_N$. The Shimura covering supplies the Cartier-dual multiplicative direction without being confused with either the cusp or the component group.

At an Eisenstein prime, local completion and rational support solve different problems. The local idempotent creates an integral direct factor of every torsion level. The rational projector creates an optimal quotient over $\mathbf Q$. Exactness of the connected kernel makes their Tate lattices agree. The resulting divisible group has admissible constant and multiplicative constituents, including the full dyadic endpoint, sign, and carry data.

Descent then proceeds through actual extensions rather than a semisimplification. The strict Selmer groups of the two atoms vanish; cartesian devissage carries that vanishing through the tower; the remaining level and real component defects are uniformly finite. The selected quotient therefore has rank zero and finite rational points, with precisely Eisenstein residual support but without an unsupported exact torsion formula.

Finally, the optimal quotient has a primitive Néron cotangent lattice. A nonzero reduced differential has a nonzero Fourier coefficient, and a Hecke translate moves that coefficient to the cusp cotangent. At an outward point-level cusp this is the formal-immersion criterion. Finiteness and odd good-prime specialization then turn first-order nondegeneracy into rational cusp-disk rigidity.

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
\text{primitive cotangents and formal immersion}.
$$

Its strength comes from the precision of each arrow. The exact index is not multiplicity one; equal orders are not an intersection theorem; ordinary constituents are not a split group; residual support is not annihilation by $I$; and a rational quotient is not an integral local projector. With those boundaries fixed, the selected Eisenstein quotient provides the complete algebraic and geometric engine needed for the prime-level rational-point argument.
