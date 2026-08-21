# The Chebotarev Density Theorem

## Contents

1. [Why primes should see finite Galois groups](#1-why-primes-should-see-finite-galois-groups)
   - [The distribution problem](#11-the-distribution-problem)
   - [What this theorem does and does not say](#12-what-this-theorem-does-and-does-not-say)
   - [The proof architecture](#13-the-proof-architecture)
   - [Standing conventions and prerequisites](#14-standing-conventions-and-prerequisites)
2. [Frobenius classes in global extensions](#2-frobenius-classes-in-global-extensions)
   - [Decomposition and inertia](#21-decomposition-and-inertia)
   - [Arithmetic and geometric Frobenius](#22-arithmetic-and-geometric-frobenius)
   - [Independence of the prime upstairs](#23-independence-of-the-prime-upstairs)
   - [Restriction, quotient, and change of base](#24-restriction-quotient-and-change-of-base)
   - [Primes in intermediate fields](#25-primes-in-intermediate-fields)
   - [Ramification is a finite exceptional set](#26-ramification-is-a-finite-exceptional-set)
3. [Dirichlet density and its calculus](#3-dirichlet-density-and-its-calculus)
   - [Prime sums and normalization](#31-prime-sums-and-normalization)
   - [Bounded perturbations](#32-bounded-perturbations)
   - [Finite sets, unions, and monotonicity](#33-finite-sets-unions-and-monotonicity)
   - [Residue degree at least two is negligible](#34-residue-degree-at-least-two-is-negligible)
   - [Why Dirichlet density is the right invariant](#35-why-dirichlet-density-is-the-right-invariant)
4. [The zeta singularity at one](#4-the-zeta-singularity-at-one)
   - [Ray partial zeta functions](#41-ray-partial-zeta-functions)
   - [Affine ideal lattices](#42-affine-ideal-lattices)
   - [Theta kernels and Poisson summation](#43-theta-kernels-and-poisson-summation)
   - [Mellin unfolding through the unit lattice](#44-mellin-unfolding-through-the-unit-lattice)
   - [Continuation and the equal-residue theorem](#45-continuation-and-the-equal-residue-theorem)
   - [A power-saving ray-class count](#45a-a-power-saving-ray-class-count)
   - [Dedekind zeta and the full prime sum](#46-dedekind-zeta-and-the-full-prime-sum)
5. [Finite-order Hecke characters at one](#5-finite-order-hecke-characters-at-one)
   - [From ray classes to characters](#51-from-ray-classes-to-characters)
   - [Holomorphy by cancellation of residues](#52-holomorphy-by-cancellation-of-residues)
   - [Nonvanishing by cyclic factorization](#53-nonvanishing-by-cyclic-factorization)
   - [Logarithmic Euler products](#54-logarithmic-euler-products)
   - [The prime-sum character lemma](#55-the-prime-sum-character-lemma)
6. [Artin characters and the exact reduction needed](#6-artin-characters-and-the-exact-reduction-needed)
   - [Artin Euler factors](#61-artin-euler-factors)
   - [Permutation characters and zeta quotients](#62-permutation-characters-and-zeta-quotients)
   - [Induction and Euler products](#63-induction-and-euler-products)
   - [Brauer induction as an alternative route](#64-brauer-induction-as-an-alternative-route)
   - [The holomorphy boundary](#65-the-holomorphy-boundary)
7. [The abelian density theorem](#7-the-abelian-density-theorem)
   - [Orthogonality on a finite abelian group](#71-orthogonality-on-a-finite-abelian-group)
   - [Reciprocity identifies the prime values](#72-reciprocity-identifies-the-prime-values)
   - [Density of one Frobenius element](#73-density-of-one-frobenius-element)
   - [Splitting completely and elementary examples](#74-splitting-completely-and-elementary-examples)
8. [From cyclic subgroups to conjugacy classes](#8-from-cyclic-subgroups-to-conjugacy-classes)
   - [The cyclic fixed field](#81-the-cyclic-fixed-field)
   - [Removing higher residue degrees](#82-removing-higher-residue-degrees)
   - [The centralizer multiplicity](#83-the-centralizer-multiplicity)
   - [The comparison identity](#84-the-comparison-identity)
9. [Chebotarev density](#9-chebotarev-density)
   - [The theorem](#91-the-theorem)
   - [Class functions and averaged prime sums](#92-class-functions-and-averaged-prime-sums)
   - [Ramified primes and changes of convention](#93-ramified-primes-and-changes-of-convention)
   - [No effective assertion is hidden here](#94-no-effective-assertion-is-hidden-here)
10. [Finite-quotient existence and selection](#10-finite-quotient-existence-and-selection)
    - [Avoiding a finite set](#101-avoiding-a-finite-set)
    - [Simultaneous splitting and prescribed Frobenius](#102-simultaneous-splitting-and-prescribed-frobenius)
    - [Witnesses for generators and conjugacy classes](#103-witnesses-for-generators-and-conjugacy-classes)
    - [Intermediate fields and compatible Frobenius powers](#104-intermediate-fields-and-compatible-frobenius-powers)
    - [Density in an absolute Galois group](#105-density-in-an-absolute-galois-group)
11. [Representation-theoretic transport](#11-representation-theoretic-transport)
    - [Continuous class functions are determined by good Frobenius](#111-continuous-class-functions-are-determined-by-good-frobenius)
    - [Brauer--Nesbitt in characteristic zero](#112-brauer--nesbitt-in-characteristic-zero)
    - [Characteristic polynomials and semisimplification](#113-characteristic-polynomials-and-semisimplification)
    - [Order-valued traces and closed conditions](#114-order-valued-traces-and-closed-conditions)
    - [Finite residual quotients](#115-finite-residual-quotients)
    - [Restriction, induction, and Frobenius powers](#116-restriction-induction-and-frobenius-powers)
    - [Limits of transport](#117-limits-of-transport)
12. [The reusable theorem package](#12-the-reusable-theorem-package)
    - [Dependency ledger](#121-dependency-ledger)
    - [Failure modes](#122-failure-modes)
    - [Final synthesis](#123-final-synthesis)

## 1. Why primes should see finite Galois groups

### 1.1 The distribution problem

Let $L/K$ be a finite Galois extension of number fields and let

$$
G=\operatorname{Gal}(L/K).
$$

At every finite prime $\mathfrak p$ of $K$ unramified in $L$, reduction modulo a prime of
$L$ above $\mathfrak p$ produces a distinguished element of $G$, well defined up to conjugacy.
This is the arithmetic Frobenius class $\operatorname{Frob}_{\mathfrak p}$. It records how the
prime decomposes in $L$: its order is the common residue degree, and its cycle structure in a
permutation action records the residue degrees in the corresponding intermediate field.

The elementary splitting question asks whether a prescribed class ever occurs. Chebotarev's
theorem gives the much more rigid answer

$$
\delta\{\mathfrak p:\operatorname{Frob}_{\mathfrak p}=C\}
=\frac{|C|}{|G|}.
\tag{1.1}
$$

The right side is exactly the proportion of elements of $G$ lying in $C$. Thus primes sample a
finite Galois group as uniformly as conjugacy permits. This is not uniformity in bounded norm,
and it contains no estimate for the discrepancy below a real number $x$. It is an asymptotic
statement in Dirichlet density, obtained from the logarithmic singularity of Euler products at
$s=1$.

The theorem has two lives. In algebraic number theory it manufactures primes with specified
splitting. In representation theory it says that good Frobenius classes are dense enough to
determine every continuous class function on an absolute Galois group. Both uses depend on the
same finite-quotient statement, but their conclusions are different: one produces primes, while
the other recognizes already existing representations.

### 1.2 What this theorem does and does not say

The exact result proved here is the conjugacy-class form of Chebotarev for a finite Galois
extension of number fields, with arithmetic Frobenius and Dirichlet density. It immediately gives
infinitely many primes in every class, primes outside any fixed finite exceptional set, and
density of good Frobenius conjugacy classes in profinite Galois groups.

Several familiar strengthenings are outside the statement.

- We prove no natural-density limit, although that limit is also known.
- We prove no prime-counting asymptotic, error term, zero-free region, or least-prime bound.
- We impose no generalized Riemann hypothesis and derive no conclusion conditional on it.
- We prove no general holomorphy theorem for nontrivial irreducible Artin $L$-functions.
- We do not recover ramification, lattices, extension classes, or local monodromy from good-prime
  characteristic polynomials.

These exclusions are mathematical boundaries, not editorial omissions. The proof needs only the
behavior at $s=1$ of finite-order one-dimensional Hecke $L$-functions. Nonabelianity is handled
by a cyclic fixed-field argument, so no unproved Artin holomorphy assertion enters.

### 1.3 The proof architecture

There are four layers.

First, local algebra defines Frobenius and proves its conjugacy and functoriality properties.
Second, a theta-series and Mellin argument proves that ray-class partial zeta functions have the
same positive residue at $s=1$. Character orthogonality then makes every nontrivial finite-order
Hecke $L$-function holomorphic there. A cyclic zeta factorization proves that its value at $1$
is nonzero. Logarithmic Euler products consequently give the prime-sum dichotomy

$$
\sum_{\mathfrak p}\chi(\mathfrak p)(N\mathfrak p)^{-s}=

\begin{cases}
\log(1/(s-1))+O(1),&\chi=1,\\
O(1),&\chi\ne1.
\end{cases}
\tag{1.2}
$$

Third, finite abelian character orthogonality turns (1.2) into the abelian density theorem.
Finally, for $g\in G$ one passes to the cyclic extension $L/L^{\langle g\rangle}$ and counts
degree-one primes of the intermediate field. The centralizer $C_G(g)$ supplies exactly the
multiplicity needed to convert density $1/|\langle g\rangle|$ upstairs into $|[g]|/|G|$
downstairs.

The route may be pictured as

```text
Poisson summation + unit lattice
                |
                v
 equal residues of ray partial zeta functions
                |
                v
 finite-order Hecke L-functions at s = 1
                |
                v
       abelian Chebotarev
                |
                v
 cyclic fixed field + centralizer count
                |
                v
       full Chebotarev density.
```

### 1.4 Standing conventions and prerequisites

Every prime is a nonzero prime ideal of the ring of integers of a number field. Its absolute norm
is $N\mathfrak p=|\mathcal O_K/\mathfrak p|$. All finite Galois groups are written on the
automorphism side. Arithmetic Frobenius acts on the residue field by
$x\mapsto x^{N\mathfrak p}$; geometric Frobenius is its inverse.

The local extension theory, decomposition and inertia groups, and Frobenius normalization are
the content of Books 2--3. Book 4 supplies Minkowski lattices, the unit lattice, ideles, ray
classes, and finite-order Hecke characters. Books 5--6 supply local and global reciprocity,
including the identification of unramified prime uniformizers with arithmetic Frobenius and the
existence of the cyclic extension cut out by a finite-order character. Book 7 supplies the
general analytic language of Mellin transforms, gamma integrals, lattice Poisson summation, and
Dedekind zeta functions. We recall and specialize those results at every point where their exact
normalization matters.

Finite étale covers and fundamental groups from Book 17 explain why finite quotients of an
absolute Galois group correspond to finite Galois extensions. Books 21 and 23 explain the
geometric-Frobenius convention used in cohomology and trace formulas. Book 24 supplies the
topology of profinite groups and the principle that an open normal subgroup gives a finite
continuous quotient. None of their cohomological results is needed for the analytic proof.

## 2. Frobenius classes in global extensions

### 2.1 Decomposition and inertia

Fix a prime $\mathfrak P$ of $L$ above $\mathfrak p$ of $K$. Its decomposition group is

$$
D_{\mathfrak P}=\{\sigma\in G:\sigma\mathfrak P=\mathfrak P\}.
$$

Reduction gives a surjection

$$
D_{\mathfrak P}\longrightarrow
\operatorname{Gal}(k_{\mathfrak P}/k_{\mathfrak p}),
$$

whose kernel is the inertia group $I_{\mathfrak P}$. Since finite residue fields have cyclic
Galois groups, there is an exact sequence

$$
1\longrightarrow I_{\mathfrak P}
\longrightarrow D_{\mathfrak P}
\longrightarrow
\langle x\mapsto x^{N\mathfrak p}\rangle
\longrightarrow1.
\tag{2.1}
$$

The prime $\mathfrak p$ is unramified in $L$ precisely when $I_{\mathfrak P}=1$. In that case
reduction identifies $D_{\mathfrak P}$ with the residue-field Galois group, and the preferred
residue automorphism has a unique lift to $D_{\mathfrak P}$.

This explains why Frobenius belongs only to unramified prime theory. At a ramified prime the
residue automorphism determines a coset modulo inertia, not a preferred element of $G$. Any
argument that assigns a canonical Galois element to a ramified prime has discarded the kernel in
(2.1).

### 2.2 Arithmetic and geometric Frobenius

For unramified $\mathfrak p$, define $\operatorname{Frob}_{\mathfrak P}\in D_{\mathfrak P}$
by

$$
\operatorname{Frob}_{\mathfrak P}(x)
\equiv x^{N\mathfrak p}\pmod{\mathfrak P}
\qquad(x\in\mathcal O_L).
\tag{2.2}
$$

This is arithmetic Frobenius. Its inverse is geometric Frobenius. The distinction affects labels,
not densities: inversion bijects conjugacy classes and preserves their sizes. It does affect
formulas for characteristic polynomials and Hecke characters, so we never suppress it.

The order of $\operatorname{Frob}_{\mathfrak P}$ equals the residue degree
$f(\mathfrak P/\mathfrak p)$. In a Galois extension this number is independent of
$\mathfrak P\mid\mathfrak p$. The decomposition group is cyclic and generated by Frobenius.

### 2.3 Independence of the prime upstairs

If $\mathfrak P'=\tau\mathfrak P$, then

$$
D_{\mathfrak P'}=\tau D_{\mathfrak P}\tau^{-1}
\quad\text{and}\quad
\operatorname{Frob}_{\mathfrak P'}
=\tau\operatorname{Frob}_{\mathfrak P}\tau^{-1}.
\tag{2.3}
$$

Indeed, conjugation carries the stabilizer of $\mathfrak P$ to that of $\mathfrak P'$, and
the residue action of the conjugate still raises elements of the base residue field to the
$N\mathfrak p$th power. Uniqueness in (2.2) proves the second identity.

Because $G$ acts transitively on the primes above $\mathfrak p$, all Frobenius elements above
$\mathfrak p$ form one conjugacy class. We denote it by
$\operatorname{Frob}_{\mathfrak p}(L/K)$. For a conjugacy class $C\subset G$, set

$$
S_C(L/K)=\{\mathfrak p:\mathfrak p\text{ unramified in }L,
\ \operatorname{Frob}_{\mathfrak p}(L/K)=C\}.
\tag{2.4}
$$

### 2.4 Restriction, quotient, and change of base

Frobenius has two functorialities which are easily confused. Suppose $K\subset E\subset L$.
If $E/K$ is Galois, restriction gives $G\to\operatorname{Gal}(E/K)$ and sends arithmetic
Frobenius at $\mathfrak P$ to arithmetic Frobenius at $\mathfrak P\cap\mathcal O_E$. The base
prime is unchanged, so no power appears.

If instead one changes the base from $K$ to $E$, let $\mathfrak q$ be a prime of $E$ above
$\mathfrak p$, with residue degree $f=f(\mathfrak q/\mathfrak p)$. Then

$$
N\mathfrak q=(N\mathfrak p)^f,
$$

and relative arithmetic Frobenius in $L/E$ is the $f$th power of the $K$-Frobenius, after
choosing compatible primes:

$$
\operatorname{Frob}_{\mathfrak P}(L/E)
=\operatorname{Frob}_{\mathfrak P}(L/K)^f.
\tag{2.5}
$$

Restriction to a quotient and change of base are therefore different operations. The first
keeps Frobenius unchanged and restricts the automorphism; the second changes the residue-field
cardinality and introduces a power.

### 2.5 Primes in intermediate fields

Let $H\le G$ and $E=L^H$. Fix an unramified prime $\mathfrak P$ of $L$ over $\mathfrak p$ and
write $c=\operatorname{Frob}_{\mathfrak P}$. The primes of $E$ above $\mathfrak p$ correspond
to orbits of $\langle c\rangle$ on $G/H$. More precisely, the orbit of $xH$ corresponds to

$$
\mathfrak q_x=x^{-1}\mathfrak P\cap\mathcal O_E,
$$

and its length is $f(\mathfrak q_x/\mathfrak p)$. If that length is $f$, then
$c^fxH=xH$, so $x^{-1}c^fx\in H$, and

$$
\operatorname{Frob}_{x^{-1}\mathfrak P}(L/E)=x^{-1}c^fx.
\tag{2.6}
$$

This is the exact fixed-field interface used later for restriction and induction. The same
arithmetic prime can have different residue degrees in different intermediate fields, and the
upper Frobenius element must be raised to the corresponding degree. Formula (2.6) prevents the
common error of using the same eigenvalue at every prime above $\mathfrak p$.

### 2.6 Ramification is a finite exceptional set

Only finitely many primes of $K$ ramify in $L$. One proof uses the relative discriminant:
ramified primes are precisely among the prime divisors of the nonzero ideal
$\mathfrak d_{L/K}$. Equivalently, localizing the integral closure outside the discriminant
makes it finite étale, and a finite étale algebra is unramified at every remaining prime.

This finiteness has two consequences. Frobenius is defined at all but finitely many primes, and
removing ramified primes never changes a Dirichlet density. Neither assertion permits one to
define Frobenius at a ramified prime; the exceptional set is removed, not repaired.

## 3. Dirichlet density and its calculus

### 3.1 Prime sums and normalization

For a set $S$ of primes of $K$ and real $s>1$, put

$$
P_S(s)=\sum_{\mathfrak p\in S}(N\mathfrak p)^{-s},
\qquad
\Lambda(s)=\log\frac1{s-1}.
\tag{3.1}
$$

We say that $S$ has Dirichlet density $\delta$ if

$$
\lim_{s\to1^+}\frac{P_S(s)}{\Lambda(s)}=\delta.
\tag{3.2}
$$

One may equivalently divide by the prime sum over all primes. Chapter 4 will prove

$$
P_{\mathrm{all}}(s)=\Lambda(s)+O(1),
\tag{3.3}
$$

so the quotient of the two denominators tends to one. Definition (3.2) is preferable in the
proof because the logarithmic singularity appears directly from $L$-functions.

The upper and lower Dirichlet densities are the limsup and liminf of the ratio in (3.2). If both
equal $\delta$, the ratio converges to $\delta$: for every $\epsilon>0$, the definition of
limsup eventually gives an upper bound $\delta+\epsilon$, and the definition of liminf
eventually gives a lower bound $\delta-\epsilon$. This is the ordinary squeeze criterion.

### 3.2 Bounded perturbations

The central elementary observation is that $\Lambda(s)\to+\infty$ as $s\to1^+$. Hence if

$$
P_S(s)=a\Lambda(s)+O(1),
\tag{3.4}
$$

then $S$ has density $a$. More generally, if $P_S(s)-P_T(s)$ stays bounded, then $S$ and $T$
have the same density whenever either density exists.

This makes finite Euler factors and prime powers of exponent at least two analytically invisible
to density. It is also why every $O(1)$ below must be uniform as $s\to1^+$ through real values
$s>1$. A bound depending on $s$ without control would prove nothing.

### 3.3 Finite sets, unions, and monotonicity

A finite set $F$ has density zero, because each term $(N\mathfrak p)^{-s}$ is at most one for
$s>0$, and therefore $P_F(s)\le |F|$. If $S$ and $T$ are disjoint and have densities
$a$ and $b$, then

$$
P_{S\cup T}(s)=P_S(s)+P_T(s)
$$

gives density $a+b$. A finite disjoint union is handled by induction.

If $S\subseteq T$, then $P_S(s)\le P_T(s)$ for $s>1$. Dividing by the positive quantity
$\Lambda(s)$ and taking liminf gives

$$
\underline\delta(S)\le\underline\delta(T)
$$

whenever the displayed lower densities exist as finite values. The analogous limsup inequality
is equally immediate. In particular, a subset of a density-zero set has density zero if its
density exists, and a positive-density set cannot be finite.

### 3.4 Residue degree at least two is negligible

Let $E/K$ be finite. Consider primes $\mathfrak q$ of $E$ whose residue degree over the prime
$\mathfrak p$ below is at least two. Then

$$
N_E\mathfrak q=(N_K\mathfrak p)^{f(\mathfrak q/\mathfrak p)}
\ge (N_K\mathfrak p)^2.
$$

At most $[E:K]$ primes lie above one $\mathfrak p$, so for real $s\ge1$ their total prime sum is
bounded by

$$
[E:K]\sum_{\mathfrak p}(N\mathfrak p)^{-2s}
\le [E:K]\sum_{\mathfrak a\ne0}(N\mathfrak a)^{-2}.
\tag{3.5}
$$

The last ideal sum converges. For instance, the Minkowski lattice estimate counts ideals of norm
at most $X$ by $O(X)$, and summation by dyadic intervals gives convergence at exponent $2$.
Thus higher-residue-degree primes have density zero when measured by their norms in $E$.

This small lemma is the hinge of the nonabelian proof. It lets us compare prime sums in an
intermediate field with prime sums in the base without invoking a prime-ideal theorem.

### 3.5 Why Dirichlet density is the right invariant

Euler products naturally produce weights $(N\mathfrak p)^{-s}$ and their logarithms naturally
separate the first prime power from the bounded higher-power tail. Dirichlet density is designed
to read the coefficient of the one universal divergence at $s=1$. It is stable under the finite
exceptions forced by ramification and conductors, and under the higher-residue-degree deletion
forced by passage through an intermediate field.

Natural density instead asks for a limit of counts with $N\mathfrak p\le x$. Passing from the
analytic statement proved here to that counting statement requires a Tauberian theorem and finer
control. No such passage is needed for prime selection or representation-theoretic density, so
we retain the invariant that the proof establishes directly.

There is also a useful contrast with density by rational primes. A prime $p$ can have several
primes of $K$ above it, with different residue degrees in a nongalois extension. Chebotarev in
the form proved here counts prime ideals of $K$ with their ideal norms. Grouping them by the
rational prime below is a different operation and can change weights. The residue-degree
estimate of Section 3.4 is the safe mechanism for discarding the degree-at-least-two part when a
comparison genuinely requires it.

Bounded perturbation also proves uniqueness of density. If
$P_S(s)=a\Lambda(s)+O(1)$ and $P_S(s)=b\Lambda(s)+O(1)$, subtraction gives
$(a-b)\Lambda(s)=O(1)$. Since $\Lambda(s)\to\infty$, one has $a=b$. Thus no set can acquire two
different densities through two different Euler-product presentations.

## 4. The zeta singularity at one

### 4.1 Ray partial zeta functions

The abelian density theorem will be a finite Fourier inversion once nontrivial characters are
known to contribute no logarithmic singularity at $1$. The hard analytic point is therefore not
an estimate for primes. It is the equality of residues of the partial zeta functions belonging
to ray classes. We prove that equality by making every ray class into an affine lattice and
reading the pole from the zero frequency in Poisson summation.

Fix a modulus

$$
\mathfrak m=\mathfrak m_0\mathfrak m_\infty,
$$

where $\mathfrak m_\infty$ contains every real place. Let $I_{\mathfrak m}$ be the fractional
ideals prime to $\mathfrak m_0$, and let $P_{\mathfrak m,1}$ consist of $(\alpha)$ with

$$
\alpha\equiv1\pmod{\mathfrak m_0},
\qquad \sigma(\alpha)>0
\quad\text{for every real embedding }\sigma.
$$

The narrow ray class group

$$
C_{\mathfrak m}=I_{\mathfrak m}/P_{\mathfrak m,1}
$$

is finite. Indeed, its map to the ordinary ideal class group has finite target, and its kernel
is a quotient of
$(\mathcal O_K/\mathfrak m_0)^\times\times\{\pm1\}^{r_1}$.

For $c\in C_{\mathfrak m}$ define

$$
\zeta_c(s)=
\sum_{\substack{\mathfrak b\subset\mathcal O_K,
(\mathfrak b,\mathfrak m_0)=1\\[1pt]
[\mathfrak b]=c}}
(N\mathfrak b)^{-s},
\qquad \Re(s)>1.
\tag{4.1}
$$

The goal is stronger than showing that each $\zeta_c$ has a pole: all residues must be equal and
positive. Equality makes nontrivial character sums cancel; positivity makes the trivial pole and
the later nonvanishing quotient unambiguous.

### 4.2 Affine ideal lattices

Choose an integral ideal $\mathfrak a$, prime to $\mathfrak m_0$, in the inverse ray class
$c^{-1}$. Every ideal in (4.1) has the form

$$
\mathfrak b=(\alpha)\mathfrak a^{-1},
$$

where $\alpha\in\mathfrak a$, $\alpha\equiv1\pmod{\mathfrak m_0}$, and $\alpha$ is positive at
every real place. Conversely every such $\alpha$ gives an ideal in the desired class. The finite
congruence cuts out an affine lattice

$$
A_{\mathfrak a}=\alpha_0+\mathfrak m_0\mathfrak a
\subset K_\infty.
\tag{4.2}
$$

To see this locally, at a prime dividing $\mathfrak m_0$ the ideal $\mathfrak a$ is a unit and
the condition is the stated congruence. Away from $\mathfrak m_0$, multiplication by
$\mathfrak m_0$ is a unit and both sides impose only membership in $\mathfrak a$. The Chinese
remainder theorem glues these descriptions.

Let

$$
U_{\mathfrak m}=\{u\in\mathcal O_K^\times:
u\equiv1\pmod{\mathfrak m_0},\ u>0\text{ at all real places}\}.
$$

Choose a torsion-free subgroup $U\subset U_{\mathfrak m}$ of finite index $h$. The action on
nonzero elements is free, and a $U_{\mathfrak m}$-orbit consists of $h$ $U$-orbits. Since
$N\mathfrak b=|N_{K/\mathbf Q}\alpha|/N\mathfrak a$, we obtain the exact identity

$$
\zeta_c(s)=\frac{(N\mathfrak a)^s}{h}
\sum_{\substack{\alpha\in A_{\mathfrak a},\ \alpha\ne0\\
\alpha>0\text{ at real places}}}^{/U}
|N_{K/\mathbf Q}\alpha|^{-s}.
\tag{4.3}
$$

No asymptotic estimate has entered: (4.3) is a parametrization of ideals by positive unit
orbits.

### 4.3 Theta kernels and Poisson summation

Write

$$
K_\infty\simeq\mathbf R^{r_1}\times\mathbf C^{r_2},
$$

and put $d_v=1$ at a real place and $d_v=2$ at a complex place. For
$t=(t_v)\in T=(\mathbf R_{>0})^{r_1+r_2}$ define

$$
q(t)=\prod_{v\mid\infty}t_v^{d_v},
\qquad d^\times t=\prod_v\frac{dt_v}{t_v}.
$$

For a parity vector $\epsilon\in\{0,1\}^{r_1}$ use the Schwartz kernel

$$
\Phi_\epsilon(x)=
\prod_{v\text{ real}}x_v^{\epsilon_v}e^{-\pi x_v^2}
\prod_{v\text{ complex}}e^{-2\pi|x_v|^2},
\tag{4.4}
$$

and the theta sum

$$
\Theta_{\mathfrak a,\epsilon}(t)
=\sum_{\alpha\in A_{\mathfrak a}}\Phi_\epsilon(t\alpha).
$$

Write a star when the zero vector is omitted. If $L_0\subset K_\infty$ is a full lattice,
$x_0+L_0$ an affine translate, and $L_0^\vee$ the trace-dual lattice, Poisson summation gives

$$
\sum_{x\in x_0+L_0}\Phi_\epsilon(tx)
=\frac{q(t)^{-1}}{\operatorname{covol}(L_0)}
\sum_{y\in L_0^\vee}
e^{2\pi i\langle y,x_0\rangle}
\widehat\Phi_\epsilon(t^{-1}y).
\tag{4.5}
$$

The factor $q(t)^{-1}$ is the Jacobian of coordinatewise scaling. Fourier transforms of the
Gaussian factors are again polynomials times Gaussians, and

$$
\widehat\Phi_\epsilon(0)=0\quad(\epsilon\ne0),
\qquad \widehat\Phi_0(0)>0.
\tag{4.6}
$$

For the standard Minkowski measure there is a positive constant $c_K$ with

$$
\operatorname{covol}(\mathfrak b)=c_KN\mathfrak b,
\qquad
\operatorname{covol}(\mathfrak m_0\mathfrak a)
=c_KN\mathfrak m_0N\mathfrak a.
\tag{4.7}
$$

The determinant calculation behind (4.7) is the discriminant formula for an integral basis;
passing from $\mathcal O_K$ to an ideal multiplies covolume by its index, hence by its norm.

For completeness, the affine Poisson formula follows from the ordinary lattice version. If
$f_{x_0}(x)=f(x+x_0)$, then its Fourier transform is the transform of $f$ multiplied by the
phase $e^{2\pi i\langle y,x_0\rangle}$, up to the sign fixed by the Fourier convention.
Replacing $f(x)$ by $f(tx)$ multiplies its integral by $q(t)^{-1}$ and replaces the dual
argument by $t^{-1}y$. These two transformations account for every factor in (4.5); no
ideal-class-dependent scalar is hidden in the formula.

The zero-frequency criterion (4.6) is equally concrete. At a real place the transform of
$xe^{-\pi x^2}$ vanishes at zero because the function is odd. Hence any parity vector with a
nonzero coordinate kills the product at zero. For $\epsilon=0$, every local Gaussian integral
is positive. The unique pole at $1$ therefore lies in the all-even component, exactly the
component selected by averaging real signs in (4.12).

### 4.4 Mellin unfolding through the unit lattice

The logarithmic map sends $U$ to a full lattice in

$$
\left\{(y_v):\sum_vd_vy_v=0\right\}.
$$

Consequently $T/U$ is a compact shape space times the radial variable $q>0$, and after fixing a
shape measure

$$
d^\times t=\frac{dq}{q}\,dy.
\tag{4.8}
$$

For $\Re(s)>1$, define

$$
J_{\mathfrak a,\epsilon}(s)
=\int_{T/U}\Theta^*_{\mathfrak a,\epsilon}(t)q(t)^s,d^\times t.
\tag{4.9}
$$

Unfolding a $U$-orbit across a fundamental domain gives

$$
J_{\mathfrak a,\epsilon}(s)
=G_\epsilon(s)
\sum_{\substack{\alpha\in A_{\mathfrak a},\ \alpha\ne0}}^{/U}
\left(\prod_{v\text{ real}}
\operatorname{sgn}(\alpha_v)^{\epsilon_v}\right)
|N_{K/\mathbf Q}\alpha|^{-s},
\tag{4.10}
$$

where direct Gaussian integration gives

$$
G_\epsilon(s)=
\prod_{v\text{ real}}
\frac12\pi^{-(s+\epsilon_v)/2}
\Gamma\!\left(\frac{s+\epsilon_v}{2}\right)
\prod_{v\text{ complex}}
\frac12(2\pi)^{-s}\Gamma(s).
\tag{4.11}
$$

For example, the real factor follows from substituting $u=\pi t^2\alpha^2$ in

$$
\int_0^\infty(t\alpha)^\epsilon e^{-\pi t^2\alpha^2}
t^s\frac{dt}{t}.
$$

Absolute convergence justifies the unfolding. Uniformly on the compact shape space, a lattice
has $O(R^{[K:\mathbf Q]})$ points of norm at most $R$, while the Gaussian is bounded by a
polynomial times $e^{-cq^{2/[K:\mathbf Q]}\|\alpha\|^2}$. Summing over Euclidean shells gives
$O(q^{-1})$ as $q\to0$ and exponential decay after zero is omitted as $q\to\infty$. Multiplying
by $q^{\Re(s)}dq/q$ is integrable for $\Re(s)>1$, so sums and integrals may be interchanged.

Here is the shell estimate with the endpoint visible. For a full lattice
$L_0\subset\mathbf R^n$, disjoint small balls around lattice points show

$$
\#\{x\in x_0+L_0:\|x\|\le R\}=O(1+R^n),
\tag{4.12a}
$$

uniformly when the lattice ranges through a compact set of shapes of fixed covolume. If
$0<q\le1$, split into shells $j\le q^{1/n}\|x\|<j+1$. The number of points in the $j$th shell
is $O(q^{-1}(j+1)^n)$, and the Gaussian supplies $e^{-cj^2}$. Summing gives $O(q^{-1})$.
For $q\ge1$, the starred affine lattice has a positive shortest-vector bound uniformly in the
shape variable, and the same argument gives $O(e^{-cq^{2/n}})$ after changing constants. These
are exactly the bounds used at the two radial ends.

Positivity at all real places has the finite Fourier expansion

$$
1_{\{\alpha_v>0\ \forall v\text{ real}\}}
=2^{-r_1}\sum_{\epsilon\in\{0,1\}^{r_1}}
\prod_{v\text{ real}}\operatorname{sgn}(\alpha_v)^{\epsilon_v}.
\tag{4.12}
$$

Combining (4.3), (4.10), and (4.12) yields

$$
\zeta_c(s)=
\frac{2^{-r_1}(N\mathfrak a)^s}{h}
\sum_\epsilon\frac{J_{\mathfrak a,\epsilon}(s)}{G_\epsilon(s)}.
\tag{4.13}
$$

### 4.5 Continuation and the equal-residue theorem

We now isolate the singular term. On the compact shape space, as $q\to\infty$ the starred theta
sum decreases exponentially. As $q\to0$, apply (4.5) with
$L_0=\mathfrak m_0\mathfrak a$. The nonzero dual frequencies again decrease exponentially,
while the zero frequency gives

$$
\Theta^*_{\mathfrak a,\epsilon}(t)
=\frac{\widehat\Phi_\epsilon(0)}
{\operatorname{covol}(\mathfrak m_0\mathfrak a)}q^{-1}
-1_{\{0\in A_{\mathfrak a}\}}\Phi_\epsilon(0)
+O(e^{-cq^{-2/[K:\mathbf Q]}}),
\tag{4.14}
$$

where a harmless polynomial factor can be absorbed into the exponential estimate.

Split the radial integral at $q=1$ and subtract the two explicit terms on $(0,1)$. The
remainders have entire Mellin transforms. Therefore $J_{\mathfrak a,\epsilon}$ is meromorphic,
with possible simple poles only at $0$ and $1$. By (4.6), only $\epsilon=0$ contributes at
$1$. If $V_U$ is the positive volume of the shape domain, then

$$
\operatorname*{res}_{s=1}J_{\mathfrak a,0}(s)
=\frac{V_U\widehat\Phi_0(0)}
{\operatorname{covol}(\mathfrak m_0\mathfrak a)}.
\tag{4.15}
$$

Since $G_0(1)>0$, equations (4.7), (4.13), and (4.15) imply

$$
\operatorname*{res}_{s=1}\zeta_c(s)
=\frac{2^{-r_1}V_U\widehat\Phi_0(0)}
{hG_0(1)c_KN\mathfrak m_0}>0.
\tag{4.16}
$$

Crucially, this expression is independent of $c$. The factor $N\mathfrak a$ in (4.13) cancels
the factor $N\mathfrak a$ in the covolume. We have proved the required analytic theorem:

**Theorem 4.1 (equal ray residues).** Every narrow ray partial zeta function $\zeta_c(s)$
extends meromorphically to a neighborhood of $s=1$, has there one simple pole, and all classes
$c\in C_{\mathfrak m}$ have the same positive residue.

The argument proves more continuation than will be used, but only the local statement at $1$
enters density.

It is worth checking why the chosen ideal $\mathfrak a$ disappears. In the orbit sum, passage
from $\alpha$ to $(\alpha)\mathfrak a^{-1}$ contributes $(N\mathfrak a)^s$. At the pole one
sets $s=1$, while the zero-frequency term divides by
$\operatorname{covol}(\mathfrak m_0\mathfrak a)$, which is proportional to
$N\mathfrak a$. The cancellation is exact. Without it, residues could depend on the ray class
and character orthogonality would not remove the pole.

### 4.5a A power-saving ray-class count

The Taylor--Wiles application formerly carried a separate geometry-of-numbers proof of the
following refinement. It belongs with the analytic density package and is recorded here so that
the application volume need not reproduce it.

**Corollary 4.2 (analytic ray-class estimate).** Let $B$ be a number field and $\mathfrak m$ a
modulus. For each $c\in\operatorname{Cl}_{\mathfrak m}(B)$ there are constants
$a_{\mathfrak m}>0$ and $\eta>0$, independent of $c$, such that

$$
A_c(X)=\#\{\mathfrak a\subseteq\mathcal O_B:(\mathfrak a,\mathfrak m)=1,
[\mathfrak a]=c,\ \mathrm N\mathfrak a\le X\}
=a_{\mathfrak m}X+O_{B,\mathfrak m}(X^{1-\eta}).
\tag{4.17a}
$$

Consequently the ideal series of every nontrivial character of the narrow ray class group is
holomorphic in a neighborhood of $s=1$.

**Proof.** Choose an integral ideal $\mathfrak b_c$, prime to $\mathfrak m$, in the inverse
ordinary ideal class. Writing $\mathfrak a\mathfrak b_c=(\alpha)$ turns the ray condition into
one fixed finite congruence and one fixed sign condition on $\alpha$. A bounded fundamental
parallelepiped for the logarithms of the ray units selects one generator from each ray-unit
orbit. In Minkowski space the norm bound cuts out finitely many Lipschitz regions dilated by
$X^{1/[B:\mathbf Q]}$. Their volume is a constant times
$(\mathrm N\mathfrak b_c)X$, while the covolume of the ideal lattice contains the same factor
$\mathrm N\mathfrak b_c$. Thus the leading constant is independent of $c$.

The elementary Lipschitz lattice-point estimate proved in Book 6, Section 4.2 (by covering the
boundary with $O(t^{[B:\mathbf Q]-1})$ fundamental parallelotopes), applies unchanged to each
of the finitely many congruence translates and sign sectors. Followed by a dyadic decomposition
along the finitely many faces of the logarithmic fundamental domain, it gives an error
$O(X^{1-1/[B:\mathbf Q]}(\log X)^r)$, hence $O(X^{1-\eta})$ after decreasing $\eta$. Only
finitely many ideal classes, congruence translates, and sign sectors occur, so the constants are
uniform in $c$. Summing the displayed asymptotic with the values of a nontrivial ray-class
character cancels the common main term. Partial summation then continues its ideal series
holomorphically across $s=1$. $\square$

### 4.6 Dedekind zeta and the full prime sum

Summing (4.1) over ray classes gives the Dedekind zeta function with the finitely many primes
dividing $\mathfrak m_0$ removed. Taking trivial modulus shows

$$
\zeta_K(s)=\frac{R_K}{s-1}+H(s),
\qquad R_K>0,
\tag{4.17}
$$

with $H$ holomorphic near $1$. For real $s>1$, the Euler product is positive and

$$
\log\zeta_K(s)
=\sum_{\mathfrak p}\sum_{r\ge1}
\frac1{r(N\mathfrak p)^{rs}}.
\tag{4.18}
$$

The tail $r\ge2$ is uniformly bounded for $s\ge1$:

$$
\sum_{\mathfrak p}\sum_{r\ge2}
\frac1{r(N\mathfrak p)^{rs}}
\le 2\sum_{\mathfrak p}(N\mathfrak p)^{-2}<\infty.
\tag{4.19}
$$

The elementary inequality follows by summing the geometric series, using
$N\mathfrak p\ge2$. The final convergence follows from (3.5). On the other hand, (4.17) gives

$$
\log\zeta_K(s)=\log\frac1{s-1}+O(1).
$$

Subtracting the bounded tail from (4.18) proves (3.3). This completes the density normalization
and also proves that the set of all primes has Dirichlet density one.

Equivalently, there is a constant $C$ such that, for $s>1$ sufficiently close to $1$,

$$
\Lambda(s)-C\le P_{\mathrm{all}}(s)\le\Lambda(s)+C.
\tag{4.20}
$$

Dividing by $\Lambda(s)>0$ squeezes the ratio to one. This gives the denominator comparison in
the limsup and liminf definitions as well as in the ordinary limit definition.

## 5. Finite-order Hecke characters at one

### 5.1 From ray classes to characters

Let $\chi$ be a finite-order Hecke character of $K$. Its conductor is finite, so after enlarging
a modulus it factors through $C_{\mathfrak m}$. With conductor primes omitted, its ideal
$L$-series is

$$
L_{\mathfrak m}(s,\chi)
=\sum_{c\in C_{\mathfrak m}}\chi(c)\zeta_c(s)
=\prod_{\mathfrak p\nmid\mathfrak m_0}
(1-\chi(\mathfrak p)(N\mathfrak p)^{-s})^{-1}.
\tag{5.1}
$$

The equality of series and product holds absolutely for $\Re(s)>1$. The convention from global
reciprocity is that $\chi(\mathfrak p)$ equals the value of the associated Galois character on
arithmetic Frobenius.

### 5.2 Holomorphy by cancellation of residues

If $\chi\ne1$, finite character orthogonality gives

$$
\sum_{c\in C_{\mathfrak m}}\chi(c)=0.
\tag{5.2}
$$

The equal residues in Theorem 4.1 therefore cancel in (5.1). Thus
$L_{\mathfrak m}(s,\chi)$ is holomorphic at $s=1$. If $\chi=1$, the residues add, producing a
simple pole with positive residue.

Holomorphy alone is insufficient for taking a bounded logarithm: the value at $1$ could still
vanish. Nonvanishing is the delicate second half of the argument. We prove it without using
prime distribution.

### 5.3 Nonvanishing by cyclic factorization

Suppose $\chi$ has order $m>1$. Global reciprocity attaches to it a cyclic extension $F/K$ of
degree $m$ and a faithful character of $\operatorname{Gal}(F/K)$ with the prescribed unramified
Frobenius values. Let $S$ contain the conductor primes and all primes ramified in $F$. Removing
the primes above $S$ from the zeta function of $F$, one has

$$
\zeta_{F,S_F}(s)=\prod_{j=0}^{m-1}L_S(s,\chi^j).
\tag{5.3}
$$

This identity is verified prime by prime and is independent of Chebotarev. If an unramified
prime $\mathfrak p$ has Frobenius of order $d$, it splits into $m/d$ primes of residue degree
$d$, so its factor on the left is

$$
(1-(N\mathfrak p)^{-ds})^{-m/d}.
$$

Because $\chi$ is faithful, the numbers
$\chi(\operatorname{Frob}_{\mathfrak p})^j$ run through all $d$th roots of unity, each $m/d$
times. Hence the product on the right has the same factor, by

$$
\prod_{\zeta^d=1}(1-\zeta X)=1-X^d.
$$

Every nontrivial factor in (5.3) is holomorphic at $1$. Both $\zeta_{F,S_F}$ and the trivial
factor $L_S(s,1)=\zeta_{K,S}(s)$ have simple poles with positive residues. Dividing and taking
$s\to1$ gives

$$
\prod_{j=1}^{m-1}L_S(1,\chi^j)
=\frac{\operatorname*{res}_{s=1}\zeta_{F,S_F}(s)}
{\operatorname*{res}_{s=1}\zeta_{K,S}(s)}>0.
\tag{5.4}
$$

No factor on the left can vanish. In particular $L_S(1,\chi)\ne0$. Adding or deleting finitely
many Euler factors multiplies this value by nonzero numbers, so the same conclusion holds for
the conductor-omitted series in (5.1).

The use of faithfulness causes no loss. A character of exact order $m$ has image $\mu_m$, and
the fixed field of its kernel has Galois group isomorphic to that image. If one begins with a
nonfaithful character of a larger abelian group, one first passes to this quotient. Formula
(5.3) uses the degree $m$ of the character field, not the order of the ambient group.

Nor is (5.4) circular. Its proof uses splitting types only to compare two Euler factors for a
fixed prime. The order of an already defined Frobenius determines the factorization of that
prime by local Galois theory. No assertion about how often such a Frobenius occurs is used.

### 5.4 Logarithmic Euler products

For $\Re(s)>1$, absolute convergence permits the logarithm

$$
\log L_S(s,\chi)
=\sum_{\mathfrak p\notin S}\sum_{r\ge1}
\frac{\chi(\mathfrak p)^r}{r(N\mathfrak p)^{rs}}.
\tag{5.5}
$$

For real $s>1$ this is the branch obtained continuously from large real $s$, where the Euler
product is close to $1$. The $r\ge2$ tail is bounded in absolute value by (4.19). If
$\chi\ne1$, holomorphy and nonvanishing at $1$ give a zero-free neighborhood and hence a bounded
analytic logarithm there. Therefore the $r=1$ part of (5.5) is bounded.

More explicitly, choose a disk about $1$ on which $L_S(s,\chi)$ has no zero. A holomorphic
logarithm exists on a smaller simply connected disk. Along real $s>1$ it differs from the
Euler-product logarithm by a constant multiple of $2\pi i$; agreement at one point fixes that
constant. Hence the logarithm stays bounded as $s\to1^+$. This is the precise place where
nonvanishing, not merely holomorphy, is required.

For $\chi=1$, the simple positive pole gives

$$
\log L_S(s,1)=\log\frac1{s-1}+O(1),
$$

and subtracting the same bounded higher-power tail leaves the universal logarithm.

### 5.5 The prime-sum character lemma

We record the analytic engine in its reusable form.

**Theorem 5.1 (finite-order character prime sum).** Let $\chi$ be a finite-order Hecke
character of a number field $K$, and omit any finite set containing its conductor primes. As
$s\to1^+$ through real values,

$$
\sum_{\mathfrak p}\chi(\mathfrak p)(N\mathfrak p)^{-s}=

\begin{cases}
\log(1/(s-1))+O(1),&\chi=1,\\
O(1),&\chi\ne1.
\end{cases}
\tag{5.6}
$$

**Proof.** Sections 5.2 and 5.3 show that a nontrivial character has an $L$-function holomorphic
and nonzero at $1$, while a trivial character has a simple pole with positive residue. Section
5.4 compares the logarithm with the $r=1$ prime sum and bounds the remaining prime powers.
Finite omitted sets contribute $O(1)$. $\square$

This theorem uses only one-dimensional finite-order characters. No claim about a general Artin
$L$-function has been smuggled into the logarithm.

## 6. Artin characters and the exact reduction needed

### 6.1 Artin Euler factors

It is useful to place the proof beside the conventional Artin $L$-function language, both to
explain why character theory appears and to mark the exact point beyond which we do not go.
Let $\rho:G\to\operatorname{GL}(V)$ be a finite-dimensional complex representation of the
finite Galois group $G=\operatorname{Gal}(L/K)$. At a prime $\mathfrak p$, choose
$\mathfrak P\mid\mathfrak p$. The local factor is

$$
L_{\mathfrak p}(s,\rho)
=\det\!\left(1-(N\mathfrak p)^{-s}\rho(\phi_{\mathfrak P})
\mid V^{I_{\mathfrak P}}\right)^{-1},
\tag{6.1}
$$

where $\phi_{\mathfrak P}$ is any lift of arithmetic residue Frobenius to
$D_{\mathfrak P}$. Its action on $V^{I_{\mathfrak P}}$ is independent of the lift, because
inertia acts trivially there. Conjugating $\mathfrak P$ conjugates the operator, so its
determinant is independent of the chosen prime upstairs.

The Artin $L$-function is the product of (6.1). It converges absolutely for $\Re(s)>1$ because
the eigenvalues of every finite-order matrix have absolute value one. At an unramified prime,
its logarithm begins with

$$
\operatorname{tr}\rho(\operatorname{Frob}_{\mathfrak p})
(N\mathfrak p)^{-s}.
$$

Thus a theorem saying that every nontrivial irreducible Artin $L$-function is holomorphic and
nonzero at $1$ would prove Chebotarev by nonabelian character orthogonality. Such a theorem is
substantially stronger than what density needs and is not assumed here; our proof establishes
nonvanishing only for the one-dimensional Hecke factors it actually uses.

The distinction can be seen from a virtual identity. An Artin character may be written as an
integral combination of induced one-dimensional characters, so its $L$-function becomes a
quotient of Hecke $L$-functions. Every factor in that quotient is controlled at $1$, but zeros
and poles may cancel between numerator and denominator. The quotient proves meromorphy and
determines an order only after the virtual coefficients are analyzed. It does not show that the
original Artin $L$-function has no pole at other points. Treating the quotient as a product with
nonnegative exponents would silently assume the effectivity one is trying to prove.

### 6.2 Permutation characters and zeta quotients

For a subgroup $H\le G$, let $E=L^H$. The permutation representation
$\mathbf C[G/H]$ has Artin $L$-function

$$
L(s,\mathbf C[G/H])=\zeta_E(s).
\tag{6.2}
$$

To verify this, work prime by prime. At an unramified prime $\mathfrak p$, Frobenius permutes
$G/H$; an orbit of length $f$ contributes $1-X^f$ to
$\det(1-X\operatorname{Frob})$. The orbits are the primes $\mathfrak q$ of $E$ over
$\mathfrak p$, and their lengths are $f(\mathfrak q/\mathfrak p)$, so
$X^f=(N\mathfrak q)^{-s}$ when $X=(N\mathfrak p)^{-s}$. At ramified primes the same statement
on inertia invariants identifies the local factors. This proves (6.2).

Consequently, any virtual character

$$
\Theta=\sum_i n_i\operatorname{Ind}_{H_i}^G\mathbf1
$$

has

$$
L(s,\Theta)=\prod_i\zeta_{L^{H_i}}(s)^{n_i}.
\tag{6.3}
$$

The order at $s=1$ is $-\sum_i n_i$, because every Dedekind zeta factor has one simple pole.
Formula (6.3) is safe even when some $n_i$ are negative: it is an identity of meromorphic
functions, not an assertion that the virtual representation is effective.

### 6.3 Induction and Euler products

More generally, if $H\le G$ and $\theta$ is a one-dimensional character of $H$, global
reciprocity over $E=L^H$ identifies $\theta$ with a finite-order Hecke character of $E$, and

$$
L_K(s,\operatorname{Ind}_H^G\theta)=L_E(s,\theta).
\tag{6.4}
$$

At a good prime, the proof again decomposes the Frobenius permutation on $G/H$ into cycles. If
the orbit of $xH$ has length $f$, the return map is $x^{-1}c^fx\in H$ and its contribution to
the characteristic polynomial is

$$
1-\theta(x^{-1}c^fx)(N\mathfrak p)^{-fs}.
$$

This is exactly the Euler factor at the corresponding prime of $E$, by (2.6). Ramified factors
agree after taking inertia invariants. Thus induction compatibility is a local calculation, not
a density consequence.

To make the ramified statement explicit, inertia acts on the coset summands of the induced
space. Its invariant vectors are obtained by summing over inertia orbits on which the stabilizer
acts trivially through $\theta$. Residue Frobenius permutes those invariant orbit sums. Following
one Frobenius cycle returns to the initial summand with scalar equal to the value of $\theta$ on
the corresponding upper decomposition-group element. These are exactly the invariant spaces and
return scalars defining the local Hecke factor over $E$. Thus (6.4) includes, rather than
discards, ramified Euler factors. For density one may omit them because there are finitely many,
but the induction identity itself is stronger and exact.

### 6.4 Brauer induction as an alternative route

The Brauer induction theorem, which is not invoked in this book, expresses every complex
character of $G$ as an integral combination of characters induced from one-dimensional
characters of elementary subgroups. If that independent finite-group theorem is combined with
(6.4), the associated Artin $L$-function is expressed as a quotient of finite-order Hecke
$L$-functions.
At $s=1$, Theorem 5.1 controls every factor: the only poles come from trivial characters and
every nontrivial factor is nonzero.

This provides an alternative character-theoretic route to the logarithmic comparison needed for
Chebotarev. It must be used with care. A quotient expression may contain cancellations between
poles and zeros, and it gives meromorphy, not general holomorphy of the Artin factor. For the
present theorem the cyclic fixed-field proof in Chapter 8 is shorter and avoids bookkeeping of
Brauer coefficients. We record Brauer induction because later representation-theoretic
applications use precisely the induction identity (6.4), not because the density theorem needs
the full strength of the induction theorem.

We do not use Brauer induction as an input to Theorem 9.1. The only statement from this section
used later is the elementary local induction identity (6.4), whose proof was given above. Thus
the density proof remains closed even if one treats the general finite-group induction theorem
as a separate representation-theoretic result. The role of this comparison is diagnostic: it
shows precisely which Hecke $L$-functions would occur in the traditional Artin-character proof
and why their behavior at $1$ is enough, without promoting that comparison to an unproved
holomorphy claim.

### 6.5 The holomorphy boundary

The analytic input established in this book is exactly:

1. Dedekind zeta functions have a simple positive pole at $1$.
2. Nontrivial finite-order one-dimensional Hecke $L$-functions are holomorphic and nonzero at
   $1$.
3. Induction preserves Euler products as in (6.4).

We do not assert that a nontrivial irreducible Artin $L$-function is entire, holomorphic on the
whole line $\Re(s)=1$, or zero-free in a quantitative region. The cyclic reduction below needs
none of those statements. This boundary is also why no error term or least-prime estimate will
emerge from the proof.

There is one harmless Artin statement that does follow immediately from what has been proved.
For a permutation character, (6.2) makes its $L$-function a Dedekind zeta function and therefore
gives a simple pole at $1$. For a difference of permutation characters, (6.3) computes the
order at $1$ as the corresponding difference of dimensions of invariant lines. This limited
pole comparison is enough to check normalizations and contains no assertion about arbitrary
irreducible characters.

## 7. The abelian density theorem

### 7.1 Orthogonality on a finite abelian group

Let $A$ be a finite abelian group and $\widehat A$ its group of complex characters. For
$a,b\in A$,

$$
\frac1{|A|}\sum_{\chi\in\widehat A}\overline{\chi(a)}\chi(b)=

\begin{cases}1,&b=a,\\0,&b\ne a.\end{cases}
\tag{7.1}
$$

Indeed, if $b\ne a$, choose a character $\psi$ nontrivial on $ba^{-1}$. Multiplication
$\chi\mapsto\chi\psi$ permutes $\widehat A$ but multiplies the sum by
$\psi(ba^{-1})\ne1$, forcing it to vanish. If $b=a$, every summand is one. Thus

$$
1_{\{a\}}(b)=\frac1{|A|}\sum_{\chi\in\widehat A}
\overline{\chi(a)}\chi(b).
\tag{7.2}
$$

This identity explains the shape of the density. The trivial character supplies exactly
$1/|A|$ of the universal logarithmic divergence, and every nontrivial Fourier mode is bounded.

### 7.2 Reciprocity identifies the prime values

Let $L/K$ be finite abelian with group $A$. Finite global reciprocity identifies every
$\chi\in\widehat A$ with a finite-order Hecke character of $K$. At a prime unramified in both
the extension and the character conductor,

$$
\chi(\mathfrak p)=\chi(\operatorname{Frob}_{\mathfrak p}).
\tag{7.3}
$$

This equation uses arithmetic normalization on both sides. With geometric reciprocity both
sides would be inverted. The finitely many omitted primes contribute only a bounded function to
all prime sums.

### 7.3 Density of one Frobenius element

The analytic character lemma and reciprocity now meet. A point mass on the finite Galois group
is decomposed into its character modes; density reads only the trivial mode because every other
mode stays bounded at $1$. This is the abelian theorem in one sentence, but the proof below
keeps the finite exceptional set and the normalization visible.

**Theorem 7.1 (abelian Chebotarev).** If $L/K$ is finite abelian with group $A$, then for every
$a\in A$ the set of unramified primes with $\operatorname{Frob}_{\mathfrak p}=a$ has Dirichlet
density $1/|A|$.

**Proof strategy.** Insert Frobenius into (7.2), sum over primes, and apply Theorem 5.1 term by
term. The character group is finite, so no interchange issue remains.

**Proof.** Let $S_a$ denote the desired set. Equations (7.2)--(7.3) give

$$
P_{S_a}(s)=\frac1{|A|}\sum_{\chi\in\widehat A}
\overline{\chi(a)}
\sum_{\mathfrak p}\chi(\mathfrak p)(N\mathfrak p)^{-s}+O(1).
$$

By Theorem 5.1 the trivial character contributes
$|A|^{-1}\log(1/(s-1))$, while every other term is bounded. Division by the logarithm and
passage to the limit gives $1/|A|$. $\square$

Positive density implies infinitude and permits removal of any prescribed finite set.

### 7.4 Splitting completely and elementary examples

The identity element corresponds to complete splitting. Therefore the completely split primes
in a finite abelian extension have density $1/[L:K]$. For a quadratic extension, the two classes
each have density $1/2$: inert and split primes are equally distributed in Dirichlet density,
after the finitely many ramified primes are removed.

For $K=\mathbf Q$ and $L=\mathbf Q(\zeta_m)$, arithmetic Frobenius at $p\nmid m$ is the
automorphism $\zeta_m\mapsto\zeta_m^p$. Thus Theorem 7.1 says that every invertible residue
class modulo $m$ contains primes of density $1/\varphi(m)$. This is the cyclotomic instance of
the theorem; its proof here is not used as an input for the general case.

## 8. From cyclic subgroups to conjugacy classes

### 8.1 The cyclic fixed field

Let $L/K$ now be finite Galois with arbitrary group $G$. Fix $g\in G$, write

$$
H=\langle g\rangle,
\qquad E=L^H,
\qquad C=[g].
$$

The extension $L/E$ is cyclic with group $H$. By Theorem 7.1, primes $\mathfrak q$ of $E$
whose relative Frobenius equals $g$ have density $1/|H|$. The problem is to compare those primes
with base primes $\mathfrak p$ whose $G$-Frobenius class is $C$.

Only degree-one primes $\mathfrak q/\mathfrak p$ correspond directly: when
$f(\mathfrak q/\mathfrak p)=1$, the norm weights agree and the relative Frobenius is conjugate
to the base Frobenius. Chapter 3 showed that all higher-degree primes make only a bounded
contribution, so no logarithmic mass is lost by deleting them.

### 8.2 Removing higher residue degrees

Let $T_g$ be the primes $\mathfrak q$ of $E$ unramified in $L$ with
$\operatorname{Frob}_{\mathfrak q}(L/E)=g$. Split $T_g=T_g^{(1)}\sqcup T_g^{(\ge2)}$ according
to residue degree over $K$. Equation (3.5) gives

$$
P_{T_g^{(\ge2)}}(s)=O(1).
\tag{8.1}
$$

Consequently

$$
P_{T_g^{(1)}}(s)=\frac1{|H|}\log\frac1{s-1}+O(1).
\tag{8.2}
$$

The same estimate absorbs the finite ramified set. It remains to count how many primes in
$T_g^{(1)}$ lie over one $\mathfrak p\in S_C(L/K)$.

### 8.3 The centralizer multiplicity

Fix $\mathfrak p\in S_C(L/K)$. Choose $\mathfrak P\mid\mathfrak p$ with Frobenius exactly
$g$; this is possible because the elements above $\mathfrak p$ form $C$. Its decomposition
group is $H$. Primes of $E$ above $\mathfrak p$ correspond to $H$-orbits on $G/H$. A
degree-one prime is a fixed coset $xH$. At the corresponding prime $x^{-1}\mathfrak P$ of $L$,
the relative Frobenius is $x^{-1}gx$. It equals the chosen element $g$ precisely when

$$
x^{-1}gx=g,
$$

or equivalently $x\in C_G(g)$. Right multiplication by $H$ does not change the coset and
preserves the equation because $H$ centralizes $g$. Hence the number of desired primes over
$\mathfrak p$ is

$$
\frac{|C_G(g)|}{|H|}.
\tag{8.3}
$$

This division by $|H|$ is essential. Counting elements $x$ instead of cosets would overcount
every prime by the order of the cyclic subgroup.

### 8.4 The comparison identity

At residue degree one, $N_E\mathfrak q=N_K\mathfrak p$. Combining the converse correspondence
and multiplicity (8.3), while absorbing ramified and higher-degree primes into a bounded term,
gives

$$
\sum_{\substack{\mathfrak q\text{ prime of }E\\
\operatorname{Frob}_{\mathfrak q}(L/E)=g}}
(N_E\mathfrak q)^{-s}
=\frac{|C_G(g)|}{|H|}P_{S_C(L/K)}(s)+O(1).
\tag{8.4}
$$

Every part of (8.4) is exact at degree one. The $O(1)$ records only the two already controlled
exceptions; it does not hide an unproved density comparison.

An $S_3$ example makes the multiplicity visible. Let $g$ be a transposition. Then
$H=\langle g\rangle$ has order $2$, $C_G(g)=H$, and the transposition class has size $3$.
Exactly $|C_G(g)|/|H|=1$ degree-one prime of $E$ lies over each base prime with transposition
Frobenius, so cyclic density $1/2$ becomes $3/6$.

If $g$ is a $3$-cycle, then $H=A_3=C_G(g)$ has order $3$, while its class has size $2$.
Again the multiplicity is one, and density $1/3$ becomes $2/6$. For $g=1$, one has $H=1$ and
$C_G(g)=G$; each completely split base prime has $|G|$ degree-one primes in $L$, so density one
for primes of $L$ becomes density $1/|G|$ downstairs. These cases test every factor in (8.4).

## 9. Chebotarev density

### 9.1 The theorem

All difficult inputs have now been isolated: cyclic density is known, higher residue degrees are
negligible, and the exact number of relevant degree-one primes is the centralizer quotient.
Combining them produces the full theorem without any new analytic assertion.

**Theorem 9.1 (Chebotarev density theorem).** Let $L/K$ be a finite Galois extension of number
fields, let $G=\operatorname{Gal}(L/K)$, and let $C\subset G$ be a conjugacy class. Then

$$
\boxed{\delta(S_C(L/K))=\frac{|C|}{|G|}.}
\tag{9.1}
$$

**Proof strategy.** Choose $g\in C$, apply abelian Chebotarev to the cyclic extension
$L/L^{\langle g\rangle}$, and compare the resulting prime sum with the base-field class sum by
(8.4). The orbit-stabilizer identity turns the centralizer into the size of $C$.

**Proof.** Put $H=\langle g\rangle$ and $E=L^H$. The left side of (8.4) equals

$$
\frac1{|H|}\log\frac1{s-1}+O(1)
$$

by Theorem 7.1 and (8.1). Therefore (8.4) yields

$$
P_{S_C(L/K)}(s)
=\frac1{|C_G(g)|}\log\frac1{s-1}+O(1).
$$

Since $|C|=[G:C_G(g)]$, one has
$1/|C_G(g)|=|C|/|G|$. Dividing by the logarithm proves (9.1). $\square$

### 9.2 Class functions and averaged prime sums

Every complex class function $f$ on $G$ is constant on conjugacy classes. Summing Theorem 9.1
over the finitely many classes gives

$$
\sum_{\mathfrak p\text{ unramified}}
f(\operatorname{Frob}_{\mathfrak p})(N\mathfrak p)^{-s}
=\left(\frac1{|G|}\sum_{g\in G}f(g)\right)
\log\frac1{s-1}+O(1).
\tag{9.2}
$$

Thus the Dirichlet-weighted Frobenius average is the uniform group average. Taking $f$ to be a
character gives a conceptual bridge to Chapter 6: a nontrivial irreducible character has group
average zero, while the trivial character has average one. Taking $f$ to be the indicator of a
union of conjugacy classes shows that its density is its cardinality divided by $|G|$.

If $\rho$ is a complex representation on $V$, then the average of its character is
$\dim V^G$. Indeed,

$$
e_G=\frac1{|G|}\sum_{g\in G}\rho(g)
$$

is the projector onto $V^G$, and its trace is the average character. Formula (9.2) therefore
specializes to

$$
\sum_{\mathfrak p}
\operatorname{tr}\rho(\operatorname{Frob}_{\mathfrak p})
(N\mathfrak p)^{-s}
=\dim(V^G)\log\frac1{s-1}+O(1).
\tag{9.3}
$$

This is the exact trace-level Artin comparison at $1$ furnished by Chebotarev. It is a prime-sum
statement, not analytic continuation of $L(s,\rho)$.

### 9.3 Ramified primes and changes of convention

If finitely many unramified primes are removed or added, the density is unchanged. All ramified
primes may therefore be placed in the exceptional set. There is no requirement to choose a
Frobenius lift at them.

Replacing arithmetic by geometric Frobenius sends $C$ to

$$
C^{-1}=\{g^{-1}:g\in C\}.
$$

Inversion is a bijection $C\to C^{-1}$, so the density remains $|C|/|G|$. A downstream formula
must nevertheless invert eigenvalues or character values consistently.

### 9.4 No effective assertion is hidden here

The conclusion is a limit as $s\to1^+$. It does not bound the least norm of a prime in $S_C$,
does not estimate

$$
\#\{\mathfrak p\in S_C:N\mathfrak p\le x\},
$$

and does not provide an error term relative to a logarithmic integral. Such results require
quantitative zero-free information for zeta and Artin $L$-functions, with possible exceptional
zeros and discriminant dependence. None of that information was proved or used. In particular,
no conclusion in this book is conditional on a Riemann hypothesis.

## 10. Finite-quotient existence and selection

### 10.1 Avoiding a finite set

Most arithmetic applications need existence rather than a numerical density. The essential
advantage of positive density over bare nonemptiness is that finitely many already controlled or
ramified primes may be excluded without exhausting the class.

**Corollary 10.1 (Frobenius selection).** Let $L/K$ be finite Galois, let $C$ be a conjugacy
class in $\operatorname{Gal}(L/K)$, and let $T$ be a finite set of primes of $K$. There are
infinitely many primes $\mathfrak p\notin T$, unramified in $L$, with
$\operatorname{Frob}_{\mathfrak p}=C$.

**Proof.** Theorem 9.1 gives the class set positive density $|C|/|G|$. A finite set has density
zero, so the difference remains infinite. $\square$

The same assertion holds for geometric Frobenius after replacing $C$ by $C^{-1}$. This is the
form needed whenever a cohomological representation is normalized geometrically.

### 10.2 Simultaneous splitting and prescribed Frobenius

Auxiliary primes are often required to be invisible to one extension while detecting a class in
another. Linear disjointness turns these two requests into independent coordinates of one
product Galois group, where a single Chebotarev application handles them simultaneously.

**Corollary 10.2.** Let $A/K$ and $B/K$ be finite Galois extensions with $A\cap B=K$. Given a
conjugacy class $C\subset\operatorname{Gal}(A/K)$ and a finite exceptional set, there are
infinitely many primes outside that set which split completely in $B$ and have Frobenius class
$C$ in $A$. Their density is

$$
\frac{|C|}{[A:K][B:K]}.
$$

**Proof.** Linear disjointness gives

$$
\operatorname{Gal}(AB/K)
\simeq\operatorname{Gal}(A/K)\times\operatorname{Gal}(B/K).
$$

Apply Theorem 9.1 to $C\times\{1\}$. Its relative size in the product is the displayed number.
$\square$

If $A\cap B\ne K$, the pair of requested classes must have the same image in
$\operatorname{Gal}(A\cap B/K)$. When that compatibility holds, one applies Chebotarev to the
corresponding conjugacy classes in the fiber-product Galois group. Linear disjointness is a
convenient sufficient hypothesis, not a dispensable decoration.

### 10.3 Witnesses for generators and conjugacy classes

Let $G$ be finite and choose classes $C_1,\ldots,C_r$ such that no proper subgroup of $G$
meets every $C_i$. For a Galois extension with group $G$, Corollary 10.1 permits one to choose
distinct primes $\mathfrak p_i$ outside any prescribed finite set with Frobenius in $C_i$.
Any subgroup containing representatives of all these Frobenius classes must equal $G$.

This is a finite witness principle. It is often used to certify that a specialization has full
monodromy or that a finite image has not shrunk after restriction. The group-theoretic condition
on the classes must be checked separately; Chebotarev produces representatives but does not
prove that a selected list generates.

A simpler version realizes any finite list of classes, with repetitions allowed, at pairwise
distinct primes. Choose them successively and add previously chosen primes to the exceptional
set. Positive density ensures the induction never stops.

One may impose finitely many quotient conditions simultaneously. Given finite Galois extensions
$L_i/K$, pass to their compositum $M$. A tuple of desired classes is realizable only if it is
the image of a conjugacy class in $\operatorname{Gal}(M/K)$. Once such a class is chosen,
Corollary 10.1 supplies infinitely many primes realizing every condition. This compatibility
test is essential when the $L_i$ have nontrivial intersections.

### 10.4 Intermediate fields and compatible Frobenius powers

Fix $L/K$ Galois with group $G$, an element $c\in G$, and finitely many subgroups $H\le G$.
Choose $\mathfrak p$ with Frobenius class $[c]$ and a prime $\mathfrak P$ above it with
Frobenius exactly $c$. For each $H$, the following data are simultaneous:

1. primes of $L^H$ over $\mathfrak p$ are $\langle c\rangle$-orbits on $G/H$;
2. the orbit length $f$ is the residue degree;
3. the orbit of $xH$ has upper Frobenius $x^{-1}c^fx\in H$;
4. a one-dimensional character $\theta$ of $H$ has local value
   $\theta(x^{-1}c^fx)$ at that prime.

If $H_1\le H_2$, the map $G/H_1\to G/H_2$ sends an orbit of length $f_1$ to one of length
$f_2$ with $f_2\mid f_1$, and

$$
\left(x^{-1}c^{f_2}x\right)^{f_1/f_2}=x^{-1}c^{f_1}x.
\tag{10.1}
$$

This is the tower law for arithmetic Frobenius. It is the precise transport interface for
Brauer-induced families on several fixed fields. Chebotarev selects the base prime; equations
(2.6) and (10.1), rather than density, determine every upper-field value.

### 10.5 Density in an absolute Galois group

Let $K$ be a number field, let $S$ be a finite set of places, and write $G_{K,S}$ for the Galois
group of the maximal extension unramified outside $S$. For $v\notin S$, choose a geometric or
arithmetic Frobenius conjugacy class $\Phi_v$ in $G_{K,S}$. Then the union of these conjugacy
classes, after deleting any further finite set of $v$, is dense in $G_{K,S}$.

To prove this, take a nonempty open subset $U\subset G_{K,S}$ and $g\in U$. Choose an open
normal subgroup $N$ with $gN\subset U$. The quotient $G_{K,S}/N$ cuts out a finite Galois
extension $M/K$. Corollary 10.1 supplies a good prime whose Frobenius in the quotient lies in
the conjugacy class of $gN$. Conjugating a representative in $G_{K,S}$ places it inside $gN$
and hence in $U$. Thus every nonempty open set meets a good Frobenius conjugacy class.

Notice that a conjugate, not necessarily the originally chosen representative $\Phi_v$, lies in
$U$. This is why the clean statement concerns the union of conjugacy classes and why the
functions transported below must be class functions.

The same proof applies to the full absolute Galois group $G_K$: every open normal subgroup cuts
out a finite Galois extension, and one enlarges the finite forbidden set to include its ramified
primes. Removing an arbitrary density-zero set is not equally automatic. Positive density of a
class and density zero of an excluded set do imply that their difference retains the same
density, but one must know the excluded set has density and use additivity; mere verbal
smallness of an infinite exceptional set is insufficient.

## 11. Representation-theoretic transport

### 11.1 Continuous class functions are determined by good Frobenius

Finite-quotient density becomes useful for representations only after topology is brought back
in. A continuous class function cannot distinguish an element from limits of conjugate
Frobenius elements. The closed-set formulation below packages equality, integrality, and
congruence transport in one statement.

**Theorem 11.1 (closed-condition transport).** Let $A$ be a Hausdorff topological space, let
$f:G_{K,S}\to A$ be a continuous class function, and let $Z\subseteq A$ be closed. If
$f(\Phi_v)\in Z$ for every $v$ outside a finite set, then $f(g)\in Z$ for every
$g\in G_{K,S}$.

**Proof.** Suppose $f(g)\notin Z$. Since $Z$ is closed, $A\setminus Z$ is an open
neighborhood of $f(g)$, and continuity gives an open neighborhood $U$ of $g$ mapped into
$A\setminus Z$. By Section 10.5, a conjugate $h\Phi_vh^{-1}$ of some good Frobenius lies in
$U$. Class invariance gives

$$
f(h\Phi_vh^{-1})=f(\Phi_v)\in Z,
$$

contradicting $f(U)\subset A\setminus Z$. $\square$

Taking $Z$ to be the diagonal in $A\times A$ shows that two continuous class functions agreeing
at almost every good Frobenius agree everywhere. Taking $A$ to be a topological ring and $Z$ a
closed subring, ideal, lattice, or congruence locus transports membership. Closedness is
essential: a limit of elements in a nonclosed subset need not remain in it.

### 11.2 Brauer--Nesbitt in characteristic zero

Let $F$ be a characteristic-zero field and let $V,W$ be finite-dimensional semisimple
representations of a group $\Gamma$. If

$$
\operatorname{tr}_V(\gamma)=\operatorname{tr}_W(\gamma)
\qquad(\gamma\in\Gamma),
\tag{11.1}
$$

then $V\simeq W$ after passing, if necessary, to a common splitting field.

Here is the algebra argument. Let $B$ be the finite-dimensional image of $F[\Gamma]$ in
$\operatorname{End}(V\oplus W)$. Equality (11.1) makes the two trace functionals equal on all
of $B$ by linearity. Semisimple modules factor through $B/\operatorname{rad}(B)$. After scalar
extension to an algebraic closure, this quotient is a product of full matrix algebras. The
characters of its simple modules are linearly independent: evaluating on the central idempotent
of each matrix factor isolates its multiplicity. Thus $V$ and $W$ have the same simple
multiplicities.

More explicitly, write

$$
B/\operatorname{rad}(B)\simeq\prod_{i=1}^rM_{d_i}(\overline F).
$$

The $i$th simple module is the column module $\overline F^{d_i}$. The central idempotent $e_i$
acts as the identity on that module and as zero on every other simple. If $m_i(V)$ is its
multiplicity in $V$, then

$$
\operatorname{tr}_V(e_i)=m_i(V)d_i.
$$

Equality of trace functionals gives $m_i(V)d_i=m_i(W)d_i$, and characteristic zero allows
cancellation of the positive integer $d_i$. Hence all multiplicities agree. This proof also
shows why one first semisimplifies: the radical acts trivially on simple constituents but can
encode extension data invisible to trace.

For arbitrary finite-dimensional representations, the conclusion is

$$
V^{\mathrm{ss}}\simeq W^{\mathrm{ss}}.
\tag{11.2}
$$

Traces cannot distinguish nonsplit extensions, so the semisimplification qualifier cannot be
removed without a separate semisimplicity or irreducibility hypothesis.

### 11.3 Characteristic polynomials and semisimplification

The preceding two ingredients compose cleanly: Chebotarev extends trace equality from good
primes to the whole Galois group, and Brauer--Nesbitt turns global character equality into an
isomorphism after semisimplification. This is the uniqueness interface used by compatible
systems and overlap comparisons.

**Corollary 11.2 (Chebotarev--Brauer--Nesbitt).** Let $E$ be a characteristic-zero
nonarchimedean local field and

$$
\rho_1,\rho_2:G_K\longrightarrow\operatorname{GL}_n(E)
$$

continuous representations unramified outside finite sets. If their Frobenius characteristic
polynomials agree at all but finitely many finite places, then

$$
\rho_1^{\mathrm{ss}}\simeq\rho_2^{\mathrm{ss}}
$$

after a common finite scalar extension. Equality of traces alone is sufficient.

**Proof.** Traces are continuous class functions. Theorem 11.1 extends their equality from good
Frobenius to every element of $G_K$. Section 11.2 identifies semisimplifications. $\square$

The coefficient fields must first be embedded in one common characteristic-zero local field.
Representations with different residue characteristics are compared separately after their
algebraic Frobenius polynomials have been identified; one does not directly compare a
$p$-adic matrix with a $q$-adic matrix.

**Corollary 11.3 (dense rank-two trace criterion).** Let $E$ be as above, let
$\rho:G_K\to\operatorname{GL}_2(E)$ be continuous, and let
$\chi:G_K\to E^\times$ be a continuous character. Suppose a union of good Frobenius conjugacy
classes is dense in $G_K$ and

$$
\operatorname{tr}\rho(\Phi_v)=1+\chi(\Phi_v)
$$

on that union. Then

$$
\rho^{\mathrm{ss}}\simeq\mathbf1\oplus\chi.
\tag{11.3a}
$$

**Proof.** The two sides define continuous trace functions which agree on a dense set, hence
everywhere. Brauer--Nesbitt gives (11.3a). No determinant hypothesis is needed once the full
trace identity is known. $\square$

If $\rho$ is semisimple and absolutely irreducible, the conclusion is a contradiction. If it is
not semisimple, the conclusion permits either nonsplit extension between the two characters; it
must not be rewritten as an isomorphism before semisimplification.

### 11.4 Order-valued traces and closed conditions

Let $Q$ be a finite-dimensional nonarchimedean algebra over a local field and let
$\mathbb T\subset Q$ be a finite lattice or finite algebra over the valuation ring. It is
complete and therefore closed in $Q$. If a continuous representation into
$\operatorname{GL}_n(Q)$ has

$$
\operatorname{tr}\rho(\Phi_v)\in\mathbb T
$$

at every good prime, Theorem 11.1 gives

$$
\operatorname{tr}\rho(g)\in\mathbb T
\qquad(g\in G_{K,S}).
\tag{11.3}
$$

The same applies to determinants and to any coefficient of the characteristic polynomial,
because each is a continuous class function. Congruence relations are closed: if
$\lambda:Q\to Q'$ is continuous, then the condition $\lambda(x)=0$ is the inverse image of the
closed point $0$. Hence good-prime Hecke congruences extend to every group element.

This transports scalar identities, not matrices. An order-valued trace and determinant form a
pseudorepresentation; constructing an actual representation over $\mathbb T$ requires a
separate realization argument, often residual absolute irreducibility plus a trace-pairing or
Azumaya-algebra theorem.

### 11.5 Finite residual quotients

Suppose two residual representations have finite image. Their product factors through one
finite quotient $\Gamma$ of $G_{K,S}$. Corollary 10.1 realizes every conjugacy class of
$\Gamma$ by a good Frobenius prime outside any fixed finite set. Thus equality of residual
characteristic polynomials at all good primes gives equality on every element of $\Gamma$.
Over an algebraic closure of the finite coefficient field, the modular Brauer--Nesbitt theorem
then identifies semisimplifications. One way to see the required input is to restrict to
$p$-regular elements, where semisimple matrices have prime-to-$p$ order and their eigenvalue
multiplicities define Brauer characters; those characters of simple modules are linearly
independent. Equality of full characteristic polynomials is more than enough to give equality
of these Brauer characters. Equality of ordinary traces alone can lose information in
characteristic $p$ and is not asserted as sufficient without an additional dimension or
small-characteristic hypothesis.

In particular, an operator identity known at all good Frobenius elements descends to every
element of the finite quotient cut out by a radical layer and any auxiliary finite character.
Density does not itself produce a stable flag. Once simple constituents have been recognized,
constructing and closing an actual flag is a separate module-theoretic step.

There is an even more direct finite-quotient use which needs no modular character theorem. If a
polynomial identity in the image operators holds at every good Frobenius and is invariant under
conjugation, realization of every conjugacy class shows it holds for every element of
$\Gamma$. For example, if $(X-1)(X-\bar\chi(\gamma))$ annihilates each Frobenius operator,
then it annihilates each element of the quotient. Turning those elementwise annihilation
relations into a filtration still requires the algebra of the image module.

### 11.6 Restriction, induction, and Frobenius powers

Let $M/K$ be finite and let $\rho$ be a representation of $G_K$. At a prime $w$ of $M$ over a
good prime $v$ of $K$, with residue degree $f$, restriction satisfies

$$
\rho|_{G_M}(\operatorname{Frob}_w)
=\rho(\operatorname{Frob}_v^f)
\tag{11.4}
$$

after compatible choices. Therefore the polynomial at $w$ is obtained by raising each
Frobenius eigenvalue at $v$ to the $f$th power, not by copying the polynomial at $v$.

For induction of a one-dimensional character from $G_M$, the cycles of Frobenius on the
embeddings of $M$ determine the characteristic polynomial. An orbit of length $f$ contributes
the return value of the character at the element corresponding to $\operatorname{Frob}_v^f$.
This is the representation-theoretic version of (2.6) and the local calculation proving (6.4).

Consequently, if two already existing representations over an intermediate field have equal
almost-everywhere Frobenius polynomials, Corollary 11.2 identifies their semisimplifications.
This is the overlap interface used in induced and Brauer-organized families. Chebotarev supplies
recognition after the local polynomials have been correctly transported; it does not supply the
local induction formula.

### 11.7 Limits of transport

The following nonconclusions are as important as the theorem.

- Equal good Frobenius polynomials determine semisimplification, not extension classes.
- They do not choose or compare stable lattices, and reductions of different lattices can have
  different nonsplit structures.
- They do not prove local--global compatibility at a bad prime, determine inertia, monodromy, a
  conductor, or a filtered local object.
- They do not turn a virtual character with negative multiplicities into an actual
  representation. Effectivity needs an independent positivity or multiplicity argument.
- A dense trace identity such as $\operatorname{tr}\rho=1+\chi$ proves
  $\rho^{\mathrm{ss}}\simeq\mathbf1\oplus\chi$; it does not make a nonsplit extension split.
- An infinite set of primes need not be Frobenius-dense. The finite-quotient conclusion, not
  mere infinitude, is what makes continuity applicable.

These boundaries prevent density from being used as an existence theorem. Both representations,
both coefficient embeddings, and every local polynomial being compared must already exist.

## 12. The reusable theorem package

### 12.1 Dependency ledger

The proof has a deliberately short dependency chain.

- Books 2--3 provide decomposition groups, inertia, the local Frobenius exact sequence,
  discriminants, and finiteness of ramification.
- Book 4 provides Minkowski covolumes, Dirichlet's unit lattice, ray class groups, finite-order
  Hecke characters, and the adelic normalization.
- Books 5--6 provide arithmetic local and global reciprocity, cyclic character fields, and
  the match between an unramified prime value and arithmetic Frobenius.
- Book 7 provides the Gaussian Mellin integral and lattice Poisson summation in the analytic
  setting used in Chapter 4.
- Book 17 supplies the finite-cover interpretation of finite Galois quotients; Books 21 and 23
  fix the geometric convention in cohomological applications; Book 24 supplies the profinite
  topology used in Sections 10.5 and 11.1.

All other essential ingredients have been proved here: density calculus, the bounded
higher-prime-power tail, equal ray residues, holomorphy and nonvanishing at $1$, character
orthogonality, abelian density, the higher-residue-degree bound, the centralizer count, the full
conjugacy-class theorem, finite-quotient density, and characteristic-zero trace recognition.

No later volume is a proof dependency. Later uses may cite Theorem 9.1, Corollaries 10.1--10.2,
the fixed-field package of Section 10.4, Theorem 11.1, or Corollary 11.2 without reopening the
analytic argument.

### 12.2 Failure modes

A hostile check of a Chebotarev argument should ask the following questions.

1. Is the extension finite and Galois when a conjugacy class in one group is named?
2. Has the ramified finite set been removed rather than assigned arbitrary Frobenius lifts?
3. Is arithmetic or geometric Frobenius fixed consistently in reciprocity and characteristic
   polynomials?
4. When the base field changes, has Frobenius been raised to the residue degree?
5. Is the density denominator known to have the universal logarithmic growth?
6. Are all $r\ge2$ Euler-product terms uniformly bounded near $1$?
7. For a nontrivial finite-order character, have both holomorphy and nonvanishing at $1$ been
   proved before taking a bounded logarithm?
8. Does the nonabelian reduction count cosets and divide the centralizer by
   $|\langle g\rangle|$?
9. Are higher-degree primes bounded by exponent-two convergence rather than simply discarded?
10. Is a representation-theoretic conclusion limited to semisimplification unless more input is
    present?
11. Is the target condition closed before continuity is used?
12. Has any claimed effective conclusion been removed unless quantitative zero-free estimates
    were separately supplied?

Each item corresponds to a real logical failure. Together they also explain why the proof is
longer than the final formula (9.1): the theorem's apparent simplicity rests on several exact
normalizations and two nontrivial analytic comparisons at $s=1$.

### 12.3 Final synthesis

For a finite Galois extension $L/K$, every unramified prime produces a conjugacy class through
residue-field Frobenius. Theta series on affine ideal lattices reveal one common positive pole
for all ray classes. Fourier cancellation removes that pole for nontrivial finite-order
characters; cyclic zeta factorization proves their values at one do not vanish; logarithmic
Euler products isolate the first prime powers. This yields uniform distribution in abelian
quotients. Passing through the cyclic subgroup generated by one element and counting
degree-one primes with a centralizer calculation yields

$$
\delta(S_C(L/K))=\frac{|C|}{|\operatorname{Gal}(L/K)|}.
$$

The theorem then becomes a versatile finite-quotient principle. It selects primes with prescribed
Frobenius while avoiding finitely many conditions, combines splitting with prescribed classes in
linearly disjoint extensions, tracks residue-degree powers through every fixed field, and makes
good Frobenius conjugacy classes dense in absolute Galois groups. Continuous trace identities
therefore extend to all Galois elements, and characteristic-zero Brauer--Nesbitt theory recognizes
semisimplified representations.

The scope remains exact. Density recognizes existing global objects and supplies finite-quotient
witnesses. It does not construct representations, choose lattices, recover nonsplit extensions,
prove bad-place compatibility, or provide effective prime bounds. Within those boundaries,
Chebotarev is the precise bridge between the finite symmetry of a Galois extension and the
arithmetic distribution of its primes.
