# Eisenstein Series, Congruences, and the Eisenstein Ideal

## Contents

1. [The prime-level problem](#1-the-prime-level-problem)
   - [Why an Eisenstein ideal appears](#11-why-an-eisenstein-ideal-appears)
   - [Prime-level conventions](#12-prime-level-conventions)
   - [The exact integer](#13-the-exact-integer)
   - [The logical route](#14-the-logical-route)
2. [The weight-two Eisenstein series](#2-the-weight-two-eisenstein-series)
   - [The defect of the level-one series](#21-the-defect-of-the-level-one-series)
   - [Cancellation at prime level](#22-cancellation-at-prime-level)
   - [Fourier coefficients](#23-fourier-coefficients)
   - [The two cusps and the Fricke involution](#24-the-two-cusps-and-the-fricke-involution)
   - [The eta quotient as a normalization check](#25-the-eta-quotient-as-a-normalization-check)
3. [Hecke eigenvalues of the Eisenstein series](#3-hecke-eigenvalues-of-the-eisenstein-series)
   - [Good-prime operators](#31-good-prime-operators)
   - [The operator at the level prime](#32-the-operator-at-the-level-prime)
   - [All coefficients from the eigenvalues](#33-all-coefficients-from-the-eigenvalues)
   - [Why normalization matters](#34-why-normalization-matters)
   - [The Dirichlet series and the missing Euler factor](#35-the-dirichlet-series-and-the-missing-euler-factor)
4. [Integral weight-two forms at prime level](#4-integral-weight-two-forms-at-prime-level)
   - [The cusp-form lattice](#41-the-cusp-form-lattice)
   - [Constant terms as residues](#42-constant-terms-as-residues)
   - [What the denominator 24 does and does not prove](#43-what-the-denominator-24-does-and-does-not-prove)
   - [Reduction modulo an integer](#44-reduction-modulo-an-integer)
5. [The acting Hecke algebra and its Fourier dual](#5-the-acting-hecke-algebra-and-its-fourier-dual)
   - [Definition of the algebra](#51-definition-of-the-algebra)
   - [The first-coefficient pairing](#52-the-first-coefficient-pairing)
   - [Perfectness](#53-perfectness)
   - [The formal Eisenstein quotient](#54-the-formal-eisenstein-quotient)
   - [The quotient's universal property](#55-the-quotients-universal-property)
6. [The integral Eisenstein congruence calculation](#6-the-integral-eisenstein-congruence-calculation)
   - [The statement to be proved](#61-the-statement-to-be-proved)
   - [The two-cusp integral lattice](#62-the-two-cusp-integral-lattice)
   - [The calculation at primes at least five](#63-the-calculation-at-primes-at-least-five)
   - [The prime three](#64-the-prime-three)
   - [The two-primary calculation](#65-the-two-primary-calculation)
   - [Global synthesis](#66-global-synthesis)
7. [The q-expansion congruence theorem](#7-the-q-expansion-congruence-theorem)
   - [Existence, uniqueness, and exact modulus](#71-existence-uniqueness-and-exact-modulus)
   - [Faithful extension of the coefficient ring](#72-faithful-extension-of-the-coefficient-ring)
   - [Prime-power and composite moduli](#73-prime-power-and-composite-moduli)
   - [The exceptional small levels](#74-the-exceptional-small-levels)
   - [Coefficient congruence versus operator congruence](#75-coefficient-congruence-versus-operator-congruence)
8. [The Eisenstein ideal](#8-the-eisenstein-ideal)
   - [Definition and equivalent generating sets](#81-definition-and-equivalent-generating-sets)
   - [Eisenstein maximal ideals](#82-eisenstein-maximal-ideals)
   - [Congruent eigenforms](#83-congruent-eigenforms)
   - [No lifting claim is hidden](#84-no-lifting-claim-is-hidden)
9. [The exact index theorem](#9-the-exact-index-theorem)
   - [Dualizing the quotient](#91-dualizing-the-quotient)
   - [Identification with the Eisenstein line](#92-identification-with-the-eisenstein-line)
   - [Calculation of the quotient](#93-calculation-of-the-quotient)
   - [Index, order, and ring structure](#94-index-order-and-ring-structure)
10. [Local structure and depth of congruence](#10-local-structure-and-depth-of-congruence)
    - [Localization at an Eisenstein prime](#101-localization-at-an-eisenstein-prime)
    - [The local index](#102-the-local-index)
    - [Characteristic-zero branches](#103-characteristic-zero-branches)
    - [The two-primary boundary](#104-the-two-primary-boundary)
    - [What the local length does not measure](#105-what-the-local-length-does-not-measure)
11. [Examples and diagnostic calculations](#11-examples-and-diagnostic-calculations)
    - [Levels with trivial Eisenstein quotient](#111-levels-with-trivial-eisenstein-quotient)
    - [Levels 11 and 17](#112-levels-11-and-17)
    - [Levels 19, 37, and 73](#113-levels-19-37-and-73)
    - [A Sturm-style finite check](#114-a-sturm-style-finite-check)
12. [The prime-level Eisenstein package](#12-the-prime-level-eisenstein-package)
    - [Dependency-closed theorem](#121-dependency-closed-theorem)
    - [Hypotheses and boundaries](#122-hypotheses-and-boundaries)
    - [Conclusion](#123-conclusion)

## 1. The prime-level problem

### 1.1 Why an Eisenstein ideal appears

The Fourier coefficients of a cusp form usually encode genuinely cuspidal arithmetic. Eisenstein series behave differently: their coefficients are built from divisor sums and therefore look reducible. At prime level these two worlds can nevertheless become indistinguishable after reduction modulo an integer. The algebraic record of that collision is the Eisenstein ideal.

There are three questions, and their order matters.

First, which weight-two Eisenstein series has the correct prime-level symmetry? Weight two is exceptional because the familiar level-one series is not modular. A particular difference of it and its prime-level rescaling cancels the defect.

Second, for which moduli can the nonconstant expansion of that Eisenstein series be the expansion of a cusp form? Looking only at its constant term gives an incomplete answer at the prime $2$. The exact calculation must see the integral modular curve, including the elliptic stabilizers responsible for the denominator $12$.

Third, how does this congruence determine an ideal and its index inside the acting Hecke algebra? The bridge is a perfect pairing: an operator is paired with a cusp form by taking the first coefficient after applying the operator. Once that pairing is proved perfect, the exact q-expansion congruence becomes an exact algebra-index theorem.

This route is deliberately confined to modular forms and their Hecke algebra. No assertion about cuspidal divisor groups, Jacobians, finite group schemes, or rational torsion is used. Those geometric consequences require additional arguments. Here the goal is the precise analytic and integral algebraic input on which they rest.

### 1.2 Prime-level conventions

Let $p$ be a prime. The main argument assumes $p\geq 5$; the levels $2$ and $3$ are treated separately in Section 7.4. Write

$$
\Gamma_0(p)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{SL}_2(\mathbf Z):p\mid c
\right\}.
$$

Let $X_0(p)$ be the compactified modular curve. We define the integral q-expansion lattice by

$$
S_2(\Gamma_0(p);\mathbf Z)
=S_2(\Gamma_0(p);\mathbf Q)\cap\mathbf Z[[q]]
\subset \mathbf Q[[q]].
$$

Thus its elements have the form

$$
f(q)\frac{dq}{q},
\qquad
f(q)=\sum_{m\geq1}a_m(f)q^m,
\qquad a_m(f)\in\mathbf Z.
$$

Over $\mathbf Z[1/p]$, Book 113 identifies this lattice locally with regular dualizing differentials, proves the all-cusp q-expansion criterion, and proves the good-prime Hecke coefficient formulas. Book 113 explicitly does not treat the bad-level fiber at $p$. The comparison needed there is proved in Section 6.3 below; it is not being smuggled in through the notation $S_2(\Gamma_0(p);\mathbf Z)$.

For a prime $\ell\neq p$, $T_\ell$ denotes the usual normalized weight-two Hecke operator. At $p$ define the rational operator $U_p$ by

$$
a_m(U_pf)=a_{pm}(f).
$$

The displayed coefficient formula shows directly that $U_p$ preserves the q-expansion lattice; no integral correspondence at the level prime is being assumed. All Hecke algebras below are acting image algebras. Thus two formal operators that act identically on the cusp-form lattice are already identified. This convention, developed abstractly in Book 85, prevents irrelevant maximal ideals of a formal polynomial algebra from entering the argument.

### 1.3 The exact integer

Put

$$
\boxed{
n_p=\operatorname{num}\left(\frac{p-1}{12}\right)
=\frac{p-1}{\gcd(p-1,12)}.}
\tag{1.1}
$$

Here $\operatorname{num}(a/b)$ means the positive numerator after the fraction is reduced. The equality on the right follows by dividing $p-1$ and $12$ by their greatest common divisor.

The integer $n_p$ is not usually $p-1$, and it is not always the numerator of $(p-1)/24$. For example,

$$
n_{11}=5,\qquad n_{17}=4,\qquad n_{37}=3,\qquad n_{73}=6.
$$

At $p=17$ the Eisenstein constant term is $(p-1)/24=2/3$, whose numerator is $2$, while the exact congruence modulus is $4$. This example is the quickest warning against a constant-term-only proof.

The elementary valuation form of (1.1) will be useful. For every prime $r$,

$$
v_r(n_p)=\max\{0,v_r(p-1)-v_r(12)\}.
\tag{1.2}
$$

Thus odd primes $r\geq5$ occur to their full exponent in $p-1$, the prime $3$ loses one exponent, and the prime $2$ loses two. The loss of exactly the factor $12$ reflects the elliptic automorphisms in the integral modular problem.

### 1.4 The logical route

The proof can be summarized without concealing its difficult point:

$$
\begin{array}{c}
\text{prime-level Eisenstein series }E_p\\
\Downarrow\ \text{Hecke calculation}\\
T_\ell(E_p)=(1+\ell)E_p,\quad U_p(E_p)=E_p\\
\Downarrow\ \text{two-cusp integral lattice calculation}\\
\text{cuspidal q-expansion modulo }m\iff m\mid n_p\\
\Downarrow\ \text{perfect Hecke--Fourier pairing}\\
\mathbb T/I\simeq\mathbf Z/n_p\mathbf Z.
\end{array}
$$

The middle implication is the substance. The first is an explicit coefficient computation; the last is finite-module duality. Separating the three makes clear where every hypothesis is used.

## 2. The weight-two Eisenstein series

### 2.1 The defect of the level-one series

Define the holomorphic q-series

$$
G_2(z)=-\frac1{24}+\sum_{m\geq1}\sigma_1(m)q^m,
\qquad q=e^{2\pi iz},
\tag{2.1}
$$

where $\sigma_1(m)=\sum_{d\mid m}d$. This normalization is convenient because its positive coefficients are integral and its first coefficient is $1$.

The series is not a modular form of weight two for $\operatorname{SL}_2(\mathbf Z)$. Its transformation law contains an additive term. One efficient derivation uses the discriminant

$$
\Delta(q)=q\prod_{m\geq1}(1-q^m)^{24}.
$$

Logarithmic differentiation gives

$$
q\frac{d}{dq}\log\Delta
=1-24\sum_{m\geq1}\sigma_1(m)q^m
=-24G_2.
\tag{2.2}
$$

Since $\Delta(\gamma z)=(cz+d)^{12}\Delta(z)$, differentiating the logarithm produces the weight-two transformation of $G_2$ plus a term proportional to $c(cz+d)$. That term is the defect. There is no contradiction with holomorphy: weight two at level one simply has no nonzero holomorphic modular form with this constant term.

The defect is universal and linear in $c$. Consequently, a suitable difference of two rescalings can cancel it on a subgroup where one lower-left entry is divisible by the scaling factor.

### 2.2 Cancellation at prime level

Define

$$
\boxed{E_p(z)=G_2(z)-pG_2(pz).}
\tag{2.3}
$$

**Proposition 2.1.** For every prime $p$, $E_p$ is a holomorphic modular form of weight two on $\Gamma_0(p)$ over $\mathbf Q$.

**Proof strategy.** The logarithmic derivative in (2.2) turns the difference into the differential of a weight-zero modular function. This cancels the anomalous transformation without leaving a pole in the upper half-plane. The cusp expansions then establish holomorphy at the boundary.

**Proof.** Put

$$
u_p(z)=\frac{\Delta(z)}{\Delta(pz)}.
$$

For $\gamma=\left(\begin{smallmatrix}a&b\\pc&d\end{smallmatrix}\right)\in\Gamma_0(p)$, the two transformations of $\Delta$ show that $u_p(\gamma z)$ differs from $u_p(z)$ by a nonzero constant. Therefore $d\log u_p$ is $\Gamma_0(p)$-invariant as a differential. By (2.2),

$$
\frac{1}{2\pi i}\frac{d}{dz}\log u_p(z)
=-24\bigl(G_2(z)-pG_2(pz)\bigr)
=-24E_p(z).
\tag{2.4}
$$

Invariance of $E_p(z)\,dz$ is precisely weight-two modularity of $E_p$. The product for $\Delta$ shows that $u_p$ has neither zeros nor poles in the upper half-plane, so its logarithmic derivative is holomorphic there. At a cusp, $u_p$ is a monomial in a local parameter times a unit; its logarithmic derivative has at most a logarithmic pole, which corresponds to a finite constant term for the weight-two form. Thus $E_p$ is holomorphic at both cusps. $\square$

The proof explains why weight two is natural here. A modular unit has a logarithmic differential of weight two. Its zeros and poles become residues rather than poles of the coefficient function.

### 2.3 Fourier coefficients

Expanding (2.3) gives

$$
E_p(q)=\frac{p-1}{24}+\sum_{m\geq1}b_p(m)q^m,
\tag{2.5}
$$

where

$$
b_p(m)=\sigma_1(m)-p\,\mathbf1_{p\mid m}\sigma_1(m/p).
\tag{2.6}
$$

If $m=p^rs$ with $(s,p)=1$, then

$$
\sigma_1(p^rs)-p\sigma_1(p^{r-1}s)
=\sigma_1(s),
$$

so

$$
\boxed{b_p(m)=\sum_{\substack{d\mid m\\p\nmid d}}d
=\sigma_1\bigl(m/p^{v_p(m)}\bigr).}
\tag{2.7}
$$

In particular,

$$
b_p(1)=1,\qquad b_p(p^r)=1,
\qquad b_p(\ell^r)=1+\ell+\cdots+\ell^r\quad(\ell\neq p).
\tag{2.8}
$$

The function $b_p$ is multiplicative. This follows either from (2.7) and multiplicativity of $\sigma_1$, or directly by separating divisors prime to $p$. These coefficients are the unique multiplicative system with local generating factors

$$
\sum_{r\geq0}b_p(\ell^r)X^r
=\frac1{(1-X)(1-\ell X)}\quad(\ell\neq p),
\qquad
\sum_{r\geq0}b_p(p^r)X^r=\frac1{1-X}.
\tag{2.9}
$$

### 2.4 The two cusps and the Fricke involution

The curve $X_0(p)$ has two rational cusps, represented by $\infty$ and $0$. The Fricke involution is represented by

$$
W_p=\begin{pmatrix}0&-1\\p&0\end{pmatrix}.
$$

For weight two we use

$$
(f|W_p)(z)=p(pz)^{-2}f\left(-\frac1{pz}\right).
\tag{2.10}
$$

**Proposition 2.2.** One has $E_p|W_p=-E_p$. Consequently, in the Fricke-compatible local frame, the constant terms at $\infty$ and $0$ are respectively

$$
c_\infty(E_p)=\frac{p-1}{24},
\qquad
c_0(E_p)=-\frac{p-1}{24}.
\tag{2.11}
$$

**Proof.** Apply the transformation law obtained by differentiating $\Delta(-1/z)=z^{12}\Delta(z)$ to the two terms in (2.3). The anomalous terms are equal and cancel; the remaining terms give

$$
p(pz)^{-2}\left(
G_2\left(-\frac1{pz}\right)
-pG_2\left(-\frac1z\right)
\right)
=-G_2(z)+pG_2(pz).
$$

This is $-E_p(z)$. Since $W_p$ exchanges the cusps, its q-expansion at $\infty$ is the expansion of $E_p$ at $0$ in the transported frame. The constants therefore have opposite signs. $\square$

The sum of the two residues is zero, as it must be for a logarithmic differential on a proper curve. This is a consistency check, not yet the congruence theorem.

### 2.5 The eta quotient as a normalization check

The discriminant proof of modularity has a useful refinement. Recall

$$
\Delta=\eta^{24},
\qquad
\eta(z)=q^{1/24}\prod_{m\geq1}(1-q^m).
$$

Put

$$
k_p=\frac{24}{\gcd(p-1,12)}.
\tag{2.12}
$$

This is the least positive even integer $k$ for which $24\mid k(p-1)$. The eta transformation formula shows that

$$
v_p(z)=\left(\frac{\eta(pz)}{\eta(z)}\right)^{k_p}
\tag{2.13}
$$

is a weight-zero rational modular function on $X_0(p)$. Both conditions are necessary: $24\mid k(p-1)$ removes the eta multiplier on the unipotent generators, while evenness makes $p^k$ a rational square and removes the quadratic character. Since eta has no zeros in the upper half-plane, $v_p$ is a modular unit.

At $\infty$ its order is

$$
\operatorname{ord}_\infty(v_p)
=\frac{k_p(p-1)}{24}=n_p.
\tag{2.14}
$$

Fricke exchanges its zero and pole, so

$$
\operatorname{div}(v_p)=n_p([\infty]-[0]).
\tag{2.15}
$$

Logarithmic differentiation gives

$$
q\frac d{dq}\log v_p=k_pE_p.
\tag{2.16}
$$

The signs agree with our choice $E_p=G_2-pG_2(pz)$ because $q\,d\log\eta/dq=-G_2$. Equations (2.14)--(2.16) check simultaneously the first coefficient, the Fricke sign, and the appearance of $n_p$.

They do not by themselves prove the q-expansion congruence. Reducing $d\log v_p$ gives the coefficient system $k_pb_p(m)$, not $b_p(m)$, and $k_p$ need not be a unit modulo $n_p$. At $p=17$, for example, $k_p=6$ and $n_p=4$. The logarithmic derivative sees twice the desired mod-$4$ class. The divided correction of Section 6.5 is exactly what restores the missing factor. This explains both the value and the limitation of the modular-unit heuristic.

## 3. Hecke eigenvalues of the Eisenstein series

### 3.1 Good-prime operators

The next goal is to identify the character of the Hecke algebra suggested by $E_p$. For $\ell\neq p$, Book 113 gives the weight-two coefficient formula

$$
a_m(T_\ell f)=a_{\ell m}(f)+\ell a_{m/\ell}(f),
\tag{3.1}
$$

where the second term is zero unless $\ell\mid m$.

**Proposition 3.1.** If $\ell\neq p$, then

$$
T_\ell E_p=(1+\ell)E_p.
\tag{3.2}
$$

**Proof strategy.** Check the coefficient identity using the divisor-sum recurrence, including the constant term. Q-expansion injectivity then turns coefficient equality into equality of forms.

**Proof.** Write $m=\ell^rs$ with $\ell\nmid s$. Because $\ell\neq p$, multiplicativity and (2.8) give

$$
b_p(\ell m)+\ell b_p(m/\ell)
=b_p(s)\bigl(b_p(\ell^{r+1})+\ell b_p(\ell^{r-1})\bigr).
$$

With the second summand omitted for $r=0$, the geometric sums satisfy

$$
b_p(\ell^{r+1})+\ell b_p(\ell^{r-1})
=(1+\ell)b_p(\ell^r).
$$

Thus every positive coefficient is multiplied by $1+\ell$. The constant-term formula for $T_\ell$ in weight two is also multiplication by $1+\ell$. Hence (3.2) follows from q-expansion injectivity. $\square$

### 3.2 The operator at the level prime

At $p$ the operator is $U_p$, not the good-prime $T_p$. Its coefficient action is especially simple.

**Proposition 3.2.** One has

$$
U_pE_p=E_p.
\tag{3.3}
$$

**Proof.** Formula (2.7) gives $b_p(pm)=b_p(m)$ for every $m\geq1$. The constant at the infinity cusp is fixed by the standard $U_p$ normalization. Hence the two q-expansions agree, and q-expansion injectivity proves the assertion. $\square$

This is the ordinary $p$-stabilization of the level-one Eisenstein eigenvalue system. The other root of the formal polynomial at $p$ would be $p$; the choice in (2.3) selects the root $1$.

### 3.3 All coefficients from the eigenvalues

For $m$ prime to $p$, let $T_m$ be determined by the usual Hecke recurrences. Propositions 3.1 and 3.2 imply

$$
T_mE_p=\sigma_1(m)E_p\quad((m,p)=1),
\qquad
U_p^rE_p=E_p.
\tag{3.4}
$$

If $n=p^rm$ with $(m,p)=1$, set

$$
\mathcal T_n=U_p^rT_m.
\tag{3.5}
$$

Then

$$
\mathcal T_nE_p=b_p(n)E_p.
\tag{3.6}
$$

The same operators recover Fourier coefficients of cusp forms:

$$
a_1(\mathcal T_nf)=a_n(f).
\tag{3.7}
$$

For $(n,p)=1$ this is the standard identity $a_1(T_nf)=a_n(f)$; repeated use of $a_1(U_pg)=a_p(g)$ gives the general case. Equation (3.7) will make the first Fourier coefficient into a perfect duality functional.

### 3.4 Why normalization matters

Multiplying $E_p$ by a rational scalar does not change its eigenvalues, but it changes its first coefficient and its apparent congruence modulus. We have fixed $a_1(E_p)=1$. This makes the Eisenstein character

$$
T_\ell\longmapsto1+\ell,
\qquad U_p\longmapsto1
\tag{3.8}
$$

compatible with the identity operator through $b_p(1)=1$. It also makes a congruent cusp form normalized by $a_1=1$.

There are two further normalization traps. First, adjoining a formal $T_p$ and imposing $T_p=1+p$ is not the same as using the level operator $U_p$ and imposing $U_p=1$. Second, omitting $U_p$ defines a smaller away-from-$p$ Hecke algebra; its quotient can fail to distinguish the two $p$-stabilizations. The exact index theorem below is for the acting algebra containing $U_p$.

### 3.5 The Dirichlet series and the missing Euler factor

The divisor-sum coefficients admit an analytic consistency check. For $\operatorname{Re}(s)>2$, absolute convergence permits rearrangement:

$$
\begin{aligned}
\sum_{m\geq1}\frac{b_p(m)}{m^s}
&=\sum_{m\geq1}\sum_{\substack{d\mid m\\p\nmid d}}
\frac d{m^s}\\
&=\sum_{\substack{d\geq1\\p\nmid d}}d^{1-s}
\sum_{e\geq1}e^{-s}\\
&=\zeta(s)\zeta(s-1)(1-p^{1-s}).
\end{aligned}
\tag{3.9}
$$

At a good prime $\ell$, the local factor is

$$
\frac1{(1-\ell^{-s})(1-\ell^{1-s})},
$$

whose two formal parameters are $1$ and $\ell$ and whose trace is $1+\ell$. At $p$, multiplication by $1-p^{1-s}$ cancels the second factor and leaves $(1-p^{-s})^{-1}$, corresponding to the single eigenvalue $U_p=1$. Thus the Euler product recovers the Hecke system of Chapter 3.

This factorization is explanatory rather than foundational. Equality of Dirichlet series verifies the coefficient calculation, but an integral congruence requires the q-expansion lattice and cannot be read from Euler factors alone.

## 4. Integral weight-two forms at prime level

### 4.1 The cusp-form lattice

Let

$$
S=S_2(\Gamma_0(p);\mathbf Z).
\tag{4.1}
$$

The traditional geometric model uses the relative dualizing sheaf on the integral compactification. In this book we instead begin with the specialized integral q-expansion identity

$$
S=S_2(\Gamma_0(p);\mathbf Q)\cap\mathbf Z[[q]].
\tag{4.2}
$$

The intersection is taken inside $\mathbf Q[[q]]$ at $\infty$, and (4.2) is the definition of $S$. To see finiteness without assuming an integral model, choose finitely many coefficient functionals that separate the finite-dimensional rational cusp space. They embed it into $\mathbf Q^d$; the q-integral intersection lies in the inverse image of $\mathbf Z^d$, while clearing the denominators of a rational basis supplies a full sublattice. Hence $S$ is finite free. Away from $p$, the all-cusp criterion of Book 113 identifies it with the regular-dualizing lattice. At $p$, the special fiber is reducible, so a one-cusp argument from Book 113 would be invalid; the normalization and weighted-node calculation in Section 6.3 proves the required $p$-saturation. Thus agreement with the geometric model over all of $\mathbf Z$ is a conclusion of the present denominator calculation, not an unrecorded prerequisite.

When testing an arbitrary rational modular form not already known to be cuspidal, integrality at both cusps remains the safe criterion. The special q-lattice (4.2) is available only because the object being tested is already in the rational cusp space.

The essential properties, supplied by Book 113 away from $p$ and by the definitions and saturation calculation here at $p$, are:

1. the map $f\mapsto(a_m(f))_{m\geq1}$ is injective and its integral image is the saturated lattice (4.2);
2. $S$ is saturated in the rational cusp space $S_\mathbf Q$;
3. every $T_\ell$ for $\ell\neq p$ and $U_p$ preserves $S$;
4. reduction of a member of $S$ modulo an integer is determined by its q-expansion.

The distinction between the specialized identity (4.2) and the general criterion matters. A rational logarithmic form can have an integral series at one cusp and a denominator at the other. The stronger statement for the established cusp lattice is a theorem, not a license to ignore the second cusp in later boundary calculations.

### 4.2 Constant terms as residues

Logarithmic Kodaira--Spencer identifies a weight-two form with a differential having at worst simple logarithmic poles at the cusps. In a genuine cusp parameter $t$,

$$
f(t)=\sum_{m\geq0}a_m t^m
\quad\longmapsto\quad
f(t)\frac{dt}{t}
\tag{4.3}
$$

after the chosen frame absorbs the cusp width. The residue is $a_0$. A weight-two form is cuspidal exactly when both residues vanish.

For $E_p$, (2.11) gives opposite residues. Over $\mathbf Q$ they are nonzero, so $E_p$ is not cuspidal. If the whole form had an integral model over a ring $R$ and those constants vanished in $R$, it would become cuspidal by the boundary criterion. The subtlety is that $E_p$ itself need not lie in the integral modular-form lattice at $2$ and $3$, even though all its positive Fourier coefficients are integers.

### 4.3 What the denominator 24 does and does not prove

Suppose an odd prime $r\geq5$ divides $p-1$. Since $24$ is a unit modulo $r$, the constant $(p-1)/24$ vanishes modulo the appropriate power of $r$ exactly when that power divides $p-1$. In this range the constant-term argument predicts the correct exponent in $n_p$.

At $r=3$, one factor of $3$ is absorbed by the denominator. This again agrees with (1.2). At $r=2$, however, the constant term suggests losing three powers of $2$, while (1.2) loses only two. The missing factor of $2$ comes from integral descent at the elliptic points: the normalized positive q-series can be congruent to a cusp form even when the rational Eisenstein series, viewed with its chosen rational constant term, does not reduce as an integral global section.

The level $17$ calculation makes this concrete. The exact theorem produces a cusp form

$$
f(q)\equiv\sum_{m\geq1}b_{17}(m)q^m\pmod4,
\tag{4.4}
$$

although $(17-1)/24=2/3$ is not zero modulo $4$. There is no contradiction: (4.4) compares the nonconstant series with an integral cusp form. It does not claim that the rational section $E_{17}$ has an integral reduction modulo $4$ with its displayed constant term.

### 4.4 Reduction modulo an integer

For $m\geq1$, write

$$
S_m=S/mS.
\tag{4.5}
$$

This is the reduction of the fixed integral cusp lattice. A congruence

$$
f(q)\equiv\sum_{n\geq1}b_p(n)q^n\pmod m
\tag{4.6}
$$

means that $f\in S_m$ and $a_n(f)=b_p(n)$ in $\mathbf Z/m\mathbf Z$ for every $n\geq1$. The first coefficient forces $a_1(f)=1$, so such an $f$ is unique by q-expansion injectivity.

It is often useful to divide an integral lift by $m$. The congruence (4.6) is equivalent to the existence of a class

$$
\bar g\in S_\mathbf Q/S
\tag{4.7}
$$

whose coefficients in $\mathbf Q/\mathbf Z$ are

$$
a_n(\bar g)=\frac{b_p(n)}m+\mathbf Z.
\tag{4.8}
$$

Indeed, if $f_0\in S$ lifts $f$, take $\bar g=f_0/m+S$. Conversely, if (4.8) holds, multiplying a representative by $m$ gives an integral cusp form with the required coefficient congruence. This reformulation turns all moduli at once into one finite subgroup of $\mathbf Q/\mathbf Z$.

## 5. The acting Hecke algebra and its Fourier dual

### 5.1 Definition of the algebra

Let

$$
\boxed{
\mathbb T=\mathbf Z[T_\ell\ (\ell\neq p),U_p]
\subseteq\operatorname{End}_{\mathbf Z}(S)}
\tag{5.1}
$$

be the image of the indicated commuting operators. It is enough to use prime-index generators because the Hecke recurrences produce every $T_m$ with $(m,p)=1$. Since $S$ is finite free, $\mathbb T$ is a finite torsion-free, hence finite free, $\mathbf Z$-module.

If $S=0$, its endomorphism ring is the zero ring and $\mathbb T$ is the zero ring. This convention makes the small genus-zero cases agree with the formula $\mathbf Z/1\mathbf Z=0$.

### 5.2 The first-coefficient pairing

Define

$$
\langle T,f\rangle=a_1(Tf),
\qquad T\in\mathbb T,\quad f\in S.
\tag{5.2}
$$

This is a bilinear pairing $\mathbb T\times S\to\mathbf Z$. Equation (3.7) says

$$
\langle\mathcal T_n,f\rangle=a_n(f).
\tag{5.3}
$$

Thus the Hecke orbit of the first-coefficient functional contains every Fourier-coefficient functional. This is the special feature that turns q-expansion injectivity into duality.

### 5.3 Perfectness

**Theorem 5.1 (Hecke--Fourier duality).** The map

$$
S\longrightarrow\operatorname{Hom}_{\mathbf Z}(\mathbb T,\mathbf Z),
\qquad
f\longmapsto(T\mapsto a_1(Tf)),
\tag{5.4}
$$

is an isomorphism.

**Proof strategy.** Identify the Hecke algebra with the lattice spanned by all Fourier-coefficient functionals. The dual of that span consists exactly of rational cusp forms with integral q-expansion, which is $S$ by (4.2). Equality of dual lattices then gives equality of the original lattices.

**Proof.** Let $L\subseteq S^\vee=\operatorname{Hom}_{\mathbf Z}(S,\mathbf Z)$ be the lattice generated by all $a_n$. Every product of the generators in (5.1) is a $\mathbf Z$-linear combination of the operators $\mathcal T_n$, by the good-prime recurrences and the relation defining $U_p$. Hence

$$
\mathbb T\longrightarrow S^\vee,
\qquad T\longmapsto(f\mapsto a_1(Tf))
\tag{5.5}
$$

has image $L$.

The map is injective. If its value on $T$ is zero, then commutativity and (3.7) give, for every $n$ and $f$,

$$
a_n(Tf)=a_1(\mathcal T_nTf)=0.
$$

Q-expansion injectivity gives $Tf=0$ for every $f$, and the acting-image convention gives $T=0$.

Compute the dual lattice of $L$ inside $S_\mathbf Q$:

$$
L^\sharp
=\{f\in S_\mathbf Q:a_n(f)\in\mathbf Z
\text{ for every }n\geq1\}.
\tag{5.6}
$$

Identity (4.2) says exactly that $L^\sharp=S$. The dual lattice of the full dual $S^\vee$ is also $S$, because a finite free module is its double dual. Finally, two full lattices in one rational vector space are equal when their dual lattices are equal. In a basis, if one is obtained from the other by a rational matrix $A$, equality of the two duals says that both $A$ and $A^{-1}$ are integral; hence $\det A$ is a unit and the lattices coincide. Therefore $L=S^\vee$.

Thus (5.5) identifies $\mathbb T$ with $S^\vee$. Dualizing identifies $S$ with $\mathbb T^\vee$, and the resulting map is (5.4). $\square$

This proof is integral from the beginning. Rational semisimplicity or multiplicity one would not by itself exclude a finite index between the two lattices; the dual-lattice calculation does.

Tensoring (5.4) with $\mathbf Q/\mathbf Z$ gives a canonical identification

$$
S_\mathbf Q/S
\xrightarrow{\sim}
\operatorname{Hom}_{\mathbf Z}(\mathbb T,\mathbf Q/\mathbf Z).
\tag{5.7}
$$

Under it, the $n$th coefficient of a class is its value on $\mathcal T_n$.

### 5.4 The formal Eisenstein quotient

The formulas of Chapter 3 suggest imposing

$$
T_\ell=1+\ell\quad(\ell\neq p),
\qquad U_p=1.
$$

Define the Eisenstein ideal

$$
I=(T_\ell-(1+\ell):\ell\neq p)+(U_p-1)\subseteq\mathbb T.
\tag{5.8}
$$

Modulo $I$, the Hecke recurrences give

$$
\mathcal T_n\equiv b_p(n)\cdot1\pmod I
\quad(n\geq1).
\tag{5.9}
$$

Since the $\mathcal T_n$ span $\mathbb T$ as a $\mathbf Z$-module, (5.9) shows that $\mathbb T/I$ is cyclic as an abelian group, generated by the image of $1$. Therefore

$$
\mathbb T/I\simeq\mathbf Z/d\mathbf Z
\tag{5.10}
$$

for a uniquely determined $d\geq0$, using $\mathbf Z/0\mathbf Z=\mathbf Z$ and representing the zero ring by $d=1$. Nothing so far proves that $d$ is nonzero. The next chapter computes the torsion dual; that calculation will simultaneously prove finiteness and show $d=n_p$.

### 5.5 The quotient's universal property

The ideal $I$ is best understood through maps out of its quotient. If $A$ is a commutative ring, a homomorphism

$$
\psi:\mathbb T/I\longrightarrow A
\tag{5.11}
$$

is the same thing as an acting Hecke character $\mathbb T\to A$ satisfying

$$
\psi(T_\ell)=1+\ell\quad(\ell\neq p),
\qquad
\psi(U_p)=1.
\tag{5.12}
$$

The recurrences force

$$
\psi(\mathcal T_n)=b_p(n)
\tag{5.13}
$$

for every $n$. Conversely (5.13) includes the prime generators and implies (5.12). Thus $\mathbb T/I$ represents the Eisenstein eigensystem occurring inside the cuspidal acting algebra.

Because every $\mathcal T_n$ is scalar modulo $I$, the structural map $\mathbf Z\to\mathbb T/I$ is surjective. Its kernel is some ideal $(d)$, recovering (5.10) without choosing a basis of $\mathbb T$; at this stage $(d)$ could be the zero ideal. The exact index problem is therefore the problem of proving that a positive integer acts as zero and determining the least one.

The rational form $E_p$ does not itself define a character of the algebra in (5.1), because that algebra acts only on cusp forms. It supplies the desired eigenvalues. The q-expansion congruence theorem decides exactly over which quotient coefficient rings those values actually occur on the cuspidal lattice.

## 6. The integral Eisenstein congruence calculation

### 6.1 The statement to be proved

The difficult arithmetic input is most economical when stated in $\mathbf Q/\mathbf Z$. Let $C_p$ be the set of $x\in\mathbf Q/\mathbf Z$ for which there exists $g\in S_\mathbf Q/S$ satisfying

$$
a_m(g)=b_p(m)x
\qquad(m\geq1).
\tag{6.1}
$$

Because q-expansion is injective, $g$ is unique when it exists. Addition of forms shows that $C_p$ is a subgroup of $\mathbf Q/\mathbf Z$.

**Theorem 6.1 (integral Eisenstein calculation).** For every prime $p\geq5$,

$$
\boxed{C_p=(\tfrac1{n_p}\mathbf Z)/\mathbf Z.}
\tag{6.2}
$$

Thus an Eisenstein coefficient system of additive order $m$ occurs in the cuspidal lattice quotient exactly when $m\mid n_p$.

The rest of this chapter proves the theorem. Neither a rational residue argument nor abstract Hecke algebra supplies the integral denominator. The proof uses the boundary residue sequence, the Hasse filtration and elliptic-gerbe descent at the good-level primes, and an explicit normalization-residue determinant at the level prime.

### 6.2 The two-cusp integral lattice

Over $\mathbf Z[1/p]$, the rational form $E_p$ is a section of

$$
H^0\bigl(\mathscr X_0(p)_\mathbf Q,\lambda^2\bigr)
\simeq H^0\bigl(\mathscr X_0(p)_\mathbf Q,
\omega_{\mathrm{dual}}(0+\infty)\bigr).
\tag{6.3}
$$

For $r\ne p$, the cusp lattice is locally

$$
S\otimes\mathbf Z_r
=H^0\bigl(\mathscr X_0(p)_{\mathbf Z_r},
\omega_{\mathrm{dual}}\bigr).
\tag{6.4}
$$

At an elliptic point a stabilizer acts on the Hodge fiber, so passing to the coarse curve before taking invariants can change the integral lattice at $2$ or $3$. We need the following precise two-cusp calculation. It also includes the bad-level saturation at $r=p$ that Book 113 does not supply.

**Lemma 6.2 (two-cusp Eisenstein lattice lemma).** Fix a prime $r$ and put $a=v_r(p-1)$. Let $x\in\mathbf Q_r/\mathbf Z_r$ have order $r^s$. There is a class $g\in S_{\mathbf Q_r}/S_{\mathbf Z_r}$ satisfying

$$
a_m(g)=b_p(m)x\qquad(m\geq1)
\tag{6.5}
$$

if and only if

$$
s\leq
\begin{cases}
a=0,&r=p,\\
a,&r\geq5,\ r\ne p,\\
\max(0,a-1),&r=3,\\
\max(0,a-2),&r=2.
\end{cases}
\tag{6.6}
$$

**Proof plan.** The q-series fixes a rational section on the punctured cusp disc. Normality reduces extension to codimension one. At a good-level prime, the ordinary Igusa trivialization and the Hasse invariant classify q-invisible corrections; descent at the order-three and order-four elliptic gerbes determines their exact integral denominator. At the level prime, normalization of the two-component fiber reduces saturation to an explicit weighted graph determinant.

The boundary mechanism comes directly from the Cartier sequence. Let $D=0+\infty$. Tensor

$$
0\longrightarrow\mathcal O(-D)
\longrightarrow\mathcal O
\longrightarrow\mathcal O_D
\longrightarrow0
$$

with $\lambda^2$. Logarithmic Kodaira--Spencer identifies $\lambda^2$ with $\omega_{\mathrm{dual}}(D)$ and $\lambda^2(-D)$ with $\omega_{\mathrm{dual}}$. Global sections therefore begin an exact sequence

$$
0\longrightarrow S_2
\longrightarrow M_2
\xrightarrow{\mathrm{ct}}
H^0(D,\lambda^2|_D)
\xrightarrow{\delta}H^1(\omega_{\mathrm{dual}}).
$$

After inverting $6p$, relative duality identifies the last module with the dual of the constants. On a connected tame fiber, $\delta$ is the sum-of-residues map. In the two Tate frames its kernel is the opposite-value line

$$
\{(u,v):u+v=0\}.
$$

Thus a logarithmic form is cuspidal precisely when its boundary pair is zero. In tame characteristic the opposite-value relation is the only relation. At $2$ and $3$, taking stabilizer invariants is not exact and must be calculated.

**Local correction lemma.** Let $r\ne p$. Among weight-two special-fiber sections whose positive expansion at $\infty$ is zero, the only possible nonzero directions are

$$
\begin{array}{c|c|c}
r&\text{q-invisible direction}&(c_\infty,c_0)\\ \hline
r\ge5&0&0\\
3&\mathbf F_3 A_3&(t,t)\\
2&\mathbf F_2 A_2^2&(t,t).
\end{array}
\tag{6.7}
$$

At $2$ the last direction contributes one elementary divisor $2$ to the saturation of the integral descent lattice, and no second divisor. At $3$ it contributes nothing to the opposite-value line.

**Proof.** On the ordinary locus, trivialize the Hodge line by the differential of the canonical multiplicative subgroup. The Igusa deck character has order $r-1$. A section with constant q-expansion is invariant under that character only if its weight is $0$ modulo $r-1$. In weight two this is impossible for $r\ge5$, gives $A_3$ for $r=3$, and gives $A_2^2$ for $r=2$.

Here $A_r$ is the Hasse invariant: Verschiebung induces a map on invariant differentials, and its scalar is a section of $\lambda^{r-1}$. On the Tate curve the canonical subgroup is multiplicative, so this scalar has q-expansion $1$. It vanishes exactly when the elliptic curve is supersingular. Moreover, each zero is simple. Indeed, the framed deformation ring of a supersingular elliptic curve is $W(\overline{\mathbf F}_r)[[t]]$; the connected--étale boundary of its height-two group is cut out to first order by $t$, and the Verschiebung scalar has nonzero image in $(t)/(t^2)$. Thus $A_r$ is a parameter up to a unit there.

These observations also prove that the displayed list is exhaustive. If two integral sections have the same positive q-expansion modulo $r$, their difference is constant on the punctured ordinary Igusa cover, so the deck-character calculation makes it the stated Hasse direction. Division by another Hasse factor would have negative order at every supersingular point. Normality tests extension in codimension one, hence excludes it. For a congruence modulo $r^j$, divide the difference of two lifts by the largest known power of $r$ and reduce modulo $r$; repeating the same argument gives the successive Smith layers and introduces no new direction.

For integral descent, choose a finite framed cover and take the Čech equalizer. Away from the elliptic residual gerbes, its group order is prime to $r$, so invariants are exact. The Hasse forms take value $1$ at both cusps, giving the displayed equal-value line. At the order-four gerbe, pass faithfully flatly to $\mathbf Z_2[i]$ and choose a Hodge frame $e$. Since $i^*e=ie$, the action on $e^2$ is $-1$. A coefficient $c$ modulo $2^j$ descends exactly when

$$
c=-c,
\qquad 2c=0.
\tag{6.8}
$$

The solution module is $2^{j-1}\mathbf Z_2[i]/2^j$, a single layer of order $2$; a unit coefficient cannot descend modulo $4$. There may be two framed elliptic points, but the Igusa calculation has already reduced the q-invisible space to the single global line $\mathbf F_2A_2^2$. Every gerbe tests the same coefficient and imposes the same equation (6.8), so their number does not create extra elementary divisors. The Čech equalizer is saturated everywhere else, because there all stabilizer orders are units and averaging splits the invariants. Consequently its Smith normal form adds exactly one divisor $2$ to the global lattice. At the order-three gerbes the single global line $\mathbf F_3A_3$ remains on the equal-value line and cannot meet the opposite-value line because $2$ is a unit in $\mathbf F_3$. This proves the lemma. $\square$

This argument proves existence as well as obstruction: exactness of the Čech complex glues the unique permitted correction. It does not infer a global form merely from a value at one stacky point.

### 6.3 The calculation at primes at least five

We first dispose of $r=p$. This is a saturation question at the bad-level fiber, not an application of Book 113.

**Bad-level saturation lemma.** The quotient between the one-cusp q-expansion lattice and the regular-dualizing lattice on the normalized prime-level model has order prime to $p$. Consequently no $p$-primary class can satisfy (6.5).

**Proof.** The moduli problem has two normalized components in characteristic $p$, corresponding to the connected and étale choices for the cyclic subgroup. Each is the level-one coarse curve, hence a projective line, and they meet at the supersingular classes.

Here is the local calculation rather than an appeal to a bad-level model. Frame the source and target of the universal degree-$p$ isogeny. The deformation functor of a framed supersingular elliptic curve is unobstructed of dimension one, and choosing a cyclic subgroup adds the choice of one of the connected and étale directions. Let $x$ be the scalar induced by the isogeny on invariant differentials and $y$ the scalar induced by its dual. Their images generate the cotangent lines of those two directions. The identity $\varphi^\vee\varphi=[p]$ gives $xy=p$ up to a unit; rescaling one parameter removes the unit. The resulting map from $W[[x,y]]/(xy-p)$ to the completed framed deformation ring is an isomorphism: both rings are flat relative complete intersections of dimension two, and the tangent map is an isomorphism. If $x$ is a unit the kernel is étale, and if $y$ is a unit it is connected. In characteristic $p$ these are the two branches $x=0$ and $y=0$, and they meet exactly when neither scalar is a unit, which is the supersingular case. Thus the framed completed equation is $xy=p$, and the preceding description proves both the two-component normalization and its crossing locus.

After removing the generic central involution, an exceptional supersingular class has effective stabilizer

$$
e(E)=1,\ 2,\ \text{or }3.
$$

The stabilizer acts by opposite characters, $(x,y)\mapsto(\zeta x,\zeta^{-1}y)$. Hence the invariant parameters $X=x^{e(E)}$ and $Y=y^{e(E)}$ satisfy $XY=p^{e(E)}$; every other invariant monomial is generated by $X,Y,$ and $xy=p$. Successive blowups of $XY=p^{e(E)}$ insert $e(E)-1$ rational curves, so the resolved node is a path of $e(E)$ unit edges.

The normalization residue sequence identifies the possible failure of one-component q-saturation with the discriminant of

$$
X=\left\{(a_E)\in\mathbf Z^{\mathcal S}:\sum_Ea_E=0\right\},
\qquad q(a,b)=\sum_Ee(E)a_Eb_E.
\tag{6.9}
$$

Indeed, a dualizing differential is a tuple on the normalized components with opposite residues on the two branches of every resolved node. Changing an integral tuple changes its residue vector by $qX$. Thus the obstruction group is $X^\vee/qX$. Choose one edge $E_0$ and the basis $[E]-[E_0]$. Its Gram matrix is

$$
Q=\operatorname{diag}(e(E):E\ne E_0)
+e(E_0)\mathbf1\mathbf1^t,
$$

and the matrix determinant lemma gives

$$
|\det Q|
=\left(\prod_Ee(E)\right)
\left(\sum_E\frac1{e(E)}\right).
\tag{6.10}
$$

The Hasse invariant has weight $p-1$, q-expansion $1$, and one simple zero at each supersingular point. Simplicity follows from the universal deformation ring: its first-order Hasse scalar is the nonzero parameter separating the connected and étale loci. On the rigidified level-one stack, $\deg\lambda=1/12$ because $\Delta$ has weight $12$ and one cusp zero. Taking degrees gives

$$
\sum_E\frac1{e(E)}=\frac{p-1}{12}.
\tag{6.11}
$$

There is at most one factor $2$ and at most one factor $3$. The Hasse-coefficient test on $y^2=x^3-x$ and $y^2=x^3-1$ shows that they occur respectively for $p\equiv3\pmod4$ and $p\equiv2\pmod3$. Hence

$$
\prod_Ee(E)=\frac{12}{\gcd(p-1,12)}.
$$

Equations (6.10)--(6.11) give $|\det Q|=n_p$, which is prime to $p$. The two lattices therefore have the same $p$-saturation.

If (6.5) held with $x$ of order $p^s>1$, multiply by a $p$-adic unit so that $x$ is represented by $p^{-s}$. Subtracting $p^{-s}E_p$ from a rational representative of the cusp class would give integral positive q-coefficients but boundary value $-(p-1)/(24p^s)$. Both $p-1$ and $24$ are $p$-adic units, so this value is nonintegral. The just-proved saturation leaves no correction that can absorb it. $\square$

Now assume $r\geq5$ and $r\neq p$. The stabilizers of orders $2$ and $3$ are linearly reductive over $\mathbf Z_r$, so taking invariants is exact. The stack and coarse q-integral lattices therefore agree at $r$.

Write

$$
p-1=r^a u,
\qquad u\in\mathbf Z_r^\times.
$$

Because $24$ is a unit in $\mathbf Z_r$, the form $E_p$ is integral over $\mathbf Z_r$: all positive coefficients are integers and its two constants

$$
\pm\frac{p-1}{24}
$$

lie in $r^a\mathbf Z_r$. Reduction modulo $r^a$ is therefore a regular differential at both cusps. This gives a cusp form with q-expansion

$$
\sum_{m\geq1}b_p(m)q^m\pmod{r^a}.
\tag{6.12}
$$

It proves existence for every $s\leq a$ by further reduction.

For necessity, suppose (6.5) holds with $x$ of order $r^s$. Multiplying by a unit, we may take $x=r^{-s}+\mathbf Z_r$. Choose a rational lift $g$ and consider

$$
h=g-r^{-s}E_p.
\tag{6.13}
$$

All positive coefficients of $h$ are integral. The all-cusp divisibility theorem says that the only obstruction to $h$ lying in the integral logarithmic lattice is its boundary value. At $\infty$ that value is

$$
-\frac{p-1}{24r^s}.
\tag{6.14}
$$

At $0$ it is the negative, because both $g$ and the Eisenstein eigensystem lie in the $-1$ Fricke direction. The local correction lemma gives no q-invisible direction when $r\geq5$. Hence the displayed boundary value must be integral, and $s\leq a$.

Here is the promised justification of the Fricke direction. Sum the weight-two translates over the $p+1$ right cosets of $\Gamma_0(p)$ in $\operatorname{SL}_2(\mathbf Z)$. Pairing the $p$ nonidentity cosets with the Fricke matrix gives the normalized trace identity

$$
\operatorname{Tr}_{\Gamma_0(p)}^{\operatorname{SL}_2(\mathbf Z)}(f)
=f+U_pW_pf.
$$

This follows directly on q-expansions: the root-of-unity sum in those $p$ cosets keeps precisely the coefficients indexed by multiples of $p$, and the determinant factor in the weight-two slash operator is the factor in (2.10), so no residual power of $p$ occurs. The trace lands in $S_2(\operatorname{SL}_2(\mathbf Z))=0$. Since $W_p^2=1$, right multiplication by $W_p$ gives

$$
U_p=-W_p.
\tag{6.15}
$$

Both sides preserve $S$, hence the rational identity is integral. Since (6.5) implies $(U_p-1)g\in S$, it gives $(W_p+1)g\in S$. Thus the two boundary obstructions are indeed opposite modulo the integral lattice.

This completes both directions for $r\geq5$.

### 6.4 The prime three

Now let $r=3$ and write $p-1=3^a u$. If $a=0$, there is nothing to prove. Suppose $a\geq1$.

The rational constant $(p-1)/24$ has $3$-adic valuation $a-1$. By the local correction lemma, the only possible q-invisible correction is a multiple of $A_3$. It takes the same value at the two cusps, whereas the Eisenstein residues are opposite.

We make this precise using actual boundary values rather than the tame residue image. Over the special fiber, the boundary restriction map in weight two is

$$
M_2(\mathbf F_3)\longrightarrow
\mathbf F_3\oplus\mathbf F_3,
\qquad f\longmapsto(c_\infty(f),c_0(f)).
\tag{6.16}
$$

The Hasse invariant maps to $(1,1)$, while the Eisenstein boundary pair is $(c,-c)$. A multiple $tA_3$ cancels both entries only if

$$
t=c,
\qquad t=-c.
$$

Thus $2c=0$. In characteristic $3$, multiplication by $2$ is invertible, so $c=0$. A q-invisible Hasse correction therefore cannot cancel a nonzero opposite Eisenstein pair. Notice that we did not assert that every weight-two boundary pair lies on the tame opposite-value line: $A_3$ itself shows why that assertion would be false on the wild stack.

Existence through $3^{a-1}$ is direct. The form $E_p$ is integral over $\mathbf Z_3$ once $3\mid p-1$, and both constants are divisible by $3^{a-1}$. Its reduction is therefore cuspidal modulo that power.

For necessity, repeat the subtraction of $3^{-s}E_p$. If $s>a-1$, the first nonintegral boundary layer becomes, after multiplication by $3^{s-a+1}$ and reduction modulo $3$, a nonzero vector on the opposite-residue line. By (6.7), every q-invisible correction lies on the equal-value line. The two cannot cancel. Hence $s\leq a-1$.

This proves the $r=3$ line of (6.6). It also shows why simply saying “divide the constant by $24$” is not the proof: one must rule out a divided Hasse correction. The two-cusp residue relation does exactly that.

### 6.5 The two-primary calculation

Let $r=2$ and write $p-1=2^a u$ with $u$ odd. The assertion is empty for $a\leq2$, so assume $a\geq3$. The constant $(p-1)/24$ has valuation $a-3$, one less than the desired exponent $a-2$. Thus an extra divided step must exist, and no second extra step may exist.

The mod-$2$ Hasse invariant $A_2$ has weight $1$ and q-expansion $1$. Its square $A_2^2$ has weight two. At the two cusps it has values $(1,1)$. In characteristic $2$, equal and opposite pairs coincide:

$$
(1,1)=(1,-1).
\tag{6.17}
$$

This is the source of the extra factor.

We first construct the extra class. Divide $p-1$ by $2^{a}$ and choose the inverse of its odd part modulo $2$. The boundary of

$$
2^{-(a-2)}E_p
\tag{6.18}
$$

has first nonintegral layer represented by $(1,1)$ in characteristic $2$. Subtract the unique multiple of $A_2^2$ with that boundary value. The local correction lemma identifies the relevant invariant-lattice quotient, not merely its special fiber: its Smith normal form has one elementary divisor $2$. It therefore raises the constant-term exponent $a-3$ by exactly one and constructs a cusp class through $2^{a-2}$.

For clarity, the gerbe used in that calculation really occurs here. Since $a\ge3$, one has $p\equiv1\pmod4$. On an elliptic curve with automorphism $i$, the action on $E[p]$ has eigenlines over $\mathbf F_p$, so an $i$-stable cyclic subgroup of order $p$ exists. After the faithfully flat extension $\mathbf Z_2\subset\mathbf Z_2[i]$, choose a Hodge frame $e$. The automorphism acts by

$$
i^*e=i e,
\qquad
i^*(e^2)=-e^2.
\tag{6.19}
$$

Thus a coefficient $c$ multiplying the weight-two fiber descends only if $c=-c$, or

$$
2c=0.
\tag{6.20}
$$

Over $\mathbf Z/2^j\mathbf Z$, the solutions of (6.20) form the one-layer subgroup $2^{j-1}\mathbf Z/2^j\mathbf Z$. A further division would require a unit coefficient to satisfy (6.20) modulo $4$, which is impossible. Faithful flatness proves failure before extension. At a supersingular point, $A_2$ is a parameter up to a unit, so no additional q-invisible quotient can evade this obstruction by vanishing elsewhere.

We have proved existence up to $2^{a-2}$ and obstruction at the next power. This establishes the $r=2$ line of (6.6). It also explains why a coarse-curve calculation is unsafe: rigidifying the order-four stabilizer removes the anti-invariant fiber in (6.19) and loses the exact stopping point.

### 6.6 Global synthesis

Lemma 6.2 is now proved at every prime. We use it to prove Theorem 6.1.

Let $x\in\mathbf Q/\mathbf Z$ and write it as the sum of its primary components $x=\sum_r x_r$. The cusp lattice is finite free, so

$$
S_\mathbf Q/S\simeq\bigoplus_r
S_{\mathbf Q_r}/S_{\mathbf Z_r}
\tag{6.21}
$$

on torsion subgroups. Thus (6.1) is solvable for $x$ exactly when it is solvable for every $x_r$.

If $x_r$ has order $r^{s_r}$, Lemma 6.2 says

$$
s_r\leq\max\{0,v_r(p-1)-v_r(12)\}
=v_r(n_p).
\tag{6.22}
$$

Equivalently, $n_px_r=0$ for every $r$, hence $n_px=0$. Conversely, if $n_px=0$, each primary component satisfies the bound, and the locally constructed classes add to a global class in $S_\mathbf Q/S$. Therefore

$$
C_p=\{x\in\mathbf Q/\mathbf Z:n_px=0\}
=(\tfrac1{n_p}\mathbf Z)/\mathbf Z.
$$

This proves Theorem 6.1. Notice that the proof treated existence and maximality together. At $r\geq3$ the rational Eisenstein form itself supplies existence; at $2$ the single Hasse-square correction supplies the missing step; the stack stabilizer obstruction proves there is no second step.

## 7. The q-expansion congruence theorem

### 7.1 Existence, uniqueness, and exact modulus

The preceding calculation has a direct modular-form formulation.

**Theorem 7.1 (prime-level q-expansion congruence).** Let $p\geq5$ be prime and $m\geq1$. There exists a cusp form $f_m\in S/mS$ with

$$
f_m(q)=\sum_{r\geq1}b_p(r)q^r
\quad\text{in }(\mathbf Z/m\mathbf Z)[[q]]
\tag{7.1}
$$

if and only if $m\mid n_p$. When it exists, $f_m$ is unique and normalized by $a_1(f_m)=1$.

**Proof.** Section 4.4 identifies existence with the assertion that $x=1/m+\mathbf Z$ belongs to $C_p$. Its order in $\mathbf Q/\mathbf Z$ is $m$. By Theorem 6.1, this occurs exactly when $m\mid n_p$. Uniqueness follows from q-expansion injectivity, and the first coefficient is $b_p(1)=1$. $\square$

This is stronger than saying that finitely many coefficients happen to agree. It gives equality of the entire formal q-series and proves that no larger modulus is possible.

### 7.2 Faithful extension of the coefficient ring

The cyclic theorem is stable under a faithfully flat change of coefficients. This is the safe generality in which the modulus cannot disappear.

**Corollary 7.2.** Let $R$ be a faithfully flat $\mathbf Z/m\mathbf Z$-algebra. There is a cusp form $f_R\in S\otimes R$ with

$$
f_R(q)=\sum_{n\geq1}b_p(n)q^n
\quad\text{in }R[[q]]
\tag{7.2}
$$

if and only if $m\mid n_p$. It is unique.

**Proof.** If $m\mid n_p$, base change of $f_m$ from Theorem 7.1 gives $f_R$. Conversely, suppose $f_R$ exists. Theorem 5.1 says that the coefficient functionals generate $S^\vee$; consequently the q-expansion map remains injective after every coefficient extension, including nonflat ones. The two pullbacks of $f_R$ to $R\otimes_{\mathbf Z/m}R$ have identical q-expansions and are therefore equal. Faithfully flat descent gives $f_m\in S/mS$ with the stated expansion. Theorem 7.1 forces $m\mid n_p$. Uniqueness follows in the same way. $\square$

Faithfulness is important. After passing to a quotient in which a nonzero divisor of $m$ becomes zero, the additive order of $1$ can decrease, so the original modulus is no longer detectable. The theorem concerns the fixed integral cusp lattice and its honest coefficient extensions, not extra sections created by a nonflat base change.

### 7.3 Prime-power and composite moduli

If $r$ is prime, Theorem 7.1 gives a congruence modulo $r^e$ precisely for

$$
e\leq v_r(n_p)=\max\{0,v_r(p-1)-v_r(12)\}.
\tag{7.4}
$$

For coprime $m_1,m_2$, the Chinese remainder theorem identifies

$$
S/(m_1m_2)S\simeq S/m_1S\times S/m_2S.
$$

The two unique Eisenstein congruence forms glue to the unique form modulo $m_1m_2$. Thus the composite-modulus assertion contains no compatibility choice. This also gives an independent prime-by-prime proof of the sufficiency direction once the prime-power calculation is known.

The exactness says more: if $r^{e+1}\nmid n_p$, no change of integral lift can improve the congruence modulo $r^{e+1}$. Failure is global, not an artifact of a poorly normalized eigenform.

### 7.4 The exceptional small levels

At $p=2$ and $p=3$, the curves $X_0(p)$ have genus zero, so $S_2(\Gamma_0(p);\mathbf Z)=0$. Also

$$
n_2=\operatorname{num}(1/12)=1,
\qquad
n_3=\operatorname{num}(1/6)=1.
$$

Hence Theorem 7.1 remains true: only the modulus $1$ occurs. We separated these levels because their wild stack stabilizers require different local models, not because the final formula changes.

### 7.5 Coefficient congruence versus operator congruence

Three formulations of the Eisenstein congruence now coincide, but only after normalization. Let $R=\mathbf Z/m\mathbf Z$ and let $f\in S\otimes R$ have $a_1(f)=1$. The following are equivalent:

1. $a_n(f)=b_p(n)$ for every $n\geq1$;
2. $T_\ell f=(1+\ell)f$ for every prime $\ell\neq p$ and $U_pf=f$;
3. the assignments $T_\ell\mapsto1+\ell$ and $U_p\mapsto1$ respect all relations in $\mathbb T$, hence define a character $\epsilon:\mathbb T\to R$, and $Tf=\epsilon(T)f$ for every $T\in\mathbb T$.

For 1 implies 2, apply the coefficient formulas of Sections 3.1--3.2 and then q-expansion injectivity. For 2 implies 3, a polynomial relation among the generators acts on $f$ by the same polynomial in the proposed scalars. Since the relation is the zero operator and $a_1(f)=1$, that scalar is zero in $R$. The assignments therefore descend to the acting algebra and the generators give the eigenvector identity. The Hecke recurrences also give $\epsilon(\mathcal T_n)=b_p(n)$. Finally, from 3 and (3.7),

$$
a_n(f)=a_1(\mathcal T_nf)
=\epsilon(\mathcal T_n)a_1(f)=b_p(n),
\tag{7.5}
$$

which proves 3 implies 1.

Normalization is indispensable. The zero form satisfies every homogeneous eigenvalue equation, and a scalar multiple has coefficients $cb_p(n)$. Over a ring with zero divisors, merely asking that $f$ be nonzero is inadequate; asking that $a_1(f)$ be a unit is the natural condition, after which one rescales to $a_1(f)=1$.

The equivalence also clarifies finite verification. A Sturm bound can certify statement 1 after both sides are known to be cusp forms. It cannot define $\epsilon$ before existence is established, because the assigned scalars must first satisfy every relation in the acting Hecke algebra.

## 8. The Eisenstein ideal

### 8.1 Definition and equivalent generating sets

Recall

$$
I=(T_\ell-(1+\ell):\ell\neq p)+(U_p-1).
\tag{8.1}
$$

It is enough to let $\ell$ range over primes different from $p$. The Hecke relations then imply, for every $m$ prime to $p$,

$$
T_m-\sigma_1(m)\in I.
\tag{8.2}
$$

Indeed, coprime multiplicativity reduces to prime powers, and the recurrence

$$
T_{\ell^{r+1}}=T_\ell T_{\ell^r}-\ell T_{\ell^{r-1}}
\tag{8.3}
$$

matches

$$
\sigma_1(\ell^{r+1})=(1+\ell)\sigma_1(\ell^r)-\ell\sigma_1(\ell^{r-1}).
$$

Together with $U_p-1$, this is equivalent to

$$
I=(\mathcal T_n-b_p(n):n\geq1).
\tag{8.4}
$$

Equation (8.4) is particularly useful in duality because the $\mathcal T_n$ recover all Fourier coefficients.

### 8.2 Eisenstein maximal ideals

For a prime $r$, put

$$
\mathfrak m_r=(r,I)\subseteq\mathbb T.
\tag{8.5}
$$

This is a proper maximal ideal exactly when $r\mid n_p$. The forward implication will follow from the index theorem; the q-expansion theorem already proves the reverse implication. If $r\mid n_p$, the form $f_r$ of Theorem 7.1 is nonzero because $a_1(f_r)=1$, and

$$
T_\ell f_r=(1+\ell)f_r,
\qquad U_pf_r=f_r
\tag{8.6}
$$

by the Hecke coefficient formulas and q-expansion injectivity. Thus the acting algebra has the character

$$
\mathbb T\longrightarrow\mathbf F_r,
\quad T_\ell\mapsto1+\ell,
\quad U_p\mapsto1,
\tag{8.7}
$$

whose kernel is $\mathfrak m_r$.

The residual system is called Eisenstein because its good-prime polynomial is

$$
X^2-(1+\ell)X+\ell=(X-1)(X-\ell).
\tag{8.8}
$$

This factorization motivates the word “reducible,” but no representation is constructed or used here.

### 8.3 Congruent eigenforms

The form $f_m$ in $S/mS$ is a simultaneous eigenform for the entire specified Hecke algebra. For $\ell\neq p$, apply (3.1) to its coefficients:

$$
a_n(T_\ell f_m)
=b_p(\ell n)+\ell b_p(n/\ell)
=(1+\ell)b_p(n).
$$

The $U_p$ identity follows from $b_p(pn)=b_p(n)$. Since expansions determine forms,

$$
T_\ell f_m=(1+\ell)f_m,
\qquad U_pf_m=f_m.
\tag{8.9}
$$

Conversely, if $f\in S/mS$ is normalized by $a_1(f)=1$ and satisfies (8.9), the Hecke recurrences give $a_n(f)=b_p(n)$ for every $n$. Theorem 7.1 then forces $m\mid n_p$. Thus coefficient congruence and the Eisenstein eigensystem are exactly equivalent after normalization.

### 8.4 No lifting claim is hidden

The existence of $f_r$ modulo $r$ does not by itself produce an eigenform over a characteristic-zero discrete valuation ring. Abstract lifting of a residual character can fail when the local Hecke algebra is nonreduced or ramified. What is automatic is only that a maximal ideal $\mathfrak m_r$ occurs in the acting algebra and that its localized cusp module is nonzero.

If a characteristic-zero eigencharacter $\lambda:\mathbb T\to\mathcal O$ passes through $\mathfrak m_r$, then

$$
\lambda(T_\ell)\equiv1+\ell,
\qquad
\lambda(U_p)\equiv1
\pmod{\mathfrak p_\mathcal O}.
$$

That is a genuine congruence of eigencharacters in the sense of Book 85. The present theorem determines the total Eisenstein quotient, not the number, ramification, or multiplicity of characteristic-zero cuspidal branches above it.

## 9. The exact index theorem

### 9.1 Dualizing the quotient

We now turn the q-expansion calculation into the promised algebra theorem. The quotient $\mathbb T/I$ is cyclic and finitely generated, but finiteness has not yet been assumed. Its Pontryagin dual

$$
(\mathbb T/I)^\vee
=\operatorname{Hom}_{\mathbf Z}(\mathbb T/I,\mathbf Q/\mathbf Z)
\tag{9.1}
$$

detects both possibilities: the dual of $\mathbf Z/d\mathbf Z$ has order $d$ for $d>0$, whereas the dual of $\mathbf Z$ is the infinite group $\mathbf Q/\mathbf Z$. A homomorphism $\phi:\mathbb T\to\mathbf Q/\mathbf Z$ factors through $\mathbb T/I$ exactly when $\phi(I)=0$.

By Hecke--Fourier duality (5.7), such a $\phi$ corresponds to a unique class $g_\phi\in S_\mathbf Q/S$ with

$$
a_n(g_\phi)=\phi(\mathcal T_n).
\tag{9.2}
$$

This correspondence is integral: no rank comparison or semisimplification remains to be made.

### 9.2 Identification with the Eisenstein line

If $\phi(I)=0$, equation (8.4) yields

$$
\phi(\mathcal T_n)=b_p(n)\phi(1).
\tag{9.3}
$$

Thus $g_\phi$ lies on the Eisenstein coefficient line (6.1), with parameter $x=\phi(1)$. Conversely, if $x\in C_p$ and $g$ has coefficients $b_p(n)x$, the corresponding functional satisfies

$$
\phi(\mathcal T_n-b_p(n))=0
$$

for every $n$, so it kills $I$. Evaluation at $1$ therefore gives an isomorphism

$$
\boxed{
(\mathbb T/I)^\vee\xrightarrow{\sim}C_p,
\qquad \phi\longmapsto\phi(1).}
\tag{9.4}
$$

This is the decisive bridge. It also shows why all coefficients, rather than a finite sample, occur naturally: the operators $\mathcal T_n$ span the acting algebra.

### 9.3 Calculation of the quotient

**Theorem 9.1 (exact Eisenstein index).** For every prime $p$,

$$
\boxed{
\mathbb T/I\simeq\mathbf Z/n_p\mathbf Z.}
\tag{9.5}
$$

For $p\geq5$, the isomorphism sends the image of an integer to its residue class and satisfies

$$
T_\ell\longmapsto1+\ell,
\qquad U_p\longmapsto1.
\tag{9.6}
$$

**Proof.** By Theorem 6.1 and (9.4),

$$
(\mathbb T/I)^\vee
\simeq(\tfrac1{n_p}\mathbf Z)/\mathbf Z,
$$

a cyclic group of order $n_p$. The infinite alternative in Section 9.1 is therefore impossible, so $\mathbb T/I$ is finite. Its order equals the order of its dual, namely $n_p$. Section 5.4 showed that it is generated by $1$, so the structural map $\mathbf Z\to\mathbb T/I$ induces the asserted isomorphism. The cases $p=2,3$ have both sides equal to the zero ring. $\square$

The proof gives both inequalities simultaneously. The congruence form modulo $n_p$ proves that the quotient has at least that much torsion; the denominator obstruction proves that it has no more.

### 9.4 Index, order, and ring structure

Because $I$ has full rank in the finite free abelian group $\mathbb T$, the additive index is

$$
[\mathbb T:I]=\#(\mathbb T/I)=n_p.
\tag{9.7}
$$

This notation does not mean that $I$ is a rank-one ideal or that $\mathbb T$ is a principal ideal ring. It only measures the finite additive quotient. The stronger ring statement (9.5) says that the quotient is generated by the scalar class of $1$, so there are no extra nilpotents or noncyclic components in the global Eisenstein quotient.

The annihilator of $\mathbb T/I$ as a $\mathbf Z$-module is $(n_p)$. Equivalently,

$$
I\cap\mathbf Z=(n_p).
\tag{9.8}
$$

Indeed, an integer lies in $I$ precisely when its image vanishes in $\mathbf Z/n_p\mathbf Z$. Formula (9.8) is often the most useful integral form of the index theorem.

## 10. Local structure and depth of congruence

### 10.1 Localization at an Eisenstein prime

Let $r$ be a prime dividing $n_p$ and let

$$
\mathfrak m_r=(r,I).
$$

First tensor with $\mathbf Z_r$. The finite $\mathbf Z_r$-algebra $\mathbb T\otimes\mathbf Z_r$ is a product of complete local factors; let $\mathbb T_{\mathfrak m_r}$ denote the factor selected by $\mathfrak m_r$. Equivalently, it is the completion of the ordinary localization of $\mathbb T$ at $\mathfrak m_r$. Ordinary localization over $\mathbf Z_{(r)}$ alone would not yet be complete.

The localized module $S_{\mathfrak m_r}$ is faithful. This follows from the acting-image convention and localization of annihilators. It need not be free of rank one over $\mathbb T_{\mathfrak m_r}$, and its residual eigenspace need not be one-dimensional. None of those stronger multiplicity statements is needed for the index calculation.

### 10.2 The local index

Tensor (9.5) with $\mathbf Z_r$. If $e_r=v_r(n_p)$, then

$$
\boxed{
(\mathbb T/I)\otimes\mathbf Z_r
\simeq\mathbf Z_r/r^{e_r}\mathbf Z_r.}
\tag{10.1}
$$

Equivalently, in the Eisenstein local factor,

$$
\mathbb T_{\mathfrak m_r}/I\mathbb T_{\mathfrak m_r}
\simeq\mathbf Z_r/r^{e_r}\mathbf Z_r.
\tag{10.2}
$$

All other local factors vanish after quotienting by $I$. Thus the global integer decomposes exactly into its Eisenstein local lengths:

$$
\operatorname{length}_{\mathbf Z_r}
(\mathbb T_{\mathfrak m_r}/I)
=v_r(n_p).
\tag{10.3}
$$

This is a length over the coefficient DVR. It is not automatically the length of a cotangent module $I/I^2$, nor does it assert that the local algebra is a complete intersection. Book 85 distinguishes these invariants carefully.

### 10.3 Characteristic-zero branches

Suppose $\lambda:\mathbb T_{\mathfrak m_r}\to\mathcal O$ is a characteristic-zero eigencharacter with values in a finite extension of $\mathbf Z_r$. Its difference ideal from the Eisenstein values is

$$
J_\lambda=
(\lambda(T_\ell)-(1+\ell),\ \lambda(U_p)-1)
\subseteq\mathcal O.
\tag{10.4}
$$

If $J_\lambda\subseteq\varpi^a\mathcal O$, then the branch is congruent to the Eisenstein system to depth at least $a$ in the normalized valuation of $\mathcal O$. The exact index theorem bounds the combined congruence contribution of all branches, but it does not say that one branch realizes the entire exponent $e_r$. Several branches can share it, and ramification changes raw uniformizer lengths.

What is invariant is the ideal (10.4). If $\mathcal O'/\mathcal O$ has ramification index $e$, then the numerical valuation multiplies by $e$, while the extended ideal records the same congruence. This is why (10.1), stated over $\mathbf Z_r$, is the canonical base-level measurement.

### 10.4 The two-primary boundary

When $p\equiv1\pmod8$, the integer $n_p$ can be even. Formula (1.2) gives

$$
v_2(n_p)=v_2(p-1)-2.
\tag{10.5}
$$

The rational constant term $(p-1)/24$ would instead suggest $v_2(p-1)-3$. The discrepancy is exactly one. The integral stack calculation retains the sign stabilizer and its first divided Hasse correction, supplying that extra factor.

No division by $2$ is legitimate in this case. In particular, one may not pass to the coarse curve, average under the involution, or identify invariants with coinvariants without checking two-torsion. The proof of Chapter 6 is designed to survive precisely this boundary. At odd Eisenstein primes, the simpler residue heuristic happens to give the same exponent, but it remains a heuristic until integral descent is checked.

### 10.5 What the local length does not measure

The quotient in (10.2) is sometimes called the Eisenstein congruence module. Its length is exact, but several nearby modules can have different lengths. Put $A=\mathbb T_{\mathfrak m_r}$ and $J=IA$. The quotient $A/J$ measures the order to which the scalar Eisenstein character occurs. The conormal module

$$
J/J^2
\tag{10.6}
$$

measures first-order equations of the Eisenstein locus inside $A$. If an augmentation $\epsilon:A\to\mathbf Z_r$ has been defined, the annihilator ideal

$$
\epsilon(\operatorname{Ann}_A J)\subseteq\mathbf Z_r
\tag{10.7}
$$

measures the denominator of the generic projector onto that branch. There is no formal equality among these three objects.

For a simple warning, take

$$
A=\mathbf Z_r[X]/(X^2-rX).
$$

Its two generic branches meet modulo $r$. With $J=(X)$, the quotient $A/J\simeq\mathbf Z_r$ is not finite, while $X-r$ annihilates $J$ and its value on the branch $X=0$ has modulus $r$. Thus quotient length and branch congruence length answer different questions even in a hypersurface.

In the present arithmetic setting, Theorem 9.1 proves the special fact that $A/IA$ is finite of the length in (10.3). Equality with a conormal or annihilator length would require additional complete-intersection, Gorenstein, or multiplicity hypotheses. Those are not consequences of the exact index and are not asserted here.

## 11. Examples and diagnostic calculations

### 11.1 Levels with trivial Eisenstein quotient

If $p-1$ divides $12$, then $n_p=1$. For prime $p$ this occurs at

$$
p=2,3,5,7,13.
$$

The theorem says $\mathbb T/I=0$, or equivalently $I=\mathbb T$. There is no proper Eisenstein maximal ideal in the specified cusp-form Hecke algebra. For $p=5,7,13$, the genus of $X_0(p)$ is zero, so $S=0$ and this is visible immediately. The formula also explains the answer uniformly rather than treating zero-dimensional spaces as exceptions.

### 11.2 Levels 11 and 17

At $p=11$,

$$
n_{11}=\frac{10}{\gcd(10,12)}=5.
$$

Hence there is a unique normalized cusp form modulo $5$ with

$$
f(q)\equiv q+3q^2+4q^3+2q^4+q^5+\cdots\pmod5,
$$

where the coefficients are $b_{11}(m)=\sigma_1(m)$ until the first multiple of $11$. The Hecke quotient is $\mathbf Z/5\mathbf Z$.

At $p=17$,

$$
n_{17}=\frac{16}{4}=4.
$$

The unique congruence form modulo $4$ begins

$$
q+3q^2+0q^3+3q^4+2q^5+0q^6+0q^7+3q^8+\cdots.
$$

Here $\sigma_1(3)=4$, $\sigma_1(4)=7$, and $\sigma_1(5)=6$. This example displays the two-primary correction: a congruence modulo $4$ exists even though the displayed rational constant term $2/3$ does not vanish modulo $4$.

### 11.3 Levels 19, 37, and 73

At level $19$,

$$
n_{19}=\frac{18}{6}=3.
$$

There is an Eisenstein maximal ideal only above $3$, and its local quotient has length one over $\mathbf Z_3$.

At level $37$,

$$
n_{37}=\frac{36}{12}=3.
$$

Although $p-1$ contains $3^2$, one factor of $3$ is absorbed by the denominator $12$. Again the exact quotient is $\mathbf Z/3\mathbf Z$.

At level $73$,

$$
n_{73}=\frac{72}{12}=6.
$$

The quotient decomposes locally as

$$
\mathbf Z/6\mathbf Z
\simeq\mathbf Z/2\mathbf Z\times\mathbf Z/3\mathbf Z.
$$

The unique forms modulo $2$ and $3$ glue to the unique form modulo $6$. This illustrates why the global quotient is cyclic even though it has several Eisenstein maximal ideals.

### 11.4 A Sturm-style finite check

Theorem 7.1 is an infinite coefficient statement, but a proposed congruence can be certified finitely. The index of $\Gamma_0(p)$ in $\operatorname{SL}_2(\mathbf Z)$ is $p+1$, so a safe weight-two Sturm bound at the width-one cusp is

$$
B=\left\lfloor\frac{p+1}{6}\right\rfloor.
\tag{11.1}
$$

If $M$ is prime to $p$ and an integral cusp form $f$ satisfies

$$
a_m(f)\equiv b_p(m)\pmod M
\qquad(1\leq m\leq B)
\tag{11.2}
$$

then the finite-jet theorem of Book 113 forces the full congruence after comparing $f$ with the cusp class supplied by Theorem 7.1. Both forms are already cuspidal, so their constant terms vanish and positive coefficients through $B$ suffice. The condition $(M,p)=1$ keeps the comparison on the good-level base covered by Book 113; every possible Eisenstein modulus satisfies it because $p\nmid n_p$.

The bound verifies a candidate; it does not prove that a candidate exists. Existence and the maximal modulus come from the denominator calculation. Confusing these two roles would make a finite computation appear to establish an integral theorem that it only checks in a known space.

## 12. The prime-level Eisenstein package

### 12.1 Dependency-closed theorem

We collect the result in the exact form available for later use.

**Theorem 12.1 (prime-level Eisenstein package).** Let $p$ be prime, let

$$
S=S_2(\Gamma_0(p);\mathbf Z),
$$

and let $\mathbb T\subseteq\operatorname{End}_{\mathbf Z}(S)$ be the acting algebra generated by $T_\ell$ for $\ell\neq p$ and $U_p$. Define

$$
E_p=G_2-pG_2(pz),
\qquad
I=(T_\ell-1-\ell,\ U_p-1),
\qquad
n_p=\operatorname{num}\left(\frac{p-1}{12}\right).
$$

Then:

1. $E_p$ is a rational weight-two form on $\Gamma_0(p)$ with

   $$
   E_p(q)=\frac{p-1}{24}
   +\sum_{m\geq1}\left(\sum_{\substack{d\mid m\\p\nmid d}}d\right)q^m.
   $$

2. Its cusp constants are $(p-1)/24$ and $-(p-1)/24$ in Fricke-compatible frames, and $E_p|W_p=-E_p$.

3. It has Hecke eigenvalues

   $$
   T_\ell E_p=(1+\ell)E_p\quad(\ell\neq p),
   \qquad U_pE_p=E_p.
   $$

4. For an integer $m\geq1$, there is a unique normalized cusp form modulo $m$ whose complete q-expansion is congruent to the nonconstant expansion of $E_p$ if and only if $m\mid n_p$.

5. The Eisenstein ideal has exact quotient and index

   $$
   \mathbb T/I\simeq\mathbf Z/n_p\mathbf Z,
   \qquad [\mathbb T:I]=n_p.
   $$

6. For every prime $r\mid n_p$, the Eisenstein maximal ideal is $(r,I)$ and its local quotient has $\mathbf Z_r$-length

   $$
   v_r(n_p)=\max\{0,v_r(p-1)-v_r(12)\}.
   $$

**Proof.** Items 1--3 are Propositions 2.1, 2.2, 3.1, and 3.2. Item 4 is Theorem 7.1, whose integral denominator is computed in Theorem 6.1. Item 5 is Theorem 9.1. Tensoring item 5 with $\mathbf Z_r$ proves item 6. $\square$

Every substantial input is now accounted for. Book 113 supplies the good-level all-cusp q-expansion principle, weight-two differential interpretation, good-prime Hecke formula, and finite Sturm certification. It does not supply $U_p$ or bad-level geometry: $U_p$ was defined and checked on the q-lattice in Chapters 1 and 3, while Section 6.3 proved the required level-prime saturation from the two-component normalization. Book 85 supplies the acting-image convention and finite integral algebra language; the particular perfect Hecke--Fourier pairing needed here was proved in Chapter 5. The exact denominator $n_p$, including its two-primary part, was proved in Chapter 6 from the two-cusp Hodge lattice, the Hasse filtration, stabilizer descent, and the explicit bad-level residue lattice.

### 12.2 Hypotheses and boundaries

Several nearby statements are intentionally not being asserted.

The level is prime and the character is trivial. At composite level there are more cusps, several Eisenstein series, old Eisenstein systems, and choices of $U_q$ eigenvalue at every level prime. The quotient need not be governed by one integer.

The weight is two. In higher weight, Bernoulli numbers replace $(p-1)/12$, and the constant-term and integrality analysis has different denominators. In weight two, logarithmic differentials and the two-cusp residue relation are decisive.

The Hecke algebra contains $U_p$ with eigenvalue $1$. Omitting it or choosing the other stabilization changes the ideal. The algebra is the faithful image on the integral cusp lattice, not a formal polynomial algebra and not an algebra acting on all modular forms.

The exact index does not prove multiplicity one at an Eisenstein maximal ideal, Gorensteinness, principality of $I$, freeness of the localized cusp module, or existence of a characteristic-zero cuspidal branch realizing the whole local exponent. Each is a separate structural question.

No fact about the divisor class of $0-\infty$, the rational torsion of a modular Jacobian, specialization at $p$, or a finite subgroup scheme has entered the proof. Those subjects can use Theorem 12.1, but they cannot be used to justify it without circularity.

Finally, the rational constant term alone is not an integral criterion at $2$. The exact denominator is $12$, not $24$, because one divided Hasse-square correction descends through the sign stabilizer and a second does not. Any argument that divides by $2$ without treating this descent loses the level-$17$ congruence modulo $4$ and cannot prove the stated theorem.

### 12.3 Conclusion

The prime-level Eisenstein phenomenon begins with a cancellation. The nonmodular defect of the level-one weight-two series disappears in $G_2(z)-pG_2(pz)$, leaving a genuine form whose coefficients are the divisors prime to $p$. Its two cusp residues are opposite, its good-prime eigenvalues are $1+\ell$, and its level-prime eigenvalue is $1$.

Congruence turns this rational Eisenstein form into cuspidal information, but only after integral structure is respected. At primes at least five the two cusp constants give the full obstruction; at $3$ the Hasse value cannot cancel opposite residues; at $2$ equal and opposite residues coincide and exactly one divided correction survives. Together these calculations produce the denominator $12$ and the exact modulus

$$
n_p=\operatorname{num}\left(\frac{p-1}{12}\right).
$$

The Hecke--Fourier pairing then makes every coefficient into evaluation at an operator. Functionals killed by the Eisenstein ideal are exactly the Eisenstein coefficient line in the cuspidal lattice quotient. Its order is $n_p$, so the algebraic collision has the exact form

$$
\boxed{
\mathbb T/I\simeq\mathbf Z/n_p\mathbf Z.}
$$

This is the complete prime-level bridge from an explicit Eisenstein series to an integral cusp-form congruence and from that congruence to the exact index of the Eisenstein ideal. It is strong enough to feed later geometric arguments and precise enough to show which additional conclusions still require new geometry.
