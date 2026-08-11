# Eisenstein Descent and the Mordell--Weil Group of the Eisenstein Quotient

## Contents

1. [Why Eisenstein descent is a rank argument](#1-why-eisenstein-descent-is-a-rank-argument)
   - [From finite flat torsion to rational points](#11-from-finite-flat-torsion-to-rational-points)
   - [Prime-level notation](#12-prime-level-notation)
   - [The three obstructions](#13-the-three-obstructions)
   - [The proof architecture](#14-the-proof-architecture)
2. [The selected quotient and its Kummer modules](#2-the-selected-quotient-and-its-kummer-modules)
   - [Rational support and the local idempotent](#21-rational-support-and-the-local-idempotent)
   - [The selected Mordell--Weil completion](#22-the-selected-mordell--weil-completion)
   - [Finite-level Kummer maps](#23-finite-level-kummer-maps)
   - [Why saturation is indispensable](#24-why-saturation-is-indispensable)
3. [Flat local conditions away from the level](#3-flat-local-conditions-away-from-the-level)
   - [The integral condition at a good prime](#31-the-integral-condition-at-a-good-prime)
   - [The coefficient prime](#32-the-coefficient-prime)
   - [Primes away from the coefficient](#33-primes-away-from-the-coefficient)
   - [The real place and the dyadic convention](#34-the-real-place-and-the-dyadic-convention)
4. [The strict condition at the level prime](#4-the-strict-condition-at-the-level-prime)
   - [Identity components and component classes](#41-identity-components-and-component-classes)
   - [Strict local Kummer classes](#42-strict-local-kummer-classes)
   - [The component-relaxed condition](#43-the-component-relaxed-condition)
   - [A finite comparison sequence](#44-a-finite-comparison-sequence)
5. [The two atomic Selmer calculations](#5-the-two-atomic-selmer-calculations)
   - [Multiplicative atoms and units](#51-multiplicative-atoms-and-units)
   - [Constant atoms and unramified covers](#52-constant-atoms-and-unramified-covers)
   - [The odd-prime calculation](#53-the-odd-prime-calculation)
   - [The dyadic sign](#54-the-dyadic-sign)
   - [Exact hypotheses of the atomic vanishing](#55-exact-hypotheses-of-the-atomic-vanishing)
6. [Cartesian devissage of strict Selmer groups](#6-cartesian-devissage-of-strict-selmer-groups)
   - [Propagating a local condition](#61-propagating-a-local-condition)
   - [The left-exact Selmer lemma](#62-the-left-exact-selmer-lemma)
   - [Local cartesianness for an admissible flag](#63-local-cartesianness-for-an-admissible-flag)
   - [Strict Eisenstein Selmer vanishing](#64-strict-eisenstein-selmer-vanishing)
   - [Independence of the filtration](#65-independence-of-the-filtration)
7. [The component bound and zero selected rank](#7-the-component-bound-and-zero-selected-rank)
   - [The Kummer-to-component injection](#71-the-kummer-to-component-injection)
   - [Uniformity in the torsion level](#72-uniformity-in-the-torsion-level)
   - [The rank calculation](#73-the-rank-calculation)
   - [From one completion to the rational quotient](#74-from-one-completion-to-the-rational-quotient)
8. [Height theory and finiteness](#8-height-theory-and-finiteness)
   - [Why rank zero is not yet the final sentence](#81-why-rank-zero-is-not-yet-the-final-sentence)
   - [Mordell--Weil finite generation](#82-mordell--weil-finite-generation)
   - [Finiteness of the Eisenstein quotient](#83-finiteness-of-the-eisenstein-quotient)
   - [Isogenies, companions, and quotients](#84-isogenies-companions-and-quotients)
9. [Hecke support of rational torsion](#9-hecke-support-of-rational-torsion)
   - [Good-prime Frobenius](#91-good-prime-frobenius)
   - [The missing coefficient prime](#92-the-missing-coefficient-prime)
   - [The level operator](#93-the-level-operator)
   - [The Eisenstein support theorem](#94-the-eisenstein-support-theorem)
10. [Hecke annihilators without multiplicity one](#10-hecke-annihilators-without-multiplicity-one)
    - [Radicals and Loewy length](#101-radicals-and-loewy-length)
    - [The exact annihilator statement](#102-the-exact-annihilator-statement)
    - [Why one must not replace a power by the ideal](#103-why-one-must-not-replace-a-power-by-the-ideal)
    - [Prime-by-prime form](#104-prime-by-prime-form)
11. [Exceptional levels and boundary cases](#11-exceptional-levels-and-boundary-cases)
    - [Trivial Eisenstein index](#111-trivial-eisenstein-index)
    - [The prime three](#112-the-prime-three)
    - [The full two-primary boundary](#113-the-full-two-primary-boundary)
    - [The level prime](#114-the-level-prime)
    - [What the theorem does not identify](#115-what-the-theorem-does-not-identify)
12. [The Eisenstein descent package](#12-the-eisenstein-descent-package)
    - [Main theorem](#121-main-theorem)
    - [Dependency ledger](#122-dependency-ledger)
    - [Normalization and failure ledger](#123-normalization-and-failure-ledger)
    - [Conclusion](#124-conclusion)

## 1. Why Eisenstein descent is a rank argument

The completed Eisenstein piece built in the preceding stage contains finite flat torsion at every power of an Eisenstein prime. That fact is not itself a theorem about rational points. A finite flat group can have many global torsors, and a compatible tower can support a positive-rank Mordell--Weil group. The task of descent is to show that the Kummer classes of rational points have nowhere to grow.

The decisive distinction is between strict identity-component conditions and
relaxed point conditions. At the level prime, their difference is measured
by the finite Néron component group. At the prime $2$, an arbitrary real
point may also occupy a nonidentity real component, giving a second finite
defect. We shall prove that the strict global Selmer group of every selected
Eisenstein torsion level is zero. It follows that a global Kummer class is
determined by these finite component defects. Since their groups are fixed
while the torsion level tends to infinity, the Kummer groups stay uniformly
bounded. A positive free rank would make them grow without bound. This
contradiction is the algebraic heart of the argument.

### 1.1 From finite flat torsion to rational points

Let $A$ be an abelian variety over $\mathbf Q$. For an integer $m\geq2$, Kummer theory gives

$$
0\longrightarrow A(\mathbf Q)/mA(\mathbf Q)
\longrightarrow H^1(\mathbf Q,A[m]). \tag{1.1}
$$

The right side is much too large unless local conditions are imposed. At a prime of good reduction the class of a rational point extends over the valuation ring. At the bad level prime it comes from a local point of the Néron model, and its only failure to come from the identity component is a finite component class. These observations put the image of (1.1) in a Selmer group.

Suppose for the moment that a fixed finite group $D$ admits injections

$$
A(\mathbf Q)/\ell^rA(\mathbf Q)\hookrightarrow D/\ell^rD
\qquad(r\geq1). \tag{1.2}
$$

If $A(\mathbf Q)$ is finitely generated of rank $d$, then

$$
\# A(\mathbf Q)/\ell^rA(\mathbf Q)
=\ell^{rd}\# A(\mathbf Q)[\ell^r]. \tag{1.3}
$$

The right side of (1.2) is bounded independently of $r$, so (1.3) forces
$d=0$. The entire book is devoted to constructing the selected version of
(1.2), with $D$ the appropriate part of the level-prime component group
together with the real component group when $\ell=2$, and to proving every
integral hypothesis needed for it.

The quantifier “for every $r$” is decisive. A single finite-level descent can
show that $A(\mathbf Q)/\ell A(\mathbf Q)$ is small, but a free group of any
rank has a finite quotient modulo $\ell$. Rank is detected only by the linear
growth of the exponent in (1.3). The exact torsion tower supplies all $r$,
and the component comparison supplies a bound which does not grow with $r$.

There are two ways a proof could fail at this first step. If the target had
order $O(\ell^{cr})$ for some $c>0$, one would obtain only a rank bound
$d\leq c$. If the maps had kernels of growing order, one could not compare
growth at all. Strict vanishing produces injections into one fixed finite
target and avoids both failures.

The argument is performed on $A_{\mathfrak m}$ rather than on all of $J$.
The full Jacobian contains many non-Eisenstein factors of positive rank, so
no global rank-zero statement for $J$ is expected. Selection isolates the
rational simple factors detected by the chosen Eisenstein completion. The
rational-support argument of Section 7.4 will then show that zero rank on the
completed summand detects zero rank on exactly that rational quotient.

### 1.2 Prime-level notation

Let $N$ be prime and set

$$
U=\operatorname{Spec}\mathbf Z[1/N],
\qquad
n_N=\operatorname{num}\left(\frac{N-1}{12}\right)
=\frac{N-1}{\gcd(N-1,12)}. \tag{1.4}
$$

Let $J=J_0(N)$ and let $\mathbb T$ be the faithful Hecke algebra generated by $T_q$ for primes $q\ne N$ and by $U_N$. Its Eisenstein ideal is

$$
I=(T_q-(1+q):q\ne N)+(U_N-1). \tag{1.5}
$$

The exact index and the cusp--component calculation are

$$
\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z, \tag{1.6}
$$

$$
\langle[0]-[\infty]\rangle
\xrightarrow{\sim}\Phi_N(J)
\simeq\mathbf Z/n_N\mathbf Z. \tag{1.7}
$$

Fix a prime $\ell\mid n_N$ and put

$$
\mathfrak m=(\ell,I),
\qquad e=v_\ell(n_N). \tag{1.8}
$$

Then $\ell\ne N$. Let $A=A_{\mathfrak m}$ be the selected optimal Eisenstein quotient of $J$ and let $e_{\mathfrak m}$ be the idempotent selecting the complete local factor of $\mathbb T\otimes\mathbf Z_\ell$. To keep the notation readable, write $\varepsilon=e_{\mathfrak m}$. Over $U$, let $\mathcal A$ be the abelian scheme obtained from the Néron model of $A$, and put

$$
G_r=\varepsilon\mathcal A[\ell^r]
\qquad(r\geq1). \tag{1.9}
$$

The preceding book proves that $G_r$ is finite flat over $U$, that

$$
0\longrightarrow G_r\longrightarrow G_{r+s}
\xrightarrow{\ell^r}G_s\longrightarrow0 \tag{1.10}
$$

is fppf exact, and that every $G_r$ has a filtration by

$$
\underline{\mathbf Z/\ell\mathbf Z}
\quad\text{and}\quad
\mu_\ell. \tag{1.11}
$$

At $\ell=2$ the factors in (1.11) are labeled by their integral connectedness after closure, not by their identical generic characters.

The numerator in (1.4) is not cosmetic. If $\ell\geq5$, then
$v_\ell(n_N)=v_\ell(N-1)$. At $3$ one power is removed, and at $2$ two
powers are removed. Those losses agree simultaneously in three places: the
constant term obstruction in the Eisenstein Fourier series, the exact order
of the rational cusp difference, and the order of the component group at
$N$. Using $(N-1)/12$ as a rational number or using $N-1$ as an integral
order would destroy that agreement.

The operator $U_N$ is part of the faithful algebra and part of the ideal.
At prime level there is no separate $T_N$ generator. Thus the relation at the
level is $U_N-1$, whereas for every $q\ne N$ it is
$T_q-(1+q)$. This distinction will reappear in Chapter 9, where $T_p$ at a
coefficient prime is recovered from good reduction but $U_N$ is recovered
from the prime-level sign lemma.

Equation (1.7) supplies more than a group order. It fixes the orientation
$[0]-[\infty]$, the specialization map, and the Hecke sign on components.
The quotient $A$ may have a smaller or differently presented component
group, so descent later uses its actual image $D_N(A)$. Nevertheless the
calculation for $J$ is what normalizes the selected maximal ideal and the
finite-flat tower from which $A$ is constructed.

### 1.3 The three obstructions

Three possible shortcuts would make the proof false.

First, the rational projector defining $A$ is not the integral idempotent $\varepsilon$. A coefficient field can have several primes above $\ell$. The rational quotient retains every conjugate prime, while $\varepsilon$ selects one completed factor. The saturation theorem is what lets us compare their integral Tate lattices exactly.

Second, a filtration by the two groups in (1.11) is not a direct sum. Mixed extensions are measured, for odd $\ell$, by the level unit $N$:

$$
\operatorname{Ext}^1_U
(\underline{\mathbf Z/\ell\mathbf Z},\mu_\ell)
\simeq\langle[N]\rangle. \tag{1.12}
$$

At $2$ there are also a sign and a carry. Descent must remove the level-unit residue without splitting the coefficient group.

Third, vanishing of a strict Selmer group does not mean that every local point belongs to the identity component at $N$. The quotient by the identity component is the Néron component group. It is finite but generally nonzero, and it is exactly the finite error that remains in (1.2).

At $2$, the third obstruction has an archimedean manifestation as well. The
positive real condition is needed to kill the multiplicative sign atom, but
a rational point can lie outside $A(\mathbf R)^0$. The correct response is
not to relax the atomic calculation. It is to keep the strict condition
positive and put the finite group $\pi_0(A(\mathbf R))$ into the relaxed
error term. This separation is carried out in Sections 3.4 and 4.4.

These obstructions are logically independent. Saturation concerns the
coefficient lattice, nonsplitting concerns the internal extension structure
of that lattice, and components concern local point groups. Solving one does
not solve either of the others.

### 1.4 The proof architecture

The logical chain is

$$
\begin{array}{c}
G_r\text{ finite flat and admissible over }U\\
\Downarrow\\
\text{flat local conditions away from }N
\text{ and the identity-component condition at }N\\
\Downarrow\\
\text{strict atomic Selmer groups vanish}\\
\Downarrow\ \text{cartesian devissage}\\
\operatorname{Sel}^{\mathrm{str}}(G_r)=0\\
\Downarrow\\
\varepsilon A(\mathbf Q)/\ell^r
\hookrightarrow\text{a quotient of the fixed component group at }N\\
\Downarrow\\
\operatorname{rank}_{\mathbf Z_\ell}
\varepsilon(A(\mathbf Q)\otimes\mathbf Z_\ell)=0\\
\Downarrow\ \text{rational support and heights}\\
A(\mathbf Q)\text{ is finite}.
\end{array} \tag{1.13}
$$

Only after finiteness is proved do we study the Hecke support of the remaining torsion. We shall obtain an Eisenstein radical-annihilator statement. We will not replace it by the stronger assertion $IA(\mathbf Q)=0$, because such an assertion requires additional multiplicity or cross-homomorphism control not present in the dependency package.

The architecture is algebraic at every stage. The Eisenstein Fourier series
enters through its integral congruence index and the level-operator sign; it
is not used to evaluate an $L$-value. Heights enter only after rank has been
forced to zero, through the general finite-generation theorem for abelian
varieties. This division keeps the argument confined to the selected
Eisenstein quotient and does not import a rank theorem for unrelated modular
factors.

## 2. The selected quotient and its Kummer modules

The local idempotent acts naturally on $\ell$-adic objects, while rational points form an ordinary finitely generated abelian group. This chapter constructs the exact bridge between them. The saturation theorem from the completed piece is the reason no finite-index error occurs.

### 2.1 Rational support and the local idempotent

The rational Hecke algebra is a product of number fields. Let $E\in\mathbb T_{\mathbf Q}$ be the sum of the primitive rational idempotents whose scalar extension has a prime belonging to $\mathfrak m$. The optimal quotient $A$ is defined by the connected kernel complementary to $E$. The completed idempotent satisfies

$$
\varepsilon E=\varepsilon, \tag{2.1}
$$

but in general $\varepsilon\ne E\otimes1$.

The quotient map $\pi:J\to A$ has connected kernel. At the level of $\ell$-adic Tate modules, the saturation theorem gives

$$
\varepsilon T_\ell J\xrightarrow{\sim}\varepsilon T_\ell A. \tag{2.2}
$$

Reducing (2.2) modulo $\ell^r$ identifies the generic fiber of (1.9) with the selected direct factor of $A[\ell^r]$. The finite-flat comparison over $U$ strengthens this to

$$
G_r\xrightarrow{\sim}\varepsilon\mathcal A[\ell^r]. \tag{2.3}
$$

We henceforth use (2.3) without changing notation.

To make the support construction explicit, write the rational Hecke algebra,
after dividing by its annihilator on $J$, as

$$
\mathbb T_{\mathbf Q}=K_1\times\cdots\times K_t. \tag{2.3a}
$$

A maximal ideal of $\mathbb T\otimes\mathbf Z_\ell$ determines pairs
$(i,\lambda)$ with $\lambda$ a place of $K_i$ above $\ell$. The completed
idempotent $\varepsilon$ is the characteristic function of the selected
pairs. A rational idempotent must be constant on all places of each $K_i$,
so $E$ retains precisely those $K_i$ for which at least one selected pair
occurs. This proves $\varepsilon E=\varepsilon$ and explains why
$\varepsilon$ need not equal the scalar extension of $E$.

The connectedness of the optimal kernel has two roles. It makes $A$ an
abelian variety, and it makes the image lattice primitive inside rational
homology. Primitivity becomes saturation after completion. If two lattices
inside the same rational space differ by nonzero $\ell$-power index, their
reductions modulo $\ell^r$ differ at every sufficiently large level.
Equation (2.2) asserts that this defect is absent on the selected factor.

### 2.2 The selected Mordell--Weil completion

The Hecke action on $A$ makes $A(\mathbf Q)$ a module over the image of $\mathbb T$ in $\operatorname{End}(A)$. Put

$$
M_\ell=A(\mathbf Q)\otimes_{\mathbf Z}\mathbf Z_\ell. \tag{2.4}
$$

The tensor product in (2.4) retains the free part and the $\ell$-primary torsion and kills torsion prime to $\ell$. The continuous algebra $\mathbb T\otimes\mathbf Z_\ell$ acts on it. Define

$$
M_{\mathfrak m}=\varepsilon M_\ell. \tag{2.5}
$$

This definition does not require $\varepsilon$ to be a rational endomorphism. At finite level $\varepsilon$ acts through the finite ring $\mathbb T/\ell^r\mathbb T$, and

$$
M_{\mathfrak m}/\ell^rM_{\mathfrak m}
=\varepsilon\bigl(A(\mathbf Q)/\ell^rA(\mathbf Q)\bigr). \tag{2.6}
$$

To verify (2.6), first use it for a finitely generated free module, where an idempotent gives a direct-sum decomposition, and then for a finite $\ell$-group, where both sides are obtained levelwise. Passing to the direct sum of the free and finite parts proves the formula.

For a finitely generated abelian group $M$ there is a compatible inverse
limit description

$$
M\otimes\mathbf Z_\ell\simeq\varprojlim_r M/\ell^rM. \tag{2.6a}
$$

Since $\varepsilon$ is an actual idempotent in the completed algebra, it
commutes with this limit and gives

$$
M_{\mathfrak m}\simeq
\varprojlim_r\varepsilon(A(\mathbf Q)/\ell^rA(\mathbf Q)). \tag{2.6b}
$$

Thus all finite Kummer sources come from one compact module. If
$A(\mathbf Q)\simeq\mathbf Z^d\oplus T$, then explicitly

$$
A(\mathbf Q)\otimes\mathbf Z_\ell
\simeq\mathbf Z_\ell^d\oplus T[\ell^\infty]. \tag{2.6c}
$$

The selected rational $\ell$-power torsion is retained. Later, only the free
summand can cause unbounded growth.

### 2.3 Finite-level Kummer maps

The multiplication sequence on $A$ gives

$$
0\longrightarrow A[\ell^r]\longrightarrow A
\xrightarrow{\ell^r}A\longrightarrow0. \tag{2.7}
$$

Taking fppf cohomology over $\mathbf Q$ yields the injective Kummer map

$$
\delta_r:A(\mathbf Q)/\ell^rA(\mathbf Q)
\hookrightarrow H^1(\mathbf Q,A[\ell^r]). \tag{2.8}
$$

Every Hecke operator commutes with multiplication, so (2.8) is Hecke equivariant. Applying $\varepsilon$ and using (2.3) gives

$$
\boxed{
\delta_{\mathfrak m,r}:
M_{\mathfrak m}/\ell^rM_{\mathfrak m}
\hookrightarrow H^1(\mathbf Q,G_r).}
\tag{2.9}
$$

Concretely, if $P$ represents a class in the source and $Q\in A(\overline{\mathbf Q})$ satisfies $\ell^rQ=P$, then

$$
\delta_{\mathfrak m,r}(P)(\sigma)
=\varepsilon(\sigma Q-Q). \tag{2.10}
$$

Changing $Q$ changes (2.10) by a coboundary. Changing a lift of $\varepsilon$ modulo $\ell^r$ changes nothing because the action on $A[\ell^r]$ already factors through the finite Hecke quotient.

Applying the idempotent has not weakened injectivity. Indeed, an idempotent
decomposes both source and target into direct summands, and the Hecke
equivariance of (2.8) maps the selected source into the selected target. The
restriction of an injective map to a direct summand remains injective.

The maps also respect the torsion tower. If $s\leq r$ and
$\ell^rQ=P$, then $\ell^{r-s}Q$ is an $\ell^s$-division point of $P$.
Consequently reduction through $G_r\to G_s$ sends
$\delta_{\mathfrak m,r}(P)$ to $\delta_{\mathfrak m,s}(P)$. This
compatibility confirms that the varying Kummer classes measure successive
quotients of the one module (2.6b).

### 2.4 Why saturation is indispensable

Suppose (2.2) were known only after tensoring with $\mathbf Q_\ell$. Then the integral lattices could differ by a finite index. At level $r$ the putative comparison could have a kernel or cokernel of bounded but nonzero order. Such an error is harmless for rational representations and fatal for descent: it can create or remove Kummer classes at exactly the prime being studied.

The connected optimal kernel eliminates that error. Its selected Tate module is zero, not merely torsion:

$$
\varepsilon T_\ell(\ker\pi)=0. \tag{2.11}
$$

Consequently (2.9) uses the actual finite-flat group $G_r$. No isogenous replacement, denominator cancellation, or unproved flat kernel lies between a rational point and its coefficient group.

A rational isogeny between coefficient representations would give only
finite kernels and cokernels on integral lattices. Such bounded errors can be
harmless for some rank comparisons, but they are fatal for strict vanishing:
an order-$\ell$ error is itself an atomic Selmer coefficient. Saturation
removes the error before local conditions are defined, ensuring that the
local Kummer image and the finite-flat local image refer to the same group.

## 3. Flat local conditions away from the level

At every finite prime $v\ne N$, the selected quotient has good reduction. A Kummer class of a local point is therefore integral. At the coefficient prime, integrality must be understood in flat cohomology; ordinary unramified cohomology is too small. This chapter fixes the local condition in a form compatible with finite-flat filtrations.

### 3.1 The integral condition at a good prime

Let $v\ne N$ be finite. Write $\mathcal O_v=\mathbf Z_v$, and let $\mathcal A_v$ and $G_{r,v}$ be the base changes of $\mathcal A$ and $G_r$. Define

$$
H^1_f(\mathbf Q_v,G_r)
=\operatorname{im}\left(
H^1_{\mathrm{fppf}}(\mathcal O_v,G_{r,v})
\longrightarrow H^1(\mathbf Q_v,G_r)
\right). \tag{3.1}
$$

The multiplication sequence over the abelian scheme is fppf exact. Moreover

$$
H^1(\mathcal O_v,\mathcal A_v)=0. \tag{3.2}
$$

Indeed, a torsor under $\mathcal A_v$ is smooth and proper. Its special fiber is a torsor under a connected algebraic group over a finite field, hence has a rational point by Lang's theorem; smooth henselian lifting gives an $\mathcal O_v$-point. Therefore the integral boundary identifies

$$
\mathcal A_v(\mathcal O_v)/\ell^r\mathcal A_v(\mathcal O_v)
\xrightarrow{\sim}H^1(\mathcal O_v,\mathcal A_v[\ell^r]). \tag{3.3}
$$

Properness gives $\mathcal A_v(\mathcal O_v)=A(\mathbf Q_v)$. Applying the idempotent shows that the localization of (2.9) belongs to (3.1).

The proof of (3.2) contains all the geometry needed here. A class is
represented by a smooth proper torsor $X$ under $\mathcal A_v$. Its special
fiber is a torsor under the connected group
$\mathcal A_{v,\mathbf F_v}$. Lang's theorem makes that torsor trivial over
$\mathbf F_v$. Smooth henselian lifting then raises a special-fiber point to
an $\mathcal O_v$-point, which trivializes $X$. Properness, through the
valuative criterion, is separately responsible for the equality of local
and integral point groups.

If $H'\subset H$ are finite flat over $\mathcal O_v$, functoriality gives a
commutative square from $H^1(\mathcal O_v,H')$ to
$H^1(\mathcal O_v,H)$ and from their generic-fiber cohomology groups. Hence
the image of an integral class stays integral under subquotient maps. This
simple observation will ensure that every quotient atom of an admissible
flag receives a local condition contained in its standard flat condition.

### 3.2 The coefficient prime

At $v=\ell$, the group $G_r$ need not be étale. Its multiplicative factors have connected special fiber, and principal units contribute to Kummer cohomology. Definition (3.1) retains this information.

For the two atoms it reads

$$
H^1_f(\mathbf Q_\ell,\mu_{\ell^a})
=\mathbf Z_\ell^\times/\mathbf Z_\ell^{\times\ell^a}, \tag{3.4}
$$

and

$$
H^1_f(\mathbf Q_\ell,\underline{\mathbf Z/\ell^a\mathbf Z})
=H^1_{\mathrm{et}}(\mathbf Z_\ell,
\mathbf Z/\ell^a\mathbf Z). \tag{3.5}
$$

Formula (3.4) is flat Kummer theory. Formula (3.5) classifies finite étale cyclic covers of $\mathbf Z_\ell$. Neither may be replaced by the raw inertia kernel on geometric points when $a>0$ and the group scheme is not étale.

Concretely,

$$
H^1(\mathbf Q_\ell,\mu_{\ell^a})
=\mathbf Q_\ell^\times/\mathbf Q_\ell^{\times\ell^a}. \tag{3.5a}
$$

Write a representative as $x=\ell^nu$ with
$u\in\mathbf Z_\ell^\times$. It lies in the integral subgroup exactly when
$n$ is divisible by $\ell^a$; after changing $x$ by an $\ell^a$-th power,
it is represented by the unit $u$. Principal units can still give nonzero
classes. Thus the integral condition is richer than the statement that a
geometric character has trivial inertia.

For a constant atom, a torsor over $\mathbf Z_\ell$ is finite etale. Its
generic character is unramified, and every unramified character extends
uniquely over the henselian base. Cartier duality exchanges the two
coefficient group schemes, but the descent below does not infer an
orthogonality theorem from that fact.  What it uses is only functoriality:
maps in an admissible finite-flat sequence carry integral torsors to
integral torsors.  Thus induced quotient conditions are contained in the
standard conditions (3.4) and (3.5).  No local-flat duality theorem, and no
surjectivity on $H^1$, is needed.

### 3.3 Primes away from the coefficient

If $v\ne N,\ell$, then $G_r$ is finite étale over $\mathbf Z_v$. The integral condition equals the unramified subgroup:

$$
H^1_f(\mathbf Q_v,G_r)
=H^1_{\mathrm{ur}}(\mathbf Q_v,G_r). \tag{3.6}
$$

This is the equivalence between finite étale torsors over a henselian DVR and torsors over its residue field. If arithmetic Frobenius is $F_v$, then for an unramified finite module $H$,

$$
H^1_f(\mathbf Q_v,H)
\simeq H/(F_v-1)H. \tag{3.7}
$$

The arithmetic normalization in (3.7) agrees with the convention used in the Hecke polynomial

$$
F_v^2-T_vF_v+v=0. \tag{3.8}
$$

Switching to geometric Frobenius would invert $F_v$ and would require changing every later polynomial simultaneously.

For a fixed global class, all but finitely many localizations are unramified
automatically. The Selmer condition nevertheless quantifies over every
place: it rules out the finitely many accidental ramification primes. On the
two atoms, (3.6) has elementary forms. A multiplicative Kummer representative
$x$ must satisfy

$$
v(x)\equiv0\pmod\ell, \tag{3.8a}
$$

while a constant cyclic character must be unramified. These are precisely
the valuation and covering conditions used in Chapter 5.

### 3.4 The real place and the dyadic convention

For odd $\ell$, positive-degree cohomology at $\mathbf R$ vanishes on $\ell$-primary coefficients. No real local condition is needed. At $\ell=2$, put

$$
H^1_+(\mathbf R,H)=H^1(\mathbf R,H)
=\widehat H^1(\operatorname{Gal}(\mathbf C/\mathbf R),H). \tag{3.9}
$$

The **positive strict condition** is zero. In multiplicative Kummer coordinates this excludes the sign class $[-1]$:

$$
\mathbf R^\times/\mathbf R^{\times2}
=\{[1],[-1]\},
\qquad H^1_{\mathrm{str}}(\mathbf R,\mu_2)=0. \tag{3.10}
$$

This is not an arbitrary narrowing. The connected compact Lie group
$A(\mathbf R)^0$ is divisible, so multiplication by $2^r$ is surjective on
it and its Kummer image is zero. Thus (3.10) is the condition coming from the
real identity component. An arbitrary rational point can occupy a different
real component; that finite defect will be admitted in the relaxed condition
and bounded just as the component defect at $N$ is bounded. More invariantly,
the real condition is paired with itself through the modified local duality
convention, so it remains cartesian in the dyadic devissage of Chapter 6.

## 4. The strict condition at the level prime

The level prime is the only finite prime omitted from $U$. The selected quotient has semistable reduction there, not good reduction. Its Néron model separates local points into an identity-component part, which behaves integrally, and a finite component part. Descent uses both, but never confuses them.

### 4.1 Identity components and component classes

Let $\mathcal A_N/\mathbf Z_N$ be the Néron model of $A_{\mathbf Q_N}$. Write

$$
\mathcal A_N^0
\subseteq\mathcal A_N
\quad\text{and}\quad
\Phi_N(A)=\mathcal A_{N,\mathbf F_N}/\mathcal A^0_{N,\mathbf F_N}. \tag{4.1}
$$

The Néron property gives

$$
A(\mathbf Q_N)=\mathcal A_N(\mathbf Z_N), \tag{4.2}
$$

and reduction gives an exact sequence

$$
0\longrightarrow\mathcal A_N^0(\mathbf Z_N)
\longrightarrow A(\mathbf Q_N)
\xrightarrow{\operatorname{comp}_N}
\Phi_N(A)(\mathbf F_N). \tag{4.3}
$$

Surjectivity at the right is not needed. Denote the actual image by

$$
D_N(A)=\operatorname{im}(\operatorname{comp}_N). \tag{4.4}
$$

This is a finite group. Its selected part

$$
D_{\mathfrak m,N}=\varepsilon(D_N(A)\otimes\mathbf Z_\ell) \tag{4.5}
$$

is therefore a finite $\mathbf Z_\ell$-module. The rank argument needs only this finiteness; no unsupported surjectivity from $J(\mathbf Q_N)$ to $A(\mathbf Q_N)$ will be used.

The distinction between $\Phi_N(A)(\mathbf F_N)$ and its actual image is
minor for finiteness and major for correctness. The component group is
defined geometrically on the special fiber. A local point produces a
rational component, but not every rational component must lift through the
reduction map for an arbitrary quotient model. Defining $D_N(A)$ as the
image makes (4.3) right exact by definition and gives every later snake-lemma
map its precise target.

Hecke correspondences extend to the Néron model and preserve its identity
component. They therefore act on the component quotient and on the image of
local points. Tensoring with $\mathbf Z_\ell$ in (4.5) discards component
torsion prime to $\ell$, which no $\ell^r$-Kummer map could detect.

### 4.2 Strict local Kummer classes

The **strict local Kummer subgroup** is

$$
L_N^{\mathrm{str}}(G_r)
=\operatorname{im}\left(
\varepsilon\mathcal A_N^0(\mathbf Z_N)/\ell^r
\longrightarrow H^1(\mathbf Q_N,G_r)
\right). \tag{4.6}
$$

Here the boundary is computed on the generic fiber. The notation does not assert that the whole $G_r$ extends as torsion of an abelian scheme over $\mathbf Z_N$. Semistable identity-component theory supplies the boundary on the semiabelian identity group, and the selected finite subgroup is obtained by intersection with the generic coefficient group.

Because $\ell\ne N$, multiplication by $\ell^r$ on the toric and abelian parts of $\mathcal A_N^0$ is étale. On each order-$\ell$ constant or multiplicative constituent, (4.6) propagates to the unramified subgroup. For $\mu_\ell$, this means that a Kummer class has $N$-adic valuation divisible by $\ell$; for the constant atom, it means that the corresponding character is unramified at $N$.

For a split torus this follows from
$\mathbf Q_N^\times/\mathbf Q_N^{\times\ell^r}$: points of the identity
model have valuation zero, so their Kummer classes are represented by units.
For the abelian part, good reduction gives the integral calculation of
Section 3.1. Passing to an unramified splitting field and descending proves
the assertion for a nonsplit torus.

We need only containment in the unramified atomic condition. A boundary in a
nonsplit semiabelian extension may make an induced quotient condition
smaller. That is harmless because the atomic Selmer group for the larger
unramified condition already vanishes.

### 4.3 The component-relaxed condition

The full local Kummer subgroup is

$$
L_N^{\mathrm{rel}}(G_r)
=\operatorname{im}\left(
\varepsilon A(\mathbf Q_N)/\ell^rA(\mathbf Q_N)
\longrightarrow H^1(\mathbf Q_N,G_r)
\right). \tag{4.7}
$$

Clearly

$$
L_N^{\mathrm{str}}(G_r)
\subseteq L_N^{\mathrm{rel}}(G_r). \tag{4.8}
$$

The quotient is controlled by components. Applying the snake lemma to multiplication by $\ell^r$ in (4.3) gives an injection

$$
L_N^{\mathrm{rel}}(G_r)/L_N^{\mathrm{str}}(G_r)
\hookrightarrow D_{\mathfrak m,N}/\ell^rD_{\mathfrak m,N}. \tag{4.9}
$$

The relaxed condition is necessary even when the component group is cyclic.
A point whose component has exact order $\ell^a$ cannot be moved into the
identity component by subtracting an $\ell^r$-multiple unless its component
is divisible by $\ell^r$. Formula (4.9) says that this failure of strictness
is recorded faithfully by the finite component quotient and nowhere else.

Let us verify the only subtle point. If the Kummer class of $P\in A(\mathbf Q_N)$ belongs to the strict image, choose $P_0\in\mathcal A_N^0(\mathbf Z_N)$ with the same boundary. Kummer injectivity says

$$
P-P_0\in\ell^rA(\mathbf Q_N).
$$

Therefore the component of $P$ is divisible by $\ell^r$ in $D_N(A)$. This proves injectivity in (4.9). No assertion about all geometric components is required.

Equivalently, the snake-lemma calculation starts from the diagram

$$
\begin{array}{ccccccccc}
0&\longrightarrow&\mathcal A_N^0(\mathbf Z_N)&\longrightarrow&A(\mathbf Q_N)
&\longrightarrow&D_N(A)&\longrightarrow&0\\
&&\downarrow\ell^r&&\downarrow\ell^r&&\downarrow\ell^r&&\\
0&\longrightarrow&\mathcal A_N^0(\mathbf Z_N)&\longrightarrow&A(\mathbf Q_N)
&\longrightarrow&D_N(A)&\longrightarrow&0.
\end{array} \tag{4.9a}
$$

Taking cokernels gives a map from the quotient of full local points by the
quotient of identity-component points to $D_N(A)/\ell^rD_N(A)$. The Kummer
map identifies the former quotient with
$L_N^{\mathrm{rel}}/L_N^{\mathrm{str}}$ after dividing out the common
kernel. This proves (4.9) directly and shows why only the actual image
$D_N(A)$, rather than every geometric component, appears.

The order of $D_{\mathfrak m,N}$ is independent of $r$. It may be smaller
than the selected part of $\Phi_N(J)$ because passage to an optimal quotient
can change component groups. The descent requires no equality with
$\mathbf Z/n_N\mathbf Z$; that cyclic calculation motivates the selected
support and supplies the original Eisenstein normalization, while (4.4)
gives the exact finite error for $A$.

### 4.4 A finite comparison sequence

Define the strict Selmer group by

$$
\operatorname{Sel}^{\mathrm{str}}(G_r)
=\left\{c\in H^1(\mathbf Q,G_r):
\begin{array}{l}
c_v\in H^1_f(\mathbf Q_v,G_r)\quad(v\ne N,\infty),\\
c_N\in L_N^{\mathrm{str}}(G_r),\\
c_\infty=0\quad\text{if }\ell=2
\end{array}
\right\}. \tag{4.10}
$$

When $\ell=2$, define

$$
D_{\mathfrak m,\infty}
=\varepsilon\bigl(\pi_0(A(\mathbf R))\otimes\mathbf Z_2\bigr). \tag{4.11}
$$

It is a finite elementary $2$-group. The full real Kummer image modulo the
strict zero image injects into
$D_{\mathfrak m,\infty}/2^rD_{\mathfrak m,\infty}$, by the same argument as
(4.9), using the exact sequence
$0\to A(\mathbf R)^0\to A(\mathbf R)\to\pi_0(A(\mathbf R))\to0$.
For odd $\ell$, put $D_{\mathfrak m,\infty}=0$.

The component-relaxed Selmer group
$\operatorname{Sel}^{\mathrm{rel}}(G_r)$ is defined by replacing the
condition at $N$ with (4.7) and, when $\ell=2$, replacing the strict real
condition by the full real Kummer image. Changing these finitely many local
conditions gives an exact sequence

$$
0\longrightarrow\operatorname{Sel}^{\mathrm{str}}(G_r)
\longrightarrow\operatorname{Sel}^{\mathrm{rel}}(G_r)
\longrightarrow
\left(L_N^{\mathrm{rel}}(G_r)/L_N^{\mathrm{str}}(G_r)\right)
\oplus L_\infty^{\mathrm{rel}}(G_r). \tag{4.12}
$$

The final arrow need not be surjective. Combining (4.9), the real component
comparison following (4.11), and (4.12), once strict vanishing is proved,
will give

$$
\operatorname{Sel}^{\mathrm{rel}}(G_r)
\hookrightarrow
\left(D_{\mathfrak m,N}/\ell^rD_{\mathfrak m,N}\right)
\oplus
\left(D_{\mathfrak m,\infty}/\ell^rD_{\mathfrak m,\infty}\right). \tag{4.13}
$$

This is the finite target promised in the introduction.

For completeness, exactness in (4.12) is a localization argument. A strict
class is certainly relaxed. A relaxed class maps to zero in both quotient
local conditions exactly when its localization at $N$ is strict and, in the
dyadic case, its real localization is zero. All its other local conditions
were unchanged, so it is a strict Selmer class. Surjectivity at the final
term would require solving a global localization problem and is neither
known nor used.

The real and level-prime errors play parallel logical roles but arise from
different geometry. The first is the component group of a compact real Lie
group and is killed by $2$; the second is the component group of a
semistable Néron model and may have higher $\ell$-power exponent. Both are
fixed finite groups. Consequently adding the real term repairs the dyadic
Kummer condition without changing the asymptotic rank argument.

## 5. The two atomic Selmer calculations

An admissible finite flat group need not split into its constant and
multiplicative constituents.  Nevertheless, its strict Selmer group can be
studied one constituent at a time.  The base of that induction is an explicit
calculation over $U=\operatorname{Spec}\mathbf Z[1/N]$.  The calculation is
short, but every local condition matters: the strict condition removes the
power of $N$, and at $2$ the real condition removes the sign.

### 5.1 Multiplicative atoms and units

Flat Kummer theory gives

$$
H^1(U,\mu_{\ell})
=\mathbf Z[1/N]^\times/\mathbf Z[1/N]^{\times\ell}. \tag{5.1}
$$

Since $N$ is prime,

$$
\mathbf Z[1/N]^\times=\{\pm N^a:a\in\mathbf Z\}. \tag{5.2}
$$

There is a useful global reformulation.  A class
$x\in\mathbf Q^\times/\mathbf Q^{\times\ell}$ is integral at every finite
prime $v\ne N$ precisely when

$$
v(x)\equiv0\pmod\ell\qquad(v\ne N). \tag{5.3}
$$

After multiplying by an $\ell$-th power, such a class is represented by
$\pm N^a$.  The strict condition at $N$ is

$$
v_N(x)\equiv0\pmod\ell. \tag{5.4}
$$

It removes $N^a$.  If $\ell$ is odd, the remaining sign is already an
$\ell$-th power because $-1=(-1)^\ell$.  If $\ell=2$, the positive condition
at the real place removes the class of $-1$.  Thus

$$
\operatorname{Sel}^{\mathrm{str}}(\mu_\ell)=0. \tag{5.5}
$$

This argument also explains why the condition at $N$ cannot be omitted.  With
the relaxed condition, the class of $N$ survives.  It is the cohomological
shadow of the component class that descent is designed to isolate.

For example, if $x=N^bu^\ell$ in $\mathbf Q^\times$, all valuations away
from $N$ are divisible by $\ell$. Its strict localization at $N$ is integral
exactly when $\ell\mid b$. Thus the quotient between relaxed and strict
multiplicative conditions records the residue of $b$ modulo $\ell$. The
global calculation removes exactly that residue; it never requires a chosen
$\ell$-th root of the unit part.

### 5.2 Constant atoms and unramified covers

For the constant atom,

$$
H^1(\mathbf Q,\underline{\mathbf Z/\ell\mathbf Z})
=\operatorname{Hom}_{\mathrm{cont}}
(G_{\mathbf Q},\mathbf Z/\ell\mathbf Z). \tag{5.6}
$$

The flat condition at a finite prime says that the character is unramified
there.  The strict condition says the same at $N$.  Hence a strict class is
unramified at every finite prime.

We recall why such a character is zero.  A nonzero character has a cyclic
degree-$\ell$ quotient.  The corresponding number field $K$ is unramified at
every finite prime, so its absolute discriminant is $1$.  Minkowski's theorem
says that a number field of degree $d>1$, with $r_2$ pairs of complex
embeddings, satisfies

$$
|d_K|^{1/2}\geq
\left(\frac{\pi}{4}\right)^{r_2}\frac{d^d}{d!}. \tag{5.7}
$$

The right side is greater than $1$ for $d>1$ after the standard sharpened
form of the convex-body estimate is applied to a nonzero ideal class.  In
particular every nontrivial extension of $\mathbf Q$ has a ramified finite
prime.  Thus $K=\mathbf Q$, a contradiction.  Equivalently, $\mathbf Q$ has
no nontrivial extension unramified at all finite primes.

The torsor in (5.6) need not be connected. If its character is nonzero, its
image is the whole group $\mathbf Z/\ell\mathbf Z$, and a connected component
gives the cyclic degree-$\ell$ field used above. If the character is zero,
the torsor is split. The discriminant proof therefore covers every constant
torsor, not only one assumed connected in advance.

In ideal-theoretic form, Minkowski says that each ideal class of a
degree-$d$ field contains an integral ideal of norm at most

$$
\left(\frac4\pi\right)^{r_2}
\frac{d!}{d^d}\sqrt{|d_K|}. \tag{5.7a}
$$

For a hypothetical nontrivial field with $|d_K|=1$, the sharpened strict
bound yields an integral ideal of norm below $1$, impossible. This is the
quantitative reason an everywhere-unramified nontrivial field cannot occur.

When $\ell=2$, a quadratic character ramified only at the real place would
correspond to a quadratic field of discriminant of absolute value $1$; no
such field exists.  The imposed real condition is nevertheless retained,
because it is the condition propagated by the geometric Kummer problem and
because it treats constant and multiplicative dyadic atoms uniformly.
Consequently

$$
\operatorname{Sel}^{\mathrm{str}}
(\underline{\mathbf Z/\ell\mathbf Z})=0. \tag{5.8}
$$

### 5.3 The odd-prime calculation

For later use it is helpful to record the calculation as a proposition in
which the local hypotheses are visible.

**Proposition 5.1 (odd atomic vanishing).**  Let $\ell$ be odd and
$\ell\ne N$.  Let $H$ be either $\mu_\ell$ or
$\underline{\mathbf Z/\ell\mathbf Z}$.  Impose the flat condition at every
finite $v\ne N$ and the unramified strict condition at $N$.  Then

$$
\operatorname{Sel}^{\mathrm{str}}(H)=0. \tag{5.9}
$$

**Proof.**  For $H=\mu_\ell$, (5.3) makes a global class a level unit and
(5.4) removes its $N$-power; the sign is an $\ell$-th power.  For constant
$H$, every permitted character is everywhere unramified and hence zero by
the discriminant argument above.  These are all cases. $\square$

Notice that the proof does not assume that $N$ is an $\ell$-th power in
$\mathbf Q_N$.  It asserts the opposite sort of fact: the valuation of an
$\ell$-th power is divisible by $\ell$.  The strict valuation condition is
therefore exactly what kills the global generator $[N]$ occurring in the
extension group of admissible finite flat groups.

### 5.4 The dyadic sign

At $\ell=2$, the generic fibers of $\mu_2$ and
$\underline{\mathbf Z/2\mathbf Z}$ are both trivial Galois modules.  Their
closures over $\mathbf Z_2$ are different, so their flat local conditions are
different.  The calculation must be made on those closures.

For $\mu_2$, an integral global class has the form $\pm N^a$.  Strictness at
$N$ makes $a$ even, leaving $\pm1$.  Positivity at infinity leaves $+1$.
For the constant closure, the class is a quadratic character unramified at
every finite prime and hence is zero.  We have proved

**Proposition 5.2 (dyadic atomic vanishing).**  For either integral dyadic
atom, with its flat condition at $2$, its unramified strict condition at $N$,
and the positive condition at infinity,

$$
\operatorname{Sel}^{\mathrm{str}}(H)=0. \tag{5.10}
$$

The sign in the dyadic extension classification does not alter (5.10).  It
describes how two atoms may be glued; it is not an additional class in the
Selmer group of an atom.  The carry occurring in a tower has the same status.
Both phenomena will be retained by devissage rather than discarded by an
imaginary splitting.

### 5.5 Exact hypotheses of the atomic vanishing

The preceding proof establishes a slightly stronger statement than we shall
need.  Suppose a local condition on an atom is contained in the flat
condition away from $N$, contained in the unramified condition at $N$, and,
at $2$, contained in the positive real condition.  Its Selmer group is a
subgroup of the group just computed, and is therefore zero.  Thus quotient
conditions obtained from a nonsplit extension need not fill the standard
atomic local condition.

The calculation uses exactly four inputs:

1. the only allowed bad finite prime is $N$;
2. $\ell\ne N$, so constant and multiplicative closures at $N$ are etale;
3. the strict condition is unramified at $N$; and
4. at $\ell=2$ the real sign is positive.

No class-group term is hidden here.  The ring $\mathbf Z[1/N]$ has trivial
class group, and the constant calculation uses the fact that the ground
field is $\mathbf Q$.  These hypotheses will be checked again when the
atomic result is applied to $G_r$.

We finish the atomic chapter by justifying the passage from local integrality
to cohomology over $U$. For a finite flat group $H/U$, a global generic-fiber
torsor whose localization extends over every $\mathbf Z_v$ with $v\ne N$
extends uniquely over $U$. Normalize $U$ in the finite generic torsor. The
local extensions make the normalization flat at every codimension-one point.
Since $U$ is a regular curve, finite torsion-free modules are locally free,
and normality extends the group action and torsor identity. Thus no
ramification condition is lost between the Selmer definition and (5.1).

For $\mu_\ell$ the class-group sequence is

$$
0\longrightarrow
\mathbf Z[1/N]^\times/\mathbf Z[1/N]^{\times\ell}
\longrightarrow H^1(U,\mu_\ell)
\longrightarrow\operatorname{Pic}(U)[\ell]
\longrightarrow0. \tag{5.11}
$$

Every ideal of $\mathbf Z[1/N]$ is principal, so the last group is zero.
Formula (5.1) is exact, not an omission of a class-group summand. For the
constant atom, purity says that a generic finite etale cover extends over
$U$ exactly when it is unramified at every closed point of $U$. Strictness
adds the missing point $N$, producing an everywhere-unramified cover of
$\operatorname{Spec}\mathbf Z$, which the discriminant argument trivializes.

Although order-$\ell$ atoms suffice, the higher-order pattern is instructive.
For $\mu_{\ell^a}$, strictness makes the exponent of $N$ divisible by
$\ell^a$, and positivity removes the sign when necessary. For the constant
cyclic group of order $\ell^a$, strictness again gives an everywhere-
unramified cyclic extension and hence the zero character. Thus consecutive
identical atoms could be grouped. The order-$\ell$ flag is retained because
it also handles nonsplit mixed extensions.

## 6. Cartesian devissage of strict Selmer groups

The finite flat group $G_r$ generally contains nonsplit extensions.  We now
show that atomic vanishing still forces its strict Selmer group to vanish.
The method is a left-exact induction: map a Selmer class to the final atom,
use atomic vanishing, lift it to the preceding subgroup, and repeat.

### 6.1 Propagating a local condition

Let

$$
0\longrightarrow H'\longrightarrow H\longrightarrow H''
\longrightarrow0 \tag{6.1}
$$

be an exact sequence of finite Galois modules arising as generic fibers of
finite flat groups wherever an integral condition is imposed.  Given a local
subgroup $L_v(H)\subseteq H^1(\mathbf Q_v,H)$, define the propagated
subobject condition by

$$
L_v(H')=
\{x\in H^1(\mathbf Q_v,H'):
x\mapsto L_v(H)\}. \tag{6.2}
$$

Define the quotient condition to be the image of $L_v(H)$ in
$H^1(\mathbf Q_v,H'')$.  With these definitions,

$$
L_v(H')\longrightarrow L_v(H)\longrightarrow L_v(H'') \tag{6.3}
$$

is exact at the middle term.  This elementary condition is the portion of
cartesianness needed below.

If $L_v(H)$ is the image of integral flat cohomology, the quotient condition
is contained in the integral flat condition for $H''$.  Indeed, the map in
cohomology is induced by a map of finite flat groups over $\mathbf Z_v$.
Surjectivity is neither asserted nor needed.  The same observation applies
to the identity-component Kummer condition at $N$.

### 6.2 The left-exact Selmer lemma

**Lemma 6.1 (left-exact devissage).**  In (6.1), use propagated subobject and
quotient conditions at every place.  If
$\operatorname{Sel}(H'')=0$, then every class in
$\operatorname{Sel}(H)$ is the image of a class in
$\operatorname{Sel}(H')$.

**Proof.**  Let $c\in\operatorname{Sel}(H)$.  Its image $c''$ in
$H^1(\mathbf Q,H'')$ satisfies every quotient local condition, so
$c''\in\operatorname{Sel}(H'')$.  It is zero.  The global cohomology sequence
therefore supplies $c'\in H^1(\mathbf Q,H')$ mapping to $c$.  At each place,
the localization of $c'$ maps to the localization of $c$, which lies in
$L_v(H)$.  Formula (6.2) says precisely that $c'_v\in L_v(H')$.  Hence
$c'\in\operatorname{Sel}(H')$. $\square$

The lift $c'$ need not be unique.  Nonuniqueness comes from the boundary of
$H^0(\mathbf Q,H'')$, but every lift that maps to $c$ satisfies (6.2).  Thus
no $H^0$-vanishing or multiplicity-one hypothesis has entered the argument.

The same lemma applies when the quotient local condition is merely contained
in a larger standard condition. If the Selmer group for the larger
conditions is zero, then the smaller quotient Selmer group is zero as well.
This is exactly what (6.5) supplies. Flat cohomology gives an upper bound for
the quotient condition; local surjectivity is unnecessary.

The lemma is genuinely left exact. A short exact sequence of coefficients
rarely produces right exactness for Selmer groups, because a collection of
local quotient classes need not globalize. Our induction never attempts that
operation. It begins with an existing global class and moves that class into
a smaller coefficient group.

### 6.3 Local cartesianness for an admissible flag

Choose an admissible finite-flat flag over $U$,

$$
0=F_0\subset F_1\subset\cdots\subset F_s=G_r,
\qquad Q_i=F_i/F_{i-1}, \tag{6.4}
$$

where every $Q_i$ is $\mu_\ell$ or
$\underline{\mathbf Z/\ell\mathbf Z}$.  Begin with the actual strict local
conditions of $G_r$ and propagate them downward by (6.2).  The induced
quotient conditions on $Q_i$ satisfy the hypotheses of Section 5.5.

At a finite $v\ne N$, this follows from functoriality of
$H^1(\mathbf Z_v,-)$ for the finite-flat exact sequence obtained from (6.4).
At $v=N$, multiplication by $\ell$ is etale on the semiabelian identity
component because $\ell\ne N$.  A constituent of an identity-component
Kummer class is consequently unramified.  At the real place, the dyadic
condition was defined by propagation from the positive identity direction.
These verifications prove

$$
L_v(Q_i)\subseteq
\begin{cases}
H^1_f(\mathbf Q_v,Q_i),&v\ne N,\infty,\\
H^1_{\mathrm{ur}}(\mathbf Q_N,Q_i),&v=N,\\
0,&v=\infty,\ \ell=2.
\end{cases} \tag{6.5}
$$

This is where finite-flat admissibility at every level is essential.  A
generic Jordan--Holder series would not determine the condition at the
coefficient prime, and at $2$ it would not distinguish the two integral
closures.

At the level prime, the identity component of the semistable Néron model has
an exact sequence

$$
0\longrightarrow\mathcal T\longrightarrow\mathcal A_N^0
\longrightarrow\mathcal B\longrightarrow0, \tag{6.5a}
$$

with $\mathcal T$ a torus and $\mathcal B$ an abelian scheme. Since $\ell$
is invertible in $\mathbf Z_N$, multiplication by $\ell$ is etale on both
pieces. Its torsors extend over $\mathbf Z_N$, so their generic characters
are unramified. Passing to a finite-flat subquotient cannot create
ramification. This proves the middle line of (6.5).

At the coefficient prime the integral flag matters even more. A sequence
with a $\mu_\ell$ quotient can have a boundary on principal units, and at
$2$ one generic character has two possible integral closures. Because (6.4)
exists over $U$, every cohomology map uses the correct closure. A quotient
condition may shrink, but Section 5.5 shows that shrinking only strengthens
atomic vanishing.

### 6.4 Strict Eisenstein Selmer vanishing

**Theorem 6.2 (strict vanishing).**  For every $r\geq1$,

$$
\boxed{\operatorname{Sel}^{\mathrm{str}}(G_r)=0.} \tag{6.6}
$$

**Proof.**  Start with a class $c_s$ in the left side.  Map it through
$F_s\twoheadrightarrow Q_s$.  By (6.5), its image belongs to a Selmer group
whose local conditions are contained in the standard atomic strict
conditions.  Section 5.5 makes that group zero.  Lemma 6.1 lifts $c_s$ to a
strict class $c_{s-1}$ with coefficients in $F_{s-1}$.

Repeat.  At stage $i$, atomic vanishing for $Q_i$ and Lemma 6.1 lift the
class to $F_{i-1}$.  After $s$ steps it is a class with coefficients in
$F_0=0$, hence is zero.  Its image in $H^1(\mathbf Q,G_r)$ was the original
class, so that class is zero. $\square$

The proof preserves every extension class in the flag.  For odd $\ell$ the
possible $[N]$-extension is neutralized because the strict local condition
kills the level unit on the quotient atom.  At $2$ the sign and carry remain
inside the propagated subobject conditions; atomic positivity and repeated
left-exact lifting handle them without a splitting assertion.

The induction proves detection rather than decomposition. If a strict class
maps to zero on the final atom, it comes from the preceding subgroup; if its
next atomic image is zero, it moves down again. Eventually it has
coefficients in zero. No direct-sum coordinates on $G_r$ are ever chosen.

The flag length grows with $r$, but no error accumulates because every
atomic group is exactly zero. If atomic groups were merely bounded, repeated
extensions could produce a bound growing with the flag length and hence with
$r$. Exact vanishing is what later makes the component bound uniform.

### 6.5 Independence of the filtration

Different admissible flags can have different intermediate extension
classes.  The group in (6.6), however, was defined before a flag was chosen,
using integral Kummer conditions and the Néron identity component.  A flag
is only a device for proving that this intrinsic group is zero.

More formally, choose either of two admissible flags.  Functoriality gives
(6.5) for each, and the same induction proves that every element of the one
intrinsic group is zero.  There is no comparison isomorphism between the two
lists of intermediate Selmer groups to construct.  This observation also
shows why the result is stable under refinement of a flag.

## 7. The component bound and zero selected rank

Strict vanishing turns the relaxed local conditions into a finite global
bound.  We now apply that bound to Kummer classes of rational points and let
$r$ grow.

### 7.1 The Kummer-to-component injection

The localization of a global Kummer class at every finite $v\ne N$ is
integral by Section 3.1. At $N$ it is in the full local Kummer image (4.7),
and at the real place it is in the full real Kummer image. Therefore (2.9)
factors as

$$
M_{\mathfrak m}/\ell^rM_{\mathfrak m}
\hookrightarrow\operatorname{Sel}^{\mathrm{rel}}(G_r). \tag{7.1}
$$

Combining (7.1), strict vanishing, and the two component comparisons gives

$$
\boxed{
M_{\mathfrak m}/\ell^rM_{\mathfrak m}
\hookrightarrow
\left(D_{\mathfrak m,N}/\ell^rD_{\mathfrak m,N}\right)
\oplus
\left(D_{\mathfrak m,\infty}/\ell^rD_{\mathfrak m,\infty}\right).}
\tag{7.2}
$$

The injection is canonical up to the harmless choice of representing a
local component class.  Its kernel is canonical: a global point maps to zero
exactly when its relaxed Kummer class becomes strict, and Theorem 6.2 then
makes that class zero.

### 7.2 Uniformity in the torsion level

The group on the right of (7.2) is a quotient of the fixed finite group
$D_{\mathfrak m,N}\oplus D_{\mathfrak m,\infty}$. Hence

$$
\#(M_{\mathfrak m}/\ell^rM_{\mathfrak m})
\leq\#D_{\mathfrak m,N}\,\#D_{\mathfrak m,\infty}
\qquad(r\geq1). \tag{7.3}
$$

No compatibility map between the targets for different $r$ is required for
this inequality.  The exact tower (1.10) ensures that all sources use the
same completed lattice, while the component group supplies a single numeric
bound.

Pointwise, if a selected point class is trivial in both component quotients,
then its local Kummer class is strict at every place. Theorem 6.2 makes its
global Kummer class zero, and Kummer injectivity makes the point divisible by
$\ell^r$ in $M_{\mathfrak m}$. Thus two point classes with the same component
data coincide. This is the direct meaning of (7.2).

The component data need not all be realized by global points. Such a claim
would be surjectivity of (7.2), a much stronger local-to-global assertion.
Injectivity and boundedness are sufficient for rank zero.

It is tempting to replace $D_{\mathfrak m,N}$ by the full component group of
$J$.  That replacement may give a convenient upper bound, but it is not
needed and may obscure the behavior of optimal quotients.  The actual image
defined in (4.4) is the precise target supported by the Néron sequence.

### 7.3 The rank calculation

Let a finitely generated $\mathbf Z_\ell$-module $M$ have the form

$$
M\simeq\mathbf Z_\ell^d\oplus T,
\qquad T\text{ finite}. \tag{7.4}
$$

Then

$$
\#(M/\ell^rM)=\ell^{rd}\#(T/\ell^rT). \tag{7.5}
$$

The second factor is at least $1$ and eventually equals $\#T$.  Thus a
uniform bound in $r$ forces $d=0$.  Applying this to (7.3) yields

$$
\operatorname{rank}_{\mathbf Z_\ell}M_{\mathfrak m}=0. \tag{7.6}
$$

The finite generation used here will be supplied in Chapter 8.  There is no
circularity: Chapters 3--7 establish the uniform bound for the abstract
Kummer quotients, and height theory identifies the algebraic structure of
the source afterward.

Equivalently, a hypothetical free direction would contain a primitive
element $x$. Its class modulo $\ell^r$ would have exact order $\ell^r$ for
every $r$, contradicting (7.3). Finite generation guarantees such a lattice
element and excludes pathologies coming from infinitely divisible torsion.

### 7.4 From one completion to the rational quotient

We must still show that (7.6) kills the entire rational rank of $A$, not only
one completed summand.  Let

$$
R=\operatorname{im}(\mathbb T_{\mathbf Q}\to
\operatorname{End}^0(A)). \tag{7.7}
$$

It is a finite product of number fields.  The rational projector defining
$A$ retains precisely the factors $K$ for which at least one place
$\lambda\mid\ell$ lies under the selected maximal ideal.  If
$W=A(\mathbf Q)\otimes\mathbf Q$ were nonzero, then some retained factor
$K$ would act nontrivially on a nonzero summand $W_K$.  Since a nonzero
finite-dimensional $K$-vector space stays nonzero after completion,

$$
W_K\otimes_KK_\lambda\ne0. \tag{7.8}
$$

But this completed space is a summand of
$M_{\mathfrak m}\otimes_{\mathbf Z_\ell}\mathbf Q_\ell$, contradicting
(7.6).  Therefore

$$
A(\mathbf Q)\otimes\mathbf Q=0. \tag{7.9}
$$

This argument is exactly why the rational projector $E$ and the local
idempotent $\varepsilon$ were both retained.  One completion detects every
rational simple factor included in $A$, although it does not equal the
rational projector integrally.

More explicitly, a nonzero vector in $W_K$ spans a nonzero finite-dimensional
$K$-space. Completion $K\to K_\lambda$ is flat and faithful on such spaces,
so the vector remains nonzero after tensoring. The definition of $E$
guarantees that at least one such $\lambda$ belongs to $\varepsilon$.
Therefore rational rank cannot hide at a conjugate place omitted by the
completed idempotent.

## 8. Height theory and finiteness

The descent has proved rational rank zero conditional only on finite
generation.  Height theory supplies finite generation for every abelian
quotient under consideration and turns rank zero into actual finiteness.

### 8.1 Why rank zero is not yet the final sentence

An arbitrary torsion abelian group can be infinite.  Consequently
$A(\mathbf Q)\otimes\mathbf Q=0$ does not by itself imply that
$A(\mathbf Q)$ is finite.  The missing input is the Mordell--Weil theorem,
whose hypotheses are satisfied because $A$ is an abelian variety over the
number field $\mathbf Q$.

The order of the argument matters.  Finite-flat descent proves bounded
Kummer quotients.  Heights prove finite generation.  Together they prove
finiteness; neither assertion substitutes for the other.

### 8.2 Mordell--Weil finite generation

Choose a symmetric ample line bundle $L$ on $A$.  Its canonical height
$\widehat h_L$ satisfies

$$
\widehat h_L([m]P)=m^2\widehat h_L(P), \tag{8.1}
$$

and differs by a bounded function from a Weil height associated with $L$.
Northcott finiteness says that points of bounded degree and bounded Weil
height form a finite set.  The weak Mordell--Weil theorem says that
$A(\mathbf Q)/mA(\mathbf Q)$ is finite for one, hence every, $m\geq2$.

The weak theorem applies with exactly the local hypotheses already available:
for the isogeny $[m]$, its Kummer image lies in a finite Selmer group, and
the Kummer map injects $A(\mathbf Q)/mA(\mathbf Q)$ into that group. No
reduction hypothesis at $N$ is needed for the general finite-generation
theorem; local Kummer images at the finitely many bad primes are finite.

Symmetry of $L$ gives the parallelogram identity

$$
\widehat h_L(P+Q)+\widehat h_L(P-Q)
=2\widehat h_L(P)+2\widehat h_L(Q). \tag{8.1a}
$$

It follows that the associated bilinear pairing obeys Cauchy--Schwarz after
quotienting by torsion. In particular, for each fixed representative $R_i$,
the cross term in $\widehat h_L(P-R_i)$ is bounded by a constant times
$\sqrt{\widehat h_L(P)}$.  That square-root term cannot be absorbed into an
additive constant while retaining the coefficient $m^{-2}$.  Instead, fix
once and for all a real number

$$
m^{-2}<\rho<1. \tag{8.1b}
$$

The inequality $2ab\leq\eta a^2+\eta^{-1}b^2$, with
$\eta=m^2\rho-1>0$, absorbs the cross term and gives a genuine contraction.

For completeness, these facts imply finite generation as follows.  Choose
representatives $R_1,\ldots,R_t$ of $A(\mathbf Q)/mA(\mathbf Q)$.  Since
there are only finitely many $R_i$, Cauchy--Schwarz and the preceding
inequality give one constant $C_\rho$ such that whenever $P=mQ+R_i$,

$$
\widehat h_L(Q)\leq\rho\widehat h_L(P)+C_\rho. \tag{8.2}
$$

Indeed,
$m^2\widehat h_L(Q)=\widehat h_L(P-R_i)$, and expansion by the height
pairing followed by $2ab\leq\eta a^2+\eta^{-1}b^2$ gives (8.2), with the
bounded $\widehat h_L(R_i)$ terms included in $C_\rho$.

Repeated division modulo the finite representative set now reaches a point
of uniformly bounded height.  Northcott makes the terminal set finite.
Induction back through the decompositions shows that the terminal points
together with the $R_i$ generate $A(\mathbf Q)$.  Thus

$$
A(\mathbf Q)\simeq\mathbf Z^d\oplus A(\mathbf Q)_{\mathrm{tors}}. \tag{8.3}
$$

All hypotheses are intrinsic to an abelian variety over $\mathbf Q$; no
property of a modular parametrization is needed in this step.

To make the termination precise, iterate (8.2).  After $j$ steps,

$$
\widehat h_L(Q_j)
\leq\rho^j\widehat h_L(P)
+\frac{C_\rho(1-\rho^j)}{1-\rho}
\leq\rho^j\widehat h_L(P)+\frac{C_\rho}{1-\rho}. \tag{8.2a}
$$

For sufficiently large $j$ this lies under one fixed bound independent of
$P$. Northcott then gives a finite terminal set. Reversing the finitely many
decompositions expresses $P$ in the subgroup generated by that terminal set
and the $R_i$. This supplies the precise termination missing from a bare
height-decrease slogan.

### 8.3 Finiteness of the Eisenstein quotient

Finite generation makes $M_{\mathfrak m}$ a finitely generated
$\mathbf Z_\ell$-module, so Section 7.3 applies.  Section 7.4 then gives
$d=0$ in (8.3).  A finitely generated torsion abelian group is finite.
Therefore

$$
\boxed{A_{\mathfrak m}(\mathbf Q)\text{ is finite}.} \tag{8.4}
$$

This conclusion is algebraic.  Its inputs are the Eisenstein index, the
cuspidal and component normalization, finite-flat torsion, Kummer theory,
and heights.  No statement about the analytic rank of an arbitrary modular
factor has been inserted.

There is a useful numerical version. If
$b=\#D_{\mathfrak m,N}\#D_{\mathfrak m,\infty}$, then (7.3) implies

$$
\#M_{\mathfrak m}[\ell^\infty]\leq b. \tag{8.5}
$$

Indeed, for $r$ at least the exponent of the finite selected torsion,
$M_{\mathfrak m}/\ell^rM_{\mathfrak m}$ is that torsion group. This does not
compute the group, because the injection into component data need not be
surjective, but it records the effective finite error produced by descent.

### 8.4 Isogenies, companions, and quotients

Finiteness is invariant under isogeny over $\mathbf Q$.  Indeed, if
$f:A\to B$ has finite kernel and a dual isogeny $g:B\to A$ satisfies
$g\circ f=[m]$, then $f\circ g=[m]$ on $B$.  Hence
$B(\mathbf Q)/fA(\mathbf Q)$ is killed by $m$ and is a quotient of
$B(\mathbf Q)/mB(\mathbf Q)$, which is finite by finite generation.  Thus
finiteness of either rational group implies finiteness of the other.

For a positive-dimensional quotient, it is not enough to say that rational
points should lift: the relevant first cohomology group need not be finite.
Instead use Poincare reducibility. If $q:A\to B$ is a surjective map of
abelian varieties with connected kernel $K$, there is an abelian subvariety
$C\subset A$ such that $K\times C\to A$ is an isogeny and $C\to B$ is an
isogeny. Therefore

$$
\operatorname{rank}A(\mathbf Q)
=\operatorname{rank}K(\mathbf Q)+\operatorname{rank}B(\mathbf Q). \tag{8.6}
$$

If $A(\mathbf Q)$ is finite, both ranks on the right are zero, and finite
generation makes $B(\mathbf Q)$ finite. Thus every abelian quotient or
isogenous companion to which the selected rational support is transported
also has finite rational points. This does not enlarge the chosen support;
it records the isogeny invariance of the conclusion with the necessary
lifting issue handled correctly.

## 9. Hecke support of rational torsion

Finiteness leaves a finite Hecke module $A(\mathbf Q)$.  We next determine
the maximal ideals that can occur in its support.  The argument is residual:
a maximal ideal in the support supplies a rational line in characteristic
$p$, and the Hecke relations on that line are the Eisenstein relations.

Two distinctions are important. First, support is detected after reduction
modulo a maximal ideal, whereas annihilation of the original finite group can
involve powers of that ideal. Second, the coefficient prime is a good prime
of the modular variety but not an etale prime for its $p$-torsion. We shall
use Frobenius directly away from $p$ and finite-flat closure at $p$.

### 9.1 Good-prime Frobenius

Let $C$ be a nonzero finite $\mathbb T$-stable subgroup of rational points on
a prime-level modular quotient, and let $\mathfrak n$ be a maximal ideal in
its support.  Its residue characteristic will be denoted $p$.  The socle of
the nonzero localized module $C_{\mathfrak n}$ contains an element

$$
0\ne P\in C[p],
\qquad \mathfrak nP=0. \tag{9.1}
$$

Put $k=\mathbb T/\mathfrak n$ and let $V=kP$. This is a one-dimensional
$k$-eigenspace, though it can have dimension greater than one over
$\mathbf F_p$. Every point of $V$ is rational, so $G_{\mathbf Q}$ acts
trivially on its underlying $\mathbf F_p$-space.

The socle element exists by elementary commutative algebra. Localize $C$ at
$\mathfrak n$ and choose the least $j$ such that
$\mathfrak n^jC_{\mathfrak n}=0$. Then
$\mathfrak n^{j-1}C_{\mathfrak n}$ is nonzero and killed by
$\mathfrak n$. Clearing a denominator not in $\mathfrak n$ realizes a
nonzero such element in $C$. Since $p\in\mathfrak n$, it is killed by $p$.

Let $q\nmid Np$.  Good reduction and the Eichler--Shimura relation give, on
prime-to-$q$ torsion,

$$
F_q^2-T_qF_q+q=0, \tag{9.2}
$$

where $F_q$ is arithmetic Frobenius.  Since $F_q$ is the identity on $V$,
applying (9.2) to $V$
gives

$$
(T_q-(1+q))P=0. \tag{9.3}
$$

Therefore

$$
T_q\equiv1+q\pmod{\mathfrak n}
\qquad(q\nmid Np). \tag{9.4}
$$

The exclusion of $q=p$ is genuine: (9.2) on geometric $p$-torsion cannot be
used as though the group were etale at $p$.  The missing operator is recovered
from the integral closure of the rational line.

Hecke multiplicativity now determines more than prime coefficients. If
$m$ is prime to $Np$, repeated use of

$$
T_{q^{a+1}}=T_qT_{q^a}-qT_{q^{a-1}} \tag{9.4a}
$$

and multiplicativity for coprime indices gives
$T_mP=\sigma_1(m)P$. This is the residual divisor-sum eigensystem. The only
missing generators of the faithful algebra are $T_p$ and $U_N$.

### 9.2 The missing coefficient prime

Because $p\mid n_N$ will follow from the argument, ultimately $p\ne N$.
For the moment suppose only that $p\ne N$, so the modular Jacobian has good
reduction at $p$. Take the schematic closure $\mathcal V$ of the residual
eigenspace $V$ in the $p$-torsion of the abelian scheme over $\mathbf Z_p$.
It is finite flat of rank $p^{[k:\mathbf F_p]}$ and is stable under the Hecke
operators.

Choose a finite-flat composition flag of $\mathcal V$. For odd $p$, every
generic constituent has trivial Galois character. Endpoint recognition
therefore makes every factor constant; a multiplicative atom would have
nontrivial cyclotomic generic character. For $p=2$, the two generic
characters coincide, so either integral atom can occur. On each covariant
special-fiber constituent, Frobenius and Verschiebung have the values

$$
\begin{array}{c|cc|c}
\text{closure}&F&V&F+V\\ \hline
\underline{\mathbf Z/p\mathbf Z}&1&0&1\\
\mu_p&0&1&1
\end{array} \tag{9.5}
$$

The $p$-th Hecke correspondence satisfies

$$
T_p=F+V \tag{9.6}
$$

on every order-$p$ factor.  This is the special-fiber form of the integral
Eichler--Shimura correspondence recorded in Book 145; it is stronger than
merely substituting $F$ into the generic quadratic polynomial.  Thus
$T_p-1$ acts as zero on all successive
factors of $\mathcal V$. On the other hand $T_p$ acts on $V$ through the
single scalar $\lambda(T_p)\in k$. A scalar whose difference from $1$ acts
nilpotently on a nonzero $k$-space must equal $1$. It follows, including for
both dyadic endpoints, that

$$
T_pP=P=(1+p)P. \tag{9.7}
$$

This proves (9.3) for the missing coefficient prime.  The argument uses the
integral atom only to interpret $F$ and $V$; it does not identify
$\mu_2$ with the constant group over $\mathbf Z_2$.

Why does scalar action eliminate a possible nonsplit extension in
$\mathcal V$? A flag of length $d=[k:\mathbf F_p]$ shows
$(T_p-1)^d\mathcal V=0$. Restriction to the generic eigenspace gives
$(\lambda(T_p)-1)^dV=0$. Since $V$ is a vector space over the field $k$,
this scalar endomorphism is zero only when $\lambda(T_p)=1$. Thus the
integral extension may be nonsplit, but it cannot change the residual
eigenvalue.

The temporary assumption $p\ne N$ will not be used circularly. If $p=N$,
there is no missing operator $T_p$ in the prime-level Hecke algebra: the
level operator is $U_N$. Thus (9.4) already supplies every relation required
in the hypothesis of Lemma 9.2 below. That lemma will rule out $p=N$.

### 9.3 The level operator

It remains to determine $U_N$. The exact prime-level Fourier pairing gives
the following algebraic sign lemma.

**Lemma 9.2 (prime-level Eisenstein sign).** Let $k$ be a finite field of
characteristic $p$ and let $\lambda:\mathbb T\to k$ be a system of Hecke
eigenvalues satisfying

$$
\lambda(T_q)=1+q\qquad(q\ne N). \tag{9.8}
$$

Then

$$
\lambda(U_N)=1,
\qquad p\mid n_N. \tag{9.9}
$$

**Proof.** Hecke--Fourier duality realizes the functional $\lambda$ in a
unique $f$ in the mod-$p$ cusp lattice.  Since $\lambda(1)=1$, one has
$a_1(f)=1$; commutativity and perfectness give
$Tf=\lambda(T)f$ for every $T\in\mathbb T$.  Thus $f$ is a normalized
mod-$p$ cuspidal eigenform.  The relations (9.8), multiplicativity, and the
prime-power recurrence give

$$
a_m(f)=\sigma_1(m)\qquad(N\nmid m). \tag{9.9a}
$$

We use one precise consequence of the all-cusp integral calculation in Book
142.  Suppose a normalized weight-two cuspidal form of prime level $N$ has
the coefficients (9.9a), and write $u$ for its $U_N$-eigenvalue.  Then

$$
a_N(f)=1. \tag{9.9b}
$$

Here is the support-descent proof, including the small characteristics.  On
the punctured Tate chart subtract the prescribed Eisenstein *coefficient
functional*, rather than pretending that its rational constant term is an
integral modular form.  The resulting positive expansion is supported on
$q^{Nm}$, and its first such coefficient is $u-1$.  The all-cusp
q-expansion calculation descends such a supported weight-two differential
to level one.  On the chart at the other cusp, the two-cusp residue lattice
is exactly the condition that removes a possible pole.  Thus the descended
positive part is a level-one cuspidal differential and is zero because
$X(1)$ has genus zero.

At characteristics $2$ and $3$, the integral calculation is made before
reduction on the stack, not by dividing the rational constant term.  Its
only additional q-invisible directions are the level-one Hasse directions;
their q-expansions have no positive coefficient, so they cannot alter the
coefficient of $q^N$.  If $p=N$, the same conclusion is the bad-level part
of the calculation: one works on the two normalized components and the
weighted node lattice, rather than descending through an inseparable Tate
isogeny.  These are precisely the good-level Hasse and bad-level
normalization checks used in Book 142 to obtain the factors removed from
$N-1$ at $2$ and $3$.  They prove (9.9b) in every characteristic without
turning a Fourier functional into a form.

On the other hand, $U_Nf=uf$ and normalization give
$a_N(f)=u a_1(f)=u$.  Hence (9.9b) gives $u=1$.  Now the recurrences determine
the complete expansion

$$
a_m(f)=\sum_{\substack{d\mid m\\N\nmid d}}d
\qquad(m\geq1). \tag{9.9c}
$$

Book 142's exact integral Eisenstein calculation says that this normalized
cuspidal coefficient system occurs over a field of characteristic $p$ if
and only if $p\mid n_N$, where

$$
n_N=\frac{N-1}{\gcd(N-1,12)}. \tag{9.10}
$$

Equivalently, $\lambda$ now kills $I$ and factors through
$\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z$.  This proves both assertions.
$\square$

If the residue characteristic is $2$, the same proof includes the equality
$+1=-1$ in $k$ and the exact two-primary correction in $n_N$. Thus no
separate sign convention is hidden in the lemma.

The distinction in the proof is essential.  For $p\geq5$ with $p\ne N$ one
may make the comparison with the usual integral Eisenstein form directly.
At $2$, $3$, or the bad characteristic $N$, the saturated all-cusp lattice
must be used.  A rational Fourier series with a forbidden constant
denominator is not a modular form that can be subtracted from $f$.

When $p\ne N$, Sections 9.1 and 9.2 give (9.8), so Lemma 9.2 gives
$U_NP=P$. When $p=N$, Section 9.1 already gives (9.8) for every generator
$T_q$ with $q\ne N$; Lemma 9.2 would imply $N\mid n_N$, impossible because
$n_N\mid N-1$. Hence $p=N$ never occurs. In all possible cases,

$$
U_NP=P. \tag{9.12}
$$

Combining (9.3), (9.7), and (9.12) gives

$$
IP=0. \tag{9.13}
$$

### 9.4 The Eisenstein support theorem

**Theorem 9.3 (rational torsion support).**  Let $C$ be a finite
$\mathbb T$-stable group of rational points on a prime-level modular abelian
quotient.  Every maximal ideal in $\operatorname{Supp}_{\mathbb T}(C)$ is

$$
\mathfrak m_p=(p,I) \tag{9.14}
$$

for a prime $p\mid n_N$.  In particular, no prime dividing $C$ equals $N$.

**Proof.**  Choose $P$ as in (9.1).  Sections 9.1--9.3 show that $I$ and $p$
annihilate $P$, so $(p,I)\subseteq\mathfrak n$.  The quotient
$\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z$ has a maximal ideal of residue
characteristic $p$ exactly when $p\mid n_N$, and its inverse image is the
unique ideal $(p,I)$.  Thus $p\mid n_N$ and
$\mathfrak n=(p,I)$. $\square$

Apply the theorem to $C=A(\mathbf Q)$, finite by (8.4).  It says exactly that
the residual support of the remaining rational points is Eisenstein.  It
does not say that every point is cuspidal, nor that the rational torsion group
has order $n_N$.

The uniqueness after factorization through $\mathbb T/I$ is worth
emphasizing. Since
$\mathbb T/I$ is the single cyclic ring $\mathbf Z/n_N\mathbf Z$, there is
one Eisenstein maximal ideal above each prime divisor of $n_N$. The theorem
does not leave room for a second level sign or a different residue extension.
In particular its residue field is $\mathbf F_p$, even though the argument
allowed a larger field until Lemma 9.2 was applied.

## 10. Hecke annihilators without multiplicity one

Support determines the radical of an annihilator, but not generally the
annihilator itself.  Since the dependency package deliberately avoids a
complete multiplicity-one theorem, the correct statement uses powers of the
Eisenstein maximal ideals.

### 10.1 Radicals and Loewy length

Let $C=A(\mathbf Q)$ and write

$$
C=\bigoplus_{p\mid\#C}C_p \tag{10.1}
$$

for its primary decomposition.  By Theorem 9.3, $C_p$ is supported at the
single maximal ideal $\mathfrak m_p=(p,I)$.  As a finite module over the
Artinian image of $\mathbb T_{\mathfrak m_p}$, it has a finite Loewy
filtration

$$
C_p\supseteq\mathfrak m_pC_p\supseteq
\mathfrak m_p^2C_p\supseteq\cdots\supseteq0. \tag{10.2}
$$

Let $s_p$ be the least exponent with

$$
\mathfrak m_p^{s_p}C_p=0. \tag{10.3}
$$

Every nonzero quotient in (10.2) is a nonzero vector space over a field of
characteristic $p$.  Hence the elementary bound

$$
1\leq s_p\leq\log_p\#C_p \tag{10.4}
$$

holds whenever $C_p\ne0$.

To prove termination of (10.2), let $R_p$ be the image of
$\mathbb T_{\mathfrak m_p}$ in $\operatorname{End}(C_p)$. It is a finite
commutative local ring. Its maximal ideal is the image of $\mathfrak m_p$,
and every element of that ideal is nilpotent because the ring is Artinian.
The ideal itself is nilpotent, so some power kills $C_p$. If the inclusions
in (10.2) are strict through stage $s_p$, each quotient has at least $p$
elements. Multiplying their orders proves (10.4).

### 10.2 The exact annihilator statement

For a finite module over a commutative ring, the radical of its annihilator
is the intersection of the maximal ideals in its support.  Theorem 9.3
therefore gives the exact formula

$$
\boxed{
\sqrt{\operatorname{Ann}_{\mathbb T}A(\mathbf Q)}
=\bigcap_{p\mid\#A(\mathbf Q)}(p,I).}
\tag{10.5}
$$

If $A(\mathbf Q)=0$, the intersection is empty by convention and both sides
are the unit ideal.  In addition, (10.3) gives the explicit annihilator

$$
\boxed{
\prod_{p\mid\#A(\mathbf Q)}(p,I)^{s_p}
\subseteq\operatorname{Ann}_{\mathbb T}A(\mathbf Q).}
\tag{10.6}
$$

Indeed, on $C_p$ the $p$-factor in the product acts as zero, and primary
decomposition proves the assertion on all of $C$.  Equations (10.5) and
(10.6) are the promised computation of the Hecke annihilator at the level of
generality justified here.

Here is a direct proof of the radical identity. A maximal ideal
$\mathfrak n$ contains $\operatorname{Ann}(C)$ exactly when
$C_{\mathfrak n}\ne0$. If the localization were zero, finitely many
denominators outside $\mathfrak n$ would multiply to an annihilator outside
$\mathfrak n$; conversely an annihilator outside $\mathfrak n$ becomes a
unit and forces the localization to vanish. The radical of an ideal is the
intersection of all prime ideals containing it. Because the quotient by the
annihilator is Artinian, all its prime ideals are maximal. Combining these
facts proves (10.5).

For (10.6), fix $q\ne p$. On the $p$-primary group $C_p$, the integer $q$
acts invertibly, so the maximal ideal $\mathfrak m_q$ becomes the unit ideal
after localization at $p$. The factor
$\mathfrak m_p^{s_p}$ kills $C_p$, while all other factors are harmless.
Thus the complete product kills every primary summand.

### 10.3 Why one must not replace a power by the ideal

Knowing that every composition factor is killed by $\mathfrak m_p$ proves
only that some power of $\mathfrak m_p$ kills the module.  For example, on
$R/\mathfrak m^2$ the ideal $\mathfrak m$ kills both successive composition
factors but does not kill the whole module.  An extension between two
Eisenstein constituents can behave in exactly this way.

Consequently neither

$$
IA(\mathbf Q)=0 \tag{10.7}
$$

nor

$$
\mathfrak m_pC_p=0 \tag{10.8}
$$

is asserted.  Either conclusion would require control of extension classes
or a suitable multiplicity-one statement.  The radical formula loses no
information that support alone can provide, while the Loewy exponent records
the remaining nilpotence exactly.

The distinction already appears for abelian groups. The group
$\mathbf Z/p^2\mathbf Z$ has a filtration with two factors killed by $p$,
but $p$ does not kill the group. Replacing $p$ by an Eisenstein maximal ideal
gives the Hecke-theoretic analogue. Finite-flat admissibility controls which
composition factors occur; it does not automatically split their extensions
inside rational torsion.

### 10.4 Prime-by-prime form

Because $I\subseteq\mathfrak m_p$, (10.3) implies

$$
I^{s_p}C_p=0,
\qquad p^{s_p}C_p=0. \tag{10.9}
$$

The first equation is the Eisenstein Hecke annihilator on the $p$-primary
part; the second is a deliberately coarse exponent bound.  The actual group
exponent may be smaller.  Combining all primes yields

$$
I^sA(\mathbf Q)=0,
\qquad
s=\max_{p\mid\#A(\mathbf Q)}s_p. \tag{10.10}
$$

Thus finiteness and Eisenstein support produce a genuine global Hecke
annihilator, while (10.5) records precisely which maximal ideals occur.

There are three levels of precision, and they should not be conflated:

$$
\begin{array}{c|c}
\text{information}&\text{conclusion}\\ \hline
\text{residual eigenvalues}&\operatorname{Supp}(C)\subseteq\{(p,I)\}\\
\text{actual nonzero primary parts}&
\sqrt{\operatorname{Ann}(C)}=\bigcap(p,I)\\
\text{Loewy lengths}&\prod(p,I)^{s_p}C=0
\end{array} \tag{10.11}
$$

The first is supplied by Frobenius and the level sign, the second by the
finite module itself, and the third by its local Artinian structure.

## 11. Exceptional levels and boundary cases

The formula $n_N=(N-1)/\gcd(N-1,12)$ contains all small-prime corrections.
This chapter makes them explicit and checks that none was silently restored
during descent.

### 11.1 Trivial Eisenstein index

If $n_N=1$, then $\mathbb T/I=0$ and there is no Eisenstein maximal ideal
$\mathfrak m=(\ell,I)$.  The selected quotient associated with such an ideal
is absent, so the theorem is vacuous rather than false.  This includes the
small prime levels for which the numerator in (1.4) is $1$.

For prime $N$, the equality $n_N=1$ means $N-1$ divides $12$. Thus the full
list is

$$
N\in\{2,3,5,7,13\}. \tag{11.0a}
$$

At these levels one should not choose an arbitrary prime $\ell$ and call
$(\ell,I)$ Eisenstein: the quotient $\mathbb T/I$ has no maximal ideals.
This boundary check prevents the descent hypotheses from being applied to a
nonexistent selected factor.

More generally, a prime $\ell$ can be selected only if $\ell\mid n_N$.
Since $n_N\mid N-1$, this automatically gives $\ell\ne N$, exactly the
hypothesis used at the semistable level prime.

For every prime divisor of the index the valuation can be read at once:

$$
v_\ell(n_N)=
\begin{cases}
\max\{v_2(N-1)-2,0\},&\ell=2,\\
\max\{v_3(N-1)-1,0\},&\ell=3,\\
v_\ell(N-1),&\ell\geq5.
\end{cases} \tag{11.0b}
$$

Every later exponent $e=v_\ell(n_N)$ uses this table.

### 11.2 The prime three

If $3\mid n_N$, then necessarily $N\equiv1\pmod9$ and

$$
v_3(n_N)=v_3(N-1)-1. \tag{11.1}
$$

The missing factor of $3$ is the denominator correction already present in
the exact Hecke index and cusp order. Descent never replaces $n_N$ by
$N-1$: this normalized index selects $\mathfrak m$, while the component
bound itself uses the actual component image of $A$. The support theorem
returns to $\mathbb T/I$, whose order is exactly $n_N$.

The coefficient prime is odd, so the two generic atomic characters are
distinct.  Endpoint recognition and the unit calculation of Proposition 5.1
apply without a real condition.  Nothing special happens to the
$[N]$-extension except that strictness removes its valuation class.

### 11.3 The full two-primary boundary

The prime $2$ divides $n_N$ exactly when $N\equiv1\pmod8$, and then

$$
v_2(n_N)=v_2(N-1)-2. \tag{11.2}
$$

Thus the denominator correction removes two powers of $2$.  It must not be
confused with the single power removed at $3$.

There are four dyadic issues, all already present in the proof:

1. the generic characters of $\mu_2$ and the constant atom coincide, so the
   integral closure labels the endpoint;
2. the sign class $[-1]$ is removed by the positive real condition; and
3. nonsplit towers may contain both a sign and a carry, which are retained by
   propagated local conditions in Chapter 6; and
4. arbitrary rational points can occupy a nonidentity real component, whose
   finite image is admitted in the relaxed group and included in (7.2).

At the missing Hecke operator $T_2$, both endpoint rows in (9.5) have
$F+V=1$, so no choice between the closures is required.  At the level
operator, $+1=-1$ in characteristic $2$, so the Steinberg sign ambiguity
still yields $U_N=1$ in the residue field.  These observations cover the
entire two-primary boundary, not only the first layer.

The strict and relaxed real conditions must not be interchanged. Using the
full real Kummer image in the atomic strict calculation would allow the sign
$[-1]$ and destroy Proposition 5.2. Using the zero real condition for the
relaxed group would exclude legitimate global Kummer classes. The finite
group $D_{\mathfrak m,\infty}$ is exactly what permits both statements to be
true.

Some small numerical checks help locate the correction. At $N=17$ one has
$n_N=4$, so the two-primary exponent is $2$, not $4$. At $N=41$ one has
$n_N=10$, so only one power of $2$ remains. At $N=73$ one has $n_N=6$:
the $2$- and $3$-corrections have both acted. These are checks of the index,
not assertions about the exact order of any rational point group.

### 11.4 The level prime

The level prime is never a coefficient prime in this descent.  At $N$ the
model is semistable, the strict condition uses the identity component, and
the relaxed error uses the actual finite component image.  At every other
finite prime the selected quotient has good reduction and the Kummer
condition is integral flat.

This division of roles is essential.  Treating $N$ as a good prime would
erase the component target and falsely force every local point into the
strict group.  Treating the coefficient prime by ordinary unramified
cohomology would erase connected flat classes.  The proof makes neither
replacement.

The same separation appears in the Hecke calculation. If the residue
characteristic $p$ differs from $N$, $T_p$ is recovered from good-reduction
Frobenius and Verschiebung, while $U_N$ is recovered from the prime-level
Fourier sign lemma. If $p=N$, there is no $T_p$ generator; the sign lemma
would force $N\mid n_N$ and rules the case out. Thus no formula valid only
away from the level is evaluated at the level.

### 11.5 What the theorem does not identify

The result proves finiteness, Eisenstein support of the finite rational group,
the radical formula (10.5), and a power annihilator.  It does not identify
$A(\mathbf Q)$ with the rational cuspidal subgroup, compute its exact order,
prove that $I$ itself annihilates it, or establish a complete intersection or
multiplicity-one theorem for the local Hecke algebra.

It also does not assert finiteness of a Tate--Shafarevich group.  The strict
Selmer groups here have the selected finite coefficients $G_r$ and specially
chosen local conditions.  Their vanishing controls the Kummer images needed
for Mordell--Weil rank; it is not a statement about every torsor under $A$.

No winding quotient is used, and no analytic rank-zero theorem for arbitrary
modular factors is invoked. The rank calculation is the uniform algebraic
Kummer bound (7.3), followed by the general height theorem.

## 12. The Eisenstein descent package

We can now state the result with all normalizations, hypotheses, and limits
visible in one place.

### 12.1 Main theorem

**Theorem 12.1 (Eisenstein descent and finiteness).**  Let $N$ be prime, let

$$
n_N=\frac{N-1}{\gcd(N-1,12)},
\qquad
I=(T_q-(1+q):q\ne N)+(U_N-1), \tag{12.1}
$$

and fix $\ell\mid n_N$ and $\mathfrak m=(\ell,I)$.  Let
$A=A_{\mathfrak m}$ be the selected optimal Eisenstein quotient, let
$\varepsilon$ be the completed local idempotent, and let
$G_r=\varepsilon\mathcal A[\ell^r]$ be its finite-flat selected torsion over
$\mathbf Z[1/N]$.  Assume the saturated Tate comparison, exact finite-flat
tower, and admissible constant--multiplicative filtrations established for
this selected quotient.  Then:

1. for every $r\geq1$,
   $$
   \operatorname{Sel}^{\mathrm{str}}(G_r)=0; \tag{12.2}
   $$
2. if $D_{\mathfrak m,N}$ is the selected image of the level-prime component
   map and $D_{\mathfrak m,\infty}$ is the selected real component group
   when $\ell=2$ (zero otherwise), then
   $$
   \varepsilon(A(\mathbf Q)\otimes\mathbf Z_\ell)/\ell^r
   \hookrightarrow
   D_{\mathfrak m,N}/\ell^rD_{\mathfrak m,N}
   \oplus
   D_{\mathfrak m,\infty}/\ell^rD_{\mathfrak m,\infty}; \tag{12.3}
   $$
3. the selected completion has $\mathbf Z_\ell$-rank zero, the rational
   support argument gives $\operatorname{rank}A(\mathbf Q)=0$, and
   $$
   A(\mathbf Q)\text{ is finite}; \tag{12.4}
   $$
4. every maximal ideal in the Hecke support of $A(\mathbf Q)$ is
   $(p,I)$ for a prime $p\mid n_N$; and
5. with $s_p$ the Loewy length of the $p$-primary part,
   $$
   \sqrt{\operatorname{Ann}_{\mathbb T}A(\mathbf Q)}
   =\bigcap_{p\mid\#A(\mathbf Q)}(p,I),
   \qquad
   \prod_{p\mid\#A(\mathbf Q)}(p,I)^{s_p}
   \subseteq\operatorname{Ann}_{\mathbb T}A(\mathbf Q). \tag{12.5}
   $$

**Proof.**  Atomic strict vanishing is Propositions 5.1 and 5.2.  The
admissible filtration and left-exact devissage give (12.2) by Theorem 6.2.
The strict--relaxed comparison at the level prime and, dyadically, at the
real place gives (12.3). Its finite right side bounds all Kummer quotients,
so finite generation and the growth formula force zero selected rank.
Rational support gives zero total rank,
and the Mordell--Weil theorem gives (12.4).  Theorem 9.3 proves the support
claim, and finite-module commutative algebra proves (12.5). $\square$

Let us isolate the quantifiers in the proof. The selected prime $\ell$ is
fixed, but the torsion level $r$ is arbitrary. For each $r$, admissibility
may supply a different flag; Theorem 6.2 nevertheless gives exact zero, so
the flag length contributes no constant. The groups
$D_{\mathfrak m,N}$ and $D_{\mathfrak m,\infty}$ are fixed before $r$ is
chosen. Therefore (12.3) is a genuinely uniform family of injections. This
uniformity, rather than finite-level Selmer finiteness by itself, is what
forces rank zero.

The proof has four logically separate transitions:

$$
\begin{array}{c|c|c}
\text{transition}&\text{input}&\text{output}\\ \hline
\text{atomic to finite flat}&\text{admissible flag and cartesianness}
&\operatorname{Sel}^{\mathrm{str}}(G_r)=0\\
\text{strict to relaxed}&\text{local component sequences}
&\text{uniform Kummer bound}\\
\text{completion to rational rank}&\text{saturation and rational support}
&A(\mathbf Q)\otimes\mathbf Q=0\\
\text{rank to cardinality}&\text{Mordell--Weil finite generation}
&\#A(\mathbf Q)<\infty
\end{array} \tag{12.5a}
$$

None can be omitted. Atomic calculations do not see nonsplit extensions;
strict vanishing does not include component classes; a single completion
does not equal a rational projector; and rank zero does not imply finiteness
for an arbitrary abelian group. The preceding chapters supply exactly the
bridge at each transition.

The final Hecke assertions begin only after the fourth transition. For each
maximal ideal in the support of the finite group, its socle supplies a
rational residual eigenspace. Good-prime Frobenius, finite-flat closure at
the coefficient prime, and the prime-level sign lemma show that its maximal
ideal is $(p,I)$. Artinian local algebra then converts residual support into
the radical equality and power annihilator. This order prevents residual
semisimplicity from being mistaken for an integral splitting.

### 12.2 Dependency ledger

Every substantial input occurs earlier with the same hypotheses:

- Book 31 supplies finite-module local Tate duality and, crucially, the
  warning that its coefficient-prime unramified subgroup is not the flat
  condition needed here.  This book does not attribute a local-flat duality
  theorem to Book 31.
- Book 32 supplies Selmer structures, propagation of local conditions,
  strict and relaxed modifications, and the exact sequence obtained by
  changing one local condition; (4.12) applies that sequence successively at
  the level prime and at the real place.
- Book 42 supplies isogeny Kummer maps, finite-flat local images at good
  primes, finiteness of finite-level Selmer groups, and weak
  Mordell--Weil.
- Book 43 supplies canonical heights, Northcott finiteness, the
  Mordell--Weil theorem, and its applicability to every abelian quotient of
  a Jacobian.
- Book 142 fixes the prime-level Hecke algebra including $U_N$, the
  Hecke--Fourier pairing, the good-level Hasse and bad-level normalization
  calculations used in Lemma 9.2, the Eisenstein ideal, and the exact quotient
  $\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z$, including the distinct
  corrections at $2$ and $3$.
- Book 143 supplies the order-$n_N$ cuspidal subgroup, its isomorphic
  specialization to the cyclic component group at $N$, the matching Hecke
  action, and the warning that component behavior under quotients requires
  care.
- Book 144 classifies the admissible constant and multiplicative atoms and
  their extensions, including the odd $[N]$-class and the dyadic sign and
  carry.
- Book 145 constructs the selected optimal quotient, distinguishes the
  rational projector from the completed idempotent, proves saturation of the
  selected Tate lattice, constructs the exact finite-flat tower $G_r$, and
  proves admissibility at every level, including the dyadic endpoints and
  the connected--etale sequence; its integral Eichler--Shimura input gives
  the good-prime identities used in Sections 9.1 and 9.2.

The hypothesis matching is exact.  Book 32 provides the language of
finite-flat-shaped local images, while the actual coefficient-prime models
and their functorial fppf conditions come from Books 42, 144, and 145 and
the direct flat Kummer calculations (3.4)--(3.5).  Book 31's generic-fiber
duality is not used to manufacture an integral orthogonality statement.
Book 42 applies to the multiplication isogenies of an abelian variety over
$\mathbf Q$ and identifies their good-reduction Kummer images. Book 43
applies because an optimal quotient of $J_0(N)$ is an abelian variety over a
number field. Books 142 and 143 assume prime level and use the same
arithmetic Frobenius and $U_N$ convention as (1.5). Books 144 and 145 work
over $\mathbf Z[1/N]$ with $\ell\mid n_N$, hence $\ell\ne N$, and include
the full dyadic closure data needed in Chapters 5 and 6.

The imported results are used without strengthening them. The cyclic
component calculation for $J$ is not promoted to an equality for
$\Phi_N(A)$. Admissible constituents are not promoted to a direct-sum
decomposition. Saturation is asserted only on the selected completion.
Finite generation is not promoted to rank zero without descent. Finally,
constituent-wise Eisenstein action is promoted only to a power annihilator,
not to annihilation by $I$ itself.

The present argument uses no global duality theorem beyond this list.  Its
Selmer induction is left exact and is proved directly in Lemma 6.1.

### 12.3 Normalization and failure ledger

For reference, the assertions most vulnerable to a normalization error are:

$$
\begin{array}{c|c|c}
\text{object}&\text{normalization used}&\text{consequence of changing it}\\ \hline
n_N&(N-1)/\gcd(N-1,12)&\text{wrong Eisenstein primes and exponents}\\
U_N&U_N-1\in I&\text{wrong level-prime sign}\\
F_q&\text{arithmetic Frobenius}&\text{inverted Hecke polynomial}\\
v=\ell&\text{flat integral condition}&\text{lost connected classes}\\
v=N&\text{identity-component strictness}&\text{lost component error}\\
v=\infty,\ \ell=2&\text{positive condition}&\text{surviving sign class}\\
\varepsilon&\text{completed local idempotent}&\text{unsaturated finite levels}
\end{array} \tag{12.6}
$$

The proof also fails if an admissible filtration is replaced by a
semisimplification: the $[N]$-extension, dyadic sign, and carry would
disappear.  It fails if the component map is assumed surjective without
proof, or if support is promoted from radical annihilation to annihilation by
$I$ itself.  Each of these failure modes has been excluded explicitly.

### 12.4 Conclusion

Eisenstein descent converts a tower of finite-flat torsion into a statement
about rational points by separating finite local component defects from an
otherwise vanishing Selmer problem. Units and unramified covers settle the
atoms; cartesian devissage preserves every nonsplit extension; the Néron and
real component groups bound the relaxed classes; and height theory turns
bounded Kummer growth into finiteness. The surviving finite group has precisely Eisenstein
residual support and is annihilated by an explicit product of powers of the
corresponding Eisenstein maximal ideals.

The argument is therefore complete without identifying the rational group
with the cuspidal subgroup and without assuming a stronger local Hecke
structure than the preceding finite-flat construction supplies.
