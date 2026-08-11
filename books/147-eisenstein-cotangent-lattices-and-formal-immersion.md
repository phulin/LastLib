# Eisenstein Cotangent Lattices and Formal Immersion

## Contents

1. [Why a cotangent calculation controls rational points](#1-why-a-cotangent-calculation-controls-rational-points)
   - [The local-to-global problem](#11-the-local-to-global-problem)
   - [Prime-level notation](#12-prime-level-notation)
   - [The proof architecture](#13-the-proof-architecture)
   - [The boundaries of the argument](#14-the-boundaries-of-the-argument)
2. [Formal immersions and sections over a discrete valuation ring](#2-formal-immersions-and-sections-over-a-discrete-valuation-ring)
   - [Completed local rings and cotangent spaces](#21-completed-local-rings-and-cotangent-spaces)
   - [A relative cotangent criterion](#22-a-relative-cotangent-criterion)
   - [Separation of two sections](#23-separation-of-two-sections)
   - [Why equality on the special fiber is insufficient](#24-why-equality-on-the-special-fiber-is-insufficient)
3. [The oriented $\Gamma_1$ cusp](#3-the-oriented-gamma_1-cusp)
   - [Point level and cyclic level](#31-point-level-and-cyclic-level)
   - [The two kinds of cusp](#32-the-two-kinds-of-cusp)
   - [The outward cusp parameter](#33-the-outward-cusp-parameter)
   - [Rationality and reduction of the orientation](#34-rationality-and-reduction-of-the-orientation)
4. [Cotangent lattices of optimal Eisenstein quotients](#4-cotangent-lattices-of-optimal-eisenstein-quotients)
   - [The exact abelian quotient](#41-the-exact-abelian-quotient)
   - [Primitive invariant differentials](#42-primitive-invariant-differentials)
   - [Comparison with the completed Hecke piece](#43-comparison-with-the-completed-hecke-piece)
   - [Companion factors and what is actually selected](#44-companion-factors-and-what-is-actually-selected)
5. [Dualizing forms, Hecke operators, and the first coefficient](#5-dualizing-forms-hecke-operators-and-the-first-coefficient)
   - [The canonical differential lattice](#51-the-canonical-differential-lattice)
   - [The coefficient identity](#52-the-coefficient-identity)
   - [Finding a unit coefficient](#53-finding-a-unit-coefficient)
   - [Small characteristics and integral reduction](#54-small-characteristics-and-integral-reduction)
6. [The selected cotangent theorem](#6-the-selected-cotangent-theorem)
   - [Statement of the comparison](#61-statement-of-the-comparison)
   - [Proof of primitivity and base change](#62-proof-of-primitivity-and-base-change)
   - [The selected summand at the Eisenstein prime](#63-the-selected-summand-at-the-eisenstein-prime)
   - [A failure ledger for rational projectors](#64-a-failure-ledger-for-rational-projectors)
7. [Formal immersion at an oriented cusp](#7-formal-immersion-at-an-oriented-cusp)
   - [The pointed map to the selected quotient](#71-the-pointed-map-to-the-selected-quotient)
   - [The cotangent calculation](#72-the-cotangent-calculation)
   - [The oriented formal-immersion theorem](#73-the-oriented-formal-immersion-theorem)
   - [Uniformity and the role of the Hecke translate](#74-uniformity-and-the-role-of-the-hecke-translate)
8. [Specialization of finite rational points](#8-specialization-of-finite-rational-points)
   - [The kernel of reduction at an odd good prime](#81-the-kernel-of-reduction-at-an-odd-good-prime)
   - [Cusp-disk rigidity for the selected quotient](#82-cusp-disk-rigidity-for-the-selected-quotient)
   - [Why the argument is stated at an odd prime](#83-why-the-argument-is-stated-at-an-odd-prime)
   - [Compatibility with changing the oriented cusp](#84-compatibility-with-changing-the-oriented-cusp)
9. [Reducing a rational prime-order point](#9-reducing-a-rational-prime-order-point)
   - [The modular point attached to $(E,P)$](#91-the-modular-point-attached-to-ep)
   - [Interior reduction and the Hasse bound](#92-interior-reduction-and-the-hasse-bound)
   - [Multiplicative reduction and the outward direction](#93-multiplicative-reduction-and-the-outward-direction)
   - [The rational oriented cusp reached at three](#94-the-rational-oriented-cusp-reached-at-three)
10. [The uniform theorem for primes at least seventeen](#10-the-uniform-theorem-for-primes-at-least-seventeen)
    - [The Eisenstein prime exists](#101-the-eisenstein-prime-exists)
    - [The uniform exclusion](#102-the-uniform-exclusion)
    - [Exceptional index and residue-characteristic checks](#103-exceptional-index-and-residue-characteristic-checks)
    - [What the uniform theorem does and does not classify](#104-what-the-uniform-theorem-does-and-does-not-classify)
11. [The genus-one calculation at level eleven](#11-the-genus-one-calculation-at-level-eleven)
    - [A model of $X_1(11)$](#111-a-model-of-x_111)
    - [Finiteness of its Mordell--Weil group](#112-finiteness-of-its-mordell--weil-group)
    - [Two reduction counts](#113-two-reduction-counts)
    - [All rational points are cusps](#114-all-rational-points-are-cusps)
12. [The remaining small-prime geometry](#12-the-remaining-small-prime-geometry)
    - [Tate normal form](#121-tate-normal-form)
    - [The five-primary genus-one calculation](#122-the-five-primary-genus-one-calculation)
    - [The mixed-seven genus-two curve](#123-the-mixed-seven-genus-two-curve)
    - [Why a square discriminant is only necessary](#124-why-a-square-discriminant-is-only-necessary)
13. [The level-thirteen genus-two curve](#13-the-level-thirteen-genus-two-curve)
    - [An integral affine model](#131-an-integral-affine-model)
    - [Genus, cusps, and the hyperelliptic form](#132-genus-cusps-and-the-hyperelliptic-form)
    - [The exact rational-point problem](#133-the-exact-rational-point-problem)
    - [The two genus-two handoffs](#134-the-two-genus-two-handoffs)
14. [The complete formal-immersion package](#14-the-complete-formal-immersion-package)
    - [Main theorem](#141-main-theorem)
    - [Dependency ledger](#142-dependency-ledger)
    - [Normalization and exceptional-case ledger](#143-normalization-and-exceptional-case-ledger)
    - [Conclusion](#144-conclusion)

## 1. Why a cotangent calculation controls rational points

### 1.1 The local-to-global problem

A rational point on a modular curve can be forced into a very small residue disk without being determined by its reduction. Properness extends the point across a valuation ring, and reduction identifies a point of the special fiber, but many sections can pass through the same special point. The missing datum is first-order: one needs a map from the curve to a finite arithmetic group whose completed local ring sees the entire cusp disk.

The relevant map begins with an Abel--Jacobi map and ends in an Eisenstein quotient. Let $X$ be a modular curve, let $c$ be a cusp, and let $J$ be the Jacobian. The pointed map

$$
x\longmapsto[x-c]
$$

turns the difference between a rational point and the cusp into a rational point of $J$. Passing to a quotient $A$ gives two complementary advantages. First, if $A(\mathbf Q)$ is finite, equality after reduction can force equality in $A(\mathbf Q)$. Second, if the map $X\to A$ is a formal immersion at $c$, equality in $A$ forces equality of sections in the cusp disk.

These two implications solve different problems. Finiteness is global and arithmetic. Formal immersion is local and integral. A proof that establishes only one of them cannot conclude that the rational point is the cusp. Book 146 established finiteness for the selected Eisenstein quotient. The purpose of the present book is to establish the integral cotangent comparison and the formal immersion, then join the two statements without losing the oriented point-level structure.

The central chain is

$$
\begin{array}{c}
\text{primitive quotient cotangent lattice}\\
\Downarrow\\
\text{a nonzero reduced dualizing form}\\
\Downarrow\ \text{q-expansion and a Hecke translate}\\
\text{a unit first coefficient at the cusp}\\
\Downarrow\\
\text{formal immersion at the oriented cusp}\\
\Downarrow\ \text{finite rational quotient and specialization}\\
\text{rigidity of a rational point in that cusp disk}.
\end{array} \tag{1.1}
$$

Every arrow is integral. A rational decomposition of a Jacobian is not enough, because denominators can destroy a cotangent direction after reduction.

### 1.2 Prime-level notation

Let $N\ge 5$ be prime. Write

$$
X_0=X_0(N),\qquad X_1=X_1(N),\qquad J=J_0(N).
$$

The map

$$
\rho:X_1\longrightarrow X_0,
\qquad(E,P)\longmapsto(E,\langle P\rangle) \tag{1.2}
$$

forgets the generator but retains its cyclic subgroup. It is a finite map of compactified curves. We work over $\mathbf Z[1/N]$, where the point-level and cyclic-level compactifications have their good integral meaning.

Let $\mathbb T$ be the faithful Hecke algebra acting on $J$, with $T_q$ for primes $q\ne N$ and incoming operator $U_N$. Its Eisenstein ideal and exact index are

$$
I=(T_q-(1+q):q\ne N)+(U_N-1), \tag{1.3}
$$

$$
\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z,
\qquad
n_N=\frac{N-1}{\gcd(N-1,12)}. \tag{1.4}
$$

Fix a prime $\ell\mid n_N$ and put

$$
\mathfrak m=(\ell,I).
$$

Books 145 and 146 construct the selected optimal quotient

$$
\pi:J\twoheadrightarrow A_{\mathfrak m}, \tag{1.5}
$$

distinguish its rational support from the completed idempotent $e_{\mathfrak m}$, and prove

$$
A_{\mathfrak m}(\mathbf Q)\text{ is finite}. \tag{1.6}
$$

We abbreviate $A=A_{\mathfrak m}$ when the selected maximal ideal is fixed.

Our Frobenius convention remains arithmetic. Our correspondence action on Jacobians is covariant:

$$
T=(\pi_2)_*\pi_1^*.
$$

Pullback on invariant differentials is contravariant and agrees with the normalized weight-two Hecke action. These conventions are the ones fixed in Books 119 and 121.

### 1.3 The proof architecture

There are four distinct pieces.

First, over every good localization $R=\mathbf Z_r$ with $r\ne N$, the optimal quotient extends to an exact sequence of abelian schemes

$$
0\longrightarrow\mathcal K\longrightarrow\mathcal J
\xrightarrow{\pi}\mathcal A\longrightarrow0. \tag{1.7}
$$

Smoothness of the quotient makes the induced cotangent sequence exact. Consequently $\pi^*\omega_{\mathcal A/R}$ is a primitive sublattice of $\omega_{\mathcal J/R}$.

Second, Book 121 identifies $\omega_{\mathcal J/R}$ with the regular dualizing differentials on the modular curve, and Book 119 identifies these at good level with integral weight-two cusp forms. If a primitive differential remains nonzero modulo $r$, its expansion at a cusp is nonzero. Some coefficient is therefore a unit modulo $r$. A Hecke operator moves that coefficient into the first position.

Third, the first coefficient is the cotangent of the Abel--Jacobi map at the cusp. At the outward oriented $\Gamma_1$ cusp, forgetting the generator preserves the smoothing parameter. The resulting map $X_1\to A$ is therefore a formal immersion after a suitable Hecke translate.

Fourth, take $r=3$. A rational point of exact prime order $N\ge17$ reduces either to an interior elliptic curve over $\mathbf F_3$ or to an oriented cusp. The first alternative contradicts the Hasse bound. In the second, the chosen generator must point along the component group rather than the multiplicative identity component; it therefore reaches a rational outward cusp. Finiteness of $A(\mathbf Q)$ and odd-prime specialization make its Abel image zero, while formal immersion makes the original section equal to the cusp.

The level $11$ calculation is kept separate because it is a complete genus-one problem. The level $13$ curve has trivial Eisenstein index and falls outside the selected-quotient construction. It is one of the two genus-two rational-point problems isolated at the end.

### 1.4 The boundaries of the argument

Several tempting strengthenings are neither needed nor justified.

We do not claim that the rational projector defining $A$ is an integral idempotent. A coefficient field can have several places above $\ell$. The rational quotient retains every companion place, while $e_{\mathfrak m}$ selects one completed factor.

We do not claim that $I$ itself annihilates $A(\mathbf Q)$. Book 146 proves Eisenstein support and a power annihilator; formal immersion uses only finiteness.

We do not infer injectivity of torsion specialization at $2$ from good reduction. The uniform rational-point application is made at $3$, where the kernel of reduction of an abelian variety over the unramified field $\mathbf Q_3$ is torsion-free.

We do not forget the generator before analyzing the cusp. On $X_0(N)$ the subgroup is unoriented. On $X_1(N)$ the rational generator distinguishes an outward component direction from an inward multiplicative direction. This distinction is exactly what makes the reached cusp rational.

Finally, the formal-immersion theorem is not a classification of all rational points of $X_1(N)$. It controls a section already known to lie in a specified oriented cusp disk. The reduction argument supplies that hypothesis in the prime-order application.

## 2. Formal immersions and sections over a discrete valuation ring

### 2.1 Completed local rings and cotangent spaces

Let $k$ be a field, let $f:Y\to Z$ be a morphism locally of finite type, and let $y\in Y(k)$ map to $z\in Z(k)$. The morphism is a **formal immersion at $y$** if

$$
\widehat{\mathcal O}_{Z,z}\longrightarrow
\widehat{\mathcal O}_{Y,y} \tag{2.1}
$$

is surjective. The direction is worth noticing: functions on the target restrict to enough functions to generate the entire formal neighborhood of $y$ in the source.

Let $\mathfrak m_y$ and $\mathfrak m_z$ be the maximal ideals. Surjectivity of (2.1) implies surjectivity on cotangent spaces

$$
\mathfrak m_z/\mathfrak m_z^2
\longrightarrow
\mathfrak m_y/\mathfrak m_y^2. \tag{2.2}
$$

The converse holds when the residue fields agree. Choose elements of $\mathfrak m_z$ whose images span the right side of (2.2). Their images generate $\mathfrak m_y$ by Nakayama's lemma. Inductively they generate every quotient

$$
\mathcal O_{Y,y}/\mathfrak m_y^n.
$$

Passing to the inverse limit proves (2.1). This is the cotangent criterion established abstractly in Book 9.

For a smooth curve, the target of (2.2) has dimension one. It is therefore enough to find one target differential whose pullback is nonzero at $y$. The whole formal-neighborhood statement has been reduced to one coefficient.

### 2.2 A relative cotangent criterion

We need a version over a discrete valuation ring. Let $R$ be a complete DVR with residue field $k$. Let $Y$ and $Z$ be separated finite-type $R$-schemes, let $y:\operatorname{Spec}R\to Y$ be a section, and put $z=f\circ y$. Assume $Y$ is smooth over $R$ of relative dimension one at the special point $\bar y$ and $Z$ is smooth over $R$ at $\bar z$.

**Proposition 2.1 (relative formal-immersion criterion).** If the special-fiber cotangent map

$$
\bar z^*\Omega^1_{Z_k/k}
\longrightarrow
\bar y^*\Omega^1_{Y_k/k} \tag{2.3}
$$

is surjective, then $f_k$ is a formal immersion at $\bar y$. Moreover the induced map between completions along the two sections is surjective after the common base parameter is retained.

**Proof.** The first assertion is the field-valued cotangent criterion. For the relative statement, write $\pi$ for a uniformizer of $R$. Smoothness gives regular completed local rings

$$
\widehat{\mathcal O}_{Y,\bar y}\simeq R[[t]],
$$

and a power-series presentation of the completed target. The image of the relative cotangent map contains a generator of $(t)/(\pi,t)^2$ by (2.3), while the base map already contains $\pi$. Hence the images of $\pi$ and suitable target parameters generate the maximal ideal $(\pi,t)$. Nakayama's lemma gives surjectivity modulo every power of that ideal. Completeness gives surjectivity of the completed map. $\square$

The proposition is insensitive to replacing $R$ by its strict henselization and completion. Thus residue fields can first be split and the conclusion descended.

### 2.3 Separation of two sections

Formal immersion becomes useful through the following rigidity lemma.

**Lemma 2.2 (section separation).** In the setting of Proposition 2.1, suppose $y_1,y_2\in Y(R)$ have the same special point $\bar y$, and suppose

$$
f(y_1)=f(y_2)\quad\text{in }Z(R). \tag{2.4}
$$

If $f_k$ is a formal immersion at $\bar y$, then $y_1=y_2$.

**Proof strategy.** Both sections define maps from the completed local ring of $Y$ to $R$. Equality of their images in $Z$ says that the two maps agree on the image of the completed local ring of $Z$. Surjectivity says that image is the whole completed local ring of $Y$.

**Proof.** Because the sections have the same special point, each factors uniquely through

$$
\operatorname{Spf}\widehat{\mathcal O}_{Y,\bar y}.
$$

They give continuous $R$-algebra homomorphisms

$$
s_1^*,s_2^*:\widehat{\mathcal O}_{Y,\bar y}\longrightarrow R.
$$

Equation (2.4) says that their composites with the surjection from the completed target ring agree. Therefore $s_1^*=s_2^*$. The sections agree on the formal neighborhood of the closed fiber. Since $Y$ is separated over $R$, they agree as $R$-sections. $\square$

This proof is stronger than a tangent-vector argument. It excludes two sections agreeing to first order but separating at higher order because formal immersion gives the entire completed ring, not only its first infinitesimal quotient.

### 2.4 Why equality on the special fiber is insufficient

Consider the identity map from the affine line to a point after reduction. Every pair of sections with values in the maximal ideal has the same special point, but the sections are plainly different. Reduction has forgotten all higher powers of the uniformizer.

Even an injective tangent map does not separate sections unless it comes from a formal immersion at their common special point and their target images are equal. Conversely, equality of target images does not help if the target map is constant to first order. Both hypotheses in Lemma 2.2 are essential.

In the modular application, the equality of target images comes from the finite rational group and specialization. The formal immersion comes from a unit Fourier coefficient. Keeping these roles separate prevents a circular assertion that a point equals the cusp merely because both reduce there.

## 3. The oriented $\Gamma_1$ cusp

### 3.1 Point level and cyclic level

An object of $Y_1(N)$ is an elliptic curve $E$ with a point $P$ of exact order $N$. Its image on $Y_0(N)$ is the cyclic subgroup $C=\langle P\rangle$. The map $\rho$ in (1.2) forgets the choice of generator.

At the compactified boundary, an elliptic curve is replaced by a generalized elliptic curve. A cusp of $X_1(N)$ therefore remembers more than a cusp of $X_0(N)$: it remembers where the chosen generator lies on the smooth part of a polygon. This is the **orientation**.

Over a base on which $N$ is invertible, the standard split $N$-gon has smooth part fitting into

$$
0\longrightarrow\mathbf G_m
\longrightarrow E^{\mathrm{sm}}
\longrightarrow\mathbf Z/N\mathbf Z
\longrightarrow0. \tag{3.1}
$$

A point of exact order $N$ can point in the multiplicative direction, in the component direction, or in a mixture of the two. At a cusp rational over the ground ring, the component direction is the important one.

### 3.2 The two kinds of cusp

On a Tate curve, an $N$-torsion point can be represented after a suitable extension by

$$
u=\zeta_N^a q^{b/N},
\qquad(a,b)\in(\mathbf Z/N\mathbf Z)^2\setminus\{(0,0)\}. \tag{3.2}
$$

The integer $b$ records the component reached in the limiting $N$-gon; $a$ records the multiplicative coordinate. For prime $N$, an exact-order point has $(a,b)\ne(0,0)$.

There are two boundary types after the usual identifications.

- If $b\ne0$, rescale the generator so that $b=1$. The point meets a generator of the component group. We call this the **outward** or **component-oriented** cusp.

- If $b=0$, then $a\ne0$ and the point is a primitive root of unity in the identity component. We call this the **inward** or **multiplicative-oriented** cusp.

The terminology is geometric rather than topological. Outward means that the level point survives in the component group of the polygon; inward means that it remains inside the torus.

The two types behave differently under forgetting the generator. At an outward cusp, the cyclic subgroup meets every component and its image on $X_0(N)$ is the cusp customarily denoted $\infty$ after choosing the standard orientation. At an inward cusp, the subgroup is multiplicative and maps to the other cyclic-level cusp. Atkin--Lehner interchanges the two cyclic-level cusps, but it does not erase the point-level orientation.

### 3.3 The outward cusp parameter

Let $c$ be an outward cusp. The completed point-level chart has a Tate parameter $q$ and a chosen section represented by $q^{1/N}$ on the $N$-gon. Forgetting the generator leaves the underlying Tate generalized elliptic curve and its smoothing parameter unchanged. Consequently

$$
\widehat{\mathcal O}_{X_0,\rho(c)}
\longrightarrow
\widehat{\mathcal O}_{X_1,c}
$$

sends

$$
q\longmapsto u q \tag{3.3}
$$

for a unit $u$ determined by the chosen frames. After choosing compatible standard frames, $u=1$.

**Proposition 3.1.** Over $\mathbf Z[1/N]$, the forgetful map $\rho$ is unramified at every outward cusp, and the induced map on relative cotangent lines is an isomorphism.

**Proof.** The deformation of the split polygon with its component-oriented point is the deformation of the polygon itself. The component label is finite étale data because $N$ is invertible, so it lifts uniquely across nilpotent thickenings. Thus no new infinitesimal parameter appears and no old parameter is raised to a power. The Tate calculation gives (3.3), whose linear term is a unit. This proves the cotangent assertion and hence unramifiedness. $\square$

At an inward cusp the natural parameter on one side can be an $N$th root of the parameter on the other. The map can be ramified, and a cotangent direction from $X_0(N)$ need not detect it. This is why the theorem is stated at the outward oriented cusp rather than at an unspecified point-level cusp.

### 3.4 Rationality and reduction of the orientation

The outward cusps are rational. Indeed the standard split $N$-gon, its identity, and the section meeting component $1$ are defined over $\mathbf Z[1/N]$. Multiplying the component label by

$$
a\in(\mathbf Z/N\mathbf Z)^\times
$$

gives the other outward cusps. On the coarse point-level curve the involution $(E,P)\simeq(E,-P)$ identifies $a$ and $-a$, so there are $(N-1)/2$ rational outward cusps.

The inward cusp requires a primitive $N$th root of unity in the torus. Its field of definition is cyclotomic in general. This field-of-definition distinction supplies a useful reduction test.

**Lemma 3.2 (orientation test).** Let $r\ne N$ be prime. Suppose a $\mathbf Q_r$-rational point of exact order $N$ on a Tate generalized elliptic curve specializes to the boundary. If its component index is zero, then $\mathbf F_r^\times$ contains an element of order $N$. In particular

$$
N\mid r-1. \tag{3.4}
$$

If $N\nmid r-1$, the specialization is outward.

**Proof.** Component index zero means that the point specializes to the identity torus. Because $N$ is prime to $r$, the $N$-torsion of that torus is finite étale and reduction preserves exact order. Its special fiber is $\mu_N$. A rational point of exact order $N$ in $\mu_N(\mathbf F_r)$ exists only when $N\mid\#\mathbf F_r^\times=r-1$. The contrapositive proves the final assertion. $\square$

For $r=3$ and $N\ge5$, condition (3.4) is impossible. Thus every rational prime-order point that reaches the boundary at $3$ reaches a rational outward cusp. This elementary orientation test is the bridge from specialization to the exact cusp where the cotangent theorem applies.

## 4. Cotangent lattices of optimal Eisenstein quotients

### 4.1 The exact abelian quotient

The selected quotient is defined by rational Hecke support, but its integral usefulness comes from optimality. Let

$$
0\longrightarrow K\longrightarrow J
\xrightarrow{\pi}A\longrightarrow0 \tag{4.1}
$$

be the selected optimal quotient over $\mathbf Q$. Its kernel $K$ is connected. Book 145 proves that, over

$$
S=\operatorname{Spec}\mathbf Z[1/N],
$$

the good-reduction abelian schemes form an fppf exact sequence

$$
0\longrightarrow\mathcal K\longrightarrow\mathcal J
\xrightarrow{\pi}\mathcal A\longrightarrow0. \tag{4.2}
$$

The quotient map is smooth and faithfully flat. Smoothness follows either because its kernel is the abelian scheme $\mathcal K$, or from the fiberwise criterion: every geometric fiber is a surjective homomorphism of abelian varieties with smooth connected kernel.

This exactness is stronger than extension of a generic endomorphism to Néron models. A generic isogeny can have a nonfinite Néron kernel at a bad prime. Here we have restricted away from $N$, and the quotient is the actual optimal quotient with its connected kernel. These are precisely the hypotheses under which its cotangent sequence is an exact sequence of vector bundles.

Let

$$
\omega_{\mathcal B/S}=e_{\mathcal B}^*\Omega^1_{\mathcal B/S}
$$

for an abelian scheme $\mathcal B/S$. Pullback along (4.2) gives

$$
0\longrightarrow\omega_{\mathcal A/S}
\xrightarrow{\pi^*}\omega_{\mathcal J/S}
\longrightarrow\omega_{\mathcal K/S}
\longrightarrow0. \tag{4.3}
$$

To verify (4.3), take the conormal sequence of $\mathcal K\to\mathcal J\to\mathcal A$ at the identity. Smoothness makes the relative conormal term locally free and kills the possible right-hand obstruction. Fiberwise, (4.3) is dual to the exact tangent sequence of smooth algebraic groups. Since all terms are vector bundles and the fiber sequence is exact, the relative sequence is exact.

### 4.2 Primitive invariant differentials

Let $r\ne N$ and base change (4.3) to $R=\mathbf Z_r$. Put

$$
\Omega_{A,r}=\pi^*\omega_{\mathcal A/R}
\subseteq\omega_{\mathcal J/R}. \tag{4.4}
$$

A submodule $L\subset M$ of a finite free module over a DVR is **primitive** or **saturated** if $M/L$ is torsion-free. Equation (4.3) identifies the quotient in (4.4) with the finite free module $\omega_{\mathcal K/R}$. Therefore $\Omega_{A,r}$ is primitive.

This elementary consequence of exactness is the first cotangent comparison. It has three important corollaries.

First, reduction is injective:

$$
\Omega_{A,r}/r\Omega_{A,r}
\hookrightarrow
\omega_{\mathcal J/R}/r\omega_{\mathcal J/R}. \tag{4.5}
$$

Second, the image has dimension $\dim A$ on every geometric fiber. Thus a positive-dimensional quotient always supplies a nonzero reduced differential.

Third, the image commutes with arbitrary base change from $R$. Indeed (4.3) is a short exact sequence of locally free modules, so tensoring remains exact. No adjacent-cohomology obstruction occurs at this stage.

Primitivity would not follow from an inclusion

$$
\omega_A\otimes\mathbf Q_r\subseteq\omega_J\otimes\mathbf Q_r.
$$

For example, $rR\subset R$ has the same rational span as $R$ but becomes zero after mapping to the quotient $R/rR$. Formal immersion is exactly sensitive to this loss. The integral exact sequence prevents it.

### 4.3 Comparison with the completed Hecke piece

Now take $r=\ell$, the residue characteristic of the selected Eisenstein maximal ideal. The complete local factor has an idempotent

$$
e=e_{\mathfrak m}\in\mathbb T\otimes\mathbf Z_\ell.
$$

Book 145 proves the saturated Tate comparison

$$
eT_\ell J\xrightarrow{\sim}eT_\ell A \tag{4.6}
$$

and, more strongly, equality of the selected finite-flat torsion towers over $S$. The same finite-flat equality controls cotangents.

For an abelian scheme $B/\mathbf Z_\ell$, the cotangent module of its $\ell$-divisible group at the identity is canonically $\omega_{B/\mathbf Z_\ell}$. At finite level, the conormal module of $B[\ell^n]$ maps onto the same invariant differential module, and the compatible limit recovers it. An idempotent acts on these conormal modules and hence on $\omega_B$.

Applying $e$ to the finite-flat comparison of Book 145 gives

$$
e\bigl(\omega_{\mathcal J/\mathbf Z_\ell}\bigr)
\xrightarrow{\sim}
e\bigl(\omega_{\mathcal A/\mathbf Z_\ell}\bigr). \tag{4.7}
$$

Here the map is induced by $\pi^*$, with the action on differentials interpreted contravariantly. To see the kernel directly, apply $e$ to (4.3). The selected finite-flat part of $\mathcal K[\ell^n]$ is zero at every $n$ by the saturation theorem. Its conormal module is therefore zero, so

$$
e\omega_{\mathcal K/\mathbf Z_\ell}=0.
$$

Exactness of the direct-summand functor $e(-)$ turns (4.3) into (4.7).

Equation (4.7) is the **completed cotangent comparison**. It says that the selected completed direction is identical on the Jacobian and on the optimal quotient, including its integral lattice. It does not say that the whole cotangent module of $A$ is the $e$-summand.

### 4.4 Companion factors and what is actually selected

Let

$$
\mathbb T_{\mathbf Q}=\prod_iK_i
$$

be the rational Hecke algebra. A field $K_i$ can have several places above $\ell$. The rational projector $E$ defining $A$ retains all of $K_i$ if even one of those places lies under $\mathfrak m$. The completed idempotent $e$ retains only the chosen local factors. Thus

$$
eE=e,
$$

but generally $e\ne E\otimes1$.

On cotangents this yields two honest statements:

$$
\Omega_{A,r}\subseteq\omega_{\mathcal J/\mathbf Z_r}
\quad\text{is the primitive lattice of the rational support}, \tag{4.8}
$$

and

$$
e\Omega_{A,\ell}=e\omega_{\mathcal J/\mathbf Z_\ell}
\quad\text{is the exact completed selected lattice}. \tag{4.9}
$$

They answer different questions. Formal immersion needs only a nonzero primitive differential in (4.8), so it can be checked in any good residue characteristic $r$. Descent at the Eisenstein prime uses (4.9), so that its finite-flat coefficients coincide with the selected part of the quotient. Treating (4.8) and (4.9) as the same decomposition would discard companion places or introduce a denominator.

## 5. Dualizing forms, Hecke operators, and the first coefficient

### 5.1 The canonical differential lattice

Fix $r\ne N$. Since $J_0(N)$ has good reduction at $r$, Book 121 identifies its invariant differentials with regular dualizing differentials on the compactified modular curve:

$$
\omega_{\mathcal J/\mathbf Z_r}
\simeq H^0(\mathcal X_0(N)_{\mathbf Z_r},
\omega_{\mathcal X_0(N)/\mathbf Z_r}). \tag{5.1}
$$

At good level, logarithmic Kodaira--Spencer from Book 119 identifies the right side with the integral weight-two cusp-form lattice

$$
S_2(\Gamma_0(N);\mathbf Z_r). \tag{5.2}
$$

The statement is interpreted on the compactified stack or a fine cover before descent. In characteristics two and three, one must retain the stabilizer action. The canonical Néron cotangent module ensures that the resulting lattice is independent of a coarse presentation.

Let $f\in\omega_{\mathcal J/\mathbf Z_r}$. At the standard cusp $\infty$, write its expansion as a regular differential

$$
f(q)\frac{dq}{q}
=\left(\sum_{n\ge1}a_n(f)q^n\right)\frac{dq}{q}
=\left(a_1(f)+a_2(f)q+\cdots\right)dq. \tag{5.3}
$$

There is no constant coefficient $a_0$ because $f$ is cuspidal. The coefficient $a_1(f)$ is exactly the value of the regular differential in the cotangent line at the cusp.

The expansion map is injective on the geometrically integral component containing $\infty$. Hence a nonzero reduction of $f$ has at least one nonzero coefficient.

### 5.2 The coefficient identity

For $m$ prime to $N$, the normalized weight-two Hecke formula gives

$$
a_n(T_mf)
=\sum_{d\mid(m,n)}d\,
a_{mn/d^2}(\langle d\rangle f). \tag{5.4}
$$

On $X_0(N)$ the diamond action is invisible. Taking $n=1$ leaves only $d=1$ and yields

$$
a_1(T_mf)=a_m(f). \tag{5.5}
$$

If $N\mid m$, write $m=N^bs$ with $(s,N)=1$. The incoming operator has expansion

$$
a_n(U_Nf)=a_{Nn}(f). \tag{5.6}
$$

Repeatedly applying (5.6) and then (5.5) gives an integral Hecke operator $T_m=U_N^bT_s$ satisfying

$$
a_1(T_mf)=a_m(f) \tag{5.7}
$$

for every $m\ge1$.

The equality uses the incoming normalization $U_N$, the same one for which $U_N-1$ belongs to the Eisenstein ideal. Replacing it by the adjoint outgoing operator would alter (5.6) and the cusp orientation.

### 5.3 Finding a unit coefficient

Let $L\subseteq\omega_{\mathcal J/\mathbf Z_r}$ be a nonzero primitive Hecke-stable sublattice. Choose

$$
0\ne\bar f\in L/rL.
$$

Primitivity makes its image in the full differential lattice nonzero. Q-expansion injectivity gives an integer $m\ge1$ such that

$$
a_m(\bar f)\ne0\quad\text{in }\mathbf F_r. \tag{5.8}
$$

Lift $\bar f$ to $f\in L$. Then $a_m(f)$ is a unit of $\mathbf Z_r$. Hecke stability puts $T_mf$ back in $L$, and (5.7) gives

$$
a_1(T_mf)=a_m(f)\in\mathbf Z_r^\times. \tag{5.9}
$$

This is the coefficient-moving lemma. It requires neither a normalized eigenform nor freeness of $L$ over a local Hecke algebra. It uses only primitivity, Hecke stability, and q-expansion injectivity.

It also explains why the Hecke translate may depend on $r$. A primitive lattice can contain a differential whose first coefficient is divisible by $r$ even though a later coefficient is a unit. Moving the first nonzero reduced coefficient to position one is the uniform remedy.

### 5.4 Small characteristics and integral reduction

At $r=2$ or $3$, a rational q-series with integral-looking coefficients is not by itself a proof that a differential lies in the Néron cotangent lattice. Stabilizer characters can merge, and a coarse curve can miss a stack correction. Our proof avoids this mistake in two ways.

First, the lattice $\omega_{\mathcal J/\mathbf Z_r}$ is defined intrinsically from the abelian scheme. Book 121 compares it with regular dualizing differentials, including the residue conditions at singular stack charts.

Second, primitivity comes from the exact sequence of abelian schemes, not from coefficientwise divisibility. After that integral fact is established, Book 119's q-expansion principle is used only to detect a nonzero section and a unit coefficient.

Thus (5.9) remains valid at $3$, the characteristic used in the rational-point application. No averaging by a stabilizer order and no division by $2$ or $3$ occurs.

## 6. The selected cotangent theorem

### 6.1 Statement of the comparison

We now collect the preceding arguments in the form used by formal immersion.

**Theorem 6.1 (integral cotangent comparison for a selected Eisenstein quotient).** Let $N$ be prime, let $\ell\mid n_N$, let $\mathfrak m=(\ell,I)$, and let

$$
\pi:J_0(N)\twoheadrightarrow A_{\mathfrak m}
$$

be the selected optimal quotient. For every prime $r\ne N$:

1. pullback identifies $\omega_{\mathcal A/\mathbf Z_r}$ with a primitive Hecke-stable sublattice
   $$
   \Omega_{\mathfrak m,r}
   \subseteq S_2(\Gamma_0(N);\mathbf Z_r);
   $$
2. the quotient lattice is canonically $\omega_{\mathcal K/\mathbf Z_r}$ and is finite free;
3. formation of $\Omega_{\mathfrak m,r}$ commutes with reduction and every extension of $\mathbf Z_r$;
4. if $A_{\mathfrak m}$ is nonzero, then for some $m\ge1$ there is
   $$
   f\in\Omega_{\mathfrak m,r}
   \quad\text{with}\quad
   a_1(T_mf)=a_m(f)\in\mathbf Z_r^\times;
   \tag{6.1}
   $$
5. at $r=\ell$, the completed selected cotangent is exactly
   $$
   e_{\mathfrak m}\omega_{\mathcal J/\mathbf Z_\ell}
   \xrightarrow{\sim}
   e_{\mathfrak m}\omega_{\mathcal A/\mathbf Z_\ell}.
   \tag{6.2}
   $$

The theorem makes no multiplicity-one or rank-two assertion.

### 6.2 Proof of primitivity and base change

**Proof of Theorem 6.1, items 1--4.** Book 145 supplies the exact sequence (4.2). Its cotangent sequence is (4.3). After base change to $\mathbf Z_r$, the image of $\pi^*$ has finite free quotient $\omega_{\mathcal K/\mathbf Z_r}$, proving primitivity and item 2. Exactness of a sequence of vector bundles survives arbitrary base change, proving item 3.

Book 121 identifies the middle cotangent module with the canonical dualizing differential lattice, and Book 119 identifies that lattice at good level with integral weight-two cusp forms. Hecke endomorphisms descend to $A$ because its rational support is Hecke stable; uniqueness of Néron extension makes the cotangent image Hecke stable. This proves item 1.

If $A\ne0$, its cotangent module has positive rank. Item 3 makes its reduction nonzero. Choose a nonzero reduced differential and apply the coefficient-moving argument of Section 5.3. This gives (6.1) and item 4. $\square$

The proof uses the whole optimal quotient lattice at $r$, not merely the chosen $\ell$-adic factor. This is legitimate and useful: a single nonzero companion differential suffices to produce formal immersion, while finiteness of the whole selected rational-support quotient is already known.

### 6.3 The selected summand at the Eisenstein prime

**Proof of Theorem 6.1, item 5.** The local idempotent $e_{\mathfrak m}$ acts on the finite-flat $\ell$-power torsion tower and on its conormal modules. Book 145 identifies the selected towers in $\mathcal J$ and $\mathcal A$ level by level. Passing to invariant differentials gives (6.2).

Equivalently, apply $e_{\mathfrak m}$ to (4.3). The selected torsion of $\mathcal K$ is zero because

$$
e_{\mathfrak m}T_\ell K=0.
$$

The selected conormal module of $\mathcal K[\ell^n]$ is therefore zero at every level, and so $e_{\mathfrak m}\omega_{\mathcal K}=0$. Exactness gives the asserted isomorphism. $\square$

The use of conormal modules is important. A statement only about rational Tate spaces would show equality after tensoring with $\mathbf Q_\ell$ but would not exclude an $\ell$-power index between the cotangent lattices.

### 6.4 A failure ledger for rational projectors

The theorem excludes four common errors.

1. A rational projector need not preserve the integral cotangent lattice. Its denominator can be divisible by $r$.

2. A primitive quotient of rational homology does not automatically give a primitive Néron cotangent inclusion. Here primitivity is proved from the exact sequence of abelian schemes.

3. Equality of selected Tate spaces after tensoring with $\mathbf Q_\ell$ does not imply equality of finite-flat towers or cotangent lattices. Book 145's saturated comparison supplies the integral statement.

4. Faithfulness of the completed Hecke action does not make the cotangent module free of rank one over $\mathbb T_{\mathfrak m}$. No such freeness is needed to find the coefficient in (6.1).

These distinctions are what allow the argument to include ramified coefficient fields, several characteristic-zero branches, and the small Eisenstein primes without a hidden multiplicity hypothesis.

## 7. Formal immersion at an oriented cusp

### 7.1 The pointed map to the selected quotient

Let $c\in X_1(N)(\mathbf Z[1/N])$ be an outward cusp and let

$$
c_0=\rho(c)\in X_0(N)(\mathbf Z[1/N]).
$$

Use $c_0$ as the Abel--Jacobi base point:

$$
j_{c_0}:X_0(N)\longrightarrow J_0(N),
\qquad x\longmapsto[x-c_0]. \tag{7.1}
$$

Define

$$
h=\pi\circ j_{c_0}\circ\rho:X_1(N)\longrightarrow A. \tag{7.2}
$$

Then $h(c)=0$. Every Hecke operator acting on $A$ gives a translate

$$
h_m=T_m\circ h. \tag{7.3}
$$

The phrase “Hecke translate” refers to composition on the target, not to moving the cusp on the source. Since $T_m(0)=0$, one still has $h_m(c)=0$.

Over $\mathbf Z_r$ with $r\ne N$, the curve is smooth at the cusp and $\mathcal A$ is an abelian scheme. Thus (7.2)--(7.3) extend to the relevant integral neighborhoods. This follows from the integral Abel map on the smooth locus and the Néron mapping property, or directly from the Cartier divisor $x-c_0$.

### 7.2 The cotangent calculation

Let $f\in\omega_{\mathcal A/\mathbf Z_r}$ and use the same letter for its primitive image in the differential lattice of $X_0(N)$. Pullback along the Abel map identifies invariant differentials on the Jacobian with the same regular differentials on the curve. Therefore

$$
h_m^*f=\rho^*(T_mf). \tag{7.4}
$$

At $c_0$, write

$$
T_mf=
\left(a_1(T_mf)+a_2(T_mf)q+\cdots\right)dq. \tag{7.5}
$$

At the outward point-level cusp, Proposition 3.1 gives $q=ut+O(t^2)$ with $u$ a unit and $t$ a local parameter on $X_1(N)$. Pulling back (7.5) gives

$$
h_m^*f=
\left(u\,a_1(T_mf)+O(t)\right)dt. \tag{7.6}
$$

If $a_1(T_mf)$ is a unit modulo $r$, then (7.6) spans the cotangent line of $X_1(N)_{\mathbf F_r}$ at $c$. The induced map

$$
\omega_{\mathcal A/\mathbf Z_r}\otimes\mathbf F_r
\longrightarrow
\Omega^1_{X_1(N)_{\mathbf F_r}/\mathbf F_r,c} \tag{7.7}
$$

is surjective. The cotangent criterion of Chapter 2 then makes $h_m$ a formal immersion at the special cusp.

### 7.3 The oriented formal-immersion theorem

**Theorem 7.1 (oriented Eisenstein formal immersion).** Let $N$ be prime with $n_N>1$. Choose $\ell\mid n_N$ and the selected optimal quotient $A_{\mathfrak m}$ for $\mathfrak m=(\ell,I)$. Let $c$ be any outward rational cusp of $X_1(N)$. For every prime $r\ne N$, there is an integer $m\ge1$ such that

$$
h_m:X_1(N)_{\mathbf Z_r}\longrightarrow
\mathcal A_{\mathfrak m,\mathbf Z_r}
$$

is a formal immersion at the reduction of $c$.

**Proof.** Because $\ell\mid n_N$, the completed Eisenstein piece is nonzero: its finite level contains the nonzero $\ell$-primary cuspidal subgroup established in Book 145. Hence $A_{\mathfrak m}$ has positive dimension.

Apply Theorem 6.1 at $r$. It gives $f$ in the primitive quotient cotangent lattice and $m\ge1$ such that $a_1(T_mf)$ is a unit. Equation (7.6) shows that $h_m^*f$ is nonzero in the one-dimensional cotangent line at $c$. Thus (7.7) is surjective. Proposition 2.1 gives the formal immersion. $\square$

The theorem holds in every good residue characteristic, including $2$ and $3$, as a statement about cotangents. Its rational-point consequence will be stated at odd $r$ because that later step also requires injectivity of torsion specialization on the quotient.

### 7.4 Uniformity and the role of the Hecke translate

The quotient $A_{\mathfrak m}$ and the cusp $c$ are fixed, while $m$ may depend on $r$. This is sufficient. A formal-immersion argument at one residue prime needs one map with a unit cotangent there.

There need not be a single differential in $\Omega_{\mathfrak m,r}$ whose first coefficient is a unit for every $r$. Nor need a chosen normalized eigenform lie integrally in the quotient lattice at every prime. The coefficient-moving lemma replaces both unsupported assertions by a finite, local choice.

The argument also works at every outward cusp. Multiplication of the component orientation by $a\in(\mathbf Z/N\mathbf Z)^\times$ is a diamond automorphism of $X_1(N)$. It changes the standard frame by a unit, so nonvanishing of (7.6) is preserved. The required Hecke translate can be transported along that automorphism.

## 8. Specialization of finite rational points

### 8.1 The kernel of reduction at an odd good prime

Formal immersion separates sections once their target images are equal. Finiteness of the target produces that equality through specialization.

Let $B/\mathbf Q$ be an abelian variety with good reduction at an odd prime $r$, and let $\mathcal B/\mathbf Z_r$ be its abelian scheme. Reduction gives

$$
\operatorname{red}:B(\mathbf Q_r)=\mathcal B(\mathbf Z_r)
\longrightarrow\mathcal B(\mathbf F_r). \tag{8.1}
$$

**Proposition 8.1 (torsion injectivity at an odd unramified prime).** The kernel of (8.1) contains no nonzero torsion point. Consequently reduction is injective on every finite subgroup of $B(\mathbf Q)$.

**Proof strategy.** Prime-to-$r$ torsion cannot lie in the formal group because the reduction kernel is pro-$r$. The $r$-primary part is excluded by the formal logarithm, which identifies the kernel with an additive $r$-adic lattice when $r$ is odd.

**Proof.** The reduction kernel $B_1(\mathbf Q_r)$ is the group of $\mathbf Z_r$-points of the formal completion of $\mathcal B$ at the identity. Its filtration by powers of the maximal ideal has successive quotients isomorphic to the additive group of the tangent space over $\mathbf F_r$. Hence it is a pro-$r$ group. A torsion point of order prime to $r$ in this kernel is therefore zero.

Choose formal parameters $X_1,\ldots,X_g$. Because $r$ is odd, the formal logarithm converges on the maximal ideal and gives a group isomorphism

$$
\log_{\mathcal B}:B_1(\mathbf Q_r)
\xrightarrow{\sim}(r\mathbf Z_r)^g \tag{8.2}
$$

after a harmless integral linear change of parameters. Its linear term is the identity, and the denominators in higher terms have valuation dominated by the powers of the parameters. The additive group on the right is torsion-free, so the $r$-primary torsion in $B_1(\mathbf Q_r)$ is also zero. This proves the first assertion. A finite subgroup of $B(\mathbf Q)$ embeds in $B(\mathbf Q_r)$, so the second follows. $\square$

At a ramified extension of $\mathbf Q_r$, shallow torsion can occur in a formal group. The unramified ground field and odd residue characteristic are both visible hypotheses in Proposition 8.1.

### 8.2 Cusp-disk rigidity for the selected quotient

Let $A=A_{\mathfrak m}$ and retain the map $h$ of (7.2). Book 146 proves that $A(\mathbf Q)$ is finite. Fix an odd prime $r\ne N$ and an outward rational cusp $c$. Suppose

$$
x\in X_1(N)(\mathbf Q)
$$

reduces to the same special point as $c$ modulo $r$.

The difference

$$
D=h(x)-h(c)=h(x)\in A(\mathbf Q) \tag{8.3}
$$

reduces to zero because the integral maps send the two sections to the same special point. It is torsion by finiteness of $A(\mathbf Q)$. Proposition 8.1 gives

$$
D=0. \tag{8.4}
$$

Choose the Hecke translate $h_m$ supplied by Theorem 7.1. Then

$$
h_m(x)=T_mh(x)=0=T_mh(c)=h_m(c). \tag{8.5}
$$

Both sections pass through the same special cusp, and $h_m$ is a formal immersion there. Lemma 2.2 gives $x=c$.

We have proved the exact rigidity statement.

**Theorem 8.2 (odd cusp-disk rigidity).** Let $N$ be prime with $n_N>1$, let $r$ be an odd prime different from $N$, and let $c$ be an outward rational cusp of $X_1(N)$. If

$$
x\in X_1(N)(\mathbf Q),
\qquad x\equiv c\pmod r,
$$

then $x=c$.

The theorem uses one selected Eisenstein quotient, for any choice of $\ell\mid n_N$. It does not require $x-c$ to lift to a rational torsion point on $J_0(N)$. The point already lies on the quotient, whose rational group is finite in its own right.

### 8.3 Why the argument is stated at an odd prime

The cotangent theorem itself remains valid at $r=2$. The obstruction is Proposition 8.1. The formal logarithm does not automatically identify the full first congruence kernel over $\mathbf Z_2$ with a torsion-free additive lattice. More importantly, knowing the rational torsion of $J_0(N)$ would not determine the specialization kernel on a quotient: a quotient torsion point need not lift to a rational torsion point upstairs.

One could establish a separate connected--étale theorem for the exact quotient at $2$, but no such theorem is needed here. The prime-order specialization argument works at $3$. Stating Theorem 8.2 at odd $r$ makes the input exact and prevents an accidental two-primary strengthening.

This boundary is independent of the dyadic admissibility in Book 145. Admissibility describes finite-flat constituents of the selected $2$-divisible group. It does not by itself say that every rational torsion point of the abelian quotient specializes injectively.

### 8.4 Compatibility with changing the oriented cusp

Let $c_a$ be the outward cusp with component label $a$. The diamond automorphism $\langle a\rangle$ on $X_1(N)$ carries $c_1$ to $c_a$. It commutes with the forgetful map up to the natural equality on cyclic subgroups. Therefore the diagram

$$
\begin{array}{ccc}
X_1(N)&\xrightarrow{\langle a\rangle}&X_1(N)\\
\downarrow h&&\downarrow h\\
A&=&A
\end{array}
$$

commutes after translating the pointed Abel map by its cusp value; that value is zero for either compatible base cusp. On completed local parameters, the diamond action multiplies the parameter by a unit. It follows that formal immersion and section separation transport from $c_1$ to $c_a$.

Thus Theorem 8.2 is not tied to a preferred label. A reduction argument may produce any rational outward orientation, and the same rigidity conclusion applies.

## 9. Reducing a rational prime-order point

### 9.1 The modular point attached to $(E,P)$

Let $p\ge5$ be prime, let $E/\mathbf Q$ be an elliptic curve, and suppose

$$
P\in E(\mathbf Q)
$$

has exact order $p$. The pair defines a noncuspidal rational point

$$
x(E,P)\in Y_1(p)(\mathbf Q). \tag{9.1}
$$

The adjective noncuspidal is essential: the generic fiber is a smooth elliptic curve, so the point lies in the open modular curve.

Fix a prime $r\ne p$. Properness of the compactified point-level curve extends $x(E,P)$ to an integral section after using the standard coarse descent. On a fine cusp chart, the section is represented by a generalized elliptic curve with its exact-order point. Since $p$ is invertible in $\mathbf Z_r$, the $p$-torsion is finite étale on the smooth locus, and exact order survives every interior specialization.

The special point is of one of two kinds:

1. it lies in the interior and represents an elliptic curve $\widetilde E/\mathbf F_r$ with a point $\widetilde P$ of exact order $p$;
2. it lies on the boundary and represents a polygon with an oriented point of exact order $p$.

The compactification is doing real work here. It replaces a possibly singular special Weierstrass equation by the stable modular object, so “boundary” means multiplicative generalized-elliptic reduction, not merely a singular equation chosen before minimization.

### 9.2 Interior reduction and the Hasse bound

In the first alternative,

$$
p\mid\#\widetilde E(\mathbf F_r). \tag{9.2}
$$

The Hasse bound gives

$$
\#\widetilde E(\mathbf F_r)
\le r+1+2\sqrt r. \tag{9.3}
$$

For $r=3$, the right side is less than $8$, so

$$
\#\widetilde E(\mathbf F_3)\le7. \tag{9.4}
$$

Therefore a rational point of prime order $p\ge11$ cannot have interior reduction at $3$.

The exact-order assertion in (9.2) deserves proof. Multiplication by $p$ is étale because $p\ne r$. If the reduction of $P$ had smaller order, a nonzero multiple $aP$ with $1\le a<p$ would reduce to the identity. It would lie in the kernel of reduction of the finite étale group $E[p]$, but finite étale sections over a henselian DVR are determined by their specializations. Hence $aP=0$, contradicting exact order $p$.

### 9.3 Multiplicative reduction and the outward direction

We are therefore in the boundary alternative at $r=3$ for every $p\ge11$. The oriented point can a priori lie in the toric identity component or meet a nonidentity component.

If it lies in the identity component, its reduction is a point of exact order $p$ in

$$
\mathbf G_m(\mathbf F_3)=\mathbf F_3^\times,
$$

which has order $2$. This is impossible for $p\ge5$. Equivalently, Lemma 3.2 gives the impossible divisibility $p\mid2$.

Thus the level point has nonzero component index. Since $p$ is prime, that index generates the component group after rescaling the chosen generator. The reduction is an outward component-oriented cusp.

There is no hidden second rational $p$-direction. If both an independent toric direction and a component direction were rational, their Weil pairing would give a rational primitive $p$th root of unity. For $p\ge5$ this cannot lie in $\mathbf Q$. In the present argument the simpler count in $\mathbf F_3^\times$ already excludes the toric direction, but the Weil-pairing observation explains why the orientation is intrinsic.

### 9.4 The rational oriented cusp reached at three

By Section 3.4, every outward cusp has a model over $\mathbf Z[1/p]$. Let $c_a$ be the one whose component label equals that of the reduction of $P$, modulo the identification $a\sim-a$ on the coarse point-level curve. Then

$$
x(E,P)\equiv c_a\pmod3. \tag{9.5}
$$

This is equality of special points, not merely equality after forgetting the generator. The component label is part of the point-level cusp data.

We summarize the specialization argument.

**Proposition 9.1 (oriented specialization at three).** Let $p\ge11$ be prime and let $P\in E(\mathbf Q)$ have exact order $p$. The corresponding point of $X_1(p)(\mathbf Q)$ reduces modulo $3$ to a rational outward cusp.

**Proof.** Interior reduction contradicts (9.2)--(9.4). Boundary reduction in the identity torus would give an order-$p$ point of $\mathbf F_3^\times$, also impossible. Hence the component index is nonzero, so the point reaches the rational outward cusp with that index. $\square$

The proposition alone does not rule out the rational point. It locates the residue disk. The formal-immersion theorem will show that, when an Eisenstein quotient exists, the only rational point in that disk is its cusp.

## 10. The uniform theorem for primes at least seventeen

### 10.1 The Eisenstein prime exists

For a prime $p$, put

$$
n_p=\frac{p-1}{\gcd(p-1,12)}. \tag{10.1}
$$

If $p=13$, then $n_p=1$. This is the exceptional level at which the selected Eisenstein construction is absent. If $p\ge17$, then $n_p>1$.

Indeed $n_{17}=4$. For $p\ge19$, one has $p-1\ge18$, while $\gcd(p-1,12)\le12$. Equality $n_p=1$ would require $p-1\mid12$, impossible. Thus $n_p$ has a prime divisor $\ell$, and

$$
\mathfrak m=(\ell,I)
$$

is an Eisenstein maximal ideal. The selected quotient $A_{\mathfrak m}$ is nonzero because its completed torsion contains the nonzero $\ell$-primary cuspidal line.

The prime $3$ used for specialization is always different from the level $p\ge17$. It may equal the selected Eisenstein prime $\ell$. This causes no problem: the cotangent comparison and finiteness theorem both include the coefficient prime integrally.

### 10.2 The uniform exclusion

We can now prove the uniform arithmetic theorem.

**Theorem 10.1 (uniform prime-order exclusion).** Let $p\ge17$ be prime. There is no elliptic curve over $\mathbf Q$ with a rational point of exact order $p$.

**Proof strategy.** The point reduces to a rational outward cusp modulo $3$. The selected quotient is finite on rational points and formally immersive at that cusp. Cusp-disk rigidity makes the point itself cuspidal, contradicting its modular origin from a smooth elliptic curve.

**Proof.** Suppose $P\in E(\mathbf Q)$ has exact order $p$, and let

$$
x=x(E,P)\in Y_1(p)(\mathbf Q).
$$

Proposition 9.1 gives an outward rational cusp $c$ such that

$$
x\equiv c\pmod3. \tag{10.2}
$$

Choose a prime $\ell\mid n_p$ and the selected quotient $A_{\mathfrak m}$. Book 146 gives

$$
A_{\mathfrak m}(\mathbf Q)\text{ finite}.
$$

Theorem 7.1 gives a Hecke translate of the pointed map $X_1(p)\to A_{\mathfrak m}$ that is a formal immersion at $c$ modulo $3$. Since $3$ is odd and is a good prime for the quotient, Theorem 8.2 applies to (10.2) and gives

$$
x=c.
$$

But $x$ lies in the open modular curve and $c$ lies in the boundary. This contradiction proves the theorem. $\square$

Every hypothesis has now been used. The threshold $17$ guarantees a nontrivial Eisenstein index. The prime $3$ guarantees both the Hasse exclusion and torsion-free formal reduction. The point-level orientation guarantees that the reached cusp is rational and that forgetting the generator is unramified there.

### 10.3 Exceptional index and residue-characteristic checks

The small-prime corrections in $n_p$ remain exactly those of Books 145 and 146:

$$
v_\ell(n_p)=
\begin{cases}
\max\{v_2(p-1)-2,0\},&\ell=2,\\
\max\{v_3(p-1)-1,0\},&\ell=3,\\
v_\ell(p-1),&\ell\ge5.
\end{cases} \tag{10.3}
$$

The proof needs only one prime divisor of $n_p$, but using the incorrect order $p-1$ would falsely create an Eisenstein factor at $p=13$. The denominator correction is therefore responsible for the genuine genus-two exception.

At $p=17$, the only Eisenstein prime is $2$, with depth two. The quotient and its finite rational group are still available, and the cotangent argument is performed at $r=3$, not at the dyadic coefficient prime. At $p=19$, the Eisenstein prime is $3$, the same as the specialization characteristic. The primitive cotangent theorem was proved integrally at the coefficient prime, so reduction remains nonzero and the proof still works.

No step divides by the order of a diamond group or by the degree of $X_1(p)\to X_0(p)$. Such divisions would fail in characteristics dividing $p-1$, precisely where Eisenstein congruences occur.

### 10.4 What the uniform theorem does and does not classify

Theorem 10.1 excludes prime-order rational points for $p\ge17$. It does not classify rational cyclic isogenies of degree $p$. A rational subgroup can be Galois stable without possessing a rational generator, so it defines a point of $X_0(p)$ but not of $X_1(p)$.

It also does not settle $p=13$, because $n_{13}=1$. No selected Eisenstein quotient exists at that level. Nor does the uniform theorem by itself settle the surviving small primes $2,3,5,7$, for which noncuspidal rational points do exist on $X_1(p)$.

The next chapter gives the required separate calculation at $p=11$. The final two chapters identify the genus-two problems that remain after the uniform and genus-one arguments: the complete rational-point problem on $X_1(13)$ and the mixed-seven problem arising when a rational point of order seven is combined with full rational two-torsion.

## 11. The genus-one calculation at level eleven

### 11.1 A model of $X_1(11)$

The uniform theorem was deliberately stated for $p\ge17$. At level $11$ the point-level curve has genus one and admits a complete elementary calculation.

**Proposition 11.1.** With a rational outward cusp as origin, $X_1(11)$ is the elliptic curve

$$
C_{11}:\quad y^2+y=x^3-x^2. \tag{11.1}
$$

Its discriminant is $-11$, and its five evident rational points are

$$
O,\quad(0,0),\quad(0,-1),\quad(1,0),\quad(1,-1). \tag{11.2}
$$

They are outward rational cusps.

**Proof strategy.** Put an elliptic curve with a marked point of order at least four in Tate normal form, impose the order-$11$ relation using the chord-and-tangent law, and normalize the resulting plane curve. The normalization is (11.1). Degeneration of the Tate discriminant identifies the points in (11.2) with the rational component-oriented cusps.

**Proof.** A pair $(E,P)$ with $P$ of order at least four and with nonsingular $E$ has a unique Tate normal form up to the standard scaling:

$$
E(b,c):\quad
Y^2+(1-c)XY-bY=X^3-bX^2,
\qquad P=(0,0), \tag{11.3}
$$

where $b\ne0$ and the discriminant is nonzero. Uniqueness follows by taking the tangent at $P$ as the line $Y=0$, sending $-P$ to the second intersection prescribed by the Weierstrass inverse, and scaling the remaining coordinates.

For a general Weierstrass equation, addition of distinct points $(x_1,y_1)$ and $(x_2,y_2)$ uses

$$
\lambda=\frac{y_2-y_1}{x_2-x_1},
\qquad
\nu=\frac{y_1x_2-y_2x_1}{x_2-x_1}, \tag{11.4}
$$

$$
x_3=\lambda^2+a_1\lambda-a_2-x_1-x_2,
\qquad
y_3=-(\lambda+a_1)x_3-\nu-a_3. \tag{11.5}
$$

The tangent formula is obtained by replacing the secant slope with the derivative of the Weierstrass equation. Starting with $(0,0)$ and applying (11.4)--(11.5) gives

$$
2P=(b,bc),\qquad
3P=(c,b-c),\qquad
4P=\left(
\frac{b(b-c)}{c^2},
\frac{b^2(c^2+c-b)}{c^3}
\right). \tag{11.5a}
$$

These formulas hold on the open set $bc\ne0$. They follow by one tangent addition and then two secant additions; direct substitution in (11.4)--(11.5) verifies every numerator and denominator. Continuing the same recurrence, the condition

$$
5P=-6P \tag{11.6}
$$

cuts out the exact order-$11$ locus after the factors $b=0$, the discriminant, and the lower-order loci are removed. Successive cancellation gives a smooth affine curve whose normalization is transformed by completing the square and the elementary substitutions arising from the two ratios of consecutive denominators into

$$
y^2+y=x^3-x^2.
$$

This calculation is reversible: substituting the recovered rational functions $b(x,y),c(x,y)$ in (11.3) makes (11.6) an identity, while (11.4)--(11.5) recover $(x,y)$ from a nondegenerate order-$11$ pair. Hence the two curves represent the same open moduli problem and have the same smooth compactification.

For (11.1), the Weierstrass coefficients are

$$
a_1=0,\quad a_2=-1,\quad a_3=1,
\quad a_4=a_6=0.
$$

Thus

$$
b_2=-4,\quad b_4=0,\quad b_6=1,\quad b_8=-1,
$$

and

$$
\Delta=-b_2^2b_8-27b_6^2+9b_2b_4b_6=16-27=-11. \tag{11.7}
$$

The model is therefore smooth away from $11$. The points in (11.2) satisfy the equation by substitution. In the Tate normalization, the boundary factors removed before (11.6) map to precisely these five points; equivalently, the cusp charts show that they are the five component labels in $(\mathbf Z/11\mathbf Z)^\times/\{\pm1\}$. Hence they are exactly the outward rational cusps. $\square$

The normalization calculation in the proof is a finite group-law calculation, not an appeal to a rational-point classification. Its role is to identify the modular curve and its rational boundary on one integral genus-one model.

### 11.2 Finiteness of its Mordell--Weil group

Let $J_1(11)=\operatorname{Jac}(X_1(11))$. Choosing $O$ in (11.2) identifies

$$
X_1(11)\simeq J_1(11) \tag{11.8}
$$

as a genus-one curve with its Jacobian.

The forgetful map

$$
\rho:X_1(11)\longrightarrow X_0(11)
$$

is nonconstant. Pullback and norm induce nonzero homomorphisms between the two one-dimensional Jacobians. A nonzero homomorphism of elliptic curves is an isogeny, so

$$
J_1(11)\sim J_0(11). \tag{11.9}
$$

At level $11$,

$$
n_{11}=\frac{10}{\gcd(10,12)}=5.
$$

The faithful Hecke algebra of the one-dimensional $J_0(11)$ has a nonzero selected maximal ideal $(5,I)$. Its selected rational support is the whole elliptic curve. Book 146 therefore gives

$$
J_0(11)(\mathbf Q)\text{ finite}. \tag{11.10}
$$

Finiteness is invariant under isogeny, and here no finite-generation theorem is needed. If $u:B\to B'$ is an isogeny and $B'(\mathbf Q)$ is finite, then

$$
B(\mathbf Q)=
\bigcup_{Q\in B'(\mathbf Q)}
\bigl(u^{-1}(Q)\cap B(\mathbf Q)\bigr).
$$

Every fiber of the finite morphism $u$ is a finite scheme, so the union on the right is finite. Applying the same argument to a dual isogeny proves the converse. Equations (11.9)--(11.10) therefore give

$$
C_{11}(\mathbf Q)\text{ finite}. \tag{11.11}
$$

This is where Eisenstein descent enters the genus-one calculation. We have not assumed an analytic rank statement or the full torsion theorem for $J_0(11)$.

### 11.3 Two reduction counts

The model (11.1) has good reduction at $2$ and $3$. Direct counting gives

$$
\#C_{11}(\mathbf F_2)=5. \tag{11.12}
$$

Indeed, for $x=0$ and $x=1$, the right side is zero and both $y=0,1$ solve $y^2+y=0$ in $\mathbf F_2$. Together with the point at infinity this gives five points.

Likewise

$$
\#C_{11}(\mathbf F_3)=5. \tag{11.13}
$$

For $x=0$ and $x=1$, the right side is zero and $y=0,2$ solve $y^2+y=0$. For $x=2$, the right side is $1$, while $y^2+y$ takes the values $0,2,0$ for $y=0,1,2$. There is no point with $x=2$, and adding infinity gives five.

Because (11.11) makes every rational point torsion, the reduction counts bound the whole group. For a prime $q$ different from the residue characteristic, the $q$-primary rational torsion injects under good reduction. Thus:

- the $2$-primary part injects at $3$ and is trivial because $5$ is odd;
- the $3$-primary part injects at $2$ and is trivial because $3\nmid5$;
- for $q\ne2,3$, the $q$-primary part injects at both primes and has order dividing $5$.

Consequently

$$
\#C_{11}(\mathbf Q)\mid5. \tag{11.14}
$$

The five points in (11.2) show that equality holds.

### 11.4 All rational points are cusps

Combining the preceding results gives

$$
C_{11}(\mathbf Q)=
\{O,(0,0),(0,-1),(1,0),(1,-1)\}
\simeq\mathbf Z/5\mathbf Z. \tag{11.15}
$$

Every point in the set is a cusp by Proposition 11.1. Hence

**Theorem 11.2 (level eleven).** Every rational point of $X_1(11)$ is cuspidal. In particular no elliptic curve over $\mathbf Q$ has a rational point of exact order $11$.

The final implication follows because a smooth elliptic curve with such a point would define a rational point of the open curve $Y_1(11)$, whereas (11.15) lies entirely in the boundary.

This argument is exact about the role of finiteness. Reduction counts alone bound rational torsion, not a positive-rank Mordell--Weil group. Book 146 first proves finiteness through the isogenous Eisenstein quotient; only then do the two finite-field counts determine every rational point.

## 12. The remaining small-prime geometry

### 12.1 Tate normal form

The uniform theorem and the level-$11$ calculation reduce the prime-order problem to

$$
p\in\{2,3,5,7,13\}. \tag{12.1}
$$

The level-$13$ problem will be isolated in Chapter 13. The primes $5$ and $7$ acquire a second role in applications where the elliptic curve also has full rational $2$-torsion. Tate normal form makes that extra condition explicit.

For a point $P$ of exact order at least four, use (11.3). Repeated application of the group law gives the following parametrizations:

$$
\begin{array}{c|cc}
\operatorname{ord}(P)&b&c\\ \hline
5&t&t,\\
7&t^3-t^2&t^2-t.
\end{array} \tag{12.2}
$$

We indicate the calculation. In Tate normal form one has

$$
2P=(b,bc),
$$

after using (11.4)--(11.5) and the defining coefficients. The equality $2P=-3P$ for order five reduces, after removing $b=0$ and the discriminant, to $b=c$; write the common value as $t$. For order seven, the equality $3P=-4P$ first gives a ratio $t=c/b$ on the nondegenerate locus, and clearing denominators yields the second row of (12.2). Substitution back into the group law verifies $5P=0$ or $7P=0$, while the removed factors are precisely the lower-order or singular cases.

The nonzero points of order two on a general Weierstrass equation are fixed by negation. Since

$$
-(x,y)=(x,-y-(1-c)x+b),
$$

the condition $Q=-Q$ gives

$$
2y+(1-c)x-b=0.
$$

Eliminating $y$ from this equation and (11.3) shows that their $x$-coordinates are the roots of

$$
F_{b,c}(X)=
4X^3+\bigl((1-c)^2-4b\bigr)X^2
+2b(c-1)X+b^2. \tag{12.3}
$$

Full rational $2$-torsion forces this cubic to split over $\mathbf Q$.

### 12.2 The five-primary genus-one calculation

Substitute $b=c=t$ in (12.3). A direct cubic-discriminant calculation gives

$$
\operatorname{disc}F_{t,t}
=16t^5(t^2-11t-1). \tag{12.4}
$$

If $t\ne0$ and $F_{t,t}$ splits, its discriminant is a square. Dividing a square root by $4t^2$ produces a rational point on

$$
C_5:\quad z^2=t(t^2-11t-1)
=t^3-11t^2-t. \tag{12.5}
$$

This is an elliptic curve with point $(0,0)$ of order two. We now show that its only rational points are the point at infinity and $(0,0)$.

Write

$$
E_5:y^2=x^3-11x^2-x.
$$

The quotient by $(0,0)$ is

$$
E_5':Y^2=X^3+22X^2+125X, \tag{12.6}
$$

with $2$-isogeny

$$
(x,y)\longmapsto
\left(\frac{y^2}{x^2},
-\frac{y(x^2+1)}{x^2}\right). \tag{12.7}
$$

For a curve $y^2=x^3+Ax^2+Bx$ with rational point $(0,0)$, the elementary $2$-isogeny descent map sends $O$ to $1$, $(0,0)$ to the squareclass of $B$, and every other point to the squareclass of its $x$-coordinate. The image squareclass has a squarefree representative dividing $B$. This follows by writing $x=d u^2/v^2$ with squarefree $d$, substituting in the equation, and observing prime by prime that every odd valuation of $d$ must occur in $B$; the converse local equations are obtained by reversing the substitution.

For $E_5$, $B=-1$, so the image is exactly

$$
\{1,-1\}, \tag{12.8}
$$

witnessed by $O$ and $(0,0)$. For $E_5'$, $B=125$, so the possible images are $1,-1,5,-5$. But

$$
X^2+22X+125=(X+11)^2+4>0,
$$

and the equation $Y^2=X(X^2+22X+125)$ forces $X\ge0$ at every real point. The negative squareclasses are impossible, while $O$ and $(0,0)$ realize $1$ and $5$. Thus the second image is

$$
\{1,5\}. \tag{12.9}
$$

The exact $2$-isogeny sequences give

$$
2^{\operatorname{rank}E_5(\mathbf Q)}
=\frac{\#\operatorname{im}\delta\,
\#\operatorname{im}\delta'}{4}=1. \tag{12.10}
$$

For completeness, (12.10) is obtained by taking dimensions over $\mathbf F_2$ in the two exact quotients by the dual isogenies; the two rational kernels each contribute one factor of $2$, and the free rank contributes equally to the two quotients.

Direct counting gives

$$
\#E_5(\mathbf F_3)=6,
\qquad
\#E_5(\mathbf F_7)=6. \tag{12.11}
$$

Hence rational torsion has order dividing $6$. The $3$-division polynomial factors as

$$
\psi_3(x)=3x^4-44x^3-6x^2-1
=(3x+1)(x^3-15x^2+3x-1). \tag{12.12}
$$

The cubic has no rational root, and at $x=-1/3$ the curve would require

$$
y^2=-25/27,
$$

which is impossible over $\mathbf Q$. Thus there is no rational $3$-torsion. The visible point $(0,0)$ accounts for the full rational torsion, and

$$
C_5(\mathbf Q)=\{\infty,(0,0)\}. \tag{12.13}
$$

Both points have degenerate Tate parameter: $t=0$ or the boundary at infinity. Therefore full rational $2$-torsion cannot coexist nondegenerately with a rational point of order five.

### 12.3 The mixed-seven genus-two curve

Substitute the order-seven row of (12.2) into (12.3). Its discriminant is

$$
\operatorname{disc}F_{t^3-t^2,t^2-t}
=16t^7(t-1)^7(t^3-8t^2+5t+1). \tag{12.14}
$$

For $t\ne0,1$, a split cubic has square discriminant. Divide a square root in (12.14) by $4t^3(t-1)^3$. This produces a rational point on

$$
C_7:\quad
z^2=t(t-1)(t^3-8t^2+5t+1). \tag{12.15}
$$

The polynomial on the right has degree five and discriminant $7^4$, so it is squarefree. Its smooth projective completion is a genus-two curve with one rational point at infinity. The values $t=0$ and $t=1$ are degenerate Tate parameters; the point at infinity is a boundary parameter.

We have proved a precise necessary implication:

$$
\begin{array}{c}
E/\mathbf Q\text{ has full rational }2\text{-torsion}\\
\text{and a rational point of order }7
\end{array}
\Longrightarrow
\begin{array}{c}
(t,z)\in C_7(\mathbf Q)\\
\text{with }t\ne0,1,\infty.
\end{array} \tag{12.16}
$$

Thus excluding the mixed-seven configuration is reduced to proving that every rational point of $C_7$ is cuspidal or degenerate. This is the first of the two remaining genus-two rational-point problems.

### 12.4 Why a square discriminant is only necessary

A separable cubic over $\mathbf Q$ has square discriminant if and only if its Galois group is contained in the alternating group. It can remain irreducible with cyclic Galois group of order three. Therefore a square discriminant does not imply that the cubic splits.

Our deductions use only the safe direction

$$
F_{b,c}\text{ splits over }\mathbf Q
\Longrightarrow
\operatorname{disc}F_{b,c}\in\mathbf Q^{\times2}. \tag{12.17}
$$

Consequently every forbidden elliptic configuration yields a rational point on $C_5$ or $C_7$, but an arbitrary rational point on one of those curves need not reconstruct full rational $2$-torsion. For exclusion, a necessary condition is enough: proving that no nondegenerate point satisfies it rules out the original configuration.

This logical direction must be preserved in the later genus-two calculation. Promoting (12.16) to an equivalence would add a false splitting assertion.

## 13. The level-thirteen genus-two curve

### 13.1 An integral affine model

The remaining prime level is $13$. Tate normal form and the order-$13$ relation give a smooth affine modular curve whose compactification has the following convenient equation:

$$
X_1(13):\quad
y^2+(x^3+x^2+1)y=x^2+x. \tag{13.1}
$$

We recall how the equation is certified. Begin with (11.3), compute consecutive multiples of $P=(0,0)$ by (11.4)--(11.5), and impose

$$
6P=-7P. \tag{13.2}
$$

After removing the factors for singular curves and lower-order points, two ratios of successive denominators give functions $x$ and $y$ satisfying (13.1). Conversely, solving for $b$ and $c$ in terms of these ratios and substituting in the group law makes (13.2) an identity. Thus the normalization of the exact-order locus is the affine curve (13.1), and adding its points at infinity gives $X_1(13)$.

The same calculation identifies the visible boundary points. On (13.1) they are

$$
\infty^+,\quad\infty^-,\quad
(0,0),\quad(0,-1),\quad
(-1,0),\quad(-1,-1). \tag{13.3}
$$

The four affine points follow immediately from $x^2+x=0$. The two points at infinity are the two branches of the even-degree hyperelliptic completion described below. Cusp charts identify these six points with the outward rational cusps, indexed by

$$
(\mathbf Z/13\mathbf Z)^\times/\{\pm1\}.
$$

### 13.2 Genus, cusps, and the hyperelliptic form

Complete the square by putting

$$
z=2y+x^3+x^2+1.
$$

Equation (13.1) becomes

$$
C_{13}:\quad z^2=F(x), \tag{13.4}
$$

where

$$
F(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1. \tag{13.5}
$$

The discriminant is

$$
\operatorname{disc}(F)=-2^{12}13^2. \tag{13.6}
$$

It is nonzero, so $F$ is squarefree. A smooth double cover of $\mathbf P^1$ branched at the six roots of a squarefree sextic has genus

$$
g=\frac{6-2}{2}=2. \tag{13.7}
$$

Because $F$ is monic of even degree, the projective curve has two points above infinity. They are rational and distinguished by

$$
z/x^3\longrightarrow+1
\quad\text{or}\quad-1.
$$

This proves the claims about $\infty^+$ and $\infty^-$ in (13.3).

The modular genus formula gives the same check. For prime $p\ge5$, the image of $\Gamma_1(p)$ in $\operatorname{PSL}_2(\mathbf Z)$ has index $(p^2-1)/2$ and no elliptic fixed points. There are $p-1$ geometric cusps. Hence

$$
g(X_1(p))
=1+\frac{p^2-1}{24}-\frac{p-1}{2}
=\frac{(p-5)(p-7)}{24}. \tag{13.8}
$$

At $p=13$, this is $2$. At $p=11$, it is $1$, agreeing with Chapter 11.

### 13.3 The exact rational-point problem

The six points in (13.3) are rational cusps. A rational point outside this set would represent a smooth elliptic curve over $\mathbf Q$ with a rational point of exact order $13$. Conversely every such elliptic pair gives a noncuspidal rational point. Therefore

$$
\begin{array}{c}
\text{there is no rational point of exact order }13
\end{array}
\Longleftrightarrow
X_1(13)(\mathbf Q)
=\{\text{the six points in }(13.3)\}. \tag{13.9}
$$

The formal-immersion theorem does not settle (13.9), because

$$
n_{13}=\frac{12}{\gcd(12,12)}=1. \tag{13.10}
$$

There is no Eisenstein maximal ideal and no selected quotient of the kind used in Chapters 4--10. This is an absence of the required arithmetic object, not a failure of its cotangent comparison.

Nor can one use genus-one group structure. The Abel--Jacobi map embeds $C_{13}$ in its two-dimensional Jacobian after choosing a rational cusp, but rational points on the curve are a proper subset of rational points on the Jacobian. Determining the latter group and intersecting it with the embedded curve requires a genuine genus-two calculation.

Thus (13.9) is the second remaining genus-two rational-point problem.

### 13.4 The two genus-two handoffs

The work of this book ends with two explicit curves and two exact statements to prove:

$$
C_7:\quad
z^2=t(t-1)(t^3-8t^2+5t+1), \tag{13.11}
$$

for which every rational point must be shown cuspidal or degenerate, and

$$
C_{13}:\quad
z^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1, \tag{13.12}
$$

for which the six rational cusps in (13.3) must be shown exhaustive.

Both are smooth genus-two curves, but their marked geometry differs. The mixed-seven curve has an odd-degree model and one rational point at infinity. The level-thirteen curve has an even-degree model and two rational points at infinity. Any divisor-class calculation must retain that distinction: a reduced divisor on an even-degree hyperelliptic curve can carry a nontrivial infinity class that has no analogue in the odd-degree model.

The handoff is exact and one-directional. For $C_7$, the modular configuration implies a rational point, but the converse is not asserted because square discriminant does not force a cubic to split. For $C_{13}$, the noncuspidal rational points are exactly the elliptic pairs with a rational point of order $13$ by the defining point-level moduli problem.

No result about either rational-point set is used earlier in this book. The uniform theorem and the level-$11$ calculation are complete independently of them.

## 14. The complete formal-immersion package

### 14.1 Main theorem

We collect the results in one dependency-closed statement.

**Theorem 14.1 (Eisenstein cotangents, oriented formal immersion, and prime-order reduction).** Let $N\ge5$ be prime, put

$$
n_N=\frac{N-1}{\gcd(N-1,12)},
\qquad
I=(T_q-(1+q):q\ne N)+(U_N-1),
$$

and suppose $\ell\mid n_N$. Let $\mathfrak m=(\ell,I)$ and let

$$
\pi:J_0(N)\twoheadrightarrow A_{\mathfrak m}
$$

be the selected optimal Eisenstein quotient. Then:

1. for every prime $r\ne N$, pullback identifies the Néron cotangent module of $A_{\mathfrak m}$ with a primitive Hecke-stable sublattice
   $$
   \Omega_{\mathfrak m,r}
   \subseteq S_2(\Gamma_0(N);\mathbf Z_r);
   $$
2. the inclusion and its finite free quotient commute with arbitrary base change from $\mathbf Z_r$;
3. at $r=\ell$, the completed idempotent gives the exact integral comparison
   $$
   e_{\mathfrak m}\omega_{J_0(N),\mathbf Z_\ell}
   \simeq
   e_{\mathfrak m}\omega_{A_{\mathfrak m},\mathbf Z_\ell};
   $$
4. for every outward rational cusp $c$ of $X_1(N)$ and every $r\ne N$, a Hecke translate of
   $$
   X_1(N)\longrightarrow X_0(N)
   \longrightarrow J_0(N)
   \longrightarrow A_{\mathfrak m}
   $$
   is a formal immersion at $c$ modulo $r$;
5. if $r$ is odd and $x\in X_1(N)(\mathbf Q)$ reduces to $c$ modulo $r$, then $x=c$;
6. no elliptic curve over $\mathbf Q$ has a rational point of prime order $p\ge17$;
7. every rational point of $X_1(11)$ is one of its five rational cusps, so order $11$ is also impossible; and
8. after these results, the unresolved prime-order case is the explicit genus-two rational-point problem on $X_1(13)$, while the surviving order-seven configuration with full rational two-torsion reduces to the explicit mixed-seven genus-two problem (13.11). The five-primary mixed configuration is already excluded by the genus-one calculation (12.13).

**Proof.** Items 1--3 are Theorem 6.1. Item 4 is Theorem 7.1. Book 146 supplies finiteness of $A_{\mathfrak m}(\mathbf Q)$; Proposition 8.1 and formal section separation give item 5. Proposition 9.1 locates a prime-order point in an outward cusp disk at $3$, and the exact index ensures a selected quotient for $p\ge17$; Theorem 10.1 gives item 6. Chapter 11 gives item 7. Chapters 12--13 prove the reductions and equations in item 8, including the warning that the mixed-seven implication is only necessary. $\square$

As an immediate prime-order summary, if an elliptic curve over $\mathbf Q$ has a rational point of prime order, the results proved here reduce the prime to

$$
p\in\{2,3,5,7,13\}. \tag{14.1}
$$

The remaining value $13$ is isolated rather than silently classified.

### 14.2 Dependency ledger

Every substantial imported statement occurs in a declared prerequisite with matching hypotheses.

**Book 9.** The formal-immersion criterion in Chapter 2 is the cotangent criterion of Book 9, applied where residue fields agree. Its section-separation consequence is proved here at the level of completed local rings. Book 9 also supplies the Abel map, the identification of its differential by restriction of dualizing forms, and the fact that a cusp section in the smooth locus defines a Cartier divisor. We use the nodal extension only through regular dualizing differentials, never through ordinary differentials at a node.

**Book 15.** Coherent base change supplies local freeness and arbitrary base change of Hodge and dualizing pushforwards in proper flat families. In this book the most important base-change statement is even more elementary: (4.3) is a short exact sequence of vector bundles arising from a smooth exact sequence of abelian schemes. Book 15 justifies identifying the curve and Jacobian Hodge bundles fiberwise and then relatively. No fiberwise dimension equality is promoted to local freeness without this input.

**Book 119.** Integral modular forms are global Hodge sections on the compactified modular stack; weight-two cusp forms are regular dualizing differentials; q-expansion at a cusp is injective on a geometrically integral component; and the away-level coefficient formula gives

$$
a_1(T_mf)=a_m(f)
$$

for $(m,N)=1$. We prove the $U_N$ extension (5.6)--(5.7) in the incoming normalization. At $r=3$, the stack and stabilizer cautions of Book 119 are retained; a naive coarse q-lattice is never used.

**Book 121.** The Néron cotangent lattice is the canonical lattice of regular dualizing differentials, the correspondence action has variance $(\pi_2)_*\pi_1^*$, and pullback on cotangents agrees with the normalized weight-two Hecke operator. The integral Hecke action extends to Néron models and preserves cotangents. We use no rank-two conclusion from Eichler--Shimura and no rational projector on a component lattice.

**Book 145.** The selected rational support defines an optimal quotient with connected kernel; over $\mathbf Z[1/N]$ it gives the exact abelian-scheme sequence (4.2). The local idempotent $e_{\mathfrak m}$ is distinct from the rational projector, the selected Tate lattice is saturated, and the selected finite-flat torsion towers in $J$ and $A$ agree. These facts prove both the primitive whole-quotient cotangent inclusion and the completed comparison (4.7). Nontriviality follows from the actual cuspidal $\ell$-primary subgroup, not merely from a formal maximal ideal.

**Book 146.** For every $\ell\mid n_N$, the exact selected quotient satisfies

$$
A_{\mathfrak m}(\mathbf Q)\text{ finite}.
$$

We use precisely this conclusion. We do not strengthen its power annihilator to annihilation by $I$, identify the rational group with the cuspidal subgroup, or assume that quotient torsion lifts to $J$. At level $11$, isogeny invariance transports the finiteness of $J_0(11)(\mathbf Q)$ to the genus-one curve before reduction counts determine its exact group.

The new results proved in this book are sharply located. Theorem 6.1 is the integral cotangent comparison. Theorem 7.1 is formal immersion at the outward oriented $\Gamma_1$ cusp. Theorem 8.2 joins it to finite rational points at an odd good prime. Theorem 10.1 is the uniform prime-order exclusion, and Theorem 11.2 is the separate level-$11$ calculation. Chapters 12--13 derive the exact two genus-two handoffs.

### 14.3 Normalization and exceptional-case ledger

The following table records the conventions on which the conclusions depend.

$$
\begin{array}{c|c|c}
\text{object}&\text{normalization}&\text{failure if changed}\\ \hline
n_N&(N-1)/\gcd(N-1,12)&
\text{a false selected factor at }N=13\\
I&T_q-(1+q),\ U_N-1&
\text{wrong cusp coefficient or level sign}\\
T&(\pi_2)_*\pi_1^*&
\text{cotangent action replaced by its adjoint}\\
\text{Frobenius}&\text{arithmetic}&
\text{inverted good-prime polynomial}\\
\text{cusp}&\text{outward component orientation}&
\text{ramified forgetful parameter}\\
\text{differentials}&\text{Néron dualizing lattice}&
\text{nonsaturated coarse lattice at }2,3\\
\text{specialization prime}&r=3&
\text{unsupported dyadic torsion injection}
\end{array} \tag{14.2}
$$

The exceptional levels and primes are as follows.

- If $n_N=1$, no selected Eisenstein maximal ideal exists. For prime $N$, this occurs at $N\in\{2,3,5,7,13\}$. The level-$13$ absence is the relevant boundary here.

- At $\ell=2$, generic constant and multiplicative characters coincide, but the cotangent argument at $r=3$ does not require an orientation of every dyadic finite-flat atom.

- At $\ell=3$, one power of $3$ has already been removed in $n_N$. When $r=\ell=3$, primitivity and the completed finite-flat comparison ensure that the differential does not disappear on reduction.

- At $N=11$, a selected quotient exists, and the complete genus-one calculation is supplied separately.

- The inward $\Gamma_1$ cusp is not covered by Theorem 7.1 through the forgetful map to $X_0(N)$; its parameter can be ramified. The prime-order specialization at $3$ reaches the outward cusp, so no case is omitted in the application.

- Square discriminant of the two-torsion cubic is necessary but not sufficient for splitting. The mixed-seven conclusion is stated only in the necessary direction.

### 14.4 Conclusion

The selected Eisenstein quotient has two integral realizations that must be kept together. Rational support constructs an optimal abelian quotient with connected kernel. Completion at an Eisenstein maximal ideal constructs an exact finite-flat torsion summand. The connected kernel makes the quotient cotangent lattice primitive at every good prime, while the completed torsion comparison identifies the exact selected cotangent direction at the Eisenstein prime.

Once that lattice is placed inside regular dualizing cusp forms, q-expansion turns a nonzero reduced differential into a visible coefficient. A Hecke operator moves that coefficient to the first position. At an outward $\Gamma_1$ cusp, forgetting the generator preserves the smoothing parameter, so the unit first coefficient spans the point-level cotangent line. This is the formal immersion.

Finiteness of the quotient's rational group supplies the global half of the argument. At the odd good prime $3$, torsion specializes injectively. A rational point in the cusp disk therefore has the same quotient image as the cusp, and formal immersion makes the two sections equal. A rational point of prime order at least seventeen is forced into exactly such a disk by the Hasse bound and the component orientation, proving the uniform exclusion.

The exceptional levels are not hidden beneath that uniform statement. Level eleven is a genus-one curve whose finite rational group is calculated exactly from Eisenstein finiteness and two reduction counts. Level thirteen has trivial Eisenstein index and becomes the explicit even-degree genus-two curve (13.12). Combining order seven with full rational two-torsion produces the odd-degree mixed-seven curve (13.11), while the analogous order-five curve is settled by a complete genus-one descent.

The resulting package is therefore both local and arithmetic:

$$
\text{exact quotient}
\longrightarrow\text{primitive cotangents}
\longrightarrow\text{unit cusp coefficient}
\longrightarrow\text{formal immersion}
\longrightarrow\text{cusp-disk rigidity}.
$$

It proves the uniform theorem in its exact range, handles the level-$11$ exception, and leaves precisely two named genus-two rational-point problems with their models, marked boundary, and logical direction fully specified.
