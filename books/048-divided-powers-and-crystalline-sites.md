# Divided Powers and Crystalline Sites

## Contents

- [1. Infinitesimal geometry with denominators removed](#1-infinitesimal-geometry-with-denominators-removed)
  - [1.1 The factorial problem](#11-the-factorial-problem)
  - [1.2 Four regimes that must not be confused](#12-four-regimes-that-must-not-be-confused)
  - [1.3 Standing conventions](#13-standing-conventions)
- [2. Divided-power ideals](#2-divided-power-ideals)
  - [2.1 The axioms](#21-the-axioms)
  - [2.2 Identities forced by the axioms](#22-identities-forced-by-the-axioms)
  - [2.3 Exponential intuition and uniqueness](#23-exponential-intuition-and-uniqueness)
- [3. Examples and obstructions](#3-examples-and-obstructions)
  - [3.1 Rational algebras and square-zero ideals](#31-rational-algebras-and-square-zero-ideals)
  - [3.2 Truncated divided powers in characteristic $p$](#32-truncated-divided-powers-in-characteristic-p)
  - [3.3 The canonical divided powers on $(p)$](#33-the-canonical-divided-powers-on-p)
  - [3.4 Nilpotence tests and counterexamples](#34-nilpotence-tests-and-counterexamples)
- [4. Morphisms, subideals, and quotients](#4-morphisms-subideals-and-quotients)
  - [4.1 Morphisms and compatibility](#41-morphisms-and-compatibility)
  - [4.2 Stable subideals](#42-stable-subideals)
  - [4.3 Descent to a quotient](#43-descent-to-a-quotient)
  - [4.4 Base divided powers](#44-base-divided-powers)
- [5. Divided-power polynomial algebras](#5-divided-power-polynomial-algebras)
  - [5.1 One variable](#51-one-variable)
  - [5.2 Several variables and the universal property](#52-several-variables-and-the-universal-property)
  - [5.3 Relative divided-power polynomials](#53-relative-divided-power-polynomials)
  - [5.4 Explicit calculations](#54-explicit-calculations)
- [6. Divided-power envelopes](#6-divided-power-envelopes)
  - [6.1 The universal problem](#61-the-universal-problem)
  - [6.2 Construction by generators and relations](#62-construction-by-generators-and-relations)
  - [6.3 Independence of presentation](#63-independence-of-presentation)
  - [6.4 Principal and diagonal calculations](#64-principal-and-diagonal-calculations)
- [7. Filtrations, nilpotence, and completion](#7-filtrations-nilpotence-and-completion)
  - [7.1 The divided-power filtration](#71-the-divided-power-filtration)
  - [7.2 Nilpotent thickenings](#72-nilpotent-thickenings)
  - [7.3 Ordinary and divided-power completion](#73-ordinary-and-divided-power-completion)
  - [7.4 Restricted divided-power series](#74-restricted-divided-power-series)
- [8. Base change and its failure modes](#8-base-change-and-its-failure-modes)
  - [8.1 Ordinary base change](#81-ordinary-base-change)
  - [8.2 Flat base change for envelopes](#82-flat-base-change-for-envelopes)
  - [8.3 Derived base change](#83-derived-base-change)
  - [8.4 Completed base change](#84-completed-base-change)
- [9. Divided-power schemes and thickenings](#9-divided-power-schemes-and-thickenings)
  - [9.1 Sheafwise divided powers](#91-sheafwise-divided-powers)
  - [9.2 Exact closed immersions](#92-exact-closed-immersions)
  - [9.3 Affine gluing of envelopes](#93-affine-gluing-of-envelopes)
- [10. The crystalline site](#10-the-crystalline-site)
  - [10.1 Objects and arrows](#101-objects-and-arrows)
  - [10.2 The crystalline topology](#102-the-crystalline-topology)
  - [10.3 The structure and defining-ideal sheaves](#103-the-structure-and-defining-ideal-sheaves)
  - [10.4 Small, big, nilpotent, and completed variants](#104-small-big-nilpotent-and-completed-variants)
- [11. Crystals](#11-crystals)
  - [11.1 Rigidity under pullback](#111-rigidity-under-pullback)
  - [11.2 Quasi-coherent and finite locally free crystals](#112-quasi-coherent-and-finite-locally-free-crystals)
  - [11.3 Tensor operations and exactness](#113-tensor-operations-and-exactness)
  - [11.4 A basic counterexample](#114-a-basic-counterexample)
- [12. Smooth lifts and affine evaluation](#12-smooth-lifts-and-affine-evaluation)
  - [12.1 Why a lift is useful](#121-why-a-lift-is-useful)
  - [12.2 The divided-power infinitesimal groupoid](#122-the-divided-power-infinitesimal-groupoid)
  - [12.3 Reconstruction from one evaluation](#123-reconstruction-from-one-evaluation)
- [13. Divided-power stratifications](#13-divided-power-stratifications)
  - [13.1 The diagonal envelope](#131-the-diagonal-envelope)
  - [13.2 Cocycle and normalization](#132-cocycle-and-normalization)
  - [13.3 Crystals and stratifications](#133-crystals-and-stratifications)
  - [13.4 Coordinate form](#134-coordinate-form)
- [14. Connections and Taylor expansion](#14-connections-and-taylor-expansion)
  - [14.1 Connections and curvature](#141-connections-and-curvature)
  - [14.2 From a stratification to a connection](#142-from-a-stratification-to-a-connection)
  - [14.3 Quasi-nilpotence](#143-quasi-nilpotence)
  - [14.4 The equivalence in the smooth affine case](#144-the-equivalence-in-the-smooth-affine-case)
  - [14.5 Limits of the connection description](#145-limits-of-the-connection-description)
- [15. Functoriality and pullback](#15-functoriality-and-pullback)
  - [15.1 Morphisms of divided-power bases](#151-morphisms-of-divided-power-bases)
  - [15.2 Pullback of crystals](#152-pullback-of-crystals)
  - [15.3 Flat and derived coefficient change](#153-flat-and-derived-coefficient-change)
  - [15.4 Transitivity](#154-transitivity)
- [16. Frobenius](#16-frobenius)
  - [16.1 Frobenius on the special fiber](#161-frobenius-on-the-special-fiber)
  - [16.2 Frobenius lifts](#162-frobenius-lifts)
  - [16.3 Frobenius crystals and isocrystals](#163-frobenius-crystals-and-isocrystals)
  - [16.4 The divided differential](#164-the-divided-differential)
- [17. Degree-one constructions](#17-degree-one-constructions)
  - [17.1 The first crystalline complex](#171-the-first-crystalline-complex)
  - [17.2 Extensions and first cohomology](#172-extensions-and-first-cohomology)
  - [17.3 Curves and abelian objects](#173-curves-and-abelian-objects)
  - [17.4 Finite-level and torsion coefficients](#174-finite-level-and-torsion-coefficients)
  - [17.5 Functorial degree-one data](#175-functorial-degree-one-data)
- [18. Synthesis and precise boundaries](#18-synthesis-and-precise-boundaries)
  - [18.1 The construction pipeline](#181-the-construction-pipeline)
  - [18.2 Hypothesis ledger](#182-hypothesis-ledger)
  - [18.3 Final perspective](#183-final-perspective)

## 1. Infinitesimal geometry with denominators removed

### 1.1 The factorial problem

Differential geometry studies a function near a point by its Taylor coefficients. If $x$ is an infinitesimal displacement, the natural monomials are

$$
1,\quad x,\quad \frac{x^2}{2!},\quad \frac{x^3}{3!},\ldots.
$$

Over a field of characteristic zero this notation is harmless. Over an integral ring, and especially near a prime $p$, the denominators cease to exist. Simply deleting them is not an answer: the binomial identity for Taylor expansion then acquires coefficients which may vanish or become zero divisors. Divided powers solve exactly this problem. They retain the symbols $x^n/n!$ together with the identities those symbols ought to satisfy, without requiring $n!$ to be invertible.

This algebra is the correct language for infinitesimal thickenings in characteristic $p$. Ordinary nilpotents remember that two functions agree on a reduced subscheme. Divided-power nilpotents remember how Taylor expansions should behave integrally. Crystalline geometry organizes all such compatible thickenings of a scheme into a site. A crystal is then an object whose value does not change when transported through one of these infinitesimal thickenings.

The word “crystal” expresses rigidity, not constancy. Its value may vary from open set to open set, and may carry a nontrivial connection. What is rigid is its response to nilpotent divided-power displacement: pullback along every arrow of thickenings is an isomorphism.

### 1.2 Four regimes that must not be confused

The same notation can conceal four different constructions.

1. In the **ordinary algebraic regime**, a divided-power envelope is an ordinary ring with finite sums of divided monomials. Tensor products are ordinary tensor products.
2. In the **nilpotent crystalline regime**, every object has an ordinarily nilpotent defining ideal, usually with the prime $p$ locally nilpotent on the ambient ring. Ordinary monomials terminate, but divided monomials need not; termination of a module's Taylor expansion still uses quasi-nilpotence or a PD-order truncation.
3. In the **completed regime**, one passes to an inverse limit, normally $p$-adically or along a specified divided-power filtration. Infinite divided-power series are allowed only with a stated convergence condition.
4. In the **derived regime**, tensor products and inverse limits retain Tor and first-derived-limit terms. A derived tensor product does not become ordinary merely because the notation is shorter.

There are comparison theorems among these regimes, but none is an identity by definition. Flatness removes Tor. Mittag--Leffler hypotheses remove first-derived-limit terms. A divided-power-order truncation, or modulewise quasi-nilpotence on an ordinary nilpotent thickening, turns an infinite-looking Taylor series into a finite sum. Every later theorem will name the mechanism it uses.

### 1.3 Standing conventions

All rings are commutative with identity. A **divided-power pair**, abbreviated **PD pair**, is written $(A,I,\gamma)$, where $I\subset A$ is an ideal and $\gamma=(\gamma_n)_{n\geq0}$ is a divided-power structure. We write $x^{[n]}$ for $\gamma_n(x)$ only when the structure is unambiguous. The letter $p$ always denotes a prime number.

A **PD base** is a triple $(S,\mathcal J,\gamma)$ in the geometric language, or $(A,J,\gamma)$ affinely. Its special fiber is

$$
S_0=V(\mathcal J),\qquad A_0=A/J.
$$

Compatibility with the base always means compatibility with the specified operations on $J$, not merely preservation of the underlying ideal. Unless completion is explicitly mentioned, rings and schemes are ordinary. Unless a derived tensor symbol appears, base change is underived. A claim about a nilpotent crystalline site assumes nilpotence object by object; it does not assert a uniform exponent across the whole site.

The general machinery of complexes, derived global sections, derived tensor products, ringed sites, and derived inverse limits is taken from the earlier treatment of arithmetic derived cohomology. We recall the needed consequences when they control a hypothesis.

## 2. Divided-power ideals

### 2.1 The axioms

The axioms are chosen so that $x^{[n]}$ behaves exactly like $x^n/n!$. Let $I$ be an ideal of a ring $A$. A **divided-power structure** on $I$ is a family of maps

$$
\gamma_n:I\longrightarrow A\qquad(n\geq0)
$$

such that, for $x,y\in I$, $a\in A$, and $m,n\geq0$,

$$
\begin{aligned}
\gamma_0(x)&=1, & \gamma_1(x)&=x,\\
\gamma_n(x)&\in I &&(n>0),\\
\gamma_n(ax)&=a^n\gamma_n(x),
\end{aligned}
\tag{2.1}
$$

$$
\gamma_n(x+y)=\sum_{i+j=n}\gamma_i(x)\gamma_j(y),
\tag{2.2}
$$

$$
\gamma_m(x)\gamma_n(x)=\binom{m+n}{m}\gamma_{m+n}(x),
\tag{2.3}
$$

and

$$
\gamma_m(\gamma_n(x))=
\frac{(mn)!}{m!(n!)^m}\gamma_{mn}(x)\qquad(n>0).
\tag{2.4}
$$

The coefficient in (2.4) is an integer: it counts the partitions of an $mn$-element labelled set into $m$ unordered blocks of size $n$. Thus no division is performed in $A$.

The membership condition in (2.1) makes the iteration in (2.4) meaningful. The operations are part of the structure on the ideal $I$; no operation on elements outside $I$ is intended.

Why are all four substantive identities needed? Equation (2.2) is the denominator-free binomial theorem. Equation (2.3) controls multiplication of Taylor monomials. Equation (2.4) controls Taylor expansion inside a Taylor coefficient. Scalar compatibility ensures that the construction is intrinsic to the ideal, rather than to a chosen set of generators.

### 2.2 Identities forced by the axioms

The first indispensable identity recovers ordinary powers.

**Proposition 2.1.** For $x\in I$ and $n\geq0$,

$$
n!\gamma_n(x)=x^n.
\tag{2.5}
$$

**Proof.** The assertion is clear for $n=0$. Suppose it holds for $n$. Apply (2.3) with indices $n$ and $1$:

$$
\gamma_n(x)x=(n+1)\gamma_{n+1}(x).
$$

Multiplication by $n!$ and the induction hypothesis give

$$
x^{n+1}=(n+1)!\gamma_{n+1}(x).
$$

This completes the induction. $\square$

This proof displays both the strength and the limitation of divided powers. The operations refine ordinary powers, but ordinary powers do not recover them when factorials are zero divisors.

For a finite family $x_1,\ldots,x_r\in I$, repeated use of (2.2) gives

$$
\gamma_n(x_1+\cdots+x_r)=
\sum_{n_1+\cdots+n_r=n}
\gamma_{n_1}(x_1)\cdots\gamma_{n_r}(x_r).
\tag{2.6}
$$

The proof is induction on $r$; after splitting off $x_r$, group the terms according to the last index. Likewise, repeated use of (2.3) gives

$$
\prod_{i=1}^r\gamma_{n_i}(x)=
\frac{(n_1+\cdots+n_r)!}{n_1!\cdots n_r!}
\gamma_{n_1+\cdots+n_r}(x).
\tag{2.7}
$$

The coefficient is a multinomial integer. These formulas are the computational engine of every envelope calculation below.

Taking $a=0$ in scalar compatibility shows $\gamma_n(0)=0$ for $n>0$. Taking $y=-x$ in (2.2), or directly taking $a=-1$, gives

$$
\gamma_n(-x)=(-1)^n\gamma_n(x).
$$

### 2.3 Exponential intuition and uniqueness

Attach to $x\in I$ the series

$$
E_x(T)=\sum_{n\geq0}\gamma_n(x)T^n\in A[[T]].
$$

Equation (2.2) is equivalent to

$$
E_{x+y}(T)=E_x(T)E_y(T).
\tag{2.8}
$$

Thus a divided-power structure turns addition in $I$ into multiplication of exponential series. This is intuition, not a convergence statement: the series is purely formal. In a nilpotent quotient only finitely many terms may survive; in a completion it converges only for the topology being used.

If every $n!$ is invertible in $A$, Proposition 2.1 forces

$$
\gamma_n(x)=\frac{x^n}{n!}.
\tag{2.9}
$$

Consequently a PD structure on any ideal of a rational algebra is unique if it exists, and (2.9) shows that it does exist. In mixed or positive characteristic, uniqueness can fail because (2.5) no longer determines $\gamma_n(x)$. The extra operations are genuine structure.

## 3. Examples and obstructions

### 3.1 Rational algebras and square-zero ideals

Let $A$ be a rational algebra and $I\subset A$ any ideal. Formula (2.9) defines divided powers. The binomial theorem proves (2.2), the identity

$$
\frac{x^m}{m!}\frac{x^n}{n!}
=\binom{m+n}{m}\frac{x^{m+n}}{(m+n)!}
$$

proves (2.3), and the factorial calculation proves (2.4). No nilpotence is required.

At the opposite extreme, suppose $I^2=0$ in an arbitrary ring. Define

$$
\gamma_0(x)=1,\qquad \gamma_1(x)=x,\qquad
\gamma_n(x)=0\quad(n\geq2).
\tag{3.1}
$$

All products of two elements of $I$ vanish. Hence (2.2) has only the two linear terms when $n=1$ and is zero for $n\geq2$; the other axioms follow immediately. This is a distinguished structure, but it need not be the only one. It is the first indication that divided powers are a nonlinear extension of first-order deformation theory.

For an explicit nonuniqueness, take $A=\mathbf F_2[\epsilon]/(\epsilon^2)$ and $I=(\epsilon)$. Besides (3.1), define, for $n>0$,

$$
\gamma_n(\epsilon)=
\begin{cases}
\epsilon,&n\text{ is a power of }2,\\
0,&\text{otherwise}.
\end{cases}
\tag{3.2}
$$

Extend by $\gamma_n(0)=0$. The addition and scalar rules hold because $I^2=0$ and $\mathbf F_2$ has two elements. For the product rule, if $m+n$ is a power of two with $m,n>0$, then $\binom{m+n}{m}$ is even; otherwise the relevant higher divided power is zero. For composition, a nonzero case requires $m$ and $n$ both to be powers of two, and the integer $(mn)!/(m!(n!)^m)$ is odd by the formula $v_2(r!)=r-s_2(r)$, where $s_2(r)$ is the sum of the binary digits. Thus all axioms hold. This exotic structure and (3.1) have the same ordinary powers but different higher divided powers.

Square-zero is sufficient, not necessary. For example, in a rational algebra the ideal $(t)$ has divided powers even though no power of $t$ vanishes. Conversely, nilpotence alone is not sufficient in small characteristic, as Section 3.4 will show.

### 3.2 Truncated divided powers in characteristic $p$

Let $A$ have characteristic $p$, and suppose $I^p=0$. Since $n!$ is invertible in $A$ for $0\leq n<p$, put

$$
\gamma_n(x)=
\begin{cases}
x^n/n!,&n<p,\\
0,&n\geq p.
\end{cases}
\tag{3.3}
$$

This defines a PD structure. Here is the decisive verification. For total degree below $p$, all axioms reduce to the usual factorial identities. In total degree at least $p$, every monomial occurring in (2.2) has total degree at least $p$ in elements of $I$, hence vanishes because $I^p=0$. In (2.3), if $m+n\geq p$, either the product lies in $I^{m+n}=0$, or one factor was already declared zero. The same degree argument handles (2.4). Thus the truncation is compatible with all identities.

The hypothesis $I^p=0$ cannot be replaced by “$I$ is nilpotent” without controlling its nilpotence exponent. If $I^p\neq0$, Proposition 2.1 would force $x^p=p!\gamma_p(x)=0$ for every $x\in I$, which may fail.

### 3.3 The canonical divided powers on $(p)$

Let $A=\mathbf Z_{(p)}$, or $A=\mathbf Z_p$. On the ideal $pA$ define

$$
\gamma_n(pa)=\frac{p^na^n}{n!}.
\tag{3.4}
$$

The quotient lies in $A$. Indeed,

$$
v_p(n!)=\sum_{r\geq1}\left\lfloor\frac{n}{p^r}\right\rfloor<n
$$

for $n>0$, so $v_p(p^n/n!)\geq1$. The rational factorial identities prove the PD axioms in $\mathbf Q_p$, and injectivity of $A\hookrightarrow\mathbf Q_p$ brings the equalities back to $A$. This argument also proves uniqueness among structures obtained by restriction from the rational algebra.

More generally, if $A$ is a $p$-torsion-free algebra over $\mathbf Z_{(p)}$ and the elements $p^n a^n/n!$ lie in $A$ for $a\in A$, the same formula defines divided powers on $pA$. The integrality condition is essential. Torsion-freeness alone does not ensure that a fraction lying in $A[1/p]$ lies in $A$.

Modulo $p^N$, formula (3.4) descends because the kernel of $\mathbf Z_p\to\mathbf Z/p^N$ is stable under divided powers: for $x\in p^N\mathbf Z_p\cap p\mathbf Z_p$, every $\gamma_n(x)$ again lies in $p^N\mathbf Z_p$. This supplies the standard nilpotent PD bases

$$
(\mathbf Z/p^N,(p),\gamma).
$$

Notice that $(p)$ is nilpotent in the quotient but not in $\mathbf Z_p$. Thus the $p$-adic base and its finite nilpotent levels belong to different regimes.

### 3.4 Nilpotence tests and counterexamples

Divided powers impose strong nilpotence when integers annihilate the ideal.

**Proposition 3.1.** If $nI=0$ for some integer $n>0$, then $x^n=0$ for every $x\in I$.

**Proof.** Proposition 2.1 gives

$$
x^n=n!\gamma_n(x)=n\bigl((n-1)!\gamma_n(x)\bigr).
$$

The element in parentheses belongs to $I$, so multiplication by $n$ kills it. $\square$

In particular, over a ring of characteristic $p$, every element of a PD ideal has $p$th power zero. Therefore the ideal $(t)$ in $\mathbf F_p[t]/(t^{p+1})$ admits no PD structure: $t^p\neq0$. This is the basic obstruction showing that nilpotence of the ideal is not enough.

If the whole ring $A$ is used as the PD ideal, Proposition 2.1 applied to $1$ gives $n!\gamma_n(1)=1$. Thus every factorial is invertible. Conversely, a rational algebra carries the structure $\gamma_n(x)=x^n/n!$ on the whole ring. The geometric warning is different: $V(A)$ is empty, so such a pair supplies no thickening of a nonempty scheme. Algebraic existence and geometric usefulness must not be confused.

Finally, two PD structures can agree on ordinary powers and still differ when factorial torsion is present. Equation (2.5) sees only $n!\gamma_n(x)$. This is why a morphism of PD rings must preserve the operations themselves rather than merely the ideals and their ordinary powers.

## 4. Morphisms, subideals, and quotients

### 4.1 Morphisms and compatibility

Let $(A,I,\gamma)$ and $(B,K,\delta)$ be PD pairs. A **PD morphism** is a ring map $f:A\to B$ such that

$$
f(I)\subseteq K,\qquad
f(\gamma_n(x))=\delta_n(f(x))
\tag{4.1}
$$

for every $x\in I$ and $n\geq0$. Identity maps and composites are PD morphisms. If $I$ is generated as an ideal by a set $E$, it is enough to check (4.1) on $E$.

To prove the last assertion, first use scalar compatibility to pass from $x\in E$ to $ax$, and then use the addition formula to pass to finite sums. Every element of $I$ is such a sum. The proof also explains why generation as an ideal, not merely as an additive group, is the relevant notion.

A ring map carrying $I$ into $K$ need not be a PD morphism. For instance, in characteristic $p$, a target can have several possible higher divided powers on a torsion ideal. Preservation of ordinary products detects only the factorial multiples of those operations.

### 4.2 Stable subideals

An ideal $L\subseteq I$ is a **PD subideal** if

$$
\gamma_n(L)\subseteq L\qquad(n>0).
\tag{4.2}
$$

Restricting $\gamma$ then makes $(A,L)$ a PD pair. Intersections and sums of PD subideals are again PD subideals. Intersections are immediate. For a sum, write $z=x+y$ and use (2.2): every term of positive total degree contains a positive divided power of $x$ or $y$, hence lies in the corresponding subideal.

For any ideal $H\subseteq A$, the product $IH$ is a PD subideal of $I$. It is enough to treat $ax$ with $a\in H$ and $x\in I$; scalar compatibility gives

$$
\gamma_n(ax)=a^n\gamma_n(x)\in IH
$$

for $n>0$. Sums then follow from (2.2). This simple observation controls many quotient constructions.

Given a subset $E\subset I$, the smallest PD subideal containing $E$ is generated as an ordinary ideal by all $\gamma_n(e)$ with $e\in E$ and $n>0$. Indeed, that ideal is stable by (2.2), scalar compatibility, and the composition axiom; every stable ideal containing $E$ must contain all these generators.

### 4.3 Descent to a quotient

Let $q:A\twoheadrightarrow B=A/H$, and let $K=q(I)$. We want to define

$$
\bar\gamma_n(q(x))=q(\gamma_n(x)).
\tag{4.3}
$$

The expression is independent of the lift precisely when $H\cap I$ is a PD subideal of $I$.

**Proposition 4.1.** Formula (4.3) defines a unique PD structure on $K$ making $q$ a PD morphism if and only if

$$
\gamma_n(H\cap I)\subseteq H\qquad(n>0).
\tag{4.4}
$$

**Proof.** Necessity follows by applying a compatible quotient structure to an element of $H\cap I$. For sufficiency, two lifts differ by $h\in H\cap I$. By (2.2),

$$
\gamma_n(x+h)-\gamma_n(x)
=\sum_{i=0}^{n-1}\gamma_i(x)\gamma_{n-i}(h).
$$

Every term lies in $H$ by (4.4), so (4.3) is well defined. Each PD identity descends from $A$. Uniqueness is forced by compatibility with the surjection. $\square$

This criterion is useful negatively. Quotienting a PD ring by an arbitrary ideal can destroy divided powers. The kernel must be stable where it meets the PD ideal.

### 4.4 Base divided powers

Suppose $(A,J,\gamma)$ is fixed. A PD $A$-algebra is a PD pair $(B,K,\delta)$ together with a PD morphism

$$
(A,J,\gamma)\longrightarrow(B,K,\delta).
$$

The condition includes $JB\subseteq K$ and

$$
\delta_n(f(x))=f(\gamma_n(x))\qquad(x\in J).
$$

If $B\twoheadrightarrow R$ is to model a thickening over $A$, the ideal $K$ will usually contain both $JB$ and the kernel of $B\to R$. Compatibility is therefore a gluing condition between pre-existing divided powers from the base and newly adjoined divided powers normal to $R$.

The base ideal is often $(p)$. Saying only that $p$ belongs to $K$ is insufficient: its divided powers must be the canonical elements $p^n/n!$ inherited from the chosen base.

## 5. Divided-power polynomial algebras

### 5.1 One variable

In Sections 5.1 and 5.2 the coefficient ring $A$ has the trivial base PD
ideal $(0)$; the nontrivial relative construction begins in Section 5.3. The
ordinary polynomial ring freely adjoins an element. The divided-power
polynomial algebra freely adjoins an element of a PD ideal. As an $A$-module,
define

$$
A\langle t\rangle=\bigoplus_{n\geq0}A\,t^{[n]}.
\tag{5.1}
$$

Multiplication is determined by

$$
t^{[m]}t^{[n]}=\binom{m+n}{m}t^{[m+n]},
\qquad t^{[0]}=1.
\tag{5.2}
$$

Associativity follows from the integer identity

$$
\binom{m+n}{m}\binom{m+n+r}{m+n}
=\frac{(m+n+r)!}{m!n!r!}
=\binom{n+r}{n}\binom{m+n+r}{m}.
$$

The element $t=t^{[1]}$ satisfies $t^n=n!t^{[n]}$, but $t^{[n]}$ is not generally an ordinary polynomial in $t$. This is the entire point of the construction.

Let $A\langle t\rangle_+$ be the ideal spanned by $t^{[n]}$ for $n>0$. It has a unique PD structure for which $\gamma_n(t)=t^{[n]}$. On a general element $x=\sum_{r>0}a_rt^{[r]}$, scalar compatibility and the multinomial formula prescribe $\gamma_n(x)$. These prescriptions respect (5.2); checking on the generators reduces the composition identity to the counting formula for partitions into equal blocks. Thus existence and uniqueness follow.

### 5.2 Several variables and the universal property

For variables $t_1,\ldots,t_d$, write a multi-index $\nu=(\nu_1,\ldots,\nu_d)$ and set

$$
t^{[\nu]}=\prod_{i=1}^d t_i^{[\nu_i]}.
$$

Then

$$
A\langle t_1,\ldots,t_d\rangle
=\bigoplus_{\nu\in\mathbf N^d}A\,t^{[\nu]},
\tag{5.3}
$$

with

$$
t^{[\mu]}t^{[\nu]}
=\prod_i\binom{\mu_i+\nu_i}{\mu_i}t^{[\mu+\nu]}.
\tag{5.4}
$$

**Theorem 5.1.** Let $(B,K,\delta)$ be a PD $A$-algebra and choose $b_1,\ldots,b_d\in K$. There is a unique PD $A$-algebra map

$$
A\langle t_1,\ldots,t_d\rangle\longrightarrow B
\tag{5.5}
$$

sending $t_i$ to $b_i$. It is given by

$$
\sum_\nu a_\nu t^{[\nu]}\longmapsto
\sum_\nu a_\nu\prod_i\delta_{\nu_i}(b_i).
\tag{5.6}
$$

**Proof strategy.** Formula (5.6) is forced by PD compatibility. Equation (2.3) proves that it respects multiplication, while (2.2) and (2.4) prove compatibility with divided powers. It preserves the unit and coefficients visibly. Uniqueness follows because the displayed divided monomials span the source. $\square$

For an arbitrary $A$-module $M$, the same construction is obtained from symbols $m^{[n]}$, linearity in degree one, and the divided-power identities. Its universal property classifies $A$-linear maps $M\to K$. When $M$ is finite free, a basis identifies it with (5.3). Without a basis the universal description, not a choice of coordinates, is intrinsic.

### 5.3 Relative divided-power polynomials

Now let $(A,J,\gamma)$ be a PD base. The relevant ideal of $A\langle t_1,\ldots,t_d\rangle$ is

$$
K=J A\langle t_1,\ldots,t_d\rangle
+A\langle t_1,\ldots,t_d\rangle_+.
\tag{5.7}
$$

There is a unique PD structure on $K$ extending that of $J$ and satisfying $\gamma_n(t_i)=t_i^{[n]}$. For $a\in J$ and $u$ in the positive ideal, the addition axiom forces

$$
\gamma_n(a+u)=\sum_{r+s=n}\gamma_r(a)\gamma_s(u).
\tag{5.8}
$$

This formula proves compatibility on the overlap. The universal property now classifies PD $A$-algebra maps carrying each $t_i$ to the target PD ideal.

One must not replace (5.7) by the positive ideal alone: the structural image of $J$ has to lie in the target PD ideal. Nor may one arbitrarily choose new operations on $JA\langle t\rangle$; they are fixed by the base.

### 5.4 Explicit calculations

In one variable,

$$
(at^{[2]}+bt^{[3]})^{[2]}
=a^2\gamma_2(t^{[2]})+ab\,t^{[2]}t^{[3]}
+b^2\gamma_2(t^{[3]}).
$$

Using (2.4) and (5.2),

$$
\gamma_2(t^{[2]})=3t^{[4]},\qquad
t^{[2]}t^{[3]}=10t^{[5]},\qquad
\gamma_2(t^{[3]})=10t^{[6]}.
$$

Hence

$$
(at^{[2]}+bt^{[3]})^{[2]}
=3a^2t^{[4]}+10ab\,t^{[5]}+10b^2t^{[6]}.
\tag{5.9}
$$

This calculation illustrates why divided-power polynomials are not ordinary polynomials with suggestive typography: their structure constants carry precise integral combinatorics.

If $2$ is invertible, $t^{[2]}=t^2/2$. If $2=0$, the relation becomes $t^2=0$ while $t^{[2]}$ can remain nonzero. Thus the map $A[t]\to A\langle t\rangle$ need not be injective, and the underlying ring can contain information invisible to the ordinary polynomial generator.

## 6. Divided-power envelopes

### 6.1 The universal problem

Let $(A,J,\gamma)$ be a PD base, let $P$ be an $A$-algebra, and let $I\subset P$ be an ideal containing the image of $J$ whenever that is required by the chosen quotient. A **PD envelope** of $(P,I)$ relative to $(A,J,\gamma)$ is a PD $A$-algebra $(D,K,\delta)$ with an $A$-algebra map $u:P\to D$ such that $u(I)\subseteq K$ and with the following universal property:

$$
\begin{array}{c}
P\longrightarrow B,\quad (B,L,\epsilon)\text{ a compatible PD }A\text{-algebra},\\
I\text{ maps into }L
\end{array}
\quad\Longrightarrow\quad
\exists!\,D\longrightarrow B
\tag{6.1}
$$

as a PD $A$-algebra map extending $P\to B$.

The envelope is initial, so it is unique up to a unique compatible isomorphism. This observation will later prove independence of every presentation used to construct it.

### 6.2 Construction by generators and relations

Choose generators $(f_\lambda)_{\lambda\in\Lambda}$ of $I$. Start with the free relative PD $P$-algebra

$$
P\langle t_\lambda\mid\lambda\in\Lambda\rangle_{(A,J,\gamma)}.
$$

This free object is constructed by adjoining symbols for the divided powers of the $t_\lambda$ and of the image of $J$, then imposing the PD axioms and base-compatibility relations; it does not require a pre-existing PD structure on $JP$. Now impose $t_\lambda=f_\lambda$. More precisely, take the smallest ring congruence containing these relations for which the intersection of its kernel with the distinguished PD ideal is PD-stable. Proposition 4.1 gives the quotient PD structure. Call the result $D$. Equivalently, adjoin symbols $f^{[n]}$ for every $f\in I$ and quotient by all PD identities at once; this second construction makes the stability condition manifest.

To verify (6.1), map $t_\lambda$ to the image of $f_\lambda$ in a target. The universal property of the divided-power polynomial algebra gives a unique map before quotienting. It kills the stated relations, hence factors through $D$. Conversely every map from $D$ must send $t_\lambda$ to $f_\lambda$, so uniqueness survives. This proves existence.

The all-symbol construction avoids a choice of generators but is larger. The two constructions are uniquely isomorphic because both solve (6.1).

The image of $I$ need not embed in $D$. Even $P\to D$ can have a kernel: factorial torsion may force ordinary powers to vanish. Envelopes are universal PD thickenings, not faithfully enlarged copies of the original ring.

### 6.3 Independence of presentation

Suppose $P\twoheadrightarrow R$ and $P'\twoheadrightarrow R$ are two polynomial presentations, with kernels $I$ and $I'$. Their envelopes need not be isomorphic as bare rings without relating $P$ and $P'$. What is intrinsic is the sheaf obtained after passing to a smooth local comparison.

If a map $P\to P'$ over $A$ carries $I$ into $I'$, universality gives
$D_P(I)\to D_{P'}(I')$. Even if maps in both directions induce the identity
on $R$ and their composites differ from the relevant identity maps only by
kernel-valued corrections, the induced maps on envelopes are not automatically
inverse. The safe statement is the following: when the two presentations are
joined by an isomorphism of pairs, their envelopes are uniquely isomorphic.
For general smooth presentations, the diagonal-envelope descent of Chapters
12 and 13 supplies canonical comparison data rather than a bare global
identification.

This distinction prevents a common mistake. A universal property is independent of how one presents the _same input pair_; it does not identify different input pairs merely because they have the same quotient.

### 6.4 Principal and diagonal calculations

For $P=A[x]$ and $I=(x)$, the relative envelope is

$$
D_P(I)=A\langle x\rangle,
$$

with the base divided powers included as in Section 5.3. Its quotient by the PD ideal is $A/J$ when the full ideal is $(J,x)$, and is $A$ when only $(x)$ is enveloped over a trivial base.

For $P=A[x_1,\ldots,x_d]$ and $I=(x_1,\ldots,x_d)$,

$$
D_P(I)=A\langle x_1,\ldots,x_d\rangle.
\tag{6.2}
$$

The most important geometric example is the diagonal. Let $R=A[x_1,\ldots,x_d]$ and put

$$
P=R\otimes_A R,\qquad \xi_i=1\otimes x_i-x_i\otimes1.
$$

The multiplication map $P\to R$ has kernel generated by the $\xi_i$, so its envelope is

$$
D(1)\cong R\langle\xi_1,\ldots,\xi_d\rangle.
\tag{6.3}
$$

Writing $p_1(x)=x\otimes1$ and $p_2(x)=1\otimes x$, the two maps
$R\rightrightarrows D(1)$ differ by

$$
p_2(x_i)-p_1(x_i)=\xi_i.
$$

This ring is the integral Taylor neighborhood of the diagonal. It will turn crystals into stratifications and then into connections.

## 7. Filtrations, nilpotence, and completion

### 7.1 The divided-power filtration

For a PD ideal $(I,\gamma)$, define $I^{[r]}$ to be the ideal generated by products

$$
\gamma_{n_1}(x_1)\cdots\gamma_{n_s}(x_s),
\qquad x_i\in I,\quad n_1+\cdots+n_s\geq r.
\tag{7.1}
$$

Then $I^{[0]}=A$, $I^{[1]}=I$, and

$$
I^{[r]}I^{[s]}\subseteq I^{[r+s]}.
\tag{7.2}
$$

Moreover $\gamma_n(I^{[r]})\subseteq I^{[nr]}$; expand a generator with the composition and product identities, then use the sum identity. Thus the filtration measures divided-power order.

Ordinary and divided-power filtrations point in opposite directions:

$$
I^r\subseteq I^{[r]}.
\tag{7.3}
$$

Indeed a product of $r$ elements is a product of $r$ first divided powers. Equality is exceptional. In $A\langle t\rangle$, $t^{[p]}\in I^{[p]}$ need not lie in the ordinary ideal $I^p=(t^p)$; in characteristic $p$, the latter may be zero.

### 7.2 Nilpotent thickenings

An ideal is **ordinarily nilpotent** if $I^N=0$ for some $N$. It is **PD-nilpotent** if $I^{[N]}=0$ for some $N$. By (7.3), PD-nilpotence implies ordinary nilpotence, but the converse is not automatic.

For the nilpotent crystalline site we require ordinary nilpotence of the defining ideal. Some arguments, especially finite Taylor expansions without a modulewise quasi-nilpotence condition, require the stronger PD-nilpotence and will say so. If $p$ is locally nilpotent on the ambient ring, coefficients can kill many high divided monomials, but this does not by itself give a uniform PD-nilpotence exponent.

A **level-$N$ truncation** of a PD envelope is

$$
D_{<N}=D/D^{[N]},
\tag{7.4}
$$

where $D^{[N]}$ is formed from its distinguished PD ideal. This quotient is legitimate because $D^{[N]}$ is PD-stable. It represents the same universal problem among targets whose distinguished PD ideal has divided-power order less than $N$.

### 7.3 Ordinary and divided-power completion

Given an ideal $H\subset A$, ordinary $H$-adic completion is

$$
\widehat A_H=\varprojlim_m A/H^m.
$$

Given a PD ideal $I$, PD completion is

$$
\widehat A_{\mathrm{PD}}=\varprojlim_m A/I^{[m]}.
\tag{7.5}
$$

These completions need not agree because the filtrations need not be cofinal. A third common operation is $p$-adic completion. It agrees with neither of the preceding constructions without a cofinality theorem.

The divided powers extend continuously to (7.5). At each finite level they descend by Proposition 4.1, and the transition maps preserve them. Applying $\gamma_n$ componentwise to a compatible inverse system gives a compatible inverse system. This proves existence; uniqueness follows from density when the completion is separated.

Ordinary inverse limits are not automatically derived inverse limits. For a
countable tower of complexes of abelian groups, or of modules in a category
with exact countable products, there is an exact sequence

$$
0\to R^1\!\varprojlim H^{q-1}(A_m)
\to H^q(R\!\varprojlim A_m)
\to\varprojlim H^q(A_m)\to0.
\tag{7.6}
$$

Surjective transition maps make the first term vanish. The quotient towers in (7.5) are surjective as rings, but towers obtained after applying cohomology or tensor product need not remain surjective. Completed cohomological statements therefore need a separate Mittag--Leffler check.

### 7.4 Restricted divided-power series

The PD completion of $A\langle t_1,\ldots,t_d\rangle$ consists of sums

$$
\sum_{\nu\in\mathbf N^d}a_\nu t^{[\nu]}
\tag{7.7}
$$

interpreted modulo divided-power order: for every $N$, only terms with $|\nu|<N$ affect the quotient by $I^{[N]}$. This is a product over degrees, not the direct sum in (5.3).

For $p$-adic completion the convergence condition is different: coefficients of terms not tending to zero $p$-adically may still define a PD-adic series but not a $p$-adically convergent one. When both filtrations are present, one often uses the mixed neighborhoods

$$
p^mD+I^{[N]}.
$$

Any use of the phrase “completed envelope” must specify which of these systems is intended.

## 8. Base change and its failure modes

### 8.1 Ordinary base change

Let $(A,J,\gamma)\to(A',J',\gamma')$ be a PD morphism. For a PD $A$-algebra $(B,K,\delta)$, the ordinary tensor product $B\otimes_AA'$ does not always inherit a PD structure on the sum of the images of $K$ and $J'$. Relations created by torsion can make the proposed formula depend on a tensor presentation.

If $A'$ is flat over $A$, the expected structure is well defined. Locally write an element of the extended ideal as a sum of pure tensors from $K$ and elements from $J'$, use (2.2) to define its divided powers, and use flatness to see that relations among pure tensors are obtained by tensoring relations over $A$. The axioms may then be checked before base change. This gives the **flat PD base change** $B_{A'}$.

There is a categorical PD pushout even without flatness, constructed by taking a free PD algebra and imposing the tensor relations. Its underlying ring need not be the ordinary tensor product. Distinguishing these two objects prevents an erroneous base-change formula.

### 8.2 Flat base change for envelopes

**Theorem 8.1.** Let $A\to A'$ be flat and compatible with the chosen base divided powers. Let $P$ be an $A$-algebra, $I\subset P$ an ideal, and set

$$
P'=P\otimes_AA',\qquad I'=\operatorname{im}(I\otimes_AA'\to P').
$$

Then the natural map

$$
D_{P/A}(I)\otimes_AA'\longrightarrow D_{P'/A'}(I')
\tag{8.1}
$$

is an isomorphism of PD $A'$-algebras.

**Proof strategy.** Construct the left side with its flatly extended PD structure. A map from it to a PD $A'$-algebra $C$ is the same as an $A$-algebra map $P\to C$ carrying $I$ to the PD ideal. By adjunction this is the same as an $A'$-algebra map $P'\to C$ carrying $I'$ to that ideal. The envelope on the right represents the latter functor. The two representing objects are uniquely isomorphic. $\square$

Flatness serves two roles: it gives the ordinary tensor product its PD structure and identifies the extended kernel with the expected image. Without flatness, the PD pushout still has a universal property, but (8.1) with an ordinary tensor product can fail.

### 8.3 Derived base change

The correct coefficient change for a complex $M$ is

$$
M\otimes_A^LA'.
$$

If $A'$ is flat, this is represented by the ordinary tensor product. Otherwise its negative cohomology contains Tor. For a module $M$ in degree zero,

$$
H^{-i}(M\otimes_A^LA')=\operatorname{Tor}_i^A(M,A').
\tag{8.2}
$$

Thus an ordinary base-change assertion about a crystal or a de Rham complex is stronger than a derived base-change assertion unless Tor vanishes.

This book does not identify an ordinary PD envelope with a hypothetical derived PD envelope. What is used here is more modest and precise: once an ordinary or completed envelope has been constructed, complexes of modules on it undergo derived coefficient change by the machinery of derived tensor products. If an envelope itself is to commute with nonflat base change, the correct algebraic object is the PD pushout; its higher homological refinement requires additional cotangent theory.

### 8.4 Completed base change

Let $D$ be filtered by ideals $F^mD$ and let $A\to A'$ be a coefficient
change. If the left side means the completion of
$\widehat D\otimes_AA'$ for the induced filtration, there is a natural
comparison

$$
\widehat D\,\widehat\otimes_A A'
\longrightarrow
\varprojlim_m\bigl((D/F^mD)\otimes_AA'\bigr).
\tag{8.3}
$$

Flatness removes Tor at each finite level, but it does not by itself make
tensor product commute with an inverse limit. The comparison is an isomorphism
when tensoring with $A'$ commutes with the displayed inverse limit and the
induced completion; a safe sufficient case is that $A'$ is finite projective
over $A$ and the quotient tower is surjective. Alternatively one may _define_
the completed tensor product to be the right side, in which case (8.3) is a
definition rather than a theorem about commuting operations. For derived
completion one replaces each tensor by $\otimes^L$ and the limit by
$R\varprojlim$. Finite generation, noetherian completeness, and
Mittag--Leffler hypotheses often prove the needed comparison, but their exact
form must be stated in each theorem.

A particularly safe finite-level procedure is: first form $D/F^mD$, then make the stated base change, and only afterward pass to the inverse limit. Reversing the order requires exactly the comparison in (8.3).

## 9. Divided-power schemes and thickenings

### 9.1 Sheafwise divided powers

A PD scheme is a scheme $S$ with a quasi-coherent ideal sheaf $\mathcal J\subset\mathcal O_S$ and operations

$$
\gamma_n:\mathcal J\longrightarrow\mathcal O_S
$$

whose restrictions to every open set satisfy the PD axioms and commute with restriction. It is enough to give the structure on an affine open cover and check agreement on overlaps. Localization is flat, and

$$
\gamma_n(a/s)=\gamma_n(s^{-1}a)=s^{-n}\gamma_n(a)
\tag{9.1}
$$

whenever $a$ lies in the localized ideal. Hence an affine PD pair sheafifies canonically.

A morphism of PD schemes is a scheme morphism whose map on structure sheaves carries the target PD ideal into the source PD ideal and preserves every divided power. The reversal is the usual affine reversal: a scheme map $T\to S$ corresponds to a ring map in the other direction.

The closed subscheme $S_0=V(\mathcal J)$ is the base on which the objects of interest live. For Frobenius theory we will assume $S_0$ has characteristic $p$. The construction of the crystalline site itself does not require choosing a prime.

### 9.2 Exact closed immersions

A **PD thickening** of a scheme $U$ over the PD base $S$ is a closed immersion

$$
i:U\hookrightarrow T
$$

over $S$ whose defining ideal

$$
\mathcal I=\ker(\mathcal O_T\to i_*\mathcal O_U)
$$

has a PD structure compatible with that on $S$. We require the immersion to be scheme-theoretically exact:

$$
\mathcal O_U\cong\mathcal O_T/\mathcal I.
\tag{9.2}
$$

In the nilpotent site, $\mathcal I$ is locally nilpotent. In the PD-nilpotent variant, its divided-power filtration is locally finite. In the completed variant, $T$ is replaced by a separated complete ringed space or by the compatible tower of its finite quotients.

Compatibility with $S$ says that the image of $\mathcal J$ in $\mathcal O_T$ lies in $\mathcal I$ and has the prescribed divided powers. Consequently the structural map $U\to S$ factors through $S_0$.

### 9.3 Affine gluing of envelopes

Suppose $U=\operatorname{Spec}(R)$ is embedded in $Y=\operatorname{Spec}(P)$ over $S=\operatorname{Spec}(A)$, with kernel $I$. The affine PD envelope is $\operatorname{Spec}(D_{P/A}(I))$ with the arrows reversed. This construction localizes:

$$
S^{-1}D_{P/A}(I)\cong
D_{S^{-1}P/A}(S^{-1}I)
\tag{9.3}
$$

for any multiplicative set $S\subset P$.

To prove (9.3), observe that a PD map from either side to a target in which $S$ is invertible is exactly a map from $P$ carrying $I$ into the target PD ideal and carrying $S$ to units. The two sides represent the same functor. Uniqueness of representing objects gives the isomorphism.

Therefore affine envelopes glue over open covers of $Y$. The result is the PD envelope of $U$ in $Y$. No separatedness assumption is needed for the local gluing, though separatedness may be required later when comparing diagonal neighborhoods globally.

## 10. The crystalline site

### 10.1 Objects and arrows

Fix a PD base $(S,\mathcal J,\gamma)$ and an $S_0$-scheme $X$. The **small nilpotent crystalline site** $(X/S)_{\mathrm{cris}}$ has objects

$$
(U,T,\delta),\qquad U\subseteq X\text{ open},\quad U\hookrightarrow T
\tag{10.1}
$$

where $U\hookrightarrow T$ is a nilpotent PD thickening over $S$ compatible with the base.

An arrow

$$
(U,T,\delta)\longrightarrow(U',T',\delta')
$$

is a commutative diagram

$$
\begin{array}{ccc}
U&\longrightarrow&T\\
\downarrow&&\downarrow\\
U'&\longrightarrow&T'
\end{array}
$$

over $X$ and $S$, in which $T\to T'$ is a PD morphism. The map on the left is the restriction of the map on the right to the closed subschemes. Composition is ordinary composition of diagrams.

There is generally no final object. Even when $X$ has a global lift, other thickenings need not admit a unique map to it. Cohomology on this site is therefore genuinely sheaf-theoretic rather than evaluation at one universal thickening.

### 10.2 The crystalline topology

A family

$$
\{(U_i,T_i,\delta_i)\to(U,T,\delta)\}_{i\in I}
$$

is a covering if the maps $T_i\to T$ are open immersions whose images cover $T$, and

$$
U_i=U\times_TT_i
$$

with the induced divided powers. Pullbacks of coverings are coverings because open covers are stable under base change. Identity families cover, and composites of covers cover. These three facts verify the axioms of a Grothendieck topology.

One can instead use an étale or flat crystalline topology. That changes the sheaf category and must be stated. Throughout this book, “the crystalline topology” means the Zariski topology just defined unless a qualifier is present.

Representable presheaves are sheaves: maps of schemes glue uniquely over open covers, and the condition of respecting a closed immersion and divided powers is local. Thus the site is subcanonical.

The **small crystalline topos** is

$$
(X/S)_{\mathrm{cris}}^{\sim}
=\operatorname{Sh}((X/S)_{\mathrm{cris}}),
$$

the category of sheaves of sets on this site. Together with the sheaf
$\mathcal O_{X/S}$ defined below, it is a ringed topos. A continuous left-exact
functor between crystalline sites therefore produces a geometric morphism of
their topoi. Its inverse-image functor is left exact on sheaves of sets, while
pullback of modules also includes extension of scalars and is generally only
right exact.

### 10.3 The structure and defining-ideal sheaves

Define

$$
\mathcal O_{X/S}(U,T,\delta)=\Gamma(T,\mathcal O_T).
\tag{10.2}
$$

Open-cover descent for functions proves that this presheaf is a sheaf of rings. It is the **crystalline structure sheaf**. The quotient

$$
\mathcal O_{X/S}\longrightarrow\underline{\mathcal O}_X,\qquad
\underline{\mathcal O}_X(U,T)=\Gamma(U,\mathcal O_U)
\tag{10.3}
$$

has kernel $\mathcal I_{X/S}$, the sheaf of defining ideals. Objectwise, $\mathcal I_{X/S}(U,T)$ is the kernel of functions on $T$ restricted to $U$.

The operations $\delta_n$ glue and make $\mathcal I_{X/S}$ a sheaf of PD ideals. Its PD filtration gives sheaves $\mathcal I_{X/S}^{[r]}$. The quotient

$$
\mathcal O_{X/S}/\mathcal I_{X/S}^{[r]}
$$

records divided-power neighborhoods of order less than $r$.

The structure sheaf is a crystal over itself: pullback of the unit module is the unit module. The ideal sheaf $\mathcal I_{X/S}$ is generally not a crystal, as Section 11.4 shows.

### 10.4 Small, big, nilpotent, and completed variants

In the **big crystalline site**, $U$ is allowed to be an arbitrary $X$-scheme in a stated size class, rather than an open subscheme. The topology may combine open or flat coverings. The big site is convenient for functoriality; the small site is convenient for quasi-coherent calculations. Passing between them requires a comparison theorem and is not an equality of definitions.

The **nilpotent site** requires the defining ideal to be locally nilpotent. If $p$ is locally nilpotent on $S$, this is the classical finite-level setting. The **completed crystalline site** is built from compatible systems modulo $p^n$, or from adic PD thickenings with continuous arrows. Its structure sheaf is an inverse system before a limit is taken.

A completed object is not an object of the nilpotent site merely because each finite quotient is. Conversely, a family of finite-level objects may fail to come from a complete object if effectivity or separatedness fails. Derived cohomology of the completed site involves $R\varprojlim$, not an unqualified ordinary limit.

## 11. Crystals

### 11.1 Rigidity under pullback

Let $\mathcal M$ be a sheaf of $\mathcal O_{X/S}$-modules. Evaluating it on $(U,T)$ gives a sheaf $\mathcal M_T$ on $T$. For an arrow $f:(U,T)\to(U',T')$, there is a canonical transition map

$$
f^*\mathcal M_{T'}=
\mathcal O_T\otimes_{f^{-1}\mathcal O_{T'}}f^{-1}\mathcal M_{T'}
\longrightarrow\mathcal M_T.
\tag{11.1}
$$

The sheaf $\mathcal M$ is a **crystal** if (11.1) is an isomorphism for every arrow. Thus all values are obtained from one another by scalar extension whenever the site supplies an arrow between their thickenings.

The condition is transitive. For $T\xrightarrow{f}T'\xrightarrow{g}T''$, associativity of tensor products identifies $(g\circ f)^*$ with $f^*g^*$, and the transition map for the composite is the composite of transition maps. A crystal therefore carries coherent rigidity, not a collection of unrelated isomorphisms.

### 11.2 Quasi-coherent and finite locally free crystals

A crystal is **quasi-coherent** if every $\mathcal M_T$ is quasi-coherent on $T$. It is **finite locally free** if every $\mathcal M_T$ is finite locally free. Because the transition maps are isomorphisms, it is enough to verify finite local freeness on a collection of objects which locally receives maps from every object; a smooth lift will supply such a collection in Chapter 12.

Finite presentation alone is weaker. Pullback preserves finite presentation, but it does not make an arbitrary transition map invertible. Likewise, a quasi-coherent sheaf on $X$ does not automatically extend to a crystal: extending it to every thickening requires coherent infinitesimal descent data.

For a finite locally free crystal $\mathcal E$, the dual

$$
\mathcal E^\vee=\mathcal Hom_{\mathcal O_{X/S}}(\mathcal E,\mathcal O_{X/S})
$$

is again a crystal. Finite projectivity makes dual formation commute with every scalar extension in (11.1). Without finite projectivity, the natural base-change map for Hom need not be an isomorphism.

### 11.3 Tensor operations and exactness

Tensor products and symmetric and exterior powers of crystals are crystals whenever those operations commute with the relevant scalar extension. In particular,

$$
(\mathcal E\otimes\mathcal F)_T
=\mathcal E_T\otimes_{\mathcal O_T}\mathcal F_T.
$$

Finite locally free crystals form a rigid tensor category: the unit is $\mathcal O_{X/S}$, duals exist, and evaluation and coevaluation are objectwise the usual maps.

Quotients of crystals are crystals because tensor product is right exact. Kernels require care: pullback need not be left exact. A short exact sequence

$$
0\to\mathcal E'\to\mathcal E\to\mathcal E''\to0
$$

remains a short exact sequence of crystals if $\mathcal E''_T$ is flat on every object, or if every arrow used is flat. Without such a hypothesis, the pullback of the kernel can acquire a Tor term. This is the objectwise shadow of derived base change.

### 11.4 A basic counterexample

The defining ideal sheaf is not generally a crystal. Let $k$ be a field, let

$$
U=\operatorname{Spec}(k),\qquad
T=\operatorname{Spec}(k[\epsilon]/(\epsilon^2)),
$$

with its square-zero PD ideal $(\epsilon)$. There is an arrow from $(U,T)$ to the trivial thickening $(U,U)$. Pulling the defining ideal of the trivial thickening back to $T$ gives zero, whereas the defining ideal on $T$ is $(\epsilon)$. The transition map

$$
0\longrightarrow(\epsilon)
$$

is not an isomorphism.

Thus being naturally defined on every thickening is not enough to be a crystal. Crystallinity is the much stronger demand that the definition commute with every infinitesimal base change.

## 12. Smooth lifts and affine evaluation

### 12.1 Why a lift is useful

The crystalline site contains many thickenings and usually has no final one. A smooth lift creates a local substitute: smoothness lets maps from a nilpotent closed subscheme lift locally to its thickening. A crystal can then be evaluated on the lift, and its values elsewhere can be reconstructed. The price is descent data comparing different lifts of the same map.

Let $S=\operatorname{Spec}(A)$ with nilpotent PD ideal $J$, and let

$$
X=\operatorname{Spec}(R_0)
$$

be smooth and finitely presented over $A_0=A/J$. Locally on $X$, there is a smooth $A$-algebra $R$ with

$$
R/JR\cong R_0.
\tag{12.1}
$$

One proof chooses a finite presentation of $R_0$ and an invertible Jacobian minor, lifts its equations and the inverse of the minor to $A$, and localizes. The Jacobian criterion then gives a smooth lift. The nilpotence of $J$ ensures that a lift of an invertible element remains invertible. Global lifts may fail to exist, so the conclusion is deliberately local.

Put $Y=\operatorname{Spec}(R)$. The immersion $X\hookrightarrow Y$ has ideal $JR$. Since $R$ is smooth, hence flat, the base divided powers extend to $JR$ by flat base change. Thus $(X,Y)$ is an object of the crystalline site.

### 12.2 The divided-power infinitesimal groupoid

For $n\geq0$, let $\widetilde D(n)$ be the PD envelope of the closed immersion

$$
X\hookrightarrow Y^{n+1}=Y\times_S\cdots\times_SY.
\tag{12.2}
$$

Its full diagonal PD ideal need not be nilpotent, so $\widetilde D(n)$ is not generally an object of the nilpotent site. Let

$$
D_N(n)=\widetilde D(n)/\mathcal K(n)^N.
\tag{12.3}
$$

The ordinary power $\mathcal K(n)^N$ is PD-stable by Section 4.2, so each quotient inherits divided powers and is a nilpotent object. Any map from $\widetilde D(n)$ to a thickening with $N$th power of its defining ideal zero factors through $D_N(n)$. The compatible tower over $N$ is the divided-power infinitesimal neighborhood. Below, $D(n)$ denotes this tower; in a completed setting it denotes the specified inverse limit of the tower. An algebraic formula over the uncompleted envelope is asserted only when its divided-power expansion is locally finite.

Deleting, repeating, or permuting factors of $Y^{n+1}$ induces maps among the towers $D(n)$ by the universal property. In particular, $D(1)$ has two projections to $Y$, and $D(2)$ has three projections to $D(1)$. These maps satisfy the simplicial identities because they do so before taking envelopes and universal factorization is unique.

The family

$$
D(0)\;\substack{\longleftarrow\\[-6pt]\longleftarrow}\;D(1)
\;\substack{\longleftarrow\\[-6pt]\longleftarrow\\[-6pt]\longleftarrow}\;D(2)
$$

is the divided-power infinitesimal groupoid of the lift. It records not points of $Y$ but mutually infinitesimally close lifts of points of $X$.

### 12.3 Reconstruction from one evaluation

Let $\mathcal E$ be a crystal and put $M=\Gamma(Y,\mathcal E_Y)$ in the affine case. At every level $N$, the two maps $D_N(1)\rightrightarrows Y$ give two pullbacks of $M$. Crystallinity identifies both with the value of $\mathcal E$ on $D_N(1)$, hence gives an isomorphism between them. These isomorphisms are compatible in $N$. On $D_N(2)$, the three comparisons compose coherently because the transition maps of a sheaf do.

Conversely, consider an arbitrary object $(U,T)$ and a map $U\to X$. Smoothness of $Y\to S$ lifts the composite $U\to X\to Y$ locally on $T$ to a map $T\to Y$. Pulling $M$ back along this lift proposes a value on $T$. Two choices $a,b:T\to Y$ define a map

$$
T\longrightarrow Y\times_SY
$$

whose restriction to $U$ lands on the diagonal. Since the defining ideal of $U$ in $T$ has divided powers, universality factors this map through the full envelope. Locally choose $N$ with $\mathcal I_T^N=0$; the factorization then passes through $D_N(1)$. Its comparison identifies $a^*M$ and $b^*M$. The cocycle on a sufficiently large $D_N(2)$ shows that these identifications are transitive for three choices.

Open descent now glues the locally proposed modules. This reconstructs a crystal from a module on $Y$ equipped with the comparison data described next.

## 13. Divided-power stratifications

### 13.1 The diagonal envelope

Let $p_1,p_2:D(1)\rightrightarrows Y$ be the two projections of towers. A **PD stratification** on an $\mathcal O_Y$-module $M$ is a compatible family of isomorphisms at every nilpotent level, written schematically as

$$
\varepsilon:p_2^*M\xrightarrow{\sim}p_1^*M
\tag{13.1}
$$

over $D(1)$ satisfying normalization and a cocycle condition. Passing from the family to one isomorphism on an inverse-limit completion requires completeness and effectivity. An isomorphism over the ordinary full envelope is equivalent only when its coefficients are locally finite. The direction is conventional; reversing it replaces $\varepsilon$ by its inverse.

If $Y=\operatorname{Spec}(R)$ has étale coordinates $x_1,\ldots,x_d$, then locally

$$
\mathcal O_{\widetilde D(1)}\cong R\langle\xi_1,\ldots,\xi_d\rangle,\qquad
\xi_i=p_2(x_i)-p_1(x_i).
\tag{13.2}
$$

Thus (13.1) is an integral Taylor isomorphism.

### 13.2 Cocycle and normalization

The diagonal map $Y\to D(1)$ pulls both projections back to the identity. **Normalization** requires its pullback of $\varepsilon$ to be $\operatorname{id}_M$.

On $D(2)$ write $p_{ij}:D(2)\to D(1)$ for the map selecting factors $i$ and $j$. The **cocycle condition** is

$$
p_{13}^*\varepsilon
=p_{12}^*\varepsilon\circ p_{23}^*\varepsilon,
\tag{13.3}
$$

after the evident identifications of the three pullbacks of $M$. It says that transport from the third infinitesimally close point to the first is transport through the second.

Pulling (13.3) back along a repeated-factor map shows that normalization is forced if one includes all degeneracy identities, but stating it separately makes the definition transparent.

### 13.3 Crystals and stratifications

**Theorem 13.1.** Under the hypotheses of Section 12.1, quasi-coherent crystals on the small nilpotent crystalline site of $X/S$ are equivalent, locally on $X$, to quasi-coherent $R$-modules with a compatible PD stratification on all the towers $D_N(1)$. Finite locally free objects correspond on both sides.

**Proof.** Evaluation of a crystal on $Y$ and comparison of its two pullbacks gives (13.1). Functoriality for the identity arrow gives normalization; functoriality for a composite on $D(2)$ gives (13.3).

For the reverse construction, use local smooth lifting as in Section 12.3. Define the value on $(U,T)$ by pulling $M$ back along a local lift $T\to Y$. The map from $T$ to $D(1)$ associated with two lifts makes $\varepsilon$ an isomorphism between the two proposed values. Equation (13.3) is exactly the descent cocycle on triple overlaps and among three lift choices. Quasi-coherent open descent gives a unique glued module. A morphism of stratified modules glues by the same argument, and the two constructions are inverse because the identity lift recovers $M$. Finite local freeness is local and stable under pullback and descent. $\square$

This is an equivalence relative to a chosen local lift, but the crystal category is intrinsic. A second lift gives an equivalent stratification category through the envelope of the mixed product of the two lifts.

### 13.4 Coordinate form

With coordinates as in (13.2), every normalized stratification has an expansion

$$
\varepsilon(1\otimes m)=
\sum_{\nu\in\mathbf N^d}\theta_\nu(m)\otimes\xi^{[\nu]}.
\tag{13.4}
$$

In an ordinary, noncompleted envelope the right side must be locally finite for each $m$. In a specified completion it must converge in that topology. On the separate quotient by divided-power order $N$, only $|\nu|<N$ occurs; the ordinary nilpotent quotients $D_N(1)$ of Chapter 12 do not impose this latter bound.

Normalization gives $\theta_0=\operatorname{id}$. Semilinearity of $\varepsilon$ determines the action on $fm$ from the divided Taylor expansion of $f$. The cocycle implies

$$
\theta_{\mu+\nu}=\theta_\mu\theta_\nu
\tag{13.5}
$$

when the operators are normalized as ordinary iterated coordinate derivatives paired with divided monomials. In particular the degree-one operators commute. Equation (13.5), together with the Leibniz rule, is the algebraic content of an integrable connection.

## 14. Connections and Taylor expansion

### 14.1 Connections and curvature

Let $R$ be an $A$-algebra and $M$ an $R$-module. A connection is an $A$-linear map

$$
\nabla:M\longrightarrow M\otimes_R\Omega^1_{R/A}
\tag{14.1}
$$

satisfying

$$
\nabla(fm)=f\nabla(m)+m\otimes df.
\tag{14.2}
$$

Extend it to $M\otimes\Omega^q$ by

$$
\nabla(m\otimes\omega)=\nabla(m)\wedge\omega+m\otimes d\omega.
$$

Its curvature is $\nabla^2:M\to M\otimes\Omega^2$. The connection is **integrable** if $\nabla^2=0$. Integrability makes

$$
M\xrightarrow{\nabla}M\otimes\Omega^1
\xrightarrow{\nabla}M\otimes\Omega^2\longrightarrow\cdots
\tag{14.3}
$$

a complex.

With étale coordinates $x_i$, write

$$
\nabla(m)=\sum_i\theta_i(m)\otimes dx_i.
\tag{14.4}
$$

The Leibniz rule becomes $\theta_i(fm)=f\theta_i(m)+(\partial_i f)m$, and curvature zero is equivalent to $[\theta_i,\theta_j]=0$ for all $i,j$.

### 14.2 From a stratification to a connection

Let $Q$ be the augmentation ideal for the diagonal section $Y\to D(1)$; on
rings it is the kernel of $\mathcal O_{D(1)}\to\mathcal O_Y$. This is
the PD ideal generated by the differences $p_2(f)-p_1(f)$, not the larger
defining ideal of $X$ in $D(1)$, which also contains the image of the base
ideal. Modulo $Q^{[2]}$, the difference $\varepsilon-1$ takes values in

$$
M\otimes_R Q/Q^{[2]}.
$$

There is a canonical isomorphism

$$
Q/Q^{[2]}\cong\Omega^1_{R/A},\qquad
p_2(f)-p_1(f)\longmapsto df.
\tag{14.5}
$$

To prove it, the universal derivation gives a surjection from differentials. In étale coordinates both sides are free on the classes of $\xi_i$ and $dx_i$, so it is an isomorphism locally and hence globally.

Define $\nabla$ as the degree-one part of $\varepsilon-1$. Semilinearity of $\varepsilon$ gives (14.2). Reduce the cocycle (13.3) modulo total divided-power order three. Its bidegree $(1,1)$ part says that the two possible second transports agree, which is exactly $\nabla^2=0$. Hence every stratification yields an integrable connection.

### 14.3 Quasi-nilpotence

Not every integrable connection comes from a crystal. The Taylor series must terminate or converge. In coordinates, call $(M,\nabla)$ **quasi-nilpotent** in the nilpotent setting if, locally for every $m\in M$, there is an $N$ such that

$$
\theta_1^{\nu_1}\cdots\theta_d^{\nu_d}(m)=0
\qquad\text{whenever }|\nu|\geq N.
\tag{14.6}
$$

In an adic setting replace zero by convergence to zero in the module topology. Equivalently, the Taylor expression

$$
\sum_\nu
\theta_1^{\nu_1}\cdots\theta_d^{\nu_d}(m)
\otimes\xi^{[\nu]}
\tag{14.7}
$$

defines an element of the chosen ordinary truncation or completion.

Under the hypotheses used below---$R/A$ smooth and $p$ locally nilpotent in
$A$---this condition is independent of the chosen étale coordinates. To see
the point which a mere change-of-basis argument misses, write each new
derivation as an $R$-linear combination of the old ones and repeatedly apply
Leibniz. Terms of bounded old-operator order contain increasingly high
derivatives of the change-of-coordinate coefficients. Those derivatives are
eventually divisible by any fixed power of $p$, by the same factorial estimate
used for the canonical connection in the next paragraph; terms of unbounded
old-operator order kill the chosen section by (14.6). Thus every sufficiently
long new iterate vanishes locally. The identical argument with convergence in
place of vanishing proves invariance in the adic setting. Equivalently, the
condition says intrinsically that the Taylor isomorphism is defined on the
ordinary nilpotent diagonal towers, a coordinate-free property.

When $p$ is locally nilpotent on $A$, the canonical connection $d$ on $R$ is quasi-nilpotent. For a localized coordinate, repeated derivatives contain factorial factors; the $p$-adic valuation of $n!$ tends to infinity, so sufficiently high iterates vanish modulo a fixed power of $p$. On a $p$-adically complete ring they need not vanish, but the Taylor expansion converges in the diagonal PD topology. This example shows why nilpotent and completed definitions differ.

### 14.4 The equivalence in the smooth affine case

**Theorem 14.1.** Let $(A,J,\gamma)$ have nilpotent $J$, assume that $p$ is nilpotent in $A$, let $R$ be smooth over $A$, and let $X=\operatorname{Spec}(R/JR)$. Quasi-coherent crystals on $(X/S)_{\mathrm{cris}}$ correspond to quasi-coherent $R$-modules with integrable quasi-nilpotent connection. In the $p$-adically completed setting, use complete modules and topological quasi-nilpotence.

**Proof strategy.** Theorem 13.1 reduces crystals to stratifications. Section
14.2 sends a stratification to an integrable connection. To see
quasi-nilpotence rather than merely formal convergence, evaluate the
stratification on the ordinary-power quotients of the diagonal envelope. At
each level its value on a fixed section is an algebraic, hence finite, sum of
divided monomials.

The needed coefficient estimate is elementary. In one variable, write
$s_p(n)$ for the sum of the base-$p$ digits of $n$. Multiplying the divided
monomials indexed by those digits gives

$$
\prod_r\bigl(\xi^{[p^r]}\bigr)^{a_r}
=u_n\xi^{[n]},\qquad n=\sum_ra_rp^r,
$$

where $u_n$ is prime to $p$: Legendre's formula gives zero $p$-adic valuation
for the multinomial coefficient. Conversely, if
$p^r=n_1+\cdots+n_b$ with every $n_j>0$, the coefficient of
$\xi^{[p^r]}$ in the product of the $b$ corresponding divided monomials has
valuation

$$
\frac{\sum_j s_p(n_j)-1}{p-1}
\geq\frac{b-1}{p-1}.
$$

It follows that the possible coefficient of $\xi^{[p^r]}$ in the ordinary
power $K^N$, where $K$ is generated by $J$ and the positive divided
monomials, lies in an ideal contained in $((p)+J)^{c(N)}$ for integers
$c(N)\to\infty$; one may take

$$
c(N)=\min_{a+b=N,\ b\geq1}
\left(a+\left\lceil\frac{b-1}{p-1}\right\rceil\right).
$$

Thus finiteness of the stratification modulo every $K^N$
forces $\theta_i^{p^r}(m)$ into $((p)+J)^{c(N)}$ for all sufficiently large
$r$. The ideal $(p)+J$ is nilpotent, so after fixing a sufficiently large
$N$ one gets $\theta_i^{p^r}(m)=0$ for all sufficiently large $r$.
The same statement for finitely many coordinates implies (14.6) by the
pigeonhole principle. Thus the full expansion gives quasi-nilpotence.

Conversely, choose étale coordinates and commuting operators $\theta_i$. Define $\varepsilon$ by (14.7). Quasi-nilpotence makes the sum meaningful. The Leibniz rule and the divided Taylor formula, with coefficients viewed through $p_1$,

$$
p_2(f)=\sum_\nu p_1(\partial^\nu(f))\,\xi^{[\nu]}
\tag{14.8}
$$

show that $\varepsilon$ is $\mathcal O_{D(1)}$-linear from $p_2^*M$ to
$p_1^*M$. This is exactly where the sign convention
$\xi=p_2(x)-p_1(x)$ enters. Replacing $\xi$ by $-\xi$ constructs its inverse.
Commutativity of the $\theta_i$ proves the cocycle: expanding transport by
$\xi$ and then by $\eta$ gives the expansion by $\xi+\eta$, because

$$
(\xi+\eta)^{[n]}=\sum_{r+s=n}\xi^{[r]}\eta^{[s]}.
$$

Thus one obtains a stratification. The two constructions are inverse by comparison of divided-power coefficients. Coordinate independence follows from uniqueness of the stratification with the prescribed Taylor action. $\square$

### 14.5 Limits of the connection description

Smoothness is essential. It supplies local lifts and makes the diagonal conormal module equal to a locally free module of differentials. For a singular algebra, first-order connection data need not integrate to all divided-power orders; higher obstruction classes survive.

Integrability is also essential. A nonzero curvature appears as the failure of the cocycle on the triple diagonal. Quasi-nilpotence is independent: an integrable connection can have an infinite Taylor series which belongs to neither an ordinary nilpotent envelope nor the chosen completion.

Finally, the equivalence is local when $X$ has no global smooth lift. Connections on different lifts are related by stratified descent. It is incorrect to select one global module with connection unless a global lift and the required descent have actually been supplied.

## 15. Functoriality and pullback

### 15.1 Morphisms of divided-power bases

Consider a PD morphism of bases

$$
g:(S',\mathcal J',\gamma')\longrightarrow(S,\mathcal J,\gamma)
$$

and a map of special-fiber schemes

$$
h:X'\longrightarrow X
$$

compatible with $S'_0\to S_0$. On the big crystalline sites, an $S'$-thickening of an $X'$-scheme can be viewed as an $S$-thickening after composition, and its special subscheme maps to $X$. This gives the direct geometric part of a morphism of sites. On small sites, the image of an open subscheme of $X'$ need not be open in $X$; one constructs the morphism through the big sites and then restricts, or works locally with inverse-image opens.

The resulting morphism of ringed sites will be denoted

$$
h_{\mathrm{cris}}:(X'/S')_{\mathrm{cris}}\longrightarrow(X/S)_{\mathrm{cris}}.
\tag{15.1}
$$

Its inverse-image operation on modules includes scalar extension from the pulled-back structure sheaf to $\mathcal O_{X'/S'}$. This scalar extension is why pullback is right exact rather than automatically exact.

### 15.2 Pullback of crystals

For a crystal $\mathcal E$ on $X/S$, define

$$
h_{\mathrm{cris}}^*\mathcal E
=\mathcal O_{X'/S'}\otimes_{h_{\mathrm{cris}}^{-1}\mathcal O_{X/S}}
h_{\mathrm{cris}}^{-1}\mathcal E.
\tag{15.2}
$$

This is again a crystal. To check it, take an arrow $T_1'\to T_2'$ of thickenings. Pullback of (15.2) to $T_1'$ can be regrouped as scalar extension of the pullback of $\mathcal E$ from the corresponding $S$-thickening. The transition map for $\mathcal E$ is an isomorphism, and associativity of tensor products preserves it.

Finite locally free crystals remain finite locally free. A quasi-coherent
crystal remains quasi-coherent: objectwise this is the usual fact that pullback
of a quasi-coherent module along a scheme morphism is quasi-coherent. No
quasi-compactness hypothesis is needed for pullback.

On a smooth lift with connection, (15.2) is the familiar pullback connection

$$
\nabla'(a\otimes m)=da\otimes m+a\,(1\otimes\nabla m),
\tag{15.3}
$$

using the map on differentials. Integrability follows from $d^2=0$ and integrability of $\nabla$. When this construction comes from pulling back a crystal between smooth-lift charts, quasi-nilpotence is preserved because the Taylor stratification itself pulls back. For a connection presented without such a stratification, especially after topological coefficient change, convergence must be checked rather than inferred from flatness alone.

### 15.3 Flat and derived coefficient change

Suppose only coefficients change from $A$ to $A'$. If $A'$ is flat and the base divided powers extend, an evaluated crystal $M_T$ changes to

$$
M_T\otimes_AA'.
$$

Flatness preserves exact sequences, quasi-coherence, and the crystal transition isomorphisms. If $A'$ is not flat, the invariant construction for complexes is

$$
M_T\otimes_A^LA'.
\tag{15.4}
$$

The result is a derived crystal: its transition maps are equivalences after
derived scalar extension. A perfect complex of crystals is a safe coefficient
for this derived operation because it is locally represented by a bounded
complex of finite locally free crystals. Even then, its individual cohomology
sheaves need not commute with underived pullback, and hence need not be
ordinary crystals, unless the relevant Tor terms vanish.

If multiplication by $p^n$ is injective on the coefficient ring $A$, the
two-term free resolution of $A/(p^n)$ gives the triangle

$$
K\xrightarrow{p^n}K\longrightarrow
K\otimes^L_AA/(p^n)\longrightarrow K[1].
\tag{15.5}
$$

and the associated universal-coefficient short exact sequence. Hence ordinary
reduction of $H^q(K)$ agrees with derived reduction in degree $q$ only when
$H^{q+1}(K)$ has no $p^n$-torsion. If $p^n$ is a zero divisor in $A$, (15.5)
need not hold: one must use an actual flat resolution of $A/(p^n)$, whose
higher Tor terms may occupy more than one degree. This warning becomes
decisive in degree one.

### 15.4 Transitivity

For composable maps $(X'',S'')\to(X',S')\to(X,S)$, there is a canonical isomorphism

$$
(h\circ k)_{\mathrm{cris}}^*\mathcal E
\cong k_{\mathrm{cris}}^*h_{\mathrm{cris}}^*\mathcal E.
\tag{15.6}
$$

It is the associativity isomorphism for scalar extension. For three maps, the two ways of comparing fourfold tensor products agree by associativity coherence. Thus crystalline pullback is functorial, not merely objectwise defined up to unrelated choices.

The same conclusion holds for smooth-lift stratifications: pull back the diagonal envelope by its universal property, then pull back $\varepsilon$. The cocycle pulls back to the cocycle. For connections, transitivity is immediate from (15.3).

## 16. Frobenius

### 16.1 Frobenius on the special fiber

Assume $S_0$ has characteristic $p$. The absolute Frobenius of an $S_0$-scheme sends a local function to its $p$th power. If the base Frobenius is not the identity, the map naturally factors through the Frobenius twist

$$
X^{(p)}=X\times_{S_0,F_{S_0}}S_0.
$$

The relative Frobenius is

$$
F_{X/S_0}:X\longrightarrow X^{(p)}.
\tag{16.1}
$$

Confusing absolute and relative Frobenius loses semilinearity. A Frobenius module over a nontrivial base endomorphism is not an ordinary linear endomorphism.

Suppose the PD base has an endomorphism $\sigma:S\to S$ lifting $F_{S_0}$ and preserving the base divided powers. Then (16.1), together with $\sigma$, induces a crystalline pullback functor

$$
F_{\mathrm{cris}}^*:
\operatorname{Crys}(X^{(p)}/S)\longrightarrow
\operatorname{Crys}(X/S).
\tag{16.2}
$$

If $X^{(p)}$ is identified with $X$, the identification is extra data unless it is canonical from the situation.

### 16.2 Frobenius lifts

Let $A$ carry a lift $\sigma$ of Frobenius and let $R$ be an $A$-algebra. A **Frobenius lift** is a $\sigma$-semilinear ring map

$$
\varphi:R\longrightarrow R
$$

whose reduction modulo $p$ is $r\mapsto r^p$. Thus

$$
\varphi(r)-r^p\in pR.
\tag{16.3}
$$

If $R$ is $p$-torsion-free, there is a uniquely defined function

$$
\Delta_\varphi(r)=\frac{\varphi(r)-r^p}{p}.
\tag{16.4}
$$

It is not a derivation. Expanding $\varphi(r+s)$ and $\varphi(rs)$ gives the correction laws

$$
\Delta_\varphi(r+s)=\Delta_\varphi(r)+\Delta_\varphi(s)
-\frac{(r+s)^p-r^p-s^p}{p},
$$

$$
\Delta_\varphi(rs)=r^p\Delta_\varphi(s)+s^p\Delta_\varphi(r)
+p\Delta_\varphi(r)\Delta_\varphi(s).
\tag{16.5}
$$

These identities explain how a Frobenius lift packages first-order arithmetic information. If $R$ has $p$-torsion, divisibility in (16.3) does not determine a quotient, so (16.4) is not canonical.

At a nilpotent level, a smooth algebra has Frobenius lifts locally after
choosing an étale map to affine space: send the affine coordinates to their
$p$th powers and use formal étaleness to lift across the nilpotent ideal
$(p)$. Over a $p$-adically complete algebra the same construction is performed
successively modulo $p^n$ and then passed to the limit, so completeness and
separatedness are required. Without nilpotence or completeness, formal
étaleness alone does not produce a lift across the nonnilpotent ideal $pR$.
Different choices are expected and are compared by the crystal stratification.

### 16.3 Frobenius crystals and isocrystals

At a fixed nilpotent level, let $\mathcal E^{(p)}$ denote the $\sigma$-twist of
a crystal $\mathcal E$, a crystal on $X^{(p)}/S$ obtained by the base-change
pullback of Chapter 15. A **crystal with Frobenius** is $\mathcal E$ together
with a morphism

$$
\Phi:F_{\mathrm{cris}}^*\mathcal E^{(p)}\longrightarrow\mathcal E.
\tag{16.6}
$$

If an identification $X^{(p)}\cong X$ has been fixed, the twist is commonly
suppressed and (16.6) is written $F_{\mathrm{cris}}^*\mathcal E\to\mathcal E$.
Without that identification, suppressing $\mathcal E^{(p)}$ would make the
source and target live on different crystalline topoi.

No invertibility condition follows from this definition. Since $p$ is nilpotent at a finite level, inverting $p$ would annihilate the whole coefficient ring and cannot define a useful isogeny category.

Over a $p$-adically complete, $p$-torsion-free base, an **$F$-crystal** will mean a finite locally free crystal with a map (16.6) which is an isogeny: locally its kernel and cokernel are killed by some power of $p$. Equivalently, after tensoring with $\mathbf Q_p$, it becomes an isomorphism. If the source and target are finite projective and $\Phi$ is injective, it is enough that the cokernel be killed by a power of $p$.

An **$F$-isocrystal** is obtained after rationalizing coefficients. Integral lattices inside the same isocrystal need not be unique. Thus an isocrystal does not by itself supply finite-level integral objects.

Pullback and tensor product carry Frobenius in the expected covariant way.
Duality requires a variance warning. Dualizing (16.6) gives
$\mathcal E^\vee\to F_{\mathrm{cris}}^*(\mathcal E^{(p)})^\vee$, the reverse
of (16.6). After rationalization, $\Phi$ is invertible and its inverse transpose
gives a canonical Frobenius on the dual isocrystal. Integrally, a map in the
direction (16.6) is obtained only after choosing an exponent $a$ for which
$p^a\Phi^{-1}$ preserves the chosen dual lattice; different adequate $a$ give
different integral Frobenius maps. Thus the dual isocrystal is canonical, but
an integral dual $F$-crystal in this convention includes a lattice choice and
an integral normalization.

### 16.4 The divided differential

Differentiate (16.3). In a $p$-torsion-free smooth algebra,

$$
d\varphi(r)=p\bigl(r^{p-1}dr+d\Delta_\varphi(r)\bigr).
\tag{16.7}
$$

Hence $d\varphi$ is divisible by $p$, and one obtains a $\sigma$-semilinear map

$$
\frac{d\varphi}{p}:\Omega^1_{R/A}\longrightarrow\Omega^1_{R/A}.
\tag{16.8}
$$

Equivalently, keeping the Frobenius twist visible, this is the $R$-linear map

$$
\varphi^*\Omega^1_{R/A}:=
R\otimes_{R,\varphi}\Omega^1_{R/A}
\longrightarrow\Omega^1_{R/A},\qquad
a\otimes dr\longmapsto a\,\frac{d\varphi(r)}p.
\tag{16.9}
$$

Here the right $R$-action on the first factor is
$a\cdot r=a\varphi(r)$; this convention records exactly the
$\sigma$-semilinearity suppressed in (16.8).

This degree-one operator is the first place where the Frobenius lift carries more information than special-fiber Frobenius, whose differential is zero. It depends on the lift, but two lifts are infinitesimally close and a crystal's stratification gives the canonical comparison required in cohomological constructions.

Division by $p$ in (16.8) requires $p$-torsion-freeness of the target module
of differentials, or a separately supplied factorization through
multiplication by $p$. For smooth $R/A$, $\Omega^1_{R/A}$ is locally
projective over $R$, so $p$-torsion-freeness of $R$ implies the needed
torsion-freeness. It is not legitimate merely because $d\varphi$ reduces to
zero modulo $p$.

## 17. Degree-one constructions

### 17.1 The first crystalline complex

The full finiteness, base-change, duality, and Künneth theory of crystalline cohomology belongs to the next stage. Here we isolate the degree-one construction that those theorems will act on.

For a crystal $\mathcal E$, derived global sections on the ringed crystalline site are defined, using an injective replacement, by

$$
R\Gamma_{\mathrm{cris}}(X/S,\mathcal E).
\tag{17.1}
$$

We use only

$$
H^0_{\mathrm{cris}}=H^0R\Gamma_{\mathrm{cris}},
\qquad
H^1_{\mathrm{cris}}=H^1R\Gamma_{\mathrm{cris}}.
$$

Under the hypotheses of Theorem 14.1, if $X$ admits a smooth lift $Y/S$ and $\mathcal E$ corresponds to $(M,\nabla)$, the local crystalline Poincaré argument identifies the low-degree complex with

$$
M\xrightarrow{\nabla}M\otimes\Omega^1_{Y/S}
\xrightarrow{\nabla}M\otimes\Omega^2_{Y/S}.
\tag{17.2}
$$

Here is the mechanism, including the descent step. Over any object $(U,T)$,
smoothness supplies locally a map $T\to Y$. The augmented nerve of all such
local lifts has a local extra degeneracy after one lift is chosen, so its
alternating sheaf complex is contractible in positive degrees. Consequently
the alternating cosimplicial evaluations on the diagonal towers $D(n)$ form a
resolution of the crystal; this is a Čech--Alexander argument on the
crystalline site, not an assertion that $Y$ is a final object.

In étale coordinates, filter the normalized complex by total divided-power
degree. Its associated graded complex is a tensor product of one-variable
complexes. In one variable the positive-degree part is contracted by

$$
h(\xi^{[n]}d\xi)=\xi^{[n+1]},\qquad n\geq0,
$$

because the identity

$$
d(\xi^{[n]})=\xi^{[n-1]}d\xi\qquad(n\geq1)
$$

for PD differentials gives $dh+hd=1$ on that part. Tensoring these contractions
removes the divided variables one at a time; the usual alternating sign in a
tensor product makes the contractions compatible. The survivors are exactly
the exterior forms on $Y$, and conjugating by the Taylor stratification makes
the surviving differential $\nabla$. At finite divided-power order every
contraction is finite. On the ordinary nilpotent towers, local nilpotence of
$p$ together with quasi-nilpotence makes the coefficient Taylor expressions
locally finite; in the completed setting the same homotopies are continuous
and pass through the stated inverse-limit topology. The augmentation and the
coordinate contraction therefore give the comparison through degree one.
This proves the low-degree assertion without using the later finiteness,
proper base-change, or global duality theorems.

In particular, on an affine lift,

$$
H^0_{\mathrm{cris}}(X/S,\mathcal E)=\ker\nabla,
$$

and, when higher Zariski cohomology of the quasi-coherent terms vanishes,

$$
H^1_{\mathrm{cris}}(X/S,\mathcal E)=
\frac{\ker(M\otimes\Omega^1\to M\otimes\Omega^2)}
{\nabla M}.
\tag{17.3}
$$

The affineness and quasi-coherence hypotheses are essential for the second formula. Globally, hypercohomology contains Cech gluing terms.

### 17.2 Extensions and first cohomology

Because global sections are

$$
\Gamma(\mathcal E)=
\operatorname{Hom}_{\mathcal O_{X/S}}(\mathcal O_{X/S},\mathcal E),
$$

the general derived-functor argument gives

$$
H^1_{\mathrm{cris}}(X/S,\mathcal E)
\cong
\operatorname{Ext}^1_{\mathcal O_{X/S}}
(\mathcal O_{X/S},\mathcal E).
\tag{17.4}
$$

Thus a degree-one class is represented by an extension

$$
0\longrightarrow\mathcal E\longrightarrow\mathcal V
\longrightarrow\mathcal O_{X/S}\longrightarrow0
\tag{17.5}
$$

of sheaves of modules, modulo equivalence. The middle sheaf need not be a crystal. If one asks for extensions inside a category of finite locally free crystals, extra flatness and exactness conditions enter, and the resulting extension group need not equal (17.4) without a comparison theorem.

On a cover $(T_i)$, a class may be represented by local splittings of (17.5). Their differences are sections of $\mathcal E$ on pairwise overlaps and satisfy the Cech cocycle condition. Changing splittings changes the cocycle by a coboundary. This is the concrete degree-one descent picture.

### 17.3 Curves and abelian objects

Let $f:X\to B_0$ be smooth over the special fiber of a PD base $B$. For an
object $(U,T)$ of $(B_0/B)_{\mathrm{cris}}$, write $X_U=X\times_{B_0}U$.
Degree-one relative cohomology is the sheaf on $T$ whose value on an open
$V\subseteq T$ is the corresponding crystalline cohomology of
$X_{U\times_TV}/V$; on affine objects its module of global sections is denoted

$$
(U,T)\longmapsto
H^1_{\mathrm{cris}}(X_U/T,\mathcal O)
\tag{17.6}
$$

An arrow $(U,T)\to(U',T')$ gives a derived pullback comparison from the value
over $T'$ to the value over $T$. Pasting arrows gives the same comparison as
pulling back once along the composite, by the transitivity of Chapter 15.
Under the properness, finite-presentation, and base-change hypotheses proved in
the next volume, these comparisons are isomorphisms and the sheaves are finite
locally free, so the values form a finite locally free crystal on $B_0/B$.
This book constructs the comparison maps and proves their coherence; it does
not assume their finiteness or base-change bijectivity.

For a smooth proper relative curve, the local lift model is the two-term beginning

$$
\mathcal O_Y\xrightarrow{d}\Omega^1_{Y/B},
$$

because $\Omega^2_{Y/B}=0$. Degree one therefore receives both gluing classes of functions and closed relative differentials. A direct-sum decomposition does not follow: even if a later spectral sequence degenerates, the Hodge pieces can form a nontrivial extension.

For a smooth proper commutative group object, multiplication, inversion, and the identity section induce pullback maps on (17.6). Once the required Künneth isomorphism is available, the primitive identity is the well-typed formula

$$
m^*(z)=\operatorname{pr}_1^*(z)+\operatorname{pr}_2^*(z)
\tag{17.7}
$$

inside $H^1$ of the product. At this stage we construct $m^*$ and the two
projection pullbacks; the Künneth identification of the target with a direct
sum is deliberately deferred. This is the degree-one functorial skeleton later
used for abelian schemes.

### 17.4 Finite-level and torsion coefficients

Integral degree one cannot be recovered by naively reducing a rational object.
Let $K=R\Gamma_{\mathrm{cris}}(X/S,\mathcal E)$ and regard it as a complex of
abelian groups. Since multiplication by $p^n$ is injective on $\mathbf Z$, the
triangle (15.5), now formed over $\mathbf Z$, gives

$$
0\longrightarrow
H^1(K)/p^nH^1(K)
\longrightarrow
H^1(K\otimes^L_{\mathbf Z}\mathbf Z/p^n)
\longrightarrow
H^2(K)[p^n]
\longrightarrow0.
\tag{17.8}
$$

Thus derived reduction of the integral degree-one complex has an extra
contribution precisely when degree two has $p^n$-torsion. Identifying this
derived reduction with crystalline cohomology on a base reduced modulo $p^n$
is a separate base-change theorem; (17.8) alone does not make that
identification. Flatness of $H^2$, or an appropriate vanishing theorem,
removes the right-hand term. No such hypothesis is silently imposed here.

For a countable compatible system of crystals $\mathcal E_n$ modulo $p^n$,
apply the Milnor sequence in abelian groups to obtain

$$
0\to R^1\!\varprojlim H^0_{\mathrm{cris}}(\mathcal E_n)
\to H^1(R\!\varprojlim R\Gamma_{\mathrm{cris}}(\mathcal E_n))
\to\varprojlim H^1_{\mathrm{cris}}(\mathcal E_n)
\to0.
\tag{17.9}
$$

The displayed sequence computes the derived inverse limit; it does not by
itself identify that limit with cohomology on a completed crystalline topos.
Surjectivity of the $H^0$ transition maps kills the first term. Effectivity of
the coefficient system and the comparison with the completed site are separate
requirements before a finite-flat or divisible object can be reconstructed
from all torsion levels.

### 17.5 Functorial degree-one data

The constructions needed later can now be listed as proved operations rather than hoped-for identifications:

- a morphism $X\to Y$ induces pullback $H^1_{\mathrm{cris}}(Y/S,\mathcal E)\to H^1_{\mathrm{cris}}(X/S,f^*\mathcal E)$;
- a morphism of PD bases induces a derived base-change comparison; Chapter 15
  controls coefficient pullback, but invertibility of the comparison for
  crystalline cohomology additionally requires the geometric base-change
  theorem proved in the next volume;
- a correspondence supplies pullback along one leg and, only after a separately established proper trace, pushforward along the other;
- tensor products give cup products into degree two, but duality or perfectness is not inferred from their existence;
- for the structure crystal, a Frobenius lift acts semilinearly on (17.2); for
  general coefficients one also needs a Frobenius morphism (16.6), and
  different choices of lift are compared through the stratification;
- derived finite-level coefficient reduction is governed by (17.8), while
  passage to a derived inverse-limit lattice is governed by (17.9); geometric
  identification with reduced or completed crystalline sites requires the
  separate comparisons stated there.

These distinctions are exactly what degree-one applications to curves, abelian schemes, and finite-flat objects require. The site supplies functorial maps; geometry must still supply finiteness, perfectness, trace, and comparison isomorphisms.

## 18. Synthesis and precise boundaries

### 18.1 The construction pipeline

The theory developed here follows one reusable chain:

$$
\begin{array}{c}
\text{PD base and a special-fiber scheme}\\
\downarrow\\
\text{nilpotent PD thickenings and the crystalline topology}\\
\downarrow\\
\text{the ringed crystalline site and crystals}\\
\downarrow\quad\text{after a local smooth lift}\\
\text{PD stratifications on diagonal envelopes}\\
\downarrow\quad\text{under quasi-nilpotence}\\
\text{integrable connections and Taylor expansion}\\
\downarrow\\
\text{functorial degree-zero and degree-one objects.}
\end{array}
$$

Every downward step has a distinct hypothesis. Divided powers remove factorial denominators. Nilpotence makes the infinitesimal site finite level. Smoothness supplies local lifts. Integrability is the cocycle condition to second order. Quasi-nilpotence makes the full Taylor expansion meaningful. Flatness removes Tor in base change. Mittag--Leffler conditions remove first-derived-limit terms in completion.

### 18.2 Hypothesis ledger

| Assertion                                         | Required hypotheses                                                                                       | What can fail without them                                                  |
| ------------------------------------------------- | --------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------- |
| $\gamma_n(x)=x^n/n!$                              | every $n!$ invertible                                                                                     | divided powers are not determined by ordinary powers                        |
| truncated structure in characteristic $p$         | $I^p=0$                                                                                                   | Proposition 3.1 obstructs existence                                         |
| canonical structure on $(p)$                      | integrality of $p^n/n!$; torsion-free embedding for the proof used                                        | the proposed fractions need not lie in the ring                             |
| quotient PD structure                             | kernel intersection is PD-stable                                                                          | the operation depends on the chosen lift                                    |
| envelope commutes with ordinary tensor            | flat compatible base change                                                                               | the ordinary tensor need not be the PD pushout                              |
| ordinary completion computes derived completion   | derived completeness and vanishing first derived limit                                                    | hidden inverse-limit classes remain                                         |
| completed tensor commutes with the quotient limit | tensor commutes with that limit, for example finite-projective coefficient change with a surjective tower | flatness alone does not commute with inverse limits                         |
| crystals equal modules with stratification        | a local smooth lift                                                                                       | values on arbitrary thickenings cannot be reconstructed from one evaluation |
| stratifications equal connections                 | smoothness, integrability, quasi-nilpotence, and $p$ locally nilpotent in the nilpotent version           | curvature or divergent Taylor series obstructs descent                      |
| dual of a crystal is a crystal                    | finite local freeness, or another dualizable hypothesis                                                   | Hom need not commute with pullback                                          |
| kernels stay crystals                             | flat pullback or flat quotient                                                                            | Tor changes the pulled-back kernel                                          |
| Frobenius isogeny                                 | a $p$-adic integral system; rationalization meaningful                                                    | at one nilpotent level, inverting $p$ annihilates coefficients              |
| dual Frobenius has the direction (16.6)           | rational invertibility, and integrally a normalized lattice-preserving inverse transpose                  | ordinary duality reverses the Frobenius arrow                               |
| $d\varphi/p$ is defined                           | $p$-torsion-freeness of $\Omega^1$, or a chosen factorization                                             | divisibility does not choose a quotient                                     |
| derived reduction has the two-row sequence (17.8) | reduction over $\mathbf Z$, or a coefficient ring on which $p^n$ is a non-zero-divisor                    | extra Tor rows may occur                                                    |
| reduction commutes with $H^1$                     | the preceding two-row hypothesis and $H^2[p^n]=0$                                                         | the right term of (17.8) survives                                           |
| completed $H^1$ is the inverse limit              | $R^1\varprojlim H^0=0$, plus effectivity and comparison with the completed site                           | a derived-limit class or noneffective tower survives                        |

Finiteness of crystalline cohomology, proper and smooth base change, global Poincaré duality, Künneth isomorphisms, comparison with the degree-one cohomology of curves and abelian schemes, and the classification consequences for finite-flat groups require additional geometry. They are not consequences of the site axioms and have not been smuggled into the constructions above.

### 18.3 Final perspective

Divided powers are an arithmetic replacement for factorial denominators. Their universal algebras and envelopes turn an ordinary closed immersion into a Taylor neighborhood which remains meaningful in characteristic $p$. Organizing all nilpotent PD thickenings into a ringed site makes infinitesimal transport intrinsic. A crystal is precisely a module rigid under that transport.

Smooth coordinates reveal the mechanism without defining it: the diagonal envelope contains the divided monomials, a stratification is a Taylor isomorphism, its linear term is a connection, its triple-overlap identity is zero curvature, and quasi-nilpotence is convergence. Frobenius adds a semilinear arithmetic transport whose differential becomes visible only after division by $p$ under an honest torsion-freeness hypothesis.

The degree-one theory already carries pullback, extensions, Frobenius, derived
finite-level reduction, and derived inverse-limit bookkeeping. What it does not
yet carry automatically is just as important: finiteness, duality, traces,
Künneth decompositions, effectivity on a completed site, or torsion-free base
change. With those boundaries explicit, crystalline sites provide a reliable
integral framework for the later cohomology of curves and abelian schemes and
for the finite-level structures attached to them.
