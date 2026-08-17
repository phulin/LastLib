# Valuations, DVRs, and Completions

## Contents

1. [Measuring vanishing](#1-measuring-vanishing)
   - [A local question](#11-a-local-question)
   - [Order of vanishing on a line](#12-order-of-vanishing-on-a-line)
   - [What should count as integral?](#13-what-should-count-as-integral)
   - [Localizations of Dedekind domains](#14-localizations-of-dedekind-domains)
   - [Measurements that are not discrete](#15-measurements-that-are-not-discrete)
2. [Ordered groups and valuations](#2-ordered-groups-and-valuations)
   - [Why the values form a group](#21-why-the-values-form-a-group)
   - [Additive valuations](#22-additive-valuations)
   - [The decisive equality](#23-the-decisive-equality)
   - [Equivalence and normalization](#24-equivalence-and-normalization)
   - [Absolute values and multiplicative size](#25-absolute-values-and-multiplicative-size)
   - [The trivial valuation and failure modes](#26-the-trivial-valuation-and-failure-modes)
   - [Gauss valuations and two-stage measurement](#27-gauss-valuations-and-two-stage-measurement)
3. [Valuation rings and divisibility](#3-valuation-rings-and-divisibility)
   - [Bounded elements](#31-bounded-elements)
   - [The intrinsic characterization](#32-the-intrinsic-characterization)
   - [Ideals are ordered](#33-ideals-are-ordered)
   - [Prime ideals and rank](#34-prime-ideals-and-rank)
   - [Integrality and maximality](#35-integrality-and-maximality)
   - [Residues and leading coefficients](#36-residues-and-leading-coefficients)
4. [Discrete valuation rings](#4-discrete-valuation-rings)
   - [Why discreteness is decisive](#41-why-discreteness-is-decisive)
   - [Equivalent characterizations](#42-equivalent-characterizations)
   - [Arithmetic and examples](#43-arithmetic-and-examples)
5. [The valuation filtration](#5-the-valuation-filtration)
   - [Successive precision](#51-successive-precision)
   - [Leading terms and digits](#52-leading-terms-and-digits)
   - [Fractional ideals and precision](#53-fractional-ideals-and-precision)
   - [Filtered modules and elementary divisors](#54-filtered-modules-and-elementary-divisors)
6. [Nonarchimedean topology and analysis](#6-nonarchimedean-topology-and-analysis)
   - [Balls and the strong triangle inequality](#61-balls-and-the-strong-triangle-inequality)
   - [Continuity of algebraic operations](#62-continuity-of-algebraic-operations)
   - [Cauchy sequences](#63-cauchy-sequences)
   - [Series](#64-series)
   - [Infinite products](#65-infinite-products)
   - [Compactness and local compactness](#66-compactness-and-local-compactness)
   - [Nondiscrete topology](#67-nondiscrete-topology)
7. [Completion](#7-completion)
   - [Filling the missing limits](#71-filling-the-missing-limits)
   - [Extending inverses](#72-extending-inverses)
   - [Universal property](#73-universal-property)
   - [Completion of the valuation ring](#74-completion-of-the-valuation-ring)
   - [Separated completion of rings](#75-separated-completion-of-rings)
   - [Examples of incomplete and complete fields](#76-examples-of-incomplete-and-complete-fields)
8. [Inverse limits and digit expansions](#8-inverse-limits-and-digit-expansions)
   - [Compatible finite approximations](#81-compatible-finite-approximations)
   - [Infinite digits](#82-infinite-digits)
   - [The p-adic integers and numbers](#83-the-p-adic-integers-and-numbers)
   - [Formal power series](#84-formal-power-series)
   - [Units and principal units](#85-units-and-principal-units)
   - [Complete does not mean algebraically closed](#86-complete-does-not-mean-algebraically-closed)
9. [Hensel lifting](#9-hensel-lifting)
   - [Correcting an approximate root](#91-correcting-an-approximate-root)
   - [The valuation form](#92-the-valuation-form)
   - [Lifting factorizations](#93-lifting-factorizations)
   - [Henselian local rings](#94-henselian-local-rings)
   - [Worked lifts](#95-worked-lifts)
   - [Algebraic consequences](#96-algebraic-consequences)
10. [Valuations in algebraic extensions](#10-valuations-in-algebraic-extensions)
    - [The extension problem](#101-the-extension-problem)
    - [Existence by maximal domination](#102-existence-by-maximal-domination)
    - [Integral elements are bounded](#103-integral-elements-are-bounded)
    - [Ramification index and residue degree](#104-ramification-index-and-residue-degree)
    - [Several extensions and the fundamental equality](#105-several-extensions-and-the-fundamental-equality)
    - [Finite extensions of complete fields](#106-finite-extensions-of-complete-fields)
    - [Concrete finite extensions](#107-concrete-finite-extensions)
11. [Integral closure and factorization](#11-integral-closure-and-factorization)
    - [From one local ring to several](#111-from-one-local-ring-to-several)
    - [Finiteness hypotheses](#112-finiteness-hypotheses)
    - [Semilocal Dedekind structure](#113-semilocal-dedekind-structure)
    - [Factorization of the maximal ideal](#114-factorization-of-the-maximal-ideal)
    - [Splitting patterns](#115-splitting-patterns)
    - [Localization and residues](#116-localization-and-residues)
    - [Norms and ideals](#117-norms-and-ideals)
    - [Trace and boundedness](#118-trace-and-boundedness)
    - [Towers](#119-towers)
12. [Completion and finite extensions](#12-completion-and-finite-extensions)
    - [Separating branches by completion](#121-separating-branches-by-completion)
    - [The completed product theorem](#122-the-completed-product-theorem)
    - [Completion of a localization](#123-completion-of-a-localization)
    - [An example of splitting after completion](#124-an-example-of-splitting-after-completion)
    - [Unique extension and henselianity](#125-unique-extension-and-henselianity)
    - [The valuation ring in a finite complete extension](#126-the-valuation-ring-in-a-finite-complete-extension)
    - [Unramified and totally ramified endpoints](#127-unramified-and-totally-ramified-endpoints)
    - [A final synthesis](#128-a-final-synthesis)
13. [Structure of complete local rings](#13-structure-of-complete-local-rings)
    - [Coordinates for a complete local ring](#131-coordinates-for-a-complete-local-ring)
    - [Coefficient fields in equal characteristic zero](#132-coefficient-fields-in-equal-characteristic-zero)
    - [p-bases and derivations](#133-p-bases-and-derivations)
    - [Coefficient fields in equal characteristic p](#134-coefficient-fields-in-equal-characteristic-p)
    - [Cohen rings: existence](#135-cohen-rings-existence)
    - [The lifting property and uniqueness of Cohen rings](#136-the-lifting-property-and-uniqueness-of-cohen-rings)
    - [The structure theorem](#137-the-structure-theorem)
    - [Worked examples and counterexamples](#138-worked-examples-and-counterexamples)
    - [Coordinates, and what they cost](#139-coordinates-and-what-they-cost)

## 1. Measuring vanishing

### 1.1 A local question

Many questions in algebra become clearer after one stops asking for an exact value and asks instead for an order of magnitude. Near a point of a curve, a rational function may be complicated as a formula but simple in its leading behavior: it has a zero of a certain order, a pole of a certain order, or neither. In arithmetic, an integer may be large in the ordinary sense but highly divisible by a fixed prime. These are the same kind of measurement.

Take a nonzero rational function near the origin. It can often be written

$$
f(t)=t^n u(t),
$$

where $u$ is defined and nonzero at $0$. The integer $n$ is positive for a zero, negative for a pole, and zero for a nonvanishing regular function. Multiplication adds orders. Addition cannot create a term of lower order than the lower of the two input orders, though cancellation can raise the order. Those two observations are the valuation laws.

The same pattern appears at a prime $p$. Every nonzero rational number has a unique expression

$$
x=p^n\frac ab,
$$

where $a,b$ are coprime integers not divisible by $p$ and $b>0$. The exponent $n$, denoted $v_p(x)$, is the $p$-adic order. Set $v_p(0)=+\infty$. Thus $v_p(xy)=v_p(x)+v_p(y)$, while

$$
v_p(x+y)\geq \min\{v_p(x),v_p(y)\}.
$$

For example, $v_3(45/14)=2$, whereas $v_3(1+2)=1$ is strictly larger than $\min(v_3(1),v_3(2))=0$. The strict inequality records cancellation modulo $3$.

The usefulness of the measurement comes from deliberately forgetting units. At the origin, the factor $u(t)$ is locally invertible and therefore irrelevant to the order of vanishing. At $p$, the fraction $a/b$ is a $p$-adic unit. A valuation separates a multiplicative object into a magnitude and a unit part. Much of this book develops the consequences of that separation.

### 1.2 Order of vanishing on a line

The simplest setting in which local measurement is exact is the affine line. Factorization by the coordinate gives both a computable model and the prototype for a local parameter on a curve.

Let $k$ be a field. For a nonzero polynomial $f\in k[t]$, let $\operatorname{ord}_0(f)$ be the largest $n\geq0$ for which $t^n$ divides $f$. Unique factorization gives

$$
f=t^n(a_0+a_1t+\cdots+a_rt^r),\qquad a_0\ne0.
$$

Extend this to $k(t)^\times$ by

$$
\operatorname{ord}_0(f/g)=\operatorname{ord}_0(f)-\operatorname{ord}_0(g).
$$

Set $\operatorname{ord}_0(0)=+\infty$.

This is well defined: replacing $f/g$ by $fh/gh$ adds the same order to numerator and denominator. The value is the zero order if positive and the negative of the pole order if negative.

The inequality for sums is visible from factorizations. If $f=t^m u$ and $g=t^n w$, with $u(0),w(0)\ne0$ and $m\leq n$, then

$$
f+g=t^m(u+t^{n-m}w).
$$

The parenthesis is regular, so the sum has order at least $m$. If $m<n$, its value at zero is $u(0)\ne0$, and equality follows. Thus unequal orders never cancel:

$$
\operatorname{ord}_0(f)\ne\operatorname{ord}_0(g)
\quad\Longrightarrow\quad
\operatorname{ord}_0(f+g)=\min\{\operatorname{ord}_0(f),\operatorname{ord}_0(g)\}.
$$

This strengthening of the triangle inequality is one of the small facts that makes nonarchimedean analysis unusually rigid.

The point $0$ has no special status. Define $\operatorname{ord}_a(f)$ as the order at zero of $f(a+t)$, equivalently as the multiplicity of $t-a$ in $f$. On a smooth algebraic curve a local parameter plays the role of $t-a$. The resulting order is intrinsic even though the parameter is not: two parameters differ by a local unit.

### 1.3 What should count as integral?

A local measurement immediately singles out the objects without poles. For $\operatorname{ord}_0$ they form

$$
k[t]_{(t)}=\left\{\frac{f(t)}{g(t)}:g(0)\ne0\right\}.
$$

For $v_p$ they form

$$
\mathbf Z_{(p)}=\left\{\frac ab:a,b\in\mathbf Z, p\nmid b\right\}.
$$

Both are local rings. Their unique maximal ideals consist of elements having positive order, and every nonzero element is a power of one distinguished element times a unit. In the first ring the distinguished element is $t$; in the second it is $p$. This parallel is the basic model for a discrete valuation ring.

There is a second, subtler lesson. The ring of objects having no pole determines the comparison completely. Given a field $K$ and a subring $V\subset K$, suppose that for every $x\in K^\times$, at least one of $x$ and $x^{-1}$ belongs to $V$. Then $V$ behaves like a ring of locally bounded elements, and in fact it is precisely a valuation ring. The numerical measurement may be reconstructed from divisibility among principal fractional ideals. Thus valuations can be studied either as functions or as rings.

### 1.4 Localizations of Dedekind domains

The polynomial and prime-adic examples are instances of a general local operation. A Dedekind domain carries one exponent for every nonzero prime; localization isolates one exponent and turns global ideal factorization into a single valuation.

Let $A$ be a Dedekind domain with fraction field $K$, and let $\mathfrak p$ be a nonzero prime ideal. Unique factorization of fractional ideals writes

$$
xA=\prod_{\mathfrak q}\mathfrak q^{n_{\mathfrak q}(x)}
$$

for each $x\in K^\times$, with only finitely many nonzero exponents. The exponent $n_{\mathfrak p}(x)$ is a valuation. An element belongs to the localization $A_{\mathfrak p}$ exactly when $n_{\mathfrak p}(x)\geq0$. Indeed, denominators outside $\mathfrak p$ contribute no $\mathfrak p$-factor. Consequently $A_{\mathfrak p}$ is a discrete valuation ring.

This example explains why localizing a one-dimensional nonsingular arithmetic object at a closed point produces a valuation. Globally, different primes compete and ideals need not be principal. Locally at one prime, every other prime becomes a unit, and the remaining ideal theory is governed by one integer.

### 1.5 Measurements that are not discrete

Integer-valued orders are central, but the axioms do not force them. Choose compatible roots $t^{1/n!}$ in a fixed algebraic closure of $k((t))$, and let

$$
K=\bigcup_{n\geq1} k((t^{1/n!})).
$$

The factorials make these fields nested. A nonzero element of $k((t^{1/n!}))$ has a lowest exponent in $\frac1{n!}\mathbf Z$. These definitions agree under the inclusions and give a valuation

$$
v:K^\times\longrightarrow \mathbf Q.
$$

Its value group is $\mathbf Q$, which has no smallest positive element. The valuation ring has maximal ideal consisting of positive-valued elements, but that ideal is not generated by one element: if $v(a)>0$, choose a positive rational smaller than $v(a)$ and an element $b$ of that value; then $a\in(b)$ but $b\notin(a)$. This is a valuation ring but not a discrete valuation ring and not Noetherian.

The counterexample warns us not to blur rank one, which concerns the ordering of the value group, with discreteness, which concerns the existence of a least positive value. The distinction will matter repeatedly.

## 2. Ordered groups and valuations

### 2.1 Why the values form a group

An order of vanishing must add under multiplication, so the possible finite values should form an abelian group $\Gamma$. It must also make sense to compare magnitudes, and multiplying by a fixed element should preserve comparisons. This leads to a totally ordered abelian group: an abelian group $(\Gamma,+)$ with a total order such that

$$
\alpha\leq\beta\quad\Longrightarrow\quad
\alpha+\gamma\leq\beta+\gamma.
$$

We adjoin a symbol $\infty$, larger than every element, and impose $\gamma+\infty=\infty$. The symbol represents zero, whose order of vanishing is infinite.

The familiar value group is $\mathbf Z$. Subgroups of $\mathbf R$, such as $\mathbf Q$ or $\mathbf Z+\sqrt2\mathbf Z$, give rank-one examples. Ordered groups can also have several scales. Give $\mathbf Z^2$ the lexicographic order: $(a,b)<(c,d)$ when $a<c$, or when $a=c$ and $b<d$. Here $(0,1)$ is smaller than every $(1,n)$, no matter how negative $n$ is. The first coordinate measures a coarser order, while the second refines elements tied at the first level.

An ordered group is **archimedean** if for all positive $\alpha,\beta$ there exists $n\geq1$ with $n\alpha\geq\beta$. Such groups embed order-preservingly in $\mathbf R$; valuation theorists call valuations with archimedean value group **rank one**. Lexicographically ordered $\mathbf Z^2$ is not archimedean. A rank-one group may nevertheless be dense in $\mathbf R$, so rank one does not imply discreteness.

### 2.2 Additive valuations

The examples suggest exactly which information a definition should preserve: zero has infinite order, products add orders, and a sum cannot have order below its least summand. Allowing a support also lets the same definition measure a ring before passing to a domain quotient.

Let $R$ be a commutative ring. A map

$$
v:R\longrightarrow \Gamma\cup\{\infty\}
$$

is an **additive valuation** if

$$
v(0)=\infty,
\qquad v(1)=0,
\qquad v(xy)=v(x)+v(y),
\qquad v(x+y)\geq\min\{v(x),v(y)\}.
$$

Some authors permit the zero ring or slightly alter the convention at $1$; throughout this book rings have identity and the displayed normalization is understood. The set

$$
\operatorname{supp}(v)=\{x\in R:v(x)=\infty\}
$$

is called the support. It is a prime ideal. Closure under addition follows from the inequality, absorption follows from multiplicativity, and if $xy$ has infinite value then one of $x,y$ must: the sum of two elements of $\Gamma$ is finite.

For a field $K$, the support is necessarily $(0)$, and restriction to $K^\times$ is a group homomorphism $K^\times\to\Gamma$. Conversely, a group homomorphism satisfying the sum inequality extends uniquely by setting $v(0)=\infty$. For a general ring, the valuation factors through the domain $R/\operatorname{supp}(v)$ and then extends uniquely to its fraction field by

$$
v(a/b)=v(a)-v(b).
$$

Thus support is the algebraic locus at which the measurement becomes infinite. Most of our central theory concerns valuations on fields, where there is no support to track.

A valuation is **surjective** when $v(K^\times)=\Gamma$. Nothing essential is gained by retaining unused elements of $\Gamma$, so we normally replace $\Gamma$ by the subgroup actually attained, called the value group and denoted $\Gamma_v$.

### 2.3 The decisive equality

The valuation inequality contains a sharper statement.

**Lemma 2.1 (unequal values do not cancel).** If $v(x)\ne v(y)$, then

$$
v(x+y)=\min\{v(x),v(y)\}.
$$

**Proof.** Suppose $v(x)<v(y)$. The triangle inequality gives $v(x+y)\geq v(x)$. On the other hand, $x=(x+y)-y$, so

$$
v(x)\geq\min\{v(x+y),v(y)\}.
$$

If $v(x+y)>v(x)$, both terms in this minimum would exceed $v(x)$, a contradiction. Hence equality holds. $\square$

This short argument is used constantly. Cancellation is possible only among terms of equal value. In a finite sum, a term whose value is strictly smaller than all others controls the sum. In particular, in a nonempty finite sum of nonzero terms whose sum is zero, the least value must occur at least twice.

### 2.4 Equivalence and normalization

The same local geometry can be labeled by different ordered groups. Two valuations $v:K^\times\to\Gamma$ and $w:K^\times\to\Delta$ are **equivalent** if there is an order-preserving group isomorphism $\Gamma_v\to\Gamma_w$ carrying $v(x)$ to $w(x)$ for every $x$. Equivalently, they make exactly the same comparisons:

$$
v(x)\leq v(y)\quad\Longleftrightarrow\quad w(x)\leq w(y).
$$

For a discrete valuation, its value group is isomorphic to $\mathbf Z$. Choosing the unique isomorphism that sends the smallest positive value to $1$ gives the **normalized valuation**. Without normalization, $v$ and $2v$ express the same valuation ring but attach different integers to ideals. Statements involving a ramification index require normalized valuations.

A **coarsening** deliberately forgets some distinctions. If $H\subset\Gamma$ is a convex subgroup, meaning that $0\leq\gamma\leq h\in H$ implies $\gamma\in H$, the ordered quotient $\Gamma/H$ is defined and the composite valuation is a coarsening. For lexicographic $\mathbf Z^2$, quotienting by $\{0\}\times\mathbf Z$ remembers only the first coordinate. Coarsenings clarify higher-rank valuations, but discrete rank-one valuations have no nontrivial proper coarsenings.

### 2.5 Absolute values and multiplicative size

Analysis usually describes smallness by a real number rather than by an element of an ordered group. An **absolute value** on a field $K$ is a function $|\cdot|:K\to\mathbf R_{\geq0}$ such that

$$
|x|=0\Longleftrightarrow x=0,
\qquad |xy|=|x||y|,
\qquad |x+y|\leq |x|+|y|.
$$

It is **nonarchimedean** when it satisfies the stronger inequality

$$
|x+y|\leq\max\{|x|,|y|\}.
$$

The ordinary absolute value is archimedean; prime-adic and order-of-vanishing absolute values are nonarchimedean. This distinction controls the geometry of balls, the criterion for convergence of series, and the algebraic meaning of the closed unit ball.

An additive valuation describes greater divisibility by a larger value, so its direction is opposite to that of size. Fix a real number $c$ with $0<c<1$. For a real-valued valuation define

$$
|x|_v=c^{v(x)},\qquad c^\infty=0.
$$

Then

$$
|xy|_v=|x|_v|y|_v,
\qquad |x+y|_v\leq\max\{|x|_v,|y|_v\}.
$$

The second inequality is the **ultrametric triangle inequality**. For $v_p$ the customary choice is $c=p^{-1}$, so $|p|_p=p^{-1}$ and $|p^n a/b|_p=p^{-n}$ when $a,b$ are prime to $p$.

Conversely, a multiplicative absolute value with the ultrametric inequality yields a real-valued additive valuation after choosing a logarithmic base:

$$
v(x)=\log_c|x|
$$

so that $c^{v(x)}=|x|$. Because $c<1$, small absolute values correspond to large positive valuations. Different choices of $c$ rescale the valuation by a positive constant and give the same topology.

Two nontrivial absolute values are **equivalent** when they define the same topology. For nonarchimedean absolute values this happens exactly when there is a real $r>0$ such that

$$
|x|_2=|x|_1^r
$$

for all $x\in K$. One way to see the rigidity is to compare the elements whose powers tend to zero. Topological equivalence gives the same order comparisons between the logarithmic valuations, and an order-preserving homomorphism between subgroups of $\mathbf R$ is multiplication by a positive scalar. Thus the topology remembers the valuation up to a harmless choice of scale. For a normalized prime-adic valuation, the customary condition $|p|_p=p^{-1}$ fixes that scale.

There is also a useful algebraic test for the strong inequality. An absolute value is nonarchimedean if and only if $|n|\leq1$ for every integer $n$ mapped into $K$. The forward implication follows by adding $1$ repeatedly. Conversely, the binomial theorem gives

$$
|x+y|^m\leq \sum_{i=0}^m\binom mi |x|^i|y|^{m-i}
\leq (m+1)\max\{|x|,|y|\}^m.
$$

Taking $m$th roots and letting $m$ grow yields the ultrametric inequality. This criterion explains why every absolute value on a field of positive characteristic is nonarchimedean: the image of the integers is finite.

Not every valuation has real values. Higher-rank ordered groups have no faithful real scale, and their natural topology must be expressed through value inequalities rather than one real metric. Our analytic chapters concentrate on rank-one valuations, especially discrete ones, where an ultrametric captures the topology completely.

### 2.6 The trivial valuation and failure modes

The **trivial valuation** on a field sends every nonzero element to $0$. Its valuation ring is the whole field and its induced absolute value is $1$ away from zero. The resulting metric is discrete: distinct points have distance $1$. It satisfies every formal axiom but carries no local arithmetic information. We will generally say explicitly when a valuation is nontrivial.

The ordinary absolute value on $\mathbf Q$ is multiplicative but not nonarchimedean: $|1+1|=2>1$. Its topology and completion lead to the real numbers, not to a valuation ring of the kind studied here. This contrast is structural. In an ultrametric space, a sum cannot be larger than its largest summand, triangles are dominated by their longest side, and series converge under a criterion unavailable over $\mathbf R$.

### 2.7 Gauss valuations and two-stage measurement

Valuations can be transported from coefficients to polynomials. Let $(K,v)$ be a valued field and fix $\alpha$ in an ordered group containing $\Gamma_v$. For a nonzero polynomial $f=\sum_i a_iT^i$, set

$$
v_\alpha(f)=\min_i\{v(a_i)+i\alpha\}.
$$

The sum inequality is immediate. Multiplicativity deserves attention because several products can contribute to the same coefficient and cancel. Choose among the terms of least weighted value in each polynomial the one of largest index. The product of those selected terms has least possible value in the product, and among terms of that value it has uniquely largest combined index. It therefore cannot cancel. Hence $v_\alpha(fg)=v_\alpha(f)+v_\alpha(g)$, and the valuation extends to $K(T)$ by quotients.

When $\alpha=0$, this is the Gauss valuation: a polynomial has value equal to the minimum value of its coefficients. Its residue remembers a polynomial over the residue field after scaling one coefficient to a unit. When $\alpha>0$, the variable itself is treated as small. The formula explains how coefficient size and order in a parameter can be combined into one measurement.

There is also a genuinely higher-rank combination. On $K((T))$, first record the lowest exponent of $T$, then record the valuation of its leading coefficient. The values lie in lexicographically ordered $\mathbf Z\times\Gamma_v$:

$$
w\left(\sum_{i\geq n}a_iT^i\right)=(n,v(a_n)).
$$

This valuation distinguishes two scales: any positive $T$-order outweighs every coefficient valuation. Coarsening to the first coordinate gives the ordinary $T$-adic valuation; passing to the residue at that first stage recovers the valuation on $K$. This example makes higher rank concrete while also showing why our later analytic treatment, based on a single real absolute value, naturally focuses on rank one.

## 3. Valuation rings and divisibility

### 3.1 Bounded elements

Once a valuation has been defined on a field, its first algebraic output is the ring of elements that do not blow up. Separating bounded elements from poles converts an external numerical measurement into an intrinsic local ring.

Let $K$ be a field with valuation $v:K^\times\to\Gamma$. The elements having no pole form

$$
V=\{x\in K:v(x)\geq0\}\cup\{0\}.
$$

This is the **valuation ring** of $v$. The valuation inequalities show that it is a subring. Its strictly positive elements form

$$
\mathfrak m_V=\{x\in K:v(x)>0\}\cup\{0\}.
$$

An element $x\in V$ is invertible in $V$ exactly when $v(x)=0$, because $v(x^{-1})=-v(x)$. Thus $\mathfrak m_V$ is precisely the set of nonunits, so $V$ is local with unique maximal ideal $\mathfrak m_V$. The quotient

$$
\kappa(v)=V/\mathfrak m_V
$$

is the residue field.

The names “bounded” and “infinitesimal” are useful. Under a multiplicative absolute value with $c<1$, $V$ consists of $|x|\leq1$ and $\mathfrak m_V$ of $|x|<1$. Reduction to the residue field forgets infinitesimal differences. Two bounded elements have the same residue exactly when their difference is strictly smaller than $1$.

For $v_p$ on $\mathbf Q$, the ring is $\mathbf Z_{(p)}$, the maximal ideal is $p\mathbf Z_{(p)}$, and the residue field is $\mathbf F_p$. For $\operatorname{ord}_t$ on $k(t)$, the ring is $k[t]_{(t)}$, maximal ideal is generated by $t$, and residue field is $k$, via evaluation at $t=0$.

The characteristic of $\kappa(v)$ is the **residue characteristic**. If it equals $\operatorname{char}(K)$, the valued field has **equal characteristic**; otherwise $K$ has characteristic $0$ and the residue field has characteristic some prime $p$, and one speaks of **mixed characteristic $(0,p)$**. The models are respectively $k((t))$ and $\mathbf Q_p$. This distinction does not change the elementary valuation laws, but it changes how residue representatives multiply and how derivatives behave in lifting arguments.

### 3.2 The intrinsic characterization

The numerical definition is efficient, but the ring knows the valuation. The following theorem is the intrinsic gateway.

**Theorem 3.1 (valuation-ring criterion).** Let $K$ be a field and $V\subset K$ a subring. The following conditions are equivalent.

1. $V$ is the valuation ring of a valuation on $K$.
2. For every $x\in K^\times$, either $x\in V$ or $x^{-1}\in V$.
3. The principal fractional ideals $xV$, for $x\in K^\times$, are totally ordered by inclusion.

The valuation is determined up to equivalence by $V$.

**Proof roadmap.** A valuation compares $v(x)$ with $0$, which gives condition 2. Comparing $xV$ and $yV$ is the same as deciding whether $x/y$ or $y/x$ lies in $V$, giving condition 3. To reconstruct a valuation, quotient $K^\times$ by the unit group $V^\times$ and order the quotient through divisibility.

**Proof.** If $V$ comes from $v$, then either $v(x)\geq0$ or $v(x^{-1})=-v(x)\geq0$. Thus 1 implies 2. Next, $xV\subseteq yV$ exactly when $x/y\in V$. Applied to $x/y$, condition 2 therefore gives condition 3, and taking $y=1$ shows the converse.

Assume condition 2. Let

$$
\Gamma=K^\times/V^\times
$$

and write $v(x)$ for the class of $x$. Define $v(x)\geq v(y)$ when $x/y\in V$. This is well defined under multiplication by units. Condition 2 makes the order total, and multiplication in $K^\times$ makes $\Gamma$ an ordered abelian group. The set of elements with $v(x)\geq0$ is exactly $V$. It remains to see the addition inequality. If, say, $v(x)\leq v(y)$, then $y/x\in V$, and

$$
\frac{x+y}{x}=1+\frac yx\in V.
$$

Hence $v(x+y)\geq v(x)$. This constructs the valuation. Since its comparisons are prescribed by membership of quotients in $V$, any other valuation ring equal to $V$ gives an equivalent valuation. $\square$

The theorem changes the subject from numerical functions to commutative algebra. It tells us that a local subring of a field is a valuation ring precisely when every pair of elements is comparable by divisibility.

### 3.3 Ideals are ordered

Let $V$ be a valuation ring. Any two ideals of $V$ are comparable. Indeed, if neither $I\subseteq J$ nor $J\subseteq I$, choose $x\in I\setminus J$ and $y\in J\setminus I$. The principal ideals $(x)$ and $(y)$ are comparable; either comparison contradicts one of the choices.

More concretely, principal ideals reverse value:

$$
(x)\subseteq(y)\quad\Longleftrightarrow\quad v(x)\geq v(y).
$$

Every finitely generated ideal is principal, because among finitely many generators one has least value and divides all the others. Therefore every valuation ring is a Bézout domain. It need not be a principal ideal domain: infinitely generated ideals may have no element of least value. The nondiscrete $\mathbf Q$-valued example from Chapter 1 illustrates exactly this failure.

An ideal can be described by the values of its nonzero elements. This set is upward closed in the nonnegative cone $\Gamma_{\geq0}$. Conversely, any upward-closed subset stable under addition by $\Gamma_{\geq0}$ determines an ideal, provided it uses values that occur. In a discrete group, every nonempty upward-closed set has a least element, making every nonzero ideal principal. In a dense group, a cut such as $\{\gamma>\alpha\}$ may have no least value.

### 3.4 Prime ideals and rank

The chain of prime ideals in a valuation ring reflects the hierarchy of scales in its value group. Convex subgroups of $\Gamma$ correspond, with reversed inclusions, to prime ideals of $V$. We need only the main consequence: a nontrivial valuation ring has Krull dimension one exactly when its value group has rank one. In that case its only prime ideals are $(0)$ and $\mathfrak m_V$.

For a rank-one valuation, every positive value is eventually exceeded by multiples of any other positive value. If $0\ne x\in\mathfrak m_V$ and $0\ne y\in\mathfrak m_V$, some $n$ satisfies $nv(x)\geq v(y)$, so $x^n\in(y)$. Hence the radical of every nonzero proper ideal is $\mathfrak m_V$. This is the valuation-theoretic face of one-dimensionality.

Lexicographic $\mathbf Z^2$ behaves differently. Elements of value $(1,0)$ remain larger than every multiple of $(0,1)$, so there is a nonzero prime ideal separating the two scales. A single “infinitesimal” comparison cannot capture this geometry.

### 3.5 Integrality and maximality

Valuation rings are integrally closed. Suppose $x\in K$ is integral over $V$. If $x\notin V$, then $x^{-1}\in\mathfrak m_V$. From a monic relation

$$
x^n+a_{n-1}x^{n-1}+\cdots+a_0=0
$$

divide by $x^n$ to obtain

$$
1+a_{n-1}x^{-1}+\cdots+a_0x^{-n}=0.
$$

Every term after $1$ lies in $\mathfrak m_V$, so their sum cannot equal $-1$, a unit. This contradiction proves $x\in V$.

There is also a useful maximality principle: valuation rings are maximal among local subrings of $K$ dominated by the same place. More precisely, if $V\subseteq W\subseteq K$ is local and the maximal ideal of $W$ contracts to $\mathfrak m_V$, then $W=V$. For if $x\in W\setminus V$, then $x^{-1}\in\mathfrak m_V\subseteq\mathfrak m_W$, while $x$ and $x^{-1}$ both lie in $W$, contradicting that an element of the maximal ideal cannot be a unit.

### 3.6 Residues and leading coefficients

Reduction $V\to\kappa(v)$ extracts the value-zero part of a bounded element. When the value group is $\mathbf Z$ and a uniformizer $\pi$ has value $1$, every $x\ne0$ can be written uniquely in the form

$$
x=\pi^{v(x)}u,
$$

with $u\in V^\times$. The residue $\overline u\in\kappa(v)^\times$ is the leading coefficient of $x$ relative to $\pi$. Define

$$
\operatorname{ac}_\pi(x)=\overline{\pi^{-v(x)}x},\qquad
\operatorname{ac}_\pi(0)=0.
$$

This angular-component map is multiplicative. It depends on $\pi$: replacing $\pi$ by $a\pi$, with $a$ a unit, multiplies the angular component of an element of value $n$ by $\overline a^{-n}$. Thus the leading coefficient is not intrinsic without a choice of parameter, although the pair “value plus leading term in the associated graded ring” is intrinsic.

For $k((t))$, the value of $\sum_{n\geq N}a_nt^n$ is the least $n$ with $a_n\ne0$, and its angular component for $t$ is $a_n$. For $\mathbf Q$ with $v_p$, the angular component of $p^n a/b$, with $p\nmid ab$, is $\overline a\,\overline b^{-1}\in\mathbf F_p^\times$. These examples make precise the slogan that a valuation records the first nonzero digit.

## 4. Discrete valuation rings

### 4.1 Why discreteness is decisive

A general valuation ring has totally ordered ideals, but the ordering may be continuous: there need not be a first positive magnitude. Discreteness replaces that continuum by steps. If the value group is $\mathbf Z$, an element of value $1$ generates the maximal ideal, every ideal is a power of it, and questions about divisibility become questions about integers. The same condition has several algebraic disguises, each useful in a different setting.

A **discrete valuation** is a surjective valuation $v:K^\times\to\mathbf Z$. Its valuation ring is a **discrete valuation ring**, abbreviated DVR. An element $\pi$ with $v(\pi)=1$ is a **uniformizer**. Every $x\in K^\times$ has a unique expression $x=\pi^n u$ with $n\in\mathbf Z$ and $u$ a unit. Two uniformizers differ by a unit, and every generator of the maximal ideal is a uniformizer.

### 4.2 Equivalent characterizations

In applications a local ring is often presented by generators, ideals, dimension, or normality rather than by a valuation function. The next theorem shows that several familiar one-dimensional conditions all recover the same discrete measurement.

**Theorem 4.1 (characterizations of a DVR).** Let $A$ be a domain that is not a field, with fraction field $K$. The following are equivalent.

1. $A$ is the valuation ring of a discrete valuation $K^\times\to\mathbf Z$.
2. $A$ is a Noetherian valuation ring.
3. $A$ is a principal ideal domain with a unique nonzero prime ideal.
4. $A$ is a one-dimensional Noetherian local domain whose maximal ideal is principal.
5. $A$ is a one-dimensional Noetherian local integrally closed domain.
6. $A$ is local and has $0\ne\pi$ such that every nonzero ideal is uniquely $(\pi^n)$ for $n\geq0$.

In each case the maximal ideal is $(\pi)$, and the normalized valuation is uniquely determined by $A$.

**Proof roadmap.** From a discrete valuation, the least value in an ideal gives its generator. Conversely, a principal maximal ideal allows repeated division by its generator; Noetherianity forces that process to stop. The integrally closed characterization uses an element of the inverse of the maximal ideal: it either makes that ideal principal or is forced to be integral.

**Proof.** Suppose 1 holds. If $I\ne0$, choose $x\in I$ of least valuation. Every $y\in I$ has $v(y)\geq v(x)$, so $y/x\in A$ and $I=(x)=(\pi^{v(x)})$. This gives 6, and $A$ is a PID with unique nonzero prime $(\pi)$. Thus 3 and 2 follow. Condition 3 gives 4 and 6 immediately.

Suppose 2 holds. Its maximal ideal is finitely generated and hence principal, because every finitely generated ideal of a valuation ring is generated by an element of least value. Write $\mathfrak m=(\pi)$. The argument in the next paragraph, which uses only Noetherianity and this principal maximal ideal, shows that every nonzero element is $\pi^n$ times a unit. Sending the least positive value $v(\pi)$ to $1$ therefore identifies the value group with $\mathbf Z$. Thus 2 implies 1.

Assume 4, say $\mathfrak m=(\pi)$. For $0\ne x\in A$, if $x$ lay in every $(\pi^n)$, write $x=\pi^n x_n$. The ideals $(x_n)$ ascend and eventually stabilize. Then $x_n=\pi x_{n+1}$ and $(x_n)=(x_{n+1})$, making $\pi$ a unit, impossible. Hence some largest $n$ has $x\in(\pi^n)$, and $x=\pi^n u$ with $u\notin\mathfrak m$, hence a unit. This gives 6 and defines $v(x/y)=n_x-n_y$.

A DVR is integrally closed, so 1 implies 5. Now suppose 5. Choose $0\ne x\in\mathfrak m$. Since the radical of $(x)$ is $\mathfrak m$, some least $n\geq1$ satisfies $\mathfrak m^n\subseteq(x)$. Choose $y\in\mathfrak m^{n-1}\setminus(x)$. Then $z=y/x$ satisfies $z\mathfrak m\subseteq A$, while $z\notin A$. If $z\mathfrak m\subseteq\mathfrak m$, multiplication by $z$ is an endomorphism of the finite $A$-module $\mathfrak m$. The determinant trick gives a monic polynomial over $A$ satisfied by $z$, contradicting integral closedness. Hence $z\mathfrak m=A$. Choose $\pi\in\mathfrak m$ with $z\pi=1$. Every $a\in\mathfrak m$ has $za\in A$, hence $a=\pi(za)$, so $\mathfrak m=(\pi)$. This proves 4. Uniqueness follows from the unique ideal exponent. $\square$

The Noetherian hypothesis is indispensable. A nondiscrete rank-one valuation ring is local, one-dimensional, and integrally closed, but not Noetherian and not a DVR.

### 4.3 Arithmetic and examples

After the recognition theorem, the abstract ring becomes computational. Fixing a uniformizer translates divisibility, units, and ideal operations into integer arithmetic and lets us compare the principal examples without changing language.

Fix a DVR $A$, maximal ideal $\mathfrak m=(\pi)$, fraction field $K$, normalized valuation $v$, and residue field $k$. Then

$$
x\in A\iff v(x)\geq0,
\quad x\in A^\times\iff v(x)=0,
\quad x\in\mathfrak m^r\iff v(x)\geq r.
$$

Divisibility is total. Sums and intersections satisfy

$$
(\pi^a)+(\pi^b)=(\pi^{\min(a,b)}),\qquad
(\pi^a)\cap(\pi^b)=(\pi^{\max(a,b)}).
$$

Products add exponents. An element is irreducible precisely when it has value $1$, and all irreducibles are associates.

For a prime $p$, $\mathbf Z_{(p)}$ is a DVR with uniformizer $p$ and residue field $\mathbf F_p$. For a field $k$, $k[t]_{(t)}$ is a DVR. For irreducible $P\in k[t]$, $k[t]_{(P)}$ has uniformizer $P$ and residue field $k[t]/(P)$.

The formal power-series ring

$$
k[[t]]=\left\{\sum_{n=0}^\infty a_nt^n:a_n\in k\right\}
$$

is a DVR: a series is a unit exactly when $a_0\ne0$, and each nonzero series is $t^n u$. Its fraction field is $k((t))$, the Laurent-series field. Unlike $k[t]_{(t)}$, $k[[t]]$ is complete. Both have uniformizer $t$ and residue field $k$.

If $R$ is Dedekind and $\mathfrak p\ne0$, then $R_{\mathfrak p}$ is a DVR. A uniformizer need only generate $\mathfrak pR_{\mathfrak p}$, not $\mathfrak p$ globally.

The local ring $k[x,y]_{(x,y)}$ is integrally closed but two-dimensional, so not a DVR. The one-dimensional complete domain $k[[t^2,t^3]]$ is not integrally closed: $t$ is integral over it but absent. The complete regular local ring $\mathbf Z_p[[t]]$ has dimension two and maximal ideal $(p,t)$. These failures separate dimension, normality, and completeness.

## 5. The valuation filtration

### 5.1 Successive precision

Reduction modulo $\mathfrak m$ keeps only the leading digit. Increasing precision means reducing modulo $\mathfrak m^n$. Since $\mathfrak m^n=(\pi^n)$, these ideals form a strictly descending chain with intersection zero.

Multiplication by $\pi^n$ gives an isomorphism

$$
A/(\pi)\longrightarrow(\pi^n)/(\pi^{n+1}),
\qquad \overline a\longmapsto\overline{a\pi^n}.
$$

If $a\pi^n\in(\pi^{n+1})$, cancellation gives $a\in(\pi)$. Thus each layer is one-dimensional over $k$, and short exact sequences give

$$
\operatorname{length}_A(A/(\pi^n))=n,
\qquad
\operatorname{length}_A(A/(x))=v(x)
$$

for $0\ne x\in A$. A finitely generated torsion module decomposes as $\bigoplus_i A/(\pi^{n_i})$ and has length $\sum_i n_i$.

### 5.2 Leading terms and digits

Successive quotients become more informative when they are multiplied together. The associated graded ring records the first surviving term of every element, while residue representatives turn the same layers into digits.

The filtration packages leading terms into

$$
\operatorname{gr}_{\mathfrak m}(A)
=\bigoplus_{n\geq0}\mathfrak m^n/\mathfrak m^{n+1}\cong k[T],
$$

where $T$ is the initial form of $\pi$. Replacing $\pi$ by $u\pi$ sends $T$ to $\overline uT$. Initial forms multiply; equal-degree initial forms may cancel under addition, explaining the strict valuation inequality.

Choose representatives $S\subset A$ for $k$, including $0$. Every class modulo $\pi^n$ has a unique expression

$$
s_0+s_1\pi+\cdots+s_{n-1}\pi^{n-1}\pmod{\pi^n},
\qquad s_i\in S.
$$

Choose $s_0$ modulo $\pi$, divide $x-s_0$ by $\pi$, and repeat. Uniqueness follows by inspecting the first differing coefficient. Infinite expansions require completeness; arbitrary infinite base-$p$ strings generally do not represent elements of $\mathbf Z_{(p)}$.

If $|k|=q<\infty$, then $|A/(\pi^n)|=q^n$ for $n\geq0$. For $n\geq1$, the quotient is Artinian local, with ideals $(\overline\pi^i)$, and $\overline\pi$ has nilpotence index $n$.

### 5.3 Fractional ideals and precision

Integral ideals record zeros, but field elements may also have poles. Fractional ideals extend the filtration to negative indices and make precise how multiplication shifts a known level of accuracy.

Every nonzero fractional ideal equals $\mathfrak m^n=(\pi^n)$ for a unique $n\in\mathbf Z$. Hence their group is infinite cyclic and $K^\times/A^\times\cong\mathbf Z$. For a Dedekind domain, localization at $\mathfrak p$ projects the global ideal exponent vector onto its $\mathfrak p$-coordinate.

Multiplication shifts the filtration exactly:

$$
x\mathfrak m^n=\mathfrak m^{n+v(x)}
\qquad(x\in K^\times,\ n\in\mathbf Z).
$$

Thus units preserve precision, maximal-ideal elements gain it, and negative-valued elements lose digits. Ramification indices will measure this shift between two valuation filtrations.

### 5.4 Filtered modules and elementary divisors

The ideal filtration becomes more powerful when several coordinates must be controlled at once. A lattice is the integral shadow of a finite-dimensional vector space, and elementary divisors say that two lattices differ by finitely many independent shifts of valuation. This is the mechanism behind length formulas, determinant valuations, and later comparisons between integral closures and coordinate lattices.

Let $M$ be a free $A$-module of finite rank. Its filtration is

$$
M\supset \pi M\supset \pi^2M\supset\cdots.
$$

Each layer $\pi^nM/\pi^{n+1}M$ is naturally isomorphic to the $k$-vector space $M/\pi M$. In particular, if $M$ has rank $r$, then

$$
\operatorname{length}_A(M/\pi^nM)=nr.
$$

The intersection of all $\pi^nM$ is zero: in coordinates, a vector divisible by every power of $\pi$ has every coordinate equal to zero. Thus the filtration is separated. A congruence $x\equiv y\pmod{\pi^nM}$ means that the two vectors agree to precision $n$; applying an $A$-linear map cannot decrease that precision.

A full **lattice** in a finite-dimensional $K$-vector space $E$ is a finitely generated $A$-submodule $M\subset E$ whose $K$-span is $E$. Any two full lattices $M,N$ are commensurable: there is an integer $r\geq0$ with

$$
\pi^rM\subseteq N\subseteq\pi^{-r}M.
$$

To prove this, express a basis of each lattice in a basis of the other and clear the finitely many denominators. The assertion is elementary but conceptually important: changing an integral model changes boundedness only by a finite shift.

The structure theorem over the PID $A$ sharpens commensurability. After multiplying one lattice by a scalar, it is enough to consider $N\subseteq M$. There is a basis $e_1,\ldots,e_r$ of $M$ and integers $a_i\geq0$ such that

$$
N=A\pi^{a_1}e_1\oplus\cdots\oplus A\pi^{a_r}e_r.
$$

Consequently

$$
M/N\cong\bigoplus_{i=1}^r A/(\pi^{a_i}),
\qquad
\operatorname{length}_A(M/N)=\sum_i a_i.
$$

If $T:M\to M$ is injective, apply this description to $T(M)\subseteq M$. Elementary row and column operations over $A$ diagonalize the matrix of $T$ up to units. Taking determinants gives the decisive identity

$$
\operatorname{length}_A(M/TM)=v(\det T).
$$

This turns a multiplicative invariant into the size of a filtered quotient. If $E/K$ is a finite field extension and a full $A$-lattice $M\subset E$ is stable under multiplication by $x\in E^\times$, the induced endomorphism has determinant $N_{E/K}(x)$. For multiplication by the base uniformizer on a rank-$r$ free module, the length is $r$. These two readings will account for residue degrees and ramification indices in Chapters 10 and 11.

Not every torsion-free module over an arbitrary valuation ring behaves this cleanly. The diagonal decomposition and finite-length calculation use both discreteness and finite generation. This is another reason DVRs, rather than general valuation rings, are the natural integral objects for finite-dimensional local arithmetic.

## 6. Nonarchimedean topology and analysis

### 6.1 Balls and the strong triangle inequality

Let $K$ carry a nonarchimedean absolute value $|\cdot|$. The formula $d(x,y)=|x-y|$ is a metric; for the trivial absolute value it is simply the discrete metric. Its geometry is controlled by

$$
d(x,z)\leq\max\{d(x,y),d(y,z)\}.
$$

This is stronger than the ordinary triangle inequality, and it changes the meaning of a ball. If $y$ lies in the ball $B(a,r)=\{x:|x-a|<r\}$, then $B(y,r)=B(a,r)$. Indeed, each point of either ball lies in the other by the strong inequality. Every point is a center.

Two balls of the same radius are either disjoint or equal. More generally, two balls that meet are nested when their radii are comparable. Open balls are closed: the complement is a union of balls of the same radius. Closed balls are open when the value group is discrete, because the next larger possible radius gives the same set. Hence valued fields are totally disconnected; connected subsets contain only one point.

If $v$ is a discrete valuation and $|x|=c^{v(x)}$, the ball of radius corresponding to $c^n$ about $a$ is a coset $a+\mathfrak m^{n+1}$ or $a+\mathfrak m^n$, depending on strict versus weak inequality. The precise indexing matters less than the conclusion: the valuation topology on $A$ is exactly the $\mathfrak m$-adic topology.

Triangles are isosceles in a strong sense. If $|x-y|\ne|y-z|$, then

$$
|x-z|=\max\{|x-y|,|y-z|\}.
$$

Thus among three side lengths the maximum occurs at least twice. A mental picture based on Euclidean thin triangles is misleading; points naturally organize into nested clusters.

### 6.2 Continuity of algebraic operations

The metric is useful for algebra only if sums, products, and inverses respect limits. The strong triangle inequality makes that compatibility unusually transparent and prepares the termwise constructions used in completion.

Translation is an isometry, and multiplication by $a$ scales distances by $|a|$. Addition is uniformly continuous because

$$
|(x+y)-(x'+y')|\leq\max\{|x-x'|,|y-y'|\}.
$$

Multiplication is continuous since

$$
xy-x'y'=x(y-y')+y'(x-x').
$$

On a bounded set the two coefficients $x,y'$ have bounded size, giving uniform control. Inversion is continuous away from zero, as

$$
x^{-1}-y^{-1}=\frac{y-x}{xy}.
$$

If $y$ is sufficiently close to nonzero $x$, then $|y|=|x|$, so the denominator has fixed size. Consequently a valued field is a topological field and its valuation ring an open-and-closed topological subring.

The unit group $A^\times$ is open, and reduction $A\to k$ is continuous when $k$ has the discrete topology. Its fibers are the cosets of $\mathfrak m$. More generally, reduction modulo $\mathfrak m^n$ is continuous with discrete target.

### 6.3 Cauchy sequences

To complete a field we must recognize sequences that ought to have limits even when no limit is yet present. In an ultrametric space, consecutive differences already control every longer tail.

A sequence $(x_n)$ is Cauchy when for every $\varepsilon>0$ there is $N$ such that $|x_m-x_n|<\varepsilon$ for $m,n\geq N$. In valuation language, $v(x_m-x_n)$ tends uniformly to infinity. A convergent sequence is Cauchy, and limits are unique.

Nonarchimedean Cauchy behavior has a useful shortcut. If

$$
|x_{n+1}-x_n|\longrightarrow0,
$$

then $(x_n)$ is Cauchy, because for $m>n$,

$$
|x_m-x_n|\leq\max_{n\leq i<m}|x_{i+1}-x_i|.
$$

Over the real numbers, increments tending to zero do not suffice; the harmonic series is the standard warning. Here the largest increment controls the entire tail.

If a sequence converges to a nonzero $x$, then eventually $|x_n|=|x|$. Indeed, once $|x_n-x|<|x|$, unequal-size rigidity applied to $x_n=x+(x_n-x)$ gives equality. In fact the map $x\mapsto|x|$ is locally constant on $K^\times$ for every nonarchimedean absolute value: the open ball $|y-x|<|x|$ is a neighborhood on which $|y|=|x|$. No discreteness of the value group is needed.

### 6.4 Series

Series are the first test of how different nonarchimedean analysis is from real analysis. Because no accumulation of many small terms can exceed the largest one, convergence has a strikingly simple criterion.

In a complete nonarchimedean field, a series $\sum_{n\geq0}a_n$ converges if and only if $a_n\to0$. Necessity holds in every topological group. For sufficiency, partial-sum differences satisfy

$$
\left|\sum_{i=n+1}^m a_i\right|
\leq\max_{n<i\leq m}|a_i|,
$$

which tends to zero; completeness supplies the limit.

This criterion makes many formal manipulations transparent. If $|x|<1$, the geometric series converges and

$$
(1-x)^{-1}=\sum_{n=0}^\infty x^n.
$$

Hence $1+\mathfrak m\subset A^\times$, a fact already known algebraically but now accompanied by an explicit inverse. More generally, if $a_n\to0$, reordering the terms does not change the sum: tails after any finite set are bounded by the largest omitted term. Double sums may be rearranged whenever, for each threshold, only finitely many terms exceed it.

For $k((t))$, the series $1+t+t^2+\cdots$ converges to $(1-t)^{-1}$. The same formula in $\mathbf Q_p$ works for $|x|_p<1$. By contrast, $1+p^{-1}+p^{-2}+\cdots$ has terms of growing size and cannot converge $p$-adically, although it is a geometric expression algebraically.

### 6.5 Infinite products

Multiplicative correction processes naturally produce products rather than sums. The same tail estimate shows when their partial products stabilize and ensures that a product of nonzero near-units does not collapse to zero.

An infinite product $\prod_{n\geq0}(1+a_n)$ in a complete valued field is defined as the limit of partial products. If $a_n\to0$, then the product converges. For large $n$, $|a_n|<1$, so $|1+a_n|=1$. For $m>n$,

$$
\prod_{i=n+1}^m(1+a_i)-1
$$

is a sum of products, each containing at least one $a_i$; its absolute value is at most $\max_{i>n}|a_i|$. Thus the partial products are Cauchy. Their limit is nonzero if none of the factors is zero, because sufficiently late partial products are units and earlier nonzero factors have fixed absolute value.

This clean criterion is another ultrametric privilege. It underlies constructions of analytic functions and successive correction procedures. The essential condition is not summability of $|a_n|$ but simply $a_n\to0$.

### 6.6 Compactness and local compactness

Completeness should not be confused with compactness. If $A$ is a complete DVR with finite residue field $k$ of size $q$, then $A$ is compact. Given a sequence in $A$, infinitely many terms have the same residue modulo $\pi$; pass to that subsequence. Then pass to a subsequence constant modulo $\pi^2$, and so on. A diagonal subsequence is Cauchy and therefore converges. In metric spaces, sequential compactness gives compactness.

If $k$ is infinite, the residue classes modulo $\pi$ form an infinite disjoint open cover of $A$, so $A$ is not compact. This also rules out local compactness of $K$: if $K$ had a compact neighborhood of $0$, it would contain some ball $\pi^nA$; that ball is closed in the compact neighborhood and hence compact, and scaling would make $A$ compact. Thus a complete discretely valued field is locally compact exactly when its residue field is finite. In that case $K=\bigcup_{n\geq0}\pi^{-n}A$ is locally compact but not compact.

The fields $\mathbf Q_p$ and finite extensions of it are locally compact. The field $k((t))$ is locally compact when $k$ is finite, but not when $k$ is infinite. All are complete; the residue field decides compactness.

### 6.7 Nondiscrete topology

For a rank-one nondiscrete valuation, choose an embedding of the value group in $\mathbf R$ and an associated absolute value. Balls now occur at a dense range of radii. The valuation ring is still the closed unit ball and its maximal ideal the open unit ball, but powers of a single ideal need not form a neighborhood basis. Indeed, the maximal ideal may satisfy $\mathfrak m^2=\mathfrak m$: every positive value can be split into two smaller positive values when the value group is divisible.

Thus the $\mathfrak m$-adic topology can be much coarser than the valuation topology outside the discrete setting. Statements identifying completion with $\varprojlim A/\mathfrak m^n$ require a discrete valuation, or more generally a chosen ideal whose powers are valuation-open and form a neighborhood basis of zero.

## 7. Completion

### 7.1 Filling the missing limits

The ring $\mathbf Z_{(p)}$ permits every finite $p$-adic approximation, but many compatible infinite digit strings have no rational representative. Completion adds exactly the limits forced by the metric, without adding algebraic relations unnecessarily.

A **completion** of a metric valued field $K$ is a complete valued field $\widehat K$ together with an isometric embedding $i:K\to\widehat K$ having dense image. It is unique up to a unique isometric field isomorphism commuting with the embeddings.

One construction uses Cauchy sequences. Declare two Cauchy sequences equivalent if their difference tends to zero. Termwise addition and multiplication descend to equivalence classes; the constant sequences embed $K$. The absolute value extends by

$$
|(x_n)|=\lim_n|x_n|.
$$

Why does this limit exist? If the sequence tends to zero, the answer is zero. Otherwise it is eventually at distance smaller than one of its nonzero terms, after which all $|x_n|$ are equal. This also shows independence of the representative. A diagonal argument proves the resulting space complete.

### 7.2 Extending inverses

It is worth isolating why completion remains a field. Let $(x_n)$ represent a nonzero class. It does not tend to zero, so after discarding finitely many terms, $|x_n|$ is a fixed positive number. Then $(x_n^{-1})$ is Cauchy because

$$
|x_m^{-1}-x_n^{-1}|=
\frac{|x_m-x_n|}{|x_mx_n|}.
$$

Its class is the inverse of $(x_n)$. Thus the completion of a valued field, unlike the completion of an arbitrary domain at an ideal, is automatically a field.

The additive valuation also extends. For a discrete valuation, any nonzero Cauchy class has representatives of eventually constant valuation, and that integer is its value. The same local constancy holds for every rank-one valuation: a representative sufficiently close to a nonzero limit has exactly the limit's absolute value. Thus metric completion preserves the value group, even when that group is dense in $\mathbf R$.

### 7.3 Universal property

The construction matters less than its mapping property.

**Theorem 7.1 (universal property of completion).** Let $K$ be a valued field, $i:K\to\widehat K$ its completion, and $F$ a complete Hausdorff valued field. Every uniformly continuous map $f:K\to F$ extends uniquely to a continuous map $\widehat f:\widehat K\to F$. If $f$ is a field homomorphism compatible with the absolute values, then $\widehat f$ is a field homomorphism with the same compatibility.

**Proof roadmap.** Approximate a point of $\widehat K$ by a sequence from $K$, apply $f$, and take the limit in $F$. Uniform continuity makes the image sequence Cauchy and makes the result independent of choices. Density gives uniqueness. Algebraic identities pass to limits because operations are continuous.

**Proof.** For $x\in\widehat K$, choose $x_n\in K$ with $i(x_n)\to x$ and set $\widehat f(x)=\lim f(x_n)$. Uniform continuity makes $(f(x_n))$ Cauchy. If $y_n$ is another approximation, then $d(x_n,y_n)\to0$, so uniform continuity yields $d(f(x_n),f(y_n))\to0$; the limit is independent of the approximation. The construction extends $f$ and is continuous. Any continuous extension must take $x$ to the same limit, proving uniqueness. When $f$ respects sums and products, continuity lets those identities pass to the limits. $\square$

The Hausdorff condition prevents distinct candidate limits; completeness supplies existence. This theorem is the legitimate way to define functions on a completion. One defines them densely and proves uniform continuity.

### 7.4 Completion of the valuation ring

Completing the field should not obscure which elements are integral. The closed unit ball survives completion exactly, and in the discrete case every finite quotient remains unchanged.

Let $A$ be the valuation ring of a rank-one valued field $K$. The closure of $A$ in $\widehat K$ is the valuation ring $\widehat A$ of the extended valuation. One inclusion follows because $|x|\leq1$ is a closed condition. Conversely, if $x\in\widehat K$ has $|x|\leq1$, approximate it by $x_n\in K$ close enough that $|x-x_n|\leq1$; then $|x_n|\leq1$, so $x_n\in A$.

In fact completion is an **immediate extension**: it changes neither the value group nor the residue field. If $0\ne x\in\widehat K$, choose $a\in K$ with

$$
|x-a|<|x|.
$$

Then $|a|=|x|$, so every nonzero absolute value attained in the completion was already attained in $K$. If $x\in\widehat A^\times$, choose $a\in K$ with $|x-a|<1$. Then $|a|=1$, hence $a\in A^\times$, and $x$ and $a$ have the same residue. Thus $A/\mathfrak m_A\to\widehat A/\mathfrak m_{\widehat A}$ is both injective and surjective. Completion supplies missing limits without inserting a new value scale or new leading coefficients.

This statement also corrects a tempting misconception in the nondiscrete case. The set of real values may be dense, but metric completion still does not fill gaps in that set: closeness to a nonzero limit forces eventual equality of absolute values. What can fail outside the discrete case is the description of completion by powers of the maximal ideal, not immediacy of the completed valued-field extension.

For a DVR the picture is sharper.

**Theorem 7.2 (completion of a DVR).** Let $A$ be a DVR with fraction field $K$, uniformizer $\pi$, and residue field $k$. The closure $\widehat A\subset\widehat K$ is a complete DVR with the same uniformizer, value group $\mathbf Z$, and residue field canonically $k$. Moreover $\widehat K=\operatorname{Frac}(\widehat A)$ and $A/(\pi^n)\cong\widehat A/(\pi^n)$ for every $n\geq1$.

**Proof roadmap.** Values of a nonzero convergent sequence eventually stabilize, so completion introduces no fractional values. Density gives representatives modulo every power of $\pi$. Finally, any completed-field element can be scaled into the completed valuation ring.

**Proof.** The extended value of any nonzero $x\in\widehat K$ equals the eventual value of a sufficiently close sequence from $K$, hence lies in $\mathbf Z$. Since $\pi$ still has value $1$, the value group is all of $\mathbf Z$, and its valuation ring is a DVR with maximal ideal $(\pi)$. For $x\in\widehat A$, density gives $a\in A$ with $v(x-a)\geq n$, proving surjectivity of $A/(\pi^n)\to\widehat A/(\pi^n)$. Injectivity follows because $A\cap\pi^n\widehat A=\pi^nA$, as both sides are characterized by $v(a)\geq n$. Taking $n=1$ identifies residue fields. Finally, for nonzero $x\in\widehat K$, the element $\pi^{-v(x)}x$ is a unit of $\widehat A$, so $x$ lies in its fraction field. $\square$

Completion preserves the entire finite-level filtration while adding its missing compatible limits. This is the central bridge from local algebra to local analysis.

### 7.5 Separated completion of rings

Metric completion has an algebraic counterpart that makes sense without an absolute value. Comparing the two also identifies the possible obstruction to embedding the original ring: elements invisible at every finite precision.

For any ring $R$ and ideal $I$, the $I$-adic completion is

$$
\widehat R=\varprojlim_n R/I^n.
$$

The natural map $R\to\widehat R$ has kernel $\bigcap_n I^n$. Thus injectivity requires separatedness. For a Noetherian local domain with $I$ in the maximal ideal, the intersection is zero, but in arbitrary rings it need not be.

For a DVR with $I=(\pi)$, this algebraic completion agrees with the metric completion of $A$. We will prove this concretely in the next chapter. Outside the discrete setting, the inverse limit of powers of the maximal ideal may fail to describe the valuation completion, as the nondiscrete example already warned.

### 7.6 Examples of incomplete and complete fields

The field $\mathbf Q$ is incomplete for $|\cdot|_p$. Its completion is $\mathbf Q_p$, while the completion of $\mathbf Z_{(p)}$ is $\mathbf Z_p$. A sequence of rational truncations $\sum_{i=0}^n a_ip^i$ always converges in $\mathbf Z_p$, whatever digits $a_i\in\{0,\ldots,p-1\}$ are chosen.

The field $k(t)$ with the $t$-adic valuation completes to $k((t))$, and $k[t]_{(t)}$ completes to $k[[t]]$. Given a Laurent series, truncation gives rational functions converging to it. Conversely, a Cauchy sequence fixes each coefficient after finitely many stages, producing a Laurent series with a uniform lower bound on exponents.

Completeness depends on the chosen valuation. The same abstract field $\mathbf Q$ has different completions at different primes and at the ordinary absolute value. Completion is a local operation: it magnifies one chosen notion of nearness and discards the others.

## 8. Inverse limits and digit expansions

### 8.1 Compatible finite approximations

For a DVR $A$, an element known to every finite precision is a compatible family

$$
(x_n)_{n\geq1},\qquad x_n\in A/(\pi^n),
$$

such that $x_{n+1}$ reduces to $x_n$. Coordinatewise addition and multiplication make these families a ring. The inverse-limit description says that no further consistency condition is needed.

**Theorem 8.1 (inverse-limit description).** There is a canonical topological-ring isomorphism

$$
\widehat A\xrightarrow{\sim}\varprojlim_n A/(\pi^n).
$$

**Proof.** Map $x\in\widehat A$ to all its residues. If every residue is zero, then $v(x)\geq n$ for every $n$, so $x=0$. For surjectivity, choose lifts $a_n\in A$ of the compatible classes. Compatibility gives $a_{n+1}-a_n\in(\pi^n)$, so $(a_n)$ is Cauchy. Its limit $a$ has residue $x_n$ modulo $\pi^n$. The map and its inverse respect operations. The neighborhoods $(\pi^n)$ correspond to kernels of finite projections, proving the topological claim. $\square$

This theorem makes completeness algebraic. It also makes functoriality easy: a compatible collection of maps on all truncations induces a map on completions.

### 8.2 Infinite digits

The inverse limit is canonical but abstract. Choosing residue representatives turns a compatible family into a convergent expansion and reveals exactly where choices and carries enter.

With residue representatives $S$, every $x\in\widehat A$ has a unique convergent expansion

$$
x=\sum_{n=0}^\infty s_n\pi^n,\qquad s_n\in S.
$$

At stage $n$, the truncated digit lemma chooses the unique first $n$ digits matching $x$ modulo $\pi^n$. Compatibility preserves earlier digits. The partial sums differ from $x$ by an element of $(\pi^n)$, so they converge. Conversely every digit series converges because its terms tend to zero.

Digit addition generally involves carries, so this is a bijection of sets, not usually a coefficientwise ring isomorphism. Whether the carries can be removed depends on whether the digits can be chosen to form a subring. In equal characteristic they can: Theorem 13.15, proved in the final chapter and used here only as a signpost, shows that a complete local ring containing a field contains a **coefficient field**, a subfield $K$ mapping isomorphically onto $k$. Taking $S=K$ then makes the digits close under addition and multiplication, and Corollary 13.17 identifies $A$ with the power series ring $K[[t]]$, in which multiplication is the Cauchy product. In mixed characteristic no such choice is possible, since no embedding of $\mathbf F_p$ into a characteristic-zero ring exists, so carries are unavoidable; the coefficients then form a Cohen ring lying over $A$ rather than a field inside it, again as constructed in the final chapter. Nothing in the present chapter depends on those results.

### 8.3 The p-adic integers and numbers

The universal mixed-characteristic example deserves a construction independent of prior intuition about limits. Its finite quotients define the ring, its digits describe the elements, and inversion of the uniformizer produces the field.

Define

$$
\mathbf Z_p=\varprojlim_n\mathbf Z/p^n\mathbf Z.
$$

Applied to the DVR $\mathbf Z_{(p)}$, Theorem 8.1 identifies this inverse limit with its completion. Theorem 7.2 therefore shows that it is a complete DVR with uniformizer $p$ and residue field $\mathbf F_p$. Every element has a unique expansion

$$
a_0+a_1p+a_2p^2+\cdots,\qquad 0\leq a_i<p.
$$

Its fraction field $\mathbf Q_p$ consists of expansions $\sum_{i=N}^\infty a_ip^i$ with $N\in\mathbf Z$. For a nonzero element, the valuation is the first index with nonzero digit; the all-zero expansion represents $0$, whose valuation is $+\infty$.

Negative ordinary integers have infinite $p$-adic expansions. Since

$$
-1=(p-1)+(p-1)p+(p-1)p^2+\cdots,
$$

the partial sums are $p^n-1$, whose difference from $-1$ is $p^n$. This is no paradox: $p^n\to0$ $p$-adically. More generally, arithmetic carries propagate toward higher powers, exactly as ordinary decimal carries do, but “higher” powers are smaller in the $p$-adic metric.

The rational numbers are dense in $\mathbf Q_p$ but countable, whereas the digit set shows $\mathbf Z_p$ is uncountable. Completion has genuinely added elements. Yet each element is controlled by finite quotients, making $\mathbf Z_p$ compact.

### 8.4 Formal power series

Equal characteristic removes carries between coefficient representatives. The inverse limit then becomes the familiar ring of formal series, making the analogy with p-adic integers exact at the level of filtrations.

For a field $k$,

$$
k[[t]]\cong\varprojlim_n k[t]/(t^n).
$$

Here representatives can be chosen from the embedded copy of $k$, so compatible digits are literally coefficient sequences and operations are the usual Cauchy product. Its fraction field $k((t))$ is complete: a Cauchy sequence eventually fixes the coefficient of each $t^n$ and has a common lower exponent bound.

The analogy

$$
\mathbf Z_p\leftrightarrow k[[t]],
\qquad \mathbf Q_p\leftrightarrow k((t)),
\qquad p\leftrightarrow t
$$

is powerful but incomplete. The left side has characteristic zero with residue characteristic $p$; the right side has equal characteristic $\operatorname{char}(k)$. In $k[[t]]$ the residue field embeds canonically as constants. In $\mathbf Z_p$, $\mathbf F_p$ cannot embed as a subfield. Many structural arguments work uniformly, while coefficient constructions must respect this difference.

### 8.5 Units and principal units

After valuation separates off the power of a uniformizer, the remaining arithmetic lives in the unit group. Its filtration repeats the additive residue field one layer at a time.

For a complete DVR,

$$
A^\times\supset U^1\supset U^2\supset\cdots,
\qquad U^n=1+\mathfrak m^n.
$$

Reduction yields $A^\times/U^1\cong k^\times$. For $n\geq1$, the map

$$
U^n/U^{n+1}\longrightarrow\mathfrak m^n/\mathfrak m^{n+1},
\qquad 1+x\longmapsto x
$$

is an isomorphism of abelian groups, because $(1+x)(1+y)\equiv1+x+y\pmod{\mathfrak m^{n+1}}$. Thus the unit group is assembled from the residue multiplicative group and additive residue-field layers.

An infinite product of principal units $\prod(1+a_n)$ converges whenever $a_n\to0$. This gives a multiplicative version of digit-by-digit construction. We postpone refined structure of unit groups, but the filtration already shows why units carry most of the subtle arithmetic after the valuation has been separated off.

### 8.6 Complete does not mean algebraically closed

Completion fills analytic gaps, not algebraic ones. The polynomial $X^2-u$ may have no root in a complete valued field even though approximations exist to low precision. For instance, a nonsquare residue unit cannot be a square upstairs: reducing a hypothetical square would make its residue a square. Conversely, a simple root modulo the maximal ideal does lift. The missing principle is that a sufficiently nondegenerate approximate root can be corrected indefinitely. That is Hensel's lemma, the subject of the next chapter.

## 9. Hensel lifting

### 9.1 Correcting an approximate root

Suppose $A$ is a complete DVR and $f\in A[X]$. A residue class $\overline a\in k$ satisfying $\overline f(\overline a)=0$ is a first approximation to a root. It need not lift: $X^2-p$ has the root $0$ modulo $p$, but no root in $\mathbf Q_p$ because the valuation of a square is even. The defect is that the derivative also vanishes modulo $p$. When $\overline f'(\overline a)\ne0$, linearization predicts a unique correction.

Write $a_1=a+h$. Taylor expansion gives

$$
f(a+h)=f(a)+hf'(a)+h^2g
$$

for some $g\in A$ when $a,h\in A$. If $f'(a)$ is a unit, choose $h$ modulo the next power of $\pi$ so that the first two terms cancel. Repeating doubles or at least increases the known precision. Completeness turns the corrections into an actual root.

**Theorem 9.1 (simple-root form of Hensel's lemma).** Let $A$ be a complete DVR with maximal ideal $\mathfrak m$ and residue field $k$. If $f\in A[X]$ and $a_0\in A$ satisfy

$$
f(a_0)\in\mathfrak m,\qquad f'(a_0)\notin\mathfrak m,
$$

then there is a unique $a\in A$ such that

$$
f(a)=0,\qquad a\equiv a_0\pmod{\mathfrak m}.
$$

**Proof roadmap.** Newton's correction $-f(a_n)/f'(a_n)$ is integral because the denominator is a unit. Taylor expansion shows that it squares the error. The corrections tend to zero, producing a limit. Any two roots in the residue class differ by a factor times a unit, so they coincide.

**Proof.** Define

$$
a_{n+1}=a_n-\frac{f(a_n)}{f'(a_n)}.
$$

Inductively $f'(a_n)$ is a unit: since $a_n\equiv a_0\pmod{\mathfrak m}$, polynomial evaluation gives $f'(a_n)\equiv f'(a_0)$ modulo $\mathfrak m$. Taylor's formula at $a_n$, with $h_n=-f(a_n)/f'(a_n)$, yields

$$
f(a_{n+1})=f(a_n)+h_nf'(a_n)+h_n^2g_n=h_n^2g_n.
$$

Therefore $v(f(a_{n+1}))\geq2v(f(a_n))$, and $v(h_n)=v(f(a_n))$ tends to infinity. The sequence $(a_n)$ is Cauchy and converges to some $a\in A$. Continuity gives $f(a)=0$, and all corrections lie in $\mathfrak m$, so $a\equiv a_0$.

For uniqueness, let $a,b$ be roots congruent to $a_0$. Polynomial division gives

$$
f(a)-f(b)=(a-b)q(a,b),
$$

where $q(a,b)\equiv f'(a_0)\pmod{\mathfrak m}$. Thus $q(a,b)$ is a unit. Since the left side is zero and $A$ is a domain, $a=b$. $\square$

The proof gives more than existence: the Newton iterates converge quadratically in valuation. Once the error is divisible by $\pi^r$, the next is divisible by $\pi^{2r}$.

### 9.2 The valuation form

Sometimes the derivative is not a unit, yet the initial approximation is accurate enough to compensate.

**Theorem 9.2 (Newton form).** Let $K$ be complete for a rank-one nonarchimedean valuation $v$, let $A$ be its valuation ring, let $f\in A[X]$, and suppose $a_0\in A$ satisfies

$$
v(f(a_0))>2v(f'(a_0)).
$$

Then there is a unique root $a$ with

$$
v(a-a_0)>v(f'(a_0)).
$$

Moreover $v(a-a_0)=v(f(a_0))-v(f'(a_0))$.

**Proof roadmap.** We again use Newton correction, but must now track two quantities: the value of the derivative and the excess of the error beyond twice that value. Taylor expansion shows that the derivative value stays fixed while the excess at least doubles. This forces convergence. A divided-difference estimate then proves both the exact displacement and uniqueness in the stated ball.

**Proof.** Put

$$
s=v(f'(a_0)),\qquad r=v(f(a_0)),\qquad q_0=r-2s>0.
$$

If $f(a_0)=0$, take $a=a_0$; the asserted displacement has value $\infty$ and uniqueness follows from the divided-difference argument below. We therefore assume $f(a_0)\ne0$. The derivative is nonzero, and because $f\in A[X]$ and $a_0\in A$, we have $s\geq0$. Define $a_{n+1}=a_n+h_n$, where

$$
h_n=-\frac{f(a_n)}{f'(a_n)}.
$$

We prove inductively that

$$
v(f'(a_n))=s,
\qquad
q_n:=v(f(a_n))-2s\geq2^nq_0,
\qquad
v(h_n)=s+q_n.
$$

These statements hold at $n=0$. In particular $h_n\in A$ and $v(h_n)>s$. Taylor expansion, first for $f$ and then for $f'$, gives polynomials evaluated at integral arguments such that

$$
f(a_n+h_n)=f(a_n)+h_nf'(a_n)+h_n^2c_n=h_n^2c_n
$$

and

$$
f'(a_n+h_n)=f'(a_n)+h_nd_n,
$$

with $c_n,d_n\in A$. The second formula has one term of value $s$ and another of value at least $v(h_n)>s$, so unequal-value rigidity yields $v(f'(a_{n+1}))=s$. The first formula gives

$$
v(f(a_{n+1}))\geq2v(h_n)=2s+2q_n,
$$

hence $q_{n+1}\geq2q_n$. This proves the induction.

Because the value group is archimedean and $q_n\geq2^nq_0$ with $q_0>0$, the correction values $v(h_n)=s+q_n$ eventually exceed every fixed value. For $m>n$, the strong triangle inequality gives

$$
v(a_m-a_n)\geq\min_{n\leq j<m}v(h_j)=v(h_n),
$$

so $(a_n)$ is Cauchy. Let $a$ be its limit. Continuity gives $f(a)=0$. Since the first correction has value $r-s$ and every later correction has strictly larger value, Lemma 2.1 gives

$$
v(a-a_0)=v(h_0)=r-s>s.
$$

It remains to prove that no other root lies in this ball. For any $b$ with $v(b-a_0)>s$, polynomial division in two variables yields

$$
f(b)-f(a_0)=(b-a_0)D(b,a_0),
$$

where $D(b,a_0)-f'(a_0)$ is $(b-a_0)$ times an element of $A$; this follows term by term from

$$
\frac{b^m-a_0^m}{b-a_0}
=b^{m-1}+b^{m-2}a_0+\cdots+a_0^{m-1}.
$$

Hence $v(D(b,a_0))=s$. If $f(b)=0$, comparison with $v(f(a_0))=r$ forces $v(b-a_0)=r-s$. If $a$ and $b$ are both roots in the ball, the divided difference $D(a,b)$ differs from $f'(a_0)$ by a sum of terms divisible by $a-a_0$ or $b-a_0$. It therefore has value $s$, and

$$
0=f(a)-f(b)=(a-b)D(a,b)
$$

forces $a=b$. Thus $a$ is unique. $\square$

The strict inequality cannot simply be discarded. Approximate multiple roots may split into several roots or fail to lift. Hensel's lemma succeeds when the error is smaller than the square of the derivative in the valuation scale.

### 9.3 Lifting factorizations

Roots are linear factors, and the more structural version of Hensel's lemma lifts coprime factorizations.

**Theorem 9.3 (factorization form).** Let $A$ be a complete DVR and let $f\in A[X]$ be monic. Suppose

$$
\overline f=\overline g_0\,\overline h_0
$$

in $k[X]$, where $\overline g_0$ and $\overline h_0$ are monic and relatively prime. Then there are unique monic $g,h\in A[X]$ reducing to $\overline g_0,\overline h_0$, with the same degrees, such that $f=gh$.

**Proof roadmap.** Correct a factorization modulo $\pi^n$ to one modulo $\pi^{n+1}$. Coprimality solves the linear correction equation by Bézout. Compatible corrected coefficients converge in $A$, and uniqueness is proved by the same linear equation at the first precision where two lifts could differ.

**Proof.** Start with arbitrary monic lifts $g_1,h_1$, so $f-g_1h_1\in\pi A[X]$. Suppose monic $g_n,h_n$ give a factorization modulo $\pi^n$. Seek

$$
g_{n+1}=g_n+\pi^n r,\qquad h_{n+1}=h_n+\pi^n s,
$$

with $\deg r<\deg g_n$ and $\deg s<\deg h_n$. Modulo $\pi^{n+1}$ the required equation is

$$
\overline r\,\overline h_0+\overline s\,\overline g_0
=\overline{(f-g_nh_n)/\pi^n}.
$$

Because $\overline g_0$ and $\overline h_0$ are coprime, multiplication induces an isomorphism from the indicated bounded-degree pairs to polynomials of degree below $\deg f$; equivalently, use a Bézout identity and reduce remainders. Thus $r,s$ exist uniquely modulo $\pi$. Choose lifts and iterate. Each coefficient sequence is Cauchy, and its limit defines monic $g,h$ with $f=gh$. If two factorizations existed, reduce their difference at the first nonzero precision; the homogeneous form of the same coprime equation forces that difference to vanish. $\square$

An immediate consequence is that a monic polynomial whose reduction has a simple root has a unique corresponding root in $A$. Another is that pairwise coprime factors of $\overline f$ lift simultaneously. Thus factorization over the residue field predicts a substantial part of factorization over the complete field.

### 9.4 Henselian local rings

Completeness was used to make successive corrections converge, but the lifting property itself deserves a name. A local ring $(A,\mathfrak m)$ is **henselian** if every factorization of a monic polynomial modulo $\mathfrak m$ into coprime monic factors lifts uniquely to $A$. Taking one factor to be $X-\overline a$ shows immediately that every simple residue root lifts uniquely. We use the factorization formulation because it records all coprime factors at once.

**Theorem 9.4 (complete local rings are henselian).** Let $(A,\mathfrak m)$ be a commutative local ring that is complete and separated for its $\mathfrak m$-adic topology. Then $A$ is henselian.

**Proof roadmap.** Beginning with arbitrary monic lifts of the two residue factors, correct their product coefficient by coefficient. Coprimality makes the linear correction map invertible over $A$. A correction whose coefficients lie in $\mathfrak m^n$ leaves an error in $\mathfrak m^{2n}$, so completeness supplies limiting factors; separatedness proves that their product is exactly the original polynomial. The same quadratic estimate gives uniqueness.

**Proof.** Let $f\in A[X]$ be monic, and suppose

$$
\overline f=\overline g_0\,\overline h_0
$$

with $\overline g_0$ and $\overline h_0$ monic and coprime. Put $r=\deg \overline g_0$, $s=\deg \overline h_0$, and $d=r+s=\deg f$. Choose monic lifts $g_1,h_1\in A[X]$ of degrees $r,s$. Then every coefficient of

$$
E_1=f-g_1h_1
$$

lies in $\mathfrak m$.

Suppose more generally that $g,h$ are monic lifts of the same degrees and that every coefficient of $E=f-gh$ lies in $\mathfrak m^n$, where $n\geq1$. Consider the map between free $A$-modules

$$
\Phi_{g,h}:A[X]_{<r}\oplus A[X]_{<s}
\longrightarrow A[X]_{<d},
\qquad
(u,v)\longmapsto uh+vg,
$$

where $A[X]_{<a}$ denotes the polynomials of degree less than $a$. In the monomial bases its determinant is, up to sign, the resultant of $g$ and $h$. Its residue is the resultant of the coprime polynomials $\overline g_0,\overline h_0$, hence is nonzero. The determinant is therefore a unit of the local ring $A$, so $\Phi_{g,h}$ is an isomorphism.

There are consequently unique $u\in A[X]_{<r}$ and $v\in A[X]_{<s}$ satisfying

$$
uh+vg=E.
$$

The inverse matrix of $\Phi_{g,h}$ has entries in $A$. Since the coefficients of $E$ lie in $\mathfrak m^n$, the coefficients of $u$ and $v$ do as well. Set $g'=g+u$ and $h'=h+v$. These are again monic lifts of the prescribed degrees, and

$$
f-g'h'
=E-(uh+vg)-uv
=-uv.
$$

Every coefficient of the new error therefore lies in $\mathfrak m^{2n}$. Starting with $(g_1,h_1)$ and iterating this construction gives pairs $(g_j,h_j)$ for which

$$
f-g_jh_j\in\mathfrak m^{2^{j-1}}A[X],
\qquad
g_{j+1}-g_j,\ h_{j+1}-h_j
\in\mathfrak m^{2^{j-1}}A[X]
$$

coefficientwise. The degrees remain fixed, so only finitely many coefficient sequences occur. They are $\mathfrak m$-adically Cauchy and hence converge, by completeness, to monic polynomials $g,h$ of degrees $r,s$ with the required reductions. Multiplication involves only finite sums of coefficients, so $g_jh_j$ converges coefficientwise to $gh$. The errors lie in every prescribed power of $\mathfrak m$; separatedness therefore gives $f=gh$.

For uniqueness, suppose $(g^*,h^*)$ is another such lift and put $a=g^*-g$, $b=h^*-h$. Their coefficients lie in $\mathfrak m$, their degrees are less than $r,s$, and equality of the two products gives

$$
ah+bg=-ab.
$$

If the coefficients of $a,b$ lie in $\mathfrak m^n$, then the right side has coefficients in $\mathfrak m^{2n}$. Applying the integral inverse of $\Phi_{g,h}$ shows that the coefficients of $a,b$ lie in $\mathfrak m^{2n}$. Beginning with $n=1$ and iterating, they lie in every power of $\mathfrak m$; separatedness forces $a=b=0$. Thus the lift is unique. $\square$

Theorem 9.3 is the DVR instance of this argument. There is also a metric version needed for nondiscrete rank-one fields. Start with monic lifts $g,h$ of coprime residue factors of $f$. On pairs $(r,s)$ with $\deg r<\deg g$ and $\deg s<\deg h$, the linear map

$$
(r,s)\longmapsto rh+sg
$$

has determinant equal, up to sign, to the resultant of $g$ and $h$. Coprimality of the reductions says that this determinant is a unit, so the inverse linear map has integral coefficients. Solve the linear equation that cancels the current error $f-gh$, replace $(g,h)$ by $(g+r,h+s)$, and observe that the new error is the quadratic term $-rs$. If the old coefficient errors have value at least $\delta>0$, the new ones have value at least $2\delta$. Rank one makes $2^n\delta$ tend beyond every fixed value, and completeness of the finite coefficient space supplies limiting factors. The same invertible linear map proves uniqueness. Thus the valuation ring of every complete rank-one nonarchimedean field is henselian.

Henselianity is algebraic, concerned with finite equations; completeness is topological, concerned with all Cauchy sequences. The distinction matters: uniqueness of valuation extensions will use only henselianity, whereas infinite sums and inverse-limit constructions require completeness.

### 9.5 Worked lifts

The hypotheses of Hensel's lemma are easiest to remember through computations. Odd and even residue characteristic behave differently because the derivative may cease to be a unit, while Newton's stronger inequality explains the replacement modulus.

Let $p$ be odd and let $u\in\mathbf Z_p^\times$. If its residue $\overline u$ is a square in $\mathbf F_p^\times$, choose $a_0$ with $a_0^2\equiv u\pmod p$. For $f=X^2-u$, the derivative $2a_0$ is a unit, so $u$ has a unique square root congruent to $a_0$ modulo $p$. There are two roots overall, corresponding to the two residue roots. Thus a $p$-adic unit is a square exactly when its residue is a square, for odd $p$.

For a numerical lift, take $u=2$ in $\mathbf Z_7$. The residue $3$ is a root because $3^2\equiv2\pmod7$, and $f'(3)=6$ is a unit. Newton's first correction is

$$
a_1=3-\frac{7}{6}.
$$

Modulo $49$, the inverse of $6$ is $41$, so $a_1\equiv3-7\cdot41\equiv10\pmod{49}$. Indeed $10^2=100\equiv2\pmod{49}$. The next correction determines the root modulo $7^4$, not merely modulo $7^3$, because the error valuation doubles. This illustrates why Newton iteration is much faster than choosing one digit at a time.

At $p=2$ the derivative of $X^2-u$ is never a unit at a unit. The stronger Newton form shows that every $u\equiv1\pmod8$ is a square in $\mathbf Z_2$: taking $a_0=1$ gives $v_2(1-u)\geq3>2v_2(2)=2$. The modulus $8$, rather than $2$, records the derivative degeneracy.

For $u=17$, the stronger inequality is particularly visible: $v_2(f(1))=4$ and $v_2(f'(1))=1$. Newton's first iterate is $1-(-16)/2=9$, and $9^2-17=64$. The error value has risen from $4$ to $6$. The theorem also predicts $v_2(a-1)=4-1=3$ for the lifted root $a$, which agrees with the first correction $9-1=8$.

For $f=X^p-X-a$ over a complete DVR of residue characteristic $p$, one has $f' = pX^{p-1}-1$, always a unit. Every residue root lifts uniquely. This simple observation is often useful when separating unramified behavior from ramified behavior.

### 9.6 Algebraic consequences

Root lifting is not merely a numerical algorithm. Combined with integral closedness, it constrains irreducibility and, more profoundly, prevents valuations from branching in algebraic extensions.

Let $A$ be a DVR with fraction field $K$. If a monic $f\in A[X]$ has irreducible reduction, then $f$ is irreducible over $K$. Indeed, a factorization of a monic polynomial over $K$ into monic factors has coefficients integral over $A$: the roots of each factor are among the roots of $f$, hence integral, and the factor coefficients are elementary symmetric functions of them. Since a DVR is integrally closed, the factors lie in $A[X]$, and their reductions would factor $\overline f$. The converse fails because reduction can acquire repeated factors. More generally, the same argument works for any integrally closed local domain; henselianity becomes relevant when one asks to lift a factorization from the residue field.

More importantly, henselianity controls extensions of the valuation. For a finite field extension $L/K$, primes of the integral closure above $\mathfrak m$ correspond to extensions of the valuation. Over a henselian field there is exactly one such prime, hence exactly one extension. Completeness implies henselianity and therefore yields uniqueness. The next chapter proves this implication before using it, includes the hypotheses under which existence and finiteness hold, and quantifies what happens when there are several primes.

## 10. Valuations in algebraic extensions

### 10.1 The extension problem

Let $(K,v)$ be a valued field and $L/K$ an algebraic extension. We seek a valuation $w$ on $L$ whose restriction to $K$ is $v$, perhaps after identifying value groups. There are three distinct questions:

1. Does an extension exist?
2. How many inequivalent extensions are there?
3. For a finite extension, how are their value groups and residue fields related to $[L:K]$?

Existence is general. Uniqueness is not. For example, a prime of a number field can split into several primes in an extension, and each prime gives a different extension of the local valuation. Uniqueness becomes true when the base valuation is henselian, in particular when it is complete and nonarchimedean.

It is helpful to phrase the problem in rings. Let $V$ be the valuation ring of $v$ and let $B$ be its integral closure in $L$. An extension $w$ has valuation ring $W$, and $W$ contains $B$: every element integral over $V$ belongs to the integrally closed ring $W$. The maximal ideal of $W$ contracts to a prime $\mathfrak q$ of $B$ above $\mathfrak m_V$. Conversely, a suitable valuation ring dominating $B_{\mathfrak q}$ supplies an extension.

### 10.2 Existence by maximal domination

An explicit formula for an extended valuation is usually unavailable before the extension is understood. The robust existence proof instead enlarges the bounded subring as far as possible and lets maximality force total divisibility.

**Theorem 10.1 (extension theorem).** Every valuation $v$ on $K$ extends to a valuation on every algebraic extension $L/K$.

**Proof roadmap.** Work with valuation rings. Among local subrings of $L$ containing $V$ and whose maximal ideal contracts to $\mathfrak m_V$, choose a maximal one. Show that maximality forces the test “$x$ or $x^{-1}$” for every $x\in L^\times$; then the intrinsic criterion makes it a valuation ring.

**Proof.** Consider pairs $(R,\mathfrak p)$ where $V\subseteq R\subseteq L$, $\mathfrak p$ is a prime ideal of $R$, and $\mathfrak p\cap V=\mathfrak m_V$. Order them by domination: $(R,\mathfrak p)\leq(S,\mathfrak q)$ if $R\subseteq S$ and $\mathfrak q\cap R=\mathfrak p$. For a chain, take the union of the rings and the union of the primes. Membership in a chain is comparable, so the latter union is prime, and its contraction remains $\mathfrak m_V$. Thus every chain has an upper bound, and a maximal pair exists.

Localize $R$ at $\mathfrak p$. Its maximal ideal is $\mathfrak pR_{\mathfrak p}$ and its contraction to $V$ is still $\mathfrak m_V$: elements of $V\setminus\mathfrak m_V$ were already units. The localized pair dominates the original one, so maximality lets us replace $R$ by this localization. Hence $R$ is local with maximal ideal $\mathfrak p$.

Suppose some $x\in L^\times$ has neither $x$ nor $x^{-1}$ in $R$. We first explain why maximality forces both extended ideals $\mathfrak pR[x]$ and $\mathfrak pR[x^{-1}]$ to be the unit ideal. If, for example, $\mathfrak pR[x]$ were proper, choose a prime ideal $\mathfrak q$ containing it. Its contraction to $R$ contains $\mathfrak p$ and is proper, hence equals the maximal ideal $\mathfrak p$. Then $R[x]_{\mathfrak q}$ would be a local ring strictly dominating $R$, contrary to maximality. The inverse case is identical.

We therefore have relations

$$
1=a_0+a_1x+\cdots+a_nx^n,\qquad
1=b_0+b_1x^{-1}+\cdots+b_mx^{-m}
$$

with all coefficients in $\mathfrak p$. Choose the first relation of least possible degree $n$ and the second of least possible degree $m$. Since $1-a_0$ and $1-b_0$ are units of the local ring $R$, absorb them into the remaining coefficients. We may therefore assume $a_0=b_0=0$ while keeping all other coefficients in $\mathfrak p$:

$$
1=a_1x+\cdots+a_nx^n,
\qquad
1=b_1x^{-1}+\cdots+b_mx^{-m}.
$$

Multiplying the second equation by $x^m$ gives

$$
x^m=b_1x^{m-1}+\cdots+b_m.
$$

If $n\geq m$, use this monic relation to replace the highest power $x^n$ in the first equation by terms of lower degree. Every new coefficient remains in $\mathfrak p$, because it contains the factor $a_n\in\mathfrak p$. The result expresses $1$ as an element of $\mathfrak pR[x]$ with degree strictly below $n$, contradicting minimality. If $n<m$, interchange $x$ and $x^{-1}$ and use the first relation, after multiplication by $x^{-n}$, to shorten the second. Both possibilities are impossible.

Consequently no $x\in L^\times$ can have both $x$ and $x^{-1}$ outside $R$. The intrinsic criterion, Theorem 3.1, makes $R$ a valuation ring of $L$. Finally $R\cap K=V$: the inclusion $V\subseteq R\cap K$ holds, and if $y\in K\setminus V$, then $y^{-1}\in\mathfrak m_V\subseteq\mathfrak p$, so $y$ cannot also belong to the local ring $R$. Thus the resulting valuation restricts to $v$. $\square$

The proof works for arbitrary field extensions with the usual maximality argument; algebraicity becomes important for controlling residue and value extensions. Existence alone says nothing about uniqueness or discreteness.

### 10.3 Integral elements are bounded

Extension theory introduces two notions of having no pole: satisfying a monic equation over the base valuation ring, and having nonnegative value at every branch. Their equivalence is the organizing principle behind integral closure.

Let $L/K$ be algebraic and $w$ extend $v$. If $x\in L$ is integral over $V$, then $x$ lies in the valuation ring $W$ of $w$. This is exactly the earlier proof that valuation rings are integrally closed, now applied to a monic equation with coefficients in $V\subset W$. Thus

$$
B\subseteq\bigcap_w W,
$$

where $B$ is the integral closure and $w$ ranges over extensions.

The reverse inclusion also holds. Here is the contrapositive, including the point at which nonintegrality is used. Suppose $x\in L$ is not integral over $V$. In the ring $V[x^{-1}]$, the ideal

$$
I=\mathfrak m_VV[x^{-1}]+x^{-1}V[x^{-1}]
$$

is proper. Indeed, a relation $1\in I$, after collecting powers of $x^{-1}$, would have the form

$$
1=a_0+a_1x^{-1}+\cdots+a_nx^{-n},
\qquad a_0\in\mathfrak m_V,\quad a_i\in V.
$$

Multiplication by $x^n$ and division by the unit $1-a_0$ would give a monic equation for $x$ over $V$, contrary to the assumption. Choose a prime ideal containing $I$, localize, and apply the maximal-domination construction of Theorem 10.1. The resulting valuation ring contains $V$ and $x^{-1}$, with $x^{-1}$ in its maximal ideal; it therefore cannot contain $x$. Thus an element lying in every valuation ring above $V$ must be integral, and

$$
B=\bigcap_{w\mid v} W.
$$

This identity is the valuative criterion for integrality in this field-theoretic form. “Integral” means “bounded at every extension of the chosen place.” If there is a unique extension, the integral closure is itself its valuation ring, provided the extension is algebraic and the contraction is fixed.

For finite extensions of a discretely valued field, algebraic boundedness also admits a norm test in favorable situations. If $x$ is integral, its characteristic polynomial has coefficients in $A$, so its trace and norm lie in $A$. The converse from norm alone is false: cancellation among conjugate valuations can hide a pole. One must control all conjugates or all extended valuations.

We can now prove the part of the henselian uniqueness criterion needed later in this chapter. First we isolate the bridge between valuation extensions and integral closure.

**Extension-center lemma.** Let $E/K$ be algebraic and let $B$ be the integral closure of $A$ in $E$. Then

$$
W\longmapsto\mathfrak m_W\cap B
$$

is a bijection from valuation rings $W$ of $E$ extending $A$ to maximal ideals of $B$ above $\mathfrak m_A$; the inverse sends $\mathfrak P$ to $B_{\mathfrak P}$.

**Proof.** Every such $W$ contains $B$, because elements of $B$ are integral over $A\subset W$ and valuation rings are integrally closed. Its maximal ideal therefore has a center $\mathfrak P=\mathfrak m_W\cap B$ above $\mathfrak m_A$, and localization gives $B_{\mathfrak P}\subseteq W$.

Conversely, fix a maximal ideal $\mathfrak P$ of $B$ above $\mathfrak m_A$. The maximal-domination construction in the proof of Theorem 10.1, begun with the local domain $B_{\mathfrak P}$ in place of $A$, produces a valuation ring $W\subset E$ dominating $B_{\mathfrak P}$; write $w$ for its valuation. Its maximal ideal contracts to $\mathfrak m_A$ on $A$. Moreover $W\cap K=A$: if $c\in K\setminus A$, then $c^{-1}\in\mathfrak m_A\subset\mathfrak m_W$, so $c$ cannot also belong to $W$. Thus $W$ extends the original valuation.

We prove that $W=B_{\mathfrak P}$. Take $0\ne z\in W$. Choose a nonzero relation

$$
b_0+b_1z+\cdots+b_nz^n=0
$$

by starting with an equation over $K$ and dividing all its coefficients by one having least $v$-value. Then every $b_i$ lies in $A$ and at least one is a unit. Let $j$ be the largest index for which $b_j\in A^\times$. In fact $j\geq1$: if $j=0$, then in $W$ the constant term would have value zero and every other term positive value, which is impossible in a zero sum. Set

$$
y=b_j+b_{j+1}z+\cdots+b_nz^{n-j}.
$$

We claim that both $y$ and $zy$ lie in $B$. By the valuative criterion for integrality just proved, it is enough to check boundedness in every valuation ring $U$ of $E$ extending $A$. Write $u$ for its additive valuation. If $u(z)\geq0$, then every term of $y$ after $b_j$ has positive value, by the maximal choice of $j$, while $u(b_j)=0$. Hence $u(y)=0$ and $u(zy)\geq0$. If $u(z)<0$, divide the displayed relation by $z^j$ to obtain

$$
y=-\sum_{i<j}b_i z^{i-j}.
$$

Every term on the right has value at least $(j-i)(-u(z))\geq-u(z)$. Therefore

$$
u(y)\geq-u(z)>0,
\qquad
u(zy)\geq0.
$$

This proves $y,zy\in B$. For the particular ring $W$, we have $w(z)\geq0$, so the first case also shows that $y$ is a unit of $W$. Consequently $y\notin\mathfrak P$, and

$$
z=\frac{zy}{y}\in B_{\mathfrak P}.
$$

Thus $W\subseteq B_{\mathfrak P}$; the reverse inclusion was built into the construction, so equality holds. Applying the same conclusion to any valuation ring centered at $\mathfrak P$ proves uniqueness, while distinct centers plainly give distinct rings. $\square$

**Henselian uniqueness lemma.** If $A$ is henselian, then the valuation of $K$ has a unique extension, up to equivalence, to every algebraic extension of $K$. Equivalently, for every finite extension $E/K$, the integral closure of $A$ in $E$ is local.

**Proof.** First let $E/K$ be finite, with integral closure $B$. Suppose $B$ had distinct maximal ideals $\mathfrak P$ and $\mathfrak Q$. Choose $x\in\mathfrak P\setminus\mathfrak Q$. Its minimal polynomial $q\in K[X]$ lies in $A[X]$: the element $x$ is integral, the coefficients of $q$ are integral over $A$, and $A$ is integrally closed. Moreover

$$
A[x]\cong A[X]/(q).
$$

The contractions of $\mathfrak P$ and $\mathfrak Q$ give two distinct maximal ideals of $A[x]$, so the residue algebra

$$
A[x]/\mathfrak m_AA[x]\cong k[X]/(\overline q)
$$

is not local. Therefore $\overline q$ has at least two distinct monic irreducible factors. Grouping their powers gives a coprime factorization $\overline q=\overline g_0\overline h_0$ with both factors nonconstant. Henselianity lifts it to $q=gh$ in $A[X]$, contradicting irreducibility of $q$ over $K$. Thus $B$ is local.

The extension-center lemma now gives a unique extension on every finite field extension. Theorem 10.1 supplies existence on an arbitrary algebraic extension, and any two extensions agree because their restrictions agree on every finite subextension. $\square$

### 10.4 Ramification index and residue degree

Now let $v$ be discrete and normalized, and let $w$ be an extension to a finite field extension $L/K$. View $\Gamma_v$ inside $\Gamma_w$ through restriction. We will prove that the quotient $\Gamma_w/\Gamma_v$ is finite. Its order

$$
e(w/v)=[\Gamma_w:\Gamma_v]
$$

is the **ramification index**. Normalize $w$ so that $\Gamma_w=\mathbf Z$. Then the restriction satisfies

$$
w(x)=e(w/v)v(x)\qquad(x\in K^\times).
$$

Equivalently, if $\pi$ is a uniformizer of $K$ and $\Pi$ one for $L$, then

$$
\pi=u\Pi^e
$$

for a unit $u$ in the valuation ring of $w$.

The normalization used here is justified by finiteness of the index: an ordered abelian group containing a copy of $\mathbf Z$ with finite index is a finitely generated torsion-free group of rank one, hence is infinite cyclic. Its order chooses one of the two generators as positive.

The inclusion of valuation rings induces an injection of residue fields $k_v\hookrightarrow k_w$. We will likewise prove that its degree is finite. That degree

$$
f(w/v)=[k_w:k_v]
$$

is the **residue degree**. Both $e$ and $f$ are finite and satisfy

$$
e(w/v)f(w/v)\leq[L:K].
$$

**Proof.** Do not initially assume either index finite. Choose any finite list $x_1,\ldots,x_r\in L^\times$ whose values represent distinct cosets of $\Gamma_w/\Gamma_v$, and any units $y_1,\ldots,y_s$ whose residues are linearly independent over $k_v$. We claim the $rs$ products $x_i y_j$ are $K$-linearly independent. Suppose

$$
\sum_{i,j}a_{ij}x_iy_j=0.
$$

For each fixed $i$, choose a coefficient $a_{ij_i}$ for which $w(a_{ij}x_i)$ is least among the nonzero terms in that block. The block minima for different $i$ lie in distinct cosets modulo $\Gamma_v$ and are therefore distinct. Let the unique smallest block be indexed by $i_0$. Divide the relation by $a_{i_0j_0}x_{i_0}$, where $a_{i_0j_0}$ has minimal value in that block. Every term from another block now has positive value and vanishes on reduction. Terms in the chosen block whose coefficients have larger value vanish as well. The terms of value zero give a nontrivial $k_v$-linear relation among some $\overline y_j$; the coefficient of $\overline y_{j_0}$ is nonzero. This is impossible.

Thus $rs\leq[L:K]$ for every such pair of finite lists. Taking $s=1$ shows that there are at most $[L:K]$ value-group cosets, so $e$ is finite. Taking $r=1$ shows that every linearly independent residue-field family has at most $[L:K]$ members, so $f$ is finite. We may now take all coset representatives and a residue basis; the same argument yields $ef\leq[L:K]$. $\square$

This proof is fundamental: value-group directions and residue-field directions contribute independently to vector-space dimension.

### 10.5 Several extensions and the fundamental equality

For one extension $w$, Section 10.4 proved $ef\leq[L:K]$. If the valuation has several extensions, those separate contributions must be added. The clean ring-theoretic accounting requires the integral closure to be finite; this is precisely the hypothesis under which the local branches form a finite semilocal algebra rather than an uncontrolled normalization.

**Theorem 10.2 (fundamental equality under finite normalization).** Let $A$ be a DVR with fraction field $K$, let $L/K$ be finite, and suppose that the integral closure $B$ of $A$ in $L$ is finite over $A$. Then the extensions $w_1,\ldots,w_g$ of the normalized valuation of $A$ are finite in number and

$$
\sum_{i=1}^g e_i f_i=[L:K].
$$

No separability hypothesis on $L/K$ is required.

**Proof roadmap.** Finite torsion-free modules over a DVR are free. Normality and dimension one make the finite normalization a semilocal Dedekind domain. Its maximal ideals are the valuation branches. Factoring $\pi B$ records the $e_i$, and taking the length of $B/\pi B$ records both $e_i$ and $f_i$.

**Proof.** Because $B$ is finite and torsion-free over the PID $A$, it is free. Moreover

$$
B\otimes_AK=L:
$$

if $x\in L$, a sufficiently large power of a uniformizer clears the denominators in an algebraic equation and makes that multiple of $x$ integral. Hence the free rank of $B$ is $[L:K]$.

The finite integral extension $A\subset B$ is Noetherian, and $B$ is integrally closed by construction. Dimension is preserved under an integral extension, so every nonzero prime of $B$ is maximal. Since $B/\pi B$ is a finite-dimensional algebra over $k=A/\pi A$, it has only finitely many maximal ideals; call their inverse images $\mathfrak P_1,\ldots,\mathfrak P_g$. Each localization $B_{\mathfrak P_i}$ is a DVR. Its valuation extends that of $A$, and every extension occurs in this way: an extended valuation ring contains $B$, its maximal ideal selects one $\mathfrak P_i$, and the maximality principle of Section 3.5 identifies it with $B_{\mathfrak P_i}$. Thus the $\mathfrak P_i$ are exactly the branches.

If $e_i$ is the value of $\pi$ in the normalized valuation of $B_{\mathfrak P_i}$, unique ideal factorization gives

$$
\pi B=\prod_i\mathfrak P_i^{e_i}.
$$

The factors are pairwise comaximal. The Chinese remainder theorem and the filtration by powers of $\mathfrak P_i$ therefore give

$$
\dim_k(B/\pi B)
=\sum_i\dim_k(B/\mathfrak P_i^{e_i})
=\sum_i e_i[B/\mathfrak P_i:k]
=\sum_i e_if_i.
$$

On the other hand, reducing a free $A$-basis of $B$ modulo $\pi$ shows that the left side is $[L:K]$. This proves the equality. $\square$

Chapter 11 develops each step of this proof in detail and relates it to ideal factorization, norms, and traces. The finiteness assumption is real: not every DVR has finite normalization in every finite extension. It holds for complete DVRs, as Section 12.6 will prove directly, and in the standard arithmetic and geometric DVRs obtained by localizing rings with finite normalization. For a general valued field one still has the single-branch inequality of Section 10.4; the broader theory of defect requires additional valuation-theoretic machinery and is not used here.

### 10.6 Finite extensions of complete fields

Let $K$ be complete for a nontrivial nonarchimedean absolute value and let $L/K$ be finite. Two structures must be distinguished. First, $L$ is a finite-dimensional topological vector space over $K$. Second, its field multiplication should be measured by an absolute value. Completeness settles the first directly; henselianity settles the second.

Choose a basis $e_1,\ldots,e_n$ and put

$$
\left\|\sum_i a_ie_i\right\|_0=\max_i|a_i|_K.
$$

This norm makes $L$ complete because a sequence is Cauchy precisely when every coordinate sequence is Cauchy in $K$. Any $K$-linear endomorphism is bounded: if its matrix is $(c_{ij})$, then

$$
\|Tx\|_0\leq\left(\max_{i,j}|c_{ij}|_K\right)\|x\|_0.
$$

If $\|\cdot\|_1$ is the coordinate norm from another basis, the change-of-basis matrix and its inverse bound each norm by a constant times the other. Thus the topology and completeness do not depend on the basis. Multiplication is continuous because each map $y\mapsto xy$ is linear and the finitely many structure constants give a uniform bilinear bound.

We will use the stronger finite-dimensional norm lemma: **every** nonarchimedean $K$-norm $N$ on $L$ is equivalent to the coordinate norm when $K$ is complete. The upper comparison

$$
N\left(\sum_i a_ie_i\right)\leq
\left(\max_iN(e_i)\right)\max_i|a_i|_K
$$

is immediate. For the reverse comparison, argue by induction on the dimension. Let $W$ be the span of the first $n-1$ basis vectors. By induction $W$ is complete for $N$ and hence closed. Therefore

$$
\delta=\inf_{w\in W}N(e_n-w)>0;
$$

if the infimum were zero, approximants in $W$ would be Cauchy and would converge to $e_n\in W$, a contradiction. For $x=w+ae_n$ with $a\ne0$, the definition of $\delta$ gives $N(x)\geq|a|\delta$. Then $w=x-ae_n$, so the induction bound on $W$, together with the bound on $|a|$, controls every coordinate of $w$ by a constant times $N(x)$. This completes the induction and proves norm equivalence.

**Theorem 10.3 (unique extension over a complete field).** A nonarchimedean absolute value on a complete field $K$ has a unique extension to every algebraic extension $L$, with the requirement that it restrict exactly to the given absolute value. Every $K$-automorphism of $L$ preserves it. If $L/K$ is finite, then $L$ is complete for the extended absolute value and

$$
|x|_L=|N_{L/K}(x)|_K^{1/[L:K]}.
$$

**Proof roadmap.** Completeness gives Hensel factor lifting, and the henselian uniqueness lemma of Section 10.3 converts that lifting property into uniqueness of the algebraic extension of the valuation. After uniqueness is established, automorphisms preserve the value automatically. Norm transitivity separates the separable and purely inseparable cases and yields the formula. Finite-dimensional norm equivalence then identifies the valuation topology with the complete vector-space topology constructed above.

**Proof.** For the trivial absolute value, algebraicity forces the only extension to remain trivial. Indeed, in the monic minimal equation of a nonzero algebraic element, the nonzero base coefficients all have size $1$. If the element had size less than $1$, the constant term would be the unique largest term; if it had size greater than $1$, the leading term would be the unique largest term. Either case is impossible in a zero sum. In the nontrivial case, Section 9.4 proves that the valuation ring is henselian. The henselian uniqueness lemma of Section 10.3 therefore gives a unique extension ring in every algebraic field; existence also follows independently from Theorem 10.1.

We must still show that the real scale of the given absolute value extends uniquely, rather than only up to equivalence. Put

$$
v_K(a)=-\log|a|_K
$$

for $a\ne0$, and let $w:L^\times\to\Gamma$ be any additive valuation belonging to the unique extension class, with $\Gamma=w(L^\times)$ its attained value group. The quotient $\Gamma/w(K^\times)$ is torsion. Indeed, if $x\in L^\times$ satisfies a relation $\sum_i a_ix^i=0$ over $K$, the least value among the nonzero terms $a_ix^i$ occurs at least twice. Thus for some $i\ne j$,

$$
(i-j)w(x)=w(a_j)-w(a_i)\in w(K^\times).
$$

For $\gamma\in\Gamma$, choose $m\geq1$ and $a\in K^\times$ with $m\gamma=w(a)$, and define

$$
\lambda(\gamma)=\frac{v_K(a)}m.
$$

This is well defined. If also $n\gamma=w(b)$, then $w(a^n)=w(b^m)$; equivalence on $K$ gives $nv_K(a)=mv_K(b)$. The same calculation with common multiples proves additivity. It is order preserving because $\gamma>0$ implies $w(a)=m\gamma>0$, hence $v_K(a)>0$. Finally it is the unique additive map $\Gamma\to\mathbf R$ extending the prescribed values on $K^\times$, since the equation $m\gamma=w(a)$ forces its value at $\gamma$.

Consequently

$$
|x|_L=\exp\bigl(-\lambda(w(x))\bigr),
\qquad |0|_L=0,
$$

is a nonarchimedean absolute value restricting exactly to $|\cdot|_K$. The uniqueness of the extension ring and of $\lambda$ proves uniqueness with this normalization.

Now assume $L/K$ is finite. Let $M/K$ be a finite normal extension containing the normal closure of the maximal separable subextension of $L/K$. Uniqueness implies that every $K$-automorphism $\sigma$ of $M$ preserves the extended absolute value: $x\mapsto|\sigma x|_M$ is another extension of $|\cdot|_K$. If $L/K$ is separable, the norm is the product over its $K$-embeddings into $M$, so

$$
|N_{L/K}(x)|_K
=\prod_{\sigma:L\hookrightarrow M}|\sigma x|_M
=|x|_L^{[L:K]}.
$$

For a general finite extension, let $L_s$ be its maximal separable subextension. Then $L/L_s$ is purely inseparable. Norms in a finite purely inseparable extension satisfy

$$
N_{L/L_s}(x)=x^{[L:L_s]};
$$

this follows first for a simple extension from its polynomial $T^{p^r}-x^{p^r}$ and then in towers. Norm transitivity and the separable calculation over $L_s/K$ now give

$$
\begin{aligned}
|N_{L/K}(x)|_K
&=|N_{L_s/K}(N_{L/L_s}(x))|_K\\
&=|x|_L^{[L:L_s][L_s:K]}
=|x|_L^{[L:K]}.
\end{aligned}
$$

Thus in all cases

$$
|N_{L/K}(x)|_K=|x|_L^{[L:K]}.
$$

Taking the indicated root proves the norm formula without inventing embeddings in the inseparable part.

The extended absolute value is itself a nonarchimedean $K$-norm on the vector space $L$. The finite-dimensional norm lemma therefore makes it equivalent to $\|\cdot\|_0$. Since the latter is complete, so is $L$. For infinite algebraic $L$, uniqueness on finite subextensions gives compatible values and therefore one value on their union. $\square$

The displayed norm formula is a consequence of uniqueness, not a circular proof of it. Completeness is sufficient but not necessary: henselianity is the exact algebraic hypothesis. A henselian field can fail to contain limits of arbitrary Cauchy sequences, yet finite algebraic equations still see only one extension of its valuation.

### 10.7 Concrete finite extensions

Let $K=k((t))$. In $L=k((u))$ with $t=u^n$, the $u$-adic valuation restricts as

$$
v_u(x)=n v_t(x),
$$

so $e=n$ and $f=1$. The polynomial $X^n-t$ is Eisenstein in $k[[t]][X]$, hence irreducible, and $1,u,\ldots,u^{n-1}$ form a $K$-basis of $L$. Thus $[L:K]=n$ and the extension is totally ramified. It is separable exactly when $n$ is not divisible by $\operatorname{char}(k)$.

If $k'/k$ is finite, then $k'((t))/k((t))$ has $e=1$ and $f=[k':k]$. This is the equal-characteristic model of an unramified extension when $k'/k$ is separable; an inseparable residue extension is not called unramified under the convention of Section 12.7. Combining the constructions gives $k'((u))/k((t))$ with $t=u^e$ and degree $e[k':k]$, without a separability assumption.

For $\mathbf Q_p$, adjoining a root $\Pi$ of an Eisenstein polynomial

$$
X^n+a_{n-1}X^{n-1}+\cdots+a_0,
$$

where $p$ divides every $a_i$ for $i<n$ and $p^2$ does not divide $a_0$, produces a totally ramified extension of degree $n$. To see the normalization without circularity, first use the extension of $v_p$ that restricts exactly to $v_p$ on $\mathbf Q_p$. The root is integral and reduces to $0$, so its value $\gamma$ is positive. The constant term has value $1$, every intermediate term has value greater than $1$, and the leading term has value $n\gamma$. Since the least value in a zero sum occurs at least twice, $n\gamma=1$. Thus $0,\gamma,\ldots,(n-1)\gamma$ represent $n$ distinct value-group cosets modulo $\mathbf Z$. Eisenstein irreducibility gives degree $n$, and the single-branch inequality now forces $e=n$ and $f=1$. After normalizing upstairs, $\Pi$ has value $1$ and $p$ has value $n$.

By contrast, if a monic polynomial over $\mathbf Z_p$ has irreducible separable reduction of degree $f$, the polynomial itself is irreducible by Section 9.6. Adjoining a root gives degree $f$, while the root residue already generates an extension of residue degree $f$. The inequality $ef\leq[L:K]$ therefore forces $e=1$. These two constructions isolate the two factors in the degree formula without yet entering the finer theory of ramification.

## 11. Integral closure and factorization

### 11.1 From one local ring to several

Passing to a field extension can turn one local direction into several. Integral closure retains all branches simultaneously; its maximal ideals label them, and localization will later isolate them.

Let $A$ be a DVR with fraction field $K$, let $L/K$ be finite, and let $B$ be the integral closure of $A$ in $L$. Even though $A$ is local, $B$ need not be. Distinct extensions of the valuation appear as distinct maximal ideals of $B$ above $\mathfrak m_A$. Localizing $B$ at each such ideal separates the branches.

This is the local version of prime factorization in number fields. If $A=R_{\mathfrak p}$ for a Dedekind domain $R$ and $S$ is the integral closure of $R$ in $L$, then

$$
B=S\otimes_R A=S_{R\setminus\mathfrak p}.
$$

All nonzero primes of $S$ not above $\mathfrak p$ disappear. The remaining maximal ideals encode exactly the ways of extending the $\mathfrak p$-adic valuation.

### 11.2 Finiteness hypotheses

To get a finite algebra rather than an uncontrolled integral closure, we need exact hypotheses. There are two principal sufficient ones here.

- If $L/K$ is finite separable, then $B$ is finite over any DVR $A$. The trace-dual argument in Section 11.8 proves this: separability makes the trace pairing nondegenerate and traps $B$ inside the dual of a full $A$-lattice.

- If $A$ is a complete DVR, then $B$ is finite for every finite extension, including inseparable ones. Section 12.6 proves this by comparing the extended unit ball with a coordinate lattice.

More generally, a domain whose normalization is finite in every finite extension of its fraction field is called Japanese; rings of integers of number fields and polynomial rings in one variable over a field have the required finiteness. Finiteness is not automatic for an arbitrary DVR in a finite inseparable extension. Any theorem using module rank or finite length must therefore state an appropriate hypothesis. In this chapter we assume explicitly that $B$ is finite over $A$, except when separability or completeness supplies it.

Because $B$ is finite and torsion-free over the PID $A$, it is free. Its rank is

$$
\operatorname{rank}_A B=[L:K].
$$

Indeed, tensoring with $K$ gives $B\otimes_AK=L$: every $x\in L$ becomes integral after multiplication by a sufficiently high power of $\pi$, since the coefficients of an algebraic equation can be cleared and rescaled to make it monic.

### 11.3 Semilocal Dedekind structure

With finiteness in hand, normality and dimension force a remarkably rigid ring. The next theorem explains why its localizations are exactly the extended valuation rings and why only finitely many branches occur.

**Theorem 11.1 (finite normalization over a DVR).** Under the finiteness assumption above, $B$ is a semilocal Dedekind domain. Its maximal ideals $\mathfrak P_1,\ldots,\mathfrak P_g$ are precisely the primes above $\mathfrak m_A$, and each localization $B_{\mathfrak P_i}$ is a DVR whose valuation extends that of $A$. Every extension arises uniquely this way.

**Proof roadmap.** Integral closure gives normality, module finiteness gives Noetherianity, and integrality preserves dimension one. Semilocality follows because $B/\pi B$ is a finite-dimensional algebra over the residue field. Localizing at each nonzero prime invokes the DVR characterization. Finally, valuation rings above $A$ contract to primes of $B$ and maximality identifies them with these localizations.

**Proof.** The ring $B$ is Noetherian because it is finite over the Noetherian ring $A$, and it is integrally closed by definition. Every nonzero prime $\mathfrak P$ contracts to the nonzero prime $\mathfrak m_A$. Indeed, choose $0\ne x\in\mathfrak P$. The minimal polynomial of the integral element $x$ over $K$ is monic with coefficients in $A$: its coefficients are integral over $A$ and lie in $K$, while $A$ is integrally closed. Its nonzero constant term belongs to $\mathfrak P\cap A$. Finally, primes in an integral extension lying over the same prime are incomparable, so no nonzero prime of $B$ can lie properly below another. Hence $B$ has dimension one and is Dedekind.

All maximal ideals contain $\pi$, and maximal ideals of $B$ correspond to those of the finite-dimensional $k$-algebra $B/\pi B$, so there are finitely many. Each $B_{\mathfrak P_i}$ is a one-dimensional Noetherian local integrally closed domain, hence a DVR. Its intersection with $K$ is $A$. For if $x\in K\setminus A$, then $x^{-1}\in\mathfrak m_A\subseteq\mathfrak P_iB_{\mathfrak P_i}$; were $x$ also in $B_{\mathfrak P_i}$, the element $x^{-1}$ would be both a unit and a member of the maximal ideal. Thus the normalized valuation of $B_{\mathfrak P_i}$ extends the valuation of $A$, up to the expected positive scaling.

Conversely, let $W$ be a valuation ring of $L$ extending $A$. Since $W$ is integrally closed it contains $B$. Its maximal ideal contracts to some $\mathfrak P_i$. Hence $B_{\mathfrak P_i}\subseteq W$, and both are valuation rings with the same domination. The maximality principle of Chapter 3 forces equality. Distinct primes give distinct contractions, hence inequivalent extensions. $\square$

The word semilocal is essential. If $\mathfrak p$ splits, $B$ has several maximal ideals and cannot itself be a valuation ring: an element positive at one branch and negative at another defeats total divisibility.

### 11.4 Factorization of the maximal ideal

The numerical invariants $e_i$ and $f_i$ become most meaningful when read directly from the extended ideal. Factorization records ramification exponents, while module length records residue-field multiplicity and recovers the degree formula.

Let $e_i=e(\mathfrak P_i/\mathfrak m)$ and $f_i=[B/\mathfrak P_i:A/\mathfrak m]$. In the DVR $B_{\mathfrak P_i}$,

$$
\pi B_{\mathfrak P_i}=\mathfrak P_i^{e_i}B_{\mathfrak P_i}.
$$

Unique ideal factorization in the Dedekind domain $B$ therefore yields

$$
\mathfrak m_AB=\pi B=\prod_{i=1}^g\mathfrak P_i^{e_i}.
$$

The factors are pairwise comaximal, so the Chinese remainder theorem gives

$$
B/\pi B\cong\prod_{i=1}^g B/\mathfrak P_i^{e_i}.
$$

The $i$th factor has a filtration with $e_i$ layers. Each layer $\mathfrak P_i^j/\mathfrak P_i^{j+1}$ is one-dimensional over $B/\mathfrak P_i$ and therefore has dimension $f_i$ over $k$. Consequently

$$
\dim_k(B/\pi B)=\sum_{i=1}^g e_i f_i.
$$

But $B$ is free of rank $[L:K]$, so $B/\pi B$ has $k$-dimension $[L:K]$. We obtain the fundamental equality

$$
\boxed{\sum_{i=1}^g e_i f_i=[L:K].}
$$

This proof also reveals exactly where equality comes from: finite freeness of the integral closure. Without finiteness this length computation is unavailable, which is why Theorem 10.2 was stated with that hypothesis.

### 11.5 Splitting patterns

For a quadratic extension under the finite-normalization hypotheses, there are three basic patterns. The prime may split: $g=2$, with $e_1=e_2=f_1=f_2=1$. It may remain inert: $g=1,e=1,f=2$. Or it may ramify: $g=1,e=2,f=1$. These names describe the allocation of degree between number of branches, residue extension, and value-group extension.

Consider $L=\mathbf Q(i)$ over $K=\mathbf Q$ at an odd prime $p$. The factorization of $X^2+1$ modulo $p$ predicts the behavior. If it has two distinct roots, Hensel lifting at the completion gives two embeddings into $\mathbf Q_p$ and the prime splits. If it is irreducible, the residue degree is two. At $p=2$ the reduction has a repeated root and ramification occurs. This example illustrates the role of separability modulo the prime without requiring detailed quadratic reciprocity.

For $k(t)\subset k(u)$ with $t=u^n$, the prime $(t)$ has one prime $(u)$ above it, with $e=n$ and $f=1$. For $k(t)\subset k'(t)$, it has one prime with $e=1$ and $f=[k':k]$. If a polynomial defining $L$ reduces to a product of distinct irreducibles of degrees $f_1,\ldots,f_g$ and its discriminant is a unit, then the corresponding prime is unramified and splits with those residue degrees.

The quadratic Gaussian example makes all three patterns explicit. In $\mathbf Z[i]$ one has

$$
5=(2+i)(2-i).
$$

The two factors generate distinct prime ideals, each residue field is $\mathbf F_5$, and neither factor is repeated. Thus above $(5)$ there are two primes with $(e,f)=(1,1)$. At $3$, the polynomial $X^2+1$ remains irreducible modulo $3$, so $(3)$ remains prime and its residue field is $\mathbf F_9$; here $(g,e,f)=(1,1,2)$. Finally

$$
2=-i(1+i)^2,
$$

so there is one prime above $2$, generated by $1+i$, with $(e,f)=(2,1)$. In each case the sum of the products $e_if_i$ is $2=[\mathbf Q(i):\mathbf Q]$.

The corresponding completed tensor products display the same calculation as field algebra:

$$
\mathbf Q(i)\otimes_{\mathbf Q}\mathbf Q_5
\cong\mathbf Q_5\times\mathbf Q_5,
$$

$$
\mathbf Q(i)\otimes_{\mathbf Q}\mathbf Q_3
\cong\mathbf Q_3(i),
$$

and

$$
\mathbf Q(i)\otimes_{\mathbf Q}\mathbf Q_2
\cong\mathbf Q_2(i).
$$

The first algebra has two field factors because there are two primes. The second and third are each fields, but for different reasons: the $3$-adic extension spends its degree on the residue field, while the $2$-adic extension spends it on the value group.

An equal-characteristic cover shows that the pattern is geometric rather than specifically arithmetic. Assume $\operatorname{char}(k)\ne2$ and consider

$$
K=k(t),\qquad L=K(u),\qquad u^2=t.
$$

At the point $t=0$, the element $u$ is a uniformizer and $t=u^2$, so $e=2,f=1$. At $t=1$, put $s=t-1$. Modulo $s$ the equation becomes $u^2=1$, with two simple roots $1$ and $-1$. Hensel lifting in $k((s))$ produces two roots, and

$$
L\otimes_Kk((s))\cong k((s))\times k((s)).
$$

If $c\in k^\times$ is a nonsquare and we complete at $t=c$, the reduction $U^2-c$ is irreducible. There is one unramified quadratic factor, with residue field $k(\sqrt c)$. The ramified, split, and inert outcomes thus occur at different points of the same quadratic function-field extension.

In mixed characteristic, $X^2+X+1$ is irreducible and separable modulo $2$. Adjoining a root to $\mathbf Q_2$ gives an unramified quadratic extension: $e=1,f=2$. Adjoining a root of $X^2-2$ gives a totally ramified quadratic extension: the polynomial is Eisenstein, the root is a uniformizer, and $e=2,f=1$. These concrete computations explain why the residue polynomial must be inspected together with the valuation of its discriminant or constant term.

The examples also expose a common trap. A factorization of one chosen defining polynomial modulo $\mathfrak p$ computes prime factorization directly only when the order generated by its root is already sufficiently close to the integral closure, for instance when the polynomial discriminant is a unit at $\mathfrak p$. Repeated residue factors can reflect genuine ramification, but they can also reflect a poor generator. The intrinsic objects are the primes of the integral closure and their localized DVRs.

### 11.6 Localization and residues

Once a global prime has separated into branches, calculations should be performed in one branch at a time. Localization discards all the other maximal ideals while preserving the chosen residue field. This section records that passage carefully, because it is where global prime notation becomes a normalized local valuation.

The residue field at $\mathfrak P_i$ may be computed before or after localization:

$$
B_{\mathfrak P_i}/\mathfrak P_iB_{\mathfrak P_i}\cong\operatorname{Frac}(B/\mathfrak P_i)=B/\mathfrak P_i,
$$

because $\mathfrak P_i$ is maximal. The equality of the last two expressions uses that the quotient is already a field.

The normalized valuation $w_i$ satisfies

$$
w_i(x)=\operatorname{length}_{B_{\mathfrak P_i}}
\bigl(B_{\mathfrak P_i}/xB_{\mathfrak P_i}\bigr)
$$

for nonzero integral $x$. Applied to $x=\pi$, this length is $e_i$. Viewing the same quotient as an $A$-module multiplies by the residue degree, giving $e_if_i$. This length conversion is often the cleanest way to prevent normalization errors.

### 11.7 Norms and ideals

The valuation of an element depends on a chosen branch, whereas the field norm returns to the base field and therefore combines all branches. The resulting formula is a useful consistency check: residue degrees supply the weights, and ramification is already contained in the normalized values upstairs.

For $0\ne x\in L$, the determinant of multiplication by $x$ is the field norm $N_{L/K}(x)$. Valuations of norms aggregate local valuations:

$$
v\bigl(N_{L/K}(x)\bigr)
=\sum_{i=1}^g f_i w_i(x)
$$

when each $w_i$ is normalized to value group $\mathbf Z$. To see the coefficient, first take $x$ integral and interpret both sides as lengths. Multiplication by $x$ on the free $A$-lattice $B$ has determinant of valuation equal to the $A$-length of $B/xB$. Chinese remainder localization splits this length into local contributions; one unit of $B_{\mathfrak P_i}$-length contributes $f_i$ units of $A$-length. Fractions follow by division.

Notice that $e_i$ does not appear explicitly in this formula because it is already built into $w_i(\pi)=e_i$. Setting $x=\pi$ gives

$$
v(N_{L/K}(\pi))=[L:K]
=\sum_i f_i e_i,
$$

as it must, since multiplication by $\pi\in K$ acts as scalar multiplication on an $[L:K]$-dimensional vector space.

### 11.8 Trace and boundedness

Norm is only one coefficient of the characteristic polynomial of multiplication. Trace and the remaining coefficients give a broader boundedness principle, linking integrality of elements to integrality of their conjugate-symmetric data.

If $x\in B$, multiplication by $x$ preserves the finite $A$-module $B$, so its characteristic polynomial lies in $A[T]$. In particular

$$
\operatorname{Tr}_{L/K}(x),\ N_{L/K}(x)\in A.
$$

There is a second proof of the integrality of trace and norm that does not presuppose that $B$ is finite. In a normal field containing all conjugates of $x$, every conjugate is integral over $A$. The coefficients of the characteristic polynomial are symmetric polynomials in these conjugates, with the appropriate inseparable multiplicities, so they are integral over $A$. They also lie in $K$; since the DVR $A$ is integrally closed in $K$, they belong to $A$. This observation is what allows the trace pairing itself to prove finiteness in the separable case, rather than assuming the desired conclusion.

When $L/K$ is separable, the trace pairing is nondegenerate over $K$. Since $\operatorname{Tr}_{L/K}(xy)\in A$ for $x,y\in B$, it gives an injection

$$
B\longrightarrow\operatorname{Hom}_A(B,A),
\qquad x\longmapsto\bigl(y\mapsto\operatorname{Tr}_{L/K}(xy)\bigr).
$$

Choose a $K$-basis of $L$ and multiply its elements by a common denominator so that the resulting full $A$-lattice $M$ lies inside $B$. For $x\in B$ and $m\in M$, the product $xm$ is integral, so the preceding conjugate argument gives $\operatorname{Tr}_{L/K}(xm)\in A$. Nondegeneracy identifies $L$ with its $K$-dual, and this trace condition places $B$ inside the dual lattice

$$
M^\vee=\{z\in L:\operatorname{Tr}_{L/K}(zM)\subseteq A\}.
$$

The dual lattice is finite free over $A$. Thus $M\subseteq B\subseteq M^\vee$, and Noetherianity makes $B$ finite over $A$. This proves the separable finiteness claim used in Section 11.2 without circularity. The same pairing later leads to the different, but the boundedness principle needed here is already clear: integral elements have integral symmetric functions of their conjugates.

The converse “integral trace and norm imply integral” holds for quadratic elements because their monic characteristic polynomial is $T^2-\operatorname{Tr}(x)T+N(x)$. In higher degree, trace and norm alone omit the intermediate coefficients and do not suffice.

### 11.9 Towers

Extensions are rarely studied in one step. To use intermediate fields without renormalizing incorrectly, we need to know that value-group indices and residue degrees multiply along a chosen chain of primes.

Let $K\subset L\subset M$ and choose compatible extensions of discrete valuations. Then

$$
e(M/K)=e(M/L)e(L/K),
\qquad
f(M/K)=f(M/L)f(L/K).
$$

The first is multiplicativity of indices of value groups; the second is the tower law for residue-field degrees. In a nonhenselian setting one must specify a chain of primes, since several choices can lie over the same lower prime. Under finite normalization, summing the fundamental equality through the tree of primes recovers $[M:K]=[M:L][L:K]$.

These simple multiplicative laws are the foundation for ramification in towers. The more delicate distinction between tame and wild behavior belongs later; here the essential data are already usable: how much the value scale stretches, how much the residue field grows, and how many local branches appear.

## 12. Completion and finite extensions

### 12.1 Separating branches by completion

Return to a DVR $A$, a finite extension $L/K$, and a finite integral closure $B$ with maximal ideals $\mathfrak P_1,\ldots,\mathfrak P_g$. The semilocal ring $B$ stores all extensions of the valuation at once. Completion separates them into complete local factors.

Let $\widehat A$ be the $\mathfrak m$-adic completion, and let $\widehat{B_i}$ denote the $\mathfrak P_i$-adic completion of $B_{\mathfrak P_i}$. The expected decomposition is

$$
B\otimes_A\widehat A\cong\prod_{i=1}^g\widehat{B_i}.
$$

This formula is not merely a formal convenience. Its fraction fields are the completions of $L$ at the distinct extended valuations, so tensoring a global extension with a local completion produces one field for each local branch.

### 12.2 The completed product theorem

The preceding picture should be an isomorphism, not only a metaphor. Proving it at finite precision reveals why Chinese remainders separate branches and why completion commutes with a finite normalization.

**Theorem 12.1 (completed product decomposition).** With the finiteness hypotheses of Chapter 11, there is a canonical isomorphism of $\widehat A$-algebras

$$
B\otimes_A\widehat A
\xrightarrow{\sim}
\prod_{i=1}^g\widehat{B_{\mathfrak P_i}}.
$$

Each factor is a complete DVR finite free over $\widehat A$, with ramification index $e_i$ and residue degree $f_i$. After inverting $\pi$,

$$
L\otimes_K\widehat K
\cong
\prod_{i=1}^g L_i,
$$

where $L_i=\operatorname{Frac}(\widehat{B_{\mathfrak P_i}})$ is the completion of $L$ for $w_i$.

**Proof roadmap.** Reduce at every finite precision. Powers of distinct maximal ideals become comaximal, so the Chinese remainder theorem splits $B/\pi^nB$. The $\pi$-adic and $\mathfrak P_i$-adic filtrations are cofinal locally because $\pi$ has $w_i$-value $e_i$. Passing to inverse limits gives the product. Finite freeness allows completion to commute with tensor product.

**Proof.** Ideal factorization gives

$$
\pi^nB=\prod_i\mathfrak P_i^{ne_i},
$$

and the factors are pairwise comaximal. Hence

$$
B/\pi^nB\cong\prod_i B/\mathfrak P_i^{ne_i}.
$$

Localizing the $i$th quotient at $\mathfrak P_i$ changes nothing, since every element outside $\mathfrak P_i$ is already invertible modulo its power. Thus it is $B_{\mathfrak P_i}/\mathfrak P_i^{ne_i}B_{\mathfrak P_i}$. The subsequence of exponents $ne_i$ is cofinal among all positive exponents, so its inverse limit is the $\mathfrak P_i$-adic completion. Taking inverse limits and commuting a finite product with the limit gives

$$
\varprojlim_n B/\pi^nB\cong\prod_i\widehat{B_{\mathfrak P_i}}.
$$

Since $B$ is finite free over $A$, choosing a basis shows directly that its $\pi$-adic completion is $B\otimes_A\widehat A$. This proves the first statement. Each localized completion is a complete DVR by Theorem 7.2, with unchanged finite quotients and therefore unchanged residue field and value of $\pi$; its $e_i,f_i$ are preserved. Inverting $\pi$ commutes with finite products and identifies the left side with $L\otimes_K\widehat K$, proving the field decomposition. $\square$

If $K$ is already complete, then $\widehat K=K$. A finite field extension $L$ makes $L\otimes_KK=L$ a field, so the product on the right can have only one factor. This recovers uniqueness of the extended valuation. It also shows, under the finite-normalization hypotheses, that

$$
e(L/K)f(L/K)=[L:K].
$$

### 12.3 Completion of a localization

The product theorem becomes most useful when a global Dedekind domain is localized at one prime. It then translates a finite global extension into the family of complete local fields lying above that prime.

Suppose $R$ is Dedekind, $K=\operatorname{Frac}(R)$, and $\mathfrak p$ is nonzero. Completing $R_{\mathfrak p}$ gives a complete DVR $\widehat{R_{\mathfrak p}}$. If $S$ is the finite integral closure of $R$ in a finite separable extension $L$, then

$$
S\otimes_R\widehat{R_{\mathfrak p}}
\cong
\prod_{\mathfrak P\mid\mathfrak p}\widehat{S_{\mathfrak P}}.
$$

At fraction-field level,

$$
L\otimes_K K_{\mathfrak p}
\cong
\prod_{\mathfrak P\mid\mathfrak p}L_{\mathfrak P}.
$$

This is the exact local-global dictionary needed later. A prime $\mathfrak p$ of the base does not select a unique field upstairs until a prime $\mathfrak P$ above it is chosen. Tensoring with the completion remembers all choices by returning their product.

### 12.4 An example of splitting after completion

A primitive element turns the abstract tensor product into polynomial factorization. This makes branching computable: irreducible completed factors are the local fields, and their idempotents are projectors onto the branches. Throughout this section we retain the finite-normalization hypotheses of Theorem 12.1.

Let $L=K(\alpha)$ with minimal polynomial $f\in K[X]$, and suppose $f$ is integral at a DVR $A$. Then

$$
L\otimes_K\widehat K\cong\widehat K[X]/(f)
$$

when $L=K[X]/(f)$. If $f$ factors over $\widehat K$ as a product of distinct irreducibles $f_1\cdots f_g$, the Chinese remainder theorem gives

$$
\widehat K[X]/(f)\cong\prod_{i=1}^g\widehat K[X]/(f_i).
$$

Each factor is a completion $L_i$. Hensel's lemma often reads the factorization from $\overline f$: coprime residue factors lift uniquely. Thus the algebraic factorization of $f$ in a completed field, the prime factorization in the integral closure, and the extensions of the valuation are three views of one event.

The product decomposition has concrete projectors. If $f=(X-a)(X-b)$ in $\widehat K[X]$ with $a-b$ a unit, then in $\widehat K[X]/(f)$ the elements

$$
e_a=\frac{X-b}{a-b},\qquad e_b=\frac{X-a}{b-a}
$$

satisfy $e_a^2=e_a$, $e_b^2=e_b$, $e_ae_b=0$, and $e_a+e_b=1$. They project onto the factors corresponding to the roots $a$ and $b$. Before completion these idempotents may not exist because the two roots need not lie in $K$; after completion they encode the two primes above the chosen base prime.

At finite precision, the same separation appears in the Chinese remainder isomorphism

$$
B/\pi^nB
\cong
\prod_i B/\mathfrak P_i^{ne_i}.
$$

The factor indexed by $i$ remembers the $i$th branch to precision $ne_i$ in its own uniformizer. Compatibility as $n$ grows turns these finite projectors into the idempotents of $B\otimes_A\widehat A$. Thus the completed tensor product is not an abstract afterthought: it is the ring of all compatible, simultaneous local approximations, sorted by branch.

One can now trace a single branch through all languages:

$$
\mathfrak P_i
\longleftrightarrow
B_{\mathfrak P_i}
\longleftrightarrow
w_i
\longleftrightarrow
\widehat{B_{\mathfrak P_i}}
\longleftrightarrow
L_i.
$$

The prime is the algebraic center, the localization is its DVR, $w_i$ is its numerical order, the completed ring supplies all compatible digits, and $L_i$ is the resulting complete local field. The ramification and residue degrees are unchanged at every arrow.

Repeated factors require care. They signal possible ramification but do not determine it alone, since the chosen polynomial may define a nonmaximal order. Passing to the integral closure is what makes $e_i$ and $f_i$ intrinsic.

### 12.5 Unique extension and henselianity

We can now collect the exact uniqueness statements.

**Theorem 12.2 (henselian uniqueness criterion).** For a valued field $(K,v)$ with valuation ring $A$, the following are equivalent.

1. $A$ is henselian.
2. The valuation $v$ has a unique extension, up to equivalence, to every algebraic extension of $K$.
3. The valuation has a unique extension, up to equivalence, to a fixed algebraic closure of $K$.
4. For every finite field extension $E/K$, the integral closure of $A$ in $E$ is a local ring.

For a complete nonarchimedean valued field these conditions hold.

**Proof roadmap.** Section 10.3 already proved that henselianity makes every finite integral closure local and every algebraic valuation extension unique. For the converse, locality sorts the irreducible factors of a monic polynomial uniquely according to coprime factors of its reduction.

**Proof.** The extension-center lemma of Section 10.3 shows that condition 4 is equivalent to uniqueness on every finite extension. Uniqueness on all finite subextensions is the same as uniqueness on every algebraic extension, so conditions 2 and 4 are equivalent. The henselian uniqueness lemma of that section proves $1\Rightarrow2$ (and directly $1\Rightarrow4$).

Condition 2 implies 3 by taking a fixed algebraic closure. Conversely, if two extensions existed on a finite field $E$, Theorem 10.1 would extend both to the fixed algebraic closure, where their restrictions to $E$ would remain distinct. Hence 3 implies 2.

It remains to recover henselianity from 4. Let $f\in A[X]$ be monic and suppose

$$
\overline f=\overline g_0\,\overline h_0
$$

with the residue factors monic and coprime. Factor $f$ over $K$ as a product of monic irreducibles, repeated according to multiplicity:

$$
f=q_1\cdots q_r.
$$

Each $q_j$ belongs to $A[X]$. One way to see this is to pass to a splitting field: its coefficients are symmetric functions of integral roots of $f$, so they are integral over $A$; because they lie in $K$ and $A$ is integrally closed, they lie in $A$.

Put $E_j=K[X]/(q_j)$ and let $B_j$ be the integral closure of $A$ in $E_j$. By 4, $B_j$ is local. The integral subring $A[X]/(q_j)\subseteq B_j$ is then local as well: every maximal ideal downstairs has a maximal ideal above it, and the latter is unique. Its residue algebra is

$$
k[X]/(\overline q_j),
$$

so this quotient is local. A quotient $k[X]/(r)$ is local exactly when $r$ is a power of one monic irreducible polynomial. Hence every $\overline q_j$ is a power of a single irreducible. Since $\overline g_0$ and $\overline h_0$ are coprime, each $q_j$ belongs unambiguously to the group whose reduction divides $\overline g_0$ or to the group whose reduction divides $\overline h_0$. Multiplying the factors in the two groups produces monic $g,h\in A[X]$ with

$$
f=gh,\qquad \overline g=\overline g_0,\qquad
\overline h=\overline h_0.
$$

The assignment of every irreducible factor is forced by coprimality, so the lift is unique. Thus 4 implies 1.

We have proved the equivalence. Section 9.4 proved directly, by coefficient correction, that the valuation ring of a complete nonarchimedean field is henselian. $\square$

The equivalence packages a single phenomenon in three languages. A coprime residue factorization is a decomposition visible to polynomial algebra. Locality of the integral closure says that no algebraic branch has split. Uniqueness says the same thing in the language of valuations. Henselianity makes these descriptions agree without passing to the completion.

Completeness implies condition 1 by Chapter 9. The theorem itself separates the roles of the hypotheses: arguments that require only uniqueness of extension should assume henselianity, while arguments involving infinite sums, limits, or compactness genuinely need completeness.

### 12.6 The valuation ring in a finite complete extension

Uniqueness tells us which valuation to use, but arithmetic also needs its bounded ring to be finite over the base. A comparison with an ordinary coordinate lattice supplies that missing finiteness and establishes the exact degree formula.

Let $K$ be complete discretely valued, $L/K$ finite, and $w$ the unique normalized valuation of $L$. Denote their valuation rings by $A\subset B$. Then $B$ is the integral closure of $A$ in $L$. It is a complete DVR, finite free over $A$, and

$$
\mathfrak m_AB=\mathfrak m_B^e,\qquad
[L:K]=ef,\qquad
[B/\mathfrak m_B:A/\mathfrak m_A]=f.
$$

**Proof of the structural assertions.** Let $n=[L:K]$, choose a $K$-basis $e_1,\ldots,e_n$, and put $M=\sum_iAe_i$. This is an $A$-lattice in $L$. The coordinate norm attached to the basis and the uniquely extended absolute value are equivalent finite-dimensional norms, as in Section 10.6. Because the value group of $K$ is discrete, the comparison constants may be bounded by integral powers of $|\pi|$. Hence there are integers $r,s\geq0$ such that the extended closed unit ball

$$
B_0=\{x\in L:|x|_L\leq1\}
$$

satisfies

$$
\pi^rM\subseteq B_0\subseteq\pi^{-s}M.
$$

The left inclusion can also be seen directly: choose $r$ large enough that every $\pi^re_i$ is integral in size, then use the ultrametric inequality. The right inclusion says that an element whose field size is bounded has bounded coordinates.

Now $\pi^{-s}M$ is a finite free $A$-module. Since $A$ is Noetherian, its submodule $B_0$ is a finite $A$-module. It is torsion-free and contains the full lattice $\pi^rM$, so it has rank $n$. It is also a ring: sums and products of elements of absolute value at most $1$ again have absolute value at most $1$.

Every $x\in B_0$ acts by multiplication on the finite $A$-module $B_0$. The determinant trick applied to this endomorphism gives a monic polynomial over $A$ satisfied by $x$, so $x$ is integral over $A$. Conversely, if $x$ is integral, then it lies in every valuation ring extending $A$, by Section 10.3; in particular $|x|_L\leq1$. Thus $B_0$ is exactly the integral closure $B$.

The extended value group has finite index over $\mathbf Z$ by Section 10.4, so after normalization it is $\mathbf Z$; consequently $B$ is a DVR. It is complete because it is the closed unit ball in the complete field $L$. As a finite torsion-free module over the PID $A$, it is free of rank $n$. Chapter 11 now applies and gives

$$
[L:K]=ef.
$$

This proves simultaneously that the normalization is finite and that $[L:K]=ef$. Nothing in the lattice argument used separability or perfection of the residue field; a finite extension of a complete discretely valued field needs neither hypothesis for these conclusions.

Finite freeness deserves emphasis. It permits an integral basis, reduction modulo powers of the maximal ideal, determinants of multiplication, and passage between field dimension and module length. The proof also explains precisely why completeness matters: it makes the extended field topology complete and permits the unit ball to be compared with an ordinary finite lattice.

### 12.7 Unramified and totally ramified endpoints

The degree equality has two extreme allocations. Naming them isolates residue growth from value-group growth and prepares the finer study of how a general finite extension combines the two.

A finite extension of complete discretely valued fields is **unramified** at this foundational level if $e=1$ and the residue extension is separable. It is **totally ramified** if $f=1$. By Section 12.6, unramified means $[L:K]=f$, while totally ramified means $[L:K]=e$.

When $\overline f\in k[X]$ is monic irreducible and separable, lift it monically to $f\in A[X]$. Section 9.6 shows that $f$ is irreducible. If $\alpha$ is a root and $L=K(\alpha)$, then $\overline\alpha$ already generates a residue extension of degree $\deg f=[L:K]$. The equality $[L:K]=ef$ forces $e=1$, so $L/K$ is unramified with the prescribed residue field. The classification and uniqueness of all such lifts is the next stage of the theory, not an extra assertion needed here.

Eisenstein polynomials give totally ramified extensions. If $A$ is a complete DVR, $f\in A[X]$ is Eisenstein of degree $n$, and $\Pi$ is a root, then the calculation of Section 10.7 gives $[K(\Pi):K]=e=n$, $f=1$, and normalized values

$$
v_L(\Pi)=1,\qquad v_L(a)=n\,v_K(a)\quad(a\in K^\times).
$$

It also identifies the whole integral closure. Write each element of $K(\Pi)$ uniquely as

$$
x=\sum_{i=0}^{n-1}a_i\Pi^i,\qquad a_i\in K.
$$

The nonzero summands have values $nv_K(a_i)+i$, which occupy distinct congruence classes modulo $n$. Their least value therefore occurs only once and cannot cancel. Hence

$$
v_L(x)=\min_i\{nv_K(a_i)+i\}.
$$

This value is nonnegative exactly when every $a_i\in A$. Consequently the valuation ring is $A[\Pi]$, the element $\Pi$ is a uniformizer, and reduction kills every positive power of $\Pi$, leaving the original residue field.

General extensions combine these behaviors, although a canonical decomposition and its detailed ramification theory require further work. The present book supplies the invariants and compatibility statements needed to begin that analysis without ambiguity.

### 12.8 A final synthesis

We began with a local question: how can one retain only the first meaningful order of a function or number? The answer was an ordered-group measurement whose multiplicative law turns factorization into addition and whose strong triangle inequality isolates cancellation. Its bounded elements form a valuation ring, characterized intrinsically by total divisibility. Discreteness then compresses the ideal theory into powers of one maximal ideal and turns that ring into a DVR.

The powers of the maximal ideal provided more than a list of ideals. Their successive quotients recorded leading coefficients, their lengths recovered valuations, and their inverse limit produced completion. Nonarchimedean analysis explained why this limit behaves so rigidly: tails are controlled by their largest term, series converge exactly when their terms vanish, and Newton corrections accelerate. Hensel's lemma converted that analytic rigidity back into algebra by lifting roots and factorizations.

Finally, a finite field extension redistributed degree among three visible phenomena: several extensions of the valuation, enlargement of the value group, and enlargement of the residue field. Integral closure assembled the branches, localization separated them, and completion displayed them as a product. Under the stated finite-normalization hypotheses, the accounting is exact:

$$
\sum_{w\mid v}e(w/v)f(w/v)=[L:K].
$$

Over a complete or merely henselian base, there is one branch. We may therefore move coherently among a valued field, its valuation ring, its residue field, finite-precision quotients, its completion, and the corresponding objects in finite extensions. That coherent local language is the foundation on which the finer arithmetic of ramification is built.

One promise made along the way is still outstanding. Section 8.2 produced digit expansions for every complete DVR and announced, without proof, that in equal characteristic the digits may be chosen to form a subring isomorphic to the residue field, while Section 8.4 recorded that no such subring can exist in mixed characteristic. The final chapter settles both points, for complete local rings far more general than DVRs: it produces the promised copy of the residue field whenever one can exist, produces a substitute when one cannot, and thereby writes every complete Noetherian local ring in coordinates.

## 13. Structure of complete local rings

### 13.1 Coordinates for a complete local ring

The theme of this book has been that completion trades exactness for coordinates. A complete DVR was described in Section 8.2 by digit strings; the coefficients of those strings lived in a chosen set $S$ of residue representatives, and the arithmetic of the strings was the arithmetic of $A$ only up to carries. Two examples showed the two extremes. In $k[[t]]$ one may take $S=k$, because $k$ genuinely sits inside $k[[t]]$ as the constant series; digits then multiply by the Cauchy product and the digit description _is_ the ring. In $\mathbf Z_p$ one may not: a ring containing $\mathbf F_p$ has characteristic $p$, whereas $\mathbf Z_p$ has characteristic zero, so the digits $\{0,\ldots,p-1\}$ can only be a set of representatives and carries are forced.

This chapter shows that these two examples are not accidents but a complete classification, and that the classification holds far beyond DVRs. The results are due to Cohen, and they say the following. A complete Noetherian local ring that contains _some_ field contains a field mapping isomorphically onto its residue field — a **coefficient field** — so its arithmetic is that of a quotient of a formal power series ring over the residue field. A complete Noetherian local ring of mixed characteristic contains no field at all, but it does receive a map from a canonical-up-to-isomorphism complete DVR with residue field $k$ and uniformizer $p$ — a **Cohen ring** — which plays exactly the role $\mathbf Z_p$ plays for $\mathbf F_p$. In both cases the outcome is the same: every complete Noetherian local ring is a quotient of a formal power series ring over a ring of coefficients, and complete regular local rings are, up to the ramification of $p$, exactly such power series rings.

The reason to prove this in a book on valuations and completions is that it is the statement which converts local algebra into local _analysis_ in the sense used throughout Chapters 5 to 9. It says that after completing, an abstract local ring acquires coordinates: a coefficient ring in which one may compute residues, and finitely many variables in which one may expand. Every later use of complete local rings — comparing a singular local ring with a regular one, resolving singularities on a two-dimensional model, testing normality after completion — begins by choosing those coordinates.

Throughout this chapter $(A,\mathfrak m)$ denotes a Noetherian local ring with residue field $k=A/\mathfrak m$, and **complete** always means complete _and separated_ for the $\mathfrak m$-adic topology, that is,

$$
A\xrightarrow{\ \sim\ }\varprojlim_n A/\mathfrak m^n .
$$

This is the notion of Section 7.5, specialized to $I=\mathfrak m$; by Theorem 8.1 it agrees with metric completeness when $A$ is a DVR. A homomorphism $f:R\to A$ of local rings is **local** if $f(\mathfrak m_R)\subseteq\mathfrak m_A$; every ring homomorphism we write between local rings will be local.

Beyond what this book has already developed, the arguments use only standard commutative algebra: Nakayama's lemma, the Artin–Rees lemma and the Krull intersection theorem it yields, the fact that a formal power series ring in finitely many variables over a Noetherian ring is Noetherian, tensor products, and Zorn's lemma. We record the three consequences of this background that get used continually.

**Lemma 13.1 (finite modules over a complete local ring).** Let $(A,\mathfrak m)$ be a complete Noetherian local ring and $M$ a finitely generated $A$-module. Then:

1. $\bigcap_n\mathfrak m^nM=0$, and $M$ is complete for its $\mathfrak m$-adic topology;
2. if $m_1,\ldots,m_r\in M$ have images spanning the $k$-vector space $M/\mathfrak mM$, then they generate $M$;
3. every series $\sum_{n\geq0}z_n$ with $z_n\in\mathfrak m^nM$ converges in $M$, and its value is unchanged by reordering.

**Proof.** Part 1 is the Krull intersection theorem together with the standard fact that completion is exact on finitely generated modules over a Noetherian ring: writing $M$ as a quotient of $A^r$, the Artin–Rees lemma says that the submodule topology induced on the kernel $N\subseteq A^r$ agrees with its own $\mathfrak m$-adic topology, so $\varprojlim_n M/\mathfrak m^nM=A^r/N=M$ because $A^r$ is complete. Part 2 is Nakayama's lemma applied to the finitely generated module $M/\sum_iAm_i$, which satisfies $M'=\mathfrak mM'$. Part 3 holds because the partial sums are Cauchy for a filtration with zero intersection, and because rearranging changes a partial sum only by terms lying in arbitrarily high powers of $\mathfrak m$. $\square$

**Lemma 13.2 (power series rings and quotients).** Let $(R,\mathfrak m_R)$ be a complete Noetherian local ring. Then every quotient $R/I$ is a complete Noetherian local ring, and $R[[X_1,\ldots,X_n]]$ is a complete Noetherian local ring with maximal ideal

$$
\mathfrak n=\mathfrak m_RR[[X_1,\ldots,X_n]]+(X_1,\ldots,X_n)
$$

and residue field $R/\mathfrak m_R$.

**Proof.** For a quotient, the ideals $(\mathfrak m_R^n+I)/I$ are cofinal with the powers of the maximal ideal of $R/I$, and $\varprojlim_n R/(\mathfrak m_R^n+I)=R/I$ because $R$ is complete and $I$ is closed, being an intersection of the ideals $\mathfrak m_R^n+I$ by the Krull intersection theorem applied in $R/I$.

For power series it suffices to treat $n=1$ and iterate. Noetherianity is the power series form of the Hilbert basis theorem. A series is a unit exactly when its constant term is a unit of $R$, since one may then solve for the inverse coefficients recursively; hence the non-units form the ideal $\mathfrak n$ and the ring is local with the stated residue field. For completeness, compare $\mathfrak n^m$ with

$$
I_m=\mathfrak m_R^mR[[X]]+X^mR[[X]].
$$

Expanding, $\mathfrak n^m=\sum_{i+j=m}\mathfrak m_R^iX^jR[[X]]$. Each such summand has $i\geq m/2$ or $j\geq m/2$, so $I_m\subseteq\mathfrak n^m\subseteq I_{\lceil m/2\rceil}$ and the two filtrations define the same topology. Now reducing coefficients modulo $\mathfrak m_R^m$ and truncating above degree $m$ identifies

$$
R[[X]]/I_m\cong (R/\mathfrak m_R^m)[X]/(X^m),
$$

since a series lies in $I_m$ exactly when its coefficients in degrees below $m$ lie in $\mathfrak m_R^m$. In the inverse limit over $m$, the coefficient of $X^j$ becomes a compatible family in $\varprojlim_m R/\mathfrak m_R^m=R$, and these coefficients are unconstrained; so $\varprojlim_mR[[X]]/I_m=R[[X]]$. $\square$

The third preliminary is the mapping property that will actually produce the structure theorem. It says that a complete local ring is generated over a subring in the _topological_ sense as soon as it is generated modulo one power of the maximal ideal, and that power series in a chosen finite list of elements are exactly the available expressions.

**Lemma 13.3 (evaluation of power series).** Let $R_0$ and $A$ be complete Noetherian local rings, let $\sigma:R_0\to A$ be a local homomorphism, and let $x_1,\ldots,x_n\in\mathfrak m_A$. Then there is a unique continuous $R_0$-algebra homomorphism

$$
\Sigma:R_0[[X_1,\ldots,X_n]]\longrightarrow A,
\qquad
\Sigma\Big(\sum_\alpha c_\alpha X^\alpha\Big)=\sum_\alpha \sigma(c_\alpha)x^\alpha ,
$$

and it is local. Writing $J=\sigma(\mathfrak m_{R_0})A+(x_1,\ldots,x_n)A$, the map $\Sigma$ is surjective if and only if $A=\sigma(R_0)+J$.

**Proof roadmap.** Convergence of the defining sum is immediate because the monomials of total degree $d$ lie in $\mathfrak m_A^d$. For surjectivity, the hypothesis lets one write any element of $A$ as an image plus an error in $J$, then expand the coefficients of that error and repeat; the successive corrections lie in higher and higher powers of the maximal ideal of $R_0[[X]]$, so they sum to a power series.

**Proof.** For each $d$ there are only finitely many monomials $X^\alpha$ of total degree $d$, and $x^\alpha\in\mathfrak m_A^d$ for such $\alpha$; so the displayed sum converges by Lemma 13.1.3 and $\Sigma$ is well defined. It respects sums visibly, and respects products because a product of two power series has each of its coefficients given by a finite sum, and because multiplication in $A$ is continuous. It carries $\mathfrak n$ into $\mathfrak m_A$, hence is local, and continuity plus the values on $R_0$ and on the $X_i$ determine it, since polynomials are dense.

If $\Sigma$ is surjective, then since every power series is its constant term plus an element of $\mathfrak n$, and $\Sigma(\mathfrak n)\subseteq J$, we get $A=\sigma(R_0)+J$.

Conversely assume $A=\sigma(R_0)+J$. Choose generators $u_1,\ldots,u_s$ of $\mathfrak m_{R_0}$, possible as $R_0$ is Noetherian, so that $J$ is generated by the $s+n$ elements $\sigma(u_1),\ldots,\sigma(u_s),x_1,\ldots,x_n$. Fix $a\in A$. We construct $F_m\in R_0[[X]]$ with

$$
a-\Sigma(F_m)\in J^m,
\qquad
F_{m+1}-F_m\in\mathfrak n^m .
$$

Take $F_0=0$. Given $F_m$, the ideal $J^m$ is generated by the images under $\Sigma$ of the degree-$m$ monomials $M$ in the letters $u_1,\ldots,u_s,X_1,\ldots,X_n$, and each such $M$ lies in $\mathfrak n^m$. Write

$$
a-\Sigma(F_m)=\sum_M c_M\,\Sigma(M),
\qquad c_M\in A,
$$

a finite sum. By hypothesis $c_M=\sigma(r_M)+j_M$ with $r_M\in R_0$ and $j_M\in J$. Put $F_{m+1}=F_m+\sum_M r_MM$. Then $F_{m+1}-F_m\in\mathfrak n^m$ and

$$
a-\Sigma(F_{m+1})=\sum_M j_M\,\Sigma(M)\in J^{m+1},
$$

as required. Since $R_0[[X]]$ is complete by Lemma 13.2, the $F_m$ converge to some $F$, and continuity gives $\Sigma(F_m)\to\Sigma(F)$. But $J\subseteq\mathfrak m_A$, so $a-\Sigma(F_m)\in\mathfrak m_A^m$ tends to $0$. Hence $a=\Sigma(F)$. $\square$

With the mechanics in place we can name the objects the chapter is about. Let $(A,\mathfrak m)$ be a complete Noetherian local ring with residue field $k$. A **coefficient field** of $A$ is a subfield $K\subseteq A$ such that the reduction map $K\to k$ is an isomorphism; equivalently, $K\subseteq A$ is a subfield with $K\cap\mathfrak m=0$ and $K+\mathfrak m=A$. More generally, a **coefficient ring** of $A$ is a complete Noetherian local subring $C\subseteq A$ whose maximal ideal is $\mathfrak m_C=\mathfrak m\cap C$, whose residue map $C/\mathfrak m_C\to k$ is an isomorphism, and which is either a field or a DVR with uniformizer $p$.

Whether a coefficient field can exist is decided by characteristics alone. Let $p\geq0$ be the characteristic of $k$. Since $\mathfrak m$ is nilpotent modulo no power of itself but consists of non-units, the characteristic of $A$ is either $0$ or a power of $p$. Three cases occur:

- **Equal characteristic zero:** $\operatorname{char}A=\operatorname{char}k=0$, equivalently $\mathbf Q\subseteq A$.
- **Equal characteristic $p$:** $\operatorname{char}A=\operatorname{char}k=p>0$, equivalently $A$ contains $\mathbf F_p$.
- **Mixed characteristic:** $\operatorname{char}k=p>0$ and $\operatorname{char}A=0$ or $p^e$ with $e\geq2$; equivalently $p\in\mathfrak m$ and $p\neq0$ in $A$.

A ring containing a field is exactly one of equal characteristic, since a field inside $A$ maps injectively to $k$ and hence has the same characteristic as $k$; and conversely $\mathbf F_p\subseteq A$ or $\mathbf Q\subseteq A$ in the two equal-characteristic cases. Thus a coefficient field can exist only in equal characteristic, and Sections 13.2 and 13.4 will show that in equal characteristic it always does. In mixed characteristic the substitute is a Cohen ring, constructed in Section 13.5.

Some orienting examples. The ring $k[[t]]$ has coefficient field the constants $k$. The ring $\mathbf Z_p$ is its own coefficient ring, a DVR with uniformizer $p$ and residue field $\mathbf F_p$; it contains no field, because a subfield would have to contain $\mathbf Z$ or $\mathbf F_p$, and $\mathbf Z\subseteq\mathbf Z_p$ generates the non-complete field $\mathbf Q\not\subseteq\mathbf Z_p$ while $\mathbf F_p$ cannot embed in a characteristic-zero ring. The ring $\mathbf Z_p[[t]]$, met in Section 4.3, is a two-dimensional complete regular local ring of mixed characteristic with coefficient ring $\mathbf Z_p$. The ring $\mathbf Z/p^2\mathbf Z$ is complete local of mixed characteristic $p^2$; it contains no field, and its coefficient ring cannot be a subring of itself in the naive sense — indeed the correct statement, proved in Section 13.7, is that it is a _quotient_ $\mathbf Z_p/p^2\mathbf Z_p$ of a Cohen ring rather than an extension of one. This last example is the reason the structure theorem is stated with surjections rather than with inclusions.

### 13.2 Coefficient fields in equal characteristic zero

A coefficient field is a subfield of $A$ as large as possible: one that already accounts for the entire residue field. The natural first attempt is therefore to take a subfield of $A$ that cannot be enlarged and hope that maximality forces surjectivity onto $k$. Zorn's lemma supplies such a maximal subfield with no effort. The content of the argument is the enlargement step: given a subfield $K\subseteq A$ whose residue image misses some $\overline b\in k$, one must produce a strictly larger subfield of $A$.

There are two ways $\overline b$ can fail to lie in the image $\overline K$ of $K$, and each has its own enlargement mechanism. If $\overline b$ is transcendental over $\overline K$, then _any_ lift of it to $A$ works, because a nonzero polynomial expression in a transcendental element cannot reduce to zero and hence cannot lie in $\mathfrak m$. If $\overline b$ is algebraic over $\overline K$, an arbitrary lift is useless; one needs a lift satisfying the same algebraic equation, and that is precisely what Hensel's lemma provides — _provided the equation has $\overline b$ as a simple root_. In characteristic zero every minimal polynomial is separable, so the simple-root hypothesis is automatic and the two mechanisms exhaust the possibilities. This is why equal characteristic zero is the easy case. In characteristic $p$ a purely inseparable residue element is a multiple root of its minimal polynomial, Hensel's lemma says nothing, and the enlargement step genuinely fails; Section 13.8 exhibits a maximal subfield of $\mathbf F_p(u)[[t]]$ that is not a coefficient field.

We begin with the three elementary facts that make the two mechanisms precise. Throughout, $(A,\mathfrak m)$ is a local ring that is complete and separated for its $\mathfrak m$-adic topology, with residue field $k$, and for a subfield $K\subseteq A$ we write $\overline K\subseteq k$ for its image under reduction.

**Lemma 13.4 (subfields reduce injectively).** Every subfield $K\subseteq A$ satisfies $K\cap\mathfrak m=0$, so reduction restricts to an isomorphism $K\xrightarrow{\sim}\overline K$ of fields. Consequently $K$ is a coefficient field if and only if $\overline K=k$.

**Proof.** A nonzero element of $K$ is invertible in $K$, hence a unit of $A$, hence not in $\mathfrak m$. So the kernel of $K\to k$ is zero, and a field homomorphism onto its image is an isomorphism. The last sentence restates the definition of a coefficient field. $\square$

**Lemma 13.5 (adjoining a transcendental residue element).** Let $K\subseteq A$ be a subfield and let $\overline b\in k$ be transcendental over $\overline K$. Choose any $b\in A$ reducing to $\overline b$. Then every nonzero element of the subring $K[b]\subseteq A$ is a unit of $A$, so the elements $f(b)g(b)^{-1}$ with $f,g\in K[X]$ and $g\neq0$ form a subfield $K(b)\subseteq A$ containing $K$ properly, with residue image $\overline K(\overline b)$.

**Proof.** Identify $K$ with $\overline K$ by Lemma 13.4 and let $f\in K[X]$ be nonzero, with reduced polynomial $\overline f\in\overline K[X]$, also nonzero. Reduction is a ring homomorphism, so $f(b)$ reduces to $\overline f(\overline b)$, which is nonzero because $\overline b$ is transcendental over $\overline K$. Hence $f(b)\notin\mathfrak m$, so $f(b)$ is a unit of the local ring $A$. In particular $K[b]$ is a domain and the indicated quotients are well defined elements of $A$; they are closed under the field operations, so they form a subfield. It contains $b\notin K$, since $\overline b\notin\overline K$. Its residue image consists of all $\overline f(\overline b)\overline g(\overline b)^{-1}$, which is $\overline K(\overline b)$. $\square$

**Lemma 13.6 (adjoining a separable algebraic residue element).** Let $K\subseteq A$ be a subfield and let $\overline b\in k$ be algebraic and _separable_ over $\overline K$. Then there is a unique $b\in A$ reducing to $\overline b$ and annihilated by the polynomial $g\in K[X]$ corresponding, under the isomorphism $K\cong\overline K$, to the minimal polynomial of $\overline b$ over $\overline K$. For this $b$ the subring $K[b]\subseteq A$ is a subfield, isomorphic to $K[X]/(g)$, with residue image $\overline K(\overline b)$.

**Proof.** Let $\overline g\in\overline K[X]$ be the minimal polynomial of $\overline b$ and let $g\in K[X]\subseteq A[X]$ be the corresponding monic polynomial; its reduction in $k[X]$ is $\overline g$ regarded inside $k[X]$. Separability means $\overline g'(\overline b)\neq0$, that is, $\overline b$ is a simple root, so over $k$ we may factor

$$
\overline g=(X-\overline b)\,\overline h,
\qquad \overline h(\overline b)\neq0,
$$

with the two monic factors coprime in $k[X]$. By Theorem 9.4 the complete separated local ring $A$ is henselian, so this factorization lifts uniquely to a factorization $g=(X-b)h$ with $b\in A$ reducing to $\overline b$ and $h\in A[X]$ monic. Thus $g(b)=0$, and uniqueness of the henselian lift gives uniqueness of $b$ among roots of $g$ reducing to $\overline b$; any root of $g$ reducing to $\overline b$ produces such a factorization by division, so $b$ is unique as claimed.

Now consider the evaluation map $K[X]\to A$, $X\mapsto b$. Its kernel contains $g$. Since $\overline g$ is irreducible over $\overline K$ and $K\cong\overline K$ carries $\overline g$ to $g$, the polynomial $g$ is irreducible over $K$, so $K[X]/(g)$ is a field and the induced map $K[X]/(g)\to A$ is a nonzero homomorphism from a field, hence injective. Its image is $K[b]$, a subfield of $A$. Reduction carries $K[b]$ onto $\overline K[\overline b]=\overline K(\overline b)$. $\square$

We can now settle equal characteristic zero. Note that the proof uses completeness only through henselianity and does not use the Noetherian hypothesis at all.

**Theorem 13.7 (coefficient fields in equal characteristic zero).** Let $(A,\mathfrak m)$ be a local ring that is complete and separated for its $\mathfrak m$-adic topology and whose residue field $k$ has characteristic zero. Suppose $A$ contains a field. Then $A$ has a coefficient field. Moreover, every maximal subfield of $A$ is a coefficient field, and every subfield of $A$ is contained in one.

**Proof roadmap.** Subfields of $A$ form a nonempty poset closed under unions of chains, so Zorn's lemma produces maximal ones. If the residue image of a maximal subfield were not all of $k$, pick a residue element outside it: Lemma 13.5 or Lemma 13.6 enlarges the subfield, contradicting maximality. Characteristic zero guarantees that the algebraic alternative is always separable.

**Proof.** First, $A$ has characteristic zero: a field $F\subseteq A$ reduces injectively into $k$ by Lemma 13.4, so $\operatorname{char}F=\operatorname{char}k=0$, and $F$ contains a copy of $\mathbf Q$. So the collection $\mathcal S$ of subfields of $A$ is nonempty. It is a set, being a collection of subsets of $A$, and it is partially ordered by inclusion. The union of a chain in $\mathcal S$ is again a subfield, since any two of its elements already lie in a common member of the chain. By Zorn's lemma, every member of $\mathcal S$ is contained in a maximal member.

Let $K\in\mathcal S$ be maximal and suppose, for contradiction, that $\overline K\neq k$. Choose $\overline b\in k\setminus\overline K$. Since $\operatorname{char}k=0$, the extension $k/\overline K$ is separable, so $\overline b$ is either transcendental over $\overline K$ or separably algebraic over it. In the transcendental case, Lemma 13.5 produces a subfield $K(b)\subseteq A$ strictly containing $K$. In the algebraic case, Lemma 13.6 produces a subfield $K[b]\subseteq A$ whose residue image contains $\overline b\notin\overline K$, so again $K[b]\supsetneq K$. Either way maximality is contradicted. Hence $\overline K=k$, and Lemma 13.4 makes $K$ a coefficient field. $\square$

Two remarks are worth recording before turning to characteristic $p$.

First, the theorem gives _many_ coefficient fields, not a canonical one. Starting the Zorn process from different subfields generally produces different maximal ones. Section 13.8 makes this concrete in $\mathbf Q(u)[[t]]$, where $\mathbf Q(u)$ and $\mathbf Q(u+t)$ are two distinct coefficient fields; there is no way to choose one of them naturally, and the isomorphism $A\cong k[[t]]$ produced by a coefficient field is correspondingly non-canonical. This absence of canonicity is not a defect of the proof. It reflects the fact that the residue field of $A$ has no preferred lift, and it will reappear, with the same source, in the theory of Cohen rings.

Second, the proof isolates exactly what characteristic zero was used for: it guaranteed that every algebraic residue element is a simple root of its minimal polynomial. In characteristic $p$ this holds for separable residue elements and fails for inseparable ones. If $\overline b^p=\overline c\in\overline K$ with $\overline b\notin\overline K$, the relevant equation is $X^p-c=0$ with $c\in K$ the element corresponding to $\overline c$; its derivative vanishes identically, so no lifting theorem of Hensel type applies, and indeed a solution in $A$ may simply not exist. Repairing this requires a different idea: rather than lifting residue elements one at a time by solving equations, one lifts a whole _coordinate system_ for the inseparability of $k$ — a $p$-basis — and builds the coefficient field from it by extracting $p$-th powers. That is the subject of the next two sections.

### 13.3 $p$-bases and derivations

Fix a field $k$ of characteristic $p>0$. The Frobenius map $x\mapsto x^p$ is an injective ring endomorphism of $k$, so its image

$$
k^p=\{x^p:x\in k\}
$$

is a subfield, and $k$ is a vector space over $k^p$. The field $k$ is **perfect** exactly when $k=k^p$. Imperfection is measured by how far $k$ is from $k^p$, and the previous section showed that this is precisely the obstruction to lifting residue elements by Hensel's lemma: an element $\overline b\in k\setminus k^p(\ldots)$ satisfies only the inseparable equation $X^p=\overline b^p$.

The idea that resolves the difficulty is to stop treating residue elements one at a time. The extension $k/k^p$ is generated by elements each of degree $1$ or $p$, and it has a well-behaved notion of independent generators: a family $B$ such that $k$ is obtained from $k^p$ by adjoining the elements of $B$ with no relations beyond the forced ones $b^p\in k^p$. Such a family is a **$p$-basis**. Two facts make $p$-bases the right tool. First, they always exist, by a Zorn's lemma argument no harder than for transcendence bases. Second — and this is the decisive point — a $p$-basis presents $k$ by _explicit equations of a very special shape_, namely $X_b^p=c_b$ with $c_b\in k^p$. Whenever one must lift a homomorphism out of $k$ into some ring, one may therefore lift generator by generator, and the only obligation is to find $p$-th roots that were already available for free. This is why an obstruction that looked fatal for one element at a time evaporates when a whole $p$-basis is treated at once.

This section develops $p$-bases from scratch, proves the derivation-extension theorem that expresses their universal role, and then proves the lifting theorem in the form used twice in the sequel. We begin with the elementary degree computation on which everything rests.

**Lemma 13.8 (degrees over intermediate fields).** Let $F$ be a field with $k^p\subseteq F\subseteq k$, and let $b\in k$. Then $F(b)=F[b]$ and

$$
[F(b):F]=\begin{cases}1,&b\in F,\\ p,&b\notin F.\end{cases}
$$

**Proof.** We have $b^p\in k^p\subseteq F$, so $b$ is a root of $X^p-b^p=(X-b)^p\in F[X]$; in particular $b$ is algebraic over $F$ and $F[b]=F(b)$. The minimal polynomial of $b$ over $F$ divides $(X-b)^p$ in $k[X]$, hence equals $(X-b)^m$ for some $1\leq m\leq p$. Its coefficient of $X^{m-1}$ is $-mb$ and lies in $F$. If $1<m<p$, then $m$ is invertible in $k$, so $b\in F$ and the minimal polynomial would be $X-b$, contradicting $m>1$. Hence $m=1$, which happens exactly when $b\in F$, or $m=p$. $\square$

A subset $B\subseteq k$ is called **$p$-independent** if for every finite set of distinct elements $b_1,\ldots,b_r\in B$ the $p^r$ **$p$-monomials**

$$
b_1^{e_1}b_2^{e_2}\cdots b_r^{e_r},
\qquad 0\leq e_i<p,
$$

are linearly independent over $k^p$. It is a **$p$-basis** of $k$ if in addition $k=k^p(B)$. For a subset $S\subseteq k$ we write $k^p(S)$ for the subfield generated; by Lemma 13.8 and the fact that every element of $k^p(S)$ involves only finitely many elements of $S$, we have $k^p(S)=k^p[S]$, the subring generated.

**Lemma 13.9 (three forms of $p$-independence).** For a subset $B\subseteq k$ the following are equivalent.

1. $B$ is $p$-independent.
2. $[k^p(b_1,\ldots,b_r):k^p]=p^r$ for all distinct $b_1,\ldots,b_r\in B$.
3. $b\notin k^p(B\setminus\{b\})$ for every $b\in B$.

**Proof.** The ring $k^p[b_1,\ldots,b_r]=k^p(b_1,\ldots,b_r)$ is spanned over $k^p$ by all monomials in the $b_i$, and since $b_i^p\in k^p$ every exponent may be reduced modulo $p$. So the $p^r$ $p$-monomials span, and they are independent exactly when the dimension equals $p^r$. This is the equivalence of 1 and 2.

Assume 2 and suppose $b\in k^p(B\setminus\{b\})$ for some $b\in B$. Then $b\in k^p(b_1,\ldots,b_s)$ for finitely many distinct $b_i\in B\setminus\{b\}$, whence $k^p(b,b_1,\ldots,b_s)=k^p(b_1,\ldots,b_s)$ has degree $p^s$ over $k^p$, contradicting 2 applied to the $s+1$ distinct elements $b,b_1,\ldots,b_s$. So 2 implies 3.

Assume 3 and let $b_1,\ldots,b_r\in B$ be distinct. Argue by induction on $r$, the case $r=0$ being trivial. Put $F=k^p(b_1,\ldots,b_{r-1})$, of degree $p^{r-1}$ by induction. Since $F\subseteq k^p(B\setminus\{b_r\})$ and $b_r\notin k^p(B\setminus\{b_r\})$, we get $b_r\notin F$, so $[F(b_r):F]=p$ by Lemma 13.8. Multiplying degrees in the tower gives $p^r$. $\square$

**Lemma 13.10 (existence of $p$-bases).** Every $p$-independent subset of $k$ is contained in a $p$-basis; in particular $k$ has a $p$-basis. A subset is a $p$-basis if and only if it is a maximal $p$-independent subset. The field $k$ is perfect if and only if $\emptyset$ is a $p$-basis of $k$.

**Proof.** $p$-independence is a condition on finite subsets, so the union of a chain of $p$-independent subsets is $p$-independent, and Zorn's lemma provides a maximal $p$-independent subset $B$ containing any given one. Suppose $k\neq k^p(B)$ and pick $x\in k\setminus k^p(B)$. We claim $B\cup\{x\}$ is $p$-independent, using criterion 3 of Lemma 13.9. For the element $x$ itself, $x\notin k^p(B)$ by choice. For $b\in B$, set $F=k^p(B\setminus\{b\})$ and suppose $b\in F(x)$. Since $b\notin F$ by $p$-independence of $B$, Lemma 13.8 gives $[F(b):F]=p$, while $[F(x):F]\leq p$; from $F\subseteq F(b)\subseteq F(x)$ we conclude $F(x)=F(b)$, so $x\in F(b)\subseteq k^p(B)$, a contradiction. Thus $B\cup\{x\}$ is $p$-independent and strictly larger, contradicting maximality. Hence $k=k^p(B)$ and $B$ is a $p$-basis.

Conversely a $p$-basis $B$ is maximal: for $x\in k\setminus B$ we have $x\in k=k^p(B)$, so criterion 3 fails for $B\cup\{x\}$. Finally $\emptyset$ is always $p$-independent, and it is a $p$-basis exactly when $k=k^p$. $\square$

**Lemma 13.11 (monomial basis and presentation).** Let $B$ be a $p$-basis of $k$. Then the $p$-monomials

$$
\prod_{b\in B}b^{e_b},
\qquad 0\leq e_b<p,\ \ e_b=0\ \text{for all but finitely many}\ b,
$$

form a basis of $k$ as a $k^p$-vector space. Consequently, if $\{X_b\}_{b\in B}$ are indeterminates, the $k^p$-algebra homomorphism

$$
k^p[X_b:b\in B]\longrightarrow k,\qquad X_b\longmapsto b,
$$

is surjective with kernel generated by the polynomials $X_b^p-b^p$, so that

$$
k\cong k^p[X_b:b\in B]\big/\big(X_b^p-b^p:b\in B\big).
$$

If $B$ is finite with $n$ elements, then $[k:k^p]=p^n$.

**Proof.** Linear independence is the definition of $p$-independence, since any linear relation involves finitely many monomials and hence finitely many elements of $B$. They span because $k=k^p(B)=k^p[B]$ and every monomial in elements of $B$ reduces, using $b^p\in k^p$, to a $k^p$-multiple of a $p$-monomial.

For the presentation, surjectivity is $k=k^p[B]$, and the listed polynomials lie in the kernel. Let $Q$ denote the quotient of $k^p[X_b]$ by the ideal they generate. In $Q$ each $X_b^p$ equals the scalar $b^p\in k^p$, so $Q$ is spanned over $k^p$ by the images of the monomials $\prod X_b^{e_b}$ with all $e_b<p$. The induced surjection $Q\to k$ carries this spanning family bijectively onto the $p$-monomials, which are a $k^p$-basis of $k$. A surjection carrying a spanning family onto a basis is an isomorphism and the family is a basis. Hence $Q\cong k$. The degree formula is immediate from the basis. $\square$

Lemma 13.11 already contains the whole point: _a $p$-basis presents $k$ over $k^p$ by the equations $X_b^p=b^p$, with no other relations._ Everything below is an application of that presentation. The first application explains the name "differential criterion" and shows that a $p$-basis is exactly a system of independent coordinates for differentiation.

Recall that for a $k$-vector space $M$, a **derivation** $D:k\to M$ is an additive map satisfying the Leibniz rule $D(xy)=xD(y)+yD(x)$. Every derivation kills $1$, since $D(1)=D(1\cdot1)=2D(1)$, and kills $k^p$, since $D(x^p)=px^{p-1}D(x)=0$; hence every derivation is $k^p$-linear, because $D(x^py)=x^pD(y)+yD(x^p)=x^pD(y)$.

**Theorem 13.12 (derivation extension).** Let $B$ be a $p$-basis of $k$ and $M$ a $k$-vector space. For every function $\delta:B\to M$ there is a unique derivation $D:k\to M$ with $D(b)=\delta(b)$ for all $b\in B$. Thus restriction to $B$ identifies the $k$-vector space of derivations $k\to M$ with the space of all functions $B\to M$.

**Proof roadmap.** A derivation into $M$ is the same thing as a ring-theoretic splitting of the square-zero extension $k\oplus M\to k$. Splittings are constructed from the presentation of Lemma 13.11: one must choose, for each $b$, an element of $k\oplus M$ lifting $b$ whose $p$-th power is the prescribed $b^p$. Because $M$ has square zero and the characteristic is $p$, _every_ lift has this property, so the choices are free.

**Proof.** Let $R=k\oplus M$ be the ring with $M$ an ideal of square zero and the given $k$-module structure, so $(x+m)(y+m')=xy+(xm'+ym)$. Let $\pi:R\to k$ be the projection. Giving a derivation $D:k\to M$ is the same as giving a ring homomorphism $\phi:k\to R$ with $\pi\circ\phi=\operatorname{id}$, via $\phi(x)=x+D(x)$: additivity of $\phi$ is additivity of $D$, and multiplicativity of $\phi$ is exactly the Leibniz rule.

For $x\in k$ and $m\in M$ the binomial expansion in $R$ gives

$$
(x+m)^p=x^p+px^{p-1}m=x^p,
$$

because $m^2=0$ kills all terms of degree at least two in $m$, and $p=0$ in $k$. So every lift of $x$ to $R$ has $p$-th power equal to $x^p\in k\subseteq R$.

Now let $\delta:B\to M$ be given and set $\beta_b=b+\delta(b)\in R$. By the previous paragraph $\beta_b^p=b^p$. Regard $R$ as a $k^p$-algebra through $k^p\subseteq k\subseteq R$. Then the $k^p$-algebra homomorphism $k^p[X_b]\to R$ sending $X_b\mapsto\beta_b$ kills every $X_b^p-b^p$, hence factors through the presentation of Lemma 13.11 and yields a ring homomorphism $\phi:k\to R$ with $\phi|_{k^p}$ the inclusion and $\phi(b)=\beta_b$. The composite $\pi\circ\phi:k\to k$ is a $k^p$-algebra homomorphism fixing every $b\in B$, hence fixes $k^p[B]=k$; so $\phi$ is a splitting and $D(x)=\phi(x)-x$ is a derivation with $D(b)=\delta(b)$.

For uniqueness, let $D$ be any derivation with $D|_B=\delta$ and let $\phi$ be the corresponding splitting. Then $\phi$ is $k^p$-linear because $D$ is, so $\phi$ is a $k^p$-algebra homomorphism determined by its values on the generators $B$ of $k$ over $k^p$; these are prescribed. Hence $\phi$, and therefore $D$, is unique. $\square$

The same presentation argument, run over an arbitrary base rather than over $k\oplus M$, gives the lifting theorem that will produce coefficient fields in characteristic $p$. It is the precise sense in which a field of characteristic $p$ is "formally smooth over $\mathbf F_p$": homomorphisms out of $k$ extend across nilpotent thickenings.

**Theorem 13.13 (lifting a field of characteristic $p$ across a square-zero extension).** Let $R$ be a ring with $pR=0$, let $I\subseteq R$ be an ideal with $I^2=0$, and write $\pi:R\to R/I$ for the quotient map. Let $k$ be a field of characteristic $p$, let $B$ be a $p$-basis of $k$, and let $\psi:k\to R/I$ be a ring homomorphism. Then for every choice of elements $\beta_b\in R$ with $\pi(\beta_b)=\psi(b)$ there is a unique ring homomorphism $\phi:k\to R$ with

$$
\pi\circ\phi=\psi
\qquad\text{and}\qquad
\phi(b)=\beta_b\ \ (b\in B).
$$

In particular $\psi$ lifts to $R$, and the lifts are in bijection with the families of lifts of the $\psi(b)$.

**Proof roadmap.** Since $R$ has characteristic $p$ and $I$ has square zero, the $p$-th power map on $R$ is insensitive to $I$ and therefore descends to a canonical ring homomorphism $R/I\to R$. Composing it with $\psi$ and the inverse of Frobenius produces the only possible lift of $\psi$ on $k^p$, with no choices at all. On the generators $B$ the presentation of Lemma 13.11 shows that the choices are unconstrained.

**Proof.** For $x\in R$ and $i\in I$ we have, as in the previous proof, $(x+i)^p=x^p$, because $i^2=0$ and $p=0$ in $R$. Hence the map

$$
\theta:R/I\longrightarrow R,\qquad \theta(\overline x)=x^p\ \ \text{for any lift }x\in R,
$$

is well defined. It is a ring homomorphism: multiplicativity is clear, and additivity holds because $(x+y)^p=x^p+y^p$ in the characteristic-$p$ ring $R$. By construction $\pi\circ\theta$ is the $p$-th power map of $R/I$.

Since Frobenius is a bijection from $k$ onto $k^p$, we may define $\phi_0:k^p\to R$ by $\phi_0(x^p)=\theta(\psi(x))$. It is a ring homomorphism, being the composite of the inverse Frobenius $k^p\to k$, then $\psi$, then $\theta$. It lifts $\psi|_{k^p}$, since

$$
\pi\big(\phi_0(x^p)\big)=\pi\theta\big(\psi(x)\big)=\psi(x)^p=\psi(x^p).
$$

Regard $R$ as a $k^p$-algebra via $\phi_0$. For $b\in B$ the chosen lift $\beta_b$ of $\psi(b)$ satisfies

$$
\beta_b^p=\theta\big(\pi(\beta_b)\big)=\theta\big(\psi(b)\big)=\phi_0(b^p),
$$

so the $k^p$-algebra homomorphism $k^p[X_b]\to R$ with $X_b\mapsto\beta_b$ kills every $X_b^p-b^p$. By Lemma 13.11 it factors through $k$, producing a ring homomorphism $\phi:k\to R$ extending $\phi_0$ with $\phi(b)=\beta_b$. Both $\pi\circ\phi$ and $\psi$ are ring homomorphisms $k\to R/I$ which agree on $k^p$ and on $B$, hence on $k^p[B]=k$; so $\pi\circ\phi=\psi$.

For uniqueness, let $\phi$ be any lift of $\psi$ with $\phi(b)=\beta_b$. For $x\in k$ the element $\phi(x)$ lifts $\psi(x)$, so $\phi(x^p)=\phi(x)^p=\theta(\psi(x))=\phi_0(x^p)$. Thus $\phi$ agrees with $\phi_0$ on $k^p$, and it is prescribed on $B$; since $k=k^p[B]$, it is determined. $\square$

Some examples fix the notions. A perfect field, such as any finite field, any algebraically closed field, or $\mathbf F_p((t))^{\mathrm{perf}}$, has empty $p$-basis; Theorem 13.13 then says that a homomorphism from a perfect field of characteristic $p$ lifts _uniquely_ across a square-zero extension in characteristic $p$, since there are no choices to make. The rational function field $k_0=\mathbf F_p(u)$ has $p$-basis $\{u\}$ and $[k_0:k_0^p]=p$; the field $\mathbf F_p(u_1,\ldots,u_n)$ has $p$-basis $\{u_1,\ldots,u_n\}$ and degree $p^n$ over its $p$-th powers. The field $\mathbf F_p(u_1,u_2,u_3,\ldots)$ in countably many variables has infinite $p$-basis $\{u_1,u_2,\ldots\}$, so $[k:k^p]$ is infinite; this is a perfectly ordinary field, and it shows that no finiteness of $p$-bases may be assumed. Finally, a separable algebraic extension $k'/k$ has the property that a $p$-basis of $k$ remains a $p$-basis of $k'$; we shall not need this, but it explains why the residue fields occurring in arithmetic — finitely generated fields and their separable extensions — always have finite $p$-bases even when they are far from perfect.

### 13.4 Coefficient fields in equal characteristic $p$

We can now construct coefficient fields in the remaining equal-characteristic case. Let $(A,\mathfrak m)$ be a local ring, complete and separated for its $\mathfrak m$-adic topology, with $pA=0$; equivalently, $A$ contains $\mathbf F_p$ and its residue field $k$ has characteristic $p$.

The strategy is the one the previous section was built for. A coefficient field is the same thing as a ring homomorphism $\phi:k\to A$ splitting the reduction $A\to k$: given such a $\phi$, its image is a subfield mapping isomorphically onto $k$, and conversely a coefficient field $K$ yields $\phi$ as the inverse of $K\xrightarrow{\sim}k$. Since $A=\varprojlim_nA/\mathfrak m^n$, constructing $\phi$ amounts to constructing a compatible system of splittings

$$
\phi_n:k\longrightarrow A/\mathfrak m^n,
\qquad n\geq1,
$$

of the reductions $A/\mathfrak m^n\to k$. The first one is forced: $A/\mathfrak m=k$ and $\phi_1=\operatorname{id}$. Passing from level $n$ to level $n+1$ means lifting a homomorphism across the surjection

$$
A/\mathfrak m^{n+1}\longrightarrow A/\mathfrak m^n,
\qquad
\text{kernel }\ \mathfrak m^n/\mathfrak m^{n+1},
$$

whose kernel has square zero because $\mathfrak m^{2n}\subseteq\mathfrak m^{n+1}$ for $n\geq1$. That is exactly the situation of Theorem 13.13, and its hypothesis $pR=0$ holds since $A/\mathfrak m^{n+1}$ is a quotient of $A$. So each step succeeds. Moreover Theorem 13.13 tells us precisely what the step depends on: a choice of lift, at level $n+1$, of the image of each element of a $p$-basis. Fixing lifts in $A$ once and for all makes the whole tower canonical, and this is what turns existence into a clean parametrization of _all_ coefficient fields.

**Theorem 13.14 (coefficient fields in equal characteristic $p$).** Let $(A,\mathfrak m)$ be a local ring that is complete and separated for its $\mathfrak m$-adic topology, with $pA=0$, and let $B$ be a $p$-basis of its residue field $k$. Then for every family $(a_b)_{b\in B}$ of elements of $A$ with $a_b\equiv b\pmod{\mathfrak m}$ there is a _unique_ ring homomorphism

$$
\phi:k\longrightarrow A
$$

splitting the reduction $A\to k$ and satisfying $\phi(b)=a_b$ for all $b\in B$. Its image $K=\phi(k)$ is a coefficient field of $A$, and

$$
K\longmapsto\big(\text{the unique element of }K\text{ reducing to }b\big)_{b\in B}
$$

is a bijection from the set of coefficient fields of $A$ onto the set of such families. In particular $A$ has a coefficient field.

**Proof roadmap.** Split the reduction one nilpotent layer at a time. Each layer is a square-zero extension of $\mathbf F_p$-algebras, so Theorem 13.13 lifts the splitting, uniquely once the images of the $p$-basis are pinned down; pinning them down by fixed elements of $A$ makes the levels compatible. The inverse limit of the levels is the desired homomorphism, and the same uniqueness read backwards shows that a coefficient field is recovered from the lifts it contains.

**Proof.** Write $A_n=A/\mathfrak m^n$ and let $\rho_n:A\to A_n$ and $\pi_n:A_{n+1}\to A_n$ be the reductions; so $A_1=k$ and $A=\varprojlim_nA_n$.

_Construction of the levels._ We define ring homomorphisms $\phi_n:k\to A_n$ with

$$
\pi_n\circ\phi_{n+1}=\phi_n,
\qquad
\phi_n(b)=\rho_n(a_b)\ \ (b\in B),
$$

and with $\phi_n$ splitting $A_n\to k$, by induction on $n$. For $n=1$ take $\phi_1=\operatorname{id}_k$; it splits the identity and satisfies $\phi_1(b)=b=\rho_1(a_b)$. Suppose $\phi_n$ has been constructed. Apply Theorem 13.13 with $R=A_{n+1}$, which satisfies $pR=0$, with $I=\ker\pi_n=\mathfrak m^n/\mathfrak m^{n+1}$, which satisfies $I^2=0$ because $\mathfrak m^{2n}\subseteq\mathfrak m^{n+1}$, with $\psi=\phi_n:k\to R/I=A_n$, and with the lifts $\beta_b=\rho_{n+1}(a_b)$, which indeed satisfy $\pi_n(\beta_b)=\rho_n(a_b)=\phi_n(b)=\psi(b)$. The theorem provides a unique ring homomorphism $\phi_{n+1}:k\to A_{n+1}$ with $\pi_n\circ\phi_{n+1}=\phi_n$ and $\phi_{n+1}(b)=\rho_{n+1}(a_b)$. Composing $\phi_{n+1}$ with $A_{n+1}\to k$ gives the composite of $\phi_n$ with $A_n\to k$, which is the identity by induction; so $\phi_{n+1}$ splits as required.

_Passage to the limit._ The compatibility $\pi_n\circ\phi_{n+1}=\phi_n$ says that the $\phi_n$ assemble into a ring homomorphism

$$
\phi:k\longrightarrow\varprojlim_nA_n=A,
$$

with $\rho_n\circ\phi=\phi_n$. Since $\rho_1\circ\phi=\phi_1=\operatorname{id}$, the map $\phi$ splits $A\to k$. Since $\rho_n(\phi(b))=\rho_n(a_b)$ for every $n$ and $A$ is separated, $\phi(b)=a_b$. Being a homomorphism from a field into a nonzero ring, $\phi$ is injective, so $K=\phi(k)$ is a subfield of $A$ mapping isomorphically onto $k$: a coefficient field.

_Uniqueness._ Let $\phi'$ be any splitting with $\phi'(b)=a_b$ for all $b$. Then $\rho_n\circ\phi'$ splits $A_n\to k$ and sends $b$ to $\rho_n(a_b)$. By induction on $n$ these maps coincide with the $\phi_n$: for $n=1$ both are the identity of $k$, and if $\rho_n\circ\phi'=\phi_n$ then $\rho_{n+1}\circ\phi'$ is a lift of $\phi_n$ across $\pi_n$ carrying $b$ to $\rho_{n+1}(a_b)$, hence equals $\phi_{n+1}$ by the uniqueness clause of Theorem 13.13. Therefore $\rho_n\circ\phi'=\rho_n\circ\phi$ for all $n$, and separatedness gives $\phi'=\phi$.

_The bijection._ Given a coefficient field $K$, let $\phi_K:k\to A$ be the inverse of $K\xrightarrow{\sim}k$ followed by the inclusion; it is a splitting with image $K$, and it assigns to each $b\in B$ the unique element $\phi_K(b)$ of $K$ reducing to $b$. This is the map in the statement, and it lands in the set of admissible families. It is surjective by the construction above. It is injective because two coefficient fields $K,K'$ producing the same family give splittings $\phi_K,\phi_{K'}$ that agree on $B$, hence are equal by uniqueness, hence have the same image. $\square$

Combining this with Theorem 13.7 disposes of both equal-characteristic cases at once. The following is the statement invoked whenever a complete local ring containing a field is put in coordinates.

**Theorem 13.15 (existence of coefficient fields).** Let $(A,\mathfrak m)$ be a local ring that is complete and separated for its $\mathfrak m$-adic topology and that contains a field. Then $A$ has a coefficient field: a subfield $K\subseteq A$ mapping isomorphically onto the residue field $k$. Consequently $A=K\oplus\mathfrak m$ as $K$-vector spaces, and every element of $A$ has a unique expression as a residue coefficient plus an element of $\mathfrak m$.

**Proof.** As noted in Section 13.1, a ring containing a field is of equal characteristic. If $\operatorname{char}k=0$ then Theorem 13.7 applies. If $\operatorname{char}k=p>0$ then $A$ contains $\mathbf F_p$, so $pA=0$, and Theorem 13.14 applies, using a $p$-basis of $k$ furnished by Lemma 13.10. In either case a coefficient field $K$ exists. The decomposition $A=K\oplus\mathfrak m$ holds because $K\to A/\mathfrak m$ is bijective: surjectivity gives $A=K+\mathfrak m$ and injectivity gives $K\cap\mathfrak m=0$. $\square$

No Noetherian hypothesis was used; completeness and separatedness suffice. The Noetherian condition will enter only in Section 13.7, where finitely many variables are needed to present $A$.

Theorem 13.14 also measures the failure of uniqueness exactly: coefficient fields correspond bijectively to families of lifts of a $p$-basis. Two consequences deserve to be recorded.

**Corollary 13.16 (perfect residue field).** Let $(A,\mathfrak m)$ be complete and separated local with $pA=0$ and perfect residue field $k$. Then $A$ has exactly one coefficient field, namely

$$
K=\bigcap_{n\geq0}A^{p^n},
\qquad
A^{p^n}=\{x^{p^n}:x\in A\}.
$$

**Proof.** A perfect field has empty $p$-basis by Lemma 13.10, so there is exactly one admissible family in Theorem 13.14, namely the empty one, and hence exactly one coefficient field $K=\phi(k)$.

For the description, note first that $K=\phi(k)=\phi(k^{p^n})=\phi(k)^{p^n}\subseteq A^{p^n}$ for every $n$, using perfection of $k$. Conversely let $x\in\bigcap_nA^{p^n}$ and let $\overline x\in k$ be its residue. Fix $n$ and write $x=y^{p^n}$ with $y\in A$. Then $\overline x=\overline y^{\,p^n}$, so $\phi(\overline x)=\phi(\overline y)^{p^n}$, and since $y-\phi(\overline y)\in\mathfrak m$ we get, using $pA=0$,

$$
x-\phi(\overline x)=y^{p^n}-\phi(\overline y)^{p^n}=\big(y-\phi(\overline y)\big)^{p^n}\in\mathfrak m^{p^n}.
$$

This holds for every $n$, and $\bigcap_n\mathfrak m^n=0$; hence $x=\phi(\overline x)\in K$. $\square$

**Corollary 13.17 (equicharacteristic complete DVRs are power series rings).** Let $A$ be a complete DVR with uniformizer $\pi$ and residue field $k$, and suppose $A$ contains a field. Then any coefficient field $K\subseteq A$ gives an isomorphism of topological rings

$$
K[[X]]\xrightarrow{\ \sim\ }A,
\qquad X\longmapsto\pi ,
$$

so that $A\cong k[[t]]$. Under this isomorphism the digit expansion of Section 8.2, taken with the residue representatives $S=K$, becomes the coefficient expansion of a power series, and digits multiply by the Cauchy product without carries.

**Proof.** A complete DVR is a complete Noetherian local ring, so Lemma 13.3 applies with $R_0=K$, $\sigma$ the inclusion, and $x_1=\pi$. Here $\mathfrak m_K=0$, so $J=(\pi)A=\mathfrak m$, and $A=K+\mathfrak m$ by Theorem 13.15; hence the evaluation map $\Sigma:K[[X]]\to A$ is surjective. Its kernel is a proper ideal of the DVR $K[[X]]$, hence is $0$ or $(X^n)$ for some $n\geq1$ by Section 4.3; but $\Sigma(X^n)=\pi^n\neq0$, so the kernel is $0$ and $\Sigma$ is an isomorphism. It is continuous and carries the maximal ideal onto $\mathfrak m$, so it identifies the two adic topologies. The last sentence is a restatement: the unique expansion $x=\sum_ns_n\pi^n$ with $s_n\in K$ is the image of the power series $\sum_ns_nX^n$, and multiplication in $K[[X]]$ is the Cauchy product. $\square$

This settles the point deferred in Section 8.2: in equal characteristic a coefficient field is not an accident of the examples but always available, so digit arithmetic really is power series arithmetic. In mixed characteristic no such field exists, and carries are genuinely unavoidable. The remedy there is to replace the coefficient field by a complete DVR of mixed characteristic whose residue field is $k$; constructing it is the subject of the next section.

### 13.5 Cohen rings: existence

In mixed characteristic a complete local ring $A$ contains no field, so no coefficient field can be sought. What is the right substitute? The example to imitate is $\mathbf Z_p\subseteq\mathbf Z_p[[t]]$. There the coefficients of a $t$-expansion do not form a field; they form the complete DVR $\mathbf Z_p$, in which $p$ is the uniformizer, and reducing modulo that uniformizer returns the residue field $\mathbf F_p$ of the big ring. The essential features are that the coefficient ring is _as unramified as possible_ — its maximal ideal is generated by $p$ itself, so it introduces no ramification of its own — and that it has the correct residue field.

Accordingly, let $k$ be a field of characteristic $p>0$. A **Cohen ring** for $k$ is a complete DVR $C$ whose maximal ideal is $pC$, together with an identification of its residue field $C/pC$ with $k$. Equivalently, $C$ is a complete discrete valuation ring of mixed characteristic which is _absolutely unramified_: the normalized valuation of $p$ is $1$. Since $C$ is a domain in which $p\neq0$, a Cohen ring always has characteristic zero. For $k=\mathbf F_p$ the ring $\mathbf Z_p$ is a Cohen ring, by Section 8.3.

It is convenient to allow incomplete approximations during the construction. Call a **$p$-lift** of $k$ a DVR $D$ whose maximal ideal is $pD$, together with an identification $D/pD\cong k$. A Cohen ring is exactly a complete $p$-lift, and completion costs nothing:

**Lemma 13.18 (completing a $p$-lift).** If $D$ is a $p$-lift of $k$, then its $p$-adic completion $\widehat D=\varprojlim_nD/p^nD$ is a Cohen ring for $k$, and $D\to\widehat D$ is injective with $\widehat D/p^n\widehat D\cong D/p^nD$ for all $n$.

**Proof.** This is Theorem 7.2 combined with Theorem 8.1: for a DVR with uniformizer $\pi=p$, the inverse limit of the quotients $D/(p^n)$ is the completion, it is a complete DVR with the same uniformizer and the same residue field, and $D/(p^n)\cong\widehat D/(p^n)$. Injectivity of $D\to\widehat D$ is separatedness of $D$, part of the definition of a DVR through the valuation. $\square$

So it suffices to produce a $p$-lift. The strategy is to build $k$ up from $\mathbf F_p$ one element at a time and to carry a $p$-lift along at each step. Only two kinds of steps occur, and each has a completely explicit lift.

If we adjoin a _transcendental_ element, the residue field grows from $k'$ to the rational function field $k'(x)$. On the lift side one adjoins a variable $X$ to $D$ and then localizes at the prime ideal $pD[X]$: modulo $p$ this localizes $k'[X]$ at its zero ideal, producing exactly $k'(X)$.

If we adjoin an _algebraic_ element $x$ with minimal polynomial $\overline f\in k'[X]$, we lift $\overline f$ to a monic polynomial $f$ over $D$ and form $D[X]/(f)$. Modulo $p$ this is $k'[X]/(\overline f)=k'(x)$, a field. Notice that separability plays no role: irreducibility of $\overline f$ is all that is needed for the quotient to be a field, and irreducibility of $f$ over the fraction field of $D$ was proved in Section 9.6 for any monic polynomial with irreducible reduction. This is the point at which the mixed-characteristic theory is _easier_ than one might fear: existence of a Cohen ring requires no $p$-basis at all. The $p$-basis will be indispensable in the next section, where we must compare two Cohen rings and map them into other rings.

**Lemma 13.19 (simple extensions of $p$-lifts).** Let $D$ be a $p$-lift of a field $k'$ of characteristic $p$, and let $k''=k'(x)$ be a simple extension of $k'$. Then there is a $p$-lift $D''$ of $k''$ containing $D$ as a subring, in such a way that $pD''\cap D=pD$ and the induced map $D/pD\to D''/pD''$ is the inclusion $k'\subseteq k''$.

**Proof.** _Case 1: $x$ transcendental over $k'$._ The polynomial ring $D[X]$ is a domain, and $\bigcap_np^nD[X]=\big(\bigcap_np^nD\big)[X]=0$. Since $D[X]/pD[X]=k'[X]$ is a domain, $pD[X]$ is a prime ideal; let

$$
D''=D[X]_{pD[X]}
$$

be the localization at it, a subring of the fraction field of $D[X]$ containing $D$. It is a local domain with maximal ideal $pD''$. Reduction commutes with localization, so

$$
D''/pD''=\big(k'[X]\big)_{(0)}=k'(X)\cong k'' ,
$$

the isomorphism carrying $X$ to $x$. For every nonzero $f\in D[X]$ there is a largest $n$ with $f\in p^nD[X]$, and writing $f=p^ng$ we have $g\notin pD[X]$, so $g$ is a unit of $D''$. Hence every nonzero element of $D''$ is $p^n$ times a unit, so $D''$ is a DVR with uniformizer $p$ and $\bigcap_np^nD''=0$. Finally $pD''\cap D=pD$, because an element of $D$ of valuation $0$ in $D$ remains a unit in $D''$.

_Case 2: $x$ algebraic over $k'$._ Let $\overline f\in k'[X]$ be the minimal polynomial of $x$, of degree $d$, and choose a monic $f\in D[X]$ of degree $d$ reducing to $\overline f$. Put $D''=D[X]/(f)$, a free $D$-module with basis $1,X,\ldots,X^{d-1}$. Reduction modulo $p$ gives

$$
D''/pD''=k'[X]/(\overline f)=k'(x)=k'',
$$

a field, so $pD''$ is a maximal ideal of $D''$. Freeness gives $\bigcap_np^nD''=0$, since a coordinate expression lies in $p^nD''$ exactly when all $d$ of its coordinates lie in $p^nD$.

That $D''$ is a domain follows from Section 9.6: $D$ is a DVR with fraction field $K$, and the monic polynomial $f$ has irreducible reduction, hence is irreducible over $K$. Therefore $K[X]/(f)$ is a field, and $D''\to K[X]/(f)$ is injective because it carries the $D$-basis $1,\ldots,X^{d-1}$ to a $K$-basis.

Next, every $w\in D''\setminus pD''$ is a unit. Indeed $w$ has nonzero residue in the field $k''=D''/pD''$, so $wD''+pD''=D''$; hence the $D$-module $M=D''/wD''$ satisfies $M=pM$. It is finitely generated over $D$, because $D''$ is, and $pD$ is the maximal ideal of the local ring $D$; Nakayama's lemma gives $M=0$, that is, $wD''=D''$.

Finally, for nonzero $z\in D''$ let $n$ be the largest integer with $z\in p^nD''$, which exists because $\bigcap_np^nD''=0$; then $z=p^nw$ with $w\notin pD''$, so $w$ is a unit. Thus $D''$ is local with maximal ideal $pD''$, every nonzero element is $p^n$ times a unit, and $D''$ is a DVR with uniformizer $p$, that is, a $p$-lift of $k''$. It contains $D$ as a subring, and $pD''\cap D=pD$ because an element of $D$ that is a unit in $D$ is a unit in $D''$. $\square$

**Lemma 13.20 (increasing unions of $p$-lifts).** Let $(D_\beta)_{\beta<\alpha}$ be a family of $p$-lifts of subfields $k_\beta\subseteq k$, indexed by an ordinal and increasing in the sense that $\beta\leq\gamma$ implies $D_\beta\subseteq D_\gamma$ with $pD_\gamma\cap D_\beta=pD_\beta$ and $k_\beta\subseteq k_\gamma$ compatibly. Then $D=\bigcup_\beta D_\beta$ is a $p$-lift of $k^\dagger=\bigcup_\beta k_\beta$.

**Proof.** $D$ is a domain, being a union of subrings of a common domain in a compatible way — concretely, each $D_\beta$ is a subring of $D$ and any two elements lie in a common $D_\gamma$. The condition $pD_\gamma\cap D_\beta=pD_\beta$ says that the normalized valuation $v_\beta$ of $D_\beta$ is the restriction of $v_\gamma$: for $z\in D_\beta$ nonzero, $z=p^{v_\beta(z)}u$ with $u\in D_\beta^\times$, and $u$ remains a unit of $D_\gamma$, so $v_\gamma(z)=v_\beta(z)$. Hence there is a well-defined function $v$ on $D\setminus\{0\}$ with values in $\mathbf N$, and every nonzero $z\in D$ equals $p^{v(z)}$ times a unit of $D$. So $D$ is local with maximal ideal $pD$, and $\bigcap_np^nD=0$; thus $D$ is a DVR with uniformizer $p$. Finally $pD\cap D_\beta=pD_\beta$ by the same valuation comparison, so

$$
D/pD=\varinjlim_\beta D_\beta/pD_\beta=\varinjlim_\beta k_\beta=k^\dagger . \square
$$

**Theorem 13.21 (existence of Cohen rings).** Every field $k$ of characteristic $p>0$ admits a Cohen ring: a complete DVR $C$ with maximal ideal $pC$ and residue field $k$.

**Proof roadmap.** Well-order $k$ and adjoin its elements one at a time, carrying a $p$-lift along by Lemma 13.19 at successor stages and by Lemma 13.20 at limit stages. The union at the end is a $p$-lift of $k$; complete it with Lemma 13.18.

**Proof.** Write $k=\{x_\alpha:\alpha<\lambda\}$ for some ordinal $\lambda$, using a well-ordering. We construct by transfinite recursion an increasing family of subfields $k_\alpha\subseteq k$ and $p$-lifts $D_\alpha$ of $k_\alpha$, compatible in the sense of Lemma 13.20.

Start with $k_0=\mathbf F_p$ and $D_0=\mathbf Z_{(p)}$, which is a DVR with maximal ideal $p\mathbf Z_{(p)}$ and residue field $\mathbf F_p$ by Section 4.3, hence a $p$-lift of $k_0$.

At a successor stage, suppose $k_\alpha$ and $D_\alpha$ have been constructed. Set $k_{\alpha+1}=k_\alpha(x_\alpha)\subseteq k$, a simple extension, and let $D_{\alpha+1}$ be a $p$-lift of $k_{\alpha+1}$ containing $D_\alpha$ as provided by Lemma 13.19.

At a limit stage $\alpha$, set $k_\alpha=\bigcup_{\beta<\alpha}k_\beta$ and $D_\alpha=\bigcup_{\beta<\alpha}D_\beta$, a $p$-lift by Lemma 13.20.

Since $x_\alpha\in k_{\alpha+1}$ for every $\alpha<\lambda$, we have $k_\lambda=k$, and $D_\lambda$ is a $p$-lift of $k$. Its $p$-adic completion is a Cohen ring for $k$ by Lemma 13.18. $\square$

Three examples make the construction concrete. For $k=\mathbf F_p$ the recursion never leaves $\mathbf Z_{(p)}$ and produces $\mathbf Z_p$. For a finite field $k=\mathbf F_{p^f}=\mathbf F_p(x)$ with $x$ algebraic, Case 2 of Lemma 13.19 gives $D=\mathbf Z_{(p)}[X]/(f)$ with $f$ a monic lift of the minimal polynomial, and the Cohen ring is $\mathbf Z_p[X]/(f)$; by Section 12.7 this is precisely the valuation ring of the unramified extension of $\mathbf Q_p$ of degree $f$, which is the expected answer. For $k=\mathbf F_p(u)$, Case 1 gives $D=\mathbf Z_{(p)}[X]_{(p)}$, whose $p$-adic completion

$$
C=\varprojlim_n\ \big(\mathbf Z/p^n\big)[X]_{(p)}
$$

is a Cohen ring for $\mathbf F_p(u)$. Its elements are the $p$-adically convergent series $\sum_{n\geq0}c_np^n$ with each $c_n$ chosen from a fixed set of representatives of $\mathbf F_p(u)$ in $C$; that these representatives cannot be chosen to form a subring is exactly the content of mixed characteristic.

It is equally instructive to see what is _not_ a Cohen ring. The ring $\mathbf Z_p[\zeta_p]$ of Section 12.7, generated by a primitive $p$-th root of unity, is a complete DVR with residue field $\mathbf F_p$, but its uniformizer is $\zeta_p-1$ and $p$ has valuation $p-1$. It is ramified, and therefore not absolutely unramified; a Cohen ring is the _unramified_ coefficient ring, and the point of Section 13.7 will be that ramification of $p$ inside a complete local ring should be recorded by the presentation, not by the coefficient ring.

Nothing so far shows that the Cohen ring is essentially unique, nor that it maps into an arbitrary complete local ring with residue field $k$. Both statements are needed before Cohen rings can serve as coefficient rings, and both require the $p$-basis technology of Section 13.3. That is the next section.

### 13.6 The lifting property and uniqueness of Cohen rings

A coefficient field was obtained in Section 13.4 by lifting a splitting one nilpotent layer at a time. In mixed characteristic the same plan will produce a homomorphism from a Cohen ring $C$ into a complete local ring $A$, provided we can solve the one-layer problem:

> given a surjection $R\to\bar R$ whose kernel $I$ satisfies $I^2=0$, and a homomorphism $C\to\bar R$, lift it to $C\to R$.

This property — lifting across square-zero thickenings — is what "formally smooth over $\mathbf Z_p$" means for $C$, and it is the mixed-characteristic analogue of Theorem 13.13. It is the technical heart of the chapter. Once it is available, everything else follows formally: the map $C\to A$, the uniqueness of Cohen rings, and the correct (weak) form of functoriality.

Throughout this section, $k$ is a field of characteristic $p$, $C$ is a Cohen ring for $k$, $R\to\bar R=R/I$ is a surjective ring homomorphism with $I^2=0$, and $p$ is nilpotent in $R$, say $p^M=0$. The last hypothesis is harmless for us: in the application $R=A/\mathfrak m_A^{n}$ with $p\in\mathfrak m_A$, so $p$ is nilpotent. It is also necessary for the statement to have content, since it makes every homomorphism out of $C$ factor through $C/p^MC$.

Recall that for a ring homomorphism $f:S\to T$ and a $T$-module $N$, a **derivation** $D:S\to N$ is an additive map with $D(ab)=f(a)D(b)+f(b)D(a)$; then $D(1)=0$ and $D(n)=0$ for every integer $n$. We suppress $f$ from the notation. Two facts about square-zero extensions are used repeatedly. First, if $w:S\to R$ is a ring homomorphism and $D:S\to I$ is a derivation, where $I$ carries the $S$-module structure coming from $w$, then $w+D$ is again a ring homomorphism, because the correction term $D(a)D(b)$ lies in $I^2=0$. Second, conversely, the difference of two ring homomorphisms $S\to R$ that agree modulo $I$ is a derivation $S\to I$.

We begin with uniqueness, which is short and already explains the role of the $p$-basis.

**Lemma 13.22 (rigidity of lifts).** Let $B$ be a $p$-basis of $k$ and let $\gamma_b\in C$ be lifts of the elements $b\in B$. Let $u,u':C\to R$ be ring homomorphisms with the same composite $C\to\bar R$ and with $u(\gamma_b)=u'(\gamma_b)$ for all $b\in B$. Then $u=u'$.

**Proof roadmap.** The difference is a derivation into $I$. Because $C$ is generated, modulo any power of $p$, by the $\gamma_b$ together with $p$-th powers, and because a derivation multiplies $p$-th powers by $p$, the derivation takes values in $pI$, then in $p^2I$, and so on; the values die because $p$ is nilpotent.

**Proof.** Put $\delta=u'-u$. Since $u,u'$ agree modulo $I$, $\delta$ takes values in $I$, and it is a derivation $C\to I$, the module structure being given by $u$ (equivalently by $u'$, since the two differ by $I$ and $I^2=0$).

First we record a generation statement. Fix $N\geq1$ and let $S\subseteq C/p^NC$ be the subring generated by the images of the $\gamma_b$ together with all $p$-th powers $y^p$ ($y\in C/p^NC$). Modulo $p$ the image of $S$ contains $B$ and contains $k^p$, hence equals $k^p[B]=k$ by Lemma 13.11. Therefore $S+p(C/p^NC)=C/p^NC$. Substituting this equality into itself repeatedly gives $S+p^j(C/p^NC)=C/p^NC$ for every $j$, and taking $j=N$ yields $S=C/p^NC$.

Now let $I_0\subseteq I$ be any $C$-submodule with $\delta(C)\subseteq I_0$. The set $T=\{c\in C:\delta(c)\in pI_0\}$ is a subring of $C$: it is closed under addition, and if $c,c'\in T$ then $\delta(cc')=u(c)\delta(c')+u(c')\delta(c)\in pI_0$. It contains every $\gamma_b$, because $\delta(\gamma_b)=0$. It contains every $p$-th power, because $\delta(y^p)=pu(y)^{p-1}\delta(y)\in pI_0$. Since $\delta$ kills $p^MC$ — indeed $\delta(p^Mc)=p^M\delta(c)$ and $p^MI=0$ — the containment $T\supseteq C$ may be checked modulo $p^M$, where the previous paragraph shows that the $\gamma_b$ and the $p$-th powers generate. Hence $T=C$, that is, $\delta(C)\subseteq pI_0$.

Starting from $I_0=I$ and iterating gives $\delta(C)\subseteq p^jI$ for every $j$, hence $\delta=0$ because $p^MI=0$. $\square$

For existence we present $C$ as a quotient of a ring for which lifting is trivial, and then measure the obstruction. The ring is a $p$-adically completed polynomial ring on a huge set of variables.

**Lemma 13.23 (a smooth presentation of a Cohen ring).** Let $\Lambda$ be the $p$-adic completion of the polynomial ring $\mathbf Z[T_x:x\in k]$ on one variable for each element of $k$. Then:

1. $\Lambda/p^n\Lambda\cong(\mathbf Z/p^n)[T_x:x\in k]$ for every $n\geq1$; in particular $\Lambda$ is $p$-torsion-free, $p$-adically complete and separated, and $\Lambda/p\Lambda=\mathbf F_p[T_x]$.
2. If $R$ is a ring with $p^M=0$, then a ring homomorphism $\Lambda\to R$ is the same thing as an arbitrary family $(r_x)_{x\in k}$ of elements of $R$, via $T_x\mapsto r_x$; and if $N$ is an $R$-module with $p^MN=0$, then a derivation $\Lambda\to N$ is the same thing as an arbitrary family $(n_x)_{x\in k}$ in $N$, via $T_x\mapsto n_x$.
3. Choosing for each $x\in k$ an element $c_x\in C$ reducing to $x$, the homomorphism $\pi:\Lambda\to C$ with $\pi(T_x)=c_x$ is surjective. Its kernel $J$ satisfies $J\cap p^n\Lambda=p^nJ$ for all $n$.

**Proof.** 1. Write $P=\mathbf Z[T_x]$, so $\Lambda=\varprojlim_nP/p^nP$. The map $\Lambda\to P/p^nP$ is surjective by construction. Its kernel is $p^n\Lambda$: if $\lambda=(\lambda_m)_m$ has $\lambda_n=0$, choose for each $j$ a representative of $\lambda_{n+j}$ of the form $p^n\mu_j$ with $\mu_j\in P$, which is possible because $\lambda_{n+j}$ dies in $P/p^nP$; compatibility gives $p^n(\mu_{j+1}-\mu_j)\in p^{n+j}P$, and $P$ is $p$-torsion-free, so $\mu_{j+1}\equiv\mu_j$ modulo $p^jP$. The $\mu_j$ therefore define $\mu\in\Lambda$ with $p^n\mu=\lambda$. The same $p$-torsion-freeness of $P$ shows that $\Lambda$ is $p$-torsion-free, and completeness and separatedness follow from the identification $\Lambda/p^n\Lambda=P/p^nP$.

2. A homomorphism $\Lambda\to R$ kills $p^M\Lambda$, hence factors through the polynomial ring $(\mathbf Z/p^M)[T_x]$, where it is determined by, and may be prescribed arbitrarily on, the variables. A derivation $D:\Lambda\to N$ satisfies $D(p^M\lambda)=p^MD(\lambda)=0$, so it too factors through $(\mathbf Z/p^M)[T_x]$; on a polynomial ring a derivation is $\sum_xn_x\,\partial/\partial T_x$, a finite sum on each element, with $n_x=D(T_x)$ arbitrary.

3. Let $S=\pi(\Lambda)$. Since every $x\in k$ is hit modulo $p$, we have $S+pC=C$, hence $S+p^nC=C$ for every $n$ as in the proof of Lemma 13.22. Given $c\in C$ write $c=s_0+pc_1$, then $c_1=s_1+pc_2$, and so on, with $s_i\in S$; then $c=\sum_ip^is_i$ in the complete ring $C$. Choosing $\lambda_i\in\Lambda$ with $\pi(\lambda_i)=s_i$, the series $\sum_ip^i\lambda_i$ converges in the complete ring $\Lambda$ and maps to $c$. So $\pi$ is surjective. Finally, if $p\lambda\in J$ then $p\pi(\lambda)=0$ in $C$, and $C$ is $p$-torsion-free, so $\pi(\lambda)=0$, that is, $\lambda\in J$; thus $J\cap p\Lambda=pJ$, and the general case follows by induction. $\square$

The presentation lets us convert the lifting problem into a question about the **conormal module** $J/J^2$, which is a module over $C=\Lambda/J$. A derivation $D:\Lambda\to I$ restricts to a $C$-linear map $J/J^2\to I$: indeed $D(\lambda j)=\lambda D(j)+jD(\lambda)$, and $j$ acts on $I$ through its image $0$ in $C$, so $D(\lambda j)=\lambda D(j)$, and likewise $D(J^2)=0$. By Lemma 13.23.2 the derivations into $I$ correspond to families $(i_x)$, so restriction to $J$ is the map

$$
\prod_{x\in k}I=\operatorname{Der}(\Lambda,I)\longrightarrow\operatorname{Hom}_C(J/J^2,I),
$$

which is $\operatorname{Hom}_C(-,I)$ applied to the $C$-linear map

$$
\alpha:J/J^2\longrightarrow\bigoplus_{x\in k}C\,dT_x,
\qquad
\alpha(j)=\sum_x\overline{\partial j/\partial T_x}\;dT_x .
$$

Working modulo $p^M$ makes $\alpha$ well defined, since modulo $p^M$ every element of $\Lambda$ is a polynomial and involves only finitely many variables. The lifting problem will be solved once we know that $\alpha$ is split injective after reduction modulo $p^M$. That is where the $p$-basis re-enters: modulo $p$, the splitting is exactly the formal smoothness of $k$ over $\mathbf F_p$ established in Theorem 13.13.

**Theorem 13.24 (Cohen rings lift across square-zero extensions).** Let $C$ be a Cohen ring for $k$, let $R\to\bar R=R/I$ be a surjective ring homomorphism with $I^2=0$, and suppose $p^M=0$ in $R$ for some $M$. Then every ring homomorphism $v:C\to\bar R$ lifts to a ring homomorphism $u:C\to R$.

**Proof roadmap.** Lift $v$ through the presentation to $w:\Lambda\to R$, which is free of charge. Then $w$ kills $J$ only up to an error in $I$, and this error is a $C$-linear map $J/J^2\to I$. Correcting $w$ by a derivation changes the error by an arbitrary element of the image of $\operatorname{Der}(\Lambda,I)$. So it suffices to prove that $\alpha$ becomes split injective modulo $p^M$. Modulo $p$ this splitting is produced by Theorem 13.13; a nilpotent-Neumann-series argument then lifts the splitting from level $1$ to level $M$.

**Proof.** _Step 1: reduction to a splitting._ By Lemma 13.23.2 choose $w:\Lambda\to R$ with $w(T_x)$ any lift of $v(c_x)\in\bar R$; then $w$ reduces to $v\circ\pi$ modulo $I$. For $j\in J$ we get $w(j)\in I$, and as noted above $j\mapsto -w(j)$ defines a $C$-linear map $h:J/J^2\to I$. Suppose we find a derivation $D:\Lambda\to I$ with $D|_J=h$. Then $u'=w+D$ is a ring homomorphism reducing to $v\circ\pi$ and killing $J$, so it factors as $u\circ\pi$ for a ring homomorphism $u:C\to R$, which lifts $v$. Since $p^MI=0$, the desired $D$ exists for every $h$ as soon as

$$
\alpha_M:N:=(J/J^2)/p^M(J/J^2)\longrightarrow F:=\bigoplus_{x\in k}(C/p^MC)\,dT_x
$$

admits a $C$-linear retraction.

_Step 2: the splitting modulo $p$._ Set $\Lambda_1=\Lambda/p\Lambda=\mathbf F_p[T_x]$ and let $\mathfrak q\subseteq\Lambda_1$ be the image of $J$. Since $\Lambda/(J+p\Lambda)=C/pC=k$, the ideal $\mathfrak q$ is the kernel of $\Lambda_1\to k$. Apply Theorem 13.13 to the square-zero extension $\Lambda_1/\mathfrak q^2\to\Lambda_1/\mathfrak q=k$ of $\mathbf F_p$-algebras, whose kernel $\mathfrak q/\mathfrak q^2$ has square zero: it yields a ring homomorphism $s:k\to\Lambda_1/\mathfrak q^2$ splitting the projection. Writing each $\lambda\in\Lambda_1/\mathfrak q^2$ as $s(\overline\lambda)+n_\lambda$ with $n_\lambda\in\mathfrak q/\mathfrak q^2$, the computation

$$
\lambda\mu=s(\overline\lambda)s(\overline\mu)+s(\overline\lambda)n_\mu+s(\overline\mu)n_\lambda
=s(\overline{\lambda\mu})+\overline\lambda n_\mu+\overline\mu n_\lambda
$$

shows that $\partial(\lambda)=n_\lambda$ is a derivation $\Lambda_1\to\mathfrak q/\mathfrak q^2$, and $\partial$ restricts to the identity on $\mathfrak q/\mathfrak q^2$. Since $\Lambda_1$ is a polynomial ring, $\partial$ is $\sum_x\partial(T_x)\,\partial/\partial T_x$, so it factors as $\Lambda_1\to\bigoplus_xk\,dT_x\xrightarrow{\ \overline r\ }\mathfrak q/\mathfrak q^2$. Restricting to $\mathfrak q$, we obtain $\overline r\circ\overline\alpha=\operatorname{id}$, where $\overline\alpha:\mathfrak q/\mathfrak q^2\to\bigoplus_xk\,dT_x$ is induced by partial derivatives.

_Step 3: identifying the conormal modules._ We claim the natural surjection

$$
\beta:(J/J^2)\otimes_Ck=J/(J^2+pJ)\longrightarrow\mathfrak q/\mathfrak q^2
$$

is an isomorphism. Indeed $\mathfrak q=(J+p\Lambda)/p\Lambda$ and $\mathfrak q^2=(J^2+p\Lambda)/p\Lambda$, so

$$
\mathfrak q/\mathfrak q^2=(J+p\Lambda)/(J^2+p\Lambda)=J/\big(J^2+(J\cap p\Lambda)\big)=J/(J^2+pJ),
$$

using $J\cap p\Lambda=pJ$ from Lemma 13.23.3. The composite $\overline\alpha\circ\beta$ is the reduction $\alpha_1$ of $\alpha$ modulo $p$, so $\alpha_1$ is split injective with retraction $\overline r\circ$ (the inverse of $\beta$).

_Step 4: from level $1$ to level $M$._ The module $F$ is free over $C/p^MC$ on the basis $\{dT_x\}$, so the retraction of $\alpha_1$ lifts to a $C$-linear map $r_0:F\to N$ whose reduction modulo $p$ is that retraction. Set $\phi=r_0\circ\alpha_M:N\to N$ and $\psi=\operatorname{id}-\phi$. Modulo $p$ we have $\phi=\operatorname{id}$, so $\psi(N)\subseteq pN$; consequently $\psi^2(N)\subseteq\psi(pN)=p\psi(N)\subseteq p^2N$, and inductively $\psi^M(N)\subseteq p^MN=0$. Hence $\psi$ is nilpotent, $\phi=\operatorname{id}-\psi$ is invertible with inverse $\sum_{i<M}\psi^i$, and $r=\phi^{-1}\circ r_0$ is a retraction of $\alpha_M$. By Step 1 the lift $u$ exists. $\square$

Combining Theorem 13.24 with Lemma 13.22: a lift exists, and it is uniquely determined once its values on lifts of a $p$-basis are prescribed. We turn this one-layer statement into the mapping property that the structure theorem consumes.

**Theorem 13.25 (mapping property of Cohen rings).** Let $C$ be a Cohen ring for a field $k$ of characteristic $p$. Let $(A,\mathfrak m)$ be a local ring, complete and separated for its $\mathfrak m$-adic topology, whose residue field $\ell$ has characteristic $p$. Then for every field homomorphism $\varphi:k\to\ell$ there is a local homomorphism

$$
u:C\longrightarrow A
$$

inducing $\varphi$ on residue fields. Any two such homomorphisms that agree on lifts of a $p$-basis of $k$ coincide.

**Proof roadmap.** Exactly as for coefficient fields in Section 13.4: construct compatible homomorphisms into the finite-precision quotients $A/\mathfrak m^n$, using Theorem 13.24 for each nilpotent layer, and pass to the limit. The hypothesis of Theorem 13.24 that $p$ be nilpotent is automatic because $p$ lies in $\mathfrak m$.

**Proof.** Since $\ell$ has characteristic $p$, the element $p\cdot1_A$ reduces to $0$, so $p\in\mathfrak m$. Write $A_n=A/\mathfrak m^n$, so $A_1=\ell$ and $A=\varprojlim_nA_n$.

We construct ring homomorphisms $u_n:C\to A_n$ with $u_{n+1}$ lifting $u_n$, by induction. Take $u_1$ to be $\varphi$ composed with the reduction $C\to C/pC=k$. Given $u_n$, apply Theorem 13.24 to the surjection $A_{n+1}\to A_n$, whose kernel $\mathfrak m^n/\mathfrak m^{n+1}$ has square zero because $\mathfrak m^{2n}\subseteq\mathfrak m^{n+1}$ for $n\geq1$, and in whose source $p^{n+1}=0$ because $p\in\mathfrak m$ and $\mathfrak m^{n+1}=0$ in $A_{n+1}$. This yields $u_{n+1}:C\to A_{n+1}$ lifting $u_n$.

The compatible family defines a ring homomorphism $u:C\to\varprojlim_nA_n=A$. Its composite with $A\to\ell$ is $u_1$, that is, $\varphi$ on residues. It is local: an element of $C$ outside $pC$ has nonzero residue in $k$, hence its image has residue $\varphi$ of that, which is nonzero because $\varphi$ is injective; so units go to units and $u^{-1}(\mathfrak m)=pC$.

For the last statement, let $u,u'$ be two such homomorphisms agreeing on lifts $\gamma_b$ of a $p$-basis. For each $n$ the induced maps $C\to A_n$ agree modulo $\mathfrak m^{n-1}/\mathfrak m^n$ by induction, and Lemma 13.22 applied to $A_n\to A_{n-1}$ upgrades this to equality; since $A$ is separated, $u=u'$. $\square$

Two comments on how this theorem is used. First, $u$ need not be injective. The complete local ring $A=\mathbf Z/p^2\mathbf Z$ has residue field $\mathbf F_p$ and Cohen ring $\mathbf Z_p$, and the only local homomorphism $\mathbf Z_p\to\mathbf Z/p^2\mathbf Z$ is the reduction, with kernel $p^2\mathbf Z_p$. So in mixed characteristic the right structure is not a coefficient subring but a **coefficient-ring map**: a local homomorphism $u:C\to A$ from a Cohen ring for the residue field of $A$ inducing the identity on residue fields. When $u$ happens to be injective, its image is a coefficient ring in the sense of Section 13.1. Second, the theorem applies verbatim when $\varphi$ is an isomorphism, which is the case used to put $A$ in coordinates, and when $\varphi$ is an inclusion, which is the case used to compare two complete local rings with different residue fields.

Taking $A$ to be another Cohen ring gives uniqueness.

**Theorem 13.26 (uniqueness of Cohen rings).** Let $C$ and $C'$ be Cohen rings for the same field $k$ of characteristic $p$. Then:

1. every local homomorphism $u:C\to C'$ inducing the identity on $k$ is an isomorphism;
2. such a homomorphism exists.

Hence $C$ is determined by $k$ up to isomorphism.

**Proof.** 2 is Theorem 13.25 applied with $A=C'$, which is a complete local ring with residue field $k$, and $\varphi=\operatorname{id}_k$.

For 1, note first that $u(p)=p$ and, since $u$ is local, $u(p^nC)\subseteq p^nC'$; so $u$ is continuous for the $p$-adic topologies. Surjectivity: because $u$ induces the identity on residue fields, $u(C)+pC'=C'$, and substituting repeatedly gives $u(C)+p^nC'=C'$ for every $n$. Given $c'\in C'$, write $c'=u(c_0)+pc_1'$, then $c_1'=u(c_1)+pc_2'$, and so on; the series $c=\sum_ip^ic_i$ converges in the complete ring $C$, and continuity gives

$$
u(c)=\sum_ip^iu(c_i)=c' .
$$

Injectivity: $\ker u$ is an ideal of the DVR $C$, hence is $0$ or contains $p^n$ for some $n$ by Section 4.3; but $u(p^n)=p^n\neq0$ in the domain $C'$, so $\ker u=0$. $\square$

The word "hence" in the last line of Theorem 13.26 hides an important caveat: the isomorphism is _not_ canonical, and there is in general no way to choose one naturally. The following example, which is as simple as such an example can be, shows that already the identity of $k$ is induced by more than one endomorphism of $C$.

**Example 13.27 (non-uniqueness of the isomorphism).** Let $k=\mathbf F_p(t)$ and let

$$
C=\text{the $p$-adic completion of }\ \mathbf Z_{(p)}[T]_{(p)} ,
$$

the Cohen ring for $k$ built in Section 13.5, with $T$ reducing to $t$. Consider the ring homomorphism $\mathbf Z_{(p)}[T]\to C$ sending $T$ to $T+p$. If $s\in\mathbf Z_{(p)}[T]$ does not lie in the prime ideal $(p)$, then $s(T+p)$ reduces to $\overline s(t)\neq0$ in $k$, hence is a unit of $C$; so the homomorphism extends to $\mathbf Z_{(p)}[T]_{(p)}\to C$, and then, being continuous for the $p$-adic topologies, to a local homomorphism

$$
\sigma:C\longrightarrow C,\qquad \sigma(T)=T+p .
$$

By construction $\sigma$ induces the identity on $k$, since $T$ and $T+p$ have the same residue. By Theorem 13.26 it is an automorphism. It is not the identity, because $\sigma(T)-T=p\neq0$.

Thus $C$ has at least two automorphisms over $\operatorname{id}_k$, and Theorem 13.25 correspondingly produces many maps $C\to A$ realizing a given $\varphi$: composing one with $\sigma$ gives another. Lemma 13.22 says exactly how much freedom there is — the value on a lift of each $p$-basis element may be moved — and here the single $p$-basis element $t$ has been lifted to $T$ in one case and to $T+p$ in the other. Consequently the assignment $k\mapsto C(k)$ cannot be made into a functor by any canonical choice: a field homomorphism $k\to k'$ induces many maps of Cohen rings, and there is no rule for selecting one that is compatible with composition. This is the precise sense in which imperfect residue fields behave worse than perfect ones.

**Corollary 13.28 (the perfect case).** Let $k$ be a perfect field of characteristic $p$ and $C$ a Cohen ring for $k$. Then:

1. for every complete separated local ring $A$ with residue field $\ell$ of characteristic $p$ and every $\varphi:k\to\ell$, there is exactly one local homomorphism $C\to A$ inducing $\varphi$;
2. $C$ is unique up to a unique isomorphism inducing $\operatorname{id}_k$, and $k\mapsto C$ is functorial: a field homomorphism $k\to k'$ of perfect fields induces a unique homomorphism of the corresponding Cohen rings, compatibly with composition;
3. there is a multiplicative section $\tau:k\to C$ of the reduction, the **Teichmüller lift**, characterized by $\tau(x)\in\bigcap_nC^{p^n}$-type limits: explicitly $\tau(x)=\lim_ny_n^{p^n}$ where $y_n\in C$ is any lift of $x^{p^{-n}}$.

**Proof.** 1. A perfect field has empty $p$-basis by Lemma 13.10, so the uniqueness clause of Theorem 13.25 has no hypotheses left: any two lifts agree. Existence is Theorem 13.25.

2. Uniqueness of the isomorphism follows from 1 applied with $A=C'$. Functoriality follows because the composite of the unique maps is a map inducing the composite residue map, hence _is_ the unique such map.

3. First, if $y\equiv y'\pmod{pC}$ then $y^p\equiv y'^p\pmod{p^2C}$: writing $y'=y+pz$ and expanding, the term $\binom p1y^{p-1}pz$ lies in $p^2C$ and every later term contains $p^2$. Inductively $y\equiv y'\pmod{pC}$ implies $y^{p^n}\equiv y'^{p^n}\pmod{p^{n+1}C}$, so $y_n^{p^n}$ depends only on $x$ modulo $p^{n+1}$. Since $y_{n+1}^p$ is a lift of $x^{p^{-n}}$, the same estimate gives $y_{n+1}^{p^{n+1}}\equiv y_n^{p^n}\pmod{p^{n+1}C}$, so the sequence is Cauchy and $\tau(x)=\lim_ny_n^{p^n}$ exists in the complete ring $C$. It reduces to $x$, because $y_0$ does. Multiplicativity is inherited from the products $y_n^{p^n}$ termwise, since a lift of $(xx')^{p^{-n}}$ may be taken to be the product of lifts. $\square$

The Teichmüller lift is multiplicative but never additive when $k\neq\mathbf F_p$, since an additive multiplicative section would be a ring homomorphism $k\to C$ and $C$ has characteristic zero. The classical construction of the Cohen ring of a perfect field encodes an element by the sequence of Teichmüller coordinates of its $p$-adic digits; the resulting explicit addition and multiplication formulas are the Witt vector operations. For imperfect $k$ no such canonical set of representatives exists, and Example 13.27 shows that none can exist, which is why the general Cohen ring has been constructed here by lifting rather than by a formula.

With existence, uniqueness, and the mapping property in hand, both kinds of coefficients are now available: a coefficient field in equal characteristic by Theorem 13.15, and a coefficient-ring map from a Cohen ring in mixed characteristic by Theorems 13.21 and 13.25. The structure theorem is now a short deduction.

### 13.7 The structure theorem

Everything is in place. A complete Noetherian local ring has a supply of coefficients — a coefficient field if it contains a field, a map from a Cohen ring otherwise — and its maximal ideal is finitely generated. Lemma 13.3 says that these two pieces of data are exactly what is needed to write the ring as a quotient of a formal power series ring: the coefficients supply the constants, and finitely many generators of the maximal ideal supply the variables. Every element then has a convergent expansion in those variables with coefficients from the coefficient ring, and the only thing left unspecified is which such expansions vanish.

Recall the standard terminology. A Noetherian local ring $(R,\mathfrak m_R)$ with residue field $\kappa$ is **regular** if $\dim R=\dim_\kappa\mathfrak m_R/\mathfrak m_R^2$; equivalently, by Krull's height theorem, if $\mathfrak m_R$ can be generated by $\dim R$ elements. Such a generating family is a **regular system of parameters**. We use two standard facts of dimension theory: Krull's height theorem, which gives $\dim R\leq\dim_\kappa\mathfrak m_R/\mathfrak m_R^2$ for every Noetherian local ring, and the fact that a Noetherian local ring of dimension $d$ contains elements $x_1,\ldots,x_d$ of $\mathfrak m_R$ with $R/(x_1,\ldots,x_d)$ of finite length, a **system of parameters**.

**Lemma 13.29 (power series rings over coefficients are regular).** Let $\kappa$ be a field and $C$ a Cohen ring. Then $\kappa[[X_1,\ldots,X_n]]$ is a complete regular local domain of dimension $n$, and $C[[X_1,\ldots,X_n]]$ is a complete regular local domain of dimension $n+1$.

**Proof.** Both rings are complete Noetherian local by Lemma 13.2, with maximal ideals $\mathfrak n=(X_1,\ldots,X_n)$ and $\mathfrak n=(p,X_1,\ldots,X_n)$ respectively, and both are domains, a power series ring over a domain being a domain. In the first case $\mathfrak n$ is generated by $n$ elements, so $\dim\leq n$ by Krull's height theorem, while the chain of primes

$$
0\subsetneq(X_1)\subsetneq(X_1,X_2)\subsetneq\cdots\subsetneq(X_1,\ldots,X_n)
$$

has length $n$; each ideal in the chain is prime because the quotient is again a power series ring over $\kappa$, hence a domain. So $\dim=n$. The classes of $X_1,\ldots,X_n$ span $\mathfrak n/\mathfrak n^2$, so the ring is regular.

In the second case $\mathfrak n$ is generated by $n+1$ elements and the chain $0\subsetneq(p)\subsetneq(p,X_1)\subsetneq\cdots\subsetneq(p,X_1,\ldots,X_n)$ has length $n+1$, its successive quotients being $k[[X_1,\ldots,X_n]]$, $k[[X_2,\ldots,X_n]]$, and so on, all domains. So $\dim=n+1$. For regularity we must see that $p,X_1,\ldots,X_n$ are linearly independent in $\mathfrak n/\mathfrak n^2$; since they span, it is enough to check that $\dim_k\mathfrak n/\mathfrak n^2\geq n+1$, and for this it suffices that $p\notin(p^2,pX_i,X_iX_j)=\mathfrak n^2$. If $p$ were of that form, comparing the terms of degree $0$ in the variables would give $p=p^2c$ in $C$ for some $c$, hence $1=pc$, impossible in the local ring $C$ with $p$ in its maximal ideal. $\square$

**Theorem 13.30 (Cohen structure theorem).** Let $(A,\mathfrak m)$ be a complete Noetherian local ring with residue field $k$, and let $x_1,\ldots,x_n$ generate $\mathfrak m$.

1. If $A$ contains a field, choose a coefficient field $K\subseteq A$, which exists by Theorem 13.15. Then the evaluation homomorphism
   $$
\Sigma:K[[X_1,\ldots,X_n]]\longrightarrow A,\qquad X_i\longmapsto x_i,
$$
   is surjective. In particular $A\cong k[[X_1,\ldots,X_n]]/I$ for some ideal $I$.
2. Otherwise $A$ has mixed characteristic with residue characteristic $p$. Choose a Cohen ring $C$ for $k$, which exists by Theorem 13.21, and a local homomorphism $u:C\to A$ inducing the identity on $k$, which exists by Theorem 13.25. Then the evaluation homomorphism
   $$
\Sigma:C[[X_1,\ldots,X_n]]\longrightarrow A,\qquad X_i\longmapsto x_i,
$$
   extending $u$, is surjective. In particular $A\cong C[[X_1,\ldots,X_n]]/I$ for some ideal $I$.

**Proof roadmap.** Both statements are Lemma 13.3, whose surjectivity criterion asks that the coefficients together with the chosen variables generate $A$ modulo nothing at all: one has to check that the ideal $J$ of that lemma is the whole maximal ideal and that the coefficients surject onto the residue field.

**Proof.** In case 1, apply Lemma 13.3 with $R_0=K$ and $\sigma$ the inclusion $K\subseteq A$; the ring $K$ is a complete Noetherian local ring, being a field, and $A$ is one by hypothesis. Here $\mathfrak m_K=0$, so the ideal of the lemma is $J=(x_1,\ldots,x_n)A=\mathfrak m$, and $A=K+\mathfrak m$ by Theorem 13.15. The criterion $A=\sigma(R_0)+J$ holds, so $\Sigma$ is surjective. Since $K\cong k$, the source is isomorphic to $k[[X_1,\ldots,X_n]]$.

In case 2, apply Lemma 13.3 with $R_0=C$, which is a complete Noetherian local ring by definition, and $\sigma=u$. Here $\mathfrak m_C=pC$, so

$$
J=u(pC)A+(x_1,\ldots,x_n)A=pA+\mathfrak m=\mathfrak m ,
$$

because $p\in\mathfrak m$. Moreover $u(C)+\mathfrak m=A$, since $u$ induces an isomorphism $C/pC\to k$ on residue fields. So the criterion holds and $\Sigma$ is surjective. $\square$

The theorem should be read as saying that a complete Noetherian local ring is _nothing more_ than a system of convergent power series equations over a coefficient ring. Two immediate consequences are the statements most often used.

**Corollary 13.31 (surjection from a complete regular local ring).** Every complete Noetherian local ring $A$ is a quotient of a complete regular local ring. One may take the regular ring to be $k[[X_1,\ldots,X_n]]$ if $A$ contains a field and $C[[X_1,\ldots,X_n]]$ otherwise, where $n$ is the minimal number of generators of $\mathfrak m$; its dimension is then $n$, respectively $n+1$.

**Proof.** Combine Theorem 13.30 with Lemma 13.29. $\square$

This is the form in which the structure theorem enters homological arguments: having a surjection $Q\twoheadrightarrow A$ from a complete regular local ring $Q$ lets one study $A$ through finite free resolutions over $Q$, which exist because a regular local ring has finite global dimension. Nothing about $A$ itself needs to be assumed beyond completeness and Noetherianity.

The second consequence identifies the complete regular local rings themselves. In equal characteristic they are exactly power series rings.

**Corollary 13.32 (complete regular local rings in equal characteristic).** Let $A$ be a complete regular local ring of dimension $d$ containing a field, with residue field $k$. Then

$$
A\cong k[[X_1,\ldots,X_d]] .
$$

**Proof.** Regularity gives a regular system of parameters $x_1,\ldots,x_d$ generating $\mathfrak m$. Theorem 13.30 provides a surjection $\Sigma:k[[X_1,\ldots,X_d]]\to A$; let $I$ be its kernel. Then $\dim k[[X]]/I=\dim A=d$, so there is a chain of $d+1$ distinct primes of $k[[X]]$ containing $I$, say $\mathfrak p_0\subsetneq\cdots\subsetneq\mathfrak p_d$. If $I\neq0$ then $\mathfrak p_0\neq0$, and prefixing the zero ideal — prime, since $k[[X]]$ is a domain — gives a chain of length $d+1$ in a ring of dimension $d$, which is impossible. Hence $I=0$ and $\Sigma$ is an isomorphism. $\square$

In mixed characteristic the answer depends on how $p$ sits inside the maximal ideal. Call a regular local ring $A$ of mixed characteristic **unramified** if $p\notin\mathfrak m^2$; this is the condition that $p$ can be taken as one member of a regular system of parameters, and it says that $A$ introduces no ramification of $p$ beyond what the coefficient ring already carries.

**Corollary 13.33 (complete regular local rings in mixed characteristic).** Let $A$ be a complete regular local ring of dimension $d$ and mixed characteristic, with residue field $k$, and let $C$ be a Cohen ring for $k$. Then $A$ is a quotient of $C[[X_1,\ldots,X_d]]$. If moreover $A$ is unramified, then

$$
A\cong C[[X_1,\ldots,X_{d-1}]] .
$$

**Proof.** The first assertion is Theorem 13.30 applied to a regular system of parameters $x_1,\ldots,x_d$.

Suppose $p\notin\mathfrak m^2$. Then the class of $p$ is a nonzero element of the $d$-dimensional $k$-vector space $\mathfrak m/\mathfrak m^2$; extend it to a basis by classes of elements $x_2,\ldots,x_d\in\mathfrak m$. By Nakayama's lemma, $\mathfrak m=(p,x_2,\ldots,x_d)$. Apply Lemma 13.3 with $R_0=C$, with $u:C\to A$ from Theorem 13.25, and with the variables mapping to $x_2,\ldots,x_d$: the ideal of the lemma is

$$
J=u(pC)A+(x_2,\ldots,x_d)A=pA+(x_2,\ldots,x_d)A=\mathfrak m ,
$$

and $u(C)+\mathfrak m=A$, so the evaluation map

$$
\Sigma:C[[X_2,\ldots,X_d]]\longrightarrow A
$$

is surjective. By Lemma 13.29 the source is a complete regular local domain of dimension $1+(d-1)=d$. The dimension argument of Corollary 13.32 applies verbatim: the kernel is contained in a prime that begins a chain of length $d$, so it must be zero. Hence $\Sigma$ is an isomorphism, and relabelling the variables gives the stated form. $\square$

The unramifiedness hypothesis cannot be dropped. The ring $A=\mathbf Z_p[\zeta_p]$ of Section 12.7 is a complete regular local ring — indeed a complete DVR — of dimension one and mixed characteristic, with residue field $\mathbf F_p$ and Cohen ring $\mathbf Z_p$. Here $p=(\zeta_p-1)^{p-1}\cdot(\text{unit})$ lies in $\mathfrak m^2$ as soon as $p>2$, so $A$ is ramified, and indeed $A$ is not isomorphic to $C[[X_1,\ldots,X_{d-1}]]=\mathbf Z_p$, which has a different fraction field. What Corollary 13.33 does give is a presentation $A\cong\mathbf Z_p[[X]]/(f)$ with $f$ the Eisenstein polynomial $\big((1+X)^p-1\big)/X$: the ramification has been pushed into the presenting equation, exactly where it belongs.

The structure theorem presents $A$ as a quotient of a large regular ring, with as many variables as it takes to generate $\mathfrak m$. There is a complementary statement in which the number of variables is as small as possible — equal to the dimension — at the price of replacing "quotient" by "finite extension". This is the local analogue of Noether normalization, and it is the form in which the theorem is used whenever one wants to compare $A$ with a regular ring having the _same_ fraction field up to a finite extension: for instance to prove finiteness of normalization, or to run an induction on the degree of a finite extension of complete local domains.

The mechanism is the same convergence argument that proved Lemma 13.3, with generators replaced by module generators. If the chosen parameters cut $A$ down to something of finite length, then finitely many elements of $A$ suffice to span that finite-length quotient, and everything else can be expanded in the parameters with coefficients from the coefficient ring.

**Theorem 13.34 (finiteness over a power series subring).** Let $(A,\mathfrak m)$ be a complete Noetherian local ring with residue field $k$.

1. Suppose $A$ contains a field and let $K\subseteq A$ be a coefficient field. Let $x_1,\ldots,x_s\in\mathfrak m$ be such that $A/(x_1,\ldots,x_s)A$ has finite length. Then the evaluation homomorphism
   $$
\Sigma:K[[X_1,\ldots,X_s]]\longrightarrow A,\qquad X_i\longmapsto x_i,
$$
   makes $A$ a finitely generated $K[[X_1,\ldots,X_s]]$-module.
2. Suppose $A$ has mixed characteristic, let $C$ be a Cohen ring for $k$ and $u:C\to A$ a local homomorphism inducing the identity on $k$. Let $x_1,\ldots,x_s\in\mathfrak m$ be such that $A/(p,x_1,\ldots,x_s)A$ has finite length. Then the evaluation homomorphism
   $$
\Sigma:C[[X_1,\ldots,X_s]]\longrightarrow A,\qquad X_i\longmapsto x_i,
$$
   extending $u$, makes $A$ a finitely generated $C[[X_1,\ldots,X_s]]$-module.

In both cases, if $A$ is a domain and the dimension of the power series ring equals $\dim A$, then $\Sigma$ is injective, so $A$ is a finite extension of a complete regular local domain of the same dimension.

**Proof roadmap.** Write $P$ for the power series ring, $\mathfrak n$ for its maximal ideal, and $\mathfrak a=\Sigma(\mathfrak n)A$ for the ideal cut out by the parameters. The quotient $A/\mathfrak a$ is a finite-dimensional vector space over the residue field; lift a spanning family to elements $a_1,\ldots,a_r$ of $A$. Every element of $A$ is then a $P$-combination of the $a_i$ modulo $\mathfrak a$; the error can be expanded again, one power of $\mathfrak n$ deeper each time, and completeness of $P$ sums up the resulting coefficients into honest power series.

**Proof.** Treat both cases at once. Let $P$ denote $K[[X_1,\ldots,X_s]]$ or $C[[X_1,\ldots,X_s]]$, let $\mathfrak n$ be its maximal ideal, let $R_0$ be $K$ or $C$, and let $\kappa=R_0/\mathfrak m_{R_0}$, which is $K\cong k$ in the first case and $C/pC\cong k$ in the second. Set

$$
\mathfrak a=\Sigma(\mathfrak n)A .
$$

Because $\mathfrak n$ is generated by $\mathfrak m_{R_0}$ together with $X_1,\ldots,X_s$, this ideal is $(x_1,\ldots,x_s)A$ in case 1 and $pA+(x_1,\ldots,x_s)A$ in case 2. In both cases the hypothesis says that $A/\mathfrak a$ has finite length as an $A$-module. Note $\mathfrak a\subseteq\mathfrak m$, so $\Sigma$ is local.

_Step 1: a finite spanning family._ The homomorphism $R_0\to A\to A/\mathfrak a$ kills $\mathfrak m_{R_0}$, since $\Sigma(\mathfrak m_{R_0})\subseteq\mathfrak a$; so $A/\mathfrak a$ is a vector space over $\kappa\cong k$. Its $A$-module composition factors are all isomorphic to $A/\mathfrak m=k$, and the $k$-structure on each factor agrees with the one just described, so the $\kappa$-dimension of $A/\mathfrak a$ equals its length and is finite. Choose $a_1,\ldots,a_r\in A$ whose classes span $A/\mathfrak a$ over $\kappa$, and set

$$
M=\sum_{i=1}^r\Sigma(P)\,a_i\subseteq A,
$$

the $P$-submodule of $A$ they generate. We must show $M=A$.

_Step 2: one layer._ Since $R_0\to\kappa$ is surjective, for any $a\in A$ there are $\lambda_i\in R_0$ with $a-\sum_i\Sigma(\lambda_i)a_i\in\mathfrak a$. Hence

$$
A=M+\mathfrak a .
$$

_Step 3: deeper layers._ Write $\mathfrak b_j=\Sigma(\mathfrak n^j)A$, so $\mathfrak b_0=A$ and $\mathfrak b_1=\mathfrak a$. Since $R_0$ is Noetherian, $\mathfrak n$ is generated by finitely many elements — generators of $\mathfrak m_{R_0}$ together with the $X_i$ — so $\mathfrak n^j$ is generated by the monomials of degree $j$ in them, and $\mathfrak b_j$ is generated as an ideal of $A$ by the images $\Sigma(\mu)$ of these monomials. For such a $\mu$, Step 2 gives

$$
\Sigma(\mu)A=\Sigma(\mu)M+\Sigma(\mu)\mathfrak a
\subseteq\Sigma(\mathfrak n^j)M+\Sigma(\mathfrak n^{j+1})A ,
$$

using $\Sigma(\mathfrak n^j)\Sigma(\mathfrak n)\subseteq\Sigma(\mathfrak n^{j+1})$. Summing over $\mu$,

$$
\mathfrak b_j\subseteq\Sigma(\mathfrak n^j)M+\mathfrak b_{j+1}.
$$

Moreover $\Sigma(\mathfrak n^j)M=\sum_i\Sigma(\mathfrak n^j)a_i$, because $M$ is a module over $\Sigma(P)$ and $\mathfrak n^jP=\mathfrak n^j$.

_Step 4: summation._ Let $a\in A$. Using Step 2 write $a=m_0+b_1$ with $m_0\in M$ and $b_1\in\mathfrak b_1$; note $m_0=\sum_i\Sigma(\rho_{0i})a_i$ for suitable $\rho_{0i}\in P$. Using Step 3 repeatedly, write

$$
b_j=m_j+b_{j+1},
\qquad
m_j=\sum_i\Sigma(\rho_{ji})a_i\ \text{ with }\ \rho_{ji}\in\mathfrak n^j,
\qquad b_{j+1}\in\mathfrak b_{j+1}.
$$

For each $i$ the series $\rho_i=\sum_{j\geq0}\rho_{ji}$ converges in $P$, which is complete by Lemma 13.2. The map $\Sigma$ is continuous by Lemma 13.3, so

$$
\sum_i\Sigma(\rho_i)a_i=\sum_i\sum_j\Sigma(\rho_{ji})a_i=\sum_{j\geq0}m_j .
$$

On the other hand $a-\sum_{j<n}m_j=b_n\in\mathfrak b_n\subseteq\mathfrak m^n$ for every $n$, and $A$ is separated, so $a=\sum_{j\geq0}m_j$. Therefore $a=\sum_i\Sigma(\rho_i)a_i\in M$, and $M=A$. Thus $a_1,\ldots,a_r$ generate $A$ as a $P$-module.

_Step 5: injectivity for domains._ Suppose $A$ is a domain and $\dim P=\dim A$. Since $A$ is a finite module over the subring $\Sigma(P)=P/\ker\Sigma$, it is integral over it, and dimension is preserved by an integral extension, as recalled in Section 10.5; hence $\dim P/\ker\Sigma=\dim A=\dim P$. If $\ker\Sigma$ were nonzero, then a chain of $\dim P+1$ distinct primes containing $\ker\Sigma$ could be prefixed with the prime ideal $0$ of the domain $P$, producing a chain of length $\dim P+1$ in $P$, which is impossible. So $\ker\Sigma=0$, and $P$ is a complete regular local domain of dimension $\dim A$ by Lemma 13.29. $\square$

The dimension hypothesis in the last statement is met by the natural choices. In equal characteristic, take $x_1,\ldots,x_d$ to be a system of parameters, so $s=d=\dim A$ and $\dim K[[X_1,\ldots,X_d]]=d$. In mixed characteristic, suppose $A$ is a domain of dimension $d$; then $p\neq0$, and

$$
\dim A/pA=d-1 .
$$

Indeed $\dim A/pA\geq d-1$ by Krull's principal ideal theorem, while a chain of $d+1$ distinct primes of $A$ containing $p$ could be prefixed by the prime $0$ to give a chain of length $d+1$ in $A$, which is impossible; so $\dim A/pA\leq d-1$. Choosing $x_1,\ldots,x_{d-1}$ to be a system of parameters of $A/pA$ and lifting them to $A$ makes $A/(p,x_1,\ldots,x_{d-1})A$ of finite length, and $\dim C[[X_1,\ldots,X_{d-1}]]=d$ by Lemma 13.29. So a complete Noetherian local domain of dimension $d$ is always a finite extension of a complete regular local domain of dimension $d$: of $k[[X_1,\ldots,X_d]]$ in equal characteristic, and of $C[[X_1,\ldots,X_{d-1}]]$ in mixed characteristic.

This is the precise sense in which the local rings of arithmetic geometry are governed by two model families. Up to a finite extension of local domains, a complete local domain of dimension $d$ is a power series ring in $d$ variables over a field, or a power series ring in $d-1$ variables over a Cohen ring. The finite extension carries the remaining information — ramification, singularities, inseparability — while the model ring supplies regularity, and hence finite free resolutions and a workable dimension theory, on which arguments about the extension can be based.

### 13.8 Worked examples and counterexamples

The theorems of this chapter all assert existence, never canonicity, and the examples below are chosen to show that this is not a defect of the proofs. We also compute a few structure-theorem presentations explicitly, since the content of Theorem 13.30 is easiest to appreciate when the ideal $I$ is written down.

**Coefficient fields are far from unique.** Let $k$ be a field and $A=k[[t]]$, whose obvious coefficient field is the field of constants $K_1=k$. It is not the only one. Take $k=\mathbf Q(u)$ and put

$$
K_2=\mathbf Q(u+t)\subseteq A .
$$

To see that this is a subfield, apply Lemma 13.5 with the subfield $\mathbf Q\subseteq A$, the residue element $u$, which is transcendental over $\mathbf Q$, and the lift $u+t$: every nonzero $f\in\mathbf Q[Y]$ has $f(u+t)$ of residue $f(u)\neq0$, hence a unit of $A$. The residue image of $K_2$ is $\mathbf Q(u)=k$, so $K_2$ is a coefficient field, and $K_2\neq K_1$ because $u+t\notin k$. The two coefficient fields give two different isomorphisms $k[[T]]\to A$, sending $T$ to $t$ in both cases but sending the constant $u$ to $u$ in one and to $u+t$ in the other.

In characteristic $p$ the ambiguity is measured exactly. Let $k=\mathbf F_p(u)$, whose $p$-basis is $\{u\}$ by Lemma 13.10, and again $A=k[[t]]$. By Theorem 13.14 the coefficient fields of $A$ are in bijection with the lifts of $u$, that is, with the elements

$$
u+g,\qquad g\in t\,k[[t]] .
$$

So there are as many coefficient fields as there are elements of the maximal ideal: uncountably many, with no distinguished one visible from the ring structure alone. The constants $k$ look distinguished only because we wrote $A$ as $k[[t]]$ to begin with; an abstract isomorphism of $A$ with itself can carry $k$ to any of the others.

**A maximal subfield need not be a coefficient field.** In characteristic zero, Theorem 13.7 produced coefficient fields as maximal subfields. The following shows that this route is unavailable in characteristic $p$, and therefore that the $p$-basis argument of Section 13.4 is not merely a convenience.

**Proposition 13.35.** Let $k=\mathbf F_p(u)$ and $A=k[[t]]$. Then $A$ has a maximal subfield that is not a coefficient field.

**Proof.** Set $c=u^p+t\in A$, a lift of $u^p\in k$. Since $u^p$ is transcendental over $\mathbf F_p$, Lemma 13.5 applied with the prime subfield $\mathbf F_p\subseteq A$ shows that $\mathbf F_p(c)$ is a subfield of $A$, with residue image $\mathbf F_p(u^p)$.

Now let $K\subseteq A$ be any subfield containing $c$, and suppose that some $b\in K$ has residue $u$. Write $b=u+\sum_{n\geq1}\beta_nt^n$ with $\beta_n\in k$. Frobenius on $k[[t]]$ raises each coefficient to the $p$-th power and each exponent by a factor $p$, so

$$
b^p=u^p+\sum_{n\geq1}\beta_n^pt^{np},
$$

and therefore

$$
b^p-c=-t+\sum_{n\geq1}\beta_n^pt^{np}.
$$

Every term of the sum has degree at least $p\geq2$, so $b^p-c$ has $t$-order exactly $1$. In particular $b^p-c$ is a nonzero element of the maximal ideal of $A$. But $b^p-c$ lies in the field $K$, all of whose nonzero elements are units of $A$ — a contradiction. Hence no element of $K$ has residue $u$, that is, $u\notin\overline K$.

Finally, the subfields of $A$ form a poset in which every chain has an upper bound, namely its union, so Zorn's lemma provides a maximal subfield $K$ containing $\mathbf F_p(c)$. By the previous paragraph $\overline K\neq k$, so $K$ is not a coefficient field. $\square$

Of course $A=\mathbf F_p(u)[[t]]$ does possess coefficient fields; Theorem 13.14 produces them. What fails is the characteristic-zero mechanism, and it fails precisely at the purely inseparable residue element $u$ over $\mathbf F_p(u^p)$, whose defining equation $X^p=c$ has no root in $A$: the $p$-th powers in $k[[t]]$ are the series $\sum a_n^pt^{np}$, and $u^p+t$ is not among them.

**A singular curve: the cusp.** Let $k$ be a field and let

$$
A=k[[t^2,t^3]]\subseteq k[[t]],
$$

the ring of power series with no linear term, met already in Section 4.3. It is a complete Noetherian local domain of dimension one, with maximal ideal $\mathfrak m=(t^2,t^3)$; since $\mathfrak m^2=(t^4,t^5,t^6)$, the classes of $t^2$ and $t^3$ form a basis of $\mathfrak m/\mathfrak m^2$, so $A$ is not regular. It contains the field $k$, which is a coefficient field, so Theorem 13.30 gives a surjection

$$
\Sigma:k[[X,Y]]\longrightarrow A,
\qquad X\longmapsto t^2,\quad Y\longmapsto t^3 .
$$

Its kernel contains $Y^2-X^3$. We claim it equals $(Y^2-X^3)$, so that

$$
k[[t^2,t^3]]\cong k[[X,Y]]/(Y^2-X^3).
$$

First, every $f\in k[[X,Y]]$ can be written $f=q\,(Y^2-X^3)+a(X)+b(X)Y$. Indeed, write $f=\sum_jf_j(X)Y^j$; modulo $Y^2-X^3$ one may replace $Y^j$ by $X^{3\lfloor j/2\rfloor}Y^{j\bmod2}$, and the resulting series

$$
a(X)=\sum_mf_{2m}(X)X^{3m},
\qquad
b(X)=\sum_mf_{2m+1}(X)X^{3m}
$$

converge in $k[[X]]$ because the $m$-th terms are divisible by $X^{3m}$. The difference $f-a-bY$ is the sum over $j$ of $f_j(X)\big(Y^j-X^{3\lfloor j/2\rfloor}Y^{j\bmod2}\big)$; each summand is divisible by $Y^2-X^3$, and the summands have order at least $j$ in the maximal ideal, so the quotients converge and $q$ exists.

Now suppose $f\in\ker\Sigma$. Then $a(t^2)+b(t^2)t^3=0$ in $k[[t]]$. The first term involves only even powers of $t$ and the second only odd powers, so both vanish, forcing $a=b=0$ and $f\in(Y^2-X^3)$. This is the promised presentation, and it exhibits the cusp as the simplest failure of regularity: one variable too many for the dimension, with one equation to compensate.

**Mixed characteristic without a coefficient subring.** Let $A=\mathbf Z/p^2\mathbf Z$. It is a complete local ring of dimension zero with residue field $\mathbf F_p$ and maximal ideal $\mathfrak m=pA$. It has mixed characteristic, since $p\neq0$ and $p^2=0$, and consequently contains no field: a subfield would have to contain either $\mathbf Q$, impossible in a finite ring, or $\mathbf F_p$, impossible because $p\neq0$ in $A$. Its Cohen ring is $\mathbf Z_p$, and the only local homomorphism $u:\mathbf Z_p\to A$ is the reduction, which is surjective with kernel $p^2\mathbf Z_p$. Since $\mathfrak m=u(p)A$, no variables are needed and Theorem 13.30 reads

$$
A\cong\mathbf Z_p/(p^2).
$$

This example is the reason Section 13.6 insisted on coefficient-ring _maps_: the Cohen ring sits over $A$, not inside it.

**Two mixed-characteristic regular rings.** The ring $\mathbf Z_p[[t]]$ of Section 4.3 is a complete regular local ring of dimension two with residue field $\mathbf F_p$ and maximal ideal $(p,t)$. Since $\mathfrak m^2=(p^2,pt,t^2)$ does not contain $p$, it is unramified, and Corollary 13.33 returns the tautology $A\cong C[[X]]$ with $C=\mathbf Z_p$. By contrast $\mathbf Z_p[\zeta_p]$, discussed after Corollary 13.33, is a complete regular local ring of dimension one whose maximal ideal contains $p$ in its square when $p>2$; it is ramified, is not isomorphic to its Cohen ring $\mathbf Z_p$, and appears instead as $\mathbf Z_p[[X]]/(f)$ for an Eisenstein $f$. The contrast is exactly the one drawn in Section 12.7 between unramified and totally ramified extensions, now seen from the structural side.

**Formal local coordinates.** A geometric reading is worth recording. If $R$ is a Noetherian local ring of dimension $d$ containing a field, with residue field $k$, and if $R$ is regular — the algebraic form of smoothness at the point — then its completion is regular of dimension $d$ and Corollary 13.32 gives

$$
\widehat R\cong k[[X_1,\ldots,X_d]].
$$

All regular points of the same dimension with the same residue field therefore look identical after completion, and the differences among them are invisible to the formal local ring. Singularities, by contrast, are detected: the cusp above has completion $k[[X,Y]]/(Y^2-X^3)$, which is not a power series ring because its maximal ideal needs two generators while its dimension is one. This is why formal-local methods classify singularities but not global geometry.

### 13.9 Coordinates, and what they cost

The book began by replacing an element with its order of vanishing, and the whole development has been an elaboration of what that replacement makes possible. A valuation separated magnitude from unit; its bounded elements formed a valuation ring; discreteness turned that ring into a DVR whose ideals are powers of one maximal ideal. Completion then supplied the limits that the filtration demanded, and Hensel's lemma converted the resulting analytic rigidity back into algebra by lifting factorizations. This chapter closed the circle by showing that the digit expansions of Chapter 8, which looked like an artefact of choosing residue representatives, are in fact the intrinsic coordinates of a complete local ring.

The conclusion has two halves, corresponding to the two ways a complete local ring can relate to its residue characteristic. If the ring contains a field, it contains a copy of its whole residue field: a coefficient field, produced by lifting maximal subfields in characteristic zero and by lifting a $p$-basis through the layers $A/\mathfrak m^n$ in characteristic $p$. If it does not, there is no field inside at all, and the substitute is a map from outside — from a Cohen ring, the unique-up-to-isomorphism complete discrete valuation ring with uniformizer $p$ and the correct residue field. In both cases the coefficients, together with finitely many generators of the maximal ideal, present the ring:

$$
A\cong k[[X_1,\ldots,X_n]]/I
\qquad\text{or}\qquad
A\cong C[[X_1,\ldots,X_n]]/I .
$$

Every complete Noetherian local ring is therefore a quotient of a complete regular local ring, and, if it is a domain, a finite extension of one of the two model rings $k[[X_1,\ldots,X_d]]$ and $C[[X_1,\ldots,X_{d-1}]]$. Regularity is characterized inside the picture: in equal characteristic the complete regular local rings are exactly the power series rings over a field, and in mixed characteristic exactly the power series rings over a Cohen ring, once $p$ is unramified; when $p$ ramifies, the ramification appears as an Eisenstein equation in the presentation rather than as a defect of the coefficient ring.

The cost of these coordinates is canonicity, and the chapter has been careful to say exactly how much. A coefficient field is a choice of lift for each element of a $p$-basis of the residue field, and Theorem 13.14 turns that sentence into a bijection; in characteristic zero the choices are hidden inside a maximal-subfield argument but are no less real. A Cohen ring is unique, but only up to an isomorphism that itself admits a nontrivial automorphism group over the identity of the residue field, as the map $T\mapsto T+p$ showed. Only when the residue field is perfect do the choices disappear: then the $p$-basis is empty, lifts are unique, Cohen rings are functorial in the residue field, and Teichmüller representatives give a canonical multiplicative section. Everything that arithmetic applications need, however, survives without perfection, because what they consume is the presentation and the finite extension, not a canonical choice of coefficients.

The structure theory also explains, retroactively, why so much of this book could be proved by successive approximation. Completeness was used three times in essentially the same way: to correct an approximate root, to sum a digit expansion, and to lift a splitting one nilpotent layer at a time. The last of these is the most flexible, and it is what produced both the coefficient field and the Cohen ring. A complete local ring is, in the end, a ring in which one may always improve an approximation and then pass to the limit — and having coordinates is nothing but the systematic exploitation of that single fact.
