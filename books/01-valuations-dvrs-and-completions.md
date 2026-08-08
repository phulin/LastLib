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
   - [From additive to multiplicative size](#25-from-additive-to-multiplicative-size)
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
    - [Several extensions and the fundamental inequality](#105-several-extensions-and-the-fundamental-inequality)
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

where $a,b$ are integers not divisible by $p$. The exponent $n$, denoted $v_p(x)$, is the $p$-adic order. Thus $v_p(xy)=v_p(x)+v_p(y)$, while

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

The point $0$ has no special status. Replacing $t$ by $t-a$ defines $\operatorname{ord}_a$ at any $a\in k$. On a smooth algebraic curve a local parameter plays the role of $t-a$. The resulting order is intrinsic even though the parameter is not: two parameters differ by a local unit.

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

Integer-valued orders are central, but the axioms do not force them. Let

$$
K=\bigcup_{n\geq1} k((t^{1/n}))
$$

inside a fixed algebraic closure of $k((t))$. A nonzero element of $k((t^{1/n}))$ has a lowest exponent in $\frac1n\mathbf Z$. These definitions agree on overlaps and give a valuation

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

This short argument is used constantly. Cancellation is possible only among terms of equal value. In a finite sum, a term whose value is strictly smaller than all others controls the sum. In particular, if a finite sum is zero, its least value must occur at least twice.

### 2.4 Equivalence and normalization

The same local geometry can be labeled by different ordered groups. Two valuations $v:K^\times\to\Gamma$ and $w:K^\times\to\Delta$ are **equivalent** if there is an order-preserving group isomorphism $\Gamma_v\to\Gamma_w$ carrying $v(x)$ to $w(x)$ for every $x$. Equivalently, they make exactly the same comparisons:

$$
v(x)\leq v(y)\quad\Longleftrightarrow\quad w(x)\leq w(y).
$$

For a discrete valuation, its value group is isomorphic to $\mathbf Z$. Choosing the unique isomorphism that sends the smallest positive value to $1$ gives the **normalized valuation**. Without normalization, $v$ and $2v$ express the same valuation ring but attach different integers to ideals. Statements involving a ramification index require normalized valuations.

A **coarsening** deliberately forgets some distinctions. If $H\subset\Gamma$ is a convex subgroup, meaning that $0\leq\gamma\leq h\in H$ implies $\gamma\in H$, the ordered quotient $\Gamma/H$ is defined and the composite valuation is a coarsening. For lexicographic $\mathbf Z^2$, quotienting by $\{0\}\times\mathbf Z$ remembers only the first coordinate. Coarsenings clarify higher-rank valuations, but discrete rank-one valuations have no nontrivial proper coarsenings.

### 2.5 From additive to multiplicative size

Analysis usually describes smallness by an absolute value: smaller numbers have smaller positive real size. A valuation describes greater divisibility by a larger value. Fix a real number $c$ with $0<c<1$. For a real-valued valuation define

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

If $|k|=q<\infty$, then $|A/(\pi^n)|=q^n$. The quotient is Artinian local, with ideals $(\overline\pi^i)$, and $\overline\pi$ has nilpotence index $n$.

### 5.3 Fractional ideals and precision

Integral ideals record zeros, but field elements may also have poles. Fractional ideals extend the filtration to negative indices and make precise how multiplication shifts a known level of accuracy.

Every nonzero fractional ideal equals $\mathfrak m^n=(\pi^n)$ for a unique $n\in\mathbf Z$. Hence their group is infinite cyclic and $K^\times/A^\times\cong\mathbf Z$. For a Dedekind domain, localization at $\mathfrak p$ projects the global ideal exponent vector onto its $\mathfrak p$-coordinate.

Multiplication shifts the filtration exactly:

$$
x\mathfrak m^n=\mathfrak m^{n+v(x)}.
$$

Thus units preserve precision, maximal-ideal elements gain it, and negative-valued elements lose digits. Ramification indices will measure this shift between two valuation filtrations.

## 6. Nonarchimedean topology and analysis

### 6.1 Balls and the strong triangle inequality

Let $K$ carry a nonarchimedean absolute value $|\cdot|$. The formula $d(x,y)=|x-y|$ is a metric when the absolute value is nontrivial. Its geometry is controlled by

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

If a sequence converges to a nonzero $x$, then eventually $|x_n|=|x|$. Indeed, once $|x_n-x|<|x|$, unequal-size rigidity applied to $x_n=x+(x_n-x)$ gives equality. Thus the absolute value is locally constant on $K^\times$ when its value group is discrete, while it remains continuous in general.

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

If $k$ is infinite, the residue classes modulo $\pi$ form an infinite disjoint open cover of $A$, so $A$ is not compact. Thus a complete discretely valued field is locally compact exactly when its residue field is finite. In that case $K=\bigcup_{n\geq0}\pi^{-n}A$ is locally compact but not compact.

The fields $\mathbf Q_p$ and finite extensions of it are locally compact. The field $k((t))$ is locally compact when $k$ is finite, but not when $k$ is infinite. All are complete; the residue field decides compactness.

### 6.7 Nondiscrete topology

For a rank-one nondiscrete valuation, choose an embedding of the value group in $\mathbf R$ and an associated absolute value. Balls now occur at a dense range of radii. The valuation ring is still the closed unit ball and its maximal ideal the open unit ball, but powers of a single ideal need not form a neighborhood basis. Indeed, the maximal ideal may satisfy $\mathfrak m^2=\mathfrak m$: every positive value can be split into two smaller positive values when the value group is divisible.

Thus the $\mathfrak m$-adic topology can be much coarser than the valuation topology outside the discrete setting. Statements identifying completion with $\varprojlim A/\mathfrak m^n$ require a discrete valuation, or more generally a chosen ideal whose powers are cofinal among valuation neighborhoods.

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

The additive valuation also extends. For a discrete valuation, any nonzero Cauchy class has representatives of eventually constant valuation, and that integer is its value. For a general rank-one valuation, extending the absolute value and taking logarithms gives a valuation whose value group may enlarge only in its closure; for the metric completion the attained nonzero norms are limits of norms from $K$.

### 7.3 Universal property

The construction matters less than its mapping property.

**Theorem 7.1 (universal property of completion).** Let $K$ be a valued field, $i:K\to\widehat K$ its completion, and $F$ a complete Hausdorff valued field. Every uniformly continuous map $f:K\to F$ extends uniquely to a continuous map $\widehat f:\widehat K\to F$. If $f$ is a field homomorphism compatible with the absolute values, then $\widehat f$ is a field homomorphism with the same compatibility.

**Proof roadmap.** Approximate a point of $\widehat K$ by a sequence from $K$, apply $f$, and take the limit in $F$. Uniform continuity makes the image sequence Cauchy and makes the result independent of choices. Density gives uniqueness. Algebraic identities pass to limits because operations are continuous.

**Proof.** For $x\in\widehat K$, choose $x_n\in K$ with $i(x_n)\to x$ and set $\widehat f(x)=\lim f(x_n)$. Uniform continuity makes $(f(x_n))$ Cauchy. If $y_n$ is another approximation, then $d(x_n,y_n)\to0$, so uniform continuity yields $d(f(x_n),f(y_n))\to0$; the limit is independent of the approximation. The construction extends $f$ and is continuous. Any continuous extension must take $x$ to the same limit, proving uniqueness. When $f$ respects sums and products, continuity lets those identities pass to the limits. $\square$

The Hausdorff condition prevents distinct candidate limits; completeness supplies existence. This theorem is the legitimate way to define functions on a completion. One defines them densely and proves uniform continuity.

### 7.4 Completion of the valuation ring

Completing the field should not obscure which elements are integral. The closed unit ball survives completion exactly, and in the discrete case every finite quotient remains unchanged.

Let $A$ be the valuation ring of a rank-one valued field $K$. The closure of $A$ in $\widehat K$ is the valuation ring $\widehat A$ of the extended valuation. One inclusion follows because $|x|\leq1$ is a closed condition. Conversely, if $x\in\widehat K$ has $|x|\leq1$, approximate it by $x_n\in K$ close enough that $|x-x_n|\leq1$; then $|x_n|\leq1$, so $x_n\in A$.

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

Digit addition generally involves carries, so this is a bijection of sets, not usually a coefficientwise ring isomorphism. In equal characteristic, if $A$ contains a coefficient field mapping isomorphically onto $k$, one may take $S=k$ and multiplication becomes formal power-series multiplication. In mixed characteristic no embedding of $\mathbf F_p$ into a characteristic-zero ring exists, so carries are unavoidable.

### 8.3 The p-adic integers and numbers

The universal mixed-characteristic example deserves a construction independent of prior intuition about limits. Its finite quotients define the ring, its digits describe the elements, and inversion of the uniformizer produces the field.

Define

$$
\mathbf Z_p=\varprojlim_n\mathbf Z/p^n\mathbf Z.
$$

It is a complete DVR with uniformizer $p$ and residue field $\mathbf F_p$. Every element has a unique expansion

$$
a_0+a_1p+a_2p^2+\cdots,\qquad 0\leq a_i<p.
$$

Its fraction field $\mathbf Q_p$ consists of expansions $\sum_{i=N}^\infty a_ip^i$ with $N\in\mathbf Z$. The valuation is the first index with nonzero digit.

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

**Theorem 9.2 (Newton form).** Let $K$ be complete for a nonarchimedean valuation $v$, let $A$ be its valuation ring, let $f\in A[X]$, and suppose $a_0\in A$ satisfies

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

The derivative is nonzero, and because $f\in A[X]$ and $a_0\in A$, we have $s\geq0$. Define $a_{n+1}=a_n+h_n$, where

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

The correction values $v(h_n)=s+q_n$ tend to infinity. For $m>n$, the strong triangle inequality gives

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

where $D(b,a_0)-f'(a_0)$ is divisible by $b-a_0$ with integral coefficient. Hence $v(D(b,a_0))=s$. If $f(b)=0$, comparison with $v(f(a_0))=r$ forces $v(b-a_0)=r-s$. If $a$ and $b$ are both roots in the ball, apply the same divided-difference argument to $f(a)-f(b)$; its second factor has value $s$ and is nonzero, so $a-b=0$. Thus $a$ is unique. $\square$

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

Completeness was used to make successive corrections converge, but the lifting property itself deserves a name. A local ring $(A,\mathfrak m)$ is **henselian** if every factorization of a monic polynomial modulo $\mathfrak m$ into coprime monic factors lifts uniquely to $A$. Equivalently, every simple root in the residue field lifts uniquely. The equivalence is obtained by viewing a simple root as a factor $X-\overline a$, and by lifting factors one at a time.

Every local ring that is complete and separated for its maximal-ideal-adic topology is henselian; the preceding proof for DVRs is the case we need. A henselian DVR need not be complete. Henselianity is algebraic, concerned with finite equations; completeness is topological, concerned with all Cauchy sequences. The henselization of a local ring adds the algebraic solutions forced by Hensel's property but is generally smaller than its completion.

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

Let $A$ be a henselian DVR with fraction field $K$. If a monic $f\in A[X]$ has irreducible reduction, then $f$ is irreducible over $K$. Indeed, a factorization of a monic polynomial over $K$ into monic factors has coefficients integral over $A$: the roots of each factor are among the roots of $f$, hence integral, and the factor coefficients are elementary symmetric functions of them. Since a DVR is integrally closed, the factors lie in $A[X]$, and their reductions would factor $\overline f$. The converse fails because reduction can acquire repeated factors. More generally, the same argument works for any integrally closed local domain; henselianity becomes relevant when one asks to lift a factorization from the residue field.

More importantly, henselianity controls extensions of the valuation. For a finite field extension $L/K$, primes of the integral closure above $\mathfrak m$ correspond to extensions of the valuation. Over a henselian field there is exactly one such prime, hence exactly one extension. Completeness implies henselianity and therefore yields uniqueness. The remaining chapters make this statement precise, include the hypotheses under which existence and finiteness hold, and quantify what happens when there are several primes.

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

The reverse inclusion also holds: an element of $L$ lying in every valuation ring above $V$ is integral over $V$. One proves the contrapositive by adjoining the element and using a maximal domination argument to find a valuation ring that excludes it. Therefore

$$
B=\bigcap_{w\mid v} W.
$$

This identity is the valuative criterion for integrality in this field-theoretic form. “Integral” means “bounded at every extension of the chosen place.” If there is a unique extension, the integral closure is itself its valuation ring, provided the extension is algebraic and the contraction is fixed.

For finite extensions of a discretely valued field, algebraic boundedness also admits a norm test in favorable situations. If $x$ is integral, its characteristic polynomial has coefficients in $A$, so its trace and norm lie in $A$. The converse from norm alone is false: cancellation among conjugate valuations can hide a pole. One must control all conjugates or all extended valuations.

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

### 10.5 Several extensions and the fundamental inequality

Let $L/K$ be finite and let $w_1,\ldots,w_g$ be the distinct extensions of a discrete valuation $v$. The single-extension inequality must now be summed without counting the same $K$-directions more than once.

**Theorem 10.2 (fundamental inequality).** For every finite field extension $L/K$ and every valuation $v$ on $K$, there are only finitely many extensions $w_i$ to $L$, and

$$
\sum_{i=1}^g e_i f_i\leq[L:K],
$$

where $e_i=[\Gamma_{w_i}:\Gamma_v]$ and $f_i=[k_{w_i}:k_v]$.

**Proof roadmap.** The cleanest general proof briefly passes to the henselization $K^h$. Henselization changes neither value group nor residue field but makes extensions stop branching. The finite $K^h$-algebra $L\otimes_KK^h$ splits into factors indexed by the extensions $w_i$. The dimension of each factor bounds $e_if_i$ by the single-extension argument, and the dimensions of all factors add to $[L:K]$.

**Proof.** Fix an algebraic closure containing $L$ and a henselization $K^h$ of $(K,v)$. The extension $K^h/K$ is separable algebraic and immediate: its value group is $\Gamma_v$ and its residue field is $k_v$. The finite algebra

$$
C=L\otimes_KK^h
$$

has $K^h$-dimension $[L:K]$. Its maximal ideals correspond to the distinct extensions of $v$ to $L$. To see the correspondence, a maximal quotient of $C$ is a finite field extension of $K^h$, whose unique valuation restricts to one on $L$; conversely, embedding the compositum $LK^h$ according to an extension $w$ produces the corresponding quotient. Purely inseparable parts cause no extra choices, because an extension across a purely inseparable field extension is automatically unique.

Write the resulting nonzero local factors as $C_i$ and let $n_i=\dim_{K^h}C_i$. If nilpotents occur in an inseparable tensor product, pass to the residue field of the local factor; its degree is at most $n_i$. Applying the single-extension inequality to that field over $K^h$ gives

$$
e_i f_i\leq n_i.
$$

The invariants are unchanged by the immediate extension $K^h/K$. Since the dimensions of the local factors, counted with their Artinian multiplicities, sum to $\dim_{K^h}C=[L:K]$, summing the displayed inequalities proves the result. It also bounds the number of factors, hence the number of extensions. $\square$

This proof locates the possible loss: some dimension of a local tensor factor may not appear in either the value group or the residue field. Under a henselian valuation there is one extension, and the quotient

$$
d(L/K)=\frac{[L:K]}{ef}
$$

is called the **defect** when the standard divisibility theorem identifies it as an integer. It is $1$ exactly when the fundamental inequality is an equality. Defect is not confined formally to inseparable extensions: separable defect extensions occur for some henselian valued fields, especially with positive residue characteristic and poorly controlled value group or residue field.

Here are the equality hypotheses used in this book.

- If the integral closure $B$ of a DVR $A$ in $L$ is finite over $A$, then $B$ is free of rank $[L:K]$ and the length calculation of Chapter 11 proves $\sum e_if_i=[L:K]$. This statement does not require $L/K$ to be separable.

- If $A$ is a Dedekind domain and $L/K$ is finite separable, its integral closure is finite over $A$, so equality holds after summing over primes. For a general DVR and a finite inseparable extension, finiteness of normalization must not be assumed without an additional hypothesis.

- If $K$ is complete and discretely valued, every finite extension is defectless. Section 12.6 will prove this directly by showing that the extended unit ball is a finite $A$-module. No perfection hypothesis on the residue field is needed for that complete discrete theorem.

- For henselian valued fields that are not complete, defect can occur. A useful sufficient theorem says that a henselian discretely valued field with perfect residue field is defectless for finite extensions. Perfectness is therefore a standard route to equality, but it is not needed once completeness and discreteness are both available.

These distinctions reconcile the general inequality with the equalities familiar from local fields. Henselianity controls the number of branches; finiteness of the integral closure or an equivalent defectlessness theorem controls whether value and residue data account for the full degree.

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

**Proof roadmap.** Completeness gives Hensel lifting, and henselianity is exactly the condition that an absolute value have one algebraic extension. We prove that equivalence in full in Theorem 12.2, independently of the norm formula. After uniqueness is established, automorphisms preserve the value automatically, and the norm formula follows by counting all conjugates, with inseparable multiplicities included. Norm equivalence then identifies the valuation topology with the complete vector-space topology just constructed.

**Proof.** The Newton proof of Chapter 9 works for every complete nonarchimedean field: its correction values tend to infinity, so completeness supplies the limit. Thus every simple residue root lifts uniquely, which is equivalent to henselianity as explained in Section 9.4. By Theorem 12.2—whose proof uses factor and idempotent lifting, not the norm formula—the valuation extends uniquely to every algebraic field. Existence can alternatively be taken from Theorem 10.1.

Let $M/K$ be a finite normal extension containing the normal closure of the maximal separable subextension of $L/K$. Uniqueness implies that every $K$-automorphism $\sigma$ of $M$ preserves the extended absolute value: $x\mapsto|\sigma x|_M$ is another extension of $|\cdot|_K$. If $L/K$ is separable, the norm is the product over its $K$-embeddings into $M$, so

$$
|N_{L/K}(x)|_K
=\prod_{\sigma:L\hookrightarrow M}|\sigma x|_M
=|x|_L^{[L:K]}.
$$

In characteristic $p>0$, let $L_s$ be the maximal separable subextension and write $[L:L_s]=p^r$. The characteristic polynomial of multiplication by $x$ has each separable conjugate repeated with the appropriate inseparable multiplicity; equivalently, after a large enough $p$-power, $x^{p^r}$ lies in a separable setting and valuation divides uniquely by $p^r$. The same product calculation, with these multiplicities, again gives

$$
|N_{L/K}(x)|_K=|x|_L^{[L:K]}.
$$

This handles inseparable extensions without inventing embeddings that do not exist. Taking the indicated root proves the norm formula.

The extended absolute value is itself a nonarchimedean $K$-norm on the vector space $L$. The finite-dimensional norm lemma therefore makes it equivalent to $\|\cdot\|_0$. Since the latter is complete, so is $L$. For infinite algebraic $L$, uniqueness on finite subextensions gives compatible values and therefore one value on their union. $\square$

The displayed norm formula is a consequence of uniqueness, not a circular proof of it. Completeness is sufficient but not necessary: henselianity is the exact algebraic hypothesis. A henselian field can fail to contain limits of arbitrary Cauchy sequences, yet finite algebraic equations still see only one extension of its valuation.

### 10.7 Concrete finite extensions

Let $K=k((t))$ and suppose $n$ is prime to $\operatorname{char}(k)$. In $L=k((u))$ with $t=u^n$, the $u$-adic valuation restricts as

$$
v_u(x)=n v_t(x),
$$

so $e=n$ and $f=1$. The extension has degree $n$ when $X^n-t$ is irreducible, as follows from the valuation: a root in a lower-degree factor would force an impossible fractional value. This is a totally ramified extension.

If $k'/k$ is finite, then $k'((t))/k((t))$ has $e=1$ and $f=[k':k]$. This is the equal-characteristic model of an unramified extension. Combining the constructions gives $k'((u))/k((t))$ with $t=u^e$, degree $ef$ under the natural separability assumptions.

For $\mathbf Q_p$, adjoining a root $\Pi$ of an Eisenstein polynomial

$$
X^n+a_{n-1}X^{n-1}+\cdots+a_0,
$$

where $p$ divides every $a_i$ and $p^2$ does not divide $a_0$, produces a totally ramified extension of degree $n$. The root has normalized extended value $1$ and $p$ has value $n$. Indeed, comparing the terms of the equation shows $n\,v(\Pi)=v(p)$; if a different term alone had least value, the sum could not vanish. Eisenstein irreducibility supplies the degree.

By contrast, if a monic polynomial over $\mathbf Z_p$ has irreducible separable reduction of degree $f$, adjoining a lift of a root gives an extension with $e=1$ and residue degree $f$, hence degree $f$. These two constructions isolate the two factors in the degree formula without yet entering the finer theory of ramification.

## 11. Integral closure and factorization

### 11.1 From one local ring to several

Passing to a field extension can turn one local direction into several. Integral closure retains all branches simultaneously; its maximal ideals label them, and localization will later isolate them.

Let $A$ be a DVR with fraction field $K$, let $L/K$ be finite, and let $B$ be the integral closure of $A$ in $L$. Even though $A$ is local, $B$ need not be. Distinct extensions of the valuation appear as distinct maximal ideals of $B$ above $\mathfrak m_A$. Localizing $B$ at each such ideal separates the branches.

This is the local version of prime factorization in number fields. If $A=R_{\mathfrak p}$ for a Dedekind domain $R$ and $S$ is the integral closure of $R$ in $L$, then

$$
B=S\otimes_R A=S_{R\setminus\mathfrak p}.
$$

All primes of $S$ not above $\mathfrak p$ disappear. The remaining maximal ideals encode exactly the ways of extending the $\mathfrak p$-adic valuation.

### 11.2 Finiteness hypotheses

To get a finite algebra rather than an uncontrolled integral closure, we need hypotheses. If $A$ is excellent—for our purposes, if $A$ is a complete DVR—or if $A$ arises as a localization of a Dedekind domain whose integral closure in finite separable extensions is finite, then $B$ is a finite $A$-module. A Dedekind domain with this finiteness property is often called Japanese in this context; rings of integers of number fields and polynomial rings in one variable over a field have it.

Finiteness is not automatic for every DVR. There exist DVRs whose integral closure in a finite extension is not finite. Any theorem using module rank, finite length, or a finite set of primes must state an appropriate finiteness assumption. In this chapter we therefore assume explicitly that $B$ is finite over $A$, except when a stronger named hypothesis supplies it.

Because $B$ is finite and torsion-free over the PID $A$, it is free. Its rank is

$$
\operatorname{rank}_A B=[L:K].
$$

Indeed, tensoring with $K$ gives $B\otimes_AK=L$: every $x\in L$ becomes integral after multiplication by a sufficiently high power of $\pi$, since the coefficients of an algebraic equation can be cleared and rescaled to make it monic.

### 11.3 Semilocal Dedekind structure

With finiteness in hand, normality and dimension force a remarkably rigid ring. The next theorem explains why its localizations are exactly the extended valuation rings and why only finitely many branches occur.

**Theorem 11.1 (finite normalization over a DVR).** Under the finiteness assumption above, $B$ is a semilocal Dedekind domain. Its maximal ideals $\mathfrak P_1,\ldots,\mathfrak P_g$ are precisely the primes above $\mathfrak m_A$, and each localization $B_{\mathfrak P_i}$ is a DVR whose valuation extends that of $A$. Every extension arises uniquely this way.

**Proof roadmap.** Integral closure gives normality, module finiteness gives Noetherianity, and integrality preserves dimension one. Semilocality follows because $B/\pi B$ is a finite-dimensional algebra over the residue field. Localizing at each nonzero prime invokes the DVR characterization. Finally, valuation rings above $A$ contract to primes of $B$ and maximality identifies them with these localizations.

**Proof.** The ring $B$ is Noetherian because it is finite over the Noetherian ring $A$, and it is integrally closed by definition. Every nonzero prime $\mathfrak P$ contracts to the nonzero prime $\mathfrak m_A$: if a nonzero $x\in\mathfrak P$ is algebraic over $K$, the constant term of a suitable integral equation, or its field norm after clearing denominators, gives a nonzero element of $A\cap\mathfrak P$. Hence $B$ has dimension one. Thus it is Dedekind.

All maximal ideals contain $\pi$, and maximal ideals of $B$ correspond to those of the finite-dimensional $k$-algebra $B/\pi B$, so there are finitely many. Each $B_{\mathfrak P_i}$ is a one-dimensional Noetherian local integrally closed domain, hence a DVR. Its contraction to $K$ is $A$: an element of $K$ integral at the extension has nonnegative original value. Thus its valuation extends $v$.

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

This proof also reveals exactly where equality comes from: finite freeness of the integral closure. Without finiteness one still has the fundamental inequality, but this length computation is unavailable and defect may intervene.

### 11.5 Splitting patterns

For a quadratic extension there are three basic defectless patterns. The prime may split: $g=2$, with $e_1=e_2=f_1=f_2=1$. It may remain inert: $g=1,e=1,f=2$. Or it may ramify: $g=1,e=2,f=1$. These names describe the allocation of degree between number of branches, residue extension, and value-group extension.

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

When $L/K$ is separable, the trace pairing embeds $B$ into its $A$-dual after multiplying by a common denominator. This provides another route to module finiteness in standard arithmetic settings and later leads to the different. We do not develop that finer invariant here, but the boundedness principle is already important: integral elements have integral symmetric functions of their conjugates.

The converse “integral trace and norm imply integral” holds for quadratic elements because their monic characteristic polynomial is $T^2-\operatorname{Tr}(x)T+N(x)$. In higher degree, trace and norm alone omit the intermediate coefficients and do not suffice.

### 11.9 Towers

Extensions are rarely studied in one step. To use intermediate fields without renormalizing incorrectly, we need to know that value-group indices and residue degrees multiply along a chosen chain of primes.

Let $K\subset L\subset M$ and choose compatible extensions of discrete valuations. Then

$$
e(M/K)=e(M/L)e(L/K),
\qquad
f(M/K)=f(M/L)f(L/K).
$$

The first is multiplicativity of indices of value groups; the second is the tower law for residue-field degrees. In a nonhenselian setting one must specify a chain of primes, since several choices can lie over the same lower prime. Summing the fundamental equality through the tree of primes recovers $[M:K]=[M:L][L:K]$ in the defectless finite setting.

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

If $K$ is already complete, then $\widehat K=K$. A finite field extension $L$ makes $L\otimes_KK=L$ a field, so the product on the right can have only one factor. This recovers uniqueness of the extended valuation. It also shows, under the defectless hypotheses, that

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

A primitive element turns the abstract tensor product into polynomial factorization. This makes branching computable: irreducible completed factors are the local fields, and their idempotents are projectors onto the branches.

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
3. The valuation has a unique extension to a fixed algebraic closure of $K$.
4. For every finite field extension $E/K$, the integral closure of $A$ in $E$ is a local ring.
5. Every finite commutative $A$-algebra is a finite product of local rings.

For a complete nonarchimedean valued field these conditions hold.

**Proof roadmap.** The bridge is an idempotent. A coprime factorization of a polynomial corresponds to a decomposition of its quotient algebra, and decompositions correspond to idempotents. Hensel lifting lifts the residue idempotents, forcing every finite algebra to split into local factors. Applied inside a field, where there are no nontrivial idempotents, this says that the integral closure is local. Maximal ideals of that closure are exactly centers of extended valuations, so locality is uniqueness. Reversing the argument recovers factor lifting.

**Proof.** First assume 1. We use the idempotent-lifting lemma for henselian local rings: if $C$ is a finite commutative $A$-algebra, reduction induces a bijection

$$
\{e\in C:e^2=e\}\longrightarrow
\{\overline e\in C/\mathfrak mC:\overline e^2=\overline e\}.
$$

Here is the factorization argument behind the lemma. The two factors $T$ and $T-1$ of $T^2-T$ are coprime. Apply henselian factor lifting after adjoining finitely many $A$-module generators of $C$ and use the determinant trick to replace their multiplication relations by monic equations. Bézout identities between the lifted factors give complementary projectors in each monogenic subalgebra; adjoining the generators one at a time gives a projector in $C$. This constructs an idempotent above $\overline e$ and is independent of the chosen generators.

The lift is unique. If $e,e'$ are two lifts, then $e(1-e')$ and $e'(1-e)$ are idempotents lying in the Jacobson radical of the finite $A$-algebra. An idempotent $z$ in the Jacobson radical is zero: $1-z$ is a unit while $z(1-z)=0$. Hence $e=ee'=e'$. Thus idempotents lift uniquely.

The Artinian ring $C/\mathfrak mC$ is a finite product of Artinian local rings. Its primitive orthogonal idempotents lift uniquely; uniqueness ensures that their lifts remain orthogonal and sum to $1$. They decompose

$$
C\cong C_1\times\cdots\times C_r.
$$

Each $C_i/\mathfrak mC_i$ is local. Every maximal ideal of the integral $A$-algebra $C_i$ lies above $\mathfrak m$, so maximal ideals correspond to those of the residue algebra; hence $C_i$ itself is local. This proves 5.

Let now $E/K$ be finite and $B$ the integral closure of $A$ in $E$. Suppose $B$ had two maximal ideals $\mathfrak P\ne\mathfrak Q$. Choose $x\in\mathfrak P\setminus\mathfrak Q$. The element $x$ is integral, so $A[x]$ is a finite $A$-algebra. It is a domain and therefore has no nontrivial idempotents; condition 5 makes it local. But the contractions of $\mathfrak P$ and $\mathfrak Q$ to $A[x]$ are distinct, since one contains $x$ and the other does not. This contradiction proves 4.

We recall the general center fact used next. If $B$ is the integral closure of a valuation ring $A$ in an algebraic extension $E$, then for every prime $\mathfrak P$ above $\mathfrak m_A$, the localization $B_{\mathfrak P}$ is a valuation ring of $E$ extending $A$. One can verify the valuation-ring criterion directly: apply a minimal equation to $z\in E^\times$, divide its coefficients by one of extremal value, and use membership outside $\mathfrak P$ to show that either $z$ or $z^{-1}$ lies in the localization. Conversely every extended valuation ring contains $B$ and is centered at such a prime; maximal domination then identifies it with $B_{\mathfrak P}$. This argument uses algebraicity, not module finiteness.

Condition 4 therefore implies 2: there is only one prime at which to localize. Conversely, if the integral closure had two maximal ideals, their localizations would give two extensions, so 2 implies 4. Condition 2 plainly implies 3 by taking $E$ to be the chosen algebraic closure, and 3 implies 2 because two extensions to a finite $E$ extend further to the algebraic closure by Theorem 10.1; their restrictions would remain distinct.

It remains to recover henselianity. Assume 2, hence 4. Let $f\in A[X]$ be monic and suppose

$$
\overline f=\overline g_0\,\overline h_0
$$

with the residue factors monic and coprime. The finite generic algebra $K[X]/(f)$ is a product of finite field extensions after grouping its irreducible factors, with possible local nilpotent factors in the inseparable case. Condition 4 says that the integral closure in each field factor is local. Their product therefore has one local factor for each generic field factor, and reduction partitions these factors according to the coprime factors $\overline g_0$ and $\overline h_0$. The corresponding complementary idempotents are integral over $A$ because they satisfy $T^2-T=0$, so they lie in the product of the integral closures. Pulling the partition back to $A[X]/(f)$ gives complementary monic factors $g,h\in A[X]$. Their degrees and reductions are prescribed, and uniqueness follows because two lifts would define the same idempotent in every field factor. Thus the coprime factorization lifts, proving 1.

We have shown all five conditions equivalent. A complete nonarchimedean field satisfies the simple-root form of Hensel's lemma by the convergent Newton argument of Chapter 9; the simple-root criterion is equivalent to the factor form, so its valuation ring is henselian. $\square$

The equivalence packages a single phenomenon in three languages. A residue factorization is a decomposition visible to polynomial algebra. An idempotent is the same decomposition visible inside a finite algebra. Several maximal ideals are the decomposition visible as several valuation branches. Henselianity says that these descriptions agree without passing to the completion.

Completeness implies condition 1 by Chapter 9. The converse is false. A henselization is henselian but usually incomplete. Thus later arguments that require only uniqueness of extension should assume henselianity, while arguments involving infinite sums, limits, or compactness genuinely need completeness.

### 12.6 The valuation ring in a finite complete extension

Uniqueness tells us which valuation to use, but arithmetic also needs its bounded ring to be finite over the base. A comparison with an ordinary coordinate lattice supplies that missing finiteness and simultaneously eliminates defect.

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

This proves simultaneously that the normalization is finite and that no defect occurs. Nothing in the lattice argument used separability or perfection of the residue field. Those hypotheses are important in other defectlessness theorems, but a finite extension of a complete discretely valued field needs neither.

Finite freeness deserves emphasis. It permits an integral basis, reduction modulo powers of the maximal ideal, determinants of multiplication, and passage between field dimension and module length. The proof also explains precisely why completeness matters: it makes the extended field topology complete and permits the unit ball to be compared with an ordinary finite lattice.

### 12.7 Unramified and totally ramified endpoints

The degree equality has two extreme allocations. Naming them isolates residue growth from value-group growth and prepares the finer study of how a general finite extension combines the two.

A finite extension of complete discretely valued fields is **unramified** at this foundational level if $e=1$ and the residue extension is separable. It is **totally ramified** if $f=1$. In a defectless complete discrete extension, unramified means $[L:K]=f$, while totally ramified means $[L:K]=e$.

When $\overline f\in k[X]$ is monic irreducible and separable, lift it monically to $f\in A[X]$. If a root generates an extension of degree $\deg f$, Hensel theory and the fundamental equality show the extension is unramified with the prescribed residue field. Conversely, finite separable residue extensions lift uniquely, up to $K$-isomorphism, to unramified extensions when the standard finiteness hypotheses hold.

Eisenstein polynomials give totally ramified extensions. If $A$ is a complete DVR, $f\in A[X]$ is Eisenstein of degree $n$, and $\Pi$ is a root, then $B=A[\Pi]$, the element $\Pi$ is a uniformizer, and $e=n$. To see the equality of rings, write each element uniquely as $\sum_{i=0}^{n-1}a_i\Pi^i$. The values $nv_K(a_i)+i$ occupy distinct congruence classes modulo $n$, so terms of least value cannot cancel. The sum is integral exactly when every $a_i\in A$. The residue field does not change because an integral polynomial in $\Pi$ reduces to its constant coefficient.

General extensions combine these behaviors, although a canonical decomposition and its detailed ramification theory require further work. The present book supplies the invariants and compatibility statements needed to begin that analysis without ambiguity.

### 12.8 A final synthesis

We began with a local question: how can one retain only the first meaningful order of a function or number? The answer was an ordered-group measurement whose multiplicative law turns factorization into addition and whose strong triangle inequality isolates cancellation. Its bounded elements form a valuation ring, characterized intrinsically by total divisibility. Discreteness then compresses the ideal theory into powers of one maximal ideal and turns that ring into a DVR.

The powers of the maximal ideal provided more than a list of ideals. Their successive quotients recorded leading coefficients, their lengths recovered valuations, and their inverse limit produced completion. Nonarchimedean analysis explained why this limit behaves so rigidly: tails are controlled by their largest term, series converge exactly when their terms vanish, and Newton corrections accelerate. Hensel's lemma converted that analytic rigidity back into algebra by lifting roots and factorizations.

Finally, a finite field extension redistributed degree among three visible phenomena: several extensions of the valuation, enlargement of the value group, and enlargement of the residue field. Integral closure assembled the branches, localization separated them, and completion displayed them as a product. Under the stated finiteness and defectlessness hypotheses, the accounting is exact:

$$
\sum_{w\mid v}e(w/v)f(w/v)=[L:K].
$$

Over a complete or merely henselian base, there is one branch. We may therefore move coherently among a valued field, its valuation ring, its residue field, finite-precision quotients, its completion, and the corresponding objects in finite extensions. That coherent local language is the foundation on which the finer arithmetic of ramification is built.
