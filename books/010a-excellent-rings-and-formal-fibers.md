# Excellent Rings and Formal Fibers

Completion is the sharpest local instrument in commutative algebra. It replaces a local ring by a
ring with coordinates, in which singularities can be inspected, branches separated, and equations
put in normal form; Book 1 built that instrument in Chapter 13. The instrument is worth nothing
unless the answers it returns are answers about the original ring. If a local ring $A$ is normal
but its completion $\widehat A$ is not, then no computation performed in $\widehat A$ says
anything about $A$. If $A$ is singular but $\widehat A$ is regular, then resolving singularities
after completion resolves nothing.

The condition that forbids these pathologies is a condition on the **formal fibers** of $A$: the
fibers of $\operatorname{Spec}\widehat{A_{\mathfrak p}}\to\operatorname{Spec}A_{\mathfrak p}$. A
ring whose formal fibers are geometrically regular is called a $G$-ring, and for such a ring
completion neither creates nor destroys regularity, normality, or reducedness. Together with two
further conditions — universal catenarity, which controls dimensions of chains, and openness of
regular loci, which lets singular points be isolated — the $G$-property makes up **excellence**.

The difficulty with excellence is not the definition but the permanence. A geometric argument
never stays inside one ring: it passes to affine charts of a blowup, to fibers of a projection,
to finite covers, to localizations at generic points of exceptional divisors. All of these are
finite-type constructions, and the whole theory is useless unless excellence survives them. That
permanence is a genuine theorem of Grothendieck, and it is the theorem this volume proves: a
finite-type algebra over a $G$-ring is a $G$-ring. Everything else — the Nagata property, the
finiteness of normalization it supplies, openness of regular loci, and the assembled excellence
package — follows from it together with the base cases delivered by Cohen's structure theory.

The proof has one hard core and a great deal of formal bookkeeping around it. The bookkeeping is
worth setting up carefully, because it is what reduces the theorem to its core. Quotients and
localizations cost nothing: the formal fibers of $A/I$ are literally among the formal fibers of
$A$, and the $G$-property is defined by a condition at every prime, so it localizes by fiat. Base
change along $A\to\widehat A$ replaces an arbitrary $G$-ring by a complete local ring at the cost
of one application of the hypothesis. What remains is the assertion that an algebra essentially of
finite type over a complete noetherian local ring is a $G$-ring, and that is where Cohen theory
enters: such a ring is a quotient of a localized polynomial algebra over $k[[x_1,\ldots,x_n]]$ or
$C[[x_1,\ldots,x_n]]$, and those coefficient rings come with coordinates. In characteristic $p$
the coordinates form a finite $p$-basis, so that the ring carries finitely many partial
derivatives and a Jacobian criterion decides regularity; in characteristic zero the residue fields
are finitely generated over the fraction field of the coefficient ring, and a count of
differentials does the same work. Chapter 5 develops the classical alternative — formal smoothness,
the calculus of lifting homomorphisms across square-zero extensions — which explains why this base
case is the only difficulty, and which supplies Cohen's theorem that separable field extensions
lift.

Two preliminary chapters make the rest possible. Chapter 2 proves Serre's homological
characterization of regular local rings, which is not available in the earlier volumes and which
is needed for two facts used constantly here: that localizations of regular rings are regular, and
that regularity descends along faithfully flat maps. Chapter 3 develops geometric regularity over
a field, where separability and $p$-bases decide everything, and proves that geometric regularity
survives arbitrary field extensions. The remaining chapters build the permanence theory, the
openness of regular loci, the Nagata property, and finally the excellence package in the exact
form that the construction of regular models of arithmetic curves consumes.

## Contents

1. [What excellence has to prove](#1-what-excellence-has-to-prove)
   - [Three conditions, and the one that resists](#11-three-conditions-and-the-one-that-resists)
   - [Standing conventions](#12-standing-conventions)
   - [The shape of the argument](#13-the-shape-of-the-argument)
2. [Regularity, resolutions, and flat maps](#2-regularity-resolutions-and-flat-maps)
   - [Minimal free resolutions and projective dimension](#21-minimal-free-resolutions-and-projective-dimension)
   - [Serre's homological criterion](#22-serres-homological-criterion)
   - [Flat local homomorphisms](#23-flat-local-homomorphisms)
3. [Geometric regularity over a field](#3-geometric-regularity-over-a-field)
   - [Separable field extensions](#31-separable-field-extensions)
   - [Geometrically regular algebras](#32-geometrically-regular-algebras)
   - [Test extensions and base change](#33-test-extensions-and-base-change)
4. [Regular homomorphisms and G-rings](#4-regular-homomorphisms-and-g-rings)
   - [Regular homomorphisms](#41-regular-homomorphisms)
   - [Composition, base change, and descent](#42-composition-base-change-and-descent)
   - [G-rings and their formal permanence](#43-g-rings-and-their-formal-permanence)
5. [Formal smoothness](#5-formal-smoothness)
   - [The lifting problem in the adic category](#51-the-lifting-problem-in-the-adic-category)
   - [Differentials and the relative criterion](#52-differentials-and-the-relative-criterion)
   - [Grothendieck's criterion](#53-grothendiecks-criterion)
   - [Separable extensions are formally smooth](#54-separable-extensions-are-formally-smooth)
6. [Complete local rings and their finite-type algebras](#6-complete-local-rings-and-their-finite-type-algebras)
   - [Complete local rings are G-rings](#61-complete-local-rings-are-g-rings)
   - [Algebras essentially of finite type over a field](#62-algebras-essentially-of-finite-type-over-a-field)
   - [Base change to the completion, and what remains](#63-base-change-to-the-completion-and-what-remains)
   - [Reduction to the closed-point case](#64-reduction-to-the-closed-point-case)
   - [The closed-point case in equal characteristic p](#65-the-closed-point-case-in-equal-characteristic-p)
   - [The remaining cases, and the theorem](#66-the-remaining-cases-and-the-theorem)
7. [The permanence theorems](#7-the-permanence-theorems)
   - [Testing the G-property at maximal ideals](#71-testing-the-g-property-at-maximal-ideals)
   - [Finite-type algebras over a G-ring](#72-finite-type-algebras-over-a-g-ring)
   - [The bases that occur in arithmetic](#73-the-bases-that-occur-in-arithmetic)
8. [Openness of regular loci](#8-openness-of-regular-loci)
   - [Nagata's criterion](#81-nagatas-criterion)
   - [From the G-property to openness](#82-from-the-g-property-to-openness)
   - [Quasi-excellent rings](#83-quasi-excellent-rings)
9. [Nagata rings](#9-nagata-rings)
   - [Finiteness of normalization](#91-finiteness-of-normalization)
   - [Quasi-excellent rings are universally Japanese](#92-quasi-excellent-rings-are-universally-japanese)
10. [Excellence assembled](#10-excellence-assembled)
    - [Universal catenarity](#101-universal-catenarity)
    - [The definition and the excellent bases](#102-the-definition-and-the-excellent-bases)
    - [The package for models of arithmetic curves](#103-the-package-for-models-of-arithmetic-curves)
    - [What is not proved here](#104-what-is-not-proved-here)
    - [Conclusion](#105-conclusion)

## 1. What excellence has to prove

### 1.1 Three conditions, and the one that resists

Let $(A,\mathfrak m)$ be a noetherian local ring and $\widehat A$ its $\mathfrak m$-adic
completion. The map $A\to\widehat A$ is faithfully flat, so it loses no information in the crude
sense: an ideal of $A$ is recovered from its extension, a module is zero if its completion is.
What can be lost is _local structure_. The map $\operatorname{Spec}\widehat A\to\operatorname{Spec}A$
is surjective but far from injective, and the local rings of $\widehat A$ at primes lying over a
fixed prime $\mathfrak q$ of $A$ are new rings, about which nothing is known a priori. They are
the local rings of the **formal fiber**.

**Definition 1.1.** Let $A$ be a noetherian ring and $\mathfrak p\in\operatorname{Spec}A$. The
**formal fibers of $A$ at $\mathfrak p$** are the fibers of
$\operatorname{Spec}\widehat{A_{\mathfrak p}}\to\operatorname{Spec}A_{\mathfrak p}$, that is, the
rings

$$
\widehat{A_{\mathfrak p}}\otimes_{A_{\mathfrak p}}\kappa(\mathfrak q),
\qquad\mathfrak q\subseteq\mathfrak p,
$$

where $\kappa(\mathfrak q)=\operatorname{Frac}(A/\mathfrak q)$ is the residue field at
$\mathfrak q$. When every such ring is _geometrically regular_ over $\kappa(\mathfrak q)$ — a
notion made precise in Chapter 3, which for a perfect residue field means simply that the ring is
regular — we say that $A$ has geometrically regular formal fibers, and call $A$ a **$G$-ring**.

Why this is the right condition is best seen from the failure it forbids. Consider the local ring
$A=k[x,y]_{(x,y)}/(y^2-x^2(x+1))$ of a nodal plane cubic at its singular point, $\operatorname{char}k\neq2$.
It is a domain, because $x+1$ is not a square in $k(x)$, so $y^2-x^2(x+1)$ is irreducible. In
$\widehat A=k[[x,y]]/(y^2-x^2(x+1))$ the unit $x+1$ acquires a square root $u$ with $u^2=x+1$, by
Hensel's lemma or by the binomial series, and

$$
y^2-x^2(x+1)=(y-xu)(y+xu),
$$

so $\widehat A$ is not a domain: completion has separated the two branches of the node. This is
not a defect. It is the entire reason completion is useful, and it is invisible to the formal
fiber, which asks only about _regularity_, not about irreducibility. What excellence does forbid
is the situation where $A$ is normal and $\widehat A$ is not reduced, or where $A$ is singular and
$\widehat A$ is regular; in either case a computation performed after completion would be a
computation about a different ring. Chapter 4 proves that for a $G$-ring neither can happen.

Two further conditions accompany the $G$-property. A ring is **catenary** when any two saturated
chains of primes between the same two primes have the same length, and **universally catenary**
when every finite-type algebra over it is catenary; this is what makes dimension counts on charts
of a blowup consistent. A ring satisfies **$J_2$** when the regular locus of every finite-type
algebra over it is open; this is what allows a singular locus to be treated as a closed subscheme
and resolved. A noetherian ring that is universally catenary, a $G$-ring, and $J_2$ is called
**excellent**.

The definition is not the difficulty. Universal catenarity and $J_2$ are quantified over all
finite-type algebras from the start, so they propagate to finite-type algebras by their own
definitions, and they are known for the classical bases: a field, a complete noetherian local
ring, a Dedekind domain of characteristic zero. For the $G$-property no such bookkeeping is
available: the definition speaks about $A$ alone, and the statement

$$
A\ \text{a }G\text{-ring}\ \Longrightarrow\ A[x_1,\ldots,x_n]\ \text{a }G\text{-ring}
\tag{1.1}
$$

is a theorem with genuine content, due to Grothendieck. It is the theorem this volume exists to
prove. Without it, every finiteness statement about normalization on a finite-type scheme, and
every comparison of a local ring on such a scheme with its completion, has to be carried as a
hypothesis on the base rather than deduced; with it, the entire package descends from the four
classical bases to everything built from them.

The route to $(1.1)$ also delivers the second permanence theorem that the geometry needs. A
noetherian domain is **Japanese** when its integral closure in every finite extension of its
fraction field is a finite module, and a noetherian ring is **Nagata** when all of its prime
quotients are Japanese. This is precisely the condition making normalization of a scheme a finite
morphism. The Nagata property is not stable under finite-type extension for any elementary
reason, and the classical route to its stability runs through excellence: a $G$-ring which is
$J_2$ is universally Japanese, because the $G$-property forces local rings of finite-type
algebras to have reduced completions, and reduced completions force finite normalization.
Chapter 9 carries this out.

### 1.2 Standing conventions

All rings are commutative with identity. From Chapter 2 onward every ring is noetherian unless
the contrary is stated explicitly; the words "local ring" always include the noetherian
hypothesis, and $(A,\mathfrak m,k)$ denotes a noetherian local ring with maximal ideal
$\mathfrak m$ and residue field $k=A/\mathfrak m$. For a local ring $A$ the symbol $\widehat A$
is the $\mathfrak m$-adic completion, which is again noetherian local with maximal ideal
$\mathfrak m\widehat A$ and the same residue field, and which is faithfully flat over $A$ and
satisfies $\widehat A/I\widehat A=\widehat{A/I}$ for every ideal $I$. For a prime $\mathfrak p$ of
a ring $A$ we write $\kappa(\mathfrak p)=A_{\mathfrak p}/\mathfrak pA_{\mathfrak p}$, and
$\widehat{A_{\mathfrak p}}$ always means the completion of the _local ring_ $A_{\mathfrak p}$ at
its maximal ideal.

A ring homomorphism $A\to B$ is **essentially of finite type** if $B$ is a localization
$S^{-1}C$ of a finite-type $A$-algebra $C$. All the constructions of this book — passing to a
chart, to a local ring at a point, to a fiber, to a quotient — stay inside this class, and it is
closed under composition, so it is the natural class in which to state permanence.

We call a noetherian ring **regular** when all its localizations at prime ideals are regular local
rings. Corollary 2.10 shows that it is enough to test maximal ideals, and that the class of regular
rings is stable under localization; before that corollary is available we test all primes.

The following standard local algebra is used freely. Krull's height theorem and the theory of
systems of parameters; Nakayama's lemma and prime avoidance; the Artin–Rees lemma and the Krull
intersection theorem; associated primes and primary decomposition for finite modules; the
elementary theory of flatness, including faithful flatness, going-down for flat maps, and the
local criterion of flatness; the fact that a regular local ring is a domain; Noether normalization
and Grothendieck's generic freeness lemma; the elementary theory of Cohen–Macaulay local rings,
including the fact that an ideal of height $h$ contains a regular sequence of that length and that
quotients by regular sequences remain Cohen–Macaulay and equidimensional; the module of Kähler
differentials
$\Omega_{B/A}$ together with the two fundamental exact sequences and its behaviour under
localization and base change; Serre's criterion that a noetherian ring is normal exactly when it
satisfies $R_1$ and $S_2$; and the functor $\operatorname{Tor}$ with its balancing property and
long exact sequences. Book 1, Chapter 13, supplies everything about complete local rings that we
need, and is cited by number where used.

One standard result is _not_ assumed, because the earlier volumes of this library do not develop
it: the homological characterization of regular local rings. Chapter 2 proves it in full. It is
needed twice, in ways that no elementary argument replaces — to know that a localization of a
regular local ring is regular, and to descend regularity along a faithfully flat map — and both
facts are used constantly from Chapter 4 onward.

### 1.2A Two Serre criteria

The declaration above lists two criteria of Serre among the standing tools. Because they carry
weight from Chapter 3 onward, they are recorded here with proofs rather than as declarations.
Throughout, $A$ is noetherian. Recall that $A$ satisfies
$S_1$ when $\operatorname{depth}A_{\mathfrak p}\geq\min(1,\dim A_{\mathfrak p})$ for every
prime $\mathfrak p$, and $R_0$ when $A_{\mathfrak p}$ is regular for every minimal prime
$\mathfrak p$ (equivalently, a field).

**Lemma 1.2A.1.** $S_1$ holds if and only if every associated prime of $A$ is minimal.

_Proof._ If $\mathfrak p\in\operatorname{Ass}(A)$ then $\mathfrak p A_{\mathfrak p}$ is
associated to $A_{\mathfrak p}$, so $\operatorname{depth}A_{\mathfrak p}=0$; if moreover
$\dim A_{\mathfrak p}\geq1$ this violates $S_1$, so $\mathfrak p$ is minimal. Conversely,
assume all associated primes are minimal and let $\mathfrak p$ be a prime with
$\dim A_{\mathfrak p}\geq1$. The associated primes of $A_{\mathfrak p}$ are the extensions
$\mathfrak q A_{\mathfrak p}$ of the associated primes $\mathfrak q\subseteq\mathfrak p$ of
$A$; each such $\mathfrak q$ is minimal, hence distinct from $\mathfrak p$, so
$\mathfrak p A_{\mathfrak p}$ is not associated and $\operatorname{depth}A_{\mathfrak p}\geq1$.
$\square$

**Lemma 1.2A.2.** Let $x\in A$ and let
$\mathcal F=\{\operatorname{Ann}(u):0\neq u,\ xu=0\}$ be nonempty. Every maximal member of
$\mathcal F$ is a prime ideal belonging to $\operatorname{Ass}(A)$.

_Proof._ Let $P=\operatorname{Ann}(z)$ be maximal in $\mathcal F$, with $z\neq0$ and $xz=0$.
If $ab\in P$ and $a\notin P$, then $bz\neq0$ and $x(bz)=0$, so
$\operatorname{Ann}(bz)\in\mathcal F$; it contains $P$ together with $b$, hence equals $P$
by maximality, whence $b\in P$. Thus $P$ is prime, and a prime that is the annihilator of an
element belongs to $\operatorname{Ass}(A)$. $\square$

**Proposition 1.2A.3 (Serre).** If $A$ satisfies $R_0$ and $S_1$, then $A$ is reduced.

_Proof._ Suppose $x\neq0$ is nilpotent and choose $n\geq1$ maximal with $y=x^n\neq0$; then
$xy=0$, so the family $\mathcal F$ of Lemma 1.2A.2 is nonempty. Take a maximal member
$P=\operatorname{Ann}(z)$ of $\mathcal F$: by Lemmas 1.2A.1 and 1.2A.2, $P$ is a minimal
prime. By $R_0$, $A_P$ is a field, so $PA_P=0$; since $x\in P$ (as $xz=0$), there exists
$s\notin P$ with $sx=0$. Then $sz\neq0$ (its annihilator would contain $s$ outside $P$,
contradicting $\operatorname{Ann}(z)=P$), while $x(sz)=0$ and
$\operatorname{Ann}(sz)\supseteq P+\mathbf Z s$ strictly contain $P$, contradicting
contradicting maximality of $P$ inside $\mathcal F$. Hence no nonzero nilpotent exists. $\square$

### 1.2B Serre's normality criterion

The declaration of Section 1.2 lists Serre's normality criterion among the standing tools; like
the two criteria of Section 1.2A, it is recorded here with a proof of the direction that carries
the weight. A noetherian ring $A$ is **normal** when $A_{\mathfrak p}$ is an integrally closed
domain for every prime $\mathfrak p$. Recall that $A$ satisfies $R_1$ when $A_{\mathfrak p}$ is
regular for every prime with $\operatorname{ht}\mathfrak p\leq1$, and $S_2$ when
$\operatorname{depth}A_{\mathfrak p}\geq\min(2,\dim A_{\mathfrak p})$ for every prime
$\mathfrak p$.

**Lemma 1.2B.1.** Let $(V,\mathfrak n)$ be a one-dimensional regular local ring. Then $V$ is a
domain and there is a discrete valuation $v$ of $K=\operatorname{Frac}(V)$ whose valuation ring
is $V$. In particular $V$ is a discrete valuation ring in the sense of Book 1, Theorem 4.1, and
is integrally closed.

_Proof._ Regularity gives $\dim_k\mathfrak n/\mathfrak n^2=\dim V=1$, so $\mathfrak n=(t)$ for
some $t\neq0$: were $t=0$ the ring would be a field, of dimension zero. Krull's intersection
theorem gives $\bigcap_k\mathfrak n^k=0$, so for every $0\neq a\in V$ the set of integers
$k\geq0$ with $a\in\mathfrak n^k$ has a largest element — it contains $0$ but not all $k$ — and
then $a=t^Ku$ with $u\notin\mathfrak n$, that is, with $u$ a unit. If $ab=0$ with $a,b\neq0$,
say $a=t^ju$ and $b=t^kv$ with units $u,v$, then multiplying $t^{j+k}uv=0$ by the inverse of
$uv$ gives $t^{j+k}=0$, hence $t=0$, a contradiction; so $V$ is a domain. Every
$x\in K^\times$ now has a unique expression $x=t^nu$ with $n\in\mathbf Z$ and $u$ a unit: write
$x=a/b$ and combine the expressions found for $a$ and $b$. Setting $v(x)=n$ gives
$v(xy)=v(x)+v(y)$ by uniqueness and $v(x+y)\geq\min\big(v(x),v(y)\big)$: if $v(x)<v(y)$ then
$x+y=t^{v(x)}\big(u+t^{\,v(y)-v(x)}\,v'\big)$ and the parenthesis lies outside $\mathfrak n$
because its first summand is a unit. Since $v(t)=1$ the map $v$ is a surjective valuation
$K^\times\to\mathbf Z$, and its valuation ring — the elements of nonnegative value — is exactly
$V$. Integrality follows formally: if $x\in K$ is integral over $V$ and $v(x)<0$, then in a
monic relation $x^n+a_1x^{n-1}+\cdots+a_n=0$ the leading term has value $nv(x)$, while each
$a_ix^{n-i}$ has value at least $(n-i)v(x)>nv(x)$ because $v(a_i)\geq0$; a sum in which one term
has strictly smallest value has that value and cannot vanish. Hence $v(x)\geq0$ and $x\in V$.
$\square$

**Lemma 1.2B.2.** Let $B$ be a reduced noetherian ring satisfying $S_1$, with minimal primes
$\mathfrak p_1,\ldots,\mathfrak p_r$. Then the zerodivisors of $B$ are exactly the elements of
$\mathfrak p_1\cup\cdots\cup\mathfrak p_r$, every nonzerodivisor is a unit of the total quotient
ring $Q(B)$, and

$$
Q(B)\;\cong\;\prod_{i=1}^{r}\kappa(\mathfrak p_i).
$$

_Proof._ By Lemma 1.2A.1 the associated primes of $B$ are precisely its minimal primes, and the
zerodivisors are the union of the associated primes. Hence $Q(B)=S^{-1}B$ where $S$ is the
complement of $\bigcup_i\mathfrak p_i$, and elements of $S$ are invertible in $Q(B)$ by
construction. The primes of $S^{-1}B$ correspond to the primes of $B$ disjoint from $S$, that
is, to the $\mathfrak p_i$ themselves, and

$$
S^{-1}B\,/\,\mathfrak p_iS^{-1}B\;\cong\;S^{-1}(B/\mathfrak p_i)
\;=\;\operatorname{Frac}(B/\mathfrak p_i)\;=\;\kappa(\mathfrak p_i),
$$

since the image of $S$ in the domain $B/\mathfrak p_i$ is the set of its nonzero elements. Thus
$S^{-1}B$ is artinian, all of its primes being maximal, and reduced. Its Jacobson radical is
nilpotent — artinian radicals always are — hence zero, so $S^{-1}B$ is a product of fields,
namely its residue fields as displayed. $\square$

**Proposition 1.2B.3 (Serre).** A noetherian ring satisfying $R_1$ and $S_2$ is normal: every
localization at a prime is an integrally closed domain.

_Proof._ Trivially $R_1$ implies $R_0$ and $S_2$ implies $S_1$, so $A$ is reduced by Proposition
1.2A.3. Both conditions pass to localizations: the primes below a fixed prime are unchanged by
localization, so heights do not increase, while depth and dimension at corresponding primes take
the same values. Fix a prime $\mathfrak q$ and put $B=A_{\mathfrak q}$. We prove more generally,
by induction on $d=\dim B$, the statement

$$
\text{every local noetherian ring of dimension }d\text{ satisfying }R_1\text{ and }S_2
\text{ is an integrally closed domain.}
\tag{1.3}
$$

If $d=0$, then $B$ is reduced and artinian local, so its maximal ideal, being the nilradical,
vanishes: $B$ is a field. If $d=1$, every prime of $B$ has height at most one, so every
localization of $B$ is regular and $B$ itself is a one-dimensional regular local ring;
Lemma 1.2B.1 makes it an integrally closed domain.

Let $d\geq2$. Write $(B,\mathfrak m)$ and $Q=Q(B)$.

(a) By $S_2$ the depth of $B$ is at least $2$, and the standard theory of depths declared in
Section 1.2 produces a regular sequence of length two inside $\mathfrak m$: an element
$t\in\mathfrak m$ that is a nonzerodivisor on $B$, and an element $s\in\mathfrak m$ that is a
nonzerodivisor on $B/tB$.

(b) Let $x\in Q$ be integral over $B$ and let $\mathfrak p\subsetneq\mathfrak m$ be a prime.
Then $\dim B_{\mathfrak p}\leq d-1$, and $B_{\mathfrak p}$ is again a local noetherian ring
satisfying $R_1$ and $S_2$: its primes are the primes of $B$ contained in $\mathfrak p$, with
unchanged heights, depths, and dimensions, so both conditions are read off from those of $B$.
Statement $(1.3)$ at smaller dimension makes $B_{\mathfrak p}$ integrally closed in
$Q(B_{\mathfrak p})$. The natural map $Q(B)\to Q(B_{\mathfrak p})$ is defined — a denominator
$e$ that is a nonzerodivisor on $B$ avoids the associated primes of $B_{\mathfrak p}$, which
are extended from associated primes of $B$ contained in $\mathfrak p$ — and it carries $x$ to
an element integral over $B_{\mathfrak p}$. Hence $x/1\in B_{\mathfrak p}$.

(c) The subring $B'=B[x]$ of $Q$ is a finite $B$-module: a monic relation for $x$ of degree $n$
lets every power $x^m$ with $m\geq n$ be rewritten as a $B$-linear combination of
$1,x,\ldots,x^{n-1}$. So $M=B'/B$ is a finite $B$-module, and (b) says
$\operatorname{Supp}M\subseteq\{\mathfrak m\}$. Suppose $M\neq0$. Then $\mathfrak m$ is the
radical of $\operatorname{Ann}M$, so $\mathfrak m^NM=0$ for some $N$; taking $i$ maximal with
$\mathfrak m^iM\neq0$ and any nonzero $\xi$ in that submodule, $\xi$ is killed by
$\mathfrak m$. Since $B$ is reduced it embeds in $Q$, so $B'$ is a subring of $Q$; lift $\xi$ to
$y\in B'$. Then $y\notin B$ while $\mathfrak m\,y\subseteq B$.

(d) Put $w=ty\in B$. Were $w\in tB$, say $w=t\rho$, then $t(y-\rho)=0$ in $Q$, and $t$ is a unit
of $Q$ because it is a nonzerodivisor; so $y=\rho\in B$, contradicting (c). Hence the class
$\bar w$ of $w$ in $B/tB$ is nonzero. On the other hand $sw=s\,ty=t(sy)$ lies in $tB$ because
$sy\in B$, so $s\bar w=0$ in $B/tB$ — impossible, since $s$ was chosen a nonzerodivisor there.
Therefore $M=0$ after all, meaning $x\in B$; and as $x$ was arbitrary, $B$ is integrally closed
in $Q$.

(e) It remains to see that $B$ is a domain. Suppose there were $r\geq2$ minimal primes. By
Lemma 1.2B.2,

$$
Q\;\cong\;\kappa(\mathfrak p_1)\times\cdots\times\kappa(\mathfrak p_r),
$$

and the idempotent $e=(1,0,\ldots,0)$ satisfies $e^2-e=0$, a monic equation over $B$, so $e$ is
integral over $B$ and belongs to $B$. But then $B=Be\times B(1-e)$ with both factors nonzero,
and a product of two nonzero rings has at least two maximal ideals, contradicting locality.
Hence $r=1$, so $Q=\operatorname{Frac}(B)$, and by (d) $B$ is an integrally closed domain. This
completes the induction, and $A_{\mathfrak q}$ is an integrally closed domain for every
$\mathfrak q$. $\square$

The converse implication is classical — EGA IV$_2$, Theorem 5.8.6 — and is covered by the
standing declaration of Section 1.2; part of it is immediate from what has been proved here. If
$A$ is normal, its local rings are domains, so $A$ is reduced and satisfies $R_0$; a local
domain of positive dimension never has $\mathfrak m$ as an associated prime, whence $S_1$; and a
one-dimensional normal local domain is a one-dimensional noetherian local integrally closed
domain, hence a discrete valuation ring and regular by Book 1, Theorem 4.1, whence $R_1$. That
a normal local domain of dimension at least two has depth at least two needs an additional
argument, for which we invoke the declaration rather than duplicate it here.

### 1.2C Cohen--Macaulay inputs

The declaration in Section 1.2 also relies on three facts about Cohen--Macaulay local rings.
They are proved here. Recall that a noetherian local ring $(A,\mathfrak m)$ is
_Cohen--Macaulay_ when $\operatorname{depth}A=\dim A$, that $S_1$ holds for every
Cohen--Macaulay ring (the depth inequality forces the associated primes to be minimal, as in
Lemma 1.2A.1), and that localizations of Cohen--Macaulay local rings at primes are again
Cohen--Macaulay (depth and dimension localize compatibly; this is recorded as Lemma 1.2C.3).

**Lemma 1.2C.1.** Let $(A,\mathfrak m)$ be a Cohen--Macaulay local ring of dimension
$d\geq1$ and let $f_1,\ldots,f_d$ be a system of parameters. Then $f_1,\ldots,f_d$ is an
$A$-regular sequence and $A/(f_1,\ldots,f_i)$ is Cohen--Macaulay of dimension $d-i$ for
every $i$.

_Proof._ By induction on $d$. The set of minimal primes of $A$ is finite, and none contains
$\mathfrak m$; by prime avoidance there exists $f_1\in\mathfrak m$ outside all of them,
so $f_1$ avoids $\operatorname{Ass}(A)=\operatorname{Min}(A)$ (Lemma 1.2A.1) and is a
nonzerodivisor. Since $f_1$ belongs to no minimal prime while lying in $\mathfrak m$, the
chain $\dim A/(f_1)\leq d-1$ holds, and equality follows because any parameter sequence of
$A/(f_1)$ together with $f_1$ spans an $\mathfrak m$-primary ideal, giving
$d=\dim A\leq\dim A/(f_1)+1$. From the short exact sequence
$0\to A\xrightarrow{f_1}A\to A/(f_1)\to0$ the long exact depth sequence gives
$\operatorname{depth}A/(f_1)\geq d-1$, while $\dim A/(f_1)=d-1$, so $A/(f_1)$ is
Cohen--Macaulay of dimension $d-1$. The induction hypothesis applied to the parameter
sequence $f_2,\ldots,f_d$ of $A/(f_1)$ completes the proof. $\square$

**Lemma 1.2C.2.** Let $A$ be a noetherian ring and let $J=(g_1,\ldots,g_r)$ be generated by
$r$ elements. Then every prime minimal over $J$ has height at most $r$.

_Proof._ This is Krull's principal ideal theorem iterated: each $g_{i+1}$ is principal in
$A/(g_1,\ldots,g_i)$, so chains descending from a minimal prime over $J$ grow by at most one
per generator. $\square$

**Lemma 1.2C.3.** Let $(A,\mathfrak m)$ be Cohen--Macaulay local and let $I\subseteq
\mathfrak m$ be an ideal of height $h$. Then $I$ contains an $A$-regular sequence
$f_1,\ldots,f_h$; moreover every prime minimal over $(f_1,\ldots,f_r)$ has height exactly
$r$ for each $r\leq h$, and $A/(f_1,\ldots,f_r)$ is Cohen--Macaulay of dimension
$d-r$ where $d=\dim A$.

_Proof._ Choose $f_1,\ldots,f_h\in I$ inductively so that every prime minimal over
$J_r=(f_1,\ldots,f_r)$ has height exactly $r$: given such $J_{r-1}$, its minimal primes are
finite, each of height exactly $r-1$ (inductively by Lemma 1.2C.2 together with the chain
constructed so far), and since $\operatorname{ht}I=h>r-1$ the ideal $I$ is contained in none
of them; prime avoidance supplies $f_r\in I$ outside their union, and Lemma 1.2C.2 bounds
minimal heights by $r$ while the construction gives at least $r$. Extend $f_1,\ldots,f_h$ to
a full system of parameters $f_1,\ldots,f_d$ (possible by further avoidance against the
finitely many primes minimal over $J_h$, whose height is $h<d$ unless $h=d$). Lemma 1.2C.1
makes $f_1,\ldots,f_d$ an $A$-regular sequence, so its initial segment
$f_1,\ldots,f_h$ is regular and $A/J_r$ is Cohen--Macaulay of dimension $d-r$. Finally, if
$\mathfrak q$ is minimal over $J_r$, then localizing at $\mathfrak q$ the quotient
$(A/J_r)_{\mathfrak q}$ is zero-dimensional, so $\mathfrak q$'s height satisfies
$r\leq\operatorname{ht}\mathfrak q\leq r$ by the same two bounds: the chain from the
construction gives at least $r$ and Lemma 1.2C.2 at most $r$. $\square$

### 1.3 The shape of the argument

It is worth recording at the outset how Theorem $(1.1)$ is reduced to a statement about complete
local rings, because the reduction dictates the order of the chapters and explains why so much of
the work is preparation.

Two of the three moves are free. If $A$ is a $G$-ring, so is every quotient $A/I$: the local rings
of $A/I$ are quotients $A_{\mathfrak p}/IA_{\mathfrak p}$, their completions are
$\widehat{A_{\mathfrak p}}/I\widehat{A_{\mathfrak p}}$, and the formal fibers over primes
containing $I$ are literally the same rings as before, because tensoring with $\kappa(\mathfrak q)$
already annihilates $I$. If $A$ is a $G$-ring, so is every localization $S^{-1}A$, because the
defining condition is a condition at each prime and the local rings do not change. So $(1.1)$ is a
statement about the polynomial algebra only, and may be tested on the local rings of
$A[x_1,\ldots,x_n]$, and after localizing the base we may assume that $A$ is local.

The third move uses the hypothesis exactly once. With $A$ local and $B$ a local ring of
$A[x_1,\ldots,x_n]$, set $C=B\otimes_A\widehat A$. The hypothesis says $A\to\widehat A$ is a
_regular homomorphism_, and regularity of a homomorphism survives base change, so $B\to C$ is
regular; moreover the completion of $C$ at the relevant maximal ideal is $\widehat B$, because $C$
and $B$ have the same finite-length quotients. Composing regular homomorphisms, what remains to
be proved is that

$$
\text{every algebra essentially of finite type over a complete noetherian local ring
is a }G\text{-ring.}
\tag{1.2}
$$

Statement $(1.2)$ is the whole content of the theorem, and it is where Cohen's structure theory
enters. By Book 1, Corollary 13.31, a complete noetherian local ring is a quotient of
$k[[x_1,\ldots,x_n]]$ or of $C_0[[x_1,\ldots,x_n]]$ with $C_0$ a Cohen ring, and quotients cost
nothing; so $(1.2)$ concerns localized polynomial algebras over those two coefficient rings. What
distinguishes those rings is that they carry coordinates in which differentials can be counted. In
characteristic $p$ the coefficient field and the variables form a finite $p$-basis, provided
$[k:k^p]<\infty$; Cartier's equality then pins down the $p$-degree of every residue field, a
Jacobian criterion decides regularity of the formal fibers, and the Frobenius upgrades regularity
to geometric regularity. When the fraction field has characteristic zero, the residue fields at
primes meeting the coefficient ring trivially are finitely generated over its fraction field, a
transcendence-degree count replaces Cartier's equality, and primes meeting it nontrivially are
removed by an induction on dimension. That is the argument, and Chapter 6 carries it out.

Chapters 2 and 3 supply the two toolkits that the argument presupposes: the homological theory of
regularity, and the theory of geometric regularity over a field, where separability decides
everything and characteristic $p$ is the only difficulty. Chapter 4 introduces regular
homomorphisms and proves the formal permanence used in the reduction above. Chapter 5 develops
formal smoothness, the classical instrument for the same base case; it is not needed by the route
actually taken, and Section 10.4 says so explicitly. Chapters 7 to 10 then convert the main theorem
into the statements the geometry consumes: openness of regular loci, finiteness of normalization,
and the assembled excellence package.

## 2. Regularity, resolutions, and flat maps

Regularity is defined by a numerical coincidence: a noetherian local ring $(A,\mathfrak m,k)$ is
regular when $\dim_k\mathfrak m/\mathfrak m^2=\dim A$, the smallest value permitted by Krull's
height theorem. The definition is local at the closed point and says nothing whatever about the
other primes of $A$, nor about rings mapping to or from $A$. Yet the entire theory of formal
fibers consists of statements of exactly that kind. A formal fiber is a ring of the form
$\widehat{A_{\mathfrak p}}\otimes\kappa(\mathfrak q)$, and asserting that it is _regular_ means
asserting that all of its localizations are regular local rings; comparing a ring with a flat
extension of it means transporting regularity in both directions along a map.

Neither transport is accessible from the definition. That a localization of a regular local ring
is again regular is not visible in the numerical definition at all, since localization changes
both the dimension and the cotangent space in uncontrolled ways. That regularity descends along a
faithfully flat map — if $R\to S$ is faithfully flat and $S$ is regular, then $R$ is regular — is
likewise invisible. Both become transparent once regularity is recognized as a _homological_
condition: $A$ is regular exactly when the residue field admits a finite free resolution. Finite
free resolutions localize, because localization is exact and preserves freeness, and they descend
along faithfully flat maps, because a minimal resolution stays minimal after base change. This
chapter proves that characterization, which is due to Serre, and then assembles the elementary
theory of flat local homomorphisms that the later chapters use to move regularity across maps
whose fibers are under control.

### 2.1 Minimal free resolutions and projective dimension

Over a local ring one can always resolve a finite module _efficiently_: at each stage generate the
kernel by the smallest possible number of elements. The resulting resolution is rigid — its ranks
are invariants of the module — because after tensoring with the residue field all differentials
vanish, so the resolution computes $\operatorname{Tor}$ with no cancellation. This is the one
technical device on which the whole chapter rests.

Throughout, $(A,\mathfrak m,k)$ is a noetherian local ring and modules are finitely generated. A
complex of finite free modules

$$
F_\bullet:\qquad\cdots\longrightarrow F_2\xrightarrow{\ d_2\ }F_1\xrightarrow{\ d_1\ }F_0
$$

is **minimal** if $d_i(F_i)\subseteq\mathfrak mF_{i-1}$ for every $i\geq1$; equivalently, if the
matrices of the differentials have all entries in $\mathfrak m$.

**Lemma 2.1 (minimal resolutions and Betti numbers).** Every finite $A$-module $M$ admits a
minimal free resolution $F_\bullet\to M$ by finite free modules. For any such resolution the
complex $F_\bullet\otimes_Ak$ has zero differentials, so

$$
\operatorname{Tor}^A_i(M,k)\cong F_i\otimes_Ak,\qquad
\operatorname{rank}F_i=\dim_k\operatorname{Tor}^A_i(M,k)=:\beta_i(M).
\tag{2.1}
$$

In particular the ranks of a minimal free resolution do not depend on the choices made.

**Proof.** Choose elements $m_1,\ldots,m_{\beta}\in M$ whose classes form a $k$-basis of
$M/\mathfrak mM$. By Nakayama they generate $M$, so $F_0=A^{\beta}\to M$ is surjective; and its
kernel $Z_0$ lies in $\mathfrak mF_0$, for if $\sum a_ie_i\mapsto0$ with some
$a_i\notin \mathfrak m$ then the classes of the $m_i$ would be linearly dependent over $k$. The
module $Z_0$ is finite because $A$ is noetherian, so the construction may be repeated with $Z_0$
in place of $M$, producing $F_1\to Z_0\subseteq F_0$ with image contained in $\mathfrak mF_0$ and
with kernel inside $\mathfrak mF_1$. Iterating gives a minimal free resolution.

Given any minimal resolution, the differentials of $F_\bullet\otimes_Ak$ are induced by matrices
with entries in $\mathfrak m$, hence are zero. Since $F_\bullet$ is a free — in particular flat —
resolution of $M$, it computes $\operatorname{Tor}^A_\bullet(M,k)$, and with zero differentials
the homology is the complex itself. $\square$

**Lemma 2.2 (projective dimension is measured by the residue field).** For a finite $A$-module
$M$ and an integer $n\geq0$ the following are equivalent: $M$ has a free resolution of length
$\leq n$ by finite free modules; $\operatorname{Tor}^A_{n+1}(M,k)=0$; the minimal free resolution
of $M$ has $F_i=0$ for $i>n$. Consequently

$$
\operatorname{pd}_AM=\sup\{i:\operatorname{Tor}^A_i(M,k)\neq0\},
\tag{2.2}
$$

where $\operatorname{pd}_AM$ denotes the least length of a finite free resolution, and $\infty$ if
there is none.

**Proof.** A free resolution of length $\leq n$ computes $\operatorname{Tor}^A_{n+1}(M,k)$ as the
homology of a complex which is zero in degree $n+1$, so the first condition implies the second. If
$\operatorname{Tor}^A_{n+1}(M,k)=0$ then $(2.1)$ gives $F_{n+1}\otimes k=0$ for the minimal
resolution, hence $F_{n+1}=0$ by Nakayama, and then exactness at $F_n$ forces $F_i=0$ for all
$i>n$: indeed $F_{n+2}\to F_{n+1}=0$, so the kernel of $F_{n+1}\to F_n$ is the image of $F_{n+2}$,
and each successive module is again killed by the same argument applied to the truncated
resolution. The third condition trivially implies the first. Formula $(2.2)$ follows because the
minimal resolution has $F_i\neq0$ exactly when $\operatorname{Tor}^A_i(M,k)\neq0$. $\square$

Two remarks on the formula. It shows that projective dimension over a local ring is computed by a
single module, the residue field; and it shows that finite projective dimension is inherited by
every module admitting a length bound, which is what makes the invariant usable. We now identify
the modules of finite projective dimension over a regular local ring, by exhibiting an explicit
resolution of $k$.

Recall that a sequence $x_1,\ldots,x_r$ in $\mathfrak m$ is a **regular sequence** if $x_{i}$ is a
nonzerodivisor on $A/(x_1,\ldots,x_{i-1})$ for each $i$. The **Koszul complex** on
$x_1,\ldots,x_r$ is the tensor product over $A$ of the two-term complexes
$(0\to A\xrightarrow{x_i}A\to0)$ placed in degrees $1$ and $0$; explicitly
$K_i(x)=\textstyle\bigwedge^iA^r$ with differential

$$
d(e_{j_1}\wedge\cdots\wedge e_{j_i})
=\sum_{s=1}^i(-1)^{s-1}x_{j_s}\,e_{j_1}\wedge\cdots\widehat{e_{j_s}}\cdots\wedge e_{j_i}.
$$

**Lemma 2.3 (Koszul resolution).** If $x_1,\ldots,x_r\in\mathfrak m$ is a regular sequence then
$K_\bullet(x_1,\ldots,x_r)$ is a free resolution of $A/(x_1,\ldots,x_r)$, and it is minimal.

**Proof.** For any complex $C_\bullet$ of $A$-modules and any $y\in A$, the complex
$C_\bullet\otimes_AK_\bullet(y)$ is the mapping cone of multiplication by $y$ on $C_\bullet$, so
the long exact homology sequence of the cone gives short exact sequences

$$
0\longrightarrow H_i(C)/yH_i(C)\longrightarrow H_i\big(C\otimes K(y)\big)
\longrightarrow\{z\in H_{i-1}(C):yz=0\}\longrightarrow0
\tag{2.3}
$$

for every $i$. Argue by induction on $r$. For $r=0$ the complex is $A$ in degree zero. Assume
$K_\bullet(x_1,\ldots,x_{r-1})$ has homology $A/(x_1,\ldots,x_{r-1})$ in degree $0$ and zero
elsewhere. Applying $(2.3)$ with $C=K_\bullet(x_1,\ldots,x_{r-1})$ and $y=x_r$: for $i\geq2$ both
outer terms vanish; for $i=1$ the left term vanishes and the right term is the $x_r$-torsion of
$A/(x_1,\ldots,x_{r-1})$, which is zero because $x_r$ is a nonzerodivisor on that quotient; and
for $i=0$ we get $A/(x_1,\ldots,x_r)$. Minimality holds because every entry of the differential is
one of the $x_j\in\mathfrak m$. $\square$

**Theorem 2.4 (regular local rings have finite global dimension).** Let $A$ be a regular local
ring of dimension $d$ and let $x_1,\ldots,x_d$ be a regular system of parameters. Then
$x_1,\ldots,x_d$ is a regular sequence, $K_\bullet(x_1,\ldots,x_d)$ is the minimal free resolution
of $k$, and

$$
\operatorname{pd}_Ak=d,\qquad\dim_k\operatorname{Tor}^A_i(k,k)=\binom{d}{i}.
$$

**Proof.** Put $A_i=A/(x_1,\ldots,x_i)$. Its maximal ideal is generated by the $d-i$ remaining
parameters, so $\dim A_i\leq d-i$ by Krull's height theorem, while $\dim A_i\geq d-i$ because
killing one element drops the dimension by at most one. Hence $\dim A_i=d-i$ and $A_i$ is regular.
A regular local ring is a domain, so $A_i$ is a domain; and $x_{i+1}\neq0$ in $A_i$, since
otherwise $A_{i+1}=A_i$ would have dimension $d-i$ rather than $d-i-1$. Therefore $x_{i+1}$ is a
nonzerodivisor on $A_i$ and the sequence is regular. Lemma 2.3 now makes $K_\bullet(x)$ a minimal
free resolution of $A/(x_1,\ldots,x_d)=k$, and $(2.1)$ gives
$\operatorname{Tor}^A_i(k,k)\cong\bigwedge^ik^d$, which is nonzero exactly for $0\leq i\leq d$.
$\square$

**Corollary 2.5.** If $\operatorname{pd}_Ak=n<\infty$ then $\operatorname{pd}_AM\leq n$ for every
finite $A$-module $M$. In particular, over a regular local ring of dimension $d$ every finite
module has a free resolution of length at most $d$ by finite free modules.

**Proof.** By Lemma 2.2 applied to $k$, the residue field has a free resolution of length $n$.
Since $\operatorname{Tor}$ may be computed from a resolution of either argument, that resolution
gives $\operatorname{Tor}^A_{n+1}(M,k)=0$ for every $M$, and Lemma 2.2 applied to $M$ bounds
$\operatorname{pd}_AM$ by $n$. The last assertion is Theorem 2.4. $\square$

The final lemma of this section records how minimal resolutions behave under a flat local map. It
is the mechanism behind every descent statement in this book: freeness and exactness are preserved
by flat base change, and _minimality_ is preserved because the maximal ideal of the source lands
inside the maximal ideal of the target.

**Lemma 2.6 (minimal resolutions under flat local maps).** Let
$\varphi:(A,\mathfrak m,k)\to (B,\mathfrak n,\ell)$ be a flat local homomorphism of noetherian
local rings and let $M$ be a finite $A$-module. If $F_\bullet$ is a minimal free resolution of
$M$ over $A$, then $F_\bullet\otimes_AB$ is a minimal free resolution of $M\otimes_AB$ over $B$.
Consequently

$$
\beta^B_i(M\otimes_AB)=\beta^A_i(M)\quad\text{for all }i,
\qquad\text{and}\qquad
\operatorname{pd}_B(M\otimes_AB)=\operatorname{pd}_AM.
$$

**Proof.** Flatness of $\varphi$ makes $F_\bullet\otimes_AB\to M\otimes_AB$ exact, and each
$F_i\otimes_AB$ is finite free over $B$. The differentials have entries in
$\varphi(\mathfrak m)\subseteq\mathfrak n$, so the resolution is minimal. The Betti numbers and
the projective dimension are read off from $(2.1)$ and $(2.2)$. $\square$

### 2.2 Serre's homological criterion

Theorem 2.4 says that regularity forces the residue field to have a finite free resolution. The
converse is the substantial half, and it is what converts regularity from a numerical accident
into a property that can be transported along maps. The proof is an induction on the embedding
dimension $\dim_k\mathfrak m/\mathfrak m^2$. To lower it one divides by a single element
$x\in\mathfrak m\setminus\mathfrak m^2$; for the induction to be usable, $x$ must be a
nonzerodivisor, so that dividing by it drops the dimension by exactly one and does not disturb
resolutions. The one case where no such $x$ exists is when $\mathfrak m$ consists of
zerodivisors, and the first lemma shows that finite projective dimension of $k$ excludes this
outright except in the trivial situation.

**Lemma 2.7 (the depth-zero case).** Suppose $\operatorname{pd}_Ak<\infty$ and there exists
$a\in A$, $a\neq0$, with $a\mathfrak m=0$. Then $A$ is a field.

**Proof.** Let $F_\bullet$ be the minimal free resolution of $k$, of length $n=\operatorname{pd}_Ak$,
so $F_n\neq0$ and $d_n:F_n\to F_{n-1}$ is injective when $n\geq1$. The matrix of $d_n$ has all
entries in $\mathfrak m$, hence is annihilated by $a$; therefore $d_n(aF_n)=a\,d_n(F_n)=0$, so
$aF_n\subseteq\ker d_n=0$. Since $F_n$ is a nonzero free module and $a\neq0$, this is impossible.
Hence $n=0$, that is, $k$ is a finite free $A$-module. Tensoring $k\cong A^r$ with $k$ gives
$r=1$, so $k\cong A$ as $A$-modules; but $\mathfrak m$ annihilates $k$, so $\mathfrak m$
annihilates $A$ and $\mathfrak m=0$. $\square$

**Lemma 2.8 (dividing by a parameter).** Let $x\in\mathfrak m\setminus\mathfrak m^2$ be a
nonzerodivisor and put $\bar A=A/xA$, $\bar{\mathfrak m}=\mathfrak m/xA$.

1. If $M$ is a finite $A$-module on which $x$ is a nonzerodivisor, then
   $\operatorname{pd}_{\bar A}(M/xM)=\operatorname{pd}_AM$.
2. There is an isomorphism of $\bar A$-modules
   $\mathfrak m/x\mathfrak m\cong\bar{\mathfrak m}\oplus k$.
3. If $\operatorname{pd}_Ak<\infty$ then $\operatorname{pd}_{\bar A}k<\infty$.

**Proof.** (1) From $0\to A\xrightarrow{x}A\to\bar A\to0$ we get
$\operatorname{Tor}^A_1(M,\bar A)=\{m\in M:xm=0\}=0$ and $\operatorname{Tor}^A_i(M,\bar A)=0$ for
$i\geq2$. Hence for a minimal free resolution $F_\bullet$ of $M$ over $A$ the complex
$F_\bullet\otimes_A\bar A=F_\bullet/xF_\bullet$ is a resolution of $M/xM$ over $\bar A$; it is by
finite free modules and is minimal, its differentials having entries in
$\bar{\mathfrak m}$. Comparing lengths of minimal resolutions gives the equality.

(2) Extend $x$ to a minimal generating set $x=x_1,x_2,\ldots,x_e$ of $\mathfrak m$; this is
possible because $x\notin\mathfrak m^2$, so its class in $\mathfrak m/\mathfrak m^2$ is part of a
basis. Inside $\mathfrak m/x\mathfrak m$ consider the submodules $N=xA/x\mathfrak m$ and
$W=\big((x_2,\ldots,x_e)+x\mathfrak m\big)/x\mathfrak m$. They span, since the $x_i$ generate
$\mathfrak m$. They intersect trivially: if $ax\in(x_2,\ldots,x_e)+x\mathfrak m$ with
$a\notin\mathfrak m$ then $x\in(x_2,\ldots,x_e)+\mathfrak m^2$, contradicting the minimality of
the chosen generating set; so $a\in\mathfrak m$ and $ax\in x\mathfrak m$. Thus
$\mathfrak m/x\mathfrak m=W\oplus N$. Now $N=xA/x\mathfrak m\cong A/\mathfrak m=k$ because $x$ is a
nonzerodivisor, and the surjection $\mathfrak m/x\mathfrak m\to\mathfrak m/xA=\bar{\mathfrak m}$
has kernel exactly $N$, hence restricts to an isomorphism $W\cong\bar{\mathfrak m}$.

(3) Let $n=\operatorname{pd}_Ak$. If $n=0$ then $A$ is a field by the argument at the end of
Lemma 2.7, and there is nothing to prove; so assume $n\geq1$. The sequence
$0\to\mathfrak m\to A\to k\to0$ gives $\operatorname{pd}_A\mathfrak m=n-1<\infty$. As a submodule
of $A$, the module $\mathfrak m$ has $x$ as a nonzerodivisor, so (1) gives
$\operatorname{pd}_{\bar A}(\mathfrak m/x\mathfrak m)=n-1$. By (2) the $\bar A$-module $k$ is a
direct summand of $\mathfrak m/x\mathfrak m$, and $\operatorname{Tor}$ commutes with direct sums,
so $(2.2)$ gives $\operatorname{pd}_{\bar A}k\leq n-1<\infty$. $\square$

**Theorem 2.9 (Serre's criterion for regularity).** For a noetherian local ring
$(A,\mathfrak m,k)$ the following are equivalent.

1. $A$ is regular.
2. $\operatorname{pd}_Ak<\infty$.
3. Every finite $A$-module has finite projective dimension.

When they hold, $\operatorname{pd}_Ak=\dim A$ and every finite module has a free resolution of
length at most $\dim A$ by finite free modules.

**Proof.** (1) $\Rightarrow$ (3) is Corollary 2.5 and (3) $\Rightarrow$ (2) is trivial. We prove
(2) $\Rightarrow$ (1) by induction on $e=\dim_k\mathfrak m/\mathfrak m^2$.

If $e=0$ then $\mathfrak m=\mathfrak m^2$, so $\mathfrak m=0$ by Nakayama and $A$ is a field,
which is regular of dimension $0$.

Let $e\geq1$. First, $\mathfrak m$ is not an associated prime of $A$: otherwise there is
$a\neq0$ with $a\mathfrak m=0$, and Lemma 2.7 would make $A$ a field, contradicting $e\geq1$.
Hence every associated prime of $A$ is properly contained in $\mathfrak m$, and there are finitely
many of them, say $\mathfrak p_1,\ldots,\mathfrak p_r$. Also $\mathfrak m\not\subseteq\mathfrak m^2$
because $e\geq1$. Prime avoidance — applicable because at most one of the ideals in the union,
namely $\mathfrak m^2$, fails to be prime — produces

$$
x\in\mathfrak m\setminus\big(\mathfrak m^2\cup\mathfrak p_1\cup\cdots\cup\mathfrak p_r\big).
$$

Since the zerodivisors of $A$ are the union of the associated primes, $x$ is a nonzerodivisor.

Put $\bar A=A/xA$. By Lemma 2.8(3), $\operatorname{pd}_{\bar A}k<\infty$. Its embedding dimension
is $\dim_k\mathfrak m/(\mathfrak m^2+xA)=e-1$, because $x\notin\mathfrak m^2$. By the induction
hypothesis $\bar A$ is regular, so $\dim\bar A=e-1$. Finally, killing a nonzerodivisor in a
noetherian local ring lowers the dimension by exactly one: $\dim\bar A\geq\dim A-1$ always, and
$\dim\bar A\leq\dim A-1$ because $x$ lies in no minimal prime. Hence $\dim A=e$ and $A$ is
regular. The supplementary assertions are Theorem 2.4 and Corollary 2.5. $\square$

The criterion pays for itself immediately. Both corollaries below are false-looking from the
numerical definition and immediate from the homological one.

**Corollary 2.10 (localization).** Let $A$ be a regular local ring and $\mathfrak p$ a prime of
$A$. Then $A_{\mathfrak p}$ is regular. Consequently a noetherian ring all of whose localizations
at maximal ideals are regular is regular in the sense of Section 1.2, and any localization of a
regular ring is regular.

**Proof.** By Corollary 2.5 the module $A/\mathfrak p$ has a finite free resolution $F_\bullet$
of finite length over $A$. Localizing at $\mathfrak p$ is exact and carries finite free modules to
finite free modules, so $(F_\bullet)_{\mathfrak p}$ is a finite free resolution of
$(A/\mathfrak p)_{\mathfrak p}=\kappa(\mathfrak p)$, the residue field of $A_{\mathfrak p}$.
Theorem 2.9 applied to $A_{\mathfrak p}$ gives regularity. For the second assertion, a prime
$\mathfrak q$ of a noetherian ring is contained in a maximal ideal $\mathfrak m$, and
$A_{\mathfrak q}=(A_{\mathfrak m})_{\mathfrak qA_{\mathfrak m}}$. $\square$

**Corollary 2.11 (faithfully flat descent of regularity).** Let $\varphi:R\to S$ be a faithfully
flat homomorphism of noetherian rings. If $S$ is regular then $R$ is regular. In particular, if
$(R,\mathfrak m)\to(S,\mathfrak n)$ is a flat local homomorphism of noetherian local rings and $S$
is regular, then $R$ is regular.

**Proof.** Consider first the local case; a flat local homomorphism is faithfully flat. By
Corollary 2.5 the finite $S$-module $S/\mathfrak mS=k\otimes_RS$ has finite projective dimension
over $S$. By Lemma 2.6 its projective dimension equals $\operatorname{pd}_Rk$, which is therefore
finite, and Theorem 2.9 makes $R$ regular.

In general, let $\mathfrak p\in\operatorname{Spec}R$. Faithful flatness makes
$\operatorname{Spec}S\to\operatorname{Spec}R$ surjective, so there is
$\mathfrak q\in\operatorname{Spec}S$ with $\mathfrak q\cap R=\mathfrak p$. The induced map
$R_{\mathfrak p}\to S_{\mathfrak q}$ is a flat local homomorphism, and $S_{\mathfrak q}$ is
regular by Corollary 2.10. The local case gives regularity of $R_{\mathfrak p}$. $\square$

### 2.3 Flat local homomorphisms

Corollary 2.11 descends regularity along an arbitrary faithfully flat map, but it says nothing in
the ascending direction, and for good reason: a flat local extension of a regular ring can easily
be singular. What controls the passage in both directions is the _fiber_. The theory of formal
fibers is built on the following principle, which the rest of the book uses constantly: for a flat
local homomorphism with regular closed fiber, source and target are regular together. Because the
statement is symmetric, it is what allows a property of $A$ to be read off from $\widehat A$ and
conversely, once the formal fibers are known to be regular.

Two elementary computations precede it.

**Lemma 2.12 (dimension formula).** Let $\varphi:(A,\mathfrak m)\to(B,\mathfrak n)$ be a flat
local homomorphism of noetherian local rings. Then

$$
\dim B=\dim A+\dim B/\mathfrak mB.
\tag{2.4}
$$

**Proof.** Write $r=\dim A$ and $s=\dim B/\mathfrak mB$. Choose a system of parameters
$x_1,\ldots,x_r$ of $A$ and elements $y_1,\ldots,y_s\in\mathfrak n$ whose images form a system of
parameters of $B/\mathfrak mB$. Then $B/(\varphi(x_1),\ldots,\varphi(x_r),y_1,\ldots,y_s)B$ has
$\mathfrak n$ as its unique prime: modulo $\mathfrak mB$ the elements $y_j$ already cut out an
ideal primary to the maximal ideal, and modulo the $x_i$ the ideal $\mathfrak mB$ becomes
nilpotent because $\mathfrak m^N\subseteq(x_1,\ldots,x_r)$ for some $N$. Hence $\mathfrak n$ is
the radical of an ideal generated by $r+s$ elements and $\dim B\leq r+s$.

Conversely, a chain of primes $\mathfrak q_0\subsetneq\cdots\subsetneq\mathfrak q_s=\mathfrak n$
in $B$ containing $\mathfrak mB$ has length $s$ for a suitable choice, since
$\dim B/\mathfrak mB=s$; and a chain
$\mathfrak p_0\subsetneq\cdots\subsetneq\mathfrak p_r=\mathfrak m$ of length $r$ in $A$ lifts
downward from $\mathfrak q_0$ by going-down for flat maps, producing primes
$\mathfrak q'_0\subsetneq\cdots\subsetneq\mathfrak q'_r=\mathfrak q_0$ of $B$ with
$\mathfrak q'_i\cap A=\mathfrak p_i$. Concatenating gives a chain of length $r+s$ in $B$, so
$\dim B\geq r+s$. $\square$

**Lemma 2.13 (minimal generators are preserved).** With $\varphi$ as above, $\mathfrak mB$ is
minimally generated by $\mu_A(\mathfrak m)=\dim_k\mathfrak m/\mathfrak m^2$ elements.

**Proof.** Flatness gives $\mathfrak mB=\mathfrak m\otimes_AB$, so with $\ell=B/\mathfrak n$,

$$
\mathfrak mB\otimes_B\ell=\mathfrak m\otimes_A\ell
=(\mathfrak m/\mathfrak m^2)\otimes_k\ell,
$$

a vector space over $\ell$ of dimension $\mu_A(\mathfrak m)$. By Nakayama this dimension is the
minimal number of generators of $\mathfrak mB$. $\square$

**Lemma 2.14 (ideals with regular quotient).** Let $(B,\mathfrak n)$ be a regular local ring of
dimension $d$ and $I\subseteq\mathfrak n$ an ideal with $B/I$ regular of dimension $t$. Then $I$
is generated by $d-t$ elements forming part of a regular system of parameters of $B$.

**Proof.** The cotangent space of $B/I$ is $\mathfrak n/(I+\mathfrak n^2)$, of dimension $t$;
hence $(I+\mathfrak n^2)/\mathfrak n^2$ has dimension $d-t$ inside the $d$-dimensional space
$\mathfrak n/\mathfrak n^2$. Choose $z_1,\ldots,z_{d-t}\in I$ whose classes form a basis of it and
$y_1,\ldots,y_t\in\mathfrak n$ completing the basis of $\mathfrak n/\mathfrak n^2$; then
$z_1,\ldots,z_{d-t},y_1,\ldots,y_t$ is a regular system of parameters of $B$. Set
$J=(z_1,\ldots,z_{d-t})\subseteq I$. The ring $B/J$ has maximal ideal generated by the $t$ images
of the $y_j$, so $\dim B/J\leq t$; and $\dim B/J\geq d-(d-t)=t$ by Krull's height theorem. Hence
$B/J$ is regular of dimension $t$, in particular a domain, and the surjection $B/J\to B/I$ has
source and target of the same dimension $t$. If $I\supsetneq J$ then $I/J$ is a nonzero ideal of
the domain $B/J$ and contains a nonzero element $b$, which lies in no minimal prime of $B/J$
because $(0)$ is the only one; killing it drops the dimension, so
$\dim B/I\leq\dim(B/J)/(b)\leq t-1$, contradicting $\dim B/I=t$. Hence $I=J$. $\square$

**Proposition 2.15 (ascent and descent with a regular fiber).** Let
$\varphi:(A,\mathfrak m)\to(B,\mathfrak n)$ be a flat local homomorphism of noetherian local rings
whose closed fiber $B/\mathfrak mB$ is regular. Then

$$
A\ \text{regular}\iff B\ \text{regular}.
$$

**Proof.** Write $r=\dim A$, $s=\dim B/\mathfrak mB$, so $\dim B=r+s$ by $(2.4)$.

Suppose $A$ is regular, with regular system of parameters $x_1,\ldots,x_r$, and choose
$y_1,\ldots,y_s\in\mathfrak n$ lifting a regular system of parameters of $B/\mathfrak mB$. Then
$\mathfrak n=\mathfrak mB+(y_1,\ldots,y_s)=(\varphi(x_1),\ldots,\varphi(x_r),y_1,\ldots,y_s)$, an
ideal generated by $r+s=\dim B$ elements, so $B$ is regular.

Suppose $B$ is regular. The quotient $B/\mathfrak mB$ is regular of dimension $s=\dim B-r$, so
Lemma 2.14 shows that $\mathfrak mB$ is generated by $\dim B-s=r$ elements. By Lemma 2.13 that
number is $\mu_A(\mathfrak m)$, whence $\dim_k\mathfrak m/\mathfrak m^2=r=\dim A$ and $A$ is
regular. $\square$

The hypothesis on the fiber cannot be dropped in the ascending direction. Let $k$ be a field and
consider the inclusion of the localizations

$$
A=k[x^2]_{(x^2)}\longrightarrow B=k[x]_{(x)} ,
$$

which is flat because $B$ is free of rank $2$ over $A$ with basis $1,x$. Both rings are discrete
valuation rings, hence regular, but the closed fiber is $k[x]/(x^2)$, which is not regular. In
the descending direction Corollary 2.11 shows that no hypothesis on the fiber is needed at all;
Proposition 2.15 is nevertheless the form used later, because in the situations of interest the
fibers are regular anyway and the proposition is elementary.

**Corollary 2.16 (polynomial and power series rings).** If $A$ is a regular ring then
$A[x_1,\ldots,x_n]$ is regular. If $(A,\mathfrak m)$ is a regular local ring then $A[[x]]$ is a
regular local ring of dimension $\dim A+1$.

**Proof.** For the first statement it suffices, by induction and Corollary 2.10, to treat
$A[x]$ and a prime $\mathfrak q$ of $A[x]$; let $\mathfrak p=\mathfrak q\cap A$. The map
$A_{\mathfrak p}\to A[x]_{\mathfrak q}$ is flat and local, and its closed fiber is a localization
of $\kappa(\mathfrak p)[x]$, hence either $\kappa(\mathfrak p)(x)$ or the localization of a
principal ideal domain at a maximal ideal; in both cases it is regular. Proposition 2.15 applies.
For the second, $A[[x]]$ is local with maximal ideal $(\mathfrak m,x)$, which is generated by
$\dim A+1$ elements, and $\dim A[[x]]=\dim A+1$ because $A\to A[[x]]$ is flat local with closed
fiber $k[[x]]$ of dimension one; now apply $(2.4)$. $\square$

**Corollary 2.17 (regular loci under a flat map with regular fibers).** Let $\varphi:R\to S$ be a
flat homomorphism of noetherian rings all of whose fibers are regular rings, and let
$\mathfrak q\in\operatorname{Spec}S$ with $\mathfrak p=\mathfrak q\cap R$. Then $S_{\mathfrak q}$
is regular if and only if $R_{\mathfrak p}$ is regular. If moreover $\varphi$ is faithfully flat,
the regular locus of $\operatorname{Spec}S$ is the preimage of the regular locus of
$\operatorname{Spec}R$.

**Proof.** The map $R_{\mathfrak p}\to S_{\mathfrak q}$ is flat and local, and its closed fiber is
the localization of the fiber ring $S\otimes_R\kappa(\mathfrak p)$ at the prime corresponding to
$\mathfrak q$, hence regular by hypothesis and Corollary 2.10. Proposition 2.15 gives the
equivalence, and the last statement is a restatement of it together with the surjectivity of
$\operatorname{Spec}S\to\operatorname{Spec}R$. $\square$

This is the shape of every argument to come. A ring $A$ and its completion, or a ring and a
finite-type extension of it, are compared through a flat map; whatever is known about the fibers
of that map is exactly what can be transported. The whole point of the $G$-property is to make the
fibers of $A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ regular — and regular after every finite
field extension, which is the refinement Chapter 3 now explains and which is needed because
regularity of a ring over a field is not by itself stable under enlarging the field.

## 3. Geometric regularity over a field

A fiber of a ring homomorphism is an algebra over a residue field, so any fiberwise condition is a
condition on algebras over a field. Regularity is the obvious candidate, and in characteristic
zero it is the right one. In characteristic $p$ it is not, for a reason that is visible in one
example. Let $K=\mathbf F_p(t)$ and

$$
R=K[x]/(x^p-t).
$$

Then $R$ is a field, hence regular. But $t$ becomes a $p$-th power in $K^{1/p}=K(t^{1/p})$, and

$$
R\otimes_KK^{1/p}=K^{1/p}[x]/(x^p-t)=K^{1/p}[x]/\big((x-t^{1/p})^p\big)
$$

is a nonreduced artinian local ring. A single inseparable field extension has destroyed
regularity, and with it every conclusion that regularity was supposed to support. The same
phenomenon in families is the reason a purely inseparable morphism can look smooth at every point
and fail to be smooth: regularity of a $K$-algebra is not a statement about the geometry of
$\operatorname{Spec}R$ over $K$ unless it survives extension of $K$.

The repair is to build the extensions into the definition. This chapter defines geometric
regularity, shows that it can be tested on finite purely inseparable extensions alone, and proves
that it is stable under _arbitrary_ field extensions — the property that makes it usable as a
fiberwise condition, since the residue fields appearing in a base change are arbitrary. The
characteristic-$p$ bookkeeping is done with the $p$-bases of Book 1, Section 13.3.

### 3.1 Separable field extensions

Throughout this section $K$ is a field. If $\operatorname{char}K=p>0$ we work inside a fixed
algebraic closure $\overline K$ and write $K^{1/p^n}=\{a\in\overline K:a^{p^n}\in K\}$; a finite
extension $K'/K$ is **purely inseparable** exactly when $K'\subseteq K^{1/p^n}$ for some $n$.
Recall from Book 1, Section 13.3, that a subset $B\subseteq K$ is **$p$-independent** if the
$p$-monomials $\prod b^{e_b}$, $0\leq e_b<p$, in any finite subset of $B$ are linearly independent
over $K^p$, equivalently (Book 1, Lemma 13.9) if $[K^p(b_1,\ldots,b_r):K^p]=p^r$ for distinct
$b_i\in B$; a **$p$-basis** is a $p$-independent subset with $K=K^p(B)$, and $p$-independent sets
extend to $p$-bases (Book 1, Lemma 13.10).

**Definition 3.1.** A field extension $L/K$ is **separable** if $L\otimes_KK'$ is reduced for
every finite purely inseparable extension $K'/K$. In characteristic zero there are no such
extensions other than $K$ itself, so every extension is separable.

**Lemma 3.2.** Let $K'/K$ be a finite purely inseparable extension and $R$ a $K$-algebra. Then
$\operatorname{Spec}(R\otimes_KK')\to\operatorname{Spec}R$ is a homeomorphism. In particular, for a
field $L$ the ring $L\otimes_KK'$ is local artinian, and it is reduced if and only if it is a
field.

**Proof.** Every element of $K'$ has a $p^n$-th power in $K$ for some $n$, so for
$z=\sum r_i\otimes c_i\in R\otimes_KK'$ a large enough $p^n$-th power satisfies
$z^{p^n}=\sum r_i^{p^n}\otimes c_i^{p^n}\in\operatorname{image}(R)$. Hence
$R\to R\otimes_KK'$ is integral and injective, and the kernel of $R\otimes_KK'\to R\otimes_KK'$
modulo any prime is determined by its contraction: if two primes $\mathfrak P_1,\mathfrak P_2$
contract to the same prime $\mathfrak p$ then for $z\in\mathfrak P_1$ we get
$z^{p^n}\in\mathfrak p\subseteq\mathfrak P_2$, so $z\in\mathfrak P_2$ and symmetrically. Thus the
map on spectra is a continuous bijection, and it is closed because the ring map is integral. For
$R=L$ a field, $L\otimes_KK'$ is a finite $L$-algebra with a single prime, hence local artinian,
and being reduced means the maximal ideal, which is the nilradical, vanishes. $\square$

**Lemma 3.3 (first-layer extensions).** Let $a_1,\ldots,a_s\in K$ be $p$-independent and set
$K'=K(a_1^{1/p},\ldots,a_s^{1/p})$. Then $K'=K[x_1,\ldots,x_s]/(x_i^p-a_i)$ is purely inseparable
of degree $p^s$ over $K$, and for every extension $L/K$

$$
L\otimes_KK'=L[x_1,\ldots,x_s]/(x_i^p-a_i)
$$

is reduced — equivalently a field — if and only if $a_1,\ldots,a_s$ are $p$-independent in $L$.

**Proof.** The displayed ring is spanned over $L$ by the $p^s$ monomials $x^e$ with $0\leq e_i<p$,
and these are linearly independent, so it is a free $L$-module of rank $p^s$; taking $L=K$ and
using $[K^p(a_1,\ldots,a_s):K^p]=p^s$ shows that $K'$ has degree $p^s$, which is the first claim.
If the $a_i$ are $p$-independent in $L$, the same computation applied to $L$ shows that
$L(a_1^{1/p},\ldots,a_s^{1/p})$ has degree $p^s$ over $L$, so the surjection from the displayed
ring onto it, both being $L$-spaces of dimension $p^s$, is an isomorphism and the ring is a field.
If the $a_i$ are $p$-dependent in $L$, then by Book 1, Lemma 13.9 there are exponents
$0\leq e_i<p$, not all zero, and $c\in L$ with $\prod a_i^{e_i}=c^p$. The element
$z=\prod x_i^{e_i}-c$ is nonzero, being a nontrivial $L$-combination of basis monomials, while
$z^p=\prod a_i^{e_i}-c^p=0$. So the ring is not reduced. $\square$

**Proposition 3.4 ($p$-independence and separability).** Let $L/K$ be an extension of fields of
characteristic $p$.

1. If $L/K$ is separable, then every finite $p$-independent subset of $K$ remains $p$-independent
   in $L$; in particular every $p$-basis of $K$ is $p$-independent in $L$.
2. Conversely, if every finite $p$-independent subset of $K$ remains $p$-independent in $L$, then
   $L\otimes_KK'$ is a field for every finite extension $K'/K$ with $(K')^p\subseteq K$.

**Proof.** (1) Let $a_1,\ldots,a_s\in K$ be $p$-independent. The extension
$K'=K(a_1^{1/p},\ldots,a_s^{1/p})$ is finite purely inseparable, so $L\otimes_KK'$ is reduced by
separability, and Lemma 3.3 says that this forces $p$-independence of the $a_i$ in $L$.

(2) Let $K'/K$ be finite with $(K')^p\subseteq K$. Choose $\beta_1,\ldots,\beta_s\in K'$
generating $K'$ over $K$ with $s$ minimal; then $a_i=\beta_i^p\in K$ and
$[K':K]=p^s$, since each step $K(\beta_1,\ldots,\beta_{j})/K(\beta_1,\ldots,\beta_{j-1})$ has
degree $p$ by minimality. Comparing with Lemma 3.3 applied over $K$ shows that the $a_i$ are
$p$-independent in $K$, hence in $L$ by hypothesis, and Lemma 3.3 applied over $L$ makes
$L\otimes_KK'$ a field. $\square$

Part (2) is the only converse we shall need; the corresponding statement for higher purely
inseparable layers is true but requires a bookkeeping argument with $p$-bases of the intermediate
fields that no later result of this book uses.

Two standard sufficient conditions deserve mention, both immediate from Lemma 3.3. If $K$ is
perfect, then $K$ has no proper purely inseparable extension at all, so every extension of $K$ is
separable. If $L/K$ is _separably generated_, that is, $L$ is a separable algebraic extension of a
purely transcendental extension $K(t_1,\ldots,t_r)$, then $L/K$ is separable: a $p$-independent
subset of $K$ stays $p$-independent in $K(t)$, because $K(t)^p=K^p(t^p)$ and the monomials in
question remain linearly independent, and then in $L$, because a separable algebraic extension
does not enlarge $p$-th powers relative to the base in a way that creates dependencies —
concretely, $L^p(a_1,\ldots,a_s)=L\otimes_{K(t)}K(t)^p(a_1,\ldots,a_s)$ has the expected degree
since $L/K(t)$ is separable and hence $L=L^pK(t)$.

### 3.2 Geometrically regular algebras

**Definition 3.5.** A noetherian $K$-algebra $R$ is **geometrically regular over $K$** if
$R\otimes_KL$ is a regular ring for every finite field extension $L/K$. A field extension $L/K$ is
geometrically regular precisely when $L$ is geometrically regular as a $K$-algebra.

The base changes appearing in the definition are harmless from the finiteness point of view: for
$L/K$ finite, $R\otimes_KL$ is a finite free $R$-module, hence noetherian, and the map
$R\to R\otimes_KL$ is finite, flat and injective. The example at the head of the chapter shows
that regularity of $R$ is strictly weaker than geometric regularity, and Lemma 3.2 identifies the
mechanism: an inseparable extension can create nilpotents.

The definition quantifies over all finite extensions, but the separable ones never cause trouble.

**Lemma 3.6 (separable base change preserves regularity).** Let $R$ be a regular noetherian
$K$-algebra and $L/K$ a finite separable algebraic extension. Then $R\otimes_KL$ is regular.

**Proof.** Let $\mathfrak Q$ be a prime of $S=R\otimes_KL$ and $\mathfrak q=\mathfrak Q\cap R$. The
map $R\to S$ is flat, so $R_{\mathfrak q}\to S_{\mathfrak Q}$ is a flat local homomorphism, and
its closed fiber is a localization of

$$
\kappa(\mathfrak q)\otimes_KL,
$$

which is a finite étale $\kappa(\mathfrak q)$-algebra: writing $L=K[x]/(f)$ with $f$ separable,
the ring is $\kappa(\mathfrak q)[x]/(f)$, and $f$ remains squarefree over any extension of $K$
because $\gcd(f,f')=1$ is preserved by base change. Hence it is a finite product of finite
separable field extensions of $\kappa(\mathfrak q)$, and its localizations are fields, in
particular regular. Proposition 2.15 makes $S_{\mathfrak Q}$ regular. $\square$

**Theorem 3.7 (test extensions).** A noetherian $K$-algebra $R$ is geometrically regular over $K$
if and only if $R\otimes_KK'$ is regular for every finite _purely inseparable_ extension $K'/K$.
In characteristic zero, therefore, geometric regularity over $K$ is the same as regularity.

**Proof.** Necessity is contained in the definition. Conversely let $L/K$ be a finite extension
and let $K'$ be the set of elements of $L$ purely inseparable over $K$; it is a subfield,
$K'/K$ is finite purely inseparable, and $L/K'$ is a finite separable extension by the standard
structure of finite extensions. By hypothesis $R\otimes_KK'$ is regular, and

$$
R\otimes_KL=(R\otimes_KK')\otimes_{K'}L
$$

is regular by Lemma 3.6. In characteristic zero the only finite purely inseparable extension is
$K$ itself. $\square$

**Lemma 3.8 (descent along a field extension).** Let $R$ be a $K$-algebra and $K\subseteq M$ a
field extension such that $R\otimes_KM$ is noetherian. If $R\otimes_KM$ is regular then $R$ is
regular. More generally, if $M\subseteq M'$ are extensions of $K$ with $R\otimes_KM$ and
$R\otimes_KM'$ noetherian and $R\otimes_KM'$ regular, then $R\otimes_KM$ is regular.

**Proof.** The map $M\to M'$ is faithfully flat, being an injection of fields, and faithful
flatness is preserved by base change, so $R\otimes_KM\to R\otimes_KM'$ is faithfully flat.
Corollary 2.11 applies. The first assertion is the case $M'=M$, $M=K$. $\square$

This innocuous lemma is the reason geometric regularity is manageable: to prove that a base change
is regular one is free to enlarge the field first, and enlarging it is exactly what turns awkward
inseparable extensions into transparent ones.

### 3.3 Test extensions and base change

Definition 3.5 quantifies over finite extensions only, because those are the ones for which
noetherianity is automatic. What the theory actually needs is stability under _arbitrary_
extensions: when a regular homomorphism is base changed, the residue fields that appear are
unrelated to the original ones and are rarely finite over them. The main theorem of this chapter
supplies that stability. Its proof has two moves. The first reduces an arbitrary extension to a
finitely generated one, by observing that a single prime of the base-changed ring already sees
only finitely much of the field. The second treats a finitely generated extension by enlarging it
until it becomes a purely transcendental extension of a _finite_ extension, where Corollary 2.16
applies; Lemma 3.8 then descends the conclusion back.

**Lemma 3.9 (only finitely much of the field matters).** Let $R$ be a noetherian $K$-algebra,
$M/K$ a field extension, and suppose $S=R\otimes_KM$ is noetherian. Write $M$ as the filtered union
of its finitely generated subextensions $M_i/K$ and put $S_i=R\otimes_KM_i$, a noetherian ring.
Fix $\mathfrak Q\in\operatorname{Spec}S$ and let $\mathfrak Q_i=\mathfrak Q\cap S_i$. Then for all
large enough $i$,

$$
\mathfrak QS_{\mathfrak Q}=\mathfrak Q_iS_{\mathfrak Q},
$$

and for such $i$ the ring $S_{\mathfrak Q}$ is regular if and only if
$(S_i)_{\mathfrak Q_i}$ is regular.

**Proof.** Each $M_i$ is a localization of a finite-type $K$-algebra, so $S_i$ is a localization of
a finite-type $R$-algebra and is noetherian. Since $M_i\to M$ is a flat ring map, so is
$S_i\to S=S_i\otimes_{M_i}M$, and therefore $(S_i)_{\mathfrak Q_i}\to S_{\mathfrak Q}$ is a flat
local homomorphism. As $S$ is noetherian, $\mathfrak QS_{\mathfrak Q}$ is generated by finitely
many elements $z_1,\ldots,z_m\in\mathfrak Q$; the union defining $M$ is filtered, so all $z_j$ lie
in $S_i$ for large $i$, and then $z_j\in\mathfrak Q\cap S_i=\mathfrak Q_i$, whence
$\mathfrak QS_{\mathfrak Q}=\mathfrak Q_iS_{\mathfrak Q}$. For such an $i$ the closed fiber of
$(S_i)_{\mathfrak Q_i}\to S_{\mathfrak Q}$ is
$S_{\mathfrak Q}/\mathfrak Q_iS_{\mathfrak Q}=\kappa(\mathfrak Q)$, a field, hence regular, and
Proposition 2.15 gives the equivalence. $\square$

**Theorem 3.10 (stability under arbitrary field extensions).** Let $R$ be a noetherian $K$-algebra
which is geometrically regular over $K$, and let $M/K$ be any field extension such that
$R\otimes_KM$ is noetherian. Then $R\otimes_KM$ is regular, and it is geometrically regular over
$M$.

**Proof.** _Step 1: finitely generated extensions._ Let $N/K$ be a finitely generated field
extension; we show that $R\otimes_KN$, which is noetherian because $N$ is a localization of a
finite-type $K$-algebra, is regular. Choose a transcendence basis $t_1,\ldots,t_r$ of $N/K$, so
that $N$ is finite over $K(t)=K(t_1,\ldots,t_r)$. Let $N_0$ be the purely inseparable closure of
$K(t)$ in $N$; then $N_0/K(t)$ is finite purely inseparable and $N/N_0$ is finite separable, so by
Lemma 3.6 it suffices to prove that $R\otimes_KN_0$ is regular. In characteristic zero $N_0=K(t)$
and the next paragraph applies with $n=0$.

Since $N_0/K(t)$ is finite purely inseparable, $N_0\subseteq K(t)^{1/p^n}$ for some $n$. An element
of $K(t)^{1/p^n}$ has the form $f(u)/g(u)$ where $u_i=t_i^{1/p^n}$ and $f,g$ are polynomials whose
coefficients are $p^n$-th roots of elements of $K$. As $N_0$ is generated over $K(t)$ by finitely
many such elements, there is a _finite_ extension $L/K$ inside $K^{1/p^n}$ with

$$
N_0\subseteq N':=L(u_1,\ldots,u_r),\qquad u_i=t_i^{1/p^n}.
$$

The $u_i$ are algebraically independent over $L$, because their $p^n$-th powers $t_i$ are
algebraically independent over $K$. Hence $R\otimes_KN'=(R\otimes_KL)\otimes_LL(u_1,\ldots,u_r)$ is
a localization of the polynomial ring $(R\otimes_KL)[u_1,\ldots,u_r]$. Now $R\otimes_KL$ is regular
because $L/K$ is finite and $R$ is geometrically regular, so $(R\otimes_KL)[u]$ is regular by
Corollary 2.16 and its localization $R\otimes_KN'$ is regular by Corollary 2.10. Both $N_0$ and
$N'$ are finitely generated over $K$, so both base changes are noetherian, and Lemma 3.8 descends
regularity from $R\otimes_KN'$ to $R\otimes_KN_0$. This proves Step 1.

_Step 2: arbitrary extensions._ Let $M/K$ be arbitrary with $S=R\otimes_KM$ noetherian, and let
$\mathfrak Q$ be a prime of $S$. By Lemma 3.9 there is a finitely generated subextension $M_i/K$
such that $S_{\mathfrak Q}$ is regular if and only if $(S_i)_{\mathfrak Q_i}$ is, and
$S_i=R\otimes_KM_i$ is regular by Step 1. Hence $S_{\mathfrak Q}$ is regular for every prime, that
is, $S$ is regular.

_Step 3: geometric regularity over $M$._ Let $M'/M$ be a finite extension. Then
$(R\otimes_KM)\otimes_MM'=R\otimes_KM'$ is a finite free module over the noetherian ring
$R\otimes_KM$, hence noetherian, and $M'/K$ is a field extension; Step 2 applies to it and shows
that $R\otimes_KM'$ is regular. $\square$

The theorem removes the last asymmetry from the definition: geometric regularity is a property of
$R$ over $K$ that persists under every enlargement of the field, so it can be imposed on the
fibers of a homomorphism and will survive any base change performed later. Three corollaries
record the facts used repeatedly in the sequel.

**Corollary 3.11 (fields).** A field extension $L/K$ is geometrically regular if and only if it is
separable. In that case $L\otimes_KM$ is regular for every extension $M/K$ for which it is
noetherian.

**Proof.** If $L/K$ is geometrically regular then for finite purely inseparable $K'/K$ the ring
$L\otimes_KK'$ is regular, hence reduced, so $L/K$ is separable. Conversely, if $L/K$ is separable
then $L\otimes_KK'$ is reduced for every finite purely inseparable $K'/K$, hence a field by
Lemma 3.2, hence regular; Theorem 3.7 upgrades this to geometric regularity. The last statement is
Theorem 3.10. $\square$

**Corollary 3.12 (reducedness and normality).** A geometrically regular $K$-algebra $R$ is
reduced and normal; more precisely, every localization of $R$ is a normal domain.

**Proof.** $R$ is regular, so each $R_{\mathfrak p}$ is a regular local ring and in particular a
domain; hence $R$ is reduced. For normality we verify Serre's conditions. Condition $R_1$ holds
because _every_ localization is regular, by Corollary 2.10. Condition $S_2$ holds because a
regular local ring is Cohen–Macaulay: by Theorem 2.4 a regular system of parameters is a regular
sequence, so the depth equals the dimension, and this persists in localizations by
Corollary 2.10. Serre's criterion now says that $R$ is normal. $\square$

**Corollary 3.13 (perfect base fields).** If $K$ is perfect — in particular if
$\operatorname{char}K=0$, or $K$ is algebraically closed, or $K$ is finite — then a noetherian
$K$-algebra is geometrically regular over $K$ if and only if it is regular.

**Proof.** A perfect field has no proper finite purely inseparable extension, so Theorem 3.7
applies. $\square$

Chapter 4 puts these notions to work. A homomorphism will be called regular when it is flat with
geometrically regular fibers; Corollary 3.12 then says that such a homomorphism carries reduced
and normal rings to reduced and normal rings in the fiber direction, Theorem 3.10 says that the
notion survives base change, and Proposition 2.15 says that regularity of local rings may be read
in either direction across it. Those three facts are the entire elementary theory of $G$-rings.

## 4. Regular homomorphisms and G-rings

### 4.1 Regular homomorphisms

**Definition 4.1.** A homomorphism $\varphi:A\to B$ of noetherian rings is **regular** if it is
flat and for every $\mathfrak p\in\operatorname{Spec}A$ the fiber ring
$B\otimes_A\kappa(\mathfrak p)$ is geometrically regular over $\kappa(\mathfrak p)$. A local
homomorphism of noetherian local rings is **regular at the closed point** if it is flat and the
closed fiber is geometrically regular over the residue field of the source.

Fiber rings are noetherian, being localizations of quotients of $B$, so Definition 3.5 applies to
them. The condition is deliberately fiberwise: it says nothing about $A$ or $B$ separately, and
everything about how they differ.

**Lemma 4.2 (pointwise form).** A flat homomorphism $\varphi:A\to B$ of noetherian rings is
regular if and only if for every $\mathfrak Q\in\operatorname{Spec}B$ with
$\mathfrak q=\mathfrak Q\cap A$ the flat local homomorphism
$A_{\mathfrak q}\to B_{\mathfrak Q}$ is regular at the closed point.

**Proof.** Fix $\mathfrak q$ and write $F=B\otimes_A\kappa(\mathfrak q)$. For a finite extension
$L/\kappa(\mathfrak q)$, the ring $F\otimes_{\kappa(\mathfrak q)}L$ is regular precisely when all
its localizations are regular; its primes lie over primes $\mathfrak Q$ of $F$, and the
localization at such a prime is a localization of
$F_{\mathfrak Q}\otimes_{\kappa(\mathfrak q)}L$. Since
$F_{\mathfrak Q}=B_{\mathfrak Q}/\mathfrak qB_{\mathfrak Q}$ is the closed fiber of
$A_{\mathfrak q}\to B_{\mathfrak Q}$, and since a localization of a regular ring is regular by
Corollary 2.10, the two conditions agree. $\square$

**Proposition 4.3 (regularity travels both ways).** Let $\varphi:A\to B$ be regular,
$\mathfrak Q\in\operatorname{Spec}B$ and $\mathfrak q=\mathfrak Q\cap A$. Then $A_{\mathfrak q}$ is
regular if and only if $B_{\mathfrak Q}$ is regular. If $\varphi$ is in addition faithfully flat,
then $A$ is a regular ring if and only if $B$ is.

**Proof.** By Lemma 4.2 the map $A_{\mathfrak q}\to B_{\mathfrak Q}$ is flat local with regular
closed fiber, so Proposition 2.15 gives the equivalence. If $\varphi$ is faithfully flat then
every prime of $A$ is a contraction, so the second statement follows. $\square$

Transporting reducedness and normality requires one more ingredient, the behaviour of depth. We
need only the inequality, and one equality in the case of an artinian fiber.

**Lemma 4.4 (depth across a flat local map).** Let $\varphi:(A,\mathfrak m)\to(B,\mathfrak n)$ be a
flat local homomorphism of noetherian local rings.

1. $\operatorname{depth}B\geq\operatorname{depth}A+\operatorname{depth}B/\mathfrak mB$.
2. If $B/\mathfrak mB$ is artinian, then $\operatorname{depth}B=\operatorname{depth}A$.

**Proof.** (1) Let $x_1,\ldots,x_r\in\mathfrak m$ be a regular sequence on $A$ of length
$r=\operatorname{depth}A$. Since $B$ is flat over $A$, multiplication by $x_1$ is injective on $B$,
and $B/x_1B$ is flat over $A/x_1A$ with the same closed fiber; iterating, $x_1,\ldots,x_r$ is a
regular sequence on $B$ and $\bar B=B/(x_1,\ldots,x_r)B$ is flat over $\bar A=A/(x_1,\ldots,x_r)A$
with closed fiber $B/\mathfrak mB$. Now let $y_1,\ldots,y_s\in\mathfrak n$ lift a regular sequence
on $B/\mathfrak mB$ of length $s=\operatorname{depth}B/\mathfrak mB$. By the local criterion of
flatness, if $M$ is flat over $\bar A$ and $y$ is a nonzerodivisor on $M/\mathfrak m M$, then $y$
is a nonzerodivisor on $M$ and $M/yM$ is again flat over $\bar A$; applying this successively to
$\bar B$ shows that $y_1,\ldots,y_s$ is a regular sequence on $\bar B$. Concatenating, $B$ admits a
regular sequence of length $r+s$.

(2) An artinian closed fiber has depth $0$, so (1) gives
$\operatorname{depth}B\geq\operatorname{depth}A$; we prove equality by induction on
$\operatorname{depth}A$. Suppose $\operatorname{depth}A=0$ and choose $a\neq0$ in $A$ with
$a\mathfrak m=0$, so that $aA\cong A/\mathfrak m=k$. Flatness gives
$aB\cong k\otimes_AB=B/\mathfrak mB\neq0$, a nonzero submodule of $B$ annihilated by
$\mathfrak mB$. Since the fiber is artinian, $\mathfrak n$ is the radical of $\mathfrak mB$, so
this submodule has finite length and contains a nonzero element killed by $\mathfrak n$; hence
$\mathfrak n$ is an associated prime of $B$ and $\operatorname{depth}B=0$. If
$\operatorname{depth}A=r>0$, choose $x\in\mathfrak m$ a nonzerodivisor on $A$; it is a
nonzerodivisor on $B$, the map $A/xA\to B/xB$ is again flat local with the same artinian closed
fiber, and $\operatorname{depth}A/xA=r-1$. By induction $\operatorname{depth}B/xB=r-1$, and since
$x\in\mathfrak n$ is a nonzerodivisor on $B$ we get $\operatorname{depth}B=r$. $\square$

**Proposition 4.5 (reducedness and normality).** Let $\varphi:A\to B$ be a homomorphism of
noetherian rings.

1. If $\varphi$ is regular and $A$ is reduced, then $B$ is reduced; if $\varphi$ is regular and
   $A$ is normal, then $B$ is normal.
2. If $\varphi$ is faithfully flat and $B$ is reduced, then $A$ is reduced; if $\varphi$ is
   faithfully flat and $B$ is normal, then $A$ is normal.

**Proof.** (1) Fix $\mathfrak Q\in\operatorname{Spec}B$, put $\mathfrak q=\mathfrak Q\cap A$ and
let $F$ be the closed fiber of $A_{\mathfrak q}\to B_{\mathfrak Q}$, a regular local ring by
Lemma 4.2. Lemma 2.12 gives $\dim B_{\mathfrak Q}=\dim A_{\mathfrak q}+\dim F$, and Lemma 4.4(1)
together with the Cohen–Macaulayness of $F$ — a regular system of parameters is a regular sequence
by Theorem 2.4 — gives
$\operatorname{depth}B_{\mathfrak Q}\geq\operatorname{depth}A_{\mathfrak q}+\dim F$.

Assume $A$ reduced, so $A$ satisfies $R_0$ and $S_1$. If $\dim B_{\mathfrak Q}=0$ then
$\dim A_{\mathfrak q}=0$, so $A_{\mathfrak q}$ is a field and $B_{\mathfrak Q}=F$ is a
zero-dimensional regular local ring, that is, a field: this is $R_0$ for $B$. For $S_1$: if
$\dim A_{\mathfrak q}\geq1$ then $\operatorname{depth}A_{\mathfrak q}\geq1$ and hence
$\operatorname{depth}B_{\mathfrak Q}\geq1$; if $\dim A_{\mathfrak q}=0$ then $A_{\mathfrak q}$ is a
field and $\operatorname{depth}B_{\mathfrak Q}\geq\dim F=\dim B_{\mathfrak Q}$. Either way
$\operatorname{depth}B_{\mathfrak Q}\geq\min(1,\dim B_{\mathfrak Q})$, so $B$ is reduced by Serre's
criterion.

Assume $A$ normal, so $A$ satisfies $R_1$ and $S_2$. If $\dim B_{\mathfrak Q}\leq1$ then
$\dim A_{\mathfrak q}\leq1$, so $A_{\mathfrak q}$ is regular and Proposition 2.15 makes
$B_{\mathfrak Q}$ regular: this is $R_1$. For $S_2$, if $\dim A_{\mathfrak q}\geq2$ then
$\operatorname{depth}B_{\mathfrak Q}\geq2$; otherwise
$\operatorname{depth}A_{\mathfrak q}=\dim A_{\mathfrak q}$ because $A_{\mathfrak q}$ is regular of
dimension at most one, and
$\operatorname{depth}B_{\mathfrak Q}\geq\dim A_{\mathfrak q}+\dim F= \dim B_{\mathfrak Q}$. In
both cases $\operatorname{depth}B_{\mathfrak Q}\geq\min(2,\dim B_{\mathfrak Q})$, so $B$ is
normal by Serre's criterion.

(2) A faithfully flat map is injective, so $A$ is reduced whenever $B$ is. Assume $B$ normal and
let $\mathfrak p\in\operatorname{Spec}A$. Choose $\mathfrak Q$ minimal among the primes of $B$
containing $\mathfrak pB$; such a prime exists because $\operatorname{Spec}B\to\operatorname{Spec}A$
is surjective, and its choice makes the closed fiber of the flat local map
$A_{\mathfrak p}\to B_{\mathfrak Q}$ artinian. Lemma 2.12 gives
$\dim B_{\mathfrak Q}=\dim A_{\mathfrak p}$ and Lemma 4.4(2) gives
$\operatorname{depth}B_{\mathfrak Q}=\operatorname{depth}A_{\mathfrak p}$. Hence $S_2$ for
$B_{\mathfrak Q}$ is $S_2$ for $A_{\mathfrak p}$; and if $\dim A_{\mathfrak p}\leq1$ then
$B_{\mathfrak Q}$ is regular by $R_1$ for $B$, so $A_{\mathfrak p}$ is regular by Corollary 2.11.
Serre's criterion applies. $\square$

Part (2) uses no hypothesis on the fibers: reducedness and normality always descend along a
faithfully flat map. Part (1) is where the fibers matter, and it is the statement that a regular
homomorphism cannot manufacture a singularity of any of the three kinds we track.

### 4.2 Composition, base change, and descent

The class of regular homomorphisms is stable under the three operations that a permanence argument
performs. Composition lets a chain of comparisons be collapsed into one; base change moves a known
regular map along an arbitrary map; descent recovers a regular map from a regular composite. All
three rest on Chapter 3: composition and base change on the stability of geometric regularity under
arbitrary field extensions, descent on Corollary 2.11.

**Proposition 4.6 (composition).** If $A\to B$ and $B\to C$ are regular homomorphisms of noetherian
rings, then $A\to C$ is regular.

**Proof.** The composite of flat maps is flat. Let $\mathfrak p\in\operatorname{Spec}A$ and let
$L/\kappa(\mathfrak p)$ be a finite extension; we must show that $C\otimes_AL$ is regular. Put
$B'=B\otimes_AL$ and $C'=C\otimes_AL=C\otimes_BB'$; both are noetherian, being finite free modules
over $B\otimes_A\kappa(\mathfrak p)$ and $C\otimes_A\kappa(\mathfrak p)$ respectively. Since
$B\otimes_A\kappa(\mathfrak p)$ is geometrically regular over $\kappa(\mathfrak p)$, the ring $B'$
is regular.

The map $B'\to C'$ is flat, being a base change of $B\to C$. Its fiber over a prime
$\mathfrak Q'$ of $B'$, lying over $\mathfrak Q\subseteq B$, is

$$
C\otimes_B\kappa(\mathfrak Q')=\big(C\otimes_B\kappa(\mathfrak Q)\big)
\otimes_{\kappa(\mathfrak Q)}\kappa(\mathfrak Q'),
$$

a localization of the noetherian ring $C'/\mathfrak Q'C'$, hence noetherian; it is regular by
Theorem 3.10, because $C\otimes_B\kappa(\mathfrak Q)$ is geometrically regular over
$\kappa(\mathfrak Q)$ and $\kappa(\mathfrak Q')$ is a field extension of $\kappa(\mathfrak Q)$.
Thus $B'\to C'$ is flat with regular fibers, and Corollary 2.17 transports regularity from $B'$ to
$C'$. $\square$

**Proposition 4.7 (base change).** Let $A\to B$ be regular and let $A\to A'$ be any homomorphism
with $A'$ and $B'=B\otimes_AA'$ noetherian. Then $A'\to B'$ is regular. In particular this applies
whenever $A\to A'$ is essentially of finite type, or $B$ is essentially of finite type over $A$ and
$A'$ is noetherian.

**Proof.** Flatness is preserved by base change. For
$\mathfrak p'\in\operatorname{Spec}A'$ with $\mathfrak p=\mathfrak p'\cap A$,

$$
B'\otimes_{A'}\kappa(\mathfrak p')
=\big(B\otimes_A\kappa(\mathfrak p)\big)\otimes_{\kappa(\mathfrak p)}\kappa(\mathfrak p'),
$$

which is noetherian, being a localization of $B'/\mathfrak p'B'$, and is geometrically regular over
$\kappa(\mathfrak p')$ by Theorem 3.10. $\square$

**Proposition 4.8 (descent).** Let $A\to B\to C$ be homomorphisms of noetherian rings with $B\to C$
faithfully flat. If $A\to C$ is regular, then $A\to B$ is regular.

**Proof.** _Flatness._ Let $M'\hookrightarrow M$ be an injection of $A$-modules. Applying
$-\otimes_AB$ and then the faithfully flat functor $-\otimes_BC$ produces
$M'\otimes_AC\to M\otimes_AC$, injective because $C$ is flat over $A$. Faithful flatness of
$B\to C$ then makes $M'\otimes_AB\to M\otimes_AB$ injective, so $B$ is flat over $A$.

_Fibers._ Fix $\mathfrak p\in\operatorname{Spec}A$ and a finite extension $L/\kappa(\mathfrak p)$.
The map $B\otimes_AL\to C\otimes_AL$ is faithfully flat, being a base change of $B\to C$, both
rings are noetherian, and $C\otimes_AL$ is regular by hypothesis. Corollary 2.11 makes
$B\otimes_AL$ regular. $\square$

It is worth noting how much Corollary 2.11 buys here: no hypothesis whatever is imposed on the map
$B\to C$ beyond faithful flatness. This is the form in which descent is used in Chapter 7, where
$C$ is a completion of a localization of a completion and nothing is known about its fibers over
$B$.

### 4.3 G-rings and their formal permanence

**Definition 4.9.** A noetherian ring $A$ is a **$G$-ring** if for every
$\mathfrak p\in\operatorname{Spec}A$ the completion map
$A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ is a regular homomorphism; equivalently, if all
formal fibers of $A$ in the sense of Definition 1.1 are geometrically regular.

The completion map is always flat, so the condition is exactly a condition on the formal fibers.
Two permanence statements are immediate from the shape of the definition, and it is worth being
explicit about how little they cost, since they carry a large part of the main theorem.

**Lemma 4.10 (localizations and quotients).** Let $A$ be a $G$-ring. Then $S^{-1}A$ is a $G$-ring
for every multiplicative set $S$, and $A/I$ is a $G$-ring for every ideal $I$.

**Proof.** The primes of $S^{-1}A$ are the primes $\mathfrak p$ of $A$ with
$\mathfrak p\cap S=\emptyset$, and $(S^{-1}A)_{\mathfrak p}=A_{\mathfrak p}$; so the formal fibers
of $S^{-1}A$ form a subfamily of those of $A$.

For a quotient, let $\bar{\mathfrak p}=\mathfrak p/I$ with $I\subseteq\mathfrak p$. Then
$(A/I)_{\bar{\mathfrak p}}=A_{\mathfrak p}/IA_{\mathfrak p}$ and, completion commuting with
quotients, $\widehat{(A/I)_{\bar{\mathfrak p}}}=\widehat{A_{\mathfrak p}}/I\widehat{A_{\mathfrak p}}$.
For a prime $\bar{\mathfrak q}\subseteq\bar{\mathfrak p}$, corresponding to
$\mathfrak q\supseteq I$, we have $\kappa(\bar{\mathfrak q})=\kappa(\mathfrak q)$ and

$$
\widehat{(A/I)_{\bar{\mathfrak p}}}\otimes_{(A/I)_{\bar{\mathfrak p}}}\kappa(\bar{\mathfrak q})
=\widehat{A_{\mathfrak p}}\otimes_{A_{\mathfrak p}}\kappa(\mathfrak q),
$$

because tensoring with $\kappa(\mathfrak q)$ already annihilates $I$. So the formal fibers of $A/I$
are literally formal fibers of $A$. $\square$

**Lemma 4.11 (generic-fiber criterion).** A noetherian ring $A$ is a $G$-ring if and only if for
every pair of primes $\mathfrak q\subseteq\mathfrak p$ the _generic_ formal fiber of the local
domain $(A/\mathfrak q)_{\mathfrak p/\mathfrak q}$ is geometrically regular over
$\operatorname{Frac}(A/\mathfrak q)$.

**Proof.** Write $\bar A=A/\mathfrak q$ and $\bar{\mathfrak p}=\mathfrak p/\mathfrak q$. Since
$\kappa(\mathfrak q)=\operatorname{Frac}(\bar A)$ is an $\bar A_{\bar{\mathfrak p}}$-algebra,

$$
\widehat{A_{\mathfrak p}}\otimes_{A_{\mathfrak p}}\kappa(\mathfrak q)
=\big(\widehat{A_{\mathfrak p}}/\mathfrak q\widehat{A_{\mathfrak p}}\big)
\otimes_{\bar A_{\bar{\mathfrak p}}}\operatorname{Frac}(\bar A)
=\widehat{\bar A_{\bar{\mathfrak p}}}\otimes_{\bar A_{\bar{\mathfrak p}}}\operatorname{Frac}(\bar A),
$$

using again that completion commutes with quotients. So the formal fibers of $A$ are exactly the
generic formal fibers of the local domains $(A/\mathfrak q)_{\mathfrak p/\mathfrak q}$. $\square$

The criterion is the standard reduction device: it replaces an arbitrary formal fiber by the one
fiber of a _local domain_ over its fraction field, which is where structure theory can be applied.

**Proposition 4.12 (finite algebras).** Let $A$ be a $G$-ring and $B$ a finite $A$-algebra. Then
$B$ is a $G$-ring.

**Proof.** Fix $\mathfrak Q\in\operatorname{Spec}B$ and put $\mathfrak q=\mathfrak Q\cap A$. By
Lemma 4.10 we may replace $A$ by $A_{\mathfrak q}$ and $B$ by $B\otimes_AA_{\mathfrak q}$, so $A$ is
local with maximal ideal $\mathfrak m$ and $B$ is a finite $A$-algebra, hence semilocal with
maximal ideals $\mathfrak Q_1,\ldots,\mathfrak Q_t$, all lying over $\mathfrak m$.

The $\mathfrak m$-adic completion of the finite $A$-module $B$ is $B\otimes_A\widehat A$, which is
therefore a finite $\widehat A$-algebra, noetherian, semilocal and complete; consequently it is the
product of its localizations at its maximal ideals, and those are the
$\mathfrak Q_i$-adic completions:

$$
B\otimes_A\widehat A\;\cong\;\prod_{i=1}^t\widehat{B_{\mathfrak Q_i}} .
$$

By Proposition 4.7 the base change $B\to B\otimes_A\widehat A$ of the regular map $A\to\widehat A$
is regular. Projection onto a factor of a finite product is a localization, hence a regular
homomorphism, so $B\to\widehat{B_{\mathfrak Q}}$ is regular by Proposition 4.6. Finally the fibers
of $B_{\mathfrak Q}\to\widehat{B_{\mathfrak Q}}$ are among the fibers of
$B\to\widehat{B_{\mathfrak Q}}$, since
$\widehat{B_{\mathfrak Q}}\otimes_B\kappa(\mathfrak q')= \widehat{B_{\mathfrak Q}}\otimes_{B_{\mathfrak Q}}\kappa(\mathfrak q')$
for $\mathfrak q'\subseteq\mathfrak Q$; and $B_{\mathfrak Q}\to\widehat{B_{\mathfrak Q}}$ is
flat. Hence it is regular. $\square$

**Theorem 4.13 (what the $G$-property delivers).** Let $A$ be a $G$-ring and
$\mathfrak p\in\operatorname{Spec}A$. Then $A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ is a
faithfully flat regular homomorphism, and consequently:

1. $A_{\mathfrak p}$ is regular if and only if $\widehat{A_{\mathfrak p}}$ is regular;
2. $A_{\mathfrak p}$ is reduced if and only if $\widehat{A_{\mathfrak p}}$ is reduced;
3. $A_{\mathfrak p}$ is normal if and only if $\widehat{A_{\mathfrak p}}$ is normal;
4. every formal fiber of $A$ is regular, reduced and normal.

**Proof.** Statement (1) is Proposition 4.3, and (2), (3) combine the two halves of
Proposition 4.5, the forward implications using regularity of the map and the reverse ones only
its faithful flatness. Statement (4) is Corollary 3.12 applied to the fibers. $\square$

Theorem 4.13 is the entire practical content of the $G$-property: completion becomes a faithful
probe of the local structure. What is still missing is any supply of $G$-rings beyond the trivial
ones, and any indication that the class is stable under finite-type extension. Chapter 5 develops
the classical instrument for producing them — formal smoothness — and Chapter 6 supplies the base
case, by an elementary route which in the end bypasses that instrument; both are recorded, since
the formal calculus is what explains why the base case is the only difficulty.

## 5. Formal smoothness

Geometric regularity of a fiber is a statement about a ring; it is verified by computing
dimensions and cotangent spaces, and it does not obviously propagate. Formal smoothness is a
statement about _maps out of_ a ring — every homomorphism into a quotient by a square-zero ideal
extends — and statements of that shape propagate for free: they compose, they base change, they
localize, they survive completion, because in each case one simply chains or transports lifting
problems. Grothendieck's theorem is that for local homomorphisms of noetherian local rings the two
notions coincide. The theorem thus converts a rigid geometric condition into a flexible formal
one. It is the classical mechanism behind the permanence theory of $G$-rings, and although the
proofs of Chapters 6 to 10 take an elementary route that does not invoke it, it is what makes the
shape of those proofs intelligible: it identifies precisely which step can carry content.

This chapter develops the formal side. Section 5.1 sets up the lifting problem in the adic
category — the only version usable for complete local rings, where all maps must be continuous —
and proves the permanence properties, all of which are short. It ends with the two facts that
Book 1, Chapter 13, contributes: a field is formally smooth over its prime field, and a Cohen ring
is formally smooth over the $p$-adic integers. Section 5.2 records the derivation calculus that
measures the ambiguity in a lift and derives from it the criterion by which a formally smooth
algebra over a base is recognized as formally smooth over an intermediate ring.

### 5.1 The lifting problem in the adic category

**Definition 5.1.** Let $\Lambda$ be a noetherian ring with a chosen ideal $J$, and let $B$ be a
noetherian $\Lambda$-algebra with a chosen ideal $\mathfrak b\supseteq JB$. We call $B$
**formally smooth over $(\Lambda,J)$ for the $\mathfrak b$-adic topology** if the following lifting
property holds. Let $R$ be a $\Lambda$-algebra with $J^nR=0$ for some $n\geq1$, let $I\subseteq R$
be an ideal with $I^2=0$, write $\pi:R\to R/I$ for the quotient map, and let $u:B\to R/I$ be a
$\Lambda$-algebra homomorphism with $u(\mathfrak b^m)=0$ for some $m\geq1$. Then there exists a
$\Lambda$-algebra homomorphism $v:B\to R$ with $\pi\circ v=u$.

Taking $J=0$ and $\mathfrak b=0$ recovers the familiar notion for discrete rings: every
homomorphism to $R/I$ lifts. The ideals $J$ and $\mathfrak b$ record topologies, and their only
role is to restrict the lifting problems that must be solved: only $\Lambda$-algebras on which $J$
acts nilpotently, and only homomorphisms killing a power of $\mathfrak b$, are tested. Two remarks
make the definition easier to use.

_Lifts are automatically continuous._ If $u(\mathfrak b^m)=0$ and $\pi v=u$, then
$v(\mathfrak b^m)\subseteq I$, hence $v(\mathfrak b^{2m})\subseteq I^2=0$. In particular $v$
factors through $B/\mathfrak b^{2m}$.

_A finer topology on $B$ is a weaker hypothesis._ If $\mathfrak b\subseteq\mathfrak b'$ then any
$u$ killing a power of $\mathfrak b'$ kills a power of $\mathfrak b$; so formal smoothness for the
$\mathfrak b$-adic topology implies formal smoothness for the $\mathfrak b'$-adic topology. We use
this silently when passing from an ideal to a larger one, for instance from $\mathfrak bB'$ to a
maximal ideal of a localization $B'$ of $B$.

**Lemma 5.2 (composition).** Let $\Lambda\to B\to C$ with ideals $J\subseteq\Lambda$,
$\mathfrak b\subseteq B$, $\mathfrak c\subseteq C$ satisfying $JB\subseteq\mathfrak b$ and
$\mathfrak bC\subseteq\mathfrak c$. If $B$ is formally smooth over $(\Lambda,J)$ for the
$\mathfrak b$-adic topology and $C$ is formally smooth over $(B,\mathfrak b)$ for the
$\mathfrak c$-adic topology, then $C$ is formally smooth over $(\Lambda,J)$ for the
$\mathfrak c$-adic topology.

**Proof.** Let $R$, $I$, $u:C\to R/I$ be a lifting problem for $C$ over $\Lambda$, with
$J^nR=0$ and $u(\mathfrak c^m)=0$. The composite $u_B:B\to C\to R/I$ is a $\Lambda$-algebra
homomorphism killing $\mathfrak b^m$, because $\mathfrak b^mC\subseteq\mathfrak c^m$, so it lifts
to a $\Lambda$-algebra homomorphism $w:B\to R$. Then $w(\mathfrak b^{2m})=0$, so $R$ is a
$B$-algebra via $w$ on which $\mathfrak b$ acts nilpotently, and $u$ is a $B$-algebra homomorphism
$C\to R/I$ for these structures, since $\pi w=u_B$. Formal smoothness of $C$ over $B$ produces a
$B$-algebra lift $v:C\to R$, which is in particular a $\Lambda$-algebra lift of $u$. $\square$

**Lemma 5.3 (base change).** Let $B$ be formally smooth over $(\Lambda,J)$ for the
$\mathfrak b$-adic topology and let $\Lambda\to\Lambda'$ be a homomorphism to a noetherian ring
with an ideal $J'\supseteq J\Lambda'$. Suppose $B'=B\otimes_\Lambda\Lambda'$ is noetherian and let
$\mathfrak b'\subseteq B'$ be an ideal containing $\mathfrak bB'+J'B'$. Then $B'$ is formally
smooth over $(\Lambda',J')$ for the $\mathfrak b'$-adic topology.

**Proof.** Given $R'$ a $\Lambda'$-algebra with $(J')^nR'=0$, a square-zero ideal $I'\subseteq R'$
and a $\Lambda'$-algebra homomorphism $u':B'\to R'/I'$ killing $(\mathfrak b')^m$, restrict along
$B\to B'$ to get a $\Lambda$-algebra homomorphism $u:B\to R'/I'$ killing $\mathfrak b^m$; note
$J^nR'\subseteq(J')^nR'=0$. Lift $u$ to a $\Lambda$-algebra homomorphism $v:B\to R'$. The pair
consisting of $v$ and the structure map $\Lambda'\to R'$ defines a $\Lambda'$-algebra
homomorphism $B'=B\otimes_\Lambda\Lambda'\to R'$, which reduces to $u'$ because both agree on the
images of $B$ and of $\Lambda'$. $\square$

**Lemma 5.4 (localization).** Let $B$ be formally smooth over $(\Lambda,J)$ for the
$\mathfrak b$-adic topology and let $S\subseteq B$ be a multiplicative set. Then $S^{-1}B$ is
formally smooth over $(\Lambda,J)$ for the $\mathfrak b S^{-1}B$-adic topology, hence also for the
$\mathfrak b'$-adic topology for any larger ideal $\mathfrak b'$.

**Proof.** Let $u:S^{-1}B\to R/I$ kill $(\mathfrak bS^{-1}B)^m$. Its restriction to $B$ kills
$\mathfrak b^m$ and lifts to $v_0:B\to R$. For $s\in S$ the element $u(s/1)$ is a unit of $R/I$,
so $v_0(s)$ is a unit modulo the nilpotent ideal $I$ and therefore a unit of $R$. Hence $v_0$
extends uniquely to $v:S^{-1}B\to R$, and $\pi v=u$ because both are homomorphisms agreeing on
$B$ and on inverses of elements of $S$. $\square$

**Lemma 5.5 (polynomial algebras).** $B=\Lambda[y_1,\ldots,y_m]$ is formally smooth over
$(\Lambda,J)$ for the $\mathfrak b$-adic topology, for any ideal $\mathfrak b\supseteq JB$.

**Proof.** Choose any preimages in $R$ of the elements $u(y_j)$ and let $v$ be the
$\Lambda$-algebra homomorphism sending $y_j$ to them. $\square$

**Lemma 5.6 (power series algebras).** Let $B$ be formally smooth over $(\Lambda,J)$ for the
$\mathfrak b$-adic topology and suppose $B$ is $\mathfrak b$-adically complete. Then
$B[[x_1,\ldots,x_n]]$ is formally smooth over $(\Lambda,J)$ for the
$(\mathfrak b,x_1,\ldots,x_n)$-adic topology.

**Proof.** Write $\mathfrak c=(\mathfrak b,x_1,\ldots,x_n)$ and let $u:B[[x]]\to R/I$ kill
$\mathfrak c^m$, with $J^nR=0$ and $I^2=0$. Restricting $u$ to $B$ gives a $\Lambda$-algebra
homomorphism killing $\mathfrak b^m$, which lifts to $w:B\to R$. Choose $r_i\in R$ lifting
$u(x_i)$. Since $u(x_i^m)=0$ we get $r_i^m\in I$ and hence $r_i^{2m}=0$, so all $r_i$ are
nilpotent and the ideal $(r_1,\ldots,r_n)R$ is nilpotent, say $(r)^N=0$. Therefore the assignment
$\sum_\alpha b_\alpha x^\alpha\mapsto\sum_{|\alpha|<N}w(b_\alpha)r^\alpha$ is a finite sum and
defines a ring homomorphism $v:B[[x]]\to R$: it factors through $B[[x]]/(x)^N=B[x]/(x)^N$, where
it is the ordinary evaluation homomorphism. Both $\pi v$ and $u$ factor through
$B[x]/(x)^{\max(N,m)}$ and agree on $B$ and on the $x_i$, so $\pi v=u$. $\square$

**Lemma 5.7 (completion).** Let $B$ be formally smooth over $(\Lambda,J)$ for the
$\mathfrak b$-adic topology and let $\widehat B$ be the $\mathfrak b$-adic completion, with
$\widehat{\mathfrak b}=\mathfrak b\widehat B$. Then $\widehat B$ is formally smooth over
$(\Lambda,J)$ for the $\widehat{\mathfrak b}$-adic topology.

**Proof.** Let $u:\widehat B\to R/I$ kill $\widehat{\mathfrak b}^m$. Its restriction along
$B\to\widehat B$ kills $\mathfrak b^m$, hence lifts to $v_0:B\to R$, and $v_0(\mathfrak b^{2m})=0$,
so $v_0$ factors through $B/\mathfrak b^{2m}=\widehat B/\widehat{\mathfrak b}^{2m}$ and yields
$v:\widehat B\to R$. Both $\pi v$ and $u$ factor through
$\widehat B/\widehat{\mathfrak b}^{2m}$ and agree on the image of $B$, which generates that
quotient; hence $\pi v=u$. $\square$

The five lemmas above are the entire permanence theory, and none of them used anything but the
definition. What they need in order to say something is a supply of formally smooth algebras.
Book 1, Chapter 13, provides exactly the two that Cohen's structure theory requires.

**Theorem 5.8 (coefficient rings are formally smooth).**

1. Every field $K$ is formally smooth over its prime field, with the discrete topologies.
2. Every Cohen ring $C$ for a field $k$ of characteristic $p$ is formally smooth over
   $(\mathbf Z,p\mathbf Z)$ for the $p$-adic topology.
3. Consequently $K[[x_1,\ldots,x_n]]$ is formally smooth over the prime field of $K$ for its
   maximal-adic topology, and $C[[x_1,\ldots,x_n]]$ is formally smooth over
   $(\mathbf Z,p\mathbf Z)$ for its maximal-adic topology; and so is any localization of a
   polynomial algebra over either of them, for any adic topology finer than the one induced.

**Proof.** (1) In characteristic $p$ this is Book 1, Theorem 13.13: for a ring $R$ with $pR=0$, a
square-zero ideal $I$, a homomorphism $\psi:K\to R/I$ and any choice of lifts of the images of a
$p$-basis of $K$, there is a (unique) lift $K\to R$. A $\Lambda=\mathbf F_p$-algebra satisfies
$pR=0$ automatically, so this is exactly the required lifting property.

In characteristic zero the prime field is $\mathbf Q$ and $R/I$ is a $\mathbf Q$-algebra; since
$I^2=0$, every integer $n\neq0$ acts invertibly on $R$ as well, so $R$ is a $\mathbf Q$-algebra.
Consider pairs $(L,\varphi)$ with $\mathbf Q\subseteq L\subseteq K$ a subfield and
$\varphi:L\to R$ a ring homomorphism lifting $\psi|_L$, ordered by extension. The pair
$(\mathbf Q,\text{structure map})$ is one, and unions of chains are again such pairs, so Zorn's
lemma provides a maximal $(L,\varphi)$. Suppose $a\in K\setminus L$. Note first that $\psi$, being
a homomorphism from a field, carries nonzero elements to units, so $\varphi$ carries nonzero
elements to units of $R$. If $a$ is transcendental over $L$, choose any $r\in R$ lifting
$\psi(a)$; the homomorphism $L[X]\to R$, $X\mapsto r$, carries every nonzero $f$ to an element
whose reduction $\psi(f(a))$ is a unit, hence to a unit, and therefore extends to $L(a)$. If $a$
is algebraic over $L$ with minimal polynomial $g$, then $g'(a)\neq0$ because
$\operatorname{char}=0$; choose $r_0\in R$ lifting $\psi(a)$, so that $\varphi(g)(r_0)\in I$ and
$\varphi(g')(r_0)$ is a unit, and set

$$
r=r_0-\frac{\varphi(g)(r_0)}{\varphi(g')(r_0)} .
$$

Expanding and using $I^2=0$ gives $\varphi(g)(r)=0$, so $\varphi$ extends to
$L[X]/(g)=L(a)$. Either way $(L,\varphi)$ was not maximal, a contradiction; hence $L=K$.

(2) This is Book 1, Theorem 13.24: for a ring $R$ with $p^M=0$ and a square-zero ideal $I$, every
homomorphism $C\to R/I$ lifts to $R$. A $\mathbf Z$-algebra with $(p\mathbf Z)^nR=0$ is precisely
a ring with $p^n=0$.

(3) Combine (1) or (2) with Lemma 5.6, then with Lemmas 5.5, 5.4 and 5.2, and finally with the
remark that a finer adic topology on the source is a weaker requirement. $\square$

### 5.2 Differentials and the relative criterion

A lifting problem, once solvable, is solvable in many ways, and the ambiguity is measured by
derivations. This is the standard calculus attached to square-zero extensions, and it is what lets
one _correct_ a lift that is not of the required kind — for instance a lift which is a
homomorphism over $\Lambda$ but not over an intermediate ring $B$.

Throughout, $\operatorname{Der}_\Lambda(B,M)$ denotes the module of $\Lambda$-derivations
$B\to M$, canonically identified with $\operatorname{Hom}_B(\Omega_{B/\Lambda},M)$.

**Lemma 5.9 (lifts form a torsor under derivations).** Let $\Lambda\to B$ be a ring homomorphism,
$R$ a $\Lambda$-algebra, $I\subseteq R$ an ideal with $I^2=0$, and $u:B\to R/I$ a
$\Lambda$-algebra homomorphism. Regard $I$ as a $B$-module through $u$.

1. If $v,v':B\to R$ are $\Lambda$-algebra homomorphisms lifting $u$, then $v-v'$ is a
   $\Lambda$-derivation $B\to I$.
2. If $v$ lifts $u$ and $D\in\operatorname{Der}_\Lambda(B,I)$, then $v+D$ is a $\Lambda$-algebra
   homomorphism lifting $u$.

**Proof.** For (1), $\delta=v-v'$ takes values in $I$ and is $\Lambda$-linear; writing
$v=v'+\delta$ and expanding $v(bb')=v(b)v(b')$ gives
$\delta(bb')=v'(b)\delta(b')+v'(b')\delta(b)$, because $\delta(b)\delta(b')\in I^2=0$, and
$v'(b)$ acts on $I$ as $u(b)$ does. This is the Leibniz rule. For (2), the same computation run
backwards shows that $v+D$ is multiplicative; it is additive and $\Lambda$-linear, and reduces to
$u$ because $D$ has values in $I$. $\square$

The correction mechanism yields the criterion we need. It is stated as a sufficient condition,
which is the direction used in the sequel.

**Proposition 5.10 (relative criterion).** Let $\Lambda\to B\to C$ be homomorphisms of noetherian
rings with ideals $J\subseteq\Lambda$, $\mathfrak b\subseteq B$, $\mathfrak c\subseteq C$
satisfying $JB\subseteq\mathfrak b$ and $\mathfrak bC\subseteq\mathfrak c$. Assume:

1. $C$ is formally smooth over $(\Lambda,J)$ for the $\mathfrak c$-adic topology;
2. for every $C$-module $I$ annihilated by a power of $\mathfrak c$, the restriction map

$$
\operatorname{Der}_\Lambda(C,I)\longrightarrow\operatorname{Der}_\Lambda(B,I)
$$

is surjective.

Then $C$ is formally smooth over $(B,\mathfrak b)$ for the $\mathfrak c$-adic topology.

**Proof.** Let $R$ be a $B$-algebra with $\mathfrak b^nR=0$, let $I\subseteq R$ satisfy $I^2=0$,
and let $u:C\to R/I$ be a $B$-algebra homomorphism with $u(\mathfrak c^m)=0$. Write
$\sigma:B\to R$ for the structure map. Since $JB\subseteq\mathfrak b$ we have $J^nR=0$, so
hypothesis (1) applies and produces a $\Lambda$-algebra homomorphism $v_0:C\to R$ with
$\pi v_0=u$.

Give $I$ the $C$-module structure coming from $u$; it is annihilated by $\mathfrak c^m$. The two
$\Lambda$-algebra homomorphisms $v_0|_B$ and $\sigma$ from $B$ to $R$ have the same reduction
modulo $I$, namely the composite $B\to C\xrightarrow{u}R/I$, which equals $\pi\sigma$ because $u$
is a $B$-algebra map. By Lemma 5.9(1) their difference
$\delta=v_0|_B-\sigma$ is a $\Lambda$-derivation $B\to I$. Hypothesis (2) provides
$D\in\operatorname{Der}_\Lambda(C,I)$ with $D|_B=\delta$, and Lemma 5.9(2) makes $v=v_0-D$ a
$\Lambda$-algebra homomorphism lifting $u$. Finally $v|_B=v_0|_B-\delta=\sigma$, so $v$ is a
homomorphism of $B$-algebras. $\square$

**Corollary 5.11 (completions).** Let $B$ be a noetherian ring with an ideal $\mathfrak b$, let
$\widehat B$ be its $\mathfrak b$-adic completion and
$\widehat{\mathfrak b}=\mathfrak b\widehat B$, and let $\Lambda$, $J$ be as above with
$JB\subseteq\mathfrak b$. If $\widehat B$ is formally smooth over $(\Lambda,J)$ for the
$\widehat{\mathfrak b}$-adic topology, then $\widehat B$ is formally smooth over
$(B,\mathfrak b)$ for the $\widehat{\mathfrak b}$-adic topology.

**Proof.** We verify hypothesis (2) of Proposition 5.10, and in fact the restriction map is
surjective for a trivial reason: _every_ $\Lambda$-derivation of $B$ into a module annihilated by
a power of $\widehat{\mathfrak b}$ is continuous. Let $I$ be a $\widehat B$-module with
$\widehat{\mathfrak b}^nI=0$ and let $\delta:B\to I$ be a $\Lambda$-derivation. For
$b_1,\ldots,b_{2n}\in\mathfrak b$ the Leibniz rule gives

$$
\delta(b_1\cdots b_{2n})=\sum_{i}\Big(\prod_{j\neq i}b_j\Big)\delta(b_i)
\in\mathfrak b^{2n-1}I=0,
$$

since $2n-1\geq n$. Hence $\delta$ kills $\mathfrak b^{2n}$ and factors through a
$\Lambda$-derivation $B/\mathfrak b^{2n}\to I$, the Leibniz rule descending because $I$ is a
module over $B/\mathfrak b^{2n}$. Composing with the ring homomorphism
$\widehat B\to\widehat B/\widehat{\mathfrak b}^{2n}=B/\mathfrak b^{2n}$ gives a
$\Lambda$-derivation $\widehat B\to I$ restricting to $\delta$ on $B$. $\square$

It is worth being precise about what Corollary 5.11 does and does not say, because the point is
easy to misread. Take $B$ to be a noetherian local ring, $\mathfrak b$ its maximal ideal, and
suppose $\widehat B$ is a power series ring over a field — as it is whenever $B$ is a regular local
ring containing a field. Then Theorem 5.8 makes $\widehat B$ formally smooth over the prime field,
and Corollary 5.11 makes $\widehat B$ formally smooth over $B$. By the criterion of Section 5.3
this will mean that $B\to\widehat B$ is flat with geometrically regular _closed_ fiber — which is
no information at all, the closed fiber being the residue field.

The $G$-property is a statement about the _other_ primes. It requires, for each prime
$\mathfrak Q$ of $\widehat B$ over a prime $\mathfrak q$ of $B$, that the local homomorphism
$B_{\mathfrak q}\to\widehat B_{\mathfrak Q}$ be flat with geometrically regular closed fiber,
equivalently that $\widehat B_{\mathfrak Q}$ be formally smooth over $B_{\mathfrak q}$. Localizing
preserves formal smoothness over $\Lambda$ by Lemma 5.4, so hypothesis (1) of Proposition 5.10
remains available; but the modules $I$ that now occur are annihilated by a power of
$\mathfrak Q\widehat B_{\mathfrak Q}$ and not by a power of the maximal ideal of $\widehat B$, so
the derivations to be extended are no longer continuous and the argument of Corollary 5.11
collapses. Extending them is the real content of the theory, and it is where the structure of the
rings in question — not merely their topology — has to be used. Section 5.3 supplies the
translation between formal smoothness and geometric regularity, and Chapter 6 does the work.

### 5.3 Grothendieck's criterion

We now convert formal smoothness back into geometry. The statement to be proved is that a
noetherian local algebra which is formally smooth over a field is geometrically regular over it;
combined with base change along $A\to k$, this says that a formally smooth local homomorphism has
geometrically regular closed fiber, which is the form Chapter 6 consumes.

Two comments on scope, made here rather than buried later. First, formal smoothness of a local
homomorphism also forces flatness; we neither prove nor use this, because in every application
below the map is a localization or a completion, whose flatness is known independently. Second,
the converse implication — that a flat local homomorphism with geometrically regular closed fiber
is formally smooth — is a classical theorem of Cohen and Grothendieck. It is _not_ proved in this
book and is _not_ used anywhere in it: every application runs in the direction proved here, from
formal smoothness, which is established for the rings of Chapter 6 by the lifting theorems of
Book 1 and the permanence of Section 5.1. Nothing later depends on the converse.

The proof of the main proposition is short, and its mechanism is worth stating in advance. Present
the completion of the ring as $S/\mathfrak a$ with $S$ a power series ring over a coefficient
field, chosen so that $\mathfrak a\subseteq\mathfrak m_S^2$. Formal smoothness produces, at each
finite level, a section of the presentation; comparing that section with the presentation itself
gives a derivation of $S$ which is the identity on $\mathfrak a$. But a derivation moves
$\mathfrak m_S^2$ into $\mathfrak m_S$ times the target, so the identity on $\mathfrak a$ lands in
a proper submodule, and Nakayama forces $\mathfrak a$ to vanish.

**Proposition 5.12 (formally smooth over a field implies geometrically regular).** Let $k$ be a
field and $(C,\mathfrak n,\ell)$ a noetherian local $k$-algebra which is formally smooth over
$(k,0)$ for the $\mathfrak n$-adic topology. Then $C$ is geometrically regular over $k$.

**Proof.** _Step 1: reduction to regularity._ Suppose it is known that every noetherian local
algebra formally smooth over a field is regular. Let $K/k$ be a finite field extension. Then
$C_K=C\otimes_kK$ is a finite free $C$-module, hence noetherian and semilocal, and it is formally
smooth over $(K,0)$ for the $\mathfrak nC_K$-adic topology by Lemma 5.3. For each maximal ideal
$\mathfrak m'$ of $C_K$, the localization $(C_K)_{\mathfrak m'}$ is formally smooth over $K$ for
the $\mathfrak nC_K$-adic topology by Lemma 5.4, hence also for the finer $\mathfrak m'$-adic
topology. By the assumed statement each $(C_K)_{\mathfrak m'}$ is regular, so $C_K$ is regular by
Corollary 2.10. As $K$ was an arbitrary finite extension, $C$ is geometrically regular over $k$.

_Step 2: reduction to the complete case._ The completion $\widehat C$ is formally smooth over
$(k,0)$ for the $\mathfrak n\widehat C$-adic topology by Lemma 5.7. The map $C\to\widehat C$ is
flat and local with closed fiber the field $\ell$, so Proposition 2.15 shows that $C$ is regular if
and only if $\widehat C$ is. We may therefore assume $C$ complete.

_Step 3: a minimal presentation._ $C$ contains the field $k$, so by Book 1, Theorem 13.15 it has a
coefficient field $L$, and by Book 1, Theorem 13.30 the evaluation homomorphism

$$
\rho:S=L[[z_1,\ldots,z_N]]\twoheadrightarrow C,\qquad z_i\longmapsto c_i,
$$

is surjective, where $c_1,\ldots,c_N$ is a _minimal_ generating set of $\mathfrak n$, so that
$N=\dim_\ell\mathfrak n/\mathfrak n^2$. Put $\mathfrak a=\ker\rho$ and let $\mathfrak m_S$ be the
maximal ideal of $S$. Since $\mathfrak m_S/\mathfrak m_S^2$ has dimension $N$ over $\ell$ and
$\mathfrak n/\mathfrak n^2=\mathfrak m_S/(\mathfrak m_S^2+\mathfrak a)$ also has dimension $N$, we
get

$$
\mathfrak a\subseteq\mathfrak m_S^2 .
\tag{5.1}
$$

The ring $S$ is a complete regular local ring of dimension $N$ by Book 1, Lemma 13.29, and it is a
domain; so $C=S/\mathfrak a$ is regular if and only if $\mathfrak a=0$. Note that $L$ need not
contain $k$, and no such compatibility will be required.

_Step 4: sections at finite level._ Fix $n\geq1$ and set

$$
S_n=S/(\mathfrak a^2+\mathfrak m_S^n),\qquad
K_n=(\mathfrak a+\mathfrak m_S^n)/(\mathfrak a^2+\mathfrak m_S^n)\subseteq S_n .
$$

Then $K_n^2=0$, because $(\mathfrak a+\mathfrak m_S^n)^2\subseteq\mathfrak a^2+\mathfrak m_S^n$,
and $S_n/K_n=S/(\mathfrak a+\mathfrak m_S^n)=C/\mathfrak n^n$. Moreover $K_n$ is generated as an
$S$-module by the image of $\mathfrak a$, since $\mathfrak m_S^n$ maps to zero in $K_n$.

Before applying formal smoothness we must make $S_n$ a $k$-algebra compatibly. The ring
homomorphism $k\to C\to C/\mathfrak n^n=S_n/K_n$ lifts to a ring homomorphism $\tau_n:k\to S_n$ by
Theorem 5.8(1): the field $k$ is formally smooth over its prime field, $K_n$ has square zero, and
$S_n$ is an algebra over that prime field, being a quotient of $S$, whose characteristic equals
that of $\ell$ and hence of $k$. Give $S_n$ the $k$-algebra structure $\tau_n$; then
$S_n/K_n=C/\mathfrak n^n$ carries its original $k$-algebra structure, and the projection
$u:C\to C/\mathfrak n^n$ is a $k$-algebra homomorphism killing $\mathfrak n^n$. Formal smoothness
of $C$ over $(k,0)$ for the $\mathfrak n$-adic topology therefore yields a $k$-algebra
homomorphism

$$
v_n:C\longrightarrow S_n,\qquad v_n\ \text{lifting}\ u .
$$

_Step 5: the derivation._ Let $\nu_n:S\to S_n$ be the natural projection and
$w_n=v_n\circ\rho:S\to S_n$. Both are ring homomorphisms, and both reduce modulo $K_n$ to the
composite $S\xrightarrow{\rho}C\to C/\mathfrak n^n$. By Lemma 5.9(1), applied with $\Lambda$ the
prime ring, the difference

$$
\delta_n=\nu_n-w_n:S\longrightarrow K_n
$$

is a derivation. For $j\in\mathfrak a$ we have $\rho(j)=0$, hence $w_n(j)=v_n(0)=0$, while
$\nu_n(j)$ is the class $\bar j$ of $j$ in $K_n$. Thus

$$
\delta_n(j)=\bar j\qquad\text{for all }j\in\mathfrak a .
\tag{5.2}
$$

_Step 6: Nakayama._ By $(5.1)$ every $j\in\mathfrak a$ is a finite sum of products $st$ with
$s,t\in\mathfrak m_S$, so the Leibniz rule gives
$\delta_n(j)=\sum(s\,\delta_n(t)+t\,\delta_n(s))\in\mathfrak m_SK_n$. Combined with $(5.2)$ and
with the fact that the classes $\bar j$ generate $K_n$, this yields $K_n=\mathfrak m_SK_n$. The
module $K_n$ is finite over the noetherian local ring $S$, so Nakayama gives $K_n=0$, that is,

$$
\mathfrak a\subseteq\mathfrak a^2+\mathfrak m_S^n\qquad\text{for every }n\geq1 .
$$

The submodule $\mathfrak a^2$ is closed in the $\mathfrak m_S$-adic topology of the complete local
ring $S$, by the Krull intersection theorem applied to $\mathfrak a/\mathfrak a^2$; hence
$\mathfrak a=\mathfrak a^2$, and Nakayama once more gives $\mathfrak a=0$. Therefore $C\cong S$ is
regular, which completes Step 1 and the proof. $\square$

**Theorem 5.13 (Grothendieck's criterion, the direction used here).** Let
$\varphi:(A,\mathfrak m,k)\to(B,\mathfrak n)$ be a local homomorphism of noetherian local rings
and suppose that $B$ is formally smooth over $(A,\mathfrak m)$ for the $\mathfrak n$-adic
topology. Then the closed fiber $B/\mathfrak mB$ is geometrically regular over $k$. If in addition
$\varphi$ is flat, then $\varphi$ is regular at the closed point in the sense of Definition 4.1.

**Proof.** Apply Lemma 5.3 with $\Lambda=A$, $J=\mathfrak m$, $\Lambda'=k=A/\mathfrak m$ and
$J'=0$: the ring $B\otimes_Ak=B/\mathfrak mB$ is noetherian local and formally smooth over
$(k,0)$ for the adic topology of its maximal ideal. Proposition 5.12 makes it geometrically
regular over $k$. $\square$

**Corollary 5.14 (pointwise form).** Let $\varphi:A\to B$ be a flat homomorphism of noetherian
rings and suppose that for every $\mathfrak Q\in\operatorname{Spec}B$, with
$\mathfrak q=\mathfrak Q\cap A$, the local ring $B_{\mathfrak Q}$ is formally smooth over
$(A_{\mathfrak q},\mathfrak qA_{\mathfrak q})$ for the $\mathfrak QB_{\mathfrak Q}$-adic topology.
Then $\varphi$ is a regular homomorphism.

**Proof.** Theorem 5.13 applied to each $A_{\mathfrak q}\to B_{\mathfrak Q}$ gives geometric
regularity of every closed fiber, and Lemma 4.2 assembles these into regularity of $\varphi$.
$\square$

### 5.4 Separable extensions are formally smooth

Section 5.3 converted formal smoothness into geometric regularity. The converse conversion needs
one substantial input, and it concerns fields alone: a separable field extension must be formally
smooth. This is Cohen's theorem, and with the $p$-basis machinery of Book 1, Section 13.3, and of
Chapter 3 it has a short proof. The mechanism is the one already used for coefficient fields: in
characteristic $p$ a homomorphism out of a field into a square-zero extension is _uniquely_
determined by the images of a $p$-basis, so one lifts a $p$-basis of the big field in such a way
that the prescribed lifts on the base field are respected — which is possible precisely because
separability makes a $p$-basis of the base field part of a $p$-basis of the extension.

We first record the converse of Lemma 5.7, which is what allows a statement about complete rings to
be used for incomplete ones.

**Lemma 5.15 (descending formal smoothness along a completion).** Let $B$ be a noetherian ring
with an ideal $\mathfrak b$ and let $\widehat B$ be its $\mathfrak b$-adic completion. If
$\widehat B$ is formally smooth over $(\Lambda,J)$ for the $\mathfrak b\widehat B$-adic topology,
then so is $B$ for the $\mathfrak b$-adic topology.

**Proof.** Let $u:B\to R/I$ be a $\Lambda$-algebra homomorphism killing $\mathfrak b^m$, with
$J^nR=0$ and $I^2=0$. Then $u$ factors through $B/\mathfrak b^m=\widehat B/\mathfrak b^m\widehat B$,
hence extends to a $\Lambda$-algebra homomorphism $\widehat u:\widehat B\to R/I$ killing
$\mathfrak b^m\widehat B$. A lift $\widehat v:\widehat B\to R$ exists by hypothesis, and its
restriction to $B$ lifts $u$. $\square$

**Theorem 5.16 (Cohen's separability theorem).** Let $L/k$ be a separable extension of fields in
the sense of Definition 3.1. Then $L$ is formally smooth over $k$ for the discrete topologies:
for every $k$-algebra $R$, every ideal $I\subseteq R$ with $I^2=0$ and every $k$-algebra
homomorphism $\psi:L\to R/I$, there is a $k$-algebra homomorphism $\varphi:L\to R$ with
$\pi\circ\varphi=\psi$.

**Proof.** Suppose first that $\operatorname{char}k=p>0$; then $pR=0$, since $R$ is a $k$-algebra.
Choose a $p$-basis $B_k$ of $k$. Because $L/k$ is separable, Proposition 3.4(1) shows that every
finite subset of $B_k$ remains $p$-independent in $L$, and $p$-independence is a condition on
finite subsets, so the image of $B_k$ in $L$ is $p$-independent. By Book 1, Lemma 13.10, it is
contained in a $p$-basis $B_L$ of $L$.

Write $\sigma:k\to R$ for the structure map, so that $\pi\circ\sigma=\psi|_k$ because $\psi$ is a
$k$-algebra homomorphism. Choose lifts of the images of the $p$-basis $B_L$ as follows: for
$b\in B_k$ take $\beta_b=\sigma(b)$, which is a lift of $\psi(b)$; for $b\in B_L\setminus B_k$
take any lift $\beta_b\in R$ of $\psi(b)$. Book 1, Theorem 13.13, applied to the field $L$ with
$p$-basis $B_L$, produces a ring homomorphism

$$
\varphi:L\longrightarrow R,\qquad \pi\circ\varphi=\psi,\qquad\varphi(b)=\beta_b\ (b\in B_L).
$$

It remains to see that $\varphi$ is a $k$-algebra homomorphism, that is, $\varphi|_k=\sigma$. Both
$\varphi|_k$ and $\sigma$ are ring homomorphisms $k\to R$ whose composition with $\pi$ is
$\psi|_k$, and both send $b\in B_k$ to $\sigma(b)$. The uniqueness clause of Book 1,
Theorem 13.13, applied this time to the field $k$ with $p$-basis $B_k$, gives $\varphi|_k=\sigma$.

Now suppose $\operatorname{char}k=0$. Every algebraic extension is then separable in the classical
sense, and the argument of Theorem 5.8(1) applies verbatim with $k$ in place of the prime field.
In detail: consider pairs $(M,\varphi_M)$ with $k\subseteq M\subseteq L$ a subfield and
$\varphi_M:M\to R$ a $k$-algebra homomorphism lifting $\psi|_M$; the pair $(k,\sigma)$ is one, and
unions of chains are again such pairs, so Zorn's lemma provides a maximal $(M,\varphi_M)$. Since
$\psi$ carries nonzero elements to units, so does $\varphi_M$. If $a\in L\setminus M$ is
transcendental over $M$, choose any $r\in R$ lifting $\psi(a)$; the homomorphism $M[X]\to R$ with
$X\mapsto r$ carries each nonzero polynomial in $a$ to an element that is a unit modulo $I$, hence
to a unit, so it extends to $M(a)$. If $a$ is algebraic over $M$ with minimal polynomial $g$, then
$g'(a)\neq0$, and for any lift $r_0$ of $\psi(a)$ the element
$r=r_0-\varphi_M(g)(r_0)/\varphi_M(g')(r_0)$ satisfies $\varphi_M(g)(r)=0$ because $I^2=0$; so
$\varphi_M$ extends to $M(a)=M[X]/(g)$. Either way maximality is contradicted, so $M=L$.
$\square$

Two consequences are recorded for use in Chapter 6. The first packages the theorem with the
permanence of Section 5.1; the second is the form in which a complete local ring over a field is
recognized as formally smooth.

**Corollary 5.17.** Let $K$ be a field.

1. If $\kappa/K$ is a separable field extension, then $\kappa[[z_1,\ldots,z_N]]$ is formally
   smooth over $(K,0)$ for its maximal-adic topology.
2. Let $(C,\mathfrak n,\ell)$ be a noetherian local $K$-algebra such that $\widehat C$ is a
   _regular_ local ring and the residue field extension $\ell/K$ is separable. Then $C$ is
   formally smooth over $(K,0)$ for the $\mathfrak n$-adic topology, and consequently $C$ is
   geometrically regular over $K$.

**Proof.** (1) Theorem 5.16 makes $\kappa$ formally smooth over $K$ with the discrete topologies,
and $\kappa$ is trivially complete for the zero ideal; Lemma 5.6 adds the power series variables,
and Lemma 5.2 composes.

(2) The ring $\widehat C$ is a complete noetherian local ring containing the field $K$, hence
containing a field, so Book 1, Theorem 13.15, provides a coefficient field, and Book 1,
Corollary 13.32, identifies the complete regular local ring $\widehat C$ with
$\ell[[z_1,\ldots,z_N]]$, $N=\dim\widehat C$. Its residue field is $\ell$, separable over $K$ by
hypothesis, so part (1) makes $\widehat C$ formally smooth over $K$ for its maximal-adic topology.
Lemma 5.15 transfers this to $C$, and Proposition 5.12 converts formal smoothness over a field
into geometric regularity. $\square$

Part (2) is the converse of Section 5.3 in the only case where a converse is available here: a
local algebra over a field whose completion is regular and whose residue field is separable over
the base field is not merely regular but geometrically regular. Note what it does _not_ assume —
no finiteness of the extension $\ell/K$, and no relation between a coefficient field of
$\widehat C$ and $K$.

Corollary 5.14 is the classical interface with the next chapter: to prove that a map is regular one
exhibits, at each pair of primes, a solution of the lifting problem. Section 5.1 shows that
solutions propagate along polynomial extensions, localizations and completions from the coefficient
rings of Cohen's theorem; Proposition 5.10 shows what has to be checked to move from smoothness
over a coefficient ring to smoothness over an intermediate ring; and the discussion closing
Section 5.2 identifies the one place where that check has content — the pairs of primes at which
the modules involved are not adically torsion. Chapter 6 attacks exactly that point, and does so by
a direct computation with Cohen coordinates rather than through the lifting problem; the reader who
wants the shortest path to the main theorems may read Chapter 6 immediately after Chapter 4.

## 6. Complete local rings and their finite-type algebras

A complete local ring is its own completion, so the formal fiber at its maximal ideal is a point
and carries no information. The formal fibers at the _other_ primes are a different matter: the
localization $A_{\mathfrak p}$ of a complete local ring is not complete, and its completion is a
genuinely new ring. That these formal fibers are geometrically regular is the first substantial
theorem about $G$-rings, and it is the base case on which all later permanence rests.

The proof in Section 6.1 uses no formal smoothness at all; it is a dimension induction on Cohen
coordinates, resting on four facts already available. First, the generic-fiber criterion
(Lemma 4.11) reduces every formal fiber to a _generic_ formal fiber of a local domain. Second,
Book 1, Theorem 13.34, presents a complete local domain as a finite extension of a complete
_regular_ local ring, and Proposition 4.12 transports formal-fiber regularity across such a finite
extension. Third, the generic formal fiber of a regular local ring is automatically regular,
because it is a localization of the completion, which is regular. Fourth, geometric regularity
adds nothing in characteristic zero, and in characteristic $p$ it is obtained by enlarging the
test field: a finite purely inseparable extension of $\operatorname{Frac}k[[x_1,\ldots,x_n]]$ is
contained in $\operatorname{Frac}k^{1/p^e}[[x_1^{1/p^e},\ldots,x_n^{1/p^e}]]$, which is again the
fraction field of a complete regular local ring, and regularity descends along field extensions by
Lemma 3.8.

The last step requires the enlarged power series ring to be _finite_ over the original one, which
holds exactly when $[k:k^p]<\infty$. We therefore prove Section 6.1 under that hypothesis on the
residue field, and we state it explicitly in every theorem rather than hiding it in a convention.
It is satisfied by every perfect field, by every field finitely generated over a perfect field —
in particular by every residue field occurring on a scheme of finite type over $\mathbf Z$ or over
a field finitely generated over its prime field — and it is vacuous in characteristic zero and in
mixed characteristic, where the fraction fields concerned have characteristic zero. Section 10.4
records precisely what is left open without it.

### 6.1 Complete local rings are G-rings

We begin with three lemmas, each a short consequence of earlier chapters.

**Lemma 6.1 (finite transfer).** Let $(A,\mathfrak m)$ be a noetherian local ring such that
$A\to\widehat A$ is a regular homomorphism, and let $B$ be a finite $A$-algebra. Then for every
maximal ideal $\mathfrak Q$ of $B$ the map $B_{\mathfrak Q}\to\widehat{B_{\mathfrak Q}}$ is
regular.

**Proof.** This is the body of the proof of Proposition 4.12, which used about $A$ only that
$A\to\widehat A$ is regular: the $\mathfrak m$-adic completion of $B$ is $B\otimes_A\widehat A$, a
complete semilocal finite $\widehat A$-algebra, hence the product of the
$\widehat{B_{\mathfrak Q_i}}$; the map $B\to B\otimes_A\widehat A$ is regular by Proposition 4.7;
projection to a factor is a localization, hence regular, so $B\to\widehat{B_{\mathfrak Q}}$ is
regular by Proposition 4.6; and the fibers of $B_{\mathfrak Q}\to\widehat{B_{\mathfrak Q}}$ are
among those of $B\to\widehat{B_{\mathfrak Q}}$. $\square$

**Lemma 6.2 (generic formal fibers of regular local rings).** Let $R$ be a regular local ring, or
more generally a noetherian local ring which is a localization of a regular ring. Then
$\widehat R$ is regular, and every localization of $\widehat R$ is regular. In particular, if $R$
is a domain with fraction field $F$, the generic formal fiber $\widehat R\otimes_RF$ is a regular
ring.

**Proof.** $R\to\widehat R$ is flat and local with closed fiber the residue field, so
Proposition 2.15 makes $\widehat R$ regular, and Corollary 2.10 makes all its localizations
regular. The ring $\widehat R\otimes_RF$ is the localization of $\widehat R$ at the image of
$R\setminus\{0\}$. $\square$

**Lemma 6.3 (purely inseparable ring extensions).** Let $T\subseteq T'$ be an extension of rings
such that every element of $T'$ has a $p^e$-th power in $T$ for a fixed $e$. Then
$\operatorname{Spec}T'\to\operatorname{Spec}T$ is injective. In particular, if $T$ is local and
$T'$ is finite over $T$, then $T'$ is local.

**Proof.** If $\mathfrak P_1,\mathfrak P_2$ are primes of $T'$ contracting to the same prime
$\mathfrak p$ and $z\in\mathfrak P_1$, then $z^{p^e}\in\mathfrak p\subseteq\mathfrak P_2$, so
$z\in\mathfrak P_2$; by symmetry $\mathfrak P_1=\mathfrak P_2$. A finite extension of a local ring
is semilocal with maximal ideals lying over the maximal ideal, and injectivity leaves only one.
$\square$

The next proposition is the heart of the chapter. It says that the two power series rings supplied
by Cohen's theorem have geometrically regular formal fibers, and it is here that the $p$-degree
hypothesis is used.

**Proposition 6.4 (Cohen coordinate rings).** Let $T$ be either $k[[x_1,\ldots,x_n]]$ with $k$ a
field satisfying $[k:k^p]<\infty$ when $\operatorname{char}k=p>0$, or $C_0[[x_1,\ldots,x_n]]$ with
$C_0$ a Cohen ring. Let $F=\operatorname{Frac}T$ and let $\mathfrak p$ be a prime of $T$. Then the
generic formal fiber

$$
\widehat{T_{\mathfrak p}}\otimes_{T_{\mathfrak p}}F
$$

is geometrically regular over $F$.

**Proof.** The ring $T$ is a complete regular local domain by Book 1, Lemma 13.29, so
$T_{\mathfrak p}$ is regular by Corollary 2.10 and the displayed ring is regular by Lemma 6.2;
write $G$ for it.

If $\operatorname{char}F=0$ — which is the case for $T=C_0[[x]]$, since a Cohen ring is a domain of
characteristic zero, and for $T=k[[x]]$ with $\operatorname{char}k=0$ — then regularity is
geometric regularity by Theorem 3.7, and we are done.

So let $T=k[[x_1,\ldots,x_n]]$ with $\operatorname{char}k=p$ and $[k:k^p]=p^s$. By Theorem 3.7 it
suffices to prove that $G\otimes_FL$ is regular for every finite purely inseparable extension
$L/F$. Fix such an $L$ and choose $e$ with $L\subseteq F^{1/p^e}$, the field of $p^e$-th roots of
$F$ inside an algebraic closure. Set

$$
T_e=k^{1/p^e}\big[[\,x_1^{1/p^e},\ldots,x_n^{1/p^e}\,]\big] .
$$

Raising to the $p^e$-th power carries a power series $\sum b_\beta u^\beta$ over $k^{1/p^e}$ in the
variables $u_i=x_i^{1/p^e}$ to $\sum b_\beta^{p^e}u^{p^e\beta}$, and this identifies $T_e$ with the
ring of $p^e$-th roots of elements of $T$; hence $T\subseteq T_e$, every element of $T_e$ has its
$p^e$-th power in $T$, and $\operatorname{Frac}T_e=F^{1/p^e}$. Moreover $T_e$ is a complete regular
local domain by Book 1, Lemma 13.29, and it is _finite_ over $T$: the extension
$k^{1/p^e}/k$ has degree $[k:k^{p^e}]=p^{es}$, which is finite precisely because $[k:k^p]$ is, and
$T_e$ is generated over $k^{1/p^e}[[x_1,\ldots,x_n]]$ by the monomials $u^\beta$ with
$\beta_i<p^e$, so

$$
[\operatorname{Frac}T_e:F]=p^{es}\cdot p^{en}<\infty .
$$

By Lemma 3.8 it is enough to prove that $G\otimes_FF^{1/p^e}$ is regular, since
$F\subseteq L\subseteq F^{1/p^e}$ and both base changes are noetherian, being finite over $G$.

Now compute. Since $F^{1/p^e}=\operatorname{Frac}T_e$,

$$
G\otimes_FF^{1/p^e}
=\widehat{T_{\mathfrak p}}\otimes_T\operatorname{Frac}T_e
=\Big(\widehat{T_{\mathfrak p}}\otimes_TT_e\Big)\otimes_{T_e}\operatorname{Frac}T_e .
$$

The ring $T_e\otimes_TT_{\mathfrak p}$ is a finite $T_{\mathfrak p}$-algebra, and it is local by
Lemma 6.3; call its maximal ideal $\mathfrak p_e$, so that
$T_e\otimes_TT_{\mathfrak p}= (T_e)_{\mathfrak p_e}$. Completion of a finite module over a local
ring is base change to the completion, so

$$
\widehat{T_{\mathfrak p}}\otimes_TT_e=\widehat{(T_e)_{\mathfrak p_e}} .
$$

Therefore $G\otimes_FF^{1/p^e}$ is the generic formal fiber of the local ring
$(T_e)_{\mathfrak p_e}$, which is a localization of the regular ring $T_e$; Lemma 6.2 makes it
regular. $\square$

**Theorem 6.5 (complete local rings).** Let $A$ be a complete noetherian local ring whose residue
field $k$ satisfies $[k:k^p]<\infty$ when $\operatorname{char}k=p>0$. Then $A$ is a $G$-ring:
for every prime $\mathfrak p$ the map $A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ is regular. In
particular every field, every complete discrete valuation ring with residue field of finite
$p$-degree, and every quotient of a power series ring over such a ring, is a $G$-ring.

**Proof.** By Lemma 4.11 it suffices to prove the following statement for all $d\geq0$, by
induction on $d$:

> $(\ast_d)$ for every complete noetherian local _domain_ $R$ of dimension at most $d$ whose
> residue field satisfies the stated $p$-degree hypothesis, and every prime
> $\mathfrak p\subseteq R$, the map $R_{\mathfrak p}\to\widehat{R_{\mathfrak p}}$ is regular.

Indeed, granting $(\ast_d)$ for all $d$: for a pair $\mathfrak q\subseteq\mathfrak p$ in $A$, the
ring $A/\mathfrak q$ is a complete noetherian local domain with the same residue field, by Book 1,
Lemma 13.2, and the formal fiber of $A$ at $\mathfrak p$ over $\mathfrak q$ is the generic formal
fiber of $(A/\mathfrak q)_{\mathfrak p/\mathfrak q}$ by Lemma 4.11.

For $d=0$ the ring $R$ is a field and there is nothing to prove. Let $d\geq1$ and assume
$(\ast_{d-1})$. Let $R$ be a complete local domain of dimension $d$ and $\mathfrak p$ a prime.
By Book 1, Theorem 13.34 — using Book 1, Theorem 13.15 for a coefficient field in equal
characteristic and Book 1, Theorems 13.21 and 13.25 for a Cohen ring in mixed characteristic, and
Book 1, Lemma 13.29 for the dimension count that makes the map injective — there is a finite
injection

$$
T\hookrightarrow R,\qquad T=k[[x_1,\ldots,x_d]]\ \text{or}\ T=C_0[[x_1,\ldots,x_{d-1}]],
$$

with $T$ a complete regular local domain of dimension $d$ and residue field $k$. Put
$\mathfrak p_0=\mathfrak p\cap T$. Then $R\otimes_TT_{\mathfrak p_0}$ is a finite
$T_{\mathfrak p_0}$-algebra whose maximal ideals are the primes of $R$ over $\mathfrak p_0$, and
$R_{\mathfrak p}$ is its localization at the maximal ideal $\mathfrak p$. By Lemma 6.1 it
therefore suffices to prove that $T_{\mathfrak p_0}\to\widehat{T_{\mathfrak p_0}}$ is regular.

Let $\mathfrak q_0\subseteq\mathfrak p_0$ be a prime of $T$. By the computation of Lemma 4.11, the
fiber of $T_{\mathfrak p_0}\to\widehat{T_{\mathfrak p_0}}$ over $\mathfrak q_0$ is the generic
formal fiber of $(T/\mathfrak q_0)_{\mathfrak p_0/\mathfrak q_0}$. If $\mathfrak q_0=0$ this is
geometrically regular by Proposition 6.4. If $\mathfrak q_0\neq0$ then $T/\mathfrak q_0$ is a
complete noetherian local domain of dimension at most $d-1$, with residue field $k$, so the
induction hypothesis $(\ast_{d-1})$ applies and gives geometric regularity. Hence all fibers of
$T_{\mathfrak p_0}\to\widehat{T_{\mathfrak p_0}}$ are geometrically regular, and the map is flat,
so it is regular. This proves $(\ast_d)$ and the theorem. $\square$

**Corollary 6.6.** Under the hypothesis of Theorem 6.5, every localization of $A$, every quotient
of $A$, and every finite $A$-algebra is a $G$-ring; and for every prime $\mathfrak p$ of such a
ring, completion at $\mathfrak p$ preserves and reflects regularity, reducedness and normality.

**Proof.** Lemma 4.10 for quotients and localizations, Proposition 4.12 for finite algebras, and
Theorem 4.13 for the transfer statements. $\square$

### 6.2 Algebras essentially of finite type over a field

The proof of Theorem 6.5 used completeness in exactly two places: to obtain a finite injection from
a regular ring (Book 1, Theorem 13.34) and to know that the regular ring in question is a power
series ring, so that adjoining $p^e$-th roots produces a _finite_ extension which is again
regular. Over a field both inputs are supplied by classical commutative algebra: Noether
normalization plays the role of Theorem 13.34, and $k^{1/p^e}[t_1^{1/p^e},\ldots,t_r^{1/p^e}]$
plays the role of $T_e$. The same induction therefore runs verbatim.

**Theorem 6.7 (algebras essentially of finite type over a field).** Let $k$ be a field such that
$[k:k^p]<\infty$ when $\operatorname{char}k=p>0$. Then every algebra essentially of finite type
over $k$ is a $G$-ring.

**Proof.** By Lemma 4.10 the $G$-property passes to localizations, so it suffices to treat
finite-type $k$-algebras; and by the same lemma it suffices, thanks to Lemma 4.11, to prove the
following statement for every $d\geq0$, by induction on $d$:

> $(\ast_d)$ for every finite-type $k$-algebra domain $C$ with $\dim C\leq d$ and every prime
> $\mathfrak q$ of $C$, the map $C_{\mathfrak q}\to\widehat{C_{\mathfrak q}}$ is regular.

Indeed, given $(\ast_d)$ for all $d$: a finite-type $k$-algebra $A$ has, for each pair
$\mathfrak q\subseteq\mathfrak p$, the formal fiber of $A$ at $\mathfrak p$ over $\mathfrak q$
equal to the generic formal fiber of $(A/\mathfrak q)_{\mathfrak p/\mathfrak q}$ by Lemma 4.11, and
$A/\mathfrak q$ is again a finite-type $k$-algebra domain.

For $d=0$ a finite-type $k$-domain of dimension zero is a field and there is nothing to prove.
Let $d\geq1$ and assume $(\ast_{d-1})$. Let $C$ be a finite-type $k$-domain of dimension
$r\leq d$ and $\mathfrak q$ a prime of $C$. Noether normalization provides algebraically
independent $t_1,\ldots,t_r\in C$ with $C$ finite over the polynomial ring
$Q=k[t_1,\ldots,t_r]$. Put $\mathfrak n=\mathfrak q\cap Q$. Then $C\otimes_QQ_{\mathfrak n}$ is a
finite $Q_{\mathfrak n}$-algebra whose maximal ideals are the primes of $C$ lying over
$\mathfrak n$, and $C_{\mathfrak q}$ is its localization at the maximal ideal $\mathfrak q$; so by
Lemma 6.1 it suffices to prove that $Q_{\mathfrak n}\to\widehat{Q_{\mathfrak n}}$ is regular.

By the computation in Lemma 4.11, the fiber of $Q_{\mathfrak n}\to\widehat{Q_{\mathfrak n}}$ over a
prime $\mathfrak q_0\subseteq\mathfrak n$ is the generic formal fiber of
$(Q/\mathfrak q_0)_{\mathfrak n/\mathfrak q_0}$. If $\mathfrak q_0\neq0$ then $Q/\mathfrak q_0$ is
a finite-type $k$-domain of dimension at most $r-1\leq d-1$ and $(\ast_{d-1})$ applies. There
remains the case $\mathfrak q_0=0$, that is, the generic formal fiber
$G=\widehat{Q_{\mathfrak n}}\otimes_QF$ of the regular local ring $Q_{\mathfrak n}$, where
$F=k(t_1,\ldots,t_r)$.

The ring $G$ is regular by Lemma 6.2. If $\operatorname{char}k=0$, Theorem 3.7 upgrades this to
geometric regularity. Suppose $\operatorname{char}k=p$ and $[k:k^p]=p^s$, and let $L/F$ be a finite
purely inseparable extension, say $L\subseteq F^{1/p^e}$. Set

$$
Q_e=k^{1/p^e}\big[t_1^{1/p^e},\ldots,t_r^{1/p^e}\big],
$$

a polynomial ring in $r$ variables over the field $k^{1/p^e}$, hence a regular ring. Every
element of $Q$ has its $p^e$-th root in $Q_e$ and conversely, so
$\operatorname{Frac}Q_e=F^{1/p^e}$, and $Q_e$ is finite over $Q$ of degree
$[k:k^{p^e}]\cdot p^{er}=p^{es}p^{er}<\infty$, the finiteness of $[k:k^{p^e}]=p^{es}$ being
exactly the hypothesis $[k:k^p]<\infty$. By Lemma 3.8 it suffices to prove that
$G\otimes_FF^{1/p^e}$ is regular. Since $Q\subseteq Q_e$ is purely inseparable, Lemma 6.3 makes
$Q_e\otimes_QQ_{\mathfrak n}$ local, say with maximal ideal $\mathfrak n_e$, and completion of a
finite module gives $\widehat{Q_{\mathfrak n}}\otimes_QQ_e= \widehat{(Q_e)_{\mathfrak n_e}}$.
Hence

$$
G\otimes_FF^{1/p^e}
=\widehat{(Q_e)_{\mathfrak n_e}}\otimes_{Q_e}\operatorname{Frac}Q_e,
$$

the generic formal fiber of the regular local ring $(Q_e)_{\mathfrak n_e}$, which is regular by
Lemma 6.2. This proves $(\ast_d)$ and the theorem. $\square$

**Corollary 6.8.** Let $k$ be as in Theorem 6.7. Then every finite-type $k$-algebra $A$, every
localization of one, and every finite algebra over one is a $G$-ring; and for every prime
$\mathfrak p$ of such a ring, completion at $\mathfrak p$ preserves and reflects regularity,
reducedness and normality. In particular this holds for every perfect field, hence for every
finite field, every algebraically closed field, and every field of characteristic zero.

**Proof.** Theorem 6.7 with Lemma 4.10, Proposition 4.12 and Theorem 4.13; a perfect field has
$[k:k^p]=1$. $\square$

The same enlargement argument applies to the Cohen coordinate rings with polynomial variables
adjoined, which is the case of a _regular_ ring essentially of finite type over a complete local
ring.

**Proposition 6.9 (regular algebras over Cohen coordinate rings).** Let $T$ be as in
Proposition 6.4 and put $P=T[y_1,\ldots,y_m]$. Then $P$ is a regular ring, and for every prime
$\mathfrak q$ of $P$ the generic formal fiber of $P_{\mathfrak q}$ is geometrically regular over
$\operatorname{Frac}P$.

**Proof.** $P$ is regular by Corollary 2.16, so $P_{\mathfrak q}$ is regular by Corollary 2.10 and
its generic formal fiber $G$ is regular by Lemma 6.2. If $\operatorname{Frac}P$ has
characteristic zero we are done by Theorem 3.7; this covers the mixed characteristic case
$T=C_0[[x]]$. Otherwise $T=k[[x_1,\ldots,x_n]]$ with $\operatorname{char}k=p$ and
$[k:k^p]=p^s<\infty$. Let $L\subseteq(\operatorname{Frac}P)^{1/p^e}$ be a finite purely
inseparable extension and put

$$
P_e=T_e\big[y_1^{1/p^e},\ldots,y_m^{1/p^e}\big],\qquad
T_e=k^{1/p^e}\big[[\,x_1^{1/p^e},\ldots,x_n^{1/p^e}\,]\big],
$$

as in the proof of Proposition 6.4. Then $P_e$ consists exactly of the $p^e$-th roots of elements
of $P$, so $\operatorname{Frac}P_e=(\operatorname{Frac}P)^{1/p^e}$; it is finite over $P$, being
finite over $T_e[y_1,\ldots,y_m]$ which is finite over $P$; and it is regular, being a polynomial
ring over the complete regular local ring $T_e$. Exactly as before, Lemma 6.3 and completion of a
finite module identify $G\otimes_{\operatorname{Frac}P}\operatorname{Frac}P_e$ with the generic
formal fiber of $(P_e)_{\mathfrak q_e}$, which is regular by Lemma 6.2, and Lemma 3.8 descends
regularity to $G\otimes L$. $\square$

### 6.3 Base change to the completion, and what remains

The engine of all further permanence is the following elementary lemma, which trades a base $R$
for its completion at the cost of one application of the $G$-property. It is stated here because
Section 6.4 already needs it; Chapter 7 uses it again.

**Lemma 6.10 (base change to the completion).** Let $(R,\mathfrak m_R)$ be a noetherian local ring
with $R\to\widehat R$ regular, and let $(B,\mathfrak m_B)$ be a local ring essentially of finite
type over $R$ with $\mathfrak m_R\subseteq\mathfrak m_B$. Put $C=B\otimes_R\widehat R$ and
$\mathfrak n'=\mathfrak m_BC$. Then:

1. $C$ is noetherian and essentially of finite type over $\widehat R$, and $\mathfrak n'$ is a
   maximal ideal of $C$ with residue field $B/\mathfrak m_B$;
2. $B\to C$ is regular;
3. $C/\mathfrak n'^n=B/\mathfrak m_B^n$ for all $n$, hence
   $\widehat{C_{\mathfrak n'}}=\widehat B$;
4. if $C_{\mathfrak n'}\to\widehat{C_{\mathfrak n'}}$ is regular, then $B\to\widehat B$ is regular.

**Proof.** (1) $B$ is a localization of a finite-type $R$-algebra, so $C$ is a localization of a
finite-type $\widehat R$-algebra and is noetherian. Moreover
$C/\mathfrak m_BC=(B/\mathfrak m_B)\otimes_R\widehat R=(B/\mathfrak m_B)\otimes_{R/\mathfrak m_R} \widehat R/\mathfrak m_R\widehat R=B/\mathfrak m_B$
, a field.

(2) Proposition 4.7, the base change of the regular map $R\to\widehat R$ along $R\to B$; the
tensor product is noetherian by (1).

(3) The ring $B/\mathfrak m_B^n$ is annihilated by $\mathfrak m_R^n$, so
$(B/\mathfrak m_B^n)\otimes_R\widehat R=(B/\mathfrak m_B^n)\otimes_{R/\mathfrak m_R^n} \widehat R/\mathfrak m_R^n\widehat R=B/\mathfrak m_B^n$
. As these rings are local, localizing at $\mathfrak n'$ changes nothing, and passing to the limit
gives $\widehat{C_{\mathfrak n'}}=\widehat B$.

(4) The composite $B\to C\to C_{\mathfrak n'}\to\widehat{C_{\mathfrak n'}}=\widehat B$ is the
completion map. Its first two stages are regular by (2) and because a localization is regular, and
the third is regular by hypothesis; Proposition 4.6 composes them. $\square$

**Corollary 6.11 (dimension reduction over a complete base).** Let $T$ be a Cohen coordinate ring
as in Proposition 6.4 and let $B$ be a local ring essentially of finite type over $T$ with
$\mathfrak p_0=\mathfrak m_B\cap T\neq\mathfrak m_T$. If every local ring essentially of finite
type over the complete local ring $\widehat{T_{\mathfrak p_0}}$ is a $G$-ring, then
$B\to\widehat B$ is regular.

**Proof.** $B$ is essentially of finite type over $R=T_{\mathfrak p_0}$, which is a $G$-ring by
Theorem 6.5 and Lemma 4.10, and $\mathfrak m_R\subseteq\mathfrak m_B$. Lemma 6.10 replaces $B$ by
$C_{\mathfrak n'}$, a local ring essentially of finite type over the complete local ring
$\widehat R=\widehat{T_{\mathfrak p_0}}$, whose dimension is
$\operatorname{ht}\mathfrak p_0<\dim T$. $\square$

### 6.4 Reduction to the closed-point case

Combining Lemma 4.11 with Corollary 6.11, the assertion

> $(\mathrm{EFT})$ every local ring essentially of finite type over a complete noetherian local
> ring with residue field of finite $p$-degree is a $G$-ring

reduces by induction on the dimension of the base to the following single case, which we call the
**closed-point case**: $T$ a Cohen coordinate ring, $C$ a finite-type $T$-algebra domain, and
$\mathfrak q$ a prime of $C$ with $\mathfrak q\cap T=\mathfrak m_T$; one must show that the generic
formal fiber of $C_{\mathfrak q}$ is geometrically regular. Indeed, the base of that induction is
$\dim T=0$, where $T$ is a field and Theorem 6.7 applies; for $\dim T>0$ the primes
$\mathfrak q$ with $\mathfrak q\cap T\neq\mathfrak m_T$ are handled by Corollary 6.11 and the
inductive hypothesis; and quotients are handled by Lemma 4.11 together with the reduction of a
complete local ring to a Cohen coordinate ring.

The closed-point case is settled in the two sections that follow — Section 6.5 in equal
characteristic $p$, which is where the difficulty lies, and Section 6.6 in the remaining cases —
so that the reduction just described is a roadmap rather than a gap. Two observations drive the argument, and both are consequences of the hypothesis
$[k:k^p]<\infty$: the ring $P=T[y_1,\ldots,y_m]$ has a _finite_ $p$-basis, so that it carries a
finite supply of partial derivatives which detect regularity through a Jacobian criterion; and $P$
is _$F$-finite_, so that a purely inseparable base extension of a formal fiber is again a formal
fiber of the same kind and geometric regularity is free once regularity is known. Section 6.6
completes the argument in the remaining cases, in which the fields involved have characteristic
zero and a different, easier count of differentials is available.

### 6.5 The closed-point case in equal characteristic p

Throughout this section $k$ is a field of characteristic $p$ with $[k:k^p]=p^s<\infty$, and
$\Gamma=\{\gamma_1,\ldots,\gamma_s\}$ is a $p$-basis of $k$ (Book 1, Lemma 13.10). We write

$$
T=k[[x_1,\ldots,x_n]],\qquad P=T[y_1,\ldots,y_m],\qquad
t=(\gamma_1,\ldots,\gamma_s,x_1,\ldots,x_n,y_1,\ldots,y_m),\qquad N=s+n+m.
$$

A ring $R$ of characteristic $p$ is **$F$-finite** if $R$ is a finite module over its subring
$R^p$ of $p$-th powers; equivalently, if the ring $R^{1/p}$ of $p$-th roots of elements of $R$,
formed inside a fixed algebraic closure of $\operatorname{Frac}R$ when $R$ is a domain, is a
finite $R$-module.

**Lemma 6.12 (a finite $p$-basis).** The ring $P$ is free over $P^p$ with basis the $p$-monomials
$t^\alpha=\prod_it_i^{\alpha_i}$, $0\leq\alpha_i<p$; in particular $P=P^p[t_1,\ldots,t_N]$ and $P$
is $F$-finite, and $P^{1/p}$ is a free $P$-module of rank $p^N$. Moreover every ring essentially of
finite type over $P$ is $F$-finite, and for every prime $\mathfrak q$ of such a ring the residue
field is $F$-finite.

**Proof.** Since $\Gamma$ is a $p$-basis, $k=\bigoplus_{\varepsilon<p}k^p\gamma^\varepsilon$ as a
$k^p$-module (Book 1, Lemma 13.11), and applying this coefficientwise to power series in the $x^p$
gives $k[[x^p]]=\bigoplus_\varepsilon k^p[[x^p]]\gamma^\varepsilon$. Splitting a power series
according to the residues modulo $p$ of its exponents gives
$k[[x]]=\bigoplus_{\alpha<p}k[[x^p]]x^\alpha$, and finally
$P=\bigoplus_{\beta<p}T[y^p]y^\beta$. Composing the three decompositions and using
$P^p=k^p[[x^p]][y^p]$ yields the asserted basis. Applying the same statement to the ring
$P^{1/p}=k^{1/p}[[x_1^{1/p},\ldots]][y_1^{1/p},\ldots]$ — which is of the same shape, over the
field $k^{1/p}$ with $[k^{1/p}:k^{1/p\cdot p}]=[k:k^p]=p^s$ — shows that $P^{1/p}$ is free over
$(P^{1/p})^p=P$ of rank $p^N$.

$F$-finiteness passes to quotients, because $(R/I)^p$ is the image of $R^p$ and the images of
module generators generate; and to localizations, because $S^{-1}R$ is generated over
$(S^{-1}R)^p\supseteq S^{-p}R^p$ by the same generators. A residue field
$\kappa(\mathfrak q)$ is a localization of a quotient. $\square$

The next lemma is Cartier's equality: for a ring with a finite $p$-basis, the $p$-degree of a
residue field drops by exactly the height of the prime. It is what converts a count of
differentials into the Jacobian criterion.

**Lemma 6.13 (Cartier's equality).** Let $\mathfrak q$ be a prime of $P$ of height $c$ and
$\kappa=\kappa(\mathfrak q)$. Then $[\kappa:\kappa^p]=p^{N-c}$, and
$\dim_\kappa\Omega_{\kappa/\mathbf F_p}=N-c$.

**Proof.** Put $R=P_{\mathfrak q}$, a regular local ring of dimension $c$ by Corollary 2.10, and
let $f_1,\ldots,f_c$ be a regular system of parameters of $R$. Localizing the free module of
Lemma 6.12 gives that $R^{1/p}=(P^{1/p})_{\mathfrak q}$ — the two localizations agree, because a
unit and its $p$-th root are invertible together — is a free $R$-module of rank $p^N$. Hence

$$
\dim_\kappa\big(R^{1/p}/\mathfrak qR^{1/p}\big)=p^N .
$$

On the other hand the $p$-th power map is a ring isomorphism $R^{1/p}\to R$, so $R^{1/p}$ is a
regular local ring of dimension $c$ whose maximal ideal is generated by the regular system of
parameters $g_j=f_j^{1/p}$, and whose residue field is $\kappa^{1/p}$. Since
$\mathfrak qR^{1/p}=(g_1^p,\ldots,g_c^p)$ and $g_1^p,\ldots,g_c^p$ is a regular sequence in
$R^{1/p}$, the quotient $R^{1/p}/\mathfrak qR^{1/p}$ has length $p^c$ over $R^{1/p}$, all of whose
composition factors are $\kappa^{1/p}$. Therefore

$$
p^N=\dim_\kappa\big(R^{1/p}/\mathfrak qR^{1/p}\big)=p^c\cdot[\kappa^{1/p}:\kappa]
=p^c\cdot[\kappa:\kappa^p],
$$

which is the first assertion. For the second, Book 1, Theorem 13.12, identifies derivations of
$\kappa$ with arbitrary functions on a $p$-basis, so $\Omega_{\kappa/\mathbf F_p}$ is a
$\kappa$-vector space of dimension equal to the cardinality of a $p$-basis of $\kappa$, that is,
$\log_p[\kappa:\kappa^p]=N-c$. $\square$

**Lemma 6.14 (coordinate derivations).** For each $i\leq N$ there is a unique $P^p$-derivation
$D_i:P\to P$ with $D_i(t_j)=\delta_{ij}$. Each $D_i$ extends uniquely to every localization of
$P$, continuously to the completion $\widehat{P_{\mathfrak q}}$ at any prime, and further to every
localization of that completion.

**Proof.** By Lemma 6.12 the surjection $P^p[Z_1,\ldots,Z_N]\to P$, $Z_i\mapsto t_i$, has kernel
$(Z_1^p-t_1^p,\ldots,Z_N^p-t_N^p)$: both sides are free $P^p$-modules with the monomial bases
matching. The partial derivative $\partial/\partial Z_i$ is a $P^p$-derivation of $P^p[Z]$ which
kills each generator $Z_j^p-t_j^p$, since $\partial(Z_j^p)/\partial Z_i=pZ_j^{p-1}\delta_{ij}=0$
in characteristic $p$; hence it descends to $P$, giving $D_i$, and uniqueness holds because
$P=P^p[t_1,\ldots,t_N]$. A derivation extends uniquely to a localization by the quotient rule, and
$D_i(\mathfrak q^r)\subseteq\mathfrak q^{r-1}$ makes $D_i$ continuous for the
$\mathfrak q$-adic topology, hence extendable to the completion. $\square$

**Lemma 6.15 (Jacobian criterion).** Let $(A,\mathfrak m,\kappa_A)$ be a regular local ring, let
$D_1,\ldots,D_N$ be derivations of $A$, and let $f_1,\ldots,f_c\in\mathfrak m$ be such that some
$c\times c$ minor of the matrix $(D_i(f_j))$ is a unit of $A$. Then $f_1,\ldots,f_c$ is part of a
regular system of parameters of $A$, and $A/(f_1,\ldots,f_c)$ is regular.

**Proof.** The assignment $g\mapsto(D_i(g)\bmod\mathfrak m)_i$ carries $\mathfrak m$ to
$\kappa_A^N$, kills $\mathfrak m^2$ by the Leibniz rule, and is $\kappa_A$-linear modulo
$\mathfrak m$, since $D_i(ag)=aD_i(g)+gD_i(a)\equiv aD_i(g)$ for $g\in\mathfrak m$. It therefore
induces a $\kappa_A$-linear map $\mathfrak m/\mathfrak m^2\to\kappa_A^N$ under which the images of
$f_1,\ldots,f_c$ have a matrix of rank $c$; hence those images are linearly independent in
$\mathfrak m/\mathfrak m^2$ and extend to a basis, that is, $f_1,\ldots,f_c$ is part of a regular
system of parameters. Killing part of a regular system of parameters of a regular local ring
leaves a ring whose maximal ideal is generated by the remaining $\dim A-c$ parameters and whose
dimension is at least $\dim A-c$, hence a regular local ring. $\square$

**Proposition 6.16 (the formal fibers of $P$ are regular).** For every prime $\mathfrak q$ of $P$,
every prime $q\subseteq\mathfrak q$ and every prime $\mathfrak Q$ of $A=\widehat{P_{\mathfrak q}}$
lying over $q$, the local ring $A_{\mathfrak Q}/qA_{\mathfrak Q}$ is regular. Equivalently, all
fibers of $P_{\mathfrak q}\to\widehat{P_{\mathfrak q}}$ are regular rings.

**Proof.** The ring $P$ is regular by Corollary 2.16, so $P_{\mathfrak q}$ is regular and
$A=\widehat{P_{\mathfrak q}}$ is a complete regular local ring by Proposition 2.15; hence
$A_{\mathfrak Q}$ is regular by Corollary 2.10. Write $c=\operatorname{ht}q$ and choose
$f_1,\ldots,f_c\in q$ forming a regular system of parameters of the regular local ring $P_q$.
Since $\mathfrak Q\cap P=q$, every element of $P\setminus q$ is invertible in $A_{\mathfrak Q}$,
so from $qP_q=(f_1,\ldots,f_c)P_q$ we get

$$
qA_{\mathfrak Q}=(f_1,\ldots,f_c)A_{\mathfrak Q}.
$$

By Lemmas 6.14 and 6.15 it therefore suffices to produce a $c\times c$ minor of $(D_i(f_j))$
lying outside $\mathfrak Q$; and since $\mathfrak Q\cap P=q$, it suffices to produce one lying
outside $q$. Equivalently, we must show that the matrix $(D_i(f_j))$ has rank $c$ modulo $q$.

Let $\kappa=\kappa(q)$ and consider the two $\kappa$-linear maps

$$
\psi:qP_q/q^2P_q\longrightarrow\kappa^N,\quad g\longmapsto(\overline{D_i(g)})_i,
\qquad
\rho:\kappa^N\longrightarrow\Omega_{\kappa/\mathbf F_p},\quad e_i\longmapsto d\bar t_i .
$$

The map $\psi$ is well defined and $\kappa$-linear by the computation in the proof of Lemma 6.15,
and $\rho$ is surjective because $\kappa=\kappa^p(\bar t_1,\ldots,\bar t_N)$ by Lemma 6.12, so
that the $d\bar t_i$ generate $\Omega_{\kappa/\mathbf F_p}$.

We claim the sequence $\psi,\rho$ is exact at $\kappa^N$. The map
$\tilde d:P\to\widetilde\Omega=\bigoplus_iP\,dt_i$, $g\mapsto\sum_iD_i(g)\,dt_i$, is a derivation,
hence factors through a surjection $\Omega_{P/\mathbf F_p}\twoheadrightarrow\widetilde\Omega$.
Writing $g\in P$ as $\sum_\alpha c_\alpha^pt^\alpha$ and using that derivations kill $p$-th powers
gives, in $\Omega_{\kappa/\mathbf F_p}$,

$$
d\bar g=\sum_\alpha\bar c_\alpha^{\,p}\,d(\bar t^{\,\alpha})
=\sum_i\overline{D_i(g)}\,d\bar t_i ,
$$

so the canonical map $\Omega_{P/\mathbf F_p}\otimes\kappa\to\Omega_{\kappa/\mathbf F_p}$ factors
through $\widetilde\Omega\otimes\kappa=\kappa^N$ as $\rho$. The second fundamental exact sequence
of $\mathbf F_p\to P_q\to\kappa$,

$$
qP_q/q^2P_q\longrightarrow\Omega_{P/\mathbf F_p}\otimes\kappa
\longrightarrow\Omega_{\kappa/\mathbf F_p}\longrightarrow0,
$$

is exact; given $\omega\in\kappa^N$ with $\rho(\omega)=0$, lift it to
$\Omega_{P/\mathbf F_p}\otimes\kappa$ along the surjection, use exactness there, and project back:
$\omega$ lies in the image of $\psi$. This proves the claim.

Now count. By Lemma 6.13, $\dim_\kappa\Omega_{\kappa/\mathbf F_p}=N-c$, so
$\ker\rho$ has dimension $c$, and by exactness the image of $\psi$ is all of $\ker\rho$, of
dimension $c$. The source $qP_q/q^2P_q$ also has dimension $c$, since $P_q$ is regular of
dimension $c$; hence $\psi$ is injective and the images $\psi(f_1),\ldots,\psi(f_c)$, being a basis
of $qP_q/q^2P_q$, are linearly independent. That is exactly the statement that $(D_i(f_j))$ has
rank $c$ modulo $q$. $\square$

Regularity of the formal fibers is now upgraded to geometric regularity by the Frobenius, at no
cost: over an $F$-finite ring a purely inseparable base change of a formal fiber is again a formal
fiber of a ring isomorphic to the original one.

**Proposition 6.17 (Frobenius upgrade).** Let $C$ be an $F$-finite noetherian domain of
characteristic $p$ such that for _every_ prime $\mathfrak q$ the generic formal fiber of
$C_{\mathfrak q}$ is a regular ring. Then each of these generic formal fibers is geometrically
regular over $M=\operatorname{Frac}C$.

**Proof.** Fix $\mathfrak q$, put $B=C_{\mathfrak q}$ and $G=\widehat B\otimes_BM$, and let $L/M$
be a finite purely inseparable extension, say $L\subseteq M^{1/p^e}$. Iterating $F$-finiteness,
$C^{1/p^e}$ is a finite $C$-algebra, a domain with fraction field $M^{1/p^e}$; in particular
$M^{1/p^e}/M$ is finite, so all base changes below are noetherian. By Lemma 3.8 it suffices to
prove that $G\otimes_MM^{1/p^e}$ is regular.

Every element of $C^{1/p^e}$ has its $p^e$-th power in $C$, so $C^{1/p^e}\otimes_CB$ is local by
Lemma 6.3; call it $B'$, a localization of $C^{1/p^e}$ at the unique prime over $\mathfrak q$.
Completion of a finite module over a local ring gives $\widehat B\otimes_BB'=\widehat{B'}$, whence

$$
G\otimes_MM^{1/p^e}=\widehat B\otimes_BM^{1/p^e}
=\widehat{B'}\otimes_{B'}\operatorname{Frac}C^{1/p^e},
$$

the generic formal fiber of $B'$. The $p^e$-th power map is a ring isomorphism $C^{1/p^e}\to C$
carrying the prime of $B'$ to a prime $\mathfrak q''$ of $C$, so $B'\cong C_{\mathfrak q''}$ and
the displayed ring is isomorphic to the generic formal fiber of $C_{\mathfrak q''}$, which is
regular by hypothesis. Regularity is invariant under ring isomorphism, so $G\otimes_MM^{1/p^e}$ is
regular, and Theorem 3.7 concludes. $\square$

**Theorem 6.18 (the closed-point case, equal characteristic $p$).** Let $A$ be a complete
noetherian local ring of equal characteristic $p$ whose residue field $k$ satisfies
$[k:k^p]<\infty$. Then every algebra essentially of finite type over $A$ is a $G$-ring.

**Proof.** By Book 1, Corollary 13.31, $A$ is a quotient of $T=k[[x_1,\ldots,x_n]]$, so every
algebra essentially of finite type over $A$ is a localization of a quotient of
$P=T[y_1,\ldots,y_m]$ for some $m$. By Lemma 4.10 it therefore suffices to prove that $P$ is a
$G$-ring, that is, that $P_{\mathfrak q}\to\widehat{P_{\mathfrak q}}$ is regular for every prime
$\mathfrak q$.

Flatness is automatic. For the fibers, fix $\mathfrak q$ and a prime $q\subseteq\mathfrak q$. By
Lemma 4.11 the fiber over $q$ is the generic formal fiber of $(P/q)_{\mathfrak q/q}$. Put $C=P/q$
, an $F$-finite noetherian domain by Lemma 6.12. For every prime $\mathfrak q'$ of $C$, the
generic formal fiber of $C_{\mathfrak q'}$ is a fiber of
$P_{\mathfrak q''}\to \widehat{P_{\mathfrak q''}}$ over $q$, where $\mathfrak q''$ is the
preimage of $\mathfrak q'$ — again by Lemma 4.11 and Lemma 4.10 — hence regular by Proposition
6.16. Proposition 6.17 now makes all of them geometrically regular, and in particular the fiber we
started with. $\square$

Theorem 6.18 contains the characteristic-$p$ half of Theorem 6.7 as the case $n=0$, and together
with Corollary 6.11 it removes the closed-point obstruction in equal characteristic $p$
altogether.

### 6.6 The remaining cases, and the theorem

What is left is the situation in which the fraction field of the coefficient ring has
characteristic zero: a complete regular local ring $T=k[[x_1,\ldots,x_n]]$ with
$\operatorname{char}k=0$, or $T=C_0[[x_1,\ldots,x_n]]$ with $C_0$ a Cohen ring, so that $T$ has
mixed characteristic and $\operatorname{Frac}T$ has characteristic zero. Call such a $T$ a **Cohen
coordinate ring**, as in Proposition 6.4, and keep the standing hypothesis that its residue field
$k$ satisfies $[k:k^p]<\infty$ when $\operatorname{char}k=p$.

Two features replace the ones exploited in Section 6.5. First, a prime $q$ of $P=T[y_1,\ldots,y_m]$
meeting $T$ nontrivially can be removed by passing to $T/(q\cap T)$, a complete local domain of
_smaller dimension_; this is where the induction lives. Second, a prime $q$ with $q\cap T=0$ makes
$P_q$ a localization of the polynomial ring $F[y_1,\ldots,y_m]$ over the field
$F=\operatorname{Frac}T$, so that the residue field $\kappa(q)$ is a _finitely generated_
extension of $F$; in characteristic zero its module of differentials has dimension equal to the
transcendence degree, and the resulting count gives the Jacobian criterion using only the
derivations $\partial/\partial y_j$. No differentials of $T$ itself are needed, which is exactly
what makes the argument work even though $\Omega_{T/k}$ is unmanageable.

**Theorem 6.19 (polynomial algebras over a Cohen coordinate ring).** Let $T$ be a Cohen coordinate
ring, with residue field of finite $p$-degree in characteristic $p$. Then $P=T[y_1,\ldots,y_m]$ is
a $G$-ring for every $m\geq0$.

**Proof.** If $T$ has equal characteristic $p$ this is Theorem 6.18, so assume that
$F=\operatorname{Frac}T$ has characteristic zero. We argue by induction on $d=\dim T$; the case
$d=0$ has $T=k$ a field of characteristic zero and is Theorem 6.7.

Fix a prime $\mathfrak q$ of $P$; flatness of $P_{\mathfrak q}\to A:=\widehat{P_{\mathfrak q}}$ is
automatic, and we must show that the fiber over each prime $q\subseteq\mathfrak q$ is
geometrically regular over $\kappa(q)$. Note that $P$ is regular by Corollary 2.16, hence
$P_{\mathfrak q}$ is regular by Corollary 2.10 and $A$ is a complete regular local ring by
Proposition 2.15; so $A_{\mathfrak Q}$ is regular for every prime $\mathfrak Q$ of $A$. Put
$\mathfrak p=q\cap T$.

_Case 1: $\mathfrak p\neq0$._ By Lemma 4.11 the fiber of $P_{\mathfrak q}$ over $q$ is the generic
formal fiber of $(P/q)_{\mathfrak q/q}$. Since $\mathfrak pP\subseteq q$, the ring $P/q$ is a
quotient of $(T/\mathfrak p)[y_1,\ldots,y_m]$. Now $T/\mathfrak p$ is a complete noetherian local
domain by Book 1, Lemma 13.2, of dimension $d-\operatorname{ht}\mathfrak p<d$, with the same
residue field $k$; by Book 1, Theorem 13.34 — with Book 1, Theorem 13.15 in equal characteristic
and Book 1, Theorems 13.21 and 13.25 in mixed characteristic — it is a finite extension of a Cohen
coordinate ring $T'$ with $\dim T'=\dim T/\mathfrak p<d$. Hence $(T/\mathfrak p)[y]$ is finite over
$T'[y]$, and $P/q$ is of finite type over $T'$. The induction hypothesis says that
$T'[y'_1,\ldots,y'_{m'}]$ is a $G$-ring for every $m'$, so by Lemma 4.10 every algebra essentially
of finite type over $T'$ is a $G$-ring; in particular $(P/q)_{\mathfrak q/q}$ is a $G$-ring and its
generic formal fiber is geometrically regular.

_Case 2: $\mathfrak p=0$._ Every nonzero element of $T$ is then invertible in $P_q$, so

$$
P_q=\big(F[y_1,\ldots,y_m]\big)_{q'},\qquad q'=qF[y_1,\ldots,y_m],
$$

a localization of a polynomial ring over the field $F$ of characteristic zero. Write
$c=\operatorname{ht}q=\operatorname{ht}q'$ and $\kappa=\kappa(q)$, and choose $f_1,\ldots,f_c\in q$
forming a regular system of parameters of the regular local ring $P_q$.

We claim that the Jacobian matrix $(\partial f_j/\partial y_i)$ has rank $c$ modulo $q$. The
second fundamental exact sequence of $F\to P_q\to\kappa$ reads

$$
qP_q/q^2P_q\longrightarrow\Omega_{P_q/F}\otimes\kappa
\longrightarrow\Omega_{\kappa/F}\longrightarrow0,
$$

and $\Omega_{P_q/F}=\bigoplus_jP_q\,dy_j$ is free of rank $m$, because $P_q$ is a localization of
$F[y_1,\ldots,y_m]$. The residue field of a prime of a polynomial ring over a field satisfies
$\operatorname{trdeg}_F\kappa=m-\operatorname{ht}q'=m-c$, and $\kappa/F$ is finitely generated;
as $\operatorname{char}F=0$ it is separably generated, so
$\dim_\kappa\Omega_{\kappa/F}=\operatorname{trdeg}_F\kappa=m-c$. Exactness therefore makes the
image of $qP_q/q^2P_q$ in $\kappa^m$ of dimension $m-(m-c)=c$; since the source has dimension $c$
as well, the map is injective, and the images of $f_1,\ldots,f_c$ — whose coordinates are the
entries $\overline{\partial f_j/\partial y_i}$ — are linearly independent. This is the claim.

Now let $\mathfrak Q$ be a prime of $A$ lying over $q$, so $\mathfrak Q\cap P=q$. Some $c\times c$
minor of $(\partial f_j/\partial y_i)$ lies outside $q$, hence outside $\mathfrak Q$, hence is a
unit of $A_{\mathfrak Q}$. The derivations $\partial/\partial y_j$ are $T$-derivations of $P$; they
extend to $P_{\mathfrak q}$ by the quotient rule, continuously to $A$ because
$\partial/\partial y_j(\mathfrak q^r)\subseteq\mathfrak q^{r-1}$, and then to $A_{\mathfrak Q}$.
Moreover $qA_{\mathfrak Q}=(f_1,\ldots,f_c)A_{\mathfrak Q}$, since every element of
$P\setminus q$ is invertible in $A_{\mathfrak Q}$ and $qP_q=(f_1,\ldots,f_c)P_q$. Lemma 6.15 now
makes $A_{\mathfrak Q}/qA_{\mathfrak Q}$ regular. As this holds for every $\mathfrak Q$ over $q$,
the fiber ring $A\otimes_{P_{\mathfrak q}}\kappa(q)$ is regular; and $\kappa(q)$ contains $F$,
hence has characteristic zero, so Theorem 3.7 upgrades regularity to geometric regularity.

In both cases the fiber over $q$ is geometrically regular, so $P_{\mathfrak q}\to A$ is regular for
every $\mathfrak q$, that is, $P$ is a $G$-ring. $\square$

**Theorem 6.20 (algebras essentially of finite type over a complete local ring).** Let $A$ be a
complete noetherian local ring whose residue field $k$ satisfies $[k:k^p]<\infty$ when
$\operatorname{char}k=p>0$. Then every algebra essentially of finite type over $A$ is a $G$-ring.
In particular $A$ itself, every finite-type $A$-algebra, every localization of one, every quotient
of one and every finite algebra over one is a $G$-ring, and for each of their primes completion
preserves and reflects regularity, reducedness and normality.

**Proof.** By Book 1, Corollary 13.31, $A$ is a quotient of a Cohen coordinate ring $T$, namely
$k[[X_1,\ldots,X_N]]$ if $A$ contains a field and $C_0[[X_1,\ldots,X_N]]$ otherwise. An algebra
essentially of finite type over $A$ is a localization of a quotient of $A[y_1,\ldots,y_m]$ for some
$m$, hence a localization of a quotient of $T[y_1,\ldots,y_m]$. Theorem 6.19 makes the latter a
$G$-ring, and Lemma 4.10 transports the property to quotients and localizations. The final
assertions add Proposition 4.12 and Theorem 4.13. $\square$

Theorem 6.20 supersedes Theorem 6.5, which is the case $m=0$ together with Lemma 4.10, and
Theorem 6.7, which is the case of a field; both were used as ingredients and both retain their
independent, shorter proofs. It also removes the hypothesis under which Corollary 6.11 was stated:
the dimension reduction recorded there is now unconditional, and Section 6.4 is a description of
the strategy rather than a statement of a gap. The one hypothesis that does persist is
$[k:k^p]<\infty$, which entered in Proposition 6.4 and again through Lemma 6.12, and which is
carried explicitly in every statement from here to the end of the book.

## 7. The permanence theorems

Chapter 6 settled the base case: over a complete local ring, everything essentially of finite type
is a $G$-ring. The present chapter converts that into the two permanence statements which make the
notion usable. The first says that the $G$-property, although defined by a condition at every
prime, need only be checked at the maximal ideals; the second is Grothendieck's theorem that a
finite-type algebra over a $G$-ring is a $G$-ring. Both are deductions from Chapter 6 together
with the formal apparatus of Chapter 4 — composition, base change and descent of regular
homomorphisms — and neither requires a new idea about formal fibers.

One hypothesis propagates from Chapter 6 and must be stated explicitly each time.

**Definition 7.1.** A noetherian ring $A$ has **$p$-finite residue fields** if for every prime
$\mathfrak p$ whose residue field $\kappa(\mathfrak p)$ has characteristic $p>0$ one has
$[\kappa(\mathfrak p):\kappa(\mathfrak p)^p]<\infty$.

The condition is vacuous when all residue fields have characteristic zero, it holds for every
perfect field and for $\mathbf Z$, and Section 7.3 shows that it is inherited by every algebra
essentially of finite type over such a ring; so it is satisfied by every ring occurring in the
applications. It enters here only through Theorem 6.20, which requires the residue field of the
complete local ring in question to have finite $p$-degree.

### 7.1 Testing the G-property at maximal ideals

The definition of a $G$-ring quantifies over all primes, but the completions that occur at
non-maximal primes are not naturally related to the completion at a maximal ideal containing them.
The bridge is provided by a prime of $\widehat{A_{\mathfrak m}}$ chosen minimal over the extension
of the small prime: the local ring there is a localization of a complete local ring, so Chapter 6
applies to it, while its fiber over the small prime is a field. Descent along a faithfully flat map
— Proposition 4.8, which needs nothing about the map beyond faithful flatness — then transfers the
conclusion back to the completion we care about.

We first record a standard flatness statement about completions of flat local maps.

**Lemma 7.2.** Let $\varphi:(R,\mathfrak m_R)\to(S,\mathfrak m_S)$ be a flat local homomorphism of
noetherian local rings. Then the induced homomorphism $\widehat R\to\widehat S$ of completions is
faithfully flat.

**Proof.** The composite $R\to S\to\widehat S$ is flat, and $\widehat R$ is flat over $R$, so for
every $R$-module $N$ and every $i$ there is a base-change identification
$\operatorname{Tor}^{\widehat R}_i(\widehat S,N\otimes_R\widehat R)=\operatorname{Tor}^R_i(\widehat S,N)$:
a free $R$-resolution of $N$ becomes, after tensoring with the flat $R$-algebra $\widehat R$, a
free $\widehat R$-resolution of $N\otimes_R\widehat R$, and tensoring that with $\widehat S$ over
$\widehat R$ returns the original complex tensored with $\widehat S$ over $R$. Taking $N=R/\mathfrak m_R$
and using $R/\mathfrak m_R\otimes_R\widehat R=\widehat R/\mathfrak m_R\widehat R$, the residue field
of $\widehat R$, gives

$$
\operatorname{Tor}_1^{\widehat R}\big(\widehat S,\widehat R/\mathfrak m_R\widehat R\big)
=\operatorname{Tor}_1^R\big(\widehat S,R/\mathfrak m_R\big)=0,
$$

because $\widehat S$ is flat over $R$. The ring $\widehat S$ is a noetherian local ring and the map
$\widehat R\to\widehat S$ is local, so $\widehat S$ is ideal-separated for the maximal-adic
topology of $\widehat R$; the local criterion of flatness therefore makes $\widehat S$ flat over
$\widehat R$, and a flat local homomorphism is faithfully flat. $\square$

**Theorem 7.3 (localization theorem).** Let $A$ be a noetherian ring with $p$-finite residue
fields, and suppose that $A_{\mathfrak m}\to\widehat{A_{\mathfrak m}}$ is regular for every maximal
ideal $\mathfrak m$. Then $A$ is a $G$-ring.

**Proof.** Let $\mathfrak p$ be a prime of $A$ and choose a maximal ideal
$\mathfrak m\supseteq\mathfrak p$. Since $A_{\mathfrak p}=(A_{\mathfrak m})_{\mathfrak pA_{\mathfrak m}}$,
we may replace $A$ by $A_{\mathfrak m}$ and assume that $(A,\mathfrak m)$ is local with
$A\to\widehat A$ regular; we must show that $A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ is
regular.

_Choice of a prime upstairs._ Let $P$ be a prime of $\widehat A$ minimal among those containing
$\mathfrak p\widehat A$. Then $P\cap A=\mathfrak p$: certainly $P\cap A\supseteq\mathfrak p$, and
if $\mathfrak p'=P\cap A$ were strictly larger, going-down for the faithfully flat map
$A\to\widehat A$ would produce a prime $P'\subseteq P$ with $P'\cap A=\mathfrak p$, whence
$P'\supseteq\mathfrak p\widehat A$, contradicting minimality unless $P'=P$.

_The map $A_{\mathfrak p}\to\widehat A_P$ is regular._ It is flat and local. For a prime
$\mathfrak q\subseteq\mathfrak p$ of $A$, its fiber is

$$
\widehat A_P\otimes_{A_{\mathfrak p}}\kappa(\mathfrak q)
=\big(\widehat A\otimes_A\kappa(\mathfrak q)\big)_P,
$$

a localization of the formal fiber of $A$ at $\mathfrak q$, which is geometrically regular by
hypothesis; localizations of geometrically regular algebras are geometrically regular, by
Corollary 2.10 applied after each finite base field extension. So all fibers are geometrically
regular.

_The ring $\widehat A_P$ is a $G$-ring._ It is a localization of the complete noetherian local ring
$\widehat A$, whose residue field is $A/\mathfrak m$ and therefore of finite $p$-degree; hence
Theorem 6.20 applies, and $\widehat A_P\to\widehat{\widehat A_P}$ is regular.

_Composition and descent._ By Proposition 4.6 the composite
$A_{\mathfrak p}\to\widehat A_P\to\widehat{\widehat A_P}$ is regular. Completion is functorial for
local homomorphisms, so this composite factors as

$$
A_{\mathfrak p}\longrightarrow\widehat{A_{\mathfrak p}}
\longrightarrow\widehat{\widehat A_P},
$$

and the second map is faithfully flat by Lemma 7.2 applied to the flat local homomorphism
$A_{\mathfrak p}\to\widehat A_P$. Proposition 4.8 now descends regularity:
$A_{\mathfrak p}\to \widehat{A_{\mathfrak p}}$ is regular. $\square$

It is worth noting how much of the work is done by Corollary 2.11, hidden inside Proposition 4.8.
No hypothesis whatever is available on the fibers of
$\widehat{A_{\mathfrak p}}\to\widehat{\widehat A_P}$; all that is known is faithful flatness, and
the descent of regularity along faithfully flat maps — which rests on Serre's criterion — is what
makes the last step legitimate.

### 7.2 Finite-type algebras over a G-ring

Everything is now in place for Grothendieck's theorem. The proof is the reduction sketched in
Section 1.3: localize so that the base is local, base change to its completion — which costs
exactly one application of the hypothesis — and appeal to Chapter 6 over the resulting complete
base.

**Theorem 7.4 (Grothendieck).** Let $A$ be a noetherian $G$-ring with $p$-finite residue fields.
Then every algebra essentially of finite type over $A$ is a $G$-ring. In particular
$A[x_1,\ldots,x_n]$ is a $G$-ring, as is every finite-type $A$-algebra, every quotient of one and
every localization of one.

**Proof.** Let $B$ be essentially of finite type over $A$ and let $\mathfrak n$ be a prime of $B$;
we must show that $B_{\mathfrak n}\to\widehat{B_{\mathfrak n}}$ is regular. Put
$\mathfrak p=\mathfrak n\cap A$. The ring $R=A_{\mathfrak p}$ is a noetherian local $G$-ring by
Lemma 4.10, so $R\to\widehat R$ is regular, and $B_{\mathfrak n}$ is a local ring essentially of
finite type over $R$ with $\mathfrak m_R\subseteq\mathfrak m_{B_{\mathfrak n}}$.

Apply Lemma 6.10 to $R\to B_{\mathfrak n}$. It produces $C=B_{\mathfrak n}\otimes_R\widehat R$,
noetherian and essentially of finite type over the complete local ring $\widehat R$, together with
a maximal ideal $\mathfrak n'$ of $C$ such that $\widehat{C_{\mathfrak n'}}=\widehat{B_{\mathfrak n}}$,
and it reduces the assertion to the regularity of $C_{\mathfrak n'}\to\widehat{C_{\mathfrak n'}}$.
The residue field of $\widehat R$ is $\kappa(\mathfrak p)$, which has finite $p$-degree by
hypothesis; so Theorem 6.20 applies to $\widehat R$ and makes $C$ — and hence its localization
$C_{\mathfrak n'}$ — a $G$-ring. Lemma 6.10(4) concludes. $\square$

For the class of rings just described to be closed under the operations of the theorem, the
hypothesis on residue fields must propagate as well. It does, by the classical multiplicativity of
the $p$-degree.

**Lemma 7.5 ($p$-degree in field extensions).** Let $K\subseteq L$ be fields of characteristic $p$.

1. If $L/K$ is finite, then $[L:L^p]=[K:K^p]$.
2. If $L=K(t_1,\ldots,t_r)$ is purely transcendental, then $[L:L^p]=[K:K^p]\cdot p^r$.
3. If $L/K$ is finitely generated, then $[L:L^p]=[K:K^p]\cdot p^{\operatorname{trdeg}_KL}$; in
   particular $[L:L^p]<\infty$ as soon as $[K:K^p]<\infty$.

**Proof.** (1) The Frobenius $x\mapsto x^p$ is an isomorphism of $L$ onto $L^p$ carrying $K$ onto
$K^p$, so $[L^p:K^p]=[L:K]$. Multiplying degrees in $K^p\subseteq L^p\subseteq L$ and in
$K^p\subseteq K\subseteq L$ gives $[L:L^p][L^p:K^p]=[L:K^p]=[L:K][K:K^p]$, whence
$[L:L^p]=[K:K^p]$.

(2) Here $L^p=K^p(t_1^p,\ldots,t_r^p)$. A $K^p$-basis of $K$ remains linearly independent over
$K^p(t_1,\ldots,t_r)$ because the $t_i$ are transcendental, so $[K(t):K^p(t)]=[K:K^p]$; and
$[K^p(t_1,\ldots,t_r):K^p(t_1^p,\ldots,t_r^p)]=p^r$, the monomials $t^\alpha$ with $\alpha_i<p$
forming a basis. Multiply the two degrees.

(3) Choose a transcendence basis $t_1,\ldots,t_r$ of $L/K$; then $L/K(t)$ is finite, and (1)
applied to it together with (2) gives the formula. $\square$

**Corollary 7.6 (the permanence package).** Let $A$ be a noetherian $G$-ring with $p$-finite
residue fields. Then each of the following is again a noetherian $G$-ring with $p$-finite residue
fields: every localization $S^{-1}A$; every quotient $A/I$; every finite $A$-algebra; every algebra
essentially of finite type over $A$; and every completion $\widehat{A_{\mathfrak p}}$. Moreover,
for every prime $\mathfrak q$ of such a ring $B$, the completion map
$B_{\mathfrak q}\to\widehat{B_{\mathfrak q}}$ is faithfully flat and regular, so it preserves and
reflects regularity, reducedness and normality.

**Proof.** The $G$-property: Lemma 4.10 for localizations and quotients, Proposition 4.12 for
finite algebras, Theorem 7.4 for algebras essentially of finite type, and Theorem 6.20 (with $m=0$)
for the complete local rings $\widehat{A_{\mathfrak p}}$, whose residue field
$\kappa(\mathfrak p)$ has finite $p$-degree.

The residue fields: those of a localization or a quotient are residue fields of $A$; those of a
finite $A$-algebra are finite extensions of residue fields of $A$, so Lemma 7.5(1) applies; and if
$B$ is essentially of finite type over $A$ and $\mathfrak q$ is a prime of $B$ over $\mathfrak p$,
then $B\otimes_A\kappa(\mathfrak p)$ is essentially of finite type over $\kappa(\mathfrak p)$, so
$\kappa(\mathfrak q)$ is a finitely generated field extension of $\kappa(\mathfrak p)$ and
Lemma 7.5(3) applies. For $\widehat{A_{\mathfrak p}}$, use Book 1, Corollary 13.31: it is a
quotient of a Cohen coordinate ring $T$ built on the residue field $\kappa(\mathfrak p)$, whose
residue fields all have finite $p$-degree — by Lemma 6.13 in characteristic $p$, and vacuously in
characteristic zero — and the residue fields of a quotient are among those of $T$.

The last sentence is Theorem 4.13. $\square$

### 7.3 The bases that occur in arithmetic

**Theorem 7.7.** The following noetherian rings are $G$-rings, and all of them have $p$-finite
residue fields except where noted; consequently, by Theorem 7.4 and Corollary 7.6, every algebra
essentially of finite type over any of them is again a $G$-ring with $p$-finite residue fields.

1. Every field $k$ with $[k:k^p]<\infty$ in characteristic $p$; in particular every perfect field,
   every finite field, and every field of characteristic zero.
2. Every complete noetherian local ring whose residue field has finite $p$-degree; in particular
   every complete discrete valuation ring with perfect residue field, such as $\mathbf Z_p$ and
   $k[[t]]$ with $k$ perfect.
3. Every Dedekind domain $A$ of characteristic zero — for instance $\mathbf Z$, the ring of
   integers of a number field, and every localization of such a ring. Such an $A$ has $p$-finite
   residue fields exactly when its residue fields at maximal ideals do, which holds for
   $\mathbf Z$ and for rings of integers of number fields, whose residue fields are finite.

**Proof.** (1) A field is a complete local ring, so this is Theorem 6.5, or Theorem 6.20 with
$A=k$. The residue field is $k$ itself.

(2) Theorem 6.5. The residue fields of a complete local ring $A$ have finite $p$-degree by the
argument given in Corollary 7.6: $A$ is a quotient of a Cohen coordinate ring $T$ and, by
Lemma 6.13, all residue fields of $T$ have finite $p$-degree in characteristic $p$; in
characteristic zero the condition is vacuous.

(3) Let $\mathfrak p$ be a prime of the Dedekind domain $A$ with fraction field $K$. If
$\mathfrak p=0$ then $A_{\mathfrak p}=K$ is its own completion and the only formal fiber is $K$.
Otherwise $A_{\mathfrak p}$ is a discrete valuation ring and $\widehat{A_{\mathfrak p}}$ is a
complete discrete valuation ring with the same residue field; it has exactly two primes, so there
are two formal fibers, namely $\kappa(\mathfrak p)$ over $\mathfrak p$ and
$\operatorname{Frac}\widehat{A_{\mathfrak p}}$ over $0$. Both are fields, hence regular, and both
are extensions of fields of characteristic zero — $\kappa(\mathfrak p)$ over itself, and
$\operatorname{Frac}\widehat{A_{\mathfrak p}}$ over $K$, which has characteristic zero because $A$
does. Theorem 3.7 makes them geometrically regular, so $A$ is a $G$-ring. The statement about
residue fields is immediate, $\kappa(0)=K$ having characteristic zero. $\square$

The three families are exactly the bases over which arithmetic geometry constructs models: a
field, for varieties; a Dedekind domain of characteristic zero, for arithmetic surfaces over
$\operatorname{Spec}\mathbf Z$ or over the ring of integers of a number field; and a complete
discrete valuation ring, for the local analysis at one place. Theorem 7.4 says that the
$G$-property, once known for the base, is available on every chart of every finite-type scheme
over it — on the charts of a blowup, on the local rings at generic points of exceptional divisors,
and on the finite covers appearing in a normalization. That is the permanence which Chapter 1
identified as the point of the whole theory, and the remaining chapters convert it into openness of
regular loci, finiteness of normalization, and the excellence package.

## 8. Openness of regular loci

The second component of excellence asks that singularities form a closed set. On a variety this is
familiar: the singular locus is cut out by the vanishing of Jacobian minors, hence is closed. In
general it can fail, and it fails for the same kind of ring for which formal fibers misbehave. What
is needed is a criterion turning a _generic_ statement — the regular locus is nonempty and open at
the generic point of each integral closed subscheme — into a global one, and then a supply of
generic statements.

Both ingredients are at hand. The criterion is topological and is proved in Section 8.1; the only
ring-theoretic input it needs is that regularity is preserved by localization, which is
Corollary 2.10. The generic statements come from the Jacobian machinery of Chapter 6: the same
computation that made the formal fibers regular shows that a domain essentially of finite type over
a Cohen coordinate ring is regular in a neighbourhood of its generic point. Section 8.3 then names
the combination of Chapters 7 and 8 — the $G$-property together with openness for all finite-type
algebras — as quasi-excellence.

### 8.1 Nagata's criterion

**Definition 8.1.** Let $A$ be a noetherian ring. Its **regular locus** is
$\operatorname{Reg}(A)=\{\mathfrak p\in\operatorname{Spec}A:A_{\mathfrak p}\ \text{is regular}\}$.
The ring $A$ is **$J$-$0$** if $\operatorname{Reg}(A)$ contains a nonempty open subset of
$\operatorname{Spec}A$; it is **$J$-$1$** if $\operatorname{Reg}(A)$ is open; and it is
**$J$-$2$** if every finite-type $A$-algebra is $J$-$1$.

The $J$-$2$ condition is quantified over finite-type algebras from the start, so it passes to
finite-type algebras and to localizations of these by its own definition, exactly as universal
catenarity does. What has to be proved is that it holds at all.

Two elementary remarks are used constantly. First, $\operatorname{Reg}(A)$ is stable under
generization: if $\mathfrak q\subseteq\mathfrak p$ and $A_{\mathfrak p}$ is regular, then
$A_{\mathfrak q}=(A_{\mathfrak p})_{\mathfrak qA_{\mathfrak p}}$ is regular by Corollary 2.10.
Second, openness of $\operatorname{Reg}$ is local on the spectrum: since
$\operatorname{Reg}(A)\cap D(f)=\operatorname{Reg}(A_f)$, the locus is open as soon as it is open
on each member of a covering family of basic opens.

**Lemma 8.2 (a topological criterion).** Let $X$ be the spectrum of a noetherian ring and let
$U\subseteq X$ be a subset such that

1. $U$ is stable under generization, and
2. for every $x\in U$ the closed set $\overline{\{x\}}$ contains a nonempty open subset of itself
   which is contained in $U$.

Then $U$ is open.

**Proof.** Put $Z=X\setminus U$ and let $Z'=\overline Z$; we show $Z'=Z$, which makes $Z$ closed.
Since $X$ is a noetherian space, $Z'$ has finitely many irreducible components
$Z'_1,\ldots,Z'_r$, with generic points $z_1,\ldots,z_r$.

Fix $i$ and suppose $z_i\in U$. By (2) there is a nonempty open subset $V$ of
$\overline{\{z_i\}}=Z'_i$ with $V\subseteq U$. The set $W=Z'\setminus\bigcup_{j\neq i}Z'_j$ is a
nonempty open subset of $Z'$ contained in $Z'_i$, and $Z$ is dense in $Z'$, so
$W\cap Z\neq \emptyset$; as $W$ is dense in $Z'_i$, the set $Z\cap Z'_i$ is dense in $Z'_i$ and
therefore meets the nonempty open $V$. This contradicts $V\subseteq U$ and $Z\cap U=\emptyset$.
Hence $z_i\in Z$ for every $i$.

Now let $x\in Z'$, say $x\in Z'_i$. Then $z_i$ is a generization of $x$. If $x$ were in $U$, then
(1) would put $z_i$ in $U$, contradicting $z_i\in Z$. So $x\in Z$, giving $Z'\subseteq Z$.
$\square$

The criterion that follows is the form of Nagata's theorem used here. It converts a statement about
_domains_ — where a nonempty open regular locus is a generic statement, provable by a Jacobian
computation — into openness for all finite-type algebras. Its proof is a spreading-out argument:
regularity at a prime means the maximal ideal is generated by as few elements as its height allows,
and both the generators and the height persist in a neighbourhood.

**Theorem 8.3 (openness criterion).** Let $A$ be a noetherian ring such that every finite-type
$A$-algebra which is a domain is $J$-$0$. Then $A$ is $J$-$2$.

**Proof.** Let $C$ be a finite-type $A$-algebra; we verify the two hypotheses of Lemma 8.2 for
$U=\operatorname{Reg}(C)\subseteq X=\operatorname{Spec}C$. Stability under generization is
Corollary 2.10.

For the second hypothesis, let $\mathfrak q\in\operatorname{Reg}(C)$ and put
$c=\operatorname{ht} \mathfrak q$, so that $\mathfrak qC_{\mathfrak q}$ is generated by a regular
system of parameters $f_1,\ldots,f_c\in\mathfrak q$. The ideal $\mathfrak q$ is finitely
generated and $\mathfrak qC_{\mathfrak q}=(f_1,\ldots,f_c)C_{\mathfrak q}$, so there is
$g\notin\mathfrak q$ with $g\mathfrak q\subseteq(f_1,\ldots,f_c)$; hence

$$
\mathfrak qC_{\mathfrak q'}=(f_1,\ldots,f_c)C_{\mathfrak q'}
\qquad\text{for every prime }\mathfrak q'\ \text{with}\ g\notin\mathfrak q' .
\tag{8.1}
$$

The quotient $C/\mathfrak q$ is a finite-type $A$-algebra domain, hence $J$-$0$ by hypothesis:
there is a nonempty open $V\subseteq\operatorname{Spec}(C/\mathfrak q)=\overline{\{\mathfrak q\}}$
on which $C/\mathfrak q$ is regular. Shrinking $V$ to $V\cap D(g)$, which is still nonempty because
$\mathfrak q$ itself lies in it, we may assume $g\notin\mathfrak q'$ for all $\mathfrak q'\in V$.

Fix $\mathfrak q'\in V$ and write $d'=\dim(C/\mathfrak q)_{\mathfrak q'}$. By regularity of
$(C/\mathfrak q)_{\mathfrak q'}$ its maximal ideal is generated by $d'$ elements, which we lift to
$C_{\mathfrak q'}$; together with $f_1,\ldots,f_c$, which generate $\mathfrak qC_{\mathfrak q'}$ by
$(8.1)$, they generate $\mathfrak q'C_{\mathfrak q'}$. Hence
$\mu(\mathfrak q'C_{\mathfrak q'})\leq c+d'$. On the other hand a chain of primes of length $c$
below $\mathfrak q$ followed by one of length $d'$ from $\mathfrak q$ to $\mathfrak q'$ gives
$\dim C_{\mathfrak q'}\geq c+d'$. Since always
$\dim C_{\mathfrak q'}\leq\mu(\mathfrak q'C_{\mathfrak q'})$ by Krull's height theorem, all three
numbers agree and $C_{\mathfrak q'}$ is regular. Thus $V\subseteq\operatorname{Reg}(C)$, and
Lemma 8.2 applies. $\square$

### 8.2 From the G-property to openness

It remains to supply the generic input. The Jacobian computations of Chapter 6 do exactly that,
and it is worth isolating what they proved. In equal characteristic $p$ the proof of
Proposition 6.16 established the following statement about $P=T[y_1,\ldots,y_m]$ over a Cohen
coordinate ring $T$ with $[k:k^p]<\infty$: for every prime $q$ of $P$ of height $c$ and every
regular system of parameters $f_1,\ldots,f_c$ of $P_q$, the matrix $(D_i(f_j))$ formed with the
partial derivatives of Lemma 6.14 has rank $c$ modulo $q$. When $\operatorname{Frac}T$ has
characteristic zero, the proof of Theorem 6.19, Case 2, established the same conclusion for primes
$q$ with $q\cap T=0$, using the derivations $\partial/\partial y_j$. Both statements are used
again now, this time downstairs rather than in a completion.

**Proposition 8.4 (generic regularity).** Let $T$ be a Cohen coordinate ring with residue field of
finite $p$-degree, or a field $k$ with $[k:k^p]<\infty$. Then every domain of finite type over $T$
is $J$-$0$.

**Proof.** Induct on $\dim T$; write the domain as $D=P/I$ with $P=T[y_1,\ldots,y_m]$ and $I$ a
prime, and put $c=\operatorname{ht}I$.

Suppose first that $T$ has equal characteristic $p$, or that $I\cap T=0$. Let $f_1,\ldots,f_c\in I$
be a regular system of parameters of the regular local ring $P_I$ — regular by Corollary 2.16 and
Corollary 2.10 — and let $D_1,\ldots,D_N$ be the derivations recalled above. By the statements just
quoted, some $c\times c$ minor $\Delta$ of $(D_i(f_j))$ lies outside $I$. Since $I$ is finitely
generated and $IP_I=(f_1,\ldots,f_c)P_I$, there is $g\notin I$ with
$gI\subseteq(f_1,\ldots,f_c)$.

Let $\mathfrak q\supseteq I$ be a prime containing neither $g$ nor $\Delta$. Then
$IP_{\mathfrak q}=(f_1,\ldots,f_c)P_{\mathfrak q}$, the element $\Delta$ is a unit of
$P_{\mathfrak q}$, and $P_{\mathfrak q}$ is regular; Lemma 6.15 makes $f_1,\ldots,f_c$ part of a
regular system of parameters, so that

$$
D_{\mathfrak q}=P_{\mathfrak q}/IP_{\mathfrak q}
$$

is regular. The primes in question form an open subset of $\operatorname{Spec}D$, nonempty because
it contains $I$ itself. Hence $D$ is $J$-$0$.

Now suppose that $\operatorname{Frac}T$ has characteristic zero and $\mathfrak p=I\cap T\neq0$.
Then $D$ is a finite-type algebra over $T/\mathfrak p$, a complete local domain of dimension
$\dim T-\operatorname{ht}\mathfrak p<\dim T$, which by Book 1, Theorem 13.34, is finite over a
Cohen coordinate ring $T'$ of that smaller dimension; so $D$ is a finite-type $T'$-domain and the
induction hypothesis applies. When $\dim T=0$ the ring $T$ is a field and $I\cap T=0$
automatically, so the induction starts. $\square$

**Theorem 8.5 (openness of regular loci).** Each of the following noetherian rings is $J$-$2$, and
therefore so is every ring essentially of finite type over one of them:

1. every field $k$ with $[k:k^p]<\infty$ in characteristic $p$;
2. every complete noetherian local ring whose residue field has finite $p$-degree;
3. every Dedekind domain of characteristic zero with $p$-finite residue fields — in particular
   $\mathbf Z$, every ring of integers of a number field, and every localization of one.

**Proof.** By Theorem 8.3 it suffices in each case to prove that every finite-type algebra domain
over the base is $J$-$0$.

(2) By Book 1, Corollary 13.31, a complete noetherian local ring $A$ is a quotient of a Cohen
coordinate ring $T$, whose residue field is that of $A$; so a finite-type $A$-algebra is a
finite-type $T$-algebra and Proposition 8.4 applies. Case (1) is the case $T=k$.

(3) Let $A$ be such a Dedekind domain, $K=\operatorname{Frac}A$, and let $D$ be a finite-type
$A$-algebra domain, say $D=P/I$ with $P=A[y_1,\ldots,y_m]$ and $I$ prime. If $I\cap A\neq0$ then
$I\cap A$ is a maximal ideal $\mathfrak p$ of $A$, and $D$ is a finite-type algebra over the field
$\kappa(\mathfrak p)$, which has finite $p$-degree by hypothesis; so (1) applies. If $I\cap A=0$,
then $P$ is regular by Corollary 2.16, $P_I$ is a localization of $K[y_1,\ldots,y_m]$ with $K$ of
characteristic zero, and the count in the proof of Theorem 6.19, Case 2, applies verbatim with $A$
in place of $T$: the second fundamental exact sequence of $K\to P_I\to\kappa(I)$ has middle term
free of rank $m$, the extension $\kappa(I)/K$ is finitely generated of transcendence degree
$m-\operatorname{ht}I$, and separably generated because $\operatorname{char}K=0$, so the Jacobian
matrix $(\partial f_j/\partial y_i)$ of a regular system of parameters of $P_I$ has rank
$\operatorname{ht}I$ modulo $I$. The argument of Proposition 8.4 then produces a nonempty open
regular locus.

Finally, $J$-$2$ passes to finite-type algebras and to localizations of these by its own
definition: a finite-type algebra over a localization of a finite-type $A$-algebra is a
localization of a finite-type $A$-algebra, and the regular locus of a localization is the trace of
the regular locus. $\square$

### 8.3 Quasi-excellent rings

**Definition 8.6.** A noetherian ring is **quasi-excellent** if it is a $G$-ring and satisfies
$J$-$2$. A locally noetherian scheme is quasi-excellent when its affine coordinate rings are.

**Theorem 8.7.** Let $A$ be a quasi-excellent ring with $p$-finite residue fields. Then every
algebra essentially of finite type over $A$, every quotient of $A$, every localization of $A$,
every finite $A$-algebra and every completion $\widehat{A_{\mathfrak p}}$ is again quasi-excellent
with $p$-finite residue fields. Moreover the following rings are quasi-excellent with $p$-finite
residue fields, hence so is everything essentially of finite type over them:

1. every field $k$ with $[k:k^p]<\infty$, in particular every perfect field;
2. every complete noetherian local ring whose residue field has finite $p$-degree, in particular
   every complete discrete valuation ring with perfect residue field;
3. $\mathbf Z$, every ring of integers of a number field, and every localization of such a ring;
   more generally every Dedekind domain of characteristic zero with $p$-finite residue fields.

**Proof.** The $G$-property and the residue field condition are Corollary 7.6. For $J$-$2$: it
passes to finite-type algebras, quotients and localizations by definition, as recorded at the end
of the proof of Theorem 8.5, and a finite $A$-algebra is in particular of finite type. For a
completion $\widehat{A_{\mathfrak p}}$, which is a complete noetherian local ring whose residue
field $\kappa(\mathfrak p)$ has finite $p$-degree, $J$-$2$ is Theorem 8.5(2).

The list is Theorem 7.7 for the $G$-property and Theorem 8.5 for $J$-$2$. $\square$

Quasi-excellence is thus stable under every operation performed on rings in the sequel, and it
holds for the bases of interest. What it does not yet contain is the dimension-theoretic condition
— universal catenarity — which is independent of the two conditions above and which Chapter 10
adds to complete the definition of excellence. Before that, Chapter 9 extracts from quasi-excellence
the finiteness of normalization, which is the property that the construction of models actually
consumes.

## 9. Nagata rings

Normalization is the first repair performed on a singular model: one replaces a reduced scheme by
the integral closure of its coordinate rings in their total rings of fractions. The construction is
useless unless it is _finite_, for otherwise the result is not a scheme of finite type over the
base and none of the tools of projective geometry apply to it. Finiteness of normalization is not
automatic; it is the content of the Nagata condition, and this chapter shows that quasi-excellence
supplies it.

The route has two halves. Locally, finiteness follows from a reduced completion: if
$\widehat{A}$ is reduced then the integral closure of a local ring $A$ in its total ring of
fractions is finite, and the $G$-property guarantees the reduced completion. Globally, the local
statements are glued by an argument that uses only one nonempty open on which the ring is already
normal — which openness of the regular locus provides. The complete local case, needed to start
the induction, is settled by a theorem of Tate and Akizuki about $t$-adically complete normal
domains.

### 9.1 Finiteness of normalization

**Definition 9.1.** Let $D$ be a noetherian domain with fraction field $K$. Then $D$ is **$N$-$1$**
if its integral closure in $K$ — its **normalization** — is a finite $D$-module, and **$N$-$2$**,
or **Japanese**, if its integral closure in every finite field extension $L/K$ is a finite
$D$-module. A noetherian ring $A$ is **Nagata** if $A/\mathfrak p$ is Japanese for every prime
$\mathfrak p$, and **universally Japanese** if every finite-type $A$-algebra is Nagata.

**Lemma 9.2 (the trace argument).** Let $D$ be a normal noetherian domain with fraction field $K$
and let $L/K$ be a finite _separable_ extension. Then the integral closure of $D$ in $L$ is a
finite $D$-module. In particular a normal noetherian domain of characteristic zero is $N$-$2$.

**Proof.** Choose a $K$-basis $e_1,\ldots,e_n$ of $L$; multiplying each $e_i$ by a suitable nonzero
element of $D$ we may assume that all $e_i$ are integral over $D$. Separability makes the trace
form $(u,v)\mapsto\operatorname{Tr}_{L/K}(uv)$ nondegenerate, so there is a dual basis
$e_1^*,\ldots,e_n^*$ with $\operatorname{Tr}(e_ie_j^*)=\delta_{ij}$. If $x\in L$ is integral over
$D$ then each $xe_i$ is integral over $D$, so its trace — a coefficient of a characteristic
polynomial, hence integral over $D$ — lies in $K$ and therefore in $D$, which is normal. Writing
$x=\sum_i\operatorname{Tr}(xe_i)e_i^*$ shows that the integral closure is contained in
$\sum_iDe_i^*$, a finite module over the noetherian ring $D$. In characteristic zero every finite
extension is separable. $\square$

The characteristic-$p$ input is the following theorem of Tate and Akizuki, which converts the
Japanese property across a complete hypersurface section. It is the reason power series rings are
Japanese without any perfectness assumption on the coefficient field.

**Lemma 9.3 (Tate–Akizuki).** Let $R$ be a normal noetherian domain, let $0\neq t\in R$, and
suppose that $R$ is $t$-adically complete and that $R/tR$ is a domain which is $N$-$2$. Then $R$ is
$N$-$2$.

**Proof.** Write $K=\operatorname{Frac}R$ and let $L/K$ be finite. If $\operatorname{char}K=0$, or
more generally if $L/K$ is separable, this is Lemma 9.2. In general there is a finite purely
inseparable extension $K'/K$, obtained by adjoining finitely many $p^r$-th roots of the
coefficients of minimal polynomials of generators of $L$, such that $LK'/K'$ is separable. If the
integral closure $R'$ of $R$ in $K'$ is finite, then $R'$ is a normal noetherian domain, the trace
argument applies to $LK'/K'$, and the integral closure of $R$ in $L$ — a submodule of the integral
closure of $R'$ in $LK'$ — is finite over $R$. So we may assume $L/K$ purely inseparable, say
$L^q\subseteq K$ with $q=p^r$; enlarging $L$ by one further purely inseparable extension, which
only enlarges the module to be shown finite, we may also assume that $t$ has a $q$-th root $y\in L$.

Let $S$ be the integral closure of $R$ in $L$. Since $L/K$ is purely inseparable,
$\operatorname{Spec}S\to\operatorname{Spec}R$ is injective, as in Lemma 6.3, and $S$ is integral
over $R$, so there is exactly one prime $\mathfrak q$ of $S$ over the prime $tR$ — prime because
$R/tR$ is a domain. We claim

$$
\mathfrak q=yS .
$$

Indeed $y^q=t\in\mathfrak q$ gives $y\in\mathfrak q$; conversely, if $z\in\mathfrak q$ then
$z^q\in K$ is integral over $R$, hence lies in $R$, and lies in $\mathfrak q\cap R=tR$, so
$(z/y)^q=z^q/t\in R$ and $z/y$ is integral over $R$, that is, $z\in yS$.

The localization $R_{tR}$ is a normal noetherian local domain of dimension one, hence a discrete
valuation ring; let $v$ be its valuation. Its unique extension to $L$ is $w(z)=v(z^q)/q$, and
$S_{\mathfrak q}$, being the integral closure of $R_{tR}$ in $L$, is exactly
$\{z\in L:w(z)\geq0\}$: a $q$-th power of such a $z$ lies in $R_{tR}$, so $z$ is integral. Thus
$S_{\mathfrak q}$ is a discrete valuation ring with residue field
$\operatorname{Frac}(S/\mathfrak q)$, and that residue field is finite over
$\operatorname{Frac}(R/tR)$: lifting elements linearly independent over the residue field and
normalizing them to valuation zero produces elements of $L$ linearly independent over $K$, so
their number is at most $[L:K]$.

Consequently $S/\mathfrak q$ is a domain, integral over $R/tR$, whose fraction field is finite over
$\operatorname{Frac}(R/tR)$; the $N$-$2$ hypothesis therefore makes $S/\mathfrak q=S/yS$ a finite
$R/tR$-module. Each layer of the filtration
$S/y^qS\supseteq yS/y^qS\supseteq\cdots\supseteq y^{q-1}S/y^qS\supseteq0$ is a quotient of $S/yS$,
by multiplication by a power of $y$, so $S/tS=S/y^qS$ is a finite $R/tR$-module, and in particular
a finite $R$-module.

Finally $\bigcap_nt^nS=0$: if $z$ lies in every $t^nS$, then $z^q\in K$ is integral over $R$, hence
lies in $R$, and lies in $t^{nq}S\cap R=t^{nq}R$ — for $a=t^ms$ with $a\in R$, $s\in S$ forces
$s=a/t^m\in S\cap K=R$ — so $z^q=0$ by the Krull intersection theorem. Now choose
$s_1,\ldots,s_m\in S$ lifting generators of $S/tS$ and put $M=\sum_iRs_i$. Then $S=M+tS$, hence
$S=M+t^nS$ for every $n$; a finite module over the $t$-adically complete noetherian ring $R$ is
$t$-adically complete, so the successive approximations converge in $M$ and their difference from
a given element of $S$ lies in $\bigcap_nt^nS=0$. Therefore $S=M$ is finite over $R$. $\square$

**Corollary 9.4 (Cohen coordinate rings are Japanese).** Every field is $N$-$2$; every complete
discrete valuation ring is $N$-$2$; and $k[[x_1,\ldots,x_n]]$ and $C_0[[x_1,\ldots,x_n]]$ are
$N$-$2$ for every field $k$ and every Cohen ring $C_0$.

**Proof.** For a field the integral closure in a finite extension is that extension, a finite
module. A complete discrete valuation ring $R$ with uniformizer $t$ is a normal noetherian domain,
$t$-adically complete, with $R/tR$ a field; Lemma 9.3 applies. For the power series rings, induct
on the number of variables: $T=k[[x_1,\ldots,x_n]]$ is a complete regular local ring by Book 1,
Lemma 13.29, hence normal — a regular ring satisfies $R_1$ by Corollary 2.10 and $S_2$ because
regular local rings are Cohen–Macaulay by Theorem 2.4, so Serre's criterion applies — it is
$x_n$-adically complete, and $T/x_nT=k[[x_1,\ldots,x_{n-1}]]$ is a domain which is $N$-$2$ by
induction. The same induction applies to $C_0[[x_1,\ldots,x_n]]$, starting from the Cohen ring
$C_0$. $\square$

**Proposition 9.5 (complete local rings are Nagata).** Every complete noetherian local ring is
Nagata.

**Proof.** A quotient of a complete noetherian local ring by a prime is again one, by Book 1,
Lemma 13.2, so it suffices to show that a complete local domain $B$ is Japanese. By Book 1,
Theorem 13.34 — with Book 1, Theorem 13.15 in equal characteristic and Book 1, Theorems 13.21 and
13.25 in mixed characteristic — there is a finite injection $T\hookrightarrow B$ with $T$ a Cohen
coordinate ring of the same dimension. Let $L$ be a finite extension of $\operatorname{Frac}B$;
then $L$ is finite over $\operatorname{Frac}T$, so the integral closure of $T$ in $L$ is a finite
$T$-module by Corollary 9.4. That integral closure coincides with the integral closure of $B$ in
$L$, by transitivity of integrality, and being finite over $T$ it is finite over $B$. $\square$

**Proposition 9.6 (analytically unramified implies $N$-$1$).** Let $(A,\mathfrak m)$ be a
noetherian local ring whose completion $\widehat A$ is reduced. Then the integral closure of $A$ in
its total ring of fractions is a finite $A$-module. In particular a local domain with reduced
completion is $N$-$1$.

**Proof.** Faithful flatness embeds $A$ in $\widehat A$, so $A$ is reduced. Let
$\mathfrak p_1,\ldots,\mathfrak p_s$ be the minimal primes of $\widehat A$; since $\widehat A$ is
reduced, its total ring of fractions is
$Q(\widehat A)=\prod_i\operatorname{Frac} (\widehat A/\mathfrak p_i)$, and the integral closure
$S$ of $\widehat A$ in $Q(\widehat A)$ is the product of the normalizations of the domains
$\widehat A/\mathfrak p_i$, hence a finite $\widehat A$-module by Proposition 9.5.

Let $A'$ be the integral closure of $A$ in $Q(A)$. A nonzerodivisor of $A$ stays a nonzerodivisor
in $\widehat A$, by flatness, so $Q(A)\otimes_A\widehat A$ is a localization of $\widehat A$ inside
$Q(\widehat A)$ and there are inclusions

$$
A'\otimes_A\widehat A\subseteq Q(A)\otimes_A\widehat A\subseteq Q(\widehat A).
$$

The left-hand ring is integral over $\widehat A$, hence a $\widehat A$-submodule of $S$, hence
finite. Choose $f_1,\ldots,f_r\in A'$ whose images generate it. The cokernel of
$\sum_iAf_i\to A'$ becomes zero after tensoring with the faithfully flat $A$-algebra
$\widehat A$, so it is zero, and $A'$ is finite over $A$. $\square$

### 9.2 Quasi-excellent rings are universally Japanese

Proposition 9.6 is local. Passing to a global statement is the step at which the openness of the
regular locus enters: it supplies a single nonempty open on which the ring is already normal, and
that is enough to organize the local finiteness statements into one.

**Lemma 9.7 (globalization).** Let $D$ be a noetherian domain with fraction field $K$ such that

1. $D_f$ is normal for some $f\neq0$, and
2. $D_{\mathfrak m}$ is $N$-$1$ for every maximal ideal $\mathfrak m$.

Then $D$ is $N$-$1$.

**Proof.** Let $D'\subseteq K$ be the normalization. Integral closure commutes with localization,
so $D'_{\mathfrak p}=(D_{\mathfrak p})'$ for every prime $\mathfrak p$; by (2) and the fact that
every prime is contained in a maximal ideal, $D'_{\mathfrak p}$ is a finite $D_{\mathfrak p}$-module
for _every_ prime $\mathfrak p$. By (1), $D'_f=(D_f)'=D_f$, so every element of $D'$ has the form
$d/f^n$. Setting

$$
M_n=D'\cap f^{-n}D\qquad(n\geq0),
$$

we obtain an increasing chain of $D$-submodules of $K$ with union $D'$; each $M_n$ is finite,
since $f^nM_n$ is a $D$-submodule of $D$, that is, an ideal of the noetherian ring $D$.

Localization commutes with the intersection of two submodules of $K$, so
$(M_n)_{\mathfrak p}=D'_{\mathfrak p}\cap f^{-n}D_{\mathfrak p}$. Because $D'_{\mathfrak p}$ is
generated by finitely many elements of $D_{f,\mathfrak p}$, there is $n(\mathfrak p)$ with
$D'_{\mathfrak p}\subseteq f^{-n}D_{\mathfrak p}$, hence $(M_n)_{\mathfrak p}=D'_{\mathfrak p}$, for
all $n\geq n(\mathfrak p)$.

Put $V_n=\operatorname{Supp}(M_{n+1}/M_n)$, a closed subset of $\operatorname{Spec}D$ since
$M_{n+1}/M_n$ is a finite module. These sets decrease: suppose
$(M_n)_{\mathfrak p}=(M_{n+1})_{\mathfrak p}$ and let $x\in(M_{n+2})_{\mathfrak p}$, so
$x\in D'_{\mathfrak p}$ and $f^{n+2}x\in D_{\mathfrak p}$. Then $y=fx$ lies in $D'_{\mathfrak p}$
and satisfies $f^{n+1}y\in D_{\mathfrak p}$, so $y\in(M_{n+1})_{\mathfrak p}=(M_n)_{\mathfrak p}$,
whence $f^{n+1}x=f^ny\in D_{\mathfrak p}$ and $x\in(M_{n+1})_{\mathfrak p}$. Thus
$V_{n+1}\subseteq V_n$.

A descending chain of closed subsets of the noetherian space $\operatorname{Spec}D$ stabilizes,
say $V_n=V$ for $n\geq n_0$; and $V=\emptyset$, because every prime $\mathfrak p$ fails to lie in
$V_n$ once $n\geq n(\mathfrak p)$. A finite module with empty support is zero, so $M_{n+1}=M_n$ for
$n\geq n_0$ and $D'=M_{n_0}$ is finite. $\square$

**Theorem 9.8 (quasi-excellent implies universally Japanese).** Let $A$ be a quasi-excellent
noetherian ring with $p$-finite residue fields. Then:

1. every finite-type $A$-algebra domain $D$ is $N$-$2$, that is, its integral closure in every
   finite extension of $\operatorname{Frac}D$ is a finite $D$-module;
2. every finite-type $A$-algebra, and every localization of one, is Nagata;
3. $A$ is universally Japanese.

**Proof.** (1) Let $D$ be a finite-type $A$-algebra domain. By Theorem 7.4 it is a $G$-ring, so for
every maximal ideal $\mathfrak m$ the map $D_{\mathfrak m}\to\widehat{D_{\mathfrak m}}$ is regular;
since $D_{\mathfrak m}$ is a domain, hence reduced, Proposition 4.5(1) makes
$\widehat{D_{\mathfrak m}}$ reduced, and Proposition 9.6 makes $D_{\mathfrak m}$ an $N$-$1$ ring.

Since $A$ is $J$-$2$, the regular locus of $D$ is open; it contains the generic point, because
$D_{(0)}=\operatorname{Frac}D$ is a field, so it contains a nonempty basic open $D(f)$. Then $D_f$
is a regular ring, hence normal: it satisfies $R_1$ by Corollary 2.10 and $S_2$ because regular
local rings are Cohen–Macaulay, so Serre's criterion applies. Lemma 9.7 now shows that $D$ is
$N$-$1$.

For an arbitrary finite extension $L/\operatorname{Frac}D$, choose field generators of $L$ over
$\operatorname{Frac}D$ and multiply them by nonzero elements of $D$ so that they become integral
over $D$; the resulting ring $D_0=D[\beta_1,\ldots,\beta_r]$ is a finite $D$-module, hence a
finite-type $A$-algebra domain, and its fraction field is $L$. By the previous paragraph $D_0$ is
$N$-$1$, and its normalization is the integral closure of $D$ in $L$ by transitivity of
integrality; being finite over $D_0$ it is finite over $D$.

(2) A prime quotient of a finite-type $A$-algebra is a finite-type $A$-algebra domain, hence
Japanese by (1); so every finite-type $A$-algebra is Nagata. For a localization $S^{-1}B$ of such a
$B$, a prime quotient is $S^{-1}(B/\mathfrak q)$, and the integral closure of a localization in a
finite extension of its fraction field is the localization of the integral closure, hence finite.

(3) This is (2) restated. $\square$

**Corollary 9.9 (the arithmetic bases).** Let $A$ be any of the following: a field $k$ with
$[k:k^p]<\infty$; a complete noetherian local ring whose residue field has finite $p$-degree; a
Dedekind domain of characteristic zero with $p$-finite residue fields, such as $\mathbf Z$, the
ring of integers of a number field, or a localization of one. Then $A$ is universally Japanese: for
every finite-type $A$-algebra domain $D$ and every finite extension $L$ of $\operatorname{Frac}D$,
the integral closure of $D$ in $L$ is a finite $D$-module; and every algebra essentially of finite
type over $A$ is Nagata.

**Proof.** These rings are quasi-excellent with $p$-finite residue fields by Theorem 8.7, so
Theorem 9.8 applies. $\square$

Two comments delimit the statement. First, the Nagata property by itself has no finite-type
permanence: it is a condition on the prime quotients of one ring, and nothing in it refers to
algebras over that ring. What propagates is the package — geometrically regular formal fibers to
make completions reduced, and openness of regular loci to make the local statements glue — which is
exactly quasi-excellence. Second, Proposition 9.5 shows that a complete noetherian local ring is
Nagata with no hypothesis on its residue field; the finite $p$-degree hypothesis is needed only to
transport the property to finite-type algebras, where it entered through Chapters 6 and 8.

Geometrically, Corollary 9.9 says that the normalization morphism of a reduced scheme of finite
type over one of these bases is finite. That is the statement consumed whenever a singular model is
replaced by its normalization: the normalized model is again of finite type, and if the original
was proper or projective, so is the new one, a finite morphism being projective.

## 10. Excellence assembled

Three conditions have now been studied separately: geometrically regular formal fibers, openness of
regular loci, and — implicitly, through the dimension counts of Chapters 6 and 8 — the behaviour of
chains of primes. The last of these is the subject of Section 10.1; it is the easiest of the three,
because it is quantified over finite-type algebras from the outset and holds for every quotient of
a regular ring. Section 10.2 assembles the three into excellence and records the bases,
Section 10.3 states the package in the form that the construction of models of arithmetic curves
consumes, and Section 10.4 is the ledger of what this volume does and does not prove.

### 10.1 Universal catenarity

**Definition 10.1.** A noetherian ring $A$ is **catenary** if for every pair of primes
$\mathfrak q\subseteq\mathfrak p$ all saturated chains of primes from $\mathfrak q$ to
$\mathfrak p$ have the same length, and **universally catenary** if every finite-type $A$-algebra
is catenary.

Universal catenarity passes to finite-type algebras, to quotients and to localizations for the same
bookkeeping reason as $J$-$2$: a finite-type algebra over a finite-type $A$-algebra, or over a
localization of one, is a localization of a finite-type $A$-algebra, and catenarity is inherited by
quotients and localizations because chains of primes in those rings are chains of primes upstairs.
So the only thing to prove is that the condition holds at all, and for the rings of this book it
does for a structural reason: they are quotients of regular rings.

**Proposition 10.2 (regular rings are universally catenary).** A regular noetherian ring is
universally catenary. Consequently every quotient of a regular ring, every localization of such a
quotient, and every finite-type algebra over one is universally catenary.

**Proof.** Let $R$ be a regular local ring and $\mathfrak p$ a prime of height $h$. By Theorem 2.4
a regular system of parameters is a regular sequence, so $R$ is Cohen–Macaulay; by the standard
theory of Cohen–Macaulay local rings, an ideal of height $h$ contains a regular sequence of length
$h$, and the quotient of a Cohen–Macaulay local ring by a regular sequence is again
Cohen–Macaulay and equidimensional. Choosing a regular sequence $x_1,\ldots,x_h$ inside
$\mathfrak p$, the prime $\mathfrak p/(x)$ is minimal in the Cohen–Macaulay ring $R/(x)$, which is
equidimensional of dimension $\dim R-h$; hence

$$
\dim R/\mathfrak p=\dim R/(x)=\dim R-h=\dim R-\operatorname{ht}\mathfrak p .
$$

Applying this to $R_{\mathfrak p}$ and to quotients shows that for
$\mathfrak q\subseteq\mathfrak p$ one has
$\operatorname{ht}(\mathfrak p/\mathfrak q)=\operatorname{ht}\mathfrak p- \operatorname{ht}\mathfrak q$
, which is exactly the statement that all saturated chains between $\mathfrak q$ and $\mathfrak p$
have the same length. So a regular local ring is catenary, and a regular ring is catenary because
catenarity is a condition on localizations.

Now let $R$ be regular. A finite-type $R$-algebra is a quotient of a polynomial ring
$R[y_1,\ldots,y_m]$, which is regular by Corollary 2.16, hence catenary; and catenarity passes to
quotients. So $R$ is universally catenary, and so are its quotients, their localizations and their
finite-type algebras, by the bookkeeping remark above. $\square$

**Corollary 10.3.** Every algebra essentially of finite type over a complete noetherian local ring,
over a field, or over a Dedekind domain is universally catenary.

**Proof.** A complete noetherian local ring is a quotient of a Cohen coordinate ring by Book 1,
Corollary 13.31, and a Cohen coordinate ring is regular by Book 1, Lemma 13.29. A field and a
Dedekind domain are regular. Proposition 10.2 applies in each case. $\square$

### 10.2 The definition and the excellent bases

**Definition 10.4.** A noetherian ring is **excellent** if it is universally catenary, a $G$-ring,
and $J$-$2$; equivalently, if it is universally catenary and quasi-excellent. A noetherian ring is
**universally excellent** if every finite-type algebra over it is excellent, and a locally
noetherian scheme is excellent, respectively universally excellent, when its affine coordinate
rings are.

**Theorem 10.5 (permanence).** Let $A$ be an excellent ring with $p$-finite residue fields. Then
every algebra essentially of finite type over $A$, every quotient of $A$, every localization of
$A$, every finite $A$-algebra and every completion $\widehat{A_{\mathfrak p}}$ is again excellent
with $p$-finite residue fields. In particular $A$ is universally excellent.

**Proof.** Quasi-excellence and the residue field condition are Theorem 8.7. Universal catenarity
passes to finite-type algebras, quotients and localizations by definition, and a finite algebra is
of finite type. For the completion $\widehat{A_{\mathfrak p}}$, universal catenarity is
Corollary 10.3, it being a complete noetherian local ring. $\square$

**Theorem 10.6 (the excellent bases).** Each of the following noetherian rings is excellent with
$p$-finite residue fields, hence universally excellent; and every algebra essentially of finite
type over any of them is again excellent with $p$-finite residue fields:

1. every field $k$ with $[k:k^p]<\infty$ in characteristic $p$ — in particular every perfect field,
   every finite field, every algebraically closed field and every field of characteristic zero;
2. every complete noetherian local ring whose residue field has finite $p$-degree — in particular
   every complete discrete valuation ring with perfect residue field, such as $\mathbf Z_p$,
   $\mathbf F_q[[t]]$ and $k[[t]]$ with $k$ perfect;
3. $\mathbf Z$, the ring of integers of a number field, every localization of such a ring, and more
   generally every Dedekind domain of characteristic zero with $p$-finite residue fields.

**Proof.** The $G$-property is Theorem 7.7, the $J$-$2$ condition is Theorem 8.5, universal
catenarity is Corollary 10.3, and the residue field condition was checked in Theorem 7.7 and
Corollary 7.6. Theorem 10.5 propagates all of it. $\square$

### 10.3 The package for models of arithmetic curves

The construction of integral models of curves uses excellence in three distinct ways, and it uses
it not for the base ring but for the finite-type algebras built from it: the affine charts of a
projective model, the charts of a blowup, the local rings at generic points of exceptional
divisors, the finite covers arising in a normalization. The following theorem states exactly what
is available for those algebras, clause by clause.

**Theorem 10.7 (the excellence package).** Let $A$ be one of the bases listed in Theorem 10.6 — a
field of finite $p$-degree, a complete noetherian local ring whose residue field has finite
$p$-degree, or a Dedekind domain of characteristic zero with $p$-finite residue fields, such as
$\mathbf Z$, a ring of integers of a number field, or a localization of one — and let $S$ be a
scheme of finite type over $\operatorname{Spec}A$. Then:

1. _(Excellence of all charts.)_ Every affine coordinate ring of $S$, every localization of one and
   every finite algebra over one is excellent: universally catenary, a $G$-ring, and $J$-$2$. In
   particular $A$ is universally excellent.
2. _(Finiteness of normalization.)_ Every affine coordinate ring of $S$ is Nagata, and for every
   integral affine chart $\operatorname{Spec}D\subseteq S$ and every finite extension $L$ of
   $\operatorname{Frac}D$, the integral closure of $D$ in $L$ is a finite $D$-module. Hence if $S$
   is reduced its normalization $S^{\mathrm{nor}}\to S$ is a finite morphism, and $S^{\mathrm{nor}}$
   is again of finite type over $A$; if $S$ is proper, respectively projective, over $A$, so is
   $S^{\mathrm{nor}}$.
3. _(Completion is a faithful probe.)_ For every point $s\in S$ the completion map
   $\mathcal O_{S,s}\to\widehat{\mathcal O_{S,s}}$ is faithfully flat and regular. Consequently
   $\widehat{\mathcal O_{S,s}}$ is regular if and only if $\mathcal O_{S,s}$ is, reduced if and only
   if $\mathcal O_{S,s}$ is, and normal if and only if $\mathcal O_{S,s}$ is; and all formal fibers
   of $\mathcal O_{S,s}$ are regular, reduced and normal.
4. _(Openness of singularities.)_ The regular locus of $S$ is open, and so is the regular locus of
   every scheme of finite type over $S$; the singular locus is therefore a closed subscheme, and on
   a normal $S$ of dimension two it is a finite set of closed points.

**Proof.** (1) An affine coordinate ring of $S$ is a finite-type $A$-algebra, hence excellent by
Theorem 10.6; localizations and finite algebras over it are excellent by Theorem 10.5.

(2) Corollary 9.9 gives the Nagata property and the finiteness of integral closures. Finiteness of
the normalization morphism is the affine-local statement glued over a finite affine cover; a finite
morphism is projective and proper, and a composite of proper, respectively projective, morphisms is
again such.

(3) The local ring $\mathcal O_{S,s}$ is a localization of a finite-type $A$-algebra, hence a
$G$-ring by (1); Theorem 4.13 gives all the assertions.

(4) A scheme of finite type over $S$ is of finite type over $A$, so its affine coordinate rings
are $J$-$2$ by (1), and openness of the regular locus is affine-local. For the last statement, on a
normal scheme the singular locus is closed and contains no point of codimension at most one, by
Serre's criterion $R_1$; in dimension two it therefore consists of closed points, and being closed
in a noetherian space of dimension two with no positive-dimensional component, it is finite.
$\square$

Clause (1) is what makes an induction on blowups legitimate: each chart of a blowup of a
finite-type $A$-scheme is again a finite-type $A$-algebra, so the hypotheses under which a
resolution procedure operates are reproduced at every stage rather than assumed anew. Clause (2)
is what makes normalization an operation inside the category of finite-type $S$-schemes. Clause (3)
is the statement used whenever a two-dimensional normal local ring on a model is replaced by its
completion in order to classify a singularity: the completion is again normal, and it is regular
exactly when the original ring was, so nothing is created and nothing is destroyed. Clause (4) is
what turns "the model is singular somewhere" into a closed subscheme that can be blown up.

### 10.4 What is not proved here

This section lists, without softening, the hypotheses carried and the statements not established.

**The finite $p$-degree hypothesis.** Every theorem from Chapter 6 onward assumes that the residue
fields of characteristic $p$ occurring in it satisfy $[\kappa:\kappa^p]<\infty$. It entered twice:
in Proposition 6.4, where the enlarged power series ring
$k^{1/p^e}[[x_1^{1/p^e},\ldots]]$ must be finite over $k[[x_1,\ldots]]$, and in Lemma 6.12, where
$P=T[y]$ must have a finite $p$-basis. It is satisfied by every perfect field, by every field
finitely generated over a perfect field, by $\mathbf Z$ and by every ring essentially of finite type
over these — by Lemma 7.5 — so it covers every base and every chart occurring in the construction
of models over $\mathbf Z$, over a ring of integers, or over a field finitely generated over its
prime field. It is _not_ satisfied by a field of infinite $p$-degree such as
$\mathbf F_p(u_1,u_2,\ldots)$, nor by $k[[t]]$ for such a $k$; those rings are excellent
classically, and the present volume does not prove it.

**Statements deliberately not proved.** Section 5.3 records two: that a formally smooth local
homomorphism is flat, and the converse half of Grothendieck's criterion — that a flat local
homomorphism with geometrically regular closed fiber is formally smooth. Neither is used anywhere.
Only the special case of Corollary 5.17(2), proved from Cohen's separability theorem, is
established in the converse direction, and even it is not used by the final proofs: the route
through Chapter 6 that succeeded is the elementary one, so Chapter 5 stands as an independent
development of the formal-smoothness calculus rather than as a link in the chain. Proposition 3.4
proves the $p$-independence criterion for separability in one direction in general and in the
converse direction only for extensions generated by $p$-th roots, which is all that is needed.

**Standard results used without proof.** Three classical facts from the background list of
Section 1.2 carry more weight than the rest and are named here: that in a Cohen–Macaulay local ring an ideal of height
$h$ contains a regular sequence of length $h$ and that quotients by regular sequences stay
Cohen–Macaulay and equidimensional, used in Proposition 10.2; that every finite field extension
becomes separable after a finite purely inseparable extension of the base field, used in
Lemma 9.3; and Serre's criteria for reducedness and for normality, used in Proposition 4.5 and
Corollary 3.12. The homological characterization of regularity, by contrast, is _not_ assumed: it
is proved in Chapter 2 precisely because the two consequences drawn from it — that localizations of
regular rings are regular, and that regularity descends along faithfully flat maps — carry
Theorem 7.3 and much of Chapters 3 and 4.

**Statements outside the scope.** No resolution of singularities is claimed here, in any dimension;
excellence is a hypothesis for such theorems, not a substitute. The desingularization theorem of
Néron and Popescu, which characterizes regular homomorphisms as filtered colimits of smooth ones,
is neither proved nor used. Nothing is asserted about non-noetherian rings.

### 10.5 Conclusion

The theory has one shape, visible now in retrospect. Regularity is a homological condition
(Theorem 2.9), so it survives localization and descends along faithfully flat maps; that alone
makes it possible to compare a ring with a flat extension of it, provided the fibers are
controlled. Controlling the fibers means controlling them after every field extension, which in
characteristic $p$ is a statement about $p$-bases (Chapter 3). A homomorphism whose fibers are
controlled in this sense — a regular homomorphism — composes, base changes and descends
(Chapter 4), so the entire question of which rings have geometrically regular formal fibers reduces
to a single base case.

That base case is Cohen's structure theory. A complete local ring has coordinates: a coefficient
field or a Cohen ring, and finitely many power series variables. Over such coordinates the formal
fibers can be computed, because the coordinates supply a finite $p$-basis in characteristic $p$ and
a finitely generated residue field extension in characteristic zero, and in both cases a Jacobian
criterion decides regularity (Chapter 6). Everything else is deduction: testing at maximal ideals
and finite-type permanence (Chapter 7), openness of regular loci by spreading out a regular system
of parameters (Chapter 8), finiteness of normalization from reduced completions glued along one
normal open (Chapter 9).

What excellence finally asserts is a single sentence: for these rings, completion is a faithful
local probe, singularities form a closed set, and both properties persist through every finite-type
construction. That is precisely the licence needed to build a model of a curve over a
one-dimensional arithmetic base, to normalize it, to blow it up, and to inspect the result one
completed local ring at a time.
