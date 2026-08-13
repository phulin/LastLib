# Odlyzko Bounds and Fontaine's Argument

## Contents

1. [Discriminant as analytic complexity](#1-discriminant-as-analytic-complexity)
2. [Imported geometric baseline](#2-imported-geometric-baseline)
3. [Imported Dedekind-zeta package](#3-imported-dedekind-zeta-package)
4. [Imported Weil--Poitou explicit formula](#4-imported-weil--poitou-explicit-formula)
5. [Imported positivity and test functions](#5-imported-positivity-and-test-functions)
6. [Imported Odlyzko--Poitou inequalities](#6-imported-odlyzko--poitou-inequalities)
7. [Imported certified finite-degree ledger](#7-imported-certified-finite-degree-ledger)
8. [Imported threshold principle](#8-imported-threshold-principle)
9. [Towers and the meaning of a threshold](#9-towers-and-the-meaning-of-a-threshold)
10. [Finite-flat torsion fields](#10-finite-flat-torsion-fields)
11. [Fontaine's fixed-exponent mechanism](#11-fontaines-fixed-exponent-mechanism)
12. [Small-prime and image-order tables](#12-small-prime-and-image-order-tables)
13. [Signature and base-field refinements](#13-signature-and-base-field-refinements)
14. [Comparative examples and failure diagnostics](#14-comparative-examples-and-failure-diagnostics)
15. [The combined theorem package](#15-the-combined-theorem-package)
16. [Conclusion](#16-conclusion)

## 1. Discriminant as analytic complexity

### 1.1 The collision this book owns

This book owns the collision between two earlier packages; it does not own either package's
internal proof.  Book 7 is the canonical source for the Dedekind functional equation, the
Weil--Poitou explicit formula, unconditional zero positivity, test functions, rational numerical
certificates, and analytic degree cutoffs.  Book 56 is the canonical source for finite-flat upper
breaks, differents, coefficient/model stability, and global root-discriminant ceilings.  Book 158
supplies the general cutout-field and three-adic coefficient ledger.

For a field $L$ cut out by a finite action, arithmetic supplies

$$
\operatorname{rd}(L)<U,
$$

while analysis supplies a lower bound increasing with $[L:\mathbf Q]$.  If the two bounds cross,
the degree is bounded.  If every finite subcompositum of a class has the same ceiling, its total
compositum is finite.  If successive obstructions in a torsion problem return to that fixed
exponent class, the representation-theoretic tower stabilizes.  Those implications, and the
small-prime image exclusions they yield, are the new synthesis here.

### 1.2 Normalizations

For a number field $K$ of degree $n=r_1+2r_2$, put

$$
D_K=|\operatorname{disc}(\mathcal O_K/\mathbf Z)|,
\qquad
\operatorname{rd}(K)=D_K^{1/n},
\qquad
\alpha(K)=\frac{r_1}{n}.
$$

For a tower $L/K/\mathbf Q$,

$$
\operatorname{rd}(L)
=\operatorname{rd}(K)
N_{K/\mathbf Q}(\mathfrak d_{L/K})^{1/[L:\mathbf Q]}.
\tag{1.1}
$$

Thus root discriminants do not decrease in towers, and equality means that the relative extension
is unramified at all finite places.  The real proportion is a separate input: total reality of a
base field does not force total reality of its extensions.

### 1.3 Three logically different conclusions

A numerical comparison may exclude one degree, bound all degrees, or stabilize a nested family.
It does not classify a Galois image.  For example, the degree cap $20$ excludes a faithful image
of order $24$ or $48$, but it does not distinguish a Borel group of order $12$ from a nonsplit
Cartan normalizer of order $16$.  Group structure, determinant, parity, and integral extension
classes remain separate inputs.

### 1.4 Ownership map

The imported analytic Chapters 2--8 replace the former duplicate derivation.  They state every
interface used later and point to the exact source proof.

| Interface used here | Canonical source |
|---|---|
| Minkowski ideal-class and root-discriminant bounds | Book 7, Theorem 2.1 and §§2.3--2.4 |
| Dedekind functional equation and zero count | Book 7, Theorem 4.1 and §4.4 |
| Weil--Poitou identity | Book 7, Theorem 6.1 |
| Unconditional zero positivity | Book 7, Lemma 7.1 and §7.3 |
| Triangular test function and losses | Book 7, §§8.2--8.4 |
| Universal analytic inequality | Book 7, Theorems 9.1 and 15.1 |
| Directed numerical certificates | Book 7, §§10--11 |
| Degree caps and threshold principle | Book 7, Theorems 15.2 and 9.2 |
| Finite-flat upper breaks and differents | Book 56, Theorems 6.1, 7.1, and 14.1 |
| Global finite-flat ceiling and fixed-level composita | Book 56, Theorem 14.2 |

## 2. Imported geometric baseline

### 2.1 Exact compatibility theorem

**Theorem 2.1 (imported Minkowski ideal-class bound; Book 7, Theorem 2.1).** Every ideal class of
$K$ contains an integral ideal $\mathfrak a$ satisfying

$$
N\mathfrak a\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}.
\tag{2.1}
$$

This is the exact former Book 159 statement, now an imported compatibility alias.  Its convex-body
proof, including the complex-place covolume factor, belongs to Book 7, §2.2.

### 2.2 Root form and monotonicity

Applying (2.1) to the principal class gives the imported inequality

$$
\operatorname{rd}(K)\geq
\left(\frac\pi4\right)^{1-\alpha}M_n,
\qquad
M_n=\left(\frac{n^n}{n!}\right)^{2/n}.
\tag{2.2}
$$

Book 7, §2.4 proves $M_{n+1}\geq M_n$ and $M_n\to e^2$.  Hence the worst-signature geometric
limit is $\pi e^2/4$, while the totally real limit is $e^2$.  Geometry alone certifies several
small thresholds, but it cannot cross $5^{5/4}>e^2$; the explicit formula is genuinely needed.

### 2.3 What is and is not imported

No new analytic assertion is proved in this chapter.  We retain (2.1)--(2.2) because the small
prime tables use the exact signature factor and because the independent Minkowski certificate at
$3^{3/2}$ is a useful check on the stronger explicit-formula result.

## 3. Imported Dedekind-zeta package

### 3.1 Euler product and completion

Book 7, Chapter 3 proves absolute convergence and the Euler product for $\zeta_K(s)$ in
$\Re(s)>1$, with

$$
-\frac{\zeta_K'}{\zeta_K}(s)
=\sum_{\mathfrak p}\sum_{m\geq1}
\frac{\log N\mathfrak p}{(N\mathfrak p)^{ms}}.
\tag{3.1}
$$

The coefficients are nonnegative.  Book 7, Chapter 4 uses theta kernels and trace-dual ideal
lattices to prove, rather than assume, the completed functional equation

$$
\Lambda_K(s)=D_K^{s/2}\Gamma_{\mathbf R}(s)^{r_1}
\Gamma_{\mathbf C}(s)^{r_2}\zeta_K(s)
=\Lambda_K(1-s).
\tag{3.2}
$$

The canonical source theorem is Book 7, Theorem 4.1.  Its proof also fixes the exponent of $D_K$,
the gamma normalization, and the poles at $0$ and $1$ used by the explicit formula.

### 3.2 Zeros and contour control

For $\xi_K(s)=\tfrac12s(s-1)\Lambda_K(s)$, Book 7, §4.4 proves order one, the symmetries
$s\leftrightarrow1-s$ and conjugation, location of the nontrivial zeros in the closed critical
strip, and the unit-band zero-count estimate required to remove contour truncations.  The
unconditional argument below does not assume GRH or a boundary zero-free theorem.

## 4. Imported Weil--Poitou explicit formula

### 4.1 Exact identity and compatibility locator

For Book 7's basically admissible even function $F$, put

$$
\Phi_F(s)=\int_{-\infty}^{\infty}F(x)e^{(s-1/2)x}\,dx.
$$

**Theorem 4.1 (imported explicit formula; Book 7, Theorem 6.1).** Let $K$ have degree $n$ and
signature $(r_1,r_2)$.  Then

$$
\begin{aligned}
\log D_K={}&n(\gamma+\log(8\pi))+\frac{\pi r_1}{2}
-4\int_0^\infty F(x)\cosh(x/2)\,dx\\
&-n\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx
-r_1\int_0^\infty\frac{1-F(x)}{2\cosh(x/2)}\,dx\\
&+\sum_\rho\Phi_F(\rho)
+2\sum_{\mathfrak p}\sum_{m\geq1}
\frac{\log N\mathfrak p}{(N\mathfrak p)^{m/2}}
F(m\log N\mathfrak p).
\end{aligned}
\tag{4.1}
$$

The zero sum is symmetric and the prime sum is finite for compactly supported $F$.  This theorem
is an exact import under the former Book 159 locator.  Book 7, §§6.2--6.5 owns the contour proof,
the factor of two in the prime term, the gamma calculation, and the limiting argument for
nonsmooth kernels.

### 4.2 Normalization diagnostics

The zero and prime sums have positive signs; the pole term has a negative sign; a real place adds
$\pi/2$ before its archimedean loss; and the common completed constant is $\log(8\pi)+\gamma$.
Dropping nonnegative terms is valid only after both positivity conditions have been proved.

## 5. Imported positivity and test functions

### 5.1 Unconditional zero positivity

Book 7, Lemma 7.1 proves that, for $|a|<1/2$,

$$
H_a(x)=\frac{\cosh(ax)}{\cosh(x/2)}
$$

has nonnegative Fourier transform, with the endpoints obtained by limits.  Thus if $G$ is even,
nonnegative, compactly supported, and of positive type, then

$$
F(x)=\frac{G(x)}{\cosh(x/2)}
$$

makes paired zero contributions nonnegative throughout the whole critical strip.  This is Book 7,
§7.3; it is unconditional.

### 5.2 The triangular package

For $T>0$, take

$$
G_T(x)=\left(1-\frac{|x|}{T}\right)_+,
\qquad
F_T(x)=\frac{G_T(x)}{\cosh(x/2)}.
\tag{5.1}
$$

$G_T$ is an autocorrelation, so its Fourier transform is nonnegative, while $F_T\geq0$ makes the
prime sum nonnegative.  Define

$$
\begin{aligned}
A(F)&=\int_0^\infty F(x)\cosh(x/2)\,dx,\\
B(F)&=\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx,\\
C(F)&=\int_0^\infty\frac{1-F(x)}{2\cosh(x/2)}\,dx.
\end{aligned}
\tag{5.2}
$$

Book 7, §§8.2--8.4 proves $A(F_T)=T/2$, gives exact finite formulas for
$B_T=B(F_T)$ and $C_T=C(F_T)$, and proves that smooth positive-type approximants converge with
the required singular-kernel domination.  Hence the corners of the triangle conceal no analytic
hypothesis.

### 5.3 Conditional comparison

Under GRH one may instead use $G_T$ itself.  That doubles the general asymptotic threshold, but no
Fontaine conclusion in this book uses it.  Every numerical exclusion below is unconditional.

## 6. Imported Odlyzko--Poitou inequalities

### 6.1 One test function

Dropping the nonnegative zero and prime terms in (4.1), dividing by $n$, and using (5.2) gives the
Book 7 inequality

$$
\log\operatorname{rd}(K)\geq
\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{4A(F)}n-B(F)-\alpha C(F).
\tag{6.1}
$$

For (5.1), Book 7, Theorem 9.1 specializes this to

$$
\boxed{
\operatorname{rd}(K)\geq
\exp\left(\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{2T}{n}-B_T-\alpha C_T\right).}
\tag{6.2}
$$

For fixed $T$, its logarithm is nondecreasing in $n$ and, because $C_T<\pi/2$, in $\alpha$.

### 6.2 Asymptotic constants

Book 7 proves $B_T\to\log2$ and $C_T\to\pi/2-1$.  Choosing $T\to\infty$ slowly relative to the
degree yields

$$
\liminf\operatorname{rd}(K)\geq4\pi e^{\gamma+\alpha_0}
$$

for sequences with degrees tending to infinity and $\liminf\alpha\geq\alpha_0$.  Under GRH the
corresponding constant is $8\pi e^{\gamma+\alpha_0\pi/2}$.  A limiting constant is not a
finite-degree certificate; the next chapter imports the actual directed computations.

## 7. Imported certified finite-degree ledger

### 7.1 Certificate source and method

Book 7, Chapter 10 is the canonical certificate ledger.  It bounds $\log2$, $\log3$, $\log5$,
$\pi$, $\gamma$, exponentials, $B_T$, and $C_T$ by rational finite sums with directed remainders.
The tight interval needed most often is

$$
1.1035544459<B_6<1.1035544460.
$$

No quadrature, network table, or machine transcendental value is an input.  Book 7,
§§10.6a--10.6j records every term count and tail.

### 7.2 Imported cutoff table

Book 7, Theorem 15.2 gives the following unconditional arbitrary-signature caps:

| Strict root-discriminant ceiling | Degree conclusion | Exact certificate |
|---|---:|---|
| $4$ | $[K:\mathbf Q]\leq11$ | Book 7, (11.1) |
| $3^{3/2}$ | $[K:\mathbf Q]\leq20$ | Book 7, (11.8a) |
| $5^{5/4}$ | $[K:\mathbf Q]\leq16$ | Book 7, (11.5) |
| $3^{3/2}2^{2/3}$ | $[K:\mathbf Q]\leq20$ | Book 7, (11.8) |

For totally real fields the first three caps improve respectively to $5$, $12$, and $6$.  The
standalone Minkowski computation at $3^{3/2}$ gives the valid but weaker cap $52$; the degree-$20$
row follows because the explicit-formula certificate works at the larger ceiling
$3^{3/2}2^{2/3}$.

### 7.3 The decisive two-prime crossing

At $T=6$, $n=21$, and $\alpha=0$, Book 7, (11.6)--(11.8) gives

$$
\log\operatorname{rd}(K)>2.126398521002197,
\tag{7.1}
$$

whereas

$$
\log(3^{3/2}2^{2/3})<2.110016553375462.
\tag{7.2}
$$

The positive logarithmic margin exceeds $0.01638$.  Monotonicity therefore excludes every degree
at least $21$.  Thus

$$
\boxed{
\operatorname{rd}(K)<3^{3/2}2^{2/3}
\Longrightarrow [K:\mathbf Q]\leq20.}
\tag{7.3}
$$

Since $3^{3/2}<3^{3/2}2^{2/3}$, the same certificate also gives

$$
\operatorname{rd}(K)<3^{3/2}
\Longrightarrow [K:\mathbf Q]\leq20.
\tag{7.4}
$$

These are the certificates used in the order-$24$ and order-$48$ exclusions below.

### 7.4 The broad dyadic ceiling

The same imported inequality and (7.1), evaluated at $n=34$, gives a lower logarithm greater than
$2.3448859$, while $\log(2\cdot3^{3/2})<2.3410657$.  Hence

$$
\operatorname{rd}(K)<2\cdot3^{3/2}
\quad\Longrightarrow\quad [K:\mathbf Q]\leq33.
$$

This derived row is retained here because Book 160 needs the broad odd-tame ceiling, whereas Book
7's reusable table records the sharper standard thresholds.

## 8. Imported threshold principle

**Theorem 8.1 (imported unconditional threshold principle; Book 7, Theorem 9.2).** Fix
$0\leq\alpha_0\leq1$ and $0<U<4\pi e^{\gamma+\alpha_0}$.  There is an explicit integer
$N(U,\alpha_0)$ such that

$$
\operatorname{rd}(K)\leq U,
\qquad
\alpha(K)\geq\alpha_0
$$

imply $[K:\mathbf Q]<N(U,\alpha_0)$.

This is the former Book 159 locator, now an exact compatibility import.  Book 7 chooses a rational
$T$ so the infinite-degree side of (6.2) exceeds $\log U$ and then chooses $N$ so the pole cost
$2T/N$ fits in the remaining rationally certified gap.  Equality with the asymptotic constant is
insufficient.

## 9. Towers and the meaning of a threshold

### 9.1 Nested fields

**Theorem 9.1 (small-tower obstruction; Book 7, Theorem 13.2).** Suppose

$$
K_0\subseteq K_1\subseteq K_2\subseteq\cdots,
\qquad
\operatorname{rd}(K_j)\leq U,
\qquad
\alpha(K_j)\geq\alpha_0,
$$

and $U<4\pi e^{\gamma+\alpha_0}$.  Then the tower stabilizes.

**Proof.** The imported threshold principle bounds the absolute degrees.  Those degrees are
nondecreasing integers, and an inclusion of equal-degree fields is equality. $\square$

### 9.2 Finite composita

If every finite compositum in a family satisfies one root-discriminant ceiling and one signature
lower bound below the analytic threshold, then their directed compositum is finite.  Indeed, the
finite subcomposita have bounded degrees; one of maximal degree contains every other member.

The uniform ceiling is an arithmetic premise.  Multiplying unrelated discriminant inequalities
usually makes the ceiling grow with the number of fields.  Fixed-exponent product models are what
make the premise true in Fontaine's application.

### 9.3 Growing-tower warning

Bounded step degree is not bounded total degree, and it is not bounded root discriminant.  The
cyclotomic fields $\mathbf Q(\zeta_{\ell^n})$ have uniformly bounded successive degrees but local
different costs growing with $n$.  Applying a finite-flat theorem to the full module killed by
$\ell^n$ produces a ceiling growing like $\ell^{n+1/(\ell-1)}$, not a fixed ceiling.  No analytic
argument below treats that growing bound as uniform.

## 10. Finite-flat torsion fields

### 10.1 Imported local input

The local proofs belong to Book 56.  We retain two compatibility locators because earlier readers
may enter this book through them.

**Lemma 10.1 (imported congruence-to-ramification lemma; Book 56, Lemma 5.1).** If a finite locally
free commutative $\mathcal O_K$-group is killed by $\ell^n$ and every nonzero point has integral
depth at most $c$, then $G_K^u$ fixes all geometric points for $u>e_Kn+c-1$.

**Theorem 10.2 (imported finite-flat upper break; Book 56, Theorem 6.1).** If a finite continuous
$G_K$-module $M$ is killed by $\ell^n$ and admits a finite-flat model over $\mathcal O_K$, then

$$
G_K^u\text{ acts trivially on }M
\quad\text{for}\quad
u>e_K\left(n+\frac1{\ell-1}\right)-1.
\tag{10.1}
$$

Book 56, Theorem 7.1 gives, for the faithful cutout field $E/K$,

$$
\frac{d(E/K)}{e(E/K)}
<e_K\left(n+\frac1{\ell-1}\right).
\tag{10.2}
$$

The theorem needs an actual model over the stated base.  Potential finite flatness after ramified
extension is not a substitute.

### 10.2 Global ceiling

Book 56, Theorem 14.2 globalizes (10.2).  If a global module over $F$ is killed by $\ell^n$,
finite flat at all $v\mid\ell$, unramified away from those places and a finite set $S$, and has
auxiliary upper cutoffs $R_v$, then

$$
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\ell^{n+1/(\ell-1)}
\prod_{v\in S}(Nv)^{(1+R_v)/[F:\mathbf Q]}.
\tag{10.3}
$$

At a tame place with inertia order $e_v$, replace its factor by
$(Nv)^{(1-1/e_v)/[F:\mathbf Q]}$.  Fixed-exponent finite direct sums receive the bound once,
with the maximum exponent, because products of the supplied models cut out the compositum.

### 10.3 Three-adic exponent ledger

The coefficient exponent must be computed before inserting $n$ in (10.3).  For a lattice $T$ over
a three-adic coefficient order and an open ideal $J$, put

$$
m(J)=\min\{m\geq1:3^m\in J\}.
$$

Then $T/JT$ is killed by $3^{m(J)}$.  Book 158, Chapter 13 records the detailed coefficient-ring,
cutout-field, and auxiliary-place bookkeeping.  The cases used here are:

| Module/field | Actual exponent | Coefficient-prime factor | Additional dyadic factor |
|---|---:|---:|---:|
| residual module $T/\mathfrak mT$ | $3$ | $3^{3/2}$ | none if unramified |
| residual module with tame cubic inertia at $2$ | $3$ | $3^{3/2}$ | $2^{2/3}$ |
| quotient $T/JT$ | $3^{m(J)}$ | $3^{m(J)+1/2}$ | supplied local cost |
| finite direct sum at fixed exponent $3$ | $3$ | $3^{3/2}$ once | $2^{2/3}$ once if common inertia is cubic |

Only the residual row has $m(J)=1$ automatically.  A uniformizer of a ramified coefficient order
need not contain $3$ itself, so a “mod uniformizer-power” quotient cannot silently use the
exponent-three constant.

### 10.4 Rank-two residual degree ledger

For a rank-two residual module over $\mathbf F_3$,

$$
[\mathbf Q(M):\mathbf Q]
=|\operatorname{im}\rho_M|
\leq|\operatorname{GL}_2(\mathbf F_3)|=48.
\tag{10.4}
$$

If the determinant is trivial, the ambient group has order $24$.  These matrix bounds are not
ramification bounds; their role is to convert the analytic degree cap into an image exclusion.

## 11. Fontaine's fixed-exponent mechanism

### 11.1 The combined two-prime theorem

**Theorem 11.1 (two-prime forbidden-field theorem).** Let $M$ be a finite
$\mathbf F_3$-representation of $G_{\mathbf Q}$ such that:

- $M$ has an actual finite locally free commutative model over $\mathbf Z_3$;
- $L=\mathbf Q(M)$ is unramified outside $\{2,3\}$;
- inertia at $2$ is trivial or cyclic of order $3$.

Then

$$
[L:\mathbf Q]\leq20.
\tag{11.1}
$$

Consequently the faithful image has order not divisible by $24$.  In dimension two it is neither
$\operatorname{SL}_2(\mathbf F_3)$ nor $\operatorname{GL}_2(\mathbf F_3)$.

**Proof.** Book 56, Theorem 7.1 gives $d_3/e_3<3/2$.  The exact tame cost at $2$ is absent or at
most $2/3$.  Hence

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}.
$$

Book 7, Theorem 15.2, specifically its certificate (11.8), gives the degree cap $20$.  Since the
action is faithful, the degree is the image order; an order divisible by $24$ is at least $24$.
The named groups have orders $24$ and $48$. $\square$

### 11.2 Quotients and finite composita

Upper numbering and root-discriminant ceilings pass to quotient actions and subfields.  Thus a
projective image $\operatorname{PGL}_2(\mathbf F_3)$ of order $24$ is also excluded.  Products of
modeled exponent-three modules remain killed by $3$.  At $2$, the image of one tame generator on
their direct sum is still cyclic of order at most $3$.  Every finite subcompositum therefore has
the same ceiling and degree at most $20$, so their total compositum is finite.

### 11.3 Fixed-exponent Fontaine criterion

Let $\mathscr C$ be a class of global modules killed by $\ell$, closed under finite direct sums,
with actual finite-flat models at all places above $\ell$ and one common auxiliary ramification
ledger.  Suppose every finite compositum has real proportion at least $\alpha_0$, and let $U$ be
the common ceiling obtained from Book 56.  If

$$
U<4\pi e^{\gamma+\alpha_0},
\tag{11.2}
$$

then Book 7 bounds all finite-compositum degrees, so their maximal compositum is finite.  Any
nested sequence inside it stabilizes.

To deduce finite image for a lattice $T$, one needs a further bridge: every first-order
obstruction or congruence layer must be realized by an object of $\mathscr C$ over the fixed base,
and those quotients must separate the image.  This is the fixed-exponent Fontaine mechanism.

### 11.4 Why the full tower is not the criterion

For $T/\ell^mT$, Book 56 gives the safe full-level ceiling with exponent
$\ell^{m+1/(\ell-1)}$, which grows with $m$.  The relative kernel
$\operatorname{Gal}(F_{m+1}/F_m)$ may have bounded order, but it lives over a moving base and is
not automatically the generic fiber of a finite-flat exponent-$\ell$ group over that base.  The
criterion in §11.3 succeeds by returning each obstruction to a fixed exponent-$\ell$ category,
not by asserting a false uniform bound for the full torsion tower.

### 11.5 The remaining group theory

Finite image does not imply reducibility.  Applications may still require classification of
residual constituents, control of extension classes, a Frattini or generation argument,
determinant and parity constraints, and classification of remaining finite subgroups.  None of
these is supplied by the analytic comparison.

## 12. Small-prime and image-order tables

### 12.1 One-prime application table

Combining Book 56, Theorem 14.2 at exponent $\ell$ with Book 7, Theorem 15.2 gives:

| $\ell$ | Strict ceiling over $\mathbf Q$ | Arbitrary-signature cap | Totally real cap |
|---:|---:|---:|---:|
| $2$ | $4$ | $11$ | $5$ |
| $3$ | $3^{3/2}$ | $20$ | $12$ |
| $5$ | $5^{5/4}$ | $16$ | $6$ |

The degree-$20$ entry at $3$ uses the larger two-prime analytic certificate; the independent
geometric cap is $52$.

### 12.2 Rank-two large-image table

| Residual target | Order | Relevant cap | Conclusion under the stated local hypotheses |
|---|---:|---:|---|
| $\operatorname{GL}_2(\mathbf F_2)$ | $6$ | $11$ | not excluded numerically |
| $\operatorname{SL}_2(\mathbf F_3)$ | $24$ | $20$ | excluded |
| $\operatorname{GL}_2(\mathbf F_3)$ | $48$ | $20$ | excluded |
| $\operatorname{GL}_2(\mathbf F_5)$ | $480$ | $16$ | excluded |

For the two three-adic rows, local hypotheses mean finite flatness at $3$, no ramification outside
$\{2,3\}$, and dyadic inertia trivial or of order $3$.  In the one-prime case, dyadic ramification
is absent.  These are exclusions of faithful actions, not declarations that every residual image
is reducible.

### 12.3 Surviving three-adic orders

If separate structure makes the image an extension of a $3$-group by a group of order dividing
$2$, the cap $20$ leaves only

$$
1,2,3,6,9,18.
$$

A Borel subgroup of $\operatorname{GL}_2(\mathbf F_3)$ has order $12$, a nonsplit Cartan has order
$8$, and its normalizer has order $16$; the numerical cap alone does not exclude them.  A
projective $S_4$ image has order $24$ and is excluded, whereas projective $A_4$ has order $12$ and
is not.

### 12.4 Broad odd-tame row

If exponent-three dyadic inertia is only known to be odd and tame, its contribution is less than
$2$, not necessarily at most $2^{2/3}$.  The ceiling is

$$
\operatorname{rd}(L)<2\cdot3^{3/2},
$$

and (7.2) gives $[L:\mathbf Q]\leq33$.  This broad row is weaker but applies before cubic inertia
has been established.

## 13. Signature and base-field refinements

### 13.1 Signature must belong to the cutout field

The real proportion in (6.2) is $r_1(L)/[L:\mathbf Q]$.  A totally real base can acquire complex
places, while a parity condition may force complex conjugation into the kernel and make the
cutout field totally real.  That representation-theoretic assertion must be proved before the
totally real table is used.

### 13.2 Base-field factor

For a finite extension $L/F$, the arithmetic ceiling begins with (1.1).  If normalized local costs
are $b_v$, a typical absolute bound is

$$
U=\operatorname{rd}(F)
\prod_v(Nv)^{b_v/[F:\mathbf Q]}.
\tag{13.1}
$$

Book 7, Theorem 13.1 compares this absolute $U$ with its analytic lower bound.  Once the absolute
degree is capped, division by $[F:\mathbf Q]$ gives the relative cap.  Omitting
$\operatorname{rd}(F)$ changes the premise rather than sharpening the argument.

### 13.3 Quadratic-base check

Book 7, (11.10) certifies

$$
\operatorname{rd}(K)<4\sqrt5
\quad\Longrightarrow\quad [K:\mathbf Q]\leq23.
$$

If $K$ contains a quadratic base, its degree is even, hence at most $22$ and its relative degree is
at most $11$.  This example is a useful audit of both the base-field factor and degree divisibility.

## 14. Comparative examples and failure diagnostics

### 14.1 Tame fields

For a Galois field tamely ramified only at rational primes $q_i$ with inertia orders $e_i$,

$$
\operatorname{rd}(L)=\prod_iq_i^{1-1/e_i}.
$$

This exact cost should replace the coarser upper-break factor.  At $2$, tame cubic inertia costs
$2^{2/3}$ exactly.

### 14.2 Cyclotomic warning

Cyclotomic towers show simultaneously that bounded step degree is not bounded total degree, that a
full-level finite-flat ceiling grows with the annihilating exponent, and that the base field in a
relative step cannot be replaced by the original base.  Any claimed uniform tower bound must name
the additional fixed-exponent structure that defeats this example.

### 14.3 Compositum warning

Separate ceilings for $L_1$ and $L_2$ do not automatically give the same ceiling for $L_1L_2$.
The maximum principle used here comes from a product of actual models at one fixed exponent and a
common auxiliary inertia ledger.  Without that integral product, the generic compositum estimate
adds local costs.

### 14.4 Endpoint and classification warnings

A local group may be nontrivial at the last permitted break; the strict normalized different bound
comes from the $-1/e$ term, not endpoint triviality.  Analytic asymptotic equality gives no finite
cutoff.  Finally, small degree controls group order but not group shape: classification remains a
separate theorem.

## 15. The combined theorem package

### 15.1 Analytic compatibility theorem

**Theorem 15.1 (imported explicit lower-bound theorem; Book 7, Theorem 15.1).** Let $K$ have degree
$n$ and real proportion $\alpha$.  For $T>0$ put

$$
F_T(x)=\frac{(1-|x|/T)_+}{\cosh(x/2)}.
$$

Then, unconditionally,

$$
\operatorname{rd}(K)\geq
\exp\left(\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{2T}{n}-B_T-\alpha C_T\right),
$$

with the exact formulas and tail in Book 7, (8.5)--(8.6).  Under GRH for $\zeta_K$, any basically
admissible $F$ with $F\geq0$ and $\widehat F\geq0$ gives Book 7, (8.2); for the triangle $G_T$ the
pole cost is $16(\cosh(T/2)-1)/(nT)$.

Consequently, for every $U<4\pi e^{\gamma+\alpha_0}$ there is an explicit
$N(U,\alpha_0)$ such that $\operatorname{rd}(K)\leq U$ and $\alpha(K)\geq\alpha_0$ imply
$n<N(U,\alpha_0)$.  Under GRH the corresponding asymptotic threshold is
$8\pi e^{\gamma+\alpha_0\pi/2}$.  This conditional sentence is not used in Theorems 15.2 or
15.3.

This is the exact source statement imported under the established Book 159 locator.  Its proof is
Book 7, Chapters 4, 6, 7, and 8; the two threshold consequences are Book 7, §§9.2--9.5.

### 15.2 Combined finite-flat cutoff

**Theorem 15.2 (finite-flat field bound).** Let $F$ be a number field and $M$ a finite global
module killed by $\ell$.  Assume that $M$ is finite flat at every place above $\ell$, unramified
outside those places and a finite set $S$, and has normalized auxiliary local costs $b_v$ at
$v\in S$.  For $L=F(M)$,

$$
\boxed{
\operatorname{rd}(L)<U,
\qquad
U=\operatorname{rd}(F)\ell^{\ell/(\ell-1)}
\prod_{v\in S}(Nv)^{b_v/[F:\mathbf Q]}.}
\tag{15.1}
$$

Here $b_v=1-1/e_v$ for known tame ramification, while $b_v=1+R_v$ is valid when the last upper
break is at most $R_v$.  If $U<4\pi e^{\gamma+\alpha_0}$ and
$\alpha(L)\geq\alpha_0$, then $[L:\mathbf Q]$ is explicitly bounded.

Over $\mathbf Q$, the one-prime degree rows are those in §12.1.  For $\ell=3$ and dyadic inertia
of order at most $3$,

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}
\quad\Longrightarrow\quad [L:\mathbf Q]\leq20.
\tag{15.2}
$$

**Proof.** The ceiling (15.1) is Book 56, Theorem 14.2 at exponent one, with its exact tame
refinement.  The analytic comparison is Book 7, Theorems 15.1--15.2.  The application rows and
image-order consequences are §§7, 11, and 12 above. $\square$

### 15.3 Uniform-compositum stabilization

**Theorem 15.3 (Fontaine stabilization criterion).** Let $\mathscr C$ be a direct-sum-closed class
of global modules killed by $\ell$, satisfying the hypotheses of Theorem 15.2 with one common
upper constant $U$.  Assume every finite compositum of their cutout fields has real proportion at
least $\alpha_0$.  If

$$
U<4\pi e^{\gamma+\alpha_0},
$$

then the compositum of all fields $F(M)$, $M\in\mathscr C$, is finite over $F$.

Consequently every nested sequence inside that compositum stabilizes.  If a torsion tower
$F(T/\ell^mT)$ is contained in a fixed finite extension of this compositum and its finite
quotients separate the image, then the action on $T$ has finite image.  The same conclusion holds
when successive obstructions are realized in $\mathscr C$ over the fixed base, separate the image,
and a supplied group-theoretic descent places the resulting tower in such a fixed finite extension.

**Proof.** A finite direct sum cuts out the corresponding finite compositum, and Book 56 gives it
the same ceiling.  Book 7 bounds its degree.  A finite subcompositum of maximal degree contains
every member.  The final assertion is the separated inverse-limit argument, under the explicitly
stated fixed-exponent bridge. $\square$

### 15.4 Handoff

The package supplies field size.  A downstream classification must still supply the actual local
models, exact auxiliary inertia, signature information, descent of first-order obstructions to the
fixed exponent category, and the group-theoretic analysis of the remaining small images.

## 16. Conclusion

The ownership boundary is now sharp.  Book 7 proves and certifies the analytic lower bounds.  Book
56 proves the finite-flat upper-break, different, model-stability, and global-ceiling package.
Book 158 carries the general field calculus and detailed coefficient ledger.  This book combines
those inputs: it produces the degree-$20$ two-prime cutoff, excludes faithful images of orders
$24$ and $48$, states the fixed-exponent Fontaine criterion, and records exactly why the same
argument cannot be applied to a growing full torsion tower.
