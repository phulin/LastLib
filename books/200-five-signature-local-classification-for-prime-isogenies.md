# Five-Signature Local Classification for Prime Isogenies

## Contents

1. [Why a rational line has five local weights](#1-why-a-rational-line-has-five-local-weights)
   - [The local question inside a global isogeny](#11-the-local-question-inside-a-global-isogeny)
   - [Local notation and Frobenius convention](#12-local-notation-and-frobenius-convention)
   - [Reduction language and the stable trichotomy](#13-reduction-language-and-the-stable-trichotomy)
   - [The theorem to be proved](#14-the-theorem-to-be-proved)
2. [Places away from the coefficient prime](#2-places-away-from-the-coefficient-prime)
   - [Good reduction](#21-good-reduction)
   - [Split multiplicative reduction and the minimal discriminant](#22-split-multiplicative-reduction-and-the-minimal-discriminant)
   - [Nonsplit multiplicative reduction](#23-nonsplit-multiplicative-reduction)
   - [Additive potentially multiplicative reduction](#24-additive-potentially-multiplicative-reduction)
   - [The potentially multiplicative summary](#25-the-potentially-multiplicative-summary)
3. [Potentially good reduction away from the coefficient prime](#3-potentially-good-reduction-away-from-p)
   - [Stable descent and automorphisms of the good fiber](#31-stable-descent-and-automorphisms-of-the-good-fiber)
   - [Tame residue characteristic](#32-tame-residue-characteristic)
   - [Why the primes three and two are genuinely different](#33-why-the-primes-three-and-two-are-genuinely-different)
   - [Characteristic three: the automorphism calculation](#34-characteristic-three-the-automorphism-calculation)
   - [Characteristic two: the automorphism calculation](#35-characteristic-two-the-automorphism-calculation)
   - [The complete away-from-$p$ ledger](#36-the-complete-away-from-p-ledger)
4. [Order-$p$ group schemes at the coefficient prime](#4-order-p-group-schemes-at-the-coefficient-prime)
   - [Why generic representation theory is insufficient](#41-why-generic-representation-theory-is-insufficient)
   - [Derivation of the order-$p$ normal form](#42-derivation-of-the-order-p-normal-form)
   - [The inertia character of the normal form](#43-the-inertia-character-of-the-normal-form)
   - [Ordinary and supersingular ambient torsion](#44-ordinary-and-supersingular-ambient-torsion)
   - [Why the stable degree is one of $1,2,3,4,6$](#45-why-the-stable-degree-is-one-of-12346)
5. [Descent of the finite-flat exponent](#5-descent-of-the-finite-flat-exponent)
   - [The descent congruence](#51-the-descent-congruence)
   - [From a length to a twelfth-power weight](#52-from-a-length-to-a-twelfth-power-weight)
   - [Derivation of every $(e,r)$ row](#53-derivation-of-every-er-row)
   - [The same rows in minimal-discriminant language](#54-the-same-rows-in-minimal-discriminant-language)
   - [Direct congruence check on the descended character](#55-direct-congruence-check-on-the-descended-character)
   - [Cartier duality and the balanced midpoint](#56-cartier-duality-and-the-balanced-midpoint)
6. [Semistable and potentially multiplicative reduction at $p$](#6-semistable-and-potentially-multiplicative-reduction-at-p)
   - [Good ordinary reduction](#61-good-ordinary-reduction)
   - [Split and nonsplit multiplicative reduction](#62-split-and-nonsplit-multiplicative-reduction)
   - [Additive potentially multiplicative reduction](#63-additive-potentially-multiplicative-reduction)
   - [Completion of the local theorem](#64-completion-of-the-local-theorem)
7. [From the local weight to a global signature](#7-from-the-local-weight-to-a-global-signature)
   - [The everywhere-unramified ratio](#71-the-everywhere-unramified-ratio)
   - [What changes over a number field](#72-what-changes-over-a-number-field)
   - [Duality and the three global branches](#73-duality-and-the-three-global-branches)
   - [Exact small-prime collisions](#74-exact-small-prime-collisions)
   - [The semistable global endpoint](#75-the-semistable-global-endpoint)
8. [Stable specialization and a line-valued Frobenius root](#8-stable-specialization-and-a-line-valued-frobenius-root)
   - [Why potentially good reduction needs descent](#81-why-potentially-good-reduction-needs-descent)
   - [The stable-specialization lemma](#82-the-stable-specialization-lemma)
   - [Exceptional twists made visible](#83-exceptional-twists-made-visible)
9. [The unbalanced resultant sieve](#9-the-unbalanced-resultant-sieve)
   - [The general resultant restriction](#91-the-general-resultant-restriction)
   - [A recurrence deriving every resultant](#92-a-recurrence-deriving-every-resultant)
   - [The three-prime certificate](#93-the-three-prime-certificate)
   - [Why the geometric resultant root is not enough](#94-why-the-geometric-resultant-root-is-not-enough)
10. [The balanced signature and its quadratic character](#10-the-balanced-signature-and-its-quadratic-character)
    - [The local midpoint forces $p\equiv3\pmod4$](#101-the-local-midpoint-forces-pequiv3pmod4)
    - [Construction and conductor of the quadratic character](#102-construction-and-conductor-of-the-quadratic-character)
    - [Why everywhere potential good reduction is the exact next hypothesis](#103-why-everywhere-potential-good-reduction-is-the-exact-next-hypothesis)
    - [Split primes and the balanced trace congruence](#104-split-primes-and-the-balanced-trace-congruence)
    - [No split rational prime below $p/4$](#105-no-split-rational-prime-below-p4)
    - [Minkowski generation and class number one](#106-minkowski-generation-and-class-number-one)
11. [Exact hypotheses, exceptions, and reusable theorem package](#11-exact-hypotheses-exceptions-and-reusable-theorem-package)
    - [One table for every finite place](#111-one-table-for-every-finite-place)
    - [The coefficient-prime row certificate](#112-the-coefficient-prime-row-certificate)
    - [Boundaries that must remain visible](#113-boundaries-that-must-remain-visible)
    - [A necessity theorem ready for global use](#114-a-necessity-theorem-ready-for-global-use)
12. [Conclusion](#12-conclusion)

## 1. Why a rational line has five local weights

### 1.1 The local question inside a global isogeny

Let $p$ be a prime and let $E/\mathbf Q$ be an elliptic curve. A rational cyclic
$p$-isogeny is equivalent to a $G_{\mathbf Q}$-stable line

$$
C\subset E[p](\overline{\mathbf Q}).
$$

Choosing a nonzero point $P\in C$ defines the **isogeny character**

$$
\lambda:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times,
\qquad
\sigma(P)=\lambda(\sigma)P.
\tag{1.1}
$$

The subgroup $C$ is rational even when no generator is rational. Thus
$\lambda$ is generally nontrivial. In a basis beginning with $P$, the residual
representation has the form

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\lambda(\sigma)&*\\
0&\chi_p(\sigma)\lambda(\sigma)^{-1}
\end{pmatrix},
\tag{1.2}
$$

where $\chi_p:G_{\mathbf Q}\to\mathbf F_p^\times$ is the mod-$p$
cyclotomic character. The second diagonal character is the character of the
dual isogeny. Every local calculation must therefore be compatible with the
involution

$$
\lambda\longmapsto\chi_p\lambda^{-1}.
\tag{1.3}
$$

The central problem of this book is to determine the restriction of $\lambda$
to inertia at every finite place. Away from $p$, the answer is controlled by
stable reduction and automorphisms of the stable special fiber. At $p$, the
answer is integral: one must close $C$ inside a finite-flat $p$-torsion model
and measure the resulting order-$p$ group scheme. These two calculations have
different inputs and must not be merged into one informal automorphism
argument.

The reward for keeping them separate is a remarkably small conclusion. For
$p\ge5$, the twelfth power of the local character at $p$ is one of

$$
1,\quad \chi_p^4,\quad \chi_p^6,\quad \chi_p^8,\quad \chi_p^{12},
\tag{1.4}
$$

and its twelfth power is unramified at every other finite prime. Over
$\mathbf Q$, global reciprocity then turns one of these five local possibilities
into a global equality. The purpose here is to prove every entry in this
statement, including the small residue characteristics and the finite-flat
endpoints.

### 1.2 Local notation and Frobenius convention

For a rational prime $q$, write

$$
G_q=\operatorname{Gal}(\overline{\mathbf Q}_q/\mathbf Q_q),
\qquad I_q\subset G_q
$$

for a chosen decomposition group and its inertia subgroup. The wild inertia
subgroup is $P_q$. If $q\ne p$, then $\chi_p|_{I_q}=1$.

An **arithmetic Frobenius** at a prime of good or unramified reduction is a lift
of $x\mapsto x^q$ on the residue algebraic closure. With this convention,

$$
\chi_p(\operatorname{Frob}_q)=q\pmod p.
\tag{1.5}
$$

Local reciprocity is normalized so that a uniformizer maps to arithmetic
Frobenius. On units, this normalization makes the action on Lubin--Tate or
cyclotomic torsion involve the inverse unit. The inverse does not alter any
order or conductor computation below, and formula (1.5) fixes the direction
in every Frobenius identity.

For a one-dimensional finite character $\nu$ of $G_q$, its conductor exponent
is

$$
a_q(\nu)=
\begin{cases}
0,&\nu|_{I_q}=1,\\
1+\operatorname{Swan}_q(\nu),&\nu|_{I_q}\ne1.
\end{cases}
\tag{1.6}
$$

Thus a nontrivial tame character has conductor exponent one. At $q=2,3$ we
will derive the wild bounds from the unit filtration rather than call a wild
character tame.

### 1.3 Reduction language and the stable trichotomy

Let $K$ be a finite extension of $\mathbf Q_q$ and let $v$ be its normalized
valuation. For a minimal integral Weierstrass equation, write

$$
\delta(E/K)=v(\Delta_{\min}),
\qquad
j(E)=c_4^3/\Delta_{\min}.
\tag{1.7}
$$

The three stable outcomes are:

- good reduction, represented by a smooth elliptic special fiber;
- potentially multiplicative reduction, characterized by $v(j)<0$;
- potentially good reduction, characterized by $v(j)\ge0$ once the stable
  reduction theorem is invoked.

Already multiplicative reduction may be split or nonsplit. Additive reduction
is not a fourth stable outcome: after extension it becomes either good or
multiplicative. In particular, a cuspidal plane cubic from a chosen equation
does not decide whether the stable object is smooth or polygonal. Minimality
and $j$ decide the stable branch.

The additive case requires more than the divisibility of a discriminant. We
give the missing Tate-algorithm calculation here because the later inertia
tables use every column of it.

Let $K$ be henselian with algebraically closed residue field of characteristic
$q\ge5$. Passing to the strict henselization does not change normalized
discriminant valuations, geometric components, or ramification indices. Since
$2$ and $3$ are units, a minimal equation can be put in short form

$$
y^2=x^3+Ax+B.
\tag{1.8}
$$

Put $\alpha=v(A)$ and $\beta=v(B)$, allowing the value $+\infty$. Its
discriminant and $j$-invariant are

$$
\Delta=-16(4A^3+27B^2),
\qquad
j=\frac{(-48A)^3}{\Delta}.
\tag{1.8a}
$$

If the reduction is additive, then $\alpha,\beta\ge1$. Minimality says that
we do not have both $\alpha\ge4$ and $\beta\ge6$, because in that case
$x=\pi^2X$, $y=\pi^3Y$ gives another integral equation and lowers the
discriminant valuation by $12$. Conversely, away from $2$ and $3$, the
failure of those two inequalities is the short-equation minimality test.

The valuation comparison in (1.8a) now gives the whole potentially good
branch. If $3\alpha\ne2\beta$, then

$$
v(\Delta)=\min(3\alpha,2\beta).
\tag{1.8b}
$$

Equality can occur in a minimal additive equation only at
$(\alpha,\beta)=(2,3)$. Write then

$$
A=\pi^2A_0,\qquad B=\pi^3B_0.
\tag{1.8c}
$$

If $4A_0^3+27B_0^2$ is a unit, the discriminant valuation is $6$. If it is
not a unit, then $v(\Delta)>6=3v(A)$, so $v(j)<0$ and the curve lies in the
potentially multiplicative branch. Thus cancellation at the only equal-slope
point creates no missing potentially good row.

It follows, successively, that a minimal additive curve with integral
$j$ has exactly one of the following coefficient patterns. The entries in
the third column are the decisive unit conditions; a blank inequality means
that the displayed lower bound is enough.

| type | coefficient pattern in (1.8) | decisive residue datum | $\delta=v(\Delta_{\min})$ |
|---|---|---|---:|
| $\mathrm{II}$ | $\alpha\ge1$, $\beta=1$ | $B/\pi\ne0$ | $2$ |
| $\mathrm{III}$ | $\alpha=1$, $\beta\ge2$ | $A/\pi\ne0$ | $3$ |
| $\mathrm{IV}$ | $\alpha\ge2$, $\beta=2$ | $B/\pi^2\ne0$ | $4$ |
| $\mathrm{I}_0^*$ | $\alpha\ge2$, $\beta\ge3$ | the cubic $T^3+(A/\pi^2)T+B/\pi^3$ is separable | $6$ |
| $\mathrm{IV}^*$ | $\alpha\ge3$, $\beta=4$ | $B/\pi^4\ne0$ | $8$ |
| $\mathrm{III}^*$ | $\alpha=3$, $\beta\ge5$ | $A/\pi^3\ne0$ | $9$ |
| $\mathrm{II}^*$ | $\alpha\ge4$, $\beta=5$ | $B/\pi^5\ne0$ | $10$ |

Here the cubic in the $\mathrm I_0^*$ row has discriminant a unit precisely
when $4A_0^3+27B_0^2$ is a unit. If it has one double root and one simple
root, translate the double root to zero and continue the two-branch
iteration of Tate's algorithm. This gives $\mathrm I_n^*$ with $n>0$ and
$v(j)=-n$, so that branch is potentially multiplicative. If all three roots
coincide, translation puts the triple root at zero; in short form this says
$\alpha\ge3$, $\beta\ge4$, and the next coefficient test gives
$\mathrm{IV}^*$, $\mathrm{III}^*$, or $\mathrm{II}^*$. Thus the repeated-root
test separates the potentially multiplicative double-root branch from the
three starred potentially good rows. This proves exhaustiveness rather than
assuming a list of seven symbols.

We next perform the resolution step which attaches the symbols and component
counts to these coefficient tests. Put

$$
F=y^2-x^3-Ax-B.
$$

The total space is regular at the cusp in the first row: in its completed
local equation the term $-\pi(B/\pi)$ is a nonzero linear term in the
maximal-ideal cotangent space. In every other row its only singular closed
point is the origin. Blow up that point and, whenever the
strict transform is still singular, translate the new point to the origin
before blowing up again. On the chart meeting the old cusp, the substitution

$$
x=\pi X,\qquad y=\pi Y
\tag{1.8d}
$$

gives the strict-transform equation

$$
Y^2=\pi X^3+\frac A\pi X+\frac B{\pi^2}.
\tag{1.8d0}
$$

Thus the coefficient orders become $(\alpha-1,\beta-2)$. On the $x$-chart,
write $y=xY$ and $\pi=xP$. If $A=\pi^\alpha a$ and
$B=\pi^\beta b$, division by $x^2$ gives

$$
Y^2=x+x^{\alpha-1}P^\alpha a+x^{\beta-2}P^\beta b.
\tag{1.8d00}
$$

The $y$-chart has unit constant term on the exceptional divisor and contains
no additional component. Equations (1.8d0)--(1.8d00) make the first four
counts explicit. In type $\mathrm{III}$ the exceptional curve in (1.8d0) is
the smooth line $Y^2=\overline aX+\overline b$ and contributes one component.
In type $\mathrm{IV}$ it splits as the two lines
$Y=\pm\sqrt{\overline b}$, contributing two. In the
$\mathrm I_0^*$ case the first exceptional divisor is a double line. Its
singular points are exactly

$$
Y=0,\qquad
X^3+\overline{A/\pi^2}X+\overline{B/\pi^3}=0.
$$

When the cubic is separable, blowing up its three roots inserts three outer
curves around the central one. Together with the strict transform of the
original fiber this gives five components. A triple root leaves one singular
point; repeating the same three equations at that point gives the starred
rows. The resulting surface singularities and the complete curve counts are
as follows. The displayed leading equation means that terms omitted after
the indicated translations have strictly larger order in every remaining
chart, so they vanish from each exceptional equation.

| coefficient row | leading completed local equation | exceptional curves in the minimal resolution |
|---|---|---:|
| $\mathrm{II}$ | $y^2-x^3-\pi b$ | $0$; the total space is already regular |
| $\mathrm{III}$ | $y^2-x^3-\pi a x$ | $1$, a chain of type $A_1$ |
| $\mathrm{IV}$ | $y^2-x^3-\pi^2 b$ | $2$, a chain of type $A_2$ |
| $\mathrm I_0^*$ | $y^2-x^3-\pi^2a x-\pi^3b$ | $4$, the $D_4$ tree |
| $\mathrm{IV}^*$ | $y^2-x^3-\pi^3a x-\pi^4b$ | $6$, the $E_6$ tree |
| $\mathrm{III}^*$ | $y^2-x^3-\pi^3a x$ | $7$, the $E_7$ tree |
| $\mathrm{II}^*$ | $y^2-x^3-\pi^5b$ | $8$, the $E_8$ tree |

Here $a$ or $b$ is a unit whenever it is the last displayed term. This table
does not invoke the classification of rational double points: it is shorthand
for the blowup calculation just described. In each of the three charts,
cancel the largest common exceptional factor, differentiate the resulting
equation to locate the remaining singular points, and repeat. Numbering the
exceptional curves conveniently, the nonempty adjacency lists are

$$
\begin{array}{c|c}
A_1&\text{one vertex},\\
A_2&1-2,\\
D_4&1-2,\ 1-3,\ 1-4,\\
E_6&1-2-3-4-5,\ 3-6,\\
E_7&1-2-3-4-5-6,\ 3-7,\\
E_8&1-2-3-4-5-6-7,\ 3-8.
\end{array}
\tag{1.8d1}
$$

Substitution shows that every listed curve is a smooth rational exceptional
divisor of multiplicity prescribed by the total transform, while the
Jacobian criterion shows that no singular point remains after the last
listed blowup. In the $\mathrm I_0^*$ row the polynomial locating the three
singular points of the first exceptional double line is

$$
P(X)=X^3+\overline{A_0}X+\overline{B_0}.
\tag{1.8e}
$$

Its three distinct roots give three exceptional branches; the strict
transform of the original cubic is the fourth outer branch, and all four meet
the central exceptional component of multiplicity two. A double root starts
the $\mathrm I_n^*$ iteration described above. Thus the strict transform of
the original fiber, together with the exceptional curves counted in the last
column, gives the following complete resolution ledger. The graph names
abbreviate only the intersection pattern already obtained in the charts.

| coefficient test | terminal fiber | successive geometric configuration | number $m$ of components |
|---|---|---|---:|
| $(\alpha\ge1,\beta=1)$ | $\mathrm{II}$ | one cuspidal rational component | $1$ |
| $(\alpha=1,\beta\ge2)$ | $\mathrm{III}$ | two rational components tangent with intersection multiplicity $2$ | $2$ |
| $(\alpha\ge2,\beta=2)$ | $\mathrm{IV}$ | three rational components through one point | $3$ |
| separable cubic (1.8e) | $\mathrm I_0^*$ | one central component and four disjoint outer components, the affine $D_4$ graph | $5$ |
| $(\alpha\ge3,\beta=4)$ | $\mathrm{IV}^*$ | the affine $E_6$ graph | $7$ |
| $(\alpha=3,\beta\ge5)$ | $\mathrm{III}^*$ | the affine $E_7$ graph | $8$ |
| $(\alpha\ge4,\beta=5)$ | $\mathrm{II}^*$ | the affine $E_8$ graph | $9$ |

For an additional check on the chart count, the exceptional divisor is the
lowest nonzero homogeneous part of $F$ at each center: it is a double line,
or two reduced lines. In the double-line case the derivative normal to the
exceptional divisor is the cubic (1.8e), whose roots locate the next centers.
A chart not containing a remaining singular point is regular and contributes
exactly one rational curve. Iterating the same test gives exactly the
adjacency lists in (1.8d1). Hence the numbers of exceptional curves are

$$
0,1,2,4,6,7,8,
$$

and adding the strict transform gives
$m=1,2,3,5,7,8,9$. The intersection numbers follow directly from the rule
that a blowup lowers the self-intersection of each component through its
center by one and inserts an exceptional curve of self-intersection $-1$.
Contracting only vertical $(-1)$-curves which do not meet the identity gives
the relatively minimal configurations in the ledger. This proves both the
symbol and $m$ for every coefficient row.

It remains to prove, rather than guess from a divisibility condition, the
good-reduction degree. Let $d$ be the ramification index of any extension over
which the curve has good reduction. Base change gives discriminant valuation
$d\delta$, and every integral minimalizing dilation changes it by a multiple
of $12$. Hence

$$
12\mid d\delta.
\tag{1.8f}
$$

This is only the lower bound. To prove the converse, put

$$
e=\frac{12}{\gcd(12,\delta)},\qquad
n=\frac{e\delta}{12}.
\tag{1.8g}
$$

Over the maximal unramified extension, every unit has an $e$th root because
$e$ is prime to $q$. We may therefore choose $\varpi$ with $\varpi^e=\pi$.
In each row make the single weighted change

$$
x=\varpi^{2n}X,\qquad y=\varpi^{3n}Y.
\tag{1.8h}
$$

The coefficient checks are literal:

| type | $(e,n)$ | valuations after dividing $A$ by $\varpi^{4n}$ and $B$ by $\varpi^{6n}$ |
|---|---:|---|
| $\mathrm{II}$ | $(6,1)$ | $6\alpha-4\ge2$, $6\beta-6=0$ |
| $\mathrm{III}$ | $(4,1)$ | $4\alpha-4=0$, $4\beta-6\ge2$ |
| $\mathrm{IV}$ | $(3,1)$ | $3\alpha-4\ge2$, $3\beta-6=0$ |
| $\mathrm I_0^*$ | $(2,1)$ | $2\alpha-4\ge0$, $2\beta-6\ge0$; (1.8e) has unit discriminant |
| $\mathrm{IV}^*$ | $(3,2)$ | $3\alpha-8\ge1$, $3\beta-12=0$ |
| $\mathrm{III}^*$ | $(4,3)$ | $4\alpha-12=0$, $4\beta-18\ge2$ |
| $\mathrm{II}^*$ | $(6,5)$ | $6\alpha-20\ge4$, $6\beta-30=0$ |

Thus (1.8h) is integral and its discriminant is a unit in every row. It
constructs good reduction at the lower-bound degree. Consequently the exact
tame classification is

| Kodaira type | $\delta$ | $m$ | minimal good-reduction ramification $e$ | stable $j$ | stable inertia |
|---|---:|---:|---:|---:|---|
| $\mathrm{II}$ | $2$ | $1$ | $6$ | $0$ | cyclic of order $6$ |
| $\mathrm{III}$ | $3$ | $2$ | $4$ | $1728$ | cyclic of order $4$ |
| $\mathrm{IV}$ | $4$ | $3$ | $3$ | $0$ | cyclic of order $3$ |
| $\mathrm{I}_0^*$ | $6$ | $5$ | $2$ | arbitrary | cyclic of order $2$, generated by $[-1]$ |
| $\mathrm{IV}^*$ | $8$ | $7$ | $3$ | $0$ | cyclic of order $3$ |
| $\mathrm{III}^*$ | $9$ | $8$ | $4$ | $1728$ | cyclic of order $4$ |
| $\mathrm{II}^*$ | $10$ | $9$ | $6$ | $0$ | cyclic of order $6$ |

Indeed tame inertia is procyclic, (1.8f) proves that no proper subgroup gives
good reduction, and (1.8h) proves that the displayed subgroup does. If
$\sigma(\varpi)=\zeta\varpi$, its action on the good equation is

$$
(X,Y)\longmapsto(\zeta^{-2n}X,\zeta^{-3n}Y).
\tag{1.8i}
$$

It multiplies the good invariant differential by $\zeta^n$. In every row
$\gcd(e,n)=1$, so this automorphism has exact order $e$. This connects the
minimal equation, the extension, and the stable inertia action without using
the necessary condition (1.8f) as a converse.

Residue characteristics $2$ and $3$ require a precise qualification. A short
integral equation need not exist, and the seven numerical discriminant values
above are no longer valid without a wild correction. The general
Tate algorithm uses

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6
\tag{1.8j}
$$

and the successive $b_2,b_4,b_6,b_8$ congruences. Its blowups give the same
geometric component counts for a fixed symbol, but an $\mathrm I_n^*$ symbol
with $n>0$ can now lie in the potentially good branch. Put
$w=\operatorname{Swan}(V_\ell E)$ for one, hence every,
$\ell\ne q$. The complete numerical relation is

| symbol | $m$ | $v(\Delta_{\min})$ in residue characteristic $2$ or $3$ |
|---|---:|---:|
| $\mathrm{II},\mathrm{III},\mathrm{IV}$ | $1,2,3$ | $2+w,3+w,4+w$ respectively |
| $\mathrm I_n^*$, $n\ge0$ | $n+5$ | $n+6+w$ |
| $\mathrm{IV}^*,\mathrm{III}^*,\mathrm{II}^*$ | $7,8,9$ | $8+w,9+w,10+w$ respectively |

We prove this wild correction because it prevents a second discriminant
shortcut. Let $\mathcal X$ be the minimal regular model and write its
geometric special fiber as $Z=\sum n_i\Gamma_i$. On a resolution chart of a
node of thickness $r$, the completed equation is

$$
uv=\pi^r,
$$

and the relative dualizing form is $du/u=-dv/v$. Blowing up replaces $r$ by
$r-1$ on one chart and inserts one rational component on the other. The
quotient of the old dualizing lattice by the new one therefore loses one
length at the same time that $m$ increases by one. At the initial additive
cusp, normalization separates two differential directions and contributes
two lengths. Applying this calculation at every center of the general
Weierstrass algorithm gives

$$
\text{differential defect}=v(\Delta_{\min})+1-m.
\tag{1.8j1}
$$

This calculation uses the general equation (1.8j): the successive
$b_2,b_4,b_6,b_8$ tests decide the center, while the completed chart above
computes its contribution. It is unchanged by residue extensions and hence
may be performed over an algebraic closure.

Now take a finite Galois good-reduction extension and let $H_i$ be the lower
ramification groups of its stable inertia action. The same differential
defect can be computed before resolving the quotient. Choose an integral
basis on the good model and filter the trace lattice by the augmentation
ideals of the $H_i$. On the quotient belonging to $H_i/H_{i+1}$, the trace
pairing is nondegenerate on the invariant subspace and has one factor of the
maximal ideal on each complementary direction. Additivity of length therefore
gives

$$
v(\Delta_{\min})+1-m
=\sum_{i\ge0}\frac{|H_i|}{|H_0|}
\operatorname{codim}(V_\ell E)^{H_i}.
\tag{1.8j2}
$$

This is a direct equality of the two computations of the same lattice
cokernel; no equality between discriminant and conductor has been assumed.
Because the reduction is additive and potentially good, $H_0$ has no
invariant vector on $V_\ell E$. Indeed a nonzero invariant line, together
with determinant one, would make every finite-order element have both
eigenvalues one; semisimplicity in characteristic zero would make the entire
inertia action trivial, and the good-reduction criterion would give good
reduction already. Thus the $i=0$ term in (1.8j2) is $2$. The remaining terms
compute

$$
\sum_{i\ge1}\frac{|H_i|}{|H_0|}
\operatorname{codim}(V_\ell E)^{H_i}
=\operatorname{Swan}(V_\ell E).
\tag{1.8k}
$$

Thus

$$
v(\Delta_{\min})+1-m
=2+\operatorname{Swan}(V_\ell E),
\tag{1.8l}
$$

which gives every entry of the wild table. The left side is obtained from
the explicit blowup lengths; the right side is the same different length
grouped by ramification strata. This is the genus-one conductor--discriminant
calculation, not an assumption that discriminant and conductor are equal.

In small residue characteristic neither the symbol nor
$v(\Delta_{\min})$ alone determines the minimal good-reduction extension.
Over the maximal unramified field its Galois group is the finite stable
inertia group $H$. Section 3 will prove

$$
\begin{array}{c|c|c}
q&\text{stable fiber}&H\\ \hline
3&j\ne0&H\subset C_2,\quad |H|\in\{1,2\},\\
3&j=0&H\subset C_3\rtimes C_4,\quad |H|\in\{1,2,3,4,6,12\},\\
2&j\ne0&H\subset C_2,\quad |H|\in\{1,2\},\\
2&j=0&H\subset Q_8\rtimes C_3,\quad |H|\in\{1,2,3,4,6,8,24\}.
\end{array}
\tag{1.8m}
$$

The minimal ramification degree is $|H|$; the wild subgroup is the normal
$q$-Sylow subgroup. This is the exact replacement for
$12/\gcd(12,\delta)$ at $2$ and $3$. Good reduction still has
$(\delta,e)=(0,1)$. Multiplicative type $\mathrm I_n$ has
$\delta=n=-v(j)$; for $q\ge5$, additive potentially multiplicative type
$\mathrm I_n^*$ with $n\ge1$ has $\delta=n+6$ and $v(j)=-n$.
The groups in (1.8m) classify elliptic curves before imposing a rational
prime-isogeny line. Section 3 will prove that such a line forces $H$ to act
faithfully and cyclically; local reciprocity then restricts its order to
$1,2,3,6$ at $q=3$ and to $1,2,4$ at $q=2$.

### 1.4 The theorem to be proved

Here is the complete output, stated before its mechanisms are developed.

**Theorem 1.1 (five-signature local theorem over $\mathbf Q$).** Let $p\ge5$,
let $E/\mathbf Q$ be an elliptic curve with a $G_{\mathbf Q}$-stable line
$C\subset E[p]$, and let $\lambda$ be its isogeny character.

1. At every $q\ne p$,

   $$
   \lambda^{12}|_{I_q}=1.
   \tag{1.9}
   $$

   More precisely, the character and conductor are given by the derived local
   ledger in Chapters 2--3.

2. At $p$ there is an integer

   $$
   s\in\{0,4,6,8,12\}
   \tag{1.10}
   $$

   such that

   $$
   \lambda^{12}|_{I_p}=\chi_p^s|_{I_p}.
   \tag{1.11}
   $$

3. If $E$ is semistable at $p$, then

   $$
   \lambda|_{I_p}=1
   \quad\text{or}\quad
   \lambda|_{I_p}=\chi_p|_{I_p}.
   \tag{1.12}
   $$

   If $E$ is merely potentially multiplicative at $p$, only $s=0,12$
   occur.

4. A mechanism with $s=4$ or $8$ can occur only when

   $$
   p\equiv2\pmod3,
   \tag{1.13}
   $$

   and a mechanism with $s=6$ can occur only when

   $$
   p\equiv3\pmod4.
   \tag{1.14}
   $$

5. Cartier duality sends $s$ to $12-s$. Thus $0,12$ are the endpoint pair,
   $4,8$ are the cubic pair, and $6$ is self-dual or **balanced**.

The word “mechanism” in parts 4 and 5 matters for $p=5,7,13$, where distinct
integers in (1.10) may define the same power of $\chi_p$. The exact collision
ledger will be given after the finite-flat proof. For every $p\ge17$, the five
integers are distinct modulo $p-1$.

## 2. Places away from the coefficient prime

### 2.1 Good reduction

Fix $q\ne p$. If $E/\mathbf Q_q$ has good reduction, the group scheme
$\mathcal E[p]$ on the elliptic model is finite étale because $p$ is invertible
in $\mathbf Z_q$. Finite étale groups over a henselian DVR correspond to
unramified Galois modules. Therefore

$$
E[p]^{I_q}=E[p],
\qquad
\lambda|_{I_q}=1,
\qquad
a_q(\lambda)=0.
\tag{2.1}
$$

This statement does not distinguish ordinary and supersingular reduction of
the characteristic-$q$ special fiber. That distinction concerns $q$-power
torsion; the present torsion has order prime to $q$.

### 2.2 Split multiplicative reduction and the minimal discriminant

Suppose first that $E$ has split multiplicative reduction. Tate
uniformization gives a unique parameter $t\in\mathbf Q_q^\times$ with
$v_q(t)>0$ and

$$
E(\overline{\mathbf Q}_q)\simeq
\overline{\mathbf Q}_q^\times/t^{\mathbf Z}.
\tag{2.2}
$$

The parameter records the intrinsic thickness:

$$
v_q(t)=v_q(\Delta_{\min})=-v_q(j(E)).
\tag{2.3}
$$

Choosing a primitive $p$th root of unity and a $p$th root of $t$ gives

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0
\tag{2.4}
$$

and a matrix

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\chi_p(\sigma)&c_t(\sigma)\\
0&1
\end{pmatrix}.
\tag{2.5}
$$

On $I_q$, the cyclotomic character is trivial. The Kummer cocycle is the
reduction of

$$
v_q(t)\,t_p:I_q\longrightarrow\mathbf F_p,
\tag{2.6}
$$

where $t_p$ is the tame $p$-character. Thus inertia is unipotent. If the
unipotent class is nonzero, its unique stable line is fixed pointwise. If it
vanishes, inertia is trivial on every line. In both cases every
$G_q$-stable line has trivial inertia character:

$$
\lambda|_{I_q}=1,
\qquad a_q(\lambda)=0.
\tag{2.7}
$$

This is stronger than the statement that the semisimplification is
unramified. The full two-dimensional residual representation is ramified
exactly when

$$
p\nmid v_q(\Delta_{\min}),
\tag{2.8}
$$

but its stable-line character is unramified in either case.

### 2.3 Nonsplit multiplicative reduction

For nonsplit multiplicative reduction, the two tangent branches at the node
are exchanged by the nontrivial unramified quadratic character $\eta_q$.
After the unramified quadratic extension the curve is a Tate curve, and

$$
\overline\rho_{E,p}\simeq
\eta_q\otimes
\begin{pmatrix}
\chi_p&c_t\\
0&1
\end{pmatrix}.
\tag{2.9}
$$

Because $\eta_q|_{I_q}=1$, the inertial calculation is identical to the split
case:

$$
\lambda|_{I_q}=1,
\qquad a_q(\lambda)=0.
\tag{2.10}
$$

Splitness is visible on arithmetic Frobenius, not on inertia. If $F_q$ is
arithmetic Frobenius, the two semisimple eigenvalues are

$$
\eta_q(F_q)q,
\qquad
\eta_q(F_q),
\tag{2.11}
$$

with sign $+1$ in the split case and $-1$ in the nonsplit case.

### 2.4 Additive potentially multiplicative reduction

Now suppose $v_q(j(E))<0$ but $E$ is not already multiplicative. There is a
unique quadratic character $\eta_q$ for which

$$
E\otimes\eta_q\simeq E_t
\tag{2.12}
$$

is a Tate curve. Here $\eta_q$ is ramified; otherwise reduction would already
be multiplicative. Twisting (2.5) shows that both diagonal characters acquire
the same factor $\eta_q$. Any stable line therefore satisfies

$$
\lambda|_{I_q}=\eta_q|_{I_q}.
\tag{2.13}
$$

Consequently

$$
\lambda^2|_{I_q}=1,
\qquad
\lambda^{12}|_{I_q}=1.
\tag{2.14}
$$

The conductor follows directly from local units. If $q$ is odd, wild inertia
is pro-$q$ and has no quotient of order two. A ramified quadratic character is
therefore tame and

$$
a_q(\lambda)=1
\qquad(q\text{ odd}).
\tag{2.15}
$$

At $q=2$, use

$$
\mathbf Z_2^\times\simeq\{\pm1\}\times(1+4\mathbf Z_2),
\qquad
\log:(1+4\mathbf Z_2)\xrightarrow{\sim}4\mathbf Z_2.
\tag{2.16}
$$

A homomorphism from $4\mathbf Z_2$ to a group of exponent two kills
$8\mathbf Z_2$. Under the logarithm this is $1+8\mathbf Z_2$. Local
reciprocity identifies units with abelian inertia, so every quadratic
character of $G_2$ is trivial on the third unit group. A ramified character
cannot have conductor one because $\mathbf F_2^\times$ is trivial. Hence

$$
a_2(\lambda)=a_2(\eta_2)\in\{2,3\}.
\tag{2.17}
$$

Both values occur among ramified quadratic characters of $\mathbf Q_2$.

### 2.5 The potentially multiplicative summary

The stable multiplicative cases can now be read without suppressing the twist:

| reduction over $\mathbf Q_q$ | splitting character | $\lambda\mid_{I_q}$ | $a_q(\lambda)$ | $\lambda^{12}\mid_{I_q}$ |
|---|---|---|---:|---|
| split multiplicative | trivial | $1$ | $0$ | $1$ |
| nonsplit multiplicative | unramified quadratic | $1$ | $0$ | $1$ |
| additive potentially multiplicative, $q$ odd | ramified quadratic | $\eta_q$ | $1$ | $1$ |
| additive potentially multiplicative, $q=2$ | ramified quadratic | $\eta_2$ | $2$ or $3$ | $1$ |

The minimal discriminant controls the unipotent extension in the first two
rows through (2.8), but it does not change the character on the stable line.
In the additive rows the quadratic twist, not the unipotent class, supplies
the inertial character.

## 3. Potentially good reduction away from $p$

### 3.1 Stable descent and automorphisms of the good fiber

Continue to assume $q\ne p$ and suppose $E$ is potentially good. Pass first
to the maximal unramified extension of $\mathbf Q_q$ and then to a finite
Galois totally ramified extension $L$ over which $E$ has good reduction. Take
$L$ minimal with this property and let
$\widetilde E/\overline{\mathbf F}_q$ be the good special fiber. Uniqueness of
the smooth proper model makes the finite inertia quotient act by pointed
automorphisms:

$$
H_q=I_q/I_L\hookrightarrow\operatorname{Aut}
(\widetilde E,0).
\tag{3.1}
$$

Both minimality and injectivity deserve proof. Fix a prime $\ell\ne q$.
Prime-to-$q$ specialization identifies $T_\ell E$ over $L$ with
$T_\ell\widetilde E$. If a subgroup of $H_q$ acts trivially on the latter,
then inertia over its fixed field acts trivially on $T_\ell E$. The
good-reduction criterion gives good reduction over that fixed field,
contradicting the minimality of $L$ unless the subgroup is trivial. Thus the
kernel in (3.1) is genuinely zero. Equivalently, $L$ is the field cut out by
the finite inertial action on one prime-to-$q$ Tate module, and

$$
e(L/\mathbf Q_q^{\mathrm{nr}})=|H_q|.
\tag{3.1a}
$$

We will repeatedly use the following intrinsic action calculation. For every
elliptic curve $D$ over an algebraically closed field of characteristic $q$
and every $\ell\ne q$, the homomorphism

$$
\operatorname{Aut}(D,0)\longrightarrow
\operatorname{GL}(T_\ell D)
\tag{3.1b}
$$

is faithful. Indeed, if $u$ acts trivially, then $u-1$ kills
$D[\ell^n]$ for every $n$. Unless $u=1$, the nonzero endomorphism $u-1$ is
an isogeny and has finite kernel, which cannot contain groups of orders
$\ell^{2n}$ for all $n$. Moreover the determinant of $u$ on $T_\ell D$ is
$\deg u=1$: this follows either from the degree formula for isogenies or from
preservation of the Weil pairing. Hence

$$
\operatorname{Aut}(D,0)\hookrightarrow
\operatorname{SL}_2(\mathbf Z_\ell).
\tag{3.1c}
$$

An element of order $2,3,4$, or $6$ consequently has characteristic
polynomial, respectively,

$$
(T+1)^2,\qquad T^2+T+1,\qquad T^2+1,\qquad T^2-T+1.
\tag{3.1d}
$$

The order-two element is $[-1]$, including in characteristics $2$ and $3$;
on prime-to-$q$ torsion it acts as the scalar $-1$.

The line $C$ is stable under $G_q$, so $H_q$ acts on it through a homomorphism

$$
H_q\longrightarrow\mathbf F_p^\times.
\tag{3.1e}
$$

Its image is cyclic even when $H_q$ is not. Thus a bound on element orders in
the complete automorphism group gives an exponent bound on the line, while
local reciprocity will impose the sharper conductor bound.

In the present isogeny setting one can say more about $H_q$ itself. The
orders of all geometric pointed automorphism groups below divide $24$, while
$p\ge5$ and $q\ne p$. The reduction map

$$
\operatorname{Aut}(D,0)\longrightarrow\operatorname{GL}(D[p])
\tag{3.1f}
$$

is faithful on these groups: its kernel inside
$\operatorname{GL}_2(\mathbf Z_p)$ is pro-$p$ and therefore has no
nontrivial element of order dividing $24$. Since $p\nmid |H_q|$, Maschke's
averaging argument supplies an $H_q$-stable complement to $C$. In a basis of
the two stable lines every element is diagonal, so the faithful image, and
hence $H_q$, is abelian. Thus nonabelian subgroups in the complete geometric
classification can occur as stable inertia for elliptic curves in general,
but not when the prime-to-$q$ torsion representation has the rational
$p$-isogeny line considered here. In fact the character on that line is
faithful. On the stable complement the character is
$\lambda^{-1}$ because the determinant is one. An element in the kernel of
$\lambda$ therefore acts trivially on both lines and hence on $D[p]$; the
faithfulness of (3.1f) makes it the identity. Consequently

$$
H_q\xrightarrow{\ \lambda\ }\mathbf F_p^\times
\quad\text{is injective},
\qquad
|\lambda(I_q)|=|H_q|.
\tag{3.1g}
$$

Thus the stable inertia group attached to a rational prime-isogeny line is
itself cyclic. The larger groups below remain essential to prove the
universal geometric classification and to see why no unexamined fiber can
escape the bound.

### 3.2 Tame residue characteristic

Assume $q\ge5$. Every elliptic curve over an algebraically closed field of
characteristic different from $2$ and $3$ has a short equation

$$
y^2=x^3+Ax+B.
$$

A pointed automorphism preserves the pole spaces of $x$ and $y$, so it starts
as a general Weierstrass change. Comparing the $x^2$, $xy$, and $y$ terms in
the same short equation forces its translation parameters to vanish. It is
therefore $(x,y)\mapsto(u^2x,u^3y)$. Comparing the remaining coefficients
gives

$$
u^2=1\quad(AB\ne0),
\qquad
u^4=1\quad(B=0),
\qquad
u^6=1\quad(A=0).
\tag{3.2}
$$

Conversely every displayed root of unity gives an automorphism. Thus this is
the complete classification:

$$
\operatorname{Aut}(\widetilde E,0)\simeq
\begin{cases}
C_2,&j\ne0,1728,\\
C_4,&j=1728,\\
C_6,&j=0.
\end{cases}
\tag{3.2a}
$$

Wild inertia is pro-$q$ and these group orders are prime to $q$, so it acts
trivially. The exact Tate-algorithm proof in Section 1.3 identifies the order
$e=|H_q|$ from the original Kodaira symbol:

| original type | $\mathrm{II},\mathrm{II}^*$ | $\mathrm{III},\mathrm{III}^*$ | $\mathrm{IV},\mathrm{IV}^*$ | $\mathrm I_0^*$ |
|---|---:|---:|---:|---:|
| $\delta$ | $2,10$ | $3,9$ | $4,8$ | $6$ |
| exact $\lvert H_q\rvert$ | $6$ | $4$ | $3$ | $2$ |
| stable automorphism | order $6$ | order $4$ | order $3$ | $[-1]$ |
| exact order of $\lambda(I_q)$ | $6$ | $4$ | $3$ | $2$ |

Equivalently, for a tame fundamental character $\vartheta_q$,

$$
\lambda|_{I_q}=\vartheta_q^b,
\qquad
\operatorname{ord}(\vartheta_q^b)=e,
\qquad e\mid p-1.
\tag{3.3}
$$

Therefore

$$
\lambda^{12}|_{I_q}=1.
\tag{3.4}
$$

Every additive row has $e>1$, so the character is nontrivial, tame, and has
conductor exponent one. The divisibility $e\mid p-1$ is a necessary local
condition for the original rational kernel line to exist; if it fails, the
two-dimensional stable inertia representation is irreducible over
$\mathbf F_p$. No eigenline is being manufactured by the table: the original
rational kernel supplies it, and (3.1g) then forces the displayed exact
order.

### 3.3 Why the primes three and two are genuinely different

At $q=3$ or $2$, wild inertia can act nontrivially on the good special fiber.
It would be incorrect to reuse the tame list (3.2), and it would also be
incorrect to assign conductor exponent one merely because the final character
has finite order. We need a classification of **every** geometric elliptic
fiber, not only a calculation on the exceptional supersingular one.

The normal forms below are exhaustive. They are obtained from the general
Weierstrass equation by transformations preserving the origin. In
characteristic $3$, completing the square is allowed but depressing the cubic
is not; in characteristic $2$, the $xy$ term distinguishes the ordinary
case. We will solve all pointed coordinate changes on each normal form, then
combine that classification with the faithful Tate-module action (3.1b) and
the unit filtration of $\mathbf Q_q$. This separates three questions which
must not be conflated:

1. the full, possibly nonabelian stable inertia group $H_q$;
2. its cyclic image on the given $\mathbf F_p$-line;
3. the depth of that character in abelian local inertia.

### 3.4 Characteristic three: the automorphism calculation

Let $k$ be algebraically closed of characteristic three. Completing the square
puts every elliptic curve in the form

$$
y^2=x^3+a_2x^2+a_4x+a_6.
$$

Here $c_4=a_2^2$, so $j\ne0$ exactly when $a_2\ne0$. In that case a
translation of $x$ removes the linear term: the cubic term has no cross term
in characteristic three, while the coefficient of $x$ in
$a_2(x+r)^2+a_4(x+r)$ is $2a_2r+a_4$. A scaling then normalizes $a_2$ to
one and gives

$$
E_c:y^2=x^3+x^2+c,
\qquad c\ne0.
\tag{3.4a}
$$

A general pointed change between such equations is

$$
x\longmapsto u^2x+r,
\qquad
y\longmapsto u^3y+s x+t.
\tag{3.4b}
$$

The $xy$ and $y$ coefficients force $s=t=0$; the $x^2$ coefficient then
forces $u^2=1$, and the $x$ coefficient forces $r=0$. Hence

$$
j\ne0\quad\Longrightarrow\quad
\operatorname{Aut}(E_c,0)=\{1,[-1]\}\simeq C_2.
\tag{3.4c}
$$

This proves the nonexceptional case rather than placing it in an unexplained
subgroup.

If $j=0$, then $a_2=0$, and nonsingularity forces $a_4\ne0$ because the
derivative of $x^3+a_4x+a_6$ is $a_4$. Scale $a_4$ to $-1$ and translate a
root of $r^3-r+a_6$ to remove the constant term. This polynomial has a root
because $k$ is algebraically closed. Thus the unique normal form is the
supersingular curve

$$
\widetilde E:y^2=x^3-x.
\tag{3.5}
$$

For each $r\in\mathbf F_3$, translation $x\mapsto x+r$ preserves the right
side because $r^3=r$. These translations form $C_3$. If $i^2=-1$, the map

$$
(x,y)\longmapsto(-x,iy)
\tag{3.6}
$$

has order four and conjugates a translation to its inverse. A general pointed
Weierstrass change has the form

$$
x\longmapsto u^2x+r,
\qquad
y\longmapsto u^3y+s x+t.
\tag{3.6a}
$$

Substitution in (3.5) makes the $xy$- and $y$-coefficients force $s=t=0$;
the $x$-coefficient then gives $u^4=1$, and the constant coefficient gives
$r^3=r$. Thus the $x$-translation has exactly three choices and the
differential multiplier has exactly four. Hence

$$
\operatorname{Aut}(\widetilde E,0)\simeq C_3\rtimes C_4,
\qquad |\operatorname{Aut}(\widetilde E,0)|=12,
\tag{3.7}
$$

where a generator of $C_4$ acts on $C_3$ by inversion. Nonexceptional fibers
were classified separately in (3.4c), so (3.7) completes all geometric
fibers. Its element orders are $1,2,3,4,6$; the central element of order two
is $[-1]$, and multiplying it by a translation gives the elements of order
six. By (3.1b)--(3.1d), these orders and their cyclotomic quadratic
characteristic polynomials are realized faithfully on every prime-to-three
Tate module.

The subgroup list is also explicit. Intersect a subgroup with the normal
$C_3$ and project it to $C_4$. If the intersection is trivial, the subgroup
is conjugate into $C_4$. If it contains $C_3$, its image in $C_4$ has order
$1$, $2$, or $4$. Thus, up to isomorphism,

$$
H_3\in\{1,C_2,C_3,C_4,C_6,C_3\rtimes C_4\},
\qquad
|H_3|\in\{1,2,3,4,6,12\}.
\tag{3.7a}
$$

Thus only these minimal good-reduction degrees can occur for an exceptional
characteristic-three stable fiber. The Kodaira symbol alone does not select
one of them; the wild correction and ramification filtration in (1.8k) do.
If the rational $p$-isogeny line is present, (3.1g) excludes the final
nonabelian entry and identifies the order of $H_3$ with the order of the line
character. Local reciprocity below will also exclude $C_4$.

For every subgroup of (3.7), a cyclic quotient has $3$-primary part of order
at most $3$ and prime-to-$3$ part of exponent at most $4$.
Therefore the automorphism calculation alone gives

$$
\operatorname{ord}(\lambda(I_3))\mid12.
\tag{3.8}
$$

Local reciprocity sharpens this. The unit group is

$$
\mathbf Z_3^\times\simeq\mu_2\times(1+3\mathbf Z_3),
\qquad
\log:(1+3\mathbf Z_3)\xrightarrow{\sim}3\mathbf Z_3.
\tag{3.9}
$$

The tame part of an abelian inertia character therefore has order at most
two, not four. The wild part has order at most three by (3.7). A homomorphism
from $3\mathbf Z_3$ to a group of exponent three kills $9\mathbf Z_3$.
Consequently

$$
\operatorname{ord}(\lambda(I_3))\mid6,
\qquad
a_3(\lambda)\le2,
\qquad
\lambda^6|_{I_3}=1.
\tag{3.10}
$$

Together with (3.1g), this says that in the rational-isogeny setting

$$
H_3\in\{1,C_2,C_3,C_6\},
\qquad
|H_3|=\operatorname{ord}(\lambda(I_3)).
$$

The exact conductor possibilities are now visible. A trivial inertial character has
conductor $0$; a nontrivial character supported on $\mu_2$ has conductor $1$;
and a character with nontrivial order-three wild part has conductor $2$,
whether or not it also has a quadratic tame part. This derives both the wild
exponent and every conductor possibility from (3.7) and (3.9).

There is a useful refinement which will be retained in the final ledger:

$$
\begin{array}{c|c|c|c}
\text{stable }j& H_3&\operatorname{ord}\lambda(I_3)&a_3(\lambda)\\ \hline
j\ne0&H_3\in\{1,C_2\}&|H_3|\text{ divides }2&0\text{ or }1,\\
j=0&H_3\in\{1,C_2,C_3,C_6\}&|H_3|\text{ divides }6&0,1,\text{ or }2.
\end{array}
\tag{3.10a}
$$

### 3.5 Characteristic two: the automorphism calculation

Let $k$ be algebraically closed of characteristic two. If $j\ne0$, the curve
is ordinary. In the general Weierstrass equation, $c_4=a_1^4$, so this is
equivalent to $a_1\ne0$. Scale to $a_1=1$. Translation of $x$ kills $a_3$;
then $y\mapsto y+s x+t$ changes the $x^2$ coefficient by $s^2+s$ and changes
the remaining linear coefficient affinely in $t$. Since
$s\mapsto s^2+s$ is surjective on $k$, these two coefficients can be killed
successively. The resulting exhaustive ordinary normal form is

$$
E_c:y^2+xy=x^3+c,
\qquad c\ne0.
\tag{3.10b}
$$

Coefficient comparison in a general pointed Weierstrass change first forces
$u=1$ and $r=t=0$. The only remaining transformations are

$$
(x,y)\longmapsto(x,y+s x),
\qquad s^2+s=0.
\tag{3.10c}
$$

Thus $s=0,1$, and the nontrivial map is precisely
$[-1]:(x,y)\mapsto(x,y+x)$. Therefore

$$
j\ne0\quad\Longrightarrow\quad
\operatorname{Aut}(E_c,0)\simeq C_2.
\tag{3.10d}
$$

If $j=0$, then $a_1=0$. Nonsingularity forces $a_3\ne0$, so scale to
$a_3=1$. The same general coordinate change first kills $a_2$ and $a_4$:
after eliminating $a_2$ the remaining equation for the translation parameter
has the form $s^4+s=d$, which has a root in $k$. The final constant changes
by $t^2+t$, again a surjective polynomial on the algebraically closed field.
Thus the supersingular curve has the unique normal form

$$
\widetilde E:y^2+y=x^3.
\tag{3.11}
$$

The order of its automorphism group can be calculated without quoting a list.
Seek maps

$$
x\longmapsto x+r,
\qquad
y\longmapsto y+s x+t.
\tag{3.12}
$$

Substitution in (3.11) gives

$$
s^2=r,
\qquad s=r^2,
\qquad t^2+t=r^3.
\tag{3.13}
$$

Thus $r=0$ or $r^3=1$. For $r=0$ there are two choices of $t$; for each of
the three cube roots of unity there are two choices. These eight maps form a
quaternion group $Q_8$: the central involution is $y\mapsto y+1$, and each
noncentral generator has order four. In addition,

$$
(x,y)\longmapsto(\zeta x,y),
\qquad \zeta^3=1,
\tag{3.14}
$$

permutes the three pairs of order-four elements. To see that these maps are
exhaustive, write a general pointed change as

$$
x\longmapsto u^2x+r,
\qquad
y\longmapsto u^3y+s x+t.
\tag{3.14a}
$$

After using $y^2=x^3+y$, coefficient comparison gives

$$
u^3=1,\qquad
s^2=u^4r,\qquad
s=u^2r^2,\qquad
t^2+t=r^3.
\tag{3.14b}
$$

The middle two equations give $r^4=r$, so $r=0$ or $r^3=1$. For each of the
three choices of $u$, there are four choices of $r$ and two choices of $t$;
$s$ is then forced. Equivalently, composing with one of the three scalings
(3.14) reduces to $u=1$, after which (3.14b) is exactly (3.13), with its eight
solutions. Hence there are $3\cdot8=24$ maps and no others. Therefore

$$
\operatorname{Aut}(\widetilde E,0)\simeq Q_8\rtimes C_3
\simeq\operatorname{SL}_2(\mathbf F_3),
\qquad |\operatorname{Aut}(\widetilde E,0)|=24.
\tag{3.15}
$$

The subgroup with $u=1$ has one central involution and six elements of order
four, hence is $Q_8$; the scalings cyclically permute its three pairs of
noncentral cyclic subgroups. This proves the asserted semidirect product.
Together with (3.10d), it is the complete geometric classification in
characteristic two. Its element orders are $1,2,3,4,6$, so its exponent is
$12$. The faithful action (3.1b) puts the corresponding characteristic
polynomials (3.1d) on every prime-to-two Tate module.

Every subgroup either lies in the normal $Q_8$ or has image $C_3$ in the
quotient. Since $Q_8$ has only the subgroup types $1,C_2,C_4,Q_8$, its
intersection with such a subgroup must be invariant under the induced
$C_3$-action. That action cyclically permutes the three subgroups of order
four, so the intersection cannot be a single $C_4$. The remaining
intersections $1,C_2,Q_8$ give respectively $C_3,C_6$, and the full
semidirect product. Hence, up to isomorphism,

$$
H_2\in\{1,C_2,C_3,C_4,C_6,Q_8,Q_8\rtimes C_3\},
\qquad
|H_2|\in\{1,2,3,4,6,8,24\}.
\tag{3.15a}
$$

Thus only these minimal good-reduction degrees can occur for the exceptional
characteristic-two fiber. As in characteristic three, the symbol and
discriminant valuation do not determine which subgroup occurs.
With the rational $p$-isogeny line, (3.1g) excludes $Q_8$ and the full
semidirect product and identifies the line order with $|H_2|$. Local
reciprocity below also excludes the two cyclic groups with a factor of three.

Every cyclic quotient of a subgroup has $2$-primary exponent at most four and
odd part of order at most three. The automorphism group alone therefore gives
exponent dividing twelve on a stable line. More structurally, the wild image
is contained in the normal $Q_8$, and the tame quotient is contained in
$C_3$.

Again local reciprocity is sharper. Since $\mathbf F_2^\times$ is trivial,
abelian inertia over $\mathbf Q_2$ has no odd-order tame quotient. From
(2.16), a character of exponent at most four on $1+4\mathbf Z_2$ kills the
subgroup whose logarithm is $16\mathbf Z_2$, namely $1+16\mathbf Z_2$.
Therefore

$$
\operatorname{ord}(\lambda(I_2))\mid4,
\qquad
a_2(\lambda)\le4,
\qquad
\lambda^4|_{I_2}=1.
\tag{3.16}
$$

Combining this with (3.1g) gives the exact stable-inertia restriction

$$
H_2\in\{1,C_2,C_4\},
\qquad
|H_2|=\operatorname{ord}(\lambda(I_2))
$$

for a rational $p$-isogeny line.

An order-four wild character can have conductor four, so the bound is the
correct one at the level of all possible one-dimensional quotients. More
precisely, a nontrivial character supported only on the factor
$\{\pm1\}$ kills $1+4\mathbf Z_2$ and has conductor $2$. A quadratic
character nontrivial on $1+4\mathbf Z_2$ kills $1+8\mathbf Z_2$ and has
conductor $3$. A character of order four kills $1+16\mathbf Z_2$ but not
$1+8\mathbf Z_2$, so it has conductor $4$. Together with the trivial
character of conductor $0$, these exhaust the possibilities allowed by
(3.15).

For the nonexceptional fiber, (3.10d) improves this to order at most two and
conductor at most three. Thus the complete refinement is

$$
\begin{array}{c|c|c|c}
\text{stable }j&H_2&\operatorname{ord}\lambda(I_2)&a_2(\lambda)\\ \hline
j\ne0&H_2\in\{1,C_2\}&|H_2|\text{ divides }2&0,2,\text{ or }3,\\
j=0&H_2\in\{1,C_2,C_4\}&|H_2|\text{ divides }4&0,2,3,\text{ or }4.
\end{array}
\tag{3.16a}
$$

There is no conductor-one row because $\mathbf F_2^\times$ is trivial. The
full subgroup lists (3.7a) and (3.15a), together with (3.1a), prove the
general small-characteristic stable-inertia qualifications announced in
(1.8m); the refined tables (3.10a) and (3.16a) prove the sharper restrictions
when the rational prime-isogeny line is present.

### 3.6 The complete away-from-$p$ ledger

Combining Chapters 2 and 3 gives the promised classification.

| place and reduction | exact inertial mechanism on $C$ | conductor bound for $\lambda$ | power already trivial |
|---|---|---:|---:|
| any $q\ne p$, good | trivial | $0$ | $1$ |
| split or nonsplit multiplicative | trivial; nonsplit sign is unramified | $0$ | $1$ |
| additive potentially multiplicative, odd $q$ | ramified quadratic twist | $1$ | $2$ |
| additive potentially multiplicative, $q=2$ | ramified quadratic twist | $2$ or $3$ | $2$ |
| additive potentially good, $q\ge5$ | faithful tame cyclic character of exact order $e=2,3,4$, or $6$ | $1$ | $12$ |
| potentially good, $q=3$, stable $j\ne0$ | $H_3\in\{1,C_2\}$; line character faithful | $0$ or $1$ | $2$ |
| potentially good, $q=3$, stable $j=0$ | $H_3\in\{1,C_2,C_3,C_6\}$; line character faithful | at most $2$ | $6$ |
| potentially good, $q=2$, stable $j\ne0$ | $H_2\in\{1,C_2\}$; line character faithful | $0$, $2$, or $3$ | $2$ |
| potentially good, $q=2$, stable $j=0$ | $H_2\in\{1,C_2,C_4\}$; line character faithful | at most $4$ | $4$ |

Every row implies

$$
\boxed{\lambda^{12}|_{I_q}=1\quad(q\ne p).}
\tag{3.17}
$$

The table classifies the character on the stable line, not every possible
two-dimensional representation. In particular, multiplicative monodromy can
ramify the extension class while leaving $\lambda$ unramified. The complete
geometric automorphism groups at $2$ and $3$ are nonabelian, but (3.1g) shows
that their nonabelian stable-inertia subgroups cannot preserve the rational
prime-isogeny line; the groups which do occur in this table are cyclic and
act on that line faithfully.

At $q\ge5$, the proved calculation (1.8g)--(1.8i) gives the exact tame stable
degree. At $q=2,3$, that formula must not be reused: wild contributions in the
minimalization process mean that $v_q(\Delta_{\min})$ alone need not determine
the stable inertia group. The wild rows instead use $v_q(j)\ge0$ to select
potential good reduction, the qualified Tate-algorithm relation
(1.8l), the complete pointed automorphism classification, its faithful
prime-to-$q$ Tate-module action, and the unit filtration. Thus the conclusions
in those rows are independent of any unlisted small-characteristic
discriminant shortcut.

## 4. Order-$p$ group schemes at the coefficient prime

### 4.1 Why generic representation theory is insufficient

We now work locally over $K=\mathbf Q_p$, with $p\ge5$. The coefficient prime
is different from every place considered so far. The cyclotomic character is
ramified, $E[p]$ need not be étale over the valuation ring, and specialization
of geometric $p$-torsion points loses nonreduced directions. The correct
object is the schematic closure of the line inside an integral torsion model.

Suppose first that $E$ acquires good reduction over a finite extension $L/K$.
Let $R=\mathcal O_L$ and let $\mathcal E/R$ be the elliptic scheme. The closure

$$
\mathcal C=\overline{C_{L}}\subset\mathcal E[p]
\tag{4.1}
$$

is finite flat of rank $p$. To see the flatness rather than assume it, take the
ideal of $C_L$ in the generic Hopf algebra of $\mathcal E[p]$ and saturate its
inverse image in the integral Hopf algebra. The quotient is torsion-free over
the DVR, hence flat, and the Hopf operations preserve it because they do so on
the generic fiber. This also proves uniqueness: two finite-flat closed
subgroups with generic fiber $C_L$ have the same saturated Hopf ideal.

The closure has more information than the generic character. Over a ramified
base there are several nonisomorphic order-$p$ group schemes with the same
generic dimension. We next derive the integer which measures their position.

### 4.2 Derivation of the order-$p$ normal form

Let $R$ be a henselian mixed-characteristic DVR, let $v$ be normalized by
$v(\pi)=1$, and put

$$
e_R=v(p).
\tag{4.2}
$$

Let $H/R$ be a finite-flat commutative group of order $p$. Multiplication by
$p$ vanishes on its characteristic-zero generic fiber, and flatness makes the
generic fiber schematically dense, so it vanishes on $H$. Thus
$\mathbf F_p^\times$ acts by scalar automorphisms. Since $p-1$ is a
unit in $R$, the augmentation ideal of the Hopf algebra decomposes into
Teichmuller weight spaces. On the generic fiber, the nonzero geometric points
form one orbit under $\mathbf F_p^\times$, and every weight occurs once. The
weight-one summand is therefore an invertible $R$-module.

Here is the lattice calculation which shows that this one summand generates
the algebra. After a finite faithfully flat DVR extension which splits the
generic group, let $Z$ be the function taking the values $[c]$ on
$c\in\mathbf F_p$. Then

$$
Z^p=Z,
\qquad
1,Z,\ldots,Z^{p-1}
\tag{4.2a}
$$

is the generic coordinate basis, and $Z^i$ has scalar weight $i$. Write a
generator of the integral weight-$i$ lattice as $Y_i=\ell_iZ^i$. For
$i+j\le p-1$, closure under multiplication gives

$$
v(\ell_i)+v(\ell_j)\ge v(\ell_{i+j}).
\tag{4.2b}
$$

In the coproduct of $Z^{i+j}$, the coefficient of $Z^i\otimes Z^j$ reduces
to $\binom{i+j}{i}$: modulo the maximal ideal, addition is $U+V$. This
binomial coefficient is a unit because $i+j<p$. When $i+j=p-1$, it is still
a unit because $\binom{p-1}{i}\equiv(-1)^i\pmod p$. Integrality of the
coproduct therefore gives the reverse inequality in (4.2b). Hence equality
holds for every $i+j\le p-1$. Taking $j=1$ inductively shows that the
weight-$i$ lattice is generated by the $i$th power of a generator $X$ of the
weight-one lattice. The calculation descends along the faithfully flat
extension. Consequently

$$
1,X,X^2,\ldots,X^{p-1}
\tag{4.3}
$$

forms an $R$-basis, and the remaining product has weight one:

$$
X^p=aX
\tag{4.4}
$$

for some $a\in R$. We now derive the coproduct and its second parameter.
They will satisfy

$$
ab=w_p,
\qquad v(w_p)=v(p)=e_R.
\tag{4.5}
$$

Here $w_p/p$ is a unit depending only on the chosen universal weight-one
coordinate. The exact polynomial in the coproduct is irrelevant for inertia,
but deriving (4.5) ensures that the interval below has no missing integral
models.

We make the interpolation argument explicit. In the unramified ring
containing the Teichmuller representatives $[c]$, $c\in\mathbf F_p$, there is
a unique polynomial $\Phi_p(U,V)$ of degree at most $p-1$ in each variable
such that

$$
\Phi_p([c],[d])=[c+d].
\tag{4.5a}
$$

The relevant Vandermonde determinant is a unit because distinct
Teichmuller representatives have distinct residues. Scalar equivariance shows
that every mixed monomial of $\Phi_p-U-V$ has total degree $p$, and reduction
modulo $p$ makes this difference zero. Its coefficient ideal has valuation
exactly one: if all coefficients were divisible by $p^2$, the Teichmuller map
would be additive modulo $p^2$, contradicting
$p[1]\ne0\pmod {p^2}$. Choose a generator $w_p=p u_p$, with
$u_p\in R^\times$, of this coefficient ideal and put

$$
C_p(U,V)=\frac{\Phi_p(U,V)-U-V}{w_p}.
\tag{4.5b}
$$

At least one coefficient of $C_p$ is a unit. Over the universal ring

$$
R_0=R[A,B]/(AB-w_p),
\tag{4.5c}
$$

the formulas

$$
X^p=AX,
\qquad
\Delta(X)=X\otimes1+1\otimes X
+B C_p(X\otimes1,1\otimes X)
\tag{4.5d}
$$

define a Hopf algebra. Indeed, after adjoining $t$ with $t^{p-1}=A$ and
passing to the fraction field, put $Z=X/t$. Equation (4.5d) becomes
$t\Phi_p(Z_1,Z_2)$, ordinary addition on the constant group
$\mathbf F_p$. The Hopf identities are polynomial identities in the
torsion-free universal algebra. Since they hold on this dense generic locus,
they hold integrally and descend to $R_0$.

Conversely, for the arbitrary group $H$ already put into the form (4.4),
split its generic fiber and write $X=tZ$ with $t^{p-1}=a$. Homogeneity of
$C_p$ gives

$$
t\Phi_p(Z_1,Z_2)
=X_1+X_2+\frac{w_p}{a}C_p(X_1,X_2).
\tag{4.5e}
$$

Since $C_p$ has a unit coefficient, integrality of the original coproduct
forces $b=w_p/a\in R$. This proves $ab=w_p$ and proves that no additional
order-$p$ model has been omitted. In the perfect Hopf pairing with the
Cartier dual, the relation coefficient on one side is the primitive
coproduct coefficient on the other. Thus duality gives
$(a,b)\leftrightarrow(b,a)$ after a unit normalization.

Thus, after a harmless choice of frame,

$$
H=H_{a,b}=\operatorname{Spec}R[X]/(X^p-aX),
\qquad ab=w_p.
\tag{4.6}
$$

Changing $X$ to $uX$, $u\in R^\times$, replaces $a$ by $u^{p-1}a$ and $b$
by $u^{1-p}b$. Hence the integer

$$
r(H)=v(a),
\qquad 0\le r(H)\le e_R,
\tag{4.7}
$$

is intrinsic. It is the Oort--Tate or Raynaud exponent. The conormal module at
the identity gives a coordinate-free interpretation:

$$
\omega_H\simeq R/(a),
\qquad
\operatorname{length}_R(\omega_H)=r(H).
\tag{4.8}
$$

Traditional isogeny-signature tables often call this integer $a$. To avoid
confusing it with the Hopf parameter $a$ in (4.4), we write $r$ in the proofs
and set

$$
a_{\mathrm{OT}}=r(H).
\tag{4.8a}
$$

Thus every $(e,a)$ row requested by the traditional notation is the
corresponding $(e,a_{\mathrm{OT}})=(e,r)$ row below.

Duality gives

$$
r(H^D)=e_R-r(H).
\tag{4.9}
$$

Reduction of (4.6) derives the three types:

$$
\begin{array}{c|c|c}
r(H)&r(H^D)&H_{\overline k}\\ \hline
0&e_R&\text{étale},\\
0<r(H)<e_R&e_R-r(H)&\alpha_p\text{-type and local-local},\\
e_R&0&\text{multiplicative type}.
\end{array}
\tag{4.10}
$$

At the endpoints, after strict henselization, the groups are respectively
$\mathbf Z/p\mathbf Z$ and $\mu_p$. The unit part of $a$ records an unramified
twist and does not affect inertia.

### 4.3 The inertia character of the normal form

A nonzero geometric point of (4.6) has coordinate $z$ satisfying

$$
z^{p-1}=a.
\tag{4.11}
$$

Write $a=u\pi^r$. A $(p-1)$st root of the unit $u$ is obtained after an
unramified extension, whereas inertia acts on a chosen
$(p-1)$st root of $\pi$. Define the niveau-one tame fundamental character

$$
\theta_R:I_L\longrightarrow\mathbf F_p^\times
$$

by this action, normalized so that

$$
\chi_p|_{I_L}=\theta_R^{e_R}.
\tag{4.12}
$$

Equation (4.11) then gives the literal inertia formula

$$
\chi_H|_{I_L}=\theta_R^{r(H)}.
\tag{4.13}
$$

This proves, rather than labels, the endpoint characters: $r=0$ is
unramified, and $r=e_R$ is cyclotomic up to an unramified twist. Formula
(4.13) is also compatible with duality because

$$
\theta_R^{e_R-r}
=\chi_p\theta_R^{-r}.
\tag{4.14}
$$

### 4.4 Ordinary and supersingular ambient torsion

Return to $\mathcal C\subset\mathcal E[p]$. The reduction of the ambient
height-two group decides whether the exponent is an endpoint or an interior
point.

If $\widetilde E$ is ordinary, then over an algebraic closure its connected
and étale directions are

$$
0\longrightarrow\mu_p\longrightarrow\widetilde E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0.
\tag{4.15}
$$

There is no local-local order-$p$ subgroup of this ordinary group. Indeed, a
connected order-$p$ subgroup maps trivially to the étale quotient and hence
lies in the rank-$p$ subgroup $\mu_p$; it must therefore equal $\mu_p$. If an
order-$p$ subgroup is not connected, its identity component has rank one, so
the subgroup is étale. Therefore

$$
\widetilde E\text{ ordinary}
\quad\Longrightarrow\quad
r(\mathcal C)=0\text{ or }e_R.
\tag{4.16}
$$

If $\widetilde E$ is supersingular, the group $\widetilde E[p]$ and its dual
are connected. An étale or multiplicative subgroup would, after duality if
necessary, give a nonzero étale quotient, contradicting connectedness.
Therefore

$$
\widetilde E\text{ supersingular}
\quad\Longrightarrow\quad
0<r(\mathcal C)<e_R.
\tag{4.17}
$$

Over the unramified field $\mathbf Q_p$ itself, $e_R=1$, so (4.17) has no
integer solution. This proves directly that good supersingular reduction at
$p$ is incompatible with a $G_{\mathbf Q_p}$-stable $\mathbf F_p$-line.

### 4.5 Why the stable degree is one of $1,2,3,4,6$

At the coefficient prime $p\ge5$, potential good reduction is tame. Over the
maximal unramified extension, inertia acts on the stable differential through
the cyclic pointed automorphism groups of orders $2,3,4,6$. Let
$L/\mathbf Q_p^{\mathrm{nr}}$ be the minimal totally ramified field of good
reduction and put

$$
e=e(L/\mathbf Q_p^{\mathrm{nr}}).
\tag{4.19}
$$

Then

$$
e\in\{1,2,3,4,6\}.
\tag{4.20}
$$

The residue field is algebraically closed and $v_L(p)=e$. Thus the same
integer $e$ is both the stable ramification degree and the length of the
Oort--Tate interval $0\le r\le e$. For additive potentially good reduction,
the minimal equation derives $e$ through (1.8g)--(1.8h). This coincidence is what
turns finite-flat lengths into the rational numbers $r/e$, and ultimately into
the five integer weights.

## 5. Descent of the finite-flat exponent

### 5.1 The descent congruence

Let

$$
\omega=\chi_p|_{I_p}:I_p\longrightarrow\mathbf F_p^\times.
\tag{5.1}
$$

Wild inertia is pro-$p$, whereas $\mathbf F_p^\times$ has order $p-1$.
Therefore every $\mathbf F_p$-valued character of $I_p$ is tame, and since
$\omega$ is surjective it has the form

$$
\lambda|_{I_p}=\omega^k
\tag{5.2}
$$

for some $k\in\mathbf Z/(p-1)\mathbf Z$. Let $r=r(\mathcal C)$ over the
minimal good-reduction field $L$. Restricting (5.2) to $I_L$ and comparing
(4.12)--(4.13) gives

$$
\theta_L^{ek}=\theta_L^r,
$$

hence the exact descent congruence

$$
\boxed{ek\equiv r\pmod{p-1}.}
\tag{5.3}
$$

The same observation completes the conductor ledger at the coefficient prime:

$$
a_p(\lambda)=
\begin{cases}
0,&k\equiv0\pmod{p-1},\\
1,&k\not\equiv0\pmod{p-1}.
\end{cases}
\tag{5.3a}
$$

There is no Swan term. This remains true in the potentially multiplicative
quadratic-twist rows because a quadratic character at the odd prime $p$ is
tame.

This congruence contains all of the congruence restrictions in the
five-signature theorem. In particular, an exponent $r$ descends to an
$\mathbf F_p$-line precisely when

$$
\gcd(e,p-1)\mid r.
\tag{5.4}
$$

No guess about roots of unity in $\mathbf F_p$ is needed; (5.4) is the exact
linear congruence forced by the original line.

### 5.2 From a length to a twelfth-power weight

Because every $e$ in (4.20) divides $12$, define

$$
s=\frac{12r}{e}.
\tag{5.5}
$$

Multiplying (5.3) by $12/e$ gives

$$
12k\equiv\frac{12r}{e}=s\pmod{p-1}.
\tag{5.6}
$$

Using (5.2), this proves on the original inertia group, not merely after
restriction to $I_L$, that

$$
\boxed{\lambda^{12}|_{I_p}=\chi_p^s|_{I_p}.}
\tag{5.7}
$$

The twelfth power has two simultaneous origins. It clears the denominators
$e=2,3,4,6$ in the finite-flat ratio $r/e$, and it kills every stable descent
automorphism away from $p$. Either explanation alone would leave part of the
theorem unproved.

### 5.3 Derivation of every $(e,r)$ row

We now combine the ambient restriction (4.16)--(4.17) with the descent
criterion (5.4).

For ordinary stable reduction, only $r=0,e$ occur. They always satisfy (5.4)
and give $s=0,12$.

For supersingular stable reduction, $0<r<e$. Since $p$ is odd,
$\gcd(2,p-1)=2$, so there is no interior value for $e=2$. For the remaining
degrees:

- if $e=3$, the values $r=1,2$ descend exactly when $3\nmid p-1$, equivalently
  $p\equiv2\pmod3$;
- if $e=4$, the values $r=1,3$ never descend because $2\mid p-1$, while
  $r=2$ descends exactly when $4\nmid p-1$, equivalently
  $p\equiv3\pmod4$;
- if $e=6$, odd $r$ never descend, while $r=2,4$ descend exactly when
  $3\nmid p-1$, equivalently $p\equiv2\pmod3$.

The ordinary--supersingular label itself can also be read from the stable
automorphism. A descent of degree $3$ or $6$ forces the stable fiber to have
$j=0$, while degree $4$ forces $j=1728$. For a model $y^2=f(x)$ in
characteristic $p\ge5$, the Hasse invariant is the coefficient of $x^{p-1}$
in $f(x)^{(p-1)/2}$, and the fiber is ordinary exactly when this coefficient
is nonzero. For $j=0$ one may take $f=x^3+1$; the relevant coefficient is

$$
\binom{(p-1)/2}{(p-1)/3},
\tag{5.4a}
$$

which exists and is nonzero modulo $p$ exactly when $p\equiv1\pmod3$.
For $j=1728$ take $f=x^3+x$; the relevant coefficient is

$$
\binom{(p-1)/2}{(p-1)/4},
\tag{5.4b}
$$

which exists and is nonzero exactly when $p\equiv1\pmod4$. Thus cubic and
sextic stable fibers are ordinary in the congruence class complementary to
the class supporting their interior rows, and the same is true of quartic
stable fibers. This verifies that the endpoint and interior alternatives in
each such row never compete on the same stable fiber.

Substitution in (5.5) yields the complete table.

| stable reduction over $L$ | $e$ | allowed Oort--Tate exponents $r$ | resulting $s=12r/e$ | exact fiber/descent condition |
|---|---:|---|---|---|
| good ordinary | $1$ | $0,1$ | $0,12$ | none |
| potentially good ordinary, quadratic descent | $2$ | $0,2$ | $0,12$ | stable fiber ordinary |
| potentially good supersingular, quadratic descent | $2$ | none | none | impossible by (5.4) |
| potentially good ordinary, cubic descent | $3$ | $0,3$ | $0,12$ | $p\equiv1\pmod3$ |
| potentially good supersingular, cubic descent | $3$ | $1,2$ | $4,8$ | $p\equiv2\pmod3$ |
| potentially good ordinary, quartic descent | $4$ | $0,4$ | $0,12$ | $p\equiv1\pmod4$ |
| potentially good supersingular, quartic descent | $4$ | $2$ | $6$ | $p\equiv3\pmod4$ |
| potentially good ordinary, sextic descent | $6$ | $0,6$ | $0,12$ | $p\equiv1\pmod3$ |
| potentially good supersingular, sextic descent | $6$ | $2,4$ | $4,8$ | $p\equiv2\pmod3$ |

This derives, rather than postulates, the five values

$$
\boxed{s\in\{0,4,6,8,12\}.}
\tag{5.8}
$$

The table also explains what the compressed rows “$e=3,4,6$” mean. Endpoint
values come from ordinary stable reduction; interior values come from
supersingular stable reduction. Combining them without retaining this
ordinary--supersingular label hides the group-scheme reason for the omissions.

### 5.4 The same rows in minimal-discriminant language

At $p\ge5$, the Tate-algorithm classification and (1.8g) convert the table
into a minimal-discriminant test.

| $v_p(\Delta_{\min})$ and type | stable degree $e$ | possible supersingular signature mechanism |
|---|---:|---|
| $0$, good | $1$ | none; good supersingular has no stable line |
| $6$, $\mathrm I_0^*$ | $2$ | none |
| $4,8$, $\mathrm{IV},\mathrm{IV}^*$ | $3$ | $s=4,8$ if $p\equiv2\pmod3$ |
| $3,9$, $\mathrm{III},\mathrm{III}^*$ | $4$ | $s=6$ if $p\equiv3\pmod4$ |
| $2,10$, $\mathrm{II},\mathrm{II}^*$ | $6$ | $s=4,8$ if $p\equiv2\pmod3$ |

Whenever the stable fiber in a row is ordinary, it adds the endpoints
$0,12$. For degrees $3,6$ this means $p\equiv1\pmod3$, and for degree $4$
it means $p\equiv1\pmod4$; in the quadratic row one must inspect the stable
fiber itself. The minimal discriminant determines the stable degree but does
not by itself record this ordinary--supersingular datum.

Three explicit families make the interior rows visible. Assume $p\ge5$.

First consider

$$
E_3:y^2=x^3+p^2.
\tag{5.8a}
$$

Its discriminant has valuation $4$, so its stable degree is $3$. If
$p=\varpi^3$, the change $x=\varpi^2X$, $y=\varpi^3Y$ gives

$$
Y^2=X^3+1.
\tag{5.8b}
$$

The $j=0$ special fiber is supersingular exactly when
$p\equiv2\pmod3$. In that case the only descending interior exponents are
$a_{\mathrm{OT}}=1,2$, giving $s=4,8$.

Next consider

$$
E_4:y^2=x^3+px.
\tag{5.8c}
$$

Here $v_p(\Delta_{\min})=3$ and the stable degree is $4$. With
$p=\varpi^4$, the same weighted change gives

$$
Y^2=X^3+X.
\tag{5.8d}
$$

The $j=1728$ fiber is supersingular exactly when
$p\equiv3\pmod4$. The sole descending interior exponent is
$a_{\mathrm{OT}}=2$, and it gives $s=6$.

Finally,

$$
E_6:y^2=x^3+p
\tag{5.8e}
$$

has minimal discriminant valuation $2$ and stable degree $6$. After
$p=\varpi^6$ it again reduces to $Y^2=X^3+1$. When that fiber is
supersingular, the descending interior exponents are
$a_{\mathrm{OT}}=2,4$, again giving $s=4,8$.

These models do not prove existence of a rational isogeny: they display the
stable geometry which would support each finite-flat mechanism. The descent
congruence still decides whether a line defined over the original field can
occur.

### 5.5 Direct congruence check on the descended character

There is a useful independent check. Since $\lambda|_{I_p}=\omega^k$, equation
(5.7) is the congruence

$$
12k\equiv s\pmod{p-1}.
\tag{5.9}
$$

Thus

$$
\gcd(12,p-1)\mid s.
\tag{5.10}
$$

For $s=4,8$, this forces $3\nmid p-1$, giving (1.13). For $s=6$, it forces
$4\nmid p-1$, giving (1.14). This agrees with the row-by-row descent
calculation. The row calculation is stronger: it identifies cubic or sextic
supersingular descent behind $4,8$, and quartic supersingular descent behind
$6$.

### 5.6 Cartier duality and the balanced midpoint

The quotient direction in (1.2) has character $\chi_p\lambda^{-1}$. Over the
good-reduction field, Cartier duality replaces $r$ by $e-r$. Therefore

$$
s=\frac{12r}{e}
\longmapsto
\frac{12(e-r)}e=12-s.
\tag{5.11}
$$

The pairs and midpoint are

$$
0\longleftrightarrow12,
\qquad
4\longleftrightarrow8,
\qquad
6\longleftrightarrow6.
\tag{5.12}
$$

The word **balanced** for $s=6$ is therefore integral: the closure and its
Cartier dual both have conormal length $e/2$, and this midpoint can descend
only in the quartic row.

## 6. Semistable and potentially multiplicative reduction at $p$

### 6.1 Good ordinary reduction

If $E/\mathbf Q_p$ has good ordinary reduction, the base is unramified and the
Oort--Tate interval has length one. The only order-$p$ models are the étale and
multiplicative endpoints. Thus

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\chi_p.
\tag{6.1}
$$

If the reduction were good supersingular, Section 4.4 would leave no endpoint
and no interior integer. Hence no stable line exists.

### 6.2 Split and nonsplit multiplicative reduction

For a split Tate curve over $\mathbf Q_p$, the generic exact sequence remains

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0.
\tag{6.2}
$$

Its two diagonal inertia characters are $\chi_p$ and $1$. Any stable line has
one of these characters. For nonsplit multiplicative reduction the splitting
character is unramified, so the same inertia statement holds. This proves the
semistable assertion

$$
\boxed{\lambda|_{I_p}=1\text{ or }\chi_p}
\tag{6.3}
$$

for good ordinary and both multiplicative types.

The divisibility of $v_p(\Delta_{\min})$ by $p$ decides whether the canonical
Tate extension (6.2) has a finite-flat middle model over $\mathbf Z_p$; it does
not alter the two line characters. Indeed the Kummer class of the Tate
parameter has a unit representative modulo $p$th powers exactly when
$p\mid v_p(\Delta_{\min})$. The five-signature theorem needs only the line,
not an unjustified finite-flat model of the entire Tate $p$-torsion.

### 6.3 Additive potentially multiplicative reduction

If $v_p(j)<0$ but $E$ is additive, a ramified quadratic twist $\eta_p$ makes
it a Tate curve. Therefore the two possible line characters are

$$
\eta_p
\quad\text{and}\quad
\eta_p\chi_p.
\tag{6.4}
$$

Because $p$ is odd, the ramified quadratic character is tame and

$$
\eta_p|_{I_p}=\omega^{(p-1)/2}.
\tag{6.4a}
$$

The two exponents $(p-1)/2$ and $(p+1)/2$ are nonzero modulo $p-1$ for
$p\ge5$, so both characters in (6.4) have conductor exponent exactly one.
Taking twelfth powers removes the quadratic factor and gives

$$
\lambda^{12}|_{I_p}=1
\quad\text{or}\quad
\chi_p^{12}|_{I_p}.
\tag{6.5}
$$

Thus potentially multiplicative reduction permits only the endpoint
signatures $s=0,12$. The stronger unpowered assertion (6.3) requires actual
semistability; it is false for a ramified quadratic twist.

### 6.4 Completion of the local theorem

The coefficient-prime calculation gives (1.10)--(1.14), Sections 6.1--6.3 give
the semistable and potentially multiplicative refinements, and (3.17) gives
the away-from-$p$ assertion. This completes the proof of Theorem 1.1.

It is worth isolating the logical roles:

$$
\begin{array}{c|c}
\text{input}&\text{output}\\ \hline
\text{Tate uniformization}&\text{endpoint characters and quadratic twists},\\
\text{stable automorphism groups}&\lambda^{12}\text{ unramified away from }p,\\
\text{order-}p\text{ schematic closure}&0\le r\le e,\\
\text{ordinary/supersingular special fiber}&r\text{ endpoint/interior},\\
\text{descent congruence }ek\equiv r&\{0,4,6,8,12\}.
\end{array}
\tag{6.6}
$$

None of the five exponents is a possible prime degree. They are local weights
attached to a line whose existence is already assumed.

## 7. From the local weight to a global signature

### 7.1 The everywhere-unramified ratio

Choose the coefficient-prime mechanism and its integer
$s\in\{0,4,6,8,12\}$. Define

$$
\Theta=\lambda^{12}\chi_p^{-s}.
\tag{7.1}
$$

At $p$, equation (5.7) says that $\Theta|_{I_p}=1$. At every $q\ne p$,
equation (3.17) and the unramifiedness of $\chi_p$ give
$\Theta|_{I_q}=1$. Thus $\Theta$ is unramified at every finite prime.

Let $c$ be complex conjugation. Since $c^2=1$ and $p$ is odd,
$\lambda(c)=\pm1$. Every signature exponent is even, so

$$
\lambda(c)^{12}=1=(-1)^s=\chi_p(c)^s.
\tag{7.2}
$$

Hence $\Theta$ is even at the real place. A finite character of
$G_{\mathbf Q}$ unramified at every finite prime and even at infinity factors
through the ordinary ideal class group of $\mathbf Q$. That class group is
trivial. Therefore

$$
\boxed{
\lambda^{12}=\chi_p^s,
\qquad s\in\{0,4,6,8,12\}.}
\tag{7.3}
$$

This is the **global signature equality**. With arithmetic Frobenius, it reads

$$
\lambda(\operatorname{Frob}_r)^{12}=r^s
\qquad(r\ne p)
\tag{7.4}
$$

whenever a Frobenius lift is chosen. If $\lambda$ is ramified at $r$, changing
the lift multiplies its value by an inertial scalar whose twelfth power is one,
so (7.4) remains well defined.

### 7.2 What changes over a number field

The equality (7.3) uses two special facts about $\mathbf Q$: there is one
coefficient place and the ordinary class group is trivial. Let $F$ be a number
field in which $p$ is unramified. At each $\mathfrak p\mid p$, the same
finite-flat proof gives a local entry

$$
s_{\mathfrak p}\in\{0,4,6,8,12\}.
\tag{7.5}
$$

If all entries equal one integer $s$, then
$\lambda^{12}\chi_p^{-s}$ is unramified at every finite place and, after the
same parity check, factors through an appropriate class group of $F$. It need
not be trivial. If the entries differ, there is no single cyclotomic power to
remove them; the correct global object is a signature indexed by the
embeddings or by the primes above $p$.

Thus the local five-value theorem generalizes directly to every unramified
coefficient place, while the scalar global equality (7.3) is the precise
$\mathbf Q$ specialization. Ramification of $F$ at $p$ changes the length of
the Oort--Tate interval and requires a modified local statement; it is not
silently included here.

### 7.3 Duality and the three global branches

Replacing the isogeny by its dual changes $\lambda$ to
$\chi_p\lambda^{-1}$ and changes $s$ to $12-s$. Hence the five possibilities
organize into three branches:

$$
\begin{array}{c|c|c}
\text{branch}&\text{signatures}&\text{local origin at }p\\ \hline
\text{endpoint}&0,12&\text{étale or multiplicative direction},\\
\text{cubic}&4,8&\text{cubic or sextic supersingular descent},\\
\text{balanced}&6&\text{quartic supersingular midpoint}.
\end{array}
\tag{7.6}
$$

The endpoint and cubic branches are **unbalanced** because duality exchanges
two distinct weights. The balanced branch is fixed by duality and calls for a
quadratic character rather than an asymmetric resultant alone.

### 7.4 Exact small-prime collisions

The geometric mechanism determines an integer $s$, but the character
$\chi_p^s$ depends only on $s\bmod p-1$. The collision ledger is:

| coefficient prime | possible interior mechanisms | collisions among the five powers |
|---:|---|---|
| $5$ | $4,8$; no $6$ | $0,4,8,12$ all give the same power |
| $7$ | $6$; no $4,8$ | $0,6,12$ all give the same power |
| $11$ | $4,6,8$ | all five powers are distinct |
| $13$ | no interior mechanism | $0$ and $12$ give the same power |
| $p\ge17$ | subject to (1.13)--(1.14) | all five powers are distinct |

For $p=5,7,13$, one must retain the $(e,r)$ mechanism if a later argument
distinguishes balanced from endpoint behavior. For $p>13$, the integer
signature is intrinsic to the equality (7.3). The coefficient primes $2$ and
$3$ are excluded from the theorem because the coefficient characteristic then
coincides with the wild automorphism phenomena and the order-$p$ weight
decomposition used in Chapter 4 no longer supplies this five-row statement.

### 7.5 The semistable global endpoint

Suppose $E/\mathbf Q$ is semistable at every prime. At $q\ne p$, good or
multiplicative reduction makes $\lambda$ unramified by Chapter 2. At $p$,
equation (6.3) gives an endpoint. If $\lambda|_{I_p}=1$, then $\lambda$ is
unramified at every finite prime; if $\lambda|_{I_p}=\chi_p$, then the dual
character $\chi_p\lambda^{-1}$ is unramified at every finite prime. There is no
nontrivial finite extension of $\mathbf Q$ unramified at every finite prime;
equivalently, both the ordinary and narrow class groups of $\mathbf Q$ are
trivial. The chosen character is therefore trivial. Thus one of the two
isogenous curves has a rational point of order $p$.

This sharper conclusion uses the unpowered local statement (6.3). It cannot be
deduced merely by taking a twelfth root of (7.3), and it fails without treating
the ramified quadratic twist in additive potentially multiplicative reduction.

## 8. Stable specialization and a line-valued Frobenius root

### 8.1 Why potentially good reduction needs descent

Let $r\ne p$ be a rational prime and suppose

$$
v_r(j(E))\ge0.
\tag{8.1}
$$

Then $E$ has potentially good reduction. It is tempting to pass to a good
reduction field and use the Frobenius polynomial of the raw special fiber.
That is incomplete: Frobenius on the original descended line is a composite
of good-fiber Frobenius with the stable descent automorphism. At
$j=1728$ or $0$, that scalar can have order four or six, and at $r=2,3$ it
can come from a wild automorphism group.

Work over the maximal unramified extension of $\mathbf Q_r$, and take a finite
totally ramified extension $L$ over which $E$ has good reduction. Its residue
field is still $\overline{\mathbf F}_r$. Uniqueness of the elliptic model gives
descent automorphisms

$$
\gamma_\sigma:\widetilde E\longrightarrow\widetilde E
\qquad(\sigma\in\Phi_r).
\tag{8.2}
$$

If $F$ is arithmetic Frobenius, then

$$
F\gamma_\sigma F^{-1}=\gamma_\sigma^{\,r}
\tag{8.3}
$$

in the cyclic tame cases, with the analogous conjugation action on the full
wild group. The actual descent datum selects a composite $\gamma F$.
Faithfully flat descent for the proper smooth pointed curve is effective, so
$\gamma F$ is the arithmetic Frobenius of an $\mathbf F_r$-form
$E_\gamma$ of $\widetilde E$. Hence its action on prime-to-$r$ torsion has

$$
\det(\gamma F)=r,
\qquad
\operatorname{tr}(\gamma F)=a\in\mathbf Z,
\qquad
|a|\le2\sqrt r.
\tag{8.4}
$$

The determinant is $r$ because a pointed automorphism preserves the Weil
pairing and Frobenius acts on it by $r$. The trace and Hasse bound come from
the actual $\mathbf F_r$-form, not from assigning an integer trace to an
arbitrary matrix.

### 8.2 The stable-specialization lemma

The line $C$ descends with the curve. Let

$$
\alpha=\lambda(\gamma F)\in\mathbf F_p^\times.
\tag{8.5}
$$

It is an eigenvalue of (8.4), so

$$
\alpha^2-a\alpha+r=0.
\tag{8.6}
$$

The assertion $\alpha\in\mathbf F_p$, rather than merely
$\overline{\mathbf F}_p$, uses the original rational kernel line. By the
global signature equality,

$$
\alpha^{12}=r^s.
\tag{8.7}
$$

Changing the compatible Frobenius lift multiplies $\alpha$ by an inertial
line scalar. Chapters 2--3 prove that its twelfth power is one, so (8.7) is
unchanged.

We have proved the following reusable statement.

**Theorem 8.1 (stable-specialization trace lemma).** Assume $p\ge5$,
$r\ne p$, $v_r(j(E))\ge0$, and
$\lambda^{12}=\chi_p^s$. Then there exist

$$
a\in\mathbf Z,
\qquad
\alpha\in\mathbf F_p^\times
\tag{8.8}
$$

such that

$$
a^2\le4r,
\qquad
\alpha^2-a\alpha+r=0,
\qquad
\alpha^{12}=r^s.
\tag{8.9}
$$

The proof is valid for $r=2,3$. At those primes one retains the full wild
descent datum; equations (3.10) and (3.16) ensure that its scalar on the line
is killed by twelve. No tame-conductor assertion is used there.

### 8.3 Exceptional twists made visible

At a tame auxiliary prime, the descent ambiguity has the following concrete
forms:

| stable special fiber | twist coordinate | line scalar order | power killed by $12$ |
|---|---|---:|---:|
| $j\ne0,1728$ | quadratic | divides $2$ | yes |
| $j=1728$ | quartic | divides $4$ | yes |
| $j=0$ | sextic | divides $6$ | yes |

For $j=1728$, write $y^2=x^3+dx$ and choose $t^4=d$. The substitution
$x=t^2X$, $y=t^3Y$ changes by a fourth root of unity when $t$ is changed. For
$j=0$, the model $y^2=x^3+d$ and a sixth root $t^6=d$ give the sextic
analogue. In both cases the twisted eigenvalue changes by $\kappa$ with
$\kappa^{12}=1$, while the determinant remains $r$. These explicit twists are
the tame shadows of the descent construction in Section 8.1.

## 9. The unbalanced resultant sieve

### 9.1 The general resultant restriction

For a rational prime $r$, define the Hasse set

$$
H_r=\{a\in\mathbf Z:a^2\le4r\}.
\tag{9.1}
$$

For $a\in H_r$ and a signature $s$, put

$$
R_{r,a,s}=
\operatorname{Res}_T(T^2-aT+r,T^{12}-r^s)
\tag{9.2}
$$

and

$$
B_{r,s}=\prod_{a\in H_r}|R_{r,a,s}|.
\tag{9.3}
$$

If $v_r(j(E))\ge0$, Theorem 8.1 supplies a common root in $\mathbf F_p$.
Therefore

$$
p\mid R_{r,a,s}
\quad\text{for some }a\in H_r,
\qquad
p\mid B_{r,s}.
\tag{9.4}
$$

For $s\ne6$, every integer in (9.2) is nonzero. Indeed, a common complex root
$\beta$ of the two polynomials satisfies $|\beta|=\sqrt r$ by the quadratic
Weil polynomial, while $\beta^{12}=r^s$. Absolute values give
$r^6=r^s$, hence $s=6$. This proves nonvanishing for every unbalanced
signature.

For $s=6$, take $a=0$. The roots satisfy $\beta^2=-r$, and therefore
$\beta^{12}=r^6$. Thus $R_{r,0,6}=0$ and $B_{r,6}=0$. The failure of the
balanced resultant is structural, not a numerical accident.

### 9.2 A recurrence deriving every resultant

Reduce powers of $T$ modulo $T^2-aT+r$. Write

$$
T^n\equiv u_nT+v_n.
\tag{9.5}
$$

Then

$$
u_0=0,
\qquad v_0=1,
\tag{9.6}
$$

and multiplication by $T$ gives

$$
u_{n+1}=au_n+v_n,
\qquad
v_{n+1}=-ru_n.
\tag{9.7}
$$

At $n=12$ this yields

$$
u_{12}=a^{11}-10a^9r+36a^7r^2-56a^5r^3
+35a^3r^4-6ar^5,
\tag{9.8}
$$

$$
v_{12}=-a^{10}r+9a^8r^2-28a^6r^3+35a^4r^4
-15a^2r^5+r^6.
\tag{9.9}
$$

The remainder of $T^{12}-r^s$ is
$u_{12}T+(v_{12}-r^s)$. Evaluating it at the two roots of the quadratic and
multiplying derives

$$
\boxed{
R_{r,a,s}=(v_{12}-r^s)^2
+au_{12}(v_{12}-r^s)+ru_{12}^2.}
\tag{9.10}
$$

Thus the sieve requires no opaque Sylvester determinant. Equations
(9.1), (9.8)--(9.10) reproduce every integer used below.

### 9.3 The three-prime certificate

Suppose

$$
v_5(j(E)),\ v_7(j(E)),\ v_{11}(j(E))\ge0.
\tag{9.11}
$$

Then (9.4) gives

$$
p\mid\gcd(B_{5,s},B_{7,s},B_{11,s}).
\tag{9.12}
$$

For full reproducibility, substitution in (9.10) gives the endpoint ledger

$$
\begin{aligned}
B_{5,0}={}&2^{66}3^{14}5^{10}7^6 13^8 17^2 31^2 37^4
61^4 157^2 229^2,\\
B_{7,0}={}&2^{66}3^{42}5^8 7^{10}11^2 13^{12}19^4 31^2
37^6 43^2 61^6 73^2 2953^2,\\
B_{11,0}={}&2^{80}3^{24}5^{24}7^{16}11^2 13^{12}17^4 19^4
29^2 31^2 37^2 73^2 79^2 101^2 109^2 139^2\\
&\qquad\cdot313^2 337^2 3541^2 13009^2 15289^2 17041^2,
\end{aligned}
\tag{9.12a}
$$

the cubic ledger

$$
\begin{aligned}
B_{5,4}={}&2^{66}3^6 5^{40}11^2 13^8 17^4 149^2 181^2,\\
B_{7,4}={}&2^{66}3^{22}5^8 7^{48}11^2 17^2 19^6 23^2
73^2 541^6,\\
B_{11,4}={}&2^{84}3^{10}5^{22}11^{56}17^4 19^4 23^2 29^2
37^4 41^2 43^2 113^2 137^2 149^2\\
&\qquad\cdot193^2 1553^2 1933^2,
\end{aligned}
\tag{9.12b}
$$

and the dual ledgers

$$
\begin{aligned}
B_{5,8}={}&2^{66}3^6 5^{76}11^2 13^8 17^4 149^2 181^2,\\
B_{7,8}={}&2^{66}3^{22}5^8 7^{92}11^2 17^2 19^6 23^2
73^2 541^6,\\
B_{11,8}={}&2^{84}3^{10}5^{22}11^{108}17^4 19^4 23^2 29^2
37^4 41^2 43^2 113^2 137^2 149^2\\
&\qquad\cdot193^2 1553^2 1933^2,
\end{aligned}
\tag{9.12c}
$$

$$
\begin{aligned}
B_{5,12}={}&2^{66}3^{14}5^{118}7^6 13^8 17^2 31^2 37^4
61^4 157^2 229^2,\\
B_{7,12}={}&2^{66}3^{42}5^8 7^{142}11^2 13^{12}19^4 31^2
37^6 43^2 61^6 73^2 2953^2,\\
B_{11,12}={}&2^{80}3^{24}5^{24}7^{16}11^{158}13^{12}17^4 19^4
29^2 31^2 37^2 73^2 79^2 101^2 109^2 139^2\\
&\qquad\cdot313^2 337^2 3541^2 13009^2 15289^2 17041^2.
\end{aligned}
\tag{9.12d}
$$

Every remaining displayed factor is prime; trial division through its square
root verifies this, the largest being $17041$. Taking the minimum valuation
in each three-row ledger gives

$$
\gcd(B_{5,0},B_{7,0},B_{11,0})
=\gcd(B_{5,12},B_{7,12},B_{11,12})
$$

$$
=2^{66}3^{14}5^8 7^6 13^8 31^2 37^2,
\tag{9.13}
$$

and

$$
\gcd(B_{5,4},B_{7,4},B_{11,4})
=\gcd(B_{5,8},B_{7,8},B_{11,8})
$$

$$
=2^{66}3^6 5^8 11^2 17^2.
\tag{9.14}
$$

These factorizations are certificates because the recurrence computes each
factor in a finite Hasse interval:

$$
H_5=\{-4,\ldots,4\},
\quad
H_7=\{-5,\ldots,5\},
\quad
H_{11}=\{-6,\ldots,6\}.
\tag{9.15}
$$

Dual signatures have the same gcd because replacing a root $\alpha$ by
$r/\alpha$ exchanges $s$ with $12-s$; only powers of the auxiliary prime can
change before the three gcds are taken.

For $p>19$, (9.14) eliminates $s=4,8$. Equation (9.13) leaves

$$
p=31\quad\text{or}\quad p=37
\tag{9.16}
$$

in the endpoint branch.

### 9.4 Why the geometric resultant root is not enough

A resultant vanishes modulo $p$ when the two polynomials have a common root in
$\overline{\mathbf F}_p$. The kernel character gives the stronger condition
$\alpha\in\mathbf F_p$. This distinction removes $31$.

At $r=5$,

$$
5^{12}=1\pmod{31}.
\tag{9.17}
$$

The solutions of $\alpha^{12}=1$ in $\mathbf F_{31}^\times$ are

$$
\alpha\in\{1,5,6,25,26,30\}.
\tag{9.18}
$$

The trace forced by $\alpha^2-a\alpha+5=0$ is
$a=\alpha+5\alpha^{-1}$. Direct inversion gives

$$
\begin{array}{c|rrrrrr}
\alpha&1&5&6&25&26&30\\ \hline
\alpha+5\alpha^{-1}&6&6&12&19&25&25.
\end{array}
\tag{9.19}
$$

But the Hasse traces modulo $31$ are

$$
H_5\bmod31=\{0,1,2,3,4,27,28,29,30\},
\tag{9.20}
$$

which is disjoint from the second row of (9.19). Hence no
$\mathbf F_{31}$-valued line eigenvalue exists, and $p=31$ is impossible.

We have proved the exact conditional unbalanced restriction:

**Theorem 9.1 (three-prime unbalanced sieve).** Let $p>19$, suppose
$E/\mathbf Q$ has a rational $p$-isogeny, and assume (9.11). Then

$$
s=4,8\text{ is impossible},
\qquad
s=0,12\Longrightarrow p=37.
\tag{9.21}
$$

The hypotheses (9.11) do not follow from the local isogeny-character theorem.
In a rational-isogeny classification they must be supplied by an independent
modular specialization or cusp-rigidity argument. This boundary prevents the
resultant sieve from being applied at a potentially multiplicative auxiliary
prime, where there is no Hasse-bounded smooth special fiber.

## 10. The balanced signature and its quadratic character

### 10.1 The local midpoint forces $p\equiv3\pmod4$

Assume from now on that

$$
p>19,
\qquad
\lambda^{12}=\chi_p^6.
\tag{10.1}
$$

Because the five signature powers are distinct, this equality comes from the
quartic supersingular row

$$
(e,r)=(4,2).
\tag{10.2}
$$

The descent congruence is

$$
4k\equiv2\pmod{p-1}.
\tag{10.3}
$$

It has a solution exactly when $p\equiv3\pmod4$. Thus the balanced branch
begins with

$$
\boxed{p\equiv3\pmod4.}
\tag{10.4}
$$

This is not a later quadratic-reciprocity coincidence. It is the solvability
condition for descent of the self-dual order-$p$ group scheme.

### 10.2 Construction and conductor of the quadratic character

Define

$$
\psi=\lambda^6\chi_p^{-3}.
\tag{10.5}
$$

Equation (10.1) gives $\psi^2=1$. We determine its conductor at every place.

At $p$, write $\lambda|_{I_p}=\omega^k$. From (10.3),

$$
4k-2=(p-1)n
\tag{10.6}
$$

for an integer $n$. Both sides are congruent to $2$ modulo $4$, because
$p-1\equiv2\pmod4$, so $n$ is odd. Therefore

$$
6k-3=\frac32(4k-2)
=\frac{3n(p-1)}2
\equiv\frac{p-1}{2}\pmod{p-1}.
\tag{10.7}
$$

It follows that

$$
\psi|_{I_p}=\omega^{(p-1)/2},
\tag{10.8}
$$

the unique nontrivial quadratic tame character. Its conductor exponent is
exactly one.

Let $q\ne p$. The cyclotomic character is unramified. For $q\ge5$, Chapter 3
shows that the order of $\lambda(I_q)$ divides $12$. Since
$v_2(p-1)=1$, an element of $\mathbf F_p^\times$ whose order divides $12$
actually has order dividing $6$, so its sixth power is one. At $q=3$,
equation (3.10) already gives order dividing $6$. At $q=2$, equation (3.16)
gives order dividing $4$, and intersection with
$\mathbf F_p^\times$, whose $2$-part has order two, again gives order dividing
two. Consequently

$$
\psi|_{I_q}=\lambda^6|_{I_q}=1
\qquad(q\ne p).
\tag{10.9}
$$

At the real place, $\lambda(c)^6=1$ and $\chi_p(c)^{-3}=-1$, so

$$
\psi(c)=-1.
\tag{10.10}
$$

Thus $\psi$ is the unique odd quadratic character of finite conductor $p$.
Because $p\equiv3\pmod4$, its fundamental discriminant is $-p$:

$$
\boxed{
\psi(n)=\left(\frac{-p}{n}\right),
\qquad
K=\mathbf Q(\sqrt{-p}).}
\tag{10.11}
$$

Every local assertion in this conductor calculation has now been derived,
including the wild primes. In particular, (10.9) does not come from falsely
calling the $2$- or $3$-adic character tame.

### 10.3 Why everywhere potential good reduction is the exact next hypothesis

The class-group argument requires Theorem 8.1 at every split rational prime,
so assume

$$
j(E)\in\mathbf Z,
\tag{10.12}
$$

equivalently that $E$ is everywhere potentially good.

The balanced local theorem explains part, but not all, of this integrality. At
$p$, potentially multiplicative reduction permits only endpoint signatures,
contradicting the distinct balanced signature; hence $v_p(j)\ge0$. If
$q\ne p$ is potentially multiplicative, the Tate calculation gives, on a
compatible Frobenius lift,

$$
\lambda(\operatorname{Frob}_q)^{12}
\in\{1,q^{12}\}.
\tag{10.13}
$$

The global balanced equality gives $q^6$. Thus

$$
p\mid q^6-1.
\tag{10.14}
$$

At $q=2$, this is impossible for $p>19$ because $2^6-1=63$. At arbitrary odd
$q$, (10.14) alone is not a contradiction; a rational-isogeny classification
uses an independent cusp-rigidity theorem to exclude odd cuspidal reduction.
Thus (10.12) is the exact self-contained hypothesis for the class-field
theorem below, and the local proof specifies how a global application obtains
the $p$-adic and dyadic parts.

### 10.4 Split primes and the balanced trace congruence

Let $r\ne p$ be a rational prime split in
$K=\mathbf Q(\sqrt{-p})$. Under (10.12), Theorem 8.1 gives

$$
\alpha^2-a_r\alpha+r=0,
\qquad
|a_r|\le2\sqrt r,
\qquad
\alpha\in\mathbf F_p^\times.
\tag{10.15}
$$

Splitting means $\psi(\operatorname{Frob}_r)=1$. From (10.5),

$$
\alpha^6=r^3.
\tag{10.16}
$$

Put

$$
\zeta=\frac{\alpha^2}{r}.
\tag{10.17}
$$

Then $\zeta^3=1$. The other root of the quadratic in (10.15) is
$r/\alpha$, so

$$
\frac{a_r^2}{r}
=\zeta+2+\zeta^{-1}
=\begin{cases}
4,&\zeta=1,\\
1,&\zeta\ne1.
\end{cases}
\tag{10.18}
$$

in $\mathbf F_p$. Hence

$$
\boxed{p\mid(a_r^2-4r)(a_r^2-r).}
\tag{10.19}
$$

The argument works at $r=2,3$: wild stable descent was retained in Theorem
8.1, and its scalar was killed before (10.15) was formed.

### 10.5 No split rational prime below $p/4$

Suppose $r<p/4$. The Hasse bound gives

$$
0\le4r-a_r^2<p,
\qquad
|a_r^2-r|\le3r<p.
\tag{10.20}
$$

If (10.19) holds, one of the two integer factors must be zero. But neither
$a_r^2=4r$ nor $a_r^2=r$ is possible for a rational prime $r$. Therefore

$$
\boxed{r<p/4\quad\Longrightarrow\quad r\text{ is not split in }K.}
\tag{10.21}
$$

For completeness, the small-prime Hasse values are

$$
\begin{array}{c|c|c|c}
r& a_r&4r-a_r^2&a_r^2-r\\ \hline
2&-2,-1,0,1,2&4,7,8&-2,-1,2\\
3&-3,-2,-1,0,1,2,3&3,8,11,12&-3,-2,1,6.
\end{array}
\tag{10.22}
$$

No entry is divisible by $p>19$, confirming (10.21) directly at the two wild
places.

### 10.6 Minkowski generation and class number one

Every ideal class of the imaginary quadratic field $K$ contains an integral
ideal of norm at most

$$
\frac2\pi\sqrt p.
\tag{10.23}
$$

For $p>19$,

$$
\frac2\pi\sqrt p<\frac p4.
\tag{10.24}
$$

Choose such an ideal $\mathfrak a$ of least norm in its class and remove every
rational principal ideal dividing it. Consider a prime ideal factor
$\mathfrak r$ of what remains.

- It cannot lie above an inert prime $r$, because the unique prime above $r$
  is the principal ideal $(r)$, of norm $r^2$, and could be removed.
- It cannot be the ramified prime above $p$, whose norm $p$ exceeds the bound
  in (10.23).
- It cannot lie above a split prime, because then
  $r\le N\mathfrak a<(p/4)$, contradicting (10.21).

No prime factor remains. Hence $\mathfrak a=\mathcal O_K$, and every ideal
class is trivial. We have proved:

**Theorem 10.1 (balanced class-field theorem).** Let $p>19$. Suppose
$E/\mathbf Q$ is everywhere potentially good, has a rational $p$-isogeny,
and has balanced signature

$$
\lambda^{12}=\chi_p^6.
$$

Then

$$
\boxed{
p\equiv3\pmod4,
\qquad
h(\mathbf Q(\sqrt{-p}))=1.}
\tag{10.25}
$$

This theorem does not enumerate the imaginary quadratic fields of class
number one. That enumeration is an independent global theorem. The local
five-signature classification ends at the conductor of $\psi$; stable
specialization and Minkowski turn that conductor into the class-number
condition.

## 11. Exact hypotheses, exceptions, and reusable theorem package

### 11.1 One table for every finite place

For convenient citation, the local results can be compressed without losing
their hypotheses.

Let $p\ge5$, let $E/\mathbf Q$ have a rational $p$-isogeny, and let $\lambda$
be the kernel character.

| place | reduction | $\lambda\mid_I$ or its exact source | conductor information | twelfth-power conclusion |
|---|---|---|---|---|
| $q\ne p$ | good | $1$ | $0$ | $1$ |
| $q\ne p$ | split/nonsplit multiplicative | $1$; nonsplit sign unramified | $0$ | $1$ |
| odd $q\ne p$ | additive potentially multiplicative | ramified quadratic $\eta_q$ | $1$ | $1$ |
| $q=2\ne p$ | additive potentially multiplicative | ramified quadratic $\eta_2$ | $2$ or $3$ | $1$ |
| $q\ge5$, $q\ne p$ | additive potentially good | faithful tame character of exact order $e=2,3,4,6$ from Section 1.3 | $1$ | $1$ |
| $q=3\ne p$ | potentially good, stable $j\ne0$ | faithful $H_3\in\{1,C_2\}$ | $0$ or $1$ | $1$ |
| $q=3\ne p$ | potentially good, stable $j=0$ | faithful $H_3\in\{1,C_2,C_3,C_6\}$ | at most $2$ | $1$ |
| $q=2\ne p$ | potentially good, stable $j\ne0$ | faithful $H_2\in\{1,C_2\}$ | $0$, $2$, or $3$ | $1$ |
| $q=2\ne p$ | potentially good, stable $j=0$ | faithful $H_2\in\{1,C_2,C_4\}$ | at most $4$ | $1$ |
| $q=p$ | good ordinary | $1$ or $\chi_p$ | $0$ or $1$; finite-flat endpoint | $s=0$ or $12$ |
| $q=p$ | good supersingular | no $\mathbf F_p$-stable line | impossible | none |
| $q=p$ | split/nonsplit multiplicative | $1$ or $\chi_p$ on inertia | $0$ or $1$; semistable endpoint | $s=0$ or $12$ |
| $q=p$ | additive potentially multiplicative | $\eta_p$ or $\eta_p\chi_p$ | $1$; ramified quadratic twist | $s=0$ or $12$ |
| $q=p$ | potentially good ordinary | Oort--Tate endpoint $r=0,e$ | $0$ or $1$; $e=2,3,4,6$ | $s=0$ or $12$ |
| $q=p$ | potentially good supersingular | interior rows of Section 5.3 | $0$ or $1$; finite-flat local-local model | $s=4,6,8$ as in Section 5.3 |

The wild conductor bounds concern $\lambda$ itself. The conductor exponent of
$\lambda^{12}$ away from $p$ is exactly zero in every row. For the tame
additive row, the exact Kodaira type, discriminant valuation, component count,
good-reduction degree, and stable inertia order are the proved table in
Section 1.3. For the two wild residue characteristics, the Kodaira symbol has
the qualified discriminant relation (1.8l), while (3.10a) and (3.16a) give
the complete automorphism and character bounds; no column is inferred from
$12\mid e\delta$.

### 11.2 The coefficient-prime row certificate

The entire five-row calculation is contained in four formulas:

$$
0\le r\le e,
\qquad
\lambda|_{I_L}=\theta_L^r,
\qquad
ek\equiv r\pmod{p-1},
\qquad
s=\frac{12r}{e}.
\tag{11.1}
$$

Ordinary reduction forces $r=0,e$; supersingular reduction forces
$0<r<e$. With $e=1,2,3,4,6$, (11.1) gives exactly

$$
\begin{array}{c|c|c}
s& (e,r)&\text{condition}\\ \hline
0&(e,0)&\text{none},\\
4&(3,1),(6,2)&p\equiv2\pmod3,\\
6&(4,2)&p\equiv3\pmod4,\\
8&(3,2),(6,4)&p\equiv2\pmod3,\\
12&(e,e)&\text{none}.
\end{array}
\tag{11.2}
$$

This is the citation-level certificate for every local signature entry. The
omitted candidates are not omitted by convention: $e=2,r=1$ fails the descent
congruence; odd $r$ for $e=4,6$ fail because $p-1$ is even; and the remaining
interior values fail exactly in the complementary congruence classes.
In the two endpoint rows, “none” means that there is no further descent
congruence once an ordinary stable direction exists. For potentially good
reduction the fiber must still be ordinary: Section 5.3 derives
$p\equiv1\pmod3$ in degrees $3,6$ and $p\equiv1\pmod4$ in degree $4$.

### 11.3 Boundaries that must remain visible

The following qualifications are part of the theorem.

1. The coefficient prime satisfies $p\ge5$. The primes $2$ and $3$ require a
   different coefficient-prime theory.
2. The base field for the scalar global equality is $\mathbf Q$. Over a number
   field, class-group characters and multiple primes above $p$ remain.
3. The five integers label mechanisms. They are character-theoretically
   unambiguous only when their residues modulo $p-1$ are distinct; $p>13$ is a
   sufficient exact threshold among primes.
4. Potentially multiplicative reduction at $p$ gives endpoints only, but
   unpowered characters can carry a ramified quadratic twist unless the curve
   is semistable.
5. At $q\ne p$, multiplicative reduction can ramify the two-dimensional
   extension class even though the line character is unramified.
6. At $q=2,3$, the full stable automorphism group may be nonabelian. A
   rational prime-isogeny line forces the actual stable inertia subgroup to
   be cyclic and sees it faithfully; its conductor comes from the unit
   filtration.
7. A stable-specialization Hasse polynomial requires $v_q(j)\ge0$. It is not
   available at a potentially multiplicative auxiliary prime.
8. A vanishing resultant gives a geometric root. The rational isogeny gives
   the stronger $\mathbf F_p$-valued root condition.
9. The balanced class-number theorem requires everywhere potential good
   reduction. The local theorem supplies this at $p$ and, for $p>19$, at $2$;
   an independent global argument is needed at arbitrary odd bad primes.
10. Neither the local theorem, the resultant sieve, nor the balanced
    class-number condition is a classification of rational points on
    $X_0(p)$.

### 11.4 A necessity theorem ready for global use

The local and global consequences may now be stated in the form used by a
rational prime-isogeny necessity argument.

**Theorem 11.1 (five-signature necessity package).** Let $p>19$ and suppose
$E/\mathbf Q$ admits a rational cyclic $p$-isogeny with kernel character
$\lambda$. Then exactly one of the following character identities holds:

$$
\lambda^{12}=1,
\quad
\lambda^{12}=\chi_p^4,
\quad
\lambda^{12}=\chi_p^6,
\quad
\lambda^{12}=\chi_p^8,
\quad
\lambda^{12}=\chi_p^{12}.
\tag{11.3}
$$

The cubic identities require $p\equiv2\pmod3$; the balanced identity requires
$p\equiv3\pmod4$; and potential multiplicative reduction at $p$ permits only
the two endpoints.

If $j(E)$ is integral at $5,7,11$, the cubic branches are impossible and the
endpoint branches force $p=37$. If $E$ is everywhere potentially good, the
balanced branch forces

$$
h(\mathbf Q(\sqrt{-p}))=1.
\tag{11.4}
$$

Every implication in this statement has been proved above. What remains in a
full rational-isogeny classification is global geometry: proving the needed
integrality hypotheses, enumerating the independent class-number condition,
and analyzing the surviving modular curves.

## 12. Conclusion

A rational prime isogeny begins as a single invariant line, but its local
behavior is not governed by one uniform picture. Away from the coefficient
prime, stable reduction turns inertia into Tate monodromy, a quadratic twist,
or an automorphism of a good special fiber. The tame automorphism orders are
$2,3,4,6$; the exceptional characteristic-$3$ and characteristic-$2$ groups
have orders $12$ and $24$. Faithfulness on prime-to-residue-characteristic
torsion makes a stable prime-isogeny line exclude the nonabelian inertia
subgroups, and local units reduce the surviving cyclic orders to divisors of
$6$ and $4$. This gives the twelfth-power unramifiedness together with the
wild conductor bounds.

At the coefficient prime, the decisive datum is integral. The schematic
closure of the line is an order-$p$ group scheme with conormal length
$r$ in an interval of length $e$. Ordinary reduction forces the endpoints,
supersingular reduction forces the interior, and descent to the original
$\mathbf F_p$-line is the congruence $ek\equiv r\pmod{p-1}$. Clearing the
stable degrees by twelve produces exactly the five weights
$0,4,6,8,12$, with no hidden row.

Global reciprocity over $\mathbf Q$ then turns the one local weight into a
global signature. The unbalanced signatures meet Hasse-bounded Frobenius
polynomials and exact resultants. The balanced midpoint instead produces the
quadratic character of $\mathbf Q(\sqrt{-p})$, whose local conductor and small
split primes force a class-number condition. These are complementary
consequences of the same local classification, and their hypotheses now remain
visible at every step.
