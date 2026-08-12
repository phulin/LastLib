# Frey Isogeny Characters and Residual Irreducibility

## Contents

1. [The precise residual problem](#1-the-precise-residual-problem)
   - [The theorem needed by the Frey argument](#11-the-theorem-needed-by-the-frey-argument)
   - [Conventions](#12-conventions)
   - [The route and its boundary](#13-the-route-and-its-boundary)
2. [Stable lines, isogenies, and two-torsion](#2-stable-lines-isogenies-and-two-torsion)
   - [From a stable line to a rational isogeny](#21-from-a-stable-line-to-a-rational-isogeny)
   - [The two diagonal characters](#22-the-two-diagonal-characters)
   - [Odd isogenies preserve full two-torsion](#23-odd-isogenies-preserve-full-two-torsion)
3. [The local semistable character theorem](#3-the-local-semistable-character-theorem)
   - [Good reduction away from the coefficient prime](#31-good-reduction-away-from-the-coefficient-prime)
   - [Multiplicative reduction away from the coefficient prime](#32-multiplicative-reduction-away-from-the-coefficient-prime)
   - [Good reduction at the coefficient prime](#33-good-reduction-at-the-coefficient-prime)
   - [Multiplicative reduction at the coefficient prime](#34-multiplicative-reduction-at-the-coefficient-prime)
   - [The two signatures and their conductors](#35-the-two-signatures-and-their-conductors)
4. [Global reciprocity and a rational generator](#4-global-reciprocity-and-a-rational-generator)
   - [Balancing the two characters](#41-balancing-the-two-characters)
   - [Everywhere-unramified characters of the rationals](#42-everywhere-unramified-characters-of-the-rationals)
   - [The semistable isogeny theorem](#43-the-semistable-isogeny-theorem)
5. [The exact torsion exclusions used here](#5-the-exact-torsion-exclusions-used-here)
   - [The uniform range and level eleven](#51-the-uniform-range-and-level-eleven)
   - [A specialized genus-two descent criterion](#52-a-specialized-genus-two-descent-criterion)
   - [The level-thirteen curve](#53-the-level-thirteen-curve)
   - [The corrected two-descent certificate](#54-the-corrected-two-descent-certificate)
   - [The terminal reduction at seventeen](#55-the-terminal-reduction-at-seventeen)
6. [The mixed-seven obstruction](#6-the-mixed-seven-obstruction)
   - [Tate normal form and the order-seven locus](#61-tate-normal-form-and-the-order-seven-locus)
   - [Full two-torsion produces a genus-two point](#62-full-two-torsion-produces-a-genus-two-point)
   - [The complete Jacobian certificate](#63-the-complete-jacobian-certificate)
   - [The Abel-image calculation](#64-the-abel-image-calculation)
7. [The semistable full-two criterion](#7-the-semistable-full-two-criterion)
   - [The focused torsion input](#71-the-focused-torsion-input)
   - [Irreducibility in the full-two isogeny class](#72-irreducibility-in-the-full-two-isogeny-class)
8. [The Frey curve and its local ledger](#8-the-frey-curve-and-its-local-ledger)
   - [Normalization, two-torsion, and invariants](#81-normalization-two-torsion-and-invariants)
   - [Odd primes](#82-odd-primes)
   - [The minimal equation at two](#83-the-minimal-equation-at-two)
   - [Residual inertia and the exact conductor](#84-residual-inertia-and-the-exact-conductor)
   - [The coefficient-prime finite-flat condition](#85-the-coefficient-prime-finite-flat-condition)
9. [Frey irreducibility](#9-frey-irreducibility)
   - [The contradiction and the endpoint seven](#91-the-contradiction-and-the-endpoint-seven)
   - [Exact dependency and hypothesis ledger](#92-exact-dependency-and-hypothesis-ledger)
   - [Final theorem package](#93-final-theorem-package)
   - [Conclusion](#94-conclusion)

## 1. The precise residual problem

### 1.1 The theorem needed by the Frey argument

The Frey curve does not require a classification of every prime degree that
can occur as a rational isogeny. It requires a more focused statement. A
putative Fermat solution supplies a semistable elliptic curve with all of its
two-torsion rational. If its mod-$p$ representation were reducible, the
stable line would define a rational $p$-isogeny. Semistability then makes one
of the two diagonal characters globally unramified, hence trivial. A
rational point of order $p$ appears on one side of the isogeny, while full
rational two-torsion appears on both sides. Only the torsion configurations
that can arise in this chain need to be excluded.

The central structural theorem of this book is therefore the following.

**Semistable full-two irreducibility theorem.** Let $E/\mathbf Q$ be a
semistable elliptic curve and let $p\geq7$ be prime. If

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
$$

then $E[p]$ has no $G_{\mathbf Q}$-stable $\mathbf F_p$-line.

The application keeps all local data needed later. If

$$
a^p+b^p=c^p
$$

were a primitive nonzero solution and $E_{a,b,p}$ were its normalized Frey
curve, then

$$
\overline\rho_{E_{a,b,p},p}:G_{\mathbf Q}
\longrightarrow\operatorname{GL}_2(\mathbf F_p)
$$

would be irreducible, finite flat at $p$, odd, and unramified away from
$\{2,p\}$. Its prime-to-$p$ Artin conductor would be exactly $2$.

Broader isogeny, torsion, and Diophantine classification questions lie
outside this focused scope. The only point-level facts proved here are the
exclusions needed after the semistable character argument: prime order at
least $11$, and order $7$ in the presence of full rational two-torsion.

### 1.2 Conventions

The letter $p$ always denotes the coefficient prime and, when a stable line
is present, the degree of the resulting isogeny. Auxiliary rational primes
are denoted $q$ or $r$. For a finite prime $q$, let $G_q$ and $I_q$ be a
decomposition group and its inertia subgroup. We use arithmetic Frobenius,
normalized by

$$
\overline\chi_p(\operatorname{Frob}_q)=q\pmod p
\qquad(q\ne p),
\tag{1.1}
$$

where

$$
\overline\chi_p:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times
$$

is the mod-$p$ cyclotomic character. An elliptic curve over $\mathbf Q$ is
semistable when it has good or multiplicative reduction at every finite
prime. Full rational two-torsion means that the finite étale group scheme
$E[2]$ is constant, equivalently

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
\tag{1.2}
$$

For a one-dimensional residual character $\psi$ at a finite prime, its
Artin conductor exponent is denoted $a_q(\psi)$. For the two-dimensional
Frey representation, the prime-to-$p$ conductor is

$$
N(\overline\rho)=\prod_{q\ne p}q^{a_q(\overline\rho)}.
\tag{1.3}
$$

Every use of a modular curve starts with an actual elliptic curve and an
actual level structure. Thus no coarse rational point is silently promoted
to a pair over $\mathbf Q$.

### 1.3 The route and its boundary

There are four transitions in the proof:

$$
\begin{array}{c}
\text{stable line in }E[p]\\
\Downarrow\\
\text{rational }p\text{-isogeny with characters }\lambda,\mu\\
\Downarrow\ \text{semistable local analysis and reciprocity}\\
\text{rational }p\text{-torsion on one isogenous curve}\\
\Downarrow\ \text{focused point-level exclusions}\\
\text{contradiction for }p\ge7\text{ when }E[2]\text{ is rational.}
\end{array}
\tag{1.4}
$$

The first transition is the characteristic-zero subgroup-scheme dictionary.
The second is the main reusable isogeny-character argument. The third uses
the oriented formal-immersion theorem already established for $p\ge17$, the
completed level-$11$ calculation, a complete calculation on
$X_1(13)$, and a complete mixed-$7$ calculation. The final chapters
verify semistability and the complete local conductor ledger directly from
the Frey equation.

The prime $5$ is not a missing endpoint of this route. In the Fermat
blueprint it is eliminated on the separate cyclotomic-descent branch before
the Frey residual theorem is invoked. Nothing below imports that later
argument or claims a mod-$5$ irreducibility theorem.

General potentially good reduction produces twelfth-power signatures and
intermediate exponents. None occurs for a semistable curve. Developing those
branches would enlarge the book without strengthening (1.4), so the local
theorem below proves exactly the two semistable signatures $1$ and
$\overline\chi_p$. No potentially-good branch enters the argument.

## 2. Stable lines, isogenies, and two-torsion

### 2.1 From a stable line to a rational isogeny

Let $E/\mathbf Q$ be an elliptic curve and let $p$ be prime. In
characteristic zero,

$$
E[p](\overline{\mathbf Q})\simeq\mathbf F_p^2.
$$

Suppose $L\subset E[p](\overline{\mathbf Q})$ is a one-dimensional
$G_{\mathbf Q}$-stable subspace. Because $E[p]$ is finite étale, descent
identifies the $p$ geometric points of $L$ with a finite étale subgroup
scheme

$$
C\subset E[p]
$$

of rank $p$ over $\mathbf Q$. The quotient by this subgroup exists and gives
a separable isogeny

$$
\varphi:E\longrightarrow E'=E/C
\tag{2.1}
$$

of degree $p$. Conversely, the scheme-theoretic kernel of any rational
degree-$p$ isogeny gives such a line. Hence

$$
\boxed{
E[p]\text{ has a }G_{\mathbf Q}\text{-stable }\mathbf F_p\text{-line}
\Longleftrightarrow
E\text{ admits a rational cyclic }p\text{-isogeny}.}
\tag{2.2}
$$

The coefficient field in (2.2) is important. The proof produces a subgroup
scheme of rank $p$ over $\mathbf Q$, not merely a line after an arbitrary
extension of $\mathbf F_p$.

### 2.2 The two diagonal characters

Choose $0\ne P\in C(\overline{\mathbf Q})$. Stability of $C$ defines the
isogeny character

$$
\lambda:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times,
\qquad \sigma P=\lambda(\sigma)P.
\tag{2.3}
$$

In a basis beginning with $P$, the representation is upper triangular:

$$
\overline\rho_{E,p}\sim
\begin{pmatrix}
\lambda&*\\
0&\mu
\end{pmatrix}.
\tag{2.4}
$$

The Weil pairing gives

$$
\det\overline\rho_{E,p}=\overline\chi_p,
$$

and therefore

$$
\mu=\overline\chi_p\lambda^{-1}.
\tag{2.5}
$$

The character $\mu$ is not only the abstract quotient character. Cartier
duality and the Weil pairing identify it with the character on the kernel of
the dual isogeny

$$
\widehat\varphi:E'\longrightarrow E.
\tag{2.6}
$$

Thus replacing $\varphi$ by its dual exchanges $\lambda$ and $\mu$.

A rational subgroup is not necessarily rationally generated. The original
kernel contains a nonzero rational point exactly when $\lambda=1$; the dual
kernel contains one exactly when $\mu=1$. The global argument will prove
that one of these two alternatives occurs under semistability.

### 2.3 Odd isogenies preserve full two-torsion

The rational generator may occur on $E'$ rather than $E$, so the extra
two-torsion carried by the Frey curve must cross the isogeny. Let
$\varphi:A\to B$ be an isogeny of abelian varieties of odd degree $d$.
There is an isogeny $\varphi':B\to A$ such that

$$
\varphi'\varphi=[d]_A,
\qquad
\varphi\varphi'=[d]_B.
\tag{2.7}
$$

On a group scheme killed by $2$, multiplication by $d$ is the identity.
Restricting (2.7) therefore gives mutually inverse group-scheme maps

$$
\varphi[2]:A[2]\xrightarrow{\sim}B[2],
\qquad
\varphi'[2]:B[2]\xrightarrow{\sim}A[2].
\tag{2.8}
$$

Over $\mathbf Q$ these maps are Galois equivariant. In particular,

$$
A[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2
\Longleftrightarrow
B[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
\tag{2.9}
$$

If one of these curves also has a rational point of odd prime order $p$, its
rational torsion contains

$$
(\mathbf Z/2\mathbf Z)^2\oplus\mathbf Z/p\mathbf Z
\simeq
\mathbf Z/2\mathbf Z\oplus\mathbf Z/2p\mathbf Z.
\tag{2.10}
$$

Only the cases $p=7$ and $p\ge11$ of this observation will be used.

## 3. The local semistable character theorem

The local theorem is the engine of the argument. Its conclusion is simple,
but each hypothesis has a distinct role. Away from $p$, semistability makes
both diagonal characters unramified even when the extension class in (2.4)
is ramified. At $p$, finite-flat geometry leaves exactly an étale and a
multiplicative direction. We prove all four combinations of reduction type
and residue characteristic.

### 3.1 Good reduction away from the coefficient prime

Let $q\ne p$ and suppose $E$ has good reduction at $q$. Proper smooth base
change, or equivalently the prime-to-$q$ torsion theorem for the Néron model,
gives

$$
E[p]^{I_q}=E[p].
\tag{3.1}
$$

Thus inertia is trivial on $C$ and on $E[p]/C$. Consequently

$$
\lambda|_{I_q}=\mu|_{I_q}=1,
\qquad
a_q(\lambda)=a_q(\mu)=0.
\tag{3.2}
$$

This is stronger than saying that a power of $\lambda$ is unramified.

### 3.2 Multiplicative reduction away from the coefficient prime

Suppose next that $E$ has split multiplicative reduction at $q\ne p$.
Tate uniformization gives, after choosing a compatible $p$th root of the
Tate parameter, an exact sequence

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0.
\tag{3.3}
$$

In a Tate basis the local representation has the form

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\overline\chi_p(\sigma)&c_q(\sigma)\\
0&1
\end{pmatrix}.
\tag{3.4}
$$

For $q\ne p$, the cyclotomic character is unramified. On inertia, (3.4) is
therefore unipotent. Every eigenvalue of every inertial element is $1$, so
the scalar by which inertia acts on any stable line is $1$. The quotient
line has the same property. Hence (3.2) also holds in the split
multiplicative case.

For nonsplit multiplicative reduction, an unramified quadratic twist makes
the reduction split. If $\eta_q$ denotes the unramified splitting character,
both diagonal characters in (3.4) are multiplied by $\eta_q$. Its
restriction to $I_q$ is trivial, so the conclusion is unchanged.

This argument separates the diagonal characters from the extension class.
When $p\nmid v_q(\Delta_{\min})$, the cocycle $c_q|_{I_q}$ is nonzero and
the full two-dimensional representation is ramified, even though
$a_q(\lambda)=a_q(\mu)=0$. More precisely, for multiplicative reduction at
$q\ne p$,

$$
\overline\rho_{E,p}|_{I_q}=1
\Longleftrightarrow
p\mid v_q(\Delta_{\min}).
\tag{3.5}
$$

When the right side fails, inertia has a single nontrivial unipotent block,
its fixed space has dimension one, wild inertia is trivial, and

$$
a_q(\overline\rho_{E,p})=1.
\tag{3.6}
$$

### 3.3 Good reduction at the coefficient prime

Now let $q=p$ and suppose $E$ has good reduction. The stable subgroup
$C\subset E[p]$ has a unique finite-flat schematic closure

$$
\mathcal C\subset\mathcal E[p]
$$

over $\mathbf Z_p$. It has rank $p$. The order-$p$ classification over an
unramified discrete valuation ring has only two generic inertial types. If
the special fiber of $\mathcal C$ is étale, its generic character is
unramified. If it is connected, Cartier duality identifies its inertial
character with that of $\mu_p$. Therefore

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\overline\chi_p|_{I_p}.
\tag{3.7}
$$

Here is why no intermediate finite-flat weight has been hidden. The
order-$p$ group schemes over a DVR are described by parameters whose
valuation and the valuation of the dual parameter add to $v_p(p)$. Over
$\mathbf Z_p$ this sum is $1$, so integrality leaves only valuations $0$
and $1$. They are the étale and multiplicative cases above. Ramified bases
can have intermediate valuations; the base in this argument is not
ramified.

If $E$ has supersingular reduction, the ambient $E[p]$ has no stable
$\mathbf F_p$-line of the assumed kind; (3.7) remains a valid implication.
In the ordinary case it is the familiar connected--étale dichotomy.

### 3.4 Multiplicative reduction at the coefficient prime

Suppose $E$ has split multiplicative reduction over $\mathbf Q_p$. Tate
uniformization again gives (3.3), now with ramified cyclotomic character. If
$C=\mu_p$, then

$$
\lambda|_{I_p}=\overline\chi_p|_{I_p}.
$$

If $C\ne\mu_p$, its projection to the constant quotient in (3.3) is
nonzero and hence an isomorphism. Inertia acts trivially on that quotient,
so it acts trivially on $C$. Thus (3.7) holds here as well. An unramified
quadratic twist handles nonsplit multiplicative reduction without changing
inertia.

This proof does not assert that the Tate extension splits. The stable line
is either the canonical multiplicative line or maps isomorphically to the
constant quotient; those are precisely the two possibilities needed for
its character.

### 3.5 The two signatures and their conductors

Combining the preceding sections gives the exact local theorem.

**Local semistable isogeny-character theorem.** Let $p\ge5$, let
$E/\mathbf Q$ be semistable, and suppose that $E[p]$ has a stable line with
characters $\lambda$ and
$\mu=\overline\chi_p\lambda^{-1}$. Then

$$
\lambda|_{I_q}=\mu|_{I_q}=1
\qquad(q\ne p),
\tag{3.8}
$$

and at $p$ exactly one of the following two rows occurs:

| branch | $\lambda|_{I_p}$ | $\mu|_{I_p}$ | $(a_p(\lambda),a_p(\mu))$ |
|---|---|---|---|
| étale kernel | $1$ | $\overline\chi_p$ | $(0,1)$ |
| multiplicative kernel | $\overline\chi_p$ | $1$ | $(1,0)$ |

The conductor entries are exact. The extension
$\mathbf Q_p(\mu_p)/\mathbf Q_p$ is tamely ramified of degree $p-1$, so
$\overline\chi_p$ has Swan conductor zero and Artin conductor exponent one.
Duality exchanges the two rows.

These are the only local signatures retained in this book. The intermediate
twelfth-power signatures associated with additive potentially good
reduction are absent because semistability excludes that reduction type.
The “balanced” step needed globally is simply the choice of the unramified
member of the dual pair in this two-row table.

## 4. Global reciprocity and a rational generator

### 4.1 Balancing the two characters

Retain the hypotheses of the local theorem. Equation (3.8) says that both
$\lambda$ and $\mu$ are unramified at every finite prime different from
$p$. At $p$, the table in Section 3.5 says that one of them is unramified.
Define

$$
\psi=
\begin{cases}
\lambda,&\lambda|_{I_p}=1,\\
\mu,&\lambda|_{I_p}=\overline\chi_p|_{I_p}.
\end{cases}
\tag{4.1}
$$

Then

$$
\psi:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times
$$

is unramified at every finite prime. It is essential that we used the
characters themselves. From an assertion about $\lambda^{12}$ one could
only deduce that $\lambda$ has bounded order on inertia, not that a diagonal
character is globally unramified.

### 4.2 Everywhere-unramified characters of the rationals

Global reciprocity now closes the argument. Because $\psi$ has abelian
image, Artin reciprocity identifies it with a finite-order idele class
character of $\mathbf Q$. Unramifiedness at every finite prime says that its
finite conductor is $1$. Allowing ramification at the real place replaces
the ordinary class group by the narrow class group. But every nonzero ideal
of $\mathbf Z$ has a positive generator, so

$$
\operatorname{Cl}^+(\mathbf Q)=1.
\tag{4.2}
$$

The ray class group of conductor dividing the real place is therefore
trivial, and

$$
\psi=1.
\tag{4.3}
$$

The same conclusion also follows without reciprocity. The fixed field of
$\ker\psi$ would be a finite abelian extension of $\mathbf Q$ unramified at
all finite primes, hence would have discriminant $\pm1$. Minkowski's
discriminant bound excludes every nontrivial number field with that
discriminant. The reciprocity proof identifies the exact class group being
used; the discriminant proof confirms that no sign character at infinity
was overlooked.

### 4.3 The semistable isogeny theorem

If the first branch of (4.1) occurs, (4.3) says $\lambda=1$. Every generator
of $C$ is then rational and

$$
E(\mathbf Q)[p]\ne0.
$$

If the second branch occurs, $\mu=1$. The kernel of the dual isogeny has a
rational generator and

$$
E'(\mathbf Q)[p]\ne0.
$$

We have proved the reusable global statement.

**Semistable isogeny theorem.** Let $p\ge5$ and let $E/\mathbf Q$ be
semistable. If $E$ admits a rational cyclic $p$-isogeny
$E\to E'=E/C$, then

$$
\boxed{E(\mathbf Q)[p]\ne0\quad\text{or}\quad E'(\mathbf Q)[p]\ne0.}
\tag{4.4}
$$

The theorem does not say in advance which side contains the rational point.
That is why the group-scheme isomorphism (2.8) is indispensable in the
full-two application.

## 5. The exact torsion exclusions used here

The semistable isogeny theorem reduces residual reducibility to a
point-level question. We now prove only the part of that question used by
the Frey argument:

$$
E(\mathbf Q)[p]=0\quad(p\ge11\text{ prime}).
\tag{5.1}
$$

The preceding Eisenstein-cotangent theory already proves (5.1) for
$p\ge17$ and for $p=11$. We recall its mechanism to expose every
hypothesis. The sole remaining prime, $13$, is closed here by one explicit
genus-two descent and one finite reduction calculation.

### 5.1 The uniform range and level eleven

Suppose $P\in E(\mathbf Q)$ has prime order $p\ge17$. The pair $(E,P)$
defines a noncuspidal point of $Y_1(p)(\mathbf Q)$. Reduce its integral
extension at $3$. At an interior point the prime-to-$3$ point retains exact
order $p$, while

$$
\#\widetilde E(\mathbf F_3)\le3+1+2\sqrt3<8.
\tag{5.2}
$$

Thus reduction lies at the boundary. The orientation test for a Tate
$p$-gon says that a rational inward point would give order $p$ in a torus of
order $3-1$ or $3+1$. Since $p\nmid8$, the section reaches a rational
outward cusp $c$.

Put

$$
n_p=\frac{p-1}{\gcd(p-1,12)}.
\tag{5.3}
$$

For $p\ge17$, one has $n_p>1$. Choose a prime $\ell\mid n_p$. The
selected Eisenstein quotient $A_{\mathfrak m}$ constructed in the preceding
prime-level theory has finite rational group. Moreover, for the
component-oriented map

$$
X_1(p)\xrightarrow{w_p\rho}X_0(p)
\longrightarrow J_0(p)\longrightarrow A_{\mathfrak m},
\tag{5.4}
$$

a Hecke translate is a formal immersion at $c$ modulo $3$. The images of
the rational section and $c$ have the same reduction. Their difference is
torsion because $A_{\mathfrak m}(\mathbf Q)$ is finite, and reduction on
torsion is injective at the odd unramified prime $3$. Hence the two images
are equal. Formal immersion separates the two sections, forcing the
noncuspidal point to equal $c$, a contradiction.

This argument includes the boundary primes $17$ and $19$. At $17$ the
selected Eisenstein prime is $2$, and at $19$ it is $3$; primitive integral
cotangents make (5.4) valid in both cases.

At level $11$, the point-level curve has the genus-one model

$$
X_1(11):\quad y^2+y=x^3-x^2.
\tag{5.5}
$$

Its discriminant is $-11$. The five evident points are

$$
O, (0,0), (0,-1), (1,0), (1,-1),
\tag{5.6}
$$

and Tate parameters identify all five as cusps. The level-$11$ Eisenstein
quotient is isogenous to this Jacobian and has finite rational group.
Direct counts at the two good primes give

$$
\#X_1(11)(\mathbf F_2)=5,
\qquad
\#X_1(11)(\mathbf F_3)=5.
\tag{5.7}
$$

Reduction at the two primes bounds every rational torsion primary part, so
the rational group has order at most $5$. The points in (5.6) exhaust it.
Consequently there is no rational point of order $11$.

We have now proved (5.1) except at $p=13$. The failure of the uniform method
there is exact: $n_{13}=1$, so the selected Eisenstein quotient used in
(5.4) does not exist.

### 5.2 A specialized genus-two descent criterion

We isolate enough two-descent theory to make the level-$13$ calculation
complete from the stated foundations. Let

$$
C:z^2=F(x)
$$

be a smooth genus-two curve over $\mathbf Q$, where $F$ is a monic
squarefree sextic, and suppose the two points at infinity are rational. Put

$$
L=\mathbf Q[T]/(F(T)),
$$

and let $J$ be the Jacobian. Evaluation of $x-T$ on a divisor disjoint from
the branch divisor defines the even-degree Kummer map

$$
J(\mathbf Q)/2J(\mathbf Q)\longrightarrow
\mathcal F_{\mathbf Q},
\tag{5.8}
$$

where

$$
\mathcal F_{\mathbf Q}=
\left\{[\alpha]\in
L^\times/(L^{\times2}\mathbf Q^\times):
N_{L/\mathbf Q}(\alpha)\in\mathbf Q^{\times2}\right\}.
\tag{5.9}
$$

The scalar quotient distinguishes this from odd-degree descent. To retain
the lost norm trivialization, use pairs

$$
\mathcal H_{\mathbf Q}=
\frac{\{(\alpha,s):N(\alpha)=s^2\}}
{\{(\gamma^2r,N(\gamma)r^3):
\gamma\in L^\times, r\in\mathbf Q^\times\}}.
\tag{5.10}
$$

Kummer theory for the norm-one subgroup of
$\operatorname{Res}_{L/\mathbf Q}\mu_2$ identifies the obstruction-zero
part of $H^1(\mathbf Q,J[2])$ with (5.10). The rational point at infinity
removes the Picard obstruction. Projection to the first coordinate gives
an exact sequence

$$
0\longrightarrow\mathcal A_{\mathbf Q}
\longrightarrow\mathcal H_{\mathbf Q}
\longrightarrow\mathcal F_{\mathbf Q}\longrightarrow0,
\tag{5.11}
$$

with

$$
\mathcal A_{\mathbf Q}=\mu_2(\mathbf Q)/E_{\mathbf Q},
\tag{5.12}
$$

$$
E_{\mathbf Q}=
\{r^3N(\gamma)\in\mu_2(\mathbf Q):
\gamma^2r=1\}.
\tag{5.13}
$$

Indeed, a fake-trivial first coordinate is $\gamma^2r$; dividing by its
denominator in (5.10) leaves $(1,\epsilon)$ with $\epsilon^2=1$, and it is
trivial precisely for the signs in (5.13). In particular, if

$$
\zeta^2=-1,
\qquad N(\zeta)=1
\tag{5.14}
$$

for some $\zeta\in L$, then $(\gamma,r)=(\zeta,-1)$ gives
$E_{\mathbf Q}=\mu_2(\mathbf Q)$ and $\mathcal A_{\mathbf Q}=0$.

Choose a finite set $S$ containing $2$, infinity, and the primes of bad
reduction. Global Kummer classes have even valuation outside $S$, so they
lie in the finite squareclass space

$$
L(S,2)=\{[\alpha]\in L^\times/L^{\times2}:
v_{\mathfrak P}(\alpha)\equiv0\pmod2
\text{ for }\mathfrak P\nmid S\}.
\tag{5.15}
$$

Intersect the norm kernel modulo rational scalars with the complete local
images of (5.8). If this intersection is zero and (5.14) holds, (5.11)
shows that the true $2$-Selmer group is zero. The Kummer exact sequence and
finite generation then give

$$
J(\mathbf Q)/2J(\mathbf Q)=0,
\qquad
\operatorname{rank}J(\mathbf Q)=0,
\qquad
J(\mathbf Q)[2]=0.
\tag{5.16}
$$

This is the exact criterion used below. It requires complete local images,
not a sample of locally soluble points, and it retains the true-to-fake
kernel (5.11).

### 5.3 The level-thirteen curve

The reversible Tate-normal-form calculation in Book 147 gives the affine
modular model

$$
y^2+(x^3+x^2+1)y=x^2+x.
\tag{5.17}
$$

Completing the square with

$$
z=2y+x^3+x^2+1
$$

gives

$$
C_{13}:\quad z^2=F(x),
\tag{5.18}
$$

$$
F(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1,
\qquad
\operatorname{disc}(F)=-2^{12}13^2.
\tag{5.19}
$$

The two rational branches at infinity are denoted $\infty^+$ and
$\infty^-$ according as $z/x^3$ tends to $1$ or $-1$. In the coordinates
of (5.17), the six visible rational cusps are

$$
\mathcal C_{13}=
\{\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)\}.
\tag{5.20}
$$

Let $J_{13}=\operatorname{Jac}(C_{13})$ and put

$$
j(P)=[P-\infty^+],
\qquad
T=[\infty^- -\infty^+].
\tag{5.21}
$$

If $\iota$ is the hyperelliptic involution, then

$$
j(P)+j(\iota P)=T.
\tag{5.22}
$$

The translation by $T$ is the characteristic even-degree feature; treating
$\iota$ as negation would corrupt the final point sieve.

Put $L=\mathbf Q[\theta]/(F(\theta))$. Irreducibility follows modulo $3$
from

$$
\gcd(F,X^{3^2}-X)=\gcd(F,X^{3^3}-X)=1,
\qquad X^{3^6}\equiv X\pmod F.
\tag{5.23}
$$

The identity

$$
F(x)=(x^3+x^2+1)^2+4x(x+1)
\tag{5.24}
$$

also shows that $F$ has no real root. Outside $[-1,0]$ both terms are
nonnegative. Inside, put $x=-t$ with $0<t<1$; the square is at least $1$
and $4t(1-t)\le1$, with equality impossible simultaneously. Thus $L$ has
signature $(0,3)$.

An integral basis is

$$
\begin{aligned}
\beta_0&=1,&\beta_1&=\theta,&\beta_2&=\theta^2,\\
\beta_3&=\frac{\theta^2+\theta^4+\theta^5}{2},&
\beta_4&=\frac{\theta+\theta^3+\theta^4}{2},&
\beta_5&=\frac{1+\theta^3+\theta^4+\theta^5}{2}.
\end{aligned}
\tag{5.25}
$$

To make the computation explicit, multiplication by $\theta$ in this basis is

$$
M_\theta=
\begin{pmatrix}
0&0&-1&0&0&1\\
1&0&0&-2&0&-2\\
0&1&1&-3&0&-4\\
0&0&-2&0&1&2\\
0&0&0&0&0&1\\
0&0&2&-1&0&-3
\end{pmatrix}.
\tag{5.26}
$$

The other multiplication matrices are obtained exactly by substituting
$M_\theta$ into (5.25). They are integral, so the displayed lattice is an
order. Its trace-pairing determinant is

$$
-10816=-2^6 13^2.
\tag{5.27}
$$

The change-of-basis index over $\mathbf Z[\theta]$ is $8$. To certify
$2$-maximality, test the $63$ nonzero half-vectors
$\frac12\sum a_i\beta_i$, with $a_i\in\{0,1\}$. Their characteristic
polynomials are computed as determinants from (5.26). Write $c_k$ for the
coefficient of $X^{6-k}$. The first nonintegral coefficient is $c_4$ for

$$
000100, 000111, 010101, 111001,
$$

and $c_3$ for

$$
\begin{gathered}
001010, 001101, 001110, 010010, 010110, 011011,\\
100010, 100101, 100110, 101011, 110011.
\end{gathered}
$$

The first failure is $c_2$ for the other $48$ nonzero bit
vectors. Thus no integral half-vector enlarges the order. At $13$, direct
reduction gives

$$
F(X)\equiv
(X-3)^3(X^3+11X^2+8X+12)\pmod {13}.
\tag{5.28}
$$

After translating $X=3+U$, the Newton segment from $(0,1)$ to $(3,0)$ has
residual polynomial $5+6Y$. It gives one tame prime of type $(e,f)=(3,1)$;
for $q=X^3+11X^2+8X+12$ the test
$\gcd(q,X^{13}-X)=1$ proves that the cubic in (5.28) is irreducible and
unramified. The local different has
exponent $2$, already equal to (5.27), so no $13$-index remains. Therefore
(5.25) is the full ring of integers and

$$
\operatorname{disc}(L)=-2^6 13^2.
\tag{5.29}
$$

The Minkowski bound is

$$
\left(\frac4\pi\right)^3\frac{6!}{6^6}\sqrt{10816}
=\frac{8320}{81\pi^3}<3.32.
\tag{5.30}
$$

Reduction of the multiplication matrices modulo $2$ gives one nonunit ideal
of $8$ elements in the $64$-element ring, hence every prime above $2$ has
norm at least $8$. Modulo $3$, $F$ is irreducible, so every prime above $3$
has norm $3^6$. There is no ideal of norm $2$ or $3$, and (5.30) proves

$$
\operatorname{Cl}(L)=0.
\tag{5.31}
$$

Define

$$
\begin{aligned}
\zeta&=-\frac{4+11\theta+4\theta^2+\theta^3+3\theta^4+2\theta^5}{2},\\
\epsilon_1&=\frac{2+\theta+\theta^3+\theta^4}{2},\\
\epsilon_2&=\frac{4\theta+\theta^2+\theta^4+\theta^5}{2}.
\end{aligned}
\tag{5.32}
$$

Their characteristic polynomials are

$$
(X^2+1)^3,
\quad
X^6+2X^5-2X^3-X^2+1,
\quad
X^6+2X^5+4X^4+4X^3+3X^2+2X+1.
\tag{5.33}
$$

Thus $\zeta^2=-1$ and $\epsilon_1,\epsilon_2$ are units. A finite unit-index
certificate proves that they are fundamental. Interval Newton isolates the
three upper-half-plane roots of $F$ in rational boxes of width $10^{-9}$
centered at

$$
-1.4022257768+0.5865084714i,
\quad -0.3930361082+0.2538745688i,
\quad 0.7952618850+1.1596169599i.
\tag{5.34}
$$

The logarithmic rows of $\epsilon_1,\epsilon_2$ give regulator in
$(0.4341,0.4342)$. A representative of any missing unit coset lies in the
centered fundamental parallelogram, and inversion of the Minkowski matrix
bounds its integral coordinates by

$$
|a_0|<4.402, |a_1|<7.391, |a_2|<2.111,
|a_3|<5.308, |a_4|<2.803, |a_5|<2.104.
\tag{5.35}
$$

Exact determinants of the $185625$ multiplication matrices in this box,
together with interval evaluation in (5.34), leave only the coordinate
vectors

$$
\pm(1,0,0,0,0,0),
\qquad
\pm(2,5,1,2,1,0),
$$

the second pair being $\pm\zeta$. Hence

$$
\mathcal O_L^\times=
\langle\zeta\rangle\times\langle\epsilon_1,\epsilon_2\rangle,
\qquad |\langle\zeta\rangle|=4.
\tag{5.36}
$$

This completes the number-field input.

### 5.4 The corrected two-descent certificate

Put

$$
\pi_2=\frac{1+\theta^2-\theta^3}{2},
\quad
\pi_{13}=1+\theta+\theta^2,
$$

$$
\rho_{13}=15-62\theta-29\theta^2+7\theta^3
-15\theta^4-15\theta^5.
\tag{5.37}
$$

Exact norm and multiplication calculations give

$$
N(\pi_2)=8,
\qquad N(\pi_{13})=13,
\qquad N(\rho_{13})=13^3,
\tag{5.38}
$$

$$
2\epsilon_1^4\epsilon_2^6=\zeta\pi_2^2,
\qquad
13=\pi_{13}^3\rho_{13}.
\tag{5.39}
$$

Modulo $2$ one has

$$
F(X)\equiv(X^3+X^2+1)^2,
$$

with irreducible cubic factor. Reduction of the integral multiplication
table has a unique maximal ideal of residue degree three, and (5.39) gives
$(2)=(\pi_2)^2$. Thus $L\otimes\mathbf Q_2$ is one field with
$(e,f)=(2,3)$. At $13$, the two factors in (5.28) give primes of types
$(3,1)$ and $(1,3)$.

For $S=\{2,13,\infty\}$, equations (5.31), (5.36), and (5.39) show that

$$
L(S,2)=
\langle\zeta,\epsilon_1,\epsilon_2,
\pi_2,\pi_{13},\rho_{13}\rangle.
\tag{5.40}
$$

In this ordered basis, the columns of the rational scalar image
$(-1,2,13)$ and the rows of the norm map to the same rational squareclass
basis are

$$
C=
\begin{pmatrix}
0&1&0\\0&0&0\\0&0&0\\0&0&0\\0&0&1\\0&0&1
\end{pmatrix},
\qquad
N=
\begin{pmatrix}
0&0&0&0&0&0\\
0&0&0&1&0&0\\
0&0&0&0&1&1
\end{pmatrix}.
\tag{5.41}
$$

Indeed $[2]=[\zeta]$, $[-1]=[\zeta^2]=0$, and
$[13]=[\pi_{13}\rho_{13}]$. Thus the exact global ledger is

$$
6\xrightarrow{\text{scalar quotient}}4
\xrightarrow{\text{norm}}2,
\tag{5.42}
$$

and the two remaining fake classes are

$$
b_1=[\epsilon_1],
\qquad b_2=[\epsilon_2].
\tag{5.43}
$$

At every finite place outside $S$, these global classes are unramified. The
curve has good odd reduction there, and the local Kummer image is exactly
the unramified subgroup. Hence no omitted good place can impose an
additional cut.

At $2$, since $1+8\mathcal O_{L,2}$ consists of squares, unit
squareclasses are decided modulo $8$ in the basis (5.25). The following
seven residues are a basis of the local unit squareclass group:

$$
\begin{aligned}
q_1&=[0,0,0,0,0,1],&q_2&=[0,0,0,0,1,0],&
q_3&=[0,0,0,0,1,1],\\
q_4&=[0,0,0,1,1,1],&q_5&=[0,0,1,0,0,1],&
q_6&=[0,0,1,0,1,0],\\
q_7&=[0,0,1,1,0,0].&&
\end{aligned}
\tag{5.44}
$$

Here $[a_0,\ldots,a_5]$ denotes $\sum a_i\beta_i$ modulo $8$. Exact
multiplication in the $8^6$-element quotient finds $229376$ units and
$1792$ unit squares; the $128$ products of the $q_i$ occupy distinct square
cosets. This proves both independence and completeness. In $q_i$ coordinates
the scalar rows, two local point rows, and the two global rows are

$$
\begin{array}{c|c}
2/\pi_2^2&0100010\\
5&0001011\\
1-\theta&0010110\\
2-\theta&0110010\\
\epsilon_1&1111001\\
\epsilon_2&0100000.
\end{array}
\tag{5.45}
$$

The first two rows are the complete local scalar image: $-1=\zeta^2$ is a
square in $L_2$, while $2/\pi_2^2$ and $5$ represent the remaining
squareclasses of rational scalars of even local valuation.

The local point rows come from

$$
(1,\sqrt{17}),
\qquad(2,\sqrt{193})\in C_{13}(\mathbf Q_2),
$$

because both radicands are $1$ modulo $8$. Since $F$ is irreducible over
$\mathbf Q_2$, one has $J_{13}(\mathbf Q_2)[2]=0$, and the local dimension
formula gives

$$
\dim_{\mathbf F_2}J_{13}(\mathbf Q_2)/2J_{13}(\mathbf Q_2)=2.
\tag{5.46}
$$

The two point rows in (5.45) are independent modulo the scalar rows, so they
are the complete projected local image. Two functionals annihilating those
four rows evaluate on $(b_1,b_2)$ as

$$
\begin{array}{c|cc}
&b_1&b_2\\ \hline
\mathbf Q_2&1&0\\
\mathbf Q_2&0&1.
\end{array}
\tag{5.47}
$$

Both global candidates are therefore excluded at $2$.

For an independent check at $13$, the algebra has a totally ramified cubic
factor and an unramified cubic factor. If $\bar\eta$ is the residue of $X$
in the latter, direct exponentiation for the listed unit $u$ gives

$$
\begin{array}{c|cc|cc}
&u(3)&u(3)^6&u(\bar\eta)&
u(\bar\eta)^{(13^3-1)/2}\\ \hline
\epsilon_1&11&-1&9+2\bar\eta+12\bar\eta^2&-1\\
\epsilon_2&10&1&12+5\bar\eta&1.
\end{array}
\tag{5.48}
$$

A rational nonsquare has character $(-1,-1)$ in these odd-degree factors,
so both classes are locally scalar. The two irreducible cubic factors also
give $J_{13}(\mathbf Q_{13})[2]=0$, and multiplication by $2$ is an
automorphism on the pro-$13$ subgroup. Hence the $13$-adic local quotient is
zero. The corrected local ledger is

$$
2\xrightarrow{\mathbf Q_2}0
\xrightarrow{\mathbf Q_{13}}0.
\tag{5.49}
$$

There is no second obstruction at $13$. Finally, (5.33) gives
$\zeta^2=-1$, and a determinant gives $N(\zeta)=1$. Criterion (5.14)
makes the true-to-fake kernel zero. Thus

$$
\operatorname{Sel}_2(J_{13}/\mathbf Q)=0,
\qquad
\operatorname{rank}J_{13}(\mathbf Q)=0,
\qquad
J_{13}(\mathbf Q)[2]=0.
\tag{5.50}
$$

Direct good-reduction counts are

$$
\begin{array}{c|cc|c}
r&\#C_{13}(\mathbf F_r)&\#C_{13}(\mathbf F_{r^2})
&\#J_{13}(\mathbf F_r)\\ \hline
3&6&8&19\\
5&6&12&19.
\end{array}
\tag{5.51}
$$

For genus two the last column follows from

$$
\#J(\mathbf F_r)=
\frac{\#C(\mathbf F_r)^2+\#C(\mathbf F_{r^2})}{2}-r.
\tag{5.52}
$$

The class $T$ in (5.21) is nonzero: if its divisor were principal, the
corresponding function would have degree one on a genus-two curve. Since
(5.50) makes $J_{13}(\mathbf Q)$ finite, prime-by-prime injection into the
two groups in (5.51) bounds its order by $19$. The nonzero class $T$ then
has order $19$ and exhausts the group:

$$
\boxed{J_{13}(\mathbf Q)=\langle T\rangle
\simeq\mathbf Z/19\mathbf Z.}
\tag{5.53}
$$

### 5.5 The terminal reduction at seventeen

It remains to determine which of the nineteen Jacobian classes lie on the
curve. At $17$, the root $x=1$ of the reduced sextic is moved to infinity by

$$
X=(x-1)^{-1},
\qquad Y=zX^3,
\qquad w=Y/5.
$$

The resulting pointed quintic is

$$
w^2=X^5+13X^4+10X^3+16X^2+X+15.
\tag{5.54}
$$

The reduction of $T$ is represented in Mumford notation by

$$
\overline T=[X^2,10+6X].
$$

For completeness, here is the exact composition rule used to check the
table below. On a monic quintic $w^2=H(X)$ over a field of characteristic
different from $2$, let $[u_i,v_i]$ be reduced pairs. Choose monic greatest
common divisors and Bezout coefficients

$$
d_1=a u_1+b u_2,
\qquad
d=c d_1+e(v_1+v_2).
$$

The unreduced sum is represented by

$$
u=\frac{u_1u_2}{d^2},
\qquad
v\equiv
\frac{ca u_1v_2+cb u_2v_1+e(v_1v_2+H)}{d}
\pmod u.
$$

Make $u$ monic. While $\deg u>2$, replace

$$
u\longleftarrow
\operatorname{monic}\!\left(\frac{H-v^2}{u}\right),
\qquad
v\longleftarrow -v\pmod u.
$$

The identity is $[1,0]$ and the inverse of $[u,v]$ is
$[u,-v\bmod u]$. The two gcds handle coincident or conjugate support, so
this rule verifies doubling as well as addition of disjoint divisors. It is
the degree-two Riemann--Roch reduction written as an explicit polynomial
calculation.

Repeated exact Cantor addition gives the following nineteen distinct
reduced pairs, with coefficients in $\mathbf F_{17}$:

$$
\begin{array}{c|c|c@{\qquad}c|c|c}
n&u_n&v_n&n&u_n&v_n\\ \hline
0&1&0&10&X^2+10X+9&4+14X\\
1&X^2&10+6X&11&X^2+2X+1&11+X\\
2&X^2+10X+9&1+8X&12&X^2+X+13&6X\\
3&X^2+9X&7+8X&13&X^2+X&7\\
4&X^2+9X&10+14X&14&X^2+X&10+3X\\
5&X^2+X&7+14X&15&X^2+9X&7+3X\\
6&X^2+X&10&16&X^2+9X&10+9X\\
7&X^2+X+13&11X&17&X^2+10X+9&16+9X\\
8&X^2+2X+1&6+16X&18&X^2&7+11X\\
9&X^2+10X+9&13+3X&&&
\end{array}
\tag{5.55}
$$

Each $u_n$ is monic, $\deg v_n<\deg u_n\le2$, and $u_n$ divides the
right side of (5.54) minus $v_n^2$. Addition by $\overline T$ advances one
row. Unique reduced representation makes (5.55) an exact cyclic-group
certificate rather than a numerical search.

Direct evaluation of the curve over $\mathbf F_{17}$ and comparison with
(5.55) is finite and transparent:

$$
\begin{aligned}
C_{13}(\mathbf F_{17})=\{&\infty^+,\infty^-,(0,\pm1),(1,0),
(6,\pm6),(8,0),\\
&(12,\pm2),(13,\pm8),(15,0),(16,\pm1)\}.
\end{aligned}
$$

Converting these points to the quintic coordinates gives

$$
j_{17}(C_{13}(\mathbf F_{17}))\cap\langle\overline T\rangle
=\{0,1,4,6,14,16\}\overline T.
\tag{5.56}
$$

The six global cusps have precisely these labels:

$$
\begin{array}{c|cccccc}
P&\infty^+&\infty^-&(0,0)&(0,-1)&(-1,0)&(-1,-1)\\ \hline
j(P)/T&0&1&6&14&16&4.
\end{array}
\tag{5.57}
$$

Reduction is injective on the rational group of order $19$. Hence any
rational point has the same Abel class as one of the six cusps. The Abel map
$P\mapsto[P-\infty^+]$ is injective: a principal divisor $P-Q$ would give
a degree-one function on a genus-two curve. Therefore

$$
\boxed{X_1(13)(\mathbf Q)=\mathcal C_{13}.}
\tag{5.58}
$$

All these points are cuspidal, so no elliptic curve over $\mathbf Q$ has a
rational point of order $13$. Together with Sections 5.1, this proves (5.1)
for every prime $p\ge11$ without invoking any classification of rational
isogeny degrees or of composite torsion groups.

## 6. The mixed-seven obstruction

Rational points of order $7$ exist on elliptic curves over $\mathbf Q$, so
the point-level theorem (5.1) cannot handle the endpoint of the Frey range.
The missing input is full rational two-torsion. Tate normal form turns that
extra condition into a rational point on one explicit genus-two curve. We
then determine that curve directly.

### 6.1 Tate normal form and the order-seven locus

Let $P$ be a rational point of order at least four. Moving $P$ to the
origin, making its tangent the line $y=0$, and using the remaining scaling
puts the marked curve in Tate normal form

$$
E(b,c):\quad
y^2+(1-c)xy-by=x^3-bx^2,
\qquad P=(0,0),
\tag{6.1}
$$

with $b\ne0$ and nonzero discriminant. The chord-and-tangent law gives

$$
2P=(b,bc),
\qquad
3P=(c,b-c),
\tag{6.2}
$$

$$
4P=\left(
\frac{b(b-c)}{c^2},
\frac{b^2(c^2+c-b)}{c^3}
\right).
\tag{6.3}
$$

On the nondegenerate locus, imposing $3P=-4P$ first produces
$t=b/c$ from the equality of $x$-coordinates. The equality of the
$y$-coordinates then gives

$$
b=t^3-t^2,
\qquad c=t^2-t.
\tag{6.4}
$$

Conversely substitution in (6.2)--(6.3) gives $3P=-4P$. The removed
factors are precisely $t=0,1$ and the singular discriminant factors, so
every nonsingular marked curve with $P$ of exact order $7$ occurs in the
open part of (6.4).

### 6.2 Full two-torsion produces a genus-two point

On a generalized Weierstrass equation, a point is fixed by negation when
$2y+a_1x+a_3=0$. Eliminating $y$ from this equation and (6.1) gives the
cubic whose roots are the $x$-coordinates of the three nonzero
two-torsion points:

$$
F_{b,c}(X)=
4X^3+\bigl((1-c)^2-4b\bigr)X^2
+2b(c-1)X+b^2.
\tag{6.5}
$$

Full rational two-torsion makes this cubic split over $\mathbf Q$, so its
discriminant is a square. Substitution of (6.4) gives the exact identity

$$
\operatorname{disc}F_{t^3-t^2,t^2-t}
=16t^7(t-1)^7(t^3-8t^2+5t+1).
\tag{6.6}
$$

For $t\ne0,1$, divide a square root by $4t^3(t-1)^3$. Every elliptic curve
with the forbidden mixed torsion then gives a nondegenerate rational point
on

$$
C_7:\quad
z^2=t(t-1)(t^3-8t^2+5t+1).
\tag{6.7}
$$

Only this direction is asserted. A square discriminant does not by itself
make a cubic split.

The quintic

$$
f(t)=t^5-9t^4+13t^3-4t^2-t
\tag{6.8}
$$

is squarefree, with discriminant $7^4$. Its smooth projective model has
genus two and one rational point $\infty$ at infinity. The parameters
$t=0,1$ give $(0,0),(1,0)$ and are degenerate in (6.4); $\infty$ is the
compactifying cusp. It remains to prove

$$
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.
\tag{6.9}
$$

### 6.3 The complete Jacobian certificate

Let $J_7=\operatorname{Jac}(C_7)$ and use $\infty$ as Abel base point.
For a monic quintic, every Jacobian class has a unique reduced Mumford pair
$[u,v]$, where $u$ is monic,

$$
\deg v<\deg u\le2,
\qquad u\mid f-v^2.
\tag{6.10}
$$

This is the degree-two Riemann--Roch reduction: cancel conjugate pairs in an
effective divisor and replace every residual divisor of degree greater than
two by the complementary intersection with a function $v(t)-z$.
Uniqueness follows because two reduced divisors of degree at most two in the
same class would give a function with an impossible pole divisor, except
for the conjugate-pair cancellation already removed.

Define

$$
T_0=[t,0],
\qquad T_1=[t-1,0],
\qquad A=[t^2-t+1,1-3t].
\tag{6.11}
$$

The first two are independent points of order two: their sum is the
nonidentity reduced class $[t(t-1),0]$. Exact division gives

$$
f-(1-3t)^2=(t^2-t+1)(t^3-8t^2+4t-1),
\tag{6.12}
$$

and one Cantor reduction gives

$$
2A=[t^2-t+1,3t-1]=-A.
\tag{6.13}
$$

Thus $A$ has exact order three.

The odd-degree descent algebra is

$$
L=\mathbf Q\times\mathbf Q\times K,
\qquad
K=\mathbf Q(\theta),
\quad \theta^3-8\theta^2+5\theta+1=0.
\tag{6.14}
$$

Let $\alpha^3+\alpha^2-2\alpha-1=0$. Direct substitution gives

$$
\theta=-1-\alpha+2\alpha^2,
\qquad
\mathcal O_K=\mathbf Z[\alpha],
\qquad
\operatorname{disc}(K)=49.
\tag{6.15}
$$

The Minkowski bound is $14/9<2$, so $K$ has class number one. The following
short unit-index certificate determines all units. The three real roots of
the polynomial of $\alpha$ lie in width-$10^{-9}$ rational intervals
centered at

$$
-1.801937736,
\qquad -0.445041868,
\qquad 1.246979604.
\tag{6.16}
$$

The logarithmic rows of $\alpha$ and $\alpha+1$ have regulator in
$(0.5254,0.5256)$. A representative of a missing unit coset would have
coordinates $a+b\alpha+c\alpha^2$ satisfying

$$
|a|<2.431,
\qquad |b|<1.507,
\qquad |c|<1.564.
\tag{6.17}
$$

The exact norm form is

$$
\begin{aligned}
N(a+b\alpha+c\alpha^2)={}&a^3-a^2b+5a^2c-2ab^2-abc+6ac^2\\
&+b^3-b^2c-2bc^2+c^3.
\end{aligned}
\tag{6.18}
$$

Checking the $45$ integral triples allowed by (6.17), with the embedding
bounds certified by interval arithmetic, leaves only $\pm1$. Hence

$$
\mathcal O_K^\times=\langle-1,\alpha,\alpha+1\rangle.
\tag{6.19}
$$

Furthermore,

$$
N(2-\alpha)=7,
\qquad
\frac7{(2-\alpha)^3}=\alpha^{-2}(\alpha+1)^4,
\tag{6.20}
$$

so $(7)=(2-\alpha)^3$, while $2$ is inert. The identities

$$
\theta=\frac{\alpha^3}{\alpha+1},
\qquad
1-\theta=\frac{\alpha^2}{(\alpha+1)^3}
\tag{6.21}
$$

complete the prime and unit ledger for $S=\{2,7,\infty\}$.

For a divisor represented by $[u,v]$, the $x-T$ descent map is

$$
\delta([u,v])=
\bigl((-1)^{\deg u}u(0),
(-1)^{\deg u}u(1),
(-1)^{\deg u}u(\theta)\bigr).
\tag{6.22}
$$

The derivative rule at a branch point gives

$$
e_0:=\delta(T_0)=(-1,-1,-\theta),
\qquad
e_1:=\delta(T_1)=(1,-1,1-\theta).
\tag{6.23}
$$

Using (6.19)--(6.21), the complete $S$-unit norm kernel has basis

$$
\begin{aligned}
e_0,e_1,\qquad
h_1&=(-1,1,-1),&h_2&=(1,-1,-1),\\
h_3&=(2,1,2),&h_4&=(1,2,2),\\
h_5&=(7,1,2-\alpha),&h_6&=(1,7,2-\alpha).
\end{aligned}
\tag{6.24}
$$

For verification, the ambient squareclass space has eleven generators: the
classes $-1,2,7$ in each rational factor and the classes
$-1,\alpha,\alpha+1,2,2-\alpha$ in $K$. The product-norm map to
$\langle-1,2,7\rangle$ has rank three. The eight vectors in (6.24) are
independent and lie in its kernel, so they are the entire kernel. In that
ordered ambient basis, their coordinate matrix is

$$
B_S=
\begin{pmatrix}
1&0&1&0&0&0&0&0\\
0&0&0&0&1&0&0&0\\
0&0&0&0&0&0&1&0\\
1&1&0&1&0&0&0&0\\
0&0&0&0&0&1&0&0\\
0&0&0&0&0&0&0&1\\
1&0&1&1&0&0&0&0\\
1&0&0&0&0&0&0&0\\
1&1&0&0&0&0&0&0\\
0&0&0&0&1&1&0&0\\
0&0&0&0&0&0&1&1
\end{pmatrix}.
\tag{6.24a}
$$

Row reduction makes the independence and norm-kernel dimension directly
checkable.

At finite primes outside $S$, the curve has good odd reduction and every
class in this $S$-unit space is unramified. The local Kummer image is the
unramified subgroup, so only the real, $2$-adic, and $7$-adic conditions can
cut the global space.

All five finite branch points are real. The real Kummer image has dimension
two, generated by $e_0,e_1$, and the real local condition cuts (6.24) to

$$
\langle e_0,e_1,h_3,h_4,h_5,h_6\rangle.
\tag{6.25}
$$

At $2$, $K_2/\mathbf Q_2$ is the unramified cubic extension. Squareclasses
are decided modulo $8\mathcal O_{K_2}$. Exact multiplication in the
$512$-element residue ring gives $448$ units and $28$ unit squares. In the
power basis $1,\alpha,\alpha^2$, the four classes

$$
3\alpha^2,
\quad5\alpha^2,
\quad\alpha,
\quad\alpha+\alpha^2
\tag{6.26}
$$

generate the unit squareclass group; their sixteen products represent all
unit squareclasses. Combining them with the usual
$(-1,2,5)$ bases in the two rational factors gives the exact intersection

$$
V_S\cap\operatorname{im}\delta_2
=\langle e_0,e_1,h_1+h_5,h_2+h_6\rangle.
\tag{6.27}
$$

For a complete residue certificate, write the local coordinate space as

$$
(-1,2,5)_0\mid(-1,2,5)_1
\mid(2,3\alpha^2,5\alpha^2,\alpha,\alpha+\alpha^2)_K.
$$

The global basis rows and the two local point rows $d_x=(x,x-1,x-\theta)$
are then

$$
\begin{array}{c|c|c|c}
&\mathbf Q_{2,0}&\mathbf Q_{2,1}&K_2\\ \hline
e_0&100&100&01101\\
e_1&000&100&00011\\
h_1&100&000&01100\\
h_2&000&100&01100\\
h_3&010&000&10000\\
h_4&000&010&10000\\
h_5&100&000&01100\\
h_6&000&100&01100\\ \hline
d_{-4}&100&101&01001\\
d_{13}&001&101&00011.
\end{array}
\tag{6.27a}
$$

Binary row reduction of this table gives (6.27).

Completeness of this local image is certified by two genuine local points.
Indeed

$$
f(-4)=4(-1055),
\qquad
f(13)=4(35529),
\tag{6.28}
$$

and both parenthesized units are $1$ modulo $8$. The two resulting Kummer
classes, together with $e_0,e_1$, are independent. On the other hand

$$
\dim_{\mathbf F_2}J_7(\mathbf Q_2)/2J_7(\mathbf Q_2)
=2+\dim_{\mathbf F_2}J_7(\mathbf Q_2)[2]=4,
\tag{6.29}
$$

so these four classes are the complete local image, not merely a lower
bound.

At $7$, the three branch-algebra factors remain
$\mathbf Q_7,\mathbf Q_7,K_7$, with $K_7/\mathbf Q_7$ totally ramified of
degree three. Thus

$$
J_7(\mathbf Q_7)[2]=\langle T_0,T_1\rangle,
\qquad
\dim J_7(\mathbf Q_7)/2J_7(\mathbf Q_7)=2.
\tag{6.30}
$$

Indeed, multiplication by $2$ is an automorphism on a pro-$7$ open subgroup,
and on the finite quotient its kernel and cokernel have the same order. The
visible classes therefore give the full local image, so $7$ makes no additional
cut. Equivalently, in the ordered basis (6.24), the complete obstruction
matrix is

$$
\begin{array}{c|cc|cccccc}
&e_0&e_1&h_1&h_2&h_3&h_4&h_5&h_6\\ \hline
\mathbf R&0&0&1&0&0&0&0&0\\
\mathbf R&0&0&0&1&0&0&0&0\\
\mathbf Q_2&0&0&0&0&1&0&0&0\\
\mathbf Q_2&0&0&0&0&0&1&0&0\\
\mathbf Q_2&0&0&1&0&0&0&1&0\\
\mathbf Q_2&0&0&0&1&0&0&0&1.
\end{array}
\tag{6.31}
$$

Its kernel is exactly $\langle e_0,e_1\rangle$. This is an odd-degree true
descent, so

$$
\operatorname{Sel}_2(J_7/\mathbf Q)=
\langle\delta(T_0),\delta(T_1)\rangle,
\qquad
\operatorname{rank}J_7(\mathbf Q)=0.
\tag{6.32}
$$

Direct point counting gives

$$
\begin{array}{c|cc|c}
q&\#C_7(\mathbf F_q)&\#C_7(\mathbf F_{q^2})
&\#J_7(\mathbf F_q)\\ \hline
3&5&5&12\\
5&9&25&48.
\end{array}
\tag{6.33}
$$

Prime by prime, using the other reduction when the torsion prime equals the
residue characteristic, rational torsion has order dividing $12$. The subgroup generated
by $A,T_0,T_1$ already has order $3\cdot2\cdot2=12$, so

$$
\boxed{
J_7(\mathbf Q)=
\langle A\rangle\oplus\langle T_0\rangle\oplus\langle T_1\rangle
\simeq\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2.}
\tag{6.34}
$$

### 6.4 The Abel-image calculation

The abstract group (6.34) does not yet determine the rational points of the
curve. Using the composition rule of Section 5.5, exact Cantor addition
gives all twelve unique reduced pairs:

$$
\begin{array}{c|c|c}
(a,b,c)&u&v\\ \hline
(0,0,0)&1&0\\
(0,0,1)&t-1&0\\
(0,1,0)&t&0\\
(0,1,1)&t^2-t&0\\
(1,0,0)&t^2-t+1&1-3t\\
(1,0,1)&t^2-11t+9&15-17t\\
(1,1,0)&t^2-9t-1&1+11t\\
(1,1,1)&t^2-\frac79t-\frac19&\frac5{27}-\frac1{27}t\\
(2,0,0)&t^2-t+1&-1+3t\\
(2,0,1)&t^2-11t+9&-15+17t\\
(2,1,0)&t^2-9t-1&-1-11t\\
(2,1,1)&t^2-\frac79t-\frac19&-\frac5{27}+\frac1{27}t.
\end{array}
\tag{6.35}
$$

The row $(a,b,c)$ represents $aA+bT_0+cT_1$. Every row is checked by
$u\mid f-v^2$ and the inequalities (6.10); the group relations advance
through all twelve rows, and uniqueness makes them distinct and exhaustive.

For a pointed monic quintic, the Abel image consists exactly of the identity
and reduced pairs with $\deg u=1$:

$$
(r,s)\longmapsto[t-r,s],
\qquad
\infty\longmapsto[1,0].
\tag{6.36}
$$

Inspection of (6.35) leaves only

$$
[1,0],
\qquad[t,0],
\qquad[t-1,0].
$$

These are the classes of $\infty,(0,0),(1,0)$. Abel injectivity proves
(6.9). All three are boundary or degenerate parameters, and therefore

$$
\boxed{
\mathbf Z/2\mathbf Z\oplus\mathbf Z/14\mathbf Z
\not\subset E(\mathbf Q)
\quad\text{for every elliptic curve }E/\mathbf Q.}
\tag{6.37}
$$

This is the only mixed-torsion theorem needed below.

## 7. The semistable full-two criterion

### 7.1 The focused torsion input

The two preceding chapters established exactly the following pair of facts:

$$
E(\mathbf Q)[p]=0
\qquad(p\ge11\text{ prime}),
\tag{7.1}
$$

and

$$
\mathbf Z/2\mathbf Z\oplus\mathbf Z/14\mathbf Z
\not\subset E(\mathbf Q).
\tag{7.2}
$$

Nothing about rational torsion of order $2,3,$ or $5$ is required, and no
list of rational isogeny degrees is being used. Equation (7.1) is the
point-level exclusion in the large-prime branch; equation (7.2) is the
full-two correction at the surviving point-level prime $7$.

### 7.2 Irreducibility in the full-two isogeny class

Let $E/\mathbf Q$ be semistable with full rational two-torsion, let
$p\ge7$ be prime, and suppose $E[p]$ has a stable line. By (2.2), it gives a
rational isogeny

$$
\varphi:E\longrightarrow E'=E/C.
$$

The semistable isogeny theorem (4.4) gives a rational point of order $p$ on
$E$ or on $E'$. Since $p$ is odd, (2.8) transports full rational
two-torsion across $\varphi$.

If $p\ge11$, the rational point contradicts (7.1). If $p=7$, the curve on
which the point occurs contains the group in (7.2), again a contradiction.
This proves

$$
\boxed{
E/\mathbf Q\text{ semistable},\quad
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
\quad p\ge7
\Longrightarrow E[p]\text{ is irreducible over }\mathbf F_p.}
\tag{7.3}
$$

The endpoint $7$ is explicit rather than hidden in a large-prime estimate.
The next chapter checks the two hypotheses of (7.3) and the stronger local
ramification data directly for the Frey curve.

## 8. The Frey curve and its local ledger

### 8.1 Normalization, two-torsion, and invariants

Let $p\ge7$ be prime and suppose

$$
a^p+b^p=c^p
\tag{8.1}
$$

is a primitive nonzero integer solution. Pairwise coprimality follows from
primitivity. Exactly one of $a,b,c$ is even. By permuting the signed
three-term equation and changing all signs if necessary, arrange

$$
a\text{ even},
\qquad b,c\text{ odd},
\qquad b\equiv c\equiv1\pmod4.
\tag{8.2}
$$

Put

$$
A=a^p,
\qquad B=b^p,
\qquad C=c^p=A+B,
$$

and define

$$
E=E_{a,b,p}:\quad y^2=x(x-A)(x+B).
\tag{8.3}
$$

Its nonzero two-torsion points are

$$
(0,0),
\qquad(A,0),
\qquad(-B,0),
\tag{8.4}
$$

so

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
\tag{8.5}
$$

Expanding the cubic and applying the integral invariant formulas gives

$$
\begin{aligned}
c_4&=16(A^2+AB+B^2),\\
c_6&=-32(B-A)(2A^2+5AB+2B^2),\\
\Delta&=16A^2B^2C^2=2^4(abc)^{2p},\\
j&=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.
\end{aligned}
\tag{8.6}
$$

The factorization of $\Delta$ is the square of the product of the three
root differences, with the standard factor $16$. It makes all odd local
calculations immediate; the displayed equation still has to be minimized
at $2$.

### 8.2 Odd primes

Let $q$ be odd. If $q\nmid abc$, (8.6) has unit discriminant and $E$ has
good reduction. If $q\mid a$, then $B,C$ are units and

$$
A^2+AB+B^2\equiv B^2\not\equiv0\pmod q.
$$

Thus $c_4$ is a unit, the equation is minimal, and the reduction is
multiplicative. The same root-difference argument applies when $q$ divides
$b$ or $c$. Therefore

$$
v_q(\Delta_{\min})=
\begin{cases}
2p\,v_q(a),&q\mid a,\\
2p\,v_q(b),&q\mid b,\\
2p\,v_q(c),&q\mid c.
\end{cases}
\tag{8.7}
$$

In particular, $E$ is semistable at every odd prime and every odd
multiplicative discriminant exponent is divisible by $p$.

### 8.3 The minimal equation at two

The equation (8.3) is not minimal at $2$. From (8.2),

$$
v_2(A)=p\,v_2(a)\ge7,
\qquad B-A\equiv1\pmod4.
\tag{8.8}
$$

Make the integral change of variables

$$
x=4x',
\qquad
y=8y'+4x'.
\tag{8.9}
$$

After division by $64$, the equation becomes

$$
y'^2+x'y'=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'.
\tag{8.10}
$$

Both coefficients are integral. Its invariants are

$$
c_{4,\min}=A^2+AB+B^2,
\qquad
\Delta_{\min}=2^{-8}A^2B^2C^2.
\tag{8.11}
$$

The first is odd, so (8.10) is minimal and has multiplicative reduction.
The exact exponent is

$$
m_2:=v_2(\Delta_{\min})=2p\,v_2(a)-8>0.
\tag{8.12}
$$

The subtraction of $8$ records the admissible dyadic scaling and cannot be
read from the raw equation (8.3). A tangent-cone calculation in (8.10) also
gives the splitting sign

$$
\varepsilon_2=
\begin{cases}
+1,&b\equiv1\pmod8\quad\text{(split)},\\
-1,&b\equiv5\pmod8\quad\text{(nonsplit)}.
\end{cases}
\tag{8.13}
$$

Combining Sections 8.2 and 8.3 proves

$$
\boxed{E/\mathbf Q\text{ is semistable}.}
\tag{8.14}
$$

### 8.4 Residual inertia and the exact conductor

At a multiplicative prime $q\ne p$, the Tate criterion (3.5) and (8.7)
give

$$
\overline\rho_{E,p}|_{I_q}=1
\qquad(q\mid abc,\ q\ne2,p).
\tag{8.15}
$$

At $2$, equation (8.12) gives

$$
m_2\equiv-8\not\equiv0\pmod p.
\tag{8.16}
$$

Let
$\overline t_p:I_2\twoheadrightarrow\mathbf F_p$ be the $p$-primary
tame character. A Tate basis gives the complete inertial equation

$$
\overline\rho_{E,p}(\sigma)
=1+\overline t_p(\sigma)\overline N,
\qquad
\overline N=
\begin{pmatrix}0&\overline m_2\\0&0\end{pmatrix},
\qquad
\overline N^2=0,
\quad\overline N\ne0.
\tag{8.17}
$$

Wild inertia acts trivially, and $\overline t_p$ is onto. Thus the inertial
image is cyclic of order $p$, with unique fixed line

$$
L_2=\ker\overline N=\operatorname{im}\overline N.
\tag{8.18}
$$

If $\phi_2$ is arithmetic Frobenius, an upper-unipotent basis change removes
the off-diagonal Frobenius entry because $2-1$ is a unit modulo $p$. Then

$$
\overline\rho_{E,p}(\phi_2)=
\varepsilon_2
\begin{pmatrix}2&0\\0&1\end{pmatrix},
\qquad
\overline\rho_{E,p}(\phi_2)\overline N
\overline\rho_{E,p}(\phi_2)^{-1}=2\overline N.
\tag{8.19}
$$

The fixed space has codimension one and the Swan conductor is zero, so

$$
a_2(\overline\rho_{E,p})=1.
\tag{8.20}
$$

Every prime $q\ne2,p$ is either good or covered by (8.15). Consequently

$$
\overline\rho_{E,p}\text{ is unramified outside }\{2,p\},
\tag{8.21}
$$

and its exact prime-to-$p$ Artin conductor is

$$
\boxed{N(\overline\rho_{E,p})=2.}
\tag{8.22}
$$

### 8.5 The coefficient-prime finite-flat condition

If $p\nmid abc$, the curve has good reduction at $p$, so $E[p]$ is the
generic fiber of the finite-flat group scheme $\mathcal E[p]$ over
$\mathbf Z_p$. If $p\mid abc$, the reduction is multiplicative and (8.7)
gives

$$
p\mid v_p(\Delta_{\min}).
\tag{8.23}
$$

For the Tate curve, the extension class of
$0\to\mu_p\to E[p]\to\mathbf Z/p\to0$ is the Kummer class of the Tate
parameter. Its valuation is $v_p(\Delta_{\min})$. Condition (8.23) allows a
$p$th power of a uniformizer to be removed, leaving a unit Kummer class.
The finite-flat Kummer sequence over $\mathbf Z_p$ then extends the
representation. Nonsplit multiplicative reduction becomes split over the
unramified quadratic extension; the same finite-flat model descends, so no
splitting case is omitted. Hence in both cases

$$
\boxed{E[p]\text{ is finite flat at }p.}
\tag{8.24}
$$

Finally, the Weil pairing gives

$$
\det\overline\rho_{E,p}=\overline\chi_p.
\tag{8.25}
$$

Complex conjugation has determinant $-1$, so the representation is odd.
No assertion of absolute irreducibility or of full residual image has been
made.

## 9. Frey irreducibility

### 9.1 The contradiction and the endpoint seven

Suppose that $\overline\rho_{E,p}$ is reducible. By (2.2), the Frey curve
admits a rational cyclic $p$-isogeny

$$
\varphi:E\longrightarrow E'=E/C.
\tag{9.1}
$$

Semistability (8.14) and global reciprocity give

$$
E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.
\tag{9.2}
$$

Both curves have full rational two-torsion by (8.5) and (2.8). For
$p\ge11$, (9.2) contradicts the focused prime-order theorem (5.1). For
$p=7$, it would give

$$
\mathbf Z/2\mathbf Z\oplus\mathbf Z/14\mathbf Z
\subset E(\mathbf Q)
\quad\text{or}\quad
\mathbf Z/2\mathbf Z\oplus\mathbf Z/14\mathbf Z
\subset E'(\mathbf Q),
$$

contradicting (6.37). Thus every prime in the required range, including the
endpoint $7$, is covered.

### 9.2 Exact dependency and hypothesis ledger

The direct earlier-book interfaces are the following.

| Earlier foundation | Result used here | Exact boundary |
|---|---|---|
| Book 3 | tame inertia and exact Artin and Swan conductor formulas | no unrelated ramification-filtration calculation |
| Books 4 and 6 | Minkowski and unit lattices; global reciprocity and narrow ray classes | only the explicit fields here and the trivial narrow class group of $\mathbf Q$ |
| Book 9 | Riemann--Roch reduction and injectivity of a pointed Abel map | no later genus-two point classification |
| Books 37, 42, and 43 | Jacobians; Kummer descent and Selmer groups; finite generation | no precomputed $J_{13}(\mathbf Q)$ or $J_7(\mathbf Q)$ |
| Book 38 | quotients by finite subgroup schemes and odd-isogeny functoriality | only the given isogeny and its two-torsion map |
| Books 46--48 | schematic closure, connected--étale structure, Cartier duality, finite-flat representations | no potentially-good signature table |
| Book 56 | the Oort--Tate order-$p$ classification over unramified mixed-characteristic DVRs | only the étale and multiplicative endpoints over $\mathbf Z_p$ |
| Books 49--51 | minimal models, Tate curves, torsion representations, Weil pairing, and conductor criteria | no Frey irreducibility theorem |
| Book 139 | stable-line/isogeny and point-level modular dictionaries | no rational-point classification |
| Book 147 | oriented formal immersion for $p\ge17$, the level-$11$ calculation, and the reversible $X_1(13)$ model with its six rational cusps | no level-$13$ rational-point or mixed-$7$ conclusion |

Book 147 carries the preceding Eisenstein-quotient construction through its
own earlier dependencies; this book uses its formal-immersion and
level-$11$ conclusions, together with its reversible level-$13$ model, as
interfaces. The two exceptional genus-two rational-point conclusions are
proved in Chapters 5 and 6 from the earlier divisor, Jacobian, and Kummer
foundations. No result from a later-numbered book is used.

The exceptional hypotheses have also been kept visible:

| Issue | Exact treatment |
|---|---|
| stable subgroup versus rational generator | the character $\lambda$ in (2.3) |
| dual kernel | $\mu=\overline\chi_p\lambda^{-1}$ |
| multiplicative $q\ne p$ | diagonal characters unramified; extension class tested by (3.5) |
| coefficient prime | finite-flat order-$p$ closure over unramified $\mathbf Z_p$, or the Tate direction |
| global unramifiedness | narrow class group of $\mathbf Q$, including the real place |
| rational prime order $13$ | true-to-fake kernel and two independent $2$-adic obstruction rows |
| full two-torsion with order $7$ | only the necessary square-discriminant implication, followed by the complete $C_7$ calculation |
| even-degree Abel map | $j(P)+j(\iota P)=T$ |
| Frey prime $2$ | minimal equation (8.10), with discriminant exponent reduced by $8$ |
| conductor | diagonal character conductors distinguished from the ramified extension class |

### 9.3 Final theorem package

The results can now be passed forward in their exact forms.

**Frey isogeny-character theorem.** If a semistable elliptic curve
$E/\mathbf Q$ has a rational cyclic $p$-isogeny for $p\ge5$, its two
diagonal characters are unramified away from $p$. At $p$ their inertial
restrictions are $1$ and $\overline\chi_p$, in one order. Global reciprocity
therefore makes one character trivial, so $E$ or the quotient curve has a
rational point of order $p$.

**Semistable full-two theorem.** If $E/\mathbf Q$ is semistable and has full
rational two-torsion, then

$$
E[p]\text{ is irreducible over }\mathbf F_p
\qquad(p\ge7\text{ prime}).
\tag{9.3}
$$

**Frey residual theorem.** Let $p\ge7$ be prime and let $(a,b,c)$ be a
primitive nonzero solution of $a^p+b^p=c^p$, normalized by (8.2). For

$$
E_{a,b,p}:y^2=x(x-a^p)(x+b^p),
$$

one has

$$
\boxed{
\overline\rho_{E_{a,b,p},p}:G_{\mathbf Q}
\longrightarrow\operatorname{GL}_2(\mathbf F_p)
\text{ is irreducible}.}
\tag{9.4}
$$

Moreover,

$$
\det\overline\rho_{E,p}=\overline\chi_p,
\qquad
N(\overline\rho_{E,p})=2,
\tag{9.5}
$$

$E[p]$ is finite flat at $p$, and

$$
v_q(\Delta_{\min})=2p\,v_q(abc)
\qquad(q\mid abc,\ q\text{ odd}),
\tag{9.6}
$$

$$
v_2(\Delta_{\min})=2p\,v_2(a)-8.
\tag{9.7}
$$

For odd $q\mid abc$ with $q\ne p$, the residual representation is
unramified. At $2$ its inertia image is cyclic of order $p$, its unique
fixed line is the monodromy line (8.18), and its Artin conductor exponent is
one. These statements include every local case used in the later Frey
argument.

### 9.4 Conclusion

The decisive object is not a list of rational isogeny degrees but the
character on a stable line. Semistable reduction makes that character and
its dual unramified away from the coefficient prime. Finite-flat geometry
at the coefficient prime leaves one étale and one cyclotomic direction.
Global reciprocity over $\mathbf Q$ then turns the unramified direction into
a rational generator on one side of the isogeny.

The Frey curve supplies the extra rigidity needed at the remaining small
prime. Its three rational roots display full two-torsion, and odd isogenies
transport that entire group scheme. The oriented point-level theorem
excludes prime order at least eleven; the corrected level-$13$ descent
closes its genuine exceptional level; and the mixed-$7$ curve has only
three degenerate rational points. Reducibility is therefore impossible for
every $p\ge7$.

At the same time, the minimal Frey equation records more than
irreducibility. All odd multiplicative discriminant exponents disappear
modulo $p$, while the corrected dyadic exponent remains $-8$ modulo $p$.
Thus residual ramification is concentrated exactly at $2$ and the
coefficient prime, with prime-to-$p$ conductor $2$. This is the coherent
isogeny-character and local-representation package required by the next
stage of the Fermat argument.
