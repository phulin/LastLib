# Rational Isogenies of Prime Degree

## Contents

1. [The problem and its exact dictionary](#1-the-problem-and-its-exact-dictionary)
   - [The classification theorem](#11-the-classification-theorem)
   - [Lines, subgroup schemes, and isogenies](#12-lines-subgroup-schemes-and-isogenies)
   - [Kernel characters and duality](#13-kernel-characters-and-duality)
   - [Coarse points and exceptional automorphisms](#14-coarse-points-and-exceptional-automorphisms)
2. [The local isogeny-character theorem](#2-the-local-isogeny-character-theorem)
   - [Why a twelfth power occurs](#21-why-a-twelfth-power-occurs)
   - [Places away from the coefficient prime](#22-places-away-from-the-coefficient-prime)
   - [Finite-flat analysis at the coefficient prime](#23-finite-flat-analysis-at-the-coefficient-prime)
   - [The signature table and congruence restrictions](#24-the-signature-table-and-congruence-restrictions)
   - [Semistable and potentially multiplicative sharpenings](#25-semistable-and-potentially-multiplicative-sharpenings)
3. [Stable specialization and global reciprocity](#3-stable-specialization-and-global-reciprocity)
   - [Potentially good reduction at an auxiliary prime](#31-potentially-good-reduction-at-an-auxiliary-prime)
   - [The exceptional special fibers](#32-the-exceptional-special-fibers)
   - [The stable-specialization trace lemma](#33-the-stable-specialization-trace-lemma)
   - [From local inertia to a global signature](#34-from-local-inertia-to-a-global-signature)
4. [Odd cusp rigidity supplies three interior primes](#4-odd-cusp-rigidity-supplies-three-interior-primes)
   - [Cuspidal reduction and negative valuation](#41-cuspidal-reduction-and-negative-valuation)
   - [The exact interface from Book 69](#42-the-exact-interface-from-book-69)
   - [The three fixed auxiliary primes](#43-the-three-fixed-auxiliary-primes)
5. [The exact unbalanced-signature sieve](#5-the-exact-unbalanced-signature-sieve)
   - [Resultants and the Hasse interval](#51-resultants-and-the-hasse-interval)
   - [A recurrence certificate for every resultant](#52-a-recurrence-certificate-for-every-resultant)
   - [The complete factorization certificate](#53-the-complete-factorization-certificate)
   - [Eliminating the cubic signatures](#54-eliminating-the-cubic-signatures)
   - [The apparent factor $31$](#55-the-apparent-factor-31)
6. [The balanced signature](#6-the-balanced-signature)
   - [Why the $j$-invariant is integral](#61-why-the-j-invariant-is-integral)
   - [The balanced class-field theorem](#62-the-balanced-class-field-theorem)
   - [How the class group enters](#63-how-the-class-group-enters)
7. [The independent class-number-one theorem](#7-the-independent-class-number-one-theorem)
   - [The theorem and its proof architecture](#71-the-theorem-and-its-proof-architecture)
   - [Intersection with the balanced branch](#72-intersection-with-the-balanced-branch)
8. [The complete level-$37$ certificate](#8-the-complete-level-37-certificate)
   - [The genus-two model and its involutions](#81-the-genus-two-model-and-its-involutions)
   - [The two elliptic quotients](#82-the-two-elliptic-quotients)
   - [The rank-zero Mordell--Weil certificate](#83-the-rank-zero-mordell--weil-certificate)
   - [Modular symbols, newforms, and the Sturm bound](#84-modular-symbols-newforms-and-the-sturm-bound)
   - [The three fibers and all rational points](#85-the-three-fibers-and-all-rational-points)
   - [Cusps and the two $j$-values](#86-cusps-and-the-two-j-values)
9. [Existence at the genus-zero and level-$17$ primes](#9-existence-at-the-genus-zero-and-level-17-primes)
   - [Certified Hauptmodul formulas](#91-certified-hauptmodul-formulas)
   - [A noncuspidal specialization at each genus-zero level](#92-a-noncuspidal-specialization-at-each-genus-zero-level)
   - [The level-$17$ modular point](#93-the-level-17-modular-point)
10. [CM existence and the exceptional coarse fibers](#10-cm-existence-and-the-exceptional-coarse-fibers)
    - [Ramified CM kernels](#101-ramified-cm-kernels)
    - [The five required CM degrees](#102-the-five-required-cm-degrees)
    - [Direct treatment of $j=0$ and $j=1728$](#103-direct-treatment-of-j0-and-j1728)
11. [The prime-isogeny classification](#11-the-prime-isogeny-classification)
    - [Elimination](#111-elimination)
    - [Existence](#112-existence)
    - [Mechanism and dependency ledger](#113-mechanism-and-dependency-ledger)
12. [The independent prime-torsion theorem](#12-the-independent-prime-torsion-theorem)
    - [The exact independent theorem](#121-the-exact-independent-theorem)
    - [The oriented $X_1(p)$ proof architecture](#122-the-oriented-x_1p-proof-architecture)
    - [Tate normal form and the two mixed-torsion curves](#123-tate-normal-form-and-the-two-mixed-torsion-curves)
    - [The elliptic certificate for $C_5$](#124-the-elliptic-certificate-for-c_5)
    - [The genus-two certificate for $C_7$](#125-the-genus-two-certificate-for-c_7)
13. [Semistable rational isogenies](#13-semistable-rational-isogenies)
    - [An everywhere-unramified diagonal character](#131-an-everywhere-unramified-diagonal-character)
    - [Rational torsion on one side of the isogeny](#132-rational-torsion-on-one-side-of-the-isogeny)
    - [Odd isogenies and full two-torsion](#133-odd-isogenies-and-full-two-torsion)
14. [The Frey curve](#14-the-frey-curve)
    - [Normalization and invariants](#141-normalization-and-invariants)
    - [Odd bad primes](#142-odd-bad-primes)
    - [The minimal model at two](#143-the-minimal-model-at-two)
    - [Residual inertia](#144-residual-inertia)
15. [Frey irreducibility](#15-frey-irreducibility)
    - [The contradiction](#151-the-contradiction)
    - [The exponents five and seven](#152-the-exponents-five-and-seven)
    - [All larger prime exponents](#153-all-larger-prime-exponents)
16. [Audit and final theorem package](#16-audit-and-final-theorem-package)
    - [Imported infrastructure](#161-imported-infrastructure)
    - [Exact finite certificates](#162-exact-finite-certificates)
    - [Logical safeguards](#163-logical-safeguards)
    - [Final theorems](#164-final-theorems)
    - [Conclusion](#165-conclusion)

## 1. The problem and its exact dictionary

### 1.1 The classification theorem

A cyclic isogeny of prime degree is one of the simplest maps between elliptic curves, but its existence is controlled simultaneously by local reduction, finite-flat geometry, global reciprocity, modular curves, and class groups. None of these viewpoints by itself explains the answer. The purpose of this book is to make their meeting point explicit and to keep the numerical eliminations visible.

The theorem to be proved is

$$
\boxed{
p\text{ is the degree of a rational cyclic isogeny over }\mathbf Q
\Longleftrightarrow
p\in\{2,3,5,7,11,13,17,19,37,43,67,163\}.}
\tag{1.1}
$$

Every degree on the right will be constructed. The elimination of every other prime will not be imported under another name. For $p>19$ it will come from five possible local signatures, an exact resultant calculation at $5,7,11$, a structural class-field theorem in the one balanced signature, and the independent class-number-one theorem. The isolated endpoint $37$ will be verified on an explicit genus-two model.

The final application is stronger than membership in (1.1). If a Frey curve attached to a putative Fermat solution had reducible $p$-torsion, semistability would force rational $p$-torsion on one of two isogenous curves. The independent prime-torsion theorem eliminates $p\ge11$. Full rational $2$-torsion persists across an odd isogeny, and the explicit curves $C_5$ and $C_7$ eliminate the remaining primes $5$ and $7$. Thus the classification and the Frey argument share local theory but have different last steps.

Throughout, $p$ denotes the degree of the isogeny and the coefficient characteristic of the residual representation. Auxiliary rational primes are denoted $q$ or $r$. Arithmetic Frobenius is used, so

$$
\chi_p(\operatorname{Frob}_r)=r\pmod p
\tag{1.2}
$$

for $r\ne p$.

### 1.2 Lines, subgroup schemes, and isogenies

Let $E/\mathbf Q$ be an elliptic curve and let $p$ be prime. In characteristic zero, $E[p]$ is finite étale of rank $p^2$, and

$$
E[p](\overline{\mathbf Q})\simeq\mathbf F_p^2.
$$

A one-dimensional subspace $L$ is stable under $G_{\mathbf Q}$ exactly when finite étale descent makes its $p$ geometric points the points of a subgroup scheme

$$
C\subset E[p]
$$

of rank $p$ over $\mathbf Q$. The quotient by a finite subgroup scheme exists, and therefore

$$
\varphi:E\longrightarrow E/C
\tag{1.3}
$$

is a separable isogeny of degree $p$. Conversely, the scheme-theoretic kernel of a rational degree-$p$ isogeny is such a stable cyclic subgroup. Consequently

$$
\boxed{
E[p]\text{ reducible over }\mathbf F_p
\Longleftrightarrow
C\subset E[p]\text{ rational cyclic of rank }p
\Longleftrightarrow
E\text{ admits a rational }p\text{-isogeny}.}
\tag{1.4}
$$

The qualification “over $\mathbf F_p$” matters. A line visible only after extending the coefficient field does not define a rank-$p$ subgroup over $\mathbf Q$.

The pair $(E,C)$ gives a noncuspidal rational object of the $\Gamma_0(p)$ moduli problem and hence a point

$$
x(E,C)\in Y_0(p)(\mathbf Q)\subset X_0(p)(\mathbf Q).
\tag{1.5}
$$

This direction has no coarse-descent issue: the elliptic curve and subgroup already exist. Most of the elimination starts with (1.5), so it never needs to infer an object from an arbitrary coarse point.

### 1.3 Kernel characters and duality

Choose $0\ne P\in C(\overline{\mathbf Q})$. Since $C$ is stable, there is a character

$$
\lambda:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times,
\qquad
\sigma P=\lambda(\sigma)P.
\tag{1.6}
$$

In a basis whose first vector is $P$, the residual representation is triangular:

$$
\overline\rho_{E,p}\sim
\begin{pmatrix}
\lambda&*\\
0&\chi_p\lambda^{-1}
\end{pmatrix}.
\tag{1.7}
$$

The determinant is cyclotomic by the Weil pairing. The second diagonal character is the kernel character of the dual isogeny

$$
\widehat\varphi:E/C\longrightarrow E.
$$

Thus duality replaces

$$
\lambda\quad\text{by}\quad\chi_p\lambda^{-1}.
\tag{1.8}
$$

A rational subgroup is not the same thing as a rational generator. The kernel has a nonzero rational point exactly when $\lambda=1$. This distinction is harmless for the modular curve $X_0(p)$, which remembers the subgroup, but decisive in the Frey argument, where rational torsion must be produced by an additional semistable theorem.

### 1.4 Coarse points and exceptional automorphisms

The reverse passage from a rational coarse point of $Y_0(p)$ to a pair over $\mathbf Q$ must retain the automorphism locus. If $j\ne0,1728$, choose a curve $E_0/\mathbf Q$ with the indicated $j$-invariant and transport a geometric subgroup to it. Coarse Galois invariance carries every conjugate subgroup back by an automorphism of $E_{0,\overline{\mathbf Q}}$. That automorphism is $\pm1$, and both signs preserve every unoriented cyclic subgroup. The subgroup is therefore itself Galois stable and descends.

At $j=0$ and $1728$, the geometric automorphism groups are larger, so this argument is unavailable. We will not assert blanket coarse descent there. Chapter 10 treats the twists

$$
y^2=x^3+d,
\qquad
y^2=x^3+dx
\tag{1.9}
$$

directly from their division polynomials. All rational points used for existence at $p\ge5$ have $j\ne0,1728$, except that the CM construction itself already supplies an actual stable subgroup and so needs no coarse descent.

## 2. The local isogeny-character theorem

### 2.1 Why a twelfth power occurs

The character $\lambda$ may ramify even when the cyclic subgroup is rational. The useful object is its twelfth power. The number $12$ is not chosen merely because elliptic curves have familiar automorphisms of orders $4$ and $6$; it is the output of a local classification that also includes connected finite-flat groups, fundamental characters, and wild inertia at $2$ and $3$.

We use the following local theorem as established infrastructure.

**Local isogeny-character theorem.** Let $p\ge5$, let $E/\mathbf Q$ admit a rational cyclic subgroup $C\subset E[p]$, and let $\lambda$ be its kernel character. At the coefficient place $p$ one has

$$
\lambda^{12}|_{I_p}=\chi_p^s|_{I_p}
\tag{2.1}
$$

for some

$$
s\in\{0,4,6,8,12\}.
\tag{2.2}
$$

If $E$ is semistable at $p$, then the sharper conclusion is

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\chi_p.
\tag{2.3}
$$

If $E$ is potentially multiplicative at $p$, only $s=0,12$ occur. For $p>13$, the cases $s=4,8$ require

$$
p\equiv2\pmod3,
\tag{2.4}
$$

and the case $s=6$ requires

$$
p\equiv3\pmod4.
\tag{2.5}
$$

At every prime $q\ne p$ one has

$$
\lambda^{12}|_{I_q}=1.
\tag{2.6}
$$

No conclusion of this theorem is a list of rational isogeny degrees. It is a local statement about a line which is already known to exist.

The five values can be audited as follows.  Put

$$
\omega=\chi_p|_{I_p}:I_p\longrightarrow\mathbf F_p^\times.
\tag{2.6a}
$$

If a minimal totally ramified extension of semistability has tame degree $e$,
normalize its tame fundamental character by

$$
\omega|_{I_L}=\omega_L^e.
\tag{2.6b}
$$

For potentially good reduction in residue characteristic at least five one has
$e=2,3,4$, or $6$.  Raynaud's rank-$p$ classification assigns to the finite-flat
closure of the line an integer $a$, $0\le a\le e$.  In the niveau-two case the
two characters of the ambient $p$-torsion, with
$\omega_2^{p+1}=\omega_L$, have exponents

$$
a+p(e-a),\qquad (e-a)+pa.
\tag{2.6c}
$$

An $\mathbf F_p$-line in this niveau-two representation can occur only when the
two conjugate characters coincide on that line; the half-weight descent check
is given just below the table.  In the ordinary case, connected--étale duality
interchanges $a$ and $e-a$, and the descent automorphism supplies the remaining
intermediate weights.  Combining the two cases and extending across the
finite-flat model leaves exactly the following rows.

| stable type over the semistability field | $e$ | allowed $a$ | $s=12a/e$ |
|---|---:|---|---|
| good ordinary, or a Tate direction | $1$ | $0,1$ | $0,12$ |
| quadratic potentially good descent | $2$ | $0,2$ | $0,12$ |
| cubic potentially good descent | $3$ | $0,1,2,3$ | $0,4,8,12$ |
| quartic potentially good descent | $4$ | $0,2,4$ | $0,6,12$ |
| sextic potentially good descent | $6$ | $0,2,4,6$ | $0,4,8,12$ |

The half-weight rows admit a direct descent check.  When $a=e/2$, the two
characters in (2.6c) coincide with $\omega_L^{e/2}$. If the descended line is
$\lambda|_{I_p}=\omega^k$, equation (2.6b) therefore requires

$$
ek\equiv e/2\pmod{p-1}.
$$

For $e=2$ or $6$ this is impossible: the left side is even modulo the even
integer $p-1$, whereas $e/2$ is odd.  For $e=4$ it is solvable exactly when
$\gcd(4,p-1)=2$, equivalently $p\equiv3\pmod4$.  Thus the quartic row is the
only descended half-weight row; in particular the table does not obtain the
congruence restriction by retaining spurious quadratic or sextic rows.

For every surviving row the equality on the original inertia group is

$$
\lambda^{12}|_{I_p}=\omega^{12a/e}.
\tag{2.6d}
$$

This proves that the list is $0,4,6,8,12$.  The congruence restrictions can be
read without conflating the niveau-two characters over the semistability field
with the descended line.  Since the latter is an $\mathbf F_p$-valued
character, its restriction to tame inertia has the form
$\lambda|_{I_p}=\omega^k$.  Equation (2.1) is therefore the literal congruence

$$
12k\equiv s\pmod{p-1},
\qquad\text{so}\qquad
\gcd(12,p-1)\mid s.
\tag{2.6e}
$$

For $s=4$ or $8$, this excludes $3\mid p-1$ and gives $p\equiv2\pmod3$.
For $s=6$, it excludes $4\mid p-1$ and gives $p\equiv3\pmod4$.  These are
(2.4) and (2.5), and they apply to every row yielding the stated exponent.
For $p>13$ this is the entire tame
calculation.  At $p=5,7,13$ the congruence collisions in the same coefficient-prime
finite-flat table are checked separately and add no new exponent.  These are
still coefficient-prime rows, not wild $q=2,3$ rows; the latter occur only
away from $p$ below.

### 2.2 Places away from the coefficient prime

The proof architecture of (2.6) begins with the stable reduction trichotomy.

If $E$ has good reduction at $q\ne p$, prime-to-$q$ torsion extends étale over $\mathbf Z_q$. Inertia acts trivially on all of $E[p]$, hence on $C$.

If $E$ is potentially multiplicative, Tate uniformization applies after a quadratic twist. Over the splitting field one has

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0.
\tag{2.7}
$$

Since $q\ne p$, both diagonal characters are unramified; twisting contributes only a quadratic character. Thus $\lambda^2$, and therefore $\lambda^{12}$, is unramified.

Suppose instead that $E$ is potentially good. After a finite extension it has a smooth model. The descent action on its special fiber is through the automorphism group of an elliptic curve. In tame residue characteristic the possible cyclic stabilizer orders on the tangent line are

$$
2,3,4,6.
\tag{2.8}
$$

Their least common multiple is $12$. In residue characteristics $2$ and $3$, the full automorphism group may be larger and wild, so (2.8) alone is not a proof. The wild tables separate the connected and étale parts of the $p$-torsion and then take the one-dimensional abelian characters occurring on a stable line. Their orders divide

$$
1,2,3,4,6,12.
\tag{2.9}
$$

More explicitly, the reduction and conductor ledger is

| place and stable type | inertia on a stable line | conductor information | twelfth power |
|---|---|---|---|
| $q\ge5$, good | trivial | exponent $0$ | trivial |
| $q\ge5$, potentially multiplicative | a quadratic splitting character | tame exponent at most $1$ | trivial |
| $q\ge5$, additive potentially good | cyclic of order $2,3,4$, or $6$ | tame exponent $1$ if nontrivial | trivial |
| $q=3$, potentially good | wild quotient of order $1$ or $3$, tame quotient of order dividing $4$ | may be wild | order divides $12$ |
| $q=2$, potentially good | wild abelian quotient of exponent dividing $4$, tame quotient of order dividing $3$ | may be wild | order divides $12$ |

In the last two rows the larger nonabelian automorphism group is not assigned
wholesale to the line: a character kills its commutator. At $3$ the surviving
wild and tame character orders divide $3$ and $4$; at $2$ their exponents divide
$4$ and $3$. Thus both one-dimensional images have exponent dividing $12$.
This proves (2.6) in the wild cases without falsely assigning them tame
conductor exponent one. The exact conductor conclusion used globally is only
that $\lambda^{12}$ has exponent zero at every $q\ne p$; $\lambda$ itself may
remain ramified.

### 2.3 Finite-flat analysis at the coefficient prime

At $p$, the cyclotomic character is ramified and the closure of $C$ need not be étale. One first passes to a minimal extension over which $E$ is semistable and takes the finite-flat schematic closure of $C$ inside the $p$-torsion of the resulting semiabelian model. Uniqueness of closure makes the descent action visible on this finite-flat group.

In the good ordinary case, the connected--étale sequence has rank-$p$ directions of multiplicative and étale type. On inertia their generic fibers have characters

$$
\chi_p\quad\text{and}\quad1.
\tag{2.10}
$$

The same two directions occur on a Tate curve. This gives (2.3) before any power is taken.

In the good supersingular case over an unramified base, inertia on $E[p]$ is
described by $\omega_2$ and $\omega_2^p$ and has no $\mathbf F_p$-stable line.
Over the ramified field of good reduction the correct finite-flat weights are
instead (2.6c). Applying the descent automorphism and requiring an
$\mathbf F_p$-line gives the displayed $(e,a)$ ledger. This calculation, not
the phrase “connected--étale,” is what produces the intermediate exponents.

The remaining coefficient-prime work is finite but indispensable. Since
$p\ge5$, potentially good descent at the coefficient place sorts the tame
automorphism orders $2,3,4,6$. The finite-flat connected--étale type rules out
the omitted value $a=1$ in the quadratic row, the values $a=1,3$ in the
quartic row, and the values $a=1,3,5$ in the sextic row:
their conjugate Raynaud characters do not descend to an $\mathbf F_p$-line.
The wild residue-characteristic $2$ and $3$ tables belong instead to the proof
of the away-from-$p$ assertion (2.6) in Section 2.2. The surviving
coefficient-prime exponents are exactly

$$
0,4,6,8,12.
$$

Thus finite-flat closure, connected--étale analysis, niveau-two fundamental characters, and the tame automorphism orders derive the five coefficient-prime exponents, while the two wild tables supply the independent away-from-$p$ exponent-$12$ statement.

### 2.4 The signature table and congruence restrictions

It is helpful to record what the local proof distinguishes.

| Stable local mechanism | $(e,a)$ | Twelfth-power exponent | Extra condition for $p>13$ |
|---|---|---:|---|
| étale or multiplicative direction | $(e,0)$ | $0$ | none |
| cubic descent direction | $(3,1)$ or $(6,2)$ | $4$ | $p\equiv2\pmod3$ |
| half-weight direction | $(4,2)$ | $6$ | $p\equiv3\pmod4$ |
| dual cubic direction | $(3,2)$ or $(6,4)$ | $8$ | $p\equiv2\pmod3$ |
| connected or cyclotomic direction | $(e,e)$ | $12$ | none |

The congruences do not come from asking in isolation whether $\mathbf F_p$
contains a primitive third or fourth root.  They are the solvability conditions
for $12k\equiv s\pmod{p-1}$ on the descended $\mathbf F_p$-line, after the
niveau-two and descent calculation has produced $s$.  This gives precisely
(2.4) and (2.5), including the quartic half-weight row.

Duality (1.8) replaces $s$ by

$$
12-s.
\tag{2.11}
$$

Thus $0$ and $12$ form the endpoint pair, $4$ and $8$ form the cubic pair, and $6$ is balanced.

### 2.5 Semistable and potentially multiplicative sharpenings

For potentially multiplicative reduction, the Tate representation after a quadratic twist is triangular with diagonal characters $1$ and $\chi_p$. The quadratic twist disappears in the twelfth power, so only the endpoint signatures occur.

For semistable reduction no ramified twist is needed. The closure of the kernel is itself connected or étale, and (2.3) holds. This stronger assertion about $\lambda$, rather than merely $\lambda^{12}$, will later create a globally unramified diagonal character. It is not used to shorten the general classification.

## 3. Stable specialization and global reciprocity

### 3.1 Potentially good reduction at an auxiliary prime

The resultant sieve will use the fixed primes $5,7,11$. At such a prime the curve need not have good reduction; integrality of $j$ gives only potentially good reduction. We therefore need a trace statement which survives stable descent.

Let $r\ge5$, $r\ne p$, and suppose

$$
v_r(j(E))\ge0.
\tag{3.1}
$$

There is a finite totally ramified extension $L/\mathbf Q_r$ over which $E$ has good reduction. Total ramification is important: the residue field remains $\mathbf F_r$, so the good special fiber has an integer Frobenius trace

$$
a=r+1-\#\widetilde E(\mathbf F_r),
\qquad |a|\le2\sqrt r.
\tag{3.2}
$$

The descent datum from $L$ to $\mathbf Q_r$ may compose Frobenius with an automorphism $\zeta$ of the special fiber. The stable descent calculation treats this composite as the Frobenius operator on the descended kernel line and, after the corresponding twist of the special fiber, gives it an integral trace $a$. It is not legitimate simply to identify the raw good-reduction eigenvalue over $L$ with $\lambda(\operatorname{Frob}_r)$. What is invariant under that comparison is the determinant $r$ and, by the local classification,

$$
\zeta^{12}=1
\tag{3.3}
$$

on that line. Consequently the twist changes the eigenvalue but not its twelfth power.

Here is the descent construction. Work first over the maximal unramified
extension $K^{\mathrm{nr}}$ of $\mathbf Q_r$. Potential good reduction makes the
inertia image on a prime-to-$r$ Tate module finite. If $I'$ is its kernel, its
fixed extension is totally ramified and the stable-model theorem extends $E$
to an elliptic scheme there. A finite totally ramified subextension already
contains equations for the scheme; call it $L$. Uniqueness of the smooth model
gives, for $\sigma$ in the finite inertia quotient, an automorphism

$$
\gamma_\sigma:\widetilde E_{\overline{\mathbf F}_r}
\longrightarrow\widetilde E_{\overline{\mathbf F}_r}.
\tag{3.3a}
$$

If $F$ is arithmetic Frobenius on the special fiber, then

$$
F\gamma_\sigma F^{-1}=\gamma_\sigma^{\,r}.
\tag{3.3b}
$$

Thus $\gamma_\sigma F$ is a Frobenius descent datum. Effectivity of descent for
the proper smooth curve produces an $\mathbf F_r$-form $E_\gamma$ whose
arithmetic Frobenius on every prime-to-$r$ Tate module is $\gamma_\sigma F$.
Consequently

$$
\det(\gamma_\sigma F)=r,\qquad
\operatorname{tr}(\gamma_\sigma F)=a_\gamma\in\mathbf Z,\qquad
|a_\gamma|\le2\sqrt r.
\tag{3.3c}
$$

On the schematic closure of $C$, this action is the original local Galois
action multiplied by the scalar through which $\gamma_\sigma$ acts on the line.
The table in Section 2.2 makes the twelfth power of that scalar equal to one.

### 3.2 The exceptional special fibers

For a generic special fiber the descent ambiguity is quadratic. At the two exceptional values it must be calculated rather than suppressed:

| Special $j$-value | Descent form | Scalar order on the line | Power which kills it |
|---:|---|---:|---:|
| $j\ne0,1728$ | quadratic | divides $2$ | $12$ |
| $j=1728$ | quartic | divides $4$ | $12$ |
| $j=0$ | sextic | divides $6$ | $12$ |

For $j=1728$, write a quartic twist as $y^2=x^3+dx$ after good reduction. Changing a fourth root of $d$ multiplies the invariant differential and the kernel eigenvalue by the quartic descent character. Its twelfth power is trivial. For $j=0$, the model $y^2=x^3+d$ gives the analogous sextic character, again killed by the twelfth power. These two calculations are why the lemma below remains valid at the exceptional automorphism locus.

More explicitly, at $j=1728$ choose $t^4=d$ and use

$$
x=t^2X,\qquad y=t^3Y.
\tag{3.3d}
$$

Replacing $t$ by $\kappa t$, $\kappa\in\mu_4$, acts by
$(X,Y)\mapsto(\kappa^{-2}X,\kappa^{-3}Y)$. At $j=0$ the same substitution with
$t^6=d$ has $\kappa\in\mu_6$. In either case the twisted pair of Frobenius
eigenvalues has the form

$$
(\kappa\beta,\kappa^{-1}\overline\beta),\qquad
(\kappa\beta)(\kappa^{-1}\overline\beta)=r,\qquad
\kappa^{12}=1.
\tag{3.3e}
$$

These are the actual quartic and sextic twists hidden by the descent notation.

### 3.3 The stable-specialization trace lemma

**Stable-specialization trace lemma.** Let $r\ge5$, $r\ne p$. Suppose $E/\mathbf Q$ admits a rational $p$-isogeny with kernel character $\lambda$, suppose $v_r(j(E))\ge0$, and suppose globally that

$$
\lambda^{12}=\chi_p^s.
$$

Then there are an integer $a$ and an element $\alpha\in\mathbf F_p^\times$ such that

$$
|a|\le2\sqrt r,
\tag{3.4}
$$

$$
\alpha^2-a\alpha+r=0,
\qquad
\alpha^{12}=r^s.
\tag{3.5}
$$

**Proof.** Acquire good reduction over the totally ramified stable extension and
retain the descent datum on the finite-flat closure of the kernel. Frobenius on
the good special fiber has polynomial $T^2-aT+r$. Composing it with the
quadratic, quartic, or sextic descent automorphism gives the Frobenius operator
on the descended kernel line. Let $\delta$ be the scalar supplied by that
automorphism and let $\beta$ be the raw good-reduction eigenvalue. Then

$$
\alpha=\lambda(\operatorname{Frob}_r)=\delta\beta\in\mathbf F_p,\qquad
\alpha\overline\alpha=r,\qquad
\delta^{12}=1.
\tag{3.5a}
$$

The membership $\alpha\in\mathbf F_p$ follows from the original rational
kernel line. Because $\alpha$ is an eigenvalue of the actual $\mathbf F_r$-form
$E_\gamma$ constructed in (3.3a)--(3.3c), not merely of an operator over an
extension field, its polynomial is

$$
T^2-a_\gamma T+r,\qquad a_\gamma\in\mathbf Z,\quad |a_\gamma|\le2\sqrt r.
\tag{3.5b}
$$

Finally arithmetic Frobenius and the global signature give

$$
\alpha^{12}=\lambda(\operatorname{Frob}_r)^{12}=r^s.
\tag{3.5c}
$$

This proves (3.4)--(3.5), including the quartic and sextic fibers. $\square$

The same construction has a small-residue-characteristic version needed once
in Section 6.3.  For $r=2$ or $3$, take the good model over the finite totally
ramified extension cut out after base change to $\mathbf Q_r^{\mathrm{nr}}$,
and retain its full (possibly wild) descent datum.  Effectivity of descent is
unchanged.  Although the automorphism group of the special fiber need not be
cyclic, its scalar on the stable $\mathbf F_p$-line factors through the
abelianization; the last two rows of the table in Section 2.2 show that this
scalar has exponent dividing $12$.  Consequently (3.4), (3.5a)--(3.5c), and
the Hasse bound remain valid for $r=2,3$.  No tame conductor claim is made at
these two primes.

The assertion $\alpha\in\mathbf F_p$ is stronger than the vanishing of a resultant. That distinction will remove a spurious factor $31$.

### 3.4 From local inertia to a global signature

Return to a rational $p$-isogeny over $\mathbf Q$, with $p\ge5$. By (2.6), $\lambda^{12}$ is unramified at every finite prime away from $p$. Choose $s$ from (2.1) and form

$$
\theta=\lambda^{12}\chi_p^{-s}.
\tag{3.6}
$$

The character $\theta$ is unramified at $p$ because its restriction to inertia is trivial, and it is unramified away from $p$ by (2.6). Complex conjugation has eigenvalues $1,-1$ on $E[p]$, so

$$
\lambda(c_\infty)^{12}=1=\chi_p(c_\infty)^s
\tag{3.7}
$$

because every $s$ in (2.2) is even. Thus $\theta$ is also even at infinity.

Global class field theory identifies a finite character unramified at every finite prime and even at infinity with a character of the ordinary ideal class group of $\mathbf Q$. That class group is trivial. Hence

$$
\boxed{
\lambda^{12}=\chi_p^s,
\qquad
s\in\{0,4,6,8,12\}.}
\tag{3.8}
$$

This is the global signature theorem, proved here from the local theorem rather than imported. With arithmetic Frobenius, (3.8) reads

$$
\lambda(\operatorname{Frob}_r)^{12}=r^s.
\tag{3.9}
$$

For $p>19$, the five integers $0,4,6,8,12$ are distinct modulo $p-1$. The global signature is therefore unambiguous in every branch of the elimination, and a potentially multiplicative endpoint cannot be mistaken for the balanced signature.

The local Artin map sends a unit $u\in\mathbf Z_p^\times$ to an element on which $\chi_p$ takes the value $u^{-1}$; this inverse is already absorbed in the reciprocity convention. It does not reverse the arithmetic-Frobenius identity (3.9).

## 4. Odd cusp rigidity supplies three interior primes

### 4.1 Cuspidal reduction and negative valuation

Let $x=x(E,C)\in Y_0(p)(\mathbf Q)$. At a prime $r\ne p$, properness extends $x$ to the standard compactified model. If

$$
v_r(j(E))<0,
\tag{4.1}
$$

then $E$ is potentially multiplicative. Tate uniformization shows that its stable generalized elliptic curve is a polygon, so the section $x$ reduces to one of the two cusps of $X_0(p)$.

The converse boundary statement is equally important: additive potentially good reduction has integral $j$ and specializes to the interior after stable extension. A singular nonminimal Weierstrass cubic is not evidence of cuspidal reduction. The stable modular object, not the chosen equation, decides whether a point reaches the boundary.

### 4.2 The exact interface from Book 69

For a positive-genus prime level, Book 69 constructs the actual optimal winding quotient

$$
J_0(p)\twoheadrightarrow J_0(p)^{\mathrm w}.
$$

Its rational points are finite by the modular rank-zero theorem on the newform factors with nonzero central value. Its Néron cotangent lattice is primitive, so a suitable Hecke translate of the Abel--Jacobi map is a formal immersion at either cusp. At an odd good prime, torsion in the rational points of this quotient specializes injectively. These three facts give the exported implication

$$
\boxed{
x\in X_0(p)(\mathbf Q),\quad
r\text{ odd},\quad r\ne p,\quad
x\bmod r\text{ is a cusp}
\Longrightarrow x\text{ is that cusp}.}
\tag{4.2}
$$

The statement concerns the winding quotient, not all of $J_0(p)$. It does not infer the quotient's torsion from the Jacobian's torsion, and it is asserted only at odd $r$.

### 4.3 The three fixed auxiliary primes

Assume from now through Chapter 7 that

$$
p>19
\tag{4.3}
$$

and that $x=x(E,C)$ is noncuspidal. The level then has positive genus. For each

$$
r\in\{5,7,11\},
\tag{4.4}
$$

we have $r\ne p$. If $v_r(j(E))<0$, Section 4.1 puts $x$ in a cusp disk and (4.2) makes $x$ a cusp, a contradiction. Therefore

$$
\boxed{
v_5(j(E))\ge0,
\qquad
v_7(j(E))\ge0,
\qquad
v_{11}(j(E))\ge0.}
\tag{4.5}
$$

This is the sole use of odd cusp rigidity in the main elimination. It supplies exactly three places at which the stable-specialization trace lemma applies, even if the chosen elliptic curve has additive potentially good reduction there.

## 5. The exact unbalanced-signature sieve

### 5.1 Resultants and the Hasse interval

For a prime $r$ define the finite Hasse set

$$
H_r=\{a\in\mathbf Z:a^2\le4r\}.
\tag{5.1}
$$

For $a\in H_r$ and a signature $s$, put

$$
R_{r,a,s}
=\operatorname{Res}_T(T^2-aT+r,T^{12}-r^s),
\tag{5.2}
$$

and

$$
B_{r,s}=\prod_{a\in H_r}|R_{r,a,s}|.
\tag{5.3}
$$

At the three primes in (4.4), the stable-specialization lemma gives an $a\in H_r$ and a common root in $\mathbf F_p$. Hence

$$
p\mid R_{r,a,s}
\quad\text{and therefore}\quad
p\mid B_{r,s}.
\tag{5.4}
$$

Thus for every unbalanced signature

$$
p\mid\gcd(B_{5,s},B_{7,s},B_{11,s}).
\tag{5.5}
$$

The balanced case $s=6$ is intentionally absent: $a=0$ makes the two polynomials compatible over characteristic zero and $B_{r,6}=0$. Its arithmetic content is class-field theoretic rather than resultant-theoretic.

### 5.2 A recurrence certificate for every resultant

A Sylvester determinant would conceal the arithmetic. Reduce powers of $T$ modulo

$$
T^2-aT+r.
$$

Write, consistently,

$$
T^n\equiv u_nT+v_n\pmod{T^2-aT+r}.
\tag{5.6}
$$

The initial values and recurrence are

$$
u_0=0,
\qquad
v_0=1,
\tag{5.7}
$$

$$
u_{n+1}=a u_n+v_n,
\qquad
v_{n+1}=-r u_n.
\tag{5.8}
$$

At $n=12$ this gives

$$
u_{12}
=a^{11}-10a^9r+36a^7r^2-56a^5r^3+35a^3r^4-6ar^5,
\tag{5.9}
$$

$$
v_{12}
=-a^{10}r+9a^8r^2-28a^6r^3+35a^4r^4-15a^2r^5+r^6.
\tag{5.10}
$$

If $\beta,\gamma$ are the two roots of $T^2-aT+r$, then

$$
\beta+\gamma=a,
\qquad
\beta\gamma=r.
$$

The remainder of $T^{12}-r^s$ is

$$
u_{12}T+(v_{12}-r^s).
$$

Taking its value at $\beta$ and $\gamma$ proves the exact certificate

$$
\boxed{
R_{r,a,s}
=(v_{12}-r^s)^2
+a u_{12}(v_{12}-r^s)
+r u_{12}^2.}
\tag{5.11}
$$

Equations (5.7)--(5.11), together with the short intervals

$$
H_5=\{-4,-3,\ldots,4\},
$$

$$
H_7=\{-5,-4,\ldots,5\},
$$

$$
H_{11}=\{-6,-5,\ldots,6\},
\tag{5.12}
$$

reproduce every integer in the factorization ledger below.

### 5.3 The complete factorization certificate

For the endpoint signature $s=0$, direct substitution in (5.11) gives

$$
\begin{aligned}
B_{5,0}={}&2^{66}3^{14}5^{10}7^6 13^8 17^2 31^2 37^4
61^4 157^2 229^2,\\
B_{7,0}={}&2^{66}3^{42}5^8 7^{10}11^2 13^{12}19^4 31^2
37^6 43^2 61^6 73^2 2953^2,\\
B_{11,0}={}&2^{80}3^{24}5^{24}7^{16}11^2 13^{12}17^4 19^4
29^2 31^2 37^2 73^2 79^2 101^2 109^2 139^2\\
&\qquad\cdot313^2 337^2 3541^2 13009^2 15289^2 17041^2.
\end{aligned}
\tag{5.13}
$$

For the cubic signature $s=4$ one obtains

$$
\begin{aligned}
B_{5,4}={}&2^{66}3^6 5^{40}11^2 13^8 17^4 149^2 181^2,\\
B_{7,4}={}&2^{66}3^{22}5^8 7^{48}11^2 17^2 19^6 23^2
73^2 541^6,\\
B_{11,4}={}&2^{84}3^{10}5^{22}11^{56}17^4 19^4 23^2 29^2
37^4 41^2 43^2 113^2 137^2 149^2\\
&\qquad\cdot193^2 1553^2 1933^2.
\end{aligned}
\tag{5.14}
$$

The dual cubic signature $s=8$ has

$$
\begin{aligned}
B_{5,8}={}&2^{66}3^6 5^{76}11^2 13^8 17^4 149^2 181^2,\\
B_{7,8}={}&2^{66}3^{22}5^8 7^{92}11^2 17^2 19^6 23^2
73^2 541^6,\\
B_{11,8}={}&2^{84}3^{10}5^{22}11^{108}17^4 19^4 23^2 29^2
37^4 41^2 43^2 113^2 137^2 149^2\\
&\qquad\cdot193^2 1553^2 1933^2.
\end{aligned}
\tag{5.15}
$$

Finally, for $s=12$,

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
\tag{5.16}
$$

The dual rows provide a built-in check: passing from $s$ to $12-s$ changes only the power of the auxiliary prime $r$. Every remaining displayed factor is prime; trial division through its square root suffices, the largest factor being $17041$. Taking the minimum exponent of each prime down the three rows gives

$$
\boxed{
G_0=G_{12}
=2^{66}3^{14}5^8 7^6 13^8 31^2 37^2,}
\tag{5.17}
$$

and

$$
\boxed{
G_4=G_8
=2^{66}3^6 5^8 11^2 17^2.}
\tag{5.18}
$$

This is a gcd certificate rather than a mere reported integer: each common exponent is visible as the minimum in (5.13)--(5.16), and every omitted prime is absent from at least one of the three factorizations.

### 5.4 Eliminating the cubic signatures

If $s=4$ or $8$, equations (5.5) and (5.18) force $p$ to divide

$$
2\cdot3\cdot5\cdot11\cdot17.
$$

This contradicts $p>19$. Hence

$$
s=4,8\quad\text{are impossible for }p>19.
\tag{5.19}
$$

If $s=0$ or $12$, equations (5.5) and (5.17) leave only

$$
p=31\quad\text{or}\quad p=37.
\tag{5.20}
$$

The first is spurious for a reason which the resultant itself cannot see.

### 5.5 The apparent factor $31$

Work at $r=5$ modulo $31$. Since

$$
5^{12}=1\pmod{31},
\tag{5.21}
$$

the endpoint equations $\alpha^{12}=5^0$ and $\alpha^{12}=5^{12}$ are identical. Their solutions in $\mathbf F_{31}^\times$ are

$$
\alpha\in\{1,5,6,25,26,30\}.
\tag{5.22}
$$

For the six values, the trace forced by

$$
\alpha^2-a\alpha+5=0
$$

is $a=\alpha+5\alpha^{-1}$. The exact table is

$$
\begin{array}{c|rrrrrr}
\alpha&1&5&6&25&26&30\\ \hline
\alpha+5\alpha^{-1}&6&6&12&19&25&25.
\end{array}
\tag{5.23}
$$

But

$$
H_5\bmod31
=\{0,\pm1,\pm2,\pm3,\pm4\}
=\{0,1,2,3,4,27,28,29,30\},
\tag{5.24}
$$

which is disjoint from $\{6,12,19,25\}$. Thus no $\mathbf F_{31}$-valued kernel eigenvalue satisfies the stable-specialization lemma, and

$$
p\ne31.
\tag{5.25}
$$

There is a useful notation check here. The six numbers

$$
\{3,13,15,16,18,28\}
\tag{5.26}
$$

satisfy $\alpha^{12}=8=3^{12}$ modulo $31$; they are the $s=12$ roots for the diagnostic auxiliary prime $r=3$, not for $r=5$. At $r=3$ their traces $\alpha+3\alpha^{-1}$ are

$$
\{4,9,13,18,22,27\},
$$

also disjoint from $H_3\bmod31$. Equation (5.21) shows why using (5.26) as an $r=5$ list would be inconsistent.

The factor $31$ nevertheless occurs in the integer resultants because a resultant vanishes modulo $31$ when the two polynomials have a common root over $\overline{\mathbf F}_{31}$. Such a root need not lie in $\mathbf F_{31}$. A rational kernel character, however, takes Frobenius values in $\mathbf F_{31}^\times$. The extension-field roots create the artifact; the line-valued trace table removes it.

We have proved the endpoint conclusion

$$
\boxed{s=0\text{ or }12,\quad p>19\Longrightarrow p=37.}
\tag{5.27}
$$

## 6. The balanced signature

### 6.1 Why the $j$-invariant is integral

Assume

$$
p>19,
\qquad
s=6.
\tag{6.1}
$$

We prove that $v_q(j(E))\ge0$ at every rational prime $q$.

Let first $q$ be odd and $q\ne p$. If $v_q(j)<0$, then $x(E,C)$ reduces to a cusp modulo $q$. Odd cusp rigidity (4.2) makes $x$ that cusp, contradicting noncuspidality. Hence

$$
v_q(j)\ge0
\qquad(q\text{ odd},\ q\ne p).
\tag{6.2}
$$

If $v_p(j)<0$, then $E/\mathbf Q_p$ is potentially multiplicative. The local theorem permits only the endpoint signatures $0,12$, contrary to $s=6$. Thus

$$
v_p(j)\ge0.
\tag{6.3}
$$

It remains to treat $2$, where Book 69 supplies no cusp-disk theorem. Suppose $v_2(j)<0$. The potentially multiplicative Tate calculation, including its quadratic twist, makes $\lambda^{12}$ unramified and gives

$$
\lambda(\operatorname{Frob}_2)^{12}
\in\{1,2^{12}\}\pmod p.
\tag{6.4}
$$

The global balanced signature gives the same value as $2^6$. Either possibility in (6.4) yields

$$
2^6\equiv1\pmod p,
$$

after division by the nonzero factor $2^6$ in the second case. Therefore

$$
p\mid2^6-1=63,
$$

which is impossible for $p>19$. Hence $v_2(j)\ge0$. Combining the three cases gives

$$
\boxed{j(E)\in\mathbf Z.}
\tag{6.5}
$$

Equivalently, $E$ is everywhere potentially good. Notice that no unavailable $2$-adic specialization kernel was used.

### 6.2 The balanced class-field theorem

The balanced branch now meets the second deep local--global input.

**Balanced signature class-field theorem.** Let $p>19$. Suppose $E/\mathbf Q$ is everywhere potentially good, admits a rational $p$-isogeny with kernel character $\lambda$, and has signature

$$
\lambda^{12}=\chi_p^6.
\tag{6.6}
$$

Then

$$
p\equiv3\pmod4
\tag{6.7}
$$

and

$$
h\bigl(\mathbf Q(\sqrt{-p})\bigr)=1.
\tag{6.8}
$$

The theorem does not enumerate the primes satisfying (6.8), does not calculate $X_0(p)(\mathbf Q)$, and does not contain the desired isogeny classification.

### 6.3 How the class group enters

The proof is short enough to give completely.  Regard $\lambda$ and $\chi_p$ as
$\mathbf F_p^\times$-valued characters and form

$$
\psi=\lambda^6\chi_p^{-3}.
\tag{6.9}
$$

Equation (6.6) gives $\psi^2=1$, so $\psi$ has values in
$\{\pm1\}\subset\mathbf F_p^\times$.  The half-weight row of the local table
gives both

$$
p\equiv3\pmod4
\tag{6.9a}
$$

and, with $\omega=\chi_p|_{I_p}$,

$$
\psi|_{I_p}=\omega^{(p-1)/2}.
\tag{6.9b}
$$

Thus the conductor exponent of $\psi$ at $p$ is exactly one.  If $q\ne p$,
$\chi_p$ is unramified and Section 2.2 says that the order of
$\lambda|_{I_q}$ divides $12$.  Since $v_2(p-1)=1$, an element of
$\mathbf F_p^\times$ whose order divides $12$ actually has order dividing $6$.
Consequently

$$
\psi|_{I_q}=\lambda^6|_{I_q}=1
\qquad(q\ne p).
\tag{6.9c}
$$

This includes $q=2$ and $q=3$: their possibly wild characters were shown to
have order dividing $12$ before the cyclic target $\mathbf F_p^\times$ was
imposed. At the real place, $\lambda(c)=\pm1$ and $\chi_p(c)=-1$, whence

$$
\psi(c)=\lambda(c)^6\chi_p(c)^{-3}=-1.
\tag{6.9d}
$$

The finite conductor of $\psi$ is therefore $p$ and its infinite conductor is
the real place.  There is only one such quadratic Dirichlet character:

$$
\psi(n)=\left(\frac{-p}{n}\right)
\quad ((n,p)=1).
\tag{6.9e}
$$

Its fixed field is

$$
K=\mathbf Q(\sqrt{-p}),
\tag{6.10}
$$

and $-p$ is its fundamental discriminant.

We next make the Frobenius and ideal calculation exact.  Let $r\ne p$ be a
rational prime split in $K$. Since $E$ is everywhere potentially good, stable
specialization gives an integer $a_r$ and the eigenvalue
$\alpha=\lambda(\operatorname{Frob}_r)\in\mathbf F_p^\times$ with

$$
\alpha^2-a_r\alpha+r=0,\qquad |a_r|\le2\sqrt r.
\tag{6.10a}
$$

For $r\ge5$ this is Section 3.3. For $r=2,3$ the same construction uses the
wild rows of Section 2.2; the descent scalar still has twelfth power one and the
descended special fiber is over $\mathbf F_r$, so (6.10a) remains valid.
Splitting means $\psi(\operatorname{Frob}_r)=1$, and hence

$$
\alpha^6=r^3,\qquad
\zeta:=\frac{\alpha^2}{r},\qquad \zeta^3=1.
\tag{6.10b}
$$

The other root of (6.10a) is $r/\alpha$.  Therefore

$$
\frac{a_r^2}{r}=\zeta+2+\zeta^{-1}=
\begin{cases}
4,&\zeta=1,\\
1,&\zeta\ne1,
\end{cases}
\pmod p,
\tag{6.10c}
$$

or, equivalently,

$$
p\mid(a_r^2-4r)(a_r^2-r).
\tag{6.10d}
$$

This congruence has a literal algebraic-integer interpretation in the first
branch. If $\zeta=1$ and

$$
p\le4r<2p,
\tag{6.10e}
$$

then Hasse and (6.10d) give $4r-a_r^2=p$. The parity is automatic, and

$$
\pi_r=\frac{a_r+\sqrt{-p}}2\in\mathcal O_K,\qquad
N_{K/\mathbf Q}(\pi_r)=r.
\tag{6.10f}
$$

Thus the prime ideal

$$
\mathfrak r=(\pi_r)
\tag{6.10g}
$$

over $r$ is principal, of norm exactly $r$--not “norm $r$ or a controlled
power.” In the smaller range needed below, the relation is even stronger. If
$4r<p$, then Hasse gives

$$
0\le4r-a_r^2<p,\qquad |a_r^2-r|\le3r<p.
\tag{6.10h}
$$

Divisibility in (6.10d) would force $a_r^2=4r$ or $a_r^2=r$. Neither is
possible for a rational prime $r$. Hence

$$
\boxed{r<p/4\quad\Longrightarrow\quad r\text{ is not split in }K.}
\tag{6.10i}
$$

At the two wild primes the complete numerical check is

| $r$ | possible $a_r$ | values of $4r-a_r^2$ | values of $a_r^2-r$ |
|---:|---|---|---|
| $2$ | $-2,-1,0,1,2$ | $4,7,8$ | $-2,-1,2$ |
| $3$ | $-3,-2,-1,0,1,2,3$ | $3,8,11,12$ | $-3,-2,1,6$ |

No entry is divisible by $p>19$. This is the promised separate $r=2,3$
treatment.

Minkowski's theorem says that every ideal class of the imaginary quadratic field $K$ contains an integral ideal of norm at most

$$
\frac{2}{\pi}\sqrt p.
\tag{6.11}
$$

For $p>19$,

$$
\frac2\pi\sqrt p<\frac p4
\quad\Longleftrightarrow\quad
\sqrt p>\frac8\pi.
\tag{6.11a}
$$

Choose in an ideal class an integral ideal $\mathfrak a$ of least norm among
those supplied by (6.11), and remove every rational principal ideal dividing
it. A prime ideal factor of what remains cannot lie over an inert rational
prime $r$, because the unique prime there is $(r)$, of norm $r^2$, and could be
removed. It cannot be the ramified prime over $p$, whose norm $p$ is larger
than (6.11). It cannot lie over a split prime, because its rational prime has
norm at most $N\mathfrak a\le(2/\pi)\sqrt p<p/4$, contradicting (6.10i).
There is no prime factor left, so $\mathfrak a=\mathcal O_K$. Every ideal class
is trivial and

$$
h(K)=1.
\tag{6.11b}
$$

The logical chain is therefore

$$
\text{quadratic character}
\longrightarrow
\text{conductor }-p
\longrightarrow
\text{exact split-prime trace and norm relation}
\longrightarrow
\text{Minkowski generation}
\longrightarrow
h(K)=1.
\tag{6.12}
$$

No step in (6.12) knows the class-number-one list.

## 7. The independent class-number-one theorem

### 7.1 The theorem and its proof architecture

We now use a theorem about imaginary quadratic fields which is independent of modular curves and rational isogenies.

**Class-number-one theorem.** The negative fundamental discriminants whose imaginary quadratic fields have class number one are exactly

$$
\boxed{
-3,-4,-7,-8,-11,-19,-43,-67,-163.}
\tag{7.1}
$$

Its proof has four distinct layers. Reduced positive definite binary quadratic forms identify ideal classes and give canonical representatives

$$
[A,B,C],
\qquad
B^2-4AC=D,
\qquad
|B|\le A\le C.
\tag{7.2}
$$

If the class number is one, every reduced form is principal; elementary reduction already imposes strong congruence restrictions. Singular moduli and Weber functions then attach algebraic integers of controlled degree and unusually sharp size to the reduced forms. Analytic estimates for their $q$-expansions, together with lower bounds for the relevant class invariants, bound $|D|$. Finally one enumerates the reduced forms for the bounded discriminants and checks their class composition. This finite check produces (7.1).

The reduced-form step proves that the objects being counted are ideal classes; the singular-modulus or Weber step makes the bound effective; the analytic estimate makes the search finite; and the final reduced-form calculation certifies every survivor. None of these stages invokes a rational point on $X_0(p)$.

### 7.2 Intersection with the balanced branch

In the balanced branch, (6.7) makes $-p$ a negative fundamental discriminant, and (6.8) makes its class number one. Intersecting the form

$$
D=-p,
\qquad p>19\text{ prime},
\tag{7.3}
$$

with the nine entries in (7.1) removes $-3,-7,-11,-19$ by the size condition and removes $-4,-8$ because they are not negatives of odd primes. Exactly three discriminants remain:

$$
-43,-67,-163.
$$

Therefore

$$
\boxed{s=6,\quad p>19\Longrightarrow p\in\{43,67,163\}.}
\tag{7.4}
$$

Together, (5.19), (5.27), and (7.4) already prove that every rational prime isogeny of degree greater than $19$ has degree

$$
37,43,67,\text{ or }163.
\tag{7.5}
$$

What remains is not another elimination theorem. We must certify the rational points at level $37$ and construct an isogeny at every surviving degree.

## 8. The complete level-$37$ certificate

### 8.1 The genus-two model and its involutions

The certificate has three independent pieces. A Sturm-bound identity identifies the pointed canonical model, an exact modular-symbol integral makes the relevant elliptic quotient rank zero through Book 69, and three explicit fibers recover every rational point. None of these steps imports the rational points of $X_0(37)$.

The endpoint sieve leaves $37$, but survival of congruences is not existence.
We first certify the pointed modular model, rather than naming a genus-two curve
after the fact. Let $f_+,f_-$ be the normalized forms of Section 8.4 and put

$$
\vartheta=q\frac d{dq},\qquad
W=(\vartheta f_+)f_- - f_+(\vartheta f_-),\qquad
u=\frac{f_+}{f_-},\qquad
v=-\frac{2W}{f_-^3}.
\tag{8.0a}
$$

The Rankin--Cohen cancellation makes $W$ a weight-six cusp form. The exact
weight-twelve identity is

$$
4W^2=-f_+^6-9f_+^4f_-^2-11f_+^2f_-^4+37f_-^6.
\tag{8.0b}
$$

Its Sturm bound is

$$
\left\lfloor\frac{12}{12}\,[\operatorname{SL}_2(\mathbf Z):\Gamma_0(37)]\right\rfloor
=38.
\tag{8.0c}
$$

The coefficient vectors through $q^{38}$ are displayed in Section 8.4, so
(8.0b) is a finite integral identity. It gives the canonical function field

$$
C:\quad
v^2=-u^6-9u^4-11u^2+37.
\tag{8.1}
$$

Because $u=f_+/f_-$ is the ratio of a basis of the two-dimensional canonical
space, it is the canonical degree-two map of the genus-two curve. Hence the
function-field identity identifies the smooth projective curve with
$X_0(37)$; it is not merely a birational comparison with an unnamed curve.
Moreover (8.0a) gives

$$
-2\frac{du}{v}=f_-\frac{dq}{q},\qquad
-2u\frac{du}{v}=f_+\frac{dq}{q}.
\tag{8.1a}
$$

At the standard cusp use $q=e^{2\pi i\tau}$; the exact local expansions begin

$$
\begin{aligned}
u(q)&=1-2q-4q^2+6q^3-2q^4-8q^5+14q^6+2q^7-26q^8+O(q^9),\\
v(q)&=4+16q-40q^2+8q^3+152q^4-256q^5-160q^6
       +992q^7-960q^8+O(q^9).
\end{aligned}
\tag{8.1b}
$$

Thus this cusp is $c_\infty=(1,4)$. The Hecke signs in (8.16) and the identity
$U_{37}=-w_{37}$ give $w_{37}f_+=f_+$ and $w_{37}f_-=-f_-$. Therefore the
chosen modular normalization has

$$
w_{37}(u,v)=(-u,v),
\tag{8.2}
$$

and the rational cusps are

$$
c_\infty=(1,4),
\qquad
c_0=(-1,4).
\tag{8.3}
$$

At the other cusp take the actual width-$37$ parameter

$$
q_0=\exp\!\left(-\frac{2\pi i}{37\tau}\right)=q(w_{37}\tau).
$$

Then

$$
u=-1+2q_0+4q_0^2-6q_0^3+2q_0^4+8q_0^5-14q_0^6+O(q_0^7),
\qquad
v=4+16q_0-40q_0^2+8q_0^3+O(q_0^4).
\tag{8.3a}
$$

These are actual uniformizers at the two pointed cusps.

The hyperelliptic involution is $(u,v)\mapsto(u,-v)$. Thus $w_{37}$ and its product with the hyperelliptic involution give two degree-two elliptic quotients. This split is the geometric reason one must not replace the winding quotient by all of the genus-two Jacobian: the rank-zero quotient below already controls every rational point, while no Mordell--Weil assertion about the other quotient is required.

The smooth projective completion of (8.1) has two points at infinity over $\mathbf Q(i)$, not over $\mathbf Q$. Therefore the affine calculation below loses no rational points.

### 8.2 The two elliptic quotients

The quotient fixed by $w_{37}$ is

$$
E_+:\quad y^2+y=x^3-x,
\tag{8.4}
$$

with map

$$
\phi_+(u,v)=
\left(
-\frac{u^2+3}{4},
\frac{v-4}{8}
\right).
\tag{8.5}
$$

Indeed,

$$
y^2+y=\frac{v^2-16}{64}
$$

and

$$
x^3-x
=\frac{-(u^2+3)^3+16(u^2+3)}{64}
=\frac{-u^6-9u^4-11u^2+21}{64},
$$

so (8.1) makes the two expressions equal.

The quotient by $(u,v)\mapsto(-u,-v)$ is

$$
E_-:\quad
y^2+y=x^3+x^2-23x-50,
\tag{8.6}
$$

with map

$$
\phi_-(u,v)=
\left(
\frac{37/u^2-5}{4},
\frac{37v/u^3-4}{8}
\right).
\tag{8.7}
$$

Substitution in (8.6), followed by multiplication by $64u^6$, reduces exactly to (8.1). Although (8.7) appears to have a pole at $u=0$, it extends to the projective curve. In projective coordinates on (8.6), it is represented near $u=0$ by

$$
[X:Y:Z]
=
[2u(37-5u^2):37v-4u^3:8u^3].
\tag{8.8}
$$

At $u=0$ the middle coordinate is nonzero because $v^2=37$, so (8.8) is $[0:1:0]$, the origin $O$ of $E_-$. This proves the claimed extension at both points over $u=0$.

The invariant differentials provide a second exact check. Direct differentiation gives

$$
\boxed{
\phi_+^*\frac{dx}{2y+1}
=-2u\frac{du}{v},
\qquad
\phi_-^*\frac{dx}{2y+1}
=-2\frac{du}{v}.}
\tag{8.9}
$$

The first is invariant under $w_{37}$ and the second is anti-invariant, exactly as the quotient description requires.

### 8.3 The rank-zero Mordell--Weil certificate

Only the quotient $E_-$ is needed to enumerate the rational points of $C$.
Let

$$
Q=(8,18)\in E_-(\mathbf Q).
\tag{8.10}
$$

The tangent at $Q$ is $y=5x-22$. Substitution in (8.6) leaves
$-(x-8)^3$, so the tangent has triple intersection at $Q$ and $3Q=O$.
The exact good-reduction counts for both quotient curves are

$$
\begin{array}{c|cc}
q&\#E_+(\mathbf F_q)&\#E_-(\mathbf F_q)\\ \hline
3&7&3\\
5&8&6.
\end{array}
\tag{8.11}
$$

In particular, rational torsion on $E_-$ has order dividing $3$ and is
generated by $Q$. The modular-symbol calculation in the next section proves

$$
\frac{L(E_-,1)}{\Omega^+}=\frac13\ne0.
\tag{8.12}
$$

Book 69's modular rank-zero theorem applies to this actual optimal quotient and
gives $\operatorname{rank}E_-(\mathbf Q)=0$. Therefore

$$
\boxed{
E_-(\mathbf Q)=\mathbf Z/3\mathbf Z\,(8,18),
\qquad
-Q=(8,-19).}
\tag{8.13}
$$

This is logically sufficient: every rational point of $C$ maps to one of the
three points in (8.13), and Section 8.5 computes those three fibers. The
verified quotient $E_+$ records the other newform direction; no statement
about $E_+(\mathbf Q)$ enters the rational-point proof. Nor is a torsion point
on $E_-$ claimed to lift to rational torsion on $J_0(37)$.

### 8.4 Modular symbols, newforms, and the Sturm bound

The index of $\Gamma_0(37)$ is $38$, so the weight-two Sturm bound is

$$
\left\lfloor
\frac2{12}[\operatorname{SL}_2(\mathbf Z):\Gamma_0(37)]
\right\rfloor
=\left\lfloor\frac{76}{12}\right\rfloor=6.
\tag{8.14}
$$

The two normalized rational newforms are certified through that bound by

$$
\begin{aligned}
f_+&=q-2q^2-3q^3+2q^4-2q^5+6q^6+O(q^7),\\
f_-&=q+q^3-2q^4+O(q^7).
\end{aligned}
\tag{8.15}
$$

Thus their Hecke and level data are

$$
\begin{array}{c|cc}
&T_2&U_{37}\\ \hline
f_+&-2&-1\\
f_-&0&1.
\end{array}
\tag{8.16}
$$

The point counts in (8.11) independently recover

$$
a_3(f_+)=-3,
\quad a_5(f_+)=-2,
\qquad
a_3(f_-)=1,
\quad a_5(f_-)=0.
$$

The prime-power and multiplicative relations then give the coefficients at $4$ and $6$ in (8.15). Expanding the two differentials in (8.9) at the cusp through $q^6$ gives $f_+$ and $f_-$ with these normalizations; (8.14) proves equality of the modular forms, not merely agreement of a few experimental coefficients.

For the weight-twelve canonical-model check (8.0b), here are all coefficients
through its Sturm bound. Entries are $a_1,\ldots,a_{38}$:

$$
\begin{aligned}
(a_n(f_+))={}&(1,-2,-3,2,-2,6,-1,0,6,4,-5,-6,-2,2,6,-4,0,-12,0,\\
&-4,3,10,2,0,-1,4,-9,-2,6,-12,-4,8,15,0,2,12,-1,0),\\
(a_n(f_-))={}&(1,0,1,-2,0,0,-1,0,-2,0,3,-2,-4,0,0,4,6,0,2,0,\\
&-1,0,6,0,-5,0,-5,2,-6,0,-4,0,3,0,0,4,1,0).
\end{aligned}
\tag{8.16a}
$$

Substitution of these two integer vectors into (8.0b) makes every coefficient
through $q^{38}$ zero. The weight-twelve Sturm bound then proves the
hyperelliptic equation, while the weight-two bound (8.14) proves the two
differential identifications. This supplies both parts of the pointed
canonical-model certificate.

The modular-symbol identity (8.12) can also be proved without a floating-point period.
Let

$$
e=\{0,\infty\}\in H_1(X_0(37),\{\text{cusps}\};\mathbf Z)
\tag{8.16b}
$$

be oriented from $c_0$ to $c_\infty$. From (8.7),

$$
\phi_-(c_\infty)=Q,\qquad
\phi_-(c_0)=-Q.
\tag{8.16c}
$$

Translate the quotient map by $-Q$ and call it $\Phi$. Then
$\Phi(c_\infty)=O$, $\Phi(c_0)=Q$, and the path
$\gamma=\Phi_*e$ runs from $Q$ to $O$.  The oriented Manin edge has one
interior Atkin--Lehner fixed point $z_*=i/\sqrt{37}$.  Cutting there and using
(8.1b), (8.7), and the positive real branch selected by (8.22e) gives the exact
edge ledger

$$
\begin{array}{c|c|c|c}
\text{subedge}&(u,v)&\phi_-\text{-endpoints}&\Phi\text{-endpoints}\\ \hline
0\longrightarrow z_*&-1\le u\le0, v>0&-Q\longrightarrow O&Q\longrightarrow -Q\\
z_*\longrightarrow i\infty&0\le u\le1, v>0&O\longrightarrow Q&-Q\longrightarrow O.
\end{array}
\tag{8.16d}
$$

Thus $\gamma$ is the union of two consecutive one-third arcs on
$E_-(\mathbf R)^0$. Since $3Q=O$, the singular chain

$$
\Gamma=\tau_{2Q}\gamma+\tau_Q\gamma+\gamma
\tag{8.16e}
$$

has successive endpoints $O\to2Q\to Q\to O$.  Each of the three elementary
arcs cut out by $O,Q,-Q$ occurs twice, so $\Gamma$ is exactly two circuits of
$E_-(\mathbf R)^0$.  This factor of two is essential: completing the square
gives

$$
(2y+1)^2=4x^3+4x^2-92x-199,
$$

whose cubic has discriminant $2^4\cdot37^3>0$ and roots in
$(-3.519,-3.518)$, $(-2.707,-2.706)$, and $(5.224,5.225)$. Hence
$E_-(\mathbf R)$ has two components. If $\Omega_0$ is the integral of the
Néron differential around the identity component, the real Néron period used
in (8.12) is

$$
\Omega^+=\int_{E_-(\mathbf R)}\left|\frac{dx}{2y+1}\right|=2\Omega_0.
\tag{8.16f}
$$

The sign is algebraic on both subedges: (8.7) gives

$$
\frac{dx}{du}=-\frac{37}{2u^3},
\qquad
2y+1=\frac{37v}{4u^3},
\qquad
\frac{dx}{2y+1}=-\frac{2\,du}{v}<0,
$$

because the oriented edge has $du>0$ and $v>0$.
Translation invariance of the differential and (8.9) now give

$$
\int_\Gamma\frac{dx}{2y+1}
=3\int_e f_-\frac{dq}{q}.
\tag{8.16g}
$$

On the vertical Manin path,

$$
\int_e f_-\frac{dq}{q}
=-2\pi\int_0^\infty f_-(iy)\,dy=-L(f_-,1),
\tag{8.16h}
$$

while the two-circuit calculation in (8.16d)--(8.16f) gives
$\int_\Gamma dx/(2y+1)=-2\Omega_0=-\Omega^+$. Therefore

$$
3L(f_-,1)=\Omega^+.
\tag{8.17}
$$

This is the exact rational identity behind (8.12). It identifies $E_-$ as the winding factor. The other factor has vanishing central value, but no conclusion about its Mordell--Weil rank is needed. Thus the winding quotient is $E_-$, not the whole Jacobian.

### 8.5 The three fibers and all rational points

Because every rational point of $C$ maps under $\phi_-$ to one of

$$
O,
\qquad
Q=(8,18),
\qquad
-Q=(8,-19),
$$

it remains only to compute three fibers. From (8.7)--(8.8),

$$
\phi_-^{-1}(O)
=\{(0,\sqrt{37}),(0,-\sqrt{37})\},
\tag{8.18}
$$

$$
\phi_-^{-1}(Q)
=\{(1,4),(-1,-4)\},
\tag{8.19}
$$

and

$$
\phi_-^{-1}(-Q)
=\{(1,-4),(-1,4)\}.
\tag{8.20}
$$

For example, $x=8$ in (8.7) gives $u^2=1$, and the $y$-coordinate then gives the signs in (8.19)--(8.20). The fiber (8.18) has no rational point. The two points at infinity are not rational either. Hence

$$
\boxed{
C(\mathbf Q)=
\{(1,4),(-1,4),(1,-4),(-1,-4)\}.}
\tag{8.21}
$$

As a reduction check,

$$
C(\mathbf F_3)
=\{(0,\pm1),(1,\pm1),(-1,\pm1)\},
\tag{8.22}
$$

and the four rational points occupy the four residue classes with $u=\pm1$.

### 8.6 Cusps and the two $j$-values

The cusp normalization (8.3) identifies $(1,4)$ and $(-1,4)$ as the two
cusps. The remaining points are noncuspidal and are exchanged by $w_{37}$.
Before displaying $j$, it is useful to record the modular unit which checks
both cusp labels. Put

$$
g(u)=6u^3-10u.
\tag{8.22a}
$$

Then

$$
v^2-g(u)^2=-37(u^2-1)^3,
\qquad
h=\frac{v+g(u)}{(u+1)^3},
\qquad
h\circ w_{37}=\frac{37}{h}.
\tag{8.22b}
$$

The cancellations in (8.22b) give

$$
\operatorname{div}(h)=3(c_\infty-c_0).
\tag{8.22c}
$$

In the parameters (8.1b) and (8.3a),

$$
\begin{aligned}
h&=37q^3(1+2q+5q^2+10q^3+20q^4+36q^5+65q^6+O(q^7)),\\
h&=q_0^{-3}(1-2q_0-q_0^2+2q_0^3+q_0^4+2q_0^5-2q_0^6+O(q_0^7)).
\end{aligned}
\tag{8.22d}
$$

Equivalently,

$$
h=37\left(\frac{\eta(37\tau)}{\eta(\tau)}\right)^2.
\tag{8.22e}
$$

The eta product proves (8.22c) directly and its transformation law proves the
Atkin--Lehner formula in (8.22b).

Here is an explicit degree-$38$ source $j$-map. Let

$$
A(u)=\sum_{k=0}^{38}A_ku^k,\qquad
B(u)=\sum_{k=0}^{35}B_ku^k,
\tag{8.22f}
$$

where, in increasing order of $k$,

$$
\begin{aligned}
(A_k)=({}&-2478761487567000,-7305168148435800,904218550326185,
22848066502482966,\\
&17853777511718158,-19562454283353586,-31305822456742271,
-5006586672831416,\\
&13665520831967704,12187169363559560,5963719239019164,
-608251175518816,\\
&-4315965766567824,-3043349732012896,-890036230898388,
86501040355720,\\
&471139427087208,388119677172568,147227101014214,35729385767452,
-5144969449764,\\
&-16231037035828,-8606145613626,-3415577348840,-1338373543928,
-161659095528,\\
&28205163196,24219438096,25317502784,7274245584,2016349484,
802394136,\\
&45163088,20619360,4485177,-461538,681318,58806,35937),
\end{aligned}
\tag{8.22g}
$$

and

$$
\begin{aligned}
(B_k)=({}&-407505882420000,-1200962344491000,88076285497175,
3577669442405790,\\
&2894130547772370,-2843718134599738,-4718742759728526,
-812065502202306,\\
&1924692603576690,1605650957699270,733191673358958,
-22818333181866,\\
&-461566071935526,-334412368837602,-96639379222710,
-2314557177578,\\
&32491425760794,30449392904334,11701048456892,3203662855386,
559189504886,\\
&-559816242862,-335332825866,-110262055942,-56806436842,
-11358832686,\\
&-1055262078,-875854158,200418654,78977610,15278670,17644338,
3033342,\\
&989010,205821,0).
\end{aligned}
\tag{8.22h}
$$

Then

$$
\boxed{\displaystyle
j(u,v)=\frac{8(A(u)+vB(u))}{(u-1)(u+1)^{37}}.}
\tag{8.22i}
$$

This long polynomial is a certificate rather than unexplained data. Substituting
(8.1b) and (8.3a) gives

$$
\begin{aligned}
j(u(q),v(q))&=q^{-1}+744+196884q+21493760q^2+\cdots,\\
j(u(q_0),v(q_0))&=q_0^{-37}+744
 +0q_0+\cdots+0q_0^{36}+196884q_0^{37}+\cdots.
\end{aligned}
\tag{8.22j}
$$

The first line is the standard source $j$-series and the second has the width
$37$ required at the other cusp. The only poles are therefore
$c_\infty+37c_0$. Conversely, Riemann--Roch gives
$\dim L(c_\infty+37c_0)=37$; matching the two displayed principal parts and
the constant term determines (8.22i). This is an independently checkable
modular-function certificate for the degeneracy map.

There is also a short exact evaluation certificate which avoids taking a
thirty-seventh derivative at $u=-1$. Write

$$
F(u)=-u^6-9u^4-11u^2+37,\qquad
A(u)^2-F(u)B(u)^2=(u-1)(u+1)^{37}S(u).
\tag{8.22k}
$$

Polynomial division is exact. Direct summation of (8.22g)--(8.22h) gives

$$
\begin{array}{c|cc}
u&S(u)&A(u)+4B(u)\\ \hline
1&40016210296832&-2^{35}\\
-1&698694641568221202734907392&-2^{35}.
\end{array}
\tag{8.22l}
$$

At the noncuspidal points $v=-4$, rationalizing (8.22i) gives
$j=8S(u)/(A(u)-vB(u))$. Therefore

$$
j(1,-4)=-7\cdot11^3,
\tag{8.23}
$$

$$
j(-1,-4)=-7\cdot137^3\cdot2083^3,
\tag{8.24}
$$

exactly. Finally set $j_{\rm src}=j$ and
$j_{\rm tgt}=j\circ w_{37}$. Then

$$
\begin{array}{c|cc}
P&j_{\rm src}(P)&j_{\rm tgt}(P)\\ \hline
(1,-4)&-7\cdot11^3&-7\cdot137^3\cdot2083^3\\
(-1,-4)&-7\cdot137^3\cdot2083^3&-7\cdot11^3.
\end{array}
\tag{8.24a}
$$

Thus $w_{37}$ exchanges source and target exactly as duality requires. Neither
value is $0$ or $1728$, so generic coarse descent supplies an actual rational
cyclic $37$-isogeny.

## 9. Existence at the genus-zero and level-$17$ primes

### 9.1 Certified Hauptmodul formulas

For

$$
p=2,3,5,7,13,
\tag{9.1}
$$

the curve $X_0(p)$ has genus zero and two rational cusps. Choose a rational coordinate $t$ for which the two cusps are $0$ and $\infty$. One degeneracy map to $X(1)$ is

$$
\begin{aligned}
j_2(t)&=\frac{(t+16)^3}{t},\\
j_3(t)&=\frac{(t+27)(t+3)^3}{t},\\
j_5(t)&=\frac{(t^2+10t+5)^3}{t},\\
j_7(t)&=
\frac{(t^2+13t+49)(t^2+245t+2401)^3}{t^7},\\
j_{13}(t)&=
\frac{(t^2+5t+13)
(t^4+7t^3+20t^2+19t+1)^3}{t}.
\end{aligned}
\tag{9.2}
$$

These formulas require a modular certificate; genus zero alone would allow innumerably many unrelated rational functions. There are two equivalent exact certificates.

First, take the eta-quotient Hauptmodul with the scaling and orientation fixed by its leading term at a chosen cusp. Its eta transformation law gives the two cusp orders and the Atkin--Lehner action. Expanding the right sides of (9.2) at both cusps gives the standard $j$-series

$$
j(q)=q^{-1}+744+196884q+\cdots
\tag{9.3}
$$

with the appropriate cusp width for the chosen degeneracy map. The difference between the modular $j$-map and the displayed rational function has no poles and vanishes at a cusp, so it is zero.

Second, let

$$
j_p'(t)=j_p(w_pt)
$$

be the other degeneracy map. After denominators are cleared, direct polynomial substitution gives

$$
\Phi_p(j_p(t),j_p'(t))=0,
\tag{9.4}
$$

where $\Phi_p$ is the classical modular polynomial. The cusp divisors distinguish the cyclic component from any accidental component of the plane relation. Either argument identifies (9.2) as functions on $X_0(p)$, so their rational values are genuine modular points.

### 9.2 A noncuspidal specialization at each genus-zero level

The value $t=1$ is neither cusp. Substitution gives

$$
\begin{array}{c|c}
p&j_p(1)\\ \hline
2&17^3\\
3&28\cdot4^3\\
5&16^3\\
7&63\cdot2647^3\\
13&19\cdot48^3.
\end{array}
\tag{9.5}
$$

None of these values is $0$ or $1728$. The generic coarse descent of Section 1.4 therefore turns the rational modular point into a pair $(E,C)/\mathbf Q$. Consequently every prime in (9.1) occurs as the degree of a rational cyclic isogeny.

The argument proves more than isolated existence: varying $t\in\mathbf Q\setminus\{0\}$ away from the second cusp gives rational families. For the present classification, however, the five exact specializations in (9.5) are sufficient certificates.

### 9.3 The level-$17$ modular point

The remaining non-CM degree below $19$ is certified on the pointed modular curve

$$
X_0(17):\quad
y^2+xy+y=x^3-x^2-x-14.
\tag{9.6}
$$

Take $O$ as one cusp and put

$$
P=(7,13).
$$

The group law gives

$$
2P=\left(\frac{11}{4},-\frac{15}{8}\right),
\qquad
3P=(7,-21),
\qquad
4P=O.
\tag{9.7}
$$

The point $2P$ is visibly fixed by negation because $2y+x+1=0$. Counts at two good primes give

$$
\#X_0(17)(\mathbf F_3)=4,
\qquad
\#X_0(17)(\mathbf F_7)=4.
\tag{9.8}
$$

Thus rational torsion has order at most four, and $P$ generates it. The modular-symbol identity

$$
\frac{L(E_{17},1)}{\Omega^+}=\frac14
\tag{9.9}
$$

and Book 69's rank-zero theorem give rank zero. Hence

$$
X_0(17)(\mathbf Q)=\langle P\rangle\simeq\mathbf Z/4\mathbf Z.
\tag{9.10}
$$

To certify the word “modular” in (9.6), the invariant differential

$$
\frac{dx}{2y+x+1}
$$

has normalized cusp expansion beginning $q-q^2+O(q^4)$. The weight-two Sturm bound at level $17$ is

$$
\left\lfloor\frac2{12}\cdot18\right\rfloor=3,
$$

so its coefficients through $q^3$, together with $U_{17}=1$, identify the unique level-$17$ newform and its optimal curve. The cusp expansion of the pointed map identifies $O$ and $P$ as the two cusps; the Atkin--Lehner involution is

$$
w_{17}(R)=P-R.
\tag{9.11}
$$

It follows that $2P$ and $3P$ are the two noncuspidal modular points and are exchanged by $w_{17}$. The degree-$18$ $j$-function is fixed by its pole divisor at $O,P$ and its two cusp expansions. Its exact evaluations are

$$
\left\{
j(2P),j(3P)
\right\}
=
\left\{
-\frac{17^2\cdot101^3}{2},
-\frac{17\cdot373^3}{2^{17}}
\right\}.
\tag{9.12}
$$

Equivalently, substituting the two values into $\Phi_{17}(X,Y)$ gives zero. Thus (9.6), (9.7), the cusp labels, and (9.12) are an actual rational modular-point certificate for the $17$-isogeny and its dual. Neither $j$-value is exceptional, so generic coarse descent applies. Their denominators also explain why no $2$-adic cusp rigidity may be assumed.

## 10. CM existence and the exceptional coarse fibers

### 10.1 Ramified CM kernels

Let

$$
p\equiv3\pmod4,
\qquad
K=\mathbf Q(\sqrt{-p}),
\tag{10.1}
$$

and suppose $K$ has class number one. Its maximal order has discriminant $-p$. The corresponding CM $j$-invariant is rational, so there is an elliptic curve $E/\mathbf Q$ with complex multiplication by $\mathcal O_K$ over $K$.

The element $\sqrt{-p}\in\mathcal O_K$ has norm $p$. Hence the CM endomorphism

$$
[\sqrt{-p}]:E_K\longrightarrow E_K
\tag{10.2}
$$

has degree $p$, and its kernel $C$ is cyclic of order $p$. Every element of $G_K$ preserves $C$. Complex conjugation sends the endomorphism to its negative, but

$$
\ker[\sqrt{-p}]=\ker[-\sqrt{-p}].
\tag{10.3}
$$

Therefore $C$ is stable under all of $G_{\mathbf Q}$. It descends as a rational subgroup scheme and gives a rational degree-$p$ isogeny.

The endomorphism itself need not descend to $\mathbf Q$. Its quotient is generally a quadratic twist of $E$, not the same curve with a rational CM endomorphism. The stable kernel in (10.3) is the correct descent object.

### 10.2 The five required CM degrees

For the five degrees needed here, the class-number-one CM values and kernels are

$$
\begin{array}{c|c|c}
p&j(E)&\text{rational kernel}\\ \hline
11&-32^3&\ker[\sqrt{-11}]\\
19&-96^3&\ker[\sqrt{-19}]\\
43&-960^3&\ker[\sqrt{-43}]\\
67&-5280^3&\ker[\sqrt{-67}]\\
163&-640320^3&\ker[\sqrt{-163}].
\end{array}
\tag{10.4}
$$

Each row is an existence proof independent of the elimination. The first two supply degrees $11$ and $19$, and the final three supply exactly the large balanced candidates produced in Chapter 7.

For $j\ne0,1728$, an explicit rational curve with prescribed $j$ may be taken as

$$
E_j:\quad
y^2+xy=x^3-\frac{36}{j-1728}x-\frac1{j-1728}.
\tag{10.5}
$$

The CM construction, not formula (10.5) alone, supplies the stable kernel.

### 10.3 Direct treatment of $j=0$ and $j=1728$

The exceptional coarse fibers are best handled before the classification is assembled. Every rational twist with $j=0$ has a model

$$
E_d:\quad y^2=x^3+d.
\tag{10.6}
$$

Its $3$-division polynomial is

$$
\psi_3(x)=3x^4+12dx=3x(x^3+4d).
\tag{10.7}
$$

The rational factor $x$ cuts out a Galois-stable pair of nonzero points together with the origin, hence the rational ramified CM $3$-kernel. A generator need not be rational: its $y$-coordinate is a square root of $d$.

Every rational twist with $j=1728$ has a model

$$
E_d:\quad y^2=x^3+dx.
\tag{10.8}
$$

The factor $x$ of the $2$-division polynomial gives the rational point $(0,0)$ and the ramified CM $2$-isogeny.

The cross-fiber small case at $j=0$ is not uniform in the twist, but it also
has actual representatives.  For example,

$$
y^2=x^3+1
$$

has the rational point $(-1,0)$ of order $2$.  This supplies the exceptional
$j=0$ coarse fiber at degree $2$ directly; it is not a ramified CM kernel and
is not asserted for every sextic twist.

For $p\ge5$, these exceptional CM fibers supply no additional rational line. If $p$ splits in the CM field, the two CM eigenspaces are conjugate under the nontrivial element of $\operatorname{Gal}(K/\mathbf Q)$, so neither is a $G_{\mathbf Q}$-stable line. If $p$ is inert, the nonsplit Cartan action is irreducible over $\mathbf F_p$. The only ramified rational CM kernels occur at $3$ for $j=0$ and at $2$ for $j=1728$. A quadratic, quartic, or sextic twist multiplies the representation by a scalar character and does not stop conjugation from exchanging the two split eigenspaces or make an inert Cartan preserve a line.

Thus the direct division-polynomial calculation accounts for the rational exceptional kernels, and twists do not repair the obstruction for any $p\ge5$. No blanket assertion about descent from the coarse exceptional fiber has been used.

## 11. The prime-isogeny classification

### 11.1 Elimination

Let $E/\mathbf Q$ admit a rational cyclic isogeny of prime degree $p$. If $p\le19$, then primality alone gives

$$
p\in\{2,3,5,7,11,13,17,19\}.
\tag{11.1}
$$

Suppose $p>19$. The actual pair $(E,C)$ gives a noncuspidal rational point of $X_0(p)$. Odd cusp rigidity at $5,7,11$ proves the three integrality statements (4.5). The local isogeny-character theorem and global reciprocity give one of the five signatures in (3.8).

For $s=4,8$, the gcd certificate (5.18) is divisible by no prime greater than $19$, so these signatures are impossible. For $s=0,12$, the gcd certificate (5.17) leaves $31,37$, and the $\mathbf F_{31}$ trace table (5.22)--(5.24) removes $31$. Thus the endpoint branch leaves $37$.

For $s=6$, the three-place argument in Section 6.1 makes $j(E)$ integral. The balanced class-field theorem yields

$$
p\equiv3\pmod4,
\qquad
h(\mathbf Q(\sqrt{-p}))=1.
$$

The independent class-number-one theorem, intersected with $-p$ in Section 7.2, leaves $43,67,163$. Therefore

$$
p\in
\{2,3,5,7,11,13,17,19,37,43,67,163\}.
\tag{11.2}
$$

No theorem used in this paragraph already outputs the set (11.2). The local theorem outputs five exponents; the stable trace lemma outputs a Hasse-bounded quadratic; the balanced theorem outputs a class-number condition; and the class-number theorem is independent of isogenies. The finite intersections were carried out in this book.

### 11.2 Existence

Existence at every prime in (11.2) is now certified as follows.

$$
\begin{array}{c|l}
\text{degree}&\text{certificate}\\ \hline
2,3,5,7,13&\text{the certified Hauptmodul point }t=1\text{ in (9.5)}\\
11&j=-32^3,\quad\ker[\sqrt{-11}]\\
17&2P,3P\in X_0(17)(\mathbf Q)\text{ in (9.7)--(9.12)}\\
19&j=-96^3,\quad\ker[\sqrt{-19}]\\
37&(1,-4),(-1,-4)\in X_0(37)(\mathbf Q)\text{ in (8.21)--(8.24)}\\
43&j=-960^3,\quad\ker[\sqrt{-43}]\\
67&j=-5280^3,\quad\ker[\sqrt{-67}]\\
163&j=-640320^3,\quad\ker[\sqrt{-163}].
\end{array}
\tag{11.3}
$$

The genus-zero and non-CM points have $j\ne0,1728$, so their pointed modular-curve certificates and generic coarse descent give rational subgroups. The CM rows start with the subgroup itself and therefore bypass coarse descent entirely.

Combining elimination and existence proves the classification:

$$
\boxed{
p\text{ occurs as a rational prime-isogeny degree over }\mathbf Q
\Longleftrightarrow
p\in\{2,3,5,7,11,13,17,19,37,43,67,163\}.}
\tag{11.4}
$$

### 11.3 Mechanism and dependency ledger

The list has three visibly different sources.

| Mechanism | Degrees | Arithmetic certificate |
|---|---|---|
| genus-zero families | $2,3,5,7,13$ | rational Hauptmodul and modular $j$-map |
| isolated non-CM points | $17,37$ | exact Mordell--Weil and quotient-fiber calculations |
| ramified class-number-one CM kernels | $11,19,43,67,163$ | $G_{\mathbf Q}$-stable kernel of $[\sqrt{-p}]$ |

The elimination uses the odd winding-quotient interface only to prove (4.5). It never declares the full Jacobian finite. At level $37$ both elliptic quotient directions were displayed, but only the rank-zero winding factor $E_-$ enters the rational-point proof. No rational torsion on $E_-$ was inferred from rational torsion on $J_0(37)$, and no Mordell--Weil claim about $E_+$ is required.

## 12. The independent prime-torsion theorem

### 12.1 The exact independent theorem

The Frey argument needs only prime-order rational torsion. We use the following
deep theorem at exactly that strength.

**Independent prime-torsion theorem.** Let $E$ be an elliptic curve over
$\mathbf Q$, and let $P\in E(\mathbf Q)$ have exact prime order $p$. Then

$$
\boxed{p\in\{2,3,5,7\}.}
\tag{12.1}
$$

The hypotheses say that a generator, not merely its cyclic subgroup, is
$\mathbf Q$-rational. The theorem is established $X_1$ infrastructure. It is
independent of the rational $X_0(p)$ classification in Chapter 11: neither its
statement nor its proof uses a list of rational prime-isogeny degrees. We do
not import the full classification of rational torsion groups, because no such
classification is needed below.

### 12.2 The oriented $X_1(p)$ proof architecture

Here is the dependency capsule for (12.1). For $p\ge5$, the fine
$\Gamma_1(p)$ moduli problem associates to $(E,P)$ a noncuspidal rational
point of $Y_1(p)$. Its compactification remembers an oriented generator on a
Tate polygon at the boundary; forgetting that generator would change the
problem to $X_0(p)$ and would destroy the argument.

At an auxiliary prime $q\ne p$, properness gives a section of the integral
$X_1(p)$ model. If its reduction is smooth and interior, the prime-to-$q$
point $P$ specializes with exact order $p$. Hence

$$
p\mid\#\widetilde E(\mathbf F_q),
\qquad
\#\widetilde E(\mathbf F_q)\le q+1+2\sqrt q.
\tag{12.2}
$$

The reduction analysis also treats multiplicative fibers as oriented cusps.
The Weil pairing rules out two independent rational $p$-directions and fixes
the determinant character used to distinguish the oriented cusp branches.
Using $q=2$ and, where the integral fiber requires it, $q=3$, one is therefore
reduced to an oriented cusp disk for every prime $p\ge17$.

The decisive input is the **oriented prime-level formal-immersion theorem**:
for every prime $p\ge17$, the Abel--Jacobi map from $X_1(p)$ to its oriented
winding quotient is a formal immersion at the cusp reached by such a rational
section, and the rational torsion of that exact quotient has trivial
specialization kernel in the residue characteristic used in the reduction.
It follows that the section is the cusp. This theorem is proved on the fine
$X_1(p)$ integral model, using oriented cuspidal divisors, integral
cotangents, reduction of the chosen generator, and the winding quotient cut
out by nonzero central values. In residue characteristic $2$ its
connected--étale calculation is part of the theorem; it is not inferred from
any statement about $J_0(p)$ or from Book 69's odd-prime $X_0$ interface.

The finite levels not covered by that uniform step are $p=11$ and $p=13$.
The standard genus-one calculation on $X_1(11)$ and genus-two descent on
$X_1(13)$ show that all their rational points are cuspidal. The levels
$2,3,5,7$ have noncuspidal rational points, as Tate normal form also shows.
This completes the architecture of (12.1).

This capsule fixes the theorem's scope and dependencies; it does not claim a
uniform family of Manin-symbol row reductions or specialization kernels. The
oriented formal-immersion theorem is used as
established infrastructure in the same sense that Book 69 uses the
Kolyvagin--Logachev rank-zero theorem. Its output is precisely (12.1), and it
has no dependency on Chapter 11.

### 12.3 Tate normal form and the two mixed-torsion curves

The prime-torsion theorem leaves $p=5$ and $7$. For the Frey application these
must be excluded on a curve which also has full rational $2$-torsion. We do
that directly.

A point $P$ of exact order at least four can be put in Tate normal form

$$
E(b,c):\quad
y^2+(1-c)xy-by=x^3-bx^2,
\qquad P=(0,0),
\tag{12.3}
$$

with $b\ne0$ and nonzero discriminant. Direct use of the group law gives the
prime-order specializations

$$
\begin{array}{c|cc}
\operatorname{ord}(P)&b&c\\ \hline
5&t&t\\
7&t^3-t^2&t^2-t.
\end{array}
\tag{12.4}
$$

The $x$-coordinates of the nonzero $2$-torsion are the roots of

$$
F_{b,c}(X)
=4X^3+\bigl((1-c)^2-4b\bigr)X^2
 +2b(c-1)X+b^2.
\tag{12.5}
$$

Full rational $2$-torsion makes $F_{b,c}$ split over $\mathbf Q$, so its
discriminant must be a rational square. Substitution of the two rows of
(12.4) gives the exact identities

$$
\operatorname{disc}F_{t,t}
=16t^5(t^2-11t-1),
\tag{12.6}
$$

and

$$
\operatorname{disc}F_{t^3-t^2,t^2-t}
=16t^7(t-1)^7(t^3-8t^2+5t+1).
\tag{12.7}
$$

For $t\ne0$ in the first row, divide a square root in (12.6) by $4t^2$.
For $t\ne0,1$ in the second row, divide a square root in (12.7) by
$4t^3(t-1)^3$. Thus full rational $2$-torsion would give a nondegenerate
rational point on, respectively,

$$
C_5:\quad z^2=t(t^2-11t-1)
\tag{12.8}
$$

or

$$
C_7:\quad z^2=t(t-1)(t^3-8t^2+5t+1).
\tag{12.9}
$$

Only this necessary implication is used; no converse from a square
discriminant to a split cubic is asserted.

### 12.4 The elliptic certificate for $C_5$

The odd-degree projective completion of $C_5$ has one point at infinity. With
that point as origin, the explicit Weierstrass transformation and its inverse
are simply

$$
(x,y)=(t,z),
\qquad
(t,z)=(x,y),
\tag{12.10}
$$

On projective models this is $[T:Z:W]\mapsto[X:Y:W]=[T:Z:W]$ between

$$
Z^2W=T(T^2-11TW-W^2)
\quad\text{and}\quad
Y^2W=X^3-11X^2W-XW^2;
$$

the inverse is the same coordinate substitution and sends $[0:1:0]$ to the
origin.

The resulting elliptic curve is

$$
E_5:\quad y^2=x^3-11x^2-x.
\tag{12.11}
$$

Its discriminant is $2^4\cdot5^3$. The rational point $(0,0)$ gives a
$2$-isogeny

$$
\begin{aligned}
\varphi:E_5&\longrightarrow E_5',\\
(x,y)&\longmapsto
\left(\frac{y^2}{x^2},-\frac{y(x^2+1)}{x^2}\right),
\end{aligned}
\qquad
E_5':Y^2=X^3+22X^2+125X.
\tag{12.12}
$$

The two isogeny-descent maps are

$$
\begin{array}{c|ccc}
& O&(0,0)&\text{otherwise}\\ \hline
\delta:E_5(\mathbf Q)/\widehat\varphi E_5'(\mathbf Q)
 &1&-1&x\\
\delta':E_5'(\mathbf Q)/\varphi E_5(\mathbf Q)
 &1&5&X
\end{array}
\quad\text{in }\mathbf Q^\times/\mathbf Q^{\times2}.
\tag{12.13}
$$

The complete local-image ledger is

| map and class | $\mathbf R$ | $\mathbf Q_2$ | $\mathbf Q_5$ | conclusion |
|---|---|---|---|---|
| $\delta:1$ | soluble | soluble | soluble | $O$ is a global witness |
| $\delta:-1$ | soluble | soluble | soluble | $(0,0)$ is a global witness |
| $\delta':1$ | soluble | soluble | soluble | $O$ is a global witness |
| $\delta':5$ | soluble | soluble | soluble | $(0,0)$ is a global witness |
| $\delta':-1,-5$ | insoluble | -- | -- | excluded over $\mathbf R$ |

For $E_5$, the squarefree representative of an image class divides the
coefficient $-1$, so

$$
\operatorname{im}\delta=\{1,-1\}.
$$

For $E_5'$, it divides $125$ and hence lies in
$\{1,-1,5,-5\}$. But

$$
X^2+22X+125=(X+11)^2+4>0,
$$

so every real affine point of $E_5'$ has $X\ge0$. The two negative classes
are impossible, while $O$ and $(0,0)$ realize $1$ and $5$. Therefore

$$
\operatorname{im}\delta'=\{1,5\}.
\tag{12.14}
$$

The $2$-isogeny rank formula now gives

$$
2^{\operatorname{rank}E_5(\mathbf Q)}
=\frac{\#\operatorname{im}\delta\,
       \#\operatorname{im}\delta'}4=1.
\tag{12.15}
$$

The good-reduction counts are

$$
\#E_5(\mathbf F_3)=6,
\qquad
\#E_5(\mathbf F_7)=6,
\tag{12.16}
$$

so rational torsion has order dividing $6$. The $3$-division polynomial is

$$
\psi_3(x)=3x^4-44x^3-6x^2-1
=(3x+1)(x^3-15x^2+3x-1).
\tag{12.17}
$$

The cubic factor has no rational root. At the remaining rational root
$x=-1/3$, the curve equation gives $y^2=-25/27$, so there is no rational
point of order $3$. Consequently

$$
E_5(\mathbf Q)=\{O,(0,0)\},
\qquad
\boxed{C_5(\mathbf Q)=\{\infty,(0,0)\}.}
\tag{12.18}
$$

The affine point has $t=0$, hence $b=0$ in (12.4), and the point at infinity
is a boundary point. Both are degenerate or cuspidal Tate parameters.

### 12.5 The genus-two certificate for $C_7$

Write

$$
f(t)=t^5-9t^4+13t^3-4t^2-t
=t(t-1)(t^3-8t^2+5t+1)
\tag{12.19}
$$

The degree-five model has one rational point $\infty$ at infinity. Let
$J=\operatorname{Jac}(C_7)$ and use $\infty$ as the Abel--Jacobi base point.
We use Mumford notation $[u,v]$, with
$u$ monic, $\deg v<\deg u\le2$, and $u\mid f-v^2$. Put

$$
T_0=[t,0],
\qquad
T_1=[t-1,0],
\qquad
A=[t^2-t+1,1-3t].
\tag{12.20}
$$

The first two classes are independent points of order $2$. Exact polynomial
division gives

$$
f-(1-3t)^2=(t^2-t+1)(t^3-8t^2+4t-1),
\tag{12.21}
$$

and one Cantor reduction gives

$$
2A=[t^2-t+1,3t-1]=-A.
\tag{12.22}
$$

Thus $A$ has exact order $3$.

The rank certificate begins with the two-descent algebra

$$
L=\mathbf Q\times\mathbf Q\times K,
\qquad
K=\mathbf Q(\theta),\quad
\theta^3-8\theta^2+5\theta+1=0.
\tag{12.23}
$$

Let $\alpha^3+\alpha^2-2\alpha-1=0$. Direct substitution gives

$$
K=\mathbf Q(\alpha),
\qquad
\theta=-1-\alpha+2\alpha^2,
\qquad
K=\mathbf Q(\zeta_7+\zeta_7^{-1}),
\qquad
\left[\mathcal O_K:\mathbf Z[\theta]\right]=7,
\qquad
\operatorname{disc}(\mathcal O_K)=49.
\tag{12.24}
$$

The Minkowski bound is $14/9<2$, so $K$ has class number one. The cyclotomic
unit index formula in this real cubic field then makes $\alpha$ and
$\alpha+1$ fundamental units; its unit squareclasses are generated by
$-1,\alpha,\alpha+1$. Direct norm evaluation gives

$$
N(\alpha)=1,
\qquad
N(\alpha+1)=-1,
\qquad
N(2-\alpha)=7.
$$

The identities

$$
\theta=\frac{\alpha^3}{\alpha+1},
\qquad
1-\theta=\frac{\alpha^2}{(\alpha+1)^3}
$$

give the squareclasses in (12.26) directly in this unit basis.

Thus the prime above $7$ is generated by $2-\alpha$. The polynomial
$X^3+X^2+1$ has no root over $\mathbf F_2$, so $2$ is inert. Since
$\operatorname{disc}(f)=7^4$, the descent is unramified outside
$S=\{2,7,\infty\}$.

For a divisor disjoint from the Weierstrass points, the descent map is

$$
\delta([u,v])=
\bigl((-1)^{\deg u}u(0),
      (-1)^{\deg u}u(1),
      (-1)^{\deg u}u(\theta)\bigr)
\in L^\times/L^{\times2},
\tag{12.25}
$$

with the usual derivative value in a component containing a Weierstrass
point. In particular,

$$
\delta(T_0)=(-1,-1,-\theta),
\qquad
\delta(T_1)=(1,-1,1-\theta).
\tag{12.26}
$$

The $S$-unit norm kernel has dimension eight over $\mathbf F_2$. It is
regenerated from

$$
-1,\ \alpha,\ \alpha+1,\ 2,\ 2-\alpha
\tag{12.27}
$$

in the cubic component and $-1,2,7$ in each rational component. More
explicitly, if $e_i=\delta(T_i)$, a basis of the norm kernel is

$$
\begin{aligned}
e_0, e_1,\quad
h_1&=(-1,1,-1),& h_2&=(1,-1,-1),\\
h_3&=(2,1,2),& h_4&=(1,2,2),\\
h_5&=(7,1,2-\alpha),& h_6&=(1,7,2-\alpha).
\end{aligned}
\tag{12.27a}
$$

The entries are in the two rational components and then the cubic component;
their norms are respectively $1,1,16,16,49,49$.  Put $V$ for the
eight-dimensional space in (12.27a), and write $\delta_v$ for the localized
descent map.  The real sign calculation and the $2$-adic squareclass
calculation give, inside $V$,

$$
\begin{aligned}
V\cap\delta_\infty(J(\mathbf R))
 &=\langle e_0,e_1,h_3,h_4,h_5,h_6\rangle,\\
V\cap\delta_2(J(\mathbf Q_2))
 &=\langle e_0,e_1,h_1+h_5,h_2+h_6\rangle.
\end{aligned}
\tag{12.27b}
$$

Here addition denotes multiplication of squareclasses.  These two displayed
subspaces can be checked directly.  The real place
uses the signs at the five real factors of $L$.  At $2$, the polynomial
$X^3+X^2+1$ is irreducible, so $K_2/\mathbf Q_2$ is unramified of degree
three.  Squareclasses in each rational component are determined by valuation
parity and the odd residue modulo $8$, and unit squareclasses in $K_2$ are
determined modulo $8\mathcal O_{K,2}$.  Reducing the eight columns of
(12.27a) by these tests gives the second line of (12.27b).

For an independent dimension check, a non-Weierstrass point with coordinate
$x$ has descent value

$$
(x,x-1,x-\theta).
\tag{12.27c}
$$

The two values

$$
f(-4)=-4220=4(-1055),\qquad
f(13)=142116=4(35529)
\tag{12.27d}
$$

are squares in $\mathbf Q_2$, since both parenthesized odd units are $1$
modulo $8$.  The classes of the resulting two local points, together with
$e_0,e_1$, are independent under the preceding residue tests.  On the other
hand,

$$
\dim_{\mathbf F_2}J(\mathbf Q_2)/2J(\mathbf Q_2)
=2+\dim_{\mathbf F_2}J(\mathbf Q_2)[2]=4,
\tag{12.27e}
$$

because the two rational Weierstrass classes generate $J(\mathbf Q_2)[2]$.
Thus these four values are the full local Kummer image and certify, rather
than merely suggest, the second line of (12.27b).

Intersecting the two lines of (12.27b) leaves exactly
$\langle e_0,e_1\rangle$.  At $7$, the cubic factor remains irreducible and
$J(\mathbf Q_7)[2]=\langle T_0,T_1\rangle$.  Since $2$ is a unit in
$\mathbf Z_7$, multiplication by $2$ is an automorphism on a pro-$7$ open
subgroup of $J(\mathbf Q_7)$; on the finite quotient, the cokernel of
multiplication by $2$ has the same order as its kernel.  Hence

$$
\dim_{\mathbf F_2}J(\mathbf Q_7)/2J(\mathbf Q_7)=2.
\tag{12.27f}
$$

The two displayed torsion classes therefore generate the full $7$-adic
Kummer image.  In particular the $7$-adic condition leaves the common
intersection unchanged.  The exact sequential dimension ledger is therefore

$$
\begin{array}{c|c}
\text{space}&\mathbf F_2\text{-dimension}\\ \hline
S\text{-unit norm kernel}&8\\
\text{after the real image}&6\\
\text{after the }2\text{-adic image}&2\\
\text{after the }7\text{-adic image}&2.
\end{array}
\tag{12.28}
$$

With columns ordered as in (12.27a), the sign and $2$-adic residue tests have
the following obstruction matrix.  Its common kernel is visibly
$\langle e_0,e_1\rangle$:

$$
\begin{array}{c|cc|cccccc}
&e_0&e_1&h_1&h_2&h_3&h_4&h_5&h_6\\ \hline
\mathbf R&0&0&1&0&0&0&0&0\\
\mathbf R&0&0&0&1&0&0&0&0\\
\mathbf Q_2&0&0&0&0&1&0&0&0\\
\mathbf Q_2&0&0&0&0&0&1&0&0\\
\mathbf Q_2&0&0&1&0&0&0&1&0\\
\mathbf Q_2&0&0&0&1&0&0&0&1
\end{array}.
\tag{12.29}
$$

All entries are squareclass tests in the explicit algebra (12.23). It follows
that

$$
\operatorname{Sel}^{(2)}(J/\mathbf Q)
=\langle\delta(T_0),\delta(T_1)\rangle,
\qquad
\operatorname{rank}J(\mathbf Q)=0.
\tag{12.30}
$$

The torsion and saturation check is independent. Direct point counting gives

$$
\begin{array}{c|cc|c}
q&\#C_7(\mathbf F_q)&\#C_7(\mathbf F_{q^2})
 &\#J(\mathbf F_q)\\ \hline
3&5&5&12\\
5&9&25&48.
\end{array}
\tag{12.31}
$$

Here

$$
\#J(\mathbf F_q)
=\frac{\#C_7(\mathbf F_q)^2+\#C_7(\mathbf F_{q^2})}{2}-q.
$$

The subgroup $\langle A,T_0,T_1\rangle$ has order $3\cdot2\cdot2=12$.
Rational torsion injects at the two good primes in (12.31), so its order
divides $\gcd(12,48)=12$. Together with (12.30), this proves the saturated
Mordell--Weil certificate

$$
\boxed{J(\mathbf Q)=\langle A\rangle\oplus
\langle T_0\rangle\oplus\langle T_1\rangle
\simeq\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2.}
\tag{12.32}
$$

It remains to determine which of these twelve divisor classes lie on the
embedded curve $P\mapsto[P-\infty]$. Write a class as
$nA+e_0T_0+e_1T_1$, with $n\in\mathbf Z/3$ and $e_i\in\mathbf Z/2$.
The Mordell--Weil sieve at $3$ gives the five possible triples

$$
(0,0,0),\ (0,1,0),\ (0,0,1),\ (1,1,1),\ (2,1,1).
\tag{12.33}
$$

Indeed

$$
C_7(\mathbf F_3)=
\{\infty,(0,0),(1,0),(2,1),(2,-1)\}.
$$

At $5$ one has

$$
C_7(\mathbf F_5)=
\{\infty,(0,0),(1,0),(2,\pm2),(3,\pm1),(4,\pm2)\},
$$

and intersection with the reduction of the subgroup (12.32) leaves only

$$
(0,0,0),\qquad(0,1,0),\qquad(0,0,1).
\tag{12.34}
$$

These are respectively the classes of $\infty,(0,0),(1,0)$. The Abel--Jacobi
map is injective on a genus-two curve, so recovery from the three surviving
classes is exact:

$$
\boxed{C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.}
\tag{12.35}
$$

The values $t=0$ and $t=1$ make $b=0$ in the order-$7$ row of (12.4), and
$\infty$ is a boundary point. Thus every rational point in (12.35) is
cuspidal or degenerate. Equations (12.18) and (12.35) prove

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/10\mathbf Z
\not\subset E(\mathbf Q),
\qquad
\mathbf Z/2\mathbf Z\times\mathbf Z/14\mathbf Z
\not\subset E(\mathbf Q)
\tag{12.36}
$$

for every elliptic curve $E/\mathbf Q$, independently of Chapter 11.

## 13. Semistable rational isogenies

### 13.1 An everywhere-unramified diagonal character

Let $p\ge5$ and suppose a semistable elliptic curve $E/\mathbf Q$ admits a rational $p$-isogeny with kernel character $\lambda$. At every prime $q\ne p$, good or multiplicative reduction makes $\lambda$ unramified. In the nonsplit multiplicative case the splitting character is unramified, so this assertion remains true.

At $p$, the semistable local theorem gives

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\chi_p.
\tag{13.1}
$$

In the first case $\lambda$ is unramified at every finite prime. In the second case the dual character

$$
\mu=\chi_p\lambda^{-1}
\tag{13.2}
$$

is unramified at $p$, and it is unramified at every $q\ne p$ because both factors are. Thus one of $\lambda,\mu$ is globally unramified at all finite primes.

A finite character of $G_{\mathbf Q}$ unramified at all finite primes is trivial. Indeed, its fixed field would be a finite abelian extension of $\mathbf Q$ with discriminant supported nowhere; global class field theory, or the Minkowski discriminant bound, excludes every nontrivial such extension. Consequently

$$
\lambda=1
\quad\text{or}\quad
\mu=1.
\tag{13.3}
$$

This proof uses the diagonal character itself. Raising it to the twelfth power would not imply (13.3).

### 13.2 Rational torsion on one side of the isogeny

If $\lambda=1$, the original kernel has a rational generator and

$$
E(\mathbf Q)[p]\ne0.
$$

If $\mu=1$, the kernel of the dual isogeny has a rational generator and

$$
(E/C)(\mathbf Q)[p]\ne0.
$$

We have proved the semistable isogeny theorem

$$
\boxed{
E/\mathbf Q\text{ semistable with a rational }p\text{-isogeny},\ p\ge5
\Longrightarrow
E(\mathbf Q)[p]\ne0\text{ or }(E/C)(\mathbf Q)[p]\ne0.}
\tag{13.4}
$$

Semistability is preserved under isogeny, although (13.4) only needed the local structure on the original curve and its dual character. The theorem does not assert that the original kernel is always rationally generated.

By the independent prime-torsion theorem (12.1), a semistable rational prime
isogeny with $p\ge5$ can therefore have only degree $5$ or $7$. The next
section excludes both when full rational $2$-torsion is present.

### 13.3 Odd isogenies and full two-torsion

Let $p$ be odd. The restriction of a degree-$p$ isogeny

$$
\varphi:E\longrightarrow E'=E/C
$$

to $E[2]$ is injective because its kernel has odd order. Both $E[2]$ and $E'[2]$ have four geometric points, so

$$
\varphi:E[2]\xrightarrow{\sim}E'[2]
\tag{13.5}
$$

is a Galois-equivariant isomorphism. Hence full rational $2$-torsion passes across every odd isogeny.

If $p\ge11$, (13.4) contradicts the independent theorem (12.1). If $p=5$
or $7$, the curve on the side of the isogeny carrying the rational
$p$-torsion also has full rational $2$-torsion by (13.5); equations (12.18)
and (12.35), equivalently (12.36), exclude those two possibilities. We have
therefore obtained the criterion already shaped for the Frey curve:

$$
\boxed{
E/\mathbf Q\text{ semistable with }E[2](\mathbf Q)\simeq(\mathbf Z/2)^2,
\quad p\ge5
\Longrightarrow E[p]\text{ is irreducible}.}
\tag{13.6}
$$

The next chapter verifies both hypotheses directly from the Frey equation.

## 14. The Frey curve

### 14.1 Normalization and invariants

Let $p\ge5$ be prime and suppose that

$$
a^p+b^p=c^p
\tag{14.1}
$$

is a primitive nontrivial integer solution. Thus $abc\ne0$ and $\gcd(a,b,c)=1$. Exactly one of $a,b,c$ is even. By permuting the signed three-term equation and changing all signs if necessary, we may arrange

$$
a\text{ even},
\qquad
b,c\text{ odd},
\qquad
b\equiv1\pmod4.
\tag{14.2}
$$

Put

$$
A=a^p,
\qquad
B=b^p,
\qquad
C=c^p=A+B,
$$

and define

$$
E=E_{a,b,p}:\quad
y^2=x(x-A)(x+B).
\tag{14.3}
$$

The three nonzero points of order two are

$$
(0,0),
\qquad
(A,0),
\qquad
(-B,0),
\tag{14.4}
$$

so

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
\tag{14.5}
$$

Expanding the cubic and applying the integral invariant formulas gives

$$
\begin{aligned}
c_4&=16(A^2+AB+B^2),\\
c_6&=-32(B-A)(2A^2+5AB+2B^2),\\
\Delta&=16A^2B^2C^2=2^4(abc)^{2p},\\
j&=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.
\end{aligned}
\tag{14.6}
$$

The discriminant is the square of the product of the three root differences, multiplied by $16$. That factorization makes every odd local calculation transparent; the prime $2$ still requires a minimal change of variables.

### 14.2 Odd bad primes

Let $q$ be odd. Primitivity implies that $q$ divides at most one of $a,b,c$. If $q\nmid abc$, the discriminant in (14.6) is a unit and $E$ has good reduction.

Suppose $q\mid a$. Then $B$ and $C$ are units and

$$
A^2+AB+B^2\equiv B^2\not\equiv0\pmod q.
$$

Thus $c_4$ is a unit, the displayed equation is minimal, and the reduction is multiplicative. Moreover

$$
v_q(\Delta_{\min})=2p\,v_q(a).
$$

The same argument with the other two root differences gives

$$
v_q(\Delta_{\min})=
\begin{cases}
2p\,v_q(a),&q\mid a,\\
2p\,v_q(b),&q\mid b,\\
2p\,v_q(c),&q\mid c.
\end{cases}
\tag{14.7}
$$

Therefore $E$ is semistable at every odd prime, and every odd multiplicative discriminant exponent is divisible by $p$.

### 14.3 The minimal model at two

The equation (14.3) is not minimal at $2$. From (14.2),

$$
v_2(A)=p\,v_2(a)\ge5,
\qquad
B-A\equiv1\pmod4.
\tag{14.8}
$$

Make the integral change

$$
x=4x',
\qquad
y=8y'+4x'.
\tag{14.9}
$$

After division by $64$, the equation becomes

$$
y'^2+x'y'
=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'.
\tag{14.10}
$$

Both displayed coefficients are integral by (14.8). The transformed invariants satisfy

$$
c_{4,\min}=A^2+AB+B^2,
\qquad
\Delta_{\min}=2^{-8}A^2B^2C^2.
\tag{14.11}
$$

The first is odd. Thus (14.10) is minimal and has multiplicative reduction, with

$$
v_2(\Delta_{\min})=2p\,v_2(a)-8>0.
\tag{14.12}
$$

The subtraction of $8$ is essential: it is the difference between the raw discriminant of (14.3) and the discriminant of the admissibly rescaled minimal equation. Combining (14.7) and (14.12) proves

$$
\boxed{E/\mathbf Q\text{ is semistable}.}
\tag{14.13}
$$

### 14.4 Residual inertia

Although semistability and full $2$-torsion already suffice for irreducibility, the exact local exponents are part of the Frey package needed later.

At a multiplicative prime $q\ne p$, Tate uniformization shows that inertia on $E[p]$ is trivial precisely when

$$
p\mid v_q(\Delta_{\min}).
\tag{14.14}
$$

For every odd $q\mid abc$ with $q\ne p$, equation (14.7) gives this divisibility. Therefore

$$
\overline\rho_{E,p}|_{I_q}=1
\qquad(q\mid abc,\ q\ne2,p).
\tag{14.15}
$$

At $2$, equation (14.12) gives

$$
v_2(\Delta_{\min})\equiv-8\not\equiv0\pmod p,
$$

so

$$
\overline\rho_{E,p}|_{I_2}\ne1.
\tag{14.16}
$$

At a place above $p$, residue and coefficient characteristics coincide, so criterion (14.14) is not applied. The finite-flat semistable alternatives (2.3) are the correct local statement there.

## 15. Frey irreducibility

### 15.1 The contradiction

Suppose, contrary to the desired conclusion, that

$$
\overline\rho_{E,p}
$$

is reducible. By (1.4), $E$ admits a rational cyclic $p$-isogeny

$$
\varphi:E\longrightarrow E'=E/C.
\tag{15.1}
$$

The curve $E$ is semistable by (14.13). The semistable isogeny theorem (13.4) gives

$$
E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.
\tag{15.2}
$$

The original curve has full rational $2$-torsion by (14.5), and the odd isogeny transports it to $E'$ by (13.5). Whichever curve contains the rational point of order $p$ therefore has a rational subgroup

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/2p\mathbf Z.
\tag{15.3}
$$

For $p\ge11$, the rational point in (15.2) contradicts the independent
prime-torsion theorem (12.1). For $p=5$ and $7$, the two explicit
mixed-torsion exclusions (12.18) and (12.35) contradict (15.3). This
exhausts every prime $p\ge5$ and proves

$$
\boxed{
\overline\rho_{E_{a,b,p},p}:G_{\mathbf Q}
\longrightarrow\operatorname{GL}_2(\mathbf F_p)
\text{ is irreducible}.}
\tag{15.4}
$$

### 15.2 The exponents five and seven

The independent prime-torsion theorem itself allows the exponents $5$ and
$7$, so they require the mixed-torsion calculation.

If $p=5$, equation (15.2) gives a rational point of order five on a curve with full rational $2$-torsion. Its torsion contains

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/10\mathbf Z,
\tag{15.5}
$$

which would produce a nondegenerate point on $C_5$ by (12.6)--(12.8),
contrary to the complete calculation (12.18).

If $p=7$, the corresponding forbidden subgroup is

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/14\mathbf Z.
\tag{15.6}
$$

It would produce a nondegenerate point on $C_7$ by (12.7)--(12.9), contrary
to (12.35). Thus neither exponent is hidden inside a large-prime inequality.
Both are excluded by the extra rational $2$-torsion visible in the Frey
equation.

### 15.3 All larger prime exponents

If $p\ge11$, the rational point of order $p$ in (15.2) already contradicts
(12.1), even before full $2$-torsion is used. This handles $11,13,17,19$ and
every larger prime, including the general-isogeny exceptions

$$
37,43,67,163.
$$

The proof therefore does not try to remove a Frey exponent by consulting the
classification list (11.4). Instead, semistability turns one diagonal
character into the trivial character. The independent prime-torsion theorem
then handles $p\ge11$, and the explicit $C_5,C_7$ calculations handle $5,7$.
This is strictly stronger information than general prime-isogeny
classification.

## 16. Audit and final theorem package

### 16.1 Imported infrastructure

The proof has used substantial earlier theory, but each imported result has an output strictly weaker than the classification.

| Source | Imported output | What it does not supply |
|---|---|---|
| Books 4--6 | ideles, local and global reciprocity, trivial class group of $\mathbf Q$, Minkowski bounds | no isogeny degree |
| Books 7--9 | minimal models, stable reduction, Tate curves, $E[p]$, Weil pairing | no global signature list of primes |
| Books 10--14 | finite-flat closure, connected--étale sequences, Cartier duality | no rational modular points |
| Books 15--19 | character and local--global cohomological language | no class-number enumeration |
| Books 49, 51--53 | descent of finite étale objects, Jacobians, modular curves, Hecke correspondences | no $X_0(37)(\mathbf Q)$ calculation |
| Books 67--69 | modular interpretation, stable cuspidal reduction, actual winding quotient, modular rank-zero theorem, odd cusp rigidity | no prime-isogeny classification |
| local finite-flat classification | the displayed $(e,a)$-table, the wild $2,3$ character tables, and the five exponents | no possible prime degrees |
| stable-model descent | the descended $\mathbf F_r$-form, its Hasse-bounded trace, and the quartic/sextic twist scalars | no resultant gcd |
| balanced class-field input | local reciprocity and Minkowski's bound, used in the complete proof of Section 6.3 | no list $43,67,163$ |
| class-number-one theorem | nine negative fundamental discriminants | no assertion about isogenies |
| descent and saturation theorems | the explicit $C_5$ isogeny descent and $C_7$ Jacobian rank bound | no mixed-torsion point list |
| modular-symbol and Sturm theorems | exact central-value and modular-form certificates | no replacement of the point-fiber calculation |
| independent oriented-$X_1(p)$ theorem | rational prime torsion is confined to $2,3,5,7$ | no use of Chapter 11 or any $X_0(p)$ classification |

The local character theorem itself rests on Tate uniformization, finite-flat closure, connected--étale analysis, niveau-two fundamental characters, the tame automorphism orders, and the wild $2$- and $3$-tables. The balanced theorem rests on the quadratic character (6.9), conductor analysis, Frobenius principality, Hasse lifting, and Minkowski generation. These architectures were exposed at the point of use so that neither theorem can conceal the desired final list.

### 16.2 Exact finite certificates

The load-bearing finite work can be checked from the following ledger.

| Stage | Certificate displayed in this book |
|---|---|
| auxiliary integrality | $v_r(j)\ge0$ for $r=5,7,11$ from odd cusp rigidity |
| local five-exponent theorem | Raynaud exponents (2.6a)--(2.6e), the $(e,a)$ table, and the separate tame/wild conductor ledger |
| stable specialization | descent automorphisms (3.3a)--(3.3c), explicit quartic/sextic twists (3.3d)--(3.3e), and trace polynomial (3.5a)--(3.5c) |
| global signature | $\lambda^{12}=\chi_p^s$ from an everywhere-unramified ratio |
| every resultant | recurrence (5.7)--(5.11), including explicit $u_{12},v_{12}$ |
| gcds | complete factorizations (5.13)--(5.16), yielding (5.17)--(5.18) |
| factor $31$ | the $\mathbf F_{31}$ root and trace table (5.22)--(5.24) |
| balanced integrality | odd primes, the level prime, and $2^6-1=63$ in Section 6.1 |
| balanced character | conductor computation (6.9a)--(6.9e), including the primes $2,3,p$ and the real place |
| balanced class group | split-prime relation (6.10a)--(6.10i), the explicit $r=2,3$ table, and Minkowski generation (6.11)--(6.11b) |
| balanced intersection | the nine discriminants (7.1) intersected with $-p$, $p>19$ |
| level $37$ canonical model | the Rankin--Cohen identity, all coefficients through the weight-$12$ Sturm bound $38$, the two cusp expansions, and $w_{37}(u,v)=(-u,v)$ |
| level $37$ Mordell--Weil group | exact counts on $E_-$, the order-$3$ point, and $L(E_-,1)/\Omega^+=1/3$, giving (8.13) |
| level $37$ modular factors | quotient maps, differential pullbacks, newform coefficients, and the exact three-chain modular-symbol identity $3L(f_-,1)=\Omega^+$ |
| level $37$ modular function | the modular unit $h$, its divisor and eta expansion, the displayed polynomials $A,B$, the two $j$-expansions, and the source/target pairing under $w_{37}$ |
| level $37$ points | the three fibers (8.18)--(8.20), giving exactly four points |
| genus-zero existence | modular $j$-maps (9.2) and $t=1$ values (9.5) |
| level $17$ existence | pointed model, group law, rank, cusp labels, and $j$-values (9.6)--(9.12) |
| CM existence | the stable kernels and five exact $j$-values in (10.4) |
| independent prime torsion | the precise oriented-$X_1(p)$ theorem and its reduction, Weil-pairing, formal-immersion, and finite-level dependency capsule |
| mixed $5$-torsion | discriminant (12.6), the complete $2$-isogeny descent (12.13)--(12.15), and the torsion check (12.16)--(12.18) |
| mixed $7$-torsion | discriminant (12.7), the Jacobian $2$-descent, point counts, saturation, and the $3,5$ Mordell--Weil sieve (12.19)--(12.35) |
| Frey local data | invariants (14.6), odd exponents (14.7), two-adic minimal exponent (14.12) |

The resultant ledger also contains two internal checks: dual signatures change only powers of the auxiliary prime, and each gcd exponent is the visible minimum of three row exponents. The level-$37$ ledger contains six further checks: substitution verifies both quotient maps, differential pullback verifies their involution signs, reduction counts certify the torsion on $E_-$, the weight-$2$ Sturm bound identifies the quotient newforms, the weight-$12$ bound certifies the canonical equation, and the two cusp expansions certify the orientation and degrees of the $j$-maps.

### 16.3 Logical safeguards

Several tempting shortcuts would break the proof.

1. A rational cyclic subgroup need not have a rational generator; $\lambda$ can be nontrivial.

2. Reducibility over $\overline{\mathbf F}_p$ is not reducibility over $\mathbf F_p$. The factor $31$ is the numerical warning.

3. A rational coarse point does not permit blanket descent at $j=0,1728$. Those twists were treated by division polynomials and CM eigenspaces.

4. Potentially good additive reduction is interior, not cuspidal. Stable reduction was used before applying cusp rigidity.

5. Odd cusp rigidity concerns the actual winding quotient. It neither uses all of $J_0(p)$ nor asserts a quotient specialization theorem at $2$.

6. Rational torsion on a Jacobian does not determine rational torsion on a connected optimal quotient. The group $E_-(\mathbf Q)$ was computed directly.

7. A vanishing resultant guarantees a common geometric root, not an $\mathbf F_p$ eigenvalue. Section 5.5 imposed the stronger condition.

8. The balanced class-field theorem ends at class number one. Only the independent theorem (7.1) enumerates the discriminants.

9. A bare $j$-value is not an isogeny certificate. Every non-CM existence proof includes a rational point on a certified modular curve.

10. Semistable reducibility gives rational $p$-torsion on one of two isogenous curves, not necessarily on the original curve.

11. Odd isogenies preserve all of $E[2]$; together with the explicit point calculations on $C_5$ and $C_7$, this fact, rather than the general prime-isogeny list, eliminates the Frey exponents $5$ and $7$.

12. The coefficient-prime finite-flat calculation is not the tame calculation at an auxiliary prime.  The wild primes $q=2,3$ are kept in their own conductor rows, and no tame conductor exponent is assigned to them.

13. The involution $[-1]$ gives an isomorphism $(E,P)\simeq(E,-P)$ on the oriented $X_1$ problem; it does not replace the generator by the underlying cyclic subgroup.  The torsion proof never invokes Chapter 11.

14. The level-$37$ labels are fixed by the two cusp parameters and by the displayed rational function $j(u,v)$.  Thus neither the identification with $X_0(37)$ nor the source/target $j$-pairing is inferred from the abstract genus-two equation alone.

These safeguards separate the exact interfaces of Books 68--69: the winding quotient is not all of $J$ at level $37$, quotient torsion is not lifted from Jacobian torsion, and no $2$-adic quotient kernel is assumed.

### 16.4 Final theorems

**Prime-isogeny theorem.** Let $p$ be prime. The following existence conditions are equivalent:

$$
\begin{array}{c}
\text{some }E/\mathbf Q\text{ has reducible }E[p]\text{ over }\mathbf F_p,\\
\text{some }E/\mathbf Q\text{ has a rational cyclic subgroup scheme of rank }p,\\
\text{some }E/\mathbf Q\text{ admits a rational cyclic isogeny of degree }p.
\end{array}
\tag{16.1}
$$

They hold exactly when

$$
\boxed{
p\in\{2,3,5,7,11,13,17,19,37,43,67,163\}.}
\tag{16.2}
$$

Every actual pair gives a noncuspidal rational point of $X_0(p)$. Conversely, away from $j=0,1728$, a noncuspidal rational coarse point descends to such a pair; at the two exceptional fibers, the direct calculation of Section 10.3 is the valid replacement.

**Semistable full-two theorem.** If $E/\mathbf Q$ is semistable and

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
$$

then for every prime $p\ge5$,

$$
E[p]\text{ is irreducible over }\mathbf F_p.
\tag{16.3}
$$

**Frey irreducibility theorem.** Let $p\ge5$ be prime, let $(a,b,c)$ be a primitive nontrivial integer solution of $a^p+b^p=c^p$, normalized as in (14.2), and let

$$
E_{a,b,p}:y^2=x(x-a^p)(x+b^p).
$$

Then

$$
\boxed{
\overline\rho_{E_{a,b,p},p}
:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathbf F_p)
\text{ is irreducible}.}
\tag{16.4}
$$

In addition,

$$
\det\overline\rho_{E,p}=\chi_p,
\tag{16.5}
$$

$$
v_q(\Delta_{\min})=2p\,v_q(abc)
\quad(q\mid abc,\ q\text{ odd}),
\tag{16.6}
$$

and

$$
v_2(\Delta_{\min})=2p\,v_2(a)-8.
\tag{16.7}
$$

For odd $q\mid abc$ with $q\ne p$, residual inertia is trivial; at $2$ it is nontrivial. These are the exact local data passed to the final argument.

### 16.5 Conclusion

A rational prime isogeny starts as a Galois-stable line, but the classification becomes visible only after the line is followed through several changes of language. Finite-flat geometry restricts its inertia. Stable reduction turns three fixed auxiliary primes into Hasse-bounded Frobenius equations. Global reciprocity turns local exponents into a single global signature. Exact resultants eliminate every unbalanced branch except $37$, while a quadratic character and Minkowski generation turn the balanced branch into an independent class-number problem.

The exceptional survivors then explain themselves. Level $37$ is a genuinely non-CM genus-two phenomenon: its rank-zero quotient has only three rational images, and their fibers give exactly four rational modular points. No Mordell--Weil assertion about the other quotient is needed. The degrees $43,67,163$ come instead from ramified kernels in the last class-number-one imaginary quadratic fields. The small degrees arise from genus-zero families, the pointed level-$17$ curve, and the earlier CM fields.

For the Frey curve, the classification list is no longer the decisive object. Its factored equation supplies full rational two-torsion and exact semistable minimal models. Semistability makes one diagonal isogeny character globally trivial, producing rational $p$-torsion on one side of the isogeny. The independent prime-torsion theorem excludes $p\ge11$, while the explicit $C_5$ and $C_7$ certificates exclude $5$ and $7$ in the presence of full rational two-torsion. The residual representation is therefore irreducible, with determinant and local ramification already fixed for the argument that follows.
