# Semistable Full-Two Residual Irreducibility

## Contents

1. [The irreducibility problem](#1-the-irreducibility-problem)
   - [From a matrix question to an isogeny](#11-from-a-matrix-question-to-an-isogeny)
   - [Why semistability should constrain a character](#12-why-semistability-should-constrain-a-character)
   - [Standing conventions](#13-standing-conventions)
   - [The proof architecture](#14-the-proof-architecture)
2. [Reducible torsion and its two characters](#2-reducible-torsion-and-its-two-characters)
   - [The kernel character](#21-the-kernel-character)
   - [The quotient character](#22-the-quotient-character)
   - [The dual isogeny](#23-the-dual-isogeny)
   - [Rational subgroup versus rational generator](#24-rational-subgroup-versus-rational-generator)
3. [Places away from the coefficient prime](#3-places-away-from-the-coefficient-prime)
   - [Good reduction](#31-good-reduction)
   - [Split multiplicative reduction](#32-split-multiplicative-reduction)
   - [Nonsplit multiplicative reduction](#33-nonsplit-multiplicative-reduction)
4. [Good reduction at the coefficient prime](#4-good-reduction-at-the-coefficient-prime)
   - [Why unramifiedness is the wrong condition](#41-why-unramifiedness-is-the-wrong-condition)
   - [Closing the invariant line](#42-closing-the-invariant-line)
   - [The unramified Oort--Tate dichotomy](#43-the-unramified-oort--tate-dichotomy)
   - [The two inertial alternatives](#44-the-two-inertial-alternatives)
5. [Multiplicative reduction at the coefficient prime](#5-multiplicative-reduction-at-the-coefficient-prime)
   - [The Tate exact sequence](#51-the-tate-exact-sequence)
   - [Stable lines in a triangular extension](#52-stable-lines-in-a-triangular-extension)
   - [The nonsplit twist](#53-the-nonsplit-twist)
6. [The semistable local character theorem](#6-the-semistable-local-character-theorem)
   - [Statement and proof](#61-statement-and-proof)
   - [The complementary character](#62-the-complementary-character)
   - [Sharpness and excluded hypotheses](#63-sharpness-and-excluded-hypotheses)
7. [The global unramifiedness argument](#7-the-global-unramifiedness-argument)
   - [Choosing the unramified diagonal](#71-choosing-the-unramified-diagonal)
   - [There is no nontrivial everywhere-unramified character of the rationals](#72-there-is-no-nontrivial-everywhere-unramified-character-of-the-rationals)
   - [The semistable isogeny theorem](#73-the-semistable-isogeny-theorem)
   - [Why powers of the character do not suffice](#74-why-powers-of-the-character-do-not-suffice)
8. [Prime torsion in the range at least eleven](#8-prime-torsion-in-the-range-at-least-eleven)
   - [The formal-immersion range](#81-the-formal-immersion-range)
   - [The exceptional levels eleven and thirteen](#82-the-exceptional-levels-eleven-and-thirteen)
   - [The prime-torsion theorem used here](#83-the-prime-torsion-theorem-used-here)
9. [Odd isogenies and full rational two-torsion](#9-odd-isogenies-and-full-rational-two-torsion)
   - [The Bezout inverse](#91-the-bezout-inverse)
   - [Preservation as a group scheme](#92-preservation-as-a-group-scheme)
   - [The mixed torsion subgroup](#93-the-mixed-torsion-subgroup)
10. [The exceptional prime seven](#10-the-exceptional-prime-seven)
    - [The exact modular reduction](#101-the-exact-modular-reduction)
    - [The imported rational-point computation](#102-the-imported-rational-point-computation)
    - [The mixed-seven exclusion](#103-the-mixed-seven-exclusion)
11. [The full-two irreducibility theorem](#11-the-full-two-irreducibility-theorem)
    - [Statement and proof strategy](#111-statement-and-proof-strategy)
    - [Proof by passage across the isogeny](#112-proof-by-passage-across-the-isogeny)
    - [Exact scope](#113-exact-scope)
12. [Dependency and hypothesis audit](#12-dependency-and-hypothesis-audit)
    - [Direct dependencies](#121-direct-dependencies)
    - [Exceptional-prime ledger](#122-exceptional-prime-ledger)
    - [Conclusion](#123-conclusion)

## 1. The irreducibility problem

The residual representation of an elliptic curve is a two-dimensional object, but its reducibility is governed by a one-dimensional character. That reduction in dimension is the central opportunity of this book. A stable line in $E[p]$ is the kernel of a rational isogeny; Galois acts on that line through a character; semistable reduction sharply restricts the character on inertia; and arithmetic over $\mathbf Q$ then forces one of the two diagonal characters to be trivial. The last statement turns a rational isogeny, whose kernel need not have a rational generator, into an actual rational point of order $p$ on one of two isogenous curves.

For a general elliptic curve this conclusion is not enough to prove irreducibility, because rational prime torsion exists at small primes. The additional hypothesis studied here is full rational two-torsion. An odd isogeny preserves that structure, so the curve on which rational $p$-torsion appears would have both full rational two-torsion and a rational point of order $p$. The formal-immersion and exceptional-level results of Books 148--149 eliminate $p\ge11$, while their exact mixed-seven reduction and sieve eliminate the sole remaining prime in this book's range.

The point of the argument is not merely its short conclusion. Several superficially similar local statements have different hypotheses. Away from $p$, semistability makes diagonal characters unramified. At $p$, good reduction leads to finite-flat group schemes and the Oort--Tate dichotomy, whereas multiplicative reduction leads to the Tate curve and need not make the whole residual representation finite flat. Keeping these branches separate is what makes the global argument valid.

### 1.1 From a matrix question to an isogeny

Let $E/\mathbf Q$ be an elliptic curve and let $p$ be a prime. Since the ground field has characteristic zero,

$$
E[p](\overline{\mathbf Q})\simeq \mathbf F_p^2.
$$

Choosing a basis gives

$$
\overline\rho_{E,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p),
$$

well defined up to conjugacy. The question whether this representation is reducible is basis independent: it asks whether $E[p]$ has a $G_{\mathbf Q}$-stable line.

Book 45 proves the isogeny--line equivalence with exactly the hypothesis needed here. Because $p$ is invertible in $\mathbf Q$, a stable line is a finite étale subgroup scheme $C\subset E[p]$ of order $p$, defined over $\mathbf Q$. The quotient $E/C$ exists, and

$$
\varphi:E\longrightarrow E'=E/C
$$

is a $\mathbf Q$-rational isogeny of degree $p$. Conversely, the kernel of every rational degree-$p$ isogeny is such a line. Thus

$$
\overline\rho_{E,p}\text{ reducible}
\quad\Longleftrightarrow\quad
E\text{ admits a rational }p\text{-isogeny}.
\tag{1.1}
$$

This is the decisive translation. It replaces a representation-theoretic branch by a geometric map carrying a kernel character and a dual kernel character.

### 1.2 Why semistability should constrain a character

Semistability means that at every finite prime the curve has good or multiplicative reduction. These two forms of reduction look different geometrically, but both suppress complicated diagonal ramification.

At good primes away from $p$, the entire $p$-torsion representation is unramified. At multiplicative primes away from $p$, inertia is unipotent, so every diagonal character is again trivial on inertia. At the coefficient prime $p$, the cyclotomic character is ramified and cannot be discarded. The correct conclusion is the two-valued alternative

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\overline\chi_p,
\tag{1.2}
$$

where $\lambda$ is the character of a stable line and $\overline\chi_p$ is the mod-$p$ cyclotomic character.

The determinant of $E[p]$ is $\overline\chi_p$. Hence the other diagonal character is

$$
\mu=\overline\chi_p\lambda^{-1}.
\tag{1.3}
$$

The alternatives in (1.2) say exactly that one of $\lambda$ and $\mu$ is unramified at $p$. Away from $p$, both are unramified. The local theory has therefore manufactured an everywhere-unramified one-dimensional global character.

### 1.3 Standing conventions

We use arithmetic Frobenius. The mod-$p$ cyclotomic character

$$
\overline\chi_p:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times
$$

is defined by

$$
\sigma(\zeta)=\zeta^{\overline\chi_p(\sigma)}
\qquad(\zeta\in\mu_p).
$$

For a prime $q$, a decomposition group and inertia group are denoted $G_q$ and $I_q$. Their embeddings in $G_{\mathbf Q}$ are fixed only up to conjugacy, but all characters considered are abelian, so their restrictions are unambiguous up to canonical identification.

An elliptic curve over $\mathbf Q$ is **semistable** when it has good or multiplicative reduction at every prime. Full rational two-torsion means

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
$$

or equivalently that the finite étale group scheme $E[2]$ is constant. A rational $p$-isogeny means an isogeny defined over $\mathbf Q$; it does not mean that its kernel has a rational generator.

Throughout, $p\ge7$ is prime. This is the exact reusable range of the theorem proved here. The book makes no claim below that range and assumes no arithmetic special to a later curve construction.

### 1.4 The proof architecture

The argument has five logically independent layers:

$$
\begin{array}{c}
\text{stable line in }E[p]\\
\Downarrow\\
\text{kernel character }\lambda\text{ and quotient character }\mu\\
\Downarrow\\
\text{one of }\lambda,\mu\text{ unramified at every finite prime}\\
\Downarrow\\
\lambda=1\text{ or }\mu=1\\
\Downarrow\\
\text{rational }p\text{-torsion on }E\text{ or }E/C.
\end{array}
\tag{1.4}
$$

For a curve with full rational two-torsion, an odd isogeny carries that structure to the quotient. The prime-torsion theorem handles $p\ge11$, and the exact mixed-seven theorem handles $p=7$. These two branches exhaust the stated range and require no classification of all rational isogenies.

## 2. Reducible torsion and its two characters

The star in an upper-triangular representation is important local extension data, but the global argument uses only the two diagonal characters. This chapter defines them invariantly, identifies the second through the Weil pairing, and explains how the dual isogeny makes it geometric.

### 2.1 The kernel character

Assume $E[p]$ has a $G_{\mathbf Q}$-stable line $C$. Since $C$ is one-dimensional over $\mathbf F_p$, there is a unique character

$$
\lambda:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times
$$

such that

$$
\sigma(P)=\lambda(\sigma)P
$$

for every $P\in C$ and every $\sigma\in G_{\mathbf Q}$. This is the **isogeny character** of the chosen kernel. Choosing a nonzero $P\in C$ does not change $\lambda$, since replacing $P$ by $aP$ with $a\in\mathbf F_p^\times$ commutes with Galois.

The stable line descends to a finite subgroup scheme, and the quotient isogeny

$$
0\longrightarrow C\longrightarrow E
\xrightarrow{\varphi}E'\longrightarrow0
$$

is defined over $\mathbf Q$. In a basis $(P,Q)$ beginning with a generator of $C$,

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\lambda(\sigma)&b(\sigma)\\
0&\mu(\sigma)
\end{pmatrix}.
\tag{2.1}
$$

The function $b$ records whether the representation splits. Nothing below assumes that it does.

### 2.2 The quotient character

The Weil pairing

$$
e_p:E[p]\times E[p]\longrightarrow\mu_p
$$

is perfect, alternating, and Galois equivariant. In dimension two this gives

$$
\det\overline\rho_{E,p}=\overline\chi_p.
\tag{2.2}
$$

Taking determinants in (2.1) yields

$$
\lambda\mu=\overline\chi_p,
$$

and hence

$$
\mu=\overline\chi_p\lambda^{-1}.
\tag{2.3}
$$

This proof does not depend on a symplectic basis. Indeed, for any basis the matrix of the alternating pairing is a nonzero scalar multiple of

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
$$

and the identity $A^{\mathsf t}JA=(\det A)J$ forces (2.2).

The quotient $E[p]/C$ is one-dimensional and carries the character $\mu$. The extension class $b$ can vary while $\lambda$ and $\mu$ remain fixed. This is why the diagonal-character argument cannot decide whether the original representation is split; it needs only reducibility.

### 2.3 The dual isogeny

Let $\widehat\varphi:E'\to E$ be the dual isogeny. Book 35 identifies its kernel with the Cartier dual $C^D$, and Book 45 identifies the generic character of that dual with the cyclotomic dual of $\lambda$. Thus

$$
\ker\widehat\varphi\simeq C^D,
\qquad
\chi_{\ker\widehat\varphi}
=\overline\chi_p\lambda^{-1}=\mu.
\tag{2.4}
$$

There is also a direct pointwise description. The degree-$p$ isogeny changes the integral $p$-adic lattice in one direction. Modulo $p$, the image of $E[p]$ in $E'[p]$ is a line, and that line is the kernel of the dual isogeny. Pairing compatibility identifies its character with the quotient character in (2.3).

Thus the two diagonal characters live on the two sides of one isogeny:

$$
\begin{array}{c|c}
\text{character}&\text{geometric line}\\ \hline
\lambda&\ker(E\to E')\\
\mu&\ker(E'\to E).
\end{array}
\tag{2.5}
$$

This table will turn triviality of either character into rational torsion.

### 2.4 Rational subgroup versus rational generator

The subgroup $C$ is defined over $\mathbf Q$ precisely because Galois preserves it. A generator is rational precisely when Galois fixes it pointwise. Therefore

$$
C\text{ has a rational generator}
\quad\Longleftrightarrow\quad
\lambda=1.
\tag{2.6}
$$

Similarly,

$$
\ker\widehat\varphi\text{ has a rational generator}
\quad\Longleftrightarrow\quad
\mu=1.
\tag{2.7}
$$

For odd $p$, a nontrivial character can preserve the cyclic subgroup while permuting all of its nonzero generators. The split Tate curve supplies the local model: its subgroup $\mu_p$ is defined over the base field, but a generator is rational only if the field contains a primitive $p$th root of unity. The distinction in (2.6) is therefore substantive, not terminological.

## 3. Places away from the coefficient prime

We now determine the ramification of $\lambda$ and $\mu$ at a prime $q\ne p$. Semistability is precisely strong enough: good reduction makes the full representation unramified, while multiplicative reduction makes inertia unipotent with trivial diagonal. Additive reduction would introduce finite characters on the diagonal and is the exact excluded case.

### 3.1 Good reduction

Suppose $E$ has good reduction at $q\ne p$. The prime-to-residue-characteristic specialization theorem from Book 45 identifies $E[p]$ with the geometric $p$-torsion of the special fiber. Equivalently,

$$
\overline\rho_{E,p}|_{I_q}=1.
\tag{3.1}
$$

Every subrepresentation and quotient of an unramified representation is unramified, so

$$
\lambda|_{I_q}=1,
\qquad
\mu|_{I_q}=1.
\tag{3.2}
$$

One may also see this integrally. The good model is an elliptic scheme over $\mathbf Z_q$, its $p$-torsion is finite étale because $p$ is invertible, and finite étale groups over a henselian DVR correspond to unramified modules. No coefficient-prime group-scheme classification is involved.

### 3.2 Split multiplicative reduction

Suppose $E/\mathbf Q_q$ has split multiplicative reduction. Book 44 supplies a Tate parameter $u\in\mathbf Q_q^\times$ with $v_q(u)>0$ and a Galois-equivariant exact sequence

$$
0\longrightarrow\mu_p
\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z
\longrightarrow0.
\tag{3.3}
$$

In a basis adapted to the multiplicative line,

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\overline\chi_p(\sigma)&c_u(\sigma)\\
0&1
\end{pmatrix}.
\tag{3.4}
$$

Because $q\ne p$, all $p$-power roots of unity are unramified over $\mathbf Q_q$, so $\overline\chi_p|_{I_q}=1$. Tate uniformization gives

$$
\overline\rho_{E,p}(\tau)=
\begin{pmatrix}
1&m\,t_p(\tau)\\
0&1
\end{pmatrix}
\qquad(\tau\in I_q),
\tag{3.5}
$$

where $m=v_q(\Delta_{\min})$ and $t_p$ is the mod-$p$ tame character. Every matrix in (3.5) is unipotent. Its only eigenvalue is $1$. Hence inertia acts trivially on every one-dimensional subquotient, whether or not the extension (3.3) splits. Therefore (3.2) holds at a split multiplicative prime as well.

### 3.3 Nonsplit multiplicative reduction

If the reduction is nonsplit multiplicative, it becomes split over the unramified quadratic extension. There is an unramified quadratic character $\eta_q$ such that

$$
E[p]\simeq E_u[p]\otimes\eta_q
$$

for a split Tate curve $E_u$. The diagonal characters are then $\overline\chi_p\eta_q$ and $\eta_q$. Since $\eta_q|_{I_q}=1$, the inertial matrix is still (3.5). Thus

$$
\lambda|_{I_q}=\mu|_{I_q}=1
$$

also in the nonsplit case.

The unramified twist matters on Frobenius: it records the splitness sign. It does not matter for the present ramification argument. This is why passing to the unramified splitting field is safe here and why passing to an unspecified ramified extension would not be.

## 4. Good reduction at the coefficient prime

At $q=p$, the cyclotomic character is ramified. Good reduction no longer gives an unramified $p$-torsion representation, but it does give a finite-flat integral model. A stable generic line can then be closed in that model, and the rank-$p$ classification over the unramified base $\mathbf Z_p$ leaves exactly two integral types.

### 4.1 Why unramifiedness is the wrong condition

Suppose $E/\mathbf Q_p$ has good reduction. It extends to an elliptic scheme $\mathcal E/\mathbf Z_p$, and

$$
\mathcal E[p]
$$

is finite flat of rank $p^2$. Its generic fiber is $E[p]$. This is the coefficient-prime local condition supplied by Books 42 and 45.

The group $\mu_p$ over $\mathbf Z_p$ is finite flat, but its generic points carry $\overline\chi_p$, which is nontrivial on inertia. Thus

$$
\text{finite flat at }p\not\Longrightarrow\text{unramified at }p.
$$

The integral model distinguishes an étale direction from a multiplicative direction; these become the two allowable inertia characters.

### 4.2 Closing the invariant line

Let $C\subset E[p]$ be the stable line with character $\lambda$. Regard $C$ as a finite étale subgroup of the generic fiber of $\mathcal E[p]$. By the closure theorem of Books 42 and 51, its schematic closure

$$
\mathcal C\subset\mathcal E[p]
$$

is a finite-flat subgroup of order $p$, unique inside this ambient model. Moreover the quotient

$$
0\longrightarrow\mathcal C
\longrightarrow\mathcal E[p]
\longrightarrow\mathcal E[p]/\mathcal C
\longrightarrow0
\tag{4.1}
$$

is finite-flat exact and has generic fiber

$$
0\longrightarrow C\longrightarrow E[p]
\longrightarrow E[p]/C\longrightarrow0.
$$

The fixed ambient group is essential. The closure theorem does not say that an abstract generic group has a unique model. It says that the chosen generic subgroup has a unique saturated closure inside $\mathcal E[p]$.

The Weil pairing on $\mathcal E[p]$ makes (4.1) self-dual in the appropriate order. The line $\mathcal C$ is isotropic because the pairing is alternating, and its annihilator has the same rank $p$, hence equals $\mathcal C$. Therefore

$$
\mathcal E[p]/\mathcal C\simeq\mathcal C^D.
\tag{4.2}
$$

On generic characters, (4.2) recovers $\mu=\overline\chi_p\lambda^{-1}$.

### 4.3 The unramified Oort--Tate dichotomy

Book 51 classifies order-$p$ finite-flat groups over a mixed-characteristic DVR. With $e=v(p)$ and Oort--Tate exponent $r$, one has

$$
0\le r\le e,
\qquad
\chi_{\mathcal C}|_{I_p}=\theta^r,
\qquad
\overline\chi_p|_{I_p}=\theta^e.
\tag{4.3}
$$

Over $\mathbf Z_p$, the absolute ramification index is $e=1$. Hence $r$ is either $0$ or $1$. The first endpoint is finite étale and has unramified generic character. The second is of multiplicative type and has cyclotomic generic character up to an unramified twist. Consequently

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\overline\chi_p|_{I_p}.
\tag{4.4}
$$

This conclusion remains true when the good special fiber is supersingular. In that case a stable generic line may fail to exist; but if reducibility supplies one, its closure is still an order-$p$ finite-flat group and must be one of the two endpoints. There is no contradiction in using an endpoint subgroup inside a height-two group only when the stable generic line actually exists.

### 4.4 The two inertial alternatives

Cartier duality complements the Oort--Tate exponent. Thus if $\mathcal C$ has exponent $r$, its quotient in (4.2) has exponent $1-r$. The two diagonal restrictions are therefore

$$
(\lambda|_{I_p},\mu|_{I_p})=
\begin{cases}
(1,\overline\chi_p),&r=0,\\
(\overline\chi_p,1),&r=1.
\end{cases}
\tag{4.5}
$$

Equation (4.5) is stronger than merely knowing their product. It uses finite-flat geometry to show that no intermediate tame exponent occurs over the unramified base. Over a ramified extension of $\mathbf Q_p$ with $e>1$, intermediate exponents $0<r<e$ can occur and (4.4) can fail. The fact that the global base is $\mathbf Q$ is therefore used locally through $\mathbf Q_p/\mathbf Q_p$ having absolute ramification index one.

## 5. Multiplicative reduction at the coefficient prime

Multiplicative reduction at $p$ must not be folded into the good-reduction argument. A Tate curve does not extend to an elliptic scheme, and its full $p$-torsion need not be finite flat. Nevertheless its generic exact sequence is explicit enough to prove the same two alternatives for every stable line.

### 5.1 The Tate exact sequence

Suppose first that $E/\mathbf Q_p$ has split multiplicative reduction. There is a Tate parameter $u$ with $v_p(u)>0$ and an exact sequence

$$
0\longrightarrow\mu_p
\longrightarrow E[p]
\xrightarrow{\nu}\mathbf Z/p\mathbf Z
\longrightarrow0.
\tag{5.1}
$$

The extension class is the Kummer class of $u$ in

$$
\mathbf Q_p^\times/\mathbf Q_p^{\times p}.
$$

In a basis adapted to $\mu_p$,

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\overline\chi_p(\sigma)&c_u(\sigma)\\
0&1
\end{pmatrix}.
\tag{5.2}
$$

Unlike the prime-to-$p$ situation, both the cyclotomic character and the unit part of $c_u$ can be ramified. The tame unipotent formula (3.5) is not valid at the coefficient prime.

### 5.2 Stable lines in a triangular extension

Let $L\subset E[p]$ be any $G_p$-stable line, not necessarily the canonical multiplicative line $M=\mu_p(\overline{\mathbf Q}_p)$. We prove that its inertial character is either $\overline\chi_p$ or $1$.

If $L=M$, its character is $\overline\chi_p$ and there is nothing to prove. Suppose $L\ne M$. Since both are lines in a two-dimensional space,

$$
L\cap M=0.
$$

The quotient map $\nu$ in (5.1) therefore restricts to a nonzero map

$$
L\longrightarrow\mathbf F_p.
$$

It is an isomorphism of one-dimensional vector spaces. Because $\nu$ is Galois equivariant and the quotient in (5.1) is trivial, $G_p$ acts trivially on $L$. Hence the character of $L$ is $1$ on all of $G_p$, and in particular on inertia.

We have proved, without assuming that (5.1) splits,

$$
\lambda|_{I_p}=\overline\chi_p|_{I_p}
\quad\text{or}\quad
\lambda|_{I_p}=1.
\tag{5.3}
$$

If the extension is nonsplit as a $G_p$-module, $M$ may be its only stable line. If it splits, the complementary trivial line also exists. The proof handles both possibilities.

### 5.3 The nonsplit twist

For nonsplit multiplicative reduction, an unramified quadratic character $\eta_p$ makes $E\otimes\eta_p$ a split Tate curve. The exact sequence becomes

$$
0\longrightarrow\mathbf F_p(\overline\chi_p\eta_p)
\longrightarrow E[p]
\longrightarrow\mathbf F_p(\eta_p)
\longrightarrow0.
\tag{5.4}
$$

The same intersection-and-projection proof shows that a stable line has character $\overline\chi_p\eta_p$ or $\eta_p$. Since $\eta_p$ is unramified,

$$
\lambda|_{I_p}=\overline\chi_p|_{I_p}
\quad\text{or}\quad
\lambda|_{I_p}=1.
$$

Thus splitness affects Frobenius values but not the inertial alternative.

## 6. The semistable local character theorem

Good and multiplicative reduction have now been treated by different integral mechanisms. We can combine their conclusions into one local theorem, while retaining the proof branches that justify it.

### 6.1 Statement and proof

**Theorem 6.1 (semistable isogeny-character alternatives).** Let $p\ge7$ be prime, let $E/\mathbf Q$ be semistable, and let $C\subset E[p]$ be a $G_{\mathbf Q}$-stable line with character $\lambda$. Put

$$
\mu=\overline\chi_p\lambda^{-1}.
$$

Then:

1. for every prime $q\ne p$,
   $$
   \lambda|_{I_q}=\mu|_{I_q}=1;
   $$
2. at $p$,
   $$
   \{\lambda|_{I_p},\mu|_{I_p}\}
   =\{1,\overline\chi_p|_{I_p}\}.
   $$

**Proof strategy.** Away from $p$, use good specialization or Tate unipotence. At $p$, use the finite-flat closure of the line in the good case and the generic Tate exact sequence in the multiplicative case.

**Proof.** Let $q\ne p$. If $E$ has good reduction at $q$, equation (3.1) makes the full representation unramified. If $E$ has multiplicative reduction, equations (3.5) and its unramified quadratic twist show that inertia is unipotent with sole eigenvalue $1$. In either case every one-dimensional subquotient has trivial inertia. This proves the first assertion.

At $p$, suppose first that $E$ has good reduction. Close $C$ inside the finite-flat group $\mathcal E[p]$. Since $\mathbf Z_p$ has absolute ramification index one, the order-$p$ closure is étale or multiplicative. Its character on inertia is respectively $1$ or $\overline\chi_p$. Cartier duality gives the complementary alternative for the quotient.

If $E$ has multiplicative reduction, pass through the unramified quadratic splitting extension. The canonical Tate line has character $\overline\chi_p$ times an unramified sign. Any other stable line maps isomorphically to the quotient and has the unramified quotient character. Restriction to inertia gives the same unordered pair. These cases exhaust semistability. $\square$

### 6.2 The complementary character

The unordered formulation in Theorem 6.1 is exactly what duality predicts. If

$$
\lambda|_{I_p}=1,
$$

then

$$
\mu|_{I_p}=\overline\chi_p|_{I_p}.
$$

If

$$
\lambda|_{I_p}=\overline\chi_p|_{I_p},
$$

then

$$
\mu|_{I_p}=1.
$$

There is no choice of normalization here: the product $\lambda\mu=\overline\chi_p$ fixes the complement. Switching from arithmetic to geometric Frobenius would invert unramified Frobenius values, but it would not change these inertia restrictions.

### 6.3 Sharpness and excluded hypotheses

Three boundaries are essential.

First, additive reduction is excluded. A potentially good additive curve can carry nontrivial finite inertia characters on the diagonal, and a potentially multiplicative additive curve can carry a ramified quadratic splitting character. Semistability removes both phenomena.

Second, the global field is $\mathbf Q$. Over a local field with absolute ramification index $e>1$, an order-$p$ finite-flat line may have Oort--Tate exponent strictly between $0$ and $e$, producing inertia $\theta^r$ rather than $1$ or $\overline\chi_p$.

Third, at $p=2$ the mod-$2$ cyclotomic character is trivial, so constant and multiplicative generic characters coincide. The Oort--Tate endpoints still exist, but the character alone cannot distinguish them. Our final application has $p\ge7$, so this dyadic collapse never enters.

The theorem does not claim that $E[p]$ is unramified at multiplicative primes or finite flat at every multiplicative coefficient prime. It claims only the precise diagonal restrictions proved above.

## 7. The global unramifiedness argument

The local theorem leaves one global step: a finite character of $G_{\mathbf Q}$ unramified at every finite prime is trivial. Global class field theory turns this into the vanishing of the conductor and the triviality of the corresponding ray class quotient.

### 7.1 Choosing the unramified diagonal

By Theorem 6.1, both $\lambda$ and $\mu$ are unramified at every $q\ne p$. At $p$, exactly one has trivial inertia. Define

$$
\psi=
\begin{cases}
\lambda,&\lambda|_{I_p}=1,\\
\mu,&\mu|_{I_p}=1.
\end{cases}
\tag{7.1}
$$

Then

$$
\psi|_{I_q}=1
\qquad\text{for every finite prime }q.
\tag{7.2}
$$

The image of $\psi$ is a subgroup of the finite group $\mathbf F_p^\times$, so $\psi$ cuts out a finite abelian extension $L/\mathbf Q$. Local reciprocity identifies $\psi|_{I_q}=1$ with $L/\mathbf Q$ being unramified at $q$. Thus $L$ is unramified at every finite prime.

### 7.2 There is no nontrivial everywhere-unramified character of the rationals

**Lemma 7.1.** Let

$$
\psi:G_{\mathbf Q}\longrightarrow A
$$

be a finite abelian character, where $A$ is a finite group. If $\psi$ is unramified at every finite prime, then $\psi=1$.

**Proof strategy.** Translate the character into a finite abelian extension and use the conductor--discriminant formula from global class field theory.

**Proof.** Replace $A$ by the image of $\psi$ and let $L$ be the fixed field of its kernel. Then $L/\mathbf Q$ is finite abelian and its character group $X$ consists of finite characters unramified at every finite prime. Their finite conductor ideals are therefore all $(1)$. The conductor--discriminant formula of Book 6 gives

$$
\mathfrak d_{L/\mathbf Q}
=\prod_{\chi\in X}\mathfrak f_0(\chi)
=(1).
\tag{7.3}
$$

Thus the absolute discriminant of $L$ has absolute value $1$. A nontrivial number field has absolute discriminant greater than $1$: this follows from the Minkowski lattice bound, whose equality case would force degree one. Hence $L=\mathbf Q$, so the image of $\psi$ is trivial. $\square$

There is an equivalent ray-class proof. An abelian extension of $\mathbf Q$ unramified at finite places is contained in the ray class field of modulus consisting only of the real place. The corresponding narrow ideal class group of $\mathbf Q$ is trivial because every fractional ideal has a positive rational generator. The discriminant proof has the advantage of treating possible complexification at infinity without an extra sign discussion.

### 7.3 The semistable isogeny theorem

**Theorem 7.2 (rational torsion on one side).** Let $p\ge7$ be prime. Let $E/\mathbf Q$ be semistable and suppose that $E$ has a rational isogeny

$$
\varphi:E\longrightarrow E'=E/C
$$

of degree $p$. Then

$$
E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.
\tag{7.4}
$$

More precisely, if $\lambda$ is the character of $C$ and $\mu=\overline\chi_p\lambda^{-1}$, then

$$
\lambda=1
\quad\text{or}\quad
\mu=1.
\tag{7.5}
$$

**Proof.** Theorem 6.1 and (7.1) produce one of $\lambda,\mu$ that is unramified at every finite prime. Lemma 7.1 makes that character trivial. If $\lambda=1$, every point of $C$ is rational, so a nonzero point gives $E(\mathbf Q)[p]\ne0$. If $\mu=1$, the dual kernel $C^D=\ker\widehat\varphi$ has a rational generator, so $E'(\mathbf Q)[p]\ne0$. $\square$

The conclusion is symmetric in the two sides of the isogeny. It does not assert that the original kernel character is trivial; sometimes only the dual kernel is rationally generated.

### 7.4 Why powers of the character do not suffice

It is tempting to prove that a bounded power such as $\lambda^{12}$ is unramified and then infer that $\lambda$ is trivial. That inference is false: a nontrivial character can have trivial twelfth power. The present proof avoids the loss of information. The coefficient-prime alternatives apply to $\lambda$ itself, and the determinant identifies the exact complementary character. Global class field theory is then applied to one actual diagonal character, not to a power of it.

Nor can one replace Lemma 7.1 by the assertion that every unramified local character is trivial. Unramified local characters may have nontrivial Frobenius values. It is the simultaneous absence of ramification at all finite primes, together with the global arithmetic of $\mathbf Q$, that forces triviality.

## 8. Prime torsion in the range at least eleven

The semistable isogeny theorem reduces reducibility to rational prime torsion on one side of an isogeny. For primes at least eleven, Books 148--149 already supply the exact exclusion. This chapter records that imported theorem with its exceptional levels visible, so the main proof will not conceal a general torsion-classification theorem.

### 8.1 The formal-immersion range

Book 148 studies a rational point $P$ of prime order $p$ through its point on $X_1(p)$. For $p\ge11$, reduction modulo $3$ cannot remain in the interior: the Hasse bound gives

$$
\#\widetilde E(\mathbf F_3)\le7<p.
$$

Nor can the reduction lie in the identity torus of a boundary fiber. A one-dimensional torus over $\mathbf F_3$ has order two in the split case and order four in the nonsplit case, neither divisible by $p\ge11$. The modular point therefore reduces to an outward rational cusp.

For $p\ge17$, the corrected Eisenstein index

$$
n_p=\frac{p-1}{\gcd(p-1,12)}
$$

is greater than one. The selected Eisenstein quotient is finite on rational points and the pointed modular map is a formal immersion at the outward cusp. Cusp-disk rigidity forces the modular point to equal the cusp, contradicting that it represents a smooth elliptic curve. Hence no rational point of prime order $p\ge17$ exists.

The denominator in $n_p$ is essential. At $p=13$, $n_{13}=1$, so the selected quotient used in the uniform proof does not exist. Level thirteen must be handled by its actual genus-two curve.

### 8.2 The exceptional levels eleven and thirteen

Book 148 identifies $X_1(11)$ with

$$
y^2+y=x^3-x^2
$$

and proves that its five rational points are precisely its five cusps. Therefore no elliptic curve over $\mathbf Q$ has a rational point of order $11$.

Book 149 completes the level-thirteen handoff. On the model

$$
y^2+(x^3+x^2+1)y=x^2+x,
$$

it proves

$$
X_1(13)(\mathbf Q)=
\{\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)\}.
\tag{8.1}
$$

All six points are cusps. The proof uses the exact equality

$$
J_1(13)(\mathbf Q)\simeq\mathbf Z/19\mathbf Z
$$

and an exhaustive reduction at $17$, not the absent Eisenstein quotient. Thus rational prime torsion of order $13$ is also impossible.

### 8.3 The prime-torsion theorem used here

Combining the uniform range with the two exceptional calculations gives the exact statement required below.

**Theorem 8.1 (prime-torsion exclusion).** If $E/\mathbf Q$ is an elliptic curve and $p\ge11$ is prime, then

$$
E(\mathbf Q)[p]=0.
\tag{8.2}
$$

**Proof.** If $p=11$, use the complete rational-point calculation on $X_1(11)$. If $p=13$, use (8.1). Every remaining prime $p\ge11$ satisfies $p\ge17$, so the uniform formal-immersion theorem applies. $\square$

The theorem says nothing about rational isogenies with nontrivially generated kernels. That is precisely why Theorem 7.2 was needed first: it converts a semistable rational isogeny into rational torsion on one side.

## 9. Odd isogenies and full rational two-torsion

The next invariant survives passage from $E$ to $E/C$. The clean statement is scheme-theoretic and works over any base, although the rational-point consequence is used over $\mathbf Q$.

### 9.1 The Bezout inverse

Let $\varphi:A\to B$ be an isogeny of odd degree $d$ between abelian schemes. Book 35 supplies a quasi-inverse $\varphi':B\to A$ such that

$$
\varphi'\varphi=[d]_A,
\qquad
\varphi\varphi'=[d]_B.
\tag{9.1}
$$

On a group scheme killed by $2$, multiplication by the odd integer $d$ is the identity:

$$
[d]=[1+2k]=[1].
\tag{9.2}
$$

Restricting (9.1) to two-torsion makes $\varphi'[2]$ a two-sided inverse to $\varphi[2]$.

### 9.2 Preservation as a group scheme

**Theorem 9.1 (odd-isogeny invariance).** If $\varphi:A\to B$ is an odd-degree isogeny of abelian schemes, then

$$
\varphi[2]:A[2]\xrightarrow{\sim}B[2]
\tag{9.3}
$$

is an isomorphism of finite-flat group schemes, compatible with arbitrary base change.

**Proof.** Every homomorphism commutes with multiplication by $2$, so $\varphi$ and $\varphi'$ restrict to the two kernels. Equations (9.1)--(9.2) show that the restrictions are inverse. $\square$

Over a field of characteristic different from two, (9.3) is Galois equivariant on geometric points. Hence

$$
A[2]\text{ is constant}
\quad\Longleftrightarrow\quad
B[2]\text{ is constant}.
\tag{9.4}
$$

This proof is stronger than counting four points. It remains correct in characteristic two, where the group schemes may be nonreduced and point counting would fail.

### 9.3 The mixed torsion subgroup

Let $F$ be a field of characteristic zero, let $E/F$ have full rational two-torsion, and let $P\in E(F)$ have odd prime order $p$. Since the orders are coprime,

$$
E[2](F)\cap\langle P\rangle=0.
$$

Therefore

$$
E[2](F)\oplus\langle P\rangle
\simeq(\mathbf Z/2\mathbf Z)^2\oplus\mathbf Z/p\mathbf Z.
\tag{9.5}
$$

By the Chinese remainder theorem,

$$
(\mathbf Z/2\mathbf Z)^2\oplus\mathbf Z/p\mathbf Z
\simeq\mathbf Z/2\mathbf Z\oplus\mathbf Z/2p\mathbf Z.
\tag{9.6}
$$

Thus full rational two-torsion and a rational point of order $p$ force the mixed subgroup

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/2p\mathbf Z
\subseteq E(F).
\tag{9.7}
$$

For $p=7$, the exact impossibility of (9.7) is the remaining arithmetic input.

## 10. The exceptional prime seven

The large-prime theorem begins at eleven, so one prime remains in the range of this book. Elliptic curves over $\mathbf Q$ can have rational points of order seven; the contradiction must use full rational two-torsion as well. The required arithmetic has already been completed in Books 148--149. Our task is to import its exact logical form, not to repeat its parameter calculations or Mordell--Weil sieve.

### 10.1 The exact modular reduction

Book 148 starts from Tate normal form for an elliptic curve with a rational point of order seven. Requiring full rational two-torsion makes the cubic of nonzero two-torsion coordinates split. Its discriminant is therefore a square, and the parameter consequently determines a rational point on

$$
C_7:z^2=t(t-1)(t^3-8t^2+5t+1).
\tag{10.1}
$$

The implication needed here is precise:

$$
\begin{array}{c}
E/\mathbf Q\text{ has full rational two-torsion}\
\text{and }P\in E(\mathbf Q)\text{ has order }7
\end{array}
\Longrightarrow
\begin{array}{c}
(t,z)\in C_7(\mathbf Q),\t\notin\{0,1,\infty\}.
\end{array}
\tag{10.2}
$$

Book 148 proves this implication, including the Tate-normal-form substitutions and the identification of $t=0,1,\infty$ as degenerate or boundary parameters. It does not use the false converse that a square cubic discriminant forces the cubic to split.

### 10.2 The imported rational-point computation

Book 149 completes the rational-point problem left by (10.1). Using the full Jacobian

$$
J_7(\mathbf Q)\simeq
\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2
$$

and an exhaustive Abel-image sieve over all twelve classes, it proves

$$
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.
\tag{10.3}
$$

Thus every rational point of $C_7$ has one of the three parameters excluded in (10.2). The completeness of (10.3), rather than a search bound or a finite-index subgroup of the Jacobian, is the decisive imported computation.

### 10.3 The mixed-seven exclusion

**Theorem 10.1 (mixed-seven exclusion).** If $E/\mathbf Q$ has full rational two-torsion, then

$$
E(\mathbf Q)[7]=0.
\tag{10.4}
$$

**Proof.** A rational point of order seven, together with $E[2](\mathbf Q)$, would give the mixed subgroup

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/14\mathbf Z
\subseteq E(\mathbf Q).
$$

By the exact implication (10.2), this configuration yields a nonboundary rational point of $C_7$. Equation (10.3) says that no such point exists. $\square$

No semistability hypothesis is needed for Theorem 10.1. Semistability enters earlier, solely in converting a rational isogeny into rational torsion on one side.

## 11. The full-two irreducibility theorem

Every ingredient is now in place. The proof is short because the local character theorem, the global triviality step, preservation of two-torsion, and the exceptional arithmetic have each been isolated with their hypotheses visible.

### 11.1 Statement and proof strategy

**Theorem 11.1 (semistable full-two residual irreducibility).** Let $E/\mathbf Q$ be a semistable elliptic curve satisfying

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
$$

For every prime $p\ge7$, the representation

$$
\overline\rho_{E,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
$$

is irreducible.

The proof proceeds by contradiction. Reducibility produces a rational degree-$p$ isogeny. Semistability and global class field theory put rational $p$-torsion on one side of that isogeny. Odd degree carries full rational two-torsion to the same side. The prime is then either seven, where Theorem 10.1 applies, or at least eleven, where Theorem 8.1 applies.

### 11.2 Proof by passage across the isogeny

**Proof.** Suppose that $E[p]$ is reducible. By (1.1), a stable line $C$ gives a rational isogeny

$$
\varphi:E\longrightarrow E'=E/C
$$

of degree $p$. Theorem 7.2 gives

$$
E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.
\tag{11.1}
$$

Because $p$ is odd, Theorem 9.1 gives a Galois-equivariant isomorphism

$$
E[2]\xrightarrow{\sim}E'[2].
\tag{11.2}
$$

Hence both curves have full rational two-torsion. Let $A$ be the curve in (11.1) carrying rational $p$-torsion.

If $p=7$, Theorem 10.1 contradicts $A(\mathbf Q)[7]\ne0$. If $p\ge11$, Theorem 8.1 contradicts $A(\mathbf Q)[p]\ne0$. These cases exhaust the primes $p\ge7$. Therefore the assumed stable line cannot exist, and $E[p]$ is irreducible. $\square$

Notice that the rational point is allowed to occur on the dual side $E'$. The proof never replaces “rational subgroup” by “rational generator” without first applying the global character argument.

### 11.3 Exact scope

The conclusion is irreducibility over $\mathbf F_p$: equivalently, there is no $G_{\mathbf Q}$-stable $\mathbf F_p$-line and no rational isogeny of degree $p$. Absolute irreducibility is a separate group-theoretic assertion and is not claimed here. Nor does the theorem classify the image of the representation.

The lower bound is intentionally $p\ge7$, and no theorem below that range is asserted. Semistability is essential: at an additive prime a diagonal character can acquire nontrivial ramification, destroying the everywhere-unramified character used in Chapter 7. Full rational two-torsion is essential at $p=7$, where rational seven-torsion exists on other elliptic curves.

The theorem is reusable without any equation, minimal model, conductor computation, or deformation condition attached to a particular elliptic curve. A later application need only verify semistability, full rational two-torsion, and $p\ge7$.

## 12. Dependency and hypothesis audit

A standalone theorem is only as sound as its imports. This final chapter records the deep or nonstandard results used directly, separates them from downstream applications, and checks each exceptional prime.

### 12.1 Direct dependencies

| Book | Imported result | Use here |
|---|---|---|
| 6 | global reciprocity and the conductor--discriminant formula over $\mathbf Q$ | Lemma 7.1 |
| 35 | quotients and dual isogenies; odd-isogeny invariance of two-torsion | Sections 2.3 and 9 |
| 42 | finite-flat torsion at good reduction and schematic closure of a generic line | Chapter 4 |
| 44 | Tate uniformization and its torsion exact sequence, including the unramified nonsplit twist | Chapters 3 and 5 |
| 45 | stable-line/isogeny equivalence, Weil-pairing determinant, and good-reduction unramifiedness | Chapters 1--3 |
| 51 | order-$p$ finite-flat classification over the unramified base $\mathbf Z_p$ | Chapter 4 |
| 148 | formal-immersion exclusion for $p\ge17$, the level-$11$ calculation, and the one-way mixed-seven parameter reduction | Sections 8.1--8.2 and 10.1 |
| 149 | complete rational-point sets for $X_1(13)$ and the mixed-seven curve | Sections 8.2 and 10.2 |

Book 149 itself imports the exact Jacobian arithmetic needed for its exhaustive sieves; those books are transitive, not direct, dependencies here. No later manuscript supplies any step in Theorem 11.1.

### 12.2 Exceptional-prime ledger

| Prime or place | Input | Exact conclusion |
|---|---|---|
| $q\ne p$, good | prime-to-$q$ specialization | both diagonal characters are unramified |
| $q\ne p$, multiplicative | Tate unipotence and an unramified possible twist | both diagonal characters are unramified |
| $q=p$, good | finite-flat closure and absolute ramification index one | diagonal inertia is $1$ or $\overline\chi_p$ |
| $q=p$, multiplicative | stable-line analysis in the Tate exact sequence | diagonal inertia is $1$ or $\overline\chi_p$ |
| $p=7$ | Book 148 reduction plus Book 149 exhaustive sieve | full rational two-torsion forbids rational $7$-torsion |
| $p=11$ | Book 148 genus-one calculation | rational $11$-torsion is impossible |
| $p=13$ | Book 149 genus-two sieve | rational $13$-torsion is impossible |
| $p\ge17$ | Book 148 oriented formal immersion | rational $p$-torsion is impossible |

Arithmetic Frobenius is used throughout. The nonsplit multiplicative twist is unramified, so it does not alter inertia. The square-discriminant condition in the mixed-seven reduction is used only in the necessary direction.

### 12.3 Conclusion

Semistability removes diagonal ramification away from the coefficient prime and leaves only the trivial and cyclotomic characters at that prime. Their product is the cyclotomic determinant, so one actual diagonal character—not merely a power of one—is unramified at every finite place. Global arithmetic over $\mathbf Q$ makes it trivial, placing rational $p$-torsion on one side of the isogeny.

Odd isogenies preserve full rational two-torsion. The exact prime-torsion computations eliminate every $p\ge11$, and the exact mixed-seven computation eliminates $p=7$. This proves the reusable theorem for precisely the declared range and stops before any curve-specific arithmetic.
