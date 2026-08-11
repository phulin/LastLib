# Semistable Isogeny Characters and Frey Residual Representations

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
   - [The conductor interpretation](#34-the-conductor-interpretation)
4. [Good reduction at the coefficient prime](#4-good-reduction-at-the-coefficient-prime)
   - [Why unramifiedness is the wrong condition](#41-why-unramifiedness-is-the-wrong-condition)
   - [Closing the invariant line](#42-closing-the-invariant-line)
   - [The unramified Oort--Tate dichotomy](#43-the-unramified-oort--tate-dichotomy)
   - [The two inertial alternatives](#44-the-two-inertial-alternatives)
5. [Multiplicative reduction at the coefficient prime](#5-multiplicative-reduction-at-the-coefficient-prime)
   - [The Tate exact sequence](#51-the-tate-exact-sequence)
   - [Stable lines in a triangular extension](#52-stable-lines-in-a-triangular-extension)
   - [The nonsplit twist](#53-the-nonsplit-twist)
   - [Finite-flatness and discriminant divisibility](#54-finite-flatness-and-discriminant-divisibility)
6. [The semistable local character theorem](#6-the-semistable-local-character-theorem)
   - [Statement and proof](#61-statement-and-proof)
   - [The complementary character](#62-the-complementary-character)
   - [Sharpness and excluded hypotheses](#63-sharpness-and-excluded-hypotheses)
7. [The global unramifiedness argument](#7-the-global-unramifiedness-argument)
   - [Choosing the unramified diagonal](#71-choosing-the-unramified-diagonal)
   - [There is no nontrivial everywhere-unramified character of the rationals](#72-there-is-no-nontrivial-everywhere-unramified-character-of-the-rationals)
   - [The semistable isogeny theorem](#73-the-semistable-isogeny-theorem)
   - [Why powers of the character do not suffice](#74-why-powers-of-the-character-do-not-suffice)
8. [Prime torsion over the rationals](#8-prime-torsion-over-the-rationals)
   - [The formal-immersion range](#81-the-formal-immersion-range)
   - [The exceptional levels eleven and thirteen](#82-the-exceptional-levels-eleven-and-thirteen)
   - [The prime-torsion theorem used here](#83-the-prime-torsion-theorem-used-here)
9. [Odd isogenies and full rational two-torsion](#9-odd-isogenies-and-full-rational-two-torsion)
   - [The Bezout inverse](#91-the-bezout-inverse)
   - [Preservation as a group scheme](#92-preservation-as-a-group-scheme)
   - [The mixed torsion subgroup](#93-the-mixed-torsion-subgroup)
10. [The exceptional primes five and seven](#10-the-exceptional-primes-five-and-seven)
    - [Why the prime-torsion theorem leaves two cases](#101-why-the-prime-torsion-theorem-leaves-two-cases)
    - [The five-primary mixed curve](#102-the-five-primary-mixed-curve)
    - [The mixed-seven curve](#103-the-mixed-seven-curve)
    - [The exact mixed-torsion exclusion](#104-the-exact-mixed-torsion-exclusion)
11. [Irreducibility for semistable curves with full two-torsion](#11-irreducibility-for-semistable-curves-with-full-two-torsion)
    - [The main criterion](#111-the-main-criterion)
    - [Proof by passage across the isogeny](#112-proof-by-passage-across-the-isogeny)
    - [What the theorem does and does not say](#113-what-the-theorem-does-and-does-not-say)
12. [The Frey curve](#12-the-frey-curve)
    - [Normalization of a primitive triple](#121-normalization-of-a-primitive-triple)
    - [Visible two-torsion and invariants](#122-visible-two-torsion-and-invariants)
    - [Odd-prime reduction](#123-odd-prime-reduction)
    - [The minimal model at two](#124-the-minimal-model-at-two)
    - [Semistability](#125-semistability)
13. [Frey residual irreducibility](#13-frey-residual-irreducibility)
    - [The residual representation](#131-the-residual-representation)
    - [The contradiction argument](#132-the-contradiction-argument)
    - [The local ramification ledger](#133-the-local-ramification-ledger)
    - [All prime exponents at least seven](#134-all-prime-exponents-at-least-seven)
14. [Dependency and hypothesis audit](#14-dependency-and-hypothesis-audit)
    - [Imported local results](#141-imported-local-results)
    - [Imported global and geometric results](#142-imported-global-and-geometric-results)
    - [Exceptional-prime and normalization ledger](#143-exceptional-prime-and-normalization-ledger)
    - [Conclusion](#144-conclusion)

## 1. The irreducibility problem

The residual representation of an elliptic curve is a two-dimensional object, but its reducibility is governed by a one-dimensional character. That reduction in dimension is the central opportunity of this book. A stable line in $E[p]$ is the kernel of a rational isogeny; Galois acts on that line through a character; semistable reduction sharply restricts the character on inertia; and arithmetic over $mathbf Q$ then forces one of the two diagonal characters to be trivial. The last statement turns a rational isogeny, whose kernel need not have a rational generator, into an actual rational point of order $p$ on one of two isogenous curves.

For a general elliptic curve this conclusion is not enough to prove irreducibility. Rational prime torsion does exist at small primes. The Frey curve brings one more rigid feature: all of its two-torsion is rational. An odd isogeny preserves that full two-torsion. Consequently the curve on which the rational $p$-torsion appears would have both full rational two-torsion and a rational point of order $p$. The formal-immersion prime-torsion theorem eliminates large $p$, while exact low-genus calculations eliminate $p=5$ and $p=7$.

The point of the argument is not merely its short conclusion. Several superficially similar local statements have different hypotheses. Away from $p$, semistability makes diagonal characters unramified. At $p$, good reduction leads to finite-flat group schemes and the Oort--Tate dichotomy, whereas multiplicative reduction leads to the Tate curve and need not make the whole residual representation finite flat. Keeping these branches separate is what makes the global argument valid.

### 1.1 From a matrix question to an isogeny

Let $E/mathbf Q$ be an elliptic curve and let $p$ be a prime. Since the ground field has characteristic zero,

$$
E[p](\overline{\mathbf Q})\simeq \mathbf F_p^2.
$$

Choosing a basis gives

$$
\overline\rho_{E,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p),
$$

well defined up to conjugacy. The question whether this representation is reducible is basis independent: it asks whether $E[p]$ has a $G_{\mathbf Q}$-stable line.

Book 51 proves the isogeny--line equivalence with exactly the hypothesis needed here. Because $p$ is invertible in $mathbf Q$, a stable line is a finite étale subgroup scheme $C\subset E[p]$ of order $p$, defined over $mathbf Q$. The quotient $E/C$ exists, and

$$
\varphi:E\longrightarrow E'=E/C
$$

is a $mathbf Q$-rational isogeny of degree $p$. Conversely, the kernel of every rational degree-$p$ isogeny is such a line. Thus

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

An elliptic curve over $mathbf Q$ is **semistable** when it has good or multiplicative reduction at every prime. Full rational two-torsion means

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
$$

or equivalently that the finite étale group scheme $E[2]$ is constant. A rational $p$-isogeny means an isogeny defined over $mathbf Q$; it does not mean that its kernel has a rational generator.

Throughout the main isogeny argument, $p\ge5$ is prime. This avoids the collapse of the two coefficient-prime inertia characters at $p=2$ and places the final application in the range relevant to Frey curves. The final Frey theorem will be stated for $p\ge7$, exactly as required for prime exponents remaining after the separate small-exponent arguments.

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

For a curve with full rational two-torsion, an odd isogeny carries that structure to the quotient. Prime-torsion and mixed-torsion theorems then contradict the last line. For a Frey curve, direct invariant calculations establish semistability and display full rational two-torsion, so the criterion applies without any modularity input.

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

is defined over $mathbf Q$. In a basis $(P,Q)$ beginning with a generator of $C$,

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

Let $\widehat\varphi:E'\to E$ be the dual isogeny. Book 38 identifies its kernel with the Cartier dual $C^D$, and Book 51 identifies the generic character of that dual with the cyclotomic dual of $\lambda$. Thus

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

The subgroup $C$ is defined over $mathbf Q$ precisely because Galois preserves it. A generator is rational precisely when Galois fixes it pointwise. Therefore

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

Suppose $E$ has good reduction at $q\ne p$. The prime-to-residue-characteristic specialization theorem from Book 51 identifies $E[p]$ with the geometric $p$-torsion of the special fiber. Equivalently,

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

Suppose $E/\mathbf Q_q$ has split multiplicative reduction. Book 50 supplies a Tate parameter $u\in\mathbf Q_q^\times$ with $v_q(u)>0$ and a Galois-equivariant exact sequence

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

### 3.4 The conductor interpretation

For every semistable prime $q\ne p$, we have proved

$$
a_q(\lambda)=a_q(\mu)=0.
\tag{3.6}
$$

At a multiplicative prime the full two-dimensional representation can still be ramified: the off-diagonal Kummer class in (3.5) has conductor exponent one when $p\nmid m$. The semisimplification is unramified in all cases. Thus diagonal unramifiedness is strictly weaker than unramifiedness of $E[p]$.

More precisely,

$$
\overline\rho_{E,p}|_{I_q}=1
\quad\Longleftrightarrow\quad
p\mid v_q(\Delta_{\min})
\tag{3.7}
$$

at a multiplicative prime $q\ne p$. Equation (3.7) will later explain why much of the ramification of a Frey curve disappears modulo its exponent. It is not needed for the diagonal-character theorem, which uses only the unipotence of (3.5).

## 4. Good reduction at the coefficient prime

At $q=p$, the cyclotomic character is ramified. Good reduction no longer gives an unramified $p$-torsion representation, but it does give a finite-flat integral model. A stable generic line can then be closed in that model, and the rank-$p$ classification over the unramified base $\mathbf Z_p$ leaves exactly two integral types.

### 4.1 Why unramifiedness is the wrong condition

Suppose $E/\mathbf Q_p$ has good reduction. It extends to an elliptic scheme $\mathcal E/\mathbf Z_p$, and

$$
\mathcal E[p]
$$

is finite flat of rank $p^2$. Its generic fiber is $E[p]$. This is the coefficient-prime local condition supplied by Books 48 and 51.

The group $\mu_p$ over $\mathbf Z_p$ is finite flat, but its generic points carry $\overline\chi_p$, which is nontrivial on inertia. Thus

$$
\text{finite flat at }p\not\Longrightarrow\text{unramified at }p.
$$

The integral model distinguishes an étale direction from a multiplicative direction; these become the two allowable inertia characters.

### 4.2 Closing the invariant line

Let $C\subset E[p]$ be the stable line with character $\lambda$. Regard $C$ as a finite étale subgroup of the generic fiber of $\mathcal E[p]$. By the closure theorem of Books 48 and 56, its schematic closure

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

Book 56 classifies order-$p$ finite-flat groups over a mixed-characteristic DVR. With $e=v(p)$ and Oort--Tate exponent $r$, one has

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

Equation (4.5) is stronger than merely knowing their product. It uses finite-flat geometry to show that no intermediate tame exponent occurs over the unramified base. Over a ramified extension of $\mathbf Q_p$ with $e>1$, intermediate exponents $0<r<e$ can occur and (4.4) can fail. The fact that the global base is $mathbf Q$ is therefore used locally through $\mathbf Q_p/\mathbf Q_p$ having absolute ramification index one.

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

### 5.4 Finite-flatness and discriminant divisibility

The Tate exact sequence has a canonical finite-flat extension over $\mathbf Z_p$ exactly when its Kummer class has a unit representative. If

$$
u=p^m a,
\qquad a\in\mathbf Z_p^\times,
$$

then multiplication by a $p$th power changes $m$ by a multiple of $p$. Hence

$$
[u]\text{ comes from }\mathbf Z_p^\times/(\mathbf Z_p^\times)^p
\quad\Longleftrightarrow\quad
p\mid m.
\tag{5.5}
$$

Book 50 constructs the corresponding finite-flat extension explicitly and proves that, for odd $p$ over the unramified base, any finite-flat model must preserve the intrinsic cyclotomic line. Therefore

$$
E[p]\text{ is finite flat over }\mathbf Z_p
\quad\Longleftrightarrow\quad
p\mid v_p(\Delta_{\min})
\tag{5.6}
$$

for multiplicative $E/\mathbf Q_p$ and odd $p$.

Equation (5.6) is important for Frey ramification, but it is not needed to prove (5.3). The inertial alternatives hold for every multiplicative curve, even when $p\nmid v_p(\Delta_{\min})$ and the full residual representation is not finite flat. This separation closes a common logical gap.

## 6. The semistable local character theorem

Good and multiplicative reduction have now been treated by different integral mechanisms. We can combine their conclusions into one local theorem, while retaining the proof branches that justify it.

### 6.1 Statement and proof

**Theorem 6.1 (semistable isogeny-character alternatives).** Let $p\ge5$ be prime, let $E/\mathbf Q$ be semistable, and let $C\subset E[p]$ be a $G_{\mathbf Q}$-stable line with character $\lambda$. Put

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

Second, the global field is $mathbf Q$. Over a local field with absolute ramification index $e>1$, an order-$p$ finite-flat line may have Oort--Tate exponent strictly between $0$ and $e$, producing inertia $\theta^r$ rather than $1$ or $\overline\chi_p$.

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

There is an equivalent ray-class proof. An abelian extension of $mathbf Q$ unramified at finite places is contained in the ray class field of modulus consisting only of the real place. The corresponding narrow ideal class group of $mathbf Q$ is trivial because every fractional ideal has a positive rational generator. The discriminant proof has the advantage of treating possible complexification at infinity without an extra sign discussion.

### 7.3 The semistable isogeny theorem

**Theorem 7.2 (rational torsion on one side).** Let $p\ge5$ be prime. Let $E/\mathbf Q$ be semistable and suppose that $E$ has a rational isogeny

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

Nor can one replace Lemma 7.1 by the assertion that every unramified local character is trivial. Unramified local characters may have nontrivial Frobenius values. It is the simultaneous absence of ramification at all finite primes, together with the global arithmetic of $mathbf Q$, that forces triviality.

## 8. Prime torsion over the rationals

The semistable isogeny theorem reduces reducibility to rational prime torsion, but rational points of order $5$ and $7$ exist. We first state the exact large-prime theorem available from the formal-immersion and Mordell--Weil-sieve prerequisites, then isolate the two mixed cases that need full rational two-torsion.

### 8.1 The formal-immersion range

Book 147 studies a rational point $P$ of prime order $p$ through its point on $X_1(p)$. For $p\ge11$, reduction modulo $3$ cannot remain in the interior: the Hasse bound gives

$$
\#\widetilde E(\mathbf F_3)\le7<p.
$$

Nor can the reduction lie in the identity torus of a boundary fiber, because $\mathbf F_3^\times$ has order two. The modular point therefore reduces to an outward rational cusp.

For $p\ge17$, the corrected Eisenstein index

$$
n_p=\frac{p-1}{\gcd(p-1,12)}
$$

is greater than one. The selected Eisenstein quotient is finite on rational points and the pointed modular map is a formal immersion at the outward cusp. Cusp-disk rigidity forces the modular point to equal the cusp, contradicting that it represents a smooth elliptic curve. Hence no rational point of prime order $p\ge17$ exists.

The denominator in $n_p$ is essential. At $p=13$, $n_{13}=1$, so the selected quotient used in the uniform proof does not exist. Level thirteen must be handled by its actual genus-two curve.

### 8.2 The exceptional levels eleven and thirteen

Book 147 identifies $X_1(11)$ with

$$
y^2+y=x^3-x^2
$$

and proves that its five rational points are precisely its five cusps. Therefore no elliptic curve over $mathbf Q$ has a rational point of order $11$.

Book 152 completes the level-thirteen handoff. On the model

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

The next invariant survives passage from $E$ to $E/C$. The clean statement is scheme-theoretic and works over any base, although the rational-point consequence is used over $mathbf Q$.

### 9.1 The Bezout inverse

Let $\varphi:A\to B$ be an isogeny of odd degree $d$ between abelian schemes. Book 38 supplies a quasi-inverse $\varphi':B\to A$ such that

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

For $p=5$ and $p=7$, the exact impossibility of (9.7) is the remaining arithmetic input.

## 10. The exceptional primes five and seven

The large-prime theorem begins at eleven. The primes five and seven are not errors in the bound: elliptic curves over $mathbf Q$ can have rational points of those orders. The extra full two-torsion must be used, and it leads to two explicit low-genus parameter curves.

### 10.1 Why the prime-torsion theorem leaves two cases

Suppose a semistable curve with full rational two-torsion has a rational $p$-isogeny. Theorem 7.2 places rational $p$-torsion on one of the two isogenous curves, and Theorem 9.1 gives full rational two-torsion on that same curve. If $p\ge11$, Theorem 8.1 immediately contradicts the rational point. For $p=5$ and $p=7$, one must instead contradict the mixed subgroup (9.7).

The low-prime calculations begin with Tate normal form for a point $P$ of order at least four:

$$
Y^2+(1-c)XY-bY=X^3-bX^2,
\qquad P=(0,0).
\tag{10.1}
$$

The order conditions give

$$
(b,c)=(t,t)\quad\text{for order }5,
$$

and

$$
(b,c)=(t^3-t^2,t^2-t)\quad\text{for order }7.
$$

Full rational two-torsion makes the cubic of nonzero two-torsion $x$-coordinates split over $mathbf Q$. Its discriminant must therefore be a square. Only this necessary direction is used; a square cubic discriminant does not by itself imply splitting.

### 10.2 The five-primary mixed curve

For order five, the square-discriminant condition leads to the genus-one curve

$$
C_5:s^2=t(t^2-11t-1).
\tag{10.2}
$$

Book 147 carries out the complete descent and reduction calculation and proves

$$
C_5(\mathbf Q)=\{\infty,(0,0)\}.
\tag{10.3}
$$

The affine point has $t=0$, which is a degenerate Tate parameter, and the point at infinity is boundary. Hence no smooth elliptic curve over $mathbf Q$ has both full rational two-torsion and a rational point of order five. Equivalently,

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/10\mathbf Z
\not\subset E(\mathbf Q)
\tag{10.4}
$$

for every elliptic curve $E/\mathbf Q$.

The logic is one-way and sufficient. A forbidden elliptic configuration gives a nondegenerate rational point of $C_5$; the complete rational-point set contains none. It is unnecessary to reconstruct an elliptic curve from every point of $C_5$.

### 10.3 The mixed-seven curve

For order seven, the necessary square-discriminant condition gives

$$
C_7:z^2=t(t-1)(t^3-8t^2+5t+1).
\tag{10.5}
$$

This is a smooth genus-two curve. Book 152 imports the exact Mordell--Weil group

$$
J_7(\mathbf Q)
\simeq\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2
$$

and checks all twelve reduced divisor classes. Exactly three lie on the pointed Abel image. It proves

$$
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.
\tag{10.6}
$$

The parameters $t=0$ and $t=1$ are degenerate, and the point at infinity is boundary. Thus no nondegenerate mixed-seven configuration exists, and

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/14\mathbf Z
\not\subset E(\mathbf Q)
\tag{10.7}
$$

for every elliptic curve $E/\mathbf Q$.

### 10.4 The exact mixed-torsion exclusion

**Theorem 10.1 (mixed five and seven).** Let $E/\mathbf Q$ have full rational two-torsion. Then

$$
E(\mathbf Q)[5]=0
\qquad\text{and}\qquad
E(\mathbf Q)[7]=0.
\tag{10.8}
$$

**Proof.** A rational point of order $5$ would combine with $E[2](\mathbf Q)$ to give the subgroup in (10.4), which the complete calculation (10.3) excludes. A rational point of order $7$ would give the subgroup in (10.7), excluded by (10.6). $\square$

No semistability hypothesis is needed in Theorem 10.1. Semistability entered earlier only to turn a rational isogeny into rational torsion on one side.

## 11. Irreducibility for semistable curves with full two-torsion

All layers can now be assembled. The main criterion is slightly stronger than the final Frey statement: it applies to every semistable elliptic curve over $mathbf Q$ with full rational two-torsion and every prime $p\ge5$.

### 11.1 The main criterion

**Theorem 11.1 (semistable full-two-torsion irreducibility).** Let $E/\mathbf Q$ be semistable and suppose

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
$$

Then for every prime $p\ge5$,

$$
\overline\rho_{E,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
$$

is irreducible.

This theorem is tailored to the Frey configuration. Its proof needs neither modularity of $E$ nor a classification of all rational isogenies.

### 11.2 Proof by passage across the isogeny

**Proof strategy.** Assume reducibility, pass to the rational $p$-isogeny, make one kernel rationally generated by the global character theorem, carry full two-torsion across the odd isogeny, and apply the exact torsion exclusions.

**Proof.** Suppose $E[p]$ is reducible. By (1.1), there is a rational degree-$p$ isogeny

$$
\varphi:E\longrightarrow E'=E/C.
$$

Theorem 7.2 gives

$$
E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.
\tag{11.1}
$$

Since $p$ is odd, Theorem 9.1 gives a Galois-equivariant isomorphism

$$
E[2]\simeq E'[2].
$$

Thus both $E$ and $E'$ have full rational two-torsion. Let $A$ denote the curve on the side of (11.1) carrying the rational point of order $p$.

If $p\ge11$, Theorem 8.1 says $A(\mathbf Q)[p]=0$, a contradiction. If $p=5$ or $p=7$, Theorem 10.1 gives the same contradiction using full rational two-torsion. These cases exhaust all primes $p\ge5$. Therefore $E[p]$ is irreducible. $\square$

### 11.3 What the theorem does and does not say

The theorem proves irreducibility over $\mathbf F_p$, which is exactly equivalent to the absence of a rational degree-$p$ isogeny. It does not assert absolute irreducibility after every coefficient extension; that is a different group-theoretic question. It does not classify the image of the representation, which may lie in a Cartan normalizer or another proper irreducible subgroup.

The full rational two-torsion hypothesis is essential to the small-prime conclusion. Curves with rational points of order five or seven exist, and some semistable curves have rational isogenies of those degrees. The theorem excludes them only in the full-two-torsion isogeny class.

Semistability is essential to the character argument. Without it, additive primes can ramify the diagonal characters, so neither $\lambda$ nor $\mu$ need be everywhere unramified. The proof does not claim otherwise.

## 12. The Frey curve

We now verify the two geometric hypotheses of Theorem 11.1 directly from a primitive Fermat-type triple. The discriminant factorization handles odd primes. The prime two requires a genuine minimal coordinate change; using the raw equation there would give the wrong discriminant exponent.

### 12.1 Normalization of a primitive triple

Let $p\ge7$ be prime and suppose

$$
a^p+b^p=c^p
\tag{12.1}
$$

is a primitive nontrivial integer solution:

$$
abc\ne0,
\qquad
\gcd(a,b,c)=1.
$$

Exactly one of $a,b,c$ is even. Indeed, they cannot all be even by primitivity. If $a$ and $b$ are both odd, then $c$ is even; if exactly one of $a,b$ is even, then $c$ is odd. They cannot both be even. Rewriting the signed three-term equation and changing all signs if necessary lets us arrange

$$
a\text{ even},
\qquad b,c\text{ odd},
\qquad b\equiv1\pmod4.
\tag{12.2}
$$

The operations only permute the three roots used below and replace the curve by an isomorphic member of the same normalized Frey configuration.

Put

$$
A=a^p,
\qquad B=b^p,
\qquad C=c^p=A+B.
\tag{12.3}
$$

The Frey curve is

$$
E=E_{a,b,p}:
\qquad y^2=x(x-A)(x+B).
\tag{12.4}
$$

The three roots $0,A,-B$ are distinct because $ABC\ne0$. Thus (12.4) is a nonsingular elliptic curve.

### 12.2 Visible two-torsion and invariants

The three nonzero points

$$
(0,0),\qquad(A,0),\qquad(-B,0)
\tag{12.5}
$$

are rational and have order two. Together with the origin they exhaust $E[2]$, so

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
\tag{12.6}
$$

Expanding gives

$$
y^2=x^3+(B-A)x^2-ABx.
$$

The integral Weierstrass formulas of Book 49 yield

$$
\begin{aligned}
c_4&=16(A^2+AB+B^2),\\
c_6&=-32(B-A)(2A^2+5AB+2B^2),\\
\Delta&=16A^2B^2C^2=2^4(abc)^{2p},\\
j&=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.
\end{aligned}
\tag{12.7}
$$

The discriminant is $16$ times the square of the product of the three root differences. This factorization makes the local thickness at odd primes a multiple of $p$.

### 12.3 Odd-prime reduction

Let $q$ be odd. Primitivity implies that $q$ divides at most one of $a,b,c$. If $q\nmid abc$, then $\Delta$ is a $q$-adic unit, so $E$ has good reduction at $q$.

Suppose $q\mid a$. Then $B$ and $C$ are units and

$$
A^2+AB+B^2\equiv B^2\not\equiv0\pmod q.
$$

Thus $c_4$ is a unit. The displayed integral equation is minimal, because an integral improvement would force $q\mid c_4$. Since $v_q(\Delta)>0$, the reduction is multiplicative. Moreover

$$
v_q(\Delta_{\min})=2p\,v_q(a).
\tag{12.8}
$$

The same proof, using the appropriate root difference, gives

$$
v_q(\Delta_{\min})=
\begin{cases}
2p\,v_q(a),&q\mid a,\\
2p\,v_q(b),&q\mid b,\\
2p\,v_q(c),&q\mid c.
\end{cases}
\tag{12.9}
$$

Hence every odd bad prime is multiplicative. In particular, the curve is semistable away from two.

### 12.4 The minimal model at two

The raw equation (12.4) is not minimal at two. From (12.2),

$$
v_2(A)=p\,v_2(a)\ge p\ge7,
\qquad
B-A\equiv1\pmod4.
\tag{12.10}
$$

Make the change

$$
x=4x',
\qquad
y=8y'+4x'.
\tag{12.11}
$$

Substitution into (12.4) and division by $64$ give

$$
y'^2+x'y'
=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'.
\tag{12.12}
$$

Both coefficients are integral: the first by (12.10), the second because $v_2(A)\ge7$. The transformation has scale factor $2$, so the invariants change by weights four and twelve. Thus

$$
c_{4,\min}=A^2+AB+B^2,
\qquad
\Delta_{\min}=2^{-8}A^2B^2C^2.
\tag{12.13}
$$

Since $A$ is even and $B$ is odd,

$$
A^2+AB+B^2\equiv1\pmod2.
$$

Therefore $c_{4,\min}$ is a unit. The integral equation (12.12) is minimal and has multiplicative reduction. Its discriminant exponent is

$$
v_2(\Delta_{\min})
=2p\,v_2(a)-8>0.
\tag{12.14}
$$

The subtraction of eight is indispensable. Applying the raw exponent $4+2p,v_2(a)$ would miss the admissible coordinate improvement and give incorrect residual inertia at two.

### 12.5 Semistability

**Proposition 12.1 (Frey semistability).** The Frey curve (12.4) is semistable over $mathbf Q$. It has good reduction outside $2abc$ and multiplicative reduction at every prime dividing $2abc$.

**Proof.** Section 12.3 proves the statement at every odd prime. Section 12.4 proves multiplicative reduction at two. These cases exhaust all finite primes. $\square$

Together, (12.6) and Proposition 12.1 give exactly the hypotheses of Theorem 11.1.

## 13. Frey residual irreducibility

The local calculations and the semistable isogeny theorem now meet. The irreducibility proof itself is short because every exceptional case has already been isolated and proved.

### 13.1 The residual representation

The action of $G_{\mathbf Q}$ on $E[p]$ gives

$$
\overline\rho_{a,b,p}:G_{\mathbf Q}
\longrightarrow\operatorname{GL}_2(\mathbf F_p),
\tag{13.1}
$$

with

$$
\det\overline\rho_{a,b,p}=\overline\chi_p.
\tag{13.2}
$$

The representation is continuous and defined up to conjugacy. Its irreducibility is therefore an intrinsic statement about the absence of a $G_{\mathbf Q}$-stable subgroup of order $p$ in $E[p]$.

### 13.2 The contradiction argument

**Theorem 13.1 (Frey residual irreducibility).** Let $p\ge7$ be prime, and let $(a,b,c)$ be a primitive nontrivial integer solution of

$$
a^p+b^p=c^p.
$$

For the Frey curve (12.4), the representation (13.1) is irreducible.

**Proof strategy.** Reducibility gives a rational isogeny. Semistability makes one of its two kernel characters trivial. The corresponding isogenous curve has rational $p$-torsion and still has full rational two-torsion. The exact prime- and mixed-torsion theorems give the contradiction.

**Proof.** Suppose $\overline\rho_{a,b,p}$ is reducible. By the isogeny--line equivalence there is a rational degree-$p$ isogeny

$$
\varphi:E\to E'=E/C.
$$

Proposition 12.1 makes $E$ semistable. Theorem 7.2 therefore gives rational $p$-torsion on $E$ or on $E'$. Equation (12.6) gives full rational two-torsion on $E$, and Theorem 9.1 transports it to $E'$ because $p$ is odd.

If $p\ge11$, rational $p$-torsion contradicts Theorem 8.1. The only remaining prime in the stated range is $p=7$, and then full rational two-torsion together with rational seven-torsion contradicts Theorem 10.1. Hence reducibility is impossible. $\square$

The stronger Theorem 11.1 also covers $p=5$. The present statement begins at seven because that is the exact residual-irreducibility range required after the separate exponent-five treatment.

### 13.3 The local ramification ledger

Although irreducibility uses only semistability and two-torsion, the Frey equation gives more precise local information.

At an odd prime $q\mid abc$ with $q\ne p$, equations (12.9) and (3.7) give

$$
p\mid v_q(\Delta_{\min})
\quad\Longrightarrow\quad
\overline\rho_{a,b,p}|_{I_q}=1.
\tag{13.3}
$$

At two,

$$
v_2(\Delta_{\min})
=2p\,v_2(a)-8\equiv-8\pmod p.
$$

For $p\ge7$, this is nonzero modulo $p$, so multiplicative inertia remains nontrivial:

$$
\overline\rho_{a,b,p}|_{I_2}\ne1.
\tag{13.4}
$$

At the coefficient prime $p$, there are two cases. If $p\nmid abc$, the curve has good reduction and $E[p]$ is finite flat over $\mathbf Z_p$. If $p\mid abc$, it has multiplicative reduction and (12.9) gives

$$
p\mid v_p(\Delta_{\min});
$$

the coefficient-prime Tate criterion (5.6) again makes $E[p]$ finite flat over $\mathbf Z_p$. Thus

$$
E[p]\text{ is finite flat at }p
\tag{13.5}
$$

for the Frey curve. This conclusion is stronger than what was required for the isogeny-character alternatives.

The conductor picture is consequently sharp. Away from $2p$, the residual representation is unramified at every prime dividing $abc$. At two it has the nontrivial semistable unipotent contribution. At $p$ its correct integral condition is finite flat, not unramifiedness.

### 13.4 All prime exponents at least seven

The proof contains no hidden congruence class of $p$. The large-prime torsion theorem treats $p=11$, $p=13$, and all $p\ge17$ through their exact separate branches. The mixed-seven calculation treats $p=7$. There is no prime strictly between $7$ and $11$. Therefore Theorem 13.1 covers every prime exponent $p\ge7$.

Nor does the proof assume that the original kernel of a hypothetical isogeny has a rational generator. The global argument explicitly permits the rational point to appear on the dual side. Odd-isogeny invariance is what keeps the two-torsion hypothesis available after that switch.

## 14. Dependency and hypothesis audit

The proof is short only because its imports have been kept exact. This chapter records each substantial dependency, the hypothesis under which it is used, and the conclusions proved here rather than imported.

### 14.1 Imported local results

**Book 49.** Integral Weierstrass invariants, minimality criteria, and the good/multiplicative reduction test justify (12.7)--(12.14). Its primitive Frey-curve calculation supplies the admissible dyadic change and verifies that the transformed equation is minimal. We use no coarse additive-reduction shortcut.

**Book 50.** Tate uniformization supplies (3.3), (3.5), (5.1), and their unramified quadratic twists. Its Kummer calculation proves the residual unramified criterion away from the coefficient prime and the canonical finite-flat criterion at the coefficient prime. We use the latter as a criterion for the abstract representation only over the unramified base and for odd $p$, exactly where the intrinsic-line proof applies.

**Book 51.** The Weil pairing supplies the cyclotomic determinant; a stable line is equivalent to a rational prime-degree isogeny; the dual line has character $\overline\chi_p\lambda^{-1}$; good reduction away from $p$ gives unramifiedness; and the Frey torsion representation is two-dimensional because the ground field has characteristic zero.

**Book 48.** A good model supplies a finite-flat torsion representation at the coefficient prime. Schematic closure carries a stable generic line to a finite-flat subgroup in a fixed ambient model, and the represented quotient has the correct generic character. We do not infer that every extension of finite-flat endpoints is finite flat.

**Book 56.** Over an unramified mixed-characteristic DVR, every order-$p$ finite-flat group is étale or multiplicative. The inertia formula identifies their generic restrictions as $1$ or $\overline\chi_p$, and Cartier duality exchanges the alternatives. Intermediate exponents over ramified bases are explicitly excluded from the global-$\mathbf Q$ theorem.

**Book 38.** Quotients by finite subgroup schemes, dual kernels, quasi-inverses of isogenies, and odd-isogeny invariance of two-torsion justify the passage between $E$ and $E/C$. The two-torsion result is used as a group-scheme isomorphism, not merely as equality of point counts.

### 14.2 Imported global and geometric results

**Book 6.** Finite Galois characters correspond to finite-order idele class characters; conductor exponent zero means unramified; and the conductor--discriminant formula gives (7.3). Applied to $mathbf Q$, this proves that a finite character unramified at every finite prime is trivial. No prime-distribution theorem is required.

**Book 147.** The selected Eisenstein quotient and formal immersion exclude rational points of prime order $p\ge17$. The separate genus-one calculation excludes $p=11$. The same book proves the complete five-primary mixed-torsion exclusion and derives the mixed-seven curve with the logically correct necessary direction.

**Book 152.** The exhaustive Mordell--Weil sieve proves that $X_1(13)(\mathbf Q)$ consists of its six cusps and that the mixed-seven curve has only $\infty,(0,0),(1,0)$. These results close the exceptional prime $13$ and the mixed prime $7$ respectively. We use the exact rational-point sets, not an uncertified search or a finite-index subgroup of a Jacobian.

No later book enters any proof. In particular, Frey irreducibility is established before any modularity-lifting or final Fermat synthesis.

### 14.3 Exceptional-prime and normalization ledger

The exceptional cases are summarized as follows.

| Place or prime | Input | Exact conclusion |
|---|---|---|
| $q\ne p$, good | prime-to-$q$ specialization | both diagonal characters unramified |
| $q\ne p$, multiplicative | Tate unipotence | both diagonal characters unramified; the extension may remain ramified |
| $q=p$, good | finite-flat closure and $e=1$ | diagonal inertia is $1$ or $\overline\chi_p$ |
| $q=p$, multiplicative | Tate exact sequence | every stable line has inertia $1$ or $\overline\chi_p$ |
| $p=5$ | complete mixed-five curve | no full-two-torsion curve has rational $5$-torsion |
| $p=7$ | complete mixed-seven curve | no full-two-torsion curve has rational $7$-torsion |
| $p=11$ | genus-one $X_1(11)$ calculation | no rational $11$-torsion |
| $p=13$ | genus-two sieve on $X_1(13)$ | no rational $13$-torsion |
| $p\ge17$ | oriented formal immersion | no rational $p$-torsion |
| $q=2$ on the Frey curve | dyadic minimal change | $v_2(\Delta_{\min})=2p,v_2(a)-8$ |

Arithmetic Frobenius is used throughout. The determinant is the mod-$p$ cyclotomic character for the covariant action on torsion points. The nonsplit multiplicative character is unramified. Full rational two-torsion is transported only across odd-degree isogenies. Square discriminant of the two-torsion cubic is used only as a necessary condition in the mixed-five and mixed-seven reductions.

### 14.4 Conclusion

A reducible elliptic-curve torsion representation contains a line, but semistability makes that line far more rigid than an arbitrary character. Away from the coefficient prime, good reduction and multiplicative unipotence erase diagonal inertia. At the coefficient prime, finite-flat closure in the good case and the Tate exact sequence in the multiplicative case leave only the trivial and cyclotomic alternatives. Duality makes those alternatives complementary.

Global class field theory then supplies the decisive collapse: one diagonal character is unramified at every finite prime, and over $mathbf Q$ such a finite character is trivial. A semistable rational $p$-isogeny therefore has a rationally generated kernel on one side. An odd isogeny preserves full rational two-torsion, so in the Frey isogeny class this rational point would create forbidden mixed torsion. Formal immersion excludes prime torsion from eleven upward, while the exact five- and seven-primary curves close the small cases.

For a primitive Fermat-type triple, the Frey equation displays all two-torsion and factors its discriminant into the square of the three root differences. The odd-prime calculation and the corrected minimal model at two prove semistability. The general criterion then proves that its mod-$p$ representation is irreducible for every prime exponent at least seven. The resulting package is fully local at its inputs, global only in the one-dimensional class-field step, and exact at every exceptional prime.
