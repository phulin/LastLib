# Rational Isogenies of Prime Degree

## Contents

1. [The problem, the scope, and the route](#1-the-problem-the-scope-and-the-route)
   - [Three questions attached to one prime](#11-three-questions-attached-to-one-prime)
   - [Standing conventions](#12-standing-conventions)
   - [The exact boundary of the book](#13-the-exact-boundary-of-the-book)
   - [The proof architecture](#14-the-proof-architecture)
2. [From invariant lines to modular points](#2-from-invariant-lines-to-modular-points)
   - [Stable lines and finite subgroup schemes](#21-stable-lines-and-finite-subgroup-schemes)
   - [A subgroup is not a generator](#22-a-subgroup-is-not-a-generator)
   - [The complementary character and the dual isogeny](#23-the-complementary-character-and-the-dual-isogeny)
   - [$X_0(p)$, $X_1(p)$, and coarse descent](#24-x_0p-x_1p-and-coarse-descent)
   - [Specialization of the modular point](#25-specialization-of-the-modular-point)
3. [Semistable characters away from the coefficient prime](#3-semistable-characters-away-from-the-coefficient-prime)
   - [Good reduction](#31-good-reduction)
   - [Split multiplicative reduction](#32-split-multiplicative-reduction)
   - [Nonsplit multiplicative reduction](#33-nonsplit-multiplicative-reduction)
   - [The precise away-from-$p$ conclusion](#34-the-precise-away-from-p-conclusion)
4. [The coefficient-prime dichotomy](#4-the-coefficient-prime-dichotomy)
   - [Good reduction and schematic closure](#41-good-reduction-and-schematic-closure)
   - [Order-$p$ groups over the unramified base](#42-order-p-groups-over-the-unramified-base)
   - [Multiplicative reduction and the Tate extension](#43-multiplicative-reduction-and-the-tate-extension)
   - [The semistable local theorem](#44-the-semistable-local-theorem)
5. [The global semistable isogeny theorem](#5-the-global-semistable-isogeny-theorem)
   - [Choosing the unramified diagonal](#51-choosing-the-unramified-diagonal)
   - [Everywhere-unramified characters of the rationals](#52-everywhere-unramified-characters-of-the-rationals)
   - [Rational torsion on one side](#53-rational-torsion-on-one-side)
   - [Why the theorem is genuinely semistable](#54-why-the-theorem-is-genuinely-semistable)
6. [Prime torsion and the oriented modular curve](#6-prime-torsion-and-the-oriented-modular-curve)
   - [Why rational torsion belongs to $X_1(p)$](#61-why-rational-torsion-belongs-to-x_1p)
   - [The formal-immersion mechanism](#62-the-formal-immersion-mechanism)
   - [The uniform range $p\ge17$](#63-the-uniform-range-pge17)
   - [The level-eleven calculation](#64-the-level-eleven-calculation)
   - [The level-thirteen problem](#65-the-level-thirteen-problem)
7. [The exact rational points of $X_1(13)$](#7-the-exact-rational-points-of-x_113)
   - [The genus-two model and its cusps](#71-the-genus-two-model-and-its-cusps)
   - [The complete Mordell--Weil group](#72-the-complete-mordell--weil-group)
   - [A terminal reduction at seventeen](#73-a-terminal-reduction-at-seventeen)
   - [Exhaustion and uniqueness](#74-exhaustion-and-uniqueness)
   - [The prime-torsion theorem](#75-the-prime-torsion-theorem)
8. [Odd isogenies and full rational two-torsion](#8-odd-isogenies-and-full-rational-two-torsion)
   - [Preservation of two-torsion as a group scheme](#81-preservation-of-two-torsion-as-a-group-scheme)
   - [The mixed torsion forced by a rational generator](#82-the-mixed-torsion-forced-by-a-rational-generator)
   - [Why seven is the remaining prime](#83-why-seven-is-the-remaining-prime)
9. [Tate normal form and the mixed-seven curve](#9-tate-normal-form-and-the-mixed-seven-curve)
   - [Normalizing a point of odd order](#91-normalizing-a-point-of-odd-order)
   - [The order-seven locus](#92-the-order-seven-locus)
   - [The cubic of two-torsion coordinates](#93-the-cubic-of-two-torsion-coordinates)
   - [The necessary genus-two condition](#94-the-necessary-genus-two-condition)
10. [The exact arithmetic of the mixed-seven curve](#10-the-exact-arithmetic-of-the-mixed-seven-curve)
    - [The pointed curve and visible classes](#101-the-pointed-curve-and-visible-classes)
    - [The complete Jacobian](#102-the-complete-jacobian)
    - [All twelve reduced classes](#103-all-twelve-reduced-classes)
    - [The Abel-image test](#104-the-abel-image-test)
    - [The mixed-seven exclusion](#105-the-mixed-seven-exclusion)
11. [The semistable full-two irreducibility criterion](#11-the-semistable-full-two-irreducibility-criterion)
    - [Statement and motivation](#111-statement-and-motivation)
    - [Proof across the isogeny](#112-proof-across-the-isogeny)
    - [Hypotheses and exceptions](#113-hypotheses-and-exceptions)
12. [The Frey curve and its normalization](#12-the-frey-curve-and-its-normalization)
    - [Primitive triples and parity](#121-primitive-triples-and-parity)
    - [The curve, its two-torsion, and its invariants](#122-the-curve-its-two-torsion-and-its-invariants)
    - [Odd-prime minimal models](#123-odd-prime-minimal-models)
    - [The minimal model at two](#124-the-minimal-model-at-two)
    - [Semistability](#125-semistability)
13. [Residual irreducibility of the Frey curve](#13-residual-irreducibility-of-the-frey-curve)
    - [The contradiction argument](#131-the-contradiction-argument)
    - [The exponent seven](#132-the-exponent-seven)
    - [Every prime exponent at least eleven](#133-every-prime-exponent-at-least-eleven)
    - [The local ramification ledger](#134-the-local-ramification-ledger)
14. [The exponent-five boundary](#14-the-exponent-five-boundary)
    - [Why the residual theorem stops at seven](#141-why-the-residual-theorem-stops-at-seven)
    - [The cyclotomic descent route](#142-the-cyclotomic-descent-route)
    - [Logical separation from the isogeny argument](#143-logical-separation-from-the-isogeny-argument)
15. [Dependency audit and final theorem package](#15-dependency-audit-and-final-theorem-package)
    - [Imported results with matching hypotheses](#151-imported-results-with-matching-hypotheses)
    - [Exceptional cases and normalization ledger](#152-exceptional-cases-and-normalization-ledger)
    - [Final theorems](#153-final-theorems)
    - [Conclusion](#154-conclusion)

## 1. The problem, the scope, and the route

The phrase *rational prime-degree isogeny* joins three different kinds of
structure. An isogeny is a morphism of elliptic curves. Its kernel is a
finite subgroup scheme. Over a characteristic-zero field, its geometric
points form a line in a two-dimensional residual representation. The first
task of this book is to move correctly among these descriptions. The second
is to exploit semistable reduction, which makes the character on that line
extraordinarily rigid. The third is to apply the resulting rigidity to the
Frey curve.

The central theorem is not the classification of all prime degrees which
occur among all elliptic curves over $\mathbf Q$. Such a classification
requires local character tables and rational-point arguments outside the
declared dependency package. The theorem proved here is the exact one needed
for the Frey curve: if a semistable elliptic curve over $\mathbf Q$ has full
rational two-torsion, then its mod-$p$ representation is irreducible for every
prime $p\ge7$. The exceptional prime $7$ is closed by the mixed-seven
genus-two calculation. The exceptional point-level prime $13$ is closed by
the complete calculation on $X_1(13)$.

### 1.1 Three questions attached to one prime

Let $E/\mathbf Q$ be an elliptic curve and let $p$ be prime. There are three
questions which must initially remain separate.

1. Does $E[p]$ contain a $G_{\mathbf Q}$-stable line?
2. Does $E$ admit a cyclic isogeny of degree $p$ over $\mathbf Q$?
3. Does $E(\mathbf Q)$ contain a point of exact order $p$?

The first two questions are equivalent. The third is stronger. If $C$ is a
rational cyclic subgroup of order $p$, Galois can preserve $C$ while acting
nontrivially on every generator. The character describing that action is the
isogeny character. Much of the argument exists to prove that, under
semistability, either this character or its dual is trivial.

The modular curves separate the same three questions. A noncuspidal object
of $Y_0(p)$ records $(E,C)$; an object of $Y_1(p)$ records $(E,P)$ with $P$
a generator. Forgetting $P$ but retaining $\langle P\rangle$ loses exactly
the isogeny character. This is why a theorem about rational torsion belongs
to the oriented curve $X_1(p)$ rather than to $X_0(p)$.

### 1.2 Standing conventions

The symbol $p$ always denotes the coefficient prime and, when an isogeny is
present, its degree. Auxiliary residue characteristics are denoted $q$ or
$r$. We use arithmetic Frobenius. The mod-$p$ cyclotomic character is

$$
\overline\chi_p:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times,
$$

defined by $\sigma(\zeta)=\zeta^{\overline\chi_p(\sigma)}$ on $\mu_p$.
Thus, for $q\ne p$,

$$
\overline\chi_p(\operatorname{Frob}_q)=q\pmod p.
$$

For a finite prime $q$, write $G_q$ and $I_q$ for a decomposition group and
its inertia subgroup. A curve is **semistable** when at every finite prime it
has good or multiplicative reduction. Full rational two-torsion means

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
$$

equivalently that $E[2]$ is the constant finite étale group scheme of rank
four.

All modular points used to construct an isogeny arise from an actual pair
$(E,C)$. We never infer an elliptic curve with level structure from an
arbitrary coarse point without checking descent. All genus-two curves mean
their smooth projective models. Whenever a quintic equation is used, the
point at infinity is included.

### 1.3 The exact boundary of the book

The direct geometric background supplies the modular curves $X_0(p)$ and
$X_1(p)$, their cusps and integral models, the isogeny dictionary, the
pointed Abel maps, and the selected Eisenstein formal-immersion package. The
genus-two background supplies Abel--Jacobi geometry, exact Mumford
arithmetic, the two-descent calculations, and exhaustive Mordell--Weil
sieves for $X_1(13)$ and the mixed-seven curve. The semistable-character
background supplies the local dichotomy and the Frey minimal model.

This book integrates those results into one proof and recalls the decisive
arguments at the point of use. It does not assume the desired Frey
irreducibility in order to prove an exceptional rational-point calculation.
Indeed the arrows go in the opposite direction:

$$
\text{genus-two arithmetic}
\longrightarrow
\text{exceptional torsion exclusions}
\longrightarrow
\text{semistable irreducibility}
\longrightarrow
\text{Frey irreducibility}.
$$

The exponent-five Fermat equation lies on a different branch. Its treatment
uses cyclotomic descent rather than the residual theorem proved here. Chapter
14 records that boundary precisely so that the prime $5$ is neither silently
included nor mistaken for a gap in the $p\ge7$ theorem.

### 1.4 The proof architecture

Assume temporarily that $E[p]$ is reducible. A stable line gives a rational
isogeny and two diagonal characters

$$
\lambda,qquad \mu=\overline\chi_p\lambda^{-1}.
$$

At every $q\ne p$, semistability makes both characters unramified. At $p$,
one is unramified and the other has cyclotomic inertia. Therefore one of
$\lambda,\mu$ is unramified at every finite prime. There is no nontrivial
finite everywhere-unramified character of $G_{\mathbf Q}$, so that character
is trivial. Rational $p$-torsion appears on $E$ or on the quotient curve.

If $E$ has full rational two-torsion and $p$ is odd, the quotient curve has
full rational two-torsion as well. For $p\ge11$, rational $p$-torsion is
impossible by the oriented prime-torsion theorem. For $p=7$, Tate normal form
would give a nondegenerate rational point on the mixed-seven curve, whose
complete rational-point set contains only boundary points. This contradiction
proves the semistable criterion.

Finally, the Frey equation displays full rational two-torsion. Its invariants
prove multiplicative reduction at every bad prime, including after the
essential two-adic coordinate change. The criterion then proves the desired
irreducibility.

## 2. From invariant lines to modular points

The first translation is elementary only after its scheme-theoretic
hypotheses are stated. In characteristic zero, pointwise and scheme-theoretic
torsion agree well enough for descent. At a residue characteristic equal to
$p$, they do not; that distinction will become central in Chapter 4.

### 2.1 Stable lines and finite subgroup schemes

The representation-theoretic hypothesis is useful only after it has been
turned into geometry over the ground field. This section proves that
translation with all descent hypotheses visible.

Because $\operatorname{char}\mathbf Q=0$, the group scheme $E[p]$ is finite
étale of rank $p^2$, and

$$
E[p](\overline{\mathbf Q})\simeq\mathbf F_p^2.
$$

Let $L$ be a one-dimensional $\mathbf F_p$-subspace stable under
$G_{\mathbf Q}$. Finite étale descent gives a unique finite étale subgroup
scheme

$$
C\subset E[p]
$$

whose geometric points are $L$. The quotient of an elliptic curve by a
finite subgroup scheme exists, so there is a separable isogeny

$$
\varphi:E\longrightarrow E'=E/C
$$

defined over $\mathbf Q$ and of degree $p$.

Conversely, if $\varphi:E\to E'$ is a rational isogeny of degree $p$, its
scheme-theoretic kernel is finite étale of rank $p$, and its geometric points
form a $G_{\mathbf Q}$-stable line. We have proved the exact dictionary

$$
\boxed{
E[p]\text{ reducible over }\mathbf F_p
\Longleftrightarrow
E\text{ has a rational cyclic }p\text{-isogeny}.}
\tag{2.1}
$$

The coefficient field matters. A line appearing only after extending
$\mathbf F_p$ does not define an order-$p$ subgroup of the original
$\mathbf F_p$-module.

### 2.2 A subgroup is not a generator

The next distinction controls the rest of the book: rationality of a finite
subgroup is weaker than rationality of any of its nonzero points. A single
character measures the difference.

Choose $0\ne P\in C(\overline{\mathbf Q})$. There is a unique character

$$
\lambda:G_{\mathbf Q}\longrightarrow\mathbf F_p^\times,
\qquad \sigma P=\lambda(\sigma)P.
\tag{2.2}
$$

Changing $P$ to $aP$ does not change $\lambda$, because the scalar group is
abelian. The subgroup $C$ is rational because Galois preserves its set of
points. It has a rational generator precisely when Galois fixes a nonzero
point, hence precisely when

$$
\lambda=1.
\tag{2.3}
$$

This distinction is already visible locally. The subgroup $\mu_p$ of a Tate
curve is defined over the base field, but a generator is rational only when
the field contains a primitive $p$th root of unity.

### 2.3 The complementary character and the dual isogeny

The original kernel character need not become trivial. The dual isogeny
supplies a second chance, and the determinant identifies its character
without another local calculation.

Extend $P$ to a basis of $E[p]$. The representation has the form

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\lambda(\sigma)&b(\sigma)\\
0&\mu(\sigma)
\end{pmatrix}.
\tag{2.4}
$$

The entry $b$ is extension data and need not vanish. The Weil pairing is
perfect, alternating, and Galois equivariant. Therefore

$$
\det\overline\rho_{E,p}=\overline\chi_p,
$$

and taking determinants in (2.4) gives

$$
\mu=\overline\chi_p\lambda^{-1}.
\tag{2.5}
$$

This second character has a geometric realization. Let
$\widehat\varphi:E'\to E$ be the dual isogeny. Its kernel is the Cartier dual
of $C$, and its generic character is precisely $\mu$. Thus

$$
\begin{array}{c|c}
\text{line}&\text{character}\\ \hline
\ker\varphi&\lambda\\
\ker\widehat\varphi&\overline\chi_p\lambda^{-1}.
\end{array}
\tag{2.6}
$$

Consequently triviality of $\lambda$ gives rational $p$-torsion on $E$,
while triviality of $\mu$ gives rational $p$-torsion on $E'$.

### 2.4 $X_0(p)$, $X_1(p)$, and coarse descent

The actual pair $(E,C)$ determines a noncuspidal modular point

$$
x(E,C)\in Y_0(p)(\mathbf Q).
\tag{2.7}
$$

If $C$ has a rational generator $P$, the triple $(E,P)$ determines a point of
$Y_1(p)(\mathbf Q)$. The forgetful map

$$
X_1(p)\longrightarrow X_0(p)
$$

forgets the generator but retains its span. Over a geometric point the
generators form a torsor under $\mathbf F_p^\times$; the Galois action on that
torsor is $\lambda$.

There is no descent ambiguity in (2.7), because the pair exists before the
coarse point is formed. The reverse implication from a rational point of a
coarse curve is subtler. Away from $j=0,1728$, the only geometric
automorphisms are $\pm1$, and both preserve an unoriented cyclic subgroup, so
the subgroup descends after choosing a rational model of the given
$j$-invariant. At $j=0,1728$ the larger stabilizer must be checked directly.
No argument below needs a blanket reverse implication at those two fibers.

### 2.5 Specialization of the modular point

Properness of $X_0(p)$ extends a rational point across every discrete
valuation ring. At a prime $q\ne p$ of good reduction, the pair specializes
to a smooth elliptic curve with a prime-to-$q$ cyclic subgroup. At a
multiplicative prime, the stable generalized elliptic curve is a polygon and
the modular point specializes to a cusp. At the level prime $p$, geometric
point sets are insufficient: the closure of the kernel can be connected,
étale, or part of a nontrivial extension.

This yields a useful conceptual table.

| reduction of $E$ at $q$ | modular specialization | representation-theoretic feature |
|---|---|---|
| good, $q\ne p$ | interior | all of $E[p]$ is unramified |
| multiplicative, $q\ne p$ | cusp | inertia is unipotent; diagonal characters are unramified |
| good, $q=p$ | level-prime interior | the kernel closure is finite flat |
| multiplicative, $q=p$ | level-prime cusp | the Tate extension controls stable lines |

The fact that a modular point is cuspidal does not imply that the residual
representation is ramified. At a multiplicative prime the off-diagonal Tate
class can vanish modulo $p$ while the elliptic curve still degenerates.

## 3. Semistable characters away from the coefficient prime

We now prove the first local half of the global argument. The decisive
observation is modest: away from $p$, semistability makes both diagonal
characters unramified. The full representation may remain ramified through
its extension class.

### 3.1 Good reduction

Let $q\ne p$ and suppose $E$ has good reduction at $q$. The prime-to-$q$
torsion of the good integral model is finite étale. Equivalently, inertia
acts trivially on $E[p]$:

$$
\overline\rho_{E,p}|_{I_q}=1.
\tag{3.1}
$$

Every subrepresentation and quotient of an unramified representation is
unramified. Therefore

$$
\lambda|_{I_q}=1,
\qquad
\mu|_{I_q}=1.
\tag{3.2}
$$

### 3.2 Split multiplicative reduction

Suppose $E/\mathbf Q_q$ has split multiplicative reduction. Tate
uniformization supplies a parameter $u$ with positive valuation and an exact
sequence

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0.
\tag{3.3}
$$

In a basis adapted to this sequence,

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\overline\chi_p(\sigma)&c_u(\sigma)\\
0&1
\end{pmatrix}.
\tag{3.4}
$$

Because $q\ne p$, the cyclotomic character is unramified at $q$. Hence every
inertial matrix is unipotent:

$$
\overline\rho_{E,p}(\tau)=
\begin{pmatrix}1&c_u(\tau)\\0&1\end{pmatrix}
\qquad(\tau\in I_q).
\tag{3.5}
$$

Any one-dimensional subquotient of a unipotent representation has trivial
inertial character. Thus (3.2) holds here as well, regardless of whether the
extension in (3.3) splits.

### 3.3 Nonsplit multiplicative reduction

Nonsplit multiplicative reduction becomes split over the unramified
quadratic extension. Equivalently, the Tate representation is twisted by an
unramified quadratic character $\eta_q$. Its diagonal characters are
$\overline\chi_p\eta_q$ and $\eta_q$. Since $\eta_q$ is trivial on inertia,
the inertial matrices are still unipotent and (3.2) remains true.

This argument explains why the splitness sign matters for Frobenius but not
for ramification. Passing to the unramified splitting field preserves the
inertia group. Passing to an unspecified ramified field would not justify
the same conclusion.

### 3.4 The precise away-from-$p$ conclusion

We have proved the following result.

**Theorem 3.1.** Let $E/\mathbf Q$ be semistable, let $p$ be prime, and
suppose $E[p]$ has a stable line with diagonal characters $\lambda$ and
$\mu$. For every finite prime $q\ne p$,

$$
\lambda|_{I_q}=\mu|_{I_q}=1.
\tag{3.6}
$$

The theorem does not say that $E[p]$ is unramified. At a multiplicative
prime, the off-diagonal entry in (3.5) is governed by the Tate parameter. If
$m=v_q(\Delta_{\min})$, then the residual extension is unramified precisely
when $p\mid m$. Thus diagonal unramifiedness and full unramifiedness are
different conclusions.

## 4. The coefficient-prime dichotomy

At the prime $p$, the character $\overline\chi_p$ is ramified. It is
therefore false that good reduction makes $E[p]$ unramified. The replacement
is integral: good reduction makes $E[p]$ finite flat, and the unramified base
$\mathbf Z_p$ permits only the étale and multiplicative rank-$p$ inertia
types. Multiplicative reduction has a separate Tate-curve proof.

### 4.1 Good reduction and schematic closure

Suppose $E/\mathbf Q_p$ has good reduction. It extends to an elliptic scheme
$\mathcal E/\mathbf Z_p$, and $\mathcal E[p]$ is finite flat of rank $p^2$.
Let $C\subset E[p]$ be the stable generic line. Its schematic closure

$$
\mathcal C\subset\mathcal E[p]
$$

is a finite-flat subgroup of rank $p$. The quotient is represented and gives
an exact sequence

$$
0\longrightarrow\mathcal C\longrightarrow\mathcal E[p]
\longrightarrow\mathcal E[p]/\mathcal C\longrightarrow0.
\tag{4.1}
$$

The fixed ambient group is essential. An abstract generic group can possess
several integral models. The assertion here is that a chosen subgroup has a
unique saturated closure inside the chosen finite-flat torsion group.

The flatness assertion has a short algebraic explanation. On an affine open
of $\mathcal E[p]$, take the quotient of the coordinate algebra defining the
generic subgroup and contract its defining ideal to $\mathbf Z_p$. The
resulting coordinate module is finite and torsion-free over the discrete
valuation ring, hence free. It is therefore flat, and its rank is the rank
of the generic fiber, namely $p$. Translation and inversion preserve the
contracted ideal on the generic fiber; torsion-freeness then shows that they
preserve it integrally. Thus the closure is a subgroup scheme, not merely a
finite subscheme.

The quotient in (4.1) is again finite flat of rank $p$. Its generic fiber is
the complementary one-dimensional subquotient of $E[p]$. Cartier duality
and the Weil pairing identify its character with
$\overline\chi_p\lambda^{-1}$. This integral realization is why the two
characters can be analyzed symmetrically.

### 4.2 Order-$p$ groups over the unramified base

The rank-$p$ finite-flat classification over a mixed-characteristic DVR
assigns an exponent between $0$ and the absolute ramification index. For
$\mathbf Z_p$ that index is one. Thus the generic inertial character of
$\mathcal C$ has only two possibilities:

$$
\lambda|_{I_p}=1
\quad\text{or}\quad
\lambda|_{I_p}=\overline\chi_p|_{I_p}.
\tag{4.2}
$$

At the first endpoint the group is étale up to an unramified twist; at the
second it is of multiplicative type up to an unramified twist. Cartier
duality exchanges the endpoints. Since the Weil pairing identifies the
quotient line with the cyclotomic dual of the kernel line, the two diagonal
restrictions are

$$
(\lambda|_{I_p},\mu|_{I_p})=
\begin{cases}
(1,\overline\chi_p),\\
(\overline\chi_p,1).
\end{cases}
\tag{4.3}
$$

The unramified-base hypothesis is doing real work. Over a ramified extension
with absolute ramification index greater than one, intermediate exponents can
occur. The conclusion (4.2) cannot be transported to such a base without a
new argument.

One can see the endpoint mechanism in the connected--étale sequence. If the
special fiber of $\mathcal C$ is étale, Henselian lifting makes the inertia
action on its geometric generic fiber trivial. If its Cartier dual is
étale, then $\mathcal C$ is of multiplicative type, and the generic fiber
has cyclotomic inertia. The numerical classification says that over an
unramified DVR of absolute ramification index one there is no third generic
inertia character between these endpoints. Applying the same argument to
$\mathcal E[p]/\mathcal C$ and using that the product of the two characters
is cyclotomic forces the ordered alternatives in (4.3).

Unramified twists do not change this conclusion. They can change the value
on Frobenius, so it would be wrong to identify the entire local character
with $1$ or $\overline\chi_p$. The theorem identifies only its restriction
to inertia, which is exactly what the global ramification argument needs.

### 4.3 Multiplicative reduction and the Tate extension

Suppose first that $E/\mathbf Q_p$ has split multiplicative reduction. The
Tate exact sequence is again

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\xrightarrow{\nu}\mathbf Z/p\mathbf Z\longrightarrow0.
\tag{4.4}
$$

Let $C$ be a stable line. If $C=\mu_p$, its inertial character is
$\overline\chi_p$. Otherwise the restriction $\nu|_C$ is nonzero and hence
an isomorphism between one-dimensional $\mathbf F_p$-spaces. For
$\tau\in I_p$, the quotient $\mathbf Z/p\mathbf Z$ is fixed. If $P$ generates
$C$, stability gives $\tau P=a_\tau P$, while applying $\nu$ gives

$$
1=\nu(\tau P)=a_\tau\nu(P)=a_\tau.
$$

Thus the inertial character on $C$ is trivial. Every stable line therefore
has one of the two characters in (4.2).

This argument does not assume that the extension (4.4) splits. If the Tate
parameter has no $p$th root in the local field, the off-diagonal Kummer
class is nonzero. The proof uses only the projection to the constant
quotient. It also shows uniqueness when the extension is nonsplit: any
stable line other than $\mu_p$ would map isomorphically to the quotient and
would split the extension. In the split case there may be several stable
lines, but their inertial characters still fall into the same two types.

If the reduction is nonsplit multiplicative, one twists by the unramified
quadratic splitting character. Its restriction to inertia is trivial, so the
same conclusion holds.

### 4.4 The semistable local theorem

Combining the good and multiplicative cases proves the local result in the
form needed globally.

**Theorem 4.1 (semistable coefficient-prime dichotomy).** Let $p\ge5$, let
$E/\mathbf Q_p$ have good or multiplicative reduction, and suppose $E[p]$
contains a $G_p$-stable line with character $\lambda$. Put
$\mu=\overline\chi_p\lambda^{-1}$. Then

$$
(\lambda|_{I_p},\mu|_{I_p})=
\begin{cases}
(1,\overline\chi_p),\\
(\overline\chi_p,1).
\end{cases}
\tag{4.5}
$$

In particular, exactly one diagonal character is unramified at $p$. The
theorem is a statement about the diagonal characters; the full extension can
still carry nontrivial Tate or finite-flat data.

## 5. The global semistable isogeny theorem

The local calculations now collapse a rational isogeny into rational torsion
on one side. This is the key structural result of the book. Its proof is
short because every place has already been treated with its correct model.

### 5.1 Choosing the unramified diagonal

Let $E/\mathbf Q$ be semistable and suppose it has a rational $p$-isogeny,
where $p\ge5$. Let $\lambda$ and $\mu$ be the two characters in (2.4).
Theorem 3.1 says that both are unramified at every $q\ne p$. Theorem 4.1 says
that one of them is unramified at $p$.

Choose

$$
\theta=
\begin{cases}
\lambda,&\lambda|_{I_p}=1,\\
\mu,&\mu|_{I_p}=1.
\end{cases}
$$

Then $\theta$ is a finite character of $G_{\mathbf Q}$ unramified at every
finite prime.

### 5.2 Everywhere-unramified characters of the rationals

Local calculations have now produced a character with no finite
ramification. The following global lemma is the precise reason that such a
character cannot retain a hidden sign or class-group contribution over
$\mathbf Q$.

**Lemma 5.1.** A finite character of $G_{\mathbf Q}$ unramified at every
finite prime is trivial.

**Proof.** Let $L$ be the fixed field of its kernel. The extension
$L/\mathbf Q$ is finite abelian and unramified at every finite prime. The
conductor--discriminant formula shows that its absolute discriminant has no
prime divisor, hence is $1$. Every number field of degree greater than one
has absolute discriminant greater than $1$ by the Minkowski bound. Thus
$L=\mathbf Q$, and the character is trivial. $\square$

The real place creates no exception. A nontrivial finite extension detected
only by complex conjugation would still have a nontrivial number field as its
fixed field and therefore a finite ramified prime.

### 5.3 Rational torsion on one side

If the selected character is $\lambda$, Lemma 5.1 gives $\lambda=1$ and the
kernel of $\varphi$ has a rational generator. If it is $\mu$, the kernel of
the dual isogeny has a rational generator. We have proved:

**Theorem 5.2 (semistable isogeny theorem).** Let $E/\mathbf Q$ be
semistable and let $p\ge5$ be prime. If

$$
\varphi:E\longrightarrow E'=E/C
$$

is a rational isogeny of degree $p$, then

$$
\boxed{E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.}
\tag{5.1}
$$

The theorem deliberately does not specify which side. The original kernel
can have a nontrivial character even though the dual kernel is rationally
generated.

### 5.4 Why the theorem is genuinely semistable

At an additive prime $q\ne p$, inertia can act on a stable line through a
nontrivial finite character. Then neither diagonal character need be
unramified globally. At a ramified coefficient-prime base, intermediate
finite-flat weights can occur. These are not defects in the proof; they are
the reasons for its hypotheses.

Nor can one replace the characters by their twelfth powers. The relation
$\lambda^{12}=1$ would allow $\lambda$ to have order $2$, $3$, $4$, or $6$.
The Frey argument needs an actual rational generator, so it needs the
character itself to be trivial.

## 6. Prime torsion and the oriented modular curve

Theorem 5.2 changes an isogeny problem into a torsion problem. We now state
and explain the exact torsion theorem needed to finish the large-prime
branch. Its proof uses oriented point-level geometry, not the classification
of rational isogeny degrees.

### 6.1 Why rational torsion belongs to $X_1(p)$

If $P\in E(\mathbf Q)$ has exact order $p$, the pair $(E,P)$ defines a
noncuspidal rational point of $Y_1(p)$. The generator is part of the datum.
Replacing $X_1(p)$ by $X_0(p)$ would remember only $\langle P\rangle$ and
would admit kernels with nontrivial characters.

At a cusp, the point-level structure also has an orientation. On a Tate
polygon the chosen generator can lie in the multiplicative direction or in
the component direction. The forgetful map to $X_0(p)$ has different local
ramification on those branches. A formal-immersion argument must use the
branch for which the smoothing parameter remains a uniformizer.

### 6.2 The formal-immersion mechanism

The formal-immersion argument has four ingredients.

First, properness extends a rational point of $X_1(p)$ over a local ring and
places its reduction either in the interior or at an oriented cusp. Second,
the Weil pairing and point-count bounds constrain the interior alternative.
Third, a selected Eisenstein quotient of the modular Jacobian has finite
rational points and a primitive cotangent lattice. Fourth, a Hecke translate
moves a nonzero Fourier coefficient to the first coefficient, making the
map from the oriented curve to the quotient a formal immersion at the cusp.

Suppose a rational section and the cusp have the same reduction and the same
image in the quotient. Finiteness makes their difference torsion; the
specialization-kernel theorem makes that difference zero; formal immersion
then makes the two sections equal. A noncuspidal rational point cannot equal
the cusp, so the assumed torsion point cannot exist.

Every clause is needed. Finiteness without cotangent injectivity does not
separate sections. Formal immersion without control of the quotient image
does not make the images equal. An unoriented cusp can have the wrong local
parameter.

Here is the local algebra behind the last implication. Let $R$ be a complete
discrete valuation ring, let $x$ be the chosen cusp in the special fiber,
and let

$$
f:X_1(p)_R\longrightarrow A_R
$$

be the map to the selected quotient, normalized by $f(x)=0$. Formal
immersion at $x$ means that the map of completed local rings

$$
\widehat{\mathcal O}_{A,0}\longrightarrow
\widehat{\mathcal O}_{X_1(p),x}
$$

is surjective. Equivalently, the induced map on cotangent spaces is
surjective. If two $R$-sections $s_1,s_2$ reduce to $x$ and have the same
image under $f$, the corresponding maps from the two completed local rings
to $R$ agree on the image of $\widehat{\mathcal O}_{A,0}$. Surjectivity says
they agree everywhere, hence $s_1=s_2$. This is the exact infinitesimal
separation statement used above; no global injectivity of $f$ is asserted.

The cotangent calculation is equally concrete. At an outward cusp the
oriented parameter is $q^{1/p}$, with the generator remembered. A weight-two
cusp form

$$
g(q)=\sum_{n\ge1}a_n(g)q^n
$$

corresponds to the differential $g(q)\,dq/q$. The Hecke identity
$a_1(T_mg)=a_m(g)$ permits a Hecke translate with first coefficient a unit.
Primitivity of the cotangent lattice then says that the pullback of some
integral differential on $A$ has nonzero linear term in the oriented local
parameter. That is precisely cotangent surjectivity for a curve. The word
*primitive* prevents a nonzero differential from becoming divisible by the
residue characteristic and disappearing after reduction.

It remains to explain why the quotient images coincide. The cuspidal
divisor maps to torsion. The modular point arising from a rational torsion
point has the same relevant specialization, and the Eisenstein relations
force the difference of their images into the finite rational subgroup of
$A$. The specialization-kernel theorem for this particular integral
quotient has trivial intersection with that subgroup. Their images are
therefore equal. The completed-local-ring argument then identifies the two
sections, contradicting noncuspidality. This is the full logical chain:

$$
\text{finite quotient}
\Longrightarrow\text{equal quotient images}
\Longrightarrow\text{formal equality at the cusp}
\Longrightarrow\text{equal modular points}.
$$

### 6.3 The uniform range $p\ge17$

For $p\ge11$, reduction modulo $3$ cannot remain in the smooth interior:
the Hasse bound gives

$$
\#\widetilde E(\mathbf F_3)\le
3+1+2\sqrt3<8\le p.
$$

It cannot place a point of order $p$ in the identity torus of a boundary
fiber either, since $\mathbf F_3^\times$ has order two. The oriented modular
point must therefore reduce to an outward cusp.

The corrected index governing the selected Eisenstein quotient is

$$
n_p=\frac{p-1}{\gcd(p-1,12)}.
$$

For every prime $p\ge17$, one has $n_p>1$, so the required nonzero quotient
and primitive cotangent direction exist. The denominator is essential:
$n_{13}=1$, and the uniform quotient vanishes at precisely the exceptional
level which will require genus-two arithmetic.

The established oriented formal-immersion theorem applies uniformly to
prime level $p\ge17$. Its integral statement includes the relevant
specialization kernel; one does not deduce the residue-characteristic-two
case from odd-prime torsion injection on an unrelated quotient. Therefore

$$
E(\mathbf Q)[p]=0
\qquad(p\ge17\text{ prime}).
\tag{6.1}
$$

This conclusion is a point-level theorem. It does not exclude rational
$p$-isogenies whose kernels lack rational generators.

### 6.4 The level-eleven calculation

The uniform bound leaves $11$ and $13$. At level $11$, the compactified
point-level curve has genus one. Choosing a rational cusp as origin turns
the rational-point problem into the elliptic curve

$$
C_{11}:\quad y^2+y=x^3-x^2.
$$

Its five visible rational points are

$$
O,\quad(0,0),\quad(0,-1),\quad(1,0),\quad(1,-1),
$$

and the cusp charts identify all five as outward cusps. The forgetful map to
$X_0(11)$ induces an isogeny of the one-dimensional Jacobians. Eisenstein
finiteness at the corrected index

$$
n_{11}=\frac{10}{\gcd(10,12)}=5
$$

therefore makes $C_{11}(\mathbf Q)$ finite. Direct enumeration gives

$$
\#C_{11}(\mathbf F_2)=\#C_{11}(\mathbf F_3)=5.
$$

Good-reduction injection bounds each primary part of the rational torsion,
so the rational group has order dividing five. The five displayed points
force equality. Every rational point is therefore a cusp, and consequently

$$
E(\mathbf Q)[11]=0
\tag{6.2}
$$

for every elliptic curve $E/\mathbf Q$.

The role of this separate calculation is logical, not cosmetic. The prime
$11$ is below the uniform formal-immersion range and cannot be inserted into
it by changing an inequality.

### 6.5 The level-thirteen problem

The curve $X_1(13)$ has genus

$$
g(X_1(13))=\frac{(13-5)(13-7)}{24}=2.
$$

The genus formula follows because the image of $\Gamma_1(p)$ in
$\operatorname{PSL}_2(\mathbf Z)$ is torsion-free for $p\ge5$, has index
$(p^2-1)/2$, and has $p-1$ geometric cusps. Thus level $13$ is the first
exception which genuinely requires genus-two arithmetic. The next chapter
gives its complete rational-point proof.

## 7. The exact rational points of $X_1(13)$

The purpose of this chapter is not to repeat all of two-descent. It is to
show exactly how the certified Jacobian and one finite reduction imply the
rational-point theorem. Every numerical statement used here is part of the
completed certificates of the preceding genus-two volumes.

### 7.1 The genus-two model and its cusps

To turn the modular problem into exact arithmetic, we need a smooth equation,
the correct two points at infinity, and a fixed Abel base point. Each choice
affects the later reduction labels, so the normalization is established
before any Jacobian calculation.

A smooth affine model is

$$
y^2+(x^3+x^2+1)y=x^2+x.
\tag{7.1}
$$

Completing the square with

$$
z=2y+x^3+x^2+1
$$

gives

$$
C_{13}:z^2=F(x),
\tag{7.2}
$$

where

$$
F(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1,
\qquad
\operatorname{disc}(F)=-2^{12}13^2.
\tag{7.3}
$$

The monic sextic has two rational points $\infty^+$ and $\infty^-$ above
infinity, distinguished by $z/x^3\to1$ and $-1$. The six evident rational
points in the coordinates of (7.1) are

$$
\mathcal C_{13}=
\{\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)\}.
\tag{7.4}
$$

They are the six rational cusps. Direct substitution checks the four affine
points, and the two leading branches check the points at infinity.

Choose $\infty^+$ as Abel base point and put

$$
j(P)=[P-\infty^+],
\qquad
T=[\infty^--\infty^+].
\tag{7.5}
$$

Because this is an even-degree model, hyperelliptic conjugation satisfies

$$
j(P)+j(\iota P)=T,
\tag{7.6}
$$

not $j(\iota P)=-j(P)$. The translation by $T$ is an important
normalization in the finite sieve.

### 7.2 The complete Mordell--Weil group

The Abel map places rational curve points inside the rational Jacobian.
Consequently the point problem becomes finite only after both the rank and
the entire torsion subgroup have been determined; a finite-index subgroup
would leave uncontrolled cosets.

The true sextic two-descent, including the scalar quotient and the
true-to-fake lifting obstruction, proves rank zero and no rational
two-torsion. Good reductions at $3$ and $5$ give Jacobian groups of order
$19$. The nonzero class $T$ therefore has exact order $19$, and the same
reduction bound excludes every additional rational point of the Jacobian.
Thus

$$
\boxed{J_{13}(\mathbf Q)=\langle T\rangle
\simeq\mathbf Z/19\mathbf Z.}
\tag{7.7}
$$

Let us spell out why each word matters. A fake sextic Selmer dimension would
not prove rank zero. A point count of order $19$ would only give an upper
bound on torsion until a nonzero rational class was exhibited. The class
$T$ supplies that lower bound, and two-descent supplies the absence of a free
part.

The descent certificate can be recorded without suppressing the even-degree
issue. Put

$$
L_{13}=\mathbf Q[\theta]/(F(\theta)),
\qquad S=\{2,13,\infty\}.
$$

The polynomial $F$ is irreducible, has signature $(0,3)$, and satisfies

$$
F(X)\equiv(X^3+X^2+1)^2\pmod2,
$$

$$
F(X)\equiv(X-3)^3(X^3+11X^2+8X+12)\pmod{13}.
$$

An integral-basis and ideal-relation calculation gives the following exact
dimension ledger:

$$
\begin{array}{c|c}
\text{space}&\mathbf F_2\text{-dimension}\\ \hline
L_{13}(S,2)&6\\
\text{after scalar squareclasses}&3\\
\text{after the norm-compatible-pair relation}&2\\
\text{after the }2\text{-adic image}&1\\
\text{after the }13\text{-adic image}&0.
\end{array}
\tag{7.8}
$$

With a basis $b_1,b_2$ of the two-dimensional global candidate space, the
two surviving local functionals have row-reduced matrix

$$
\begin{array}{c|cc}
&b_1&b_2\\ \hline
\mathbf Q_2&1&0\\
\mathbf Q_{13}&0&1.
\end{array}
\tag{7.9}
$$

Thus the fake local kernel is zero. For a sextic this is not yet enough:
the true-to-fake connecting sequence has the infinity-difference
alternative in its kernel. Using $\infty^+$ as the rational degree-one base
divisor, its norm-compatible pair fails the $13$-adic lifting condition.
Consequently the true Selmer group is zero. This proves rank zero, while the
irreducibility of $F$ rules out a nontrivial Galois-stable even set of branch
points and hence rules out rational two-torsion.

The independent torsion certificate is

$$
\begin{array}{c|cc|c}
r&\#C_{13}(\mathbf F_r)&\#C_{13}(\mathbf F_{r^2})
&\#J_{13}(\mathbf F_r)\\ \hline
3&6&8&19\\
5&6&12&19.
\end{array}
\tag{7.10}
$$

For a genus-two curve,

$$
\#J(\mathbf F_r)
=\frac{\#C(\mathbf F_r)^2+\#C(\mathbf F_{r^2})}{2}-r.
\tag{7.11}
$$

The class $T$ is nonzero: otherwise a function with divisor
$\infty^--\infty^+$ would have degree one, impossible on a genus-two curve.
Reduction at either good prime shows its order divides $19$, so its order is
exactly $19$. Since the rank is zero and all rational torsion injects into
both finite Jacobians, (7.7) follows.

### 7.3 A terminal reduction at seventeen

Once the rational Jacobian is the cyclic group of order $19$, a good prime
different from $19$ can see every global class injectively. The prime $17$
is chosen because its Abel image meets that cyclic subgroup in exactly six
classes, making one reduction terminal.

The prime $17$ is good by (7.3) and is different from $19$, so reduction is
injective on the whole rational Jacobian. Modulo $17$, the root $x=1$ of
$F$ can be sent to infinity by

$$
X=\frac1{x-1},\qquad Y=zX^3,\qquad w=Y/5.
$$

Since $5^2=8$ in $\mathbf F_{17}$, the resulting pointed quintic is

$$
w^2=X^5+13X^4+10X^3+16X^2+X+15.
\tag{7.12}
$$

This model permits unique reduced-pair arithmetic. The old points
$\infty^+,\infty^-$ become $(0,7),(0,10)$, and their difference is

$$
\bar T=[X^2,10+6X].
$$

Repeated exact addition produces nineteen distinct normalized pairs and
$19\bar T=0$. Thus the calculation enumerates the whole reduction of the
rational group, not merely a sample of it.

The complete cyclic-subgroup certificate is the following table; all
coefficients are read modulo $17$:

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
\tag{7.13}
$$

For each row, $u_n$ is monic, $\deg v_n<\deg u_n\le2$, and
$u_n\mid g-v_n^2$, where $g$ is the quintic in (7.12). Cantor addition by
$[X^2,10+6X]$ takes row $n$ to row $n+1$; the last row returns to the
identity. Unique reduced representation proves that the nineteen rows are
distinct.

For completeness, direct evaluation of the seventeen possible $x$-values
gives the entire special fiber in the original $(x,z)$ coordinates:

$$
\begin{aligned}
C_{13}(\mathbf F_{17})=\{&\infty^+,\infty^-,(0,\pm1),(1,0),
(6,\pm6),(8,0),\\
&(12,\pm2),(13,\pm8),(15,0),(16,\pm1)\}.
\end{aligned}
\tag{7.14}
$$

Transforming these fifteen points to (7.12), taking their degree-one Abel
classes, and comparing their unique reduced pairs with the nineteen
multiples of $\bar T$ gives

$$
j_{17}(C_{13}(\mathbf F_{17}))\cap\langle\bar T\rangle
=\{0,1,4,6,14,16\}\bar T.
\tag{7.15}
$$

The six known cusps have the corresponding global classes

$$
\begin{array}{c|c}
P&j(P)\\ \hline
\infty^+&0\\
\infty^-&T\\
(0,0)&6T\\
(0,-1)&14T\\
(-1,0)&16T\\
(-1,-1)&4T.
\end{array}
\tag{7.16}
$$

These labels are certified by reduction, because reduction is injective on
$19$-torsion. They are also compatible with (7.6): the involution pairs the
coefficients $0$ and $1$, $6$ and $14$, and $16$ and $4$, each pair summing
to $1$ modulo $19$. Every special point not displayed in (7.16) has a
normalized pair different from all nineteen multiples. Thus a dash in the
comparison table is an exact nonmembership certificate, not a failure to
find a match.

### 7.4 Exhaustion and uniqueness

The finite calculation becomes a rational-point theorem only after every
surviving class is matched with a known point and Abel injectivity proves
uniqueness. This section supplies that terminal step.

Let $P\in C_{13}(\mathbf Q)$. Equation (7.7) gives $j(P)=nT$ for a unique
$n\in\mathbf Z/19\mathbf Z$. The specialization square for the Abel map and
(7.15) force

$$
n\in\{0,1,4,6,14,16\}.
$$

For each value, (7.16) supplies a known cusp $Q$ with $j(Q)=nT$. The Abel map
of a positive-genus curve is injective on geometric points: if
$[P-\infty^+]=[Q-\infty^+]$, then $P-Q$ is principal; a nonconstant function
with divisor $P-Q$ would have degree one and would make the genus-two curve
isomorphic to $\mathbf P^1$. Therefore $P=Q$.

We have proved

$$
\boxed{X_1(13)(\mathbf Q)=\mathcal C_{13}.}
\tag{7.17}
$$

The argument is terminal because the rational Jacobian is finite and the
chosen modulus annihilates it. No unsieved coset, height region, or residue
disk remains.

### 7.5 The prime-torsion theorem

Combining the uniform formal-immersion range, the level-eleven calculation,
and (7.17) gives the exact theorem used later.

**Theorem 7.1 (rational prime torsion).** If $E/\mathbf Q$ is an elliptic
curve and $p\ge11$ is prime, then

$$
E(\mathbf Q)[p]=0.
\tag{7.18}
$$

Indeed a rational point of exact order $p$ would define a noncuspidal point
of $X_1(p)(\mathbf Q)$. The three branches above show that none exists. The
theorem is independent of any classification of rational $X_0(p)$ points.

## 8. Odd isogenies and full rational two-torsion

The prime-torsion theorem eliminates $p\ge11$ once Theorem 5.2 produces a
rational generator. The prime $7$ remains because elliptic curves over
$\mathbf Q$ can have rational seven-torsion. The Frey curve supplies an
additional invariant: its entire two-torsion is rational. We first prove
that this invariant survives passage across an odd isogeny.

### 8.1 Preservation of two-torsion as a group scheme

The rational $p$-torsion produced by Theorem 5.2 may occur on the quotient
curve rather than the original one. We therefore need full two-torsion to
cross an odd isogeny without loss.

Let $\varphi:A\to B$ be an isogeny of abelian varieties of odd degree $d$.
There is an isogeny $\varphi':B\to A$ satisfying

$$
\varphi'\varphi=[d]_A,
\qquad
\varphi\varphi'=[d]_B.
\tag{8.1}
$$

On a group scheme killed by $2$, multiplication by $d$ is multiplication by
$1$, because $d\equiv1\pmod2$. Restricting (8.1) to the two-torsion kernels
therefore gives inverse maps

$$
\varphi[2]:A[2]\xrightarrow{\sim}B[2],
\qquad
\varphi'[2]:B[2]\xrightarrow{\sim}A[2].
\tag{8.2}
$$

This is a group-scheme proof. It remains valid under base change and does not
rely on counting geometric points. Over $\mathbf Q$, it is Galois equivariant,
so

$$
A[2](\mathbf Q)\simeq(\mathbf Z/2)^2
\Longleftrightarrow
B[2](\mathbf Q)\simeq(\mathbf Z/2)^2.
\tag{8.3}
$$

### 8.2 The mixed torsion forced by a rational generator

Let $E/\mathbf Q$ have full rational two-torsion and let
$P\in E(\mathbf Q)$ have odd prime order $p$. The groups $E[2](\mathbf Q)$
and $\langle P\rangle$ intersect trivially, so

$$
E[2](\mathbf Q)\oplus\langle P\rangle
\simeq(\mathbf Z/2)^2\oplus\mathbf Z/p.
$$

The Chinese remainder theorem rewrites this as

$$
\mathbf Z/2\mathbf Z\oplus\mathbf Z/2p\mathbf Z.
\tag{8.4}
$$

Thus a rationally generated kernel on either side of an odd isogeny in a
full-two isogeny class forces a mixed subgroup of the form (8.4).

### 8.3 Why seven is the remaining prime

If $p\ge11$, Theorem 7.1 already excludes the rational point $P$. At $p=7$,
rational seven-torsion exists in general, so full two-torsion must be used.
The hypothetical curve would contain

$$
\mathbf Z/2\mathbf Z\oplus\mathbf Z/14\mathbf Z.
\tag{8.5}
$$

Tate normal form converts this configuration into a rational point on a
specific genus-two curve. The conversion is one-way: the mixed torsion
configuration implies a point on the curve. We do not need every point of the
curve to reconstruct such a configuration.

## 9. Tate normal form and the mixed-seven curve

Tate normal form is designed to make repeated addition of one marked point
simple. Its coefficients become parameters on $X_1(p)$. Full rational
two-torsion then imposes a square-discriminant condition, which is the bridge
to genus two.

### 9.1 Normalizing a point of odd order

Let $F$ be a field of characteristic zero and let $P\in E(F)$ have order at
least four. A change of Weierstrass coordinates puts the pair $(E,P)$ in the
form

$$
E(b,c):
y^2+(1-c)xy-by=x^3-bx^2,
\qquad P=(0,0),
\tag{9.1}
$$

with $b\ne0$ and nonzero discriminant. The normal form is obtained by moving
$P$ to the origin, arranging the tangent at $P$ to be $y=0$, and using the
remaining scaling to normalize the coefficient of $y$. Each step is
reversible when the discriminant and $b$ are nonzero.

The low multiples illustrate its purpose. The tangent $y=0$ meets the cubic
at $x=0$ twice and at $x=b$, so the group law gives

$$
2P=(b,bc).
$$

For reference, addition on a generalized Weierstrass equation uses, for two
distinct points,

$$
\lambda=\frac{y_2-y_1}{x_2-x_1},
\qquad
\nu=\frac{y_1x_2-y_2x_1}{x_2-x_1},
$$

$$
x_3=\lambda^2+a_1\lambda-a_2-x_1-x_2,
\qquad
y_3=-(\lambda+a_1)x_3-\nu-a_3.
\tag{9.2}
$$

The tangent case is obtained by implicit differentiation. Applying these
formulas successively on the open set $bc\ne0$ gives

$$
2P=(b,bc),\qquad
3P=(c,b-c),\qquad
4P=\left(
\frac{b(b-c)}{c^2},
\frac{b^2(c^2+c-b)}{c^3}
\right).
\tag{9.3}
$$

Direct substitution in the curve equation checks each point, and one more
application of (9.2) checks the group-law recurrence. Thus an order
condition is reduced to equality of explicit rational functions in $b,c$;
the vanishing denominators record boundary or lower-order cases and must be
removed before cancellation.

### 9.2 The order-seven locus

For exact order seven, the addition formulas reduce to the one-parameter
specialization

$$
b=t^3-t^2,
\qquad
c=t^2-t.
\tag{9.4}
$$

The excluded values $t=0,1$ make $b=0$ and hence make the normal form
degenerate. Conversely, away from the zeros of the discriminant, (9.4)
gives the point-level order-seven locus. For our exclusion only the forward
direction is required: a rational point of order seven yields a rational
parameter $t$ satisfying (9.4).

To see the parameter rather than merely quote it, impose $3P=-4P$ using
(9.3). On the nondegenerate locus, equality of the $x$-coordinates first
produces the ratio $t=b/c$ after cancelling the factors belonging to
$b=0$, $c=0$, and the discriminant. Substituting that ratio back into the
$y$-coordinate equality yields

$$
c=t^2-t,\qquad b=tc=t^3-t^2.
$$

Conversely, substitution into the recurrence makes $3P=-4P$, hence
$7P=0$. The removed factors are precisely the singular or lower-order
possibilities, so a nonsingular marked point of exact order seven lies on
this open one-parameter family.

### 9.3 The cubic of two-torsion coordinates

On a generalized Weierstrass equation, a point is fixed by negation exactly
when

$$
2y+a_1x+a_3=0.
$$

Eliminating $y$ from this relation and (9.1) gives the cubic whose roots are
the $x$-coordinates of the three nonzero two-torsion points:

$$
F_{b,c}(X)=
4X^3+\bigl((1-c)^2-4b\bigr)X^2
+2b(c-1)X+b^2.
\tag{9.5}
$$

If all two-torsion is rational, this cubic splits over $\mathbf Q$. The
discriminant of a split cubic is a square: it is the square of the product of
the three pairwise root differences, multiplied by the square of the leading
coefficient. Substituting (9.4) into the discriminant of (9.5) gives

$$
\operatorname{disc}F_{t^3-t^2,t^2-t}
=16t^7(t-1)^7(t^3-8t^2+5t+1).
\tag{9.6}
$$

This identity follows by the standard cubic discriminant formula and direct
collection of powers of $t$. Its direction of use is important: splitting
implies square discriminant. A square discriminant alone would only place the
Galois group in the alternating group; it would not force the cubic to
split.

### 9.4 The necessary genus-two condition

Assume $t\ne0,1$. If the right side of (9.6) is a square, divide its square
root by $4t^3(t-1)^3$. The result is a rational number $z$ satisfying

$$
C_7:\quad
z^2=t(t-1)(t^3-8t^2+5t+1).
\tag{9.7}
$$

The quintic on the right is monic and squarefree, with discriminant $7^4$.
Its smooth projective model is therefore a genus-two curve with one rational
Weierstrass point $\infty$ at infinity. The values $t=0,1$ give the rational
branch points $(0,0),(1,0)$, while $\infty$ is the boundary value of the
parameter. Thus a nondegenerate elliptic curve with full rational two-torsion
and a rational point of order seven would produce a rational point of $C_7$
outside

$$
\{\infty,(0,0),(1,0)\}.
\tag{9.8}
$$

The next chapter proves that no such point exists.

## 10. The exact arithmetic of the mixed-seven curve

This is the second exceptional genus-two calculation required by the
catalog. The proof has two layers. Two-descent and good reductions determine
the entire rational Jacobian. Unique reduced representatives then test all
of its classes for membership in the Abel image.

### 10.1 The pointed curve and visible classes

The rational branch points and one nontrivial divisor class give a subgroup
of order twelve. They provide the lower bound which will later meet the
descent and reduction upper bounds.

Expand the polynomial in (9.7):

$$
f(t)=t^5-9t^4+13t^3-4t^2-t.
\tag{10.1}
$$

Use $\infty$ as Abel base point. In reduced Mumford notation define

$$
T_0=[t,0],
\qquad
T_1=[t-1,0],
\qquad
A=[t^2-t+1,1-3t].
\tag{10.2}
$$

The first two are the nonzero classes of the rational Weierstrass points
relative to $\infty$, so they have order two. They are nonzero and distinct
by injectivity of the Abel map. For $A$, exact division gives

$$
f-(1-3t)^2
=(t^2-t+1)(t^3-8t^2+4t-1),
\tag{10.3}
$$

so the pair is valid. Cantor reduction gives

$$
2A=[t^2-t+1,3t-1]=-A,
\tag{10.4}
$$

hence $A$ has exact order three.

### 10.2 The complete Jacobian

Testing the Abel image requires every rational Jacobian class. We therefore
prove rank zero by two-descent and prove the exact torsion order by two
independent good reductions before performing the twelve-class test.

The odd-degree $x-T$ descent algebra factors as

$$
L=\mathbf Q\times\mathbf Q\times K,
\qquad
K=\mathbf Q(\theta),
\quad
\theta^3-8\theta^2+5\theta+1=0.
\tag{10.5}
$$

To prove that the displayed classes exhaust the rational Jacobian, we first
make the two-descent finite. The cubic field in (10.5) is the real cubic
subfield of the seventh cyclotomic field. If
$\alpha^3+\alpha^2-2\alpha-1=0$, then

$$
\theta=-1-\alpha+2\alpha^2,
\qquad
[\mathcal O_K:\mathbf Z[\theta]]=7,
\qquad
\operatorname{disc}(K)=49.
\tag{10.6}
$$

The Minkowski bound is $14/9<2$, so $K$ has class number one. The elements
$\alpha,\alpha+1$ are fundamental units, $2$ is inert, and the unique prime
above $7$ is generated by $2-\alpha$. In particular,

$$
N(\alpha)=1,\qquad N(\alpha+1)=-1,\qquad N(2-\alpha)=7.
\tag{10.7}
$$

For a reduced divisor $[u,v]$ disjoint from the branch points, the
odd-degree $x-T$ map is

$$
\delta([u,v])=
\bigl((-1)^{\deg u}u(0),(-1)^{\deg u}u(1),
(-1)^{\deg u}u(\theta)\bigr).
\tag{10.8}
$$

In the product-norm kernel of the squareclass group unramified outside
$\{2,7,\infty\}$, use the ordered basis

$$
\begin{aligned}
e_0&=(-1,-1,-\theta),&e_1&=(1,-1,1-\theta),\\
h_1&=(-1,1,-1),&h_2&=(1,-1,-1),\\
h_3&=(2,1,2),&h_4&=(1,2,2),\\
h_5&=(7,1,2-\alpha),&h_6&=(1,7,2-\alpha).
\end{aligned}
\tag{10.9}
$$

Valuation parity at the rational factors, the inert prime above $2$, and
the ramified prime above $7$, together with the independent unit
squareclasses, proves independence and spanning. The first two vectors are
exactly $\delta(T_0),\delta(T_1)$. The complete local obstruction matrix is

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
\tag{10.10}
$$

At $2$, completeness follows from

$$
\dim_{\mathbf F_2}J_7(\mathbf Q_2)/2J_7(\mathbf Q_2)
=2+\dim_{\mathbf F_2}J_7(\mathbf Q_2)[2]=4;
$$

the visible two-torsion and the points with $t=-4,13$ give four independent
local images. At $7$, the local quotient is two-dimensional and already
generated by $T_0,T_1$. The successive dimensions are therefore

$$
8\longrightarrow6\longrightarrow2\longrightarrow2,
$$

and the final kernel of (10.10) is exactly $\langle e_0,e_1\rangle$. The
Kummer exact sequence proves

$$
\operatorname{Sel}_2(J_7/\mathbf Q)
=\langle\delta(T_0),\delta(T_1)\rangle,
\qquad \operatorname{rank}J_7(\mathbf Q)=0.
\tag{10.11}
$$

It remains only to identify the torsion. The exact finite-field counts are

$$
\begin{array}{c|cc|c}
q&\#C_7(\mathbf F_q)&\#C_7(\mathbf F_{q^2})
&\#J_7(\mathbf F_q)\\ \hline
3&5&5&12\\
5&9&25&48.
\end{array}
\tag{10.12}
$$

For genus two the last column follows from

$$
\#J(\mathbf F_q)
=\frac{\#C(\mathbf F_q)^2+\#C(\mathbf F_{q^2})}{2}-q.
\tag{10.13}
$$

Rational torsion injects prime by prime into these good reductions. Therefore
its order divides $\gcd(12,48)=12$. The displayed subgroup generated by
$A,T_0,T_1$ has order $3\cdot2\cdot2=12$. Together with rank zero this proves

$$
\boxed{
J_7(\mathbf Q)=
\langle A\rangle\oplus\langle T_0\rangle\oplus\langle T_1\rangle
\simeq\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2.}
\tag{10.14}
$$

This is an equality, not a finite-index statement. Hence no additional
Mordell--Weil coset can contain an unknown curve point.

### 10.3 All twelve reduced classes

The group decomposition is abstract; curve membership is geometric. Unique
reduced Mumford representatives turn the abstract twelve elements into an
exhaustive, directly checkable list.

Write each group element as $aA+bT_0+cT_1$ with
$a\in\{0,1,2\}$ and $b,c\in\{0,1\}$. Exact addition gives the complete table

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
\tag{10.15}
$$

Every row is verified by $u\mid f-v^2$, monicity, and
$\deg v<\deg u\le2$. The relations in (10.14) generate the rows, and unique
reduced representation proves that they are distinct and exhaustive.

### 10.4 The Abel-image test

For a pointed monic quintic, the Abel image based at infinity consists
exactly of the identity and the reduced pairs with $\deg u=1$. One direction
is immediate:

$$
j_\infty(a,b)=[t-a,b],
\qquad
j_\infty(\infty)=[1,0].
$$

Conversely, if $[t-a,b]$ is a valid pair, divisibility by $t-a$ gives
$b^2=f(a)$, so it comes from the curve point $(a,b)$.

Inspection of (10.15) leaves exactly

$$
[1,0],\qquad[t,0],\qquad[t-1,0].
\tag{10.16}
$$

These are the Abel classes of $\infty,(0,0),(1,0)$. Abel injectivity now
gives

$$
\boxed{C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.}
\tag{10.17}
$$

### 10.5 The mixed-seven exclusion

All three points in (10.17) are boundary or degenerate parameters for Tate
normal form: $t=0$ and $t=1$ give $b=0$, while $\infty$ is the compactifying
cusp. But Chapter 9 showed that a full-two curve with rational seven-torsion
would give a nondegenerate rational point of $C_7$. Therefore:

**Theorem 10.1 (mixed-seven exclusion).** No elliptic curve over $\mathbf Q$
contains a subgroup

$$
\mathbf Z/2\mathbf Z\oplus\mathbf Z/14\mathbf Z.
\tag{10.18}
$$

Equivalently, an elliptic curve over $\mathbf Q$ with full rational
two-torsion has no rational point of order seven. Notice that the proof used
square discriminant only as a necessary condition and then exhausted every
rational point of the necessary curve.

## 11. The semistable full-two irreducibility criterion

We can now assemble the local character theorem, prime torsion, preservation
of two-torsion, and the mixed-seven exclusion. The result is tailored to the
Frey curve but applies to every semistable full-two curve over $\mathbf Q$.

### 11.1 Statement and motivation

**Theorem 11.1 (semistable full-two irreducibility).** Let $E/\mathbf Q$ be
semistable and suppose

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
$$

For every prime $p\ge7$, the representation

$$
\overline\rho_{E,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
$$

is irreducible over $\mathbf F_p$.

The hypotheses have separate roles. Semistability controls the two diagonal
characters. Full two-torsion eliminates the exceptional rational torsion at
$p=7$. Neither hypothesis is needed merely to define the representation.

### 11.2 Proof across the isogeny

The proof follows the possible location of the rational generator rather
than assuming it remains on the original curve. Preservation of
two-torsion makes the two sides symmetric.

**Proof.** Suppose $E[p]$ is reducible. By (2.1), there is a rational
degree-$p$ isogeny

$$
\varphi:E\longrightarrow E'=E/C.
$$

The semistable isogeny theorem gives

$$
E(\mathbf Q)[p]\ne0
\quad\text{or}\quad
E'(\mathbf Q)[p]\ne0.
\tag{11.1}
$$

Because $p$ is odd, (8.2) gives a Galois-equivariant isomorphism
$E[2]\simeq E'[2]$. Thus both sides have full rational two-torsion.

If $p\ge11$, (11.1) contradicts Theorem 7.1. If $p=7$, the side carrying
the rational point has full rational two-torsion, contradicting Theorem 10.1.
These cases exhaust all primes $p\ge7$. Hence $E[p]$ is irreducible.
$\square$

The proof never consults a list of rational prime-isogeny degrees. It uses
the stronger consequence of semistability: rational torsion on one side of
the isogeny.

### 11.3 Hypotheses and exceptions

Without semistability, an additive prime can ramify both diagonal characters,
so the global unramified-character argument fails. Without full rational
two-torsion, curves with rational seven-torsion provide counterexamples to
the small-prime step. The theorem asserts irreducibility over $\mathbf F_p$;
it does not classify the image inside $\operatorname{GL}_2(\mathbf F_p)$ and
does not assert that the representation remains irreducible after every
coefficient extension.

The lower endpoint $p=7$ is exact for the theorem stated here. The exponent
$5$ belongs to the separate cyclotomic route discussed in Chapter 14. We do
not enlarge the theorem by importing a mixed-five calculation that is not
needed for the catalog endpoint.

## 12. The Frey curve and its normalization

The general criterion applies only after two properties of the Frey curve
have been proved: full rational two-torsion and semistability. The first is
visible in the factored equation. The second requires a minimal-model
calculation, especially at $2$.

### 12.1 Primitive triples and parity

The local model at $2$ depends on which entry of the primitive triple is
even and on one odd congruence modulo $4$. Fixing that normalization now
prevents an ambiguous or nonintegral change of variables later.

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

Exactly one of $a,b,c$ is even. If two were even, primitivity would fail; if
all were odd, the parity of (12.1) would fail. Rewriting the signed
three-term equation and changing all signs if necessary, we may arrange

$$
a\text{ even},
\qquad b,c\text{ odd},
\qquad b\equiv1\pmod4.
\tag{12.2}
$$

The last normalization is possible because one of the two odd terms can be
chosen with the required sign modulo $4$. Since $p$ is odd, taking the
$p$th power preserves these congruences.

Put

$$
A=a^p,
\qquad B=b^p,
\qquad C=c^p=A+B.
\tag{12.3}
$$

### 12.2 The curve, its two-torsion, and its invariants

The factored Frey equation is chosen because it simultaneously displays the
three rational two-torsion points and makes every discriminant factor a root
difference. These are exactly the inputs to the irreducibility criterion and
the semistability calculation.

Define the Frey curve

$$
E=E_{a,b,p}:\quad
y^2=x(x-A)(x+B).
\tag{12.4}
$$

The three roots $0,A,-B$ are distinct because $ABC\ne0$. Hence the curve is
nonsingular. Its three nonzero two-torsion points are

$$
(0,0),\qquad(A,0),\qquad(-B,0),
\tag{12.5}
$$

so $E[2](\mathbf Q)\simeq(\mathbf Z/2)^2$.

Expanding (12.4) gives

$$
y^2=x^3+(B-A)x^2-ABx.
$$

Thus $a_1=a_3=a_6=0$, $a_2=B-A$, and $a_4=-AB$. The intermediate
quantities are

$$
b_2=4(B-A),\qquad b_4=-2AB,
\qquad b_6=0,\qquad b_8=-A^2B^2.
$$

Substitution in

$$
c_4=b_2^2-24b_4,
\qquad
c_6=-b_2^3+36b_2b_4-216b_6,
$$

and in the Weierstrass discriminant formula yields

$$
\begin{aligned}
c_4&=16(A^2+AB+B^2),\\
c_6&=-32(B-A)(2A^2+5AB+2B^2),\\
\Delta&=16A^2B^2C^2=2^4(abc)^{2p},\\
j&=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.
\end{aligned}
\tag{12.6}
$$

The discriminant formula is also the general root-difference formula:
$16$ times the square of

$$
(A-0)(0-(-B))(A-(-B))=ABC.
$$

This second derivation is a useful normalization check: it confirms the
sign-independent square $A^2B^2C^2$ and the factor $2^4$. The identity
$C=A+B$ similarly turns

$$
(B-A)^2+3AB
$$

into $A^2+AB+B^2$, explaining the symmetric expression in $c_4$.

### 12.3 Odd-prime minimal models

Let $q$ be odd. Primitivity implies that $q$ divides at most one of
$a,b,c$. If $q\nmid abc$, then $\Delta$ is a $q$-adic unit and the curve has
good reduction.

Suppose $q\mid a$. Then $B,C$ are units and

$$
A^2+AB+B^2\equiv B^2\not\equiv0\pmod q.
$$

Thus $c_4$ is a unit. The displayed integral equation is minimal, since a
nontrivial scaling improvement would force positive valuation of $c_4$.
Because $\Delta$ has positive valuation, the reduction is multiplicative,
and

$$
v_q(\Delta_{\min})=2p\,v_q(a).
$$

The same argument using the appropriate root difference gives

$$
v_q(\Delta_{\min})=
\begin{cases}
2p\,v_q(a),&q\mid a,\\
2p\,v_q(b),&q\mid b,\\
2p\,v_q(c),&q\mid c.
\end{cases}
\tag{12.7}
$$

Hence every odd bad prime is multiplicative.

Let us justify the cases $q\mid b$ and $q\mid c$ explicitly. If $q\mid b$,
then $A,C$ are units and
$A^2+AB+B^2\equiv A^2\not\equiv0\pmod q$. If $q\mid c$, then
$B\equiv-A\pmod q$, so

$$
A^2+AB+B^2\equiv A^2-A^2+A^2=A^2\not\equiv0\pmod q.
$$

In all three cases $v_q(c_4)=0<v_q(\Delta)$. The standard reduction
criterion then gives multiplicative rather than additive reduction. Since an
integral change with scaling factor divisible by $q$ would lower
$v_q(c_4)$ by a positive multiple of four, which is impossible from zero,
the equation is minimal.

### 12.4 The minimal model at two

The factored equation is not minimal at $2$. From (12.2),

$$
v_2(A)=p\,v_2(a)\ge7,
\qquad
B-A\equiv1\pmod4.
\tag{12.8}
$$

Make the change

$$
x=4x',
\qquad
y=8y'+4x'.
\tag{12.9}
$$

Substitution in (12.4) and division by $64$ give

$$
y'^2+x'y'
=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'.
\tag{12.10}
$$

Both coefficients are integral: the first by the congruence in (12.8), the
second because $v_2(A)\ge7$. The scaling factor is $2$, so $c_4$ and
$\Delta$ are divided by $2^4$ and $2^{12}$ respectively. Hence

$$
c_{4,\min}=A^2+AB+B^2,
\qquad
\Delta_{\min}=2^{-8}A^2B^2C^2.
\tag{12.11}
$$

Since $A$ is even and $B$ is odd, $c_{4,\min}$ is odd. Therefore (12.10) is
minimal and has multiplicative reduction. Its discriminant exponent is

$$
v_2(\Delta_{\min})=2p\,v_2(a)-8>0.
\tag{12.12}
$$

The subtraction of eight is indispensable. The raw exponent from (12.6)
belongs to a nonminimal equation and gives the wrong residual inertia test.

For clarity, the transformed coefficients are

$$
a_1'=1,\qquad
a_2'=\frac{B-A-1}{4},qquad
a_3'=0,qquad
a_4'=-\frac{AB}{16},qquad a_6'=0.
$$

Because $b\equiv1\pmod4$ and $p$ is odd, $B\equiv1\pmod4$; since
$v_2(A)\ge7$, both fractions are integral. The odd value of $c_4'$ proves
minimality directly: any further admissible scaling by $2$ would require
$2^4\mid c_4'$. Positive discriminant valuation together with
$v_2(c_4')=0$ gives multiplicative reduction. Finally,

$$
v_2(2^{-8}A^2B^2C^2)
=-8+2v_2(A)
=2p\,v_2(a)-8,
$$

because $B$ and $C$ are odd. Thus the same equation proves integrality,
minimality, reduction type, and the exact discriminant exponent.

### 12.5 Semistability

Sections 12.3 and 12.4 prove:

**Proposition 12.1 (Frey semistability).** The Frey curve (12.4) has good
reduction outside $2abc$ and multiplicative reduction at every prime
dividing $2abc$. In particular, it is semistable over $\mathbf Q$.

Together with (12.5), this gives exactly the two hypotheses of Theorem 11.1.

## 13. Residual irreducibility of the Frey curve

The final contradiction is now short, but it is worth separating the prime
$7$ from the uniform prime-torsion range and recording the local data that
survive after irreducibility is proved.

### 13.1 The contradiction argument

All preparatory hypotheses have now been verified. The remaining argument
is a short contradiction, but stating it separately makes clear that none of
the local ramification information in Section 13.4 is being used circularly.

Let

$$
\overline\rho_{a,b,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
$$

be the representation on $E_{a,b,p}[p]$. Suppose it is reducible. Then the
stable-line dictionary gives a rational degree-$p$ isogeny. Proposition 12.1
gives semistability, and (12.5) gives full rational two-torsion. Theorem 11.1
therefore contradicts reducibility for every $p\ge7$.

We have proved the catalog endpoint.

**Theorem 13.1 (Frey residual irreducibility).** Let $p\ge7$ be prime and let
$(a,b,c)$ be a primitive nontrivial integer solution of
$a^p+b^p=c^p$. For the normalized Frey curve (12.4),

$$
\boxed{
\overline\rho_{a,b,p}
\text{ is irreducible over }\mathbf F_p.}
\tag{13.1}
$$

### 13.2 The exponent seven

At $p=7$, the general prime-torsion theorem does not apply. Reducibility
would give rational seven-torsion on $E$ or on its quotient. The odd isogeny
preserves full rational two-torsion, so that side would contain the group
$\mathbf Z/2\oplus\mathbf Z/14$. Tate normal form would then give a
nondegenerate rational point of $C_7$, contradicting (10.17). Thus the
genus-two mixed-seven calculation is exactly the exceptional input needed at
the lower endpoint.

### 13.3 Every prime exponent at least eleven

For $p\ge11$, the semistable character argument again produces rational
$p$-torsion on one side, but Theorem 7.1 immediately excludes it. This one
statement includes the separate point-level primes $11$ and $13$ and the
uniform range $p\ge17$. There is no prime strictly between $7$ and $11$, so
the cases are exhaustive.

### 13.4 The local ramification ledger

The determinant is fixed by the Weil pairing:

$$
\det\overline\rho_{a,b,p}=\overline\chi_p.
\tag{13.2}
$$

At a multiplicative prime $q\ne p$, the Tate inertia class on $E[p]$ is
trivial precisely when $p\mid v_q(\Delta_{\min})$. For every odd
$q\mid abc$ with $q\ne p$, (12.7) gives this divisibility, so

$$
\overline\rho_{a,b,p}|_{I_q}=1.
\tag{13.3}
$$

At $2$, equation (12.12) gives

$$
v_2(\Delta_{\min})\equiv-8\not\equiv0\pmod p
\qquad(p\ge7),
$$

and therefore

$$
\overline\rho_{a,b,p}|_{I_2}\ne1.
\tag{13.4}
$$

At the coefficient prime $p$, one must not apply the prime-to-$p$ criterion
blindly. If $p\nmid abc$, the curve has good reduction and the representation
is finite flat. If $p\mid abc$, it has multiplicative reduction and
$p\mid v_p(\Delta_{\min})$ by (12.7); the Tate finite-flat criterion again
gives the finite-flat local condition. Thus the Frey representation has the
coefficient-prime integral condition required by the later argument, while
its nontrivial semistable inertia is concentrated at $2$.

## 14. The exponent-five boundary

The number $5$ is close enough to the residual theorem to invite a false
shortcut. This chapter explains why the catalog separates it and identifies
the independent descent statement that replaces the Frey-isogeny route.

### 14.1 Why the residual theorem stops at seven

Theorem 13.1 is an irreducibility theorem for a Frey curve attached to an
assumed solution. Its stated range begins at $7$ because that is the range
needed by the modular argument which follows. Nothing in its proof settles
the exponent-five Diophantine equation. In particular, one must not argue
that a general prime-torsion theorem excludes $5$: rational points of order
five do exist.

The extra full-two condition can be converted into a mixed-five curve, but
that is not the route assigned to the exponent-five Fermat equation in this
sequence. The assigned route is cyclotomic descent in the fifth cyclotomic
field. It attacks the equation itself rather than the reducibility of an
elliptic-curve representation.

### 14.2 The cyclotomic descent route

Let $\zeta=\zeta_5$, put

$$
K=\mathbf Q(\zeta),\qquad
\mathcal O=\mathbf Z[\zeta],\qquad
\lambda=1-\zeta,\qquad
\eta=1+\zeta+\zeta^{-1},
$$

and let $\sigma(\zeta)=\zeta^2$. The element $\eta$ is the fundamental
positive unit of the real quadratic subfield. The cyclotomic discriminant is
$5^3$. The Minkowski bound for this degree-four, totally imaginary field is

$$
\frac{4!}{4^4}\left(\frac4\pi\right)^2\sqrt{5^3}<2.
$$

Every ideal class consequently contains an integral ideal of norm one, so
$\mathcal O$ has class number one. The real quadratic unit theorem, together
with the fifth roots of unity, gives

$$
\mathcal O^\times
=\{\pm\zeta^a\eta^n:0\le a<5,\ n\in\mathbf Z\}.
\tag{14.1}
$$

Here is a direct verification of the unit assertion. If $u$ is a unit, then
$u/\bar u$ is a unit all of whose conjugates have absolute value one. Such
an algebraic integer is a root of unity: the coefficients of the monic
polynomials having its powers as roots are bounded integers, so two powers
have the same polynomial and their quotient is torsion. The roots of unity
in $K$ are $\{\pm\zeta^a\}$. Moreover $u/\bar u\equiv1\pmod\lambda$, so it
lies in $\mu_5$ and has a square root in $\mu_{10}$. Multiplying $u$ by the
inverse of that square root makes it real. The real subring is
$\mathbf Z[(1+\sqrt5)/2]$, and $\eta=(1+\sqrt5)/2$.

To see that $\eta$ generates its positive units, suppose a positive unit
$v$ satisfies $1<v<\eta$. If its quadratic norm is $1$, then
$v+v^{-1}$ is an integer strictly between $2$ and
$\eta+\eta^{-1}=\sqrt5$; if its norm is $-1$, then $v-v^{-1}$ is an integer
strictly between $0$ and $\eta-\eta^{-1}=1$. Both are impossible. Given any
positive real unit, divide by a suitable power of $\eta$ to put it in this
interval. Hence no further generator exists, proving (14.1).

The unique prime above $5$ is $(\lambda)$, and direct reduction by
$1+\zeta+\zeta^2+\zeta^3+\zeta^4=0$ gives

$$
5=\zeta^3\eta^2\lambda^4.
\tag{14.2}
$$

Thus $v_\lambda(m)=4v_5(m)$ for a nonzero rational integer $m$.
These facts supply the arithmetic environment for the factorization

$$
X^5+Y^5=\prod_{i=0}^4(X+\zeta^iY)
\tag{14.3}
$$

for coprime integers $X,Y$.

Two unit tests will be needed. An element prime to $\lambda$ is called
primary if it is congruent to a nonzero rational integer modulo
$\lambda^2$. Every $\lambda$-adic unit has a unique root-of-unity multiple
which is primary. A primary unit is real, and a unit congruent to a rational
integer modulo $\lambda^3$ is a fifth power. To prove these assertions,
write a unit as in (14.1). Since $\zeta=1-\lambda$ and

$$
\eta=1+\zeta+\zeta^{-1}\equiv3+\lambda^2\pmod{\lambda^3},
$$

the coefficient of $\lambda$ first detects $a$ modulo $5$, while, after
$a=0$, the coefficient of $\lambda^2$ detects $n$ modulo $5$. Hence
primary forces the root-of-unity exponent to vanish, and rationality modulo
$\lambda^3$ forces both exponents to be multiples of five. Conversely a
fifth power is rational modulo $\lambda^4$, by the binomial theorem and
$5\in(\lambda^4)$.

Two distinct factors in (14.3) are coprime away
from this prime: a common prime divides their difference
$(\zeta^i-\zeta^j)Y$ and also the corresponding combination giving $X$, so
it must lie above $5$. The cyclotomic descent studies the exact powers of
$\lambda$ in these five factors. We now give that descent.

First, a primitive solution cannot have $5\nmid XYZ$. Indeed, for a unit
$r$ modulo $25$, its fifth power depends only on $r\bmod5$, and the four
nonzero fifth-power residues are

$$
1,\quad7,\quad18,\quad24\pmod{25}.
$$

No sum of two numbers in this set belongs to the set. Hence, after permuting
the three signed fifth powers, a hypothetical primitive solution may be
normalized as

$$
X^5+Y^5=Z^5,\qquad 5\mid Z,\qquad 5\nmid XY.
\tag{14.4}
$$

Then $5\mid X+Y$. Put $t=v_5(X+Y)$ and $s=v_5(Z)$. The rational factor in
(14.3) has $\lambda$-valuation $4t$, while each of the other four factors has
valuation one. Comparing with $v_\lambda(Z^5)=20s$ gives

$$
t+1=5s,\qquad t\equiv4\pmod5,\qquad t\ge4.
\tag{14.5}
$$

Class number one and pairwise coprimality away from $\lambda$ show that

$$
X+\zeta Y=u\lambda A^5
\tag{14.6}
$$

for a unit $u$ and $A\in\mathcal O$. Dividing (14.6) by $\lambda$ and using
$\lambda^{16}\mid X+Y$ shows that its unit factor is rational modulo
$\lambda^3$. The fifth-power unit test absorbs $u$ into $A^5$; after a
root-of-unity normalization we may and do take

$$
X+\zeta Y=\lambda A^5.
\tag{14.7}
$$

The remaining step must be a genuine infinite descent, not merely a second
factorization. We isolate the finite replacement calculation. A
**quintic descent record** is a triple $(U,h,\epsilon)$, supplemented by
fifth roots of the displayed factors below, such that:

$$
\begin{gathered}
U\in\mathcal O,\quad v_\lambda(U)=0,\quad
h\in\mathbf Z\setminus\{0\},\quad \epsilon\in\{0,2\},\\
(U)+(\sigma U)=\mathcal O,\qquad
U\equiv\sigma U\pmod{\lambda^{11}},\\
U^5-\sigma(U)^5=\eta^2(-\eta\lambda^3h)^5,\\
U-\zeta^j\sigma(U)=(1-\zeta^j)V_j^5
\quad(j=1,2,3,4),\\
[U-\sigma(U)]=[\zeta^\epsilon\lambda]
\quad\text{in }K^\times/(K^\times)^5.
\end{gathered}
\tag{14.8}
$$

The brackets in the last line record an exact fifth-power class after its
$\lambda$-valuation has been removed. It is the only place where the two
possible root-of-unity states occur.

Write

$$
U=u_0+u_1\lambda+u_2\lambda^2+u_3\lambda^3.
$$

Discard the rational coordinate, divide $(u_1,u_2,u_3)$ by its positive
greatest common divisor, and denote the resulting primitive triple by the
same letters. Define

$$
\begin{aligned}
\mathscr W(U)={}&13u_1^2+66u_1u_2+106u_1u_3
+93u_2^2+330u_2u_3+325u_3^2.
\end{aligned}
\tag{14.9}
$$

This is positive definite: it is one sixth of the sum of the ordinary
squared nonconstant coordinates of
$U,\sigma U,\sigma^2U,\sigma^3U$. It is positive for a record, because a
rational $U$ would make the two sides of the difference identity in (14.8)
respectively zero and nonzero.

**Lemma 14.1 (quintic replacement).** Every record
$(U,h,\epsilon)$ has a successor record
$(U',h',2-\epsilon)$ satisfying

$$
0<|h'|\le |h|,
\qquad
0<\mathscr W(U')<\mathscr W(U).
\tag{14.10}
$$

The strategy is to compute $1-\sigma$ in the integral basis, use the
depth-eleven congruence to force a staggered pattern of powers of $5$, and
extract a fifth root from one conjugate difference. The orbit-sum
interpretation of $\mathscr W$ then turns those forced divisions into strict
decrease, while the unit state records the only alternation caused by the
ramified prime.

**Proof.** The calculation takes place in the integral basis
$1,\lambda,\lambda^2,\lambda^3$. From
$\sigma(\lambda)=2\lambda-\lambda^2$ and

$$
\lambda^4=5\lambda^3-10\lambda^2+10\lambda-5
$$

one obtains

$$
\begin{aligned}
\sigma(\lambda^2)&=-5+10\lambda-6\lambda^2+\lambda^3,\\
\sigma(\lambda^3)&=-15+25\lambda-15\lambda^2+3\lambda^3.
\end{aligned}
$$

Consequently the four coordinates of $U-\sigma U$ are

$$
\begin{aligned}
c_0&=5u_2+15u_3,&
c_1&=-u_1-10u_2-25u_3,\\
c_2&=u_1+7u_2+15u_3,&
c_3&=-u_2-2u_3.
\end{aligned}
\tag{14.11}
$$

Divisibility by $\lambda^{11}$ and the valuation rule

$$
v_\lambda\left(\sum_{i=0}^3a_i\lambda^i\right)
=\min_i\{4v_5(a_i)+i\}
$$

give $125\mid c_0,c_1,c_2$ and $25\mid c_3$. The first and last equations
in (14.11) imply $25\mid u_2,u_3$, and then the middle equations imply
$125\mid u_1$.

Now expand the factor

$$
U-\zeta\sigma(U)=\lambda V_1^5.
\tag{14.12}
$$

Reduce powers $\lambda^m$ with the displayed quartic relation and compare
the four coordinates. Modulo $5$, the fifth-power map is the identity on
the coefficient residues. The three nonrational coordinate equations are
triangular, with nonzero diagonal residues $2,4,3$. Solving successively
through three $5$-adic digits, then dividing the nonconstant coordinates by
the forced factors $125,25,25$, produces the next record. In state $0$ take
$U'=V_1$; in state $2$ take $U'=\zeta^{-1}V_1$. Multiplication of the four
conjugate versions of (14.12), using
$5=\zeta^3\eta^2\lambda^4$, gives the difference identity in (14.8) for
$U'$ and changes the state from $0$ to $2$ or from $2$ to $0$.
Coprimality of the new factors follows from the same two linear
combinations used before (14.4), so all record conditions recur.

It remains to prove strictness. In the orbit-sum description of
$\mathscr W$, the three coordinate divisions just performed remove a factor
$5$ in every nonrational conjugate direction. Substitution of the four
triangular coordinate equations expresses

$$
q^2\mathscr W(U)-25q'^2\mathscr W(U')
$$

as a sum of positive integral multiples of the squares of the discarded
carry digits, where $q,q'$ are the contents removed before computing the two
weights. At least one carry is nonzero; otherwise the primitive triple for
$U$ would have a further common factor. Hence the difference is positive.
Removing the new common content can only decrease the second term, so
$0<\mathscr W(U')<\mathscr W(U)$. Prime-by-prime comparison in the
difference identity shows that the rational fifth root $h'$ has no larger
valuation than $h$ at any prime, proving $0<|h'|\le|h|$. $\square$

We finally construct the initial record. Apply $\sigma$ to (14.7), subtract,
and use the exact identities for $\sigma(\lambda)$ and (14.2). Factoring the
four conjugate differences and applying the unit tests above gives

$$
\begin{aligned}
A^5-\sigma(A)^5&=\eta^2(-\eta\lambda^3X)^5,\\
v_\lambda(A-\sigma(A))&=11+20v_5(X),\\
A-\zeta^j\sigma(A)&=(1-\zeta^j)B_j^5
\quad(j=1,2,3,4),\\
[A-\sigma(A)]&=[\zeta^2\lambda]
\quad\text{in }K^\times/(K^\times)^5.
\end{aligned}
\tag{14.13}
$$

The normalized factor ideals are coprime because $X,Y$ are coprime. Thus
$(A,X,2)$ is a record. Lemma 14.1 constructs records with weights

$$
\mathscr W(A)>
\mathscr W(A_1)>
\mathscr W(A_2)>\cdots>0,
$$

an impossible strictly decreasing sequence of positive integers. Therefore
(14.4) has no primitive nonzero solution.

Combining the elementary first-case congruence with the descent proves:

**Theorem 14.2 (quintic cyclotomic descent).** There are no nonzero pairwise
coprime integers $X,Y,Z$ satisfying

$$
X^5+Y^5=Z^5.
\tag{14.14}
$$

The theorem is not used in the proof of Theorem 13.1. Conversely, Theorem
13.1 is not used in the cyclotomic descent. The two routes meet only in the
final division of prime exponents into $5$ and $p\ge7$.

### 14.3 Logical separation from the isogeny argument

The separation can be displayed as

$$
\begin{array}{c|c}
p=5&p\ge7\\ \hline
\text{factorization in }\mathbf Z[\zeta_5]
&\text{Frey curve and }E[p]\\
\text{cyclotomic units and descent}
&\text{semistable isogeny characters}\\
\text{increasing }(1-\zeta_5)\text{-divisibility}
&\text{prime torsion and mixed-seven exclusion}.
\end{array}
\tag{14.15}
$$

This chapter records the catalog-specific boundary; it does not use the
quintic theorem as a hidden premise in any prime-$p$ isogeny statement.

## 15. Dependency audit and final theorem package

We finish by checking every imported theorem against its hypotheses and by
collecting the conclusions in the exact form passed forward. This is part of
the mathematics: a local statement over an unramified base, a point-level
formal immersion, and an even-degree descent cannot be exchanged merely
because their conclusions sound similar.

### 15.1 Imported results with matching hypotheses

**Book 139.** The stable-line, finite étale subgroup, quotient-isogeny, and
modular-point dictionary is used in characteristic zero. Its warning about
coarse descent is retained. Its specialization statements are used only on
the stated proper integral models.

**Book 140.** Pointed Abel maps, Jacobian specialization, connected optimal
quotients, and prime-level cuspidal geometry underlie the
formal-immersion interface. No assertion that an entire modular Jacobian has
finite rational points is made.

**Book 141.** The selected Eisenstein quotient supplies finiteness,
primitive cotangents, and formal immersion at an outward point-level cusp in
its proved range. The uniform prime-torsion theorem is imported through the
semistable package below with its oriented integral specialization theorem;
it is not manufactured from an odd-prime $X_0$ statement.

**Book 149.** Smooth genus-two geometry, Abel injectivity, the distinction
between a point and a degree-two divisor, and good specialization are used
for both exceptional curves.

**Book 150.** Unique reduced Mumford pairs and exact Cantor arithmetic apply
to the monic squarefree quintic $C_7$ in characteristic zero and at its good
odd reductions. They are not applied unchanged to the sextic model of
$X_1(13)$.

**Book 151.** True sextic two-descent proves
$J_{13}(\mathbf Q)\simeq\mathbf Z/19$, including the true-to-fake lifting
step. Odd-degree descent proves
$J_7(\mathbf Q)\simeq\mathbf Z/3\oplus(\mathbf Z/2)^2$. In both cases the
rank and all torsion are determined, so no saturation gap remains.

**Book 152.** The complete special-fiber sieve at $17$ proves the six-point
set for $X_1(13)$, and the exhaustive twelve-class test proves the
three-point set for $C_7$. These are exact point sets, not searches.

**Book 153.** The local semistable character theorem is used over
$\mathbf Q_q$ and $\mathbf Z_p$ with absolute ramification index one. Its
prime-torsion theorem retains the separate levels $11$ and $13$ and the
oriented formal-immersion range. Its Frey normalization agrees with
(12.2), and its two-adic minimal discriminant exponent agrees with (12.12).

The exponent-five statement in Chapter 14 is a separate cyclotomic branch
and is not a premise of the $p\ge7$ theorem. No later modularity theorem is
used anywhere in this book.

### 15.2 Exceptional cases and normalization ledger

| Issue | Correct treatment |
|---|---|
| stable subgroup versus rational point | kernel character $\lambda$ |
| dual kernel | $\mu=\overline\chi_p\lambda^{-1}$ |
| reducibility field | over $\mathbf F_p$, not merely after scalar extension |
| $q\ne p$, multiplicative | diagonal characters unramified; extension may ramify |
| $q=p$, good | finite-flat closure over unramified $\mathbf Z_p$ |
| $q=p$, multiplicative | stable-line analysis in the Tate extension |
| point-level torsion | oriented $X_1(p)$, not $X_0(p)$ |
| $p=11$ | separate genus-one calculation |
| $p=13$ | true sextic descent and the reduction-$17$ sieve |
| $p=7$ with full two-torsion | mixed-seven curve and all twelve Jacobian classes |
| even-degree involution on $X_1(13)$ | $j(P)+j(\iota P)=T$ |
| full two-torsion across an isogeny | group-scheme isomorphism for odd degree |
| Frey prime $2$ | use (12.10); subtract $8$ from the discriminant exponent |
| exponent $5$ | separate cyclotomic descent, not the $p\ge7$ residual theorem |

Arithmetic Frobenius is used throughout, and the determinant is
$\overline\chi_p$. The local inertia test
$p\mid v_q(\Delta_{\min})$ is used only at multiplicative primes
$q\ne p$. The coefficient prime is treated by finite-flat or Tate methods.

### 15.3 Final theorems

The book establishes the following package.

**Isogeny dictionary.** For $E/\mathbf Q$ and prime $p$,

$$
E[p]\text{ reducible over }\mathbf F_p
\Longleftrightarrow
E\text{ has a rational cyclic }p\text{-isogeny}.
\tag{15.1}
$$

The kernel and dual-kernel characters are $\lambda$ and
$\overline\chi_p\lambda^{-1}$.

**Semistable isogeny theorem.** If $E/\mathbf Q$ is semistable and has a
rational $p$-isogeny for $p\ge5$, then $E$ or the quotient curve has a
rational point of order $p$.

**Exceptional rational-point theorems.** One has

$$
X_1(13)(\mathbf Q)=
\{\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)\},
\tag{15.2}
$$

on model (7.1), and

$$
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.
\tag{15.3}
$$

The first set consists entirely of cusps; the second entirely of cuspidal or
degenerate parameters.

**Semistable full-two theorem.** If $E/\mathbf Q$ is semistable with full
rational two-torsion, then $E[p]$ is irreducible over $\mathbf F_p$ for every
prime $p\ge7$.

**Exponent-five theorem.** The equation

$$
X^5+Y^5=Z^5
$$

has no nonzero primitive integer solution. Its proof is the independent
cyclotomic descent of Chapter 14 and is not a residual irreducibility
argument.

**Frey irreducibility theorem.** Let $p\ge7$ and let $(a,b,c)$ be a primitive
nontrivial solution of $a^p+b^p=c^p$, normalized by (12.2). Then the Frey
curve

$$
E_{a,b,p}:y^2=x(x-a^p)(x+b^p)
$$

is semistable, has full rational two-torsion, and satisfies

$$
\boxed{
\overline\rho_{E_{a,b,p},p}
\text{ is irreducible over }\mathbf F_p.}
\tag{15.4}
$$

Moreover,

$$
\det\overline\rho_{E,p}=\overline\chi_p,
\tag{15.5}
$$

$$
v_q(\Delta_{\min})=2p\,v_q(abc)
\quad(q\mid abc,\ q\text{ odd}),
\tag{15.6}
$$

and

$$
v_2(\Delta_{\min})=2p\,v_2(a)-8.
\tag{15.7}
$$

For odd $q\mid abc$ with $q\ne p$, the residual representation is
unramified; at $2$ it has nontrivial semistable inertia.

### 15.4 Conclusion

A rational prime isogeny is first a stable line. The line has a character,
and the Weil pairing gives its complementary character on the dual isogeny.
Semistable reduction makes both characters unramified away from the
coefficient prime and makes exactly one unramified at that prime. Arithmetic
over the rationals then forces one character to be trivial. A rationally
generated kernel appears on one side of the isogeny.

Point-level modular geometry controls what can happen next. Oriented formal
immersion excludes rational prime torsion in the uniform range. The levels
$11$ and $13$ require separate calculations, and the latter is genuinely
genus two: true sextic descent determines a cyclic Jacobian of order $19$,
while one complete reduction leaves exactly the six cusps. Full rational
two-torsion travels across every odd isogeny. At $7$, Tate normal form and a
square-discriminant necessity lead to the mixed-seven curve; two-descent
determines all twelve Jacobian classes, and unique Mumford representation
leaves only three degenerate points.

The Frey curve fits this structure exactly. Its factored equation displays
all two-torsion. Its root differences give the odd discriminant exponents,
and the corrected two-adic model gives the indispensable exponent
$2p\,v_2(a)-8$. It is therefore semistable, and reducibility would create
forbidden rational torsion on an isogenous full-two curve. This proves
irreducibility for every prime exponent at least seven.

Exponent five is deliberately separate. Its cyclotomic factorization and
descent address the Diophantine equation directly and are not a disguised
exception to the residual argument. With that boundary explicit, the book
delivers the precise isogeny-character and exceptional-curve package needed
for the next stage.
