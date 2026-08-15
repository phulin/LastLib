# Changing the Coefficient Prime while Keeping the Frey Special Place

## Contents

1. [Scope](#1-scope)
2. [The starting arithmetic data](#2-the-starting-arithmetic-data)
   - [The family and its coefficient field](#21-the-family-and-its-coefficient-field)
   - [The exact local record at two](#22-the-exact-local-record-at-two)
   - [Ramification away from two](#23-ramification-away-from-two)
3. [The special parameter at two](#3-the-special-parameter-at-two)
   - [The monodromy line](#31-the-monodromy-line)
   - [The conductor is one](#32-the-conductor-is-one)
4. [Selecting the coefficient place above three](#4-selecting-the-coefficient-place-above-three)
   - [Prime versus place](#41-prime-versus-place)
   - [The rational companion](#42-the-rational-companion)
   - [What local--global compatibility is doing](#43-what-local--global-compatibility-is-doing)
5. [Lattices and the integral special line](#5-lattices-and-the-integral-special-line)
   - [A stable lattice and its saturated line](#51-a-stable-lattice-and-its-saturated-line)
   - [Integral monodromy thickness](#52-integral-monodromy-thickness)
   - [The residual line and sign](#53-the-residual-line-and-sign)
   - [Changing the lattice](#54-changing-the-lattice)
6. [Residual image at the selected place](#6-residual-image-at-the-selected-place)
   - [What compatibility does not prove](#61-what-compatibility-does-not-prove)
   - [A valid direct certificate](#62-a-valid-direct-certificate)
   - [Choosing an admissible place](#63-choosing-an-admissible-place)
7. [Prime-switch theorem](#7-prime-switch-theorem)
8. [The role of the switched member in the endgame](#8-the-role-of-the-switched-member-in-the-endgame)
   - [Coefficient-prime integrality](#81-coefficient-prime-integrality)
   - [The residual stage](#82-the-residual-stage)
   - [The classification theorem](#83-the-classification-theorem)
   - [The exact integral requirements](#84-the-exact-integral-requirements)
9. [Logical boundaries of the prime switch](#9-logical-boundaries-of-the-prime-switch)
   - [The decisive local argument](#91-the-decisive-local-argument)
   - [Coefficient fields and compatibility](#92-coefficient-fields-and-compatibility)
   - [What integrality and reduction retain](#93-what-integrality-and-reduction-retain)
   - [Chronology of the proof](#94-chronology-of-the-proof)
10. [Conclusion](#10-conclusion)

## 1. Scope

This chapter performs one operation. Starting with either the rank-two compatible collection
that contains the distinguished Frey lift or its selected-three member, it selects a member of coefficient characteristic
$3$ and proves that its local representation at $2$ has the same special
(Steinberg) record as the original member.

The record to be preserved is

$$
\operatorname{Sp}_2(\varepsilon):
\qquad r_2|_{I_2}=1,\qquad N_2\ne0,\qquad
\operatorname{rank}N_2=1,
$$

together with its monodromy line, its sign $\varepsilon\in\{\pm1\}$, and its
conductor exponent $1$. The nilpotent operator is part of the datum. Deleting it
would change a special parameter into an unramified one.

Nothing here reconstructs compatible-family theory, automorphic descent, integral
$3$-adic Hodge theory, or the classification of finite-flat group schemes. The argument
isolates the rational prime-switching step, and the final sections explain how its output
enters the later integral and classification arguments.

A family-wide all-odd spreading theorem, which equips every odd-coefficient member with an
integral model, is stronger and lies outside the scope needed here. The contradiction selects
one place $\nu\mid3$, and the selected route needs an all-level
integral tower only for this one member. It still needs that member to be unramified at
every base prime outside $\{2,3\}$, because those local conditions glue the tower over
$\mathbf Z[1/2]$. Thus `one coefficient place'' must not be confused with`one rational
base place.''

Book 178, Theorem 12.2 supplies the restricted signed-special finite fibre and retained
support. Book 182, Proposition 7.1 and Theorem 9.1 then construct the selected packet array and
its member at the chosen place above $3$. Books 183--185 turn that member into the effective
base-field representation used below. No uniform all-coefficient raw-to-global theorem is
part of this route.

Throughout, Frobenius is arithmetic and
$\chi_q(\operatorname{Frob}_v)=v$ for $v\ne q$.

## 2. The starting arithmetic data

Let $p\ge5$ be the coefficient characteristic of the distinguished Frey lift. The
argument begins with the following arithmetic data.

### 2.1 The family and its coefficient field

The preferred input is the selected conclusion of Book 185, Theorem 9.1: a number field $E$,
a place $\nu\mid3$, and one actual member $V_\nu$ over $E_\nu$, together with the determinant,
common pure good polynomials, clean support, restriction recovery, and dyadic SP pair listed
below. No representation at a second coefficient place is assumed.

Optionally, this member may be displayed inside an away-from-two compatible collection

$$
\mathcal R^{(2)}=\{r_\lambda:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(E_\lambda)\}_{\lambda\nmid2}
\tag{2.1}
$$

of continuous absolutely irreducible rank-two representations. In that display the member
$r_{\lambda_p}$ is the distinguished Frey lift after a stated common scalar extension. Every
coefficient enlargement needed to define the family and its local parameters has
already been made. In particular, $E$ in (2.1) is the final coefficient field,
not a temporary trace field.

In the preferred reading every occurrence of $r_\nu$ means $V_\nu$. Sections 3--7 inspect only
this member, so every universal quantifier over $\lambda$ in Sections 2--3 may be specialized
to $\lambda=\nu$.

There is a finite certified exceptional set $S$, containing $2$, such that for every
rational prime $v\notin S$ there is a polynomial

$$
P_v(X)=X^2-a_vX+v\in E[X]
\tag{2.2}
$$

such that, for $v\nmid\ell(\lambda)$,

$$
\det\!\left(X-r_\lambda(\operatorname{Frob}_v)\right)
=\iota_\lambda P_v(X).
\tag{2.3}
$$

Also,

$$
\det r_\lambda=\chi_{\ell(\lambda)}.
\tag{2.4}
$$

The polynomials are pure of weight one: for every root $\alpha$ of $P_v$ and every
complex embedding $\iota$ of a splitting field,

$$
|\iota(\alpha)|=v^{1/2}.
\tag{2.4a}
$$

Purity is an independent part of the compatible-family input. It is not a consequence of
the constant term $v$ or of the cyclotomic determinant.

The phrase “same Frobenius polynomial” always means the two images of (2.2)
under the relevant embeddings. It never means that two unrelated completions of
$E$ have been identified.

### 2.2 The exact local record at two

Strong local compatibility at $2$ supplies one Frobenius-semisimple
Weil--Deligne pair over $E$,

$$
D_2=(r_2,N_2),
\tag{2.5}
$$

whose scalar extension is
$\operatorname{WD}_2(r_\lambda)^{\mathrm{F\text{-}ss}}$ for every
$\lambda\nmid2$. It is known from the Frey member, by local--global
compatibility at $2$, that $D_2$ is special. Explicitly,

$$
r_2|_{I_2}=1,
\qquad N_2^2=0,
\qquad N_2\ne0.
\tag{2.6}
$$

If $\phi_2$ denotes arithmetic Frobenius, the Weil--Deligne relation is

$$
r_2(\phi_2)N_2r_2(\phi_2)^{-1}=2N_2.
\tag{2.7}
$$

The action of $D_2$ on its one-dimensional quotient defines an unramified character
$\eta$. Its Frobenius value is the sign

$$
\eta^2=1,
\qquad \varepsilon=\eta(\phi_2)\in\{\pm1\}.
\tag{2.8}
$$

Here the pair $D_2$ determines which sign occurs; the determinant and the
Weil--Deligne relation force its square to be one.

The word _sign_ in this chapter means exactly (2.8). It is the Frobenius
eigenvalue on the one-dimensional quotient by the monodromy line. No root-number
convention is being smuggled into the notation.

The input is the full pair (2.5), not merely a local Euler factor or a conductor
integer. Weak compatibility alone is insufficient for this chapter.

### 2.3 Ramification away from two

Book 185 gives the common pure polynomials outside $S$ and separately proves the clean-support
statement

$$
(\mathrm U)\qquad
r_\nu\text{ is unramified at every rational prime }v\ne2,3
\quad\text{for the selected }\nu\mid3.
\tag{2.9}
$$

This is not a consequence of equality at the cofinite set of good Frobenius classes. Book
185, Proposition 8.3 proves it by a different argument: equivariant conductor and
invariant-Frobenius independence anchor every elementary raw packet at the distinguished
irreducible member; Book 128, Lemma 3.2 passes its unramified pair to the elementary
semisimplification; and actual Brauer direct-sum cancellation constructs the common rank-two
local complement. The distinguished member makes that complement unramified away from $2$
and the old coefficient prime, and the split unitary good cover treats that old prime. Thus
Book 185 proves $(\mathrm{AUX}_\nu)$ and then $(\mathrm U)$ for the selected $\nu\mid3$.
Under the optional uniform hypotheses it also proves $(\mathrm{AUX}_{\mathrm{all}})$ and
$(\mathrm{Cond}_2)$. The selected argument also supplies an exceptional-prime Galois Frobenius
polynomial, but not its weight-one purity or an automorphic-type identification.

## 3. The special parameter at two

The local calculation is short, but every part of it is used later.

### 3.1 The monodromy line

Put

$$
L_2=\ker N_2.
\tag{3.1}
$$

Since $N_2$ is a nonzero nilpotent operator on a two-dimensional space,

$$
\dim_E L_2=1,
\qquad
L_2=\ker N_2=\operatorname{im}N_2.
\tag{3.2}
$$

Equation (2.7) makes $L_2$ stable under the Weil group. It is the unique line
with this monodromy description, so it is defined over the actual coefficient
field $E$; no splitting field for Frobenius is required.

Choose $e_1\in L_2$ and choose $e_0$ with $N_2e_0=e_1$. After
Frobenius-semisimplification the basis may be chosen so that

$$
r_2(\phi_2)e_1=2\varepsilon e_1,
\qquad
r_2(\phi_2)e_0=\varepsilon e_0,
\qquad
N_2e_0=e_1.
\tag{3.3}
$$

Indeed, (2.7) says that the eigenvalue on $L_2$ is twice the eigenvalue on
$D_2/L_2$, and (2.4) says that their product is $2$. The quotient eigenvalue
therefore has square $1$, giving (2.8) and (3.3).

Equivalently, every adic realization at a coefficient place $\lambda\nmid2$
has a nonsplit special filtration

$$
0\longrightarrow E_\lambda(\eta_\lambda\chi_{\ell(\lambda)})
\longrightarrow r_\lambda|_{G_{\mathbf Q_2}}
\longrightarrow E_\lambda(\eta_\lambda)
\longrightarrow0,
\tag{3.4}
$$

where “nonsplit” refers to its nonzero monodromy. Formula (3.4) records the
orientation of the line as well as the semisimplified characters.

### 3.2 The conductor is one

The finite part $r_2$ is unramified, so its Artin conductor is zero. The
Weil--Deligne conductor formula gives

$$
\begin{aligned}
a_2(D_2)
&=a(r_2)+\dim D_2^{I_2}
  -\dim(\ker N_2)^{I_2}\\
&=0+2-1=1.
\end{aligned}
\tag{3.5}
$$

The same result is visible on the associated adic representation: tame inertia
acts unipotently and nontrivially, its fixed space is $L_2$, wild inertia is
trivial, and hence the tame conductor is one and the Swan conductor is zero.

Thus the four pieces

$$
(N_2\ne0,\ L_2,\ \varepsilon,\ a_2=1)
\tag{3.6}
$$

are mutually compatible consequences of one special local parameter. The
conductor alone does not recover the line or the sign, and trivial finite
inertial type does not mean that the adic representation is unramified.

## 4. Selecting the coefficient place above three

### 4.1 Prime versus place

Factor in the final coefficient field

$$
3\mathcal O_E=\prod_{\nu\mid3}\nu^{e_\nu}.
\tag{4.1}
$$

Select an actual place $\nu\mid3$ and put

$$
K=E_\nu,
\qquad \mathcal O=\mathcal O_K,
\qquad \mathfrak m=(\varpi),
\qquad k=\mathcal O/\mathfrak m.
\tag{4.2}
$$

The selected member is

$$
V=r_\nu:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(K).
\tag{4.3}
$$

This is selection from (2.1), or the representation constructed directly by Book 185,
Proposition 9.2; it is not scalar extension of
$r_{\lambda_p}$. There is generally no map
$E_{\lambda_p}\to E_\nu$ over which such a tensor product could be formed.

The residue field is $k\simeq\mathbf F_{3^{f_\nu}}$. A rank-two residual
representation over $k$ becomes $2f_\nu$-dimensional after restriction of scalars
to $\mathbf F_3$. It is already two-dimensional over $\mathbf F_3$ when
$f_\nu=1$; when $f_\nu>1$, that conclusion requires a separate coefficient
descent. Likewise, $K=\mathbf Q_3$ requires both ramification index and residue
degree one; residue degree one by itself does not exclude a ramified extension.

Because $3$ is fixed, density and large-prime exceptional-set arguments do not
select $\nu$. Every downstream condition must be checked at one of the finitely
many actual places in (4.1).

### 4.2 The rational companion

For every certified good prime $v\notin S$ with $v\ne3$, the rational input gives

$$
V\text{ is unramified at }v,
\qquad
\det\!\left(X-V(\operatorname{Frob}_v)\right)
=X^2-\iota_\nu(a_v)X+v.
\tag{4.4}
$$

Every root of the algebraic polynomial $P_v\in E[X]$ has complex absolute value $v^{1/2}$
under every complex embedding. Separately, the clean-support certificate $(\mathrm U)$ says that
$V$ is unramified at all $v\ne2,3$, including the finitely many auxiliary primes not covered
by the certified good set. It does not manufacture a pure common polynomial at one of those
auxiliary primes: Book 185 supplies the common unramified Galois polynomial there, but not the
separate weight-one purity assertion.

In addition,

$$
\det V=\chi_3.
\tag{4.5}
$$

Since $2\ne3$, strong compatibility at $2$ applies directly:

$$
\operatorname{WD}_2(V)^{\mathrm{F\text{-}ss}}
\simeq D_2\otimes_EK.
\tag{4.6}
$$

Scalar extension cannot kill a nonzero linear map. Therefore

$$
N_{2,\nu}\ne0,
\qquad
L_{2,\nu}=L_2\otimes_EK,
\qquad
\varepsilon_\nu=\varepsilon,
\qquad
a_2(V)=1.
\tag{4.7}
$$

This is the required preservation of the Frey special record.

### 4.3 What local--global compatibility is doing

There are two distinct identifications in the proof:

1. the good polynomials (2.2) identify the global semisimple member at $\nu$;
2. the strong local statement (2.5) identifies its full pair at $2$, including
   $N_2$.

Chebotarev may identify two already-constructed semisimple global
representations from their good polynomials. It does not, from a list of local
Euler factors alone, manufacture a bad-place monodromy operator. Conversely,
strong compatibility at $2$ says nothing about the behavior of $V$ at the
coefficient-prime place $3$. Crystallinity, Hodge type, and finite flatness at
$3$ require the separate certificate assigned to Book 187.

## 5. Lattices and the integral special line

### 5.1 A stable lattice and its saturated line

Compactness of the image of $V$ gives a globally
$G_{\mathbf Q}$-stable free rank-two lattice

$$
T\subset V.
\tag{5.1}
$$

This lattice is not canonical. Define

$$
T_2^+=T\cap L_{2,\nu}.
\tag{5.2}
$$

Because $L_{2,\nu}$ is a $K$-line, $T_2^+$ is saturated in $T$ and is free of
rank one. Both it and the free rank-one quotient $T/T_2^+$ are
$G_{\mathbf Q_2}$-stable. After choosing generators, (3.4) becomes

$$
0\longrightarrow\mathcal O(\eta\chi_3)
\longrightarrow T
\longrightarrow\mathcal O(\eta)
\longrightarrow0
\quad\text{over }G_{\mathbf Q_2}.
\tag{5.3}
$$

The displayed copies of $\mathcal O$ depend on choices of generators; the
saturated submodule (5.2) does not.

### 5.2 Integral monodromy thickness

Normalize the tame $3$-adic character
$t_3:I_2\twoheadrightarrow\mathbf Z_3$. For a generator $x$ of $T_2^+$ and a
lift $y\in T$ of a generator of $T/T_2^+$, inertia has the form

$$
\sigma(x)=x,
\qquad
\sigma(y)=y+c_Tt_3(\sigma)x,
\qquad c_T\in\mathcal O\setminus\{0\}.
\tag{5.4}
$$

Changing the normalized generators multiplies $c_T$ by a unit. Hence the ideal

$$
\mathfrak c_2(T)=c_T\mathcal O
\tag{5.5}
$$

is the lattice's integral monodromy thickness at $2$. Its nonvanishing is the
rational assertion $N_{2,\nu}\ne0$; its valuation is additional integral data.

For an open ideal $I\subset\mathcal O$, the inertia action on $T/IT$ is
nontrivial exactly when

$$
c_T\notin I.
\tag{5.6}
$$

In particular, for $\overline T=T/\mathfrak mT$,

$$
a_2(\overline T)=
\begin{cases}
1,&c_T\notin\mathfrak m,\\
0,&c_T\in\mathfrak m.
\end{cases}
\tag{5.7}
$$

Here the conductor refers to the actual residual representation attached to
$T$, not just its semisimplification. Rational nonzero monodromy does not by
itself imply the first line of (5.7). A claim that the residual conductor remains
one must therefore include the primitive-monodromy certificate
$\mathfrak c_2(T)=\mathcal O$.

For a concrete counterexample to the tempting rational-to-residual inference, take
$\mathcal O=\mathbf Z_3$ and let tame inertia act in an adapted basis by

$$
\sigma\longmapsto
\begin{pmatrix}1&3t_3(\sigma)\\0&1\end{pmatrix}.
\tag{5.7a}
$$

The resulting rational monodromy is nonzero, but reduction modulo $3$ makes inertia trivial.
Here $c_T=3$, so (5.7a) realizes exactly the second case of (5.7).

### 5.3 The residual line and sign

Reduction of (5.2) gives a $G_{\mathbf Q_2}$-stable line

$$
\overline L_2=T_2^+/\mathfrak mT_2^+
\subset\overline T.
\tag{5.8}
$$

On this line arithmetic Frobenius has eigenvalue
$2\overline\varepsilon=-\overline\varepsilon$, while on the quotient it has
eigenvalue $\overline\varepsilon$. These are distinct in characteristic $3$.
Thus (5.8) retains the orientation and sign of the special filtration even if
the residual inertia extension in (5.4) happens to split.

The residual semisimplification is

$$
\overline T^{\mathrm{ss}}|_{G_{\mathbf Q_2}}
\simeq
\overline\eta\,\overline\chi_3
\oplus\overline\eta.
\tag{5.9}
$$

It is unramified at $2$ and forgets $c_T$. Consequently (5.9) cannot be used to
prove residual conductor one. The full lattice extension (5.4), not residual
Brauer--Nesbitt, is the relevant object.

### 5.4 Changing the lattice

All globally stable lattices in $V$ are commensurable. Commensurability preserves
the rational pair (4.6), the $K$-line $L_{2,\nu}$, the sign, and conductor one of
$V$. It need not preserve the valuation of $c_T$ or the residual extension class.

If $\overline T$ is absolutely irreducible for one stable lattice, stable lattices
are homothetic and the residual representation is independent up to isomorphism.
Even then, residual conductor one must be read from the resulting value of
$\mathfrak c_2(T)$; absolute irreducibility is not a substitute for that local
calculation.

Book 187 may need to replace $T$ in order to obtain its coefficient-prime
integral model at $3$. After that replacement, (5.2)--(5.9) must be recomputed for
the selected lattice. One may not retain $c_T$ from a discarded lattice.

## 6. Residual image at the selected place

### 6.1 What compatibility does not prove

The lattice-independent object is

$$
\overline r_\nu^{\mathrm{ss}}:
G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k).
\tag{6.1}
$$

Neither compatibility nor characteristic-zero absolute irreducibility proves
that (6.1) is absolutely irreducible. At the fixed prime $3$ there is no
“all but finitely many primes” argument to invoke.

If a downstream theorem needs absolute irreducibility, adequacy, a specified
projective image, or a two-dimensional $\mathbf F_3$ model, that condition is
part of the selection test for $\nu$ and must be established directly.

### 6.2 A valid direct certificate

A direct absolute-irreducibility certificate may be given by two elements
$g,h\in G_{\mathbf Q}$ whose matrices are computed from unramified Frobenius
classes:

- $\overline r_\nu(g)$ has two distinct eigenlines over $\overline k$;
- $\overline r_\nu(h)$ preserves neither of those eigenlines.

Then no line over $\overline k$ is stable under the image, so (6.1) is absolutely
irreducible. A single irreducible characteristic polynomial over $k$ proves only
irreducibility over $k$; it is not an absolute-irreducibility certificate.

If no such image calculation or earlier theorem is available, this chapter makes no
residual-image assertion. The rational prime switch still goes through, but a later residual
argument may require the missing calculation.

### 6.3 Choosing an admissible place

The factorization of $3\mathcal O_E$ first determines the fields $K=E_\nu$ and $k$. The
actual representation $V=r_\nu$ must then come from the family (2.1) or from Book 185,
Proposition 9.2. Book 185's certified good set supplies its Frobenius polynomials and purity,
while Propositions 8.3 and 8.1 supply clean support outside $\{2,3\}$. Strong compatibility
in (4.6) supplies the special record at two. These are rational properties of the chosen
member.

Integral and residual properties require further objects. A named stable lattice determines
the residual representation and the thickness ideal $\mathfrak c_2(T)$; absolute
irreducibility or a more precise image statement requires a direct calculation such as
Section 6.2 or an exact earlier theorem. Crystalline Hodge behavior at three requires a
coefficient-prime comparison, and finite-flat quotients require an integral lattice theorem.
Thus selecting $\nu$ means finding one actual place for which every property used later has
its own proof. Merely choosing the rational prime $3$ does not make all places above it behave
alike.

## 7. Prime-switch theorem

**Theorem 7.1 (Frey special record at coefficient prime three).** Assume the rational starting
data of Sections 2.1--2.3, and choose a place $\nu\mid3$ of the final coefficient
field. Let $V=r_\nu$.

Then:

1. $V$ is an actual absolutely irreducible two-dimensional $E_\nu$-representation with
   $\det V=\chi_3$; it is not obtained by tensoring the original $p$-adic member
   with $E_\nu$.
2. At every certified good prime $v\notin S$ with $v\ne3$, it has the common
   polynomial $P_v$, whose roots are pure of weight one. It is unramified outside
   $\{2,3\}$.
3. Its Frobenius-semisimple Weil--Deligne pair at $2$ is
   $D_2\otimes_EE_\nu$.
4. Its monodromy is nonzero of rank one. The line
   $L_{2,\nu}=\ker N_{2,\nu}=\operatorname{im}N_{2,\nu}$ is
   $G_{\mathbf Q_2}$-stable; arithmetic Frobenius acts by
   $2\varepsilon$ on this line and by $\varepsilon$ on the quotient.
5. Its Artin conductor exponent at $2$ is one.
6. Every globally stable lattice $T$ has the saturated special line (5.2) and
   the integral thickness ideal (5.5). Its residual conductor is one exactly
   when that ideal is the unit ideal.

No assertion about residual absolute irreducibility, crystallinity at $3$, or
finite flatness at $3$ is included unless the corresponding conditions in
Section 6.3 have separately been certified. The theorem does not require
$(\mathrm{AI}_2)$; it uses the selected conclusion of Book 185, Theorem 9.1.

**Proof.** Clause 1 and the good-prime part of clause 2 follow from the selected input (or its
optional display in (2.1)), the common pure polynomials, and the determinant identity. The final support statement
in clause 2 is exactly $(\mathrm U)$. Because the coefficient characteristic of $V$ is $3$, the base place
$2$ lies in the away-from-coefficient range. Strong local compatibility gives
(4.6). Equations (3.1)--(3.3) then give the nonzero monodromy, the line, and the
sign, while (3.5) gives conductor one. Compactness supplies $T$; intersection
with the rational monodromy line gives the saturated sequence (5.3). Formula
(5.4) is the integral form of nonzero tame monodromy, and reduction gives the
criterion (5.7). No other conclusion is used. $\square$

## 8. The role of the switched member in the endgame

### 8.1 Coefficient-prime integrality

The next integral step fixes the tuple

$$
(E,\nu,K,V,\det V=\chi_3,\{0,1\}\text{ as the target Hodge type})
\tag{8.1}
$$

together with the rational ramification statement and the special line at $2$.
Here the ramification statement is Book 185's Galois auxiliary-comparison theorem, independently
checked by its conductor calculation, and is not a consequence of weak compatibility. Theorem
7.1 does not settle the coefficient-prime problem. Once the comparison certificate
$(\mathrm C_3)$ is proved, Book 187 constructs a global stable lattice with the needed
finite-flat quotient system and keeps that same lattice $T$ throughout. Neither the target Hodge labels in (8.1) nor the rational
representation by itself proves crystallinity or finite flatness at $3$.

Once Book 187 fixes $T$, the local intersection $T\cap L_{2,\nu}$ and the ideal
$\mathfrak c_2(T)$ must be evaluated on that lattice. The rational special record
survives every lattice change; a primitive residual monodromy class does not.

### 8.2 The residual stage

The rational data relevant to the residual stage are

$$
(V,\det V=\chi_3,D_2\otimes_EK,\{P_v\}_{v\notin S\cup\{3\}}),
\tag{8.2}
$$

with the transported SP record and the imported weight-one purity. The all-level finite-flat tower is not
contained in (8.2); Book 187 constructs it for the same $\nu$ and the same named lattice $T$.
For any residual argument, Book 188 may use only checked objects such as

$$
(k,\overline T,\overline L_2,\overline\varepsilon,
\mathfrak c_2(T),\text{ the certified global residual image}).
\tag{8.3}
$$

The signed-special endgame of Book 188 does not require primitive residual monodromy or
residual absolute irreducibility: it permits the residual inertia extension to split and uses
the saturated all-level filtration. If a variant requires residual conductor one, it must see
$\mathfrak c_2(T)=\mathcal O$. If it requires a representation over
$\mathbf F_3$, it must see an $\mathbf F_3$-descent or $k=\mathbf F_3$. If it
requires residual absolute irreducibility, the certificate of Section 6.2 or an exact
replacement must be present. The rational equality $a_2(V)=1$ supplies none of
these three residual assertions by itself.

### 8.3 The classification theorem

Book 161 proves the finite-flat category and classification theorem that Book 188 applies to
the tower produced by Book 187. It does not select the place $\nu$ or the lattice $T$, so those
must already have been fixed here and in Book 187. The later route keeps the
rational facts

$$
\det V=\chi_3,
\qquad
\operatorname{WD}_2(V)^{\mathrm{F\text{-}ss}}
=\operatorname{Sp}_2(\varepsilon),
\qquad
a_2(V)=1.
\tag{8.4}
$$

attached to the single member selected in this book. Applying Book 161 inside Book 188 does not
permit one to replace $\nu$, descend coefficients,
change $T$, or upgrade a split residual local extension to a nonsplit one.

The dependency direction is therefore

$$
\text{Book 186 rational switch}
\longrightarrow
\text{Book 187 named integral lattice}
\longrightarrow
\text{Book 161 category/classification applied in Book 188}
\longrightarrow
\text{Book 188 $\mathcal O$-adic line and contradiction}.
\tag{8.5}
$$

No result of those later books is used to prove Theorem 7.1.

### 8.4 The exact integral requirements

The family-wide spreading theorem produces integral models at every odd coefficient place.
That is a natural strong form of the argument, but the final three-adic proof uses only one
of them. After Theorem 7.1 has selected $\nu\mid3$, the remaining chain uses exactly:

1. one globally stable $\mathcal O_{E_\nu}$-lattice in $V$;
2. compatible finite-flat models for one cofinal coefficient tower (Book 187 constructs all
   $T/\varpi^nT$) at the base prime $3$;
3. $(\mathrm U)$ for this same $V$, so those quotients are finite etale at every odd base
   prime $q\ne3$ and glue over $\mathbf Z[1/2]$; and
4. the determinant and dyadic odd-tame behavior needed by Book 161.

There is no second lattice at another coefficient place in this list. Compactness alone
provides item 1 but not item 2. A single finite-flat residual layer does not provide item 2,
because the integral line in Book 188 is obtained by passing finite-level identities through
a separated cofinal tower. Conversely, no residual irreducibility, residue-degree-one
condition, primitive residual monodromy, or coefficient-place-above-two model is required.
The conductor-one integer is a consequence of the full SP pair; it is not an additional
classification hypothesis.

This also locates the preferred contradiction. Theorem 7.1 already retains absolute
irreducibility of $V$. Once Books 187, 161, and 188 construct a characteristic-zero
cyclotomic line in $V$, the contradiction is immediate. A certified pure good prime gives
an independent trace contradiction, but is not needed on this preferred route.

## 9. Logical boundaries of the prime switch

### 9.1 The decisive local argument

The proof preserves the full pair (2.5), so nonzero monodromy survives the field extension in
(4.6) without being reconstructed from a conductor. Rank-one nilpotence in dimension two gives
$\ker N=\operatorname{im}N$, and relation (2.7) makes this line stable. The line is therefore
defined before a lattice is chosen and survives the coefficient switch intrinsically.

The sign is similarly intrinsic: it is the eigenvalue on the quotient by the monodromy line.
Relation (2.7) and the cyclotomic determinant give the ordered eigenvalues
$(2\varepsilon,\varepsilon)$ and force $\varepsilon^2=1$. Finally, the finite inertial
representation is trivial while $N$ is nonzero, so the correction term in (3.5) is one. A
conductor calculation that discards $N$ would return zero; replacing the special parameter by
a two-dimensional finite inertial type would instead calculate the wrong local object.

### 9.2 Coefficient fields and compatibility

All coefficient enlargements occur before the factorization (4.1), and only then is a place
above three chosen. Consequently the residue degree attached to $\nu$ cannot change later
without changing the notation. There is also no tensor product between the original
$p$-adic completion and $E_\nu$. The bridge is the common algebraic packet datum, and the only
scalar extension used locally is the well-defined pair $D_2\otimes_EE_\nu$.

This local comparison is available because the new coefficient characteristic is three and
the preserved base place is two. It says nothing about the behavior of $V$ at the base place
three. Likewise, unramifiedness of the new member at the old coefficient prime $p$ comes from
the direct local certificate in $(\mathrm U)$, not from the coefficient-prime behavior of the
old $p$-adic member. The global good polynomials recognize a semisimple representation, while
the bad-place pair, including $N$, comes from strong local compatibility. Purity is another
independent input: neither the product of the roots nor $\det V=\chi_3$ proves that each root
has complex absolute value $v^{1/2}$.

### 9.3 What integrality and reduction retain

Compactness guarantees the existence of a stable lattice but does not select the lattice
needed for the coefficient-prime construction or control $c_T$. The rational condition
$c_T\ne0$ allows $c_T\in\mathfrak m$, as the example (5.7a) shows, so residual monodromy can
vanish. The saturated line is more robust: in characteristic three its two Frobenius
eigenvalues remain distinct and retain the orientation even when the residual inertia
extension splits.

Residual image and coefficient descent are separate questions. Compatibility alone implies
neither absolute irreducibility nor adequacy at this fixed place. Nor does containment of
traces in $\mathbf F_3$ automatically give a two-dimensional $\mathbf F_3$-model. Residue
degree one does imply $k=\mathbf F_3$, but $K=\mathbf Q_3$ additionally requires ramification
index one.

### 9.4 Chronology of the proof

Theorem 7.1 uses the controlled SP datum through Book 185's away-from-two assembly over its
final coefficient field, the certified pure good polynomials and cyclotomic determinant,
strong local compatibility at two, and the identification of the distinguished dyadic pair as
$\operatorname{Sp}_2(\varepsilon)$. The controlled datum itself includes Book 182,
Proposition 7.1 and Theorem 9.1 through Book 183's selected packet-array theorem; Book 185,
Theorem 9.1 then assembles the selected member. Clean support comes from Book 185,
Proposition 8.3, either through the rational family theorem or through Proposition 9.2.

No later finite-flat theorem, residual classification, or final contradiction enters this
argument, and $(\mathrm{AI}_2)$ is unnecessary because no coefficient-two member is used.
After the prime switch, Book 187 constructs the named integral tower; Book 161 supplies the
category and classification applied by Book 188. This chronological order prevents any later
conclusion from becoming a premise of Theorem 7.1.

## 10. Conclusion

Changing the coefficient prime is therefore a selection, not a scalar extension. The
selected conclusion of Book 185, Theorem 9.1 supplies one actual place $\nu\mid3$ and one
absolutely irreducible member $V=r_\nu$. Its common algebraic local object at the different
base prime $2$ transports the nonzero monodromy, intrinsic line, Frobenius sign, and conductor
one without crossing coefficient topologies. Book 185's proved Galois local complements also
give clean support for this same member at every rational prime outside $\{2,3\}$.

The chapter's final certified object is

$$
\boxed{
V=r_\nu,
\quad
\det V=\chi_3,
\quad
\det(X-V(\operatorname{Frob}_v))=\iota_\nu P_v(X)
\text{ with }P_v\text{ pure of weight one }(v\notin S\cup\{3\}),
\quad
\operatorname{WD}_2(V)^{\mathrm{F\text{-}ss}}
=\operatorname{Sp}_2(\varepsilon),
\quad
L_{2,\nu}=\ker N_{2,\nu},
\quad
a_2(V)=1.
}
\tag{10.1}
$$

Any stable lattice meets the rational monodromy line in a saturated rank-one module. For a
named lattice $T$, the additional local integral data are

$$
\boxed{
T_2^+=T\cap L_{2,\nu},
\quad
\overline L_2\subset T/\mathfrak mT,
\quad
\mathfrak c_2(T),
\quad
a_2(T/\mathfrak mT)=1
\Longleftrightarrow
\mathfrak c_2(T)=\mathcal O.
}
\tag{10.2}
$$

Book 187 will choose the lattice that carries the all-level finite-flat tower at $3$ and will
recompute these integral data on that lattice. The final argument needs no member above the
coefficient prime $2$, no family-wide collection of integral models, no residual
irreducibility, and no primitive residual monodromy. It uses the characteristic-zero absolute
irreducibility already present in $V$, the clean support of this one member, and the tower
constructed for this one place $\nu$.
