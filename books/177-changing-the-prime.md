# Changing the Coefficient Prime while Keeping the Frey Special Place

## 1. Scope

This chapter performs one operation. Starting with the rank-two compatible family that
contains the distinguished Frey lift, it selects a member of coefficient characteristic
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
$3$-adic Hodge theory, or a classification of finite-flat group schemes. Those are
dependency boundaries. The final sections state exactly what is handed to Books
190, 180, and 181.

Throughout, Frobenius is arithmetic and
$\chi_q(\operatorname{Frob}_v)=v$ for $v\ne q$.

## 2. Input contract

Let $p\ge5$ be the coefficient characteristic of the distinguished Frey lift. The
input consists of the following already-proved data.

### 2.1 The family and its coefficient field

There is a number field $E$, a place $\lambda_p\mid p$, and a family

$$
\mathcal R=\{r_\lambda:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(E_\lambda)\}_\lambda
\tag{2.1}
$$

of continuous semisimple rank-two representations. The member $r_{\lambda_p}$
is the distinguished Frey lift after a stated common scalar extension. Every
coefficient enlargement needed to define the family and its local parameters has
already been made. In particular, $E$ in (2.1) is the final coefficient field,
not a temporary trace field.

For every rational prime $v$ outside the declared bad set, there is a polynomial

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

The determinant in (2.4) fixes an unramified quadratic character $\eta$ and a
sign

$$
\eta^2=1,
\qquad \varepsilon=\eta(\phi_2)\in\{\pm1\}.
\tag{2.8}
$$

The word *sign* in this chapter means exactly (2.8). It is the Frobenius
eigenvalue on the one-dimensional quotient by the monodromy line. No root-number
convention is being smuggled into the notation.

The input is the full pair (2.5), not merely a local Euler factor or a conductor
integer. Weak compatibility alone is insufficient for this chapter.

### 2.3 Ramification away from two

For the minimal FLT family under discussion, the common away-from-coefficient
local pair at every $v\ne2$ is unramified. Consequently a member of coefficient
characteristic $q$ is unramified outside $\{2,q\}$. This is an input about the
assembled family. In particular, removal of the old coefficient prime $p$ is not
deduced from its role in the original member; it is certified by the common local
pair at $p$ as read by every member of coefficient characteristic different from
$p$.

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

This is selection from (2.1), not scalar extension of
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

For every $v\ne2,3$, the family input gives

$$
V\text{ is unramified at }v,
\qquad
\det\!\left(X-V(\operatorname{Frob}_v)\right)
=X^2-\iota_\nu(a_v)X+v.
\tag{4.4}
$$

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
$3$ require the separate certificate assigned to Book 190.

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

Book 190 may need to replace $T$ in order to obtain its coefficient-prime
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

If no such image calculation or imported theorem is available, the honest output
of this chapter is “residual image unchecked.” That status does not obstruct the
rational prime switch, but it may obstruct a later residual argument.

### 6.3 The admissible-place ledger

For each $\nu\mid3$, record the following without conflation:

| item | required evidence |
|---|---|
| $K$ and $k$ | factorization of $3\mathcal O_E$ |
| existence of $V=r_\nu$ | the actual family (2.1) |
| special record at $2$ | strong compatibility (4.6) |
| residual representation | a named stable lattice |
| absolute irreducibility or image | a direct calculation or an exact imported theorem |
| residual conductor at $2$ | the ideal $\mathfrak c_2(T)$ |
| crystalline/Hodge behavior at $3$ | coefficient-prime comparison |
| finite-flat quotients at $3$ | an integral lattice theorem |

Selecting $\nu$ means selecting one row of actual local data satisfying every
condition required downstream. It does not mean choosing the rational prime $3$
and assuming that all places above it behave alike.

## 7. Prime-switch theorem

**Theorem 7.1 (Frey special record at coefficient prime three).** Assume the input
contract of Section 2, and choose a place $\nu\mid3$ of the final coefficient
field. Let $V=r_\nu$.

Then:

1. $V$ is an actual two-dimensional $E_\nu$-representation with
   $\det V=\chi_3$; it is not obtained by tensoring the original $p$-adic member
   with $E_\nu$.
2. It has the common Frobenius polynomials and is unramified outside
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
finite flatness at $3$ is included unless the corresponding entries in the
ledger of Section 6.3 have separately been certified.

**Proof.** Clauses 1 and 2 follow from selection of the member in (2.1), the
common polynomials, the common unramified local pairs, and the determinant
identity. Because the coefficient characteristic of $V$ is $3$, the base place
$2$ lies in the away-from-coefficient range. Strong local compatibility gives
(4.6). Equations (3.1)--(3.3) then give the nonzero monodromy, the line, and the
sign, while (3.5) gives conductor one. Compactness supplies $T$; intersection
with the rational monodromy line gives the saturated sequence (5.3). Formula
(5.4) is the integral form of nonzero tame monodromy, and reduction gives the
criterion (5.7). No other conclusion is used. $\square$

## 8. Handoff to Books 190, 180, and 181

### 8.1 Book 190: coefficient-prime integrality

Book 190 receives

$$
(E,\nu,K,V,\det V=\chi_3,\{0,1\}\text{ as the target Hodge type})
\tag{8.1}
$$

together with the rational ramification statement and the special line at $2$.
Its task is separate from Theorem 7.1: prove the required coefficient-prime
comparison at $3$, construct or identify a global stable lattice with the needed
finite-flat quotient system, and return that same named lattice $T$.

Once Book 190 fixes $T$, the local intersection $T\cap L_{2,\nu}$ and the ideal
$\mathfrak c_2(T)$ must be evaluated on that lattice. The rational special record
survives every lattice change; a primitive residual monodromy class does not.

### 8.2 Book 180: the residual input

Book 180 may use only the following checked objects:

$$
(k,\overline T,\overline L_2,\overline\varepsilon,
\mathfrak c_2(T),\text{ the certified global residual image}).
\tag{8.2}
$$

If its theorem requires residual conductor one, it must see
$\mathfrak c_2(T)=\mathcal O$. If it requires a representation over
$\mathbf F_3$, it must see an $\mathbf F_3$-descent or $k=\mathbf F_3$. If it
requires absolute irreducibility, the certificate of Section 6.2 or an exact
replacement must be present. The rational equality $a_2(V)=1$ supplies none of
these three residual assertions by itself.

### 8.3 Book 181: no change of object

Book 181 receives the output of Book 180 for the same place $\nu$ and the same
lattice $T$ returned by Book 190. It may combine that output with the rational
facts

$$
\det V=\chi_3,
\qquad
\operatorname{WD}_2(V)^{\mathrm{F\text{-}ss}}
=\operatorname{Sp}_2(\varepsilon),
\qquad
a_2(V)=1.
\tag{8.3}
$$

It may not silently replace $\nu$, descend coefficients, change $T$, or upgrade
a split residual local extension to a nonsplit one. Any such change requires a
new comparison.

The dependency direction is therefore

$$
\text{Book 177 rational switch}
\longrightarrow
\text{Book 190 named integral lattice}
\longrightarrow
\text{Book 180 checked residual input}
\longrightarrow
\text{Book 181 final use}.
\tag{8.4}
$$

No result of those later books is used to prove Theorem 7.1.

## 9. Hostile proof and dependency audit

### 9.1 Local mathematics

**Nonzero monodromy.** The proof imports the full pair (2.5). Nonvanishing is
preserved by field extension in (4.6); it is never inferred from the conductor.

**Invariant line.** Rank-one nilpotence in dimension two proves
$\ker N=\operatorname{im}N$. Relation (2.7) proves stability. The line is defined
before choosing a lattice and therefore survives the coefficient switch.

**Sign.** The sign is defined on the quotient. Relation (2.7) and cyclotomic
determinant give eigenvalues $(2\varepsilon,\varepsilon)$ and force
$\varepsilon^2=1$. This avoids an unrecorded sign convention.

**Conductor.** The finite inertial representation is trivial but $N$ is not.
The correction term in (3.5) is one. Any calculation returning zero has dropped
$N$; any calculation returning two has replaced the special parameter by a
two-dimensional finite inertial type.

### 9.2 Coefficients and compatibility

**Final coefficient field first.** All enlargements occur before (4.1). A place
above $3$ is selected only in the final $E$, so residue degrees are not changed
behind the notation.

**No cross-completion tensor product.** The bridge is the algebraic family. The
only scalar extension at $2$ is $D_2\otimes_EE_\nu$, which is defined.

**Correct compatibility range.** The new coefficient characteristic is $3$ and
the preserved base place is $2$, so (4.6) lies strictly away from the coefficient
prime. Nothing in that statement addresses the base place $3$.

**Old coefficient prime.** Unramifiedness at $p$ comes from the common local
record at $p$ for the new member, not from the old $p$-adic member's
coefficient-prime behavior.

**Global versus local recognition.** Good Frobenius polynomials recognize the
global semisimplification. The bad-place pair, including $N$, comes from the
stated strong local compatibility. The two arguments are not interchanged.

### 9.3 Integral and residual boundaries

**Existence is not selection.** Compactness gives some stable lattice. It does
not choose the lattice needed by Book 190 and does not control $c_T$.

**Rational nonzero is not residual nonzero.** The element $c_T$ is nonzero in
$\mathcal O$ but may lie in $\mathfrak m$. Formula (5.7) records both cases.

**The line survives more robustly than the extension.** The saturated reduction
$\overline L_2$ is oriented by two distinct Frobenius eigenvalues in
characteristic $3$, while the inertia extension can split.

**Residual image is separate.** No large-image, adequacy, or absolute
irreducibility claim is extracted from compatibility. A fixed place above $3$
is checked directly.

**Coefficient descent is separate.** Trace containment alone does not give a
two-dimensional $\mathbf F_3$-model. Residue degree one does give
$k=\mathbf F_3$, but it does not give $K=\mathbf Q_3$ unless the ramification
index is also one.

### 9.4 Dependency boundary

Theorem 7.1 imports only:

- the already-assembled family over its final coefficient field;
- common good polynomials and determinant;
- common unramified local pairs away from $2$;
- full strong local compatibility at $2$; and
- identification of the distinguished member's dyadic pair as
  $\operatorname{Sp}_2(\varepsilon)$.

It does not import a later finite-flat theorem, residual classification, or final
FLT contradiction. Books 190, 180, and 181 receive outputs in that order and do
not feed assumptions backward into the proof.

## 10. Mechanical audit

The theorem has one coefficient prime $\nu\mid3$, one distinguished base place
$2$, and one local shape. All equations use the arithmetic-Frobenius convention.
Every occurrence of a residual representation is attached either to a named
lattice or explicitly marked as a semisimplification. Every claim at the base
place $3$ is deferred to a coefficient-prime certificate. Every conductor claim
states whether it is rational or residual.

The chapter's final certified object is

$$
\boxed{
V=r_\nu,
\quad
\det V=\chi_3,
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

For a named lattice $T$, the additional certified local integral data are

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

These are precisely the rational and integral facts that may cross the handoff.
