# Hardly Ramified $3$-adic Representations

## Contents

1. [The signed-special endgame](#1-the-signed-special-endgame)
   - [The purpose and boundary of the theorem](#11-the-purpose-and-boundary-of-the-theorem)
   - [The exact input](#12-the-exact-input)
   - [The reusable theorem](#13-the-reusable-theorem)
   - [What is conditional upstream](#14-what-is-conditional-upstream)
2. [The local signed-special calculation](#2-the-local-signed-special-calculation)
   - [Nonzero monodromy and the intrinsic line](#21-nonzero-monodromy-and-the-intrinsic-line)
   - [The saturated integral filtration](#22-the-saturated-integral-filtration)
   - [Every finite coefficient level](#23-every-finite-coefficient-level)
   - [Exponent-three subquotients](#24-exponent-three-subquotients)
3. [Finite-flat devissage and torsion fields](#3-finite-flat-devissage-and-torsion-fields)
   - [The modeled levels](#31-the-modeled-levels)
   - [Simple factors have exponent three](#32-simple-factors-have-exponent-three)
   - [The field cut out by an exponent-three factor](#33-the-field-cut-out-by-an-exponent-three-factor)
   - [Why the full tower is different](#34-why-the-full-tower-is-different)
4. [The exact root-discriminant ceiling](#4-the-exact-root-discriminant-ceiling)
   - [The contribution at three](#41-the-contribution-at-three)
   - [The contribution at two](#42-the-contribution-at-two)
   - [The global inequality and its numerical certificate](#43-the-global-inequality-and-its-numerical-certificate)
   - [The finite-image consequence](#44-the-finite-image-consequence)
5. [The class-field calculation](#5-the-class-field-calculation)
   - [Abelian subfields over the rationals](#51-abelian-subfields-over-the-rationals)
   - [The quadratic field and its ray groups](#52-the-quadratic-field-and-its-ray-groups)
   - [Solvability and the commutator](#53-solvability-and-the-commutator)
   - [The two simple factors](#54-the-two-simple-factors)
6. [Extensions and the ordered filtration](#6-extensions-and-the-ordered-filtration)
   - [The extension convention](#61-the-extension-convention)
   - [Pure extensions](#62-pure-extensions)
   - [The surviving Kummer direction](#63-the-surviving-kummer-direction)
   - [Vanishing in the reverse direction](#64-vanishing-in-the-reverse-direction)
   - [Sorting a composition series](#65-sorting-a-composition-series)
7. [The finite-coefficient identity](#7-the-finite-coefficient-identity)
   - [The canonical augmentation submodule](#71-the-canonical-augmentation-submodule)
   - [The cross relation](#72-the-cross-relation)
   - [Cayley--Hamilton and trace](#73-cayley--hamilton-and-trace)
   - [The residual orientation](#74-the-residual-orientation)
8. [The integral cyclotomic line](#8-the-integral-cyclotomic-line)
   - [Separated passage through all levels](#81-separated-passage-through-all-levels)
   - [Rank and saturation](#82-rank-and-saturation)
   - [The signed-special reducibility theorem](#83-the-signed-special-reducibility-theorem)
   - [Comparison with the local SP line](#84-comparison-with-the-local-sp-line)
9. [The certified Frobenius contradiction](#9-the-certified-frobenius-contradiction)
   - [One certified good prime](#91-one-certified-good-prime)
   - [Transport to the algebraic coefficient field](#92-transport-to-the-algebraic-coefficient-field)
   - [Purity](#93-purity)
   - [The Frey endpoint](#94-the-frey-endpoint)
10. [Dependencies, hostile audit, and readiness](#10-dependencies-hostile-audit-and-readiness)
    - [Direct dependencies](#101-direct-dependencies)
    - [Exact upstream blockers](#102-exact-upstream-blockers)
    - [Hostile audit](#103-hostile-audit)
    - [Conclusion](#104-conclusion)

## 1. The signed-special endgame

### 1.1 The purpose and boundary of the theorem

The final three-adic step in the Frey argument starts after the compatible family and its
integral lattice have been constructed. It must not reconstruct either object. Its task is to
consume one precise all-level tower and show that the corresponding characteristic-zero
representation is reducible.

The dyadic member is on the signed-special, or **SP**, branch. Its Weil--Deligne monodromy
operator is nonzero of rank one. The associated adic representation has a unique inertia-fixed
line and nontrivial unipotent tame inertia. Thus the SP branch has conductor exponent one. It is
not a finite cubic inertial type, it does not have monodromy zero, and it does not have conductor
exponent two.

At the coefficient prime, this book uses only the integral output already isolated by Book 187:
every actual coefficient quotient of one globally stable lattice has a compatible
coefficient-linear finite-flat model over $\mathbf Z_3$, and, under clean support, those models
glue over $\mathbf Z[1/2]$. Rational crystallinity is the source of that output in Book 187, but
it is not reproved or used as a substitute for the tower here.

The proof has four stages:

$$
\begin{array}{c}
\text{SP square-zero inertia on exponent-three subquotients}
\\ \Downarrow
\operatorname{rd}<3^{3/2}2^{2/3}\text{ and degree at most }20
\\ \Downarrow
\text{constant and multiplicative simple factors, with ordered extensions}
\\ \Downarrow
0\to\mathcal O(1)\to T\to\mathcal O\to0.
\end{array}
\tag{1.1}
$$

The last sequence gives a trace identity at every good Frobenius. A prime is used only when
Book 185 certifies both its common algebraic polynomial and weight-one purity. There is no need
to name the prime $5$.

### 1.2 The exact input

Let $K/\mathbf Q_3$ be finite, let $\mathcal O$ be its ring of integers, choose a uniformizer
$\varpi$, and put

$$
k=\mathcal O/\varpi\mathcal O,
\qquad
A_n=\mathcal O/\varpi^n\mathcal O.
\tag{1.2}
$$

Let

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_{\mathcal O}(T)
\tag{1.3}
$$

be continuous, where $T$ is free of rank two over $\mathcal O$, and put

$$
V=T\otimes_{\mathcal O}K,
\qquad
T_n=T/\varpi^nT.
\tag{1.4}
$$

The **Schoof-ready signed-special package** consists of the following data.

1. The determinant is exactly cyclotomic:
   $$
   \det\rho=\chi_3.
   \tag{1.5}
   $$
2. For every $n\ge1$, there is a finite locally free commutative group
   $$
   \mathcal G_n/\mathbf Z[1/2]
   \tag{1.6}
   $$
   of $3$-power order, with an $A_n$-action and a marking
   $$
   \mathcal G_n(\overline{\mathbf Q})\simeq T_n
   \tag{1.7}
   $$
   compatible with Galois and coefficients. The coefficient reductions and the exact
   multiplication sequences are modeled by the supplied tower.
3. At $2$, the rational member has the signed-special pair
   $$
   (r_2,N_2),
   \qquad
   N_2^2=0,
   \quad N_2\ne0,
   \quad\operatorname{rank}N_2=1,
   \tag{1.8}
   $$
   with trivial finite Weil inertia and
   $$
   r_2(F_2)N_2r_2(F_2)^{-1}=2N_2.
   \tag{1.9}
   $$
   If
   $$
   \mathscr L_2=\ker N_2=\operatorname{im}N_2,
   \tag{1.10}
   $$
   arithmetic Frobenius acts on $V/\mathscr L_2$ by a sign
   $\varepsilon_2\in\{1,-1\}$ and on $\mathscr L_2$ by $2\varepsilon_2$.

The existence of (1.6) already records clean support at every odd prime other than $3$.
Indeed a finite locally free $3$-primary group over $\mathbf Z_q$, for $q\ne3$, is finite
etale, so its generic module is unramified. No stronger support assertion will be inferred from
weak compatibility.

For the final numerical contradiction, add a separate **certified good-prime record**. It
consists of a number field $E$, an embedding $\iota_\nu:E\hookrightarrow K$, and a prime
$q\ne2,3$ for which

$$
P_q(X)=X^2-a_qX+q\in E[X]
\tag{1.11}
$$

is the characteristic polynomial of $\rho(\operatorname{Frob}_q)$ after applying
$\iota_\nu$, and every root of $P_q$ has complex absolute value $\sqrt q$ under every
complex embedding. Book 185 supplies such records for every $q$ outside its finite certified
exceptional set. Book 187's clean-support certificate is stronger: it is needed for (1.6), not
merely for choosing one $q$.

### 1.3 The reusable theorem

**Theorem 1.1 (signed-special hardly ramified three-adic endgame).** Assume the
Schoof-ready signed-special package of Section 1.2. Then there is a saturated
$G_{\mathbf Q}$-stable exact sequence

$$
\boxed{
0\longrightarrow\mathcal O(1)
\longrightarrow T
\longrightarrow\mathcal O
\longrightarrow0.
}
\tag{1.12}
$$

Consequently

$$
\boxed{
V^{\mathrm{ss}}\simeq K(1)\oplus K,
\qquad
\operatorname{tr}\rho(g)=1+\chi_3(g)
\quad(g\in G_{\mathbf Q}).
}
\tag{1.13}
$$

If $V$ is absolutely irreducible, (1.12) is already a contradiction. If instead the
certified good-prime record is supplied, then

$$
a_q=1+q,
\qquad
1+q\le2\sqrt q,
\tag{1.14}
$$

which is impossible because

$$
1+q-2\sqrt q=(\sqrt q-1)^2>0.
\tag{1.15}
$$

The theorem is reusable because its conclusion uses neither the provenance of the family nor a
preferred lattice construction. It needs the actual tower (1.6), the exact determinant, and the
SP local record. It does not need a residual nonzero-monodromy assertion for the chosen lattice.

### 1.4 What is conditional upstream

Book 185, Theorem 9.1, conditionally supplies the actual compatible family, the cyclotomic
determinant, the pure polynomials outside a finite set, and the rational SP pair (1.8)--(1.10).
It does not supply a lattice or coefficient-prime finite flatness.

Book 187, Theorem 10.2, conditionally supplies (1.6)--(1.7). Its hypotheses include both the
coefficient-prime certificate $(\mathrm C_3)$ and the clean-support certificate $(\mathrm U)$.
This book consumes that theorem exactly as stated. It does not assert that either certificate
has already been proved.

Thus Theorem 1.1 is a complete conditional implication. The unconditional FLT chain remains
blocked upstream of its antecedent. The distinction will be recorded again in Section 10.2.

## 2. The local signed-special calculation

### 2.1 Nonzero monodromy and the intrinsic line

Let $D_2$ be a decomposition group at $2$. The pair (1.8)--(1.10) corresponds to an
unramified character

$$
\eta_2:D_2\longrightarrow\{1,-1\},
\qquad
\eta_2(F_2)=\varepsilon_2,
\tag{2.1}
$$

and an exact sequence

$$
0\longrightarrow K(1)\otimes\eta_2
\longrightarrow V|_{D_2}
\longrightarrow K\otimes\eta_2
\longrightarrow0.
\tag{2.2}
$$

The first line is the $K$-line $\mathscr L_2$ from the base-changed algebraic local pair. The
extension is nonsplit on inertia because $N_2\ne0$. Wild inertia is trivial, while tame inertia
acts unipotently. In particular

$$
\dim_KV^{I_2}=1,
\qquad
a_2(V)=2-1=1.
\tag{2.3}
$$

Equation (2.3) is a consequence, not the definition, of the SP branch. A conductor integer alone
would forget the line, the sign, and the nonzero monodromy.

The line in (2.2) is intrinsic. If a two-dimensional unipotent representation has nonzero
rank-one monodromy, then

$$
\ker N_2=\operatorname{im}N_2=V^{I_2}.
\tag{2.4}
$$

No second inertia-fixed line exists. This uniqueness will be used only after the global line has
been constructed.

### 2.2 The saturated integral filtration

Intersect the rational SP line with the already chosen global lattice:

$$
T_2^+=T\cap\mathscr L_2,
\qquad
T_2^-=T/T_2^+.
\tag{2.5}
$$

The intersection is a rank-one $\mathcal O$-lattice. It is saturated: if
$\varpi x\in T_2^+$ with $x\in T$, then $x$ belongs to the $K$-line $\mathscr L_2$, hence to
$T_2^+$. Therefore $T_2^-$ is torsion free of rank one and thus free. After choosing generators,

$$
0\longrightarrow\mathcal O(1)\otimes\eta_2
\longrightarrow T|_{D_2}
\longrightarrow\mathcal O\otimes\eta_2
\longrightarrow0
\tag{2.6}
$$

is exact.

Choose a normalized $3$-primary tame character

$$
t_3:I_2\twoheadrightarrow\mathbf Z_3.
\tag{2.7}
$$

In a basis adapted to (2.6), inertia acts as

$$
\rho(\sigma)=
\begin{pmatrix}
1&\alpha t_3(\sigma)\\
0&1
\end{pmatrix},
\qquad
\alpha\in\mathcal O\setminus\{0\}.
\tag{2.8}
$$

The coefficient $\alpha$ is integral because $T$ is stable, and it is nonzero because the
rational monodromy is nonzero. Its valuation can be positive. Therefore rational nonzero
monodromy need not remain nonzero in $T/\varpi T$.

### 2.3 Every finite coefficient level

Because the quotient in (2.6) is free, reduction modulo $\varpi^n$ remains exact:

$$
0\longrightarrow A_n(1)\otimes\eta_2
\longrightarrow T_n|_{D_2}
\longrightarrow A_n\otimes\eta_2
\longrightarrow0.
\tag{2.9}
$$

Both endpoint characters are trivial on inertia: $\eta_2$ is unramified, and the $3$-adic
cyclotomic character is unramified at $2$. Hence, for every $\sigma\in I_2$,

$$
(\rho_n(\sigma)-1)T_n
\subset A_n(1)\otimes\eta_2,
\qquad
(\rho_n(\sigma)-1)(A_n(1)\otimes\eta_2)=0.
\tag{2.10}
$$

Thus

$$
\boxed{(\rho_n(\sigma)-1)^2=0.}
\tag{2.11}
$$

Formula (2.8) gives the exact inertia size. If $e=v_\varpi(3)$ and
$s=v_\varpi(\alpha)$, its image on $T_n$ is cyclic of order

$$
3^{\max\{0,\lceil(n-s)/e\rceil\}}.
\tag{2.12}
$$

The image can therefore grow through the tower. The universal conclusion is that it is a cyclic
$3$-group, hence odd, and that (2.11) holds. No all-level order-three claim is made.

### 2.4 Exponent-three subquotients

Let $W$ be a subquotient of some $T_n$ which is killed by $3$. Saturated schematic closure and
represented quotient inside $\mathcal G_n$ give $W$ an actual finite-flat model over
$\mathbf Z[1/2]$. Relation (2.11) descends to $W$.

Write $u=\rho_W(\sigma)-1$. Then $u^2=0$, and in characteristic three

$$
(1+u)^3=1+3u+3u^2+u^3=1.
\tag{2.13}
$$

Tame inertia is procyclic. Hence its image on $W$ is either trivial or cyclic of order $3$.
Wild inertia is already trivial. We have proved the precise local statement used in every
residual discriminant calculation:

$$
\boxed{
W[3]=W
\quad\Longrightarrow\quad
\operatorname{im}(I_2\mid W)\in\{1,C_3\}.
}
\tag{2.14}
$$

This is where the SP filtration enters the classification. Characteristic-zero monodromy stays
nonzero, but a particular exponent-three subquotient is allowed to have trivial inertia.

## 3. Finite-flat devissage and torsion fields

### 3.1 The modeled levels

Put $R=\mathbf Z[1/2]$. Each $\mathcal G_n/R$ is already supplied; this book does not glue it.
The relevant exact operations are performed inside these supplied middle objects.

If $W'\subset T_n$ is stable, its saturated schematic closure in $\mathcal G_n$ is finite
locally free. The represented quotient is finite locally free as well. Coefficient endomorphisms
preserving $W'$ preserve its closure. Thus a composition series of the finite generic module can
be realized as a composition series of finite-flat group schemes.

The direction is important. We start with a finite-flat middle object and take its subobjects and
quotients. We never infer that an arbitrary generic extension is finite flat merely because its
two endpoints possess models.

At every odd $q\ne3$, a finite locally free group of $3$-power order over $\mathbf Z_q$ is
finite etale. Hence every generic subquotient is unramified at $q$. At $3$, the closure retains
an actual finite-flat model over $\mathbf Z_3$. At $2$, Section 2.4 controls the generic inertia.

### 3.2 Simple factors have exponent three

Let $S$ be a nonzero simple factor occurring in a composition series of some $\mathcal G_n$.
The generic group $S(\overline{\mathbf Q})$ is a nonzero finite abelian $3$-group. Its subgroup
killed by $3$ is nonzero. Saturated closure gives a nonzero subobject of $S$, so simplicity makes
it all of $S$. Therefore

$$
[3]_S=0.
\tag{3.1}
$$

The generic points of $S$ form an irreducible finite-dimensional $\mathbf F_3$-representation.
By Section 2.4 its inertia at $2$ is trivial or cyclic of order three. This reduction to exponent
three is the legitimate fixed-base return in Fontaine's argument.

### 3.3 The field cut out by an exponent-three factor

Let $W$ be any modeled exponent-three subquotient and define

$$
L=\mathbf Q(W)
=\overline{\mathbf Q}^{\ker(G_{\mathbf Q}\to\operatorname{Aut}_{\mathbf F_3}(W))}.
\tag{3.2}
$$

Then $L/\mathbf Q$ is finite Galois, and

$$
\operatorname{Gal}(L/\mathbf Q)
\simeq\operatorname{im}(G_{\mathbf Q}\mid W).
\tag{3.3}
$$

It is unramified outside $\{2,3\}$. Its local representation at $3$ has an actual finite-flat
model over $\mathbf Z_3$. At $2$, inertia has order $1$ or $3$. These are all the inputs of the
two-prime field bound in Books 158--159.

The same statement applies to a finite direct sum of modeled exponent-three subquotients. The
product of their models is finite flat at $3$. Since tame inertia is procyclic and every summand
has exponent-three image, the image on the direct sum still has order at most three. Therefore a
finite compositum of their cutout fields pays the dyadic cost only once.

### 3.4 Why the full tower is different

If

$$
e_{\mathcal O}=v_\varpi(3),
\qquad
m(n)=\left\lceil\frac n{e_{\mathcal O}}\right\rceil,
\tag{3.4}
$$

then $T_n$ is killed by $3^{m(n)}$, not generally by $3^n$. The finite-flat root-discriminant
bound at level $n$ contains the factor

$$
3^{m(n)+1/2},
\tag{3.5}
$$

before the dyadic contribution. It grows with $n$.

This growth is necessary. The cyclotomic quotients $\mu_{3^n}$ are finite flat at every level,
while the root discriminants of $\mathbf Q(\zeta_{3^n})$ grow. Uniform bounds on successive
matrix-kernel orders do not control ramification depth. Consequently the degree-$20$ cutoff below
is applied only to modeled modules killed by $3$ and their finite products, never to the full
$\varpi^n$-torsion field.

## 4. The exact root-discriminant ceiling

### 4.1 The contribution at three

Let $L_3/\mathbf Q_3$ be the local field cut out by $W$. Since $W$ is killed by $3$ and has an
actual finite-flat model over $\mathbf Z_3$, the finite-flat ramification theorem of Book 158
gives

$$
G_{\mathbf Q_3}^u\text{ acts trivially on }W
\qquad(u>1/2).
\tag{4.1}
$$

Let $e_3$ be the local ramification index and $d_3$ the different exponent. The upper-numbering
form of Hilbert's formula gives

$$
\frac{d_3}{e_3}
=1-\frac1{e_3}
+\int_0^\infty
\left(1-\frac1{|G^u|}\right)du.
\tag{4.2}
$$

The integral is supported in an interval of length at most $1/2$ and its integrand is at most
one. Therefore

$$
\boxed{\frac{d_3}{e_3}<1+\frac12=\frac32.}
\tag{4.3}
$$

The strict inequality comes from $1-1/e_3<1$. It does not assert that a break at $1/2$ is
forbidden; an endpoint has measure zero in (4.2).

### 4.2 The contribution at two

If the inertia image at $2$ is trivial, then $d_2/e_2=0$. If it has order three, the extension
is tame and

$$
e_2=3,
\qquad
d_2=e_2-1=2,
\qquad
\boxed{\frac{d_2}{e_2}=\frac23.}
\tag{4.4}
$$

An unramified residue extension changes neither $e_2$ nor $d_2/e_2$. The exponent is not
multiplied by the dimension of $W$ or by the number of primes above $2$. After taking the
absolute degree root, the local normalized ratio is exactly the exponent of $2$.

### 4.3 The global inequality and its numerical certificate

Because $L/\mathbf Q$ is Galois and ramified only at $2$ and $3$,

$$
\operatorname{rd}(L)
=2^{d_2/e_2}3^{d_3/e_3}.
\tag{4.5}
$$

Equations (4.3)--(4.4) give

$$
\boxed{
\operatorname{rd}(L)<3^{3/2}2^{2/3}
=8.248377821991616\ldots .
}
\tag{4.6}
$$

When dyadic inertia is trivial, the factor $2^{2/3}$ is omitted; using (4.6) remains a valid
uniform upper bound.

Book 159 certifies the matching unconditional Odlyzko--Poitou inequality. With support parameter
$6$, it proves for every number field of degree $d$

$$
\log\operatorname{rd}(L)>
\gamma+\log(8\pi)-\frac{12}{d}-1.10356.
\tag{4.7}
$$

At $d=21$, the right side satisfies

$$
\gamma+\log(8\pi)-\frac{12}{21}-1.10356
>2.126398521002197,
\tag{4.8}
$$

whereas

$$
\log(3^{3/2}2^{2/3})
<2.110016553375462.
\tag{4.9}
$$

The lower bound in (4.7) increases with $d$. Hence (4.6) and (4.7) are incompatible for every
$d\ge21$.

### 4.4 The finite-image consequence

We have proved the exact finite-image statement used below.

**Proposition 4.1 (two-prime exponent-three cutoff).** Every modeled exponent-three subquotient
$W$ of the SP tower satisfies

$$
\boxed{
[\mathbf Q(W):\mathbf Q]
=|\operatorname{im}(G_{\mathbf Q}\mid W)|
\le20.
}
\tag{4.10}
$$

The same degree bound holds for every finite compositum of fields cut out by a finite collection
of such subquotients.

The proposition does not say that the field is abelian or that the representation splits. The
field

$$
\mathbf Q(\zeta_3,\sqrt[3]{2})
\tag{4.11}
$$

has degree six and satisfies the same local restrictions. It is the genuine nonsplit Kummer
example that the later extension calculation must retain.

## 5. The class-field calculation

### 5.1 Abelian subfields over the rationals

Let $L=\mathbf Q(W)$ as above and let $A/\mathbf Q$ be an abelian subextension. At $2$, tame
inertia in an abelian quotient is trivial. Indeed, if $\tau$ is a tame generator and $F_2$ is
arithmetic Frobenius, then

$$
F_2\tau F_2^{-1}=\tau^2.
\tag{5.1}
$$

In an abelian quotient (5.1) gives $\tau=\tau^2$, hence $\tau=1$.

At $3$, upper breaks pass to quotients, so every positive upper break of $A/\mathbf Q$ is at
most $1/2$. Hasse--Arf says that the breaks of an abelian extension are integers. There is
therefore no positive break. The remaining tame inertia has order dividing
$|\mathbf F_3^\times|=2$.

Let $I_3$ be the inertia subgroup in $\operatorname{Gal}(A/\mathbf Q)$. Its fixed field is
unramified at every finite prime: there is no ramification at $2$, all ramification at $3$ has
been removed, and no other prime ramifies. Minkowski's discriminant theorem rules out a
nontrivial number field of absolute discriminant one. Thus the fixed field is $\mathbf Q$, and

$$
[A:\mathbf Q]=|I_3|\le2.
\tag{5.2}
$$

The only quadratic field whose fundamental discriminant is supported at $3$ is

$$
K_0=\mathbf Q(\zeta_3)=\mathbf Q(\sqrt{-3}).
\tag{5.3}
$$

Consequently every abelian subfield of $L$ is $\mathbf Q$ or $K_0$.

### 5.2 The quadratic field and its ray groups

The ring of integers of $K_0$ is $\mathbf Z[\zeta_3]$, and its discriminant is $-3$. Its
Minkowski class bound is

$$
\frac{2\sqrt3}{\pi}<2,
\tag{5.4}
$$

so its class number is one.

Let

$$
\lambda=1-\zeta_3
\tag{5.5}
$$

be the unique prime above $3$. For every $m\ge1$,

$$
|(\mathcal O_{K_0}/\lambda^m)^\times|
=2\cdot3^{m-1}.
\tag{5.6}
$$

The global unit $-1$ maps to the nontrivial element of
$(\mathcal O_{K_0}/\lambda)^\times\simeq\mathbf F_3^\times$. Since the ordinary class group is
trivial, the ray exact sequence

$$
\mathcal O_{K_0}^\times
\longrightarrow(\mathcal O_{K_0}/\lambda^m)^\times
\longrightarrow\operatorname{Cl}_{\lambda^m}(K_0)
\longrightarrow\operatorname{Cl}(K_0)
\longrightarrow1
\tag{5.7}
$$

shows that every $\lambda^m$-ray class group is a $3$-group. In particular, there is no
nontrivial prime-to-three abelian extension of $K_0$ ramified only at $\lambda$.

At the prime above $2$, the residue field is $\mathbf F_4$, because $2$ is inert in $K_0$.
Tame abelian inertia there has order dividing $4-1=3$. Hence a prime-to-three abelian quotient
of an extension of $K_0$ satisfying our local conditions is unramified above $2$. Combining this
with (5.7) excludes every nontrivial prime-to-three abelian quotient.

### 5.3 Solvability and the commutator

Let

$$
G=\operatorname{Gal}(L/\mathbf Q).
\tag{5.8}
$$

By Proposition 4.1, $|G|\le20$. Every group of order at most twenty is solvable. For
completeness, an elementary Sylow induction proves this. Prime-power groups are solvable. At the
remaining possible orders $6,10,14,15,18,$ and $20$, a largest Sylow subgroup is normal except
for the possible order-$12$ case. For order $12$, either a Sylow $3$-subgroup is normal or
conjugation on the four Sylow $3$-subgroups maps the group nontrivially into the solvable group
$S_4$; the kernel has smaller order and is solvable by induction. Thus $G$ is solvable.

If $G$ is nontrivial, its abelianization is nontrivial: a nontrivial solvable perfect group would
have a constant derived series and could not reach the identity. Section 5.1 therefore gives

$$
G^{\mathrm{ab}}\simeq C_2.
\tag{5.9}
$$

Put

$$
H=[G,G].
\tag{5.10}
$$

Then $H=\operatorname{Gal}(L/K_0)$ and $|H|=|G|/2\le10$. The maximal abelian quotient of $H$
cuts out an abelian extension of $K_0$. Section 5.2 shows that it has no prime-to-three quotient.
Thus $H^{\mathrm{ab}}$ is a $3$-group.

If $H\ne1$, solvability makes $H^{\mathrm{ab}}$ nontrivial, so $3$ divides $|H|$. With
$|H|\le10$, the possibilities relevant to a nontrivial $3$-primary abelianization are
$3,6,$ and $9$. A group of order six is either cyclic, with abelianization $C_6$, or isomorphic
to $S_3$, with abelianization $C_2$. Neither is possible. Hence

$$
H=1
\quad\text{or}\quad
H\text{ is a }3\text{-group of order }3\text{ or }9.
\tag{5.11}
$$

Now suppose $W$ is simple. A finite $3$-group acting on a nonzero vector space in
characteristic three has a nonzero fixed vector. One proves this by choosing a central element
$z$ of order three, observing that

$$
(z-1)^3=z^3-1=0,
\tag{5.12}
$$

and inducting on the group order. Since $H$ is normal, $W^H$ is $G$-stable. Simplicity gives
$W^H=W$. The action defining $L$ is faithful, so $H=1$.

It follows that the faithful image of a simple $W$ is trivial or $C_2$.

### 5.4 The two simple factors

Over $\mathbf F_3$, the two irreducible characters of $C_2$ are the trivial character and the
mod-$3$ cyclotomic character $\bar\chi_3$. Therefore a simple generic module is
one-dimensional and is isomorphic to

$$
\mathbf F_3
\quad\text{or}\quad
\mathbf F_3(1).
\tag{5.13}
$$

The order-three finite-flat classification over the unramified DVR $\mathbf Z_3$ identifies
their integral models. The trivial generic character has the etale model

$$
C=\underline{\mathbf Z/3\mathbf Z},
\tag{5.14}
$$

and Cartier duality identifies the cyclotomic model as

$$
M=\mu_3.
\tag{5.15}
$$

They are nonisomorphic: their special fibers at $3$ are respectively etale and connected. We
have proved, for every object arising in the SP tower, that its simple factors are exactly $C$
and $M$.

## 6. Extensions and the ordered filtration

### 6.1 The extension convention

Write $\operatorname{Ext}^1(B,A)$ for extensions

$$
0\longrightarrow A\longrightarrow E\longrightarrow B\longrightarrow0
\tag{6.1}
$$

inside the finite-flat category over $R=\mathbf Z[1/2]$ with the local conditions inherited
from the SP tower. The order of the arguments matters. The Kummer extension has multiplicative
subgroup and constant quotient, so it lies in $\operatorname{Ext}^1(C,M)$. The reverse group
$\operatorname{Ext}^1(M,C)$ is the one that must vanish.

### 6.2 Pure extensions

Consider an extension of $C$ by $C$. Over $\mathbf Z_3$, both endpoints are finite etale, and
the middle term is finite etale as a torsor under a finite etale group. Its generic action is
unramified at $3$ and at every other odd prime.

Any Galois action inducing the identity on the named subgroup and quotient has $3$-power image.
A nontrivial quotient of that image would cut out a cyclic cubic extension of $\mathbf Q$
unramified at every odd prime and at most tamely ramified at $2$. Equation (5.1) makes an abelian
tame extension at $2$ unramified. Minkowski then excludes the field. Thus the middle generic
group is constant.

The only extension classes of the underlying cyclic group by itself are generated under Baer
sum by

$$
0\longrightarrow C
\xrightarrow{\ 3\ }
\underline{\mathbf Z/9\mathbf Z}
\longrightarrow C
\longrightarrow0.
\tag{6.2}
$$

Hence

$$
\operatorname{Ext}^1(C,C)\simeq\mathbf Z/3\mathbf Z.
\tag{6.3}
$$

Cartier duality reverses exact sequences and exchanges $C$ and $M$, so

$$
\operatorname{Ext}^1(M,M)\simeq\mathbf Z/3\mathbf Z,
\tag{6.4}
$$

generated by

$$
0\longrightarrow\mu_3
\longrightarrow\mu_9
\xrightarrow{(\cdot)^3}\mu_3
\longrightarrow0.
\tag{6.5}
$$

Inductively, an object all of whose simple factors are $C$ is constant. Dually, an object all of
whose simple factors are $M$ is of multiplicative type.

### 6.3 The surviving Kummer direction

Consider

$$
0\longrightarrow M\longrightarrow E\longrightarrow C\longrightarrow0.
\tag{6.6}
$$

Multiplication by $3$ on $E$ factors through a morphism $C\to M$, which is zero on generic
characters. Hence $E$ is killed by $3$. Pulling (6.6) back along the section
$1\in C(R)$ gives a $\mu_3$-torsor, and conversely that torsor reconstructs the extension.
Since $\operatorname{Pic}(R)=0$, the fppf Kummer sequence gives

$$
\operatorname{Ext}^1(C,M)
\simeq H^1(R,\mu_3)
\simeq R^\times/R^{\times3}.
\tag{6.7}
$$

Now

$$
R^\times=\{\pm2^m:m\in\mathbf Z\},
\tag{6.8}
$$

and $-1$ is a cube. Thus

$$
\boxed{
\operatorname{Ext}^1(C,M)\simeq\mathbf Z/3\mathbf Z[2].
}
\tag{6.9}
$$

The class of $2$ is finite flat at $3$ because $2$ is a $3$-adic unit, and it has tame cubic
inertia at $2$. Its generic splitting field is (4.11). This is why the final integral sequence
need not split.

### 6.4 Vanishing in the reverse direction

Now consider

$$
0\longrightarrow C\longrightarrow E\longrightarrow M\longrightarrow0.
\tag{6.10}
$$

As before, multiplication by $3$ factors through a morphism $M\to C$, which is zero. Thus $E$
is killed by $3$.

First base change to $\mathbf Z_3$. The connected--etale sequence of $E$ has connected part
$E^0$ of rank three. Indeed the image of $E^0$ in the connected quotient $M$ cannot be trivial,
because then the faithfully flat map $E\to M$ would factor through an etale component group.
It is therefore surjective. Its kernel is connected and lies in the etale subgroup $C$, so the
kernel is trivial. Hence

$$
E^0\xrightarrow{\sim}M
\tag{6.11}
$$

and (6.10) splits over $\mathbf Z_3$.

On generic fibers, (6.10) is measured by

$$
H^1(\mathbf Q,\mathbf F_3(-1))
=H^1(\mathbf Q,\mathbf F_3(1)),
\tag{6.12}
$$

because $\bar\chi_3^{-1}=\bar\chi_3$. Ramification outside $\{2,3\}$ and Kummer theory place
the class in

$$
\langle[2],[3]\rangle
\subset\mathbf Q^\times/\mathbf Q^{\times3}.
\tag{6.13}
$$

The two classes remain independent in
$\mathbf Q_3^\times/\mathbf Q_3^{\times3}$. Valuation separates $[3]$ from units. To see that
$[2]$ is nonzero, replace it by $[-2]$ and suppose $-2=x^3$. Then $x\equiv1\pmod3$, so
$x^3\equiv1\pmod9$, whereas $-2\equiv7\pmod9$. Similarly $[4]$ is nonzero because a cube
congruent to $1$ modulo $3$ is $1$ modulo $9$, not $4$. Thus no nonzero power of $[2]$ is
trivial.

The local splitting (6.11) makes the localization of (6.13) zero, so both coefficients vanish.
The generic extension is split. Its global Galois-equivariant section is unique because
$\operatorname{Hom}(M,C)=0$. At $3$, the section supplied by (6.11) has this generic fiber
(the local Hom group also vanishes), and at every other odd prime finite-etale descent extends
the generic section uniquely. These local sections glue over the Dedekind base. Therefore
(6.10) splits globally, and

$$
\boxed{\operatorname{Ext}^1(M,C)=0.}
\tag{6.14}
$$

The complete table is

$$
\begin{array}{c|cc}
\operatorname{Ext}^1(B,A)&B=C&B=M\\
\hline
A=C&\mathbf F_3[\underline{\mathbf Z/9}]&0\\
A=M&\mathbf F_3[E_2]&\mathbf F_3[\mu_9].
\end{array}
\tag{6.15}
$$

### 6.5 Sorting a composition series

Call two adjacent factors an inversion when a constant factor lies below a multiplicative
factor. The corresponding two-step subquotient has the form

$$
0\longrightarrow C\longrightarrow X\longrightarrow M\longrightarrow0.
\tag{6.16}
$$

By (6.14), $X\simeq C\times M$. Replace the lower factor $C$ by the other direct factor $M$,
take its saturated inverse image in the original object, and form the represented quotient. This
exchanges the adjacent factors inside the finite-flat category.

Every exchange lowers the finite inversion number. Repetition therefore terminates and gives an
exact sequence

$$
0\longrightarrow G^{\mathrm m}
\longrightarrow G
\longrightarrow G^{\mathrm c}
\longrightarrow0,
\tag{6.17}
$$

where $G^{\mathrm m}$ is of multiplicative type and $G^{\mathrm c}$ is constant.

The subgroup is canonical. Any morphism from a multiplicative-type object to a constant object
is zero: over $\mathbf Z_3$ its source has connected special fiber and its target is etale, and
generic-fiber faithfulness globalizes the vanishing. Hence every multiplicative subgroup of $G$
lies in $G^{\mathrm m}$. It is the unique maximal multiplicative subgroup, so (6.17) is functorial
for every morphism and every coefficient endomorphism.

## 7. The finite-coefficient identity

### 7.1 The canonical augmentation submodule

Fix $n$ and write

$$
A=A_n,
\qquad
W=T_n,
\qquad
\rho_n:G_{\mathbf Q}\to\operatorname{GL}_A(W).
\tag{7.1}
$$

The object $\mathcal G_n$ carries the full $A$-action, and $W$ is free of rank two over $A$.
The determinant is

$$
\det\rho_n=\chi_3\pmod{\varpi^n}.
\tag{7.2}
$$

Apply (6.17) to $\mathcal G_n$ and define

$$
N_n=\sum_{g\in G_{\mathbf Q}}(\rho_n(g)-1)W.
\tag{7.3}
$$

The sum is a finite $A$-submodule because $W$ is noetherian. The constant quotient in (6.17)
shows that $N_n$ lies in the generic points of the multiplicative block. Galois acts trivially
on $W/N_n$.

On the geometric points of a multiplicative $3$-primary group, Galois acts by the cyclotomic
character. This is clear on $\mu_{3^a}$ and hence on finite products. Therefore

$$
\rho_n(h)x=\chi_3(h)x
\qquad(x\in N_n).
\tag{7.4}
$$

Neither $N_n$ nor $W/N_n$ is asserted to be free at this isolated level.

### 7.2 The cross relation

The image of $\rho_n(g)-1$ lies in $N_n$, and (7.4) identifies the action on that image. Hence

$$
\boxed{
(\rho_n(h)-\chi_3(h))(\rho_n(g)-1)=0
\qquad(g,h\in G_{\mathbf Q}).
}
\tag{7.5}
$$

This relation retains extension data. Knowing only that every simple factor is $C$ or $M$ would
give the semisimplified characters but would not imply (7.5).

### 7.3 Cayley--Hamilton and trace

Fix $g$ and put

$$
f=\rho_n(g),
\qquad
d=\det f=\chi_3(g)\in A^\times.
\tag{7.6}
$$

Taking $h=g$ in (7.5) gives

$$
(f-d)(f-1)=0,
\tag{7.7}
$$

or

$$
f^2-(1+d)f+d=0.
\tag{7.8}
$$

Cayley--Hamilton on the free rank-two $A$-module $W$ gives

$$
f^2-(\operatorname{tr}f)f+d=0.
\tag{7.9}
$$

Subtracting (7.8) from (7.9) and multiplying by $f^{-1}$ yields

$$
\boxed{
\operatorname{tr}\rho_n(g)=1+\chi_3(g)
\quad\text{in }A_n.
}
\tag{7.10}
$$

The determinant hypothesis is used exactly at (7.6). Odd-tame membership and the simple-factor
classification alone would not identify the second scalar in the characteristic polynomial.

### 7.4 The residual orientation

At $n=1$, the $k$-vector space $T_1$ has dimension two. The subspace $N_1$ is neither zero nor
all of $T_1$.

If $N_1=0$, the action is trivial and its determinant is $1$, contradicting
$\bar\chi_3(c)=-1$ for complex conjugation $c$. If $N_1=T_1$, equation (7.4) makes every
element act by the scalar $\bar\chi_3$; its determinant is then
$\bar\chi_3^2=1$, giving the same contradiction at $c$.

Thus $N_1$ is a line and

$$
0\longrightarrow k(1)
\longrightarrow T_1
\longrightarrow k
\longrightarrow0.
\tag{7.11}
$$

The sequence is oriented but can split. If it is nonsplit, its class is a scalar multiple of
the $2$-Kummer direction from (6.9). The rational condition $N_2\ne0$ does not force that scalar
to be nonzero for an arbitrary global lattice; the integral thickness in (2.8) can postpone the
first nontrivial dyadic reduction.

## 8. The integral cyclotomic line

### 8.1 Separated passage through all levels

Define the algebraic augmentation submodule

$$
N=\sum_{g\in G_{\mathbf Q}}(\rho(g)-1)T\subseteq T.
\tag{8.1}
$$

No completion is hidden in this definition. Since $T$ is noetherian, finitely many augmentation
images generate $N$. It is finitely generated and therefore $\varpi$-adically closed. Its image
in $T_n$ is exactly $N_n$.

For fixed $g,h$, relation (7.5) says that the endomorphism

$$
D_{g,h}=(\rho(h)-\chi_3(h))(\rho(g)-1)
\tag{8.2}
$$

has image in $\varpi^nT$ for every $n$. The lattice is separated:

$$
\bigcap_{n\ge1}\varpi^nT=0.
\tag{8.3}
$$

Therefore

$$
\boxed{
(\rho(h)-\chi_3(h))(\rho(g)-1)=0
\qquad(g,h\in G_{\mathbf Q}).
}
\tag{8.4}
$$

It follows that Galois acts cyclotomically on $N$ and trivially on $T/N$.

### 8.2 Rank and saturation

The residual line $N_1$ is nonzero, so $N$ contains an element not divisible by $\varpi$ in
$T$. In particular $N\ne0$. As a submodule of the free $\mathcal O$-module $T$, it is torsion
free.

Its rank cannot be two. If it were, $N\otimes K=V$, and (8.4) would make every
$\rho(h)$ the scalar $\chi_3(h)$ on $V$. Its determinant would be $\chi_3(h)^2$, contrary to
$\det\rho=\chi_3$ at complex conjugation.

Thus $N$ has rank one. Let

$$
\mathcal L=(N\otimes_{\mathcal O}K)\cap T.
\tag{8.5}
$$

Then $\mathcal L$ is a saturated rank-one submodule. Relation (8.4) holds on the $K$-span of
$N$, so Galois acts on $\mathcal L$ by $\chi_3$. Every augmentation image lies in
$N\subseteq\mathcal L$, so Galois acts trivially on $T/\mathcal L$. Saturation makes the quotient
free of rank one.

Consequently

$$
\mathcal L\simeq\mathcal O(1),
\qquad
T/\mathcal L\simeq\mathcal O.
\tag{8.6}
$$

### 8.3 The signed-special reducibility theorem

Equations (8.5)--(8.6) prove (1.12). Taking traces gives, for every $g$,

$$
\operatorname{tr}\rho(g)=1+\chi_3(g),
\qquad
\det\rho(g)=\chi_3(g).
\tag{8.7}
$$

Tensoring with $K$ gives

$$
0\longrightarrow K(1)
\longrightarrow V
\longrightarrow K
\longrightarrow0,
\tag{8.8}
$$

and hence

$$
V^{\mathrm{ss}}\simeq K(1)\oplus K.
\tag{8.9}
$$

No semisimplicity hypothesis was used to construct the line. If $V$ is semisimple, (8.8) splits
over $K$. The integral sequence need not split, because the Kummer class of $2$ survives.

### 8.4 Comparison with the local SP line

The global line $\mathcal L\otimes K$ is inertia-fixed at $2$, since $\chi_3$ is unramified
there. By the uniqueness in (2.4), it equals the rational local SP line. The local Frobenius
character on that line is $\chi_3\eta_2$, whereas the global character is exactly $\chi_3$.
Therefore

$$
\eta_2=1,
\qquad
\varepsilon_2=1.
\tag{8.10}
$$

Thus a negative-sign input $\varepsilon_2=-1$ is already incompatible with the global
finite-flat conclusion. The main theorem does not rely on this shortcut: the good-prime trace
contradiction treats either input sign uniformly.

## 9. The certified Frobenius contradiction

### 9.1 One certified good prime

Book 185, Theorem 9.1, supplies a finite exceptional set $S$ and, for every prime
$q\notin S$, a polynomial

$$
P_q(X)=X^2-a_qX+q\in E[X]
\tag{9.1}
$$

which is pure of weight one. Since $S\cup\{2,3\}$ is finite, there exists a prime

$$
q\notin S\cup\{2,3\}.
\tag{9.2}
$$

For the selected place $\nu\mid3$, weak compatibility certifies that $V$ is unramified at this
$q$ and that (9.1), after the embedding $\iota_\nu:E\hookrightarrow K$, is the characteristic
polynomial of arithmetic Frobenius.

This choice uses only the proved cofinite good set. If one wants to take $q=5$, one must first
verify $5\notin S$ or separately certify its local polynomial. No such verification is needed for
Theorem 1.1.

### 9.2 Transport to the algebraic coefficient field

Equation (8.7) gives

$$
\operatorname{tr}\rho(\operatorname{Frob}_q)=1+q
\tag{9.3}
$$

because arithmetic Frobenius satisfies

$$
\chi_3(\operatorname{Frob}_q)=q.
\tag{9.4}
$$

Compatibility gives the same trace as $\iota_\nu(a_q)$. Therefore

$$
\iota_\nu(a_q)=1+q.
\tag{9.5}
$$

The coefficient embedding is injective, so equality in the completion implies equality in the
algebraic coefficient field:

$$
\boxed{a_q=1+q\quad\text{in }E.}
\tag{9.6}
$$

No Chebotarev theorem is needed for this step. It compares one already constructed member with
its defining common polynomial at one certified prime.

### 9.3 Purity

Let $\alpha_q,\beta_q$ be the roots of $P_q$. Weight-one purity says that for every complex
embedding $\tau$ of a splitting field,

$$
|\tau(\alpha_q)|=|\tau(\beta_q)|=\sqrt q.
\tag{9.7}
$$

Hence

$$
|\tau(a_q)|
=|\tau(\alpha_q)+\tau(\beta_q)|
\le2\sqrt q.
\tag{9.8}
$$

But (9.6) is equality with the rational integer $1+q$, so every $\tau$ sends $a_q$ to
$1+q$. Thus

$$
1+q\le2\sqrt q,
\tag{9.9}
$$

contrary to (1.15). The determinant identity $\alpha_q\beta_q=q$ would not prove (9.7);
purity is a separate and indispensable compatible-family input.

### 9.4 The Frey endpoint

Book 163 supplies the residual signed-SP Frey datum and states the downstream contract. Book 185
conditionally supplies an absolutely irreducible compatible member with the rational SP record
and pure good polynomials. Book 187 conditionally supplies the all-level tower. Once those
antecedents exist, Theorem 1.1 gives two contradictions:

1. the line in (8.8) contradicts absolute irreducibility; and
2. any certified prime (9.2) contradicts weight-one purity.

The second endpoint is independent of a claim that the prime $5$ is good. The first endpoint does
not need semisimplicity or purity. Both use the actual characteristic-zero line, not merely a
reducible residual representation.

## 10. Dependencies, hostile audit, and readiness

### 10.1 Direct dependencies

The proof uses the following results directly.

| Source | Exact input | Use here |
|---|---|---|
| Books 2--3 | local Galois groups, tame return, upper numbering, Hilbert's different formula, Hasse--Arf | Sections 2, 4, and 5 |
| Books 5--6 | local and global reciprocity and ray exact sequences | the abelian exclusions in Section 5 |
| Class Field Theory development | the reciprocity/existence identification of ray quotients with abelian extensions | Sections 5.1--5.2 |
| Book 17 | finite-etale descent over henselian odd local bases | local uniqueness and gluing of the reverse splitting |
| Book 29 | fppf Kummer theory | the mixed extension calculation in Section 6 |
| Books 28, 34, and 42 | saturated closure, represented quotients, finite-flat generic modules, and coefficient actions | the exact devissage in Sections 3 and 6 |
| Book 34 | Cartier duality | the multiplicative simple factor and pure extensions |
| Book 51 | order-three finite-flat classification over $\mathbf Z_3$ | identification of $C$ and $M$ |
| Book 158 | the exponent-three upper-break and root-discriminant bounds | (4.1)--(4.6) |
| Book 159 | the unconditional degree-$21$ numerical certificate | (4.7)--(4.10) |
| Book 185, Theorem 9.1 | determinant, rational SP pair, cofinite common good polynomials, and purity | the rational local record and Section 9 |
| Book 187, Theorem 10.2 | the conditional clean-support, coefficient-linear all-level tower over $\mathbf Z[1/2]$ | the sole integral input at and away from $3$ |

Book 163 is the Frey provenance and downstream consumer contract, not a proof input to the
bounded representation-theoretic theorem. Book 160 gives a broader monograph treatment of the
finite-flat category, but no theorem of Book 160 is needed here: the SP-specific degree-$20$
classification and trace argument have been proved above.

The recommended direct dependency row is

$$
\boxed{
188\mid
2,3,5,6,17,29,28,34,42,51,158,159,185,187,\mathrm{CFT}.
}
\tag{10.1}
$$

### 10.2 Exact upstream blockers

The bounded implication of Theorem 1.1 is complete. Its antecedent is not currently produced
unconditionally by the spine.

1. **Controlled SP top datum.** Book 185, Theorem 9.1, assumes the controlled SP packet-array
   datum used by Books 183--184. Book 185's own audit records that the current Book 182 does not
   unconditionally supply the controlled residual automorphic seed.
2. **Coefficient-prime certificate $(\mathrm C_3)$.** Even after the conditional Book 185
   member is granted, Book 187 requires a proof that the selected member at $\nu\mid3$ is
   crystalline over $\mathbf Q_3$ of Hodge type $(0,1)$. Book 185 does not prove this.
3. **Clean-support certificate $(\mathrm U)$.** Book 187 also requires actual unramifiedness at
   every prime in the finite auxiliary set left by Book 185. Weak compatibility does not remove
   those primes. Without these finite checks, the local tower at $3$ cannot be glued over
   $\mathbf Z[1/2]$.

No additional blocker occurs inside Book 188 once Book 187, Theorem 10.2, and one prime from Book
185's already certified cofinite good set are supplied.

### 10.3 Hostile audit

**SP type.** The dyadic object has $N_2\ne0$ of rank one, the intrinsic line
$\ker N_2=\operatorname{im}N_2$, the sign $\varepsilon_2$, and conductor exponent one. No
monodromy-zero or conductor-two language occurs.

**Integral thickness.** Rational nonzero monodromy does not imply nonzero residual monodromy for
an arbitrary global lattice. The proof uses only the saturated filtration and square-zero action;
it allows the first residual inertia image to be trivial.

**Higher dyadic inertia.** The image on $T_n$ can have order $3^r$ with $r>1$. The order-three
bound is used only after passing to a subquotient killed by $3$.

**Coefficient prime.** Crystallinity is not treated as finite flatness of an arbitrary lattice.
The only coefficient-prime input is the actual tower exported conditionally by Book 187,
Theorem 10.2. Every level is $\varpi^n$, not merely $3^n$.

**Support.** A global model over $\mathbf Z[1/2]$ is used only under Book 187's clean-support
certificate. No auxiliary prime is removed from equality of almost all Frobenius traces.

**Discriminant normalization.** At $3$, $1/2$ is an upper-break cutoff and $3/2$ is a normalized
different bound. At $2$, the exact tame exponent is $2/3$. The global ceiling pays each factor
once and is applied only to exponent-three modeled objects.

**Numerics.** The logarithmic lower bound at degree $21$ is strictly larger than the logarithm
of the arithmetic ceiling. Monotonicity in the degree gives $[L:\mathbf Q]\le20$. No conditional
GRH table enters.

**Finite image.** Degree at most twenty does not imply reducibility. The proof separately uses
the abelian subfield calculation, the $\lambda$-ray groups of $\mathbf Q(\zeta_3)$, solvability,
and the normal-$3$-group fixed-vector argument.

**Extensions.** The $2$-Kummer extension survives in $\operatorname{Ext}^1(C,M)$. Only the
reverse group $\operatorname{Ext}^1(M,C)$ vanishes. Therefore the final integral sequence is not
declared split.

**Coefficient action.** The $A_n$-action is retained on every finite-flat model. It is what makes
Cayley--Hamilton a rank-two identity over $A_n$ and produces (7.10) for ramified coefficient
fields as well.

**Limit.** The proof does not lift a chosen residual vector. It passes the cross relation through
all separated coefficient levels, forms the algebraic augmentation submodule, and saturates its
rank-one $K$-span.

**Good prime.** The final prime lies in Book 185's certified cofinite good set. The argument does
not assume that $5$ is outside the exceptional set. The inequality is valid for every certified
prime $q>1$. In particular, Book 163's illustrative downstream choice of $5$ is not imported as
an unproved local certificate.

### 10.4 Conclusion

The signed-special local record supplies exactly the residual ramification needed by Fontaine's
argument. Every exponent-three subquotient has trivial or cubic tame inertia at $2$ and an actual
finite-flat model at $3$. Its field therefore has root discriminant below
$3^{3/2}2^{2/3}$ and degree at most twenty. Class field theory over $\mathbf Q$ and
$\mathbf Q(\zeta_3)$ then reduces every simple factor to the constant group or $\mu_3$.

The asymmetric mixed extension calculation sorts all multiplicative factors below all constant
factors without discarding the genuine Kummer class of $2$. With coefficients retained, that
ordered filtration gives the finite-level cross relation. Separated passage through the tower
produces an actual saturated cyclotomic line in $T$, and hence semisimplification
$1\oplus\chi_3$.

At any prime in the certified pure good set, the trace is simultaneously $1+q$ and bounded in
absolute value by $2\sqrt q$, an impossibility. Thus the bounded conditional theorem of this book
is

$$
\boxed{\textbf{READY}.}
\tag{10.2}
$$

The unconditional FLT dependency spine is not ready for the three upstream reasons listed in
Section 10.2. That upstream status does not weaken the proved implication from the exact tower to
the contradiction.
