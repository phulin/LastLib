# Local Conditions for Hardly-Ramified Minimal Deformations

## Contents

- [1. The Frey minimal problem](#1-the-frey-minimal-problem)
  - [1.1 Scope](#11-scope)
  - [1.2 Coefficients and conventions](#12-coefficients-and-conventions)
  - [1.3 The residual local data](#13-the-residual-local-data)
  - [1.4 Tangents and constrained obstructions](#14-tangents-and-constrained-obstructions)
- [2. The dyadic minimal-special condition](#2-the-dyadic-minimal-special-condition)
  - [2.1 Tame monodromy and the intrinsic line](#21-tame-monodromy-and-the-intrinsic-line)
  - [2.2 Definition over Artinian rings](#22-definition-over-artinian-rings)
  - [2.3 The strict normal form](#23-the-strict-normal-form)
  - [2.4 Representability, rings, and liftability](#24-representability-rings-and-liftability)
  - [2.5 Conductor and adjoint cohomology](#25-conductor-and-adjoint-cohomology)
  - [2.6 Scalar, monodromy-zero, and exceptional boundaries](#26-scalar-monodromy-zero-and-exceptional-boundaries)
- [3. Finite flatness at the coefficient prime](#3-finite-flatness-at-the-coefficient-prime)
  - [3.1 The integral condition](#31-the-integral-condition)
  - [3.2 The low-weight coordinates](#32-the-low-weight-coordinates)
  - [3.3 The tangent complex](#33-the-tangent-complex)
  - [3.4 Liftability and local rings](#34-liftability-and-local-rings)
  - [3.5 Residual shapes and the hardly-ramified line](#35-residual-shapes-and-the-hardly-ramified-line)
- [4. The global hardly-ramified functor](#4-the-global-hardly-ramified-functor)
  - [4.1 Global hypotheses](#41-global-hypotheses)
  - [4.2 Definition and representability](#42-definition-and-representability)
  - [4.3 The global tangent space](#43-the-global-tangent-space)
  - [4.4 What local smoothness does and does not prove](#44-what-local-smoothness-does-and-does-not-prove)
  - [4.5 Coefficient extension and compatible finite levels](#45-coefficient-extension-and-compatible-finite-levels)
- [5. Exact interfaces to Books 166--167 and 181](#5-exact-interfaces-to-books-166--167-and-181)
  - [5.1 Input to supported cohomology](#51-input-to-supported-cohomology)
  - [5.2 Input to relation obstructions](#52-input-to-relation-obstructions)
  - [5.3 Input to the balanced lift argument](#53-input-to-the-balanced-lift-argument)
  - [5.4 Non-exports](#54-non-exports)
- [6. The theorem package and dependency audit](#6-the-theorem-package-and-dependency-audit)
  - [6.1 Main theorem](#61-main-theorem)
  - [6.2 Hypothesis and boundary ledger](#62-hypothesis-and-boundary-ledger)
  - [6.3 Direct prerequisites and circularity audit](#63-direct-prerequisites-and-circularity-audit)
  - [6.4 Conclusion](#64-conclusion)

## 1. The Frey minimal problem

### 1.1 Scope

This book constructs the local deformation conditions used by the
hardly-ramified **Frey minimal-special** problem.  There are two distinguished
finite places:

$$
2\qquad\text{and}\qquad \ell,
$$

where $\ell\geq7$ is the coefficient prime.  At $2$ the residual Frey
representation already has a nonzero tame unipotent block.  Minimality means
retaining that block, its intrinsic line, its split or nonsplit unramified
sign, and its conductor-one special shape.  At $\ell$ the representation is
required to have an actual coefficient-linear finite-flat model over
$\mathbf Z_\ell$.  Away from $\{2,\ell\}$ no ramification is allowed.

The purpose is not merely to name characteristic-zero local types.  For each
Artinian coefficient ring we must have a functorial and closed condition, an
honest representing ring in the framed convention, a calculated tangent
subspace, and an effective lifting theorem.  Those are the inputs consumed by
supported cohomology, relation-obstruction theory, and the balanced minimal-lift
argument in Books 166--167 and 181.

### 1.2 Coefficients and conventions

Let $E/\mathbf Q_\ell$ be finite, with ring of integers $\mathcal O$,
uniformizer $\varpi$, and finite residue field

$$
k=\mathcal O/\varpi.
$$

Write $\operatorname{Art}_{\mathcal O}$ for the category of Artinian local
$\mathcal O$-algebras with residue field $k$.  A lift of a residual
representation

$$
\bar\rho:G\longrightarrow\operatorname{GL}_2(k)
$$

to $A\in\operatorname{Art}_{\mathcal O}$ is a continuous homomorphism
$\rho_A:G\to\operatorname{GL}_2(A)$ reducing to the fixed residual matrix
representation.  Two lifts are **strictly equivalent** if they are conjugate
by an element of

$$
\ker\bigl(\operatorname{GL}_2(A)\to\operatorname{GL}_2(k)\bigr).
$$

A framed lift retains the fixed basis and is not divided by strict conjugacy.
All deformations in this book have determinant

$$
\det\rho_A=\chi_\ell, \tag{1.1}
$$

where $\chi_\ell$ is the $\ell$-adic cyclotomic character.

We use arithmetic Frobenius.  Hence at $p\ne\ell$,

$$
\chi_\ell(\phi_p)=p. \tag{1.2}
$$

For a two-dimensional residual representation put

$$
\operatorname{ad}\bar\rho=\operatorname{End}_k(k^2),
\qquad
M=\operatorname{ad}^0\bar\rho.
$$

Since $\ell$ is odd, trace splits the adjoint representation:

$$
\operatorname{ad}\bar\rho=kI\oplus M. \tag{1.3}
$$

The trace pairing is perfect on $M$, so its Tate dual is

$$
M'=M^*(1)\simeq M(1). \tag{1.4}
$$

These two elementary facts are used in every fixed-determinant tangent and
local-duality calculation below.

### 1.3 The residual local data

The local problem starts with a residual representation satisfying two
different integral hypotheses.

At $2$, choose the $\ell$-primary tame character

$$
t_\ell:I_2\twoheadrightarrow\mathbf Z_\ell
$$

so that, for arithmetic Frobenius $\phi$,

$$
t_\ell(\phi\sigma\phi^{-1})=2t_\ell(\sigma).
\tag{1.5}
$$

After one fixed residual change of basis, assume

$$
\bar\rho_2(\sigma)
=I+\overline t_\ell(\sigma)\bar N,
\qquad
\bar N=e_{12},
\qquad \sigma\in I_2, \tag{1.6}
$$

and

$$
\bar F:=\bar\rho_2(\phi)
=\begin{pmatrix}2\bar s&0\\0&\bar s\end{pmatrix},
\qquad \bar s\in\{1,-1\}. \tag{1.7}
$$

Equation (1.6) says that residual monodromy is nonzero.  Equation (1.7)
records the unramified split or nonsplit sign.  The determinant equation gives
$2\bar s^2=2$, and odd coefficient characteristic separates the two signs.
The Tate-curve calculation for a Frey curve supplies exactly (1.6): the
coefficient of $e_{12}$ is the dyadic minimal-discriminant valuation modulo
$\ell$.  In the standard normalized equation

$$
a^\ell+b^\ell=c^\ell,
$$

Book 164, Sections 3.1 and 4.3, take $a$ to be the even leg and give

$$
m_2=v_2(\Delta_{\min})=2\ell v_2(a)-8.
$$

Thus $m_2\equiv-8\not\equiv0\pmod\ell$ for $\ell\geq7$, and the
Tate-curve inertia formula gives the nonzero matrix $m_2e_{12}$ in a Tate
basis, as recorded in Book 164, Section 5.2.  A residual diagonal change of
basis then normalizes it to the $\bar N=e_{12}$ of (1.6).  The local theorem
below needs only this nonvanishing; it does not reuse any later lifting
conclusion.

At the coefficient prime assume

$$
\bar\rho_\ell:G_{\mathbf Q_\ell}
\longrightarrow\operatorname{GL}_2(k) \tag{1.8}
$$

is coefficient-linearly finite flat: it is the generic fiber of a finite
flat group scheme over $\mathbf Z_\ell$ with its $k$-action, and it has
determinant $\bar\chi_\ell$.  This is an integral existence assertion, not an
inertia condition; Section 3.1 gives the definition over every Artinian
coefficient ring.  The local theory starts from this explicit residual
hypothesis and does not import a global lift or Selmer conclusion.

### 1.4 Tangents and constrained obstructions

A first-order lift has the form

$$
\rho_\epsilon(g)=(I+\epsilon c(g))\bar\rho(g),
\qquad \epsilon^2=0.
$$

Multiplicativity makes $c$ a $1$-cocycle in
$\operatorname{ad}\bar\rho$, and strict conjugacy changes it by a
coboundary.  Differentiating determinant gives trace.  Consequently the
ambient fixed-determinant unframed tangent is

$$
H^1(G,M). \tag{1.9}
$$

A local deformation condition $\mathcal D_v$ cuts out a subspace

$$
L_v\subseteq H^1(G_v,M). \tag{1.10}
$$

The tangent subspace is not the full deformation condition.  For a small
extension

$$
0\longrightarrow J\longrightarrow A'
\longrightarrow A\longrightarrow0,
\qquad \mathfrak m_{A'}J=0, \tag{1.11}
$$

an ambient matrix lift has a factor-set obstruction in

$$
H^2(G_v,M)\otimes_kJ.
$$

A constrained problem can nevertheless be liftable when this ambient group
is nonzero: its particular obstruction map can be zero.  At $2$ we shall
prove the stronger ambient vanishing.  At $\ell$ we shall lift the integral
filtered data directly and will make no ambient $H^2$-vanishing claim.

## 2. The dyadic minimal-special condition

### 2.1 Tame monodromy and the intrinsic line

Wild inertia at $2$ is pro-$2$.  The Frey residual representation in odd
coefficient characteristic has trivial wild action, while the pro-$\ell$
tame quotient acts through (1.6).  Since

$$
\bar N^2=0,
\qquad
\bar N\ne0,
$$

the residual monodromy has rank one and determines the line

$$
\bar L=\ker\bar N=\operatorname{im}\bar N. \tag{2.1}
$$

This line is intrinsic.  It is not an enhancement chosen over a scalar
residual point.  Frobenius preserves it because

$$
\bar F\bar N\bar F^{-1}=2\bar N. \tag{2.2}
$$

On $\bar L$ Frobenius has eigenvalue $2\bar s$, while on the quotient it
has eigenvalue $\bar s$.  Thus the residual representation has the special
orientation

$$
0\longrightarrow k(\bar\psi\bar\chi_\ell)
\longrightarrow \bar V
\longrightarrow k(\bar\psi)\longrightarrow0, \tag{2.3}
$$

where $\bar\psi$ is unramified and
$\bar\psi(\phi)=\bar s$.

### 2.2 Definition over Artinian rings

Let $s\in\{1,-1\}\subset\mathcal O^\times$ be the unique lift of
$\bar s$.  For $A\in\operatorname{Art}_{\mathcal O}$, define
$\mathcal D_2^{\mathrm{sp,min},\chi}(A)$ to be the strict-equivalence classes
of lifts $\rho_A:G_{\mathbf Q_2}\to\operatorname{GL}_2(A)$ satisfying
(1.1) and the following conditions:

1. wild inertia acts trivially;
2. there is an endomorphism $N_A$ lifting $\bar N$ such that
   $$
   \rho_A(\sigma)=I+t_\ell(\sigma)N_A
   \quad(\sigma\in I_2),
   \qquad N_A^2=0; \tag{2.4}
   $$
3. for $F_A=\rho_A(\phi)$,
   $$
   F_AN_AF_A^{-1}=2N_A; \tag{2.5}
   $$
4. the unramified character on the quotient by
   $L_A=\ker N_A$ has Frobenius value $s$.

If $\tau\in I_2$ is chosen with $t_\ell(\tau)=1$, then (2.4) forces
$N_A=\rho_A(\tau)-I$.  Thus $N_A$ is determined by the representation;
the word “there is” does not hide a projection of an auxiliary moduli
space.

Because $N_A$ reduces to the nonzero rank-one operator $\bar N$, one entry
of $N_A$ is a unit.  Hence

$$
L_A=\ker N_A=\operatorname{im}N_A \tag{2.6}
$$

is a direct-summand line.  It is the unique lift of the inertial fixed line.
The line-enhanced and intrinsic matrix conditions therefore define the same
functor.

The definition is independent of the normalization of $t_\ell$.  Replacing
$t_\ell$ by $u t_\ell$ for $u\in\mathbf Z_\ell^\times$ replaces $N_A$ by
$u^{-1}N_A$.  It is also stable under every coefficient map: the residual
unit entry keeps monodromy nonzero after every map in
$\operatorname{Art}_{\mathcal O}$.  This last assertion would be false if
the residual operator were zero.

The equations include the diagonal characters, not merely the two incidence
relations $N_A^2=0$ and (2.5).  At $N_A=0$ those two relations alone contain
an extraneous unramified locus.  Nonzero residual monodromy is what keeps the
present minimal problem away from that boundary.

### 2.3 The strict normal form

The local functor can be classified without appealing to a dimension
count.

**Lemma 2.1 (normalizing monodromy).** Every lift $N_A$ of $e_{12}$ with
$N_A^2=0$ is strictly conjugate to $e_{12}$.

**Proof.** Choose $v\in A^2$ reducing to the second standard basis vector.
Then $N_Av$ reduces to the first standard basis vector and is unimodular.
Moreover $N_A(N_Av)=0$.  Thus $(N_Av,v)$ is a basis reducing to the
standard basis, and the matrix of $N_A$ in this basis is $e_{12}$.  The
change-of-basis matrix is congruent to the identity. $\square$

After this strict conjugacy, write

$$
F_A=\begin{pmatrix}x&b\\z&a\end{pmatrix}.
$$

Solving $F_Ae_{12}=2e_{12}F_A$ gives

$$
z=0,
\qquad x=2a,
$$

so

$$
F_A=\begin{pmatrix}2a&b\\0&a\end{pmatrix}. \tag{2.7}
$$

The residual basis was chosen so that $b\in\mathfrak m_A$.  Fixed
cyclotomic determinant gives

$$
2a^2=\chi_\ell(\phi)=2,
\qquad a^2=1. \tag{2.8}
$$

Since $a\equiv s$ and $a+s$ is a unit, $(a-s)(a+s)=0$ forces

$$
a=s. \tag{2.9}
$$

Finally, strict conjugation by $I+ue_{12}$ replaces $b$ by $b-su$.
Taking $u=b/s$ removes $b$.  We have proved the unique normal form

$$
\boxed{
N=e_{12},
\qquad
F=\begin{pmatrix}2s&0\\0&s\end{pmatrix}.}
\tag{2.10}
$$

Conversely, (2.10) together with (2.4) defines a continuous representation
of the tame quotient, has determinant $\chi_\ell$, and reduces to the fixed
residual representation.  Thus the normal form proves existence as well as
uniqueness over every Artinian coefficient ring.

### 2.4 Representability, rings, and liftability

The equations (2.4)--(2.5), the determinant, and the named diagonal
characters are closed matrix-and-line equations.  Book 67, Theorem 7.1,
proves closed representability and smoothness for precisely this nonzero
rank-one monodromy case when the residue cardinality is not $1$ modulo
$\ell$ and $2$ is invertible.  Here the residue cardinality is $2$ and
$\ell\geq7$, so its hypotheses hold.  Lemma 2.1 and (2.7)--(2.10) reproduce
the complete calculation in the present normalization.

**Theorem 2.2 (dyadic Frey-special rings).** The unframed fixed-determinant
functor has one point over every $A\in\operatorname{Art}_{\mathcal O}$ and
is represented by

$$
R_2^{\mathrm{sp,min},\chi}\simeq\mathcal O. \tag{2.11}
$$

The residual centralizer of the pair $(\bar F,\bar N)$ is scalar.  Hence the
framed functor is the formal change-of-frame orbit and is represented
noncanonically by

$$
R_2^{\square,\mathrm{sp,min},\chi}
\simeq\mathcal O[[Y_1,Y_2,Y_3]]. \tag{2.12}
$$

Both functors lift through every small extension, and the unframed tangent
space is

$$
L_2=0. \tag{2.13}
$$

**Proof.** Normal form (2.10) proves that the unframed functor is the
one-point functor and proves liftability directly.  A matrix commuting with
$e_{12}$ has equal diagonal entries; commuting also with
$\operatorname{diag}(2\bar s,\bar s)$ kills its upper-right entry.  The
centralizer is therefore $kI$.  The formal quotient of
$\widehat{\operatorname{GL}}_2$ by its scalar stabilizer is smooth of
dimension $4-1=3$, giving (2.12).  A one-point functor has tangent zero.
$\square$

The nonzero-monodromy condition is closed here because nonvanishing is
already visible modulo $\varpi$.  This must not be generalized to a
residually unramified special chart, where nonzero generic monodromy is an
open condition and the closed chart contains the monodromy-zero divisor.

### 2.5 Conductor and adjoint cohomology

Every characteristic-zero point of the dyadic condition is trivial on wild
inertia.  Its tame inertia-fixed vectors are exactly $\ker N$, a line.
Therefore its Swan conductor is zero and its Artin conductor exponent is

$$
a_2(\rho)=\dim V-\dim V^{I_2}=2-1=1. \tag{2.14}
$$

This is the conductor-one Steinberg shape of the Frey curve.  Conductor is a
consequence of the constant-rank monodromy equation; conductor one by itself
would not define the integral component.

The same normal form computes the entire residual adjoint cohomology needed
later.  Let

$$
M=\operatorname{ad}^0\bar\rho_2.
$$

A trace-zero matrix commuting with $\bar N=e_{12}$ is a multiple of
$\bar N$, because $2$ is invertible.  Thus

$$
M^{I_2}=k\bar N. \tag{2.15}
$$

Conjugation by arithmetic Frobenius acts on this line by $2$.  Hence

$$
H^0(\mathbf Q_2,M)=0. \tag{2.16}
$$

The cyclotomic character is unramified at $2$ and takes $\phi$ to $2$.
On $(M(1))^{I_2}$, Frobenius therefore acts by

$$
2\cdot2=4. \tag{2.17}
$$

Since $\ell\geq7$, $4\ne1$ in $k$, so

$$
H^0(\mathbf Q_2,M(1))=0. \tag{2.18}
$$

The trace pairing identifies $M^*$ with $M$.  Local Tate duality now gives

$$
H^2(\mathbf Q_2,M)=0. \tag{2.19}
$$

The away-from-$\ell$ local Euler characteristic is

$$
h^0-h^1+h^2=0.
$$

Together with (2.16) and (2.19), it gives

$$
H^1(\mathbf Q_2,M)=0. \tag{2.20}
$$

For $M'=M(1)$, local duality identifies $H^2(\mathbf Q_2,M')$ with the
dual of $H^0(\mathbf Q_2,M)$.  Combining this with (2.16), (2.18), and the
Euler characteristic gives the full dual vanishing

$$
H^i(\mathbf Q_2,M')=0
\qquad(0\leq i\leq2). \tag{2.21}
$$

Thus the selected tangent $L_2=0$ agrees with the zero ambient group, and
the ambient fixed-determinant obstruction group vanishes as well.  This is
stronger than the formal smoothness already proved by normal forms.

### 2.6 Scalar, monodromy-zero, and exceptional boundaries

The hypotheses exclude three nearby but different problems.

First, the dyadic residual representation is not scalar.  Nonzero $\bar N$
already rules that out, and the two Frobenius eigenvalues in (1.7) have
ratio $2\ne1$.  Its full local centralizer is scalar even though the
representation is reducible.  This is exactly why the unframed local
functor is representable.

Second, $\bar N\ne0$ is essential.  If $\bar N=0$, the equations
$N^2=0$ and $FNF^{-1}=2N$ contain $N=0$ and cannot represent the open
condition “$N\ne0$.”  One must then retain a line-enhanced closed special
chart and distinguish its unramified divisor.  None of the rigidity
statements of Theorem 2.2 may be specialized to that boundary.

Third, the Galois sign is intrinsic once the residual quotient character is
named: the two possibilities $s=1$ and $s=-1$ are distinct because $2$ is
invertible.  No automorphic occurrence or integral type-lattice assertion is
part of this local theorem.  In characteristic $3$, the twisted eigenvalue in
(2.17) becomes $1$, so the adjoint obstruction calculation changes.  In
characteristic $2$, trace zero does not split from scalars and the determinant
square-root argument is inseparable.  The unified theorem therefore remains
in the range $\ell\geq7$.

## 3. Finite flatness at the coefficient prime

### 3.1 The integral condition

Let $A\in\operatorname{Art}_{\mathcal O}$ and let $V_A=A^2$ carry a
continuous $A$-linear action of $G_{\mathbf Q_\ell}$.  An
**$A$-linear finite-flat model** is a finite locally free commutative group
scheme $\mathcal G_A/\mathbf Z_\ell$, an action

$$
A\longrightarrow\operatorname{End}_{\mathbf Z_\ell}(\mathcal G_A),
$$

and an $A[G_{\mathbf Q_\ell}]$-linear identification

$$
\mathcal G_A(\overline{\mathbf Q}_\ell)\simeq V_A. \tag{3.1}
$$

Define $\mathcal D_\ell^{\mathrm{fl},\chi}(A)$ to be the
strict-equivalence classes of lifts of $\bar\rho_\ell$ which admit such a
model and have determinant $\chi_\ell$.  The framed version retains the
basis.

This definition is deliberately integral.

- Finite flat does not mean unramified: $\mu_{\ell^n}$ realizes the
  cyclotomic character.
- Finite-flat diagonal characters do not make every generic extension
  finite flat; the middle term must have a model.
- Rational crystalline or Hodge--Tate labels do not choose an integral
  lattice.
- A model of one torsion quotient does not by itself provide a compatible
  tower.

The condition is stable under every map of Artinian coefficient rings.
For a quotient $A\to A/I$, close the generic subgroup $IV_A$ inside a
chosen model and take the represented finite-flat quotient.  For a general
map $A\to B$, use a finite presentation of $B$ over $A$, model a finite
direct sum of copies of $V_A$, close the generic relation subgroup, and
take the represented quotient.  The scalar relations descend and give the
quotient its $B$-action.  This is Book 68, Theorem 2.3.  It avoids raw
scheme-theoretic kernels, which need not be flat.

Because the absolute ramification index of $\mathbf Q_\ell$ is
$1<\ell-1$, Raynaud full faithfulness gives more: a marked finite-flat
model, when it exists, is unique up to unique marked isomorphism, and every
generic coefficient endomorphism extends uniquely.  This uniqueness is
what makes compatible quotient models canonical in the present range.

### 3.2 The low-weight coordinates

Book 68, Theorem 14.3, gives the covariant torsion
Fontaine--Laffaille equivalence in weights $[0,1]$ and turns the finite-flat
condition into explicit linear algebra.  We state only its specialization to
the field actually used in the global problem, namely $\mathbf Q_\ell$.

For every $A\in\operatorname{Art}_{\mathcal O}$, a rank-two finite-flat
lift corresponds to a triple

$$
\mathcal M_A=(M_A,L_A,\Phi_A), \tag{3.2}
$$

where

- $M_A$ is projective of rank two over $A$, hence free;
- $L_A\subset M_A$ is a direct-summand line;
- putting
  $$
  D_{L_A}(M_A)
  =\frac{L_A\oplus M_A}
  {\langle(\ell x,-x):x\in L_A\rangle}, \tag{3.3}
  $$
  divided Frobenius is an isomorphism
  $$
  \Phi_A:D_{L_A}(M_A)\xrightarrow{\sim}M_A. \tag{3.4}
  $$

The construction is exact, fully faithful, and compatible with every
Artinian coefficient quotient.  Conversely every triple (3.2)--(3.4)
has a unique marked finite-flat realization with free generic module of
rank two.

The line is forced, rather than separately assumed, by cyclotomic
determinant.  Exterior multiplication gives a perfect alternating pairing

$$
V_A\times V_A\longrightarrow A(1). \tag{3.5}
$$

Raynaud full faithfulness extends its adjoint to the integral model, and
Fontaine--Laffaille duality changes filtration rank $r$ to $2-r$.
Self-duality therefore gives $r=2-r$, so $r=1$.  This is Book 68,
Lemma 14.5.  It works for ordinary and local-local residual groups alike.

Choose a residual basis with $\bar L=k\bar e$.  A based lift has

$$
L_A=A(e+x f),
\qquad x\in\mathfrak m_A, \tag{3.6}
$$

and, in the corresponding divided basis, $\Phi_A$ is an arbitrary
invertible lift of the residual $2\times2$ matrix.  Thus based objects have
one line coordinate and four matrix coordinates.  Fixed cyclotomic
determinant is the single smooth equation

$$
\det\Phi_A=c_\chi, \tag{3.7}
$$

where $c_\chi\in\mathcal O^\times$ is the divided-Frobenius scalar of the
fixed cyclotomic rank-one object.  Its derivative is

$$
\dot\Phi\longmapsto
\operatorname{tr}(\bar\Phi^{-1}\dot\Phi), \tag{3.8}
$$

which is surjective.

### 3.3 The tangent complex

The based parameter count must be divided by changes of the internal
Fontaine--Laffaille basis.  At the residual object put

$$
C^0=\operatorname{End}_k(\bar M),
$$

and

$$
C^1=
\operatorname{Hom}_k(\bar L,\bar M/\bar L)
\oplus\operatorname{End}_k(\bar M). \tag{3.9}
$$

Hence

$$
\dim_kC^0=4,
\qquad \dim_kC^1=5. \tag{3.10}
$$

Linearizing the gauge action gives

$$
d:C^0\longrightarrow C^1. \tag{3.11}
$$

Its line component sends $v\in\bar L$ to $Xv$ modulo $\bar L$.  Its
matrix component is the derivative of

$$
\Phi\longmapsto g\Phi D(g)^{-1}, \tag{3.12}
$$

not ordinary conjugation: the divided source changes with the Hodge line.
Full faithfulness identifies the kernel with residual Galois
endomorphisms.  Put

$$
h_\ell
=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V). \tag{3.13}
$$

Then

$$
\dim_k\ker d=h_\ell,
\qquad
\dim_k\operatorname{im}d=4-h_\ell. \tag{3.14}
$$

Let $\lambda:C^1\to k$ be the determinant derivative (3.8).  It is
surjective and vanishes on $\operatorname{im}d$.  Therefore the unframed
fixed-determinant finite-flat tangent is

$$
L_\ell
=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)
\simeq\ker\lambda/\operatorname{im}d, \tag{3.15}
$$

and

$$
\boxed{\dim_kL_\ell=h_\ell.} \tag{3.16}
$$

For a framed deformation, add the four-dimensional variation of the
generic Galois basis before quotienting by the four internal gauge
directions.  The gauge action on an object with a fixed generic frame is
free by full faithfulness.  Hence the framed fixed-determinant tangent has
dimension

$$
4+4-4=4. \tag{3.17}
$$

This calculation explains the scalar correction used later.  From (1.3),

$$
h^0(\mathbf Q_\ell,M)=h_\ell-1, \tag{3.18}
$$

so

$$
\dim L_\ell-h^0(\mathbf Q_\ell,M)=1. \tag{3.19}
$$

The difference is one even when a nonscalar local centralizer makes both
terms larger.

### 3.4 Liftability and local rings

Let $A'\twoheadrightarrow A$ be a small extension.  Lift the line in (3.6)
by lifting its graph coordinate.  Lift every entry of $\Phi_A$ arbitrarily;
the lifted determinant is still a unit, so the new matrix is invertible.
If its determinant differs from $c_\chi$ by $u\in1+\ker(A'\to A)$,
multiply one column by $u^{-1}$.  This corrects (3.7) without changing the
reduction.  Finally lift the generic frame through
$\operatorname{GL}_2(A')\twoheadrightarrow\operatorname{GL}_2(A)$.

The low-weight classification realizes the lifted triple as a unique
finite-flat model.  Thus every framed or unframed finite-flat lifting
problem is soluble.  The restricted obstruction map is zero.

Combining Book 68, Theorems 9.1--9.2, 16.1, and 17.1, with
(3.16)--(3.17) and this explicit liftability gives the exact ring statement.

**Theorem 3.1 (coefficient-prime rings).** The framed fixed-determinant
finite-flat functor is represented by a closed quotient of the ambient
framed ring and is formally smooth, with

$$
R_\ell^{\square,\mathrm{fl},\chi}
\simeq\mathcal O[[Z_1,Z_2,Z_3,Z_4]]. \tag{3.20}
$$

If $h_\ell=1$, the unframed functor is represented and formally smooth,
with

$$
R_\ell^{\mathrm{fl},\chi}
\simeq\mathcal O[[X]], \tag{3.21}
$$

and noncanonically

$$
R_\ell^{\square,\mathrm{fl},\chi}
\simeq R_\ell^{\mathrm{fl},\chi}[[Y_1,Y_2,Y_3]]. \tag{3.22}
$$

If $h_\ell>1$, (3.20) still holds.  No coarse unframed universal ring is
asserted without a separate rigidification.

The theorem does **not** say

$$
H^2(\mathbf Q_\ell,M)=0.
$$

For example, at the split ordinary point $k(1)\oplus k$, there is a
nonzero trace-zero map $V\to V(1)$ from the $k(1)$ source line to the
$k(1)$ target line.  Local duality then makes the ambient $H^2$ nonzero.
The filtered lifting construction still kills every obstruction arising
inside the finite-flat condition.

### 3.5 Residual shapes and the hardly-ramified line

After a finite residue-field extension, the permitted residual shapes are:

| Residual shape | $h_\ell$ | $\dim L_\ell$ | Framed tangent |
|---|---:|---:|---:|
| absolutely irreducible, including local-local | $1$ | $1$ | $4$ |
| nonsplit extension of distinct characters | $1$ | $1$ | $4$ |
| split sum of distinct characters | $2$ | $2$ | $4$ |

A split scalar representation and a nonsplit self-extension of one
character are impossible in this finite-flat cyclotomic-determinant range.
Indeed the two equal rank-one endpoint models would have the same Hodge
rank $r\in\{0,1\}$; exactness would give middle Hodge rank $2r$, whereas
cyclotomic self-duality forces middle rank one.  This is the scalar boundary
of the finite-flat theorem.  One must not insert a scalar local point into
(3.16) without redoing the integral classification; under the present
hypotheses there is no such point.

The word *hardly ramified* can be seen in the ordinary extension

$$
0\longrightarrow k(1)\longrightarrow V_c
\longrightarrow k\longrightarrow0.
$$

Kummer theory gives

$$
H^1(\mathbf Q_\ell,k(1))
\simeq
\bigl(\mathbf Q_\ell^\times/
(\mathbf Q_\ell^\times)^\ell\bigr)\otimes_{\mathbf F_\ell}k. \tag{3.23}
$$

This space has a unit direction and a valuation direction.  Exact finite-flat
Kummer theory gives

$$
H^1_{\mathrm{fl}}(\mathbf Q_\ell,k(1))
=\bigl(\mathbf Z_\ell^\times/
(\mathbf Z_\ell^\times)^\ell\bigr)
\otimes_{\mathbf F_\ell}k, \tag{3.24}
$$

which is the one-dimensional unit line.  Principal units can still define
ramified extensions.  “Hardly ramified” means that the valuation coordinate
is absent, not that inertia is trivial.  Equation (3.24) illustrates one
ordinary extension direction; it is not a substitute for the full tangent
calculation (3.15)--(3.16), especially at a split point.

## 4. The global hardly-ramified functor

### 4.1 Global hypotheses

Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k) \tag{4.1}
$$

satisfy:

1. $\ell\geq7$ and $\det\bar\rho=\bar\chi_\ell$;
2. $\bar\rho$ is absolutely irreducible;
3. $\bar\rho$ is odd;
4. $\bar\rho$ is unramified outside $\{2,\ell\}$;
5. $\bar\rho|_{G_{\mathbf Q_2}}$ has the nonzero-monodromy Frey-special
   form (1.6)--(1.7), including its sign;
6. $\bar\rho|_{G_{\mathbf Q_\ell}}$ is coefficient-linearly finite flat.

Put

$$
S=\{2,\ell,\infty\},
$$

and let $G_{\mathbf Q,S}$ be the Galois group of the maximal extension
unramified outside $S$.  Absolute irreducibility gives the global Schur
condition

$$
\operatorname{End}_{k[G_{\mathbf Q}]}(k^2)=k. \tag{4.2}
$$

It does not force the local restriction at $\ell$ to have scalar
centralizer; this is why Theorem 3.1 was stated in the framed convention
for every permitted local shape.

### 4.2 Definition and representability

For $A\in\operatorname{Art}_{\mathcal O}$, let
$D^{\mathrm{hr,SP}}(A)$ be the strict-equivalence classes of continuous
lifts

$$
\rho_A:G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(A) \tag{4.3}
$$

such that

$$
\det\rho_A=\chi_\ell, \tag{4.4}
$$

$$
\rho_A|_{G_{\mathbf Q_2}}
\in\mathcal D_2^{\mathrm{sp,min},\chi}(A), \tag{4.5}
$$

and

$$
\rho_A|_{G_{\mathbf Q_\ell}}
\in\mathcal D_\ell^{\mathrm{fl},\chi}(A). \tag{4.6}
$$

Oddness is automatic: complex conjugation squares to one, $2$ is
invertible, and determinant $-1$ forces one $+1$ and one $-1$ eigenline.
Unramifiedness outside $\{2,\ell\}$ is built into the source group.

**Theorem 4.1 (universal Frey-special hardly-ramified ring).** The functor
$D^{\mathrm{hr,SP}}$ is represented by a complete Noetherian local
$\mathcal O$-algebra

$$
R^{\mathrm{hr,SP}}. \tag{4.7}
$$

It is a quotient of the universal fixed-determinant deformation ring of
$\bar\rho$ unramified outside $S$.

**Proof.** The global Schur condition (4.2) and the global cohomology
finiteness theorem of Book 32, Section 3.2, applied to
$H^1(G_{\mathbf Q,S},M)$, give the universal unframed fixed-determinant ring.
Choose a representative of its universal class and restrict it to the two
decomposition groups.  Theorems 2.2 and 3.1 represent the framed local
conditions by closed quotients of the ambient framed local rings.  Pull
their defining ideals back along the two restrictions and quotient the
global ring by the closed sum of those ideals.

Membership in both local conditions is invariant under strict conjugacy,
so changing the chosen representative of the universal global class does
not change the quotient functor.  The universal property of the quotient
now says that its maps to $A$ are exactly (4.3)--(4.6).  This is the standard
framed-local/unframed-global assembly argument from general deformation
theory; local coarse representability at $\ell$ is not required. $\square$

No global $H^2$-vanishing is used in representability.  Global degree two
controls relations after the ring exists.

### 4.3 The global tangent space

Put

$$
M=\operatorname{ad}^0\bar\rho.
$$

The ambient fixed-determinant tangent is
$H^1(G_{\mathbf Q,S},M)$.  Evaluating (4.5)--(4.6) on dual numbers gives

$$
t^{\mathrm{hr,SP}}
=\left\{c\in H^1(G_{\mathbf Q,S},M):
\operatorname{res}_2c\in L_2,
\ \operatorname{res}_\ell c\in L_\ell\right\}. \tag{4.8}
$$

Using (2.13) and (3.15),

$$
\boxed{
t^{\mathrm{hr,SP}}
=\ker\left(
H^1(G_{\mathbf Q,S},M)
\longrightarrow
H^1(\mathbf Q_2,M)
\oplus
\frac{H^1(\mathbf Q_\ell,M)}
{H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)}
\right).}
\tag{4.9}
$$

The first target is zero by (2.20), but retaining it records the nonlinear
dyadic condition.  Formula (4.9) is the exact localization-kernel interface,
not merely a dimension equality.

### 4.4 What local smoothness does and does not prove

Both local conditions lift through small extensions.  This has three exact
consequences.

At $2$, an admissible lift is unique up to strict equivalence, and the
ambient groups $H^1(\mathbf Q_2,M)$ and $H^2(\mathbf Q_2,M)$ vanish.  At
$\ell$, admissible lifts exist and their first-order differences lie in
$L_\ell$, but ambient $H^2(\mathbf Q_\ell,M)$ may be nonzero.  In both
cases the lift torsors and their difference classes commute with pushout of
the kernel in a small extension: this is immediate from the dyadic normal
form and from the linear line/matrix coordinates at $\ell$.

These statements do not imply that a global lift exists.  Given an ambient
global lift, moving both local restrictions into their admissible torsors is
a global localization problem.  A global factor-set obstruction can remain,
and compatible local corrections need not come from one global correction.
Books 166--167 introduce supported cohomology precisely to retain those
two defects.

### 4.5 Coefficient extension and compatible finite levels

Let $\mathcal O'/\mathcal O$ be a finite extension.  The dyadic equations,
the line, and the sign commute with scalar extension.  At $\ell$, Book 68,
Theorem 2.3, constructs a coefficient-linear finite-flat model after every
finite coefficient map.  Thus the scalar-extended residual representation
has the scalar-extended local problem, after selecting the corresponding
closed residual point if the residue field grows.

For a complete coefficient algebra, finite flatness means that every
Artinian quotient belongs to the finite-flat functor.  Raynaud uniqueness
makes the resulting marked models compatible along nested quotients.  This
is a pro-system of finite group schemes, not one finite group scheme of
infinite order.

Consequently a map from $R^{\mathrm{hr,SP}}$ to a coefficient DVR
$\mathcal O'$ produces a lattice whose every quotient by an open ideal has
a compatible coefficient-linear finite-flat model at $\ell$.  This
conclusion comes from the represented local condition, not from any flatness
property of the global ring over $\mathcal O$.

No general ground-field base-change theorem is needed in the Frey minimal
argument.  The later totally real field is required to split completely at
$2$ and $\ell$, so its completions at the selected places are literally
$\mathbf Q_2$ and $\mathbf Q_\ell$ and the local problems above are
unchanged.

## 5. Exact interfaces to Books 166--167 and 181

### 5.1 Input to supported cohomology

For the Frey-SP specialization, Book 166 uses the following data and no
stronger local assertion.  Let

$$
M=\operatorname{ad}^0\bar\rho,
\qquad M'=M(1),
\qquad
\mathcal L=(L_2,L_\ell,L_\infty).
$$

The exported local ledger is

| Place | Tangent condition | Invariants and correction |
|---|---|---|
| $2$ | $L_2=0$ | $H^i(\mathbf Q_2,M)=H^i(\mathbf Q_2,M')=0$ for $i=0,1,2$ |
| $\ell$ | $L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)$ | $\dim L_\ell=h_\ell$ and $h^0(\mathbf Q_\ell,M)=h_\ell-1$ |
| $\infty$ | $L_\infty=0$ | oddness gives $h^0(\mathbf R,M)=1$ and $H^1(\mathbf R,M)=0$ |

Therefore

$$
\dim L_2-h^0(\mathbf Q_2,M)=0, \tag{5.1}
$$

$$
\dim L_\ell-h^0(\mathbf Q_\ell,M)=1, \tag{5.2}
$$

and

$$
\dim L_\infty-h^0(\mathbf R,M)=-1. \tag{5.3}
$$

The last two corrections cancel.  Global absolute irreducibility gives
$H^0(G_{\mathbf Q,S},M)=0$, while restriction to $G_{\mathbf Q_2}$ and
(2.18) give

$$
H^0(G_{\mathbf Q,S},M(1))=0. \tag{5.4}
$$

These are exactly the local and endpoint inputs for the Greenberg--Wiles
and supported-duality calculation.  Book 166 defines the dual local
condition at $\ell$ as the exact Tate orthogonal $L_\ell^\perp$; this book
does not relabel that orthogonal as another finite-flat deformation functor.

### 5.2 Input to relation obstructions

For its Frey-SP specialization, Book 167 needs nonlinear local conditions,
not only the subspaces in Section 5.1.  The precise exports are:

1. the framed dyadic and coefficient-prime conditions are represented by
   closed quotients;
2. both lift through every small extension;
3. their lift torsors and difference cocycles commute with pushout of the
   small-extension kernel;
4. at $2$ the ambient obstruction group vanishes;
5. at $\ell$ only the **restricted** finite-flat obstruction map is proved
   zero.

Thus local factor sets admit the nullhomotopies required for the supported
mapping fiber.  Nothing here identifies supported degree two with ordinary
global $H^2$, and nothing here proves that every tuple of local corrections
comes from a global correction.

The possible nonscalar local centralizer at $\ell$ causes no gap.  Book 167
uses the represented framed ring (3.20), while the global unframed ring is
justified by global absolute irreducibility.  A nonexistent local coarse
ring is never inserted into a fiber product.

### 5.3 Input to the balanced lift argument

Book 181 receives:

- the represented global ring $R^{\mathrm{hr,SP}}$ and its universal
  strict-equivalence class;
- the exact dyadic equations (2.4)--(2.5), intrinsic line (2.6), sign $s$,
  determinant, and conductor-one consequence;
- the coefficient-prime condition as compatible finite-flat models on all
  Artinian quotients;
- stability under finite extension of coefficient rings;
- preservation of both local problems after restriction to a totally real
  field split completely at $2$ and $\ell$;
- the tangent and obstruction inputs already passed through Books 166--167.

Book 181 treats its additional restricted reduced-finiteness hypothesis
**(RF)** separately.  This book exports only the Galois local conditions and
the represented global deformation functor; it neither proves nor assumes
(RF).

### 5.4 Non-exports

This book does not prove any of the following:

- residual potential modularity or automorphy;
- Book 181's restricted reduced-finiteness hypothesis (RF);
- an $R=T$ theorem, finite scalar fibre, or characteristic-zero point;
- global smoothness or vanishing of the global obstruction group;
- ambient $H^2$-vanishing at $\ell$;
- a local deformation theorem for a different dyadic inertial profile.

In particular, a downstream statement that allows an additional dyadic
branch must source that branch from its own local theorem.  The interface of
this book to Books 166--167 and 181 is exactly the Frey-special specialization
recorded in Sections 5.1--5.3; no different local profile may be substituted
for the conductor-one Frey transvection.

## 6. The theorem package and dependency audit

### 6.1 Main theorem

**Theorem 6.1 (local conditions for the hardly-ramified Frey minimal
problem).** Let $\ell\geq7$, let $\mathcal O$ and $k$ be as in Section
1.2, and let $\bar\rho$ satisfy the six hypotheses of Section 4.1.  Then:

1. The equations (2.4)--(2.5), fixed cyclotomic determinant, intrinsic
   monodromy line, and sign $s$ define a closed, coefficient-stable,
   conductor-one minimal-special condition at $2$.

2. Its unframed functor is represented by $\mathcal O$, its framed functor
   is represented by $\mathcal O[[Y_1,Y_2,Y_3]]$, and both are formally
   smooth.  Its tangent is $L_2=0$.

3. For $M=\operatorname{ad}^0\bar\rho$,
   $$
   H^0(\mathbf Q_2,M)=H^1(\mathbf Q_2,M)
   =H^2(\mathbf Q_2,M)=0,
   $$
   and
   $$
   H^0(\mathbf Q_2,M(1))=H^1(\mathbf Q_2,M(1))
   =H^2(\mathbf Q_2,M(1))=0.
   $$

4. Coefficient-linear finite flatness over $\mathbf Z_\ell$ with
   determinant $\chi_\ell$ is a closed condition stable under every
   Artinian coefficient map.  Its framed ring is
   $$
   R_\ell^{\square,\mathrm{fl},\chi}
   \simeq\mathcal O[[Z_1,Z_2,Z_3,Z_4]].
   $$

5. If
   $$
   h_\ell
   =\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V),
   $$
   then
   $$
   \dim_kH^1_{\mathrm{fl}}(\mathbf Q_\ell,M)=h_\ell.
   $$
   If $h_\ell=1$, the unframed ring is $\mathcal O[[X]]$.  If
   $h_\ell>1$, the framed theorem remains valid but no coarse unframed
   universal ring is asserted.

6. The finite-flat condition lifts through every small extension.  Its
   restricted obstruction map is zero even when
   $H^2(\mathbf Q_\ell,M)$ is nonzero.

7. The global functor (4.3)--(4.6) is represented by
   $R^{\mathrm{hr,SP}}$, and its tangent is the localization kernel (4.9).

8. The exact downstream interface is the ledger of Sections 5.1--5.3.  In
   particular, the local theorem supplies neither Book 181's hypothesis
   (RF) nor a characteristic-zero global point.

**Proof.** Parts 1--3 are Lemma 2.1, Theorem 2.2, the conductor calculation
(2.14), and the cohomology calculation (2.15)--(2.21).  Parts 4--6 are the
coefficient-stability construction, the low-weight classification, the
tangent complex (3.9)--(3.17), and the explicit small-extension lift of
Section 3.4; these specialize Book 68, Theorems 2.3, 14.3, 16.1, and 17.1,
to $\mathbf Q_\ell$.  Part 7 is Theorem 4.1 and the dual-number calculation
(4.8)--(4.9).  Part 8 merely records those proved outputs without adding a
new theorem. $\square$

### 6.2 Hypothesis and boundary ledger

| Hypothesis | Exact use | Failure if removed |
|---|---|---|
| $\ell\geq7$ | odd trace splitting, dyadic twisted eigenvalue $4\ne1$, and the Frey exponent range | characteristics $2$ and $3$ change the determinant or cohomology; the global range at $5$ is not asserted |
| $\bar N\ne0$ at $2$ | intrinsic direct-summand line and closed nonzero-monodromy locus | with $\bar N=0$, nonzero monodromy is open and the closed special chart contains an unramified divisor |
| named sign $s$ | fixes the unramified Steinberg twist | determinant and conductor alone do not distinguish split from nonsplit multiplicative reduction |
| determinant $\chi_\ell$ | fixes $a=s$ at $2$ and forces one Hodge line at $\ell$ | an unramified scalar parameter remains at $2$, and the coefficient-prime Hodge ranks and tangent count change |
| actual finite-flat model | supplies integral middle extensions and coefficient quotients | rational Hodge labels or finite-flat endpoints do not control the middle representation |
| base $\mathbf Z_\ell$ | Raynaud uniqueness and the unramified weight-$[0,1]$ coordinates | over a ramified base the power-series and tangent formulas are not proved |
| global absolute irreducibility | global Schur condition and unframed universal ring | only a framed global ring or a hull is automatic |
| arithmetic Frobenius | dyadic eigenvalues $2$ and $4$ | geometric Frobenius inverts the displayed eigenvalues and must be used consistently |

Two local facts hold in a wider range than the theorem: the nonzero-monodromy
normal form works whenever the determinant square root is transverse, and
the finite-flat theorem works for every odd $\ell$ over an unramified base.
The book does not splice those wider local ranges into the FLT package.  At
$\ell=5$ the displayed local computations are favorable, but the later
global image and modularity machinery is stated uniformly for
$\ell\geq7$.

### 6.3 Direct prerequisites and circularity audit

The proof uses only foundational mathematics and books preceding this one.

| Source | Imported result | Use here |
|---|---|---|
| Books 30--31 | local Euler characteristic and Tate duality, including $H^2\simeq H^0(M^*(1))^*$ | Section 2.5 |
| Book 32, Section 3.2 | finiteness of $H^1(G_{\mathbf Q,S},M)$ for finite coefficients and a controlling set containing the coefficient prime | Section 4.2 |
| Book 44 | Tate-curve inertia, Frobenius sign, and conductor of a rank-one monodromy block | Sections 1.3 and 2.5 |
| Books 63 and 66 | strict equivalence, tangent and obstruction theory, scalar-centralizer representability, and closed global quotients | Sections 1.4, 2.4, 3.4, and 4.2 |
| Book 67, Theorem 7.1 | closed and liftable nonzero-monodromy minimal condition | Section 2.4 |
| Book 68, Theorems 2.3, 9.1--9.2, 14.3, 16.1, and 17.1 | coefficient change, finite-flat classification, representability, liftability, tangent dimensions, and smooth rings | Chapter 3 |
| Book 164, Sections 3.1, 4.3, and 5.2 | normalized Frey equation, dyadic discriminant and sign, and nonzero residual monodromy | Section 1.3 |

The key normal forms, tangent dimensions, and obstruction distinctions are
reproved in this book after the deep integral classifications are imported.
Book 68 discharges the lower-level integral inputs on closure, Raynaud
rigidity, and Fontaine--Laffaille theory; this book invokes its packaged
theorems rather than silently strengthening them.  No result from Books 166--167 or 181 is used to prove Theorem 6.1.  Those books consume the outputs
listed in Chapter 5.

There is therefore no hidden conditional theorem in the local package.
The later global conclusion remains external: Book 181 states the additional
restricted reduced-finiteness hypothesis (RF) under which its balanced ring
argument produces a characteristic-zero point.

### 6.4 Conclusion

The hardly-ramified Frey problem has one dyadic branch.  Nonzero residual
monodromy recovers its line, Frobenius scales the monodromy by $2$, and the
cyclotomic determinant plus the residual sign removes the final unramified
parameter.  The dyadic unframed ring is therefore $\mathcal O$, its framed
ring has only three change-of-frame variables, and its adjoint tangent and
obstruction groups vanish.  The conductor is exactly one.

At the coefficient prime, finite flatness is genuinely integral.  Raynaud
rigidity and the weight-$[0,1]$ classification turn it into one Hodge line
and one invertible divided-Frobenius matrix.  Their tangent complex gives
$\dim L_\ell=h_\ell$, while an explicit determinant correction lifts every
small-extension problem.  The framed ring is always a four-variable power
series ring; a coarse unframed ring is asserted only in the Schur local
case.

These local conditions cut out the universal global quotient whose tangent
is (4.9).  They supply exact local nullhomotopies and dimension corrections,
but no global lift by themselves.  That boundary is the correct interface:
Book 166 performs the supported cohomology calculation, Book 167 converts
relations into supported obstructions, and Book 181 adds its separately
stated restricted reduced-finiteness input.  The local deformation node is
complete without importing any conclusion from those later stages.
