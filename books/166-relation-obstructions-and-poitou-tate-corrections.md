# Relation Obstructions and Poitou--Tate Corrections

## Contents

- [1. The exact deformation problem and the result](#1-the-exact-deformation-problem-and-the-result)
  - [1.1 Standing data](#11-standing-data)
  - [1.2 Local conditions and coefficient modules](#12-local-conditions-and-coefficient-modules)
  - [1.3 The theorem proved here](#13-the-theorem-proved-here)
- [2. Minimal presentations and relation directions](#2-minimal-presentations-and-relation-directions)
  - [2.1 Small extensions](#21-small-extensions)
  - [2.2 Minimal variables and the conormal relation space](#22-minimal-variables-and-the-conormal-relation-space)
  - [2.3 The relation-socle extension](#23-the-relation-socle-extension)
- [3. The fixed-determinant factor set](#3-the-fixed-determinant-factor-set)
  - [3.1 Determinant-compatible matrix lifts](#31-determinant-compatible-matrix-lifts)
  - [3.2 Cocycle and sign calculations](#32-cocycle-and-sign-calculations)
  - [3.3 Unrestricted completeness](#33-unrestricted-completeness)
  - [3.4 Why the coefficient is the trace-zero adjoint](#34-why-the-coefficient-is-the-trace-zero-adjoint)
- [4. Local lift groupoids and the supported obstruction](#4-local-lift-groupoids-and-the-supported-obstruction)
  - [4.1 The dyadic SP and coefficient-prime inputs](#41-the-dyadic-sp-and-coefficient-prime-inputs)
  - [4.2 Positive local complexes](#42-positive-local-complexes)
  - [4.3 The mapping fiber and its sign](#43-the-mapping-fiber-and-its-sign)
  - [4.4 Construction and choice independence](#44-construction-and-choice-independence)
  - [4.5 Completeness](#45-completeness)
- [5. The Poitou--Tate correction term](#5-the-poitou--tate-correction-term)
  - [5.1 The affine mismatch](#51-the-affine-mismatch)
  - [5.2 The exact correction functional](#52-the-exact-correction-functional)
  - [5.3 The two layers of supported degree two](#53-the-two-layers-of-supported-degree-two)
- [6. From relation functionals to supported obstructions](#6-from-relation-functionals-to-supported-obstructions)
  - [6.1 The universal relation obstruction](#61-the-universal-relation-obstruction)
  - [6.2 Pro-Artinian effectiveness](#62-pro-artinian-effectiveness)
  - [6.3 Injectivity and variance](#63-injectivity-and-variance)
- [7. The balanced hardly-ramified bound](#7-the-balanced-hardly-ramified-bound)
  - [7.1 The local correction ledger](#71-the-local-correction-ledger)
  - [7.2 Relations versus variables](#72-relations-versus-variables)
  - [7.3 The exact interface to Book 181](#73-the-exact-interface-to-book-181)
- [8. Dependency and hostile audit](#8-dependency-and-hostile-audit)
  - [8.1 Imported results](#81-imported-results)
  - [8.2 Sign, degree, and variance ledger](#82-sign-degree-and-variance-ledger)
  - [8.3 Forbidden inferences](#83-forbidden-inferences)

## 1. The exact deformation problem and the result

### 1.1 Standing data

Let \(\ell\geq 7\), let \(\mathcal O\) be the ring of integers in a finite
extension of \(\mathbf Q_\ell\), let \(\varpi\) be a uniformizer, and let
\(k\) be the residue field. Fix a continuous representation

$$
\bar\rho:G_{\mathbf Q}\longrightarrow \operatorname{GL}_2(k) \tag{1.1}
$$

which is absolutely irreducible and odd, has determinant
\(\bar\chi_\ell\), is unramified outside \(\{2,\ell\}\), has the
minimal-special Frey condition SP from Book 164 at \(2\), and is
coefficient-linearly finite flat at \(\ell\).

Put

$$
S=\{2,\ell,\infty\},\qquad
M=\operatorname{ad}^0\bar\rho,\qquad
M'=M^*(1)\simeq M(1). \tag{1.2}
$$

The last identification uses the trace pairing. It is valid because \(2\)
is invertible in \(k\); it is also the reason that fixed-determinant
factor sets take values in \(M\), rather than in the full adjoint module.

Book 164, Theorem 4.1, constructs the represented global deformation functor
\(D^{\mathrm{hr,SP}}\) of strict-equivalence classes of lifts with determinant
\(\chi_\ell\), the SP condition at \(2\), the coefficient-linear finite-flat
condition at \(\ell\), and no ramification elsewhere. Throughout, write

$$
D_{\mathrm{hr}}=D^{\mathrm{hr,SP}},
\qquad
R_{\mathrm{hr}}=R^{\mathrm{hr,SP}}
$$

for its universal complete Noetherian local \(\mathcal O\)-algebra. Nothing
in this book assumes that \(R_{\mathrm{hr}}\) is finite, flat, reduced, a
complete intersection, or has a characteristic-zero point.

### 1.2 Local conditions and coefficient modules

The fixed-determinant tangent conditions are

$$
L_2=0,\qquad
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),\qquad
L_\infty=0. \tag{1.3}
$$

At every finite prime outside \(S\), unramifiedness is already imposed by
using \(G_{\mathbf Q,S}\). For \(v\in S\), let

$$
L_v^\perp\subseteq H^1(\mathbf Q_v,M') \tag{1.4}
$$

be the exact orthogonal for local Tate duality, not merely a subspace of the
expected dimension.

Book 165 constructs the supported mapping fiber
\(C^\bullet_{\mathrm{hr}}(\mathbf Q,M)\), proves the perfect pairing

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*, \tag{1.5}
$$

and proves the balanced equality

$$
\dim_k H^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim_k H^1_{\mathrm{hr}}(\mathbf Q,M). \tag{1.6}
$$

We reconstruct the part of the mapping fiber needed for obstruction theory,
including its signs, and show that it is a complete obstruction space for
the represented functor. Formula (1.5) is then used with its stated
variance.

### 1.3 The theorem proved here

**Theorem 1.1 (relation obstruction theorem for the hardly-ramified
problem).** Let

$$
P=\mathcal O[[X_1,\ldots,X_t]]
\twoheadrightarrow R_{\mathrm{hr}},\qquad J=\ker(P\to R_{\mathrm{hr}}),
\tag{1.7}
$$

be minimal in its variables, and let
\(\mathfrak n=(\varpi,X_1,\ldots,X_t)\). Then:

1. every small-extension lifting problem for \(D_{\mathrm{hr}}\) has a
   functorial class in
   \(H^2_{\mathrm{hr}}(\mathbf Q,M)\) tensored with the square-zero kernel;
2. that class vanishes if and only if a global lift satisfying the SP
   condition and the coefficient-linear finite-flat condition exists;
3. the affine local correction is exact: a family of local mismatches is
   globally correctable if and only if its Poitou--Tate pairing with every
   class in \(H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')\) is zero;
4. there is an injective, presentation-relative map

   $$
   (J/\mathfrak nJ)^*
   \hookrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M)
   \simeq H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*; \tag{1.8}
   $$

5. consequently, if \(r=\dim_kJ/\mathfrak nJ\), then

   $$
   r\leq \dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)=t. \tag{1.9}
   $$

The adjective *presentation-relative* in (1.8) is deliberate. The chosen
minimal presentation supplies its conormal space. The dimension \(r\) is
intrinsic, but no unique coordinate-free identification between conormal
spaces of two unrelated presentations is asserted.

## 2. Minimal presentations and relation directions

### 2.1 Small extensions

A surjection of Artinian local \(\mathcal O\)-algebras

$$
A'\twoheadrightarrow A \tag{2.1}
$$

is a **small extension** if its kernel \(I\) satisfies

$$
\mathfrak m_{A'}I=0. \tag{2.2}
$$

Then \(I\) is a finite-dimensional \(k\)-vector space and \(I^2=0\). In
particular,

$$
(1+X)(1+Y)=1+X+Y
\qquad (X,Y\in M_2(I)). \tag{2.3}
$$

All deformation obstructions below are linear in \(I\). A map
\(I\to I'\) pushes an obstruction forward, and a decomposition of \(I\)
decomposes the obstruction into its components.

### 2.2 Minimal variables and the conormal relation space

The relative tangent space of the represented functor is

$$
T_{\mathrm{hr}}
=H^1_{\mathrm{hr}}(\mathbf Q,M). \tag{2.4}
$$

Choose the variables in (1.7) so that their classes give a basis of the
relative cotangent space of \(R_{\mathrm{hr}}\). Thus

$$
t=\dim_kT_{\mathrm{hr}}. \tag{2.5}
$$

Minimality of the variables is equivalent to the absence of a relative
linear term in every element of \(J\):

$$
J\subseteq \varpi P+\mathfrak n^2. \tag{2.6}
$$

The **conormal relation space** for this presentation is

$$
\operatorname{Rel}_P(R_{\mathrm{hr}})
=J/\mathfrak nJ. \tag{2.7}
$$

It is finite-dimensional. Nakayama's lemma gives

$$
r:=\dim_kJ/\mathfrak nJ
=\text{the minimal number of generators of }J. \tag{2.8}
$$

The space that maps covariantly to obstructions is its dual:

$$
\operatorname{Rel}^{\mathrm{ob}}_P(R_{\mathrm{hr}})
=(J/\mathfrak nJ)^*. \tag{2.9}
$$

A functional, rather than an equation, selects a one-dimensional quotient
of a square-zero relation kernel. This fixes the variance used in (1.8).

### 2.3 The relation-socle extension

Set

$$
\mathcal R=J/\mathfrak nJ,
\qquad B=P/\mathfrak nJ. \tag{2.10}
$$

There is an exact sequence of complete local \(\mathcal O\)-algebras

$$
0\longrightarrow \mathcal R
\longrightarrow B\xrightarrow{q}R_{\mathrm{hr}}
\longrightarrow0. \tag{2.11}
$$

The kernel is an ideal, is square zero, and is killed by the maximal ideal
of \(B\). Thus (2.11) is a small extension in the pro-Artinian sense. This
does **not** mean that \(R_{\mathrm{hr}}\) is Artinian. It means that for all
sufficiently large \(N\), Krull intersection gives

$$
\mathcal R\cap\mathfrak m_B^N=0, \tag{2.12}
$$

and reduction produces an honest small extension of Artinian rings

$$
0\longrightarrow\mathcal R
\longrightarrow B/\mathfrak m_B^N
\longrightarrow R_{\mathrm{hr}}/\mathfrak m_{R_{\mathrm{hr}}}^N
\longrightarrow0. \tag{2.13}
$$

For \(\lambda\in\mathcal R^*\), put

$$
J_\lambda=
\{j\in J:\lambda(j\bmod\mathfrak nJ)=0\},
\qquad B_\lambda=P/J_\lambda. \tag{2.14}
$$

Because \(\mathfrak nJ\subseteq J_\lambda\), the set \(J_\lambda\) is an
ideal. If \(\lambda\ne0\), then

$$
0\longrightarrow I_\lambda\simeq k
\longrightarrow B_\lambda
\xrightarrow{q_\lambda}R_{\mathrm{hr}}
\longrightarrow0 \tag{2.15}
$$

is the one-dimensional quotient of (2.11) selected by \(\lambda\).

## 3. The fixed-determinant factor set

### 3.1 Determinant-compatible matrix lifts

Let (2.1) be a small extension and let

$$
\rho_A:G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(A) \tag{3.1}
$$

be a deformation with determinant \(\chi_\ell\). Choose matrices
\(\widetilde\rho(g)\in\operatorname{GL}_2(A')\) lifting \(\rho_A(g)\),
normalized by \(\widetilde\rho(1)=1\), and satisfying

$$
\det\widetilde\rho(g)=\chi_\ell(g). \tag{3.2}
$$

Such choices exist. Starting from any matrix lift, its determinant differs
from (3.2) by \(1+e\), with \(e\in I\). Multiplication by the scalar
\(1-e/2\) removes the discrepancy because
\(\det(1+u)=1+2u\) for a scalar square-zero \(u\). This is where odd
residue characteristic enters.

Continuity causes no hidden problem. The joint map

$$
g\longmapsto\bigl(\rho_A(g),\chi_\ell(g)\bmod A'\bigr) \tag{3.3}
$$

has finite image. Choose the determinant-compatible matrix lift on that
finite image and compose with (3.3). No discontinuous section of an
infinite topological group is used.

Define the multiplicative defect by

$$
\widetilde\rho(g)\widetilde\rho(h)
\widetilde\rho(gh)^{-1}=1+c(g,h). \tag{3.4}
$$

Here

$$
c(g,h)\in M_2(k)\otimes_k I, \tag{3.5}
$$

with \(G_{\mathbf Q,S}\) acting by conjugation through \(\bar\rho\).

### 3.2 Cocycle and sign calculations

From (3.4),

$$
\widetilde\rho(g)\widetilde\rho(h)
=(1+c(g,h))\widetilde\rho(gh). \tag{3.6}
$$

Associating a triple product in the two possible ways and using \(I^2=0\)
gives

$$
c(g,h)+c(gh,r)
=g\cdot c(h,r)+c(g,hr). \tag{3.7}
$$

Thus \(dc=0\) for the inhomogeneous differential

$$
(db)(g,h)=b(g)+g b(h)-b(gh). \tag{3.8}
$$

The order in (3.4) is important. If the matrix section is changed on the
left by

$$
\widetilde\rho'(g)=(1+b(g))\widetilde\rho(g), \tag{3.9}
$$

then direct multiplication gives

$$
c'=c+db. \tag{3.10}
$$

Consequently a correction by \(1-b(g)\) kills the factor set when
\(c=db\). Reversing the order in (3.4), or correcting on the right, would
change these displayed formulas; neither convention is used here.

### 3.3 Unrestricted completeness

If \(\rho_A\) has an honest determinant-compatible lift to \(A'\), choose
it as the section and obtain \(c=0\). Conversely, if

$$
[c]=0\in H^2(G_{\mathbf Q,S},M)\otimes_k I, \tag{3.11}
$$

choose \(b\in C^1(G_{\mathbf Q,S},M)\otimes I\) with \(c=db\). Then

$$
\rho_{A'}(g)=(1-b(g))\widetilde\rho(g) \tag{3.12}
$$

is a representation with the prescribed determinant. Hence ordinary
\(H^2\) is a complete obstruction space for the unrestricted
fixed-determinant problem.

If one honest lift exists, the difference between two honest lifts is a
\(1\)-cocycle in \(M\otimes I\). Strict conjugation changes that cocycle by
a coboundary. Thus strict-equivalence classes of unrestricted lifts form a
torsor under \(H^1(G_{\mathbf Q,S},M)\otimes I\).

### 3.4 Why the coefficient is the trace-zero adjoint

Taking determinants in (3.4) gives \(\det(1+c(g,h))=1\). For a square-zero
matrix,

$$
\det(1+X)=1+\operatorname{tr}(X), \tag{3.13}
$$

so

$$
\operatorname{tr}c(g,h)=0. \tag{3.14}
$$

The factor set therefore lies in \(M\otimes I\). A correction preserves
the determinant precisely when its cochain is trace zero. If a trace-zero
cocycle is first found to be a coboundary in the full adjoint complex, the
splitting

$$
\operatorname{ad}\bar\rho=kI\oplus\operatorname{ad}^0\bar\rho \tag{3.15}
$$

projects a primitive to a trace-zero primitive. There is no lost scalar
obstruction. This argument fails in characteristic two and is not used
there.

## 4. Local lift groupoids and the supported obstruction

### 4.1 The dyadic SP and coefficient-prime inputs

The local statements used here are the exact outputs of Book 164, Theorem
6.1 and Sections 5.1--5.2.

For the Frey minimal-special condition, after a fixed residual normalization,

$$
\bar\rho(\sigma)=1+\overline t_\ell(\sigma)\bar N,
\qquad \bar N^2=0,\qquad \bar N\ne0, \tag{4.1}
$$

and arithmetic Frobenius satisfies

$$
\bar F\bar N\bar F^{-1}=2\bar N. \tag{4.2}
$$

The lift condition retains the nonzero rank-one nilpotent, its intrinsic
line, its named unramified sign, the equation \(FNF^{-1}=2N\), and the
cyclotomic determinant. Its unframed ring is \(\mathcal O\), its framed ring
is \(\mathcal O[[Y_1,Y_2,Y_3]]\), and it lifts through every small
extension. In particular,

$$
L_2=0. \tag{4.3}
$$

The trace-zero inertia invariants are \(k\bar N\). Frobenius acts on this
line by \(2\), and on its Tate twist by \(4\). Since \(\ell\geq7\),

$$
H^0(\mathbf Q_2,M)=H^0(\mathbf Q_2,M')=0. \tag{4.4}
$$

Book 164's adjoint calculation, equivalently local duality and the
away-from-\(\ell\) Euler formula applied to (4.4), gives the full vanishing

$$
H^i(\mathbf Q_2,M)=H^i(\mathbf Q_2,M')=0
\qquad(0\leq i\leq2). \tag{4.5}
$$

Thus SP rigidity is not a slogan about conductor: it is the precise
nonzero-monodromy local functor whose degree-one and ambient degree-two
groups vanish.

At \(\ell\), the condition is coefficient-linear finite flat of weight
\(\{0,1\}\), with determinant \(\chi_\ell\). It lifts through every small
extension by lifting the Hodge line and divided Frobenius and correcting the
determinant. If

$$
h_\ell=
\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V), \tag{4.6}
$$

then

$$
\dim_k L_\ell=h_\ell,
\qquad
\dim_kH^0(\mathbf Q_\ell,M)=h_\ell-1. \tag{4.7}
$$

The framed finite-flat local ring is smooth in four variables. If
\(h_\ell>1\), no coarse unframed local universal ring is inferred. This
does not harm the global problem: the framed local lift groupoid has the
required deformation and automorphism complexes.

Most importantly, local finite-flat liftability does **not** imply

$$
H^2(\mathbf Q_\ell,M)=0. \tag{4.8}
$$

The ambient group in (4.8) may be nonzero. What vanishes is the obstruction
map of the finite-flat subfunctor.

At infinity, \(2\) is invertible in \(k\). The complete Tate complex is
acyclic, oddness has no tangent direction, and there is no local lifting
obstruction. The ordinary invariant line \(H^0(\mathbf R,M)\), however,
still contributes to the Euler characteristic in Chapter 7.

### 4.2 Positive local complexes

For a finite \(v\in S\), let \(C_v^\bullet(M)\) be the continuous
inhomogeneous cochain complex and set

$$
Z^1_{L_v}(M)
=\{z\in Z^1(\mathbf Q_v,M):[z]\in L_v\}. \tag{4.9}
$$

The positive local complex is

$$
U_v^+(M):
C_v^0(M)\xrightarrow{d}Z^1_{L_v}(M), \tag{4.10}
$$

in degrees \(0\) and \(1\). It records both strict local changes of frame
and admissible tangent displacements. Its cohomology is

$$
H^0(U_v^+)=H^0(\mathbf Q_v,M),
\qquad H^1(U_v^+)=L_v. \tag{4.11}
$$

Define the unshifted quotient cone

$$
U_v^-(M)=\operatorname{Cone}
\bigl(U_v^+(M)\longrightarrow C_v^\bullet(M)\bigr). \tag{4.12}
$$

With the cone convention used here,

$$
H^1(U_v^-)=H^1(\mathbf Q_v,M)/L_v,
\qquad H^2(U_v^-)=H^2(\mathbf Q_v,M). \tag{4.13}
$$

At infinity we use the acyclic complete complex, which contributes no
positive-degree obstruction coordinate in the present odd-characteristic
problem.

The statement that local lifts form a torsor must be made at this complex
level. Framed admissible lifts over a fixed small extension are acted on by
\(Z^1_{L_v}(M)\otimes I\); degree-zero cochains change the frame. After
passing to strict-equivalence classes, the difference class lies in
\(L_v\otimes I\). At a split coefficient-prime residual representation this
groupoid statement remains valid even though a coarse unframed local ring
need not exist.

### 4.3 The mapping fiber and its sign

Let

$$
Q_{\mathrm{hr}}^\bullet(M)
=\bigoplus_{v\in S}U_v^-(M) \tag{4.14}
$$

and let

$$
\lambda_{\mathrm{hr}}:
C^\bullet(G_{\mathbf Q,S},M)
\longrightarrow Q_{\mathrm{hr}}^\bullet(M) \tag{4.15}
$$

be localization followed by the quotient maps. Define

$$
C_{\mathrm{hr}}^\bullet(\mathbf Q,M)
=\operatorname{Cone}(\lambda_{\mathrm{hr}})[-1]. \tag{4.16}
$$

Thus

$$
C_{\mathrm{hr}}^q
=C^q(G_{\mathbf Q,S},M)
\oplus Q_{\mathrm{hr}}^{q-1}(M), \tag{4.17}
$$

with differential

$$
d_{\mathrm{hr}}(x,y)
=(dx,\lambda_{\mathrm{hr}}(x)-dy). \tag{4.18}
$$

Consequently a pair \((c,y)\) of degrees \((2,1)\) is closed exactly when

$$
dc=0,
\qquad dy=\lambda_{\mathrm{hr}}(c). \tag{4.19}
$$

This equation fixes the sign of the local nullhomotopy.

### 4.4 Construction and choice independence

Return to a small extension \(A'\to A\), a deformation \(\rho_A\), and the
factor set \(c\) of Chapter 3. Local liftability supplies an admissible
local representation \(\rho_v^{\mathrm{adm}}\) over \(A'\) at \(2\) and
\(\ell\). Compare it with the restricted matrix section by writing

$$
\rho_v^{\mathrm{adm}}(g)
=(1+b_v(g))\widetilde\rho(g)|_{G_{\mathbf Q_v}}. \tag{4.20}
$$

Both sides have the prescribed determinant, so \(b_v\) is trace zero. The
left side is multiplicative. Formula (3.10) therefore gives

$$
\operatorname{loc}_v(c)+db_v=0. \tag{4.21}
$$

Set

$$
y_v=-b_v. \tag{4.22}
$$

Then \(dy_v=\operatorname{loc}_v(c)\), exactly as required by (4.19). The
images of the \(y_v\) in the quotient cones define a supported cocycle

$$
(c,y)\in Z^2(C_{\mathrm{hr}}^\bullet)\otimes_k I \tag{4.23}
$$

and hence an obstruction

$$
\operatorname{ob}_{\mathrm{hr}}(\rho_A,A')
=[(c,y)]
\in H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes_k I. \tag{4.24}
$$

All choices disappear for explicit reasons.

If the global matrix section is changed by \(1+a\), then
\(c'=c+da\). Keeping the same admissible local lift changes
\(b_v\) to \(b_v-a|_v\), and hence

$$
y'=y+\lambda_{\mathrm{hr}}(a). \tag{4.25}
$$

Therefore

$$
(c',y')-(c,y)=d_{\mathrm{hr}}(a,0). \tag{4.26}
$$

Changing the admissible local lift adds an element of
\(Z^1_{L_v}(M)\otimes I\) to \(b_v\). Its image is a boundary in the
quotient cone \(U_v^-\). Changing a local rigidification adds a local
coboundary and is likewise a quotient-cone boundary. Thus (4.24) is
independent of the matrix section, the admissible local base points, and all
rigidifications. The same formulas prove additivity and functoriality in
\(I\).

### 4.5 Completeness

**Proposition 4.1 (complete supported obstruction).** The class (4.24)
vanishes if and only if \(\rho_A\) lifts to a deformation over \(A'\)
satisfying every local condition.

**Proof.** If an admissible global lift exists, take it as the global matrix
section and take its restrictions as the admissible local lifts. Then
\((c,y)=(0,0)\).

Conversely, suppose \([(c,y)]=0\). By (4.18), there are a global
\(1\)-cochain \(a\) and a family \(z\in Q_{\mathrm{hr}}^0(M)\otimes I\)
such that

$$
c=da,
\qquad y=\lambda_{\mathrm{hr}}(a)-dz. \tag{4.27}
$$

Replace the global matrix section by \((1-a)\widetilde\rho\). Equations
(3.10) and (4.27) make it an honest determinant-compatible global
representation. Its local difference from the chosen admissible lift has
zero class in \(H^1(U_v^-)\): the new supported coordinate is
\(y-\lambda_{\mathrm{hr}}(a)=-dz\), while the actual mismatch cocycle has
the opposite sign and is \(dz\). Either is a quotient-cone boundary. By
(4.13), that says precisely that, after a strict local conjugacy, the
difference cocycle lies in \(L_v\).

The local lift-groupoid property of Section 4.2 now finishes the argument.
On SP, \(L_2=0\), so the restriction is strictly equivalent to the unique
admissible class. At \(\ell\), displacement by a class of \(L_\ell\) stays
inside the coefficient-linear finite-flat lift groupoid. Hence the corrected
global representation satisfies both local conditions. \(\square\)

The proposition is stronger than ordinary factor-set vanishing. It rules
out both a nonzero global factor set and a failure to move an honest global
lift into the prescribed local lift groupoids.

## 5. The Poitou--Tate correction term

### 5.1 The affine mismatch

Suppose the ordinary factor-set class vanishes and choose an honest global
lift \(\rho^{\mathrm{glob}}\) over \(A'\). Choose an admissible local lift
\(\rho_v^{\mathrm{adm}}\). Their ratio is a cocycle:

$$
\rho_v^{\mathrm{adm}}(g)
=(1+q_v(g))\rho^{\mathrm{glob}}(g),
\qquad q_v\in Z^1(\mathbf Q_v,M)\otimes I. \tag{5.1}
$$

Changing the admissible local lift changes \([q_v]\) by
\(L_v\otimes I\). Changing the global lift to
\((1+x)\rho^{\mathrm{glob}}\), for a global cocycle \(x\), changes the
mismatch by

$$
[q_v]\longmapsto[q_v]-\operatorname{loc}_v[x]. \tag{5.2}
$$

Thus the intrinsic mismatch lies in

$$
Q_{\mathrm{hr}}(M)
=\frac{H^1(\mathbf Q_2,M)}{L_2}
\oplus
\frac{H^1(\mathbf Q_\ell,M)}{L_\ell}. \tag{5.3}
$$

There is no positive real term for odd \(\ell\). On SP, (4.5) and
\(L_2=0\) simplify (5.3) to

$$
Q_{\mathrm{hr}}(M)
\simeq H^1(\mathbf Q_\ell,M)/L_\ell. \tag{5.4}
$$

The mismatch is correctable by a global change if and only if its class is
in the image of

$$
H^1(G_{\mathbf Q,S},M)
\longrightarrow Q_{\mathrm{hr}}(M). \tag{5.5}
$$

### 5.2 The exact correction functional

For \(\bar q=(q_v+L_v)_v\in Q_{\mathrm{hr}}(M)\), define

$$
\Theta_{\mathrm{hr}}(\bar q)(y)
=\sum_{v\in S}
\operatorname{inv}_v
\bigl(q_v\smile\operatorname{loc}_v(y)\bigr),
\quad
y\in H^1_{\mathrm{hr}^\perp}(\mathbf Q,M'). \tag{5.6}
$$

The coefficient order is \(M\) first and \(M'=M^*(1)\) second. The cup
has degree two and values in the Tate line. We use arithmetic Frobenius and
the corresponding normalized local invariant. Reversing the two degree-one
arguments would introduce the graded minus sign; no reversal is made in
(5.6).

Formula (5.6) is well defined because
\(\operatorname{loc}_v(y)\in L_v^\perp\). Book 165's supported
Poitou--Tate theorem gives the exact segment

$$
H^1(G_{\mathbf Q,S},M)
\longrightarrow Q_{\mathrm{hr}}(M)
\xrightarrow{\Theta_{\mathrm{hr}}}
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*
\longrightarrow H^2(G_{\mathbf Q,S},M). \tag{5.7}
$$

Consequently

$$
\bar q\text{ is globally correctable}
\quad\Longleftrightarrow\quad
\Theta_{\mathrm{hr}}(\bar q)=0. \tag{5.8}
$$

The forward implication can be seen directly. If \(\bar q\) is the
localization of a global class \(x\), then the right side of (5.6) is the
sum of local invariants of the global cup \(x\smile y\), and global
reciprocity makes the sum zero. The reverse implication is the exactness,
not merely the zero-sum part, of Poitou--Tate duality.

On SP the dyadic summand in (5.6) is zero, but the SP calculation is still
essential: it makes that summand zero, removes dyadic ambient \(H^2\), and
forces the global twisted invariant group to vanish in Chapter 7.

### 5.3 The two layers of supported degree two

Let

$$
D_{\mathrm{hr}}(M)
=\operatorname{coker}\left(
H^1(G_{\mathbf Q,S},M)\to Q_{\mathrm{hr}}(M)
\right). \tag{5.9}
$$

This is the affine correction obstruction. From the supported cone sequence,

$$
0\longrightarrow D_{\mathrm{hr}}(M)
\longrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M)
\longrightarrow \Sha_S^2(M)
\longrightarrow0, \tag{5.10}
$$

where

$$
\Sha_S^2(M)
=\ker\left(
H^2(G_{\mathbf Q,S},M)
\longrightarrow
\bigoplus_{v\in S}\widetilde H^2(\mathbf Q_v,M)
\right). \tag{5.11}
$$

The first term records a locally admissible family that cannot be reached by
one global correction. The last term records an ordinary global factor-set
class that dies in all ambient local obstruction groups. The middle group is
an extension of these terms; there is no canonical direct-sum splitting.

Poitou--Tate exactness also identifies

$$
D_{\mathrm{hr}}(M)
\simeq
\ker\left(
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*
\to H^2(G_{\mathbf Q,S},M)
\right). \tag{5.12}
$$

It is generally false that \(D_{\mathrm{hr}}(M)\) is the full dual of the
dual Selmer group. The full supported group, rather than its affine
subquotient, satisfies the perfect duality (1.5).

## 6. From relation functionals to supported obstructions

### 6.1 The universal relation obstruction

Apply the supported factor-set construction to the pro-Artinian relation
extension (2.11). More explicitly, use the Artinian extensions (2.13). The
universal deformation over
\(R_{\mathrm{hr}}/\mathfrak m_{R_{\mathrm{hr}}}^N\) has an obstruction

$$
\Omega_N\in
H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes_k\mathcal R. \tag{6.1}
$$

Naturality under reduction makes these classes equal for all sufficiently
large \(N\). Denote their common value by

$$
\Omega_R\in
H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes_k\mathcal R. \tag{6.2}
$$

For \(\lambda\in\mathcal R^*\), contraction gives

$$
\operatorname{ob}_R(\lambda)
=(1\otimes\lambda)(\Omega_R)
\in H^2_{\mathrm{hr}}(\mathbf Q,M). \tag{6.3}
$$

This is the obstruction to lifting the universal deformation through the
one-dimensional extension (2.15). Pushout functoriality makes

$$
\operatorname{ob}_R:\mathcal R^*
\longrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M) \tag{6.4}
$$

linear. The construction does not choose a basis of relations.

### 6.2 Pro-Artinian effectiveness

We isolate the passage from vanishing at every Artinian level to a lift over
the complete relation extension.

**Lemma 6.1 (effectiveness for a relation-socle extension).** Let
\(B'\twoheadrightarrow B\) be a surjection of complete Noetherian local
\(\mathcal O\)-algebras with finite-dimensional kernel \(I\), and suppose
\(\mathfrak m_{B'}I=0\). Let a represented deformation over \(B\) have zero
complete supported obstruction in
\(H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes I\). Then it lifts to \(B'\).

**Proof.** Krull intersection and finite-dimensionality give
\(I\cap\mathfrak m_{B'}^N=0\) for all sufficiently large \(N\). At those
levels,

$$
B'/\mathfrak m_{B'}^N
\longrightarrow B/\mathfrak m_B^N \tag{6.5}
$$

is an Artinian small extension with kernel \(I\). Proposition 4.1 and the
zero obstruction give a nonempty set \(X_N\) of admissible lifts.

The transition maps \(X_{N+1}\to X_N\) are surjective. Indeed, reduce any
lift at level \(N+1\). Its reduction and a prescribed member of \(X_N\)
are two admissible lifts of the same deformation across the same kernel
\(I\). Their difference is a class in
\(H^1_{\mathrm{hr}}(\mathbf Q,M)\otimes I\). Acting on the level
\(N+1\) lift by a cocycle representing that class adjusts its reduction to
the prescribed member while preserving every local condition.

The fibers are finite, so the nonempty finite inverse system with
surjective transition maps has a compatible point. Completeness gives a
deformation over \(B'\). \(\square\)

The lemma uses the actual tangent action and the complete supported
obstruction. An arbitrary vector space that merely contains obstruction
classes would not provide this effectiveness statement.

### 6.3 Injectivity and variance

**Theorem 6.2 (relation injection).** The map (6.4) is injective.

**Proof.** Suppose \(0\ne\lambda\in\mathcal R^*\) and
\(\operatorname{ob}_R(\lambda)=0\). Lemma 6.1 lifts the universal
deformation through

$$
q_\lambda:B_\lambda\longrightarrow R_{\mathrm{hr}}. \tag{6.6}
$$

Representability gives a local \(\mathcal O\)-algebra map

$$
s:R_{\mathrm{hr}}\longrightarrow B_\lambda. \tag{6.7}
$$

The reduction of the lifted deformation is the universal deformation.
Therefore the representing property gives

$$
q_\lambda\circ s=\operatorname{id}_{R_{\mathrm{hr}}}. \tag{6.8}
$$

Let \(I_\lambda=\ker q_\lambda\). Since (6.8) splits the ring map,

$$
B_\lambda=s(R_{\mathrm{hr}})\oplus I_\lambda \tag{6.9}
$$

as \(\mathcal O\)-modules. Moreover
\(\mathfrak m_{B_\lambda}I_\lambda=I_\lambda^2=0\), so

$$
\mathfrak m_{B_\lambda}^2+\varpi B_\lambda
\subseteq s(R_{\mathrm{hr}}). \tag{6.10}
$$

On the other hand, minimality of the variables gives (2.6). Passing its
image to \(B_\lambda\) gives

$$
I_\lambda\subseteq
\mathfrak m_{B_\lambda}^2+\varpi B_\lambda. \tag{6.11}
$$

Equations (6.9)--(6.11) force
\(I_\lambda\subseteq s(R_{\mathrm{hr}})\cap I_\lambda=0\), contradicting
\(I_\lambda\simeq k\). Thus no nonzero \(\lambda\) is killed. \(\square\)

Combining Theorem 6.2 with supported duality gives the injection

$$
\boxed{
\mathcal R^*
\hookrightarrow
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*.
} \tag{6.12}
$$

Dualizing finite-dimensional spaces gives the equivalent quotient

$$
\boxed{
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
\twoheadrightarrow\mathcal R.
} \tag{6.13}
$$

There is no canonical injection
\(\mathcal R\hookrightarrow H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')\).
Confusing (6.12) with such an injection reverses the variance and is
incorrect.

## 7. The balanced hardly-ramified bound

### 7.1 The local correction ledger

The Greenberg--Wiles correction at \(v\) is

$$
c_v=\dim_kL_v-\dim_kH^0(\mathbf Q_v,M). \tag{7.1}
$$

For the Frey-SP condition, (4.3)--(4.4) give

$$
c_2=0-0=0. \tag{7.2}
$$

At the coefficient prime, (4.7) gives

$$
c_\ell=h_\ell-(h_\ell-1)=1. \tag{7.3}
$$

This is the finite-flat correction. It remains \(+1\) when the local
restriction splits and \(h_\ell\) increases. It does not use ambient
\(H^2(\mathbf Q_\ell,M)\)-vanishing.

At infinity, oddness gives one trace-zero invariant and no tangent:

$$
c_\infty=0-1=-1. \tag{7.4}
$$

Globally, absolute irreducibility gives

$$
H^0(G_{\mathbf Q,S},M)=0. \tag{7.5}
$$

Restriction to \(G_{\mathbf Q_2}\), followed by (4.4), gives

$$
H^0(G_{\mathbf Q,S},M')=0. \tag{7.6}
$$

Thus the finite-flat \(+1\) and the real \(-1\) cancel, while the SP term
is zero. Book 165's exact Greenberg--Wiles identity yields

$$
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M'), \tag{7.7}
$$

and supported duality yields

$$
\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M). \tag{7.8}
$$

### 7.2 Relations versus variables

Let

$$
t=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M),
\qquad r=\dim_k\mathcal R. \tag{7.9}
$$

Theorem 6.2 and (7.8) give

$$
\boxed{r\leq t.} \tag{7.10}
$$

Choose a basis of \(\mathcal R=J/\mathfrak nJ\) and lift it to
\(f_1,\ldots,f_r\in J\). Nakayama's lemma gives

$$
J=(f_1,\ldots,f_r), \tag{7.11}
$$

so

$$
\boxed{
R_{\mathrm{hr}}
\simeq
\mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r),
\qquad r\leq t.
} \tag{7.12}
$$

Since \(P\) is regular local of dimension \(1+t\), the generalized
principal ideal theorem gives

$$
\dim R_{\mathrm{hr}}
\geq 1+t-r\geq1. \tag{7.13}
$$

Equations (7.10)--(7.13) do not imply \(r=t\). They do not imply that the
\(f_i\) form a regular sequence, that \(\varpi\) is a nonzerodivisor, or
that \(R_{\mathrm{hr}}\) is finite over \(\mathcal O\).

### 7.3 The exact interface to Book 181

The complete output of this book that Book 181 may use is the following
package, and no more.

1. \(R_{\mathrm{hr}}\) represents the Frey-SP fixed-determinant
   hardly-ramified problem constructed in Book 164.
2. Its relative tangent dimension is
   \(t=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)\).
3. For a minimal power-series presentation, the relation ideal is generated
   by \(r=\dim_kJ/\mathfrak nJ\) elements and \(r\leq t\).
4. Hence the presentation (7.12) and the lower bound (7.13) hold.
5. Every characteristic-zero point obtained later from this same universal
   ring automatically retains the SP condition and the coefficient-linear
   finite-flat condition, because those predicates are built into the
   represented functor.

No conclusion of Book 181 is used to prove this package. In particular, the
argument here does not assume scalar-fiber finiteness, automorphy after
restriction, trace generation, finiteness over \(\mathcal O\), injectivity
of \(\mathcal O\to R_{\mathrm{hr}}\), a horizontal component, or a
characteristic-zero lift. Those are later inputs or conclusions.

## 8. Dependency and hostile audit

### 8.1 Imported results

Only the following prior results carry mathematical weight here.

| source | exact input used | hypothesis matched here |
|---|---|---|
| Book 164, Theorem 6.1 and Sections 5.1--5.2 | represented global Frey-SP functor; SP and finite-flat local lift groupoids; \(L_2=0\); SP eigenvalues \(2,4\); finite-flat liftability and \(\dim L_\ell=h_\ell\) | \(\ell\geq7\); nonzero SP monodromy with intrinsic line and named sign; actual coefficient-linear finite-flat model; cyclotomic determinant |
| Book 165 | positive local complexes; supported duality; the exact Poitou--Tate sequence; Greenberg--Wiles balance | \(S=\{2,\ell,\infty\}\); finite modules; exact local orthogonals; complete real convention; \(M'=M^*(1)\) |
| standard complete-local algebra | Nakayama, Krull intersection, the generalized principal ideal theorem, and representability over inverse limits | complete Noetherian local rings and the minimal presentation (1.7) |

The factor-set calculation, supported obstruction, completeness proof,
relation-socle construction, pro-Artinian effectiveness, and relation
injection are proved in this book. Global Brauer reciprocity is not reproved:
it enters once, through the already-established Poitou--Tate theorem of Book
165. No general number-field or idelic detour is needed for the stated
deformation problem.

### 8.2 Sign, degree, and variance ledger

| item | convention | checked consequence |
|---|---|---|
| factor set | \(\widetilde\rho(g)\widetilde\rho(h)\widetilde\rho(gh)^{-1}=1+c(g,h)\) | left change by \(1+b\) gives \(c'=c+db\) |
| determinant | every matrix lift has determinant \(\chi_\ell\) | \(\operatorname{tr}c=0\), and all correcting cochains lie in \(M\) |
| local comparison | \(\rho_v^{\mathrm{adm}}=(1+b_v)\widetilde\rho|_v\) | \(\operatorname{loc}_vc+db_v=0\) |
| mapping-fiber coordinate | \(y_v=-b_v\) | \(dy_v=\operatorname{loc}_vc\) |
| supported differential | \(d(x,y)=(dx,\lambda x-dy)\) | \((c,y)\) is closed with the preceding sign |
| Tate dual | \(M'=M^*(1)\simeq M(1)\) | local \(H^1\) pairs with local \(H^1\) |
| correction cup | mismatch in \(M\) first, dual Selmer class in \(M'\) second | (5.6) has no unrecorded graded sign |
| Frobenius | arithmetic | SP eigenvalues are \(2\) on \(M^{I_2}\) and \(4\) after twisting |
| relation map | \(\mathcal R^*\to H^2_{\mathrm{hr}}\) | duality gives dual Selmer \(\twoheadrightarrow\mathcal R\), not the reverse injection |

The degree shifts are also forced. A supported degree-two cocycle has a
global degree-two coordinate and local degree-one nullhomotopies. Local Tate
duality has complementary degree two; the global localization fiber adds
one, so supported degree two pairs with supported degree one for the dual
structure.

### 8.3 Forbidden inferences

The following possible shortcuts have been tested and excluded.

- SP is not replaced by a conductor-only condition. Its nonzero nilpotent,
  intrinsic line, named sign, and equation \(FNF^{-1}=2N\) are retained.
- Finite flatness is not replaced by unramifiedness, endpoint characters, or
  rational Hodge labels. The middle coefficient-linear finite-flat object is
  required.
- Local finite-flat smoothness is not promoted to
  \(H^2(\mathbf Q_\ell,M)=0\).
- A split local restriction at \(\ell\) is not assigned a coarse unframed
  universal ring. The framed groupoid and its tangent complex are used.
- The real place is absent from the positive obstruction coordinate only
  because complete cohomology is acyclic for odd \(\ell\); its
  \(-1\) Euler correction is retained.
- The affine correction cokernel is not identified with the whole dual
  Selmer dual; the possible \(\Sha_S^2\) tail in (5.10) is retained.
- A cohomological obstruction receptacle alone is not used to bound
  relations. Completeness, functoriality, tangent actions, and the
  effectiveness Lemma 6.1 are all used before injectivity is claimed.
- Minimal variables are used through (2.6). Without minimality, a removable
  variable--relation pair would lie in the kernel of the obstruction map.
- Balance proves only \(r\leq t\). Equality, regular-sequence structure,
  coefficient flatness, and existence of a horizontal point require later
  arguments and are not assumed here.

The obstruction package is therefore closed at exactly the boundary needed
for Book 181: actual relation directions inject into the correctly supported
degree-two space, every local correction term is present, and the only
commutative-algebra conclusion is the balanced presentation and its
dimension lower bound.
