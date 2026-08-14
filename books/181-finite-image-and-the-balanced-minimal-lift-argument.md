# Finite Image and the Balanced Minimal-Lift Argument

## Contents

1. [From balanced deformations to a Frey lift](#1-from-balanced-deformations-to-a-frey-lift)
   - [The gap between balance and a point](#11-the-gap-between-balance-and-a-point)
   - [An abstract criterion and its unconditional Frey application](#12-an-abstract-criterion-and-its-unconditional-frey-application)
   - [Why the finite-fibre hypothesis has the right strength](#13-why-the-finite-fibre-hypothesis-has-the-right-strength)
2. [The signed-special deformation problem](#2-the-signed-special-deformation-problem)
   - [Coefficients and residual data](#21-coefficients-and-residual-data)
   - [The dyadic minimal-special condition](#22-the-dyadic-minimal-special-condition)
   - [The coefficient-prime condition](#23-the-coefficient-prime-condition)
   - [The global functor](#24-the-global-functor)
   - [Cyclotomic absolute irreducibility](#25-cyclotomic-absolute-irreducibility)
3. [Supported balance and actual relations](#3-supported-balance-and-actual-relations)
   - [The Selmer tangent and supported obstruction](#31-the-selmer-tangent-and-supported-obstruction)
   - [The relation-obstruction injection](#32-the-relation-obstruction-injection)
   - [The balanced presentation](#33-the-balanced-presentation)
4. [Finiteness after restriction](#4-finiteness-after-restriction)
   - [The special-fibre hypothesis and an automorphic sufficient condition](#41-the-special-fibre-hypothesis-and-an-automorphic-sufficient-condition)
   - [Finiteness from the prior minimal theorem](#42-finiteness-from-the-prior-minimal-theorem)
   - [Target preparation proves the Frey case](#43-target-preparation-proves-the-frey-case)
5. [Finite image of the universal scalar fibre](#5-finite-image-of-the-universal-scalar-fibre)
   - [Restriction to the totally real field](#51-restriction-to-the-totally-real-field)
   - [From an open subgroup to the full group](#52-from-an-open-subgroup-to-the-full-group)
6. [Trace descent and scalar-fibre finiteness](#6-trace-descent-and-scalar-fibre-finiteness)
   - [The finite closed trace ring](#61-the-finite-closed-trace-ring)
   - [Carayol descent and reflection of closed conditions](#62-carayol-descent-and-reflection-of-closed-conditions)
   - [Universality forces equality](#63-universality-forces-equality)
7. [Topological Nakayama over the coefficient DVR](#7-topological-nakayama-over-the-coefficient-dvr)
   - [The complete-module lemma](#71-the-complete-module-lemma)
   - [Application to the universal ring](#72-application-to-the-universal-ring)
8. [Balance plus finiteness gives finite flatness](#8-balance-plus-finiteness-gives-finite-flatness)
   - [Every dimension inequality](#81-every-dimension-inequality)
   - [Complete intersection and coefficient flatness](#82-complete-intersection-and-coefficient-flatness)
   - [Failure examples](#83-failure-examples)
9. [Horizontal components and normalization](#9-horizontal-components-and-normalization)
   - [A horizontal minimal prime](#91-a-horizontal-minimal-prime)
   - [Finite normalization without an excellence shortcut](#92-finite-normalization-without-an-excellence-shortcut)
   - [The coefficient DVR point](#93-the-coefficient-dvr-point)
10. [Extraction of the characteristic-zero SP lift](#10-extraction-of-the-characteristic-zero-sp-lift)
    - [Global properties](#101-global-properties)
    - [Nonzero dyadic monodromy](#102-nonzero-dyadic-monodromy)
    - [Finite flatness at the coefficient prime](#103-finite-flatness-at-the-coefficient-prime)
11. [Frey specialization and logical boundaries](#11-frey-specialization-and-logical-boundaries)
    - [The Frey input](#111-the-frey-input)
    - [The unconditional FLT-range theorem](#112-the-unconditional-flt-range-theorem)
    - [Exceptional characteristics](#113-exceptional-characteristics)
12. [The completed minimal-lift construction](#12-the-completed-minimal-lift-construction)
    - [Why the automorphy argument is not circular](#121-why-the-automorphy-argument-is-not-circular)
    - [The chosen lift for the changing-prime argument](#122-the-chosen-lift-for-the-changing-prime-argument)
    - [Conclusion](#123-conclusion)

## 1. From balanced deformations to a Frey lift

### 1.1 The gap between balance and a point

The preceding books construct one precise fixed-determinant deformation problem and prove a
balanced presentation for its universal ring. Balance is indispensable, but it is not the
existence theorem. If

$$
R\simeq\mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r),
\qquad r\leq t,
\tag{1.1}
$$

then Krull's height theorem gives only

$$
\dim R\geq 1+t-r\geq1.
\tag{1.2}
$$

The ring $\mathcal O[[X]]$ is already a counterexample to any stronger inference: it is
balanced and has dimension two, but it is not finite over $\mathcal O$. A positive-dimensional
formal space over the coefficient DVR need not contain a point finite over that DVR.

The missing upper bound is supplied by finiteness of the scalar fibre $R/\varpi R$. That
finiteness promotes, by topological Nakayama, to finiteness of $R$ over $\mathcal O$. The upper
dimension bound from a finite map then meets (1.2), forces all inequalities to be equalities,
and turns the balanced presentation into a complete intersection finite flat over
$\mathcal O$. A horizontal minimal prime and normalization finally produce a coefficient DVR
point.

There are two subtleties between the arithmetic input and that upper bound. First, the
automorphic theorem is naturally available only after restriction to a carefully chosen
totally real field $F$, whereas the desired ring and lift live over $\mathbf Q$. Finiteness of
the restricted universal ring gives finite image on the open subgroup $G_F$; elementary
finite-index group theory then returns finite image on $G_{\mathbf Q}$. Second, finite image of
a representation over a large coefficient ring does not by itself show that the coefficient
ring is finite. A change of basis can introduce arbitrary matrix entries without changing the
finite abstract image. Absolute residual irreducibility and Carayol descent solve this problem:
the conjugacy-invariant trace ring is finite, the representation descends to it, and
universality identifies that trace ring with the entire scalar fibre. Chapters 5--6 keep these
two descent steps separate.

The argument is governed by the following chain of mathematical implications:

$$
\begin{array}{c}
\text{supported Selmer balance and relation injection}\\
\Downarrow\\
\text{balanced presentation}\\
\Downarrow\\
\text{finite image of the universal scalar-fibre representation}\\
\Downarrow\\
R/\varpi R\text{ finite over }k\\
\Downarrow\\
R\text{ finite flat over }\mathcal O\\
\Downarrow\\
\text{horizontal normalized DVR point and an SP lift}.
\end{array}
\tag{1.3}
$$

Only the third line requires arithmetic beyond deformation theory. Book 178 supplies it for
the Frey representation by proving that a broad tame-unipotent deformation ring is finite and
then passing to its signed-special quotient. The proof of that finiteness uses an independently
constructed upper automorphic packet, not the minimal point sought here. Every later arrow in
(1.3) follows in this book from trace descent and complete local algebra.

### 1.2 An abstract criterion and its unconditional Frey application

Fix the exact SP datum of Chapter 2 and let $R^{\mathrm{hr,SP}}$ be its universal ring.
Chapter 4 introduces the special-fibre hypothesis $(\mathrm{SF}_{\mathrm{SP}})$: after
restriction to a suitable totally real field, the represented signed-special deformation ring
has finite special fibre. This is the sole extra hypothesis in the abstract theorem below.
One way to prove it is the stronger signed-special automorphic condition
$(\mathrm{Seed}_{\mathrm{SP}})$, through the minimal $R=\mathbb T$ theorem of Book 173.

The Frey application is different and unconditional. It does not assume either of those
abstract conditions. Book 178, Theorems 12.1 and 12.2, proves
$(\mathrm{SF}_{\mathrm{SP}})$ for the Frey representation from an independently constructed
upper packet. The same theorem also shows that every later characteristic-zero point of the
restricted signed-special quotient is automorphic. Thus Theorem 1.1 is a reusable abstract
criterion, whereas Theorem 1.2 is its established arithmetic application.

**Theorem 1.1 (balanced signed-special minimal-lift criterion).** Assume the residual
hypotheses of Section 2.1, the SP and coefficient-prime conditions of Sections 2.2--2.3, and
$(\mathrm{SF}_{\mathrm{SP}})$. Then:

1. the universal scalar-fibre representation has finite image;
2. $R^{\mathrm{hr,SP}}/\varpi R^{\mathrm{hr,SP}}$ is a finite-dimensional $k$-algebra;
3. $R^{\mathrm{hr,SP}}$ is a finite free $\mathcal O$-algebra and a one-dimensional complete
   intersection;
4. there are a finite extension $E'/E$, its integer ring $\mathcal O'$, and a continuous lift

   $$
   \rho':G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O')
   \tag{1.4}
   $$

   of $\bar\rho$ after residue-field extension, absolutely irreducible over its fraction field,
   with determinant $\chi_\ell$, unramified outside $\{2,\ell\}$,
   coefficient-linearly finite flat at $\ell$, and with the selected dyadic line, sign,
   primitive rank-one monodromy (its reduction is the specified nonzero $\bar N$), and
   conductor exponent one.

The residual restriction to $G_{\mathbf Q(\zeta_\ell)}$ is absolutely irreducible by
Proposition 2.1, and the same is therefore true after the residue-field extension in (1.4).

We now state that application separately so that its hypotheses cannot be confused with those
of the abstract criterion.

**Theorem 1.2 (Frey-range primitive lift and automorphy).** Suppose a normalized
primitive Fermat solution of prime exponent $p\geq7$ is given, and let $\bar\rho$ be its Frey
representation.  There are a totally real field $F^{\mathrm{tar}}/\mathbf Q$ supplied by the
target preparation of Book 178, a finite extension $E'/\mathbf Q_p$ with integer ring
$\mathcal O'$ and residue field $k'$, and a lift

$$
\rho':G_{\mathbf Q}\longrightarrow\operatorname {GL}_2(\mathcal O')
\tag{1.5}
$$

with the following properties.

1. It reduces to $\bar\rho$ after residue-field extension, has determinant $\chi_p$, is
   unramified outside $\{2,p\}$, and is absolutely irreducible over $E'$.
2. At $p$ it has compatible coefficient-linear finite-flat models for
   $\rho'\bmod\mathfrak m_{\mathcal O'}^n$ for every $n\geq1$.
3. At $2$ it has the chosen sign and intrinsic line, and its rank-one monodromy $N'$ is
   primitive:
   $N'\bmod\mathfrak m_{\mathcal O'}=\bar N\otimes_{\mathbf F_p}k'\ne0$ and
   $F'N'(F')^{-1}=2N'$.  Its Artin conductor exponent is one.
4. The primes $2$ and $p$ split completely in $F^{\mathrm{tar}}$.  Both
   $\bar\rho|_{G_{F^{\mathrm{tar}}}}$ and
   $\bar\rho|_{G_{F^{\mathrm{tar}}(\zeta_p)}}$ remain absolutely irreducible, and
   $\rho'|_{G_{F^{\mathrm{tar}}}}$ is automorphic through the finite action constructed in
   Book 178, Theorems 12.1 and 12.2.

The proof is given in Section 11.2. Book 178 first proves finiteness of the restricted
signed-special fibre. Theorem 1.1 then constructs (1.5), and only afterward does the
factorization theorem of Book 178 identify its restriction as automorphic.

### 1.3 Why the finite-fibre hypothesis has the right strength

It is worth understanding why $(\mathrm{SF}_{\mathrm{SP}})$ is neither too weak nor
unnecessarily strong. It does not say that the scalar-fibre representation over $\mathbf Q$
has finite image. Restriction to the totally real field and a finite-index argument will prove
that. Nor does it assume that $R/\varpi R$ is finite, that $R$ is flat, or that a
characteristic-zero lift exists; Chapters 5--10 establish those assertions in that order.

The stronger condition in Chapter 4 is useful only when an actual non-Eisenstein localization
on the same integral SP component is known, together with the hypotheses of Book 173. Merely
knowing residual automorphy would not imply finite special fibre, because it controls a closed
point rather than all infinitesimal directions of the deformation ring.

For the Frey representation, target preparation proves more: the broad deformation ring has a
finite Hecke action with nilpotent kernel, and every characteristic-zero point of its minimal
quotient factors through that action. Consequently the lift (1.5) is not only primitive and
finite flat at the coefficient prime; after restriction to the prepared totally real field it
is attached to a parallel-weight-two automorphic packet. This is the form needed for the
subsequent changing-prime argument.

## 2. The signed-special deformation problem

Before using deformation theory, we must specify which infinitesimal deformations are allowed.
The two ramified primes play different roles. At $2$, primitive tame monodromy rigidifies the
local representation so strongly that the unframed tangent space vanishes. At the coefficient
prime $\ell$, finite-flat geometry supplies a nontrivial but liftable local condition. Their
opposite contributions, together with oddness at the real place, are what make the global
problem balanced.

### 2.1 Coefficients and residual data

Let $\ell\geq7$, let $E/\mathbf Q_\ell$ be finite, and let
$(\mathcal O,(\varpi),k)$ be its integer ring, a uniformizer, and its finite residue field. We
use covariant representations and arithmetic Frobenius. Thus

$$
\det\rho=\chi_\ell,
\qquad \chi_\ell(\phi_p)=p
\quad(p\ne\ell).
\tag{2.1}
$$

Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
\tag{2.2}
$$

be continuous and satisfy:

1. $\det\bar\rho=\bar\chi_\ell$;
2. $\bar\rho$ is absolutely irreducible and odd;
3. $\bar\rho$ is unramified outside $\{2,\ell\}$;
4. its restriction at $2$ has the nonzero-monodromy SP form of Section 2.2, including a named
   sign;
5. its restriction at $\ell$ is coefficient-linearly finite flat of weights $\{0,1\}$.

Put

$$
S=\{2,\ell,\infty\},
\qquad M=\operatorname{ad}^0\bar\rho,
\qquad M'=M^*(1)\simeq M(1).
\tag{2.3}
$$

The last identification uses the perfect trace pairing on $M$. Absolute irreducibility gives
the scalar global centralizer, so the unframed fixed-determinant problem is representable.

These are abstract representation-theoretic hypotheses. No elliptic curve, Frey package, or
automorphic realization occurs in them.

### 2.2 The dyadic minimal-special condition

Choose the $\ell$-primary tame character

$$
t_\ell:I_2\twoheadrightarrow\mathbf Z_\ell
$$

normalized so that arithmetic Frobenius $\phi$ satisfies

$$
t_\ell(\phi\sigma\phi^{-1})=2t_\ell(\sigma).
\tag{2.4}
$$

After one residual change of basis, the SP datum is

$$
\bar\rho(\sigma)=I+\overline t_\ell(\sigma)\bar N,
\qquad \bar N=e_{12}\ne0,
\tag{2.5}
$$

and

$$
\bar F=\bar\rho(\phi)
=\begin{pmatrix}2\bar s&0\\0&\bar s\end{pmatrix},
\qquad \bar s\in\{1,-1\}.
\tag{2.6}
$$

For an Artinian local $\mathcal O$-algebra $A$ with residue field $k$, an SP lift has trivial
wild inertia and matrices

$$
\rho_A(\sigma)=I+t_\ell(\sigma)N_A,
\qquad N_A^2=0,
\qquad F_AN_AF_A^{-1}=2N_A,
\tag{2.7}
$$

where $N_A$ lifts $\bar N$, the determinant is cyclotomic, and the unramified character on
the quotient by

$$
L_A=\ker N_A=\operatorname{im}N_A
\tag{2.8}
$$

has Frobenius value $s\in\{1,-1\}$ lifting $\bar s$. Because one entry of $N_A$ is a unit,
$N_A$ has rank one and (2.8) is a direct-summand line over every $A$. Nonzero monodromy is not
an open condition being inserted into a functor: it is forced on every lift by the nonzero
residual matrix.

Book 165 proves the strict normal form

$$
N_A=e_{12},
\qquad F_A=\begin{pmatrix}2s&0\\0&s\end{pmatrix}
\tag{2.9}
$$

after strict conjugacy. The rigidity can be seen directly. Since $N_A$ has a unit entry and
reduces to $e_{12}$, its image and kernel give a lifted ordered basis in which
$N_A=e_{12}$. Write

$$
F_A=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
$$

The relation $F_Ae_{12}=2e_{12}F_A$ gives

$$
c=0,
\qquad a=2d,
\qquad
F_A=\begin{pmatrix}2d&b\\0&d\end{pmatrix}.
$$

Cyclotomic determinant at arithmetic Frobenius gives
$2d^2=\chi_\ell(\phi)=2$, hence $d^2=1$. The chosen residual sign and the fact that $2$ is a
unit imply $d=s$: of the two factors $(d-s)(d+s)=0$, the second is a unit. Finally strict
conjugation by $I+(b/d)e_{12}$ kills the upper-right entry; it is strict because $b$ reduces
to zero. This is (2.9). There is no infinitesimal unframed parameter at $2$.

Consequently the unframed fixed-determinant local ring is $\mathcal O$, the framed ring is
noncanonically $\mathcal O[[Y_1,Y_2,Y_3]]$, and

$$
L_2=0.
\tag{2.10}
$$

The adjoint vanishing is equally concrete. On $M=\operatorname{ad}^0\bar\rho$, invariance
under the nontrivial residual unipotent inertia is the centralizer calculation

$$
M^{I_2}=k e_{12}.
$$

Arithmetic Frobenius acts on that line by $2$, so it has no fixed vector. On
$M'=M(1)$, the cyclotomic twist multiplies the eigenvalue by another $2$, giving eigenvalue
$4$. Since $\ell\geq7$, neither eigenvalue is $1$. Thus
$H^0(\mathbf Q_2,M)=H^0(\mathbf Q_2,M')=0$. Local Tate duality exchanges these two invariant
groups with the respective degree-two groups, and the away-from-$\ell$ local Euler
characteristic then kills degree one. Hence Book 165's full result is

$$
H^i(\mathbf Q_2,M)=0\quad(i=0,1,2),
\qquad
H^i(\mathbf Q_2,M')=0\quad(i=0,1,2).
\tag{2.11}
$$

The characteristic-zero Artin conductor is one: wild inertia is trivial and the inertia-fixed
space is the single line $\ker N$. This calculation also explains why the sign and the
nonzero residual monodromy belong to the deformation datum: omitting either changes the local
component rather than merely changing its notation.

### 2.3 The coefficient-prime condition

At $\ell$, membership is integral. For each Artinian coefficient algebra $A$, the
$G_{\mathbf Q_\ell}$-representation must be the generic fibre of the selected
coefficient-linear finite locally free group scheme, equivalently of the selected
weight-$\{0,1\}$ filtered object. This condition includes cyclotomic determinant and is stable
under coefficient change and quotient.

Book 165 proves that the framed fixed-determinant condition is represented and liftable. To
interpret its tangent formula, put

$$
h_\ell=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V).
$$

Because $\ell$ is odd, the local adjoint splits as
$\operatorname{ad}\bar V=k\oplus M$, and therefore
$h_\ell=1+h^0(\mathbf Q_\ell,M)$. The weight-$\{0,1\}$ finite-flat
classification over the unramified base $\mathbf Q_\ell$ gives unframed fixed-determinant
tangent dimension $h_\ell$. If

$$
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),
\tag{2.12}
$$

then

$$
\dim_kL_\ell=h^0(\mathbf Q_\ell,M)+1.
\tag{2.13}
$$

The added $1$ is the coefficient-prime local correction in the global Euler formula. Local
liftability says that the obstruction map for this *constrained functor* is zero for every
small extension. It does not imply $H^2(\mathbf Q_\ell,M)=0$; the ambient group may be
nonzero. The supported obstruction theory must therefore retain the ambient group while
remembering that the selected local object can itself be lifted.

Two different uses of the word *flat* must remain separate. Section 2.3 concerns compatible
finite-flat models of the Galois representation on all Artinian quotients. Section 8.2 will
prove that the global universal ring is flat as an $\mathcal O$-module. Neither assertion
implies the other.

### 2.4 The global functor

Let $D^{\mathrm{hr,SP}}(A)$ be the strict-equivalence classes of lifts

$$
\rho_A:G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(A)
\tag{2.14}
$$

with determinant $\chi_\ell$, the SP condition at $2$, and the coefficient-linearly
finite-flat condition at $\ell$. The source group builds in unramifiedness away from
$\{2,\ell\}$.

Book 165 proves that this functor is represented by a complete Noetherian local
$\mathcal O$-algebra

$$
R=R^{\mathrm{hr,SP}}
\tag{2.15}
$$

with universal class $\rho_R$. Its relative tangent space is the Selmer kernel

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\left(
H^1(G_{\mathbf Q,S},M)\longrightarrow
H^1(\mathbf Q_2,M)\oplus
\frac{H^1(\mathbf Q_\ell,M)}{L_\ell}
\right).
\tag{2.16}
$$

The tangent identification follows from the standard dual-number calculation, which also
fixes the coefficient module and the equivalence relation. A determinant-preserving lift to
$k[\epsilon]/(\epsilon^2)$ can be written

$$
\rho_\epsilon(g)=(I+\epsilon c(g))\bar\rho(g),
\qquad c(g)\in M.
$$

The homomorphism equation is

$$
c(gh)=c(g)+\bar\rho(g)c(h)\bar\rho(g)^{-1},
$$

so $c$ is a continuous $1$-cocycle in $M$. Strict conjugation by
$I+\epsilon X$ changes $c$ by the coboundary
$g\mapsto X-\bar\rho(g)X\bar\rho(g)^{-1}$. The dyadic restriction must lie in
$L_2=0$, while the coefficient-prime restriction must lie in $L_\ell$. Taking cocycles modulo
coboundaries gives exactly (2.16). In particular, the scalar summand of
$\operatorname{ad}\bar\rho$ never enters: fixing the determinant places the calculation in
$M=\operatorname{ad}^0\bar\rho$ from the start.

Representability uses two different facts that should not be conflated. The scalar global
centralizer supplies the Schur hypothesis needed for an unframed universal functor. The local
SP and finite-flat conditions are represented closed subfunctors stable under coefficient
pushout. Their completed fibre product with the unrestricted global functor therefore gives
the ring $R$; local formal smoothness is not being used to assert global smoothness.

The zero dyadic target could be omitted numerically by (2.11), but retaining it remembers the
nonlinear SP condition whose tangent it represents.

### 2.5 Cyclotomic absolute irreducibility

The automorphic theorem used in Chapter 4 requires absolute irreducibility on the cyclotomic
subgroup. Here it follows from the primitive dyadic SP datum, without any automorphy or an
unrecorded classification of finite-flat inertia.

**Proposition 2.1 (primitive dyadic inertia excludes the cyclotomic dihedral branch).** The
restriction

$$
\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}
\tag{2.17}
$$

is absolutely irreducible.

**Proof strategy.** Book 141 turns failure of cyclotomic irreducibility into induction from
the unique cyclotomic quadratic field. That field is unramified at $2$, whereas the SP datum
contains a nontrivial unipotent element of order $\ell$ in dyadic inertia. The two local
descriptions are incompatible.

**Proof.** Suppose (2.17) were not absolutely irreducible. By the cyclotomic restriction
dichotomy of Book 141, after extending $k$ inside $\overline k$ there would be a character
$\bar\theta:G_M\to\overline k^\times$ such that

$$
\bar\rho\otimes_k\overline k
\simeq\operatorname{Ind}_{G_M}^{G_{\mathbf Q}}\bar\theta,
\tag{2.18}
$$

where $M$ is the unique quadratic subfield of $\mathbf Q(\zeta_\ell)$. Its fundamental
discriminant is

$$
\ell^*=(-1)^{(\ell-1)/2}\ell,
\tag{2.19}
$$

which is odd. Hence $M/\mathbf Q$ is unramified at $2$, so the quadratic character cutting
out $M$ is trivial on $I_2$ and $I_2\subseteq G_M$.

Restriction of (2.18) to $G_M$ is the sum of the two characters
$\bar\theta$ and $\bar\theta^c$. In particular its restriction to $I_2$ is semisimple after
extension to $\overline k$. Every value of either character lies in
$\overline k^\times$, whose finite subgroups have order prime to $\ell$.

On the other hand, choose $\tau\in I_2$ with
$\overline t_\ell(\tau)=1$. Equation (2.5) gives

$$
\bar\rho(\tau)=I+\bar N,
\qquad \bar N\ne0,
\qquad (I+\bar N)^\ell=I.
\tag{2.20}
$$

This is a nontrivial unipotent matrix. It is not semisimple over
$\overline k$ and has order $\ell$, contradicting the character-sum description. Thus
(2.17) is absolutely irreducible. $\square$

This argument uses the actual SP residual monodromy. Finite flatness at $\ell$ is needed for
the deformation problem and its tangent calculation, but it is not pressed into service as a
small-image theorem.

## 3. Supported balance and actual relations

A tangent-space calculation counts possible first-order deformations, but it does not by
itself bound the number of equations defining the universal ring. For that one needs an
obstruction theory which remembers the chosen local conditions. The supported mapping-fibre
cohomology of Book 166 does exactly this: its first cohomology is the Selmer tangent space and
its second cohomology receives every relation obstruction. Poitou--Tate duality then makes the
two dimensions agree, producing the balanced presentation used later.

### 3.1 The Selmer tangent and supported obstruction

For $v\in S$, put

$$
L_2=0,
\qquad L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),
\qquad L_\infty=0,
\tag{3.1}
$$

and let $L_v^\perp\subseteq H^1(\mathbf Q_v,M')$ be the exact annihilator under local Tate
duality. Book 166 constructs local positive complexes $U_v^+(M)$ that realize the actual
liftable conditions, not just subspaces having the same dimension. With complete Tate cochains
at the real place, the supported complex has the schematic form

$$
C^\bullet_{\mathrm{hr}}(\mathbf Q,M)=
\operatorname{Cone}\!\left(
C^\bullet(G_{\mathbf Q,S},M)\oplus\bigoplus_{v\in S}U_v^+(M)
\longrightarrow
\bigoplus_{v\in S}C^\bullet(\mathbf Q_v,M)
\right)[-1].
$$

Its degree-one group is exactly (2.16). Degree two records a global factor set together with
chosen local null-homotopies; changing the global matrix lift or a local admissible lift changes
that pair by a supported coboundary. This is why the group detects whether one global
correction can satisfy both local conditions simultaneously. Supported Poitou--Tate duality,
with the exact orthogonal local complexes, gives

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*.
\tag{3.2}
$$

Here is the numerical calculation, rather than only its slogan. Absolute irreducibility gives
$H^0(G_{\mathbf Q,S},M)=0$. The injection of global invariants into the dyadic invariants and
the vanishing $H^0(\mathbf Q_2,M')=0$ give
$H^0(G_{\mathbf Q,S},M')=0$. The local contributions are

$$
\begin{array}{c|c|c|c}
v&\dim_kL_v&h^0(\mathbf Q_v,M)&
\dim_kL_v-h^0(\mathbf Q_v,M)\\ \hline
2&0&0&0\\
\ell&h^0(\mathbf Q_\ell,M)+1&h^0(\mathbf Q_\ell,M)&1\\
\infty&0&1&-1.
\end{array}
\tag{3.3}
$$

The final row uses ordinary real invariants: oddness makes conjugation act on $M$ with a
one-dimensional fixed diagonal line. Positive-degree complete real cohomology vanishes, but
that does not erase the $-h^0(\mathbf R,M)$ term in the Euler formula. Consequently the exact
Greenberg--Wiles identity is

$$
\begin{aligned}
&\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
-\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M')\\
&\qquad=h^0(G_{\mathbf Q,S},M)-h^0(G_{\mathbf Q,S},M')
+\sum_{v\in S}\bigl(\dim_kL_v-h^0(\mathbf Q_v,M)\bigr)\\
&\qquad=0-0+(0+1-1)=0.
\end{aligned}
\tag{3.4}
$$

An independent exact-sequence check shows where the possibly nonzero coefficient-prime
$H^2$ went. The global Euler characteristic gives
$h_S^1(M)-h_S^2(M)=2$. Local Euler characteristic and Tate duality give

$$
\dim_k\bigl(H^1(\mathbf Q_\ell,M)/L_\ell\bigr)
=h^0(\mathbf Q_\ell,M')+2,
\qquad
h^2(\mathbf Q_\ell,M)=h^0(\mathbf Q_\ell,M').
$$

Taking alternating dimensions in the specialized Poitou--Tate sequence therefore gives

$$
2-\bigl(h^0(\mathbf Q_\ell,M')+2\bigr)
+h^0(\mathbf Q_\ell,M')=0.
$$

The last term is the ambient coefficient-prime obstruction group. It cancels; it has not been
declared zero.

Thus

$$
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M').
\tag{3.5}
$$

Combining (3.2) and (3.5), if

$$
t=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M),
\tag{3.6}
$$

then

$$
\boxed{\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)=t.}
\tag{3.7}
$$

The supported group is not ordinary global $H^2$. Projecting a supported class to its global
factor set forgets the local null-homotopies and can lose the obstruction to making them
compatible. Conversely, local liftability only says that each restricted factor set can be
null-homotoped separately. The mapping fibre retains the affine Poitou--Tate correction needed
to choose one global correction compatible with all local conditions.

### 3.2 The relation-obstruction injection

Choose a minimal relative cotangent presentation

$$
P=\mathcal O[[X_1,\ldots,X_t]]\twoheadrightarrow R,
\qquad J=\ker(P\to R),
\tag{3.8}
$$

and let $\mathfrak n=(\varpi,X_1,\ldots,X_t)$. The number of variables is exactly $t$ because
the dual of the relative cotangent space is (2.16).

Here is the small-extension class used by Book 167. Let
$A'\twoheadrightarrow A$ have kernel $I$ with $\mathfrak m_{A'}I=0$, and let
$\rho_A$ be an admissible deformation. Choose matrix lifts $\widetilde\rho(g)$ and use
$2\in k^\times$ to normalize their determinants to the fixed character. Their failure to be
a representation is the factor set

$$
\widetilde\rho(g)\widetilde\rho(h)
\widetilde\rho(gh)^{-1}=I+c(g,h),
\qquad c(g,h)\in M\otimes_k I.
$$

Associativity makes $c$ a continuous $2$-cocycle. Changing the matrix lifts changes it by a
coboundary. At each selected place, local liftability gives an admissible local lift; comparing
that lift with $\widetilde\rho|_{G_v}$ gives a local $1$-cochain $b_v$ satisfying
$db_v=c|_{G_v}$. Thus the pair $(c,(b_v)_v)$ is a degree-two cocycle in the supported mapping
fibre. Changing the local admissible lifts changes it by the allowed local tangent action.

The resulting class vanishes precisely when a global $1$-cochain kills $c$ and its local
restrictions differ from the $b_v$ by classes in the selected tangent spaces. Correcting the
matrix lifts by that cochain then produces one global lift satisfying both local conditions.
This proves completeness of the supported obstruction; separate vanishing of the two local
obstructions would not suffice.

The universal algebraic extension behind the relation bound is worth displaying. Put

$$
\mathcal R=J/\mathfrak nJ,
\qquad B=P/\mathfrak nJ.
$$

Then

$$
0\longrightarrow\mathcal R\longrightarrow B\longrightarrow R\longrightarrow0
$$

has square-zero kernel annihilated by the maximal ideal of $B$. Although $B$ and $R$ need not
be Artinian, reduction modulo sufficiently high powers of their maximal ideals produces honest
Artinian small extensions with the same finite kernel. Applying the complete supported
obstruction at those levels and passing through the compatible system gives

$$
\Omega_R\in H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes_k\mathcal R.
$$

A functional $\lambda\in\mathcal R^*$ pushes the relation kernel out to a principal
small extension and contracts $\Omega_R$. Thus the covariant map goes from the *dual*
conormal space to obstructions:

$$
(J/\mathfrak nJ)^*
\hookrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M).
\tag{3.9}
$$

For completeness, suppose $0\ne\lambda\in\mathcal R^*$ mapped to zero. Effectiveness of the
complete obstruction would lift the universal deformation through the corresponding
one-dimensional relation extension $q_\lambda:B_\lambda\twoheadrightarrow R$.
Representability would then give a section $s:R\to B_\lambda$ with
$q_\lambda\circ s=\operatorname{id}_R$. If $I_\lambda=\ker q_\lambda\simeq k$, then

$$
B_\lambda=s(R)\oplus I_\lambda
$$

as $\mathcal O$-modules. Since
$\mathfrak m_{B_\lambda}I_\lambda=I_\lambda^2=0$, both
$\varpi B_\lambda$ and $\mathfrak m_{B_\lambda}^2$ lie in $s(R)$. On the other hand,
minimality of the variables says $J\subseteq\varpi P+\mathfrak n^2$, whose image gives

$$
I_\lambda\subseteq
\varpi B_\lambda+\mathfrak m_{B_\lambda}^2
\subseteq s(R).
$$

This contradicts $s(R)\cap I_\lambda=0$. Hence (3.9) is injective. It does not
assert that every supported obstruction is a relation; dualizing gives a quotient of the dual
Selmer group onto the conormal space, not an injection in the reverse direction.

Put

$$
r=\dim_kJ/\mathfrak nJ.
\tag{3.10}
$$

Equations (3.7) and (3.9) give only

$$
r\leq t.
\tag{3.11}
$$

Neither source proves $r=t$. That equality will follow later from finiteness and dimension,
not from cohomology alone.

### 3.3 The balanced presentation

Topological Nakayama for the finite ideal $J$ lifts a basis of
$J/\mathfrak nJ$ to a minimal generating set $f_1,\ldots,f_r$. Thus

$$
\boxed{
R\simeq
\mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r),
\qquad r\leq t.}
\tag{3.12}
$$

Since $P$ has dimension $t+1$, the height theorem gives

$$
\dim R\geq(t+1)-r\geq1.
\tag{3.13}
$$

This is what follows unconditionally from Books 165--167. It does not prove coefficient
injectivity, finiteness, flatness, reducedness, a horizontal prime, or a characteristic-zero
point.

## 4. Finiteness after restriction

### 4.1 The special-fibre hypothesis and an automorphic sufficient condition

The scalar-fibre argument begins by restricting deformations from $G_{\mathbf Q}$ to a
totally real field $F$. To force finite image on $G_F$, the universal restricted
representation must be defined over a finite ring after reduction modulo $\varpi$. This
motivates the following hypothesis.

**Hypothesis $(\mathrm{SF}_{\mathrm{SP}})$ (restricted special-fibre finiteness).** There is
a finite totally real field $F/\mathbf Q$ such that:

1. $2$ and $\ell$ split completely in $F$, while $\bar\rho|_{G_F}$ and
   $\bar\rho|_{G_{F(\zeta_\ell)}}$ remain absolutely irreducible;
2. restriction of the named dyadic signed-special, coefficient-prime finite-flat, determinant,
   and unramified conditions defines the represented ring $R_F^{\mathrm{SP}}$; and
3. the whole represented special fibre, including its nilpotents, is finite:

   $$
   \dim_k(R_F^{\mathrm{SP}}/\varpi R_F^{\mathrm{SP}})<\infty.
   \tag{4.0}
   $$

No automorphic module or characteristic-zero point occurs in this hypothesis. Finiteness of a
collection of automorphic generic points, or finiteness after inverting $\varpi$, would not
control vertical or nilpotent directions in the special fibre. By contrast, a map to a finite
algebra with nilpotent kernel does imply the required whole-ring finiteness: the powers of the
kernel give a finite filtration, as in Book 176, Lemma 1.1A.

**Hypothesis $(\mathrm{Seed}_{\mathrm{SP}})$.** There exist a finite totally real field
$F/\mathbf Q$ of even degree and an exact clean minimal automorphic datum with the following
properties.

1. The primes $2$ and $\ell$ split completely in $F$. Both
   $\bar\rho_F=\bar\rho|_{G_F}$ and
   $\bar\rho|_{G_{F(\zeta_\ell)}}$ are absolutely irreducible.
2. The restricted fixed-determinant deformation problem has determinant
   $\chi_\ell|_{G_F}$; at every $w\mid2$ it imposes the schematic closure of the same named
   minimal-special component, including the inherited line, sign, and relation
   $F_wN_wF_w^{-1}=2N_w$; at every $w\mid\ell$ it imposes the coefficient-linear
   weight-$\{0,1\}$ finite-flat condition; and it is unramified at every other finite place.
   Write its represented complete local ring as $R_F^{\mathrm{SP}}$.
3. The representation $\bar\rho_F$ occurs in a nonzero non-Eisenstein localized
   parallel-weight-two definite-quaternionic module whose central character is compatible with
   $\chi_\ell|_{G_F}$ and whose every integral local factor agrees with item 2. In particular,
   this is an automorphic carrier on the selected SP component, not merely a system of
   good-prime residual traces.
4. The minimal and auxiliary localized modules satisfy the remaining clean-datum hypotheses
   of Book 173, Theorem 1.1: finite freeness over $\mathcal O$; effective stabilizer and
   diamond-torsor control; integral saturation of the type lattices and degeneracy maps; a
   perfect primary--companion pairing with the prescribed adjoints; generic reducedness of
   every relevant Hecke algebra; branchwise integral Galois attachment and local--global
   compatibility; and specialization of the named Hecke and diamond actions onto the full
   faithful minimal Hecke image.

This condition is stronger than $(\mathrm{SF}_{\mathrm{SP}})$ because it specifies an
integral automorphic realization on the same local components, together with the hypotheses
needed for minimal patching. It is an alternative sufficient condition for the abstract
theorem, not a hypothesis in the Frey application.

The finiteness hypothesis $(\mathrm{SF}_{\mathrm{SP}})$ alone says nothing about automorphy.
In the Frey case, Section 4.3 proves it using a broad Hecke action which has a second
consequence: every characteristic-zero point of the signed-special quotient is automorphic.
That second consequence will be applied only after Chapters 5--10 construct such a point.

Complete splitting is used for more than notation. It identifies every completion at a place
above $2$ or $\ell$ with the local field for which Books 165--167 computed the condition. Thus
restriction retains the nonzero monodromy matrix, intrinsic line, sign, and selected finite-flat
model without a ramified-base-change descent problem. The two irreducibility clauses put the
restricted representation in the Schur and adequate range used by the minimal theorem.

Book 173 writes the named-special equation using geometric Frobenius. With
$\Phi_w=F_w^{-1}$, item 2 becomes

$$
\Phi_wN_w\Phi_w^{-1}=2^{-1}N_w,
$$

so its local condition is exactly the arithmetic-Frobenius condition above, not a different
component.

The final two items explain why residual automorphy alone is not enough for this alternative.
The minimal theorem needs the integral carrier, its pairings and saturated maps, the faithful
Hecke action, and compatible Galois attachment on the named local components.

### 4.2 Finiteness from the prior minimal theorem

**Proposition 4.1 (restricted finite-freeness).** Under
$(\mathrm{Seed}_{\mathrm{SP}})$, there is a canonical isomorphism

$$
R_F^{\mathrm{SP}}\xrightarrow{\sim}\mathbb T_F^{\mathrm{SP}},
\tag{4.1}
$$

and this common ring is a nonzero finite free $\mathcal O$-algebra and a relative complete
intersection.

**Proof.** The standing oddness of $\bar\rho$ makes its restriction to the totally real field
$F$ totally odd. Item 1 gives the global Schur and cyclotomic absolute-irreducibility
hypotheses, while the standing bound $\ell\geq7$ gives the coefficient range required by Book
173, Theorem 1.1. Complete splitting at $\ell$ makes the coefficient-prime extensions
unramified, and item 2 supplies precisely its
clean finite-flat and named minimal-special local conditions. Item 3 is its exact residual
automorphy hypothesis. Item 4 reproduces, rather than anticipates, all of its integral patching
and Hecke-valued Galois hypotheses. The theorem therefore applies to the same represented ring
$R_F^{\mathrm{SP}}$ and gives (4.1) together with finite freeness and the complete-intersection
statement. $\square$

Only the consequence

$$
R_F^{\mathrm{SP}}/\varpi R_F^{\mathrm{SP}}
\quad\text{is a finite-dimensional }k\text{-algebra}
\tag{4.2}
$$

will enter the descent argument. In this alternative route, the stronger established theorem
is the source of (4.2). No reduced-finiteness or reduced-support assertion is manufactured
inside this book.

In particular, Proposition 4.1 proves

$$
(\mathrm{Seed}_{\mathrm{SP}})\Longrightarrow
(\mathrm{SF}_{\mathrm{SP}}).
\tag{4.2a}
$$

The converse need not hold. Special-fibre finiteness does not reconstruct the Hecke module,
the Taylor--Wiles data, or characteristic-zero automorphy. Book 178 proves a separate
factorization through a broad Hecke action; that theorem is additional to
$(\mathrm{SF}_{\mathrm{SP}})$.

Within the exact-minimal formulation there is no second restricted-finiteness hypothesis:
Proposition 4.1 derives the stronger whole-ring statement (4.2) from
$(\mathrm{Seed}_{\mathrm{SP}})$. Finiteness only of
an unspecified set of points of $(R_F^{\mathrm{SP}})_{\mathrm{red}}[1/\varpi]$ would not
suffice, because vertical directions can survive in the special fibre.  But if a canonical
map from $R_F^{\mathrm{SP}}$ to a finite $\mathcal O$-algebra has nilpotent kernel, then
noetherianity and the filtration by powers of that kernel make the whole ring
$\mathcal O$-finite.  Thus a reduced finite-level recovery theorem is sufficient here only
when it retains that actual nilpotent-kernel control.

There is an important distinction in that last sentence. Generic reducedness is one of the
automorphic hypotheses used by Book 173 to assemble a Hecke-valued Galois representation and
identify its branches. It is not being promoted here to a claim that
$R_F^{\mathrm{SP}}$ or its special fibre is reduced. Nor is such a claim needed: a finite free
$\mathcal O$-algebra can have nilpotents in its special fibre, while (4.2) remains true. The
finite-image argument needs module-finiteness of the whole represented restricted ring so that
the universal restricted representation is defined over a finite coefficient ring after
modulo $\varpi$; a statement only about an unspecified collection of generic points would not
provide that.

The named component is also essential. At a minimal-special place, equality of conductor
numbers would not identify the integral deformation quotient. The seed matches the line,
Frobenius sign, monodromy relation, determinant, and their schematic closure. This is exactly
what lets the map in Chapter 5 classify the restriction of the universal SP representation,
rather than a representation on some neighboring local component.

The hypotheses and conclusions in this invocation should not be interchanged.  Generic
reducedness of the relevant **Hecke** algebras and faithfulness of the named automorphic action
are explicit clauses of $(\mathrm{Seed}_{\mathrm{SP}})$ because Books 171--172 use them to
construct the comparison and the patched action.  Equality
$R_F^{\mathrm{SP}}=\mathbb T_F^{\mathrm{SP}}$, scheme-theoretic faithfulness of the deformation
action, and finite freeness of the whole represented deformation ring are conclusions of the
minimal patching theorem.  Chapters 5--10 use only that last whole-ring finiteness consequence;
they assume neither reducedness of $R_F^{\mathrm{SP}}$ nor a prior point of its generic fibre.

### 4.3 Target preparation proves the Frey case

The upper packet constructed in Book 178 is special at a finite set of non-dyadic places where
the minimal problem is unramified.  Its exact special local component is too narrow for the
argument here: an arbitrary unramified point need not retain the upper packet's special line
or Frobenius-incidence equation.  The correct common ambient problem is instead broad
tame-unipotent.  At every active place it remembers only that inertia has characteristic
polynomial $(X-1)^2$.  It contains both the upper special point and the unramified minimal
quotient, giving a canonical map

$$
R_{F^{\mathrm{tar}}}^{\mathrm{uni}}
 (P^{\mathrm{tar}}_{\mathrm{top}})
\twoheadrightarrow R_{F^{\mathrm{tar}}}^{\mathrm{SP}}.
\tag{4.3}
$$

The important point is the order in which this map is used.  The upper packet creates a
primitive vector in the common definite localization.  Source patching then proves finiteness
of the entire broad ring.  Only after that whole-ring statement has been established does one
pass through (4.3) to the minimal special fibre.  No characteristic-zero point of the minimal
quotient occurs in this construction.

**Theorem 4.2 (restricted finiteness and automorphy for the Frey problem).** Let $\bar\rho$ be the
Frey residual representation supplied by Book 164, Theorem 1.1, for a normalized primitive
solution of prime exponent $p\geq7$, after the common finite coefficient extension made in
Book 178, Section 12.3. Let
$F^{\mathrm{tar}}$, the active set $P^{\mathrm{tar}}_{\mathrm{top}}$, the broad ring, and the
finite definite Hecke action be those constructed in Book 178, Sections 12.1--12.3. Then
$(\mathrm{SF}_{\mathrm{SP}})$ holds with $\ell=p$ and $F=F^{\mathrm{tar}}$. More precisely,

1. $2$ and $p$ split completely in $F^{\mathrm{tar}}$, and the restrictions of $\bar\rho$
   to $G_{F^{\mathrm{tar}}}$ and to
   $G_{F^{\mathrm{tar}}(\zeta_p)}$ are absolutely irreducible;
2. the represented signed-special ring is the quotient in (4.3), with the named dyadic
   signed-special factors, selected coefficient-linear finite-flat factors above $p$, fixed
   cyclotomic determinant, and unramified conditions elsewhere; and
3. its whole special fibre is finite:

   $$
   \dim_k\bigl(R_{F^{\mathrm{tar}}}^{\mathrm{SP}}/
   \varpi R_{F^{\mathrm{tar}}}^{\mathrm{SP}}\bigr)<\infty.
   \tag{4.4}
   $$

In addition, every characteristic-zero point of
$R_{F^{\mathrm{tar}}}^{\mathrm{SP}}$ factors through the finite Hecke action on
the broad ring.

**Proof.** Book 178, Theorem 12.1, proves that the map from the broad ring in (4.3) to its
actual finite definite Hecke action has nilpotent kernel.  Its proof invokes the prepared
target application of Book 176, Theorem 1.1K.  Book 176, Corollary 1.1L, then gives both
finiteness of the signed-special quotient's whole special fibre and factorization of every
characteristic-zero point of that quotient through the same Hecke action. Book 178,
Theorem 12.2, proves these conclusions together with complete splitting and the two
irreducibility statements. Its three numbered assertions are the three clauses of
$(\mathrm{SF}_{\mathrm{SP}})$ above. The proof of the nilpotent-kernel statement uses the
upper packet to produce a nonzero vector in a broad deformation problem. Since the minimal
ring is obtained only afterward as the quotient (4.3), no characteristic-zero point of that
minimal ring enters the argument.
$\square$

The stronger seed condition remains mathematically useful because Proposition 4.1 gives a
second sufficient condition for the abstract criterion.  It is unnecessary for Theorem 1.2.
Other level-changing constructions address stronger exact-minimal comparison questions, but
they play no role in the finite-fibre route or in the pointwise automorphy proved here.

## 5. Finite image of the universal scalar fibre

The hypothesis in Chapter 4 concerns a deformation ring over a totally real field, while the
universal representation of interest is defined over $\mathbf Q$. This chapter bridges the
two. Restriction gives a representation over a finite coefficient ring on the subgroup
$G_F$; because $G_F$ has finite index, finiteness of its image forces finiteness of the full
image. At this stage we prove only a group-theoretic statement. Turning it into finiteness of
the coefficient algebra requires the trace argument of Chapter 6.

### 5.1 Restriction to the totally real field

Set

$$
A=R/\varpi R
\tag{5.1}
$$

and let

$$
\rho_A:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(A)
\tag{5.2}
$$

be the universal representation after scalar reduction. Under
$(\mathrm{SF}_{\mathrm{SP}})$, restriction of the universal deformation to $G_F$ satisfies
the exact restricted problem. At a place
$w\mid2$ or $w\mid\ell$, complete splitting identifies $F_w$ with the corresponding rational
local field, so the represented local quotient is literally unchanged. At every other finite
place, an unramified representation remains unramified on restriction. The determinant becomes
$\chi_\ell|_{G_F}$, and the residual representation is $\bar\rho_F$. Universality therefore
gives a local map

$$
R_F^{\mathrm{SP}}\longrightarrow A.
\tag{5.3}
$$

Because $A$ has characteristic $\ell$, (5.3) factors through
$R_F^{\mathrm{SP}}/\varpi R_F^{\mathrm{SP}}$. Let $B$ be its image. Equation (4.2) makes
$B$ a finite-dimensional $k$-algebra, hence a finite ring.

After a strict conjugacy, $\rho_A|_{G_F}$ is obtained by scalar extension from the universal
restricted representation over $B$. Equivalently, after choosing a representative of the
universal strict-equivalence class, all its matrices lie in $\operatorname{GL}_2(B)$.

The argument needs no characteristic-zero point over $F$.  It uses only the map of represented
rings and the finiteness of its source modulo $\varpi$.  On the preferred Frey route, the
additional automorphic action supplied by Theorem 4.2 is left unused until the
normalized horizontal point has been constructed.

Since $B$ is a finite ring, $\operatorname{GL}_2(B)$ is a finite set. Consequently

$$
\rho_A(G_F)
\quad\text{is finite}.
\tag{5.4}
$$

Notice the direction of the argument. We did not assume finite image of (5.2). We obtained
finite image after restriction from finiteness of a represented restricted deformation ring.

### 5.2 From an open subgroup to the full group

The subgroup $G_F\subseteq G_{\mathbf Q}$ has finite index. The map of left-coset sets

$$
G_{\mathbf Q}/G_F
\longrightarrow
\rho_A(G_{\mathbf Q})/\rho_A(G_F)
\tag{5.5}
$$

is surjective. Thus the second index is finite. Since its subgroup in (5.4) is finite, so is
the whole group:

$$
\boxed{\rho_A(G_{\mathbf Q})\text{ is finite}.}
\tag{5.6}
$$

No Galois or normality hypothesis on $F/\mathbf Q$ is needed for this elementary finite-index
step.

## 6. Trace descent and scalar-fibre finiteness

A finite abstract image does not force the visible matrix entries to generate a finite
algebra, since conjugating by a matrix with transcendental entries can enlarge the
matrix-entry ring. Traces avoid this defect because they are invariant under conjugation.
The rank-two trace identity makes their span a finite algebra, and residual absolute
irreducibility then lets Carayol descent recover the representation over that trace algebra.
Universality will show that no part of the scalar fibre lies outside it.

### 6.1 The finite closed trace ring

Let $T\subseteq A$ be the closed $k$-subalgebra generated by

$$
\{\operatorname{tr}\rho_A(g):g\in G_{\mathbf Q}\}.
\tag{6.1}
$$

Finite image makes the displayed set finite, but finite generation as an algebra would not by
itself imply finite dimension. The rank-two trace identity supplies the missing multiplicative
closure:

$$
\operatorname{tr}(X)\operatorname{tr}(Y)
=\operatorname{tr}(XY)+\det(Y)\operatorname{tr}(XY^{-1}).
\tag{6.2}
$$

Indeed, Cayley--Hamilton for the invertible $2\times2$ matrix $Y$ gives
$Y+\det(Y)Y^{-1}=\operatorname{tr}(Y)I$; multiply by $X$ and take traces. Thus the identity is
valid over the possibly nonreduced commutative ring $A$, not only over a field.

Here every determinant lies in the finite field $k$ because it is the residual cyclotomic
character. Hence the $k$-linear span $W$ of the finite trace set is a subalgebra. It contains
$1$ because $\operatorname{tr}(I)=2$ and $2\in k^\times$. The space $W$ is finite, and
therefore closed in the Hausdorff ring $A$. Thus

$$
T=W
\quad\text{is a finite-dimensional }k\text{-algebra}.
\tag{6.3}
$$

It is local. Indeed, an element of $T$ with nonzero residue is a unit in $A$. Multiplication by
it is injective on the finite-dimensional space $T$, hence surjective, so its inverse also lies
in $T$.

Finite image alone does not make an arbitrarily chosen matrix-entry algebra finite. Conjugating
a constant finite representation by a matrix with an entry $X\in k[[X]]$ can make an entry
generate the infinite-dimensional algebra $k[X]$. Traces are invariant under conjugacy, which
is why the trace ring is the correct object.

### 6.2 Carayol descent and reflection of closed conditions

The residual representation is absolutely irreducible. The mechanism behind Carayol descent
is useful here. Burnside's theorem makes the residual group algebra span
$M_2(k)$. Choose four residual group-algebra elements giving a basis and a trace-dual basis.
The determinant and trace identities express the coefficients of every $\rho_A(g)$ in the
lifted basis through traces belonging to $T$. The resulting rank-two $T$-lattice inside
$A^2$ is stable under $G_{\mathbf Q}$; residual absolute irreducibility makes it free and
allows its basis to be normalized to the original residual basis. Book 62 carries out this
construction in the pseudocompact category and proves compatibility across all Artinian
shadows.

Carayol descent therefore strictly conjugates $\rho_A$ to a representation

$$
\rho_T:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(T).
\tag{6.4}
$$

The hypotheses here are exact: $A$ and $T$ are local pseudocompact rings with the same residue
field, the determinant already takes values in $k\subseteq T$, and the residual centralizer is
scalar. Carayol descent uses absolute irreducibility to recover matrix coefficients after a
strict change of basis; it is not the false assertion that arbitrary representations with the
same traces are isomorphic over a ring with nilpotents.

One must still check that (6.4) is a point of the same SP deformation functor. Matrix descent
alone does not say that an integral local condition descends through a coefficient subring.

**Lemma 6.1 (reflection of represented closed conditions).** Let an unrestricted represented
deformation functor have universal ring $U$, and let a closed subfunctor be represented by
$R=U/I$. Suppose $T\hookrightarrow A$ is injective and a $T$-valued representation becomes,
after scalar extension to $A$, a point of the closed subfunctor. Then the $T$-valued point
already belongs to the closed subfunctor.

**Proof.** The $T$-valued point gives a map $U\to T$. Its composite with $T\hookrightarrow A$
kills $I$. Injectivity therefore implies that $U\to T$ kills $I$, so it factors through
$R=U/I$. $\square$

Book 165 constructs the global SP and finite-flat problem exactly as such a closed quotient of
the unrestricted fixed-determinant ring, using represented framed local quotients. Lemma 6.1
therefore applies to (6.4). It avoids any unjustified attempt to descend a finite-flat group
scheme directly through an arbitrary subring.

### 6.3 Universality forces equality

Since $\rho_T$ belongs to $D^{\mathrm{hr,SP}}(T)$, universality gives

$$
R\longrightarrow T.
\tag{6.5}
$$

The ring $T$ has characteristic $\ell$, so (6.5) factors through a map

$$
f:A=R/\varpi R\longrightarrow T.
\tag{6.6}
$$

Let $i:T\hookrightarrow A$ be the inclusion. Scalar extension of $\rho_T$ along $i$ is
strictly equivalent to $\rho_A$. Since $R$ represents strict-equivalence classes, the two
corresponding maps from $R$ to $A$ are equal. Therefore

$$
i\circ f=\operatorname{id}_A.
\tag{6.7}
$$

The inclusion $i$ is consequently surjective, and

$$
\boxed{A=T.}
\tag{6.8}
$$

Together with (6.3), this proves that $R/\varpi R$ is finite-dimensional over $k$. This is the
precise scalar-fibre factorization. No additional faithfulness or support assertion appears in
this step: the restricted $R=\mathbb T$ theorem was used earlier, and only earlier, to obtain
finite image after restriction.

## 7. Topological Nakayama over the coefficient DVR

Chapter 6 proves finiteness only after reducing modulo $\varpi$. To lift a finite basis from
the special fibre one cannot invoke ordinary Nakayama, because finite generation is precisely
what is still unknown. Completeness supplies the missing convergence: successive corrections
modulo powers of $\varpi$ converge in the pseudocompact topology. The resulting complete
Nakayama lemma promotes scalar-fibre finiteness to module-finiteness over $\mathcal O$.

### 7.1 The complete-module lemma

Ordinary Nakayama applies to modules already known to be finite. Here finiteness is the
conclusion, so completeness must enter explicitly.

**Lemma 7.1 (pseudocompact Nakayama over a DVR).** Let $M$ be a pseudocompact
$\mathcal O$-module. If $M/\varpi M$ is finite-dimensional over $k$ and $\varpi M$ is closed,
then $M$ is a finite $\mathcal O$-module.

**Proof strategy.** Lift a basis of the scalar fibre, then use the complete form of Nakayama
to turn topological spanning into algebraic generation.

**Proof.** Choose lifts $m_1,\ldots,m_d$ of a $k$-basis and let
$N=\sum_i\mathcal O m_i$. The continuous image of the compact module $\mathcal O^d$ in the
Hausdorff module $M$ is compact and hence closed; compactness uses that the residue field is
finite, so the coefficient DVR is the inverse limit of finite rings. The quotient $Q=M/N$ is
therefore
pseudocompact. Surjectivity modulo $\varpi$ says $Q=\varpi Q$. Iteration gives
$Q=\varpi^nQ$ for every $n$. A pseudocompact $\mathcal O$-module is separated for the
$\varpi$-adic filtration in the needed sense: for every open submodule $U$, the finite-length
module $Q/U$ is killed by some power of $\varpi$, so an element in every $\varpi^nQ$ maps to
zero in $Q/U$. Finite-shadow reconstruction and Hausdorffness then give

$$
Q=\bigcap_{n\geq0}\varpi^nQ=0.
\tag{7.1}
$$

Thus the $m_i$ generate $M$. $\square$

This is the coefficient-base specialization of the pseudocompact Nakayama theorem in Book 57.

### 7.2 Application to the universal ring

As a module over $\mathcal O$, the complete Noetherian local ring $R$ is pseudocompact:

$$
R\simeq\varprojlim_nR/\mathfrak m_R^n,
\tag{7.2}
$$

and each quotient has finite length over $\mathcal O$. The ideal $\varpi R$ is closed in the
maximal-ideal topology because every ideal of a complete Noetherian local ring is closed.
Equation (6.8) makes $R/\varpi R$ finite-dimensional over $k$. Lemma 7.1 now gives

$$
\boxed{R\text{ is finite over }\mathcal O.}
\tag{7.3}
$$

The topology is not ornamental in this step. Without completeness, a finite spanning set
modulo $\varpi$ need not sum to exact coefficients in $\mathcal O$.

## 8. Balance plus finiteness gives finite flatness

The two halves of the argument now meet. Balance supplies a lower bound on the dimension of
$R$, while finiteness over the coefficient DVR supplies an upper bound. Equality forces the
coefficient map to be injective and the number of relations to equal the number of variables.
The universal ring is consequently a one-dimensional complete intersection, and its
Cohen--Macaulay property turns $\varpi$ into a non-zero-divisor. This is the step that yields
finite flatness rather than mere finiteness.

### 8.1 Every dimension inequality

Recall the minimal presentation (3.12). Since $R$ is finite over $\mathcal O$, the exact
dimension formula for a finite map gives

$$
\dim R=\dim\bigl(\mathcal O/\ker(\mathcal O\to R)\bigr)\leq1.
\tag{8.1}
$$

The balanced lower bound (3.13) gives the opposite inequality. Hence

$$
\dim R=1.
\tag{8.2}
$$

A nonzero ideal in a DVR contains a power of $\varpi$, and its quotient has dimension zero.
Equations (8.1)--(8.2) therefore force

$$
\ker(\mathcal O\to R)=0.
\tag{8.3}
$$

This is the first point at which a characteristic-zero component is proved to exist. Before
(8.3), a complete local deformation ring could have been supported entirely in
characteristic $\ell$. The lower bound coming from balance rules that out only after the upper
bound from module-finiteness is available.

Now (3.13) and (8.2) yield

$$
1=\dim R\geq1+t-r,
\qquad r\geq t.
\tag{8.4}
$$

Together with the obstruction inequality $r\leq t$, this gives

$$
\boxed{r=t.}
\tag{8.5}
$$

Thus equality of relations and variables is a consequence of scalar-fibre finiteness. It was
not silently inserted into the Selmer calculation.

### 8.2 Complete intersection and coefficient flatness

The regular local source

$$
P=\mathcal O[[X_1,\ldots,X_t]]
\tag{8.6}
$$

has dimension $t+1$. The exact dimension formula for its quotient gives

$$
\operatorname{ht}J=(t+1)-1=t.
\tag{8.7}
$$

The ideal $J$ is minimally generated by the $t$ elements in (8.5). In the Cohen--Macaulay
regular local ring $P$, an ideal of height $t$ minimally generated by $t$ elements is generated
by a regular sequence. Therefore $R$ is a complete intersection and is Cohen--Macaulay of
dimension one.

More explicitly, $P$ is regular and hence Cohen--Macaulay, so
$\operatorname{grade}(J)=\operatorname{ht}(J)=t$. An ideal generated by $t$ elements cannot
have a regular sequence in it longer than its number of generators. Equality of grade and the
minimal number of generators therefore makes a minimal generating sequence
$f_1,\ldots,f_t$ regular. This is the algebraic step for which both inequalities
$r\leq t$ and $r\geq t$ were needed.

Because $R$ is finite local over $\mathcal O$, the quotient $R/\varpi R$ is Artinian. Thus
$\varpi$ is a parameter of the one-dimensional local ring $R$. Every parameter in a
one-dimensional Cohen--Macaulay ring is a non-zero-divisor: a Cohen--Macaulay local ring has
no embedded associated prime, and an element whose quotient has dimension zero avoids every
one-dimensional minimal prime. Therefore

$$
R[\varpi]=0.
\tag{8.8}
$$

Over a DVR, torsion-free is equivalent to flat. A finite flat module over a local ring is free.
Indeed, multiplication by $\varpi$ being injective makes multiplication by every nonzero
element of $\mathcal O$ injective, since each is a unit times a power of $\varpi$.
Consequently

$$
\boxed{R\text{ is finite free over }\mathcal O.}
\tag{8.9}
$$

This proves coefficient-ring flatness with no appeal to reducedness. A complete intersection
can be nonreduced, but its parameter $\varpi$ is still regular here.

### 8.3 Failure examples

Each hypothesis above has a distinct role.

The balanced ring $\mathcal O[[X]]$ is not finite over $\mathcal O$; balance supplies only a
lower dimension bound. The finite algebra $\mathcal O/(\varpi)$ has no horizontal
characteristic-zero point; finiteness without coefficient injectivity or balance is
insufficient. Finally,

$$
\mathcal O[[X]]/(\varpi X)
\tag{8.10}
$$

has a horizontal and a vertical component and is not flat: the nonzero class of $X$ is killed
by $\varpi$. The height-equals-relations conclusion is what excludes this coefficient torsion
in the universal ring.

## 9. Horizontal components and normalization

Finite freeness guarantees that the generic fibre is nonzero, but a useful Galois
representation requires an integral point with values in a coefficient DVR. We therefore
choose a horizontal irreducible component, pass to its fraction field, and normalize. The
trace-dual argument below proves directly that the normalization is finite, so the universal
representation can be evaluated on a genuine finite extension of the original coefficient
DVR.

### 9.1 A horizontal minimal prime

The finite map $\mathcal O\hookrightarrow R$ is integral, but integrality by itself does **not**
force the contraction of every minimal prime to be minimal: a finite injective algebra can have
a vertical minimal component.  What rules that out here is the coefficient flatness proved in
Section 8.2.  If $\mathfrak p$ is a minimal prime of $R$ and
$\mathfrak p\cap\mathcal O\ne(0)$, then, because $\mathcal O$ is a DVR, the contraction contains
a power of $\varpi$.  Primality then gives $\varpi\in\mathfrak p$.  But every minimal prime of a
Noetherian ring is associated, while (8.8) says that multiplication by $\varpi$ on $R$ is
injective.  Hence $\varpi$ belongs to no minimal prime, a contradiction.  Therefore

$$
\mathfrak p\cap\mathcal O=(0).
\tag{9.1}
$$

Equivalently, flatness puts $\varpi$ in no associated prime. Choose one minimal prime and set

$$
C=R/\mathfrak p.
\tag{9.2}
$$

Then $C$ is a complete local domain finite over $\mathcal O$, the coefficient map into $C$ is
injective, and

$$
L=\operatorname{Frac}(C)
\tag{9.3}
$$

is a finite extension of $E=\operatorname{Frac}(\mathcal O)$.

### 9.2 Finite normalization without an excellence shortcut

Let $\mathcal O_L$ be the integral closure of $\mathcal O$ in $L$. We prove directly that it
is finite over $\mathcal O$.

Choose an $E$-basis $a_1,\ldots,a_n$ of $L$ consisting of elements integral over
$\mathcal O$; multiplying an arbitrary basis by sufficiently large powers of $\varpi$ produces
such a basis. Put

$$
\Lambda=\sum_i\mathcal Oa_i,
\qquad
\Lambda^\vee=
\{x\in L:\operatorname{Tr}_{L/E}(x\Lambda)\subseteq\mathcal O\}.
\tag{9.4}
$$

Characteristic zero makes $L/E$ separable, so the trace pairing is nondegenerate and
$\Lambda^\vee$ is a finite free fractional $\mathcal O$-lattice. Concretely, the Gram matrix
$(\operatorname{Tr}_{L/E}(a_ia_j))$ is invertible over $E$; clearing the denominators of its
inverse sandwiches $\Lambda^\vee$ between two finite free fractional lattices. If
$x\in\mathcal O_L$, then
$xa_i$ is integral over $\mathcal O$. Its trace lies in $E$ and is integral over the integrally
closed DVR $\mathcal O$, hence lies in $\mathcal O$: the conjugates of an integral element are
integral, so their sum is integral. Thus

$$
\mathcal O_L\subseteq\Lambda^\vee.
\tag{9.5}
$$

As an $\mathcal O$-submodule of a finite module, $\mathcal O_L$ is finite. This direct
trace-dual argument is why no excellence theorem is needed.

The normalization of $C$ in $L$ is exactly $\mathcal O_L$. Indeed, an element integral over
$C$ is integral over $\mathcal O$ by transitivity because $C$ is finite over $\mathcal O$.
Conversely, a monic polynomial over $\mathcal O\subseteq C$ shows that every element of
$\mathcal O_L$ is integral over $C$.

### 9.3 The coefficient DVR point

The complete local ring $\mathcal O$ is henselian. A finite $\mathcal O$-algebra decomposes
as the product of its local factors, because the primitive idempotents of its Artinian special
fibre lift uniquely. The ring $\mathcal O_L$ is a domain, so this product has only one factor.
Thus $\mathcal O_L$ is already local. Put

$$
\mathcal O'=\mathcal O_L.
\tag{9.6}
$$

It is a one-dimensional Noetherian normal local domain, hence a DVR. It is finite over
$\mathcal O$, has fraction field $L$, and has residue field $k'$ finite over $k$. The composite

$$
x:R\twoheadrightarrow C\longrightarrow\mathcal O'
\tag{9.7}
$$

is local and reduces to the original residual map followed by $k\hookrightarrow k'$. No
reducedness of $R$ was required: quotienting by one minimal prime chooses a reduced horizontal
component, and normalization regularizes that component.

The locality of (9.7) matters. It ensures that the reduction of every universal matrix is the
given residual matrix after $k\hookrightarrow k'$, rather than a point on a different maximal
ideal of a finite coefficient algebra. Passing to the normalization changes coefficients and
removes singularities on the selected component; it does not change any equation already
satisfied by the universal representation.

## 10. Extraction of the characteristic-zero SP lift

The normalized map of Chapter 9 can now be applied to the universal representation. Because
all local conditions were imposed as closed integral deformation conditions, evaluation
preserves more than the generic Weil--Deligne type: it preserves the primitive dyadic matrix
and the compatible finite-flat models at every Artinian coefficient quotient. This chapter
collects those properties and verifies characteristic-zero irreducibility.

### 10.1 Global properties

Evaluate the universal representation along (9.7):

$$
\rho'=x\circ\rho_R:
G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O').
\tag{10.1}
$$

It reduces to $\bar\rho\otimes_kk'$. Since determinant and unramifiedness are equations in the
universal problem,

$$
\det\rho'=\chi_\ell,
\qquad
\rho'\text{ is unramified outside }\{2,\ell\}.
\tag{10.2}
$$

The fraction field of $\mathcal O'$ is a finite characteristic-zero extension of $E$, so
(10.1) is the desired integral characteristic-zero point.

The representation over that fraction field is absolutely irreducible. Otherwise, after a
finite coefficient extension, a stable line could be intersected with the lattice and
saturated. Its reduction would give a nonzero proper invariant line in
$\bar\rho\otimes_k\overline k$, contradicting residual absolute irreducibility. This uses no
automorphy of the extracted point.

### 10.2 Nonzero dyadic monodromy

At $2$, the universal identities (2.7) base-change to $\mathcal O'$:

$$
\rho'(\sigma)=I+t_\ell(\sigma)N',
\qquad (N')^2=0,
\qquad F'N'(F')^{-1}=2N'.
\tag{10.3}
$$

The reduction of $N'$ is $\bar N\otimes_kk'\ne0$. Thus one entry of $N'$ is a unit: the
monodromy is primitive on the chosen lattice, not merely nonzero after inverting the
uniformizer. It follows that $N'$ has rank one and that its kernel and image are the same
direct-summand line. The quotient Frobenius value is the selected $s\in\{1,-1\}$. Thus the
lift retains the full SP record, not merely conductor one:

$$
N'\bmod\mathfrak m_{\mathcal O'}=\bar N\otimes_kk'\ne0,
\qquad
\ker N'=\operatorname{im}N',
\qquad
F'N'(F')^{-1}=2N'.
\tag{10.4}
$$

Wild inertia is trivial and the fixed space has dimension one, so the Artin conductor exponent
is one. Nonzero monodromy survives because it was nonzero already in the residual condition;
normalization cannot move the point to a monodromy-zero boundary.

### 10.3 Finite flatness at the coefficient prime

For every $n\geq1$, reduce (10.1) modulo the $n$th power of the maximal ideal of
$\mathcal O'$. Book 165's coefficient-extension and quotient compatibility supplies the
selected coefficient-linear finite locally free model for

$$
\rho'\bmod\mathfrak m_{\mathcal O'}^n.
\tag{10.5}
$$

These models are compatible with further quotient. This is exactly the pro-Artinian meaning
of finite flatness used in the signed-special problem. Raynaud uniqueness in the low-weight
range supplies the compatibility; arbitrary existence of unrelated models at each level would
not be enough. We do not claim that the infinite free $\mathcal O'$-lattice itself is a finite
group scheme.

It is useful to distinguish the two residual statements preserved by $\rho'$. First,
$\rho'\bmod\mathfrak m_{\mathcal O'}$ is
$\bar\rho\otimes_kk'$, so Proposition 2.1 still gives absolute irreducibility on the
cyclotomic subgroup. Second, the reduction of $N'$ is the specified nonzero matrix, so the
dyadic line and sign are not merely characteristic-zero choices. These are precisely the
image and local-component clauses needed to begin the changing-prime argument.

Equations (10.1)--(10.5), together with Proposition 2.1, complete the proof of Theorem 1.1
under $(\mathrm{SF}_{\mathrm{SP}})$.

## 11. Frey specialization and logical boundaries

The preceding theorem applies to any residual representation satisfying the signed-special
local hypotheses and special-fibre finiteness. We now specialize it to the representation of
a Frey curve. Book 164 supplies the local arithmetic, while Book 178 supplies the restricted
finiteness theorem and the automorphic factorization. Their combination removes the abstract
special-fibre hypothesis from the Fermat application.

### 11.1 The Frey input

The criterion is reusable, but its intended first input is concrete. Book 164 proves that a
normalized primitive Fermat solution of prime exponent $p\geq7$ produces a representation

$$
\bar\rho_{a,b,c,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
\tag{11.1}
$$

which is odd and absolutely irreducible, has determinant $\bar\chi_p$, is unramified outside
$\{2,p\}$, is coefficient-linearly finite flat at $p$, and has at $2$ the exact signed SP
datum (2.5)--(2.6) with $\bar N\ne0$. Thus it satisfies every residual and local hypothesis
of Chapters 2--3 after setting

$$
\ell=p,
\qquad
\bar\rho=\bar\rho_{a,b,c,p}\otimes_{\mathbf F_p}k,
\qquad
\mathcal O/\mathfrak m_{\mathcal O}=k,
\tag{11.2}
$$

where $\mathcal O$ is chosen large enough to contain the target coefficient data constructed in
Book 178.  This finite scalar extension preserves every residual condition. Proposition 2.1
supplies the cyclotomic absolute irreducibility needed for the automorphic theorem directly
from the dyadic SP datum.

The adjective “exact” here carries arithmetic content. Book 164 computes the dyadic
discriminant valuation modulo $p$ and shows that the residual tame parameter does not vanish;
after the chosen basis, inertia contains

$$
I+\overline t_p(\sigma)e_{12}
$$

rather than only a representation whose conductor is bounded by one. Split or nonsplit
multiplicative reduction supplies the named quotient sign. The intrinsic line is simultaneously
$\ker e_{12}$ and $\operatorname{im}e_{12}$. At the coefficient prime, the finite-flat model
is coefficient-linear, so it is the integral local condition represented in Book 165, not only
a statement about Hodge--Tate weights after inverting $p$. These are exactly the pieces used in
Sections 2.2--2.4.

Accordingly, Theorem 1.2 needs no additional condition on the Frey representation. Theorem
4.2 proves $(\mathrm{SF}_{\mathrm{SP}})$ from Book 178's target theorem, so the Frey
application assumes neither $(\mathrm{SF}_{\mathrm{SP}})$ nor
$(\mathrm{Seed}_{\mathrm{SP}})$ independently.

Arithmetic Frobenius is used throughout. Hence the relation remains

$$
FNF^{-1}=2N.
\tag{11.3}
$$

For geometric Frobenius $\Phi=F^{-1}$ the equivalent relation is
$\Phi N\Phi^{-1}=2^{-1}N$. The line and quotient sign are unchanged by this notational
conversion.

### 11.2 The unconditional FLT-range theorem

We now prove Theorem 1.2.  This is the point at which the abstract finite-fibre criterion is
joined to the arithmetic construction of the preceding books.

**Theorem 11.1 (primitive SP lift and automorphy).** Given the normalized primitive
Fermat solution and Frey representation of Section 11.1, there are
$F^{\mathrm{tar}}$, $\mathcal O'$, and $\rho'$ satisfying all four conclusions of Theorem
1.2.

**Proof strategy.** The target source patch is completed before the minimal point exists.  Its
finite signed-special fibre is then fed into the finite-image and balance argument of this
book. Once normalization has produced the point, the previously constructed target action is
evaluated at its restriction.

**Proof.** Book 164, Theorem 1.1, gives every residual and local hypothesis of Theorem 1.1,
as checked in Section 11.1.  Book 178, Sections 12.1--12.3, prepare the actual target active
set, construct the upper primitive definite localization, and apply Book 176, Theorem 1.1K.
Book 178, Theorem 12.1, proves whole broad-ring finiteness before any minimal point is chosen;
Book 176, Corollary 1.1L, gives the finite signed-special fibre and pointwise automorphy.
Book 178, Theorem 12.2, proves those conclusions together with complete splitting at $2p$
and the two residual irreducibility statements.  Thus Theorem 4.2 supplies
$(\mathrm{SF}_{\mathrm{SP}})$ unconditionally relative to the Frey contradiction datum.

Apply Theorem 1.1.  Chapters 5--6 make the universal scalar fibre finite, Chapters 7--8 make
the universal ring a finite free one-dimensional complete intersection, and Chapters 9--10
choose and normalize a horizontal component.  The resulting $\rho'$ has cyclotomic
determinant, is unramified outside $\{2,p\}$, and is absolutely irreducible in characteristic
zero.  Equations (10.3)--(10.4) give its primitive dyadic SP datum, including the intrinsic
line, chosen sign, nonzero residual monodromy, and conductor exponent one.  Equation (10.5)
gives the compatible coefficient-linear finite-flat models at $p$.  Proposition 2.1 gives
cyclotomic residual absolute irreducibility.

Because $2$ and $p$ split completely in $F^{\mathrm{tar}}$, restriction of $\rho'$ satisfies
the signed-special deformation problem represented by
$R_{F^{\mathrm{tar}}}^{\mathrm{SP}}$.  It is therefore a characteristic-zero point of the
quotient (4.3). The pointwise clause of Book 178, Theorem 12.2, now makes
$\rho'|_{G_{F^{\mathrm{tar}}}}$ automorphic through the finite action of Book 178, Theorem
12.1.  This last invocation occurs strictly after the point has been constructed; the same
point played no role in proving (4.4). $\square$

The stronger seed of Section 4.1 remains an alternative sufficient condition for the abstract
Theorem 1.1.  Results about exact minimal $R=\mathbb T$ comparisons or other level-changing
routes lie outside the present construction and are unnecessary for Theorem 11.1.

### 11.3 Exceptional characteristics

The restriction $\ell\geq7$ is structural. In characteristic two, trace does not split the
adjoint, signs coalesce, and the determinant correction changes. In characteristic three, the
dyadic twisted-adjoint eigenvalue used in the SP vanishing becomes $4=1$, so (2.11) and the
supported balance do not have the stated proof. In characteristic five, the local SP
calculation remains favorable, but the imported image and patching range has an additional
icosahedral boundary. A theorem in any of these characteristics requires a separate local,
Selmer, and automorphic analysis.

## 12. The completed minimal-lift construction

### 12.1 Why the automorphy argument is not circular

The possible circularity is resolved by the quotient

$$
R_{F^{\mathrm{tar}}}^{\mathrm{uni}}
\twoheadrightarrow R_{F^{\mathrm{tar}}}^{\mathrm{SP}}.
\tag{12.0}
$$

Book 178 proves that the ring on the left is finite by using an upper packet which is special
at the active auxiliary places. This upper packet is not a point of the quotient on the right:
its nonzero auxiliary monodromy generally prevents that. Nevertheless, the quotient is finite
because it is a quotient of the finite broad ring. Chapters 5--10 use this consequence to
construct a characteristic-zero point of the signed-special ring over $\mathbf Q$.

After restriction to $F^{\mathrm{tar}}$, the new point is unramified at the active places and
therefore factors through the right-hand side of (12.0), hence also defines a point of the
broad ring. The nilpotent-kernel theorem for the broad Hecke action then makes this particular
point automorphic. Thus two different characteristic-zero representations play two different
roles: the upper packet proves finiteness of the ambient ring, while the newly normalized
minimal point is identified automorphically only after it has been constructed.

The automorphic condition $(\mathrm{Seed}_{\mathrm{SP}})$ offers a separate route to the
abstract finite-fibre hypothesis through Book 173. It is not part of the unconditional
Frey-range theorem.

### 12.2 The chosen lift for the changing-prime argument

Fix the horizontal component selected in Chapter 9 and the resulting representation $\rho'$.
Its data are not merely generic.  On the chosen $\mathcal O'$-lattice one has

$$
\det\rho'=\chi_p,
\qquad
\rho'\text{ unramified outside }\{2,p\},
\tag{12.1}
$$

and $\rho'$ is absolutely irreducible over $\operatorname {Frac}(\mathcal O')$.  Its residual
representation is $\bar\rho\otimes_k k'$, whose restriction to the cyclotomic subgroup remains
absolutely irreducible.  At $p$, every quotient
$\rho'\bmod\mathfrak m_{\mathcal O'}^n$ has the selected coefficient-linear finite-flat model,
compatibly in $n$.  At $2$, the same lattice carries a primitive rank-one operator $N'$ with

$$
N'\bmod\mathfrak m_{\mathcal O'}=\bar N\otimes_k k'\ne0,
\qquad
\ker N'=\operatorname {im}N',
\qquad
F'N'(F')^{-1}=2N'.
\tag{12.2}
$$

The quotient Frobenius has the chosen sign, wild inertia is trivial, and the conductor exponent
is one. Finally, over the field $F^{\mathrm{tar}}$ constructed in Book 178, Theorem 12.2, the
restriction $\rho'|_{G_{F^{\mathrm{tar}}}}$ factors through the finite automorphic
action. Thus $\rho'$ simultaneously has primitive SP monodromy, the integral finite-flat
coefficient condition, the required irreducibility, and automorphy over
$F^{\mathrm{tar}}$, as needed to start the changing-prime argument.

### 12.3 Conclusion

The central algebraic implication of this book is

$$
\boxed{
(\mathrm{SF}_{\mathrm{SP}})
\Longrightarrow
\begin{gathered}
R^{\mathrm{hr,SP}}\text{ is a finite free one-dimensional complete intersection over }
\mathcal O,\\
\text{and a normalized horizontal component gives a primitive integral SP lift.}
\end{gathered}}
\tag{12.3}
$$

For a Frey residual representation, Theorem 4.2 proves the hypothesis from Book 178,
Theorems 12.1 and 12.2, using Book 176, Corollary 1.1L. Theorem 11.1 then gives the lift and
identifies its restriction with an automorphic representation. The heart of the argument is
that a lower dimension bound from Selmer theory and an upper bound from restricted
automorphy meet at dimension one. Their equality produces a finite free complete intersection,
and normalization turns that geometric fact into the primitive integral representation needed
for the changing-prime method.
