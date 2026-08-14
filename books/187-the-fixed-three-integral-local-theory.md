# The Fixed-Three Integral Local Theory

## Contents

1. [The rational member and the integral problem](#1-the-rational-member-and-the-integral-problem)
2. [The coefficient-prime comparison certificate](#2-the-coefficient-prime-comparison-certificate)
3. [Constructing a strongly divisible lattice](#3-constructing-a-strongly-divisible-lattice)
4. [From a local lattice to one global lattice](#4-from-a-local-lattice-to-one-global-lattice)
5. [Every coefficient level and every transition](#5-every-coefficient-level-and-every-transition)
6. [The signed special place at two](#6-the-signed-special-place-at-two)
7. [Clean support away from two and three](#7-clean-support-away-from-two-and-three)
8. [Gluing over the integers with two inverted](#8-gluing-over-the-integers-with-two-inverted)
9. [The exact handoff to the Schoof endgame](#9-the-exact-handoff-to-the-schoof-endgame)
10. [The conditional fixed-three theorem](#10-the-conditional-fixed-three-theorem)
11. [Dependency and hostile audits](#11-dependency-and-hostile-audits)
12. [Conclusion and readiness](#12-conclusion-and-readiness)

## 1. The rational member and the integral problem

### 1.1 What Books 185--186 actually supply

The change from a compatible family to its member of coefficient characteristic three is
not a scalar extension of the original lift. It is the selection of another member of the
same algebraic family. That distinction is the starting point of this book.

Assume the controlled signed-special, or **SP**, top datum used by Books 183--185. The
restricted conclusion of Book 185, which does not assume $(\mathrm{AI}_2)$, gives a number
field $E$ and an away-from-two collection of actual continuous rank-two representations

$$
\mathcal R^{(2)}=
\left\{r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda)
\right\}_{\lambda\nmid2}.
\tag{1.1}
$$

Here and below $\lambda$ ranges only over $\lambda\nmid2$. These members are semisimple and
absolutely irreducible. They have cyclotomic determinant and one algebraic system of pure
weight-one good Frobenius polynomials. At the rational prime two they have the same full SP
Weil--Deligne object. This is not the tame-quadratic branch. Its finite Weil inertia is trivial
and its monodromy is nonzero of rank one. Book 186, Theorem 7.1, packages the selection made
below and proves explicitly that it uses only this away-from-two collection.

Choose a place $\nu\mid3$ and write

$$
K=E_\nu,\qquad
\mathcal O=\mathcal O_K,\qquad
\mathfrak m=(\varpi),\qquad
k=\mathcal O/\mathfrak m,
\tag{1.2}
$$

and

$$
V=r_\nu.
\tag{1.3}
$$

Thus $V$ is an honest $K$-representation, not a virtual Brauer class, and

$$
\det V=K(1).
\tag{1.4}
$$

At two, in arithmetic-Frobenius normalization, Book 186 transports from the restricted Book
185 family an algebraic pair

$$
D_2=(r_2,N_2),\qquad
N_2^2=0,\qquad
N_2\ne0,\qquad
\operatorname{rank}N_2=1,
\tag{1.5}
$$

with

$$
r_2(F_2)N_2r_2(F_2)^{-1}=2N_2.
\tag{1.6}
$$

Its intrinsic line and sign are

$$
\mathscr L_2=\ker N_2=\operatorname{im}N_2,
\tag{1.7}
$$

and, for one $\varepsilon_2\in\{1,-1\}$, arithmetic Frobenius acts by

$$
(\varepsilon_2,2\varepsilon_2)
\tag{1.8}
$$

on the quotient and line, in that order. Its Artin conductor exponent is one. These are
already the correct Frey local data. A lattice cannot turn this pair into a monodromy-zero
finite inertial type, and no such replacement will be made below.

Since $\nu\mid3$, no coefficient place above two occurs in this input. In particular, neither
the local and integral arguments below nor their global gluing theorem use
$(\mathrm{AI}_2)$. The missing assertions for $V$ are instead the coefficient-three and
clean-support certificates isolated next.

### 1.2 What rational assembly deliberately leaves open

The rational theorem stops at exactly the point where an integral small-ramification argument
must begin. It does not provide any of the following.

- It does not compare $V|_{G_{\mathbf Q_3}}$ with a good coefficient-prime geometric
  object.
- It does not prove that $V|_{G_{\mathbf Q_3}}$ is crystalline or that its Hodge jumps are
  zero and one.
- It does not select a globally stable lattice whose coefficient quotients are finite flat.
- It does not make the characteristic-zero Brauer cancellation integral.
- It does not certify unramifiedness at every auxiliary prime in its finite exceptional set.

The first two omissions are not cosmetic. Prime-to-coefficient local--global compatibility at
the rational prime three applies to members whose coefficient characteristic is not three. It
does not apply to (1.3). An unramified three-local Weil--Deligne companion at another
coefficient place does not prove that $V$ is crystalline over $\mathbf Q_3$.

The last omission is equally important. Book 185 proves unramifiedness outside a finite set
and removes an auxiliary prime only when its actual local comparison lies in the proved
range. Equality of almost all Frobenius polynomials does not force inertia to be trivial at an
omitted prime. A global group scheme over $\mathbf Z[1/2]$ therefore cannot yet be glued.

### 1.3 The two certificates needed here

We isolate the missing data rather than hiding them in the phrase “weight-two compatible
system.”

The **coefficient-prime certificate** $(\mathrm C_3)$ is the assertion

$$
V|_{G_{\mathbf Q_3}}
\text{ is crystalline of Fontaine--Laffaille Hodge type }(0,1).
\tag{C3}
$$

Equivalently, its crystalline periods have full dimension two and, in the covariant
normalization below, the resulting filtered Frobenius module is weakly admissible, has one
Hodge line, and has total Newton number one. The full-dimension condition is essential: the
filtered numerical assertions alone, applied to a proper period subspace, would not certify
crystallinity of $V$. Section 2 gives two concrete ways an upstream geometric theorem can prove
this certificate. It is a rational comparison certificate; no lattice is included in it.

The **clean-support certificate** $(\mathrm U)$ is the assertion

$$
V\text{ is unramified at every rational prime }q\ne2,3.
\tag{U}
$$

It is enough to verify $(\mathrm U)$ at the finite auxiliary set left by Book 185, since
unramifiedness outside that set is already proved. A reusable version records at each such
prime the algebraic unramified local pair and its Frobenius polynomial; this also extends the
good-prime ledger needed for compatibility arguments.

The local integral theorem of Chapters 3--6 uses $(\mathrm C_3)$ but not $(\mathrm U)$. The
global gluing theorem of Chapter 8 uses both. This separation identifies exactly which part of
the construction remains available if the global clean-support comparison is still missing.

Both certificates concern the single selected member $V=r_\nu$. They are not a request for
integral models at every odd coefficient place of the compatible family. The final argument
needs all coefficient levels at this one place and all odd *base-prime* local models for those
levels. This is strictly weaker than the blueprint's family-wide all-odd integral-model
record.

### 1.4 The target

Starting from (1.1)--(1.8) and $(\mathrm C_3)$, we shall construct rather than assume:

1. one globally $G_{\mathbf Q}$-stable free rank-two $\mathcal O$-lattice $T\subset V$;
2. for every nonzero proper ideal $I\subset\mathcal O$, a marked coefficient-linear
   finite-flat model of $T/IT$ over $\mathbf Z_3$;
3. all coefficient-reduction morphisms and all exact multiplication sequences between those
   models;
4. the saturated signed SP line inside the same global lattice and its exact reductions at
   every level; and
5. determinant and duality records with the coefficient-dual warning retained.

Under $(\mathrm U)$ we shall then glue these local objects to one compatible tower over
$\mathbf Z[1/2]$. That tower, rather than rational crystallinity or a collection of unrelated
finite-flat witnesses, is the input to the Schoof endgame.

## 2. The coefficient-prime comparison certificate

### 2.1 Why this is the first post-assembly question

At a rational prime $q\ne3$, a three-adic representation with quasi-unipotent inertia has a
Weil--Deligne pair. At $q=3$, the correct comparison category is filtered crystalline theory.
The assertions

$$
N_3=0
\qquad\text{and}\qquad
V|_{G_{\mathbf Q_3}}\text{ crystalline}
\tag{2.1}
$$

are not interchangeable: the first is a prime-to-coefficient statement made about other
members, while the second is a period-dimension equality for the selected three-adic member.
Even potential crystallinity would not be enough for this book, because the finite-flat models
must exist over $\mathbf Z_3$, not only after a ramified extension.

This explains why $(\mathrm C_3)$ is the first exact local question after the
$(\mathrm{AI}_2)$-independent prime-three selection of Book 186.  It is not, however, an
irreducible new arithmetic hypothesis once a good carrier exists: Section 2.5 derives the
stronger $(\mathrm{IC}_3)$ from $(\mathrm{AVCar}_{3,\ell}^+)$ once $3$ was named split in
the controlled top and its split local packet was supplied. Section 2.5 reduces that carrier
certificate to the finite unitary common-multiplier cover constructed there.
Once $(\mathrm C_3)$ is known,
the lattice and tower will be consequences. Before it is known, integral Fontaine--Laffaille
theory has no object to which it can be applied.

### 2.2 A direct good-reduction certificate

One acceptable source for $(\mathrm C_3)$ is a genuine good geometric carrier. Suppose there
is an abelian scheme $\mathcal A/\mathbf Z_3$. Choose a finite power $\mathcal B$ of
$\mathcal A$ or $\mathcal A^\vee$ in the covariant normalization, equipped with a commuting
coefficient action, such that $M_{\mathrm{geom}}=T_3\mathcal B$ is finite free over $\mathcal O$.
Assume there is a rational $G_{\mathbf Q_3}$-equivariant embedding

$$
V\hookrightarrow
M_{\mathrm{geom}}\otimes_{\mathcal O}K.
\tag{2.2}
$$

The normalization in (2.2) matters. Untwisted curve $H^1$ is not itself the covariant Tate
module; the Kummer comparison inserts the required Tate twist or Cartier-twisted dual. A
statement that forgets this twist can reverse the determinant and does not prove finite
flatness for the desired representation.

Smooth proper comparison makes the ambient rational Tate representation crystalline with
Hodge jumps in $\{0,1\}$. The crystalline category is closed under subobjects. Hence $V$ is
crystalline and also has jumps only at zero and one. Equation (1.4) says their sum is one, so
they are exactly $0$ and $1$. This proves $(\mathrm C_3)$.

The geometric certificate is stronger than needed: Book 129 then constructs the first local
lattice directly as the saturated intersection of (2.2) with the ambient Tate lattice and
constructs its closure tower in abelian torsion. We will nevertheless develop the filtered
route because it also applies when the upstream theorem provides a rational comparison without
a fixed abelian carrier.

### 2.3 A certificate through actual Brauer cancellation

Book 185, Proposition 9.2 provides at the selected $\nu\mid3$ an actual
characteristic-zero cancellation

$$
R_\nu^+\simeq V\oplus R_\nu^-.
\tag{2.3}
$$

This identity alone proves no coefficient-prime Hodge property. It becomes a certificate if
an upstream theorem separately proves that the restrictions of both displaying terms to
$G_{\mathbf Q_3}$ are crystalline and have Hodge jumps only at zero and one. For example,
this can follow when three splits completely in every field used in the display, the finite
Brauer characters are locally unramified there, and each elementary packet has an actual
smooth-proper good comparison at its coefficient-prime place.

Under those hypotheses, restrict (2.3) to $G_{\mathbf Q_3}$. Crystalline representations are
closed under direct summands, so

$$
D_{\mathrm{cris}}(R_\nu^+)
\simeq D_{\mathrm{cris}}(V)\oplus D_{\mathrm{cris}}(R_\nu^-)
\tag{2.4}
$$

and $\dim_KD_{\mathrm{cris}}(V)=2$. Strictness of the filtration on crystalline
representations leaves only Hodge jumps zero and one on the summand. The determinant again
forces one of each. Thus (2.3), together with the displaying-term comparison, proves
$(\mathrm C_3)$.

The order of this argument is load bearing:

$$
\text{actual cancellation}
+\text{crystalline displaying terms}
\Longrightarrow\text{crystalline complement}.
\tag{2.5}
$$

A signed equality in a Grothendieck group or an equality of Hodge-number sums would not be
enough. Book 185 supplies the first term of (2.5), not the second.

### 2.4 A source-facing flat companion

The arithmetic source audited for the compatible-family step is naturally stronger than the
rational certificate $(\mathrm C_3)$. Its coefficient-three specialization would supply the
following datum.

> **Flat-companion certificate $(\mathrm{IC}_3)$.** There are a finite free local
> $\mathbf Z_3$-domain $A$, its fraction field $L=A[1/3]$, a free rank-two $A$-module $W$
> with continuous $G_{\mathbf Q}$-action, and a finite common coefficient extension $C$ such
> that
> $$
> W[1/3]\otimes_{L}C\simeq V\otimes_KC.
> \tag{IC3}
> $$
> Every quotient $W/IW$ by an open ideal of $A$, restricted to $G_{\mathbf Q_3}$, is the
> marked generic fiber of a finite-flat commutative group over $\mathbf Z_3$.

The full source-facing datum also retains the integral quotient at two. That extra local
condition is useful for the general hardly-ramified family theorem, but it is not needed for
the implication below because Book 186 has already supplied the rational SP pair.

**Proposition 2.1 (flat companion implies $(\mathrm C_3)$).** The certificate
$(\mathrm{IC}_3)$, together with $\det V=K(1)$, proves that
$V|_{G_{\mathbf Q_3}}$ is crystalline of Hodge type $(0,1)$.

**Proof.** Regard $W$ first as a finite free $\mathbf Z_3$-lattice. For every $n\ge1$, the
ideal $3^nA$ is open, so $(\mathrm{IC}_3)$ makes $W/3^nW$ finite flat over
$\mathbf Z_3$. In the Fontaine--Laffaille range $[0,1]\subset[0,3-2]$, Book 54, Theorem
14.1 reconstructs from these finite levels a strongly divisible lattice of weights in
$[0,1]$. The transition maps do not require an additional arithmetic input: marked
finite-flat models are fully faithful over $\mathbf Z_3$, and Book 54's compatible-quotient
theorem reconstructs the unique compatible system. After inverting $3$, the rational
Fontaine--Laffaille comparison used again in Section 3.3 identifies the resulting
representation with the crystalline realization of that strongly divisible module. Hence
$W[1/3]$ is crystalline and all of its Hodge--Tate weights lie in $\{0,1\}$.

Enlarge $C$ finitely so that it contains every $\mathbf Q_3$-embedding of $L$. The commuting
$L$-action gives

$$
W[1/3]\otimes_{\mathbf Q_3}C
\simeq
\bigoplus_{\jmath:L\hookrightarrow C}
W[1/3]\otimes_{L,\jmath}C.
$$

Each summand is cut out by an idempotent commuting with $G_{\mathbf Q_3}$. Crystalline
representations of weights in $[0,1]$ are preserved by finite coefficient extension and by
direct summands. The summand selected in (IC3) is $V\otimes_KC$, so it is crystalline with
weights in $\{0,1\}$. Crystallinity and the filtered dimensions descend through the faithful
finite extension $K\to C$. Finally, the determinant $K(1)$ says that the two Hodge--Tate
weights have sum one. Since each is zero or one, they are exactly $0$ and $1$. $\square$

Thus $(\mathrm{IC}_3)$ is a sufficient integral source for the rational hypothesis used in
Chapters 3--6, and in fact already contains finite-flat witnesses. The point of Proposition
2.1 is that no unproved passage from the word ``flat'' to the selected crystalline member is
left implicit. Once $(\mathrm C_3)$ has been extracted, Proposition 3.1 and Chapters 4--5
construct the named $K$-lattice required here without descending a particular auxiliary
$A$-lattice.

In the audited source, $(\mathrm{IC}_3)$ is the coefficient-three case of the
away-from-original-prime integral-companion clause in the compatible-family arithmetic
theorem. Its displayed comparison is made over an algebraic closure, but this introduces no
further arithmetic premise: after choosing bases, the intertwiner has finitely many algebraic
matrix entries, hence descends to a finite extension containing the chosen images of $L$ and
$K$. This is the field $C$ in (IC3). That arithmetic theorem is admitted rather than derived
there; the later three-adic and Schoof stages merely consume its flatness clause. The
blueprint likewise states that the three-adic specialization is flat but supplies only a sketch of the
potential-modularity/Brauer argument. Consequently Proposition 2.1 closes the reduction from
that source theorem.  Section 2.5 gives a different, FLT-scoped geometric proof which avoids
that source theorem once the actual positive packet carriers have been constructed.

### 2.5 The fixed-three positive-carrier theorem

There is a direct geometric route to $(\mathrm{IC}_3)$ which is substantially weaker than
the source-facing compatible-family arithmetic core.  Book 158, Theorem 5.1 and Book 182,
Section 4.2 construct the exact split evaluated packet over $\mathbf Q_3$ together with the packets
over $\mathbf Q_2$ and $\mathbf Q_\ell$.  The normal-top construction therefore makes $3$
split completely in $M$ and hence in every elementary fixed field.  After the top and one
integral Brauer datum
$\mathfrak B=\{(H_i,\theta_i,n_i)\}$ have been chosen, write
$n_i=n_i^+-n_i^-$.  Book 182, Proposition 6.1 already supplies every corrected packet with an
actual compact division-quaternion one-split basic carrier $X_i$ and its all-coefficient
attachment, while Proposition 8.1 supplies its common unramified algebraic pair away from two.
If $d_i=[M^{H_i}:\mathbf Q]$ is even, its finite ramification set can be one
dyadic special place; if $d_i$ is odd, it can be empty.  In both cases the carrier is split and
the packet is spherical at every place above $3\ell$.  Thus basic carrier existence is no
longer part of the positive hypothesis below.

The still weaker output actually used below will be denoted
$(\mathrm{AVCar}_{3,\ell}^+)$.  It asks, for each positive elementary term, for an abelian
variety over the elementary fixed field with good reduction at all places above $3$ and
$\ell$, together with a rational embedding of the correctly twisted raw multiplicity plane
into a finite power of its covariant Tate module, equipped with the regular integral
coefficient action of Book 129, and the identification of the plane's semisimplification with
the elementary representation.  The relative Jacobian of a curve
carrier is the intended source, but it is not part of the minimal statement.  The subscript
$\ell$ is irrelevant to the finite-flat construction but will remove the old coefficient
prime from the selected member's auxiliary support in Section 7.2.  Both carrier symbols retain
the split-at-three controlled-top and local-packet requirement in the preceding paragraph.

The previously proposed direct common-norm source for this output is impossible in the present
mixed signature.

**Lemma 2.2A (the common-norm carrier is vacuous).**  For every elementary term in the
controlled top, the one-split basic Hodge map does not lift to the connected common-norm group

$$
G_i^\star=\{b\in\operatorname{Res}_{F_i/\mathbf Q}B_i^\times:
\operatorname{Nrd}(b)\in\mathbf G_m\}.
$$

Hence no direct-trace common-norm PEL curve of the kind formerly required by
$(\mathrm{Car}_3^+)$ exists.

**Proof.**  The group $\Gamma=G_0\times S_5$ is not solvable, while every elementary subgroup
$H_i$ is solvable.  Thus $H_i\ne\Gamma$ and $[F_i:\mathbf Q]=[\Gamma:H_i]>1$.  The carrier has
one active split real place and at least one compact real place.  Book 118, Proposition 8.2
then applies: at the active factor every lift has reduced-norm character
$(z\bar z)^{2m+1}$, while an adjoint-trivial compact factor has reduced-norm character
$(z\bar z)^{2n}$.  The common-norm equation cannot equate an odd and an even exponent.  Varying
the pure multiplier, the order, or the finite level does not change this real-group
obstruction. $\square$

The replacement is the unitary common-multiplier, or modèle-étrange, cover.  Choose once an
imaginary quadratic field $K_{\mathrm{CM}}/\mathbf Q$ which is nonsplit at $2$ and split at
$3$ and $\ell$.
The $n=2$ case of Book 6, Theorem 6.1 and its Grunwald alternative supplies such a field after
prescribing the nontrivial local class at the real place and at $2$, and the trivial class at
$3$ and $\ell$; there is no Wang exception at exponent two.  For a positive term put

$$
L_i=F_iK_{\mathrm{CM}}.
\tag{2.5b}
$$

The field $F_i$ is totally real, so $F_i\cap K_{\mathrm{CM}}=\mathbf Q$.  If $d_i$ is odd, $B_i$ has no
finite ramification.  If $d_i$ is even, its only finite ramified place is one $w_i\mid2$ and
$(F_i)_{w_i}=\mathbf Q_2$; nonsplitting of $K_{\mathrm{CM}}$ at $2$ makes $(L_i)_{w_i}$ a field.  At every
ramified real place $L_i$ is complex.  The quaternion embedding criterion of Book 118,
Section 8.5 therefore gives

$$
L_i\hookrightarrow B_i.
\tag{2.5c}
$$

Regard $B_i$ as a rank-two right $L_i$-space with Hermitian norm
$H_i(x,x)=\operatorname{Nrd}_{B_i}(x)$.  Book 118, Proposition 8.3 constructs the PEL-exact
unitary common-multiplier central modification $G_i^{\mathrm u}$, with reflex field $L_i$ and
the same adjoint datum as the basic curve.  This is the trivial-character FLT packet: Book 127,
Section 6.2 records $s_v=1$ and $\eta=1$ (equivalently, its covariant determinant is
cyclotomic), and Book 182 retains that normalization on every candidate.
Enlarging the basic local levels by the central signs therefore changes neither the packet
block nor its raw multiplicity plane and makes the level centrally saturated on
$\operatorname{Res}_{F_i/\mathbf Q}B_i^1$.  Corollary 10.3A, applied with
$S=\{3,\ell\}$, gives a finite extension $E_i/L_i$ unramified above $3\ell$, a unitary
PEL component union $Y_i/E_i$, and, at compatible levels and on the full component-routing
unions, a finite surjective morphism

$$
f_i:Y_i\longrightarrow X_i\times_{F_i}E_i.
\tag{2.5d}
$$

The integral ledger can be imposed simultaneously at $3$ and $\ell$. Indeed, these primes
split completely in $F_i$, the algebra $B_i$ is split there, and splitting of $K_{\mathrm{CM}}$ gives the
two CM idempotents. Multiply the anti-invariant $\xi$ of (8.3b) by a totally positive element
of $F_i^\times$ chosen by weak approximation so that it is a unit at those places; this
preserves every polarization sign. The standard split Hermitian
plane has a self-dual lattice; Book 82, Section 4.3 patches these prescribed local lattices into
one global $\mathcal O_{L_i}$-lattice. Take the full routed component union together with its
finite Galois orbit over $L_i$, choose polarization type prime to $3\ell$, and choose the fine
level hyperspecial at both primes, shrinking only away from them. This union is globally
$L_i$-defined and in particular stable under both decomposition groups; adding its finitely
many translates preserves finite surjectivity. Corollary 10.3A permits these simultaneous
compatible level choices.

Book 121, Theorem 11.2 gives smooth projective models of the unitary component union over
$L_i$ and good reduction of its relative Picard scheme at all places above $3\ell$.
Corollary 10.3A constructs $Y_i$ by lowering only the prime-to-$3\ell$ unitary level, so the
same theorem applies to those globally defined orbit unions.  After the unramified base
change to $E_i$, their component idempotents are open and closed, so the selected labelled
union remains smooth and projective.
This exact construction is $(\mathrm{Car}_3^+)$.  It is unitary common-multiplier PEL
geometry, not the impossible direct common-norm trace datum of Lemma 2.2A.

**Proposition 2.2 (the unitary cover supplies the abelian carrier).**  The construction
$(\mathrm{Car}_3^+)$ proves $(\mathrm{AVCar}_{3,\ell}^+)$.

**Proof.**  Book 127 extracts the intrinsic raw rank-two multiplicity plane from $H^1(X_i)$
and, in (2.5) and (2.9), defines its covariant form by the Tate twist.  Write
$W_i^{\mathrm{raw}}$ for that covariant plane, as in the FLT normalization, and choose a
nonzero vector in its finite oldvector factor.  On each target component, pullback and trace
on $H^1(1)$ give

$$
(f_i)_*f_i^*=(\deg f_{i,\mathrm{comp}})\operatorname{id}
$$

on rational first cohomology.  The component degrees are nonzero, so after restriction to
$G_{E_i}$ the map $f_i^*$ embeds the raw plane into, at every coefficient place $\lambda$,

$$
H^1_{\mathrm{et}}(Y_{i,\overline E_i},L_\lambda(1))
\simeq V_\lambda(\operatorname{Pic}^0_{Y_i}),
$$

by Book 125, (3.4).

Let $J_i=\operatorname{Pic}^0_{Y_i/E_i}$, the product of the Jacobians of the smooth
projective components of $Y_i$, and put

$$
A_i=\operatorname{Res}_{E_i/F_i}J_i.
\tag{2.5e}
$$

This is an abelian variety over $F_i$.  At every place above $3\ell$ the quadratic algebra
$L_i/F_i$ is split and $E_i/L_i$ is unramified.  Weil
restriction along the resulting finite etale extension of local valuation rings preserves
abelian schemes: Book 26, Sections 20.4--20.5 represent the restriction and commute it with
base change, after which the split cover is a product of abelian schemes and Book 10 descends
the abelian-scheme properties.  Thus (2.5e) has good reduction.  Over $\overline F_i$ the same
base-change formula is the product indexed by the embeddings $E_i\hookrightarrow\overline F_i$;
Galois permutes those factors, so on rational Tate modules

$$
V(A_i)\simeq
\operatorname{Ind}_{G_{E_i}}^{G_{F_i}}V(J_i).
\tag{2.5f}
$$

The constant-function line in the finite permutation representation gives a
$G_{F_i}$-equivariant injection

$$
W_i^{\mathrm{raw}}
\longrightarrow
\operatorname{Ind}_{G_{E_i}}^{G_{F_i}}
\operatorname{Res}_{G_{E_i}}^{G_{F_i}}W_i^{\mathrm{raw}}.
\tag{2.5g}
$$

Inducing $f_i^*$ and using (2.5f) embeds the correctly covariantly twisted raw plane into a
finite power of $V(A_i)$.  A finite further power realizes the regular integral coefficient
action exactly as in Book 129, Section 1.2. Proposition 6.1 of Book 182 identifies the
plane's semisimplification with the elementary representation used by Book 185.  Thus every
clause of $(\mathrm{AVCar}_{3,\ell}^+)$ holds.  Neither the degree of $f_i$ nor $[E_i:F_i]$
is required to be a unit: only a rational injection is used, and Book 129 later
saturates it rather than extending an integral projector.  In particular, no extension of
$f_i$ to the basic curve's integral model is asserted or needed; the good integral model is
the proved unitary source model. $\square$

**Theorem 2.3 (the positive display supplies $(\mathrm{IC}_3)$).** Under
$(\mathrm{AVCar}_{3,\ell}^+)$, and hence under the constructed $(\mathrm{Car}_3^+)$ for every
positive term, the actual cancellation
(2.3) constructs a flat companion satisfying $(\mathrm{IC}_3)$.  In fact its quotients form
one compatible exact coefficient-linear finite-flat tower over $\mathbf Z_3$.

**Proof.** Enlarge the coefficient field once to a finite extension $C/K$ which splits all
positive packet blocks, and put $A=\mathcal O_C$.  For a positive elementary packet and a
place $w\mid3$, use the rational embedding supplied by
$(\mathrm{AVCar}_{3,\ell}^+)$.  When that certificate comes from Proposition 2.2, it is the
composite of a nonzero-oldvector embedding with $f_i^*$.  Book 129, Theorem 5.1 applies to a
finite power of the supplied good abelian variety; saturated intersection and schematic
closure give an all-level finite-flat lattice in that raw plane.  Book 129,
Proposition 8.1 transfers existence of such a tower to its global semisimplification.
Book 129, Section 7.2 then extends each tower to the common coefficient DVR $A$; possible
ramification of $C/K$ changes the coefficient different in duality but not finite flatness.

Choose any global stable $A$-lattice $L_i$ in that elementary semisimple representation.
At each of the finitely many $w\mid3$, it is commensurable with the lattice just constructed,
so Book 129, Proposition 9.1 gives finite-flat models for all quotients of the same global
lattice $L_i$.  This is why no simultaneous choice of geometric packet lattice is needed.

Now induce $L_i\otimes\theta_i$ to $G_{\mathbf Q}$ and take the required positive direct
sums.  Local Mackey decomposition at $3$ is an actual direct sum over $w\mid3$: every
completion $(F_i)_w$ is $\mathbf Q_3$ and $\theta_i|_{G_{(F_i)_w}}=1$.  Products of the
elementary finite-flat towers therefore give a global stable $A$-lattice
$L^+\subset R_{\mathfrak B,\nu}^+\otimes_KC$ whose restriction at $3$ has an all-level
finite-flat tower.

After extending (2.3) to $C$, fix the resulting rational injection

$$
V\otimes_KC\hookrightarrow R_{\mathfrak B,\nu}^+\otimes_KC
$$

and set

$$
W=L^+\cap(V\otimes_KC).                                      \tag{2.5a}
$$

This is a free rank-two globally stable $A$-lattice and is saturated in $L^+$.  Hence
$W/\varpi_C^nW$ injects into $L^+/\varpi_C^nL^+$ for every $n$.  Close this marked generic
subgroup in the known finite-flat model of the latter quotient.  Schematic closure over a
DVR is finite flat.  Since $e(\mathbf Z_3)=1<3-1$, Raynaud full faithfulness identifies the
closure kernels and represented quotients at different levels and makes the transition maps
coefficient linear and exact, exactly as in Book 129, Propositions 4.1 and 8.1.  Every open
ideal of the DVR $A$ is $(\varpi_C^n)$, while

$$
W[1/3]=V\otimes_KC.
$$

Thus $(A,W,C)$ is the datum $(\mathrm{IC}_3)$. $\square$

Two features of this proof are important.  Only the positive displaying terms need good
carriers.  Also, no rational packet idempotent and no projector for the summand $V$ is extended
integrally: nonzero-oldvector embeddings, saturated intersections, schematic closures, and
represented quotients replace every such step.  Denominators in the rational Hecke
idempotents therefore do not obstruct $(\mathrm{IC}_3)$.  Ambient Tate-module semisimplicity
is not needed for this fixed-three conclusion either: Book 129, Proposition 8.1 transfers the
finite-flat existence property from the raw plane to its semisimplification.

In particular, the proof does not assert that $V$ is the Tate module of an abelian quotient.
It places $V$ rationally inside the product of the positive good abelian carriers and closes a
saturated lattice in their torsion.  This weaker carrier relation is exactly what finite
flatness needs and avoids an unsourced integral idempotent or isogeny-factor theorem.

The theorem removes $(\mathrm{IC}_3)$ as an independent post-assembly arithmetic premise once
$(\mathrm{AVCar}_{3,\ell}^+)$ is supplied. Book 182 supplies basic positive attachment and the
split $\mathbf Q_3$ packet; Proposition 2.2 supplies $(\mathrm{AVCar}_{3,\ell}^+)$ from the
unitary PEL covers.  Thus no additional full compatible-family arithmetic core is needed at
three.  This
positive-only argument does not make characteristic-zero Brauer cancellation integral; it
uses the actual rational injection (2.3), saturated intersections, and finite-flat closure.

### 2.6 The filtered module

Assume $(\mathrm C_3)$ and put

$$
D=D_{\mathrm{cris}}(V|_{G_{\mathbf Q_3}}),
\qquad
L=\operatorname{Fil}^1D.
\tag{2.6}
$$

Then $D$ is a two-dimensional $K$-space, $L$ is a $K$-line, and Frobenius $\varphi$ is
$K$-linear because the local ground field is $\mathbf Q_3$. In the covariant
Fontaine--Laffaille normalization used here,

$$
t_H(D)=1=t_N(D),
\qquad
v_3(\det\varphi)=1,
\tag{2.7}
$$

where $v_3(3)=1$. Weak admissibility also says

$$
t_N(D')\ge t_H(D')
\tag{2.8}
$$

for every $\varphi$-stable subobject $D'$. The line inequalities in (2.8), not merely the
total equality in (2.7), are what permit an integral lattice to be constructed.

## 3. Constructing a strongly divisible lattice

### 3.1 The integral problem in rank two

A rational filtered module does not come with a preferred lattice. We seek one free
$\mathcal O$-lattice $M\subset D$ for which

$$
F_M=M\cap L
\tag{3.1}
$$

is a saturated rank-one submodule and divided Frobenius generates $M$.

More precisely, we require $\varphi(M)\subset M$ and
$\varphi(F_M)\subset 3M$, set
$\varphi_0=\varphi|_M$ and $\varphi_1=3^{-1}\varphi|_{F_M}$, and require their normal map to
be an isomorphism. If

$$
M=\mathcal Oe_0\oplus\mathcal Oe_1,
\qquad F_M=\mathcal Oe_1,
\tag{3.2}
$$

then strong divisibility is the assertion that the two columns

$$
\varphi(e_0),\qquad 3^{-1}\varphi(e_1)
\tag{3.3}
$$

form an $\mathcal O$-basis of $M$. At the prime three this is exactly within the interval
$[0,1]\subset[0,3-2]$ of integral Fontaine--Laffaille theory.

The next proposition proves existence directly from (2.7)--(2.8). It does not assume that the
rational representation has already been given a finite-flat lattice.

### 3.2 The explicit rank-two construction

**Proposition 3.1 (strongly divisible lattice).** The filtered Frobenius module $(D,L,\varphi)$
contains a free strongly divisible $\mathcal O$-lattice $M$ of Hodge type $(0,1)$.

**Proof.** We separate the two possible positions of the Hodge line.

Suppose first that $L$ is not $\varphi$-stable. Choose $0\ne e_1\in L$ and put

$$
e_0=3^{-1}\varphi(e_1).
\tag{3.4}
$$

The two vectors are a basis, since proportionality would make $L$ stable. Define

$$
c=\operatorname{tr}\varphi,
\qquad
u=3^{-1}\det\varphi.
\tag{3.5}
$$

We first show

$$
c\in\mathcal O,
\qquad
u\in\mathcal O^\times.
\tag{3.6}
$$

If one Newton slope were negative, the two slopes would be distinct because their sum is one.
The slope-factorization theorem for polynomials over a complete valued field would then split
off the length-one negative-slope segment, producing a $K$-rational $\varphi$-stable line.
That line would have Hodge number zero: it cannot equal $L$, since $L$ is not stable. This
would contradict (2.8). Hence both slopes are nonnegative. Their sum is one, so the determinant
has valuation one, as already recorded in (2.7), and $u$ is a unit. Both eigenvalues are
integral over $\mathcal O$; their sum lies in $K$, hence belongs to the integrally closed ring
$\mathcal O$. Thus $c\in\mathcal O$.

Cayley--Hamilton and (3.4) now give

$$
\varphi(e_0)=ce_0-ue_1,
\qquad
3^{-1}\varphi(e_1)=e_0.
\tag{3.7}
$$

Set

$$
M=\mathcal Oe_0\oplus\mathcal Oe_1.
\tag{3.8}
$$

Because $L=Ke_1$, its intersection with $M$ is $F_M=\mathcal Oe_1$, which is saturated.
The normal matrix whose columns are (3.7) is

$$
\begin{pmatrix}c&1\\-u&0\end{pmatrix}.
\tag{3.9}
$$

Its determinant is the unit $u$, so (3.3) is a basis. This is strong divisibility.

Suppose now that $L$ is $\varphi$-stable, and let $\alpha\in K^\times$ be its eigenvalue.
Weak admissibility of $L$ gives $v_3(\alpha)\ge1$. The other root

$$
\beta=\det(\varphi)/\alpha
\tag{3.10}
$$

lies in $K$. If it had negative valuation, its eigenline would be distinct from $L$, would
have Hodge number zero, and would violate (2.8). Therefore

$$
v_3(\alpha)=1,
\qquad
v_3(\beta)=0.
\tag{3.11}
$$

The roots are distinct. Choose a $\beta$-eigenvector $e_0$ and an $\alpha$-eigenvector
$e_1\in L$. With $M$ as in (3.8), the normal matrix is diagonal with entries

$$
\beta,\qquad \alpha/3,
\tag{3.12}
$$

both units. Again $M$ is strongly divisible and its Hodge step is saturated of rank one.
$\square$

The proof constructs at least one lattice. It does not prove uniqueness, homothety, or
compatibility with a lattice obtained from an unrelated geometric presentation. Those are
different questions.

### 3.3 Galois realization and the first local tower

The coefficient-linear integral Fontaine--Laffaille realization of $M$ is a free rank-two
$\mathcal O$-lattice

$$
T_0\subset V
\tag{3.13}
$$

stable under $G_{\mathbf Q_3}$. The rational Fontaine--Laffaille comparison, in the same
covariant normalization used in $(\mathrm C_3)$, identifies the realization of $M[1/3]=D$
with the original $V|_{G_{\mathbf Q_3}}$. Thus (3.13) is a lattice in the specified rational
representation, not merely in another representation with the same Hodge numbers.

For every nonzero proper ideal $I\subset\mathcal O$, integral Fontaine--Laffaille theory
constructs a marked finite locally free commutative group

$$
\mathcal G^0_{I,3}/\mathbf Z_3,
\qquad
\mathcal G^0_{I,3}(\overline{\mathbf Q}_3)=T_0/IT_0,
\tag{3.14}
$$

with its $\mathcal O/I$-action. The admissible-annihilator construction makes these objects
functorial in $I$ and supplies the transition maps. Thus the first local lattice already has
an all-level tower.

If the direct geometric certificate (2.2) is available, Book 129 supplies another route to
the same conclusion. Put

$$
T_0=M_{\mathrm{geom}}\cap V
\tag{3.15}
$$

inside the fixed rational carrier. This intersection is saturated. Each quotient embeds in
finite abelian torsion, schematic closure is finite flat, and Raynaud rigidity over
$\mathbf Z_3$ identifies the levels into one exact tower. Formula (3.15) makes no integral
projector claim and is generally not the same lattice as (3.13).

### 3.4 Why the construction is not circular

There are three logically different operations.

1. Proposition 3.1 constructs a strongly divisible lattice from the rational filtered module.
2. Integral Fontaine--Laffaille theory constructs finite-flat groups from that lattice.
3. Later schematic subquotients transfer the property to a different global lattice.

At no point is full faithfulness used to manufacture an object before one exists. Nor is a
stable lattice obtained from compactness declared finite flat merely because the rational
representation is crystalline. The first finite-flat middle objects are the groups in (3.14)
or the geometric closures arising from (3.15).

## 4. From a local lattice to one global lattice

### 4.1 Compactness supplies global stability

The lattice $T_0$ need only be stable under $G_{\mathbf Q_3}$. The Schoof argument needs a
single lattice stable under all of $G_{\mathbf Q}$. Such a lattice exists for a topological
reason.

**Lemma 4.1 (global stable lattice).** The continuous representation $V$ contains a globally
$G_{\mathbf Q}$-stable free rank-two $\mathcal O$-lattice.

**Proof.** Start with any lattice $L_0\subset V$. Its stabilizer in
$\operatorname{GL}_K(V)$ is open. The image of the profinite group $G_{\mathbf Q}$ is compact,
so it has only finitely many translates of $L_0$. Their sum

$$
T=\sum_{g\in G_{\mathbf Q}}gL_0
\tag{4.1}
$$

is therefore a finite sum. It is a full finitely generated torsion-free $\mathcal O$-module,
hence free, and it is visibly stable. $\square$

Fix such a $T$. All full lattices in a finite-dimensional local vector space are
commensurable, so there is a $c\ge0$ with

$$
\varpi^cT_0\subset T\subset\varpi^{-c}T_0.
\tag{4.2}
$$

Commensurability does not identify reductions or extension classes. It does, however, allow
finite flatness to be transferred by supplied subquotients.

### 4.2 The saturated subquotient calculation

**Proposition 4.2 (commensurability transfer).** For every $n\ge1$, the
$G_{\mathbf Q_3}$-module $T/\varpi^nT$ has a coefficient-linear finite-flat model over
$\mathbf Z_3$.

**Proof.** Consider the finite module

$$
H=\varpi^{-c}T_0/\varpi^{n+c}T_0
\simeq T_0/\varpi^{n+2c}T_0.
\tag{4.3}
$$

It has the finite-flat model supplied by (3.14). Let $A$ and $B$ be the images in $H$ of
$T$ and $\varpi^nT$. They are stable $\mathcal O$-submodules and $B\subset A$. There is a
natural identification

$$
A/B\simeq
T/\bigl(\varpi^nT+T\cap\varpi^{n+c}T_0\bigr).
\tag{4.4}
$$

The first inclusion in (4.2) implies

$$
\varpi^{n+c}T_0\subset\varpi^nT,
\tag{4.5}
$$

so the denominator in (4.4) is exactly $\varpi^nT$. Hence

$$
A/B\simeq T/\varpi^nT.
\tag{4.6}
$$

Take the schematic closure of $A$ in the known finite-flat model of $H$, then the schematic
closure of $B$ inside it, and finally the represented quotient. Over the DVR $\mathbf Z_3$,
the closures are finite flat and the represented quotient is finite flat. The generic module
of the result is (4.6). Every coefficient scalar preserves $A$ and $B$, so it preserves their
closures and descends to the quotient. Multiplication by $\varpi^n$ is zero on the generic
quotient and therefore zero on its finite-flat model by generic-fiber faithfulness. The action
thus factors through the full ring $\mathcal O/\varpi^n$. $\square$

The ambient denominator $n+c$ in (4.3) is essential. Replacing it by $n$ would make (4.5)
false in general and would prove only a smaller quotient.

### 4.3 What saturation proves

The proof is a special case of the committed closure-tower theorem of Book 129. Its decisive
features are worth isolating.

- The desired quotient is a subquotient of a supplied finite-flat middle object, not an
  extension inferred from finite-flat endpoints.
- Schematic closure makes stable generic subgroups finite flat over a DVR.
- The represented quotient is taken only after the subgroup has been closed.
- The coefficient action is retained because the whole construction is invariant under its
  endomorphisms.

No residual irreducibility is needed. If a residual lattice were absolutely irreducible, it
would make all stable lattices homothetic, but homothety is not used here. Reducible residual
lattices can encode different extensions, and Proposition 4.2 correctly allows them to do so.

### 4.4 The lattice has now been chosen

From this point onward, $T$ always denotes the globally stable lattice of Lemma 4.1. We do not
replace it again to improve the local shape at two. Instead, the intrinsic rational SP line is
intersected with this same $T$ in Chapter 6. That intersection is automatically saturated and
therefore gives compatible exact filtrations at every coefficient level.

This is the useful reconciliation of the two local problems:

$$
\begin{array}{c}
\text{Fontaine--Laffaille lattice at }3
\\ \Downarrow\text{ commensurability and closure}
\\ \text{one global lattice }T
\\ \Downarrow\text{ intersection with the rational SP line}
\\ \text{integral signed-special filtration at }2.
\end{array}
\tag{4.7}
$$

No simultaneous fixed vertex in two unrelated local Bruhat--Tits trees is being assumed.

## 5. Every coefficient level and every transition

### 5.1 Ideals of the coefficient ring

Every nonzero proper ideal of the DVR $\mathcal O$ is

$$
I_n=(\varpi^n),\qquad n\ge1.
\tag{5.1}
$$

The use of $\varpi^n$, rather than only $3^n$, is necessary. If
$3=u\varpi^e$, the quotients by powers of three see only the levels divisible by $e$ and omit
the intervening coefficient quotients on which a coefficient-linear devissage operates.

Write

$$
T_n=T/\varpi^nT.
\tag{5.2}
$$

Proposition 4.2 gives at least one marked coefficient-linear finite-flat model of each $T_n$.
We next prove that the models can and must be organized into one system.

### 5.2 Rigidity over the unramified base

The base $\mathbf Z_3$ has absolute ramification index one, and

$$
1<3-1.
\tag{5.3}
$$

Raynaud full faithfulness therefore applies to finite-flat commutative $3$-primary groups over
$\mathbf Z_3$. A morphism of their generic fibers extends uniquely. In particular, two
marked finite-flat models of the same finite Galois module are uniquely isomorphic.

Choose one model from Proposition 4.2 and denote it

$$
\mathcal G_{n,3}/\mathbf Z_3,
\qquad
\mathcal G_{n,3}(\overline{\mathbf Q}_3)=T_n.
\tag{5.4}
$$

For $m\ge n$, the generic reduction $T_m\twoheadrightarrow T_n$ extends uniquely to

$$
q_{m,n,3}:\mathcal G_{m,3}\longrightarrow\mathcal G_{n,3}.
\tag{5.5}
$$

The composite $q_{n,r,3}q_{m,n,3}$ and $q_{m,r,3}$ have the same generic fiber, so
faithfulness makes them equal. Thus the transition maps are transitive. The scalar action of
$\mathcal O/\varpi^n$ also extends uniquely from the generic fiber, and uniqueness makes it
commute with every transition.

This is the rigidity step emphasized in Book 129: levelwise closure gives flatness, but it is
full faithfulness that identifies independently constructed lower levels with quotients of
higher levels.

### 5.3 Exact multiplication sequences

For $a,b\ge1$, the coefficient modules have an exact sequence

$$
0\longrightarrow T_a
\xrightarrow{\ \varpi^b\ }
T_{a+b}
\longrightarrow T_b
\longrightarrow0.
\tag{5.6}
$$

Close the first generic term inside $\mathcal G_{a+b,3}$ and call the closure $\mathcal H$.
It is finite flat. Form the represented finite-flat quotient

$$
0\longrightarrow\mathcal H
\longrightarrow\mathcal G_{a+b,3}
\longrightarrow\mathcal Q
\longrightarrow0.
\tag{5.7}
$$

The marked generic fibers of $\mathcal H$ and $\mathcal Q$ are $T_a$ and $T_b$. Raynaud full
faithfulness therefore gives unique marked isomorphisms

$$
\mathcal H\simeq\mathcal G_{a,3},
\qquad
\mathcal Q\simeq\mathcal G_{b,3}.
\tag{5.8}
$$

Transporting (5.7) through (5.8) proves the fppf-exact sequence

$$
0\longrightarrow\mathcal G_{a,3}
\xrightarrow{\ \varpi^b\ }
\mathcal G_{a+b,3}
\longrightarrow\mathcal G_{b,3}
\longrightarrow0.
\tag{5.9}
$$

This proves all-level exactness, not merely the existence of adjacent quotient maps. The
kernel in (5.9) is the represented schematic kernel. It is not identified with a naive tensor
product involving an ideal quotient.

### 5.4 Determinant and the coefficient pairing

The rational determinant isomorphism in (1.4) sends the free rank-one lattice
$\bigwedge_{\mathcal O}^2T$ to a fractional ideal times $\mathcal O(1)$. Rescale that rational
isomorphism by one element of $K^\times$. This gives an integral isomorphism

$$
\bigwedge_{\mathcal O}^2T\simeq\mathcal O(1).
\tag{5.10}
$$

Consequently

$$
\det T_n=\chi_3\pmod{\varpi^n}
\tag{5.11}
$$

at every level. The exterior product also gives a perfect alternating
$\mathcal O$-linear pairing

$$
T\times T\longrightarrow\mathcal O(1)
\tag{5.12}
$$

and its perfect reductions with values in $(\mathcal O/\varpi^n)(1)$.

This coefficient pairing is not automatically a Cartier self-duality over $\mathbf Z_3$.
Cartier duality uses the $\mathbf Z_3$-linear dual, whereas (5.12) uses the
$\mathcal O$-linear dual. The relation between them contains

$$
\mathcal O^\dagger
=\operatorname{Hom}_{\mathbf Z_3}(\mathcal O,\mathbf Z_3)
\simeq\mathfrak D_{\mathcal O/\mathbf Z_3}^{-1}.
\tag{5.13}
$$

Thus the invariant conclusions are the cyclotomic coefficient determinant, the perfect
coefficient pairing, and the compatible Cartier-dual tower
$\{\mathcal G_{n,3}^D\}_n$. A self-duality of $\mathcal G_{n,3}$ requires a chosen generator
of the inverse different and the corresponding coefficient-adjoint normalization. The Schoof
handoff below needs (5.11), not such a choice.

### 5.5 The complete local output at three

Under $(\mathrm C_3)$, the construction so far is unconditional relative to the rational
member. It has produced one globally stable lattice $T$ such that:

- every actual coefficient quotient $T_n$ is finite flat over $\mathbf Z_3$;
- the full $\mathcal O/\varpi^n$-action extends to its model;
- all reductions and exact multiplication sequences are morphisms of finite-flat groups;
- the inverse limit of generic points recovers $T$; and
- determinant and duality are compatible with the tower.

No global ramification assertion was used. Therefore this local output remains valid even if
the clean-support certificate $(\mathrm U)$ is not yet known.

## 6. The signed special place at two

### 6.1 From the Weil--Deligne pair to the local sequence

The rational SP pair (1.5)--(1.8) determines more than a conductor. In the associated
three-adic representation, inertia acts through the exponential of rank-one monodromy. Let

$$
\eta_2:G_{\mathbf Q_2}\longrightarrow\{1,-1\}
\tag{6.1}
$$

be the unramified character satisfying $\eta_2(F_2)=\varepsilon_2$. The ordered Frobenius
eigenvalues in (1.8), together with the cyclotomic determinant, give a
$G_{\mathbf Q_2}$-stable exact
sequence

$$
0\longrightarrow K(1)\otimes\eta_2
\longrightarrow V|_{G_{\mathbf Q_2}}
\longrightarrow K\otimes\eta_2
\longrightarrow0.
\tag{6.2}
$$

The sequence is nonsplit as a representation of inertia, since $N_2\ne0$. Its first term is
the unique inertia-fixed line

$$
V_2^+=\mathscr L_2\otimes_EK.
\tag{6.3}
$$

Wild inertia is trivial. Finite Weil inertia is also trivial; the nontrivial inertia in the
adic representation is the unipotent tame action coming from $N_2$. This is why the phrase
“trivial inertial type” does not mean “unramified representation” in the special case.

The Swan conductor is zero, and

$$
a_2(V)=\dim V-\dim V^{I_2}=2-1=1.
\tag{6.4}
$$

Thus the branch has conductor exponent one. The line, sign, return equation, and nonzero
monodromy are primary; (6.4) is their consequence.

### 6.2 The saturated integral line

Use the globally stable lattice chosen in Chapter 4 and define

$$
T_2^+=T\cap V_2^+,
\qquad
T_2^-=T/T_2^+.
\tag{6.5}
$$

**Lemma 6.1 (integral SP filtration).** The two modules in (6.5) are free of rank one over
$\mathcal O$, the first is $G_{\mathbf Q_2}$-stable and saturated in $T$, and

$$
0\longrightarrow T_2^+
\longrightarrow T|_{G_{\mathbf Q_2}}
\longrightarrow T_2^-
\longrightarrow0
\tag{6.6}
$$

is exact. After choosing generators,

$$
T_2^+\simeq\mathcal O(1)\otimes\eta_2,
\qquad
T_2^-\simeq\mathcal O\otimes\eta_2.
\tag{6.7}
$$

**Proof.** The intersection of a full lattice with a rational line is a rank-one lattice. It
is stable because both factors in the intersection are stable. If $\varpi x\in T_2^+$ for
$x\in T$, then $x\in V_2^+$ because $V_2^+$ is a $K$-space. Hence $x\in T_2^+$, proving
saturation. Therefore $T/T_2^+$ is torsion free of rank one and is free over the DVR
$\mathcal O$.

The rational characters in (6.2) take values in $\mathcal O^\times$ and preserve the two
rank-one fractional ideals. Choosing generators identifies the integral characters as in
(6.7). $\square$

The construction proves the integral line for the same lattice whose quotients are finite
flat at three. No new type-adapted lattice is selected, and no commensurability argument is
needed after the line has been intersected.

### 6.3 Exact reduction at every coefficient level

Because $T_2^-$ is free, tensoring (6.6) with $\mathcal O/\varpi^n$ remains exact:

$$
0\longrightarrow T_2^+/\varpi^nT_2^+
\longrightarrow T_n|_{G_{\mathbf Q_2}}
\longrightarrow T_2^-/\varpi^nT_2^-
\longrightarrow0.
\tag{6.8}
$$

These sequences commute with every transition $T_m\twoheadrightarrow T_n$. Both endpoint
characters are unramified on $I_2$: $\eta_2$ is unramified by definition, and the $3$-adic
cyclotomic character is unramified at the rational prime two. Consequently, for every
$\sigma\in I_2$,

$$
(\rho_n(\sigma)-1)T_n
\subset T_2^+/\varpi^nT_2^+,
\qquad
(\rho_n(\sigma)-1)(T_2^+/\varpi^nT_2^+)=0.
\tag{6.9}
$$

Therefore

$$
(\rho_n(\sigma)-1)^2=0.
\tag{6.10}
$$

This square-zero statement holds at every level. It is not a statement that the inertia image
has order at most three at every level.

### 6.4 Integral monodromy thickness

Choose generators of the two free terms in (6.6) and lift the quotient generator to $T$.
Let

$$
t_3:I_2\twoheadrightarrow\mathbf Z_3
\tag{6.11}
$$

be a normalized $3$-primary tame character. In the adapted basis, inertia has the form

$$
\rho(\sigma)=
\begin{pmatrix}
1&\alpha t_3(\sigma)\\
0&1
\end{pmatrix},
\qquad
\alpha\in\mathcal O\setminus\{0\}.
\tag{6.12}
$$

The coefficient belongs to $\mathcal O$ because inertia preserves $T$, and it is nonzero
because the rational monodromy in (1.5) is nonzero. Changing the two generators multiplies
$\alpha$ by a unit. Hence

$$
s_2(T)=v_\varpi(\alpha)
\tag{6.13}
$$

is an invariant of this integral filtration.

Put $e=v_\varpi(3)$. On $T_n$, the inertia image is cyclic of order

$$
3^{\max\{0,\lceil(n-s_2(T))/e\rceil\}}.
\tag{6.14}
$$

Indeed, the kernel of the additive map
$\mathbf Z_3\to\mathcal O/\varpi^n$, $z\mapsto\alpha z$, consists of the $z$ with
$s_2(T)+ev_3(z)\ge n$. Formula (6.14) follows.

Thus the image is always a finite cyclic $3$-group and hence has odd order. On any subquotient
killed by three, (6.10) gives

$$
\rho(\sigma)^3=1,
\tag{6.15}
$$

so its inertia image is trivial or cyclic of order three. An arbitrary global lattice may have
$s_2(T)>0$, in which case the first residual action is trivial. Rational nonzero monodromy
implies eventual nontriviality, not primitive residual monodromy on every lattice. The later
Schoof category needs the odd-tame conclusion, not the stronger primitive assertion.

### 6.5 The exact dyadic output

The conclusions at two are now all derived from the rational SP pair selected in Book 186 from
Book 185's away-from-two collection, together with the chosen global lattice:

- the rational monodromy is nonzero of rank one;
- its line is intrinsic and carries the cyclotomic side of the filtration;
- the unramified sign $\eta_2$ is retained on both endpoints;
- wild inertia is trivial;
- the rational conductor exponent is one;
- every finite coefficient quotient has cyclic $3$-power tame inertia; and
- the filtration and square-zero relation are compatible through all levels.

There is no zero-monodromy branch, primitive finite cubic characteristic-zero type, or
conductor-two assertion in this list.

## 7. Clean support away from two and three

### 7.1 The finite exceptional set left by assembly

Let $S_0$ be the finite exceptional set in the restricted Book 185 assembly theorem. Outside
$S_0$ and away from the varying coefficient characteristic, the away-from-two members are
unramified and have the common algebraic polynomial

$$
P_q(X)=X^2-a_qX+q.
\tag{7.1}
$$

The roots of these polynomials are pure of weight one. At a prime in $S_0$, Book 185 proves a
local statement only if every elementary packet term lies in the established local comparison
range. It then constructs an algebraic local complement $D_q$. If that complement is
unramified, the prime can be removed from the actual support ledger.

Following Book 185, define the unresolved selected-member auxiliary set

$$
S_{\mathrm{aux}}=S_{\mathrm{aux}}(\nu)
=\{q\in S_0\setminus\{2,3\}:r_\nu\text{ has not yet been proved unramified at }q\}.
\tag{7.2}
$$

Before Book 185, Proposition 8.3, the clean-support certificate $(\mathrm U)$ would be the
finite theorem that $V|_{I_q}$ is trivial for every $q\in S_{\mathrm{aux}}$.  That proposition
now proves the theorem and makes this support set empty.  It also constructs the algebraic
unramified Galois pair $D_q$ and its exceptional-prime Frobenius polynomial at every such
prime.  A separate automorphic-type problem may remain: the Galois pair by itself does not
construct a principal/dihedral type projector, exchange line, or return-map calculation.

### 7.2 What can prove the finite checks

There are two safe routes.

First, one may prove actual local cancellation. If the positive and negative displaying terms
at $q$ are unramified and

$$
R_q^+\simeq V|_{G_{\mathbf Q_q}}\oplus R_q^-,
\tag{7.3}
$$

then inertia is the identity on the positive term and therefore on its direct summand $V$.
This uses an actual representation, not subtraction of conductor exponents.

Second, one may use Book 185's algebraic local complement. If

$$
\operatorname{WD}_q(V)^{\mathrm{F\text{-}ss}}
\simeq D_q\otimes_EK
\tag{7.4}
$$

and $D_q$ has trivial finite inertia and $N_q=0$, then $V$ is unramified at $q$. This route
requires the local comparison at that prime. A good Frobenius polynomial on a density-one set
does not substitute for (7.4).

Book 185 proves the second route, as well as the conductor check.  On each actual Jacobian
carrier, Book 61's equivariant theorem makes both the Artin conductor and the
inertia-invariant Frobenius polynomial of the raw Hecke multiplicity factor independent of the
coefficient place.  At $q\ne\ell$ the distinguished raw factor is the irreducible
representation $\rho|_{G_{F_H}}$ and is unramified; Book 128, Lemma 3.2 passes the resulting
unramified pair to the elementary semisimplification.  At $q=\ell$ the split unitary good
cover and pull--trace give the same conclusion.  Thus every untwisted elementary packet factor
has a common unramified algebraic Galois pair away from two.

Algebraic finite twisting and Weil induction form the local positive and negative Mackey
pairs, and actual global cancellation plus Krull--Schmidt gives a common rank-two complement.
The distinguished member makes it unramified at $q\ne\ell$; complete splitting gives the same
result at $q=\ell$.  Book 185, Proposition 8.3 therefore proves
$(\mathrm{AUX}_{\mathrm{all}})$ and $(\mathrm{AUX}_\nu)$.  Proposition 8.2 concludes
$(\mathrm{Cond}_2)$ and

$$
(\mathrm{Cond}_2)\Longrightarrow(\mathrm U).
\tag{7.4a}
$$

Book 184's conductor identity gives an independent check: twisting an unramified rank-two
factor by a finite Brauer character contributes twice the conductor of that character, and
the local induction discriminants are coefficient-independent.  What remains unproved is not
an AUX certificate but Book 182's stronger automorphic-type theorem.  At a nonspherical place
that theorem requires the actual principal or dihedral descent comparison, including the
prior tameness ledger, type or exchange lines, zero monodromy, and normalized return maps.
This does not affect $(\mathrm U)$.  In particular the positive and negative Brauer terms may
both be ramified while their actual rank-two complement is unramified.

### 7.3 Consequences of clean support

Assume $(\mathrm U)$. For $q\ne2,3$, inertia acts trivially on $V$, hence on the stable
lattice $T$ and every quotient $T_n$:

$$
T_n\text{ is unramified at every }q\ne2,3.
\tag{7.5}
$$

Because $T_n$ has $3$-power order and $q\ne3$, its unique finite-flat model over
$\mathbf Z_q$ is finite etale. Denote it by

$$
\mathcal G_{n,q}/\mathbf Z_q.
\tag{7.6}
$$

The generic coefficient action and every transition map extend uniquely to (7.6). Therefore
the only non-etale odd-prime local model used below is the selected finite-flat model at three.

If $(\mathrm U)$ is absent, Chapters 3--6 remain valid, but (7.6) is missing at least at one
odd prime and no object over $\mathbf Z[1/2]$ has been constructed. This is a genuine second
blocker, independent of the coefficient-prime certificate.

### 7.4 The good polynomial used for the final contradiction

The eventual trace contradiction needs one rational prime at which the family has a pure
weight-one common polynomial and which is unramified for $V$. The original good set of Book
185 is cofinite, so such a prime exists even before a particular auxiliary prime has been
removed. If one wants to use the conventional prime five, the clean local ledger must also
certify the algebraic Frobenius polynomial at five when five originally lay in $S$.

This observation keeps two statements separate:

$$
\begin{array}{ll}
\text{global Schoof model:}&\text{unramifiedness at every }q\ne2,3,\\
\text{purity contradiction:}&\text{one certified pure good prime.}
\end{array}
\tag{7.7}
$$

The first is stronger and is exactly what gluing requires.

Neither line in (7.7) asks for integral models at a second coefficient place. The first ranges
over base primes for the quotients of the one $\nu$-adic lattice; the second is only an optional
characteristic-zero fallback once Book 188 has already proved reducibility.

## 8. Gluing over the integers with two inverted

### 8.1 The local ledger

Assume both $(\mathrm C_3)$ and $(\mathrm U)$. For every $n\ge1$, the local data are now:

| rational prime | integral or generic record |
|---|---|
| $3$ | the marked coefficient-linear finite-flat model $\mathcal G_{n,3}$ |
| odd $q\ne3$ | the unique finite-etale model $\mathcal G_{n,q}$ |
| $2$ | no integral fiber; the generic module has the SP filtration (6.8) and odd-tame inertia |

The prime two must be inverted for the full tower. A finite-flat group of $3$-power order over
$\mathbf Z_2$ is finite etale, so its generic module is unramified. The sufficiently deep,
nontrivial SP quotients cannot extend over $\mathbf Z_2$.

### 8.2 The Dedekind intersection

Let $B_n$ be the coordinate Hopf algebra over $\mathbf Q$ of the finite etale generic group
attached to $T_n$. For every odd prime $q$, let

$$
A_{n,q}\subset B_n\otimes_{\mathbf Q}\mathbf Q_q
\tag{8.1}
$$

be the coordinate Hopf order of the local model in Section 8.1.

Only finitely many of these orders differ from one spread-out order. Indeed, choose a
$\mathbf Q$-basis of $B_n$ containing $1$ and clear the denominators in the multiplication,
coproduct, counit, and antipode. After inverting one odd integer, the resulting lattice is a
Hopf order. After inverting its trace discriminant, it is finite etale. At every remaining
odd prime, uniqueness of the finite-etale model identifies it with $A_{n,q}$.

Inside $B_n$, define

$$
A_n=
\{x\in B_n:x\in A_{n,q}\text{ for every odd prime }q\}.
\tag{8.2}
$$

**Lemma 8.1 (Hopf-order intersection).** The module $A_n$ is finite projective over
$\mathbf Z[1/2]$, its localization at every odd $q$ is $A_{n,q}$, and it is preserved by all
Hopf operations.

**Proof.** Relative to one spread-out lattice, only finitely many local conditions in (8.2)
are exceptional. Clearing their denominators places $A_n$ between a nonzero ideal multiple of
that lattice and its inverse ideal multiple. Thus $A_n$ is finite and torsion free over the
Dedekind domain $\mathbf Z[1/2]$, hence projective. Localizing at $q$ makes every condition at
the other primes a unit condition and recovers $A_{n,q}$.

The same lattice-intersection statement applies in $B_n\otimes B_n$: the intersection of the
local tensor lattices is $A_n\otimes A_n$. Since local comultiplication carries every
$A_{n,q}$ into $A_{n,q}\otimes A_{n,q}$, global comultiplication carries $A_n$ into
$A_n\otimes A_n$. Multiplication, counit, and antipode are treated identically. All Hopf
identities already hold over $\mathbf Q$ and therefore on the torsion-free lattice $A_n$.
$\square$

Set

$$
\mathcal G_n=\operatorname{Spec}A_n.
\tag{8.3}
$$

Then $\mathcal G_n$ is a finite locally free commutative group over $\mathbf Z[1/2]$, its
generic module is $T_n$, its localization at three is $\mathcal G_{n,3}$, and at every other
odd prime it is the finite-etale model.

### 8.3 Coefficients and transition maps glue

Every scalar in $\mathcal O/\varpi^n$ acts on the generic group. It preserves the selected
order at three by Chapter 5 and every finite-etale order by uniqueness. Hence it preserves
their intersection and acts on $\mathcal G_n$.

For $m\ge n$, the generic reduction $T_m\twoheadrightarrow T_n$ extends at three by (5.5) and
at every other odd prime by finite-etale uniqueness. The corresponding local Hopf maps preserve
all local orders and hence their intersections. They give a global faithfully flat map

$$
q_{m,n}:\mathcal G_m\twoheadrightarrow\mathcal G_n.
\tag{8.4}
$$

Faithful flatness can be checked after localization at every maximal ideal. Transitivity holds
because the composites agree on the generic fiber. The same localization argument globalizes
(5.9):

$$
0\longrightarrow\mathcal G_a
\xrightarrow{\ \varpi^b\ }
\mathcal G_{a+b}
\longrightarrow\mathcal G_b
\longrightarrow0
\tag{8.5}
$$

is fppf exact for every $a,b\ge1$.

Cartier duality commutes with localization, so the dual local towers glue to
$\{\mathcal G_n^D\}_n$. The determinant and coefficient pairings of Section 5.4 glue on
generic fibers. As before, a coefficient-linear pairing should not be called a canonical
Cartier self-duality without the inverse-different normalization.

### 8.4 The global tower is derived, not assumed

The global construction used precisely two arithmetic inputs:

1. the actual finite-flat model over $\mathbf Z_3$, constructed from $(\mathrm C_3)$; and
2. actual unramifiedness at every other odd prime, supplied by $(\mathrm U)$.

Everything else in Chapter 8 is Dedekind gluing. In particular, no theorem from the later
Schoof classification is used to manufacture the objects that classification will consume.

## 9. The exact handoff to the Schoof endgame

### 9.1 Membership in the Schoof category

For every $n$, the group $\mathcal G_n/\mathbf Z[1/2]$ has $3$-power order. Its generic
module is unramified outside $\{2,3\}$. At two, wild inertia is trivial and (6.14) shows that
the finite inertia image is a cyclic $3$-group. Hence it has odd-tame inertia.

Therefore every $\mathcal G_n$ is an object of the Schoof category. Moreover:

1. $T_n$ is free of rank two over $\mathcal O/\varpi^n$;
2. the coefficient action extends to $\mathcal G_n$;
3. $\det T_n=\chi_3\bmod\varpi^n$;
4. the maps $q_{m,n}$ are compatible coefficient reductions; and
5. every exponent-three subquotient satisfies the square-zero relation (6.10), and hence the
   cube-one relation (6.15).

The category requires only odd-tame inertia, not nontrivial residual inertia and not a uniform
order-three bound on every higher quotient. Higher SP quotients may have inertia of order
$3^r$ with $r>1$.

### 9.2 What Book 188 may use

The branch-independent input to the three-adic endgame is now exactly present. Book 161,
Theorem 10.1 supplies the finite-level Schoof identity after the membership check above. Book
188 imports Book 161's category, simple objects, Ext calculation, and canonical filtration, then
applies its own $\mathcal O$-adic coefficient-tower and saturation argument to
$(T,\{\mathcal G_n\})$. Its conditional reducibility theorem then produces

$$
0\longrightarrow\mathcal O(1)
\longrightarrow T
\longrightarrow\mathcal O
\longrightarrow0
\tag{9.1}
$$

and

$$
V^{\mathrm{ss}}\simeq K(1)\oplus K.
\tag{9.2}
$$

The controlled rational input already says that $V$ is absolutely irreducible. Therefore
(9.1), or even the $K$-line obtained from it, is the preferred final contradiction. It uses
neither a residual irreducibility assertion nor a pure good-prime record.

The global cyclotomic line in (9.1) is an output of the classification. It must not be
identified in advance with the local $D_2$-stable line $T_2^+$. After (9.1) exists, uniqueness
of the inertia-fixed line for nonzero SP monodromy identifies the two rational lines. This can
force the dyadic sign to be split, but the usual good-Frobenius trace contradiction works
without using that shortcut.

Independently, at any certified pure good prime $q\ne2,3$, (9.2) gives

$$
\operatorname{tr}V(\operatorname{Frob}_q)=1+q.
\tag{9.3}
$$

Weight-one purity gives the fallback contradiction

$$
|a_q|\le2\sqrt q,
\tag{9.4}
$$

whereas $1+q>2\sqrt q$ for every $q>1$. Thus one certified good prime is enough. If the prime
five has its clean local polynomial, it gives the familiar inequality $6>2\sqrt5$.

### 9.3 What is not exported

This book does not prove:

- the simple-object classification in the Schoof category;
- the global extension calculation or filtration rearrangement;
- a global line before that classification is applied;
- primitive residual SP monodromy for an arbitrary global lattice;
- an integral splitting of (9.1); or
- either of the rational source certificates $(\mathrm C_3)$ and $(\mathrm U)$ from Book
  185 alone.

These exclusions keep the dependency direction

$$
\text{comparison certificates}
\Longrightarrow\text{integral tower}
\Longrightarrow\text{Schoof classification}
\tag{9.5}
$$

strictly forward.

## 10. The conditional fixed-three theorem

### 10.1 Local theorem

**Theorem 10.1 (fixed-three local integral package).** Assume the away-from-two SP input
contract of Book 186, Theorem 7.1, for the selected place $\nu\mid3$, and the coefficient-prime
certificate $(\mathrm C_3)$. Then there is a globally
$G_{\mathbf Q}$-stable free rank-two lattice $T\subset V$ with the following properties.

1. For every nonzero proper ideal $I=(\varpi^n)\subset\mathcal O$, the module $T/IT$ has a
   marked coefficient-linear finite-flat model $\mathcal G_{I,3}/\mathbf Z_3$.
2. For nested ideals, coefficient reduction extends to unique faithfully flat transition maps.
   All compositions are transitive, and the exact multiplication sequences (5.9) hold.
3. The determinant is cyclotomic at every level, and the coefficient exterior pairing is
   perfect. Cartier duality gives a compatible dual tower, with the inverse-different warning
   of (5.13).
4. At two, $T$ has the saturated exact filtration (6.6), with signed unramified endpoints.
   Every finite quotient has square-zero unipotent tame inertia and a finite cyclic
   $3$-power inertia image; wild inertia is trivial.
5. Rationally, the monodromy at two is nonzero of rank one, its line and sign are those
   transported in Book 186, and its Artin conductor exponent is one.

**Proof.** Proposition 3.1 constructs one strongly divisible lattice from $(\mathrm C_3)$,
and integral Fontaine--Laffaille theory gives its local tower. Lemma 4.1 chooses a global
stable lattice. Proposition 4.2 transfers finite-flatness by schematic subquotients, and
Sections 5.2--5.3 use Raynaud rigidity to construct all transitions and exact sequences.
Section 5.4 proves determinant and duality. Lemma 6.1 and Sections 6.3--6.4 construct the
integral SP filtration and calculate every finite inertia image. $\square$

For the controlled top, Proposition 2.2 supplies $(\mathrm{AVCar}_{3,\ell}^+)$ from the
constructed unitary cover.  The separate hypothesis $(\mathrm C_3)$ in Theorem 10.1 is
therefore automatic: Theorem 2.3 supplies $(\mathrm{IC}_3)$ and Proposition 2.1 supplies
$(\mathrm C_3)$. The FLT-scoped geometric version begins with the controlled top, not with an
admitted integral companion.

The theorem is genuinely local at the coefficient prime even though its lattice is globally
stable. It makes no claim of a group scheme over $\mathbf Z[1/2]$ without clean support.

### 10.2 Global theorem

**Theorem 10.2 (fixed-three Schoof-ready package).** Add the clean-support certificate
$(\mathrm U)$ to the hypotheses of Theorem 10.1. Then, for every nonzero proper ideal
$I=(\varpi^n)$, there is a finite locally free commutative group

$$
\mathcal G_I/\mathbf Z[1/2]
\tag{10.1}
$$

with $\mathcal O/I$-action and marked generic module $T/IT$. These groups form one compatible
coefficient-linear tower with fppf-exact multiplication sequences. Every $\mathcal G_I$ lies
in the Schoof category, its determinant is cyclotomic, and its exponent-three subquotients have
inertia image trivial or cyclic of order three.

Consequently the tower supplies the integral and local hypotheses actually used in the proof
of the conditional Frey--SP three-adic reducibility theorem in Book 188. Since Book 186's
selected member is absolutely irreducible, that reducibility theorem already ends the
preferred FLT chain. A prime in the cofinite certified good set transported by Book 186
supplies the separate pure Frobenius polynomial only for the optional trace fallback.

**Proof.** Under $(\mathrm U)$, Section 7.3 supplies the unique finite-etale model at every
odd prime other than three. Lemma 8.1 intersects these orders with the model constructed at
three and gives $\mathcal G_I$. Section 8.3 glues the coefficient actions, transitions, and
exact sequences. Section 9.1 verifies the Schoof-category hypotheses from the dyadic
calculation. $\square$

### 10.3 What the theorem says about lattices

Theorems 10.1--10.2 are existence theorems. They do not say that $V$ canonically selects $T$.
The construction makes two choices:

1. one strongly divisible lattice, or one good geometric carrier; and
2. one globally stable lattice.

Book 129's commensurability theorem proves that the finite-flat existence property survives
the second choice. Different global lattices can still have different residual extension
classes and different monodromy thickness $s_2(T)$. The downstream category was designed to
accept exactly this amount of nonuniqueness.

## 11. Dependency and hostile audits

### 11.1 Direct prerequisites

The proof uses the following sources directly.

| source | exact input | use here | strengthening not made |
|---|---|---|---|
| Book 3 | tame characters, finite-image ramification bookkeeping, and the trace-dual description of the inverse different | (5.13) and the tame quotient calculations in Sections 6.3--6.4 | its finite-image conductor theory is not used to manufacture the characteristic-zero SP conductor transported in Book 186 |
| Book 6 | the exponent-two Grunwald alternative with prescribed local quadratic classes | the imaginary quadratic field used in (2.5b) | the carrier CM field is independent of the auxiliary dihedral CM field in Book 182 |
| Book 10 | effective fpqc descent of schemes, group laws, properness, smoothness, and geometric connectedness | descent of the local Weil restriction in Proposition 2.2 | good reduction is used only after $E_i/F_i$ is finite etale locally |
| Book 26 | representability and arbitrary base change for Weil restriction along a finite locally free map | $A_i=\operatorname{Res}_{E_i/F_i}J_i$ and the induced Tate-module formula | no ramified integral restriction is asserted |
| Book 42 | marked finite-flat models, schematic closure, represented quotients, coefficient actions, and finite-etale models | Proposition 4.2 and the local-to-global model calculus | no extension is called finite flat from its endpoints alone |
| Book 54 | integral Fontaine--Laffaille realization, full faithfulness over $\mathbf Z_3$, admissible coefficient quotients, exact compatible systems, and coefficient-dual normalization | Chapters 3 and 5 | rational Hodge labels do not select a lattice, and coefficient duality is not silently identified with Cartier self-duality |
| Book 82 | patching a finite collection of prescribed local quaternionic lattices into one global lattice | the unitary lattice in (2.5b)--(2.5d) which is self-dual at every place above $3\ell$ | local self-duality is proved from the split Hermitian plane before patching and is not inferred from rational splitting alone |
| Book 118 | the direct common-norm parity obstruction, the PEL-exact unitary common-multiplier central modification, its reflex field, and its finite unitary-to-basic full-component cover over a component field unramified at the retained primes | Lemma 2.2A and construction (2.5b)--(2.5d) | the cover uses a distinct CM-unitary group and does not rehabilitate the obstructed direct trace group |
| Book 119 | representability and the universal abelian scheme for the exact unitary PEL datum | the fine carrier curve in Proposition 2.2 | equality of adjoint groups alone is not a moduli interpretation |
| Book 121 | the split odd hyperspecial local model, anisotropic-Hermitian boundary exclusion, and smooth projective unitary PEL model | good reduction of $Y_i$ and its Jacobian at $3\ell$ | no dyadic parahoric conclusion is imported |
| Book 125 | rational pullback--trace on full component unions and the complete finite Hecke block in curve cohomology | transporting the basic raw packet plane to the good PEL cover | the cover degree is not assumed to be a coefficient unit |
| Book 127 | the parity-complete basic one-split curve carrier and its covariantly normalized raw multiplicity space | Proposition 2.2 | no basic-to-PEL comparison or good abelian carrier is inferred |
| Book 128 | the exact good, tame-principal, and tame-dihedral local comparison criteria | the finite auxiliary blocker in Chapter 7 | an automorphic type name is not substituted for the geometric type and return-map package |
| Book 129 | saturated geometric intersections, exact closure towers, commensurability transfer, coefficient change, and the fixed-three handoff | the geometric route and the proof architecture of Chapters 3--5 | no canonical geometric carrier or integral projector is claimed |
| Book 161 | the Schoof category, its classification and filtration theorem, and the finite-level coefficient trace identity | Section 9 handoff and Theorem 10.2's Schoof-ready output | it does not select the coefficient place or construct the named tower |
| Book 182 | the exact evaluated packets at $2,3,\ell$, the normal-top splitting mechanism, minimality away from $\{2,\ell\}$, and parity-complete basic attachment of every elementary candidate | the split-three and basic-carrier inputs to Section 2.5 | it does not construct the separate auxiliary-prime descent complexes audited below |
| Book 185 | the $(\mathrm{AI}_2)$-independent away-from-two members, actual characteristic-zero Brauer cancellation, all-place algebraic Galois local complements, the AUX certificates, clean support, and the common pure polynomial ledger | the rational input and finite clean-support theorem in Chapter 7 | no coefficient-two member, coefficient-prime comparison, automorphic-type identification, or integral lattice is imported |
| Book 186 | selection of the actual member at $\nu\mid3$, its determinant, pure good polynomials, clean support from Book 185, and its full signed SP pair at two | the rational starting object, clean support, and dyadic local data | its theorem explicitly uses no $(\mathrm{AI}_2)$ and supplies no coefficient-prime comparison, lattice, or tower |

Accordingly the proposed direct dependency row is

$$
\boxed{187\mid 3,\ 6,\ 10,\ 26,\ 42,\ 54,\ 82,\ 118,\ 119,\ 121,\ 125,\ 127,\ 128,\ 129,\ 161,\ 182,\ 185,\ 186.}
\tag{11.1}
$$

Book 82 is now a direct lattice-patching source for the distinct unitary presentation. Book 115
remains a comparative carrier-audit source through Book 118: it shows why changing an order or
real multiplier cannot repair the direct Hodge-lift obstruction. Books 119 and 121 are direct
proof inputs for the unitary presentation. Books 142 and 180 are transitive
recognition sources through the packet construction.  Book 168 is a transitive source for the
packet comparison records used inside Books 183--185. Books 164--165 establish the Frey
provenance and deformation-theoretic meaning of the signed SP line. Books 183--184 construct
the SP packet array and prove rational effectivity. None is a separate direct proof input after
the restricted Book 185 result and Book 186 handoff are assumed. Book 161 is the actual category
and classification source named in the Schoof-ready handoff; Book 188 is the downstream
application layer.

### 11.2 Exact blocker audit

Books 185--186 by themselves do not prove $(\mathrm C_3)$. Book 182 includes $3$ among the sensitive places, constructs its split evaluated
$\mathbf Q_3$ packet, and supplies parity-complete basic carriers. Lemma 2.2A rules out the
formerly proposed direct common-norm trace group. The distinct unitary construction
(2.5b)--(2.5d) proves $(\mathrm{Car}_3^+)$.  Its CM center repairs the real parity and Book
118 calculates the exact PEL centralizer.  Corollary 10.3A uses the connected fiber product over
the common adjoint group, first saturates the trivial-central-character basic level by the
central signs, and removes its finite arithmetic cosets at primes away from $3\ell$; it
therefore gives an actual fine unitary PEL level cover of every routed basic component over a
component field unramified above $3\ell$.  Book 121 supplies the smooth projective model and
good relative Picard scheme, and Proposition 2.2 proves

$$
(\mathrm{Car}_3^+)\Longrightarrow(\mathrm{AVCar}_{3,\ell}^+).
$$

Theorem 2.3 proves $(\mathrm{IC}_3)$, and Proposition 2.1 proves $(\mathrm C_3)$. Thus there is
no remaining positive-carrier assertion in the fixed-three route: the group, PEL datum,
field of definition, finite cover, proper good model, and rational Tate injection are all
constructed.

This closure remains separate from integral Brauer effectivity. The construction uses only
the positive terms of one actual characteristic-zero display. No rational packet idempotent is
extended integrally, no cancellation is asserted in a Grothendieck group of finite-flat group
schemes, and no ambient Tate-module semisimplicity is needed: saturated subquotients transfer
finite-flat existence to the semisimplification. The direct common-norm obstruction also
remains valid; it is bypassed by a CM-unitary common-multiplier group, not repaired by changing
the direct order or pure quaternion.

There is no remaining local-support obstruction.  Book 185, Proposition 8.3 proves
$(\mathrm{AUX}_{\mathrm{all}})$ and $(\mathrm{AUX}_\nu)$ by equivariant Galois comparison
and actual Brauer effectivity.  Proposition 8.2 records

$$
(\mathrm{AUX}_\nu)\Longrightarrow(\mathrm U),
\qquad
(\mathrm{AUX}_{\mathrm{all}})\Longrightarrow(\mathrm{Cond}_2)
\Longrightarrow(\mathrm U).                                \tag{11.2}
$$

The implications in (11.2) concern full Frobenius-semisimple Galois pairs and are stronger
than support.  They do not supply the type/exchange/return-map data of the stronger automorphic
statement at every auxiliary prime, and ramified cyclic principal rows are not even known tame
without the additional field ledger of Book 182.  Almost-all Frobenius polynomials alone
contain none of those exceptional local matrices; Book 185 obtains them instead from
equivariant local geometry.  Book 186's unramified-outside-$\{2,3\}$ conclusion is therefore
an output of the Book 185 family package.  The admitted arithmetic-core fields
$(\mathrm{IC}_3)$ and $(\mathrm{Cond}_2)$ are both discharged by the positive carrier and
equivariant-conductor arguments, respectively.

### 11.3 Rational-to-integral attacks

**Attack: crystallinity makes an arbitrary global lattice finite flat.** It does not. We first
construct $T_0$ by Proposition 3.1 and Fontaine--Laffaille realization, then exhibit every
quotient of $T$ as a subquotient of a supplied finite-flat middle object.

**Attack: rational cancellation at three gives integral cancellation.** It does not.  In
Theorem 2.3 it gives only a rational injection of $V$ into the positive term.  Saturated
intersection and schematic closure construct the desired finite-flat subobjects; no lattice
decomposition of (2.3) is asserted, and the negative term needs no good carrier.

**Attack: the packet idempotent must be integral at three.** It need not be.  A nonzero
oldvector embeds the rational multiplicity plane in the good Jacobian Tate module.  The
denominator of a rational block idempotent is never inverted on a finite-flat group.

**Attack: levelwise finite flatness automatically gives transition maps.** It does not over a
general DVR. Over $\mathbf Z_3$, Raynaud full faithfulness identifies the closure quotient
with the chosen lower marked model and forces transitivity.

**Attack: quotients by $3^n$ are all coefficient quotients.** They are not if
$\mathcal O/\mathbf Z_3$ is ramified. Every level is indexed by $\varpi^n$.

**Attack: cyclotomic determinant is the same as canonical Cartier self-duality.** It is not.
The coefficient exterior pairing is perfect, while the $\mathbf Z_3$-linear Cartier dual
contains the inverse different.

### 11.4 Dyadic attacks

**Attack: Books 183--185 have monodromy zero or a tame-quadratic type.** They do not. Their
current SP object has $N_2\ne0$ of rank one, the line (1.7), the sign (1.8), and conductor
exponent one.

**Attack: trivial finite Weil inertia makes the adic representation unramified.** It does not
when $N_2\ne0$. Tame inertia acts unipotently through the monodromy exponential.

**Attack: nonzero rational monodromy is nonzero modulo every lattice.** It need not be.
The thickness (6.13) measures the loss. The universal statements are the saturated filtration,
square-zero action, odd-tame image, and eventual nontriviality.

**Attack: every higher quotient has inertia of order at most three.** Formula (6.14) shows
that the order can grow. The order-three statement applies only to exponent-three subquotients.

**Attack: conductor one defines the local branch.** It does not. The defining record is the
nonzero monodromy, intrinsic line, return equation, and sign. Conductor is derived afterward.

### 11.5 Global and dependency attacks

**Attack: the fixed-three theorem needs Book 185's all-place system.** It does not. The selected
place $\nu\mid3$ belongs to the away-from-two collection constructed without
$(\mathrm{AI}_2)$, and Book 186 transports every rational datum used here. A hypothetical
member at a coefficient place above two never enters the lattice, local, or gluing arguments.

**Attack: the blueprint's `integralModelsAway` record is a hidden input.** It is not. That
record proves one integral statement for every odd coefficient place. This book constructs
the only instance consumed downstream, at the chosen $\nu\mid3$. Its use of every odd
rational prime in Chapter 8 is clean-support gluing for this one tower, not a return to the
family-wide record.

**Attack: weak compatibility removes all auxiliary ramification.** It does not. The finite
checks in $(\mathrm U)$ require actual local comparison or actual direct-summand
unramifiedness.  Frobenius density in one completion does not identify the values of two
continuous trace functions at an inertia element by taking limits in different completions.

**Attack: every auxiliary packet factor may be taken spherical.** It may not.  Ramification
of the controlled top and nonsplit cyclic descent can produce principal or tame-dihedral
factors.  Only the fixed prime $3$, named split before the construction, has the uniform
spherical argument used in the positive-carrier certificate.

**Attack: a spherical basic quaternionic packet automatically has the good PEL carrier used
in Proposition 2.2.** It does not follow formally from sphericality. Lemma 2.2A proves that
the natural direct common-norm realization has no Hodge lift in mixed signature, so varying its
multiplier or order cannot help. The proposed proof instead chooses the CM field (2.5b),
calculates the unitary PEL centralizer and Hodge lift, realizes the connected adjoint
fiber-product component after the harmless central saturation as an actual prime-to-$3\ell$
fine unitary level cover, controls its
component field, verifies the split hyperspecial local model, and excludes the integral
boundary by anisotropy of the reduced-norm Hermitian form. Those are the substantive inputs of
$(\mathrm{Car}_3^+)$; none is an inference from the local word ``spherical.''

**Attack: a finite-flat model at three alone glues over $\mathbf Z[1/2]$.** It does not. Every
other odd prime needs its finite-etale model, which is available precisely under
$(\mathrm U)$.

**Attack: the dyadic line should be globalized before Schoof.** It is only $D_2$-stable.
Globalizing it would assume the later classification's conclusion.

**Attack: citing Book 161 constructs the tower.** It does not. This book constructs its named
tower from Books 42, 54, and 129 and verifies membership in Book 161's category. Book 161 then
supplies the actual classification and finite-level identity; Book 188 consumes both the tower
and that imported theorem package.

## 12. Conclusion and readiness

### 12.1 The mathematical conclusion

The fixed-three integral problem has a short rational input and a genuinely integral middle.
Book 186 selects from Book 185's away-from-two collection the correct signed-special member at
two: its monodromy is nonzero of rank one, its kernel and image are the same intrinsic line,
its Frobenius sign is retained, and its conductor exponent is one. Nothing at two needs to be
replaced by a tame-quadratic or monodromy-zero branch, and no coefficient-two member is used.

At three, the source-facing flat companion still implies the needed crystalline certificate.
The full arithmetic core is unnecessary: Section 2.5 constructs the positive
good-abelian-carrier theorem $(\mathrm{AVCar}_{3,\ell}^+)$. Its source is the unitary
common-multiplier PEL cover $(\mathrm{Car}_3^+)$ of the compact division-quaternion basic
carrier. The direct common-norm trace candidate is impossible by Lemma 2.2A; the CM-unitary
center instead supplies the Hodge lift.  The connected adjoint fiber product identifies an
actual unitary level cover over a component field unramified at $3\ell$, Book 121 supplies its
good model, and Proposition 2.2 transports the raw plane to the Tate module of a good abelian
variety over $F_i$.
Nonzero-oldvector embeddings, semisimplification,
commensurability, local Mackey decomposition, and saturated closure inside the positive Brauer
term then construct $(\mathrm{IC}_3)$ directly.  The rank-two filtered calculation gives an
independent second construction of a strongly divisible lattice.  In either route, compactness
chooses a global lattice and the saturated subquotient theorem transfers finite flatness without
identifying two integral structures. Raynaud rigidity supplies all transition maps and exact
multiplication sequences. No integral packet projector is constructed because none is needed.

The same global lattice meets the rational SP line in a saturated rank-one module. Its finite
reductions form compatible signed-special filtrations. Their tame inertia is cyclic of
$3$-power order, square-zero on the rank-two module, and of order at most three on every
exponent-three subquotient. This is exactly the odd-tame local behavior used by the Schoof
category.

Book 185, Proposition 8.3 certifies clean support.  Unique finite-etale models away from three and the selected
finite-flat model at three intersect to one Hopf order over $\mathbf Z[1/2]$. Coefficients,
transition maps, exact sequences, determinant, and duality glue with it. The resulting tower
is precisely the input to Book 188's conditional Frey--SP reducibility theorem.

### 12.2 Readiness verdict

The positive good-abelian carriers and the fixed-three integral construction are complete.
The direct argument removes $(\mathrm{IC}_3)$ as an independent field of the admitted
compatible-family arithmetic core. Book 185, Proposition 8.3 removes
$(\mathrm{Cond}_2)$ as a second independent field and proves clean support at every auxiliary
prime.  Thus Theorem 10.2 is Schoof-ready from the controlled rational family; the stronger
automorphic-type comparisons are not required.

Therefore the unconditional FLT dependency status of this book is

$$
\boxed{\textbf{READY}.}
\tag{12.1}
$$

Book 182 supplies the controlled top on the preferred selected-three route. The split moving
specialization, selected ascent and descent, packet
attachment, fixed-three raw-to-global comparison, and clean auxiliary support are now proved.
Book 176, Theorem 1.1H and Corollary 1.1I prove the auxiliary and target instantiations of
$({\rm CIAV}_P)$ separately; no clean minimal-SP seed is required.
The raw dyadic carriers are supplied targetwise by Books 118, 122, and 168, and the selected
coefficient-three raw-to-global step is supplied by the finite-flat bridge of Books 54 and
168; full smooth-proper $(\mathrm{HT}_{\mathrm{curve}})$ remains necessary only for the
optional uniform all-coefficient packet statement. The AUX Galois comparisons are proved
once the controlled top is supplied. Book 182's stronger automorphic-type theorem remains
open, but it no longer lies on the clean-support path.
