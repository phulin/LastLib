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
the controlled top and its split local packet was supplied.  The current source chain does not
construct that carrier certificate.
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

The restricted Book 185 conclusion provides, at each coefficient place away from two and hence
at the selected $\nu\mid3$, an actual characteristic-zero cancellation

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
the source-facing compatible-family arithmetic core.  As part of the carrier input, require
the rational prime $3$ to be among the sensitive places in Book 182's normal-top construction
and require the corresponding split evaluated packet over $\mathbf Q_3$ in its moving datum.
The normal-top theorem then makes $3$ split completely in $M$ and hence in every elementary
fixed field.  This is an input, not a consequence of merely writing $3$ in the sensitive set:
Book 182, Proposition 6.2A constructs the base-completion packets at $2$ and $\ell$, not an
additional packet at $3$.
After the top and one integral Brauer datum
$\mathfrak B=\{(H_i,\theta_i,n_i)\}$ have been chosen, write
$n_i=n_i^+-n_i^-$.  For every $i$ with $n_i^+>0$, require the following rational carrier
certificate.

- The corrected packet $\pi_{H_i}$ occurs on an actual compact division-quaternion
  one-split carrier $X_i$.  There is also a specified direct-trace PEL-exact curve $Y_i$ for
  the connected common-norm central modification to which the basic Hodge map lifts, or for
  the basic group when the two data coincide, together
  with a finite surjective morphism $f_i:Y_i\to X_i$ over the elementary fixed field, at
  compatible levels and on full component-routing unions.  Equality of adjoint groups is not
  substituted for this morphism.
- The rational raw multiplicity plane extracted from $H^1(X_i)$, after the covariant Tate
  twist, has semisimplification equal to the elementary representation used in Book 185.
  Every local factor above $3\ell$ is spherical, and the basic packet occurrence and finite
  comparison persist when those local levels are replaced by compatible hyperspecial
  stabilizers.

Call this finite requirement $(\mathrm{Car}_3^+)$.  No carrier is required for an index
occurring only on the negative side.  The requirement does not say that an integral Hecke
idempotent cuts out the packet, and it does not assume a good integral model.  It supplies the
exact rational PEL cover to which the good-model theorem can be applied.  This distinction is
necessary: a basic quaternionic curve and a direct-trace PEL central modification have the
same adjoint domain but need not have the same component set or universal abelian scheme.
The finite map, rather than an identification of the two curves, will transport the rational
packet plane.

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

**Proposition 2.2 (good carriers at the prescribed split primes).** Under
$(\mathrm{Car}_3^+)$, the positive carriers may be chosen so that their curves, and hence
their relative Jacobians, have good reduction at every place above both $3$ and the old
coefficient prime $\ell$.  Their covariant raw multiplicity planes have semisimplifications
equal to the elementary representations used in $R_{\mathfrak B,\nu}^+$.

**Proof.** The top seed is minimal away from $\{2,\ell\}$.  Thus its factor at every place
above $3$ is spherical.  The exact SP seed also uses the clean hyperspecial
coefficient-prime automorphic level, so its factor at every place above $\ell$ is spherical.
Complete splitting at both $3$ and $\ell$ makes every
downward local extension there the identity and makes every quotient-character correction and
every Brauer character $\theta_i$ locally trivial.  Consequently each $\pi_{H_i,w}$ with
$w\mid3\ell$ is spherical.

Use the division one-split quaternion algebra supplied by $(\mathrm{Car}_3^+)$.  Its finite ramification
set is chosen from the eligible special or tame-dihedral places, so it contains no spherical
place above $3\ell$.  Choose its local order at $w\mid3\ell$ to be the full matrix order and its
level to be hyperspecial.  It remains to verify rather than assume the integral trace lattice.

Fix splittings $B_w\simeq M_2(\mathbf Q_p)$ for $w\mid p$ and
$p\in\{3,\ell\}$.  Since both rational primes split completely in $F_i$, there is no local
inverse-different factor in the field trace.  In the pure subspace of $M_2(\mathbf Q_p)$ the
matrix

$$
\delta_w^0=\begin{pmatrix}1&0\\0&-1\end{pmatrix}
$$

is invertible.  For the direct-trace form on $M_2(\mathbf Z_p)$ its Gram matrix, in the four
matrix units, pairs the two diagonal units and the two off-diagonal units in two alternating
blocks with unit entries.  It is therefore perfect.  Moreover the positive involution
$b\mapsto(\delta_w^0)^{-1}\bar b\delta_w^0$ preserves $M_2(\mathbf Z_p)$.  Both properties
remain true when the pure multiplier lies in a sufficiently small $p$-adic neighborhood of
$\delta_w^0$.

Start from the positive multiplier in the rational PEL datum stipulated by
$(\mathrm{Car}_3^+)$.  Weak approximation in the global pure-quaternion subspace chooses one
invertible $\delta$ in all the prescribed finite neighborhoods and sufficiently close to that
multiplier at every real place to stay in the same positive Hodge cones.
This simultaneously addresses the warning in Book 115 that a rational pure multiplier and an
integral order cannot be selected independently.  At $w\mid3\ell$ prescribe the full matrix
order.  Away from those places start with any auxiliary local order and intersect it with its
image under the $\delta$-involution; these intersections agree with one reference order at
almost every place.  Book 82's reconstruction theorem gives a global $*$-stable order with
the prescribed completions.  Use that order itself as the left-module lattice.  The
direct-trace form is already integral and perfect at $w\mid3\ell$; multiplying it by one
positive integer supported away from $3\ell$ clears every remaining denominator without
changing the involution or local self-duality.  The common-norm similitude group is independent
of the pure multiplier, and the real approximation stays in the original positive component.
Thus the new multiplier gives another PEL-exact realization of the same common-norm Shimura
datum.  Canonical-model uniqueness identifies its component union with the stipulated one and
transports the finite central comparison and packet occurrence, although the literal PEL
presentation has changed.  The integral
constructions of Books 115 and 119 now give
polarization degree a unit and reductive self-dual stabilizer at both prescribed primes; Book
118 retains the specified basic-to-central-modification comparison and its actual component
labels.

Take the full component-routing union, retain the entire multiplier-and-orientation label
union occurring in the rational datum, and choose a normal fine auxiliary level away from
$3\ell$ and from the polarization degree.  Because $3$ splits completely in $F_i$, the decomposition
$\mathcal O_{F_i}\otimes\mathbf Z_3\simeq\prod_{w\mid3}\mathbf Z_3$ has integral primitive
idempotents.  The direct-trace determinant law is therefore the standard rank-one law on the
active matrix factor and the fixed rank-zero or full-rank law on every inactive factor.  No
smaller multiplier or orientation component is selected, so those two ledger clauses impose
no generic idempotent whose integral extension would have to be proved.  The full component
union is decomposition-group stable, and the self-dual matrix lattice has the reductive
hyperspecial stabilizer.  Thus every nonvacuous item in the exact ledger holds over the split
reflex local ring $\mathbf Z_3$.  This
verifies the complete ledger of Book 121, Theorem 12.1.  That theorem supplies a smooth
projective integral curve with its universal PEL data.  Book 129, Section 8.2 then makes its
relative identity Picard scheme, equivalently the product of its component Jacobians after a
splitting extension, an abelian scheme over $\mathbf Z_3$.  The identical argument using the integral
decomposition at $\ell$ gives good reduction over every completion above $\ell$.

The spherical basic packet still occurs after this choice of level: a spherical vector is
fixed by the hyperspecial factor, and the other level factors may be shrunk without destroying
a previously fixed vector.  Book 127 extracts its intrinsic raw rank-two multiplicity space
$W_i^{\mathrm{raw}}$.  Choose a nonzero vector in the finite oldvector factor; Book 129,
Sections 8.1--8.2 then embeds a copy of $W_i^{\mathrm{raw}}$ in $H^1(X_i)$ with the required
curve-to-Tate normalization.  For the finite central
comparison, on each target component one has

$$
(f_i)_*f_i^*=(\deg f_{i,\mathrm{comp}})\operatorname{id}
$$

on rational first cohomology.  Every displayed degree is nonzero, so $f_i^*$ embeds
$W_i^{\mathrm{raw}}$ into $H^1(Y_i)$,
and therefore, with the covariant twist, into a finite power of the Tate module of the good
relative Jacobian of $Y_i$.  No assumption that the universal PEL abelian scheme descends to
$X_i$ is used.  If the elementary representation in the controlled array was first
constructed from another level, the two semisimplifications have the same packet Frobenius
polynomials at a density-one set; Book 142's density theorem and Book 180's
Brauer--Nesbitt criterion identify them.  The degree of $f_i$ and the
level-return maps may be divisible by $3$ or $\ell$: only the rational embedding is used, and
Book 129 later saturates it rather than dividing integrally.  Thus the good PEL cover realizes
precisely the elementary semisimple representation used by Book 185.  This is
$(\mathrm{AVCar}_{3,\ell}^+)$. $\square$

**Theorem 2.3 (the positive display supplies $(\mathrm{IC}_3)$).** Under
$(\mathrm{AVCar}_{3,\ell}^+)$, and hence under $(\mathrm{Car}_3^+)$, the actual cancellation
(2.3) constructs a flat companion satisfying $(\mathrm{IC}_3)$.  In fact its quotients form
one compatible exact coefficient-linear finite-flat tower over $\mathbf Z_3$.

**Proof.** Enlarge the coefficient field once to a finite extension $C/K$ which splits all
positive packet blocks, and put $A=\mathcal O_C$.  For a positive elementary packet and a
place $w\mid3$, use the rational embedding supplied by
$(\mathrm{AVCar}_{3,\ell}^+)$.  In the PEL-cover construction of Proposition 2.2 it is the
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

The integral primitive idempotents used in Proposition 2.2 are of a different kind: they are
the factors of $\mathcal O_{F_i}\otimes\mathbf Z_3$ supplied by complete splitting, and they
route the determinant and Hodge labels of the PEL local model.  They do not cut the packet out
of cohomology.  The packet and coefficient-block projectors remain rational and may have
nonunit denominators; neither finite flatness nor exactness is deduced by applying them to
torsion.

The theorem removes $(\mathrm{IC}_3)$ as an independent post-assembly arithmetic premise
once $(\mathrm{AVCar}_{3,\ell}^+)$ is supplied.  It does not construct the still-missing
positive attachment and basic-carrier theorem upstream of Book 183, nor the exact direct-trace
PEL cover used to prove the good-carrier certificate.  It proves that no additional full
compatible-family arithmetic core is needed at three after those earlier carrier inputs are
supplied.

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

The clean-support certificate $(\mathrm U)$ is therefore a finite theorem: for each
$q\in S_{\mathrm{aux}}$, prove that the local representation $V|_{I_q}$ is trivial. A stronger
and more reusable certificate proves that $q$ lies in Book 185's local comparison range and
that $D_q$ is unramified. It then also supplies the algebraic polynomial of Frobenius at $q$.

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

At the distinguished original coefficient place, the chosen lift is unramified away from its
two permitted primes. That fact identifies $D_q$ as unramified only when the common local
object at $q$ has actually been constructed and compared. Injectivity of a coefficient
embedding transports a zero monodromy matrix and identity inertia once those algebraic
matrices exist; it does not create them.

The old coefficient prime $q=\ell$ is already removed on the geometric route
$(\mathrm{AVCar}_{3,\ell}^+)$.  In the sufficient PEL version, Proposition 2.2 chooses every
positive carrier good and hyperspecial at $\ell$.  In either formulation, the oldvector
embedding into the good Jacobian makes the raw three-adic multiplicity plane unramified at
$\ell$, and unramifiedness survives its semisimplification.  In the PEL formulation this is
also exactly Book 128's good-place comparison.  Complete splitting makes the Brauer characters
trivial and local Mackey induction a direct sum, so
$R_{\mathfrak B,\nu}^+$ is unramified at $\ell$.  The actual injection
$V\hookrightarrow R_{\mathfrak B,\nu}^+$ from (2.3) then makes $V$ unramified at $\ell$.
Thus the selected-member auxiliary theorem remaining after
$(\mathrm{AVCar}_{3,\ell}^+)$ concerns only
$q\in S_{\mathrm{aux}}\setminus\{\ell\}$.

Book 185, Proposition 8.2 packages the minimal finite statement as
$(\mathrm{AUX}_\nu)$.  For $q\in S_{\mathrm{aux}}\setminus\{\ell\}$ it requires the
algebraic complement and its comparisons with both the distinguished $\ell$-adic member and
the selected three-adic member.  The first member is unramified, so the complement, and then
$V$, is unramified.  At $q=\ell$ there is no prime-to-$q$ comparison with the distinguished
member; the replacement is the spherical algebraic packet calculation together with its
prime-to-$\ell$ comparison at $\nu$.  These finitely many checks prove $(\mathrm U)$ directly
and do not quantify over the unused coefficient places.

Book 185, Proposition 8.1 packages the source-facing alternative as the conductor-support
assertion $(\mathrm{Cond}_2)$: the common bad-place set of the actual genuine Brauer
realization is supported at the rational prime two. Its specialization theorem applies to a
member at coefficient characteristic $3$ at every $q\ne3$. Hence, if $q\ne2,3$, support at
two puts $q$ outside the common bad set and specialization makes $V$ unramified at $q$.
Therefore

$$
(\mathrm{Cond}_2)\Longrightarrow(\mathrm U).
\tag{7.4a}
$$

This implication is a complete conductor reduction.  Book 185's stronger
$(\mathrm{AUX}_{\mathrm{all}})$ supplies all of the finite local-complement checks and proves
$(\mathrm{Cond}_2)$ without using the source-facing compatible-family arithmetic core.  It
is not presently proved: at the nonspherical auxiliary places the missing input is the actual
tame principal or dihedral descent comparison, including its type lines, zero-monodromy
calculation, exchange and Frobenius return maps, and raw-to-global passage.  The already proved
common finite-bad-set statement does not imply that its support is only two.

One cannot instead declare all auxiliary primes spherical.  Primes ramified in the
nontrivial controlled top do not split there, and nonsplit cyclic descent can turn a spherical
top factor into a tame principal-series or selected tame-dihedral factor.  The positive and
negative Brauer terms can therefore both be ramified even though their genuine rank-two
complement is expected to be unramified.  Actual local cancellation, not positive-term good
reduction at every auxiliary prime, is the required argument.

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

The global cyclotomic line in (9.1) is an output of the classification. It must not be
identified in advance with the local $D_2$-stable line $T_2^+$. After (9.1) exists, uniqueness
of the inertia-fixed line for nonzero SP monodromy identifies the two rational lines. This can
force the dyadic sign to be split, but the usual good-Frobenius trace contradiction works
without using that shortcut.

At any certified pure good prime $q\ne2,3$, (9.2) gives

$$
\operatorname{tr}V(\operatorname{Frob}_q)=1+q.
\tag{9.3}
$$

Weight-one purity gives

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

Under $(\mathrm{AVCar}_{3,\ell}^+)$, and hence under $(\mathrm{Car}_3^+)$, the separate
hypothesis $(\mathrm C_3)$ in Theorem 10.1 is automatic: Theorem 2.3 supplies
$(\mathrm{IC}_3)$ and Proposition 2.1 supplies $(\mathrm C_3)$.  Thus the FLT-scoped
geometric version of the theorem begins with the positive good-carrier statement, not with an
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
of the conditional Frey--SP three-adic reducibility theorem in Book 188. A prime in the
cofinite certified good set transported by Book 186 supplies the separate pure Frobenius
polynomial used after reducibility.

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
| Book 42 | marked finite-flat models, schematic closure, represented quotients, coefficient actions, and finite-etale models | Proposition 4.2 and the local-to-global model calculus | no extension is called finite flat from its endpoints alone |
| Book 54 | integral Fontaine--Laffaille realization, full faithfulness over $\mathbf Z_3$, admissible coefficient quotients, exact compatible systems, and coefficient-dual normalization | Chapters 3 and 5 | rational Hodge labels do not select a lattice, and coefficient duality is not silently identified with Cartier self-duality |
| Book 82 | reconstruction of global quaternion orders and lattices from finitely prescribed local models | Proposition 2.2's fixed-three integral selection | local maximality at three is not called a global canonical order |
| Book 115 | direct quaternion-trace pairing, multiplier group, positivity boundary, and the separate integral self-duality test | Proposition 2.2's local standard matrix calculation | a pure multiplier and an order are not selected independently |
| Book 118 | PEL-exact central modifications, their finite comparison with the basic canonical curve, their component labels, and the warning that equal adjoint groups do not identify curves | the precise carrier certificate and rational pullback in Section 2.5 | the basic curve is not silently identified with a PEL cover |
| Book 119 | exact quaternionic PEL datum, finite central cover, integral order, lattice, polarization type, determinant law, and representability interface | Proposition 2.2's passage from the rational cover to integral PEL data | rational PEL realizability is not inferred from the quaternion algebra alone |
| Book 121 | the complete odd hyperspecial ledger and the resulting smooth projective direct-trace curve with universal abelian scheme | Proposition 2.2 | sphericality alone is not called good reduction |
| Book 125 | rational pullback--trace on full component unions and the complete finite Hecke block in curve cohomology | transporting the basic raw packet plane to the good PEL cover | the cover degree is not assumed to be a coefficient unit |
| Book 127 | the actual basic one-split curve carrier and its covariantly normalized raw multiplicity space | Proposition 2.2 | no carrier is asserted outside its stated eligibility range and no basic-to-PEL comparison is inferred |
| Book 128 | the exact good, tame-principal, and tame-dihedral local comparison criteria | the finite auxiliary blocker in Chapter 7 | an automorphic type name is not substituted for the geometric type and return-map package |
| Book 129 | saturated geometric intersections, exact closure towers, commensurability transfer, coefficient change, and the fixed-three handoff | the geometric route and the proof architecture of Chapters 3--5 | no canonical geometric carrier or integral projector is claimed |
| Book 142 | density of Frobenius classes after removal of the finite packet exceptional set | recognizing the semisimple packet realization after the fixed-three level change | density is not used to construct a representation or compare different coefficient topologies |
| Book 161 | the Schoof category, its classification and filtration theorem, and the finite-level coefficient trace identity | Section 9 handoff and Theorem 10.2's Schoof-ready output | it does not select the coefficient place or construct the named tower |
| Book 180 | Brauer--Nesbitt recognition for already existing semisimple representations and local Mackey algebra | identifying the same packet after the fixed-three level choice | density is not used across different coefficient topologies |
| Book 182 | the normal-top mechanism making a supplied finite set of split local packets split in the controlled top, and minimality of the top packet away from $\{2,\ell\}$ | the spherical fixed-three input to Proposition 2.2 after the $\mathbf Q_3$ packet has been supplied | it constructs the base-completion packets at $2$ and $\ell$, not the additional split packet at $3$ or the missing elementary carriers |
| Book 185 | the $(\mathrm{AI}_2)$-independent away-from-two members, actual characteristic-zero Brauer cancellation, algebraic local complements, and the common pure polynomial ledger | the optional cancellation route in Section 2.3 and the finite clean-support checks in Chapter 7 | no coefficient-two member or coefficient-prime comparison is imported |
| Book 186 | selection of the actual member at $\nu\mid3$, its determinant, pure good polynomials, and its full signed SP pair at two | the rational starting object and dyadic local data | its theorem explicitly uses no $(\mathrm{AI}_2)$ and supplies no coefficient-prime comparison, clean support, lattice, or tower |

Accordingly the proposed direct dependency row is

$$
\boxed{187\mid 3,\ 42,\ 54,\ 82,\ 115,\ 118,\ 119,\ 121,\ 125,\ 127,\ 128,\ 129,\ 142,\ 161,\ 180,\ 182,\ 185,\ 186.}
\tag{11.1}
$$

Book 168 is a transitive source for the packet comparison records used inside Books 183--185.
Books 164--165 establish the Frey provenance and deformation-theoretic meaning of the signed
SP line. Books 183--184 construct
the SP packet array and prove rational effectivity. None is a separate direct proof input after
the restricted Book 185 result and Book 186 handoff are assumed. Book 161 is the actual category
and classification source named in the Schoof-ready handoff; Book 188 is the downstream
application layer.

### 11.2 Exact blocker audit

Books 185--186 by themselves do not prove $(\mathrm C_3)$, but
$(\mathrm{IC}_3)$ is no longer an independent post-assembly arithmetic hypothesis once the
positive good-abelian-carrier certificate is supplied.  Require $3$ among the sensitive places
before constructing the controlled top and include its split $\mathbf Q_3$ packet in that
input.  Proposition 2.2 proves
$(\mathrm{Car}_3^+)\Rightarrow(\mathrm{AVCar}_{3,\ell}^+)$, and Theorem 2.3 proves
$(\mathrm{AVCar}_{3,\ell}^+)\Rightarrow(\mathrm{IC}_3)$.  Proposition 2.1 then proves
$(\mathrm C_3)$.  In particular, an integral coefficient idempotent, an integral Brauer
cancellation, and the admitted full compatible-family arithmetic core are not needed after
the good positive carriers exist.

The first missing carrier theorem is therefore upstream and exact:

> **Positive good-abelian-carrier theorem
> $(\mathrm{AVCar}_{3,\ell}^+)$.** Start with a controlled top whose moving datum includes
> the split evaluated packet over $\mathbf Q_3$.  Along the selected cyclic descents used by
> one integral Brauer relation, construct for every positive corrected packet an abelian variety good above
> $3$ and $\ell$, together with the correctly normalized raw multiplicity embedding in its
> coefficient-linear Tate module and the identification after semisimplification with the
> elementary representation.  A sufficient geometric version is $(\mathrm{Car}_3^+)$:
> construct the actual direct-trace PEL cover of a compact division-quaternion basic carrier,
> including the finite morphism on the required full component unions and compatible levels.
> Proposition 2.2 then makes its integral datum hyperspecial and self-dual at the two split
> primes and injects the basic raw packet plane by rational pullback.

This is the positive part of Book 182's already isolated all-elementary attachment, descent,
and raw-carrier problem, sharpened by one indispensable clause: each positive compact
division-quaternion basic carrier must admit the stated direct-trace PEL central cover and
finite component-level comparison.
The prior PEL books construct such a finite comparison once the exact PEL realization is
supplied, but they do not prove that the direct-trace positive-Hodge realization required by
the good-model theorem exists for every one-split carrier in this packet array.  The present
corpus also does not exhibit an integral Brauer relation whose positive
subgroup list avoids every missing carrier range; abstract Brauer induction gives no control
of the signs needed for that shortcut.  Some elementary fixed fields have odd degree, the
minimal top packet can lack an eligible away-from-two place, and the candidate cyclic descents
still need their attachment and base-change compatibility.  Book 182's ambient-semisimplicity
clause is not required for this fixed-three substatement because Theorem 2.3 passes to
semisimplification by finite-flat subquotients.  Once these actual positive PEL carriers exist,
no further coefficient-three blocker remains.

Before those carrier questions, the controlled-seed construction has the separate local task
of supplying the split $\mathbf Q_3$ packet; Proposition 6.2A of Book 182 handles only $2$ and
$\ell$.  This task is folded into the standing input of both carrier symbols above, not inferred
from the normal-top field geometry.

There are then two carrier failure points, not one theorem hidden under two names.
The earlier one is the positive-sign part of Book 182's attachment/descent/raw-carrier theorem:
some required corrected packets and basic carriers have not yet been constructed.  Even after
that theorem, the present good-model source still needs the exact direct-trace PEL realization
for each resulting carrier.  The combined minimal conclusion needed by this book is
$(\mathrm{AVCar}_{3,\ell}^+)$; $(\mathrm{Car}_3^+)$ is the source-facing geometric theorem
which proves it.  Neither gap may be replaced by the statement that the automorphic local
factor is spherical.

There is a separate local-support obstruction.  For the selected member the minimal missing
theorem is Book 185's finite certificate $(\mathrm{AUX}_\nu)$; for the whole family it is
$(\mathrm{AUX}_{\mathrm{all}})$, which implies $(\mathrm{Cond}_2)$.  At each nonspherical
auxiliary prime this theorem must construct the actual algebraic packet pairs and verify the
principal or dihedral descent complex, type lines, zero monodromy, exchange and Frobenius
return maps, and raw-to-global passage at the two coefficient places used in the comparison.
For the family-wide statement, $q=\ell$ instead uses the spherical algebraic calculation and
its prime-to-$\ell$ realization.  For the selected member the good positive display in
$(\mathrm{AVCar}_{3,\ell}^+)$ removes $q=\ell$ directly; in the sufficient PEL route,
Proposition 2.2 constructs that display and its good-place comparison.  Book 185,
Proposition 8.2 proves

$$
(\mathrm{AUX}_\nu)\Longrightarrow(\mathrm U),
\qquad
(\mathrm{AUX}_{\mathrm{all}})\Longrightarrow(\mathrm{Cond}_2)
\Longrightarrow(\mathrm U).                                \tag{11.2}
$$

No theorem in the current packet input supplies those data at every auxiliary prime.  In
particular, the ramified primes of a nontrivial controlled top cannot all be split, and
nonsplit descent can produce tame principal or dihedral factors.  Almost-all Frobenius
polynomials contain neither inertia nor monodromy at an exceptional prime and do not compare
continuous trace limits in two different coefficient topologies.

Book 186's unramified-outside-$\{2,3\}$ conclusion is conditional on precisely
$(\mathrm U)$.  Book 188 consumes Theorem 10.2 only after clean support, so it cannot feed the
missing comparison backward.  The audited FLT source packages $(\mathrm{IC}_3)$ and
$(\mathrm{Cond}_2)$ as fields of one admitted arithmetic core, but Sections 2.5 and 7.2 show
that this package is far stronger than necessary: the positive good-abelian-carrier theorem
$(\mathrm{AVCar}_{3,\ell}^+)$ proves the former, while the finite two-coefficient auxiliary
theorem is the first exact remaining local input for the latter.

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

**Attack: weak compatibility removes all auxiliary ramification.** It does not. The finite
checks in $(\mathrm U)$ require actual local comparison or actual direct-summand
unramifiedness.  Frobenius density in one completion does not identify the values of two
continuous trace functions at an inertia element by taking limits in different completions.

**Attack: every auxiliary packet factor may be taken spherical.** It may not.  Ramification
of the controlled top and nonsplit cyclic descent can produce principal or tame-dihedral
factors.  Only the fixed prime $3$, named split before the construction, has the uniform
spherical argument used in Proposition 2.2.

**Attack: a spherical basic quaternionic packet automatically has the good PEL carrier used
in Proposition 2.2.** It does not.  The good-model theorem is typed to an exact PEL
realization.  A central modification can change components and the abelian quotient, and a
rational quaternion algebra does not by itself supply a positive involution or a self-dual
trace lattice.  A supplied finite central map is enough to transport the raw plane by rational
pullback, even when its degree is not a unit, but equality of adjoint groups does not construct
that map or the exact direct-trace realization.  These are precisely the extra clauses in
$(\mathrm{Car}_3^+)$; the weaker minimal alternative is to supply
$(\mathrm{AVCar}_{3,\ell}^+)$ directly.

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
The full arithmetic core is unnecessary once the weaker positive good-abelian-carrier theorem
$(\mathrm{AVCar}_{3,\ell}^+)$ is supplied.  A sufficient source is the exact rational PEL
carrier certificate $(\mathrm{Car}_3^+)$ on compact division-quaternion carriers, from which
Proposition 2.2 constructs good reduction at the two prescribed split primes.
Nonzero-oldvector embeddings, semisimplification,
commensurability, local Mackey decomposition, and saturated closure inside the positive Brauer
term then construct $(\mathrm{IC}_3)$ directly.  The rank-two filtered calculation gives an
independent second construction of a strongly divisible lattice.  In either route, compactness
chooses a global lattice and the saturated subquotient theorem transfers finite flatness without
identifying two integral structures.  Raynaud rigidity supplies all transition maps and exact
multiplication sequences.  The present source chain does not construct
$(\mathrm{AVCar}_{3,\ell}^+)$ or $(\mathrm{Car}_3^+)$.

The same global lattice meets the rational SP line in a saturated rank-one module. Its finite
reductions form compatible signed-special filtrations. Their tame inertia is cyclic of
$3$-power order, square-zero on the rank-two module, and of order at most three on every
exponent-three subquotient. This is exactly the odd-tame local behavior used by the Schoof
category.

Once clean support is certified, unique finite-etale models away from three and the selected
finite-flat model at three intersect to one Hopf order over $\mathbf Z[1/2]$. Coefficients,
transition maps, exact sequences, determinant, and duality glue with it. The resulting tower
is precisely the input to Book 188's conditional Frey--SP reducibility theorem.

### 12.2 Readiness verdict

The integral construction is complete as a conditional theorem.  The direct fixed-three
argument removes $(\mathrm{IC}_3)$ as an independent field of the admitted compatible-family
arithmetic core after $(\mathrm{AVCar}_{3,\ell}^+)$ is supplied.  The current spine does not
construct that good-abelian-carrier theorem or its sufficient exact PEL version
$(\mathrm{Car}_3^+)$.  Clean support at every auxiliary prime is also not proved.

Therefore the unconditional FLT dependency status of this book is

$$
\boxed{\textbf{NOT READY}.}
\tag{12.1}
$$

The first carrier blocker is now the exact upstream theorem
$(\mathrm{AVCar}_{3,\ell}^+)$ of Section 11.2, with $(\mathrm{Car}_3^+)$ as a sufficient
PEL-geometric version, not a separate flat-companion theorem.  Once it is supplied, Theorem
2.3 proves $(\mathrm{IC}_3)$ and hence the entire local integral tower.  The remaining global blocker is
the finite selected-member comparison $(\mathrm{AUX}_\nu)$; its family-wide form
$(\mathrm{AUX}_{\mathrm{all}})$ proves $(\mathrm{Cond}_2)$, and Proposition 8.1 then gives
$(\mathrm U)$.  After those exact carrier and local-comparison clauses, Theorem 10.2 is
Schoof-ready.
