# Auxiliary Dihedral Data and Residual Potential Modularity

## Contents

1. [The two-prime method](#1-the-two-prime-method)
   - [The problem and the bridge](#11-the-problem-and-the-bridge)
   - [Standing conventions](#12-standing-conventions)
   - [What must be chosen](#13-what-must-be-chosen)
   - [The logical boundary](#14-the-logical-boundary)
2. [Residual and coefficient data](#2-residual-and-coefficient-data)
   - [The target representation](#21-the-target-representation)
   - [Determinant normalization](#22-determinant-normalization)
   - [Simultaneous coefficient-field realization](#23-simultaneous-coefficient-field-realization)
   - [The finite-set lifting interface](#24-the-finite-set-lifting-interface)
3. [Choosing the auxiliary prime](#3-choosing-the-auxiliary-prime)
   - [Why a second residue characteristic is useful](#31-why-a-second-residue-characteristic-is-useful)
   - [Avoiding finitely many bad choices](#32-avoiding-finitely-many-bad-choices)
   - [Two independent primes of the real-multiplication field](#33-two-independent-primes-of-the-real-multiplication-field)
   - [Local coefficient-prime requirements](#34-local-coefficient-prime-requirements)
4. [The dihedral seed](#4-the-dihedral-seed)
   - [CM induction and parallel weight two](#41-cm-induction-and-parallel-weight-two)
   - [The determinant equation](#42-the-determinant-equation)
   - [Local ray data and global units](#43-local-ray-data-and-global-units)
   - [The inverse-branch ray-class lemma](#44-the-inverse-branch-ray-class-lemma)
   - [Residual irreducibility and cyclotomic irreducibility](#45-residual-irreducibility-and-cyclotomic-irreducibility)
   - [Finite flatness at the auxiliary prime](#46-finite-flatness-at-the-auxiliary-prime)
   - [The controlled dihedral-seed theorem](#47-the-controlled-dihedral-seed-theorem)
   - [Protected Frobenius correction](#48-protected-frobenius-correction)
5. [Protected local branches on the split route](#5-protected-local-branches-on-the-split-route)
   - [Branch data at the controlled places](#51-branch-data-at-the-controlled-places)
6. [The twisted Hilbert--Blumenthal cover](#6-the-twisted-hilbert--blumenthal-cover)
   - [The moduli datum](#61-the-moduli-datum)
   - [The two prescribed torsion systems](#62-the-two-prescribed-torsion-systems)
   - [Why determinants are an existence condition](#63-why-determinants-are-an-existence-condition)
   - [Geometric monodromy and connectedness](#64-geometric-monodromy-and-connectedness)
   - [Arithmetic components](#65-arithmetic-components)
7. [Local points on one component](#7-local-points-on-one-component)
   - [Real places](#71-real-places)
   - [The target coefficient prime](#72-the-target-coefficient-prime)
   - [The auxiliary coefficient prime](#73-the-auxiliary-coefficient-prime)
   - [Ramification of the dihedral seed](#74-ramification-of-the-dihedral-seed)
   - [The split special places](#75-the-split-special-places)
   - [Good and semistable auxiliary conditions](#76-good-and-semistable-auxiliary-conditions)
   - [The simultaneous local-neighborhood lemma](#77-the-simultaneous-local-neighborhood-lemma)
8. [Split Galois-top specialization](#8-split-galois-top-specialization)
   - [The avoidance field](#81-the-avoidance-field)
   - [The Book 158 specialization](#82-the-book-158-specialization)
   - [Preservation of residual images](#83-preservation-of-residual-images)
   - [The specialization theorem](#84-the-specialization-theorem)
9. [The Hilbert--Blumenthal bridge](#9-the-hilbert--blumenthal-bridge)
   - [The specialized abelian variety](#91-the-specialized-abelian-variety)
   - [What the two torsion identifications say](#92-what-the-two-torsion-identifications-say)
   - [Local properties of the auxiliary-adic representation](#93-local-properties-of-the-auxiliary-adic-representation)
   - [No inference from torsion alone](#94-no-inference-from-torsion-alone)
10. [The finite-set modularity transfer](#10-the-finite-set-modularity-transfer)
    - [Automorphy of the residual dihedral member](#101-automorphy-of-the-residual-dihedral-member)
    - [The all-active-place handoff](#102-the-all-active-place-handoff)
11. [Recovering residual automorphy at the original prime](#11-recovering-residual-automorphy-at-the-original-prime)
    - [Weight-two Galois realization](#111-weight-two-galois-realization)
    - [The cross-prime Tate comparison](#112-the-cross-prime-tate-comparison)
    - [The residual potential-modularity theorem](#113-the-residual-potential-modularity-theorem)
    - [A stronger controlled form](#114-a-stronger-controlled-form)
12. [Exceptional cases and failure tests](#12-exceptional-cases-and-failure-tests)
    - [Coefficient characteristics below seven](#121-coefficient-characteristics-below-seven)
    - [Reducible and cyclotomically reducible images](#122-reducible-and-cyclotomically-reducible-images)
    - [Determinant and pairing failures](#123-determinant-and-pairing-failures)
    - [Component and local-solvability failures](#124-component-and-local-solvability-failures)
    - [Failure of closure-level disjointness](#125-failure-of-closure-level-disjointness)
    - [Failure of finite-set modularity lifting](#126-failure-of-finite-set-modularity-lifting)
13. [Dependency and hypothesis audit](#13-dependency-and-hypothesis-audit)
    - [The prerequisite interfaces](#131-the-prerequisite-interfaces)
    - [The theorem-by-theorem hypothesis ledger](#132-the-theorem-by-theorem-hypothesis-ledger)
    - [Circularity audit](#133-circularity-audit)
    - [Normalization audit](#134-normalization-audit)
14. [Conclusion](#14-conclusion)
   - [The split two-prime package](#141-the-split-two-prime-package)

## 1. The two-prime method

### 1.1 The problem and the bridge

Let $K$ be a totally real number field and let

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(k)
$$

be continuous, where $k$ is a finite field of characteristic $\ell$. Residual potential
modularity asks for a finite totally real extension $K'/K$ and a cuspidal parallel-weight-two
automorphic representation $\Pi$ over $K'$ such that

$$
\bar\rho|_{G_{K'}}\otimes_k k_\lambda
\simeq\bar\rho^T_{\Pi,\lambda}
$$

for a place $\lambda$ above $\ell$ of the coefficient field of $\Pi$, where the superscript
$T$ denotes Book 127's covariant Tate realization; in the trivial component-character range
used here it is isomorphic to the dual of the default cohomological realization. The field is allowed to
vary, and that freedom is used to solve several independent local and geometric problems at
once. When the packet coefficient residue field is larger than $k$, the comparison is by scalar
extension as displayed; Chapter 11 also identifies a descended form whose distinguished lattice
reduces over exactly $k$.

A modularity-lifting theorem begins with residual automorphy, which is precisely what is unknown
for $\bar\rho$. A second prime $q\ne\ell$ breaks the circle. We construct a
Hilbert--Blumenthal abelian variety $A$ with real multiplication and torsion identifications

$$
A[\mathfrak l]\simeq\bar\rho|_{G_{K'}},
\qquad
A[\mathfrak q]\simeq\bar r|_{G_{K'}},
\tag{1.1}
$$

where $\mathfrak l$ and $\mathfrak q$ lie above $\ell$ and $q$, and $\bar r$ is a chosen
dihedral representation. It is automorphic because it is induced from a Hecke character of a
CM quadratic extension. Modularity lifting at $q$ then makes the $\mathfrak q$-adic Tate module
of $A$ automorphic. The resulting weight-two packet has a Galois representation at every
coefficient prime, and its $\mathfrak l$-member reduces to the first representation in (1.1).

The bridge is

$$
\begin{array}{ccccc}
\bar r&\longleftarrow&A[\mathfrak q]&\longrightarrow&V_{\mathfrak q}(A)\\
\text{dihedrally automorphic}&&&&\text{automorphic by lifting}\\[2mm]
&&A&&\\[-1mm]
\bar\rho&\longleftarrow&A[\mathfrak l]&\longleftarrow&V_{\mathfrak l}(A).
\end{array}
\tag{1.2}
$$

Every arrow has content. The left arrows are exact paired frames on a twisted moduli space. The
upper right arrow requires a component-sensitive lifting theorem. The lower conclusion requires
a weight-two Galois realization, not merely equality of Hecke eigenvalues at $q$.

### 1.2 Standing conventions

The initial totally real field is $K$; in the FLT application it is $\mathbf Q$, and the final
field is the split Galois top $F/K$ supplied by Book 158. A CM quadratic extension used for
induction is $M/K$. The target and auxiliary rational primes are $\ell$ and $q$. The totally real multiplication field $E$, with primes
$\mathfrak l\mid\ell$ and $\mathfrak q\mid q$, is fixed only after the dihedral coefficient
field has been constructed. This order is essential: $E$ must receive both residual coefficient
fields, not only the target field.

Reciprocity is arithmetically normalized. A uniformizer maps to arithmetic Frobenius. The
mod-$p$ cyclotomic character is $\bar\epsilon_p$, and its characteristic-zero version is
$\epsilon_p$. Covariant Tate modules have cyclotomic determinant after the fixed coefficient-line
identification. The default cohomological realization of a weight-two packet is contravariant:
it has inverse-cyclotomic determinant in the geometric-Frobenius convention. In the two-prime
bridge we use the **covariant automorphic realization**, so that it compares directly with a
Tate module. In Book 127's normalization it is the Tate twist of the untwisted cohomological
member, and essential self-duality identifies it with the dual in the trivial
component-character case. Parallel weight two means labeled weights $\{0,1\}$.

For a finite representation $V$, $K(V)$ denotes the field cut out by its full matrix kernel.
Its projective cutout field is not silently substituted. Disjointness from $K(V)$ preserves the
full matrix image after restriction; projective disjointness preserves less.

Every Hilbert--Blumenthal space in this book uses the tensor choice

$$
I=\mathcal O_E,
\qquad
\mathfrak c=\mathfrak d_E^{-1},
\qquad
\mathfrak c^\vee=\mathcal O_E,
\tag{1.3}
$$

and the corrected auxiliary level source

$$
\mathscr L_N^\natural
=(\mathcal O_E/N\mathcal O_E)
 \oplus(\mathcal O_E/N\mathcal O_E)(1),
\tag{1.4}
$$

whose determinant pairing takes values in $(\mathcal O_E/N\mathcal O_E)(1)$. It is not the
constant oriented module $\mathcal O_E^2/N$. The component is always the
$\mathbf Q$-defined tensor component $H^{\mathrm{ten}}$ of the corrected space
$H^\natural$. This convention is load-bearing at real places and in the product-monodromy
argument.  In the Frey-adapted base-completion refinement, the explicitly permitted replacement
is

$$
E_*[N]\otimes_{\mathbf Z/N\mathbf Z}\mathcal O_E/N\mathcal O_E,
\tag{1.4a}
$$

with $E_*/\mathbf Q$ selected by Book 157, Lemma 4.1B.  Book 157, Proposition 4.1A proves that
this is an arithmetic twist of the same geometric neat-level scheme, defines its own
$\mathbf Q$-tensor component, and leaves product monodromy unchanged.  Every occurrence of
“corrected auxiliary source” below allows (1.4a) only when that refinement is explicitly
invoked.

### 1.3 What must be chosen

The construction has six ledgers. The residual ledger records oddness, absolute and cyclotomic
irreducibility, determinant, finite flatness, and an adjoint-twist invariant. The dihedral ledger
records a CM field, Hecke character, conductor, determinant, residual conjugate ratio, and local
behavior. The moduli ledger records polarization, neat level, two paired torsion systems,
components, and product monodromy. The local ledger records real, integral, ordinary,
nonordinary, and semistable seed points over the controlled rational completions. The field
ledger records the regular Galois top, total reality, complete splitting, and closure-level
disjointness. The lifting ledger records the actual auxiliary active set and one exact
finite-set certificate for the named point.

The order matters. A global point chosen before its component may have incompatible local
specializations. A field chosen before the cutout fields are listed may shrink a residual image.
Local characters chosen without the diagonal-unit condition may not globalize.

There is one application-specific precedence rule. If the target finite-flat module at
$\ell$ comes from a multiplicative Frey curve, first construct and fix the good ordinary
replacement $\mathcal B_\ell$ of Book 157, Proposition 8.4B, together with

$$
P_\ell(X)=X^2-a_\ell(\mathcal B_\ell)X+\ell,
\qquad
\Delta_\ell=a_\ell(\mathcal B_\ell)^2-4\ell.                 \tag{1.5}
$$

Only then choose $q$, imposing $q\nmid\Delta_\ell$, and only afterward prescribe the ordered
$q$-branches at $\ell$ by protected anti-cyclotomic correction. The multiplicative Tate
curve itself is not the characteristic-zero finite-flat seed, and a branch selected from its
semisimplification need not occur on any good replacement.

### 1.4 The logical boundary

This book does not assume a potential-modularity theorem. It also does not promote ordinary
arithmetic approximation to control of a normal closure. Closure control is used only after a
Galois approximation datum has been supplied.

There is already a pre-specialization ray boundary. Lemma 4.1 cancels the CM ray-unit
obstruction by inverse branch characters, but does not by itself settle every relative
ray-class or capitulation relation forced by the determinant restriction. Theorem 4.2 therefore
starts from a corrected relative ray datum whose full compatibility has been verified.  Lemma
4.1A verifies this extra relation when the base is $\mathbf Q$; it remains a hypothesis over a
general totally real base.

There is a further boundary at modularity lifting. Absolute irreducibility and matching residual
torsion do not make a lift automorphic. In the split FLT construction every dyadic place of the
Galois top lies in the auxiliary active set: complete splitting gives the same Tate neighborhood
on every sheet. Consequently no theorem in the FLT chain can use a hypothesis saying that
exactly one place is nonminimal. The relevant input is instead Book 176's direct
$({\rm IAV}_S)$ theorem, or one of its explicitly stronger finite-set substitutes, for the
actual post-specialization set $S=P_{\mathrm{aux}}(A_F)$.

This book therefore does not retain the retired one-special-factor moving problem, its
toroidal joining hypotheses, or the one-prime scalar-augmentation branch. Its sole lifting
boundary is the honest finite-set certificate of Section 2.4. This gap does not create a
separate curve-carrier gap: after automorphy, even absolute degree and any one special dyadic
place let Book 104 construct a compact one-split packet, and Book 127 attaches its rank-two
family.

## 2. Residual and coefficient data

### 2.1 The target representation

Let $\ell\geq7$ and let

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

be continuous. It is a **weight-two residual datum** when:

1. $K$ is totally real and is unramified at the places above $\ell$ where the unramified
   low-weight finite-flat theory is used;
2. $\bar\rho$ is absolutely irreducible and totally odd;
3. $\bar\rho|_{G_{K(\zeta_\ell)}}$ is absolutely irreducible;
4. after fixing the coefficient line,
   $$
   \det\bar\rho=\bar\epsilon_\ell;
   \tag{2.2}
   $$
5. every restriction at $w\mid\ell$ is finite flat of weights $\{0,1\}$ in the integral
   sense;
6. the adjoint-twist invariant required by the finite-set lifting datum vanishes:
   $$
   H^0(K,\operatorname{ad}^0\bar\rho(1))=0.
   \tag{2.3}
   $$

Condition 3 is stronger than absolute irreducibility over $K$. In dimension two and
characteristic at least seven it gives adequacy on the group used for auxiliary-prime selection.
Condition (2.3) is separate: adequacy is not a statement about this cyclotomic self-twist.

Finite flatness is an integral extension condition, not a synonym for two numerical weights.
At an ordinary place a model may split as a constant group and a multiplicative group; at a
local--local place it does not.

### 2.2 Determinant normalization

Suppose initially that

$$
\det\bar\rho=\bar\epsilon_\ell\bar\nu
$$

with $\bar\nu$ finite order. Total oddness gives $\bar\nu(c_v)=1$ at every real place. Passing
to the kernel field of $\bar\nu$ kills the extra factor, but that restriction may destroy
irreducibility or intersect a residual cutout field. It is harmless only after those facts are
checked. A scalar twist changes the determinant by a square, so it removes $\bar\nu$ only when
the required square root exists with the right local behavior.

The polarization supplies

$$
\det A[\mathfrak l]\simeq
(\mathfrak c^\vee\otimes k_{\mathfrak l})(1).
\tag{2.4}
$$

Identifying the constant line with $k$ turns (2.4) into (2.2). Thus determinant compatibility is
an existence condition for the paired frame cover, not a normalization imposed after a point is
found.

### 2.3 Simultaneous coefficient-field realization

The target field $k$ is only half of the coefficient problem. The Hecke character constructed
at $q$ has a number field of values, and extending its ray-class character can enlarge that
field. If $\mathfrak Q$ is a place of the final character field above $q$, write

$$
k_\psi=\mathcal O_{C_\psi}/\mathfrak Q.
\tag{2.5}
$$

The real-multiplication field must have one prime with residue field $k$ and another with
residue field $k_\psi$. Choosing it before $k_\psi$ exists is therefore logically backwards.
The following result is the simultaneous replacement for that premature choice.

**Theorem 2.1 (simultaneous real-multiplication coefficient realization).** Let $p$ and $s$ be
distinct odd rational primes, let $k_p/\mathbf F_p$ and $k_s/\mathbf F_s$ be finite fields, and
let $V_p$ and $V_s$ be rank-two residual systems with specified isomorphisms

$$
\det V_p\xrightarrow{\sim}k_p(1),
\qquad
\det V_s\xrightarrow{\sim}k_s(1).
\tag{2.6}
$$

There are a totally real field $E$, primes $\mathfrak p\mid p$ and $\mathfrak s\mid s$, and
residue-field isomorphisms

$$
\iota_p:k_{\mathfrak p}\xrightarrow{\sim}k_p,
\qquad
\iota_s:k_{\mathfrak s}\xrightarrow{\sim}k_s
\tag{2.7}
$$

with the following simultaneous properties.

1. The rational primes $p$ and $s$ are unramified in $E$.
2. For the Hilbert--Blumenthal tensor choice
   $$
   I=\mathcal O_E,
   \qquad
   \mathfrak c=\mathfrak d_E^{-1},
   \qquad
   \mathfrak c^\vee=\mathcal O_E,
   \qquad
   L=\mathcal O_E^2,
   \tag{2.8}
   $$
   and a neat level $N\geq3$ prime to $2ps$, use the corrected source
   $$
   \mathscr L_N^\natural
   =(\mathcal O_E/N\mathcal O_E)
    \oplus(\mathcal O_E/N\mathcal O_E)(1).
   \tag{2.8a}
   $$
   Both $\mathfrak p$ and $\mathfrak s$ are monodromy-admissible on the tensor component of
   $H^\natural$. Simultaneous monodromy there is the full product
   $$
   \operatorname{SL}_2(k_{\mathfrak p})\times
   \operatorname{SL}_2(k_{\mathfrak s}).
   $$
   In the rational-base refinement, if finitely many $\mathbf Q_v$-tensor seeds have already
   been selected, one may instead choose $E_*/\mathbf Q$ by Book 157, Lemma 4.1B and use the elliptic source
   $E_*[N]\otimes_{\mathbf Z/N\mathbf Z}\mathcal O_E/N\mathcal O_E$.  The resulting tensor
   component is still defined over $\mathbf Q$ and has the same displayed product monodromy.
3. Under (2.7) and the canonical generators of the two copies of
   $\mathfrak c^\vee\otimes k_{\mathfrak r}=k_{\mathfrak r}$, the maps (2.6) become specified
   determinant-line isomorphisms
   $$
   \det V_p\xrightarrow{\sim}
   (\mathfrak c^\vee\otimes k_{\mathfrak p})(1),
   \qquad
   \det V_s\xrightarrow{\sim}
   (\mathfrak c^\vee\otimes k_{\mathfrak s})(1).
   \tag{2.9}
   $$

**Proof strategy.** First prescribe the two residue fields by local factorization, use a third
prime to force global irreducibility, and impose total reality at the archimedean place. Then
use the canonical tensor component, whose congruence subgroup is visibly full at both selected
primes.

**Proof.** Write $[k_p:\mathbf F_p]=f$ and $[k_s:\mathbf F_s]=g$, and put
$d=\max(f,g)$. Choose squarefree monic polynomials of degree $d$ over $\mathbf F_p$ and
$\mathbf F_s$ having irreducible factors of degrees $f$ and $g$, respectively. Choose a third
rational prime $r\ne p,s$ and a monic irreducible polynomial of degree $d$ over $\mathbf F_r$.
Weak approximation in the $d$ nonleading coefficients gives a monic polynomial
$F(X)\in\mathbf Q[X]$ whose coefficients are integral at $p,s,r$, have the prescribed
reductions there, and are sufficiently close over $\mathbf R$ to those of a monic polynomial
with $d$ distinct real roots. No global integrality of those rational coefficients is being
asserted.

The reduction at $r$ makes $F$ irreducible over $\mathbf Q_r$, hence over $\mathbf Q$. The
archimedean open condition makes all its roots real. Squarefreeness at $p$ and $s$, Hensel
factorization, and the unramified local extension criterion show that
$E=\mathbf Q[X]/(F)$ is unramified at both primes and has primes with residue fields $k_p$ and
$k_s$. This proves (2.7) without requiring either residue field to contain the other.

For (2.8), the inverse-different formula gives $\mathfrak c^\vee=\mathcal O_E$, and the standard
alternating determinant form makes $L$ self-dual. Since $p$ and $s$ are unramified in $E$ and
$N$ is prime to them, neither prime divides the different, polarization line, lattice index, or
level. Book 157 proves that the corrected source (2.8a) becomes, after a geometric choice of a
primitive $N$th root, one fixed-pairing orientation of the principal level for $L$; it also
proves that the tensor component is defined over $\mathbf Q$. On that component the arithmetic
group contains the principal congruence subgroup $\Gamma(N)$. Chinese remaindering elementary
upper and lower unipotents modulo $N$, $\mathfrak p$, and $\mathfrak s$ proves surjectivity onto
the displayed product. Thus both primes are monodromy-admissible, with no exceptional set chosen
before them.  For the optional elliptic source, Book 157, Proposition 4.1A identifies the same
geometric congruence subgroup and Lemma 4.1B supplies the asserted simultaneous local matching;
only the arithmetic descent datum changes. Finally $\mathfrak c^\vee=\mathcal O_E$ identifies each polarization coefficient
line with its residue field; composing with (2.6)--(2.7) gives (2.9). $\square$

We will apply Theorem 2.1 with $p=\ell$, $k_p=k$, $s=q$, and $k_s=k_\psi$ only after the
dihedral character and its place $\mathfrak Q$ have been fixed. From that point onward the two
torsion groups $A[\mathfrak l]$ and $A[\mathfrak q]$ are two-dimensional over exactly the
residue fields of the target and the constructed dihedral representation.

### 2.4 The finite-set lifting interface

After Book 158 specializes the paired-frame space, let $F/K$ be its totally real Galois top,
let $A_F/F$ be the resulting Hilbert--Blumenthal abelian variety, and put

$$
r_A=V_{\mathfrak q}(A_F),\qquad
\bar r_A=A_F[\mathfrak q]\simeq\bar r|_{G_F}.
\tag{2.10}
$$

The **auxiliary active set** is the finite set

$$
P_{\mathrm{aux}}(A_F)=
\{w:r_A\text{ has more level than the selected residual automorphic reference at }w\}.
\tag{2.11}
$$

It is defined only after specialization and after the reference packet and all actual bad
places have been recorded. In the Frey split Tate construction,

$$
\{w:w\mid2\}\subseteq P_{\mathrm{aux}}(A_F).
\tag{2.12}
$$

Because $2$ splits completely in $F$ and $[F:\mathbf Q]\ge2$, this set is never a singleton.
Accidental semistable places and retained places above $3$ may enlarge it.

A **finite-set lifting certificate** for $(A_F,\bar r)$ means one of the exact interfaces of
Book 176, applied to the full set $S=P_{\mathrm{aux}}(A_F)$:

1. the direct $({\rm IAV}_S)$ comparison, with paired desired and avoidance local rings,
   common special fibers and component bijections, synchronized Taylor--Wiles systems,
   support transfer, and descent;
2. a fully reverified ordered chain which retains every previously changed local condition;
3. the all-point finite-set theorem with its mixed exactness, product-residue, joint-support,
   augmentation, and reciprocity hypotheses; or
4. the pointed theorem for this named lift, including its actual joint cube, simultaneous
   branch verification, reciprocity on the torsion-free top carrier, and occurrence of the
   one global product component through the point.

Separate one-place statements do not assemble into this certificate. Nor does complete
splitting reduce the problem: it is precisely what creates all of the active dyadic places.
The direct $({\rm IAV}_S)$ interface is the scope-minimal handoff used below. The other three
are retained only as logically stronger substitutes.

The construction ledger needed before this handoff consists of: the residual datum of Section
2.1; the auxiliary prime and compatible corrected relative ray datum of Chapters 3--4; the
simultaneous coefficient realization of Theorem 2.1; the determinant-compatible paired-frame
space and point-centered local opens of Books 156--158; and Book 158's split Galois-top
specialization with closure-level disjointness. None of these clauses asks for one exceptional
factor, a common moving presentation for mixed local algebras, or any of Book 157's Required
$({\rm IIT})$, $({\rm MPE})$, $({\rm ACE})$, $({\rm TCG})_\Sigma$,
$({\rm FTJ})$, or $({\rm ICS})$ statements.


## 3. Choosing the auxiliary prime

### 3.1 Why a second residue characteristic is useful

The auxiliary prime does three jobs. It supplies a residual representation whose automorphy is
constructed from a character, the coefficient characteristic for modularity lifting, and the
second factor in a connected two-prime frame cover. These jobs impose distinct exclusions.

In the multiplicative-Frey coefficient-prime case, this chapter is entered only after the
ordinary replacement $\mathcal B_\ell$ and $P_\ell$ of (1.5) have been fixed. Add the finite
exclusion $q\nmid\Delta_\ell$; then $P_\ell$ has two distinct roots modulo $q$, and their
chosen order is the good local $q$-branch which Lemma 4.3 must impose. If another fixed good
seed, for example at $3$, also participates in the paired frame, add the analogous nonzero
discriminant to the exclusion list before invoking Chebotarev.

Let $S(\bar\rho)$ be the finite set of rational residue characteristics below places where
$\bar\rho$ is ramified. We exclude $S(\bar\rho)$, the rational primes ramified in $K$, and
$2,3,5,\ell$. We also take

$$
q-1>(2[K:\mathbf Q])!.
\tag{3.1}
$$

If $M/K$ is quadratic, the degree of its normal closure over $\mathbf Q$ is at most
$(2[K:\mathbf Q])!$. Thus (3.1) prevents that normal closure from containing a nontrivial
$q$-power root of unity. This will make the CM-type ray-unit obstruction prime to $q$.

The field $E$ has deliberately not yet been chosen. After the Hecke character produces its
actual residue field at $q$, Theorem 2.1 will construct $E$ so that both $\ell$ and $q$ are
unramified and monodromy-admissible. There is therefore no circular attempt to avoid an
exceptional set belonging to a field not yet known.

**Lemma 3.1 (auxiliary-prime selection).** Given finitely many number fields, finite sets of
primes, and compatible Frobenius requirements in one finite Galois compositum, infinitely many
rational primes $q\geq7$ meet the requirements.

**Proof.** Remove the finitely many ramified and forbidden primes. A compatible tuple of class
requirements is one conjugacy class in the Galois group of the compositum. Primes with that
class have positive density. $\square$

Compatibility is essential. Classes prescribed independently in two fields with nontrivial
intersection need not lift to the compositum. We always form the compositum first.

### 3.2 Avoiding finitely many bad choices

Several later conditions also eliminate finitely many $q$. The finite-set lifting theorem requires
characteristic at least seven, the local bases must be unramified at $q$, and every finite field
used in a compatible Frobenius prescription contributes its ramified primes to the exclusion
list. Most importantly, $q\notin S(\bar\rho)$ is imposed before any local $q$-adic frame is
attempted.

Once $q$ is fixed, the protected conjugate-ratio character and every correction character are
chosen with order prime to $q$. Such roots of unity reduce injectively at every place above
$q$. The character-value field is allowed to enlarge during ray-class extension; its resulting
residue field is then received by $E$ through Theorem 2.1. This order removes the false choice
between coefficient enlargement and a previously fixed real-multiplication prime.

### 3.3 Two independent primes of the real-multiplication field

After the application of Theorem 2.1, the two frame groups are

$$
\operatorname{SL}_2(k_{\mathfrak l})
\quad\text{and}\quad
\operatorname{SL}_2(k_{\mathfrak q}).
$$

Surjectivity to both factors would not alone imply product monodromy: a graph subgroup can
project onto both. The simultaneous elementary-matrix argument in Theorem 2.1 gives the full
product at the two received prime ideals. This is why the two frames are placed on one
fiber-product cover.

The residue degrees may differ. If the finite fields happen to be isomorphic, the graph danger
is more visible, but the product theorem still rules it out. Distinct rational residue
characteristics are retained throughout.

### 3.4 Local coefficient-prime requirements

The lifting theorem at $q$ requires an unramified local base. We choose $q$ unramified in $K$
and, in the rational split application, require the simultaneous seed already over
$\mathbf Q_q$. Book 158 then makes $q$ split completely, so every top completion remains the
same unramified base.

There is a second, independent condition at the same places: $\bar\rho|_{G_{K_w}}$ must be
unramified. A good Hilbert--Blumenthal variety has unramified $\mathfrak l$-torsion at residue
characteristic $q\ne\ell$. If $\bar\rho$ had nontrivial inertia at $w$, no unramified extension
could make an exact good $\mathfrak l$-frame exist. Since $q\notin S(\bar\rho)$, the target is
unramified; the rational-base tensor source and chosen ordinary seed must realize its actual
Frobenius over $\mathbf Q_q$ itself.

At $\ell$, the target finite-flat module must be realized over $\mathbf Q_\ell$ by an ordinary
or local--local Hilbert--Blumenthal seed on the selected component. A seed known only after a
nontrivial local extension belongs to the nonsplit problem and is not an input to Theorem 8.2.

## 4. The dihedral seed

### 4.1 CM induction and parallel weight two

Let $M/K$ be CM quadratic, with nontrivial automorphism $\sigma$. Choose an algebraic Hecke
character $\psi$ of infinity type $(1,0)$ at every complex pair. Its automorphic induction

$$
\pi(\psi)=\operatorname{AI}_{M/K}(\psi)
\tag{4.1}
$$

has parallel weight two, and it is cuspidal exactly when $\psi\ne\psi^\sigma$. At a coefficient
place above $q$, its Galois representation is

$$
r_{\psi,q}=\operatorname{Ind}_{G_M}^{G_K}\chi_{\psi,q}.
\tag{4.2}
$$

At a good split prime its Frobenius roots are the two branch values. At a good inert prime its
trace is zero. At a regular nonsplit place its automorphic component is dihedral supercuspidal.
The monodromy operator is always zero, so the dihedral form supplies the residual avoidance
side at every place where the Tate-module point has special monodromy.

### 4.2 The determinant equation

The determinant is

$$
\det r_{\psi,q}
=\eta_{M/K}(\chi_{\psi,q}\circ\operatorname{Ver}),
\tag{4.3}
$$

corresponding on ideles to $\eta_{M/K}\psi|_{C_K}$. The desired equation is

$$
\eta_{M/K}\psi|_{C_K}=|\cdot|^{-1},
\tag{4.4}
$$

because arithmetic $|\cdot|^{-1}$ has $q$-adic avatar $\epsilon_q$. The quadratic factor cannot
be dropped: induction of the trivial character has determinant $\eta$. Nor can a later twist
always repair an error, since a twist from $K$ changes the determinant by a square.

### 4.3 Local ray data and global units

Prescribe finite-order local factors at a finite set containing the places above $q$, one
conjugate-ratio witness, and any desired conductor primes. A global character exists only if
the product of the local characters and infinity type is trivial on the diagonal ray-unit
subgroup. The determinant equation imposes a second restriction on the diagonal copy of $C_K$.
They must agree on the intersection.

To make the obstruction explicit, take a $\sigma$-stable modulus $\mathfrak m$ containing the
initial conductors and put

$$
U_{\mathfrak m}
=\{u\in\mathcal O_M^\times:u\equiv1\pmod{\mathfrak m}\}.
\tag{4.5}
$$

The infinity rule and the prescribed local factors define a finite character

$$
\omega_{\mathfrak m}:U_{\mathfrak m}\longrightarrow\boldsymbol\mu_\infty.
\tag{4.6}
$$

For the local and infinity rule alone, globalization is equivalent to killing
$\omega_{\mathfrak m}$. Compatibility with (4.4) says that it is trivial on
$U_{\mathfrak m}\cap K^\times$. The anti-unit map
$u\mapsto u/u^\sigma$ therefore makes it factor through a subgroup of
$\boldsymbol\mu(M)$, as proved in Lemma 4.1. Condition (3.1) makes this finite group prime to
$q$, and all initially prescribed finite factors are also chosen of order prime to $q$.
Hence $\omega_{\mathfrak m}$ has order prime to $q$.

There is also a relative ray-class intersection to retain. Let $R$ be the subgroup of the ray
ideal group generated by the prescribed principal rule, the diagonal image from $K$, and the
prescribed local unit quotients. A **corrected relative ray datum** is called compatible only
when its proposed values agree on every intersection of these subgroups and hence define a
character of $R$. Triviality on diagonal ray units is the unit part of this check; it does not
by itself settle a possible capitulation relation between a $K$-ideal and a principal
$M$-ideal. Theorem 4.2 retains this full compatibility after the inverse-branch correction
rather than inferring it from the unit calculation; Lemma 4.1A proves it when $K=\mathbf Q$.

### 4.4 The inverse-branch ray-class lemma

The phrase “add split auxiliary primes” is not a proof: the local characters at those primes
must be produced and must not erase the already chosen irreducibility detector.

**Lemma 4.1 (prime-to-$q$ inverse-branch correction).** Let $K$ be totally real, let $M/K$ be
CM quadratic with involution $\sigma$, let $q$ be odd, and let $\mathfrak m$ be a
$\sigma$-stable modulus prime to $q$. Let

$$
\omega:U_{\mathfrak m}\longrightarrow\boldsymbol\mu_n,
\qquad (n,q)=1,
\tag{4.7}
$$

be trivial on $U_{\mathfrak m}\cap K^\times$. Fix a finite protected set of local characters
away from $q$. Then there are finitely many new places $v_i$ of $K$, disjoint from the protected
set and split as $v_i=\mathfrak u_i\mathfrak u_i^\sigma$ in $M$, and characters of order prime
to $q$ (write $\boldsymbol\mu_{q'}$ for all roots of unity of order prime to $q$)

$$
\xi_i:k_{\mathfrak u_i}^\times\longrightarrow
\boldsymbol\mu_{q'},
\tag{4.8}
$$

such that the local character at $\mathfrak u_i^\sigma$ is
$\xi_i^{-1}\circ\sigma^{-1}$ and

$$
\prod_i
\xi_i(u\bmod\mathfrak u_i)
\xi_i^{-1}(u\bmod\mathfrak u_i^\sigma)
=\omega(u)^{-1}
\qquad(u\in U_{\mathfrak m}).
\tag{4.9}
$$

Every pair is trivial on the diagonal copy of $K_{v_i}^\times$, so it preserves (4.4). The
protected local characters remain unchanged.

**Proof strategy.** Pass from a unit to its anti-invariant ratio $u/u^\sigma$. In a CM
extension that ratio is a root of unity, so one split residue group detects the entire finite
quotient. Extend its character to the ambient cyclic residue group.

**Proof.** The map

$$
\Delta:U_{\mathfrak m}\longrightarrow M^\times,
\qquad u\longmapsto u/u^\sigma
\tag{4.10}
$$

has kernel $U_{\mathfrak m}\cap K^\times$. Thus $\omega$ descends to a character
$\widetilde\omega$ of $D=\Delta(U_{\mathfrak m})$. Every conjugate of $u/u^\sigma$ has
absolute value one. It is an algebraic integer and a unit, so Kronecker's theorem makes it a
root of unity. Hence $D$ is a finite subgroup of $\boldsymbol\mu(M)$.

Choose a place $v$ of $K$, outside the modulus and every protected place, which splits as
$v=\mathfrak u\mathfrak u^\sigma$ in $M$ and whose residue characteristic does not divide
$|\boldsymbol\mu(M)|$. Chebotarev gives infinitely many such places. Reduction at
$\mathfrak u$ is injective on $D$: a root of unity of order prime to the residue characteristic
retains its order. Transport $\widetilde\omega^{-1}$ to the image of $D$ in
$k_{\mathfrak u}^\times$. The latter group is cyclic. A character of one of its subgroups
extends to all of $k_{\mathfrak u}^\times$ because roots may be chosen successively in
$\boldsymbol\mu_\infty$. More explicitly, split the cyclic residue group into its $q$-primary
and prime-to-$q$ factors. The transported character kills the intersection with the first
factor, because its image has order prime to $q$; extend it on the second factor and take the
trivial character on the first. The resulting extension has order prime to $q$. Call it $\xi$
and put the inverse conjugate character on $\mathfrak u^\sigma$.

Under the identification of the two residue fields induced by $\sigma$, the value of this
inverse pair on $u$ is

$$
\xi\bigl((u/u^\sigma)\bmod\mathfrak u\bigr).
$$

It equals $\widetilde\omega(\Delta u)^{-1}=\omega(u)^{-1}$, proving (4.9) with one pair.
For $u\in K_v^\times$ the two branch values are equal and inverse, so their product is one.
The new place avoids the protected set, which proves the last assertion. $\square$

After (4.9), the infinity rule and all local factors are trivial on ray units. If the corrected
values also satisfy the full relative compatibility of Section 4.3, they define a character on
$R$. The finite ray-class extension argument then extends it to the full ideal group, possibly
adjoining roots of relations and thereby enlarging the character-value field. This enlargement
is retained; it is exactly why $E$ was not chosen in Chapter 2 before the character existed.
The field $C_\psi$ itself is not claimed to be unramified at $q$: a ray-class relation may
require a root of $q$-power order. Such an extra finite factor is trivial on the protected local
unit subgroups and does not alter their inertial characters, while every protected
prime-to-$q$ value still reduces injectively. Theorem 2.1 constructs the separate, unramified
real-multiplication field from the actual residue field left after this extension.

Over the rational base the remaining relative compatibility is automatic.  This special case
is recorded here because later Frey constructions need to prescribe additional split local
branch factors before the character is globalized.

**Lemma 4.1A (rational-base relative-ray compatibility).**  Take $K=\mathbf Q$ and write
$M/\mathbf Q$ for the CM quadratic field.  Include the conductor of $\eta_{M/\mathbf Q}$ and
the real sign in the modulus, and prescribe determinant-compatible branch pairs.  Then the
inverse-branch correction of Lemma 4.1 is compatible on the full subgroup $R$ of Section 4.3.

**Proof.**  The diagonal fractional-ideal group of $\mathbf Q$ is principal.  If a diagonal
ideal becomes equal to a ray-principal $M$-ideal, two generators differ by a global unit.
Equivalently, the diagonal idele map $C_{\mathbf Q}\to C_M$ is injective: if a rational idele
is represented by $a\in M^\times$, conjugation gives $a=a^\sigma$, hence
$a\in\mathbf Q^\times$.  Changing an ideal generator changes the relation by a ray unit.

The corrected principal and local rules agree on ray units by Lemma 4.1.  On rational
principal ideles they agree with the diagonal determinant rule because the modulus contains the
quadratic conductor and the real sign resolves the only rational-unit ambiguity.  Each inverse
branch pair is trivial on the diagonal $\mathbf Q_v^\times$, so the correction preserves this
agreement.  The ray exact sequence shows that these exhaust the relations between the
principal, diagonal, and local-unit subgroups.  Thus the proposed values define a character of
$R$. $\square$

### 4.5 Residual irreducibility and cyclotomic irreducibility

For a coefficient prime $\mathfrak Q\mid q$, put

$$
\bar r=\operatorname{Ind}_{G_M}^{G_K}\bar\chi_{\psi,\mathfrak Q}.
\tag{4.11}
$$

Then

$$
\bar r\text{ is absolutely irreducible}
\quad\Longleftrightarrow\quad
\bar\chi_{\psi,\mathfrak Q}\ne
\bar\chi_{\psi,\mathfrak Q}^{\sigma}.
\tag{4.12}
$$

Choose a Frobenius or inertia element witnessing the inequality with a value of order prime to
$q$. For the cyclotomic restriction one needs the stronger condition that the conjugate ratio
remain nontrivial on $G_{M K(\zeta_q)}$. Merely requiring $M$ not to be the quadratic subfield of
$K(\zeta_q)$ is insufficient: the characters might still agree on the intersection subgroup.

At $q\geq7$, cyclotomic absolute irreducibility gives adequacy. A small dihedral image causes no
problem if it is absolutely irreducible: its projective order is prime to $q$, so averaging and
semisimple spanning apply.

Choose an integer $m>2$ prime to $q$. Chebotarev supplies a place $z$ outside every protected
set which splits completely in the Galois closure of $M(\boldsymbol\mu_m)/K$; write
$z=\mathfrak z\mathfrak z^\sigma$ in $M$. Then $m$ divides
$|k_{\mathfrak z}^{\times}|$, so there is a branch character of exact order $m$. Put that
character and its inverse conjugate on the two branches. On a suitable inertia element their
conjugate ratio is the square of a value of order $m$, chosen nontrivial.
The mod-$q$ cyclotomic character is unramified at $z$, so that inertia element already lies in
$G_{M K(\zeta_q)}$. Prime-to-$q$ roots of unity retain their order on reduction, and Lemma 4.1
does not change the protected local pair. This single protected inertia element therefore
witnesses both (4.12) and cyclotomic absolute irreducibility after the global extension step.

### 4.6 Finite flatness at the auxiliary prime

Require every $w\mid q$ to split in $M$. The local unit data force the two characters, after
the algebraic correction, to have the form

$$
\theta_w\quad\text{and}\quad\epsilon_q\theta_w^{-1},
\tag{4.13}
$$

where $\theta_w$ is finite order and unramified. The ray-class extension step can change a
uniformizer value, so the proof does not silently replace $\theta_w$ by $1$.  Lemma 4.3 below
uses a separate protected anti-cyclotomic Grunwald twist when an application needs specified
residual uniformizer values at split places.  After a finite
unramified extension killing its reduction, the residual local module is the generic fiber of

$$
(\mathbf Z/q\mathbf Z)\oplus\boldsymbol\mu_q
\tag{4.14}
$$

after coefficient extension. Before that extension it is the direct sum of an unramified twist
of the constant factor and an unramified twist of the multiplicative factor, which is still
ordinary finite flat. It has determinant $\bar\epsilon_q$ and admits compatible finite-flat
quotients at every power of the coefficient uniformizer. A nonordinary local--local
choice is possible only with a separately supplied Hilbert--Blumenthal seed and integral
quotient system.

### 4.7 The controlled dihedral-seed theorem

First choose the quadratic field. Given finitely many desired local quadratic algebras, weak
approximation on squareclasses produces a CM quadratic extension $M/K$ which is split above
$q$ and has those localizations: take a square locally at $q$, a negative element at every real
place, and the prescribed squareclass at the remaining controlled places, inserting one
auxiliary nonsquare place if necessary. At dyadic places the squareclass itself must be
prescribed. This elementary choice of $M$ does not verify the subsequent relative ray-class
compatibility.

**Theorem 4.2 (controlled dihedral seed from compatible ray data).** Let $K$ be totally real,
let $q\geq7$ satisfy the exclusions of Chapter 3, retain the target $\bar\rho$ of Chapter 2,
and fix a CM quadratic extension $M/K$ as above. Fix a $\sigma$-stable modulus, parallel type
$(1,0)$, the unramified ordinary branch data (4.13) above $q$, finitely many protected
prime-to-$q$ local ray factors including the conjugate-ratio witness of Section 4.5, and
determinant rule (4.4). Assume that the resulting unit obstruction is trivial on $K$-units and
has order prime to $q$. Assume moreover that one inverse-branch correction furnished by Lemma
4.1 has been fixed for which the corrected relative ray datum is fully compatible in the sense
of Section 4.3. Then there exist an algebraic Hecke character $\psi$, a
character-value field $C_\psi$, and a place $\mathfrak Q\mid q$ of $C_\psi$ such that:

1. $\psi$ has parallel type $(1,0)$ and satisfies (4.4);
2. $\pi(\psi)$ is cuspidal of parallel weight two;
3. $\bar r$ is absolutely irreducible, totally odd, and ordinary finite flat at $q$;
4. $\bar r|_{G_{K(\zeta_q)}}$ is absolutely irreducible;
5. $H^0(K,\operatorname{ad}^0\bar r(1))=0$;
6. every prescribed prime-to-$q$ inertial distinction survives reduction.

**Proof.** Fix an embedding $\overline{\mathbf Q}\hookrightarrow\overline{\mathbf Q}_q$; the
place $\mathfrak Q$ below will be the one it induces on the character-value field. Use the
protected inverse-branch inertia witness already included in the datum. By hypothesis the
complete unit obstruction is trivial on the $K$-units and has order prime to $q$; equivalently
it factors through the prime-to-$q$ anti-unit group
$\Delta(U_{\mathfrak m})\subset\boldsymbol\mu(M)$ of Lemma 4.1. Use the fixed inverse branch
characters furnished there; they cancel the obstruction without changing either the determinant
or the protected witness.

Let $R$ be the subgroup of the ray ideal group from Section 4.3. The full compatibility
hypothesis says that the corrected proposed values define a character of $R$; equation (4.9)
is precisely its ray-unit relation and the inverse pairs are trivial on the diagonal copy from
$K$. Since the ray class quotient is finite abelian, the character extends to the full ray
ideal group after the coefficient field is enlarged to contain roots required by its relations.
Let $C_\psi$ contain all resulting values, choose $\mathfrak Q\mid q$, and let $\psi$ be the
associated idele class character.

Noninvariance gives cuspidality and (4.12); the protected inertia witness gives cyclotomic
irreducibility.
Formula (4.3) gives the determinant. A complex conjugation exchanges the induced lines, so its
trace is zero and determinant $-1$. The local model (4.14) proves finite flatness. Finally, a
nonzero element of $H^0(K,\operatorname{ad}^0\bar r(1))$ would, by absolute irreducibility,
give an isomorphism $\bar r\simeq\bar r(1)$. Taking determinants would force
$\bar\epsilon_q^2=1$ on $G_K$. Since $q$ is unramified in $K$, one has
$K\cap\mathbf Q(\zeta_q)=\mathbf Q$, so $\bar\epsilon_q(G_K)=\mathbf F_q^\times$; this is
impossible for $q\geq7$. $\square$

### 4.8 Protected Frobenius correction

The extension step in Theorem 4.2 does not by itself control unramified uniformizer values.
They can nevertheless be corrected *after* that step without changing the determinant.  The
extra input is the exact Grunwald--Wang alternative of Book 6, not smoothness of a moduli
space.

**Lemma 4.3 (protected anti-cyclotomic Grunwald correction).**  Fix the embedding
$\overline{\mathbf Q}\hookrightarrow\overline{\mathbf Q}_q$.  Let $M/K$ be quadratic with
involution $\sigma$, let $P$ be a finite $\sigma$-stable set of places of $M$, and let $S$ be
a finite set of finite places of $K$, disjoint from the places below $P$ and from those above
$q$, which split in $M$.  For each $v\in S$ choose one branch $w\mid v$ and a finite local
character

$$
\bar\delta_v:G_{K_v}\longrightarrow\overline{\mathbf F}_q^\times.
\tag{4.16}
$$

There is a finite-order Hecke character $\nu$ of $M$, of order prime to $q$, such that

$$
\nu|_{C_K}=1,
\qquad
\bar\nu_w=\bar\delta_v,
\qquad
\bar\nu_{w^\sigma}=\bar\delta_v^{-1},
\qquad
\nu_u=1\quad(u\in P).
\tag{4.17}
$$

Here the two split completions are identified with $K_v$, bars mean reduction through the
fixed $q$-adic embedding, and the inverse character on the conjugate branch is transported by
$\sigma$.  No restriction is asserted on the finite set of new ramified places outside
$P\cup\{w,w^\sigma:v\in S\}$.

**Proof.**  Every value in (4.16) has order prime to $q$.  Lift it through the Teichmuller map
to a complex root of unity using the fixed embeddings, and call the resulting local character
$\delta_v:K_v^\times\to\boldsymbol\mu_{q'}$.  Let $n$ be the least common multiple of the
orders of these characters.  If $n=1$, take $\nu=1$.  Otherwise prescribe a local character
$\theta_w=\delta_v$ and $\theta_{w^\sigma}=1$ at the two branches over each $v\in S$, and
prescribe $\theta_u=1$ at every $u\in P$.  Include conjugates of all these places in the local
set.

Book 6, Section 6.2's exact Grunwald--Wang alternative, applied over $M$, globalizes these full
local characters to a finite-order global character $\theta$.  In the Wang-special case it
may replace exponent $n$ by $2n$, but it preserves the prescribed local characters.  Since
$q$ is odd and $(n,q)=1$, the order of $\theta$ is still prime to $q$.  Through global class
field theory regard $\theta$ as a finite-order Hecke character and put

$$
\nu=\theta/\theta^\sigma.
\tag{4.18}
$$

On the diagonal image of $C_K$, conjugation is the identity, so the two factors in (4.18) are
equal and $\nu|_{C_K}=1$.  At $w$ the conjugate factor is the prescribed trivial character at
$w^\sigma$, whereas at $w^\sigma$ the quotient is the inverse transported character.  Both
factors are trivial at $P$, which proves all of (4.17).  The order of $\nu$ divides that of a
product of two prime-to-$q$ characters, so it is prime to $q$ and reduction preserves the
specified values. $\square$

Apply the lemma to the character $\psi_0$ produced by Theorem 4.2.  At a split place $v$, let
$(\bar\alpha_v,\bar\beta_v)$ be any desired pair of residual branch characters whose product
equals the determinant of $\bar r_0|_{G_{K_v}}$.  After labeling the two branches, put

$$
\bar\delta_v=\bar\alpha_v/\bar\chi_{0,w}.
\tag{4.19}
$$

Equality of the two determinants says that the required correction on $w^\sigma$ is exactly
$\bar\delta_v^{-1}$.  Put in $P$ every auxiliary-prime place, the protected
conjugate-ratio witness, and every previously protected local factor away from $S$.  Replacing
$\psi_0$ by

$$
\psi=\psi_0\nu
\tag{4.20}
$$

therefore realizes the exact residual branch pairs at all $v\in S$.  Because
$\nu|_{C_K}=1$, equation (4.4), the infinity type, and the induction determinant are unchanged.
Because $\nu$ is exactly trivial at $P$, ordinary finite flatness at $q$, the protected
inertial distinctions, and the cyclotomic-irreducibility witness are unchanged.  The proof of
the adjoint-twist vanishing in Theorem 4.2 depends only on absolute irreducibility and the
cyclotomic determinant, so it applies to the corrected representation as well.  The finitely
many new ramified places of $\nu$ are listed in the later local and avoidance ledgers.

Enlarge $C_\psi$ to contain the values of the corrected character (4.20), retain the place
induced by the fixed embedding, and put $k_\psi=\mathcal O_{C_\psi}/\mathfrak Q$. Apply
Theorem 2.1 to
$\bar\rho$ over $k$ and $\bar r$ over $k_\psi$. Only now fix the resulting field $E$, primes
$\mathfrak l,\mathfrak q$, Hilbert--Blumenthal tensor datum, and determinant-line orientations. Under the
residue isomorphism $k_{\mathfrak q}\simeq k_\psi$, the second prescribed local system is
literally the constructed $\bar r$, not an unrecorded scalar extension of it.

One can see the irreducibility calculation directly. Choose $s\in G_K\setminus G_M$. In the
coset basis,

$$
\bar r(h)=
\begin{pmatrix}
\bar\chi(h)&0\\0&\bar\chi^\sigma(h)
\end{pmatrix},
\qquad
\bar r(s)=
\begin{pmatrix}0&\bar\chi(s^2)\\1&0\end{pmatrix}.
\tag{4.15}
$$

If the two diagonal characters differ, their only common eigenlines are the coordinate lines,
and $s$ exchanges them. If they agree, the second matrix diagonalizes after scalar extension.
The same matrices give

$$
\det\bar r(h)=\bar\chi(h)\bar\chi^\sigma(h),
\qquad
\det\bar r(s)=-\bar\chi(s^2),
$$

which is precisely the quadratic transfer formula (4.3). Thus irreducibility, oddness, and the
determinant sign are checked in one fixed normalization.

All full and projective cutout fields, the cyclotomic field, and the ray fields used here are
finite. We record their compositum in the later avoidance field. The theorem does not assert
that these fields are mutually disjoint.

## 5. Protected local branches on the split route

### 5.1 Branch data at the controlled places

The split construction needs no auxiliary level-raising prime. The dihedral member is already
automorphic by induction, and Book 176 compares it with the actual Tate-module point at the
whole active set. What must be fixed before specialization is instead the local paired-frame
datum at each controlled rational place.

At $2$, choose the Frey Tate neighborhood for the target frame and use Lemma 4.3 to impose the
determinant-compatible residual dihedral branch on the same split Tate point. At $\ell$, first
fix the good ordinary replacement when the target residual module came from a multiplicative
curve, then choose $q\nmid\Delta_\ell$ and impose one of the two ordered roots of its
Frobenius polynomial as the protected $q$-branch. Treat a fixed good seed at $3$ in the same
order. At $q$, use the unramified ordinary frame of Section 4.6. Every auxiliary correction is
chosen after the seed whose Frobenius it must match.

These are finitely many split local prescriptions with common determinants, so the protected
anti-cyclotomic correction of Lemma 4.3 realizes them simultaneously without changing the CM
determinant or conjugate-ratio witness. They are input to Book 158's simultaneous point-centered
opens. No scalar repeated-root congruence, enhanced one-prime line, unique exceptional sheet,
or toroidal connecting slice is used.


## 6. The twisted Hilbert--Blumenthal cover

### 6.1 The moduli datum

Use the field and tensor datum supplied by Theorem 2.1. Thus

$$
I=\mathcal O_E,
\qquad
\mathfrak c=\mathfrak d_E^{-1},
\qquad
\mathfrak c^\vee=\mathfrak d_E^{-1}\mathfrak c^{-1}=\mathcal O_E,
\qquad
L=\mathcal O_E^2.
\tag{6.0}
$$

Take either the corrected auxiliary source $\mathscr L_N^\natural$ of (1.4) or the
elliptic-source replacement permitted by Theorem 2.1, with $N\geq3$ prime to $2\ell q$.
Write $H^{\mathrm{aux}}$ for the chosen version. Put into $\Sigma$
every rational prime dividing the discriminant of $E$, the numerator or denominator of
$\mathfrak c$, the level, a self-duality index, or a component-lattice denominator. Theorem 2.1
and the standard tensor component ensure that $\ell$ and $q$ lie outside $\Sigma$ and that the
two selected prime ideals have full product monodromy. This is a conclusion of the simultaneous
choice, not a later genericity assumption.

The resulting determinant-condition, $\mathfrak c$-polarized functor is a corrected fine
scheme of relative dimension $[E:\mathbf Q]$. Book 157 proves that its tensor
component $H^{\mathrm{ten}}$ is defined over $\mathbf Q$, contains every tensor seed used
below, and has the product monodromy of Theorem 2.1. Fine level is essential: without it the
natural object has stabilizers, and a universal abelian scheme need not exist on a coarse
space.

### 6.2 The two prescribed torsion systems

On a connected characteristic-zero base, let

$$
V_{\mathfrak l}=\bar\rho,
\qquad
V_{\mathfrak q}=\bar r,
$$

after identifying their coefficient fields with $k_{\mathfrak l}$ and
$k_{\mathfrak q}$. Choose determinant isomorphisms

$$
\det V_{\mathfrak l}\simeq
(\mathfrak c^\vee\otimes k_{\mathfrak l})(1),
\qquad
\det V_{\mathfrak q}\simeq
(\mathfrak c^\vee\otimes k_{\mathfrak q})(1).
\tag{6.1}
$$

The twisted frame cover $Y^{\mathrm{ten}}\to H^{\mathrm{ten}}$ represents tuples

$$
(A,\iota,\lambda,\eta_N,
\alpha_{\mathfrak l},\alpha_{\mathfrak q})
$$

with pairing-preserving equivariant isomorphisms

$$
\alpha_{\mathfrak l}:V_{\mathfrak l}\xrightarrow{\sim}A[\mathfrak l],
\qquad
\alpha_{\mathfrak q}:V_{\mathfrak q}\xrightarrow{\sim}A[\mathfrak q].
\tag{6.2}
$$

It is finite étale in characteristic zero. Geometrically it is a torsor under

$$
\operatorname{SL}_2(k_{\mathfrak l})
\times\operatorname{SL}_2(k_{\mathfrak q}).
\tag{6.3}
$$

The frames in (6.2) identify the representations themselves, not only their
semisimplifications. This distinction matters when the target is a nonsplit residual extension.

### 6.3 Why determinants are an existence condition

For two symplectic two-dimensional spaces over a finite field, an arbitrary linear isomorphism
need not preserve the alternating form. Its multiplier is its determinant. Consequently the
paired isomorphism scheme is nonempty exactly when the determinant lines have already been
identified. If (6.1) fails, forgetting pairings may produce an unpaired frame, but it does not
produce a point of $Y^{\mathrm{ten}}$.

The inverse different in $\mathfrak c^\vee$ is also genuine. The polarization pairing is
$\mathcal O_E$-balanced and becomes scalar-valued only after the trace-dual identification.
Replacing $\mathfrak c^\vee$ by $\mathfrak c^{-1}$ changes the integral pairing and can make a
supposed frame cover empty.

### 6.4 Geometric monodromy and connectedness

On $H^{\mathrm{ten}}$, simultaneous reduction of the arithmetic group at $\mathfrak l$ and
$\mathfrak q$ is the product (6.3), by Theorem 2.1 and the corrected-level comparison of
Book 157. Therefore the standard two-prime cover acts transitively on its fiber and is
geometrically connected.

The arithmetic twist by $V_{\mathfrak l}\times V_{\mathfrak q}$ becomes standard after base
change to an algebraic closure. It has the same geometric monodromy and is geometrically
connected. It is defined over $K$ because both residual systems and the tensor component are;
twisting does not provide a rational point.

### 6.5 Arithmetic components

Geometric components of a general Hilbert moduli space are indexed by determinant classes in a
narrow adelic quotient, and a constant oriented auxiliary level can even remove all real
points. Those variants are not needed here. The tensor choice (6.0) and either corrected source
allowed in Section 6.1 select a $\mathbf Q$-defined component $H^{\mathrm{ten}}$, and Book 157 puts every
real, good, ordinary, local--local, and semistable tensor seed used below on it. What remains is
to keep all local neighborhoods on its one twist $Y^{\mathrm{ten}}$.

**Proposition 6.1 (tensor-component ledger).** The twist $Y^{\mathrm{ten}}$ is smooth and
geometrically connected over $K$. Every sufficiently small local neighborhood of one of its
points remains on this same arithmetic component.

**Proof.** Smoothness follows from the corrected determinant-condition moduli theorem and
finite étaleness of the frame cover. Product monodromy makes the geometric cover over
$H^{\mathrm{ten}}$ connected. The twist is geometrically isomorphic to that cover, hence is
geometrically connected. The tensor component is open and closed and defined over $\mathbf Q$,
so a local neighborhood cannot cross it after shrinking. $\square$

The monodromy step deserves a precise reading. Choose a geometric base point on
$H^{\mathrm{ten}}$. The two torsion sheaves identify the geometric fiber of the standard cover with

$$
\operatorname{Isom}^{\mathrm{pair}}(k_{\mathfrak l}^2,A[\mathfrak l])
\times
\operatorname{Isom}^{\mathrm{pair}}(k_{\mathfrak q}^2,A[\mathfrak q]).
$$

The geometric fundamental group acts through simultaneous reduction of the Hilbert arithmetic
group. Surjectivity onto the product in (6.3) makes this action simply transitive, so the cover
has one geometric component. Replacing the constant frames by $V_{\mathfrak l}$ and
$V_{\mathfrak q}$ changes the descent cocycle but not the geometric action. This proves exactly
geometric connectedness; it does not supply a $K$-point.

Proposition 6.1 does not manufacture local points. Their simultaneous existence on
$Y^{\mathrm{ten}}$ is the subject of Chapter 7.

## 7. Local points on one component

### 7.1 Real places

At a real place, Book 157's corrected level has a tensor point; the constant oriented level
discarded in Section 6.5 need not have any real point. Complex conjugation acts on the torsion
of a polarized weight-two object with eigenvalues $1$ and $-1$. Both $\bar\rho$ and $\bar r$
are odd, so each has determinant $-1$.
A real Hilbert--Blumenthal tensor point has the same paired involution. An isomorphism between the $+1$ lines,
followed by the uniquely normalized isomorphism between the $-1$ lines, gives each paired frame.

Thus oddness is exactly the real frame criterion. It is not enough to construct a point at one
real place: every real place of the base enters the local ledger. Small neighborhoods preserve
the real component and the signs. Later a split real completion algebra will force every
embedding of the split top $F$ to remain real.

### 7.2 The target coefficient prime

Let $w\mid\ell$. The target module is finite flat of weights $\{0,1\}$. If it is ordinary, use
an ordinary Hilbert--Blumenthal seed over the stated completion whose connected--étale torsion
has the same paired generic representation. If it is nonordinary, use a local--local
Hilbert--Blumenthal seed, such as a supersingular tensor seed on a tensor-admissible component.

The ordinary locus is open by nonvanishing of the Hasse invariants. Nonordinarity is closed in
the special fiber, so its openness in the local field is obtained differently: fix the entire
special point and take its residue tube. Every point in that open tube has the same nonordinary
reduction. In either case, the generic frame is locally constant because its isomorphism scheme
is finite étale.

If the proposed finite-flat module is not realized by a Hilbert--Blumenthal seed of the selected polarization
type, finite flatness alone does not create a point. Existence over the stated completion is an
explicit hypothesis of the split local package.

There is a sharper boundary when the target module is the finite-flat residual torsion of a
Tate curve at $\ell$.  Book 157, Proposition 8.4A shows that its selected model is ordinary,
so a local--local seed cannot realize it, and that the multiplicative Tate curve does not give
a finite-flat characteristic-zero tower.  The split application must first construct a good
ordinary seed over the stated base completion.  The auxiliary
branch at that same place should then be prescribed to equal the prime-to-$\ell$ torsion of
this seed.  Lemma 4.3 permits exactly that determinant-compatible correction at a split place.
A branch pair fixed earlier from the multiplicative Tate semisimplification need not have the
good seed's Frobenius polynomial.  Thus the order

$$
\text{one-prime good seed and }P_\ell\quad\longrightarrow\quad
q\nmid\Delta_\ell\quad\longrightarrow\quad
\text{protected auxiliary branch correction}\quad\longrightarrow\quad
\text{two-frame point}                                      \tag{7.1a}
$$

is load-bearing. Book 157, Proposition 8.4B supplies the first arrow over the rational
completion in the FLT range.

### 7.3 The auxiliary coefficient prime

At $q$, the split local datum must already be defined over $\mathbf Q_q$. The prime-selection
step makes the target frame unramified there, and the dihedral construction supplies the exact
ordinary finite-flat auxiliary frame. Choose the rational-base tensor seed permitted by Book
157, Lemma 4.1B so that both frames, the determinant lines, and the ordinary
characteristic-zero lift occur on one point over $\mathbf Q_q$. Book 157's local openness then
gives a nonempty point-centered ordinary tube.

The base is unramified at $q$, as required by the weight-two finite-flat lifting condition. A
frame obtained only after a nontrivial unramified extension would solve a different exact-local-
algebra problem and would not be compatible with Book 158's complete splitting at $q$.


### 7.4 Ramification of the dihedral seed

At a finite place where the CM field or Hecke character is ramified, the split local package
must contain a good or semistable Hilbert--Blumenthal seed over the original rational
completion whose $\mathfrak q$-torsion realizes that exact residual inertia and whose
$\mathfrak l$-torsion realizes the target frame. The conductor of the dihedral character is
chosen with these seeds in view, and Lemma 4.3 adjusts only the protected split branches.

A seed available only after a nontrivial local extension does not suffice: Book 158 later makes
the controlled place split completely. If no simultaneous seed exists over the base
completion, the split theorem is inapplicable rather than repaired by inserting a nonsplit
completion algebra.

The local seed records the desired component but does not prove automorphy of the specialized
$q$-adic point. That is the role of the finite-set certificate.


### 7.5 The split special places

At the dyadic controlled place, choose the split semistable tensor Tate point used by Book 158.
Its $q$-adic Tate module has rank-one monodromy and conductor one, whereas its residual
$q$-torsion is the protected unramified branch fixed in Chapter 5. Choose the Tate parameter to
be an $\ell qN$th power with positive valuation, so both residual torsion frames and the
corrected neat level occur on the same point. Pairing fixes the determinant.

The local datum is a point-centered open, not a degree-indexed factorization with one exceptional
sheet. Book 158 specializes with $2$ completely split in its Galois top. Hence the same Tate
open occurs at every $w\mid2$, and every such $w$ belongs to the post-specialization active set.
Semistability, toric rank, the frames, and the Kummer shell persist after shrinking.

### 7.6 Good and semistable auxiliary conditions

At any other controlled place, use the good, ordinary, nonordinary finite-flat, or semistable
point prescribed in Chapter 5 and Book 158. Each condition is imposed on every sheet above the
place. Exact valuations and nonsplitness require the stated local model, while good reduction,
ordinary type, semistability, frames, and components persist on the point-centered open.


### 7.7 The simultaneous local-neighborhood lemma

**Theorem 7.1 (one-component split local package).** Let
$Z\subsetneq Y^{\mathrm{ten}}$ be closed. For every controlled place $v$ of the rational
base, suppose there is a point

$$
y_v\in(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_v)
$$

carrying the assigned real, good, ordinary, nonordinary finite-flat, or split-semistable model
and both exact frames. Then there is a nonempty point-centered open
$\Omega_v\subset(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_v)$ on which the selected local
condition, frames, ordered polarization, auxiliary level, and tensor component all persist.

**Proof.** Use a real component at infinity, a smooth residue tube at good places, the
Hasse-invariant open in the ordinary case, a fixed special-fiber tube in the nonordinary case,
and fixed valuation and Kummer shells in the semistable case. The two frame isomorphism schemes
are finite etale, so local sections exist after shrinking around the common point. Intersect
these neighborhoods with the complement of $Z$. $\square$

The point-centered hypothesis is load-bearing: separately nonempty opens can lie on different
ordinary or determinant components and have empty intersection. In the split application the
witness must already exist over $\mathbf Q_v$; a point obtained only after a nontrivial local
extension is not enough because Book 158 later makes $v$ split completely.


## 8. Split Galois-top specialization

### 8.1 The avoidance field

Let $D_{\mathrm{av}}/\mathbf Q$ be a finite Galois compositum containing the full joint
cutout fields of $(\bar\rho,\bar\epsilon_\ell)$ and $(\bar r,\bar\epsilon_q)$, the normal
closure of the CM induction field, the determinant and component fields, every protected
character witness, and every other finite extension named by the later descent ledger. Full
matrix cutouts are used; projective cutouts would not preserve central scalars or determinants.

### 8.2 The Book 158 specialization

Apply Book 158 to the determinant-compatible paired-frame space and the simultaneous
point-centered opens of Chapter 7. Its regular symmetric split-presentation theorem chooses a
simply branched pencil on the fine interior, and its Galois-refined specialization theorem
imposes total reality, complete splitting at every controlled place, and disjointness from
$D_{\mathrm{av}}$.

The output is a totally real Galois extension $F/\mathbf Q$ of positive even degree and a point

$$
y_F\in Y^{\mathrm{ten}}(F)
\tag{8.1}
$$

whose associated abelian variety $A_F/F$ has both exact residual frames and every named local
model. At each controlled rational place every sheet lies in the same chosen open. In
particular all $w\mid2$ are split Tate places. This is an interior construction: it asks for
neither a mixed exact local algebra nor a toroidal compactification.

### 8.3 Preservation of residual images

**Lemma 8.1 (image preservation).** Let $V$ be a finite representation of $G_K$ and let $L/K$
be finite. If $L$ is linearly disjoint from $K(V)$, then

$$
V(G_L)=V(G_K).
\tag{8.2}
$$

If $L$ is disjoint from the joint cutout of $(V,\bar\epsilon_s)$, then the image on
$G_{L(\zeta_s)}$ equals the original cyclotomic-restriction image.

**Proof.** The image of $G_L$ is the Galois group of $K(V)L/L$. Disjointness makes restriction
to $K(V)$ an isomorphism. Apply the same argument to the joint representation and then take the
kernel of its cyclotomic factor. $\square$

Thus Book 158's closure-level avoidance preserves the full and cyclotomic residual images,
absolute irreducibility, adequacy, determinant image, adjoint-twist invariants, and the
protected conjugate-ratio witness.

### 8.4 The specialization theorem

**Theorem 8.2 (split two-prime specialization).** Retain the rational-base residual datum,
compatible corrected relative ray datum, simultaneous coefficient realization, paired-frame
space, and point-centered local opens above. Then Book 158 supplies $F$ and $A_F$ with

$$
A_F[\mathfrak l]\simeq\bar\rho|_{G_F},
\qquad
A_F[\mathfrak q]\simeq\bar r|_{G_F},
\tag{8.3}
$$

preserves both joint residual images, and places every dyadic sheet in the split Tate open.
The field is totally real, Galois, of positive even degree, and disjoint from
$D_{\mathrm{av}}$.

The theorem proves the geometric specialization and exact local frames. It does not prove that
$V_{\mathfrak q}(A_F)$ is automorphic. That assertion begins only after the actual set
$P_{\mathrm{aux}}(A_F)$ is known and a finite-set lifting certificate of Section 2.4 is
supplied.

**Proof.** This is Book 158, Theorem 5.1 and Corollary 6.1, applied to the protected local
branches of Chapter 5. Lemma 8.1 gives the image assertions. $\square$


## 9. The Hilbert--Blumenthal bridge

### 9.1 The specialized abelian variety

The point (8.1) gives a Hilbert--Blumenthal abelian variety $A_F/F$ with $\mathcal O_E$-action,
ordered polarization, auxiliary level, and the two paired frames. Every prime-adic Tate factor
has weight-two Hodge type.

### 9.2 What the two torsion identifications say

The universal property gives exact equivariant paired isomorphisms

$$
A_F[\mathfrak l]\simeq\bar\rho|_{G_F},
\qquad
A_F[\mathfrak q]\simeq\bar r|_{G_F}.
\tag{9.1}
$$

These are not merely equalities of traces or semisimplifications. Pairing compatibility gives
the two cyclotomic determinant lines, and Lemma 8.1 shows that the full residual and
cyclotomic-restriction images have not shrunk.

### 9.3 Local properties of the auxiliary-adic representation

Put

$$
r_A=V_{\mathfrak q}(A_F):G_F\longrightarrow
\operatorname{GL}_2(E_{\mathfrak q}).
\tag{9.2}
$$

At $w\mid q$ it has the selected finite-flat weight-two model over an unramified base. At every
$w\mid2$ it has rank-one Tate monodromy while its residual representation is the protected
unramified dihedral branch. At all other controlled places it lies on the point-centered local
component selected before specialization.

List every actual bad place of $r_A$ and compare it with the norm-pulled dihedral reference.
This determines $P_{\mathrm{aux}}(A_F)$. No place is removed from that set merely because it
was not predicted before specialization.

### 9.4 No inference from torsion alone

The congruence $A_F[\mathfrak q]\simeq\bar r|_{G_F}$ does not determine the local components
of $r_A$ and does not prove its automorphy. The local models record the desired components; the
finite-set certificate of Section 2.4 is what transfers residual automorphy to this particular
characteristic-zero point. Separate one-place level changes are not a substitute.


## 10. The finite-set modularity transfer

### 10.1 Automorphy of the residual dihedral member

Base-change the Hecke character to the CM compositum over $F$ by the norm. Book 158's
closure-level disjointness keeps that compositum quadratic over $F$ and preserves the protected
conjugate-ratio witness. Quadratic induction therefore gives a cuspidal parallel-weight-two
packet $\pi'_F/F$ with

$$
\bar r^T_{\pi'_F,\mathfrak Q}
\simeq\bar r|_{G_F}
\simeq A_F[\mathfrak q].
\tag{10.1}
$$

This is a direct reconstruction of the automorphic induction over $F$, not an appeal to
nonsolvable base change. The protected local branch data identify its residual local conditions
with the lower faces in the finite-set comparison.

### 10.2 The all-active-place handoff

**Theorem 10.1 (finite-set transfer to the Tate-module point).** Let $S$ be the actual set
$P_{\mathrm{aux}}(A_F)$, and assume a finite-set lifting certificate of Section 2.4 for the
residual automorphic reference (10.1) and the point $r_A$. Then, after a finite coefficient
extension, there is a cuspidal parallel-weight-two packet $\Pi_A/F$ such that

$$
V_{\mathfrak q}(A_F)\simeq\rho^T_{\Pi_A,\mathfrak Q}
\tag{10.2}
$$

integrally.

**Proof.** Apply the selected Book 176 interface to the entire set $S$. In the preferred direct
route, $({\rm IAV}_S)$ supplies paired desired and avoidance local rings with common special
fibers, synchronized patching systems, componentwise support transfer, and descent; evaluating
the resulting comparison at the named characteristic-zero point gives automorphy of $r_A$.
The other three interfaces give the same conclusion under their stronger stated hypotheses.

The residual representation remains absolutely irreducible after cyclotomic restriction by
Lemma 8.1, so the automorphic endpoint is cuspidal. At good places the attached representation
and $r_A$ have the same Frobenius polynomials. Absolute residual irreducibility makes every
stable lattice homothetic to $T_{\mathfrak q}A_F$, which upgrades the generic comparison to
(10.2). $\square$

The theorem changes all active places at once. It neither assumes nor proves that $S$ has one
element. In the split Frey application $\{w:w\mid2\}\subseteq S$, so a singleton reduction
would contradict the local geometry already fixed by Book 158.


## 11. Recovering residual automorphy at the original prime

### 11.1 Weight-two Galois realization

The packet $\Pi_A/F$ is noncharacter, cuspidal, parallel weight two, and has trivial central
character in the fixed-determinant normalization. The field $F$ has positive even degree, and
every dyadic place is special for $V_{\mathfrak q}(A_F)$. Choose one $w_*\mid2$. Book 104
constructs the quaternion algebra ramified at every real place except one and at $w_*$, together
with the compact one-split packet corresponding to $\Pi_A$. The ramification count is even,
and the finite ramified place makes the algebra a division algebra.

Book 127, applied to the full component-routing orbit, supplies a rational rank-two family. Let
$E_\Pi$ contain the Hecke data and all splitting values. For every finite place $\lambda$ of
$E_\Pi$ it attaches a semisimple cohomological representation
$\rho^{\mathrm{coh}}_{\Pi_A,\lambda}$ with common good Frobenius polynomials. Put

$$
\rho^T_{\Pi_A,\lambda}
=\rho^{\mathrm{coh}}_{\Pi_A,\lambda}(1)
\simeq\left(\rho^{\mathrm{coh}}_{\Pi_A,\lambda}\right)^\vee.
\tag{11.1}
$$

The isomorphism uses essential self-duality in the trivial component-character case, and
$\det\rho^T_{\Pi_A,\lambda}=\epsilon_\lambda$. The attachment gives a rational weakly
compatible family and stable lattices. Identification of its $\ell$-adic lattice with the
target frame is the cross-prime comparison below.

The $\mathbf Q$-definition of the Hilbert tensor component selects the arithmetic component;
it does not descend $A_F$, $\Pi_A$, or this family from $F$ to $\mathbf Q$.


### 11.2 The cross-prime Tate comparison

**Proposition 11.1 (integral comparison derived from one coefficient prime).** Let $A/K'$ be a
Hilbert--Blumenthal abelian variety with real multiplication by $\mathcal O_E$, and let $\Pi$ be
a noncharacter parallel-weight-two packet with the rational realization datum of Section 11.1.
Suppose that at one prime $\mathfrak q$ of $E$ there is, after a finite coefficient extension,
an isomorphism

$$
V_{\mathfrak q}(A)\simeq\rho^T_{\Pi,\mathfrak Q}.
\tag{11.2}
$$

Then at every prime $\mathfrak l$ of $E$ for which $A[\mathfrak l]$ is absolutely irreducible,
after placing the packet field and $E$ in one common number field $C$ and choosing a place
$\widetilde\lambda\mid\mathfrak l$, one has

$$
V_{\mathfrak l}(A)\otimes_{E_{\mathfrak l}}C_{\widetilde\lambda}
\simeq\rho^T_{\Pi,\widetilde\lambda}.
\tag{11.3}
$$

The left side supplies an $E_{\mathfrak l}$-form of the automorphic member. Every stable
$\mathcal O_{E_{\mathfrak l}}$-lattice in that descended form is homothetic to
$T_{\mathfrak l}A$, and a stable lattice over $\mathcal O_{C_{\widetilde\lambda}}$ reduces as

$$
\bar\rho^T_{\Pi,\widetilde\lambda}
\simeq A[\mathfrak l]\otimes_{k_{\mathfrak l}}k_{\widetilde\lambda}.
\tag{11.4}
$$

The descended lattice itself reduces to $A[\mathfrak l]$ over the fixed field
$k_{\mathfrak l}$. Thus neither exact residue field nor integral comparison is silently inferred
from an enlarged packet coefficient field.

**Proof strategy.** Extract the common algebraic Frobenius polynomial from the
real-multiplication abelian variety, use (11.2) to identify it with the packet polynomial, then
apply density and an elementary stable-lattice argument at $\mathfrak l$.

**Proof.** At every place $v$ of good reduction, prime to the coefficient characteristics, the
$\mathcal O_E$-action commutes with Frobenius. The $E$-linear reduced characteristic polynomial
of that actual Frobenius endomorphism, by Book 35's construction already imported through Book
156, therefore gives one polynomial

$$
P_{A,v}(X)=X^2-a_v(A)X+q_v\in E[X]
\tag{11.5}
$$

whose image in every $E_{\mathfrak p}[X]$ is the characteristic polynomial on
$V_{\mathfrak p}(A)$. The determinant is independently $q_v$ by the polarization; hence
(11.5) remains a characteristic polynomial when Frobenius is scalar.

Fix embeddings of the packet field and $E$ into one algebraic closure and then into
$\overline{\mathbf Q}_q$ as dictated by (11.2), and replace them by their compositum $C$. At
almost every $v$, (11.2) identifies the images in $\overline{\mathbf Q}_q[X]$ of $P_{A,v}$ and
the algebraic packet polynomial. The
embedding is injective, so those algebraic polynomials are equal before completion. After
embedding the common coefficient field at $\mathfrak l$, the two representations in (11.3)
have the same characteristic polynomials on a dense set of Frobenius elements.

The automorphic representation is semisimple. The representation $V_{\mathfrak l}(A)$ is
irreducible whenever $A[\mathfrak l]$ is: a characteristic-zero stable line, intersected and
saturated in $T_{\mathfrak l}A$, would reduce to a nonzero proper stable line. Density and
Brauer--Nesbitt now give (11.3). In particular the right side has the
$E_{\mathfrak l}$-form furnished by the left side, so any auxiliary coefficient enlargement
can be descended through that form.

Let $L=T_{\mathfrak l}A$ and first transport an arbitrary stable lattice in the descended
$E_{\mathfrak l}$-form through (11.3). Scale it, writing it as $L'$, so that
$L'\subseteq L$ but $L'\nsubseteq\varpi L$. Its image in
$L/\varpi L=A[\mathfrak l]$ is a nonzero stable subspace and hence, by absolute irreducibility,
the whole space. Nakayama's lemma gives $L'=L$. Extending this equality to
$\mathcal O_{C_{\widetilde\lambda}}$ and reducing proves (11.4). Absolute irreducibility
persists after residue-field extension, so the same argument makes every stable lattice over
$\mathcal O_{C_{\widetilde\lambda}}$ homothetic to this scalar extension. $\square$

For the specialized variety, Lemma 8.1 preserves absolute irreducibility of
$A_F[\mathfrak l]\simeq\bar\rho|_{G_F}$. Proposition 11.1 and the first frame in (9.1) give

$$
\bar\rho^T_{\Pi_A,\widetilde\lambda}
\simeq A_F[\mathfrak l]\otimes_{k_{\mathfrak l}}k_{\widetilde\lambda}
\simeq\bar\rho|_{G_F}\otimes_k k_{\widetilde\lambda}.
\tag{11.6}
$$

The descended $E_{\mathfrak l}$-form has residual representation exactly
$\bar\rho|_{G_F}$ under the fixed isomorphism $k_{\mathfrak l}\simeq k$.

**Corollary 11.1A (the nonzero upper target localization).** Retain the common coefficient DVR
and its uniformizer $\varpi$. Let
$L_{\Pi_A}$ be the saturated intersection of the rational $\Pi_A$ packet block in the compact
curve carrier of Section 11.1 with its finite free integral cohomology lattice. Let
$\mathfrak m_{\ell,A}$ be the maximal ideal in this carrier's commuting faithful Hecke image
order obtained by reducing the packet character at $\widetilde\lambda$. Then

$$
(L_{\Pi_A})_{\mathfrak m_{\ell,A}}/\varpi\ne0,                \tag{11.6a}
$$

and hence the ambient integral curve-cohomology localization at
$\mathfrak m_{\ell,A}$ is nonzero modulo $\varpi$.  Moreover, the associated rational
rank-two Galois factor admits a stable lattice whose residual
representation is (11.6).  No integral Morita extraction of that rank-two lattice from
$L_{\Pi_A}$ is asserted.

**Proof.** The intersection is saturated by its definition as the intersection of a rational
subspace with a DVR lattice. Scale a nonzero simultaneous packet eigenvector for the selected
character to be primitive in it. Its reduction
injects into the ambient cohomology reduction, is nonzero, and is supported at
$\mathfrak m_{\ell,A}$, which proves (11.6a). Proposition 11.1
identifies the reduction of every stable lattice in the packet representation with
$A_F[\mathfrak l]$ after the displayed scalar extension, so the residual rank-two factor is
(11.6).  This stable lattice is attached to the rational factor; it need not be an integral
direct factor of $L_{\Pi_A}$. $\square$

This corollary is deliberately at the actual upper target level. The target signed-special
problem retains its dyadic special condition, so the chosen carrier place $w_*\mid2$ is not an
edge in the later target-lowering set. Any genuinely extra target place still requires the
separate certified path described in Book 182; the corollary does not provide that path.

### 11.3 The residual potential-modularity theorem

**Theorem 11.2 (conditional split-top residual potential modularity).** Let $K=\mathbf Q$,
let $\ell\ge7$, and let $\bar\rho$ be the Frey signed-special residual datum of Section 2.1.
Construct the auxiliary dihedral representation at $q$ from the rational-base compatible ray
datum of Chapter 4, impose the protected local branches of Chapter 5, and let $F$ and $A_F$ be
the split Galois-top output of Theorem 8.2. Assume a finite-set lifting certificate of Section
2.4 for the actual set $P_{\mathrm{aux}}(A_F)$. Then there is a cuspidal
parallel-weight-two packet $\Pi_A/F$ and, for a place
$\widetilde\lambda\mid\mathfrak l$,

$$
\boxed{
\bar\rho|_{G_F}\otimes_k k_{\widetilde\lambda}
\simeq\bar\rho^T_{\Pi_A,\widetilde\lambda}.}
\tag{11.7}
$$

The packet family has a descended $E_{\mathfrak l}$-form whose distinguished stable lattice
reduces exactly to $\bar\rho|_{G_F}$ over $k$. The field $F/\mathbf Q$ is totally real,
Galois, of positive even degree, completely split at every controlled place, and disjoint from
the full avoidance field fixed before specialization.

**Proof.** Theorem 4.2 and Lemma 4.3 construct the dihedral seed and its protected local
branches. Theorem 2.1 supplies the simultaneous real-multiplication coefficient datum.
Books 156--158 and Theorem 8.2 supply $F$, $A_F$, both exact frames, and image preservation.
Automorphic induction gives (10.1). The selected Book 176 certificate and Theorem 10.1 make
$V_{\mathfrak q}(A_F)$ automorphic. Book 104 supplies a compact one-split carrier using any
one dyadic special place, Book 127 attaches its rank-two family, and Proposition 11.1 identifies
the $\ell$-adic residual member with the first frame in (9.1). $\square$

The conditional boundary is exactly the finite-set certificate for the actual active set. The
theorem neither asserts that this certificate follows from separate one-place results nor
reduces the active set to a distinguished place. Indeed,

$$
\{w:w\mid2\}\subseteq P_{\mathrm{aux}}(A_F),
\qquad
\#\{w:w\mid2\}=[F:\mathbf Q]\ge2.
\tag{11.8}
$$

The earlier one-special-factor theorem has been retired because its hypotheses cannot be met by
this split top and no later step of the FLT proof consumes it.


### 11.4 A stronger controlled form

It is useful to record exactly what survives the construction. Suppose
$D_{\mathrm{av}}$ contains the full target and dihedral cutout fields and both cyclotomic
extensions. Then

$$
\bar\rho(G_F)=\bar\rho(G_{\mathbf Q}),
\qquad
\bar r(G_F)=\bar r(G_{\mathbf Q}),
\tag{11.9}
$$

and the same equalities hold for the cyclotomic restrictions. Thus absolute irreducibility,
adequacy, projective type, trace field, and determinant image are unchanged. The controlled
places split completely, so their local fields, lines, signs, and component labels are
literally unchanged on every sheet.

The theorem permits finitely many further closed loci and finite avoidance fields to be named
before Book 158 chooses its pencil. It does not promise arbitrary degree or nonsplit exact
completion algebras; those belong to a different approximation problem and are not needed here.

## 12. Exceptional cases and failure tests

### 12.1 Coefficient characteristics below seven

The theorem assumes both coefficient characteristics used in finite-set lifting are at least
seven. Characteristic five has a genuine icosahedral exception: the natural two-dimensional
representation of the special-linear cover of $A_5$ has surviving adjoint cohomology. Absolute
irreducibility therefore does not imply the adequacy input of the lifting theorem. In
characteristics two and three, additional failures occur in projective classification,
semisimple spanning, signs, finite-flat theory, and stabilizer orders.

Nothing here proves the result at five by replacing adequacy with a slogan such as “large
image.” A separate five-adic theorem would have to isolate or calculate the exceptional branch.

### 12.2 Reducible and cyclotomically reducible images

If $\bar\rho$ is reducible, the non-Eisenstein Hilbert and quaternionic localizations used in
the proof are unavailable. If it is absolutely irreducible over $K$ but reducible over
$K(\zeta_\ell)$, Clifford theory identifies a quadratic induced branch. The cyclotomic image is
then reducible and cannot be declared adequate.

The same test applies to $\bar r$. A dihedral representation can be absolutely irreducible over
$K$ and become reducible after cyclotomic restriction. The explicit conjugate-ratio witness in
Chapter 4 rules this out.

### 12.3 Determinant and pairing failures

If $\det\bar\rho$ is not the prescribed cyclotomic coefficient line, the paired
$\mathfrak l$-frame twist may be empty. An unpaired isomorphism does not fix the problem. At the
dihedral prime, omitting $\eta_{M/K}$ from the induction determinant creates the same failure.
Even with the correct sign, cancellation of the diagonal ray-unit character does not prove that
the determinant rule and local values agree on every relative ray-class intersection. Without
the compatible corrected datum assumed in Theorem 4.2, the asserted Hecke character has not
been globalized.

Changing the polarization ideal changes the inverse-different value line and can move the
arithmetic component. A prime-to-level isogeny does not automatically preserve the ordered
polarization-module identification. Every such change requires transporting both determinant
isomorphisms.

### 12.4 Component and local-solvability failures

Full geometric monodromy does not put local points on a chosen arithmetic component. A real
point, an ordinary point, and a semistable point constructed on three different components
cannot be intersected. Similarly, separate varieties realizing the two torsion frames do not
give a point of their fiber product.

A finite-flat representation need not be the torsion of a Hilbert--Blumenthal seed of the selected
polarization type. A local frame appearing after an unramified extension does not descend to
the original local field. Each extension used to solve a local point must occur in the global
completion algebra.

### 12.5 Failure of closure-level disjointness

Disjointness of an arbitrary point field from $D$ would not control its normal closure. Book
158 avoids this problem by imposing connectedness after base change to $D$ on the regular
symmetric top before specialization. The resulting Galois field $F$ is disjoint from $D$.

Nor is disjointness from a projective cutout field enough to preserve the full image. Scalars
and determinants may shrink. The avoidance ledger therefore uses full matrix cutout fields.

### 12.6 Failure of finite-set modularity lifting

Residual automorphy in an unspecified packet does not verify the local components of the named
Tate-module point. Separate one-place Ihara, support, or component statements do not imply a
joint finite-set comparison, and an ordered list is not a proof that earlier conditions survive
later changes.

For the preferred direct route, failure of any paired local-ring comparison, component
bijection, synchronization of the Taylor--Wiles systems, support transfer, or descent clause of
$({\rm IAV}_S)$ stops Theorem 10.1. The all-point and pointed alternatives have their own
strictly stronger hypotheses and cannot be invoked by name alone. An accidental semistable
place of $A_F$ belongs to the actual set $S$ whenever it is nonminimal relative to the residual
reference; omitting it invalidates the application.

The compact carrier needs only even degree and one special dyadic factor, both supplied by
Book 158. It does not reduce the lifting set and cannot be used backward to prove the finite-set
certificate.


## 13. Dependency and hypothesis audit

### 13.1 The prerequisite interfaces

The direct prerequisites are Books 6, 98, 104, 127, 141--142, 156--158, and 176. Book 6
supplies the exact Grunwald--Wang alternative used in Lemma 4.3; Book 98 supplies algebraic
Hecke characters and quadratic automorphic induction; Books 141--142 supply the image and
Chebotarev inputs. Books 156--157 supply the fine paired-frame moduli, the corrected tensor
component, product monodromy, and the local interior points. Book 158 owns the simply branched
pencil and split Galois-top specialization. Book 176 owns the finite-set lifting interfaces.
Books 104 and 127 supply the compact carrier and its rational rank-two family.

Book 157 is used only for reusable interior and local results: corrected auxiliary level,
tensor component, product monodromy, ordinary and semistable seeds, exact frames, and
point-centered openness. None of its conditional singleton boundary program
$({\rm IIT})$--$({\rm ICS})$ is a prerequisite.

### 13.2 The theorem-by-theorem hypothesis ledger

| Step | Hypotheses retained | Conclusion used |
|---|---|---|
| simultaneous coefficients | both actual residue fields; distinct odd primes; corrected tensor choice | one real-multiplication field receiving both primes with determinant lines and product monodromy |
| dihedral seed | rational-base compatible ray datum; determinant; type $(1,0)$; protected conjugate-ratio witness | cuspidal weight-two induction with cyclotomic determinant and adequate residual image |
| protected correction | finitely many split determinant-compatible branch pairs; protected witnesses; exact Grunwald--Wang alternative | simultaneous local residual branches without changing determinant or irreducibility |
| local paired-frame space | exact ordinary, finite-flat, good, and split Tate seeds on one tensor component | simultaneous point-centered opens carrying both frames |
| split top | Book 158's simply branched interior pencil, regular symmetric closure, complete splitting, and avoidance | totally real even-degree Galois field $F$ and $A_F$ with every controlled sheet in its chosen open |
| finite-set lifting | actual $P_{\mathrm{aux}}(A_F)$ and one complete Book 176 certificate | automorphy of the named point $V_{\mathfrak q}(A_F)$ |
| compact realization | even degree and any one dyadic special place | compact one-split carrier and rational rank-two compatible family |
| cross-prime comparison | $q$-adic equality; common abelian Frobenius polynomials; absolute irreducibility of target torsion | exact target residual member at $\ell$ |

Every row is used in the displayed direction. In particular, local openness does not prove the
split top, and separate one-place comparisons do not prove the finite-set lifting row.

### 13.3 Circularity audit

The dihedral packet is constructed before $A_F$ and independently of the target. Its residual
automorphy is the starting point. Book 158 then constructs the paired-frame abelian variety
without using automorphy of its Tate module. Only after the actual active set is known does
Book 176 transfer automorphy to that point. The target residual conclusion is read at $\ell$
only after the $q$-adic automorphic packet and its rational family exist.

There is no use of Books 177, 181, 182, or later compatible-family volumes. The unresolved input
is one actual finite-set certificate for $P_{\mathrm{aux}}(A_F)$; it is not hidden in the
geometric specialization. The rational-base ray compatibility is proved here, while the
general totally real-base ray datum remains a separate optional extension and is not needed by
the FLT chain.

### 13.4 Normalization audit

Arithmetic Frobenius is used in the character values and covariant Tate-module polynomials.
Quadratic induction includes the quadratic determinant character. The corrected auxiliary
level is Tate-twisted, and both frame groups are special linear because their determinant lines
are fixed. Covariant Tate modules have cyclotomic determinant; the cohomological automorphic
member is twisted as in (11.1) before comparison.

Coefficient enlargement preserves rank two by scalar extension. Proposition 11.1 first
identifies the rational members and then uses absolute residual irreducibility to identify the
stable lattice. Thus the exact target residual representation is not inferred from an arbitrary
lattice over an enlarged coefficient field.


## 14. Conclusion

### 14.1 The split two-prime package

The two-prime method assigns the explicit residual starting point to $q$ and the target residual
member to $\ell$. A corrected CM ray datum and protected anti-cyclotomic correction construct
the dihedral member with the exact local branches. The determinant-compatible Hilbert--Blumenthal
space places both torsion systems on one arithmetic tensor component. Book 158 specializes its
fine interior to a totally real even-degree Galois top, completely split at every controlled
place and disjoint from the full avoidance field.

Complete splitting forces all dyadic Tate sheets to be active for the auxiliary Tate-module
lift. Therefore the relevant arithmetic handoff is Book 176's finite-set comparison for the
actual set $P_{\mathrm{aux}}(A_F)$. With that certificate, automorphy transfers from the
norm-pulled dihedral packet to $V_{\mathfrak q}(A_F)$; a compact one-split carrier and the
cross-prime comparison then identify the $\ell$-adic residual member with the prescribed
target.

The route has one exact unresolved lifting boundary: construction of the finite-set certificate
for the actual active set. It has no singleton subproblem. The retired one-special-factor
moving presentation, Book 157's conditional toroidal chain, and one-prime scalar augmentation
are neither hypotheses nor alternative conclusions of the FLT theorem. Book 157 remains a
direct source only for its reusable interior component, local seed, frame, and openness results.

Thus Theorem 11.2 is ready as an implication from the finite-set input and supplies precisely
the residual potential-modularity ingredient consumed before Book 181. It does not prove that
input, descend automorphy back to $\mathbf Q$, construct Book 181's entire minimal Hecke
ledger, or address the later compatible-family descent. Those tasks remain with their natural
volumes.
