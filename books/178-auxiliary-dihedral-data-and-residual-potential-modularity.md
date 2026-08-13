# Auxiliary Dihedral Data and Residual Potential Modularity

## Contents

1. [The two-prime method](#1-the-two-prime-method)
   - [The problem and the bridge](#11-the-problem-and-the-bridge)
   - [Standing conventions](#12-standing-conventions)
   - [What must be chosen](#13-what-must-be-chosen)
   - [The logical boundary](#14-the-logical-boundary)
2. [Residual data and admissibility](#2-residual-data-and-admissibility)
   - [The target representation](#21-the-target-representation)
   - [Determinant normalization](#22-determinant-normalization)
   - [Simultaneous coefficient-field realization](#23-simultaneous-coefficient-field-realization)
   - [Cleanability at the auxiliary prime](#24-cleanability-at-the-auxiliary-prime)
   - [The complete input ledger](#25-the-complete-input-ledger)
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
5. [An auxiliary level-raising place](#5-an-auxiliary-level-raising-place)
   - [The Frobenius relation](#51-the-frobenius-relation)
   - [Selecting the prime](#52-selecting-the-prime)
   - [From an old class to a special residual class](#53-from-an-old-class-to-a-special-residual-class)
   - [Signs, repeated roots, and exceptional congruences](#54-signs-repeated-roots-and-exceptional-congruences)
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
   - [The special place](#75-the-special-place)
   - [Good and semistable auxiliary conditions](#76-good-and-semistable-auxiliary-conditions)
   - [The simultaneous local-neighborhood lemma](#77-the-simultaneous-local-neighborhood-lemma)
8. [Arithmetic approximation with closure control](#8-arithmetic-approximation-with-closure-control)
   - [The avoidance field](#81-the-avoidance-field)
   - [Ordinary and Galois-refined specialization](#82-ordinary-and-galois-refined-specialization)
   - [Exact completion data](#83-exact-completion-data)
   - [Preservation of residual images](#84-preservation-of-residual-images)
   - [The specialization theorem](#85-the-specialization-theorem)
9. [The Hilbert--Blumenthal bridge](#9-the-hilbert--blumenthal-bridge)
   - [The specialized abelian variety](#91-the-specialized-abelian-variety)
   - [What the two torsion identifications say](#92-what-the-two-torsion-identifications-say)
   - [Local properties of the auxiliary-adic representation](#93-local-properties-of-the-auxiliary-adic-representation)
   - [No inference from torsion alone](#94-no-inference-from-torsion-alone)
10. [The modularity transfer](#10-the-modularity-transfer)
    - [Automorphy of the residual dihedral member](#101-automorphy-of-the-residual-dihedral-member)
    - [The scalar augmentation lemma](#102-the-scalar-augmentation-lemma)
    - [Applying one-prime modularity lifting](#103-applying-one-prime-modularity-lifting)
    - [Solvable bridges and descent](#104-solvable-bridges-and-descent)
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
    - [Failure of clean modularity lifting](#126-failure-of-clean-modularity-lifting)
13. [Dependency and hypothesis audit](#13-dependency-and-hypothesis-audit)
    - [The prerequisite interfaces](#131-the-prerequisite-interfaces)
    - [The theorem-by-theorem hypothesis ledger](#132-the-theorem-by-theorem-hypothesis-ledger)
    - [Circularity audit](#133-circularity-audit)
    - [Normalization audit](#134-normalization-audit)
14. [Conclusion](#14-conclusion)
   - [The two-prime package and its remaining boundary](#141-the-two-prime-package-and-its-remaining-boundary)

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

The initial and final totally real fields are $K$ and $K'$. A CM quadratic extension used for
induction is $M/K$. The target and auxiliary rational primes are $\ell$ and $q$, and the special
level-raising place is $v_0$. The totally real multiplication field $E$, with primes
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
nonordinary, and semistable seed points. The field ledger records exact completions, total
reality, normal closures, disjointness, and any solvable bridge. The lifting ledger records the
exact residual automorphic localization and every named local component.

The order matters. A global point chosen before its component may have incompatible local
specializations. A field chosen before the cutout fields are listed may shrink a residual image.
Local characters chosen without the diagonal-unit condition may not globalize.

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
torsion do not make a lift automorphic. The available theorem has named local components and
integral hypotheses. In particular, the special residual localization used at $v_0$ still
depends first on the abelian-Ihara family isolated in Book 139; that family is not proved by a
prior source. Its vanishing would still leave the independent typed-Ihara, support,
reciprocity, ray, augmentation, and faithful-carrier hypotheses of Book 175 to verify at the
actual localization. Separately, an approximation point may acquire several additional bad
places, whereas the prior lifting theorem changes only one place and does not provide a
finite-set iteration theorem retaining earlier nonminimal conditions. We therefore isolate a
**cleanable** two-prime datum and prove the final implication only for that exact datum. These
gaps prevent the catalog-wide potential-modularity assertion. They do not create a separate
curve-carrier gap. We choose the point field of even absolute degree, and the clean lifting
datum retains the selected conductor-one Steinberg place. Book 104 then constructs a compact
one-split packet and Book 127 attaches its rank-two family. Outside the clean lifting range the
conclusion stops at the geometric realization (1.1).

## 2. Residual data and admissibility

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
6. the adjoint-twist invariant required by the clean lifting datum vanishes:
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

### 2.4 Cleanability at the auxiliary prime

Let $s\geq7$. A lift $r:G_F\to\operatorname{GL}_2(\mathcal O_s)$ is **one-prime clean** when
it fits the complete one-prime nonminimal datum: $F$ is totally real; the residual cyclotomic
restriction is absolutely irreducible; the adjoint-twist invariant vanishes; coefficient-prime
conditions are unramified finite flat of weights $\{0,1\}$; every other condition is a named
represented minimal component; residual automorphy occurs in the exact non-Eisenstein
quaternionic localization; the normalized branch Smith correction and component-support
conditions are recorded; and the exact hypotheses
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, and $({\rm REC}_v)$ of Book 175
hold, together with $({\rm RAY}_v)$ when the scalar family is used and $({\rm AUX}_Q)$
when a patched auxiliary level is augmented. In particular, the type-incidence and typed-Ihara
hypotheses, the five support clauses, faithful-order generation, branchwise local--global
compatibility, and the Taylor--Wiles hypotheses are not compressed into residual automorphy.
The reduced faithful-order comparison is sufficient for a characteristic-zero point; global
reducedness of the conductor-one deformation source is not required unless a full
scheme-theoretic $R=T$ statement is claimed. The automorphic central character is the one
corresponding to the fixed determinant; in the cyclotomic-determinant normalization used here
it is trivial. At the selected prime the abelian Ihara
conditions of Book 139 and the resulting saturation and perfect-duality statements are part of
the datum whenever the constant-coefficient level-change package is invoked, not consequences
of the numerical level-raising congruence. In the notation used by Books 174--175, the first
missing constant-coefficient input is the finite family of exact vanishings

$$
({\rm AIH}_{\mathscr F})_{v_0}:\qquad
\bigl(H^1_{\mathrm{nc}}(\Gamma_D^{v_0},\kappa)^{\Delta_D}\bigr)_{\mathfrak m_D}=0
\quad\bigl(D\in\mathscr F_{v_0}(Q)\bigr),
\tag{2.10}
$$

equivalently injectivity of every localized residual two-degeneracy map in the actual finite
constant-coefficient flag diagram. Here $Q$ is the auxiliary shadow, $D$ labels a curve in its
actual flag $\mathscr F_{v_0}(Q)$, $\Delta_D$ and $\mathfrak m_D$ are its stabilizer and
localized maximal ideal, and $\kappa$ is the residue field of the auxiliary coefficient order.
Book 139 computes these kernels but does not prove their vanishing. The
crossed-coefficient typed-Ihara vanishings inside $({\rm TYPE}_{v_0})$ are independent inputs;
neither (2.10) nor saturation of the constant rows proves them.

At a selected $v_0\nmid s$, the scalar-twist datum requires $q_{v_0}\equiv1\pmod s$ and retains
scalar residual Frobenius, an enhanced invariant line, a sign, a determinant, and the special
relation. It also includes an actual nontrivial global ray character through the tame
$s$-power quotient; divisibility of $q_{v_0}-1$ does not create that character. Its
augmentation specialization has conductor one. A nontrivial tame-character specialization has
conductor two.

For a specialized lift, let $P_{\mathrm{nm}}$ be the actual set of fixed places at which its
local condition is nonminimal relative to the residual conductor and hence needs a fixed-prime
type complex. This set is defined only after every bad place of the lift is known and after a
lower residual automorphic carrier has been chosen. The phrase **one-prime clean** includes the
equality

$$
P_{\mathrm{nm}}=\{v_0\}.
\tag{2.11}
$$

At every other bad place, the lift and the lower carrier must lie on the same named represented
minimal component permitted as a spectator by Book 175. If the original dihedral packet has
superfluous characteristic-zero level at such a place, a proved saturated integral
level-lowering comparison must first place its residual eigensystem in that minimal carrier.
If the lift itself acquires an extra special component relative to the residual conductor, that
place belongs to $P_{\mathrm{nm}}$; lowering the residual carrier does not remove the lift's
monodromy. Such an output is not one-prime clean. A numerical conductor congruence proves
neither the required spectator comparison nor a theorem handling that extra active place.

A list of individually clean places is not a clean global datum. After the first nonminimal
change, the next application would have to retain an already changed local condition, which the
one-prime theorem does not assert. Thus this book uses only one genuinely clean selected prime.
A future finite-chain or simultaneous route would require a prior theorem proving the mixed
intermediate deformation problems, their cross-Tor terms, and the relevant order-independence
or joint-support statements. No such route is part of the present definition or available from
the declared prior source.

### 2.5 The complete input ledger

A weight-two residual datum together with its auxiliary choices is a
**pre-specialization two-prime package** if it satisfies items 1--6 below. It is
**two-prime admissible** only when at least one output $(K',A)$ of Theorem 8.2 for that
package has also been fixed and satisfies the post-specialization item 7. Thus admissibility
has an existentially witnessed clean output; it is not a promise that every point furnished by
approximation is clean.

1. a distinct $q\geq7$ has been selected with all exclusions of Chapter 3, including
   unramifiedness of $\bar\rho$ at every place above $q$;
2. a corrected relative ray datum satisfying the compatibility hypothesis of Theorem 4.2 has
   been supplied, and the resulting dihedral seed has cyclotomic determinant, cyclotomic
   absolute irreducibility, and clean finite-flat local behavior at $q$ over its actual residue
   field $k_\psi$; when $K=\mathbf Q$, Lemma 4.1A supplies the relative-compatibility part from
   determinant-compatible local branch factors; any finitely many exact residual branch pairs
   at additional split places, with the same determinant, may then be imposed by Lemma 4.3;
3. Theorem 2.1 has then produced $E$, $\mathfrak l$, $\mathfrak q$, the tensor polarization,
   self-dual lattice, a corrected cyclotomic-split or elliptic source, both determinant-line
   identifications, and simultaneous monodromy admissibility;
4. the determinant-compatible two-prime twist over the $\mathbf Q$-defined tensor component
   has a smooth geometrically connected twist $Y^{\mathrm{ten}}$ over $K$;
5. every required real, coefficient-prime, ramified, good, and semistable seed lies on that same
   component after the recorded local extension;
6. in the ordinary specialization form, all local completion algebras have the common-degree
   moving-family presentations required by Book 154, and their common degree $d$ is chosen so
   that $d[K:\mathbf Q]$ is even; in the closure-controlled form, a full Galois approximation
   datum is supplied as in Book 155 and $[G:J][K:\mathbf Q]$ is even. In either form the
   completion algebra at $v_0$ has exactly one distinguished degree-one factor carrying the
   special seed, while every other factor carries a good minimal seed;
7. after specialization, the actual bad set of $A$, the local conditions of
   $T_{\mathfrak q}A$, and a lower residual automorphic carrier have been listed. After every
   required saturated integral level lowering at superfluous dihedral conductor primes through
   a verified chain whose intermediate carriers and retained local components are recorded, the
   final carrier lies in the exact signed special localization at the distinguished place
   $w_0\mid v_0$ and in the same named minimal spectator components as the Tate module
   everywhere else. The equality $P_{\mathrm{nm}}=\{w_0\}$ holds, and at $w_0$ all hypotheses
   of Book 175 are verified: $({\rm AUT}_{w_0})$, $({\rm TYPE}_{w_0})$ including its typed
   parahoric-extension, incidence, and typed-Ihara rows, all five clauses of $({\rm SUP}_{w_0})$,
   $({\rm REC}_{w_0})$, and the effective global $({\rm RAY}_{w_0})$ datum. The entire
   applicable family $({\rm AIH}_{\mathscr F})$, the line and sign, primitive primary and
   companion lattices, normalized branch correction, component support, finite-flat quotients,
   faithful trace/structural Hecke order, and exact fixed-prime augmentation are retained;
   $({\rm AUX}_Q)$ is added if the comparison descends from patched auxiliary level, and the
   applicable $({\rm PRI}_{\rm type})$, $({\rm NU}_{\rm type})$, and Book 140
   node-uniformization hypothesis are added whenever their level-change consequences are used.
   Generic support and common-kernel equality are then conclusions of Books 140 and 174 under
   the preceding inputs, not further hypotheses. The specialized Tate-module point has nonzero rank-one
   conductor-one monodromy and the fixed determinant corresponding to trivial automorphic
   central character.

Items 1--6 are pre-specialization construction clauses. Item 7 is a post-specialization
verification clause and is not an input to the approximation theorem. Book 157 places the
corrected tensor seeds on one arithmetic component, and product monodromy proves the twist over
that component geometrically connected. The local geometry verifies item 5 in its stated good,
ordinary, local--local, and split-semistable ranges. Item 7 is the exact boundary of the lifting
theorem; calling the entire package admissible does not prove that a point supplied by
approximation satisfies it. The compact curve carrier is not another item: even absolute
degree and the retained special factor let Books 104 and 127 construct the carrier for the
final lifted packet in Chapter 11. The exact compact residual localization required by
$({\rm AUT}_{w_0})$ is already part of item 7; it is not inferred from torsion or from the
eventual carrier.

Book 154, Lemma 5.2A makes item 6 automatic for every nonsplit packet which the application
permits to be repeated wholesale.  It does not make the one-special-factor clause automatic.
On the local curve used by its pencil construction, let $V_{\mathrm{sp}}$ be the assigned
degree-one special neighborhood containing $S$, let $P$ be a good point, and let $\mathcal A$
have degree $e$.  Book 154, Lemma 5.2B gives the exact fixed-slice condition

$$
n([\mathcal A]-e[P])
\in\{[T-P]:T\in V_{\mathrm{sp}}\}
+\mathscr R^{\mathrm{good}}_{v_0,ne-1},
\tag{2.12a}
$$

where the right side consists of the Abel classes of all reduced degree-$(ne-1)$ divisors whose
residue-field factors carry good minimal seeds, added to the class of the unique varying special
factor.  Thus (2.12a) already allows compensating good factors of arbitrary permitted finite
etale type.  Freezing the special representative at $S$ gives the sufficient condition

$$
n([\mathcal A]-e[P])-[S-P]
\in\mathscr R^{\mathrm{good}}_{v_0,ne-1}.
$$

If every added factor is instead obtained by repeating one degree-one good neighborhood of
$P$, and $G_{v_0}$ is the open subgroup of the local Jacobian generated by its differences,
shrink $V_{\mathrm{sp}}$ so that $[T-S]\in G_{v_0}$ for every $T\in V_{\mathrm{sp}}$.
For sufficiently large degree, the bounded-generation and collision-removal argument of Book
154, Step 2 identifies the degree-indexed one-tube Abel image with $G_{v_0}$.  Then (2.12a)
reduces to

$$
n([\mathcal A]-e[P])-[S-P]\in G_{v_0}
\tag{2.12}
$$

for one common allowed exponent $n$.  Divisibility kills the first term in the finite quotient
but not the fixed second term.  A finite coset-complete collection of compensating good divisors
would make (2.12a) automatic in high degree, but no prior result constructs such a collection on
the actual slice.  Book 154, Lemma 5.2D would also make (2.12a) automatic if that slice had a
smooth proper integral model whose allowed good factors contained every tube above a nonempty
special-fiber Zariski open; Book 154, Corollary 5.2E turns either verified repair into the common
presentation.  Book 157, Lemmas 13.2A.1--13.2A.2 prove the finite-residue relative Bertini,
complete-intersection, and coefficient-stability steps.  Its Lemmas 13.2B.1--13.2B.2 normalize
the paired-frame division monomials and construct a regular projective equivariant fan.  They do
not construct algebraic cusp embeddings for that fan, glue them to the good interior, identify
the resulting completions, or descend an ample bundle.  Those claims are isolated as Book 157,
Required Theorem 13.2B.3.  Conditional on that theorem, Proposition 13.2B.4 gives
$(\mathrm{FTJ})_{v_0,Z}$, Corollary 13.2B.5 gives the weaker form of
$(\mathrm{ICS})_{v_0,Z}$ used by Book 154, and Book 154, Corollary 5.2E proves (2.12a) in every
sufficiently large compatible degree.  Without it, item 6 remains an input.
The literal stronger clause requiring a good $k$-point to reduce inside the allowed
special-fiber open still needs Book 157, (13.21), but it is not used here.  Equal ranks, Hensel
lifting, local realizability, and arbitrary norm
factors in one residue tube do not by themselves supply it; Book 154, Counterexample 5.2C gives a local
counterexample.

## 3. Choosing the auxiliary prime

### 3.1 Why a second residue characteristic is useful

The auxiliary prime does three jobs. It supplies a residual representation whose automorphy is
constructed from a character, the coefficient characteristic for modularity lifting, and the
second factor in a connected two-prime frame cover. These jobs impose distinct exclusions.

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

Several later conditions also eliminate finitely many $q$. The one-prime theorem requires
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

The lifting theorem at $q$ requires unramified local bases. We choose $q$ unramified in $K$ and
later prescribe split or unramified completion algebras at every $w\mid q$. An arbitrary
specialization can ramify at $q$ even if $K$ does not; this must be prevented in the local
algebra.

There is a second, independent condition at the same places: $\bar\rho|_{G_{K_w}}$ must be
unramified. A good Hilbert--Blumenthal variety has unramified $\mathfrak l$-torsion at residue
characteristic $q\ne\ell$. If $\bar\rho$ had nontrivial inertia at $w$, no unramified extension
could make an exact good $\mathfrak l$-frame exist. Since $q\notin S(\bar\rho)$, the target is
unramified; after a finite unramified extension its finite Frobenius action becomes trivial and
the prime-to-$q$ frame can be solved on the ordinary seed.

At $\ell$, the target finite-flat module must be realized by an ordinary or local--local Hilbert--Blumenthal
seed on the selected component. If a local extension is required, it is recorded in the global
completion datum. Finite flatness persists upward, but finite flatness acquired after ramified
extension need not descend.

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
The monodromy operator is always zero, so the dihedral form supplies an old residual class at
the later special place, not a characteristic-zero Steinberg component.

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

## 5. An auxiliary level-raising place

### 5.1 The Frobenius relation

The dihedral automorphic representation is not special anywhere: induced character parameters
have zero monodromy. The lifting datum nevertheless needs a special automorphic residual
localization. We create it by level raising at one good prime $v_0\nmid q$.

Let the unramified arithmetic-Frobenius roots of $\bar r$ at $v_0$ be $\alpha$ and $\beta$.
For a conductor-one covariant special lift, the exact sequence is an unramified scalar twist of

$$
0\longrightarrow\mathcal O_q(1)
\longrightarrow T
\longrightarrow\mathcal O_q
\longrightarrow0.
\tag{5.0}
$$

Thus the monodromy-invariant subline has the cyclotomic-multiple root. If $\alpha$ labels that
line and $\beta$ labels the quotient, reduction can be unramified only if

$$
\alpha=q_{v_0}\beta
\quad\text{or}\quad
\beta=q_{v_0}\alpha.
\tag{5.1}
$$

Equivalently,

$$
(\operatorname{tr}\bar r(\Phi_{v_0}))^2
=(q_{v_0}+1)^2q_{v_0}^{-1}\det\bar r(\Phi_{v_0}).
\tag{5.2}
$$

When the two roots are distinct, their ordering fixes the special line. The branch used below
is scalar, so a line must instead be included in the enhanced residual datum. The signed
primary localization fixes the sign; Equation (5.2) alone fixes neither label.

### 5.2 Selecting the prime

The prior one-prime theorem treats the scalar-twist branch

$$
q_{v_0}\equiv1\pmod q,
\tag{5.3}
$$

not the distinct-root branch. Prescribe the identity class in the finite Galois compositum cut
out jointly by $(\bar r,\bar\epsilon_q)$, $(\bar\rho,\bar\epsilon_\ell)$, the normal closure
of $M/K$, and the prime-to-$q$ auxiliary-level, determinant-line, and protected-character
fields. Chebotarev gives a good prime $v_0\nmid\ell q$, outside both conductors and every moduli
exclusion, which splits completely in that compositum. For arithmetic Frobenius this gives

$$
\bar r(\Phi_{v_0})=1,
\qquad
\bar\epsilon_q(\Phi_{v_0})=1,
\qquad
\bar\rho(\Phi_{v_0})=1,
\qquad
\bar\epsilon_\ell(\Phi_{v_0})=1.
\tag{5.4}
$$

Thus (5.1)--(5.3) hold with $\alpha=\beta=1$. The residual representation is scalar, so its
matrix does not select a line. Choose a line as part of the enhanced local datum and later
identify it with the multiplicative line of the Tate model. The normalized trace is $2$, so
the primary sign is selected; the companion signed factor is $4$, a unit because $q\geq7$.

### 5.3 From an old class to a special residual class

At level prime to $v_0$, the dihedral packet contributes an old eigensystem. The two degeneracy
maps at $v_0$ have a Gram matrix whose determinant, after localizing at the residual maximal
ideal, vanishes precisely under the level-raising relation. Hence its cokernel has nonzero
residual support. Saturation of the degeneracy image ensures that this residual cokernel is not
created by torsion in the ambient lattice. The free new quotient and the monodromy--component
sequence then place the same residual eigensystem in the selected special localization.

Under the exact integral hypotheses, this argument gives more than a conductor congruence. The
scalar line enhancement chooses the invariant line; the primary localization chooses the sign;
the determinant remains cyclotomic; and the new quotient has rank-one monodromy in
characteristic zero. The scalar Frobenius matrix and numerical congruence by themselves give
none of the line, saturation, or component-support conclusions.

**Proposition 5.1 (conditional scalar residual level raising).** Assume (5.1), (5.3)--(5.4),
the chosen scalar line and primary sign, non-Eisenstein localization, the full applicable
$({\rm AIH}_{\mathscr F})$ family of Book 139, saturated degeneracy maps, the type-incidence
and typed-Ihara hypotheses needed for the actual coefficient flag, primitive primary and
companion type lattices, the normalized branch Smith correction and its component support, and
the branchwise local--global compatibility hypotheses of the one-prime datum. Then
the residual eigensystem of $\pi(\psi)$ occurs in the named minimal-special localization at
$v_0$, with the chosen line, sign, and determinant.

**Proof.** The determinant of the old Gram matrix vanishes modulo the residual maximal ideal by
(5.1). The primary null direction is nonzero because its companion factor is the unit $4$. If
its localized cokernel vanished, the determinant would be a unit, a contradiction.
The assumed abelian Ihara family supplies every constant-row residual injectivity needed by
Book 139, while the separately assumed typed rows control the crossed coefficients;
saturation then identifies reduction of the cokernel with the cokernel of reduction. The free
new quotient identifies the nonzero cokernel with a new special class. The normalized branch
Smith correction ensures that this class survives on the asserted component rather than only
in the ambient graph quotient. Primary--companion adjunction transports the enhanced line to
the line and sign labels. Full local--global compatibility identifies the characteristic-zero
branches as the asserted special packets. $\square$

Proposition 5.1 is conditional because its abelian Ihara hypothesis is conditional in the
prior source. Nothing in the displayed Gram determinant proves that hypothesis.

Here is the local algebra behind the determinant statement. After scaling by the central
character, the two degeneracy maps have Gram matrix

$$
G_{v_0}=
\begin{pmatrix}
q_{v_0}+1&T_{v_0}\\
T_{v_0}&q_{v_0}+1
\end{pmatrix}
\tag{5.5}
$$

on the old summand. On an eigensystem with trace $a_{v_0}$, its determinant is
$(q_{v_0}+1)^2-a_{v_0}^2$ in trivial central normalization; restoring the determinant character
gives (5.2). In the scalar branch, a null vector records the primary relation between the two
degeneracy branches, while the separately chosen residual line records the special invariant
line. The new quotient is therefore not obtained from a dimension count: it is the saturated
cokernel detected by this explicit null direction and the enhanced line datum.

### 5.4 Signs, repeated roots, and exceptional congruences

The congruence $q_{v_0}\equiv1\pmod q$ is deliberate: it is exactly the scalar-twist range of
Book 175. Because the roots collide, an integral root idempotent cannot select the line; the
enhanced scalar line is indispensable. If $q_{v_0}\equiv-1\pmod q$, no nontrivial scalar
$q$-power tame character exists and the two-sign Smith problem remains. If
$q_{v_0}\not\equiv1\pmod q$, a distinct-root special chart may exist, but it is not the
one-prime theorem supplied by Book 175.

Changing from arithmetic to geometric Frobenius would invert the cyclotomic ratio in (5.1); we
use arithmetic Frobenius throughout this construction. Finally, a nonzero new quotient proves
residual occurrence, not that the original dihedral characteristic-zero packet has become
special. The new special packet is a congruent packet.

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
embedding of $K'$ to remain real.

### 7.2 The target coefficient prime

Let $w\mid\ell$. The target module is finite flat of weights $\{0,1\}$. If it is ordinary, use
an ordinary Hilbert--Blumenthal seed whose connected--étale torsion has the same paired generic representation,
after the explicitly allowed finite local extension. If it is nonordinary, use a local--local
Hilbert--Blumenthal seed, such as a supersingular tensor seed on a tensor-admissible component.

The ordinary locus is open by nonvanishing of the Hasse invariants. Nonordinarity is closed in
the special fiber, so its openness in the local field is obtained differently: fix the entire
special point and take its residue tube. Every point in that open tube has the same nonordinary
reduction. In either case, the generic frame is locally constant because its isomorphism scheme
is finite étale.

If the proposed finite-flat module is not realized by a Hilbert--Blumenthal seed of the selected polarization
type, finite flatness alone does not create a point. This is one of the explicit admissibility
checks.

There is a sharper boundary when the target module is the finite-flat residual torsion of a
Tate curve at $\ell$.  Book 157, Proposition 8.4A shows that its selected model is ordinary,
so a local--local seed cannot realize it, and that the multiplicative Tate curve does not give
a finite-flat characteristic-zero tower.  If the application forbids a local extension, it
must first construct a good ordinary seed over the stated base completion.  The auxiliary
branch at that same place should then be prescribed to equal the prime-to-$\ell$ torsion of
this seed.  Lemma 4.3 permits exactly that determinant-compatible correction at a split place.
A branch pair fixed earlier from the multiplicative Tate semisimplification need not have the
good seed's Frobenius polynomial.  Thus the order

$$
\text{one-prime good seed}\quad\longrightarrow\quad
\text{auxiliary branch correction}\quad\longrightarrow\quad
\text{two-frame point}                                      \tag{7.1a}
$$

is load-bearing.  This section's extension-valued admissibility statement proves neither the
first arrow over the original completion nor descent of the resulting point.

### 7.3 The auxiliary coefficient prime

At a place above $q$, use the ordinary unramified-twist model (4.13). After the recorded finite
unramified extension kills $\bar\theta_w$, choose an ordinary Hilbert--Blumenthal seed with
$\mathfrak q$-torsion paired-isomorphic to $1\oplus\bar\epsilon_q$ and solve the
$\mathfrak l$-frame simultaneously. This last phrase now has a proof: Chapter 3 excluded every
rational prime below the ramification set of $\bar\rho$, so
$\bar\rho|_{G_{K_w}}$ is unramified. A finite unramified extension kills its finite Frobenius
action. The ordinary seed's prime-to-$q$ torsion and its determinant line also become constant
after a finite unramified extension, and paired bases then give the exact $\mathfrak l$-frame on
the same seed. The ordinary deformation tube gives a nonempty open set on which good ordinary
reduction and both frames persist.

The completion field is chosen unramified over $\mathbf Q_q$. This retains the exact range of
the finite-flat lifting theorem. Allowing an arbitrary ramified splitting field for the frames
would solve the moduli point problem but could invalidate modularity lifting.

Had $\bar\rho$ been ramified at $w$, good reduction would force $A[\mathfrak l]$ to be
unramified while the requested frame forced it to have the same nontrivial inertia as
$\bar\rho$. No choice of an unramified frame field could reconcile those conditions. The
prime-selection exclusion is therefore necessary, not a convenience.

### 7.4 Ramification of the dihedral seed

At a finite place where $M/K$ or $\psi$ is ramified, $\bar r$ may be ramified. A good abelian
variety over the original local field has unramified prime-to-residue-characteristic torsion, so
it cannot realize an arbitrary ramified $\bar r$ there. The correct repair is to prescribe a
finite local extension on which the residual module becomes compatible with a Hilbert--Blumenthal seed.

Because $\bar r$ has finite image, a finite extension trivializes it. One rarely needs so much:
it is enough to kill the local quadratic permutation character and the finite character values
appearing in its inertia. Over that extension one chooses a good Hilbert--Blumenthal point and paired frames.
The exact extension is put into the completion algebra used globally.

This procedure restricts the residual representation; it does not assert that ramification has
disappeared over the original field. Nor does it identify the full $q$-adic local type of an
arbitrary lift. That type is fixed separately in the clean lifting ledger.

### 7.5 The special place

At $v_0$, choose a split semistable tensor Tate point. Its $q$-adic Tate module has rank-one
monodromy, a canonical invariant line, and conductor one at the augmentation specialization.
Equation (5.4) is what makes both frames possible on this same point. Both residual systems and
both cyclotomic characters are trivial on the local decomposition group: they are unramified
and their arithmetic Frobenius values are trivial. Choose a Tate parameter in

$$
(K_{v_0}^\times)^{\ell qN}
$$

with positive valuation. Write the parameter as $q_0=q_N^N$; its Kummer classes vanish modulo
both coefficient primes and $q_N$ supplies the corrected auxiliary level. The split Tate torsion is therefore
$1\oplus\bar\epsilon_\ell$ at $\mathfrak l$ and
$1\oplus\bar\epsilon_q$ at $\mathfrak q$; (5.4) identifies both with the required trivial
restrictions. Map the enhanced scalar line chosen in Section 5.2 to the multiplicative line of
the $\mathfrak q$-torsion. The finite constant
fields included in the Chebotarev compositum are split at $v_0$, so paired bases give both exact
frames over $K_{v_0}$ itself. Pairing fixes the determinant; the primary special localization
of Proposition 5.1 fixes the sign.

Semistability and toric rank persist in a boundary neighborhood. A Kummer class is locally
constant after shrinking because $K_{v_0}^\times/(K_{v_0}^\times)^q$ is discrete. If finite
flatness of Tate $q$-torsion is required at a residue-characteristic place, the valuation must
be divisible by $q$; here $v_0\nmid q$, so the generic torsion is finite étale and that
coefficient-prime issue does not arise.

### 7.6 Good and semistable auxiliary conditions

At a controlled place away from $\ell qv_0$, a smooth special-fiber point gives a good integral
point after the recorded unramified extension. Its residue tube is open and preserves good
reduction and both frames. At a place where a clean special component is required, use a
semiabelian seed with the exact toric rank, splitness, and Kummer class.

The completion algebra at $v_0$ deliberately uses two kinds of factors. Its one distinguished
degree-one factor uses the special seed of Section 7.5. Every other factor uses a good tensor
seed with the same trivial residual frames supplied by (5.4). Consequently the specialization
has exactly one prescribed nonminimal place above $v_0$, rather than one such place for every
degree of $K'/K$.

Good reduction, ordinary or local--local type, semistability, toric rank, and finite flatness
persist after finite extension. Exact valuations multiply by ramification index; nonsplit
multiplicative reduction may become split; a Kummer class may become trivial. Therefore exact
valuation and nonsplitness assertions require the completion algebra, not just persistence.

### 7.7 The simultaneous local-neighborhood lemma

**Theorem 7.1 (one-component local package).** Let $Z\subsetneq Y^{\mathrm{ten}}$ be closed.
For each controlled place $v$, write the recorded completion algebra as
$B_v=\prod_iK_{v,i}$. Suppose that on every factor there is a point of
$(Y^{\mathrm{ten}}\setminus Z)(K_{v,i})$ carrying the assigned real, good, ordinary,
nonordinary finite-flat, or split-semistable model above. Then there are nonempty opens

$$
\Omega_v=\prod_i\Omega_{v,i}
\subset(Y^{\mathrm{ten}}\setminus Z)(B_v)
\tag{7.1}
$$

on which the factorwise selected local conditions, both exact paired frames, ordered
polarization, auxiliary level, and component all persist.

**Proof.** At real places use the odd-involution criterion and a real component. At good places
use a smooth residue tube. At ordinary places intersect the tube with the Hasse-invariant open.
At nonordinary places fix the local--local special point. At semistable places use the boundary
chart and fixed valuation and Kummer shells. The two frame isomorphism schemes are finite étale,
so they admit local sections after shrinking. The complement of $Z$ is open and contains the
seed. Every intersection is made around one point already satisfying all conditions, hence is
nonempty. $\square$

For completeness, consider why the frame condition is open. If $\mathcal A[\mathfrak p]$ is the
finite étale torsion family on a characteristic-zero analytic neighborhood $U$, then

$$
\mathcal I_{\mathfrak p}
=\operatorname{Isom}^{\mathrm{pair}}
(V_{\mathfrak p},\mathcal A[\mathfrak p])\longrightarrow U
$$

is finite étale. At a point carrying a frame, the local inverse theorem gives neighborhoods on
which one sheet of $\mathcal I_{\mathfrak p}$ maps homeomorphically to $U$. Intersect these
neighborhoods for $\mathfrak l$ and $\mathfrak q$. Thus simultaneous framing is not deduced from
local constancy of two abstract isomorphism classes; it is represented by a common finite étale
section.

The point-centered hypothesis prevents a common error: separately nonempty opens can have empty
intersection, particularly when they lie on ordinary and supersingular tubes or on different
determinant components.

## 8. Arithmetic approximation with closure control

### 8.1 The avoidance field

Let $D_{\mathrm{av}}/K$ be a finite Galois compositum containing:

- the full joint cutout fields of $(\bar\rho,\bar\epsilon_\ell)$ and
  $(\bar r,\bar\epsilon_q)$;
- the normal closure of $M/K$;
- the fields cut out by determinant, component, and prescribed frame torsors;
- every ray or auxiliary field whose intersection could erase a local character witness;
- any finite field already forbidden by a later clean lifting or descent step.

Using the full residual fields preserves matrix images. The projective fields alone would not
preserve determinants or central scalars. The compositum is taken before specialization so that
all compatibility conditions can be imposed at once.

### 8.2 Ordinary and Galois-refined specialization

If only a finite totally real point field, local opens, exact finite étale completion algebras,
and disjointness of the point field from $D_{\mathrm{av}}$ are needed, simultaneous
Moret--Bailly approximation applies to $Y^{\mathrm{ten}}\setminus Z$ when the local algebras
have the common-degree moving-family presentations required in Book 154. It produces $K'$ and
a point, but does not assert that $K'/K$ is Galois or that its normal closure is disjoint from
$D_{\mathrm{av}}$.

If later arguments require image preservation throughout a normal-closure diagram or a
solvable bridge from the point field, ordinary approximation is insufficient. One supplies a
Galois approximation datum

$$
(H,\widetilde T,G,J,T,e)
\tag{8.1}
$$

with $J$ core-free, and solvable when an upper bridge is required. Full monodromy of
$\widetilde T\to H$, local realizability of every top torsor, and the evaluation map
$T\to Y^{\mathrm{ten}}$ are hypotheses verified before specialization. The resulting top field
$\widetilde L$ is Galois with group $G$, the point field is $K'=\widetilde L^J$, and
$\widetilde L$ is the normal closure of $K'$.

### 8.3 Exact completion data

At a controlled place $v$, a local homomorphism

$$
\phi_v:G_{K_v}\longrightarrow G
$$

has image $D_v$ and inertia image $I_v$. The point-field algebra is

$$
K'\otimes_K K_v
\simeq
\prod_{D_vgJ\in D_v\backslash G/J}
\widetilde L_w^{D_v\cap gJg^{-1}}.
\tag{8.2}
$$

Thus one top local torsor controls every factor and every intermediate field. At real places a
trivial top homomorphism gives a product of copies of $\mathbf R$, proving total reality of the
top field and all subfields. At a place required to split, a trivial finite local homomorphism
gives complete splitting everywhere in the diagram.

The local point must be specified on every factor in (8.2). One acceptable completion does not
control the other double cosets.

At $v_0$, the required algebra has one distinguished factor equal to $K_{v_0}$ and all other
factors assigned to good minimal neighborhoods. In the ordinary form this is one
common-degree moving-family datum. In the Galois form the action of $D_{v_0}$ on $G/J$ must
have exactly one fixed coset designated by the special seed, and the remaining orbits must
realize the stated good factors. Taking the local homomorphism trivial would instead split
$v_0$ completely and create several fixed nonminimal places.

### 8.4 Preservation of residual images

**Lemma 8.1 (image preservation).** Let $V$ be a finite representation of $G_K$ and let
$L/K$ be finite. If $L$ is linearly disjoint from $K(V)$,
then

$$
V(G_L)=V(G_K).
\tag{8.3}
$$

If $L$ is also disjoint from the joint cutout of $(V,\bar\epsilon_s)$, then the image of
$G_{L(\zeta_s)}$ equals the original cyclotomic-restriction image.

**Proof.** The image of $G_L$ is the Galois group of $K(V)L/L$. Disjointness makes restriction
$\operatorname{Gal}(K(V)L/L)\to\operatorname{Gal}(K(V)/K)$ an isomorphism. For the second
claim apply this to the joint representation and then take the kernel of its cyclotomic
factor. $\square$

Consequently absolute irreducibility, cyclotomic absolute irreducibility, adequacy, determinant
image, the adjoint-twist invariant, and any conjugate-ratio witness are preserved. For the
adjoint assertion one must retain the joint image with $\bar\epsilon_s$; preserving the matrix
image and cyclotomic image separately would not suffice. Solvability of $L/K$ by itself would
preserve none of them.

### 8.5 The specialization theorem

**Theorem 8.2 (controlled two-prime specialization).** Assume items 1--6 of the two-prime
ledger and the local package of Theorem 7.1. In the ordinary form, assume a common degree and a
simultaneous moving-family presentation for every exact local algebra as required by Book 154.
In the closure-controlled form, assume the Galois datum (8.1), including a split top torsor at
every real place and a realized evaluated point on every factor of each prescribed quotient
algebra. Then there are a finite totally real extension $K'/K$ of even absolute degree and a
point

$$
y\in(Y^{\mathrm{ten}}\setminus Z)(K')
\tag{8.4}
$$

such that every localized conjugate of $y$ lies in its prescribed neighborhood, all exact
completion data hold, in particular there is exactly one distinguished degree-one special
place $w_0\mid v_0$ and all other places above $v_0$ are on the prescribed good neighborhoods,
$K'$ is linearly disjoint from $D_{\mathrm{av}}$, and, in the Galois
form, the normal closure is disjoint from $D_{\mathrm{av}}$ and has the prescribed group and
core-free stabilizer $J$. If the supplied datum is a solvable bridge datum, then $J$ is
solvable and the upper extension comes with the prime-cyclic tower of Book 155; solvability is
not a conclusion for an arbitrary Galois approximation datum.

**Proof.** In the ordinary form, apply simultaneous Moret--Bailly approximation to the smooth
geometrically connected variety $Y^{\mathrm{ten}}\setminus Z$, using split real cycles, the local
algebras underlying (7.1), the even common degree fixed in item 6, and connectedness after base
change to $D_{\mathrm{av}}$. In the Galois form, apply Galois-refined approximation to (8.1),
with split top fibers at all real and
split finite places and the realized top homomorphisms elsewhere. Full top monodromy gives the
normal closure and base-changed connectedness gives closure-level disjointness; the fixed-field
index in item 6 gives even absolute degree. Evaluation gives $y$. The double-coset formula proves
every completion assertion. $\square$

In the ordinary form, the proof first replaces each local point by a reduced effective cycle of
one common degree. These cycles lie in the reduced symmetric locus. The universal incidence
family is finite étale; imposing connectedness of its specialization turns the resulting étale
algebra into one field rather than a product. At real places the local cycle is a collection of
real points, so the specialized algebra is a product of copies of $\mathbf R$. At a finite
place with prescribed algebra $B_v$, its entire conjugacy orbit is placed in the chosen open.
Connectedness after scalar extension to $D_{\mathrm{av}}$ makes
$K'\otimes_K D_{\mathrm{av}}$ a field and proves linear disjointness.

In the Galois form, connectedness of the quotient incidence fiber would not suffice. The top
fiber of $\widetilde T$ is forced to have full group $G$ by maximal-subgroup resolvents. Its
base change to $D_{\mathrm{av}}$ is forced to remain connected. Core-freeness of $J$ then makes
the top field the actual normal closure of the quotient field. These are three separate Hilbert
conditions, compatible because they are imposed on one affine parameter space before
specialization.

The theorem does not replace the geometric verification of (8.1). A connected two-prime frame
cover is not automatically a presentation with a prescribed Galois group, nor does it make the
sheet stabilizer solvable.

## 9. The Hilbert--Blumenthal bridge

### 9.1 The specialized abelian variety

The point (8.4) corresponds to a Hilbert--Blumenthal abelian variety

$$
A/K'
$$

with $\mathcal O_E$-action, ordered $\mathfrak c$-polarization, auxiliary level, and the two
paired frames. Its dimension is $[E:\mathbf Q]$. The determinant condition makes its Lie algebra
rank one at every embedding, so every prime-adic Tate factor has weight-two Hodge type.

Because $y$ avoids $Z$, all deliberately removed degeneracies are absent. Typical choices of
$Z$ exclude extra endomorphisms, reducible geometric monodromy, or a locus where a desired local
parameter ceases to be regular. Avoidance works only when each seed already lies outside $Z$.

### 9.2 What the two torsion identifications say

The universal property gives exact equivariant paired isomorphisms

$$
A[\mathfrak l]\simeq\bar\rho|_{G_{K'}},
\qquad
A[\mathfrak q]\simeq\bar r|_{G_{K'}}.
\tag{9.1}
$$

These are not merely equalities of traces or semisimplifications. Pairing compatibility gives

$$
\det A[\mathfrak l]=\bar\epsilon_\ell,
\qquad
\det A[\mathfrak q]=\bar\epsilon_q
\tag{9.2}
$$

in the fixed coefficient lines. By Lemma 8.1 the two residual images and their cyclotomic
restrictions have not shrunk.

### 9.3 Local properties of the auxiliary-adic representation

Let

$$
r_A=V_{\mathfrak q}(A):G_{K'}\longrightarrow
\operatorname{GL}_2(E_{\mathfrak q}).
\tag{9.3}
$$

At places above $q$, the ordinary good model supplies compatible finite-flat quotients and
weights $\{0,1\}$ over an unramified base. At the distinguished $w_0\mid v_0$, the Tate model supplies the enhanced
special augmentation component with rank-one monodromy, invariant line, sign, and cyclotomic
determinant. At the remaining controlled places, the local neighborhoods put $r_A$ on the named
good, finite-descent, tame-dihedral, or special component used in the clean ledger.

The representation is unramified outside finitely many places because it comes from an abelian
variety. After listing this actual bad set, item 7 chooses a lower residual automorphic carrier
and computes $P_{\mathrm{nm}}$. It requires $P_{\mathrm{nm}}=\{w_0\}$. At every other bad
place, $r_A$ and the carrier must lie on the same named represented minimal spectator
component. This includes primes introduced by the dihedral character: any superfluous
characteristic-zero conductor of $\pi'$ must already have been removed by a proved saturated
integral level-lowering chain with every intermediate carrier recorded. If an additional bad
place of $A$ is nonminimal, the one-prime datum fails; a list of further places is not silently
promoted to a finite-set theorem.

There is no pre-specialization proof of that last sentence. The extra bad places are known only
after $A$ has been produced. If an extra place is semistable and its residual representation is
unramified, the special congruence relation is visible, but that numerical fact does not by
itself construct a saturated lower-face automorphic class, an ordered integral flag, or a
compatible vanishing-cycle nullhomotopy. Those are exactly the data a finite-set theorem would
need in order to handle several such places while retaining the condition at $v_0$. Such a
theorem would define a different admissibility route; current item 7 instead excludes that
output by requiring $P_{\mathrm{nm}}=\{w_0\}$.

### 9.4 No inference from torsion alone

The congruence $A[\mathfrak q]\simeq\bar r$ does not determine the local component of $r_A$.
An unramified residual representation can have crystalline, special, or ramified lifts. Nor does
it prove that $r_A$ is automorphic. The local Hilbert--Blumenthal models identify the lift's component, and the
one-prime theorem supplies automorphy.

Likewise, good reduction at a place above $q$ does not make the $q$-adic representation
unramified. It makes its finite quotients finite flat and its generic representation crystalline.
Unramifiedness at a good place is asserted only away from the coefficient characteristic.

## 10. The modularity transfer

### 10.1 Automorphy of the residual dihedral member

The Hecke character base-changes to $M K'$ by composition with the norm. Since $D_{\mathrm{av}}$
contains $M$ and the point field $K'$ is disjoint from $D_{\mathrm{av}}$, the extension
$M K'/K'$ remains CM quadratic. No normal-closure assertion is needed for this ordinary-form
claim. Quadratic induction gives a cuspidal parallel-weight-two representation

$$
\pi'=\operatorname{AI}_{M K'/K'}(\psi\circ N_{M K'/M}).
\tag{10.1}
$$

Its residual Galois representation is

$$
\operatorname{Ind}_{G_{M K'}}^{G_{K'}}
\bar\chi_{\psi}|_{G_{M K'}}
\simeq\bar r|_{G_{K'}}.
\tag{10.2}
$$

The isomorphism is Mackey induction under the quadratic disjointness. Cuspidality follows
because the conjugate-ratio witness survives on $G_{M K'}$. Thus no nonsolvable base-change
theorem for a general rank-two automorphic representation is being used: automorphy over $K'$
is reconstructed directly from the norm-pulled character.

Because the distinguished completion satisfies $K'_{w_0}=K_{v_0}$, the local scalar
Frobenius, enhanced line, and primary sign of Sections 5.2 and 7.5 are unchanged at $w_0$.
Every other place above $v_0$ was assigned a good minimal seed. This numerical and local
identification does not transport an integral new quotient from $K$ to $K'$. Item 7 requires
Proposition 5.1 to be verified anew for the dihedral packet (10.1) over $K'$, including the
abelian Ihara and branch-correction hypotheses. At every other controlled place, item 7 requires
the character construction together with the proved integral level changes to put the residual
eigensystem in the same named minimal component as $r_A$. In particular, reduction of a
ramified character to an unramified residual character does not by itself lower automorphic
level. Under item 7 these comparisons verify residual automorphy in the sense required by the
deformation problem, which is stronger than saying only that (10.2) comes from some automorphic
form.

### 10.2 The scalar augmentation lemma

The scalar family has nontrivial tame-character fibers of conductor two, whereas the
semistable Tate module in (9.3) lies on its conductor-one augmentation face. Full equality of
the global deformation ring with the Hecke algebra is not known, but the prior reduced
comparison is enough for a characteristic-zero point.

**Lemma 10.1 (scalar augmentation modularity lifting).** Let a one-prime clean datum in residue
characteristic $s\geq7$ be given at a place with $q_v\equiv1\pmod s$, including the enhanced
scalar line, sign, and all hypotheses required for Book 175's conductor-one reduced comparison.
If this face is reached by specializing the scalar family, assume $({\rm RAY}_v)$ as well. Let

$$
r:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
$$

be a lift satisfying the fixed determinant, finite-flat coefficient-prime conditions, named
minimal conditions away from the selected place, and the named conductor-one enhanced special
condition at the selected place, with nonzero rank-one monodromy. Then $r$ is attached to a
cuspidal parallel-weight-two automorphic representation.

**Proof strategy.** Factor the characteristic-zero point through the reduced conductor-one
deformation ring, identify that reduction with the faithful Hecke order, and then compare the
two stable lattices.

**Proof.** The local conditions give a point

$$
x_r:R^{\mathrm{sp},1}\longrightarrow\mathcal O'.
$$

Since $\mathcal O'$ is a domain, $x_r$ kills the nilradical. Book 175 gives the reduced
comparison

$$
\bigl(R^{\mathrm{sp},1}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1}.
\tag{10.3}
$$

Thus $x_r$ occurs in the faithful automorphic carrier at the conductor-one line-special type.
No full scheme-theoretic $R=T$ statement or acting-order augmentation is used: (10.3) is the
direct conductor-one reduced comparison. The projective-complex hypotheses construct its
carrier with no coefficient-algebra Tor, while $({\rm RAY}_v)$ supplies strict specialization
only when the conductor-one face is reached from the scalar family. None of these facts is
inferred from the displayed reduced equality.

Type occurrence identifies the selected line, sign, and determinant; the hypothesis that the
given point has nonzero rank-one monodromy supplies its conductor-one assertion. At good
places the attached automorphic Galois representation and $r$ have the same Frobenius
polynomials. Both are irreducible because their residual representation is absolutely
irreducible. Density and semisimplicity identify their generic fibers. The universal deformation
point identifies the integral strict-equivalence classes; equivalently, two stable lattices with
the same absolutely irreducible reduction are homothetic. Hence the integral representations
are isomorphic. $\square$

The lemma would be false if one merely specialized a nonflat module. It also does not apply in
the distinct-root branch or at $q_v\equiv-1\pmod s$; those are outside Book 175's theorem.

### 10.3 Applying one-prime modularity lifting

Assume item 7 of Section 2.5 has been independently verified for the specialized $A$. Apply
Lemma 10.1 directly to $r_A$. The remaining hypotheses are checked as follows.

- The base $K'$ is totally real.
- The residual representation is (10.2), absolutely irreducible after cyclotomic restriction
  by the joint-cutout disjointness of Lemma 8.1: point-field disjointness suffices in the
  ordinary form, while the stronger top-field disjointness supplies the same conclusion on
  every intermediate field in the Galois form.
- In characteristic $q\geq7$, its cyclotomic image is adequate.
- The adjoint-twist invariant is part of the dihedral and clean ledgers and survives restriction
  because the joint $(\bar r,\bar\epsilon_q)$ image is preserved.
- At $w\mid q$, the representation has compatible finite-flat quotients of weights $\{0,1\}$
  over an unramified base.
- At $w_0$, it lies on the selected augmentation special component; every other place above
  $v_0$ is minimal.
- Every other local condition, determinant, type label, and automorphic localization is the one
  recorded in the clean datum.

Therefore there is a cuspidal parallel-weight-two automorphic representation $\Pi_A$ over $K'$
such that

$$
r_A\simeq\rho^T_{\Pi_A,\mathfrak Q}
\tag{10.4}
$$

integrally after a finite coefficient extension.

Let us spell out the last identification. The point of the common deformation--Hecke ring gives
an automorphic packet whose attached representation $r_{\Pi_A}$ has, at every good $v$, the same
trace and determinant as $r_A$. Hence their semisimplifications agree. If $r_A$ had a stable
line over the fraction field, intersecting and saturating it in a stable lattice would give a
proper stable line in $A[\mathfrak q]$, contradicting absolute irreducibility of $\bar r$.
Thus $r_A$ is irreducible, and the generic isomorphism is an actual isomorphism.

Write $\varpi$ for a uniformizer of the common coefficient DVR after this extension. For
lattices, scale an automorphic stable lattice $L'$ so that $L'\subseteq L=T_{\mathfrak q}A$
but $L'\nsubseteq\varpi L$. Its image in $L/\varpi L$ is a nonzero stable subspace and therefore
the whole space. Nakayama's lemma gives $L'=L$. The finite-flat quotient models at $q$ then
agree by full faithfulness in the clean unramified weight range. This is why (10.4) is integral,
not merely an isomorphism after inverting the coefficient uniformizer.

There is no successive finite-chain argument here. After one change, a second application would
have to retain the first nonminimal condition, contrary to the one-prime boundary of Book 175.

### 10.4 Solvable bridges and descent

Sometimes the clean datum is verified only after a finite solvable totally real extension
$L/K'$. A solvable sheet stabilizer in the Galois approximation datum gives a prime-cyclic tower

$$
K'=L_0\subset L_1\subset\cdots\subset L_m=L.
\tag{10.5}
$$

If $w_0$ remains the selected one-prime place, require it to have a single place in $L$ and
verify the restricted enhanced datum there. Complete splitting would create several fixed
nonminimal places and leave the one-prime theorem. At all places, local parameters are
restricted and checked anew; solvability alone does not preserve conductors, dihedral
irreducibility, or special signs.

Assume in addition that every downward cyclic step is **descent-admissible** in the exact
solvable-descent interface exported by Book 175: the top and intermediate packets are selected
and trace-comparable, every reverse comparison has a strongly cuspidal factor, and all nonsplit
local parameters are
antecedent-complete selected for every fixed-determinant norm antecedent. Whenever an entire
quotient-character fiber is used, require fiber saturation. Also require Galois attachment to
commute with the cyclic comparisons and finite-order twists, and require equality of good
polynomials to identify semisimplifications. These conditions are arithmetic certificates;
they do not follow from the solvability of the sheet stabilizer.

Under that ledger, if modularity lifting over $L$ makes $r_A|_{G_L}$ automorphic, the
representation $r_A$ already extends to $G_{K'}$. Strong multiplicity one identifies Galois
conjugates at each cyclic step, and the extension-comparison lemma selects the unique
quotient-character correction whose attached representation is the next lower restriction.
Iteration gives $\Pi_A$ over $K'$.

Irreducibility at every step, cuspidality, compatible central characters and full local
parameters, and any inner-form discreteness conditions are retained in the same ledger.
Endpoint invariance by itself does not supply coherent descent.

This optional descent route is not used in Theorem 11.2 as stated: its admissibility witness
already verifies item 7 over $K'$. Invoking the route would require replacing that witness by
the entire stepwise ledger above, not merely choosing a solvable stabilizer.

## 11. Recovering residual automorphy at the original prime

### 11.1 Weight-two Galois realization

Two carrier assertions must be kept separate. Before Lemma 10.1 is applied,
$({\rm AUT}_{w_0})$ in item 7 requires an exact compact automorphic localization for the
congruent residual special seed. Even degree and that seed's selected special factor make the
Book 104 one-split carrier available, but all type, saturation, faithful-order, and bad-place
local--global certificates remain part of item 7. The present chapter constructs the carrier
for the different, final characteristic-zero packet $\Pi_A$ after lifting; that later carrier
cannot be used backwards to prove $({\rm AUT}_{w_0})$.

The packet $\Pi_A$ is noncharacter, cuspidal, parallel weight two, and has trivial central
character in the fixed-determinant normalization. Item 6 made $[K':\mathbf Q]$ even, while item
7 retained nonzero conductor-one special monodromy at $w_0$. Thus $(\Pi_A)_{w_0}$ is an
eligible selected Steinberg factor in the sense of Book 104. If the lifting theorem first
produces a totally definite packet, Book 104, Theorem 9.1 first transfers it to this split packet
with the same good polynomials and selected local factor.

Fix a real place $\tau_0$ of $K'$ and take $W=\{w_0\}$. The set $W$ is odd and nonempty.
Book 104, Theorem 9.2 constructs the quaternion algebra $B/K'$ ramified at every real place
except $\tau_0$ and at $w_0$, together with the unique one-split packet

$$
\Pi_B=\operatorname{JL}_B^{-1}(\Pi_A).
\tag{11.0}
$$

The ramification count is
$[K':\mathbf Q]-1+1=[K':\mathbf Q]$, which is even, and the finite ramified place makes $B$
a division algebra. Its Shimura curve is therefore compact. Book 127, Theorem 8.1, applied to
the full component-routing orbit of $\Pi_B$, now supplies the rational rank-two family. This
application retains the component descent, the basic-group determinant datum, an embedding of
the full Hecke-block center, and a number field splitting the selected Schur factor. The carrier
is consequently a theorem, not a further admissibility hypothesis.

Let $E_\Pi$ be a coefficient field containing the Hecke data and all required splitting values.
For every finite place $\lambda$ of $E_\Pi$, the weight-two realization first attaches a
continuous semisimple cohomological representation

$$
\rho^{\mathrm{coh}}_{\Pi_A,\lambda}:G_{K'}\longrightarrow
\operatorname{GL}_2(E_{\Pi,\lambda})
\tag{11.1}
$$

with common good geometric-Frobenius polynomials, inverse-cyclotomic determinant in the trivial
component-character case, total oddness, and good-place compatibility in the proved curve
range. Put

$$
\rho^T_{\Pi_A,\lambda}
=\rho^{\mathrm{coh}}_{\Pi_A,\lambda}(1)
\simeq\left(\rho^{\mathrm{coh}}_{\Pi_A,\lambda}\right)^\vee.
\tag{11.1a}
$$

The displayed isomorphism uses essential self-duality in the present trivial
component-character case. With a nontrivial component character the twist and dual differ by
that character and must not be identified. Here
$\det\rho^T_{\Pi_A,\lambda}=\epsilon_\lambda$.

At this stage the attachment theorem supplies a rational weakly compatible family and stable lattices.
We do not assume that its canonical cohomological lattice has already been identified with a
Tate lattice of $A$. That identification is the cross-prime problem, and it follows from the
$q$-adic isomorphism and common Frobenius polynomials.

The fact that $H^{\mathrm{ten}}$ is defined over $\mathbf Q$ only selects the arithmetic
component of the Hilbert moduli space. It does not descend $A$, $\Pi_A$, $\Pi_B$, or any member
of (11.1) to $\mathbf Q$. The Galois representations in this chapter are representations of
$G_{K'}$, and the residual conclusion remains over $K'$.

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
$A[\mathfrak l]\simeq\bar\rho|_{G_{K'}}$. Proposition 11.1 and the first frame in (9.1) give

$$
\bar\rho^T_{\Pi_A,\widetilde\lambda}
\simeq A[\mathfrak l]\otimes_{k_{\mathfrak l}}k_{\widetilde\lambda}
\simeq\bar\rho|_{G_{K'}}\otimes_k k_{\widetilde\lambda}.
\tag{11.6}
$$

The descended $E_{\mathfrak l}$-form has residual representation exactly
$\bar\rho|_{G_{K'}}$ under the fixed isomorphism $k_{\mathfrak l}\simeq k$.

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
$A[\mathfrak l]$ after the displayed scalar extension, so the residual rank-two factor is
(11.6).  This stable lattice is attached to the rational factor; it need not be an integral
direct factor of $L_{\Pi_A}$. $\square$

This corollary is deliberately at the **actual upper level** of $\Pi_A$. It neither lowers an
extra specialization-dependent special place nor places the eigensystem on the bottom minimal
SP face. A type projector defined only after inverting $\varpi$ also cannot be inserted into
$L_{\Pi_A}$ without a separate integral saturation theorem. Thus the corollary supplies the
nonzero upper occurrence from which a later certified lowering construction starts, not the
endpoint or, when $w_0$ must be lowered, the actual first path carrier.
The particular compact carrier of Section 11.1 is ramified at $w_0$.  Since Book 140 requires
its changing place to be split in the current quaternion algebra, this carrier cannot itself
be used to lower $w_0$.  A later application whose target minimal problem is unramified at
$w_0$ must first construct a path-compatible carrier, with a new primitive packet lattice;
Corollary 11.1A does not provide an integral switch between the two carriers.

### 11.3 The residual potential-modularity theorem

**Theorem 11.2 (conditional residual potential modularity).** Let $K$ be totally real, let
$\ell\geq7$, and let

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(k)
$$

be a two-prime admissible weight-two residual datum of Chapter 2. Then there exist a finite
totally real extension $K'/K$ of even absolute degree and a cuspidal parallel-weight-two
automorphic representation $\Pi$ of $\operatorname{GL}_2(\mathbf A_{K'})$ such that, after
enlarging the coefficient field of $\Pi$ to contain $E$, for a place
$\lambda\mid\mathfrak l$,

$$
\boxed{
\bar\rho|_{G_{K'}}\otimes_k k_\lambda
\simeq\bar\rho^T_{\Pi,\lambda}.}
\tag{11.7}
$$

The weakly compatible family also has the descended $E_{\mathfrak l}$-form whose distinguished
stable lattice reduces exactly to $\bar\rho|_{G_{K'}}$ over $k$.

The field is linearly disjoint from every finite extension included in the avoidance ledger of
the admissibility witness. Thus an additional prescribed field may be avoided only after it is
inserted before specialization and item 7 is verified for an output of that enlarged package.
In the Galois-refined form, the normal closure has the prescribed finite group, is disjoint from
that ledger, and has the prescribed core-free point stabilizer; that stabilizer is solvable only
when the admissibility witness contains a solvable bridge datum. All real places and controlled
finite completions have the exact local behavior specified before specialization. No
automorphic packet or Galois family is asserted to descend from $K'$ to
$K$; in particular, when $K=\mathbf Q$, nothing here descends automorphy back to
$\mathbf Q$.

**Proof strategy.** Construct a weight-two dihedral seed at $q$, put it and the target on a
connected determinant-compatible two-prime Hilbert cover, globalize one point with closure-level
control, transfer automorphy to the specialized abelian variety at $q$, and read the same packet
at $\ell$.

**Proof.** Item 2 supplies $M$ and the compatible corrected relative ray datum; Theorem 4.2
then supplies $\psi$, $C_\psi$, and $\bar r$, and Lemma 4.3 supplies any exact protected split
branch pairs included in that item. Theorem 2.1 supplies the simultaneous
real-multiplication coefficient datum. Proposition 5.1 states the exact
conditional special residual localization. Chapters 6 and 7 construct the smooth geometrically
connected twist and nonempty local neighborhoods on one arithmetic component. By the definition
in Section 2.5, admissibility fixes an output $(K',A)$ of Theorem 8.2 which has all image and
completion controls and for which item 7 has actually been verified. The point gives the exact
frames (9.1).

Automorphic induction over $M K'/K'$ makes $\bar r|_{G_{K'}}$ residually automorphic. Item 7
supplies its exact conditional localization over $K'$. The scalar augmentation lemma makes
$V_{\mathfrak q}(A)$ automorphic and produces $\Pi_A$. Weight-two realization at $\ell$ and the
derived cross-prime comparison give (11.6). Take $\Pi=\Pi_A$. Every field-control
assertion is a conclusion of Theorem 8.2. $\square$

The word “conditional” records two stages of the lifting boundary. The first occurs already at
the selected place. Book 139 does not prove the family $({\rm AIH}_{\mathscr F})$, so
Proposition 5.1 and item 7 are not unconditional; even after those constant rows are granted,
the independent $({\rm TYPE}_{w_0})$, $({\rm SUP}_{w_0})$, $({\rm REC}_{w_0})$,
$({\rm RAY}_{w_0})$, and any required $({\rm AUX}_Q)$ and switched-carrier hypotheses still
have to be verified for the actual localization. The second stage concerns uncontrolled extra
bad primes of $A$, which are known only after specialization. The prior one-prime theorem
neither constructs their exact lower-face classes, flags, and branch corrections nor retains
several fixed nonminimal conditions. Treating both stages as part of “two-prime admissible”
proves the implication in Theorem 11.2 but does not prove that every target is admissible. Once
lifting succeeds, even absolute degree and the retained special place prove final carrier
eligibility in Section 11.1. The catalog objective therefore remains open first in the exact
one-prime localization package and then at actual post-specialization one-prime cleanability.

No uniqueness of $K'$ or $A$ is asserted. Different ray characters, determinant components,
local cycles, or Hilbert specializations generally give different fields and abelian varieties.
What is canonical is the logical transfer: once a specialized point and clean lifting datum are
fixed, the two frames determine which residual members occur at $q$ and $\ell$.

### 11.4 A stronger controlled form

It is useful to record exactly what survives the construction. Suppose
$D_{\mathrm{av}}$ contains the full target and dihedral cutout fields and both cyclotomic
extensions. Then

$$
\bar\rho(G_{K'})=\bar\rho(G_K),
\qquad
\bar r(G_{K'})=\bar r(G_K),
\tag{11.8}
$$

and the same equalities hold for the cyclotomic restrictions. Thus absolute irreducibility,
adequacy, projective type, trace field, and determinant image are unchanged. If selected places
split completely, their local fields, lines, signs, and component labels are literally
unchanged. At general places the double-coset formula records every restriction.

The theorem permits finitely many further closed loci to be avoided, and finitely many locally
realizable completion algebras to be imposed. It does not promise arbitrary degree, a Galois
point field without a Galois presentation, or a solvable normal closure. Those are separate and
often incompatible demands.

## 12. Exceptional cases and failure tests

### 12.1 Coefficient characteristics below seven

The theorem assumes both coefficient characteristics used in uniform lifting are at least
seven. Characteristic five has a genuine icosahedral exception: the natural two-dimensional
representation of the special-linear cover of $A_5$ has surviving adjoint cohomology. Absolute
irreducibility therefore does not imply the adequacy input of the one-prime theorem. In
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

Point-field disjointness $K'\cap D=K$ does not imply that the normal closure of $K'$ is
disjoint from $D$. The normal closure can acquire an intersection invisible in the root field.
If later arguments use all conjugates, elementary fixed fields, or a solvable upper bridge, the
top field must be controlled by a Galois approximation datum.

Nor is disjointness from a projective cutout field enough to preserve the full image. Scalars
and determinants may shrink. The avoidance ledger therefore uses full matrix cutout fields.

### 12.6 Failure of clean modularity lifting

Residual automorphy in an unspecified packet does not verify the exact quaternionic
localization. A conductor number does not identify an irreducible component. Scalar inertia at
$v_0$ does not identify the invariant line, sign, or monodromy. Rational crystallinity at $q$
does not give compatible finite-flat quotients.

In the chosen branch, repeated roots $q_{v_0}\equiv1\pmod q$ destroy the integral root
idempotent, so the scalar line enhancement and primary sign cannot be omitted. At
$q_{v_0}\equiv-1\pmod q$ there is no nontrivial scalar $q$-power tame character, while the
distinct-root branch $q_{v_0}\not\equiv1\pmod q$ is not covered by the prior one-prime theorem.
Wild primitive types, residue characteristic equal to $v_0$, $q$-divisible stabilizers, or a
failure of $({\rm AUT}_{v_0})$, $({\rm TYPE}_{v_0})$, $({\rm SUP}_{v_0})$,
$({\rm REC}_{v_0})$, $({\rm RAY}_{v_0})$, the applicable Ihara and augmentation families,
or the branch-correction and component-support conditions lie outside the theorem. A
nonreduced global conductor-one deformation source is not by itself an obstruction to
pointwise modularity: a characteristic-zero point kills its nilradical. It obstructs only an
unqualified full scheme-theoretic $R=T$ assertion.

In any of these cases, the Hilbert--Blumenthal variety and frames may still exist. What fails is
the transfer of automorphy from $A[\mathfrak q]$ to $V_{\mathfrak q}(A)$.

Even after that transfer, an abstract $\operatorname{GL}_2$ packet need not have a compact
one-split carrier. The present construction records the two facts that make the carrier
available: $[K':\mathbf Q]$ is even and $w_0$ is an eligible selected Steinberg place with
nonzero monodromy. Deleting either fact would stop Chapter 11. With both facts retained, Books 104 and 127 prove the carrier, so it is not an additional failure of the stated theorem.

An extra semistable prime of the specialized $A$ is not automatically a clean local change.
Residual unramifiedness supplies a congruence relation, but exact lowering also needs a
saturated lower-face class, primary--companion flags and pairings, and coherent integral
vanishing-cycle data. Since those primes are not known before specialization, a theorem used to
handle them must construct these data for the actual $A$ rather than include them in an input
ledger. The present one-prime theorem does not contain such a route.

## 13. Dependency and hypothesis audit

### 13.1 The prerequisite interfaces

The declared direct prerequisites are Books 6, 98, 104, 127, 141, 142, 154--157, and 175. Book
175 in turn exposes the load-bearing interfaces from Books 139--140 and 174; they are not
treated as stronger than their stated hypotheses, and its descent clause exposes Book 109's
admissible cyclic interface. Book 6 supplies the exact Grunwald--Wang alternative used in
Lemma 4.3, while Book 98 supplies the Hecke-character interface and Book 156
imports Book 35's reduced characteristic polynomial for endomorphisms of abelian schemes. The
proof uses these prerequisites in distinct roles.

**Hecke characters and automorphic induction.** The character-extension theorem, quadratic
induction matrices, determinant with the quadratic sign, cuspidality criterion, conductor
formulas, local compatibility, coefficient fields, residual irreducibility, and controlled ray
data are used in Chapters 4, 5, and 10. The ray-unit, determinant, and full relative
ray-subgroup compatibility hypotheses are retained.

**CM anti-unit correction.** Lemma 4.1 is proved here in precisely the CM range in which it is
used. Kronecker's theorem makes every ratio $u/u^\sigma$ a root of unity; reduction at one
split prime detects the resulting finite group, and elementary character extension produces
the inverse branch. This proves the unit correction. Lemma 4.1A separately proves the
capitulation-intersection compatibility over $\mathbf Q$; Theorem 4.2 retains it over a general
base.  Lemma 4.3 separately uses Book 6 to globalize full local characters and forms
$\theta/\theta^\sigma$; the Wang exception only doubles a prime-to-$q$ exponent, so it neither
changes the determinant nor erases protected residual values. Chebotarev is taken from its
actual source, Book 142; Book
155 supplies the Galois and solvable approximation refinements. No Kummer congruence
theorem or later congruence-subgroup result is an undeclared input.

**Compact carrier and weight-two Galois realization.** Book 104 first transfers a totally
definite output to the split packet when necessary. Even absolute degree and the eligible
special factor at $w_0$ then satisfy its compact one-split inverse theorem with
$W=\{w_0\}$. The semistable geometry, packet decomposition, and rational extraction of Books 122 and 125--126 feed Book 127, which supplies component descent, the full Hecke block, rank-two
extraction, determinant, oddness, common good Frobenius polynomials, and stable lattices. The
stronger local, compatibility, and integral statements of Books 128--129 and 168 are not silently used:
the comparison here needs only the good rational family, and Proposition 11.1 derives its
relevant integral lattice from $T_{\mathfrak l}A$ and absolute residual irreducibility.

**Dickson classification and adequacy.** Cyclotomic absolute irreducibility in characteristic at
least seven implies adequacy. Image preservation under disjoint base change uses the full
cutout field. Adequacy is not used to infer the separate adjoint-twist vanishing.

**One-prime nonminimal patching.** Book 175's reduced conductor-one comparison, scalar line and
sign, and its exact $({\rm AUT})$, $({\rm TYPE})$,
$({\rm SUP})$, $({\rm REC})$, and $({\rm RAY})$ ledger give Lemma 10.1 and the transfer in
Chapter 10; $({\rm AUX}_Q)$ is retained when patched auxiliary level is removed. The selected
prime satisfies $q_{v_0}\equiv1\pmod q$, and the point has nonzero rank-one monodromy. A
characteristic-zero point kills the possible nilradical, so no full scheme-theoretic ring
equality is asserted. Book 175 still assumes the applicable Book 139 abelian-Ihara family and
does not derive its typed-Ihara or support hypotheses from that family.

**Moret--Bailly approximation.** Smooth geometrically connected point spaces, nonempty local
opens, exact local algebras, total reality, finite disjointness, and closed-locus avoidance give
the ordinary form of Theorem 8.2. No Galois conclusion is attributed to it.

**Galois and solvable refinements.** A supplied full-monodromy Galois presentation gives the
normal closure, exact top local torsors, closure-level disjointness, compatible fixed fields, and
a prime-cyclic upper tower when the stabilizer is solvable. Automorphic descent down that tower
additionally requires the stepwise selected, trace-comparable, strongly cuspidal,
antecedent-complete, and where applicable fiber-saturated certificates. The presentation is
verified geometrically rather than inferred from ordinary approximation, and group solvability
does not supply those arithmetic certificates.

**Two-prime Hilbert--Blumenthal moduli.** Books 156--157 supply the determinant-condition fine
scheme, ordered polarization, inverse-different pairing line, corrected Tate-twisted auxiliary
source, two special-linear frame torsors, the $\mathbf Q$-defined tensor component, and full
product monodromy. The constant oriented level rejected by Book 157 is not used. All bad-prime
and neatness exclusions are retained.

**Local Hilbert--Blumenthal geometry.** Real, good, ordinary, nonordinary finite-flat, and
semistable seed points; residue tubes; exact frames; openness; component bookkeeping; and
persistence give Chapter 7. A seed after local extension is always recorded in the global
completion algebra.

### 13.2 The theorem-by-theorem hypothesis ledger

| Step | Hypotheses retained | Conclusion used |
|---|---|---|
| simultaneous coefficients | both actual residual fields; distinct odd primes; weak approximation; Hilbert--Blumenthal tensor choice | one totally real $E$ receiving both fields, unramified and monodromy-admissible at both primes, with determinant lines |
| dihedral construction | CM quadratic field; full relative ray-subgroup compatibility, including ray units and diagonal $K$-ideal intersections; determinant (4.4); type $(1,0)$; prime-to-$q$ witnesses | cuspidal weight-two induction with controlled residual representation |
| inverse-branch correction | CM quadratic extension; prime-to-$q$ ray-unit obstruction; triviality on diagonal $K$-units; protected witness | the finite anti-unit group is detected at one split prime, and inverse auxiliary characters cancel the obstruction |
| protected Frobenius correction | finitely many split places away from $q$; determinant-compatible residual branch pairs; a $\sigma$-stable protected set; exact Grunwald--Wang, including its possible exponent doubling | an anti-cyclotomic finite-order twist, trivial on $C_K$ and the protected places, imposing the full residual local characters |
| residual irreducibility | conjugate ratio nontrivial after reduction | absolute irreducibility of $\bar r$ |
| cyclotomic adequacy | $q\geq7$; absolute irreducibility on $G_{K(\zeta_q)}$ | adequate cyclotomic image |
| level raising | relation (5.1); $q_{v_0}\equiv1\pmod q$; scalar line; primary sign; full applicable $({\rm AIH}_{\mathscr F})$ family and independent typed rows; saturated maps; normalized branch correction; non-Eisenstein localization | conditional exact line-special residual occurrence |
| two-prime cover | good primes; corrected source $\mathscr L_N^\natural$; self-dual tensor lattice; determinant-compatible local systems | smooth fine moduli and finite étale paired frame cover |
| connected twist | $\mathbf Q$-defined tensor component; full product monodromy; characteristic zero | geometrically connected twisted cover over $K$ |
| local package | one seed satisfying all conditions on the chosen component; odd coefficient primes; $\bar\rho$ unramified above $q$; required integral model | nonempty open neighborhoods with exact frames over the permitted completions |
| ordinary approximation | smooth geometric connectedness; common-degree moving-family presentations of all exact local algebras; even absolute output degree; real opens; finite disjointness | finite totally real point field of even absolute degree with the asserted completions |
| Galois refinement | geometrically connected Galois cover; core-free stabilizer; even fixed-field index; realized top torsors; base-changed connectedness; solvability of $J$ only when a bridge is requested | controlled normal closure and exact fixed-field completions with an even-degree point field; a prime-cyclic upper bridge only in the solvable-$J$ case |
| image preservation | disjointness from full cutout and cyclotomic compositum | unchanged full and cyclotomic images |
| post-specialization level control | actual bad set; lower residual carrier after proved saturated level lowering; $P_{\mathrm{nm}}=\{w_0\}$; every other place on the same named minimal spectator component | one fixed nonminimal problem rather than an unproved finite-set problem |
| one-prime lifting | scalar branch $q_{v_0}\equiv1$; global tame ray character; $({\rm AUT})$, $({\rm TYPE})$, $({\rm SUP})$, $({\rm REC})$, $({\rm RAY})$, and any required $({\rm AUX}_Q)$; reduced conductor-one comparison; finite-flat quotients; named components; nonzero rank-one monodromy of the point | automorphy of the characteristic-zero point $V_{\mathfrak q}(A)$ with conductor-one special monodromy and trivial central character |
| compact curve carrier | even $[K':\mathbf Q]$; eligible selected Steinberg factor at $w_0$; $W=\{w_0\}$; full component-routing and Schur-splitting data | Book 104 one-split packet and Book 127 rational rank-two family over $K'$ |
| cross-prime comparison | noncharacter cuspidal packet; rational rank-two realization; $q$-adic equality after scalar extension; common abelian Frobenius polynomials; absolutely irreducible target torsion | equality after the necessary coefficient extension, an $E_{\mathfrak l}$-form, and exact residual equality over $k_{\mathfrak l}$ for its distinguished lattice |

Every row is used in the indicated direction. In particular, local openness does not prove
global connectedness, and residual image preservation does not prove automorphy.

### 13.3 Circularity audit

The dihedral packet is constructed before the Hilbert--Blumenthal point and independently of
the desired target. Its residual automorphy is therefore a genuine starting point. The
specialized abelian variety is not assumed automorphic. Its $q$-adic automorphy follows from the
one-prime theorem using the dihedral residual packet. Only afterward is the weight-two system at
$\ell$ attached.

The target conclusion (11.7) is never used to choose $K'$, prove connectedness, or select an
auxiliary prime. Adequacy is proved from cyclotomic irreducibility and not from the existence of
Taylor--Wiles primes. The arithmetic distribution theorem selects Frobenius classes only after
the finite-image detector has been constructed. Normal-closure disjointness is imposed on the
generic Galois family before specialization.

There is no appeal to Book 177's potential-modularity theorem, Book 181's later balanced
minimal-lift argument, Book 182's potential-automorphy refinement, or any later
compatible-system, Brauer-descent, or changing-prime theorem. The weakly compatible family used
in Chapter 11 is the weight-two family attached directly to the already automorphic packet
$\Pi_A$.

No later-numbered congruence-subgroup, simultaneous semistable-carrier, or finite-set lifting
manuscript is used. Such a source either depends on this book or lies after it and therefore
cannot close Proposition 5.1 or the post-specialization cleanability clause without a dependency
cycle. Outside the rational-base case of Lemma 4.1A, a future repair must construct the
compatible relative ray datum of Theorem 4.2; in every case it must place
the abelian-Ihara family and the remaining exact one-prime type, support, reciprocity, ray, and
augmentation certificates in an acyclic prior source, and then either produce a specialization
with singleton active set or prove an actual finite-set theorem and enlarge the admissibility
route accordingly. Only then can the lifting inputs be inserted at the boundaries in Sections
5.3, 9.3, and 10.3.

### 13.4 Normalization audit

Arithmetic Frobenius is used in every character value and every covariant Tate-module
polynomial. The cohomological weight-two factor uses geometric Frobenius and is dualized before
comparison with torsion. The determinant of
quadratic induction includes $\eta_{M/K}$. Type $(1,0)$ gives parallel weight two and
cyclotomic determinant through $|\cdot|^{-1}$. The Hilbert torsion pairing takes values in

$$
(\mathfrak d_E^{-1}\mathfrak c^{-1}\otimes k_{\mathfrak p})(1).
$$

The frame groups are special linear because the determinant line is fixed. Covariant Tate
modules have cyclotomic determinant, while the untwisted cohomological factor has
inverse-cyclotomic determinant. At $v_0$, the augmentation
face has conductor one; nontrivial tame characters have conductor two. The two are never
identified. In arithmetic-Frobenius normalization, the invariant line in (5.0) has the
cyclotomic-multiple root. The scalar residual matrix does not choose this line; the enhanced
line does. The primary type chooses the sign, not the polarization pairing.

The auxiliary level source is Tate-twisted as in (1.4); it is not a constant orientation.
Coefficient enlargements preserve rank two by scalar extension. At $\ell$, the packet residual
member is compared with $A[\mathfrak l]$ only after extending both to the enlarged residue
field, while the descended $E_{\mathfrak l}$-form retains the exact original residue field.
The $\mathbf Q$-definition of the tensor component supplies no descent of the specialized
abelian variety or automorphic packet; every attached representation remains a representation
of $G_{K'}$.

Finite flatness is used at the coefficient residue characteristic and unramifiedness only away
from it. Without absolute residual irreducibility, an arbitrary stable lattice would determine
only a residual semisimplification. Here absolute irreducibility and Proposition 11.1 force all
stable lattices to be homothetic to $T_{\mathfrak l}A$, so the exact residual representation is
a conclusion. All normalizations in the proof follow these conventions.

## 14. Conclusion

### 14.1 The two-prime package and its remaining boundary

The two-prime method succeeds because it assigns one task to each prime. At $q$, a rank-one
Hecke character constructed from a supplied compatible corrected relative ray datum over a CM
field gives an explicit dihedral rank-two representation. Its infinity type gives parallel
weight two; its diagonal restriction fixes the determinant; ray data control conductor and local
inertia; a conjugate-ratio witness survives both reduction and cyclotomic restriction; and the
protected anti-cyclotomic Grunwald correction can impose exact residual split branch characters
without changing those data. A
carefully selected scalar prime gives the numerical, enhanced-line, and sign data for the
special localization. The exact integral localization remains conditional
first on the abelian-Ihara family and then on the independent typed-Ihara, support,
reciprocity, ray, augmentation, and faithful-carrier inputs of the one-prime theorem.

At $\ell$, the original residual representation is placed on the same polarized abelian variety.
The determinant-compatible two-prime cover remembers both torsion systems exactly. The
corrected cyclotomic-split or elliptic-source auxiliary level and tensor choice give one
$\mathbf Q$-defined arithmetic
component, and product monodromy makes its twist geometrically connected. Real, ordinary,
local--local, good, and semistable tensor seeds produce genuine open neighborhoods on that one
piece.

Arithmetic approximation then chooses the field rather than demanding a rational point over
the original base. In its Galois-refined form it controls the normal closure, every completion in
the fixed-field diagram, and disjointness from full residual cutout fields. These controls keep
oddness, absolute irreducibility, cyclotomic adequacy, determinants, and local witnesses intact.
The point field is chosen of even absolute degree, and its exact algebra at $v_0$ creates one
distinguished special place while keeping every other place above $v_0$ minimal.

The specialized abelian variety carries the bridge. Once its post-specialization clean datum is
verified, its residual $q$-member is dihedrally automorphic; the scalar augmentation theorem
transfers that automorphy to its $q$-adic Tate module. Weight-two Galois realization and the
derived cross-prime Tate comparison then reads the same packet at $\ell$, and the paired
$\ell$-frame identifies that residual member with the prescribed target.

The selected special factor also supplies the compact carrier: together with even absolute
degree it gives the one-split inverse Jacquet--Langlands datum for $W=\{w_0\}$, after which
Book 127 constructs the rational rank-two family. The $\mathbf Q$-defined Hilbert component
does not descend this packet or family to $\mathbf Q$; the conclusion stays over $K'$.

The proved conclusion is therefore a conditional transfer theorem with an exact boundary. For
$\ell\geq7$, every two-prime admissible weight-two residual datum becomes automorphic over a
controlled finite totally real field. Simultaneous coefficient realization, the correction of
the ray-unit part of a supplied compatible relative datum, determinant lines, components,
normal closures, protected exact split Frobenius branches, the unramified auxiliary frame, and
cross-prime integrality are proved on that domain.

The catalog objective is stronger: every weight-two residual datum in the stated range must be
shown to admit the complete package. Before lifting over a general totally real base, one must
construct the compatible corrected relative ray datum retained by Theorem 4.2; Lemma 4.1 proves
only its unit relation, while Lemma 4.1A closes the rational-base case. At the
lifting boundary, the first missing prior result is the abelian Ihara family used by Proposition
5.1. Granting it does not discharge the independent
$({\rm TYPE})$, $({\rm SUP})$, $({\rm REC})$, $({\rm RAY})$, augmentation, and
switched-carrier clauses at the selected prime. After the complete one-prime package is proved,
one must either prove that a specialization exists with no extra nonminimal Tate-module places,
so that $P_{\mathrm{nm}}=\{w_0\}$, or enlarge the argument using a genuine prior finite-set
theorem which constructs the exact automorphic and vanishing-cycle seeds at every extra active
place without circular use of this potential-modularity conclusion. Every superfluous
dihedral level at a claimed minimal spectator still requires a proved saturated integral
lowering comparison. Until these inputs are available as genuine prior results, Book 178
has not completed the full catalog objective. The source-closed conditional transfer of Theorem
11.2 is **READY** on its exact two-prime-admissible domain; the unrestricted assertion that
every target in the catalog range admits such a package is **NOT READY**.
