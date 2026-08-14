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
   - [The two arithmetic comparisons](#24-the-two-arithmetic-comparisons)
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
5. [Protected local branches and unramifying packets](#5-protected-local-branches-and-unramifying-packets)
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
8. [Mixed Galois-top specialization](#8-mixed-galois-top-specialization)
   - [The avoidance field](#81-the-avoidance-field)
   - [The mixed moving presentation](#82-the-mixed-moving-presentation)
   - [Preservation of residual images](#83-preservation-of-residual-images)
   - [The specialization theorem](#84-the-specialization-theorem)
9. [The Hilbert--Blumenthal bridge](#9-the-hilbert--blumenthal-bridge)
   - [The specialized abelian variety](#91-the-specialized-abelian-variety)
   - [What the two torsion identifications say](#92-what-the-two-torsion-identifications-say)
   - [Local properties of the auxiliary-adic representation](#93-local-properties-of-the-auxiliary-adic-representation)
   - [No inference from torsion alone](#94-no-inference-from-torsion-alone)
10. [The auxiliary componentwise comparison](#10-the-auxiliary-componentwise-comparison)
    - [Automorphy of the residual dihedral member](#101-automorphy-of-the-residual-dihedral-member)
    - [Solvable preparation of the actual active set](#102-solvable-preparation-of-the-actual-active-set)
    - [The avoidance packet and the common definite module](#103-the-avoidance-packet-and-the-common-definite-module)
    - [The auxiliary source patch and descent](#104-the-auxiliary-source-patch-and-descent)
11. [Recovering residual automorphy at the original prime](#11-recovering-residual-automorphy-at-the-original-prime)
    - [Weight-two Galois realization](#111-weight-two-galois-realization)
    - [The cross-prime Tate comparison](#112-the-cross-prime-tate-comparison)
    - [The residual potential-modularity theorem](#113-the-residual-potential-modularity-theorem)
    - [A stronger controlled form](#114-a-stronger-controlled-form)
12. [The target broad-unipotent comparison](#12-the-target-broad-unipotent-comparison)
    - [The actual target active set](#121-the-actual-target-active-set)
    - [Target preparation and the upper packet](#122-target-preparation-and-the-upper-packet)
    - [The common target module and paired source patch](#123-the-common-target-module-and-paired-source-patch)
    - [The restricted special-fibre theorem](#124-the-restricted-special-fibre-theorem)
13. [Exceptional cases and failure tests](#13-exceptional-cases-and-failure-tests)
    - [Coefficient characteristics below seven](#131-coefficient-characteristics-below-seven)
    - [Reducible and cyclotomically reducible images](#132-reducible-and-cyclotomically-reducible-images)
    - [Determinant and pairing failures](#133-determinant-and-pairing-failures)
    - [Component and local-solvability failures](#134-component-and-local-solvability-failures)
    - [Failure of closure-level disjointness](#135-failure-of-closure-level-disjointness)
    - [Failure of arithmetic source patching](#136-failure-of-arithmetic-source-patching)
14. [Proof architecture and hypotheses](#14-proof-architecture-and-hypotheses)
    - [The earlier interfaces](#141-the-earlier-interfaces)
    - [The theorem-by-theorem hypothesis flow](#142-the-theorem-by-theorem-hypothesis-flow)
    - [The noncircular order](#143-the-noncircular-order)
    - [Normalization](#144-normalization)
15. [Conclusion](#15-conclusion)
   - [The mixed two-prime package](#151-the-mixed-two-prime-package)

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
field is the mixed Galois top $F/K$ constructed by the specialization method of Books
154--158. A CM quadratic extension used for
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

The construction has six interacting layers. The residual layer records oddness, absolute and
cyclotomic irreducibility, determinant, finite flatness, and the adjoint-twist invariant. The
dihedral layer records a CM field, Hecke character, conductor, determinant, residual conjugate
ratio, and local behavior. The moduli layer records polarization, neat level, two paired torsion
systems, components, and product monodromy. The local layer records real, integral, ordinary,
nonordinary, and semistable seed points over the permitted completion fields. The first
field layer produces a regular Galois top, split at the protected coefficient and Frey places
and with exact solvable completions at the ramified helper places, while preserving the joint
residual images.
The second field layer prepares the actual active places for the scalar paired rings of Book
176.  At that second layer the arithmetic proof also constructs the two definite coefficient
systems and their common nonzero residual localization.

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
torsion do not make a lift automorphic. In the FLT construction every dyadic place of the
Galois top lies in the auxiliary active set: complete splitting gives the same Tate neighborhood
on every sheet. Consequently no theorem in the argument may ask that exactly one place be
nonminimal.  Chapter 10 applies Book 109 to the full post-specialization set
$P_{\mathrm{aux}}(A_F)$ and then constructs the actual paired definite modules required by
Book 176, Theorem 1.1J.  Chapter 12 repeats the construction in characteristic $\ell$ for the
target active set and applies Book 176, Theorem 1.1K.

Geometric one-place moving constructions and iterative level-lowering arguments are outside
the scope of this book and are unnecessary for its main result.  Once the auxiliary source
patch gives automorphy, even absolute degree and any one special dyadic place let Book 104
construct a compact one-split packet, and Book 127 attaches its rank-two family.

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
6. the adjoint-twist invariant used in the strict relative deformation count vanishes:
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

### 2.4 The two arithmetic comparisons

After Theorem 8.2 specializes the paired-frame space, let $F/K$ be its totally real Galois top,
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
Accidental semistable places and retained places above $3$ may enlarge it.  The set is nevertheless
finite: both $r_A$ and the reference packet are unramified outside finite sets.
The common ordinary finite-flat local problem fixed in Section 7.3 contains both members at
every place above $q$, so no coefficient place belongs to $P_{\mathrm{aux}}(A_F)$.

The first arithmetic comparison is made in residue characteristic $q$.  Book 109, Corollary
14.5 prepares the actual set $P_{\mathrm{aux}}(A_F)$ while preserving the joint
residual--cyclotomic image and the chosen coefficient-prime completions.  On the prepared field,
the scalar desired and avoidance rings of Book 176, Theorem 1.1C are realized by two explicit
coefficient systems on one definite class groupoid.  The norm-pulled dihedral packet, modified
by an anti-cyclotomic character of order $q$, supplies a primitive avoidance eigenvector.  Its
nonzero reduction is the common residual module required by Book 152, Theorem 20.5.  This is
the arithmetic content proved in Chapter 10; it is not an additional hypothesis.

The second comparison is made in residue characteristic $\ell$ after the upper packet has been
recovered.  Chapter 12 enumerates its complete finite bad set.  The places with nonzero
monodromy form $P_{\mathrm{tar}}$; the ramified zero-monodromy places receive exact solvable
unramifying completions before Book 109, Corollary 14.6 performs the scalar target preparation.
All completions above $2\ell$ remain literally unchanged.  The upper packet itself supplies a
primitive vector in the broad-unipotent desired system.  Chapter 12 constructs the common residual definite module and invokes Book 176,
Theorem 1.1K and Corollary 1.1L.  The resulting whole-ring finiteness precedes, and is
independent of, the choice of any characteristic-zero minimal point.

Thus the inputs entering Chapter 10 are exactly the residual datum of Section 2.1, the
auxiliary prime and corrected relative ray datum of Chapters 3--4, the simultaneous coefficient
realization of Theorem 2.1, the determinant-compatible paired-frame space and point-centered
local opens of Books 156--157, and the mixed Galois-top specialization of Chapter 8 with
closure-level disjointness and exact helper completions.  No one-place moving presentation or
later minimal point is used.


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

Several later conditions also eliminate finitely many $q$. The paired source-patching theorem requires
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
and require the simultaneous seed already over
$\mathbf Q_q$. The mixed specialization keeps $q$ split completely, so every top completion remains the
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
inertial distinctions, and the cyclotomic-irreducibility witness are unchanged.  Before applying
the lemma, put in $P$ every place where the target is ramified and every place required to stay
on its original completion.  In the initial squareclass choice of Section 4.7 require $M$ to
split at that finite set, and choose the original CM modulus and the inverse-branch primes away
from it.  Thus the quadratic induction algebra, the original character, and the later
correction are all unramified at a ramified target place, while a place newly ramified by the
corrected dihedral character is not a ramified target place.  The proof of
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

Let $S_{\mathrm{dih}}$ be the finite set of finite places, away from $q$, at which the
quadratic induction algebra, $\psi$, or the correction $\nu$ has nontrivial inertia.  The
preceding choice makes $\bar\rho$ unramified at every member of $S_{\mathrm{dih}}$.  The set is
defined only now, after all ray-class extensions and corrections have been made; no claim that
its support was predicted from the initial modulus is used below.  At $2$, $3$, $\ell$, and
$q$, and at any further place whose original completion is genuinely needed, choose $M$ split
and all finite branch corrections unramified.  These places form the split protected set
$S_{\mathrm{split}}$ and are disjoint from $S_{\mathrm{dih}}$.

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

## 5. Protected local branches and unramifying packets

### 5.1 Branch data at the controlled places

The construction needs no auxiliary level-raising prime. The dihedral member is already
automorphic by induction, and Book 176 compares it with the actual Tate-module point at the
whole active set. What must be fixed before specialization is instead the local paired-frame
datum at each protected rational place and the unramifying packet at each member of
$S_{\mathrm{dih}}$.

At $2$, choose the Frey Tate neighborhood for the target frame and use Lemma 4.3 to impose the
determinant-compatible residual dihedral branch on the same split Tate point. At $\ell$, first
fix the good ordinary replacement when the target residual module came from a multiplicative
curve, then choose $q\nmid\Delta_\ell$ and impose one of the two ordered roots of its
Frobenius polynomial as the protected $q$-branch. Treat a fixed good seed at $3$ in the same
order. At $q$, use the unramified ordinary frame of Section 4.6. Every auxiliary correction is
chosen after the seed whose Frobenius it must match.

These are finitely many split local prescriptions with common determinants, so the protected
anti-cyclotomic correction of Lemma 4.3 realizes them simultaneously without changing the CM
determinant or conjugate-ratio witness. They are input to the point-centered split packets of
Chapter 8 and are the places that remain completely split in the eventual Galois top.

The places in $S_{\mathrm{dih}}$ are treated differently.  There the corrected residual
dihedral representation has genuine inertia, so a good seed over the original completion is
impossible.  Chapter 7 chooses one finite solvable Galois completion field which kills both
residual frames and the finite semisimple inertia of the characteristic-zero reference, and
constructs a good paired seed over that field.  The whole Galois orbit of this seed is a
repeatable local packet.  Chapter 8 puts that exact packet, rather than a fictitious rational
point, into the specialization problem.  No scalar repeated-root congruence, enhanced
one-prime line, unique exceptional sheet, or toroidal connecting slice is used.


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
algebra problem and would not be compatible with the required complete splitting at $q$.


### 7.4 Ramification of the dihedral seed

Fix $v\in S_{\mathrm{dih}}$ and write $K_v$ for the original completion.  The residual local
image of $\bar r$ is monomial, hence solvable.  The target is unramified at $v$ by the choice
made in Section 4.8, so its residual local image is cyclic.  The finite semisimple inertial
image of $r_{\psi,q}$ is also solvable: in any finite local Galois quotient wild inertia is a
$p$-group, tame inertia modulo wild inertia is cyclic, and the residue quotient is cyclic.
This is the ramification filtration of Book 3, and it gives a subnormal series with solvable
successive quotients.

Take the compositum of the finite Galois fields which kill

$$
\bar r|_{G_{K_v}},\qquad
\bar\rho|_{G_{K_v}},\qquad
\text{and the finite semisimple inertia of }r_{\psi,q}|_{G_{K_v}}.
\tag{7.1b}
$$

It is finite, Galois, and solvable over $K_v$.  Over this field both prescribed residual
systems are unramified, indeed trivial, and the characteristic-zero dihedral reference is
unramified.  Book 157, Theorem 9.1 then gives a good tensor seed after a further finite
unramified extension; enlarge once more, still unramified, to split the two seed torsion
systems, their determinant lines, and the corrected auxiliary level.  Choose the unramified
degree divisible by the residue degree of the first compositum.  The resulting compositum

$$
E_v/K_v                                                     \tag{7.1c}
$$

is again finite solvable Galois.  It contains the complete frame field required by Book 157,
not merely an inertial kernel.  Theorem 12.1 of that book supplies a nonempty good
point-centered open

$$
\Omega_v\subset Y^{\mathrm{ten}}(E_v)                       \tag{7.1d}
$$

with both exact paired frames.  We may and do choose this point with field of definition
exactly $E_v$.  Indeed, on a sufficiently small smooth chart contained in $\Omega_v$, an
étale coordinate ranges through an open ball of $E_v$.  The finite Galois extension
$E_v/K_v$ has only finitely many proper intermediate fields, each closed with empty interior
in $E_v$.  Choose the coordinate outside their union.  Since the coordinate is defined over
$K_v$, a point descending to a proper intermediate field would have its coordinate there,
a contradiction.

Consequently the conjugates under
$D_v=\operatorname {Gal}(E_v/K_v)$ are distinct and form a $K_v$-rational reduced packet
whose root algebra is exactly $E_v$.  After shrinking, all its members are good and lie on
the same tensor component.  Because the variety has positive dimension, finitely many nearby
copies of this full-orbit packet can be chosen pairwise geometrically disjoint.  Thus it is a
wholesale-repeatable packet in the sense of Book 154, Lemma 5.2A; its permutation action is
the regular action of $D_v$, rather than an action through a proper quotient.

This construction kills finite semisimple inertia, not Frobenius of infinite order.  That is
exactly what good reduction requires.  After specialization, the Tate-module point and the
dihedral reference are both unramified over the selected top completion $E_v$, and their
common residual $\mathfrak q$-frame is the trivial restriction of $\bar r$.  No descent of
this frame or seed to $K_v$ is asserted.  The local seed records the component but does not
prove automorphy of the specialized $q$-adic point; Chapter 10 supplies that conclusion.


### 7.5 The split special places

At the dyadic controlled place, choose the split semistable tensor Tate point used by Book 158.
Its $q$-adic Tate module has rank-one monodromy and conductor one, whereas its residual
$q$-torsion is the protected unramified branch fixed in Chapter 5. Choose the Tate parameter to
be an $\ell qN$th power with positive valuation, so both residual torsion frames and the
corrected neat level occur on the same point. Pairing fixes the determinant.

The local datum is a point-centered open, not a degree-indexed factorization with one exceptional
sheet. The mixed specialization keeps $2$ completely split in its Galois top. Hence the same Tate
open occurs at every $w\mid2$, and every such $w$ belongs to the post-specialization active set.
Semistability, toric rank, the frames, and the Kummer shell persist after shrinking.

### 7.6 Good and semistable auxiliary conditions

At any other split protected place, use the good, ordinary, nonordinary finite-flat, or semistable
point prescribed in Chapter 5 and Book 158. Each condition is imposed on every sheet above the
place. Exact valuations and nonsplitness require the stated local model, while good reduction,
ordinary type, semistability, frames, and components persist on the point-centered open.


### 7.7 The simultaneous local-neighborhood lemma

**Theorem 7.1 (one-component local package).** Let
$Z\subsetneq Y^{\mathrm{ten}}$ be closed. For every controlled place $v$ of the rational
base, choose either the original completion $\mathbf Q_v$ or one of the exact fields $E_v$
of (7.1c), and suppose there is a point

$$
y_v\in(Y^{\mathrm{ten}}\setminus Z)(K_v')
$$

carrying the assigned real, good, ordinary, nonordinary finite-flat, or split-semistable model
and both exact frames. Then there is a nonempty point-centered open
$\Omega_v\subset(Y^{\mathrm{ten}}\setminus Z)(K_v')$ on which the selected local
condition, frames, ordered polarization, auxiliary level, and tensor component all persist.

**Proof.** Use a real component at infinity, a smooth residue tube at good places, the
Hasse-invariant open in the ordinary case, a fixed special-fiber tube in the nonordinary case,
and fixed valuation and Kummer shells in the semistable case. The two frame isomorphism schemes
are finite etale, so local sections exist after shrinking around the common point. Intersect
these neighborhoods with the complement of $Z$. $\square$

The point-centered hypothesis is load-bearing: separately nonempty opens can lie on different
ordinary or determinant components and have empty intersection. At a member of
$S_{\mathrm{split}}$ the witness is required over the original completion.  At a member of
$S_{\mathrm{dih}}$ the extension $E_v$ is part of the datum, and every conjugate packet and
its multiplicity are carried into the moving presentation of Chapter 8.


## 8. Mixed Galois-top specialization

### 8.1 The avoidance field

Let $D_{\mathrm{av}}/\mathbf Q$ be a finite Galois compositum containing the full joint
cutout fields of $(\bar\rho,\bar\epsilon_\ell)$ and $(\bar r,\bar\epsilon_q)$, the normal
closure of the CM induction field, the determinant and component fields, every protected
character witness, and every finite extension already constructed whose intersection would
shrink a required image.  The later preparation fields are not known yet and are avoided in
their own Book 109 applications. Full
matrix cutouts are used; projective cutouts would not preserve central scalars or determinants.

### 8.2 The mixed moving presentation

Book 158's stated specialization theorem is deliberately split-only, so it is not invoked at
a member of $S_{\mathrm{dih}}$.  Instead we apply the exact-local-algebra method from which its
split proof was obtained.  For $v\in S_{\mathrm{dih}}$ put

$$
e_v=[E_v:\mathbf Q_v],\qquad D_v=\operatorname {Gal}(E_v/\mathbf Q_v).
$$

Book 154, Lemma 5.2A applies because the complete Galois packet (7.1d), not one distinguished
factor, may be repeated wholesale.  Choose a sufficiently large common degree $d$, divisible
by every $e_v$.  At a helper place prescribe the root algebra

$$
\mathcal E_v=E_v^{\,d/e_v};                                 \tag{8.1a}
$$

at a finite member of $S_{\mathrm{split}}$ prescribe $\mathbf Q_v^d$, and at the real place
prescribe $\mathbf R^d$.  The norm--Abel argument of that lemma moves pairwise disjoint copies
of every packet onto one global curve and puts all these configurations in fibers of one
degree-$d$ pencil.  Taking the line bundle still more positive makes length-four separation
available.  The simple-ramification and distinct-branch-value conditions used in Book 158,
Lemma 4.1 are then nonempty Zariski-open conditions on the pencil, so weak approximation keeps
the prescribed local packets while choosing a simply branched pencil.  Its geometric and
arithmetic monodromy is $S_d$.

Let $\widetilde T\to H$ be the $S_d$-Galois closure and let $T$ be the quotient by a point
stabilizer.  At $v\in S_{\mathrm{dih}}$, the $d$ roots in (8.1a) carry $d/e_v$ copies of the
regular $D_v$-set.  Hence the local specialization homomorphism

$$
G_{\mathbf Q_v}\longrightarrow D_v\longrightarrow S_d       \tag{8.1b}
$$

is faithful on $D_v$, its root algebra is exactly (8.1a), and the splitting field of the local
top fiber is exactly $E_v$.  At a protected split or real place this homomorphism is trivial.
Thus these fibers, together with their evaluated packet points, form a realized Galois
approximation datum in the sense of Book 155, Chapter 6.  Equivariant local constancy retains
both the top torsor and every evaluated local open.

Apply Book 155, Theorems 7.1 and 8.1 to this datum, including connectedness after base change
to $D_{\mathrm{av}}$ among the Hilbert conditions.  The output is a totally real Galois
extension $F/\mathbf Q$ with group $S_d$, disjoint from $D_{\mathrm{av}}$, and a point obtained
from the root field and then base-changed to $F$.  Since $d\ge2$, $[F:\mathbf Q]=d!$ is
positive and even.  Every $v\in S_{\mathrm{split}}$ splits completely in $F$, whereas for
every $v\in S_{\mathrm{dih}}$ and every $w\mid v$ one has

$$
F_w\simeq E_v.                                               \tag{8.1c}
$$

The resulting point

$$
y_F\in Y^{\mathrm{ten}}(F)
\tag{8.1}
$$

has associated abelian variety $A_F/F$ with both exact residual frames and every named local
model. At a protected split place every sheet lies in the chosen original-completion open; at
a helper place it lies in a conjugate of (7.1d).  In particular all $w\mid2$ are split Tate
places.  The construction is entirely on the fine interior.  The only nonsplit data are the
exact finite local algebras (8.1a), whose common moving presentation has just been proved.

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

Thus the closure-level avoidance in Section 8.2 preserves the full and cyclotomic residual images,
absolute irreducibility, adequacy, determinant image, adjoint-twist invariants, and the
protected conjugate-ratio witness.

### 8.4 The specialization theorem

**Theorem 8.2 (mixed two-prime specialization).** Retain the rational-base residual datum,
compatible corrected relative ray datum, simultaneous coefficient realization, paired-frame
space, the original-completion opens at $S_{\mathrm{split}}$, and the exact solvable packets
at $S_{\mathrm{dih}}$. Then the mixed specialization of Section 8.2 supplies $F$ and $A_F$ with

$$
A_F[\mathfrak l]\simeq\bar\rho|_{G_F},
\qquad
A_F[\mathfrak q]\simeq\bar r|_{G_F},
\tag{8.3}
$$

preserves both joint residual images, and places every dyadic sheet in the split Tate open.
The field is totally real, Galois, of positive even degree, and disjoint from
$D_{\mathrm{av}}$.  Every protected place splits completely.  At every
$v\in S_{\mathrm{dih}}$, every top completion is the selected $E_v$; there $A_F$ has good
reduction, both residual frames are trivial, and $r_{\psi,q}|_{G_{F_w}}$ is unramified.

The theorem proves the geometric specialization and exact local frames. It does not yet prove
that $V_{\mathfrak q}(A_F)$ is automorphic. That assertion begins only after the actual set
$P_{\mathrm{aux}}(A_F)$ is known; Chapter 10 prepares precisely that set and constructs the
required common automorphic module.

**Proof.** Book 157 supplies all the point-centered local opens.  Book 154, Lemma 5.2A gives
their common repeatable-packet presentation; the simple-branch refinement and Book 155,
Theorems 7.1 and 8.1 give the totally real Galois top with (8.1c) and closure-level
disjointness.  Pulling back the universal paired tuple gives (8.3), and Lemma 8.1 gives the
image assertions.  The final helper-place assertions are the construction of (7.1c)--(7.1d)
and persistence of good reduction. $\square$


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
component selected before specialization.  In particular, if $w$ lies above
$v\in S_{\mathrm{dih}}$, then $F_w=E_v$, $A_F$ has good reduction, and both $r_A$ and the
dihedral reference are unramified with the same trivial residual frame.  Such a helper place
does not enter the auxiliary active set merely because the original character was ramified.

List every actual bad place of $r_A$ and compare it with the norm-pulled dihedral reference.
This determines $P_{\mathrm{aux}}(A_F)$. No place is removed from that set merely because it
was not predicted before specialization.  At a member of this set the residual reference is
locally monomial, hence its actual finite image is solvable-dihedral in the sense of Book 109,
Section 14.1.  This observation is what permits preparation of the actual set rather than a
set chosen in advance.

### 9.4 No inference from torsion alone

The congruence $A_F[\mathfrak q]\simeq\bar r|_{G_F}$ does not determine the local components
of $r_A$ and does not prove its automorphy. The local models record the desired components;
the scalar paired rings, common definite module, and source support constructed in Chapter 10
transfer residual automorphy to this particular characteristic-zero point. Separate one-place
level changes are not used.


## 10. The auxiliary componentwise comparison

### 10.1 Automorphy of the residual dihedral member

Base-change the Hecke character to the CM compositum over $F$ by the norm. Theorem 8.2's
closure-level disjointness keeps that compositum quadratic over $F$ and preserves the protected
conjugate-ratio witness. Quadratic induction therefore gives a cuspidal parallel-weight-two
packet $\pi'_F/F$ with

$$
\bar r^T_{\pi'_F,\mathfrak Q}
\simeq\bar r|_{G_F}
\simeq A_F[\mathfrak q].
\tag{10.1}
$$

This is a direct reconstruction of automorphic induction over $F$, not an appeal to a
nonsolvable base-change theorem.  Its determinant is $\epsilon_q$, because norm pullback
preserves (4.4), and its coefficient-prime factors are the ordinary finite-flat factors of
Section 4.6.  The full and cyclotomic residual images are unchanged by Lemma 8.1.

At every finite place the residual representation in (10.1) has monomial image.  Its actual
local image is consequently cyclic, dihedral, or a scalar enlargement of one of those groups.
Thus it lies in the solvable selected range of Book 109, Section 14.1.  This verification is
uniform over the actual active set; no prediction of that set entered the construction of
$A_F$.

### 10.2 Solvable preparation of the actual active set

Put

$$
P=P_{\mathrm{aux}}(A_F).
\tag{10.2}
$$

Let $Z$ contain every coefficient place above $q$, every ramified place of $r_A$ or the
dihedral characteristic-zero representation outside $P$, and every remaining controlled
place.  At a coefficient place prescribe the split completion.  A dyadic place in $P$ is a
split Tate place for $A_F$ and an unramified principal place for the protected dihedral
reference; hence its preparation can be chosen unramified.  Every other dyadic place is put in
$Z$ with its already chosen split or harmless unramified completion.  In particular no local
prime-cyclic refinement contains a ramified dyadic quadratic step.

At a place above $S_{\mathrm{dih}}$ both characteristic-zero representations are already
unramified by (8.1c), so it is either absent from $Z$ or is protected by the identity
completion $F_w$.  Nothing in the auxiliary comparison requires the original rational place
to split in $F$: the bottom component is principal, restriction through every later local
tower stays principal, and the exact residual frame was fixed before specialization.

Let $B_{\mathrm{aux}}/F$ be the Galois compositum of the avoidance field of Section 8.1, the
full joint cutout of $(\bar r|_{G_F},\bar\epsilon_q)$, the full target cutout, the cyclotomic
fields already named, and the finite fields recording the protected component and coefficient
data.  Apply Book 109, Corollary 14.5 to the actual representation
$\bar r|_{G_F}$, to $P$, to these protected completions, and to both characteristic-zero
representations $r_A$ and $r_{\psi,q}|_{G_F}$.  The local solvability hypothesis is the
monomial-image calculation of Section 10.1.  We obtain a totally real prime-cyclic tower

$$
F=F_0\subset F_1\subset\cdots\subset F_s=F^{\mathrm{aux}}
\tag{10.3}
$$

of positive even degree, layerwise disjoint from $B_{\mathrm{aux}}$.  Write

$$
P^{\mathrm{aux}}_{\mathrm{top}}
=\{w:w\text{ is a place of }F^{\mathrm{aux}}\text{ above some }v\in P\}.
\tag{10.3a}
$$

Every $w\in P^{\mathrm{aux}}_{\mathrm{top}}$ satisfies

$$
\bar r|_{G_{F^{\mathrm{aux}}_w}}=1,
\qquad
Q_w=|k_w|\equiv1\pmod q,
\tag{10.4}
$$

and the semisimple inertial parts of both named characteristic-zero representations are
trivial there.  Every place above $q$ splits throughout (10.3).  Thus the selected ordinary
finite-flat factor at $q$ is literally unchanged.  A dyadic completion changes only when it
was placed in $P$ with the displayed unramified preparation; the Tate monodromy remains
nonzero under restriction, while its residual action becomes scalar.  These temporary dyadic
extensions will disappear when the final packet descends through (10.3).

The layerwise disjointness has three consequences that will be used separately.  It preserves
absolute irreducibility of $\bar r$ and of its restriction to the $q$-cyclotomic field; hence
the adequate image and the Taylor--Wiles detector remain available.  It preserves the target
frame, although the target representation is not the coefficient-characteristic residual
representation in this patch.  Finally it keeps the CM compositum quadratic and retains the
prime-to-$q$ conjugate-ratio witness, so the base change of $\pi'_F$ is cuspidal at every
stage.

The local cyclic ledger is also explicit.  At a split protected place the same selected
principal, special, finite-flat, or dyadic factor is simply repeated.  At a nonsplit active
place the two parameters at the top of the local tower have trivial semisimple inertia: the
reference has zero monodromy and is unramified principal, while $r_A$ is unramified principal
or special according as its monodromy is zero or nonzero.  Descending one prime-cyclic local
layer, two character lines either extend separately or are exchanged in a quadratic layer;
the latter extension is dihedral.  Nonzero monodromy forces the special case.  Induction down
the local tower therefore keeps every extension and every quotient-character twist in the
principal, special, or constructed dihedral range.  The only excluded case would be a
ramified dyadic quadratic layer, which the preceding choice removed.  At the fresh
ramification witnesses for (10.3), and away from $P\cup Z$, both representations are
unramified.  This proves selected-safety on the entire controlled set, not only at its split
members.  At the bottom, the local models of Chapters 7--9 put every member of $Z$ in one of
the same principal, special, ordinary finite-flat, or constructed dihedral classes, so no
unverified protected component is hidden in this argument.

Base change through each cyclic layer now applies to $\pi'_F$.  Local parameters restrict,
the central character is pulled back by the norm, and the attached representation is
$r_{\psi,q}|_{G_{F_i}}$.  Residual irreducibility rules out an isobaric two-character endpoint,
so every member is cuspidal.  The representation $r_A$ is simply restricted through the same
tower; its determinant remains $\epsilon_q$ and its coefficient-prime finite-flat condition is
unchanged because the coefficient places split.

### 10.3 The avoidance packet and the common definite module

The base-changed packet is residually correct but is unramified at the prepared active places.
Book 176's avoidance source requires an actual characteristic-zero packet with tame
eigencharacters of order $q$.  We now construct it without adding another active place.

Let $M^{\mathrm{aux}}=MF^{\mathrm{aux}}$.  At
$w\in P^{\mathrm{aux}}_{\mathrm{top}}$, the quadratic algebra
$M^{\mathrm{aux}}\otimes_{F^{\mathrm{aux}}}F^{\mathrm{aux}}_w$ is split.  Indeed, an element
of the nonsplit Weil coset acts by an off-diagonal matrix in (4.15), whereas (10.4) says that
the whole residual action is the identity.  Choose the two branches $u,u^\sigma$ above $w$.
Since $Q_w\equiv1\pmod q$, choose

$$
\theta_w:k_w^\times\longrightarrow\boldsymbol\mu_q
\tag{10.5}
$$

of exact order $q$, and prescribe $\theta_w$ at $u$ and $\theta_w^{-1}$ at $u^\sigma$.
Choose its normalization so that a generator of the $q$-part of $k_w^\times$ maps to the fixed
primitive root $\zeta_q$.

These local characters globalize within the ray modulus supported on the branches above $P$.
Work in the relative ray class quotient obtained by dividing the ray idele class group of
$M^{\mathrm{aux}}$ by the diagonal image of $C_{F^{\mathrm{aux}}}$.  The prescribed inverse
branch product is already trivial on that diagonal.  Its only principal relation is detected
on a unit $a$ by $a/a^\sigma$, which is a root of unity because $M^{\mathrm{aux}}$ is CM.
The disjointness in (10.3), with the CM and cyclotomic fields included in
$B_{\mathrm{aux}}$, implies $\zeta_q\notin M^{\mathrm{aux}}$.  Thus this root of unity has
order prime to $q$, and every order-$q$ character in (10.5) kills it.  The relative ray exact
sequence now puts the local rule on a subgroup of the finite relative ray class group.
Divisibility of $\boldsymbol\mu_{q^\infty}$ extends it across the $q$-primary quotient; take
the extension trivial on the prime-to-$q$ quotient.  This produces an anti-cyclotomic
finite-order Hecke character $\xi$ of $M^{\mathrm{aux}}$, unramified outside the chosen ray
modulus, such that

$$
\xi|_{C_{F^{\mathrm{aux}}}}=1,
\qquad
\xi_u=\theta_w,
\qquad
\xi_{u^\sigma}=\theta_w^{-1}.
\tag{10.6}
$$

It is chosen trivial at the places above $q$.  At a protected conjugate-ratio witness outside
$P^{\mathrm{aux}}_{\mathrm{top}}$ it is also trivial; if that witness itself is active, its
prime-to-$q$ value cannot be cancelled by the prescribed $q$-power correction.  All values of
$\xi$ have $q$-power order, so $\bar\xi=1$ at the coefficient prime.  Consequently

$$
\pi_0=
\operatorname {AI}_{M^{\mathrm{aux}}/F^{\mathrm{aux}}}
\bigl((\psi\circ N_{M^{\mathrm{aux}}/M})\xi\bigr)
\tag{10.7}
$$

is an actual cuspidal parallel-weight-two packet, has determinant $\epsilon_q$, reduces to
$\bar r|_{G_{F^{\mathrm{aux}}}}$, retains the selected ordinary finite-flat factor above $q$,
and has avoidance type $\theta_w\oplus\theta_w^{-1}$ at every
$w\in P^{\mathrm{aux}}_{\mathrm{top}}$.  Cuspidality cannot
be lost: the protected conjugate-ratio witness has prime-to-$q$ order, whereas the correction
has $q$-power order.

Choose one finite $q$-adic coefficient field containing $E_{\mathfrak q}$, the values of
$\pi_0$, and $\boldsymbol\mu_q$, and extend both representations and all local lattices to its
ring of integers.  Reduction of the $q$-power values of $\xi$ is still $1$, so the common
residual representation is just the scalar extension of (10.4).  Absolute irreducibility,
the determinant line, and the selected local factors are preserved under this coefficient
extension.

Because $[F^{\mathrm{aux}}:\mathbf Q]$ is even, let $D^{\mathrm{aux}}$ be the quaternion algebra
ramified at every real place and at no finite place.  Global Jacquet--Langlands transfers
$\pi_0$ to $D^{\mathrm{aux},\times}$.  Choose a compact open level containing the newvectors
and the active types.  Choose a fresh split unramified place $a$ whose residue cardinality is
neither $0$, $1$, nor $-1$ modulo $q$, and pass to a sufficiently deep principal congruence
subgroup at $a$.  The level is then neat, while its index in the hyperspecial compact is prime
to $q$.  Apply the integral averaging idempotent for the trivial quotient representation.
This recovers the hyperspecial packet block at $a$, so the Galois condition there remains
unramified, while the projective arithmetic stabilizers of the finer class groupoid are
trivial.  The construction is common to both coefficient systems.

At $w\in P^{\mathrm{aux}}_{\mathrm{top}}$ take the two exact lattices

$$
L_w^{\mathrm{av}}
=\operatorname {Ind}_{B(k_w)}^{\operatorname {GL}_2(k_w)}
(\theta_w\otimes\theta_w^{-1}),
\qquad
L_w^{\mathrm{des}}
=\operatorname {Ind}_{B(k_w)}^{\operatorname {GL}_2(k_w)}1.
\tag{10.8}
$$

Since every $q$th root of unity is $1$ modulo the coefficient uniformizer, finite induction
gives a canonical equivariant identification

$$
L_w^{\mathrm{av}}/\varpi
\simeq L_w^{\mathrm{des}}/\varpi.
\tag{10.9}
$$

Use the same named selected lattice at every unchanged place and the same central character.
The tensor product of (10.9) is therefore an identification of coefficient systems on the
one neat class groupoid, including all local intertwiners.

Localize each of the two integral definite modules at the common non-Eisenstein residual
ideal.  Every characteristic-zero factor of its faithful Hecke image is a noncharacter
weight-two packet, and all of its nonminimal places are among the principal, special, or tame
dihedral places just listed.  Book 170, Theorem 16.1 therefore attaches the Hecke-valued
Galois representation on each side and the surjection from the corresponding represented
deformation ring.  Its coefficient-prime factorization and its principal, special, and
finite-type inertia theorems show that these maps factor through the named local sources.
Thus the two modules carry actual local--global source actions; these actions and their
finite-level augmentation maps are included in the marked data below.

Choose a simultaneous eigenvector in the transferred $\pi_0$-packet and scale it to be
primitive in its saturated integral eigenlattice.  Its reduction is nonzero.  Localizing at
its residual Hecke ideal and applying Book 152, Proposition 20.1 identifies that reduction
with a nonzero vector in the intrinsic common residual module:

$$
0\ne\bar f\in\bar P_0.
\tag{10.10}
$$

This is the required occurrence; it is not inferred from equality of dimensions.  For every
Taylor--Wiles set, take the old packet and the ordered regular refinement selected by its two
distinct residual Frobenius roots.  The corresponding vector remains primitive.  The
diamond action is a torsor because the base level is neat.  The primary--companion pairing is
the perfect definite pairing with inverse diamonds, and the desired and avoidance lattices
reduce to the same pairing by (10.9).

At a Taylor--Wiles prime, write $\bar\alpha_v,\bar\beta_v$ for the two ordered roots and
$\bar s_v=\bar\alpha_v\bar\beta_v$.  Book 152, Section 17.2's invariant Gram calculation gives

$$
\bar s_v\bar D_v
=-(\bar\alpha_v-\bar\beta_v)^2,
\tag{10.10a}
$$

so $D_v$ is a unit.  The remaining selected-support condition is also automatic in this
regular situation.  A class in the oriented new quotient would, by local--global
compatibility, have special local parameter.  Its two residual Frobenius roots have ratio
$Q_v$, hence ratio $1$ modulo $q$; they would coincide, contrary to the Taylor--Wiles
regularity.  Thus the selected primary and companion localizations are generated by the old
image.  Book 152, Theorem 16.1 and Section 20.4 therefore identify the oriented modules on
both sides with the fixed modules at the common neat level.  This is the uniform-minimal-control
alternative of Book 152, Proposition 20.6.  Hence all diamond ranks equal the one positive
integer $\dim_k\bar P_0$, and Proposition 20.6 retains a cofinal constant-rank family together
with the coefficient lattices, pairings, adjoints, Hecke labels, and augmentation maps.

### 10.4 The auxiliary source patch and descent

**Theorem 10.1 (actual auxiliary componentwise comparison).** For the mixed-top variety
$A_F$ of Theorem 8.2, the representation $r_A=V_{\mathfrak q}(A_F)$ is automorphic over $F$.
More precisely, the tower (10.3), the packet (10.7), and the definite modules of Section 10.3
satisfy every hypothesis of Book 176, Theorem 1.1J.  That theorem constructs the auxiliary
componentwise source patch over $F^{\mathrm{aux}}$, and Book 109, Proposition 14.4 descends
the resulting packet to a cuspidal parallel-weight-two packet $\Pi_A/F$ with

$$
V_{\mathfrak q}(A_F)
\simeq\rho^T_{\Pi_A,\mathfrak Q}
\tag{10.11}
$$

after one finite coefficient extension.  The isomorphism carries a stable lattice to a
homothetic copy of $T_{\mathfrak q}A_F$.

**Proof strategy.**  The field preparation supplies the scalar local charts, the modified
dihedral packet supplies one genuine avoidance vector, and the definite class groupoid turns
that vector into the common positive residual module.  Paired Taylor--Wiles selection and
source patching then prove support for the whole desired ring.  Descent is performed only after
the top packet attached to $r_A$ has been obtained.

**Proof.**  We match the four clauses of Book 176, Theorem 1.1J.

For its first clause, (10.3)--(10.4) preserve the full joint residual--cyclotomic image, while
$r_A$ retains determinant $\epsilon_q$ and the selected ordinary finite-flat condition at the
split coefficient places.  Its inertia is unipotent at every active place.  The final
paragraph of Section 10.2 verifies selected-safety at every split and nonsplit member of
$P\cup Z$, including all dyadic and coefficient-prime components.

For the second clause, $\pi_0$ in (10.7) is the required actual cuspidal reference packet.
Equations (10.6)--(10.9) give its determinant, residual representation, coefficient-prime
condition, and order-$q$ avoidance type at every active place.

For the third clause, $D^{\mathrm{aux}}$ is totally definite and the common level is neat, so
the coefficient-independent projective stabilizers have order prime to $q$.  The two exact
active lattices, common central character, primitive eigenlattice, perfect companion pairing,
named operators, and local--global source actions were constructed in Section 10.3.
Equation (10.10) proves the common residual localization nonzero at every regularly refined
level, and the unit Gram calculation supplies the fixed-rank alternative of Book 152,
Proposition 20.6.

It remains to verify the fourth clause, which is the global source-patching input.  At each
active place (10.4) puts the residual tame pair in the scalar chart, and Book 176, Theorem
1.1C identifies the desired and avoidance residual functors inside the same unrestricted
matrix functor.  The unchanged determinant, dyadic, coefficient-prime, and ramification
factors were restricted above to their one named formally smooth or geometrically integral
selected components.  Book 176, Lemma 1.1F therefore gives the avoidance domain, the reduced
equidimensional desired source, their common nilpotent residual quotient, and the
component-bijective specialization.

The cyclotomic image of $\bar r$ has order prime to $q$: its projective image is dihedral of
order prime to $q$, and its scalar kernel lies in the prime-to-$q$ group $k_\psi^\times$.
Averaging therefore proves that it has no nontrivial $q$-power quotient, kills the required
first cohomology, and shows that a trivial quotient of a nonzero stable underlying-prime-field
adjoint subspace would extend to an invariant functional on the full trace-zero adjoint,
contradicting absolute irreducibility.  Book 141, Proposition 9.2 and Corollary 10.3 give
semisimple spanning and a regular detector; enlarge the coefficient residue field once so all
the finitely many detecting eigenvalues split.  These are exactly the four image hypotheses of
Book 143, Section 14.1.  We impose no extra splitting prescription on the Taylor--Wiles
primes.  Hence Book 143's detector fiber is nonempty for every surviving strict relative class
and its padding fiber is nonempty as well.  The two residual local functors are
identically embedded, so Book 143, Proposition 15.1 gives one strict relative Selmer group.
Take the old framed set $T$ to be nonempty and to contain every conditioned place with nonzero
local defect.
The remaining finite defects vanish by construction, Theorem 4.2 together with the preserved
joint image gives
$H^0(F^{\mathrm{aux}},\operatorname {ad}^0\bar r(1))=0$, and oddness contributes $-1$ at
each real place.  Book 143, Theorem 15.2 therefore selects one ordered $Q_N$ for both
problems; padding $h$ if necessary gives

$$
q_0=h+|T|-1-[F^{\mathrm{aux}}:\mathbf Q]\ge0.
\tag{10.12}
$$

Put $m=|T|$ and $d=[F^{\mathrm{aux}}:\mathbf Q]$.  The complete old framed local product has
dimension $1+3m+d$: every fixed-determinant factor away from $q$ contributes three relative
directions, and the selected coefficient-prime factors contribute the additional local
degrees.  Consequently

$$
\dim R_{\mathrm{loc}}^\bullet[[y_1,\ldots,y_{q_0}]]
=(1+3m+d)+(h+m-1-d)
=h+4m
=\dim\mathcal O[[z_1,\ldots,z_h,w_1,\ldots,w_{4m-1}]].
\tag{10.13}
$$

This is the sharp source equality of Book 176, Proposition 1.1G; the scalar active tangent
directions already lie in the old framed product and are not counted twice.

Book 152, Theorem 20.5 applies to the modules already constructed, and its Proposition 20.6
gives the cofinal fixed positive rank.  Book 144, Theorem 17.1 supplies the uniform global
source-presentation bounds; the local sources are complete noetherian quotients with the fixed
presentations above, the modules have fixed rank, and every reduction at a fixed precision is
over a finite ring.  Thus the finite-shadow condition is proved, and Book 144, Theorem 18.2
therefore retains one paired diagonal path, all $4|T|-1$ frame variables, the common-quotient
residual module, the pairings, and exact module coinvariants.  Setting the diamond characters
and the added frame variables equal to their base values is exactly the represented
finite-level deformation functor, so Book 144, Theorem 17.1(4) gives represented-ring
recovery, and Lemma 18.1 retains it on the paired path as required in Book 176, Proposition
1.1G.  Thus every antecedent of Book 176, Theorem
1.1J has been proved.

Theorem 1.1J and Book 176, Theorem 1.1H now give a nilpotent kernel from the entire desired
ring to its finite automorphic action.  The point $r_A|_{G_{F^{\mathrm{aux}}}}$ therefore
factors through that action and is attached to a cuspidal weight-two packet at the top of
(10.3).

Finally apply Book 109, Proposition 14.4.  Determinants and central characters match under
restriction and norm pullback; the residual image stays irreducible; the real discrete-series
selector is repeated; local--global attachment holds at every layer; and Section 10.2 proved
the full selected extension and antecedent fibers.  Since $r_A$ is already defined over $F$,
it selects the correct quotient-character antecedent at every downward step.  The top packet
therefore descends through (10.3) to $\Pi_A/F$.  This descent removes all temporary dyadic
completion changes.  Absolute residual irreducibility makes stable lattices unique up to
homothety, proving the integral assertion in (10.11). $\square$

The theorem treats the entire actual active set simultaneously.  Since every $w\mid2$ is a
member of $P$ in the split Tate construction, replacing it by a singleton would contradict
the local geometry rather than simplify the proof.


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

**Theorem 11.2 (the upper target packet and its primitive definite localization).** Retain the
coefficient DVR at $\widetilde\lambda\mid\ell$ and its uniformizer $\varpi$.  The packet
$\Pi_A/F$ of Theorem 10.1 has a stable lattice reducing to
$\bar\rho|_{G_F}$, has the named signed-special factor at every place above $2$, and has the
selected weight-$\{0,1\}$ finite-flat factor at every place above $\ell$.

Let $D^{\mathrm{tar}}/F$ be ramified at every real place and at no finite place.  It exists
because $[F:\mathbf Q]$ is even.  The Jacquet--Langlands transfer of $\Pi_A$ to
$D^{\mathrm{tar},\times}$ occurs at a compact open which may be shrunk at a fresh split
unramified place to become neat.  If $M^{\mathrm{up}}$ is the resulting finite free integral
definite module and $\mathfrak m_{\ell,A}$ is the maximal ideal obtained from the packet
character, then

$$
M^{\mathrm{up}}_{\mathfrak m_{\ell,A}}/\varpi\ne0.
\tag{11.6a}
$$

The same packet has a primitive localization in the compact one-split curve carrier of
Section 11.1.  In both carriers the associated rational rank-two factor has a stable lattice
whose residual representation is (11.6).

**Proof.**  The local assertions follow from (9.2), Theorem 10.1, and Proposition 11.1.  At a
dyadic split Tate place monodromy is nonzero and the selected line and sign are the ones fixed
in Chapter 7.  At a coefficient place the completion was never changed in the auxiliary
preparation, so the selected finite-flat lattice is the original one.

Global Jacquet--Langlands transfers the weight-two discrete series at all real places to
$D^{\mathrm{tar},\times}$ and leaves every finite component unchanged.  Choose a nonzero
simultaneous eigenvector in its one-dimensional packet eigenspace.  Its intersection with the
integral definite module is a saturated eigenlattice; after scaling, the vector is primitive.
Its reduction is nonzero and is supported at $\mathfrak m_{\ell,A}$, proving (11.6a).
The identical saturated-intersection argument applies to the curve carrier.  Proposition 11.1
identifies every stable lattice in the rational Galois factor with the scalar extension of
$T_{\mathfrak l}A_F$ up to homothety, so its reduction is (11.6). $\square$

The theorem is deliberately at the actual upper level.  The dyadic signed-special factors
will remain fixed in the target comparison; only the genuinely excess non-dyadic special
places will enter its active set.

### 11.3 The residual potential-modularity theorem

**Theorem 11.3 (mixed-top residual potential modularity).** Let $K=\mathbf Q$,
let $\ell\ge7$, and let $\bar\rho$ be the Frey signed-special residual datum of Section 2.1.
Construct the auxiliary dihedral representation at $q$ from the rational-base compatible ray
datum of Chapter 4, impose the protected local branches and unramifying packets of Chapter 5,
and let $F$ and $A_F$ be the mixed Galois-top output of Theorem 8.2. Then there is a cuspidal
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
Galois, of positive even degree, completely split at every member of
$S_{\mathrm{split}}$, has completion $E_v$ at every place above
$v\in S_{\mathrm{dih}}$, and is disjoint from the full avoidance field fixed before
specialization.

**Proof.** Theorem 4.2 and Lemma 4.3 construct the dihedral seed and its protected local
branches. Theorem 2.1 supplies the simultaneous real-multiplication coefficient datum.
Books 154--157 and Theorem 8.2 supply $F$, $A_F$, both exact frames, the exact helper
completions, and image preservation.
Automorphic induction gives (10.1). Sections 10.2--10.3 construct the auxiliary preparation,
the actual avoidance packet, and the nonzero common definite module.  Theorem 10.1 applies
Book 176's source-patching theorem and descends the resulting packet, making
$V_{\mathfrak q}(A_F)$ automorphic. Book 104 supplies a compact one-split carrier using any
one dyadic special place, Book 127 attaches its rank-two family, and Proposition 11.1 identifies
the $\ell$-adic residual member with the first frame in (9.1). $\square$

The construction does not reduce the active set to a distinguished place. Indeed,

$$
\{w:w\mid2\}\subseteq P_{\mathrm{aux}}(A_F),
\qquad
\#\{w:w\mid2\}=[F:\mathbf Q]\ge2.
\tag{11.8}
$$

One-place moving geometry is unnecessary because the paired source patch treats all these
places on one common residual module.


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
places in $S_{\mathrm{split}}$ split completely, so their local fields, lines, signs, and
component labels are literally unchanged on every sheet.  At a helper place the completion is
the selected finite solvable field $E_v$ and the good unramified frame of Section 7.4 is
literally retained on every top sheet.

The theorem permits finitely many further closed loci and finite avoidance fields to be named
before the mixed pencil is chosen.  Its nonsplit completion algebras are exactly the wholesale
repetitions (8.1a); no arbitrary fixed-multiplicity local algebra is asserted.

## 12. The target broad-unipotent comparison

### 12.1 The actual target active set

The upper packet of Theorem 11.2 is now an arithmetic input already constructed over $F$.
For every finite $v\nmid\ell$, let

$$
\operatorname {WD}_v(\Pi_A)=(s_v,N_v)                       \tag{12.1}
$$

in the fixed geometric-Frobenius normalization.  Book 61, Theorem 11.1 and Section 11.4
apply to the Tate module of $A_F$: $s_v(I_v)$ is finite, $N_v^2=0$, and the representation is
ramified exactly when $s_v(I_v)\ne1$ or $N_v\ne0$.  Consequently the complete finite bad set
away from $2\ell$ is the disjoint union

$$
\begin{aligned}
P_{\mathrm{tar}}
 &=\{v\nmid2\ell:N_v\ne0\},\\
Z_{\mathrm{tar}}^{\mathrm{ram}}
 &=\{v\nmid2\ell:N_v=0,\ s_v(I_v)\ne1\}.
\end{aligned}                                                \tag{12.2}
$$

No third kind of bad place is omitted.  The first set contains every retained multiplicative
place above $3$ and every accidental potentially multiplicative place away from $2\ell$.
The second set contains every potentially good but ramified place not already protected at a
coefficient or dyadic place.  Both sets are finite and are defined from the actual upper
packet, not from the pre-specialization ledger.

For each $v$ in their union we now choose an exact finite solvable Galois field.  A finite
quotient of $G_{F_v}$ is solvable: its wild inertia is a finite group of residue-characteristic
power order, inertia modulo wild inertia is cyclic, and the decomposition quotient is cyclic.
Thus the field cut out by the full residual representation
$\bar\rho|_{G_{F_v}}$ is solvable.  The same ramification filtration, applied to the finite
group $s_v(I_v)$ together with a sufficiently large finite Frobenius quotient normalizing it,
gives a finite solvable Galois extension which kills the full finite inertial parameter.

At $v\in P_{\mathrm{tar}}$, take their compositum and adjoin an unramified extension of degree
divisible by the order of $|k_v|$ in $\mathbf F_\ell^\times$.  Call the result $E_v^+$.  At
$z\in Z_{\mathrm{tar}}^{\mathrm{ram}}$, take the analogous compositum and call it $H_z$;
no residue-cardinality enlargement is needed there.  Then

$$
\begin{array}{ll}
\bar\rho|_{G_{E_v^+}}=1,\qquad |k_{E_v^+}|\equiv1\pmod\ell,\qquad
s_v|_{I_{E_v^+}}=1,\qquad N_v\ne0,
   &v\in P_{\mathrm{tar}},\\[2mm]
\bar\rho|_{G_{H_z}}=1,\qquad s_z|_{I_{H_z}}=1,\qquad N_z=0,
   &z\in Z_{\mathrm{tar}}^{\mathrm{ram}}.
\end{array}                                                   \tag{12.3}
$$

The first line is special with trivial semisimple inertia: restriction leaves monodromy
nonzero (a change of tame generator can only rescale it by a nonzero scalar).  The second line
is genuinely unramified.
We do not claim to kill a characteristic-zero Frobenius of infinite order; the full finite
datum killed in (12.3) is the residual local image and the finite semisimple inertial
parameter, precisely the datum whose disappearance makes an $N=0$ Weil--Deligne parameter
unramified.

At a place above $2$ retain the named dyadic signed-special factor, and at a place above
$\ell$ retain the selected weight-$\{0,1\}$ finite-flat factor.  These completions will stay
split in both preparation stages.  Once (12.3) has been globalized, the broad problem imposes
only tame-unipotent inertia with characteristic polynomial $(X-1)^2$ at the places above
$P_{\mathrm{tar}}$, the two protected conditions above $2\ell$, and the unramified condition
everywhere else.  Setting inertia equal to the identity at every active place gives the
canonical closed quotient

$$
R^{\mathrm{uni}}(P_{\mathrm{tar}})
\twoheadrightarrow R^{\mathrm{SP}}.                          \tag{12.4}
$$

There need not be such a quotient from the upper packet's enhanced special-branch ring.

### 12.2 Target preparation and the upper packet

Let $Z_{\mathrm{tar}}$ consist of $Z_{\mathrm{tar}}^{\mathrm{ram}}$, every place above
$2\ell$, every additional protected split place, and every named determinant or component
place outside $P_{\mathrm{tar}}$.  Prescribe $H_z$ at a ramified $N=0$ place and the identity
completion $F_z$ at every place above $2\ell$.  Let $B_{\mathrm{tar}}/F$ be the Galois
compositum of the full joint cutout of
$(\bar\rho|_{G_F},\bar\epsilon_\ell)$, the avoidance field of Chapter 8, and all finite
component and coefficient fields actually being protected.

Apply Book 109, Lemma 14.2 directly to the finite solvable local fields (12.3), to the identity
fields above $2\ell$, and to $B_{\mathrm{tar}}$, requiring its fresh ramification witnesses to
avoid the finite bad set of $\Pi_A$.  It gives a totally real prime-cyclic tower, layerwise
disjoint from $B_{\mathrm{tar}}$,

$$
F=F_0^{\mathrm{ram}}\subset\cdots\subset
F_a^{\mathrm{ram}}=F^{\mathrm{ram}},                         \tag{12.5}
$$

whose endpoint completions are exactly $E_v^+$ above $P_{\mathrm{tar}}$, exactly $H_z$ above
$Z_{\mathrm{tar}}^{\mathrm{ram}}$, and exactly $F_z$ above $2\ell$.  In particular every
dyadic and coefficient place splits throughout (12.5).  The local tensor formula of that
lemma records every multiplicity; no choice of one favorable prime above a controlled place is
being made.

The packet $\Pi_A$ base-changes through (12.5) within Book 109's selected range.  We verify
this before using the result.  At a member of $P_{\mathrm{tar}}$, $N_v\ne0$ forces every
restriction and every extension across a prime-cyclic local layer to be special.  At a place
above $2\ell$ the component is repeated unchanged.  Every further identity-protected place
is likewise one of the named principal, special, or good unramified components already fixed
by the local models and Theorem 11.2; no unspecified ``component datum'' is being inserted.
At a member of
$Z_{\mathrm{tar}}^{\mathrm{ram}}$, the $N=0$ parameter is selected rather than an omitted
primitive-wild type.  Indeed, the original specialization made $3$ split completely and chose
there either a good seed or a tensor-Tate semistable seed.  The former is unramified and the
latter has nonzero monodromy, so no place of residue characteristic $3$ belongs to
$Z_{\mathrm{tar}}^{\mathrm{ram}}$; residue characteristic $2$ was excluded by definition.
At residue characteristic at least $5$, first separate the reducible and irreducible Weil
representations.  A reducible $s_v$ is a sum of two characters and hence is in the selected
principal range.  For irreducible $s_v$, its projective image is finite.  Indeed, a positive
power of Frobenius centralizes the finite inertial image, so its matrix commutes with the image
of both inertia and Frobenius and is scalar by Schur's lemma.  Inertia is normal in the finite
projective image and the quotient is cyclic.  The local ramification filtration makes this
projective image solvable, so the $A_5$ alternative in the finite-subgroup classification is
impossible.  If projective wild inertia is nontrivial,
its image has order divisible by the residue characteristic, which excludes $A_4$ and $S_4$
in residue characteristic at least $5$.  If projective wild inertia is trivial, projective
inertia is cyclic; neither $A_4$ nor $S_4$ has a nontrivial cyclic normal subgroup with cyclic
quotient, while trivial inertia would make the parameter unramified and reducible.  Thus the
irreducible case has dihedral projective image.  Clifford theory identifies it with induction
from a quadratic character, and any ramified quadratic extension is tame because the residue
characteristic is odd.  The bottom parameter is therefore principal or constructed
tame-dihedral; Book 81, Theorem 8.1 shows that its restriction across each cyclic local layer
is again selected.  These are exactly Book 109's selected cases; no primitive exceptional
parameter has been hidden in $Z_{\mathrm{tar}}^{\mathrm{ram}}$.

This argument also checks the complete extension fibers required for descent.  If the upper
restriction is irreducible, Schur's lemma makes every extension a quotient-character twist of
the known extension, hence again dihedral.  If it is a sum of two lines, then across an odd
prime cyclic layer the lines extend separately; across a quadratic layer they extend
separately or are exchanged and give the same dihedral class.  Quotient-character twists stay
in those classes.  There is no ramified dyadic quadratic layer.  At the fresh ramification
witnesses for (12.5), and at every place outside the original finite bad set, $\Pi_A$ was
unramified.  Hence all bottom and intermediate components in the first tower are selected and
trace-comparable, not merely the endpoint components.  Determinants correspond by norm,
the real weight-two selector is repeated, and joint-image disjointness preserves cuspidality.
Write the endpoint packet as $\Pi^{\mathrm{ram}}$.

At this point the exhaustive effect of the first tower is

$$
\begin{array}{c|c}
w\mid P_{\mathrm{tar}} & \Pi^{\mathrm{ram}}_w\text{ special, }\bar\rho_w=1,
 |k_w|\equiv1\pmod\ell,\\
w\mid Z_{\mathrm{tar}}^{\mathrm{ram}} & \Pi^{\mathrm{ram}}_w\text{ unramified},\\
w\mid2 & \text{the original signed-special factor},\\
w\mid\ell & \text{the original finite-flat factor},\\
\text{every other finite }w & \Pi^{\mathrm{ram}}_w\text{ unramified}.
\end{array}                                                   \tag{12.5a}
$$

The last row follows by exhaustion: an original bad place occurred in (12.2) or above
$2\ell$, and restriction of an unramified parameter stays unramified even when the field
extension itself ramifies.

Now apply Book 109, Corollary 14.6 in target mode over $F^{\mathrm{ram}}$ to the places above
$P_{\mathrm{tar}}$, with every place above $2\ell$ protected and split.  Its residual local
hypothesis holds because the first row of (12.5a) is already trivial.  We obtain a second
totally real prime-cyclic tower

$$
F^{\mathrm{ram}}=F'_0\subset\cdots\subset F'_t=F^{\mathrm{tar}},              \tag{12.6}
$$

again disjoint layer by layer from the enlarged joint avoidance field.  Let
$P^{\mathrm{tar}}_{\mathrm{top}}$ be the places of $F^{\mathrm{tar}}$ above
$P_{\mathrm{tar}}$.  Then every place above $2\ell$ is still split, while

$$
\bar\rho|_{G_{F^{\mathrm{tar}}_w}}=1,
\qquad Q_w\equiv1\pmod\ell
\quad(w\in P^{\mathrm{tar}}_{\mathrm{top}}).                 \tag{12.6a}
$$

Book 109, Proposition 14.4 applies to the second tower by the same special-versus-unramified
calculation, now with the unramified-away statement already proved in (12.5a).  Base-changing
$\Pi^{\mathrm{ram}}$ gives

$$
\Pi^{\mathrm{up}}
=\operatorname {BC}_{F^{\mathrm{tar}}/F^{\mathrm{ram}}}(\Pi^{\mathrm{ram}}).  \tag{12.6b}
$$

It is special at every member of $P^{\mathrm{tar}}_{\mathrm{top}}$, has the unchanged
dyadic and coefficient-prime factors, and is unramified away from
$P^{\mathrm{tar}}_{\mathrm{top}}\cup\{w:w\mid2\ell\}$.  Therefore it is genuinely an
actual point of Book 176's broad tame-unipotent problem, clause by clause.

### 12.3 The common target module and paired source patch

Let $D^{\mathrm{tar}}_{+}/F^{\mathrm{tar}}$ be ramified at every real place and at no finite
place.  Transfer $\Pi^{\mathrm{up}}$ to this totally definite algebra.  Choose a common compact
open containing its newvectors.  At a fresh unramified split place $a$, choose
$Q_a\not\equiv0,1,-1\pmod\ell$ and shrink to a sufficiently deep principal congruence subgroup.
The index in the hyperspecial compact is prime to $\ell$, so the integral averaging idempotent
for the trivial quotient representation recovers the hyperspecial block.  Thus the level is
neat and its coefficient-independent projective stabilizers are trivial, while the represented
Galois condition at $a$ remains unramified.

Enlarge the coefficient DVR once so that it contains $\boldsymbol\mu_\ell$ and all split
regular eigenvalues used below; extend the target representation, deformation problems, and
integral packet lattice simultaneously.  We continue to write $\mathcal O$, $\varpi$, and $k$
for the enlarged data.  This is a finite faithfully flat coefficient extension, so finiteness
of the resulting represented ring descends to the original coefficient DVR.

At $w\in P^{\mathrm{tar}}_{\mathrm{top}}$, choose a tame character

$$
\vartheta_w:k_w^\times\longrightarrow\boldsymbol\mu_\ell
\tag{12.7}
$$

of exact order $\ell$, which exists by (12.6a), and use
the normalization sending a chosen generator of the $\ell$-part of $k_w^\times$ to
$\zeta_\ell$.  Put

$$
L_w^{\mathrm{des}}
=\operatorname {Ind}_{B(k_w)}^{\operatorname {GL}_2(k_w)}1,
\qquad
L_w^{\mathrm{av}}
=\operatorname {Ind}_{B(k_w)}^{\operatorname {GL}_2(k_w)}
(\vartheta_w\otimes\vartheta_w^{-1}).
\tag{12.8}
$$

The upper special packet has a nonzero Iwahori vector in the first lattice.  Use the same
selected dyadic, coefficient-prime, determinant, and central-character lattices on both sides.
Because $\bar\vartheta_w=1$, finite induction yields a marked equivariant identification of
the two reductions in (12.8), compatible with the selected intertwiner.  Tensoring over the
active set gives one residual coefficient system on the neat definite class groupoid.

On each localized integral module, the faithful Hecke image has only noncharacter weight-two
generic factors: a character factor would make the absolutely irreducible residual ideal
Eisenstein.  The selected local types are exactly the controlled principal, special, tame
dihedral, dyadic, and coefficient-prime types already named.  Book 170, Theorem 16.1 attaches
the Hecke-valued representation and the represented deformation-ring surjection on both the
desired and avoidance sides.  Its local factorization statements put these maps through the
specified broad-unipotent, avoidance, signed-special, and finite-flat sources.  We retain
these genuine local--global source actions and their augmentation maps as part of every
finite-level marked diagram.

Choose an upper simultaneous eigenvector and scale it to be primitive in its saturated desired
eigenlattice.  Its reduction is nonzero.  Book 152, Proposition 20.1 identifies that reduction
with the intrinsic common localized residual module, so

$$
\bar P^{\mathrm{tar}}_0\ne0.
\tag{12.9}
$$

This proves nonvanishing before any point of the minimal quotient has been chosen.  At every
Taylor--Wiles set take the upper oldform with its regular ordered refinements.  Neatness makes
the diamond fibers torsors, the standard primary--companion definite pairing is perfect, and
Book 152's formula

$$
\bar s_v\bar D_v
=-(\bar\alpha_v-\bar\beta_v)^2
\tag{12.9a}
$$

makes the Gram determinant a unit.  If the selected oriented new quotient were nonzero,
local--global compatibility would give a special local parameter; its residual Frobenius-root
ratio would be $Q_v\equiv1\pmod\ell$, contradicting the distinct Taylor--Wiles roots.  Thus
the selected-support condition holds for the primary and companion factors.  Book 152,
Theorem 16.1 and Section 20.4 give minimal control.  Theorem 20.5 constructs the two
positive-rank systems, and Proposition 20.6 identifies all their ranks with the rank of one
fixed minimal-in-the-Taylor--Wiles-level module.  All paired finite shadows, pairings, adjoints,
operators, and augmentations survive on a cofinal constant-rank family.

We next verify the source-patching hypotheses.  At the active places, (12.6a) puts the two local
problems in Book 176's scalar pair; the desired broad-unipotent and avoidance functors have the
same embedded residual functor.  The unchanged dyadic signed-special and coefficient-prime
finite-flat factors are the same named geometrically integral or formally smooth selected
factors on both sides.  Book 176, Theorem 1.1C and Lemma 1.1F therefore supply the flat
Cohen--Macaulay avoidance domain, the reduced equidimensional desired source with
component-bijective specialization, and their common residual quotient with nilpotent kernels.

The preserved cyclotomic image of $\bar\rho$ satisfies Book 143's split-image hypotheses.
Here is the extra verification beyond the word “adequate.”  Dickson's classification has
prime-to-$\ell$ dihedral and exceptional branches, where averaging proves the
underlying-prime-field no-trivial-quotient condition.  In the remaining branch Book 141,
Section 10.1's projective lifting lemma supplies a normal $\operatorname {SL}_2(k_0)$.  The trace-zero
adjoint for this group is simple in characteristic $\ell\ge7$: the upper and lower root
matrices and their bracket generate its three weight directions from any nonzero vector.
After restriction of scalars, every composition factor of a stable underlying-prime-field
subspace is a conjugate of this nontrivial adjoint factor.  It therefore has no trivial
quotient.  Book 141, Theorem 10.4 gives the cohomology and no-$\ell$-quotient clauses, and
Corollary 10.3 supplies regular detectors.
After one common coefficient extension all detector eigenvalues lie in the residue field.
Thus all four conditions of Book 143, Section 14.1 hold in every Dickson branch.  The residual
local functors are identically embedded, so their strict-at-$T$
relative Selmer groups and detector maps agree.  Take $T$ to be nonempty, to contain all old
finite defects, and, if necessary, to contain one of the already protected dyadic places.
The remaining defects vanish, (2.3) is preserved by the joint-image disjointness, and oddness
gives the real contribution.  The detector and padding fibers of Book 143, Theorem 15.2 are
therefore nonempty by its adequate split-regular detection theorem.  One ordered set $Q_N$
kills both relative dual Selmer groups, and padding gives

$$
q_0=h+|T|-1-[F^{\mathrm{tar}}:\mathbf Q]\ge0.
\tag{12.10}
$$

With $m=|T|$ and $d=[F^{\mathrm{tar}}:\mathbf Q]$, the selected fixed-determinant old local
product on either side has dimension $1+3m+d$.  Therefore

$$
\dim R_{\mathrm{loc}}^\bullet[[y_1,\ldots,y_{q_0}]]
=1+3m+d+q_0
=h+4m
=\dim\mathcal O[[z_1,\ldots,z_h,w_1,\ldots,w_{4m-1}]].
\tag{12.10a}
$$

This verifies the sharp balanced source equality, with every partial-frame variable included.

The common modules of the preceding paragraphs now satisfy every hypothesis of Book 152,
Theorem 20.5.  Book 144, Theorem 17.1 supplies uniform global source-presentation bounds; with
the fixed module rank, these make the sets of truncated marked diagrams finite.  Book 144,
Lemma 18.1 and Theorem 18.2 retain one synchronized path,
the common-quotient residual module, all $4|T|-1$ frame coordinates, and exact module
coinvariants.  On represented deformation rings, augmenting the diamond characters and the
added frame variables is exactly restriction to the base problem, so the universal property
and Book 144, Theorem 17.1(4) give exact represented-ring recovery at every level; Book 144,
Lemma 18.1 retains those marked maps.  These are all the antecedents of Book 176, Proposition
1.1G and Theorem 1.1K.

**Theorem 12.1 (actual target source patch).** Over $F^{\mathrm{tar}}$, the broad desired
ring and its actual finite definite Hecke action satisfy

$$
R_{F^{\mathrm{tar}}}^{\mathrm{uni}}(P^{\mathrm{tar}}_{\mathrm{top}})
\longrightarrow
\mathbb T_{F^{\mathrm{tar}}}^{\mathrm{uni}}(P^{\mathrm{tar}}_{\mathrm{top}}),
\tag{12.11}
$$

with nilpotent kernel.  The whole broad ring is finite over the coefficient DVR, and every
homomorphism from it to a characteristic-zero field factors through the automorphic action.
Moreover the quotient

$$
R_{F^{\mathrm{tar}}}^{\mathrm{uni}}(P^{\mathrm{tar}}_{\mathrm{top}})
\twoheadrightarrow R_{F^{\mathrm{tar}}}^{\mathrm{SP}}
\tag{12.12}
$$

is obtained by imposing trivial inertia at the active places.

**Proof.**  Apply Book 176, Theorem 1.1K with bottom field $F^{\mathrm{ram}}$ and target-mode
tower (12.6).  Sections 12.1--12.3 verify, respectively, the broad local problem, the
target-mode field and selected upper packet, and every definite-module and paired-shadow
hypothesis.  More explicitly, its first clause is supplied by the special factors
of (12.6b), their cyclotomic determinant, and the primitive desired vector used in (12.9).  Its
second clause is supplied by the literal splitting in both (12.5) and (12.6), which preserves the named
dyadic signed-special and coefficient-prime finite-flat factors.  Its third clause is the
selected split-and-nonsplit cyclic calculation of Section 12.2, together with the attached
residual representation and the represented local--global source actions supplied in Section
12.3 by Book 170, Theorem 16.1.  The exhaustion (12.5a) and its persistence through (12.6)
prove the remaining part of that clause: the upper packet is unramified away from the active,
dyadic, and coefficient-prime places.  Its fourth clause
is supplied by neatness, the coefficient-independent stabilizers, (12.8)--(12.9), the perfect
companion systems, the fixed-rank argument (12.9a), the verified relative detector and padding
fibers, and exact represented-ring and module recovery.  Thus no antecedent of Theorem 1.1K
remains as a separate input.

That theorem applies Book 176, Theorem 1.1H to the broad desired source.  Avoidance
faithfulness transfers through the common residual module to full desired support; exact module
and represented-ring recovery then give the nilpotent kernel in (12.11).  The finite Hecke
action and the nilpotent filtration make the whole broad ring finite.  The local functoriality
in Section 12.1 gives (12.12).  Finally a field-valued point kills the nilpotent kernel and
hence factors through the finite automorphic action.  These last two conclusions are also the
specialized statements of Book 176, Corollary 1.1L. $\square$

The only characteristic-zero point used in this proof is the independently constructed upper
packet (12.6b), and it is used solely to prove (12.9).  It is not a point of the minimal quotient
selected by a later finiteness argument.  Whole-ring finiteness is proved before any such point
is considered.

### 12.4 The restricted special-fibre theorem

The preceding theorem has two outputs with different purposes.  Its ring-theoretic output is
the finite special fibre needed to construct a minimal point; its support output proves
automorphy after such a point has been constructed.  Keeping both outputs attached to the same
map (12.11) avoids a second patch.

**Theorem 12.2 (restricted signed-special finite fibre and retained point support).** There is
a finite totally real field $F^{\mathrm{tar}}/\mathbf Q$ such that:

1. $2$ and $\ell$ split completely in $F^{\mathrm{tar}}$, and both
   $\bar\rho|_{G_{F^{\mathrm{tar}}}}$ and
   $\bar\rho|_{G_{F^{\mathrm{tar}}(\zeta_\ell)}}$ are absolutely irreducible;
2. restriction of the fixed cyclotomic determinant $\epsilon_\ell$, the named dyadic
   signed-special conditions, the selected weight-$\{0,1\}$ finite-flat conditions above $\ell$,
   and the unramified
   conditions elsewhere defines the represented ring
   $R_{F^{\mathrm{tar}}}^{\mathrm{SP}}$; and
3. the whole represented special fibre, including its nilpotents, is finite:

   $$
   \dim_k
   \bigl(R_{F^{\mathrm{tar}}}^{\mathrm{SP}}/
   \varpi R_{F^{\mathrm{tar}}}^{\mathrm{SP}}\bigr)<\infty.
   \tag{12.13}
   $$

In addition, retain the broad ring, the quotient (12.12), and the finite action (12.11).
Every characteristic-zero point of $R_{F^{\mathrm{tar}}}^{\mathrm{SP}}$, whenever one is
chosen, is also a point of the broad ring and therefore factors through the retained finite
automorphic action.

**Proof.**  Complete splitting follows from the identity completions in (12.5) and the
target-mode splitting in (12.6); layerwise joint-image disjointness gives the two
irreducibility statements.  The local definition of the quotient in (12.12) is
exactly the deformation problem in item 2.  There is no suppressed upper ramification behind
the word ``elsewhere'': places in $Z_{\mathrm{tar}}^{\mathrm{ram}}$ became unramified in the
second row of (12.5a), original good places and fresh globalization witnesses are covered by
its last row, and the second tower preserves unramifiedness.  Thus the upper point really lies
on the broad ring from which (12.12) is taken.  Theorem 12.1 makes the whole broad ring finite over
the coefficient DVR, so its quotient $R_{F^{\mathrm{tar}}}^{\mathrm{SP}}$ is finite as well;
equivalently, this is the finite-fibre conclusion of Book 176, Corollary 1.1L.  Reduction
modulo $\varpi$ proves (12.13).  If the coefficient extension of Section 12.3 enlarged the
original DVR, finite faithful descent gives the same module-finiteness, and hence the same
finite-special-fibre assertion, over the original coefficients.  A characteristic-zero field
kills the nilpotent
kernel of (12.11).  Composing a point of the signed-special quotient with (12.12) therefore
gives the asserted factorization and automorphy. $\square$

The three numbered assertions are precisely the restricted special-fibre property
$({\rm SF}_{\mathrm{SP}})$.  Its proof uses no characteristic-zero minimal point.  The final
paragraph is the retained target support datum: it applies uniformly to every later
characteristic-zero minimal point without rerunning Taylor--Wiles patching.

## 13. Exceptional cases and failure tests

### 13.1 Coefficient characteristics below seven

The two source patches assume that both coefficient characteristics are at least
seven. Characteristic five has a genuine icosahedral exception: the natural two-dimensional
representation of the special-linear cover of $A_5$ has surviving adjoint cohomology. Absolute
irreducibility therefore does not imply the adequacy input of the lifting theorem. In
characteristics two and three, additional failures occur in projective classification,
semisimple spanning, signs, finite-flat theory, and stabilizer orders.

Nothing here proves the result at five by replacing adequacy with a slogan such as “large
image.” A separate five-adic theorem would have to isolate or calculate the exceptional branch.

### 13.2 Reducible and cyclotomically reducible images

If $\bar\rho$ is reducible, the non-Eisenstein Hilbert and quaternionic localizations used in
the proof are unavailable. If it is absolutely irreducible over $K$ but reducible over
$K(\zeta_\ell)$, Clifford theory identifies a quadratic induced branch. The cyclotomic image is
then reducible and cannot be declared adequate.

The same test applies to $\bar r$. A dihedral representation can be absolutely irreducible over
$K$ and become reducible after cyclotomic restriction. The explicit conjugate-ratio witness in
Chapter 4 rules this out.

### 13.3 Determinant and pairing failures

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

### 13.4 Component and local-solvability failures

Full geometric monodromy does not put local points on a chosen arithmetic component. A real
point, an ordinary point, and a semistable point constructed on three different components
cannot be intersected. Similarly, separate varieties realizing the two torsion frames do not
give a point of their fiber product.

A finite-flat representation need not be the torsion of a Hilbert--Blumenthal seed of the selected
polarization type. A local frame appearing after an unramified extension does not descend to
the original local field. Each extension used to solve a local point must occur in the global
completion algebra.  Sections 7.4 and 8.2 do this by using the whole Galois orbit packet and the
repeated regular local action; one acceptable factor would not control all top completions.

Solvability of a local killing field does not by itself put an automorphic component in Book
109's selected range.  In the target comparison, nonzero monodromy forces the special case.
For zero monodromy, Section 12.2 separately removes residue characteristics $2$ and $3$ by the
preselected split local models and proves from the two-dimensional finite-inertia
classification that every remaining component is principal or tame dihedral.  Without that
classification the first tower (12.5) would not have a valid cyclic automorphic ledger.

### 13.5 Failure of closure-level disjointness

Disjointness of an arbitrary point field from $D$ would not control its normal closure.
Section 8.2 avoids this problem by imposing connectedness after base change to $D$ on the
regular symmetric top before specialization. The resulting Galois field $F$ is disjoint from
$D$.

Nor is disjointness from a projective cutout field enough to preserve the full image. Scalars
and determinants may shrink. The avoidance ledger therefore uses full matrix cutout fields.

### 13.6 Failure of arithmetic source patching

Residual automorphy in an unspecified packet does not verify the local components of a named
Tate-module point.  The auxiliary proof would stop if the order-$q$ reference packet did not
exist on the prepared scalar charts, if its primitive vector vanished after localization, or
if the desired and avoidance lattices did not have the marked equivariant reduction (10.9).
Likewise, the target proof would stop if the upper primitive vector failed to produce (12.9).
These are arithmetic occurrence statements, not numerical rank assertions.

Source patching also needs the precise residual embedding, not an abstract isomorphism of local
special fibers.  Without it the two strict relative Selmer structures need not agree.  Without
neatness the stabilizer invariants need not commute with coefficient reduction; without the
unit Gram calculation the ranks at varying Taylor--Wiles sets need not be constant; and without
represented-ring augmentation the support theorem would not reach the finite-level ring.
Sections 10.3--10.4 and 12.3 verify each of these points for the two actual packets.

An accidental semistable place of $A_F$ belongs to the actual auxiliary or target active set
whenever its local condition differs from the relevant reference problem.  Omitting it changes
the represented ring and invalidates the comparison.  The compact carrier needs only even
degree and one special dyadic factor; it neither shrinks either active set nor supplies the
common definite module used by the source patch.


## 14. Proof architecture and hypotheses

### 14.1 The earlier interfaces

The CM construction uses Book 6's exact Grunwald--Wang theorem and Book 98's algebraic Hecke
characters and quadratic automorphic induction.  Books 141--142 give adequate-image detection
and the required finite Galois distribution theorem.  Books 156--157 provide the fine
paired-frame moduli space, corrected tensor component, product monodromy, and point-centered
local models.  Book 154, Lemma 5.2A globalizes wholesale-repeatable nonsplit packets, Book
155 retains their exact local homomorphisms in a totally real disjoint Galois top, and Book
158 supplies the simple-branch split model refined in Section 8.2.  Books 104 and 127 provide the compact
one-split realization and its rational rank-two family.

The two arithmetic comparisons use a different group of earlier results.  Book 61 supplies
quasi-unipotence and the Weil--Deligne bad-place dichotomy.  Book 109, Lemmas 14.1--14.2 and
Corollaries 14.5--14.6 construct the unramifying, auxiliary-mode, and target-mode prime-cyclic towers, while
Proposition 14.4 controls every ascent and descent antecedent.  Book 143, Proposition 15.1 and
Theorem 15.2 select one relative Taylor--Wiles system for each desired--avoidance pair.  Book
170, Theorem 16.1 supplies the represented Hecke-valued local--global source actions.  Book
152, Theorem 20.5 constructs the actual definite modules, and Proposition 20.6 supplies their
cofinal fixed positive rank.  Book 144, Theorem 18.2 retains the synchronized finite shadows.
Book 145, Theorem 17.3 and Corollary 17.4 transfer source support and recover the finite action.
Book 176, Theorems 1.1J and 1.1K assemble these verified inputs in the auxiliary and target
characteristics; Corollary 1.1L records the target finite-fibre and pointwise conclusion.

The role of Book 157 is confined to its interior constructions: corrected auxiliary level,
tensor component, product monodromy, ordinary and semistable seeds, exact frames, and
point-centered openness.  Geometric one-place moving and level-lowering constructions are not
needed for either arithmetic comparison.

### 14.2 The theorem-by-theorem hypothesis flow

| Step | Arithmetic data proved before the step | Conclusion used afterward |
|---|---|---|
| simultaneous coefficients | both actual residue fields, distinct odd primes, corrected tensor choice | one real-multiplication field receiving both primes, with determinant lines and product monodromy |
| dihedral seed | rational-base compatible ray datum, determinant, type $(1,0)$, protected conjugate-ratio witness | cuspidal weight-two induction with cyclotomic determinant and adequate residual image |
| mixed specialization | original-completion seeds at $S_{\mathrm{split}}$, exact repeatable $E_v$-packets at $S_{\mathrm{dih}}$, and closure-level disjointness | the even-degree Galois field $F$, with protected splitting, exact helper completions, both frames, and preserved joint images |
| auxiliary preparation | the actual $P_{\mathrm{aux}}(A_F)$, its solvable monomial residual images, all protected completions, and the full avoidance compositum | (10.3)--(10.4), selected-safe cyclic ascent, and scalar active charts |
| auxiliary definite occurrence | the order-$q$ packet (10.7), neat common level, primitive eigenlattice, and marked coefficient reductions | the nonzero common module (10.10), paired fixed-rank systems, and all hypotheses of Book 176, Theorem 1.1J |
| auxiliary support and descent | synchronized sources, exact ring and module recovery, and the complete Book 109 descent ledger | automorphy of $V_{\mathfrak q}(A_F)$ over $F$ |
| cross-prime comparison | $q$-adic equality, common abelian Frobenius polynomials, absolute irreducibility of target torsion | the exact upper residual member at $\ell$ and its primitive definite localization |
| target ramification removal | every finite bad place classified by $N_v\ne0$ or $N_v=0$, the exact fields $E_v^+$ and $H_z$, and the selected principal/special/dihedral ledger | (12.5a), with special scalar active places and every zero-monodromy ramified place unramified |
| target preparation | the cleaned packet over $F^{\mathrm{ram}}$, complete splitting above $2\ell$, and joint-image avoidance | (12.6)--(12.6b), with a genuine upper point of the broad problem |
| target definite occurrence | the upper desired vector, neat common level, and the lattices (12.8) | the nonzero common module (12.9) and every hypothesis of Book 176, Theorem 1.1K |
| target support | the synchronized broad desired and avoidance sources with exact recovery | whole broad-ring finiteness, (12.13), and retained automorphy for every later minimal point |

Each line consumes only conclusions already established above it.  In particular, neither
residual congruence nor a nonzero vector by itself is used as a substitute for source support.

### 14.3 The noncircular order

The dihedral packet is constructed before $A_F$ and independently of the target.  Chapter 8
constructs the paired-frame abelian variety without using automorphy of its Tate module.  Once
the actual auxiliary active set is visible, the prepared order-$q$ packet supplies the common
residual module and source patch; only then does $r_A$ become automorphic.  The target residual
member is read at $\ell$ only after that $q$-adic packet and its rational family exist.

The target patch begins with this independently constructed upper packet.  It first enumerates
every bad place and removes every zero-monodromy ramified parameter over an exact solvable
completion; only then does it form the broad problem.  It proves a
nilpotent kernel and finiteness for the entire broad-unipotent ring, then passes to the
signed-special quotient.  No characteristic-zero point of that quotient appears in the proof
of Theorem 12.2.  A later point is only a consumer of the already retained support statement.
This order is what allows the finite special fibre to be used to construct a point without
using that point to prove its own finiteness.

The rational-base ray compatibility is proved in Lemma 4.1A.  Over a general totally real
base, the additional relative ray compatibility remains the explicit hypothesis of Theorem
4.2; that optional generality is not used in Theorems 11.3 or 12.2.

### 14.4 Normalization

Arithmetic Frobenius is used in the character values and covariant Tate-module polynomials.
Quadratic induction includes the quadratic determinant character. The corrected auxiliary
level is Tate-twisted, and both frame groups are special linear because their determinant lines
are fixed. Covariant Tate modules have cyclotomic determinant; the cohomological automorphic
member is twisted as in (11.1) before comparison.

Coefficient enlargement preserves rank two by scalar extension. Proposition 11.1 first
identifies the rational members and then uses absolute residual irreducibility to identify the
stable lattice. Thus the exact target residual representation is not inferred from an arbitrary
lattice over an enlarged coefficient field.


## 15. Conclusion

### 15.1 The mixed two-prime package

The two-prime method assigns the explicit residual starting point to $q$ and the target residual
member to $\ell$. A corrected CM ray datum and protected anti-cyclotomic correction construct
the dihedral member with the exact local branches. The determinant-compatible Hilbert--Blumenthal
space places both torsion systems on one arithmetic tensor component. The mixed moving
presentation specializes its fine interior to a totally real even-degree Galois top, completely
split at the protected coefficient and Frey places, with the exact solvable good-frame
completion at every ramified dihedral helper place, and disjoint from the full avoidance field.

Complete splitting forces all dyadic Tate sheets to be active for the auxiliary Tate-module
lift.  Book 109 prepares that entire actual set.  The order-$q$ anti-cyclotomic modification of
the norm-pulled dihedral packet then produces the avoidance types, and its primitive definite
eigenvector produces the common nonzero residual module.  Books 143--145 and 152 construct the
paired source patch consumed by Book 176, Theorem 1.1J.  Its top packet descends through the
explicit prime-cyclic tower, so Theorem 10.1 proves automorphy of
$V_{\mathfrak q}(A_F)$ over the original Galois field.  The compact one-split carrier and the
cross-prime comparison identify the $\ell$-adic residual member with the prescribed target,
giving Theorem 11.3.

The upper target packet then begins a genuinely separate characteristic-$\ell$ construction.
Quasi-unipotence divides its complete bad set into nonzero-monodromy places and ramified
zero-monodromy places.  The first become the active special set; exact solvable completions make
the second unramified.  Target-mode preparation keeps all dyadic signed-special and
coefficient-prime finite-flat factors unchanged while making every active residual pair scalar
with residue cardinality one modulo $\ell$.  A primitive upper definite vector gives the second common residual module.
Book 176, Theorem 1.1K and Corollary 1.1L make the whole broad-unipotent ring finite and retain
support for all its characteristic-zero points.  The signed-special minimal ring is its
quotient, so Theorem 12.2 proves the exact restricted special-fibre property (12.13) before any
minimal point is chosen.

The construction therefore ends with both data needed downstream: residual potential
modularity over the mixed Galois field and a finite signed-special residual fibre equipped with
a retained automorphic support theorem.  No finite-set comparison, definite occurrence, or
minimal point has been inserted as an assumption.
