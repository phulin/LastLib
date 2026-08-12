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
    - [The clean augmentation lemma](#102-the-clean-augmentation-lemma)
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
    - [The nine prerequisite interfaces](#131-the-nine-prerequisite-interfaces)
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
\bar\rho|_{G_{K'}}\simeq\bar\rho^T_{\Pi,\lambda}
$$

for a place $\lambda$ above $\ell$ of the coefficient field of $\Pi$, where the superscript
$T$ denotes the covariant member dual to the default cohomological realization. The field is allowed to
vary, and that freedom is used to solve several independent local and geometric problems at
once.

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
bridge we use its dual, the **covariant automorphic realization**, so that it compares directly
with a Tate module. Parallel weight two means labeled weights $\{0,1\}$.

For a finite representation $V$, $K(V)$ denotes the field cut out by its full matrix kernel.
Its projective cutout field is not silently substituted. Disjointness from $K(V)$ preserves the
full matrix image after restriction; projective disjointness preserves less.

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

There is a second boundary at modularity lifting. Absolute irreducibility and matching residual
torsion do not make a lift automorphic. The available theorem has named local components and
integral hypotheses. We therefore isolate a **cleanable** two-prime datum. The final theorem is
proved for that exact datum. If an application lies outside it, the conclusion stops at the
geometric realization (1.1).

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
   and a corrected neat level $N\geq3$ prime to $ps$, both $\mathfrak p$ and $\mathfrak s$ are
   monodromy-admissible on the tensor component. Simultaneous monodromy is the full product
   $$
   \operatorname{SL}_2(k_{\mathfrak p})\times
   \operatorname{SL}_2(k_{\mathfrak s}).
   $$
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
level. The tensor component is represented by the standard lattice, and its arithmetic group
contains the principal congruence subgroup $\Gamma(N)$. Chinese remaindering elementary upper
and lower unipotents modulo $N$, $\mathfrak p$, and $\mathfrak s$ proves surjectivity onto the
displayed product. Thus both primes are monodromy-admissible, with no exceptional set chosen
before them. Finally $\mathfrak c^\vee=\mathcal O_E$ identifies each polarization coefficient
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
represented component; residual automorphy occurs in the exact non-Eisenstein quaternionic
localization; and all saturation, type-lattice, reducedness, reciprocity, local--global
compatibility, and Taylor--Wiles hypotheses hold.

At a selected $v_0\nmid s$, the datum retains scalar residual inertia, an invariant line, a sign,
a determinant, and the enhanced special relation. Its augmentation specialization has conductor
one. A nontrivial tame-character specialization has conductor two.

A chain $\mathcal D_0,\ldots,\mathcal D_m$ is a **clean one-prime chain** if consecutive data
differ at one selected prime and the one-prime theorem applies at each step. This permits
finitely many local changes without pretending that one theorem changes them simultaneously.

### 2.5 The complete input ledger

A weight-two residual datum is **two-prime admissible** if:

1. a distinct $q\geq7$ has been selected with all exclusions of Chapter 3, including
   unramifiedness of $\bar\rho$ at every place above $q$;
2. a dihedral seed with cyclotomic determinant, cyclotomic absolute irreducibility, and clean
   finite-flat local behavior at $q$ has been constructed over its actual residue field
   $k_\psi$;
3. Theorem 2.1 has then produced $E$, $\mathfrak l$, $\mathfrak q$, the tensor polarization,
   self-dual lattice, corrected neat level, both determinant-line identifications, and
   simultaneous monodromy admissibility;
4. the determinant-compatible two-prime twist has a smooth geometrically connected component
   $Y^\circ$ defined over an allowed totally real preliminary field preserving the residual
   images;
5. every required real, coefficient-prime, ramified, good, and semistable seed lies on that same
   component after the recorded local extension;
6. ordinary simultaneous approximation suffices, or a Galois approximation datum is supplied
   when normal-closure control is required;
7. the specialized $\mathfrak q$-adic Tate module and its residual automorphic datum form a
   one-prime clean datum or a finite clean chain;
8. the resulting parallel-weight-two packet has the verified Shimura-curve realization datum.
   No cross-prime integral comparison is assumed: Chapter 11 derives the required comparison from the common abelian
   Frobenius polynomials and absolute irreducibility of $A[\mathfrak l]$.

Items 1--6 are pre-specialization construction clauses. Items 7--8 are post-specialization
verification clauses and are not inputs to the approximation theorem. Full product monodromy
proves geometric connectedness only after the arithmetic component is selected. The local
geometry verifies item 5 in its stated good, ordinary, local--local, and split-semistable
ranges. Item 7 is the exact boundary of the lifting theorem; calling the entire package
admissible does not prove that a point supplied by approximation satisfies it.

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

Globalization is equivalent to killing $\omega_{\mathfrak m}$. Compatibility with (4.4) says
that it is trivial on $U_{\mathfrak m}\cap K^\times$. By (3.1), the CM-type unit values have
order prime to $q$, and all initially prescribed finite factors are chosen of order prime to
$q$. Hence $\omega_{\mathfrak m}$ has order prime to $q$.

### 4.4 The inverse-branch ray-class lemma

The phrase “add split auxiliary primes” is not a proof: the local characters at those primes
must be produced and must not erase the already chosen irreducibility detector.

**Lemma 4.1 (prime-to-$q$ inverse-branch correction).** Let $M/K$ be quadratic with involution
$\sigma$, let $q$ be odd, and let $\mathfrak m$ be a $\sigma$-stable modulus prime to $q$. Let

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

**Proof strategy.** Pass from a unit to its anti-invariant ratio $u/u^\sigma$, realize the
resulting finite character in residue groups at split primes, and extend it on the prime-to-$q$
parts of those finite groups.

**Proof.** The map

$$
\Delta:U_{\mathfrak m}\longrightarrow M^\times,
\qquad u\longmapsto u/u^\sigma
\tag{4.10}
$$

has kernel $U_{\mathfrak m}\cap K^\times$. Thus $\omega$ descends to a finite character
$\widetilde\omega$ of the finitely generated group $D=\Delta(U_{\mathfrak m})$.

We use the finite-character congruence lemma for units. If $D_0$ is the kernel of a finite
character of a finitely generated subgroup of $M^\times$, there is a modulus $\mathfrak t$
supported on any Chebotarev-dense set of allowed primes such that the character factors through
the image of $D$ in $(\mathcal O_M/\mathfrak t)^\times$. Here is the Kummer proof. The radical

$$
D^{\mathrm{sat}}=\{x\in M^\times:x^b\in D\text{ for some }b\geq1\}
$$

is finitely generated and $D^{\mathrm{sat}}/D$ is finite: valuations give a saturated lattice
of finite index, and the remaining unit calculation takes place in the finitely generated unit
group. Extend the given prime-to-$q$ character from $D$ to $D^{\mathrm{sat}}$. Successively
taking roots does not introduce $q$-power order: multiplication by $q$ is an automorphism on
every group of roots of unity of order prime to $q$. Let $a$, still prime to $q$, be the exponent
of the image of the extended character.

Saturation makes
$D^{\mathrm{sat}}/(D^{\mathrm{sat}})^a$ inject into $M^\times/(M^\times)^a$. The Kummer
pairing for

$$
M\bigl(\boldsymbol\mu_a,(D^{\mathrm{sat}})^{1/a}\bigr)/M(\boldsymbol\mu_a)
$$

therefore separates every class on which the character is nontrivial. Choose the corresponding
Frobenius detectors over $M(\boldsymbol\mu_a)$ and view them in the Galois closure over $K$.
Chebotarev realizes them at primes of $K$ split in $M$ and in the cyclotomic constant field,
outside any prescribed finite set. Their
power-residue maps have common kernel contained in $D_0$, so finitely many give the asserted
factorization through residue groups.

Apply this lemma to $\widetilde\omega^{-1}$, choosing the support disjoint from $q$, the modulus
$\mathfrak m$, and the protected places. Because its order is prime to $q$, it factors through
the prime-to-$q$ part of the product of residue groups. A character of a subgroup of a finite
abelian prime-to-$q$ group extends to the whole group: successively choose the required roots in
the group of all prime-to-$q$ roots of unity. Decompose the extended character over the chosen
primes to obtain the $\xi_i$.

Under the identification of the two residue fields induced by $\sigma$, the value of the
inverse pair on $u$ is

$$
\xi_i\bigl((u/u^\sigma)\bmod\mathfrak u_i\bigr).
$$

Their product is therefore $\widetilde\omega(\Delta u)^{-1}=\omega(u)^{-1}$, proving (4.9).
For $u\in K_{v_i}^\times$ the two branch values are equal and inverse, so their product is one.
All new places avoid the protected set, which proves the last assertion. $\square$

After (4.9), the infinity rule and all local factors are trivial on ray units. They define a
character on the corresponding subgroup of the ray ideal group. The finite ray-class extension
argument extends it to the full ideal group, possibly adjoining roots of relations and thereby
enlarging the character-value field. This enlargement is retained; it is exactly why $E$ was
not chosen in Chapter 2 before the character existed. The field $C_\psi$ itself is not claimed
to be unramified at $q$: a ray-class relation may require a root of $q$-power order. Such an
extra finite factor is trivial on the protected local unit subgroups and does not alter their
inertial characters, while every protected prime-to-$q$ value still reduces injectively.
Theorem 2.1 constructs the separate, unramified real-multiplication field from the actual
residue field left after this extension.

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

Require every $w\mid q$ to split in $M$ and choose the two local $q$-adic characters, after the
algebraic correction, to be

$$
1\quad\text{and}\quad\epsilon_q.
\tag{4.13}
$$

The residual local module is the generic fiber of

$$
(\mathbf Z/q\mathbf Z)\oplus\boldsymbol\mu_q
\tag{4.14}
$$

after coefficient extension. It is ordinary finite flat, has determinant
$\bar\epsilon_q$, and admits compatible finite-flat quotients at every power of the coefficient
uniformizer. A nonordinary local--local choice is possible only with a separately supplied Hilbert--Blumenthal
seed and integral quotient system.

### 4.7 The controlled dihedral-seed theorem

**Theorem 4.2 (controlled dihedral seed).** Let $K$ be totally real, let $q\geq7$ satisfy the
exclusions of Chapter 3, retain the target $\bar\rho$ of Chapter 2, and fix finitely many
compatible prime-to-$q$ local ray data and determinant (4.4). After adding finitely many
auxiliary conductor primes, there exist a CM quadratic $M/K$, an algebraic Hecke character
$\psi$, a character-value field $C_\psi$, and a place $\mathfrak Q\mid q$ of $C_\psi$ such
that:

1. $\psi$ has parallel type $(1,0)$ and satisfies (4.4);
2. $\pi(\psi)$ is cuspidal of parallel weight two;
3. $\bar r$ is absolutely irreducible, totally odd, and ordinary finite flat at $q$;
4. $\bar r|_{G_{K(\zeta_q)}}$ is absolutely irreducible;
5. $H^0(K,\operatorname{ad}^0\bar r(1))=0$;
6. every prescribed prime-to-$q$ inertial distinction survives reduction.

**Proof.** Fix an embedding $\overline{\mathbf Q}\hookrightarrow\overline{\mathbf Q}_q$; the
place $\mathfrak Q$ below will be the one it induces on the character-value field. Choose a
quadratic character of $K$ that is odd at every real place, split above
$q$, and has the prescribed finite local values. Concretely, represent every desired local
quadratic algebra by a squareclass $a_v\in K_v^\times/(K_v^\times)^2$. These squareclasses are
open. At a place above $q$ take $a_v=1$, and at every real place take a negative number. Weak
approximation gives $a\in K^\times$ in all these squareclasses. After inserting one auxiliary
place if necessary, $a$ is not a global square. Then $M=K(\sqrt a)$ has the prescribed local
quadratic algebras and is imaginary at every real place, hence CM. This construction also makes
clear that dyadic squareclasses must be prescribed rather than dismissed by an odd-prime
argument.

On $M$, impose type $(1,0)$, the ordinary local condition above $q$, the finite local data, and
(4.4). Choose the protected inverse-branch inertia witness of Section 4.5. The CM-type principal
rule on units takes values in roots of unity in the normal closure of $M$: each conjugate has
absolute value one because the two exponents over every real place add to one. Condition (3.1)
makes its order prime to $q$. Thus the complete obstruction (4.6) has prime-to-$q$ order.
Lemma 4.1 supplies actual inverse branch characters cancelling it without changing either the
determinant or the protected witness.

Let $R$ be the subgroup of the ray ideal group generated by principal ray ideals, the diagonal
image from $K$, and the prescribed local unit quotients. Equations (4.4) and (4.9) say exactly
that the proposed values define a character of $R$. Since the ray class quotient is finite
abelian, the character extends to the full ray ideal group after the coefficient field is
enlarged to contain roots required by its relations. Let $C_\psi$ contain all resulting values,
choose $\mathfrak Q\mid q$, and let $\psi$ be the associated idele class character.

Noninvariance gives cuspidality and (4.12); the protected inertia witness gives cyclotomic
irreducibility.
Formula (4.3) gives the determinant. A complex conjugation exchanges the induced lines, so its
trace is zero and determinant $-1$. The local model (4.14) proves finite flatness. Finally, a
nonzero element of $H^0(K,\operatorname{ad}^0\bar r(1))$ would, by absolute irreducibility,
give an isomorphism $\bar r\simeq\bar r(1)$. Taking determinants would force
$\bar\epsilon_q^2=1$ on $G_K$. Since $q$ is unramified in $K$, one has
$K\cap\mathbf Q(\zeta_q)=\mathbf Q$, so $\bar\epsilon_q(G_K)=\mathbf F_q^\times$; this is
impossible for $q\geq7$. $\square$

Let $k_\psi=\mathcal O_{C_\psi}/\mathfrak Q$. Apply Theorem 2.1 to
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

Let the unramified Frobenius roots of $\bar r$ at $v_0$ be $\alpha$ and $\beta$. A special lift
with invariant line of eigenvalue $\beta$ and cyclotomic determinant can reduce to this
unramified representation only if

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

The ordered choice in (5.1) fixes the special line and sign. Equation (5.2) alone does not.

### 5.2 Selecting the prime

The projective class required by (5.1) is represented by
$\operatorname{diag}(q_{v_0},1)$. The residue cardinality modulo $q$ is the value of
$\bar\epsilon_q(\Phi_{v_0})$. Thus we seek one element $g$ in the finite image satisfying

$$
\text{eigenvalue ratio}(\bar r(g))=\bar\epsilon_q(g),
\tag{5.3}
$$

together with

$$
\bar\epsilon_q(g)\ne1,-1.
\tag{5.4}
$$

The required element is already visible at the coefficient prime. At a place $w\mid q$, the
splitting of $M/K$ puts the local decomposition group inside $G_M$, while (4.13) makes the two
residual branch characters $1$ and $\bar\epsilon_q$. The mod-$q$ cyclotomic image on tame
inertia is $\mathbf F_q^\times$, so choose an inertia element $g$ with

$$
a=\bar\epsilon_q(g)\notin\{1,-1\}.
\tag{5.4a}
$$

In the induced basis the eigenvalue ratio of $\bar r(g)$ is $a$. On the other hand,
$\bar\rho$ and $\bar\epsilon_\ell$ are unramified at $q$, by the prime selection of Chapter 3,
so the same $g$ has trivial image in both.

Form the finite Galois compositum cut out by $\bar r$, $\bar\epsilon_q$, $\bar\rho$, and
$\bar\epsilon_\ell$, together with the prime-to-$q$ auxiliary-level, component, and
determinant-line fields now fixed by Theorem 2.1. These last fields are unramified at $q$, so
$g$ acts trivially on them as well. Chebotarev gives a good prime $v_0\nmid q$ with this joint
Frobenius class, outside both conductors and every moduli exclusion. Then

$$
\bar\rho(\Phi_{v_0})=1,
\qquad
\bar\epsilon_\ell(\Phi_{v_0})=1,
\tag{5.4b}
$$

the auxiliary constants split at $v_0$, and $q_{v_0}\equiv a\pmod q$. The residual roots of
$\bar r(\Phi_{v_0})$ have ratio $a$, proving (5.1), while (5.4a) proves (5.4).

The condition (5.4) is not automatic. It separates the two old roots and makes the signed
companion factor a unit in the clean one-prime theorem. We choose the class before choosing the
prime; searching only by the trace relation could leave the sign ambiguous.

### 5.3 From an old class to a special residual class

At level prime to $v_0$, the dihedral packet contributes an old eigensystem. The two degeneracy
maps at $v_0$ have a Gram matrix whose determinant, after localizing at the residual maximal
ideal, vanishes precisely under the level-raising relation. Hence its cokernel has nonzero
residual support. Saturation of the degeneracy image ensures that this residual cokernel is not
created by torsion in the ambient lattice. The free new quotient and the monodromy--component
sequence then place the same residual eigensystem in the selected special localization.

This argument gives more than a conductor congruence. The ordered root chooses the invariant
line; the adjoint pairing chooses the sign; the determinant remains cyclotomic; and the new
quotient has rank-one monodromy in characteristic zero. Therefore $\bar r$ is residually
automorphic in the exact minimal-special quaternionic datum required at the augmentation face.

**Proposition 5.1 (clean residual level raising).** Assume (5.1), (5.4), non-Eisenstein
localization, saturated degeneracy maps, primitive primary and companion type lattices, and the
branchwise local--global compatibility hypotheses of the one-prime datum. Then the residual
eigensystem of $\pi(\psi)$ occurs in the named minimal-special localization at $v_0$, with the
chosen line, sign, and determinant.

**Proof.** The determinant of the old Gram matrix vanishes modulo the residual maximal ideal by
(5.1). If its localized cokernel vanished, the determinant would be a unit, a contradiction.
Saturation identifies reduction of the cokernel with the cokernel of reduction. Residual Ihara
injectivity removes an Eisenstein kernel, and the free new quotient identifies the nonzero
cokernel with a new special class. The primary--companion adjunction transports the ordered
root to the line and sign labels. Full local--global compatibility identifies the
characteristic-zero branches as the asserted special packets. $\square$

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

on the ordered old summand. On an eigensystem with trace $a_{v_0}$, its determinant is
$(q_{v_0}+1)^2-a_{v_0}^2$ in trivial central normalization; restoring the determinant character
gives (5.2). A null vector records the chosen relation between the two degeneracy branches.
Condition (5.4) makes that vector select one root integrally. The new quotient is therefore not
obtained from a dimension count: it is the saturated cokernel detected by this explicit null
direction.

### 5.4 Signs, repeated roots, and exceptional congruences

If $q_{v_0}\equiv1\pmod q$, the roots in (5.1) collide. An integral idempotent cannot select one
of them. If $q_{v_0}\equiv-1\pmod q$, the companion signed Gram factor is not a unit. The full
two-map complex may still contain information in either case, but the clean sign theorem does
not apply. We exclude both.

The trace equation also has two signs. Replacing the ordered root by the other root changes the
special line, and changing the normalization of Frobenius reverses the ratio. We use arithmetic
Frobenius consistently. Finally, a nonzero new quotient proves residual occurrence, not that
the original dihedral characteristic-zero packet has become special. The new special packet is
a congruent packet.

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

Take the corrected principal auxiliary level $N\geq3$ prime to $\ell q$. Put into $\Sigma$
every rational prime dividing the discriminant of $E$, the numerator or denominator of
$\mathfrak c$, the level, a self-duality index, or a component-lattice denominator. Theorem 2.1
and the standard tensor component ensure that $\ell$ and $q$ lie outside $\Sigma$ and that the
two selected prime ideals have full product monodromy. This is a conclusion of the simultaneous
choice, not a later genericity assumption.

The determinant-condition, $\mathfrak c$-polarized, auxiliary-level Hilbert functor is then a
smooth quasi-projective fine scheme $H$ of relative dimension $[E:\mathbf Q]$. Fine level is
essential: without it the natural object has stabilizers, and a universal abelian scheme need
not exist on a coarse space.

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

The twisted frame cover $Y\to H$ represents tuples

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
produce a point of $Y$.

The inverse different in $\mathfrak c^\vee$ is also genuine. The polarization pairing is
$\mathcal O_E$-balanced and becomes scalar-valued only after the trace-dual identification.
Replacing $\mathfrak c^\vee$ by $\mathfrak c^{-1}$ changes the integral pairing and can make a
supposed frame cover empty.

### 6.4 Geometric monodromy and connectedness

Fix a characteristic-zero geometric component $H^\circ$ of $H$. Outside the finite monodromy
exceptional set, reduction of its arithmetic group is the full special linear group at each
prime. Simultaneous reduction at $\mathfrak l$ and $\mathfrak q$ is the product. Therefore the
standard two-prime cover above $H^\circ$ has monodromy (6.3), acts transitively on its fiber, and
is geometrically connected.

An arithmetic twist becomes standard after base change to an algebraic closure. It has the
same geometric monodromy and connectedness. Twisting does not, however, choose an arithmetic
component or provide a rational point. Those are separate problems.

### 6.5 Arithmetic components

Geometric components of the Hilbert moduli space are indexed by determinant classes in a narrow
adelic quotient. Auxiliary level can refine the component set, and Galois may permute the
components. Every local seed used in approximation must lie on one $K_0$-defined smooth
geometrically connected component $Y^\circ$.

There are three legitimate ways to obtain it. One may choose the ordered polarization and
auxiliary determinant data so that the desired determinant class is already defined over $K$.
One may pass to an explicitly controlled totally real field of definition while preserving the
full residual images. Or one may build the component choice into a Galois approximation datum.
What is not legitimate is to take local points on several geometric components and intersect
their neighborhoods.

**Proposition 6.1 (component ledger).** Suppose a determinant class $c$ is fixed, the standard
component $H_c^\circ$ is defined over a totally real $K_0$, and both determinant-compatible
twists have local points on the corresponding twist $Y_c^\circ$. Then $Y_c^\circ$ is smooth and
geometrically connected, and every sufficiently small local neighborhood of one of its points
remains on it.

**Proof.** Smoothness follows from the good determinant-condition moduli theorem and finite
étaleness of the frame cover. Product monodromy makes the geometric cover over
$H_c^\circ$ connected. A twist is geometrically isomorphic to that cover, hence geometrically
connected. A component defined over $K_0$ is open and closed, so a local neighborhood cannot
cross it after shrinking. $\square$

The monodromy step deserves a precise reading. Choose a geometric base point on
$H_c^\circ$. The two torsion sheaves identify the geometric fiber of the standard cover with

$$
\operatorname{Isom}^{\mathrm{pair}}(k_{\mathfrak l}^2,A[\mathfrak l])
\times
\operatorname{Isom}^{\mathrm{pair}}(k_{\mathfrak q}^2,A[\mathfrak q]).
$$

The geometric fundamental group acts through simultaneous reduction of the Hilbert arithmetic
group. Surjectivity onto the product in (6.3) makes this action simply transitive, so the cover
has one geometric component. Replacing the constant frames by $V_{\mathfrak l}$ and
$V_{\mathfrak q}$ changes the descent cocycle but not the geometric action. This proves exactly
geometric connectedness; it says nothing about whether the resulting component has a
$K_0$-point.

The hypothesis that all local points lie on $Y_c^\circ$ is not redundant. Proposition 6.1 does
not manufacture those points.

## 7. Local points on one component

### 7.1 Real places

At a real place, complex conjugation acts on the torsion of a polarized weight-two object with
eigenvalues $1$ and $-1$. Both $\bar\rho$ and $\bar r$ are odd, so each has determinant $-1$.
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

### 7.3 The auxiliary coefficient prime

At a place above $q$, use the ordinary split model (4.13). Choose an ordinary Hilbert--Blumenthal seed with
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
Equation (5.4b) is what makes both frames possible on this same point. The target system and
$\bar\epsilon_\ell$ are trivial on Frobenius, while the dihedral roots are $1$ and
$q_{v_0}$ modulo $q$ with their order fixed by Proposition 5.1. Choose a Tate parameter in

$$
(K_{v_0}^\times)^{\ell qN}
$$

with positive valuation. Its Kummer classes vanish modulo both coefficient primes and its
$N$th root supplies the corrected auxiliary level. The split Tate torsion is therefore
$1\oplus\bar\epsilon_\ell$ at $\mathfrak l$ and
$1\oplus\bar\epsilon_q$ at $\mathfrak q$; (5.4b) identifies the first with the trivial target
restriction, while (5.1) identifies the ordered second pair with $\bar r$. The finite constant
fields included in the Chebotarev compositum are split at $v_0$, so paired bases give both exact
frames over $K_{v_0}$ itself. Pairing fixes the determinant and sign.

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

Good reduction, ordinary or local--local type, semistability, toric rank, and finite flatness
persist after finite extension. Exact valuations multiply by ramification index; nonsplit
multiplicative reduction may become split; a Kummer class may become trivial. Therefore exact
valuation and nonsplitness assertions require the completion algebra, not just persistence.

### 7.7 The simultaneous local-neighborhood lemma

**Theorem 7.1 (one-component local package).** Let $Y^\circ$ be the selected smooth
geometrically connected component and let $Z\subsetneq Y^\circ$ be closed. Suppose that at every
controlled place there is a point of $(Y^\circ\setminus Z)$ carrying one of the verified real,
good, ordinary, nonordinary finite-flat, or split-semistable models above. Then, after only the
finite local extensions recorded in the seed data, there are nonempty opens

$$
\Omega_v\subset(Y^\circ\setminus Z)(K_v')
\tag{7.1}
$$

on which the selected local condition, both exact paired frames, ordered polarization,
auxiliary level, and component all persist.

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

Let $D_{\mathrm{av}}/K_0$ be a finite Galois compositum containing:

- the full cutout fields of $\bar\rho$ and $\bar r$;
- $K_0(\zeta_\ell,\zeta_q)$ and the full cutout fields of their cyclotomic restrictions;
- the fields cut out by determinant, component, and prescribed frame torsors;
- every ray or auxiliary field whose intersection could erase a local character witness;
- any finite field already forbidden by a later clean lifting or descent step.

Using the full residual fields preserves matrix images. The projective fields alone would not
preserve determinants or central scalars. The compositum is taken before specialization so that
all compatibility conditions can be imposed at once.

### 8.2 Ordinary and Galois-refined specialization

If only a finite totally real point field, local opens, exact finite étale completion algebras,
and disjointness of the point field from $D_{\mathrm{av}}$ are needed, simultaneous
Moret--Bailly approximation applies to $Y^\circ\setminus Z$. It produces $K'$ and a point, but
does not assert that $K'/K_0$ is Galois or that its normal closure is disjoint from
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
$T\to Y^\circ$ are hypotheses verified before specialization. The resulting top field
$\widetilde L$ is Galois with group $G$, the point field is $K'=\widetilde L^J$, and
$\widetilde L$ is the normal closure of $K'$.

### 8.3 Exact completion data

At a controlled place $v$, a local homomorphism

$$
\phi_v:G_{K_{0,v}}\longrightarrow G
$$

has image $D_v$ and inertia image $I_v$. The point-field algebra is

$$
K'\otimes_{K_0}K_{0,v}
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

### 8.4 Preservation of residual images

**Lemma 8.1 (image preservation).** Let $V$ be a finite representation of $G_{K_0}$ and let
$L/K_0$ be finite. If the normal closure $\widetilde L$ is linearly disjoint from $K_0(V)$,
then

$$
V(G_L)=V(G_{K_0}).
\tag{8.3}
$$

If $\widetilde L$ is also disjoint from $K_0(V)K_0(\zeta_s)$, then the image of
$G_{L(\zeta_s)}$ equals the original cyclotomic-restriction image.

**Proof.** The image of $G_L$ is the Galois group of $K_0(V)L/L$. Disjointness makes restriction
$\operatorname{Gal}(K_0(V)L/L)\to\operatorname{Gal}(K_0(V)/K_0)$ an isomorphism. Apply the same
argument after adjoining $\zeta_s$. $\square$

Consequently absolute irreducibility, cyclotomic absolute irreducibility, adequacy, determinant
image, and any conjugate-ratio witness are preserved. Solvability of $L/K_0$ by itself would
preserve none of them.

### 8.5 The specialization theorem

**Theorem 8.2 (controlled two-prime specialization).** Assume items 1--6 of the two-prime
ledger, the local package of Theorem 7.1, and either the simultaneous approximation hypotheses
or the Galois datum (8.1). Then there are a finite totally real extension $K'/K_0$ and a point

$$
y\in(Y^\circ\setminus Z)(K')
\tag{8.4}
$$

such that every localized conjugate of $y$ lies in its prescribed neighborhood, all exact
completion data hold, $K'$ is linearly disjoint from $D_{\mathrm{av}}$, and, in the Galois
form, the normal closure is disjoint from $D_{\mathrm{av}}$ and has the prescribed group and
solvable stabilizer.

**Proof.** In the ordinary form, apply simultaneous Moret--Bailly approximation to the smooth
geometrically connected variety $Y^\circ\setminus Z$, using split real cycles, the local
algebras underlying (7.1), and connectedness after base change to $D_{\mathrm{av}}$. In the
Galois form, apply Galois-refined approximation to (8.1), with split top fibers at all real and
split finite places and the realized top homomorphisms elsewhere. Full top monodromy gives the
normal closure and base-changed connectedness gives closure-level disjointness. Evaluation gives
$y$. The double-coset formula proves every completion assertion. $\square$

In the ordinary form, the proof first replaces each local point by a reduced effective cycle of
one common degree. These cycles lie in the reduced symmetric locus. The universal incidence
family is finite étale; imposing connectedness of its specialization turns the resulting étale
algebra into one field rather than a product. At real places the local cycle is a collection of
real points, so the specialized algebra is a product of copies of $\mathbf R$. At a finite
place with prescribed algebra $B_v$, its entire conjugacy orbit is placed in the chosen open.
Connectedness after scalar extension to $D_{\mathrm{av}}$ makes
$K'\otimes D_{\mathrm{av}}$ a field and proves linear disjointness.

In the Galois form, connectedness of the quotient incidence fiber would not suffice. The top
fiber of $\widetilde T$ is forced to have full group $G$ by maximal-subgroup resolvents. Its
base change to $D_{\mathrm{av}}$ is forced to remain connected. Core-freeness of $J$ then makes
the top field the actual normal closure of the quotient field. These are three separate Hilbert
conditions, compatible because they are imposed on one affine parameter space before
specialization.

The theorem does not replace the geometric verification of (8.1). A connected two-prime frame
cover is not automatically a presentation with a prescribed Galois group and solvable sheet
stabilizer.

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
weights $\{0,1\}$ over an unramified base. At $v_0$, the Tate model supplies the enhanced
special augmentation component with rank-one monodromy, invariant line, sign, and cyclotomic
determinant. At the remaining controlled places, the local neighborhoods put $r_A$ on the named
good, finite-descent, tame-dihedral, or special component used in the clean ledger.

The representation is unramified outside finitely many places because it comes from an abelian
variety. Any additional bad places must be included in the finite clean chain; they are not
silently called minimal. This is precisely the purpose of item 7 in two-prime admissibility.

There is no pre-specialization proof of that last sentence. The extra bad places are known only
after $A$ has been produced. If an extra place is semistable and its residual representation is
unramified, the special congruence relation is visible, but that numerical fact does not by
itself construct a saturated lower-face automorphic class, an ordered integral flag, or a
compatible vanishing-cycle nullhomotopy. Those are exactly the data needed to put the place into
a clean chain or to remove several such places simultaneously. Until a prior, acyclic theorem
constructs them for the actual specialized $A$, item 7 remains an additional hypothesis.

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

The Hecke character base-changes to $M K'$ by composition with the norm. Since the normal-closure
disjointness prevents $M$ from being absorbed into $K'$, the extension $M K'/K'$ remains CM
quadratic. Quadratic induction gives a cuspidal parallel-weight-two representation

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

At $v_0$, Proposition 5.1 puts the residual eigensystem of (10.1) in the exact special
localization. At every other controlled place, the character construction and local
specialization ledger put it in the named residual component. This verifies residual
automorphy in the sense required by the deformation problem, which is stronger than saying
that (10.2) comes from some automorphic form.

### 10.2 The clean augmentation lemma

The arithmetic lifting theorem is often stated for a nontrivial tame character, where the
selected special representation has conductor two. The semistable Tate module in (9.3) lies on
the augmentation face and has conductor one. The universal equality includes that face.

**Lemma 10.1 (augmentation modularity lifting).** Let a clean one-prime datum in residue
characteristic $s\geq7$ be given, including its universal tame deformation ring
$R^{(2)}_{\Lambda}$ and Hecke algebra $\mathbb T^{(2)}_{\Lambda}$. Let

$$
r:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
$$

be a lift satisfying the fixed determinant, finite-flat coefficient-prime conditions, named
minimal conditions away from the selected place, and the named conductor-one enhanced special
condition at the selected place. Then $r$ is attached to a cuspidal parallel-weight-two
automorphic representation.

**Proof strategy.** Use the universal equality before specializing, then specialize by the
augmentation. Exactness and the collapse of the patched type complex eliminate a possible Tor
correction.

**Proof.** The local conditions give a point

$$
x_r:R^{(2)}_{\Lambda}\longrightarrow\mathcal O'
$$

whose restriction to $\Lambda$ is augmentation. The one-prime theorem gives

$$
R^{(2)}_{\Lambda}\simeq\mathbb T^{(2)}_{\Lambda}
\tag{10.3}
$$

compatibly with augmentation. The patched type complex is concentrated in one degree and its
surviving module is free over the tame base, so tensoring (10.3) with the augmentation character
has no higher Tor term. Thus $x_r$ occurs in the faithful automorphic carrier at the
conductor-one special type.

Type occurrence identifies the selected line, sign, determinant, and nonzero monodromy. At good
places the attached automorphic Galois representation and $r$ have the same Frobenius
polynomials. Both are irreducible because their residual representation is absolutely
irreducible. Density and semisimplicity identify their generic fibers. The universal deformation
point identifies the integral strict-equivalence classes; equivalently, two stable lattices with
the same absolutely irreducible reduction are homothetic. Hence the integral representations
are isomorphic. $\square$

The lemma would be false if one merely specialized a nonflat module. Exact augmentation and
Tor-independence are essential conclusions of the one-prime theorem.

### 10.3 Applying one-prime modularity lifting

Assume item 7 of Section 2.5 has been independently verified for the specialized $A$. Apply
Lemma 10.1 to $r_A$, directly or along the supplied finite clean chain. The remaining hypotheses
are checked as follows.

- The base $K'$ is totally real.
- The residual representation is (10.2), absolutely irreducible after cyclotomic restriction
  by closure-level disjointness.
- In characteristic $q\geq7$, its cyclotomic image is adequate.
- The adjoint-twist invariant is part of the dihedral and clean ledgers and survives restriction.
- At $w\mid q$, the representation has compatible finite-flat quotients of weights $\{0,1\}$
  over an unramified base.
- At $v_0$, it lies on the selected augmentation special component.
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

For lattices, scale an automorphic stable lattice $L'$ so that $L'\subseteq L=T_{\mathfrak q}A$
but $L'\nsubseteq\varpi L$. Its image in $L/\varpi L$ is a nonzero stable subspace and therefore
the whole space. Nakayama's lemma gives $L'=L$. The finite-flat quotient models at $q$ then
agree by full faithfulness in the clean unramified weight range. This is why (10.4) is integral,
not merely an isomorphism after inverting the coefficient uniformizer.

If the local profile is a finite clean chain, apply the one-prime theorem successively. At each
stage the preceding automorphic packet supplies the exact residual automorphic datum for the
next stage. The field, determinant, and coefficient-prime finite-flat condition remain fixed;
only one named prime-to-$q$ component changes. Induction on the chain length gives (10.4).

This induction cannot be replaced by a simultaneous assertion. Nor may a bad place be inserted
into the chain merely because its conductor is bounded. Its local representation must lie on a
named component covered by the one-prime theorem.

### 10.4 Solvable bridges and descent

Sometimes the clean datum is verified only after a finite solvable totally real extension
$L/K'$. A solvable sheet stabilizer in the Galois approximation datum gives a prime-cyclic tower

$$
K'=L_0\subset L_1\subset\cdots\subset L_m=L.
\tag{10.5}
$$

Complete splitting is imposed at places whose enhanced local data must remain literally
unchanged. At the other places, local parameters are restricted and checked anew; solvability
alone does not preserve conductors, dihedral irreducibility, or special signs.

If modularity lifting over $L$ makes $r_A|_{G_L}$ automorphic, the representation $r_A$ already
extends to $G_{K'}$. At each cyclic step this extension selects the quotient-character correction
among the possible automorphic descents. Strong multiplicity one identifies Galois conjugates,
and cyclic descent with the selected correction produces a packet attached to the next lower
restriction. Iterating gives $\Pi_A$ over $K'$.

This descent requires irreducibility at every step, cuspidality of the base changes, compatible
central characters and local parameters, and any inner-form discreteness conditions. These are
part of the clean solvable-bridge ledger. Endpoint invariance by itself does not supply coherent
descent.

## 11. Recovering residual automorphy at the original prime

### 11.1 Weight-two Galois realization

The packet $\Pi_A$ is noncharacter, cuspidal, and parallel weight two. Its construction lies in
the Shimura-curve-realizable range. Let
$E_\Pi$ be a coefficient field containing the Hecke data and all required splitting values. For
every finite place $\lambda$ of $E_\Pi$, the weight-two realization first attaches a continuous
semisimple cohomological representation

$$
\rho^{\mathrm{coh}}_{\Pi_A,\lambda}:G_{K'}\longrightarrow
\operatorname{GL}_2(E_{\Pi,\lambda})
\tag{11.1}
$$

with common good geometric-Frobenius polynomials, inverse-cyclotomic determinant in the trivial
component-character case, total oddness, and the verified local compatibility. Put

$$
\rho^T_{\Pi_A,\lambda}
=\left(\rho^{\mathrm{coh}}_{\Pi_A,\lambda}\right)^\vee.
\tag{11.1a}
$$

When a finite component character is present its inverse is included in this covariant
normalization. In the present trivial finite-character case,
$\det\rho^T_{\Pi_A,\lambda}=\epsilon_\lambda$.

At this stage the attachment theorem supplies a rational compatible system and stable lattices.
We do not assume that its canonical cohomological lattice has already been identified with a
Tate lattice of $A$. That identification is the cross-prime problem, and it follows from the
$q$-adic isomorphism and common Frobenius polynomials.

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
after placing the packet field and $E$ in one common algebraic coefficient field, one has

$$
V_{\mathfrak l}(A)\simeq\rho^T_{\Pi,\lambda}.
\tag{11.3}
$$

The $E_{\mathfrak l}$-form in (11.3) descends the automorphic member to
$E_{\mathfrak l}$, every stable $\mathcal O_{E_{\mathfrak l}}$-lattice
in that descended form is homothetic to $T_{\mathfrak l}A$, and

$$
\bar\rho^T_{\Pi,\lambda}\simeq A[\mathfrak l]
\tag{11.4}
$$

over the fixed residue field $k_{\mathfrak l}$. Thus the integral comparison is a conclusion,
not a separate hypothesis.

**Proof strategy.** Extract the common algebraic Frobenius polynomial from the
real-multiplication abelian variety, use (11.2) to identify it with the packet polynomial, then
apply density and an elementary stable-lattice argument at $\mathfrak l$.

**Proof.** At every place $v$ of good reduction, prime to the coefficient characteristics, the
$\mathcal O_E$-action commutes with Frobenius. The $E$-linear reduced characteristic polynomial
of that Frobenius endomorphism, equivalently the standard independence theorem for the Tate
modules of an abelian scheme with coefficients, therefore gives one polynomial

$$
P_{A,v}(X)=X^2-a_v(A)X+q_v\in E[X]
\tag{11.5}
$$

whose image in every $E_{\mathfrak p}[X]$ is the characteristic polynomial on
$V_{\mathfrak p}(A)$. The determinant is independently $q_v$ by the polarization; hence
(11.5) remains a characteristic polynomial when Frobenius is scalar.

Fix embeddings of the packet field and $E$ into one algebraic closure and then into
$\overline{\mathbf Q}_q$ as dictated by (11.2). At almost every $v$, (11.2) identifies the
images in $\overline{\mathbf Q}_q[X]$ of $P_{A,v}$ and the algebraic packet polynomial. The
embedding is injective, so those algebraic polynomials are equal before completion. After
embedding the common coefficient field at $\mathfrak l$, the two representations in (11.3)
have the same characteristic polynomials on a dense set of Frobenius elements.

The automorphic representation is semisimple. The representation $V_{\mathfrak l}(A)$ is
irreducible whenever $A[\mathfrak l]$ is: a characteristic-zero stable line, intersected and
saturated in $T_{\mathfrak l}A$, would reduce to a nonzero proper stable line. Density and
Brauer--Nesbitt now give (11.3). In particular the right side has the
$E_{\mathfrak l}$-form furnished by the left side, so any auxiliary coefficient enlargement
can be descended through that form.

Let $L=T_{\mathfrak l}A$ and transport an arbitrary stable automorphic lattice $L'$ through
(11.3). Scale $L'$ so that $L'\subseteq L$ but $L'\nsubseteq\varpi L$. Its image in
$L/\varpi L=A[\mathfrak l]$ is a nonzero stable subspace and hence, by absolute irreducibility,
the whole space. Nakayama's lemma gives $L'=L$. Reduction proves (11.4). $\square$

For the specialized variety, Lemma 8.1 preserves absolute irreducibility of
$A[\mathfrak l]\simeq\bar\rho|_{G_{K'}}$. Proposition 11.1 and the first frame in (9.1) give

$$
\bar\rho^T_{\Pi_A,\lambda}
\simeq A[\mathfrak l]
\simeq\bar\rho|_{G_{K'}}.
\tag{11.6}
$$

### 11.3 The residual potential-modularity theorem

**Theorem 11.2 (conditional residual potential modularity).** Let $K$ be totally real, let
$\ell\geq7$, and let

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(k)
$$

be a two-prime admissible weight-two residual datum of Chapter 2. Then there exist a finite
totally real extension $K'/K$ and a cuspidal parallel-weight-two automorphic representation
$\Pi$ of $\operatorname{GL}_2(\mathbf A_{K'})$ such that, for a coefficient place
$\lambda\mid\ell$,

$$
\boxed{
\bar\rho|_{G_{K'}}\simeq\bar\rho^T_{\Pi,\lambda}.}
\tag{11.7}
$$

The field may be chosen linearly disjoint from any prescribed finite extension included in the
avoidance ledger. In the Galois-refined form, its normal closure has the prescribed finite group,
is disjoint from that ledger, and may have a prescribed solvable point stabilizer. All real
places and controlled finite completions have the exact local behavior specified before
specialization.

**Proof strategy.** Construct a weight-two dihedral seed at $q$, put it and the target on a
connected determinant-compatible two-prime Hilbert cover, globalize one point with closure-level
control, transfer automorphy to the specialized abelian variety at $q$, and read the same packet
at $\ell$.

**Proof.** Theorem 4.2 supplies $M$, $\psi$, $C_\psi$, and $\bar r$; Theorem 2.1 then supplies
the simultaneous real-multiplication coefficient datum. Proposition 5.1 supplies the exact
special residual localization. Chapters 6 and 7 construct the smooth geometrically connected
twist and nonempty local neighborhoods on one arithmetic component. Theorem 8.2 supplies a
totally real field $K'$ and a point of that twist with all image and completion controls. The
point gives $A$ and the exact frames (9.1).

Automorphic induction over $M K'/K'$ makes $\bar r|_{G_{K'}}$ residually automorphic. The clean
augmentation lemma, applied directly or along the finite clean chain, makes
$V_{\mathfrak q}(A)$ automorphic and produces $\Pi_A$. Weight-two realization at $\ell$ and the
derived cross-prime comparison give (11.6). Take $\Pi=\Pi_A$. Every field-control
assertion is a conclusion of Theorem 8.2. $\square$

The word “conditional” records the exact present logical boundary rather than weakening the
catalog objective. To obtain the catalog theorem for every weight-two residual datum, one must
prove that the specialized $V_{\mathfrak q}(A)$ always satisfies item 7 of Section 2.5. The
uncontrolled extra semistable primes of $A$ are not known before specialization, and the current
prerequisites do not construct the exact lower-face classes, flags, and integral
vanishing-cycle nullhomotopies needed to remove all of them. Treating those data as part of
“two-prime admissible” proves Theorem 11.2 but does not prove that every target is admissible.
The full catalog objective remains the removal of this last conditional clause.

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

Repeated roots $q_{v_0}\equiv1\pmod q$ destroy the integral root idempotent, while
$q_{v_0}\equiv-1\pmod q$ destroys the clean signed companion factor. Wild primitive types,
residue characteristic equal to $v_0$, nonreduced selected sources, $q$-divisible stabilizers,
or a failure of saturation lie outside the one-prime theorem.

In any of these cases, the Hilbert--Blumenthal variety and frames may still exist. What fails is
the transfer of automorphy from $A[\mathfrak q]$ to $V_{\mathfrak q}(A)$.

An extra semistable prime of the specialized $A$ is not automatically a clean local change.
Residual unramifiedness supplies a congruence relation, but exact lowering also needs a
saturated lower-face class, primary--companion flags and pairings, and coherent integral
vanishing-cycle data. Since those primes are not known before specialization, a theorem used to
remove them must construct these data for the actual $A$ rather than include them in an input
ledger.

## 13. Dependency and hypothesis audit

### 13.1 The nine prerequisite interfaces

The proof uses the direct prerequisites in distinct roles.

**Hecke characters and automorphic induction.** The character-extension theorem, quadratic
induction matrices, determinant with the quadratic sign, cuspidality criterion, conductor
formulas, local compatibility, coefficient fields, residual irreducibility, and controlled ray
data are used in Chapters 4, 5, and 10. The ray-unit and determinant hypotheses are retained.

**Kummer theory.** The exact Kummer sequence supplies the root torsors used in Lemma 4.1. That
lemma applies their finite Galois evaluation pairing to separate the saturated conjugate-ratio
subgroup from a prescribed ray-unit character, and Chebotarev then supplies the split
inverse-branch primes. The finite-generation, saturation, inverse-pair assembly, and
preservation of the protected witness are proved in this book rather than attributed to the
Kummer input.

**Weight-two Galois realization.** The rank-two Galois factor, common algebraic good Frobenius
polynomials, determinant, oddness, and existence of stable lattices are used only after
$\Pi_A$ has been proved automorphic. Proposition 11.1 derives the relevant integral lattice from
$T_{\mathfrak l}A$ and absolute residual irreducibility; it uses only the rational
Shimura-curve realization supplied by the realization theorem.

**Dickson classification and adequacy.** Cyclotomic absolute irreducibility in characteristic at
least seven implies adequacy. Image preservation under disjoint base change uses the full
cutout field. Adequacy is not used to infer the separate adjoint-twist vanishing.

**One-prime nonminimal patching.** The universal ring equality, exact augmentation,
Tor-independence, clean component ledger, and solvable descent interface give Lemma 10.1 and the
transfer in Chapter 10. The conductor-two fixed-character theorem is not misapplied to the
conductor-one Tate module.

**Moret--Bailly approximation.** Smooth geometrically connected point spaces, nonempty local
opens, exact local algebras, total reality, finite disjointness, and closed-locus avoidance give
the ordinary form of Theorem 8.2. No Galois conclusion is attributed to it.

**Galois and solvable refinements.** A supplied full-monodromy Galois presentation gives the
normal closure, exact top local torsors, closure-level disjointness, compatible fixed fields, and
a prime-cyclic upper tower when the stabilizer is solvable. The presentation is verified
geometrically rather than inferred from ordinary approximation.

**Two-prime Hilbert--Blumenthal moduli.** The determinant-condition fine scheme, ordered
polarization, inverse-different pairing line, two special-linear frame torsors, component set,
and full product monodromy give the twist in Chapter 6. All bad-prime and neatness exclusions are
retained.

**Local Hilbert--Blumenthal geometry.** Real, good, ordinary, nonordinary finite-flat, and
semistable seed points; residue tubes; exact frames; openness; component bookkeeping; and
persistence give Chapter 7. A seed after local extension is always recorded in the global
completion algebra.

### 13.2 The theorem-by-theorem hypothesis ledger

| Step | Hypotheses retained | Conclusion used |
|---|---|---|
| simultaneous coefficients | both actual residual fields; distinct odd primes; weak approximation; Hilbert--Blumenthal tensor choice | one totally real $E$ receiving both fields, unramified and monodromy-admissible at both primes, with determinant lines |
| dihedral construction | CM quadratic field; compatible ray units; determinant (4.4); type $(1,0)$; prime-to-$q$ witnesses | cuspidal weight-two induction with controlled residual representation |
| inverse-branch correction | prime-to-$q$ ray-unit obstruction; triviality on diagonal $K$-units; protected witness | explicit split auxiliary characters cancel the obstruction without changing determinant or irreducibility |
| residual irreducibility | conjugate ratio nontrivial after reduction | absolute irreducibility of $\bar r$ |
| cyclotomic adequacy | $q\geq7$; absolute irreducibility on $G_{K(\zeta_q)}$ | adequate cyclotomic image |
| level raising | relation (5.1); $q_{v_0}\not\equiv\pm1$; saturated maps; non-Eisenstein localization; line and sign | exact minimal-special residual occurrence |
| two-prime cover | good primes; neat level; self-dual lattice; determinant-compatible local systems | smooth fine moduli and finite étale paired frame cover |
| connected twist | fixed geometric component; full product monodromy; characteristic zero | geometrically connected twisted cover |
| local package | one seed satisfying all conditions on the chosen component; odd coefficient primes; $\bar\rho$ unramified above $q$; required integral model | nonempty open neighborhoods with exact frames over the permitted completions |
| ordinary approximation | smooth geometric connectedness; compatible local cycles; real opens; finite disjointness | finite totally real point field |
| Galois refinement | full-monodromy cover; core-free stabilizer; realized top torsors; base-changed connectedness | controlled normal closure and exact fixed-field completions |
| image preservation | disjointness from full cutout and cyclotomic compositum | unchanged full and cyclotomic images |
| one-prime lifting | complete clean datum; exact augmentation; finite-flat quotients; named components | automorphy of $V_{\mathfrak q}(A)$ |
| cross-prime comparison | noncharacter cuspidal packet; rational rank-two realization; $q$-adic equality; common abelian Frobenius polynomials; absolutely irreducible target torsion | $\mathfrak l$-adic equality, an $E_{\mathfrak l}$-form, and the exact target residual member for every lattice in that form |

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

There is no appeal to a later potential-modularity, compatible-system, Brauer-descent, or
changing-prime theorem. The compatible family used in Chapter 11 is the weight-two family
attached directly to the already automorphic packet $\Pi_A$.

In particular, the simultaneous semistable carrier manuscript numbered 194 is not used. In the
current dependency graph it depends on this book, so citing it here would create a cycle. Its
abstract theorem assumes an effective exactly seeded datum, and its present auxiliary-dihedral
application constructs those seeds using the dihedral and Hilbert--Blumenthal package developed here. Even if
that downstream verification is accepted on its own terms, it cannot be imported to prove its
own prerequisite. Moreover, the application chooses comparison parameters of the form $u=t^q$
at removable places; it does not derive a root $t$, a lower-face automorphic class, and all
higher coherences from the actual Tate parameters at uncontrolled places which appear only
after $A$ is specialized. The generic carrier theorem and a genuine actual-specialization seed
verification must first be extracted into an acyclic prior dependency. Such a result may then
be inserted at the explicit boundary in Sections 9.3 and 10.3.

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
identified.

Finite flatness is used at the coefficient residue characteristic and unramifiedness only away
from it. Without absolute residual irreducibility, an arbitrary stable lattice would determine
only a residual semisimplification. Here absolute irreducibility and Proposition 11.1 force all
stable lattices to be homothetic to $T_{\mathfrak l}A$, so the exact residual representation is
a conclusion. All normalizations in the proof follow these conventions.

## 14. Conclusion

### 14.1 The two-prime package and its remaining boundary

The two-prime method succeeds because it assigns one task to each prime. At $q$, a rank-one
Hecke character over a CM field supplies an explicit dihedral rank-two representation. Its
infinity type gives parallel weight two; its diagonal restriction fixes the determinant; ray
data control conductor and local inertia; and a conjugate-ratio witness survives both reduction
and cyclotomic restriction. A carefully selected good prime turns its old residual class into
the exact special localization needed by lifting.

At $\ell$, the original residual representation is placed on the same polarized abelian variety.
The determinant-compatible two-prime cover remembers both torsion systems exactly. Product
monodromy gives geometric connectedness, while component bookkeeping chooses the arithmetic
piece. Real, ordinary, local--local, good, and semistable seed points produce genuine open
neighborhoods on that one piece.

Arithmetic approximation then chooses the field rather than demanding a rational point over
the original base. In its Galois-refined form it controls the normal closure, every completion in
the fixed-field diagram, and disjointness from full residual cutout fields. These controls keep
oddness, absolute irreducibility, cyclotomic adequacy, determinants, and local witnesses intact.

The specialized abelian variety carries the bridge. Once its post-specialization clean datum is
verified, its residual $q$-member is dihedrally automorphic; the clean augmentation theorem
transfers that automorphy to its $q$-adic Tate module. Weight-two Galois realization and the
derived cross-prime Tate comparison then reads the same packet at $\ell$, and the paired
$\ell$-frame identifies that residual member with the prescribed target.

The proved conclusion is therefore a conditional transfer theorem with an exact boundary. For
$\ell\geq7$, every two-prime admissible weight-two residual datum becomes automorphic over a
controlled finite totally real field. Simultaneous coefficient realization, ray-unit
correction, determinant lines, components, normal closures, the unramified auxiliary frame, and
cross-prime integrality are now proved rather than assumed.

The catalog objective is stronger: every weight-two residual datum in the stated range must be
shown to satisfy the post-specialization cleanability clause. The first remaining obstruction is
the construction of exact automorphic and vanishing-cycle seeds at every uncontrolled extra
semistable prime of $A$, simultaneously and without circular use of this potential-modularity
conclusion. Until that theorem is available as a genuine prior input, Book 174 has not completed
the full catalog objective.
