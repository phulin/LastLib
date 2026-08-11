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
   - [The coefficient field for real multiplication](#23-the-coefficient-field-for-real-multiplication)
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
   - [Residual irreducibility and cyclotomic irreducibility](#44-residual-irreducibility-and-cyclotomic-irreducibility)
   - [Finite flatness at the auxiliary prime](#45-finite-flatness-at-the-auxiliary-prime)
   - [The controlled dihedral-seed theorem](#46-the-controlled-dihedral-seed-theorem)
5. [An auxiliary level-raising place](#5-an-auxiliary-level-raising-place)
   - [The Frobenius relation](#51-the-frobenius-relation)
   - [Selecting the prime](#52-selecting-the-prime)
   - [From an old class to a special residual class](#53-from-an-old-class-to-a-special-residual-class)
   - [Signs, repeated roots, and exceptional congruences](#54-signs-repeated-roots-and-exceptional-congruences)
6. [The twisted Hilbert--Blumenthal cover](#6-the-twisted-hilbert-blumenthal-cover)
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
    - [Comparison with the target torsion](#112-comparison-with-the-target-torsion)
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
    - [The eight prerequisite interfaces](#131-the-eight-prerequisite-interfaces)
    - [The theorem-by-theorem hypothesis ledger](#132-the-theorem-by-theorem-hypothesis-ledger)
    - [Circularity audit](#133-circularity-audit)
    - [Normalization audit](#134-normalization-audit)
14. [Conclusion](#14-conclusion)
   - [The completed two-prime package](#141-the-completed-two-prime-package)

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

The initial and final totally real fields are $K$ and $K'$. The totally real multiplication
field is $E$. A CM quadratic extension used for induction is $M/K$. The target and auxiliary
rational primes are $\ell$ and $q$, with primes $\mathfrak l,\mathfrak q$ of $E$ above them.
The special level-raising place is $v_0$.

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

### 2.3 The coefficient field for real multiplication

We need a totally real field $E$ and a prime $\mathfrak l\mid\ell$ with

$$
k_{\mathfrak l}\simeq k.
\tag{2.5}
$$

**Lemma 2.1.** If $k=\mathbf F_{\ell^f}$, there is a totally real field $E$ of degree $f$ in
which $\ell$ is unramified and has a prime of residue degree $f$. At a second rational prime
$q$, one may simultaneously prescribe any squarefree factorization pattern of total degree
$f$.

**Proof.** Choose a monic irreducible separable polynomial $\bar f_\ell$ of degree $f$ over
$\mathbf F_\ell$, a monic squarefree polynomial $\bar f_q$ with the desired factorization, and
a real monic polynomial $f_\infty$ with $f$ distinct real roots. Simultaneous approximation of
coefficients gives a monic integral polynomial congruent to the first two at $\ell$ and $q$ and
sufficiently close to $f_\infty$ over $\mathbf R$. It is irreducible by reduction at $\ell$,
has only real roots, and has discriminant prime to $\ell q$. The factorization patterns give the
claim. $\square$

After enlarging the choice if needed, fix a distinct good prime $\mathfrak q\mid q$ of $E$.
The torsion groups $A[\mathfrak l]$ and $A[\mathfrak q]$ are each two-dimensional over their own
residue fields.

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

1. good real-multiplication, ordered polarization, self-dual lattice, and neat auxiliary-level
   data are fixed;
2. a distinct $q\geq7$ and good $\mathfrak q\mid q$ are fixed;
3. a dihedral seed with cyclotomic determinant, cyclotomic absolute irreducibility, and clean
   finite-flat local behavior at $q$ is available;
4. the determinant-compatible two-prime twist has a smooth geometrically connected component
   $Y^\circ$ defined over an allowed totally real preliminary field preserving the residual
   images;
5. every required real, coefficient-prime, ramified, good, and semistable seed lies on that same
   component after the recorded local extension;
6. ordinary simultaneous approximation suffices, or a Galois approximation datum is supplied
   when normal-closure control is required;
7. the specialized $\mathfrak q$-adic Tate module and its residual automorphic datum form a
   one-prime clean datum or a finite clean chain.
8. the resulting parallel-weight-two packet has the verified curve realization datum, or a
   surface realization with full cancellation, together with the integral carrier needed to
   identify its $\mathfrak l$-adic lattice with the Tate module of the specialized abelian
   variety.

These are verification clauses. Full product monodromy proves geometric connectedness only
after the arithmetic component is selected. The local geometry verifies item 5 in its stated
good, ordinary, local--local, and split-semistable ranges. Item 7 is the exact boundary of the
lifting theorem.

## 3. Choosing the auxiliary prime

### 3.1 Why a second residue characteristic is useful

The auxiliary prime does three jobs. It supplies a residual representation whose automorphy is
constructed from a character, the coefficient characteristic for modularity lifting, and the
second factor in a connected two-prime frame cover. These jobs impose distinct exclusions.

We exclude primes below the discriminant of $E$, the polarization and auxiliary level, the
self-duality index of the PEL lattice, and the finitely many component denominators. We also
exclude the finite monodromy-exceptional set, the primes ramified in $K$, and $2,3,5,\ell$.
The remaining set is infinite. Choose $q$ in it and a prime $\mathfrak q\mid q$ of $E$.

**Lemma 3.1 (auxiliary-prime selection).** Given finitely many number fields, finite sets of
primes, and compatible Frobenius requirements in one finite Galois compositum, infinitely many
rational primes $q\geq7$ meet the requirements.

**Proof.** Remove the finitely many ramified and forbidden primes. A compatible tuple of class
requirements is one conjugacy class in the Galois group of the compositum. Primes with that
class have positive density. $\square$

Compatibility is essential. Classes prescribed independently in two fields with nontrivial
intersection need not lift to the compositum. We always form the compositum first.

### 3.2 Avoiding finitely many bad choices

Several later conditions also eliminate finitely many $q$. A fixed nonzero algebraic difference
between conjugate Hecke-character values can vanish only at finitely many coefficient primes.
Orders of chosen prime-to-$q$ local characters must remain nonzero in characteristic $q$.
The one-prime theorem requires characteristic at least seven. Finally, a desired ordinary
coefficient-prime model requires that $q$ be unramified in the local bases.

This explains why $q$ is selected after the moduli exceptional sets but before the ray-class
character. Once $q$ is fixed, the ray data are chosen to survive in that characteristic; one
does not choose a character first and hope that a previously fixed reduction preserves it.

### 3.3 Two independent primes of the real-multiplication field

The two frame groups are

$$
\operatorname{SL}_2(k_{\mathfrak l})
\quad\text{and}\quad
\operatorname{SL}_2(k_{\mathfrak q}).
$$

Surjectivity to both factors would not alone imply product monodromy: a graph subgroup can
project onto both. Simultaneous congruence approximation for the Hilbert arithmetic group gives
the full product at two distinct admissible prime ideals. This is why the two frames are placed
on one fiber-product cover.

The residue degrees may differ. If the finite fields happen to be isomorphic, the graph danger
is more visible, but the product theorem still rules it out. Distinct rational residue
characteristics are retained throughout.

### 3.4 Local coefficient-prime requirements

The lifting theorem at $q$ requires unramified local bases. We choose $q$ unramified in $K$ and
later prescribe split or unramified completion algebras at every $w\mid q$. An arbitrary
specialization can ramify at $q$ even if $K$ does not; this must be prevented in the local
algebra.

At $\ell$, the target finite-flat module must be realized by an ordinary or local--local PEL
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

Once compatibility holds, the prescription is a character on a subgroup of a finite ray class
group and extends after adjoining the needed roots of unity. If an obstruction remains, choose
a split auxiliary prime $u u^\sigma$ and inverse branch characters. They preserve the diagonal
determinant but alter $\psi/\psi^\sigma$. Auxiliary primes solve a finite character-extension
problem only when their characters are actually chosen; enlarging a modulus alone does not.

### 4.4 Residual irreducibility and cyclotomic irreducibility

For a coefficient prime $\mathfrak Q\mid q$, put

$$
\bar r=\operatorname{Ind}_{G_M}^{G_K}\bar\chi_{\psi,\mathfrak Q}.
\tag{4.5}
$$

Then

$$
\bar r\text{ is absolutely irreducible}
\quad\Longleftrightarrow\quad
\bar\chi_{\psi,\mathfrak Q}\ne
\bar\chi_{\psi,\mathfrak Q}^{\sigma}.
\tag{4.6}
$$

Choose a Frobenius or inertia element witnessing the inequality with a value of order prime to
$q$. For the cyclotomic restriction one needs the stronger condition that the conjugate ratio
remain nontrivial on $G_{M K(\zeta_q)}$. Merely requiring $M$ not to be the quadratic subfield of
$K(\zeta_q)$ is insufficient: the characters might still agree on the intersection subgroup.

At $q\geq7$, cyclotomic absolute irreducibility gives adequacy. A small dihedral image causes no
problem if it is absolutely irreducible: its projective order is prime to $q$, so averaging and
semisimple spanning apply.

### 4.5 Finite flatness at the auxiliary prime

Require every $w\mid q$ to split in $M$ and choose the two local $q$-adic characters, after the
algebraic correction, to be

$$
1\quad\text{and}\quad\epsilon_q.
\tag{4.7}
$$

The residual local module is the generic fiber of

$$
(\mathbf Z/q\mathbf Z)\oplus\boldsymbol\mu_q
\tag{4.8}
$$

after coefficient extension. It is ordinary finite flat, has determinant
$\bar\epsilon_q$, and admits compatible finite-flat quotients at every power of the coefficient
uniformizer. A nonordinary local--local choice is possible only with a separately supplied PEL
seed and integral quotient system.

### 4.6 The controlled dihedral-seed theorem

**Theorem 4.1 (controlled dihedral seed).** Let $K$ be totally real, let $q\geq7$ be unramified
in $K$, and fix finitely many compatible local ray data and determinant (4.4). After adding
finitely many auxiliary conductor primes, there exist a CM quadratic $M/K$ and an algebraic
Hecke character $\psi$ such that:

1. $\psi$ has parallel type $(1,0)$ and satisfies (4.4);
2. $\pi(\psi)$ is cuspidal of parallel weight two;
3. $\bar r$ is absolutely irreducible, totally odd, and ordinary finite flat at $q$;
4. $\bar r|_{G_{K(\zeta_q)}}$ is absolutely irreducible;
5. every prescribed prime-to-$q$ inertial distinction survives reduction.

**Proof.** Choose a quadratic character of $K$ that is odd at every real place, split above
$q$, and has the prescribed finite local values. Concretely, represent every desired local
quadratic algebra by a squareclass $a_v\in K_v^\times/(K_v^\times)^2$. These squareclasses are
open. At a place above $q$ take $a_v=1$, and at every real place take a negative number. Weak
approximation gives $a\in K^\times$ in all these squareclasses. After inserting one auxiliary
place if necessary, $a$ is not a global square. Then $M=K(\sqrt a)$ has the prescribed local
quadratic algebras and is imaginary at every real place, hence CM. This construction also makes
clear that dyadic squareclasses must be prescribed rather than dismissed by an odd-prime
argument.

On $M$, impose type $(1,0)$, (4.7), the finite local data, and (4.4). Add inverse branch
characters of order prime to $q$ at split auxiliary primes to solve the ray-unit obstruction and
to witness noninvariance. Let $R$ be the subgroup of the ray ideal group generated by principal
ray ideals, the diagonal image from $K$, and the prescribed local unit quotients. Equations
(4.4) and the ray-unit compatibility say exactly that the proposed values define a character of
$R$. Since the ray class quotient is finite abelian, the character extends to the full ray ideal
group after the coefficient field is enlarged to contain roots of its exponent. The associated
idele class character is $\psi$. Add a witness whose Frobenius remains in
$G_{M K(\zeta_q)}$ before making this extension.

Noninvariance gives cuspidality and (4.6); the second witness gives cyclotomic irreducibility.
Formula (4.3) gives the determinant. A complex conjugation exchanges the induced lines, so its
trace is zero and determinant $-1$. The local model (4.8) proves finite flatness. $\square$

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
\tag{4.9}
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
=(q_{v_0}+1)^2q_{v_0}^{-1}det\bar r(\Phi_{v_0}).
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

For the induced representation, such elements can be built inside $G_M$ by choosing a value of
the conjugate ratio and matching its cyclotomic value through compatible ray data. The resulting
conjugacy class lies in a finite compositum. A prime with that class is unramified in all the
relevant fields and satisfies (5.1). We also avoid the moduli level, the conductors, and the
finite set of bad residue characteristics.

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

Fix the totally real multiplication field $E$, an ordered invertible ideal
$(\mathfrak c,\mathfrak c^+)$, a rank-two self-dual PEL lattice with value line

$$
\mathfrak c^\vee=\mathfrak d_E^{-1}\mathfrak c^{-1},
$$

and principal auxiliary level $N\geq3$. Put into $\Sigma$ every rational prime dividing the
discriminant of $E$, the numerator or denominator of $\mathfrak c$, the level, a self-duality
index, or a component-lattice denominator. The primes $\ell$ and $q$ lie outside $\Sigma$.

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
A real PEL tensor point has the same paired involution. An isomorphism between the $+1$ lines,
followed by the uniquely normalized isomorphism between the $-1$ lines, gives each paired frame.

Thus oddness is exactly the real frame criterion. It is not enough to construct a point at one
real place: every real place of the base enters the local ledger. Small neighborhoods preserve
the real component and the signs. Later a split real completion algebra will force every
embedding of $K'$ to remain real.

### 7.2 The target coefficient prime

Let $w\mid\ell$. The target module is finite flat of weights $\{0,1\}$. If it is ordinary, use
an ordinary PEL seed whose connected--étale torsion has the same paired generic representation,
after the explicitly allowed finite local extension. If it is nonordinary, use a local--local
PEL seed, such as a supersingular tensor seed on a tensor-admissible component.

The ordinary locus is open by nonvanishing of the Hasse invariants. Nonordinarity is closed in
the special fiber, so its openness in the local field is obtained differently: fix the entire
special point and take its residue tube. Every point in that open tube has the same nonordinary
reduction. In either case, the generic frame is locally constant because its isomorphism scheme
is finite étale.

If the proposed finite-flat module is not realized by a PEL seed of the selected polarization
type, finite flatness alone does not create a point. This is one of the explicit admissibility
checks.

### 7.3 The auxiliary coefficient prime

At a place above $q$, use the ordinary split model (4.7). Choose an ordinary PEL seed with
$\mathfrak q$-torsion paired-isomorphic to $1\oplus\bar\epsilon_q$ and solve the
$\mathfrak l$-frame simultaneously after a finite unramified extension when required. The
ordinary deformation tube gives a nonempty open set on which good ordinary reduction and both
frames persist.

The completion field is chosen unramified over $\mathbf Q_q$. This retains the exact range of
the finite-flat lifting theorem. Allowing an arbitrary ramified splitting field for the frames
would solve the moduli point problem but could invalidate modularity lifting.

### 7.4 Ramification of the dihedral seed

At a finite place where $M/K$ or $\psi$ is ramified, $\bar r$ may be ramified. A good abelian
variety over the original local field has unramified prime-to-residue-characteristic torsion, so
it cannot realize an arbitrary ramified $\bar r$ there. The correct repair is to prescribe a
finite local extension on which the residual module becomes compatible with a PEL seed.

Because $\bar r$ has finite image, a finite extension trivializes it. One rarely needs so much:
it is enough to kill the local quadratic permutation character and the finite character values
appearing in its inertia. Over that extension one chooses a good PEL point and paired frames.
The exact extension is put into the completion algebra used globally.

This procedure restricts the residual representation; it does not assert that ramification has
disappeared over the original field. Nor does it identify the full $q$-adic local type of an
arbitrary lift. That type is fixed separately in the clean lifting ledger.

### 7.5 The special place

At $v_0$, choose a split semistable tensor Tate point. Its $q$-adic Tate module has rank-one
monodromy, a canonical invariant line, and conductor one at the augmentation specialization.
Choose the Tate parameter so that its residual extension and ordered Frobenius root match the
special residual localization of Proposition 5.1. Pairing fixes the determinant and sign.

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

**Theorem 8.2 (controlled two-prime specialization).** Assume the two-prime admissible ledger,
the local package of Theorem 7.1, and either the simultaneous approximation hypotheses or the
Galois datum (8.1). Then there are a finite totally real extension $K'/K_0$ and a point

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

### 9.4 No inference from torsion alone

The congruence $A[\mathfrak q]\simeq\bar r$ does not determine the local component of $r_A$.
An unramified residual representation can have crystalline, special, or ramified lifts. Nor does
it prove that $r_A$ is automorphic. The local PEL models identify the lift's component, and the
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
\pi'=operatorname{AI}_{M K'/K'}(\psi\circ N_{M K'/M}).
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

Apply Lemma 10.1 to $r_A$. The hypotheses are checked as follows.

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
the curve-realizable range, or in a surface range only when the full cancellation datum has
been verified. Let $E_\Pi$ be a coefficient field containing the Hecke data and all required
splitting values. For every finite place $\lambda$ of $E_\Pi$, the weight-two realization first
attaches a continuous semisimple cohomological representation

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

The conclusion at $\mathfrak l$ uses an integral realization datum. For the packet carried by
the abelian variety $A$, the $\mathfrak l$-adic Tate module is the geometric rank-two carrier.
Its finite-flat quotients at coefficient-prime places are supplied by the abelian scheme when
good reduction is part of the ledger. The rational representation alone would determine only a
lattice-independent residual semisimplification.

### 11.2 Comparison with the target torsion

At almost every finite place $v$ of $K'$, both $V_{\mathfrak l}(A)$ and the covariant member
$\rho^T_{\Pi_A,\lambda}$ have arithmetic-Frobenius characteristic polynomial

$$
X^2-t_vX+q_vs_v.
\tag{11.2}
$$

The polynomial is a characteristic polynomial, not merely an annihilator: the independent
polarization pairing supplies the determinant, including the scalar-Frobenius case. Density and
semisimplicity identify the generic representations. The geometric integral carrier then
identifies the canonical lattice relative to $A$. Reducing gives

$$
\bar\rho^T_{\Pi_A,\lambda}
\simeq A[\mathfrak l].
\tag{11.3}
$$

Combining (11.3) with the first frame in (9.1) yields

$$
\bar\rho^T_{\Pi_A,\lambda}
\simeq\bar\rho|_{G_{K'}}.
\tag{11.4}
$$

If one works without the integral carrier, the safe conclusion is equality of residual
semisimplifications. The exact statement (11.4) uses the paired geometric lattice and the
absolute irreducibility of the target, which makes every stable lattice homothetic.

### 11.3 The residual potential-modularity theorem

**Theorem 11.1 (residual potential modularity).** Let $K$ be totally real, let $\ell\geq7$, and
let

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
\tag{11.5}
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

**Proof.** Theorem 4.1 supplies $M$, $\psi$, and $\bar r$. Proposition 5.1 supplies its exact
special residual localization. Chapters 6 and 7 construct the smooth geometrically connected
twist and nonempty local neighborhoods on one arithmetic component. Theorem 8.2 supplies a
totally real field $K'$ and a point of that twist with all image and completion controls. The
point gives $A$ and the exact frames (9.1).

Automorphic induction over $M K'/K'$ makes $\bar r|_{G_{K'}}$ residually automorphic. The clean
augmentation lemma, applied directly or along the finite clean chain, makes
$V_{\mathfrak q}(A)$ automorphic and produces $\Pi_A$. Weight-two realization at $\ell$ and the
integral comparison with $A[\mathfrak l]$ give (11.4). Take $\Pi=\Pi_A$. Every field-control
assertion is a conclusion of Theorem 8.2. $\square$

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
\tag{11.6}
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

A finite-flat representation need not be the torsion of a PEL seed of the selected
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

## 13. Dependency and hypothesis audit

### 13.1 The eight prerequisite interfaces

The proof uses the direct prerequisites in distinct roles.

**Hecke characters and automorphic induction.** The character-extension theorem, quadratic
induction matrices, determinant with the quadratic sign, cuspidality criterion, conductor
formulas, local compatibility, coefficient fields, residual irreducibility, and controlled ray
data are used in Chapters 4, 5, and 10. The ray-unit and determinant hypotheses are retained.

**Weight-two Galois realization.** The rank-two Galois factor, good Frobenius polynomial,
determinant, oddness, integral carrier, and finite-flat quotient system are used only after
$\Pi_A$ has been proved automorphic. Surface realization is used only with the full global,
local, integral, and coefficient-prime cancellation datum.

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
| dihedral construction | CM quadratic field; compatible ray units; determinant (4.4); type $(1,0)$; prime-to-$q$ witnesses | cuspidal weight-two induction with controlled residual representation |
| residual irreducibility | conjugate ratio nontrivial after reduction | absolute irreducibility of $\bar r$ |
| cyclotomic adequacy | $q\geq7$; absolute irreducibility on $G_{K(\zeta_q)}$ | adequate cyclotomic image |
| level raising | relation (5.1); $q_{v_0}\not\equiv\pm1$; saturated maps; non-Eisenstein localization; line and sign | exact minimal-special residual occurrence |
| two-prime cover | good primes; neat level; self-dual lattice; determinant-compatible local systems | smooth fine moduli and finite étale paired frame cover |
| connected twist | fixed geometric component; full product monodromy; characteristic zero | geometrically connected twisted cover |
| local package | one seed satisfying all conditions on the chosen component; odd coefficient primes; required integral model | nonempty open neighborhoods with exact frames |
| ordinary approximation | smooth geometric connectedness; compatible local cycles; real opens; finite disjointness | finite totally real point field |
| Galois refinement | full-monodromy cover; core-free stabilizer; realized top torsors; base-changed connectedness | controlled normal closure and exact fixed-field completions |
| image preservation | disjointness from full cutout and cyclotomic compositum | unchanged full and cyclotomic images |
| one-prime lifting | complete clean datum; exact augmentation; finite-flat quotients; named components | automorphy of $V_{\mathfrak q}(A)$ |
| weight-two realization | noncharacter cuspidal packet; verified geometric carrier; integral datum for exact reduction | compatible rank-two system and target residual member |

Every row is used in the indicated direction. In particular, local openness does not prove
global connectedness, and residual image preservation does not prove automorphy.

### 13.3 Circularity audit

The dihedral packet is constructed before the Hilbert--Blumenthal point and independently of
the desired target. Its residual automorphy is therefore a genuine starting point. The
specialized abelian variety is not assumed automorphic. Its $q$-adic automorphy follows from the
one-prime theorem using the dihedral residual packet. Only afterward is the weight-two system at
$\ell$ attached.

The target conclusion (11.5) is never used to choose $K'$, prove connectedness, or select an
auxiliary prime. Adequacy is proved from cyclotomic irreducibility and not from the existence of
Taylor--Wiles primes. The arithmetic distribution theorem selects Frobenius classes only after
the finite-image detector has been constructed. Normal-closure disjointness is imposed on the
generic Galois family before specialization.

There is no appeal to a later potential-modularity, compatible-system, Brauer-descent, or
changing-prime theorem. The compatible family used in Chapter 11 is the weight-two family
attached directly to the already automorphic packet $\Pi_A$.

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
from it. Exact residual representations require the chosen integral carrier; otherwise only
semisimplification is canonical. All normalizations in the proof follow these conventions.

## 14. Conclusion

### 14.1 The completed two-prime package

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

The specialized abelian variety carries the bridge. Its residual $q$-member is dihedrally
automorphic; the clean augmentation theorem transfers that automorphy to its $q$-adic Tate
module; and weight-two Galois realization reads the resulting packet at $\ell$. The paired
$\ell$-frame identifies that residual member with the prescribed target.

The conclusion is therefore both an existence theorem and a boundary statement. For
$\ell\geq7$, every two-prime admissible weight-two residual datum becomes automorphic over a
controlled finite totally real field. Determinants, components, normal closures, coefficient-prime
integrality, and local lifting components are part of the theorem. If any of them is missing,
the proof stops exactly where that missing datum is required.
