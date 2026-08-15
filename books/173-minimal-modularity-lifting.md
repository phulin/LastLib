# Minimal Modularity Lifting

## Contents

- [1. The lifting problem](#1-the-lifting-problem)
  - [1.1 From one automorphic point to every minimal lift](#11-from-one-automorphic-point-to-every-minimal-lift)
  - [1.2 The logical shape of the argument](#12-the-logical-shape-of-the-argument)
  - [1.3 The exact theorem](#13-the-exact-theorem)
  - [1.4 A guide to the hypotheses](#14-a-guide-to-the-hypotheses)
- [2. The residual and local datum](#2-the-residual-and-local-datum)
  - [2.1 Coefficients, determinant, and Frobenius](#21-coefficients-determinant-and-frobenius)
  - [2.2 Total oddness and residual automorphy](#22-total-oddness-and-residual-automorphy)
  - [2.3 Finite flatness at the coefficient prime](#23-finite-flatness-at-the-coefficient-prime)
  - [2.4 Minimal conditions away from the coefficient prime](#24-minimal-conditions-away-from-the-coefficient-prime)
  - [2.5 What minimal does not mean](#25-what-minimal-does-not-mean)
- [3. The global minimal deformation problem](#3-the-global-minimal-deformation-problem)
  - [3.1 Representability and tangent spaces](#31-representability-and-tangent-spaces)
  - [3.2 The dual Selmer group](#32-the-dual-selmer-group)
  - [3.3 The totally real balance](#33-the-totally-real-balance)
  - [3.4 Framed and unframed counts](#34-framed-and-unframed-counts)
- [4. The automorphic side and the comparison map](#4-the-automorphic-side-and-the-comparison-map)
  - [4.1 Definite quaternionic forms](#41-definite-quaternionic-forms)
  - [4.2 Integral types, companions, and pairings](#42-integral-types-companions-and-pairings)
  - [4.3 The Hecke-valued representation](#43-the-hecke-valued-representation)
  - [4.4 The surjection from deformations to Hecke operators](#44-the-surjection-from-deformations-to-hecke-operators)
- [5. Adequacy and Taylor--Wiles primes](#5-adequacy-and-taylor--wiles-primes)
  - [5.1 Why cyclotomic irreducibility is the right image hypothesis](#51-why-cyclotomic-irreducibility-is-the-right-image-hypothesis)
  - [5.2 The coefficient-prime bound](#52-the-coefficient-prime-bound)
  - [5.3 Detecting the dual Selmer group](#53-detecting-the-dual-selmer-group)
  - [5.4 The exact auxiliary ledger](#54-the-exact-auxiliary-ledger)
- [6. Auxiliary local conditions and diamond variables](#6-auxiliary-local-conditions-and-diamond-variables)
  - [6.1 Ordered regular branches](#61-ordered-regular-branches)
  - [6.2 Group algebras and their limit](#62-group-algebras-and-their-limit)
  - [6.3 Exact deformation augmentation](#63-exact-deformation-augmentation)
  - [6.4 The old-form determinant](#64-the-old-form-determinant)
- [7. Auxiliary automorphic modules](#7-auxiliary-automorphic-modules)
  - [7.1 Deep level and group-ring freeness](#71-deep-level-and-group-ring-freeness)
  - [7.2 Integral oldness](#72-integral-oldness)
  - [7.3 Primary and companion branches](#73-primary-and-companion-branches)
  - [7.4 Exact module augmentation and the Hecke image](#74-exact-module-augmentation-and-the-hecke-image)
- [8. The finite system and its patch](#8-the-finite-system-and-its-patch)
  - [8.1 The finite-level diagram](#81-the-finite-level-diagram)
  - [8.2 Why the levels do not form a tower](#82-why-the-levels-do-not-form-a-tower)
  - [8.3 Finite shadows and diagonalization](#83-finite-shadows-and-diagonalization)
  - [8.4 The patched objects](#84-the-patched-objects)
- [9. Equal-variable rigidity](#9-equal-variable-rigidity)
  - [9.1 The sharp absolute source](#91-the-sharp-absolute-source)
  - [9.2 The dimension argument](#92-the-dimension-argument)
  - [9.3 Freeness and faithfulness](#93-freeness-and-faithfulness)
  - [9.4 Why weaker support arguments fail](#94-why-weaker-support-arguments-fail)
- [10. Descent and the minimal equality](#10-descent-and-the-minimal-equality)
  - [10.1 Regular augmentation](#101-regular-augmentation)
  - [10.2 Proof of the minimal comparison](#102-proof-of-the-minimal-comparison)
  - [10.3 Complete intersections and congruences](#103-complete-intersections-and-congruences)
- [11. Recovering automorphic representations](#11-recovering-automorphic-representations)
  - [11.1 A characteristic-zero point of the Hecke algebra](#111-a-characteristic-zero-point-of-the-hecke-algebra)
  - [11.2 Equality of Galois representations](#112-equality-of-galois-representations)
  - [11.3 Lattices and finite-flat quotients](#113-lattices-and-finite-flat-quotients)
  - [11.4 The lifting theorem proved](#114-the-lifting-theorem-proved)
- [12. Coefficient changes, descent, and exceptional cases](#12-coefficient-changes-descent-and-exceptional-cases)
  - [12.1 Extension of coefficients](#121-extension-of-coefficients)
  - [12.2 Descent to the original coefficient ring](#122-descent-to-the-original-coefficient-ring)
  - [12.3 The boundary at five and below](#123-the-boundary-at-five-and-below)
  - [12.4 Local and automorphic failures](#124-local-and-automorphic-failures)
- [13. The minimal modularity package](#13-the-minimal-modularity-package)
  - [13.1 Dependency and hypothesis audit](#131-dependency-and-hypothesis-audit)
  - [13.2 Final synthesis](#132-final-synthesis)

## 1. The lifting problem

### 1.1 From one automorphic point to every minimal lift

Let $F$ be a totally real number field and let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
$$

be a continuous residual representation in characteristic $\ell$. Suppose that
$\bar\rho$ is already known to come from a parallel-weight-two automorphic
representation. Residual automorphy gives one point on an arithmetic moduli
space. A modularity-lifting theorem asks for much more: is every
characteristic-zero lift of that point, subject to the same determinant and
the same minimal local conditions, automorphic?

There are two natural rings. The universal minimal deformation ring
$R^{\min}$ records all such Galois lifts. The localized Hecke algebra
$\mathbb T^{\min}$ records the automorphic eigensystems with the matching
weight, determinant, level, and local types. A Hecke-valued Galois
representation produces a canonical surjection

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min}.
\tag{1.1}
$$

Surjectivity says that the Hecke operators are functions of the universal
Galois representation. It does not say that every Galois point is
automorphic. The lifting theorem is the assertion that (1.1) has zero kernel.
That is an integral, scheme-theoretic assertion. Equality after inverting
$\ell$, equality of reduced quotients, or equality of dimensions would all
leave room for congruence information or nilpotents invisible to
characteristic-zero points.

The word *minimal* is equally important. It does not mean merely that the
Artin conductor is numerically smallest. It means that a represented local
condition has been chosen at every place: finite flat of weights $\{0,1\}$
above $\ell$, and an exact unramified, fixed-type, or named special component
away from $\ell$. These conditions must match the integral local types on the
automorphic side.

### 1.2 The logical shape of the argument

The proof has four independent pieces.

First, global deformation theory constructs $R^{\min}$ and computes its
tangent and obstruction spaces by Selmer groups. The totally real Euler
characteristic is balanced: the positive finite-flat contributions at places
above $\ell$ cancel the negative contributions of all real places.

Second, residual automorphy and integral local--global compatibility construct
$\mathbb T^{\min}$, a faithful automorphic module, and the surjection (1.1).
This step must precede patching; patching cannot manufacture a Galois
representation over an incorrectly chosen Hecke order.

Third, the split Taylor--Wiles image package supplies sets of auxiliary primes
that kill the dual Selmer group. At a set of $q$ primes one obtains exactly
$q$ diamond variables. The deep-level automorphic module is free over the
corresponding finite group algebra, and augmentation recovers the exact
minimal deformation problem, module, and named Hecke action.

Fourth, patching yields two power-series sources of the same dimension:

$$
P=\mathcal O[[x_1,\ldots,x_q]],
\qquad
S_\infty=\mathcal O[[z_1,\ldots,z_q]].
\tag{1.2}
$$

The patched module is free and nonzero over $S_\infty$. Its scalar action
embeds $S_\infty$ into the image of $P$. Since $P$ is a regular local domain
of the same dimension, no nonzero ideal of $P$ can lie in the kernel. This
equal-variable argument kills nilpotents as well as generic components.
Freeness and exact augmentation then descend the equality to minimal level.

This order prevents three common circles. Residual automorphy is used only to
make the automorphic module nonzero, not to assert that every component is
automorphic. Faithfulness is proved from regularity and depth, not assumed
from topological support. Cotangent--congruence equality is derived after
$R=\mathbb T$ and is not used to establish that equality.

### 1.3 The exact theorem

We now state the result in the form proved in this volume. The phrase *clean
minimal datum* is unpacked completely in Chapters 2 and 4.

**Theorem 1.1 (minimal modularity lifting).** Let $F$ be totally real, let
$\ell\geq7$, and let $(\mathcal O,\varpi,k)$ be the ring of integers,
uniformizer, and residue field of a finite extension of $\mathbf Q_\ell$.
Let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{1.3}
$$

be continuous, absolutely irreducible, and totally odd. Assume that
$\bar\rho|_{G_{F(\zeta_\ell)}}$ is absolutely irreducible. Fix a continuous
determinant lift

$$
\delta:G_F\longrightarrow\mathcal O^\times
\tag{1.4}
$$

of $\det\bar\rho$, compatible with a parallel-weight-two central character.
Put $M=\operatorname{ad}^0\bar\rho$.

Assume the following.

1. For every $v\mid\ell$, the extension $F_v/\mathbf Q_\ell$ is unramified,
   and the residual restriction belongs to the low-weight finite-flat range
   with weights $\{0,1\}$. The fixed-determinant framed condition is the clean
   formally smooth finite-flat condition.
2. At every finite $v\nmid\ell$ in the controlling set, the minimal condition
   is one of the represented clean conditions: unramified, a fixed
   prime-to-$\ell$ integral inertial type with all required labels, or the
   schematic closure of a named minimal-special component with its line,
   sign, and monodromy relation.
3. The representation $\bar\rho$ is residually automorphic in an exact
   parallel-weight-two definite-quaternionic realization whose local factors
   match those conditions and the determinant $\delta$.
4. The minimal and auxiliary localized automorphic modules satisfy finite
   freeness over $\mathcal O$, effective stabilizer and diamond-torsor
   control, integral saturation of type lattices and degeneracy maps, a
   perfect primary--companion pairing, generic reducedness of every relevant
   Hecke algebra, and branchwise Galois attachment with integral
   local--global compatibility. The named Hecke and diamond actions commute
   with module augmentation and the named Hecke operators specialize onto the
   full faithful minimal Hecke image.

Then the canonical map is an isomorphism

$$
\boxed{R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.}
\tag{1.5}
$$

The common ring is finite free and a relative complete intersection over
$\mathcal O$, hence Gorenstein. The minimal automorphic module is finite free
of positive rank over it, and its primary--companion pairing is perfect with
the prescribed adjoints.

Let $\mathcal O'/\mathcal O$ be the ring of integers in a finite extension of
coefficient fields. Every lift

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{1.6}
$$

of $\bar\rho$, with determinant $\delta$ after scalar extension and satisfying
the same minimal local conditions on every Artinian quotient, is attached to
a cuspidal parallel-weight-two automorphic representation with the prescribed
central character and local types. The attached stable lattice may be chosen
so that its integral Galois representation is isomorphic to $\rho$.

No conclusion is asserted by this theorem at $\ell=5$ from absolute
irreducibility alone, when the cyclotomic restriction is reducible, for a
local condition outside the named clean components, or without the exact
integral automorphic realization.

### 1.4 A guide to the hypotheses

Each hypothesis has one job. Absolute irreducibility gives the global Schur
condition and representability. Total oddness supplies the real local
condition and the sign in the Euler characteristic. Absolute irreducibility
after cyclotomic restriction kills the trace-zero cyclotomic self-twist and
places the group actually used to choose auxiliary primes in the adequate
range. The bound $\ell\geq7$ makes the image implication uniform in dimension
two. Section 5.2 checks the additional underlying-prime-field clauses needed
for cyclotomic disjointness rather than treating them as part of the word
“adequate.”

The finite-flat hypothesis is not shorthand for being crystalline after
inverting $\ell$. It is an integral condition on all Artinian quotients and is
the source of the exact local tangent contribution. The local conditions away
from $\ell$ are not specified merely by conductors. Their integral labels and
component closures ensure representability and exact automorphic matching.

Residual automorphy is also more precise than equality of good-prime traces.
It selects a non-Eisenstein maximal ideal in a particular integral module.
The saturation and pairing assumptions ensure that auxiliary-level
coinvariants return to that same lattice, rather than to a finite-index
variant. The named action maps are retained under augmentation so that their
faithful image on the minimal module is the original minimal Hecke algebra;
no equality of auxiliary and minimal orders is assumed at this stage.
Generic reducedness and branchwise attachment are used to construct the
Hecke-valued Galois representation; they are not used as a substitute for the
later proof of faithfulness.

A useful mental model is a nodal family. One automorphic branch may pass
through the residual point while another infinitesimal direction is visible
only in the completed local ring. Knowing the generic points on one branch
does not control that local scheme. The Taylor--Wiles construction replaces
the singular picture by a regular patched source whose dimension is forced
independently by diamond operators. Proving that this source has no kernel is
exactly what rules out an invisible direction.

There are also three meanings of “the same local behavior.” Equality of
conductors is the weakest. Equality of characteristic-zero inertial types is
stronger but still ignores lattices. Equality in a represented integral local
functor is strongest: it retains every torsion quotient, determinant,
ordering, component label, and monodromy closure. The theorem uses the third
meaning. That is why it recovers an integral representation rather than only
a semisimple representation over a fraction field.

## 2. The residual and local datum

Chapters 2--10 recall the earlier results used in the proof. Book 171 constructs the minimal
totally real deformation--Hecke datum and comparison map; Book 172 proves Taylor--Wiles
selection, deep-level freeness, patching, descent, and minimal $R=T$. This book applies those
results and does not redevelop them.

### 2.1 Coefficients, determinant, and Frobenius

We use the coefficient DVR, fixed determinant, geometric Frobenius, and good
polynomial conventions of Book 171, Sections 2.1 and 12.2. In particular,

$$
X^2-T_vX+q_vS_v
\tag{2.1}
$$

is the named Hecke polynomial on every good branch.

### 2.2 Total oddness and residual automorphy

The Schur, total-oddness, non-Eisenstein, and exact definite-quaternionic
residual automorphy hypotheses are precisely Book 171, Sections 2.2--2.3.

### 2.3 Finite flatness at the coefficient prime

At every $v\mid\ell$ we retain the unramified low-weight finite-flat condition
of Book 171, Sections 3.2 and 4.3, on all Artinian quotients. Rational
crystallinity is not substituted for this represented integral condition.

### 2.4 Minimal conditions away from the coefficient prime

The unramified, fixed prime-to-$\ell$ type, and enhanced minimal-special rows
are exactly Book 171, Sections 3.3--3.5, including every line, sign,
determinant, and component label.

### 2.5 What minimal does not mean

Equality of conductors or generic inertial types does not identify one of
these integral deformation functors. No local hypothesis of Theorem 1.1 is
weaker than the corresponding Book 171 row.

## 3. The global minimal deformation problem

### 3.1 Representability and tangent spaces

Book 171, Chapter 5 constructs $R^{\min}$ and identifies its tangent space
with the Selmer group for the represented local conditions.

### 3.2 The dual Selmer group

The dual local conditions and Poitou--Tate calculation are imported from Book
171, Sections 5.4--5.5.

### 3.3 The totally real balance

The finite-flat contributions above $\ell$ cancel the real-place terms in the
exact numerical formula of Book 171, Theorem 13.2.

### 3.4 Framed and unframed counts

All frame variables and determinant corrections are those in Book 171,
Sections 4.1 and 5.2. They are not recounted in this application volume.

## 4. The automorphic side and the comparison map

### 4.1 Definite quaternionic forms

The nonzero finite automorphic module, inner form, level, and residual maximal
ideal are the objects of Book 171, Chapter 6.

### 4.2 Integral types, companions, and pairings

Primary and companion lattices, saturation, finite freeness, and the perfect
adjoint pairing are imported with all hypotheses from Book 171, Chapter 7.

### 4.3 The Hecke-valued representation

Book 171, Chapter 8 constructs the branchwise representation over the
localized faithful Hecke order. We retain the notation

$$
\rho_{\mathbb T}:G_F\longrightarrow
\operatorname{GL}_2(\mathbb T^{\min}).
\tag{4.3}
$$

### 4.4 The surjection from deformations to Hecke operators

**Imported comparison 4.1.** Book 171, Theorem 13.1 supplies the canonical
surjection

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min},
\tag{4.4}
$$

with exact local factorization and faithful named Hecke image. It does not by
itself assert injectivity.

## 5. Adequacy and Taylor--Wiles primes

### 5.1 Why cyclotomic irreducibility is the right image hypothesis

The image implication used here is the one already checked in Books 171--172:
$\bar\rho|_{G_{F(\zeta_\ell)}}$ is absolutely irreducible.

### 5.2 The coefficient-prime bound

The uniform implication is used only for $\ell\ge7$. The prime-five
icosahedral boundary is retained in Chapter 12 below.

### 5.3 Detecting the dual Selmer group

Book 172, Chapter 3 imports the split regular-semisimple detector and chooses
the exact number of auxiliary primes required by Book 171, Theorem 13.2.

### 5.4 The exact auxiliary ledger

Ordered roots, cyclotomic and underlying-prime-field disjointness, local
regularity, and simultaneous detection are all part of Book 172's input.
The word “adequate” does not replace them.

## 6. Auxiliary local conditions and diamond variables

### 6.1 Ordered regular branches

These are Book 172, Section 4.1.

### 6.2 Group algebras and their limit

The finite diamond algebras and $S_\infty$ are Book 172, Section 4.2.

### 6.3 Exact deformation augmentation

Book 172, Section 4.3 proves that augmentation recovers the represented
minimal deformation problem, not merely a ring with the same generic fiber.

### 6.4 The old-form determinant

The ordered-root unit needed for integral oldness is retained from Book 172,
Sections 4.4 and 5.3.

## 7. Auxiliary automorphic modules

### 7.1 Deep level and group-ring freeness

This is Book 172, Sections 5.1--5.2, including effective diamond torsors and
stabilizer control.

### 7.2 Integral oldness

Saturation and exact return to minimal level are Book 172, Section 5.3.

### 7.3 Primary and companion branches

The two lattices and their adjunction are the imported Book 171--172 type
package.

### 7.4 Exact module augmentation and the Hecke image

Book 172, Section 6.3 identifies the augmented module and gives the natural
surjection onto the augmented acting image.  The faithful acting-order
identification is obtained only after patched faithfulness, in Book 172,
Section 11.2.  Module coinvariants alone would not suffice.

## 8. The finite system and its patch

### 8.1 The finite-level diagram

The rings, modules, diamond actions, and Hecke actions form the commuting
diagram of Book 172, Chapter 6.

### 8.2 Why the levels do not form a tower

Auxiliary sets vary with depth. Book 172 therefore uses finite shadows rather
than nonexistent transition maps between the arithmetic levels.

### 8.3 Finite shadows and diagonalization

Coherent diagonalization is Book 172, Sections 6.4 and 8.2.

### 8.4 The patched objects

The patched rings, module, and exact augmentation fiber are Book 172,
Sections 8.3--8.4.

## 9. Equal-variable rigidity

### 9.1 The sharp absolute source

Book 172, Chapter 7 constructs the regular absolute power-series source with
the correct number of variables.

### 9.2 The dimension argument

The two sources have the same dimension by Book 172, Chapter 9.

### 9.3 Freeness and faithfulness

Book 172, Propositions 10.1--10.2 prove equal-variable rigidity and freeness;
faithfulness is a theorem, not a support assumption.

**Lemma 9.1 (equal-variable rigidity).** This is Book 172,
Proposition 10.1 in the equal-dimensional regular-source situation used here.

### 9.4 Why weaker support arguments fail

Full topological support only kills an annihilator up to the nilradical.
Book 172's regular-domain argument is the imported step that kills the actual
kernel.

## 10. Descent and the minimal equality

### 10.1 Regular augmentation

The augmentation sequence is regular by Book 172, Section 11.1.

### 10.2 Proof of the minimal comparison

**Theorem 10.1 (minimal comparison).** Under exactly the
hypotheses listed in Theorem 1.1, Book 172, Theorem 1.1 gives

$$
\boxed{R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.}
\tag{10.3}
$$

This restatement fixes the notation used below; the proof is Book 172, Theorem 1.1.

### 10.3 Complete intersections and congruences

The finite freeness, relative complete-intersection, Gorenstein, module
freeness, and cotangent--congruence conclusions are Book 172, Chapters 12--13.
They are consequences of (10.3), not inputs to it.

## 11. Recovering automorphic representations

### 11.1 A characteristic-zero point of the Hecke algebra

Let $\mathcal O'/\mathcal O$ be finite and let $\rho$ be a lift as in (1.6).
The universal property gives a local homomorphism

$$
x_\rho:R^{\min}\longrightarrow\mathcal O'.
\tag{11.1}
$$

Through (10.3), this is a character of $\mathbb T^{\min}$. After passing to
fraction fields, the reduced finite Hecke algebra is a product of fields
generated by characteristic-zero eigenpackets. The character $x_\rho$ selects
one of these packets after a further finite coefficient extension if
necessary.

Indeed, tensor $x_\rho$ with the fraction field $E'$ of $\mathcal O'$. A map
from a finite reduced $E$-algebra to a field factors through one field factor.
On that factor the commuting Hecke operators have a simultaneous eigenvector
after a finite extension. Since $\mathbb T^{\min}$ is the faithful image on
$M^{\min}$, this eigenvector occurs in the automorphic module rather than in
an abstract quotient algebra. Finite freeness ensures that no generic factor
disappears on passage from the lattice to its fraction-space.

Because $\mathbb T^{\min}$ is the faithful image on the exact localized
definite-quaternionic module, the selected system occurs in that module. The
fixed local type lattices show that its local components have precisely the
declared unramified, finite-type, and minimal-special behavior. Transfer from
the definite quaternion algebra yields a cuspidal automorphic representation
$\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ of parallel weight two and the
prescribed central character. This transfer does not change the good Hecke
polynomials and carries the named local packets to their matching
$\operatorname{GL}_2$ packets.

Cuspidality is not inferred from irreducibility of the Galois representation.
It belongs to the noncharacter quaternionic realization and its transfer.
The non-Eisenstein localization rules out a residual sum of characters, while
the branchwise attachment hypothesis rules out generic character branches.
Exact type matching, not conductor comparison, determines the packet at each
ramified place.

### 11.2 Equality of Galois representations

Let $\rho_\pi$ be the rank-two Galois representation attached to $\pi$. At
every $v\notin S$,

$$
\operatorname{charpol}(\rho(\Phi_v);X)
=X^2-x_\rho(T_v)X+x_\rho(q_vS_v)
=\operatorname{charpol}(\rho_\pi(\Phi_v);X).
\tag{11.2}
$$

Density of Frobenius conjugacy classes and Brauer--Nesbitt identify the
semisimplifications over the coefficient field. A lift whose residual
representation is absolutely irreducible is itself irreducible: a stable line
over the fraction field has an intersection with a stable lattice whose
reduction, after saturation, gives a nonzero proper residual stable subspace.
Thus both representations are irreducible and their generic fibers are
isomorphic.

This density argument uses both trace and determinant. Equality of the
polynomials on a dense set makes the continuous pseudorepresentations equal
on all of $G_F$, after which Brauer--Nesbitt applies. The local statements at
bad places are not reconstructed from density: they were imposed on the
universal deformation and the Hecke family before (4.4) was defined. Good
traces cannot by themselves recover an integral finite-flat model or a
monodromy parameter.

There is a stronger integral explanation. The Hecke-valued representation
(4.3) is the pushforward of the universal representation along (10.3).
Specializing it by $x_\rho$ produces the same strict-equivalence class as
$\rho$ by the universal property. The canonical stable lattice in
$\rho_\pi$ used to construct (4.3) specializes to that representation.
Consequently, after conjugation,

$$
\rho\simeq\rho_\pi
\tag{11.3}
$$

over $\mathcal O'$, not merely after inverting $\ell$.

### 11.3 Lattices and finite-flat quotients

We make the lattice step explicit because generic automorphy alone would not
prove the integral lifting statement. Let $V$ be the irreducible coefficient-
field representation underlying $\rho_\pi$. Any two stable lattices $L$ and
$L'$ with absolutely irreducible residual representation are homothetic.

Indeed, scale so that $L'\subseteq L$ but $L'\nsubseteq\varpi L$. The image of
$L'$ in $L/\varpi L$ is a nonzero stable subspace, hence all of the irreducible
residual representation. Nakayama gives $L'=L$. Undoing the scale proves
homothety. Thus the lattice selected by the Hecke-valued family and the lattice
underlying $\rho$ agree up to a scalar, which does not change the integral
representation after a choice of basis.

At $v\mid\ell$, the canonical lattice theorem supplies finite-flat models for
all quotients $L/\varpi^nL$ in the low-weight range, and these models are
compatible in $n$ and under finite coefficient extension. Conversely, the
hypothesis on $\rho$ says its quotients lie in the same represented local
functor. The homothety above and full faithfulness of the integral finite-flat
realization identify the two systems. Hence coefficient-prime local
compatibility survives the passage from generic representation to stable
lattice; it is not reconstructed from good-prime traces.

### 11.4 The lifting theorem proved

We can now finish Theorem 1.1.

**Proof of the lifting assertion.** The local hypotheses place $\rho$ in the
functor represented by $R^{\min}$, yielding (11.1). The minimal equality
(10.3) turns this point into a Hecke character. Section 11.1 extracts the
parallel-weight-two cuspidal representation $\pi$ with the required central
character and exact local types. Equation (11.2) identifies the generic
Galois representations, and Sections 11.2--11.3 identify their integral
lattices and finite-flat quotients. Thus $\rho\simeq\rho_\pi$. $\square$

Residual automorphy has therefore propagated from the closed point to every
point of the clean minimal deformation space. It was not necessary to assume
that the given characteristic-zero lift was itself known to lie on an
automorphic component.

## 12. Coefficient changes, descent, and exceptional cases

### 12.1 Extension of coefficients

Auxiliary residual eigenvalues, type characters, or branch fields may require
a finite extension $\mathcal O'/\mathcal O$. The represented clean local
conditions commute with this extension after selecting the residual local
factor corresponding to $\bar\rho\otimes_k k'$, and so does the global
universal property:

$$
R^{\min}_{\mathcal O'}
\simeq R^{\min}_{\mathcal O}
\widehat\otimes_{\mathcal O}\mathcal O'.
\tag{12.1}
$$

The exact integral automorphic module, faithful Hecke image, type lattices,
and primary--companion pairing also base-change. Regular sequences, finite
freeness, and the patched equality are preserved. Thus

$$
R^{\min}\widehat\otimes_{\mathcal O}\mathcal O'
\xrightarrow{\sim}
\mathbb T^{\min}\widehat\otimes_{\mathcal O}\mathcal O'.
\tag{12.2}
$$

Adequacy is preserved under extension of the residual field: the relevant
cohomology and semisimple spans extend scalars. Absolute irreducibility of the
cyclotomic restriction must hold before extension; changing coordinates does
not change its kernel.

Raw numerical lengths are not invariant under ramified coefficient extension.
If the ramification index is $e$, then

$$
\operatorname{length}_{\mathcal O'}
(N\otimes_{\mathcal O}\mathcal O')
=e\,\operatorname{length}_{\mathcal O}N
\tag{12.3}
$$

for finite-length $N$ under the respective uniformizer normalizations.
Fitting and congruence ideals base-change in the invariant manner; one should
not claim that their raw valuations remain numerically unchanged.

### 12.2 Descent to the original coefficient ring

Suppose the equality has been proved after a finite faithfully flat extension
$\mathcal O'/\mathcal O$. Let $K$ and $C$ be the kernel and cokernel of the
original map $R^{\min}\to\mathbb T^{\min}$. Completed base change is exact on
these finite modules, and (12.2) gives

$$
K\otimes_{\mathcal O}\mathcal O'=0,
\qquad
C\otimes_{\mathcal O}\mathcal O'=0.
$$

Faithful flatness implies $K=C=0$. Hence the equality descends. The same
argument descends finite projectivity, and over a local ring finite projective
modules are free. Complete-intersection and Gorenstein conclusions descend
here through the explicit regular-sequence presentation.

For an individual lift, one may extract $\pi$ after enlarging coefficients.
The compatible good-prime Hecke eigenvalues are the values of the original
Hecke character, so their field of definition is finite over the original
coefficient field. The Galois representation (11.3) descends with its trace
and determinant. If two descended forms become isomorphic after scalar
extension, strong multiplicity one identifies their automorphic
representations. Thus coefficient enlargement is a device for splitting
roots and fields, not an enlargement of the modularity conclusion.

### 12.3 The boundary at five and below

At $\ell=5$, the icosahedral natural representation can violate the adjoint
$H^1$ vanishing needed to restrict a global class nontrivially before applying
regular-semisimple detection. Then the localization matrix in Section 5.3 may
not be made invertible, and the sets $Q_N$ used in this proof have not been
constructed. Later commutative algebra cannot repair missing auxiliary
primes.

A theorem at five remains possible after a separate argument verifies the
full adequate package or eliminates the projective $A_5$ case. It is not a
consequence of absolute irreducibility alone, so the theorem proved here makes
no coefficient-five claim.

At $\ell=3$, further exceptional projective coincidences prevent a uniform
adequacy statement. At $\ell=2$, trace zero contains the scalar matrix,
$-1=1$ in the residue field, and the odd fixed-determinant deformation
calculation changes fundamentally. None of these primes can be included by
altering the inequality $\ell\geq7$ without replacing essential arguments.

### 12.4 Local and automorphic failures

If $F_v/\mathbf Q_\ell$ is ramified or the weights leave the low finite-flat
range, the local ring can be singular or reducible and the coefficient-prime tangent
contribution of Book 171, Section 4.3 can change. The equality of source dimensions imported in Chapter 9 then has to
be recomputed; the present theorem does not cover that problem.

If auxiliary Frobenius is scalar, no ordered eigenline is uniquely recoverable,
the old determinant of Book 172, Section 4.4 vanishes, and exact augmentation fails. If a
degeneracy image or type lattice is not saturated, generic oldness can leave
integral torsion, so module augmentation may recover a finite-index lattice
and its specialized named action need not have the desired minimal image.

If generic Hecke branches do not all carry compatible integral Galois
representations, there is no representation (4.3) over the localized order
and hence no map (4.4). Patching modules cannot create that missing map. If
the automorphic module is zero, its scalar action cannot detect a kernel.

Finally, a nonminimal condition introduces new local components and changes
both Selmer groups and automorphic level control. Minimal equality is an input
to that later comparison, not a proof of it. The new problem requires its own
component-support and patching argument.

## 13. The minimal modularity package

### 13.1 Dependency and hypothesis audit

The proof uses the established foundations in exact forms.

Global deformation theory supplies representability, Selmer tangent spaces,
Poitou--Tate duality, frame corrections, and presentation bounds under a
finite controlling set, fixed determinant with $\ell\ne2$, a Schur residual
representation, and represented base-change-stable local conditions. Those
hypotheses are recorded in Chapters 2--3.

The abstract comparison theory supplies depth transfer, regular-sequence
descent, congruence ideals, and the distinction between support and
faithfulness. Its hypotheses are met only after the finite free diamond
module, exact augmentation, and regular source have been constructed; none is
assumed prematurely.

Weight-two Galois attachment supplies branchwise representations with
polynomial (2.1), total oddness, and the fixed determinant. Canonical lattice
and finite-flat quotient theory supplies the integral representation at
$v\mid\ell$. These results are used only for branches in their stated
parallel-weight-two, noncharacter, integral-realization range.

Integral type theory supplies primary and companion lattices, saturation, and
closed represented tame or special components away from $\ell$. Primitive
wild types and uncontrolled small residue-characteristic cases are excluded.

Residual image classification supplies adequacy from absolute irreducibility
of the cyclotomic restriction only for $\ell\geq7$, together with the precise
prime-five exception. The Taylor--Wiles prime theorem supplies the additional
underlying-prime-field disjointness and split-detection clauses; Section 5.2
checks them from the same finite-image classification after coefficient
extension. Book 171's adjoint-twist invariant is not folded into adequacy: it
vanishes directly by its adjoint-invariant calculation because the cyclotomic restriction is absolutely
irreducible.

The minimal totally real comparison supplies the ring $R^{\min}$, the faithful
Hecke order $\mathbb T^{\min}$, the Hecke-valued representation, the
surjection, exact local matching, the balanced integer $q$, and the auxiliary
numerical ledger. Minimal patching supplies the deep-level system, coherent
finite shadows, equal-variable rigidity, exact descent, and the structural
consequences. Every hypothesis of those two results appears in Theorem 1.1;
none is weakened to a slogan such as “large image,” “minimal conductor,” or
“standard local compatibility.”

### 13.2 Final synthesis

The minimal lifting theorem is a rigidity statement created by an exact
arithmetic balance. Finite flatness contributes the sum of the local degrees
above $\ell$; total oddness subtracts the number of real embeddings. Their
cancellation makes the primal and dual Selmer dimensions equal. The split
Taylor--Wiles image package turns the common dimension $q$ into $q$ ordered
auxiliary primes, and fixed determinant gives one diamond character at each
of them.

On the automorphic side, definite-quaternionic torsors make the deep-level
module free over the diamond group ring. The unit old-form determinant,
saturation, ordered roots, and companion adjunction ensure that augmentation
returns the exact minimal lattice and that the named action has image the
minimal Hecke order. Its faithfulness as a deformation action is then proved
after patching. Coherent finite shadows replace a nonexistent tower of
auxiliary levels.

The patch then places a nonzero free module between two regular power-series
sources of dimension $q+1$. Faithful scalar action forces the action image to
have full dimension; the domain property of the deformation source forces its
kernel to vanish. Maximal depth gives freeness, and regular augmentation gives

$$
R^{\min}=\mathbb T^{\min}.
$$

Every minimal characteristic-zero lift is consequently a Hecke point. The
weight-two packet attached to that point has the prescribed local conditions,
and residual irreducibility identifies its canonical integral lattice with
the given lift. Coefficient extension and faithfully flat descent preserve the
statement. The resulting package is exactly minimal modularity lifting over a
totally real field in the clean coefficient-prime range $\ell\geq7$: residual
automorphy propagates to every integral minimal lift, with determinant, local
types, finite-flat quotients, and coefficient descent all retained.
