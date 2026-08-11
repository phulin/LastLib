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
  - [7.4 Exact module and Hecke augmentation](#74-exact-module-and-hecke-augmentation)
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

Third, adequacy supplies sets of Taylor--Wiles primes that kill the dual
Selmer group. At a set of $q$ primes one obtains exactly $q$ diamond
variables. The deep-level automorphic module is free over the corresponding
finite group algebra, and augmentation recovers the exact minimal objects.

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
Put $M=\operatorname{ad}^0\bar\rho$ and assume separately that

$$
H^0(F,M(1))=0.
\tag{1.4a}
$$

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
4. The localized automorphic modules satisfy finite freeness over
   $\mathcal O$, effective stabilizer and diamond-torsor control, integral
   saturation of type lattices and degeneracy maps, a perfect
   primary--companion pairing, generic reducedness of the Hecke algebra, and
   branchwise Galois attachment with integral local--global compatibility.

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
after cyclotomic restriction supplies adequacy in the group actually used to
choose auxiliary primes. The bound $\ell\geq7$ makes that implication uniform
in dimension two.

The finite-flat hypothesis is not shorthand for being crystalline after
inverting $\ell$. It is an integral condition on all Artinian quotients and is
the source of the exact local tangent contribution. The local conditions away
from $\ell$ are not specified merely by conductors. Their integral labels and
component closures ensure representability and exact automorphic matching.

Residual automorphy is also more precise than equality of good-prime traces.
It selects a non-Eisenstein maximal ideal in a particular integral module.
The saturation and pairing assumptions ensure that auxiliary-level
coinvariants return to that same lattice, rather than to a finite-index
variant. Generic reducedness and branchwise attachment are used to construct
the Hecke-valued Galois representation; they are not used as a substitute for
the later proof of faithfulness.

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

### 2.1 Coefficients, determinant, and Frobenius

Fix a finite set $S$ containing every real place, every place above $\ell$,
and every finite place at which $\bar\rho$, $\delta$, the quaternion algebra,
the automorphic level, or a chosen local type ramifies. All representations
factor through $G_{F,S}$.

Put

$$
M=\operatorname{ad}^0\bar\rho.
\tag{2.1}
$$

Since $\ell$ is odd, the scalar and trace-zero summands of
$\operatorname{ad}\bar\rho$ split. The trace pairing identifies
$M^*(1)$ with $M(1)$. Absolute irreducibility gives

$$
H^0(F,M)=0.
\tag{2.2}
$$

We use geometric Frobenius $\Phi_v$. At a good finite place the automorphic
and Galois characteristic polynomial is

$$
X^2-T_vX+q_vS_v,
\tag{2.3}
$$

where $q_v$ is the residue cardinality and $S_v$ is the central operator. The
determinant compatibility is therefore

$$
\delta(\Phi_v)=q_vS_v.
\tag{2.4}
$$

The factor $S_v$ must be retained unless the central character has actually
been trivialized. Dropping it changes the fixed-determinant deformation
problem. Replacing geometric by arithmetic Frobenius would invert all three
normalizations: Frobenius, reciprocity, and the diamond involution. Any one
convention works, but they cannot be mixed.

The determinant is fixed throughout. Consequently the deformation
coefficient module is $M$, not all of $\operatorname{ad}\bar\rho$, and there
is only one independent tame character at each auxiliary prime. A twist by a
fixed character changes both $\delta$ and the central character; twisting only
one side would destroy (2.4).

### 2.2 Total oddness and residual automorphy

For every real place $v$, choose a complex conjugation $c_v$. Total oddness is

$$
\det\bar\rho(c_v)=-1.
\tag{2.5}
$$

Because $2$ is invertible, $\bar\rho(c_v)$ has a $+1$ and a $-1$ line. The
odd conjugacy class is rigid in deformations with determinant $-1$, but
conjugation fixes the trace-zero diagonal endomorphism. Hence

$$
L_v=0,
\qquad h^0(F_v,M)=1
\tag{2.6}
$$

at every real place. The resulting contribution $-1$ will be essential.

Residual automorphy means that a specified definite-quaternionic Hecke module
$M^{\min}$ has a non-Eisenstein maximal ideal $\mathfrak m$ such that

$$
T_v\bmod\mathfrak m=\operatorname{tr}\bar\rho(\Phi_v),
\qquad
q_vS_v\bmod\mathfrak m=\det\bar\rho(\Phi_v)
\tag{2.7}
$$

away from $S$. Its residue field is $k$ after a permitted finite coefficient
extension. At least one characteristic-zero branch through $\mathfrak m$ is
cuspidal, noncharacter, and parallel weight two, with the declared local
types. Every generic branch in the localization must lie in the range where
a rank-two Galois representation and integral local compatibility are known.

The first clause makes the localized module nonzero. The last clause is needed
because the Hecke order can contain several congruent branches. Constructing a
representation over the entire order requires control of every branch, not
only the distinguished residual source.

### 2.3 Finite flatness at the coefficient prime

Let $v\mid\ell$ and put $f_v=[F_v:\mathbf Q_\ell]$. We assume that
$F_v/\mathbf Q_\ell$ is unramified and that $\bar\rho|_{G_v}$ belongs to the
rank-two finite-flat range of weights $\{0,1\}$. An Artinian lift belongs to
the local condition if it is the generic fiber of a finite locally free group
with coefficient action, height two, the specified weights at every residue
embedding, and determinant $\delta|_{G_v}$.

This condition is imposed on every Artinian quotient. If a single
characteristic-zero representation is crystalline, an arbitrary stable
lattice need not have all of its torsion quotients represented by the required
finite flat groups. The integral condition is therefore genuinely stronger
than a generic-fiber statement.

For an elliptic curve with good reduction over an unramified extension of
$\mathbf Q_\ell$, the finite flat group schemes of $\ell^n$-torsion provide
the model example. Their generic fibers form the quotients of the Tate module,
and their determinant has the required cyclotomic normalization. The local
condition here is not restricted to elliptic curves: it is the deformation
functor characterized by the same low-weight integral linear algebra. Height,
coefficient action, and the models on all quotients keep its rank fixed under
arbitrary Artinian base change.

The unramified-base hypothesis is visible in the tangent formula. There is one
Hodge-filtration direction for each residue embedding, giving the $f_v$ in
(2.9); the three remaining framed directions move a basis. Ramification can
couple filtration and descent data, so this elementary count cannot be
carried outside the stated range without a different local theorem.

The clean local theorem gives a formally smooth framed fixed-determinant ring
of relative dimension

$$
f_v+3.
\tag{2.8}
$$

If $L_v\subset H^1(F_v,M)$ is its unframed tangent condition, then

$$
\dim_kL_v-h^0(F_v,M)=f_v.
\tag{2.9}
$$

To see the compatibility of these two formulas, framed cocycles add the
coboundary space, whose dimension is $3-h^0(F_v,M)$. Thus the framed tangent
has dimension

$$
\dim_kL_v+3-h^0(F_v,M)=f_v+3.
$$

This remains valid when the local residual centralizer is larger than the
scalars. In that case the framed local functor is the safe represented object;
one does not assume an unframed local coarse ring.

### 2.4 Minimal conditions away from the coefficient prime

At a finite $v\nmid\ell$ there are three clean possibilities.

If the residual representation is unramified, require every lift to be
unramified. Then

$$
L_v=H^1_{\mathrm{ur}}(F_v,M)
\simeq M/(\Phi_v-1)M.
\tag{2.10}
$$

The kernel and cokernel of the square operator $\Phi_v-1$ have equal
dimension, so

$$
\dim_kL_v=h^0(F_v,M).
\tag{2.11}
$$

If inertia factors through a finite group $J_v$ of order prime to $\ell$, fix
an integral lift of the precise inertia representation, including any
ordering, finite character, or dihedral return datum. Averaging over $J_v$
makes inertia rigid, and

$$
L_v\simeq M^{J_v}/(\Phi_v-1)M^{J_v}.
\tag{2.12}
$$

The same kernel--cokernel argument proves (2.11).

At a minimal-special place, retain a named invariant line, a sign or
Frobenius eigenvalue compatible with $\delta$, and a nilpotent monodromy
operator satisfying

$$
N^2=0,
\qquad
\rho(\Phi_v)N\rho(\Phi_v)^{-1}=q_v^{-1}N.
\tag{2.13}
$$

The condition is the schematic closure of the named special component. We
assume its represented framed ring is smooth in the chosen convention and
its tangent is neutral:

$$
\dim_kL_v=h^0(F_v,M).
\tag{2.14}
$$

This hypothesis excludes collisions of signs, uncontrolled Kummer
directions, and other singular residual charts.

In a basis adapted to the invariant line, a typical special representation
has the schematic shape

$$
\rho(\sigma)=
\begin{pmatrix}1&t_\ell(\sigma)n\\0&1\end{pmatrix},
\qquad
\rho(\Phi_v)=
\begin{pmatrix}a&b\\0&q_va\end{pmatrix},
\tag{2.14a}
$$

up to fixed scalar inertia and normalization. The relation among $a,b,n$ and
monodromy is polynomial. The locus $n\ne0$ is not closed, whereas the
component through a chosen residual point is. Reduction modulo an ideal
containing $n$ produces zero monodromy; the closure retains that specialization
without forgetting its component of origin.

The fixed-type case has a similarly concrete rigidity proof. Since $|J_v|$
is a unit, averaging splits invariants and kills positive cohomology of
$J_v$. A deformation of its inertia representation is therefore conjugate to
the chosen integral lift. All remaining first-order freedom lies in the
centralizer and is unramified, which proves (2.12) without appealing to
constancy of a conductor.

Thus every clean finite place away from $\ell$ contributes zero to the global
defect. That equality is a consequence of the actual local equations, not of
the numerical conductor.

### 2.5 What minimal does not mean

Several tempting formulations fail to define deformation conditions.

Requiring special monodromy to be nonzero is open, not closed. If its parameter
is $n\in A$, reduction modulo an ideal containing $n$ makes the monodromy zero.
The resulting quotient must remain in a deformation functor. The schematic
component closure includes it; the condition $n\ne0$ does not.

Likewise, an inertial type over the fraction field does not specify an
integral type lattice. Two lattices in the same rational representation can
have different reductions and congruence indices. Ordering characters and
choosing primary and companion lattices are part of the datum whenever the
reduction does not distinguish the branches.

Finally, allowing ramification at a place is not the same as imposing the
unramified minimal condition. Enlarging $S$ only changes the ambient Galois
group. One must still cut out the unramified quotient. These distinctions are
what make the global functor stable under coefficient quotients and what make
the later augmentation maps exact.

Several examples test the distinctions. Over $F=\mathbf Q$, take a
semistable elliptic curve with good reduction at $\ell$. At a multiplicative
prime $p\ne\ell$, its Tate module has a special filtration and a split or
nonsplit sign. If the residual extension class remains nonzero, the named
special component is the natural minimal condition. If the extension class
vanishes modulo $\ell$, the residual point can lie on several closures; the
phrase “multiplicative conductor one” no longer selects a unique represented
component. The clean theorem requires that choice to have been made and its
tangent neutrality proved.

For a fixed tame principal type, suppose inertia characters $\theta_1$ and
$\theta_2$ are distinct in characteristic zero but become congruent modulo
$\varpi$. The rational unordered pair does not remember which residual line
lifts $\theta_1$. An ordered integral type lattice does. The two choices can
have identical conductor and generic inertial semisimplification while giving
different integral projectors. This is the same phenomenon that later forces
ordered roots at auxiliary primes.

At an unramified place where Frobenius on $M$ has eigenvalues $1,a,b$, with
$a,b\ne1$, both $M^{\Phi_v=1}$ and
$M/(\Phi_v-1)M$ are one-dimensional. If $a=1$, both dimensions jump to two.
The local centralizer has grown, but neutrality survives because kernel and
cokernel dimensions of one square matrix remain equal. This example explains
why neutrality is compatible with residual centralizer jumps even though an
unframed local moduli space may cease to be representable.

Finally, consider two stable lattices in the same unramified
characteristic-zero representation whose Frobenius eigenvalues are congruent.
Their reductions can be a split sum or a nonsplit extension. Good-prime
characteristic polynomials do not distinguish them. The finite-flat and type
lattice conditions do, which is why good traces alone cannot establish the
integral local factorization used in Chapter 4.

## 3. The global minimal deformation problem

### 3.1 Representability and tangent spaces

For an Artinian local $\mathcal O$-algebra $A$ with residue field $k$, let
$D^{\min}(A)$ be the set of strict-equivalence classes of lifts

$$
\rho_A:G_{F,S}\longrightarrow\operatorname{GL}_2(A)
$$

such that $\rho_A\bmod\mathfrak m_A=\bar\rho$,
$\det\rho_A=\delta$, and every restriction belongs to its named local
condition. Absolute irreducibility gives
$\operatorname{End}_{k[G_F]}(\bar\rho)=k$. Together with closed represented
local conditions and global cohomological finiteness, this Schur condition
proves that $D^{\min}$ is represented by a complete Noetherian local
$\mathcal O$-algebra $R^{\min}$.

For dual numbers, write

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g).
$$

The homomorphism equation says that $c$ is a $1$-cocycle. Fixing determinant
forces $\operatorname{tr}c=0$, and strict conjugacy changes $c$ by a
coboundary. Therefore

$$
t_{R^{\min}}\simeq H^1_{\mathcal L}(F,M),
\tag{3.1}
$$

where

$$
H^1_{\mathcal L}(F,M)=
\ker\left(
H^1(G_{F,S},M)\longrightarrow
\bigoplus_{v\in S}H^1(F_v,M)/L_v
\right).
\tag{3.2}
$$

This is the primal Selmer group. It measures actual first-order minimal
deformations. Summing local tangent dimensions does not compute it, because
global classes satisfy localization relations.

Representability does not require $H^2$ to vanish. Obstruction classes give
relations in the universal ring. The global deformation theory supplies a
presentation whose generator space is (3.1) and whose relation number is
bounded by the corresponding obstruction space. That distinction will matter
when auxiliary conditions are introduced.

To see the obstruction mechanism, let $A'\twoheadrightarrow A$ be a small
extension with square-zero kernel $I$. Choose arbitrary matrix lifts to $A'$
of a representation over $A$. Their failure to multiply is a continuous
$2$-cocycle with values in $M\otimes_k I$. Changing the provisional lifts
changes it by a coboundary. Vanishing of its class lets one correct the
matrices into a representation. Local obstruction classes and the mismatch
between global and local corrections are recorded by the mapping cone of the
global-to-local cochain map. A complete obstruction space therefore bounds
equations even when it is nonzero. Formal smoothness means that the actual
obstruction map vanishes; it need not mean that the ambient $H^2$ is zero.

Frames fit this construction without adding arithmetic. A local frame retains
a basis, so cocycles are not divided by local coboundaries. Restriction maps
are then representable even if a local residual centralizer is nonscalar. The
global Schur condition removes the frames later with correction (3.10).

### 3.2 The dual Selmer group

Local Tate duality gives perfect pairings

$$
H^1(F_v,M)\times H^1(F_v,M(1))\longrightarrow k.
\tag{3.3}
$$

Let $L_v^\perp$ be the exact annihilator of $L_v$. The dual Selmer group is

$$
H^1_{\mathcal L^\perp}(F,M(1))=
\ker\left(
H^1(G_{F,S},M(1))\longrightarrow
\bigoplus_{v\in S}H^1(F_v,M(1))/L_v^\perp
\right).
\tag{3.4}
$$

At $v\mid\ell$, $L_v^\perp$ is defined as this exact annihilator. It must not
be identified with another geometric finite-flat condition unless an integral
duality theorem proves that identification.

Set

$$
q=\dim_kH^1_{\mathcal L^\perp}(F,M(1)).
\tag{3.5}
$$

The integer $q$ is the number of dual conditions to be killed, the number of
Taylor--Wiles primes, and ultimately the number of diamond variables. It is
an absolute unframed number. Relative obstruction dimensions computed after
placing framed local rings in the base are different quantities and must not
be substituted for it.

### 3.3 The totally real balance

Poitou--Tate duality gives the Wiles formula

$$
\begin{aligned}
&h^1_{\mathcal L}(F,M)-h^1_{\mathcal L^\perp}(F,M(1))\\
&\quad=h^0(F,M)-h^0(F,M(1))
+\sum_{v\in S}\bigl(\dim_kL_v-h^0(F_v,M)\bigr).
\end{aligned}
\tag{3.6}
$$

Here $H^0(F,M)=0$. The cyclotomic restricted-image hypothesis, together with
the absence of the corresponding trace-zero self-twist in the clean datum,
gives

$$
H^0(F,M(1))=0.
\tag{3.7}
$$

Every finite place away from $\ell$ contributes zero by (2.11), (2.12), or
(2.14). The places above $\ell$ contribute

$$
\sum_{v\mid\ell}[F_v:\mathbf Q_\ell]=[F:\mathbf Q].
\tag{3.8}
$$

There are $[F:\mathbf Q]$ real places, each contributing $-1$ by (2.6). Thus
the sum in (3.6) vanishes and

$$
h^1_{\mathcal L}(F,M)
=h^1_{\mathcal L^\perp}(F,M(1))=q.
\tag{3.9}
$$

This proves the balance. It is not a formal consequence of total reality: it
uses unramifiedness of every $F_v/\mathbf Q_\ell$, weights $\{0,1\}$, and
neutrality of every other finite local condition. For a real quadratic field
where $\ell$ is inert, one coefficient-prime place contributes $2$ and two
real places contribute $-1-1$. When $\ell$ splits, two coefficient-prime
places contribute $1+1$. The cancellation is by total degree, not by pairing
individual places.

We recall why (3.6) has exactly this sign. The Poitou--Tate localization
sequence compares the kernel defined by $L_v$ with the dual kernel defined by
$L_v^\perp$. Taking alternating dimensions leaves the global invariant terms
$h^0(F,M)-h^0(F,M(1))$. At a local place, replacing all of
$H^1(F_v,M)$ by the allowed subspace $L_v$ changes the Euler characteristic
by $\dim L_v-h^0(F_v,M)$. The $h^2$ term becomes the $h^0$ term of the Tate
dual and cancels because $L_v^\perp$ is the exact annihilator. This derives
(3.6) without assuming a geometric description of the dual finite-flat
condition.

The balance has a determinant-line version. The minimal Selmer complex is the
mapping fiber

$$
C^\bullet_{\mathcal L}(F,M)=
\operatorname{Cone}\left(
C^\bullet(G_{F,S},M)\oplus\bigoplus_{v\in S}L_v^\bullet
\longrightarrow\bigoplus_{v\in S}C^\bullet(F_v,M)
\right)[-1].
\tag{3.9a}
$$

Its determinant line has virtual degree zero because the finite-flat local
degrees sum to $[F:\mathbf Q]$ and the real degrees sum to its negative. This
does not canonically trivialize the line: a degree-zero line still needs a
basis. Separate deformation and automorphic self-dualities therefore do not
supply a comparison basis before patching.

### 3.4 Framed and unframed counts

Frames are retained locally to remove local automorphisms. If $T$ is a
nonempty framing set, raw changes of two-dimensional bases contribute four
directions at each place, while the single global scalar stabilizer acts
trivially. Thus the comparison between compatible framed and unframed global
problems has relative dimension

$$
4|T|-1.
\tag{3.10}
$$

It is incorrect to replace this by $3|T|$. The number three is the dimension
of $M=\operatorname{ad}^0\bar\rho$ and also the relative dimension of several
fixed-determinant framed local rings away from $\ell$; it is not the number of
raw frame coordinates.

Relative presentations over a completed tensor product of framed local rings
have strict Selmer generators and relaxed dual-Selmer relation bounds. Those
two counts may vary with the auxiliary level. One can stabilize them by adding
a variable together with a linear equation, but such a padded pair contributes
no geometric dimension. The kernel-killing proof below instead removes frames
and uses the exact absolute tangent dimension $q$ from (3.9). This produces a
common $q$-variable source without claiming that each finite auxiliary ring is
smooth or has no relations.

It is useful to retain the relative ledger as an audit. Let

$$
R_{\mathrm{loc}}^{\min}
=\widehat\bigotimes_{v\in T,\mathcal O}R_v^{\square,\min}.
\tag{3.11}
$$

The framed global ring has a presentation

$$
R^{\square_T,\min}\simeq
R_{\mathrm{loc}}^{\min}[[Y_1,\ldots,Y_{g_T}]]/(r_1,\ldots,r_s),
\qquad s\leq q_T,
\tag{3.12}
$$

where $g_T$ is a strict primal tangent count and $q_T$ a relaxed dual count.
Global duality computes their difference after inserting the local dimensions
and the $4|T|-1$ gauge correction; it does not identify them separately. At
auxiliary level they can vary even though the absolute tangent dimension is
always $q$. If a displayed presentation is padded by a new variable $Y$ and
the relation $Y=0$, that acyclic pair contributes no geometric dimension.

After removing the genuine smooth frame torsor, the absolute cotangent space
is exactly (5.5). Topological Nakayama then gives the source (9.1). This route
allows whole quotient ideals to be patched without inventing a uniform
minimal relation tuple, while (3.12) continues to certify effective
obstruction theory and correct variance.

## 4. The automorphic side and the comparison map

### 4.1 Definite quaternionic forms

Choose a totally definite quaternion algebra $B/F$, a compact open level
$U\subset(B\otimes_F\mathbf A_{F,f})^\times$, and a parallel-weight-two
coefficient lattice whose local factors realize the conditions of Chapter 2.
The parity of the ramification set of $B$ is part of this choice. It cannot be
deduced from the Galois conductor alone.

Because $B$ is totally definite, the relevant automorphic module is a finite
module of functions on a finite double-coset groupoid. After localization at
the non-Eisenstein maximal ideal $\mathfrak m$, denote the selected primary
module by $M^{\min}$. The standing integral hypotheses give

$$
M^{\min}\text{ finite free over }\mathcal O.
\tag{4.1}
$$

Let $\mathbb T^{\min}$ be the faithful image of the Hecke operators on this
module. By definition its action is faithful; this says nothing yet about the
faithfulness of $R^{\min}$. We assume, as supplied by the exact automorphic
realization, that $\mathbb T^{\min}$ is a complete local finite-flat
$\mathcal O$-algebra and that its generic fiber is reduced.

### 4.2 Integral types, companions, and pairings

A rational local type does not determine the lattice used in congruence
arguments. At every type place choose a primary lattice and the companion
lattice dictated by the adjoint involution. The retained local theory supplies
a perfect pairing

$$
\mathcal H^{\min}:M^{\min}\times M^{\min,\dagger}
\longrightarrow\mathcal O.
\tag{4.2}
$$

Hecke operators are adjoint under inverse double cosets. At an oriented place,
the adjoint of the operator selecting one ordered root generally selects the
companion root. The primary projector is therefore not silently
self-adjoint. This is why a second module is carried through patching.

Saturation has two roles. A saturated type lattice has the intended reduction
inside the integral automorphic module. A saturated degeneracy image has
torsion-free quotient, so a generic old/new splitting descends integrally.
Without these statements, augmentation could recover a lattice of finite
index rather than $M^{\min}$, changing its congruence ideal.

### 4.3 The Hecke-valued representation

Every generic branch of $\mathbb T^{\min}[1/\ell]$ supplies a rank-two Galois
representation with characteristic polynomial (2.3) at good places. Since
the generic algebra is reduced, their product is a representation over the
total generic algebra. Residual absolute irreducibility allows traces to
descend through the integral Hecke order: a trace algebra with scalar residual
centralizer carries an actual rank-two representation, unique up to strict
conjugacy. Thus one obtains

$$
\rho_{\mathbb T}:G_{F,S}\longrightarrow
\operatorname{GL}_2(\mathbb T^{\min})
\tag{4.3}
$$

with determinant $\delta$.

The integral local--global compatibility hypotheses do more than identify
generic Weil--Deligne representations. They show that every Artinian quotient
of (4.3) belongs to the represented finite-flat condition above $\ell$ and to
the named closed local component away from $\ell$. This is precisely what is
needed to apply the universal property of $R^{\min}$.

The construction explains why the canonical lattice and finite-flat quotient
theory is indispensable. A characteristic-zero branch alone supplies a vector
space representation. Integral realization provides a stable lattice, and
finite-flat full faithfulness shows that all its coefficient-prime torsion
quotients lie in the desired finite-flat functor. Only then is (4.3) a point
of the global integral deformation problem.

The descent from branches to the order deserves emphasis. Write the reduced
generic algebra as $\prod_iE_i$ and let $\rho_i$ be the representation on the
$i$th factor. Their traces lie in $\mathbb T^{\min}$ because good traces are
Hecke operators and density extends the identity continuously to all Galois
elements. The residual trace is absolutely irreducible. The trace-algebra
descent theorem then turns the resulting two-dimensional pseudorepresentation
over the complete local order into an actual representation, unique up to
strict conjugacy. Thus the result is independent of bases on the generic
factors.

There are two integral checks after trace descent. For each closed local
quotient $R_v^\square\twoheadrightarrow R_v^{\square,\min}$, branchwise
compatibility says that the map to every $E_i$ kills its defining ideal. The
Hecke order is torsion-free and embeds in $\prod_iE_i$, so that ideal is killed
integrally. At coefficient-prime places, generic crystalline behavior alone
does not give the factorization; canonical lattices and their finite-flat
quotients supply it on every Artinian quotient. These checks put (4.3) in the
integral functor rather than only on its generic fiber.

### 4.4 The surjection from deformations to Hecke operators

Universality applied to (4.3) gives

$$
\theta:R^{\min}\longrightarrow\mathbb T^{\min}.
\tag{4.4}
$$

At every good place, the universal trace maps to $T_v$ and the universal
determinant maps to $q_vS_v$. The faithful Hecke algebra is generated by these
good traces together with the fixed central and local operators already
determined by the local types. Hence the image of $\theta$ contains all
generators, so

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min}.
\tag{4.5}
$$

The direction follows the contravariance of representing rings: an
automorphic family is an object of the deformation functor, hence determines
a map from the universal deformation ring to its coefficient ring.

Nothing in this proof gives injectivity. The target being finite flat and
generically reduced does not prevent the source from having an extra
component or a nilpotent kernel. Pairing self-duality on the automorphic side
and Tate duality on the Galois side do not by themselves construct a
comparison of determinant lines. The kernel is eliminated only after the
auxiliary system has been built.

For example, the surjection

$$
\mathcal O[[u]]/(u^2)\twoheadrightarrow\mathcal O,
\qquad u\longmapsto0,
$$

has a finite-flat reduced target and is an isomorphism on its visible generic
branch, but its nilpotent kernel is nonzero. Replacing the source by its
reduction would erase precisely the information an integral congruence
theorem must retain.

## 5. Adequacy and Taylor--Wiles primes

### 5.1 Why cyclotomic irreducibility is the right image hypothesis

Taylor--Wiles primes must satisfy a cyclotomic congruence
$q_x\equiv1\pmod{\ell^N}$. Their Frobenius elements therefore lie in a
cyclotomic restricted Galois group. It is the image of
$G_{F(\zeta_\ell)}$, not merely the full image of $G_F$, that must detect
adjoint cohomology classes.

An absolutely irreducible representation can become reducible on a normal
subgroup: a dihedral representation induced from a quadratic extension is the
standard example. Thus global absolute irreducibility supplies the Schur
condition but does not imply the image property needed for prime selection.
The separate hypothesis

$$
\bar\rho|_{G_{F(\zeta_\ell)}}\text{ absolutely irreducible}
\tag{5.1}
$$

closes this gap.

For a finite image $G\subset\operatorname{GL}_2(k)$, adequacy consists of the
relevant scalar and adjoint $H^1$ vanishings together with the assertion that
semisimple elements span $\operatorname{End}(k^2)$. The spanning condition
implies regular-semisimple detection: a nonzero trace-zero adjoint direction
pairs nontrivially with some nonscalar semisimple element, which in dimension
two has distinct eigenvalues after a finite coefficient extension.

The spanning clause is easy to interpret. If every semisimple image element
paired trivially with a nonzero $w\in\operatorname{ad}^0(k^2)$, then $w$
would pair trivially with their span, hence with all of
$\operatorname{End}(k^2)$, contradicting nondegeneracy of the trace pairing.
A detecting semisimple element cannot be scalar because trace-zero $w$ pairs
trivially with scalars. It is therefore regular semisimple in dimension two.
The cohomology vanishings ensure that the finite cocycle extensions used in
the selection do not collapse into scalar or cyclotomic directions.

### 5.2 The coefficient-prime bound

In characteristic $\ell\geq7$, every absolutely irreducible two-dimensional
finite image is adequate. Applied to (5.1), this gives the exact adequacy
package on the cyclotomic restricted image. Adequacy is preserved by finite
extension of the residual coefficient field, so one may enlarge coefficients
to split selected residual Frobenius polynomials.

The prime five is different. A natural characteristic-five representation
with projective image

$$
A_5\simeq\operatorname{PSL}_2(\mathbf F_5)
$$

can have nonzero adjoint first cohomology. Absolute irreducibility therefore
does not give adequacy uniformly at five. Some prime-to-five dihedral,
$A_4$, or $S_4$ images remain adequate, and an individual theorem at five can
proceed after checking every adequacy clause or excluding the icosahedral
case. The present route uses the uniform implication and hence begins at
$\ell=7$.

Adequacy does not imply $H^0(F,M(1))=0$ by definition, nor does it compute the
Selmer group. Those are separately recorded in (3.7) and (3.5). Adequacy's
job is to make nonzero dual classes detectable by regular semisimple
Frobenius elements while satisfying the cyclotomic congruence.

### 5.3 Detecting the dual Selmer group

Let $q$ be as in (3.5). For each $N\geq1$, choose a set $Q_N$ of exactly $q$
finite places, disjoint from $S$ and from any prescribed finite avoidance set,
such that

$$
q_x\equiv1\pmod{\ell^N}
\tag{5.2}
$$

and $\bar\rho(\Phi_x)$ has two distinct eigenvalues. At each $x$, order the
two roots and retain one eigenline.

We explain the selection. Choose a basis
$\phi_1,\ldots,\phi_q$ of the dual Selmer group. A class $\phi_i$ cuts out a
finite elementary abelian extension over the compositum of the residual and
cyclotomic fields. Adequacy supplies a regular semisimple residual element
whose diagonal projection detects $\phi_i$. Linear disjointness from the
already selected cocycle extensions makes it possible to impose zero
detection on earlier basis vectors and nonzero detection on the next. The
cyclotomic congruence, residual conjugacy class, and avoidance conditions are
conditions in one finite Galois compositum. The density theorem for Frobenius
classes then supplies a place realizing them simultaneously.

Inductively, the localization matrix of the $\phi_i$ at the selected ordered
eigenlines is invertible. Hence the auxiliary dual Selmer group vanishes:

$$
H^1_{\mathcal L_{Q_N}^\perp}(F,M(1))=0.
\tag{5.3}
$$

The sets for different $N$ need not be nested and may be chosen disjoint. A
fixed prime cannot serve at all depths because the valuation of $q_x-1$ is
finite. This fact will determine the compactness form of patching.

More explicitly, suppose $x_1,\ldots,x_{i-1}$ have been chosen. Take a linear
combination of the $\phi_j$ vanishing at those places but nonzero in the next
undetected direction. Its cocycle field is an elementary abelian extension
over the residual cutout. Adequacy ensures that this extension has an element
whose semidirect-product component pairs nontrivially with a regular
semisimple residual matrix. Adjoin the $\ell^N$-cyclotomic field and every
field used for avoidance. The required element has trivial cyclotomic
component, the chosen residual matrix component, and the prescribed cocycle
component. The compatibility statements in adequacy ensure these coordinates
define an element of the actual compositum rather than merely of a formal
product. A Frobenius place with that conjugacy class supplies $x_i$. Row
reduction makes the final localization matrix triangular with nonzero
diagonal, hence invertible.

This proof also shows why a slogan such as “large residual image” is
insufficient. One needs the actual finite-image cohomology vanishings,
semisimple detection, compatibility with the cyclotomic quotient, and an
avoidance theorem. Conversely, containing a full special linear group is
stronger than necessary; prime-to-$\ell$ dihedral or exceptional images may
also be adequate.

### 5.4 The exact auxiliary ledger

At $x\in Q_N$, replacing the unramified local condition by the ordered
Taylor--Wiles condition adds one tangent direction. Comparison of Selmer
structures gives an exact segment

$$
\begin{aligned}
0\to H^1_{\mathcal L}(F,M)
&\to H^1_{\mathcal L_{Q_N}}(F,M)
\to\bigoplus_{x\in Q_N}L_x^{\mathrm{TW}}/L_x^{\mathrm{ur}}\\
&\to H^1_{\mathcal L^\perp}(F,M(1))^\vee
\to H^1_{\mathcal L_{Q_N}^\perp}(F,M(1))^\vee\to0.
\end{aligned}
\tag{5.4}
$$

The middle direct sum and the minimal dual Selmer group both have dimension
$q$. The connecting map is the transpose of the invertible localization
matrix used above, and the final term vanishes by (5.3). Exactness therefore
gives

$$
H^1_{\mathcal L}(F,M)
\xrightarrow{\sim}H^1_{\mathcal L_{Q_N}}(F,M),
\qquad
h^1_{\mathcal L_{Q_N}}(F,M)=q.
\tag{5.5}
$$

This is the sharp absolute count. The auxiliary local group rings still have
finite-order equations, so (5.3) does not say that the finite-level global
ring is a power-series ring. It says only that the universal auxiliary ring
has exactly $q$ topological generators over $\mathcal O$.

There are two complementary facts in (5.4). Killing the auxiliary dual group
removes obstruction directions, while the $q$ relaxed local tangent lines
replace exactly the $q$ minimal dual conditions. Exactness then says that the
primal tangent group does not grow. The same $q$ therefore counts the original
minimal tangent, the original dual tangent, the number of auxiliary places,
and the number of tame diamond coordinates. Confusing any of these with the
relative framed relation count breaks the equal-variable proof.

The local quotient in the middle of (5.4) is concrete. With the ordered
eigenline fixed, an unramified deformation lets the Frobenius eigenvalue vary.
The Taylor--Wiles condition retains that direction and adds the differential
of one tame character; fixed determinant forces the character on the second
line to be its inverse. Thus
$L_x^{\mathrm{TW}}/L_x^{\mathrm{ur}}$ is one-dimensional. The dual local
condition imposes one scalar equation: the detected diagonal projection must
vanish. This explains why the localization matrix has one row per prime.

The auxiliary and minimal rings can have the same tangent dimension without
being isomorphic before augmentation. The elementary algebra
$\mathcal O[\mathbf Z/\ell^N\mathbf Z]$ has a residual group direction and
the nonsmooth equation $(1+z)^{\ell^N}=1$; augmentation kills $z$. Its
finite-order equation survives at every level and disappears only in bounded
shadows as $N$ grows. This is the local algebraic model for the patch.

## 6. Auxiliary local conditions and diamond variables

### 6.1 Ordered regular branches

Fix $x\in Q_N$ and let $\alpha_x\ne\beta_x$ be the ordered residual
Frobenius roots. The local auxiliary functor remembers a rank-one direct
summand lifting the $\alpha_x$-line. Tame inertia acts on it through a
character $\chi_x$, while the determinant determines the character on the
complementary line:

$$
\rho|_{I_x}\sim
\begin{pmatrix}
\chi_x&0\\0&\delta|_{I_x}\chi_x^{-1}
\end{pmatrix}.
\tag{6.1}
$$

Let $\Delta_x$ be the quotient of order $\ell^N$ of the maximal
$\ell$-power quotient of the residue multiplicative group. Local reciprocity
makes $\chi_x$ its universal character. The ordered unframed local rings have
the form

$$
R_x^{\mathrm{ur},\delta,\alpha_x}\simeq\mathcal O[[X_x]],
\qquad
R_x^{\mathrm{TW},\delta,\alpha_x}
\simeq\mathcal O[\Delta_x][[X_x]].
\tag{6.2}
$$

The fixed determinant explains why only one group-ring direction occurs. The
ordered line removes the Weyl ambiguity. Distinct residual roots ensure that
an augmented unramified lift has a unique decomposition lifting its residual
eigenspaces.

### 6.2 Group algebras and their limit

Put

$$
\Delta_N=\prod_{x\in Q_N}\Delta_x
\simeq(\mathbf Z/\ell^N\mathbf Z)^q,
\qquad
\Lambda_N=\mathcal O[\Delta_N].
\tag{6.3}
$$

After choosing generators,

$$
\Lambda_N\simeq
\mathcal O[[z_1,\ldots,z_q]]/
\bigl((1+z_i)^{\ell^N}-1:1\leq i\leq q\bigr).
\tag{6.4}
$$

The limiting diamond source is

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad \dim S_\infty=q+1.
\tag{6.5}
$$

Why do the finite-order equations disappear in the patch? Fix an Artinian
precision $(\varpi^d,z_1^d,\ldots,z_q^d)$. In one variable,

$$
(1+z)^{\ell^N}-1
=\ell^Nz+\binom{\ell^N}{2}z^2+\cdots+z^{\ell^N}.
\tag{6.6}
$$

Terms of degree at least $d$ vanish at this precision. For fixed $j<d$,
the valuation of $\binom{\ell^N}{j}$ tends to infinity, as follows from

$$
\binom{\ell^N}{j}
=\frac{\ell^N}{j}\binom{\ell^N-1}{j-1}.
$$

Thus every remaining coefficient eventually vanishes modulo $\varpi^d$.
The assertion is topological: no finite group becomes $\mathbf Z_\ell$, but
every fixed finite-precision observation eventually stops seeing its exponent.

### 6.3 Exact deformation augmentation

Let $R_N$ represent the global auxiliary problem. The universal tame
characters give a map

$$
\Lambda_N\longrightarrow R_N.
\tag{6.7}
$$

Let $\mathfrak a_N$ be the augmentation ideal. Quotienting by it makes all
tame characters trivial, so the representation becomes unramified at
$Q_N$. Forgetting the ordered lines then gives a minimal deformation.

Conversely, an unramified minimal deformation has Frobenius characteristic
polynomial whose two factors remain coprime modulo the maximal ideal. Hensel's
lemma lifts the residual factorization uniquely, and the corresponding
idempotent recovers the chosen $\alpha_x$-line. These constructions commute
with all Artinian base changes and are inverse. Therefore

$$
R_N/\mathfrak a_NR_N\xrightarrow{\sim}R^{\min}.
\tag{6.8}
$$

This is equality of represented functors, not merely of tangent spaces. If
the residual roots were equal, the lifted eigenline would not be unique and
(6.8) could fail.

The inverse construction can be written with idempotents. Suppose the lifted
Frobenius polynomial factors as $P_x(X)=A(X)B(X)$ with $A$ and $B$ coprime
and $A$ lifting the factor $X-\alpha_x$. Choose $U,V$ with $UA+VB=1$.
Evaluating $VB$ at Frobenius gives the projector onto the $A$-factor. Its
uniqueness follows from coprimeness, and the formula commutes with quotienting
the coefficient algebra. If the ordering were forgotten, the two projectors
would be interchanged by the Weyl group; the quotient local problem would
have different augmentation behavior.

### 6.4 The old-form determinant

At $x$, the two degeneracy maps from hyperspecial to oriented level have an
adjoint Gram matrix

$$
G_x=
\begin{pmatrix}
q_x+1&T_x\\
S_x^{-1}T_x&q_x+1
\end{pmatrix}.
\tag{6.9}
$$

Its determinant is

$$
D_x=(q_x+1)^2-S_x^{-1}T_x^2.
\tag{6.10}
$$

Modulo the localized maximal ideal, use $q_x\equiv1\pmod\ell$ and
$\alpha_x\beta_x=q_xS_x$ to compute

$$
D_x\equiv
4-\frac{(\alpha_x+\beta_x)^2}{\alpha_x\beta_x}
=-\frac{(\alpha_x-\beta_x)^2}{\alpha_x\beta_x}\ne0.
\tag{6.11}
$$

Thus $D_x$ is a unit. This calculation simultaneously uses the geometric
Frobenius convention, the central operator, and distinct roots. Omitting
$S_x^{-1}$ would make it false except when the central character happens to
be trivial.

## 7. Auxiliary automorphic modules

### 7.1 Deep level and group-ring freeness

At each $x\in Q_N$, let $U_0(x)$ be the oriented level and let $U_1(x,N)$
be the deeper subgroup with quotient $\Delta_x$. Their products define the
deep auxiliary level. Right translation gives an action of $\Delta_N$.

A group action alone does not imply freeness over the group algebra. The
effective stabilizer hypotheses say that the fibers from deep to oriented
class groupoids are genuine $\Delta_N$-torsors and that coefficient
stabilizers do not grow. Functions on a torsor form a regular representation.
After localization and primary projection, finite projective summands remain
projective over the local ring $\Lambda_N$, and hence free. Thus, for one
positive integer $r$ independent of $N$,

$$
M_N\simeq\Lambda_N^{\oplus r},
\qquad
M_N^\dagger\simeq\Lambda_N^{\oplus r}.
\tag{7.1}
$$

The rank is positive because residual automorphy makes the minimal localized
module nonzero. A zero patched module would provide no information about the
deformation ring.

### 7.2 Integral oldness

Let

$$
d=(d_0,d_1):M^{\min}\oplus M^{\min}\longrightarrow M_0(x)
$$

be the degeneracy map to oriented level. Since $d^*d=G_x$ and $D_x$ is a
unit, the formula

$$
e_{\mathrm{old}}=d(d^*d)^{-1}d^*
\tag{7.2}
$$

defines an integral idempotent. Direct calculation gives
$e_{\mathrm{old}}^2=e_{\mathrm{old}}$, it is the identity on
$\operatorname{im}d$, and its kernel is $\ker d^*$. Hence

$$
M_0(x)=\operatorname{im}d\oplus\ker d^*.
\tag{7.3}
$$

The second summand is the integral new part. On every characteristic-zero new
constituent the level-raising relation forces $D_x=0$. But $D_x$ is a unit in
the localization. Since the module is $\mathcal O$-torsion-free, the new part
must vanish. Therefore the localized oriented module is entirely old.

Indeed, every characteristic-zero localization of the new summand is zero
because $D_x$ acts there both as zero and as a unit. The summand is therefore
$\varpi$-power torsion. But it is a direct summand of the saturated
$\mathcal O$-free module, so it is torsion-free and must vanish. Without
saturation, a quotient such as $\mathcal O/\varpi$ could survive while being
invisible after inverting $\varpi$.

Saturation is decisive here. Without it, the splitting might hold only after
inverting $\varpi$ and a torsion new quotient could remain. The proof kills
that possibility integrally.

### 7.3 Primary and companion branches

On the old image, the oriented operator has a polynomial whose reduction has
the distinct roots $\alpha_x$ and $\beta_x$. Hensel factorization gives two
integral idempotents. Selecting the $\alpha_x$-factor yields one copy of the
hyperspecial module. On the adjoint companion side, inverse-double-coset
adjunction selects the matching companion root, not necessarily the same
operator eigenvalue.

Removing the primes of $Q_N$ one at a time gives commuting projections because
they lie at distinct local factors. Consequently diamond coinvariants and
primary projection recover the exact minimal module:

$$
M_N/\mathfrak a_NM_N\xrightarrow{\sim}M^{\min}.
\tag{7.4}
$$

The torsor pairing gives a perfect group-ring-valued pairing

$$
\mathcal H_N:M_N\times M_N^\dagger\longrightarrow\Lambda_N,
\tag{7.5}
$$

linear in the first variable and semilinear in the second for
$[\gamma]\mapsto[\gamma^{-1}]$. Augmentation recovers (4.2). Because the
modules are free over $\Lambda_N$, invariants and coinvariants agree through
the norm map; this would be false for an arbitrary module in residue
characteristic dividing $|\Delta_N|$.

### 7.4 Exact module and Hecke augmentation

Let $\mathbb T_N$ be the faithful Hecke image on $M_N$. Branchwise Galois
attachment and integral local compatibility give a representation over
$\mathbb T_N$ satisfying the auxiliary local conditions, and hence a
surjection

$$
R_N\twoheadrightarrow\mathbb T_N.
\tag{7.6}
$$

Module coinvariants alone do not imply exact augmentation of the acting
order: an order can sit with finite index inside another order acting on a
rationally identical module. The retained saturation theorem rules this out
and gives

$$
\mathbb T_N/\mathfrak a_N\mathbb T_N
\xrightarrow{\sim}\mathbb T^{\min}.
\tag{7.7}
$$

Equations (6.8), (7.4), and (7.7) are three separate control theorems. Ring,
module, and faithful acting image must all be marked in the patch.

To distinguish the last two, consider orders $T'\subset T$ of finite index in
one semisimple fraction algebra, acting on commensurable lattices. Their
rational eigensystems and even their module coinvariants can agree, while
$T'/\mathfrak aT'$ maps to a proper suborder of $T/\mathfrak aT$. Saturated
type and degeneracy control rules out this index. Equation (7.7) is therefore
an order theorem, not a formal consequence of (7.4).

## 8. The finite system and its patch

### 8.1 The finite-level diagram

The auxiliary objects fit into

$$
\begin{array}{ccccc}
\Lambda_N&\longrightarrow&R_N&\twoheadrightarrow&\mathbb T_N\\
&&&&\downarrow\\
&&&&\operatorname{End}_{\Lambda_N}(M_N).
\end{array}
\tag{8.1}
$$

The upper-left map is the universal tame character. The lower action is the
geometric diamond action. Integral local--global compatibility identifies
them on every generic branch; generic reducedness and torsion-freeness then
identify them in the integral order. Equality only modulo the maximal ideal
would not suffice.

The map $R_N\to\mathbb T_N$ is surjective because good traces and the fixed
local data generate the faithful Hecke image. No faithfulness of the $R_N$
action has yet been proved.

### 8.2 Why the levels do not form a tower

The sets $Q_N$ are chosen independently and cannot be nested indefinitely.
There are therefore no arithmetic maps

$$
R_{N+1}\longrightarrow R_N
\quad\text{or}\quad
M_{N+1}\longrightarrow M_N
$$

in general. Patching cannot be an inverse limit of the original levels.

Instead one fixes an increasing sequence of Artinian precisions. At each
precision one records a finite diagram: the diamond algebra with ordered
generators, the deformation quotient, the free module with a marked basis,
the faithful action image, a finite set of named Hecke operators, the three
augmentation maps, primary projectors, companion basis, pairing matrix, and
adjoint involution. On the deformation side one records the entire quotient
ideal of a fixed source, not merely a guessed tuple of relations.

### 8.3 Finite shadows and diagonalization

At fixed precision the coefficient ring is finite. A free module of fixed
rank is a finite set, its endomorphism ring has only finitely many subrings and
tuples of named elements, and a finite quotient of a power-series ring has
only finitely many ideals. Thus only finitely many marked diagrams occur.

Choose a subsequence on which the precision-one diagram stabilizes, then a
subsequence of it on which precision two stabilizes, and so on. The diagonal
subsequence yields compatible shadows at every precision. Equivalently, the
stabilized diagrams form a finitely branching rooted tree with vertices at
every height; an infinite path supplies the compatible system.

The markings matter. Abstractly isomorphic free modules can have pairing
matrices differing by a nontrivial unit, and isomorphic rings can have
different structural diamond maps. Marked bases, ideals, maps, and pairings
ensure that exact augmentation and adjunction survive the passage to the
limit.

One convenient precision system is

$$
\mathfrak b_d=(\varpi^d,\mathfrak m_{S_\infty}^d),
\qquad
\mathfrak p_d=(\varpi^d,\mathfrak m_P^{\nu(d)}),
\tag{8.1a}
$$

where $\nu(d)$ grows fast enough that the action visible on the
$d$th module shadow factors through $P/\mathfrak p_d$. Such a choice exists
because every action image at fixed precision is a finite local ring and its
maximal ideal is nilpotent. Recording
$\ker(P\to R_N)+\mathfrak p_d$ retains the full deformation shadow, including
relations annihilating the module. Thus the construction does not silently
replace $R_N$ by $\mathbb T_N$ before faithfulness is proved.

The diagonal argument produces compatibility rather than canonicity. Different
infinite paths can give different coordinates $x_i$ or $z_i$. This is
harmless: after augmentation they all represent the same universal minimal
functor and the same faithful Hecke image. Canonicity of the finite map comes
from those universal properties, not from canonical patched coordinates.

### 8.4 The patched objects

Taking inverse limits of the coherent shadows gives a quotient

$$
R_\infty=P/I_\infty,
\tag{8.2}
$$

a module

$$
M_\infty\simeq S_\infty^{\oplus r},
\tag{8.3}
$$

and its perfectly paired companion. Here the source $P$ will be identified in
Chapter 9. Let

$$
A_\infty=\operatorname{im}\left(
P\longrightarrow R_\infty
\longrightarrow\operatorname{End}_{S_\infty}(M_\infty)
\right).
\tag{8.4}
$$

It is finite over $S_\infty$. Compatibility of the two diamond actions makes
the composite

$$
S_\infty\longrightarrow P\longrightarrow A_\infty
\hookrightarrow\operatorname{End}_{S_\infty}(M_\infty)
\tag{8.5}
$$

ordinary scalar multiplication. Since $M_\infty$ is nonzero and free over
$S_\infty$, the first composite is injective.

The asserted finiteness of $A_\infty$ is also elementary. After choosing an
$S_\infty$-basis of $M_\infty$, its endomorphism algebra is a finite matrix
algebra over $S_\infty$. The image $A_\infty$ is an $S_\infty$-submodule
because scalar diamonds lie in its center. A submodule of a finite module over
the Noetherian ring $S_\infty$ is finite. No finiteness of $R_\infty$ has been
assumed at this stage.

The scalar injection is just as concrete. If $s\in S_\infty$ maps to zero,
then it annihilates every vector of $S_\infty^{\oplus r}$. Applying it to a
basis vector gives $s=0$. Thus the positivity of $r$, inherited from residual
automorphy, has a direct algebraic role.

The marked exact sequences satisfy the Mittag--Leffler condition because all
shadow transition maps are surjective. Inverse limits therefore give

$$
\begin{aligned}
R_\infty/\mathfrak a_\infty R_\infty&\simeq R^{\min},\\
M_\infty/\mathfrak a_\infty M_\infty&\simeq M^{\min},\\
A_\infty/\mathfrak a_\infty A_\infty&\simeq\mathbb T^{\min},
\end{aligned}
\tag{8.6}
$$

where $\mathfrak a_\infty=(z_1,\ldots,z_q)$ and its image is understood
through the structural map. The first equality is not inferred from an
unproved flat tensor product; it is the inverse limit of the marked exact
ring augmentation sequences.

For example, at every retained precision there is an exact sequence

$$
0\longrightarrow K_{N,d}\longrightarrow R_{N,d}
\longrightarrow R^{\min}_d\longrightarrow0.
\tag{8.7}
$$

The transition maps on the finite kernels are eventually surjective because
the entire quotient diagrams were marked. Hence $\varprojlim^1K_{N,d}=0$,
and taking inverse limits preserves exactness. The limiting kernel is the
closed ideal generated by the images of $z_1,\ldots,z_q$; Noetherian
completeness guarantees closedness. This proves the ring line of (8.6).
Parallel marked sequences prove the module and order lines. Only after
Chapter 9 proves freeness may one recover the same statements by ordinary
Tor-independent tensor product.

Patching only the action images would construct $A_\infty$ but not the full
deformation ring: a kernel annihilating every module would disappear by
definition. The separately marked quotient ideals retain precisely that
possible kernel, allowing (9.4) to prove it zero. Likewise, without order
augmentation shadows one would recover the minimal module but not necessarily
its exact faithful Hecke order.

## 9. Equal-variable rigidity

### 9.1 The sharp absolute source

By (5.5), the cotangent space of every unframed auxiliary ring $R_N$ has
dimension $q$. Choose lifts of a cotangent basis. Topological Nakayama gives a
surjection

$$
P=\mathcal O[[x_1,\ldots,x_q]]\twoheadrightarrow R_N.
\tag{9.1}
$$

For completeness, let $B$ be the closed $\mathcal O$-subalgebra generated by
the chosen lifts. Surjectivity on cotangent spaces says

$$
\mathfrak m_{R_N}=\mathfrak m_BR_N+\mathfrak m_{R_N}^2.
$$

Ordinary Nakayama applied modulo every power of $\mathfrak m_{R_N}$ shows that
$B$ maps onto each Artinian quotient. Completeness then gives $B=R_N$ and
proves (9.1).

No claim is made that the kernel of (9.1) has a uniform generating tuple or
that $R_N$ is flat, reduced, or smooth. The full kernel ideal is retained at
each finite precision. After diagonalization these ideals define $I_\infty$
in (8.2). Both source rings now have the same dimension:

$$
\dim P=q+1=\dim S_\infty.
\tag{9.2}
$$

### 9.2 The dimension argument

We isolate the algebraic heart of the proof.

**Lemma 9.1 (equal-variable rigidity).** Let $S$ and $P$ be regular local
domains of the same dimension. Let $M$ be a nonzero finite free $S$-module.
Suppose a quotient $A$ of $P$ is a finite $S$-subalgebra of
$\operatorname{End}_S(M)$ and that the structural map $S\to A$ acts on $M$
by scalars. Then $P\to A$ is an isomorphism.

**Proof.** If an element of $S$ maps to zero in $A$, it kills the nonzero free
$S$-module $M$, so it is zero. Thus $S\hookrightarrow A$. Since $A$ is finite
over $S$, the extension is integral and

$$
\dim A=\dim S=\dim P.
$$

Write $A=P/J$. If $J\ne0$, choose $0\ne f\in J$. Because $P$ is a domain,
$f$ is a nonzerodivisor, and the principal ideal theorem gives

$$
\dim A\leq\dim P/(f)=\dim P-1,
$$

a contradiction. Hence $J=0$. $\square$

Apply the lemma with $S=S_\infty$, $M=M_\infty$, and $A=A_\infty$.
Equations (8.3)--(8.5) verify its hypotheses, and (9.2) verifies the equal
dimension. Therefore

$$
P\xrightarrow{\sim}A_\infty.
\tag{9.3}
$$

Since $P\to A_\infty$ factors through $R_\infty=P/I_\infty$, the ideal
$I_\infty$ lies in the zero kernel. Consequently

$$
R_\infty=P=A_\infty.
\tag{9.4}
$$

The patched deformation ring is thus regular of dimension $q+1$.

### 9.3 Freeness and faithfulness

The ring $P=A_\infty$ is finite over $S_\infty$. It is Cohen--Macaulay of
dimension $q+1$, so

$$
\operatorname{depth}_{S_\infty}P=q+1.
$$

The Auslander--Buchsbaum formula over the regular local ring $S_\infty$ gives
projective dimension zero. Thus $P$ is finite projective, hence finite free,
over $S_\infty$.

Likewise $M_\infty$ is free over $S_\infty$, so it has depth $q+1$ over
$P$ as well. Since $P$ is regular, Auslander--Buchsbaum again gives

$$
M_\infty\simeq P^{\oplus m}
\tag{9.5}
$$

for some $m>0$. A nonzero free module is faithful, hence

$$
\operatorname{Ann}_{R_\infty}(M_\infty)=0.
\tag{9.6}
$$

This proves scheme-theoretic full support. It detects nilpotent thickenings,
not merely irreducible components.

Here is the depth change in detail. Since $P$ is finite over $S_\infty$, the
extended maximal ideal $\mathfrak m_{S_\infty}P$ is primary for the maximal
ideal of $P$. Regular sequences from that ideal compute the same depth over
either ring. The free $S_\infty$ structure therefore gives
$\operatorname{depth}_PM_\infty=q+1$. Since a regular local ring of dimension
$q+1$ has finite global dimension, Auslander--Buchsbaum applies:

$$
\operatorname{pd}_P(M_\infty)+\operatorname{depth}_P(M_\infty)
=\operatorname{depth}P=q+1.
\tag{9.7}
$$

Thus the projective dimension is zero, and a finite projective module over a
local ring is free. No generic multiplicity-one hypothesis is needed. The
rank $m$ can differ from the diamond rank $r$ because $P$ is itself finite
free of some rank over $S_\infty$.

If $q=0$, then $S_\infty=P=\mathcal O$. The scalar action already gives
$P=A_\infty$, and the same argument applies. Thus no positive-dimensional
auxiliary system is hidden in the theorem.

### 9.4 Why weaker support arguments fail

If one replaced $P$ by $S_\infty[[u]]$ and let $u$ act as zero, the action
image would still contain $S_\infty$ faithfully, but the extra source
dimension would allow a nonzero kernel. This is why the sharp absolute count
$q$, rather than a padded presentation, is essential.

Topological support alone also misses nilpotents. The ring

$$
B=S_\infty[\epsilon]/(\epsilon^2)
$$

can act on $S_\infty$ with $\epsilon$ acting by zero. The module meets the
only irreducible component, yet the action is not faithful. The proof avoids
this trap by taking the regular domain $P$ as source. In a domain every
nonzero kernel lowers dimension.

Finally, a perfect pairing does not force faithfulness: an element can
annihilate both paired modules. The pairing is used for integral control and
congruences; regularity and depth prove faithfulness.

## 10. Descent and the minimal equality

### 10.1 Regular augmentation

Because $R_\infty=P$ is finite free over $S_\infty$, the sequence

$$
z_1,\ldots,z_q
\tag{10.1}
$$

is regular on $R_\infty$ and on $M_\infty$. Here $z_i$ means its image under
the structural map $S_\infty\to R_\infty$; it need not equal the coordinate
$x_i$. Therefore augmentation has no higher Tor terms.

Quotienting (9.4) by the image of $\mathfrak a_\infty$ and using (8.6) gives
a commutative square

$$
\begin{array}{ccc}
R_\infty&\xrightarrow{\sim}&A_\infty\\
\downarrow&&\downarrow\\
R^{\min}&\twoheadrightarrow&\mathbb T^{\min}.
\end{array}
\tag{10.2}
$$

The bottom map is the canonical map (4.4), because all structural Galois,
Hecke, and augmentation maps were retained in the finite shadows.

### 10.2 Proof of the minimal comparison

Quotienting an isomorphism by corresponding ideals yields an isomorphism.
Thus (10.2) proves

$$
\boxed{R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.}
\tag{10.3}
$$

Moreover, augmenting (9.5) gives

$$
M^{\min}\simeq(R^{\min})^{\oplus m}.
\tag{10.4}
$$

Since $R_\infty$ is finite free over $S_\infty$ and the augmentation sequence
has length $q$, $R^{\min}$ is finite free over $\mathcal O$. It is a quotient
of the regular local ring $R_\infty$ by the regular sequence (10.1), hence a
relative complete intersection. Every local complete intersection is
Cohen--Macaulay and Gorenstein. The perfect primary--companion pairing descends
because its finite-level matrices and adjoints were marked and because the
augmentation is Tor-independent.

The finite-freeness assertion can be read directly from a basis. Since
$R_\infty$ is finite free over $S_\infty$, reducing an $S_\infty$-basis
modulo $(z_1,\ldots,z_q)$ gives an $\mathcal O$-basis of $R^{\min}$. The
sequence is regular because free modules are flat and
$z_1,\ldots,z_q$ is regular on $S_\infty$. The quotient has codimension $q$
inside a regular ring and is defined by exactly $q$ regular equations, which
is the relative complete-intersection assertion.

Gorensteinness follows concretely from the Koszul resolution. For one
nonzerodivisor $z$, applying $\operatorname{Hom}(-,R_\infty)$ to

$$
0\longrightarrow R_\infty\xrightarrow{z}R_\infty
\longrightarrow R_\infty/(z)\longrightarrow0
$$

identifies the relative dualizing module of the quotient with the quotient.
Iterating over the regular sequence preserves rank-one duality. This proof
also produces the determinant generator used in the congruence calculation.

This proves the ring-theoretic portion of Theorem 1.1. Notice that no
cotangent determinant was used to kill the kernel.

### 10.3 Complete intersections and congruences

After equality, a generically isolated integral branch
$\lambda:R^{\min}\to\mathcal O$ has cotangent module

$$
\Phi_R=I/I^2,
\qquad I=\ker\lambda.
\tag{10.5}
$$

Choose a complete-intersection presentation near the branch,

$$
R^{\min}\simeq
\mathcal O[[X_1,\ldots,X_q]]/(f_1,\ldots,f_q),
$$

with $f_i$ vanishing at the branch. The conormal sequence presents
$\Phi_R$ by the Jacobian matrix

$$
D=\left(\frac{\partial f_i}{\partial X_j}\right)_\lambda.
$$

Hence

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)=(\det D).
\tag{10.6}
$$

The Koszul resolution on the regular sequence identifies the relative
dualizing generator. Its restriction to the branch is multiplied by
$\det D$. The image of the branch annihilator is therefore the same ideal,
which is the intrinsic Hecke congruence ideal $\eta_{\mathbb T}$. Thus

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)=\eta_{\mathbb T}.
\tag{10.7}
$$

When the quotients have finite length, (10.7) becomes equality of their
$\mathcal O$-lengths. If the automorphic branch has multiplicity $m$, the
module congruence length is $m$ times the ring congruence length, provided the
branch lattice is saturated and the pairing primitive. Without those
hypotheses a lattice-index or discriminant term appears.

Equation (10.7) is a consequence and an audit of (10.3), not its proof. Before
equality, the deformation and automorphic determinant lines are separately
defined but no canonical comparison unit has been constructed.

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
conditions commute with this extension, and so does the global universal
property:

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
$H^1$ vanishing needed for regular-semisimple detection. Then the localization
matrix in Section 5.3 may not be made invertible, and the sets $Q_N$ used in
this proof have not been constructed. Later commutative algebra cannot repair
missing auxiliary primes.

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
range, the local ring can be singular or reducible and the contribution
(2.9) can change. The equality of source dimensions in Chapter 9 then has to
be recomputed; the present theorem does not cover that problem.

If auxiliary Frobenius is scalar, no ordered eigenline is uniquely recoverable,
the old determinant (6.11) vanishes, and exact augmentation fails. If a
degeneracy image or type lattice is not saturated, generic oldness can leave
integral torsion and the augmented order may have finite index in the desired
minimal order.

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
polynomial (2.3), total oddness, and the fixed determinant. Canonical lattice
and finite-flat quotient theory supplies the integral representation at
$v\mid\ell$. These results are used only for branches in their stated
parallel-weight-two, noncharacter, integral-realization range.

Integral type theory supplies primary and companion lattices, saturation, and
closed represented tame or special components away from $\ell$. Primitive
wild types and uncontrolled small residue-characteristic cases are excluded.

Residual image classification supplies adequacy from absolute irreducibility
of the cyclotomic restriction only for $\ell\geq7$, together with the precise
prime-five exception. The separate adjoint-twist invariant (3.7) is retained
rather than incorrectly folded into adequacy.

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
cancellation makes the primal and dual Selmer dimensions equal. Adequacy turns
the common dimension $q$ into $q$ ordered auxiliary primes, and fixed
determinant gives one diamond character at each of them.

On the automorphic side, definite-quaternionic torsors make the deep-level
module free over the diamond group ring. The unit old-form determinant,
saturation, ordered roots, and companion adjunction ensure that augmentation
returns the exact minimal lattice and exact faithful Hecke order. Coherent
finite shadows replace a nonexistent tower of auxiliary levels.

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
the given lift. Coefficient extension and faithful-flat descent preserve the
statement. The resulting package is exactly minimal modularity lifting over a
totally real field in the clean coefficient-prime range $\ell\geq7$: residual
automorphy propagates to every integral minimal lift, with determinant, local
types, finite-flat quotients, and coefficient descent all retained.
