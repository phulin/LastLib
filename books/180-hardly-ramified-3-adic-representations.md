# Hardly Ramified $3$-adic Representations

## Contents

1. [The classification problem](#1-the-classification-problem)
   - [Why the prime $3$ is both favorable and dangerous](#11-why-the-prime-3-is-both-favorable-and-dangerous)
   - [The exact prime-$2$ hardly ramified datum](#12-the-exact-prime-2-hardly-ramified-datum)
   - [The strict specialization and general auxiliary primes](#13-the-strict-specialization-and-general-auxiliary-primes)
   - [The three conclusions that must not be conflated](#14-the-three-conclusions-that-must-not-be-conflated)
   - [The proof architecture](#15-the-proof-architecture)
2. [Lattices, finite quotients, and their fields](#2-lattices-finite-quotients-and-their-fields)
   - [The chosen integral tower](#21-the-chosen-integral-tower)
   - [Full level fields and exact Galois groups](#22-full-level-fields-and-exact-galois-groups)
   - [Successive congruence kernels](#23-successive-congruence-kernels)
   - [Determinant, scalar, and projective fields](#24-determinant-scalar-and-projective-fields)
   - [Oddness at the real place](#25-oddness-at-the-real-place)
3. [Finite flatness at $3$](#3-finite-flatness-at-3)
   - [What levelwise existence does and does not give](#31-what-levelwise-existence-does-and-does-not-give)
   - [The split reference models](#32-the-split-reference-models)
   - [Saturated subquotients and residual ramification](#33-saturated-subquotients-and-residual-ramification)
   - [The upper-break and different bounds](#34-the-upper-break-and-different-bounds)
   - [Higher levels and coefficient ramification](#35-higher-levels-and-coefficient-ramification)
4. [Ramification away from $3$ and the global discriminant](#4-ramification-away-from-3-and-the-global-discriminant)
   - [The effective residual ramification set](#41-the-effective-residual-ramification-set)
   - [Tame inertia, monodromy, and conductor](#42-tame-inertia-monodromy-and-conductor)
   - [Assembling the root-discriminant bound](#43-assembling-the-root-discriminant-bound)
   - [The strict rational bound](#44-the-strict-rational-bound)
   - [Why the full-level bound grows](#45-why-the-full-level-bound-grows)
5. [Odlyzko cutoffs and legitimate stabilization](#5-odlyzko-cutoffs-and-legitimate-stabilization)
   - [The unconditional numerical ledger](#51-the-unconditional-numerical-ledger)
   - [The conditional ledger under GRH](#52-the-conditional-ledger-under-grh)
   - [The fixed-base exponent-$3$ category](#53-the-fixed-base-exponent-3-category)
   - [The stabilization theorem](#54-the-stabilization-theorem)
   - [What stabilization says about an image](#55-what-stabilization-says-about-an-image)
6. [Finite subgroups of $\operatorname{GL}_2$ in characteristic $3$](#6-finite-subgroups-of-operatornamegl_2-in-characteristic-3)
   - [Representation image versus projective image](#61-representation-image-versus-projective-image)
   - [The general order ledger](#62-the-general-order-ledger)
   - [Reducible and Cartan cases](#63-reducible-and-cartan-cases)
   - [Cartan normalizers and dihedral images](#64-cartan-normalizers-and-dihedral-images)
   - [Exceptional and defining-characteristic images](#65-exceptional-and-defining-characteristic-images)
   - [The special coincidences over $\mathbf F_3$](#66-the-special-coincidences-over-mathbf-f_3)
7. [The small abelian field ledger over $\mathbf Q$](#7-the-small-abelian-field-ledger-over-mathbf-q)
   - [Abelian extensions supported at $3$](#71-abelian-extensions-supported-at-3)
   - [Why a cyclic cubic field is a genuine trap](#72-why-a-cyclic-cubic-field-is-a-genuine-trap)
   - [Quadratic and quartic possibilities](#73-quadratic-and-quartic-possibilities)
   - [The Eisenstein quadratic field](#74-the-eisenstein-quadratic-field)
   - [The first cubic ray layer over $\mathbf Q(\zeta_3)$](#75-the-first-cubic-ray-layer-over-mathbf-qzeta_3)
8. [Reducible residual representations](#8-reducible-residual-representations)
   - [The two diagonal characters](#81-the-two-diagonal-characters)
   - [The affine extension field](#82-the-affine-extension-field)
   - [The ray-class obstruction](#83-the-ray-class-obstruction)
   - [Orientation-independent splitting](#84-orientation-independent-splitting)
   - [The exact residual conclusion](#85-the-exact-residual-conclusion)
9. [Cartan and dihedral branches](#9-cartan-and-dihedral-branches)
   - [Split Cartan](#91-split-cartan)
   - [Nonsplit Cartan](#92-nonsplit-cartan)
   - [Even dihedral projective image](#93-even-dihedral-projective-image)
   - [Odd dihedral projective image](#94-odd-dihedral-projective-image)
   - [The induced-character interpretation](#95-the-induced-character-interpretation)
10. [Exceptional and full residual images](#10-exceptional-and-full-residual-images)
    - [Projective $A_4$](#101-projective-a_4)
    - [Projective $S_4$](#102-projective-s_4)
    - [Projective $A_5$ and subfield groups](#103-projective-a_5-and-subfield-groups)
    - [The full $\operatorname{GL}_2(\mathbf F_3)$ diagnostic](#104-the-full-operatornamegl_2mathbf-f_3-diagnostic)
    - [The residual exclusion theorem](#105-the-residual-exclusion-theorem)
11. [The complete residual candidate ledger](#11-the-complete-residual-candidate-ledger)
    - [Candidates over $\mathbf F_3$](#111-candidates-over-mathbf-f_3)
    - [Candidates over $\mathbf F_{3^f}$](#112-candidates-over-mathbf-f_3f)
    - [Fields, degrees, and decisive obstructions](#113-fields-degrees-and-decisive-obstructions)
    - [What remains after semisimplification](#114-what-remains-after-semisimplification)
12. [Congruence layers and the pro-$3$ image](#12-congruence-layers-and-the-pro-3-image)
    - [The conjugation module](#121-the-conjugation-module)
    - [Fixed determinant and trace-zero layers](#122-fixed-determinant-and-trace-zero-layers)
    - [The cyclotomic direction cannot stabilize](#123-the-cyclotomic-direction-cannot-stabilize)
    - [The common-ambient difference module](#124-the-common-ambient-difference-module)
    - [The Lie-algebra conclusion](#125-the-lie-algebra-conclusion)
13. [Lifting residual lines](#13-lifting-residual-lines)
    - [Why a residual line is not enough](#131-why-a-residual-line-is-not-enough)
    - [The obstruction at one infinitesimal step](#132-the-obstruction-at-one-infinitesimal-step)
    - [The global affine-cocycle rigidity lemma](#133-the-global-affine-cocycle-rigidity-lemma)
    - [Why every obstruction is a finite-flat difference](#134-why-every-obstruction-is-a-finite-flat-difference)
    - [Inductive lifting and conjugacy](#135-inductive-lifting-and-conjugacy)
    - [Dependence on the stable lattice](#136-dependence-on-the-stable-lattice)
14. [Characteristic-zero alternatives](#14-characteristic-zero-alternatives)
    - [Reducible representations](#141-reducible-representations)
    - [Potentially reducible representations](#142-potentially-reducible-representations)
    - [Finite image](#143-finite-image)
    - [Semisimplification $1\oplus\chi_3$](#144-semisimplification-1opluschi_3)
    - [Purity as the final incompatibility](#145-purity-as-the-final-incompatibility)
15. [Solvable layers and small-degree fields](#15-solvable-layers-and-small-degree-fields)
    - [Abelian quotients](#151-abelian-quotients)
    - [Cubic layers](#152-cubic-layers)
    - [Quartic layers](#153-quartic-layers)
    - [Unramified layers](#154-unramified-layers)
    - [A solvable-tower elimination protocol](#155-a-solvable-tower-elimination-protocol)
16. [Four hostile diagnostics](#16-four-hostile-diagnostics)
    - [Full image over $\mathbf F_3$](#161-full-image-over-mathbf-f_3)
    - [A Borel image](#162-a-borel-image)
    - [A dihedral projective image](#163-a-dihedral-projective-image)
    - [Coefficient residue degree two](#164-coefficient-residue-degree-two)
17. [Boundaries and failure modes](#17-boundaries-and-failure-modes)
    - [An additional ramified prime](#171-an-additional-ramified-prime)
    - [Absence of levelwise finite-flat models](#172-absence-of-levelwise-finite-flat-models)
    - [A weakened wild different estimate](#173-a-weakened-wild-different-estimate)
    - [Failure of strict comparison](#174-failure-of-strict-comparison)
    - [A residual line that does not lift](#175-a-residual-line-that-does-not-lift)
    - [Coefficient and lattice failures](#176-coefficient-and-lattice-failures)
    - [A full-tower misuse](#177-a-full-tower-misuse)
18. [Final theorem package and the Frey interface](#18-final-theorem-package-and-the-frey-interface)
    - [The exact local condition at $2$](#181-the-exact-local-condition-at-2)
    - [Torsion fields and the unconditional degree-$20$ cutoff](#182-torsion-fields-and-the-unconditional-degree-20-cutoff)
    - [Abelian fields and simple factors](#183-abelian-fields-and-simple-factors)
    - [Multiplicative--constant devissage](#184-multiplicative--constant-devissage)
    - [The residual extension and its Kummer class](#185-the-residual-extension-and-its-kummer-class)
    - [Integral line lifting and the $3$-adic character](#186-integral-line-lifting-and-the-3-adic-character)
    - [Coefficient extension and changing the prime](#187-coefficient-extension-and-changing-the-prime)
    - [The unconditional Frey interface](#188-the-unconditional-frey-interface)
    - [Strict specialization and the remaining general boundary](#189-strict-specialization-and-the-remaining-general-boundary)
    - [What has been proved](#1810-what-has-been-proved)

## 1. The classification problem

### 1.1 Why the prime $3$ is both favorable and dangerous

Changing the coefficient prime to $3$ puts a weight-two representation in an unusually narrow arithmetic corridor. A finite-flat module killed by $3$ over $\mathbf Z_3$ has no upper ramification above $1/2$, and its normalized different is strictly smaller than $3/2$. Thus the field cut out by a residual quotient satisfies

$$
\operatorname{rd}(L)<3^{3/2}=5.1961524227\ldots.
$$

This is far below the unconditional asymptotic discriminant threshold. It is small enough to force a sharp degree bound and, when combined with the upper ramification cutoff, to make finite group theory effective.

The same prime is dangerous for three reasons. First, the familiar large-characteristic image criteria do not apply. The group

$$
\operatorname{GL}_2(\mathbf F_3)
$$

has order only $48$, and its projective quotient is the exceptional group $S_4$. Second, reduction identifies the inverse cyclotomic character with the cyclotomic character:

$$
\bar\chi_3^{-1}=\bar\chi_3.
$$

The two orientations of a residual extension therefore have the same abstract coefficient character even though their integral finite-flat behavior is different. Third, the cyclotomic $3$-power tower itself never stabilizes. Any argument that treats all successive congruence kernels as though they were fixed-base exponent-$3$ fields would incorrectly eliminate the representation $1\oplus\chi_3$ that the classification is supposed to isolate.

The purpose of this book is to navigate that corridor without using any of those shortcuts. We first state the exact input, then classify the residual image, then decide whether its invariant lines lift. Analytic discriminant bounds restrict field size; finite group theory restricts group shape; class field theory controls one-dimensional quotients; and saturated finite-flat difference modules turn lifting obstructions into forbidden cubic fields.

### 1.2 The exact prime-$2$ hardly ramified datum

Let $E/\mathbf Q_3$ be a finite extension, let $\mathcal O$ be its valuation ring, let $\varpi$ be a uniformizer, and let

$$
k=\mathcal O/\varpi\mathcal O\simeq\mathbf F_{3^f}.
$$

An **exact prime-$2$ hardly ramified $3$-adic datum over $\mathbf Q$** consists of

$$
(E,\mathcal O,\varpi,k,V,T,\rho,\{\mathcal G_n\}_{n\geq1})
$$

with the following properties.

1. $V$ is a two-dimensional $E$-vector space and
   $$
   \rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_E(V)
   $$
   is continuous.
2. $T\subset V$ is a free rank-two $\mathcal O$-lattice stable under $G_{\mathbf Q}$.
3. The characteristic-zero representation is semisimple. When this hypothesis is omitted, every conclusion will explicitly retain a semisimplification or an extension class.
4. The determinant is exactly
   $$
   \det\rho=\chi_3,
   $$
   after any finite-order twist from the prime-switching construction has been explicitly removed. If such a factor has not been removed, its conductor, cutout field, and values must be added to the controlled datum; none of the classification conclusions below then applies without that new calculation.
5. The representation is odd: for complex conjugation $c$,
   $$
   \det\rho(c)=-1.
   $$
6. For every $n\geq1$, the quotient $T/\varpi^nT$ is identified, as an abstract finite $G_{\mathbf Q_3}$-module, with the generic points of a finite locally free commutative group scheme
   $$
   \mathcal G_n/\mathbf Z_3.
   $$
   No compatibility or uniqueness of these witnesses is included in this clause.
7. The action is unramified at every finite prime outside $\{2,3\}$.
8. Over $G_{\mathbf Q_2}$ there is an exact sequence of free rank-one
   $\mathcal O$-modules
   $$
   0\longrightarrow T_2^+
   \longrightarrow T
   \longrightarrow T_2^-\longrightarrow0, \tag{1.1}
   $$
   and the character $\eta_2$ on $T_2^-$ is unramified and satisfies
   $$
   \eta_2^2=1. \tag{1.2}
   $$

Clause 8 is the exact local condition, not a slogan about small conductor. The two copies of
$\mathcal O$ in (1.1) describe their module ranks; they are not both being declared trivial
representations. Since the determinant is $\chi_3$ and $\eta_2^{-1}=\eta_2$, the character on
the submodule is

$$
\chi_3\eta_2. \tag{1.3}
$$

Both diagonal characters are unramified at $2$. The extension between them is allowed to be
ramified. In particular, (1.1)--(1.2) neither assert that inertia is trivial nor assert that the
sequence splits.

Clause 6 is deliberately only an existence assertion. It is genuine integral input and is supplied, for example, by a good-reduction torsion tower or by one integral low-weight object; rational crystallinity alone does not supply it for an arbitrary stable lattice. The argument below neither chooses transition maps between the $\mathcal G_n$ nor identifies an independently chosen $\mathcal G_n$ with a coefficient quotient of $\mathcal G_{n+1}$. When a coefficient action is needed, it is installed on a replacement witness by a product-and-saturated-closure construction. When two congruent lifts must be compared, their generic fiber product is closed inside the product of two witnesses. These constructions prove existence of the exact models used in the argument; they assert no uniqueness of integral models.

The residual module attached to the datum is

$$
M=T/\varpi T,
$$

with action

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k).
$$

Its full isomorphism class belongs to the named lattice. Its semisimplification is independent
of the stable lattice. Both will be used, and they will never be identified without proof.

The local sequence is integral for a reason. Since its quotient is free, it is split as a
sequence of underlying $\mathcal O$-modules. Tensoring with a finite coefficient extension or
reducing modulo any coefficient ideal therefore preserves exactness. The quotient character
remains unramified and continues to square to one. This elementary observation is what lets the
same local condition pass to every torsion quotient used below.

### 1.3 The strict specialization and general auxiliary primes

The original **strict datum** consists of clauses 1--2 and 4--6, with clause 3 optional, and
unramifiedness at every finite prime away from $3$. It does not need a chosen filtration at
$2$: once inertia there is trivial, the strict argument developed in Chapters 7--13 proves
actual splitting by its own residual and affine-cocycle calculation. An exact prime-$2$ datum
which is also unramified at $2$ is a strict datum, but the strict theorem is not narrowed by
requiring clause 8.

The exact prime-$2$ datum is not merely the controlled-set schema with $S_0=\{2\}$. It carries
the additional filtration (1.1)--(1.2) at every coefficient level. That extra structure makes
the inertia image at $2$ a cyclic $3$-group, makes wild inertia trivial, determines the exact
tame different, and puts every finite quotient in one finite-flat category over
$\mathbf Z[1/2]$. Chapter 18 uses those facts to close the prime-$2$ case completely.

For comparison, some prime-switching constructions leave a genuinely general finite effective
residual ramification set

$$
S_0=\{p_1,\ldots,p_s\},
\qquad 3\notin S_0.
$$

For each $p\in S_0$, fix either an upper-break cutoff $R_p\geq0$ or an exact tame inertia order $e_p$. A **controlled hardly ramified datum** satisfies clauses 1--6 above and replaces clause 7 by the following record:

- $M$ is unramified outside $S_0\cup\{3\}$;
- if $R_p$ is recorded, the local field cut out by $M$ has last upper break at most $R_p$;
- if $e_p$ is recorded, its ramification is tame of exact inertia order $e_p$;
- the characteristic-zero ramification set and the residual ramification set are listed separately.

At a conductor-one special prime, rational monodromy can be nonzero while its reduction vanishes. The prime belongs to $S_0$ only when the actual residual inertia is nontrivial. Conversely, a small Artin conductor is not used as a substitute for a break bound unless the represented module is faithful on the local field being measured.

For an arbitrary nonempty $S_0$, this is only a numerical and local record. It does not include
the prime-$2$ filtration unless that filtration is stated separately. The strict theorem uses
$S_0=\varnothing$, and the theorem needed by the Frey route uses the exact prime-$2$ datum.
Other auxiliary sets remain subject to the finite-search boundary of Section 18.9.

### 1.4 The three conclusions that must not be conflated

There are three different reducibility questions.

The first concerns the residual semisimplification:

$$
\bar\rho^{\mathrm{ss}}
\simeq\bar\alpha\oplus\bar\beta.
$$

This statement is independent of the stable lattice. It says nothing about whether a chosen reduction is split or which character occurs as a submodule.

The second concerns the chosen residual module $M$. In the exact prime-$2$ category the correct
conclusion is an exact sequence

$$
0\longrightarrow k(1)\longrightarrow M
\longrightarrow k\longrightarrow0.
$$

Its extension class and orientation depend a priori on $T$. The allowed nonsplit class is not an
error: it is a scalar multiple of the Kummer class of $2$. At the prime $3$ the two coefficient
characters are inverses and hence equal, but the finite-flat connected--étale order still forces
the displayed orientation. In the strict specialization the Kummer line disappears and the
sequence splits.

The third concerns $V$ in characteristic zero. In the exact prime-$2$ category a saturated
cyclotomic line lifts integrally and the quotient is trivial, but the extension need not split.
The Kummer class of $2$ supplies genuine nonsplit examples. What is independent of that class is
the character identity

$$
\operatorname{tr}\rho(g)=1+\chi_3(g) \tag{1.4}
$$

for every $g$. Thus

$$
\rho^{\mathrm{ss}}\simeq1\oplus\chi_3. \tag{1.5}
$$

When $\rho$ is semisimple, as a member of the compatible system is, (1.5) is an actual split
decomposition. Without semisimplicity the extension class must be retained.

The final theorem therefore has three controlled prime-$2$ stages:

$$
0\longrightarrow k(1)\longrightarrow M\longrightarrow k\longrightarrow0,
\qquad [M]=a[2],
$$

from residual field theory and the finite-flat orientation,

$$
0\longrightarrow\mathcal O(1)\longrightarrow T
\longrightarrow\mathcal O\longrightarrow0,
$$

after finite-level devissage and saturation, and

$$
\rho^{\mathrm{ss}}\simeq1\oplus\chi_3
$$

from the character identity. The strict case strengthens both extension statements to split
ones. Confusing the strict strengthening with the exact prime-$2$ theorem would discard the
admissible Kummer example.

### 1.5 The proof architecture

The dependencies can be displayed without hiding any implication.

```text
finite flat at 3 + the exact quotient at 2
                    |
          +---------+---------+
          |                   |
          v                   v
  3-cost < 3/2       tame 2-cost = 0 or 2/3
          |                   |
          +---------+---------+
                    |
                    v
 rd < 3^(3/2) 2^(2/3), unconditional degree <= 20
                    |
          +---------+---------+
          |                   |
          v                   v
  abelian-field lemma   degree-capped group theory
          |                   |
          +---------+---------+
                    |
                    v
 simple factors are multiplicative or constant
                    |
                    v
      sorted finite-level filtration
                    |
          +---------+---------+
          |                   |
          v                   v
 residual class a[2]    trace = 1 + determinant
          |                   |
          +---------+---------+
                    |
                    v
 integral cyclotomic line and purity contradiction
```

The new degree-$20$ bound is unconditional and is calculated directly from the explicit formula
of Book 179. It is not an imported field table. The residual Kummer field of $2$ survives that
bound and is retained rather than eliminated. The decisive higher-level step is instead a
finite-flat devissage over $\mathbf Z[1/2]$: simple factors are classified, adjacent factors
are reordered, and the resulting canonical cross relation gives (1.4) at every coefficient
level. The strict affine-cocycle proof remains valid as the specialization in which the
Kummer direction is absent.

## 2. Lattices, finite quotients, and their fields

### 2.1 The chosen integral tower

Fix a strict datum, an exact prime-$2$ datum, or a general controlled datum. For $n\geq1$, put

$$
T_n=T/\varpi^nT,
\qquad
\rho_n:G_{\mathbf Q}\longrightarrow
\operatorname{Aut}_{\mathcal O/\varpi^n}(T_n).
$$

After choosing an $\mathcal O$-basis of $T$, the target is

$$
\operatorname{GL}_2(\mathcal O/\varpi^n).
$$

Changing the basis conjugates the image and changes none of the fields below. The model $\mathcal G_n$ is not reconstructed from this matrix group. It is additional integral data whose generic points have been identified with $T_n$.

If the source of the datum supplies transition morphisms, their generic fibers fit into commutative squares

$$
\begin{array}{ccc}
\mathcal G_{n+1}(\overline{\mathbf Q}_3)&\longrightarrow&
\mathcal G_n(\overline{\mathbf Q}_3)\\
\downarrow&&\downarrow\\
T_{n+1}&\longrightarrow&T_n.
\end{array}
$$

They are useful provenance, but they are not part of the strict hypothesis and are not used in the proof. Levelwise existence gives the discriminant bound for each individual $T_n$. It does not, by closure alone, identify a quotient of one selected model with another independently selected model. Chapter 3 constructs coefficient-linear witnesses one level at a time, and §12.4 compares two lifts inside a new common ambient model. Consequently no inverse limit of the chosen $\mathcal G_n$ is formed and no integral transition is inferred from its generic fiber.

### 2.2 Full level fields and exact Galois groups

Define

$$
K_n=\mathbf Q(T_n)
=(\overline{\mathbf Q})^{\ker\rho_n}
$$

and

$$
G_n=\operatorname{Gal}(K_n/\mathbf Q).
$$

Restriction identifies the Galois group exactly with the representation image:

$$
\boxed{G_n\simeq\operatorname{im}\rho_n.}
$$

The adjective “exactly” matters. The field generated by one torsion vector can be smaller because that vector can have a nontrivial stabilizer. The field $K_n$ trivializes every vector and is cut out by the kernel of the whole action.

Reduction gives a nested tower

$$
K_1\subseteq K_2\subseteq\cdots.
$$

At the first level,

$$
[K_1:\mathbf Q]=|\operatorname{im}\bar\rho|.
$$

If $k=\mathbf F_{3^f}$, the elementary matrix bound is

$$
[K_1:\mathbf Q]
\leq(3^{2f}-1)(3^{2f}-3^f).
$$

For $f=1$ this is $48$; for $f=2$ it is $5760$. These numbers belong to different coefficient fields and cannot be interchanged.

### 2.3 Successive congruence kernels

Let

$$
C_n=\ker(G_{n+1}\longrightarrow G_n).
$$

Because every element of $G_n$ is represented by the reduction of the same Galois element at level $n+1$, the reduction map is onto. Thus there is an exact sequence

$$
1\longrightarrow C_n\longrightarrow G_{n+1}
\longrightarrow G_n\longrightarrow1.
$$

Every element of $C_n$ has a unique form modulo $\varpi^{n+1}$

$$
1+\varpi^nA,
\qquad A\in M_2(k).
$$

Since $2n\geq n+1$ for $n\geq1$,

$$
(1+\varpi^nA)(1+\varpi^nB)
\equiv1+\varpi^n(A+B)pmod{\varpi^{n+1}}.
$$

Thus

$$
\boxed{C_n\hookrightarrow(M_2(k),+)}
$$

and $C_n$ is elementary abelian of order

$$
|C_n|=3^{r_n},
\qquad0\leq r_n\leq4f.
$$

Consequently

$$
[K_{n+1}:K_n]=3^{r_n}.
$$

The subgroup $C_n$ is always an $\mathbf F_3$-vector space. It need not be a $k$-vector subspace of $M_2(k)$: the coefficient action commutes with Galois, but it does not multiply Galois elements by arbitrary scalars. Writing $r_n=fd_n$ therefore requires an additional $k$-linearity argument and will not be assumed.

Conjugation by $G_{n+1}$ descends to the residual conjugation action:

$$
g:A\longmapsto\bar\rho(g)A\bar\rho(g)^{-1}.
$$

It is this $G_{\mathbf Q}$-module structure, not merely the abstract elementary abelian group, that controls whether a congruence layer descends to a fixed-base exponent-$3$ object.

When $\mathcal O=\mathbf Z_3$, this becomes the requested $3$-power filtration explicitly:

$$
C_n
=\operatorname{im}(\rho_{n+1})
\cap\bigl(1+3^nM_2(\mathbf Z/3^{n+1}\mathbf Z)\bigr),
$$

and reduction of $1+3^nA$ identifies it with an $\mathbf F_3$-subspace of $M_2(\mathbf F_3)$. For a general coefficient DVR the same formula uses $\varpi^n$ and the underlying $\mathbf F_3$-space of $M_2(k)$.

### 2.4 Determinant, scalar, and projective fields

Three subfields must be distinguished.

The determinant field $D_n$ is cut out by $\det\rho_n$. If $\mathcal O=\mathbf Z_3$, then

$$
D_n=\mathbf Q(\zeta_{3^n}),
\qquad
[D_n:\mathbf Q]=2\cdot3^{n-1}.
$$

For a ramified coefficient ring of absolute ramification index $e_{\mathcal O}=v_\varpi(3)$, reduction modulo $\varpi^n$ sees the cyclotomic character modulo

$$
3^{m(n)},
\qquad
m(n)=\left\lceil\frac n{e_{\mathcal O}}\right\rceil,
$$

so

$$
D_n=\mathbf Q(\zeta_{3^{m(n)}}).
$$

At level one, $D_1=\mathbf Q(\zeta_3)=\mathbf Q(\sqrt{-3})$ whenever the residual determinant is $\bar\chi_3$.

Let $H_n=\operatorname{im}\rho_n$ and let $Z_n$ be the scalar subgroup of the ambient matrix group. The projective field is

$$
P_n=K_n^{H_n\cap Z_n}.
$$

It has Galois group

$$
\operatorname{Gal}(P_n/\mathbf Q)
\simeq H_n/(H_n\cap Z_n),
$$

the projective image. The scalar field is not another name for $D_n$: a scalar matrix has determinant equal to the square of its scalar, and a nonscalar matrix can have any permitted determinant. At level one over $\mathbf F_3$, the scalar center is

$$
\{I,-I\},
$$

and both scalars have determinant $1$. Hence the determinant character factors through the projective quotient, but it does not determine that quotient.

Every degree ledger must therefore record

$$
|H_n|,
\qquad |H_n\cap Z_n|,
\qquad |\mathbf P H_n|,
\qquad |\det H_n|.
$$

Dropping the scalar factor can divide the true torsion-field degree by two; dropping the determinant field can erase the unavoidable cyclotomic subfield.

### 2.5 Oddness at the real place

Let $c$ be complex conjugation. Since $c^2=1$ and the coefficient characteristic is odd, $\bar\rho(c)$ is semisimple with eigenvalues in $\{1,-1\}$. Oddness gives

$$
\det\bar\rho(c)=-1,
$$

so the two eigenvalues are distinct and

$$
\operatorname{tr}\bar\rho(c)=0.
$$

In a suitable residual basis,

$$
\bar\rho(c)=
\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

Thus complex conjugation is neither scalar nor trivial in the projective image. The determinant field is imaginary quadratic, and the full residual field has no real embedding. Accordingly all unconditional analytic comparisons for $K_1$ use the arbitrary-signature bound, not the totally real refinement.

Oddness also orients the final characters. If the residual constituents are $1$ and $\bar\chi_3$, then $c$ acts trivially on the first and by $-1$ on the second. It does not by itself determine which constituent is a submodule of a chosen nonsplit reduction.

## 3. Finite flatness at $3$

### 3.1 What levelwise existence does and does not give

Put $A_n=\mathcal O/\varpi^n$. Clause 6 initially supplies only a finite-flat model of the underlying additive group of $T_n$. The following elementary construction supplies a coefficient-linear witness without claiming that the original witness already carries the action.

Throughout this construction the base remains $\operatorname{Spec}\mathbf Z_3$. An $A_n$-action means a ring of group-scheme endomorphisms; it is not a morphism $\operatorname{Spec}A_n\to\operatorname{Spec}\mathbf Z_3$, and a coefficient quotient is not a change of the geometric base.

Let $V$ be a finite $A_n[G_{\mathbf Q_3}]$-module whose underlying group has a finite-flat model $\mathcal G$. Form

$$
\mathcal P=\prod_{a\in A_n}\mathcal G
$$

and on generic points embed

$$
j:V\longrightarrow\mathcal P(\overline{\mathbf Q}_3),
\qquad
j(v)=(av)_{a\in A_n}.
$$

The coordinate indexed by $1$ makes $j$ injective. Let $\mathcal H$ be the schematic closure of $j(V)$ in $\mathcal P$. On coordinate rings its defining Hopf ideal is contracted from the generic fiber. The resulting quotient is torsion free over $\mathbf Z_3$, hence free, so $\mathcal H$ is finite flat and has exactly $V$ as generic points.

For $b\in A_n$, the product endomorphism

$$
(x_a)_a\longmapsto(x_{ab})_a
$$

carries $j(v)$ to $j(bv)$ and therefore preserves its closure. On $\mathcal H$ these endomorphisms satisfy the addition, multiplication, zero, and unit laws: the laws hold on the generic fiber, and two maps out of a flat finite scheme that agree generically agree everywhere. Thus $\mathcal H$ is an $A_n$-linear finite-flat witness. This proves existence of a coefficient action. It proves neither that scalars extend to $\mathcal G$ nor that the action on an arbitrary witness is unique.

Coefficient quotients are equally concrete. If $A_n\twoheadrightarrow B=A_n/I$, close the generic subgroup $IV\subset V$ in $\mathcal H$ and call it $\mathcal I$. The quotient fppf sheaf $\mathcal H/\mathcal I$ is represented and finite flat: on coordinate Hopf algebras its functions are the equalizer of the coaction and the trivial coaction, and faithful-flat descent along $\mathcal H\to\mathcal H/\mathcal I$ makes that algebra finite locally free of rank $|V/IV|$. Its generic points are $V/IV$. Every $i\in I$ acts trivially there and hence trivially integrally, so the action factors through $B$. It is therefore a $B$-linear witness for the coefficient quotient. In particular, a level-$(n+1)$ witness produces some level-$n$ witness. Nothing in this construction identifies that quotient with an independently chosen $\mathcal G_n$.

The same saturation argument is the exactness statement used below. If $W\subset V$ is a stable generic submodule, its closure in one fixed ambient $\mathcal H$ is the unique saturated subgroup of that ambient model with generic fiber $W$, and the represented quotient models $V/W$. This is uniqueness inside a named ambient model, not uniqueness among all models of $W$ or $V$.

Nothing in the construction used that $A_n$ is a principal quotient; it works verbatim for any finite commutative coefficient ring. In particular it will be applied to the fiber-product ring $A'\times_AA'$ and to its dual-number quotient in §12.4.

Compatible towers supplied by geometry remain useful, but the strict proof needs only these levelwise existential constructions. It forms no inverse limit of finite-flat group schemes. A rational local representation, even one with weights $\{0,1\}$, does not by itself provide the required witnesses for the quotients of a chosen lattice.

### 3.2 The split reference models

The comparison representation is

$$
\rho_0=1\oplus\chi_3.
$$

Its finite-level models can be constructed without classifying all finite-flat groups. Write the finite additive group of $A_n$ in invariant factors,

$$
A_n^+\simeq\bigoplus_j\mathbf Z/3^{r_j}\mathbf Z.
$$

The product of the constant groups $\underline{\mathbf Z/3^{r_j}\mathbf Z}$ realizes the trivial $A_n^+$-valued character. The product of $\mu_{3^{r_j}}$ realizes its cyclotomic twist $A_n(1)$. Apply the product-and-closure construction of §3.1 to each underlying model to install the full $A_n$-action. Their product models $A_n\oplus A_n(1)$, and its generic determinant is the cyclotomic character. Only this explicit split reference model is needed in the lifting argument.

The determinant of the given representation is also an equality on generic fibers. We do not use it to assert that an arbitrary witness carries a particular filtration, pairing, or connected--étale decomposition. Those would be integral statements requiring additional comparison theorems. Here the determinant is used in matrices, where it forces every first-order difference from $\rho_0$ to have trace zero.

### 3.3 Saturated subquotients and residual ramification

At level one the coefficient ring $k$ has characteristic $3$. An action of $k$ on a finite-flat witness makes multiplication by $3$ the zero endomorphism, so the underlying group scheme is killed by $3$. The same is true for every saturated subobject and represented quotient constructed inside it.

Consequently the residual field and the fields of all residual subquotients satisfy the upper-break cutoff of §3.4. This conclusion uses existence, coefficient enhancement by closure, and exactness inside a chosen ambient model. It does not use uniqueness of the model or a classification into ordinary and supersingular shapes.

This distinction is particularly useful for extensions. Once the two residual characters are known globally, a nonsplit extension cuts out an elementary abelian cubic layer over $\mathbf Q(\zeta_3)$. Rather than decide its orientation by classifying endpoint models, Chapter 8 applies the upper-break cutoff directly to that layer. At higher levels, §12.4 applies the same idea to the finite-flat dual-number module constructed from two congruent lifts.

### 3.4 The upper-break and different bounds

Let $L_3/\mathbf Q_3$ be the local extension cut out by $M$. Since $M$ is killed by $3$, the finite-flat upper-break theorem of Book 178 gives

$$
G_{\mathbf Q_3}^u\text{ acts trivially on }M
\qquad(u>1/2).
$$

Thus the last upper break is at most $1/2$. If

$$
e=e(L_3/\mathbf Q_3),
\qquad d=d(L_3/\mathbf Q_3),
$$

then Hilbert's different formula gives

$$
\boxed{d\leq\frac{3e}{2}-1}
$$

and hence

$$
\boxed{\frac de\leq\frac32-\frac1e<\frac32.}
$$

The strict inequality is the source of the strict global root-discriminant bound. The upper ramification group is allowed to be nontrivial at $u=1/2$; the strictness comes from the $-1/e$ in the normalized different, not from deleting the endpoint.

To see the numerical conversion, write the different in upper numbering. For a finite Galois extension with inertia group of order $e$,

$$
\frac de
=\int_{-1}^{\infty}
\left(1-\frac1{|G^u|}\right)du.
$$

On $-1<u\leq0$ the integrand is $1-1/e$, giving the tame cost $1-1/e$. If $G^u=1$ for $u>1/2$, the remaining interval has length at most $1/2$ and the integrand is strictly less than one whenever the group is finite. Hence

$$
\frac de
\leq1-\frac1e+\frac12
=\frac32-\frac1e.
$$

Multiplication by $e$ gives $d\leq3e/2-1$. The right side need not be an integer; the inequality means that the integral $d$ is at most its floor. This derivation also shows why the rank and the size of the matrix group do not appear: only the last upper break and the actual ramification index enter.

Two constants must not be interchanged:

$$
\text{last upper break}\leq\frac12,
\qquad
\text{normalized different}<\frac32.
$$

The first constrains quotient fields and conductors. The second enters the global root discriminant.

For the faithful two-dimensional residual module, the same cutoff gives the coarse Artin conductor bound

$$
a_3(M)
=\int_{-1}^{\infty}
\operatorname{codim}_k M^{G^u},du
\leq2\left(1+\frac12\right)=3.
$$

This conductor is useful for comparing local representation types, but it does not replace the different. The integrand for the different measures the whole faithful Galois group, while the Artin integrand measures fixed spaces in this particular rank-two module. Faithfulness of $M$ on $L_3$ makes the conductor informative, but the root-discriminant exponent remains $d/e$.

### 3.5 Higher levels and coefficient ramification

If $T_n$ is killed by $3^m$, the general finite-flat theorem gives

$$
G_{\mathbf Q_3}^u\text{ acts trivially for }
u>m-\frac12,
$$

and

$$
\frac{d(\mathbf Q_3(T_n)/\mathbf Q_3)}
{e(\mathbf Q_3(T_n)/\mathbf Q_3)}
<m+\frac12.
$$

For $\mathcal O=\mathbf Z_3$ and $T_n=T/3^nT$, one has $m=n$. For a coefficient uniformizer $\varpi$ with $v_\varpi(3)=e_{\mathcal O}$, the quotient $T/\varpi^nT$ is killed by

$$
3^{\lceil n/e_{\mathcal O}\rceil},
$$

and the safe bound uses that exponent. Coefficient ramification can make several consecutive $\varpi$-levels visible at the same $3$-power level; it never justifies pretending that $\varpi=3$.

The bound grows with $m$. This is unavoidable. For the cyclotomic line,

$$
\operatorname{rd}(\mathbf Q(\zeta_{3^m}))
=3^{m-1/2}.
$$

Finite-flat models at all levels therefore do not give one uniform root-discriminant bound for the full torsion tower.

## 4. Ramification away from $3$ and the global discriminant

### 4.1 The effective residual ramification set

Let $p\ne3$. The residual field $K_1$ is ramified at $p$ exactly when

$$
\bar\rho(I_p)\ne1.
$$

This is a statement about the chosen lattice reduction. A common characteristic-zero conductor can remain nonzero after the residual action becomes trivial. Conversely, weak compatibility alone only says that the residual action is unramified outside the common bad set; it does not calculate which bad primes disappear.

The **effective residual set** is

$$
S_0=\{p\ne3:\bar\rho(I_p)\ne1\}.
$$

For every $p\in S_0$ we retain one of three kinds of information:

1. the complete finite inertia filtration;
2. an exact tame inertia order $e_p$;
3. a last upper break $R_p$.

An Artin conductor exponent can replace these only when it belongs to a faithful representation cutting out the same local field. A rank-one conductor inside a nonfaithful two-dimensional representation need not see every ramification group of a larger field.

### 4.2 Tame inertia, monodromy, and conductor

If the residual inertia at $p$ is tame of order $e_p$, its exact normalized different contribution is

$$
\frac{d_p}{e_p}=1-\frac1{e_p}.
$$

For a nonzero tame unipotent action on a two-dimensional characteristic-$3$ module, the inertia image has order $3$, so

$$
\frac{d_p}{e_p}=\frac23.
$$

This action has conductor exponent one. The equality of that conductor with the characteristic-zero special conductor requires the integral monodromy parameter to remain nonzero modulo $\varpi$.

If the parameter becomes zero, the residual contribution is not $2/3$; it is $0$, and $p$ must be removed from $S_0$. If the parameter survives, its exact tame order is preferable to the coarse bound $d_p/e_p<1$.

When wild inertia occurs, a conductor-one slogan is unavailable. A cutoff $R_p$ gives

$$
\frac{d_p}{e_p}\leq1-\frac1{e_p}+R_p<1+R_p.
$$

The factor $1+R_p$ is safe but coarse. It is the number entered in the global ledger when no sharper filtration is known.

### 4.3 Assembling the root-discriminant bound

Let $L=K_1=\mathbf Q(M)$. The local-to-global discriminant formula is

$$
\operatorname{rd}(L)
=\prod_p p^{d_p/e_p},
$$

because the base field is $\mathbf Q$. At $3$ the finite-flat estimate gives an exponent strictly less than $3/2$. At an auxiliary prime use the recorded local cost.

Indeed, if $L/\mathbf Q$ is Galois of degree $n$ and a prime $p$ has local ramification index $e_p$, residue degree $f_p$, number of primes $g_p$, and local different exponent $d_p$, then

$$
n=e_pf_pg_p,
$$

while the exponent of $p$ in the global discriminant is

$$
f_pg_pd_p=n\frac{d_p}{e_p}.
$$

Taking the $n$th root produces the factor $p^{d_p/e_p}$. This is why a normalized local different, rather than an Artin conductor of a possibly nonfaithful constituent, is the correct global entry.

Substituting the local bounds gives

$$
\boxed{
\operatorname{rd}(L)
<3^{3/2}
\prod_{p\in S_{\mathrm{br}}}p^{1+R_p}
\prod_{p\in S_{\mathrm{tame}}}p^{1-1/e_p}.
}
$$

Here $S_{\mathrm{br}}$ and $S_{\mathrm{tame}}$ partition the effective set according to which information is being used. A prime must not appear in both products.

Over a number field $F$, the corresponding formula is

$$
\operatorname{rd}(F(M))
<\operatorname{rd}(F)3^{3/2}
\prod_{v\in S_{\mathrm{br}}}
(Nv)^{(1+R_v)/[F:\mathbf Q]}
\prod_{v\in S_{\mathrm{tame}}}
(Nv)^{(1-1/e_v)/[F:\mathbf Q]}.
$$

The factor $\operatorname{rd}(F)$ and the denominator $[F:\mathbf Q]$ are part of the formula. They cannot be suppressed by saying that the argument is relative.

### 4.4 The strict rational bound

For the strict datum, $S_0=\varnothing$, so

$$
\boxed{
\operatorname{rd}(K_1)<3^{3/2}.
}
$$

In addition, the local upper groups at $3$ satisfy

$$
\operatorname{Gal}((K_1)_w/\mathbf Q_3)^u=1
\qquad(u>1/2).
$$

Both statements are retained. The first gives a global degree cap. The second eliminates a cyclic cubic field of conductor $9$ whose root discriminant is still below $3^{3/2}$. Bounded root discriminant alone is therefore not the whole small-field input.

Every subfield $E\subseteq K_1$ satisfies

$$
\operatorname{rd}(E)<3^{3/2},
$$

and every Galois quotient of the local group inherits the cutoff $u>1/2$. This combination will be applied repeatedly to determinant, projective, cubic, and abelian subfields.

The root-discriminant inheritance follows from the discriminant tower formula. For $K_1/E/\mathbf Q$,

$$
D_{K_1/\mathbf Q}
=D_{E/\mathbf Q}^{[K_1:E]}
N_{E/\mathbf Q}(D_{K_1/E}),
$$

so

$$
\operatorname{rd}(K_1)
=\operatorname{rd}(E)
N_{E/\mathbf Q}(D_{K_1/E})^{1/[K_1:\mathbf Q]}
\geq\operatorname{rd}(E).
$$

The upper-filtration inheritance is a quotient theorem: the upper ramification group of a quotient is the image of the original upper ramification group. Neither fact requires the subfield itself to be Galois over $\mathbf Q$, although the quotient fields used later are usually Galois.

### 4.5 Why the full-level bound grows

For $\mathcal O=\mathbf Z_3$, the same calculation at level $n$ gives only

$$
\operatorname{rd}(K_n)<3^{n+1/2}
$$

in the strict case. Moreover $K_n$ contains

$$
D_n=\mathbf Q(\zeta_{3^n}),
$$

whose degree is $2\cdot3^{n-1}$ and whose root discriminant is $3^{n-1/2}$. Thus both degree and ramification depth genuinely grow.

The last formula follows from the cyclotomic discriminant identity

$$
\left|D_{\mathbf Q(\zeta_{3^n})}\right|
=3^{(2n-1)3^{n-1}}.
$$

Since the degree is $2\cdot3^{n-1}$, division of the discriminant exponent by the degree gives

$$
\frac{(2n-1)3^{n-1}}{2\cdot3^{n-1}}
=n-\frac12.
$$

Thus the growth is an exact lower bound coming from a required subfield, not an artifact of the general finite-flat estimate.

At $n=4$ the determinant field alone has degree

$$
2\cdot3^3=54,
$$

larger than the residual degree cap $52$. This is not a contradiction, because the residual bound $3^{3/2}$ does not apply to level $3^4$. Any proof that applies the level-one ceiling to every $K_n$ has silently erased the cyclotomic tower.

## 5. Odlyzko cutoffs and legitimate stabilization

### 5.1 The unconditional numerical ledger

The unconditional lower-bound package proved in Book 179 has two levels. Its arbitrary-signature asymptotic constant is

$$
C_{\mathrm{un}}(0)=4\pi e^\gamma
=22.3816160954\ldots.
$$

Thus any family of fields with one uniform upper bound

$$
U<4\pi e^\gamma
$$

has bounded degree. The inequality is strict. Equality with the asymptotic constant gives no degree bound by this comparison.

For the strict residual field over $\mathbf Q$, a direct Minkowski calculation is stronger and completely explicit. At degree $53$ the arbitrary-signature lower bound is

$$
\frac\pi4
\left(\frac{53^{53}}{53!}\right)^{2/53}
=5.2006733020\ldots
>3^{3/2}.
$$

Monotonicity in the degree therefore gives

$$
\boxed{
\operatorname{rd}(L)<3^{3/2}
\Longrightarrow[L:\mathbf Q]\leq52.
}
$$

This is the only numerical finite-degree cutoff used in the strict residual classification. It is unconditional and applies to every signature. We do not use the totally real cap $12$, because oddness forces the determinant field $\mathbf Q(\sqrt{-3})$ inside $L$.

For a controlled set $S_0$, put

$$
U(S_0)=3^{3/2}
\prod_{p\in S_{\mathrm{br}}}p^{1+R_p}
\prod_{p\in S_{\mathrm{tame}}}p^{1-1/e_p}.
$$

If $U(S_0)<4\pi e^\gamma$, the unconditional explicit-formula algorithm supplies a finite degree threshold $N(U(S_0),0)$. Unless that calculation has actually been carried out, no particular numerical value of $N$ will be quoted. For example,

$$
3^{3/2}\sqrt2=7.348\ldots<22.3816\ldots
$$

does imply an effective degree bound for one tame quadratic factor at $2$; it does not by itself say that the cap is $52$.

### 5.2 The conditional ledger under GRH

Under the generalized Riemann hypothesis for the Dedekind zeta functions of all fields being tested, the arbitrary-signature asymptotic constant becomes

$$
C_{\mathrm{GRH}}(0)=8\pi e^\gamma
=44.7632321909\ldots.
$$

More generally, for a real-embedding proportion at least $\alpha_0$, the conditional constant is

$$
8\pi e^{\gamma+\alpha_0\pi/2}.
$$

These constants may sharpen a controlled-set argument whose upper ceiling lies between the unconditional and conditional thresholds. They are never used in the strict theorem, the exact prime-$2$ theorem, or the final Frey interface. A conditional asymptotic constant also does not furnish an unstated finite-degree cap. One must choose an admissible test function, evaluate its integrals in the required signature range, and verify the numerical inequality.

The division of labor in this book is therefore exact:

$$
\begin{array}{c|c|c}
\text{claim}&\text{analytic input}&\text{status}\\
\hline
[K_1:\mathbf Q]\leq52
&\text{degree-$53$ Minkowski value}&\text{unconditional}\\
\text{bounded degree for }U<4\pi e^\gamma
&\text{unconditional threshold theorem}&\text{unconditional}\\
\text{bounded degree for }U<8\pi e^\gamma
&\text{conditional threshold theorem}&\text{GRH-dependent}.
\end{array}
$$

No row may be substituted for another.

### 5.3 The fixed-base exponent-$3$ category

Fontaine's stabilization argument applies naturally to a class of modules killed by $3$ over one fixed base. Let $F$ be a number field and let $\mathscr C$ be a collection of finite $G_F$-modules such that:

1. every object is killed by $3$;
2. every object has a finite-flat model at every place above $3$;
3. every object has the same permitted auxiliary ramification set and cutoffs;
4. finite direct sums remain in $\mathscr C$.

For $M\in\mathscr C$, let $F(M)$ be its cutout field, and let

$$
\Omega_{\mathscr C}=\prod_{M\in\mathscr C}F(M)
$$

be their directed compositum. A finite subcompositum is the field cut out by a finite direct sum. The product of the chosen finite-flat models remains killed by $3$, so every finite subcompositum has the same root-discriminant ceiling

$$
U_{\mathscr C}
=\operatorname{rd}(F)3^{3/2}
\prod_{v\in S_{\mathrm{br}}}
(Nv)^{(1+R_v)/[F:\mathbf Q]}
\prod_{v\in S_{\mathrm{tame}}}
(Nv)^{(1-1/e_v)/[F:\mathbf Q]}.
$$

The closure under direct sums is the reason the local costs take a maximum rather than being multiplied once for every object. Without it, a generic compositum inequality would destroy the uniform bound.

### 5.4 The stabilization theorem

**Theorem 5.1 (unconditional fixed-base stabilization).** Assume that every finite subcompositum of $\Omega_{\mathscr C}$ has real-embedding proportion at least $\alpha_0$ and that

$$
U_{\mathscr C}<4\pi e^{\gamma+\alpha_0}.
$$

Then $\Omega_{\mathscr C}/F$ is finite. Consequently every nested chain of fields contained in $\Omega_{\mathscr C}$ stabilizes.

**Proof strategy.** The finite-flat discriminant theorem gives the same strict upper bound for every finite subcompositum. The unconditional analytic threshold bounds all their absolute degrees by one integer. Choose a subcompositum $E$ of maximal degree. For every other finite subcompositum $E'$, the compositum $EE'$ is again in the family and cannot have larger degree. Hence $EE'=E$, so $E'\subseteq E$. Thus $\Omega_{\mathscr C}=E$. A nested chain inside a finite extension eventually has constant degree and therefore becomes constant. $\square$

For the strict rational category, one may take

$$
U_{\mathscr C}=3^{3/2}<4\pi e^\gamma.
$$

This proves finiteness of the compositum of all fixed-base exponent-$3$ objects satisfying the strict local conditions. It does not put the fields $K_n=\mathbf Q(T/3^nT)$ inside that compositum. Such an inclusion is an additional descent assertion about their successive congruence data.

### 5.5 What stabilization says about an image

There is a direct tower form of the analytic argument that does not mention a module category.

**Proposition 5.2 (uniform-tower stabilization).** Let

$$
F=E_0\subseteq E_1\subseteq E_2\subseteq\cdots
$$

be a nested tower of number fields. Suppose that for one $0\leq\alpha_0\leq1$ and one real number $U$,

$$
\frac{r_1(E_n)}{[E_n:\mathbf Q]}\geq\alpha_0,
\qquad
\operatorname{rd}(E_n)\leq U
$$

for every $n$, and that

$$
U<4\pi e^{\gamma+\alpha_0}.
$$

Then the tower stabilizes.

**Proof.** The unconditional threshold principle supplies an integer $N(U,\alpha_0)$ such that $[E_n:\mathbf Q]<N(U,\alpha_0)$ for all $n$. The degrees form a nondecreasing sequence of positive integers, so they are eventually constant. An inclusion of number fields of equal finite degree is equality. $\square$

If $E_n=F(T/3^nT)$ and the finite quotients separate the image, stabilization makes the image on $T$ finite. Indeed, once $E_{n+1}=E_n$ at every later level, an element acting trivially modulo $3^n$ acts trivially modulo all $3^m$ and hence on the separated inverse limit.

This proposition proves exactly the often-used implication from a genuinely uniform discriminant bound to a stable torsion field. It does not manufacture that uniform bound. For $1\oplus\chi_3$, the fields $\mathbf Q(\zeta_{3^n})$ have root discriminant $3^{n-1/2}$, so its hypothesis fails.

Let $T$ be a faithful lattice representation and suppose, as an additional hypothesis, that every $K_n$ lies in one fixed finite extension of $\Omega_{\mathscr C}$. Then the tower $K_n$ stabilizes. If it stabilizes at $K_N$, every element in the image acting trivially on $T_N$ acts trivially on every later quotient and hence on $T$ itself. Therefore the full image is finite.

Conversely, if the finite quotients separate the image, a finite image makes the tower stabilize. Thus

$$
\boxed{
K_n\text{ stabilizes}
\Longleftrightarrow
\rho(G_F)\text{ is finite}
}
$$

under the stated faithfulness and containment hypotheses.

For a subgroup of $\operatorname{GL}_2(\mathcal O)$, one can see the last step through the congruence filtration. At sufficiently deep level, the $3$-adic logarithm identifies

$$
1+\varpi^mM_2(\mathcal O)
$$

with the torsion-free additive lattice $\varpi^mM_2(\mathcal O)$. A finite intersection with this deep congruence group is therefore trivial. If $E$ contains a third root of unity, the first congruence group can contain torsion; passing to a depth greater than $v_\varpi(3)/2$ removes it. The phrase “the principal congruence subgroup is torsion-free” is safe only after this depth has been checked.

For our cyclotomic determinant, the full image cannot be finite because $\chi_3(G_{\mathbf Q})$ is infinite. Hence the full torsion tower cannot satisfy the fixed-compositum containment. What can stabilize is the trace-zero or noncyclotomic error tower after its congruence layers have been shown to descend to $\mathscr C$. Chapter 12 will make that distinction precise.

## 6. Finite subgroups of $\operatorname{GL}_2$ in characteristic $3$

### 6.1 Representation image versus projective image

Put

$$
q=3^f,
\qquad
H=\bar\rho(G_{\mathbf Q})\subseteq\operatorname{GL}_2(\mathbf F_q),
$$

and let

$$
Z=\{aI:a\in\mathbf F_q^\times\}.
$$

The projective image is

$$
\mathbf P H=H/(H\cap Z).
$$

Its order is the degree of the projective field, not the full torsion field. The full degree is $|H|$, and the ratio is $|H\cap Z|$. The determinant cuts out another quotient. In our setting

$$
\det H=\{1,-1\}\subseteq\mathbf F_3^\times\subseteq\mathbf F_q^\times.
$$

Thus for $f>1$ the full group $\operatorname{GL}_2(\mathbf F_q)$ is already incompatible with the determinant: its determinant image is all of $\mathbf F_q^\times$. The largest determinant-compatible ambient group is

$$
\operatorname{GL}_2(\mathbf F_q)^{\chi}
=\{g:\det g\in\mathbf F_3^\times\},
$$

of order

$$
2q(q^2-1).
$$

When $q=3$, this is all of $\operatorname{GL}_2(\mathbf F_3)$ and has order $48$.

The scalar kernel inside the determinant-compatible ambient group is

$$
Z^\chi
=\{aI:a^2\in\mathbf F_3^\times\}.
$$

Since $a^2=1$ has the two roots $\pm1$, while $a^2=-1$ has two roots exactly when $f$ is even,

$$
|Z^\chi|=
\begin{cases}
2,&f\text{ odd},\\
4,&f\text{ even}.
\end{cases}
$$

For an actual image put $s=|H\cap Z|$. Then

$$
|H|=s|\mathbf P H|,
\qquad
s\mid |Z^\chi|.
$$

The determinant descends to a character of $\mathbf P H$ if and only if it is trivial on $H\cap Z$. This is automatic when $f$ is odd, because the only available scalars are $\pm I$ and both have determinant one. It need not be automatic when $f$ is even: a scalar satisfying $a^2=-1$ already has nontrivial determinant. Thus a projective degree never silently includes the determinant field, and division by the scalar kernel is always made using the actual intersection $H\cap Z$.

An image can be irreducible over $\mathbf F_q$ without being absolutely irreducible. A nonsplit Cartan is the standard example: its natural representation is irreducible over $\mathbf F_q$ but diagonalizes over $\mathbf F_{q^2}$. Projective largeness and absolute irreducibility must therefore be audited separately.

### 6.2 The general order ledger

The ambient groups have the following orders:

$$
\begin{array}{c|c}
\text{group}&\text{order}\\
\hline
\operatorname{GL}_2(\mathbf F_q)&q(q-1)^2(q+1)\\
\operatorname{SL}_2(\mathbf F_q)&q(q^2-1)\\
Z&q-1\\
\operatorname{PGL}_2(\mathbf F_q)&q(q^2-1)\\
\operatorname{PSL}_2(\mathbf F_q)&q(q^2-1)/2\\
B&q(q-1)^2\\
C_{\mathrm s}&(q-1)^2\\
N(C_{\mathrm s})&2(q-1)^2\\
C_{\mathrm{ns}}&q^2-1\\
N(C_{\mathrm{ns}})&2(q^2-1).
\end{array}
$$

Here $B$ is a Borel subgroup, $C_{\mathrm s}$ is a split Cartan, and $C_{\mathrm{ns}}\simeq\mathbf F_{q^2}^\times$ is a nonsplit Cartan. Their projective Cartan orders are respectively $q-1$ and $q+1$, and their projective normalizers are dihedral of orders $2(q-1)$ and $2(q+1)$.

Every entry can be recovered by a short count. The first column of an invertible matrix is any nonzero vector, giving $q^2-1$ choices; the second is any vector outside its span, giving $q^2-q$ choices. Hence

$$
|\operatorname{GL}_2(\mathbf F_q)|
=(q^2-1)(q^2-q)=q(q-1)^2(q+1).
$$

The determinant is onto $\mathbf F_q^\times$, so division by $q-1$ gives the special-linear order. A split Cartan chooses two nonzero diagonal entries. A nonsplit Cartan is multiplication by $\mathbf F_{q^2}^\times$ on the two-dimensional $\mathbf F_q$-space $\mathbf F_{q^2}$. In each case the Weyl involution doubles the order of the normalizer. Finally, quotienting a Cartan by all scalar multiplications divides its order by $q-1$, giving $q-1$ and $q+1$.

For the determinant-compatible ambient group, every one of the two allowed determinant values has a fiber of size $|\operatorname{SL}_2(\mathbf F_q)|$. Therefore

$$
|\operatorname{GL}_2(\mathbf F_q)^\chi|
=2q(q^2-1).
$$

These derivations are worth retaining because three different divisions by $q-1$ occur: passing from general to special linear, passing from a linear group to its projective quotient, and restricting determinant values. They answer different field-degree questions.

The residual discriminant argument is applied before subgroup classification and gives $|H|\leq52$. That cap permits a shorter classification than the unrestricted theorem, and we prove it here.

**Theorem 6.1 (degree-capped projective subgroup theorem).** Let $\Omega$ be an algebraic closure of $\mathbf F_3$ and let

$$
\Gamma\subseteq\operatorname{PGL}_2(\Omega)
$$

be finite of order at most $52$. Then one of the following holds:

1. $\Gamma$ fixes a point of $\mathbf P^1(\Omega)$ and is conjugate into an affine Borel;
2. $\Gamma$ is cyclic of order prime to $3$ and lies in a torus, or is dihedral with prime-to-$3$ rotation subgroup and lies in its torus normalizer;
3. $\Gamma\simeq A_4$ or $S_4$.

The cyclic case can overlap the fixed-point case after extending scalars; it is listed separately because over $\mathbf F_q$ its torus can be split or nonsplit. Projective $A_5$ is already impossible because it has order $60$. A defining-characteristic or subfield group contributes no further capped case: $\operatorname{PSL}_2(\mathbf F_3)=A_4$ and $\operatorname{PGL}_2(\mathbf F_3)=S_4$, whereas

$$
|\operatorname{PSL}_2(\mathbf F_{3^r})|
=\frac{3^r(3^{2r}-1)}2\geq360
\qquad(r\geq2).
$$

**Proof.** We first treat groups of order prime to $3$. Let $Y$ be the smooth projective curve with function field $\Omega(x)^\Gamma$. The quotient map

$$
\pi:\mathbf P^1\longrightarrow Y
$$

has degree $|\Gamma|$. Choose a nonzero rational differential $\omega$ on $Y$. At a point with local parameter relation $t=u^e$ times a unit, tameness gives

$$
\operatorname{ord}_u(\pi^*\omega)
=e\operatorname{ord}_t(\omega)+(e-1).
$$

Taking degrees of divisors gives

$$
-2
=|\Gamma|(2g(Y)-2)
+\sum_{P\in\mathbf P^1}(e_P-1). \tag{6.1}
$$

The sum is nonnegative, so $g(Y)=0$. Because $\Omega$ is algebraically closed, $Y$ has a point; a genus-zero curve with a rational point is $\mathbf P^1$. This proves, rather than assumes, that the quotient is rational.

Stabilizers of points are cyclic. Indeed, after moving a fixed point to the origin, the derivative embeds a prime-to-$3$ stabilizer into $\Omega^\times$. If a finite-order fractional linear transformation has derivative one there, its first nonzero higher local term is multiplied by its order under iteration; that order is nonzero in $\Omega$, so the transformation must be the identity.

Let $e_1,\ldots,e_r$ be the nontrivial stabilizer orders of the branch orbits. One branch orbit with stabilizer $e_i$ has $|\Gamma|/e_i$ points. Using $g(Y)=0$ and dividing (6.1) by $|\Gamma|$ gives

$$
\frac2{|\Gamma|}
=2-r+\sum_{i=1}^r\frac1{e_i}. \tag{6.2}
$$

The right side is positive, so $r\leq3$. The case $r=0$ gives the trivial group, and $r=1$ is impossible: since $e_1\leq|\Gamma|$, equation (6.2) would give $2\geq|\Gamma|+1$. If $r=2$, then

$$
\frac2{|\Gamma|}=\frac1{e_1}+\frac1{e_2}.
$$

Each $e_i\leq|\Gamma|$, so equality forces $e_1=e_2=|\Gamma|$. Both branch points are fixed by the whole group, which embeds through the derivative at either point and is cyclic. With three branch orbits, order the indices increasingly. The elementary inequality

$$
\frac1{e_1}+\frac1{e_2}+\frac1{e_3}>1
$$

gives exactly

$$
(2,2,m),\quad(2,3,3),\quad(2,3,4),\quad(2,3,5).
$$

The last three triples contain a stabilizer of order $3$, impossible because $3\nmid|\Gamma|$. Thus only $(2,2,m)$ remains, and (6.2) gives $|\Gamma|=2m$. The stabilizer $C_m$ at the third branch orbit has index two and is normal. If $m>2$, its two fixed points are interchanged by every element outside $C_m$: an element preserving both would lie in the same diagonal torus, making the whole group cyclic and leaving only two branch orbits. An element interchanging the two fixed points has projective square one and conjugates the diagonal generator to its inverse. Hence $\Gamma=D_{2m}$. For $m=2$, the group has order four and three different order-two stabilizers, so it is the Klein four group, again $D_{2m}$. The prime-to-$3$ case is therefore cyclic or dihedral, with prime-to-$3$ rotation subgroup.

Now suppose $3\mid|\Gamma|$, and let $P$ be a Sylow $3$-subgroup. Every nonidentity element of $3$-power order in $\operatorname{PGL}_2(\Omega)$ is unipotent and has one fixed point. A nontrivial central element of $P$ therefore has a unique fixed point preserved by all of $P$. Move it to infinity. The homomorphism from the affine group to its multiplicative linear part kills $P$, because $\Omega^\times$ has no $3$-power torsion. Consequently

$$
P=\{x\mapsto x+a:a\in A\}
$$

for a finite $\mathbf F_3$-subspace $A\subset\Omega$. In particular $P$ is elementary abelian. If $P$ is normal, its unique common fixed point is preserved by $\Gamma$, giving the first branch.

Assume that $P$ is not normal. Let $x$ be its fixed point and let $n$ be the number of Sylow $3$-subgroups. Distinct Sylow subgroups have distinct fixed points: two translation subgroups at the same point either coincide or generate a larger $3$-subgroup. The action of $P$ on the other $n-1$ fixed points is free, since a nonidentity unipotent fixes only $x$. Hence

$$
n=1+a|P|\quad(a\geq1),
\qquad
|\Gamma|\geq |P|(|P|+1).
$$

The cap $52$ forces $|P|=3$. The stabilizer of $x$ is now $N_\Gamma(P)$. The centralizer in $\operatorname{PGL}_2(\Omega)$ of $x\mapsto x+1$ is the translation group; its intersection with $\Gamma$ is $P$, since $P$ is Sylow. Therefore conjugation embeds

$$
N_\Gamma(P)/P\hookrightarrow\operatorname{Aut}(P)\simeq C_2.
$$

Writing $c=|N_\Gamma(P)/P|$, we have $c=1$ or $2$ and

$$
|\Gamma|=3cn,
\qquad n\equiv1\pmod3.
$$

Under the cap the possibilities are

$$
\begin{array}{c|c|c}
c&n&|\Gamma|\\
\hline
1&4,7,10,13,16&12,21,30,39,48\\
2&4,7&24,42.
\end{array} \tag{6.3}
$$

The orders $21,39,$ and $42$ have a normal Sylow subgroup of order $7,13,$ and $7$, respectively. For order $30$, either its Sylow $5$-subgroup is normal or there are six such subgroups. The latter alternative, together with the ten Sylow $3$-subgroups prescribed by (6.3), would already give

$$
6(5-1)+10(3-1)=44
$$

nonidentity elements in a group of order $30$, which is impossible. Thus order $30$ also has a normal cyclic subgroup $C_r$ of prime order $r>3$. A semisimple $C_r$ fixes two points, its centralizer is a torus, and its normalizer has quotient of order two. Because a torus in characteristic $3$ has no element of order $3$, no group divisible by $3$ with such a normal $C_r$ can occur. This removes $21,30,39,$ and $42$.

It remains to remove $48$. A Sylow $2$-subgroup has order $16$ and is either normal or has three conjugates. In the second case the action on those three conjugates has transitive image in $S_3$, so its kernel is a normal $2$-subgroup of order $16$ or $8$. Thus in every case $\Gamma$ contains a normal $2$-subgroup $Q$ of order $8$ or $16$. Applying the already proved prime-to-$3$ classification to $Q$ shows that $Q$ is cyclic or dihedral. The automorphism groups of $C_8,C_{16},D_8,$ and $D_{16}$ are $2$-groups, so a Sylow $3$-subgroup centralizes $Q$. Each of these groups $Q$ contains an element of order four. Such an element is semisimple with two distinct fixed points, so its centralizer in $\operatorname{PGL}_2(\Omega)$ is a torus and has no element of order $3$. This is a contradiction.

Only orders $12$ and $24$ remain. Here $n=4$. The action on the four Sylow fixed points is faithful, because a fractional linear transformation fixing three points is the identity. Thus $\Gamma$ embeds in $S_4$. At order $12$ it is the unique index-two subgroup $A_4$; at order $24$ it is $S_4$. This proves the theorem. $\square$

Apply the theorem to $\Gamma=\mathbf P H$. The scalar kernel gives

$$
|\Gamma|=|H|/|H\cap Z|\leq52,
$$

so every hypothesis has already been verified. A projective fixed point is a line in the scalar-extended two-dimensional representation. A cyclic group preserves its two eigenlines and lies in a split or nonsplit torus over $\mathbf F_q$. In a dihedral group the cyclic rotation subgroup preserves that unordered pair and every reflection exchanges it, so the linear image lies in the corresponding Cartan normalizer after scalars are restored. The last branch consists exactly of the capped exceptional, and simultaneously defining-characteristic, groups $A_4$ and $S_4$. This proves the exhaustive list used below without importing an unproved general classification.

### 6.3 Reducible and Cartan cases

If $H$ fixes a line over $\overline{\mathbf F}_3$, then

$$
\bar\rho^{\mathrm{ss}}=\bar\alpha\oplus\bar\beta.
$$

The full image can still contain a unipotent $3$-group recording a nonsplit extension. A Borel image and its diagonal quotient must not be assigned the same degree.

A subgroup of a split Cartan is already diagonalizable over $\mathbf F_q$ and belongs to the reducible branch. A subgroup of a nonsplit Cartan can be irreducible over $\mathbf F_q$, but it is abelian and becomes diagonal over $\mathbf F_{q^2}$. Its projective field is cyclic. Global class field theory will show that a strict small projective field of this kind has degree at most two; an order-two projective action is diagonalizable in odd characteristic. Thus the nonsplit appearance cannot survive the arithmetic restrictions.

### 6.4 Cartan normalizers and dihedral images

Suppose $H$ lies in a Cartan normalizer but not in the Cartan. Its projective image is dihedral. The cyclic rotation subgroup determines a quadratic field $M/\mathbf Q$, and over $M$ the representation splits as two characters. Equivalently, in the absolutely irreducible case,

$$
\bar\rho\simeq
\operatorname{Ind}_{G_M}^{G_{\mathbf Q}}\bar\theta,
\qquad
\bar\theta\ne\bar\theta^\sigma.
$$

The field $M$ is cut out by the quotient from the normalizer to its order-two Weyl group. It is not necessarily the determinant field. Confusing those two quadratic characters can reverse the parity conclusion.

If the rotation order is even, the dihedral group has abelianization

$$
C_2\times C_2.
$$

Its projective field then contains three quadratic subfields. If the rotation order is odd, its abelianization is only $C_2$, and a separate analysis of the cyclic extension over $M$ is required. Both cases will be eliminated in Chapter 9, but for different reasons.

### 6.5 Exceptional and defining-characteristic images

The exceptional projective groups have orders

$$
|A_4|=12,
\qquad |S_4|=24,
\qquad |A_5|=60.
$$

When the projective image is one of these groups, the degree of the projective field is exactly the displayed order, and the degree of the full field is that order multiplied by $|H\cap Z|$. Consequently the unconditional cap $52$ immediately excludes projective $A_5$. It does not exclude $A_4$ or $S_4$.

Those two groups have useful solvable quotients:

$$
A_4/V_4\simeq C_3,
$$

and

$$
S_4/V_4\simeq S_3.
$$

The corresponding subfields are cubic or $S_3$ fields and retain the strict ramification cutoff. They are eliminated arithmetically in Chapter 10.

If the projective image contains $\operatorname{PSL}_2(\mathbf F_{q_0})$ with $q_0\geq9$, then its order is at least

$$
|\operatorname{PSL}_2(\mathbf F_9)|=360>52.
$$

Thus only the subfield $q_0=3$ survives the degree test. There

$$
\operatorname{PSL}_2(\mathbf F_3)\simeq A_4,
$$

so it returns to the exceptional branch already listed.

### 6.6 The special coincidences over $\mathbf F_3$

For $q=3$,

$$
|\operatorname{GL}_2(\mathbf F_3)|=48,
\qquad
|\operatorname{SL}_2(\mathbf F_3)|=24,
$$

and

$$
\operatorname{PGL}_2(\mathbf F_3)\simeq S_4,
\qquad
\operatorname{PSL}_2(\mathbf F_3)\simeq A_4.
$$

The basic subgroup ledger becomes

$$
\begin{array}{c|c|c}
\text{matrix group}&\text{matrix order}&\text{projective shape}\\
\hline
B&12&S_3\\
C_{\mathrm s}&4&C_2\\
N(C_{\mathrm s})&8&V_4\\
C_{\mathrm{ns}}&8&C_4\\
N(C_{\mathrm{ns}})&16&D_8\\
\operatorname{SL}_2(\mathbf F_3)&24&A_4\\
\operatorname{GL}_2(\mathbf F_3)&48&S_4.
\end{array}
$$

Here $D_8$ denotes a dihedral group of order $8$. The split normalizer has projective order $4$ and is the Klein four group.

The determinant on $\operatorname{GL}_2(\mathbf F_3)$ factors through the sign character of its projective $S_4$. Hence the preimage of $A_4$ is $\operatorname{SL}_2(\mathbf F_3)$ and has trivial determinant. A projective $A_4$ image is therefore incompatible with an odd cyclotomic determinant unless the claimed projective identification or coefficient field has been misstated.

Finally, the central extension

$$
1\longrightarrow\{\pm I\}
\longrightarrow\operatorname{GL}_2(\mathbf F_3)
\longrightarrow S_4\longrightarrow1
$$

has no complement mapping isomorphically onto $S_4$. Thus a subgroup with projective image $S_4$ is the full group of order $48$, not an unrecorded order-$24$ image with surjective determinant.

For completeness, a complement would meet $\operatorname{SL}_2(\mathbf F_3)$ in a subgroup mapping isomorphically to $A_4$. But $\operatorname{SL}_2(\mathbf F_3)$ has a unique element of order two, namely $-I$, whereas $A_4$ has three involutions. No such subgroup exists. This proves the nonsplitting without relying on a name for the central extension.

## 7. The small abelian field ledger over $\mathbf Q$

### 7.1 Abelian extensions supported at $3$

Every finite abelian extension of $\mathbf Q$ is contained in a cyclotomic field. If it is unramified away from $3$, it lies in

$$
\mathbf Q(\zeta_{3^m})
$$

for some $m$. The Galois group is cyclic of order

$$
\varphi(3^m)=2\cdot3^{m-1}.
$$

This already rules out abelian quotients of order $4$ and every Klein four quotient. It does not by itself rule out a cyclic cubic quotient, because the real cubic subfield of $\mathbf Q(\zeta_9)$ is ramified only at $3$.

The local upper cutoff supplies the missing restriction. Let $C/\mathbf Q$ be a cyclic cubic subfield. If its completion at $3$ were unramified, then $C$ would be unramified at every finite prime, which is impossible by the class number one of $\mathbf Q$ or by the discriminant-one obstruction. Thus $C/\mathbf Q$ is ramified at $3$. A ramified cyclic cubic extension of $\mathbf Q_3$ is wild. By Hasse--Arf its positive upper break is an integer, hence at least $1$. It cannot be a quotient of a local extension whose upper groups vanish for $u>1/2$. Therefore an abelian quotient of a strict residual field has no $3$-part.

It follows that every abelian subextension $A/\mathbf Q$ of $K_1/\mathbf Q$ is contained in

$$
\boxed{\mathbf Q(\zeta_3)=\mathbf Q(\sqrt{-3}).}
$$

Equivalently,

$$
\operatorname{Gal}(A/\mathbf Q)\in\{1,C_2\}.
$$

This conclusion uses the ramification cutoff as well as the ramification set. A root-discriminant comparison alone would be insufficient.

### 7.2 Why a cyclic cubic field is a genuine trap

Let $F_3^+$ be the real cubic subfield of $\mathbf Q(\zeta_9)$. Its discriminant is

$$
D_{F_3^+}=3^4,
$$

because its two nontrivial characters both have conductor $9$, and the conductor--discriminant product is $9\cdot9$. Therefore

$$
\operatorname{rd}(F_3^+)=3^{4/3}=4.326\ldots<3^{3/2}.
$$

Thus the sentence

$$
\operatorname{rd}(L)<3^{3/2}
\quad\Longrightarrow\quad
L\text{ has no cubic subfield}
$$

is false.

The local conductor of the cubic character is $3^2$, so its upper break is

$$
2-1=1.
$$

The local extension is cyclic of degree three with a single upper break one. For a cyclic degree-three extension with break $b$, the different exponent is

$$
d=(3-1)(b+1).
$$

Thus here

$$
e=3,
\qquad d=4,
\qquad \frac de=\frac43.
$$

This recovers the global root-discriminant exponent $4/3$ and shows concretely why the field passes the coarse discriminant test while failing the break test.

That break violates the finite-flat cutoff $1/2$. The correct exclusion is therefore

$$
\left.
\begin{array}{c}
\operatorname{rd}(L)<3^{3/2},\\
L/\mathbf Q\text{ unramified outside }3,\\
G_3^u=1\text{ for }u>1/2
\end{array}
\right\}
\Longrightarrow
L\text{ has no cyclic cubic quotient}.
$$

This example will be the standard audit whenever a later argument tries to replace upper ramification by one coarse global number.

### 7.3 Quadratic and quartic possibilities

A quadratic field unramified at every finite prime except $3$ has fundamental discriminant supported at $3$. The only nontrivial possibility is

$$
\mathbf Q(\sqrt{-3}),
$$

of discriminant $-3$. It is the field cut out by $\bar\chi_3$.

Indeed, an odd fundamental discriminant is squarefree and congruent to $1$ modulo $4$. The only nontrivial squarefree integers supported at $3$ are $3$ and $-3$; among them only $-3$ is $1$ modulo $4$. The real field $\mathbf Q(\sqrt3)$ has discriminant $12$ and is ramified at $2$, so it is not a second candidate.

There is no cyclic quartic extension supported only at $3$, because

$$
(\mathbf Z/3^m\mathbf Z)^\times
$$

has order $2\cdot3^{m-1}$ and hence no quotient of order $4$. There is no biquadratic extension either, because there is only one nontrivial quadratic character supported at $3$.

These assertions remain true without a discriminant estimate. The estimate becomes necessary for nonabelian projective groups and for large defining-characteristic images.

### 7.4 The Eisenstein quadratic field

Put

$$
K=\mathbf Q(\zeta_3)=\mathbf Q(\sqrt{-3}),
\qquad
\lambda=(1-\zeta_3).
$$

Then

$$
3\mathcal O_K=\lambda^2,
\qquad N\lambda=3,
\qquad |D_K|=3.
$$

The class number of $K$ is one. Indeed, Minkowski's ideal-class bound in degree two and signature $(0,1)$ says that every ideal class contains an integral ideal of norm at most

$$
\frac{2!}{2^2}\frac4\pi\sqrt3
=\frac{2\sqrt3}{\pi}<2.
$$

Such an ideal has norm one and is principal.

Consequently $K$ has no nontrivial abelian extension unramified at every finite prime. A cyclic extension supported only at $\lambda$ must appear in a nontrivial ray class group. This observation controls the cubic layer of an $S_3$ or $S_4$ field.

### 7.5 The first cubic ray layer over $\mathbf Q(\zeta_3)$

Because the class group is trivial, the ray group of modulus $\lambda^a$ is a quotient of

$$
(\mathcal O_K/\lambda^a)^\times
$$

by the image of the global units $\mu_6$. Its numerator has order

$$
|(\mathcal O_K/\lambda^a)^\times|
=2\cdot3^{a-1}.
$$

The exact sequence being used is

$$
\mathcal O_K^\times
\longrightarrow(\mathcal O_K/\lambda^a)^\times
\longrightarrow\operatorname{Cl}_{\lambda^a}(K)
\longrightarrow\operatorname{Cl}(K)
\longrightarrow1.
$$

There is no infinite-place factor because $K$ is imaginary. The last group is trivial, so the size and structure of the ray group are controlled entirely by the two groups on the left.

For $a=1$, the images of $\pm1$ fill the group of order two. For $a=2$, the six roots of unity have six distinct images and fill the group of order six. Hence

$$
\operatorname{Cl}_{\lambda}(K)=1,
\qquad
\operatorname{Cl}_{\lambda^2}(K)=1.
$$

At $a=3$, the numerator has order $18$, while the unit image has order $6$. The quotient has order $3$. Its cubic ray field is the first possible cyclic cubic extension of $K$ supported at $\lambda$; it is realized by

$$
\mathbf Q(\zeta_9)/\mathbf Q(\zeta_3).
$$

For every $a\geq2$, the six roots of unity remain distinct modulo $\lambda^a$. Hence

$$
|\operatorname{Cl}_{\lambda^a}(K)|=3^{a-2}.
$$

In particular every positive-order ray quotient beyond the tame residue factor is a $3$-group. This single formula controls both the odd-dihedral rotation calculation and the first $S_3$ layer.

Thus every nontrivial cyclic cubic extension $E/K$ unramified away from $\lambda$ has conductor exponent at least $3$ and upper break at least

$$
b_K=3-1=2.
$$

Since $K_\lambda/\mathbf Q_3$ is tamely ramified of degree two, upper breaks divide by two on passage to the lower base:

$$
b_{\mathbf Q_3}=\frac{b_K}{2}\geq1.
$$

This scaling is the positive-break part of the Herbrand base-change rule for a tame extension: restriction from $G_{\mathbf Q_3}$ to $G_{K_\lambda}$ multiplies positive upper indices by the tame ramification index two. It is not an informal division of conductor exponents; the conductor is first converted to the upper break and only then transported.

For the first ray field the different ledger can be checked exactly. The extension $\mathbf Q_3(\zeta_9)/K_\lambda$ has degree three and break two, so

$$
d\bigl(\mathbf Q_3(\zeta_9)/K_\lambda\bigr)
=(3-1)(2+1)=6.
$$

The tame quadratic extension $K_\lambda/\mathbf Q_3$ has different exponent one. Transitivity of the different gives

$$
d\bigl(\mathbf Q_3(\zeta_9)/\mathbf Q_3\bigr)
=6+3\cdot1=9.
$$

The absolute ramification index is six, hence the normalized different is $9/6=3/2$. This is exactly the root-discriminant endpoint $3^{3/2}$ and agrees with the cyclotomic discriminant formula.

Therefore no such cubic layer can lie inside a strict residual field whose upper cutoff over $\mathbf Q_3$ is $1/2$. The endpoint case is not ambiguous: the first cubic layer has lower-base break $1$, strictly larger than $1/2$.

## 8. Reducible residual representations

### 8.1 The two diagonal characters

Assume first that $M$ is reducible after extension of scalars to a finite field $k'/k$. Then

$$
(M\otimes_k k')^{\mathrm{ss}}
\simeq\bar\alpha\oplus\bar\beta
$$

for characters

$$
\bar\alpha,\bar\beta:G_{\mathbf Q}\longrightarrow(k')^\times.
$$

The kernel of $M$ is contained in the kernel of each constituent character, even if the line is first written over $k'$. Their cutout fields are therefore abelian subfields of $K_1$ and inherit its ramification cutoff. Chapter 7 gives

$$
\bar\alpha,\bar\beta\in\{1,\bar\chi_3\}.
$$

The determinant relation

$$
\bar\alpha\bar\beta=\bar\chi_3
$$

therefore forces the unordered pair

$$
\boxed{\{\bar\alpha,\bar\beta\}=\{1,\bar\chi_3\}.}
$$

In particular, both characters already take values in $\mathbf F_3$. A residual representation initially written over $\mathbf F_{3^f}$ acquires no new diagonal characters in the strict setting. This is coefficient descent obtained from arithmetic character classification, not from enlarging coefficients.

Oddness is visible: complex conjugation acts by $1$ on the trivial constituent and by $-1$ on the cyclotomic constituent. Equal-character semisimplification is already excluded by the global character and determinant calculation. Since the two characters are distinct, their eigenspaces and every unique stable line descend from $k'$ to $k$; thus the actual extension can be written over $k$.

### 8.2 The affine extension field

A chosen stable lattice can reduce in either triangular order:

$$
0\longrightarrow k(1)\longrightarrow M_+
\longrightarrow k\longrightarrow0,
$$

or

$$
0\longrightarrow k\longrightarrow M_-
\longrightarrow k(1)\longrightarrow0.
$$

The first class lies in $H^1(\mathbf Q,k(1))$ and the second in $H^1(\mathbf Q,k(-1))$. At the residual prime $3$ there is an equality of coefficient characters

$$
k(-1)\simeq k(1),
$$

because $\bar\chi_3^2=1$. Hence both orientations are governed, as generic representations, by a cocycle

$$
c\in Z^1(G_{\mathbf Q,\{3,\infty\}},k(1)).
$$

Put $K=\mathbf Q(\zeta_3)$. On $G_K$ the coefficient character is trivial, so $c|_{G_K}$ is an additive homomorphism. Inflation--restriction for

$$
1\longrightarrow G_K\longrightarrow G_{\mathbf Q}
\longrightarrow C_2\longrightarrow1
$$

shows that restriction on $H^1$ is injective: positive-degree cohomology of $C_2$ on a characteristic-three vector space vanishes by averaging. Thus a nonzero extension class gives a nonzero elementary abelian $3$-extension over $K$.

This field is visible inside the full cutout field $L=\mathbf Q(M)$. The determinant already puts $K$ inside $L$, and over $G_K$ the two diagonal characters are trivial. Therefore

$$
\operatorname{Gal}(L/K)=\operatorname{im}(c)
$$

for a nonsplit triangular image in the descended basis. Any nonzero image has a quotient $C_3$, hence $L/K$ contains a cyclic cubic subextension.

### 8.3 The ray-class obstruction

The coefficient-enhancement construction of §3.1 replaces the supplied residual witness by a $k$-linear one. Because $3=0$ in $k$, it is killed by $3$. The field $L$ therefore satisfies

$$
G_{L_w/\mathbf Q_3}^u=1
\qquad(u>1/2).
$$

Every subextension inherits this cutoff. Let $F/K$ be a cyclic cubic quotient supplied by a nonzero $c$. It is unramified away from the unique prime $\lambda$ above $3$. If it were unramified at $\lambda$, it would be unramified everywhere, contradicting the class number one calculation of §7.4. If it ramifies, §7.5 shows that its conductor is at least $\lambda^3$ and its upper break over $K_\lambda$ is at least $2$.

The quadratic extension $K_\lambda/\mathbf Q_3$ is tame of ramification index two. Herbrand's subgroup rule says that an ambient extension whose upper groups over $\mathbf Q_3$ vanish for $u>1/2$ has upper groups over $K_\lambda$ vanishing for $v>1$. It therefore cannot have a quotient with break at least $2$. Hence no such $F$ exists and

$$
\boxed{[c]=0.}
$$

This proof uses the finite-flat ramification theorem only on the supplied middle module. It does not classify its endpoint models and does not infer that a generic splitting extends to a selected integral model.

### 8.4 Orientation-independent splitting

The preceding argument treats both triangular orders at once. The equality $k(-1)=k(1)$ identifies their generic coefficient modules, while the field cut out by a nonzero class is independent of which character was written first. Thus no connected--étale comparison, uniqueness theorem, or local endpoint extension calculation is required.

The conclusion also survives coefficient extension. If a class over $k$ became zero only after tensoring with $k'/k$, injectivity of scalar extension on the finite-dimensional $k$-cohomology group would already make it zero over $k$. Conversely, a stable line first seen over $k'$ descends because its two characters are the distinct $\mathbf F_3$-valued characters $1$ and $\bar\chi_3$. The actual lattice reduction, not only its semisimplification, is therefore split over the original $k$.

### 8.5 The exact residual conclusion

**Proposition 8.1 (reducible residual classification).** Let $M$ be a rank-two $k$-representation of $G_{\mathbf Q}$ with determinant $\bar\chi_3$. Assume that it is unramified away from $3$, its restriction at $3$ has a finite-flat model over $\mathbf Z_3$, and it is reducible over $\overline{\mathbf F}_3$. Then

$$
\boxed{M\simeq k\oplus k(1).}
$$

**Proof.** The character fields are abelian subfields of the cutout field and inherit the local cutoff. Chapter 7 restricts both characters to $1$ and $\bar\chi_3$, and the determinant chooses one of each. The chosen lattice reduction is an extension in one of the two orientations. Sections 8.2--8.4 attach its affine cubic layer and show directly that a nonzero class would violate the residual upper-break cutoff. Hence the sequence splits in either orientation. $\square$

The proposition is invariant under extension of the residue field. It says more than

$$
M^{\mathrm{ss}}\simeq1\oplus\bar\chi_3.
$$

It says that the actual residual module supplied by the named lattice is split. It still does not say that the characteristic-zero representation has an invariant line.

## 9. Cartan and dihedral branches

### 9.1 Split Cartan

An image contained in a split Cartan preserves two lines. Proposition 8.1 therefore applies immediately. The diagonal image is generated by

$$
\begin{pmatrix}1&0\\0&-1\end{pmatrix},
$$

so it has order two, its full cutout field is $\mathbf Q(\zeta_3)$, and its projective image also has order two.

The equality of full and projective orders here comes from the scalar intersection, not from the word “split.” The surviving group is

$$
H=\{I,\operatorname{diag}(1,-1)\},
\qquad H\cap Z=\{I\}.
$$

Its determinant map is an isomorphism onto $\mathbf F_3^\times$. Thus the full, projective, and determinant fields all coincide. Before the character calculation, the ambient split Cartan has order four and contains the scalar $-I$; assigning degree two at that earlier stage would be wrong.

A subgroup of a Borel can have an additional unipotent part of order three. That part represents a nonsplit residual extension. The affine ray-class argument makes it trivial. Thus the Borel branch contracts to the same order-two split Cartan image.

### 9.2 Nonsplit Cartan

Suppose $H$ is contained in a nonsplit Cartan. Then $H$ is abelian, although its natural module can be irreducible over $k$. Its full field is an abelian subextension of $K_1$, so Chapter 7 gives

$$
|H|\leq2.
$$

If $H$ has order one, its determinant is trivial. If it has order two and is contained in the cyclic nonsplit Cartan, its unique nontrivial element is the scalar $-I$ whenever the full Cartan has a unique involution. That element also has determinant one. Either alternative contradicts

$$
\det H=\{1,-1\}.
$$

Hence a genuinely nonsplit Cartan image cannot occur. This argument distinguishes irreducibility over $k$ from absolute irreducibility: the former is eliminated by abelian field theory, not by locating a line over $k$.

### 9.3 Even dihedral projective image

Let the projective image be dihedral with even rotation order. Its abelianization is $C_2\times C_2$. Therefore its projective field contains a biquadratic subextension of $\mathbf Q$. Every one of its quadratic characters is unramified away from $3$, but Chapter 7 supplies only one nontrivial such character. This is impossible.

To verify the abelianization, write

$$
D_{2m}=\langle r,s:r^m=s^2=1,\ srs=r^{-1}\rangle.
$$

After abelianization the last relation gives $r=r^{-1}$, so $r^2=1$. When $m$ is even, this does not kill $r$, and the independent images of $r$ and $s$ give $V_4$. When $m$ is odd, $r^m=1$ together with $r^2=1$ kills $r$, leaving only $C_2$. This is why the next section needs a different argument for odd rotation order.

Over $\mathbf F_3$ this eliminates both Cartan-normalizer possibilities at once:

$$
\mathbf P N(C_{\mathrm s})\simeq V_4,
\qquad
\mathbf P N(C_{\mathrm{ns}})\simeq D_8.
$$

The argument concerns the projective field. It does not assume that the full matrix image is itself dihedral or that its scalar kernel is trivial.

### 9.4 Odd dihedral projective image

For a larger residue field, a Cartan normalizer can contain a dihedral subgroup whose rotation order $m$ is odd. Its abelianization is only $C_2$, so the preceding biquadratic argument no longer applies.

Let $M/\mathbf Q$ be the quadratic field fixed by the rotation subgroup. The small abelian ledger forces

$$
M=\mathbf Q(\zeta_3).
$$

The rotation field is a cyclic extension of $M$ of degree $m$. Since a Cartan has order prime to $3$ modulo scalars in this branch,

$$
(m,3)=1.
$$

Every ray class group of $M$ supported at the unique prime $\lambda$ above $3$ has, after its order-two unit factor is removed, $3$-power order. More concretely, for conductor exponent $a\geq2$ its order divides

$$
\frac{2\cdot3^{a-1}}6=3^{a-2}.
$$

There is therefore no nontrivial cyclic quotient of odd order prime to $3$. Hence $m=1$, contradicting the dihedral hypothesis.

This calculation is needed when $f>1$. The simpler even-dihedral abelianization test does not cover it.

### 9.5 The induced-character interpretation

The same exclusion can be phrased representation-theoretically. If

$$
\bar\rho\simeq
\operatorname{Ind}_{G_M}^{G_{\mathbf Q}}\bar\theta,
$$

then

$$
\bar\rho|_{G_M}\simeq
\bar\theta\oplus\bar\theta^\sigma.
$$

The ratio $\bar\theta/\bar\theta^\sigma$ cuts out the cyclic rotation field. If the ratio has even order, the projective group exposes a second quadratic character. If it has odd order, ray class theory over $M=\mathbf Q(\zeta_3)$ forces the ratio to be trivial. In either case

$$
\bar\theta=\bar\theta^\sigma,
$$

so the induction is reducible after semisimplification. Proposition 8.1 then gives the split residual module.

This proves the exclusion of a residually irreducible small dihedral representation. It does not say that every characteristic-zero potentially dihedral representation has already been excluded; a pair of inducing characters can become congruent modulo $\varpi$. That lifting issue returns in Chapter 14.

## 10. Exceptional and full residual images

### 10.1 Projective $A_4$

Suppose the projective field $P/\mathbf Q$ has Galois group $A_4$. The normal Klein four subgroup gives a cyclic cubic quotient:

$$
\operatorname{Gal}(P^{V_4}/\mathbf Q)
\simeq A_4/V_4\simeq C_3.
$$

This cubic field is a quotient of the strict residual field. It is unramified away from $3$ and its local upper groups vanish for $u>1/2$. Chapter 7 shows that no such cyclic cubic field exists. Hence projective $A_4$ is impossible.

Over $\mathbf F_3$ there is an even shorter determinant check: the full preimage of $A_4$ is $\operatorname{SL}_2(\mathbf F_3)$, on which determinant is trivial. The cubic-field argument is retained because it works uniformly for exceptional $A_4$ images over larger residue fields and checks the arithmetic rather than relying on a small-group coincidence.

### 10.2 Projective $S_4$

Suppose

$$
\operatorname{Gal}(P/\mathbf Q)\simeq S_4.
$$

The fixed field

$$
E=P^{V_4}
$$

has Galois group

$$
\operatorname{Gal}(E/\mathbf Q)\simeq S_3.
$$

Its unique quadratic subfield is fixed by $A_3$. By the quadratic ledger it must be

$$
K=\mathbf Q(\zeta_3).
$$

The extension $E/K$ is cyclic cubic and is unramified away from the unique prime $\lambda$ above $3$. Section 7.5 shows that its conductor exponent is at least $3$, its upper break over $K_\lambda$ is at least $2$, and its corresponding lower-base break over $\mathbf Q_3$ is at least $1$. This contradicts the inherited cutoff $1/2$.

Thus projective $S_4$ is impossible. Notice that the degree cap alone does not prove this:

$$
|S_4|=24<52.
$$

The decisive input is the cubic ray layer.

### 10.3 Projective $A_5$ and subfield groups

If the projective image is $A_5$, then

$$
[P:\mathbf Q]=60>52,
$$

contradicting the unconditional residual degree cap. No solvable quotient is needed.

If the projective image contains $\operatorname{PSL}_2(\mathbf F_{q_0})$ for $q_0\geq9$, its order is at least $360$, again impossible. If $q_0=3$, the projective special linear group is $A_4$ and has already been eliminated. A group between projective special and general linear groups is no smaller, so the same alternatives cover it.

This is the only place where the numerical value $52$ is used to eliminate a projectively simple branch. The $A_4$ and $S_4$ branches require field structure even though their degrees are small.

### 10.4 The full $\operatorname{GL}_2(\mathbf F_3)$ diagnostic

Assume for diagnosis that

$$
H=\operatorname{GL}_2(\mathbf F_3).
$$

Then the full residual field $L$ has degree $48$, the center has order two, and the projective field has degree $24$ with Galois group $S_4$. The determinant field is

$$
K=L^{\operatorname{SL}_2(\mathbf F_3)}
=\mathbf Q(\zeta_3).
$$

Inside $\operatorname{SL}_2(\mathbf F_3)$ there is a normal quaternion subgroup $Q_8$, and

$$
\operatorname{GL}_2(\mathbf F_3)/Q_8\simeq S_3.
$$

Thus

$$
E=L^{Q_8}
$$

is an $S_3$ extension of degree $6$, and $E/K$ is cyclic cubic. The ledger is

$$
\begin{array}{c|c|c}
\text{field}&\text{degree over }\mathbf Q&\text{Galois group}\\
\hline
L&48&\operatorname{GL}_2(\mathbf F_3)\\
P&24&S_4\\
E&6&S_3\\
K&2&C_2.
\end{array}
$$

All four fields inherit the strict root-discriminant bound, but that bound does not exclude degrees $48$, $24$, or $6$. The local cutoff passes to the $S_3$ quotient. The ray calculation for $E/K$ forces lower-base break at least $1$, contradicting $1/2$. Hence the assumed full image cannot occur.

This diagnostic accounts for every factor: scalar center, projective quotient, determinant subfield, quaternion kernel, and cubic layer. Replacing $48$ by $24$, or identifying $P$ with $L$, would leave the field argument incomplete even though the final contradiction happens in the common degree-$6$ quotient.

### 10.5 The residual exclusion theorem

**Theorem 10.1 (exclusion of irreducible strict residual images).** Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_{3^f})
$$

be continuous with determinant $\bar\chi_3$. Assume that its underlying module has a finite-flat model over $\mathbf Z_3$ and is unramified away from $3$. Then $\bar\rho$ is absolutely reducible. In fact the representation itself is

$$
\bar\rho\simeq1\oplus\bar\chi_3.
$$

**Proof strategy.** Its cutout field has root discriminant $<3^{3/2}$, degree at most $52$, and local upper cutoff $1/2$. Apply the proved degree-capped Theorem 6.1. A Cartan image is abelian and reduces to the split character branch. A Cartan-normalizer image is excluded by the quadratic and ray class ledgers. Projective $A_4$ gives a forbidden cyclic cubic quotient; projective $S_4$ gives a forbidden cubic ray layer over $\mathbf Q(\zeta_3)$; projective $A_5$ has order $60$, and every defining-characteristic group from $\mathbf F_{3^r}$ with $r\geq2$ has order at least $360$. Thus the representation is absolutely reducible. Proposition 8.1 classifies its characters and kills its extension class by the same upper-break and ray-class obstruction.

**Proof.** Put $H=\overline\rho(G_{\mathbf Q})$ and $P=H/(H\cap Z)$. The local finite-flat theorem and the global different formula give

$$
\operatorname{rd}(L)<3^{3/2},
\qquad
G_{L_w/\mathbf Q_3}^u=1\quad(u>1/2),
$$

for $L=\mathbf Q(M)$. The degree-$53$ lower bound gives

$$
|H|=[L:\mathbf Q]\leq52.
$$

Every subfield and quotient field used below inherits the appropriate one of these three restrictions.

Extend the coefficient field temporarily to an algebraic closure. If the representation fixes a line, it belongs to the reducible branch and Proposition 8.1 finishes the proof. Assume from now on that it is absolutely irreducible. Theorem 6.1 leaves the Cartan-normalizer and capped exceptional possibilities described below; the rational Cartan diagnostics are retained to track descent to $k$.

First suppose $P$ is cyclic and contained in a Cartan. If the linear image is in a split Cartan, it already fixes two lines, contrary to the assumption. If it is in a nonsplit Cartan, the full matrix image is abelian. Its field $L/\mathbf Q$ is then an abelian strict extension, so $|H|\leq2$. The only involution in a nonsplit Cartan is the scalar $-I$, whose determinant is one. Such an image cannot have determinant $\overline\chi_3$. Thus the cyclic case is impossible under absolute irreducibility.

Second suppose $P$ is dihedral. If its rotation order is even, $P^{\mathrm{ab}}$ is $V_4$, producing three quadratic subfields although only $\mathbf Q(\zeta_3)$ is available. If its rotation order is odd, the reflection quotient cuts out the sole possible quadratic field $K=\mathbf Q(\zeta_3)$. The rotation field over $K$ is cyclic of order prime to three. Since $K$ has class number one and its ray groups supported at $\lambda$ have only $3$-power order after the global units are divided out, that cyclic field is trivial. Either conclusion contradicts a nontrivial dihedral image.

Third suppose $P$ is exceptional. For $A_4$, quotienting by $V_4$ gives a cyclic cubic field over $\mathbf Q$. It cannot be unramified everywhere, so it ramifies at $3$; its positive upper break is then an integer at least one, violating the cutoff $1/2$. For $S_4$, quotienting by $V_4$ gives an $S_3$ field. Its quadratic resolvent is $K$, and the cubic layer over $K$ has conductor at least $\lambda^3$, hence upper break at least two over $K_\lambda$ and at least one over $\mathbf Q_3$. This again violates the cutoff. For $A_5$, the projective field alone has degree $60>52$.

The wild Sylow analysis in Theorem 6.1 has already exhausted the defining-characteristic possibilities under the cap. To reconcile that proof with the usual subfield labels, any candidate containing $\operatorname{PSL}_2(\mathbf F_{q_0})$ with $q_0\geq9$ would satisfy

$$
|P|\geq|\operatorname{PSL}_2(\mathbf F_9)|=360>52.
$$

If $q_0=3$, the special-linear projective group is $A_4$; adjoining its projective outer involution gives at most the already excluded $S_4$ branch. Thus the defining-characteristic notation introduces no group omitted by the proved capped theorem, and absolute irreducibility is contradicted in every case.

It follows that $M$ is reducible after scalar extension. Section 8.1 shows that its two characters already take values in $\mathbf F_3$ and are $1$ and $\overline\chi_3$. In either triangular orientation, a nonzero extension would give the forbidden cyclic cubic ray layer of §§8.2--8.4. Therefore the actual $k$-representation is split:

$$
M\simeq k\oplus k(1).
$$

No step in this proof replaced $H$ by $P$, assumed $f=1$, or inferred splitting from semisimplification. $\square$

The theorem does not assume $f=1$. An underlying finite-flat model is enough because §3.1 constructs a coefficient-linear replacement. The proof applies the degree-capped subgroup theorem and the actual scalar kernel before descending the characters. If one instead uses only the seven subgroups listed over $\mathbf F_3$, a residue degree greater than one is a genuine gap.

## 11. The complete residual candidate ledger

### 11.1 Candidates over $\mathbf F_3$

For quick reference, the possible maximal shapes over $\mathbf F_3$ and their arithmetic fate are as follows. The order in the second column is the full matrix order of the displayed maximal group; an actual subgroup can have smaller order.

$$
\begin{array}{c|c|c|c}
\text{shape}&|H|&|\mathbf P H|&\text{decisive test}\\
\hline
B&12&6&\text{extension class vanishes}\\
C_{\mathrm s}&4&2&\text{characters are }1,\bar\chi_3\\
C_{\mathrm{ns}}&8&4&\text{abelian image has order at most }2\\
N(C_{\mathrm s})&8&4&V_4\text{ quotient impossible}\\
N(C_{\mathrm{ns}})&16&8&V_4\text{ abelianization impossible}\\
\operatorname{SL}_2(\mathbf F_3)&24&12&\det=1\text{; also a }C_3\text{ quotient}\\
\operatorname{GL}_2(\mathbf F_3)&48&24&S_3\text{ quotient and cubic ray layer}.
\end{array}
$$

The surviving image is

$$
H=\left\{
I,
\begin{pmatrix}1&0\\0&-1\end{pmatrix}
\right\}\simeq C_2.
$$

Its full field, determinant field, and projective field all equal

$$
\mathbf Q(\zeta_3).
$$

The scalar intersection is trivial, because the nonidentity matrix is not scalar. Thus

$$
|H|=|\mathbf P H|=|\det H|=2.
$$

This final equality is special to the surviving group and should not be inserted earlier in the ledger.

After imposing the global diagonal-character calculation but before killing extension and projective branches, the concrete degree ledger is even shorter:

| Candidate matrix image | $\lvert H\rvert=[L:\mathbf Q]$ | $\lvert H\cap Z\rvert$ | Projective group | Determinant quotient | Decisive field |
|---|---:|---:|---|---:|---|
| split diagonal $C_2$ | $2$ | $1$ | $C_2$ | $C_2$ | $L=\mathbf Q(\zeta_3)$ |
| nonsplit Borel $S_3$ | $6$ | $1$ | $S_3$ | $C_2$ | $L/K$ cyclic cubic |
| split normalizer | $8$ | $2$ | $V_4$ | $C_2$ | extra quadratic field |
| nonsplit normalizer | $16$ | $2$ | $D_8$ | $C_2$ | $V_4$ abelianization |
| special-linear lift | $24$ | $2$ | $A_4$ | $1$ | wrong determinant; cubic quotient |
| full image | $48$ | $2$ | $S_4$ | $C_2$ | $Q_8$ quotient gives $S_3$ |

The full Borel of order $12$ is absent from this narrowed table because its diagonal quotient is $C_2\times C_2$, whereas the two global diagonal characters generate only one $C_2$. Its only nonsplit remnant is the order-six $S_3$ row. Likewise, the full split Cartan of order four contracts to the first row. This table records actual field degrees, not ambient subgroup orders.

### 11.2 Candidates over $\mathbf F_{3^f}$

For $q=3^f$, the same reasoning begins with the degree-capped Theorem 6.1 rather than with the preceding small table.

- A reducible image is handled by its two character fields and its extension class.
- A Cartan image has cyclic projective field. The strict abelian cutoff reduces it to projective order at most two, hence to an absolutely reducible action.
- A normalizer image has dihedral projective field. Even rotation order exposes a forbidden $V_4$ quotient; odd rotation order exposes a prime-to-$3$ ray class quotient over $\mathbf Q(\zeta_3)$, also forbidden.
- Projective $A_4$ and $S_4$ expose cubic layers; projective $A_5$ has degree $60>52$.
- A subfield group with $q_0\geq9$ has projective degree at least $360$; $q_0=3$ is $A_4$ or $S_4$.

The determinant-compatible ambient group has order

$$
2q(q^2-1),
$$

not $|\operatorname{GL}_2(\mathbf F_q)|$ when $f>1$. The arithmetic degree cap applies to the actual image $H$, not to the ambient group. A small subgroup can survive a large ambient matrix order, so one cannot prove reducibility merely by observing that the full ambient order exceeds $52$.

After the projective branches are eliminated, both characters have image of order at most two and hence values in $\mathbf F_3$. The extension-class calculation then commutes with scalar extension to $k$. This is how the general theorem returns to

$$
k\oplus k(1).
$$

### 11.3 Fields, degrees, and decisive obstructions

The field ledger can be summarized independently of matrices.

$$
\begin{array}{c|c|c}
\text{field quotient}&\text{possible degree}&\text{obstruction}\\
\hline
\text{abelian}&1,2&\text{only }\mathbf Q(\zeta_3)\text{ survives}\\
C_3&3&\text{upper break is an integer }\geq1\\
V_4&4&\text{only one quadratic character exists}\\
S_3&6&\text{cubic ray layer over }\mathbf Q(\zeta_3)\\
A_4&12&C_3\text{ quotient}\\
S_4&24&S_3\text{ quotient}\\
A_5&60&\text{degree cap }52\\
\operatorname{GL}_2(\mathbf F_3)&48&\text{normal }Q_8\text{ gives }S_3.
\end{array}
$$

The row for $C_3$ deserves its precise wording. A cyclic cubic field can have root discriminant below $3^{3/2}$; it is the cutoff $u>1/2$, not the degree or coarse discriminant, that eliminates it. The $S_3$ row similarly needs the ray conductor over the quadratic field, because $S_3$ itself has no cubic quotient over $\mathbf Q$.

### 11.4 What remains after semisimplification

At this point all residual ambiguity has been removed:

$$
M\simeq k\oplus k(1).
$$

Four questions nevertheless remain at characteristic zero.

1. Can a nontrivial congruence kernel mix the two lines?
2. Can the diagonal characters deform while their product remains $\chi_3$?
3. Can an irreducible representation reduce to this split sum?
4. Can the full torsion tower be placed in the exponent-$3$ Fontaine compositum?

The answer to the fourth is no because of the determinant tower. The answers to the first three are controlled one infinitesimal level at a time. The next two chapters construct each difference cocycle as a finite-flat dual-number representation and use its forbidden cubic ray layer to lift the residual splitting.

## 12. Congruence layers and the pro-$3$ image

### 12.1 The conjugation module

Choose the residual basis in which

$$
\bar\rho_0=
\begin{pmatrix}1&0\\0&\bar\chi_3\end{pmatrix}.
$$

Conjugation on $M_2(k)$ decomposes as

$$
M_2(k)
=kI\oplus kh\oplus ke_{12}\oplus ke_{21},
$$

where

$$
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

The first two lines are trivial $G_{\mathbf Q}$-modules. On both off-diagonal lines the action is cyclotomic:

$$
g(e_{12})=\bar\chi_3(g)^{-1}e_{12}
=\bar\chi_3(g)e_{12},
$$

$$
g(e_{21})=\bar\chi_3(g)e_{21}.
$$

Thus

$$
\operatorname{ad}\bar\rho_0
\simeq k^{\oplus2}\oplus k(1)^{\oplus2},
$$

while

$$
\operatorname{ad}^0\bar\rho_0
\simeq k\oplus k(1)\oplus k(1).
$$

Every congruence kernel $C_n$ embeds in the underlying $\mathbf F_3[G_{\mathbf Q}]$-module of this conjugation module. Its $k$-linear span is a $k[G_{\mathbf Q}]$-submodule and has constituents among the four displayed lines. The kernel itself need not be $k$-linear, as Section 2.3 emphasized. This statement describes the possible ambient constituents; it does not prove that the field cut out by the corresponding cocycle is the field of a finite-flat exponent-$3$ module over $\mathbf Q$.

### 12.2 Fixed determinant and trace-zero layers

For $A\in M_2(k)$,

$$
\det(1+\varpi^nA)
\equiv1+\varpi^n\operatorname{tr}(A)
\pmod{\varpi^{n+1}}.
$$

Hence the kernel of determinant on $C_n$ injects into

$$
\operatorname{ad}^0\bar\rho_0.
$$

Its order is at most

$$
3^{3f}.
$$

The trace quotient is not an error term: it contains the prescribed new layer of the cyclotomic determinant. To classify deformations with determinant fixed as the full character $\chi_3$, compare $\rho$ with the reference representation

$$
\rho_0=1\oplus\chi_3.
$$

Their first nonzero difference has trace zero. This converts the lifting question into cohomology with coefficients in $\operatorname{ad}^0\bar\rho_0$.

The determinant field at level $n$ has degree $2\cdot3^{n-1}$ when $\mathcal O=\mathbf Z_3$. Therefore the exact degree formula has the form

$$
[K_n:\mathbf Q]
=[K_n:D_n]\,2\cdot3^{n-1}.
$$

The relative factor $[K_n:D_n]$ measures special-linear congruence information. It is this factor, not the whole degree, that a fixed-determinant rigidity argument seeks to eliminate.

### 12.3 The cyclotomic direction cannot stabilize

For the reference representation,

$$
K_n(\rho_0)=\mathbf Q(\zeta_{3^n})
$$

when $\mathcal O=\mathbf Z_3$. Hence

$$
K_1(\rho_0)\subsetneq K_2(\rho_0)
\subsetneq\cdots,
$$

and

$$
\operatorname{rd}(K_n(\rho_0))=3^{n-1/2}.
$$

The image has a one-dimensional pro-$3$ part:

$$
\left\{
\begin{pmatrix}1&0\\0&a\end{pmatrix}:
a\in1+3\mathbf Z_3
\right\}.
$$

At each step this direction contributes the exact kernel

$$
\operatorname{Gal}
\bigl(\mathbf Q(\zeta_{3^{n+1}})/
\mathbf Q(\zeta_{3^n})\bigr)
\simeq C_3.
$$

In matrices it is represented modulo $3^{n+1}$ by

$$
1+3^n
\begin{pmatrix}0&0\\0&a\end{pmatrix},
\qquad a\in\mathbf F_3.
$$

Its trace is $a$, so it is precisely the direction removed when one passes from the full congruence module to fixed-determinant error data.

Thus none of the following implications is valid:

$$
\text{finite flat at every level}
\Longrightarrow
\text{bounded root discriminant},
$$

$$
[K_{n+1}:K_n]\leq3^4
\Longrightarrow
\text{stabilization},
$$

$$
\text{all graded constituents are }1\text{ or }\bar\chi_3
\Longrightarrow
\text{all layers descend to exponent }3\text{ over }\mathbf Q.
$$

The cyclotomic representation is a counterexample to all three. Any stabilization theorem used below will explicitly remove or prescribe this direction.

### 12.4 The common-ambient difference module

We now prove the exact descent statement needed for one congruence step using only products, saturated closure, and coefficient quotients.

Let

$$
A'=\mathcal O/\varpi^{n+1},
\qquad
A=\mathcal O/\varpi^n,
\qquad
I=\ker(A'\to A)=\varpi^n\mathcal O/\varpi^{n+1}\mathcal O.
$$

Then $I^2=0$, the maximal ideal of $A'$ kills $I$, and the chosen uniformizer identifies $I$ with $k$. Suppose two global representations

$$
\rho^{(0)},\rho^{(1)}:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(A')
$$

agree over $A$ and each has a finite-flat local model at $3$. Put

$$
B=A'\times_AA'.
$$

Their matrices glue entrywise to a representation on the free $B$-module $B^2$, whose two projections are $\rho^{(0)}$ and $\rho^{(1)}$.

We first construct its integral witness. By §3.1, replace the two supplied witnesses by $A'$-linear ones. Their product is finite flat. The generic embedding

$$
B^2\hookrightarrow (A')^2\oplus(A')^2
$$

identifies $B^2$ with the pairs whose reductions over $A$ agree. Close this generic subgroup inside the product model. Contraction of its generic Hopf ideal gives a torsion-free coordinate quotient, so the closure is finite flat. Every element of $B\subset A'\times A'$ preserves the generic subgroup; the product endomorphism therefore preserves the closure. The ring laws hold generically and hence integrally. We have obtained a $B$-linear finite-flat model of the glued representation. Notice that neither selected branch model was required to reduce to a common integral model.

Now put $D=k[\epsilon]/(\epsilon^2)$. For $(a,b)\in B$, write

$$
b-a=\varpi^n\widetilde d\pmod{\varpi^{n+1}}
$$

and let $d$ be the residue of $\widetilde d$ in $k$. Define

$$
\theta:B\longrightarrow D,
\qquad
\theta(a,b)=\bar a+d\epsilon. \tag{12.1}
$$

This is a surjective ring homomorphism. For multiplication, write $b=a+i$ and $b'=a'+i'$ with $i,i'\in I$. Since $I^2=0$ and $a$ acts on $I$ through $\bar a$, one has

$$
bb'-aa'=ai'+a'i,
$$

which is exactly the dual-number multiplication rule in (12.1). Surjectivity follows from diagonal lifts of $k$ and from the pairs $(0,\varpi^n\widetilde d)$.

Close the generic subgroup cut out by $\ker\theta$ in the $B$-linear model and take the represented quotient, as in §3.1. This gives a $D$-linear finite-flat model of

$$
D\otimes_BB^2.
$$

Suppose, in a common residual basis, that

$$
\rho^{(1)}(g)
=\bigl(1+\varpi^nc(g)\bigr)\rho^{(0)}(g)
\pmod{\varpi^{n+1}}.
$$

Taking the first coordinate of $B$ to be $\rho^{(0)}$ and the second to be $\rho^{(1)}$, the quotient representation is

$$
\rho_c(g)=
\bigl(1+\epsilon c(g)\bigr)\bar\rho^{(0)}(g)
\quad\text{on }D^2. \tag{12.2}
$$

Its homomorphism law is precisely the cocycle identity. Since $D$ has characteristic $3$, its underlying finite-flat group is killed by $3$. Therefore the affine field $E(c)$ fixed by the kernel of (12.2) satisfies the residual upper-break cutoff at $3$.

The full Galois group is retained in (12.2):

$$
g\longmapsto
\bigl(c(g),\bar\rho^{(0)}(g)\bigr)
\in
\operatorname{ad}\bar\rho^{(0)}
\rtimes\operatorname{im}\bar\rho^{(0)}.
$$

Thus the zero set of $c$ is never mistaken for a normal subgroup by itself. Over $K_1=\mathbf Q(\zeta_3)$, when $\bar\rho^{(0)}=1\oplus\bar\chi_3$, the residual conjugation action is trivial and

$$
\operatorname{Gal}(E(c)/K_1)
\subseteq\operatorname{ad}^0\bar\rho_0
$$

is elementary abelian of order at most $3^{3f}$ for a trace-zero cocycle. This is the fixed-base exponent-three object required in Chapter 13, now constructed rather than assumed.

### 12.5 The Lie-algebra conclusion

Let $\Gamma$ be the compact image of $\rho$ and let $\mathfrak g$ be its $E$-Lie algebra. The differential of determinant is trace:

$$
d(\det):\mathfrak g\longrightarrow E,
\qquad X\longmapsto\operatorname{tr}X.
$$

Because $\det\rho=\chi_3$ has open pro-$3$ image, the trace map has nonzero image. Chapter 13 proves that every trace-zero affine difference module constructed in §12.4 is trivial in cohomology. Hence the trace-zero congruence image vanishes at every depth, and therefore

$$
\ker(\operatorname{tr}|_{\mathfrak g})=0,
\qquad
\dim_E\mathfrak g=1.
$$

The passage from fields to this statement can be written entirely in the congruence filtration. Put

$$
\Gamma_m=\Gamma\cap(1+\varpi^mM_2(\mathcal O)).
$$

For sufficiently large $m$, the logarithm is a homeomorphism from $\Gamma_m$ onto a closed additive subgroup of $\varpi^mM_2(\mathcal O)$, and

$$
\mathfrak g
=E\cdot\log(\Gamma_m).
$$

The level field ceases to grow in a direction precisely when the corresponding quotient of $\Gamma_m/\Gamma_{m+1}$ vanishes at every deeper level. If all directions cease, then $\Gamma_m=1$ and the whole image is finite. Here only the fixed-determinant error directions cease, so

$$
\log(\Gamma_m)\cap\mathfrak{sl}_2(E)=0.
$$

This is the asserted injectivity of trace on $\mathfrak g$. The remaining line maps isomorphically under trace to the Lie algebra of $\chi_3(G_{\mathbf Q})$. Thus the strict affine-cocycle vanishing leaves exactly one infinitesimal direction, not an unspecified finite-index subgroup of $\operatorname{GL}_2(\mathcal O)$.

After the invariant-line lifting of the next chapter, a basis identifies

$$
\boxed{
\mathfrak g
=E\begin{pmatrix}0&0\\0&1\end{pmatrix}.
}
$$

The Lie-algebra statement alone would not construct an invariant line. The level-by-level coboundaries of Chapter 13 do: their convergent conjugations identify the entire representation, not merely its infinitesimal image.

## 13. Lifting residual lines

### 13.1 Why a residual line is not enough

Let

$$
\bar L\subset T/\varpi T
$$

be the trivial residual line. Its inverse image in $T/\varpi^2T$ is not automatically stable, and a stable lift need not exist. If it exists at one level, it need not be compatible with a choice at the next. The obstruction is cohomological.

There is also lattice dependence. Before Theorem 10.1, different stable lattices could have produced opposite nonsplit residual extensions. Theorem 10.1 and the affine ray-class argument of Chapter 8 show that every lattice satisfying the strict level-one condition reduces as the same split module. This removes the first ambiguity, but it does not yet construct an invariant $\mathcal O$-line.

We solve the problem by comparing the entire representation with

$$
\rho_0=\begin{pmatrix}1&0\\0&\chi_3\end{pmatrix}
$$

one infinitesimal level at a time.

### 13.2 The obstruction at one infinitesimal step

Suppose that, after conjugation by an element of $\operatorname{GL}_2(\mathcal O)$, one has

$$
\rho\equiv\rho_0\pmod{\varpi^n}.
$$

Write modulo $\varpi^{n+1}$

$$
\rho(g)
=\bigl(1+\varpi^n c_n(g)\bigr)\rho_0(g),
\qquad c_n(g)\in M_2(k).
$$

The homomorphism law gives

$$
c_n(gh)=c_n(g)
+\bar\rho_0(g)c_n(h)\bar\rho_0(g)^{-1}.
$$

Thus $c_n$ is a $1$-cocycle in $\operatorname{ad}\bar\rho_0$. Equality of determinants gives

$$
\operatorname{tr}c_n(g)=0,
$$

so

$$
[c_n]\in H^1(\mathbf Q,\operatorname{ad}^0\bar\rho_0).
$$

Conjugating by $1+\varpi^nX$ changes $c_n$ by the coboundary of $X$. Hence the obstruction to improving the congruence from level $n$ to level $n+1$ is exactly the cohomology class $[c_n]$.

Because both representations are unramified away from $3$, the class is unramified there. Its integral local property will not be inferred from an isomorphism of selected models. Section 12.4 instead constructs a new finite-flat dual-number model whose generic representation records exactly $c_n$.

### 13.3 The global affine-cocycle rigidity lemma

The field calculation needed at every step is independent of a decomposition into diagonal and off-diagonal tangent directions.

**Lemma 13.1 (affine-cocycle rigidity).** Let

$$
c\in Z^1\left(G_{\mathbf Q,\{3,\infty\}},
\operatorname{ad}^0\bar\rho_0\right),
\qquad
\bar\rho_0=1\oplus\bar\chi_3.
$$

Suppose the dual-number representation

$$
\rho_c(g)=
\bigl(1+\epsilon c(g)\bigr)\bar\rho_0(g)
\quad\text{on }(k[\epsilon]/\epsilon^2)^2
$$

has a finite-flat model over $\mathbf Z_3$. Then $[c]=0$.

**Proof.** Put $K=\mathbf Q(\zeta_3)$. The action of $G_K$ on $\operatorname{ad}^0\bar\rho_0$ is trivial. Inflation--restriction gives

$$
0\longrightarrow
H^1\left(C_2,(\operatorname{ad}^0\bar\rho_0)^{G_K}\right)
\longrightarrow
H^1\left(G_{\mathbf Q,\{3,\infty\}},
\operatorname{ad}^0\bar\rho_0\right)
\longrightarrow
H^1\left(G_{K,\{\lambda\}},
\operatorname{ad}^0\bar\rho_0\right).
$$

The left group is zero because multiplication by $2$ is invertible on a characteristic-three vector space. Hence a nonzero class restricts to a nonzero homomorphism

$$
G_{K,\{\lambda\}}\longrightarrow
(\operatorname{ad}^0\bar\rho_0,+).
$$

Let $E(c)$ be the field cut out by $\rho_c$. It contains $K$, and

$$
\operatorname{Gal}(E(c)/K)
=\operatorname{im}(c|_{G_K})
$$

is elementary abelian of exponent three. If it is nonzero, choose a codimension-one subgroup of its image. The corresponding subfield $F/K$ is cyclic of degree three and unramified away from $\lambda$.

The ring $k[\epsilon]/\epsilon^2$ has characteristic three, so multiplication by $3$ vanishes on the generic module. It also vanishes on any finite-flat model: the two integral endomorphisms $[3]$ and $0$ agree generically, and flatness makes generic restriction faithful. Its cutout field has no upper ramification over $\mathbf Q_3$ above $1/2$. On the other hand, $K$ has class number one and the ray groups of moduli $\lambda$ and $\lambda^2$ are trivial. Thus a nontrivial cyclic cubic $F/K$ supported at $\lambda$ has conductor at least $\lambda^3$ and upper break at least $2$ over $K_\lambda$. Herbrand's subgroup rule for the tame quadratic base change says that the ambient cutoff $1/2$ becomes a cutoff $1$ over $K_\lambda$. A quotient with break at least $2$ is impossible. Therefore the restriction of $[c]$ is zero, and injectivity makes $[c]=0$. $\square$

The lemma simultaneously removes the diagonal, both off-diagonal, and mixed irreducible first-order directions. It uses only the field of the whole affine representation; no projector onto a putative local tangent summand is needed.

### 13.4 Why every obstruction is a finite-flat difference

Return to $c_n$ from §13.2. Set

$$
A'=\mathcal O/\varpi^{n+1},
\qquad A=\mathcal O/\varpi^n.
$$

After the current integral conjugation, $\rho$ and $\rho_0$ give two $A'$-valued representations with identical reduction over $A$. The first has a finite-flat local witness by the strict levelwise hypothesis; conjugating its generic identification does not change that fact. The second has the explicit split witness of §3.2.

Apply the common-ambient construction of §12.4. It first closes their $B=A'\times_AA'$ fiber product in the product of coefficient-enhanced witnesses and then takes the coefficient quotient

$$
B\twoheadrightarrow k[\epsilon]/\epsilon^2.
$$

The resulting finite-flat representation is exactly

$$
g\longmapsto
\bigl(1+\epsilon c_n(g)\bigr)\bar\rho_0(g).
$$

This proves the hypothesis of Lemma 13.1. Consequently

$$
\boxed{[c_n]=0}
$$

at every level. Existence of the two branch models, exactness of saturated closure, and the coefficient quotient have each been used explicitly. No compatible choice of the original levelwise models, no extension of a generic comparison to those selected models, and no inverse limit of group schemes occurs.

### 13.5 Inductive lifting and conjugacy

**Theorem 13.2 (lifting the residual splitting).** Let $\rho$ be a strict hardly ramified datum. Then there is an element $U\in\operatorname{GL}_2(\mathcal O)$ such that

$$
U\rho U^{-1}
=\begin{pmatrix}1&0\\0&\chi_3\end{pmatrix}.
$$

**Proof.** The residual theorem supplies a basis with $\rho\equiv\rho_0\pmod\varpi$. Assume inductively that the congruence holds modulo $\varpi^n$. Section 13.2 produces the obstruction class $[c_n]$, and §13.4 makes it zero. Thus there is $X_n\in M_2(k)$ whose coboundary is $c_n$. Lift $X_n$ to $M_2(\mathcal O)$ and conjugate by $1+\varpi^nX_n$. The congruence improves modulo $\varpi^{n+1}$.

The infinite product of the successive conjugating matrices converges $\varpi$-adically to an element $U\in\operatorname{GL}_2(\mathcal O)$. Continuity gives $U\rho U^{-1}=\rho_0$. $\square$

The limiting operation occurs in the complete matrix ring $M_2(\mathcal O)$, equivalently in the inverse limit of the finite modules $T/\varpi^nT$. No inverse limit of the selected finite-flat group schemes is taken. The argument proves an actual splitting, not merely equality of characteristic-zero semisimplifications. Semisimplicity is therefore unnecessary for this strict conclusion, although it remains part of the standard compatible-system input and is useful when only Frobenius data are being compared.

### 13.6 Dependence on the stable lattice

The residual semisimplification is independent of the stable lattice. A full residual extension usually is not. In the strict category the arithmetic vanishing removes this dependence as follows.

Let $T'$ be another stable lattice whose quotients have finite-flat models at every level. Its residual semisimplification is again $1\oplus\bar\chi_3$. The affine ray-class calculation makes the actual reduction split. Applying Theorem 13.2 to $T'$ gives the same rational representation

$$
1\oplus\chi_3.
$$

The two lattices need not be homothetic: the split rational representation admits lattices obtained by rescaling its two direct summands independently. What is forced is the rational invariant-line decomposition and, for every lattice satisfying the strict levelwise existence condition, a split residual module.

If a finite-flat model is absent at some level, this argument stops because the dual-number difference need not be finite flat. Incompatible choices of witnesses create no obstruction here: the common-ambient construction deliberately replaces them by a new witness. Residual reducibility alone never supplies Theorem 13.2.

## 14. Characteristic-zero alternatives

### 14.1 Reducible representations

Suppose $V$ has a $G_{\mathbf Q}$-stable $E$-line $W$. Intersecting with $T$ and saturating gives a stable rank-one lattice. At each finite level its generic submodule can be closed inside a separately chosen finite-flat witness, producing a finite-flat subquotient. This is a levelwise statement and requires no comparison between the witnesses.

For the strict datum there is no need to classify that rank-one model. Theorem 13.2 has already compared the whole representation with the explicit split reference at every coefficient level and gives

$$
\rho\simeq1\oplus\chi_3.
$$

This stronger route also controls a nonsemisimple extension. If only characteristic-zero reducibility and semisimplicity were assumed, without finite-flat models for all lattice quotients, the stable line would exist but the affine-cocycle argument would be unavailable; neither of its two characters should then be identified from the strict theorem.

### 14.2 Potentially reducible representations

A semisimple two-dimensional representation is **potentially reducible** if its restriction to $G_M$ is reducible for some finite extension $M/\mathbf Q$. Suppose it is irreducible over $\mathbf Q$, replace $M$ by a finite Galois extension over which the restriction is reducible, and apply Clifford theory to an irreducible constituent of that restriction. There are two cases.

If the two constituents are distinct, the orbit of either line has two elements. Its stabilizer has index two, so there is a quadratic field $M_0$ and a character $\theta$ of $G_{M_0}$ with

$$
\rho\simeq\operatorname{Ind}_{G_{M_0}}^{G_{\mathbf Q}}\theta.
$$

The projective image is dihedral, possibly infinite in characteristic zero. There are two residual possibilities.

If $\bar\theta\ne\bar\theta^\sigma$, the residual projective image remains dihedral. Chapter 9 excludes it under the strict local conditions. If

$$
\bar\theta=\bar\theta^\sigma,
$$

the residual induction becomes reducible after semisimplification. The residual theorem makes it $1\oplus\bar\chi_3$, and Theorem 13.2 makes the characteristic-zero lift itself $1\oplus\chi_3$, contradicting irreducibility.

If instead the restriction is isotypic, the normal subgroup acts through one scalar character and the projective representation factors through a finite quotient. This finite-projective branch is not dihedral merely by Clifford theory and must be kept separate from quadratic induction. In the strict problem Theorem 13.2 excludes it together with every other irreducible lift. Under weakened hypotheses one must record either the quadratic induction, together with its inducing field, character ratio, conductor, and behavior at $3$, or the finite projective image and its central lift. Calling both branches merely “small image” loses the datum that decides them.

Thus a strict datum has no irreducible potentially reducible branch, but the conclusion uses the two-case Clifford analysis rather than the false assertion that every potentially reducible irreducible representation is dihedral.

### 14.3 Finite image

The full image of a strict datum is never finite, because

$$
\det\rho(G_{\mathbf Q})=\chi_3(G_{\mathbf Q})
=\mathbf Z_3^\times
$$

is infinite. A finite residual image is of course automatic; it is the image on $T/\varpi T$ and should not be confused with the characteristic-zero image.

Finite full image and finite projective image are also different. An infinite scalar character can sit above a finite projective quotient. The determinant rules out finite full image here, but it does not by itself rule out the finite-projective Clifford branch of Section 14.2. In the strict datum that branch is eliminated by the line-lifting theorem; in a weakened problem its projective group and central extension require a separate classification.

If a different problem has finite determinant and its full torsion-field tower lies in a Fontaine compositum satisfying the strict analytic inequality, stabilization makes its image finite. One must then classify finite subgroups of $\operatorname{GL}_2(E)$ separately. In the present cyclotomic-determinant problem, stabilization can apply only to the trace-zero error image. It leaves the one-dimensional cyclotomic torus intact.

### 14.4 Semisimplification $1\oplus\chi_3$

There are three levels at which this expression occurs:

$$
\bar\rho^{\mathrm{ss}}\simeq1\oplus\bar\chi_3,
$$

$$
\rho^{\mathrm{ss}}\simeq1\oplus\chi_3,
$$

and

$$
\rho\simeq1\oplus\chi_3.
$$

The first follows from character fields once projective irreducibility is excluded. Proposition 8.1 removes residual extension ambiguity. The second follows from a characteristic-zero invariant line plus semisimplicity. The third follows in the strict datum from the obstruction calculation, without needing semisimplicity.

Outside the strict datum, only the conclusion justified by the available hypotheses may be retained. In particular:

- residual reducibility alone gives only the first line;
- a lifted line plus characteristic-zero semisimplicity gives the second;
- finite-flat witnesses at every level plus affine-cocycle rigidity give the third.

The exact prime-$2$ datum is the additional case proved in Chapter 18. Its finite-flat
devissage gives an integral cyclotomic line with trivial quotient and hence the second line;
the integral extension can be the Kummer class $b[2]$. Semisimplicity then makes it split. Thus
the phrase ``outside the strict datum'' is not a claim that controlled ramification can never
be treated; it says that its local category must first be calculated.

### 14.5 Purity as the final incompatibility

Let $\rho$ be a member of a pure compatible system of weight one. At every good prime $p\ne3$, the roots of its Frobenius polynomial have complex absolute value

$$
\sqrt p.
$$

For $1\oplus\chi_3$, the polynomial is

$$
(X-1)(X-p)=X^2-(p+1)X+p.
$$

Its roots have absolute values $1$ and $p$, not $\sqrt p$. Equivalently,

$$
p+1>2\sqrt p
$$

for every prime $p$, because

$$
p+1-2\sqrt p=(\sqrt p-1)^2>0.
$$

Thus a pure weight-one compatible system cannot have a semisimple member $1\oplus\chi_3$. This is the final contradiction needed in the Frey interface. It uses the common algebraic Frobenius polynomials, so it is independent of the coefficient embedding chosen at $3$.

## 15. Solvable layers and small-degree fields

### 15.1 Abelian quotients

Let $L/\mathbf Q$ be a finite Galois subextension of the strict residual field. Every abelian quotient of $\operatorname{Gal}(L/\mathbf Q)$ cuts out an abelian field that is unramified away from $3$ and has local upper cutoff $1/2$. The complete list is

$$
\mathbf Q,
\qquad
\mathbf Q(\zeta_3).
$$

Therefore

$$
|\operatorname{Gal}(L/\mathbf Q)^{\mathrm{ab}}|\leq2.
$$

This does not force the whole group to have order at most two: $A_5$ is perfect, and $S_3$ has abelianization $C_2$. The assertion becomes powerful only when combined with a normal series or a degree bound.

For a finite $2$-group, it is already decisive. A finite $2$-group with cyclic abelianization is cyclic, because its minimal number of generators is the dimension of its Frattini quotient. Since no cyclic quartic extension is supported only at $3$, a strict $2$-extension has degree at most two. This is another route to the exclusion of the Cartan normalizers over $\mathbf F_3$.

### 15.2 Cubic layers

There are two cubic configurations.

A Galois cubic extension has group $C_3$. If it were unramified at $3$, it would be unramified at every finite prime and hence trivial. It must therefore be wildly ramified at $3$, and Hasse--Arf gives an integral upper break at least one. This exceeds the strict cutoff.

A non-Galois cubic field has normal closure with group $S_3$. If that normal closure lies in the strict residual field, its quadratic resolvent is $\mathbf Q(\zeta_3)$ and its cyclic cubic layer over the resolvent has ray conductor at least $\lambda^3$. The lower-base break is at least one. It too is excluded.

These arguments distinguish the two directions of Galois correspondence. A $C_3$ quotient of a Galois group produces a Galois cubic field over $\mathbf Q$. An index-three subgroup need not be normal and produces a non-Galois cubic field; its normal closure and quadratic resolvent must then be retained.

### 15.3 Quartic layers

The transitive Galois groups of normal closures of quartic fields are

$$
C_4,\quad V_4,\quad D_8,\quad A_4,\quad S_4.
$$

Each exposes one of the preceding obstructions.

- $C_4$ and $V_4$ are forbidden abelian quotients.
- $D_8$, the dihedral group of order eight, has abelianization $V_4$ and would produce too many quadratic fields.
- $A_4$ has quotient $C_3$ by its normal $V_4$.
- $S_4$ has quotient $S_3$ by its normal $V_4$.

Thus no quartic field can have its normal closure inside a strict residual field unless its action has already collapsed to degree at most two. This finite ledger is the field-theoretic shadow of the Cartan and exceptional subgroup analysis.

### 15.4 Unramified layers

Neither $\mathbf Q$ nor $K=\mathbf Q(\zeta_3)$ has a nontrivial unramified abelian extension: both have class number one. In fact neither base has a nontrivial finite solvable Galois extension unramified at all finite primes. If $G$ were the nontrivial solvable Galois group of such an extension, then its commutator subgroup would be proper and

$$
G^{\mathrm{ab}}=G/[G,G]
$$

would give a nontrivial unramified abelian subextension of the original base. This contradicts class number one.

For a $3$-group the reasoning is especially direct. Every nontrivial finite $3$-group has a nontrivial $C_3$ quotient. If a purported unramified $3$-layer existed over $\mathbf Q$ or $K$, it would yield an unramified cyclic cubic extension, contradicting class number one.

One should not globalize this sentence to arbitrary intermediate fields. A field of small root discriminant can have a nontrivial class group, and an unramified extension preserves its root discriminant. If a derived series reaches a new intermediate base, the class group of that actual base must be known before the next abelian layer is removed.

### 15.5 A solvable-tower elimination protocol

Let

$$
1=G_r\triangleleft G_{r-1}\triangleleft\cdots
\triangleleft G_0=G
$$

be a normal series with abelian factors. To eliminate a solvable candidate $G$:

1. translate every quotient $G_i/G_{i+1}$ into the corresponding abelian extension of the fixed field of $G_i$;
2. determine whether the relevant base is $\mathbf Q$, $\mathbf Q(\zeta_3)$, or a new intermediate field;
3. transport upper breaks correctly through tame base change and through Galois quotients;
4. compute the ray modulus or class group at that base;
5. compare the resulting conductor with the inherited cutoff;
6. retain the scalar and determinant subfields when returning to the matrix image.

The method is deliberately field by field. A bounded root discriminant does not make every derived layer trivial, and an abelianization calculation over $\mathbf Q$ does not automatically calculate class groups over intermediate fields.

## 16. Four hostile diagnostics

The preceding proof is compact only because several independent restrictions meet at the same point. This chapter runs four candidates through the argument without suppressing any degree, scalar, determinant, or local-conductor contribution. The purpose is diagnostic: each case reveals a shortcut that would give the wrong answer.

### 16.1 Full image over $\mathbf F_3$

Suppose first that

$$
\overline\rho(G_{\mathbf Q})=\operatorname{GL}_2(\mathbf F_3).
$$

The residual field $L=L_1$ then has degree

$$
[L:\mathbf Q]=|\operatorname{GL}_2(\mathbf F_3)|
=(3^2-1)(3^2-3)=8\cdot6=48.
$$

Its scalar center is $Z=\{\pm I\}$, its determinant kernel is

$$
\operatorname{SL}_2(\mathbf F_3),
\qquad |\operatorname{SL}_2(\mathbf F_3)|=24,
$$

and its projective quotient is

$$
\operatorname{PGL}_2(\mathbf F_3)\simeq S_4,
\qquad |S_4|=24.
$$

These two order-$24$ groups are not the same quotient. The first is a subgroup and the second is the quotient by scalar matrices. The determinant field is

$$
K=L^{\operatorname{SL}_2(\mathbf F_3)}=\mathbf Q(\zeta_3),
$$

whereas the projective field is

$$
P=L^Z,
\qquad [P:\mathbf Q]=24.
$$

The strict finite-flat bound gives

$$
\operatorname{rd}(L)<3^{3/2}=5.1961524227\ldots .
$$

The full global image does not determine the local decomposition group at $3$, so it would be false precision to assign one ramification index. The exact local ledger is instead

$$
e_3\mid48,
\qquad
d_3\leq\frac{3e_3}{2}-1,
\qquad
\frac{d_3}{e_3}<\frac32,
$$

with $d_p=0$ for every $p\neq3$. The determinant quotient forces the local field to contain $\mathbf Q_3(\zeta_3)$, so the inertia image has an order-two quotient, but it need not equal the whole global group. These statements are exactly what is justified without choosing a local inertia shape.

The unconditional degree cap $[L:\mathbf Q]\leq52$ therefore does not exclude $L$: degree $48$ is below the cap. The group must be opened.

Inside $\operatorname{GL}_2(\mathbf F_3)$ lies the normal quaternion subgroup

$$
Q_8\triangleleft\operatorname{GL}_2(\mathbf F_3),
\qquad
\operatorname{GL}_2(\mathbf F_3)/Q_8\simeq S_3.
$$

Consequently

$$
E=L^{Q_8},
\qquad [E:\mathbf Q]=6,
$$

is an $S_3$-extension. The sign quotient of this $S_3$ is the determinant quotient, so its quadratic field is $K$. Thus

$$
[E:K]=3.
$$

The extension $E/K$ is cyclic cubic. At the unique prime $\lambda$ above $3$, the first nontrivial cubic ray quotient of $K$ occurs at modulus $\lambda^3$. A character of conductor exponent three has upper break two over $K_\lambda$. Because $K_\lambda/\mathbf Q_3$ is tame of ramification index two, this becomes upper break one over $\mathbf Q_3$. That is strictly larger than the permitted cutoff $1/2$. Hence $E$ cannot occur, and the full residual image is impossible.

The calibrating first ray field is $\mathbf Q(\zeta_9)/K$, whose upper break is indeed two over $K_\lambda$ and whose Galois closure over $\mathbf Q$ has

$$
\operatorname{rd}\bigl(\mathbf Q(\zeta_9)\bigr)=3^{3/2}.
$$

It is not the proposed $S_3$ field: $\mathbf Q(\zeta_9)/\mathbf Q$ is abelian. It records the first conductor at which any cubic ray character can appear. A proposed $S_3$ layer has at least that conductor and is already excluded by the upper-break comparison.

This calculation uses all three checks. The Odlyzko degree comparison narrows the problem but does not finish it; the projective quotient exposes the $S_3$ field; and the strict upper-break cutoff removes the cubic ray layer.

### 16.2 A Borel image

Let $B$ be the upper triangular Borel in $\operatorname{GL}_2(\mathbf F_3)$. Its order is

$$
|B|=3(3-1)^2=12.
$$

The unipotent radical

$$
U=\left\{
\begin{pmatrix}1&u\\0&1\end{pmatrix}:u\in\mathbf F_3
\right\}
$$

has order three, and $B/U\simeq C_2\times C_2$. A careless Borel argument would now allow four diagonal characters. Global character classification does not. Since both diagonal characters are unramified away from $3$ and finite flat at $3$, and their product is $\overline\chi_3$, their unordered pair is

$$
\{1,\overline\chi_3\}.
$$

The diagonal image therefore has order at most two. The actual residual image inside $B$ has order at most six, not twelve. If its unipotent part is nontrivial, it is the semidirect product

$$
C_3\rtimes C_2\simeq S_3,
$$

because conjugation by $\operatorname{diag}(1,-1)$ inverts $U$.

Let $L$ be the field of this order-six image. Its determinant field is again $K=\mathbf Q(\zeta_3)$ and $L/K$ is cyclic cubic. Because the whole residual module has a finite-flat model killed by $3$, the local field $L_w/\mathbf Q_3$ has upper break at most $1/2$. But every nontrivial cyclic cubic extension of $K$ supported at $\lambda$ has conductor at least $\lambda^3$, hence break at least two over $K_\lambda$ and at least one over $\mathbf Q_3$. This contradiction is independent of the triangular orientation. Thus the unipotent radical disappears and the image is precisely the determinant group of order at most two. The result is the actual split representation

$$
\overline\rho\simeq1\oplus\overline\chi_3,
$$

not merely its semisimplification.

### 16.3 A dihedral projective image

Assume that the projective image is dihedral. There is then a quadratic character

$$
\epsilon:G_{\mathbf Q}\longrightarrow\{\pm1\}
$$

whose kernel fixes the Cartan. In the strict problem the only such character is $\overline\chi_3$, so the quadratic field is $K=\mathbf Q(\zeta_3)$. Over $G_K$ the projective representation is cyclic.

For the split Cartan in $\operatorname{GL}_2(\mathbf F_3)$ the relevant orders are

$$
|C_s|=4,
\qquad |N_s|=8,
\qquad |\mathbf P C_s|=2,
\qquad |\mathbf P N_s|=4.
$$

For the nonsplit Cartan they are

$$
|C_{ns}|=8,
\qquad |N_{ns}|=16,
\qquad |\mathbf P C_{ns}|=4,
\qquad |\mathbf P N_{ns}|=8.
$$

The projective orders divide by the scalar center of order two. In particular, projective order eight does not mean that the linear field has degree eight; the nonsplit normalizer can give degree sixteen.

The projective rotation subgroup over $K$ is cyclic of order prime to $3$, by the degree-capped subgroup theorem. In the displayed $\mathbf F_3$ normalizers it is a $2$-group, so a nontrivial rotation layer would in particular give a quadratic or quartic extension of $K$ supported only at $\lambda$. More generally, the class number of $K$ is one, the ray group of modulus $\lambda$ is trivial, and every higher ray group supported at $\lambda$ has $3$-power order. A cyclic rotation extension whose degree is prime to $3$ is therefore trivial for every residue degree. Thus the rotation subgroup is scalar. The projective image has order at most two, and the representation is reducible after the preceding character calculation.

This is stronger than saying that the projective representation becomes reducible over a quadratic field. It says that the purported dihedral rotation field itself collapses. Without that last step, one would have proved only potential reducibility.

### 16.4 Coefficient residue degree two

Now let the residue field be $k=\mathbf F_9$. The ambient orders are

$$
|\operatorname{GL}_2(\mathbf F_9)|
=9(9-1)^2(9+1)=5760,
$$

$$
|\operatorname{SL}_2(\mathbf F_9)|
=9(9^2-1)=720,
$$

$$
|\operatorname{PGL}_2(\mathbf F_9)|=720,
\qquad
|\operatorname{PSL}_2(\mathbf F_9)|=360.
$$

The center has order eight. But the determinant of the arithmetic representation lands in

$$
\mathbf F_3^\times=\{\pm1\}\subset\mathbf F_9^\times.
$$

Therefore full $\operatorname{GL}_2(\mathbf F_9)$ is incompatible with the determinant before any discriminant estimate is made. The largest determinant-compatible ambient group is

$$
G^{\det\in\mathbf F_3^\times}
=\{g\in\operatorname{GL}_2(\mathbf F_9):\det(g)\in\mathbf F_3^\times\},
$$

and

$$
|G^{\det\in\mathbf F_3^\times}|
=2|\operatorname{SL}_2(\mathbf F_9)|=1440.
$$

The determinant-compatible subgroup orders in the standard geometric families are as follows.

| Family | Full order | Determinant-compatible order | Maximal compatible projective order |
|---|---:|---:|---:|
| scalar center | $8$ | $4$ | $1$ |
| split Cartan | $64$ | $16$ | $4$ |
| split normalizer | $128$ | $32$ | $8$ |
| nonsplit Cartan | $80$ | $20$ | $5$ |
| nonsplit normalizer | $160$ | $40$ | $10$ |
| Borel | $576$ | $144$ | $36$ |
| determinant-compatible ambient group | $5760$ | $1440$ | $360$ |

For example, the determinant on a nonsplit Cartan is the norm

$$
\mathbf F_{81}^\times\longrightarrow\mathbf F_9^\times.
$$

The inverse image of the two-element subgroup $\mathbf F_3^\times$ has order

$$
(9+1)\cdot2=20,
$$

which explains the nonsplit entry. In the split Cartan, for each of the two allowed determinant values there are eight choices for the first diagonal entry, giving $16$.

The projective column divides by the compatible scalar subgroup

$$
Z^\chi=\{aI:a^2\in\mathbf F_3^\times\},
\qquad |Z^\chi|=4.
$$

This is also where the determinant and projective fields separate more sharply than over $\mathbf F_3$. The two scalars satisfying $a^2=-1$ have determinant $-1$, so the determinant character need not factor through the projective quotient. A projective-field degree calculation can therefore erase the quadratic determinant field if the scalar kernel is not retained.

For the maximal groups in the table this entire subgroup is present. An actual subgroup may meet $Z^\chi$ in a smaller group, so its projective degree must still be computed from the intersection rather than obtained by automatic division by four.

The unconditional degree cap immediately excludes images whose actual order exceeds $52$. It does not exclude the compatible split normalizer of order $32$ or the nonsplit normalizer of order $40$. Nor may one replace their linear orders by their projective orders: the compatible scalar subgroup has order four. These remaining candidates are removed by the quadratic-character and ray-class arguments, which do not require $k=\mathbf F_3$. Once their cyclic Cartan layer is restricted to $G_K$, its unramified part is killed by the class number, its tame prime-to-three part by the trivial ray group of modulus $\lambda$, and any wild ray quotient allowed by larger conductors has $3$-power order, whereas the projective Cartan order is prime to $3$. The only surviving characters take values in $\mathbf F_3^\times$, and the representation descends to the split pair

$$
1\oplus\overline\chi_3.
$$

There are also proper Borel subgroups below the degree cap. Once the two diagonal characters have been restricted to $1$ and $\overline\chi_3$, their diagonal quotient has order two and their unipotent radical is an $\mathbf F_3$-subspace of the additive group of $\mathbf F_9$. Its order can be $1$, $3$, or $9$, so the corresponding matrix image has order $2$, $6$, or $18$. The last two possibilities are not excluded by degree. Any nonzero additive image has a $C_3$ quotient over $K$, and the same ray-class break argument excludes it. This is why the residue-degree-two audit needs both the group ledger and the affine extension field.

Thus coefficient residue degree two changes the finite-group ledger substantially but not the strict conclusion. It would be an error to run the $48$-element calculation and call it a calculation in $\operatorname{GL}_2(\mathbf F_9)$.

## 17. Boundaries and failure modes

The strict theorem and the exact prime-$2$ theorem have different local hypotheses. Each
hypothesis removes a concrete obstruction. Weakening either package should therefore be
accompanied by a new calculation, not by an appeal to the same conclusion.

### 17.1 An additional ramified prime

Let $S=\{3,q\}$ with $q\neq3$. The global Kummer group now contains the class of $q$. It is represented by a $3$-adic unit, so the local finite-flat unit condition at $3$ need not kill it. The associated extension class is unramified outside $\{3,q\}$ and can be ramified at $q$. Thus the vanishing

$$
H^1_{\mathrm{ff},\{3\}}(\mathbf Q,\mathbf F_3(1))=0
$$

does not imply the analogous vanishing with $q$ allowed.

This is not merely a possible defect in the proof. Let $c_q$ be the Kummer cocycle of $q$ and form

$$
\overline\rho_q(g)=
\begin{pmatrix}
\overline\chi_3(g)&c_q(g)\\
0&1
\end{pmatrix}.
$$

Its determinant is $\overline\chi_3$, it is odd, and its local class at $3$ is a unit class. Concretely, the flat Kummer sequence over $\mathbf Z_3$ sends $q\in\mathbf Z_3^\times$ to an extension of the constant group of order three by $\mu_3$ whose generic points give this local representation. Thus it has the required finite-flat model. At $q$ its tame unipotent inertia has order three. For $q$ not a rational cube, the full field is

$$
\mathbf Q(\zeta_3,\sqrt[3]{q}),
$$

with Galois group $S_3$ in the generic case. Its exact tame normalized different contribution at $q$ is $2/3$. Thus allowing one prime changes both the extension Selmer group and the finite group ledger in a visible example.

For a finite auxiliary set $S_0$ disjoint from $3$, the calculation is completely explicit over $\mathbf Q$. Since $\mathbf Z[1/S_0]$ has trivial ideal class group,

$$
H^1_{\mathrm{ff},S_0}(\mathbf Q,k(1))
\simeq
\left(
\mathbf Z[1/S_0]^\times/
\mathbf Z[1/S_0]^{\times3}
\right)\otimes_{\mathbf F_3}k.
$$

The sign $-1$ is a cube, and the primes in $S_0$ give independent generators. Therefore

$$
\dim_kH^1_{\mathrm{ff},S_0}(\mathbf Q,k(1))
=|S_0|.
$$

The zero-dimensional strict calculation is the case $S_0=\varnothing$. This formula explains exactly why each permitted prime creates an ordinary extension direction unless a further local condition at that prime removes it.

The root-discriminant bound also acquires a factor at $q$. If $d_q/e_q$ is the normalized different contribution at $q$, then

$$
\operatorname{rd}(L)
<3^{3/2}q^{d_q/e_q}.
$$

Even a tame contribution can move the bound beyond the useful unconditional threshold. New quadratic characters, dihedral fields, and ray-class layers may appear. An extra prime therefore requires both a new global Selmer computation and a new numerical discriminant comparison.

For $q=2$ in the Kummer example, the exact tame factor is $2^{2/3}$, so

$$
U(\{2\})=3^{3/2}2^{2/3}
=8.2483778219\ldots
<4\pi e^\gamma.
$$

The analytic theorem still bounds the degree, but the nonsplit $S_3$ representation actually
exists. A discriminant comparison alone therefore cannot prove splitting. Chapter 18 performs
the extra calculation specific to $q=2$: the degree is at most $20$, the simple factors are
constant or multiplicative, the surviving residual class is exactly $a[2]$, and finite-level
devissage lifts its cyclotomic line. Thus $q=2$ with the exact local sequence is completely
resolved, while an arbitrary additional prime without such a sequence remains within the
general controlled-set boundary.

### 17.2 Absence of levelwise finite-flat models

Separately existing finite-flat models of all the quotients $T/\varpi^nT$ are enough, but not because they are uniquely compatible. Section 3.1 installs coefficient actions on replacement witnesses. At one lifting step, §12.4 closes the generic fiber product of the given lift and the split reference inside the product of two witnesses, then takes a dual-number coefficient quotient. The construction neither asks for nor produces transition maps between the originally selected models.

The genuine failure is absence of a finite-flat model at some level. A rational local representation with weights $\{0,1\}$ does not by itself produce such a model for an arbitrary stable lattice. Without levelwise existence, the local different theorem cannot be applied to that quotient and the first-order dual-number difference need not have a finite-flat witness. A statement about the generic $3$-adic representation alone does not repair that gap.

### 17.3 A weakened wild different estimate

The sharp residual inequality over $\mathbf Q_3$ is

$$
\frac{d_3}{e_3}<\frac32.
$$

If this is weakened to a non-strict inequality, the cyclotomic cubic layer reaches the boundary:

$$
\operatorname{rd}\bigl(\mathbf Q(\zeta_9)\bigr)=3^{3/2}.
$$

The separate upper-break cutoff would still exclude this field; the point is that the weakened different comparison no longer does so. One must not claim that the two local controls are equivalent.

If it is weakened further to a bound allowing upper break one over $\mathbf Q_3$, the real cubic subfield of $\mathbf Q(\zeta_9)$ also survives; its discriminant is $3^4$ and its root discriminant is

$$
3^{4/3}<3^{3/2}.
$$

This example shows why a root-discriminant inequality by itself cannot replace the upper-break cutoff. The local conductor, not merely the size of the global discriminant, excludes the cubic ray layer.

### 17.4 Failure of strict comparison

Every analytic exclusion in the proof has the form

$$
U<L_N,
$$

where $U$ is an arithmetic upper bound and $L_N$ is a lower bound valid for every degree at least $N$ in the relevant signature class. Equality does not give a contradiction. Neither does comparison with an asymptotic constant when the degree is below the range in which the tabulated lower bound has crossed $U$.

At the residual level the explicit unconditional statement used here is exactly

$$
\operatorname{rd}(L)<3^{3/2}
\quad\Longrightarrow\quad
[L:\mathbf Q]\leq52,
$$

because the degree-$53$ lower bound is

$$
5.2006733020\ldots>3^{3/2}.
$$

There is no claim here that degree $52$ is impossible, and no totally-real table is used: oddness makes the determinant field imaginary. For infinite-tower arguments the relevant unconditional asymptotic constant is

$$
4\pi e^\gamma=22.3816160954\ldots,
$$

whereas under GRH it is

$$
8\pi e^\gamma=44.7632321909\ldots.
$$

The GRH constant sharpens a conditional comparison; it plays no role in the strict theorem or in the Frey endpoint.

### 17.5 A residual line that does not lift

Residual reducibility supplies a line in $T/\varpi T$. Lifting that line through $T/\varpi^nT$ is a deformation problem. At the first nonzero level, its obstruction is represented inside the trace-zero cocycle

$$
\rho\rho_0^{-1}-1
$$

after division by the relevant power of $\varpi$.

The strict proof kills the whole cocycle by constructing its affine exponent-three field and excluding every cubic quotient over $\mathbf Q(\zeta_3)$. For an arbitrary auxiliary prime, if the local finite-flat condition is removed, or if the ray-class calculation changes, that affine field can survive. The residual line can then fail to lift even though the residual semisimplification remains $1\oplus\overline\chi_3$. The exact prime-$2$ category is the calculated exception: Chapter 18 retains its Kummer class $a[2]$ and lifts the cyclotomic line by finite-flat devissage rather than by forcing that class to vanish.

No theorem in this book infers characteristic-zero reducibility from residual reducibility alone. The lift in the strict case is supplied by the explicit vanishing and the induction of Chapter 13.

### 17.6 Coefficient and lattice failures

When $k=\mathbf F_{3^f}$ with $f>1$, all subgroup orders, scalar fields, and additive congruence dimensions acquire factors of $f$. A congruence kernel can have order as large as

$$
3^{4f},
$$

not merely $3^4$. The determinant still lands in $\mathbf F_3^\times$, so the actual ambient group is smaller than full $\operatorname{GL}_2(k)$; both facts must be used.

Thus $f>1$ is not a counterexample to the strict classification theorem; it is a failure mode for any proof that uses only the subgroup table of $\operatorname{GL}_2(\mathbf F_3)$. Such a proof has not considered split and nonsplit Cartans of orders depending on $3^f\pm1$, the larger compatible scalar group, or defining-characteristic subgroups. The degree-capped theorem proved in Chapter 6 and Chapter 16's $\mathbf F_9$ diagnostic are what repair the argument.

Coefficient ramification is a separate issue. If $e_{\mathcal O}=v_\varpi(3)>1$, then $T/\varpi^nT$ is killed by $3^{\lceil n/e_{\mathcal O}\rceil}$ and its determinant field is

$$
\mathbf Q\bigl(\zeta_{3^{\lceil n/e_{\mathcal O}\rceil}}\bigr).
$$

Several consecutive $\varpi$-levels may therefore have the same cyclotomic determinant field, while each still has its own congruence kernel in $M_2(k)$. Using $n+1/2$ as the different exponent at the $n$th $\varpi$-level is safe only when $e_{\mathcal O}=1$; the general safe exponent is $\lceil n/e_{\mathcal O}\rceil+1/2$.

If the stable lattice is changed, the visible residual extension can change orientation or become split. What cannot change is a genuine characteristic-zero invariant line. Thus a proof based on one conveniently split reduction must still show that the deformation obstruction vanishes for the original representation. The strict lifting theorem does so; a bare lattice change does not.

### 17.7 A full-tower misuse

At level $n$, finite flatness gives a bound of the shape

$$
\operatorname{rd}(L_n)<3^{n+1/2},
$$

not the residual constant $3^{3/2}$. The right-hand side grows with $n$. Therefore the Fontaine--Odlyzko theorem for a fixed exponent-three family cannot be applied directly to the union of all $L_n$.

One must instead isolate the fixed-determinant difference from the cyclotomic direction. In the strict proof this is done at each step by the common-ambient dual-number construction, which produces a module killed by $3$ over the fixed base and then excludes it immediately by ray class theory. The cyclotomic determinant tower is the standing counterexample to any argument applied to the whole $L_n$: it is infinite, finite flat, and necessarily present.

## 18. Final theorem package and the Frey interface

We now collect the exact outputs. Each theorem records the hypotheses needed at its own stage, so that a later application cannot silently exchange a residual assertion for a characteristic-zero one.

### 18.1 The exact local condition at $2$

We begin with the clause that distinguishes the theorem from an arbitrary auxiliary-prime
search. Let $A$ be a finite local $3$-primary ring, let $W$ be free of rank two over $A$, and
let

$$
\tau:G_{\mathbf Q}\longrightarrow\operatorname{GL}_A(W)
$$

have determinant equal to the reduction of $\chi_3$. The exact condition at $2$ is a stable
sequence

$$
0\longrightarrow W_2^+\longrightarrow W
\overset{\pi_2}{\longrightarrow}W_2^-\longrightarrow0, \tag{18.1}
$$

with both endpoints free of rank one, such that the character $\eta_2$ on $W_2^-$ is
unramified and

$$
\eta_2^2=1. \tag{18.2}
$$

This is precisely the condition carried by the prime-$2$ hardly ramified deformation. It does
not say that $\tau$ is unramified at $2$. The other diagonal character is
$\chi_3\eta_2$, and $\chi_3$ is unramified at $2$.

**Proposition 18.1 (exact inertia at $2$).** Suppose $A$ has characteristic dividing $3^m$.
For every $\sigma\in I_2$,

$$
(\tau(\sigma)-1)^2=0,
\qquad
\tau(\sigma)^{3^m}=1. \tag{18.3}
$$

The wild inertia group acts trivially. The finite inertia image is therefore cyclic of order
$3^a$ for some $0\leq a\leq m$, and the local extension is tame. Its normalized different
contribution is exactly

$$
\frac{d_2}{e_2}=
\begin{cases}
0,&a=0,\\[3pt]
1-3^{-a},&a>0.
\end{cases} \tag{18.4}
$$

At residual level $m=1$, the only possibilities are

$$
e_2=1,\quad \frac{d_2}{e_2}=0,
\qquad\text{or}\qquad
e_2=3,\quad \frac{d_2}{e_2}=\frac23. \tag{18.5}
$$

**Proof.** Both diagonal characters in (18.1) are trivial on inertia. In a basis adapted to
the sequence,

$$
\tau(\sigma)=
\begin{pmatrix}1&c(\sigma)\\0&1\end{pmatrix}.
$$

This proves the square-zero identity. Since the characteristic divides $3^m$,

$$
(1+N)^{3^m}=1+3^mN=1
$$

when $N^2=0$. Thus every element of the finite inertia image has $3$-power order. Wild
inertia at residue characteristic $2$ has $2$-power image in every finite quotient, so its
image here has order dividing powers of both $2$ and $3$ and is trivial. Tame inertia is
procyclic, giving the cyclic group of order $3^a$. A tame extension of ramification index
$3^a$ has different exponent $3^a-1$, which gives (18.4)--(18.5). $\square$

The exact sequence itself is preserved by scalar extension and coefficient quotient: it is
split as a sequence of underlying $A$-modules because the quotient is free. The square-zero and
$3$-power inertia conclusions are in turn preserved by stable subquotients and finite direct
sums. For a direct sum of objects killed by $3$, the tame inertia image is still a quotient of
the exponent-three part of tame inertia and hence is either trivial or cyclic of order three.

The cost $2/3$ is attained. The Kummer cocycle of $2$ gives

$$
g\longmapsto
\begin{pmatrix}overline\chi_3(g)&c_2(g)\\0&1\end{pmatrix}. \tag{18.6}
$$

It is finite flat at $3$, unramified outside $\{2,3\}$, and has tame inertia of order three
at $2$. Thus a theorem claiming residual splitting in the exact prime-$2$ category would be
false. The field in the nonsplit case is

$$
\mathbf Q(\zeta_3,\sqrt[3]{2}),
$$

with Galois group $S_3$ and exact prime-$2$ contribution $2/3$.

### 18.2 Torsion fields and the unconditional degree-$20$ cutoff

Let $T_n=T/\varpi^nT$ and $K_n=\mathbf Q(T_n)$. Put

$$
e_{\mathcal O}=v_\varpi(3),
\qquad
m(n)=\left\lceil\frac{n}{e_{\mathcal O}}\right\rceil.
$$

Then $T_n$ is killed by $3^{m(n)}$. The finite-flat estimate at $3$ and Proposition 18.1 at
$2$ give the complete two-prime ledger

$$
\frac{d_3(K_n)}{e_3(K_n)}<m(n)+\frac12,
\qquad
\frac{d_2(K_n)}{e_2(K_n)}=1-3^{-a_n} \tag{18.7}
$$

when the inertia at $2$ has order $3^{a_n}>1$, with the second entry replaced by zero when it
is unramified. Here $0\leq a_n\leq m(n)$. Hence

$$
\boxed{
\operatorname{rd}(K_n)
<3^{m(n)+1/2}2^{1-3^{-a_n}}.
} \tag{18.8}
$$

The exponent at $2$ is exact; the exponent at $3$ is the strict universal finite-flat bound.
At residual level this becomes

$$
\boxed{
\operatorname{rd}(K_1)
<U_{2,3}:=3^{3/2}2^{2/3}
=8.248377821991616\ldots .
} \tag{18.9}
$$

The old degree-$52$ Minkowski argument does not apply to (18.9): its unrestricted asymptotic
constant is only $\pi e^2/4=5.803\ldots$. The replacement is the unconditional triangular
test function already evaluated in Book 179. Take support $T=6$ and real proportion $\alpha=0$.
That calculation proves

$$
A_6=3,
\qquad B_6<1.10356,
$$

and for every degree $n$,

$$
\log\operatorname{rd}(L)>
\gamma+\log(8\pi)-\frac{12}{n}-1.10356. \tag{18.10}
$$

At $n=21$, the right side is

$$
2.126398521002197\ldots,
$$

so

$$
\operatorname{rd}(L)>8.38461535304387\ldots
>8.248377821991616\ldots=U_{2,3}. \tag{18.11}
$$

For a fixed test function the lower bound increases with $n$. Therefore (18.9)--(18.11) give
the unconditional conclusion

$$
\boxed{[K_1:\mathbf Q]\leq20.} \tag{18.12}
$$

The logarithmic margin is

$$
2.126398521002197\ldots-2.110016553375461\ldots
=0.016381967626735\ldots .
$$

No field table and no unperformed enumeration enter this cutoff. Under GRH one can obtain
stronger lower bounds, but every result below uses (18.10) and is unconditional.

Every simple subquotient of every finite level is killed by $3$. Its model is inherited by
saturated closure and quotient at $3$, and its inertia at $2$ is trivial or cyclic of order
three. Its cutout field therefore satisfies the same bound (18.9) and the same degree cap
(18.12). More generally, finite direct sums of such exponent-three objects still satisfy
(18.9); the product model at $3$ keeps the same upper cutoff, and tame inertia at $2$ remains
cyclic of exponent three. This is the fixed-base finite arena used in the devissage. The full
level bound (18.8) grows with $n$ and is never misused as a uniform tower bound.

### 18.3 Abelian fields and simple factors

The prime $2$ appears in the discriminant but disappears from every abelian quotient.

**Lemma 18.2 (abelian-field lemma).** Let $F/\mathbf Q$ be an abelian subextension of an
exponent-three cutout field occurring above. Then

$$
F=\mathbf Q
\qquad\text{or}\qquad
F=\mathbf Q(\zeta_3). \tag{18.13}
$$

**Proof.** Inertia at $2$ is a $3$-group. By the cyclotomic description of abelian extensions,
an abelian field ramified only at $2$ and $3$ lies in a cyclotomic field of conductor
$2^a3^b$. Its inertia at $2$ is a quotient of

$$
(\mathbf Z/2^a\mathbf Z)^\times,
$$

which is a $2$-group. It is simultaneously a $3$-group, so it is trivial. The conductor is
therefore a power of $3$.

At $3$, an abelian positive upper break is an integer. The finite-flat cutoff at $1/2$
excludes every positive break. Only tame ramification remains, and the tame quotient of
$(\mathbf Z/3^b\mathbf Z)^\times$ is the order-two group already present in
$\mathbf Q(\zeta_3)$. This proves (18.13). $\square$

We also need one ray calculation over

$$
K=\mathbf Q(\zeta_3).
$$

Its class number is one without appeal to a table: the Minkowski ideal-class bound is

$$
\frac{4}{\pi}\frac{2!}{2^2}\sqrt3
=\frac{2\sqrt3}{\pi}<2,
$$

so every class contains an ideal of norm one. Let $\lambda=(1-\zeta_3)$ be the prime above
$3$. The prime-to-$3$ part of

$$
(\mathcal O_K/\lambda^r)^\times
$$

is the residue group $\mathbf F_3^\times$ of order two, and the global unit $-1$ maps onto its
generator. Consequently every ray class group supported only at $\lambda$ is a $3$-group.
In particular it has no quotient of prime order different from three. This proof also shows
why no hidden quadratic ray layer appears over $K$.

**Proposition 18.3 (simple-factor classification).** Every simple generic factor of a finite
object in the exact prime-$2$ category is one-dimensional over $\mathbf F_3$. Its character is
either $1$ or $\overline\chi_3$. Its finite-flat model at $3$ is respectively the constant
group of order three or the multiplicative group $\mu_3$.

**Proof.** Let $S$ be a simple factor and let $G$ be its faithful finite image. Section 18.2
gives

$$
|G|\leq20. \tag{18.14}
$$

Every group of order at most twenty is solvable. Here is the required short proof. If a prime
$r\geq5$ divides the order, the number of Sylow $r$-subgroups is congruent to one modulo $r$
and divides a number at most four, so the Sylow subgroup is normal. If only $2$ and $3$ occur,
the only non-$r$-group orders at most twenty are $6$, $12$, and $18$. The Sylow $3$-subgroup is
normal for orders $6$ and $18$. At order $12$, either it is normal or the four Sylow
$3$-subgroups give a faithful conjugation action on four letters. Indeed, the kernel cannot
have order three, since that would be a normal Sylow subgroup. The image is then an index-two
subgroup of $S_4$, hence $A_4$, whose four-group of double transpositions is normal. Induction
on the order proves solvability.

If $G$ is nontrivial, a solvable perfect group would have a derived series that never reaches
one, so $G^{\mathrm{ab}}$ is nontrivial. Lemma 18.2 makes it $C_2$. Put

$$
H=[G,G].
$$

Then $[G:H]=2$ and $|H|\leq10$. We claim that $H$ is a $3$-group. If a prime
$r\ne3$ divided $H^{\mathrm{ab}}$, take a quotient of order $r$ and intersect its kernel with
its conjugate under the order-two quotient $G/H$. This produces a nontrivial elementary
abelian $r$-extension of $K$ which is Galois over $\mathbf Q$. At the prime above $2$ it is
unramified because inertia there is a $3$-group. At $\lambda$ it is at most tame, and the ray
calculation above shows that no prime-to-$3$ quotient exists. This contradiction proves that
$H^{\mathrm{ab}}$ is a $3$-group.

If $H\ne1$, solvability makes $H^{\mathrm{ab}}$ nontrivial. Since $|H|\leq10$, its order is
$3$, $6$, or $9$. A group of order six is cyclic or has a normal subgroup of order three and
quotient of order two; its abelianization is respectively $C_6$ or $C_2$, not a $3$-group.
Thus $H$ has order three or nine and is a $3$-group.

A normal $3$-subgroup acts trivially on every simple module in characteristic three. Indeed,
a finite $3$-group has a nonzero fixed vector on every nonzero characteristic-three module;
normality makes the fixed space $G$-stable, and simplicity makes it the whole module. Since the
action defining $G$ is faithful, this forces $H=1$. Hence $G$ is trivial or $C_2$, and $S$ is
one-dimensional with character $1$ or the unique nontrivial character
$\overline\chi_3$.

It remains to identify the order-three models. The rank-three finite-flat classification over
the unramified DVR $\mathbf Z_3$ writes the two Hopf parameters as $a,b$ with
$ab$ equal to $3$ times a unit. Their nonnegative valuations sum to one, so the only cases are
$(0,1)$ and $(1,0)$. They are the constant and multiplicative endpoints. Their generic
characters distinguish them: the first is trivial and the second is cyclotomic. $\square$

This argument explains why the allowed $S_3$ Kummer field is harmless for simple factors. In
characteristic three, its normal cubic subgroup acts trivially on every simple module; the two
simple factors are still the trivial and sign characters.

### 18.4 Multiplicative--constant devissage

We now pass from simple factors to an arbitrary finite coefficient quotient. The construction
is global and keeps the tame prime $2$ visible.

First glue the local models. At every odd prime $q\ne3$, unramifiedness gives the unique finite
étale model. At $3$, use the supplied finite-flat witness, enhanced with its coefficient action
by Section 3.1. On the coordinate algebra of the generic finite étale group, intersect these
Hopf orders inside the generic algebra. Over the Dedekind ring $\mathbf Z[1/2]$ the intersection
is finite projective, and the coproduct, counit, and antipode preserve it because they preserve
every localization. It therefore defines a finite locally free commutative group scheme over
$\mathbf Z[1/2]$. The prime $2$ is omitted from the base, while Proposition 18.1 records its
tame generic inertia.

Stable generic subgroups are closed in this model and quotients are represented and finite
flat. Thus a composition series exists inside the same category, and Proposition 18.3 labels
each simple interval as **multiplicative** or **constant**.

Two elementary extension calculations organize those labels.

1. A block all of whose simple factors are constant has trivial Galois action. Indeed, choose
   a composition series. Successive extensions of finite étale groups over $\mathbf Z_3$ are
   finite étale, so the whole block is unramified at $3$. In a basis successively adapted to
   its order-three factors, every Galois element acts upper unipotently on each exponent-three
   layer. Induction on the exponent shows that the full finite image is a $3$-group: the kernel
   on passing to the next exponent layer is an additive group killed by $3$, and the image on
   the lower layer is a $3$-group. If the image were nontrivial, its abelianization would have
   a quotient $C_3$. The corresponding cyclic cubic field would be unramified at every odd
   prime and ramified at most at $2$. But an abelian field of conductor $2^a$ has Galois group
   a quotient of $(\mathbf Z/2^a\mathbf Z)^\times$, a $2$-group. This contradiction makes the
   block constant. Cartier duality gives the parallel statement: a block all of whose factors
   are multiplicative is acted on by the determinant character.
2. A multiplicative factor lying above a constant block can be moved below it. It is enough to
   treat one constant factor at a time. A generic extension in the wrong order has the form
   $$
   0\longrightarrow\mathbf F_3
   \longrightarrow X\longrightarrow\mathbf F_3(1)
   \longrightarrow0. \tag{18.15}
   $$
   Saturate the constant line in the local model at $3$. Proposition 18.3 identifies its
   closure with the constant group and the quotient with $\mu_3$. In the connected--étale
   sequence of the rank-nine middle group, the connected component cannot have rank one,
   since the quotient by the constant subgroup is connected, and it cannot have rank nine,
   since the constant subgroup is étale. It therefore has rank three. Its map to the
   multiplicative quotient is an isomorphism: its kernel is both connected and contained in
   the constant subgroup, hence trivial, and the two groups have the same rank. This supplies
   a multiplicative subgroup complementary to the constant subgroup, so (18.15) splits on
   generic points at $3$. In particular the underlying extension of finite abelian groups is
   split and $X$ is killed by $3$. It is therefore globally an $\mathbf F_3$-linear extension,
   and its class lies in
   $$
   H^1(\mathbf Q,\mathbf F_3(1)).
   $$
   Here the coefficient character is correct because
   $\overline\chi_3^{-1}=\overline\chi_3$.
   Ramification outside $\{2,3\}$ restricts this group to the two Kummer classes of $2$ and
   $3$. Their images in
   $$
   \mathbf Q_3^\times/\mathbf Q_3^{\times3}
   $$
   are independent: $3$ is the valuation direction and $2$ is the nonzero principal-unit
   direction. For the last assertion, replace $2$ by the same Kummer class $-2=1-3$. If
   $-2=u^3$, then $u\equiv1\pmod3$, while the cube of every $u\equiv1\pmod3$ is
   $1\pmod9$; but $-2\equiv7\pmod9$. Local splitting therefore makes both coefficients zero.
   Projecting onto each
   constant simple quotient and inducting moves a multiplicative factor below an arbitrary
   constant block.

Repeatedly applying these two calculations sorts a composition series. For a finite local
coefficient ring $A$, a free rank-two object $W$, and its representation $\tau$, there is an
additive invariant cut $N_0$ such that the lower block is determinant-type and the quotient is
constant. The cut need not be an $A$-direct summand. What is canonical is the $A$-submodule

$$
N=\sum_{g\in G_{\mathbf Q}}\sum_{x\in W}
A\bigl(\tau(g)x-x\bigr). \tag{18.16}
$$

The sorted filtration gives the cross relation

$$
\bigl(\tau(h)-\det\tau(h)\bigr)
\bigl(\tau(g)-1\bigr)=0
\qquad(g,h\in G_{\mathbf Q}). \tag{18.17}
$$

Consequently $W/N$ is trivial and $G_{\mathbf Q}$ acts on $N$ through $\det\tau$. This
description makes $N$ stable under the full coefficient ring even if the original sorted
additive cut was not.

The cross relation also proves the character identity without assuming that $N$ or $W/N$ is
free. Put $f=\tau(g)$ and $d=\det f$. Taking $h=g$ in (18.17) gives

$$
f^2-(1+d)f+d=0. \tag{18.18}
$$

Cayley--Hamilton gives

$$
f^2-(\operatorname{tr}f)f+d=0.
$$

Subtracting and using the invertibility of $f$ on the faithful free $A$-module $W$ yields

$$
\boxed{
\operatorname{tr}\tau(g)=1+\det\tau(g)
\quad\text{for every }g.
} \tag{18.19}
$$

This completes the finite-level argument. It used the degree-$20$ cap only to classify simple
factors. It did not enumerate number fields, discard the Kummer field, or apply the residual
root-discriminant bound to a higher-level torsion field.

### 18.5 The residual extension and its Kummer class

Apply Section 18.4 with $A=k$ and $W=M$. The canonical submodule $N$ in (18.16) is neither zero
nor all of $M$. If $N=0$, the representation is trivial, contradicting its cyclotomic
determinant. If $N=M$, (18.17) makes every element act on all of $M$ through the determinant,
so its matrix determinant would be the square of that character. Complex conjugation gives
$-1=1$, again a contradiction. Thus $N$ has $k$-dimension one. We obtain the exact sequence

$$
\boxed{
0\longrightarrow k(1)\longrightarrow M
\longrightarrow k\longrightarrow0.
} \tag{18.20}
$$

The orientation in (18.20) is part of the conclusion. It is stronger than residual
semisimplification and weaker than residual splitting.

Its extension class lies in $H^1(\mathbf Q,k(1))$. The ramification record restricts the
global Kummer group to

$$
\left(\mathbf Z[1/2,1/3]^\times/
\mathbf Z[1/2,1/3]^{\times3}\right)
\otimes_{\mathbf F_3}k
=k[2]\oplus k[3]. \tag{18.21}
$$

The sign contributes nothing because $-1$ is a cube. At $3$, the closures of the two lines
are the unique multiplicative and constant order-three models in the low-ramification range.
The standard-endpoint Kummer calculation of Book 67 therefore identifies the finite-flat
classes with the unit line and excludes the valuation direction. Therefore

$$
\boxed{[M]=a[2]\quad\text{for a unique }a\in k.} \tag{18.22}
$$

If $a=0$, the residual representation is split and its field is
$\mathbf Q(\zeta_3)$. If $a\ne0$, rescaling the cyclotomic line normalizes $a$ to one; the
image is $S_3$, the cubic inertia at $2$ is nontrivial, and the field is
$\mathbf Q(\zeta_3,\sqrt[3]{2})$. This is the complete residual candidate ledger:

| residual class | inertia at $2$ | image order | normalized $2$-cost |
|---|---:|---:|---:|
| $a=0$ | $1$ | $2$ | $0$ |
| $a\ne0$ | $C_3$ | $6$ | $2/3$ |

Both rows satisfy the unconditional degree-$20$ cap. No other Borel, Cartan-normalizer,
exceptional, or defining-characteristic image survives the simple-factor argument.

### 18.6 Integral line lifting and the $3$-adic character

The finite-level relation does more than determine a residual semisimplification. It produces a
single integral line without asking that the original representation be semisimple.

**Theorem 18.4 (exact prime-$2$ character theorem).** Let $T$ and $\rho$ satisfy clauses
1--2 and 4--8 of the exact prime-$2$ datum in Section 1.2. Then

$$
\operatorname{tr}\rho(g)=1+\chi_3(g)
\qquad(g\in G_{\mathbf Q}), \tag{18.23}
$$

and there is an exact sequence of free $\mathcal O$-modules

$$
\boxed{
0\longrightarrow\mathcal O(1)\longrightarrow T
\longrightarrow\mathcal O\longrightarrow0.
} \tag{18.24}
$$

After bases are chosen, the class of (18.24) is

$$
\boxed{[T]=b[2]\quad\text{for a unique }b\in\mathcal O.} \tag{18.25}
$$

In particular

$$
\rho^{\mathrm{ss}}\simeq1\oplus\chi_3. \tag{18.26}
$$

If $\rho$ is semisimple, then $b=0$ and the representation is the split sum
$1\oplus\chi_3$.

**Proof.** Apply Section 18.4 to $T/\varpi^nT$ for every $n$. The hypotheses survive
coefficient quotient because the rank-one quotient in (18.1) is free. Thus (18.17) and
(18.19) hold modulo $\varpi^n$ for every $n$. The intersection of the ideals
$\varpi^n\mathcal O$ is zero,
so passage to the separated inverse limit gives (18.23) and the integral cross relation

$$
\bigl(\rho(h)-\chi_3(h)\bigr)\bigl(\rho(g)-1\bigr)=0
\qquad(g,h\in G_{\mathbf Q}). \tag{18.27}
$$

Let $N_T$ be the $\mathcal O$-submodule generated by all

$$
\rho(g)x-x,
\qquad g\in G_{\mathbf Q},\quad x\in T,
$$

and let $L$ be its saturation in $T$. Since $\mathcal O$ is noetherian, $N_T$ is generated by
finitely many such differences. Relation (18.27) says that $G_{\mathbf Q}$ acts on $N_T$
through $\chi_3$. It acts in the same way on $L$: if $\varpi^r y\in N_T$, then

$$
\varpi^r\bigl(\rho(h)y-\chi_3(h)y\bigr)=0,
$$

and $T$ is torsion free.

Put $N_E=N_T\otimes_{\mathcal O}E$. It is not zero, since otherwise $\rho$ would be trivial
and could not have determinant $\chi_3$. It is not all of $V$, since then (18.27) would make
every $\rho(h)$ the scalar $\chi_3(h)$; at complex conjugation its determinant would be
$\chi_3(c)^2=1$ instead of $\chi_3(c)=-1$. Hence $N_E$ has dimension one. The saturation $L$
is consequently free of rank one, with character $\chi_3$, and $T/L$ is torsion free of rank
one. Every difference $\rho(g)x-x$ lies in $L$, so $G_{\mathbf Q}$ acts trivially on $T/L$.
This proves (18.24).

It remains to determine the extension class. At each $3^n$-level, the Kummer sequence and the
class number one of $\mathbf Q$ identify the classes unramified outside $\{2,3\}$ with the
$3^n$-power quotient of $\mathbf Z[1/6]^\times$. Taking the inverse limit and then extending
coefficients from $\mathbf Z_3$ to $\mathcal O$ gives

$$
H^1_{\{2,3\}}(\mathbf Q,\mathcal O(1))
\simeq\mathcal O[2]\oplus\mathcal O[3]. \tag{18.28}
$$

Here $[2]$ and $[3]$ are the compatible systems of their classes modulo all powers of three;
$-1$ contributes nothing because it is already a cube. Write the class as
$b_2[2]+b_3[3]$. For every $n$, reduce (18.24) modulo $\varpi^n$. Over $\mathbf Z_3$ the
absolute ramification index is one, strictly smaller than $3-1$. The low-ramification
full-faithfulness theorem of Book 67 therefore identifies the closures of its two endpoints
with the unique coefficient multiplicative and constant models. The standard-endpoint Kummer
calculation in the same book then says that the generic class of this finite-flat extension is
in the coefficient span of the unit groups. Equivalently, after decomposing the finite additive
coefficient module into cyclic $3^r$-constituents, every projected class lies in

$$
\mathbf Z_3^\times/(\mathbf Z_3^\times)^{3^r}.
$$

Thus its local class lies on the unit line generated by $[2]$. The class $[3]$ is the
independent valuation line, so

$$
b_3\equiv0\pmod{\varpi^n}
$$

for every $n$. Separatedness gives $b_3=0$, proving (18.25). This all-level endpoint
calculation is essential: residual finite flatness alone would show only
$b_3\in\varpi\mathcal O$.

Tensoring (18.24) with $E$ gives (18.26). If $\rho$ is semisimple, this rational extension
splits. Under (18.28), the class $b[2]$ remains nonzero after tensoring with $E$ unless $b=0$,
so semisimplicity forces $b=0$ and the integral extension splits as well. $\square$

The theorem also determines the apparently possible unramified quadratic character in the
local input. The two characters in the semisimplification of (18.24) restricted to
$G_{\mathbf Q_2}$ are $1$ and $\chi_3$, while (18.1) gives $\eta_2$ and
$\chi_3\eta_2$. Equality of these unordered pairs forces $\eta_2=1$: the other possible
identification would make the infinite unramified character $\chi_3|_{G_{\mathbf Q_2}}$ have
order at most two. The quadratic allowance in (18.2) was nevertheless essential in stating
the local category before the global argument was run.

The nonsplit alternative is attained when semisimplicity is omitted. The compatible Kummer
classes of $2$ give a $\mathbf Z_3$-extension of the trivial line by the cyclotomic line; its
$3^n$-level is finite flat at $3$ because $2$ is a unit, and at $2$ it has the tame unipotent
sequence (18.1). Its class in (18.25) is $[2]$.

### 18.7 Coefficient extension and changing the prime

There are two different stability questions, and only one is formal.

**Proposition 18.5 (stability of the local clause).** The exact sequence
(1.1)--(1.2) is preserved by finite extension of the $3$-adic coefficient field and by every
finite coefficient quotient. If a compatible system is obtained from a curve with split or
nonsplit multiplicative reduction at $2$, its geometric lattice satisfies the same clause at
every odd coefficient prime. Weak equality of good-prime Frobenius polynomials alone does not
imply this integral assertion.

**Proof.** Let $\mathcal O'/\mathcal O$ be the valuation ring of a finite coefficient
extension. Since $T_2^-$ is free, (1.1) is split as a sequence of underlying
$\mathcal O$-modules. Tensoring with $\mathcal O'$ is therefore exact, as is quotienting by
any ideal of either coefficient ring. The quotient character is the scalar extension or
reduction of $\eta_2$, so it remains unramified and still satisfies $\eta_2^2=1$.

For the changing-prime assertion, let $q_E$ be a Tate parameter over a finite unramified
extension of $\mathbf Q_2$. The geometric lattice at every odd coefficient prime $\ell$ has
the exact Tate sequence

$$
0\longrightarrow\mathbf Z_\ell(1)\otimes\eta_2
\longrightarrow T_\ell
\longrightarrow\mathbf Z_\ell\otimes\eta_2
\longrightarrow0, \tag{18.29}
$$

where $\eta_2=1$ in the split case and is the unramified quadratic character in the nonsplit
case. Thus $\eta_2^2=1$, and the determinant of (18.29) is cyclotomic. Base change to the
coefficient valuation ring gives exactly (1.1)--(1.3).

More generally, a strongly compatible rank-one special local parameter gives the rational
shape of (18.29), but an integral special lattice must still be supplied: a rational change of
basis can alter the thickness of the upper-right entry. Equality of Frobenius polynomials at
good primes records neither this lattice nor the finite-flat models at the new coefficient
prime. Those two integral inputs must therefore be checked separately in a changing-prime
construction. $\square$

For the normalized Frey curve, the multiplicative reduction calculation supplies (18.29)
directly. Its minimal-discriminant valuation controls whether inertia remains nontrivial after
reduction, but nonvanishing is not required for Proposition 18.1: both the trivial and the
cyclic cubic residual inertia rows occur in the exact category.

### 18.8 The unconditional Frey interface

We can now state the endpoint in the form needed by a prime-switched Frey-compatible system.

**Theorem 18.6 (unconditional exact prime-$2$ Frey interface).** Let
$\{\rho_\lambda\}$ be a rank-two compatible system over $\mathbf Q$, and choose a place above
$3$. Write $\mathcal O$ for its coefficient valuation ring and $\varpi$ for a uniformizer,
and choose a stable lattice $T$ in the corresponding representation $\rho_3$. Assume exactly
the following.

1. $\det\rho_3=\chi_3$, and $\rho_3$ is odd.
2. The representation is unramified at every odd prime different from $3$.
3. Over $G_{\mathbf Q_2}$ the lattice has an exact sequence
   $$
   0\longrightarrow T_2^+\longrightarrow T\longrightarrow T_2^-\longrightarrow0,
   $$
   with free rank-one endpoints, and the quotient character $\eta_2$ is unramified with
   $\eta_2^2=1$.
4. Every $T/\varpi^nT$ has a finite-flat model over $\mathbf Z_3$.
5. At every prime $p\notin\{2,3\}$ the common polynomial is
   $$
   X^2-a_pX+p,
   $$
   and the system is pure of weight one.

Then no such compatible system exists. This conclusion is unconditional. Semisimplicity of
$\rho_3$ is not needed for the contradiction; if it is supplied, Theorem 18.4 additionally
identifies $\rho_3$ itself with $1\oplus\chi_3$.

**Proof.** The five hypotheses are exactly clauses 1--2 and 4--8 used in Theorem 18.4, together
with the common-polynomial and purity statements. Hence

$$
\operatorname{tr}\rho_3(\operatorname{Frob}_p)=1+p
$$

at every $p\notin\{2,3\}$. Compatibility gives

$$
a_p=1+p \tag{18.30}
$$

in the common algebraic coefficient field: the equality first holds in its completion at the
chosen place above $3$, and that embedding is injective.

Take $p=5$. Hypotheses 2 and 5 make this a common good prime of the system. In the Frey
application the system supplied to this theorem is the level-$2$ minimal companion, not the
original Frey curve before its odd bad primes have been removed; hence $5$ is permitted even
when it was bad for the original curve. Purity says that the two complex Frobenius roots have absolute value
$\sqrt5$, so

$$
|a_5|\leq2\sqrt5. \tag{18.31}
$$

But (18.30) says $a_5=6$, while

$$
6>2\sqrt5.
$$

This contradiction proves the theorem. The proof uses the unconditional calculation
(18.10)--(18.12), and it invokes neither GRH nor a field table. $\square$

The theorem deliberately says ``unramified at every odd prime different from $3$,'' not
``unramified outside $3$.'' At $2$ it uses the exact sequence in item 3, which permits the
rank-one tame monodromy present in the Frey route.

### 18.9 Strict specialization and the remaining general boundary

The exact prime-$2$ result contains the old strict endpoint as a specialization.

**Corollary 18.7 (strict theorem).** Let $T$ and $\rho$ satisfy clauses 1--2 and 4--6 of
Section 1.2 and be unramified at every finite prime away from $3$. No local filtration at $2$
and no characteristic-zero semisimplicity are required. Then

$$
T\simeq\mathcal O(1)\oplus\mathcal O,
\qquad
\rho\simeq\chi_3\oplus1.
$$

This is Theorem 13.2: the strict residual calculation removes both extension orientations, and
the common-ambient congruence argument lifts the split lines integrally. If the strict datum
also carries clause 8, there is a shorter verification from the new theorem: the class $b[2]$
in (18.25) has nontrivial inertia at $2$ whenever $b\ne0$, so unramifiedness forces $b=0$;
residually, (18.22) similarly forces $a=0$. The two routes agree without narrowing the old
strict theorem or confusing it with the nonsplit controlled case.

For a genuinely arbitrary auxiliary set, the boundary remains the following proved reduction,
not a completed classification.

**Theorem 18.8 (general controlled-set reduction).** Let a residual rank-two representation
have determinant $\overline\chi_3$, be odd, have a finite-flat model over $\mathbf Z_3$, and
have recorded normalized different contributions $d_q/e_q$ at a finite set $S_0$ disjoint
from $3$. Put

$$
U(S_0)=3^{3/2}\prod_{q\in S_0}q^{d_q/e_q}. \tag{18.32}
$$

If an unconditional explicit-formula calculation gives $U(S_0)<L_N$ in the actual signature
class, then its cutout field has degree less than $N$. Within that finite degree range, a full
classification still requires the determinant and scalar degrees, every permitted local
inertia quotient, the ray and class groups of intermediate fields, and the affine fields of
extension classes. A characteristic-zero conclusion additionally requires levelwise
finite-flat witnesses and vanishing of every infinitesimal obstruction field.

**Proof.** The local--global discriminant formula gives
$\operatorname{rd}(K)<U(S_0)$. The explicit-formula lower bound and the strict inequality then
give the degree cutoff. Chapters 6--13 prove why each item in the remaining ledger is necessary
and why, once all of them are eliminated, the line-lifting conclusion follows. None of those
eliminations is implied by the degree cutoff alone. $\square$

Under GRH the lower bound in this general reduction may be replaced by a proved GRH bound in
the relevant degree and signature; its asymptotic constant is $8\pi e^\gamma$. That is the only
GRH-dependent statement in this final package. It is not used in Theorems 18.4 or 18.6.

The set $S_0=\{2\}$ with the exact local sequence is no longer part of this unresolved
boundary: Sections 18.1--18.8 perform its different calculation, degree cutoff, group and ray
eliminations, devissage, line lifting, and purity contradiction. What remains open in
Theorem 18.8 is only an auxiliary prime for which no comparably exact local structure has been
supplied.

### 18.10 What has been proved

The complete unconditional ledger for the exact prime-$2$ theorem is:

| stage | exact output |
|---|---|
| inertia at $2$ on a level killed by $3^m$ | $C_{3^a}$, $0\leq a\leq m$, wild inertia trivial |
| normalized different at $2$ | $0$ if $a=0$; $1-3^{-a}$ if $a>0$ |
| residual $2$-cost | $0$ or $2/3$ |
| normalized different at $3$ | strictly less than $3/2$ residually |
| residual root-discriminant ceiling | $3^{3/2}2^{2/3}=8.248377821991616\ldots$ |
| degree-$21$ unconditional lower bound | $8.38461535304387\ldots$ |
| logarithmic margin | $0.016381967626735\ldots$ |
| residual field degree | at most $20$ |
| abelian subfields | $\mathbf Q$ and $\mathbf Q(\zeta_3)$ only |
| simple finite-flat factors | constant order three or $\mu_3$ |
| chosen residual representation | $0\to k(1)\to M\to k\to0$, class $a[2]$ |
| every finite coefficient level | $\operatorname{tr}=1+\det$ and the cross relation (18.17) |
| integral representation | $0\to\mathcal O(1)\to T\to\mathcal O\to0$, class $b[2]$ |
| characteristic-zero semisimplification | $1\oplus\chi_3$ |
| pure compatible system | impossible already at $p=5$ |

The nonsplit residual row is real: it cuts out
$\mathbf Q(\zeta_3,\sqrt[3]{2})$ and has group $S_3$. It is retained through the field
classification and absorbed by the multiplicative--constant filtration; it is never
incorrectly declared unramified or split. Likewise, a nonsplit integral class $b[2]$ is allowed
when semisimplicity is omitted. What the global category forces in all cases is the cyclotomic
line, the trivial quotient, and the character identity.

Thus the exact theorem now proved is unconditional: every rank-two $3$-adic representation
over $\mathbf Q$ with cyclotomic determinant, oddness, levelwise finite flatness at $3$,
unramifiedness at all odd primes away from $3$, and the precise unramified-quadratic quotient
condition at $2$ has (18.24)--(18.26). No pure weight-one compatible system can contain it. The
local condition is stable under coefficient extension and coefficient quotient, and the Tate
lattice supplies it after changing coefficient prime for split or nonsplit multiplicative
reduction at $2$. No finite enumeration and no conditional hypothesis remain in this
prime-$2$ route.
