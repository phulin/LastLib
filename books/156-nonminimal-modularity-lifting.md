# Nonminimal Modularity Lifting

## Contents

1. [Why nonminimal lifting is a separate theorem](#1-why-nonminimal-lifting-is-a-separate-theorem)
   - [1.1 The question](#11-the-question)
   - [1.2 Standing arithmetic data](#12-standing-arithmetic-data)
   - [1.3 Three proof routes](#13-three-proof-routes)
   - [1.4 The infrastructure ledger](#14-the-infrastructure-ledger)
   - [1.5 Scope and exclusions](#15-scope-and-exclusions)
2. [Comparing deformation problems without reversing arrows](#2-comparing-deformation-problems-without-reversing-arrows)
   - [2.1 Conditions, inclusions, and representing rings](#21-conditions-inclusions-and-representing-rings)
   - [2.2 Intersections when conditions are not nested](#22-intersections-when-conditions-are-not-nested)
   - [2.3 Global deformation data and canonical maps](#23-global-deformation-data-and-canonical-maps)
   - [2.4 Selmer comparison and the distribution of a local cost](#24-selmer-comparison-and-the-distribution-of-a-local-cost)
   - [2.5 Local bases, relation defects, and components](#25-local-bases-relation-defects-and-components)
3. [Local deformation conditions away from $\ell$](#3-local-deformation-conditions-away-from-ell)
   - [3.1 The unrestricted fixed-determinant problem](#31-the-unrestricted-fixed-determinant-problem)
   - [3.2 Unramified and fixed finite-type conditions](#32-unramified-and-fixed-finite-type-conditions)
   - [3.3 Nonzero unipotent and Steinberg conditions](#33-nonzero-unipotent-and-steinberg-conditions)
   - [3.4 The closed level-raising special component](#34-the-closed-level-raising-special-component)
   - [3.5 Tamely ramified principal-series conditions](#35-tamely-ramified-principal-series-conditions)
   - [3.6 The local dimension and framing table](#36-the-local-dimension-and-framing-table)
4. [The coefficient prime](#4-the-coefficient-prime)
   - [4.1 The exact finite-flat condition](#41-the-exact-finite-flat-condition)
   - [4.2 The power-series theorem and its range](#42-the-power-series-theorem-and-its-range)
   - [4.3 Ordinary and crystalline conditions are different inputs](#43-ordinary-and-crystalline-conditions-are-different-inputs)
   - [4.4 Restriction and finite-flat component control](#44-restriction-and-finite-flat-component-control)
5. [Conductors, local types, and component choices](#5-conductors-local-types-and-component-choices)
   - [5.1 Residual and characteristic-zero conductors](#51-residual-and-characteristic-zero-conductors)
   - [5.2 Scalar Frobenius and vexing primes](#52-scalar-frobenius-and-vexing-primes)
   - [5.3 Type equality is not component equality](#53-type-equality-is-not-component-equality)
   - [5.4 A controlled local datum](#54-a-controlled-local-datum)
6. [Level raising from degeneracy maps](#6-level-raising-from-degeneracy-maps)
   - [6.1 The two maps and their adjoints](#61-the-two-maps-and-their-adjoints)
   - [6.2 The Gram determinant and the congruence equation](#62-the-gram-determinant-and-the-congruence-equation)
   - [6.3 The two $U_p$ branches](#63-the-two-u_p-branches)
   - [6.4 Ihara injectivity and saturation](#64-ihara-injectivity-and-saturation)
   - [6.5 The integral level-raising theorem](#65-the-integral-level-raising-theorem)
7. [Level lowering and its noncircular hypotheses](#7-level-lowering-and-its-noncircular-hypotheses)
   - [7.1 What must be lowered](#71-what-must-be-lowered)
   - [7.2 The monodromy and component-group sequence](#72-the-monodromy-and-component-group-sequence)
   - [7.3 The integral level-lowering theorem](#73-the-integral-level-lowering-theorem)
   - [7.4 Why residual conditions matter](#74-why-residual-conditions-matter)
8. [Hecke modules, congruence ideals, and the price of level](#8-hecke-modules-congruence-ideals-and-the-price-of-level)
   - [8.1 Minimal and enlarged Hecke orders](#81-minimal-and-enlarged-hecke-orders)
   - [8.2 Old, new, and saturated lattices](#82-old-new-and-saturated-lattices)
   - [8.3 Cotangent modules and local congruence factors](#83-cotangent-modules-and-local-congruence-factors)
   - [8.4 One-prime and many-prime cost formulas](#84-one-prime-and-many-prime-cost-formulas)
9. [Fixed nonminimal primes and Taylor--Wiles primes](#9-fixed-nonminimal-primes-and-taylor--wiles-primes)
   - [9.1 Recomputing dual Selmer](#91-recomputing-dual-selmer)
   - [9.2 Two disjoint kinds of auxiliary level](#92-two-disjoint-kinds-of-auxiliary-level)
   - [9.3 Diamond actions and paired $U/V$ modules](#93-diamond-actions-and-paired-uv-modules)
   - [9.4 The framed, gauge, and relation ledger](#94-the-framed-gauge-and-relation-ledger)
10. [The three nonminimal infrastructure theorems](#10-the-three-nonminimal-infrastructure-theorems)
    - [10.1 Infrastructure NM-I: integral level and type control](#101-infrastructure-nm-i-integral-level-and-type-control)
    - [10.2 Infrastructure NM-II: integral reciprocity and local compatibility](#102-infrastructure-nm-ii-integral-reciprocity-and-local-compatibility)
    - [10.3 Infrastructure NM-III: determinant lines and component support](#103-infrastructure-nm-iii-determinant-lines-and-component-support)
    - [10.4 Logical separation of the three inputs](#104-logical-separation-of-the-three-inputs)
11. [Direct nonminimal patching](#11-direct-nonminimal-patching)
    - [11.1 The finite-level system](#111-the-finite-level-system)
    - [11.2 Verification of the Taylor--Wiles axioms](#112-verification-of-the-taylor--wiles-axioms)
    - [11.3 The patched pair and its dimension](#113-the-patched-pair-and-its-dimension)
    - [11.4 Coverage, faithfulness, and nilpotents](#114-coverage-faithfulness-and-nilpotents)
12. [The nonminimal $R=T$ theorem](#12-the-nonminimal-rt-theorem)
    - [12.1 Full equality](#121-full-equality)
    - [12.2 Reduced equality](#122-reduced-equality)
    - [12.3 Componentwise equality](#123-componentwise-equality)
    - [12.4 The numerical variant](#124-the-numerical-variant)
13. [Extracting modularity of a specified lift](#13-extracting-modularity-of-a-specified-lift)
    - [13.1 From a Galois point to a Hecke character](#131-from-a-galois-point-to-a-hecke-character)
    - [13.2 Identification and exact local type](#132-identification-and-exact-local-type)
    - [13.3 The controlled nonminimal lifting theorem](#133-the-controlled-nonminimal-lifting-theorem)
14. [The minimal-level route down and back up](#14-the-minimal-level-route-down-and-back-up)
    - [14.1 Lowering the residual source](#141-lowering-the-residual-source)
    - [14.2 Raising a congruent automorphic point](#142-raising-a-congruent-automorphic-point)
    - [14.3 Connecting the raised point to the target](#143-connecting-the-raised-point-to-the-target)
    - [14.4 The inductive relative criterion](#144-the-inductive-relative-criterion)
15. [Jacquet--Langlands and integral level control](#15-jacquet--langlands-and-integral-level-control)
    - [15.1 Parity and the choice of quaternion algebra](#151-parity-and-the-choice-of-quaternion-algebra)
    - [15.2 Characteristic-zero transfer](#152-characteristic-zero-transfer)
    - [15.3 Integral Hecke orders and type multiplicities](#153-integral-hecke-orders-and-type-multiplicities)
    - [15.4 Changing the inner form during the argument](#154-changing-the-inner-form-during-the-argument)
16. [Solvable base change, component switching, and descent](#16-solvable-base-change-component-switching-and-descent)
    - [16.1 Choosing an admissible extension](#161-choosing-an-admissible-extension)
    - [16.2 Preserving image, determinant, and cuspidality](#162-preserving-image-determinant-and-cuspidality)
    - [16.3 Modularity after restriction](#163-modularity-after-restriction)
    - [16.4 Recursive descent and the character fiber](#164-recursive-descent-and-the-character-fiber)
    - [16.5 Recovering the original local components](#165-recovering-the-original-local-components)
17. [The ordinary residually reducible maneuver](#17-the-ordinary-residually-reducible-maneuver)
    - [17.1 Why it is a different theorem](#171-why-it-is-a-different-theorem)
    - [17.2 The exact deep input](#172-the-exact-deep-input)
    - [17.3 Proof architecture](#173-proof-architecture)
    - [17.4 Interaction with base change](#174-interaction-with-base-change)
18. [Hardly ramified representations](#18-hardly-ramified-representations)
    - [18.1 A precise definition](#181-a-precise-definition)
    - [18.2 The absolutely irreducible theorem](#182-the-absolutely-irreducible-theorem)
    - [18.3 The $3$-adic boundary](#183-the-3-adic-boundary)
    - [18.4 Elliptic curves and geometric representations](#184-elliptic-curves-and-geometric-representations)
19. [Four hostile diagnostics](#19-four-hostile-diagnostics)
    - [19.1 One added Steinberg prime](#191-one-added-steinberg-prime)
    - [19.2 One tame principal-series prime](#192-one-tame-principal-series-prime)
    - [19.3 One scalar or vexing prime](#193-one-scalar-or-vexing-prime)
    - [19.4 One solvable-descent ambiguity](#194-one-solvable-descent-ambiguity)
20. [Limitations and failure boundaries](#20-limitations-and-failure-boundaries)
    - [20.1 Small coefficient primes and small images](#201-small-coefficient-primes-and-small-images)
    - [20.2 Wild types and unreached components](#202-wild-types-and-unreached-components)
    - [20.3 Failures of integral automorphic control](#203-failures-of-integral-automorphic-control)
    - [20.4 A diagnostic decision tree](#204-a-diagnostic-decision-tree)
21. [Interfaces with the later arithmetic chain](#21-interfaces-with-the-later-arithmetic-chain)
    - [21.1 Potential modularity](#211-potential-modularity)
    - [21.2 Compatible systems and changing prime](#212-compatible-systems-and-changing-prime)
    - [21.3 Hardly ramified $3$-adic representations](#213-hardly-ramified-3-adic-representations)
    - [21.4 The FLT interface](#214-the-flt-interface)
    - [21.5 Final perspective](#215-final-perspective)

## 1. Why nonminimal lifting is a separate theorem

Minimal modularity lifting controls lifts whose ramification is exactly the ramification already visible in the residual representation. Arithmetic representations rarely remain in that narrow corridor. Reduction can erase a tame character, kill a monodromy parameter divisible by $\ell$, or make two characteristic-zero local branches meet. The target lift can therefore be ramified at a prime where its residual representation is unramified. The purpose of nonminimal lifting is to recover automorphy without pretending that this extra ramification was present all along.

The central difficulty is not the word “nonminimal.” It is the need to match three geometries at once:

$$
\begin{array}{c}
\text{components of local deformation spaces}\\
\Updownarrow\\
\text{old, new, and type-selected automorphic lattices}\\
\Updownarrow\\
\text{global Selmer and congruence defects.}
\end{array}
\tag{1.1}
$$

A generic local type does not identify an integral component. A characteristic-zero level-raising theorem does not control a lattice modulo $\ell$. A congruent newform does not identify an arbitrary lift having the same residual representation. Each of those missing steps will be named and checked.

### 1.1 The question

Let $F$ be $\mathbf Q$ or a totally real field, and let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{1.2}
$$

be an odd residual representation. Suppose $\bar\rho$ is automorphic. Let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{1.3}
$$

be a characteristic-zero lift, where $\mathcal O'$ is the ring of integers
of a finite extension of the coefficient field,
$E'=\operatorname{Frac}(\mathcal O')$, and $\varpi'$ is a uniformizer. The lift has the expected
weight-two determinant and is finite flat at the places above $\ell$, but it
may have additional controlled ramification away from $\ell$.

The question is:

> Under which exact local, global, and automorphic hypotheses must $\rho$ arise from a weight-two cuspidal automorphic representation with the same local types?

There are two parts to the phrase “the same local types.” First, the automorphic and Galois parameters must match after the fixed normalization of local reciprocity. Second, the point defined by $\rho$ must lie on a component that the automorphic module actually meets. The first assertion is generic local compatibility. The second is an integral support assertion. Neither implies the other.

### 1.2 Standing arithmetic data

Fix an odd prime $\ell$, a finite extension $E/\mathbf Q_\ell$ with ring of integers $\mathcal O$, uniformizer $\varpi$, and residue field $k$. Let $F$ be totally real. Arithmetic Frobenius is used throughout. Let

$$
\bar\rho:G_F\to\operatorname{GL}_2(k)
$$

be continuous, absolutely irreducible, and totally odd. Fix a determinant

$$
\delta=\psi\chi_\ell,
\tag{1.4}
$$

where $\psi$ is finite order and has order prime to $\ell$ unless a different character deformation problem is explicitly stated. Put

$$
W=\operatorname{ad}^0\bar\rho,
\qquad
W'=W^*(1)\simeq W(1).
\tag{1.5}
$$

The last identification uses $\ell>2$. We assume

$$
H^0(F,W)=H^0(F,W(1))=0
\tag{1.6}
$$

whenever the balanced Taylor--Wiles calculation is invoked. Absolute irreducibility gives the first equality; the second excludes a global cyclotomic self-twist.

Let $S_0$ contain the archimedean places, the places above $\ell$, and every place at which $\bar\rho$ or $\delta$ is ramified, and write $S_f$ for its finite places. A minimal datum $\mathcal D^{\min}$ chooses at each finite place the exact minimal condition of Books 66--68. Let $P$ be a finite set of fixed nonminimal places, disjoint from the Taylor--Wiles sets that will vary later. At $v\in P$ choose one precise represented condition $\mathcal D_v^P$ and, when necessary, one generic component of its local ring.

At a good place $v\nmid\ell$, write $q_v$ for the residue cardinality. In the ambient central-character normalization, the good Hecke polynomial is

$$
X^2-S_v^{-1}T_vX+q_vS_v^{-1}.
\tag{1.7}
$$

On the quotient with determinant (1.4), $S_v^{-1}$ specializes to
$\psi(\operatorname{Frob}_v)$. Thus the actual trace operator in this
normalization is $S_v^{-1}T_v$, and for trivial $\psi$ it is simply $T_v$.
All level-raising congruences below are first written in the
trivial-central-character case and then translated by (1.7).

### 1.3 Three proof routes

There are three legitimate routes from residual modularity to modularity of (1.3).

The **direct route** builds the nonminimal deformation ring and matching Hecke algebra at the enlarged level, adds Taylor--Wiles primes disjoint from $P$, and patches the resulting modules. In the balanced smooth-neutral range, reusing Book 155's sharp absolute method with a newly proved $q_P$-generator count gives faithfulness and full equality directly. In a broader singular or nonbalanced range, a support argument instead gives a full, reduced, or componentwise equality under the additional coverage and nilpotent-control hypotheses stated below. Neither direct argument uses a minimal determinant comparison.

The **relative route** first lowers the residual automorphic source to a minimal level, applies the minimal theorem there, raises a congruent automorphic point back to the desired local components, and compares the extra cotangent and congruence factors one fixed prime at a time. The last comparison is essential: level raising alone produces some congruent form, not the target lift.

The **base-change route** restricts to a carefully chosen solvable totally real extension on which troublesome local components become accessible, proves modularity there, and descends. Descent is recursive. Invariance of the top automorphic representation is not, for a noncyclic solvable group, by itself a descent theorem.

The routes can be pictured as follows.

```text
                         direct nonminimal patching
                    R^P ------------------------ T^P
                     |                            |
          target ----+                            +---- automorphic point

     minimal/relative route                 solvable route
     R^min = T^min                           rho|G_E automorphic
          | level factors                         |
          v                                       v recursive descent
        R^P = T^P                              rho automorphic
```

The diagram records strategies, not automatic ring maps. In particular, the vertical arrow from a special local condition to an unramified one exists only when an actual inclusion or intersection of functors supplies it.

### 1.4 The infrastructure ledger

The foundational results already available have sharply limited roles.

| Source | Result used here |
|---|---|
| Books 29--33, 48, 62, and 64--65 | finite-flat representations, continuous cohomology, duality, deformation functors, and representability |
| Book 66 | unramified, prime-to-$\ell$ fixed type, tame matrix, and enhanced special conditions, with only the smoothness and dimension claims actually proved there |
| Book 67 | the full finite-flat type-$(0,1)$ ring over an unramified extension of $\mathbf Q_\ell$ for $\ell>2$, and only a quotient presentation outside that range |
| Book 68 | global assembly, functorial ring directions, Selmer comparison, relative generator and relation counts, and framing corrections |
| Books 71--75 | numerical criteria, Taylor--Wiles systems, patching, support, and the full/reduced/componentwise comparison theorems |
| Books 76--77, 82, 84, and 91--94 | integral Hecke modules, old/new algebra, local types, and characteristic-zero Jacquet--Langlands |
| Books 86 and 96--97 | local and global cyclic base change, solvable iteration, descent fibers, and descent obstructions |
| Books 120, 122, and 135 | degeneracy correspondences, curve cohomology, Hecke-valued determinants, and weight-two Galois representations in the stated geometric range |
| Book 155 | in its clean rational cyclotomic range, the proved minimal equality from sharp absolute $q$-generator patching, finite-flat complete-intersection and Gorenstein structure, the faithful free rank-one minimal module with perfect pairing, and the post-equality Fitting--congruence equality |

Three new infrastructure theorems, NM-I through NM-III, will be stated in
Chapter 10. NM-I and NM-II extend Book 155's two integral infrastructure
theorems to the added level and types. NM-III records only what is genuinely
new after the minimal theorem: relative determinant factors at the added
places and nonminimal component support. Book 155 did not assume a common
determinant to prove its minimal equality; it proved that equality by the
sharp absolute patch and derived the base Fitting--congruence equality
afterward. Accordingly no new hypothesis in this book is allowed to
reassume that proved base comparison.

The principal theorems of this book are conditional on the applicable parts
of those inputs exactly where the preceding books stop. This is mathematical
information: it marks the difference between a proved local equation and a
desired global packet comparison.

### 1.5 Scope and exclusions

The clean direct theorem assumes $\ell>2$, absolute residual irreducibility, adequate Taylor--Wiles prime selection, a fixed determinant, and represented local conditions. Its simplest rational specialization retains the $\ell\ge7$ and nonvexing hypotheses of Book 155. A totally real version requires the Hilbert or quaternionic analogues of the integral control theorems; it is not obtained by replacing $\mathbf Q$ with $F$ in the rational proof.

The following cases are not silently included:

- $\ell=2$, where trace zero does not split off scalars and oddness is not visible in the same residual way;
- small residual images that do not satisfy the prime-detection hypotheses;
- scalar Frobenius at a level-raising prime without a framed or line-enhanced local theorem;
- vexing congruences at which the two level-raising branches or integral determinant factors cease to be primitive;
- wildly ramified inertial types not covered by an explicit local comparison theorem;
- a local component that no automorphic module is proved to meet;
- an ordinary or residually reducible argument unless the separate theorem of Chapter 17 applies;
- generic Jacquet--Langlands without an integral order comparison;
- solvable invariance without a compatible recursive descent chain.

These boundaries will reappear as diagnostics rather than being buried in the final theorem.

## 2. Comparing deformation problems without reversing arrows

Nonminimal arguments compare several moduli problems. The first discipline is variance: a larger set of deformations is represented by a ring mapping to the ring for a smaller set. The second is geometry: two local conditions may meet without either containing the other. This chapter fixes both issues before any Hecke algebra is introduced.

### 2.1 Conditions, inclusions, and representing rings

Let $D_v^{\mathrm{amb}}$ be the framed fixed-determinant deformation functor of $\bar\rho|_{G_{F_v}}$. Suppose $D_v^0$ and $D_v^1$ are closed represented subfunctors and that

$$
D_v^0(A)\subseteq D_v^1(A)
\quad\text{for every Artinian }A.
\tag{2.1}
$$

Then the natural transformation points from the stronger condition to the weaker one,

$$
D_v^0\longrightarrow D_v^1,
\tag{2.2}
$$

and the representing-ring map points oppositely:

$$
R_v^1\twoheadrightarrow R_v^0.
\tag{2.3}
$$

The surjectivity comes from closedness. Thus if an unrestricted condition contains an unramified condition, the canonical map is

$$
R_v^{\square,\mathrm{unrstr}}\twoheadrightarrow
R_v^{\square,\mathrm{ur}},
\tag{2.4}
$$

not the reverse.

The same rule governs global rings. If $\mathcal D^0$ is obtained by strengthening local conditions in $\mathcal D^1$, then

$$
R_{\mathcal D^1}\twoheadrightarrow R_{\mathcal D^0}.
\tag{2.5}
$$

Calling $\mathcal D^1$ “nonminimal” and $\mathcal D^0$ “minimal” does not alter this variance.

### 2.2 Intersections when conditions are not nested

Let $v\nmid\ell$ and suppose $\bar\rho_v$ is unramified. The unramified condition allows arbitrary Frobenius trace with fixed determinant. A closed special condition imposes an ordered line and a ratio of diagonal characters equal to $\chi_\ell$. At monodromy zero it retains those character equations. Therefore it contains only the level-raising locus inside the unramified space, not every unramified deformation.

Let $D_v^{\mathrm{sp}}$ be the enhanced closed special condition and $D_v^{\mathrm{ur}}$ the unramified condition. Their correct common object is

$$
D_v^{\cap}
=D_v^{\mathrm{sp}}
\times_{D_v^{\mathrm{amb}}}
D_v^{\mathrm{ur}}.
\tag{2.6}
$$

It is represented by

$$
R_v^{\cap}
\simeq
R_v^{\mathrm{sp}}
\widehat\otimes_{R_v^{\mathrm{amb}}}
R_v^{\mathrm{ur}}.
\tag{2.7}
$$

There are quotient maps

$$
R_v^{\mathrm{sp}}\twoheadrightarrow R_v^{\cap},
\qquad
R_v^{\mathrm{ur}}\twoheadrightarrow R_v^{\cap}.
\tag{2.8}
$$

In general there is no canonical map between $R_v^{\mathrm{sp}}$ and $R_v^{\mathrm{ur}}$. The equation defining $R_v^{\cap}$ is precisely the level-raising equation. If both special signs are retained and the central character is trivial, their union in the unramified trace line is cut out by

$$
T_v^2-(q_v+1)^2=0
\tag{2.9}
$$

and completion at a clean residual point makes one of its two linear factors a unit. A fixed special character and sign therefore impose the remaining linear factor, not the quadratic equation as an additional independent relation.

This intersection formalism is also required for two fixed inertial types, two choices of stable line at a scalar residual point, or two generic components of one framed local ring. A diagram drawn without (2.6) can assert a ring map that no deformation-theoretic transformation produces.

### 2.3 Global deformation data and canonical maps

Let $\mathcal D=(S,\delta,(\mathcal D_v)_{v\in S})$ be a fixed-determinant global datum. Its unframed universal ring exists because $\bar\rho$ is absolutely irreducible; local conditions with large centralizers are imposed through their framed quotients as in Book 68.

If $T$ is a nonempty set of framed places, put

$$
R_{\mathrm{loc}}(\mathcal D)
=\widehat\bigotimes_{v\in T,\mathcal O}
R_v^{\square,\mathcal D_v}.
\tag{2.10}
$$

The partially framed global ring is a complete local algebra over this tensor product:

$$
R_{\mathrm{loc}}(\mathcal D)
\longrightarrow R_{\mathcal D}^{\square_T}.
\tag{2.11}
$$

Restriction of representations explains the direction of (2.11). It is generally neither injective nor surjective.

Suppose $\mathcal D^+$ strengthens $\mathcal D^-$ at one place $v\in T$. Then the comparison is the completed base change

$$
R_{\mathcal D^+}^{\square_T}
\simeq
R_{\mathcal D^-}^{\square_T}
\widehat\otimes_{R_v^{\square,\mathcal D_v^-}}
R_v^{\square,\mathcal D_v^+}.
\tag{2.12}
$$

Both arrows under the tensor product start from the weaker local ring. When the local conditions are not nested, (2.12) is replaced by the global version of the intersection (2.6). These are the only canonical comparison maps used later.

### 2.4 Selmer comparison and the distribution of a local cost

Let $L_v\subseteq L_v'$ be the tangent spaces of two nested local conditions, equal away from finitely many places. Let $\mathcal L$ and $\mathcal L'$ be the resulting Selmer structures on $W$. Poitou--Tate duality gives the exact sequence

$$
\begin{aligned}
0\longrightarrow{}&H^1_{\mathcal L}(F,W)
\longrightarrow H^1_{\mathcal L'}(F,W)
\longrightarrow\bigoplus_vL_v'/L_v\\
\longrightarrow{}&H^1_{\mathcal L^\perp}(F,W')^*
\longrightarrow H^1_{\mathcal L'^\perp}(F,W')^*
\longrightarrow0.
\end{aligned}
\tag{2.13}
$$

Consequently

$$
\begin{aligned}
&h^1_{\mathcal L'}-h^1_{\mathcal L}
+h^1_{\mathcal L^\perp}-h^1_{\mathcal L'^\perp}\\
&\hspace{42mm}
=\sum_v\bigl(\dim L_v'-\dim L_v\bigr).
\end{aligned}
\tag{2.14}
$$

One new local tangent direction need not become one new global tangent direction. It can instead kill one dual Selmer class, or its effect can be divided between the two. Equation (2.13), not a subtraction of local dimensions, decides which occurs.

Define the defect

$$
\Delta(\mathcal D)
=h^1_{\mathcal L}(F,W)
-h^1_{\mathcal L^\perp}(F,W').
\tag{2.15}
$$

Then weakening the local conditions changes the defect by the sum of the local tangent quotients. Direct patching uses the new absolute number

$$
q_P=h^1_{\mathcal L_P^\perp}(F,W'),
\tag{2.16}
$$

not the minimal number $q_{\min}$. Even if both data are balanced, the two dual Selmer dimensions can differ.

### 2.5 Local bases, relation defects, and components

The local tensor product records complete local geometry, not only tangent dimensions. A smooth local factor contributes variables to the base; a singular factor contributes its equations there. The global relative presentation has the form

$$
R_{\mathcal D}^{\square_T}
\simeq
R_{\mathrm{loc}}(\mathcal D)
[[x_1,\ldots,x_{g_T}]]
/(f_1,\ldots,f_{r_T}),
\qquad r_T\le q_T,
\tag{2.17}
$$

where $q_T$ is the relaxed-at-$T$ dual Selmer dimension, not (2.16). If an added local ring is singular, its relation count must not be moved into $r_T$ a second time.

Let $R_v$ be a local ring and let $\mathfrak p_v$ be a minimal prime of $R_v[1/\ell]$. The component closure used in a global problem is

$$
R_v^{\mathfrak p_v}
=R_v/\ker\bigl(R_v\to(R_v[1/\ell]/\mathfrak p_v)\bigr).
\tag{2.18}
$$

It is the scheme-theoretic closure of the selected generic component, not its normalization. Because it embeds in $R_v[1/\ell]/\mathfrak p_v$, it is $\varpi$-torsion-free. A global component datum is a tuple $(\mathfrak p_v)_v$. Patching on one such tuple proves, at most, a componentwise theorem unless a component-hopping result proves that every permitted tuple is met automorphically.

## 3. Local deformation conditions away from $\ell$

At a place $v\nmid\ell$, wild inertia is pro-residue-characteristic and is rigid in $\ell$-adic infinitesimal directions. The pro-$\ell$ tame quotient can move. This makes explicit matrix equations possible, but it does not make every familiar local label one smooth component. We now build only the conditions for which representability and dimensions can be justified.

Write $K=F_v$, $q=q_v$, $G=G_K$, and

$$
W=\operatorname{ad}^0\bar\rho_v,
\qquad
h_v=h^0(K,W),
\qquad
e_v=h^0(K,W(1)).
\tag{3.1}
$$

The determinant is fixed to $\delta_v$. Since $\ell>2$, the trace-zero coefficient is the correct fixed-determinant tangent module.

### 3.1 The unrestricted fixed-determinant problem

The framed unrestricted functor is represented. Its tangent space is

$$
Z^1(K,W),
\tag{3.2}
$$

and local Euler characteristic gives

$$
\dim_k Z^1(K,W)
=h^1(K,W)+3-h_v
=3+e_v.
\tag{3.3}
$$

Tate duality identifies the ambient obstruction group with the dual of $H^0(K,W(1))$. Hence

$$
e_v=0
\quad\Longrightarrow\quad
R_v^{\square,\mathrm{unrstr},\delta}
\simeq\mathcal O[[x_1,x_2,x_3]].
\tag{3.4}
$$

When $e_v\ne0$, (3.3) is only a tangent count. The universal ring has a presentation with possible relations; no smoothness conclusion follows from its dimension alone. The unrestricted condition allows every inertial behavior visible in the ambient deformation problem and therefore has no single automorphic type or conductor. A nonminimal theorem using it must patch a module that covers every claimed component, or else state only a componentwise result.

The unframed unrestricted functor is universal only under the local scalar-centralizer hypothesis. In most level-raising situations the local representation is reducible and has a larger centralizer, so the framed ring is the safe object even though the global unframed ring exists.

### 3.2 Unramified and fixed finite-type conditions

Assume first that $\bar\rho_v$ is unramified. The framed unramified fixed-determinant ring is formally smooth of relative dimension three:

$$
R_v^{\square,\mathrm{ur},\delta}
\simeq\mathcal O[[x_1,x_2,x_3]].
\tag{3.5}
$$

Its unframed tangent is

$$
L_v^{\mathrm{ur}}=H^1_{\mathrm{ur}}(K,W),
\qquad
\dim L_v^{\mathrm{ur}}=h_v.
\tag{3.6}
$$

If residual Frobenius is nonscalar, it is cyclic in dimension two. The unframed unramified fixed-determinant problem is then represented by one trace parameter. If Frobenius is scalar, trace and determinant do not classify matrices over nonreduced rings; one retains the framed ring.

Now suppose residual inertia factors through a finite quotient $H$ of order prime to $\ell$, and fix a compatible integral model

$$
\theta:H\to\operatorname{GL}_2(\mathcal O)
\tag{3.7}
$$

with determinant $\delta_v|_{I_K}$. The fixed-$\theta$ condition is a closed represented framed condition. Averaging over $H$ makes inertia rigid, and the Frobenius intertwiner varies in a smooth centralizer torsor. For odd $\ell$ the determinant derivative on that torsor is surjective, so

$$
R_v^{\square,\theta,\delta}
\text{ is formally smooth of relative dimension }3.
\tag{3.8}
$$

Its unframed tangent is again

$$
L_v^\theta=H^1_{\mathrm{ur}}(K,W),
\qquad
\dim L_v^\theta=h_v.
\tag{3.9}
$$

The conclusion uses the full integral representation $\theta$, not equality of characteristic polynomials on inertia. It does not cover finite inertia of order divisible by $\ell$.

### 3.3 Nonzero unipotent and Steinberg conditions

Choose tame generators $\tau$ and $\varphi$ with

$$
\varphi\tau\varphi^{-1}=\tau^q.
\tag{3.10}
$$

After a rigid scalar twist, a rank-one unipotent representation has

$$
\rho(\tau)=1+N,
\qquad
N^2=0,
\qquad
FNF^{-1}=qN.
\tag{3.11}
$$

Before imposing a Steinberg branch, there is a larger framed **unipotent incidence problem**. It records $F$, a square-zero operator $N$, and, when needed, a direct-summand line containing $\operatorname{im}N$ and contained in $\ker N$. Besides (3.11), impose $\operatorname{tr}N=\det N=0$ and the fixed-determinant equation on $F$. These are closed matrix and flag equations, so the enhanced framed problem is represented. It contains the divisor $N=0$, the rank-one loci with their possible orientations, and exceptional intersections; it is not asserted to be irreducible or smooth.

Its tangent space is the kernel of the derivative of all these equations. Writing

$$
F=(1+\epsilon X)\bar F,
\qquad
N=\bar N+\epsilon Y,
\tag{3.11a}
$$

the two basic linearized equations are

$$
\bar NY+Y\bar N=0,
\tag{3.11b}
$$

$$
[X,q\bar N]+\bar F Y\bar F^{-1}-qY=0,
\tag{3.11c}
$$

together with the trace, determinant, and flag derivatives. At $\bar N=0$, equation (3.11b) imposes nothing to first order and (3.11c) selects the $q$-eigenspace of $\operatorname{Ad}_{\bar F}$ for $Y$. At a scalar or repeated-root point this eigenspace and the flag tangent can jump. Thus representability of the incidence scheme supplies no uniform tangent dimension, component count, or relation defect. Those must be read from (3.11b)--(3.11c) at the actual residual point.

If the residual operator $\bar N$ is nonzero, its kernel is the unique residual stable line and remains a direct summand in every lift. Nonvanishing is forced by reduction and is therefore compatible with every coefficient map. With fixed determinant and fixed unramified Steinberg character $\epsilon_v$, the local shape is

$$
\rho_A|_{G_K}\sim
\begin{pmatrix}
\epsilon_v\chi_\ell&c_A\\
0&\epsilon_v
\end{pmatrix},
\qquad
\bar c|_{I_K}\ne0.
\tag{3.12}
$$

When $q\not\equiv1\pmod\ell$, a strict diagonal conjugation normalizes the primitive monodromy, and a strict upper-triangular conjugation removes the remaining Frobenius extension coordinate. Thus the unframed condition is rigid. Under scalar residual centralizer for the conditioned object,

$$
L_v^{\mathrm{st,min}}=0,
\qquad
R_v^{\square,\mathrm{st,min},\delta}
\simeq\mathcal O[[x_1,x_2,x_3]].
\tag{3.13}
$$

The three variables are framing directions. This is the nonzero-monodromy minimal condition used in Book 155. The further exclusion $q\not\equiv-1\pmod\ell$ is not needed for the elementary normalization itself, but is needed for the primitive newvector and determinant factors used later.

If one writes only the two equations in (3.11) at $N=0$, an extraneous unramified locus appears. The represented closed special condition must also retain the stable line and its two diagonal characters. In the scalar case the line is genuine enhancement data, not a component that can be forgotten.

### 3.4 The closed level-raising special component

Suppose $\bar\rho_v$ is unramified and residual Frobenius has distinct eigenvalues $\bar\alpha,\bar\beta$ satisfying

$$
\bar\alpha=q\bar\beta.
\tag{3.14}
$$

Choose the $\bar\alpha$-line. Fix an unramified character $\psi$ such that

$$
\psi^2\chi_\ell=\delta_v.
\tag{3.15}
$$

The enhanced special condition consists of extensions

$$
0\longrightarrow A(\psi\chi_\ell)
\longrightarrow V_A
\longrightarrow A(\psi)
\longrightarrow0
\tag{3.16}
$$

with the chosen line and with tame monodromy allowed to vanish. Since the residual diagonal characters are distinct, the line lifts uniquely. The fixed characters remove all unramified scalar motion. The extension group has one tame direction and no unramified direction. Therefore

$$
L_v^{\mathrm{sp}}\simeq k,
\qquad
\dim L_v^{\mathrm{sp}}=1=h_v.
\tag{3.17}
$$

In this fixed-character clean case, smoothness can be proved directly rather than imported from a blanket special-ring assertion. Local Kummer theory gives

$$
H^1(K,\mathcal O(1))
\simeq
\widehat{K^\times}_{\,\ell}\otimes_{\mathbf Z_\ell}\mathcal O
\simeq\mathcal O,
\tag{3.17a}
$$

because $q-1$ is an $\ell$-adic unit and the pro-$p$ principal units contribute no pro-$\ell$ quotient. Formation of this group commutes with Artinian coefficient quotients, so every extension class lifts across a small extension. The two frame-position directions supplement this free monodromy parameter, giving

$$
R_v^{\square,\mathrm{sp},\delta}
\simeq\mathcal O[[m_v,y_v,z_v]]
\tag{3.18}
$$

in this clean regular case. This proof uses fixed diagonal characters, $q\not\equiv1\pmod\ell$, and the unique residual line. It is not a smoothness claim for the general special incidence scheme of Section 3.3. The genuine Steinberg locus is $m_v\ne0$ on the generic fiber. The divisor $m_v=0$ is the level-raising intersection with the unramified condition. Nonzero monodromy is open here; it is not an Artinian deformation subfunctor.

The opposite orientation occurs when $\bar\beta=q\bar\alpha$. These are the two level-raising components. If $q\equiv1\pmod\ell$, the eigenvalues in (3.14) coincide and the preceding descent of the line fails. If $q\equiv-1\pmod\ell$, the enhanced lines remain distinct, but the trace congruence sees both signs and both Gram factors become nonunits. Both cases are excluded from the clean theorem.

### 3.5 Tamely ramified principal-series conditions

There are two different tame principal-series problems.

In the **rigid-type case**, choose two finite characters $\theta_1,\theta_2$ of inertia of order prime to $\ell$, stable under Frobenius in the prescribed order, with

$$
\theta_1\theta_2=\delta_v|_{I_K}.
\tag{3.19}
$$

Assume their residual characters are distinct. The inertia idempotents lift uniquely, so every deformation in the fixed-type condition splits into two character lines. With determinant fixed, one unramified ratio character remains. Thus the unframed tangent has dimension one, $h_v=1$, and the framed ring is smooth of relative dimension three:

$$
R_v^{\square,\mathrm{ps}(\theta_1,\theta_2),\delta}
\simeq\mathcal O[[u_v,y_v,z_v]].
\tag{3.20}
$$

This is a specialization of the prime-to-$\ell$ fixed-type theorem, together with the unique idempotent decomposition.

In the **congruence-tame case**, the characteristic-zero characters may have $\ell$-power order and reduce to the same inertial character. The fixed finite-type theorem does not apply because averaging by the group order is unavailable. One must retain an ordered pair of lines and either fix the two integral characters or let them vary through a named finite group algebra. If the residual Frobenius eigenvalues are distinct, the ordered lines still lift uniquely. For fixed characters, the same one unramified ratio parameter gives an enhanced framed ring of the form (3.20). For a universal tame character of an $\ell$-group $\Delta_v$ that is a quotient of tame inertia on which the $q$-power relation is trivial, the ring is instead smooth of relative dimension three over $\mathcal O[\Delta_v]$:

$$
R_v^{\square,\mathrm{ps,univ},\delta}
\simeq\mathcal O[\Delta_v][[u_v,y_v,z_v]].
\tag{3.21}
$$

To justify (3.21), choose the first character on inertia and the first Frobenius value. The second character is forced by determinant. The tame relation holds because both characters are one dimensional. The two ordered line positions form the completed big cell of the flag pair. Conversely, the two stable lines diagonalize the representation and recover these data. This proves representability of the enhanced problem. Forgetting the lines at a scalar residual point is not covered by this argument.

The generic fiber of $\mathcal O[\Delta_v]$ is a product of character fields. Its factors are distinct tame-character components that can cross in the special fiber. A theorem about one chosen principal-series type must quotient to, or localize on, the corresponding character factor; the label “tame principal series” does not select it automatically.

### 3.6 The local dimension and framing table

The clean fixed-determinant cases can now be summarized. All dimensions are relative to $\mathcal O$, except that the universal tame row is relative to its displayed group algebra.

| Condition | Residual hypotheses | Unframed tangent | Framed ring or tangent |
|---|---|---:|---:|
| unrestricted | none beyond representability | $H^1(K,W)$ | tangent dimension $3+e_v$; smooth of dimension $3$ if $e_v=0$ |
| unramified | residual inertia trivial | $h_v$ | smooth dimension $3$ |
| fixed finite type | compatible prime-to-$\ell$ integral type | $h_v$ | smooth dimension $3$ |
| nonzero minimal Steinberg | primitive residual monodromy, fixed sign, $q\not\equiv1$ | $0=h_v$ in the clean case | smooth dimension $3$ |
| level-raising special | unramified, distinct roots with ratio $q^{\pm1}$ | $1=h_v$ | smooth dimension $3$ |
| ordered tame principal series | regular ordered lines and fixed tame characters | $1=h_v$ | smooth dimension $3$ |
| general unipotent incidence | arbitrary $N$, possibly scalar Frobenius | derivative kernel of all equations | no uniform smoothness or component count |

The equality $\dim L_v=h_v$ is the neutral tangent identity used in balanced global problems. It holds in every clean row except the unrestricted row with $e_v\ne0$. A table entry is not a substitute for checking determinant compatibility, conductor, line descent, and automorphic realization.

## 4. The coefficient prime

At a place above $\ell$, finite flatness is an integral condition on every torsion quotient. It is neither unramifiedness nor an ordinary filtration. The exact scope of the available local theorem determines the global numerical ledger.

### 4.1 The exact finite-flat condition

Let $v\mid\ell$ and $K=F_v$. For an Artinian coefficient algebra $A$, a lift $V_A$ is finite flat if there is a finite locally free commutative group scheme over $\mathcal O_K$, with an $A$-action, whose generic geometric points are $V_A$. Membership is existential: a model witnesses the condition but is not silently added to the deformation object.

The condition is stable under strict equivalence and every coefficient map. It is represented by a quotient of the ambient framed ring. Under scalar residual endomorphisms the unframed condition is represented as well. Cartier duality identifies the correct dual tangent condition only after the compatible pairing is supplied; it does not make every finite-flat subspace self-orthogonal by name.

For a weight-two determinant

$$
\det V_A=A(\psi\chi_\ell),
\tag{4.1}
$$

the reduction to the cyclotomic-determinant theorem requires more than the
character $\psi$ itself. One must have a finite-order integral character
$\eta$ with

$$
\eta^2=\psi|_{G_K},
\tag{4.1a}
$$

possibly after an allowed coefficient extension, and twisting by
$\eta^{\pm1}$ must extend through the finite-flat integral category. One then
twists by $\eta^{-1}$, applies the type-$(0,1)$ theory, and twists back. A
ramified twist not known to extend integrally is not harmless, and a
finite-order determinant factor with no such square root is not covered by
this reduction.

### 4.2 The power-series theorem and its range

Assume

$$
K/\mathbf Q_\ell\text{ is unramified of degree }f_v,
\qquad \ell>2,
\tag{4.2}
$$

$\bar\rho_v\otimes\bar\eta^{-1}$ is finite flat with cyclotomic determinant
for a character $\eta$ satisfying Section 4.1, and

$$
\operatorname{End}_{k[G_K]}(\bar\rho_v)=k.
\tag{4.3}
$$

The full existential finite-flat condition is then formally smooth. Its unframed fixed-determinant ring and framed ring are

$$
R_v^{\mathrm{fl},\delta}
\simeq\mathcal O[[x_{v,1},\ldots,x_{v,f_v}]],
\tag{4.4}
$$

$$
R_v^{\square,\mathrm{fl},\delta}
\simeq\mathcal O[[x_{v,1},\ldots,x_{v,f_v},
y_{v,1},y_{v,2},y_{v,3}]].
\tag{4.5}
$$

Thus

$$
\dim L_v^{\mathrm{fl}}=f_v,
\qquad
\dim t_v^{\square,\mathrm{fl}}=f_v+3.
\tag{4.6}
$$

This includes irreducible, supersingular, and nonsplit ordinary residual shapes. It does not require ambient $H^2(K,W)$ to vanish. At a split sum of distinct characters the framed ring is still smooth of dimension $f_v+3$, but a coarse unframed universal ring is not asserted.

For ramified $K/\mathbf Q_\ell$, Book 67 gives only

$$
R_v^{\mathrm{fl},\delta}
\simeq\mathcal O[[X_1,\ldots,X_r]]/J
\tag{4.7}
$$

with $r$ equal to the actual finite-flat tangent dimension. The ideal $J$ remains until a separate integral classification and liftability theorem removes it. At $\ell=2$, even the trace-zero simplification behind (4.4)--(4.6) is unavailable.

### 4.3 Ordinary and crystalline conditions are different inputs

An ordinary condition chooses a stable line and prescribes the two characters on the line and quotient. A crystalline condition prescribes a rational Hodge type and often a generic inertial type. Neither is identical to the existential finite-flat condition.

A supersingular finite-flat representation need not have an ordinary line. An ordinary representation of a different weight or with a highly ramified quotient need not be finite flat of type $(0,1)$. A statement that a characteristic-zero point has Hodge--Tate weights $0$ and $1$ does not by itself prove that every Artinian quotient has an integral finite-flat model.

Accordingly this book uses (4.4) at the coefficient prime in the absolutely irreducible Taylor--Wiles theorem. An ordinary or crystalline replacement is permitted only under a separately stated package containing:

1. a represented integral local condition;
2. its exact framed dimension and component structure;
3. local--global compatibility for the Hecke-valued family on every Artinian quotient;
4. a duality and determinant-line comparison; and
5. automorphic support on the component containing the target.

Chapter 17 states the distinct ordinary residually reducible theorem. It is never substituted for the finite-flat theorem merely because both use weight two.

### 4.4 Restriction and finite-flat component control

If $K'/K$ is a finite extension, base change of a finite-flat model proves that restriction of a finite-flat representation remains finite flat. The converse is descent and requires effective descent data. Potential finite flatness over $K'$ therefore does not imply finite flatness over $K$.

Even upward restriction can change the local deformation geometry. Residual endomorphisms can grow, an irreducible representation can become reducible, and two generic components can merge after restriction. In the unramified low-weight Schur range, (4.4) is a regular local domain and there is one local component. Outside that range a component-switching argument must track the map

$$
R_{K'}^{\square,\mathrm{fl}}
\longrightarrow R_K^{\square,\mathrm{fl}}
\tag{4.8}
$$

induced contravariantly by restriction of deformation functors. Two $K$-points are compatible after base change only if their images in $\operatorname{Spec}R_{K'}[1/\ell]$ lie on the same specified component; equality of Hodge type is insufficient.

## 5. Conductors, local types, and component choices

The nonminimal set $P$ records where characteristic-zero ramification exceeds, or differs from, the minimal residual condition. To use it coherently, one must record conductor change, automorphic type, and deformation component separately.

### 5.1 Residual and characteristic-zero conductors

Write

$$
n_v(\bar\rho)=a(\bar\rho_v),
\qquad
n_v(\rho)=a(\rho_v)
\tag{5.1}
$$

for the residual and characteristic-zero conductor exponents away from $\ell$, with the tame square-zero definition used for unipotent infinite tame image. Reduction can lower conductor, so

$$
n_v(\bar\rho)<n_v(\rho)
\tag{5.2}
$$

is not exceptional. It is the basic nonminimal phenomenon.

The controlled cases have explicit costs.

| Local type of $\rho_v$ | Residual shape | $n_v(\rho)$ | Typical increase |
|---|---|---:|---:|
| unramified | unramified | $0$ | $0$ |
| fixed prime-to-$\ell$ type $\theta$ | reduction of $\theta$ | $a(\theta)$ | $0$ |
| nonzero unipotent or unramified Steinberg twist | nonzero unipotent | $1$ | $0$ |
| level-raising Steinberg | unramified | $1$ | $1$ |
| tame principal series $\chi_1\boxplus\chi_2$ | possibly unramified after reduction | $a(\chi_1)+a(\chi_2)$ | usually $2$ for inverse nontrivial tame characters with unramified determinant |
| ramified Steinberg twist $\operatorname{St}\otimes\mu$ | reduction of the twist | $2a(\mu)$ | depends on reduction of $\mu$ |

The principal-series sum is exact. It must not be replaced by the conductor of the central character $\chi_1\chi_2$, since the two ramified characters can cancel there. The Steinberg formula distinguishes an unramified twist, of exponent one, from a ramified twist, of exponent $2a(\mu)$.

An unrestricted local condition has no fixed conductor. A fixed generic inertial type can still meet several integral components, and conductor can jump at their boundary. Thus a conductor ideal is a consequence to be checked on a chosen component, not a definition of that component.

### 5.2 Scalar Frobenius and vexing primes

Let $v$ be a proposed level-raising prime. With trivial central character, the congruence

$$
T_v^2\equiv(q_v+1)^2\pmod{\mathfrak m}
\tag{5.3}
$$

says that residual Frobenius has eigenvalues

$$
\{\varepsilon q_v,\varepsilon\},
\qquad \varepsilon\in\{1,-1\}.
\tag{5.4}
$$

If $q_v\equiv1\pmod\ell$, these eigenvalues coincide. There is no residual eigenline that distinguishes a branch, the unframed cyclic-matrix coordinate fails, and the two degeneracy roots collide.

If $q_v\equiv-1\pmod\ell$, the two eigenvalues in (5.4) are distinct, but $q_v+1\equiv0$ and (5.3) forces $T_v\equiv0$. The trace congruence no longer distinguishes the two signs and both linear Gram factors are nonunits. The two residual $U_v$ roots are still distinct when $\ell$ is odd, so a refined $U_v$-selected theorem can separate them; the primitive one-factor determinant calculation cannot. This is the basic vexing situation for the present argument.

More generally, a prime is called **vexing for the chosen level comparison** when at least one of the following occurs:

1. residual Frobenius is scalar, so the ordered line is not intrinsic;
2. the two $U_v$ branches have the same residual root;
3. the Ihara or Gram determinant contains a nonunit stabilizer factor;
4. a type projector has denominator divisible by $\ell$; or
5. local component multiplicity exceeds one.

This is an operational definition. It records exactly which integral step fails. A different method can treat some such primes, but it must replace the failed step with a theorem rather than reuse the clean formula.

### 5.3 Type equality is not component equality

Let $x$ and $y$ be two characteristic-zero points of a framed local ring $R_v$. Suppose their Weil--Deligne parameters have the same inertial restriction. They can still lie on different irreducible components of $R_v[1/\ell]$. The differences can include monodromy rank, ordering of characters, extension orientation, or a component invisible after semisimplification.

The correct compatibility statement is:

$$
x,y\text{ factor through the same quotient }R_v^{\mathfrak p_v}
\text{ of (2.18).}
\tag{5.5}
$$

For a level-raising special condition, (5.5) includes the orientation of the stable line and the sign of the $U_v$ branch. For a tame principal series it includes the ordered pair of tame characters, modulo only the Weyl symmetry that is actually realized integrally. At a scalar point, a chosen flag chart is additional data and cannot be renamed a component of the coarse ring.

An automorphic point $y$ on one component proves only that this component is nonempty. To deduce modularity of a target point $x$, one needs either a componentwise $R=T$ theorem for their common component or a component-hopping theorem that carries automorphic support from $y$ to the component of $x$.

### 5.4 A controlled local datum

A fixed nonminimal place $v\nmid\ell$ is **controlled** if items 1--8 below
are recorded. Item 9 is the additional requirement for a relative numerical
comparison.

1. A framed closed local condition $D_v^P$ containing the residual point is represented.
2. Its determinant equals $\delta_v$ on every Artinian point.
3. Its tangent subspace $L_v^P$, exact Tate orthogonal, and complete obstruction theory are known.
4. Its framed ring is either explicitly smooth of dimension three or is presented with every local equation retained in the local base.
5. A generic component $\mathfrak p_v$ containing the target is specified.
6. The conductor and local automorphic type are constant on a named generic
   locus of that component, and the target lies in that locus. In particular,
   a target on the $N=0$ boundary of a closed special component is not
   relabelled Steinberg merely because the component has generically nonzero
   monodromy.
7. An integral type projector or newvector lattice is defined on the automorphic side.
8. Local--global compatibility places the Hecke-valued representation on the same quotient $R_v^{\mathfrak p_v}$.
9. For the relative numerical route, the local pairing factor used in the
   determinant comparison is computed and is a unit after any named
   congruence factor has been separated.

The clean local conditions of Chapter 3 satisfy items 1--6 under their stated
hypotheses. Items 7--8 are the integral level and reciprocity inputs of NM-I
and NM-II. Item 9 belongs only to NM-III's relative determinant part. Thus
the sharp direct route can use a controlled datum without assuming a local
determinant formula, while the numerical route adds exactly that formula.
This route-labelled package, rather than the adjective “nonminimal,” is what
later theorems use.

## 6. Level raising from degeneracy maps

Level raising begins with a congruence at a lower level and ends with an eigenclass that is new at one more prime. The bridge is integral linear algebra. Over the fraction field, the old and new summands are readily separated. Modulo $\varpi$, however, they meet exactly where the desired congruence occurs. One therefore needs a perfect lattice, two degeneracy maps, their adjoints, and a saturation theorem before the familiar quadratic congruence has any force.

Throughout this chapter let $p\nmid \ell$ be a finite place of $F$ at which the lower level is hyperspecial, the central character is unramified, and the residual maximal ideal $\mathfrak m$ is non-Eisenstein. To simplify the formulas, first suppose the central character is trivial and write $q=q_p$. The version with central character is obtained from the polynomial (1.7) and the corresponding adjoint normalization.

### 6.1 The two maps and their adjoints

Let $U$ be the lower compact open and let $U_0(p)$ be obtained by replacing $U_p$ with an Iwahori subgroup. Let

$$
M=M(U)_{\mathfrak m},
\qquad
N=M(U_0(p))_{\mathfrak m}
\tag{6.1}
$$

be localized integral Hecke modules. Depending on the global realization, these may be definite quaternionic functions or the relevant middle-degree cohomology modulo its controlled torsion. There are two maps induced by the two cosets adjacent to the hyperspecial vertex:

$$
d_1,d_2:M\longrightarrow N.
\tag{6.2}
$$

Their sum is the degeneracy map

$$
d=(d_1,d_2):M\oplus M\longrightarrow N.
\tag{6.3}
$$

Assume $M$ and $N$ carry perfect $\mathcal O$-pairings for which the prime-to-$p$ Hecke operators are self-adjoint after the standard involution. The adjoint map is

$$
d^*:N\longrightarrow M\oplus M.
\tag{6.4}
$$

The old lattice is $N^{\mathrm{old}}=\operatorname{im}d$. The orthogonal new lattice is

$$
N^{\mathrm{new}}=\ker d^*.
\tag{6.5}
$$

These definitions are integral. The quotient $N/N^{\mathrm{old}}$ need not be torsion-free, and its torsion is precisely one place where a naive characteristic-zero old/new decomposition loses the congruence being studied.

Under the normalization included in the integral level-control theorem, the four composites are

$$
d^*d=
\begin{pmatrix}
q+1&T_p\\
T_p&q+1
\end{pmatrix}.
\tag{6.6}
$$

Formula (6.6) is not a formal consequence of having two maps. It is a double-coset calculation together with a normalization of the pairings. If the central character is nontrivial, the lower-right entry and one off-diagonal entry acquire the corresponding $S_p$ factors; the invariant statement is that the determinant specializes to the discriminant of (1.7) at the special roots.

### 6.2 The Gram determinant and the congruence equation

Let $f\in M$ be an eigenvector with $T_p$-eigenvalue $a_p$. On the two-dimensional old plane generated by $d_1f,d_2f$, the determinant of the Gram matrix is

$$
\Delta_p(f)=(q+1)^2-a_p^2.
\tag{6.7}
$$

If this determinant is a unit, the old plane is a direct summand and has no congruence with the new lattice. If it is divisible by $\varpi$, the reduction of (6.6) has a nonzero kernel provided $f$ remains nonzero modulo $\varpi$. Hence the necessary level-raising congruence is

$$
a_p^2\equiv(q+1)^2\pmod\varpi.
\tag{6.8}
$$

Choose a sign $\varepsilon\in\{1,-1\}$ such that

$$
a_p\equiv\varepsilon(q+1)\pmod\varpi.
\tag{6.9}
$$

Then the vector $(1,-\varepsilon)$, with a harmless normalization depending on the chosen degeneracy convention, lies in the residual kernel. The two linear factors

$$
c_p^\varepsilon=q+1-\varepsilon a_p,
\qquad
c_p^{-\varepsilon}=q+1+\varepsilon a_p
\tag{6.10}
$$

have distinct roles. The first measures the chosen congruence. In the clean nonvexing case $q\not\equiv-1\pmod\ell$, the second is a unit. Thus the full Gram determinant and the chosen branch factor have the same valuation:

$$
\operatorname{ord}_\varpi\Delta_p(f)
=\operatorname{ord}_\varpi c_p^\varepsilon.
\tag{6.11}
$$

At $q\equiv-1\pmod\ell$, both factors in (6.10) can be nonunits. A branch-selected comparison may still exist, but (6.11) is false without a refined calculation.

The residual Galois interpretation of (6.8) is equally precise. With determinant $q$, the eigenvalues of $\bar\rho(\operatorname{Frob}_p)$ are

$$
\{\varepsilon q,\varepsilon\}.
\tag{6.12}
$$

When $q\not\equiv1\pmod\ell$ they are distinct and determine the oriented line needed by the local special condition of Section 3.4. Thus the degeneracy equation and the intersection equation (2.9) are two realizations of the same local condition.

### 6.3 The two $U_p$ branches

The Iwahori Hecke operator $U_p$ acts on the old plane with characteristic polynomial

$$
X^2-a_pX+q.
\tag{6.13}
$$

Under (6.9), its residual roots are

$$
\varepsilon,\qquad \varepsilon q.
\tag{6.14}
$$

If $q\not\equiv1\pmod\ell$, Hensel idempotents separate these two roots in the localized old algebra. The $U_p=\varepsilon$ branch is the one compatible with a weight-two Steinberg representation of sign $\varepsilon$ in the present normalization. The $U_p=\varepsilon q$ branch is its companion old stabilization. A projector chosen only after passing to the fraction field is not enough; NM-I requires the idempotent to preserve the integral lattice.

There are two different ambiguities that should not be confused. If $q\equiv1\pmod\ell$, the roots in (6.14) collide and even the ordered residual Frobenius line is lost. If $q\equiv-1\pmod\ell$, the two $U_p$ roots $\varepsilon$ and $-\varepsilon$ remain distinct because $\ell$ is odd, but (6.9) no longer determines $\varepsilon$ from $a_p$, and both Gram factors in (6.10) vanish residually. The latter case therefore needs a $U_p$-selected integral determinant theorem; it is not covered by the primitive one-factor formula.

On the genuinely new quotient, local newvector theory gives

$$
U_p^2=1
\tag{6.15}
$$

for trivial central character, and the sign of $U_p$ records the unramified twist of Steinberg. This is a characteristic-zero statement until the new quotient has been proved torsion-free and the Hecke operator has been shown to act integrally.

### 6.4 Ihara injectivity and saturation

The needed Ihara assertion has two clauses:

$$
\bar d:(M/\varpi M)^2\longrightarrow N/\varpi N
\quad\text{is injective},
\tag{6.16}
$$

and

$$
N/\operatorname{im}d\quad\text{is $\mathcal O$-torsion-free}
\tag{6.17}
$$

after localization at the relevant non-Eisenstein maximal ideal, or an equivalent saturated-image statement strong enough for the argument. The two clauses are related but neither follows merely from the existence of the degeneracy maps. In curve cohomology, (6.16) is normally a theorem about the special fiber or a group-action amalgam, while (6.17) requires control of component groups and integral cohomological torsion. In the definite setting they reduce to an integral statement about class-set lattices and stabilizers.

The hypotheses must exclude exactly the kernels that geometry permits: Eisenstein classes, residual one-dimensional quotients, and stabilizers whose orders are divisible by $\ell$. At a vexing prime one also needs a type-enhanced version, since an unlabelled scalar line can give an additional kernel.

Suppose (6.16)--(6.17) hold. The residual kernel of the Gram matrix does not mean that $d$ has a kernel; rather, it produces a vector $x\in M^2$ for which $d(x)$ is nonzero modulo $\varpi$ but is orthogonal modulo $\varpi$ to the old lattice. Perfectness then gives a nonzero class in

$$
N^{\mathrm{new}}/\varpi N^{\mathrm{new}}
\tag{6.18}
$$

with the same prime-to-$p$ eigenvalues and the selected $U_p$ sign. Saturation is what prevents this class from being merely the shadow of torsion in $N/N^{\mathrm{old}}$.

### 6.5 The integral level-raising theorem

We isolate the conclusion in the form used later.

**Theorem 6.1 (integral level raising at one prime).** Let $\mathfrak m$ be a non-Eisenstein residual maximal ideal of a lower-level Hecke order. Assume:

1. $\bar\rho_{\mathfrak m}$ is absolutely irreducible and unramified at $p$;
2. $q\not\equiv\pm1\pmod\ell$ and residual Frobenius has distinct eigenvalues;
3. the signed congruence (6.9) holds;
4. the localized modules are finite free over $\mathcal O$, carry the perfect pairings used in (6.6), and the degeneracy image satisfies (6.16)--(6.17);
5. the $p$-new quotient is Hecke-stable and local--global compatibility identifies its $U_p=\varepsilon$ localization with the special local deformation condition; and
6. the proof of clauses 4 and 5 is independent of the modularity-lifting theorem for the nonminimal deformation problem.

Then the $p$-new, $U_p=\varepsilon$ Hecke order has a maximal ideal whose residual prime-to-$p$ eigensystem is $\mathfrak m$. Equivalently, there is a characteristic-zero cuspidal automorphic eigenform congruent to the lower-level form and Steinberg of sign $\varepsilon$ at $p$.

**Proof.** Equations (6.6), (6.9), and perfectness produce the nonzero residual class (6.18). Ihara injectivity prevents it from coming from a zero lower-level vector, and saturation places it in the reduction of an integral torsion-free new lattice. The commuting Hecke algebra acts on the finite $k$-space generated by this class through a residual character. Localizing the finite torsion-free new Hecke module at that character gives a nonzero module. Its faithful Hecke order is finite over $\mathcal O$; a minimal prime above the localization has characteristic zero. The associated eigencharacter lifts the residual system. The integral $U_p$ projector selects $\varepsilon$, and clause 5 identifies the local representation as Steinberg on the chosen component. $\square$

The theorem produces a congruent automorphic point. It says nothing yet about a separately given Galois lift on the same local component. That identification is the work of Chapters 11--14.

## 7. Level lowering and its noncircular hypotheses

Level lowering runs in the opposite automorphic direction but is not the inverse of level raising. A representation can be new at $p$ in characteristic zero while its reduction is unramified. Removing $p$ from the residual automorphic level requires the integral geometry of the special fiber. A dimension comparison or the statement that the residual Galois representation is unramified does not by itself construct the lower-level eigenclass.

### 7.1 What must be lowered

Let $\pi$ be a weight-two automorphic representation contributing to a lattice $N$ at level $U_0(p)$, new at $p$, and let $\mathfrak m$ be the maximal ideal cut out by its residual eigensystem. Suppose

$$
\bar\rho_{\mathfrak m}|_{G_{F_p}}
\text{ is unramified}.
\tag{7.1}
$$

The desired conclusion is not that the characteristic-zero representation $\pi_p$ becomes unramified. It is that the same residual system of prime-to-$p$ eigenvalues occurs in the lower module $M(U)$. In symbols, if $\mathbb T^{(p)}$ denotes the Hecke algebra away from $p$, one wants

$$
M(U)_{\mathfrak m^{(p)}}\ne0.
\tag{7.2}
$$

Only after (7.2) may one choose a lower-level characteristic-zero lift of the residual system. That lift need not be congruent to $\pi$ to arbitrarily high $\varpi$-power, and it need not remember the $U_p$ sign.

### 7.2 The monodromy and component-group sequence

For a semistable curve realization, let $X_p$ be the character lattice of the toric part of the special fiber and let $\Phi_p$ be the component group. The monodromy pairing gives an exact sequence of localized lattices

$$
0\longrightarrow X_p
\xrightarrow{\,\mu_p\,}X_p^\vee
\longrightarrow\Phi_p\longrightarrow0.
\tag{7.3}
$$

The vanishing-cycles sequence connects $X_p$, the $p$-new part of $N$, and the lower-level module reached by the two degeneracy maps. In the definite realization the same algebra appears as the incidence sequence for the quotient of the Bruhat--Tits tree. An integral level-lowering input must identify all of the following after localization:

- the old image with the image of the two boundary maps;
- the new quotient with the appropriate character or cocharacter lattice;
- the Galois inertia operator with the monodromy map $\mu_p$;
- the component group with the failure of saturation; and
- the prime-to-$p$ Hecke action on every term.

The schematic sequence is

```text
 lower level^2  --degeneracy-->  Iwahori level  -->  new lattice
       |                                  |              |
       |                                  |              | monodromy
       v                                  v              v
 boundary lattice  --------------->  character lattice -> component group
```

No arrow in this diagram is an equality without the integral comparison theorem. In particular, the characteristic-zero decomposition of the middle term does not determine the torsion in the last term.

Under the comparison, unramifiedness (7.1) says that the residual monodromy operator vanishes. If no lower-level class existed, the exact sequence would force the localized new residual class to inject into a primitive monodromy quotient. The monodromy pairing would then give a nonzero inertial extension class, contradicting (7.1), unless the class lies in a component-group or scalar exceptional kernel. Ihara saturation and the nonvexing hypotheses remove precisely those alternatives.

### 7.3 The integral level-lowering theorem

**Theorem 7.1 (integral level lowering at one prime).** Let $p\nmid\ell$ and let $\mathfrak m$ be a non-Eisenstein maximal ideal occurring in the $p$-new quotient at Iwahori level. Assume:

1. $\bar\rho_{\mathfrak m}$ is absolutely irreducible and $\bar\rho_{\mathfrak m}|_{G_{F_p}}$ is unramified;
2. $q_p\not\equiv\pm1\pmod\ell$, residual Frobenius is nonscalar, and the residual representation has no local or global self-twist that identifies the two branches;
3. the degeneracy map satisfies the localized Ihara injectivity and saturation assertions (6.16)--(6.17);
4. the exact monodromy/component-group comparison of Section 7.2 holds integrally, with no $\ell$-torsion hidden in a stabilizer or component group;
5. residual multiplicity one identifies the localized Galois representation on the new lattice; and
6. these geometric and representation-theoretic assertions are established without using the nonminimal modularity-lifting conclusion.

Then the prime-to-$p$ residual eigensystem occurs at the lower level, as in (7.2).

**Proof.** Localize (7.3) and the vanishing-cycles sequence at $\mathfrak m$. Suppose (7.2) failed. Exactness and Ihara injectivity then place the nonzero new residual eigenspace in the primitive quotient of $X_p/\varpi X_p$. Saturation rules out a lift from component-group torsion. By residual multiplicity one, the monodromy endomorphism on that eigenspace is the tame inertia operator of $\bar\rho_{\mathfrak m}$. The primitive pairing makes this operator nonzero unless the vector lies in a scalar or branch-collision kernel. Clause 2 excludes that kernel. This contradicts (7.1), so the lower localization is nonzero. $\square$

Iterating the theorem lowers a set of primes only if its hypotheses remain true after every step. The order can matter: localization at one lower level can change multiplicities or expose torsion at the next prime. A simultaneous theorem avoids this issue only when its multi-prime degeneration complex is proved exact and saturated.

### 7.4 Why residual conditions matter

Four common shortcuts fail for different reasons.

First, unramified semisimplification does not imply unramifiedness of the residual representation. A nonzero unipotent extension has trivial inertial semisimplification but cannot be lowered by Theorem 7.1.

Second, scalar Frobenius leaves no canonical eigenline. The local Galois condition can then be unramified while the automorphic class survives in a flag-dependent component-group kernel.

Third, $q_p\equiv-1\pmod\ell$ makes both Gram factors nonprimitive. A nonzero congruence class need not select the intended sign, so a branch-refined theorem is required.

Fourth, residual reducibility permits Eisenstein boundary classes. Ihara injectivity in a cuspidal characteristic-zero space does not remove them modulo $\ell$.

The theorem is therefore an input to modularity lifting, not an output smuggled back into its proof. In later applications every lowered prime will be accompanied by a citation to the actual geometric saturation theorem used there.

## 8. Hecke modules, congruence ideals, and the price of level

The extra ramification at $P$ has a numerical cost. On the deformation side it changes local tangent and relation complexes. On the automorphic side it changes the integral lattice and its congruence ideal. A nonminimal numerical argument succeeds only when these two costs are identified one factor at a time.

### 8.1 Minimal and enlarged Hecke orders

Let $M^{\min}$ be the localized minimal module and let $M^P$ be the module at the level and type prescribed by the controlled datum at $P$. Define

$$
\mathbb T^{\min}
=\operatorname{im}\bigl(\mathbb T^{\mathrm{abs}}\to
\operatorname{End}_{\mathcal O}(M^{\min})\bigr),
\tag{8.1}
$$

$$
\mathbb T^P
=\operatorname{im}\bigl(\mathbb T^{\mathrm{abs},P}\to
\operatorname{End}_{\mathcal O}(M^P)\bigr).
\tag{8.2}
$$

These are faithful Hecke orders, not abstract algebras with every formally named operator. Operators away from $P$ give a common polynomial algebra mapping to both orders. There is generally no canonical map

$$
\mathbb T^P\longrightarrow\mathbb T^{\min}
\quad\text{or}\quad
\mathbb T^{\min}\longrightarrow\mathbb T^P
\tag{8.3}
$$

because the kernels of the two faithful actions need not contain one another. A map exists only after an old projector, a degeneracy correspondence, or a type comparison has produced an actual module map and its compatibility with the chosen faithful quotients has been checked.

For the exact clean rational datum of Book 155, the minimal objects come with
substantially more than a ring isomorphism. That book proves

$$
R^{\min}\simeq\mathbb T^{\min},
\qquad
M^{\min}\simeq\mathbb T^{\min}
\tag{8.3a}
$$

with the second module free of rank one and faithful, and it proves the
perfect primary--companion pairing. The common ring is finite flat,
complete-intersection, reduced, and Gorenstein. Only after establishing
(8.3a), Book 155 proves its intrinsic Fitting--congruence equality. These are
valid base-level inputs after the coefficient operation of Section 8.3; none
of them supplies an enlarged-level lattice, an action on a new component,
or a local factor at a prime of $P$.

On the Galois side, by contrast, weakening a represented local condition gives the quotient map in the direction fixed in (2.3). The two categories therefore do not come with parallel arrows merely because one level is called larger.

### 8.2 Old, new, and saturated lattices

For one added prime, define

$$
M^{\mathrm{old}}=\operatorname{im}(d:M^{\min,2}\to M^p),
\tag{8.4}
$$

$$
M^{\mathrm{sat-old}}
=M^p\cap(M^{\mathrm{old}}\otimes_{\mathcal O}E),
\tag{8.5}
$$

inside $M^p\otimes E$. There are two quotients:

$$
M^p/M^{\mathrm{old}},
\qquad
M^p/M^{\mathrm{sat-old}}.
\tag{8.6}
$$

The first remembers integral congruence torsion; the second is torsion-free and realizes the characteristic-zero new quotient. Their difference is

$$
M^{\mathrm{sat-old}}/M^{\mathrm{old}},
\tag{8.7}
$$

the old/new congruence module. If the old image is already saturated, (8.7) vanishes, but the orthogonal old and new lattices can still meet modulo $\varpi$ because the pairing discriminant is nonunit. Consequently “saturated old image” and “no level-raising congruence” are not synonymous.

At several primes, oldness is a cubical diagram indexed by subsets of $P$. Its total degeneracy complex must be exact and saturated. Pairwise saturation alone does not rule out higher $\operatorname{Tor}$ among the separate old quotients.

### 8.3 Cotangent modules and local congruence factors

After any finite coefficient extension needed to realize the distinguished
point, base-change the rings along the resulting finite flat map of
coefficient DVRs, then localize and complete at the extended augmentation.
Thus fix one coefficient DVR
$\mathcal O'$ and let $A$ be a finite flat local $\mathcal O'$-algebra with an
$\mathcal O'$-algebra augmentation $\lambda:A\to\mathcal O'$. Put

$$
\mathfrak p_\lambda=\ker\lambda,
\qquad
\Phi_{A,\lambda}=\mathfrak p_\lambda/\mathfrak p_\lambda^2,
\tag{8.8}
$$

and define the congruence ideal

$$
\eta_{A,\lambda}
=\lambda\bigl(\operatorname{Ann}_A\mathfrak p_\lambda\bigr)
\subseteq\mathcal O'.
\tag{8.9}
$$

For a complete-intersection order with a perfect eigenlattice, the Fitting ideal of the cotangent module and the congruence ideal agree. Outside that situation there is only the inequality supplied by the numerical criterion; equality must not be presumed.

For a linked minimal augmentation
$\lambda_{\min}:\mathbb T^{\min}\to\mathcal O'$, and in the
trivial-central-character normalization used for the clean formula, put
$a_p=\lambda_{\min}(T_p)$ and choose the sign $\varepsilon$. The normalized
local comparison complex has determinant

$$
c_p^\varepsilon=q_p+1-\varepsilon a_p.
\tag{8.10}
$$

Its opposite determinant factor is a unit under $q_p\not\equiv-1\pmod\ell$. The full Gram determinant is

$$
(q_p+1)^2-a_p^2
=c_p^\varepsilon c_p^{-\varepsilon}.
\tag{8.11}
$$

For an ordered tame principal-series type or another represented type, there is no universal substitute obtained by inserting its conductor into (8.10). Define instead

$$
c_v(\tau_v,\mathfrak p_v)
=\det C_v^\bullet
\quad\text{up to }\mathcal O'^{\times},
\tag{8.12}
$$

where $C_v^\bullet$ is the explicitly normalized perfect two-term complex comparing the lower lattice with the integral $\tau_v$-type lattice on the chosen component. NM-III asserts that this complex exists, is perfect, and matches the Kodaira--Spencer map of the local deformation quotient. Its determinant can depend on Gauss sums, character differences, and stabilizer orders. Conductor alone does not determine it.

### 8.4 One-prime and many-prime cost formulas

Fix compatible base and enlarged augmentations. For the clean rational
cyclotomic base in the range of Book 155, the boxed equality in Section 12.6
of that book gives,
after the finite coefficient extension and localized completion of Section
8.3,

$$
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^{\min},\lambda_{\min}}
=\eta_{\mathbb T^{\min},\lambda_{\min}}.
\tag{8.12a}
$$

This is a theorem exported by Book 155, not a determinant hypothesis and not
an inference from ring equality alone. The base-changed common
complete-intersection presentation gives the displayed equality at the
extended augmentation. Outside Book 155's exact range, a relative numerical
argument must name an analogous proved base equality; the direct patching
route does not need one.

Under the independent relative comparison hypotheses at the added places,
adding one clean Steinberg prime gives

$$
\eta_{\mathbb T^p,\lambda_p}
=\eta_{\mathbb T^{\min},\lambda_{\min}}
\bigl(c_p^\varepsilon\bigr)
\tag{8.13}
$$

and

$$
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^p,\lambda_p}
=
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^{\min},\lambda_{\min}}
\bigl(c_p^\varepsilon\bigr),
\tag{8.14}
$$

up to a common unit. Equations (8.13) and (8.14) are two theorems, not two definitions. The first is an automorphic determinant calculation; the second is a deformation-theoretic cotangent calculation. Their equality is the local numerical bridge.

If $P$ contains several primes and the multi-prime comparison complex is the derived tensor product of the local complexes without higher torsion, then

$$
\eta_{\mathbb T^P,\lambda_P}
=\eta_{\mathbb T^{\min},\lambda_{\min}}
\prod_{v\in P}\bigl(c_v\bigr),
\tag{8.15}
$$

$$
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^P,\lambda_P}
=
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^{\min},\lambda_{\min}}
\prod_{v\in P}\bigl(c_v\bigr).
\tag{8.16}
$$

Combining (8.12a) with (8.15)--(8.16) gives

$$
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^P,\lambda_P}
=\eta_{\mathbb T^P,\lambda_P}.
\tag{8.16a}
$$

Thus the only new determinant input in the clean relative route is the
matching of the local nonminimal factors and any higher-torsion factor.

Taking lengths gives the numerical price of the fixed nonminimal set:

$$
\operatorname{length}_{\mathcal O'}\Phi_{R^P,\lambda_P}
-\operatorname{length}_{\mathcal O'}\Phi_{R^{\min},\lambda_{\min}}
=\sum_{v\in P}\operatorname{ord}_{\varpi'}c_v,
\tag{8.17}
$$

and the same formula for the congruence module. If a higher $\operatorname{Tor}$ group is nonzero, its Fitting ideal is an additional factor and (8.15)--(8.17) are false as written.

These formulas explain why level raising is insufficient by itself. It supplies an augmentation $\lambda_P$ on some raised Hecke component. To reach a prescribed target point, the deformation ring at that point must have the same local factors and the global cotangent comparison must connect its augmentation to $\lambda_P$. Chapters 11--14 provide precisely that connection.

## 9. Fixed nonminimal primes and Taylor--Wiles primes

The set $P$ is fixed by the target representation. Taylor--Wiles sets $Q_n$ are chosen to kill a dual Selmer group and vary with $n$. Treating these two kinds of primes as one auxiliary level obscures both the local deformation problem and the automorphic augmentation. This chapter keeps them disjoint and recomputes the complete framed ledger.

### 9.1 Recomputing dual Selmer

Let $\mathcal L_P=(L_v^P)_v$ be the Selmer structure defined by the nonminimal datum. Its absolute dual Selmer dimension is

$$
q_P=h^1_{\mathcal L_P^\perp}(F,W(1)).
\tag{9.1}
$$

This number must be calculated after the conditions at $P$ have been imposed. The comparison sequence (2.13) shows that $q_P$ can be smaller than, equal to, or larger than the minimal dual Selmer dimension, depending on the localization map. There is no formula $q_P=q_{\min}+|P|$.

Assume the residual image satisfies the prime-detection hypothesis of the Taylor--Wiles construction and that the determinant obstruction and global self-twist obstruction vanish. Then for every sufficiently large $n$ one may choose a set

$$
Q_n=\{v_1,\ldots,v_{q_P}\}
\tag{9.2}
$$

such that:

1. $Q_n$ is disjoint from $S_0\cup P$;
2. $q_v\equiv1\pmod{\ell^n}$ for $v\in Q_n$;
3. $\bar\rho(\operatorname{Frob}_v)$ has two distinct eigenvalues with a chosen ordering; and
4. the corresponding localization functionals form a basis of the dual of (9.1).

The enlarged ordered conditions at $Q_n$ then kill the dual Selmer group. If the restriction of $\bar\rho$ to a field used in a preceding base change has acquired a self-twist or become inadequate, the Chebotarev prime-selection argument no longer supplies clause 4. Adequacy must therefore be checked over the field on which patching is actually performed.

### 9.2 Two disjoint kinds of auxiliary level

At $v\in P$, the local ring is fixed once and for all:

$$
R_v^{\square,P}=R_v^{\square,\mathcal D_v^P,\mathfrak p_v}.
\tag{9.3}
$$

It carries no Taylor--Wiles diamond variable. At $v\in Q_n$, the ordered Taylor--Wiles ring has the form

$$
R_v^{\square,\mathrm{TW}}
\simeq
\mathcal O[\Delta_v(n)][[X_v,Y_v,Z_v]],
\tag{9.4}
$$

where $\Delta_v(n)$ is the maximal quotient of the residue-field units of exponent dividing $\ell^n$. The variable $X_v$ moves the ordered unramified Frobenius root, while $Y_v,Z_v$ move its line inside the chosen frame. The tautological inertia character and its inverse occur on the two ordered lines so that the determinant remains $\delta$.

Set

$$
\Delta_n=\prod_{v\in Q_n}\Delta_v(n),
\qquad
\Lambda_n=\mathcal O[\Delta_n],
\qquad
\mathfrak a_n=\ker(\Lambda_n\to\mathcal O).
\tag{9.5}
$$

The framed local base is

$$
R_{\mathrm{loc},n}^P
=
\widehat\bigotimes_{v\in S_f\cup P\cup Q_n,\mathcal O}
R_v^{\square,\mathcal D_{v,n}},
\tag{9.6}
$$

viewed as a $\Lambda_n$-algebra through the factors (9.4). Killing diamonds removes only the tame characters at $Q_n$:

$$
R_n^P/\mathfrak a_nR_n^P\simeq R^P.
\tag{9.7}
$$

It does not remove $P$. Replacing the right side of (9.7) by $R^{\min}$ would confuse fixed ramification with patching level and would patch the wrong problem.

### 9.3 Diamond actions and paired $U/V$ modules

On the automorphic side, use three levels at every $v\in Q_n$: hyperspecial, Iwahori, and a deep subgroup whose quotient is $\Delta_v(n)$. The diagonal-ratio convention is chosen so that scalar matrices act trivially and so that the two tautological inertial characters are inverse to one another.

At a Taylor--Wiles prime there are two opposite correspondences, denoted $U_v$ and $V_v$, with $U_v^*=V_v$. One operator follows the chosen Frobenius line; the other is its adjoint correspondence. Both are retained until the full-Iwahori oldness and saturation comparison has been proved. Only then form the primary generalized $U$-block and the companion generalized $V$-block:

$$
M_n^{P,+},
\qquad
M_n^{P,-}.
\tag{9.7a}
$$

The sign labels primary and companion; they do not identify the modules. At a fixed type in $P$, the minus block uses the explicitly identified adjoint type lattice when the chosen projector is not self-adjoint. The perfect geometric pairing restricts to

$$
[\ ,\ ]_n:
M_n^{P,+}\times M_n^{P,-}\longrightarrow\Lambda_n,
\qquad
[\lambda x,y]_n=\lambda[x,y]_n,
\quad
[x,\lambda y]_n=[x,y]_n\iota(\lambda),
\tag{9.7b}
$$

where $\iota(\delta)=\delta^{-1}$. If $\mathbb T_n^{P,+}$ and $\mathbb T_n^{P,-}$ are the faithful acting orders, adjunction gives an isomorphism

$$
\mathbb T_n^{P,+}\xrightarrow{\sim}\mathbb T_n^{P,-},
\qquad
t\longmapsto t^\dagger.
\tag{9.7c}
$$

This is the companion-module form of duality in Book 73. It does not declare the primary $U$-projector self-adjoint.

Both branch modules must be finite free over $\Lambda_n$. Freeness is proved from an actual free action on class-set fibers in the definite case, or from the corresponding finite étale covering together with torsion control in the curve case. Equality of $\mathcal O$-ranks after augmentation is not enough. Put $M^{P,+}=M^P$ and let $M^{P,-}$ be its adjoint base-level type lattice. The augmentation identities required for patching are

$$
M_n^{P,\pm}/\mathfrak a_nM_n^{P,\pm}
\simeq M^{P,\pm},
\tag{9.8}
$$

and the faithful Hecke orders must satisfy the compatible identities

$$
\mathbb T_n^{P,\pm}/\mathfrak a_n\mathbb T_n^{P,\pm}
\simeq\mathbb T^{P,\pm},
\qquad
\mathbb T^{P,+}=\mathbb T^P,
\tag{9.9}
$$

with the two base orders identified by the augmentation of (9.7c). Selecting the $U_v$ root over the fraction field and discarding the $V_v$ companion can turn an integral new quotient into invisible torsion and destroys the duality axiom.

At a fixed prime $p\in P$, the pair has a different job. The $U_p$ branch selects the special sign or ordered type, while its adjoint controls the discriminant factor $c_p$. There is no diamond action at $p$. Thus the schematic pairing is

```text
 fixed p in P:       type lattice -- U_p/V_p -- adjoint type lattice
 varying v in Q_n:  deep lattice -- U_v/V_v -- inverse-diamond dual
```

The same letters record analogous correspondences, not interchangeable local deformation conditions.

### 9.4 The framed, gauge, and relation ledger

Assume for this calculation that $\ell$ is unramified in $F$, the finite-flat theorem of Section 4.2 applies at every $v\mid\ell$, every fixed condition away from $\ell$ is one of the smooth neutral conditions of Chapter 3, and every Taylor--Wiles factor is (9.4). Put

$$
d=[F:\mathbf Q]
\tag{9.10}
$$

and let $\mathscr T_n$ be the set of all finite framed places, including $P$ and $Q_n$. Write $t=|\mathscr T_n|$.

The sum of the relative dimensions of the framed local factors over $\Lambda_n$ is

$$
d_{\mathrm{loc}}
=\sum_{v\mid\ell}(f_v+3)+3\#\{v\in\mathscr T_n:v\nmid\ell\}
=d+3t.
\tag{9.11}
$$

The genuine $d$ coordinates are the finite-flat directions; all other displayed coordinates are local framing or ordered Frobenius coordinates already accounted for in the local rings.

Let $g_{\mathscr T_n}$ and $q_{\mathscr T_n}$ be the relative generator and obstruction ranks of the partially framed global problem. The strict/relaxed Poitou--Tate formula gives

$$
g_{\mathscr T_n}-q_{\mathscr T_n}
=t-1-h^0(F,W(1))
+\sum_{v\notin\mathscr T_n}
\bigl(\dim L_v-h^0(F_v,W)\bigr).
\tag{9.12}
$$

All finite conditioned places lie in $\mathscr T_n$, $h^0(F,W(1))=0$, and every real place contributes $-1$ because oddness gives $\dim H^0(F_v,W)=1$ and $L_v=0$. Therefore

$$
g_{\mathscr T_n}-q_{\mathscr T_n}=t-1-d.
\tag{9.13}
$$

Choose a uniformly padded effective relative presentation complex with source rank $G^\square$ and relation rank $b^\square$. Padding means adjoining a variable together with the actual equation setting it to zero; it changes neither the ring nor the determinant. Equation (9.13) becomes

$$
G^\square-b^\square=t-1-d,
\qquad
b^\square=G^\square-t+1+d.
\tag{9.14}
$$

The partially framed functor remembers a full $2\times2$ basis at each of the $t$ places. Its gauge torsor has

$$
c_{\mathscr T_n}=4t-h^0(F,\operatorname{ad}\bar\rho)=4t-1
\tag{9.15}
$$

coordinates. Fixed determinant does not change four basis entries into three; only the single global scalar stabilizer is removed.

Before frame removal, the source has $d+3t+G^\square$ variables over $\Lambda_n$. Removing the regular gauge torsor leaves

$$
d+3t+G^\square-(4t-1)
=G^\square-t+d+1
\tag{9.16}
$$

variables. By (9.14), this is exactly $b^\square$. The unframed augmented presentation is therefore square:

$$
R_n^P
\simeq
\Lambda_n[[Z_1,\ldots,Z_b]]/(F_1,\ldots,F_b),
\qquad
b=G^\square-t+d+1.
\tag{9.17}
$$

The cancellation explains why adding a fixed smooth neutral prime changes $t$, the local dimension, the gauge count, and the relative defect, yet preserves squareness. Deleting any one of those changes gives a wrong answer.

If a fixed local factor is singular, (9.11) cannot be used. Its complete local deformation complex, including every equation, belongs in the local base. The global relative complex must then be combined with it in the derived sense. A numerical equality of Krull dimensions does not supply the missing determinant line or prove that the resulting patched ring is Cohen--Macaulay.

## 10. The three nonminimal infrastructure theorems

The minimal theorem imported from Book 155 proves its conclusion, its faithful
rank-one module, and its post-equality numerical package for its clean datum.
It does not supply integral level raising, a type-selected Hecke-valued
representation at new primes, relative determinant factors there, or
component coverage at an enlarged level. We now state the three additional
inputs in a form that can be checked independently in any chosen automorphic
realization.

### 10.1 Infrastructure NM-I: integral level and type control

**Infrastructure Theorem NM-I.** Fix a controlled datum $\mathcal D^P$, a selected tuple of local components, and Taylor--Wiles sets $Q_n$ as in Section 9.1. Assume the following geometric assertions.

1. At the base level, at every mixed level obtained by changing a subset of $P\cup Q_n$, and at full deep level, the primary lattice and its adjoint companion are finite free over $\mathcal O$ and have the perfect Hecke-equivariant pairing used in (9.7b).
2. For each clean Steinberg prime, the two degeneracy maps have the Gram matrix (6.6), satisfy Ihara injectivity and saturation, and have torsion-free sign-selected new quotient.
3. For each finite tame type, an integral type lattice, its adjoint lattice, and saturated type-selection correspondences exist; their formation commutes with localization and coefficient reduction, and the selected type occurs with the stated multiplicity. An idempotent is required only when its denominator is a unit; an $\ell$-power congruence type is selected without averaging.
4. The multi-prime degeneracy/type cube has an exact saturated total complex. Equivalently, the derived tensor product of the one-prime comparison complexes has no unrecorded higher torsion.
5. At every $v\in Q_n$, the lower, full Iwahori, and deep modules are retained until the old/new comparison is complete. The full Iwahori old image is split and saturated, the localized new quotient is zero, the deep-level deck action is free, and the deep module is finite free over $\Lambda_n$. Only after these assertions are proved are the integral primary $U_v$-block and companion $V_v$-block formed; both are $\Lambda_n$-free, (9.7b) is perfect with diamond inversion, and adjunction identifies their faithful orders as in (9.7c).
6. Augmentation gives both exact module and faithful-order identities (9.8)--(9.9), including the companion block and its adjoint order, with no old quotient or nilpotent Hecke operator lost.
7. Every selected fixed component has a nonzero characteristic-zero automorphic point in the localized type module, and the localization excludes Eisenstein boundary classes and unwanted self-twist packets.
8. The ranks, numbers of generators, and relation-complex amplitudes are bounded independently of $n$, so finite-shadow patching applies.

Then the paired modules $M_n^{P,+},M_n^{P,-}$, their diamond actions, adjoint Hecke orders, and augmentation maps form the automorphic half of a Taylor--Wiles system for the fixed nonminimal datum. At every clean level-raising prime, the local congruence module has determinant (8.10); at a general controlled type it has determinant (8.12).

**Proof.** Clauses 1--4 construct the fixed-level lattices without replacing a saturated type lattice by its fraction-field span. Clause 5 supplies genuine $\Lambda_n$-freeness and the primary--companion inverse-diamond duality required by Book 73, axiom TW8, before finite shadows are chosen. Clause 6 identifies both augmentations with the original fixed-$P$ primary and adjoint problems rather than the minimal problem. Clause 7 makes the selected primary block nonzero. Clause 8 supplies the compactness needed to choose pairing-compatible diagonal shadows. These are exactly the module, duality, augmentation, boundedness, and nonvanishing assertions in the Taylor--Wiles axioms. The local determinant statement follows from the perfect comparison complexes of clauses 2--4. $\square$

The theorem is conditional on concrete Ihara, saturation, and type-lattice results. Characteristic-zero multiplicity one proves none of clauses 2--6 by itself.

### 10.2 Infrastructure NM-II: integral reciprocity and local compatibility

Write $\mathbb T_n^P=\mathbb T_n^{P,+}$ and $\mathbb T^P=\mathbb T^{P,+}$ for the primary orders; the companion orders remain present through (9.7c).

**Infrastructure Theorem NM-II.** In the setting of NM-I, assume:

1. the localized Hecke family carries a two-dimensional representation

   $$
   \rho_{\mathbb T_n}:G_F\longrightarrow
   \operatorname{GL}_2(\mathbb T_n^P)
   \tag{10.1}
   $$

   reducing to $\bar\rho$ and having determinant $\delta$;
2. for $v$ outside the level, its characteristic polynomial is the Hecke polynomial (1.7);
3. at every $v\mid\ell$, every Artinian quotient of (10.1) is finite flat of type $(0,1)$, not merely crystalline at characteristic-zero points;
4. at every $v\in(S_f\cup P)$ with $v\nmid\ell$, the restriction of
   (10.1), together with its line or finite-type data when applicable,
   factors through the exact named minimal or nonminimal local quotient; at
   $v\in P$ this is the selected quotient $R_v^{\square,P}$, character
   ordering is integral, and nonzero monodromy and conductor are checked on
   the relevant generic locus rather than imposed as Artinian nonvanishing
   conditions;
5. at every $v\in Q_n$, inertia acts through the tautological diamond character and its inverse on the ordered lines, and augmentation makes the restriction unramified; and
6. if the module was constructed on a quaternion algebra or transferred between inner forms, the faithful integral Hecke orders and their Galois families are identified, not only their characteristic-zero simple constituents; and
7. the faithful order $\mathbb T_n^P$ is generated as an $\mathcal O$-algebra by the verified Galois trace and determinant values, diamond characters, and those named local operators that are themselves functions of the retained line or type data.

Then universality gives compatible surjections

$$
R_n^P\twoheadrightarrow\mathbb T_n^P
\tag{10.2}
$$

whose reduction modulo $\mathfrak a_n$ is

$$
R^P\twoheadrightarrow\mathbb T^P.
\tag{10.3}
$$

**Proof.** Clause 1 supplies the matrix representation and absolute residual irreducibility makes strict equivalence unambiguous. Clauses 2--5 verify, place by place and on every Artinian quotient, the global deformation functor represented by $R_n^P$. Thus its universal property gives a map in (10.2). Clause 7, not faithfulness of the action by itself, proves that this map is surjective. Clause 6 transports the assertion integrally when an inner form intervenes. Augmentation and (9.7), (9.9) give (10.3). $\square$

The proof separates existence of a genuine representation from exact local compatibility. A characteristic-zero local Langlands parameter at every classical point does not automatically prove clauses 3--5 for the whole Hecke order.

### 10.3 Infrastructure NM-III: determinant lines and component support

**Infrastructure Theorem NM-III.** Assume NM-I and NM-II. This theorem has
two independent parts; an argument invokes only the part it uses.

For the **relative determinant part**, fix a chain from a base datum to
$\mathcal D^P$ and compatible augmentations as in Section 8.3. Treat the
base Fitting--congruence equality as an already proved input to that route:
in the clean rational cyclotomic range it is (8.12a), exported by Book 155
after its proof of minimal $R=T$. NM-III does not assume that base equality
again. Suppose the following genuinely nonminimal assertions hold:

1. the global deformation problem and every local condition are represented by complete effective perfect complexes whose tangent and obstruction groups are the stated Selmer groups;
2. the primary--companion degeneracy, type, and monodromy complexes are perfect and the pairing (9.7b), not a presumed self-adjoint $U$-projector, identifies their determinant lines with those of the corresponding local deformation complexes;
3. under this identification, the one-prime determinant is $c_p^\varepsilon$ for a clean Steinberg prime and $c_v(\tau_v,\mathfrak p_v)$ for a general controlled type;
4. the multi-prime determinant is the tensor product of the local determinant lines, with every higher $\operatorname{Tor}$ contribution either zero or explicitly included.

Then the relative deformation and automorphic determinant lines have the
same change from the base datum. At every augmentation satisfying the
finiteness hypotheses of the numerical criterion, the cotangent and
congruence factors change according to (8.13)--(8.16), and a proved base
equality gives (8.16a).

For the independent **component-support part**, suppose:

5. for each global component claimed in the theorem, the patched module is nonzero at its generic point; full coverage means that this holds at every minimal prime of the patched deformation ring; and
6. for a componentwise conclusion, the selected component ideals are compatible through the finite shadows, and augmentation of the patched component quotient is identified with the finite component-closure quotient (12.4).

These two clauses supply the nonminimal component-coverage and
specialization inputs for the abstract support theorem; they do not
themselves assert faithfulness.

**Proof.** For the determinant part, the complete effective complexes give a well-defined relative
determinant line before any presentation is chosen. Clause 2 identifies the
local Kodaira--Spencer maps with the adjoint automorphic correspondences.
Clause 3 computes their determinants, and clause 4 multiplies them without
discarding derived torsion. These are precisely the new ratios in
(8.13)--(8.16); combining them with the already proved base equality gives
(8.16a). For the support part, clause 5 is the independent arithmetic coverage statement required
by Book 75. Dimension equality, Cohen--Macaulayness, and near faithfulness
are deduced from it only after patching. Clause 6 prevents a patch-defined
union of components from being silently identified with a different finite
deformation quotient. $\square$

Component support is an independent clause. Equality of determinant lines controls multiplicity and congruence length at an augmentation; it does not force a module to meet a different component with the same generic inertial type.

The two halves of NM-III have disjoint uses. Clauses 1--4 are needed for the
relative numerical route of Sections 12.4 and 14.4, but not for a direct
support proof. Clauses 5--6 are needed for the support-based direct route,
but not for the numerical criterion at one augmentation. The sharp balanced
absolute patch of Section 11.3 needs neither half: it proves faithfulness
directly. Outside Book 155's clean base range, a relative argument must first
supply its own base Fitting--congruence theorem; that is a hypothesis on the
base theorem, not part of the new local content of NM-III.

### 10.4 Logical separation of the three inputs

The division of labor is exact.

| Input | Supplies | Does not supply |
|---|---|---|
| NM-I | integral lattices, level/type projectors, Ihara saturation, diamond freeness, primary--companion duality, augmentation | a Galois representation or local deformation factorization |
| NM-II | Hecke-valued Galois representations, determinant, exact local conditions, maps $R\twoheadrightarrow\mathbb T$ | numerical equality, faithfulness, or component coverage |
| NM-III | relative nonminimal determinant factors, nonminimal component coverage, and component-specialization compatibility | the already proved clean minimal comparison, existence of the modules or representations, reducedness, or faithfulness |

In the clean rational cyclotomic setting, Book 155's Infrastructures I--II,
sharp absolute patch, rank-one freeness, and post-equality numerical theorem
remain available at the minimal level. The new clauses involving $P$ must
still be proved. Over a totally real field, the Hilbert or quaternionic
analogues of NM-I and NM-II, the relevant nonminimal clauses of NM-III, and
any base theorem used by the relative route are hypotheses until the
relevant integral geometry has established them.

## 11. Direct nonminimal patching

We now carry the fixed datum $\mathcal D^P$ through the patching argument. The proof does not say that the minimal construction is unchanged. It replaces the minimal local base, absolute dual Selmer group, automorphic module, augmentation, determinant line, and support statement by the objects constructed in Chapters 8--10.

### 11.1 The finite-level system

For each $n$, let

$$
(R_n^P,\mathbb T_n^{P,+},M_n^{P,+};
\mathbb T_n^{P,-},M_n^{P,-};\Lambda_n)
\tag{11.1}
$$

be the paired system attached to $P\cup Q_n$. The primary objects carry the following maps and actions:

$$
\Lambda_n\longrightarrow R_n^P
\twoheadrightarrow\mathbb T_n^{P,+}
\longrightarrow\operatorname{End}_{\mathcal O}(M_n^{P,+}),
\tag{11.2}
$$

where the last action is faithful by the definition of the Hecke order. The companion action and order are transported by (9.7b)--(9.7c), not by an identification of the two modules. The augmentation ideal $\mathfrak a_n$ satisfies

$$
R_n^P/\mathfrak a_nR_n^P\simeq R^P,
\quad
\mathbb T_n^{P,\pm}/\mathfrak a_n\mathbb T_n^{P,\pm}
\simeq\mathbb T^{P,\pm},
\quad
M_n^{P,\pm}/\mathfrak a_nM_n^{P,\pm}
\simeq M^{P,\pm}.
\tag{11.3}
$$

The first identity is deformation-theoretic; both order and both module identities are integral automorphic assertions from NM-I. All are needed.

The sets $Q_n$ are not nested. Consequently there is generally no arithmetic map from the system at $n+1$ to the system at $n$. Patching uses finite shadows: for fixed integers $r$ and $m$, reduce the rings, both modules, their adjoint orders, and the pairing modulo $\varpi^m$ and the $r$th powers of their maximal ideals, note that only finitely many isomorphism classes occur, and choose a diagonal subsequence with compatible representatives. The resulting pseudo-transitions are maps between the chosen pairing-compatible finite shadows, not maps between the original spaces of automorphic forms.

### 11.2 Verification of the Taylor--Wiles axioms

The seven finite-level system checks and the additional route-specific
support check can be displayed without abbreviation.

1. **Residual identification.** Every Hecke-valued representation reduces to the same absolutely irreducible $\bar\rho$, and every determinant is $\delta$.
2. **Auxiliary groups.** The groups $\Delta_n$ have $q_P$ named cyclic factors of growing $\ell$-power order, and their group algebras receive compatible maps from one fixed power-series algebra after finite-shadow choices.
3. **Module freeness.** NM-I gives that both $M_n^{P,+}$ and $M_n^{P,-}$ are finite free over $\Lambda_n$, with one rank bounded independently of $n$. A rank equality after tensoring with $E$ is not used as a replacement.
4. **Companion duality.** The perfect pairing (9.7b) identifies the companion with the $\Lambda_n$-dual of the primary using diamond inversion and pairs every $U_v$ correspondence with $V_v$. The type projectors at $P$ are self-adjoint or occur with their explicitly identified adjoints. No self-pairing of the primary block is asserted.
5. **Augmentation.** Every exact identity in (11.3) holds and the pairing augments to the base primary--companion pairing. In particular, augmentation retains all fixed conditions at $P$.
6. **Deformation control.** The ordered primes $Q_n$ kill the dual Selmer group (9.1). NM-II gives the surjection in (11.2) and verifies its local condition at every finite place.
7. **Uniform presentations.** The complete effective complexes and the ledger (9.11)--(9.17) give uniformly bounded square presentations. Coordinates are padded only by variable--linear-relation pairs.
8. **Automorphic support.** For the support-based direct route, NM-III
   clauses 5--6 place the patched primary module on every selected component
   claimed in the conclusion; this is checked at the generic points and is
   not inferred from equality of types. This item is not an axiom of the
   sharp balanced faithful-action route, which proves full support as a
   consequence of faithfulness.

Items 1--7 verify the Taylor--Wiles system, with companion duality supplying
the role of the eighth axiom in Book 73; item 8 is the extra arithmetic
support input for the support-based comparison theorem. These checks also
explain the division between fixed and varying primes. Items 3--5 concern
the diamond tower at $Q_n$, while items 4 and 8 retain the integral component
data at $P$ throughout that tower.

### 11.3 The patched pair and its dimension

Let

$$
S_\infty=\mathcal O[[z_1,\ldots,z_{q_P}]],
\qquad
\mathfrak a_\infty=(z_1,\ldots,z_{q_P}).
\tag{11.4}
$$

After passing to the diagonal subsequence, patching produces a complete local $S_\infty$-algebra $R_\infty^P$, finite primary and companion modules $M_\infty^{P,+},M_\infty^{P,-}$, their perfect inverse-diamond pairing, and adjoint faithful orders $\mathbb T_\infty^{P,+}\simeq\mathbb T_\infty^{P,-}$. The primary order is a quotient of $R_\infty^P$ acting faithfully on $M_\infty^{P,+}$. Their augmentations are

$$
R_\infty^P/\mathfrak a_\infty R_\infty^P\simeq R^P,
\tag{11.5}
$$

$$
M_\infty^{P,\pm}/\mathfrak a_\infty M_\infty^{P,\pm}
\simeq M^{P,\pm},
\qquad
\mathbb T_\infty^{P,\pm}/\mathfrak a_\infty
\mathbb T_\infty^{P,\pm}
\simeq\mathbb T^{P,\pm}.
\tag{11.6}
$$

Both modules are finite free over $S_\infty$. From now on $M_\infty^P=M_\infty^{P,+}$ and $\mathbb T_\infty^P=\mathbb T_\infty^{P,+}$ denote the primary objects in support and ring comparisons; the companion remains present in every adjoint and determinant statement. In the smooth neutral range of Section 9.4, the ring has a square presentation

$$
R_\infty^P
\simeq
S_\infty[[Z_1,\ldots,Z_b]]/(F_1,\ldots,F_b).
\tag{11.7}
$$

Therefore

$$
\dim R_\infty^P\ge\dim S_\infty=q_P+1.
\tag{11.8}
$$

Since a nonzero $S_\infty$-free module has support of dimension $q_P+1$, (11.8) is only the lower half of the dimension argument. If NM-III gives coverage of every minimal prime, Book 75's sharp patched comparison supplies the reverse inequality on every component. It then proves that $R_\infty^P$ is equidimensional of dimension $q_P+1$, that the $F_i$ form a regular sequence, that $M_\infty^P$ is maximal Cohen--Macaulay, and that $R_\infty^P$ is finite free over $S_\infty$. If only selected components are covered, those conclusions require an independent dimension ceiling on the corresponding component quotient. They do not follow merely by ignoring the uncovered components.

In the smooth neutral range there is a stronger direct argument, and this is
the exact point at which the final method of Book 155 can be reused. The
Wiles defect of the fixed-$P$ datum is zero. Indeed, the Schur hypotheses
make $h^0(F_v,W)=0$ at $v\mid\ell$, so the places above $\ell$ contribute

$$
\sum_{v\mid\ell}f_v=[F:\mathbf Q]=d,
$$

the $d$ real places contribute $-d$, every clean condition away from $\ell$
satisfies $\dim L_v^P=h^0(F_v,W)$, and the two global invariant groups vanish
by (1.6). Hence

$$
h^1_{\mathcal L_P}(F,W)=
h^1_{\mathcal L_P^\perp}(F,W(1))=q_P.
\tag{11.8a}
$$

The Poitou--Tate sequence for the ordered conditions at $Q_n$ has a
$q_P$-dimensional local quotient mapping isomorphically to the dual of the
group in (9.1), by the prime-selection condition. Consequently

$$
h^1_{\mathcal L_{P,Q_n}}(F,W)=q_P.
\tag{11.8b}
$$

Absolute residual irreducibility identifies the tangent space of the
unframed auxiliary functor with the group in (11.8b). Choosing a basis and
lifts, topological Nakayama therefore gives the sharp absolute source

$$
\mathscr P=\mathcal O[[X_1,\ldots,X_{q_P}]]
\twoheadrightarrow R_n^P.
\tag{11.8c}
$$

Retain the kernels of these source maps, lifts of the diamond parameters,
the actions, and all three exact augmentations (11.3) in the finite shadows.
The same marked inverse-limit argument as in Book 155 gives

$$
S_\infty\longrightarrow\mathscr P
\longrightarrow R_\infty^P
\longrightarrow A_\infty^P
\subseteq\operatorname{End}_{S_\infty}(M_\infty^P),
\tag{11.8d}
$$

where $A_\infty^P$ is the action image and the composite from $S_\infty$ is
faithful scalar multiplication. The two power-series rings $S_\infty$ and
$\mathscr P$ have the same dimension $q_P+1$. Book 155's equal-variable
rigidity lemma therefore makes the action of $\mathscr P$ injective, makes
$\mathscr P$ finite free over $S_\infty$, and makes $M_\infty^P$ finite free
over $\mathscr P$. Since the action factors through the quotient
$\mathscr P\twoheadrightarrow R_\infty^P$, one obtains

$$
R_\infty^P=\mathscr P=A_\infty^P,
\qquad
M_\infty^P\simeq\mathscr P^{\,e}
\quad(e>0).
\tag{11.8e}
$$

Exact augmentation then gives

$$
R^P\simeq\mathbb T^P,
\qquad
M^P\simeq(R^P)^e.
\tag{11.8f}
$$

Indeed, the $R^P$-action on the free module in (11.8f) factors through the
faithful Hecke order, so the kernel of $R^P\twoheadrightarrow\mathbb T^P$ is
zero. This route uses NM-I and NM-II and the sharp balance (11.8a)--(11.8c).
It uses neither a minimal theorem, NM-III's determinant clauses, NM-III's
coverage clauses, nor an independent reducedness hypothesis.

When (11.8a)--(11.8c) are unavailable, the preceding square-presentation and
support argument remains a distinct direct route. It is then the coverage
statement, not the minimal equality, that supplies the missing dimension
ceiling.

For a singular local component, the patched source is built over the completed tensor product of its actual local rings. The same conclusion follows only after constructing a presentation $R_\infty^P=P_\infty/J_\infty$ in which $P_\infty$ is Cohen--Macaulay, catenary, and equidimensional of the required dimension, the dimension formula holds at primes minimal over $J_\infty$, and $J_\infty$ has the asserted generator bound. The local rings' perfect obstruction complexes must produce that presentation. One may not replace them by smooth rings having the same generic dimension.

### 11.4 Coverage, faithfulness, and nilpotents

Let $A$ be a Noetherian ring and $M$ a finite $A$-module. Full support means

$$
\operatorname{Supp}_A(M)=\operatorname{Spec}A.
\tag{11.9}
$$

It implies only

$$
\sqrt{\operatorname{Ann}_A(M)}=\sqrt{(0)}.
\tag{11.10}
$$

Thus the action has nilpotent kernel. If $A$ is reduced, the action is faithful. More generally, if $A$ is equidimensional Cohen--Macaulay and the action is faithful at every minimal prime, then $A$ has no embedded associated primes on which a nonzero annihilator can hide, and the action is faithful.

These observations give three distinct outputs:

- coverage of every component gives near faithfulness and hence equality of reduced quotients after the exact augmentation argument of Book 75;
- coverage of a selected union, together with a compatible patched component quotient and an independent dimension ceiling, gives a reduced componentwise equality; and
- source reducedness, generic reducedness plus $S_\infty$-torsion-freeness, or a direct annihilator theorem upgrades the corresponding reduced equality to full equality.

The sharp balanced route adds a fourth output: (11.8e) proves faithful action
before any component argument, so full support and absence of a kernel are
consequences rather than hypotheses.

Patching does not manufacture coverage. If the type module misses a local component, the corresponding global component is absent from (11.9), even when it has the same characteristic-zero inertial type as a component that is present.

## 12. The nonminimal $R=T$ theorem

We can now separate two mechanisms for full equality from the reduced,
componentwise, and numerical variants. In every statement, the map is the
canonical surjection (10.3). Its direction comes from the Hecke-valued
Galois representation satisfying the deformation problem.

### 12.1 Full equality

**Theorem 12.1A (sharp balanced full nonminimal $R=T$).** Let $F$,
$\ell$, $\bar\rho$, $\delta$, and $\mathcal D^P$ satisfy the standing
hypotheses and the smooth neutral hypotheses of Section 9.4. Assume that the
calculation (11.8a)--(11.8b) applies, the residual image supplies the ordered
sets $Q_n$, and NM-I and NM-II hold with the pairing-compatible finite
shadows and exact ring, module, order, and action augmentations of Sections
11.1 and 11.3. Then

$$
R^P\xrightarrow{\sim}\mathbb T^P.
\tag{12.1}
$$

The common ring is finite flat and a complete intersection over $\mathcal O$,
and $M^P$ is finite free of positive rank over it. If the selected type
module is independently cyclic, this rank is one.

**Proof.** Equations (11.8a)--(11.8c) give an absolute source with exactly
$q_P$ variables, matching the $q_P$ diamond variables. Equal-variable
rigidity gives (11.8e), and exact augmentation and faithful definition of the
Hecke order give (11.8f), which is (12.1). Since $\mathscr P$ is finite free
over $S_\infty$, the diamond parameters form a regular sequence in
$\mathscr P$; its augmentation is therefore finite flat and
complete-intersection. The module statement follows by augmenting the free
module in (11.8e). $\square$

This is the closest nonminimal analogue of Book 155's kernel-killing proof.
It does not descend to minimal level, and it does not use a determinant or
component-coverage theorem.

For local conditions outside this sharp balanced range, one can instead use
the following support-based result.

**Theorem 12.1B (support-based full nonminimal $R=T$).** Let $F$, $\ell$, $\bar\rho$, $\delta$, and $\mathcal D^P$ satisfy the standing hypotheses. Assume:

1. the finite-flat local theorem of Section 4.2 applies at all $v\mid\ell$;
2. every $v\in P$ has a smooth neutral controlled local condition, or the actual singular local base yields a presentation

   $$
   R_\infty^P=P_\infty/J_\infty
   $$

   in which $P_\infty$ is Cohen--Macaulay, catenary, and equidimensional of dimension $q_P+1+b$, the dimension formula holds at primes minimal over $J_\infty$, and $J_\infty$ is generated by at most $b$ elements;
3. the residual image admits Taylor--Wiles sets for the recomputed dual Selmer group;
4. NM-I and NM-II hold at every finite level;
5. NM-III clause 5 holds with coverage of every minimal prime of
   $R_\infty^P$, and the exact ring, module, and faithful-action augmentation
   identities (11.5)--(11.6) hold; and
6. at least one of the following independent kernel-killing hypotheses holds:

   $$
   R_\infty^P\text{ is reduced},
   \qquad
   R_\infty^P\otimes_{S_\infty}\operatorname{Frac}(S_\infty)
   \text{ is reduced},
   \qquad
   R^P\text{ is reduced}.
   \tag{12.1a}
   $$

Then (12.1) holds.

The ring is finite flat over $\mathcal O$. In the smooth neutral case it is a complete intersection and the corresponding automorphic module is maximal Cohen--Macaulay. That module is free of rank one over the Hecke order only if it is independently known to be cyclic and faithful, or if another criterion such as finite projective dimension proves freeness; generic multiplicity one alone does not suffice.

**Proof.** Sections 11.1--11.3 and clause 5 verify the sharp patched comparison theorem of Book 75. It gives a nilpotent kernel for

$$
R_\infty^P\twoheadrightarrow\mathbb T_\infty^P
\tag{12.2}
$$

and proves that $R_\infty^P$ is finite free over $S_\infty$. Under the first alternative in (12.1a), the nilpotent kernel is zero. Under the second, $S_\infty$-freeness injects the source into its reduced generic fiber, so the source is reduced and the same conclusion follows. Under the third, exact augmentation gives a nilpotent kernel in the reduced finite source $R^P$, hence zero. Book 75's regular augmentation theorem now gives (12.1), finite flatness, and the complete-intersection and maximal Cohen--Macaulay conclusions. Freeness of the module requires the additional criterion stated after the theorem. $\square$

### 12.2 Reduced equality

**Theorem 12.2 (reduced nonminimal $R=T$).** Retain clauses 1--5 of
Theorem 12.1B, but omit every alternative in (12.1a). Then

$$
(R^P)_{\mathrm{red}}\xrightarrow{\sim}(\mathbb T^P)_{\mathrm{red}}.
\tag{12.3}
$$

If the generic Hecke algebra is a product of fields and $\mathbb T^P$ is $\mathcal O$-torsion-free, then $\mathbb T^P$ is already reduced, so the right side may be written $\mathbb T^P$.

**Proof.** Apply Book 75's sharp patched comparison theorem, not the generally false rule that reduction commutes with an arbitrary quotient by the augmentation ideal. Component coverage makes the patched action nearly faithful; the square presentation then gives Cohen--Macaulayness and finite $S_\infty$-freeness, so the augmentation sequence is regular and exact control carries the nilpotent kernel to finite level. This proves (12.3). A torsion-free order inside a product of characteristic-zero fields has no nonzero nilpotent, proving the last assertion. $\square$

This reduced theorem suffices for characteristic-zero modularity of every point: a homomorphism from $R^P$ to a domain kills nilpotents. It does not identify infinitesimal deformation structure.

### 12.3 Componentwise equality

Let $\mathcal C$ be a union of irreducible components of $\operatorname{Spec}R^P[1/\ell]$, and let

$$
R^{P,\mathcal C}
=R^P/\ker\bigl(R^P\to
\prod_{\mathfrak p\in\mathcal C}R^P[1/\ell]/\mathfrak p\bigr)
\tag{12.4}
$$

be the schematic closure quotient of the selected generic components. Assume a saturated Hecke-stable quotient $M^{P,\mathcal C}$ has been constructed whose generic constituents are exactly the automorphic points on $\mathcal C$, and let $\mathbb T^{P,\mathcal C}$ be its faithful Hecke order. The existence and saturation of this quotient are integral automorphic assertions, not consequences of the notation.

**Theorem 12.3 (componentwise nonminimal $R=T$).** Suppose the presentation
and module hypotheses of Theorem 12.2 hold on a patched union $\Sigma$ of
minimal primes. Let $P_\Sigma$ be the kernel of the map from the patched
deformation ring to the product of its quotients by the primes in $\Sigma$.
Assume the patched module has exactly that generic support, an independent
ceiling proves that the selected quotient is equidimensional of dimension
$q_P+1$, and NM-III clause 6 identifies its augmentation with
$R^{P,\mathcal C}$ and $M^{P,\mathcal C}$. Then

$$
(R^{P,\mathcal C})_{\mathrm{red}}
\xrightarrow{\sim}
(\mathbb T^{P,\mathcal C})_{\mathrm{red}}
\tag{12.5}
$$

Since the quotient (12.4) embeds in a product of domains, it is already reduced. Thus one always obtains

$$
R^{P,\mathcal C}
\xrightarrow{\sim}
(\mathbb T^{P,\mathcal C})_{\mathrm{red}}.
\tag{12.5a}
$$

If $\mathbb T^{P,\mathcal C}$ is an $\mathcal O$-torsion-free order in a product of fields, it too is reduced, and (12.5a) is the full equality

$$
R^{P,\mathcal C}
\xrightarrow{\sim}
\mathbb T^{P,\mathcal C}.
\tag{12.5b}
$$

**Proof.** Book 75's componentwise theorem applied to the patch-defined ideal $P_\Sigma$ gives (12.5) after augmentation. NM-III clause 6 is what identifies that augmentation with the independently defined finite quotient (12.4); without it one would have proved a theorem for an unnamed patch-defined quotient. The closure quotient is reduced, giving (12.5a), and the stated generic semisimplicity makes its faithful Hecke order reduced, giving (12.5b). $\square$

### 12.4 The numerical variant

Sometimes the minimal post-equality Fitting--congruence package and the local
cost formulas permit a shorter argument at one augmentation. Make the
coefficient extension and localized completed base changes of Section 8.3
first, and continue to denote the resulting rings by $R^P$ and
$\mathbb T^P$. Let

$$
R^P\twoheadrightarrow\mathbb T^P
\xrightarrow{\lambda_P}\mathcal O'
\tag{12.6}
$$

be the canonical maps. Assume $\mathbb T^P$ is finite flat over $\mathcal O'$, the cotangent module $\Phi_{R^P,\lambda_P}$ is finite, and put

$$
\Psi_{\mathbb T^P,\lambda_P}
=\mathcal O'/\eta_{\mathbb T^P,\lambda_P}.
\tag{12.7}
$$

The Wiles--Lenstra inequality is

$$
\operatorname{length}_{\mathcal O'}\Phi_{R^P,\lambda_P}
\le
\operatorname{length}_{\mathcal O'}\Psi_{\mathbb T^P,\lambda_P},
\tag{12.8}
$$

equivalently

$$
\eta_{\mathbb T^P,\lambda_P}
\subseteq
\operatorname{Fitt}_{\mathcal O'}
\Phi_{R^P,\lambda_P}.
\tag{12.9}
$$

Under (12.8), the numerical criterion gives

$$
R^P\simeq\mathbb T^P
\tag{12.10}
$$

at the localized augmentation, and both are complete intersections there.

For a clean relative argument based on the rational cyclotomic datum, Book
155 supplies (8.12a) as a proved post-equality statement. NM-III clauses 1--4
supply the identical new increment

$$
\sum_{v\in P}\operatorname{ord}_{\varpi'}c_v
\tag{12.11}
$$

on both sides. Hence (12.8) follows. NM-III's coverage clauses are not used
in this numerical proof. If one local factor is missing, if an opposite
Steinberg factor is nonunit, or if higher $\operatorname{Tor}$ contributes,
this cancellation fails and the numerical proof stops.

## 13. Extracting modularity of a specified lift

An equality of rings becomes a modularity statement only after the target representation is turned into a point of the correct ring and then compared with the Galois representation over the Hecke order. Exact local type is recovered from the representation itself, not just from equality of unramified traces.

### 13.1 From a Galois point to a Hecke character

Let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{13.1}
$$

be a lift of $\bar\rho$ satisfying $\mathcal D^P$ and lying on the selected component tuple. Universality gives

$$
x_\rho:R^P\longrightarrow\mathcal O'.
\tag{13.2}
$$

For the full and reduced whole-ring theorems, put
$R^\star=R^P$ and $\mathbb T^\star=\mathbb T^P$. For the componentwise
theorem, put

$$
R^\star=R^{P,\mathcal C},
\qquad
\mathbb T^\star=\mathbb T^{P,\mathcal C};
\tag{13.2a}
$$

in this case the component hypothesis makes (13.2) factor through $R^\star$.
If Theorem 12.1A, Theorem 12.1B, or (12.5b) gives a full equality, transport the resulting
point directly to a Hecke character. If only (12.3) or (12.5a) gives a
reduced equality, the point still factors through $(R^\star)_{\mathrm{red}}$
because $\mathcal O'$ is a domain; compose the inverse reduced equality with
the quotient $\mathbb T^\star\to(\mathbb T^\star)_{\mathrm{red}}$. In every
case one obtains

$$
\lambda_\rho:\mathbb T^\star\longrightarrow\mathcal O'.
\tag{13.3}
$$

After enlarging $E'$ if necessary, a characteristic-zero simple constituent of the automorphic module affords $\lambda_\rho$. It corresponds to a cuspidal automorphic representation $\pi$ of parallel weight two.

### 13.2 Identification and exact local type

Let $\rho_\pi$ be the Galois representation obtained by specializing the Hecke-valued family at (13.3). For every finite place outside the deformation set,

$$
\operatorname{tr}\rho(\operatorname{Frob}_v)
=\lambda_\rho(S_v^{-1}T_v)
=\operatorname{tr}\rho_\pi(\operatorname{Frob}_v),
\tag{13.4}
$$

and the determinants agree. Frobenius elements at these places are dense. Hence the two pseudorepresentations agree. Their common residual representation is absolutely irreducible, so both representations are irreducible and Chebotarev plus Brauer--Nesbitt gives

$$
\rho\otimes_{\mathcal O'}E'
\simeq
\rho_\pi\otimes_{\mathcal O'}E'.
\tag{13.5}
$$

The stable-lattice uniqueness lemma upgrades (13.5) to an integral isomorphism after scaling the intertwiner. Indeed, place one stable lattice inside the other but not inside its $\varpi'$-multiple. Its image modulo $\varpi'$ is a nonzero stable subspace of the absolutely irreducible residual representation, hence is the whole residual space; Nakayama's lemma makes the two lattices equal. Thus, after the harmless coefficient extension already allowed in Section 13.1,

$$
\rho\simeq\rho_\pi
\qquad\text{as }\mathcal O'[G_F]\text{-modules}.
\tag{13.5a}
$$

Now restrict (13.5a) to every decomposition group. At $v\mid\ell$, it
transfers the integral finite-flat property of the chosen Galois lattice. At
$v\in P$, it transfers the actual inertia action, the monodromy operator, and
any stable line uniquely determined by the representation. A nonintrinsic
ordered line or flag is instead matched because (13.2)--(13.3) are the same
point of the retained deformation and Hecke refinement data, as required by
NM-II; it does not follow from an abstract isomorphism of representations.
Thus, at every $v\nmid\ell$ covered by the assumed local compatibility theorem,
$\pi_v$ has the exact prescribed special or principal-series type and
conductor. This last conclusion uses NM-II's local compatibility. No
identification of the automorphic representation $\pi_v$ at $v\mid\ell$ is
deduced from finite flatness alone; such a conclusion requires a separate
$\ell$-adic local--global compatibility theorem. Equality of traces at the
unramified places alone would identify the global semisimplification but
would not, without (13.5a) and local compatibility, label an integral
component.

### 13.3 The controlled nonminimal lifting theorem

**Theorem 13.1 (controlled nonminimal modularity lifting).** Let $F$ be totally real and let $\ell>2$ be unramified in $F$. Let

$$
\bar\rho:G_F\to\operatorname{GL}_2(k)
\tag{13.6}
$$

be continuous, absolutely irreducible, totally odd, and adequate for Taylor--Wiles prime selection. Assume $H^0(F,W(1))=0$. Suppose $\bar\rho$ occurs in a non-Eisenstein weight-two automorphic maximal ideal and the required fixed-level type module is independently known to be nonzero. This nonvanishing may come directly from the given automorphic packet or from the level-raising, saturated type-selection, and level-lowering theorems of Chapters 6, 7, and 10; it is not a consequence of the desired nonminimal $R=T$ theorem.

Let $\rho:G_F\to\operatorname{GL}_2(\mathcal O')$ be a lift such that:

1. $\det\rho=\psi\chi_\ell$, with $\psi$ finite order and compatible with every chosen integral local condition;
2. $\rho$ is unramified outside a finite set;
3. at every $v\mid\ell$, $F_v/\mathbf Q_\ell$ is unramified,
   $\rho_v$ is finite flat of type $(0,1)$, the determinant twist is supplied
   by a character $\eta_v$ satisfying Section 4.1, and the residual Schur
   hypotheses of Section 4.2 hold;
4. away from $\ell$, every nonminimal place belongs to a controlled datum in the sense of Section 5.4, and $\rho_v$ lies on its named component;
5. the residual restrictions and residue cardinalities satisfy the nonvexing hypotheses used by the relevant Ihara and type theorems;
6. the fixed determinant global deformation problem is represented and has no unrecorded local equation; and
7. NM-I and NM-II hold for the selected component tuple, and one of the
   following route-specific packages is verified: the sharp balance of
   Theorem 12.1A; NM-III clauses 5--6 together with the applicable coverage,
   component-specialization, dimension-ceiling, and nilpotent-control
   hypotheses of Theorems 12.1B--12.3; or the proved base equality,
   NM-III clauses 1--4, and the finiteness hypotheses of Section 12.4.

Then there is a cuspidal automorphic representation $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ of parallel weight two such that

$$
\rho\simeq\rho_\pi.
\tag{13.7}
$$

At every $v\nmid\ell$ covered by the stated local compatibility hypotheses,
$\pi_v$ has the conductor, inertial type, ordered branch, and monodromy
prescribed by $\rho_v$ under the fixed reciprocity normalization. At
$v\mid\ell$, the asserted conclusion is that the Galois lattice in (13.7) is
finite flat of type $(0,1)$; a stronger assertion about $\pi_v$ is included
only when a separate $\ell$-adic local--global compatibility theorem is
assumed. When an ordering is not intrinsic to the isomorphism class of
$\pi_v$, “ordered branch” refers to the retained local eigenline or
refinement in the automorphic module, whose compatibility is part of NM-I
and NM-II.

**Proof.** The local properties of $\rho$ define the point (13.2). Adequacy supplies the sets $Q_n$ for the nonminimal dual Selmer group. The hypotheses of Chapters 9--11 verify the Taylor--Wiles system with $P$ fixed. The applicable theorem of Chapter 12 identifies the relevant deformation component, at least after reduction, with its faithful Hecke order. Sections 13.1 and 13.2 then produce $\pi$, prove (13.7), and recover every local property asserted above. $\square$

For $F=\mathbf Q$ with the exact clean nontrivial squarefree nonvexing
cyclotomic-determinant datum of Book 155, that book supplies the minimal equality, the
faithful free rank-one module and perfect pairing, and the post-equality base
Fitting--congruence equality. It also supplies the minimal-level instances of
the integral control and reciprocity used by NM-I and NM-II. Theorem 13.1
still requires every new integral level/type and local-compatibility clause
at the added primes. The sharp direct route requires no NM-III clause; the
support route requires its nonminimal coverage clauses; and the relative
route requires its nonminimal determinant-factor clauses. A nontrivial
$\psi$ is not in Book 155's theorem merely because local square roots exist at
$\ell$; using that base theorem then requires a separately proved global
twisting equivalence compatible with every deformation condition and
automorphic central character.

## 14. The minimal-level route down and back up

Direct patching is conceptually uniform, but a relative argument can be shorter when the minimal ring equality and its post-equality Fitting--congruence equality are already known and every added prime has a primitive local comparison factor. The route has three separate movements: lower the residual automorphic source, raise an automorphic point on each desired branch, and prove that the entire target deformation component is controlled by the raised Hecke order.

### 14.1 Lowering the residual source

Begin with an automorphic representation $\pi_0$ whose residual representation is $\bar\rho$. Its level may contain primes at which $\bar\rho$ is unramified. Let $P_{\mathrm{low}}$ be the set of such primes that must be removed to reach the minimal deformation datum.

For every $p\in P_{\mathrm{low}}$, verify all hypotheses of Theorem 7.1 on the module that occurs after the preceding lowering steps. This includes:

- actual unramifiedness of $\bar\rho|_{G_{F_p}}$, not only unramified semisimplification;
- nonscalar residual Frobenius and the required exclusions on $q_p$;
- non-Eisenstein localization and residual multiplicity one;
- integral Ihara injectivity, saturation, and component-group control; and
- preservation of these properties at each intermediate level.

Iteration then produces a lower-level residual eigensystem. It yields some characteristic-zero automorphic lift $\pi_{\min}$ of that system. It does not assert that $\pi_{\min}$ is the original $\pi_0$ with local factors deleted.

One may now invoke the minimal theorem only if the resulting datum is exactly
within its range. In the clean rational case this means, among other things,
the coefficient-prime, nontrivial squarefree-level, nonzero residual
monodromy, nonvexing, exact-level source, cyclotomic-determinant, and two
integral infrastructure hypotheses of Book 155. Its conclusion supplies not
only $R^{\min}=\mathbb T^{\min}$ but also the faithful free rank-one minimal
module and the post-equality Fitting--congruence equality. If lowering
creates zero residual monodromy at a prime retained in the minimal set, if
the coefficient-prime restriction has nonscalar endomorphisms, or if the
determinant is not cyclotomic and no global twisting theorem has been proved,
the imported theorem does not apply.

### 14.2 Raising a congruent automorphic point

Order the target nonminimal primes as

$$
P=\{v_1,\ldots,v_r\}.
\tag{14.1}
$$

Starting from $\pi_{\min}$, construct $\pi_i$ at the level prescribed by $\{v_1,\ldots,v_i\}$. At a clean Steinberg prime, Theorem 6.1 applies with the sign determined by the target component. The residual congruence follows from the target lift itself: if $\rho_{v_i}$ is Steinberg of sign $\varepsilon_i$ and $\bar\rho_{v_i}$ is unramified, reduction gives

$$
\bar T_{v_i}=\varepsilon_i(q_{v_i}+1).
\tag{14.2}
$$

in the trivial-central-character normalization. With general $\psi$, the
same assertion is the signed special-root condition for (1.7), with
$S_{v_i}^{-1}$ specialized to $\psi(\operatorname{Frob}_{v_i})$; one must not
reuse (14.2) without that translation.

At an ordered tame principal-series prime, (14.2) has no analogue sufficient by itself. One needs an integral type-raising theorem: the tame characters must extend to integral type lattices, the type projector must be defined over $\mathcal O$, its reduction must meet the current residual block, and the selected ordered component must be nonzero. A characteristic-zero packet containing the type does not establish any of these assertions.

After all steps, one has an automorphic point

$$
y_P:R^{P,\mathcal C}\longrightarrow\mathcal O_y
\tag{14.3}
$$

on the desired component tuple $\mathcal C$. This point is congruent to $\pi_{\min}$ modulo a maximal ideal. It need not equal the target point $x_\rho$, and equality of their generic inertial types does not show that they lie on $\mathcal C$. The component assertion in (14.3) must come from local compatibility in the raising theorem.

### 14.3 Connecting the raised point to the target

There are exactly two noncircular ways to connect (14.3) to $x_\rho$.

The first is the componentwise direct theorem: prove Theorem 12.3 on $\mathcal C$. Then every characteristic-zero point of $R^{P,\mathcal C}$, including $x_\rho$, is automorphic.

The second is a relative numerical comparison. For each added prime, compare the cotangent module at the global deformation augmentation and the congruence module at the raised automorphic augmentation. The comparison must show that both acquire the same factor $c_{v_i}$. Starting from the proved minimal Fitting--congruence equality, the numerical criterion then proves the equality at the enlarged level. Minimal ring equality alone is not the numerical input, although Book 155 proves both statements in the required order.

Neither route uses the assertion “there is a congruent form on this level” as a substitute for $R=T$. The congruent form only proves nonvanishing of the Hecke localization and supplies an augmentation at which the determinant comparison can be evaluated.

It is important that special and unramified local functors are not treated as nested. The relative comparison is mediated by their incidence ring (2.7) and by the degeneracy complex. There need be no ring map between $R^{\min}$ and $R^P$. What exists at the new level is the independent canonical surjection

$$
R^P\twoheadrightarrow\mathbb T^P,
\tag{14.4}
$$

and what is transported from the minimal level is the post-equality
determinant-line comparison, not a fictitious quotient map.

### 14.4 The inductive relative criterion

The preceding argument is conveniently packaged as follows.

**Theorem 14.1 (inductive nonminimal criterion).** Let $\mathcal D_0,\ldots,\mathcal D_r$ be global data, where $\mathcal D_0$ is minimal and $\mathcal D_i$ adds the controlled condition at $v_i$. No inclusion of the local functors is assumed. After extending all augmentations to one common coefficient DVR, suppose clauses 1--3 hold for every $0\le i\le r$, clauses 4--6 hold for every $1\le i\le r$, and clause 7 holds at the base:

1. there is a finite flat faithful Hecke order $\mathbb T_i$ and a canonical surjection $R_i\twoheadrightarrow\mathbb T_i$;
2. the independent minimal source for $i=0$, and an integral
   level/type-raising theorem for $i>0$, produces an augmentation $\lambda_i$
   on the target component;
3. the cotangent module $\Phi_{R_i,\lambda_i}$ is finite;
4. a perfect incidence comparison between $\mathcal D_{i-1}$ and $\mathcal D_i$ has a nonzero determinant $c_{v_i}$;
5. the deformation and automorphic determinant theorems give

   $$
   \operatorname{Fitt}\Phi_{R_i,\lambda_i}
   =
   \operatorname{Fitt}\Phi_{R_{i-1},\lambda_{i-1}}(c_{v_i}),
   \tag{14.5}
   $$

   $$
   \eta_{\mathbb T_i,\lambda_i}
   =
   \eta_{\mathbb T_{i-1},\lambda_{i-1}}(c_{v_i});
   \tag{14.6}
   $$

6. all multi-prime higher torsion has been shown to vanish or has been included in both formulas; and
7. the base datum has already been proved to satisfy
   $R_0\simeq\mathbb T_0$ and, at $\lambda_0$,

   $$
   \operatorname{Fitt}\Phi_{R_0,\lambda_0}
   =\eta_{\mathbb T_0,\lambda_0}.
   \tag{14.7}
   $$

   In the exact clean rational cyclotomic range, Book 155 proves the ring
   equality by sharp absolute patching and then proves (14.7) in its Section
   12.6. After a permitted coefficient extension, use the
   resulting base-changed complete-intersection equality at the extended
   augmentation. Outside that range, (14.7) requires a separately named base
   theorem.

Then $R_i\simeq\mathbb T_i$ at $\lambda_i$ for every $i$. In particular, every characteristic-zero point on the controlled component reached at the last step is automorphic.

**Proof.** The base numerical equality (14.7), not ring equality by itself,
makes the minimal cotangent Fitting ideal equal to the minimal congruence
ideal. Equations (14.5)--(14.6) preserve this equality from $i-1$ to $i$.
Thus the inclusion (12.9) holds at every step. The numerical criterion
applied to the independently constructed surjection
$R_i\twoheadrightarrow\mathbb T_i$ gives the asserted isomorphism and
complete-intersection property. Induction completes the proof. $\square$

If $c_{v_i}=0$, the augmentation is not isolated and the cotangent module is not finite; the criterion does not apply. If $c_{v_i}$ contains an untracked opposite branch or stabilizer factor, the two equalities can differ even when their valuations happen to agree in one example.

## 15. Jacquet--Langlands and integral level control

Quaternion algebras often make the automorphic module finite and its pairing transparent. They also impose a parity condition and allow only discrete-series local representations at their ramified finite places. Jacquet--Langlands solves the characteristic-zero representation problem. It does not, without additional work, identify the integral Hecke orders or their congruence modules.

### 15.1 Parity and the choice of quaternion algebra

Let $B/F$ be a quaternion algebra. Its ramified places form a finite set of even cardinality:

$$
\#\operatorname{Ram}(B)\equiv0\pmod2,
\tag{15.1}
$$

where real and finite places are counted together. For a definite algebra, every real place lies in $\operatorname{Ram}(B)$. Hence the number of finite ramified places has parity congruent to $d=[F:\mathbf Q]$.

At a finite ramified place, the local Jacquet--Langlands correspondence receives essentially square-integrable representations, including twists of Steinberg and supercuspidals. It does not receive an unramified principal series or a tamely ramified principal series. Therefore one may place $B$ at a target Steinberg prime, but not at an arbitrary principal-series prime merely to repair parity.

If parity forces one extra finite ramified place $r$, one must first construct an automorphic representation discrete series at $r$, usually by an independent clean level-raising theorem. The prime $r$ then belongs to the proof datum even if it is absent from the target conductor. Removing it later requires a genuine lowering or transfer argument.

### 15.2 Characteristic-zero transfer

For a cuspidal automorphic representation $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ that is discrete series at every finite place ramified in $B$, global Jacquet--Langlands gives a representation $\pi^B$ of $B^\times(\mathbf A_F)$ with matching local parameters at every place. Conversely, every non-character automorphic representation on $B^\times$ transfers to such a $\pi$.

This statement identifies irreducible representations over characteristic-zero fields. It yields equal prime-to-level Hecke eigenvalues and preserves the relevant Weil--Deligne parameters. It does not select integral lattices, prove that their Hecke orders coincide, or compare old/new congruence ideals.

### 15.3 Integral Hecke orders and type multiplicities

An integral Jacquet--Langlands control theorem suitable for this book has the following hypotheses.

1. There are finite free $\mathcal O$-lattices $M_{\mathrm{GL}_2}$ and $M_B$ realizing exactly the prescribed local types.
2. Their characteristic-zero decompositions contain the same transferred packets, with matching multiplicities and no character constituents after localization.
3. The abstract Hecke algebra away from the ramified and level primes acts on both, and its two faithful image orders are identified as saturated $\mathcal O$-orders in the common product of coefficient fields.
4. Newvector and type multiplicities at every excluded prime are one, or their higher multiplicities are explicitly carried through the pairing determinant.
5. The perfect pairings correspond up to a computed unit; if the index of one lattice in the other is nonunit, that index is included in the congruence factor.
6. The integral Galois family on one side transports through the order identification and satisfies the local deformation conditions on the other.
7. Degeneracy maps and diamond actions used before or after transfer commute with the order identification.

**Proposition 15.1 (integral transfer criterion).** Under these clauses,

$$
\mathbb T_{\mathrm{GL}_2,\mathfrak m}
\simeq
\mathbb T_{B,\mathfrak m}
\tag{15.2}
$$

as integral faithful orders, and the congruence ideals agree up to the explicitly computed lattice-index factor.

**Proof.** Clause 2 identifies both generic Hecke algebras with the same product of coefficient fields. Clause 3 says that the two integral images are the same saturated suborder, which proves (15.2); generic equality alone would give only two commensurable orders. Clauses 4 and 5 identify their self-dual lattices and determinant lines. Clauses 6 and 7 transport the deformation maps and auxiliary-level system. $\square$

### 15.4 Changing the inner form during the argument

Suppose a level-raising step changes the set of primes at which discrete series is available, so a different quaternion algebra $B'$ is preferable. A valid change of inner form has the following sequence:

    construct the required discrete-series packet
                     |
                     v
    verify parity and local transfer at every ramified place
                     |
                     v
    identify integral localized Hecke orders and pairings
                     |
                     v
    transport the Galois family, type projectors, and determinant line

Skipping the third line leaves only a characteristic-zero packet bijection and cannot support an $R=T$ comparison. If an auxiliary parity prime was introduced, the final representation on $\operatorname{GL}_2$ is recovered by characteristic-zero transfer only after the integral proof is complete. To assert that its level has lost that prime, one must additionally apply Theorem 7.1 or prove that the local transfer is unramified there; transfer itself preserves, rather than erases, its discrete-series parameter.

## 16. Solvable base change, component switching, and descent

A solvable totally real extension can separate local branches, split coefficient-prime places, or make a desired type accessible to a Hilbert or quaternionic module. It can also shrink the residual image, create self-twists, merge components, and introduce a descent ambiguity. The extension must be chosen with all of those effects in view.

### 16.1 Choosing an admissible extension

Let $K_{\bar\rho}$ be the fixed field of $\ker\bar\rho$. A finite solvable totally real Galois extension $E/F$ is **admissible for $(\bar\rho,\rho,\mathcal D^P)$** if:

1. $E$ is presented by a tower

   $$
   F=F_0\subset F_1\subset\cdots\subset F_s=E
   \tag{16.1}
   $$

   with every $F_i/F_{i-1}$ cyclic of prime degree;
2. $E\cap K_{\bar\rho}=F$, and it is also disjoint from every auxiliary cyclotomic and self-twist field used in prime selection;
3. every place above $\ell$ has the local behavior required by the finite-flat theorem, preferably complete splitting when one wants to retain the identical local field;
4. for each $v\in P$, the completions $E_w/F_v$ have the prescribed solvable local behavior and the restriction maps on local deformation rings are defined on the selected integral components;
5. no new ramification is introduced at places where the automorphic level or determinant cannot absorb it;
6. the base change of the known residual automorphic representation remains cuspidal; and
7. the local prescriptions, total reality, and disjointness conditions are simultaneously compatible with the solvable existence theorem being used.

The last clause matters. Arbitrary completions cannot be prescribed independently in a global Galois extension. The construction proceeds one cyclic layer at a time, using split auxiliary places to enforce disjointness and checking after each layer that the remaining local requirements are still realizable.

### 16.2 Preserving image, determinant, and cuspidality

Disjointness in clause 2 gives

$$
\bar\rho(G_E)=\bar\rho(G_F).
\tag{16.2}
$$

Thus any adequacy property depending only on the residual image is preserved. Without disjointness the left side can be a proper subgroup, and an adequate representation over $F$ can become dihedral, reducible, or otherwise too small over $E$.

The determinant restricts exactly:

$$
\det(\rho|_{G_E})=(\psi|_{G_E})(\chi_\ell|_{G_E}).
\tag{16.3}
$$

Since $E$ is totally real, total oddness is also preserved. At the automorphic level, solvable base change of the residual source must be cuspidal. A sufficient check is that the source is not automorphically induced from a character of a proper subextension encountered in (16.1). Residual absolute irreducibility with the disjointness condition often detects this, but the cuspidality theorem must still be applied at each cyclic step.

Self-twists require a separate check. Even when (16.2) holds, an automorphic base change can acquire a character $\xi$ with

$$
\pi_E\simeq\pi_E\otimes\xi.
\tag{16.4}
$$

Such a twist enlarges a descent fiber and can destroy multiplicity one in a localized packet. The admissibility audit either excludes (16.4) or records the finite twist group and carries it through descent.

### 16.3 Modularity after restriction

Restriction gives a lift

$$
\rho_E=\rho|_{G_E}.
\tag{16.5}
$$

Finite flatness is preserved by base change of finite flat group schemes. Away from $\ell$, the full Weil--Deligne parameter restricts; in particular, nonzero Steinberg monodromy remains nonzero. Conductors can change under ramified restriction, so the local type for the deformation problem over $E$ is the actual restricted type, not the old conductor exponent copied from $F$.

Suppose that for every $w\mid v\in P$, the target point and an available automorphic point lie on the same specified component of the local ring over $E_w$. Suppose also that the analogues of NM-I and NM-II, the route-specific sharp-balance or NM-III clauses, any base equality required by the relative route, and Theorem 13.1 hold over $E$. Then

$$
\rho_E\simeq\rho_{\Pi_E}
\tag{16.6}
$$

for a cuspidal automorphic representation $\Pi_E$ over $E$.

This is the component-switching step. It is valid only after proving the component relation over $E_w$. In ring language, restriction of local deformations gives

$$
R_{E_w}^{\square,\mathcal D_w}
\longrightarrow R_{F_v}^{\square,\mathcal D_v}.
\tag{16.7}
$$

The two $F_v$-points become compatible if their induced $E_w$-points factor through the same named component quotient of the source in (16.7). Equality of restricted inertial types does not imply this. One proves it by an explicit local ring calculation, a flat connectedness theorem with its hypotheses checked, or an integral congruent-form construction on that component.

### 16.4 Recursive descent and the character fiber

The global representation $\rho_E$ is invariant under $\operatorname{Gal}(E/F)$ because it is the restriction of $\rho$. By (16.6), strong multiplicity one and local--global compatibility imply

$$
\Pi_E^\sigma\simeq\Pi_E
\qquad
(\sigma\in\operatorname{Gal}(E/F)).
\tag{16.8}
$$

For a noncyclic solvable group, (16.8) is not by itself a descent theorem. Descend recursively along (16.1). Suppose $\Pi_i$ has been obtained over $F_i$ and is invariant under

$$
C_i=\operatorname{Gal}(F_i/F_{i-1}).
\tag{16.9}
$$

The cyclic descent theorem gives a nonempty fiber of descents only after its central-character and local compatibility obstruction has been checked. When nonempty, the fiber is a torsor under

$$
X_i=\ker\!\left(
\operatorname{Hom}(F_{i-1}^\times\backslash\mathbf A_{F_{i-1}}^\times,\mathbf C^\times)
\longrightarrow
\operatorname{Hom}(F_i^\times\backslash\mathbf A_{F_i}^\times,\mathbf C^\times)
\right).
\tag{16.10}
$$

If $\pi_{i-1}$ is one descent, every other is $\pi_{i-1}\otimes\eta$ for $\eta\in X_i$. Twisting changes the central character by $\eta^2$.

Choose any descent $\pi_{i-1}$. Its Galois representation and $\rho|_{G_{F_{i-1}}}$ have isomorphic restrictions to $G_{F_i}$. By (16.2), the residual restrictions at every layer have the original absolutely irreducible image, so the characteristic-zero restrictions are absolutely irreducible. Clifford theory therefore gives a character

$$
\eta_i:G_{F_{i-1}}/G_{F_i}\longrightarrow\overline{\mathbf Q}_\ell^\times
\tag{16.11}
$$

such that

$$
\rho_{\pi_{i-1}}\simeq
\rho|_{G_{F_{i-1}}}\otimes\eta_i.
\tag{16.12}
$$

The determinant comparison forces $\eta_i^2=1$ when both sides have the prescribed determinant. The automorphic character corresponding to $\eta_i$ lies in $X_i$, so replacing $\pi_{i-1}$ by $\pi_{i-1}\otimes\eta_i^{-1}$ removes the ambiguity without changing its base change. This supplies the compatible descent at the next layer.

The existence of the global extension $\rho|_{G_{F_{i-1}}}$ is what neutralizes the twisting obstruction in this argument. If one starts only with the invariant representation $\Pi_i$ and no compatible global Galois parameter, a projective obstruction can remain, and a class in the relevant second cohomology group must be checked. Recursive invariance alone does not remove it.

### 16.5 Recovering the original local components

Iterating Section 16.4 yields a cuspidal representation $\pi$ over $F$ with

$$
\rho_\pi\simeq\rho.
\tag{16.13}
$$

The equality follows globally from the compatible choice at every cyclic
layer, not from solvable invariance alone. Restricting (16.13) to $G_{F_v}$
recovers the intrinsic local parameter of $\rho_v$, including inertia and
monodromy. An ordered line, $U_v$-refinement, or flag is recovered only when
it is unique for $\rho_v$ or when it has been transported explicitly through
the cyclic descent data; abstract equality of representations does not
recover a nonintrinsic enhancement. Thus any merging of components after
passage to $E_w$ is harmless only because the final global identity
distinguishes the original representation downstairs, with any required
enhancement tracked separately.

We record the route as a theorem.

**Theorem 16.1 (solvable switching and descent).** Assume there is an admissible extension $E/F$ satisfying Sections 16.1--16.2; the restricted target and a residual automorphic source are component-compatible at every place as in (16.7); controlled nonminimal modularity lifting holds over every field in the tower where it is invoked; cyclic base change and descent hold with all local compatibility and central-character hypotheses; each twisting character in (16.11) is identified and corrected; and every nonintrinsic ordered refinement claimed at the end is transported through the tower. Then modularity of $\rho|_{G_E}$ implies modularity of $\rho$ over $F$, with the original determinant, the intrinsic local types at places away from $\ell$ covered by local compatibility, and precisely the ordered refinements that were so transported. At $v\mid\ell$, the conclusion is the finite-flat Galois-lattice statement of Theorem 13.1 unless a stronger $\ell$-adic local--global compatibility theorem is assumed.

**Proof.** Apply Theorem 13.1 over $E$ to obtain (16.6). Equations (16.8)--(16.12) descend it one cyclic layer at a time, correcting the unique character ambiguity by the global representation $\rho$. At the bottom, Chebotarev identifies the resulting Galois representation with $\rho$, and restriction gives the asserted local conclusions. $\square$

## 17. The ordinary residually reducible maneuver

The absolutely irreducible finite-flat theorem and an ordinary residually reducible theorem solve different deformation problems. The former uses the full type-$(0,1)$ local space and Taylor--Wiles prime detection for $\operatorname{ad}^0\bar\rho$. The latter chooses an ordinary line, may localize at an Eisenstein residual ideal, and controls a reducibility ideal by ordinary families. Neither theorem may be substituted for the other.

### 17.1 Why it is a different theorem

At a place $v\mid\ell$, an ordinary lift has a chosen exact sequence

$$
0\longrightarrow A(\psi_{1,v})
\longrightarrow V_A
\longrightarrow A(\psi_{2,v})
\longrightarrow0,
\tag{17.1}
$$

with specified restrictions of $\psi_{1,v}$ and $\psi_{2,v}$ to inertia and with determinant $\psi_{1,v}\psi_{2,v}=\delta_v$. This line is part of the deformation object. A supersingular finite-flat representation has no such line. Conversely, a nearly ordinary family can contain weights and ramified characters outside finite-flat type $(0,1)$.

If $\bar\rho$ is globally reducible, the universal matrix representation and the non-Eisenstein Hecke localization used in Chapter 11 are unavailable in their present form. One instead works with a pseudorepresentation or a generalized matrix algebra and its reducibility ideal. Adequacy of an absolutely irreducible image is not a meaningful substitute.

### 17.2 The exact deep input

The following theorem is a separate deep input, not a consequence of Chapters 11--13.

**Deep Ordinary Input O.** Let $F$ be totally real and $\ell$ odd. Let $\rho:G_F\to\operatorname{GL}_2(\mathcal O')$ be irreducible in characteristic zero and ordinary at every $v\mid\ell$. Assume:

1. the residual semisimplification is

   $$
   \bar\rho^{\mathrm{ss}}=\bar\chi_1\oplus\bar\chi_2
   \tag{17.2}
   $$

   with $\bar\chi_1\ne\bar\chi_2$; the extension orientation is fixed, and for every real complex conjugation $c$ one has

   $$
   \bar\chi_1(c)\bar\chi_2(c)=-1;
   $$
2. at every $v\mid\ell$, the two residual ordinary characters are distinguished on the decomposition group, and the prescribed quotient character is unramified after the named finite-order twist;
3. writing $\bar\theta_{ij}=\bar\chi_i\bar\chi_j^{-1}$, the exact exceptional invariants vanish:

   $$
   H^0(F,k(\bar\theta_{ij}))
   =H^0(F,k(\bar\theta_{ij})(1))=0
   \qquad(i\ne j),
   \tag{17.2a}
   $$

   and the two off-diagonal Selmer structures $\mathcal S_{12},\mathcal S_{21}$ are explicitly defined from the ordinary local lines; the named ordinary theorem proves the required torsion/control and Fitting-ideal statements for their dual modules, rather than referring to unspecified “relevant Selmer groups”;
4. $\det\rho=\psi\chi_\ell$ and every ordinary line has determinant-compatible characters;
5. a known characteristic-zero cuspidal ordinary automorphic representation $\pi_0$ has residual pseudorepresentation $\operatorname{tr}(\bar\chi_1\oplus\bar\chi_2)$ in the same multiplicity-free Eisenstein block, with weight, central character, ordinary refinements, and every sign or type away from $\ell$ equal to the listed deformation data, and its point factors through the same named ordinary component quotient as $\rho$;
6. over a named ordinary weight algebra $\Lambda^{\mathrm{ord}}$, an integral ordinary projector produces a finite free control module and a faithful Hecke order at every fixed nonminimal and auxiliary level, with exact specialization to the weight and finite-order characters of $\rho$;
7. the ordinary pseudodeformation ring is represented with its chosen lines and has a generalized-matrix-algebra presentation with off-diagonal modules $B$ and $C$ and reducibility ideal

   $$
   I_{\mathrm{red}}=BC;
   \tag{17.2b}
   $$

   the Selmer modules in clause 3 control $B$ and $C$ by the explicitly stated maps and Fitting inclusions of the named theorem;
8. after specialization at the weight and finite-order characters of $\rho$, there is a canonical surjection

   $$
   R^{\mathrm{ord}}\twoheadrightarrow
   \mathbb T^{\mathrm{ord}},
   \tag{17.2c}
   $$

   and $\pi_0$ supplies a compatible augmentation $\lambda_0$ of both sides, constructed independently of the desired automorphy of $\rho$; the target is finite flat, the source cotangent module at $\lambda_0$ is finite, and the Eisenstein/reducibility comparison proves

   $$
   \operatorname{length}_{\mathcal O'}
   \Phi_{R^{\mathrm{ord}},\lambda_0}
   \le
   \operatorname{length}_{\mathcal O'}
   \bigl(\mathcal O'/
   \eta_{\mathbb T^{\mathrm{ord}},\lambda_0}\bigr);
   \tag{17.2d}
   $$
9. every added prime away from $\ell$ satisfies the integral Ihara/type and
   local-compatibility hypotheses analogous to NM-I--NM-II, together with
   the determinant-factor or component-support clauses used by the chosen
   ordinary comparison; and
10. any solvable base change and descent used in the proof satisfies all conditions of Chapter 16.

Then $\rho$ is automorphic of the prescribed ordinary weight and local types.

The input is a black-box theorem schema because the preceding books do not develop ordinary families or Eisenstein congruences. An application must name a theorem that supplies clauses 3 and 6--8 with the displayed Selmer structures and ideals. Merely citing an “ordinary modularity theorem” without matching these data does not verify Input O.

### 17.3 Proof architecture

The name often attached to this maneuver conceals six logically distinct steps.

First, if necessary choose an admissible solvable totally real extension on which the residual characters, ordinary lines, and local signs have the desired shape. Disjointness must preserve the nontrivial character ratio, and descent characters must be recorded from the start.

Second, construct the ordinary deformation functor with the line (17.1) included. Its tangent complex has diagonal character directions and two off-diagonal Selmer groups. The ideal $I_{\mathrm{red}}$ cutting out reducible pseudorepresentations is generated by the product of the two off-diagonal generalized-matrix-algebra modules; it is not the maximal ideal of an absolutely irreducible deformation ring.

Third, construct the ordinary Hecke algebra by applying an integral ordinary projector to a tower in $\ell$-power level. Control identifies its weight-two specialization and proves finite freeness over the weight algebra. At fixed nonminimal primes, the type projectors and degeneracy maps must commute with the ordinary projector and remain saturated.

Fourth, construct (17.2c) and the common augmentation $\lambda_0$ from $\pi_0$. The comparison of $I_{\mathrm{red}}$ with the Eisenstein congruence ideal is governed by the two named character Selmer structures in clause 3. Their control and Fitting statements supply (17.2d); this replaces adequate-image Taylor--Wiles prime detection. The target $\rho$ supplies a point of the source ring, not the augmentation on the Hecke side used to prove the comparison.

Fifth, apply the numerical criterion to (17.2c)--(17.2d) at $\lambda_0$. It identifies the local ordinary component containing $\rho$ with the faithful specialized ordinary Hecke order. The point of that ring defined by $\rho$ then produces a Hecke character and an automorphic representation with the same Galois representation.

Sixth, if the argument took place after base change, descend recursively and correct the character fiber as in (16.10)--(16.12).

This architecture explains why an irreducible finite-flat representation cannot be declared ordinary and passed through Input O. It also explains why a globally reducible residual representation cannot be passed through Theorem 13.1.

### 17.4 Interaction with base change

Base change is useful in the ordinary argument only when it preserves distinction:

$$
\bar\chi_1|_{G_{E_w}}\ne
\bar\chi_2|_{G_{E_w}}
\qquad(w\mid\ell).
\tag{17.3}
$$

If the two characters become equal, the ordinary line is no longer unique and the represented local condition changes. Likewise, if the global ratio becomes trivial or cyclotomic over $E$, the character Selmer comparison in clause 3 acquires invariants and the reducibility-ideal calculation fails.

When Input O is used after such a checked base change, the resulting automorphic representation descends by Theorem 16.1. The correcting twist must preserve the chosen ordinary determinant and local characters. Determinant equality forces its square to be trivial, but its local action on the two ordinary characters must still be checked before claiming the original ordinary type downstairs.

## 18. Hardly ramified representations

The phrase “hardly ramified” is useful only if it denotes a finite list of local alternatives. Here it means that the lift is minimal except for clean conductor-one special primes. Tame principal-series primes belong to the broader controlled theorem, not to this narrower phrase.

### 18.1 A precise definition

Let $\bar\rho$ be absolutely irreducible and let $\rho$ be a fixed-determinant lift. Let $S_{\mathrm{ft}}$ be a set of places at which $\bar\rho$ has a fixed prime-to-$\ell$ finite inertial type, and let $S_{\mathrm{st}}$ be the set at which it has primitive nonzero unipotent inertia.

**Definition 18.1.** The lift $\rho$ is **hardly ramified relative to $\bar\rho$** if the following conditions hold.

1. At every $v\mid\ell$, $\rho_v$ is finite flat of type $(0,1)$ in the existential integral sense of Section 4.1.
2. At $v\in S_{\mathrm{ft}}$, $\rho_v$ has the same specified prime-to-$\ell$ integral inertial type as $\bar\rho_v$ and lies on its minimal component.
3. At $v\in S_{\mathrm{st}}$, both representations have conductor exponent one, $\bar\rho_v$ has nonzero rank-one monodromy, and $\rho_v$ lies on the same fixed-sign primitive Steinberg component.
4. There is a finite set $P_{\mathrm{hr}}$, disjoint from $S_{\mathrm{ft}}\cup S_{\mathrm{st}}\cup\{v:v\mid\ell\}$, such that $\bar\rho_v$ is unramified and $\rho_v$ is a generic point of the closed special condition (3.16), with conductor exponent one, for every $v\in P_{\mathrm{hr}}$.
5. For $v\in P_{\mathrm{hr}}$, residual Frobenius has ordered eigenvalues

   $$
   \{\bar\psi_v(\operatorname{Frob}_v)q_v,
   \bar\psi_v(\operatorname{Frob}_v)\},
   \tag{18.1}
   $$

   and the chosen order is the stable-line order of $\rho_v$.
6. At every Steinberg place in $S_{\mathrm{st}}\cup P_{\mathrm{hr}}$,

   $$
   q_v\not\equiv\pm1\pmod\ell,
   \tag{18.2}
   $$

   and all stabilizer, multiplicity, and self-twist exclusions required by the clean integral newvector theorem hold.
7. Outside the places named above, $\rho$ is unramified. In particular, it has no additional principal-series, supercuspidal, or wild ramification.

The prime-to-$\ell$ Artin conductor is consequently

$$
\mathfrak N(\rho)
=
\mathfrak N_{\mathrm{ft}}
\prod_{v\in S_{\mathrm{st}}}v
\prod_{v\in P_{\mathrm{hr}}}v,
\tag{18.3}
$$

where $\mathfrak N_{\mathrm{ft}}$ records the exact conductor exponents of the fixed finite types, while

$$
\mathfrak N(\bar\rho)
=
\mathfrak N_{\mathrm{ft}}
\prod_{v\in S_{\mathrm{st}}}v.
\tag{18.4}
$$

Thus the only conductor increase is one at each prime of $P_{\mathrm{hr}}$. For a semistable representation over $\mathbf Q$, $S_{\mathrm{ft}}$ is empty and both conductors are squarefree away from $\ell$.

Definition 18.1 is arithmetic and local. A **lifting-admissible hardly
ramified datum** additionally requires residual modularity and adequacy, the
coefficient-prime Schur and determinant-twist hypotheses of Sections
4.1--4.2, the independent Ihara and level-control theorems, NM-I and NM-II,
and whichever sharp-balance or NM-III clauses the chosen proof route uses on
the named components, together with any base equality required by the
relative route. Keeping these global requirements out of the adjective makes
it possible to diagnose which part of an application has failed.

### 18.2 The absolutely irreducible theorem

**Theorem 18.2 (hardly ramified modularity lifting).** Let $F$ be $\mathbf Q$ or a totally real field, let $\ell>2$ be unramified in $F$, and let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{18.5}
$$

be continuous, irreducible, and totally odd, with determinant $\psi\chi_\ell$. Suppose:

1. $\bar\rho$ is absolutely irreducible, automorphic of parallel weight two, and adequate for the Taylor--Wiles selection used over $F$;
2. $H^0(F,\operatorname{ad}^0\bar\rho(1))=0$;
3. the local finite-flat Schur hypotheses of Section 4.2 hold, and for every
   $v\mid\ell$ the finite-order determinant factor has a square root
   $\eta_v$ whose twists extend through the finite-flat integral category as
   in Section 4.1;
4. $\rho$ is hardly ramified relative to $\bar\rho$ in the sense of Definition 18.1;
5. the selected fixed-level type module is independently nonzero, either by
   a direct automorphic construction or by lowering the residual system to
   the exact minimal datum and raising to every selected sign through
   Theorems 7.1 and 6.1 without circular use of this theorem; and
6. NM-I and NM-II hold on the component tuple containing $\rho$, and one of
   the three route-specific packages in Theorem 13.1, clause 7, holds.

Then $\rho$ is automorphic of parallel weight two, and its automorphic representation has exactly the conductor and local signs in (18.3).

**Proof.** Every place in $S_{\mathrm{ft}}\cup S_{\mathrm{st}}$ carries its minimal represented condition. Every place of $P_{\mathrm{hr}}$ carries the smooth closed special quotient (3.18) and the target lies in its nonzero-monodromy generic locus. Conditions (18.1)--(18.2) give the integral branch and Ihara hypotheses and, for the relative route, the primitive local determinant setting. Thus the datum is controlled in the sense of Section 5.4. Apply Theorem 13.1 and then (13.5a) to recover nonzero monodromy and the signs. The conductor formula follows from Section 5.1. $\square$

For the clean rational cyclotomic realization imported from Book 155, one
retains its stronger restriction $\ell\ge7$ and all its exact-level
hypotheses. The theorem over a general totally real field requires the
Hilbert or quaternionic forms of NM-I and NM-II and whichever independent
nonminimal determinant or support clauses the chosen route uses; it is not a
consequence of the rational case.

If a lift has an added ordered tame principal-series prime, it is **suitably
controlled** rather than hardly ramified. Theorem 13.1 still applies when the
enhanced local ring, saturated integral type lattice, and exact local
compatibility have been supplied, together with component support for the
support route or the determinant factor (8.12) for the numerical route.

### 18.3 The $3$-adic boundary

For every residue cardinality $q$ prime to $3$,

$$
q\equiv\pm1\pmod3.
\tag{18.6}
$$

Hence the clean exclusion (18.2) leaves no away-from-$3$ Steinberg prime at all. Moreover, the rational minimal theorem imported from Book 155 assumes $\ell\ge7$. Theorem 18.2 therefore cannot simply be relabelled as a $3$-adic lifting theorem.

A direct $3$-adic version requires a separate package:

1. a small-image prime-selection or derived-patching theorem replacing adequacy where it fails;
2. integral automorphic lattices with all $3$-torsion stabilizers removed or explicitly measured;
3. at $q\equiv1\pmod3$, a framed or line-enhanced treatment of scalar Frobenius and colliding $U_q$ roots;
4. at $q\equiv-1\pmod3$, a $U_q$-selected Ihara theorem and a two-factor determinant calculation replacing (6.11);
5. finite-flat local control at $3$ within Sections 4.1--4.2, including the
   determinant square-root condition and the unramified and Schur
   hypotheses; and
6. the small-prime analogues of NM-I and NM-II, together with either the
   sharp absolute generator count or the applicable relative determinant and
   component-support clauses of NM-III.

With all six inputs, the proof of Theorem 18.2 applies using the refined ledger. Without them, a hardly ramified $3$-adic representation belongs to the classification problem of the later small-ramification books, not automatically to this lifting theorem.

A frequent safe route is to establish automorphy at a coefficient prime $\ell\ge7$ where Theorem 18.2 applies, place the representation in a compatible system, and then identify its $3$-adic member by common Frobenius polynomials. That route requires the compatible-system and changing-prime theorems; it does not turn the $3$-adic member into an input to the $\ell$-adic proof.

If the residual $3$-adic representation is reducible and the target is ordinary, only Deep Ordinary Input O can apply, with its distinguished-character and Eisenstein-control hypotheses. Absolute irreducibility and ordinary reducibility are not interchangeable cases.

### 18.4 Elliptic curves and geometric representations

Let $A/F$ be an elliptic curve and let $\rho=T_\ell A\otimes_{\mathbf Z_\ell}\mathcal O'$. Its determinant is $\chi_\ell$. If $A$ has good reduction at every $v\mid\ell$, the torsion group schemes $A[\ell^n]$ give the finite-flat condition of type $(0,1)$.

At a multiplicative place $v\nmid\ell$, the representation is an unramified quadratic twist of an extension

$$
0\longrightarrow\mathcal O'(1)
\longrightarrow T_\ell A
\longrightarrow\mathcal O'
\longrightarrow0.
\tag{18.7}
$$

It has conductor exponent one and nonzero monodromy. In the Tate-curve description, the residual monodromy is the reduction of the valuation of the Tate parameter, equivalently of the minimal discriminant valuation up to the standard normalization. Thus:

- if that valuation is nonzero modulo $\ell$, the prime belongs to $S_{\mathrm{st}}$;
- if it is zero modulo $\ell$, the residual representation can be unramified and the prime belongs to $P_{\mathrm{hr}}$;
- in the second case, reduction of (18.7) gives the level-raising eigenvalues and sign in (18.1).

Consequently a semistable elliptic curve with good reduction above $\ell$, clean residue cardinalities, and no additive primes gives a hardly ramified representation relative to an absolutely irreducible residual lattice. Theorem 18.2 proves its modularity only after residual modularity, adequacy, level lowering, and the integral infrastructure have been checked.

If $A$ has multiplicative reduction at a place above $\ell$, its representation is semistable ordinary rather than finite flat of the smooth type used here. If it has additive or wildly ramified reduction away from $\ell$, Definition 18.1 also fails. Those cases require the separately stated ordinary, crystalline-semistable, or wild-type infrastructure; they are not absorbed by calling the curve geometric.

## 19. Four hostile diagnostics

The surest way to test a nonminimal argument is to run one prime through every layer: local ring, tangent space, conductor, automorphic lattice, congruence factor, global presentation, and final point. We do this for four cases in which a familiar slogan otherwise hides the failure.

### 19.1 One added Steinberg prime

Let $p\nmid\ell$, put $q=q_p$, assume trivial central character, and suppose

$$
\bar\rho(\operatorname{Frob}_p)
=
\begin{pmatrix}\varepsilon q&0\\0&\varepsilon\end{pmatrix},
\qquad
q\not\equiv\pm1\pmod\ell.
\tag{19.1}
$$

The residual representation is unramified. The target has the form

$$
\rho|_{G_{F_p}}\sim
\begin{pmatrix}
\psi\chi_\ell&*\\
0&\psi
\end{pmatrix},
\qquad
*|_{I_p}\ne0,
\tag{19.2}
$$

with sign $\varepsilon=\bar\psi(\operatorname{Frob}_p)$.

**Local-ring audit.** The unramified and closed special framed rings are both smooth of relative dimension three, but their genuine tangent directions are different. Their intersection is

$$
R_p^\cap
\simeq
R_p^{\square,\mathrm{sp}}/(m_p)
\simeq
R_p^{\square,\mathrm{ur}}/
\bigl(T_p-\varepsilon(q+1)\bigr),
\tag{19.3}
$$

after the compatible framed coordinates have been chosen. It has only the two line-position framing directions. The maps are

$$
R_p^{\square,\mathrm{amb}}\twoheadrightarrow
R_p^{\square,\mathrm{sp}}\twoheadrightarrow R_p^\cap,
\qquad
R_p^{\square,\mathrm{amb}}\twoheadrightarrow
R_p^{\square,\mathrm{ur}}\twoheadrightarrow R_p^\cap.
\tag{19.4}
$$

There is no canonical arrow between the middle two rings. Cohomologically, $L_p^{\mathrm{sp}}$ and $L_p^{\mathrm{ur}}$ are distinct one-dimensional lines in the ambient tangent space, and their common unframed tangent is zero. Any global Selmer comparison must pass through this common condition twice.

The ambient unrestricted tangent is larger than three here. Indeed $W(1)$ has an invariant coming from the lower-left root space, so (3.3) gives framed tangent dimension four. This is why the two smooth three-dimensional branches can meet inside a singular ambient space.

**Conductor audit.** One has

$$
a(\bar\rho_p)=0,
\qquad
a(\rho_p)=1.
\tag{19.5}
$$

The conductor increase is exactly one. It comes from nonzero monodromy, not from the diagonal characters.

**Automorphic audit.** The lower eigensystem satisfies

$$
a_p\equiv\varepsilon(q+1)\pmod\varpi.
\tag{19.6}
$$

The degeneracy Gram determinant factors as

$$
(q+1)^2-a_p^2
=
\bigl(q+1-\varepsilon a_p\bigr)
\bigl(q+1+\varepsilon a_p\bigr).
\tag{19.7}
$$

The second factor is a unit, so the numerical cost is

$$
\operatorname{ord}_\varpi
\bigl(q+1-\varepsilon a_p\bigr).
\tag{19.8}
$$

Ihara injectivity gives a nonzero residual new class; saturation lifts it to a torsion-free new localization; the integral $U_p=\varepsilon$ projector selects the component. Omitting any of those three assertions stops the argument at a congruence in a quotient that may be torsion.

**Global audit.** Recompute the nonminimal dual Selmer group. In the framed ledger, adding $p$ raises $t$ by one, adds three local-base variables, adds four gauge variables, and changes $G^\square-b^\square$ by one. These changes cancel in (9.16). In the relative route, NM-III clauses 1--4 insert the same new factor (19.8) in the deformation cotangent and automorphic congruence ideals, on top of Book 155's already proved base equality. In the sharp direct route, the exact absolute count instead gives (11.8b), and no determinant calculation is used to kill the kernel.

**Verdict.** The prime is controlled. If one instead draws $R_p^{\mathrm{sp}}\twoheadrightarrow R_p^{\mathrm{ur}}$, omits saturation, or identifies the target merely because a raised form exists, the proof is invalid.

### 19.2 One tame principal-series prime

Let $\bar\rho_p$ be unramified with distinct Frobenius eigenlines. Let $\theta$ be a nontrivial tame character of $\ell$-power order, stable under Frobenius, and suppose $\theta\equiv1\pmod\varpi$. Consider a target whose ordered inertial characters are

$$
(\theta,\theta^{-1}),
\tag{19.9}
$$

with both characters nontrivial and with unramified determinant.

**Local-ring audit.** This case is not covered by the prime-to-$\ell$ fixed-type theorem of Section 3.2. The order of the inertia quotient is divisible by $\ell$, so averaging and semisimple idempotents are unavailable. The represented object used here must retain the two ordered Frobenius lines and impose the two characters literally. With distinct residual Frobenius eigenvalues, the line-enhanced coordinates give a smooth three-dimensional framed chart for each fixed character pair, as in (3.20). Forgetting the lines or asserting that the entire coarse fixed-type locus is smooth is unsupported.

The universal character problem lives over $\mathcal O[\Delta_p]$. Its generic character factors meet in the special fiber. The unramified and fixed nontrivial-character problems are not nested. Their incidence quotient contains equations

$$
\theta(\tau)-1=0
\tag{19.10}
$$

and can be $\varpi$-power torsion with no characteristic-zero point. Thus the relative cost includes the integral character-congruence factor; it is not read from a difference of tangent dimensions.

**Conductor audit.** Each nontrivial tame character has conductor exponent one, so

$$
a(\rho_p)=a(\theta)+a(\theta^{-1})=2,
\qquad
a(\bar\rho_p)=0.
\tag{19.11}
$$

The increase is two even though the determinant is unramified. Using the conductor of $\theta\theta^{-1}$ would incorrectly give zero.

**Automorphic audit.** Because the character group has $\ell$-power order, the characteristic-zero central idempotent for the $\theta$-type generally has a denominator divisible by $\ell$. One therefore needs a saturated integral type lattice or a derived type-selection complex, not an averaged projector. Its determinant

$$
c_p(\theta,\theta^{-1})
\tag{19.12}
$$

must be computed from that lattice and matched with the incidence equations (19.10). A prime-to-$\ell$ type multiplicity theorem does not perform this calculation.

**Global audit.** If the enhanced fixed-character chart is used, its neutral framed dimension is three and the smooth ledger applies. If the whole group-algebra family is retained, $\mathcal O[\Delta_p]$ belongs in the local base and its nonregular special fiber must be carried into the patched complex. The automorphic module must meet the exact generic character factor containing the target.

**Verdict.** The prime is controlled only under enhanced representability,
the saturated type lattice, and exact local compatibility. A support proof
additionally needs component support, while a relative numerical proof needs
the determinant factor (19.12). Calling (19.9) a tame type and invoking the
prime-to-$\ell$ theorem loses the central integral difficulty.

### 19.3 One scalar or vexing prime

There are two different failures.

Suppose first that $q\equiv1\pmod\ell$ in the level-raising situation. The eigenvalues in (19.1) coincide, so residual Frobenius is scalar. Then

$$
h^0(F_p,W)=3,
\qquad
h^0(F_p,W(1))=3,
\tag{19.13}
$$

and the unrestricted framed tangent has dimension six. There is no intrinsic residual eigenline. A line-enhanced special problem is representable, but forgetting the flag is not the smooth coarse quotient (3.18). The roots of the old $U_p$ polynomial collide, so no integral Hensel idempotent selects a branch. Residual multiplicity can increase, and the clean Ihara statement does not identify the flag-dependent kernel.

Now suppose $q\equiv-1\pmod\ell$. Residual Frobenius in (19.1) is nonscalar and the two $U_p$ roots $\varepsilon$ and $-\varepsilon$ are distinct. Nevertheless

$$
q+1-\varepsilon a_p\equiv0,
\qquad
q+1+\varepsilon a_p\equiv0
\pmod\varpi.
\tag{19.14}
$$

The trace congruence does not determine the sign, and the Gram determinant has two nonunit factors. A $U_p$ projector can distinguish the signs, but the one-factor equality (6.11) is false. The determinant line must measure both the chosen branch and the congruence with its companion.

The diagnostic questions are therefore:

1. Is a flag part of the local functor, and is its framed ring actually presented?
2. Is the $U_p$ branch selected integrally?
3. Which stabilizer and component-group torsion appears in the Ihara sequence?
4. Is the local determinant one factor, two factors, or a matrix determinant of higher rank?
5. Does the automorphic module meet the same flag/component as the target?

If any answer is absent, the prime is not cleanly controlled. It may be treatable by a vexing-prime theorem, a different type, or solvable component switching, but it cannot be inserted into the dimension-three row of Section 3.6.

### 19.4 One solvable-descent ambiguity

Let $E/F$ be quadratic and let $\eta$ be its associated quadratic character. If $\pi$ is cuspidal over $F$, then

$$
\operatorname{BC}_{E/F}(\pi)
\simeq
\operatorname{BC}_{E/F}(\pi\otimes\eta).
\tag{19.15}
$$

The two descents have the same central character because $\eta^2=1$. At a place where $\eta$ is ramified, however, their local types differ by $\eta_v$. Thus base change has forgotten information needed by the target deformation problem.

Suppose $\rho|_{G_E}$ is absolutely irreducible, as it is under the disjoint admissibility condition of Section 16.1, and patching over $E$ gives

$$
\rho|_{G_E}\simeq\rho_{\Pi_E}
\tag{19.16}
$$

and a cyclic descent theorem produces $\pi$. From (19.16) alone, Clifford theory yields only

$$
\rho_\pi\simeq\rho
\quad\text{or}\quad
\rho_\pi\simeq\rho\otimes\eta.
\tag{19.17}
$$

Frobenius traces at primes split in $E$ cannot distinguish the two. Compare the full representations over $G_F$, determine the character in (19.17), and twist the automorphic descent by the same character if necessary. This preserves base change and changes the local types back to those of $\rho$.

For a longer solvable tower, the choices at successive cyclic layers form twisting torsors. They must be chosen compatibly. An arbitrary choice at each layer can have a nontrivial cocycle obstruction and fail to descend to the bottom even though the top representation is invariant.

**Verdict.** “The base change is invariant, hence it descends to $\rho$” omits both existence and identification. The correct conclusion follows only after the cyclic descent fiber is nonempty, the character in every fiber is computed, determinant and central character are checked, and the twists are compatible through the whole tower.

## 20. Limitations and failure boundaries

The main theorem is deliberately narrower than the set of all potentially semistable two-dimensional representations. Each excluded case corresponds to a missing local moduli theorem, an integral automorphic theorem, or a global prime-selection/descent theorem.

### 20.1 Small coefficient primes and small images

At $\ell=2$, scalars lie in $\operatorname{ad}^0$, the trace pairing is degenerate, and the fixed-determinant dual module is not identified with $W(1)$ by the argument used here. The finite-flat power-series theorem of Section 4.2 also assumes $\ell>2$. Oddness and the real-place correction require a different formulation. None of Theorems 12.1A--12.3, 13.1, or 18.2 includes $\ell=2$.

At $\ell=3$, the finite-flat theorem can apply locally, but the clean away-from-$\ell$ exclusions collapse as in (18.6), and common residual images may not meet the adequate-image hypotheses. At $\ell=5$, exceptional projective images and stabilizer torsion can still obstruct prime selection or multiplicity one. A small-prime theorem must replace each failed clause explicitly.

More generally, a dihedral, exceptional, or otherwise small residual image can have:

- a nonzero $H^0(F,W(1))$;
- too few regular conjugacy classes to kill dual Selmer;
- self-twists that merge automorphic packets; or
- failure of residual multiplicity one.

Solvable base change does not cure these automatically. It usually restricts the image and can make the problem worse.

### 20.2 Wild types and unreached components

The prime-to-$\ell$ fixed-type theorem permits a finite wild residue-characteristic group because its order is still prime to $\ell$, provided an integral type and Frobenius intertwiner are fixed. It does not cover an inertia quotient whose order is divisible by $\ell$, except for the explicitly enhanced tame charts constructed in Section 3.5.

A general wildly ramified potentially semistable type can have several components, nonreduced special fiber, and obstruction equations. Its conductor may jump on component boundaries. To include it one needs:

1. a represented integral local condition;
2. an exact component and dimension theorem;
3. an integral automorphic type lattice;
4. Hecke-valued local--global compatibility on that quotient;
5. a determinant-line comparison; and
6. automorphic support at the target generic point.

Absent any one clause, only the components already reached by the automorphic module can appear in a componentwise theorem. Generic equality of inertial types is not a component-hopping result.

### 20.3 Failures of integral automorphic control

The argument stops, rather than silently weakening its conclusion, in each of the following situations:

- a degeneracy map is injective over the fraction field but not modulo $\varpi$;
- its old image is not saturated and component-group torsion is unmeasured;
- a type projector exists only after dividing by an $\ell$-divisible group order;
- old/new pairings are perfect only up to a nonunit lattice index;
- the deep auxiliary module has the correct rank but is not free over the diamond group algebra;
- the Hecke-valued family satisfies local compatibility only at classical generic points;
- Jacquet--Langlands identifies generic packets but not saturated Hecke orders;
- the patched module has support on only some unnamed components; or
- solvable descent is asserted from invariance without its twisting fiber.

Each failure has a corresponding repair theorem named earlier. None is repaired by increasing the number of Taylor--Wiles primes.

### 20.4 A diagnostic decision tree

For a proposed added place $v$, the order of questions is:

    Is the local condition represented?
        |
        +-- no --> retain a frame or enhancement, or stop
        |
        v
    Is the target component named and its conductor constant generically?
        |
        +-- no --> compute the local ring before global patching
        |
        v
    Does an integral automorphic lattice meet that component?
        |
        +-- no --> prove level/type raising or component switching
        |
        v
    Are degeneracy/type maps exact, saturated, and paired?
        |
        +-- no --> no congruence or determinant conclusion
        |
        v
    Does the Hecke-valued representation factor through the same quotient?
        |
        +-- no --> no canonical map from the desired deformation ring
        |
        v
    Do local and automorphic determinant factors agree?
        |
        +-- no --> numerical route stops; test a direct route separately
        |
        v
    Does patched support contain the target component?
        |
        +-- no --> only a theorem on the components actually supported
        |
        v
    full, reduced, or componentwise R=T according to coverage
                 and independent nilpotent control

The sharp balanced route branches after construction of the canonical map:
if the absolute auxiliary tangent space has exactly $q_P$ generators and the
marked free diamond action is available, Theorem 12.1A proves faithfulness
without passing through either determinant or support questions.

At a proposed base change, prepend three questions: does the residual image remain adequate, does the packet remain cuspidal without new self-twists, and is the descent fiber compatible with the target determinant? A negative answer changes the theorem, not merely its proof.

## 21. Interfaces with the later arithmetic chain

The output of this book is an automorphic representation whose Galois representation is the specified lift and whose local parameters have been checked integrally. Later arguments may use that output, but they must not silently enlarge it into potential modularity, a compatible system, or a small-ramification classification.

### 21.1 Potential modularity

Book 170 can use Theorem 13.1 only through the following interface. A potential-modularity construction supplies a totally real extension $E/F$ and an auxiliary geometric object whose residual representation is known to be automorphic. To invoke Theorem 13.1 over $E$, the construction must also ensure:

1. $E$ is disjoint from the residual cutout field, or the image and adequacy of $\bar\rho|_{G_E}$ are recomputed;
2. the places above $\ell$ are unramified, or preferably split, so that the exact finite-flat local theorem remains available;
3. every prescribed local point of the moduli construction lands on a named deformation component;
4. the auxiliary residual automorphic representation is cuspidal and lies in the correct non-Eisenstein block;
5. the Hilbert or quaternionic forms of NM-I and NM-II and the
   route-specific sharp-balance or NM-III clauses hold at the levels
   introduced over $E$, together with any base equality required by the
   relative route; and
6. determinant characters of the geometric object and the target have been
   identified, including finite-order twists and the square-root and integral
   twisting condition of Section 4.1 at every place above $\ell$.

Under these clauses, Theorem 13.1 proves automorphy of $\rho|_{G_E}$. That is the exact output required by potential modularity. It does not descend automorphy to $F$ unless Theorem 16.1 or the later compatible-system descent machinery is applied.

The component-switching criterion (16.7) is especially useful here. A moduli construction may arrange that an auxiliary automorphic point and the target become component-compatible after restriction. The local moduli theorem must prove that compatibility; the mere existence of both points over $E$ is not enough.

### 21.2 Compatible systems and changing prime

Books 175--177 consume the automorphic output by constructing a compatible system, descending it when necessary, and changing the coefficient prime. Once $\rho\simeq\rho_\pi$ has been proved, the automorphic representation $\pi$ supplies common Frobenius polynomials

$$
P_v(X)=X^2-a_vX+\psi(v)q_v
\tag{21.1}
$$

at almost every place, where $\lambda_\pi$ is the Hecke character of $\pi$,
$a_v=\lambda_\pi(S_v^{-1}T_v)$ in the normalization (1.7), and
$\psi(v)=\psi(\operatorname{Frob}_v)$. The compatible-system construction
can then realize these polynomials in coefficient fields at other primes.
Theorem 13.1 contributes three pieces of data that must be retained:

- the exact determinant $\psi\chi_\ell$;
- the conductor and Weil--Deligne type at every fixed nonminimal place; and
- the global identification with the target, which removes component and twist ambiguity.

Changing the coefficient prime does not preserve every integral condition by inspection. Strong local compatibility can transport a Weil--Deligne parameter at a place away from both coefficient primes. It does not by itself prove finite flatness at the new coefficient prime, choose an integral lattice, or preserve residual adequacy. At a new prime $\lambda$, one must separately check:

$$
\bar\rho_\lambda\text{ is absolutely irreducible or satisfies Input O},
\tag{21.2}
$$

$$
\rho_\lambda|_{G_{F_v}}\text{ satisfies the exact coefficient-prime condition for }v\mid\lambda,
\tag{21.3}
$$

and

$$
\text{all newly residual conductor drops define controlled local components.}
\tag{21.4}
$$

The nonminimal set can change with $\lambda$ because reduction modulo $\lambda$ can kill different monodromy parameters or tame characters. Its Selmer group, Taylor--Wiles sets, and congruence costs must therefore be recomputed.

If automorphy is initially known only over solvable subextensions, compatible-system descent uses Brauer induction and automorphic induction in the later books. That mechanism is distinct from the direct cyclic descent of Chapter 16, although both must control determinant characters and twisting fibers.

### 21.3 Hardly ramified $3$-adic representations

Book 180 starts from an integral $3$-adic representation with a sharply bounded ramification set, finite-flat torsion at $3$, and a fixed determinant. Definition 18.1 provides an exact local ledger from which those bounds can be read:

$$
\text{unramified places},\quad
\text{conductor-one special places},\quad
\text{finite flat at }3.
\tag{21.5}
$$

The discriminant argument must use the actual set in (18.3), not the adjective alone. If its small-ramification theorem assumes unramifiedness away from $3$, then it applies only when

$$
S_{\mathrm{ft}}=S_{\mathrm{st}}=P_{\mathrm{hr}}=\varnothing.
\tag{21.6}
$$

If it permits one auxiliary tame or conductor-one place, that local contribution must be inserted into its discriminant bound.

Book 156 supplies automorphy of a $3$-adic representation only under the special small-prime package of Section 18.3 or Deep Ordinary Input O. More commonly, automorphy is first proved at a larger coefficient prime and transported through a compatible system. The $3$-adic classification then studies the resulting member and can constrain its residual image. This order avoids using a nonexistent clean level-raising prime at $3$.

The finite-flat hypothesis passed to the discriminant calculation is integral at every torsion level. A statement that the $3$-adic representation is crystalline or has weights $0,1$ is not a replacement unless an integral comparison theorem supplies the finite-flat models.

### 21.4 The FLT interface

Book 154 must deliver the following input record for its Frey curve before invoking this book.

1. The determinant of the chosen Tate module is cyclotomic, with every twist explicitly removed.
2. The representation is finite flat at the lifting prime in the exact local range being used, or a separately proved ordinary theorem applies.
3. Every multiplicative prime is placed in $S_{\mathrm{st}}$ or $P_{\mathrm{hr}}$ by reducing its Tate parameter, and its sign and residue-cardinality congruence are recorded.
4. Every additive or wild prime is either eliminated by the Frey calculation or supplied with a controlled local theorem.
5. The residual representation is irreducible by the rational-isogeny branch and is residually automorphic by an independent theorem.
6. The residual automorphic level is lowered using actual Ihara and saturation results, not conductor numerology.
7. Adequacy or the exact small-image replacement is verified at the coefficient prime where lifting is performed.
8. If potential modularity or changing prime intervenes, every base-change, compatible-system, and descent condition in Chapters 16 and 21 is checked.

Given that record and the applicable integral infrastructure, Theorem 18.2 or Theorem 13.1 returns a weight-two automorphic representation with the Frey representation's exact local parameters. Later books may combine that conclusion with compatible systems, the hardly ramified $3$-adic classification, and the arithmetic of the Frey curve. This book proves none of the rational-isogeny classification, discriminant contradiction, or final Diophantine reduction.

### 21.5 Final perspective

Nonminimal modularity lifting is governed by a conservation law. Every new ramified prime contributes simultaneously to:

$$
\begin{array}{c}
\text{a represented local component and its tangent complex},\\
\text{a conductor and automorphic type},\\
\text{an integral degeneracy or type lattice},\\
\text{a local determinant factor},\\
\text{the global Selmer and relation ledger},\\
\text{and the support of the patched module.}
\end{array}
\tag{21.7}
$$

These six entries form the complete audit ledger, but the kernel-killing
routes use different columns. In the sharp balanced case, direct patching
uses the exact local and global tangent count and the free faithful-action
system to kill the kernel by Book 155's equal-variable mechanism, without a
determinant or coverage hypothesis. The support route additionally uses the
component column and concludes at the strength allowed by nilpotent control.
The relative route instead starts from Book 155's proved minimal ring and
Fitting--congruence equalities and transports only the new local determinant
costs. Solvable base change can move the comparison to a more favorable
field, but only component control and recursive character-corrected descent
bring the original representation back.

The durable lesson is not that added ramification is harmless. It is that its
cost is local, integral, and measurable. Once the local component and
automorphic lattice are matched, that cost can be paid by one genuinely
verified bridge: sharp absolute faithfulness, component support with
nilpotent control, or relative determinant comparison from an already proved
base equality. Each bridge preserves the specified lift, and none may be
silently substituted for another.
