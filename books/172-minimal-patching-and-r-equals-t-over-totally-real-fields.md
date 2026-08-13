# Minimal Patching and $R=T$ over Totally Real Fields

## Contents

- [1. The last step in the minimal comparison](#1-the-last-step-in-the-minimal-comparison)
  - [1.1 What remains after constructing the comparison map](#11-what-remains-after-constructing-the-comparison-map)
  - [1.2 The shape of the proof](#12-the-shape-of-the-proof)
  - [1.3 The main theorem](#13-the-main-theorem)
- [2. The arithmetic datum and its hypotheses](#2-the-arithmetic-datum-and-its-hypotheses)
  - [2.1 Coefficients, determinant, and residual representation](#21-coefficients-determinant-and-residual-representation)
  - [2.2 The minimal local problem](#22-the-minimal-local-problem)
  - [2.3 The automorphic realization](#23-the-automorphic-realization)
  - [2.4 Why the prime bound is seven](#24-why-the-prime-bound-is-seven)
- [3. The balanced number and auxiliary primes](#3-the-balanced-number-and-auxiliary-primes)
  - [3.1 The global Euler-characteristic cancellation](#31-the-global-euler-characteristic-cancellation)
  - [3.2 Detecting dual classes](#32-detecting-dual-classes)
  - [3.3 Taylor--Wiles sets at every depth](#33-taylor--wiles-sets-at-every-depth)
  - [3.4 The exact cohomological ledger](#34-the-exact-cohomological-ledger)
- [4. Auxiliary local conditions and diamond groups](#4-auxiliary-local-conditions-and-diamond-groups)
  - [4.1 The ordered regular branch](#41-the-ordered-regular-branch)
  - [4.2 Finite and limiting diamond algebras](#42-finite-and-limiting-diamond-algebras)
  - [4.3 Augmentation on the deformation side](#43-augmentation-on-the-deformation-side)
  - [4.4 Conventions and a local calculation](#44-conventions-and-a-local-calculation)
- [5. Definite-quaternion modules at auxiliary level](#5-definite-quaternion-modules-at-auxiliary-level)
  - [5.1 Deep level and the effective diamond action](#51-deep-level-and-the-effective-diamond-action)
  - [5.2 Group-ring freeness](#52-group-ring-freeness)
  - [5.3 From oriented level back to minimal level](#53-from-oriented-level-back-to-minimal-level)
  - [5.4 Pairings, adjoints, and uniform rank](#54-pairings-adjoints-and-uniform-rank)
- [6. The finite Taylor--Wiles system](#6-the-finite-taylor--wiles-system)
  - [6.1 Rings, Hecke algebras, and modules](#61-rings-hecke-algebras-and-modules)
  - [6.2 The commuting action diagram](#62-the-commuting-action-diagram)
  - [6.3 Exact augmentation](#63-exact-augmentation)
  - [6.4 Nonnested levels and finite shadows](#64-nonnested-levels-and-finite-shadows)
- [7. The minimal presentation theorem](#7-the-minimal-presentation-theorem)
  - [7.1 Why absolute and relative counts must be separated](#71-why-absolute-and-relative-counts-must-be-separated)
  - [7.2 The sharp absolute source](#72-the-sharp-absolute-source)
  - [7.3 Diamond lifts and finite-order equations](#73-diamond-lifts-and-finite-order-equations)
  - [7.4 Framed and unframed ledgers](#74-framed-and-unframed-ledgers)
- [8. Patching the rings and modules](#8-patching-the-rings-and-modules)
  - [8.1 Artinian precision](#81-artinian-precision)
  - [8.2 Coherent diagonalization](#82-coherent-diagonalization)
  - [8.3 The patched objects](#83-the-patched-objects)
  - [8.4 Exact recovery at augmentation](#84-exact-recovery-at-augmentation)
- [9. The dimension and depth ledger](#9-the-dimension-and-depth-ledger)
  - [9.1 Dimensions of the two source rings](#91-dimensions-of-the-two-source-rings)
  - [9.2 Depth over three acting rings](#92-depth-over-three-acting-rings)
  - [9.3 Why equality of dimensions is exact here](#93-why-equality-of-dimensions-is-exact-here)
  - [9.4 The zero auxiliary-prime case](#94-the-zero-auxiliary-prime-case)
- [10. Regularity, freeness, and support](#10-regularity-freeness-and-support)
  - [10.1 Regularity of the patched deformation ring](#101-regularity-of-the-patched-deformation-ring)
  - [10.2 Freeness over the patched deformation ring](#102-freeness-over-the-patched-deformation-ring)
  - [10.3 Full component coverage](#103-full-component-coverage)
  - [10.4 Faithfulness and kernel killing](#104-faithfulness-and-kernel-killing)
- [11. Descent to minimal level](#11-descent-to-minimal-level)
  - [11.1 The augmentation sequence is regular](#111-the-augmentation-sequence-is-regular)
  - [11.2 Ring, module, and Hecke descent](#112-ring-module-and-hecke-descent)
  - [11.3 Proof of the minimal comparison theorem](#113-proof-of-the-minimal-comparison-theorem)
  - [11.4 Canonicity](#114-canonicity)
- [12. Complete intersections and Gorenstein duality](#12-complete-intersections-and-gorenstein-duality)
  - [12.1 The minimal ring as a regular quotient](#121-the-minimal-ring-as-a-regular-quotient)
  - [12.2 Freeness of the minimal automorphic module](#122-freeness-of-the-minimal-automorphic-module)
  - [12.3 Gorenstein conclusions](#123-gorenstein-conclusions)
  - [12.4 What is and is not rank one](#124-what-is-and-is-not-rank-one)
- [13. Determinants and congruence modules](#13-determinants-and-congruence-modules)
  - [13.1 Two determinant constructions](#131-two-determinant-constructions)
  - [13.2 Compatibility through finite shadows](#132-compatibility-through-finite-shadows)
  - [13.3 The cotangent--congruence equality](#133-the-cotangent--congruence-equality)
  - [13.4 Why the argument is not circular](#134-why-the-argument-is-not-circular)
- [14. Changes of coefficients and normalization](#14-changes-of-coefficients-and-normalization)
  - [14.1 Finite coefficient extension](#141-finite-coefficient-extension)
  - [14.2 Eigenvalues and idempotents](#142-eigenvalues-and-idempotents)
  - [14.3 Frobenius, determinants, and diamonds](#143-frobenius-determinants-and-diamonds)
  - [14.4 Returning from enlarged coefficients](#144-returning-from-enlarged-coefficients)
- [15. Boundaries and exceptional cases](#15-boundaries-and-exceptional-cases)
  - [15.1 Coefficient prime five](#151-coefficient-prime-five)
  - [15.2 Scalar Frobenius and failed level control](#152-scalar-frobenius-and-failed-level-control)
  - [15.3 Nonclean local components](#153-nonclean-local-components)
  - [15.4 Nonminimal problems](#154-nonminimal-problems)
- [16. Dependency closure](#16-dependency-closure)
  - [16.1 The five direct inputs](#161-the-five-direct-inputs)
  - [16.2 The two structural inputs used through them](#162-the-two-structural-inputs-used-through-them)
  - [16.3 Hypothesis matching](#163-hypothesis-matching)
- [17. A hostile audit of the proof](#17-a-hostile-audit-of-the-proof)
  - [17.1 Prime selection and local branches](#171-prime-selection-and-local-branches)
  - [17.2 Patching and numerical counts](#172-patching-and-numerical-counts)
  - [17.3 Support and nilpotents](#173-support-and-nilpotents)
  - [17.4 Descent and structural conclusions](#174-descent-and-structural-conclusions)
- [18. Conclusion](#18-conclusion)
  - [18.1 The established package](#181-the-established-package)

## 1. The last step in the minimal comparison

### 1.1 What remains after constructing the comparison map

Let $F$ be totally real and let $\ell$ be an odd coefficient prime. The preceding minimal deformation--Hecke comparison supplies two finite arithmetic objects. One is the universal fixed-determinant minimal deformation ring $R^{\min}$. The other is the faithful Hecke algebra $\mathbb T^{\min}$ acting on a localized definite-quaternion module $M^{\min}$. A Hecke-valued Galois representation gives a canonical surjection

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min}.
\tag{1.1}
$$

Surjectivity is already a strong compatibility statement, but it is not the desired theorem. Its kernel could contain an entire component, an embedded component, or a nilpotent thickening. Equal tangent dimensions would not eliminate any of these possibilities. Nor would the fact that both rings have the same Krull dimension: a proper quotient can be equidimensional with its source.

The missing idea is to enlarge the arithmetic problem at carefully selected finite places. At those places the deformation gains controlled tame characters, while the automorphic module gains a free action of the same finite diamond group. The auxiliary primes are changed as their depth grows, so the resulting objects do not form a literal tower. Patching replaces this changing family by one coherent limiting ring and module. At infinite level the finite-order equations disappear, leaving enough regular variables to expose the structure of the deformation ring.

The minimal situation is especially rigid. The initial Selmer and dual Selmer groups have the same dimension. Exactly that many auxiliary primes kill the dual group, so every auxiliary deformation ring is generated by $q$ absolute parameters while the diamond source also has $q$ parameters. A patched module free over the diamond power-series algebra gives a faithful scalar action of a dimension-$q+1$ ring inside the action image of the dimension-$q+1$ deformation source. This equal-variable rigidity forces the source to act injectively. The patched deformation ring is therefore regular, the module is free over it, and the action kernel vanishes scheme-theoretically.

### 1.2 The shape of the proof

Write

$$
q=\dim_k H^1_{\mathcal L^\perp}(F,\operatorname{ad}^0\bar\rho(1)).
\tag{1.2}
$$

For every $N\geq1$ we choose a set $Q_N$ of $q$ Taylor--Wiles primes. The residue cardinality at each selected place is $1$ modulo $\ell^N$, residual Frobenius has two distinct eigenvalues, and localization at the chosen eigenlines kills the dual Selmer group. Put

$$
\Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q,
\qquad
\Lambda_N=\mathcal O[\Delta_N].
\tag{1.3}
$$

At auxiliary level there are rings, acting algebras, and modules

$$
\Lambda_N\longrightarrow R_N\twoheadrightarrow\mathbb T_N
\hookrightarrow\operatorname{End}_{\Lambda_N}(M_N).
\tag{1.4}
$$

The module $M_N$ is finite free of a rank independent of $N$ over $\Lambda_N$. Augmentation recovers exactly the minimal objects:

$$
R_N/\mathfrak a_NR_N\simeq R^{\min},
\qquad
M_N/\mathfrak a_NM_N\simeq M^{\min},
\tag{1.5}
$$

and the acting image specializes to $\mathbb T^{\min}$. After passing through coherent finite shadows, patching gives

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad
R_\infty,
\qquad
M_\infty,
\tag{1.6}
$$

with $M_\infty$ finite free over $S_\infty$. The sharp absolute presentation gives

$$
P=\mathcal O[[x_1,\ldots,x_q]]\twoheadrightarrow R_\infty.
\tag{1.6a}
$$

Equal-variable rigidity then proves

$$
R_\infty\simeq\mathcal O[[x_1,\ldots,x_q]].
\tag{1.7}
$$

Both power-series rings have dimension $q+1$, although the structural map between them need not identify the displayed coordinates. Depth then yields

$$
M_\infty\simeq R_\infty^{\oplus r}
\tag{1.8}
$$

for some $r>0$. Thus $R_\infty$ acts faithfully. Exact augmentation descends this equality of action rings to (1.1), proving that (1.1) is an isomorphism.

### 1.3 The main theorem

We state the endpoint before carrying out the construction. Every phrase in the hypothesis is unpacked in Chapter 2.

**Theorem 1.1 (minimal $R=T$ over a totally real field).** Let $F$ be totally real, let $\ell\geq7$, and let $(\mathcal O,\varpi,k)$ be the integers, uniformizer, and residue field of a finite extension of $\mathbf Q_\ell$. Let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
$$

be continuous, absolutely irreducible, totally odd, and absolutely irreducible after restriction to $G_{F(\zeta_\ell)}$. Fix a determinant lift $\delta$. Assume the clean finite-flat, unramified, fixed tame-type, and minimal-special local hypotheses, together with the exact definite-quaternion realization, integral saturation, stabilizer, pairing, generic reducedness, and local--global compatibility hypotheses stated in Sections 2.2--2.3.

Then the canonical surjection is an isomorphism:

$$
\boxed{R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.}
\tag{1.9}
$$

Moreover:

1. $R^{\min}=\mathbb T^{\min}$ is finite free over $\mathcal O$;
2. it is a relative complete intersection over $\mathcal O$, hence Gorenstein;
3. $M^{\min}$ is finite free of positive rank over $R^{\min}$;
4. the primary--companion pairing remains perfect after descent and has the prescribed Hecke adjoints;
5. for every generically isolated integral branch satisfying the retained saturation and primitive multiplicity hypotheses, the cotangent and congruence Fitting ideals agree.

No conclusion is asserted here for $\ell=5$, for a residual cyclotomic restriction that is reducible, for a scalar auxiliary Frobenius, or for a local condition outside the clean represented components.

## 2. The arithmetic datum and its hypotheses

### 2.1 Coefficients, determinant, and residual representation

Fix a finite extension $E/\mathbf Q_\ell$ with ring of integers $\mathcal O$, uniformizer $\varpi$, and finite residue field $k$. We enlarge $E$ at the outset if necessary so that the residual Frobenius eigenvalues and the finite-order type characters already present in the minimal datum are defined over it. The auxiliary characters of orders $\ell^N$ are universal group-like elements of $\mathcal O[\Delta_N]$; no fixed finite coefficient field is required to contain roots of unity of every $\ell$-power order. A later coefficient extension is treated separately in Chapter 14.

Let $F$ be totally real. We fix a continuous representation

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

that is absolutely irreducible and totally odd. Total oddness means that for every real place $v$ and any complex conjugation $c_v$,

$$
\det\bar\rho(c_v)=-1.
\tag{2.2}
$$

We also require $\bar\rho|_{G_{F(\zeta_\ell)}}$ to be absolutely irreducible. Fix a continuous lift

$$
\delta:G_F\longrightarrow\mathcal O^\times
\tag{2.3}
$$

of $\det\bar\rho$. Every deformation in this book has determinant $\delta$. Put

$$
M=\operatorname{ad}^0\bar\rho.
\tag{2.4}
$$

Since $\ell$ is odd, trace zero splits off from scalar endomorphisms. The trace pairing identifies $M^*(1)$ with $M(1)$. Absolute irreducibility gives

$$
H^0(F,M)=0.
\tag{2.5}
$$

Absolute irreducibility on the cyclotomic restriction, rather than adequacy alone, rules out the cyclotomic self-twist that would contribute $H^0(F,M(1))$. Indeed, an invariant trace-zero map $\bar\rho\to\bar\rho(1)$ restricts over $F(\zeta_\ell)$ to an endomorphism of an absolutely irreducible representation. It is scalar there, and a trace-zero scalar is zero because $\ell$ is odd. Thus

$$
H^0(F,M(1))=0.
\tag{2.6}
$$

These two vanishings are endpoint hypotheses in the global duality formula. They are not cosmetic consequences of choosing a determinant.

### 2.2 The minimal local problem

Let $S$ contain the real places, the places above $\ell$, and every finite place where $\bar\rho$, $\delta$, or the automorphic level is ramified. At each $v\in S$ we impose a represented fixed-determinant local condition with tangent subspace

$$
L_v\subseteq H^1(F_v,M).
\tag{2.7}
$$

The hypotheses are as follows.

At $v\mid\ell$, the extension $F_v/\mathbf Q_\ell$ is unramified, and the residual representation belongs to the low-weight finite-flat range with weights $\{0,1\}$. The framed fixed-determinant condition is formally smooth over $\mathcal O$ of relative dimension

$$
[F_v:\mathbf Q_\ell]+3.
\tag{2.8}
$$

Its unframed tangent contribution is

$$
\dim_k L_v-h^0(F_v,M)=[F_v:\mathbf Q_\ell].
\tag{2.9}
$$

At a finite place away from $\ell$, the condition is one of three clean kinds: unramified; a fixed prime-to-$\ell$ inertia representation with every ordering and finite-type label retained; or the schematic closure of a named minimal-special component, including its invariant line, sign, and monodromy relation. In every case the represented condition is formally smooth in the chosen framed convention and is neutral:

$$
\dim_k L_v-h^0(F_v,M)=0.
\tag{2.10}
$$

At a real place the odd conjugacy class has tangent space zero, while $h^0(F_v,M)=1$. Hence the real contribution is $-1$.

The word clean includes more than a dimension calculation. Each local condition is stable under quotients of Artinian coefficient rings, compatible with the fixed determinant, and has the effective obstruction theory needed for global presentations. At special places it is a closed component condition; the open requirement that monodromy be nonzero would not define a deformation problem on all quotients.

### 2.3 The automorphic realization

Choose a totally definite quaternion algebra over $F$, a parallel-weight-two coefficient lattice, and a compact open level whose local factors match exactly the conditions of Section 2.2. The residual system occurs in the resulting finite automorphic module and defines a non-Eisenstein maximal ideal. The hypotheses retained throughout are:

- the localized minimal module $M^{\min}$ is finite free over $\mathcal O$;
- its faithful image is a complete local finite-flat algebra $\mathbb T^{\min}$;
- primary and companion modules carry a perfect integral pairing with inverse-double-coset adjoints;
- every characteristic-zero branch of the minimal module and of every auxiliary module constructed below lies in the established rank-two Galois attachment range;
- the minimal and auxiliary generic Hecke algebras are reduced, and their named acting algebras contain no operators beyond the trace-generated order, the fixed determinant scalars, and the ordered auxiliary operators proved in Section 6.1 to belong to that order;
- integral local--global compatibility puts the minimal and auxiliary Hecke-valued representations in exactly the local conditions of Section 2.2 and the ordered conditions of Section 4.1, on every Artinian quotient;
- type lattices, degeneracy maps, and primary idempotents are saturated;
- at every admissible auxiliary set, the projective diagonal-ratio diamond group has full nominal rank, every remaining arithmetic point stabilizer has trivial image in it, and the resulting deep-to-oriented fibers are genuine torsors;
- the localized oriented new complement has no support at the chosen regular refinement, and the acting-image augmentation is saturated, so that it recovers exactly $\mathbb T^{\min}$ rather than only a quotient or a finite-index order.

The first minimal-level instances of these assumptions are already needed to construct (1.1). Their auxiliary-level instances are separate input to the Taylor--Wiles system: residual occurrence at minimal level supplies a nonzero old summand, but does not by itself construct a representation over every auxiliary Hecke order or prove exact augmentation of its acting image. The auxiliary modules must use the same determinant, central character, local branches, and integral lattices. Patching cannot repair a mismatch at finite level.

Residual automorphy is assumed over $F$ in this exact definite-quaternion realization. If it is known only after a solvable extension, a separate automorphic descent theorem and an integral comparison of the descended Hecke order are required before this book applies. No such existence or descent statement is hidden in the patching argument.

The Hecke polynomial at a good finite place $v$ is written using geometric Frobenius:

$$
X^2-T_vX+q_vS_v.
\tag{2.11}
$$

The central operator $S_v$ is a unit and is not silently normalized to one. This convention will be essential in the old--new determinant calculation.

### 2.4 Why the prime bound is seven

The auxiliary-prime theorem needs more than absolute irreducibility. It requires semisimple elements that detect every nonzero adjoint cohomology direction, the vanishing of a finite-image first cohomology group, and the absence of nontrivial $\ell$-power quotients in the cyclotomic restricted image. For a two-dimensional absolutely irreducible representation these adequacy properties hold uniformly when $\ell\geq7$.

Prime selection uses the slightly more explicit split Taylor--Wiles package on the underlying $\mathbf F_\ell$-module: every stable additive subspace arising from a cocycle has no trivial quotient, and some split regular semisimple element detects it. The finite-image classification supplies this stronger formulation as well. In the prime-to-$\ell$ cases it follows from semisimplicity and the absence of adjoint invariants; in the defining-characteristic cases it follows from the special-linear core and the irreducibility of its trace-zero adjoint module. One common finite coefficient extension splits all required detecting elements.

Characteristic five has an exceptional natural representation with projective image $A_5\simeq\operatorname{PSL}_2(\mathbf F_5)$. Its adjoint first cohomology need not vanish. Consequently absolute irreducibility at five does not imply the prime-selection package used below. The main theorem therefore has a genuine arithmetic boundary at seven, not a bound inserted for convenience.

## 3. The balanced number and auxiliary primes

### 3.1 The global Euler-characteristic cancellation

Let $\mathcal L=(L_v)$ be the minimal Selmer structure. Its primal and dual Selmer groups are

$$
H^1_{\mathcal L}(F,M)
=\ker\left(H^1(G_{F,S},M)\to
\bigoplus_{v\in S}H^1(F_v,M)/L_v\right)
\tag{3.1}
$$

and

$$
H^1_{\mathcal L^\perp}(F,M(1)),
\tag{3.2}
$$

where the local orthogonal complements are taken under local Tate duality. Global duality gives

$$
\begin{aligned}
h^1_{\mathcal L}(F,M)-h^1_{\mathcal L^\perp}(F,M(1))
={}&h^0(F,M)-h^0(F,M(1))\\
&+\sum_{v\in S}
\bigl(\dim_kL_v-h^0(F_v,M)\bigr).
\end{aligned}
\tag{3.3}
$$

The global invariant terms vanish by (2.5)--(2.6). Finite places away from $\ell$ contribute zero. The coefficient-prime places contribute

$$
\sum_{v\mid\ell}[F_v:\mathbf Q_\ell]=[F:\mathbf Q],
\tag{3.4}
$$

while the $[F:\mathbf Q]$ real places contribute its negative. Therefore

$$
h^1_{\mathcal L}(F,M)
=h^1_{\mathcal L^\perp}(F,M(1)).
\tag{3.5}
$$

We denote the common dimension by $q$. Balance means equality, not vanishing. A minimal problem with $q=4$ has four genuine tangent directions and four dual obstructions; the purpose of auxiliary primes is to exchange the latter for controlled tame directions.

### 3.2 Detecting dual classes

Take a nonzero class

$$
\phi\in H^1_{\mathcal L^\perp}(F,M(1)).
\tag{3.6}
$$

The class cuts out a finite elementary abelian extension over a field containing the residual and cyclotomic fixed fields. Adequacy ensures that this extension does not collapse into the cyclotomic tower and that some split regular semisimple element detects a nonzero diagonal projection of $\phi$. The finite compositum containing the residual representation, the relevant cyclotomic layer, and the cocycle extension carries all required conditions at once.

A Frobenius-selection theorem then supplies infinitely many finite places $x\notin S$ such that:

$$
q_x\equiv1\pmod{\ell^N},
\tag{3.7}
$$

$\bar\rho$ is unramified at $x$, the matrix $\bar\rho(\Phi_x)$ has two distinct eigenvalues in $k$, and localization of $\phi$ in the chosen one-dimensional quotient is nonzero. Any prescribed finite set of forbidden places can be avoided.

The congruence and detection requirements cannot be chosen independently and intersected afterward. They are realized by one element in one finite Galois quotient. This is why the disjointness and fiber-product compatibility in the auxiliary-prime theorem are indispensable.

### 3.3 Taylor--Wiles sets at every depth

Choose a nonzero dual class and a detecting place $x_1$. The localization target is one-dimensional, so nonzero localization is surjective. Replacing the local dual condition at $x_1$ by zero cuts the dual Selmer dimension by one. Repeat inside the kernel, avoiding all previously chosen places. After exactly $q$ steps the dual group vanishes.

Thus for every $N\geq1$ there is a set

$$
Q_N=\{x_{N,1},\ldots,x_{N,q}\}
\tag{3.8}
$$

of pairwise distinct places, disjoint from $S$, satisfying (3.7), with ordered residual eigenvalues

$$
(\alpha_x,\beta_x),\qquad \alpha_x\ne\beta_x,
\tag{3.9}
$$

such that

$$
H^1_{\mathcal L_{Q_N}^\perp}(F,M(1))=0.
\tag{3.10}
$$

The sets for different $N$ may also be chosen disjoint. They cannot be nested indefinitely: a fixed finite place has finite $\ell$-adic valuation of $q_x-1$. This observation will force us to patch finite shadows rather than take an inverse limit of the arithmetic levels themselves.

### 3.4 The exact cohomological ledger

At each auxiliary place the enlarged primal tangent condition is one dimension larger than the unramified condition, while its dual orthogonal is zero. Hence adding $q$ places raises the global defect by $q$. Since the new dual Selmer group vanishes,

$$
h^1_{\mathcal L_{Q_N}}(F,M)=q.
\tag{3.11}
$$

The complete ledger is

| quantity | minimal problem | auxiliary problem |
|---|---:|---:|
| primal Selmer dimension | $q$ | $q$ |
| dual Selmer dimension | $q$ | $0$ |
| local tame directions | $0$ | $q$ |
| primal minus dual | $0$ | $q$ |

The unchanged primal dimension is not paradoxical. Enlarging local conditions creates $q$ possible local directions, but removing $q$ reciprocity constraints changes which collections of local classes globalize. The Poitou--Tate comparison sequence records both effects and gives (3.11).

To see the cancellation without relying only on dimensions, write $L_x^{\mathrm{ur}}\subset L_x^{\mathrm{TW}}$ for the two local tangent conditions. Comparison of the two Selmer structures gives the exact segment

$$
\begin{aligned}
0\longrightarrow H^1_{\mathcal L}(F,M)
&\longrightarrow H^1_{\mathcal L_{Q_N}}(F,M)
\longrightarrow
\bigoplus_{x\in Q_N}L_x^{\mathrm{TW}}/L_x^{\mathrm{ur}}\\
&\longrightarrow
H^1_{\mathcal L^\perp}(F,M(1))^\vee
\longrightarrow
H^1_{\mathcal L_{Q_N}^\perp}(F,M(1))^\vee
\longrightarrow0.
\end{aligned}
\tag{3.12}
$$

The direct sum in the middle has dimension $q$. The map from it to the dual of the minimal dual Selmer group is the transpose of the localization matrix used to select $Q_N$. That matrix is invertible by construction, and the last term is zero. Hence the middle arrow in (3.12) is an isomorphism. Exactness now shows that the first arrow is also an isomorphism:

$$
H^1_{\mathcal L}(F,M)
\xrightarrow{\sim}
H^1_{\mathcal L_{Q_N}}(F,M).
\tag{3.13}
$$

This proves (3.11) and explains a fact used later: a basis of the minimal tangent space can serve as a basis for every auxiliary tangent space after choices. It does not identify the corresponding universal rings, because their higher-order local character equations differ.

The number $q$ is absolute and unframed. It is not the dimension of a relaxed dual group used in a presentation relative to a product of framed local rings. Those relative numbers can vary with $N$ even though (3.10) holds. Chapter 7 keeps these ledgers separate.

## 4. Auxiliary local conditions and diamond groups

### 4.1 The ordered regular branch

Fix $x\in Q_N$. Choose the $\alpha_x$-eigenline of residual Frobenius. The auxiliary local functor remembers a rank-one direct summand lifting that line. Tame inertia acts on it through a character $\chi_x$, and the determinant determines the character on the complementary line. In a compatible basis the inertial restriction has the form

$$
\rho|_{I_x}\sim
\begin{pmatrix}
\chi_x&0\\0&\delta|_{I_x}\chi_x^{-1}
\end{pmatrix}.
\tag{4.1}
$$

The chosen line removes the Weyl ambiguity. Because $\alpha_x\ne\beta_x$, an unramified lift has a unique direct-sum decomposition lifting the residual eigenspaces. This uniqueness is the local reason that augmentation will recover the unenhanced minimal problem exactly.

Let $\Delta_x$ be the quotient of the maximal $\ell$-power quotient of the residue multiplicative group having order $\ell^N$. Local reciprocity makes $\chi_x$ the universal character of $\Delta_x$. The local unframed rings have the clean form

$$
R_x^{\mathrm{ur},\delta,\alpha_x}\simeq\mathcal O[[X_x]],
\qquad
R_x^{\mathrm{TW},\delta,\alpha_x}
\simeq\mathcal O[\Delta_x][[X_x]].
\tag{4.2}
$$

On the automorphic side, this cyclic group is realized by the projective diagonal ratio on the oriented subgroup, not by the lower-right residue entry alone. A scalar matrix has ratio one, so the fixed central character contributes no common-scalar kernel. The right-action and reciprocity conventions can identify the deck generator with either $\chi_x$ or $\chi_x^{-1}$; we choose the generator once so that the structural map in (4.7) agrees exactly with the automorphic diamond action. The full-effective-rank hypothesis of Section 2.3 says that no further global stabilizer quotient reduces the order $\ell^N$.

The framed versions add two eigenline-position variables. The group algebra is not smooth over $\mathcal O$; it contains the finite-order equation. The local ring is instead formally smooth over that group algebra.

### 4.2 Finite and limiting diamond algebras

Set

$$
\Delta_N=\prod_{x\in Q_N}\Delta_x
\simeq(\mathbf Z/\ell^N\mathbf Z)^q,
\qquad
\Lambda_N=\mathcal O[\Delta_N].
\tag{4.3}
$$

After choosing generators, there is a standard presentation

$$
\Lambda_N\simeq
\mathcal O[[z_1,\ldots,z_q]]/
\bigl((1+z_i)^{\ell^N}-1:1\leq i\leq q\bigr).
\tag{4.4}
$$

Thus every finite level is a quotient of

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad \dim S_\infty=q+1.
\tag{4.5}
$$

Let $\mathfrak a_N$ and $\mathfrak a_\infty$ be the respective augmentation ideals. Then

$$
S_\infty/\mathfrak a_\infty\simeq\mathcal O.
\tag{4.6}
$$

For every fixed power of the maximal ideal of $S_\infty$, the elements $(1+z_i)^{\ell^N}-1$ tend to zero as $N$ tends to infinity. Their linear coefficients $\ell^N$ tend to zero $\varpi$-adically, and every remaining coefficient or monomial has increasing adic order. This elementary convergence is what removes the finite-order equations in patched finite shadows.

The one-variable case makes the topology visible. Put $S=\mathcal O[[z]]$ and

$$
c_N=(1+z)^{\ell^N}-1
=\ell^Nz+\binom{\ell^N}{2}z^2+\cdots+z^{\ell^N}.
\tag{4.6a}
$$

Fix $d$. Modulo $(\varpi^d,z^d)$, the terms of degree at least $d$ vanish. For each remaining exponent $j<d$, the valuation of $\binom{\ell^N}{j}$ tends to infinity with $N$; this follows by writing the binomial coefficient as

$$
\frac{\ell^N}{j}\binom{\ell^N-1}{j-1}
$$

and observing that $j$ is fixed. Hence $c_N$ is zero modulo $(\varpi^d,z^d)$ for all sufficiently large $N$. The same argument applies coordinatewise for $q$ variables.

The conclusion is topological, not literal. No finite $c_N$ is zero in $S$, and no fixed finite group $\Delta_N$ becomes $\mathbf Z_\ell$. Rather, every bounded-precision observation eventually stops seeing the exponent relation. That is precisely the amount of convergence needed in diagonal patching.

### 4.3 Augmentation on the deformation side

Let $R_N$ represent the global auxiliary deformation problem. Restriction of the universal representation gives

$$
\Lambda_N\longrightarrow R_N.
\tag{4.7}
$$

After quotienting by $\mathfrak a_N$, every tame character becomes trivial, so a deformation is unramified at $Q_N$. Forgetting the ordered line gives a minimal deformation. Conversely, the two coprime residual Frobenius factors of a minimal unramified lift admit unique lifted idempotents. The selected idempotent restores the ordered line and gives the unique augmented auxiliary enhancement. These constructions commute with all Artinian base changes. Hence

$$
R_N/\mathfrak a_NR_N\xrightarrow{\sim}R^{\min}.
\tag{4.8}
$$

This is an isomorphism of represented functors, not merely an equality of tangent spaces. If residual Frobenius were scalar, lifted eigenspaces would not be unique and (4.8) could fail.

### 4.4 Conventions and a local calculation

The geometric Frobenius polynomial (2.11) gives

$$
\alpha_x+\beta_x\equiv T_x\pmod{\mathfrak m},
\qquad
\alpha_x\beta_x\equiv q_xS_x\pmod{\mathfrak m}.
\tag{4.9}
$$

Since $q_x\equiv1\pmod\ell$, the determinant of the old degeneracy Gram matrix reduces to

$$
\begin{aligned}
D_x&=(q_x+1)^2-S_x^{-1}T_x^2\\
&\equiv4-\frac{(\alpha_x+\beta_x)^2}{\alpha_x\beta_x}
=-\frac{(\alpha_x-\beta_x)^2}{\alpha_x\beta_x}\pmod{\mathfrak m}.
\end{aligned}
\tag{4.10}
$$

The last expression is nonzero because the roots are distinct and nonzero. Therefore $D_x$ is a unit after localization at the selected maximal ideal. This single calculation simultaneously checks the central normalization, the importance of ordered distinct roots, and the integral splitting needed to return from oriented level.

## 5. Definite-quaternion modules at auxiliary level

### 5.1 Deep level and the effective diamond action

At each $x\in Q_N$, choose the oriented subgroup $U_0(x)$ and let $U_1(x,N)$ be the kernel of its projective diagonal-ratio quotient of order $\ell^N$. Taking products gives levels $U_0(Q_N)$ and $U_1(Q_N,N)$. Right translation induces a diamond action of the nominal group $\Delta_N$ on the deep-level class groupoid and hence on its automorphic module.

A group action alone does not make the module free over the group ring. Freeness requires the fibers of the map from deep to oriented class groupoids to be genuine torsors and requires coefficient stabilizers to remain unchanged. Projectivization removes the local center, and the full-effective-rank hypothesis says that every remaining arithmetic stabilizer has trivial image. Hence the effective group is the full nominal product $\Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q$; passing to a smaller effective quotient would lower the number of patching variables and invalidate the dimension ledger.

Let $M_N$ denote the localized primary deep-level module and $M_N^\dagger$ its adjoint companion. The primary factor uses the chosen root $\alpha_x$ at every auxiliary place. The companion factor is dictated by the adjoint involution; it is not an informally identical copy.

### 5.2 Group-ring freeness

The torsor decomposition expresses the full deep-level module as a direct sum of modules of functions on free $\Delta_N$-orbits. After primary localization, projective summands remain projective over $\Lambda_N$. Since $\Lambda_N$ is local, finite projective modules are free. Thus

$$
M_N\simeq\Lambda_N^{\oplus r},
\qquad
M_N^\dagger\simeq\Lambda_N^{\oplus r^\dagger}.
\tag{5.1}
$$

Exact augmentation shows that the ranks are independent of the depth. Because the auxiliary root refinement of the old module has one factor isomorphic to the minimal module at each chosen root, the rank is also independent of the identities of the primes in $Q_N$. We denote it by $r>0$.

The positivity of $r$ is inherited from residual automorphy at minimal level. Patching a zero module would give no information about the deformation ring, so this nonvanishing must be recorded explicitly.

### 5.3 From oriented level back to minimal level

Diamond coinvariants descend from deep level to oriented level, not automatically to hyperspecial minimal level. At one auxiliary place the two degeneracy maps give

$$
d=(d_0,d_1):M\oplus M\longrightarrow M_0(x).
\tag{5.2}
$$

With the normalization of (2.11), the adjoint composite is

$$
d^*d=
\begin{pmatrix}
q_x+1&T_x\\
S_x^{-1}T_x&q_x+1
\end{pmatrix}.
\tag{5.3}
$$

Its determinant is $D_x$ from (4.10), hence a unit. Therefore

$$
e_{\mathrm{old}}=d(d^*d)^{-1}d^*
\tag{5.4}
$$

is an integral idempotent onto the old image. The complementary new summand is annihilated after localization: on genuine new support the level-raising relation makes $D_x$ vanish, whereas $D_x$ is a unit at our maximal ideal. The saturated degeneracy theorem ensures that this splitting is integral, not merely valid after inverting $\varpi$.

Here is the support argument in detail. Since $d^*d$ is invertible, $d$ is injective and $d^*$ is surjective after localization. For $y\in M_0(x)$,

$$
e_{\mathrm{old}}^2y
=d(d^*d)^{-1}d^*d(d^*d)^{-1}d^*y
=e_{\mathrm{old}}y.
\tag{5.5}
$$

If $y=d(u)$ is old, the same calculation gives $e_{\mathrm{old}}y=y$. If $d^*y=0$, then $e_{\mathrm{old}}y=0$. Hence

$$
M_0(x)=\operatorname{im}(d)\oplus\ker(d^*)
\tag{5.6}
$$

integrally at the selected localization. The second summand is the integral new part. Its characteristic-zero constituents satisfy the newvector relation $S_x^{-1}T_x^2=(q_x+1)^2$, so $D_x$ acts as zero on them. Since the module is $\mathcal O$-torsion-free and $D_x$ is a unit in the localized Hecke algebra, the new part must vanish. This proves full oldness without assuming that every oriented vector is visibly in the image of a degeneracy map.

On the old image, Frobenius or the oriented operator has a polynomial whose reduction has roots $\alpha_x$ and $\beta_x$. Hensel factorization produces complementary integral idempotents. Each factor is isomorphic to one original hyperspecial copy, while adjunction determines the corresponding root on the companion side.

Finally the two distinct roots split the old image into two primary factors. Localizing at the $\alpha_x$ factor selects one copy of the hyperspecial module. Removing the primes one at a time, with commuting local correspondences, gives

$$
M_N/\mathfrak a_NM_N\xrightarrow{\sim}M^{\min}.
\tag{5.7}
$$

The order of removal does not matter because the degeneracy correspondences occupy distinct local factors. The same proof applies to the companion module.

### 5.4 Pairings, adjoints, and uniform rank

The coefficient pairing and the finite diamond torsor yield a group-ring-valued pairing

$$
\mathcal H_N:M_N\times M_N^\dagger\longrightarrow\Lambda_N.
\tag{5.8}
$$

It is linear in the first variable and semilinear in the second for the involution $[\delta]\mapsto[\delta^{-1}]$. Perfectness follows fiber by fiber from the regular representation of the diamond group and the perfect coefficient pairing. The named Hecke operators are adjoint under inverse double cosets.

Augmentation of (5.8) recovers the minimal primary--companion pairing. Invariants and coinvariants agree through the norm map because the modules are free over $\Lambda_N$. This statement would be false for an arbitrary module in residue characteristic dividing $|\Delta_N|$; freeness is doing essential work.

## 6. The finite Taylor--Wiles system

### 6.1 Rings, Hecke algebras, and modules

Let $\mathbb T_N$ be the faithful image of the named auxiliary Hecke algebra on $M_N$. The auxiliary-level realization hypothesis of Section 2.3, applied to every generic branch and not inferred merely from residual occurrence, permits the same trace-coordinate descent as at minimal level. It constructs a representation

$$
\rho_N:G_F\longrightarrow\operatorname{GL}_2(\mathbb T_N)
\tag{6.1}
$$

with determinant $\delta$. At old places it satisfies the same minimal conditions as before. At $x\in Q_N$, local--global compatibility identifies the selected oriented character with the diamond character and places $\rho_N$ in the ordered auxiliary condition of (4.1). Universality therefore gives

$$
R_N\longrightarrow\mathbb T_N.
\tag{6.2}
$$

There is a small generation point here. Begin with the order generated by good Hecke traces and the fixed determinant coefficients. Density puts the trace of every Galois element in this order, and residual absolute irreducibility gives the representation over it. At $x$, let $a_x,b_x$ be the Hensel lifts of the two residual roots in that trace order. Their difference is a unit, so

$$
e_x=\frac{\rho_N(\Phi_x)-b_x}{a_x-b_x}
\tag{6.2a}
$$

is the integral projector onto the selected line. If $\tau_x$ is a tame generator, then

$$
\operatorname{tr}\bigl(e_x\rho_N(\tau_x)\bigr)=\chi_x(\tau_x).
\tag{6.2b}
$$

Local--global compatibility identifies this element, with the fixed possible inversion from Section 4.1, with the projective diamond operator. Thus the entire group algebra $\Lambda_N$, as well as the ordered Frobenius root, already lies in the trace order. The hypothesis that no further auxiliary operator has been adjoined now shows that good traces and the fixed determinant generate $\mathbb T_N$. Hence (6.2) is surjective. This is a finite-level argument and does not use the desired minimal equality.

### 6.2 The commuting action diagram

The three actions must agree in the diagram

$$
\begin{array}{ccccc}
\Lambda_N&\longrightarrow&R_N&\twoheadrightarrow&\mathbb T_N\\
&&&&\downarrow\\
&&&&\operatorname{End}_{\Lambda_N}(M_N).
\end{array}
\tag{6.3}
$$

The top-left map comes from tame inertia in the universal deformation. The bottom action comes from geometric diamonds. Their equality follows from local--global compatibility on every characteristic-zero branch and then from the reduced generic Hecke algebra together with $\mathcal O$-torsion-freeness. Merely knowing that the two actions have the same residual character would not suffice.

The algebra $\mathbb T_N$ is by definition faithful on $M_N$. No faithfulness of $R_N$ is asserted. Its kernel is precisely the question that patching will resolve.

### 6.3 Exact augmentation

Equations (4.8) and (5.7) give exact ring and module control. The acting algebra requires one more, logically independent saturation statement: endomorphisms that vanish after augmentation must be generated by the augmentation ideal in the acting image. This is the acting-image augmentation hypothesis stated in Section 2.3; module freeness and saturated degeneracy maps alone would not imply it. It gives

$$
\mathbb T_N/\mathfrak a_N\mathbb T_N\xrightarrow{\sim}\mathbb T^{\min}.
\tag{6.4}
$$

Thus the entire auxiliary datum specializes to the fixed minimal datum, not to a rationally isomorphic lattice or a larger oriented Hecke algebra.

### 6.4 Nonnested levels and finite shadows

The sets $Q_N$ are unrelated, so there are no natural maps $R_{N+1}\to R_N$ or $M_{N+1}\to M_N$. To manufacture such maps would confuse a common presentation with an arithmetic transition.

Instead, fix an increasing sequence of Artinian precision ideals. At precision $d$, retain:

- the quotient diamond algebra and its ordered generators;
- the quotient deformation ring and named structural maps;
- the free module with a marked basis;
- the acting image and a finite initial set of named Hecke operators;
- augmentation maps, primary idempotents, pairings, and adjoints;
- the chosen absolute source and its marked quotient ideal, together with any relation tuple retained for the separate framed audit.

Only finitely many marked diagrams of bounded size occur at a fixed precision. An infinite pigeonhole argument chooses a subsequence on which the precision-$1$ diagram stabilizes; a further subsequence stabilizes precision $2$; continuing diagonally gives compatible finite shadows at every precision. The transitions belong to these stabilized shadows, not to the original arithmetic family.

The finiteness assertion deserves proof. At fixed precision the coefficient ring is finite because $k$ is finite. A free module of fixed rank is therefore a finite set. Its endomorphism ring has only finitely many subrings, ideals, matrices, and tuples of named elements. The common source $P$ has a finite quotient at that precision, and a finite ring has only finitely many quotient ideals. Consequently only finitely many complete marked diagrams can occur.

Compatibility means more than repetition of isomorphism classes. A vertex at precision $d+1$ includes a chosen reduction isomorphism to its predecessor at precision $d$, and the isomorphism respects every marked map. The infinite path therefore gives actual transition maps among the shadow diagrams. This is what later permits inverse limits of action squares and exact sequences.

Pairings require their own marks. A basis change can preserve the abstract module while changing the pairing matrix by a nontrivial unit or conjugation. Retaining the companion basis, the diamond involution, and the pairing matrix ensures that perfectness and Hecke adjunction survive the diagonal passage with their precise normalization.

## 7. The minimal presentation theorem

### 7.1 Why absolute and relative counts must be separated

If full framed local rings are placed in a base ring, the relative tangent condition is strict at those places and the relative dual condition is relaxed. Its dimension can be nonzero even though the absolute auxiliary dual Selmer group (3.10) vanishes. Therefore one may not set every relative relation count equal to zero merely by citing (3.10).

For the clean minimal theorem, it is more transparent to return to the unframed absolute presentation. The exact tangent count, rather than a relative relation count, gives a common power-series source with exactly $q$ variables. We will patch the actual ideals of its finite quotients. We neither need nor assert a uniform generating tuple for those ideals.

This distinction is important. Vanishing of the absolute auxiliary dual Selmer group controls global obstruction classes, but the auxiliary local group algebra is not smooth over $\mathcal O$. One cannot conclude that $R_N$ is a power-series ring. The equal-variable argument will prove that the patched quotient of the power-series source is the whole source, using the faithful scalar diamond action rather than an unsupported finite-level equation count.

### 7.2 The sharp absolute source

The tangent space of the unframed auxiliary deformation ring is $H^1_{\mathcal L_{Q_N}}(F,M)$. Equation (3.11) therefore gives

$$
\dim_k\frac{\mathfrak m_{R_N}}
{\mathfrak m_{R_N}^2+\varpi R_N}=q.
\tag{7.1}
$$

Choose a basis of this cotangent dual and lift it to elements of $\mathfrak m_{R_N}$. The topological form of Nakayama's lemma gives a continuous surjection

$$
P=\mathcal O[[x_1,\ldots,x_q]]\twoheadrightarrow R_N.
\tag{7.2}
$$

The source $P$ is independent of $N$ after choices. Its quotient ideal may vary arbitrarily with $N$ subject to the retained finite-shadow data. In particular, (7.2) does not say that $R_N$ is flat, reduced, a complete intersection, or finite over $\mathcal O$. It records only the exact absolute generator count.

The proof of topological Nakayama is short. Let $B$ be the closed $\mathcal O$-subalgebra generated by the chosen lifts. Surjectivity on cotangent spaces says

$$
\mathfrak m_{R_N}=\mathfrak m_B R_N+\mathfrak m_{R_N}^2.
$$

Modulo every power $\mathfrak m_{R_N}^d$, ordinary Nakayama shows that the image of $B$ is the whole quotient. Completeness then gives $B=R_N$. This establishes (7.2) without selecting relations.

### 7.3 Diamond lifts and finite-order equations

The structural diamond parameters can be lifted through (7.2) to power series

$$
z_i\longmapsto h_{N,i}(x_1,\ldots,x_q)\in\mathfrak m_P.
\tag{7.3}
$$

They define a continuous local map

$$
\alpha_N:S_\infty\longrightarrow P,
\qquad z_i\longmapsto h_{N,i},
\tag{7.4}
$$

whose composite with $P\twoheadrightarrow R_N$ is the diamond map. Since the $i$th diamond has order $\ell^N$,

$$
(1+h_{N,i})^{\ell^N}-1\in\ker(P\to R_N).
\tag{7.5}
$$

These displayed relations explain why a fixed arithmetic level cannot carry a faithful action of the full power-series diamond algebra. They tend to zero in every fixed Artinian shadow as $N$ grows, so they place no finite-order restriction on the limiting scalar action. We make no claim that they generate $\ker(P\to R_N)$. Every other element of that kernel is retained simply as an element of the marked quotient ideal at finite precision.

After diagonalization, the $h_{N,i}$ converge in the shadow sense to elements $h_i\in\mathfrak m_P$. They define one map

$$
\alpha:S_\infty\longrightarrow P,
\qquad z_i\longmapsto h_i.
\tag{7.6}
$$

Compatibility of the finite diamond and automorphic actions will say that the composite of $\alpha$ with the patched $P$-action is ordinary scalar multiplication by $S_\infty$. This is the key equality used in Chapter 10.

### 7.4 Framed and unframed ledgers

Frames may be used to represent local restrictions and assemble completed local products. For a nonempty framing set $T$, the full change-of-basis correction is

$$
c_T=4|T|-1.
\tag{7.7}
$$

Compatible frames give a formally smooth extension

$$
R_\infty^{\square_T}\simeq
R_\infty[[w_1,\ldots,w_{c_T}]].
\tag{7.8}
$$

Auxiliary framed local rings have two additional eigenline-position variables beyond their unframed versions. These are counted once, either inside the local base or among presentation variables. Removing genuine frame variables uses a regular smooth sequence. Removing padding variables paired with linear equations is only cancellation in a presentation. The two operations must not be conflated.

The framed audit can be organized in four columns:

| datum | source of the number | behavior with $N$ | role in the absolute patch |
|---|---|---|---|
| $q$ | minimal absolute dual Selmer | constant | number of auxiliary primes and variables of each source |
| $q_{T,N}$ | dual Selmer relaxed at the chosen local base | bounded, not necessarily constant | bounds relative obstruction rows |
| $g_{T,N}$ | strict primal tangent plus gauge correction | bounded, not necessarily constant | counts relative presentation variables |
| $c_T$ | frame torsor | constant | removed by a genuine smooth quotient |

Global duality fixes the difference $g_{T,N}-q_{T,N}$ once the local-base and frame convention are fixed. It need not fix the two terms separately. To obtain common relative presentations, choose the maximum obstruction rank and add a variable together with the linear relation setting it to zero whenever a level needs padding. This operation raises variable and relation counts together.

The absolute patch avoids carrying that padded relation tuple. After frames are removed, (3.13) gives the exact unframed tangent dimension $q$ directly. Topological Nakayama then gives the common source $P$ in (7.2), and the entire quotient ideal is marked at each precision. Thus the relative framed ledger remains an audit of effectivity and covariance, while the sharp absolute source performs the kernel-killing argument.

For rank two, one local frame is not simply three variables at every place. A chosen basis has four infinitesimal entries, and the single global scalar stabilizer must be removed. This gives $4|T|-1$, whereas the trace-zero deformation coefficient module has dimension three. Confusing these two appearances of “three” changes the source dimension and destroys equal-variable rigidity.

The common source (7.2) is the canonical unframed numerical conclusion. It is obtained after all frame variables have been removed through the smooth comparison, not by subtracting dimensions from an unidentified framed ring. Regularity of the patched quotient will be proved only in Chapter 10.

## 8. Patching the rings and modules

### 8.1 Artinian precision

Let $\mathfrak m_S$ and $\mathfrak m_P$ be the maximal ideals of $S_\infty$ and $P$. Choose cofinal precision ideals, for example

$$
\mathfrak b_d=(\varpi^d,\mathfrak m_S^d),
\qquad
\mathfrak p_d=(\varpi^d,\mathfrak m_P^d).
\tag{8.1}
$$

At sufficiently large auxiliary depth, the group relations vanish in these quotients. The modules are quotients of free modules of one fixed rank, and every named ring and map has finite underlying cardinality. This finiteness is the compactness input.

For the absolute source $P$, choose a cofinal increasing function $\nu(d)$ and put

$$
P_d=P/\mathfrak m_P^{\nu(d)}.
\tag{8.2}
$$

The function is chosen large enough that the action image visible on the precision-$d$ module is already a quotient of $P_d$. Such a bound exists because the image is a finite local ring, so its maximal ideal is nilpotent. At level $N$, define the ring shadow

$$
R_{N,d}=R_N/\mathfrak m_{R_N}^{\nu(d)}.
\tag{8.3}
$$

Surjectivity of $P\to R_N$ gives

$$
R_{N,d}\simeq
P/\bigl(\ker(P\to R_N)+\mathfrak m_P^{\nu(d)}\bigr).
\tag{8.4}
$$

Thus the marked ideal in $P_d$ remembers the full ring shadow, including relations not visible in the module action. This prevents the patched deformation ring from being silently replaced by its Hecke quotient before faithfulness has been proved.

The marked basis matters. An abstract assertion that $M_N$ is free of rank $r$ would not produce compatible identifications of its shadows. On the ring side, it is enough to mark the ideal of the quotient of $P$ at each precision. A finite ring has only finitely many ideals, so no uniform relation tuple is required for this absolute patch.

### 8.2 Coherent diagonalization

Form a rooted tree whose vertices at height $d$ are the marked precision-$d$ diagrams occurring infinitely often. Join a height-$(d+1)$ vertex to its reduction at height $d$. The tree is finitely branching and has vertices at every height, so it has an infinite path. That path supplies compatible ring, module, action, augmentation, and pairing shadows.

To justify the infinite path directly, prune every vertex that has only finitely many descendants arising from the arithmetic family. At least one vertex remains at every height, for otherwise only finitely many arithmetic levels would occur. Starting at the root, choose a surviving child at each stage. Finite branching ensures that a surviving child exists, and the resulting path has vertices at all heights.

At height $d$, the group relations (7.5) are zero after passing sufficiently far along the selected depths. Indeed, $h_{N,i}$ is topologically nilpotent, the coefficient $\ell^N$ of its linear term tends to zero, and for every fixed degree the remaining binomial coefficients have the required increasing divisibility or the monomial itself lies beyond the fixed precision. Thus the limiting $S_\infty$-action has no finite exponent. This observation is used only to identify the limiting diamond source; it is not used to erase the marked quotient ideal of $P_d$.

This construction proves compatibility, not canonicity. Different paths can produce noncanonically isomorphic power-series coordinates. The finite conclusion will nevertheless be canonical because every path descends to the same universal minimal deformation problem and the same faithful Hecke image.

### 8.3 The patched objects

Take inverse limits along the coherent shadows. The compatible quotient ideals $I_d\subseteq P_d$ lift to one closed ideal

$$
I_\infty=\{f\in P:f\bmod\mathfrak m_P^{\nu(d)}\in I_d
\text{ for every }d\}.
\tag{8.5}
$$

They give a patched ring

$$
R_\infty=P/I_\infty.
\tag{8.6}
$$

At this stage $I_\infty$ may be nonzero. The free module shadows give

$$
M_\infty\simeq S_\infty^{\oplus r}.
\tag{8.7}
$$

For completeness, the last assertion follows by lifting compatible bases. At precision $d$, the marked basis identifies the module shadow with $(S_\infty/\mathfrak b_d)^r$. The reduction maps carry basis vectors to basis vectors. Taking inverse limits produces $r$ elements of $M_\infty$ and an isomorphism from $S_\infty^r$ because it is an isomorphism modulo every ideal in a cofinal complete filtration.

Let

$$
A_\infty=\operatorname{im}\left(
P\longrightarrow R_\infty\longrightarrow
\operatorname{End}_{S_\infty}(M_\infty)
\right).
\tag{8.8}
$$

Then $A_\infty$ is finite over $S_\infty$, and

$$
A_\infty=R_\infty/\operatorname{Ann}_{R_\infty}(M_\infty).
\tag{8.9}
$$

The map (7.6) and compatibility of the patched actions give

$$
S_\infty\xrightarrow{\alpha}P\longrightarrow A_\infty
\hookrightarrow\operatorname{End}_{S_\infty}(M_\infty),
\tag{8.10}
$$

where the composite sends $s$ to $s\operatorname{id}$. The scalar action makes $S_\infty\to A_\infty$ injective: a scalar killing the free nonzero module must be zero. We do not yet infer that $P\to A_\infty$ is injective; that is the equal-variable rigidity theorem.

The primary--companion pairings pass to a perfect $S_\infty$-valued pairing

$$
\mathcal H_\infty:M_\infty\times M_\infty^\dagger
\longrightarrow S_\infty
\tag{8.11}
$$

with diamond inversion and the named Hecke adjoints.

### 8.4 Exact recovery at augmentation

Finite inverse systems with surjective shadow transitions satisfy exact inverse-limit descent. Applying this to the augmented rings and modules gives

$$
R_\infty/\alpha(\mathfrak a_\infty)R_\infty\simeq R^{\min},
\qquad
M_\infty/\mathfrak a_\infty M_\infty\simeq M^{\min}.
\tag{8.12}
$$

Because $M_\infty$ is free over $S_\infty$,

$$
\operatorname{Tor}^{S_\infty}_i(\mathcal O,M_\infty)=0
\qquad(i>0).
\tag{8.13}
$$

The retained acting-algebra saturation gives

$$
A_\infty/\mathfrak a_\infty A_\infty\simeq\mathbb T^{\min}.
\tag{8.14}
$$

Let us prove the first isomorphism rather than infer it from a tensor product. At every finite level,

$$
R_N/(h_{N,1},\ldots,h_{N,q})R_N\simeq R^{\min}.
\tag{8.15}
$$

Reduce (8.15) at every retained precision and include its kernel and quotient maps in the finite shadow. The transition maps are surjective, so the inverse system of kernels satisfies the Mittag--Leffler condition. Inverse limits preserve the exact quotient sequence. The ideals generated by the compatible $h_i$ are closed because the limiting rings are Noetherian and complete. This proves the ring statement in (8.12). The module and acting-algebra statements follow from the separately retained exact sequences and saturation marks in the same way.

Ordinary tensor product is sufficient in (8.12)--(8.14) because the relevant modules are finite and complete. Completed tensor notation gives the same result. The first quotient uses the ideal generated by the images $h_i=\alpha(z_i)$; writing it merely as $(z_1,\ldots,z_q)R_\infty$ would hide the structural map.

## 9. The dimension and depth ledger

### 9.1 Dimensions of the two source rings

Equations (4.5) and (7.2) give

$$
\dim S_\infty=q+1,
\qquad
\dim P=q+1.
\tag{9.1}
$$

Both source rings are regular local domains. The equality is not an expected-dimension calculation: the first is the displayed diamond power-series ring and the second is the displayed absolute deformation source.

The two coordinate systems need not match. Indeed, the power series $h_i$ in (7.6) can have vanishing linear terms. What matters is that the scalar-compatible action places a quotient of $P$ between the two equal-dimensional sources and a finite endomorphism algebra.

### 9.2 Depth over three acting rings

Freeness over $S_\infty$ gives

$$
\operatorname{depth}_{S_\infty}M_\infty=q+1.
\tag{9.2}
$$

The action image $A_\infty$ is finite over $S_\infty$ and contains $S_\infty$ faithfully. Consequently its support over $S_\infty$ is the whole spectrum and

$$
\dim A_\infty=q+1.
\tag{9.3}
$$

Since $P\twoheadrightarrow A_\infty$, this is already a dimension ceiling on the kernel of the action from $P$. It is not yet a depth statement over $R_\infty$, because we have not proved $I_\infty=0$.

### 9.3 Why equality of dimensions is exact here

In a general patched problem, a module free over $S_\infty$ produces an action quotient of dimension $q+1$ but does not rule out larger or missed components of an ambient deformation ring. Here the ambient source $P$ itself has dimension $q+1$. Thus the quotient $A_\infty$ has the same dimension as the regular domain $P$.

Any nonzero ideal of the Noetherian local domain $P$ has height at least one. Its quotient has dimension at most $q$. Therefore a quotient of $P$ having dimension $q+1$ must equal $P$. This sharp source ceiling, not an assumption about component coverage, is what makes the minimal argument special.

### 9.4 The zero auxiliary-prime case

If $q=0$, take every $Q_N$ empty. Then

$$
S_\infty=\mathcal O,
\qquad
P=\mathcal O.
\tag{9.4}
$$

The patched action image contains the faithful scalar copy of $\mathcal O$ and is a quotient of $P=\mathcal O$, so it equals $\mathcal O$. The same kernel argument gives $R_\infty=P$. Descent proves $R^{\min}=\mathbb T^{\min}=\mathcal O$. Thus no positive-$q$ assumption is hidden in the theorem.

## 10. Regularity, freeness, and support

### 10.1 Regularity of the patched deformation ring

We isolate the core algebraic consequence.

**Proposition 10.1 (equal-variable rigidity).** The map

$$
P\longrightarrow A_\infty
\tag{10.1}
$$

is an isomorphism. Consequently $I_\infty=0$ and

$$
R_\infty=P=A_\infty.
\tag{10.2}
$$

In particular, the patched deformation ring is regular of dimension $q+1$.

**Proof.** The image $A_\infty$ is an $S_\infty$-submodule of the finite free module $\operatorname{End}_{S_\infty}(M_\infty)$, hence finite over the Noetherian ring $S_\infty$. Scalar compatibility in (8.10) injects $S_\infty$ into $A_\infty$. A finite integral extension has the same dimension as its base, so

$$
\dim A_\infty=\dim S_\infty=q+1.
$$

On the other hand, $A_\infty$ is a quotient of the regular local domain $P$, also of dimension $q+1$. If the kernel contained a nonzero element $f$, then $f$ would be a nonzerodivisor of $P$ and

$$
\dim A_\infty\leq\dim P/(f)=q,
$$

a contradiction. Thus $P\to A_\infty$ is injective and hence an isomorphism. The action factors through $R_\infty=P/I_\infty$, so $I_\infty$ lies in the zero kernel of $P\to A_\infty$. This proves (10.2). $\square$

The proof never describes the finite-level kernels of $P\to R_N$. It allows arbitrary relations and even nilpotents at each finite level. Equal source dimensions and the faithful scalar action force all limiting kernel elements to vanish simultaneously.

Two elementary rings show why every hypothesis is used. If

$$
P'=S_\infty[[u]],
\qquad A'=S_\infty,
$$

with $u$ acting as zero, then $A'$ is still finite over $S_\infty$ and the scalar action is faithful, but $P'$ has one extra dimension. The kernel $(u)$ is not forced to vanish. Equal variable counts rule out this surplus direction.

Conversely, let

$$
B=S_\infty[\epsilon]/(\epsilon^2)
$$

act on $S_\infty$ by killing $\epsilon$. Source and action quotient have the same dimension, and the module has full topological support on $\operatorname{Spec}B$, yet the action is not faithful. The equal-variable lemma does not start with the nonreduced ring $B$ as its source; it starts with the regular domain $P$. In a domain, a nonzero kernel lowers dimension. This is the nilpotent-sensitive feature that a bare support argument lacks.

### 10.2 Freeness over the patched deformation ring

**Proposition 10.2.** The ring $P=R_\infty$ is finite free over $S_\infty$, and there is an integer $m>0$ such that

$$
M_\infty\simeq R_\infty^{\oplus m}.
\tag{10.3}
$$

**Proof.** Proposition 10.1 identifies $P$ with the finite $S_\infty$-algebra $A_\infty$. The ideal $\mathfrak m_{S_\infty}P$ is therefore primary for the maximal ideal of $P$. Depth of a finite module can be computed over either ring, and regularity of $P$ gives

$$
\operatorname{depth}_{S_\infty}P
=\operatorname{depth}_P P=q+1.
$$

The Auslander--Buchsbaum formula over the regular ring $S_\infty$ makes $P$ finite projective, hence finite free. Likewise $M_\infty$ is free over $S_\infty$, so

$$
\operatorname{depth}_P M_\infty
=\operatorname{depth}_{S_\infty}M_\infty=q+1.
$$

A regular local ring has finite global dimension. Auslander--Buchsbaum over $P$ therefore makes $M_\infty$ finite projective and hence free. Its rank is positive because the module is nonzero. $\square$

This is the homological heart of the proof. Equal-variable rigidity first proves regularity and faithful action; maximal depth then upgrades the module to free. The logical order avoids using patched faithfulness to prove the dimension equality that establishes patched faithfulness.

### 10.3 Full component coverage

Freeness immediately gives

$$
\operatorname{Supp}_{R_\infty}M_\infty
=\operatorname{Spec}R_\infty.
\tag{10.4}
$$

This is full scheme-theoretic coverage. It is stronger than saying that the support meets every irreducible component. If one had only topological coverage, the annihilator would be known merely to be nilpotent. Here the ring has one reduced component and the module is free on every infinitesimal neighborhood of its generic point.

The support argument is therefore not an assumption smuggled in from automorphy. It is a consequence of the independently established regular presentation and module depth.

One can phrase the conclusion at the generic point as well. The unique minimal prime of $R_\infty=P$ is zero, and localization gives a nonzero vector space over $\operatorname{Frac}(P)$. More importantly, the free lattice before localization proves that every element of every infinitesimal neighborhood acts as expected. Generic nonvanishing alone would not have supplied that stronger statement.

### 10.4 Faithfulness and kernel killing

A nonzero free module over a ring is faithful. From (10.3),

$$
\operatorname{Ann}_{R_\infty}(M_\infty)=0.
\tag{10.5}
$$

Combining (8.8)--(8.9) with (10.5) recovers the isomorphism

$$
R_\infty\xrightarrow{\sim}A_\infty.
\tag{10.6}
$$

This kills ordinary kernel elements and nilpotents at the same time. Neither generic reducedness of the finite Hecke algebra nor a comparison of reduced quotients is needed at this stage. Generic reducedness was used earlier to construct and descend the Hecke-valued representation; it is not recycled as a substitute for faithfulness.

## 11. Descent to minimal level

### 11.1 The augmentation sequence is regular

The equality (10.6) shows that $R_\infty$ is finite over $S_\infty$, because $A_\infty$ is a submodule of the finite free $S_\infty$-module $\operatorname{End}_{S_\infty}(M_\infty)$. It is torsion-free over $S_\infty$ since the structural map is injective and $R_\infty$ is a domain.

More precisely, $R_\infty$ is Cohen--Macaulay of the same dimension as the regular local ring $S_\infty$. The depth formula and Auslander--Buchsbaum over $S_\infty$ show that it is finite free over $S_\infty$. Consequently

$$
z_1,\ldots,z_q
\tag{11.1}
$$

is an $R_\infty$-regular sequence. Notice that these are the images of the diamond parameters in $R_\infty$; they need not coincide with the global coordinates $x_i$.

### 11.2 Ring, module, and Hecke descent

Exact control gives the commutative diagram

$$
\begin{array}{ccc}
R_\infty&\xrightarrow{\sim}&A_\infty\\
\downarrow&&\downarrow\\
R^{\min}&\twoheadrightarrow&\mathbb T^{\min},
\end{array}
\tag{11.2}
$$

where the vertical maps are quotient by the ideals generated by the images of $\mathfrak a_\infty$. Quotienting an isomorphism by the corresponding ideal gives an isomorphism. Hence the bottom map is injective as well as surjective.

For modules, (10.3) and exact augmentation give

$$
M^{\min}
\simeq M_\infty/\mathfrak a_\infty M_\infty
\simeq
(R^{\min})^{\oplus m}.
\tag{11.3}
$$

There are no higher Tor correction terms because the augmentation sequence is regular on both the ring and the module.

### 11.3 Proof of the minimal comparison theorem

**Proof of Theorem 1.1.** Chapters 3--6 construct, for every $N$, the auxiliary sets, deformation rings, Hecke action algebras, and free diamond modules with exact augmentation. Chapters 7--8 patch their coherent finite shadows under two power-series sources with the same dimension. Chapters 9--10 use the scalar-compatible action to prove $R_\infty=P=A_\infty$, then prove $M_\infty$ free over this regular ring. Diagram (11.2) gives

$$
R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.
$$

The regular augmentation sequence makes the common ring finite free over $\mathcal O$ and a complete intersection, as proved in Chapter 12. Equation (11.3) gives module freeness. Perfect pairings descend by (8.11), and the determinant statement follows from Chapter 13. $\square$

### 11.4 Canonicity

Coordinates, ordered cyclic generators, marked bases, and the diagonal subsequence are not canonical. They affect the displayed presentations of $S_\infty$, $R_\infty$, and $M_\infty$. They do not affect the finite comparison map. The map at the bottom of (11.2) is characterized by the universal minimal representation and the Hecke-valued representation, so it is the original canonical map (1.1).

Thus one successful patch proves a choice-independent arithmetic equality. A second choice can produce a different auxiliary limiting presentation, but after augmentation it proves the same universal statement.

## 12. Complete intersections and Gorenstein duality

### 12.1 The minimal ring as a regular quotient

By (11.1) and (8.12),

$$
R^{\min}\simeq
R_\infty/(z_1,\ldots,z_q)R_\infty.
\tag{12.1}
$$

The ambient ring $R_\infty$ is regular, and the displayed sequence is regular. Therefore $R^{\min}$ is a complete intersection of codimension $q$. Its dimension is

$$
(q+1)-q=1.
\tag{12.2}
$$

There is a more direct flatness proof than inspecting the coefficient parameter. Proposition 10.2 makes $R_\infty$ finite free over $S_\infty$. Tensoring that free module with

$$
S_\infty/\mathfrak a_\infty\simeq\mathcal O
$$

and using exact augmentation gives $R^{\min}$ finite free over $\mathcal O$. In particular, the coefficient parameter is a nonzerodivisor. This argument proves flatness before invoking any reduced generic fiber.

The number of augmentation equations is exactly $q$. This is not a recycled claim that the original minimal presentation has exactly $q$ obstruction equations. The equations in (12.1) are the images of the $q$ diamond parameters on the already constructed regular patched ring. Their regularity was proved through finite freeness over $S_\infty$.

### 12.2 Freeness of the minimal automorphic module

Equation (11.3) proves

$$
M^{\min}\simeq(R^{\min})^{\oplus m}.
\tag{12.3}
$$

The rank $m$ is the automorphic multiplicity of the localized primary packet in the chosen definite-quaternion realization. Patching proves freeness without requiring $m=1$. This distinction matters: multiplicity one is a separate automorphic assertion, while freeness is a structural conclusion from regularity and depth.

The companion module is likewise free over the adjoint companion Hecke algebra. When the adjoint involution identifies the primary and companion localizations, the perfect pairing gives a duality of free modules over the common ring.

### 12.3 Gorenstein conclusions

A quotient of a regular local ring by a regular sequence is Gorenstein. Hence

$$
R^{\min}=\mathbb T^{\min}
\tag{12.4}
$$

is Gorenstein. Equivalently, its relative dualizing module over $\mathcal O$ is free of rank one. This conclusion comes from the complete-intersection presentation and does not require the automorphic module itself to have rank one.

The patched ring $R_\infty$ is regular and therefore Gorenstein as well. The finite flat map $S_\infty\to R_\infty$ has a relative dual module, and the primary--companion pairing supplies the automorphic realization of the corresponding trace duality after the adjoint identification.

### 12.4 What is and is not rank one

Three ranks occur and should not be confused:

| object | base ring | rank statement |
|---|---|---|
| $M_N$ | $\Lambda_N$ | fixed positive rank $r$ |
| $M_\infty$ | $R_\infty$ | fixed positive rank $m$ |
| dualizing module of $R^{\min}$ | $R^{\min}$ | rank one |

The last row is the Gorenstein statement. It does not force $M^{\min}$ to have rank one. If a separate multiplicity-one theorem gives $m=1$, then the automorphic module itself is free of rank one, but Theorem 1.1 does not need that extra assertion.

## 13. Determinants and congruence modules

### 13.1 Two determinant constructions

Fix a generically isolated augmentation

$$
\lambda:\mathbb T^{\min}\longrightarrow\mathcal O.
\tag{13.1}
$$

On the deformation side, the minimal Selmer complex is perfect and balanced. Its determinant line records the alternating tangent and obstruction directions. Auxiliary dual-Selmer vanishing gives the sharp absolute tangent count, while the patched regular presentation is obtained separately by equal-variable rigidity.

On the automorphic side, restrict the perfect primary--companion pairing to the selected saturated branch. The resulting two-term complex becomes acyclic after inverting $\varpi$. Its determinant section has valuation equal to the length of the module congruence quotient. Under primitive multiplicity and branch saturation, this is the branch multiplicity times the ring congruence length.

These constructions exist before the equality $R^{\min}=\mathbb T^{\min}$ is known. The deformation determinant uses the universal presentation; the automorphic determinant uses the integral pairing. They are not canonically equal merely because both are determinant lines. In the proof route adopted here their comparison is made only after the ring equality has been established independently.

### 13.2 Compatibility through finite shadows

After Theorem 1.1, write the common ring as $A=R^{\min}=\mathbb T^{\min}$. Equation (12.1) gives a square complete-intersection presentation

$$
A\simeq
\mathcal O[[x_1,\ldots,x_q]]/(h_1,\ldots,h_q),
\tag{13.2}
$$

where the $h_i$ are the images of the diamond augmentation parameters and form a regular sequence. Translate the variables so that the selected augmentation sends every $x_j$ to zero. Then every $h_i$ has zero augmentation.

Let $D$ be the $q$-by-$q$ linearization matrix

$$
D_{ij}=\lambda\left(\frac{\partial h_i}{\partial x_j}\right).
\tag{13.3}
$$

The conormal exact sequence for (13.2) gives a presentation

$$
\mathcal O^q\xrightarrow{D}\mathcal O^q
\longrightarrow\Phi_A\longrightarrow0.
\tag{13.4}
$$

Indeed, the class of $h_i$ maps in the cotangent space to its linear term $\sum_jD_{ij}x_j$. Higher-degree terms lie in the square of the augmentation ideal. Therefore

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)=(\det D).
\tag{13.5}
$$

The same determinant controls the congruence ideal. One way to see this is to use the Koszul resolution on $h_1,\ldots,h_q$. Applying $\operatorname{Hom}_{\mathcal O[[x]]}(-,\mathcal O[[x]])$ identifies the relative dualizing module of $A$ with $A$, generated by the top Koszul class. Restriction to the branch sends this generator to $\det D$ times a generator of the dual of $\mathcal O$. Thus the image of the branch annihilator under $\lambda$ is $(\det D)$. Equivalently, over the fraction field the isolated branch idempotent has denominator $\det D$; the adjugate identity $D\operatorname{adj}(D)=\det(D)I$ proves integrality in one direction, and Smith normal form proves minimality of the denominator.

Consequently the deformation cotangent determinant and the ring congruence determinant are the same element up to a unit. The finite-shadow pairings ensure that the automorphic pairing uses the same integral branch lattice and adjoint normalization, so its determinant realizes this intrinsic congruence ideal rather than a scalar multiple arising from a nonsaturated lattice.

### 13.3 The cotangent--congruence equality

Let $I_R=\ker(\lambda:R^{\min}\to\mathcal O)$ and define the cotangent module

$$
\Phi_R=I_R/I_R^2.
\tag{13.6}
$$

Let $\eta_{\mathbb T}\subseteq\mathcal O$ be the branch congruence ideal, equivalently the image under $\lambda$ of the annihilator of the branch kernel. The determinant comparison gives

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)=\eta_{\mathbb T}.
\tag{13.7}
$$

When the quotients have finite length, this is

$$
\operatorname{length}_{\mathcal O}\Phi_R
=\operatorname{length}_{\mathcal O}(\mathcal O/\eta_{\mathbb T}).
\tag{13.8}
$$

For an automorphic multiplicity $m$, the module congruence quotient has length $m$ times the right side of (13.8). To prove this, choose saturated bases of the primary and companion branch lattices. Primitivity makes the restricted pairing matrix equivalent over $\mathcal O$ to $m$ copies of a matrix whose determinant ideal is $\eta_{\mathbb T}$. Smith normal form adds the valuations of its elementary divisors in each copy, giving

$$
\operatorname{length}_{\mathcal O}\Psi_M
=m\operatorname{length}_{\mathcal O}
(\mathcal O/\eta_{\mathbb T}).
\tag{13.9}
$$

Without saturation, a lattice-index term would have to be added to (13.9). Without primitive multiplicity, the pairing could have an additional matrix discriminant. Thus division by $m$ is justified precisely under the retained hypotheses.

### 13.4 Why the argument is not circular

The route used in Chapters 10--11 proves the ring equality from equal-variable rigidity and patched module freeness. No determinant comparison enters Proposition 10.1, Proposition 10.2, or diagram (11.2). Only afterward do Sections 13.2--13.3 use the common complete-intersection presentation to identify its intrinsic cotangent and congruence determinants.

This order is deliberately asymmetric. Before equality, the Selmer determinant and the automorphic branch determinant are separately defined, and the surjection gives only the usual direction of cotangent and congruence inequalities. We do not claim that finite-shadow compatibility alone supplies the missing equality of determinant sections. After equality and the regular-sequence theorem, the Koszul calculation proves (13.7) without being used retroactively to eliminate the kernel.

There is an abstract numerical criterion that can prove $R=T$ from a common determinant constructed independently before equality, together with flatness, isolation, and saturation. That is a valid alternative in applications where such a cross-determinant theorem is available. It is not the route taken here. What would be circular is to use the post-comparison calculation (13.7) as an input to the proof of Theorem 1.1; no step does so.

## 14. Changes of coefficients and normalization

### 14.1 Finite coefficient extension

Let $\mathcal O'/\mathcal O$ be the integers in a finite extension of coefficient fields, with residue field $k'$. After selecting the local residual factor corresponding to $\bar\rho\otimes_k k'$, completed scalar extension preserves the clean local rings, the universal fixed-determinant problem, the finite automorphic modules, and the perfect pairings. It also preserves regular sequences and finite freeness.

Thus the entire patched construction may be performed after a finite extension used to split residual eigenvalues. One obtains

$$
R^{\min}\widehat\otimes_{\mathcal O}\mathcal O'
\xrightarrow{\sim}
\mathbb T^{\min}\widehat\otimes_{\mathcal O}\mathcal O'.
\tag{14.1}
$$

The common residue field convention must be fixed when forming completed tensor products. A ramified coefficient extension changes valuations of determinant sections by the ramification index, but equality of Fitting ideals after base change remains valid.

### 14.2 Eigenvalues and idempotents

If a selected residual Frobenius polynomial is irreducible over $k$, a finite unramified coefficient extension can split it. The auxiliary-prime theorem is then applied to the scalar-extended representation. Scalar extension changes coordinates but not the kernel of the residual representation, so adequacy and the cyclotomic restriction hypotheses persist.

The ordered idempotent is integral because the two residual roots remain distinct. Its formula divides by their difference, which is a unit. No idempotent is obtained by dividing by a difference that vanishes modulo $\varpi$.

### 14.3 Frobenius, determinants, and diamonds

We consistently use geometric Frobenius and the polynomial (2.11). Local reciprocity is normalized so that the diamond character in (4.1) matches the geometric action used on the automorphic module. Reversing reciprocity replaces a diamond by its inverse and must simultaneously change the pairing involution.

The old--new determinant

$$
(q_x+1)^2-S_x^{-1}T_x^2
\tag{14.2}
$$

depends on the same convention. Omitting $S_x^{-1}$ would make (4.10) false unless the central character happened to be trivial. The determinant lift $\delta$ is fixed at every level, so there is exactly one independent tame character at each auxiliary place.

### 14.4 Returning from enlarged coefficients

Suppose (14.1) is known and $R^{\min}\to\mathbb T^{\min}$ is the original map. Because $\mathcal O'$ is finite free over $\mathcal O$, completed tensor product on these complete Noetherian algebras agrees with the relevant ordinary finite base change and is exact. The kernel and cokernel therefore become zero after tensoring with $\mathcal O'$. Faithful flatness shows that they were already zero; no prior finiteness of the deformation-ring kernel as an $\mathcal O$-module is being assumed. Hence the isomorphism descends to $\mathcal O$.

The same argument descends finite projectivity. Over a local ring, finite projective modules are free, and their rank is read after faithful flat base change. Gorensteinness descends here through the explicit complete-intersection presentation, not through an unsupported claim about arbitrary faithfully flat descent of dualizing modules.

## 15. Boundaries and exceptional cases

### 15.1 Coefficient prime five

At $\ell=5$, an absolutely irreducible representation can have icosahedral projective image with nonzero adjoint first cohomology. Then the detection and disjointness argument of Chapter 3 may fail, and sets $Q_N$ with the required cohomological property have not been constructed by the hypotheses of this book. None of the later algebra compensates for missing auxiliary primes.

The theorem can be applied at five only after a separate image theorem verifies every adequacy clause actually used: no nontrivial $5$-power quotient, the relevant $H^1$ vanishing, absence of trivial quotients, and regular semisimple detection. Absolute irreducibility alone is insufficient, so no blanket coefficient-five corollary is stated.

### 15.2 Scalar Frobenius and failed level control

If $\alpha_x=\beta_x$, there is no unique residual eigenline. The ordered local functor may acquire extra components, augmentation need not forget a uniquely recoverable enhancement, and the determinant (4.10) vanishes. Group-ring freeness at deep level would then not prove minimal-level control.

If the roots are distinct but the degeneracy image is not saturated, the old splitting may exist only after inverting $\varpi$. Coinvariants could recover a lattice of finite index rather than $M^{\min}$. Exact module and Hecke augmentation would fail, invalidating descent even if the patched generic fibers looked correct.

### 15.3 Nonclean local components

A finite-flat ring outside the low-weight unramified-base range can have several components or singularities. A special local condition described only by nonzero monodromy is not closed. A wild type can lack the stated integral rigidity. In any of these cases, the balanced tangent count, exact $q$-variable absolute source, or exact automorphic augmentation can fail.

The general patched comparison can still yield a reduced or componentwise equality if dimensions and support are separately controlled. It does not yield Theorem 1.1. The clean local hypotheses are therefore part of the mathematical content, not presentational conveniences.

### 15.4 Nonminimal problems

Adding ramification at a fixed prime changes the local base, its components, the global dual Selmer group, and the automorphic level complex. The module may be represented by a complex rather than by a single free group-ring module. Component support and determinant comparison then require a new local argument.

The minimal theorem may be used as an input to such a later comparison, but it cannot be transported merely by changing superscripts from “minimal” to “nonminimal.” The one-prime nonminimal problem has its own amplitude, support, and augmentation calculations.

## 16. Dependency closure

### 16.1 The five direct inputs

The proof uses its direct prerequisites in the following exact forms.

| Prior theory | Result used here | Hypotheses matched here |
|---|---|---|
| Book 143, Taylor--Wiles primes | sets of exactly $q$ split regular primes at every depth, killing dual Selmer; local auxiliary rings and augmentation | fixed determinant, odd $\ell$, represented local conditions, adequate cyclotomic restricted image, eigenvalues in the residue field |
| Book 146, abstract $R=T$ | depth transfer, support versus faithfulness, regular-sequence descent, determinant criterion | complete local rings, finite faithful action image, exact augmentation, finite free diamond module, independent regularity or support input |
| Book 152, deep-level quaternionic modules | projective diamond torsors, full-effective-rank group-ring freeness, exact module augmentation, primary--companion duality, minimal-level control criterion | trivial scalar ratio, clean arithmetic stabilizers, saturated degeneracy maps, unit Gram determinant, no localized new support, distinct roots |
| Book 171, minimal totally real deformation--Hecke problem | $R^{\min}\twoheadrightarrow\mathbb T^{\min}$, balanced number $q$, local smoothness, trace-coordinate descent, pairings and determinant data | its standing minimal hypotheses, with the auxiliary analogues separately assumed in Section 2.3 |
| Book 141, residual image classification and adequacy | adequacy and regular semisimple detection for $\ell\geq7$, coefficient-five boundary | absolute irreducibility after cyclotomic restriction and coefficient characteristic at least seven |

The determinant convention is unchanged throughout. Book 143 states prime selection with arithmetic Frobenius; here we invert the selected conjugacy class and its ordered eigenvalues to use geometric Frobenius. This preserves the residue-cardinality congruence, regularity, and localization rank. The quaternionic Hecke polynomial and the projective diamond labels are then transported into the geometric convention fixed in Book 171. No later nonminimal, minimal-lifting, potential-modularity, or solvable-descent result enters the proof.

### 16.2 The two structural inputs used through them

The mechanics invoked in Chapters 6--8 are the results of Book 144 on Taylor--Wiles systems and Book 145 on patching modules and rings. They are direct mechanical prerequisites, distinct from the arithmetic inputs: they explain how the Book 143 primes and Book 152 modules are assembled. We use them in two precise forms.

First, a family indexed by unrelated auxiliary sets becomes patchable only after fixed power-series sources, marked quotient ideals, marked bases, named maps, and pairings are included in finite shadows. No arithmetic transition among the $Q_N$ is asserted. Marking quotient ideals rather than relation tuples is legitimate here because every precision ring is finite and therefore has only finitely many ideals.

Second, inverse limits preserve the required quotient sequences because the finite shadow systems have surjective transitions and satisfy the Mittag--Leffler condition. This justifies exact augmentation and the passage of perfect pairings. It does not justify an arbitrary inverse limit of the original finite levels.

The hypothesis matching is literal. Book 143 requires the split regular detection clauses, not merely a slogan of “large image”; Book 141 supplies those clauses under the $\ell\geq7$ cyclotomic irreducibility assumptions. Book 152 makes its deep-level freeness conditional on effective diamond torsors and makes its hyperspecial augmentation conditional on integral old--new control. Sections 5.1--5.3 verify these conditions, using the standing saturation assumption from Book 171 and the unit calculation (4.10). Book 146 distinguishes near faithfulness from faithfulness; Proposition 10.1 supplies the stronger nilpotent-sensitive conclusion needed for full equality.

Book 171 requires every generic Hecke branch to lie in the verified Galois attachment and integral local-compatibility range. Section 2.3 explicitly retains that condition at auxiliary level, and Section 6.1 uses it before constructing $R_N\to\mathbb T_N$. The map and the exact acting-image augmentation are not manufactured by patching. Book 173 is a later synthesis that depends on the present theorem and is not used here. Conversely, no theorem from Book 172 is used to justify any hypothesis imported from Book 171, so the dependency is acyclic.

### 16.3 Hypothesis matching

The dependency chain closes as follows:

$$
\begin{array}{c}
\ell\ge7,
\ \bar\rho|_{G_{F(\zeta_\ell)}}\text{ absolutely irreducible}
\\ \Downarrow\\
\text{adequate cyclotomic restricted image}
\\ \Downarrow\\
\text{detecting sets }Q_N\text{ and vanishing auxiliary dual Selmer}
\\ \Downarrow\\
\text{an exact }q\text{-variable absolute source }P\twoheadrightarrow R_N,
\end{array}
\tag{16.1}
$$

while independently

$$
\begin{array}{c}
\text{clean quaternionic stabilizers, saturation, and distinct roots}
\\ \Downarrow\\
M_N\text{ free over }\Lambda_N
\text{ with exact minimal augmentation}
\\ \Downarrow\\
M_\infty\text{ free over }S_\infty.
\end{array}
\tag{16.2}
$$

The two chains meet only after patching. Their equal number of variables makes the scalar-compatible map $P\to\operatorname{End}_{S_\infty}(M_\infty)$ injective. Regularity, depth, and faithfulness then follow. Neither chain assumes the desired equality.

## 17. A hostile audit of the proof

### 17.1 Prime selection and local branches

The auxiliary-prime audit has seven entries.

1. The selected number is the absolute dual Selmer dimension $q$, not a framed or relaxed obstruction number.
2. Every $Q_N$ has exactly $q$ primes and every residue cardinality is $1$ modulo $\ell^N$.
3. Detection, cyclotomic congruence, residual Frobenius, and avoidance are imposed in one compatible finite quotient.
4. Residual Frobenius has two distinct eigenvalues in the coefficient residue field, and an ordering is retained.
5. The new dual local condition is zero, and the localization matrix has full rank, proving (3.10).
6. The automorphic diamond is the projective diagonal ratio, so common scalars act trivially at the source, while the clean stabilizer condition leaves the full nominal group of rank $q$ effective.
7. The determinant and central-character normalization makes (4.10) a unit.

Failure of any entry changes the local functor or leaves a dual class alive.

### 17.2 Patching and numerical counts

The patching audit separates four numerical layers:

| layer | count | reason |
|---|---:|---|
| minimal primal tangent | $q$ | totally real balance |
| auxiliary dual tangent | $0$ | detecting localization matrix |
| diamond variables | $q$ | one fixed-determinant tame character per prime |
| kernel of the patched $q$-variable source action | $0$ | equal-variable rigidity and faithful scalar action |

Finite-level diamond relations number $q$, but they vanish in every fixed shadow; other finite-level relations are retained in the marked quotient ideals. Frame variables are removed by a genuine smooth descent. Padding variables occur with linear relations and contribute neither dimension nor regular parameters to the quotient. The two sources $P$ and $S_\infty$ both have dimension $q+1$, and equal-variable rigidity proves $R_\infty=P$ without double counting or a relation-generation claim.

The arithmetic levels are nonnested. Coherence comes from finite marked shadows, and every inverse-limit exactness claim is applied only to their surjective transition systems.

### 17.3 Support and nilpotents

The proof does not infer faithfulness from an expected dimension, a perfect pairing, or nonzero support. It first proves

$$
S_\infty\hookrightarrow A_\infty,
\quad A_\infty\text{ finite over }S_\infty,
\quad P\twoheadrightarrow A_\infty,
\quad\dim P=\dim S_\infty,
\Longrightarrow P=A_\infty.
\tag{17.1}
$$

Thus $R_\infty=P=A_\infty$ is regular and acts faithfully. Auslander--Buchsbaum then makes $M_\infty$ free of positive rank. Freeness gives full component coverage and sensitivity to every infinitesimal thickening. Faithfulness is not obtained by replacing either ring by its reduction.

### 17.4 Descent and structural conclusions

The final audit checks that:

- ring augmentation recovers the universal minimal functor, using uniqueness of the lifted eigenline;
- module augmentation passes through oriented level using the unit Gram determinant, saturation, and absence of new support;
- acting-algebra augmentation is saturated and recovers the faithful minimal Hecke image;
- auxiliary Hecke-valued representations exist on every generic branch in the retained range, and the ordered-projector calculation puts every diamond in the trace order;
- the images of $z_1,\ldots,z_q$ form a regular sequence on $R_\infty$ and $M_\infty$;
- quotienting $R_\infty=A_\infty$ gives the canonical map $R^{\min}\to\mathbb T^{\min}$;
- module freeness descends without higher Tor terms;
- complete-intersection and Gorenstein claims follow from the displayed regular quotient;
- determinant comparison is made only after the ring equality has been proved independently, and it is not used retroactively in a circular route.

The arithmetic input is already over $F$. Neither residual automorphy nor automorphic descent from a solvable extension is inferred from the existence of the patch.

This closes every possible gap between a patched generic comparison and the integral minimal theorem.

## 18. Conclusion

### 18.1 The established package

The minimal deformation--Hecke problem over a totally real field is balanced because the coefficient-prime local degrees exactly cancel the real places. Adequacy at coefficient primes at least seven turns the common Selmer dimension $q$ into $q$ detecting auxiliary primes at every depth. Their tame characters form finite diamond groups, while definite-quaternion torsors make the corresponding automorphic modules free over the finite group rings.

The changing prime sets do not form a tower. Coherent finite shadows retain exactly the sources, quotient ideals, modules, actions, augmentations, and pairings needed for a limit. The vanishing auxiliary dual Selmer group gives a $q$-variable absolute source, while the diamond algebra has $q$ variables as well. The free patched diamond module makes the scalar-compatible action image finite of full dimension, so equal-variable rigidity kills the entire patched quotient ideal. Thus the patched deformation ring is a regular power-series ring in $q$ variables over $\mathcal O$.

The patched module is free over the diamond power-series algebra and consequently has depth $q+1$ over the deformation ring. Regularity upgrades maximal depth to freeness. This proves full support and faithful action scheme-theoretically, killing nilpotents as well as components. Exact augmentation then yields

$$
\boxed{R^{\min}=\mathbb T^{\min}},
$$

with the common ring finite free, complete intersection, and Gorenstein over $\mathcal O$, and with the minimal automorphic module finite free over it. Perfect pairings, adjoint Hecke actions, and determinant--congruence comparisons descend with the equality. These conclusions hold under the stated clean local and automorphic hypotheses for $\ell\geq7$; the exceptional image at five, scalar auxiliary roots, nonsaturated level change, and nonminimal components remain genuinely outside the theorem.
