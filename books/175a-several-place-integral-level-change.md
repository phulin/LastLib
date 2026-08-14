# Several-Place Integral Level Change

**Status.** This is an unregistered supplemental draft, not a registered volume in the book sequence.

## Contents

1. [The simultaneous problem](#1-the-simultaneous-problem)
   - [1.1 The desired theorem and the honest boundary](#11-the-desired-theorem-and-the-honest-boundary)
   - [1.2 Why a finite set is not an iteration slogan](#12-why-a-finite-set-is-not-an-iteration-slogan)
   - [1.3 The two endpoints](#13-the-two-endpoints)
   - [1.4 Conventions](#14-conventions)
2. [Integral algebra before geometry](#2-integral-algebra-before-geometry)
   - [2.1 Primitive submodules](#21-primitive-submodules)
   - [2.2 Derived reduction over a discrete valuation ring](#22-derived-reduction-over-a-discrete-valuation-ring)
   - [2.3 Minimal complexes over a local ring](#23-minimal-complexes-over-a-local-ring)
   - [2.4 Face algebras and hyper-Tor](#24-face-algebras-and-hyper-tor)
   - [2.5 Determinants and Fitting ideals](#25-determinants-and-fitting-ideals)
   - [2.6 Sums, intersections, and excess classes](#26-sums-intersections-and-excess-classes)
3. [The exact one-place input](#3-the-exact-one-place-input)
   - [3.1 Adjacent levels and the old map](#31-adjacent-levels-and-the-old-map)
   - [3.2 Primary and companion systems](#32-primary-and-companion-systems)
   - [3.3 The semistable correction ledger](#33-the-semistable-correction-ledger)
   - [3.4 What the input does and does not say](#34-what-the-input-does-and-does-not-say)
   - [3.5 The old Gram operator](#35-the-old-gram-operator)
   - [3.6 Regular roots and branch selection](#36-regular-roots-and-branch-selection)
4. [One common global carrier](#4-one-common-global-carrier)
   - [4.1 The multiplicity-duplication error](#41-the-multiplicity-duplication-error)
   - [4.2 The packetwise common carrier](#42-the-packetwise-common-carrier)
   - [4.3 Relative local factors](#43-relative-local-factors)
   - [4.4 The integral relative-factorization criterion](#44-the-integral-relative-factorization-criterion)
   - [4.5 Relative factors and base change](#45-relative-factors-and-base-change)
5. [The coherent global level cube](#5-the-coherent-global-level-cube)
   - [5.1 Vertices and degeneracy legs](#51-vertices-and-degeneracy-legs)
   - [5.2 Cubical signs and the total complex](#52-cubical-signs-and-the-total-complex)
   - [5.3 Construction of the adjoint cube](#53-construction-of-the-adjoint-cube)
   - [5.4 Independence of strict models](#54-independence-of-strict-models)
   - [5.5 The three-place total differential](#55-the-three-place-total-differential)
6. [Two active places](#6-two-active-places)
   - [6.1 The mixed obstruction](#61-the-mixed-obstruction)
   - [6.2 The exact saturation theorem](#62-the-exact-saturation-theorem)
   - [6.3 A split-edge torsion countermodel](#63-a-split-edge-torsion-countermodel)
   - [6.4 What generic concentration proves](#64-what-generic-concentration-proves)
   - [6.5 A field-valued excess-intersection model](#65-a-field-valued-excess-intersection-model)
7. [A finite set of active places](#7-a-finite-set-of-active-places)
   - [7.1 Ordered quotient cubes](#71-ordered-quotient-cubes)
   - [7.2 The exact joint obstruction groups](#72-the-exact-joint-obstruction-groups)
   - [7.3 A sufficient recursive criterion](#73-a-sufficient-recursive-criterion)
   - [7.4 Algebraic order independence](#74-algebraic-order-independence)
   - [7.5 Filtration spectral sequences](#75-filtration-spectral-sequences)
   - [7.6 A pairwise-exact three-cube](#76-a-pairwise-exact-three-cube)
8. [The relative product theorem](#8-the-relative-product-theorem)
   - [8.1 Statement](#81-statement)
   - [8.2 Proof](#82-proof)
   - [8.3 Why the arithmetic premise is new](#83-why-the-arithmetic-premise-is-new)
   - [8.4 Comparison with the direct obstruction route](#84-comparison-with-the-direct-obstruction-route)
9. [The parity-indexed switching cube](#9-the-parity-indexed-switching-cube)
   - [9.1 Its vertices](#91-its-vertices)
   - [9.2 Routed one-place switches](#92-routed-one-place-switches)
   - [9.3 Two-face comparisons](#93-two-face-comparisons)
   - [9.4 Three-face and higher coherence](#94-three-face-and-higher-coherence)
   - [9.5 Normalizing the switch](#95-normalizing-the-switch)
10. [Product residue and the full correction terms](#10-product-residue-and-the-full-correction-terms)
   - [10.1 Why there is no arithmetic multi-fiber](#101-why-there-is-no-arithmetic-multi-fiber)
   - [10.2 Relative component complexes](#102-relative-component-complexes)
   - [10.3 The derived residue defect](#103-the-derived-residue-defect)
   - [10.4 Integral countermodels](#104-integral-countermodels)
   - [10.5 Component Fitting data](#105-component-fitting-data)
11. [Beck--Chevalley coherence and order independence](#11-beck--chevalley-coherence-and-order-independence)
   - [11.1 The formal coherence theorem](#111-the-formal-coherence-theorem)
   - [11.2 Chain-level homotopies](#112-chain-level-homotopies)
   - [11.3 What remains geometric](#113-what-remains-geometric)
   - [11.4 Strict commutation and homotopy commutation](#114-strict-commutation-and-homotopy-commutation)
12. [Simultaneous component support](#12-simultaneous-component-support)
   - [12.1 The all-component theorem](#121-the-all-component-theorem)
   - [12.2 The pointed theorem](#122-the-pointed-theorem)
   - [12.3 Separate projections are insufficient](#123-separate-projections-are-insufficient)
   - [12.4 Local product components and global components](#124-local-product-components-and-global-components)
13. [The canonical pointed carrier](#13-the-canonical-pointed-carrier)
   - [13.1 Torsion-free top cohomology](#131-torsion-free-top-cohomology)
   - [13.2 The adjoint kernel and perfect pairing](#132-the-adjoint-kernel-and-perfect-pairing)
   - [13.3 The pointed occurrence problem](#133-the-pointed-occurrence-problem)
   - [13.4 Structural labels on the pointed carrier](#134-structural-labels-on-the-pointed-carrier)
14. [Joint ray quotients and exact augmentation](#14-joint-ray-quotients-and-exact-augmentation)
   - [14.1 Cross-locally trivial ray characters](#141-cross-locally-trivial-ray-characters)
   - [14.2 Strict product twists](#142-strict-product-twists)
   - [14.3 Fixed-place and auxiliary augmentation](#143-fixed-place-and-auxiliary-augmentation)
   - [14.4 Faithful images do not commute formally with base change](#144-faithful-images-do-not-commute-formally-with-base-change)
   - [14.5 Invariants, coinvariants, and norm](#145-invariants-coinvariants-and-norm)
15. [Finite-set reciprocity](#15-finite-set-reciprocity)
   - [15.1 The exact hypotheses](#151-the-exact-hypotheses)
   - [15.2 Trace descent on the joint carrier](#152-trace-descent-on-the-joint-carrier)
   - [15.3 The deformation-to-Hecke map](#153-the-deformation-to-hecke-map)
   - [15.4 Structural generation and monodromy](#154-structural-generation-and-monodromy)
16. [Two valid simultaneous conclusions](#16-two-valid-simultaneous-conclusions)
   - [16.1 The all-component conclusion](#161-the-all-component-conclusion)
   - [16.2 The pointed conclusion](#162-the-pointed-conclusion)
   - [16.3 The exact logical separation](#163-the-exact-logical-separation)
   - [16.4 Proof-strategy map](#164-proof-strategy-map)
17. [Diagnostic examples](#17-diagnostic-examples)
   - [17.1 Two primitive planes with a nonprimitive sum](#171-two-primitive-planes-with-a-nonprimitive-sum)
   - [17.2 A residual class created by top torsion](#172-a-residual-class-created-by-top-torsion)
   - [17.3 A diagonal ray image](#173-a-diagonal-ray-image)
   - [17.4 A faithful image lost after specialization](#174-a-faithful-image-lost-after-specialization)
18. [The first unresolved arithmetic theorem](#18-the-first-unresolved-arithmetic-theorem)
   - [18.1 Exact statement of the blocker](#181-exact-statement-of-the-blocker)
   - [18.2 Consequences of resolving it](#182-consequences-of-resolving-it)
   - [18.3 Further independent geometric obligations](#183-further-independent-geometric-obligations)
   - [18.4 Exhaustion of the available comparison theorems](#184-exhaustion-of-the-available-comparison-theorems)
19. [Final synthesis](#19-final-synthesis)

## 1. The simultaneous problem

### 1.1 The desired theorem and the honest boundary

Let $P$ be a finite set of finite places. At each $v\in P$ there are two adjacent levels, an old map with two degeneracy legs, an adjoint map, a primary integral coefficient system, a companion coefficient system, and a semistable comparison carrying normalization, component, branch, and conductor information. The one-place theory proves strong integral statements for each of these data separately.

The several-place goal is to change the level at every member of $P$ at once. The desired output is not merely a list of one-place conclusions. It is one global cubical object with all of the following properties:

- the global automorphic multiplicity module occurs once;
- every face map is defined on the same routed component carrier;
- the primary and companion cubes are strict adjoints with the cubical signs included;
- the primary total complex is concentrated in top degree and has finite projective top cohomology over the declared face algebra;
- derived base change to every character and every auxiliary augmentation has no unrecorded positive Tor;
- the parity-indexed inner-form switches commute by integral two-face homotopies satisfying three-face coherence;
- every Néron component term, normalized-branch Smith term, conductor term, and coefficient-one extreme residue is carried through those homotopies;
- the resulting module has support on the required product components; and
- the faithful Hecke image carries one order-valued Galois representation satisfying all local conditions simultaneously.

There is presently no deduction of this complete arithmetic statement from the one-place inputs alone. The first obstruction is already visible for two places: even when all four one-place old maps are split injections and the rational total complex is exact below top degree, the sum of the two upper old images can fail to be primitive. That failure creates residual middle cohomology. It is not removed by generic packet factorization, separate support, or torsion-freeness of a top quotient in an unrelated complex.

This volume therefore does two things. It proves the complete algebraic reduction from an actual global cube, identifies every formal consequence, and constructs the smaller torsion-free pointed carrier that is available without mixed exactness. It also identifies, without renaming it as a hypothesis, the first arithmetic theorem still required for a full simultaneous result. No unconditional several-place arithmetic theorem is asserted where the necessary geometry has not been constructed.

### 1.2 Why a finite set is not an iteration slogan

Suppose a theorem changes the level at $v$. After applying it, the ambient lattice, its companion, the faithful Hecke order, the selected component, and the spectator data have changed. A theorem at a second place $w$ can be applied next only after its complete input has been verified on that new carrier. Thus a validated chain is possible, but it is a chain of newly verified one-place problems. It is not an induction on the cardinality of $P$.

The simultaneous problem is different. It asks for a single object containing every intermediate carrier and every comparison among them. The first new datum is the square

$$
\begin{array}{ccc}
M_{00}&\longrightarrow&M_{10}\\
\downarrow&&\downarrow\\
M_{01}&\longrightarrow&M_{11},
\end{array}
$$

where each arrow abbreviates a pair of degeneracy maps. The square can commute strictly while its total complex has middle cohomology. The obstruction is the excess intersection of the two old images in $M_{11}$. No statement about either edge alone determines that intersection.

For three places, the problem is not exhausted by its six two-faces. After quotienting in one direction, the next old map acts on a new quotient; after two quotients, the third acts on a double-new quotient. Pairwise injectivity on the original vertices says nothing about these induced maps. The exact obstruction is the lower cohomology of the entire residual total cube.

### 1.3 The two endpoints

There are two useful endpoints, and they must remain distinct.

The **all-component endpoint** asks for a finite projective top module whose support is the entire product deformation space, or at least every named irreducible component. It requires mixed exactness, enough product-residue comparison to identify all component labels, and joint boundary witnesses of maximal depth.

The **pointed endpoint** starts with one characteristic-zero point $x$. It forms the torsion-free quotient of the top cohomology of the actual finite cube and asks only that the single global component through $x$ occur in its support. This is strictly weaker. It does not imply mixed exactness, does not produce a ring equality, and does not cover the other product components. It is nevertheless sufficient to factor $x$ through the faithful Hecke image.

The smaller endpoint is not a defective version of the larger one. It is the logically minimal carrier for a pointwise automorphy argument. Conversely, separate one-place occurrence is weaker even than the pointed endpoint, because the latter concerns one component carrying the complete tuple of local labels.

### 1.4 Conventions

Throughout, $\ell$ is an odd prime. Let $\mathcal O$ be a complete discrete valuation ring with uniformizer $\varpi$, fraction field $E$, and residue field $k$ of characteristic $\ell$. More generally, face coefficients may be carried by a complete noetherian local $\mathcal O$-algebra $(A,\mathfrak n,k)$.

All complexes are cochain complexes. A one-place incidence complex occupies degrees $0$ and $1$. For $r=|P|$, the total primary complex occupies degrees $0$ through $r$, and the desired joint-new module occurs in degree $r$. The companion is normalized so that its surviving norm module occurs in degree zero. Derived tensor products and derived Hom are written $\otimes^L$ and $R\operatorname{Hom}$.

At a good place, geometric Frobenius has polynomial

$$
X^2-T_vX+q_vS_v.
$$

Every adjoint formula retains $S_v$ and the inverse central character. No forward operator is called self-adjoint unless an actual self-duality and normalization prove that assertion.

## 2. Integral algebra before geometry

### 2.1 Primitive submodules

Let $L$ be a finite free $\mathcal O$-module and let $U\subseteq L$ be a submodule. The following conditions are equivalent:

1. $L/U$ is torsion-free;
2. $U=(U\otimes_{\mathcal O}E)\cap L$ inside $L\otimes_{\mathcal O}E$;
3. $U$ is a direct summand of $L$;
4. every nonzero Smith invariant of the inclusion $U\hookrightarrow L$ is a unit.

When they hold, $U$ is called **primitive** or **saturated**. The equivalence follows from Smith normal form. If the inclusion is represented in suitable bases by

$$
\operatorname{diag}(\varpi^{a_1},\ldots,\varpi^{a_s},0,\ldots,0),
$$

then the quotient has torsion exactly when some $a_i>0$.

Primitivity is not additive. Two direct summands $U,V\subseteq L$ can have a nonprimitive sum. Indeed, the quotient $L/(U+V)$ measures a relative position, not an invariant of either inclusion separately. This elementary fact is the algebraic core of mixed level change.

For later use, note the identity

$$
\operatorname{Tor}_1^{\mathcal O}(L/(U+V),k)
\simeq (L/(U+V))[\varpi].
\tag{2.1}
$$

Thus $U+V$ is primitive if and only if the left side of (2.1) vanishes.

### 2.2 Derived reduction over a discrete valuation ring

Let $C$ be a bounded complex of finite free $\mathcal O$-modules. Derived and ordinary reduction agree at the level of complexes, but cohomology does not commute with reduction. There is a canonical short exact sequence

$$
0\longrightarrow H^i(C)\otimes_{\mathcal O}k
\longrightarrow H^i(C\otimes_{\mathcal O}k)
\longrightarrow
\operatorname{Tor}_1^{\mathcal O}(H^{i+1}(C),k)
\longrightarrow0.
\tag{2.2}
$$

The sequence need not split canonically. It follows by tensoring the exact sequences of cycles and boundaries, or from the two-line hyper-Tor spectral sequence over a ring of global dimension one.

Formula (2.2) explains how a residual class can appear even when integral lower cohomology vanishes. Torsion in the next cohomological degree contributes a Tor class one degree lower. This is precisely what happens when the top joint-new quotient has $\varpi$-torsion.

Generic concentration gives only

$$
H^i(C)\otimes_{\mathcal O}E=0
\quad (i<r),
$$

so the lower $H^i(C)$ are $\varpi$-power torsion. It does not make them zero, and it does not make $H^r(C)$ torsion-free. Both defects are invisible over $E$.

### 2.3 Minimal complexes over a local ring

Every bounded complex of finite free modules over a local ring is homotopy equivalent to a direct sum of a contractible complex and a **minimal complex**, meaning one whose differentials have entries in the maximal ideal. The construction repeatedly splits a unit entry from a differential. A unit entry produces a summand

$$
[A\xrightarrow{1}A],
$$

which is contractible.

In a minimal complex, every differential becomes zero after tensoring with $k$. Hence its residual cohomology is simply its graded residual module.

**Theorem 2.1 (top-degree criterion).** Let $(A,\mathfrak n,k)$ be local and let $C$ be a perfect complex represented by finite free modules in degrees $0,\ldots,r$. Then the following are equivalent:

1. $H^i(C\otimes_A^Lk)=0$ for every $i<r$;
2. $C$ is homotopy equivalent to a finite free $A$-module $N$ placed in degree $r$.

In this case $N=H^r(C)$, it is finite free, and for every $A$-algebra $B$,

$$
C\otimes_A^LB\simeq(N\otimes_AB)[-r],
\qquad
\operatorname{Tor}_j^A(N,B)=0\quad(j>0).
\tag{2.3}
$$

**Proof.** Replace $C$ by its minimal summand. After reduction, all differentials vanish. The residual cohomology in degree $i$ is therefore the residual degree-$i$ module. Vanishing for $i<r$ forces those modules to be zero by Nakayama's lemma. Only the degree-$r$ free module remains. The converse and (2.3) are immediate. $\square$

This theorem is stronger than generic concentration. Its hypothesis is residual derived concentration over the actual face algebra.

### 2.4 Face algebras and hyper-Tor

When $A\ne\mathcal O$, coefficient reduction is governed by the spectral sequence

$$
E_2^{-p,q}
=\operatorname{Tor}_p^A(H^q(C),k)
\Longrightarrow H^{q-p}(C\otimes_A^Lk).
\tag{2.4}
$$

The terms with $p>1$ need not vanish. Even if every $H^q(C)$ is torsion-free over $\mathcal O$, it may have positive Tor over $A$. Therefore coefficient-DVR saturation is necessary but not sufficient for concentration over a larger face algebra.

For example, let $A=k[[t_1,t_2]]$ and let $N=k=A/(t_1,t_2)$. The Koszul resolution gives

$$
\operatorname{Tor}_1^A(k,k)\simeq k^2,
\qquad
\operatorname{Tor}_2^A(k,k)\simeq k.
$$

No statement about torsion over a coefficient DVR sees these groups. In a simultaneous level problem, the analogue is residual hyper-Tor over the algebra carrying character, type, or auxiliary variables.

There is also an exact base-change test once integral concentration is known. If, without
assuming flatness of $N$, one has

$$
C\simeq N[-r],
$$

then for every $A$-algebra $B$,

$$
H^{r-j}(C\otimes_A^LB)
\simeq\operatorname{Tor}_j^A(N,B)
\qquad(j\ge0).
\tag{2.4a}
$$

Thus ordinary base change at this particular $B$ is exact precisely when the positive Tor
groups in (2.4a) vanish. Exactness for every $A$-algebra is equivalent to flatness of $N$;
when $N$ is finite over a noetherian local ring, finite presentation then makes $N$ finite
free. Coefficient-DVR torsion-freeness is the special case $A=\mathcal O$ and does not test
flatness over a larger face algebra.

### 2.5 Determinants and Fitting ideals

When a map between finite free modules is square, its determinant measures the entire defect only when the cokernel has the expected finite support. For a general map

$$
f:A^m\longrightarrow A^n,
$$

the correct invariant is the family of determinantal ideals. The ideal generated by the $j$-by-$j$ minors is denoted

$$
I_j(f).
$$

If $Q=\operatorname{coker}f$, then

$$
\operatorname{Fitt}_A^{n-j}(Q)=I_j(f).
\tag{2.5}
$$

Over a discrete valuation ring, Smith normal form diagonalizes $f$. If its nonzero diagonal entries are $\varpi^{a_1},\ldots,\varpi^{a_s}$, then the torsion length of the cokernel is

$$
\sum_{i=1}^sa_i.
\tag{2.6}
$$

The quotient is torsion-free exactly when all $a_i=0$. Thus the mixed-saturation theorem can be expressed as a maximal-minor statement: the map whose image is $U+V$ must have a unit maximal minor after its generic rank has been fixed.

Fitting ideals behave well under base change at the level of presentations:

$$
\operatorname{Fitt}_A^i(Q)B
=\operatorname{Fitt}_B^i(Q\otimes_AB).
\tag{2.7}
$$

But the module presented after base change can acquire extra Tor from a preceding exact sequence. Therefore (2.7) does not say that cohomology commutes with base change. In a cubical complex, one must first know that the relevant boundary presentation remains exact in the preceding degree.

This distinction separates three invariants that often look similar:

- the Fitting ideal of the top joint-new quotient;
- the determinant of a one-place old Gram operator; and
- the Fitting ideal of a component or branch correction module.

They live in different exact sequences. Equality among them is a comparison theorem, not a notational convention.

### 2.6 Sums, intersections, and excess classes

Let $U,V$ be submodules of a finite free module $L$. There is an exact sequence

$$
0\longrightarrow U\cap V
\xrightarrow{x\mapsto(x,-x)}
U\oplus V
\xrightarrow{(u,v)\mapsto u+v}
U+V\longrightarrow0.
\tag{2.8}
$$

Suppose a lower cubical image $J$ maps into both $U$ and $V$. Then the middle cohomology of the incidence complex

$$
J\longrightarrow U\oplus V\longrightarrow L
\tag{2.9}
$$

is

$$
(U\cap V)/J,
\tag{2.10}
$$

and its top cohomology is $L/(U+V)$. The intersection quotient measures an **excess overlap**; torsion in the sum quotient measures a **failure of primitive spanning**.

These defects are related after reduction but are not identical integrally. Under the split-edge and generic-concentration hypotheses of Theorem 6.1, (2.10) is both torsion-free and torsion, so it vanishes. The only remaining residual middle class then comes from top torsion through (2.2). Without those hypotheses, an actual integral excess class can survive in (2.10).

Over a field, dimensions give

$$
\dim(U+V)+\dim(U\cap V)=\dim U+\dim V.
\tag{2.11}
$$

Over a discrete valuation ring, ranks satisfy the same equality, but lattice indices carry additional information. The generic ranks can therefore be correct while the sum has a nontrivial finite index in its saturation. Several-place level change is precisely where that hidden index first appears.

## 3. The exact one-place input

### 3.1 Adjacent levels and the old map

Fix one active place $v$. Let $M_{0,v}$ be the hyperspecial carrier and $M_{1,v}$ the oriented carrier, with all other places held at one actual spectator tuple. The two adjacent vertices in the local building give degeneracy maps

$$
d_{v,0},d_{v,1}:M_{0,v}\longrightarrow M_{1,v}.
$$

Write

$$
d_v=(d_{v,0},d_{v,1}):M_{0,v}^{\oplus2}\longrightarrow M_{1,v}.
\tag{3.1}
$$

The one-place primary complex is

$$
C_v^+=[M_{0,v}^{\oplus2}\xrightarrow{d_v}M_{1,v}].
\tag{3.2}
$$

The exact one-place input needed below says, for each actual spectator tuple and each coefficient shadow under consideration, that the terms are finite projective over one declared local base, that $d_v$ is a split injection, and that its cokernel $N_v$ is finite projective. Equivalently,

$$
C_v^+\simeq N_v[-1].
\tag{3.3}
$$

The point of specifying the spectator tuple is that $N_v$ is already a global quotient. After another place has been changed, it is not automatically the same coefficient system to which the original one-place theorem applied.

### 3.2 Primary and companion systems

Let $M_{0,v}^-$ and $M_{1,v}^-$ be the companion carriers. They are not informal copies of the primary carriers. Their central characters, diamonds, local type labels, and forward operators are transported by the declared adjoint involution.

Assume perfect pairings

$$
\langle\ ,\ \rangle_{i,v}:
M_{i,v}^+\times M_{i,v}^-\longrightarrow A
\qquad(i=0,1)
\tag{3.4}
$$

and let $d_v^*$ be the transpose of $d_v$ under these pairings. The companion complex is normalized as

$$
C_v^-=[M_{1,v}^-\xrightarrow{d_v^*}(M_{0,v}^-)^{\oplus2}].
\tag{3.5}
$$

If (3.3) holds and the pairings are perfect, then

$$
C_v^-\simeq N_v^\vee,
\qquad
N_v^\vee=\operatorname{Hom}_A(N_v,A),
\tag{3.6}
$$

with the companion in degree zero. This is a consequence of derived duality, not a second independent old--new theorem.

### 3.3 The semistable correction ledger

The old map alone is not the full one-place comparison. At a semistable place the routed residue object contains at least the following pieces:

- the coefficient-one extreme residue map between the two extreme graded terms;
- the normalization middle term, which records the two branches above a node;
- the graph lattice and its monodromy pairing;
- the Néron component module, obtained as the appropriate cokernel of that pairing;
- the normalized-branch Smith module, which in the standard two-branch normalization is governed by the cokernel of an operator of the form

  $$
  1-(F_v^*)^2;
  $$

- the conductor or Kummer term that distinguishes zero monodromy, line-special behavior, and the chosen scalar-twist branch;
- the component route identifying the correct connected block before and after the inner-form switch; and
- the adjoint maps on the companion coefficient system.

These terms are integral. A torsion component group or branch Smith module can be invisible after tensoring with $E$ and still support a nonzero derived comparison class.

### 3.4 What the input does and does not say

The one-place input proves that each raw edge of a global cube is well behaved when its other coordinates are fixed at an actual permissible tuple. It can prove saturation of the one-place old image, freeness of the one-place new quotient, exact type incidence, perfect adjunction, and a routed one-place residue comparison.

It does not prove any of the following:

- primitivity of a sum of old images at a vertex with two or more active coordinates;
- injectivity of a degeneracy map after first passing to a quotient-new module in another direction;
- vanishing of the hyper-Tor groups of the full cube over a common face algebra;
- existence of an integral comparison between the two composites of distinct inner-form switches;
- coherence of such comparisons on a three-face;
- occurrence on a specified product component; or
- compatibility of a torsion-free top quotient with a nonflat character specialization.

These are genuinely several-place statements.

### 3.5 The old Gram operator

Let $r_v$ be the reverse correspondence from oriented level to the two hyperspecial copies. With the right-translation normalization, the old Gram operator has the form

$$
G_v=r_vd_v
=
\begin{pmatrix}
q_v+1&T_v\\
S_v^{-1}T_v&q_v+1
\end{pmatrix}.
\tag{3.7}
$$

Its determinant is

$$
D_v=(q_v+1)^2-S_v^{-1}T_v^2.
\tag{3.8}
$$

If $D_v$ is a unit on the localized source, then $G_v$ is invertible and

$$
e_{\mathrm{old},v}
=d_vG_v^{-1}r_v
\tag{3.9}
$$

is an integral idempotent. It acts as the identity on $\operatorname{im}d_v$ and has kernel $\ker r_v$. Consequently

$$
M_{1,v}
=\operatorname{im}d_v\oplus\ker r_v.
\tag{3.10}
$$

This proves injectivity and saturation of the old map in the unit-determinant regime. It still does not show that $\ker r_v$ has no support at the selected maximal ideal. Absence of localized new support is a separate occurrence statement.

At a regular auxiliary place, let $\alpha_v,\beta_v$ be the residual roots of

$$
Y^2-T_vY+q_vS_v.
\tag{3.11}
$$

If $q_v\equiv1\pmod\ell$, then

$$
S_vD_v
\equiv
-(\alpha_v-\beta_v)^2
\pmod{\mathfrak m}.
\tag{3.12}
$$

Thus distinct nonzero roots make $D_v$ a unit. This is a one-place splitness calculation. It does not imply that two old idempotent images at different places have primitive sum.

For two places, the product of the two one-place Gram determinants controls the individual splittings. The index of $U+V$ in its saturation is an additional mixed determinant. The rank-eight countermodel has both one-place Gram determinants equal to units while the mixed index is $\varpi^2$.

There is one important strengthening. If the two canonical old projectors on the common top
vertex have been proved to commute and their product has image equal to the lower composite
old image, then their sum is primitive by Corollary 6.2 below. This compatibility is stronger
than invertibility of the two Gram matrices separately. The countermodel in Section 6.3 has
unit Gram operators for suitable separate retractions, but its associated old projectors do
not commute.

### 3.6 Regular roots and branch selection

Assume the roots in (3.11) lift to $\alpha_v,\beta_v$ in a complete local coefficient algebra and that

$$
\alpha_v-\beta_v\in A^\times.
$$

On any module on which (3.11) annihilates the oriented operator $U_v$, the projectors are

$$
e_{\alpha_v}
=\frac{U_v-\beta_v}{\alpha_v-\beta_v},
\qquad
e_{\beta_v}
=\frac{U_v-\alpha_v}{\beta_v-\alpha_v}.
\tag{3.13}
$$

They are integral, orthogonal, and sum to one. For a finite set $P$, the operators at distinct places commute, so the products

$$
e_{\varepsilon}
=\prod_{v\in P}e_{\varepsilon_v},
\qquad
\varepsilon_v\in\{\alpha_v,\beta_v\},
\tag{3.14}
$$

split the common degeneracy source into $2^{|P|}$ refined factors.

This source splitting is genuinely simultaneous and useful. It still does not identify the image of each refined factor with a primitive summand of the top oriented module. Injectivity of the aggregate old map is needed first, and primitivity of sums remains a separate question.

Adjunction transports the selected root to the companion root. In the standard normalization,

$$
U_v^*=q_vS_vU_v^{-1}
$$

on an invertible old factor, so the adjoint of the $\alpha_v$-branch is the $\beta_v$-branch because

$$
\alpha_v\beta_v=q_vS_v.
\tag{3.15}
$$

For several places the companion refinement is the coordinatewise adjoint tuple. This is why the companion cube cannot be replaced by a second copy carrying the primary tuple.

## 4. One common global carrier

### 4.1 The multiplicity-duplication error

Let $\Pi$ be a characteristic-zero packet occurring in a curve carrier. Its cohomological block has a global multiplicity factor $W_\Pi$, a spectator factor away from $P$, and local invariant factors at the active places. It has the form

$$
H^1[\Pi]
\simeq
W_\Pi\otimes P_\Pi^P\otimes
\bigotimes_{v\in P}\Pi_v^{K_{v,\epsilon_v}}.
\tag{4.1}
$$

The two-dimensional factor $W_\Pi$ occurs once. If one tensors the full global one-place complexes over the coefficient field, one obtains $W_\Pi^{\otimes |P|}$. For two places and $\dim W_\Pi=2$, this has rank four, whereas the actual simultaneous block has global multiplicity rank two.

Thus the formula

$$
C_P\stackrel{?}{\simeq}
\bigotimes_{v\in P}C_v^{\mathrm{global}}
$$

is false even at the level of ranks. A simultaneous theory must remove the common global factor before taking local products and reinsert it exactly once.

### 4.2 The packetwise common carrier

Define

$$
G_{\Pi,P}=W_\Pi\otimes P_\Pi^P.
\tag{4.2}
$$

After a finite extension of $E$ which splits the relevant finite packet blocks, let
$D_{\Pi,v}$ be the genuinely local two-term incidence complex formed from the two local
invariant spaces and their degeneracy map. Then the actual packet block of the global level
cube has the generic form

$$
C_P[\Pi]_E
\simeq
G_{\Pi,P}\otimes_E
\operatorname{Tot}\left(\boxtimes_{v\in P}D_{\Pi,v}\right).
\tag{4.3}
$$

The level map in direction $v$ acts as the identity on $G_{\Pi,P}$ and on every local factor away from $v$. Formula (4.3) proves generic order independence and generic top-degree concentration when every local complex is concentrated in degree one. It is the correct packetwise relative factorization.

### 4.3 Relative local factors

An integral relative factorization requires more than the packetwise decomposition. One must construct:

1. one common coefficient algebra $A$;
2. one finite projective global carrier $G_P$ over $A$;
3. for every $v\in P$, a perfect local-factor complex $L_v$ over the same $A$;
4. an actual quasi-isomorphism

   $$
   C_P\xrightarrow{\sim}
   G_P\otimes_A^L\bigotimes_{v\in P}^LL_v;
   \tag{4.4}
   $$

5. compatibility of (4.4) with the primary--companion pairings, component routes, coefficient changes, and every face inclusion.

It is not enough that the different objects happen to be projective over different rings. Nor is perfectness over $\mathcal O$ enough to identify a relative tensor product over a component algebra. Cross-Tor is measured over the common base actually used in (4.4).

### 4.4 The integral relative-factorization criterion

Suppose (4.4) has been constructed and suppose

$$
L_v\simeq N_v[-1]
$$

with $G_P$ and every $N_v$ finite projective over the same $A$. Associativity of derived tensor products requires no projectivity. Here the projectivity hypotheses identify the derived product with the ordinary tensor product and give

$$
C_P\simeq
\left(G_P\otimes_A\bigotimes_{v\in P}N_v\right)[-|P|].
\tag{4.5}
$$

Hence the total complex is concentrated in top degree, its top module is finite projective,
every derived specialization is represented by ordinary base change and remains concentrated
in top degree, and the result is independent of the order of the places.

This is a complete proof once (4.4) exists. The unresolved arithmetic issue is the construction of (4.4) for the actual integral automorphic cube. It cannot be obtained by tensoring full one-place global complexes, because those contain the duplicated factor just exhibited.

### 4.5 Relative factors and base change

The word “relative” carries three requirements.

First, all local factors must be modules over the same algebra. If $L_v$ is naturally defined over $A_v$ and $L_w$ over $A_w$, then a tensor over $\mathcal O$ forgets the incidence relations connecting their component parameters. One must construct a common algebra $A$ together with compatible maps from the $A_v$ and an identification of the pulled-back factors.

Second, the common global carrier must be removed functorially. A decomposition at one generic packet does not automatically glue over a local order in which several packets meet. The integral object $G_P$ must retain those congruence relations while excluding the active local factors. This is stronger than matching ranks on every generic branch.

Third, the relative factorization, together with its routes and adjunction, must be formulated over $A$ so that it can be transported under the coefficient changes used later. If $B$ is a nonflat quotient of $A$, the resulting square is

$$
\begin{array}{ccc}
C_P&\longrightarrow&G_P\otimes_A^L\bigotimes_v^LL_v\\
\downarrow&&\downarrow\\
C_P\otimes_A^LB&\longrightarrow&
(G_P\otimes_A^LB)\otimes_B^L
\bigotimes_v^L(L_v\otimes_A^LB).
\end{array}
\tag{4.6}
$$

Derived extension of scalars is symmetric monoidal. Consequently, for arbitrary derived
$A$-objects $G_P$ and $L_v$, there is a canonical associative identification

$$
\left(G_P\otimes_A^L\bigotimes_v^LL_v\right)\otimes_A^LB
\simeq
(G_P\otimes_A^LB)\otimes_B^L
\bigotimes_v^L(L_v\otimes_A^LB).
\tag{4.7}
$$

Thus the bottom map in (4.6) is a quasi-isomorphism whenever the top map is, without any
projectivity hypothesis; extension of scalars also transports the declared routes and
adjunction. Projectivity enters only when one wants to replace the derived tensors by
ordinary tensors and keep the specialization concentrated in the expected degree. Without
the relevant flatness or Tor-independence, positive Tor records the failure of that underived
concentration or exact specialization. It does not obstruct derived base change or its
associativity.

The success of the common-carrier construction is now visible. It avoids the multiplicity error by placing $G_P$ outside the local tensor, records cross-Tor over one declared base rather than hiding it, and turns every later specialization into an instance of derived base change. None of these benefits is available from a tensor product of full global one-place complexes.

## 5. The coherent global level cube

### 5.1 Vertices and degeneracy legs

Fix a prime-to-$P$ global level, one joint coefficient descent, and a component union stable under every route that will occur. For a subset $I\subseteq P$, let $M_I^+$ be the primary carrier with oriented level at the places in $I$ and hyperspecial level at the places outside $I$. All spectator levels outside $P$ are kept fixed.

For $v\notin I$, the two degeneracy legs give

$$
d_{I,v,0},d_{I,v,1}:M_I^+\longrightarrow M_{I\cup\{v\}}^+.
\tag{5.1}
$$

The adelic elements defining changes at distinct places commute. Forgetful level maps are transitive. Therefore, after the joint coefficient descent and component routing have actually been chosen, the diagrams formed by the maps in (5.1) commute. This constructs the underlying Boolean level cube.

The phrase “after” is important. Separate coefficient covers need not have an effective product descent, and separately stable component unions need not have a common stable refinement. The formal level tower constructs the cube only on a carrier on which all maps are simultaneously defined.

### 5.2 Cubical signs and the total complex

Choose an ordering $P=\{v_1,\ldots,v_r\}$. In cubical degree $a$, put

$$
C_P^{+,a}
=\bigoplus_{\substack{I\subseteq P\\|I|=a}}
(M_I^+)^{\oplus 2^{r-a}}.
\tag{5.2}
$$

The multiplicity $2^{r-a}$ records the degeneracy choices in the directions not yet changed. The differential is the signed sum of the coordinate degeneracy maps. For an inclusion $I\subset I\cup\{v_j\}$, the sign is

$$
(-1)^{\#\{v_i\in I:i<j\}}.
\tag{5.3}
$$

Because distinct coordinate maps commute, every two-face appears twice in the square of the differential, with opposite signs. Thus $d^2=0$.

Changing the ordering changes the displayed signs but not the object in the derived category. A permutation $\sigma$ acts on the summand indexed by $I$ by the sign of the induced permutation of the ordered set $I$, together with the evident permutation of the degeneracy-copy labels in the complementary directions. These maps give a canonical isomorphism between the two total complexes and satisfy the group law.

### 5.3 Construction of the adjoint cube

For every vertex choose the actual companion carrier $M_I^-$ and a perfect pairing

$$
M_I^+\times M_I^-\longrightarrow A.
\tag{5.4}
$$

Let the reverse correspondence on the companion be the adjoint of each degeneracy leg. Taking the transpose of the signed primary differential constructs the companion total complex. With the normalization that one adjoint shift is introduced in each direction, there is an isomorphism

$$
C_P^-
\simeq
R\operatorname{Hom}_A(C_P^+,A)[-r].
\tag{5.5}
$$

If $C_P^+\simeq N_P[-r]$ with $N_P$ finite projective, then

$$
C_P^-\simeq N_P^\vee
\tag{5.6}
$$

in degree zero. Thus a coherent adjoint cube needs no second mixed-vanishing theorem. Without the strict compatibility in (5.5), separate perfect pairings on the faces do not imply (5.6).

### 5.4 Independence of strict models

The derived totalization of a finite cube is invariant under objectwise quasi-isomorphism. If two cellular or cohomological models represent the same routed cube and the comparison maps commute with all face maps up to coherent homotopy, their total complexes are quasi-isomorphic.

This formal invariance does not create the coherent homotopies. It says only that once they have been supplied, the choice of strict representative is harmless. In particular, replacing separate one-place models by a common subdivision is legitimate only after every route has been represented on that subdivision.

### 5.5 The three-place total differential

Let $P=\{u,v,w\}$ in that order. The total complex has the form

$$
M_{\varnothing}^{\oplus8}
\xrightarrow{d^0}
\left(
M_u^{\oplus4}\oplus
M_v^{\oplus4}\oplus
M_w^{\oplus4}
\right)
\xrightarrow{d^1}
\left(
M_{uv}^{\oplus2}\oplus
M_{uw}^{\oplus2}\oplus
M_{vw}^{\oplus2}
\right)
\xrightarrow{d^2}
M_{uvw}.
\tag{5.7}
$$

Suppress the two degeneracy-leg indices and write $d_u,d_v,d_w$ for the coordinate maps. Then

$$
d^0=
\begin{pmatrix}
d_u\\ d_v\\ d_w
\end{pmatrix},
\tag{5.8}
$$

while, with the displayed ordering of degree-one and degree-two summands,

$$
d^1=
\begin{pmatrix}
-d_v&d_u&0\\
-d_w&0&d_u\\
0&-d_w&d_v
\end{pmatrix},
\tag{5.9}
$$

and

$$
d^2=
\begin{pmatrix}
d_w&-d_v&d_u
\end{pmatrix}.
\tag{5.10}
$$

Commutation of coordinate maps gives $d^1d^0=0$ and $d^2d^1=0$. The signs are not decorative: without them, each two-face contributes twice rather than canceling.

If one first quotients in direction $u$, the remaining complex is a square on the $u$-new quotients. Its middle obstruction is not any of the original face obstructions unless quotienting in $u$ is exact and compatible with those faces. This concrete matrix is a useful reminder that the third direction sees a derived quotient of the first two.

## 6. Two active places

### 6.1 The mixed obstruction

Let $P=\{v,w\}$. Write $M_{ab}$ for the four finite projective $A$-modules at the vertices, with $a$ recording the $v$-level and $b$ the $w$-level. The total primary complex is

$$
C_{v,w}^+:
M_{00}^{\oplus4}
\longrightarrow
M_{10}^{\oplus2}\oplus M_{01}^{\oplus2}
\longrightarrow M_{11}.
\tag{6.1}
$$

Assume in this section that all four raw aggregate edges are split injections over $A$.
Their reductions are therefore injective, so taking cohomology first in either coordinate
leaves only the corresponding cokernel row.

Reduce modulo the maximal ideal and first take cokernels in the $v$-direction:

$$
N_{v\mid b,k}
=\operatorname{coker}\left(
M_{0b,k}^{\oplus2}\longrightarrow M_{1b,k}
\right),
\qquad b=0,1.
\tag{6.2}
$$

The $w$-maps induce

$$
\overline d_{w\mid v}:
N_{v\mid0,k}^{\oplus2}\longrightarrow N_{v\mid1,k}.
\tag{6.3}
$$

Define

$$
\operatorname{Ob}_{v,w}
=\ker\overline d_{w\mid v}.
\tag{6.4}
$$

Filtering (6.1) first in the $v$-direction gives

$$
H^1(C_{v,w}^+\otimes_A^Lk)
\simeq\operatorname{Ob}_{v,w}.
\tag{6.5}
$$

The opposite filtration gives the same group with $v$ and $w$ reversed. In intersection form,

$$
\operatorname{Ob}_{v,w}
\simeq
\frac{\operatorname{im}(d_v)\cap\operatorname{im}(d_w)}
{\operatorname{im}(d_vd_w)}
\quad\text{inside }M_{11,k}.
\tag{6.6}
$$

The one-place theorem proves injectivity before the cokernel in (6.2) is taken. It does not prove injectivity of (6.3), whose coefficients are already a global quotient-new module.

### 6.2 The exact saturation theorem

The coefficient-DVR form is especially sharp.

**Theorem 6.1 (two-place mixed saturation).** Let $A=\mathcal O$ and retain the finite
free vertex modules above. Assume all four aggregate edge maps of (6.1) are split injections.
In $M_{11}$ put

$$
U=\operatorname{im}(d_{v\mid1}),
\qquad
V=\operatorname{im}(d_{w\mid1}),
\qquad
L=\operatorname{im}(d_vd_w)=\operatorname{im}(d_wd_v).
\tag{6.7}
$$

Assume $C_{v,w}^+\otimes_{\mathcal O}E$ has no cohomology below degree two. Then

$$
H^0(C_{v,w}^+)=H^1(C_{v,w}^+)=0,
\qquad
H^2(C_{v,w}^+)=Q_{v,w}:=M_{11}/(U+V),
\tag{6.8}
$$

and there are canonical isomorphisms

$$
\operatorname{Ob}_{v,w}
\simeq
\operatorname{Tor}_1^{\mathcal O}(Q_{v,w},k)
\simeq Q_{v,w}[\varpi].
\tag{6.9}
$$

Consequently the following are equivalent:

1. $\operatorname{Ob}_{v,w}=0$;
2. $Q_{v,w}$ is torsion-free;
3. $U+V\subseteq M_{11}$ is primitive;
4. $C_{v,w}^+$ is homotopy equivalent to a finite free module in degree two.

**Proof.** The degree-one cohomology is $(U\cap V)/L$. The lower and upper edge splittings make $L$ a direct summand of both $U$ and $V$. Hence $(U\cap V)/L$ is torsion-free: if $\varpi x\in L$ and $x\in U\cap V$, primitivity of $L$ in $U$ gives $x\in L$. Generic concentration makes the same module torsion, so it vanishes. Degree-zero vanishing follows from either first split edge. The top cohomology is therefore the displayed quotient.

Apply (2.2) in degree one. Its left term vanishes, so residual middle cohomology is $\operatorname{Tor}_1^{\mathcal O}(Q_{v,w},k)$. Over a discrete valuation ring this is the $\varpi$-torsion of $Q_{v,w}$. The quotient is torsion-free exactly when $U+V$ is primitive. The last equivalence follows from Theorem 2.1. $\square$

The theorem identifies the first simultaneous task exactly. One must prove primitivity of a sum, not merely primitivity of its two summands.

**Corollary 6.2 (commuting-projector range).** Retain the split-edge notation of Theorem 6.1,
but do not assume generic concentration. Suppose there are commuting idempotents

$$
e_v,e_w\in\operatorname{End}_{\mathcal O}(M_{11})
$$

with images $U$ and $V$, and suppose

$$
\operatorname{im}(e_ve_w)=L.
\tag{6.9a}
$$

Then $U+V$ and $U\cap V$ are direct summands of $M_{11}$,

$$
U\cap V=L,
$$

and the two-place total complex is homotopy equivalent to the finite free module
$M_{11}/(U+V)$ in degree two.

**Proof.** Since the idempotents commute,

$$
p=e_v+e_w-e_ve_w
$$

is an idempotent. Its image is $U+V$: it fixes both $U$ and $V$, and every value of $p$ lies
in their sum. Likewise $e_ve_w$ is an idempotent with image $U\cap V$. Indeed, its image lies
in both summands, while an element fixed by both $e_v$ and $e_w$ is fixed by their product.
Hypothesis (6.9a) therefore gives $U\cap V=L$. The degree-zero differential is injective by
either lower split edge, the middle cohomology is $(U\cap V)/L=0$, and the top quotient is
finite free because $U+V=\operatorname{im}p$ is a direct summand. Theorem 2.1 finishes the
proof. $\square$

In the unit-Gram range the formula (3.9) supplies candidate projectors. Corollary 6.2 applies
only after pull--trace base change at the two distinct places has been shown to make those
projectors commute and to identify their product image with the lower composite image.
Separate unit determinants do not prove either compatibility.

### 6.3 A split-edge torsion countermodel

Take

$$
M_{00}=\mathcal O,\qquad
M_{10}=M_{01}=\mathcal O^3,\qquad
M_{11}=\mathcal O^8,
$$

and give $M_{11}$ the basis $e_1,\ldots,e_8$. Define two rank-six direct summands

$$
U=\langle e_1,e_2,e_3,e_4,e_5,e_6\rangle
\tag{6.10}
$$

and

$$
V=\langle
e_1,e_2,e_3+\varpi e_7,e_4,e_5,e_6+\varpi e_8
\rangle.
\tag{6.11}
$$

Let

$$
L=\langle e_1,e_2,e_4,e_5\rangle.
\tag{6.12}
$$

Use coordinate split injections $M_{00}^{\oplus2}\to M_{10}$ and
$M_{00}^{\oplus2}\to M_{01}$. On the upper edges, identify the two rank-six aggregate
sources $M_{10}^{\oplus2}$ and $M_{01}^{\oplus2}$ with $U$ and $V$ so that both lower
composites identify $M_{00}^{\oplus4}$ with $L$. Every aggregate edge is split and the
square commutes. Moreover

$$
U\cap V=L.
$$

Nevertheless,

$$
M_{11}/(U+V)
\simeq(\mathcal O/\varpi)^{\oplus2}.
\tag{6.13}
$$

After inverting $\varpi$, the sum is all of $M_{11}\otimes E$, so the total complex is generically concentrated in top degree. Modulo $\varpi$, the two upper images coincide in dimension six, and the mixed obstruction has dimension two.

This countermodel retains every fact that a naive induction would use: split edges, a commutative square, correct generic concentration, and primitive lower intersections. The missing datum is precisely the primitivity of the upper sum.

### 6.4 What generic concentration proves

Packet factorization of the form (4.3) is a rational theorem. It implies

$$
H^i(C_{v,w}^+)\otimes_{\mathcal O}E=0
\qquad(i<2).
\tag{6.14}
$$

It follows that $H^0$ and $H^1$ are torsion. Under the split-edge hypotheses, Theorem 6.1 further kills integral $H^0$ and $H^1$. Yet residual $H^1$ can remain because it is produced by torsion in $H^2$. Thus even the stronger statement

$$
H^i(C_{v,w}^+)=0\quad(i<2)
$$

does not imply residual concentration unless the top quotient is torsion-free.

Over a larger face algebra, one must also control every positive Tor term in (2.4).
Torsion-freeness over $\mathcal O$ does not imply projectivity over that algebra. Thus the
generic rational cube and integral mixed primitivity are different assertions: the first
fixes ranks and packet factors, while the second fixes the relative position of their
integral lattices.

### 6.5 A field-valued excess-intersection model

The mixed problem can fail even before integral torsion enters. Let

$$
M_{00}=k,\qquad
M_{10}=M_{01}=k^3,\qquad
M_{11}=k^7.
$$

Let each lower two-leg differential embed $k^2$ as the first two coordinates. Identify each upper source $k^3\oplus k^3$ with $k^6$, and let the common lower-left image be

$$
U_0=\langle a_1,a_2,a_4,a_5\rangle.
$$

Map the first upper source injectively onto

$$
\langle e_1,e_2,e_3,e_4,e_5,e_6\rangle
$$

and the second onto

$$
\langle e_1,e_2,e_3,e_4,e_5,e_7\rangle,
$$

carrying both copies of $U_0$ to

$$
\langle e_1,e_2,e_4,e_5\rangle.
$$

Every edge is split and the square commutes. The two upper images intersect in the five-dimensional space

$$
\langle e_1,e_2,e_3,e_4,e_5\rangle,
$$

while the lower composite image has dimension four. Hence the total complex has a one-dimensional middle class.

This example and the DVR example of Section 6.3 diagnose different defects. The field example has an actual excess intersection. The DVR example has no integral excess intersection, but reduction creates one from top torsion. A complete arithmetic theorem must exclude both, and over a face algebra it must also exclude their higher Tor analogues.

## 7. A finite set of active places

### 7.1 Ordered quotient cubes

Let $P=\{v_1,\ldots,v_r\}$ and let $C_P$ be the total complex of an actual strict level cube. Suppose every raw $v_1$-edge is split injective. At each spectator vertex $\epsilon$ in the remaining directions, form the cokernel

$$
N_{v_1\mid\epsilon}
=\operatorname{coker}(d_{v_1\mid\epsilon}).
\tag{7.1}
$$

Commutativity makes these cokernels into an $(r-1)$-cube $N_{v_1\mid\bullet}$. Objectwise replacement of each two-term edge by its cokernel gives a natural quasi-isomorphism

$$
C_P\simeq
\operatorname{Tot}(N_{v_1\mid\bullet})[-1].
\tag{7.2}
$$

This operation can be repeated. At the second step, however, the differential is no longer a raw old map. It is an old map on a $v_1$-new quotient. At the third step it acts on a double-new quotient. These induced maps are the new arithmetic content.

### 7.2 The exact joint obstruction groups

Define

$$
\operatorname{Ob}_{P;v_1}^j
=H^j\left(
\operatorname{Tot}(N_{v_1\mid\bullet})\otimes_A^Lk
\right),
\qquad 0\le j<r-1.
\tag{7.3}
$$

By (7.2),

$$
\operatorname{Ob}_{P;v_1}^j
\simeq H^{j+1}(C_P\otimes_A^Lk).
\tag{7.4}
$$

The split raw $v_1$-edges also give
$H^0(C_P\otimes_A^Lk)=0$. Consequently (7.3) accounts for every residual degree below the
top, not merely degrees one through $r-1$.

Theorem 2.1 gives the exact equivalence

$$
C_P\simeq N_P[-r]
\text{ for a finite free }N_P
\quad\Longleftrightarrow\quad
\operatorname{Ob}_{P;v_1}^j=0
\text{ for all }0\le j<r-1.
\tag{7.5}
$$

Although the presentations in (7.3) depend on $v_1$, their simultaneous vanishing does not. It is simply residual top-degree concentration of the total cube.

For $r\ge3$, vanishing on every original two-face is not enough. A lower class produced after one quotient can be killed by a later differential, or a new class can appear on a double-new quotient. The exact condition is the full collection in (7.3), not a pairwise checklist.

### 7.3 A sufficient recursive criterion

There is a useful cancellation-free certificate. Process the places in the order $v_1,\ldots,v_r$. Assume that at every stage and every remaining spectator vertex, the induced two-leg map on the already formed iterated-new quotient is injective after reduction to $k$.

Since its source and target are finite free over the local ring, residual injectivity exhibits a unit maximal minor. Elementary operations split the integral map, and its cokernel is finite free. Induction gives a finite free final quotient $N_P$ and

$$
C_P\simeq N_P[-r].
\tag{7.6}
$$

This criterion is sufficient, not necessary. In a complex of length at least three, different directions can cancel lower homology without every intermediate quotient map being injective. The exact criterion remains (7.5).

**Corollary 7.1 (cubically compatible split contractions).** Suppose every vertex module is
finite projective, every raw edge of the $P$-cube has a chosen retraction, and every retraction
commutes with all forward maps and retractions in the transverse directions. Then the
recursive criterion holds in every order.
Consequently

$$
C_P\simeq N_P[-|P|]
$$

for a finite projective $A$-module $N_P$, and every coefficient change is derived-exact.

**Proof.** Split one direction by its chosen retractions. Transverse compatibility makes every
remaining forward map and retraction descend to the quotient cube, where the descended
retraction still splits its edge. Repeat in any order. Every iterated-new quotient is finite
projective, so Section 7.3 applies. $\square$

This corollary isolates the extra fact hidden in a successful iteration: the splittings must
belong to one cubical contraction. A collection of unrelated split edge maps does not meet its
hypothesis.

### 7.4 Algebraic order independence

The total complex of a strict cube is canonically independent of the ordering, up to the Koszul sign isomorphism described after (5.3). Therefore, whenever it is concentrated in degree $r$, its top cohomology

$$
N_P=H^r(C_P)
\tag{7.7}
$$

is canonical and independent of the order.

If the recursive criterion succeeds in two different orders, both iterated quotients identify with (7.7). This proves order independence of the resulting module without comparing the elementary quotient presentations directly.

This algebraic result must not be confused with order independence of inner-form switching maps. The latter requires integral two-face comparisons and higher coherence, treated in Chapters 9--11.

### 7.5 Filtration spectral sequences

Every ordering of $P$ gives a filtration of the total cube. Filtering first by the $v_1$-degree produces a spectral sequence whose first page is the cohomology of the $v_1$-edge complexes. Under raw split injectivity, only their cokernels survive, and the next page is the cohomology of the quotient cube in (7.2).

For two places, this spectral sequence has only one possible lower obstruction, the kernel in (6.4). For three places, the quotient square can have middle cohomology, and a later differential can interact with it. Thus a class visible after the first quotient need not survive to total cohomology; conversely, a surviving total class need not be represented by a kernel on any original edge. Extension data determine how the resulting filtered homology is assembled, not whether a class exists in the associated graded.

Different orderings give different spectral sequences with the same abutment. This explains two facts:

- the recursive injectivity criterion can depend on an ordering even though total concentration does not; and
- a failed intermediate injectivity in one order does not prove that total concentration is impossible.

When the common relative factorization of Theorem 8.1 exists, every such spectral sequence degenerates for a simple reason: each local factor has cohomology in one degree and is projective. Without that factorization, the spectral sequences are diagnostic devices, not proofs of degeneration.

### 7.6 A pairwise-exact three-cube

Pairwise exactness fails to control the first genuinely ternary relation even over a field.
Let $k$ be any field, let

$$
L=k^2\oplus k^2,
$$

and choose the three pairwise complementary planes

$$
U=k^2\oplus0,
\qquad
V=0\oplus k^2,
\qquad
W=\{(x,x):x\in k^2\}.
\tag{7.8}
$$

Construct a three-place two-leg cube by taking

$$
M_{uvw}=L,
\qquad
M_{uv}=M_{uw}=M_{vw}=k,
\qquad
M_u=M_v=M_w=M_\varnothing=0.
\tag{7.9}
$$

Identify the two-copy aggregate sources
$M_{uv}^{\oplus2}$, $M_{uw}^{\oplus2}$, and $M_{vw}^{\oplus2}$ with $U,V,W$, respectively,
and use their inclusions into $L$ as the three upper edges. All remaining edges have zero
source. Every raw aggregate edge is therefore a split injection, and every square commutes.

Every original two-face is concentrated in its top degree. A face with the third coordinate
equal to one has total differential from two of $U,V,W$ to $L$, which is an isomorphism
because the two planes are complementary. A face with the third coordinate equal to zero is
the complex $0\to0\to k$.

The full total complex, however, is

$$
0\longrightarrow0\longrightarrow
U\oplus V\oplus W
\xrightarrow{(u,v,w)\mapsto u+v+w}L.
\tag{7.10}
$$

Its degree-two cohomology has dimension two, since the last map has a six-dimensional source
and rank four. Thus all original two-faces can be exact below their own top degrees while the
three-cube has lower total cohomology. The missing datum is the induced relation on an
iterated-new quotient, exactly as predicted by (7.3).

## 8. The relative product theorem

### 8.1 Statement

The preceding material yields a reusable theorem that cleanly separates formal algebra from arithmetic construction.

**Theorem 8.1 (common-carrier simultaneous concentration).** Let $(A,\mathfrak n,k)$ be a complete noetherian local ring and let $P$ be finite. Suppose the following objects have been constructed:

1. a strict $P$-cube of perfect primary complexes on one global carrier, with total complex $C_P^+$;
2. a strict adjoint companion cube satisfying

   $$
   C_P^-\simeq R\operatorname{Hom}_A(C_P^+,A)[-|P|];
   $$

3. one finite projective common global module $G_P$ over $A$;
4. for each $v\in P$, a perfect relative local complex $L_v$ and a finite projective module $N_v$ with $L_v\simeq N_v[-1]$;
5. a cubically compatible quasi-isomorphism

   $$
   C_P^+\xrightarrow{\sim}
   G_P\otimes_A^L\bigotimes_{v\in P}^LL_v.
   \tag{8.1}
   $$

Then

$$
C_P^+\simeq N_P[-|P|],
\qquad
N_P=G_P\otimes_A\bigotimes_{v\in P}N_v,
\tag{8.2}
$$

$N_P$ is finite projective, and

$$
C_P^-\simeq N_P^\vee.
\tag{8.3}
$$

For every $A$-algebra $B$, derived base change remains concentrated in the expected degree
and agrees with ordinary base change:

$$
C_P^+\otimes_A^LB
\simeq(N_P\otimes_AB)[-|P|].
\tag{8.4}
$$

All constructions are independent of the order of $P$ and retain the common global module exactly once.

The projectivity hypotheses separate two logically different tests. More generally, if the
quasi-isomorphism (8.1) exists and $L_v\simeq N_v[-1]$ without assuming the $N_v$ projective,
then top-degree concentration is equivalent to

$$
H^{-j}\left(
G_P\otimes_A^L\bigotimes_{v\in P}^LN_v
\right)=0
\qquad(j>0).
\tag{8.4a}
$$

When (8.4a) holds, write its degree-zero module as $N_P$. Exact base change to a specified
$A$-algebra $B$ is then equivalent to

$$
\operatorname{Tor}_j^A(N_P,B)=0
\qquad(j>0),
\tag{8.4b}
$$

and exact base change for every $B$ is equivalent, in the finite noetherian setting, to
$N_P$ being projective. Pairwise Tor vanishing among the original factors is not a substitute
for (8.4a): a sufficient ordered test requires vanishing of the positive Tor groups between
each successive ordinary tensor product, starting with $G_P$, and the next factor.

There is already a three-factor counterexample. Let

$$
A=k[[x,y]],\qquad
N_1=A/(x),\quad N_2=A/(y),\quad N_3=A/(x+y).
\tag{8.4c}
$$

Every pair is Tor-independent: modulo any one of the three distinct linear forms, either of
the other two is a non-zero-divisor, so

$$
\operatorname{Tor}_j^A(N_a,N_b)=0
\qquad(a\ne b, j>0).
$$

But $N_1\otimes_A^LN_2\simeq k$, while multiplication by $x+y$ is zero on $k$. Hence

$$
\operatorname{Tor}_1^A(N_1\otimes_AN_2,N_3)
=\operatorname{Tor}_1^A(k,A/(x+y))
\simeq k.
\tag{8.4d}
$$

Thus all original pairs can be clean while the triple derived product has negative
cohomology. Successive intermediate Tor, not only pairwise Tor, is the exact higher-product
test.

### 8.2 Proof

Associativity and symmetry of derived tensor products turn (8.1) into

$$
C_P^+
\simeq
G_P\otimes_A
\bigotimes_{v\in P}N_v[-|P|].
$$

The unshifted tensor is finite projective because every factor is finite projective over the same ring $A$. This proves (8.2). Derived duality and the declared adjoint normalization give (8.3). Projectivity kills all positive Tor after any base change, proving (8.4). Symmetry supplies order independence, with the standard graded signs. The module $G_P$ appears outside the local product and therefore occurs once. $\square$

### 8.3 Why the arithmetic premise is new

The theorem does not claim that (8.1) follows from one-place concentration. It does not. The one-place global complexes each contain the global multiplicity carrier, and their tensor product has the wrong rank. To establish (8.1), geometry must produce integral relative factors or an equivalent common-component algebra over which the global factor has been divided out.

Alternatively, one can bypass (8.1) and prove the joint obstruction groups (7.3) vanish directly. In two variables and over the final coefficient DVR, this is exactly the sum-primitivity theorem of Theorem 6.1. These are the two honest routes to mixed exactness.

### 8.4 Comparison with the direct obstruction route

The relative-product route and the direct obstruction route prove the same concentration conclusion but carry different information.

The relative-product route exhibits the top module explicitly:

$$
N_P=G_P\otimes_A\bigotimes_{v\in P}N_v.
\tag{8.5}
$$

It therefore gives ranks, base change, support intersections, and order independence immediately. Its difficult premise is the integral quasi-isomorphism (8.1).

The direct route begins with the actual cube and proves the groups in (7.3) vanish. It yields

$$
N_P=H^{|P|}(C_P)
\tag{8.6}
$$

without expressing this module as a tensor product. It can succeed even when no natural relative factorization has been constructed. Its difficult premise is recursive mixed injectivity or an equivalent geometric saturation theorem.

There is a useful way to compare the two. If the direct route proves concentration and a generic relative factorization is known, then the resulting integral top lattice sits inside the generic module in (8.5). The index between that lattice and a proposed tensor-product lattice measures the failure of the proposed integral relative comparison. Showing the index is a unit is again a primitivity statement.

Thus the two routes do not combine to make the hard step disappear. They locate the same integral information in different places: one in the exactness of the global cube, the other in the integrality of a common-carrier factorization.

## 9. The parity-indexed switching cube

### 9.1 Its vertices

The level cube changes compact open subgroups while keeping the ambient inner form fixed. Product residue requires a second cube in which the inner form changes. Let $B$ be a quaternion algebra split at one real place $\tau$, and assume every $v\in P$ is split in $B$. For $I\subseteq P$, define $B_I$ by

$$
\operatorname{Ram}(B_I)
=\operatorname{Ram}(B)\mathbin\triangle I
\mathbin\triangle
\begin{cases}
\{\tau\},&|I|\text{ odd},\\
\varnothing,&|I|\text{ even}.
\end{cases}
\tag{9.1}
$$

The parity in (9.1) is forced by the product formula for quaternion algebras. If $|I|$ is even, $B_I$ is split at $\tau$ and supports a curve carrier. If $|I|$ is odd, $B_I$ is totally definite and supports a finite class-set carrier. An edge

$$
I\longrightarrow I\cup\{v\}
$$

toggles $v$ and $\tau$, exactly the one-place inner-form switch.

The endpoint $B_P$ depends only on $P$, not on an ordering. This proves order independence of the final ramification set. It says nothing yet about integral maps between the carriers.

### 9.2 Routed one-place switches

For each vertex $I$, one needs a routed perfect object $\mathcal G_I$ on the correct component union. For an edge $I\to I\cup\{v\}$, the one-place comparison supplies, in its established range, a derived switch

$$
\operatorname{Res}_{I,v}:\mathcal G_I\longrightarrow\mathcal G_{I\cup\{v\}}.
\tag{9.2}
$$

The notation in (9.2) abbreviates a structured morphism, not a scalar map between generic packet spaces. Its integral construction must carry:

1. the primary coefficient system and its actual companion;
2. the extreme residue with coefficient one;
3. the normalization complex, including both branches;
4. the graph lattice and monodromy pairing;
5. the Néron component module;
6. the normalized-branch Smith module;
7. the conductor or Kummer parameter and selected line or sign;
8. the routed connected component;
9. every auxiliary shadow; and
10. the adjoint correspondence in the reverse direction.

If a route enters a definite vertex, the finite class-set lattice and the curve residue lattice must be compared integrally. A generic packet correspondence determines the rational label but not the lattice index, the branch correction, or the component map.

The edge maps can be composed along an ordering

$$
\sigma=(v_{\sigma(1)},\ldots,v_{\sigma(r)}).
$$

This gives a routed iterated switch

$$
\operatorname{Res}_{\sigma}
=\operatorname{Res}_{I_{r-1},v_{\sigma(r)}}\circ\cdots\circ
\operatorname{Res}_{\varnothing,v_{\sigma(1)}},
\tag{9.3}
$$

where $I_j=\{v_{\sigma(1)},\ldots,v_{\sigma(j)}\}$. Formula (9.3) is defined once every edge exists. Independence of $\sigma$ is an additional coherence theorem.

### 9.3 Two-face comparisons

Let $v,w\notin I$. The two paths around the corresponding face are

$$
\operatorname{Res}_{I\cup\{v\},w}\operatorname{Res}_{I,v}
\quad\text{and}\quad
\operatorname{Res}_{I\cup\{w\},v}\operatorname{Res}_{I,w}.
\tag{9.4}
$$

Generically, the two paths carry a packet to the same final packet. Away from $v,w,\tau$ nothing changes; the local changes at $v$ and $w$ commute; the two toggles at $\tau$ cancel. Occurrence multiplicity one determines the final packet label.

The integral comparison required for simultaneous residue is a specified quasi-isomorphism

$$
b_{I;v,w}:
\operatorname{Res}_{I\cup\{v\},w}\operatorname{Res}_{I,v}(\mathcal G_I)
\xrightarrow{\sim}
\operatorname{Res}_{I\cup\{w\},v}\operatorname{Res}_{I,w}(\mathcal G_I).
\tag{9.5}
$$

It must commute with every item in the correction ledger of Section 9.2. Equality of generic packet labels does not determine the scalar of (9.5), and it does not show that a scalar relating two lattice maps is a unit. Even after choosing that scalar, a derived extension class can obstruct a chain homotopy.

### 9.4 Three-face and higher coherence

On a three-face with directions $u,v,w$, there are six orders of composition. The two-face comparisons in (9.5) identify adjacent orders. They must satisfy the braid relation: the comparison from $uvw$ to $wvu$ obtained by interchanging the first two, then the last two, then the first two must agree with the comparison obtained in the opposite braid order.

At the level of adjacent transpositions, write $s_i$ for the interchange of the $i$th and $(i+1)$st directions. Coherence requires

$$
s_i^2=1,\qquad
s_is_j=s_js_i\quad(|i-j|>1),\qquad
s_is_{i+1}s_i=s_{i+1}s_is_{i+1}.
\tag{9.6}
$$

The first identity is normalization of a two-face comparison, the second concerns disjoint faces, and the third is the three-face condition. If these identities hold as literal equalities of two-morphisms, every two words of adjacent transpositions yield the same endpoint isomorphism. In a derived or stable $\infty$-categorical model, however, this proves only the corresponding order independence in the homotopy category. Coherent fillers for the higher relations among these relations must still be supplied; they are not forced merely by the Coxeter presentation.

The formal deduction from (9.6) is proved in Chapter 11. The arithmetic construction of the maps in (9.5), including their normalization and the three-face identity, is not supplied by the individual one-place switches.

### 9.5 Normalizing the switch

A generic packet comparison between two one-dimensional Hom spaces is unique only up to a nonzero scalar. An integral comparison between lattices is unique only up to a unit after existence has been proved. If the scalar has positive valuation, the two lattices differ by a nontrivial index.

The one-place geometry provides several possible normalizations:

- require the coefficient-one extreme residue to map the primitive generator to the primitive generator;
- require compatibility with the graph monodromy pairing;
- require adjunction under the primary--companion pairing;
- require the selected branch generator to map to the selected branch generator; and
- require the component route to carry a fixed geometric component label.

These requirements need not be redundant. The normalization middle term can introduce a sign, the inverse-double-coset adjoint can introduce $S_v^{-1}$, and reversing an orientation can exchange two branches. A valid edge normalization proves that all these conventions agree.

Around a two-face, even normalized edges can differ by a unit automorphism of the endpoint packet lattice. The comparison $b_{I;v,w}$ must show that this unit is one under the global normalization, or must record the unit in a coherent two-cell. Around a three-face, the product of these units must satisfy the braid identity.

This scalar bookkeeping is integral content. Generic multiplicity one proves that the ambiguity is scalar; it does not prove that the scalar is a unit or that the normalized scalar is one.

## 10. Product residue and the full correction terms

### 10.1 Why there is no arithmetic multi-fiber

For distinct finite places $v$ and $w$, their closed points in the arithmetic base are disjoint. Their residue ideals are comaximal, so

$$
\operatorname{Spec}k(v)
\times_{\operatorname{Spec}\mathcal O_F}
\operatorname{Spec}k(w)
=\varnothing.
\tag{10.1}
$$

Thus a curve over an open arithmetic base has a $v$-fiber and a $w$-fiber, but no closed stratum on which both nearby-cycle functors can literally be iterated. A model over an artificial base with independent parameters $t_v,t_w$ would have such a stratum, but constructing that model and comparing its coordinate traits with the arithmetic curves would itself be a new geometric theorem.

The parity-indexed cube of Chapter 9 is the intrinsic replacement. It compares separate one-place residue operations by moving among inner forms. Its virtue is that every edge is arithmetic. Its cost is that commutation must be proved by routed comparison maps rather than read from a cartesian multi-fiber.

### 10.2 Relative component complexes

For one place $v$, let $K_v^{\mathrm{comp}}$ be the strict component complex. Denote its full derived source and target by

$$
S_v^{\mathrm{comp}},
\qquad
T_v^{\mathrm{comp}},
$$

and its extreme residue arrow by

$$
\rho_v:S_v^{\mathrm{comp}}\longrightarrow T_v^{\mathrm{comp}}.
\tag{10.2}
$$

The source and target include the normalization middle term, component module, branch Smith correction, and conductor data. They are not only their extreme graded pieces.

Before taking a product, one must remove the common global packet and component carrier from each one-place object. Let

$$
S_v^{\mathrm{rel}},\qquad T_v^{\mathrm{rel}}
$$

be the resulting local relative factors over one common algebra $A$. The common global factor is suppressed from the notation and is to be inserted once. Define

$$
S_P^{\mathrm{loc}}
=\underset{v\in P}{\bigotimes_A^L} S_v^{\mathrm{rel}},
\qquad
T_P^{\mathrm{loc}}
=\underset{v\in P}{\bigotimes_A^L} T_v^{\mathrm{rel}},
\tag{10.3}
$$

and

$$
\rho_P^{\mathrm{loc}}
=\underset{v\in P}{\bigotimes_A^L}\rho_v.
\tag{10.4}
$$

If the $S_v^{\mathrm{rel}}$ are replaced by full global one-place component objects, the common factor is duplicated. If they are defined over different bases, (10.3) has no declared meaning. If ordinary tensors replace derived tensors, component Tor is erased.

Let

$$
\rho_P^{\mathrm{geom}}:
S_P^{\mathrm{geom}}\longrightarrow T_P^{\mathrm{geom}}
\tag{10.5}
$$

be the connecting map in the total geometric object constructed from the parity-indexed switching cube or from a separately constructed higher-dimensional comparison model.

### 10.3 The derived residue defect

A product-residue theorem must construct quasi-isomorphisms

$$
\beta_P^S:S_P^{\mathrm{loc}}\xrightarrow{\sim}S_P^{\mathrm{geom}},
\qquad
\beta_P^T:T_P^{\mathrm{loc}}\xrightarrow{\sim}T_P^{\mathrm{geom}}.
\tag{10.6}
$$

The defect is the derived morphism

$$
\delta_P^{\mathrm{res}}
=\beta_P^T\circ\rho_P^{\mathrm{loc}}
-\rho_P^{\mathrm{geom}}\circ\beta_P^S
\in
\operatorname{Hom}_{D(A)}
(S_P^{\mathrm{loc}},T_P^{\mathrm{geom}}).
\tag{10.7}
$$

Product residue is the assertion that the maps in (10.6) exist with the correct routes and orientations, that

$$
\delta_P^{\mathrm{res}}=0,
\tag{10.8}
$$

and that a chosen null-homotopy is compatible on all higher faces.

The coefficient-one calculation on each extreme residue determines the coordinate maps on the easiest graded pieces. It does not construct $\beta_P^S$ or $\beta_P^T$, and it does not determine the morphism on the component and branch terms. The conductor parameter also matters: a scalar-twist face can move between conductor-one and conductor-two loci, and a generic special face carries a selected invariant line.

### 10.4 Integral countermodels

Two elementary examples show why generic commutation and ordinary tensor identities are insufficient.

First, let $\mathcal O$ be a discrete valuation ring and $k=\mathcal O/\varpi$. Then $k$ is a perfect object over $\mathcal O$, and

$$
\operatorname{Hom}_{D(\mathcal O)}(k,k[1])
=\operatorname{Ext}_{\mathcal O}^1(k,k)
\simeq k.
\tag{10.9}
$$

A nonzero class in (10.9) becomes zero after tensoring with $E$. Therefore two composites can agree generically and on their extreme free terms while differing by a nonzero integral derived class. Torsion in a Néron component module or branch Smith module provides a natural target for such a class.

Second, over $A=k[[t]]$,

$$
\operatorname{Tor}_1^A(k,k)\simeq k.
\tag{10.10}
$$

Tensoring the resolution

$$
0\longrightarrow A\xrightarrow{t}A\longrightarrow k\longrightarrow0
$$

with $k$ makes its differential zero. Thus even two identity maps on the coefficient-one object $k=A/(t)$ have a derived product with an extra degree. The extra term is genuine intersection data. It may be discarded only after an explicit Tor-independence theorem.

The unwanted mixed homology of the automorphic old--new cube and the wanted component Tor in (10.10) belong to different ledgers. The first must vanish for a projective top automorphic carrier. The second must be retained and transported by product residue.

### 10.5 Component Fitting data

Let $\Lambda_v^{\mathrm{graph}}$ be the graph lattice of the semistable fiber and let

$$
\mu_v:\Lambda_v^{\mathrm{graph}}
\longrightarrow
(\Lambda_v^{\mathrm{graph}})^\vee
\tag{10.11}
$$

be its monodromy pairing. The component module is modeled by

$$
\Phi_v=\operatorname{coker}\mu_v.
\tag{10.12}
$$

If the normalized two-branch comparison contributes

$$
B_v=\operatorname{coker}\left(1-(F_v^*)^2\right),
\tag{10.13}
$$

then the one-place correction is not represented by a single scalar determinant unless both modules are cyclic and the comparison identifies their generators. The robust invariants are

$$
\operatorname{Fitt}^i(\Phi_v),
\qquad
\operatorname{Fitt}^i(B_v),
\tag{10.14}
$$

together with the derived extension joining them to the extreme residue.

For several places, the local relative complexes can have derived tensor terms such as

$$
\operatorname{Tor}_j^A(\Phi_v,B_w),
\qquad
\operatorname{Tor}_j^A(B_v,\Phi_w),
\qquad
\operatorname{Tor}_j^A(\Phi_v,\Phi_w).
\tag{10.15}
$$

These terms are part of the product component object. They should not be forced to vanish merely to make a tensor formula simpler. Product residue must match them with the corresponding filtration pieces on the iterated-switch side.

By contrast, positive Tor of the top automorphic carrier with a character residue field is an obstruction to exact underived specialization and must vanish in the all-component theorem. The shared word “Tor” therefore covers two opposite roles: retained geometric intersection data in (10.15), and forbidden nonflatness of the automorphic top module.

Fitting ideals provide a concise comparison after the derived object has been constructed. Equality of alternating Fitting divisors can be a consequence of a perfect quasi-isomorphism. It cannot replace construction of that quasi-isomorphism, because two nonisomorphic perfect complexes can have the same Euler characteristic and the same total determinant.

## 11. Beck--Chevalley coherence and order independence

### 11.1 The formal coherence theorem

The categorical content can be stated independently of the arithmetic origin of the switch maps.

**Theorem 11.1 (categorical order independence).** Let $\mathcal C$ be a category enriched in
groupoids, or the homotopy $2$-category of a stable enhancement, and let
$P=\{v_1,\ldots,v_r\}$. Suppose:

1. for every $I\subseteq P$ there is an object $\mathcal G_I$;
2. for every $v\notin I$ there is a functorial edge map

   $$
   R_{I,v}:\mathcal G_I\longrightarrow\mathcal G_{I\cup\{v\}};
   $$

3. for every two-face there is an invertible comparison

   $$
   b_{I;v,w}:R_{I\cup\{v\},w}R_{I,v}
   \xRightarrow{\sim}
   R_{I\cup\{w\},v}R_{I,w};
   $$

4. the comparisons are normalized under reversal, commute on disjoint faces, and satisfy the
   braid relation on every three-face, with these identities preserved by the whiskerings and
   face restrictions used to form longer composites.

Then for any two orderings $\sigma,\tau$ of $P$, there is a canonical isomorphism

$$
R_\sigma(\mathcal G_\varnothing)
\xrightarrow{\sim}
R_\tau(\mathcal G_\varnothing),
\tag{11.1}
$$

independent of the sequence of adjacent transpositions used to pass from $\sigma$ to $\tau$. These isomorphisms are compatible with restriction to every face and with pasting of finite sets.

**Proof.** Any permutation is a product of adjacent transpositions. Assign to an adjacent transposition the corresponding two-face comparison. Two words in adjacent transpositions represent the same permutation if and only if they are related by the Coxeter relations in (9.6). Normalization, disjoint-face commutation, and the three-face braid condition identify the transformations attached to the two sides of each relation. Hence the transformation depends only on the permutation. Compatibility with faces and pasting follows by applying the same argument in the relevant subcube. $\square$

This theorem proves path-independent endpoint isomorphisms in the stated $2$-categorical
sense. It does not construct the two- and three-face data, and by itself it does not construct
a homotopy-coherent higher cube in a chosen chain or $\infty$-categorical model.

### 11.2 Chain-level homotopies

Suppose the objects are represented by complexes and the two composites around a face are chain maps $f_{vw}$ and $f_{wv}$. A two-face homotopy is a degree $-1$ map $h_{v,w}$ satisfying

$$
f_{vw}-f_{wv}
=dh_{v,w}+h_{v,w}d.
\tag{11.2}
$$

On a three-face, the two braid routes produce two homotopies between the same endpoint chain maps. Their difference is a degree $-1$ cycle in the Hom complex. Three-face coherence requires a degree $-2$ map $H_{u,v,w}$ whose differential is that difference.

This is the chain-level meaning of the assertion that the braid diagram commutes up to a specified higher homotopy. For four or more directions, the resulting boundaries of higher permutohedra require further chosen fillers. In a stable categorical formulation, these fillers are part of a coherent cubical natural transformation; their existence is additional data unless an independent strictification or vanishing theorem supplies it.

The presence of torsion makes the distinction between equality in the derived category and a chosen coherent chain homotopy important. A derived equality can have many representatives, and their differences can contribute to later totalizations unless the higher choices are compatible.

### 11.3 What remains geometric

Theorem 11.1 reduces the arithmetic task to concrete finite data:

- construct every routed edge switch with the full correction ledger;
- construct $b_{I;v,w}$ on every two-face, not merely after inverting $\varpi$;
- show that it respects component routing, normalization branches, Néron modules, Smith modules, conductor parameters, primary--companion adjunction, and auxiliary shadows;
- construct the three-face filler or prove the braid identity strictly; and
- show compatibility under every coefficient change used in the conclusion.

The parity formula (9.1) supplies the vertices and proves that all orders end at the same inner form. Generic packet correspondence supplies agreement of rational labels. Neither statement supplies the integral homotopies above.

### 11.4 Strict commutation and homotopy commutation

The global level cube and the switching cube have different commutation mechanisms.

In the level cube, the adelic representatives at distinct places commute literally. After choosing one common carrier, the face maps can therefore be made strictly commutative. Cubical signs then give an ordinary total complex.

In the switching cube, the two paths pass through different intermediate inner forms. There is no literal equality of functors. The best natural statement is a quasi-isomorphism or chain homotopy between the composites.

This distinction affects totalization. A strictly commutative square yields a bicomplex directly. A homotopy-commutative square yields a homotopy-coherent diagram whose total object includes the chosen homotopy as part of its differential data. Replacing the homotopy by another one can change the strict model by a higher extension, although coherently equivalent choices give equivalent total objects.

When all $b_{I;v,w}$ are strict identities, three-face coherence is automatic. When they are nontrivial homotopies, the degree-$2$ fillers of Section 11.2 are indispensable. This is why proving pairwise equality in the derived category does not by itself construct a coherent finite-set switch.

One may strictify a finite homotopy-coherent cube in a suitable model of the stable category. Strictification preserves the object only after the complete coherent datum has been supplied. It cannot be used to manufacture missing two- or three-face homotopies.

## 12. Simultaneous component support

### 12.1 The all-component theorem

Let $R_P$ be a noetherian, universally catenary, locally equidimensional ring representing
the product local condition, and let $M_P$ be a finite $R_P$-module. Universal catenarity is
available for complete noetherian local rings, but local equidimensionality is not being
inferred here; it is a stated hypothesis that must be checked for the deformation ring in
use. The following support criterion is formal but powerful.

**Theorem 12.1 (all-component support).** Assume that for every irreducible component $\Xi$ of $\operatorname{Spec}(R_P)_{\mathrm{red}}$ there is a prime $\mathfrak q_\Xi\in\Xi$ such that:

1. $\Xi$ is the unique irreducible component through $\mathfrak q_\Xi$;
2. $(M_P)_{\mathfrak q_\Xi}\ne0$; and
3. the maximal-depth equality holds:

   $$
   \operatorname{depth}_{(R_P)_{\mathfrak q_\Xi}}
   (M_P)_{\mathfrak q_\Xi}
   =\dim(R_P)_{\mathfrak q_\Xi}.
   \tag{12.1}
   $$

Then every generic point of $R_P$ belongs to $\operatorname{Supp}_{R_P}(M_P)$, and hence

$$
\operatorname{Supp}_{R_P}(M_P)=\operatorname{Spec}R_P.
\tag{12.2}
$$

**Proof.** Suppose the generic point of $\Xi$ were absent from the support. Localizing at
$\mathfrak q_\Xi$, the support of $M_P$ would be a proper closed subset of the unique local
component. Catenarity and local equidimensionality make its dimension strictly smaller than
$\dim(R_P)_{\mathfrak q_\Xi}$. But for every finite module,

$$
\operatorname{depth}M
\le\dim\operatorname{Supp}M.
$$

This contradicts (12.1). Repeating for every component puts every minimal prime in the support. Since support is closed and the closures of the minimal primes cover the spectrum, (12.2) follows. Equivalently, the annihilator of $M_P$ is contained in the nilradical. This does not prove that the annihilator is zero. $\square$

The arithmetic work lies in producing the primes $\mathfrak q_\Xi$, nonzero joint boundary classes there, and the maximal-depth comparison. One-place boundary witnesses on different carriers do not supply them.

### 12.2 The pointed theorem

For a named point, the required statement is smaller.

**Theorem 12.2 (pointed component factorization).** Let $x:R_P\to D$ be a homomorphism to a domain. Let $M_P$ be finite over $R_P$, let

$$
I=\operatorname{Ann}_{R_P}(M_P),
$$

and let $\mathbb T_P=R_P/I$ be the faithful image. Suppose an irreducible component $\Xi_x$ through $x$ has minimal prime $\mathfrak p_{\Xi_x}$ satisfying

$$
\mathfrak p_{\Xi_x}\in\operatorname{Supp}_{R_P}(M_P).
\tag{12.3}
$$

Then $x$ factors through $\mathbb T_P$.

**Proof.** Condition (12.3) is equivalent to

$$
I\subseteq\mathfrak p_{\Xi_x}.
$$

Since $\Xi_x$ contains the point $x$,

$$
\mathfrak p_{\Xi_x}\subseteq\ker x.
$$

Thus $I\subseteq\ker x$, and $x$ factors through $R_P/I$. $\square$

Under the hypotheses of Theorem 12.1, it is enough to verify its three conditions at one unique-component prime on $\Xi_x$. This proves (12.3) without asking for support on the other components.

The theorem proves only factorization of the point. It does not imply that $I$ is nilpotent, zero, or supported away from any other component.

### 12.3 Separate projections are insufficient

Let $k$ have characteristic at least seven and put

$$
R=k[[x,y]]/\bigl(xy(x-y)(x-2y)\bigr).
\tag{12.4}
$$

The four distinct linear factors define four irreducible branches. Label them

$$
(0,0),\ (0,1),\ (1,0),\ (1,1)
$$

in the order $x,y,x-y,x-2y$. Let

$$
M=R/\bigl(x(x-2y)\bigr).
\tag{12.5}
$$

The support of $M$ is the union of the two diagonal branches $(0,0)$ and $(1,1)$. Its projection onto either coordinate contains both labels $0$ and $1$. Nevertheless it misses both off-diagonal product components.

Therefore even separate projections of the support of one common module do not imply product support. Separate one-place support theorems on different modules and different rings are weaker still.

There is a valid common-base tensor criterion. For perfect complexes $E_1,\ldots,E_r$ over one noetherian ring $R$,

$$
\operatorname{Supp}_R
\left(E_1\otimes_R^L\cdots\otimes_R^LE_r\right)
=\bigcap_i\operatorname{Supp}_R(E_i).
\tag{12.6}
$$

Indeed, tensor with the residue field at a prime. A tensor product of nonzero bounded complexes of finite-dimensional vector spaces is nonzero. Formula (12.6) is useful only after all one-place complexes have been pulled to the same product ring and their relative derived tensor has been identified with the actual global cube. It gives no shortcut from unrelated one-place support statements.

### 12.4 Local product components and global components

Let

$$
R_{\mathrm{loc},P}
=\widehat\bigotimes_{v\in P,\mathcal O}R_v^{\square,\mathcal D_v}
\tag{12.7}
$$

be the completed product of the represented local component rings. The global product deformation ring is obtained by imposing global reciprocity and determinant relations:

$$
R_P
=R_{F,S}^{\square_T}
\widehat\otimes_{R_{\mathrm{loc}}^\square}
R_{\mathrm{loc},P},
\tag{12.8}
$$

followed by removal of frames when the global residual endomorphisms are scalar.

An irreducible component of $R_P$ maps into a product of local components, but several global components can lie over the same local product component. Conversely, a local product component can fail to occur globally because the determinant, parity, or reciprocity constraints are incompatible.

Thus “support on the local product” is not the same as support on $\operatorname{Spec}R_P$. The former says that the module sees the local labels; the latter says that it sees the global deformations satisfying those labels.

For a pointed theorem, the component $\Xi_x$ is selected by the actual global point $x$, not merely by its tuple of local restrictions. To prove its occurrence, one can:

- transport a nonzero joint boundary class to a unique-component point on $\Xi_x$ and prove maximal depth;
- construct a common-base relative tensor whose support contains $\Xi_x$ by (12.6); or
- give a direct generic packet occurrence on the global carrier and show its prime specializes to $x$.

Each route is genuinely global. Separate local smoothness proves only that the local point deforms unobstructedly; it says nothing about automorphic support on the global component.

## 13. The canonical pointed carrier

### 13.1 Torsion-free top cohomology

Let $C_P^+$ be an actual finite free $\mathcal O$-valued level cube, with $r=|P|$. No mixed concentration is assumed. Define

$$
Q_P=H^r(C_P^+)
=C_P^{+,r}/\operatorname{im}(d^{r-1})
\tag{13.1}
$$

and remove its $\varpi$-power torsion:

$$
Q_P^{\mathrm{tf}}
=Q_P/Q_P[\varpi^\infty].
\tag{13.2}
$$

Because a finitely generated torsion-free module over a discrete valuation ring is free, $Q_P^{\mathrm{tf}}$ is finite free. It is canonical for the actual cube. Its definition does not require the lower cohomology to vanish.

After extending to $E$, torsion disappears. The packet decomposition (4.3) therefore identifies the packet blocks of $Q_P^{\mathrm{tf}}\otimes E$ with the top cohomology of the local-factor cube. The global factor $G_{\Pi,P}$ occurs once.

The construction must be performed after the final fixed-character specialization. Formation of a torsion-free quotient need not commute with a nonflat base change. If a cube is first formed over a character algebra, specialized, and then replaced by its torsion-free top, the result can differ from specializing a torsion-free top formed before the quotient.

### 13.2 The adjoint kernel and perfect pairing

On the strict adjoint side define

$$
K_P^-
=\ker\left(
(d^{r-1})^\vee:
(C_P^{+,r})^\vee
\longrightarrow
(C_P^{+,r-1})^\vee
\right).
\tag{13.3}
$$

Left exactness of $\operatorname{Hom}_{\mathcal O}(-,\mathcal O)$ gives

$$
K_P^-
\simeq\operatorname{Hom}_{\mathcal O}(Q_P,\mathcal O).
\tag{13.4}
$$

The torsion of $Q_P$ has zero Hom into $\mathcal O$, so

$$
K_P^-
\simeq\operatorname{Hom}_{\mathcal O}
(Q_P^{\mathrm{tf}},\mathcal O).
\tag{13.5}
$$

Consequently evaluation is a perfect pairing

$$
Q_P^{\mathrm{tf}}\times K_P^-
\longrightarrow\mathcal O.
\tag{13.6}
$$

Functoriality makes the first factor stable for the primary Hecke action and the second stable for the adjoint action. The pairing intertwines them under the declared involution. The companion is not inserted as a second primary deformation action.

**Theorem 13.1 (pointed carrier theorem).** For every actual finite free global cube over
$\mathcal O$, the modules in (13.2) and (13.3) are finite free, perfectly paired as in (13.6),
and stable under the primary and adjoint Hecke actions. If, in addition, the generic fiber of
that cube has the packetwise common-carrier decomposition (4.3), then every nonzero generic
packet block of the pointed carrier contains the global packet multiplicity factor exactly
once.

**Proof.** Freeness and duality are (13.2)--(13.5). Hecke stability follows because cycles, boundaries, torsion, and kernels are stable under every chain endomorphism. Under the additional generic decomposition, the packet assertion follows from (4.3) after inverting $\varpi$. $\square$

This theorem is unconditional after the actual cube has been constructed. It does not prove mixed exactness or any base-change compatibility for the torsion-free quotient.

### 13.3 The pointed occurrence problem

Let $R_P$ be the product deformation ring acting on $Q_P^{\mathrm{tf}}$, and let $x:R_P\to D$ be the named point. The remaining arithmetic statement is

$$
\mathfrak p_{\Xi_x}
\in\operatorname{Supp}_{R_P}(Q_P^{\mathrm{tf}})
\tag{13.7}
$$

for one irreducible component $\Xi_x$ through $x$, carrying the complete tuple of local determinant, type, line, sign, monodromy, and conductor labels.

Once (13.7) and finite-set reciprocity on this actual carrier are proved, Theorem 12.2 factors $x$ through the faithful Hecke image. No mixed-exactness theorem is used in that final annihilator argument.

Statement (13.7) is still genuinely joint. The component $\Xi_x$ is not determined by its separate one-place projections, and the carrier is not a tensor product of separate one-place carriers. Product residue is one method for transporting a boundary witness to $\Xi_x$, but it is not logically necessary if occurrence is established by another argument.

### 13.4 Structural labels on the pointed carrier

The faithful order on $Q_P^{\mathrm{tf}}$ is useful only after its generic factors have been identified. For every factor, one must record the complete tuple

$$
(\delta;\ \mathcal D_v,\ L_v,\ \varepsilon_v,\ N_v,\ c_v)_{v\in P},
\tag{13.8}
$$

where the entries denote determinant, represented local component, ordered line or characters, sign, monodromy, and conductor or scalar character as applicable.

The top quotient can discard packets that occur in lower cohomological degrees or are killed by the final boundary. It can also retain several packets meeting at the same residual maximal ideal. Therefore the labels cannot be read from the original vertex modules alone. They must be checked on the generic decomposition of the actual top carrier.

The companion factor supplies a consistency test. Under the perfect pairing, its diamond characters are inverted, its central character is dualized, and its selected root is the adjoint root. If the primary and companion generic decompositions do not match under these operations, the claimed action or branch selection has been normalized incorrectly.

Monodromy requires special care. Every generic factor on a selected special component has nonzero monodromy, but the order-valued monodromy matrix may vanish on a residual quotient. The pointed characteristic-zero point lies in the open nonzero locus only after its monodromy entry ideal is not contained in $\ker x$. The represented component is the closure, while the point supplies the open condition.

Only after these checks does the faithful order satisfy the simultaneous branch premise of finite-set reciprocity.

## 14. Joint ray quotients and exact augmentation

### 14.1 Cross-locally trivial ray characters

Retain the standing convention that $\ell$ is odd. Scalar-twist directions require global characters whose localizations are controlled simultaneously. Let $P_{\mathrm{sc}}\subseteq P$ be the subset of scalar active places. For $v\in P_{\mathrm{sc}}$, put

$$
e_v=\ell^{\operatorname{ord}_\ell(q_v-1)}
$$

and let

$$
\Delta_v=C_{e_v}.
$$

Thus every $\Delta_v$ has odd order, so the local--global character theorem is used only in
its nonexceptional odd-order range.

Fix a protected set $S_0$ containing the entire active set $P$, the places above $\ell$, and
every place already ramified in the global datum. Assume the local--global character theorem
applies to the prescribed odd-order local characters with the relevant unit, sign, and central
relations.

At each $v$, prescribe the residue-unit quotient

$$
F_v^\times\longrightarrow k_v^\times
\longrightarrow k_v^\times/(k_v^\times)^{e_v}
\simeq\Delta_v,
\tag{14.1}
$$

send a chosen uniformizer to $1$, and prescribe the trivial character at every $w\in S_0\setminus\{v\}$. The local--global theorem gives

$$
c_v:G_F\longrightarrow\Delta_v
\tag{14.2}
$$

with precisely these protected localizations. Additional conductor places may occur; every one of them must be added to the spectator datum and its local condition transported under the twist.

Set

$$
\Delta_P=\prod_{v\in P_{\mathrm{sc}}}\Delta_v,
\qquad
c_P=(c_v)_{v\in P_{\mathrm{sc}}}.
\tag{14.3}
$$

At inertia over $v$, the image of $c_P$ contains the entire $v$th coordinate subgroup and is trivial in the other coordinates. Those coordinate subgroups generate $\Delta_P$. Hence $c_P$ is surjective.

It follows that $c_P$ is an effective quotient of the ray class group for the least common multiple of the coordinate conductors:

$$
\operatorname{Cl}_{\mathfrak f_P}(F)\twoheadrightarrow\Delta_P.
\tag{14.4}
$$

This proof uses cross-local triviality. Separate surjections onto the $\Delta_v$ would not suffice: their product can have diagonal image.

### 14.2 Strict product twists

Let

$$
\Lambda_P=\mathcal O[\Delta_P]
\simeq
\bigotimes_{v\in P_{\mathrm{sc}},\mathcal O}\mathcal O[\Delta_v].
\tag{14.5}
$$

Assume one actual untwisted component-routed cube $C_P^0$ and its companion have already been constructed for the common product coefficient descent. Assume also that the one-place strict twist equivalence has been proved at every coordinate for every actual spectator tuple, on both represented deformation rings and complexes, and that every face is equivariant for the tautological product character attached to $c_P$.

Because $c_v$ is trivial at every other active place, the $v$th scalar twist treats all other coordinates as genuine spectators. The coordinate twists commute. Iterating the one-place strict twist gives

$$
R_P^{\mathrm{tw}}
\simeq
R_P^0\widehat\otimes_{\mathcal O}\Lambda_P,
\qquad
C_P^{\mathrm{tw}}
\simeq
\Lambda_P\otimes_{\mathcal O}C_P^0.
\tag{14.6}
$$

The companion uses the inverse product character. If the untwisted cube is concentrated in a finite free top module $M_P^0$, then

$$
M_P^{\mathrm{tw}}
\simeq\Lambda_P\otimes_{\mathcal O}M_P^0,
\tag{14.7}
$$

and the group-ring-valued pairing is the product of the regular group-ring pairing with the untwisted primary--companion pairing.

The determinant changes. If the untwisted determinant is $\delta$, the twist by a character tuple $\chi=(\chi_v)$ has determinant

$$
\delta_\chi
=\delta\prod_{v\in P_{\mathrm{sc}}}\chi_v^2.
\tag{14.8}
$$

No scalar character direction may be varied while pretending that the determinant remains $\delta$.

Formula (14.6) is not a construction of the untwisted cube. It is a strict identity on a supplied cube equivariant for the actual product quotient. Applying one-place twist formulas to separately chosen carriers would not produce it.

### 14.3 Fixed-place and auxiliary augmentation

Let $\mathfrak a_P$ be the augmentation ideal of $\Lambda_P$. From (14.6)--(14.7),

$$
R_P^{\mathrm{tw}}/\mathfrak a_PR_P^{\mathrm{tw}}
\simeq R_P^0,
\qquad
M_P^{\mathrm{tw}}/\mathfrak a_PM_P^{\mathrm{tw}}
\simeq M_P^0.
\tag{14.9}
$$

Because $M_P^{\mathrm{tw}}$ is free over $\Lambda_P$,

$$
\operatorname{Tor}_i^{\Lambda_P}
(\mathcal O,M_P^{\mathrm{tw}})=0
\qquad(i>0).
\tag{14.10}
$$

Augmenting any subset of the factors in (14.5) gives the corresponding face. Associativity of tensor products proves independence of the order of augmentation.

Auxiliary augmentation is similar in form but has different arithmetic input. Let $\Delta_Q$ be one effective auxiliary diamond group for the entire fixed-place cube. One needs:

- one common free $\Delta_Q$-torsor at every vertex;
- ordered-root idempotents compatible across all faces;
- the auxiliary oldspace comparison on every vertex;
- the represented-ring augmentation for the one product deformation problem;
- one common Hecke and deformation action; and
- compatibility of the primary--companion pairings and every fixed-place face map.

Under those conditions,

$$
R_{P,Q}\widehat\otimes_{\mathcal O[\Delta_Q]}\mathcal O
\simeq R_P,
\qquad
C_{P,Q}^{\pm}\otimes_{\mathcal O[\Delta_Q]}^L\mathcal O
\simeq C_{P,\varnothing}^{\pm}.
\tag{14.11}
$$

Totalization commutes with the derived base change. If the total top module is projective over the same auxiliary group algebra, positive augmentation Tor vanishes and the top module and pairing descend exactly.

Fixed scalar augmentation and auxiliary augmentation commute when both are realized by free tensor models over

$$
\Lambda_P\otimes_{\mathcal O}\mathcal O[\Delta_Q]
$$

and the structural actions commute. This is an actual common-package statement, not a consequence of separate exactness in the two directions.

### 14.4 Faithful images do not commute formally with base change

Exact module base change does not imply exact base change of its faithful acting image. Let

$$
A=k[[t]],\qquad M=A^2,
$$

and let a generator act by

$$
N=
\begin{pmatrix}
0&t\\
0&0
\end{pmatrix}.
\tag{14.12}
$$

The order generated by $1$ and $N$ is free of rank two over $A$, and it acts faithfully on $M$. After setting $t=0$, the specialized matrix $N$ is zero. The actual acting image on $M\otimes_Ak$ consists only of scalars, whereas the base change of the old order still contains a nonzero square-zero class.

Thus formation of an image algebra can acquire a kernel under specialization. The correct procedure before base faithfulness is known is:

1. base-change the carrier and its named actions;
2. define the faithful image anew on the specialized carrier; and
3. retain the canonical surjection from the base-changed old image to the new faithful image.

Injectivity follows later if a full base deformation-to-Hecke equality or another generic-rigidity theorem supplies a two-surjection argument. It is not inferred from module freeness.

### 14.5 Invariants, coinvariants, and norm

Let $\Delta$ be a finite $\ell$-group and let

$$
\Lambda=\mathcal O[\Delta].
$$

For a left $\Lambda$-module $M$, the coinvariants are

$$
M_\Delta
=\mathcal O\otimes_{\Lambda,\epsilon}M,
\tag{14.13}
$$

where $\epsilon$ is augmentation. The invariants are

$$
M^\Delta=\{m:\delta m=m\text{ for all }\delta\in\Delta\}.
$$

The norm map

$$
\operatorname{Nm}:M_\Delta\longrightarrow M^\Delta,
\qquad
\bar m\longmapsto\sum_{\delta\in\Delta}\delta m
\tag{14.14}
$$

is an isomorphism when $M$ is finite projective over $\Lambda$. It is enough to check the regular module, where the class of $1$ maps to

$$
N_\Delta=\sum_{\delta\in\Delta}[\delta].
$$

Orbit sum realizes coinvariants and pullback realizes invariants. Their composite on a lower-level module is multiplication by $|\Delta|$, which is usually not a unit. Thus raw trace and pullback are not inverse integrally.

For a strict product twist, freeness over $\Lambda_P$ makes every partial coinvariant operation exact. Taking coinvariants in two coordinate subgroups commutes because

$$
\mathcal O\otimes_{\mathcal O[\Delta_v]}
\left(
\mathcal O\otimes_{\mathcal O[\Delta_w]}M
\right)
\simeq
\mathcal O\otimes_{\mathcal O[\Delta_v\times\Delta_w]}M.
\tag{14.15}
$$

Without projectivity, higher group homology replaces exact coinvariants. This is the group-ring form of the augmentation Tor problem.

## 15. Finite-set reciprocity

### 15.1 The exact hypotheses

Once one joint carrier exists, trace descent is already a finite-set theorem. Let $M_P$ be a finite free $\mathcal O$-module with faithful image order

$$
\mathbb T_P\subseteq\operatorname{End}_{\mathcal O}(M_P).
$$

Assume that $\mathbb T_P$ is a complete local $\mathcal O$-algebra with residue field $k$;
this is the situation after localization at the fixed residual maximal ideal. The following
hypotheses are exact.

1. $\mathbb T_P$ is finite and $\mathcal O$-torsion-free.
2. Its generic fiber is reduced:

   $$
   \mathbb T_P\otimes_{\mathcal O}E
   \simeq\prod_{i=1}^sE_i.
   \tag{15.1}
   $$

3. Every factor in (15.1) occurs in $M_P\otimes E$ and is a noncharacter weight-two packet in the established Galois attachment range.
4. All factors have one fixed absolutely irreducible residual representation and one fixed determinant.
5. Every generic factor has, simultaneously at every $v\in P$, the named type, line, sign, monodromy, conductor, and component label.
6. At every place above the coefficient prime, the required integral realization is present, so the represented condition applies to every Artinian quotient.
7. Every integral inner-form or level comparison used to build $M_P$ satisfies its clean
   hypotheses. At each non-coefficient nonminimal place, the integral primary and companion
   lattices, required enhancement, and geometric local--global comparison have been supplied;
   the desired condition is cut out by a represented closed local ring, with ordered lines and
   special closures retained where needed.
8. Good Frobenius traces, the determinant coefficients, and every structural operator needed in the target order generate the entire faithful order. An adjoined sign, line, root, or diamond operator must be proved to belong to this generated order.

Separate one-place carriers cannot verify clause 5 for every factor of one common order. Likewise a trace order does not contain an independently adjoined structural operator merely because that operator has the desired generic eigenvalues.

### 15.2 Trace descent on the joint carrier

For each factor $E_i$, let

$$
\rho_i:G_{F,S}\longrightarrow\operatorname{GL}_2(E_i)
$$

be the attached representation. Their product is a representation over

$$
Q=\prod_iE_i.
$$

At every good place, its trace is the single Hecke operator $T_v\in\mathbb T_P$. Density of good Frobenius conjugacy classes and closedness of $\mathbb T_P$ in $Q$ imply

$$
\operatorname{tr}\rho_Q(g)\in\mathbb T_P
\qquad(g\in G_{F,S}).
\tag{15.2}
$$

The determinant is the fixed character and also lies in $\mathbb T_P^\times$.

Residual absolute irreducibility upgrades the order-valued character to matrices. Choose $g_1,\ldots,g_4$ whose residual matrices form a basis of $M_2(k)$. The trace Gram matrix

$$
\Gamma=
\left(\operatorname{tr}\rho_Q(g_ig_j)\right)_{i,j}
\tag{15.3}
$$

has unit determinant. For every $g$, define its coordinates by

$$
c_i(g)=
\sum_j(\Gamma^{-1})_{ij}
\operatorname{tr}\rho_Q(gg_j).
\tag{15.4}
$$

These coordinates belong to $\mathbb T_P$. They span a rank-four algebra

$$
\mathscr E=\sum_i\mathbb T_P\rho_Q(g_i)
\subseteq M_2(Q).
\tag{15.5}
$$

Multiplication constants are again trace coordinates, so $\mathscr E$ is an algebra. Its special fiber is $M_2(k)$. The multiplication map

$$
\mathscr E\otimes_{\mathbb T_P}\mathscr E^{\mathrm{op}}
\longrightarrow
\operatorname{End}_{\mathbb T_P}(\mathscr E)
\tag{15.6}
$$

is an isomorphism after reduction and hence an isomorphism. Thus $\mathscr E$ is an Azumaya algebra with split special fiber. Completeness and locality lift a rank-one matrix idempotent, giving

$$
\mathscr E\simeq M_2(\mathbb T_P).
\tag{15.7}
$$

Consequently, after fixing the residual identification, there is a continuous representation

$$
\rho_{\mathbb T_P}:
G_{F,S}\longrightarrow\operatorname{GL}_2(\mathbb T_P),
\tag{15.8}
$$

unique up to strict conjugacy, with the declared trace and determinant.

### 15.3 The deformation-to-Hecke map

Let $R_P$ represent the global product deformation problem with all framed local component
quotients and the fixed determinant. The integral comparisons and enhancements in clause 7
identify the required local structures over $\mathbb T_P$, while clause 5 puts every generic
factor of (15.8) on the desired local components. Since $\mathbb T_P$ is torsion-free and has
reduced generic fiber, a defining relation that vanishes in every factor vanishes in
$\mathbb T_P$. Thus (15.8) satisfies every represented local condition over the whole order
and on every Artinian quotient.

Universality gives

$$
R_P\longrightarrow\mathbb T_P.
\tag{15.9}
$$

Its image contains every trace and structural generator in clause 8. Therefore (15.9) is surjective.

**Theorem 15.1 (joint-carrier reciprocity).** Under the eight hypotheses of Section 15.1, the representation (15.8) exists, satisfies every named local condition simultaneously, and induces the surjection (15.9).

**Proof.** The trace-coordinate construction proves existence. Generic local factorization descends through the reduced torsion-free order. Trace and structural generation prove surjectivity. $\square$

The theorem does not construct $M_P$, prove its support, or show that every generic branch has the simultaneous labels. Those verifications must precede its application.

### 15.4 Structural generation and monodromy

Good traces generate the minimal trace order, but a simultaneous local problem can carry additional operators. Each requires a generation proof.

At a regular ordered place, let $a_v,b_v$ be the lifted Frobenius roots with $a_v-b_v$ a unit. The projector

$$
e_v=\frac{\rho_{\mathbb T_P}(\Phi_v)-b_v}{a_v-b_v}
\tag{15.10}
$$

belongs to the trace matrix algebra. If $\tau_v$ is a tame generator, then

$$
\operatorname{tr}\left(e_v\rho_{\mathbb T_P}(\tau_v)\right)
\tag{15.11}
$$

recovers the selected tame character. A local--global comparison can identify (15.11) with the diamond operator. This proves that the diamond lies in the trace order; it is not merely an extra symbol with matching eigenvalues.

At a special place, choose tame inertia $\sigma_v$ with unit tame coordinate and remove the finite scalar character $\xi_v$. Define

$$
N_{\mathbb T_P,v}
=t_\ell(\sigma_v)^{-1}
\left(
\xi_v(\sigma_v)^{-1}
\rho_{\mathbb T_P}(\sigma_v)-I
\right).
\tag{15.12}
$$

Generic local compatibility and reducedness give

$$
N_{\mathbb T_P,v}^2=0,
\qquad
\rho_{\mathbb T_P}(\Phi_v)
N_{\mathbb T_P,v}
\rho_{\mathbb T_P}(\Phi_v)^{-1}
=q_v^{-1}N_{\mathbb T_P,v}.
\tag{15.13}
$$

The entry ideal

$$
I_1(N_{\mathbb T_P,v})
\tag{15.14}
$$

cuts out the monodromy-zero locus. Nonzero generic monodromy does not mean that (15.12) remains nonzero in every Artinian quotient.

A sign operator, ordered line, or component idempotent is part of $\mathbb T_P$ only if it is recovered from formulas such as (15.10)--(15.12), belongs to the declared coefficient algebra, or is included in a separately represented structural order whose generation has been proved. Surjectivity of $R_P\to\mathbb T_P$ reaches only the algebra generated by universal deformation coordinates.

## 16. Two valid simultaneous conclusions

### 16.1 The all-component conclusion

The strongest valid formal conclusion can now be stated without abbreviating any premise.

**Theorem 16.1 (all-component finite-set criterion).** Let $\ell$ be the fixed odd coefficient prime and let $P$ be finite. Suppose:

1. one component-routed primary level cube and its strict adjoint companion have been constructed over one common face algebra;
2. every vertex is perfect and every raw one-place face satisfies the exact one-place integral comparison for its actual spectator tuple;
3. the residual total cube has no cohomology below degree $|P|$, equivalently all groups in (7.3) vanish;
4. a parity-indexed system of routed inner-form switches has been constructed with an integral comparison on every two-face, with all Néron, normalization, component, branch-Smith, conductor, component-route, and companion terms retained;
5. the two-face comparisons satisfy the braid identity on every three-face and the required chosen higher coherence;
6. the local relative component complexes have been defined over one common base with the global component carrier inserted once, the comparison maps in (10.6) exist, and the defect in (10.7) is zero with coherent null-homotopy;
7. the product deformation ring has the catenary and local-equidimensionality properties of
   Theorem 12.1, and for every irreducible component there is a prime satisfying all three
   conditions of that theorem for $M_P$; geometrically, this is supplied by a nonzero joint
   boundary class at a unique-component prime together with the stated maximal-depth equality;
8. every scalar direction comes from the cross-locally trivial product ray quotient of Section 14.1 and acts through the strict product twist on the actual cube;
9. fixed-place and auxiliary augmentation are realized by the free common tensor models of Section 14.3; and
10. the actual faithful order on $M_P$ satisfies the eight reciprocity hypotheses of Section 15.1.

Then $M_P$ is a simultaneous integral joint-new carrier, its construction and every routed residue map are independent of the order of $P$, and

$$
\operatorname{Supp}_{R_P}(M_P)=\operatorname{Spec}R_P.
\tag{16.1}
$$

The reciprocity map gives

$$
R_P\twoheadrightarrow\mathbb T_P.
\tag{16.2}
$$

Moreover,

$$
(R_P)_{\mathrm{red}}\xrightarrow{\sim}\mathbb T_P.
\tag{16.3}
$$

If $R_P$ is reduced, then (16.2) is an isomorphism.

**Proof.** Conditions 1--3 and Theorem 2.1 concentrate the primary cube in a finite projective top module and kill every positive base-change Tor group; (5.5) gives its companion dual. Conditions 4--6 and the coherent refinement of Theorem 11.1 give order-independent product residue with every correction term. Condition 7 and Theorem 12.1 give (16.1). Conditions 8--9 give coherent augmentation. Condition 10 and Theorem 15.1 give (16.2). The same condition includes hypotheses 1--2 of Section 15.1: $\mathbb T_P$ is $\mathcal O$-torsion-free and its generic fiber is reduced. Hence $\mathbb T_P\hookrightarrow\mathbb T_P\otimes_{\mathcal O}E$, and every nilpotent element of $\mathbb T_P$ is zero. Thus $\mathbb T_P$ is already reduced.

Let $I=\operatorname{Ann}_{R_P}(M_P)$. Full topological support gives $I\subseteq\sqrt{0}$. The target $\mathbb T_P=R_P/I$ is reduced, so $\sqrt{0}\subseteq I$. Hence $I=\sqrt{0}$, proving (16.3). If $R_P$ is reduced, $I=0$. $\square$

The theorem is an exact criterion. In the present source chain, conditions 3--7 are not consequences of the one-place inputs.

### 16.2 The pointed conclusion

The pointwise conclusion has a shorter premise.

**Theorem 16.2 (pointed finite-set criterion).** Let $x:R_P\to D$ be a characteristic-zero point with $D$ a domain. Suppose:

1. one actual final component-routed global cube and strict adjoint cube have been constructed over $\mathcal O$ after every fixed character specialization;
2. the primary carrier

   $$
   M_{P,x}=Q_P^{\mathrm{tf}}
   $$

   is nonzero and is paired perfectly with $K_P^-$ as in Theorem 13.1;
3. every generic factor of this one carrier is a noncharacter weight-two packet carrying simultaneously every named local label at every member of $P$ and the integral coefficient-prime realization;
4. the faithful image on $M_{P,x}$ satisfies the reciprocity hypotheses of Section 15.1, giving

   $$
   R_P\twoheadrightarrow\mathbb T_{P,x};
   $$

5. one irreducible component $\Xi_x$ through $x$ satisfies

   $$
   \mathfrak p_{\Xi_x}
   \in\operatorname{Supp}_{R_P}(M_{P,x}).
   $$

Then $x$ factors through $\mathbb T_{P,x}$ and, after passage to the fraction field of $D$,
is realized by an automorphic packet with all the named local data.

**Proof.** Theorem 13.1 gives the finite free carrier and its companion. Theorem 15.1 gives reciprocity only after the simultaneous generic branch verification. Theorem 12.2 then shows that the carrier annihilator lies in $\ker x$, so $x$ factors through the faithful image. Specializing (15.8) recovers the packet and its local labels. $\square$

No mixed concentration, all-component support, or ring equality occurs in this proof. Product residue is needed only if it is the method used to identify $\Xi_x$ or prove its occurrence.

### 16.3 The exact logical separation

The all-component theorem consumes a projective top module compatible with every base change. The pointed theorem consumes a torsion-free top quotient formed after specialization. These operations do not commute formally.

The all-component theorem proves a reduced ring comparison because support controls the entire nilradical. The pointed theorem proves only that one point kills the carrier annihilator.

The all-component theorem needs joint boundary witnesses on all components. The pointed theorem needs one component through one point. Neither theorem can replace that joint occurrence by separate one-place support.

Finally, the product-residue theorem belongs to the geometric identification of component labels and boundary classes. Once the relevant support statement has been proved, the annihilator argument does not use product residue a second time.

### 16.4 Proof-strategy map

The all-component route has the following dependency order:

$$
\begin{array}{c}
\text{joint coefficient descent and routed level cube}\\
\Downarrow\\
\text{mixed saturation and face-algebra hyper-Tor vanishing}\\
\Downarrow\\
\text{finite projective top module and adjoint dual}\\
\Downarrow\\
\text{coherent switching and product residue}\\
\Downarrow\\
\text{joint boundary witnesses and full support}\\
\Downarrow\\
\text{finite-set reciprocity}\\
\Downarrow\\
(R_P)_{\mathrm{red}}=\mathbb T_P.
\end{array}
\tag{16.4}
$$

The pointed route is shorter:

$$
\begin{array}{c}
\text{actual final cube after fixed specialization}\\
\Downarrow\\
Q_P^{\mathrm{tf}}\text{ and }K_P^-\\
\Downarrow\\
\text{simultaneous generic branch verification}\\
\Downarrow\\
\text{finite-set reciprocity on this carrier}\\
\Downarrow\\
\text{occurrence of the component through }x\\
\Downarrow\\
x\text{ factors through the faithful image}.
\end{array}
\tag{16.5}
$$

The diagrams expose the first blocker on each route. For the all-component route it is mixed sum-primitivity, once the one-place edges and actual cube are granted. For the pointed route it is the occurrence of the component through the named point, together with the branch verification needed before reciprocity.

A validated one-place chain is a third route. It does not pass through either simultaneous diagram, but every stage must reconstruct the one-place input on the new intermediate carrier. It is useful when the arithmetic geometry naturally supplies such a chain; it is not evidence for a simultaneous cube theorem.

## 17. Diagnostic examples

### 17.1 Two primitive planes with a nonprimitive sum

The two-place countermodel can be compressed to a smaller rank when one does not require the full incidence multiplicities. Let

$$
L=\mathcal O^3
$$

with basis $e_1,e_2,e_3$, and put

$$
U=\langle e_1,e_2\rangle,
\qquad
V=\langle e_1,e_2+\varpi e_3\rangle.
\tag{17.1}
$$

Both $U$ and $V$ are primitive rank-two submodules. Their sum is

$$
U+V=\langle e_1,e_2,\varpi e_3\rangle,
$$

so

$$
L/(U+V)\simeq\mathcal O/\varpi.
\tag{17.2}
$$

This is the smallest picture of the phenomenon. The individual inclusions have unit Smith invariants, but the relative change-of-basis matrix has determinant $\varpi$ in the new transverse direction.

The lesson is geometric: primitivity of each old lattice is a statement about its position relative to the ambient lattice; primitivity of their sum is a statement about their position relative to one another.

### 17.2 A residual class created by top torsion

Consider the two-term complex

$$
C=[\mathcal O\xrightarrow{\varpi}\mathcal O]
$$

in degrees one and two. Integrally,

$$
H^1(C)=0,
\qquad
H^2(C)=\mathcal O/\varpi.
$$

After reduction, the differential is zero, so

$$
H^1(C\otimes k)=k,
\qquad
H^2(C\otimes k)=k.
$$

The new degree-one class is

$$
\operatorname{Tor}_1^{\mathcal O}(H^2(C),k).
$$

This toy complex is the universal local shape behind Theorem 6.1. It shows why proving integral lower cohomology zero is not enough: top torsion falls one degree under reduction.

### 17.3 A diagonal ray image

Let $G=C_\ell$ and let

$$
c_1,c_2:G\longrightarrow C_\ell
$$

both be the identity. Each coordinate map is surjective, but

$$
(c_1,c_2):G\longrightarrow C_\ell\times C_\ell
$$

has diagonal image. Its group algebra is not

$$
\mathcal O[C_\ell\times C_\ell]
$$

but the quotient corresponding to the diagonal subgroup. Separate existence of ray characters therefore does not prove a product ray quotient. Cross-local triviality in Section 14.1 supplies the missing coordinate subgroups.

### 17.4 A faithful image lost after specialization

Return to (14.12). The abstract order

$$
\mathcal T=A[N]\simeq A[\epsilon]/(\epsilon^2),
\qquad \epsilon\mapsto N,
$$

acts faithfully on $A^2$. Base change gives

$$
\mathcal T\otimes_Ak\simeq k[\epsilon]/(\epsilon^2),
$$

but the actual image on $k^2$ sends $\epsilon$ to zero. Thus the base-changed order and the new faithful image differ.

This example also explains why exact augmentation of pairings is insufficient. The standard pairing on $A^2$ remains perfect after specialization, yet it does not detect the vanished operator. Faithfulness is a statement about the action map, not only about the module or its duality.

## 18. The first unresolved arithmetic theorem

### 18.1 Exact statement of the blocker

Assume every one-place input of Chapter 3 has been proved for all actual faces of a two-place
global level square, and assume the generic packet factorization (4.3), hence generic
concentration below degree two. Specialize every fixed character and auxiliary variable to
the final coefficient discrete valuation ring. Let $U,V\subseteq M_{11}$ be the two upper old
images.

The first unresolved finite-set theorem is:

> **Nonunit mixed sum-primitivity problem.** Outside the cubically compatible unit-Gram range
> of Corollaries 6.2 and 7.1, prove that
>
> $$
> U+V\subseteq M_{11}
> $$
>
> is primitive for every permitted pair of active places, every actual spectator tuple, and
> every routed primary component. When the companion cube is the strict shifted dual, its
> corresponding concentration is then formal and is not a second mixed hypothesis.

By Theorem 6.1, this is equivalent to each of the following:

$$
M_{11}/(U+V)\text{ is torsion-free};
\tag{18.1}
$$

$$
\operatorname{Tor}_1^{\mathcal O}
\left(M_{11}/(U+V),k\right)=0;
\tag{18.2}
$$

$$
H^1(C_{v,w}^+\otimes_{\mathcal O}k)=0.
\tag{18.3}
$$

Over a larger face algebra $A$, the required statement is stronger: all lower groups

$$
H^i(C_{v,w}^+\otimes_A^Lk)
$$

must vanish, including the full hyper-Tor shadows. Coefficient-DVR primitivity alone does not prove that.

The split-edge construction in Section 6.3 proves that one-place saturation and generic
concentration do not imply (18.1). Therefore nonunit sum-primitivity cannot be filled by a
formal induction. The unit-Gram result is a genuine positive several-place theorem only when
the projectors and their intersections belong to one cubically compatible contraction.

### 18.2 Consequences of resolving it

For two places, a proof of the face-algebra version would make the total cube homotopy equivalent to a finite projective module in degree two. The companion would become its perfect dual in degree zero. Every derived coefficient change would then be exact.

For a finite set, one must prove the higher groups in (7.3) vanish. A theorem asserting recursive injectivity on all iterated-new quotients would suffice. A genuine integral relative factorization of the form (8.1), with all factors projective over one common base, would also suffice and would prove order independence formally.

Neither extension follows from the two-place case alone. Pairwise vanishing on original faces
does not control a map on a double-new quotient, and a higher differential can create or
cancel classes invisible on the original two-faces. The explicit three-cube of Section 7.6
shows that even split raw edges and top-degree concentration on every original two-face do not
force top-degree concentration of the total cube.

### 18.3 Further independent geometric obligations

Even after mixed exactness is proved, the all-component theorem still requires independent geometric work:

1. construct the integral two-face switch comparisons in (9.5);
2. prove their three-face braid coherence and supply every higher chain-level filler;
3. construct the relative component factors without duplicating the global carrier;
4. retain Néron component and branch Smith Tor in their derived products;
5. construct the relative Beck--Chevalley comparisons in (10.6), including the Néron-component
   and normalized-branch Tor layers, and kill the residue defect (10.7);
6. produce joint boundary witnesses and maximal-depth points on the named product components; and
7. verify every simultaneous generic branch and structural generator before applying finite-set reciprocity.

For the pointed route, mixed exactness and full product residue can be bypassed. The first unresolved several-place assertion there is the occurrence (13.7) of the one global component through the named point, together with the simultaneous branch verification on the actual torsion-free carrier.

These obligations are ordered logically. The common global cube precedes its top carrier. The carrier and its generic factors precede reciprocity. Reciprocity precedes the annihilator factorization. A support theorem about a different carrier cannot be inserted at the end.

### 18.4 Exhaustion of the available comparison theorems

The preceding obstruction is not filled by an equivalent theorem elsewhere in the available
curriculum. The cited statements were checked at theorem level; their exact scopes are as
follows.

| Source | Existing result | Boundary relevant here |
|---|---|---|
| Book 84, Theorem 11.4 and Section 11.9 | Theorem 11.4 constructs an individual old projector when its Gram operator is a unit; Section 11.9 constructs the single $2^{|P|}$-fold common degeneracy source and the product Gram factorization | cubical compatibility of the individual projectors is a separate deduction or input; neither result by itself supplies it, and neither proves nonunit mixed saturation |
| Book 125, Theorem 15.1 | gives the split characteristic-zero packet decomposition with one two-dimensional multiplicity module $W_\Pi$ | proves (4.3) after splitting the packet block, not an integral relative factorization |
| Book 140, Theorem 15.1 and Section 14.2 | proves the conditional one-place integral comparison and records the several-prime derived-tensor implication | Section 14.2 explicitly assumes the common-carrier comparison and acting-base Tor-independence and warns against tensoring full global one-place complexes |
| Book 143, Sections 8.5, 9.1--9.3, 10.3, and 10.6 | constructs the product diamond algebra and proves functorial augmentation of the represented Taylor--Wiles deformation problem | expressly does not prove that a global arithmetic module is free over the diamond algebra and supplies no fixed-place mixed cube |
| Book 145, Proposition 11.1 and the support formalism of Chapter 11 | identifies faithfulness through associated primes and annihilators | supplies no arithmetic boundary witness on a missing product component |
| Book 152, Theorems 8.1 and 10.1 and Proposition 11.1 | proves exact diamond augmentation and regular-refinement idempotents on the common degeneracy source | source splitting is expressly conditional on degeneracy injectivity before it identifies old images; it proves no mixed quotient exactness |
| Book 170, Theorem 16.1 | constructs the order-valued representation and deformation-to-Hecke surjection for one finite controlling set | requires one actual faithful carrier, simultaneous verified generic local labels, integral coefficient-prime realization, and trace or structural generation |
| Book 174, Theorem 11.1 | packages the conditional one-place type complex, adjoint, component support, strict scalar twist, and augmentation | Section 12.1 expressly denies any sum-of-old-images, mixed-Ihara, product-component, or iterated-switch conclusion |
| Book 175, Section 8.3 | explicitly states that no theorem about two fixed nonminimal primes enters that book | supplies neither a finite-set tensor comparison nor joint support |
| Book 176, Propositions 8.2, 8.2A--8.2C, and 8.3 | proves the ordered quotient reduction, the DVR mixed-saturation equivalence, the torsion-free pointed carrier, generic packet commutation, and the joint ray quotient | Theorems 9.1 and 9.2 retain, respectively, the all-component simultaneous gates and the pointed simultaneous-branch and joint-occurrence gates |
| Book 177, Theorem 10.1 and Section 10.4 | consumes the Book 176 interfaces in its conditional potential-modularity theorem | explicitly records mixed exactness, routed product residue, joint support, and pointed joint occurrence as unresolved; it is not an upstream proof source |

The theorem-gap inventory agrees with this reading. Its retained several-place family consists
of mixed obstruction vanishing, derived product-residue or Beck--Chevalley comparison,
simultaneous component support, and coherent augmentation. Its entries for Books 176 and 177
classify the specialization-dependent common cube and the multi-place potential-modularity
interface as missing or conditional, not as proved results. Sections 14.2--14.3 above separate
this last item carefully: the joint scalar quotient and its strict twist are proved once the
equivariant cube is supplied, while auxiliary augmentation is formal from one common free
package; neither statement supplies the missing cube or mixed geometry.

The general derived and correspondence results elsewhere in the curriculum provide
totalization, base-change pasting, strict commutation of level correspondences, packetwise
rational factorization, and trace descent after a joint carrier exists. None identifies the
actual integral automorphic cube with a relative tensor product, constructs the routed
integral switch homotopies, or proves occurrence on a chosen global product component. Thus
the blockers of Sections 18.1 and 18.3 are irreducible relative to the available sources.

The remaining direct interfaces were also checked at their actual scope. Book 6, Theorem 6.1
gives the odd-order local--global character input used in Section 14.1; the standing
odd-$\ell$ convention keeps this application in its nonexceptional range. Book 14 supplies base-change morphisms, coefficient change, universal
coefficients, and signed totalization. Book 22 supplies normalization, graph, and branch
monodromy infrastructure. Books 123--124 supply transitive level maps, pull--trace adjunction,
transpose correspondences, and strict commutation at distinct adelic places. Book 175 is used
only to certify the one-prime boundary, and Book 177 only to reconcile the downstream
consumer. None of these source roles imports a later arithmetic conclusion into an earlier
formal argument.

## 19. Final synthesis

Several-place integral level change begins with one honest global object. Its vertices are the adjacent global levels, its edges are the two degeneracy maps, and its cubical signs produce a total old--new complex. The adjoint companion is the shifted derived dual of that cube. This construction uses the commutation of level changes at distinct adelic places, but exactness is a separate matter.

The generic packet block has a precise relative shape:

$$
G_{\Pi,P}\otimes
\operatorname{Tot}\left(\boxtimes_{v\in P}D_{\Pi,v}\right).
$$

The global multiplicity module is part of $G_{\Pi,P}$ and occurs once. Tensoring full global one-place complexes would duplicate it and is therefore wrong before any torsion question arises.

Integrally, the first new phenomenon is mixed saturation. At two places, under split-edge and generic-concentration hypotheses, residual middle cohomology is canonically

$$
\operatorname{Tor}_1^{\mathcal O}
\left(M_{11}/(U+V),k\right).
$$

It vanishes exactly when the sum of the two upper old images is primitive. The explicit rank-eight square shows that every edge can split and the generic cube can be exact while this sum is nonprimitive. For a larger face algebra, the full hyper-Tor spectral sequence must also vanish. For three or more places, the exact obstruction is the entire collection of lower residual cohomology groups of the total cube; pairwise checks do not replace them.

In the stronger cubically compatible split range, commuting old projectors make every required
sum and intersection a direct summand, so the total cube is concentrated in top degree in any
order. This is a genuine several-place theorem, but it does not cover the nonunit Gram faces
where level change carries congruence information.

There are two honest proofs of mixed concentration. One can prove injectivity successively on every iterated-new quotient. Or one can construct an integral relative product over one common base, with one global carrier and genuinely local projective factors. The second route makes concentration and order independence formal, but constructing that relative quasi-isomorphism is itself a several-place theorem.

Product residue is independent of automorphic mixed exactness. Distinct arithmetic fibers have empty intersection, so the replacement is a parity-indexed cube of curve and definite inner forms. The parity formula constructs its vertices and identifies its final inner form. Generic packet correspondence identifies the rational endpoint. Integral order independence requires two-face comparison maps carrying normalization, Néron, component, branch-Smith, conductor, routing, and adjoint data, together with three-face braid coherence. A nonzero extension class can vanish generically, so rational agreement does not supply these homotopies.

Support has two forms. The all-component theorem needs a nonzero maximal-depth witness on every product component and can yield a reduced ring comparison. The pointed theorem needs only the component through one named point and yields only factorization of that point through the faithful image. A reduced four-branch hypersurface shows that support can project onto every separate label while missing product components.

The torsion-free top of an actual finite cube gives a canonical pointed carrier even when mixed exactness fails. Its adjoint kernel is its perfect dual, and packetwise the global multiplicity occurs once. This construction is finite-level and must follow all nonflat character specializations. Its remaining arithmetic requirement is occurrence of the single global component through the named point.

Joint scalar augmentation is formal only after constructing cross-locally trivial ray characters whose product is an effective global quotient and after placing their strict product twist on the actual cube. Auxiliary augmentation likewise requires one common torsor and coherent vertexwise control. Exact module augmentation does not imply exact base change of a faithful image; the acting order must be defined anew after specialization until faithfulness supplies injectivity.

Finally, finite-set reciprocity is a theorem on an already constructed joint carrier. A torsion-free faithful order with reduced generic fiber, simultaneous branch labels, integral coefficient-prime realization, absolute residual irreducibility, and exact trace and structural generation carries one order-valued representation and receives a surjection from the product deformation ring. Separate one-place reciprocity statements do not verify those hypotheses for one common order.

The complete algebraic architecture is therefore closed, but the requested unconditional
arithmetic theorem is not. The first exact blocker beyond the source-closed unit-Gram range is
the nonunit sum-primitivity theorem of Section 18.1, followed for larger sets by mixed higher
Ihara vanishing. The one-place inputs do not prove either assertion, and the split-edge and
three-cube countermodels rule out a formal pairwise deduction. Beyond them lie the integral
routed two-face comparisons, higher coherence, relative product residue with its component
and branch Tor, and actual joint component occurrence with simultaneous branch verification.
A complete simultaneous theorem will be obtained only when those geometric statements are
constructed on the actual common carrier; until then, the all-component criterion and the
smaller pointed criterion mark the two rigorous endpoints.
