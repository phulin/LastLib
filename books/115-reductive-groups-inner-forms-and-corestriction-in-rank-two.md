# Reductive Groups, Inner Forms, and Corestriction in Rank Two

## Contents

1. [From matrices to forms](#1-from-matrices-to-forms)
   - [The organizing problem](#11-the-organizing-problem)
   - [Standing conventions](#12-standing-conventions)
   - [Three rank-two models](#13-three-rank-two-models)
   - [Descent as the unifying theme](#14-descent-as-the-unifying-theme)
2. [Root data and rank-two geometry](#2-root-data-and-rank-two-geometry)
   - [Characters and cocharacters](#21-characters-and-cocharacters)
   - [Roots, coroots, and reflections](#22-roots-coroots-and-reflections)
   - [Bases, chambers, and Cartan matrices](#23-bases-chambers-and-cartan-matrices)
   - [The reduced rank-two list](#24-the-reduced-rank-two-list)
   - [Central isogenies and lattices](#25-central-isogenies-and-lattices)
3. [Reductive groups over a field](#3-reductive-groups-over-a-field)
   - [Why geometric fibers govern the definition](#31-why-geometric-fibers-govern-the-definition)
   - [Tori, Borels, and parabolics](#32-tori-borels-and-parabolics)
   - [The root datum of a split group](#33-the-root-datum-of-a-split-group)
   - [The four basic degree-two groups](#34-the-four-basic-degree-two-groups)
   - [Derived groups, centers, and similitudes](#35-derived-groups-centers-and-similitudes)
4. [Restriction of scalars](#4-restriction-of-scalars)
   - [Remembering an extension as extra structure](#41-remembering-an-extension-as-extra-structure)
   - [Existence and the point formula](#42-existence-and-the-point-formula)
   - [Base change and geometric factors](#43-base-change-and-geometric-factors)
   - [Preservation theorems](#44-preservation-theorems)
   - [Characters, determinants, and norms](#45-characters-determinants-and-norms)
5. [Torsors and descent](#5-torsors-and-descent)
   - [Why a form is not a coordinate change](#51-why-a-form-is-not-a-coordinate-change)
   - [Torsors and cocycles](#52-torsors-and-cocycles)
   - [Twisting objects and representations](#53-twisting-objects-and-representations)
   - [Exactness for noncommutative classes](#54-exactness-for-noncommutative-classes)
   - [Examples and failure modes](#55-examples-and-failure-modes)
6. [Inner forms and central simple algebras](#6-inner-forms-and-central-simple-algebras)
   - [Inner versus outer twisting](#61-inner-versus-outer-twisting)
   - [Forms of the matrix groups](#62-forms-of-the-matrix-groups)
   - [The degree-two classification](#63-the-degree-two-classification)
   - [Local and global fingerprints](#64-local-and-global-fingerprints)
   - [What the root datum remembers](#65-what-the-root-datum-remembers)
7. [Quaternionic groups](#7-quaternionic-groups)
   - [Three groups attached to one algebra](#71-three-groups-attached-to-one-algebra)
   - [Smoothness, connectedness, and reductivity](#72-smoothness-connectedness-and-reductivity)
   - [Split coordinates and root subgroups](#73-split-coordinates-and-root-subgroups)
   - [Anisotropy and real forms](#74-anisotropy-and-real-forms)
   - [The quaternionic similitude group over a subfield](#75-the-quaternionic-similitude-group-over-a-subfield)
8. [Involutions and adjoint structures](#8-involutions-and-adjoint-structures)
   - [Why multiplication must be reversed](#81-why-multiplication-must-be-reversed)
   - [Kinds and types of involution](#82-kinds-and-types-of-involution)
   - [The canonical quaternion involution](#83-the-canonical-quaternion-involution)
   - [Adjoint involutions of bilinear forms](#84-adjoint-involutions-of-bilinear-forms)
   - [Hermitian and skew-hermitian forms](#85-hermitian-and-skew-hermitian-forms)
9. [Corestriction algebras](#9-corestriction-algebras)
   - [Multiplicative descent across a field extension](#91-multiplicative-descent-across-a-field-extension)
   - [The tensor-of-conjugates construction](#92-the-tensor-of-conjugates-construction)
   - [Degree, base change, and the Brauer class](#93-degree-base-change-and-the-brauer-class)
   - [The quadratic case in coordinates](#94-the-quadratic-case-in-coordinates)
   - [Local invariants and the exact splitting test](#95-local-invariants-and-the-exact-splitting-test)
10. [Trace, norm, and tensor induction](#10-trace-norm-and-tensor-induction)
    - [Additive and multiplicative transfer](#101-additive-and-multiplicative-transfer)
    - [The tensor norm of elements and modules](#102-the-tensor-norm-of-elements-and-modules)
    - [Polynomial laws and a necessary warning](#103-polynomial-laws-and-a-necessary-warning)
    - [Forms on tensor-induced spaces](#104-forms-on-tensor-induced-spaces)
    - [Parity of the tensor form](#105-parity-of-the-tensor-form)
11. [Corestriction of quaternion algebras](#11-corestriction-of-quaternion-algebras)
    - [Possible algebra structures](#111-possible-algebra-structures)
    - [Ramification counted over base places](#112-ramification-counted-over-base-places)
    - [Quadratic extensions and paired ramification](#113-quadratic-extensions-and-paired-ramification)
    - [Examples and counterexamples](#114-examples-and-counterexamples)
    - [Splittings and minimal modules](#115-splittings-and-minimal-modules)
12. [Symplectic spaces and similitude groups](#12-symplectic-spaces-and-similitude-groups)
    - [Alternating forms and their matrices](#121-alternating-forms-and-their-matrices)
    - [Isometries and similitudes](#122-isometries-and-similitudes)
    - [The rank-two coincidence](#123-the-rank-two-coincidence)
    - [Hyperbolic enlargement](#124-hyperbolic-enlargement)
    - [Integral lattices and perfectness](#125-integral-lattices-and-perfectness)
13. [Quaternionic symplectic representations](#13-quaternionic-symplectic-representations)
    - [The trace-pairing construction](#131-the-trace-pairing-construction)
    - [The multiplier calculation](#132-the-multiplier-calculation)
    - [The tensor-corestriction construction](#133-the-tensor-corestriction-construction)
    - [Parity repair and faithful realizations](#134-parity-repair-and-faithful-realizations)
    - [Polarizations and positivity at infinity](#135-polarizations-and-positivity-at-infinity)
14. [The rank-two structural package](#14-the-rank-two-structural-package)
    - [A dependency-safe construction sequence](#141-a-dependency-safe-construction-sequence)
    - [Exact hypotheses at a glance](#142-exact-hypotheses-at-a-glance)
    - [Common normalization traps](#143-common-normalization-traps)
    - [Conclusion](#144-conclusion)

## 1. From matrices to forms

The opening chapter fixes the questions and normalizations that govern the book. Its purpose is not to front-load definitions, but to show why four apparently separate operations—classifying groups, moving between fields, twisting, and constructing alternating forms—must be developed together. The three guiding models will recur in progressively less split form.

### 1.1 The organizing problem

The group of invertible $2\times2$ matrices is easy to write down, but the arithmetic groups that arise from it are rarely given in that coordinate form. A group may become a matrix group only after extending the ground field. It may naturally live over a larger field and have to be viewed over a smaller one. Its defining two-dimensional representation may disappear under descent, while a larger tensor representation survives. Finally, a moduli problem with polarizations requires not merely a linear representation but one preserving an alternating form up to a scalar.

This book develops one chain of ideas that resolves all four difficulties. Root data identify what remains invariant after coordinates are forgotten. Reductive groups provide the geometric class in which that invariant is effective. Restriction of scalars moves a group between fields without discarding its points. Torsors and twisting classify the ways in which a split group can descend. Quaternion algebras supply every inner degree-two form. Corestriction then transfers the noncommutative algebra back across a field extension, and involutions convert its trace and norm into the alternating pairings needed for polarized constructions.

The emphasis is rank two in the representation-theoretic sense: the basic object acts on a two-dimensional space after a splitting. Its derived root system is often of type $A_1$, while restriction of scalars produces several conjugate $A_1$ factors. We also develop genuine semisimple rank-two root data because they explain tensor products, accidental low-rank identifications, and the boundary between the degree-two story and higher rank.

### 1.2 Standing conventions

Unless a statement says otherwise, fields have characteristic different from $2$. A separable closure of a field $k$ is denoted $k^s$, and $\Gamma_k=\operatorname{Gal}(k^s/k)$. All algebraic groups over a field are affine and of finite type. A central simple algebra has finite dimension over its center. If $A$ has degree $n$, then $\dim A=n^2$, and its reduced trace and reduced norm are denoted $\operatorname{Trd}_A$ and $\operatorname{Nrd}_A$.

The preceding treatment of quaternion algebras supplies a precise input boundary: presentations and canonical conjugation, reduced trace and norm, the split--division dichotomy, local invariants, the global ramification classification, and the restriction--corestriction formulas for Brauer classes. We use those results with their established normalizations. Root data, algebraic-group descent, restriction of scalars, algebra corestriction, involutions, and the symplectic representations are developed here; none of them is inferred merely from the quaternion ramification dictionary.

For a finite separable extension $E/k$, scalar restriction is written $\operatorname{Res}_{E/k}$. Algebra transfer is written $\operatorname{Cor}_{E/k}$. These operations have opposite directions:

$$
\operatorname{Res}_{E/k}:\{E\text{-objects}\}\longrightarrow\{k\text{-objects}\},
\qquad
\operatorname{Cor}_{E/k}:\operatorname{Br}(E)\longrightarrow\operatorname{Br}(k).
$$

The first preserves point functors; the second is multiplicative descent of central simple algebras. Their similar English names should never be allowed to blur this distinction.

For bilinear forms we use the convention that an involution $*$ is adjoint to a form $\psi$ when

$$
\psi(ax,y)=\psi(x,a^*y).
$$

A symplectic form means a nondegenerate alternating bilinear form. In characteristic different from $2$, alternating is equivalent to skew-symmetric. Over a general base ring, alternating is the condition $\psi(x,x)=0$ and is the safer definition.

### 1.3 Three rank-two models

Three examples guide the entire development.

First, $\operatorname{GL}_2$ acts on $k^2$. Its determinant is simultaneously the ordinary determinant and the multiplier of the standard alternating form

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\qquad
g^{\mathsf t}Jg=(\det g)J.
$$

Second, if $B$ is a quaternion algebra over $k$, then $B^\times$ becomes $\operatorname{GL}_2$ over any splitting field. The reduced norm replaces determinant, canonical conjugation replaces the adjugate, and the norm-one subgroup becomes $\operatorname{SL}_2$.

Third, if $E/k$ is finite separable and $B/E$ is quaternionic, the group $\operatorname{Res}_{E/k}B^\times$ becomes a product of copies of $\operatorname{GL}_2$ over $k^s$. The tensor product of the standard two-dimensional representations has dimension $2^{[E:k]}$. It descends precisely through the corestriction algebra. This third model explains why a group built from degree-two factors may act naturally on a much larger symplectic space.

### 1.4 Descent as the unifying theme

Over $k^s$, all the groups in the preceding examples are elementary matrix groups. The arithmetic information lies in how $\Gamma_k$ permutes the factors and changes their coordinates. There are two distinct effects.

An **outer** effect changes the root datum, for example by permuting vertices of a Dynkin diagram. An **inner** effect conjugates matrices and therefore leaves the based diagram unchanged. Quaternion algebras encode the latter effect in degree two. Restriction of scalars introduces the former permutation action on conjugate factors even when the original group over $E$ was split.

The practical lesson is that “split after extending scalars” is only the beginning of a classification. One must record the descent action, decide whether it is inner, and then find a representation whose descent obstruction vanishes. Corestriction is the device that records that obstruction without prematurely choosing matrices.

## 2. Root data and rank-two geometry

Coordinates conceal the difference between a group and its central quotients. Root data retain exactly the integral information that survives conjugation: weights, coweights, reflections, and their lattices. This chapter builds that language from tori, then uses rank two as a complete laboratory for diagram shape, duality, and central isogeny.

### 2.1 Characters and cocharacters

A diagonalizable group is understood through its one-dimensional weights. Let $T$ be a split torus over $k$. Its character and cocharacter groups are

$$
X^*(T)=\operatorname{Hom}(T,\mathbf G_m),
\qquad
X_*(T)=\operatorname{Hom}(\mathbf G_m,T).
$$

They are finite free abelian groups in perfect duality. If $\chi\in X^*(T)$ and $\lambda\in X_*(T)$, the composite $\chi\circ\lambda$ is $t\mapsto t^n$ for a unique integer $n$; write

$$
\langle\chi,\lambda\rangle=n.
$$

For $T=\mathbf G_m^r$, choosing coordinates identifies both lattices with $\mathbf Z^r$ and the pairing with the dot product. The lattices, rather than the vector spaces obtained after tensoring with $\mathbf Q$, are decisive. Replacing a lattice by a finite-index sublattice changes the center and the available representations even though it leaves the rational root system unchanged.

For a nonsplit torus the same lattices are formed over $k^s$, but they carry a continuous $\Gamma_k$-action through a finite quotient. This action is the descent datum. For example,

$$
X^*(\operatorname{Res}_{E/k}\mathbf G_m)
\cong\mathbf Z[\operatorname{Hom}_k(E,k^s)],
$$

with $\Gamma_k$ permuting the basis of embeddings.

### 2.2 Roots, coroots, and reflections

A root datum is a quadruple

$$
\mathcal R=(X,\Phi,X^\vee,\Phi^\vee)
$$

consisting of perfectly paired finite free abelian groups $X$ and $X^\vee$, finite subsets $\Phi\subset X$ and $\Phi^\vee\subset X^\vee$, and a bijection $\alpha\leftrightarrow\alpha^\vee$ such that

$$
\langle\alpha,\alpha^\vee\rangle=2
$$

and the reflections

$$
s_\alpha(x)=x-\langle x,\alpha^\vee\rangle\alpha,
\qquad
s_\alpha^\vee(y)=y-\langle\alpha,y\rangle\alpha^\vee
$$

preserve $\Phi$ and $\Phi^\vee$ compatibly. The group generated by the $s_\alpha$ is the Weyl group $W$.

Why are coroots separate data? Root lengths disappear from an abstract set of reflecting hyperplanes. The coroot records the integral normalization of the reflection. In type $B_2$ and $C_2$, exchanging roots and coroots exchanges long and short roots; the two root systems have the same Weyl group but different integral representation theory.

A root datum is **reduced** if $2\alpha\notin\Phi$ whenever $\alpha\in\Phi$. The root data of connected reductive groups are reduced. Nonreduced systems occur naturally in relative root theory over nonsplit fields, so reducedness should not be silently transferred to every relative setting.

### 2.3 Bases, chambers, and Cartan matrices

A base $\Delta=\{\alpha_1,\ldots,\alpha_r\}$ is a set of roots such that every root is an integral combination of the $\alpha_i$ with either all coefficients nonnegative or all nonpositive. It chooses a positive chamber. The Cartan matrix is

$$
C=(c_{ij}),
\qquad c_{ij}=\langle\alpha_j,\alpha_i^\vee\rangle.
$$

Our row is indexed by the coroot. Thus $c_{ii}=2$, off-diagonal entries are nonpositive, and $c_{ij}=0$ exactly when $c_{ji}=0$. This row convention matters in the nonsimply-laced cases.

Changing the chamber changes the base but not the root datum: the Weyl group acts simply transitively on chambers. A based root datum adds $\Delta$ and exposes diagram automorphisms. Forgetting the base is geometrically natural; restoring one is useful for classification and descent because a Borel subgroup chooses a chamber.

### 2.4 The reduced rank-two list

For an irreducible reduced rank-two root system, after ordering the simple roots the Cartan matrix is one of

$$
A_2:\ \begin{pmatrix}2&-1\\-1&2\end{pmatrix},
\qquad
B_2:\ \begin{pmatrix}2&-2\\-1&2\end{pmatrix},
\qquad
G_2:\ \begin{pmatrix}2&-3\\-1&2\end{pmatrix}.
$$

The reducible case is

$$
A_1\times A_1:\ \begin{pmatrix}2&0\\0&2\end{pmatrix}.
$$

The product $c_{12}c_{21}$ is respectively $1,2,3,$ or $0$, and determines the angle between the simple roots. A short root is the one whose coroot is long. Reversing the arrows exchanges $B_2$ and $C_2$; their root data are dual.

The degree-two quaternionic groups themselves have semisimple rank one, type $A_1$. Rank two enters after two conjugate factors are present, as for a quadratic restriction of scalars. Over a separable closure its derived root system is $A_1\times A_1$, while the ground-field Galois action may interchange the two vertices. Calling this group “split of type $A_1\times A_1$” over the ground field would erase the essential descent action.

It is useful to see the four systems rather than only their matrices. For $A_1\times A_1$, the roots are $\{\pm\alpha_1,\pm\alpha_2\}$; the reflections commute and the Weyl group has order four. For $A_2$, there are six roots,

$$
\pm\alpha_1,\quad \pm\alpha_2,\quad
\pm(\alpha_1+\alpha_2),
$$

and the Weyl group is the symmetry group of a triangle. For $B_2$ there are eight roots and a dihedral Weyl group of order eight. For $G_2$ there are twelve roots and a dihedral Weyl group of order twelve. These counts follow by successively reflecting the simple roots. They also show why $c_{12}c_{21}$ cannot exceed three in a finite reduced system: a larger product makes the two generating reflections produce an infinite dihedral group.

The nonsimply-laced orientation is not decoration. With the row convention above, the $B_2$ matrix satisfies

$$
\langle\alpha_2,\alpha_1^\vee\rangle=-2,
\qquad
\langle\alpha_1,\alpha_2^\vee\rangle=-1.
$$

Thus $\alpha_1$ is short and $\alpha_2$ is long. Dualizing transposes the matrix and reverses this designation. An argument using only the unoriented square diagram cannot distinguish a group from its dual root datum.

### 2.5 Central isogenies and lattices

The roots span a sublattice $Q\subset X$, the root lattice. The coroots span $Q^\vee\subset X^\vee$. The weight lattice is

$$
P=\{x\in X\otimes\mathbf Q:\langle x,\alpha^\vee\rangle\in\mathbf Z
\text{ for all }\alpha\in\Phi\},
$$

and similarly for $P^\vee$. Semisimple root data lie between $Q$ and $P$. The adjoint form has character lattice $Q$; the simply connected form has cocharacter lattice $Q^\vee$.

For type $A_1$, choose a fundamental weight $\omega$ with root $\alpha=2\omega$. Then

$$
X^*(\operatorname{SL}_2\text{ torus})=\mathbf Z\omega,
\qquad
X^*(\operatorname{PGL}_2\text{ torus})=\mathbf Z\alpha.
$$

The central isogeny $\operatorname{SL}_2\to\operatorname{PGL}_2$ is invisible over $\mathbf Q$ but visible as the index-two inclusion $\mathbf Z\alpha\subset\mathbf Z\omega$. This is the simplest counterexample to the claim that a rational root system determines a group.

For $A_1\times A_1$, the gap between root and weight lattices has order four. Intermediate lattices produce quotients of $\operatorname{SL}_2\times\operatorname{SL}_2$ by central subgroups of order two. The diagonal quotient

$$
(\operatorname{SL}_2\times\operatorname{SL}_2)/
\{(1,1),(-1,-1)\}
$$

is especially important: its four-dimensional tensor representation is faithful, whereas either factor's two-dimensional representation does not descend through the diagonal quotient. This calculation anticipates the central kernel of tensor induction.

Dominant weights give a second interpretation. A weight $\lambda$ is dominant when $\langle\lambda,\alpha_i^\vee\rangle\ge0$ for every simple root. In type $A_1$, the standard representation has highest weight $\omega$, while the adjoint three-dimensional representation has highest weight $2\omega=\alpha$. The latter descends to $\operatorname{PGL}_2$; the former does not. The integral lattice decides which representation belongs to which central form.

**Classification theorem for split groups.** Split connected reductive groups over $k$, equipped with a split maximal torus and a Borel containing it, are classified up to unique pinned isomorphism by based root data.

**Proof architecture.** The assertion has an existence part and a rigidity part. For existence, begin with the Cartan integers of the based datum. For each root introduce a copy $U_\alpha\cong\mathbf G_a$ and let the split torus with character lattice $X$ act on it through $\alpha$. The rank-one subgroups generated by $U_\alpha$ and $U_{-\alpha}$ are the prescribed forms of $\operatorname{SL}_2$ or $\operatorname{PGL}_2$ according to the lattice between the root and weight lattices. For $\alpha+\beta\ne0$, the root-string calculation gives integral constants $N_{\alpha,\beta;i,j}$ and the relations

$$
[x_\alpha(u),x_\beta(v)]
=\prod_{i,j>0}x_{i\alpha+j\beta}
(N_{\alpha,\beta;i,j}u^iv^j),
$$

where the product ranges over roots $i\alpha+j\beta$ in a fixed order. The root-string identities imply the compatibility of these relations in every rank-two subsystem. Every nonproportional pair of roots lies in such a subsystem, while opposite roots are governed by the rank-one relation. The relations therefore construct the split pinned group. Passing from the simply connected semisimple datum to an intermediate character lattice is quotient by the corresponding finite central diagonalizable subgroup. In the reductive case one forms the product with the prescribed split central torus and takes the central quotient determined by $X$; this retains the required finite overlap between the center and the derived group.

For rigidity, an isomorphism of based root data first gives the unique isomorphism of the pinned split tori. The pinning identifies every simple root homomorphism $x_\alpha:\mathbf G_a\to U_\alpha$; the rank-one relations then identify the negative simple root groups, and Weyl conjugation identifies every remaining root group. The displayed commutator relations show that these identifications respect multiplication. The big cell

$$
U^-\times T\times U\longrightarrow G
$$

is a dense open subscheme, so two group morphisms agreeing on the pinned torus and all root groups agree everywhere. Existence and uniqueness of the pinned isomorphism follow. Notice where rank two enters the verification: all compatibility among root-group commutators reduces to the systems $A_1\times A_1$, $A_2$, $B_2$, and $G_2$ listed above.

The word “pinned” removes residual conjugation by the torus through chosen root vectors. Without a pinning, the classification is up to isomorphism but not unique isomorphism. This distinction becomes decisive when descent cocycles are compared.

## 3. Reductive groups over a field

Root data become arithmetic only when attached to groups that may be nonsplit over the ground field. We therefore pass from combinatorics to geometry, emphasizing which assertions are geometric, which depend on rational points, and which are altered by anisotropy. The degree-two groups at the end provide the split models for every later quaternionic form.

### 3.1 Why geometric fibers govern the definition

A connected smooth affine group $G/k$ is **reductive** if its unipotent radical after extension to an algebraic closure is trivial. It is **semisimple** if, in addition, its connected center is trivial. This geometric definition is stable under arbitrary field extensions and does not confuse anisotropy with absence of roots.

A torus is reductive even when it has no nontrivial unipotent subgroups over $k$ or over $k^s$. A quaternionic norm-one group may contain no nontrivial split torus over $k$ and still become $\operatorname{SL}_2$ over $k^s$. Conversely, a smooth connected solvable group can have no visibly troublesome $k$-points yet possess a nontrivial geometric unipotent radical. Reductivity must therefore be tested geometrically, not from an abstract group of rational points.

### 3.2 Tori, Borels, and parabolics

A maximal torus $T\subset G$ is a torus maximal for inclusion. Over $k^s$, all maximal tori are conjugate. A Borel subgroup is a maximal connected solvable subgroup; every Borel contains a maximal torus. A group is **quasi-split** if it has a Borel defined over $k$, and **split** if it has a split maximal torus over $k$.

These notions are distinct. The projective unit group of a quaternion division algebra is not quasi-split: a Borel after splitting would descend a rational point on its conic of minimal right ideals, forcing the algebra to split. A nonsplit torus, by contrast, is its own Borel and is therefore quasi-split under the standard definition for reductive groups, though it is not split.

Parabolic subgroups contain Borels after geometric scalar extension. For $\operatorname{GL}(V)$ they are stabilizers of flags. A quaternion division algebra has no nontrivial right ideal, so its projective unit group has no proper parabolic over $k$. This is the group-theoretic shadow of anisotropy.

There is a precise geometric bridge. For a degree-$n$ central simple algebra $A$, the variety of right ideals of reduced dimension $r$ is a twisted Grassmannian. Its stabilizer in $\operatorname{PGL}_1(A)$ is a parabolic, and every parabolic arises this way after descent. In degree two the only proper choice is $r=1$, so the variety is the conic of minimal right ideals. A $k$-parabolic exists exactly when this conic has a $k$-point, hence exactly when $A$ splits. This explains at once the equivalence among a Borel, a minimal ideal, a conic point, and split matrices.

Over a perfect field, every reductive group has maximal tori defined over the field, but they need not be split. In a quaternion division algebra, a quadratic field $K\subset B$ gives a maximal torus

$$
K^\times/k^\times\subset PB^\times,
$$

and its norm-one subgroup gives a maximal torus in $B^1$. This torus becomes diagonal after extending to $K$, even though no diagonalization exists over $k$.

### 3.3 The root datum of a split group

Let $G$ be split reductive, $T$ a split maximal torus, and $B\supset T$ a Borel. Conjugation of $T$ on the Lie algebra of $G$ gives

$$
\operatorname{Lie}(G)=\operatorname{Lie}(T)\oplus
\bigoplus_{\alpha\in\Phi}\mathfrak g_\alpha.
$$

The nonzero weights are the roots. Each root subgroup determines a coroot $\alpha^\vee:\mathbf G_m\to T$, normalized by the embedded rank-one subgroup. The resulting based root datum is independent of all choices up to conjugacy.

For a general reductive group, form the root datum over $k^s$. The Galois action is well defined only up to Weyl conjugacy until a compatible pinning is chosen. The induced action on the based root datum is the **outer action**. Inner forms have the same outer action; they differ by cocycles valued in the adjoint group.

One can see the ambiguity directly. If $T$ and $T'$ are maximal tori and $gTg^{-1}=T'$ over $k^s$, replacing $g$ by $gt$ with $t\in T(k^s)$ changes no Weyl element, while replacing it by an element of the normalizer changes the identification by $W$. Choosing a Borel reduces the normalizer ambiguity, and choosing root vectors removes the remaining torus rescalings. A pinning is therefore the right rigid object for defining an outer action.

For a split reductive group,

$$
\dim G=\operatorname{rank}T+|\Phi|.
$$

The toral Lie algebra contributes the rank and each root space contributes one dimension. Thus $\operatorname{SL}_2$ has dimension $1+2=3$, a semisimple group of type $A_1\times A_1$ has dimension six, and the simply connected group of type $A_2$ has dimension $2+6=8$.

### 3.4 The four basic degree-two groups

Let $V$ be two-dimensional over $k$.

- $\operatorname{GL}(V)$ is reductive of dimension $4$, with center $\mathbf G_m$ and derived group $\operatorname{SL}(V)$.
- $\operatorname{SL}(V)$ is simply connected semisimple of type $A_1$ and dimension $3$.
- $\operatorname{PGL}(V)$ is adjoint semisimple of type $A_1$ and dimension $3$.
- $\operatorname{GSp}(V,\psi)$ is the group of symplectic similitudes of a nonzero alternating form.

In dimension two there is an exceptional equality

$$
\operatorname{GSp}(V,\psi)=\operatorname{GL}(V),
\qquad \nu(g)=\det(g),
$$

and its isometry subgroup is $\operatorname{Sp}(V,\psi)=\operatorname{SL}(V)$. This coincidence fails in dimension at least four. It is the reason determinant, reduced norm, and symplectic multiplier can be treated as three forms of the same character in the rank-two setting.

### 3.5 Derived groups, centers, and similitudes

For connected reductive $G$, the derived subgroup $G^{\mathrm{der}}$ is semisimple, the connected center $Z(G)^\circ$ is a torus, and multiplication gives a central isogeny

$$
Z(G)^\circ\times G^{\mathrm{der}}\longrightarrow G.
$$

It need not be an isomorphism. For $\operatorname{GL}_2$, the map $\mathbf G_m\times\operatorname{SL}_2\to\operatorname{GL}_2$ has kernel generated by $(-1,-I)$. This finite overlap accounts for many parity conditions on weights.

A similitude character $\nu:G\to\mathbf G_m$ often isolates the central torus while $\ker(\nu)^{\circ}$ carries the semisimple geometry. One must distinguish $\ker\nu$ from its identity component in general. In the groups constructed later the kernel will be connected, but that conclusion will be proved from a split model rather than assumed.

## 4. Restriction of scalars

Many arithmetic groups are naturally defined over a field $E$ but must participate in constructions over a smaller field $k$. Restriction of scalars performs this move without choosing a basis and without losing the $E$-linear structure. The geometric product formula developed here will later explain both the multiplication of ranks and the Galois permutation of tensor factors.

### 4.1 Remembering an extension as extra structure

Suppose $E/k$ is finite. An $E$-vector space can be viewed as a larger $k$-vector space, but this forgetful operation retains the $E$-action. Restriction of scalars performs the analogous operation for varieties and groups. It is not ordinary scalar restriction in notation alone: it represents a new functor over $k$ whose test points remember tensoring with $E$.

This construction is indispensable when arithmetic data are defined over a totally real field but the final polarization is rational. It packages all embeddings of $E$ at once and makes the Galois permutation of those embeddings visible.

### 4.2 Existence and the point formula

Let $E/k$ be finite locally free and let $X$ be an affine $E$-scheme of finite type. The restriction $\operatorname{Res}_{E/k}X$ is characterized by

$$
(\operatorname{Res}_{E/k}X)(R)=X(E\otimes_kR)
$$

for every $k$-algebra $R$. It exists as an affine $k$-scheme of finite type. If $X$ is a group, the representing object is a group and the identity above is functorial as a group identity.

For example,

$$
(\operatorname{Res}_{E/k}\mathbf G_m)(k)=E^\times,
\qquad
(\operatorname{Res}_{E/k}\operatorname{GL}_n)(k)=\operatorname{GL}_n(E).
$$

If $V$ has $E$-dimension $n$, its underlying $k$-space has dimension $n[E:k]$, and the natural action gives a closed embedding

$$
\operatorname{Res}_{E/k}\operatorname{GL}_E(V)
\hookrightarrow\operatorname{GL}_k(V).
$$

The image is the centralizer of the $E$-action. Thus restriction of scalars remembers more than a large vector space: it remembers which endomorphisms are $E$-linear.

### 4.3 Base change and geometric factors

Assume now that $E/k$ is finite separable. Over $k^s$ there is a canonical decomposition

$$
E\otimes_k k^s\cong\prod_{\tau:E\hookrightarrow k^s}k^s.
$$

Consequently

$$
(\operatorname{Res}_{E/k}X)_{k^s}
\cong\prod_{\tau:E\hookrightarrow k^s}{}^\tau X,
$$

where ${}^\tau X$ is obtained by using the embedding $\tau$ on coefficients. The Galois group permutes these factors and acts inside them through the descent datum.

This formula is the decisive proof device for geometric properties. It also gives

$$
\dim_k\operatorname{Res}_{E/k}X=[E:k]\dim_E X.
$$

If $E/k$ is inseparable, the tensor product with an algebraic closure can contain nilpotents rather than split as a product of fields. Smoothness and reductivity statements then need additional hypotheses. Separability is not cosmetic.

Restriction of scalars is characterized by an adjunction. For a $k$-scheme $Y$ and an $E$-scheme $X$ in the affine finite-type setting,

$$
\operatorname{Hom}_k(Y,\operatorname{Res}_{E/k}X)
\cong\operatorname{Hom}_E(Y_E,X).
$$

Taking $Y=\operatorname{Spec}R$ recovers the point formula. The adjunction makes morphisms descend without coordinates: a representation over $E$ produces a $k$-morphism when its target is also restricted, while a map into a genuinely $k$-defined target requires an invariant construction such as trace or norm.

Restriction is transitive. If $k\subset E\subset L$ are finite extensions, then

$$
\operatorname{Res}_{L/k}X
\cong\operatorname{Res}_{E/k}(\operatorname{Res}_{L/E}X).
$$

Both sides represent $R\mapsto X(L\otimes_kR)$. This canonical identity prevents choices of intermediate bases from entering tower arguments.

### 4.4 Preservation theorems

**Theorem 4.1.** Let $E/k$ be finite separable and $G/E$ a smooth connected affine group. Then $\operatorname{Res}_{E/k}G$ is smooth and connected. If $G$ is reductive, semisimple, or a torus, so is $\operatorname{Res}_{E/k}G$.

**Proof strategy.** Pass to $k^s$, use the product decomposition, and descend properties stable under separable extension.

**Proof.** Each conjugate ${}^\tau G$ has the stated property. Finite products preserve smoothness, connectedness, and the torus condition. The geometric unipotent radical of a product is the product of the geometric unipotent radicals, so reductivity is preserved. Likewise the connected center of a product is the product of the connected centers, proving the semisimple assertion. Each property descends from $k^s$ to $k$. $\square$

The theorem fails in this form without separability. For a purely inseparable extension, restriction of a smooth group can acquire nonreduced geometric fibers. The correct general theory uses more careful hypotheses; it is unnecessary for the characteristic-zero applications here.

Connectedness deserves emphasis. A product of connected geometric factors is connected, and connectedness descends under field extension. Rational points need not reflect this: a connected group may have a disconnected real Lie group, as $\mathbf G_m(\mathbf R)=\mathbf R^\times$ shows. The theorem concerns the algebraic group, not the topology of $G(k)$.

For root data, restriction has an induction description. If $T/E$ is a torus, then

$$
X^*(\operatorname{Res}_{E/k}T)
\cong\operatorname{Ind}_{\Gamma_E}^{\Gamma_k}X^*(T).
$$

For reductive $G/E$, its geometric root datum becomes the direct sum of the conjugate root data indexed by the embeddings of $E$. For quadratic $E/k$ and type $A_1$, this gives $A_1\times A_1$ with the two components interchanged by Galois. The relative root system over $k$ need not equal this absolute product.

### 4.5 Characters, determinants, and norms

The torus $\operatorname{Res}_{E/k}\mathbf G_m$ has a canonical character, the field norm

$$
N_{E/k}:\operatorname{Res}_{E/k}\mathbf G_m\longrightarrow\mathbf G_m.
$$

On $R$-points it is the determinant of multiplication by an element of $(E\otimes_kR)^\times$. Over $k^s$, where an element is a tuple $(x_\tau)$, it is

$$
(x_\tau)_\tau\longmapsto\prod_\tau x_\tau.
$$

Thus the norm character corresponds to the sum of the embedding basis in the character lattice. It is Galois invariant and generates the invariant characters when the action on embeddings is transitive.

If $B/E$ is central simple, reduced norm gives

$$
\operatorname{Res}_{E/k}\operatorname{GL}_1(B)
\xrightarrow{\operatorname{Res}\operatorname{Nrd}}
\operatorname{Res}_{E/k}\mathbf G_m
\xrightarrow{N_{E/k}}\mathbf G_m.
$$

The composite is the determinant of left multiplication on $B$ only up to a power. If $B$ has degree $n$, then

$$
\det_k(L_b)=N_{E/k}(\operatorname{Nrd}_B(b))^n.
$$

The exponent $n$ arises because over a splitting field left multiplication on $M_n$ has determinant $(\det b)^n$. Omitting it is a typical consequence of confusing reduced norm with the determinant on the full algebra.

The norm-one torus illustrates exactness on points. There is an exact sequence of group objects

$$
1\to\operatorname{Res}^{1}_{E/k}\mathbf G_m
\to\operatorname{Res}_{E/k}\mathbf G_m
\xrightarrow{N_{E/k}}\mathbf G_m\to1,
$$

but the last map on $k$-points is $E^\times\to k^\times$ and may not be surjective. Its cokernel is arithmetic, whereas geometric surjectivity follows after a separable closure. For a quadratic extension, the norm-one torus has character lattice $\mathbf Z$ with the nontrivial Galois element acting by $-1$.

## 5. Torsors and descent

Knowing that an object becomes split does not say how it descends. Torsors convert the mismatch among local coordinate choices into an object, while cocycles turn that mismatch into a calculation. This chapter supplies the language needed to distinguish genuine forms from harmless changes of basis and to locate the obstruction to descending a representation.

### 5.1 Why a form is not a coordinate change

Let $X_0$ be an object over $k$. A **form** of $X_0$ is an object $X$ that becomes isomorphic to $X_0$ after a faithfully flat extension. An isomorphism after extension does not usually descend, because its Galois conjugates need not agree. Their discrepancy is the information classifying the form.

The elementary example is a conic. Over $k^s$ every smooth conic is a projective line, yet a conic with no $k$-point is not a projective line over $k$. Choosing an isomorphism over $k^s$ produces matrices whose failure to be Galois invariant is measured only up to scalar. The corresponding degree-two central simple algebra is the same obstruction in noncommutative form.

### 5.2 Torsors and cocycles

Let $G/k$ be a smooth affine group. A right $G$-torsor $P$ is a nonempty object locally for the faithfully flat topology on which $G$ acts simply transitively; equivalently, the map

$$
P\times G\longrightarrow P\times P,
\qquad(p,g)\longmapsto(p,pg)
$$

is an isomorphism. A torsor has a $k$-point exactly when it is trivial: a point $p$ identifies $G$ with $P$ by $g\mapsto pg$.

When $G$ is smooth and $k^s$ is used, choose $p\in P(k^s)$. For $\gamma\in\Gamma_k$ there is a unique $z_\gamma\in G(k^s)$ such that

$$
\gamma(p)=p z_\gamma.
$$

Then

$$
z_{\gamma\delta}=z_\gamma\,\gamma(z_\delta).
$$

Changing $p$ to $pg$ replaces $z_\gamma$ by $g^{-1}z_\gamma\gamma(g)$. Thus torsors are classified by the pointed set $H^1(k,G)$ of cocycles modulo this equivalence. It is generally not a group. Multiplying cocycles pointwise fails when $G$ is noncommutative, and pretending otherwise corrupts exactness arguments.

For finite étale or nonsmooth groups, the chosen topology matters. The applications below involve smooth reductive groups and central multiplicative groups, for which the stated description is adequate.

### 5.3 Twisting objects and representations

Suppose $G$ acts on an object $Y$ and $P$ is a right $G$-torsor. The twist is the contracted product

$$
{}^P Y=P\times^G Y,

$$

the quotient of $P\times Y$ by $(p,y)g=(pg,g^{-1}y)$. Locally, choosing a point of $P$ identifies ${}^P Y$ with $Y$; changing the point changes that identification by the $G$-action. This is descent with the ambiguity built in.

If $\rho:G\to\operatorname{GL}(V)$ is a representation, twisting gives a vector space ${}^P V$. Since all finite-dimensional vector spaces of fixed dimension are isomorphic over a field, the underlying vector space alone carries no obstruction. The additional tensors do. If $G$ is the stabilizer of a form, multiplication, or grading on $V$, that tensor descends and records the twisted object.

This observation explains why a central simple algebra is a twist of a matrix algebra under the projective linear group: the vector space $M_n$ descends together with its multiplication. It also explains the later symplectic construction: the alternating form must descend together with the representation, not be chosen afterward without compatibility.

### 5.4 Exactness for noncommutative classes

For an exact sequence of smooth groups

$$
1\longrightarrow A\longrightarrow B\longrightarrow C\longrightarrow1
$$

with $A$ central in $B$, there is an exact sequence of pointed sets

$$
B(k)\longrightarrow C(k)\xrightarrow{\delta}H^1(k,A)
\longrightarrow H^1(k,B)\longrightarrow H^1(k,C)
\xrightarrow{\partial}H^2(k,A).
$$

Exactness means that the fiber over the distinguished point is the preceding image. It does not assert kernels and quotient groups at the noncommutative terms.

The sequence

$$
1\longrightarrow\mathbf G_m\longrightarrow\operatorname{GL}_n
\longrightarrow\operatorname{PGL}_n\longrightarrow1
$$

is fundamental. The vanishing $H^1(k,\operatorname{GL}_n)=1$ says that vector spaces have no nontrivial forms once their dimension is fixed. Therefore the boundary injects

$$
H^1(k,\operatorname{PGL}_n)\hookrightarrow H^2(k,\mathbf G_m)=\operatorname{Br}(k),
$$

and its image consists exactly of classes represented by degree-$n$ central simple algebras. The connecting class is the obstruction to lifting projective descent matrices to compatible linear matrices.

Concretely, choose lifts $\widetilde z_\gamma\in\operatorname{GL}_n(k^s)$ of a projective cocycle. They need not form a cocycle; instead

$$
c_{\gamma,\delta}
=\widetilde z_\gamma\,\gamma(\widetilde z_\delta)
\widetilde z_{\gamma\delta}^{-1}\in(k^s)^\times.
$$

The scalars $c_{\gamma,\delta}$ form a two-cocycle. Changing the lifts changes it by a coboundary. Its class vanishes precisely when scalar corrections make the lifts a genuine linear cocycle. This formula is often the fastest way to locate the Brauer obstruction in a descent calculation.

### 5.5 Examples and failure modes

For $n=2$, a projective torsor gives a conic and a quaternion algebra. It is trivial precisely when the conic has a point, precisely when the algebra splits. These are not three independent coincidences: a point chooses a minimal right ideal, which gives a two-dimensional module and hence matrices.

A quadratic étale algebra gives another instructive torsor. Its norm-one torus

$$
\operatorname{Res}^{1}_{E/k}\mathbf G_m=\ker(N_{E/k})
$$

is split when $E=k\times k$ and usually nonsplit when $E$ is a field. It is a form of $\mathbf G_m$, but not an inner form: a torus has trivial inner automorphisms. Its nontriviality is entirely an outer Galois action on the character lattice.

Finally, twisting a group and twisting a representation are different operations. An inner form of $\operatorname{PGL}_n$ always exists for a central simple algebra $A$ of degree $n$. The standard action on $\mathbf P^{n-1}$ descends as an action of $\operatorname{PGL}_1(A)$ on the Severi--Brauer variety of minimal right ideals. It does **not** generally descend as an action on the projectivization of an $n$-dimensional $k$-space: such an identification would give a $k$-point of the Severi--Brauer variety and split $A$. A fortiori, a genuine standard linear representation need not descend. Corestriction later supplies a larger linear representation when the small one is obstructed.

As a worked quadratic example, let $K/k$ be quadratic with nontrivial automorphism $\sigma$, and let $b\in k^\times$. The cyclic algebra

$$
A=K\oplus Kj,\qquad j^2=b,\qquad jx=\sigma(x)j
$$

is split precisely when $b$ is a norm from $K^\times$. The projective descent matrix implementing $\sigma$ has square $b$ up to scalar. Correcting it to square one is possible exactly when $b=N_{K/k}(u)$, by replacing $j$ with $uj$. Thus the norm criterion is the cocycle-triviality criterion in coordinates.

## 6. Inner forms and central simple algebras

Descent can alter a root diagram or merely conjugate coordinates inside a fixed diagram. The second phenomenon is inner twisting, and central simple algebras are its concrete carriers for matrix groups. In degree two this theory becomes especially sharp: every adjoint form is quaternionic, and local-global ramification data classify the form completely over a number field.

### 6.1 Inner versus outer twisting

Let $G_0$ be a connected reductive group. Conjugation gives

$$
G_{0,\mathrm{ad}}\longrightarrow\operatorname{Aut}(G_0).
$$

The quotient is the finite group of outer automorphisms, identified after pinning with automorphisms of the based root datum. A form $G$ of $G_0$ is **inner** if its class in the outer automorphism classes is trivial; equivalently, after choosing an isomorphism $G_{k^s}\cong(G_0)_{k^s}$, the descent cocycle can be represented by inner automorphisms.

An inner form has the same Galois action on its based root datum as $G_0$. This does not make the groups isomorphic. The split and Hamiltonian real forms of $\operatorname{PGL}_2$ have identical type $A_1$ data but very different real points and parabolics.

Type $A_1$ has no nontrivial diagram automorphism. Consequently every form of the adjoint group $\operatorname{PGL}_2$ is inner. In higher type this fails: transpose-inverse produces an outer automorphism of type $A_{n-1}$ for $n\ge3$.

### 6.2 Forms of the matrix groups

Let $A/k$ be central simple of degree $n$. Define

$$
\operatorname{GL}_1(A)(R)=(A\otimes_kR)^\times,
$$

$$
\operatorname{SL}_1(A)=\ker(\operatorname{Nrd}_A:\operatorname{GL}_1(A)\to\mathbf G_m),
$$

and

$$
\operatorname{PGL}_1(A)=\operatorname{GL}_1(A)/\mathbf G_m.
$$

After a splitting $A\otimes K\cong M_n(K)$, these become $\operatorname{GL}_n$, $\operatorname{SL}_n$, and $\operatorname{PGL}_n$. Thus they are inner forms. Conversely every inner form of $\operatorname{PGL}_n$ is $\operatorname{PGL}_1(A)$ for a unique degree-$n$ central simple algebra up to isomorphism or opposite, and every inner form of $\operatorname{SL}_n$ is $\operatorname{SL}_1(A)$.

For the general linear group one must state the center as well as the derived group. Its inner forms are $\operatorname{GL}_1(A)$. Groups attached to algebras with unitary involution give outer forms and belong to a different classification.

The adjoint representation retains more information than the bare root datum. For a quaternion algebra it acts on

$$
B^0=\ker(\operatorname{Trd}_B)
$$

and preserves $x\mapsto-\operatorname{Nrd}_B(x)$. Conjugation therefore gives

$$
\operatorname{PGL}_1(B)\cong
\operatorname{SO}(B^0,-\operatorname{Nrd}_B).
$$

Both groups have dimension three, and the conjugation action has trivial kernel after quotienting scalars. Over a splitting field this is the accidental identification between adjoint type $A_1$ and a three-dimensional special orthogonal group. The quadratic form, unlike the root datum, retains the inner class.

### 6.3 The degree-two classification

When $n=2$, $A$ is a quaternion algebra $B$. Canonical conjugation identifies $B$ with its opposite, so the “up to opposite” ambiguity disappears. We obtain:

**Theorem 6.1.** Isomorphism classes of inner forms of $\operatorname{PGL}_2$ over $k$ are in bijection with isomorphism classes of quaternion algebras over $k$, by

$$
B\longmapsto\operatorname{PGL}_1(B).
$$

The corresponding simply connected form is $\operatorname{SL}_1(B)$.

**Proof strategy.** Use projective torsors to obtain a degree-two central simple algebra, then use the fact that an adjoint group determines that algebra up to opposite.

**Proof.** The boundary classification identifies $H^1(k,\operatorname{PGL}_2)$ with Brauer classes represented by degree-two central simple algebras. Twisting $M_2$ by a projective torsor yields $B$, and twisting the conjugation action on $\operatorname{PGL}_2$ yields $\operatorname{PGL}_1(B)$. Every form is inner because the based diagram $A_1$ has no nontrivial automorphism. Two twists give isomorphic forms exactly when their cocycles define the same class, up to an automorphism of the split group; all such automorphisms are inner in type $A_1$. Hence their Brauer classes agree. Degree-two central simple algebras in the same class are isomorphic, and canonical conjugation also identifies $B$ with $B^{\mathrm{op}}$. $\square$

The theorem concerns algebraic groups, not merely their abstract groups of $k$-points. Over small or exceptional fields, abstract point groups can lose geometric information.

The simply connected classification follows compatibly. If $B^1$ and $(B')^1$ are isomorphic, their adjoint quotients are isomorphic, hence $B\cong B'$. Conversely an algebra isomorphism respects reduced norm. No extra degree-two forms appear at the simply connected level.

One should not infer the analogous statement for $\operatorname{GL}_2$ from the derived group alone. The product $\mathbf G_m\times B^1$ maps onto $B^\times$ with a central kernel, and the way that kernel is embedded is part of the group. The character lattice records it.

### 6.4 Local and global fingerprints

Over a nonarchimedean local field, there are exactly two degree-two inner forms: the split group and the group attached to the unique quaternion division algebra. Over $\mathbf R$, they are $\operatorname{PGL}_2(\mathbf R)$ and $\mathbf H^\times/\mathbf R^\times$; the latter is compact.

Over a number field $F$, a quaternion algebra is determined by the finite even set $\operatorname{Ram}(B)$ of noncomplex places where it is division. Therefore the same set classifies the inner form. At $v\notin\operatorname{Ram}(B)$ the local group is split; at $v\in\operatorname{Ram}(B)$ it is the unique local inner form.

The parity condition counts real and finite places together. A proposed global inner form ramified at exactly one finite place and nowhere at infinity does not exist. This is a genuine global obstruction, not a failure to find convenient parameters.

### 6.5 What the root datum remembers

The absolute root datum of every $\operatorname{PGL}_1(B)$ is adjoint $A_1$, and that of every $\operatorname{SL}_1(B)$ is simply connected $A_1$. The root datum detects the central isogeny but not the Brauer class. The ground-field group also has a **relative rank**, the dimension of a maximal split torus. For a quaternion algebra,

$$
\operatorname{rank}_k\operatorname{PGL}_1(B)=
\begin{cases}
1,&B\text{ split},\\
0,&B\text{ division}.
\end{cases}
$$

Thus absolute and relative rank answer different questions. Absolute rank survives passage to $k^s$ and controls classification; relative rank measures visible split geometry over $k$ and controls parabolics. Confusing them would call a division form “rank zero” while simultaneously assigning it type $A_1$.

## 7. Quaternionic groups

A quaternion algebra produces not one group but a central, a simply connected, and an adjoint version. Choosing the correct one determines whether norm characters, approximation properties, or projective geometry remain visible. This chapter compares the three and then isolates the common-norm similitude group required after restriction from a larger field.

### 7.1 Three groups attached to one algebra

Let $B/k$ be quaternionic, with canonical involution $x\mapsto\bar x$. Its basic identities are

$$
x+\bar x=\operatorname{Trd}(x),
\qquad
x\bar x=\bar x x=\operatorname{Nrd}(x).
$$

The unit group $B^\times=\operatorname{GL}_1(B)$ has dimension four. Reduced norm gives an exact sequence

$$
1\longrightarrow B^1\longrightarrow B^\times
\xrightarrow{\operatorname{Nrd}}\mathbf G_m\longrightarrow1
$$

as group objects, where $B^1=\operatorname{SL}_1(B)$. Surjectivity here is geometric: after a splitting it is determinant. It does not assert that $\operatorname{Nrd}:B^\times(k)\to k^\times$ is surjective on rational points over every field.

Quotienting the central scalars gives

$$
1\longrightarrow\mathbf G_m\longrightarrow B^\times
\longrightarrow PB^\times\longrightarrow1,
$$

with $PB^\times=\operatorname{PGL}_1(B)$. The map $B^1\to PB^\times$ is a central isogeny with kernel $\mu_2$.

### 7.2 Smoothness, connectedness, and reductivity

**Proposition 7.1.** The groups $B^\times$, $B^1$, and $PB^\times$ are smooth and connected. The first is reductive, the second is simply connected semisimple of type $A_1$, and the third is adjoint semisimple of type $A_1$.

**Proof strategy.** All assertions can be tested after a faithfully flat splitting extension.

**Proof.** Choose $K/k$ with $B_K\cong M_2(K)$. The three groups become $\operatorname{GL}_2$, $\operatorname{SL}_2$, and $\operatorname{PGL}_2$. Smoothness and connectedness descend, as do reductivity and semisimplicity. The root data identify the simply connected and adjoint forms. $\square$

The proof is short because the algebra has already concentrated the descent data. Trying to verify the unipotent radical directly from quaternion coordinates would obscure this point.

### 7.3 Split coordinates and root subgroups

When $B=M_2(k)$, canonical conjugation is the adjugate

$$
\bar x=\operatorname{tr}(x)I-x,
$$

and $\operatorname{Nrd}(x)=\det(x)$. In $\operatorname{SL}_2$, take

$$
T=\left\{\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}\right\},
\quad
U_\alpha=\left\{\begin{pmatrix}1&u\\0&1\end{pmatrix}\right\},
\quad
U_{-\alpha}=\left\{\begin{pmatrix}1&0\\u&1\end{pmatrix}\right\}.
$$

Conjugation by $T$ acts on $U_\alpha$ as $u\mapsto t^2u$, so the root is twice the fundamental weight. This concrete square is the lattice index between simply connected and adjoint type $A_1$.

For division $B$, these root subgroups exist only after splitting. Their failure to descend is equivalent to the absence of nontrivial nilpotents and minimal right ideals in $B$.

The Lie algebra of $B^1$ is the pure subspace $B^0$. Differentiating reduced norm at the identity gives reduced trace, so the tangent condition is $\operatorname{Trd}(x)=0$. The bracket is the commutator. In split coordinates,

$$
e=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
f=\begin{pmatrix}0&0\\1&0\end{pmatrix},\quad
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix}
$$

satisfy $[h,e]=2e$, $[h,f]=-2f$, and $[e,f]=h$. In a division algebra there are no nonzero nilpotent $k$-points such as $e$ and $f$, although these relations appear after splitting.

### 7.4 Anisotropy and real forms

The norm-one group $B^1$ is anisotropic over $k$ precisely when $B$ is division: a nontrivial split torus would yield eigenlines after the standard representation, hence a proper right ideal. Conversely the diagonal torus appears when $B$ splits.

Over $\mathbf R$ this gives

$$
B^1(\mathbf R)\cong
\begin{cases}
\operatorname{SL}_2(\mathbf R),&B\cong M_2(\mathbf R),\\
\{x\in\mathbf H:\operatorname{Nrd}(x)=1\}\cong S^3,&B\cong\mathbf H.
\end{cases}
$$

Compactness in the second line is not a property of all division algebras over local fields; it is an archimedean topological fact coming from positive definiteness of the Hamilton norm. At a finite place the local norm-one group is compact, but the full unit group is not because powers of a uniformizer remain.

Over a number field, a global division algebra can split at some completions, so its group can have positive local rank there. It is nevertheless anisotropic over the ground field: a global split torus would yield a proper parabolic and hence a global minimal ideal. Total definiteness is stronger, requiring anisotropy at every real place and giving compactness of the full archimedean adjoint quotient.

The three quaternionic groups also serve different later purposes. The simply connected group $B^1$ is natural for approximation; $PB^\times$ records the adjoint geometry; $B^\times$ retains the reduced-norm character needed for similitudes. Passing between them without tracking the center loses arithmetic information.

### 7.5 The quaternionic similitude group over a subfield

Let $E/k$ be finite separable and $B/E$ quaternionic. The full restricted unit group has reduced norm in $\operatorname{Res}_{E/k}\mathbf G_m$, too large to be the multiplier of a $k$-valued alternating form. The correct fiber product is

$$
G(B/k)=\{b\in\operatorname{Res}_{E/k}B^\times:
\operatorname{Nrd}(b)\in\mathbf G_m\},
$$

where $\mathbf G_m\to\operatorname{Res}_{E/k}\mathbf G_m$ is the diagonal inclusion. Equivalently,

$$
G(B/k)=\operatorname{Res}_{E/k}B^\times
\times_{\operatorname{Res}_{E/k}\mathbf G_m}\mathbf G_m.
$$

Its multiplier is the common scalar $\nu(b)=\operatorname{Nrd}(b)$. Over $k^s$ it consists of tuples $(g_\tau)$ with all determinants equal. Its derived group is $\operatorname{Res}_{E/k}B^1$, and its center consists of scalar tuples $(z_\tau)$ whose squares are all equal. The connected central part is the diagonal $\mathbf G_m$; additional components can occur in the full center. This distinction matters when connectedness is used.

The group itself is connected. Over $k^s$, the multiplier maps a tuple with common determinant $d$ to $d$. Its kernel is a product of copies of $\operatorname{SL}_2$, so

$$
1\longrightarrow\prod_\tau\operatorname{SL}_2
\longrightarrow G(B/k)_{k^s}\xrightarrow{\nu}\mathbf G_m
\longrightarrow1
$$

has connected kernel and target. It also proves reductivity. Descent returns both properties over $k$. The dimension is $3[E:k]+1$: equality of the determinants imposes $[E:k]-1$ independent conditions on a group of dimension $4[E:k]$.

## 8. Involutions and adjoint structures

Polarizations force an algebra action to carry an adjoint operation. An involution is therefore structural data, not an ornament on a quaternion algebra. The chapter explains its reversal of multiplication, its orthogonal and symplectic types, and the passage between algebra involutions and bilinear or hermitian forms.

### 8.1 Why multiplication must be reversed

A bilinear form turns an operator acting on the first variable into an operator acting on the second. The order reverses:

$$
\psi(abx,y)=\psi(bx,a^*y)=\psi(x,b^*a^*y).
$$

Thus $(ab)^*=b^*a^*$. An **involution** on an algebra $A$ is an additive anti-automorphism $*$ of order two. Treating it as an automorphism would give the wrong adjoint formula and destroy the similitude calculation.

The fixed field of its action on the center determines its kind. An involution of the first kind fixes the center pointwise. An involution of the second kind acts nontrivially on a quadratic center extension; it is also called unitary.

### 8.2 Kinds and types of involution

Assume $\operatorname{char}k\ne2$ and $A/k$ is central simple. An involution of the first kind is **orthogonal** or **symplectic** according to whether, after splitting $A$, it is adjoint to a symmetric or alternating form. This definition is independent of the splitting.

There is a useful dimension test. If $A$ has degree $n$, then the fixed subspace has dimension

$$
\dim_k A^*=
\begin{cases}
n(n+1)/2,&*\text{ orthogonal},\\
n(n-1)/2,&*\text{ symplectic}.
\end{cases}
$$

For degree two, a symplectic involution has one-dimensional fixed space, namely the center. An orthogonal involution has a three-dimensional fixed space. In characteristic $2$ these criteria require modification, which is why the standing hypothesis is retained.

Type follows a sign rule under tensor product. The tensor of two involutions of the first kind is symplectic exactly when one factor is symplectic and the other orthogonal; it is orthogonal when the types agree. After splitting, this is the rule for tensor products of symmetric and alternating forms. In particular, the tensor of two canonical quaternion involutions is orthogonal. This is the involution-theoretic version of the parity rule for tensor-induced forms.

### 8.3 The canonical quaternion involution

On a quaternion algebra $B$, canonical conjugation

$$
\bar x=\operatorname{Trd}(x)-x
$$

is a symplectic involution. Indeed, after identifying $B$ with $M_2$, it is

$$
x\longmapsto J^{-1}x^{\mathsf t}J,
$$

the adjoint involution of the standard alternating form. Its fixed elements are precisely the scalars.

Every orthogonal involution on $B$ has the form

$$
x\longmapsto u\bar x u^{-1}
$$

for a nonzero pure quaternion $u$ with $\bar u=-u$. Multiplying $u$ by a scalar does not change the involution. Its discriminant is the square class of $-\operatorname{Nrd}(u)=u^2$. Thus the canonical involution is distinguished: it does not depend on a pure direction, and it is the unique symplectic involution on $B$.

For a concrete split calculation, take $B=M_2(k)$ and

$$
u=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

Canonical conjugation sends $x$ to $J^{-1}x^{\mathsf t}J$. Twisting it by $u$ gives the transpose involution after a change of basis, hence an orthogonal involution. The pure norm of $u$ records its discriminant. This also shows that canonical conjugation is neither entrywise conjugation nor ordinary transpose.

### 8.4 Adjoint involutions of bilinear forms

Let $V$ be finite-dimensional and $\psi$ a nondegenerate bilinear form. There is a unique involution $*$ on $\operatorname{End}(V)$ satisfying

$$
\psi(ax,y)=\psi(x,a^*y).
$$

In a basis with Gram matrix $H$,

$$
a^*=H^{-1}a^{\mathsf t}H.
$$

If $\psi$ is symmetric, $*$ is orthogonal; if $\psi$ is alternating, $*$ is symplectic. Conversely every involution of the first kind on a split central simple algebra is obtained this way, with the form unique up to a scalar.

The similitude group can therefore be written without coordinates:

$$
\operatorname{GSim}(A,*)=
\{a\in A^\times:a^*a\in k^\times\},
\qquad \nu(a)=a^*a.
$$

For $A=\operatorname{End}(V)$ this is the group of $g$ satisfying $\psi(gx,gy)=\nu(g)\psi(x,y)$.

The equation $a^*a\in k^\times$ is scheme-theoretic: over a test algebra, the scalar is a unit of that algebra. Requiring only that $a^*a$ be central is equivalent for a central simple algebra, but it defines a larger group when the center is a field extension of $k$. This is why $G(B/k)$ imposes that the $F$-valued reduced norm actually come from $k$.

### 8.5 Hermitian and skew-hermitian forms

Let $(A,*)$ be an algebra with involution and $M$ a right $A$-module. An $\varepsilon$-hermitian form is a biadditive map $h:M\times M\to A$ satisfying

$$
h(xa,yb)=a^*h(x,y)b,
\qquad
h(y,x)=\varepsilon h(x,y)^*,
$$

where $\varepsilon=1$ gives hermitian and $\varepsilon=-1$ gives skew-hermitian. Nondegeneracy means that $x\mapsto h(x,-)$ identifies $M$ with its $A$-dual.

Composing with a suitable trace produces a ground-field bilinear form. The sign alone does not determine whether the trace form is symmetric or alternating; the type of $*$ and the chosen trace-zero multiplier both intervene. The quaternionic construction in Chapter 13 will make the calculation directly rather than rely on a slogan.

Rank-one hermitian modules already produce the relevant groups. With $M=A$ and

$$
h(x,y)=x^*cy,
\qquad c^*=\varepsilon c,
$$

an isometry $x\mapsto gx$ satisfies $g^*cg=c$; allowing a ground-field scalar on the right gives a similitude. For canonical quaternion conjugation and a pure $c$, this equation is another form of the trace-pairing construction.

## 9. Corestriction algebras

Restriction of scalars moves point functors, but it does not descend the tensor product of conjugate representations. Corestriction is the multiplicative algebra construction that does. We construct it before using Brauer classes so that its degree, descent action, and induced involution remain visible rather than being compressed into a group-theoretic transfer symbol.

### 9.1 Multiplicative descent across a field extension

Field trace adds conjugates and field norm multiplies them. For a central simple algebra, addition of conjugates would forget multiplication, so the correct analogue of norm is a tensor product of conjugate algebras. Descent of that tensor product is the **corestriction algebra**.

Let $E/k$ be finite separable of degree $d$ and $A/E$ central simple of degree $n$. The desired $k$-algebra must become, over a field containing every embedding of $E$,

$$
\bigotimes_{\tau:E\hookrightarrow k^s}{}^\tau A.

$$

The factors are permuted by $\Gamma_k$. The permutation is not an arbitrary choice; it is exactly what makes the tensor product descend.

### 9.2 The tensor-of-conjugates construction

Choose a finite Galois extension $L/k$ containing the normal closure of $E$ and splitting $A$. For each embedding $\tau:E\hookrightarrow L$, form ${}^\tau A=A\otimes_{E,\tau}L$ and set

$$
C_L=\bigotimes_{\tau:E\hookrightarrow L}{}^\tau A.
$$

For $\gamma\in\operatorname{Gal}(L/k)$, transport coefficients and send the factor indexed by $\tau$ to the factor indexed by $\gamma\tau$. These semilinear maps satisfy the descent condition. Define

$$
\operatorname{Cor}_{E/k}(A)=C_L^{\operatorname{Gal}(L/k)}.
$$

Faithful descent shows that it is a central simple $k$-algebra and that its scalar extension to $L$ is $C_L$. Enlarging $L$ gives canonically isomorphic descended algebras. Thus the construction depends only on $A$ and $E/k$.

The order of tensor factors causes no sign: tensor products of ordinary algebras have canonical permutation isomorphisms satisfying the required coherence. This would be subtler in a graded setting.

Centrality and simplicity can be checked after $L/k$. The center of the tensor product of the split matrix factors is $L$, and the tensor product itself is a matrix algebra. Since center and two-sided ideals descend faithfully, the fixed algebra is central simple. This proof also shows that the construction is insensitive to a chosen presentation of $A$.

For an étale algebra $E=E_1\times\cdots\times E_r$, the natural extension of the definition is

$$
\operatorname{Cor}_{E/k}(A_1\times\cdots\times A_r)
=\bigotimes_{i=1}^r\operatorname{Cor}_{E_i/k}(A_i).
$$

Thus a split quadratic algebra gives $A_1\otimes_kA_2$. This formula is exactly what appears after completing a global extension at a split place.

### 9.3 Degree, base change, and the Brauer class

Since degrees multiply under tensor product,

$$
\deg\operatorname{Cor}_{E/k}(A)=n^d,
\qquad
\dim_k\operatorname{Cor}_{E/k}(A)=n^{2d}.
$$

Its Brauer class is the transfer of $[A]$:

$$
[\operatorname{Cor}_{E/k}(A)]=\operatorname{Cor}_{E/k}[A].
$$

For $A=A_1\otimes_EA_2$, corestriction distributes up to canonical isomorphism, and in towers $k\subset E\subset L$ one has

$$
\operatorname{Cor}_{L/k}(A)
\cong\operatorname{Cor}_{E/k}(\operatorname{Cor}_{L/E}(A)).
$$

Restriction followed by transfer satisfies

$$
\operatorname{Cor}_{E/k}(\operatorname{Res}_{E/k}\alpha)=d\alpha
$$

in $\operatorname{Br}(k)$. After extending the corestriction back to $E$, the formula is instead a sum of conjugates. If $E/k$ is Galois,

$$
\operatorname{Res}_{E/k}\operatorname{Cor}_{E/k}(\beta)
=\sum_{\sigma\in\operatorname{Gal}(E/k)}\sigma\beta.
$$

These two identities answer different questions and must not be interchanged.

Corestriction also respects opposites:

$$
\operatorname{Cor}_{E/k}(A^{\mathrm{op}})
\cong\operatorname{Cor}_{E/k}(A)^{\mathrm{op}}.
$$

Therefore an involution $A\to A^{\mathrm{op}}$ transfers to an involution of the corestriction. If the original involution is symplectic and there are $d$ conjugate factors, the transferred involution is symplectic for odd $d$ and orthogonal for even $d$. The conclusion follows after splitting from the tensor sign rule and then descends.

As a consistency check, take $A=M_n(E)$. Each conjugate factor is a matrix algebra on a conjugate $n$-space, and their tensor product is a matrix algebra on the tensor-induced space. Hence

$$
\operatorname{Cor}_{E/k}(M_n(E))\cong M_{n^d}(k).
$$

The isomorphism is not canonical until a model for the tensor-induced space is chosen. What is canonical is the descended algebra and hence its isomorphism class; a chosen matrix-algebra identification has the usual conjugation ambiguity.

### 9.4 The quadratic case in coordinates

Let $E/k$ be quadratic with nontrivial automorphism $\sigma$. Then

$$
\operatorname{Cor}_{E/k}(A)\otimes_kE
\cong A\otimes_E{}^\sigma A.
$$

The descent involution on the right sends $a\otimes b$ to $b\otimes a$ while applying $\sigma$ to coefficients. The fixed algebra is the corestriction.

If $A=(a,b)_E$ is quaternionic, the corestriction has degree four and dimension sixteen. It is not generally a quaternion algebra. Even though its Brauer class has exponent dividing two, a degree-four algebra of exponent two can be a biquaternion division algebra over a general field. Degree, exponent, and index must be kept separate.

If $A$ descends from $A_0/k$, then

$$
\operatorname{Cor}_{E/k}(A_0\otimes_kE)
$$

has Brauer class $2[A_0]$. For quaternion $A_0$ this class is zero, so the corestriction is split of degree four:

$$
\operatorname{Cor}_{E/k}(A_0\otimes_kE)\cong M_4(k).
$$

The algebra is split, not equal to $k$; transfer preserves the degree $2^2=4$ of the tensor construction.

The converse at the level of algebras is subtler. The equality

$$
[A]+[{}^\sigma A]=0
$$

after restriction to $E$ is necessary for split corestriction, but by itself it only says that the transferred class becomes split over $E$. A class in the relative Brauer group of $E/k$ could remain. The local invariant test below is what decides the class over $k$ without losing this information.

### 9.5 Local invariants and the exact splitting test

Let $E/k$ now be an extension of number fields and $A/E$ central simple. For a place $v$ of $k$,

$$
\operatorname{inv}_v(\operatorname{Cor}_{E/k}A)
=\sum_{w\mid v}\operatorname{inv}_w(A)
\quad\text{in }\mathbf Q/\mathbf Z.
$$

There is no local-degree factor in this formula. Local degrees occur when a class is restricted; corestriction preserves each invariant and adds over branches.

At a split place $E\otimes_kk_v=\prod_{w\mid v}E_w$, the local corestriction is the tensor product of the transfers from the factors. At a nonsplit place it is the usual local transfer from one field. Applying the local invariant in either case gives the same sum. This uniformity is the chief advantage of phrasing the formula over finite étale local algebras.

**Theorem 9.1.** A central simple algebra $A/E$ has split corestriction over $k$ if and only if

$$
\sum_{w\mid v}\operatorname{inv}_w(A)=0
$$

for every place $v$ of $k$.

**Proof strategy.** Localize transfer, apply the local invariant formula, then use injectivity of the global localization map.

**Proof.** The displayed sums are exactly the invariants of the localizations of $\operatorname{Cor}_{E/k}A$. They all vanish precisely when every localization is split. A global central simple algebra is split if and only if all its localizations are split. $\square$

For quaternion $A$, each summand is $0$ or $1/2$. The criterion says that an even number of places $w$ above every $v$ must ramify. It is not enough that the total number of ramified places of $A$ be even; that parity already holds for every global quaternion algebra and says nothing about how ramification lies over $k$.

At an archimedean place, the same rule includes no hidden convention. A complex factor contributes zero. Each Hamiltonian real factor contributes $1/2$. Thus two Hamiltonian real branches above one real base place cancel under transfer, while one Hamiltonian branch remains nontrivial. Dropping the real places would give an incorrect finite ramification set for the transferred class.

## 10. Trace, norm, and tensor induction

There are two distinct ways to transfer linear data: add conjugates by trace, or multiply them by norm and tensor induction. Their different linearity and parity properties determine which symplectic representations exist. This chapter develops both operations side by side and makes every determinant exponent explicit.

### 10.1 Additive and multiplicative transfer

Let $E/k$ be finite separable. The field trace and norm are characterized by multiplication on the $k$-space $E$:

$$
\operatorname{Tr}_{E/k}(x)=\operatorname{tr}_k(m_x),
\qquad
N_{E/k}(x)=\det_k(m_x).
$$

Over a common normal closure they become the sum and product of conjugates. Trace is $k$-linear, norm is multiplicative but not additive, and both are transitive in towers.

For a central simple $E$-algebra $A$, the composite

$$
\operatorname{Tr}_{E/k}\circ\operatorname{Trd}_A:A\longrightarrow k
$$

is the natural additive trace. It gives the nondegenerate pairing

$$
(x,y)\longmapsto
\operatorname{Tr}_{E/k}(\operatorname{Trd}_A(xy)).
$$

Nondegeneracy uses both separability of $E/k$ and separability of the central simple algebra. If $E/k$ were inseparable, the field trace could vanish and the conclusion would fail.

The multiplicative composite

$$
N_{E/k}\circ\operatorname{Nrd}_A:A^\times\longrightarrow k^\times
$$

is a character of $\operatorname{Res}_{E/k}\operatorname{GL}_1(A)$. It is not the reduced norm of the corestriction algebra evaluated at an ordinary linear image of $A$, because there is no natural additive algebra map $A\to\operatorname{Cor}_{E/k}(A)$.

The three traces in this discussion have different sizes. If $A$ has degree $n$, left multiplication on the $E$-space $A$ satisfies

$$
\operatorname{tr}_E(L_a)=n\operatorname{Trd}_A(a).
$$

After forgetting to $k$,

$$
\operatorname{tr}_k(L_a)
=n\operatorname{Tr}_{E/k}(\operatorname{Trd}_A(a)).
$$

For a quaternion algebra the factor is two. It does not appear when the trace pairing is defined using reduced trace; inserting it later rescales the rational form and can change an integral dual lattice.

### 10.2 The tensor norm of elements and modules

Over a normal closure $L$, an element $a\in A$ determines

$$
\bigotimes_\tau {}^\tau a
\in\bigotimes_\tau{}^\tau A.
$$

This tensor is invariant under the descent permutation and therefore defines an element

$$
N^{\otimes}_{E/k}(a)\in\operatorname{Cor}_{E/k}(A).
$$

It satisfies

$$
N^{\otimes}_{E/k}(ab)=N^{\otimes}_{E/k}(a)N^{\otimes}_{E/k}(b),
\qquad
N^{\otimes}_{E/k}(ca)=N_{E/k}(c)N^{\otimes}_{E/k}(a)
$$

for $c\in E$. The map is homogeneous of degree $d$ over $k$, not additive unless $d=1$.

Likewise, for an $E$-space $V$, tensor induction is the descended $k$-space whose scalar extension is

$$
N^{\otimes}_{E/k}(V)_L
=\bigotimes_{\tau:E\hookrightarrow L}{}^\tau V.
$$

If $\dim_E V=n$, then its dimension is $n^d$. A linear automorphism $g$ of $V$ acts through the tensor of its conjugates. Thus there is a representation

$$
\operatorname{Res}_{E/k}\operatorname{GL}(V)
\longrightarrow\operatorname{GL}(N^{\otimes}_{E/k}(V)).
$$

Its kernel over $k^s$ consists of scalar tuples $(c_\tau)$ with $\prod c_\tau=1$. Consequently tensor induction is generally not faithful on the full restricted general linear group, though it is often faithful modulo a central torus or on a suitable derived quotient.

Here is the linear-algebra argument for the kernel, since it will control faithfulness later. Suppose

$$
g_1\otimes\cdots\otimes g_d=1
$$

on $V_1\otimes\cdots\otimes V_d$, with every $V_i$ nonzero. Fix nonzero vectors in all factors except $V_i$ and contract the other factors against linear functionals nonzero on their images. The resulting equality says that $g_i v$ is proportional to $v$ for every nonzero $v\in V_i$. A linear automorphism preserving every line is scalar, so $g_i=c_iI$. The tensor is then multiplication by $\prod_i c_i$, which is the identity exactly when that product is one. The same argument after scalar extension proves the group-scheme kernel statement.

For $d=2$ and $\dim_E V=2$, the tensor-induced space has dimension four. The derived group over $k^s$ is $\operatorname{SL}_2\times\operatorname{SL}_2$, and $(-I,-I)$ acts trivially. The image gives the low-rank identification

$$
(\operatorname{SL}_2\times\operatorname{SL}_2)/\mu_2
\cong\operatorname{SO}_4
$$

for the split four-dimensional quadratic form. The orthogonal target is exactly what even tensor parity predicts.

### 10.3 Polynomial laws and a necessary warning

The tensor norm is best regarded as a multiplicative polynomial law. The formula

$$
a\longmapsto\bigotimes_\tau{}^\tau a
$$

looks elementwise, but it is compatible with arbitrary scalar extension and is polynomial of degree $d$. This functoriality is what permits descent.

For $d=2$,

$$
N^{\otimes}(a+b)
=a\otimes{}^\sigma a+b\otimes{}^\sigma b
+a\otimes{}^\sigma b+b\otimes{}^\sigma a.
$$

The cross terms show explicitly why tensor norm is not additive. Any argument that treats it as an algebra homomorphism has silently discarded these terms.

Reduced norm does interact cleanly with tensor norm. If $A$ has degree $n$, then after splitting and taking determinants of Kronecker products,

$$
\operatorname{Nrd}_{\operatorname{Cor}A}(N^{\otimes}_{E/k}(a))
=N_{E/k}(\operatorname{Nrd}_A(a))^{n^{d-1}}.
$$

Indeed, the determinant of $M_1\otimes\cdots\otimes M_d$ on an $n^d$-dimensional space is

$$
\prod_{i=1}^d(\det M_i)^{n^{d-1}}.
$$

For quaternion $A$, the exponent is $2^{d-1}$.

When $d=2$, this can be checked directly. Over a splitting field, let the two conjugate elements act by matrices $M$ and $M'$. Then

$$
\det(M\otimes M')=(\det M)^2(\det M')^2.
$$

The product $\det M\det M'$ is $N_{E/k}(\operatorname{Nrd}(a))$, giving its square. This locates the exponent and rules out the tempting exponent-one formula.

### 10.4 Forms on tensor-induced spaces

Suppose $V/E$ carries a nondegenerate bilinear form $h$. Over $L$, put

$$
h^{\otimes}\left(\bigotimes_\tau x_\tau,
\bigotimes_\tau y_\tau\right)
=\prod_\tau{}^\tau h(x_\tau,y_\tau).
$$

This formula is invariant under permutation of embeddings and descends to a nondegenerate $k$-bilinear form on $N^{\otimes}_{E/k}(V)$. If $g$ is a similitude with multiplier $\mu(g)\in E^\times$, then its tensor-induced action has multiplier

$$
N_{E/k}(\mu(g)).
$$

This is the representation-theoretic counterpart of multiplying conjugate norm characters.

Nondegeneracy can be checked after $L/k$: a tensor product of isomorphisms $V\to V^\vee$ is an isomorphism. No determinant calculation over $k$ is required.

### 10.5 Parity of the tensor form

Assume $h$ is alternating and $\operatorname{char}k\ne2$. Interchanging the two arguments in every factor gives

$$
h^{\otimes}(y,x)=(-1)^d h^{\otimes}(x,y).
$$

Therefore the tensor form is alternating when $d$ is odd and symmetric when $d$ is even. This parity rule is structural. A tensor product of two alternating forms is symmetric, not alternating.

For two-dimensional $V$, the standard alternating form has multiplier $\det$. Hence the tensor representation of $d$ copies of $\operatorname{GL}_2$ lands in a symplectic similitude group for odd $d$ and an orthogonal similitude group for even $d$. If a symplectic target is required in even degree, one must alter the representation, not the sign convention. Hyperbolic enlargement provides a canonical remedy.

In characteristic two, sign language alone would not prove alternation: a skew-symmetric form can have nonzero diagonal. Our standing hypothesis ensures that the parity computation carries the full diagonal condition as well as the symmetry sign.

## 11. Corestriction of quaternion algebras

For quaternion algebras over number fields, abstract transfer becomes a finite parity calculation over each base place. This chapter turns the invariant formula into a construction tool: it identifies the division representative, proves the exact splitting criterion, and describes what a splitting contributes to tensor representations. The quadratic case receives special attention because every fiber can be seen directly.

### 11.1 Possible algebra structures

Let $F/E$ be a finite extension of number fields of degree $d$, and let $B/F$ be quaternionic. The corestriction $C=\operatorname{Cor}_{F/E}(B)$ has degree $2^d$. Its Brauer class has exponent at most two because $[B]$ does.

Over a general field, exponent two does not determine index: $C$ may have division index $2^r$ for several $r$. Over a number field, however, exponent equals index. Thus only two Brauer possibilities occur here:

$$
C\cong
\begin{cases}
M_{2^d}(E),&\operatorname{Cor}[B]=0,\\
M_{2^{d-1}}(D),&\operatorname{Cor}[B]\ne0,
\end{cases}
$$

where $D/E$ is the quaternion algebra with the transferred ramification set. In particular, for $d\ge2$ the corestriction is never a division algebra over a number field, even when its class is nontrivial. Its degree is too large for its index.

### 11.2 Ramification counted over base places

For a place $v$ of $E$, define

$$
r_v(B)=\#\{w\mid v:w\in\operatorname{Ram}(B)\}.
$$

The local invariant formula gives

$$
\operatorname{inv}_v(C)=\frac{r_v(B)}2\pmod{\mathbf Z}.
$$

Hence $C$ ramifies, in the sense of its division Brauer representative, exactly at the $v$ for which $r_v(B)$ is odd. The transferred ramification set is

$$
\operatorname{Ram}(\operatorname{Cor}[B])
=\{v:r_v(B)\text{ is odd}\}.
$$

This set is automatically finite and even. Indeed, summing its half-invariants over $v$ equals the sum of all invariants of $B$, which is zero.

**Corollary 11.1.** The corestriction algebra is split if and only if every base place lies below an even number of ramified places of $B$.

This condition groups ramification by fibers. Merely counting $\operatorname{Ram}(B)$ globally cannot detect it.

### 11.3 Quadratic extensions and paired ramification

Suppose $F/E$ is quadratic. At a place $v$ there are either two places $w,w'$ above $v$, or one place. The criterion specializes as follows.

- If $v$ splits, either both $w,w'$ must ramify or neither may ramify.
- If $v$ is inert or ramified, the unique $w$ must not ramify.
- At a real place $v$, if $F$ has two real places above it, both or neither may be Hamiltonian; if $F_w=\mathbf C$, no quaternion algebra ramifies at $w$.

Thus split corestriction is much stronger than Galois stability of the total cardinality. When $F/E$ is Galois, it is equivalent to the ramification set being a union of full two-element fibers over split places and containing no one-element fiber.

If $B=B_0\otimes_EF$, the condition holds automatically. A ramified place $v$ of $B_0$ remains ramified at places of odd local degree. Over a split $v$ it gives two ramified branches; over a nonsplit quadratic branch the local degree is two and ramification disappears. This recovers the earlier fact that a descended quaternion has split corestriction.

Over number fields the ramification classification gives a useful converse in this quadratic quaternionic setting.

**Proposition 11.2.** Let $F/E$ be quadratic and $B/F$ quaternionic. Then $\operatorname{Cor}_{F/E}(B)$ is split if and only if there is a quaternion algebra $B_0/E$ with

$$
B\cong B_0\otimes_EF.
$$

**Proof strategy.** Necessity of split transfer for a descended quaternion is formal. For sufficiency, build the ramification set of $B_0$ from the paired fibers of $B$ and, when needed, repair its parity at a nonsplit place, which disappears after quadratic base change.

**Proof.** If $B$ is the base change of $B_0$, then its transferred class is $2[B_0]=0$, so the corestriction is split.

Conversely, split corestriction says that ramified places of $B$ occur in pairs above split places of $E$ and never above a nonsplit place. Let $S$ contain one base place for every such ramified pair. If $|S|$ is even, let $B_0$ ramify exactly at $S$. If $|S|$ is odd, choose a place $v_0$ of $E$ that is nonsplit in $F$ and not in $S$, and let $B_0$ ramify at $S\cup\{v_0\}$. Such a place exists because a nontrivial quadratic extension cannot split over every completion. In either case the chosen set is finite and even, so it defines $B_0$.

At $v\in S$, the two local degrees are one, so both branches of $(B_0)_F$ ramify. At the auxiliary $v_0$, the unique local degree is two, so restriction sends $1/2$ to zero. All other places remain split. Thus $(B_0)_F$ and $B$ have the same ramification set and are isomorphic. $\square$

The existence of $v_0$ is itself a genuine arithmetic input, so it is worth locating it. Write $F=E(\sqrt a)$ with $a\notin E^{\times2}$. The local--global injection of square classes gives a place $v_0$ at which $a$ is not a square; equivalently, $F\otimes_EE_{v_0}$ is a field. This square-class injection is the degree-two consequence of the established global reciprocity theory. Since every member of $S$ is split in $F$, this $v_0$ is automatically outside $S$. Thus the proof uses no density assertion and no unrecorded choice of a prime.

The converse uses the local-global classification and this supply of a nonsplit auxiliary place. Over a general field, vanishing of transfer need not imply that a quaternion algebra descends.

### 11.4 Examples and counterexamples

Let $F/E$ be real quadratic over a totally real field $E$. Suppose $B/F$ ramifies at both real places above every real place of $E$ and at no finite place. This requires the total number $2[E:\mathbf Q]$ to be even, so such $B$ exists. Every real fiber contributes two copies of $1/2$, hence the corestriction is split.

Now add one finite ramified place $w$ above a split $v$ without adding its conjugate. Global parity forces some second ramified place elsewhere, but the corestriction is already nonsplit at $v$. Adding an unrelated $w'$ above another base place repairs global parity for $B$ but leaves two distinct odd fibers, so the corestriction remains nonsplit. This is the cleanest counterexample to a total-parity criterion.

For a quadratic field $F/\mathbf Q$ and quaternion $B/F$ ramified at two conjugate finite primes above a split rational prime $p$, the corestriction is split at $p$. If these are the only ramified places, it is split everywhere. The degree-four corestriction algebra is then $M_4(\mathbf Q)$, even though $B$ is division over $F$.

### 11.5 Splittings and minimal modules

If $C=\operatorname{Cor}_{F/E}(B)$ is split, choosing an isomorphism

$$
C\xrightarrow{\sim}\operatorname{End}_E(W)
$$

produces a vector space $W$ of dimension $2^d$, unique up to isomorphism. The isomorphism itself is unique only up to conjugation. This is exactly the ambiguity expected from a minimal left module.

The multiplicative tensor norm gives a homomorphism of algebraic groups

$$
N^\otimes_{F/E}:\operatorname{Res}_{F/E}B^\times
\longrightarrow \operatorname{GL}_1(C).
$$

After the chosen identification $C\cong\operatorname{End}_E(W)$, this is an honest linear representation on $W$. Over a normal splitting field,

$$
W\otimes_E L\cong\bigotimes_{\tau:F\hookrightarrow L}V_\tau,
$$

where each $V_\tau$ is a two-dimensional splitting module for ${}^\tau B$. If one begins only with these factor modules, their tensor carries a projective descent datum; the algebra $C$ records its obstruction. A splitting of $C$ identifies that datum with the displayed linear action on $W$. Thus algebra splitting is precisely the descent condition for a $2^d$-dimensional tensor representation over $E$.

When the corestriction is $M_{2^{d-1}}(D)$ rather than split, a minimal module is naturally a right $D$-space. One can still obtain an ordinary $E$-space by forgetting the $D$-action, but its endomorphism algebra and invariant forms change. Declaring the original $2^d$-dimensional linear representation to exist would amount to falsely splitting $D$.

## 12. Symplectic spaces and similitude groups

The eventual representation target is a group of symplectic similitudes, so the basic linear algebra must be normalized independently of quaternion coordinates. We review perfect alternating forms, multipliers, the exceptional two-dimensional coincidence, and the hyperbolic device that repairs an orthogonal tensor representation. Integral duality is included because rational nondegeneracy alone does not produce a polarization lattice.

### 12.1 Alternating forms and their matrices

Let $R$ be a commutative ring and $V$ a finite projective $R$-module. An alternating form is an $R$-bilinear map $\psi:V\times V\to R$ with $\psi(x,x)=0$. It is **perfect** if

$$
V\longrightarrow V^\vee,
\qquad x\longmapsto\psi(x,-)
$$

is an isomorphism. Perfect alternating modules have even rank locally.

For a free module of rank $2g$, the standard matrix is

$$
J_g=\begin{pmatrix}0&I_g\\-I_g&0\end{pmatrix}.
$$

Over a field every nondegenerate alternating form admits a symplectic basis and hence this matrix. Over a ring, local symplectic bases exist for a perfect form, but a global basis may be obstructed by the projective module. The invariant formulation avoids choosing one.

The field statement follows from symplectic Gram--Schmidt. Choose nonzero $e_1$. Nondegeneracy gives $f_1$ with $\psi(e_1,f_1)=1$. Their plane is nondegenerate, so

$$
V=\langle e_1,f_1\rangle\perp
\langle e_1,f_1\rangle^\perp.
$$

Induction produces a symplectic basis. No square roots are used; the argument works in characteristic two as long as alternation is defined by vanishing on the diagonal.

### 12.2 Isometries and similitudes

Define

$$
\operatorname{Sp}(V,\psi)(R')=
\{g\in\operatorname{GL}(V_{R'}):\psi(gx,gy)=\psi(x,y)\},
$$

and

$$
\operatorname{GSp}(V,\psi)(R')=
\{g:\psi(gx,gy)=\nu(g)\psi(x,y),\ \nu(g)\in R'^\times\}.
$$

Perfectness makes the multiplier unique. It is a character $\nu:\operatorname{GSp}\to\mathbf G_m$, and

$$
1\longrightarrow\operatorname{Sp}(V,\psi)
\longrightarrow\operatorname{GSp}(V,\psi)
\xrightarrow{\nu}\mathbf G_m\longrightarrow1
$$

is exact as a sequence of group objects.

Taking determinants in $g^{\mathsf t}J_gg=\nu(g)J_g$ gives only $(\det g)^2=\nu(g)^{2g}$. The correct sign is

$$
\det g=\nu(g)^g.
$$

It follows by checking on the connected group over a universal base, or from the fact that it holds on a dense split torus. The square-root ambiguity cannot be dismissed merely by taking determinants.

On a split maximal torus, a similitude has the form

$$
\operatorname{diag}(t_1,\ldots,t_g,
\nu t_1^{-1},\ldots,\nu t_g^{-1}),
$$

whose determinant is visibly $\nu^g$. Characters that agree on a maximal torus agree on a connected reductive group, proving the formula. The same coordinates exhibit the derived roots $e_i-e_j$, $e_i+e_j-c$, and $2e_i-c$, where $c$ is the multiplier character.

### 12.3 The rank-two coincidence

For $g=1$, direct calculation gives

$$
g^{\mathsf t}J_1g=(\det g)J_1
$$

for every $2\times2$ matrix $g$. Hence

$$
\operatorname{GSp}_2=\operatorname{GL}_2,
\qquad
\operatorname{Sp}_2=\operatorname{SL}_2.
$$

For a quaternion algebra, this identity descends to

$$
b\bar b=\operatorname{Nrd}(b).
$$

The two formulas are the split and intrinsic versions of the same statement. This is why quaternionic unit groups are the natural inner rank-two similitude groups.

No analogous equality holds for $g>1$. The dimension of $\operatorname{GSp}_{2g}$ is $2g^2+g+1$, much smaller than $4g^2=\dim\operatorname{GL}_{2g}$ once $g>1$.

### 12.4 Hyperbolic enlargement

Every finite-dimensional space $W$ has a canonical symplectic enlargement

$$
H(W)=W\oplus W^\vee
$$

with

$$
\Psi((x,f),(y,g))=g(x)-f(y).
$$

It is alternating and nondegenerate. A representation $\rho:G\to\operatorname{GL}(W)$ acts symplectically by

$$
g\cdot(x,f)=(\rho(g)x,f\circ\rho(g)^{-1}).
$$

If a character $\nu:G\to\mathbf G_m$ is prescribed, the action

$$
g\cdot(x,f)=(\rho(g)x,\nu(g)f\circ\rho(g)^{-1})
$$

has multiplier $\nu(g)$.

This construction repairs the even-degree tensor parity without arbitrary choices. Its cost is doubling the dimension, and it may enlarge the commutant. Those costs matter in moduli problems, but they are preferable to asserting a nonexistent alternating tensor form.

### 12.5 Integral lattices and perfectness

Let $k$ be a number field and $V$ symplectic. A lattice $\Lambda$ over an order $R\subset k$ has dual

$$
\Lambda^\#=\{x\in V:\psi(x,\Lambda)\subset R\}.
$$

The form is perfect on $\Lambda$ precisely when $\Lambda=\Lambda^\#$. Scaling $\psi$ changes the dual lattice, so rational equivalence of forms does not determine the integral polarization type.

For a fractional ideal $I$ in a number field, the trace pairing identifies its dual with the inverse different times $I^{-1}$. Quaternionic trace lattices have an analogous codifferent involving the order. Consequently a multiplier $\delta$ that is harmless rationally may be forced integrally by the requirement that $\psi_\delta$ be perfect. The pure multiplier and the order cannot be selected independently in an integral model.

If an order $\mathcal O$ in a semisimple algebra acts on $\Lambda$ and is stable under $*$, the adjoint identity

$$
\psi(ax,y)=\psi(x,a^*y)
$$

makes $\Lambda^\#$ an $\mathcal O$-module. This is the integral compatibility required before one can formulate a polarized moduli problem. Existence of a self-dual lattice at every prime is a separate local question; it is not implied by the rational symplectic representation.

## 13. Quaternionic symplectic representations

All preceding structures meet in this chapter. The direct trace pairing turns the quaternion algebra itself into a faithful symplectic module, while split corestriction yields a smaller tensor-induced module. Comparing them exposes the exact tradeoffs among dimension, faithfulness, parity, endomorphisms, and archimedean positivity.

### 13.1 The trace-pairing construction

Let $F/k$ be finite separable, $B/F$ quaternionic, and choose $\delta\in B^\times$ with

$$
\bar\delta=-\delta.
$$

On the underlying $k$-space of $B$, define

$$
\psi_\delta(x,y)=
\operatorname{Tr}_{F/k}
\left(\operatorname{Trd}_B(x\delta\bar y)\right).
$$

The placement of $\delta$ is a convention. With this placement, left multiplication is adjoint to canonical conjugation after a cyclic trace calculation.

**Proposition 13.1.** The form $\psi_\delta$ is nondegenerate and alternating, and

$$
\psi_\delta(bx,y)=\psi_\delta(x,\bar b y)
$$

for $b,x,y\in B$.

**Proof strategy.** Use invariance of reduced trace under conjugation and its cyclic property; prove nondegeneracy from the perfect reduced-trace pairing.

**Proof.** Since $\operatorname{Trd}(z)=\operatorname{Trd}(\bar z)$ and reduced trace is cyclic,

$$
\begin{aligned}
\psi_\delta(y,x)
&=\operatorname{Tr}_{F/k}\operatorname{Trd}(y\delta\bar x)\\
&=\operatorname{Tr}_{F/k}\operatorname{Trd}(\overline{y\delta\bar x})\\
&=\operatorname{Tr}_{F/k}\operatorname{Trd}(x\bar\delta\bar y)\\
&=-\psi_\delta(x,y).
\end{aligned}
$$

Thus the form is alternating because the characteristic is not two. For adjointness,

$$
\operatorname{Trd}(bx\delta\bar y)
=\operatorname{Trd}(x\delta\bar y b)
=\operatorname{Trd}(x\delta\overline{\bar b y}).
$$

If $x$ pairs to zero with every $y$, separability of $F/k$ and nondegeneracy of the reduced-trace pairing force $x\delta=0$, hence $x=0$. $\square$

The invertibility of $\delta$ is essential for nondegeneracy. A nonzero pure quaternion is automatically invertible when $B$ is division, but not when $B$ is split; a nonzero nilpotent pure matrix gives a degenerate form.

Two examples fix the signs. In $M_2(k)$ take

$$
\delta=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

It is pure and invertible. With $x=(x_{ij})$ and $y=(y_{ij})$, the form obtained from $\operatorname{tr}(x\delta\bar y)$ is a nondegenerate alternating form on the four matrix coordinates. If instead

$$
\delta=\begin{pmatrix}0&1\\0&0\end{pmatrix},
$$

then $\delta$ is pure but nilpotent; every $x$ with $x\delta=0$ lies in the radical. Purity alone is insufficient in the split case.

For Hamilton quaternions over $\mathbf R$, choose $\delta=i$. The form $\psi_i(x,y)=\operatorname{Trd}(xi\bar y)$ is alternating. Right multiplication by $i$ gives a compatible complex structure after the appropriate sign choice, and $\psi_i(x,yi)$ becomes a definite symmetric form. This is the local model for positivity at a ramified real place.

### 13.2 The multiplier calculation

For $b\in B^\times$,

$$
\begin{aligned}
\psi_\delta(bx,by)
&=\operatorname{Tr}_{F/k}\operatorname{Trd}
(bx\delta\bar y\bar b)\\
&=\operatorname{Tr}_{F/k}\operatorname{Trd}
(x\delta\bar y\bar b b)\\
&=\operatorname{Tr}_{F/k}\left(
\operatorname{Nrd}(b)\operatorname{Trd}(x\delta\bar y)
\right).
\end{aligned}
$$

This is not generally a $k$-scalar multiple of $\psi_\delta$: the reduced norm lies in $F^\times$. Restricting to the group $G(B/k)$ of Section 7.5 makes $\operatorname{Nrd}(b)=\nu(b)\in k^\times$, and then

$$
\psi_\delta(bx,by)=\nu(b)\psi_\delta(x,y).
$$

We obtain a faithful representation

$$
G(B/k)\hookrightarrow\operatorname{GSp}(B,\psi_\delta).
$$

Faithfulness follows because left multiplication on $B$ is faithful. This construction has dimension $4[F:k]$ and requires no splitting of a corestriction algebra. It is therefore robust, though not always dimension-minimal.

The adjoint involution on $\operatorname{End}_k(B)$ restricts on the embedded copy of $B$ to canonical conjugation:

$$
L_b^*=L_{\bar b}.
$$

Thus the representation carries the algebra with involution, not only its unit group. Its commutant is right multiplication by $B^{\mathrm{op}}$. This double-centralizer description is important: prescribed endomorphisms appear on one side while the reductive group controlling similitudes is recovered from the other.

The common-norm condition is exact. If one allowed all of $\operatorname{Res}_{F/k}B^\times$, the formula would multiply the $F$-valued integrand by $\operatorname{Nrd}(b)$ before taking field trace. There is generally no scalar $c\in k$ that can be pulled outside the trace for every integrand unless $\operatorname{Nrd}(b)=c$ in $F$.

### 13.3 The tensor-corestriction construction

Assume $C=\operatorname{Cor}_{F/k}(B)$ is split and choose

$$
C\cong\operatorname{End}_k(W),
\qquad \dim_kW=2^{[F:k]}.
$$

Over $k^s$, $W$ is the tensor product of the standard two-dimensional modules for all conjugate quaternion factors. The derived group $\operatorname{Res}_{F/k}B^1$ acts on $W$. Scalar tuples act through their product, so the representation naturally factors through a central quotient of the full restricted unit group.

Each standard factor carries its determinant alternating form. Their tensor descends to a bilinear form $q$ on $W$, unique up to scalar once the splitting and factor forms are fixed. If $d=[F:k]$, then

$$
q(y,x)=(-1)^dq(x,y).
$$

For odd $d$, the representation is symplectic. For even $d$, it is orthogonal. On a tuple $(g_\tau)$ its multiplier is $\prod_\tau\det(g_\tau)$, the norm of the reduced-norm character.

The splitting hypothesis is exact. If $C$ is not split, there is no $2^d$-dimensional $k$-space whose full endomorphism algebra realizes $C$. One may work with a module over its quaternion division representative or enlarge the representation, but not simply choose matrices.

The action is best described on the derived group first. Over $k^s$ an element $(g_\tau)$ acts as $\bigotimes g_\tau$. The center of $\prod\operatorname{SL}_2$ is $\{(\varepsilon_\tau):\varepsilon_\tau=\pm1\}$, and its action is the product $\prod\varepsilon_\tau$. Hence the kernel is the even-sign subgroup. Descent carries this finite central kernel to the ground field. Any claim of faithfulness must either divide by it or add data detecting it.

When $d$ is odd, the tensor alternating form makes the image a subgroup of $\operatorname{Sp}(W)$. Allowing a common determinant scalar enlarges this to a similitude action. If every factor has determinant $\nu$, the tensor multiplier is $\nu^d$; if instead one uses the norm of independently varying determinants, it is their product. These are different source groups, so the exponent must be read from the defining fiber product.

### 13.4 Parity repair and faithful realizations

When $d$ is even, apply hyperbolic enlargement to $W$:

$$
H(W)=W\oplus W^\vee,
\qquad
\Psi((x,f),(y,g))=g(x)-f(y).
$$

If $\rho$ is the tensor representation and $\nu$ its intended multiplier, let

$$
g\cdot(x,f)=
(\rho(g)x,\nu(g)f\circ\rho(g)^{-1}).
$$

Then $H(W)$ is symplectic with multiplier $\nu$. The construction works equally when $d$ is odd and a canonical alternating tensor form has not been normalized.

The kernel of the tensor action must still be audited. Over $k^s$, scalar tuples with product one act trivially. One obtains faithfulness by either quotienting this central kernel or adjoining another representation that is nontrivial on every nonidentity element of it. A character cannot perform that job on the kernel inside $\prod_\tau\operatorname{SL}_2$, because every character of a connected semisimple group is trivial. The direct trace-pairing representation on $B$ avoids this kernel and is often preferable when faithful algebra action is part of the moduli data.

These alternatives should not be conflated:

| Construction | Dimension | Hypothesis | Natural issue |
|---|---:|---|---|
| underlying quaternion space | $4d$ | pure invertible $\delta$ | norm must be a common $k$-scalar |
| tensor corestriction | $2^d$ | split corestriction | parity and central kernel |
| hyperbolic tensor | $2^{d+1}$ | split corestriction | doubled commutant |

There is a fourth practical route when the corestriction has quaternionic division representative $D$. A minimal right module for

$$
C\cong M_{2^{d-1}}(D)
$$

has $D$-dimension $2^{d-1}$ and $k$-dimension $2^{d+1}$. An involution on $C$ yields a hermitian or skew-hermitian form on this module. Taking its trace can produce a symplectic representation, but its endomorphism algebra contains $D$ and its local signatures differ from the split-corestriction case. The obstruction has not disappeared; it has become additional endomorphisms.

### 13.5 Polarizations and positivity at infinity

A symplectic representation supplies the alternating form underlying a polarization, but positivity requires an additional real structure. Let $k$ be totally real. At a real embedding, choose an element $J$ in the acting algebra with $J^2=-1$ and require

$$
(x,y)\longmapsto\psi(x,Jy)
$$

to be symmetric positive definite. Then $J$ defines a complex structure compatible with $\psi$.

For Hamilton quaternions, a pure unit quaternion provides such a $J$, with the sign of $\delta$ chosen consistently. In the two-dimensional split real model, the two orientation classes represented by $J$ and $-J$ give opposite signs for $\psi(x,Jy)$; positivity chooses the one compatible with the fixed symplectic orientation. In higher dimension, the positive compatible complex structures form the connected space $\operatorname{Sp}_{2g}(\mathbf R)/U(g)$. The algebraic alternating identity alone chooses no point of this space.

An involution used for polarized endomorphisms must become positive under this real structure: the trace form $a\mapsto\operatorname{Tr}(aa^*)$ should be positive at the relevant archimedean factors. Canonical quaternion conjugation is positive on Hamilton factors but not positive definite on split matrix factors without the complex structure. Thus definiteness of the algebra and positivity of the polarization are related but not identical assertions.

At the integral level one must also choose an involution-stable order and a lattice on which the alternating form is integral, usually with prescribed dual quotient. Those choices change the integral moduli problem while leaving the rational reductive group unchanged. The present structural package supplies the rational group, its involution, and its symplectic representation; representability and integral models require further geometric input.

The linear-algebraic datum used for a polarized endomorphism problem may be summarized as

$$
(D,*,V,\psi,h),
$$

where $D$ is a finite-dimensional semisimple $k$-algebra, $*$ is a positive involution, $V$ is a faithful left $D$-module, $\psi$ is a nondegenerate alternating form satisfying

$$
\psi(dx,y)=\psi(x,d^*y),
$$

and $h$ is a real homomorphism specifying a compatible complex structure. The associated group is

$$
G(R)=\{g\in\operatorname{GL}_{D\otimes R}(V\otimes R):
\psi(gx,gy)=\nu(g)\psi(x,y),\ \nu(g)\in R^\times\}.
$$

The quaternion trace construction realizes this template with $D$ acting by one side and the group arising from the commuting side. The tensor construction realizes it after the corestriction obstruction has been neutralized.

More precisely, the Deligne torus is $\mathbb S=\operatorname{Res}_{\mathbf C/\mathbf R}\mathbf G_m$, and $h:\mathbb S\to G_{\mathbf R}$ is required to give only the two weights appropriate to a weight-one polarized structure. Equivalently, after complexification the representation decomposes into two conjugate subspaces on which $\mathbb S(\mathbf R)=\mathbf C^\times$ acts through $z$ and $\bar z$. The operator denoted $h(i)$ is then a complex structure, and positivity requires $\psi(x,h(i)y)$ to be definite with the chosen sign. These conditions constrain the real ramification and cannot be recovered from the finite-place Brauer class alone.

## 14. The rank-two structural package

The final chapter reorganizes the theory as a reusable construction sequence. Its aim is to make hypotheses auditable: each field extension, ramification choice, transfer, representation, and lattice appears only after the obstruction governing it has been resolved. The closing dictionary also separates formulas that are often confused because they use the same words “norm,” “restriction,” or “multiplier.”

### 14.1 A dependency-safe construction sequence

The constructions of this book fit into a stable order.

1. Choose a finite separable extension $F/k$ and a quaternion algebra $B/F$, specified globally by its ramification set when $F$ is a number field.
2. Form $B^\times$, $B^1$, and $PB^\times$. Their absolute type and central isogenies are determined by the $A_1$ root datum.
3. Apply restriction of scalars. Over $k^s$ the group becomes a product indexed by embeddings of $F$, with Galois permuting the factors.
4. If a common scalar similitude is needed, take the fiber product $G(B/k)$ imposing $\operatorname{Nrd}(b)\in k^\times$.
5. Choose between two representation routes. The quaternion trace pairing gives a faithful $4[F:k]$-dimensional representation. The tensor route first tests whether $\operatorname{Cor}_{F/k}(B)$ splits and then gives a $2^{[F:k]}$-dimensional representation, possibly followed by hyperbolic enlargement.
6. At each real place, impose the positivity condition appropriate to a polarization.
7. Only after the rational data are fixed, choose stable orders and lattices and test integral perfectness locally.

Each step solves one obstruction and exposes the next. Reversing the order tends to hide hypotheses—for example, choosing a tensor module before checking corestriction splitting, or choosing a lattice before fixing the adjoint involution.

### 14.2 Exact hypotheses at a glance

The principal results use the following hypotheses.

| Result | Exact hypotheses | Conclusion |
|---|---|---|
| preservation under scalar restriction | finite separable $F/k$ | smoothness, connectedness, reductivity preserved |
| degree-two inner classification | field $k$, characteristic not $2$ | inner $A_1$ forms correspond to quaternion algebras |
| trace-pairing nondegeneracy | finite separable $F/k$, quaternion $B/F$, invertible pure $\delta$ | nondegenerate alternating $k$-form |
| local invariant transfer | finite extension of local fields | transfer preserves invariant |
| global corestriction splitting test | number fields $F/k$ | sums over every branch vanish |
| tensor symplectic parity | alternating factor forms, characteristic not $2$ | alternating exactly for odd $[F:k]$ |
| tensor-corestriction representation | split $\operatorname{Cor}_{F/k}(B)$ | $k$-space of dimension $2^{[F:k]}$, with its finite central kernel recorded |

Characteristic different from $2$ is needed for the classical quaternion presentations, pure/skew decomposition, and the equivalence of alternating with skew-symmetric. Corestriction itself exists more generally. Number-field hypotheses enter the local-global splitting test and the assertion that exponent equals index; they are not needed for the tensor-of-conjugates definition.

### 14.3 Common normalization traps

Several formulas look similar enough to invite errors. The reliable dictionary is:

$$
\operatorname{inv}_L(\operatorname{Res}_{L/K}\alpha)
=[L:K]\operatorname{inv}_K(\alpha),
$$

$$
\operatorname{inv}_K(\operatorname{Cor}_{L/K}\beta)
=\operatorname{inv}_L(\beta),
$$

and globally

$$
\operatorname{inv}_v(\operatorname{Cor}_{F/k}B)
=\sum_{w\mid v}\operatorname{inv}_w(B).
$$

For degree $n$ central simple $A$,

$$
\det_k(L_a)=N_{F/k}(\operatorname{Nrd}_A(a))^n,
$$

whereas tensor norm satisfies

$$
\operatorname{Nrd}_{\operatorname{Cor}A}(N^\otimes a)
=N_{F/k}(\operatorname{Nrd}_A(a))^{n^{d-1}}.
$$

Finally, a tensor of $d$ alternating forms has sign $(-1)^d$, while the direct quaternion trace form is alternating for every $d$ because field trace is applied after a single skew identity. These constructions have different parity because they are different representations.

### 14.4 Conclusion

Rank two is the first setting in which the full descent architecture is visible and still calculable. The root datum separates semisimple type from the central lattice. Reductivity makes that datum geometric, while relative rank records which part can be seen before extending the field. Torsors then explain why a group with split geometric fibers may remain genuinely twisted over its ground field.

Quaternion algebras give the complete inner twisting mechanism for type $A_1$. Their reduced norm is determinant without chosen matrices, and canonical conjugation is the descended symplectic adjoint. Restriction of scalars assembles every field embedding into one ground-field group; corestriction assembles the corresponding algebras multiplicatively. The exact local invariant formula shows when the tensor of conjugate two-dimensional representations descends to an honest vector space.

Two symplectic routes emerge. The direct trace pairing on the quaternion algebra is faithful and exists without a corestriction splitting. The smaller tensor-induced representation exists precisely when that splitting obstruction vanishes, and its symmetry is governed by the parity of the extension degree. Hyperbolic enlargement resolves the remaining parity obstruction without concealing it.

The resulting package is the rational linear-algebraic foundation for polarized endomorphism constructions: a reductive similitude group, an involution, a faithful or minimal representation, an alternating form, and exact local-global criteria for their existence. Integral orders, lattices, and positivity refine this package, but they no longer alter its basic descent logic.
