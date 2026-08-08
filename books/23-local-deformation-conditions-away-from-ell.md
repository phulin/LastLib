# Local Deformation Conditions Away from $\ell$

## Contents

1. [The local design problem](#1-the-local-design-problem)
   - [Why away from $\ell$ is a structural simplification](#11-why-away-from-ell-is-a-structural-simplification)
   - [Standing notation](#12-standing-notation)
   - [What a local condition must accomplish](#13-what-a-local-condition-must-accomplish)
2. [Inertia seen by $\ell$-adic coefficients](#2-inertia-seen-by-ell-adic-coefficients)
   - [Wild rigidity and tame flexibility](#21-wild-rigidity-and-tame-flexibility)
   - [Arithmetic Frobenius and the tame relation](#22-arithmetic-frobenius-and-the-tame-relation)
   - [Finite inertial image and its limits](#23-finite-inertial-image-and-its-limits)
3. [Local deformation conditions as formal subspaces](#3-local-deformation-conditions-as-formal-subspaces)
   - [The ambient functors](#31-the-ambient-functors)
   - [A definition designed for base change](#32-a-definition-designed-for-base-change)
   - [Closedness, enhancement, and representability](#33-closedness-enhancement-and-representability)
   - [Tangent and obstruction modules](#34-tangent-and-obstruction-modules)
4. [Unramified deformations](#4-unramified-deformations)
   - [The intrinsic condition](#41-the-intrinsic-condition)
   - [The universal Frobenius matrix](#42-the-universal-frobenius-matrix)
   - [Unframed conjugacy and the cyclic-vector hypothesis](#43-unframed-conjugacy-and-the-cyclic-vector-hypothesis)
   - [Fixed determinant](#44-fixed-determinant)
   - [Tangent spaces and smoothness](#45-tangent-spaces-and-smoothness)
5. [Fixed finite inertial type](#5-fixed-finite-inertial-type)
   - [Why an inertial type needs an integral model](#51-why-an-inertial-type-needs-an-integral-model)
   - [The elementary prime-to-$\ell$ condition](#52-the-elementary-prime-to-ell-condition)
   - [Independence, closedness, and lifting](#53-independence-closedness-and-lifting)
   - [The tangent condition](#54-the-tangent-condition)
6. [Tame matrix deformation problems](#6-tame-matrix-deformation-problems)
   - [Generators and equations](#61-generators-and-equations)
   - [Linearizing the tame relation](#62-linearizing-the-tame-relation)
   - [A deformation complex and smoothness criterion](#63-a-deformation-complex-and-smoothness-criterion)
   - [Two-dimensional examples](#64-two-dimensional-examples)
7. [Minimal ramification, case by case](#7-minimal-ramification-case-by-case)
   - [Why there is no universal minimum](#71-why-there-is-no-universal-minimum)
   - [Unramified and finite semisimple residual inertia](#72-unramified-and-finite-semisimple-residual-inertia)
   - [Nontrivial tame unipotent residual inertia](#73-nontrivial-tame-unipotent-residual-inertia)
   - [Scalar twists and reducible inertia](#74-scalar-twists-and-reducible-inertia)
8. [Special or Steinberg-shaped deformations](#8-special-or-steinberg-shaped-deformations)
   - [The shape and its arithmetic meaning](#81-the-shape-and-its-arithmetic-meaning)
   - [The closed special condition](#82-the-closed-special-condition)
   - [Nonzero monodromy is open](#83-nonzero-monodromy-is-open)
   - [Enhanced lines, uniqueness, and tangent directions](#84-enhanced-lines-uniqueness-and-tangent-directions)
9. [Fixed determinant and characteristic two](#9-fixed-determinant-and-characteristic-two)
   - [Determinant as a condition in every construction](#91-determinant-as-a-condition-in-every-construction)
   - [Trace-zero tangent modules](#92-trace-zero-tangent-modules)
   - [What fails in characteristic two](#93-what-fails-in-characteristic-two)
10. [Obstructions, dimensions, and dual local conditions](#10-obstructions-dimensions-and-dual-local-conditions)
   - [Ambient obstruction spaces](#101-ambient-obstruction-spaces)
   - [Euler characteristic and Tate duality](#102-euler-characteristic-and-tate-duality)
   - [Orthogonals](#103-orthogonals)
   - [Why smoothness can jump](#104-why-smoothness-can-jump)
11. [Conductors and exact minimality](#11-conductors-and-exact-minimality)
   - [What conductor constancy really requires](#111-what-conductor-constancy-really-requires)
   - [Finite type and tame unipotent preservation](#112-finite-type-and-tame-unipotent-preservation)
   - [Counterexamples to naive semicontinuity claims](#113-counterexamples-to-naive-semicontinuity-claims)
12. [Functoriality](#12-functoriality)
   - [Extension of coefficient fields](#121-extension-of-coefficient-fields)
   - [Changing and forgetting frames](#122-changing-and-forgetting-frames)
   - [Unramified base change of local fields](#123-unramified-base-change-of-local-fields)
13. [A menu for global deformation problems](#13-a-menu-for-global-deformation-problems)
   - [Representable conditions and tangent spaces](#131-representable-conditions-and-tangent-spaces)
   - [Two-dimensional selection table](#132-two-dimensional-selection-table)
   - [The decision procedure](#133-the-decision-procedure)
14. [Conclusion](#14-conclusion)
   - [Local equations with global consequences](#141-local-equations-with-global-consequences)

## 1. The local design problem

### 1.1 Why away from $\ell$ is a structural simplification

A global Galois representation is assembled from local restrictions, but one should not permit every local lift at every place. At a place of good reduction one wants inertia to remain invisible. At a place already carrying finite tame ramification one may want that inertial action to remain unchanged. At a multiplicative place one wants a single unipotent direction, tied to Frobenius by the cyclotomic character. These are different deformation problems, even when their residual representations happen to look alike.

This book constructs those conditions when the residue characteristic $p$ of the local field is different from the coefficient characteristic $\ell$. The inequality

$$
p\ne\ell
$$

does not make inertia disappear. Rather, it divides inertia into a rigid pro-$p$ part and a potentially deformable pro-$\ell$ tame direction. That division is the source of nearly every calculation below. It explains why finite wild actions lift rigidly, why tame relations can be written with two matrices, and why the local Euler characteristic contains no large field-degree term.

The purpose is not to attach one label called “minimal” to every representation. Minimality is meaningful only relative to the residual inertial shape and the arithmetic application. We shall therefore build a small collection of precisely defined conditions, prove their formal properties, and say exactly which one is minimal in each residual case used later.

The prime $\ell$ itself is absent from this book's local-field side. Conditions at residue characteristic $\ell$ depend on integral models and will be treated separately. Global deformation rings are also postponed: the present task is to prepare local pieces whose functorial and tangent-space properties are already known before they are assembled.

### 1.2 Standing notation

Let $K$ be a nonarchimedean local field with residue field $\mathbf F_q$ of characteristic $p$. Fix a separable closure and write

$$
G_K=\operatorname{Gal}(K^s/K),\qquad I_K\triangleleft G_K,
$$

with $P_K\triangleleft I_K$ the wild inertia subgroup. Arithmetic Frobenius is the element

$$
\varphi:x\longmapsto x^q
$$

of $G_K/I_K$; a chosen lift to $G_K$ is denoted by the same letter. Thus geometric Frobenius is $\varphi^{-1}$. This convention is decisive in the tame relation and in every cyclotomic twist.

Let $k$ be a finite field of characteristic $\ell\ne p$. Let $\mathcal O$ be either the ring of integers in a finite extension of $\mathbf Q_\ell$ with residue field $k$, or more generally a complete Noetherian local ring with residue field $k$. Its maximal ideal is $\mathfrak m_{\mathcal O}$. The coefficient category $\mathcal C_{\mathcal O}$ consists of local Artinian $\mathcal O$-algebras $A$ equipped with an identification $A/\mathfrak m_A\simeq k$.

Fix a continuous representation

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_d(k)
$$

on a $k$-space $\bar V$. Write

$$
M=\operatorname{ad}\bar\rho=\operatorname{End}_k(\bar V),
$$

with $G_K$ acting by conjugation. When a determinant lift

$$
\delta:G_K\longrightarrow\mathcal O^\times,
\qquad \delta\bmod\mathfrak m_{\mathcal O}=\det\bar\rho,
$$

has been chosen, the fixed-determinant tangent coefficient is governed by the derivative of determinant. If $\ell\nmid d$, it is the familiar direct summand

$$
M^0=\operatorname{ad}^0\bar\rho=\ker(\operatorname{tr}:M\to k).
$$

When $\ell\mid d$, especially for $d=2$ and $\ell=2$, this notation still denotes a submodule, but it is not a complement to the scalars and must not be substituted blindly into unframed formulas.

For a module $N$, put $h^i_K(N)=\dim_kH^i(K,N)$. The unramified subspace is

$$
H^1_{\mathrm{ur}}(K,N)
=\ker\bigl(H^1(K,N)\to H^1(I_K,N)\bigr).
$$

### 1.3 What a local condition must accomplish

A useful local deformation condition has three jobs. First, it must express the intended arithmetic shape intrinsically, without depending on a generator or basis that has no arithmetic meaning. Second, it must survive every coefficient map $A\to B$. Third, it must define a manageable formal subspace: preferably a quotient of the ambient universal ring, with a tangent space and obstruction theory that can be computed.

These jobs are logically distinct. A base-change-stable collection of lifts need not be closed. A closed condition need not be smooth. A functor can possess a hull without possessing a universal object, because strict equivalence may retain automorphisms. Much of the care in this subject consists in refusing to infer one property from another.

The recurring proof architecture will be:

1. choose a coordinate description only after stating the intrinsic condition;
2. express the coordinate condition by matrix equations or a rigid finite-group action;
3. use the representability results for closed subfunctors of a framed problem;
4. linearize the equations to identify the tangent space;
5. test lifting across small extensions, usually by a degree-two obstruction or an explicit derivative;
6. pass to unframed classes only under a stated descent or centralizer hypothesis.

This order prevents an attractive matrix normal form from being mistaken for a basis-independent deformation condition.

## 2. Inertia seen by $\ell$-adic coefficients

### 2.1 Wild rigidity and tame flexibility

Ramification theory gives an exact sequence

$$
1\longrightarrow P_K\longrightarrow I_K
\longrightarrow\prod_{r\ne p}\mathbf Z_r(1)\longrightarrow1.
$$

The wild group $P_K$ is pro-$p$. Suppose $A'\twoheadrightarrow A$ is a small extension in $\mathcal C_{\mathcal O}$ with kernel $J$. The congruence kernel

$$
1+M_d(J)
$$

is an elementary abelian $\ell$-group. A continuous homomorphism from a pro-$p$ group to it is trivial. More generally, if a finite $p$-group already acts on a lift, averaging is available because $p$ is a unit in $A'$. Thus an existing wild action has no infinitesimal $\ell$-primary freedom: its lift across a small extension is unique up to strict conjugacy once the surrounding representation is fixed.

This is the precise content of “wild inertia is rigid away from $p$.” It does not say that $P_K$ acts trivially. A residual representation may have a substantial finite wild image. It says that the pro-$p$ part does not generate new tangent directions in an $\ell$-adic congruence kernel.

Tame inertia is different. Its $\mathbf Z_\ell(1)$ factor maps continuously into congruence subgroups, and a first-order homomorphism from it can be nonzero. If residual inertia is trivial, this is exactly the source of tamely ramified first-order classes. When $q\equiv1\pmod\ell$, even the trivial coefficient line has both an unramified and a tame $H^1$ direction.

**Example.** Take the trivial one-dimensional residual representation. Unramified characters over $k[\varepsilon]/(\varepsilon^2)$ are determined by

$$
\rho(\varphi)=1+a\varepsilon,\qquad \rho(I_K)=1.
$$

A tame infinitesimal character has

$$
\rho(\tau)=1+b\varepsilon.
$$

The relation below forces $(q-1)b=0$. Thus the tame direction exists precisely when $q\equiv1\pmod\ell$. The inequality $p\ne\ell$ alone does not make the full deformation problem unramified.

### 2.2 Arithmetic Frobenius and the tame relation

The maximal tame quotient of $G_K$ is topologically generated by arithmetic Frobenius $\varphi$ and a compatible tame generator $\tau$, subject to

$$
\boxed{\varphi\tau\varphi^{-1}=\tau^q.} \tag{2.1}
$$

Here $\tau$ generates the procyclic group $\prod_{r\ne p}\mathbf Z_r(1)$. Replacing arithmetic Frobenius by geometric Frobenius reverses the conjugation convention. We will not do so.

For a representation that kills wild inertia, put

$$
F=\rho(\varphi),\qquad T=\rho(\tau).
$$

Then continuity and the group law amount to the matrix equation

$$
FTF^{-1}=T^q. \tag{2.2}
$$

Over an Artinian coefficient ring the target matrix group is finite, so a pair satisfying (2.2) gives a continuous representation of the tame quotient. Over a complete coefficient ring the representation is the inverse limit of its Artinian reductions; continuity is built into that inverse-limit construction.

Equation (2.2) is the basic local equation away from $\ell$. Unramified deformations set $T=1$. Finite inertial type fixes $T$ up to strict conjugacy. A special deformation takes $T$ to be unipotent and converts (2.2) into an eigenvalue relation on its nilpotent logarithm.

### 2.3 Finite inertial image and its limits

Every residual representation has finite image, hence finite inertial image. A characteristic-zero lift, however, can have infinite tame image. For example,

$$
T=\begin{pmatrix}1&t\\0&1\end{pmatrix},\qquad t\in\mathfrak m_A,
$$

may acquire an infinite pro-$\ell$ image at the inverse limit even though every Artinian reduction has finite image. Thus “fixed inertial type” and “tame” are not synonyms. The first usually freezes a finite prime-to-$\ell$ action; the second permits the pro-$\ell$ tame direction to vary.

There is also a reduction trap. A nonzero characteristic-zero tame parameter can become zero modulo $\ell$. Consequently an $\ell$-adic special representation can have unramified residual representation. This is not a contradiction: residual conductor can be smaller than characteristic-zero conductor.

## 3. Local deformation conditions as formal subspaces

### 3.1 The ambient functors

For $A\in\mathcal C_{\mathcal O}$, let $D^\square(A)$ be the set of continuous lifts

$$
\rho_A:G_K\to\operatorname{GL}_d(A)
$$

reducing exactly to the chosen matrix representation $\bar\rho$. This is the framed deformation functor. The unframed functor $D(A)$ is obtained by quotienting by strict conjugacy, namely conjugacy by matrices in $1+M_d(\mathfrak m_A)$.

The framed functor is pro-representable. The unframed functor is pro-representable under the scalar-centralizer hypothesis

$$
\operatorname{End}_{k[G_K]}(\bar V)=k,
$$

and otherwise may have only a hull or a better-behaved groupoid. Fixed-determinant variants $D^{\square,\delta}$ and $D^\delta$ are defined by the equation $\det\rho_A=\delta_A$.

The tangent spaces are

$$
t_{D^\square}=Z^1(K,M),\qquad t_D=H^1(K,M),
$$

with the already noted determinant caveats. A frame records all cocycles; forgetting it kills coboundaries.

### 3.2 A definition designed for base change

A **local deformation condition** $\mathcal D$ on the framed problem is a collection of subsets

$$
\mathcal D(A)\subseteq D^\square(A)
$$

such that:

- $\bar\rho\in\mathcal D(k)$;
- every coefficient map $A\to B$ carries $\mathcal D(A)$ into $\mathcal D(B)$;
- membership is compatible with isomorphisms appropriate to the problem;
- compatible objects glue over fiber products whenever the ambient framed objects do.

For an unframed condition, membership must be invariant under strict equivalence. In practice we demand more: **closed relative representability**, meaning that after pulling the condition back to any represented family, it is cut out by a closed ideal. In particular, inside an ambient universal framed ring $R^\square$, there is a quotient

$$
R^\square\twoheadrightarrow R^{\square,\mathcal D}
$$

representing the condition.

The first bullet is easy to overlook. An “unramified deformation condition” exists over the deformation category of $\bar\rho$ only if $\bar\rho$ itself is unramified. If $\bar\rho$ is ramified, the rule “all lifts with trivial inertia” has no residual point and is not a deformation condition on $\bar\rho$.

### 3.3 Closedness, enhancement, and representability

Matrix equalities on a universal framed representation define closed conditions. For example, requiring $\rho(g)=1$ for every $g$ in a topologically normally generated subgroup amounts to killing matrix entries of $\rho^{\mathrm{univ}}(g)-1$. No finite list need be chosen in advance: Noetherianity makes the resulting closed ideal finitely generated.

Existence of an invariant line is subtler. The enhanced functor consisting of a lift together with a chosen direct-summand line is representable by equations, but its image after forgetting the line need not be a closedly representable set-valued subfunctor. If the two residual characters are distinct, the residual line may lift uniquely and forgetting it is harmless. If they coincide, several lines can merge in the special fiber, and descent can fail.

This distinction will recur for special representations. We shall first represent the enhanced object or an intrinsic matrix equation, and only then state conditions under which it descends to an unframed quotient.

### 3.4 Tangent and obstruction modules

Let $k[\varepsilon]=k[\varepsilon]/(\varepsilon^2)$. A framed tangent vector has the form

$$
\rho_\varepsilon(g)=(1+\varepsilon c(g))\bar\rho(g),
$$

where $c\in Z^1(K,M)$. A local condition cuts out a linear subspace

$$
Z^1_{\mathcal D}(K,M)\subseteq Z^1(K,M).
$$

If it is conjugacy-invariant, the unframed tangent is its image

$$
L_{\mathcal D}\subseteq H^1(K,M).
$$

The tangent space alone does not determine the condition. The equation $xy=0$ has no linear term but produces a singular closed subspace. Smoothness requires lifting every object across every small extension. An obstruction space $O_{\mathcal D}$ is useful only when an actual construction puts each failed lift into it and proves that zero is equivalent to liftability. Vanishing of an ambient $H^2$ is a sufficient criterion for the unconstrained problem; constrained problems can have smaller, different, or equation-theoretic obstruction spaces.

## 4. Unramified deformations

### 4.1 The intrinsic condition

Assume throughout this chapter that $\bar\rho(I_K)=1$. A lift $\rho_A$ is **unramified** if

$$
\rho_A(I_K)=1,
$$

or equivalently if it factors through $G_K/I_K\simeq\widehat{\mathbf Z}$. This definition is independent of a Frobenius lift. It is preserved by coefficient change and strict conjugacy.

The condition is closed. In the universal framed representation, form the ideal generated by the entries of

$$
\rho^{\square,\mathrm{univ}}(\sigma)-1,\qquad \sigma\in I_K.
$$

The corresponding quotient represents exactly the lifts killing inertia. Although infinitely many $\sigma$ appear, the universal ring is Noetherian and the ideal they generate is closed and finitely generated. This is a useful instance in which intrinsic closedness is clearer than a chosen presentation.

### 4.2 The universal Frobenius matrix

Choose a lift $\widetilde F\in\operatorname{GL}_d(\mathcal O)$ of

$$
\bar F=\bar\rho(\varphi).
$$

Every framed unramified lift is determined by the single matrix $F=\rho_A(\varphi)$ reducing to $\bar F$. Conversely such a matrix defines a continuous representation of $\widehat{\mathbf Z}$: at Artinian level its cyclic subgroup is finite, and the complete-ring representation is obtained by inverse limit.

Write $\mathbf X=(X_{ij})$ and put

$$
F^{\mathrm{univ}}=\widetilde F+\mathbf X.
$$

Its determinant is automatically a unit because its reduction is. Hence

$$
R^{\square,\mathrm{ur}}\simeq
\mathcal O[[X_{11},\ldots,X_{dd}]]. \tag{4.1}
$$

The framed unramified functor is formally smooth of relative dimension $d^2$. Notice how much stronger this is than ambient unobstructedness: it follows directly from lifting one invertible matrix entrywise, without needing $H^2(K,M)$ to vanish.

**Worked example: $d=2$.** If

$$
\bar F=\begin{pmatrix}\bar a&\bar b\\ \bar c&\bar d\end{pmatrix},
$$

then the universal lift is the same matrix with four independent parameters added to chosen lifts of its entries. No characteristic-polynomial equation is imposed unless trace or determinant has separately been fixed.

### 4.3 Unframed conjugacy and the cyclic-vector hypothesis

Quotienting a single matrix by strict conjugacy is already delicate. The residual centralizer of an unramified $d$-dimensional representation contains $k[\bar F]$, so for $d>1$ it is rarely scalar. The general scalar-centralizer theorem therefore does not justify an unframed universal unramified ring in the cases one most wants to study.

There is, however, a useful exact substitute. Call $\bar F$ **cyclic** if $\bar V$ has a vector $v$ such that

$$
v,\bar Fv,\ldots,\bar F^{d-1}v
$$

is a basis. Equivalently, the minimal and characteristic polynomials of $\bar F$ agree. Cyclicity is open under Artinian lifting. In a lifted cyclic basis, $F$ is the companion matrix of its characteristic polynomial, and two lifts are strictly conjugate exactly when their characteristic polynomials agree.

It follows that the unframed unramified functor is represented in the cyclic case by

$$
R^{\mathrm{ur}}\simeq\mathcal O[[a_1,\ldots,a_d]], \tag{4.2}
$$

where the $a_i$ deform the nonleading coefficients of the characteristic polynomial. It is formally smooth of relative dimension $d$. The proof uses a cyclic vector lifting a chosen residual cyclic vector; changing that lift changes the companion basis by strict conjugacy, not the polynomial.

For $d=2$, every nonscalar $\bar F$ is cyclic. Thus unframed unramified two-dimensional deformations are parametrized by trace and determinant whenever Frobenius is nonscalar. If $\bar F$ is scalar, this assertion fails: matrices with the same trace and determinant need not be strictly conjugate over nonreduced rings, and infinitesimal stabilizers obstruct naive orbit gluing.

**Counterexample.** Let $\bar F=1$ in dimension two. Over $k[\varepsilon]$, the lifts

$$
1+\varepsilon\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
1+\varepsilon\begin{pmatrix}0&1\\0&0\end{pmatrix}
$$

have the same trace and determinant but are not strictly conjugate. Indeed, strict conjugation acts trivially on the first-order matrix $X$ in a lift $1+\varepsilon X$ of a scalar matrix. The scalar special fiber has forgotten every preferred eigenline, and a coarse unframed formula cannot restore one.

### 4.4 Fixed determinant

Suppose a determinant lift $\delta$ is fixed. An unramified lift can have determinant $\delta$ only if $\delta|_{I_K}=1$. Under this necessary hypothesis, put $D=\delta(\varphi)$. The framed fixed-determinant ring is

$$
R^{\square,\mathrm{ur},\delta}
\simeq R^{\square,\mathrm{ur}}/(\det F^{\mathrm{univ}}-D). \tag{4.3}
$$

The determinant morphism on the general linear group is smooth over $\mathbf Z$. At every point one matrix entry can be corrected because the adjugate of an invertible matrix is not the zero functional. Therefore (4.3) is formally smooth of relative dimension

$$
d^2-1
$$

in every characteristic.

If $\bar F$ is cyclic, the unframed fixed-determinant ring is obtained from (4.2) by fixing its constant coefficient. It is formally smooth of relative dimension $d-1$. For $d=2$ and nonscalar $\bar F$, only the trace remains free.

### 4.5 Tangent spaces and smoothness

The unframed tangent space is

$$
L_{\mathrm{ur}}=H^1_{\mathrm{ur}}(K,M)
\simeq M^{I_K}/(\varphi-1)M^{I_K}. \tag{4.4}
$$

Because $\bar\rho$ is unramified, $M^{I_K}=M$. Kernel and cokernel of $\varphi-1$ have equal dimension, so

$$
\dim_kL_{\mathrm{ur}}=h^0_K(M)
=\dim_k\operatorname{Cent}_M(\bar F). \tag{4.5}
$$

The framed tangent consists of unramified cocycles before dividing by coboundaries and is naturally identified, by evaluation at $\varphi$, with $M$. Its dimension is $d^2$, agreeing with (4.1). In the cyclic case the centralizer has dimension $d$, agreeing with (4.2).

For fixed determinant, the framed tangent is

$$
\{X\in M:\operatorname{tr}(X)=0\},
$$

where $X=c(\varphi)$ in left-multiplicative coordinates. The unframed tangent is

$$
\ker\bigl(H^1_{\mathrm{ur}}(K,M)
\xrightarrow{\operatorname{tr}}H^1_{\mathrm{ur}}(K,k)\bigr). \tag{4.6}
$$

When $\ell\nmid d$, this is $H^1_{\mathrm{ur}}(K,M^0)$. When $\ell\mid d$, (4.6), not a dimension subtraction slogan, is the safe formula.

The contrast is worth retaining: the framed unramified problem is always smooth; the cyclic unframed problem is smooth; a naive unframed quotient at scalar Frobenius need not even be representable. These are three different statements about the same residual inertia condition.

## 5. Fixed finite inertial type

### 5.1 Why an inertial type needs an integral model

Suppose $\bar\rho|_{I_K}$ has finite image. Saying that a lift has “the same inertia” cannot mean literal equality of matrices over different coefficient rings. One needs an integral representation whose reduction is the residual action and whose scalar extensions provide the comparison object at every level.

The clean elementary setting is the following. Let $H$ be a finite quotient of $I_K$ through which $\bar\rho|_{I_K}$ factors. Require its kernel to be normal in $G_K$, so conjugation by a Frobenius lift induces an automorphism of $H$. Assume

$$
\ell\nmid |H|,
$$

and choose a representation

$$
\theta:H\longrightarrow\operatorname{GL}_d(\mathcal O)
$$

reducing to $\bar\rho|_{I_K}$. We also require compatibility with the conjugation action of $G_K$ on the chosen inertia quotient: the representation $h\mapsto\theta(\varphi h\varphi^{-1})$ must be isomorphic to $\theta$ over $\mathcal O$. Equivalently, the datum includes an integral intertwiner $F_0\in\operatorname{GL}_d(\mathcal O)$ satisfying the corresponding conjugation equations. This is stronger than invariance only after extending the fraction field, and it is exactly what is needed for the type to occur in an integral local lift.

The prime-to-$\ell$ hypothesis is not decorative. It makes the group algebra separable and permits averaging. Without it, a finite inertial representation can itself have nontrivial extension deformations, so “fixed type” is no longer a rigid condition of the form developed here.

### 5.2 The elementary prime-to-$\ell$ condition

A lift $\rho_A$ has **inertial type $\theta$** if its restriction to $I_K$ factors through $H$ and is strictly equivalent to

$$
\theta_A=\theta\otimes_{\mathcal O}A.
$$

Equivalently, there is $U\in1+M_d(\mathfrak m_A)$ such that

$$
U\rho_A(\sigma)U^{-1}=\theta_A(\bar\sigma)
\qquad(\sigma\in I_K). \tag{5.1}
$$

This is intrinsic under strict equivalence. A framed rigidification records $U$ as part of the data and then uses literal equations. The unenhanced condition forgets $U$.

There are two restrictions hidden in (5.1). The kernel of $I_K\twoheadrightarrow H$ must act trivially; in particular, the pro-$\ell$ tame direction cannot acquire new unipotent image. And the surviving finite action is not merely required to have the same characteristic polynomials: it must be isomorphic to the specified integral representation.

### 5.3 Independence, closedness, and lifting

The condition does not depend on enlarging $H$. If $H'$ is another finite prime-to-$\ell$ quotient through which the same action factors, pass to a common quotient of $I_K$ mapping to both. A representation inflated from $H$ is strictly equivalent to the inflated model from $H'$ exactly when it is equivalent after that common refinement.

Nor does it depend on replacing $\theta$ by a strictly equivalent integral model. Conjugating $\theta$ by a matrix reducing to the identity simply changes $U$ in (5.1). If two integral lifts of the same $k[H]$-module are given, the vanishing

$$
H^1(H,M_d(J))=0
$$

across successive small extensions, proved by averaging over $H$, constructs a strict equivalence between them once their residual identifications agree.

**Representability theorem.** In the prime-to-$\ell$ setting above, the fixed-$\theta$ condition is closedly relatively representable on the framed deformation functor. Indeed, once the kernel of $I_K\twoheadrightarrow H$ is killed, the inertial restriction is a deformation of the fixed residual $k[H]$-module. Averaging gives

$$
H^i(H,M_d(J))=0\qquad(i>0)
$$

for every successive square-zero kernel $J$, so every such deformation is strictly equivalent to $\theta_A$. Thus the intrinsic fixed-type condition is exactly the closed factor-through-$H$ condition, not merely the set-theoretic image of a conjugation orbit. Its rigidified version, after choosing the inertial conjugacy, is given by the finite equations

$$
\rho_A(h)=\theta_A(h)\qquad(h\in H)
$$

together with the equations killing the kernel of $I_K\twoheadrightarrow H$. Forgetting the rigidification recovers the same closed condition because averaging gives existence and uniqueness up to the centralizer of $\theta$. On an unframed ambient functor it is pro-representable whenever the usual scalar-centralizer descent hypothesis holds; without such a hypothesis one should retain the framed condition or its groupoid.

**Proof strategy.** Literal equality is visibly closed in the rigidified problem, while factorization through $H$ is visibly closed before rigidification. Across a small extension, two conjugacies whose reductions agree differ by a $1$-cocycle of $H$ in a matrix kernel. Averaging makes this cocycle a coboundary, so the conjugacies glue. The same averaging kills the obstruction in $H^2(H,-)$. Consequently the intrinsic and factor-through formulations agree on every Artinian test ring, which proves closed relative representability without assuming that an orbit image is closed.

There is also a concrete smoothness description. Use the integral intertwiner $F_0$ included above. After rigidifying inertia, every Frobenius matrix is

$$
CF_0,
$$

where $C$ belongs to the unit group of the inertia centralizer

$$
\operatorname{End}_H(\mathcal O^d).
$$

Because $H$ has order invertible in $\mathcal O$, this centralizer is a direct-summand algebra and its unit group is smooth. The choice of inertial conjugacy is redundant by the smooth centralizer action: its orbit contributes $d^2-\dim_k M^{I_K}$ directions, while $C$ contributes $\dim_k M^{I_K}$. Hence the intrinsic framed fixed-type condition is formally smooth of relative dimension $d^2$. With fixed determinant it is formally smooth of relative dimension $d^2-1$ provided the trace map on the inertial centralizer is surjective; this holds in particular when $\ell\nmid d$, because scalar endomorphisms then supply a nonzero trace direction. Without that surjectivity, especially in characteristic dividing $d$, fixing determinant can cut the Frobenius-centralizer torsor non-smoothly.

### 5.4 The tangent condition

Let $c\in Z^1(K,M)$. The first-order restriction remains strictly equivalent to $\theta$ precisely when $c|_{I_K}$ is a coboundary. Hence the unframed tangent space is

$$
L_\theta
=\ker\bigl(H^1(K,M)\to H^1(I_K,M)\bigr)
=H^1_{\mathrm{ur}}(K,M). \tag{5.2}
$$

This formula remains valid although $M$ itself may be ramified. Its Frobenius description is

$$
L_\theta\simeq
M^{I_K}/(\varphi-1)M^{I_K},
\qquad
\dim_kL_\theta=h^0_K(M). \tag{5.3}
$$

For the rigidified framed condition, cocycles vanish literally on inertia. For the intrinsic framed condition, they may restrict to coboundaries because the conjugating matrix is allowed to vary. These two framed tangent spaces differ by infinitesimal changes of the inertial rigidification; their unframed images agree.

Fixed determinant replaces (5.2) by the kernel of the determinant derivative inside it. When $\ell\nmid d$, this is $H^1_{\mathrm{ur}}(K,M^0)$. The finite-group averaging argument is compatible with determinant because trace commutes with conjugation, but the characteristic-$\ell\mid d$ warning still applies to unframed ambiguity.

## 6. Tame matrix deformation problems

### 6.1 Generators and equations

Assume first that wild inertia acts trivially and that the intended condition continues to kill it. Put

$$
\bar F=\bar\rho(\varphi),\qquad
\bar T=\bar\rho(\tau),
$$

so that $\bar F\bar T\bar F^{-1}=\bar T^q$. A framed tame lift is a pair

$$
(F,T)\in\operatorname{GL}_d(A)^2
$$

reducing to $(\bar F,\bar T)$ and satisfying

$$
FTF^{-1}=T^q. \tag{6.1}
$$

This condition is represented by a quotient of a power-series ring in $2d^2$ variables by the entries of (6.1). It is therefore closed, but it need not be smooth. The relation may have a derivative of deficient rank, and its components can meet at scalar or unipotent points.

If residual wild inertia is nontrivial, one first fixes its finite $p$-group action. Averaging makes that action rigid. The matrices $F$ and $T$ must then also normalize it according to the Galois conjugation action. These are further finite matrix equations. Nothing conceptually new occurs, but omitting them would incorrectly replace a ramified residual representation by a tame one.

### 6.2 Linearizing the tame relation

Write a first-order lift in left-multiplicative coordinates as

$$
F_\varepsilon=(1+\varepsilon X)\bar F,
\qquad
T_\varepsilon=(1+\varepsilon Y)\bar T.
$$

The derivative of the left side of (6.1), expressed relative to $\bar T^q$, is

$$
X+\operatorname{Ad}_{\bar F}(Y)
-\operatorname{Ad}_{\bar T^q}(X).
$$

The derivative of the right side is

$$
N_{q,\bar T}(Y)
=\sum_{i=0}^{q-1}\operatorname{Ad}_{\bar T^i}(Y). \tag{6.2}
$$

Thus the framed tangent pairs are the kernel of

$$
d^1:M\oplus M\longrightarrow M,
$$

$$
d^1(X,Y)=X+\operatorname{Ad}_{\bar F}(Y)
-\operatorname{Ad}_{\bar T^q}(X)-N_{q,\bar T}(Y). \tag{6.3}
$$

This formula is simply the tame group relation differentiated without discarding noncommutativity. If $\bar T=1$, it simplifies to

$$
d^1(X,Y)=(1-\operatorname{id})X+(\operatorname{Ad}_{\bar F}-q)Y
=(\operatorname{Ad}_{\bar F}-q)Y. \tag{6.4}
$$

Hence every $X$ is an unramified framed direction, while a tame direction $Y$ exists exactly in the $q$-eigenspace of $\operatorname{Ad}_{\bar F}$.

For a one-dimensional trivial residual representation, $\operatorname{Ad}_{\bar F}=1$, and (6.4) becomes $(1-q)Y=0$, recovering the example of Section 2.1.

### 6.3 A deformation complex and smoothness criterion

Infinitesimal strict conjugacy by $1+\varepsilon Z$ changes the pair through

$$
d^0(Z)=
\bigl(Z-\operatorname{Ad}_{\bar F}(Z),
Z-\operatorname{Ad}_{\bar T}(Z)\bigr). \tag{6.5}
$$

The tame relation implies $d^1d^0=0$. We obtain a three-term complex

$$
C^\bullet_{\mathrm{tame}}:
M\xrightarrow{d^0}M\oplus M\xrightarrow{d^1}M. \tag{6.6}
$$

Its degree-zero cohomology is the simultaneous centralizer of $\bar F$ and $\bar T$. Its degree-one cohomology is the unframed tangent space of the tame quotient problem. The cokernel

$$
H^2(C^\bullet_{\mathrm{tame}})=\operatorname{coker}(d^1) \tag{6.7}
$$

is an obstruction space for lifting the matrix relation across small extensions.

**Smoothness criterion.** If $d^1$ is surjective, the framed tame deformation problem is formally smooth at the residual point. Its relative dimension is

$$
2d^2-d^2=d^2.
$$

More generally, at a point where the derivative has constant rank $r$ and the relation ideal has the expected complete-intersection behavior, the local relative dimension is $2d^2-r$. Surjectivity is a clean sufficient condition; failure of surjectivity is not proof of actual obstruction, but it records a possible obstruction space.

The complex is also the correct antidote to an overly quick use of ambient $H^2(K,M)$. The tame condition kills wild inertia and is controlled by a chosen presentation. Its constrained obstruction map factors through (6.7), which can vanish even when the ambient group $H^2(K,M)$ does not, or conversely acquire equation-theoretic singularities from the chosen inertial shape.

### 6.4 Two-dimensional examples

**Semisimple inertia.** Suppose

$$
\bar T=\begin{pmatrix}\zeta&0\\0&\zeta'\end{pmatrix},
\qquad \zeta\ne\zeta',
$$

with both eigenvalues of order prime to $\ell$. The two eigenspaces lift uniquely by idempotents. Fixing this inertial type removes the off-diagonal inertial directions, and the remaining tangent space is unramified cohomology of the inertia centralizer. Frobenius may preserve the two lines or permute them; the compatibility $\bar F\bar T\bar F^{-1}=\bar T^q$ decides which.

**Trivial inertia, distinct Frobenius eigenvalues.** Suppose

$$
\bar F=\operatorname{diag}(\alpha,\beta),\qquad \bar T=1.
$$

On the upper-right line, $\operatorname{Ad}_{\bar F}$ has eigenvalue $\alpha\beta^{-1}$; on each diagonal direction it is $1$; and on the lower-left line it is $\beta\alpha^{-1}$. By (6.4), tame upper-right motion exists exactly when

$$
\alpha\beta^{-1}=q.
$$

This is the infinitesimal special relation. A lower-left tame motion exists when $\beta\alpha^{-1}=q$. Diagonal tame motion exists when $q=1$ in $k$. These exceptional ratios are precisely where tangent dimensions jump.

**Scalar residual Frobenius.** If $\bar F$ is scalar and $q\not\equiv1\pmod\ell$, (6.4) forces $Y=0$, so the framed tame tangent is unramified even though the full tame functor was allowed. If $q\equiv1\pmod\ell$, every $Y\in M$ is an infinitesimal tame direction. The dramatic jump is real and warns against quoting a uniform smooth dimension without residue congruence hypotheses.

## 7. Minimal ramification, case by case

### 7.1 Why there is no universal minimum

The word **minimal** compares a lift with the ramification already visible in the residual representation. It should mean that no new inertial characters, breaks, or unipotent blocks are introduced. But these data behave differently under reduction. A finite prime-to-$\ell$ character lifts rigidly; a tame unipotent parameter can vanish modulo $\ell$; and a residual scalar representation does not remember a preferred line. Consequently no single condition such as “same conductor” or “same dimension of inertia invariants” controls all cases in families.

We therefore define minimality only in the following elementary residual shapes. These are sufficient for the later two-dimensional applications and are stable under coefficient change.

### 7.2 Unramified and finite semisimple residual inertia

**Case U: residual inertia trivial.** The minimal condition is unramified:

$$
\rho_A(I_K)=1.
$$

This introduces no tame direction that was absent residually. A special lift whose monodromy is divisible by $\ell$ may reduce to this residual case, but it belongs to a nonminimal special component, not the minimal one.

**Case F: finite prime-to-$\ell$ residual inertia.** Assume $\bar\rho|_{I_K}$ factors through a finite group $H$ of order prime to $\ell$ and admits the integral model $\theta$ of Chapter 5. The minimal condition is fixed inertial type $\theta$. This preserves every inertial isotypic summand and every wild break seen by that finite action.

For a two-dimensional semisimple example,

$$
\bar\rho|_{I_K}=\bar\eta_1\oplus\bar\eta_2,
$$

with $\bar\eta_i$ of prime-to-$\ell$ order. Their canonical prime-to-$\ell$ lifts $\eta_i$ define the type. If $\bar\eta_1\ne\bar\eta_2$, the two idempotent summands lift uniquely. If they are equal, the inertial type is scalar and does not choose a line; adding a line would be additional structure, not minimal ramification.

The use of an integral model is essential. Merely fixing the traces of inertia elements can lose extension data when the group order is not invertible. In Case F the order is invertible, semisimplicity repairs that problem; outside it we make no such claim.

### 7.3 Nontrivial tame unipotent residual inertia

**Case N: one nonzero tame nilpotent block in dimension two.** After twisting by a fixed finite-order $G_K$-character of order prime to $\ell$, suppose

$$
\bar\rho(\tau)=1+\bar N,
\qquad
\bar N^2=0,\qquad \bar N\ne0,
$$

and wild inertia acts through the fixed scalar twist. The minimal condition is most safely made line-enhanced: retain a lift of the unique residual inertial line and require, for a fixed lift $\eta$ of the scalar character,

$$
\rho_A(\sigma)=\eta_A(\sigma)
\bigl(1+t_\ell(\sigma)N_A\bigr)\qquad(\sigma\in I_K),
$$

where $t_\ell$ is normalized by $t_\ell(\tau)=1$ and

$$
N_A^2=0,\qquad N_A\bmod\mathfrak m_A=\bar N. \tag{7.1}
$$

No additional inertial character is introduced. These are closed equations in the line-enhanced framed tame problem, so they define a closedly represented quotient. Because $\bar N\ne0$, the enhanced line is also recovered as $\ker N_A$; thus forgetting it introduces no extra choice in this residual case.

Because $\bar N\ne0$, the image of $N_A$ contains a unit multiple of a basis vector in an adapted basis. Thus $N_A$ has rank one in the appropriate direct-summand sense at every Artinian level. No open “nonzero” condition is needed: nonvanishing is forced by reduction.

Frobenius is not arbitrary. From (2.2), or directly by expanding powers of a square-zero matrix,

$$
F N_A F^{-1}=qN_A. \tag{7.2}
$$

This is the special relation studied in the next chapter. In Case N it is genuinely minimal because the nonzero monodromy is already present modulo $\ell$.

### 7.4 Scalar twists and reducible inertia

A fixed scalar inertial character $\eta$ can be removed by twisting:

$$
\rho\longmapsto\rho\otimes\eta^{-1}.
$$

If $\eta$ has finite order prime to $\ell$, it has a rigid integral lift. Minimality is then defined for the untwisted representation by Case U, F, or N and twisted back. This procedure preserves representability, tangent dimensions, and conductor differences.

For reducible residual inertia with two distinct prime-to-$\ell$ characters, Case F is appropriate. For a nonsplit residual extension between those characters, one must distinguish two situations. If the extension is carried by a finite group of order prime to $\ell$, semisimplicity says it actually splits, so the supposed nonsplit case cannot occur. If it is carried by the pro-$\ell$ tame direction, it is unipotent after twisting and belongs to Case N. This dichotomy is one of the concrete benefits of $p\ne\ell$.

If residual inertia is scalar and the full residual representation is reducible, minimality does **not** mean preserving a chosen residual line unless that line is part of the deformation datum. The scalar inertial action sees every line. A line-preserving condition may be useful, but it is an ordinary or reducible condition, not forced by minimal ramification.

## 8. Special or Steinberg-shaped deformations

### 8.1 The shape and its arithmetic meaning

Let $d=2$. A special representation is designed to model a single tame extension direction. For a fixed-character condition, choose an unramified character

$$
\psi_0:G_K\longrightarrow\mathcal O^\times
$$

lifting the required residual character, and write $\psi_A$ for its specialization to $A$. A variable-character version instead records an unramified lift $\psi_A$ as part of the deformation datum; the one-dimensional unramified functor represents that extra parameter. We use $\psi$ below for either the fixed specialization or the recorded variable character. Recall that the $\ell$-adic cyclotomic character is unramified at $p\ne\ell$, with

$$
\chi_\ell(\varphi)=q,\qquad \chi_\ell|_{I_K}=1.
$$

In an adapted basis a special-shaped lift has the form

$$
\rho_A(g)=
\begin{pmatrix}
\psi(g)\chi_\ell(g)& * (g)\\
0&\psi(g)
\end{pmatrix}. \tag{8.1}
$$

The upper-right entry is an extension cocycle, not an arbitrary function. On tame inertia it is a multiple of the $\ell$-primary tame character. If $N=e_{12}$ in this basis, then

$$
\rho_A(\tau)=1+tN
$$

after removing the scalar inertial type, and arithmetic Frobenius satisfies

$$
FNF^{-1}=qN. \tag{8.2}
$$

For $F=\operatorname{diag}(a,d)$, equation (8.2) reads

$$
\frac ad=q. \tag{8.3}
$$

Thus the upper character is the lower character times $\chi_\ell$, not its inverse. This direction follows from our arithmetic Frobenius convention.

The determinant is

$$
\det\rho_A=\psi^2\chi_\ell. \tag{8.4}
$$

Therefore a prescribed determinant $\delta$ permits such a special component only when $\delta\chi_\ell^{-1}$ admits the required unramified square root $\psi$. Taking $\psi_0$ as part of the fixed datum avoids claiming that a square root exists or is unique, especially when $\ell=2$.

The adjective “Steinberg-shaped” is only terminology for the elementary matrix pattern (8.1). No classification of representations by a correspondence, and no general theory of monodromy representations, is used in this book.

### 8.2 The closed special condition

The matrix shape (8.1) mentions a line. Fix a residual stable line $\bar L\subset\bar V$ as part of the enhanced residual datum; when the residual diagonal characters are distinct, this line is already determined by its character. A robust enhanced definition records a $G_K$-stable direct-summand line $L_A\subset A^2$ reducing to $\bar L$, identifies the quotient, and requires the two characters on line and quotient to be $\psi\chi_\ell$ and $\psi$. In an adapted frame this is expressed by vanishing of the lower-left matrix entries and equality of the diagonal characters. With fixed $\psi_0$ these are closed equations. With variable $\psi$, adjoining the represented unramified-character datum and imposing the same equations again gives a closed representable enhanced condition.

There is also a useful tame-monodromy coordinate on this enhanced condition. Normalize $t_\ell(\tau)=1$ and record the inertia operator $N_A$ through $\rho_A(\sigma)=1+t_\ell(\sigma)N_A$ after removing the fixed scalar type. Then

$$
N_A^2=0,\qquad FN_AF^{-1}=qN_A. \tag{8.5}
$$

In the elementary rank-two square-zero setting, the group law holds because $N_A^2=0$, and (8.5) is exactly the Frobenius compatibility. Together with the stable-line and diagonal-character equations, (8.5) defines the same closed special-shaped problem in these coordinates.

The qualifications in the preceding sentence are essential. The two equations (8.5) by themselves define a larger monodromy-incidence scheme. At $N_A=0$ the second equation imposes no condition at all on $F$, so that larger scheme contains an entire extraneous unramified locus and has not been proved to be the closure of the desired special points. We therefore call only the line-enhanced problem with its character equations the **closed special condition**.

The closed special condition includes the locus $N_A=0$. This inclusion is deliberate: setting monodromy equal to zero is a closed specialization of special-shaped matrices, while the diagonal-character and line requirements remain in force there.

When the residual monodromy $\bar N$ is nonzero, every lift in this component has nonzero rank-one monodromy and the closed condition already describes the desired special representations. When $\bar N=0$, it also contains the unramified special-shaped extensions satisfying the retained line and character equations. The special generic points then form only part of the closed enhanced space.

### 8.3 Nonzero monodromy is open

Over a field, genuine special behavior requires $N\ne0$. In a family, the locus on which a chosen entry or the rank-one Fitting ideal of $N$ is nonzero is open. It is not defined by quotienting the complete local ring; it is obtained by localization on a generic fiber or by a locally closed construction.

This distinction matters most when $\bar N=0$. Every entry of $N$ lies in the maximal ideal, so reduction cannot certify nonvanishing. The rule

$$
\text{“$N_A\ne0$”}
$$

is not stable under arbitrary coefficient maps: a nonzero nilpotent parameter can map to zero. It is therefore not a deformation subfunctor on all Artinian rings. What is represented by a quotient is the closed enhanced special-shaped problem, including $N=0$; identifying its scheme-theoretic closure after forgetting the enhancement requires a separate descent argument.

A later global deformation problem may use the closed enhanced special ring and then select generic points with nonzero monodromy. If residual monodromy is already nonzero, no such separation is necessary. The global assembly itself remains outside this book.

**Counterexample.** Let the universal monodromy parameter be $x$ in $\mathcal O[[x]]$. The special generic locus is $x\ne0$, but the map

$$
\mathcal O[\varepsilon]/(\varepsilon^2)\longrightarrow k,
\qquad \varepsilon\longmapsto0,
$$

sends a nonzero monodromy parameter to zero. Thus nonvanishing cannot define a base-change-stable Artinian condition.

### 8.4 Enhanced lines, uniqueness, and tangent directions

Suppose the residual diagonal characters in (8.1) are distinct. Equivalently,

$$
q\not\equiv1\pmod\ell
$$

after the common twist is removed. Then the two residual generalized eigenspaces are distinguished, the stable line lifts uniquely, and forgetting the enhanced line identifies the enhanced functor with a closed subfunctor of the ambient unframed problem, subject to the ordinary scalar-centralizer requirement for that ambient quotient.

If $q\equiv1\pmod\ell$, the diagonal residual characters coincide. A residual scalar representation has many lines; an upper-triangular lift may admit more than one; and the image of the line-enhanced functor need not be represented by a simple quotient of the coarse unframed functor. The framed or line-enhanced problem is the safe object.

At a residual point with trivial inertia, Section 6.4 identifies the possible upper-right tame tangent with the $q$-eigenspace of $\operatorname{Ad}_{\bar F}$. If

$$
\bar F=\operatorname{diag}(q\bar\psi(\varphi),\bar\psi(\varphi))
$$

and the two eigenvalues are distinct, this eigenspace is exactly $k e_{12}$. The special condition retains that tame line together with the allowed unramified variation of $\psi$ and, if determinant is not fixed, the corresponding scalar direction. Fixing determinant usually removes the unramified variation of $\psi$ once a square root branch has been fixed.

Here is the generic tangent count in cohomological form. Assume $q\not\equiv1\pmod\ell$, fix both diagonal characters in (8.1), and suppose residual inertia is trivial. Upper-triangular extensions are classified by

$$
H^1\bigl(K,k(\bar\chi_\ell)\bigr).
$$

Arithmetic Frobenius acts on this coefficient line by $q$. It has no invariants because $q\ne1$, while its Tate-dual has one invariant. The local Euler formula therefore gives

$$
\dim_kH^1\bigl(K,k(\bar\chi_\ell)\bigr)=1. \tag{8.6}
$$

The unique direction is the tame monodromy direction; there is no unramified extension direction because $\varphi-1$ is invertible on the coefficient line. If $\psi$ is allowed to vary unramified, one further scalar direction appears. If the determinant is fixed and $\ell\ne2$, the equation $\delta=\psi^2\chi_\ell$ removes that scalar direction, leaving the one-dimensional special tangent. When $q=1$ or $\ell=2$, this count must be replaced by the trace-kernel and relation calculation because diagonal characters or the squaring map cease to be transverse.

For residual nonzero monodromy, the tangent condition also requires preservation of the rank-one nilpotent orbit. In an adapted frame the allowed $Y$ is tangent to that orbit plus scaling of $N$, and (8.5) couples it to $X=c(\varphi)$. The exact dimension is the kernel dimension of the derivative of (8.5), minus the permitted change-of-basis directions in the unframed problem. It should be computed from those equations in exceptional characteristics rather than imported from a generic formula.

## 9. Fixed determinant and characteristic two

### 9.1 Determinant as a condition in every construction

Fixing determinant is not a final cosmetic quotient. It affects which inertial types and special characters are admissible.

- For unramified deformations, $\delta$ must be unramified.
- For fixed inertial type $\theta$, one must have
  $$
  \det\theta=\delta|_{I_K}.
  $$
- For a special component with fixed $\psi$, one must have $\delta=\psi^2\chi_\ell$.
- For a tame matrix pair, one adds $\det F=\delta(\varphi)$ and $\det T=\delta(\tau)$, together with the fixed wild determinant.

Each is a closed matrix equation and therefore gives a quotient of the already represented framed condition. Compatibility must be checked at the residual point; otherwise the proposed quotient has no object over $k$ and is not a deformation problem of $\bar\rho$.

### 9.2 Trace-zero tangent modules

For a first-order lift

$$
\rho_\varepsilon(g)=(1+\varepsilon c(g))\bar\rho(g),
$$

one has

$$
\det\rho_\varepsilon(g)
=\det\bar\rho(g)(1+\varepsilon\operatorname{tr}c(g)).
$$

Thus framed fixed-determinant cocycles take values in $M^0$. For an unframed problem, the universally correct tangent description is

$$
\ker\bigl(H^1(K,M)\xrightarrow{\operatorname{tr}}H^1(K,k)\bigr), \tag{9.1}
$$

intersected with the chosen local subspace. If $\ell\nmid d$, the equivariant splitting

$$
M=k\cdot I\oplus M^0
$$

identifies (9.1) with $H^1(K,M^0)$.

For a local condition with tangent $L\subseteq H^1(K,M)$, its fixed-determinant tangent is

$$
L^\delta=L\cap\ker H^1(\operatorname{tr}). \tag{9.2}
$$

This formula applies uniformly to unramified, fixed-type, tame, minimal, and special conditions.

### 9.3 What fails in characteristic two

When $d=2$ and $\ell=2$,

$$
\operatorname{tr}(I)=2=0.
$$

Hence scalar matrices lie inside $M^0$. The trace pairing restricted to $M^0$ is degenerate, and there is no equivariant direct-sum decomposition of $M$ into scalars and trace zero. Three consequences follow.

First, fixing determinant does not remove scalar infinitesimal changes. Second, the unframed tangent cannot be obtained by subtracting one from a dimension formula unless surjectivity of the trace map on the relevant $H^1$ has separately been proved. Third, the Tate dual of $M^0$ is naturally related to the quotient $M/kI$, not automatically to $M^0$ itself.

The framed determinant equation remains smooth even in characteristic two. The problem lies in decomposing conjugation directions and dual modules, not in differentiating determinant on $\operatorname{GL}_2$. For this reason framed fixed-determinant rings are often the cleanest local objects at $\ell=2$, even though the residue characteristic $p$ of $K$ is different from two.

## 10. Obstructions, dimensions, and dual local conditions

### 10.1 Ambient obstruction spaces

For the unrestricted local deformation problem, small-extension obstructions lie in

$$
H^2(K,M).
$$

Tate local duality identifies its dual with

$$
H^0(K,M^*(1)).
$$

The trace pairing gives $M^*\simeq M$, so

$$
h^2_K(M)=h^0_K(M(1)). \tag{10.1}
$$

Thus ambient unobstructedness follows from the absence of a cyclotomic self-twist in the adjoint representation. It does not follow merely from absolute irreducibility: an absolutely irreducible representation can be isomorphic to an appropriate cyclotomic twist of itself.

For fixed determinant with $\ell\nmid d$, the analogous obstruction group is $H^2(K,M^0)$ and

$$
h^2_K(M^0)=h^0_K(M^0(1)). \tag{10.2}
$$

When $\ell\mid d$, one must use the actual determinant-preserving obstruction construction and the dual quotient described in Section 9.3.

Constrained conditions can be smoother than the ambient problem. Unramified framed lifts are smooth because a Frobenius matrix always lifts. A compatible fixed prime-to-$\ell$ inertial type is smooth because finite-group cohomology is killed by averaging and its Frobenius intertwiners form a torsor under the smooth inertia-centralizer group. If one imposes further equations on that intertwiner—fixed determinant when the centralizer trace is not onto, fixed characteristic polynomial, or a special eigenvalue relation—new obstructions can appear. For the unrestricted tame two-generator problem, the explicit cokernel (6.7) is the relevant first obstruction detector.

### 10.2 Euler characteristic and Tate duality

Because $p\ne\ell$, the local Euler characteristic has no field-degree term. For every finite-dimensional $k[G_K]$-module $N$,

$$
h^1_K(N)=h^0_K(N)+h^2_K(N)
=h^0_K(N)+h^0_K(N^*(1)). \tag{10.3}
$$

Applied to $M$, this gives

$$
h^1_K(M)=h^0_K(M)+h^0_K(M(1)). \tag{10.4}
$$

The framed ambient tangent dimension is

$$
\dim_k Z^1(K,M)
=h^1_K(M)+d^2-h^0_K(M)
=d^2+h^0_K(M(1)). \tag{10.5}
$$

Thus the centralizer cancels in the framed dimension, while the twisted centralizer remains as the obstruction contribution.

For unramified or fixed-type conditions,

$$
\dim_kL_{\mathrm{ur}}=\dim_kL_\theta=h^0_K(M). \tag{10.6}
$$

This equality does not assert ambient smoothness. It says that the permitted unframed tangent directions are exactly as numerous as global centralizer elements. The explicit Frobenius description proves smoothness only in the framed or cyclic-matrix situations already stated.

**Two-character calculation.** Let

$$
\bar\rho=\chi_1\oplus\chi_2
$$

with both characters unramified, and set $\alpha=\chi_1(\varphi)\chi_2(\varphi)^{-1}$. Then

$$
M\simeq k\oplus k\oplus k(\alpha)\oplus k(\alpha^{-1}).
$$

The upper-right line contributes invariants when $\alpha=1$ and obstructions when $\alpha=q$; the lower-left line uses $\alpha^{-1}$. Therefore ratios $1,q,q^{-1}$ are precisely the exceptional values. If $q=1$ in $k$, even the diagonal lines acquire tame obstruction partners. This calculation explains both reducible tangent jumps and the special eigenvalue relation.

### 10.3 Orthogonals

For any tangent condition

$$
L\subseteq H^1(K,N),
$$

Tate local duality defines its exact orthogonal

$$
L^\perp\subseteq H^1(K,N^*(1)).
$$

Perfectness gives

$$
\dim L+\dim L^\perp=h^1_K(N). \tag{10.7}
$$

When $p\ne\ell$, the unramified condition is orthogonal to the unramified condition on the Tate-dual module:

$$
H^1_{\mathrm{ur}}(K,N)^\perp
=H^1_{\mathrm{ur}}(K,N^*(1)). \tag{10.8}
$$

Consequently the tangent spaces of fixed prime-to-$\ell$ inertial type, which equal unramified cohomology, have the same orthogonal description. This is an exact theorem, not a dimension guess.

For a tame or special tangent space, the safe definition of the dual local condition is simply the annihilator under the pairing. In favorable two-character cases one can compute it by decomposing $M$ into character lines and pairing the upper-right line with the oppositely directed twisted line. There is no general reason for a special condition to be self-orthogonal, and representability of $L^\perp$ as a deformation condition does not follow merely from its being a subspace.

If $\ell\nmid d$, the trace pairing identifies $(M^0)^*(1)$ with $M^0(1)$, so fixed-determinant orthogonals live in $H^1(K,M^0(1))$. In characteristic dividing $d$, the dual coefficient is the appropriate quotient; using $M^0(1)$ without correction would give the wrong annihilator.

### 10.4 Why smoothness can jump

There are three distinct sources of singularity.

1. **Ambient dual invariants:** $H^0(K,M(1))\ne0$ supplies possible $H^2$ obstructions.
2. **Relation degeneracy:** the derivative $d^1$ of the tame equation can fail to be surjective, especially when Frobenius eigenvalue ratios equal $q$.
3. **Orbit degeneracy:** a scalar residual matrix has a large centralizer, so an unframed coarse quotient can fail gluing even if every framed lift exists.

These phenomena can coincide but should not be conflated. For example, at trivial residual inertia with distinct Frobenius eigenvalues in special ratio $q$, the tame relation gains an upper-right direction because the same character line contributes a twisted invariant. At scalar Frobenius with $q\not\equiv1$, no tame tangent exists, yet the unframed conjugacy problem still has a large stabilizer. Smoothness is a statement about lifting in a specified functor, not a property of the residual representation in isolation.

## 11. Conductors and exact minimality

### 11.1 What conductor constancy really requires

For a characteristic-zero representation with finite inertial image, Book 3 defines the Artin conductor by the weighted codimensions of fixed spaces under the ramification groups:

$$
a_K(V)=\operatorname{codim}V^{I_K}
+\operatorname{Sw}_K(V).
$$

The special representations in this book can have infinite pro-$\ell$ tame image, so the finite-image definition cannot silently be applied to them. In the explicit square-zero tame case we use the elementary extension of the conductor exponent

$$
a_K(V):=\operatorname{codim}V^{I_K}
$$

when wild inertia is trivial. Everything claimed below for such a representation follows directly from this definition and the displayed inertia matrices; no general conductor theorem for arbitrary infinite-image representations is being assumed.

To prove conductor constancy in a family, it is not enough to know that matrices reduce to a fixed residual shape. In the finite-image case one needs the fixed submodules for the relevant ramification groups to remain finite direct summands of constant rank. In the square-zero tame case one needs an explicit constant-rank normal form. The first requirement is automatic for a fixed finite group of order invertible in the coefficient ring: the averaging idempotent

$$
e_H=\frac1{|H|}\sum_{h\in H}h
$$

projects onto invariants and commutes with base change.

It is also automatic in the nonzero rank-one tame unipotent case. If inertia acts by $1+t_\ell(\sigma)N$ with $N$ a rank-one square-zero operator on a free rank-two module, then

$$
V^{I_K}=\ker N
$$

is a direct summand of rank one. Hence the conductor is exactly one.

### 11.2 Finite type and tame unipotent preservation

**Finite-type preservation theorem.** Let $B$ be a characteristic-zero coefficient field, and suppose the inertial action on a finite-dimensional $B$-space is conjugate to the scalar extension of a fixed finite representation $\theta$ of a quotient $H$ with $\ell\nmid|H|$. Then

$$
\dim_BV^{G_i}
$$

is independent of further coefficient-field extension for every lower ramification group $G_i$, and the Artin and Swan conductors equal those of $\theta$. The same statement over a coefficient domain is read after passage to its fraction field, with dimensions replaced beforehand by ranks of the invariant direct summands.

**Proof.** Each image of $G_i$ is a subgroup $H_i\le H$. Since $|H_i|$ is invertible, the averaging idempotent $e_{H_i}$ has image $V^{H_i}$. Idempotent images commute with flat coefficient extension and have locally constant rank. The weighted conductor formula depends only on these ranks and the fixed ramification filtration of the finite quotient. Therefore every term is preserved. $\square$

This proves the conductor assertion in minimal Case F, including wild finite actions: their breaks and fixed-space codimensions are literally frozen by the type.

**Tame-unipotent preservation theorem.** Let $V$ have rank two over a characteristic-zero coefficient field and suppose wild inertia is trivial while tame inertia acts nontrivially through

$$
\rho(\sigma)=1+t_\ell(\sigma)N,\qquad
N^2=0,\qquad\operatorname{rank}N=1.
$$

Then the wild contribution is zero, $\dim V^{I_K}=1$, and the elementary tame conductor exponent of Section 11.1 is

$$
a_K(V)=1.
$$

**Proof.** Wild inertia acts trivially. Some tame element has nonzero parameter, and its fixed vectors are exactly $\ker N$. Rank one of $N$ makes this kernel one-dimensional. The tame conductor is its codimension, namely one. $\square$

Thus Case N and the genuine special locus preserve conductor one. The closed enhanced special space also contains $N=0$, where the conductor is zero. Conductor is therefore not constant on that closed space when residual monodromy vanishes.

### 11.3 Counterexamples to naive semicontinuity claims

Take a one-parameter special family with

$$
N=x e_{12}.
$$

At every characteristic-zero point with $x\ne0$, the conductor is one. At $x=0$, the representation is unramified and the conductor is zero. Hence conductor constancy fails on the closed enhanced special family even though every matrix satisfies the same square-zero and Frobenius-scaling equations together with the retained line and character equations.

Reduction modulo $\ell$ creates the same phenomenon. If $x=\ell$, the characteristic-zero representation has conductor one but its residual inertia is trivial. Thus equality of residual and lifted conductors is a substantive minimality requirement, not an automatic consequence of $p\ne\ell$.

There is a complementary warning for finite inertia of order divisible by $\ell$. Averaging is unavailable, invariant submodules need not be direct summands, and their ranks can jump under reduction. This is why the finite-type theorem required $\ell\nmid|H|$. The present book does not disguise the missing modular representation theory by calling such a type fixed.

## 12. Functoriality

### 12.1 Extension of coefficient fields

Let $\mathcal O\to\mathcal O'$ be a flat local extension of complete coefficient rings, with residue-field extension $k\to k'$. The standard example is extension of the ring of integers in the coefficient field. Base-changing $\bar\rho$ and every chosen integral datum gives a deformation problem over $\mathcal O'$. The conditions developed above commute with this operation under their stated hypotheses.

- Killing inertia commutes with tensor product, so unramified conditions base-change.
- A fixed type $\theta$ becomes $\theta\otimes_{\mathcal O}\mathcal O'$; prime-to-$\ell$ averaging still applies.
- The tame equation $FTF^{-1}=T^q$ has integral coefficients and is unchanged.
- The stable-line, character, and monodromy equations defining the enhanced special condition base-change.
- A fixed determinant becomes $\delta\otimes\mathcal O'$.

At the level of rings, flatness gives the expected completed scalar extension of the original framed quotient when the residual datum is merely scalar-extended and no new enhancement is selected. If a coefficient extension splits a residual characteristic polynomial that was irreducible, enhanced eigenline problems can acquire new choices or components. The intrinsic matrix condition still base-changes correctly, but a claim about a particular line must be reformulated after the splitting. For a nonflat map of coefficient bases there is still a natural transformation on deformation problems, but no blanket completed-tensor-product formula is asserted.

Tangent spaces satisfy

$$
L_{\mathcal D,k'}\simeq L_{\mathcal D,k}\otimes_k k'
$$

when the defining finite-group invariants commute with extension and the residual datum is simply scalar-extended. This holds for unramified and prime-to-$\ell$ fixed-type conditions, and for tame equation kernels after ordinary linear algebra base change.

### 12.2 Changing and forgetting frames

Changing the chosen residual basis conjugates $\bar\rho$, $\bar F$, $\bar T$, and every displayed type matrix simultaneously. The resulting framed functors are canonically isomorphic after carrying the frame along. Hence conditions stated intrinsically—trivial inertia, isomorphism to $\theta$, existence of the specified enhanced line, or the monodromy equations—do not depend on the initial coordinates.

Forgetting a frame is formally smooth only after one specifies what automorphisms remain. In an ambient problem with scalar residual centralizer, the relative tangent dimension is $d^2-1$. More generally the space of infinitesimal frame changes visible in the orbit is

$$
B^1(K,M),\qquad
\dim B^1=d^2-h^0_K(M).
$$

For a condition, the stabilizer may be larger because an enhancement is retained or an inertial normal form has its own centralizer. The relative dimension must then be computed from the actual automorphism group of the conditioned object.

Three safe practices emerge:

1. use framed rings whenever residual matrices are scalar or have large centralizers;
2. retain an eigenline or inertial rigidification if it is arithmetic data rather than silently quotienting it away;
3. invoke an unframed universal ring only after verifying scalar descent, cyclic-matrix classification, or another exact orbit theorem.

### 12.3 Unramified base change of local fields

Let $K'/K$ be unramified of residue degree $f$. Then

$$
I_{K'}=I_K,\qquad q'=q^f,\qquad
\varphi_{K'}=\varphi_K^f
$$

inside the residue quotient. Restriction of a tame representation sends

$$
(F,T)\longmapsto(F^f,T),
$$

and the relation becomes

$$
F^fT F^{-f}=T^{q^f}. \tag{12.1}
$$

Thus unramified representations remain unramified, and a fixed inertial type remains the same because inertia is unchanged. A special relation becomes

$$
F^fN F^{-f}=q^fN,
$$

exactly matching $\chi_\ell(\varphi_{K'})=q^f$.

For finite inertial type, Artin and Swan conductors are unchanged under unramified base change: the inertia and higher ramification groups, with their indices, are the same. The elementary tame exponent of the rank-one unipotent case is likewise unchanged because the inertia invariants are unchanged. This gives a useful consistency check on all three minimal cases.

Restriction can nevertheless change centralizers and tangent dimensions. Frobenius eigenvalues $\alpha$ and $\beta$ that were distinct can satisfy $\alpha^f=\beta^f$, making $F^f$ scalar or noncyclic. An existing exceptional relation $\alpha\beta^{-1}=q$ persists after restriction, while a new one can appear when

$$
\bigl(\alpha\beta^{-1}q^{-1}\bigr)^f=1
$$

even though $\alpha\beta^{-1}\ne q$. Therefore representability of a particular unframed conjugacy quotient must be rechecked after base change even though the intrinsic ramification condition is preserved.

For unramified tangent classes, restriction is described by the norm polynomial

$$
1+\varphi+\cdots+\varphi^{f-1}
$$

on Frobenius values. This can have a kernel in characteristic $\ell$ when $\ell\mid f$; equality of inertia does not make the restriction map on $H^1_{\mathrm{ur}}$ an isomorphism.

## 13. A menu for global deformation problems

### 13.1 Representable conditions and tangent spaces

The following table records only conclusions proved under explicit hypotheses. Here $M=\operatorname{ad}\bar\rho$, $c=h^0_K(M)$, and “framed dimension” means relative tangent dimension over the coefficient base.

| Condition | Residual hypothesis | Safe represented object | Unframed tangent | Smoothness statement |
|---|---|---|---|---|
| Unramified | $\bar\rho(I_K)=1$ | framed quotient | $H^1_{\mathrm{ur}}(K,M)$, dimension $c$ | framed smooth of dimension $d^2$ |
| Unramified, fixed $\delta$ | above and $\delta|_I=1$ | framed quotient | kernel of trace on $H^1_{\mathrm{ur}}$ | framed smooth of dimension $d^2-1$ |
| Unramified, cyclic Frobenius | $\bar F$ cyclic | unframed ring | dimension $d$ | smooth of dimension $d$ |
| Same, fixed determinant | cyclic $\bar F$ | unframed ring | dimension $d-1$ | smooth of dimension $d-1$ |
| Fixed finite type $\theta$ | $|H|$ prime to $\ell$ and compatible integral $\theta$ | framed quotient; unframed with descent | $H^1_{\mathrm{ur}}(K,M)$, dimension $c$ | framed smooth of dimension $d^2$; fixed determinant gives $d^2-1$ when the centralizer trace is onto |
| Full tame | wild action killed | framed matrix quotient | $H^1(C^\bullet_{\mathrm{tame}})$ | smooth if $d^1$ is surjective |
| Minimal unipotent | nonzero residual rank-one $\bar N$ and fixed scalar type | framed quotient; the line enhancement is redundant because $\ker N$ recovers it | derivative kernel modulo allowed conjugacy | nonvanishing automatic; smooth if the derivative of all defining equations is surjective |
| Closed special | compatible fixed or represented variable diagonal data | line-enhanced framed quotient; descended quotient only when the line is unique and ambient unframed descent holds | special relation subspace; dimension $1$ with fixed diagonal characters in the generic case (8.6) | contains the special-shaped $N=0$ locus; no blanket smoothness claim |

For every row, fixed determinant means intersection with the kernel of the determinant derivative. When $\ell\nmid d$, one may replace $M$ by $M^0$ in the standard cohomological formulas. When $\ell\mid d$, use the trace-kernel and dual-quotient formulations instead.

For a fixed nontrivial wild action, Section 6.1 still gives a framed quotient, but the normalizer equations must be added and the tangent is the kernel of their augmented derivative. The three-term complex (6.6) and its smoothness test are listed only for trivial wild action.

The menu deliberately does not list “all lifts of the same conductor.” Without a fixed finite type or constant-rank monodromy model, that property need not be closed or stable under arbitrary Artinian base change.

### 13.2 Two-dimensional selection table

For later two-dimensional applications, the residual inertia matrix gives a quick first classification.

| Residual inertial shape after a rigid scalar twist | Intended arithmetic behavior | Condition |
|---|---|---|
| $1$ | no new ramification | unramified |
| $\operatorname{diag}(\bar\eta_1,\bar\eta_2)$, prime-to-$\ell$ finite | preserve finite semisimple ramification | fixed inertial type |
| $1+\bar N$, $\bar N\ne0$, $\bar N^2=0$ | preserve existing multiplicative ramification | minimal unipotent/special |
| $1$ but Frobenius eigenvalue ratio $q$ | allow a characteristic-zero multiplicative component | closed line-enhanced special condition, not minimal unramified |
| scalar with no distinguished line | preserve ramification only | framed intrinsic condition; do not impose a line without adding it as data |

The full residual representation, not inertia alone, then decides representability and dimension. A nonscalar Frobenius permits cyclic-matrix unframed coordinates. A scalar Frobenius calls for framing. Distinct diagonal characters make an enhanced line unique; coincident characters do not. Eigenvalue ratios $q$ and $q^{-1}$ identify the two possible special extension orientations.

### 13.3 The decision procedure

To select a local condition at a place of residue characteristic $p\ne\ell$, proceed in the following order.

**Step 1: identify the arithmetic target.** Decide whether the lift should be unramified, retain existing finite inertia, retain existing nonzero tame monodromy, or permit a new special component. Do not begin with the word “minimal.”

**Step 2: compute residual inertia.** Separate the wild $p$-group image, the finite prime-to-$\ell$ tame image, and any pro-$\ell$ unipotent shadow. If a finite image has order divisible by $\ell$, the elementary fixed-type theorem does not apply.

**Step 3: fix determinant data.** Verify compatibility on inertia and Frobenius. In the special case decide whether $\psi$ is fixed or whether a chosen square-root branch of $\delta\chi_\ell^{-1}$ is part of the datum.

**Step 4: choose framed, unframed, or enhanced form.** Use a framed problem by default at scalar residual matrices. Use an enhanced line when the line itself matters. Forget it only if distinct residual characters or another descent theorem makes it unique. Use cyclic Frobenius when classifying an unramified matrix by its characteristic polynomial.

**Step 5: write the exact equations.** They are respectively

$$
T=1,
$$

$$
\rho|_I\sim\theta,
$$

$$
FTF^{-1}=T^q,
$$

or

$$
N^2=0,\qquad FNF^{-1}=qN.
$$

For the special condition, also include the stable-line and diagonal-character equations: the two monodromy equations alone have an extraneous $N=0$ locus. In every case include the fixed wild action and determinant equations. These equations prove closedness only for the data they actually record.

**Step 6: compute the tangent space.** Use $H^1_{\mathrm{ur}}$ for unramified and fixed-type conditions. Use the complex (6.6) for the full tame condition. For special conditions, linearize (8.5) in an adapted framed or enhanced problem. Intersect with the trace kernel for fixed determinant.

**Step 7: test smoothness rather than assume it.** A single Frobenius matrix lifts smoothly. A prime-to-$\ell$ finite group is rigid by averaging. A tame relation is smooth when its derivative is surjective. An unframed quotient additionally requires control of stabilizers.

**Step 8: verify conductor claims.** Fixed prime-to-$\ell$ type preserves all ramification-group invariant ranks. Nonzero rank-one tame monodromy has conductor one. The closed enhanced special condition need not have constant conductor.

**Step 9: record the Tate-dual tangent condition.** For unramified and fixed-type tangents it is unramified on the dual. Otherwise take the exact annihilator and refrain from assigning it an arithmetic name until proved.

**Step 10: check functoriality needed later.** Extend coefficients, change frames, and restrict to unramified field extensions using the formulas of Chapter 12. Recheck cyclicity and centralizers after field extension.

This procedure produces not merely a label but a package:

$$
\bigl(\text{intrinsic condition},\ \text{representing object},
\ \text{tangent space},\ \text{obstructions},
\ \text{determinant},\ \text{dual},\ \text{conductor}\bigr).
$$

That is the unit of local information needed in a global deformation problem.

## 14. Conclusion

### 14.1 Local equations with global consequences

Away from $\ell$, local deformation theory is governed by a sharp asymmetry inside inertia. Wild pro-$p$ actions are rigid in $\ell$-adic congruence directions, while the pro-$\ell$ tame factor can move. Arithmetic Frobenius controls that motion through

$$
\varphi\tau\varphi^{-1}=\tau^q.
$$

From this one relation come the universal Frobenius description of unramified lifts, the rigidity of prime-to-$\ell$ inertial types, the tame deformation complex, and the special equation $FNF^{-1}=qN$.

The formal geometry is as important as the matrix shapes. Framing cures orbit problems but adds coboundary directions. Cyclic Frobenius gives a genuine unframed coordinate system where scalar-centralizer arguments do not apply. A chosen line makes the enhanced special problem representable, yet forgetting it is safe only when uniqueness or descent has been proved. Nonzero monodromy is open, whereas the closed enhanced condition also contains its $N=0$ specializations. Fixed determinant is controlled by trace when $\ell\nmid d$ and demands greater care in characteristic two.

Minimality has consequently acquired an exact meaning rather than a slogan. Trivial residual inertia leads to the unramified condition. Finite prime-to-$\ell$ inertia leads to a fixed integral type. Existing nonzero rank-one tame monodromy leads to the minimal special condition. Each preserves conductor for a proved reason: an averaging idempotent in the finite case, and a constant-rank kernel in the unipotent case.

Finally, tangent spaces now come paired with their duals and with honest obstruction tests. Unramified and fixed-type tangents are $H^1_{\mathrm{ur}}$ and are orthogonal to the corresponding unramified dual spaces. Tame and special tangents arise by differentiating their defining equations. Local Euler characteristic and Tate duality explain the exceptional eigenvalue ratios but never substitute for a lifting proof.

The result is a finite, rigorous menu of local conditions. Each entry says what ramification is retained, which choices are remembered, what ring represents the condition, what its tangent directions are, when it is smooth, how determinant and duality modify it, and under which hypotheses its conductor remains constant. These local packages are now ready to be assembled, without ambiguity, into global deformation problems.
