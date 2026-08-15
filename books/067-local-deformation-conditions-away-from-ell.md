# Local Deformation Conditions Away from $\ell$

## Contents

1. [The local design problem](#1-the-local-design-problem)
   - [Why away from $\ell$ is a structural simplification](#11-why-away-from-ell-is-a-structural-simplification)
   - [Standing notation](#12-standing-notation)
   - [What a local condition must accomplish](#13-what-a-local-condition-must-accomplish)
   - [Hypotheses that will not be suppressed](#14-hypotheses-that-will-not-be-suppressed)
2. [Inertia seen by $\ell$-adic coefficients](#2-inertia-seen-by-ell-adic-coefficients)
   - [Wild rigidity and tame flexibility](#21-wild-rigidity-and-tame-flexibility)
   - [Arithmetic Frobenius and the tame relation](#22-arithmetic-frobenius-and-the-tame-relation)
   - [Finite inertial image and its limits](#23-finite-inertial-image-and-its-limits)
   - [The wild rigidity lemma](#24-the-wild-rigidity-lemma)
   - [Continuity and the two-generator presentation](#25-continuity-and-the-two-generator-presentation)
3. [Local deformation conditions as formal subspaces](#3-local-deformation-conditions-as-formal-subspaces)
   - [The ambient functors](#31-the-ambient-functors)
   - [A definition designed for base change](#32-a-definition-designed-for-base-change)
   - [Closedness, enhancement, and representability](#33-closedness-enhancement-and-representability)
   - [Tangent and obstruction modules](#34-tangent-and-obstruction-modules)
   - [A relative representability test](#35-a-relative-representability-test)
4. [Unramified deformations](#4-unramified-deformations)
   - [The intrinsic condition](#41-the-intrinsic-condition)
   - [The universal Frobenius matrix](#42-the-universal-frobenius-matrix)
   - [Unframed conjugacy and the cyclic-vector hypothesis](#43-unframed-conjugacy-and-the-cyclic-vector-hypothesis)
   - [Fixed determinant](#44-fixed-determinant)
   - [Tangent spaces and smoothness](#45-tangent-spaces-and-smoothness)
   - [Characters, scalar Frobenius, and exact boundary cases](#46-characters-scalar-frobenius-and-exact-boundary-cases)
5. [Fixed finite inertial type](#5-fixed-finite-inertial-type)
   - [Why an inertial type needs an integral model](#51-why-an-inertial-type-needs-an-integral-model)
   - [The elementary prime-to-$\ell$ condition](#52-the-elementary-prime-to-ell-condition)
   - [Independence, closedness, and lifting](#53-independence-closedness-and-lifting)
   - [The tangent condition](#54-the-tangent-condition)
   - [The fixed-type smoothness and dimension theorem](#55-the-fixed-type-smoothness-and-dimension-theorem)
   - [Two finite-type calculations](#56-two-finite-type-calculations)
6. [Tame matrix deformation problems](#6-tame-matrix-deformation-problems)
   - [Generators and equations](#61-generators-and-equations)
   - [Linearizing the tame relation](#62-linearizing-the-tame-relation)
   - [A deformation complex and smoothness criterion](#63-a-deformation-complex-and-smoothness-criterion)
   - [Two-dimensional examples](#64-two-dimensional-examples)
   - [The small-extension defect of the tame relation](#65-the-small-extension-defect-of-the-tame-relation)
   - [Exact dimensions at trivial residual inertia](#66-exact-dimensions-at-trivial-residual-inertia)
7. [Minimal ramification, case by case](#7-minimal-ramification-case-by-case)
   - [Why there is no universal minimum](#71-why-there-is-no-universal-minimum)
   - [Unramified and finite semisimple residual inertia](#72-unramified-and-finite-semisimple-residual-inertia)
   - [Nontrivial tame unipotent residual inertia](#73-nontrivial-tame-unipotent-residual-inertia)
   - [Scalar twists and reducible inertia](#74-scalar-twists-and-reducible-inertia)
   - [The liftability theorem for nonzero residual monodromy](#75-the-liftability-theorem-for-nonzero-residual-monodromy)
8. [Special or Steinberg-shaped deformations](#8-special-or-steinberg-shaped-deformations)
   - [The shape and its arithmetic meaning](#81-the-shape-and-its-arithmetic-meaning)
   - [The closed special condition](#82-the-closed-special-condition)
   - [Nonzero monodromy is open](#83-nonzero-monodromy-is-open)
   - [Enhanced lines, uniqueness, and tangent directions](#84-enhanced-lines-uniqueness-and-tangent-directions)
   - [The generic special component in coordinates](#85-the-generic-special-component-in-coordinates)
   - [Exceptional special points](#86-exceptional-special-points)
9. [Fixed determinant and characteristic two](#9-fixed-determinant-and-characteristic-two)
   - [Determinant as a condition in every construction](#91-determinant-as-a-condition-in-every-construction)
   - [Trace-zero tangent modules](#92-trace-zero-tangent-modules)
   - [What fails in characteristic two](#93-what-fails-in-characteristic-two)
   - [Determinant fibers inside constrained problems](#94-determinant-fibers-inside-constrained-problems)
10. [Obstructions, dimensions, and exceptional loci](#10-obstructions-dimensions-and-exceptional-loci)

- [Ambient obstruction spaces](#101-ambient-obstruction-spaces)
- [Euler characteristic and the top-degree calculation](#102-euler-characteristic-and-the-top-degree-calculation)
- [Unramified classes and relation obstructions](#103-unramified-classes-and-relation-obstructions)
- [Why smoothness can jump](#104-why-smoothness-can-jump)
- [Trace-zero dual coefficients](#105-trace-zero-dual-coefficients)
- [Three obstruction calculations](#106-three-obstruction-calculations)

11. [Conductors and exact minimality](#11-conductors-and-exact-minimality)

- [What conductor constancy really requires](#111-what-conductor-constancy-really-requires)
- [Finite type and tame unipotent preservation](#112-finite-type-and-tame-unipotent-preservation)
- [Counterexamples to naive semicontinuity claims](#113-counterexamples-to-naive-semicontinuity-claims)
- [Twists and higher ramification data](#114-twists-and-higher-ramification-data)

12. [Functoriality](#12-functoriality)

- [Extension of coefficient fields](#121-extension-of-coefficient-fields)
- [Changing and forgetting frames](#122-changing-and-forgetting-frames)
- [Unramified base change of local fields](#123-unramified-base-change-of-local-fields)
- [What changes under ramified base change](#124-what-changes-under-ramified-base-change)

13. [A menu for global deformation problems](#13-a-menu-for-global-deformation-problems)

- [Representable conditions and tangent spaces](#131-representable-conditions-and-tangent-spaces)
- [Two-dimensional selection table](#132-two-dimensional-selection-table)
- [The decision procedure](#133-the-decision-procedure)
- [The local package theorem](#134-the-local-package-theorem)

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

Let $k$ be a finite field of characteristic $\ell\ne p$. Let $\mathcal O$ be a complete Noetherian local $\mathbf Z_\ell$-algebra with residue field $k$; the principal example is the ring of integers in a finite extension of $\mathbf Q_\ell$. Its maximal ideal is $\mathfrak m_{\mathcal O}$. The coefficient category $\mathcal C_{\mathcal O}$ consists of local Artinian $\mathcal O$-algebras $A$ equipped with an identification $A/\mathfrak m_A\simeq k$. The $\mathbf Z_\ell$-algebra structure is what allows the $\ell$-adic cyclotomic character to be viewed as $A$-valued later.

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

We write $N^*=\operatorname{Hom}_k(N,k)$ with the contragredient action and $N(1)=N\otimes_k k(\bar\chi_\ell)$ for the mod-$\ell$ cyclotomic twist. Thus $N^*(1)$ is the twisted linear dual. This notation is used only for the elementary top-degree calculation of Chapter 10; no general local-duality theorem is assumed.

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

### 1.4 Hypotheses that will not be suppressed

Several assumptions recur often enough that it is useful to explain their separate jobs. The field $K$ is always a nonarchimedean local field with **finite** residue field. Finiteness supplies a Frobenius generator and the integer $q$ in the tame relation. The coefficient residue characteristic satisfies $p\ne\ell$. This makes finite $p$-groups linearly reductive over every coefficient ring in sight and removes the $[K:\mathbf Q_p]\dim N$ term from the $\ell$-primary local Euler characteristic.

These two assumptions do not imply any of the following stronger properties:

- inertia need not act trivially;
- the inertial image of a characteristic-zero lift need not be finite;
- the residual local representation need not be irreducible;
- its centralizer need not consist of scalars;
- $q-1$, $q+1$, or $2$ need not be units in $\mathcal O$;
- a determinant character need not admit a square root.

Every theorem below that needs one of these extra properties states it. In particular, there are three logically independent prime-to conditions. The inequality $p\ne\ell$ concerns the residue characteristic of $K$. The condition $\ell\nmid |H|$ concerns rigidity of a chosen finite inertial quotient. The condition $q\not\equiv1\pmod\ell$ separates the two residual characters of a special representation. None can replace another.

We use four pieces of earlier theory. Ramification theory supplies $P_K$, tame inertia, higher ramification groups, and conductor formulas for finite-image representations. Local Galois cohomology supplies inflation--restriction, the Frobenius description of unramified $H^1$, the two-step calculation of $H^2$, and the Euler characteristic. General deformation theory supplies the cocycle and obstruction constructions. Formal representability supplies universal framed rings and the closed-subfunctor criterion. Whenever a more specialized assertion is needed, such as rigidity of a finite inertial action, the top-degree adjoint calculation, or smoothness of a special normal form, it is proved here rather than hidden inside one of those general inputs.

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

### 2.4 The wild rigidity lemma

The slogan that wild inertia is rigid should be converted into a lemma that can actually be used in a lifting argument.

**Lemma 2.1 (prime-to-$\ell$ conjugacy lifting).** Let $H$ be a finite group whose order is a unit in a local Artinian $\mathcal O$-algebra $A'$, and let $A'\twoheadrightarrow A$ have square-zero kernel $J$. Suppose

$$
r_1,r_2:H\longrightarrow\operatorname{GL}_d(A')
$$

have strictly equivalent reductions over $A$ and have the same residual representation. After strictly conjugating $r_2$, assume their reductions are equal. Then $r_1$ and $r_2$ are strictly equivalent over $A'$. Moreover every representation of $H$ over $A$ lifts across $A'\twoheadrightarrow A$, and any two lifts are strictly equivalent.

**Proof strategy.** A square-zero congruence kernel is additive. Consequently the difference of two lifts is a $1$-cocycle and the multiplication defect of provisional lifts is a $2$-cocycle. Both cohomology groups vanish because averaging by $|H|^{-1}$ contracts positive-degree cochains.

**Proof.** Write

$$
r_2(h)=(1+c(h))r_1(h),\qquad c(h)\in M_d(J).
$$

Since $J^2=0$, comparison at $hh'$ gives

$$
c(hh')=c(h)+h\cdot c(h'),
$$

so $c$ is a $1$-cocycle for the adjoint action of the common reduction. Put

$$
X=-\frac1{|H|}\sum_{h\in H}c(h).
$$

The cocycle identity and a permutation of the summation index give $c(h)=hX-X$. Conjugation by $1-X$ therefore carries one lift to the other.

For existence, choose arbitrary matrix lifts $\widetilde r(h)$ of the matrices $r_A(h)$. Their multiplication defect is a $2$-cocycle with values in $M_d(J)$. Averaging on the standard finite-group cochain complex makes every positive-degree cocycle a coboundary. Correcting the provisional matrices by a $1$-cochain kills the defect. The correction is strict because it lies in $M_d(J)\subseteq M_d(\mathfrak m_{A'})$. $\square$

For $H$ a finite $p$-group, $|H|$ is a unit because $p\ne\ell$. A continuous residual action of the pro-$p$ group $P_K$ factors through such an $H$. The lemma therefore proves rigidity at each small extension. It does not canonically choose a lift, and it does not say that Frobenius normalizes an arbitrarily chosen lift. Frobenius compatibility is a separate intertwining equation.

There is also a cohomological formulation. For every finite $\ell$-primary discrete module $N$ with continuous $P_K$-action,

$$
H^i(P_K,N)=0\qquad(i>0).
$$

Continuous cochains reduce to finite $p$-group quotients, where averaging applies. Inflation--restriction then identifies all deformation freedom with the quotient acting on $P_K$-invariants. Wild inertia may act nontrivially on the residual representation, but a deformation cocycle becomes cohomologically trivial when restricted to it.

### 2.5 Continuity and the two-generator presentation

The two matrices $F$ and $T$ are useful only if they really determine a continuous representation. Let

$$
G_K^{\mathrm t}=G_K/P_K.
$$

Its inertia subgroup is $I_K/P_K\simeq\widehat{\mathbf Z}^{(p')}(1)$, where

$$
\widehat{\mathbf Z}^{(p')}=\prod_{r\ne p}\mathbf Z_r.
$$

Choose a compatible topological generator $\tau$ and an arithmetic Frobenius lift $\varphi$. Then $G_K^{\mathrm t}$ is the profinite group generated by $\tau$ and $\varphi$ with relation (2.1), understood through all finite quotients. This is not a discrete two-generator presentation: continuity retains the profinite orders of both directions.

**Proposition 2.2.** Let $A$ be Artinian and suppose $F,T\in\operatorname{GL}_d(A)$ reduce to the matrices of a residual tame representation and satisfy

$$
FTF^{-1}=T^q.
$$

Then there is a unique continuous representation of $G_K^{\mathrm t}$ carrying $\varphi$ to $F$ and $\tau$ to $T$.

**Proof.** The finite ring $A$ has finite matrix group. The order of $T$ is prime to $p$: its residual order is prime to $p$, while the kernel of reduction on $\langle T\rangle$ is an $\ell$-group and $\ell\ne p$. Thus tame inertia maps continuously to $\langle T\rangle$. The matrix $F$ also has finite order. After passing to a sufficiently large finite quotient, the displayed relation makes these maps combine on the semidirect product. Uniqueness follows from density of the subgroup generated by $\varphi$ and $\tau$. $\square$

For a complete coefficient ring $R$, a compatible system of Artinian pairs $(F_n,T_n)$ over $R/\mathfrak m_R^n$ gives a continuous representation into $\operatorname{GL}_d(R)$ because inverse images of congruence subgroups are open. One should not instead give $\operatorname{GL}_d(R)$ the discrete topology; an infinite pro-$\ell$ tame image would then cease to be continuous.

If wild inertia has a fixed finite image $W$, the presentation gains finitely many matrices $R(w)$, the multiplication equations for $W$, and normalization equations

$$
FR(w)F^{-1}=R(\varphi w\varphi^{-1}),\qquad
TR(w)T^{-1}=R(\tau w\tau^{-1}).
$$

The wild rigidity lemma shows that these matrices add orbit directions but no new unframed tangent classes. This is the precise reduction from a general away-from-$\ell$ local problem to a tame matrix problem with a rigid wild background.

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

The finiteness hypothesis behind the first assertion is available here, rather than being tacit. Local Galois cohomology gives finite-dimensional $H^1(K,M)$ because $p\ne\ell$, and $B^1(K,M)$ is a quotient of the finite-dimensional space $M$. Hence $Z^1(K,M)$ is finite-dimensional. The framed representability theorem therefore applies to $G_K$; with scalar residual centralizer, its unframed version applies as well. No vanishing of $H^2(K,M)$ is being used for representability.

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

### 3.5 A relative representability test

The following criterion is the workhorse behind the conditions in later chapters.

**Proposition 3.1.** Suppose the ambient framed functor $D^\square$ is represented by $R^\square$, and suppose a rule $\mathcal D$ on framed lifts has the following properties.

1. Membership is invariant under coefficient isomorphism and is preserved by arbitrary maps in $\mathcal C_{\mathcal O}$.
2. For every pair $A'\to A\leftarrow A''$, a lift over $A'\times_AA''$ belongs to $\mathcal D$ exactly when both projections do.
3. There is a collection of matrix-valued natural functions $f_\lambda$ on the universal family such that a lift belongs to $\mathcal D$ exactly when all $f_\lambda$ vanish.

Then $\mathcal D$ is represented by $R^\square/I$, where $I$ is the closed ideal generated by all entries of the $f_\lambda$. If $R^\square$ is Noetherian, finitely many elements generate $I$, although the intrinsic definition may quantify over infinitely many group elements.

**Proof.** A map $x:R^\square\to A$ classifies an ambient lift. It factors through $R^\square/I$ precisely when every generator of $I$ maps to zero, equivalently when every $f_\lambda(x)$ vanishes. By the assumed characterization this is exactly $x\in\mathcal D(A)$. The equivalence is natural in $A$, so the quotient mapping functor is $\mathcal D$. Closure is needed because maps from a complete ring to Artinian rings see the completed quotient. $\square$

The criterion applies immediately to trivial inertia, factorization through a specified finite quotient, fixed determinant, and literal tame matrix equations. It does **not** automatically apply to statements containing the words “there exists a line” or “is conjugate to.” Those are images of enhanced functors. To use the proposition one must retain the enhancement, prove the choice unique, or replace existence by intrinsic equations whose equivalence has been proved.

Representability and smoothness should also remain separate. If $R^\square/I$ represents the condition, formal smoothness asks whether every map from it to $A$ lifts to every small extension $A'\twoheadrightarrow A$. Matrix equations answer the first question merely by existing; their derivative and higher defects answer the second. Later proofs will always identify which of these two jobs is being performed.

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

### 4.6 Characters, scalar Frobenius, and exact boundary cases

Dimension one is a useful normalization check. Let $d=1$ and let $\bar\chi$ be unramified. Every unramified lift is determined by the unit $u=\chi(\varphi)$ reducing to $\bar\chi(\varphi)$. Choosing a lift $\widetilde u\in\mathcal O^\times$ gives

$$
R^{\mathrm{ur}}_{\bar\chi}\simeq\mathcal O[[X]],
\qquad \chi^{\mathrm{univ}}(\varphi)=\widetilde u(1+X).
$$

Framing has no effect because $\operatorname{GL}_1$ is abelian. Fixing determinant in dimension one fixes the entire character, so the fixed-determinant quotient is $\mathcal O$ when the determinant is the prescribed unramified lift and is empty when it is ramified. This agrees with the formulas $d^2=1$ and $d^2-1=0$.

In dimension two with nonscalar $\bar F$, cyclicity says that trace and determinant classify strict conjugacy classes. If the determinant is not fixed, choose lifts $\widetilde t$ and $\widetilde d$ of $\operatorname{tr}\bar F$ and $\det\bar F$. Then the companion matrix

$$
\begin{pmatrix}
0&-(\widetilde d+Y)\\
1&\widetilde t+X
\end{pmatrix}
$$

is a universal unframed normal form after transporting the chosen residual cyclic basis. Fixing determinant sets $Y$ equal to the prescribed constant and leaves the single trace parameter $X$. This is the local origin of many one-variable unramified components.

At scalar Frobenius there is no analogous normal form. It is worth seeing the failure beyond the first-order counterexample. Put $\bar F=\lambda I_2$ and consider lifts over $A=k[\varepsilon]/(\varepsilon^2)$. Every lift is $\lambda I_2+\varepsilon X$. Strict conjugation by $1+\varepsilon Z$ fixes it because the commutator is divisible by $\varepsilon^2$. Thus the unframed tangent has dimension four, not the two parameters trace and determinant would suggest. The characteristic polynomial records only $\operatorname{tr}X$ at first order; the first-order determinant variation is $\lambda\operatorname{tr}X$, so even those two coefficients collapse to one linear functional at a scalar point. Nilpotent and semisimple directions remain distinct deformation classes.

This phenomenon does not contradict smoothness of the framed ring. The four matrix entries lift freely, but the orbit relation has zero differential at the scalar special fiber and becomes nontrivial at higher order. The safe conclusions are therefore exact:

- the framed unramified ring is always a $d^2$-variable power-series ring;
- its fixed-determinant quotient is always smooth of relative dimension $d^2-1$;
- the unframed unramified ring is proved here to be smooth only under cyclicity, or in dimension one;
- scalar Frobenius should be handled by a frame or by additional structure, not by characteristic-polynomial coordinates.

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

### 5.5 The fixed-type smoothness and dimension theorem

We now isolate the exact theorem implicit in the preceding construction and prove its dimension assertion without appealing to a vague orbit count.

Let

$$
C_{\mathcal O}=\operatorname{End}_{\mathcal O[H]}(\mathcal O^d),
\qquad C_k=M^{I_K}.
$$

Because $|H|$ is a unit, the averaging operator

$$
\pi(X)=\frac1{|H|}\sum_{h\in H}\theta(h)X\theta(h)^{-1}
$$

is an idempotent on $M_d(\mathcal O)$. Hence $C_{\mathcal O}$ is a direct summand of a finite free module and is itself free, since $\mathcal O$ is local. Its group of units is the open subscheme of the affine space underlying $C_{\mathcal O}$ on which the determinant is invertible; it is formally smooth of relative dimension $\dim_k C_k$.

**Theorem 5.1.** Assume the data of Section 5.1: $H$ has order prime to $\ell$, $\theta$ is an integral lift of residual inertia, and $F_0$ is an integral Frobenius intertwiner. Then the intrinsic framed fixed-$\theta$ functor is formally smooth over $\mathcal O$ of relative dimension $d^2$. If a compatible determinant $\delta$ is imposed and

$$
\operatorname{tr}:C_k\longrightarrow k
$$

is surjective, the fixed-determinant functor is formally smooth of relative dimension $d^2-1$.

**Proof strategy.** A lift of the inertial representation is a point in the strict conjugacy orbit of $\theta$. After choosing a conjugacy, every Frobenius intertwiner is $CF_0$ with $C$ in the inertia centralizer. The choice of conjugacy is redundant precisely by the centralizer. We verify lifting directly and then count the tangent variables as orbit plus centralizer.

**Proof.** Let $A'\twoheadrightarrow A$ be a small extension and let $\rho_A$ be of type $\theta$. Choose $U_A\equiv1$ that identifies its inertia with $\theta_A$. Lift $U_A$ arbitrarily to $U_{A'}$. In that provisional frame, lift the inertia action as the literal $\theta_{A'}$. By Lemma 2.1 this loses no possible object and creates no obstruction.

Write the Frobenius matrix of $\rho_A$ as $C_AF_{0,A}$ with $C_A\in(C_{\mathcal O}\otimes A)^\times$. Since the unit group of $C_{\mathcal O}$ is smooth, $C_A$ lifts to a unit $C_{A'}$. Then $C_{A'}F_{0,A'}$ intertwines the lifted inertia action. Conjugating back by $U_{A'}$ produces the required lift of $\rho_A$. Thus every small-extension problem is solvable.

At the residual point, strict conjugation moves $\theta$ through the quotient

$$
M/C_k,
$$

of dimension $d^2-\dim C_k$. With inertia fixed, the Frobenius multiplier moves through $C_k$, of dimension $\dim C_k$. The sum is $d^2$. Equivalently, the tangent cocycles whose inertial restriction is a coboundary have this dimension before quotienting by global coboundaries.

For fixed determinant, the inertial determinant is already fixed. The remaining equation is

$$
\det(CF_0)=\delta(\varphi).
$$

Its derivative in the $C$-direction is, up to multiplication by a unit, $X\mapsto\operatorname{tr}X$. Surjectivity makes the determinant fiber formally smooth of codimension one. This proves the final assertion. $\square$

If $\ell\nmid d$, scalar endomorphisms lie in $C_k$ and have traces $d a$, so the trace map is onto. If $\ell\mid d$, surjectivity may still hold because $C_k$ can contain a nonscalar invariant of nonzero trace; it must be checked rather than guessed. Failure of surjectivity does not by itself prove that the determinant fiber is singular, but it invalidates the smooth codimension-one conclusion.

The unframed tangent is obtained by quotienting the framed dimension by the actual orbit dimension

$$
d^2-h^0_K(M).
$$

It therefore has dimension $h^0_K(M)$, in agreement with (5.3). This numerical subtraction is a tangent statement. An unframed universal ring still requires the scalar-centralizer hypothesis or another exact descent theorem.

### 5.6 Two finite-type calculations

**A pair of distinct inertial characters.** Suppose $d=2$ and

$$
\theta=\eta_1\oplus\eta_2,
\qquad \eta_1\ne\eta_2,
$$

where the characters have finite order prime to $\ell$. If Frobenius preserves both characters, then

$$
C_k=ke_{11}\oplus ke_{22}.
$$

The framed fixed-type ring is smooth of dimension four. Its two inertia-orbit directions are the off-diagonal changes of basis; its two Frobenius directions vary the diagonal entries. Fixing determinant removes the sum of the diagonal Frobenius directions and gives dimension three. The unframed tangent has dimension two if Frobenius acts trivially on this centralizer, and can be smaller only when Frobenius permutes or otherwise acts nontrivially on its summands; the exact answer is the cokernel in (5.3).

If Frobenius interchanges the two characters, then $q$ carries $\eta_1$ to $\eta_2$ on tame inertia and conversely. The inertia centralizer is still diagonal, but Frobenius swaps its two basis idempotents. Hence

$$
h^0_K(M)=1,
$$

and the unframed fixed-type tangent has dimension one. The framed dimension remains four: the loss of an unframed Frobenius direction is exactly compensated by an additional coboundary direction.

**An irreducible finite inertial type.** Suppose $\theta_k$ is absolutely irreducible as a $k[H]$-module. Then $C_k=k$. Every Frobenius intertwiner is a scalar multiple of $F_0$ after rigidifying inertia. The framed ring is again smooth of dimension $d^2$, while the unframed tangent has dimension one. If $\ell\nmid d$ and determinant is fixed, the scalar multiplier is infinitesimally determined, so the unframed fixed-determinant tangent is zero and the framed fixed-determinant ring has dimension $d^2-1$.

These examples show why the uniform framed dimension does not mean all fixed-type problems have the same quotient geometry. The inertia orbit and the Frobenius centralizer trade dimensions, while the residual global centralizer controls what survives after strict conjugacy.

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

### 6.5 The small-extension defect of the tame relation

The cokernel in (6.7) is not merely suggested by the number of equations. It receives a canonical lifting defect.

Let $A'\twoheadrightarrow A$ be a small extension with kernel $J$, and let $(F_A,T_A)$ satisfy (6.1). Choose arbitrary invertible lifts $\widetilde F,\widetilde T$ to $A'$. The matrix

$$
\widetilde F\widetilde T\widetilde F^{-1}\widetilde T^{-q}
$$

reduces to $1$, so it has the form $1+E$ with $E\in M\otimes_kJ$, after using the residual representation to identify the square-zero congruence kernel. Replacing the provisional lifts by

$$
((1+X)\widetilde F,(1+Y)\widetilde T),
\qquad X,Y\in M\otimes_kJ,
$$

changes $E$ by $d^1(X,Y)$. Consequently the class

$$
[E]\in\operatorname{coker}(d^1)\otimes_kJ \tag{6.8}
$$

is independent of provisional lifts.

It vanishes if and only if the pair lifts. Necessity is immediate from a genuine lifted relation. If the class vanishes, choose $X,Y$ with $d^1(X,Y)=-E$; the corrected pair has zero defect because products of two $J$-valued matrices vanish. This proves that (6.7) is a complete obstruction space for the single tame relation.

The same calculation proves the smoothness criterion of Section 6.3. If $d^1$ is onto at the residual point, it remains onto after every Artinian thickening: a maximal minor that is nonzero over $k$ is a unit. The defect can therefore be corrected at every small extension. Conversely, if $d^1$ is not onto, (6.8) identifies the possible obstruction directions, but not every direction need occur from a given deformation. Failure of the Jacobian criterion is a warning, not a proof that all lifts are obstructed.

Strict conjugation changes $(X,Y)$ by $d^0(Z)$ and leaves the defect unchanged because $d^1d^0=0$. Thus the full complex (6.6) has its expected deformation-theoretic meanings:

$$
H^0=\text{infinitesimal stabilizers},\qquad
H^1=\text{unframed tangent classes},\qquad
H^2=\text{relation obstructions}.
$$

This description is exact for the tame quotient with trivial wild action. If a fixed wild action is present, its normalization equations contribute additional terms to degrees one and two. Averaging makes the pure wild part acyclic, but the Frobenius and tame normalizer constraints must still be included before claiming a smoothness result.

### 6.6 Exact dimensions at trivial residual inertia

Assume $\bar T=1$ and write

$$
c_F=\dim_k\operatorname{Cent}_M(\bar F),
\qquad
s_F=\dim_k\ker(\operatorname{Ad}_{\bar F}-q).
$$

Formula (6.4) gives

$$
\dim_k\ker d^1=d^2+s_F. \tag{6.9}
$$

The image of $d^0$ has dimension $d^2-c_F$, because the $T$-component of $d^0$ is zero and the kernel of $Z\mapsto Z-\operatorname{Ad}_{\bar F}Z$ is the Frobenius centralizer. Therefore

$$
\boxed{\dim_kH^1(C^\bullet_{\mathrm{tame}})=c_F+s_F.} \tag{6.10}
$$

The obstruction space has dimension

$$
\dim_kH^2(C^\bullet_{\mathrm{tame}})=s_F, \tag{6.11}
$$

because kernel and cokernel of the endomorphism $\operatorname{Ad}_{\bar F}-q$ have equal dimension. Equations (6.10)--(6.11) are the matrix-presentation version of the away-from-$p$ Euler formula: the centralizer supplies unramified tangent classes, while the $q$-eigenspace supplies both tame tangent and dual obstruction directions.

**Theorem 6.1 (generic tame smoothness).** If $q$ is not an eigenvalue of $\operatorname{Ad}_{\bar F}$, the framed tame deformation functor killing wild inertia is formally smooth of relative dimension $d^2$. If in addition a compatible unramified determinant is fixed, the fixed-determinant tame functor is formally smooth of relative dimension $d^2-1$.

**Proof.** The eigenvalue hypothesis says $s_F=0$, so $d^1$ is onto and Section 6.5 gives formal smoothness. Equation (6.9) gives framed tangent dimension $d^2$. Since scalar matrices are always $1$-eigenvectors of $\operatorname{Ad}_{\bar F}$, the hypothesis forces $q\ne1$ in $k$. The relation then forces $\operatorname{tr}Y=0$, because taking trace in $(\operatorname{Ad}_{\bar F}-q)Y=0$ gives $(1-q)\operatorname{tr}Y=0$. Fixing determinant adds the independent equation $\operatorname{tr}X=0$, lowering the dimension by one. More explicitly, the combined derivative consisting of the tame defect and the determinant of $F$ is onto: solve the tame defect uniquely in the $Y$-variable, then choose the otherwise free $X$ with any prescribed trace. The determinant of $T$ is automatically $1$ near the residual point, since the tame relation gives $(\det T)^{q-1}=1$ and $q-1$ is a unit. The small-extension correction argument therefore works with determinant fixed. $\square$

For $d=2$ with $\bar F=\operatorname{diag}(\alpha,\beta)$, the adjoint eigenvalues are

$$
1,\quad1,\quad\alpha\beta^{-1},\quad\beta\alpha^{-1}.
$$

Hence Theorem 6.1 applies exactly when

$$
q\notin\{1,\alpha\beta^{-1},\beta\alpha^{-1}\}.
$$

At either special ratio, $s_F\ge1$ and the full tame functor gains a ramified tangent direction. At $q=1$, it gains at least the two diagonal tame directions. These are precisely the loci on which a more refined component condition, rather than the unrestricted tame equation, is needed.

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

### 7.5 The liftability theorem for nonzero residual monodromy

Case N admits a sharper theorem under the generic hypotheses used most often. Twist away the fixed prime-to-$\ell$ scalar character. Assume $d=2$, $\ell\ne2$, $q\not\equiv1\pmod\ell$, and choose a basis in which

$$
\bar N=e_{12},\qquad
\bar F=
\begin{pmatrix}q\bar a&\bar b\\0&\bar a\end{pmatrix}.
$$

The scalar $\bar a$ is nonzero. The relation with $\bar N$ forces precisely this upper-triangular shape.

**Theorem 7.1 (minimal nonzero-monodromy condition).** Under these hypotheses, the intrinsic framed condition preserving one nonzero rank-one tame block is formally smooth of relative dimension four when its unramified scalar character is allowed to vary. If a compatible determinant is fixed, it is formally smooth of relative dimension three. The residual centralizer of the pair $(\bar F,\bar N)$ is scalar, so the corresponding unframed functors are represented; they are formally smooth of dimensions one and zero, respectively.

**Proof strategy.** Nonzero residual monodromy forces every lifted $N$ to remain a rank-one nilpotent. Such matrices form one smooth strict-conjugacy orbit near $e_{12}$. After normalizing $N$, the Frobenius equation has an elementary upper-triangular solution set. We count the orbit and the normalizer fiber, then impose determinant.

**Proof.** Let $A$ be Artinian and let $N_A^2=0$ reduce to $e_{12}$. The image of $N_A$ is generated by a vector reducing to $e_1$, and the kernel is a direct summand of rank one containing that image. Nakayama's lemma makes them equal. Choose $v_1$ generating this line and choose $v_2$ with $N_Av_2=v_1$. The resulting basis reduces to the chosen residual basis after multiplying by a strict matrix, and in it $N_A=e_{12}$.

Now solve

$$
F e_{12}F^{-1}=q e_{12}.
$$

A direct multiplication shows that every solution is uniquely of the form

$$
F=
\begin{pmatrix}qa&b\\0&a\end{pmatrix},
\qquad a\in A^\times,\quad b\in A. \tag{7.3}
$$

Both $a$ and $b$ lift freely across a small extension. The conjugacy orbit of $e_{12}$ has relative dimension

$$
4-\dim\operatorname{Cent}(e_{12})=4-2=2.
$$

For fixed $N$, formula (7.3) supplies two more parameters, so the intrinsic framed condition is smooth of dimension four.

Its determinant is $qa^2$. Because $2qa$ is a unit, the equation $qa^2=\delta(\varphi)$ determines the chosen lift of $a$ smoothly and cuts one dimension. The tame determinant is already one, and the fixed scalar twist supplies the prescribed inertial determinant. This gives framed dimension three.

Finally, a matrix commuting with $e_{12}$ has the form $xI+ye_{12}$. Commuting also with $\bar F$ forces $(q-1)y=0$, hence $y=0$. The residual centralizer is therefore scalar. Forgetting the frame is formally smooth of relative dimension $4-1=3$. Subtracting these orbit directions gives unframed dimensions one and zero, and the scalar-centralizer theorem supplies universal rings. $\square$

The theorem explains a common minimality phenomenon. With determinant fixed, an already ramified nonzero special residual representation has no unframed infinitesimal freedom at all, even though its framed ring has three variables. Those variables only move the frame. Without fixed determinant, the remaining unframed parameter is the unramified scalar character $a$.

Each hypothesis has a visible role. Nonzero $\bar N$ makes the rank-one condition closed near the residual point. The condition $q\ne1$ reduces the centralizer to scalars. The condition $\ell\ne2$ makes the determinant equation transverse. If any fails, the defining equations remain valid, but the smooth dimensions in Theorem 7.1 are no longer asserted.

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

Arithmetic Frobenius acts on this coefficient line by $q$, so it has no invariants because $q\ne1$. On the other hand, the explicit top-degree formula for an inertia-trivial module gives

$$
H^2\bigl(K,k(\bar\chi_\ell)\bigr)
\simeq k(\bar\chi_\ell)(-1)/(\varphi-1)=k.
$$

The local Euler formula therefore gives

$$
\dim_kH^1\bigl(K,k(\bar\chi_\ell)\bigr)=1. \tag{8.6}
$$

The unique direction is the tame monodromy direction; there is no unramified extension direction because $\varphi-1$ is invertible on the coefficient line. If $\psi$ is allowed to vary unramified, one further scalar direction appears. If the determinant is fixed and $\ell\ne2$, the equation $\delta=\psi^2\chi_\ell$ removes that scalar direction, leaving the one-dimensional special tangent. When $q=1$ or $\ell=2$, this count must be replaced by the trace-kernel and relation calculation because diagonal characters or the squaring map cease to be transverse.

For residual nonzero monodromy, the tangent condition also requires preservation of the rank-one nilpotent orbit. In an adapted frame the allowed $Y$ is tangent to that orbit plus scaling of $N$, and (8.5) couples it to $X=c(\varphi)$. The exact dimension is the kernel dimension of the derivative of (8.5), minus the permitted change-of-basis directions in the unframed problem. It should be computed from those equations in exceptional characteristics rather than imported from a generic formula.

### 8.5 The generic special component in coordinates

We now prove a smoothness theorem when residual monodromy is zero but the special orientation is visible in Frobenius. Assume

$$
\ell\ne2,\qquad q\not\equiv1\pmod\ell,
$$

and, after the fixed common twist, assume

$$
\bar\rho(\varphi)=
\begin{pmatrix}q\bar a&0\\0&\bar a\end{pmatrix},
\qquad \bar\rho(I_K)=1.
$$

Fix unramified characters $\psi\chi_\ell$ and $\psi$ lifting the two diagonal characters. The fixed standard line normal form is

$$
T=
\begin{pmatrix}1&t\\0&1\end{pmatrix},\qquad
F=
\begin{pmatrix}q a&b\\0&a\end{pmatrix}, \tag{8.7}
$$

where $a=\psi(\varphi)$ is fixed and $b,t\in\mathfrak m_A$. Every such pair satisfies the tame relation. Conversely, every special-shaped pair in a basis adapted to the distinguished line has this form.

Thus the normal-form functor with the line identified with the standard summand is represented by

$$
\mathcal O[[B,T]], \tag{8.8}
$$

and is formally smooth of dimension two. The parameter $T$ is monodromy; $B$ is the unramified upper extension entry. Since $q-1$ is a unit, strict upper-unipotent conjugation changes $b$ by an arbitrary element while leaving the first-order monodromy parameter unchanged. Consequently only the $t$-direction survives in the unframed tangent space, agreeing with (8.6).

**Theorem 8.1 (generic closed special condition).** Under the displayed hypotheses and with the two diagonal characters fixed, the line-enhanced framed special condition is closedly represented and formally smooth of relative dimension three. Its tangent space consists of the one special extension class together with the two change-of-frame directions of the residual split representation. If an unramified character $\psi$ is allowed to vary, the dimension is four. If instead a compatible determinant is fixed, the fixed branch of $\psi$ is unique and the dimension remains three.

**Proof.** The residual Frobenius eigenvalues are distinct, so the line on which Frobenius acts by $q\bar a$ is unique and lifts uniquely as a direct summand. A framed representation determines that line, while moving it inside the fixed ambient frame contributes one smooth parameter. After choosing a generator of the line and a complementary vector, the matrices take the form (8.7). Changing the complementary vector is the upper-unipotent frame direction recorded by $b$; changing the line is the lower change-of-frame direction; and $t$ is the genuine extension direction. These three parameters lift independently. Equivalently, the unframed special tangent has dimension one and the residual centralizer has dimension two, so adding

$$
\dim B^1=4-2=2
$$

framing directions gives dimension three. The explicit normal form proves actual lifting, not merely the tangent count.

Allowing $\psi$ to vary adds its one smooth unramified parameter. If determinant is fixed, (8.4) becomes $\psi^2=\delta\chi_\ell^{-1}$. On the chosen residual branch, the derivative of squaring is multiplication by $2\bar\psi$, a unit, so there is a unique lift of $\psi$ at every Artinian level. $\square$

The theorem concerns the **closed** special-shaped component, including $t=0$. Its genuine special generic locus is $t\ne0$, an open sublocus. Smoothness of the closed component does not turn that open condition into an Artinian deformation subfunctor.

There is deliberately no assertion here that the ordinary unframed set of special representations is represented. The residual split representation has a two-dimensional diagonal centralizer, so the general scalar-centralizer theorem does not apply. The enhanced or framed ring is the correct universal local object unless some additional rigidification is retained.

### 8.6 Exceptional special points

The hypotheses of Theorem 8.1 isolate two independent degeneracies.

If $q\equiv1\pmod\ell$, the two residual diagonal characters coincide. The line is no longer recoverable from Frobenius, diagonal tame characters can appear, and the squaring relation for a fixed determinant may be inseparable when $\ell=2$. Even the tangent space changes: for the trivial coefficient line, $H^1(K,k)$ has both unramified and tame directions when $q=1$ in $k$. A one-dimensional “special tangent” statement is therefore false at such a point.

If $\ell=2$ but $q\ne1$ in $k$ cannot occur, because every odd integer reduces to $1$ in characteristic two. Thus all away-from-two special residual points lie in the coincident-character case. The line-enhanced equations still define a framed quotient, and nonzero residual monodromy can still recover a unique kernel line, but the generic dimension-three fixed-determinant theorem does not apply. One must use the full derivative of (8.5), the trace-kernel formulation, and the actual automorphism group.

There is a third exceptional situation even when $q\ne1$: the residual representation may already be a nonsplit unramified extension with the special diagonal characters. Its Frobenius matrix is upper triangular with nonzero upper entry. Because $q-1$ is a unit, a strict upper-unipotent conjugation removes that entry, so it is strictly equivalent to the split residual normal form. This reduction is harmless and explains why Theorem 8.1 chose a diagonal residual matrix. When $q=1$, the same conjugation cannot remove the extension entry, and separate residual extension classes lead to genuinely different local geometries.

These cases are not defects in the theory. They are the precise places where eigenlines collide, determinant ceases to be transverse, or stabilizers grow. Framing and enhancement retain a representable problem; only the uniform smoothness and dimension formulas must be withheld.

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

First, fixing determinant does not remove scalar infinitesimal changes. Second, the unframed tangent cannot be obtained by subtracting one from a dimension formula unless surjectivity of the trace map on the relevant $H^1$ has separately been proved. Third, the linear dual of $M^0$ under the trace pairing is naturally the quotient $M/kI$, not automatically $M^0$ itself.

The framed determinant equation remains smooth even in characteristic two. The problem lies in decomposing conjugation directions and dual modules, not in differentiating determinant on $\operatorname{GL}_2$. For this reason framed fixed-determinant rings are often the cleanest local objects at $\ell=2$, even though the residue characteristic $p$ of $K$ is different from two.

### 9.4 Determinant fibers inside constrained problems

The smoothness of determinant on the full general linear group is elementary but should be distinguished from its restriction to a local condition. If $F\in\operatorname{GL}_d(A)$ and $A'\twoheadrightarrow A$ has square-zero kernel $J$, choose any lift $\widetilde F$. Replacing it by $(1+X)\widetilde F$ changes its determinant by

$$
\det(1+X)=1+\operatorname{tr}X,
\qquad X\in M_d(J).
$$

Since $X=j e_{11}$ realizes any $j\in J$, every prescribed determinant lift can be attained. This proves that

$$
\det:\operatorname{GL}_d\longrightarrow\mathbf G_m
$$

is formally smooth in every characteristic.

Now let $\mathcal D$ be a formally smooth framed local condition with tangent subspace

$$
Z^1_{\mathcal D}(K,M)\subseteq Z^1(K,M).
$$

The determinant-fixed fiber is formally smooth of codimension one if the derivative

$$
Z^1_{\mathcal D}(K,M)\longrightarrow Z^1(K,k),
\qquad c\longmapsto\operatorname{tr}c,
$$

is onto the determinant variations allowed in the ambient determinant family and if this surjectivity persists at every Artinian point. For conditions described by a smooth group torsor, such as fixed finite type, persistence follows from a unit minor in the trace map on the relevant centralizer. For the generic tame problem it follows from the combined derivative calculated in Theorem 6.1. For the generic special problem it is the transversality of the squaring map on $\psi$.

This yields a practical determinant test.

1. Determine which parameter actually changes determinant inside the constrained normal form.
2. Differentiate determinant with respect to that parameter.
3. Check that the derivative is a unit at the residual point.
4. Only then subtract one from the smooth dimension.

The test explains the different exceptional hypotheses encountered earlier. In fixed type, the derivative is trace on the inertia centralizer. In a two-dimensional special family, it is multiplication by $2\bar\psi$. In an unramified framed family, all matrix directions are available, so $e_{11}$ always works. The phrase “determinant cuts one equation” is therefore true scheme-theoretically but does not by itself say that the equation cuts transversely.

## 10. Obstructions, dimensions, and exceptional loci

### 10.1 Ambient obstruction spaces

For the unrestricted local deformation problem, small-extension obstructions lie in

$$
H^2(K,M).
$$

For away-from-$p$ coefficients, the two-step tame-inertia calculation identifies its dimension with a twisted invariant space. More precisely, the top-degree lemma proved in Section 10.2 gives

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

### 10.2 Euler characteristic and the top-degree calculation

We first justify the top-degree equality used above without invoking a general duality theorem.

**Lemma 10.1 (elementary top-degree formula).** For every finite-dimensional $k[G_K]$-module $N$ with $p\ne\ell$,

$$
\dim_kH^2(K,N)=\dim_kH^0(K,N^*(1)).
$$

**Proof strategy.** The Hochschild--Serre calculation expresses degree two as Frobenius coinvariants of $H^1(I_K,N)$. The one pro-$\ell$ tame direction identifies the linear dual of this inertia cohomology with inertial invariants of $N^*(1)$. Dualizing Frobenius coinvariants then gives Frobenius invariants.

**Proof.** Let $J$ be the kernel of the projection from inertia onto its pro-$\ell$ tame quotient

$$
I_K\longrightarrow\mathbf Z_\ell(1).
$$

Every finite quotient of $J$ through which the action on $N$ factors has order prime to $\ell$: its wild part is a $p$-group, and its remaining tame factors have prime-to-$\ell$ order. Averaging therefore gives

$$
H^b(J,N)=0\qquad(b>0)
$$

and makes $N^J$ a direct summand. Put $W=N^J$. Hochschild--Serre for $J\triangleleft I_K$ reduces inertia cohomology to the procyclic group $\Gamma=I_K/J\simeq\mathbf Z_\ell(1)$. If $\tau$ is its chosen generator, the continuous cochain complex of $\Gamma$ in degrees zero and one is

$$
W\xrightarrow{\tau-1}W.
$$

Consequently

$$
H^1(I_K,N)\simeq W/(\tau-1)W.
$$

Because taking $J$-invariants is split by averaging, restriction of functionals identifies $(N^*)^J$ with $W^*$. The linear dual of $W/(\tau-1)W$ is the kernel of $\tau^{-1}-1$ on $W^*$, hence is $(N^*)^{I_K}$. Since the cyclotomic character is unramified at $p\ne\ell$, this is also $H^0(I_K,N^*(1))$. Evaluation on a compatible tame generator therefore gives a perfect pairing

$$
H^1(I_K,N)\times H^0(I_K,N^*(1))\longrightarrow k. \tag{10.3}
$$

We must still verify the twist and not merely guess it from dimensions. For a cocycle $c$ representing a class in $H^1(I_K,N)$, the conjugation action is

$$
(\varphi c)(\sigma)=\varphi\,c(\varphi^{-1}\sigma\varphi).
$$

Modulo $(\tau-1)W$, a procyclic cocycle satisfies $c(\tau^a)=a\,c(\tau)$ for $a\in\mathbf Z_\ell$. Since $\varphi^{-1}\tau\varphi=\tau^{q^{-1}}$, Frobenius acts on the coinvariant class of $c(\tau)$ as

$$
[w]\longmapsto[q^{-1}\varphi w].
$$

The contragredient action on its linear dual is therefore $q$ times the usual action on $N^*$. This is exactly the Frobenius action on $N^*(1)$ because $\bar\chi_\ell(\varphi)=q$. Thus (10.3) is Frobenius-equivariant, including its normalization.

Finally, both $I_K$ and the residue quotient have $\ell$-cohomological dimension one in the modules under consideration. The two-row Hochschild--Serre calculation and $G_K/I_K\simeq\widehat{\mathbf Z}$ therefore give

$$
H^2(K,N)\simeq
H^1\bigl(G_K/I_K,H^1(I_K,N)\bigr)
\simeq \frac{H^1(I_K,N)}{(\varphi-1)H^1(I_K,N)}.
$$

The dual of the final cokernel is the $\varphi$-fixed subspace of $H^1(I_K,N)^*$. By (10.3), that subspace is

$$
H^0(I_K,N^*(1))^{\varphi=1}=H^0(K,N^*(1)).
$$

Taking dimensions proves the lemma. $\square$

Because $p\ne\ell$, the local Euler characteristic has no field-degree term. Combining it with the lemma gives

$$
h^1_K(N)=h^0_K(N)+h^2_K(N)
=h^0_K(N)+h^0_K(N^*(1)). \tag{10.4}
$$

Applied to $M$, this gives

$$
h^1_K(M)=h^0_K(M)+h^0_K(M(1)). \tag{10.5}
$$

The framed ambient tangent dimension is

$$
\dim_k Z^1(K,M)
=h^1_K(M)+d^2-h^0_K(M)
=d^2+h^0_K(M(1)). \tag{10.6}
$$

Thus the centralizer cancels in the framed dimension, while the twisted centralizer remains as the obstruction contribution.

For unramified or fixed-type conditions,

$$
\dim_kL_{\mathrm{ur}}=\dim_kL_\theta=h^0_K(M). \tag{10.7}
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

### 10.3 Unramified classes and relation obstructions

The same two-row calculation separates the unramified and tame parts of degree one. Inflation--restriction gives an exact sequence

$$
0\longrightarrow H^1_{\mathrm{ur}}(K,N)
\longrightarrow H^1(K,N)
\longrightarrow H^1(I_K,N)^{\varphi=1}
\longrightarrow0. \tag{10.8}
$$

The first term is

$$
N^{I_K}/(\varphi-1)N^{I_K},
$$

and therefore has dimension $h^0_K(N)$. The last term measures tame extension classes. Its dimension equals $h^2_K(N)$ by the Euler formula, although the two spaces have different variance: one is a Frobenius kernel and the other a Frobenius cokernel.

For $N=M$ and trivial residual inertia, this exact sequence is reproduced by the tame matrix complex. The unramified quotient is the free $X$-direction modulo Frobenius coboundaries. The tame term is the $q$-eigenspace of $\operatorname{Ad}_{\bar F}$ in the $Y$-direction. The relation obstruction is the cokernel of the same endomorphism. Thus

$$
\dim(\text{tame tangent quotient})
=\dim(\text{relation obstruction}),
$$

but there is no assertion that an arbitrary tangent subspace determines a deformation condition, or that every obstruction vector is realized. The equality comes from finite-dimensional kernel--cokernel balance.

This is all the degree-one comparison needed in the present book. Perfect pairings and global annihilator formulas require additional duality theory and are not used as proof inputs here.

### 10.4 Why smoothness can jump

There are three distinct sources of singularity.

1. **Top-degree twisted invariants:** $H^0(K,M(1))\ne0$ supplies possible $H^2$ obstructions.
2. **Relation degeneracy:** the derivative $d^1$ of the tame equation can fail to be surjective, especially when Frobenius eigenvalue ratios equal $q$.
3. **Orbit degeneracy:** a scalar residual matrix has a large centralizer, so an unframed coarse quotient can fail gluing even if every framed lift exists.

These phenomena can coincide but should not be conflated. For example, at trivial residual inertia with distinct Frobenius eigenvalues in special ratio $q$, the tame relation gains an upper-right direction because the same character line contributes a twisted invariant. At scalar Frobenius with $q\not\equiv1$, no tame tangent exists, yet the unframed conjugacy problem still has a large stabilizer. Smoothness is a statement about lifting in a specified functor, not a property of the residual representation in isolation.

### 10.5 Trace-zero dual coefficients

The trace pairing

$$
M\times M\longrightarrow k,
\qquad (X,Y)\longmapsto\operatorname{tr}(XY),
$$

is perfect in every characteristic and identifies $M^*$ with $M$ as a $G_K$-module. Its restriction to $M^0$ behaves differently. The annihilator of $M^0$ inside $M$ consists exactly of scalar matrices: off-diagonal test matrices kill the opposite off-diagonal entries, and diagonal trace-zero tests force all diagonal entries to agree. Hence

$$
(M^0)^*\simeq M/kI. \tag{10.9}
$$

If $\ell\nmid d$, the trace-zero projection identifies $M/kI$ with $M^0$, recovering the familiar self-duality. If $\ell\mid d$, the scalar line lies inside $M^0$ and the two modules have different submodule structures even though they have the same dimension.

Applying Lemma 10.1 to $M^0$ gives the numerical identity

$$
\dim_kH^2(K,M^0)
=\dim_kH^0\bigl(K,(M/kI)(1)\bigr). \tag{10.10}
$$

The right side is not automatically $h^0_K(M^0(1))$. This identity concerns the framed determinant-preserving obstruction coefficient. The ordinary unframed fixed-determinant tangent is the quotient

$$
Z^1(K,M^0)/dM,
$$

so even its tangent calculation must remember that the coboundaries come from all of $M$, not just $M^0$. One should use the actual trace-kernel quotient rather than replace it by $H^1(K,M^0)$.

This is more than a characteristic-two technicality. Replacing $M/kI$ by $M^0$ when no splitting exists can change the invariant subspace and therefore the predicted obstruction dimension.

### 10.6 Three obstruction calculations

The general formulas become clearer in three residual examples.

**Trivial two-dimensional representation with $q\ne1$.** Here $M$ is a four-dimensional trivial module. Thus

$$
h^0_K(M)=4,\qquad h^0_K(M(1))=0,\qquad h^1_K(M)=4.
$$

Every first-order class is unramified. The ambient $H^2$ vanishes, so both the unrestricted framed problem and the full tame framed problem are formally smooth of dimension four. The latter assertion also follows from Theorem 6.1 because $q$ is not an eigenvalue of the identity action $\operatorname{Ad}_{\bar F}$.

**A special eigenvalue ratio.** Let

$$
\bar F=\operatorname{diag}(q\bar a,\bar a),
\qquad q\ne1.
$$

On $ke_{12}$, $\operatorname{Ad}_{\bar F}$ has eigenvalue $q$. This line contributes one tame tangent direction and one dimension to the relation obstruction space (6.11). The full tame scheme can therefore be singular or have excess dimension at this point. Nevertheless Theorem 8.1 cuts out a smooth three-dimensional framed special component by retaining the eigenline and the diagonal characters. A constrained component can be smooth at a point where the ambient tame equation has a nonzero obstruction space.

**Scalar Frobenius with $q=1$ in $k$.** Again take trivial residual inertia in dimension two. Now every element of $M$ is both a $1$-eigenvector and a $q$-eigenvector. Thus

$$
c_F=4,\qquad s_F=4,
$$

and the full tame complex has

$$
\dim H^1=8,\qquad \dim H^2=4.
$$

The four unramified and four tame tangent directions coexist. At the same time the residual centralizer is all of $M_2(k)$. Relation degeneracy and orbit degeneracy are both maximal. No dimension theorem from the generic rows may be specialized to this point.

These calculations illustrate the correct use of $H^2$. Its vanishing proves ambient liftability because the general obstruction theory is complete. Its nonvanishing merely identifies possible failures. An explicitly solved constrained normal form can still lift smoothly because its obstruction map into the ambient group is identically zero.

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

### 11.4 Twists and higher ramification data

A fixed prime-to-$\ell$ scalar twist changes the numerical conductor in a controlled but not always trivial way. Let $\eta$ be a finite-order character of $G_K$ and let $V$ have finite inertial image. The inertia invariants of $V\otimes\eta$ are the $\eta^{-1}$-isotypic vectors of $V|_{I_K}$, not generally the same as $V^{I_K}$. Thus twisting preserves **variation** of the conductor inside a fixed-type family, because the entire twisted type remains fixed, but it need not preserve the numerical value of the conductor.

For the minimal cases this distinction causes no ambiguity. If one first twists the residual representation by a chosen rigid lift $\eta^{-1}$, applies Case U, F, or N, and then twists back, the final inertial representation is fixed by construction. Every higher ramification subgroup has a constant invariant direct summand in Case F. In Case N the scalar twist is fixed and the only moving non-scalar part is the rank-one tame operator, so wild breaks remain those of the scalar type and the additional tame codimension is constant.

**Proposition 11.1.** In a fixed finite-type family with quotient $H$ of order prime to $\ell$, the following data are constant after passage to any characteristic-zero coefficient field:

- the dimensions of invariants under every upper or lower ramification subgroup whose image lies in $H$;
- the multiset of breaks of the representation;
- the Swan conductor;
- the Artin conductor.

**Proof.** Every relevant ramification subgroup has finite image $H_u\le H$. The averaging idempotent for $H_u$ gives a direct-summand invariant module commuting with scalar extension. Its rank is therefore constant. Break multiplicities are differences of these ranks, and both conductor formulas are weighted sums of the same differences. $\square$

The proposition is stronger than constancy of the total conductor and is exactly what “no new ramification” means for a finite inertial type. By contrast, the closed special family with parameter $x$ has a jump already at the tame level: $\ker(xe_{12})$ has rank one where $x$ is invertible and rank two at $x=0$. No higher-ramification formalism can repair that failure of constant rank.

One must also distinguish the conductor of a representation from that of its adjoint. Even if a two-dimensional type is fixed, $\operatorname{ad}\theta$ may have more inertia invariants than $\theta$, and special ratios can create adjoint cyclotomic invariants. The deformation tangent and obstruction formulas use the adjoint representation; minimality of $\rho$ does not imply that $H^0(K,\operatorname{ad}\bar\rho(1))$ vanishes.

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

### 12.4 What changes under ramified base change

Ramified extensions behave differently enough that no blanket invariance statement is appropriate. Let $K'/K$ be finite with ramification index $e$ and residue degree $f$. On tame inertia, after compatible choices and up to a wild factor,

$$
\tau_{K'}\longmapsto\tau_K^e. \tag{12.2}
$$

Arithmetic Frobenius maps to an element of the coset $\varphi_K^fI_K$. The inertial correction in that coset depends on choices, but the relation over $K'$ is intrinsically

$$
\varphi_{K'}\tau_{K'}\varphi_{K'}^{-1}
=\tau_{K'}^{q^f}.
$$

Restriction of an unramified representation is still unramified. Restriction of a fixed finite type is the restricted type; its image can become smaller, so its centralizer and tangent dimension can increase. If $K'$ kills the entire finite inertial quotient, the restricted type becomes unramified even though the original representation was ramified.

For square-zero tame monodromy,

$$
(1+N)^e=1+eN.
$$

Thus restriction sends $N$ to $eN$. If $e$ is a unit in the coefficient ring, nonzero rank-one monodromy remains nonzero and the special condition retains its shape. If $\ell\mid e$, the residual restricted monodromy can vanish even when the original residual monodromy was nonzero. This is a second mechanism, besides reduction of a characteristic-zero parameter, by which a special representation can become residually unramified.

Conductors under ramified base change require the Herbrand reindexing of ramification groups. It is false that the Artin or Swan conductor is always unchanged. The safe conclusions needed here are narrower: a fixed finite type restricts to a fixed finite type, and a rank-one tame block remains rank one when $e$ is invertible. Any numerical conductor transformation beyond these statements must be calculated from the ramification filtration of $K'/K$.

Corestriction does not define an inverse operation on representations. Even on tangent cohomology, restriction followed by corestriction is multiplication by $[K':K]$, which may vanish in $k$. Therefore field base change can merge components, enlarge centralizers, or kill tangent classes. Local conditions are functorial under restriction, but their smooth dimensions need not be invariant.

## 13. A menu for global deformation problems

### 13.1 Representable conditions and tangent spaces

The following table records only conclusions proved under explicit hypotheses. Here $M=\operatorname{ad}\bar\rho$, $c=h^0_K(M)$, and “framed dimension” means relative tangent dimension over the coefficient base.

| Condition                    | Residual hypothesis                                                | Safe represented object                        | Unframed tangent                                   | Smoothness statement                                                                                                     |
| ---------------------------- | ------------------------------------------------------------------ | ---------------------------------------------- | -------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| Unramified                   | $\bar\rho(I_K)=1$                                                  | framed quotient                                | $H^1_{\mathrm{ur}}(K,M)$, dimension $c$            | framed smooth of dimension $d^2$                                                                                         |
| Unramified, fixed $\delta$   | above and $\delta                                                  | _I=1$                                          | framed quotient                                    | kernel of trace on $H^1_{\mathrm{ur}}$                                                                                   |
| Unramified, cyclic Frobenius | $\bar F$ cyclic                                                    | unframed ring                                  | dimension $d$                                      | smooth of dimension $d$                                                                                                  |
| Same, fixed determinant      | cyclic $\bar F$                                                    | unframed ring                                  | dimension $d-1$                                    | smooth of dimension $d-1$                                                                                                |
| Fixed finite type $\theta$   | $                                                                  | H                                              | $ prime to $\ell$ and compatible integral $\theta$ | framed quotient; unframed with descent                                                                                   |
| Full tame                    | wild action killed                                                 | framed matrix quotient                         | $H^1(C^\bullet_{\mathrm{tame}})$                   | smooth if $d^1$ is surjective                                                                                            |
| Minimal unipotent            | nonzero residual rank-one $\bar N$, fixed scalar type              | framed quotient; unframed under scalar descent | derivative kernel modulo conjugacy                 | if $d=2$, $\ell\ne2$, and $q\ne1$: framed dimensions $4$, or $3$ with fixed determinant; unframed dimensions $1$, or $0$ |
| Closed special               | trivial residual inertia, ratio $q\ne1$, fixed diagonal characters | line-enhanced framed quotient                  | special extension line, dimension $1$              | framed smooth of dimension $3$; variable $\psi$ adds one; includes the $N=0$ locus                                       |

For every row, fixed determinant means intersection with the kernel of the determinant derivative. When $\ell\nmid d$, one may replace $M$ by $M^0$ in the standard cohomological formulas. When $\ell\mid d$, use the trace-kernel and dual-quotient formulations instead.

For a fixed nontrivial wild action, Section 6.1 still gives a framed quotient, but the normalizer equations must be added and the tangent is the kernel of their augmented derivative. The three-term complex (6.6) and its smoothness test are listed only for trivial wild action.

The menu deliberately does not list “all lifts of the same conductor.” Without a fixed finite type or constant-rank monodromy model, that property need not be closed or stable under arbitrary Artinian base change.

### 13.2 Two-dimensional selection table

For later two-dimensional applications, the residual inertia matrix gives a quick first classification.

| Residual inertial shape after a rigid scalar twist                   | Intended arithmetic behavior                         | Condition                                                                  |
| -------------------------------------------------------------------- | ---------------------------------------------------- | -------------------------------------------------------------------------- |
| $1$                                                                  | no new ramification                                  | unramified                                                                 |
| $\operatorname{diag}(\bar\eta_1,\bar\eta_2)$, prime-to-$\ell$ finite | preserve finite semisimple ramification              | fixed inertial type                                                        |
| $1+\bar N$, $\bar N\ne0$, $\bar N^2=0$                               | preserve existing multiplicative ramification        | minimal unipotent/special                                                  |
| $1$ but Frobenius eigenvalue ratio $q$                               | allow a characteristic-zero multiplicative component | closed line-enhanced special condition, not minimal unramified             |
| scalar with no distinguished line                                    | preserve ramification only                           | framed intrinsic condition; do not impose a line without adding it as data |

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

**Step 9: record the obstruction calculation.** For unramified and fixed-type conditions use the explicit smooth normal forms rather than ambient $H^2$. For tame and special conditions record the cokernel of the derivative and say whether the explicit lifting argument kills it.

**Step 10: check functoriality needed later.** Extend coefficients, change frames, and restrict to local field extensions using Chapter 12. Recheck cyclicity, centralizers, tame-generator scaling, and conductor behavior after field extension.

This procedure produces not merely a label but a package:

$$
\bigl(\text{intrinsic condition},\ \text{representing object},
\ \text{tangent space},\ \text{obstructions},
\ \text{determinant},\ \text{conductor}\bigr).
$$

That is the unit of local information needed in a global deformation problem.

### 13.4 The local package theorem

We conclude the construction with a theorem that collects exactly what has been proved. It is intentionally divided by residual shape because a single uniform statement would conceal the exceptional loci.

**Theorem 13.1 (local conditions away from $\ell$).** Let $K$ have residue characteristic $p\ne\ell$, let $\bar\rho:G_K\to\operatorname{GL}_d(k)$ be continuous, and let the coefficient and determinant data be as in Section 1.2.

1. If $\bar\rho$ is unramified, the framed unramified condition is represented by a power-series ring of relative dimension $d^2$. With compatible fixed determinant it is smooth of dimension $d^2-1$. Its unframed tangent is $H^1_{\mathrm{ur}}(K,M)$, of dimension $h^0_K(M)$. If $\bar F$ is cyclic, the unframed condition is represented and smooth of dimension $d$, or $d-1$ with determinant fixed.
2. If residual inertia has a compatible integral model $\theta$ through a finite quotient $H$ with $\ell\nmid|H|$, the framed fixed-type condition is represented and smooth of dimension $d^2$. Its unframed tangent is again $H^1_{\mathrm{ur}}(K,M)$. With fixed determinant it is smooth of dimension $d^2-1$ whenever trace on the inertia centralizer is onto.
3. If wild inertia is killed, the full framed tame condition is represented by the matrix relation $FTF^{-1}=T^q$. Its tangent and complete relation obstruction spaces are the first and second cohomology of (6.6). At trivial residual inertia it is smooth of dimension $d^2$ whenever $q$ is not an adjoint Frobenius eigenvalue; the compatible fixed-determinant fiber is then smooth of dimension $d^2-1$.
4. In dimension two, fixed prime-to-$\ell$ finite inertia gives the minimal finite-type condition. A nonzero residual rank-one tame block gives the minimal unipotent condition. Under $\ell\ne2$ and $q\ne1$ the latter has smooth framed dimensions four without fixed determinant and three with fixed determinant; its represented unframed dimensions are one and zero.
5. If residual inertia is trivial but the Frobenius eigenvalue ratio is $q\ne1$, the line-enhanced closed special condition with fixed diagonal characters is represented and smooth of framed dimension three. It contains the monodromy-zero locus; nonzero monodromy is an open generic condition, not an Artinian subfunctor. Allowing the common unramified character adds one dimension, while a compatible fixed determinant with $\ell\ne2$ fixes its chosen square-root branch.

In every row, a stated unframed universal ring requires either the explicit cyclic classification, the scalar-centralizer theorem, or another descent result named in that row. At scalar Frobenius, coincident special characters, $\ell=2$ in dimension two, modular finite inertia with $\ell\mid|H|$, or a degenerate tame derivative, the framed equations remain available but no generic smooth dimension is asserted.

**Proof.** Parts (1)--(5) are respectively the universal Frobenius construction of Chapter 4, the averaging and centralizer-torsor argument of Chapter 5, the defect calculation of Chapter 6, Theorem 7.1, and Theorem 8.1. Closed relative representability follows in each case from Proposition 3.1 after retaining every required enhancement. The tangent identifications follow by linearizing the same defining equations, and the determinant dimensions follow from the transversality tests of Chapter 9. $\square$

The theorem supplies the promised local input for global deformation theory without importing any global conclusion. In particular, it does not say that arbitrary prescribed tangent subspaces are representable, that all components are smooth, or that conductor equality alone defines a closed condition. It says precisely which arithmetic shapes have been turned into formal local spaces and exactly where their dimensions are controlled.

## 14. Conclusion

### 14.1 Local equations with global consequences

Away from $\ell$, local deformation theory is governed by a sharp asymmetry inside inertia. Wild pro-$p$ actions are rigid in $\ell$-adic congruence directions, while the pro-$\ell$ tame factor can move. Arithmetic Frobenius controls that motion through

$$
\varphi\tau\varphi^{-1}=\tau^q.
$$

From this one relation come the universal Frobenius description of unramified lifts, the rigidity of prime-to-$\ell$ inertial types, the tame deformation complex, and the special equation $FNF^{-1}=qN$.

The formal geometry is as important as the matrix shapes. Framing cures orbit problems but adds coboundary directions. Cyclic Frobenius gives a genuine unframed coordinate system where scalar-centralizer arguments do not apply. A chosen line makes the enhanced special problem representable, yet forgetting it is safe only when uniqueness or descent has been proved. Nonzero monodromy is open, whereas the closed enhanced condition also contains its $N=0$ specializations. Fixed determinant is controlled by trace when $\ell\nmid d$ and demands greater care in characteristic two.

Minimality has consequently acquired an exact meaning rather than a slogan. Trivial residual inertia leads to the unramified condition. Finite prime-to-$\ell$ inertia leads to a fixed integral type. Existing nonzero rank-one tame monodromy leads to the minimal special condition. Each preserves conductor for a proved reason: an averaging idempotent in the finite case, and a constant-rank kernel in the unipotent case.

Finally, tangent spaces now come with honest obstruction tests. Unramified and fixed-type tangents are $H^1_{\mathrm{ur}}$, while their smoothness is proved by lifting Frobenius matrices and finite group actions. Tame and special tangents arise by differentiating their defining equations. The local Euler characteristic and the elementary top-degree calculation explain the exceptional eigenvalue ratios but never substitute for a lifting proof.

The result is a finite, rigorous menu of local conditions. Each entry says what ramification is retained, which choices are remembered, what ring represents the condition, what its tangent directions are, when it is smooth, how determinant modifies it, and under which hypotheses its conductor remains constant. These local packages are now ready to be assembled, without ambiguity, into global deformation problems.
