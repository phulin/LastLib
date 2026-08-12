# Global Deformation Problems

## Contents

1. [From local lifting rules to one global space](#1-from-local-lifting-rules-to-one-global-space)
   - [The assembly problem](#11-the-assembly-problem)
   - [The endpoint and its boundary](#12-the-endpoint-and-its-boundary)
   - [Four distinctions that govern the book](#13-four-distinctions-that-govern-the-book)
2. [Global arithmetic and coefficient data](#2-global-arithmetic-and-coefficient-data)
   - [The restricted global Galois group](#21-the-restricted-global-galois-group)
   - [Decomposition groups and localization](#22-decomposition-groups-and-localization)
   - [Coefficient categories](#23-coefficient-categories)
   - [The residual representation and ramification](#24-the-residual-representation-and-ramification)
   - [Fixed and variable determinant data](#25-fixed-and-variable-determinant-data)
   - [A notation for the clean cohomological cases](#26-a-notation-for-the-clean-cohomological-cases)
   - [Partially variable determinant conditions](#27-partially-variable-determinant-conditions)
3. [Global lifts, equivalence, and framings](#3-global-lifts-equivalence-and-framings)
   - [Lifts and strict equivalence](#31-lifts-and-strict-equivalence)
   - [The fully framed functor](#32-the-fully-framed-functor)
   - [Why partial framings are needed](#33-why-partial-framings-are-needed)
   - [The intrinsic meaning of partial framing](#34-the-intrinsic-meaning-of-partial-framing)
   - [Framing conventions at infinite places](#35-framing-conventions-at-infinite-places)
4. [Local deformation conditions and global data](#4-local-deformation-conditions-and-global-data)
   - [What the local condition must remember](#41-what-the-local-condition-must-remember)
   - [Determinant and base-change compatibility](#42-determinant-and-base-change-compatibility)
   - [Standard finite places away from the coefficient prime](#43-standard-finite-places-away-from-the-coefficient-prime)
   - [The finite-flat condition at coefficient-characteristic places](#44-the-finite-flat-condition-at-coefficient-characteristic-places)
   - [Archimedean local conditions](#45-archimedean-local-conditions)
   - [The global deformation datum](#46-the-global-deformation-datum)
5. [The global functor as a fiber product](#5-the-global-functor-as-a-fiber-product)
   - [Why the fiber product is forced](#51-why-the-fiber-product-is-forced)
   - [Conditions outside the framing set](#52-conditions-outside-the-framing-set)
   - [The unframed fiber product](#53-the-unframed-fiber-product)
   - [Ring directions](#54-ring-directions)
   - [Why completion and residue hypotheses matter](#55-why-completion-and-residue-hypotheses-matter)
   - [The universal property in deformation language](#56-the-universal-property-in-deformation-language)
6. [Pro-representability and universal global rings](#6-pro-representability-and-universal-global-rings)
   - [Global finiteness replaces finite generation](#61-global-finiteness-replaces-finite-generation)
   - [Framed representability](#62-framed-representability)
   - [Unframed representability and scalar endomorphisms](#63-unframed-representability-and-scalar-endomorphisms)
   - [Representability of the conditioned functor](#64-representability-of-the-conditioned-functor)
   - [Universal representations](#65-universal-representations)
   - [Closedness and quotient maps](#66-closedness-and-quotient-maps)
7. [Tangent spaces and Selmer conditions](#7-tangent-spaces-and-selmer-conditions)
   - [The global cocycle calculation](#71-the-global-cocycle-calculation)
   - [Local tangent subspaces and the Selmer kernel](#72-local-tangent-subspaces-and-the-selmer-kernel)
   - [The partially framed tangent quotient](#73-the-partially-framed-tangent-quotient)
   - [Local framed tangents](#74-local-framed-tangents)
   - [Relative tangents over the local base](#75-relative-tangents-over-the-local-base)
   - [Tangent quotients and localization rank](#76-tangent-quotients-and-localization-rank)
   - [The determinant complex in exceptional characteristic](#77-the-determinant-complex-in-exceptional-characteristic)
8. [Global and local obstruction theory](#8-global-and-local-obstruction-theory)
   - [The ambient global obstruction](#81-the-ambient-global-obstruction)
   - [Compatibility with localization](#82-compatibility-with-localization)
   - [Two stages for a constrained lift](#83-two-stages-for-a-constrained-lift)
   - [Relative obstruction complexes](#84-relative-obstruction-complexes)
   - [What “cohomologically controlled” means](#85-what-cohomologically-controlled-means)
   - [Complete and minimal obstruction spaces](#86-complete-and-minimal-obstruction-spaces)
   - [Smoothness and degree-two cohomology](#87-smoothness-and-degree-two-cohomology)
   - [Why an obstruction bound gives finitely many equations](#88-why-an-obstruction-bound-gives-finitely-many-equations)
9. [Poitou--Tate duality and the numerical formula](#9-poitou--tate-duality-and-the-numerical-formula)
   - [The Tate-twisted dual coefficient](#91-the-tate-twisted-dual-coefficient)
   - [Orthogonal local conditions](#92-orthogonal-local-conditions)
   - [The Selmer Poitou--Tate sequence](#93-the-selmer-poitou--tate-sequence)
   - [Derivation of the Wiles formula](#94-derivation-of-the-wiles-formula)
   - [The numerical defect](#95-the-numerical-defect)
   - [Strict conditions at the local base places](#96-strict-conditions-at-the-local-base-places)
   - [Comparing two systems of local conditions](#97-comparing-two-systems-of-local-conditions)
10. [Presentations over completed local deformation rings](#10-presentations-over-completed-local-deformation-rings)
    - [The local base ring](#101-the-local-base-ring)
    - [The relative relation bound](#102-the-relative-relation-bound)
    - [The fully expanded generator--relation defect](#103-the-fully-expanded-generator--relation-defect)
    - [Krull-dimension inequalities](#104-krull-dimension-inequalities)
    - [Absolute presentations over the coefficient ring](#105-absolute-presentations-over-the-coefficient-ring)
    - [Formal smoothness and local factors](#106-formal-smoothness-and-local-factors)
    - [The direction of every comparison map](#107-the-direction-of-every-comparison-map)
11. [Balanced odd deformation problems over totally real fields](#11-balanced-odd-deformation-problems-over-totally-real-fields)
    - [Why the totally real calculation matters](#111-why-the-totally-real-calculation-matters)
    - [Oddness at real places](#112-oddness-at-real-places)
    - [Minimal places away from the coefficient prime](#113-minimal-places-away-from-the-coefficient-prime)
    - [Finite-flat coefficient-prime places](#114-finite-flat-coefficient-prime-places)
    - [The balanced conclusion](#115-the-balanced-conclusion)
    - [What changes at coefficient prime two](#116-what-changes-at-coefficient-prime-two)
12. [Three consistency tests](#12-three-consistency-tests)
    - [A one-place unrestricted problem](#121-a-one-place-unrestricted-problem)
    - [A fixed-determinant Schur representation over a totally real field](#122-a-fixed-determinant-schur-representation-over-a-totally-real-field)
    - [A formally smooth finite-flat place](#123-a-formally-smooth-finite-flat-place)
13. [Changing the deformation datum](#13-changing-the-deformation-datum)
    - [Enlarging the ramification set](#131-enlarging-the-ramification-set)
    - [Strengthening and weakening a local condition](#132-strengthening-and-weakening-a-local-condition)
    - [Strict, unramified, and relaxed replacements](#133-strict-unramified-and-relaxed-replacements)
    - [Replacing a local factor by a formally smooth one](#134-replacing-a-local-factor-by-a-formally-smooth-one)
    - [Adding and forgetting frames](#135-adding-and-forgetting-frames)
    - [Specializing the determinant](#136-specializing-the-determinant)
14. [Coefficient changes and natural operations](#14-coefficient-changes-and-natural-operations)
    - [Extension of coefficient rings](#141-extension-of-coefficient-rings)
    - [Twisting by a fixed character](#142-twisting-by-a-fixed-character)
    - [Contragredients and Tate duality](#143-contragredients-and-tate-duality)
    - [Restriction of coefficient scalars](#144-restriction-of-coefficient-scalars)
    - [Restriction to a finite extension of number fields](#145-restriction-to-a-finite-extension-of-number-fields)
    - [Compatibility of the local tensor product with operations](#146-compatibility-of-the-local-tensor-product-with-operations)
15. [The global deformation-ring theorem package](#15-the-global-deformation-ring-theorem-package)
    - [Standing hypotheses for the package](#151-standing-hypotheses-for-the-package)
    - [Representability and the universal property](#152-representability-and-the-universal-property)
    - [Tangents, presentations, and relation bounds](#153-tangents-presentations-and-relation-bounds)
    - [The Poitou--Tate identity and numerical defect](#154-the-poitou--tate-identity-and-numerical-defect)
    - [The totally real rank-two specialization](#155-the-totally-real-rank-two-specialization)
    - [What the package exports, and what it does not](#156-what-the-package-exports-and-what-it-does-not)

## 1. From local lifting rules to one global space

Before introducing notation, it is useful to see the shape of the whole problem. Local conditions are not decorations attached after a universal ring has been built; they participate in its construction, its tangent theory, and its obstruction theory. The distinctions isolated here will keep those three levels synchronized throughout the book.

### 1.1 The assembly problem

A Galois representation over a number field is one object, but it has a different local shadow at every place. Deformation theory therefore faces a compatibility problem that does not occur in a purely local setting. One wants to let a residual representation vary globally while requiring, for example, that it remain minimally ramified at one finite place, special at another, and finite flat at every place above the coefficient prime. These local requirements cannot simply be imposed independently: the local restrictions must all come from the same global homomorphism.

The central object of this book is the ring that records exactly those simultaneous lifts. Its construction has three layers. Restricted ramification replaces the absolute Galois group by a manageable quotient. Local deformation conditions cut out formal subspaces of the local lifting problems. A fiber product then asks a global lift and a tuple of allowed local lifts to have the same local restrictions. Because functors of points and complete local rings have opposite variance, getting this last step right requires particular care with every arrow.

The numerical theory has the same three layers. A global first-order lift is a cocycle in an adjoint module. Passing to strict-equivalence classes turns cocycles into cohomology classes. Local tangent subspaces cut out a Selmer group. Obstructions begin in degree two, but global duality reorganizes the relevant constraints as a dual Selmer group. The resulting difference of dimensions is the numerical defect that later patching arguments consume.

The aim is thus not merely to name a universal ring. We will construct it, state the exact hypotheses under which it is universal, calculate its tangent space with all framing corrections, give rigorously qualified bounds on generators and relations over the product of the local rings, and isolate the Poitou--Tate identity that controls its expected size.

### 1.2 The endpoint and its boundary

The theory begins with a continuous residual representation

$$
\bar\rho:G_{K,S}\longrightarrow\operatorname{GL}_d(k)
$$

and a collection of representable local conditions. It ends with a complete Noetherian local ring $R_{\mathcal D}$, or a partially framed version $R_{\mathcal D}^{\square_T}$, together with:

- a universal global representation in the framed case, and a universal strict-equivalence class under the Schur hypothesis;
- a canonical map from a completed tensor product $R_{\mathrm{loc}}$ of local deformation rings;
- a Selmer description of its tangent space;
- a complete obstruction space under explicit compatibility hypotheses;
- a presentation

  $$
  R_{\mathcal D}^{\square_T}
  \simeq
  R_{\mathrm{loc}}
  [[x_1,\ldots,x_g]]/(f_1,\ldots,f_r)
  $$

  with an exact formula for $g$ and a justified upper bound for $r$;
- the Wiles--Poitou--Tate identity comparing the Selmer and dual-Selmer dimensions.

Auxiliary-prime selection, Taylor--Wiles systems, patched rings and modules, and the numerical proof of an isomorphism between a deformation ring and a Hecke ring require additional arithmetic and commutative algebra. They do not belong here. We will explain which numbers those later constructions require, but we stop at the interface that supplies them.

### 1.3 Four distinctions that govern the book

Several pairs of notions look similar but cannot be interchanged.

First, a framed tangent space is a cocycle space, not $H^1$. Coboundaries are precisely the infinitesimal changes of frame. Partial framings add still more matrix variables, and local centralizers determine which of those variables survive in a relative presentation.

Second, fixing determinant is not the same as removing scalar endomorphisms. When the characteristic of $k$ does not divide $d$, the full adjoint splits into scalars and trace zero. When it does divide $d$, scalar matrices lie in the trace-zero submodule, and both the tangent quotient and Tate dual change.

Third, an obstruction space need not be minimal. A cohomology group can contain every actual obstruction while containing classes that never occur. Even a complete and effective obstruction theory gives an upper bound on the number of relations, not an equality unless a separate argument identifies the minimal relation space.

Fourth, nonvanishing of $H^2$ does not imply singularity, and vanishing of an ambient $H^2$ does not by itself make a constrained problem smooth. A restricted condition can have an identically zero obstruction map into a nonzero ambient group. Conversely, an integral local model can fail to lift even after the generic representation obstruction has vanished.

These distinctions are not warnings placed around the theory. They determine the correct statements of its main theorems.

## 2. Global arithmetic and coefficient data

A global deformation problem is meaningful only after its ramification, coefficients, residual point, and determinant have been fixed. Each choice changes either the category of lifts or the cohomology that controls them. This chapter establishes one set of conventions strong enough to support all later local-to-global comparisons, while marking the exceptional cases that require complexes rather than a single adjoint module.

### 2.1 The restricted global Galois group

Let $K$ be a number field, let $\overline K$ be a fixed algebraic closure, and let $S$ be a finite set of places of $K$. We require $S$ to contain every archimedean place. Once a coefficient prime $\ell$ and residual representation have been chosen, we also require $S$ to contain:

- every place above $\ell$;
- every finite place at which the residual representation is ramified;
- every finite place at which the chosen determinant is ramified;
- every place at which the local condition is not the unramified condition.

Let $K_S$ be the maximal extension of $K$ in $\overline K$ unramified at every finite place outside $S$, and write

$$
G_{K,S}=\operatorname{Gal}(K_S/K).
$$

The group $G_{K,S}$ remembers Frobenius elements outside $S$; it kills only the corresponding inertia groups. A continuous lift through $G_{K,S}$ is therefore unramified outside $S$, not trivial outside $S$.

If $S\subseteq S'$, then $K_S\subseteq K_{S'}$ and restriction gives a surjection

$$
G_{K,S'}\twoheadrightarrow G_{K,S}.
$$

The direction reflects the fact that the larger set permits more ramification. Later we will show that enlarging $S$ and imposing the unramified condition at the new places does not change the global deformation problem.

### 2.2 Decomposition groups and localization

For every place $v$, choose a geometric place of $\overline K$ above $v$. This gives a homomorphism

$$
G_{K_v}\longrightarrow G_{K,S},
$$

well defined up to conjugacy. Restricting representations and cochains along it gives localization maps. Replacing the geometric place conjugates the local homomorphism, and strict-equivalence classes and cohomology are canonically transported. Thus no universal ring constructed below depends on the geometric choices, although matrix formulas use representatives of them.

At a complex place the local Galois group is trivial. At a real place it is

$$
G_{K_v}=\langle c_v\rangle\simeq C_2.
$$

For coefficients of odd characteristic, positive-degree cohomology at a real place vanishes. For characteristic two, it is periodic and cannot be discarded. Global duality then uses Tate-modified cohomology at real places, while degree-one deformation conditions continue to use ordinary $H^1$, which agrees with modified degree one.

### 2.3 Coefficient categories

Fix a prime $\ell$, a finite field $k$ of characteristic $\ell$, and a complete Noetherian local ring $\mathcal O$ with maximal ideal $\mathfrak m_{\mathcal O}$ and specified residue field $k$. In the standard mixed-characteristic setting, $\mathcal O$ is the ring of integers in a finite extension of $\mathbf Q_\ell$. Equal characteristic is included by taking $\mathcal O=k$ or a complete local $k$-algebra.

Let $\operatorname{Art}_{\mathcal O}$ be the category of local Artinian $\mathcal O$-algebras $A$ equipped with a specified identification $A/\mathfrak m_A\simeq k$. Morphisms are local $\mathcal O$-algebra maps inducing the identity on $k$. Let $\operatorname{CNL}_{\mathcal O}$ be the corresponding category of complete Noetherian local $\mathcal O$-algebras with residue field $k$ and continuous local maps.

All deformation functors are covariant in the Artinian test ring. A map $A\to B$ extends coefficients and sends a lift over $A$ to a lift over $B$. A representing ring varies in the opposite direction: a natural transformation $F\to G$ corresponds to a continuous map $R_G\to R_F$.

The common residue field is structural. Completed tensor products of local rings with compatible residue maps remain local with residue field $k$ under the topological finite-type hypotheses used here. If the residue fields do not agree, their tensor product need not be a field, and the formal product can split into several closed points. Before combining local problems one must therefore extend all coefficient data to one common residue field.

### 2.4 The residual representation and ramification

Fix a continuous representation

$$
\bar\rho:G_{K,S}\longrightarrow\operatorname{GL}_d(k)
$$

on a $d$-dimensional $k$-space $\bar V$. Continuity means that it factors through a finite quotient. Its restriction to $G_{K_v}$ will be denoted $\bar\rho_v$.

The full adjoint module is

$$
\operatorname{ad}\bar\rho=\operatorname{End}_k(\bar V),
\qquad
g\cdot X=\bar\rho(g)X\bar\rho(g)^{-1}.
$$

Its invariants are the global residual endomorphisms:

$$
H^0(G_{K,S},\operatorname{ad}\bar\rho)
=\operatorname{End}_{k[G_{K,S}]}(\bar V).
$$

At a place $v$, $H^0(K_v,\operatorname{ad}\bar\rho)$ is the centralizer of the local image. Local centralizers can be larger than the global one, and their dimensions enter the relative framing count.

The standard Schur hypothesis is

$$
\operatorname{End}_{k[G_{K,S}]}(\bar V)=k.
\tag{2.1}
$$

Absolute irreducibility implies (2.1), but (2.1) is the exact hypothesis used to make the ordinary unframed set-valued functor universal. Framed functors do not need it. Nor does (2.1) imply that every local centralizer is scalar.

### 2.5 Fixed and variable determinant data

There are two basic determinant problems.

For a fixed determinant, choose a continuous character

$$
\delta:G_{K,S}\longrightarrow\mathcal O^\times
$$

whose reduction is $\det\bar\rho$. Its composite with $\mathcal O\to A$ is denoted $\delta_A$. A lift $\rho_A$ is required to satisfy

$$
\det\rho_A=\delta_A.
$$

The character $\delta$, not merely its residual reduction, is part of the global datum. Its restriction must agree with the determinant demanded by every local condition.

For a variable determinant, one may allow every determinant character unramified outside $S$, or impose a separate representable character-deformation condition. In the fully variable case, the tangent coefficient is $\operatorname{ad}\bar\rho$. In the fixed case, the derivative of determinant is trace, so framed first-order cocycles take values in

$$
\operatorname{ad}^0\bar\rho
=\ker\bigl(\operatorname{tr}:\operatorname{ad}\bar\rho\to k\bigr).
$$

When $\ell\nmid d$, there is a $G_{K,S}$-equivariant splitting

$$
\operatorname{ad}\bar\rho
=kI_d\oplus\operatorname{ad}^0\bar\rho.
\tag{2.2}
$$

In that case ordinary fixed-determinant unframed tangents are computed by $H^1(\operatorname{ad}^0\bar\rho)$, and the trace pairing is perfect on $\operatorname{ad}^0\bar\rho$.

When $\ell\mid d$, neither statement is automatic. The correct unframed tangent is

$$
\frac{Z^1(G_{K,S},\operatorname{ad}^0\bar\rho)}
{d(\operatorname{ad}\bar\rho)}
=\ker\left(
H^1(G_{K,S},\operatorname{ad}\bar\rho)
\xrightarrow{\operatorname{tr}}H^1(G_{K,S},k)
\right).
\tag{2.3}
$$

Moreover, the trace pairing identifies

$$
(\operatorname{ad}^0\bar\rho)^*
\simeq\operatorname{ad}\bar\rho/kI_d,
\tag{2.4}
$$

not generally with $\operatorname{ad}^0\bar\rho$. In dimension two and characteristic two, $I_2$ itself has trace zero. Any formula obtained by dividing by $2$, subtracting a scalar line, or replacing the dual in (2.4) by $\operatorname{ad}^0$ is invalid.

### 2.6 A notation for the clean cohomological cases

Many formulas have one uniform form once the tangent coefficient is an honest $G_{K,S}$-module. We therefore write

$$
M=
\begin{cases}
\operatorname{ad}\bar\rho,&\text{variable determinant},\\
\operatorname{ad}^0\bar\rho,&\text{fixed determinant and }\ell\nmid d,
\end{cases}
\tag{2.5}
$$

and

$$
M'=M^*(1).
\tag{2.6}
$$

The module governing changes of basis is always

$$
A_{\mathrm{gauge}}=\operatorname{ad}\bar\rho,
\tag{2.7}
$$

because fixing the determinant of a representation does not restrict its conjugators. In the fixed-determinant case covered by (2.2), $d(A_{\mathrm{gauge}})=d(M)$, but their invariant spaces differ by the scalar line.

When $\ell\mid d$, we will return to the exact trace-kernel complex rather than use the shorthand (2.5). This keeps the clean formulas useful without pretending that they include characteristic two.

The coefficient bookkeeping can be summarized as follows.

| determinant problem | positive-degree tangent coefficient | degree-zero gauge | Tate-dual coefficient |
|---|---|---|---|
| fully variable | $\operatorname{ad}\bar\rho$ | $\operatorname{ad}\bar\rho$ | $(\operatorname{ad}\bar\rho)^*(1)$ |
| fixed, $\ell\nmid d$ | $\operatorname{ad}^0\bar\rho$ | $\operatorname{ad}\bar\rho$ | $(\operatorname{ad}^0\bar\rho)^*(1)$ |
| fixed, $\ell\mid d$ | trace-kernel complex | $\operatorname{ad}\bar\rho$ | dual trace-kernel complex using $(\operatorname{ad}^0)^*\simeq\operatorname{ad}/kI_d$ |
| constrained variable | determinant mapping fiber | $\operatorname{ad}\bar\rho$ | Tate dual of that mapping fiber |

The second and third columns need not agree. This is exactly why determinant fixing changes cocycles without shrinking the space of changes of basis.

### 2.7 Partially variable determinant conditions

Fixed determinant and completely variable determinant are the two cases with a single familiar adjoint coefficient, but they do not exhaust the possibilities. One may require the determinant to be ordinary at places above $\ell$, unramified outside a smaller set, or to vary in a prescribed family of characters. Such a condition must itself be treated as a deformation problem.

Let $\bar\delta=\det\bar\rho$, and let $D_{\det}$ be a representable subfunctor of the functor of characters

$$
G_{K,S}\longrightarrow A^\times
$$

lifting $\bar\delta$. Write $R_{\det}$ for its universal ring. Taking determinants gives a transformation from the unrestricted representation functor to the unrestricted character functor and therefore a map from the universal character ring to the universal representation ring. Requiring the determinant to belong to $D_{\det}$ is a fiber product over the unrestricted character functor.

Let

$$
L_{\det}\subseteq H^1(G_{K,S},k)
$$

be the tangent space of $D_{\det}$. Since the derivative of determinant is trace, the unframed representation tangent with this determinant condition is

$$
\left\{
x\in H^1(G_{K,S},\operatorname{ad}\bar\rho):
\operatorname{tr}(x)\in L_{\det}
\right\}.
\tag{2.8}
$$

Local determinant conditions replace $L_{\det}$ by their own compatible local tangent subspaces and impose the corresponding fiber-product condition on localization. Coboundaries have trace zero, so (2.8) is well defined even when $\ell\mid d$.

There are two endpoint checks. If every determinant is allowed, then $L_{\det}=H^1(G_{K,S},k)$ and (2.8) is $H^1(G_{K,S},\operatorname{ad}\bar\rho)$. If the determinant is the single fixed character $\delta$, then $L_{\det}=0$ and (2.8) is the trace kernel (2.3). Only when $\ell\nmid d$ does the latter identify canonically with $H^1(G_{K,S},\operatorname{ad}^0\bar\rho)$.

For an intermediate determinant condition, the controlling object is the mapping fiber of the trace map from adjoint cochains to the quotient of scalar cochains by the determinant-condition complex. Its obstruction and Poitou--Tate theories are hypercohomological. All constructions below remain valid with that complex, provided the determinant functor has compatible complete obstruction data. The compact formulas using a single module $M$ are stated only for the two clean endpoints (2.5). This convention records determinant constraints rather than silently dropping their tangent or obstruction terms.

## 3. Global lifts, equivalence, and framings

The same representation can define different deformation functors depending on which bases are remembered. Unframed objects express the intrinsic moduli problem, fully framed objects eliminate automorphisms, and partial frames connect one global object to several independently based local objects. The purpose of this chapter is to define all three without losing track of the scalar stabilizers that later affect dimension counts.

### 3.1 Lifts and strict equivalence

For $A\in\operatorname{Art}_{\mathcal O}$, a lift of $\bar\rho$ is a continuous homomorphism

$$
\rho_A:G_{K,S}\longrightarrow\operatorname{GL}_d(A)
$$

whose reduction is exactly $\bar\rho$. In intrinsic terms it is a free rank-$d$ $A$-module with continuous $G_{K,S}$-action and a fixed identification of its special fiber with $\bar V$.

Put

$$
\Gamma_A=\ker\bigl(\operatorname{GL}_d(A)\to\operatorname{GL}_d(k)\bigr).
$$

Two lifts are strictly equivalent if they are conjugate by an element of $\Gamma_A$. The congruence condition preserves the chosen residual identification. Quotienting by arbitrary conjugacy would forget part of the residual datum and would generally change the functor.

The unframed global deformation functor is

$$
D_{K,S}(A)=
\{\text{lifts of }\bar\rho\text{ to }A\}/\text{strict equivalence}.
$$

Its fixed-determinant subfunctor is denoted $D_{K,S}^{\delta}$. Under the Schur hypothesis and the standard global cohomological finiteness condition, these functors are pro-representable. Without the Schur hypothesis they can still have a hull, but a universal coarse orbit ring is not automatic.

### 3.2 The fully framed functor

The fully framed functor retains the actual matrix homomorphism:

$$
D_{K,S}^{\square}(A)
=\{\rho_A:G_{K,S}\to\operatorname{GL}_d(A)
\text{ lifting }\bar\rho\}.
$$

There is no conjugacy quotient. Matrix representations glue exactly over coefficient fiber products, so the framed functor is the safest universal object when residual centralizers are large.

A frame should not be counted as $d^2$ free directions without examining its stabilizer. At first order the framed tangent is $Z^1$, and

$$
0\longrightarrow H^0(G_{K,S},A_{\mathrm{gauge}})
\longrightarrow A_{\mathrm{gauge}}
\xrightarrow{d}Z^1(G_{K,S},A_{\mathrm{gauge}})
\longrightarrow H^1(G_{K,S},A_{\mathrm{gauge}})
\longrightarrow0.
$$

Thus framing adds $d^2-h^0(G_{K,S},A_{\mathrm{gauge}})$ directions to an unrestricted unframed tangent. Under (2.1), this is $d^2-1$, not $d^2$.

### 3.3 Why partial framings are needed

To compare a global ring with a product of independently framed local rings, one needs an independent local coordinate system at each selected place. A single global matrix basis does not supply independent changes of basis at several places. Partial framing records precisely those comparisons.

Let $T$ be a nonempty finite set of places contained in $S$. In the standard patching application, $T$ consists of finite places and contains every place whose local deformation ring is placed in $R_{\mathrm{loc}}$.

A $T$-framed lift may be described by a tuple

$$
(\rho_A,(\alpha_v)_{v\in T}),
\qquad \alpha_v\in\Gamma_A,
$$

modulo the simultaneous action

$$
(\rho_A,(\alpha_v))
\sim
(\beta\rho_A\beta^{-1},(\alpha_v\beta^{-1})_{v\in T}),
\qquad \beta\in\Gamma_A.
\tag{3.1}
$$

The associated locally framed restriction at $v$ is

$$
\alpha_v\rho_A|_{G_{K_v}}\alpha_v^{-1}.
\tag{3.2}
$$

When $T$ has one element, (3.1) lets one set that $\alpha_v$ equal to $1$, recovering the usual globally framed matrix problem. Additional places record independent comparison matrices. Scalar ratios between different $\alpha_v$ are part of this standard rigidification even though scalar conjugation does not change an individual local matrix; their contribution will appear as local $H^0$ terms in the relative tangent space.

The notation $D_{K,S}^{\square_T}$ will denote this functor. A fixed determinant constrains $\rho_A$ but does not constrain the matrices $\alpha_v$.

### 3.4 The intrinsic meaning of partial framing

The tuple description depends on a temporary global basis, but the functor does not. Intrinsically, a $T$-framed lift is a global deformation together with, at every $v\in T$, a basis of the restricted free module lifting the chosen residual basis, with the usual identification by global isomorphisms. Formula (3.1) is obtained by choosing one auxiliary global basis.

This intrinsic description explains two points. First, changing the residual basis transports every frame and gives an isomorphic deformation problem. Second, a local framed condition can be imposed on (3.2) without choosing a preferred global representative of an unframed class.

### 3.5 Framing conventions at infinite places

Archimedean places normally enter the Selmer structure but not the completed tensor product of finite local deformation rings. For odd $\ell$, the local degree-one deformation theory at a real place is rigid because $2$ is invertible. It is therefore enough to impose the chosen real conjugacy class as a local condition and retain its $H^0$ contribution in the numerical formula.

At $\ell=2$, this shortcut is unavailable. One must either include a genuine local deformation condition for the $C_2$-representation among the represented local factors or keep its deformation complex explicitly in the global obstruction theory. No theorem below silently treats a real $2$-primary condition as rigid.

## 4. Local deformation conditions and global data

The global ring can enforce only local conditions that are genuinely functorial over coefficient rings. A tangent subspace describes first-order behavior, but it does not by itself define an integral deformation condition or guarantee compatible obstructions. We therefore specify the full local input first and extract its tangent only afterward.

### 4.1 What the local condition must remember

Fix a place $v\in S$. The residual local representation is

$$
\bar\rho_v:G_{K_v}\longrightarrow\operatorname{GL}_d(k).
$$

A useful local condition is more than a subset of local lifts. It must survive coefficient change, be invariant under the chosen equivalence relation, glue over Artinian fiber products, and be represented by a closed formal subspace of an ambient local deformation problem.

For the framed local functor $D_v^{\square}$, a **representable local deformation condition** $\mathcal D_v$ consists of subfunctors

$$
D_v^{\square,\mathcal D_v}(A)\subseteq D_v^{\square}(A)
$$

such that:

1. the residual lift belongs to the condition;
2. coefficient maps preserve membership;
3. membership is invariant under strict changes of basis in the intrinsic formulation;
4. the condition has exact framed gluing over the coefficient fiber products used in the representability criterion;
5. it is pro-represented by a quotient $R_v^{\square}\twoheadrightarrow R_v^{\square,\mathcal D_v}$.

For an unframed local condition one additionally needs a representable unframed ambient problem, or a separate descent theorem controlling automorphisms. When a local residual centralizer is not scalar, the framed quotient is the default safe object.

The tangent image of an unframed condition is a $k$-subspace

$$
L_v\subseteq H^1(K_v,M).
\tag{4.1}
$$

The corresponding framed tangent is the inverse image of $L_v$ in the appropriate cocycle space. In the clean cases (2.5), its dimension is

$$
\dim_k L_v+d^2-h^0(K_v,A_{\mathrm{gauge}}).
\tag{4.2}
$$

For fixed determinant with $\ell\nmid d$, (4.2) agrees with the cocycle calculation using $M=\operatorname{ad}^0\bar\rho$. In characteristic dividing $d$, one must use the trace-kernel quotient rather than (4.2) with a silently substituted module.

### 4.2 Determinant and base-change compatibility

In a fixed-determinant problem every object of $\mathcal D_v$ must have determinant $\delta|_{G_{K_v}}$. This is a compatibility condition at the residual and lifted levels. A finite inertial type whose determinant disagrees with $\delta$ defines an empty problem. A finite-flat condition with a separately fixed determinant must use an integral theory compatible with that character.

Base-change stability means stability under every morphism in $\operatorname{Art}_{\mathcal O}$, not only flat extensions. This is particularly important for integral conditions at $v\mid\ell$: reduction by a coefficient ideal must preserve the condition. It is also what makes the collection of local points into a functor represented by one complete ring.

### 4.3 Standard finite places away from the coefficient prime

At a finite place $v\nmid\ell$, the local theory supplies several legitimate choices.

- If $\bar\rho_v$ is unramified, the unramified condition requires inertia to remain trivial. Its tangent is $H^1_{\mathrm{ur}}(K_v,M)$. The framed condition is formally smooth because a lift is determined by one freely lifted Frobenius matrix. With fixed determinant, the same conclusion has relative dimension $d^2-1$; the determinant equation is smooth in this unramified situation.
- A compatible prime-to-$\ell$ finite inertial type, together with an integral inertia model and a Frobenius intertwiner, gives a representable fixed-type condition. Averaging over the finite inertia quotient makes its deformations rigid up to conjugacy, and its unframed tangent is again $H^1_{\mathrm{ur}}(K_v,M)$. The framed condition is formally smooth of relative dimension $d^2$. Its fixed-determinant fiber is smooth of dimension $d^2-1$ when trace on the inertia centralizer is onto; this is automatic if $\ell\nmid d$, but must otherwise be checked.
- Minimal unipotent and special conditions are available in the residual shapes for which their line, monodromy, determinant, and descent data have been specified. Their tangent spaces come from the derivative of their actual equations, not from a generic dimension slogan.
- The relaxed condition has $L_v=H^1(K_v,M)$; the strict tangent condition has $L_v=0$.

For unramified or fixed prime-to-$\ell$ type conditions,

$$
\dim_kL_v=h^0(K_v,M),
\tag{4.3}
$$

so their contribution $\dim L_v-h^0(K_v,M)$ to the Wiles formula is zero. This numerical neutrality is one reason these are the natural minimal conditions away from $\ell$.

### 4.4 The finite-flat condition at coefficient-characteristic places

At a place above $\ell$, finite flatness is a legitimate local condition supplied by the integral theory developed earlier. It is defined by the existence of an $A$-linear finite locally free group model over $\mathcal O_{K_v}$ whose generic points realize the local representation. The existential framed functor is pro-representable for every finite extension $K_v/\mathbf Q_\ell$ and every finite-flat residual representation. Under the scalar-centralizer hypothesis, the unframed functor is pro-representable as well.

Its tangent subspace is

$$
L_v=H^1_{\mathrm{fl}}(K_v,M),
\tag{4.4}
$$

with the trace-kernel interpretation for fixed determinant in exceptional characteristic. Its Tate-dual local condition is, unconditionally, the exact orthogonal $L_v^\perp$. It must not be identified with a geometric finite-flat extension condition without an additional integral duality theorem.

There is a sharper theorem in one specific range. Retain here the mixed-characteristic coefficient setup of Book 68: $\mathcal O$ is the ring of integers in a finite extension of $\mathbf Q_\ell$, enlarged as required to contain the residue embeddings used by the local classification. Suppose $K_v/\mathbf Q_\ell$ is unramified of degree $f_v$, $\ell>2$, $d=2$, $\bar\rho_v$ is finite flat with determinant $\bar\chi_\ell$, and the determinant is fixed to $\chi_\ell$. Put

$$
h_v=\dim_k\operatorname{End}_{k[G_{K_v}]}(\bar V).
$$

Then

$$
\dim_k H^1_{\mathrm{fl}}
(K_v,\operatorname{ad}^0\bar\rho)=f_v+h_v-1,
\tag{4.5}
$$

and the framed fixed-determinant ring is formally smooth:

$$
R_v^{\square,\mathrm{fl},\chi_\ell}
\simeq\mathcal O[[z_1,\ldots,z_{f_v+3}]].
\tag{4.6}
$$

If $h_v=1$, the unframed ring is $\mathcal O[[x_1,\ldots,x_{f_v}]]$. For $h_v>1$, the framed ring (4.6) still exists, but a coarse unframed universal ring is not asserted in general. Outside the unramified odd rank-two range, the general represented quotient and its tangent subspace remain valid, while a relation ideal must be retained until an independent lifting theorem removes it.

This is exactly how finite flatness enters the global theory: as one representable local condition with a proved tangent subspace, a rigorously defined orthogonal, and a smooth dimension formula only where the integral theorem supplies it.

### 4.5 Archimedean local conditions

At a complex place, $H^1$ is zero and the only local condition is trivial. Nevertheless ordinary $H^0(K_v,M)=M$ contributes to the global numerical formula.

At a real place and odd $\ell$, $H^1(K_v,M)=0$. A chosen residual conjugacy class therefore has tangent $L_v=0$. If $d=2$ and the representation is odd, complex conjugation has eigenvalues $1$ and $-1$, so on $M=\operatorname{ad}^0\bar\rho$ one has

$$
h^0(K_v,M)=1.
\tag{4.7}
$$

The local contribution is consequently $-1$. This is the cohomological source of the real-place sign in two-dimensional modularity lifting.

For $\ell=2$, neither the vanishing nor the eigenspace argument is available. The local condition at every real place must be named, and the modified Poitou--Tate convention must be retained in the proof of the numerical formula.

### 4.6 The global deformation datum

A **global deformation datum**

$$
\mathcal D=(K,S,\mathcal O,k,\bar\rho,\det\text{-data},
(\mathcal D_v)_{v\in S})
\tag{4.8}
$$

consists of the following.

1. The number field, finite controlling set, coefficient category, and residual representation satisfy the hypotheses of Chapter 2.
2. The determinant is either a fixed lift $\delta$ or a separately specified representable determinant-deformation problem.
3. At every finite $v\in S$, $\mathcal D_v$ is a representable local condition on $\bar\rho_v$, formulated in a framed category whenever unframed descent has not been proved.
4. At every archimedean place, an explicit local condition is chosen; for odd coefficients this may be the rigid residual conjugacy class.
5. All local conditions contain the residual point, are stable under arbitrary coefficient base change, and have determinant compatible with the global determinant data.
6. Outside $S$, the condition is unramified and is built into $G_{K,S}$.

The datum is called **Schur** if (2.1) holds. It is called **cohomologically controlled** if, in addition, the local lifting theories admit compatible complete and effective obstruction data of the kind specified in Chapter 8. Representability needs the former set of local formal properties; cohomological relation bounds need the latter. Keeping the two adjectives separate prevents a tangent calculation from being mistaken for an obstruction theorem.

## 5. The global functor as a fiber product

This chapter performs the actual assembly. The key is to work first on functors of coefficient algebras, where the compatibility condition is an ordinary fiber product, and only then reverse arrows to obtain a completed tensor product of rings. Doing so prevents the most common variance error and makes the universal property transparent.

### 5.1 Why the fiber product is forced

A global lift satisfying local conditions contains two descriptions of its behavior at every selected place. Restriction of the global lift gives one local representation. Membership in the local condition says that this representation is also a point of a prescribed local subfunctor. The two descriptions must agree in the ambient unrestricted local functor. This is exactly an inverse-image problem, hence a fiber product of functors.

The construction is clearest with partial framings. Fix a nonempty set $T$ of places at which local framed rings will be used. For the moment suppose $T$ contains every finite place in $S$; the version with conditions outside $T$ will be recorded later. Put

$$
D_{\mathrm{loc}}^{\square,\mathrm{unr}}
=\prod_{v\in T}D_v^{\square}
$$

and

$$
D_{\mathrm{loc}}^{\square,\mathcal D}
=\prod_{v\in T}D_v^{\square,\mathcal D_v}.
$$

Restriction using (3.2) gives a natural transformation

$$
\operatorname{res}_T:
D_{K,S}^{\square_T}
\longrightarrow D_{\mathrm{loc}}^{\square,\mathrm{unr}}.
\tag{5.1}
$$

The local conditions give an inclusion

$$
D_{\mathrm{loc}}^{\square,\mathcal D}
\longrightarrow D_{\mathrm{loc}}^{\square,\mathrm{unr}}.
\tag{5.2}
$$

Define

$$
\boxed{
D_{\mathcal D}^{\square_T}
=D_{K,S}^{\square_T}
\times_{D_{\mathrm{loc}}^{\square,\mathrm{unr}}}
D_{\mathrm{loc}}^{\square,\mathcal D}.}
\tag{5.3}
$$

A point of (5.3) is a $T$-framed global lift together with allowed local lifts whose underlying locally framed representations equal its restrictions. Since the local lift is then determined by the restriction, (5.3) is naturally the subfunctor of global $T$-framed lifts satisfying every $\mathcal D_v$. Writing it as a fiber product is nevertheless essential: it proves representability and fixes the ring-map directions.

### 5.2 Conditions outside the framing set

If $T\subsetneq S$, local conditions at $v\in S\setminus T$ are imposed directly on the unframed restriction. Let $D_{K,S}^{\square_T,\mathcal D^{S\setminus T}}$ be that closed subfunctor. Then

$$
D_{\mathcal D}^{\square_T}
=D_{K,S}^{\square_T,\mathcal D^{S\setminus T}}
\times_{\prod_{v\in T}D_v^{\square}}
\prod_{v\in T}D_v^{\square,\mathcal D_v}.
\tag{5.4}
$$

This form is useful when $T$ contains the finite local factors used as a base ring, while the rigid conditions at infinity remain outside $T$. It also shows why relative tangent theory uses the strict condition at places in $T$ and the original tangent subspace at places outside $T$.

### 5.3 The unframed fiber product

Assume the global and every required local unframed functor are pro-representable. Restriction gives

$$
D_{K,S}\longrightarrow\prod_{v\in S}D_v,
$$

and one may define

$$
D_{\mathcal D}
=D_{K,S}\times_{\prod_vD_v}\prod_vD_v^{\mathcal D_v}.
\tag{5.5}
$$

Under the global Schur hypothesis, the left-hand unframed functor is universal. Local unframed representability may still fail if a local centralizer is large. For a fiber-product construction over independent local rings, formula (5.5) must then be replaced by the framed construction (5.3), not interpreted through a nonexistent local coarse ring.

When (5.5) exists, its tangent space is the ordinary Selmer group. It is the most economical intrinsic problem. The partially framed problem is the robust comparison object used to place the global ring over independently defined local rings.

Local coarse representability is sufficient for (5.5), but it is not necessary for the existence of the global unframed ring. Under the global Schur hypothesis, choose a representative of the universal global strict-equivalence class and restrict it at $v$. Pulling the quotient $R_v^\square\twoheadrightarrow R_v^{\square,\mathcal D_v}$ back along this framed restriction cuts out a quotient of the global unframed ring. The resulting ideal is independent of the chosen universal representative because membership in $\mathcal D_v$ is invariant under strict conjugacy. Thus conjugacy-invariant framed conditions can be imposed directly on a Schur global problem even when a large local centralizer prevents a local coarse universal ring. Formula (5.5) should be used only when its local unframed factors actually exist.

### 5.4 Ring directions

Suppose the functors in (5.3) are represented. Write

$$
R_{\mathrm{loc}}^{\square,\mathrm{unr}}
=\widehat\bigotimes_{v\in T,\mathcal O}R_v^{\square}
$$

and

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in T,\mathcal O}
R_v^{\square,\mathcal D_v}.
\tag{5.6}
$$

The product of functors is represented by the completed tensor product because all factors have the same residue field and are topologically of finite type over $\mathcal O$. The inclusion of each local condition corresponds to a quotient

$$
R_v^{\square}\twoheadrightarrow R_v^{\square,\mathcal D_v},
$$

and therefore to

$$
R_{\mathrm{loc}}^{\square,\mathrm{unr}}
\longrightarrow R_{\mathrm{loc}}.
\tag{5.7}
$$

Restriction (5.1) points from the global functor to the local functor, so its representing ring map points from local to global:

$$
R_{\mathrm{loc}}^{\square,\mathrm{unr}}
\longrightarrow R_{K,S}^{\square_T}.
\tag{5.8}
$$

Consequently the ring representing (5.3) is

$$
\boxed{
R_{\mathcal D}^{\square_T}
\simeq
R_{K,S}^{\square_T}
\widehat\otimes_{R_{\mathrm{loc}}^{\square,\mathrm{unr}}}
R_{\mathrm{loc}}.}
\tag{5.9}
$$

Both arrows in the tensor product start at the unrestricted local ring. The two factor maps then give

$$
R_{\mathrm{loc}}\longrightarrow R_{\mathcal D}^{\square_T}
\tag{5.10}
$$

and

$$
R_{K,S}^{\square_T}\longrightarrow R_{\mathcal D}^{\square_T}.
$$

The second is a quotient when the global condition is closed inside the unrestricted global problem. The first is generally neither injective nor surjective; it is the structural map over which the relative presentation will be built.

### 5.5 Why completion and residue hypotheses matter

The tensor product in (5.9) is completed for the ideals generated by the maximal ideals of the factors. In power-series presentations it has the concrete form obtained by adjoining all variables and all equations in one complete ring. The ordinary tensor product would miss infinite formal series involving parameters from different places.

For two factors one may define it by

$$
R_1\widehat\otimes_{\mathcal O}R_2
=\varprojlim_n
\frac{R_1\otimes_{\mathcal O}R_2}
{(\mathfrak m_1\otimes R_2+R_1\otimes\mathfrak m_2)^n},
\tag{5.11}
$$

with the evident separated completion if the displayed ordinary tensor product is not already separated. Equivalent cofinal systems may use powers of $\mathfrak m_1$, $\mathfrak m_2$, and $\mathfrak m_{\mathcal O}$. For example, if

$$
R_1=\mathcal O[[X_1,\ldots,X_a]]/I_1,
\qquad
R_2=\mathcal O[[Y_1,\ldots,Y_b]]/I_2,
$$

then

$$
R_1\widehat\otimes_{\mathcal O}R_2
\simeq
\mathcal O[[X_1,\ldots,X_a,Y_1,\ldots,Y_b]]/(I_1,I_2).
\tag{5.12}
$$

This example also proves topological finite generation of a finite completed product when each factor has a finite power-series presentation.

Locality requires the residue maps to agree. If $R_1$ and $R_2$ have residue fields $k_1$ and $k_2$ over the residue field of the base, then $k_1\otimes k_2$ can split or fail to be a field. In that situation there is no single residual point until a component and a common residue field have been selected.

Noetherianity is also a hypothesis, not a consequence of the completion symbol. It follows here because every factor is a complete Noetherian local algebra topologically of finite type over the common base. Since $T$ is finite, iterated completed tensor products remain in the same category.

The completed tensor product in (5.9) is relative over the *unrestricted local* ring, not merely over $\mathcal O$. It is the completion of the algebraic pushout at the maximal ideal determined by the common residual representation. If several maximal ideals lie above the algebraic pushout, choosing the residual point and completing there is part of the construction. This is the ring-theoretic counterpart of requiring equality of the two locally framed residual lifts in the functor fiber product.

### 5.6 The universal property in deformation language

Let $A\in\operatorname{Art}_{\mathcal O}$. A continuous map

$$
R_{\mathcal D}^{\square_T}\longrightarrow A
$$

is equivalent, by (5.9), to a map from the unrestricted global ring and a map from $R_{\mathrm{loc}}$ whose composites from $R_{\mathrm{loc}}^{\square,\mathrm{unr}}$ agree. Translating through the representing bijections gives:

- a $T$-framed global lift;
- one allowed framed local lift at each $v\in T$;
- equality between each allowed local lift and the framed restriction of the global lift.

This is precisely (5.3). The universal property therefore proves both existence and uniqueness of the classifying map. No appeal to a geometric intersection of spectra is needed.

## 6. Pro-representability and universal global rings

A well-defined functor need not have a universal ring. The framed and unframed problems cross this gap for different reasons: matrices glue rigidly in the framed case, while the Schur condition controls hidden automorphisms in the unframed case. We now isolate these hypotheses from all later smoothness and dimension questions.

### 6.1 Global finiteness replaces finite generation

The representation-theoretic representability criterion requires finite-dimensional tangent spaces. For $G_{K,S}$ this follows from arithmetic finiteness: continuous cohomology with finite coefficients is finite when $S$ contains the coefficient-characteristic, ramified, and archimedean places. In particular,

$$
H^1(G_{K,S},\operatorname{ad}\bar\rho)
$$

and its trace-zero counterpart in the clean fixed-determinant case are finite-dimensional.

This is the global substitute for assuming that an arbitrary profinite group is topologically finitely generated. It also applies to every finite module appearing after restriction, duality, or scalar extension.

### 6.2 Framed representability

The fully framed global functor preserves coefficient fiber products exactly: a matrix over $A'\times_AA''$ is a compatible pair of matrices. Its residual value is one point, and its tangent space is finite. Therefore it is pro-representable by

$$
R_{K,S}^{\square}\in\operatorname{CNL}_{\mathcal O}.
$$

The same holds after fixing determinant, because determinant equality is a closed matrix equation. No vanishing of $H^2$ is needed. A nonzero obstruction group contributes possible equations to the universal ring; it does not prevent the ring from existing.

The $T$-framed functor is also pro-representable for every nonempty finite $T$. One can see this by choosing one place of $T$ as the global frame and adjoining one congruence matrix for every additional place. Exact matrix gluing and tangent finiteness again apply. Thus

$$
R_{K,S}^{\square_T}
$$

exists without a Schur hypothesis.

### 6.3 Unframed representability and scalar endomorphisms

For the unframed functor, equality of classes over a common coefficient quotient hides a comparison conjugator. Two choices differ by an automorphism of the common reduction. The Schur hypothesis makes every such automorphism scalar at every Artinian level. Scalars lift through coefficient surjections and act trivially by conjugation, which restores unique gluing.

**Global unframed representability theorem.** Assume

$$
\operatorname{End}_{k[G_{K,S}]}(\bar V)=k.
$$

Then the unrestricted unframed global functor and its fixed-determinant variant are pro-representable. Every closed representable system of local conditions therefore cuts out a universal unframed global ring $R_{\mathcal D}$.

Absolute irreducibility is a familiar sufficient hypothesis. If the centralizer is larger, the framed and partially framed rings still exist. The unframed functor may have a hull or may become representable after adding a stable line or another rigidification, but no coarse universal ring is inferred merely from finite $H^1$ or vanishing $H^2$.

### 6.4 Representability of the conditioned functor

The fiber product of represented functors is represented by the completed tensor product of their rings. Consequently (5.9) proves:

**Theorem 6.1.** Every global deformation datum with represented framed local conditions has a universal $T$-framed global ring $R_{\mathcal D}^{\square_T}$ for every nonempty framing set $T$ containing the local ring factors. If the datum is Schur and the conjugacy-invariant local conditions are closedly relatively representable after pullback to the global unframed problem, then the ordinary global functor is represented by $R_{\mathcal D}$. The framed quotient conditions of Section 4.1 have this property by the universal-representative pullback of Section 5.3. Representability of every local unframed functor is an alternative sufficient hypothesis that permits the literal fiber product (5.5), not a necessary one.

The determinant may be fixed or represented by a compatible variable-determinant condition. In the fixed case, the rings are obtained from their variable-determinant counterparts by the global determinant ideal, equivalently by the fiber over the chosen character. This ideal need not be principal. The local determinant ideals are restrictions of the same global requirement rather than independent incompatible constraints.

### 6.5 Universal representations

The universal framed ring supplies compatible matrix representations over all Artinian quotients

$$
R_{\mathcal D}^{\square_T}/\mathfrak m^n.
$$

Their inverse limit is a continuous representation

$$
\rho_{\mathcal D}^{\mathrm{univ}}:
G_{K,S}\longrightarrow
\operatorname{GL}_d(R_{\mathcal D}^{\square_T}).
\tag{6.1}
$$

Continuity follows because the kernels of its finite-level reductions form a neighborhood basis. Its local restrictions factor through the universal local conditions by (5.10).

For an unframed universal ring, compatible representatives can be chosen over the Artinian quotients under the Schur hypothesis. Their inverse limit is a representative of the universal strict-equivalence class, unique up to conjugation by a matrix congruent to the identity. Assertions depending only on characteristic polynomials, determinant, or strict-equivalence class are canonical.

### 6.6 Closedness and quotient maps

The inclusion $D_{\mathcal D}^{\square_T}\subseteq D_{K,S}^{\square_T}$ corresponds to a continuous local map

$$
R_{K,S}^{\square_T}\longrightarrow R_{\mathcal D}^{\square_T}.
$$

It is surjective. One way to see this is to use (5.9) and the quotient maps defining every local condition. Alternatively, injectivity on dual-number points makes the relative cotangent map surjective. Lifting cotangent generators then makes the image dense, and completeness together with the finite residue field makes the continuous image closed; hence the ring map is surjective. Thus the global local-condition locus is a closed formal subspace.

This conclusion does not say that the structural map $R_{\mathrm{loc}}\to R_{\mathcal D}^{\square_T}$ is surjective. It says that adding local equations to the unrestricted global problem gives a quotient of the unrestricted global ring.

## 7. Tangent spaces and Selmer conditions

First-order deformations translate nonlinear matrix equations into linear Galois cohomology. This translation is exact only if one distinguishes cocycles from cohomology classes and keeps the changes of local and global frames. The resulting Selmer group is the intrinsic tangent space; the extra invariant terms measure the chosen rigidifications.

### 7.1 The global cocycle calculation

Let $k[\varepsilon]=k[\varepsilon]/(\varepsilon^2)$. A first-order lift can be written uniquely as

$$
\rho_\varepsilon(g)
=(1+\varepsilon c(g))\bar\rho(g).
$$

Multiplicativity is equivalent to

$$
c(gh)=c(g)+g\cdot c(h).
$$

Thus framed first-order lifts are continuous cocycles. Conjugation by $1+\varepsilon X$ changes $c$ by the negative of $dX$, so unframed classes are cohomology classes.

For variable determinant, $c$ takes values in $M=\operatorname{ad}\bar\rho$. For fixed determinant with $\ell\nmid d$, it takes values in $M=\operatorname{ad}^0\bar\rho$. In the exceptional determinant case, it is trace zero but is still divided by coboundaries from the full adjoint, as in (2.3).

### 7.2 Local tangent subspaces and the Selmer kernel

For every $v\in S$, let

$$
L_v\subseteq H^1(K_v,M)
$$

be the tangent space of $\mathcal D_v$. Outside $S$, use the unramified subspace. The associated Selmer group is

$$
\boxed{
H^1_{\mathcal L}(K,M)
=\ker\left(
H^1(G_{K,S},M)
\longrightarrow
\bigoplus_{v\in S}H^1(K_v,M)/L_v
\right).}
\tag{7.1}
$$

The direct sum includes the archimedean places. At a complex place $L_v=0=H^1(K_v,M)$. At a real place degree one is ordinary cohomology, which equals modified degree one.

The unframed tangent theorem is now immediate.

**Theorem 7.1.** In the clean coefficient cases (2.5),

$$
t_{D_{\mathcal D}}\simeq H^1_{\mathcal L}(K,M).
\tag{7.2}
$$

**Proof.** A global first-order class belongs to the local condition at $v$ exactly when its localization lies in $L_v$. Taking all places simultaneously gives the kernel (7.1). Strict conjugation has already changed global cocycles into $H^1$. $\square$

The equality identifies a vector space, not merely its dimension. It also explains why local tangent spaces must be proved linear before they can define a Selmer structure.

### 7.3 The partially framed tangent quotient

The partially framed tangent retains both a global cocycle and infinitesimal comparison matrices. In the clean cases it has the explicit description

$$
t_{\mathcal D}^{\square_T}
\simeq
\frac{
\left\{(c,(X_v)_{v\in T}):
c\in Z^1(G_{K,S},M),\ [c]\in H^1_{\mathcal L}(K,M),
\ X_v\in A_{\mathrm{gauge}}\right\}}
{A_{\mathrm{gauge}}},
\tag{7.3}
$$

where a global infinitesimal change $X$ sends

$$
(c,(X_v))\longmapsto
(c-dX,(X_v-X)_v).
$$

The signs depend on the matrix convention but the quotient does not. Since $T$ is nonempty, this action has no stabilizer on the tuple: even a global invariant changes every comparison matrix. Taking dimensions gives

$$
\boxed{
\dim_k t_{\mathcal D}^{\square_T}
=h^1_{\mathcal L}(K,M)
+|T|d^2
-h^0(K,A_{\mathrm{gauge}}).}
\tag{7.4}
$$

For one framing place and a Schur representation, this adds $d^2-1$ variables. Every additional raw comparison frame adds $d^2$ variables. Fixing determinant does not reduce these framing variables because conjugation preserves determinant.

### 7.4 Local framed tangents

At $v\in T$, the framed tangent of the local condition is the inverse image of $L_v$ in the local cocycle space. Hence

$$
\boxed{
\dim_k t_v^{\square,\mathcal D_v}
=\dim_kL_v+d^2-h^0(K_v,A_{\mathrm{gauge}}).}
\tag{7.5}
$$

Indeed, in the variable-determinant case there is an exact sequence

$$
0\longrightarrow B^1(K_v,M)
\longrightarrow Z^1_{\mathcal D_v}(K_v,M)
\longrightarrow L_v
\longrightarrow0,
$$

and

$$
\dim_kB^1(K_v,M)
=d^2-h^0(K_v,A_{\mathrm{gauge}}).
$$

In the split fixed-determinant case, cocycles take values in $M=\operatorname{ad}^0\bar\rho$ but the image of all adjoint coboundaries equals the image of trace-zero coboundaries; the same dimension formula follows. This is the precise point where the hypothesis $\ell\nmid d$ enters (7.5).

This formula is a useful audit. For the finite-flat rank-two theorem of (4.5), $d=2$ and

$$
h^0(K_v,A_{\mathrm{gauge}})=h_v,
$$

so (7.5) becomes

$$
(f_v+h_v-1)+4-h_v=f_v+3,
$$

exactly the framed dimension in (4.6). The local centralizer cancels; it has not been ignored.

### 7.5 Relative tangents over the local base

The structural map $R_{\mathrm{loc}}\to R_{\mathcal D}^{\square_T}$ gives a transformation from the global $T$-framed functor to the product of local framed functors. A tangent vector relative to the closed point of $R_{\mathrm{loc}}$ is a global deformation whose locally framed restriction is trivial at every $v\in T$.

Define the $T$-strict Selmer group

$$
H^1_{\mathcal L,T}(K,M)
=\ker\left(
H^1_{\mathcal L}(K,M)
\longrightarrow
\bigoplus_{v\in T}H^1(K_v,M)
\right).
\tag{7.6}
$$

If $T$ does not contain every conditioned place, (7.6) means zero at places of $T$ and the original condition $L_v$ elsewhere.

There is a natural exact sequence

$$
\boxed{
0\longrightarrow
\frac{\displaystyle\bigoplus_{v\in T}
H^0(K_v,A_{\mathrm{gauge}})}
{H^0(K,A_{\mathrm{gauge}})}
\longrightarrow t_{\mathrm{rel},T}
\longrightarrow H^1_{\mathcal L,T}(K,M)
\longrightarrow0.}
\tag{7.7}
$$

The denominator maps diagonally by restriction. It is injective because $T$ is nonempty. To prove (7.7), let a strict Selmer class be represented by $c$. At every $v\in T$, its restriction is a coboundary $dX_v$, and the $X_v$ trivialize the local framed tangent. Replacing $c$ by $c-dX$ replaces every $X_v$ by $X_v-X$; this is exactly the infinitesimal simultaneous equivalence in (3.1), so the resulting relative tangent vector is unchanged. Once $c$ is fixed, two choices of $X_v$ differ by a local invariant. The stabilizers of the global representative are the global invariants, and they act diagonally on those local differences. This proves both surjectivity onto the strict Selmer group and the left-hand kernel in (7.7).

Consequently the minimal number of relative tangent generators is

$$
\boxed{
g_T=h^1_{\mathcal L,T}(K,M)
+\sum_{v\in T}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).}
\tag{7.8}
$$

Formula (7.8), rather than a bare strict Selmer dimension, is the correct framing count over $R_{\mathrm{loc}}$.

### 7.6 Tangent quotients and localization rank

Let

$$
Q_{\mathcal L}(M)
=\bigoplus_{v\in S}H^1(K_v,M)/L_v.
$$

The defining exact sequence is

$$
0\to H^1_{\mathcal L}(K,M)
\to H^1(G_{K,S},M)
\to Q_{\mathcal L}(M).
\tag{7.9}
$$

There is no zero at the right. The rank of localization determines how many local tangent quotients impose independent global first-order conditions. The dual Selmer group will measure the missing rank. Thus one must not count the dimensions of $H^1(K_v,M)/L_v$ as independent equations without a global duality argument.

### 7.7 The determinant complex in exceptional characteristic

Suppose $\ell\mid d$ and the determinant is fixed. The correct first-order complex begins in degree zero with the full gauge module and continues in positive degrees with trace-zero cochains:

$$
\mathcal C_\delta^0(G)=C^0(G,\operatorname{ad}\bar\rho),
\qquad
\mathcal C_\delta^i(G)=C^i(G,\operatorname{ad}^0\bar\rho)
\quad(i\geq1).
\tag{7.10}
$$

The ordinary differential sends degree zero into trace-zero degree one because trace is conjugation invariant. Then

$$
H^1(\mathcal C_\delta^\bullet(G))
=\frac{Z^1(G,\operatorname{ad}^0\bar\rho)}
{d(\operatorname{ad}\bar\rho)},
$$

which is (2.3), while the degree-two ambient obstruction still lies in $H^2(G,\operatorname{ad}^0\bar\rho)$.

Local conditions and Selmer kernels must be formed from these actual groups. The dual coefficient involves $\operatorname{ad}\bar\rho/kI_d$ by (2.4), and the global numerical identity is a hypercohomological version of Poitou--Tate. We will state all simplified trace-zero formulas under $\ell\nmid d$ and will not claim that (7.1)--(7.8) remain valid after merely replacing $M$ by $\operatorname{ad}^0$ in characteristic two.

## 8. Global and local obstruction theory

Tangent spaces say which infinitesimal directions begin, but not whether those directions continue through thicker coefficient rings. Obstruction theory records that failure. In a constrained global problem the obstruction has both a global degree-two component and a local compatibility component, so a mapping-fiber construction is unavoidable.

### 8.1 The ambient global obstruction

Let

$$
0\longrightarrow I\longrightarrow A'
\longrightarrow A\longrightarrow0
$$

be a small extension. Given a global lift $\rho_A$, choose continuous provisional matrix lifts to $A'$. Their multiplicative defect is a $2$-cocycle. In the variable-determinant problem it defines

$$
\operatorname{ob}_{\mathrm{glob}}(\rho_A,A'/A)
\in H^2(G_{K,S},\operatorname{ad}\bar\rho)\otimes_k I.
\tag{8.1}
$$

For fixed determinant, choose provisional lifts with determinant $\delta_{A'}$. Their defect is trace zero and gives

$$
\operatorname{ob}_{\mathrm{glob}}^\delta
\in H^2(G_{K,S},\operatorname{ad}^0\bar\rho)\otimes_k I.
\tag{8.2}
$$

These obstruction theories are complete for lifting the underlying global matrix representation: the class vanishes exactly when the provisional matrices can be corrected into a homomorphism. If it vanishes, framed lifts form a torsor under the appropriate cocycle space tensored with $I$, and infinitesimal automorphisms are governed by $H^0(G_{K,S},\operatorname{ad}\bar\rho)\otimes I$. In the variable and split fixed-determinant cases, rigidified unframed lifts form an $H^1(G_{K,S},M)\otimes I$-torsor. When $\ell\mid d$ and determinant is fixed, that torsor is instead governed by $H^1(\mathcal C_\delta^\bullet)\otimes I$, exactly as in (7.10).

### 8.2 Compatibility with localization

Restriction of provisional matrices to $G_{K_v}$ gives the provisional local lift, and its defect is the restriction of the global defect. Hence the square

$$
\begin{array}{ccc}
\{\text{global lifting problems}\}&\longrightarrow&H^2(G_{K,S},M)\otimes I\\
\downarrow&&\downarrow\operatorname{loc}_v\\
\{\text{local lifting problems}\}&\longrightarrow&H^2(K_v,M)\otimes I
\end{array}
$$

commutes. A global obstruction can vanish at every place without vanishing globally. Conversely, a nonzero local restriction proves that no global lift with the prescribed local behavior exists.

If local lifts over $A'$ are already supplied by a point of $R_{\mathrm{loc}}$, then every localized global obstruction is zero. The remaining global class lies in the kernel of localization in degree two. Even if that class vanishes, a chosen global lift may fail to agree with the supplied local lifts; their differences form degree-one local classes. This is why a relative obstruction theory is a mapping-cone theory rather than merely a kernel in $H^2$.

### 8.3 Two stages for a constrained lift

Consider first the absolute conditioned functor over $\mathcal O$. To lift a point of $D_{\mathcal D}(A)$ through $A'\to A$, one must solve two logically separate problems.

1. Lift the global representation. Its obstruction is (8.1) or (8.2).
2. Arrange that every local restriction belongs to $\mathcal D_v$. Even when the ambient local representation lifts, the local condition can have its own obstruction. If a conditioned local lift exists, the difference between it and the restriction of a chosen global lift is a local $H^1$ class; only its image modulo $L_v$ matters before framing.

Thus $H^2(G_{K,S},M)=0$ does not make an arbitrary conditioned global problem smooth. It removes only the first obstruction. Conversely, a local condition can be smooth even when the ambient local $H^2$ is nonzero, because the restricted obstruction map can vanish identically.

### 8.4 Relative obstruction complexes

The cleanest relation bound is obtained after putting all possibly singular local conditions into the base ring $R_{\mathrm{loc}}$. A relative small-extension problem then supplies the local conditioned lifts over $A'$ in advance. What remains is to globalize them.

At the linear level, replace the local tangent condition by zero at every $v\in T$ and retain $L_v$ at every $v\notin T$. Denote this modified structure by $\mathcal L_T^0$. A tangent subspace by itself does not determine a cochain-level quotient. Suppose for the moment that the local conditions outside $T$ come with compatible condition complexes whose first cohomology is $L_v$ and whose higher cohomology records their actual lifting obstructions. A deformation Selmer complex for the relative problem is then the mapping fiber of global cochains to the forbidden local quotient complexes. In the basic case where $T$ contains every finite conditioned place, its essential part is

$$
C_{\mathcal D,T}^\bullet(M)
=\operatorname{Cone}\left(
C^\bullet(G_{K,S},M)
\longrightarrow
\bigoplus_{v\in T}C^\bullet(K_v,M)
\oplus\text{the remaining local quotient complexes}
\right)[-1].
\tag{8.3}
$$

At real places the quotient complex uses the chosen local condition and the modified convention required for global duality. The raw representation deformation uses ordinary nonnegative cochains; the comparison with modified duality retains the corresponding archimedean correction rather than declaring the real terms zero.

The first cohomology of (8.3) has an exact sequence analogous to (7.7), with $M$-invariants. The difference between $M$ and the full gauge module contributes only formally smooth scalar-frame directions in the fixed-determinant split case. When the chosen local complexes are compatible with the actual small-extension lifting problems, its second cohomology is a complete receptacle for the relative obstruction: the localized degree-two defects and the degree-one mismatch of local lifts are the two adjacent pieces of the cone exact sequence.

To make those two pieces visible, let $Q_T^\bullet$ denote the direct sum of the local quotient complexes: the full local complex at $v\in T$ and the quotient by the chosen condition outside $T$. The cone sequence contains

$$
\begin{aligned}
H^1(G_{K,S},M)&\longrightarrow H^1(Q_T^\bullet)
\longrightarrow H^2(C_{\mathcal D,T}^\bullet(M))\\
&\longrightarrow H^2(G_{K,S},M)
\longrightarrow H^2(Q_T^\bullet).
\end{aligned}
\tag{8.3a}
$$

The cokernel of the first arrow measures locally prescribed first-order corrections that cannot be produced globally. The kernel of the last arrow measures global representation obstructions that disappear in every allowed local problem. The relative obstruction group is an extension of these contributions, not generally their direct sum. This exact sequence is the obstruction-theoretic analogue of the localization sequence (9.6).

### 8.5 What “cohomologically controlled” means

For a general local condition, a tangent subspace alone does not produce the quotient complex invoked in (8.3). We therefore make the extra hypothesis explicit.

A datum is **cohomologically controlled relative to $T$** if:

1. every local condition outside $T$ has a functorial complete obstruction theory compatible with its tangent $L_v$;
2. differences of local lifts form the expected $L_v$-torsors after rigidification;
3. these obstruction and torsor structures commute with coefficient pushout and with restriction of global cochains;
4. the resulting Selmer-complex obstruction is effective for minimal relations;
5. the chosen local condition complexes carry perfect local duality pairings with the complexes defining the exact orthogonals $L_v^\perp$, compatibly with the global Poitou--Tate pairing.

If $T$ contains every nontrivially obstructed local condition, the supplied points of $R_{\mathrm{loc}}$ remove the need to solve those local lifting problems again. For an unramified prime-to-$\ell$ condition, the usual unramified cochain complex has first cohomology $H^1_{\mathrm{ur}}$ and local Tate duality identifies its dual with the unramified complex for $M'$. For a rigid odd real condition, the condition complex has zero tangent and the modified real complex supplies the duality correction. These standard cases therefore satisfy the relevant compatibility directly. Any other condition, even if its representing ring happens to be smooth, must supply the cochain-level comparison and lifting theorem required above.

Under these hypotheses, vanishing of the class in

$$
H^2(C_{\mathcal D,T}^\bullet(M))\otimes_k I
$$

is equivalent to solving the relative global lifting problem. This is the complete obstruction space used in the presentation theorem.

Hypothesis 5, together with global Poitou--Tate duality, gives a perfect pairing

$$
H^2(C_{\mathcal D,T}^\bullet(M))
\times
H^1_{(\mathcal L_T^0)^\perp}(K,M')
\longrightarrow k.
\tag{8.3b}
$$

At a place of $T$, the primal condition in the relative fiber is strict, so the dual condition in (8.3b) is relaxed. Outside $T$, it is exactly $L_v^\perp$. The Tate twist in $M'$ and this strict/relaxed reversal are both forced by local duality. Under the completeness hypotheses, (8.3b) identifies the dimension of the chosen relative obstruction space with $q_T$ of (9.12). The module-level Poitou--Tate theorem of Chapter 9 always supplies the numerical identity for tangent subspaces; it supplies (8.3b) for deformation complexes only after the cochain-level compatibility in hypothesis 5 has been proved. Thus tangent orthogonals alone do not justify the relation bound.

### 8.6 Complete and minimal obstruction spaces

Let

$$
R_{\mathcal D}^{\square_T}
\simeq R_{\mathrm{loc}}[[x_1,\ldots,x_g]]/J
$$

be a minimal relative presentation, and let $\mathfrak n$ be the maximal ideal of the power-series source. The dual of

$$
J/\mathfrak nJ
$$

is the minimal relation obstruction space attached to that presentation. A complete effective obstruction theory $V$ gives an injection

$$
(J/\mathfrak nJ)^*\hookrightarrow V.
\tag{8.4}
$$

Consequently the number of minimal relations is at most $\dim_kV$.

There is generally no equality in (8.4). The cohomological space can contain classes never reached by a deformation obstruction, and several cohomology classes can encode dependent equations. Even if the dimensions happen to agree, identifying the spaces requires proving that the universal obstruction map is surjective and that no equation has redundant height.

It is therefore useful to reserve the words **complete obstruction space** for a space in which vanishing is sufficient for lifting, and **minimal obstruction space** for the dual relation space. Completeness concerns detection of lifting; minimality concerns the smallest equation count. Neither adjective implies the other without (8.4) and additional work.

### 8.7 Smoothness and degree-two cohomology

The safe implications are:

$$
H^2(G_{K,S},M)=0
\Longrightarrow
\text{the unrestricted global representation lifts across every small extension},
$$

and, for a represented cohomologically controlled problem,

$$
H^2(C_{\mathcal D,T}^\bullet(M))=0
\Longrightarrow
\text{relative formal smoothness over }R_{\mathrm{loc}}.
$$

Neither converse is valid. A nonzero cohomology group can carry an identically zero obstruction map. The finite-flat ring (4.6) is the decisive local example: at $\ell=3$ its ambient $H^2(K_v,\operatorname{ad}^0\bar\rho)$ can be nonzero, yet an explicit integral lifting theorem makes the finite-flat functor formally smooth.

Nor does ambient $H^2=0$ force a constrained integral condition to lift. The generic representation may lift while a required integral model does not. Smoothness is a property of the actual functorial lifting maps, not a synonym for the vanishing of a convenient ambient group.

### 8.8 Why an obstruction bound gives finitely many equations

The passage from obstruction classes to a ring presentation is worth making explicit. Let

$$
B=R_{\mathrm{loc}}[[x_1,\ldots,x_g]]
$$

and let $B\twoheadrightarrow R$ be a minimal relative presentation with kernel $J$. The square-zero layers of $B/J^2\to B/J$ exhibit the universal first-order failures to remove the equations represented by $J/\mathfrak nJ$, where $\mathfrak n$ is the maximal ideal of $B$. Evaluating a complete effective obstruction theory on these universal small extensions defines the injection (8.4). Effectiveness is the assertion that a nonzero minimal equation cannot have zero obstruction in every lifting problem.

Choose a basis of $J/\mathfrak nJ$ and lift it to $f_1,\ldots,f_r\in J$. The complete local form of Nakayama's lemma gives

$$
J=(f_1,\ldots,f_r),
$$

and (8.4) gives

$$
r=\dim_kJ/\mathfrak nJ\leq\dim_kV.
\tag{8.5}
$$

No statement about the height of $J$ follows from this argument. Even if $r=\dim_kV$, the sequence $f_1,\ldots,f_r$ need not be regular. The relation bound controls the minimal number of generators of an ideal; it is not yet a complete-intersection theorem.

## 9. Poitou--Tate duality and the numerical formula

Local tangent restrictions need not impose independent global equations. Reciprocity creates linear dependencies among them, and Poitou--Tate duality identifies those dependencies with a Selmer group for a Tate-twisted dual module. This chapter turns that duality into the exact dimension identity that controls the expected size of the universal ring.

### 9.1 The Tate-twisted dual coefficient

Let $M$ be as in (2.5). Its dual coefficient is

$$
M'=M^*(1)=\operatorname{Hom}_k(M,k)(1).
\tag{9.1}
$$

The twist is forced by local duality: evaluation followed by cup product must land in the local Brauer group. For the full adjoint, the trace pairing gives

$$
(\operatorname{ad}\bar\rho)^*(1)
\simeq\operatorname{ad}\bar\rho(1).
$$

For fixed determinant and $\ell\nmid d$, it restricts perfectly and gives

$$
(\operatorname{ad}^0\bar\rho)^*(1)
\simeq\operatorname{ad}^0\bar\rho(1).
\tag{9.2}
$$

The twist in (9.2) does not disappear because the untwisted trace-zero adjoint is self-dual. In characteristic dividing $d$, (2.4) replaces (9.2).

### 9.2 Orthogonal local conditions

Local Tate duality gives a perfect $k$-bilinear pairing

$$
H^1(K_v,M)\times H^1(K_v,M')\longrightarrow k
$$

using evaluation $M\otimes_kM^*\to k$, cup product, and the local invariant map for $k(1)$. Equivalently, one may first take the usual $\mathbf F_\ell$-valued invariant pairing and then use the coefficient-field trace to identify its $k$-linear adjoint. Either construction gives the same annihilator subspaces. Define

$$
L_v^\perp
=\{y\in H^1(K_v,M'):
\langle x,y\rangle_v=0\text{ for every }x\in L_v\}.
\tag{9.3}
$$

This is the exact orthogonal, not merely a subspace of complementary dimension. The resulting dual Selmer group is

$$
\boxed{
H^1_{\mathcal L^\perp}(K,M')
=\ker\left(
H^1(G_{K,S},M')
\longrightarrow
\bigoplus_{v\in S}H^1(K_v,M')/L_v^\perp
\right).}
\tag{9.4}
$$

At a prime-to-$\ell$ unramified place, the unramified conditions on $M$ and $M'$ are exact orthogonals. At a place above $\ell$, this need not be true. For a finite-flat tangent, the correct dual condition is the orthogonal by definition unless a separate integral theorem identifies it geometrically.

Strict and relaxed conditions are exchanged:

$$
0^\perp=H^1(K_v,M'),
\qquad
H^1(K_v,M)^\perp=0.
\tag{9.5}
$$

These identities determine the dual conditions that occur in a relative presentation over local rings.

### 9.3 The Selmer Poitou--Tate sequence

Put

$$
Q_{\mathcal L}(M)
=\bigoplus_{v\in S}H^1(K_v,M)/L_v.
$$

Poitou--Tate duality gives an exact sequence whose central part is

$$
\begin{aligned}
0\to{}&H^1_{\mathcal L}(K,M)
\to H^1(G_{K,S},M)
\to Q_{\mathcal L}(M)\\
\to{}&H^1_{\mathcal L^\perp}(K,M')^*
\to H^2(G_{K,S},M)
\to\bigoplus_{v\in S}\widetilde H^2(K_v,M).
\end{aligned}
\tag{9.6}
$$

Here the tilde denotes Tate modification at real places and zero at complex places. The map from $Q_{\mathcal L}(M)$ sends a local quotient class $(x_v)$ to the functional

$$
y\longmapsto
\sum_{v\in S}\langle x_v,\operatorname{loc}_v y\rangle_v.
\tag{9.7}
$$

Exactness makes the dual Selmer group the complete system of linear reciprocity tests on forbidden local directions. It does not identify the whole dual Selmer dual with the cokernel of global localization: the map to $H^2$ in (9.6) can be nonzero. The localization cokernel is the kernel of that map.

For the dimension calculation one also needs the tail

$$
H^2(G_{K,S},M)
\longrightarrow
\bigoplus_{v\in S}\widetilde H^2(K_v,M)
\longrightarrow
H^0(G_{K,S},M')^*
\longrightarrow0.
\tag{9.6a}
$$

The exact sequence is independent of auxiliary choices in the local pairing. Changing the additive identification of the local invariant group with $k$ rescales the pairings by units and leaves orthogonals, kernels, and dimensions unchanged.

This distinction mirrors the obstruction discussion. Dual Selmer supplies a natural complete cohomological receptacle. Its dimension need not be the minimal number of equations.

### 9.4 Derivation of the Wiles formula

Write

$$
h^i_{\mathcal L}(M)=\dim_kH^i_{\mathcal L}(K,M),
\qquad
l_v=\dim_kL_v,
\qquad
h_v^0(M)=\dim_kH^0(K_v,M).
$$

Taking alternating dimensions in the Selmer Poitou--Tate sequence, using local perfectness and the global Euler characteristic, gives

$$
\boxed{
\begin{aligned}
h^1_{\mathcal L}(M)
-h^1_{\mathcal L^\perp}(M')
={}&h^0(K,M)-h^0(K,M')\\
&+\sum_{v\in S}
\bigl(l_v-h_v^0(M)\bigr).
\end{aligned}}
\tag{9.8}
$$

Here is the calculation. Put

$$
Q=\sum_{v\in S}\bigl(h^1(K_v,M)-l_v\bigr).
$$

Alternating dimensions in (9.6) and (9.6a) gives

$$
\begin{aligned}
h^1_{\mathcal L}(M)-h^1_{\mathcal L^\perp}(M')
={}&h^1(K,M)-h^2(K,M)-Q\\
&+\sum_{v\in S}\widetilde h^2(K_v,M)-h^0(K,M').
\end{aligned}
\tag{9.8a}
$$

When there is no real $2$-primary exception, the global Euler-characteristic identity is

$$
h^0(K,M)-h^1(K,M)+h^2(K,M)
=\sum_{v\in S}
\left(
h^0(K_v,M)-h^1(K_v,M)+\widetilde h^2(K_v,M)
\right).
\tag{9.8b}
$$

For completeness, (9.8b) follows by devissage to finite coefficient modules. A finite place away from $\ell$ has local Euler characteristic zero in dimension notation, while a place $v\mid\ell$ contributes $-[K_v:\mathbf Q_\ell]\dim_kM$. Summing the latter degrees gives $-[K:\mathbf Q]\dim_kM$. A complex place restores $\dim_kM$, and a real place restores $h^0(K_v,M)$. The result is the global Euler characteristic.

If $\ell=2$ and real places occur, equation (9.8b) is not asserted for ordinary three-term cohomology. Instead one truncates the localization triangle in a high degree and cancels the global and complete real Tate complexes along their periodic tails. The remaining finite determinant has exactly the same real contribution $h^0(K_v,M)$ and produces the same low-degree identity below.

In the nonexceptional case, substitute (9.8b) into (9.8a); in the exceptional case, make the modified-determinant substitution just described. Expanding $Q$ and cancelling the local degree-one and degree-two terms gives exactly (9.8). This derivation fixes both the sign of $l_v$ and the sign of $h_v^0(M)$ without dividing by two.

Every term is necessary. At a complex place, $l_v=0$ while $h_v^0(M)=\dim M$. At a real place, the denominator uses ordinary invariants even in the $2$-primary theory. The proof in that case uses modified cohomology to cancel the periodic tail; it does not assert an ordinary three-term global Euler formula.

The sign can be checked from three basic conditions away from $\ell$. An unramified tangent contributes zero because $l_v=h_v^0(M)$. A strict condition contributes $-h_v^0(M)$. A relaxed condition contributes

$$
h^1(K_v,M)-h_v^0(M)=h_v^0(M')
$$

by the prime-to-$\ell$ local Euler formula. These checks fix both the local sign and the Tate twist.

### 9.5 The numerical defect

Define the **Selmer defect** of the datum by

$$
\boxed{
\Delta(\mathcal D)
=h^1_{\mathcal L}(K,M)
-h^1_{\mathcal L^\perp}(K,M').}
\tag{9.9}
$$

Formula (9.8) expresses it using only residual invariants and local tangent dimensions:

$$
\Delta(\mathcal D)
=h^0(K,M)-h^0(K,M')
+\sum_{v\in S}(l_v-h_v^0(M)).
\tag{9.10}
$$

The datum is called **balanced** when $\Delta(\mathcal D)=0$. Balanced means that the primal and dual Selmer groups have equal dimension. It does not mean that either group vanishes, nor that the universal ring is a complete intersection.

The number

$$
q(\mathcal D)=h^1_{\mathcal L^\perp}(K,M')
\tag{9.11}
$$

is the dual-Selmer dimension. Later auxiliary-prime arguments seek local directions whose pairing functionals span the dual of this group. The present theory supplies $q(\mathcal D)$ and the pairings; it does not choose those primes.

### 9.6 Strict conditions at the local base places

For a relative presentation over $R_{\mathrm{loc}}$, replace $L_v$ by zero at every $v\in T$. Denote the modified primal structure by $\mathcal L_T^0$. Its dual condition is relaxed at $T$ by (9.5) and remains $L_v^\perp$ outside $T$. Put

$$
q_T
=\dim_kH^1_{(\mathcal L_T^0)^\perp}(K,M').
\tag{9.12}
$$

Applying (9.8) to $\mathcal L_T^0$ gives

$$
\boxed{
\begin{aligned}
h^1_{\mathcal L,T}(K,M)-q_T
={}&h^0(K,M)-h^0(K,M')\\
&+\sum_{v\notin T}(l_v-h_v^0(M))
-\sum_{v\in T}h_v^0(M).
\end{aligned}}
\tag{9.13}
$$

The sums are over the controlling set, so the first includes archimedean places not placed in $R_{\mathrm{loc}}$. Formula (9.13) is the duality identity matched to the relative tangent formula (7.8).

### 9.7 Comparing two systems of local conditions

Suppose $L_v\subseteq L_v'$ at every place and equality holds almost everywhere. Then $L_v'^\perp\subseteq L_v^\perp$, and Poitou--Tate gives

$$
\begin{aligned}
0\to{}&H^1_{\mathcal L}(K,M)
\to H^1_{\mathcal L'}(K,M)
\to\bigoplus_vL_v'/L_v\\
\to{}&H^1_{\mathcal L^\perp}(K,M')^*
\to H^1_{\mathcal L'^\perp}(K,M')^*
\to0.
\end{aligned}
\tag{9.14}
$$

Therefore

$$
\begin{aligned}
&h^1_{\mathcal L'}-h^1_{\mathcal L}
+h^1_{\mathcal L^\perp}-h^1_{\mathcal L'^\perp}\\
&\hspace{35mm}=\sum_v(\dim L_v'-\dim L_v).
\end{aligned}
\tag{9.15}
$$

A one-dimensional local relaxation can increase the primal Selmer dimension, decrease the dual Selmer dimension, or split its effect between the two according to the localization map. It is never legitimate to increase the primal dimension automatically by the dimension of the local quotient.

## 10. Presentations over completed local deformation rings

The local rings already contain the geometry intrinsic to the chosen conditions. Presenting the global ring over their completed tensor product separates local equations from genuinely global equations. The relative tangent determines the number of variables, while a complete effective obstruction theory bounds the number of relations.

### 10.1 The local base ring

Let $T$ contain the finite places whose framed local condition rings will be used, and put

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in T,\mathcal O}
R_v^{\square,\mathcal D_v}.
$$

All factors are assumed complete Noetherian local, topologically of finite type over $\mathcal O$, and equipped with the same residue field $k$. Then $R_{\mathrm{loc}}$ is complete Noetherian local and (5.10) makes the global $T$-framed ring a complete local $R_{\mathrm{loc}}$-algebra.

Its relative tangent space is (7.7). Since that space is finite-dimensional, lifts of a dual basis of the relative cotangent space give a surjection

$$
R_{\mathrm{loc}}[[x_1,\ldots,x_{g_T}]]
\twoheadrightarrow R_{\mathcal D}^{\square_T},
\tag{10.1}
$$

where $g_T$ is exactly (7.8). This variable count requires only representability and complete local algebra; no obstruction hypothesis has yet been used.

### 10.2 The relative relation bound

Assume the datum is cohomologically controlled relative to $T$ in the sense of Section 8.5. Selmer-complex duality identifies the complete relative obstruction space with the dual of the relaxed-at-$T$ dual Selmer group, up to the harmless formally smooth scalar-frame summands already included in $g_T$. Effectiveness gives an injection from the dual minimal relation space into that obstruction space. Hence the kernel of (10.1) has at most $q_T$ minimal generators.

We obtain the main presentation theorem.

**Theorem 10.1 (relative presentation).** Under the preceding hypotheses there is an isomorphism

$$
\boxed{
R_{\mathcal D}^{\square_T}
\simeq
R_{\mathrm{loc}}[[x_1,\ldots,x_{g_T}]]
/(f_1,\ldots,f_{r_T}),}
\tag{10.2}
$$

where

$$
g_T=h^1_{\mathcal L,T}(K,M)
+\sum_{v\in T}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}),
\tag{10.3}
$$

and

$$
\boxed{r_T\leq q_T.}
\tag{10.4}
$$

The equations in (10.2) are not canonical. The inequality in (10.4) need not be an equality, and the height of the relation ideal can be smaller than $r_T$.

### 10.3 The fully expanded generator--relation defect

Combining (9.13), (10.3), and (10.4) gives

$$
g_T-r_T\geq g_T-q_T.
$$

The right side is

$$
\boxed{
\begin{aligned}
g_T-q_T
={}&h^0(K,M)-h^0(K,M')\\
&+\sum_{v\notin T}(l_v-h_v^0(M))
-\sum_{v\in T}h_v^0(M)\\
&+\sum_{v\in T}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).
\end{aligned}}
\tag{10.5}
$$

This is the complete bookkeeping formula. It displays global invariants, local invariants, every local tangent quotient through $l_v$, the framing correction, and all archimedean contributions among the places outside $T$.

In the fully variable-determinant case $A_{\mathrm{gauge}}=M=\operatorname{ad}\bar\rho$, the global and $T$-local $H^0(M)$ terms cancel, leaving

$$
\boxed{
g_T-q_T
=-h^0(K,M')
+\sum_{v\notin T}(l_v-h_v^0(M)).}
\tag{10.6}
$$

In the fixed-determinant case with $\ell\nmid d$, one has

$$
A_{\mathrm{gauge}}=kI_d\oplus M.
$$

Each local scalar line and the one global scalar line are invariant, so (10.5) becomes

$$
\boxed{
g_T-q_T
=|T|-1-h^0(K,M')
+\sum_{v\notin T}(l_v-h_v^0(M)).}
\tag{10.7}
$$

The term $|T|-1$ is the relative scalar-frame contribution. It would be lost by silently using $M=\operatorname{ad}^0$ as the gauge module.

### 10.4 Krull-dimension inequalities

Since quotienting a power-series ring by $r_T$ elements lowers dimension by at most $r_T$,

$$
\boxed{
\dim R_{\mathcal D}^{\square_T}
\geq\dim R_{\mathrm{loc}}+g_T-r_T
\geq\dim R_{\mathrm{loc}}+g_T-q_T.}
\tag{10.8}
$$

No equality is claimed. The first inequality can be strict because the equations can have dependent height. The second can be strict because the cohomological obstruction space can be larger than the minimal relation space.

If $\mathcal O$ is a complete discrete valuation ring and every local factor is nonzero and flat over $\mathcal O$, then

$$
\dim R_{\mathrm{loc}}
=1+\sum_{v\in T}
(\dim R_v^{\square,\mathcal D_v}-1).
\tag{10.9}
$$

Without flatness, (10.9) is not valid. The completed tensor product still has the presentation supplied by the local factors, but coefficient torsion can change its dimension.

### 10.5 Absolute presentations over the coefficient ring

Suppose the unframed global datum is Schur and cohomologically controlled at every local condition. Taking no local ring as a base gives a minimal presentation

$$
\boxed{
R_{\mathcal D}
\simeq
\mathcal O[[x_1,\ldots,x_h]]/(f_1,\ldots,f_r),}
\tag{10.10}
$$

with

$$
h=h^1_{\mathcal L}(K,M),
\qquad
r\leq h^1_{\mathcal L^\perp}(K,M').
\tag{10.11}
$$

Consequently

$$
\dim R_{\mathcal D}
\geq\dim\mathcal O+\Delta(\mathcal D).
\tag{10.12}
$$

This clean absolute bound includes local singularities only when their obstruction theories are part of the controlled Selmer complex. If a local condition is known merely to be representable by a possibly singular quotient, one should instead put its entire local ring into $R_{\mathrm{loc}}$ and use Theorem 10.1. Representability alone does not justify (10.11).

### 10.6 Formal smoothness and local factors

If the relative obstruction maps all vanish, then the structural map

$$
R_{\mathrm{loc}}\longrightarrow R_{\mathcal D}^{\square_T}
$$

is formally smooth. With relative tangent dimension $g_T$, complete local algebra gives a noncanonical isomorphism

$$
R_{\mathcal D}^{\square_T}
\simeq R_{\mathrm{loc}}[[x_1,\ldots,x_{g_T}]].
\tag{10.13}
$$

This conclusion requires actual formal smoothness, not merely $q_T=0$ unless the obstruction theory has been proved complete. Conversely, (10.13) can hold while the cohomological space used to contain obstructions is nonzero, if its actual obstruction map is zero.

### 10.7 The direction of every comparison map

The principal arrows can now be summarized without ambiguity:

$$
\begin{array}{c|c}
\text{operation on functors}&\text{operation on rings}\\ \hline
\text{restrict global lifts locally}&R_{\mathrm{loc}}^{\mathrm{unr}}\to R_{K,S}^{\square_T}\\
\text{impose a local condition}&R_v^{\square}\twoheadrightarrow R_v^{\square,\mathcal D_v}\\
\text{impose all global local conditions}&R_{K,S}^{\square_T}\twoheadrightarrow R_{\mathcal D}^{\square_T}\\
\text{view the global ring over allowed local rings}&R_{\mathrm{loc}}\to R_{\mathcal D}^{\square_T}\\
\text{strengthen a global condition}&R_{\mathrm{weaker}}\to R_{\mathrm{stronger}}.
\end{array}
\tag{10.14}
$$

The last map is a quotient when the stronger condition is closed. A larger deformation functor has a ring mapping to the ring of the smaller functor.

## 11. Balanced odd deformation problems over totally real fields

The abstract defect formula becomes useful only after its local terms have been evaluated. In rank two over a totally real field, odd real places contribute negatively and low-weight finite-flat places contribute positively. Their cancellation explains the balanced deformation problems that are central to modularity lifting.

### 11.1 Why the totally real calculation matters

Two-dimensional modularity lifting over a totally real field uses a fixed determinant, minimal conditions away from $\ell$, and a low-weight integral condition above $\ell$. The local tangent contributions at the $\ell$-adic places must exactly compensate for the real-place contributions. This cancellation is the arithmetic reason the resulting deformation problem is balanced.

We now perform the calculation with every hypothesis visible. Let $K$ be totally real of degree

$$
n=[K:\mathbf Q].
$$

Let $d=2$, let $\ell$ be odd, fix a determinant $\delta$, and assume $\bar\rho$ is globally Schur. Put

$$
M=\operatorname{ad}^0\bar\rho,
\qquad M'=M(1).
$$

Global Schur gives

$$
h^0(K,M)=0.
\tag{11.1}
$$

We separately assume the absence of a global trace-zero cyclotomic self-twist:

$$
h^0(K,M(1))=0.
\tag{11.2}
$$

Condition (11.2) is not a consequence of Schur's lemma alone.

### 11.2 Oddness at real places

The representation is **odd** if, for every real place $v$,

$$
\det\bar\rho(c_v)=-1.
\tag{11.3}
$$

Because $\ell$ is odd, $c_v^2=1$ and (11.3) give a decomposition of $\bar V$ into one $+1$ and one $-1$ eigenspace. Conjugation on $M$ fixes the trace-zero diagonal line and negates the two off-diagonal lines. Therefore

$$
h^0(K_v,M)=1,
\qquad H^1(K_v,M)=0,
\qquad L_v=0.
\tag{11.4}
$$

Each real place contributes

$$
l_v-h_v^0(M)=-1.
\tag{11.5}
$$

Summing over all real places gives $-n$. The sign comes from ordinary $H^0$ and cannot be omitted merely because real $H^1$ vanishes.

The lifted determinant must satisfy $\delta(c_v)=-1$. Since $2$ is invertible, the projectors $(1\pm\rho(c_v))/2$ show that the ranks of the two eigenspaces remain one in every lift. Thus the odd local conjugacy class is formally rigid in the unframed problem.

### 11.3 Minimal places away from the coefficient prime

At a finite place $v\nmid\ell$, take an unramified or fixed prime-to-$\ell$ minimal condition whenever the residual shape permits it. Then

$$
l_v=h_v^0(M)
\tag{11.6}
$$

and the local contribution to (9.10) is zero. A minimal special condition with existing rank-one monodromy has the analogous neutral tangent count in the standard nonexceptional case only after its actual local equations have proved it. We do not assign neutrality solely from the word “minimal.”

For the balanced calculation below, we therefore impose the exact numerical hypothesis

$$
\dim_kL_v=h^0(K_v,M)
\qquad(v\nmid\ell,\ v\text{ finite}).
\tag{11.6a}
$$

The unramified and fixed prime-to-$\ell$ type conditions above satisfy (11.6a). A special condition is included only after its own tangent calculation proves the same equality.

### 11.4 Finite-flat coefficient-prime places

Assume every completion $K_v$ for $v\mid\ell$ is unramified over $\mathbf Q_\ell$, and impose the rank-two finite-flat condition with fixed cyclotomic determinant in the range of (4.5). Let

$$
f_v=[K_v:\mathbf Q_\ell],
\qquad
h_v=\dim_k\operatorname{End}_{k[G_{K_v}]}(\bar V).
$$

Since $\ell$ is odd,

$$
h^0(K_v,M)=h_v-1.
$$

Formula (4.5) gives

$$
l_v=f_v+h_v-1,
$$

and therefore

$$
\boxed{l_v-h_v^0(M)=f_v.}
\tag{11.7}
$$

This calculation remains true at a split local residual point with $h_v=2$, even though a coarse unframed local universal ring is not available: the framed local ring exists, and both sides of (11.7) increase by one. Summing over $v\mid\ell$ gives

$$
\sum_{v\mid\ell}f_v=[K:\mathbf Q]=n.
\tag{11.8}
$$

The $\ell$-adic contribution $+n$ cancels the real contribution $-n$.

### 11.5 The balanced conclusion

Under (11.1)--(11.8), including the explicit neutrality hypothesis (11.6a), every finite place away from $\ell$ contributes zero, the places above $\ell$ contribute $+n$, and the real places contribute $-n$. Formula (9.10) becomes

$$
\Delta(\mathcal D)
=-h^0(K,M(1)).
\tag{11.9}
$$

Under (11.2),

$$
\boxed{\Delta(\mathcal D)=0.}
\tag{11.10}
$$

Thus the fixed-determinant odd finite-flat minimal problem is balanced. Equivalently,

$$
h^1_{\mathcal L}(K,M)
=h^1_{\mathcal L^\perp}(K,M(1)).
$$

This equality is the numerical input later used to choose the number of auxiliary directions. It does not say that either Selmer group is zero. If (11.2) fails, the defect is negative by the dimension of the global cyclotomic self-twist space.

### 11.6 What changes at coefficient prime two

At $\ell=2$, all three ingredients of the preceding cancellation require replacement.

First, $-1=1$ in $k$, so the residual determinant cannot distinguish odd and even complex conjugation. A characteristic-zero condition $\delta(c_v)=-1$ can still be imposed, but it is not determined by the residual determinant.

Second, one cannot form the projectors $(1\pm c_v)/2$. The residual $C_2$-representation can be nonsemisimple, real $H^1$ can be nonzero, and ordinary cohomology has a periodic tail. The real local condition and its tangent must be specified explicitly, and Poitou--Tate must use modified real cohomology.

Third, for $d=2$ the scalar line lies inside $\operatorname{ad}^0$. The fixed-determinant tangent is (2.3), its dual uses (2.4), and the trace-zero Wiles formula (9.8) cannot be used by formal substitution. The low-weight finite-flat power-series theorem (4.5)--(4.6) also assumes $\ell>2$.

There can be valid $2$-adic deformation problems, but their balanced defect must be recomputed from the trace-kernel complex, the chosen real local conditions, and the actual integral local theorem. No division by two and no odd-prime cancellation is implicit.

## 12. Three consistency tests

Long cohomological formulas are especially vulnerable to a reversed arrow, a missing scalar, or an incorrect local sign. The three tests below isolate those failure modes. Together they check the relative framing count, the totally real Euler cancellation, and the distinction between a smooth local factor and a numerically trivial one.

### 12.1 A one-place unrestricted problem

The first test isolates variance and relative tangents. Suppose one local place $v$ is in $T$ and its condition is unrestricted. Then

$$
L_v=H^1(K_v,M),
\qquad L_v^\perp=0.
$$

The local condition ring equals the unrestricted local ring, so the fiber product (5.9) imposes no new quotient at $v$. The structural ring map still records restriction:

$$
R_v^{\square}\longrightarrow R_{K,S}^{\square_{\{v\}}}.
$$

The relative tangent is not the global Selmer group with a relaxed local condition. It is the kernel of the locally framed restriction. Formula (7.7) gives

$$
g_{\{v\}}
=\dim\ker\bigl(H^1_{\mathcal L}(K,M)\to H^1(K_v,M)\bigr)
+h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).
\tag{12.1}
$$

Here $\mathcal L$ retains every condition away from $v$ and is relaxed at $v$. If there are no other conditions, its global term is the full $H^1(G_{K,S},M)$.

If the “global” group is replaced as a toy model by the same local group and restriction is the identity, both terms in (12.1) vanish: the strict kernel is zero and the local and global centralizers agree. The global ring over the one local base has no relative variables. This test detects both a reversed ring map and an omitted $H^0$ correction.

The dual condition for the strict relative tangent is relaxed, not zero. A resulting dual-Selmer relation bound can be nonminimal in more general arithmetic settings; the toy identity case reminds us why the bound is never asserted as an equality.

### 12.2 A fixed-determinant Schur representation over a totally real field

Take the situation of Chapter 11. Globally,

$$
h^0(K,A_{\mathrm{gauge}})=1,
\qquad h^0(K,M)=0.
$$

At every real place, $h_v^0(M)=1$ and $l_v=0$. At every finite-flat place above $\ell$, (11.7) contributes the local degree. The degree sum equals the number of real embeddings. Hence (9.10) gives zero defect when $h^0(K,M(1))=0$.

For a relative presentation with a finite framing set $T$, formula (10.7) reads

$$
g_T-q_T
=|T|-1-h^0(K,M(1))
+\sum_{v\notin T}(l_v-h_v^0(M)).
$$

If $T$ contains all finite conditioned places, the remaining sum contains the $n$ real terms and equals $-n$. Thus

$$
g_T-q_T=|T|-1-n
$$

under the no-self-twist hypothesis. This is a relative statement over the large local base and is not the same number as the absolute balanced defect $0$. Confusing them would double-count the finite local tangent dimensions already built into $R_{\mathrm{loc}}$.

There is a second check when $\mathcal O$ is a discrete valuation ring, every finite local factor is formally smooth, and the complete-effectiveness hypotheses of the relative presentation theorem hold. Let $m=|T|$. A neutral fixed-determinant rank-two factor away from $\ell$ has framed relative dimension

$$
h_v^0(M)+4-h_v^0(\operatorname{ad}\bar\rho)=3,
$$

while a finite-flat factor above $\ell$ has relative dimension $f_v+3$. Hence

$$
\dim R_{\mathrm{loc}}=1+3m+n.
$$

Adding the relative lower bound $g_T-q_T=m-1-n$ gives

$$
\dim R_{\mathcal D}^{\square_T}\geq4m.
$$

Under the corresponding absolute obstruction hypotheses, the unframed balanced bound is $\dim R_{\mathcal D}\geq1$, and adding $m$ partial frames contributes $4m-1$ dimensions by (7.4), again giving $4m$. Thus the absolute and relative calculations agree exactly once the local factors, real signs, and single global scalar have each been counted once.

### 12.3 A formally smooth finite-flat place

Let $v\mid\ell$ satisfy the unramified odd rank-two hypotheses of (4.5). The local coarse tangent dimension is

$$
l_v=f_v+h_v-1,
$$

while the local gauge centralizer dimension is $h_v$. Formula (7.5) gives

$$
l_v+4-h_v=f_v+3.
$$

This agrees with the formally smooth ring

$$
R_v^{\square,\mathrm{fl},\chi_\ell}
\simeq\mathcal O[[z_1,\ldots,z_{f_v+3}]].
$$

Placing this factor in $R_{\mathrm{loc}}$ absorbs all its $f_v+3$ parameters and contributes no relative local equation. Its contribution to the absolute Wiles formula is nevertheless

$$
l_v-h_v^0(M)=f_v.
$$

Thus “formally smooth local factor” does not mean “numerically invisible.” It means that its geometry lies in the base ring rather than in the relative relation ideal.

This example also tests obstruction language. The ambient local $H^2$ can be nonzero at $\ell=3$, but the finite-flat local factor is smooth because its actual obstruction map vanishes. Any theorem that required ambient $H^2=0$ would incorrectly exclude this valid local input.

## 13. Changing the deformation datum

The notation $R_{\mathcal D}$ can suggest that a global deformation problem is a rigidly packaged object. In practice one constantly changes its packaging: a place is added to the controlling set, a local condition is strengthened, a frame is introduced, or a determinant is specialized. These operations are harmless only after their functorial direction has been identified. This chapter records the comparison maps and explains which numerical invariants really change.

### 13.1 Enlarging the ramification set

Let $S'=S\cup\{w\}$, where $w$ is a finite place not in $S$. Assume that $\bar\rho$ and the determinant data are unramified at $w$. The natural quotient

$$
G_{K,S'}\twoheadrightarrow G_{K,S}
\tag{13.1}
$$

allows every representation of $G_{K,S}$ to be inflated to $G_{K,S'}$. Conversely, a representation of $G_{K,S'}$ factors through $G_{K,S}$ precisely when its inertia group at $w$, and hence every conjugate of that inertia group, acts trivially. Thus if the new datum $\mathcal D'$ imposes the exact unramified condition at $w$, inflation gives a natural isomorphism

$$
D_{\mathcal D}\xrightarrow{\sim}D_{\mathcal D'}.
\tag{13.2}
$$

The representing rings are canonically isomorphic:

$$
R_{\mathcal D'}\xrightarrow{\sim}R_{\mathcal D}.
\tag{13.3}
$$

The displayed direction is the one obtained directly from (13.2); of course an isomorphism also has an inverse. The same assertion holds with compatible partial frames.

The word *exact* matters. Requiring merely that the tangent class be unramified does not force every Artinian lift to kill inertia. Nor is every condition customarily called minimal literally the unramified condition. If a condition permits nontrivial ramification invisible at first order, then (13.2) fails even though the two tangent spaces may agree.

The Selmer groups associated with the two descriptions agree. One way to see this is to compare first-order lifts through the functorial isomorphism (13.2). Cohomologically, inflation--restriction and the unramified local condition cancel the additional inertia term. The same cancellation holds in the dual Selmer structure because the unramified subspaces are exact orthogonals at $w$. Consequently the Wiles defect is independent of this harmless enlargement of $S$.

A place can be removed by reversing this argument only if every allowed lift is genuinely unramified there and no determinant or auxiliary local datum still depends on it. Removing a place merely because its tangent contribution $l_w-h_w^0(M)$ is zero is not justified.

### 13.2 Strengthening and weakening a local condition

Suppose two data agree except at $w$, where there is a base-change-stable closed inclusion

$$
D_w^{\square,\mathcal D_w^+}
\longrightarrow
D_w^{\square,\mathcal D_w^-}.
\tag{13.4}
$$

We call $\mathcal D_w^+$ the stronger condition. The induced inclusion of global functors points in the same direction,

$$
D_{\mathcal D^+}^{\square_T}
\longrightarrow
D_{\mathcal D^-}^{\square_T},
$$

whereas the ring map points oppositely:

$$
R_{\mathcal D^-}^{\square_T}
\longrightarrow
R_{\mathcal D^+}^{\square_T}.
\tag{13.5}
$$

Because (13.4) is closed, (13.5) is a quotient. If $w\in T$, the entire comparison is a base change. There is a Cartesian square of functors and hence an isomorphism

$$
R_{\mathcal D^+}^{\square_T}
\simeq
R_{\mathcal D^-}^{\square_T}
\widehat\otimes_{R_w^{\square,\mathcal D_w^-}}
R_w^{\square,\mathcal D_w^+}.
\tag{13.6}
$$

Both maps under the completed tensor product begin at the ring for the weaker local condition. Formula (13.6) also shows why strengthening a condition can never produce a map in the reverse direction unless extra structure supplies one.

Let $L_w^+\subseteq L_w^-$ be the associated tangent subspaces, and set

$$
U_w=L_w^-/L_w^+.
$$

Specializing (9.14) gives

$$
\begin{aligned}
0\to{}&H^1_{\mathcal L^+}(K,M)
\to H^1_{\mathcal L^-}(K,M)
\to U_w\\
\to{}&H^1_{(\mathcal L^+)^\perp}(K,M')^*
\to H^1_{(\mathcal L^-)^\perp}(K,M')^*
\to0.
\end{aligned}
\tag{13.7}
$$

The middle arrow sends a global deformation to its newly permitted local direction. Its image need not be all of $U_w$. The missing local directions are detected by the dual Selmer group. Taking dimensions yields

$$
\begin{aligned}
&h^1_{\mathcal L^-}(M)-h^1_{\mathcal L^+}(M)\\
&\quad+
h^1_{(\mathcal L^+)^\perp}(M')
-h^1_{(\mathcal L^-)^\perp}(M')
=\dim_kU_w.
\end{aligned}
\tag{13.8}
$$

Equivalently, weakening the condition changes the defect by the full local dimension:

$$
\Delta(\mathcal D^-)-\Delta(\mathcal D^+)
=\dim_kU_w.
\tag{13.9}
$$

This is compatible with (9.10), but (13.7) says more: it describes how that change is divided between new global tangent directions and eliminated dual constraints.

### 13.3 Strict, unramified, and relaxed replacements

Three extreme replacements occur often. At a place $w$, the strict tangent is $0$, the original tangent is $L_w$, and the relaxed tangent is $H^1(K_w,M)$. Their duals occur in reverse order:

$$
0
\subseteq L_w
\subseteq H^1(K_w,M),
$$

$$
0
\subseteq L_w^\perp
\subseteq H^1(K_w,M').
\tag{13.10}
$$

Here the dual of strict is relaxed and the dual of relaxed is strict. An unramified condition at a prime away from $\ell$ is self-corresponding only in the sense that the unramified subspace for $M$ is orthogonal to the unramified subspace for $M'$. It is not generally a Lagrangian subspace of a single cohomology group unless an additional self-duality has been chosen.

Replacing $L_w$ by the relaxed condition increases the numerical defect by

$$
h^1(K_w,M)-l_w,
\tag{13.11}
$$

while replacing it by the strict condition decreases the defect by $l_w$. These are statements about the *difference* of Selmer dimensions. The primal dimension alone changes by the rank of an actual localization map, as (13.7) shows.

The unramified condition also illustrates why one should distinguish a condition from its tangent space. At a prime away from $\ell$, the functor of representations with trivial inertia is a nonlinear condition defined at every Artinian level. Its tangent is the kernel of restriction to inertia. The latter linear subspace is enough for the Wiles formula, but only the former defines the quotient ring.

### 13.4 Replacing a local factor by a formally smooth one

Suppose there is a transformation of framed local conditions

$$
D_w^{\square,1}\longrightarrow D_w^{\square,0}
$$

represented by a formally smooth map

$$
R_w^{\square,0}\longrightarrow R_w^{\square,1}
$$

of relative dimension $s$. Noncanonically,

$$
R_w^{\square,1}
\simeq R_w^{\square,0}[[y_1,\ldots,y_s]].
\tag{13.12}
$$

If the global comparison is the Cartesian base change at $w$, then

$$
R_{\mathcal D^1}^{\square_T}
\simeq
R_{\mathcal D^0}^{\square_T}
\widehat\otimes_{R_w^{\square,0}}
R_w^{\square,1},
\tag{13.13}
$$

and the induced global map is formally smooth of relative dimension $s$. This conclusion uses the formal smoothness of the *map* of local conditions. It is stronger than saying that both local rings happen to be formally smooth over $\mathcal O$.

If instead a local ring $R_w^{\square,\mathcal D_w}$ is formally smooth over $\mathcal O$ and is simply included as a factor of $R_{\mathrm{loc}}$, then it contributes its full dimension to the base. It contributes no local equations, but it still changes the absolute defect through $l_w-h_w^0(M)$. The finite-flat factor of Section 12.3 is the model example.

Formal smoothness is stable under completed base change in the present Noetherian complete-local category. Flatness and relative dimension must nevertheless be checked if one translates (13.13) into a Krull-dimension equality. The existence of the completed tensor product alone gives no dimension formula.

### 13.5 Adding and forgetting frames

Let $\varnothing\neq T\subseteq T'$. Forgetting the frames at $T'\setminus T$ gives

$$
D_{\mathcal D}^{\square_{T'}}
\longrightarrow D_{\mathcal D}^{\square_T}
$$

and hence a ring map

$$
R_{\mathcal D}^{\square_T}
\longrightarrow R_{\mathcal D}^{\square_{T'}}.
\tag{13.14}
$$

Once one frame is already present, each new comparison frame is an independent element of the formal completion of $\operatorname{GL}_d$ at the identity. Therefore (13.14) is formally smooth of relative dimension

$$
|T'\setminus T|d^2,
$$

and noncanonically

$$
R_{\mathcal D}^{\square_{T'}}
\simeq
R_{\mathcal D}^{\square_T}
[[z_1,\ldots,z_{|T'\setminus T|d^2}]].
\tag{13.15}
$$

If the starting point is the unframed Schur problem, the first frame contributes

$$
d^2-h^0(K,A_{\mathrm{gauge}})=d^2-1
\tag{13.16}
$$

variables, not $d^2$. The missing scalar is the infinitesimal global automorphism acting trivially by conjugation. Every later frame contributes $d^2$ because the first frame has already killed the simultaneous change-of-basis freedom. Formulas (13.15)--(13.16) recover the absolute tangent count (7.4).

These statements concern frames on the same global condition. Enlarging $T$ in the definition of $R_{\mathrm{loc}}$ is a different operation: it moves a local deformation ring into the base and changes the strict Selmer structure used for relative generators. The change in $g_T$ is then governed by (7.7), not by adding $d^2$ blindly.

### 13.6 Specializing the determinant

Assume the variable-determinant deformation functor is represented and that taking determinant defines a natural transformation to a representable character-deformation functor $D_{\det}$. Let $R_{\det}$ be its ring. A chosen determinant $\delta$ gives a point

$$
R_{\det}\longrightarrow\mathcal O.
$$

The fixed-determinant functor is the fiber over that point. Thus, with all local determinant conditions transported compatibly,

$$
R_{\mathcal D,\delta}
\simeq
R_{\mathcal D,\mathrm{var}}
\widehat\otimes_{R_{\det}}\mathcal O.
\tag{13.17}
$$

The two maps under the tensor product both start at $R_{\det}$. At first order, (13.17) takes the kernel of the trace map on cocycles. When $\ell\nmid d$, the scalar/trace-zero splitting turns this into the familiar passage from $\operatorname{ad}$ to $\operatorname{ad}^0$. When $\ell\mid d$, the fiber still exists, but its tangent is the trace-kernel quotient (2.3); (13.17) does not manufacture a splitting that the residual module lacks.

A determinant specialization may be non-flat. It can introduce new equations or coefficient torsion, so its effect on Krull dimension is not determined by tangent codimension alone. This is one more reason to retain the determinant constraint as part of the datum rather than suppress it from the notation.

## 14. Coefficient changes and natural operations

Global deformation rings should behave naturally when the coefficient field or the residual representation is changed in a controlled way. Some operations are genuine equivalences and preserve every numerical invariant. Others merely give comparison maps and can enlarge the adjoint module. The difference is most transparent at the level of functors.

### 14.1 Extension of coefficient rings

Let $\mathcal O\to\mathcal O'$ be a continuous flat local map of complete Noetherian local rings that is topologically of finite type, with finite residue extension $k\to k'$. Put

$$
\bar\rho'=\bar\rho\otimes_k k'.
$$

Assume that all local conditions are preserved by scalar extension and that the relevant Schur and representability hypotheses remain true after extending $k$. Extending the universal family over $R_{\mathcal D}$ gives a natural transformation from the functor represented by

$$
R_{\mathcal D}\widehat\otimes_{\mathcal O}\mathcal O'
$$

to the intrinsic deformation functor $D_{\mathcal D'}$ of $\bar\rho'$. By Yoneda, the direction on representing rings is

$$
\boxed{
R_{\mathcal D'}
\longrightarrow
R_{\mathcal D}\widehat\otimes_{\mathcal O}\mathcal O'.}
\tag{14.1}
$$

If a more general tensor product has several closed points, the target in (14.1) means its completion at the point corresponding to $\bar\rho'$. In the usual extension of discrete valuation coefficient rings, that point is specified by the chosen embedding of residue fields.

The map (14.1) is an isomorphism in either of two precise situations. First, if the residue field is unchanged and $\mathcal D'$ is merely the same functor restricted to $\mathcal O'$-algebras, completed base change has the asserted universal property. Second, for a genuine residue extension, one may have a separate effective scalar-extension theorem saying that, for every Artinian local $\mathcal O'$-algebra, specialization of the old universal family gives a bijection onto $D_{\mathcal D'}$. Under that stronger hypothesis, Yoneda gives

$$
R_{\mathcal D'}
\simeq
R_{\mathcal D}\widehat\otimes_{\mathcal O}\mathcal O'.
\tag{14.1a}
$$

Preservation of the local conditions proves only that the natural transformation exists. It does not prove its surjectivity: after enlarging the residual field, a deformation of $\bar\rho'$ need not descend to the old coefficient field. Thus (14.1a) must not be inferred from flatness and local compatibility alone.

Continuous cochain complexes with finite-dimensional residual coefficients commute with the finite scalar extension. Hence

$$
H^i(G,M\otimes_k k')
\simeq H^i(G,M)\otimes_k k',
\tag{14.2}
$$

and similarly for local cohomology, Selmer groups, and dual Selmer groups, provided the local tangent subspaces base change. Their dimensions over the new residue field equal the old dimensions over $k$, so the numerical defect is unchanged. If the complete effective obstruction complexes also commute with scalar extension, the presentation theorem gives the same numerical generator--relation bounds for $\mathcal D'$. Tangent-space base change alone does not transport the obstruction bound.

The finite field extension $k'/k$ in (14.2) is flat, and that flatness is doing real work in the cohomology calculation. For a non-flat coefficient quotient, tensor product can create torsion and higher derived terms. A quotient may still represent the intended specialized problem, but (14.2), dimension preservation, and flat local-factor formulas must be proved anew. Likewise, a local condition defined through an integral model does not automatically commute with a change of coefficient field; base-change stability is part of the hypothesis, while effective descent is the additional input required for (14.1a).

### 14.2 Twisting by a fixed character

Let

$$
\chi:G_{K,S}\longrightarrow\mathcal O^\times
$$

be a fixed continuous character. Twisting gives

$$
\rho_A\longmapsto\rho_A\otimes\chi_A.
\tag{14.3}
$$

If every local condition is transported by (14.3), this is an equivalence between the deformation problem for $\bar\rho$ and the transported problem for $\bar\rho\otimes\bar\chi$. Its inverse is twisting by $\chi^{-1}$. Consequently the two universal rings are canonically isomorphic.

The determinant changes by

$$
\det(\rho_A\otimes\chi_A)
=\det(\rho_A)\chi_A^d.
\tag{14.4}
$$

Thus a fixed determinant $\delta$ is transported to $\delta\chi^d$. The adjoint module does not change:

$$
\operatorname{ad}(\bar\rho\otimes\bar\chi)
\simeq\operatorname{ad}\bar\rho,
\tag{14.5}
$$

because the scalar factors cancel under conjugation. Under this identification the local tangent spaces, their Tate orthogonals, the Selmer groups, and the numerical defect agree. Twisting by a *variable* character is not the same operation; it introduces an additional character-deformation factor and belongs to variable-determinant theory.

### 14.3 Contragredients and Tate duality

Taking the contragredient,

$$
\rho_A^\vee(g)={}^{t}\rho_A(g)^{-1},
\tag{14.6}
$$

is another involutive equivalence when local conditions are transported with it. It sends determinant $\delta$ to $\delta^{-1}$. The transpose identification gives an isomorphism of adjoint modules

$$
\operatorname{ad}(\bar\rho^\vee)
\simeq\operatorname{ad}\bar\rho,
\tag{14.7}
$$

and preserves trace-zero submodules. On tangent cocycles the differential of (14.6) introduces a minus transpose; this sign does not change the resulting Selmer dimensions.

The contragredient operation must not be confused with the dual module in Poitou--Tate theory. The obstruction-theoretic dual is

$$
M'=M^*(1),
$$

which contains a Tate twist. It is a coefficient module paired with $M$ by local duality; it is not, in general, the tangent adjoint of the contragredient deformation problem. Forgetting the twist reverses the local orthogonals and gives a false numerical formula.

If a polarization identifies $\bar\rho^\vee$ with a twist of $\bar\rho$, then (14.3) and (14.6) together can identify the primal adjoint with its Tate dual. Such a self-duality is extra structure. The general theory in this book does not assume it.

### 14.4 Restriction of coefficient scalars

For the clean residual comparison, let $\mathcal O'/\mathcal O$ be finite unramified with residue extension $k'/k$ of degree $e$, let $V'$ be a $d$-dimensional $k'$-representation, and put

$$
W=\operatorname{Res}_{k'/k}V'.
$$

Then $W$ is a $de$-dimensional $k$-representation equipped with a distinguished embedding $k'\hookrightarrow\operatorname{End}_{k[G]}(W)$. To compare functors on the $\mathcal O$-coefficient category, define an enhanced deformation to be a deformation of $W$ together with an $\mathcal O'$-action lifting this residual coefficient action, commuting with Galois, and satisfying the expected rank-$d$ freeness condition. Forgetting the extra action gives a natural transformation

$$
D_{\text{with lifted }\mathcal O'\text{-action}}
\longrightarrow D_{\mathcal O\text{-linear}}
$$

and, whenever both framed problems are represented, a ring map

$$
R_{\mathcal O\text{-linear}}
\longrightarrow R_{\text{with lifted }\mathcal O'\text{-action}}.
\tag{14.8}
$$

The target describes the locus on which the extra coefficient action lifts. It is generally a proper condition, not a completed scalar extension of the source. The ordinary rank-$d$ $\mathcal O'$-linear deformation problem is recovered from this enhanced problem only after passing to the corresponding $\mathcal O'$-coefficient category and selecting its specified residual factor.

The adjoint modules explain the discrepancy. If $V'$ is the residual $k'$-space, the $k'$-linear problem uses

$$
\operatorname{End}_{k'}(V'),
$$

whereas the underlying $k$-linear problem uses

$$
\operatorname{End}_k(\operatorname{Res}_{k'/k}V'),
$$

which is larger. Its extra endomorphisms give genuine additional tangent directions unless the lifted $k'$-action is imposed. Likewise, the determinant of the underlying $k$-linear representation is the norm of the $k'$-linear determinant. Fixed-determinant data must therefore be transported by the norm, not copied unchanged.

Schur hypotheses can also change under restriction of scalars. A representation with scalar centralizer over $k'$ need not have scalar centralizer over $k$ in the sense needed for the larger linear group. The framed comparison (14.8) remains meaningful, but an unframed universal ring must be justified independently.

For a ramified finite free extension $\mathcal O'/\mathcal O$, reduction modulo $\mathfrak m_{\mathcal O}$ retains the nonreduced algebra $\mathcal O'/\mathfrak m_{\mathcal O}\mathcal O'$, not merely the residual field $k'$. One must formulate the enhanced problem with that full coefficient action and a chosen lattice. The simple pair of adjoint spaces displayed above no longer captures all infinitesimal data, so no general residual-ring formula is asserted in that case.

### 14.5 Restriction to a finite extension of number fields

There is a second, unrelated restriction operation. Let $L/K$ be finite, choose a controlling set $S_L$ containing all places above $S$ and all ramification introduced by $L/K$, and restrict representations from $G_{K,S}$ to $G_{L,S_L}$. Transporting every local condition to all places above it gives a natural transformation

$$
D_{\mathcal D_K}^{\square_T}
\longrightarrow D_{\mathcal D_L}^{\square_{T_L}}.
\tag{14.9}
$$

Whenever both sides are represented, the ring map has the reverse direction:

$$
R_{\mathcal D_L}^{\square_{T_L}}
\longrightarrow R_{\mathcal D_K}^{\square_T}.
\tag{14.10}
$$

Restriction can enlarge the residual centralizer, so the unframed problem over $L$ may cease to be representable even when the one over $K$ is Schur. Frames avoid this problem.

At first order, (14.9) is the ordinary restriction map on global cohomology together with all local restriction maps. It need be neither injective nor surjective. If $L/K$ is Galois and $\ell\nmid[L:K]$, restriction followed by corestriction is multiplication by $[L:K]$, so restriction is injective on the relevant cohomology; no such conclusion holds when $\ell$ divides the degree. Shapiro's lemma compares cohomology with an induced coefficient module, not $H^1(K,M)$ directly with $H^1(L,M)$. Therefore there is no universal degree-multiplication formula for Selmer dimensions or defects.

### 14.6 Compatibility of the local tensor product with operations

All preceding operations can be performed before or after assembling the local base only when they commute with each local condition. Under the effective functorial base-change hypothesis used for (14.1a), the comparison is

$$
R_{\mathrm{loc}}(\mathcal D')
\simeq
R_{\mathrm{loc}}(\mathcal D)
\widehat\otimes_{\mathcal O}\mathcal O'.
\tag{14.11}
$$

Without that hypothesis, scalar extension of the old local universal families gives only the canonical map

$$
R_{\mathrm{loc}}(\mathcal D')
\longrightarrow
R_{\mathrm{loc}}(\mathcal D)
\widehat\otimes_{\mathcal O}\mathcal O',
$$

obtained by completed tensoring of the factorwise comparison maps. Local preservation alone does not turn it into an isomorphism.

For twisting or contragredients, the transported local rings are isomorphic factor by factor, hence so are their completed tensor products. For a strengthened condition at one framed place, (13.6) is the corresponding base change of one factor.

These assertions use associativity of completed tensor products in the category of topologically finite-type complete local algebras over a common residue field. Without finite generation or a specified common closed point, the displayed completions need not be Noetherian or even local. The hypotheses attached to (5.6) must be rechecked after every operation; notation alone does not preserve them.

## 15. The global deformation-ring theorem package

The construction can now be compressed into a package suitable for later use. The value of such a theorem is not brevity for its own sake. It separates hypotheses needed for the existence of a universal ring from the stronger hypotheses needed for cohomological equation bounds, and it exposes every numerical input that survives at the global interface.

### 15.1 Standing hypotheses for the package

Let $\mathcal D$ be a global deformation datum as in (4.8), and assume the following.

1. The finite set $S$ contains the archimedean places, the places above $\ell$, and all ramification of $\bar\rho$, the determinant, and the local conditions.
2. The coefficient rings have a common specified residue field $k$. Every local representing ring is complete Noetherian local and topologically of finite type over $\mathcal O$.
3. Either determinant is fully variable and $M=\operatorname{ad}\bar\rho$, or determinant is fixed, $\ell\nmid d$, and $M=\operatorname{ad}^0\bar\rho$. Put $M'=M^*(1)$ and $A_{\mathrm{gauge}}=\operatorname{ad}\bar\rho$.
4. Every local condition is representable in the stated framed or unframed category, closed in the unrestricted local problem, stable under coefficient base change, and compatible with the determinant data.
5. The continuous global and local cohomology groups that occur below are finite-dimensional. For the unframed conclusion, assume the global Schur condition (2.1) and closed relative representability of the pulled-back local conditions. If the literal unframed fiber product (5.5) is used, assume its local unframed factors are representable.
6. For the relation bounds only, assume compatible complete and effective local/global obstruction theories whose relative Selmer complex is dual to the dual Selmer structure described in Chapter 9.

Let $T$ be a nonempty finite set of places at which framed local condition rings are used. Conditions outside $T$, including archimedean conditions when appropriate, are imposed directly as closed pullbacks on the global functor; no local coarse ring is required for that operation. Write

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in T,\mathcal O}
R_v^{\square,\mathcal D_v}.
\tag{15.1}
$$

These assumptions deliberately exclude the fixed-determinant case $\ell\mid d$ from the compact trace-zero formulas. That case remains valid after replacing $M$ by the trace-kernel complex (7.10) and its correct Tate dual, but it is not covered by merely changing one symbol in the theorem.

### 15.2 Representability and the universal property

**Theorem 15.1 (global assembly).** Under hypotheses 1--5, the partially framed global condition functor is pro-represented by a complete Noetherian local ring $R_{\mathcal D}^{\square_T}$. It is the functorial fiber product

$$
D_{\mathcal D}^{\square_T}
=D_{K,S}^{\square_T,\mathcal D^{S\setminus T}}
\times_{\prod_{v\in T}D_v^\square}
\prod_{v\in T}D_v^{\square,\mathcal D_v},
\tag{15.2}
$$

and its ring is the completed pushout

$$
\boxed{
R_{\mathcal D}^{\square_T}
\simeq
R_{K,S}^{\square_T,\mathcal D^{S\setminus T}}
\widehat\otimes_{
\widehat\otimes_{v\in T,\mathcal O}R_v^\square}
R_{\mathrm{loc}}.}
\tag{15.3}
$$

The structural map points from local to global:

$$
R_{\mathrm{loc}}\longrightarrow R_{\mathcal D}^{\square_T}.
\tag{15.4}
$$

If the global datum is Schur and the pulled-back local conditions are closedly relatively representable, the unframed functor is pro-represented by $R_{\mathcal D}$. Its $A$-points are precisely strict-equivalence classes of lifts $G_{K,S}\to\operatorname{GL}_d(A)$ with the prescribed determinant and local conditions. This conclusion still applies when a local residual centralizer is nonscalar and only the local framed quotient exists.

**Proof.** The unrestricted framed global lifting functor is pro-representable because $G_{K,S}$ satisfies the required finiteness condition. Conditions outside $T$ cut out closed subfunctors. Each framed local condition is represented by a quotient of its unrestricted local ring. Products of the finitely many local functors are represented by the completed tensor products because the residue field is common and all factors are topologically of finite type. The functorial pullback (15.2) is therefore represented by the ring pushout (15.3). Under the Schur condition the global unframed functor is universal; pulling the conjugacy-invariant local quotient ideals back along a representative of its universal class gives the stated unframed quotient, independently of that representative. $\square$

### 15.3 Tangents, presentations, and relation bounds

For $v\in S$, let

$$
L_v\subseteq H^1(K_v,M)
$$

be the local tangent subspace, and form $H^1_{\mathcal L}(K,M)$ as in (7.1). At the places of $T$, impose the strict tangent $0$ and write the resulting group as $H^1_{\mathcal L,T}(K,M)$. Define

$$
g_T
=h^1_{\mathcal L,T}(K,M)
+\sum_{v\in T}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).
\tag{15.5}
$$

Let $(\mathcal L_T^0)^\perp$ have the relaxed local condition at $T$ and $L_v^\perp$ elsewhere, and put

$$
q_T
=h^1_{(\mathcal L_T^0)^\perp}(K,M').
\tag{15.6}
$$

**Theorem 15.2 (tangent and presentation).** Under hypotheses 1--5, the unframed tangent space is

$$
t_{\mathcal D}\simeq H^1_{\mathcal L}(K,M),
\tag{15.7}
$$

and the relative tangent of (15.4) lies in the canonical exact sequence

$$
0\to
\frac{\bigoplus_{v\in T}H^0(K_v,A_{\mathrm{gauge}})}
{H^0(K,A_{\mathrm{gauge}})}
\to t_{\mathrm{rel},T}
\to H^1_{\mathcal L,T}(K,M)
\to0.
\tag{15.8}
$$

Consequently there is a surjection

$$
R_{\mathrm{loc}}[[x_1,\ldots,x_{g_T}]]
\twoheadrightarrow R_{\mathcal D}^{\square_T}.
\tag{15.9}
$$

Under hypothesis 6, its kernel can be generated by $r_T$ elements with

$$
r_T\leq q_T.
\tag{15.10}
$$

Equivalently,

$$
\boxed{
R_{\mathcal D}^{\square_T}
\simeq
R_{\mathrm{loc}}[[x_1,\ldots,x_{g_T}]]
/(f_1,\ldots,f_{r_T}),
\qquad r_T\leq q_T.}
\tag{15.11}
$$

**Proof.** A first-order lift is a global cocycle; strict equivalence removes global coboundaries, and membership in every local tangent subspace gives (15.7). To lie over the closed point of $R_{\mathrm{loc}}$, the restriction at each $v\in T$ must be a coboundary together with a chosen trivialization. Local invariant changes of the trivializations survive, while simultaneous global invariant changes do not. This proves (15.8) and the dimension (15.5). Minimal cotangent generators then give (15.9).

Under hypothesis 6, relative lifting obstructions land functorially in the degree-two group of the relative Selmer complex. Global duality identifies its dual with the group in (15.6). Effectiveness injects the dual minimal relation space into this complete obstruction space. Thus the minimal number of relations is at most $q_T$, proving (15.10)--(15.11). The argument gives an inequality because the complete obstruction space need not be minimal. $\square$

### 15.4 The Poitou--Tate identity and numerical defect

**Theorem 15.3 (global numerical identity).** With the same local tangent spaces and their exact Tate orthogonals,

$$
\boxed{
h^1_{\mathcal L}(K,M)
-h^1_{\mathcal L^\perp}(K,M')
=h^0(K,M)-h^0(K,M')
+\sum_{v\in S}
\bigl(\dim_kL_v-h^0(K_v,M)\bigr).}
\tag{15.12}
$$

At real places the $H^0$ term is ordinary invariants, while the proof uses Tate-modified cohomology. At complex places the contribution is $-\dim_kM$. For odd $\ell$, positive-degree real cohomology vanishes; for $\ell=2$, no such deletion is allowed.

For the relative presentation,

$$
\boxed{
\begin{aligned}
g_T-q_T
={}&h^0(K,M)-h^0(K,M')\\
&+\sum_{v\notin T}
(\dim_kL_v-h^0(K_v,M))
-\sum_{v\in T}h^0(K_v,M)\\
&+\sum_{v\in T}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).
\end{aligned}}
\tag{15.13}
$$

Thus

$$
\boxed{
\dim R_{\mathcal D}^{\square_T}
\geq
\dim R_{\mathrm{loc}}+g_T-q_T.}
\tag{15.14}
$$

The absolute defect exported by the unframed problem is

$$
\boxed{
\Delta(\mathcal D)
=h^1_{\mathcal L}(K,M)
-h^1_{\mathcal L^\perp}(K,M').}
\tag{15.15}
$$

It is computable from the right side of (15.12). Balanced means $\Delta(\mathcal D)=0$, and nothing stronger.

**Proof.** Apply the Selmer Poitou--Tate exact sequence with local condition complexes defining $L_v$ and $L_v^\perp$. Alternating dimensions, local Tate duality, and the global Euler characteristic give (15.12). Replacing $L_v$ by zero at $v\in T$ and adding the framing invariants from (15.5) gives (15.13). Finally (15.11) and the principal ideal theorem give (15.14). $\square$

### 15.5 The totally real rank-two specialization

Suppose $K$ is totally real, $d=2$, $\ell>2$, determinant is fixed, and $\bar\rho$ is Schur. Retain the mixed-characteristic coefficient setup of the low-weight theorem in Section 4.4. Assume $\bar\rho$ is odd at every real place, has no global cyclotomic adjoint self-twist, and at every $v\mid\ell$ satisfies the unramified low-weight finite-flat hypotheses stated there. At every finite $v\nmid\ell$, assume the chosen local condition has the proved neutral tangent count

$$
\dim_kL_v=h^0(K_v,\operatorname{ad}^0\bar\rho).
$$

This includes the unramified and compatible fixed prime-to-$\ell$ type conditions, and includes a minimal special condition only when its actual local calculation proves the equality. Then

$$
M=\operatorname{ad}^0\bar\rho,
\qquad
h^0(K,M)=h^0(K,M(1))=0.
$$

Every finite place away from $\ell$ is neutral by hypothesis. Each real place contributes $-1$. Each $v\mid\ell$ contributes $[K_v:\mathbf Q_\ell]$, and the sum of those degrees is $[K:\mathbf Q]$, the number of real places. Therefore

$$
\boxed{\Delta(\mathcal D)=0.}
\tag{15.16}
$$

The finite-flat local factors are formally smooth of framed relative dimension $[K_v:\mathbf Q_\ell]+3$ under precisely the stated local hypotheses. They can be placed in $R_{\mathrm{loc}}$ without adding local relations. This is the clean balanced interface used in two-dimensional modularity lifting.

For $\ell=2$, statement (15.16) is not inherited by reduction. One must use the trace-kernel determinant complex, specify the real local conditions in characteristic two, retain modified real cohomology, and supply an appropriate $2$-adic integral local theorem. Oddness cannot be read from the residual determinant, and the finite-flat power-series result used above does not apply.

### 15.6 What the package exports, and what it does not

The final output of the global theory is the following finite list of objects and identities:

- the universal ring $R_{\mathcal D}$ and, when local base rings are needed, $R_{\mathcal D}^{\square_T}$ over $R_{\mathrm{loc}}$;
- the primal tangent space $H^1_{\mathcal L}(K,M)$ and the strict relative tangent count $g_T$ with all centralizer corrections;
- the dual Selmer dimensions $q(\mathcal D)$ and $q_T$ defined using Tate-twisted exact orthogonals;
- a presentation over $R_{\mathrm{loc}}$ with $g_T$ generators and at most $q_T$ relations under the complete-effectiveness hypotheses;
- the defect $\Delta(\mathcal D)$ and the expanded local formula (15.12), including archimedean and determinant contributions;
- comparison maps under changes of $S$, local conditions, frames, coefficients, twists, duals, and restrictions.

These are exactly the deformation-theoretic numerical inputs needed before an auxiliary-prime or patching construction begins. The package does not assert that the relation bound is sharp, that the ring is a complete intersection, that it is flat over $\mathcal O$, or that its generic fiber is nonzero. It does not select auxiliary primes, construct patched modules, or compare the universal ring with a ring of operators. Each of those conclusions needs additional arithmetic.

The two dual dimensions have different downstream roles. The absolute number $q(\mathcal D)=h^1_{\mathcal L^\perp}(K,M')$ is the reciprocity defect that Taylor--Wiles primes are chosen to kill. The relaxed-at-$T$ number $q_T$ is the complete cohomological relation bound for the presentation relative to $R_{\mathrm{loc}}$. Neither may be substituted for the other merely because the absolute problem is balanced.

What has been achieved is more basic and more durable: every allowed local lift has been assembled into one universal global object, and every first-order freedom and reciprocity obstruction has been accounted for with the correct variance, determinant coefficient, framing term, Tate twist, and real-place sign. The ring $R_{\mathcal D}$ is now ready to serve as the global deformation-ring input to the next stage of the theory.
