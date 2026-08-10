# Relation Obstructions and Poitou–Tate Corrections

## Contents

- [1. From equations to arithmetic obstructions](#1-from-equations-to-arithmetic-obstructions)
  - [1.1 Why a relation has a factor set](#11-why-a-relation-has-a-factor-set)
  - [1.2 The standing hardly-ramified problem](#12-the-standing-hardly-ramified-problem)
  - [1.3 The three spaces that must not be confused](#13-the-three-spaces-that-must-not-be-confused)
  - [1.4 Main results and variance](#14-main-results-and-variance)
- [2. Small extensions and minimal relations](#2-small-extensions-and-minimal-relations)
  - [2.1 Square-zero lifting problems](#21-square-zero-lifting-problems)
  - [2.2 Minimal power-series presentations](#22-minimal-power-series-presentations)
  - [2.3 The universal relation extension](#23-the-universal-relation-extension)
  - [2.4 Linear tests of individual relations](#24-linear-tests-of-individual-relations)
  - [2.5 Effectiveness and the relation bound](#25-effectiveness-and-the-relation-bound)
- [3. Factor sets of lifted representations](#3-factor-sets-of-lifted-representations)
  - [3.1 The multiplicative defect](#31-the-multiplicative-defect)
  - [3.2 The cocycle identity](#32-the-cocycle-identity)
  - [3.3 Independence of choices](#33-independence-of-choices)
  - [3.4 Vanishing and correction](#34-vanishing-and-correction)
  - [3.5 Fixed determinant and trace zero](#35-fixed-determinant-and-trace-zero)
  - [3.6 Continuity and finite quotients](#36-continuity-and-finite-quotients)
- [4. Local admissible lifts as affine torsors](#4-local-admissible-lifts-as-affine-torsors)
  - [4.1 Why local existence is not a chosen lift](#41-why-local-existence-is-not-a-chosen-lift)
  - [4.2 Differences of local lifts](#42-differences-of-local-lifts)
  - [4.3 The three distinguished places](#43-the-three-distinguished-places)
  - [4.4 Automorphisms and rigidifications](#44-automorphisms-and-rigidifications)
  - [4.5 Functoriality under pushout](#45-functoriality-under-pushout)
- [5. The supported relation class](#5-the-supported-relation-class)
  - [5.1 Adding local nullhomotopies](#51-adding-local-nullhomotopies)
  - [5.2 The mapping-fiber cocycle](#52-the-mapping-fiber-cocycle)
  - [5.3 Choice independence](#53-choice-independence)
  - [5.4 Completeness of the obstruction](#54-completeness-of-the-obstruction)
  - [5.5 Additivity and base change](#55-additivity-and-base-change)
- [6. Correction torsors and localization defects](#6-correction-torsors-and-localization-defects)
  - [6.1 Mismatch classes](#61-mismatch-classes)
  - [6.2 The affine correction target](#62-the-affine-correction-target)
  - [6.3 The exact Poitou–Tate functional](#63-the-exact-poitou-tate-functional)
  - [6.4 What surjectivity does and does not say](#64-what-surjectivity-does-and-does-not-say)
- [7. Reciprocity for correction targets](#7-reciprocity-for-correction-targets)
  - [7.1 The local sum](#71-the-local-sum)
  - [7.2 Global families give zero](#72-global-families-give-zero)
  - [7.3 Exactness of the correction criterion](#73-exactness-of-the-correction-criterion)
  - [7.4 Changes of representatives and signs](#74-changes-of-representatives-and-signs)
- [8. A proof of the required global Brauer reciprocity](#8-a-proof-of-the-required-global-brauer-reciprocity)
  - [8.1 The precise theorem needed here](#81-the-precise-theorem-needed-here)
  - [8.2 Finite support](#82-finite-support)
  - [8.3 Cyclic relative classes](#83-cyclic-relative-classes)
  - [8.4 The principal-idèle product law](#84-the-principal-idèle-product-law)
  - [8.5 The relative invariant sequence](#85-the-relative-invariant-sequence)
  - [8.6 Real places and the prime two](#86-real-places-and-the-prime-two)
  - [8.7 Exactness at the correction target](#87-exactness-at-the-correction-target)
- [9. Universal obstructions attached to relations](#9-universal-obstructions-attached-to-relations)
  - [9.1 The universal factor-set tensor](#91-the-universal-factor-set-tensor)
  - [9.2 The obstruction map from relation functionals](#92-the-obstruction-map-from-relation-functionals)
  - [9.3 Proof of injectivity](#93-proof-of-injectivity)
  - [9.4 Presentation independence](#94-presentation-independence)
- [10. Passage to the dual Selmer space](#10-passage-to-the-dual-selmer-space)
  - [10.1 Supported duality in degree two](#101-supported-duality-in-degree-two)
  - [10.2 The canonical injection and its dual quotient](#102-the-canonical-injection-and-its-dual-quotient)
  - [10.3 Relation corrections as local pairing matrices](#103-relation-corrections-as-local-pairing-matrices)
  - [10.4 When an isomorphism occurs](#104-when-an-isomorphism-occurs)
- [11. The hardly-ramified specialization](#11-the-hardly-ramified-specialization)
  - [11.1 The local ledger](#111-the-local-ledger)
  - [11.2 Vanishing of local obstruction groups](#112-vanishing-of-local-obstruction-groups)
  - [11.3 Balanced dimensions and minimal relations](#113-balanced-dimensions-and-minimal-relations)
  - [11.4 Scalar and reducible local restrictions](#114-scalar-and-reducible-local-restrictions)
- [12. Exceptional cases and changes of data](#12-exceptional-cases-and-changes-of-data)
  - [12.1 Characteristics two, three, and five](#121-characteristics-two-three-and-five)
  - [12.2 Enlarging the controlling set](#122-enlarging-the-controlling-set)
  - [12.3 Extending the residue field](#123-extending-the-residue-field)
  - [12.4 Nonminimal presentations](#124-nonminimal-presentations)
  - [12.5 Failure of local smoothness](#125-failure-of-local-smoothness)
- [13. Dependency and normalization audit](#13-dependency-and-normalization-audit)
  - [13.1 Imported results with matching hypotheses](#131-imported-results-with-matching-hypotheses)
  - [13.2 Sign, twist, and degree ledger](#132-sign-twist-and-degree-ledger)
  - [13.3 A reliable relation-obstruction protocol](#133-a-reliable-relation-obstruction-protocol)
- [14. Conclusion](#14-conclusion)
  - [14.1 The completed obstruction package](#141-the-completed-obstruction-package)
  - [14.2 The balanced endpoint](#142-the-balanced-endpoint)

## 1. From equations to arithmetic obstructions

### 1.1 Why a relation has a factor set

A deformation ring is described by equations, whereas Galois cohomology describes failures of lifting. The two descriptions meet at a simple construction. Start with matrices that lift a representation only as a set map. Their failure to multiply correctly is a factor set. Associativity forces that factor set to be a $2$-cocycle. If the matrices can be corrected to an honest representation, the cocycle is a coboundary; conversely, a coboundary gives the required correction.

This familiar unrestricted argument is not yet enough for a deformation problem with local conditions. A global factor set may vanish in ordinary $H^2$ while every correction destroys a prescribed local type. At the other extreme, the local obstruction may vanish at every place while the chosen local corrections do not arise from one global correction. The missing datum is a local nullhomotopy at each controlled place. A global $2$-cocycle together with these local nullhomotopies is a cocycle in the supported mapping fiber developed in Book 183.

There is a second layer of ambiguity. An admissible local lift is rarely canonical. Once one exists, all of them form an affine torsor under the local tangent space. Choosing one point of each torsor creates a local mismatch. Poitou–Tate duality tests whether the mismatch can be corrected globally: pair it with every dual Selmer class and sum the local invariants. Global reciprocity proves that global changes give zero; exactness proves that these are all the relations.

The purpose of this book is to make those two layers compatible. We shall construct relation factor sets, upgrade them to supported classes, describe the affine local correction problem, prove the reciprocity law required for its target, and then compare the minimal relation space with the exact dual Selmer obstruction space. Every arrow will retain its variance. In particular, a conormal relation and a functional on conormal relations point in opposite directions under duality.

### 1.2 The standing hardly-ramified problem

The principal application uses the data fixed in Book 183. Let $\ell\geq7$, let $k$ be a finite field of characteristic $\ell$, and let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
$$

be continuous, absolutely irreducible, odd, of determinant $\bar\chi_\ell$, unramified outside $\{2,\ell\}$, of tame-quadratic order-three type at $2$, and of the stated coefficient-linear finite-flat type at $\ell$. Put

$$
S=\{2,\ell,\infty\},\qquad
M=\operatorname{ad}^0\bar\rho,\qquad
M'=M^*(1)\simeq M(1). \tag{1.1}
$$

The trace pairing is perfect on $M$ because $\ell\ne2$. The local tangent structure is

$$
L_2=0,\qquad
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),\qquad
L_\infty=0. \tag{1.2}
$$

At a harmless finite prime outside $S$ the implicit condition is unramified. The dual condition is always the exact Tate orthogonal

$$
L_v^\perp\subseteq H^1(\mathbf Q_v,M'). \tag{1.3}
$$

We write $C_{\mathcal L}^\bullet(\mathbf Q,M)$ for the supported mapping fiber and $H^i_{\mathcal L}(\mathbf Q,M)$ for its cohomology. For (1.2) we also write the subscript $\mathrm{hr}$. Book 183 proves

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*, \tag{1.4}
$$

and the balanced equality

$$
\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M). \tag{1.5}
$$

Our task is not to repeat the dimension calculation. It is to prove that actual minimal relations produce actual classes in the left side of (1.4), with all local corrections included, and that no relation direction disappears in this passage.

Most constructions will first be given for a number field $K$, a finite set $S$, a finite coefficient field $k$, a finite $G_{K,S}$-module $M$, and a system of locally liftable conditions $\mathcal L=(L_v)$. We specialize to (1.1)–(1.2) only after the general mechanism is complete.

### 1.3 The three spaces that must not be confused

Let a complete local deformation ring have a minimal relative presentation

$$
R=P/J,\qquad P=\mathcal O[[X_1,\ldots,X_t]], \tag{1.6}
$$

with maximal ideal $\mathfrak n$ in $P$. Three finite-dimensional spaces occur.

The **conormal relation space** is

$$
\operatorname{Rel}_P(R)=J/\mathfrak nJ. \tag{1.7}
$$

Its dimension is the minimal number of generators of $J$. A functional on (1.7) selects one infinitesimal relation direction. It therefore belongs to the **relation-obstruction space**

$$
\operatorname{Rel}^{\mathrm{ob}}_P(R)
=\operatorname{Rel}_P(R)^*. \tag{1.8}
$$

Finally, cohomological obstructions live in

$$
H^2_{\mathcal L}(K,M), \tag{1.9}
$$

which supported duality identifies with the linear dual of a dual Selmer group.

The canonical variance is therefore

$$
\operatorname{Rel}^{\mathrm{ob}}_P(R)
\longrightarrow H^2_{\mathcal L}(K,M)
\longrightarrow H^1_{\mathcal L^\perp}(K,M')^*. \tag{1.10}
$$

When this map is injective, dualizing gives a canonical surjection

$$
H^1_{\mathcal L^\perp}(K,M')
\twoheadrightarrow\operatorname{Rel}_P(R). \tag{1.11}
$$

There is not, without extra choices, a canonical injection in the reverse direction between the two undualized spaces. This is not pedantry: confusing (1.10) with its dual reverses kernels and cokernels. We will sometimes call the source of (1.10) the **relation module**, because it is the module of relation obstructions. Whenever the conormal space (1.7) is meant, we will say so explicitly.

### 1.4 Main results and variance

The general theorem proved below is the following.

**Theorem 1.1 (relation obstruction and correction theorem).** Let a fixed-determinant deformation problem over a complete discrete valuation ring $\mathcal O$ have absolutely irreducible residual representation, finite tangent space, locally liftable conditions represented by positive local complexes, and a universal ring with a minimal presentation (1.6). Assume that the coefficient characteristic is odd, that the local Tate duals and Poitou–Tate sequence are in their finite-module range, and that the local lift torsors are compatible with pushout of small extensions.

Then:

1. every small-extension lifting problem has a functorial supported factor-set obstruction in $H^2_{\mathcal L}(K,M)\otimes_k I$;
2. the obstruction vanishes exactly when an admissible global lift exists;
3. when local admissible lifts exist, their choices form affine torsors under $L_v\otimes_k I$;
4. a local mismatch is globally correctable exactly when its local Tate pairings with all dual Selmer classes sum to zero;
5. the universal obstruction induces a canonical injection
   $$
   \operatorname{Rel}^{\mathrm{ob}}_P(R)
   \hookrightarrow H^2_{\mathcal L}(K,M)
   \simeq H^1_{\mathcal L^\perp}(K,M')^*; \tag{1.12}
   $$
6. equivalently, there is a canonical surjection (1.11), and
   $$
   \dim_k\operatorname{Rel}_P(R)
   \leq\dim_kH^1_{\mathcal L^\perp}(K,M'). \tag{1.13}
   $$

For the hardly-ramified problem (1.1)–(1.2), the hypotheses hold and the right side of (1.13) equals the tangent dimension. Hence a minimal presentation has no more relations than variables.

The proof has two genuinely arithmetic points. First, supported degree two, rather than ordinary degree two, is the complete obstruction space. Second, the correction functional is exact because global reciprocity supplies precisely the zero relation among local invariants. We prove the exact reciprocity statement used here inside this book.

## 2. Small extensions and minimal relations

### 2.1 Square-zero lifting problems

Let $\mathcal C_{\mathcal O}$ be the category of complete local Noetherian $\mathcal O$-algebras with residue field $k$, and use its Artinian objects when discussing infinitesimal lifting. A surjection

$$
A'\twoheadrightarrow A \tag{2.1}
$$

is a **small extension** if its kernel $I$ is nonzero and

$$
\mathfrak m_{A'}I=0. \tag{2.2}
$$

Then $I$ is naturally a finite-dimensional $k$-vector space and $I^2=0$. Every surjection of Artinian local rings can be factored into small extensions: if $I$ is its kernel, filter $I$ by powers of the maximal ideal and refine the successive quotients to one-dimensional $k$-spaces. Thus solving small extensions is enough for formal lifting.

The square-zero condition makes multiplication linear. If $X,Y$ are matrices with entries in $I$, then

$$
(1+X)(1+Y)=1+X+Y. \tag{2.3}
$$

If $g$ acts on $M=\operatorname{ad}^0\bar\rho$ by conjugation, then moving $1+Y$ past a lift of $\bar\rho(g)$ replaces $Y$ by $gY$. Formula (2.3) is therefore the source of the inhomogeneous cochain differential.

A complete obstruction theory assigns to a deformation over $A$ and a small extension (2.1) a class in $V\otimes_k I$ whose vanishing is necessary and sufficient for a lift. Functoriality in $I$ is essential. If $I\to I'$ is a $k$-linear map and $A'\to A$ is pushed out along it, the new obstruction must be the image of the old one. Without this condition, testing an individual relation by a functional would not be well defined.

### 2.2 Minimal power-series presentations

Let $R$ represent the deformation problem and let

$$
P=\mathcal O[[X_1,\ldots,X_t]]\twoheadrightarrow R \tag{2.4}
$$

be a relative power-series presentation with kernel $J$. Write $\mathfrak n$ for the maximal ideal of $P$. The variables are **minimal** when their classes form a basis of the relative cotangent space of $R$. Equivalently, the induced map

$$
\mathfrak n/(\mathfrak n^2+\mathfrak m_{\mathcal O}P)
\longrightarrow
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R)
$$

is an isomorphism. In such a presentation every element of $J$ has zero relative linear part.

The minimal number of equations is

$$
r=\dim_kJ/\mathfrak nJ. \tag{2.5}
$$

Indeed, Nakayama's lemma says that $f_1,\ldots,f_r$ generate $J$ if and only if their classes span $J/\mathfrak nJ$, and they form a minimal generating set if and only if those classes form a basis. Since $P$ is Noetherian, $J$ is finitely generated.

The conormal description gives the same space:

$$
\frac{J/J^2}{\mathfrak m_R(J/J^2)}
\simeq\frac{J}{\mathfrak nJ+J^2}
=\frac{J}{\mathfrak nJ}, \tag{2.6}
$$

because $J\subseteq\mathfrak n$ implies $J^2\subseteq\mathfrak nJ$. This equality is useful: a minimal relation is an equation modulo its multiples and modulo consequences of other equations, not a differential at the closed point.

**Example.** For $R=k[[X]]/(X^m)$ with $m\ge2$, the tangent dimension and the relation number are both one. The derivative of $X^m$ at the closed point is zero, so tangent geometry does not detect the relation. The factor-set obstruction will detect it when one attempts to lift the universal nilpotent element through the next square-zero thickening.

### 2.3 The universal relation extension

Put

$$
\overline P=P/\mathfrak nJ,\qquad
\overline J=J/\mathfrak nJ. \tag{2.7}
$$

There is an exact sequence

$$
0\longrightarrow\overline J
\longrightarrow\overline P
\longrightarrow R\longrightarrow0. \tag{2.8}
$$

The kernel is killed by the maximal ideal of $\overline P$, so (2.8) is a small extension whenever $R$ is Artinian. For a general complete $R$, apply the same construction after quotienting by a sufficiently high power of the maximal ideal; every selected finite-dimensional relation direction appears at some Artinian level. This inverse system is the **universal relation extension**.

Why is (2.8) universal? Let $A'\twoheadrightarrow A$ be a small extension with kernel $I$, and let $x:R\to A$ be a local map. Choose arbitrary lifts to $A'$ of the images of the variables in $P$. They give a map $\widetilde x:P\to A'$. For $f\in J$, the element $\widetilde x(f)$ lies in $I$. If $a\in\mathfrak n$, then

$$
\widetilde x(af)=\widetilde x(a)\widetilde x(f)=0,
$$

because $\widetilde x(a)\in\mathfrak m_{A'}$ and $\mathfrak m_{A'}I=0$. Hence evaluation of relations factors through a $k$-linear map

$$
\epsilon_{\widetilde x}:\overline J\longrightarrow I. \tag{2.9}
$$

Changing the chosen variable lifts changes (2.9) by the first-order effect of a derivation. In a minimal presentation that effect has no component on $\overline J$, because every relation has zero linear part. Thus the induced relation test is intrinsic to the lifting problem.

Conversely, push (2.8) out along a linear map $\lambda:\overline J\to I$. The result is the universal small extension in the relation direction $\lambda$. Every obstruction to lifting the universal deformation through an arbitrary small extension is obtained from the universal relation obstruction by such a pushout.

### 2.4 Linear tests of individual relations

Let

$$
\lambda\in\overline J^*=\operatorname{Rel}^{\mathrm{ob}}_P(R). \tag{2.10}
$$

Push out (2.8) along $\lambda:\overline J\to k$. Denote the resulting one-dimensional small extension by

$$
0\longrightarrow k\longrightarrow A_\lambda
\longrightarrow R_{\lambda,0}\longrightarrow0, \tag{2.11}
$$

where an Artinian quotient is understood if necessary. The universal deformation over the quotient has a lifting obstruction

$$
\operatorname{ob}(\lambda)\in V. \tag{2.12}
$$

Functoriality and additivity make

$$
\operatorname{ob}:\overline J^*\longrightarrow V \tag{2.13}
$$

a $k$-linear map. This is the correct direction: a functional chooses a quotient of the universal kernel, so relation functionals map covariantly to obstruction classes.

If one instead chooses a basis $f_1,\ldots,f_r$ of $\overline J$, its dual basis gives $r$ one-dimensional tests. The resulting list of obstruction classes depends on the basis, but the linear map (2.13) does not. Replacing the relation generators by an invertible matrix applies the inverse transpose to the list of functionals and leaves the map invariant.

### 2.5 Effectiveness and the relation bound

Completeness of an obstruction theory says that a given lifting problem is solvable when its obstruction is zero. To prove that (2.13) is injective, one needs the slightly stronger universal statement that a relation direction with zero obstruction can be removed. In a represented deformation problem this follows from completeness, functorial lift torsors, and the universal property of the hull; we give the argument.

**Proposition 2.1 (effectiveness).** Suppose the obstruction theory is complete, functorial under pushout, additive in the square-zero kernel, and compatible with the simply transitive tangent action on rigidified lifts. Then the universal map (2.13) is injective.

**Proof.** Suppose $0\ne\lambda\in\ker(\operatorname{ob})$. Push the universal square-zero extension (2.8) out along $\lambda$; concretely, set

$$
B_\lambda=(P/\mathfrak nJ)/\ker(\lambda).
$$

There is an extension

$$
0\longrightarrow k e\longrightarrow B_\lambda
\xrightarrow{q}R\longrightarrow0, \tag{2.14}
$$

where $e$ is killed by the maximal ideal. The universal deformation over $R$ has obstruction $\operatorname{ob}(\lambda)=0$, so completeness gives a deformation over $B_\lambda$ reducing to the universal one.

When the rings are not Artinian, the preceding sentence means the following inverse-limit argument. Reduce (2.14) modulo successive powers of the maximal ideal. The obstruction at every level is the image of the same zero class. Choose a lift at the first level. If a lift has been chosen through level $q$, choose any lift at level $q+1$; its reduction and the chosen level-$q$ lift differ by a tangent vector. The simply transitive tangent action, and its compatibility with reduction, corrects the new lift by that vector. Induction produces a compatible system, and completeness of $B_\lambda$ produces the desired deformation over it.

Since $R$ represents the deformation problem, that lift corresponds to a local $\mathcal O$-algebra map

$$
s:R\longrightarrow B_\lambda
$$

with $q\circ s=\operatorname{id}_R$: both composites classify the universal deformation, and representability gives equality, not merely equivalence.

We now use minimality. Every element of $J$ has zero relative linear part, so the kernel $ke$ of (2.14) lies in

$$
\mathfrak m_{B_\lambda}^{2}+\mathfrak m_{\mathcal O}B_\lambda. \tag{2.15}
$$

On the other hand, a split small extension whose kernel is annihilated by the maximal ideal has

$$
B_\lambda=s(R)\oplus ke
$$

as an $\mathcal O$-module, with $s(\mathfrak m_R)e=0$ and $e^2=0$. Because $s$ is an $\mathcal O$-algebra map,

$$
\mathfrak m_{B_\lambda}^{2}
+\mathfrak m_{\mathcal O}B_\lambda
\subseteq s(R). \tag{2.16}
$$

Equations (2.15) and (2.16) force $e\in s(R)\cap ke=0$, contradicting that $\lambda$ is nonzero. Hence the kernel of (2.13) is zero. $\square$

Consequently any complete effective obstruction space $V$ satisfies

$$
\dim_kJ/\mathfrak nJ\leq\dim_kV. \tag{2.17}
$$

The inequality can be strict. A cohomology group may contain classes never realized by a deformation obstruction. Equality requires surjectivity of the universal obstruction map, which is a separate theorem and will never be inferred from balance of dimensions alone.

## 3. Factor sets of lifted representations

### 3.1 The multiplicative defect

Let (2.1) be a small extension and let

$$
\rho_A:G_{K,S}\longrightarrow\operatorname{GL}_2(A)
$$

be a deformation of $\bar\rho$ with fixed determinant. Choose, for every $g$, a matrix $\widetilde\rho(g)\in\operatorname{GL}_2(A')$ lifting $\rho_A(g)$, with $\widetilde\rho(1)=1$. It need not be multiplicative. Define

$$
F(g,h)=\widetilde\rho(g)\widetilde\rho(h)
\widetilde\rho(gh)^{-1}. \tag{3.1}
$$

Its reduction in $A$ is the identity, so there is a unique

$$
c(g,h)\in\operatorname{End}_k(\bar V)\otimes_kI
$$

such that

$$
F(g,h)=1+c(g,h). \tag{3.2}
$$

The $G_{K,S}$-action on the coefficient is conjugation through $\bar\rho$:

$$
g\cdot X=\bar\rho(g)X\bar\rho(g)^{-1}. \tag{3.3}
$$

The function $c$ is the **relation factor set** of the chosen lifts. It measures multiplication, not the failure of a local condition. The latter will be added in Chapter 5.

### 3.2 The cocycle identity

**Proposition 3.1.** The factor set $c$ is a normalized continuous $2$-cocycle.

**Proof.** Compute the product $\widetilde\rho(g)\widetilde\rho(h)\widetilde\rho(r)$ in two ways. From the first two factors,

$$
\widetilde\rho(g)\widetilde\rho(h)\widetilde\rho(r)
=(1+c(g,h))(1+c(gh,r))\widetilde\rho(ghr).
$$

From the last two factors, moving the square-zero term past $\widetilde\rho(g)$ gives

$$
\widetilde\rho(g)\widetilde\rho(h)\widetilde\rho(r)
=(1+g\cdot c(h,r))(1+c(g,hr))\widetilde\rho(ghr).
$$

Terms quadratic in $I$ vanish. Equating the remaining terms yields

$$
c(g,h)+c(gh,r)=g\cdot c(h,r)+c(g,hr), \tag{3.4}
$$

which is $dc=0$ for the inhomogeneous differential. Normalization follows from $\widetilde\rho(1)=1$.

For continuity, first choose the lifts continuously as explained in Section 3.6. Then multiplication, inversion, and the identification $1+\operatorname{End}(\bar V)\otimes I$ with its additive coefficient module are continuous. $\square$

The proof exposes why associativity is enough. No presentation of the Galois group is involved. A presentation would produce relation words, but every such word evaluates to a consequence of the same cocycle.

### 3.3 Independence of choices

Suppose another normalized lift is

$$
\widetilde\rho'(g)=(1+b(g))\widetilde\rho(g) \tag{3.5}
$$

for a continuous $1$-cochain $b:G_{K,S}\to\operatorname{End}(\bar V)\otimes I$. A direct multiplication gives

$$
c'(g,h)=c(g,h)+b(g)+g\cdot b(h)-b(gh)
=c(g,h)+(db)(g,h). \tag{3.6}
$$

Thus $[c]\in H^2(G_{K,S},\operatorname{End}(\bar V))\otimes I$ is independent of the section.

Strictly conjugating $\rho_A$ also leaves the class unchanged. Indeed, lift the strict conjugating matrix to $A'$ and conjugate every $\widetilde\rho(g)$ by it. The factor set is conjugated by a matrix reducing to the identity; its action on the square-zero coefficient is trivial. If two lifts of the conjugator are used, their quotient contributes a coboundary as in (3.6).

The same computation proves naturality. A map of small kernels $I\to I'$ sends $c$ coefficientwise to the factor set after pushout. A direct sum decomposition $I=I_1\oplus I_2$ decomposes $c$ into its two components. Hence the obstruction is functorial and additive.

### 3.4 Vanishing and correction

**Proposition 3.2 (unrestricted completeness).** The class $[c]$ vanishes if and only if $\rho_A$ has a lift to a representation over $A'$.

**Proof.** If an honest lift exists, choose it as $\widetilde\rho$ and obtain $c=0$. Conversely, if $[c]=0$, choose a continuous $1$-cochain $b$ with

$$
c=db.
$$

Replace the lifts by

$$
\rho_{A'}(g)=(1-b(g))\widetilde\rho(g). \tag{3.7}
$$

Formula (3.6), with $-b$ in place of $b$, gives zero factor set. Thus (3.7) is multiplicative and is an honest lift. $\square$

If one honest lift exists, the others form a torsor under $Z^1(G_{K,S},\operatorname{End}(\bar V))\otimes I$: multiplying by $1+z(g)$ preserves multiplicativity exactly when $dz=0$. Strict conjugation by $1+X$ changes $z$ by the coboundary $dX$. Consequently strict-equivalence classes of lifts form a torsor under $H^1$ provided the stabilizer issue has been removed by absolute irreducibility or by a rigidification.

### 3.5 Fixed determinant and trace zero

Assume the determinant has a fixed lift to $\mathcal O$ and every chosen matrix $\widetilde\rho(g)$ has that determinant. From (3.1),

$$
\det F(g,h)=1.
$$

For a square-zero matrix $X$,

$$
\det(1+X)=1+\operatorname{tr}(X). \tag{3.8}
$$

Therefore $\operatorname{tr}c(g,h)=0$, and the factor set takes values in

$$
M\otimes I=\operatorname{ad}^0\bar\rho\otimes I. \tag{3.9}
$$

Likewise, a correction $1+b(g)$ preserves the fixed determinant exactly when $b(g)$ is trace zero. Proposition 3.2 therefore remains valid with $M$ in place of the full adjoint.

The hypothesis that a determinant-compatible matrix lift can be chosen is harmless for a small extension when the rank is two and the residue characteristic is odd. Begin with any lift. The ratio between its determinant and the prescribed determinant lies in $1+I$. Multiplying by the scalar $1+u$ changes the determinant by $1+2u$. Since $2$ is invertible, choose $u$ to cancel the ratio. In characteristic two this adjustment fails and trace zero is not a complementary summand; that exceptional case is treated only as a boundary in Chapter 12.

### 3.6 Continuity and finite quotients

The section $g\mapsto\widetilde\rho(g)$ must be continuous. Because $A'$ is Artinian and has the discrete topology, $\operatorname{GL}_2(A')$ is finite. The image of $\rho_A$ is finite, and the quotient map

$$
\operatorname{GL}_2(A')\twoheadrightarrow
\operatorname{im}(\rho_A)
$$

admits a set-theoretic section after restricting the target to the image. Composing that section with the continuous finite-quotient map $G_{K,S}\to\operatorname{im}(\rho_A)$ gives a continuous choice. Normalize its value at the identity.

For complete coefficient rings, construct factor sets at each Artinian quotient. Compatibility under reduction can be enforced inductively because the space of sections at the next level is an affine product of square-zero fibers. Every statement about obstruction classes is made at a finite quotient and then passed through the inverse system. No assertion requires an arbitrary section of a map between infinite topological groups.

## 4. Local admissible lifts as affine torsors

### 4.1 Why local existence is not a chosen lift

Fix a place $v\in S$ and a local deformation condition $D_v$. Suppose $\rho_{A,v}$ belongs to $D_v(A)$ and (2.1) is small. Formal smoothness of $D_v$ says that at least one admissible lift to $A'$ exists. It does not choose one, and the set of choices is precisely where the global correction problem lives.

Let $L_v\subseteq H^1(K_v,M)$ be the tangent space of $D_v$. After choosing a rigidification, the difference of two admissible lifts is a $1$-cocycle whose cohomology class lies in $L_v$. Conversely, acting on one admissible lift by a cocycle representing a class of $L_v$ produces another admissible lift. Thus the local lifting set is affine under the positive local-condition complex, not merely under an abstract vector space.

This is why Book 183 retained $C_v^0(M)$ in the positive complex

$$
U_v^+(M):C_v^0(M)\xrightarrow{d}Z^1_{L_v}(M). \tag{4.1}
$$

Degree zero records changes of rigidification and degree one records admissible differences.

### 4.2 Differences of local lifts

Let $\rho'_{1,v}$ and $\rho'_{2,v}$ be two lifts of the same $\rho_{A,v}$. There is a unique function

$$
z_v:G_{K_v}\longrightarrow M\otimes I
$$

such that

$$
\rho'_{2,v}(g)=(1+z_v(g))\rho'_{1,v}(g). \tag{4.2}
$$

Comparing products shows

$$
z_v(gh)=z_v(g)+g\cdot z_v(h), \tag{4.3}
$$

so $z_v$ is a $1$-cocycle. If both lifts are admissible, $[z_v]\in L_v\otimes I$ by definition of the tangent condition. If one is strictly conjugated by $1+X$, then $z_v$ changes by $dX$.

Consequently the rigidified lift set is a torsor under $Z^1_{L_v}(M)\otimes I$, while strict-equivalence classes form a torsor under $L_v\otimes I$ when the strict automorphism action is free. We will work at the cochain level until the supported class is formed, so no quotient by automorphisms is taken prematurely.

### 4.3 The three distinguished places

For the hardly-ramified problem, the affine torsors have very different appearances.

At $2$, the fixed tame-quadratic type is formally smooth and its tangent space is zero. Under the hypothesis $\ell\ge7$, the ambient $H^1(\mathbf Q_2,M)$ is also zero. Hence any two admissible unframed lifts are strictly equivalent. A rigidified lift set may still be moved by local coboundaries; that movement is why degree zero remains present in (4.1).

At $\ell$, admissible lifts are coefficient-linear finite-flat lifts with fixed determinant. Their strict-equivalence classes form an affine torsor under

$$
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M). \tag{4.4}
$$

This is not the unramified subspace. In the Kummer model, unit directions are finite flat and are usually ramified, while the valuation direction is excluded.

At infinity, $\ell$ is odd and positive-degree cohomology of $C_2$ vanishes. Oddness fixes the conjugacy class, so there is one unframed admissible lift class and no degree-one correction. The ordinary invariant line still contributes to the global Euler formula, but it does not create a correction torsor.

### 4.4 Automorphisms and rigidifications

If $X\in H^0(K_v,M)\otimes I$, conjugation by $1+X$ fixes a local lift. Thus an unrigidified lifting set is generally a groupoid rather than a free affine space. The positive complex handles this correctly: the map $C_v^0\to Z^1_{L_v}$ sends a change of rigidification to its coboundary, and its degree-one cohomology is $L_v$.

Globally, absolute irreducibility gives

$$
H^0(G_{K,S},M)=0 \tag{4.5}
$$

in the odd two-dimensional fixed-determinant setting. This removes global trace-zero infinitesimal automorphisms. Local automorphisms can remain, especially when the local restriction is reducible, but they are retained in the local complexes and cancel in the mapping fiber. We never infer local scalar centralizers from global absolute irreducibility.

### 4.5 Functoriality under pushout

Let $I\to I'$ be a linear map and push out a small extension. Multiplying a lift by $1+z_v$ pushes forward to multiplication by the image of $z_v$. Thus the affine action commutes with pushout. If $I=I_1\oplus I_2$, the lift torsor is the product of the two torsors. These statements follow directly from (2.3).

Compatibility is also transitive. For consecutive small extensions, first correct a lift across the lower kernel and then across the upper kernel. The combined correction is the sum of the two cocycles after transporting coefficients. Since products of kernel elements vanish at each square-zero stage, no secondary term appears. This transitivity is the exact hypothesis needed in Proposition 2.1 to choose compatible lifts through the universal relation tower.

## 5. The supported relation class

### 5.1 Adding local nullhomotopies

Return to a global deformation $\rho_A$ satisfying the local conditions and a small extension $A'\twoheadrightarrow A$ with kernel $I$. Choose determinant-compatible matrix lifts globally and let

$$
c\in Z^2(G_{K,S},M)\otimes I \tag{5.1}
$$

be their factor set. At each $v\in S$, formal smoothness supplies an honest admissible local lift $\rho'^{\mathrm{adm}}_v$. Compare it with the restriction of the chosen global matrix section. There is a local $1$-cochain $b_v$ such that

$$
\rho'^{\mathrm{adm}}_v(g)
=(1+b_v(g))\widetilde\rho(g)|_{G_{K_v}}. \tag{5.2}
$$

The left side has zero factor set. Formula (3.6) therefore gives

$$
\operatorname{loc}_v(c)+db_v=0. \tag{5.3}
$$

Put $y_v=-b_v$. Then

$$
dy_v=\operatorname{loc}_v(c). \tag{5.4}
$$

Equation (5.4) is the local nullhomotopy required by the mapping-fiber differential. The point is not merely that the local cohomology class of $c$ vanishes. The cochain $y_v$ remembers which admissible local lift was used to trivialize it.

If the local deformation condition possesses its own obstruction complex rather than being formally smooth, (5.4) must be replaced by a nullhomotopy in that complex. The hardly-ramified conditions are locally liftable, so the two-term positive complexes of Book 183 are sufficient.

### 5.2 The mapping-fiber cocycle

Let

$$
U_v^-(M)=\operatorname{Cone}
\bigl(U_v^+(M)\to C^\bullet(K_v,M)\bigr)
$$

be the local quotient complex, and set

$$
Q_{\mathcal L}^\bullet(M)=\bigoplus_{v\in S}U_v^-(M).
$$

Localization followed by the quotient maps defines

$$
\lambda_{\mathcal L}:C^\bullet(G_{K,S},M)
\longrightarrow Q_{\mathcal L}^\bullet(M). \tag{5.5}
$$

The supported complex is

$$
C_{\mathcal L}^\bullet(K,M)
=\operatorname{Cone}(\lambda_{\mathcal L})[-1], \tag{5.6}
$$

with

$$
C_{\mathcal L}^q=C^q(G_{K,S},M)
\oplus Q_{\mathcal L}^{q-1}(M),
$$

$$
d_{\mathcal L}(x,y)=(dx,\lambda_{\mathcal L}(x)-dy). \tag{5.7}
$$

Map each $y_v$ from (5.4) to the local quotient complex and write the resulting family as $y$. Since $dc=0$ and $dy=\lambda_{\mathcal L}(c)$, the pair

$$
(c,y)\in C_{\mathcal L}^2(K,M)\otimes I \tag{5.8}
$$

is a cocycle. Its class

$$
\operatorname{ob}_{\mathcal L}(\rho_A,A')
=[(c,y)]\in H^2_{\mathcal L}(K,M)\otimes I \tag{5.9}
$$

is the **supported relation obstruction**.

The image of (5.9) in ordinary $H^2(G_{K,S},M)\otimes I$ is the unrestricted factor-set obstruction. Its extra local coordinate distinguishes two situations that ordinary cohomology merges: an unrestricted global lift may fail to be locally admissible, and locally admissible lifts may fail to be simultaneously reachable by one global correction.

### 5.3 Choice independence

There are three choices: the global matrix section, the admissible local lifts, and the cochains comparing them.

Change the global section by a global $1$-cochain $a$. Then $c$ changes to $c+da$. The comparison cochains change so that $y$ changes to $y+\lambda_{\mathcal L}(a)$, up to a local positive cochain. Hence

$$
(c+da,y+\lambda_{\mathcal L}(a))-(c,y)
=d_{\mathcal L}(a,0). \tag{5.10}
$$

Change an admissible local lift at $v$. Its difference from the old one is represented by an element of $Z^1_{L_v}(M)\otimes I$, hence lies in the positive local complex. Its image is zero in $U_v^-(M)$ up to a quotient coboundary. Thus the supported class is unchanged.

Finally, changing a comparison cochain without changing either lift amounts to a local infinitesimal automorphism. This is a degree-zero element of the positive complex, and again changes $y$ by a quotient coboundary. Therefore (5.9) is independent of every choice. Strict conjugacy of $\rho_A$ is handled by the same calculation with a global degree-zero cochain.

### 5.4 Completeness of the obstruction

**Theorem 5.1 (supported completeness).** The class (5.9) vanishes if and only if $\rho_A$ lifts to a global deformation over $A'$ satisfying all local conditions.

**Proof.** If an admissible global lift exists, use it as the global section and use its restrictions as the local admissible lifts. Then $c=0$ and $y=0$.

Conversely, suppose $[(c,y)]=0$. There is a degree-one supported cochain $(a,z)$ such that

$$
(c,y)=d_{\mathcal L}(a,z)
=(da,\lambda_{\mathcal L}(a)-dz). \tag{5.11}
$$

Correct the global matrix section by $-a$. Formula (3.6) makes its factor set zero, so it becomes an honest global representation $\rho_{A'}$. Its local mismatch from the previously chosen admissible lift is represented in the quotient complex by

$$
y-\lambda_{\mathcal L}(a)=-dz. \tag{5.12}
$$

Thus that mismatch is zero in local quotient cohomology. Equivalently, after modifying by a local positive cochain, the restriction of $\rho_{A'}$ is an admissible local lift. The modification is a strict local conjugacy together with an admissible tangent displacement, both of which preserve membership in $D_v$. Hence $\rho_{A'}$ satisfies every local condition. $\square$

The last step is where the positive complex is essential. If one retained only the statement $[c]=0$ locally, the correction $a$ could land outside $L_v$ and the conclusion would not follow.

### 5.5 Additivity and base change

Every operation in (5.8) is linear in $I$: the factor set is linear by (2.3), local comparison cochains add, quotient maps are linear, and the mapping-fiber differential is linear. A map $I\to I'$ carries (5.9) to the obstruction of the pushed-out small extension. Direct sums of kernels carry obstructions to direct sums.

If $k\subset k'$ is a finite field extension and the local conditions base-change, flatness gives

$$
H^2_{\mathcal L}(K,M)\otimes_k k'
\simeq H^2_{\mathcal L\otimes k'}(K,M\otimes_k k'). \tag{5.13}
$$

The supported obstruction maps correspond under (5.13). This statement concerns extension of the fixed residue field. Reduction of a lattice or change of residue characteristic is not flat in the required sense and will not be treated as the same operation.

## 6. Correction torsors and localization defects

### 6.1 Mismatch classes

Suppose first that the unrestricted obstruction $[c]$ vanishes, so an honest global lift $\rho'_{\mathrm{glob}}$ exists. Choose an admissible local lift $\rho'^{\mathrm{adm}}_v$ at every controlled place. Their difference defines

$$
q_v\in H^1(K_v,M)\otimes I. \tag{6.1}
$$

Changing the admissible local lift moves $q_v$ by $L_v\otimes I$. Thus the intrinsic mismatch is its class

$$
\overline q_v\in
\bigl(H^1(K_v,M)/L_v\bigr)\otimes I. \tag{6.2}
$$

Changing the global lift by a global class $x\in H^1(G_{K,S},M)\otimes I$ changes the family by the localization of $x$. Put

$$
Q_{\mathcal L}(M)
=\bigoplus_{v\in S}H^1(K_v,M)/L_v. \tag{6.3}
$$

Then the existence of a globally corrected admissible lift is equivalent to

$$
\overline q\in
\operatorname{im}\left(
H^1(G_{K,S},M)\longrightarrow Q_{\mathcal L}(M)
\right)\otimes I. \tag{6.4}
$$

This is the affine form of the degree-one localization problem.

### 6.2 The affine correction target

Let

$$
D_{\mathcal L}(M)=\operatorname{coker}\left(
H^1(G_{K,S},M)\to Q_{\mathcal L}(M)
\right). \tag{6.5}
$$

The class of $\overline q$ in $D_{\mathcal L}(M)\otimes I$ is independent of every global and local base point. It is the **affine correction obstruction**. It vanishes exactly when the chosen local lift torsors contain restrictions of one global lift.

The supported degree-two exact sequence explains its relation to (5.9):

$$
0\longrightarrow D_{\mathcal L}(M)
\longrightarrow H^2_{\mathcal L}(K,M)
\longrightarrow\Sha_S^2(K,M)\longrightarrow0, \tag{6.6}
$$

where

$$
\Sha_S^2(K,M)=\ker\left(
H^2(G_{K,S},M)\to\bigoplus_{v\in S}\widetilde H^2(K_v,M)
\right). \tag{6.7}
$$

The left term measures failure to correct local lift choices after an unrestricted global lift exists. The right term measures an ordinary global obstruction that is locally zero. Supported degree two contains both and remembers their extension.

### 6.3 The exact Poitou–Tate functional

Let

$$
\operatorname{Sel}_{\mathcal L^\perp}(M')
=H^1_{\mathcal L^\perp}(K,M'). \tag{6.8}
$$

For $\overline q=(q_v+L_v)_v\in Q_{\mathcal L}(M)$ define

$$
\Theta_{\mathcal L}(\overline q)(y)
=\sum_{v\in S}
\operatorname{inv}_v\bigl(q_v\smile\operatorname{loc}_v(y)\bigr),
\qquad y\in\operatorname{Sel}_{\mathcal L^\perp}(M'). \tag{6.9}
$$

The expression is well defined. Replacing $q_v$ by an element of $L_v$ changes no value because $\operatorname{loc}_v(y)\in L_v^\perp$. Only finitely many places occur. At a real place the modified invariant is retained; in the hardly-ramified odd-coefficient problem the positive-degree term vanishes.

Poitou–Tate exactness gives

$$
H^1(G_{K,S},M)\longrightarrow Q_{\mathcal L}(M)
\xrightarrow{\Theta_{\mathcal L}}
\operatorname{Sel}_{\mathcal L^\perp}(M')^*
\longrightarrow H^2(G_{K,S},M). \tag{6.10}
$$

Therefore

$$
\overline q\text{ is globally correctable}
\quad\Longleftrightarrow\quad
\Theta_{\mathcal L}(\overline q)=0. \tag{6.11}
$$

This is the exact reciprocity criterion for affine correction targets.

### 6.4 What surjectivity does and does not say

The map $\Theta_{\mathcal L}$ need not be onto the whole dual of the dual Selmer group. Its cokernel maps into global $H^2$. More precisely,

$$
D_{\mathcal L}(M)
\simeq\ker\left(
\operatorname{Sel}_{\mathcal L^\perp}(M')^*
\to H^2(G_{K,S},M)
\right). \tag{6.12}
$$

Equivalently,

$$
D_{\mathcal L}(M)^*
\simeq
\operatorname{Sel}_{\mathcal L^\perp}(M')/
\Sha_S^1(K,M'), \tag{6.13}
$$

where $\Sha_S^1$ denotes the everywhere locally trivial subgroup. Thus correction mismatches are tested perfectly by dual Selmer classes modulo those that have zero localization everywhere.

It would be false to replace (6.12) by an unconditional isomorphism
$D_{\mathcal L}(M)\simeq\operatorname{Sel}_{\mathcal L^\perp}(M')^*$.
The larger supported group, however, does satisfy

$$
H^2_{\mathcal L}(K,M)
\simeq\operatorname{Sel}_{\mathcal L^\perp}(M')^*. \tag{6.14}
$$

This is why relation factor sets naturally land in supported degree two rather than only in the affine correction cokernel.

## 7. Reciprocity for correction targets

### 7.1 The local sum

The functional (6.9) combines four operations:

$$
\text{localization},\qquad
\text{evaluation }M\otimes M'\to\mu_n,\qquad
\text{cup product},\qquad
\operatorname{inv}_v. \tag{7.1}
$$

The Tate twist in $M'$ is forced by the evaluation target. Local cup product has total degree two, so the invariant is defined. The order of the entries fixes a sign convention; reversing them introduces the usual degree-one minus sign together with any symmetry sign of the coefficient pairing.

The sum is not an arbitrary aggregation of local tests. A global class in the first variable must pair to zero with a global class in the second. The proof is global Brauer reciprocity.

### 7.2 Global families give zero

Let $x\in H^1(G_{K,S},M)$ and $y\in H^1(G_{K,S},M')$. Naturality of cup products gives

$$
\operatorname{loc}_v(x\smile y)
=\operatorname{loc}_v(x)\smile\operatorname{loc}_v(y). \tag{7.2}
$$

The global cup $x\smile y$ maps through evaluation to a class in $H^2(G_{K,S},\mu_n)$ and hence to an $n$-torsion Brauer class of $K$. Outside $S$ both classes are unramified; their cup inflates from the residue-field Galois group, whose degree-two cohomology is zero. Thus only $S$ contributes. Global Brauer reciprocity gives

$$
\sum_{v\in S}\operatorname{inv}_v
\bigl(\operatorname{loc}_v(x)\smile\operatorname{loc}_v(y)\bigr)=0. \tag{7.3}
$$

It follows that $\Theta_{\mathcal L}$ kills the image of global localization. This proves the easy containment in (6.10). It does not prove the reverse containment; that is the perfectness part of Poitou–Tate duality.

### 7.3 Exactness of the correction criterion

We recall the argument establishing the reverse containment in the precise degree needed here. Local Tate duality identifies

$$
Q_{\mathcal L}(M)^*
\simeq\bigoplus_{v\in S}L_v^\perp. \tag{7.4}
$$

Under this identification the transpose of localization is the map

$$
\operatorname{Sel}_{\mathcal L^\perp}(M')
\longrightarrow\bigoplus_{v\in S}L_v^\perp. \tag{7.5}
$$

Compactly supported global duality identifies the cone of the first map with the shifted dual cone of the second. Taking cohomology in the middle degrees gives the exact annihilator identity

$$
\operatorname{im}\left(H^1(G_{K,S},M)\to Q_{\mathcal L}(M)\right)^\perp
=\operatorname{im}(7.5). \tag{7.6}
$$

Finite-dimensional biduality now yields

$$
\ker\Theta_{\mathcal L}
=\operatorname{im}\left(H^1(G_{K,S},M)\to Q_{\mathcal L}(M)\right), \tag{7.7}
$$

which is (6.11). Notice the order of reasoning: reciprocity constructs the containment, global duality proves that there is no additional functional, and finite-dimensionality converts the annihilator equality into the kernel equality.

### 7.4 Changes of representatives and signs

If $q_v$ changes by $\operatorname{loc}_v(x)$ for a global class $x$, equation (7.3) shows that (6.9) is unchanged. If $q_v$ changes by $l_v\in L_v$, exact orthogonality makes the $v$th summand unchanged. If $y$ changes by a coboundary, the local cup changes by a coboundary and its invariant is unchanged.

Corestriction and restriction are adjoint:

$$
\langle\operatorname{res}_{L_w/K_v}a,b\rangle_w
=\langle a,\operatorname{cor}_{L_w/K_v}b\rangle_v. \tag{7.8}
$$

No local degree occurs in (7.8). Restricting both entries instead multiplies the invariant by $[L_w:K_v]$. These formulas ensure that correction functionals commute with finite extension of the base field and with Shapiro identifications.

## 8. A proof of the required global Brauer reciprocity

### 8.1 The precise theorem needed here

The correction construction uses the following result.

**Theorem 8.1 (global Brauer reciprocity).** For a number field $K$, localization and the normalized local invariants form an exact sequence

$$
0\longrightarrow\operatorname{Br}(K)
\longrightarrow\bigoplus_v\operatorname{Br}(K_v)
\xrightarrow{\sum_v\operatorname{inv}_v}\mathbf Q/\mathbf Z
\longrightarrow0. \tag{8.1}
$$

At a real place the nonzero quaternion class has invariant $1/2$; at a complex place the group is zero. Every global class has finite support. For the argument of Chapter 7, exactness at the middle term is stronger than necessary for the zero-sum identity but is exactly what supplies the compactly supported trace used in Poitou–Tate duality.

We now prove (8.1). The proof is organized around idèles, but every needed cohomological step is included. Write $J_L$ for the idèle group and $C_L=J_L/L^\times$ for the idèle class group of a finite Galois extension $L/K$ with group $G$.

### 8.2 Finite support

Let $A$ be a central simple $K$-algebra representing a Brauer class. Choose a $K$-basis and structure constants. After clearing denominators, there is a finite set $T$ of finite places and an algebra $\mathcal A$ over $\mathcal O_{K,T}$ whose generic fiber is $A$. Enlarge $T$ until the determinant expressing separability of the multiplication algebra is a unit. Then $\mathcal A$ is Azumaya outside $T$.

For $v\notin T$, reduce modulo $v$. The fiber is a central simple algebra over the finite residue field $k_v$. Every finite division ring is commutative, so every central simple algebra over $k_v$ is a matrix algebra. Henselian lifting of matrix units then splits $A\otimes_KK_v$. Hence the localization is zero for all $v\notin T$. There are only finitely many archimedean places, proving finite support.

The lifting of matrix units is elementary. If $\overline e_{ij}$ are matrix units in the residue algebra, lift the diagonal idempotents successively by Hensel's lemma applied to $X^2-X$, then lift the off-diagonal rank-one bimodule generators. Their multiplication constants are units and can be normalized. Completeness gives genuine matrix units in $\mathcal A\otimes\mathcal O_{K_v}$.

### 8.3 Cyclic relative classes

Let $L/K$ be cyclic of degree $m$, with generator $\sigma$. The standard periodic resolution gives

$$
H^2(G,L^\times)\simeq K^\times/N_{L/K}L^\times. \tag{8.2}
$$

The class of $a\in K^\times$ is represented by the cyclic algebra

$$
(L/K,\sigma,a)
=\bigoplus_{i=0}^{m-1}Lu^i,\qquad
u\lambda=\sigma(\lambda)u,\qquad u^m=a. \tag{8.3}
$$

To prove (8.2), a normalized $2$-cocycle is reduced by a coboundary until its only nontrivial carry occurs when exponents cross $m$; that carry is an invariant element $a\in K^\times$. A further coboundary changes $a$ by the norm of its value on $\sigma$. This gives (8.2), and multiplication of factor sets corresponds to multiplication of the parameters.

For a place $v$ of $K$ and a chosen $w\mid v$, the localization of (8.3) is the cyclic algebra for $L_w/K_v$, repeated according to the decomposition of $L\otimes_KK_v$. Let

$$
\operatorname{rec}_{v}:K_v^\times\longrightarrow G_w^{\mathrm{ab}}
$$

be arithmetic local reciprocity and let $\chi:G\to\frac1m\mathbf Z/\mathbf Z$ send $\sigma$ to $1/m$. The local cyclic-algebra calculation gives

$$
\operatorname{inv}_v(L_w/K_v,\sigma_v,a)
=\chi_v(\operatorname{rec}_v(a)), \tag{8.4}
$$

where $\chi_v$ is the restriction of $\chi$ to the decomposition group, with corestriction over the components understood. Formula (8.4) follows by checking a uniformizer in the unramified case, units in the totally ramified case, and then using the unramified–ramified tower. Norms have value zero by the projection formula, and both sides identify the same quotient $K_v^\times/NL_w^\times$ with the decomposition group.

### 8.4 The principal-idèle product law

We require one idelic theorem and prove it in the form used here.

**Lemma 8.2 (idele class theorem).** For every finite Galois extension $L/K$ with group $G$,

$$
H^1(G,C_L)=0. \tag{8.5}
$$

For cyclic $L/K$ one also has

$$
|C_K/N_{L/K}C_L|=[L:K]. \tag{8.6}
$$

**Proof.** We give the cyclic proof first. Choose a finite set $T$ containing the archimedean and ramified places. The valuation sequence for $T$-idèles separates $J_L$ into the product of local unit groups and the free divisor group on places outside $T$. The latter is a permutation $G$-module. Shapiro's lemma and local Hilbert 90 give

$$
H^1(G,J_L)=0. \tag{8.7}
$$

The Herbrand quotient is multiplicative in the exact sequence

$$
1\to L^\times\to J_L\to C_L\to1. \tag{8.8}
$$

The divisor permutation modules contribute the product of decomposition-group orders. The local unit filtrations contribute the reciprocal product of ramification indices; successive principal-unit quotients are induced additive residue modules and have Herbrand quotient one. Dirichlet's unit theorem identifies the remaining archimedean lattice contribution. Cancelling decomposition degrees by

$$
\sum_{w\mid v}e_wf_w=[L:K]
$$

gives

$$
h_G(C_L)=|G|, \tag{8.9}
$$

where $h_G(C_L)=|\widehat H^0(G,C_L)|/|\widehat H^{-1}(G,C_L)|$.

It remains to determine the numerator. Idelic approximation shows that $N C_L$ is open in $C_K$, so the quotient is finite. The first norm inequality follows by applying the ambiguous ideal-class sequence to (8.8): its alternating order, together with the unit lattice calculation above, gives

$$
|C_K/NC_L|\ge |G|. \tag{8.10}
$$

The reverse inequality is most cleanly obtained from the finite units–divisors–ideal-classes calculation given later in this chapter. That calculation is logically independent of the present idelic argument and proves (8.30) directly. Apply its injectivity over the fixed field $E=L^H$ of every subgroup $H\leq G$. The cohomology sequence of (8.8), Shapiro's identification of idèle cohomology, and Hilbert 90 identify

$$
H^1(H,C_L)
\hookrightarrow
\ker\left(
H^2(H,L^\times)\to
\bigoplus_uH^2(H_z,L_z^\times)
\right). \tag{8.11}
$$

The kernel on the right is zero by the injectivity in (8.30), applied over $E$. Thus $H^1(H,C_L)=0$ for every $H$. In particular $\widehat H^{-1}(G,C_L)=0$ when $G$ is cyclic. Equation (8.9) then gives

$$
|C_K/NC_L|=|G|. \tag{8.12}
$$

Thus (8.6) holds. Since

$$
\widehat H^0(G,C_L)=C_K/NC_L,
$$

(8.9) forces $\widehat H^{-1}(G,C_L)=0$, which is $H^1(G,C_L)$ for a cyclic group.

There is also a purely group-theoretic passage from the cyclic vanishing to the arbitrary-group vanishing. If $N\triangleleft G$ and $E=L^N$, extension of idèles gives

$$
J_E\xrightarrow{\sim}J_L^N. \tag{8.13}
$$

Indeed, on the factors above a place $v$ this is the elementary identification

$$
\left(\prod_{w\mid v}L_w^\times\right)^N=E_{v'}^\times
$$

for the places $v'$ of $E$ over $v$; the restricted-product unit conditions agree. Taking $N$-invariants in $1\to L^\times\to J_L\to C_L\to1$ and using Hilbert 90 gives

$$
C_E\xrightarrow{\sim}C_L^N. \tag{8.14}
$$

Now let $P$ be a $p$-group. Its center contains a normal subgroup $N$ of order $p$. Inflation–restriction, (8.14), and the cyclic case give

$$
0=H^1(P/N,C_E)\longrightarrow H^1(P,C_L)
\longrightarrow H^1(N,C_L)^{P/N}=0. \tag{8.15}
$$

Induction on $|P|$ proves $H^1(P,C_L)=0$. Finally take the $p$-primary part of a class in $H^1(G,C_L)$ and restrict it to a Sylow $p$-subgroup $P$. It restricts to zero, while corestriction after restriction is multiplication by $[G:P]$. Inner automorphisms act trivially on cohomology, so the usual restriction–corestriction formula applies. Since $[G:P]$ is prime to $p$, the original $p$-primary class is zero. This for every $p\mid |G|$ proves (8.5). $\square$

The logical order should be noted. Equations (8.9)–(8.15) explain the idelic consequences, while the independent finite calculation culminating in (8.30) supplies their arithmetic input. Thus neither the norm index nor a local-prescription theorem is being used to prove that same finite calculation.

Now apply cohomology to (8.8). By (8.5) and (8.7), localization induces an injection

$$
H^2(G,L^\times)\hookrightarrow H^2(G,J_L). \tag{8.16}
$$

Choose one $w$ above each $v$. The restricted product defining $J_L$ has, in positive degree,

$$
H^2(G,J_L)\simeq
\bigoplus_v H^2(G_w,L_w^\times). \tag{8.17}
$$

Indeed, for a sufficiently large finite $T$, the $T$-idèle factors are coinduced local multiplicative modules, so Shapiro gives the direct sum. Enlarging $T$ adds unramified unit factors, whose positive cohomology vanishes by the unit filtration. Hence every class stabilizes in a finite direct sum.

For cyclic $L/K$, combine (8.2), (8.4), and the equality in the norm-index theorem. The product of the local reciprocity images of a principal idèle $a\in K^\times$ lies in $G$ and annihilates every character of $G$: otherwise the corresponding character would define a norm quotient larger than the cyclic quotient of order $|G|$. Therefore

$$
\prod_v\operatorname{rec}_v(a)=1. \tag{8.18}
$$

Applying $\chi$ and using (8.4) gives

$$
\sum_v\operatorname{inv}_v(L/K,\sigma,a)=0. \tag{8.19}
$$

This proves the zero-sum law for every cyclic relative Brauer class.

### 8.5 The relative invariant sequence

The cyclic calculation extends to arbitrary finite Galois splitting fields through the following class-formation lemma. We include the passage because it avoids any assertion that a Brauer class must possess a cyclic splitting field.

**Lemma 8.3 (relative invariant sequence).** Let $L/K$ be finite Galois with group $G$, and choose one place $w$ of $L$ above every place $v$ of $K$. Then

$$
H^2(G,L^\times)\longrightarrow
\bigoplus_v H^2(G_w,L_w^\times)
\xrightarrow{\ \sum\operatorname{inv}_v\ }
\mathbf Q/\mathbf Z \tag{8.20}
$$

is exact at the middle term. The first arrow is injective. Its image, and every element in the middle term, has finite support.

**Proof.** Injection is (8.16), and (8.17) identifies its target. Apply cohomology to $1\to L^\times\to J_L\to C_L\to1$. Since $H^1(G,C_L)=H^1(G,J_L)=0$, the relevant part is

$$
0\longrightarrow H^2(G,L^\times)
\longrightarrow H^2(G,J_L)
\xrightarrow{\delta_G}H^2(G,C_L). \tag{8.21}
$$

We must identify the quotient detected by $\delta_G$. If $G$ is cyclic of order $d$, periodicity and (8.6) give

$$
H^2(G,C_L)=\widehat H^0(G,C_L)
=C_K/NC_L,\qquad |H^2(G,C_L)|=d. \tag{8.22}
$$

The sum of local invariants has image in $\frac1d\mathbf Z/\mathbf Z$. The finite calculation culminating in (8.30) shows directly that its induced image has order $d$; this order computation uses units, divisors, and ideal classes and requires no prescribed-Frobenius prime. Equation (8.19) says that the sum kills the image of the global relative group. Both its induced target and the cokernel in (8.22) therefore have order $d$, so its kernel is exactly the global image.

For general $G$, the same conclusion is obtained primary part by primary part. Here are the details of the descent. Let $P$ be a Sylow $p$-subgroup and $E=L^P$. Restriction of (8.21) to $P$ is compatible with localization; on local summands it is the sum over places of $E$ above $v$. The local restriction formula

$$
\operatorname{inv}_{u}(\operatorname{res}\gamma)
=[E_u:K_v]\operatorname{inv}_v(\gamma) \tag{8.23}
$$

and the fundamental equality $\sum_{u\mid v}[E_u:K_v]=[E:K]$ show that the restricted invariant sum is $[G:P]$ times the original sum. The same formula holds on the global term. A finite cohomology class of $p$-power order is detected after restriction to $P$, because corestriction after restriction is multiplication by $[G:P]$.

It remains only to know the assertion for a $p$-group. Choose a central subgroup $N$ of order $p$. The Hochschild–Serre sequences for $L^\times$, $J_L$, and $C_L$, placed in three rows, form a commutative diagram. The outside terms for $N$ and $P/N$ have the asserted kernels by the cyclic case and induction; (8.13)–(8.15) identify the invariant idèle and idèle-class terms. A diagram chase now proves the middle row: explicitly, restrict a zero-sum local class to $N$, subtract a global class lifting it by the cyclic case, and observe that the difference is $N$-invariant. Under (8.13) it descends to $L^N$; its invariant sum is still zero by (8.23), so induction on $P/N$ supplies a global lift. Inflating and adding the first lift gives the required class for $P$. The converse follows at each step from (8.19). Induction proves the statement for $P$, and Sylow detection proves it for $G$. This proves exactness. $\square$

We record a finite-order verification of the same exactness. Besides checking the class-formation argument, it makes clear why no exceptional local-prescription theorem is hidden in Lemma 8.3. Fix $n\geq1$ and a finite set $T$ containing the archimedean places and all places above $n$. Put

$$
A_n=\mathbf Z/n\mathbf Z,
\qquad A_n^D=\mu_n. \tag{8.24}
$$

For either member $A$ of this dual pair, form

$$
C_{T,c}^\bullet(A)=
\operatorname{Cone}\left(
C^\bullet(G_{K,T},A)\longrightarrow
\bigoplus_{v\in T}C^\bullet(K_v,A)
\right)[-1], \tag{8.25}
$$

with complete cochains at real places. Local cup products give pairings

$$
H^i(C_{T,c}^\bullet(A_n))
\times H^{3-i}(G_{K,T},\mu_n)
\longrightarrow \tfrac1n\mathbf Z/\mathbf Z. \tag{8.26}
$$

We prove directly, in the degrees used here, that these pairings are perfect. The Kummer and valuation sequences give

$$
0\longrightarrow
\mathcal O_{K,T}^\times/\mathcal O_{K,T}^{\times n}
\longrightarrow H^1(G_{K,T},\mu_n)
\longrightarrow\operatorname{Cl}(\mathcal O_{K,T})[n]
\longrightarrow0. \tag{8.27}
$$

The first map sends a unit to its Kummer torsor. For the second, the divisor of a Kummer representative has all coefficients divisible by $n$ outside $T$; dividing those coefficients by $n$ produces an ideal class killed by $n$. Changing the representative changes that ideal by a principal ideal. Conversely, an ideal whose $n$th power is principal supplies a Kummer class. This proves exactness of (8.27), rather than merely quoting it.

There is a dual filtration for $A_n$-valued characters. Its unramified part is a character of the $T$-ideal class group; its inertia values pair with $T$-units; and its Frobenius values pair with the free divisor group outside $T$. The only relation among the Frobenius coordinates is the principal-divisor relation. To see this without a reciprocity assumption, choose a finite list of primes and prescribe residues of an element at those primes by the Chinese remainder theorem. The valuation of a principal element is its principal divisor, and the ordinary product formula supplies its one archimedean relation. Thus the character is determined by the displayed unit, divisor, and class-group coordinates.

The pairings on the associated graded pieces are elementary perfect pairings. They are

$$
\begin{array}{c|c}
\text{Kummer piece}&\text{character piece}\\ \hline
\mathcal O_{K,T}^\times/mathcal O_{K,T}^{\times n}
&\operatorname{Hom}(\mathcal O_{K,T}^\times,	frac1n\mathbf Z/\mathbf Z)\\
\text{divisors modulo }n&\text{finite Frobenius coordinates}\\
\operatorname{Cl}(\mathcal O_{K,T})[n]
&\operatorname{Cl}(\mathcal O_{K,T})/n
\end{array} \tag{8.28}
$$

with the sides interchanged after dualizing. The class-group pairing is ordinary finite Pontryagin duality. For units, Dirichlet's theorem writes the free part as a lattice of rank $r_1+r_2+|T_f|-1$; the one missing rank is precisely the product-formula relation. Torsion units pair with their finite character group. At each finite completion, local reciprocity and Kummer theory identify the two local groups with a finite abelian group and its full character group. At a real place the two-term Tate resolution gives a perfect pairing of order two, and at a complex place both positive-degree groups vanish.

It remains to check that the graded pairings are induced by cup product with the claimed sign. For a unit $u$ and a local character $c_v$, the inhomogeneous cup cocycle evaluates to

$$
\operatorname{inv}_v(c_v\smile u)
=c_v(\operatorname{rec}_v(u)). \tag{8.29}
$$

For a uniformizer this is the arithmetic Frobenius value; for a unit it is the inertia value. Bilinearity proves the formula for every local element. On a diagonal global element, the valuation contributions cancel because a principal divisor has degree zero, the residue-unit contributions cancel in each finite residue field by the norm identity, and the remaining signs at real places are the archimedean part of the ordinary product formula. Thus the sum of the local cup values is zero. This is a cochain calculation using the three rows in (8.28), not an appeal to the Brauer sequence being proved.

The filtrations are finite. Perfectness on every associated graded piece and the five lemma therefore prove perfectness of (8.26) when $\mu_n\subset K$. For general $K$, pass to $K(\mu_n)$. The Hochschild–Serre double complexes for $A_n$ and $\mu_n$ are dual under restriction and corestriction. Apply the calculation just made in every row of a complete resolution and descend along the total-degree filtration. This argument does not divide by $[K(\mu_n):K]$; consequently it remains valid when that degree has a common factor with $n$. At real places the complete resolution retains the degree-zero Tate term, which is exactly the extra dyadic contribution.

Enlarge $T$ through all finite sets containing the initially required places. A cohomology class and a finitely supported local family occur at some finite stage, so the directed limit introduces no product in place of the direct sum. The long exact sequence of (8.25), paired perfectly with the ordinary complex, now contains

$$
0\longrightarrow H^2(K,\mu_n)
\longrightarrow\bigoplus_v H^2(K_v,\mu_n)
\xrightarrow{\sum\operatorname{inv}_v}
\operatorname{Hom}(H^0(K,A_n),\mathbf Q/\mathbf Z)
\longrightarrow0. \tag{8.30}
$$

The left zero follows from the degree-one dual statement: an $A_n$-valued global character trivial at every completion cuts out a finite cyclic extension split at every place, hence the trivial extension. For clarity, the last implication follows from ideal counting. A nontrivial degree-$d$ extension split everywhere would have, outside finitely many factors, a Dedekind zeta function with pole of order $d$, while lattice counting of integral ideals in Minkowski space gives a simple pole for every number field.

Hilbert 90 and the Kummer sequence identify the first two nonzero groups in (8.30) with $\operatorname{Br}(K)[n]$ and $\bigoplus_v\operatorname{Br}(K_v)[n]$. Also $H^0(K,A_n)=A_n$, so evaluation at $1$ identifies the last group with $\frac1n\mathbf Z/\mathbf Z$. Thus (8.30) is exactly the $n$-torsion part of the invariant sequence. This finite calculation proves the kernel and the unique sum relation simultaneously, including the dyadic real terms.

We can now close the two promised deductions without any idelic circularity. First consider Lemma 8.3. A finitely supported relative local family of exponent dividing $n$ and invariant sum zero is the localization of a class $\beta\in\operatorname{Br}(K)[n]$ by (8.30). Every member of the family becomes zero over the corresponding completion of $L$. Hence the restriction $\beta_L$ has zero localization at every place of $L$. Apply the left injectivity of (8.30) over $L$ to conclude that $\beta_L=0$. Therefore

$$
\beta\in\ker\bigl(\operatorname{Br}(K)\to\operatorname{Br}(L)\bigr)
=H^2(G,L^\times),
$$

so $\beta$ is the required relative global lift. Conversely, the localization of a relative global class is relative everywhere, and (8.30) makes its invariant sum zero. This proves exactness in Lemma 8.3. Its left injectivity follows in the same way: a relative global class with zero relative localizations is a global Brauer class with zero localization everywhere.

Second, apply this injectivity to the right side of (8.11). It vanishes for every subgroup $H$, so $H^1(H,C_L)=0$. For cyclic $H$, the Herbrand quotient calculation (8.9) then gives the norm index (8.6). This completes the proof of every assertion made in Lemma 8.2 and also confirms that the earlier class-formation diagram has exactly the kernel claimed.

Every central simple algebra has a finite Galois splitting field: choose a maximal separable commutative subfield of a division algebra in its Brauer class and take its normal closure. Hence a class $\beta\in\operatorname{Br}(K)$ belongs to $H^2(G,L^\times)$ for some finite Galois $L/K$. Lemma 8.3 gives

$$
\sum_v\operatorname{inv}_v(\beta_v)=0. \tag{8.31}
$$

It also proves left exactness in (8.1). If every $\beta_v$ vanishes, its image in $H^2(G,J_L)$ is zero, and injection (8.16) gives $\beta=0$.

### 8.6 Real places and the prime two

At a real place,

$$
\operatorname{Br}(\mathbf R)\simeq\mathbf Z/2\mathbf Z,
$$

generated by the Hamilton quaternion algebra, and its nonzero invariant is $1/2$. At a complex place the Brauer group is zero. If a real place of $K$ becomes complex in a finite extension, restriction kills the real class and multiplies its invariant by the local degree two:

$$
2\cdot\frac12=0\quad\text{in }\mathbf Q/\mathbf Z.
$$

Thus the restriction rule remains valid. Lemma 8.3 includes the real relative group and the restriction to a complex completion, so (8.31) retains every $1/2$ term. No separate globalization at the real places is needed.

This is exactly the modification required for $2$-primary coefficients in Poitou–Tate duality. For the hardly-ramified application $\ell$ is odd, so complete cohomology at the real place is acyclic; nevertheless the proof of Theorem 8.1 itself must cover the prime two.

### 8.7 Exactness at the correction target

It remains to prove surjectivity and middle exactness in (8.1). Surjectivity of the final arrow is immediate: at one nonarchimedean place $v$, choose the unique local Brauer class with a prescribed invariant $r\in\mathbf Q/\mathbf Z$, and put zero at every other place. Middle exactness asserts that every finite family with sum zero is global.

Let $(\alpha_v)$ be such a family, supported on $T$. For each $v\in T$, choose a finite separable splitting field $E_v/K_v$ and a primitive polynomial for it. Approximate that polynomial coefficientwise by a polynomial over $K$. If the approximation is sufficiently close at $v$, Krasner's lemma embeds $E_v$ into a completion of the global splitting field. Do this separately for every $v\in T$, take the compositum of the finitely many resulting global fields, and then take its normal closure. We obtain a finite Galois extension $L/K$ whose completions contain all the chosen $E_v$. Thus each $\alpha_v$ belongs to the relative group $H^2(G_w,L_w^\times)$, and the family defines

$$
\alpha\in H^2(G,J_L) \tag{8.32}
$$

through (8.17).

The long exact sequence of (8.8) continues

$$
H^2(G,L^\times)\longrightarrow H^2(G,J_L)
\longrightarrow H^2(G,C_L). \tag{8.33}
$$

Its invariant sum is zero. Lemma 8.3 therefore lifts $\alpha$ to a class in $H^2(G,L^\times)$, hence to a Brauer class of $K$ with exactly the prescribed localizations. This proves middle exactness. Together with the one-place construction above, it proves Theorem 8.1. $\square$

The proof supplied precisely the global input used in Chapters 6 and 7: finite support, vanishing of the sum on global cups, and the absence of another relation among finite local invariant families.

## 9. Universal obstructions attached to relations

### 9.1 The universal factor-set tensor

Let $R=P/J$ be the minimal presentation (1.6) and put

$$
\mathcal R=J/\mathfrak nJ. \tag{9.1}
$$

At a sufficiently deep Artinian level, the universal relation extension is

$$
0\longrightarrow\mathcal R
\longrightarrow P/\mathfrak nJ
\longrightarrow R\longrightarrow0. \tag{9.2}
$$

Lift the matrices of the universal representation set-theoretically through (9.2), choose admissible local lifts, and apply Chapter 5. The result is a universal class

$$
\Omega_R\in H^2_{\mathcal L}(K,M)\otimes_k\mathcal R. \tag{9.3}
$$

This tensor is independent of all matrix and local choices. It is also independent of a basis of $\mathcal R$. If

$$
\Omega_R=\sum_{i=1}^r\omega_i\otimes f_i
$$

in one basis, and $f'_j=\sum_i a_{ij}f_i$, then the coordinate classes transform by the inverse matrix. The tensor itself remains fixed.

The two components of $\Omega_R$ have clear meanings. Its image in

$$
H^2(G_{K,S},M)\otimes\mathcal R
$$

is the ordinary universal multiplication defect. Its image in the quotient described by (6.6) records the failure of locally admissible universal lifts to be reachable by one global correction. Neither component alone is a complete obstruction for the constrained problem.

### 9.2 The obstruction map from relation functionals

Contract (9.3) with a functional $\lambda\in\mathcal R^*$:

$$
\operatorname{ob}_R(\lambda)
=(1\otimes\lambda)(\Omega_R)
\in H^2_{\mathcal L}(K,M). \tag{9.4}
$$

This is exactly the obstruction obtained by pushing the universal relation extension out along $\lambda$. Indeed, factor sets, local comparison cochains, and mapping fibers all commute with pushout. Thus (9.4) agrees with the abstract map (2.13), now with the explicit complete obstruction space

$$
V=H^2_{\mathcal L}(K,M). \tag{9.5}
$$

The construction is linear. If $\lambda=a\lambda_1+b\lambda_2$, the pushed-out square-zero kernel is the corresponding linear combination, and (2.3) gives

$$
\operatorname{ob}_R(\lambda)
=a\operatorname{ob}_R(\lambda_1)
+b\operatorname{ob}_R(\lambda_2). \tag{9.6}
$$

**Worked one-relation model.** Let $R=k[[X]]/(X^m)$ with $m\ge2$. The universal relation space is generated by $f=X^m$. At the Artinian level where $X^m$ first survives as a square-zero kernel, an attempted lift of the universal image of $X$ evaluates $f$ to that kernel generator. The unique nonzero functional on $kf$ produces the obstruction to imposing $X^m=0$. If its supported class vanished, the universal point would lift after deleting $X^m$, contradicting the definition of $R$. Thus the one relation produces a nonzero supported obstruction even though its first derivative is zero.

### 9.3 Proof of injectivity

**Theorem 9.1 (relation injection).** The map

$$
\operatorname{ob}_R:\mathcal R^*
\longrightarrow H^2_{\mathcal L}(K,M) \tag{9.7}
$$

is injective.

**Proof.** Theorem 5.1 makes supported degree two a complete obstruction space: vanishing is sufficient for a global lift satisfying all local conditions. Sections 3.3 and 5.5 prove functoriality and additivity. Section 4.5 proves compatibility of the affine lift actions with pushout and with consecutive small extensions. Therefore every hypothesis of Proposition 2.1 is satisfied, and (9.7) is injective.

It is useful to see the contradiction in the present notation. If $0\ne\lambda$ mapped to zero, push $P/\mathfrak nJ\to R$ out along $\lambda$ to obtain $B_\lambda\to R$ with one-dimensional kernel. Theorem 5.1 would lift the universal admissible representation to $B_\lambda$. Representability would give an $\mathcal O$-algebra section $R\to B_\lambda$. But minimality puts the kernel direction in the relative square of the maximal ideal, while a split square-zero socle direction is disjoint from that square, exactly as in (2.15)–(2.16). This contradiction proves injectivity. $\square$

The theorem proves an upper bound, not that all supported cohomology classes are relation obstructions. The cokernel of (9.7) measures cohomological directions that are never reached by the universal multiplication and local-admissibility defects.

### 9.4 Presentation independence

The conormal relation space depends on the chosen source unless the source is minimal. Suppose

$$
P=\mathcal O[[X_1,\ldots,X_t]]\twoheadrightarrow R
$$

and

$$
P'=\mathcal O[[Y_1,\ldots,Y_t]]\twoheadrightarrow R
$$

are two minimal presentations. Lifting the two cotangent bases gives mutually inverse continuous changes of coordinates modulo the kernels. Formal substitution induces an isomorphism

$$
J/\mathfrak nJ\simeq J'/\mathfrak n'J'. \tag{9.8}
$$

To check independence, compare the universal representations after pulling both presentations back to the completed power-series ring on all $X_i$ and $Y_j$. The two matrix sections differ by a global $1$-cochain, and their local choices differ by positive local cochains. Section 5.3 shows that their supported tensors correspond under (9.8). Thus (9.7) is intrinsic up to the unique conormal isomorphism induced by the two minimal presentations.

If a presentation is not minimal, a relation with a nonzero linear part may eliminate a variable. The resulting conormal space contains a contractible variable–relation pair. The factor-set obstruction of that pair is a supported coboundary, so injectivity cannot hold before minimalization. This is why minimality is an actual hypothesis of Theorem 9.1.

## 10. Passage to the dual Selmer space

### 10.1 Supported duality in degree two

The positive local complex for $M$ is dual, in complementary local degree two, to the quotient complex for $M'$. Compactly supported global duality then compares the two supported mapping fibers in complementary global degree three. In degree two this gives the perfect pairing

$$
H^2_{\mathcal L}(K,M)
\times H^1_{\mathcal L^\perp}(K,M')
\longrightarrow k. \tag{10.1}
$$

Equivalently,

$$
\mathcal D_{\mathcal L}:
H^2_{\mathcal L}(K,M)
\xrightarrow{\sim}
H^1_{\mathcal L^\perp}(K,M')^*. \tag{10.2}
$$

At the cochain level, the value consists of local cups between the nullhomotopies in the supported class and the localizations of the dual class, together with the global reciprocity homotopy applied to the global $2$-cocycle. When the ordinary factor set is already zero, this reduces to the affine formula (6.9).

The degree shift is worth checking. A supported degree-two class has a global coordinate in degree two and local correction coordinates in degree one. A dual Selmer class has degree one. The local corrections cup to degree two, where local invariants live; the mapping fiber contributes the extra global shift from two to three.

### 10.2 The canonical injection and its dual quotient

Compose Theorem 9.1 with (10.2):

$$
\boxed{
\mathcal R^*
\hookrightarrow
H^1_{\mathcal L^\perp}(K,M')^*.
} \tag{10.3}
$$

This is the canonical injection of the relation-obstruction module into the dual Selmer obstruction space. In terms of the conormal relation space itself, finite-dimensional duality gives the equivalent canonical quotient

$$
\boxed{
H^1_{\mathcal L^\perp}(K,M')
\twoheadrightarrow\mathcal R.
} \tag{10.4}
$$

These are the same theorem with opposite variance. Formula (10.3) is the obstruction-theoretic form; formula (10.4) is the equation-counting form. Neither supplies a canonical injection $\mathcal R\hookrightarrow H^1_{\mathcal L^\perp}(K,M')$ without choosing splittings of (10.4).

Taking dimensions yields

$$
r=\dim_k\mathcal R
\leq\dim_kH^1_{\mathcal L^\perp}(K,M'). \tag{10.5}
$$

This is stronger than merely knowing that $H^2_{\mathcal L}$ is an obstruction receptacle. The injectivity proof says that distinct minimal relation functionals remain distinct after all Poitou–Tate local corrections are imposed.

### 10.3 Relation corrections as local pairing matrices

Choose a basis $\lambda_1,\ldots,\lambda_r$ of $\mathcal R^*$ and a basis $y_1,\ldots,y_q$ of the dual Selmer group. The composite (10.3) is represented by the matrix

$$
A_{ij}=\mathcal D_{\mathcal L}
\bigl(\operatorname{ob}_R(\lambda_i)\bigr)(y_j). \tag{10.6}
$$

If the ordinary factor set for the $i$th relation is trivialized globally, choose local admissible lifts and let $q_{i,v}$ be their mismatches. Then

$$
A_{ij}=
\sum_{v\in S}
\operatorname{inv}_v
\bigl(q_{i,v}\smile\operatorname{loc}_v(y_j)\bigr). \tag{10.7}
$$

For a general relation, (10.7) has the additional global trace term described after (10.2). The matrix has row rank $r$ by injectivity. Thus every nonzero linear combination of minimal relations is detected by at least one dual Selmer class after the correct local corrections.

Changing admissible local base points adds localization rows coming from global tangent classes or elements of $L_v$. Equations (7.3) and exact orthogonality show that $A$ is unchanged. Changing the bases of relations and dual Selmer applies invertible row and column operations. Its rank and the quotient (10.4) are intrinsic.

**Two-place model.** Suppose a one-dimensional correction quotient is supported at two finite places $v$ and $w$, and a dual Selmer class has nonzero localizations at both. A mismatch $(q_v,0)$ may fail the test because its pairing is $a\ne0$. The mismatch $(q_v,q_w)$ is correctable precisely when the second local invariant is $-a$. The correction is global not because either local term vanishes, but because reciprocity makes their sum vanish.

### 10.4 When an isomorphism occurs

The injection (10.3) is an isomorphism exactly when every supported obstruction direction occurs as a minimal relation obstruction. Dimension equality is sufficient once injectivity is known:

$$
\dim\mathcal R
=\dim H^1_{\mathcal L^\perp}(K,M')
\quad\Longrightarrow\quad
\mathcal R^*\simeq H^1_{\mathcal L^\perp}(K,M')^*. \tag{10.8}
$$

Balance of tangent and supported obstruction dimensions does not imply the equality in (10.8), because the relation number can be strictly smaller than either dimension. A formally smooth deformation ring has $\mathcal R=0$ even if one embeds its vacuous obstruction theory into a larger cohomology group. Conversely, when $r$ equals the tangent dimension in a balanced problem, (10.8) shows that the universal relations exhaust supported degree two. Whether those equations form a regular sequence is a further commutative-algebra question and is not a consequence of cohomological dimension alone.

## 11. The hardly-ramified specialization

### 11.1 The local ledger

We now impose the hypotheses of Section 1.2. Write

$$
h_\ell=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V). \tag{11.1}
$$

The local calculations established in Book 183 are

$$
H^0(\mathbf Q_2,M)=H^1(\mathbf Q_2,M)
=H^0(\mathbf Q_2,M')=H^1(\mathbf Q_2,M')=0, \tag{11.2}
$$

$$
h^0_\ell(M)=h_\ell-1,\qquad
\dim L_\ell=h_\ell, \tag{11.3}
$$

and

$$
h^0_\infty(M)=1,\qquad H^1(\mathbf R,M)=0. \tag{11.4}
$$

Thus the normalized primal corrections are

$$
\begin{array}{c|c}
v&\dim L_v-h^0_v(M)\\ \hline
2&0\\
\ell&1\\
\infty&-1.
\end{array} \tag{11.5}
$$

Global absolute irreducibility gives $H^0(\mathbf Q,M)=0$. The injection into the local invariant group at $2$ and (11.2) give $H^0(\mathbf Q,M')=0$. Hence the Greenberg–Wiles correction is zero.

### 11.2 Vanishing of local obstruction groups

At $2$, the local ambient obstruction vanishes:

$$
H^2(\mathbf Q_2,M)
\simeq H^0(\mathbf Q_2,M')^*=0. \tag{11.6}
$$

The calculation uses the tame order-three inertia centralizer. Frobenius acts by $-1$ on its trace-zero invariant line, and the Tate twist changes this to $-2$. Since $-2\ne1$ for $\ell\ge7$, the twisted invariant group is zero.

At $\ell$, one must state a different vanishing. The ambient group $H^2(\mathbf Q_\ell,M)$ need not vanish. What vanishes is the intrinsic obstruction to the coefficient-linear finite-flat local condition: every admissible deformation lifts through a small extension, and the admissible lift classes form the affine torsor under $L_\ell$. This is exactly the hypothesis used in (5.2). Replacing it by ambient $H^2=0$ would be an unjustified strengthening.

At infinity, the order of $C_2$ is invertible in $k$. Averaging contracts the complete Tate complex, so there is no positive local obstruction and no correction torsor. The ordinary invariant line in (11.4) remains in the Euler calculation.

Consequently all local factor-set restrictions admit the nullhomotopies required in Chapter 5. At $2$ and infinity they are unique up to the degree-zero terms already present in the positive complexes; at $\ell$ they vary through the finite-flat affine torsor.

### 11.3 Balanced dimensions and minimal relations

Let $R_{\mathrm{hr}}$ be the universal fixed-determinant hardly-ramified deformation ring and choose a minimal presentation

$$
R_{\mathrm{hr}}
\simeq\mathcal O[[X_1,\ldots,X_t]]/J. \tag{11.7}
$$

The tangent calculation gives

$$
t=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M). \tag{11.8}
$$

Supported duality and the zero correction (11.5) give

$$
\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=t. \tag{11.9}
$$

The relation injection now yields

$$
\left(J/\mathfrak nJ\right)^*
\hookrightarrow H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*, \tag{11.10}
$$

and therefore

$$
\boxed{
r=\dim_kJ/\mathfrak nJ\le t.
} \tag{11.11}
$$

This is the balanced presentation bound. The word balanced refers to the equality between tangent and supported obstruction dimensions, not to a claim that $r=t$. If $r<t$, some cohomological obstruction directions are not realized by minimal equations.

Since $P$ has relative dimension $1+t$ over the residue field convention, the elementary height inequality gives

$$
\dim R_{\mathrm{hr}}
\ge1+t-r\ge1 \tag{11.12}
$$

provided the ring is nonzero. The first inequality uses that an ideal generated by $r$ elements has height at most $r$. It does not assert flatness, reducedness, or that the equations form a regular sequence.

### 11.4 Scalar and reducible local restrictions

The local restriction at $\ell$ need not be absolutely irreducible. If its endomorphism algebra has dimension $h_\ell$, the trace-zero invariant space has dimension $h_\ell-1$ and the finite-flat tangent space has dimension $h_\ell$. Their difference remains one. Hence (11.5) and the global balance are independent of $h_\ell$.

For a split sum of two distinct local characters, $h_\ell=2$; the invariant and tangent dimensions are one and two. For a local Schur representation, they are zero and one. A scalar local representation has a larger centralizer and may fall outside the finite-flat classification used to prove $\dim L_\ell=h_\ell$. It may be inserted only after that geometric tangent theorem has been reverified. The formal identity

$$
h^0_\ell(M)=h_\ell-1
$$

alone does not prove the finite-flat dimension formula.

At $2$, scalar behavior is excluded by the prescribed order-three inertia. That non-scalar type is used twice: it makes the primal invariant line anti-invariant under Frobenius and makes the twisted invariant vanish. Replacing the local type changes both the correction target and the proof that global twisted invariants vanish.

## 12. Exceptional cases and changes of data

### 12.1 Characteristics two, three, and five

The hypothesis $\ell\ge7$ has several independent tasks.

In characteristic two, the identity matrix has trace zero, the trace pairing on the expected fixed-determinant adjoint is not used as in (1.1), determinant correction by a scalar cannot divide by two, and real complete cohomology need not vanish. Chapters 3, 7, and 11 would all require different coefficient objects.

In characteristic three, the twisted Frobenius eigenvalue at $2$ satisfies

$$
-2=1. \tag{12.1}
$$

Thus $H^0(\mathbf Q_2,M')$ and $H^2(\mathbf Q_2,M)$ can be nonzero. The local condition at $2$ is no longer automatically unobstructed in the required ambient sense, and restriction at $2$ no longer kills global twisted invariants.

In characteristic five, the two displayed failures do not occur. Nevertheless the unified local finite-flat theorem and the global hardly-ramified package used here were established only for $\ell\ge7$. Favorable isolated dimension calculations do not extend the conclusion of Section 11.3 to $\ell=5$ without a fresh verification of the local classification and all global hypotheses.

### 12.2 Enlarging the controlling set

Let $S'=S\cup\{w\}$, where $w$ is finite, $M$ is unramified at $w$, and $w$ does not divide the coefficient characteristic. Give $w$ the unramified condition. Then

$$
\dim H^1_{\mathrm{ur}}(K_w,M)=h^0_w(M), \tag{12.2}
$$

so its Greenberg–Wiles correction is zero. More strongly, the relative cone comparing the two supported complexes is the cone of unramified local cochains mapping to all local cochains. The unramified condition makes that relative cone acyclic in the supported comparison, giving a quasi-isomorphism

$$
C_{\mathcal L,S}^\bullet(K,M)
\simeq C_{\mathcal L',S'}^\bullet(K,M). \tag{12.3}
$$

Universal factor-set tensors correspond under (12.3), so the relation injection is independent of harmless enlargement.

If the new condition is strict or relaxed, the relative cone is not acyclic. The deformation problem has changed, and its relation module, supported obstruction group, and dual Selmer space can all change. Independence is never asserted without the unramified condition at a newly admitted harmless place.

### 12.3 Extending the residue field

Let $k'/k$ be finite. Flat scalar extension commutes with continuous cohomology of the finite modules in question, with kernels defining $L_v$, with exact orthogonals, and with the finite-dimensional mapping fibers. Therefore

$$
\Omega_{R\widehat\otimes_{\mathcal O}\mathcal O'}
=\Omega_R\otimes_k k', \tag{12.4}
$$

provided the presentation kernel and every local deformation condition base-change exactly. The injection (10.3) becomes its scalar extension, so dimensions are unchanged when measured over $k'$.

This conclusion can fail for a nonflat coefficient quotient. For instance, an equation equal to a uniformizer can disappear after reduction to the residue field. It can also fail when a local finite-flat model acquires extra endomorphisms after changing residue characteristic. Exact kernel base change and flatness are hypotheses, not consequences of completeness.

### 12.4 Nonminimal presentations

Suppose a presentation has $t+s$ variables but only $t$ tangent directions. Its conormal differential has rank $s$. After changes of coordinates, $s$ relations have independent linear terms in $s$ variables. Formal elimination removes those variables and relations, leaving a minimal presentation.

At the obstruction level, each removable pair contributes a contractible two-term summand. Its apparent relation factor is the coboundary of the first-order change in the removable variable. Consequently a map from the full nonminimal conormal dual to supported $H^2$ has an $s$-dimensional kernel. This is not a failure of Theorem 9.1; it is the reason the theorem begins with a minimal source.

Padding a presentation by a new variable $Y$ and a relation $Y$ is harmless after elimination, but it changes the displayed numbers of variables and equations by one. Padding by a new variable and no equation changes the represented ring. Padding a list of equations by zeros changes neither the ideal nor its minimal relation space. These three operations must not be conflated.

### 12.5 Failure of local smoothness

If a local condition has its own nonzero obstruction group, admissible local lifts need not exist. Then Chapter 4 no longer supplies an affine torsor at every small extension, and the two-term positive complex is incomplete. One must replace it by a local deformation complex with a degree-two term and a complete local obstruction map.

The global factor set still exists, but a supported class must include the local obstruction coordinates rather than chosen nullhomotopies. The change-of-local-conditions sequence can continue beyond degree two, and the short exact ending used in the effectiveness proof may fail. No relation bound from the two-term theory is valid until the enlarged local complexes are proved dual and their lift theory is compatible with pushout.

Local formal smoothness is sufficient for this book's local torsors, but it does not imply global formal smoothness. The surviving global gluing obstruction is precisely $H^2_{\mathcal L}(K,M)$, which can be nonzero even when every local obstruction vanishes.

## 13. Dependency and normalization audit

### 13.1 Imported results with matching hypotheses

The construction uses four numbered foundations, each in a specific form.

From Book 28 we use the general boundary principle: lifting transition data through a central square-zero extension produces a degree-two factor set, changing lifts adds a coboundary, and vanishing is equivalent to correction. We also use Kummer torsors, cyclic algebras, and restriction–corestriction in the proof of Theorem 8.1. Our coefficients at finite places are finite étale because every completion of a number field has characteristic zero; no equal-characteristic primary exception occurs.

From Book 31 we use local Tate duality for finite modules, exact orthogonals in $H^1$, degree-two duality

$$
H^2(K_v,M)\simeq H^0(K_v,M')^*,
$$

and restriction–corestriction adjointness. Its hypothesis is that the coefficient exponent be prime to the characteristic of the local field, not to the residue characteristic. Since $K_v$ has characteristic zero, this includes the $\ell$-primary module at $v\mid\ell$. The Tate twist and arithmetic-Frobenius convention agree with (1.1) and (7.8).

From Book 33 we use the finite-coefficient Poitou–Tate sequence, compactly supported duality, modified real cohomology, and the exact annihilator identity. Our set $S$ contains infinity, every place over the coefficient characteristic, and every ramified place. The module is finite and abelian. At real places the full modified convention is retained in the general theorem; it becomes acyclic in the hardly-ramified application because $\ell$ is odd. The global Brauer reciprocity input on which its trace depends was proved independently in Chapter 8.

From Book 183 we use the positive and quotient local complexes, supported duality, the hardly-ramified local dimension ledger, and the balanced Greenberg–Wiles identity. Its hypotheses are exactly those listed in Section 1.2: $\ell\ge7$, absolute irreducibility, oddness, cyclotomic determinant, the tame order-three type at $2$, and coefficient-linear finite flatness at $\ell$. We did not strengthen local absolute irreducibility at $\ell$, and Section 11.4 retains the local centralizer parameter.

No result from a later book is used. The relation-space algebra, factor-set construction, effectiveness argument, affine lift torsors, reciprocity theorem, and universal injection were proved here.

### 13.2 Sign, twist, and degree ledger

The conventions can be summarized as follows.

| datum | convention | consequence |
|---|---|---|
| local Frobenius | arithmetic | the twist at $2$ changes $-1$ to $-2$ |
| dual coefficient | $M'=M^*(1)$ | evaluation lands in roots of unity |
| factor set | $\widetilde\rho(g)\widetilde\rho(h)\widetilde\rho(gh)^{-1}$ | changing by $1+b$ adds $db$ |
| mapping fiber | $\operatorname{Cone}(\lambda)[-1]$ | differential is $(dx,\lambda x-dy)$ |
| local complementary degree | $2-i$ | $H^1$ pairs with $H^1$ |
| supported complementary degree | $3-i$ | supported $H^2$ pairs with dual Selmer $H^1$ |
| local invariant | unramified arithmetic cyclic algebra has invariant $1/m$ | corestriction preserves invariants |
| real invariant | quaternion class maps to $1/2$ | two real ramification terms cancel in pairs |
| relation variance | $\mathcal R^*\to H^2_{\mathcal L}$ | dualizing gives Selmer $\twoheadrightarrow\mathcal R$ |

If the global matrix lift is changed by $1+b$, the factor set changes by $db$. Our local comparison convention in (5.2) therefore gives $\operatorname{loc}c+db_v=0$ and the mapping-fiber coordinate is $y_v=-b_v$. This verifies the only potentially ambiguous sign in the supported class.

Switching every local reciprocity map to geometric normalization would negate each local invariant formula. Orthogonal subspaces and the zero criterion would be unchanged, but displayed matrix entries in (10.7) would change sign. We keep the arithmetic normalization throughout.

### 13.3 A reliable relation-obstruction protocol

A new constrained deformation problem can be treated in the following order.

1. Fix the residual coefficient module, its Tate dual, and a controlling set containing infinity and all coefficient and ramification places.
2. Prove representability and choose a minimal relative power-series presentation.
3. Prove local liftability and identify the actual tangent subspace $L_v$ at each place.
4. Represent $L_v$ by a positive local complex retaining degree-zero automorphisms.
5. For a small extension, choose determinant-compatible global matrix lifts and compute their factor set.
6. Choose admissible local lifts and attach the local nullhomotopies with the sign in Section 13.2.
7. Form the supported degree-two class and prove independence, functoriality, additivity, and completeness.
8. Prove that local mismatch families are correctable exactly when all dual Selmer reciprocity sums vanish.
9. Apply the universal relation extension and contract its tensor with relation functionals.
10. Use effectiveness to prove injectivity before taking dimensions.
11. Apply supported duality, preserving the duals, to obtain (10.3) and (10.4).
12. Only then use a Greenberg–Wiles calculation to compare the relation bound with the tangent dimension.

Three checks catch most errors. The local nullhomotopy must satisfy the mapping-fiber cocycle equation, the correction target must retain the possible $\Sha^2$ tail, and the final relation arrow must have the variance of (10.3), not its reverse.

## 14. Conclusion

### 14.1 The completed obstruction package

A minimal equation in a deformation ring is invisible to first-order differentiation when it begins in degree two or higher. Its arithmetic shadow is instead a factor set. Lifting the universal matrices through the square-zero relation extension produces a global $2$-cocycle. Associativity makes it closed, a change of section adds a coboundary, and fixed determinant places it in the trace-zero adjoint module.

Local conditions add indispensable structure. Admissible local lifts form affine torsors under their actual tangent spaces. Comparing them with a global matrix section supplies local nullhomotopies, and the global cocycle together with those nullhomotopies is a supported degree-two class. Its vanishing is equivalent to an admissible global lift, not merely to an unrestricted lift.

Poitou–Tate correction is the exact global compatibility law for the affine torsors. A mismatch family is paired with every dual Selmer class by summing local Tate invariants. Global Brauer reciprocity makes every global correction invisible to the sum; perfect global duality proves that nothing else is invisible. The correction cokernel is tested by dual Selmer modulo everywhere locally trivial classes, while the full supported obstruction group is the complete dual of the dual Selmer group.

The universal relation tensor consequently gives the canonical injection

$$
\operatorname{Rel}^{\mathrm{ob}}_P(R)
\hookrightarrow H^2_{\mathcal L}(K,M)
\simeq H^1_{\mathcal L^\perp}(K,M')^*,
$$

or, equivalently, the canonical quotient of dual Selmer onto the conormal relation space. This statement retains the correct variance and distinguishes a complete obstruction space from a minimal one.

### 14.2 The balanced endpoint

For the hardly-ramified representation, rigidity at $2$ removes both local obstruction and global twisted invariants. The finite-flat condition at $\ell$ contributes one normalized tangent direction. Oddness contributes one real invariant and no real tangent direction. These last two terms cancel. Supported degree one and degree two therefore have equal dimension.

If

$$
R_{\mathrm{hr}}
\simeq\mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r)
$$

is minimal in variables and equations, the completed relation-obstruction package proves

$$
r\le
\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=t.
$$

This is the precise balanced conclusion. It neither discards a local correction nor promotes an upper bound to an equality. Every minimal relation is detected by a dual Selmer functional, all reciprocity and real-place terms have been retained, and no additional obstruction is hidden between local liftability and global admissibility.
