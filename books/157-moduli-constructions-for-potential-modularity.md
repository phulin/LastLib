# Moduli Constructions for Potential Modularity

## Contents

1. [The realization problem](#1-the-realization-problem)
   - [From a representation to a moving abelian variety](#11-from-a-representation-to-a-moving-abelian-variety)
   - [The determinant obstruction comes first](#12-the-determinant-obstruction-comes-first)
   - [Why one elliptic curve is often too small](#13-why-one-elliptic-curve-is-often-too-small)
   - [The construction in one diagram](#14-the-construction-in-one-diagram)
2. [Symplectic modules and twisted frames](#2-symplectic-modules-and-twisted-frames)
   - [Alternating lines and multipliers](#21-alternating-lines-and-multipliers)
   - [Galois modules with a fixed pairing](#22-galois-modules-with-a-fixed-pairing)
   - [The isomorphism torsor and its cocycle](#23-the-isomorphism-torsor-and-its-cocycle)
   - [A counterexample from forgetting the multiplier](#24-a-counterexample-from-forgetting-the-multiplier)
3. [Twisted modular curves](#3-twisted-modular-curves)
   - [Why the one-prime case is the model](#31-why-the-one-prime-case-is-the-model)
   - [Descent from the standard full-level curve](#32-descent-from-the-standard-full-level-curve)
   - [Worked example: a quadratic twist of level five](#33-worked-example-a-quadratic-twist-of-level-five)
   - [Coarse level is not enough](#34-coarse-level-is-not-enough)
4. [Why two primes lead to real multiplication](#4-why-two-primes-lead-to-real-multiplication)
   - [The naive fiber product](#41-the-naive-fiber-product)
   - [The Hilbert--Blumenthal alternative](#42-the-hilbert--blumenthal-alternative)
   - [Choosing the coefficient field and its primes](#43-choosing-the-coefficient-field-and-its-primes)
   - [A two-prime datum in degree two](#44-a-two-prime-datum-in-degree-two)
5. [The Hilbert--Blumenthal moduli datum](#5-the-hilbert--blumenthal-moduli-datum)
   - [Why an action alone is insufficient](#51-why-an-action-alone-is-insufficient)
   - [Hilbert--Blumenthal abelian schemes](#52-hilbert--blumenthal-abelian-schemes)
   - [Polarization pairings at coefficient primes](#53-polarization-pairings-at-coefficient-primes)
   - [Neat auxiliary level](#54-neat-auxiliary-level)
   - [The untwisted fine space](#55-the-untwisted-fine-space)
6. [Imposing the two twisted levels](#6-imposing-the-two-twisted-levels)
   - [The target data](#61-the-target-data)
   - [Descent as a product cocycle](#62-descent-as-a-product-cocycle)
   - [Representability and the universal object](#63-representability-and-the-universal-object)
7. [Deformations, smoothness, and dimension](#7-deformations-smoothness-and-dimension)
   - [The tangent problem](#71-the-tangent-problem)
   - [Formal smoothness](#72-formal-smoothness)
   - [Why there is room](#73-why-there-is-room)
8. [Geometric components and monodromy](#8-geometric-components-and-monodromy)
   - [Three notions that must be separated](#81-three-notions-that-must-be-separated)
   - [The monodromy criterion](#82-the-monodromy-criterion)
   - [Verifying the hypothesis](#83-verifying-the-hypothesis)
   - [Determinants and component stability](#84-determinants-and-component-stability)
9. [Local points as comparison objects](#9-local-points-as-comparison-objects)
   - [The local design principle](#91-the-local-design-principle)
   - [Good places](#92-good-places)
   - [Archimedean places](#93-archimedean-places)
   - [Places above the target characteristic](#94-places-above-the-target-characteristic)
   - [Places above the auxiliary characteristic](#95-places-above-the-auxiliary-characteristic)
   - [Ramified primes and primes of the datum](#96-ramified-primes-and-primes-of-the-datum)
   - [A worked pair of residual places](#97-a-worked-pair-of-residual-places)
10. [Local conditions are open](#10-local-conditions-are-open)
   - [From a point to a neighborhood](#101-from-a-point-to-a-neighborhood)
   - [Good reduction](#102-good-reduction)
   - [Semistable reduction](#103-semistable-reduction)
   - [Constancy of finite-flat comparison](#104-constancy-of-finite-flat-comparison)
   - [The finite local set](#105-the-finite-local-set)
11. [Explicit local seeds](#11-explicit-local-seeds)
   - [The Serre tensor construction](#111-the-serre-tensor-construction)
   - [Real and good seeds](#112-real-and-good-seeds)
   - [Ordinary and nonordinary seeds](#113-ordinary-and-nonordinary-seeds)
   - [Semistable seeds from Tate curves](#114-semistable-seeds-from-tate-curves)
12. [Persistence and simultaneous local conditions](#12-persistence-and-simultaneous-local-conditions)
   - [Persistence under finite extension](#121-persistence-under-finite-extension)
   - [Intersections must have a witness](#122-intersections-must-have-a-witness)
   - [Components and degeneracy loci](#123-components-and-degeneracy-loci)
   - [The simultaneous-neighborhood theorem](#124-the-simultaneous-neighborhood-theorem)
13. [The complete geometric package](#13-the-complete-geometric-package)
   - [Admissible two-prime moduli data](#131-admissible-two-prime-moduli-data)
   - [The smooth connected cover theorem](#132-the-smooth-connected-cover-theorem)
   - [The local-open theorem](#133-the-local-open-theorem)
   - [Examples and counterexamples](#134-examples-and-counterexamples)
14. [Disjointness and the exact handoff](#14-disjointness-and-the-exact-handoff)
   - [The avoidance datum](#141-the-avoidance-datum)
   - [What disjointness would preserve](#142-what-disjointness-would-preserve)
   - [Root fields and normal closures](#143-root-fields-and-normal-closures)
   - [The output boundary](#144-the-output-boundary)
15. [Failure audit](#15-failure-audit)
   - [Empty twists and false components](#151-empty-twists-and-false-components)
   - [Generic frames and integral models](#152-generic-frames-and-integral-models)
   - [Separate local solutions](#153-separate-local-solutions)
   - [Smoothness, nonemptiness, and automorphy](#154-smoothness-nonemptiness-and-automorphy)
16. [Conclusion](#16-conclusion)

## 1. The realization problem

### 1.1 From a representation to a moving abelian variety

Let $F$ be a totally real number field, let $p$ be an odd prime, let $k$ be a finite field of characteristic $p$, and let

$$
\bar\rho:G_F\longrightarrow \operatorname{GL}_2(k)
$$

be continuous and absolutely irreducible. Potential modularity begins with a reversal of the usual direction of thought. Torsion on an abelian variety gives a Galois representation; here the representation is given first, and one asks for an abelian variety whose torsion is that representation.

The desired construction must do much more than match two abstract vector spaces. It must preserve the alternating form forced by a polarization, behave correctly at places above $p$, meet specified reduction conditions at other places, and coexist with a second torsion representation. Finally, all these requirements must define open local conditions on one smooth geometrically connected variety, for only then can a later arithmetic approximation theorem turn local models into a global point over a finite totally real extension.

This book constructs precisely that variety and its local-open package. It does not produce the global point and does not prove modularity. Our task is geometric and local-arithmetic at once: design a moduli problem that remembers enough information to realize both representations conditionally at a future point, but remains smooth and connected enough for later approximation.

### 1.2 The determinant obstruction comes first

If $E/F$ is an elliptic curve, its Weil pairing gives a perfect alternating, Galois-equivariant map

$$
e_p:E[p]\times E[p]\longrightarrow \mu_p.
$$

Taking an ordered basis shows

$$
\det E[p]=\bar\chi_p,
$$

where $\bar\chi_p$ is the mod-$p$ cyclotomic character. Consequently an isomorphism $\bar\rho\simeq E[p]$ cannot exist unless

$$
\det\bar\rho=\bar\chi_p. \tag{1.1}
$$

More generally, a polarization with coefficient or polarization module may replace $\mu_p$ by a one-dimensional pairing module $L_p$. Then the necessary condition is an identification

$$
\det V_{\bar\rho}=L_p \tag{1.2}
$$

of Galois modules, not merely equality of their dimensions. This is the first design constraint, not a cosmetic normalization. A quadratic twist does not repair an arbitrary determinant: in dimension two, twisting by $\eta$ multiplies the determinant by $\eta^2$. One must arrange determinant compatibility in the input, often after a controlled scalar twist whose square has the required ratio.

An odd representation satisfies $\det\bar\rho(c)=-1$ for every complex conjugation $c$. Since $\bar\chi_p(c)=-1$, condition (1.1) implies oddness. The converse is false: oddness tests only complex conjugations and says nothing about the determinant at finite Frobenius elements.

### 1.3 Why one elliptic curve is often too small

Suppose a second odd representation

$$
\bar\rho_{\mathrm{aux}}:G_F\longrightarrow\operatorname{GL}_2(k')
$$

of characteristic $q\ne p$ is prescribed. Asking for an elliptic curve $E$ with

$$
E[p]\simeq\bar\rho,
\qquad
E[q]\simeq\bar\rho_{\mathrm{aux}}
\tag{1.3}
$$

is a condition on a one-dimensional moduli space. The simultaneous level scheme is not literally the fiber product of two independently twisted modular curves over their $j$-lines unless their descent data and pairing coordinates agree. Even when it is correctly formed as one twist of full $pq$-level, it is still a curve. A finite list of local open conditions is not prohibited on a curve, but there may be no convenient local points, and the two residual requirements leave little geometric freedom for arranging additional PEL and reduction data.

The remedy is not to take a product of unrelated elliptic curves. It is to enlarge the endomorphism structure. A Hilbert--Blumenthal abelian variety with real multiplication by an order of degree $g$ has dimension $g$, yet each prime $\lambda$ of the coefficient order cuts out a two-dimensional torsion module. Distinct primes $\lambda$ and $\lambda'$ can therefore carry the two representations while all $g$ real directions remain available in the moduli space.

### 1.4 The construction in one diagram

The argument will have the following shape:

$$
\begin{array}{c}
(\bar\rho,\bar\rho_{\mathrm{aux}})
\ +\ \text{pairings and local models}
\\ \downarrow \\
X=X(\bar\rho,\bar\rho_{\mathrm{aux}})
\quad\text{smooth, geometrically connected, }\dim X=g
\\ \downarrow\ \text{local points and open neighborhoods} \\
x\in X(F')\quad(F'/F\text{ finite totally real and disjoint})
\\ \downarrow \\
(A,\iota,\lambda_A,\eta;\alpha,\alpha_{\mathrm{aux}})/F'.
\end{array} \tag{1.4}
$$

Every downward arrow has a separate possible failure. Pairings may be incompatible; the moduli functor may retain automorphisms; the chosen geometric component may not descend; local models may not exist at level primes; or the extension $F'$ may meet a residual fixed field and shrink an image. Keeping these obstructions visible is the governing method of the book.

## 2. Symplectic modules and twisted frames

### 2.1 Alternating lines and multipliers

Before defining a moduli space, we isolate the linear algebra it must classify. Let $R$ be a commutative ring, let $V$ be locally free of rank two, and let $L$ be invertible of rank one. A perfect alternating pairing is a map

$$
\langle\ ,\ \rangle:V\times V\longrightarrow L
$$

whose induced map $V\to\operatorname{Hom}_R(V,L)$ is an isomorphism. Equivalently, it is an isomorphism

$$
\bigwedge^2V\xrightarrow{\sim}L. \tag{2.1}
$$

For rank two this equivalence explains why determinants control pairings. If $g\in\operatorname{GL}(V)$ and $L=R$ has been trivialized, then

$$
\langle gv,gw\rangle=\det(g)\langle v,w\rangle. \tag{2.2}
$$

Thus $\operatorname{GSp}_2=\operatorname{GL}_2$, with similitude multiplier equal to determinant, while $\operatorname{Sp}_2=\operatorname{SL}_2$. It is nevertheless useful to retain the word “symplectic”: it records the pairing line and its Galois action, which a bare matrix representation conceals.

Let $V$ and $W$ be paired rank-two modules with pairing lines identified. The functor

$$
\operatorname{Isom}^{\mathrm{symp}}(V,W)
$$

of pairing-preserving isomorphisms is a torsor under $\operatorname{SL}_2$. The larger functor of similitudes with an unspecified multiplier is a torsor under $\operatorname{GL}_2$. Confusing these two torsors is exactly how an unwanted determinant component enters a modular construction.

### 2.2 Galois modules with a fixed pairing

Let $k$ be finite of odd characteristic and let $V$ be a two-dimensional $k$-space with continuous $G_F$-action. A symplectic structure with cyclotomic values is a $G_F$-equivariant isomorphism

$$
\delta:\bigwedge^2V\xrightarrow{\sim}k(1). \tag{2.3}
$$

Here $k(1)=\mu_p\otimes_{\mathbf F_p}k$ when $k$ contains the relevant residue field. Such a $\delta$ exists precisely when $\det V=\bar\chi_p$. It is not unique: multiplying $\delta$ by $a\in k^\times$ changes the chosen pairing coordinate. The moduli space will depend on this coordinate up to a predictable relabeling of components.

If $A$ is polarized and carries real multiplication, the $\lambda$-torsion pairing may naturally take values in a residue of the polarization module tensored with $\mu_p$. We therefore use the more general datum

$$
\delta_\lambda:\bigwedge^2V\xrightarrow{\sim}
(\mathfrak c^{-1}\mathfrak d_M^{-1}\otimes k_\lambda)(1), \tag{2.4}
$$

after fixing the convention that identifies the target line. Different conventions move the fractional ideals between the Tate module and its dual; what matters is that the same convention is used for the PEL pairing and the target representation. At primes where $\mathfrak c$ and the different $\mathfrak d_M$ are trivialized locally, (2.4) becomes the familiar cyclotomic determinant condition.

### 2.3 The isomorphism torsor and its cocycle

Choose a separable closure $\overline F$ and a reference symplectic space $V_0=k^2$. Over $\overline F$, all symplectic frames are isomorphic. If

$$
\alpha:V\xrightarrow{\sim}V_0
$$

is one frame, then for $\sigma\in G_F$ the discrepancy between $\alpha$ and its conjugate is

$$
c_\sigma=\alpha\,\bar\rho(\sigma)\,\alpha^{-1}\,r_0(\sigma)^{-1}, \tag{2.5}
$$

where $r_0$ is the Galois action on the reference level object. With consistent left and right conventions, the relation

$$
c_{\sigma\tau}=c_\sigma\,{}^\sigma c_\tau
$$

says that $(c_\sigma)$ is a descent cocycle. Determinant compatibility places it in the pairing-preserving group. Twisting the reference level cover by this cocycle produces a variety whose rational points are not arbitrary frames: they are precisely Galois-equivariant identifications with $V$.

The inverse in (2.5) is convention-sensitive. One can equally let frames act on the right and obtain the inverse cocycle. The safe test is the rational-point condition. If the descended point is represented by $\phi:V\to A[p]$, then it must satisfy

$$
\sigma(\phi(v))=\phi(\bar\rho(\sigma)v). \tag{2.6}
$$

Any proposed twist whose fixed points do not satisfy (2.6) has the wrong action, regardless of notation.

### 2.4 A counterexample from forgetting the multiplier

Take the ordinary full-level modular curve with ordered bases of $E[p]$. Its geometric components are indexed by the value $e_p(P,Q)\in\mu_p^{\mathrm{prim}}$. Suppose one twists the whole $\operatorname{GL}_2(\mathbf F_p)$-torsor by a representation of determinant $\bar\chi_p$ but then selects the component $e_p(P,Q)=\zeta_p$ without letting Galois act on $\zeta_p$. For $\sigma(\zeta_p)=\zeta_p^{\bar\chi_p(\sigma)}$, the selected component is not stable. The alleged descent is therefore not a variety over $F$.

There are two correct repairs. One may formulate the pairing value as a Galois-equivariant map to $\mu_p$, so the cyclotomic action is built in, or work over the cyclotomic field where the component is defined and descend it with the determinant action. In both forms, the determinant is the descent datum on components.

## 3. Twisted modular curves

### 3.1 Why the one-prime case is the model

The elliptic case displays all essential descent issues without the extra coefficient algebra. Let $p\geq3$, and let $V$ be a two-dimensional $\mathbf F_p$-representation with a fixed isomorphism $\bigwedge^2V\simeq\mu_p$. Consider the functor

$$
\mathcal Y_V(S)=\left\{(E/S,\alpha):
\alpha:V_S\xrightarrow{\sim}E[p]
\text{ preserves pairings}\right\}/\simeq. \tag{3.1}
$$

where $V_S$ denotes the finite étale local system obtained from $V$ and $p$ is invertible on $S$. This definition solves the realization problem directly: an $F'$-point yields $E[p]\simeq V|_{G_{F'}}$. The restriction “$p$ invertible on $S$” is structural. Over a characteristic-$p$ fiber, $E[p]$ need not be étale and cannot be identified with a constant étale module. For the characteristic-zero variety used later this causes no problem, while integral level at $p$ must be expressed through finite locally free group schemes.

### 3.2 Descent from the standard full-level curve

Over a field splitting $V$ and $\mu_p$, choose a symplectic basis of $V$. Then $\mathcal Y_V$ becomes the fixed-pairing full-level curve $Y(p)_{\zeta}$. Changing the basis acts through $\operatorname{SL}_2(\mathbf F_p)$, and the Galois action on $V$ supplies a cocycle in that group. Effective descent gives the twist $Y_V$ over $F$.

**Proposition 3.1.** Suppose $p\geq3$ and $\det V=\bar\chi_p$, with a chosen pairing identification. Then $\mathcal Y_V$ is represented by a smooth affine curve $Y_V/F$. Over $\overline F$ it is isomorphic to a fixed-pairing component of $Y(p)$, and hence is geometrically connected. It carries a universal elliptic curve.

**Proof strategy.** We first use full level to eliminate automorphisms. We then descend the standard fine curve and its universal family along the frame cocycle. Smoothness and geometric connectedness are geometric properties and can be checked after the splitting extension.

**Proof.** An automorphism of an elliptic curve preserving a full level-$p$ basis acts trivially on $E[p]$. For $p\geq3$ it is the identity; in particular $[-1]$ does not preserve the basis. Thus the full-level functor is fine. The chosen pairing cuts out an open-and-closed component. Over a finite Galois extension splitting the module and pairing coordinate, the cocycle acts by automorphisms of this fine component and of its universal elliptic curve. Descent is effective because both are quasi-projective. The descended curve represents (3.1), as can be verified after the faithfully flat splitting extension. Smoothness descends. Over $\overline F$ the twist becomes the original connected component, proving geometric connectedness. The universal family descends together with the level map. $\square$

After the proof, two qualifications matter. First, $p=3$ still kills automorphisms for full ordered level, but quotient levels may not. Second, the compactification does not carry an elliptic curve across its cusps; it carries a generalized elliptic curve. Our later existence theorem will be applied to the open fine moduli space, so the universal object is an abelian scheme.

### 3.3 Worked example: a quadratic twist of level five

Let $p=5$ and let

$$
\bar\rho(\sigma)=\eta(\sigma)
\begin{pmatrix}\bar\chi_5(\sigma)&0\\0&1\end{pmatrix},
$$

where $\eta:G_F\to\{\pm1\}$ is quadratic. Its determinant is $\bar\chi_5$, since $\eta^2=1$. Over the quadratic field cut out by $\eta$, the module is the split cyclotomic module $\mu_5\oplus\mathbf Z/5\mathbf Z$. The associated curve is therefore a quadratic descent of a fixed-pairing component of $Y(5)$.

A point of the twist over an extension $L/F$ is an elliptic curve with a symplectic identification

$$
E[5]\simeq
\eta|_{G_L}\otimes(\mu_5\oplus\mathbf Z/5\mathbf Z).
$$

It is not generally the quadratic twist of an elliptic curve possessing two rational torsion points. The twist is applied to the level moduli problem, not pointwise to a preselected elliptic curve. This distinction is useful: a moduli twist may have points even when the untwisted curve has none over the same field.

### 3.4 Coarse level is not enough

If one replaces full level by a cyclic subgroup, $[-1]$ survives. The resulting coarse modular curve may be a perfectly smooth scheme, but a rational point on it need not carry an elliptic curve defined over its residue field; the obstruction lies in descent of the object, not of its isomorphism class. Consequently a coarse twist cannot by itself furnish the universal curve needed for realization.

The standard repair is a fine cover: add a prime-to-$p$ auxiliary level $N\geq3$, classify $(E,C,\eta_N)$, and retain it throughout the construction. Forgetting $\eta_N$ may be harmless only after the desired elliptic curve has been obtained. The same principle will govern the higher-dimensional moduli space.

There is also a field-of-moduli warning even for full level. A geometric point can be fixed as an isomorphism class by $G_L$ while its ordered frame is not fixed. The twist is designed so that fixing the *whole tuple* is equivalent to the equivariance equation (2.6). It is therefore incorrect to first descend the elliptic curve and then hope that a geometric identification of its torsion descends automatically. The obstruction is exactly the torsor class that the twisted modular curve records.

For later reference, the one-prime conclusion can be stated cleanly. Given a paired $V$ with cyclotomic determinant and $p\geq3$, every closed point of $Y_V$ with residue field $L$ yields an elliptic curve over $L$ realizing $V|_{G_L}$. Conversely, every such elliptic curve with a chosen symplectic realization gives an $L$-point. This equivalence survives arbitrary field extension and is the functorial fact that makes local comparison possible.

## 4. Why two primes lead to real multiplication

### 4.1 The naive fiber product

Let $Y_{\bar\rho}\to Y(1)$ and $Y_{\bar\rho_{\mathrm{aux}}}\to Y(1)$ be two twisted modular curves. Their fiber product over the $j$-line does express the condition that the same elliptic curve realize both modules, provided the maps and descent data are compatible. Since each map is finite, however, the fiber product is again one-dimensional. It may be disconnected or geometrically reducible, and a chosen component can acquire a nontrivial constant field.

Worse, taking the product $Y_{\bar\rho}\times Y_{\bar\rho_{\mathrm{aux}}}$ classifies two unrelated elliptic curves. That does not create the bridge required later: known information about the auxiliary torsion of one curve says nothing about the target torsion of the other. The required object must carry both modules in one compatible system of endomorphism factors.

### 4.2 The Hilbert--Blumenthal alternative

Choose a totally real field $M$ of degree $g$, with ring of integers $\mathcal O_M$, and distinct primes

$$
\lambda\mid p,
\qquad
\lambda'\mid q.
$$

For an abelian variety $A$ with real multiplication $\iota:\mathcal O_M\hookrightarrow\operatorname{End}(A)$, the modules

$$
A[\lambda],\qquad A[\lambda']
$$

are each two-dimensional over $k_\lambda$ and $k_{\lambda'}$ under the standard Hilbert--Blumenthal determinant condition. Thus one may impose

$$
A[\lambda]\simeq V_{\bar\rho},
\qquad
A[\lambda']\simeq V_{\bar\rho_{\mathrm{aux}}}. \tag{4.1}
$$

The underlying moduli variety has dimension $g$. The two level structures are finite data: away from their residue characteristics they cut out a finite étale cover and do not reduce dimension. Hence the space retains $g$ deformation directions for local approximation and open reduction conditions.

### 4.3 Choosing the coefficient field and its primes

The residue fields must match the coefficient fields of the representations. Choose finite extensions $\widetilde k/k$ and $\widetilde k'/k'$ that can occur as residue fields of primes of one totally real field $M$, replace the representations by scalar extension, and require identifications

$$
k_\lambda\xrightarrow{\sim}\widetilde k,
\qquad
k_{\lambda'}\xrightarrow{\sim}\widetilde k'.
$$

Often it is clearest to arrange residue degree one and identify $k_\lambda=\mathbf F_p$, $k_{\lambda'}=\mathbf F_q$. If the original representation has a larger coefficient field, scalar restriction is generally wrong—it changes dimension—whereas scalar extension preserves the two-dimensional rank. An embedding $k_\lambda\hookrightarrow k$ without equality after the declared scalar extension is not enough: the two finite group schemes would have different orders. We therefore enlarge coefficients first and then choose matching residue degrees.

The field $M$ is auxiliary. It may be chosen so that $p$ and $q$ are unramified, the polarization ideal is prime to $pq$, and sufficiently many other primes support neat level. These are finite splitting and avoidance conditions. They do not assert that every prescribed $M$ works.

The existence of a coefficient field with selected residue degrees is an arithmetic input to the present construction. Once such an $M$ is fixed, all residue-field identifications and unramifiedness hypotheses are recorded explicitly. Different valid choices of $M$ produce different Hilbert modular varieties; none is canonical.

There is no advantage in making $M$ unnecessarily large. Its degree is the dimension of the moduli space and the dimension of the resulting abelian variety. A larger degree supplies more analytic room but also enlarges the polarization and component bookkeeping. The smallest degree compatible with the residue fields and local construction is usually the most transparent choice.

### 4.4 A two-prime datum in degree two

As a concrete model, let $M$ be real quadratic, let $p$ and $q$ split,

$$
p\mathcal O_M=\lambda\lambda_2,
\qquad
q\mathcal O_M=\lambda'\lambda'_2,
$$

and fix a polarization type $\mathfrak c$ prime to $pq$. A point of the desired surface consists of an abelian surface $A$ with $\mathcal O_M$-action, a $\mathfrak c$-polarization, neat auxiliary level, and symplectic isomorphisms at $\lambda$ and $\lambda'$. The factors $A[\lambda_2]$ and $A[\lambda'_2]$ remain unconstrained. They are not extra geometric dimensions—the dimension comes from the two real embeddings—but they show why real multiplication separates coefficient-prime factors cleanly.

If instead $p$ is inert, $k_\lambda=\mathbf F_{p^2}$, and $A[\lambda]$ is two-dimensional over that field. It can realize a representation with those coefficients, but not an arbitrary two-dimensional $\mathbf F_p$-module without changing the coefficient interpretation.

## 5. The Hilbert--Blumenthal moduli datum

### 5.1 Why an action alone is insufficient

An embedding $\mathcal O_M\to\operatorname{End}(A)$ does not by itself define a well-behaved $g$-dimensional moduli problem. One must prescribe how $\mathcal O_M$ acts on tangent spaces, how duality interacts with the action, and which polarizations are allowed. These conditions cut out the intended PEL locus from a much larger moduli space of abelian varieties with incidental endomorphisms.

Fix a fractional ideal $\mathfrak c$ of $M$ and its totally positive cone $\mathfrak c^+$. We assume its prime factors avoid $p$, $q$, and the auxiliary level. The ideal records polarization type globally and prevents a hidden narrow-class ambiguity from being mistaken for a connected moduli space.

### 5.2 Hilbert--Blumenthal abelian schemes

For a connected $F$-scheme $S$ of characteristic zero, a Hilbert--Blumenthal abelian scheme of type $(M,\mathfrak c)$ is a tuple $(A,\iota,\lambda)$ where:

1. $A/S$ is an abelian scheme of relative dimension $g=[M:\mathbf Q]$;
2. $\iota:\mathcal O_M\to\operatorname{End}_S(A)$ is a ring embedding;
3. the determinant condition holds:
   $$
   \det(T-\iota(a)\mid\operatorname{Lie}A)
   =\prod_{\tau:M\hookrightarrow\overline{\mathbf Q}}(T-\tau(a)); \tag{5.1}
   $$
4. $\lambda$ is an $\mathcal O_M$-linear $\mathfrak c$-polarization: it is an identification of $\mathfrak c$ with the module of symmetric $\mathcal O_M$-linear homomorphisms $A\to A^\vee$ carrying $\mathfrak c^+$ to polarizations, and the evaluation map
   $$
   A\otimes_{\mathcal O_M}\mathfrak c\longrightarrow A^\vee,
   \qquad x\otimes c\longmapsto\lambda(c)(x),
   $$
   is an isomorphism.

The determinant identity is interpreted after base change to a field containing the images of the embeddings, and therefore descends as a polynomial identity. It says that each real embedding contributes one tangent direction. Without it, the action could occur with unequal multiplicities, giving the wrong dimension and local model.

Some authors place $\mathfrak c^{-1}$ rather than $\mathfrak c$ in the polarization module. Either convention is valid, but it changes the displayed pairing line. We fix the convention above once and use its induced alternating modules at every level.

### 5.3 Polarization pairings at coefficient primes

Put

$$
\mathfrak c^\vee=\operatorname{Hom}_{\mathbf Z}(\mathfrak c,\mathbf Z)
=\mathfrak d_M^{-1}\mathfrak c^{-1}.
$$

For an integer $m$ invertible on the base, evaluate the ordinary Weil pairing against every polarization in the ordered module:

$$
\langle x,y\rangle_m(c)=e_m(x,\lambda(c)y).
$$

As a function of $c$, the right side belongs to
$\operatorname{Hom}_{\mathbf Z}(\mathfrak c,\mu_m)=(\mathfrak c^\vee/m\mathfrak c^\vee)(1)$.
Rosati self-adjointness of the $\mathcal O_M$-action makes this form $\mathcal O_M$-balanced, and symmetry of $\lambda(c)$ makes it alternating. The tensor-polarization isomorphism in Section 5.2 and perfectness of the Weil pairing identify its adjoint with an isomorphism, so it is perfect. Projecting to a prime $\mathfrak l\mid\ell$ gives a perfect alternating form on $A[\mathfrak l]$ with value line

$$
L_{\mathfrak l}(1)
=(\mathfrak d_M^{-1}\mathfrak c^{-1}\otimes k_{\mathfrak l})(1).
$$

After choosing a generator of its constant factor, this becomes

$$
e_{\mathfrak l}:A[\mathfrak l]\times A[\mathfrak l]
\longrightarrow \mu_{\ell}\otimes_{\mathbf F_\ell}k_{\mathfrak l}. \tag{5.2}
$$

The choice of generator is part of a fixed-pairing component. Changing it by $u\in k_{\mathfrak l}^\times$ changes the component coordinate, and a level automorphism of determinant $u$ has the same effect. This is why polarization type, pairing trivialization, and determinant character must be chosen together.

### 5.4 Neat auxiliary level

To obtain a scheme carrying a universal family, choose an integer $N\geq3$, prime to $pq\mathfrak c\mathfrak d_M$. A literal constant paired basis at level $N$ is the wrong arithmetic datum: over $\mathbf R$ its constant determinant line cannot be equivariantly identified with its cyclotomic twist. We therefore use the following explicit level in the realization range.

Choose an invertible fractional ideal $I$ and take the tensor polarization type

$$
\mathfrak c_I=\mathfrak d_M^{-1}I^{-2},
\qquad
\mathfrak c_I^\vee=I^2.
$$

The **cyclotomic-split principal source** is

$$
\mathscr L_{I,N}^{\natural}
=(I/NI)\oplus(I/NI)(1),
\tag{5.3}
$$

with pairing

$$
((a,b),(a',b'))\longmapsto ab'-a'b
\in(I^2/NI^2)(1).
\tag{5.4}
$$

A corrected auxiliary level is an isometry
$\eta_N^{\natural}:\mathscr L_{I,N}^{\natural}\xrightarrow{\sim}A[N]$.
After an algebraic extension and a choice of a primitive $N$th root, (5.3) becomes an ordinary full principal frame with a fixed pairing orientation. Thus its geometric congruence subgroup is the usual one, while its arithmetic descent already contains the cyclotomic action needed at real places.

This level is neat. Indeed a polarization-preserving automorphism fixing it acts trivially on $A[N]$. Its action on every prime-adic Tate lattice at a prime dividing $N$ is a finite-order matrix congruent to $1$ modulo $N$. The principal congruence kernel is torsion-free for $N\geq3$: after replacing a torsion matrix by one of prime order and expanding $(1+NA)^r=1$, reduction at a prime dividing $N$ forces $A$ to be divisible by arbitrarily high powers of that prime. Hence the matrix, and by faithfulness the automorphism, is the identity.

More general neat levels remain legitimate for the abstract geometric cover, but their descent and local points must be proved separately. The construction below uses (5.3), so representability does not depend on an unspecified rigidification.

### 5.5 The untwisted fine space

Let $Y=Y_{M,\mathfrak c}(\mathfrak n)$ denote the moduli scheme of tuples $(A,\iota,\lambda,\eta_{\mathfrak n})$ satisfying the preceding conditions. In the realization construction this means the corrected tensor datum $(\mathfrak c_I,\eta_N^{\natural})$.

The phrase “one component” is deliberate. The full Hilbert modular scheme may have components indexed by a narrow class quotient and level determinant data. Arithmetic Galois action can permute geometric components, so connectedness over $F$ does not imply geometric connectedness.

For the auxiliary data used here there is an explicit component. The corrected modular curve classifying

$$
(\mathbf Z/N\mathbf Z)\oplus\mu_N\xrightarrow{\sim}E[N]
$$

maps by $E\mapsto E\otimes_{\mathbf Z}I$ to the corrected Hilbert scheme. Its geometric source is connected, so its image lies on one geometric component, denoted $Y_I^{\mathrm{ten}}$. The map is defined over $\mathbf Q$. Every Galois conjugate of the component again contains the same image; disjointness of geometric components forces equality. Thus $Y_I^{\mathrm{ten}}$ is defined over $\mathbf Q$, hence over $F$, and every tensor seed constructed below lies on it.

In potential modularity the polarization ideal, PEL lattice, auxiliary level, and Hilbert component are auxiliary rather than prescribed arithmetic output. We may therefore take

$$
I=\mathcal O_M,
\qquad
\mathfrak c=\mathfrak d_M^{-1},
\qquad
\mathfrak c^\vee=\mathcal O_M,
\qquad
Y^\circ=Y_{\mathcal O_M}^{\mathrm{ten}}.
\tag{5.5}
$$

Then both determinant lines are the ordinary cyclotomic lines required by the residual representations. This exact reduction changes neither representation nor any requested local behavior. It is unavailable only in a different problem that externally prescribes a nonsquare narrow polarization class; such a problem must supply its own component and seeds.

Analytically, a chosen component over $\mathbf C$ is $\Gamma\backslash\mathfrak H^g$, where $\Gamma$ preserves the lattice, polarization class, orientation, and auxiliary level. The product $\mathfrak H^g$ is connected and contractible, so the quotient is connected. This proves connectedness of that complex component, but it does not determine its descent field. The narrow-class and determinant calculation must still be made algebraically.

## 6. Imposing the two twisted levels

### 6.1 The target data

Let

$$
V=V_{\bar\rho}\quad\text{over }k_\lambda,
\qquad
V'=V_{\bar\rho_{\mathrm{aux}}}\quad\text{over }k_{\lambda'}.
$$

Choose Galois-equivariant pairing identifications

$$
\delta:\bigwedge^2V\xrightarrow{\sim}L_\lambda(1),
\qquad
\delta':\bigwedge^2V'\xrightarrow{\sim}L_{\lambda'}(1). \tag{6.1}
$$

Equivalently, the determinant characters of the two representations equal the multiplier characters imposed by the polarization datum. In the locally principal normalization these are $\bar\chi_p$ and $\bar\chi_q$.

For an $F$-scheme $S$ in characteristic zero, define $\mathcal X(S)$ to be isomorphism classes of

$$
(A,\iota,\lambda,\eta_{\mathfrak n},\alpha,\alpha'), \tag{6.2}
$$

where the first four entries form an $S$-point of $Y$ and

$$
\alpha:V_S\xrightarrow{\sim}A[\lambda],
\qquad
\alpha':V'_S\xrightarrow{\sim}A[\lambda'] \tag{6.3}
$$

are $\mathcal O_M$-linear pairing-preserving isomorphisms of finite étale group schemes over $S$. Over a field this is exactly Galois equivariance on geometric points. For disconnected $S$, the definition is applied componentwise.

### 6.2 Descent as a product cocycle

After a finite Galois extension $K/F$ splitting both modules and their pairing lines, the functor becomes the usual fixed-pairing full $(\lambda,\lambda')$-level cover of $Y$. The two frame cocycles combine into

$$
c:G_F\longrightarrow
\operatorname{SL}_2(k_\lambda)\times
\operatorname{SL}_2(k_{\lambda'}). \tag{6.4}
$$

Because $p\ne q$, the two finite level group schemes are independent. The product in (6.4) does not mean that the resulting moduli space is a product: both factors act on level structures of the same abelian scheme. Twisting the full two-level cover by $c$ gives $X=X(V,V')$.

The pairing hypotheses are what make (6.4) land in the component-preserving group. If only similitudes were specified, the cocycle would act on the determinant coordinates as well, and one would have first to descend the union of the appropriate components.

### 6.3 Representability and the universal object

**Theorem 6.1 (fine twisted PEL space).** Assume:

- $M$ is totally real of degree $g$;
- $\lambda\mid p$ and $\lambda'\mid q$ are distinct, unramified in the datum, and prime to $\mathfrak c\mathfrak n$;
- the determinant condition (5.1) and pairing identifications (6.1) hold;
- the auxiliary level is the corrected cyclotomic-split level (5.3), or is another level for which neat fine representability and the required descent form have been verified;
- the tensor component $Y_I^{\mathrm{ten}}$ is used, or another geometrically connected polarization-orientation component has been defined over $F$ with its descent proved.

Then $\mathcal X$ is represented by a smooth quasi-projective $F$-scheme $X$ of pure dimension $g$. It carries a universal tuple (6.2). After a finite separable extension, $X$ is isomorphic to the corresponding fixed-pairing full-level scheme over the selected Hilbert modular component. Its geometric connectedness is a separate monodromy question treated in Chapter 8.

**Proof strategy.** Embed the PEL problem with neat level into a fine polarized-abelian moduli scheme. Real multiplication, Rosati compatibility, polarization type, and the determinant condition define the Hilbert--Blumenthal locus. The two prime-level frame schemes are finite étale in characteristic zero. Finally descend the fine cover and its universal tuple by the product cocycle.

**Proof.** A fixed polarization degree and sufficiently rigid prime-to-degree level place the underlying abelian schemes in a quasi-projective fine moduli scheme. The equations expressing the $\mathcal O_M$-action and its Rosati compatibility, together with the locally closed polarization-type and determinant conditions, cut out a quasi-projective fine PEL scheme. Since $\lambda$ and $\lambda'$ are invertible over $F$, their torsion is finite étale, and the two isomorphism functors in (6.3) are finite étale torsors over it. Fixed pairing selects open-and-closed subschemes.

Neatness makes every stabilizer trivial, so this is a scheme rather than merely a coarse space. Over $K$ the chosen Galois cocycle acts on the fine space and the universal tuple. Effective descent produces $X$ and its universal tuple over $F$. Smoothness and dimension will be verified intrinsically in the next section; quasi-projectivity and representability descend from the finite splitting extension. $\square$

The universal object is indispensable. A closed point of a coarse quotient would yield only an isomorphism class over an algebraic closure and could carry a descent obstruction. A point of $X$ literally pulls back the universal abelian scheme and both torsion identifications to its residue field.

It is useful to see exactly where automorphisms disappear. An automorphism $u$ of a polarized RM abelian variety preserving the chosen auxiliary level determines a torsion element of its level stabilizer. Polarization makes the automorphism group finite, while neatness says that the arithmetic stabilizer has no nontrivial torsion. Hence $u=1$. For a principal congruence frame this may be read concretely as the assertion that $u$ is congruent to $1$ at the auxiliary ideal. The argument does not require the two residual representations to have large image.

If the auxiliary level is omitted, the involution $[-1]$ normally remains. The coarse quotient can still be smooth because a finite stabilizer may act without producing visible singularities at every point. Smoothness of the coarse variety therefore does not imply fineness, and it does not manufacture a universal abelian scheme. Representability and smoothness solve different problems.

## 7. Deformations, smoothness, and dimension

### 7.1 The tangent problem

The preceding construction reduced smoothness to the untwisted PEL space, but the calculation is worth making because it explains the dimension and the role of every condition. Let $x=(A,\iota,\lambda,\eta,\alpha,\alpha')$ be a geometric point in characteristic zero. First-order deformations over the dual numbers are governed by lifts of the Hodge subspace

$$
\omega_A\subset H^1_{\mathrm{dR}}(A)
$$

that remain $\mathcal O_M$-stable and isotropic for the polarization form.

After extending scalars so that all embeddings $\tau:M\hookrightarrow\overline F$ are visible, the determinant condition decomposes de Rham cohomology as

$$
H^1_{\mathrm{dR}}(A)=\bigoplus_\tau H_\tau,
\qquad
\dim H_\tau=2,
\qquad
\dim(\omega_A\cap H_\tau)=1. \tag{7.1}
$$

Lifting one line in a two-dimensional symplectic plane contributes one tangent parameter. In dimension two every line is isotropic, so no further equation appears in that factor. Summing over the $g$ embeddings gives $g$ parameters.

### 7.2 Formal smoothness

**Proposition 7.1.** The characteristic-zero PEL space $Y$, and hence its finite étale two-level twist $X$, is smooth of dimension $g$.

**Proof strategy.** Infinitesimal deformation theory turns the problem into lifting $g$ independent lines. A line in a rank-two bundle lifts across a square-zero thickening, and the set of lifts is an affine space under a rank-one Hom module. Level structures of invertible order have unique infinitesimal lifts.

**Proof.** Let $S_0\hookrightarrow S$ be a square-zero thickening. The polarized abelian scheme deformation problem is equivalent to lifting its Hodge filtration subject to isotropy. The $\mathcal O_M$-action and (5.1) split this into the $g$ line-lifting problems of (7.1). Each line lifts locally on $S$, with obstruction in a second exterior condition that vanishes because the relevant quotient has rank one. Its differences form

$$
\operatorname{Hom}(\omega_\tau,H_\tau/\omega_\tau),
$$

a line. The polarization identifies complementary pieces and introduces no relation between distinct $\tau$. Thus the deformation functor is formally smooth with tangent dimension $g$.

The prime-to-characteristic auxiliary and $(\lambda,\lambda')$ levels are finite étale. Finite étale objects lift uniquely across nilpotent thickenings, so they add neither tangent directions nor obstructions. Characteristic-zero finite-type formal smoothness implies smoothness. Twisting can be checked after the finite splitting extension, so $X$ has the same property and dimension. $\square$

This proof does not claim a smooth integral model at $p$ or $q$. At those residue characteristics, full level is not étale and the local model can be singular. We need only a smooth variety over the number field and carefully chosen points in its local analytic spaces.

### 7.3 Why there is room

The two residual identifications are discrete finite étale choices over the generic fiber. Therefore

$$
\dim X=[M:\mathbf Q]=g, \tag{7.2}
$$

not $g-2$. Conditions such as good reduction, semistable reduction of a chosen type, or belonging to a specified residue disk are open conditions in $X(F_v)$; they do not normally impose algebraic codimension. This is the sense in which the Hilbert modular variety has room.

Dimension is not a substitute for local solvability. A positive-dimensional smooth variety may have no $F_v$-point, and a nonempty $F_v$-space may miss a desired open. We must construct one local abelian variety for every relevant place. Dimension then makes neighborhoods and simultaneous moving presentations available to the existence theorem.

## 8. Geometric components and monodromy

### 8.1 Three notions that must be separated

For a variety over $F$, the following are different:

1. it is connected over $F$;
2. it is geometrically connected;
3. a selected analytic component is stable under $G_F$.

A union of conjugate geometric components can be connected over $F$ without being geometrically connected. Later arithmetic approximation requires geometric connectedness. Selecting a complex component without checking its field of definition does not produce an $F$-variety at all.

Hilbert modular components are governed by polarization ideal classes, orientations, and determinant or similitude quotients. Full prime level adds pairing coordinates. Our construction first fixes the polarization-orientation component, then fixes the pairing values, and only then twists by cocycles that preserve them.

### 8.2 The monodromy criterion

Let $Y^\circ$ be a geometrically connected fine Hilbert modular component before the two prime levels, and let

$$
Y_{\lambda,\lambda'}^\circ\longrightarrow Y^\circ
$$

be the fixed-pairing frame cover. Its geometric deck group is expected to be

$$
G=\operatorname{SL}_2(k_\lambda)\times
\operatorname{SL}_2(k_{\lambda'}). \tag{8.1}
$$

The exact statement needed is not merely that $G$ acts. It is that geometric monodromy surjects onto $G$.

**Theorem 8.1 (connectedness criterion).** Assume the geometric monodromy representation of $Y^\circ$ on the two universal torsion modules has image (8.1). Then the fixed-pairing simultaneous frame cover is geometrically connected. Every twist of this cover by a cocycle with values in $G$ is geometrically connected.

**Proof strategy.** A finite étale cover of a connected geometric base is connected exactly when geometric monodromy acts transitively on one geometric fiber. The fiber is a $G$-torsor, and surjectivity makes the action simply transitive. A twist becomes the original cover over an algebraic closure.

**Proof.** Choose a geometric basepoint. The fiber of the frame cover is a principal homogeneous $G$-set. By the classification of finite étale covers, its connected components are the orbits of the geometric fundamental group. Surjectivity of monodromy gives one orbit, so the cover is geometrically connected. If $X$ is a twist, then $X_{\overline F}$ is isomorphic to the untwisted cover over $\overline F$; geometric connectedness follows. $\square$

### 8.3 Verifying the hypothesis

For the standard Hilbert modular datum, the analytic component is a quotient of $\mathfrak H^g$ by an arithmetic group. Adding fixed-determinant levels replaces that group by the intersection with principal congruence subgroups at $\lambda$ and $\lambda'$. Surjectivity in (8.1) follows when reduction of the arithmetic group maps onto each special linear factor and onto their product. Strong approximation for the simply connected derived group supplies this only after the relevant lattice, auxiliary level, and component stabilizer have been included in the calculation, and under the following explicit safeguards:

- $\lambda$ and $\lambda'$ are distinct and outside a finite exceptional set;
- the auxiliary level is prime to them;
- the chosen determinant and positivity conditions do not shrink the derived group;
- no accidental common quotient couples the two residual factors.

For small primes or special coefficient fields, surjectivity must be checked rather than asserted. If its image is a proper subgroup $H$, the frame cover has several geometric components indexed by $H$-orbits. One may still select a component, determine its field of definition, and twist only by a cocycle landing in its stabilizer. Any later arithmetic approximation must use that geometrically connected component over its actual field of definition. If this requires replacing the original base field, that replacement is made before the final datum is declared, and the residual images and all local conditions are rechecked there.

Surjectivity onto each factor separately is not always enough for surjectivity onto the product. A subgroup of $G_1\times G_2$ can project onto both factors while being the graph of an isomorphism between quotients. Here the distinct residue characteristics usually rule out such a coupling: the nonabelian simple quotients of the two special linear groups have different characteristics and, outside small exceptional coincidences, are nonisomorphic. Any remaining common abelian quotient is eliminated by working in the derived, fixed-determinant group and checking the small primes directly. This product check is the precise reason for the last bullet of Section 8.3.

The analytic picture gives the same conclusion. Reduction modulo $\lambda\lambda'$ maps the relevant congruence group to the product of the two finite groups by the Chinese remainder theorem, provided the global derived group has strong approximation and the determinant condition has already been separated off. The kernel defines a connected quotient of $\mathfrak H^g$. Twisting changes its descent action but not this geometric analytic space.

Here is the concrete congruence argument that verifies the product assertion in the standard datum. Let $\Gamma\subset\operatorname{SL}_2(M)$ be the arithmetic group of the selected component. This is not an arbitrary finite-index subgroup: it is the exact stabilizer of a projective PEL lattice with a principal congruence level. Its local open stabilizers therefore contain principal congruence kernels. After choosing coordinates on the projective lattice and clearing the finitely many denominators, their intersection contains a global principal congruence subgroup

$$
\Gamma(\mathfrak a)=
\ker\bigl(\operatorname{SL}_2(\mathcal O_M)\longrightarrow
\operatorname{SL}_2(\mathcal O_M/\mathfrak a)\bigr).
$$

Suppose $\lambda$ and $\lambda'$ are distinct and avoid $\mathfrak a\Sigma_0$. Given $x\in k_\lambda$, the Chinese remainder theorem chooses $\widetilde x\in\mathcal O_M$ satisfying

$$
\widetilde x\equiv x\pmod\lambda,\qquad
\widetilde x\equiv0\pmod{\mathfrak a\lambda'}.
$$

Then the upper and lower elementary matrices with parameter $\widetilde x$ lie in $\Gamma(\mathfrak a)$, reduce to the desired elementary matrix at $\lambda$, and reduce to the identity at $\lambda'$. Reversing the roles of the primes gives elementary matrices in the second factor. Upper and lower elementary matrices generate $\operatorname{SL}_2$ over a finite field: Gaussian elimination reduces any determinant-one matrix to a diagonal one, and a diagonal determinant-one matrix is a product of elementary matrices. Hence

$$
\Gamma\longrightarrow
\operatorname{SL}_2(k_\lambda)\times
\operatorname{SL}_2(k_{\lambda'})
$$

is surjective. There are finitely many component lattices, so enlarging $\Sigma_0$ once makes the argument uniform over all selected components. Thus “monodromy-admissible” means precisely that the two primes avoid the discriminant, polarization and lattice denominators, auxiliary level, and this finite congruence set. Under that check, the hypothesis of Theorem 8.1 is proved rather than assumed.

### 8.4 Determinants and component stability

The geometric group in (8.1) contains only determinant-one changes of frame. Galois itself acts as a similitude because it acts on the pairing line. Equation (6.1) makes the multiplier of the target representation equal to that of the universal torsion. Dividing the two actions therefore gives determinant one. This quotient cocycle preserves the fixed-pairing component.

If $\det\bar\rho$ differs from the universal multiplier, the quotient cocycle lands in $\operatorname{GL}_2$ with nontrivial determinant and permutes components. Twisting a single component is then undefined. One could enlarge the moduli problem to the entire orbit of components, but the result would generally fail to be geometrically connected. Determinant compatibility is therefore used twice: to make realization possible and to make the correct component descend.

## 9. Local points as comparison objects

### 9.1 The local design principle

Fix a finite place $v$ of $F$. To prove $X(F_v)\ne\varnothing$, it is enough to exhibit a local Hilbert--Blumenthal abelian variety

$$
B_v/F_v
$$

with the prescribed PEL and auxiliary level data, including the chosen descent form of $\eta_{\mathfrak n}$, together with symplectic Galois-module isomorphisms

$$
V|_{G_{F_v}}\simeq B_v[\lambda],
\qquad
V'|_{G_{F_v}}\simeq B_v[\lambda']. \tag{9.1}
$$

At most places these identifications can be obtained after choosing unramified level frames. At places dividing $p$ or $q$, however, generic Galois modules do not record enough information about integral reduction. We then require comparison with specified finite locally free group schemes over $\mathcal O_{F_v}$.

The local field is allowed to be replaced only by an extension recorded in the eventual completion datum. Within that policy the tensor construction below supplies the five catalog loci. If a downstream application permits only unramified extensions at a coefficient prime, exact realization over such an extension remains a representation-theoretic hypothesis; a ramified splitting field cannot be used silently.

### 9.2 Good places

Suppose $v\nmid pq\mathfrak n\mathfrak c\mathfrak d_M$ and both target modules are unramified at $v$. Choose a good elliptic curve over a finite extension of the residue field, tensor it with $I$, and equip it with the corrected auxiliary level after a further finite residue extension. The two prescribed unramified representations and the two torsion modules all have finite cyclic Frobenius image. After one more finite residue extension, the relevant Frobenius powers act trivially on all four modules. Paired bases then give both frames on the same special-fiber tensor object. Smoothness of the integral Hilbert moduli scheme lifts that complete special point to the corresponding unramified extension of $F_v$. Thus the good locus is nonempty after a finite unramified extension.

This argument deliberately passes to a closed point of the *twisted* special fiber. It would be false to start with an arbitrary good HBAV and claim that two unrelated Frobenius matrices occur on it over the original residue field. The finite unramified extension, and not unramifiedness alone, resolves the simultaneous frame constraint.

Only finitely many places enter the local package. Outside that set, no local point is prescribed. A future global abelian variety would automatically have good reduction away from finitely many places, so there is no reason to solve infinitely many local moduli problems here.

A standard source of a comparison point is the tensor construction. If $E/F_v$ is an elliptic curve and $I$ is an invertible $\mathcal O_M$-ideal, the sheaf $E\otimes I$ is an abelian variety isomorphic to $E^g$ after a temporary integral basis choice, with real multiplication and polarization module $\mathfrak d_M^{-1}I^{-2}$. Its $\mathfrak l$-torsion is obtained from $E[\ell]$ by the corresponding residue factor. Thus a local elliptic curve whose $p$-torsion realizes the desired local target can seed a local HBAV.

Over the original local field this simple construction does not realize two unrelated modules automatically. At a good place the finite unramified extension just constructed trivializes all four unramified systems simultaneously. At a coefficient or semistable place an allowed common splitting extension does the analogous job on generic torsion. When the completion policy is more restrictive, exact realization over an allowed field is genuine extra input and cannot be replaced by a claim that tensoring alone matches arbitrary modules.

### 9.3 Archimedean places

At a real place $v$, the complex points of a Hilbert modular component are modeled by $\mathfrak H^g$ modulo an arithmetic group. The chosen positivity component has real points precisely when its descent datum admits a real Hodge structure with the prescribed torsion involutions and auxiliary rigidification.

For an odd two-dimensional module, complex conjugation has eigenvalues $1$ and $-1$ at each odd residual prime. This is the torsion shadow of a polarized weight-one real Hodge structure. The corrected tensor datum makes the converse constructive. Take

$$
E/\mathbf R:y^2=x^3-x,
\qquad A=E\otimes I.
$$

If $P$ is the class of $1/N$ on $\mathbf C/(\mathbf Z+i\mathbf Z)$, the Weil pairing identifies the anti-invariant complement of $P$ with $\mu_N$. It therefore gives a paired equivariant isomorphism

$$
(\mathbf Z/N\mathbf Z)\oplus\mu_N\xrightarrow{\sim}E[N].
$$

Tensoring with $I$ supplies (5.3) on $A$. The point lies on $Y_I^{\mathrm{ten}}$ by its definition. At each odd residual prime, oddness gives one $+1$ and one $-1$ eigenline; choosing a map on the positive line and normalizing the negative line by the pairing gives the required frame. Hence two odd determinant-compatible residual systems produce a real point of the simultaneous twist, not merely a compatible involution.

Choosing a sufficiently small neighborhood in its real manifold component retains the polarization signs, corrected auxiliary level, and both frames. Requiring such an open at every real place is what later forces every embedding of the output field to be real; the mere fact that $F$ is totally real is not enough.

To make the involution calculation explicit, let $c$ be complex conjugation. Since $c^2=1$ and the residual characteristic is odd, $V$ decomposes into its $+1$ and $-1$ eigenspaces. Oddness makes each eigenspace one-dimensional. A real polarized complex torus has exactly this action on each two-dimensional coefficient-prime factor. Hence one can match frames after choosing their pairing orientation. If the determinant at $c$ were $+1$, the eigenvalues would be both $1$ or both $-1$; such a frame would lie on no real point of the desired Hilbert modular component.

### 9.4 Places above the target characteristic

Let $v\mid p$. The finite group scheme $B_v[\lambda]$ over $F_v$ is étale because $F_v$ has characteristic zero, but an integral model over $\mathcal O_{F_v}$ need not be étale. Suppose the target local module is the generic fiber of a finite locally free commutative group scheme $\mathcal G_v$ of rank $|k_\lambda|^2$, with $\mathcal O_M/\lambda$-action and a perfect alternating pairing into the appropriate roots-of-unity group scheme. This model witnesses finite flatness after every finite extension.

For an ordinary or nonordinary catalog condition, choose the corresponding tensor abelian scheme $\mathcal B_v$ as in Chapter 11. If the target representation and $\mathcal B_v[\lambda]$ are not already paired-isomorphic, pass to a permitted finite extension splitting both finite generic representations and their determinant lines. Paired bases then give the frame. The base change of $\mathcal G_v$ still witnesses finite flatness of the prescribed representation, while the base change of $\mathcal B_v$ retains its chosen reduction type. This does **not** identify their integral models.

If an application requires the stronger assertion that the named target model itself occurs as PEL torsion, it must additionally supply an isomorphism

$$
\mathcal G_v\xrightarrow{\sim}\mathcal B_v[\lambda] \tag{9.2}
$$

of finite locally free paired group schemes.

Passing to generic fibers gives the first isomorphism in (9.1), but (9.2) is stronger than the finite-flat locus required in the catalog. Two nonisomorphic finite-flat models can have isomorphic generic Galois modules. Conversely, an abstract generic isomorphism need not extend over $\mathcal O_{F_v}$. We never infer extension from generic data alone.

Cartier duality checks the pairing integrally. The polarization identifies the dual of $\mathcal B_v[\lambda]$ with the appropriate twist by the polarization line. Therefore an isomorphism in (9.2) must carry the Cartier-dual pairing on $\mathcal G_v$ to the Weil pairing, not simply identify their generic points. This forces the determinant character on inertia and prevents a generic frame with the wrong multiplier from masquerading as integral level.

The auxiliary $\lambda'$-torsion has order prime to the residue characteristic at $v$. Over an abelian scheme with good reduction it is finite étale and unramified, so it may be compared with $V'$ by a prime-to-$p$ frame when the latter is unramified with the same Frobenius. For a semistable comparison object it can be ramified, and its actual generic Galois module must instead be checked directly. Prime-to-residue-characteristic makes the level étale; it does not by itself make it unramified without good reduction.

### 9.5 Places above the auxiliary characteristic

For $v\mid q$, reverse the roles. A paired finite locally free model $\mathcal G'_v$ of $V'|_{G_{F_v}}$ witnesses finite flatness; a permitted splitting extension gives a generic frame to the chosen ordinary or nonordinary $\lambda'$-torsion seed. If the application asks to realize the named integral model itself, require the stronger comparison

$$
\mathcal G'_v\xrightarrow{\sim}\mathcal B_v[\lambda']. \tag{9.3}
$$

The target $\lambda$-torsion is prime to the residue characteristic and may be matched as an étale generic level. If the comparison abelian variety has good reduction, this module is unramified; under semistable reduction its actual inertia action must be matched rather than discarded. This separation is one benefit of $p\ne q$, but it removes integral connectedness issues only for the prime-to-residue-characteristic level.

A common error is to say that finite flatness of the representation uniquely determines (9.2) or (9.3). It does not in general. The ordinary and nonordinary local-open conclusions require finite flatness of the prescribed generic representation and a generic paired frame; exact identification with a named integral PEL kernel is a separate, stronger datum.

### 9.6 Ramified primes and primes of the datum

At places dividing $\mathfrak d_M$, the polarization degree, or the auxiliary level, a hyperspecial integral model is unavailable or inappropriate. We place every such place in a finite exceptional set $S_{\mathrm{ram}}$. For each $v\in S_{\mathrm{ram}}$ we choose one of two honest options:

- construct a local point on the generic-fiber moduli space using an abelian variety with the full required datum, then take a small analytic neighborhood; or
- alter the auxiliary choices before the construction so that the offending place is avoided.

We do not deduce local solvability merely from nonemptiness over $\overline F_v$. Nor do we call a generic abelian variety “integral” without a model. If semistable rather than good reduction is prescribed, the chosen local semiabelian model supplies the condition.

### 9.7 A worked pair of residual places

Assume $v\mid p$, $w\mid q$, and both are unramified over their rational primes. At $v$, choose an ordinary HBAV $\mathcal B_v$ whose connected--étale sequence on $\lambda$-torsion is

$$
0\longrightarrow \mu_p\otimes k_\lambda
\longrightarrow \mathcal B_v[\lambda]
\longrightarrow (\mathbf Z/p\mathbf Z)\otimes k_\lambda
\longrightarrow0. \tag{9.4}
$$

If $V|_{G_{F_v}}$ is the generic fiber of precisely this extension, with its Cartier-dual pairing, (9.2) gives the target level. The $\lambda'$-torsion is étale and can be framed after arranging its unramified Frobenius.

At $w$, choose $\mathcal B_w$ so that the analogous sequence occurs for $\lambda'$ and realizes $V'|_{G_{F_w}}$. Its $\lambda$-torsion is now the prime-to-residue-characteristic level. This example shows that “ordinary at both residual primes” means two different integral decompositions on two different local abelian varieties. There is no single special fiber in which both primes equal the residue characteristic.

As a counterexample, a wildly ramified generic $V|_{G_{F_v}}$ that admits no finite locally free model of the prescribed rank cannot be realized by the $\lambda$-torsion of an abelian scheme with good reduction. No amount of global approximation repairs this local obstruction.

## 10. Local conditions are open

### 10.1 From a point to a neighborhood

Later approximation uses nonempty open subsets $\Omega_v\subset X(F_v)$, not isolated local points. Once a comparison point $x_v$ has been constructed, we must show that the arithmetic properties needed later persist in a neighborhood.

Because $X$ is smooth, $X(F_v)$ is an analytic manifold near $x_v$. The universal abelian scheme and its level structures vary over this neighborhood. After shrinking, finite étale torsion local systems are locally constant. Integral properties are handled by extending the universal object over a suitable integral neighborhood or, equivalently, by choosing a residue tube inside an integral model.

### 10.2 Good reduction

Good reduction at $v$ is encoded by requiring the moduli point to extend to the good integral locus of the PEL model over $\mathcal O_{F_v}$. If $x_v$ extends to a smooth integral point, the inverse image of its residue class is an open subset of $X(F_v)$. Every point in a sufficiently small such tube corresponds to an abelian variety with good reduction and the same prime-to-$v$ level behavior.

This statement uses the moduli interpretation, not a claim that good reduction is Zariski open on the generic fiber in isolation. The relevant topology is the $v$-adic topology and the open is a tube around an integral point.

### 10.3 Semistable reduction

Semistable reduction may be imposed by working near a chosen boundary chart in a toroidal compactification whose universal semiabelian scheme has the desired toric rank. Fixing the valuations of the degeneration parameters in an open range, and requiring the remaining parameters to be units, defines an analytic open. Alternatively, when an explicit local family is available, semistability and the desired split toric character can be read from its semiabelian model and are stable in a sufficiently small neighborhood. The required chart or explicit family is part of the local verification; the existence of a semistable comparison point alone does not prove openness of every refined toric condition.

One must not identify the entire boundary divisor with one reduction type. Intersections of boundary strata can change toric rank, and cancellation in local parameters can alter splitting. We choose a smooth point of a named stratum and shrink away from all deeper strata.

### 10.4 Constancy of finite-flat comparison

At $v\mid p$, the condition that the generic $\lambda$-torsion equal $V|_{G_{F_v}}$ is already built into $X$. If $V$ is the generic fiber of $\mathcal G_v$, this fixed representation is finite flat throughout the local open: the same $\mathcal G_v$ witnesses the property. Independently, a good residue tube makes every nearby universal abelian variety an abelian scheme, and fixing an ordinary or local--local special point retains that reduction type.

The stronger condition that the universal integral kernel itself be isomorphic to one named model $\mathcal G_v$ is not automatic on an arbitrary disk and is not part of the basic finite-flat conclusion. When it is required, one must construct an integral isomorphism at the seed and restrict to an integral neighborhood on which its finite isomorphism scheme has a section. The same distinction applies at $q$.

Notice the two distinct sorts of openness. The generic representation is fixed everywhere on the twisted moduli variety by the universal level isomorphism. The integral finite-flat type is fixed only on the selected local neighborhood. Likewise, good reduction is not encoded by the residual representation alone; it is encoded by extension of the universal abelian scheme over the integral tube. Keeping these layers separate avoids deriving integral conclusions from generic torsion.

### 10.5 The finite local set

Let $S$ contain:

- every archimedean place;
- all places above $p$ and $q$;
- places where $M$, $\mathfrak c$, or the auxiliary level causes bad integral geometry;
- places where prescribed good or semistable reduction is required;
- any place used to control ramification or splitting of the output extension.

For each $v\in S$, choose a nonempty open $\Omega_v\subset X(F_v)$ around the constructed comparison point. Several requirements at the same place are combined by intersection only after checking that the chosen point satisfies all of them. An empty intersection is not repaired by the global theorem.

## 11. Explicit local seeds

### 11.1 The Serre tensor construction

Local openness begins with a point, so we need a systematic source of polarized real-multiplication abelian varieties. Let $K$ be a field of characteristic zero, let $E/K$ be an elliptic curve, and let $I$ be an invertible fractional $\mathcal O_M$-ideal. Choosing a $\mathbf Z$-basis identifies $I$ with $\mathbf Z^g$ and suggests

$$
A=E\otimes_{\mathbf Z}I\simeq E^g. \tag{11.1}
$$

Changing the basis by a matrix in $\operatorname{GL}_g(\mathbf Z)$ gives the evident integral isomorphism between the two products. Thus (11.1) is independent of the temporary basis and carries an $\mathcal O_M$-action through multiplication on $I$.

Trace duality computes the dual lattice:

$$
I^\dagger=\operatorname{Hom}_{\mathbf Z}(I,\mathbf Z)
=\mathfrak d_M^{-1}I^{-1}. \tag{11.2}
$$

Using the canonical principal polarization of $E$, an $\mathcal O_M$-linear homomorphism $A\to A^\vee$ is therefore multiplication by an element of

$$
\mathfrak c_I=\mathfrak d_M^{-1}I^{-2}. \tag{11.3}
$$

It is a polarization exactly when that element is totally positive. Hence the ordered polarization module of $A$ is $(\mathfrak c_I,\mathfrak c_I^+)$. This calculation has two consequences. It identifies the component reached by the tensor construction, and it warns that tensor seeds do not automatically reach every prescribed polarization class. If $\mathfrak c$ is not in the square class (11.3), one needs another PEL seed or an explicitly controlled isogeny.

The determinant condition is equally concrete. Since

$$
\operatorname{Lie}(A)=\operatorname{Lie}(E)\otimes_{\mathbf Z}I,
$$

the characteristic polynomial of $a\in\mathcal O_M$ on the Lie algebra is the characteristic polynomial of multiplication by $a$ on $I\otimes K$, namely $\operatorname N_{M/\mathbf Q}(T-a)$. Thus every tensor seed has Hilbert--Blumenthal Hodge type.

At a prime $\mathfrak r\mid r$ unramified in $M$, tensoring commutes with taking $r$-torsion and projecting by the idempotent for $\mathfrak r$. The result is a rank-two $k_{\mathfrak r}$-module. The Weil pairing on $E[r]$, trace duality (11.2), and the polarization module (11.3) recover precisely the determinant line

$$
(\mathfrak d_M^{-1}\mathfrak c_I^{-1}\otimes k_{\mathfrak r})(1).
$$

Thus the tensor construction respects the same pairing convention as the global frame cover; it is not merely an unpolarized source of abelian varieties.

### 11.2 Real and good seeds

Over $\mathbf R$, choose an elliptic curve and form $E\otimes I$. For any odd $r$, complex conjugation acts on $E[r]$ with one $+1$ eigenline and one $-1$ eigenline. Conversely an involution on a two-dimensional vector space over a field of odd characteristic has this shape exactly when its determinant is $-1$. Once the $+1$ lines are identified, there is a unique scaling of the $-1$ line that makes the frame preserve the chosen alternating pairing.

**Proposition 11.1 (real frame criterion).** Let $V_{\mathfrak r}$ be a paired rank-two $k_{\mathfrak r}$-representation of $G_{\mathbf R}$, with $r$ odd. It admits a paired frame to the $\mathfrak r$-torsion of a real polarized tensor seed if and only if complex conjugation has determinant $-1$. With the corrected tensor component and level (5.3), simultaneous frames at $\mathfrak p$ and $\mathfrak q$ exist exactly when this condition holds at both primes.

**Proof.** Since $c^2=1$ and $2$ is invertible, $V_{\mathfrak r}=V^+\oplus V^-$. The determinant is $-1$ precisely when both eigenspaces are lines. The same is true for $E[r]$. Choose any nonzero map $V^+\to E[r]^+$. Perfectness pairs $V^+$ with $V^-$ and $E[r]^+$ with $E[r]^-$, so there is a unique map on the negative line making the total map pairing-preserving. The converse follows because a paired isomorphism preserves the action and therefore the determinant. Apply the construction independently at the two odd primes to the real tensor point of Section 9.3; its corrected auxiliary level and membership in $Y_I^{\mathrm{ten}}$ were already proved there. $\square$

For arbitrary externally fixed PEL data, oddness still need not select a component or auxiliary rigidification. In the present realization problem those data are auxiliary, and (5.3)--(5.5) remove both obstructions. Proposition 11.1 is therefore a real-point theorem for the actual catalog datum.

Now let $K$ be a finite extension of $\mathbf Q_r$ with valuation ring $R$ and residue field $k$. Suppose $r$ is prime to the discriminant, polarization degree, auxiliary level, $p$, and $q$. The integral Hilbert moduli scheme and its two frame covers are smooth and finite étale at $r$. If a point $\bar y$ of the chosen twisted special fiber exists over $k$, formal smoothness lifts it successively through $R/\pi^n$, and completeness gives $y\in X(K)$. Its universal abelian scheme has good reduction.

The full residue tube of $\bar y$ is open. In étale coordinates, fixing reduction modulo $\pi$ fixes each coordinate in a congruence ball. Every point in that ball extends to the same smooth integral chart and therefore has good reduction. Since the frame cover is finite étale, its chosen sheet is locally constant there. If the special fiber has no $k$-point but is geometrically nonempty, a closed point over some finite $k'/k$ gives a good seed over the corresponding unramified extension of $K$. This proves local solvability after that extension, not over the original field.

### 11.3 Ordinary and nonordinary seeds

At a place of residue characteristic $p$, a geometric frame on generic $p$-torsion is insufficient. The integral group scheme distinguishes ordinary and local--local behavior. Assume that $p>2$, $K/\mathbf Q_p$ and $M_{\mathfrak p}/\mathbf Q_p$ are unramified, and the polarization degree is prime to $p$.

Both kinds of seed exist after a finite unramified extension. Put $m=(p-1)/2$ and consider the Legendre family

$$
E_a:y^2=x(x-1)(x-a).
$$

Its Hasse invariant, up to a nonzero scalar, is

$$
H_p(a)=\sum_{i=0}^{m}\binom mi^2a^i.
\tag{11.3a}
$$

This polynomial is nonzero, so some $a\ne0,1$ over a finite residue extension has $H_p(a)\ne0$ and gives an ordinary curve. It also has a root over the algebraic closure because its degree is positive; that root is not $0$ or $1$, since $H_p(0)=1$ and Vandermonde's identity gives $H_p(1)=\binom{2m}{m}\equiv(-1)^m\pmod p$. Such a root gives a supersingular curve. Lifting a smooth Weierstrass equation to the unramified valuation ring preserves unit discriminant, producing ordinary and supersingular elliptic schemes. Tensoring them with $I$ gives good Hilbert--Blumenthal seeds on $Y_I^{\mathrm{ten}}$.

For an ordinary elliptic scheme $E/R$, the connected--étale sequence has the shape

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0 \tag{11.4}
$$

after a harmless unramified extension that trivializes the étale quotient. Tensoring with $I$ and taking the $\mathfrak p$-factor gives the corresponding multiplicative-by-étale sequence for $A[\mathfrak p]$. The ordinary deformation space is a formal torus: the extension class in (11.4) is the Serre--Tate coordinate, while the real-multiplication idempotents separate one such coordinate for each $p$-adic embedding. Ordinary special fibers therefore lift, and the nonvanishing of the relevant Hasse invariants makes the ordinary good locus open.

A supersingular elliptic curve instead has local--local $E[p]$: neither its geometric special fiber nor its Cartier dual has a nonzero étale quotient. Tensoring produces a nonordinary Hilbert--Blumenthal seed with a local--local $\mathfrak p$-factor. The nonordinary locus in the special fiber is closed, so it would be false to call it a Zariski-open condition. The correct open is the residue tube

$$
]\bar y[=\{y\in\mathcal X(R):y\bmod\pi=\bar y\}. \tag{11.5}
$$

Every point of (11.5) has the fixed special fiber $\bar y$ and hence the same local--local type. The tube is open in the $p$-adic topology and full-dimensional in étale coordinates.

In either case a prescribed $G_K$-module $V_{\mathfrak p}$ must be the generic fiber of a finite locally free paired $k_{\mathfrak p}$-module scheme $\mathcal G$. If the completion policy permits arbitrary finite extension, pass to the compositum of the splitting fields of $V_{\mathfrak p}$, the seed torsion, the other prescribed module, the other seed torsion, and their determinant lines. All four generic modules then admit simultaneous paired bases. The base-changed $\mathcal G$ witnesses finite flatness of the prescribed module, while good ordinary or local--local reduction of the tensor seed persists. Thus finite flatness plus the permitted splitting policy produces a point of the exact twist.

If the named model itself must equal the PEL kernel, one must instead exhibit the stronger pairing-preserving isomorphism

$$
\mathcal G\xrightarrow{\sim}A[\mathfrak p] \tag{11.6}
$$

for the seed. Finite flatness does not supply this integral isomorphism, and its model need not be unique. If only unramified completion extensions are allowed, even the generic frame must be supplied over an allowed field; the ramified splitting argument above is then unavailable.

### 11.4 Semistable seeds from Tate curves

Let $E_{q_0}/K$ be the Tate curve with $0<|q_0|<1$. It has split multiplicative reduction and uniformization

$$
E_{q_0}(\overline K)=\overline K^\times/q_0^{\mathbf Z}.
$$

For an odd prime $s$, choosing an $s$th root of $q_0$ gives an exact sequence

$$
0\longrightarrow\mu_s\longrightarrow E_{q_0}[s]
\longrightarrow\mathbf Z/s\mathbf Z\longrightarrow0, \tag{11.7}
$$

whose extension class is the Kummer class of $q_0$ in $K^\times/K^{\times s}$. Thus valuations and unit classes can be used to prescribe the residual extension. Tensoring with $I$ produces an HBAV with split toric reduction of rank $g$ and corresponding sequences at every coefficient factor.

An individual Tate ray is only one-dimensional, so for $g>1$ it cannot by itself prove the existence of an open subset of the Hilbert variety. We now place it in the required full-dimensional chart. Put

$$
I^\dagger=\mathfrak d_M^{-1}I^{-1},
\qquad
T_I=\underline{\operatorname{Hom}}_{\mathbf Z}(I^\dagger,\mathbf G_m),
\qquad
\mathfrak M=II^\dagger=\mathfrak d_M^{-1}.
\tag{11.7a}
$$

The cocharacter lattice of $T_I$ is $I$, and $\mathfrak M$ is the rank-$g$ Fourier-exponent lattice at the tensor cusp. In the cone of real homomorphisms positive on totally positive elements, choose a regular full-dimensional rational polyhedral cone $\sigma$ containing the trace functional $\xi\mapsto\operatorname{Tr}_{M/\mathbf Q}(\xi)$ in its interior. Such a cone is obtained by first taking a small rational simplicial cone around the trace ray and then applying toric subdivision away from that ray.

For a complete valuation ring $R$, let

$$
A_\sigma=\widehat{R[\sigma^\vee\cap N^{-1}\mathfrak M]}.
$$

Regularity gives, after a finite étale coefficient extension, parameters $t_1,\ldots,t_g$ and
$A_\sigma\simeq R'[[t_1,\ldots,t_g]]$. On the punctured locus define the period map

$$
u_Q:I\longrightarrow T_I,
\qquad
x(u_Q(a))=Q^{ax}\qquad(a\in I,\ x\in I^\dagger).
\tag{11.7b}
$$

For $c\in\mathfrak c_I^+$, the form $(a,b)\mapsto Q^{abc}$ is symmetric and positive for every valuation in $\sigma$. A periodic regular polyhedral decomposition of $I\otimes\mathbf R$ therefore gives toric formal charts whose transition functions are the monomials in (11.7b). They glue to the proper polarized Raynaud quotient. The positive quadratic support function supplies a relatively ample symmetric formal line bundle; proper formal algebraization turns the quotient into a projective family over $A_\sigma$, with an open semiabelian group scheme. Its generic punctured locus is an abelian scheme, while the deepest boundary stratum has split torus $T_I$ of rank $g$.

Multiplication on $I$ algebraizes to the $\mathcal O_M$-action. The equality $I\mathfrak c_I=I^\dagger$ gives the tensor-perfect ordered polarization, and the Lie algebra is rank one over $\mathcal O_M\otimes A_\sigma$, proving the determinant condition. The $N$-torsion of the boundary one-motive fits into

$$
0\longrightarrow(I/NI)(1)\longrightarrow[I\xrightarrow{u_Q}T_I][N]
\longrightarrow I/NI\longrightarrow0.
$$

Because the base contains the $N$-division monomials, this sequence has exactly the corrected level (5.3), with pairing (5.4). Finally the logarithmic differentials $d\log Q^\xi$, $\xi\in\mathfrak M$, identify the Kodaira--Spencer map with the identity on $\mathfrak M$. The classifying map is therefore étale in all $g$ period directions. Specializing $Q^\xi$ by the trace functional recovers $E_{q_0}\otimes I$, so the chart lies on $Y_I^{\mathrm{ten}}$.

Requiring each $v(t_i)$ to remain equal to a fixed positive value defines a nonempty analytic open. Every point reduces to the same deepest stratum, so its semiabelian torus has the same split character lattice and rank $g$. This is an ambient $g$-dimensional open, not merely the tensor ray. Deeper boundary strata are avoided by keeping every parameter valuation positive and fixed.

When $s$ equals the residue characteristic and $K/\mathbf Q_s$ is unramified, the canonical sequence (11.7) is the generic fiber of the finite flat Tate-torsion model used here precisely under the divisibility condition

$$
s\mid v_K(q_0). \tag{11.8}
$$

Indeed extensions of the constant group $\mathbf Z/s\mathbf Z$ by $\mu_s$ with the displayed generic filtration are classified by
$H^1(R,\mu_s)=R^\times/(R^\times)^s$. The class of $q_0$ belongs to its image in $K^\times/(K^\times)^s$ exactly when its valuation is divisible by $s$: necessity follows from the valuation map, while if $q_0=\pi^{sm}u$, multiplication by the $s$th power $\pi^{-sm}$ replaces it by the unit $u$. The corresponding fppf Kummer torsor on each component of $\mathbf Z/s\mathbf Z$ constructs the finite flat extension. This criterion concerns the canonical Tate extension under the stated unramified, odd-prime hypotheses; it does not say that every finite-flat representation comes from a Tate curve.

On the full chart a point gives a valuation homomorphism
$\nu_Q:\mathfrak d_M^{-1}\to\mathbf Z$. The same Kummer argument shows that canonical $p$-torsion at an unramified odd coefficient prime extends finite flat precisely when

$$
\nu_Q(\mathfrak d_M^{-1})\subset p\mathbf Z.
\tag{11.9}
$$

Indeed the Kummer classes obtained by evaluating $Q^{ax}$ must all have valuation divisible by $p$, and the products $ax$ generate $II^\dagger=\mathfrak d_M^{-1}$. Conversely unit representatives for these generators assemble the constant-lattice-by-$\mu_p$-lattice extension. Fixing the parameter valuations makes (11.9) locally constant. On the tensor ray it reduces to (11.8).

Semistable does not mean good. Even when (11.7) is finite flat, $E_{q_0}$ retains multiplicative reduction. This example cleanly separates a property of one torsion layer from a property of the whole abelian variety.

## 12. Persistence and simultaneous local conditions

### 12.1 Persistence under finite extension

Suppose $L/K$ is a finite extension of local fields, with valuation rings $S/R$. An abelian scheme over $R$ remains an abelian scheme over $S$, so good reduction persists. The special fiber is obtained by scalar extension; nonvanishing of Hasse invariants, and hence ordinarity, persists. Likewise the local--local condition is geometric: Frobenius and Verschiebung remain nilpotent after extending the residue field.

A semiabelian scheme remains semiabelian after base change. Toric rank is geometric and remains unchanged. A split torus stays split, while a nonsplit torus may become split. For a Tate parameter,

$$
v_L(q_0)=e(L/K)v_K(q_0), \tag{12.1}
$$

so exact normalized valuations do not remain constant. The divisibility in (11.8) persists, although it may become true only after a ramified extension and therefore need not descend.

Finite flatness is preserved for the simplest possible reason: if $V$ is the generic fiber of $\mathcal G/R$, then $V|_{G_L}$ is the generic fiber of $\mathcal G\times_RS$. Coefficient actions, pairings, connected--étale sequences, and Cartier duality all base-change. Exact generic frames restrict to $G_L$, but a frame that appears over $L$ need not descend to $K$.

| datum | behavior after finite extension |
|---|---|
| good reduction | persists |
| ordinary or local--local type | persists |
| semistability and toric rank | persist |
| split torus | remains split |
| nonsplit torus | may split |
| finite-flat model | base-changes to a model |
| paired frame | restricts, need not descend |
| normalized valuation | multiplied by ramification index |
| Kummer class | may become trivial |

This ledger matters because a later field construction may prescribe an extension of $K$, rather than $K$ itself, as a completion. Only the persistent conclusions may be carried across such an extension without further control.

### 12.2 Intersections must have a witness

Several nonempty open subsets of $X(K)$ can have empty intersection. An ordinary tube and a supersingular tube are disjoint, and two determinant components are open and closed. Therefore simultaneous local conditions are not assembled by proving their separate nonemptiness.

The safe order is point-centered. First construct one tuple

$$
x=(A,\iota,\lambda_A,\eta_{\mathfrak n},\alpha,\alpha')\in X(K) \tag{12.2}
$$

satisfying every desired condition. Then give each condition an open neighborhood of $x$ and intersect the finitely many neighborhoods. The intersection remains nonempty because it contains $x$.

This is especially important for the two frames. A point realizing $V$ on one HBAV and another point realizing $V'$ on a second HBAV do not define a point of the simultaneous cover. The common seed (12.2) must carry both frames. Likewise finite flatness and a Tate Kummer class must be verified on the same semistable seed before shrinking begins.

### 12.3 Components and degeneracy loci

Let $X^\circ$ be the $K$-defined open-and-closed component selected globally. Every local seed must lie in $X^\circ(K)$. A point on a conjugate geometric component is not a substitute. If the component exists only after an extension, that extension changes the base datum and all representation restrictions must be reconsidered.

Often one must avoid a proper closed locus $Z\subsetneq X^\circ$, such as a locus with extra endomorphisms. If the seed lies outside $Z$, then $X^\circ(K)\setminus Z(K)$ is open near it. If the seed lies in $Z$, shrinking cannot remove it; one needs a different seed.

Positive dimension helps only after this logical point is respected. In étale coordinates a proper closed subset has empty interior on a local irreducible branch unless it contains that branch. After a finite residue extension, one can choose a residue point outside the first nonzero reduction of its defining equation and lift it. This produces a new seed outside $Z$; it does not move the old seed.

### 12.4 The simultaneous-neighborhood theorem

**Theorem 12.1.** Let $K$ be $\mathbf R$ or a finite extension of $\mathbf Q_r$. Let $X^\circ$ be a smooth $K$-defined component of the determinant-compatible two-prime twist, and let $Z\subsetneq X^\circ$ be closed. Suppose

$$
x\in(X^\circ\setminus Z)(K)
$$

is a common seed carrying both paired frames and one of the following verified structures: a real component, a good integral model, an ordinary good model, a nonordinary local--local good model, or a semiabelian model with fixed boundary stratum. Then there is a nonempty open

$$
\Omega_x\subset(X^\circ\setminus Z)(K) \tag{12.3}
$$

on which both paired torsion representations, the auxiliary level, the ordered polarization type, the component, and the named local condition all persist. Any finite list of valuation-shell, Kummer, or splitness conditions that is locally constant at $x$ may be retained after further shrinking.

**Proof strategy.** Each property is controlled by a different local mechanism. We construct all neighborhoods around the same point and intersect them only at the end.

**Proof.** At a real place, use the connected component of $x$ in the real manifold. At a good place, take an integral residue tube. In the ordinary case intersect that tube with the nonvanishing loci of the partial Hasse invariants. In the nonordinary case keep the entire fixed special point, so the residue tube retains its local--local group. In the semistable case use valuation shells in a boundary chart and avoid deeper strata. The two generic frame conditions are locally constant because their isomorphism schemes are finite étale over the characteristic-zero generic fiber. The component is already open and closed, and the complement of $Z(K)$ is open. Finitely many valuation or Kummer constraints give further open neighborhoods at points where they are locally constant. Their intersection contains $x$. $\square$

The theorem does not assert that an arbitrary determinant-compatible local representation has a seed. It starts after PEL realization has been exhibited. This boundary between representation theory and local geometry is essential.

## 13. The complete geometric package

### 13.1 Admissible two-prime moduli data

An **admissible two-prime moduli datum** over a totally real number field $F$ consists of:

1. a totally real coefficient field $M$ of degree $g$, an invertible ideal $I$, the ordered tensor polarization $\mathfrak c=\mathfrak c_I=\mathfrak d_M^{-1}I^{-2}$, the corrected level (5.3) for $N\geq3$, and the $F$-defined tensor component $Y_I^{\mathrm{ten}}$;
2. distinct odd rational primes $p\ne q$ and primes $\lambda\mid p$, $\lambda'\mid q$ of $M$, unramified and prime to the discriminant, polarization degree, and auxiliary level wherever good integral geometry is used;
3. rank-two local systems $V$ over $k_\lambda$ and $V'$ over $k_{\lambda'}$, together with specified Galois-equivariant isomorphisms
   $$
   \bigwedge^2V\simeq
   (\mathfrak d_M^{-1}\mathfrak c^{-1}\otimes k_\lambda)(1),
   \qquad
   \bigwedge^2V'\simeq
   (\mathfrak d_M^{-1}\mathfrak c^{-1}\otimes k_{\lambda'})(1); \tag{13.1}
   $$
4. monodromy-admissibility of $\lambda$ and $\lambda'$, so the congruence proof of Section 8.3 gives full product geometric monodromy
   $$
   \operatorname{SL}_2(k_\lambda)\times
   \operatorname{SL}_2(k_{\lambda'}) \tag{13.2}
   $$
   on the selected base component.

For a different application with externally prescribed PEL data, the analogous datum must instead name and descend its component and prove its auxiliary level locally solvable. The potential-modularity construction loses nothing by the tensor choice (5.5).

### 13.2 The smooth connected cover theorem

**Theorem 13.1 (two-prime geometric realization space).** From an admissible two-prime moduli datum without the local additions, the functor of tuples

$$
(A,\iota,\lambda_A,\eta_{\mathfrak n},
\alpha:V\xrightarrow{\sim}A[\lambda],
\alpha':V'\xrightarrow{\sim}A[\lambda']) \tag{13.3}
$$

with pairing-preserving frames is represented by a smooth quasi-projective fine $F$-scheme $X$ of pure dimension $g$. It carries a universal tuple and is geometrically connected.

**Proof strategy.** The determinant condition gives the correct Hodge type, the ordered polarization module fixes duality and component data, and neat level removes automorphisms. Paired frames form two independent special-linear torsors. Smoothness comes from lifting one Hodge line for each embedding, and connectedness comes from transitive product monodromy.

**Proof.** Theorem 6.1 gives a smooth quasi-projective scheme of relative dimension $g$ with universal quadruple $(A,\iota,\lambda_A,\eta_{\mathfrak n})$. The coefficient primes are invertible on the generic fiber, so each paired frame scheme is a finite étale torsor under the appropriate special linear group. Their fiber product is a torsor under the product in (13.2). The pairing identifications (13.1) make the descent cocycle determinant one in each factor, so twisting preserves the fixed-pairing cover and its universal object.

Infinitesimally, de Rham cohomology splits into $g$ symplectic planes and the Hodge filtration chooses one line in each. Every line lifts across a square-zero thickening, with a one-dimensional space of choices, while finite étale levels lift uniquely. Hence the twist is smooth of dimension $g$. Finally, geometric monodromy acts on one fiber as the full deck group. This action is transitive, so the finite étale cover is geometrically connected. A twist becomes the original cover after algebraic closure, and is therefore geometrically connected as well. $\square$

The proof separates four assertions often conflated: representability uses rigidification; smoothness uses Hodge deformation theory; nonemptiness is supplied by a seed or by geometric fibers; geometric connectedness uses monodromy. None implies all the others.

### 13.3 The local-open theorem

**Theorem 13.2 (complete local package).** Use the corrected tensor datum (5.5), and let $S$ be a finite set of places. At a good integral place away from the two level characteristics, assume the residue characteristic avoids $D_M$, $N$, $p$, and $q$. At a place above $p$ or $q$, assume the local field and the corresponding completion of $M$ are unramified, the polarization is prime to that residue characteristic, and the residue characteristic is odd. Impose the following exact representation-theoretic conditions:

1. at every real place, both prescribed systems are odd;
2. at a good place away from $p$ and $q$, both systems are unramified after any explicitly permitted preliminary inertia-killing extension;
3. at an ordinary or nonordinary coefficient place, the residue-characteristic system is finite flat, and either arbitrary finite splitting is permitted or its exact paired frame is known over the more restrictive allowed completion extension;
4. at a semistable place, any nontrivial residual Kummer classes that must survive over the chosen completion are scalar extensions of one Tate class $[q_0]$; if the frames may be split by arbitrary finite extension, no common nontrivial class is required. At an unramified coefficient prime, impose (11.8), or equivalently (11.9), when finite-flat Tate torsion is required before further ramification.

Then there are finite nonarchimedean extensions $F_v'/F_v$, respecting those permissions, and for every $v\in S$ a nonempty open

$$
\Omega_v\subset X(F_v') \tag{13.4}
$$

such that every point in $\Omega_v$ carries both prescribed paired torsion modules, lies on $Y_{\mathcal O_M}^{\mathrm{ten}}$, and has the requested real, good, ordinary, nonordinary finite-flat, or semistable behavior. The persistent conclusions of Section 12.1 survive further finite local extension. If a proper closed degeneracy locus is to be avoided, the opens may be chosen outside it after a finite residue extension.

**Proof.** Proposition 11.1 constructs the real tensor point with corrected auxiliary level and both frames directly from oddness. Away from the level characteristics, Section 9.2 makes both unramified frame systems trivial after one finite residue extension, constructs a point of the twisted special fiber, and lifts it smoothly; its residue tube is the good open.

At a coefficient characteristic, formula (11.3a) supplies ordinary and supersingular elliptic seeds after finite unramified extension. Tensoring puts both on the fixed component. If exact frames are not already available over a restricted permitted field, pass to the finite compositum splitting the two prescribed systems, the two seed torsion systems, and their pairing lines. Paired bases give both generic frames on the same seed. The prescribed finite-flat model base-changes and continues to witness finite flatness, while good ordinary or local--local reduction of the seed persists. The ordinary Hasse locus or the fixed nonordinary tube gives the open.

For a semistable condition, the $N$th-power map is invertible on the mod-$p$ and mod-$q$ Kummer quotients. Choose a simultaneous preimage class $[q_N]$ of the required compatible classes and multiply a representative by a sufficiently large $pq$th power to make its valuation positive without changing those classes; put $q_0=q_N^N$. If frames may instead be split, choose any positive-valuation $q_N$ and pass to their common splitting field. The full-dimensional algebraized chart of Section 11.4 places $E_{q_0}\otimes I$ on the corrected tensor component. Its valuation shell gives the semistable open and retains (11.9) when required.

All conjunctions are witnessed before neighborhoods are intersected, so Theorem 12.1 applies. A proper closed subset has empty interior in a smooth local polydisc; after a finite residue extension one chooses a point outside its first nonzero reduction and repeats the construction there. Section 12.1 proves every stated persistence assertion. $\square$

This theorem is the last existence theorem proved here. Its output is a variety and local open subsets. It does not produce a number-field point.

### 13.4 Examples and counterexamples

For $M=\mathbf Q$, the construction is a fixed-pairing twist of a fine modular curve. If $V$ has determinant $\bar\chi_p$, its quotient cocycle lies in $\operatorname{SL}_2(\mathbf F_p)$ and preserves one Weil-pairing component. If the pairing is forgotten, twisting the union of all full-level components can give a scheme connected over $F$ but geometrically disconnected.

For real quadratic $M$ with split degree-one primes $\lambda\mid p$ and $\lambda'\mid q$, the realization space is a surface. Under product monodromy its deck group is

$$
\operatorname{SL}_2(\mathbf F_p)\times
\operatorname{SL}_2(\mathbf F_q).
$$

A point gives one abelian surface carrying both modules. It is not a pair of points on two modular curves, and the surface need not be a product. At a $p$-adic place the $\lambda$-factor may be ordinary or local--local while the prime-to-$p$ $\lambda'$-factor remains a finite étale generic local system.

Three counterexamples summarize the hypotheses. A wrong determinant makes the paired frame functor empty. Separate surjectivity of monodromy to the two factors does not exclude a diagonal subgroup when the factors share a quotient. A finite-flat generic representation need not equal the torsion of a prescribed PEL seed. Each failure occurs before global specialization and must be repaired geometrically.

## 14. Disjointness and the exact handoff

### 14.1 The avoidance datum

Although this book does not construct a global point, it must state what a later field construction has to preserve. Let $L_V/F$ and $L_{V'}/F$ be the finite Galois extensions fixed by the kernels of the two representations. Let $D/F$ be a finite Galois extension containing both, together with every finite field used to define a component, detect an image, or carry descent data that must remain independent.

The geometric construction neither chooses $D$ nor proves the existence of a field disjoint from it. It exports $D$ as an avoidance input alongside the variety $X$ and the local opens $\Omega_v$. This ordering matters: all component and image fields must be entered before specialization, not discovered afterward.

### 14.2 What disjointness would preserve

**Lemma 14.1.** Let $r:G_F\to G$ have finite image, and let $L/F$ be the fixed field of its kernel. If a finite extension $F'/F$ satisfies $F'\cap L=F$, then

$$
r(G_{F'})=r(G_F). \tag{14.1}
$$

**Proof.** Since $L/F$ is Galois, the intersection condition gives

$$
\operatorname{Gal}(F'L/F')\simeq\operatorname{Gal}(L/F).
$$

The restriction map from $G_{F'}$ onto the group on the left is surjective. Identifying the group on the right with $r(G_F)$ proves that every element of the original image is attained after restriction. The reverse inclusion is immediate. $\square$

Consequently disjointness from $D$ would preserve the two residual images, hence absolute irreducibility and any projective-image property determined by those finite images. It would not by itself preserve a chosen local field. If a place $v$ splits completely in $F'$, every completion above it equals $F_v$ and the exact local representation and finite-flat model remain unchanged. More general completion extensions use the persistence ledger of Section 12.1.

### 14.3 Root fields and normal closures

A closed point has a residue field $F'$ that need not be Galois over $F$. The condition $F'\cap D=F$ concerns that root field. Its normal closure $\widetilde F'$ may intersect $D$ even when $F'$ does not. Therefore (14.1) over $F'$ cannot be carried automatically to $\widetilde F'$.

Likewise, total reality of $F'$ says that every embedding of $F'$ is real; it gives no prescribed Galois group for the normal closure. Any later demand for a Galois or solvable extension is a stronger arithmetic problem, not an unnoticed consequence of the present moduli construction.

### 14.4 The output boundary

The exact output of this book is

$$
\boxed{
X/F\text{ smooth, quasi-projective, geometrically connected, fine};
\quad
\Omega_v\subset X(F_v')\text{ nonempty and condition-correct};
\quad
D/F\text{ recorded for avoidance}.}
\tag{14.2}
$$

It does not output a finite totally real extension, a rational point on $X$, an auxiliary representation of automorphic origin, an abelian variety over a global extension, an automorphic representation, or a modularity-lifting conclusion. If a later arithmetic theorem supplies a closed point $x$ with residue field $F'$ satisfying the prescribed local-algebra and avoidance conditions, pulling back the universal family would give

$$
A[\lambda]\simeq V|_{G_{F'}},
\qquad
A[\lambda']\simeq V'|_{G_{F'}}. \tag{14.3}
$$

Equation (14.3) is a conditional interpretation of a future point, not an existence assertion made here. Even then, it identifies residual torsion only. It does not identify an arbitrary lift of $V$ with a Tate module and does not transfer automorphy between primes.

## 15. Failure audit

### 15.1 Empty twists and false components

The paired twist is empty if either determinant line in (13.1) is wrong. Equality of characters without a chosen line isomorphism does not specify a paired frame. If the cocycle has nontrivial determinant relative to the universal multiplier, it permutes pairing components and cannot twist a single one.

Arithmetic connectedness is not geometric connectedness. A Galois orbit of geometric components may descend to a connected $F$-scheme. The cure is full product monodromy or an explicitly descended geometric component. Separate surjections to each special-linear factor do not suffice until common quotient couplings have been excluded.

### 15.2 Generic frames and integral models

In characteristic zero, $A[\lambda]$ and $A[\lambda']$ are finite étale, including over $p$-adic and $q$-adic fields. Their integral closures over the valuation ring need not be étale, and a generic basis does not determine a finite flat model. Ordinary, local--local, and Tate-extension claims must therefore be stated for actual finite locally free group schemes.

Finite flatness of a representation is also not an integral PEL-realization theorem: it does not identify a named finite-flat model with the kernel on a chosen abelian scheme. For the catalog's generic frame, the corrected tensor seed and a permitted common splitting extension suffice, while the original model continues to witness finite flatness after base change. An exact integral comparison, an unramified-only frame policy, or an externally fixed polarization class requires the stronger data stated in Chapters 9 and 11.

### 15.3 Separate local solutions

One HBAV realizing $V$ and another realizing $V'$ do not give a point of the two-prime cover. An ordinary seed and a separate nonordinary seed do not prove a common neighborhood. Nonempty opens on different components do not intersect. Every conjunction of local requirements must first be witnessed by one point carrying the whole tuple.

Local solvability after an unramified extension is not solvability over the original field. A later completion datum must contain the extension actually used. Exact valuations rescale under ramification, Kummer classes may split, and nonsplit tori may become split. These changes are limits on persistence, not defects in openness.

### 15.4 Smoothness, nonemptiness, and automorphy

Smoothness says infinitesimal deformations lift. It does not produce a rational point. Positive dimension supplies local room around an existing point; it does not prove that the selected twist has a point over a given completion. Geometric connectedness controls components of the cover; it does not establish local nonemptiness.

Finally, none of these geometric properties implies automorphy. The moduli space relates two residual torsion factors on one future abelian variety. Constructing auxiliary arithmetic data, producing the global point, applying modularity lifting, and transporting automorphy are later tasks. Keeping this boundary explicit is part of the theorem's correctness.

## 16. Conclusion

A residual representation enters the construction as a twisted paired-frame torsor. Its determinant identifies the Weil-pairing line on which the torsor can live. The Hilbert determinant condition, ordered polarization module, and neat auxiliary level then turn the ambient classification problem into a fine smooth variety with a universal abelian scheme.

Distinct coefficient primes provide two rank-two torsion factors on the same abelian variety without consuming deformation dimension. Full product monodromy, rather than two unrelated factorwise surjections, makes the simultaneous cover geometrically connected. Twisting changes arithmetic descent but leaves that geometric connectedness intact.

The corrected cyclotomic-split level and tensor component put every local construction on the same fine space. Real seeds encode odd involutions without an orientation obstruction. Smooth integral seeds produce good tubes. Ordinary points are controlled by Hasse invariants and Serre--Tate coordinates; nonordinary finite-flat points by fixed local--local residue tubes. Tate curves sit inside an algebraized full-dimensional Mumford chart whose valuation shells supply semistable neighborhoods. Generic paired frames become simultaneous after exactly the permitted completion extensions, while integral group schemes record the finer finite-flat information that a characteristic-zero basis cannot see.

The final package is deliberately geometric: one smooth geometrically connected fine variety, its universal two-prime tuple, and component-correct nonempty local opens with precise persistence properties. Avoidance fields and completion requirements are exported as inputs to a later arithmetic construction. No global point, automorphy statement, or lifting conclusion has been smuggled across that boundary.
