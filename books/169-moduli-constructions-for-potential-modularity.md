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
11. [Constructing the auxiliary representation](#11-constructing-the-auxiliary-representation)
   - [Why the second prime must be known](#111-why-the-second-prime-must-be-known)
   - [Irreducibility and oddness](#112-irreducibility-and-oddness)
   - [Determinant engineering](#113-determinant-engineering)
   - [Controlling local behavior](#114-controlling-local-behavior)
   - [Auxiliary automorphy and its exact use](#115-auxiliary-automorphy-and-its-exact-use)
   - [A dihedral counterexample](#116-a-dihedral-counterexample)
12. [Disjointness and preservation of images](#12-disjointness-and-preservation-of-images)
   - [Why the output field must avoid fixed fields](#121-why-the-output-field-must-avoid-fixed-fields)
   - [What linear disjointness proves](#122-what-linear-disjointness-proves)
   - [Root fields are not Galois closures](#123-root-fields-are-not-galois-closures)
   - [Local splitting and global avoidance together](#124-local-splitting-and-global-avoidance-together)
13. [Applying the arithmetic existence theorem](#13-applying-the-arithmetic-existence-theorem)
   - [The verification ledger](#131-the-verification-ledger)
   - [Moving presentations](#132-moving-presentations)
   - [The global point](#133-the-global-point)
   - [Pulling back the universal family](#134-pulling-back-the-universal-family)
   - [What has not been concluded](#135-what-has-not-been-concluded)
14. [Three examples revisited](#14-three-examples-revisited)
   - [A twisted full-level modular curve](#141-a-twisted-full-level-modular-curve)
   - [A two-prime Hilbert modular surface](#142-a-two-prime-hilbert-modular-surface)
   - [Conditions at the two residual primes](#143-conditions-at-the-two-residual-primes)
15. [The moduli theorem for potential modularity](#15-the-moduli-theorem-for-potential-modularity)
   - [Admissible realization data](#151-admissible-realization-data)
   - [Main theorem](#152-main-theorem)
   - [The elliptic specialization](#153-the-elliptic-specialization)
   - [The exact handoff to potential modularity](#154-the-exact-handoff-to-potential-modularity)
16. [Conclusion](#16-conclusion)

## 1. The realization problem

### 1.1 From a representation to a moving abelian variety

Let $F$ be a totally real number field, let $p$ be an odd prime, let $k$ be a finite field of characteristic $p$, and let

$$
\bar\rho:G_F\longrightarrow \operatorname{GL}_2(k)
$$

be continuous and absolutely irreducible. Potential modularity begins with a reversal of the usual direction of thought. Torsion on an abelian variety gives a Galois representation; here the representation is given first, and one asks for an abelian variety whose torsion is that representation.

The desired construction must do much more than match two abstract vector spaces. It must preserve the alternating form forced by a polarization, behave correctly at places above $p$, meet specified reduction conditions at other places, and coexist with a second torsion representation whose automorphic origin is already understood. Finally, all these requirements must define open local conditions on one smooth geometrically connected variety, for only then can the existence theorem of Book 168 turn local models into a global point over a finite totally real extension.

This book constructs precisely that variety. It does not prove that the resulting abelian variety is modular. The passage from its two torsion representations to modularity lifting belongs to Book 170. Our task is geometric and arithmetic at once: design a moduli problem that remembers enough information to realize both representations, but remains large and connected enough to have points.

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

One convenient construction prescribes separable local factorization patterns at $p$ and $q$ and a real coefficient neighborhood in which all roots remain real. Weak approximation makes these local boxes simultaneous, and the Hilbert irreducibility method of Book 167 selects within them a polynomial irreducible over $\mathbf Q$. Its root field is a totally real field $M$ with the selected residue degrees. By keeping the local discriminants nonzero, one also makes $p$ and $q$ unramified. This argument explains the flexibility but does not canonically determine $M$; different coefficient fields produce different Hilbert modular varieties.

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
4. $\lambda$ is an $\mathcal O_M$-linear $\mathfrak c$-polarization: equivalently, an identification of $\mathfrak c$ with the module of symmetric $\mathcal O_M$-linear homomorphisms $A\to A^\vee$ carrying $\mathfrak c^+$ to polarizations, with the prescribed degree type.

The determinant identity is interpreted after base change to a field containing the images of the embeddings, and therefore descends as a polynomial identity. It says that each real embedding contributes one tangent direction. Without it, the action could occur with unequal multiplicities, giving the wrong dimension and local model.

Some authors place $\mathfrak c^{-1}$ rather than $\mathfrak c$ in the polarization module. Either convention is valid, but it changes the displayed pairing line. We fix the convention above once and use its induced alternating modules at every level.

### 5.3 Polarization pairings at coefficient primes

For a prime $\mathfrak l$ of $M$ away from the degree of the polarization, the polarization and the Weil pairing induce a perfect alternating $\mathcal O_M/\mathfrak l$-bilinear form on $A[\mathfrak l]$, with values in a fixed one-dimensional module $L_{\mathfrak l}(1)$ determined by $\mathfrak c$ and the trace dual of $\mathcal O_M$. After choosing a generator of $L_{\mathfrak l}$, this becomes

$$
e_{\mathfrak l}:A[\mathfrak l]\times A[\mathfrak l]
\longrightarrow \mu_{\ell}\otimes_{\mathbf F_\ell}k_{\mathfrak l}. \tag{5.2}
$$

The choice of generator is part of a fixed-pairing component. Changing it by $u\in k_{\mathfrak l}^\times$ changes the component coordinate, and a level automorphism of determinant $u$ has the same effect. This is why polarization type, pairing trivialization, and determinant character must be chosen together.

### 5.4 Neat auxiliary level

To obtain a scheme carrying a universal family, choose an ideal $\mathfrak n\subset\mathcal O_M$, prime to $pq\mathfrak c\mathfrak d_M$, and impose a sufficiently deep level structure at $\mathfrak n$. We require the corresponding arithmetic subgroup to be neat: the subgroup generated by eigenvalues of each element has no nontrivial torsion. A principal congruence level of sufficiently large depth is a familiar geometric way to ensure this, but its descent datum is part of the choice.

This last qualification is essential over a totally real field. A constant full basis of odd order on an abelian variety over $\mathbf R$ would force complex conjugation to act trivially on that torsion, and therefore can make the real locus empty. One may instead use a neat level orbit, a suitable one-sided level, or a twist of a principal frame whose real involution agrees with that of the comparison abelian varieties. What is required below is a neat auxiliary level problem defined over $F$, with the selected component and universal family, and with points on every local comparison object. Neatness alone does not prove this local solvability.

Neatness solves the automorphism problem. If an automorphism of $(A,\iota,\lambda)$ preserves the auxiliary level, it gives a torsion element in the relevant arithmetic group; neatness forces it to be the identity. The prime levels $\lambda$ and $\lambda'$ might also kill automorphisms, but relying on them is unsafe at small primes or after quotienting. The separate auxiliary level makes representability independent of such accidents.

### 5.5 The untwisted fine space

Let $Y=Y_{M,\mathfrak c}(\mathfrak n)$ denote the moduli scheme of tuples $(A,\iota,\lambda,\eta_{\mathfrak n})$ satisfying the preceding conditions, where the notation permits the chosen neat level orbit or twisted rigidification rather than silently meaning a constant full frame. The polarization and orientation component to be used is included in the datum from the outset; its descent to $F$ is a hypothesis, not an automatic consequence of its existence over $\mathbf C$.

The phrase “one component” is deliberate. The full Hilbert modular scheme may have components indexed by a narrow class quotient and level determinant data. Arithmetic Galois action can permute geometric components, so connectedness over $F$ does not imply geometric connectedness. We require a geometrically connected polarization-orientation component defined over $F$ before twisting. If a preliminary choice produces a component only over an extension, that extension must be totally real, the representations must first be restricted to it without losing image, and it must then be incorporated into the initial datum. One cannot silently rename the base field after the disjointness problem has been posed.

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
- the auxiliary level is neat;
- a geometrically connected polarization-orientation component has been fixed.

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

A union of conjugate geometric components can be connected over $F$ without being geometrically connected. Book 168 requires geometric connectedness. Selecting a complex component without checking its field of definition does not produce an $F$-variety at all.

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

For small primes or special coefficient fields, surjectivity must be checked rather than asserted. If its image is a proper subgroup $H$, the frame cover has several geometric components indexed by $H$-orbits. One may still select a component, determine its field of definition, and twist only by a cocycle landing in its stabilizer. Book 168 must then be applied to that geometrically connected component over its field of definition. If this requires replacing the original base field, that replacement is made before the final realization datum is declared, and the residual images and all local conditions are rechecked there. In the theorem below, the selected twisted component is required to be defined over the displayed base field $F$.

Surjectivity onto each factor separately is not always enough for surjectivity onto the product. A subgroup of $G_1\times G_2$ can project onto both factors while being the graph of an isomorphism between quotients. Here the distinct residue characteristics usually rule out such a coupling: the nonabelian simple quotients of the two special linear groups have different characteristics and, outside small exceptional coincidences, are nonisomorphic. Any remaining common abelian quotient is eliminated by working in the derived, fixed-determinant group and checking the small primes directly. This product check is the precise reason for the last bullet of Section 8.3.

The analytic picture gives the same conclusion. Reduction modulo $\lambda\lambda'$ maps the relevant congruence group to the product of the two finite groups by the Chinese remainder theorem, provided the global derived group has strong approximation and the determinant condition has already been separated off. The kernel defines a connected quotient of $\mathfrak H^g$. Twisting changes its descent action but not this geometric analytic space.

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

This is an input protocol, not a universal local existence theorem. The representation $\bar\rho$ must satisfy local hypotheses strong enough to supply the chosen $B_v$ or its finite-flat model. In potential-modularity applications those hypotheses come from the original representation or from an explicitly constructed local elliptic curve.

### 9.2 Good places

Suppose $v\nmid pq\mathfrak n\mathfrak c\mathfrak d_M$ and both target modules are unramified at $v$. A local comparison point may be obtained from a Hilbert--Blumenthal abelian variety with good reduction and the desired Frobenius actions on the two torsion factors. When a global seed variety is available, its base change gives such a point immediately. Another method starts with a smooth special-fiber point carrying precisely the prescribed finite étale levels and lifts it through the smooth integral PEL model. Unramifiedness by itself does not prove that such a special-fiber point exists: arbitrary pairs of Frobenius matrices need not come from one polarized abelian variety. Existence of the seed or special-fiber point remains part of the local datum.

Only finitely many places need to be placed in the local set for Book 168. Outside that set, no local point is prescribed. The eventual global abelian variety, being defined over a number field, automatically has good reduction away from finitely many places. Thus there is no need to solve infinitely many local moduli problems.

A standard source of a comparison point is the tensor construction. If $E/F_v$ is an elliptic curve and $P$ is a projective $\mathbf Z$-module equipped with an $\mathcal O_M$-action of rank $g$, the sheaf $E\otimes P$ is, in the split cases used here, an abelian variety isogenous to $E^g$ with real multiplication. A positive trace form on $P$ supplies a compatible polarization. Its $\mathfrak l$-torsion is obtained from $E[\ell]$ by the corresponding residue factor. Thus a local elliptic curve whose $p$-torsion realizes the desired local target can seed a local HBAV.

This simple construction does not realize two unrelated modules automatically. It is most useful when one residual condition is prescribed and the other can be arranged by choosing the remaining prime-to-residue-characteristic frame or by moving inside the local Hilbert modular space. When both local modules are rigidly prescribed, the comparison HBAV is part of the local input and must be constructed by a tailored isogeny, a lift of a suitable special-fiber object, or another explicit PEL method.

### 9.3 Archimedean places

At a real place $v$, the complex points of a Hilbert modular component are modeled by $\mathfrak H^g$ modulo an arithmetic group. The chosen positivity component has real points precisely when its descent datum admits a real Hodge structure with the prescribed torsion involutions and auxiliary rigidification.

For an odd two-dimensional module, complex conjugation has eigenvalues $1$ and $-1$ at each odd residual prime. This is the torsion shadow of a polarized weight-one real Hodge structure. If both target representations are odd, their determinant identifications agree with the positive polarization component, and the auxiliary level has compatible real descent, a real HBAV point carrying all the levels may exist. In our construction its existence is part of the archimedean local datum. The involution calculation explains compatibility of the two residual frames, but it does not manufacture the auxiliary rigidification or select a narrow-class component. Once such a point is chosen, its real locus contains an open manifold neighborhood.

Oddness alone does not choose the correct narrow-class component. The polarization orientation at every embedding must also match. We include this compatibility in the archimedean local datum. Choosing a point in each real component and a sufficiently small neighborhood is what later forces every embedding of the output field to be real; the mere fact that $F$ is totally real is not enough.

To make the involution calculation explicit, let $c$ be complex conjugation. Since $c^2=1$ and the residual characteristic is odd, $V$ decomposes into its $+1$ and $-1$ eigenspaces. Oddness makes each eigenspace one-dimensional. A real polarized complex torus has exactly this action on each two-dimensional coefficient-prime factor. Hence one can match frames after choosing their pairing orientation. If the determinant at $c$ were $+1$, the eigenvalues would be both $1$ or both $-1$; such a frame would lie on no real point of the desired Hilbert modular component.

### 9.4 Places above the target characteristic

Let $v\mid p$. The finite group scheme $B_v[\lambda]$ over $F_v$ is étale because $F_v$ has characteristic zero, but an integral model over $\mathcal O_{F_v}$ need not be étale. Suppose the target local module is the generic fiber of a finite locally free commutative group scheme $\mathcal G_v$ of rank $|k_\lambda|^2$, with $\mathcal O_M/\lambda$-action and a perfect alternating pairing into the appropriate roots-of-unity group scheme. We require a local HBAV $\mathcal B_v/\mathcal O_{F_v}$, or a specified semistable model when good reduction is not intended, and an isomorphism

$$
\mathcal G_v\xrightarrow{\sim}\mathcal B_v[\lambda] \tag{9.2}
$$

of finite locally free paired group schemes.

Passing to generic fibers gives the first isomorphism in (9.1), but (9.2) is stronger. Two nonisomorphic finite-flat models can have isomorphic generic Galois modules. Conversely, an abstract generic isomorphism need not extend over $\mathcal O_{F_v}$. We never infer extension from generic data alone.

Cartier duality checks the pairing integrally. The polarization identifies the dual of $\mathcal B_v[\lambda]$ with the appropriate twist by the polarization line. Therefore an isomorphism in (9.2) must carry the Cartier-dual pairing on $\mathcal G_v$ to the Weil pairing, not simply identify their generic points. This forces the determinant character on inertia and prevents a generic frame with the wrong multiplier from masquerading as integral level.

The auxiliary $\lambda'$-torsion has order prime to the residue characteristic at $v$. Over an abelian scheme with good reduction it is finite étale and unramified, so it may be compared with $V'$ by a prime-to-$p$ frame when the latter is unramified with the same Frobenius. For a semistable comparison object it can be ramified, and its actual generic Galois module must instead be checked directly. Prime-to-residue-characteristic makes the level étale; it does not by itself make it unramified without good reduction.

### 9.5 Places above the auxiliary characteristic

For $v\mid q$, reverse the roles. Choose a paired finite locally free model $\mathcal G'_v$ of $V'|_{G_{F_v}}$ and an isomorphism

$$
\mathcal G'_v\xrightarrow{\sim}\mathcal B_v[\lambda']. \tag{9.3}
$$

The target $\lambda$-torsion is prime to the residue characteristic and may be matched as an étale generic level. If the comparison abelian variety has good reduction, this module is unramified; under semistable reduction its actual inertia action must be matched rather than discarded. This separation is one benefit of $p\ne q$, but it removes integral connectedness issues only for the prime-to-residue-characteristic level.

A common error is to say that finite flatness of the representation uniquely determines (9.2) or (9.3). It does not in general. Our local datum names the model and the comparison. Books 46--48 justify the language of finite locally free group schemes, Cartier duality, pairings, and generic fibers; nothing here invokes a general classification or an unproved deformation theorem.

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

Book 168 accepts nonempty open subsets $\Omega_v\subset X(F_v)$, not isolated local points. Once a comparison point $x_v$ has been constructed, we must show that the arithmetic properties needed later persist in a neighborhood.

Because $X$ is smooth, $X(F_v)$ is an analytic manifold near $x_v$. The universal abelian scheme and its level structures vary over this neighborhood. After shrinking, finite étale torsion local systems are locally constant. Integral properties are handled by extending the universal object over a suitable integral neighborhood or, equivalently, by choosing a residue tube inside an integral model.

### 10.2 Good reduction

Good reduction at $v$ is encoded by requiring the moduli point to extend to the good integral locus of the PEL model over $\mathcal O_{F_v}$. If $x_v$ extends to a smooth integral point, the inverse image of its residue class is an open subset of $X(F_v)$. Every point in a sufficiently small such tube corresponds to an abelian variety with good reduction and the same prime-to-$v$ level behavior.

This statement uses the moduli interpretation, not a claim that good reduction is Zariski open on the generic fiber in isolation. The relevant topology is the $v$-adic topology and the open is a tube around an integral point.

### 10.3 Semistable reduction

Semistable reduction may be imposed by working near a chosen boundary chart in a toroidal compactification whose universal semiabelian scheme has the desired toric rank. Fixing the valuations of the degeneration parameters in an open range, and requiring the remaining parameters to be units, defines an analytic open. Alternatively, when an explicit local family is available, semistability and the desired split toric character can be read from its semiabelian model and are stable in a sufficiently small neighborhood. The required chart or explicit family is part of the local verification; the existence of a semistable comparison point alone does not prove openness of every refined toric condition.

One must not identify the entire boundary divisor with one reduction type. Intersections of boundary strata can change toric rank, and cancellation in local parameters can alter splitting. We choose a smooth point of a named stratum and shrink away from all deeper strata.

### 10.4 Constancy of finite-flat comparison

At $v\mid p$, the condition that the generic $\lambda$-torsion equal $V|_{G_{F_v}}$ is already built into $X$. The stronger condition that its integral model equal the chosen $\mathcal G_v$ is imposed only on a neighborhood where the universal abelian variety extends and where the finite locally free kernel can be compared with $\mathcal G_v$.

Such constancy is not automatic on an arbitrary large disk. In the applications covered by our theorem, it is part of the local-model hypothesis: there is an integral neighborhood $\mathcal U_v$ of the chosen point over which the universal $\lambda$-kernel is identified with the pullback of the selected model, or at least every point has the specified finite-flat type. The same clause is used at $q$. This precise hypothesis replaces any appeal to a general finite-flat deformation result.

Notice the two distinct sorts of openness. The generic representation is fixed everywhere on the twisted moduli variety by the universal level isomorphism. The integral finite-flat type is fixed only on the selected local neighborhood. Likewise, good reduction is not encoded by the residual representation alone; it is encoded by extension of the universal abelian scheme over the integral tube. Keeping these layers separate avoids deriving integral conclusions from generic torsion.

### 10.5 The finite local set

Let $S$ contain:

- every archimedean place;
- all places above $p$ and $q$;
- places where $M$, $\mathfrak c$, or the auxiliary level causes bad integral geometry;
- places where prescribed good or semistable reduction is required;
- any place used to control ramification or splitting of the output extension.

For each $v\in S$, choose a nonempty open $\Omega_v\subset X(F_v)$ around the constructed comparison point. Several requirements at the same place are combined by intersection only after checking that the chosen point satisfies all of them. An empty intersection is not repaired by the global theorem.

## 11. Constructing the auxiliary representation

### 11.1 Why the second prime must be known

The moduli variety can accommodate any compatible second module, but the later modularity argument needs one whose automorphic origin is already established. A dihedral representation is ideal: it is induced from a character of a quadratic CM extension, so its irreducibility, determinant, ramification, and automorphy can all be controlled from rank-one data.

Choose a totally imaginary quadratic extension $K/F$ with nontrivial automorphism $c$, an algebraic Hecke character $\psi$ of $K$, and an odd coefficient prime $q\ne p$. Let

$$
\chi:G_K\longrightarrow \overline{\mathbf Q}_q^\times
$$

be the $q$-adic avatar in an integral arithmetic normalization, and let

$$
\theta:G_K\longrightarrow \overline{\mathbf F}_q^\times
$$

be its reduction with respect to the evident stable rank-one lattice. Set

$$
\bar\rho_{\mathrm{aux}}=\operatorname{Ind}_{G_K}^{G_F}\theta. \tag{11.1}
$$

Book 95 supplies the corresponding automorphic induction of $\psi$ and the induced stable lattice whose reduction is (11.1).

### 11.2 Irreducibility and oddness

The induced representation (11.1) is absolutely irreducible precisely when

$$
\theta\ne\theta^c. \tag{11.2}
$$

after reduction, not merely before reduction. We choose a prime and character for which the quotient $\theta/\theta^c$ remains nontrivial modulo $q$. A complex conjugation $s$ lies outside $G_K$ and satisfies $s^2=1$. In the two-coset induction basis it therefore acts by the exchange matrix, with eigenvalues $1$ and $-1$. Hence its determinant is $-1$: the representation is odd.

This calculation also explains why a totally real quadratic inducing field is unsuitable. Complex conjugation would lie in the subgroup at some real places and need not exchange the two induced lines, so oddness would not be forced.

### 11.3 Determinant engineering

For quadratic induction the determinant is the product of the character contribution with the quadratic permutation character $\epsilon_{K/F}$. If

$$
\operatorname{Ver}:G_F^{\mathrm{ab}}\longrightarrow G_K^{\mathrm{ab}}
$$

is transfer, then the exact formula is

$$
\det\operatorname{Ind}_{G_K}^{G_F}\theta
=\epsilon_{K/F}\cdot(\theta\circ\operatorname{Ver}). \tag{11.3}
$$

Indeed, on $h\in G_K$ the determinant is $\theta(h)\theta^c(h)$, while on a coset representative $s\notin G_K$ it is $-\theta(s^2)$. Thus determinant compatibility at $\lambda'$ is an actual global condition on $\theta$, not a consequence of oddness. There is no free choice of an extension of $\theta\theta^c$ across the other coset: transfer and the permutation sign determine it.

We choose the Hecke character underlying $\theta$ so that the mod-$q$ reduction of (11.3) equals the multiplier $L_{\lambda'}(1)$ of the PEL datum. Class field theory translates this into a transfer and central-character condition. Compatible finite-order local prescriptions can be globalized by the ray-class construction of Book 95 after the global-unit obstruction has been cancelled, possibly using auxiliary conductor primes. Behavior at places above $q$, especially existence of the required finite locally free model, is an additional condition and is not supplied by that character construction alone. If a correcting character is needed, it must be chosen before induction and checked in (11.3). An arbitrary twist after the fact changes the determinant by a square and may destroy local behavior.

### 11.4 Controlling local behavior

Choose $K/F$ and $\theta$ so that:

- $K$ has prescribed split, inert, or ramified behavior at the finite set $S$;
- $\theta/\theta^c$ remains nontrivial modulo $q$;
- the determinant is the required cyclotomic-polarization character;
- at places above $q$, the residual induced module has the finite-flat model used in Section 9.5;
- away from a controlled conductor set it is unramified;
- its coefficient field admits a prime inducing the selected residue field $k_{\lambda'}$.

These requirements cannot be arbitrary independently. For example, an unramified character at both places above a split prime forces an unramified induced representation there. Likewise, determinant values on $F_v^\times$ must agree with the prescribed central character. Subject to these compatibility constraints, the local-to-global construction of Hecke characters gives the needed freedom.

One practical order of choices is important. First choose a CM extension and characteristic-zero Hecke character with the required determinant pattern and with the desired behavior at the places fixed independently of $q$. Next choose a coefficient prime $q$ outside the finite exceptional set where the character and its conjugate become equal, while also imposing the required residue field and splitting conditions on the coefficient field $M$. Then inspect the resulting places above $q$ and verify, by an explicit local calculation, the finite-flat model and comparison required in Section 9.5. If that calculation fails, the auxiliary character or prime must be changed; it cannot be repaired by asserting finite flatness afterward. Finally fix $q$, $M$, $\lambda'$, and all $q$-adic local data before constructing the moduli space. This order avoids both a circular choice of $q$ and an unsupported residual local condition.

At a split place $v=ww^c$ of $K/F$, induction restricts as $\theta_w\oplus\theta_{w^c}$. At an inert place it remains locally induced, and is irreducible when the two conjugate characters differ in the relevant decomposition group. These formulas allow ordinary reducible behavior at selected residual places while retaining global irreducibility: local reducibility at one decomposition group does not imply reducibility over $G_F$.

### 11.5 Auxiliary automorphy and its exact use

Automorphic induction of the Hecke character gives a cuspidal automorphic representation because (11.2) rules out norm descent. Its associated residual representation is (11.1), after choosing a stable lattice and reducing at the chosen prime. Therefore $\bar\rho_{\mathrm{aux}}$ has known automorphic origin before the moduli construction begins.

No lifting theorem is applied here. Nor do we conclude that the abelian variety constructed later is automorphic. The auxiliary module is one input that Book 170 will combine with modularity lifting at $q$ and then at $p$.

### 11.6 A dihedral counterexample

Suppose the inducing Hecke character descends through the norm, say it is $\mu\circ N_{K/F}$. Then its Galois avatar and its residual character are conjugation-invariant, so $\theta=\theta^c$. The induction splits as two characters differing by $\epsilon_{K/F}$, and the automorphic induction is not cuspidal. It may still be odd and may even have the desired determinant, but it does not supply an absolutely irreducible auxiliary residual representation. Determinant, oddness, irreducibility, and automorphy must therefore be checked separately.

## 12. Disjointness and preservation of images

### 12.1 Why the output field must avoid fixed fields

Let $L_{\bar\rho}$ be the fixed field of $\ker\bar\rho$, and define $L_{\mathrm{aux}}$ similarly. Restricting a representation from $G_F$ to $G_{F'}$ replaces its image by the subgroup corresponding to

$$
F'\cap L_{\bar\rho}.
$$

If $F'$ is linearly disjoint from $L_{\bar\rho}$ over $F$, the image is unchanged. If not, absolute irreducibility can fail. For example, a dihedral representation induced from $K/F$ becomes a sum of two characters after restriction to $G_K$. Thus allowing $F'$ to contain $K$ destroys the very auxiliary irreducibility that made induction useful.

The fields $L_{\bar\rho}$ and $L_{\mathrm{aux}}$ are already Galois over $F$, because they are fixed fields of normal subgroups. Choose a finite Galois avoidance field

$$
D/F
$$

containing $L_{\bar\rho}$ and $L_{\mathrm{aux}}$, the fields needed to detect any other residual images, and all finite descent or component fields whose intersection must be avoided. Applying Book 168 with linear disjointness from $D$ gives, equivalently because $D/F$ is Galois, the condition

$$
F'\cap D=F \tag{12.1}
$$

preserves both residual images and prevents the output point from descending through an unwanted constant-field intersection.

### 12.2 What linear disjointness proves

**Lemma 12.1.** Let $r:G_F\to G$ have finite image and fixed field $L/F$. If $F'/F$ is linearly disjoint from $L/F$, then

$$
r(G_{F'})=r(G_F).
$$

In particular, every property depending only on the finite image, such as absolute irreducibility or projective image, is preserved. If sensitive local places also split completely, their local representations and inertia images are preserved separately.

**Proof strategy.** Translate restriction into restriction of automorphisms of the compositum $F'L$ and use the intersection formula for linearly disjoint extensions.

**Proof.** The extension $L/F$ is finite Galois, and linear disjointness gives

$$
\operatorname{Gal}(F'L/F')\simeq\operatorname{Gal}(L/F).
$$

Restriction $G_{F'}\to\operatorname{Gal}(F'L/F')$ is surjective. Composing the displayed isomorphism with the faithful realization of $\operatorname{Gal}(L/F)$ as $r(G_F)$ shows that every element of the original image is attained by an element of $G_{F'}$. The reverse inclusion is automatic. $\square$

Local behavior needs a second observation. If a place $v$ of $F$ splits completely in $F'$, then for each $w\mid v$ there is an identification $F'_w=F_v$. Hence restriction at $w$ changes neither the local representation nor its chosen finite-flat model. Global disjointness preserves images; complete local splitting preserves the exact local field.

### 12.3 Root fields are not Galois closures

Book 168 produces $F'$ as the residue field of a closed point. It is generally not Galois over $F$. The assertion $F'\cap D=F$ concerns this root field. Its Galois closure $\widetilde F'$ can intersect $D$ nontrivially even when $F'$ does not.

This distinction prevents two invalid deductions. First, total reality of $F'$ says that every embedding $F'\hookrightarrow\mathbf C$ is real; it does not say the Galois closure has any prescribed group. Second, residual image preservation over $F'$ does not automatically imply preservation after passing to $\widetilde F'$. If Book 170 later replaces $F'$ by a Galois closure, it must redo the disjointness and image analysis, or choose a stronger construction designed for that closure.

### 12.4 Local splitting and global avoidance together

There is no conflict between requiring every $v\in S$ to split completely in $F'$ and requiring (12.1), provided the local and global data are compatible. The totally real version of Book 168 incorporates both conditions through a moving presentation and a Hilbert condition. We therefore put all sensitive places into $S$ and all image fields into $D$ before invoking the theorem. Adding either after the point is chosen is too late.

## 13. Applying the arithmetic existence theorem

### 13.1 The verification ledger

We now have the precise inputs required by Book 168:

| Requirement | Verification in this construction |
|---|---|
| quasi-projective variety | the fine PEL realization in Theorem 6.1 |
| smoothness | the Hodge-filtration calculation of Proposition 7.1 |
| geometric connectedness | Theorem 8.1, or an explicitly selected geometric component |
| nonempty local opens | comparison objects and neighborhoods in Sections 9--10 |
| real local opens | actual comparison points with odd residual involutions, compatible polarization orientation, and compatible auxiliary level in Sections 5.4 and 9.3 |
| finite avoidance field | the field $D$ of Section 12.1 |
| universal abelian scheme | neatness and fine representability in Theorem 6.1 |

This ledger is not ceremonial. Omitting any row changes the conclusion: a coarse point may not give an abelian variety; an arithmetically connected variety may fail the theorem's geometric hypothesis; one local point without an open neighborhood is insufficient for approximation; and a totally real base does not force a totally real residue field.

### 13.2 Moving presentations

The proof in Book 168 replaces local points by reduced configurations of one common degree, moves them through étale coordinates, and uses irreducibility to force the global finite algebra to be a field. For our split local-open application, the simultaneous moving-family lemma of Book 168 applies because $X$ is smooth, geometrically connected, and positive-dimensional.

Indeed, each $\Omega_v$ is a nonempty open in the analytic manifold $X(F_v)$. Around any point there is an étale map to affine $g$-space. Because $g\geq1$, one can choose arbitrarily many distinct nearby points in the same open and avoid the diagonals. This produces the local reduced split cycles, and at real places they can all be kept in the chosen real open. Local coordinates alone do not globalize those cycles. The moving-family lemma supplies one sufficiently large common degree and one global presentation interpolating all the local configurations; the split formulation is precisely the case in which that lemma makes the compatibility automatic.

### 13.3 The global point

Apply the totally real, disjoint form of Book 168 to $X/F$, the set $S$, the opens $\Omega_v$, and the avoidance field $D$. It gives a closed point $x\in X$ with residue field

$$
F'=\kappa(x)
$$

such that:

1. $F'/F$ is finite and totally real;
2. $F'$ is linearly disjoint from $D$ over $F$;
3. every $v\in S$ splits completely in $F'$;
4. for every $v\in S$ and every $F$-embedding $\sigma:F'\hookrightarrow F_v$, the conjugate point $x^\sigma$ belongs to $\Omega_v$.

The fourth clause is stronger than choosing one good place above $v$. Since $F'_w=F_v$ for every $w\mid v$, it guarantees the desired local condition at every place of $F'$ above $v$.

### 13.4 Pulling back the universal family

Pull the universal tuple on $X$ back along $x:\operatorname{Spec}F'\to X$. We obtain

$$
(A,\iota,\lambda_A,\eta_{\mathfrak n},\alpha,\alpha')/F'. \tag{13.1}
$$

By the moduli interpretation, not merely by geometric isomorphism,

$$
\alpha:V|_{G_{F'}}\xrightarrow{\sim}A[\lambda],
\qquad
\alpha':V'|_{G_{F'}}\xrightarrow{\sim}A[\lambda'] \tag{13.2}
$$

preserve the polarization pairings. Consequently

$$
\det A[\lambda]=\det V|_{G_{F'}},
\qquad
\det A[\lambda']=\det V'|_{G_{F'}}.
$$

At each $w\mid v$ with $v\in S$, membership in $\Omega_v$ gives the chosen reduction property. At $p$- and $q$-adic places it gives the named finite locally free model; at selected good places it gives good reduction; at selected semistable places it gives the chosen toric type. Linear disjointness and Lemma 12.1 preserve both residual images.

### 13.5 What has not been concluded

We have constructed an abelian variety with two prescribed torsion factors. We have not shown that an arbitrary lift of $\bar\rho$ occurs in the Tate module of $A$, nor that $A$ is automorphic, nor that automorphy transfers from $\lambda'$ to $\lambda$. Those are representation-theoretic conclusions requiring modularity lifting. The geometric output (13.1)--(13.2) is exactly the bridge on which Book 170 will operate.

## 14. Three examples revisited

### 14.1 A twisted full-level modular curve

Let $F=\mathbf Q$, $p=7$, and let $V$ be an odd absolutely irreducible module with determinant $\bar\chi_7$. Fix $\delta:\bigwedge^2V\simeq\mu_7$. Over the splitting field of $V$, select the component of $Y(7)$ on which the Weil pairing of the universal ordered basis equals the value prescribed by $\delta$. The quotient between the Galois action on $V$ and the universal cyclotomic action has determinant one, so it defines a cocycle in $\operatorname{SL}_2(\mathbf F_7)$.

The twist $Y_V$ is a smooth geometrically connected affine curve over $\mathbf Q$ with a universal elliptic curve $\mathcal E$. A closed point $y$ with residue field $L$ gives

$$
\mathcal E_y[7]\simeq V|_{G_L}.
$$

If one instead twists the union of all pairing components and forgets $\delta$, the result can be connected over $\mathbf Q$ while splitting geometrically into six components. That larger twist does not satisfy the geometric hypothesis needed for the arithmetic existence theorem without further component selection.

### 14.2 A two-prime Hilbert modular surface

Let $M$ be real quadratic, and choose split primes $p,q$ with degree-one factors $\lambda\mid p$ and $\lambda'\mid q$. Fix a narrow polarization class $\mathfrak c$, a compatible orientation, and a neat auxiliary level $\mathfrak n$ whose descent form has the required local points. Let $V$ and $V'$ be paired modules over $\mathbf F_p$ and $\mathbf F_q$ with cyclotomic determinants.

The resulting variety $X(V,V')$ is a surface. Over a splitting field it is a simultaneous fixed-pairing frame cover of a Hilbert modular surface, with deck group

$$
\operatorname{SL}_2(\mathbf F_p)\times\operatorname{SL}_2(\mathbf F_q)
$$

under the monodromy hypotheses. A point gives one abelian surface $A$ with both $A[\lambda]\simeq V$ and $A[\lambda']\simeq V'$. It is not a product of the two modular curves of Section 4.1, and $A$ need not split into elliptic curves.

The two dimensions can be used locally in different ways. Near a $p$-adic ordinary point, one direction may vary a Serre--Tate parameter while the other maintains a prescribed residue condition; near a bad auxiliary place, an open may select a semistable stratum. These are local analytic freedoms, not independent global coordinates, but they illustrate why a higher-dimensional moduli problem is robust.

### 14.3 Conditions at the two residual primes

Suppose at every $v\mid p$ the target $V$ has a chosen ordinary finite locally free model and $V'$ is unramified, while at every $w\mid q$ the auxiliary $V'$ has a chosen finite-flat model and $V$ is unramified. Choose local HBAVs realizing these pairs. Let $\Omega_v$ and $\Omega_w$ be integral residue tubes on which the corresponding kernels retain those models.

After applying Book 168, $p$- and $q$-adic places split completely in $F'$. Therefore, for every $v'\mid v\mid p$,

$$
F'_{v'}=F_v,
$$

and the finite locally free model of $A[\lambda]$ is the chosen $\mathcal G_v$. Likewise every $w'\mid w\mid q$ carries the chosen model of $A[\lambda']$. This “every place above” statement is what permits later local lifting hypotheses to be checked uniformly.

If the theorem had supplied only one completion over each residual prime, another conjugate place could have had the wrong reduction type. The split formulation is therefore not an aesthetic strengthening; it closes a genuine logical gap.

## 15. The moduli theorem for potential modularity

### 15.1 Admissible realization data

We package the construction in a form intended for direct use. An **admissible two-prime realization datum** over a totally real field $F$ consists of:

1. odd absolutely irreducible representations
   $$
   \bar\rho:G_F\to\operatorname{GL}_2(k_\lambda),
   \qquad
   \bar\rho_{\mathrm{aux}}:G_F\to\operatorname{GL}_2(k_{\lambda'}),
   $$
   of distinct odd residual characteristics $p$ and $q$;
2. a totally real coefficient field $M$, primes $\lambda\mid p$, $\lambda'\mid q$, a polarization ideal $\mathfrak c$, a determinant condition, an orientation component, and a neat auxiliary level $\mathfrak n$ with its $F$-descent form, with all indicated coprimality assumptions;
3. pairing identifications (6.1), so both determinants equal the appropriate PEL multiplier characters;
4. full product geometric monodromy at $\lambda$ and $\lambda'$, or a named twisted geometrically connected component defined over $F$, together with its stabilizer and a check that the descent cocycle lands in it;
5. a finite set $S$ containing all archimedean, level, residual-characteristic, ramified, and prescribed-reduction places;
6. for each $v\in S$, a point of the same selected component, represented by a local HBAV comparison object realizing both generic torsion modules, the auxiliary rigidifying level, and all desired reduction properties;
7. at $v\mid p$ and $v\mid q$, explicit paired finite locally free models and comparison isomorphisms as in (9.2) and (9.3), together with integral neighborhoods on which their type persists, and at every prescribed reduction place a verified nonempty analytic neighborhood on which the named good or semistable condition persists;
8. an auxiliary representation obtained from cuspidal dihedral automorphic induction, with residual irreducibility, oddness, determinant, and local conditions checked after reduction;
9. a finite Galois avoidance field $D$ containing the residual fixed fields and every finite descent, component, or image-detecting field whose intersection must be excluded.

This definition is intentionally demanding. Its purpose is to expose every hypothesis consumed by the proof. In an application, most entries are constructed from a smaller set of choices, but none may simply be omitted.

### 15.2 Main theorem

**Theorem 15.1 (two-prime moduli realization).** Given an admissible two-prime realization datum over $F$, there exist:

- a smooth geometrically connected quasi-projective $F$-variety
  $$
  X=X(\bar\rho,\bar\rho_{\mathrm{aux}})
  $$
  of dimension $[M:\mathbf Q]$, carrying a universal fine PEL tuple;
- nonempty opens $\Omega_v\subset X(F_v)$ for all $v\in S$;
- a finite totally real extension $F'/F$, linearly disjoint from $D$;
- and a Hilbert--Blumenthal abelian variety $(A,\iota,\lambda_A)/F'$ of the chosen polarization type,

such that:

$$
A[\lambda]\simeq\bar\rho|_{G_{F'}},
\qquad
A[\lambda']\simeq\bar\rho_{\mathrm{aux}}|_{G_{F'}} \tag{15.1}
$$

as paired Galois modules; every $v\in S$ splits completely in $F'$; the prescribed good, semistable, and finite-flat local conditions hold at every place above $S$; and both residual images are unchanged after restriction to $G_{F'}$.

**Proof strategy.** Construct the fine PEL component and twist its simultaneous frame cover. Prove smoothness by Hodge-filtration deformation theory and geometric connectedness by product monodromy. Build local points from the named local abelian varieties, enlarge them to analytic opens, and apply the totally real disjoint form of Book 168. Pull back the universal family and use disjointness to preserve images.

**Proof.** The data in items 2--4 define the functor (6.2). Theorem 6.1 represents it by a quasi-projective fine scheme of pure dimension $g=[M:\mathbf Q]$, and Proposition 7.1 proves smoothness. The monodromy clause and Theorem 8.1 prove geometric connectedness; in the component-selection alternative, $X$ means the selected twisted component, which is defined over $F$ by item 4.

For every $v\in S$, item 6 gives a point $x_v\in X(F_v)$. Sections 9.4--9.6 ensure that at residual and ramified places this is a point of the actual generic moduli problem together with the required integral model, not merely an abstract torsion representation. Item 7 and Section 10 give a nonempty open neighborhood $\Omega_v$ on which the desired properties persist. At real places, item 6 includes an actual point with compatible orientation and auxiliary level; oddness verifies the involution type on the two residual factors but is not used as a substitute for that point. The split moving-family lemma applies as explained in Section 13.2.

Apply the totally real theorem of Book 168 with the avoidance field $D$. It produces $F'$ and $x\in X(F')$ satisfying all-embedding local membership, complete splitting at $S$, and linear disjointness from $D$. Pulling back the universal tuple gives $A$ and the isomorphisms (15.1). The local conclusions follow because every completion over $S$ equals the original $F_v$ and the conjugate point lies in $\Omega_v$. Lemma 12.1 gives equality of both residual images. $\square$

### 15.3 The elliptic specialization

When a one-dimensional moduli space already has all required local points, one may take the elliptic construction instead. A fixed-pairing twist of a fine full-level modular curve at $p$—or simultaneous full $pq$-level with a separate neat rigidification—produces an elliptic curve over a finite totally real extension realizing the prescribed modules. The rigidification must use a descent form compatible with the real and finite local comparison points; a constant full auxiliary frame cannot be inserted without checking this. The same determinant, component, local-model, and disjointness hypotheses remain necessary.

This specialization is economical but not formally stronger. The Hilbert--Blumenthal construction is preferred when two-prime local conditions are easier to realize with real multiplication or when a higher-dimensional smooth space supplies the required local flexibility.

### 15.4 The exact handoff to potential modularity

The theorem supplies four objects needed next:

$$
\boxed{
F'/F\text{ totally real and disjoint},\quad
A/F',\quad
A[\lambda]\simeq\bar\rho,
\quad
A[\lambda']\simeq\bar\rho_{\mathrm{aux}}.}
\tag{15.2}
$$

It also supplies the local reduction conditions under which later lifting theorems may be invoked. The auxiliary representation has automorphic origin by induction. What remains is to transport modularity through the $\lambda'$-adic representation of $A$, use the compatible structure supplied by real multiplication, and return at $\lambda$ to the target representation. Those are the tasks of Book 170.

## 16. Conclusion

The realization problem is solved not by choosing equations for an abelian variety but by arranging a descent problem with the correct geometry. A residual representation specifies a twisted frame torsor. Its determinant specifies the Weil-pairing component on which that torsor can live. A polarization and the Hilbert--Blumenthal determinant condition turn the ambient classification problem into a smooth $g$-dimensional variety, while neat auxiliary level removes automorphisms and supplies a universal family.

Two primes can then be imposed on the same abelian variety without consuming deformation dimension. Product monodromy proves that the fixed-pairing cover is geometrically connected; merely knowing arithmetic connectedness would not suffice. At places dividing the two residual characteristics, generic Galois modules are replaced by explicit comparisons with finite locally free torsion models. Good and semistable reduction are recorded by nonempty analytic opens around chosen local abelian varieties. At real places, actual comparison points combine odd residual involutions, polarization orientation, and the descent form of the auxiliary level; the split real opens then keep every conjugate of the eventual point real.

With smoothness, geometric connectedness, local opens, moving presentations, and avoidance all verified, the theorem of Book 168 produces a closed point whose residue field is finite, totally real, and disjoint from the residual fixed fields. The universal family at that point carries both prescribed torsion identifications and all selected local reduction behavior. The root field is kept distinct from its Galois closure, and residual images survive because disjointness was imposed before specialization.

The geometric bridge is therefore complete. On one side lies the target residual representation; on the other lies a dihedral residual representation of known automorphic origin. Between them stands one polarized abelian variety with real multiplication, defined over a well-controlled totally real field. The next book may now cross that bridge by modularity lifting; no part of that crossing has been hidden inside the moduli construction.
