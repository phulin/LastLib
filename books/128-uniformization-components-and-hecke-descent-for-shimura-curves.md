# Uniformization, Components, and Hecke Descent for Shimura Curves

## Contents

1. [The four structures that must agree](#1-the-four-structures-that-must-agree)
   - [The problem](#11-the-problem)
   - [Standing quaternionic PEL datum](#12-standing-quaternionic-pel-datum)
   - [Conventions and the boundary of the book](#13-conventions-and-the-boundary-of-the-book)
2. [Complex abelian varieties as polarized lattices](#2-complex-abelian-varieties-as-polarized-lattices)
   - [From an abelian variety to a Hodge lattice](#21-from-an-abelian-variety-to-a-hodge-lattice)
   - [The Riemann construction in the opposite direction](#22-the-riemann-construction-in-the-opposite-direction)
   - [Endomorphisms, determinant law, and polarization](#23-endomorphisms-determinant-law-and-polarization)
   - [Markings and adelic lattices](#24-markings-and-adelic-lattices)
3. [The complex uniformization theorem](#3-the-complex-uniformization-theorem)
   - [The period map from the PEL moduli problem](#31-the-period-map-from-the-pel-moduli-problem)
   - [Reconstruction from a double coset](#32-reconstruction-from-a-double-coset)
   - [Injectivity and the role of rational quasi-isogenies](#33-injectivity-and-the-role-of-rational-quasi-isogenies)
   - [Uniformization on the selected component union](#34-uniformization-on-the-selected-component-union)
4. [Stabilizers, smooth curves, and compactness](#4-stabilizers-smooth-curves-and-compactness)
   - [The exact stabilizer](#41-the-exact-stabilizer)
   - [Neatness and fine level](#42-neatness-and-fine-level)
   - [The one-dimensional analytic structure](#43-the-one-dimensional-analytic-structure)
   - [Division algebras and absence of cusps](#44-division-algebras-and-absence-of-cusps)
5. [Connected components](#5-connected-components)
   - [The exact double-coset label](#51-the-exact-double-coset-label)
   - [Abelianization and strong approximation](#52-abelianization-and-strong-approximation)
   - [Reduced norms for the basic quaternionic group](#53-reduced-norms-for-the-basic-quaternionic-group)
   - [Central modifications and label discipline](#54-central-modifications-and-label-discipline)
   - [How level change acts on labels](#55-how-level-change-acts-on-labels)
6. [Canonical descent of components](#6-canonical-descent-of-components)
   - [Ambient reciprocity](#61-ambient-reciprocity)
   - [Galois action on the label set](#62-galois-action-on-the-label-set)
   - [Fields of definition of individual components](#63-fields-of-definition-of-individual-components)
   - [Descent of a stable component union](#64-descent-of-a-stable-component-union)
7. [Fine, stacky, and coarse levels](#7-fine-stacky-and-coarse-levels)
   - [Cofinal fine covers](#71-cofinal-fine-covers)
   - [Nominal and effective level groups](#72-nominal-and-effective-level-groups)
   - [Quotient stacks and coarse curves](#73-quotient-stacks-and-coarse-curves)
   - [What descends to which quotient](#74-what-descends-to-which-quotient)
8. [Commensurable lattices and universal isogenies](#8-commensurable-lattices-and-universal-isogenies)
   - [The lattice attached to an adelic point](#81-the-lattice-attached-to-an-adelic-point)
   - [Integral representatives and the analytic isogeny](#82-integral-representatives-and-the-analytic-isogeny)
   - [The intermediate level](#83-the-intermediate-level)
   - [Kernel, degree, and polarization multiplier](#84-kernel-degree-and-polarization-multiplier)
9. [Algebraic construction and descent of the universal isogeny](#9-algebraic-construction-and-descent-of-the-universal-isogeny)
   - [Construction from a finite subgroup](#91-construction-from-a-finite-subgroup)
   - [Identification with the translated universal family](#92-identification-with-the-translated-universal-family)
   - [Descent from a rigidifying cover](#93-descent-from-a-rigidifying-cover)
   - [Independence and composition](#94-independence-and-composition)
10. [Hecke correspondences at finite level](#10-hecke-correspondences-at-finite-level)
    - [The double-coset span](#101-the-double-coset-span)
    - [Finiteness, etaleness, and degrees](#102-finiteness-etaleness-and-degrees)
    - [Action on connected components](#103-action-on-connected-components)
    - [Transpose](#104-transpose)
11. [Composition and the Hecke algebra](#11-composition-and-the-hecke-algebra)
    - [Fiber products of spans](#111-fiber-products-of-spans)
    - [Multiplicity and double-coset convolution](#112-multiplicity-and-double-coset-convolution)
    - [The universal-isogeny cocycle](#113-the-universal-isogeny-cocycle)
    - [Correspondences on Jacobians](#114-correspondences-on-jacobians)
12. [Descent of Hecke maps and correspondences](#12-descent-of-hecke-maps-and-correspondences)
    - [Right translation commutes with canonical reciprocity](#121-right-translation-commutes-with-canonical-reciprocity)
    - [Descent at fine level](#122-descent-at-fine-level)
    - [Descent at coarse level](#123-descent-at-coarse-level)
    - [Descent of the universal isogeny](#124-descent-of-the-universal-isogeny)
13. [The complete uniformization and Hecke package](#13-the-complete-uniformization-and-hecke-package)
    - [Main theorem](#131-main-theorem)
    - [Hypothesis ledger](#132-hypothesis-ledger)
    - [Normalization checks and failure tests](#133-normalization-checks-and-failure-tests)
    - [Conclusion](#134-conclusion)

## 1. The four structures that must agree

A quaternionic Shimura curve has four descriptions. It is an arithmetic quotient of a half-plane, a moduli space of polarized abelian varieties with endomorphisms, a finite union of connected curves labelled by an adelic class set, and a canonical algebraic curve carrying Hecke correspondences. Each description is useful only if the identifications preserve all of the others. This book proves that compatibility.

### 1.1 The problem

Let $(G,X)$ be a quaternionic Shimura datum of dimension one. The analytic expression

$$
G(\mathbf Q)\backslash\bigl(X\times G(\mathbf A_f)/K\bigr)       \tag{1.1}
$$

is easy to write and surprisingly easy to misuse. It does not itself explain which abelian variety corresponds to $[h,g]$, why two representatives give the same object, which connected component contains the point, or why right translation by an adelic element is defined over the reflex field. At non-neat level it is an orbifold quotient, so it also does not carry a universal abelian variety as an ordinary family.

The preceding books supplied the ingredients separately. The quaternionic datum, its reflex field, and canonical model are known. A genuine PEL realization gives a fine moduli scheme after sufficient level and a universal abelian family. General correspondence theory explains how a finite span of curves acts on Jacobians. The present task is to join these pieces without changing a variance convention in the middle.

There are four main theorems to prove. First, the complex points of the selected PEL curve are exactly the appropriate components of (1.1). Second, connected components are computed by an exact abelianized class quotient, with the rational positivity and norm conditions retained. Third, a fine cover presents the moduli stack through the nominal level group, while its effective image presents the coarse curve. Fourth, the lattice modification attached to $a\in G(\mathbf A_f)$ produces a universal isogeny on the fine Hecke space and a Hecke correspondence on every coarse canonical curve, all defined over the reflex field.

### 1.2 Standing quaternionic PEL datum

Let $F$ be a totally real field and $B/F$ a quaternion algebra split at exactly one real embedding $\tau_0$. Thus the associated symmetric domain has one complex dimension. Write

$$
G^{\mathrm b}=\operatorname{Res}_{F/\mathbf Q}B^\times.          \tag{1.2}
$$

The group used for the PEL constructions will be denoted $G$. It is either $G^{\mathrm b}$, if the basic group itself carries the stated direct PEL realization, or a specified connected PEL-exact central modification with the same adjoint datum. In the latter case a central morphism from the PEL tower to the basic tower is an additional finite comparison; equality of their adjoint data does not identify their component sets or their universal families. No reduced-norm component formula will be asserted for $G$ unless $G=G^{\mathrm b}$.

Fix a quaternionic PEL realization

$$
\mathscr D=(D,*,V,\psi,h_0)
$$

in the precise sense established for quaternionic PEL functors. Thus $D$ is a semisimple $\mathbf Q$-algebra with positive involution, $V$ is a faithful left $D$-module, $\psi$ is a nondegenerate alternating form satisfying

$$
\psi(bx,y)=\psi(x,b^*y),
$$

and the connected $D$-linear similitude group of $(V,\psi)$ is exactly $G$. The homomorphism $h_0:\mathbb S\to G_{\mathbf R}$ gives $V$ types $(-1,0)$ and $(0,-1)$ and is positive. Its conjugacy class is $X$, and $E$ denotes the reflex field. In the one-split-place basic case, $E$ is the embedded copy $\tau_0(F)$.

Choose a $*$-stable order $\mathcal O\subset D$, an $\mathcal O$-stable lattice $\Lambda\subset V$, a polarization type, and a compact open $K\subset G(\mathbf A_f)$ compatible with the completed lattice $\widehat\Lambda$. We work in characteristic zero. Whenever a universal family is mentioned on a scheme, the level is assumed fine: it is neat and detects the rational center, or it contains a rigid principal level of order at least three. Arbitrary $K$ will be treated by a quotient stack and its coarse curve.

This convention fixes an important interface. Every adelic element used to modify the universal lattice lies in the actual PEL group $G(\mathbf A_f)$. If a finite central comparison $G\to G^{\mathrm b}$ is present, the resulting family or isogeny on the $G$-cover descends to the basic curve only when the central inertia acts trivially on the entire PEL diagram. The underlying finite correspondence can descend even when the universal object does not.

The fixed integral PEL type can select only a union of the components of (1.1). We denote its adelic label set by $\mathcal C_K$ and assume it is stable under the canonical Galois action when descent to $E$ is asserted. This qualification is necessary. Changing the adelic lattice can change the polarization module or its elementary divisors even though it does not change the rational Shimura datum.

On such a union, the polarization module includes an equivariant normalization of the actual polarization. If the form assigned to $L_g$ is $c(g)\psi$, then compatibility with the left rational action requires

$$
c(qg)\nu(q)=c(g)\qquad(q\in G(\mathbf Q)).
$$

This is part of selecting the integral PEL type. Without it the double quotient would classify rational polarization classes, whereas the fine functor with arrows preserving $\lambda$ classifies actual polarizations. We will use this compatibility when reconstructing objects from $(h,g)$.

### 1.3 Conventions and the boundary of the book

The rational group acts diagonally on the left:

$$
q\cdot(h,gK)=(qh,qgK).
$$

Right translation by $a\in G(\mathbf A_f)$ is therefore

$$
[h,gK]\longmapsto[h,ga(a^{-1}Ka)].                                \tag{1.3}
$$

Arithmetic Artin reciprocity is used. If $x=[h,g]$ is special and $s$ is an idele of its reflex field, then

$$
x^{\operatorname{Art}(s)}=[h,r_h(s_f)g].                           \tag{1.4}
$$

The reciprocity multiplier is on the left; the Hecke multiplier is on the right. Their commutation is the basic descent identity of the book.

For the ambient action on connected components, the reflex field $E$ can have real places. An Artin class is then represented by an idele whose real components are all positive; weak approximation supplies such a representative. Two positive representatives of the same Artin class differ, on their finite parts, by a totally positive principal element and a connected archimedean element. This is the normalization that makes the action well defined on the narrow quotient. No positivity choice is needed for the CM reflex field of a special point, whose archimedean idele group is connected.

For a finite correspondence

$$
C\xleftarrow{p_1}H\xrightarrow{p_2}D,
$$

its action on Jacobians is $p_{2*}p_1^*$. Its transpose reverses the two projections and is the polarized adjoint. This is the convention of the established theory of integral correspondences.

All results here concern generic characteristic-zero curves. We do not assert extension across a bad integral fiber, smoothness of a ramified local model, or an Eichler--Shimura relation in characteristic $p$. Those require good or semistable integral models. We do prove the generic correspondence and its canonical descent completely, which is the input needed before those integral questions can even be stated.

## 2. Complex abelian varieties as polarized lattices

Complex uniformization is not merely the statement that an abelian variety is a complex torus. The lattice must remember its rational endomorphisms, its alternating form, its Hodge determinant law, and its finite adelic level. This chapter isolates that classification so the double quotient proof becomes transparent.

### 2.1 From an abelian variety to a Hodge lattice

Let $A/\mathbf C$ be an abelian variety of dimension $g$. Put

$$
L=H_1(A,\mathbf Z),\qquad H=L\otimes_{\mathbf Z}\mathbf Q.
$$

The complex structure of $A(\mathbf C)$ gives a real-linear operator $J$ on $H_{\mathbf R}$ with $J^2=-1$. Define

$$
h_A:\mathbb S(\mathbf R)=\mathbf C^\times\longrightarrow
\operatorname{GL}(H_{\mathbf R}),
\qquad h_A(a+bi)=a+bJ.                                              \tag{2.1}
$$

Algebraicity of $h_A$ follows after complexification: the $i$ and $-i$ eigenspaces of $J$ are the two characters of $\mathbb S_{\mathbf C}$. With the homology convention they have Hodge types $(-1,0)$ and $(0,-1)$.

A polarization $\lambda:A\to A^\vee$ supplies an integral alternating Riemann form $\psi_\lambda$ on $L$. It satisfies

$$
\psi_\lambda(Jx,Jy)=\psi_\lambda(x,y),\qquad
\psi_\lambda(x,Jx)>0\quad(x\ne0),                                \tag{2.2}
$$

after the fixed global sign. Equivalently, $\psi_\lambda(x,h_A(i)y)$ is symmetric positive definite. If $\iota:\mathcal O\to\operatorname{End}(A)$ satisfies the Rosati condition, then

$$
\psi_\lambda(\iota(b)x,y)=\psi_\lambda(x,\iota(b^*)y).           \tag{2.3}
$$

These identities show that rational homology is a polarized $D$-Hodge module of the prescribed kind.

The integral and rational statements should be kept separate. The form $\psi_\lambda$ is integral because $\lambda$ is an actual morphism, but a rational quasi-isogeny can carry it only to a rational multiple of another integral form. This is why the rational group is a similitude group and why an adelic component must remember a polarization module. A symplectic group with multiplier fixed to one would omit legitimate isogenies; a general linear group would forget positivity and the Rosati involution.

The familiar elliptic-curve case is a useful model. If $A=\mathbf C/(\mathbf Z+\tau\mathbf Z)$ with $\operatorname{Im}\tau>0$, take the ordered basis $(1,\tau)$ of homology. The complex structure is represented by a real matrix conjugate to

$$
\begin{pmatrix}0&-1\\1&0\end{pmatrix},
$$

and the standard area form is alternating and positive after composition with that matrix. Replacing the lattice by a finite-index sublattice leaves the rational Hodge structure unchanged and produces an isogenous elliptic curve. Quaternionic PEL uniformization is the same mechanism with a noncommutative endomorphism algebra and many passive Hodge factors.

**Proposition 2.1.** The construction $(A,\iota,\lambda)\mapsto(H,h_A,\psi_\lambda)$ is faithful up to isogeny: a $D$-linear isomorphism of rational Hodge structures preserving the alternating forms up to a positive scalar is induced by a unique $D$-linear polarized quasi-isogeny.

**Proof strategy.** A Hodge map preserves the complex structures and therefore gives a holomorphic homomorphism of complex tori after an integral multiple clears denominators. Holomorphic homomorphisms of complex abelian varieties are algebraic.

**Proof.** Let $u:H_1(A,\mathbf Q)\to H_1(A',\mathbf Q)$ commute with the two Hodge homomorphisms. Choose $n>0$ with $nu(L)\subset L'$. The induced real map descends to a holomorphic homomorphism

$$
A(\mathbf C)=H_{\mathbf R}/L\longrightarrow H'_{\mathbf R}/L'=A'(\mathbf C).
$$

The graph is a closed complex subgroup of the product of two polarized complex tori, hence is algebraic; equivalently, full faithfulness for proper complex varieties algebraizes the holomorphic map. Dividing the resulting homomorphism by $n$ gives a quasi-isogeny inducing $u$. Equation (2.3) gives $D$-linearity, and the similitude identity for the forms gives the polarization relation. Uniqueness follows because a homomorphism of abelian varieties is determined by its map on $H_1$. $\square$

### 2.2 The Riemann construction in the opposite direction

Suppose now that $L$ is a lattice in a rational vector space $H$, that $J^2=-1$ on $H_{\mathbf R}$, and that $\psi:H\times H\to\mathbf Q$ is alternating. Assume that some positive rational multiple of $\psi$ is integral on $L$ and that (2.2) holds. Then

$$
A(H,L,J)=H_{\mathbf R}/L                                             \tag{2.4}
$$

is a compact complex torus. The integral multiple of $\psi$ is a positive Riemann form, so the Riemann bilinear relations make (2.4) an abelian variety. Dividing its associated polarization in the rational isogeny category recovers the original rational form.

**Proposition 2.2 (polarized lattice classification).** The constructions of Sections 2.1 and 2.2 are mutually inverse equivalences between:

- complex abelian varieties up to isogeny, with $D$-action and a rational polarization class; and
- rational $D$-modules $H$ with a weight-$-1$ Hodge structure and a positive alternating form satisfying the adjoint identity, together with a commensurability class of lattices.

With an actual lattice and an integral polarization type fixed, the equivalence is on genuine abelian varieties and genuine isomorphisms.

**Proof.** Starting from $A$, the exponential sequence identifies $A(\mathbf C)$ with $H_1(A,\mathbf R)/H_1(A,\mathbf Z)$ and recovers its complex structure, so (2.4) returns $A$. Starting from a lattice, the first homology of (2.4) is canonically $L$, its complex structure is $J$, and its Riemann form is the given integral multiple of $\psi$. Morphisms agree by Proposition 2.1; integral maps carrying one lattice isomorphically to the other give isomorphisms rather than merely quasi-isogenies. $\square$

The distinction between an actual polarization and a rational polarization class is important. The rational Shimura datum naturally controls the latter. An integral PEL component fixes enough lattice information to recover the former.

Positivity cannot be dropped from Proposition 2.2. A complex torus $H_{\mathbf R}/L$ exists for every operator $J^2=-1$, but it need not be algebraic. Algebraicity is equivalent to the existence of a positive integral Riemann form. Even an integral alternating form satisfying $\psi(Jx,Jy)=\psi(x,y)$ is not enough if the associated symmetric form has mixed sign. Thus the PEL positivity condition is precisely the effectivity condition turning a Hodge lattice into an abelian variety.

The proof also explains why commensurability is the correct equivalence relation. If $L'\subset L$ has finite index, then $H_{\mathbf R}/L'\to H_{\mathbf R}/L$ is an isogeny with kernel $L/L'$. Conversely, every isogeny of complex abelian varieties induces an inclusion of homology lattices after orienting its direction. Rational Hodge maps and commensurable lattices therefore contain exactly the information of the isogeny category.

### 2.3 Endomorphisms, determinant law, and polarization

Let $h:\mathbb S\to G_{\mathbf R}$. Because $G$ centralizes the left $D$-action, $h$ commutes with $D$ and hence $D$ acts holomorphically on $A(H,L,h(i))$. The similitude condition implies positivity of the prescribed form throughout the conjugacy class $X$.

The determinant law is also automatic on $X$. If $W_h=H_{\mathbf C}/F^0H_{\mathbf C}$ is the tangent quotient, then for every $b\in D$,

$$
\det(T-b\mid W_h)=P_{\mathscr D,b}(T),                             \tag{2.5}
$$

where the right side is the polynomial fixed by the PEL datum. Conjugating $h$ inside $G(\mathbf R)$ gives an isomorphic $D$-module $W_h$, so the polynomial is constant on $X$.

Conversely, consider a polarized $D$-Hodge module on $V$ satisfying (2.5), the fixed positivity condition, and the locally constant orientation data. By the PEL-realizability hypothesis, the common stabilizer of the algebra action and alternating form is the chosen group $G$, not a larger group. The determinant and orientation conditions put its Hodge homomorphism in the chosen conjugacy class $X$. This last implication is exactly where genuine PEL realizability is used. If extra Hodge tensors were needed to cut out $G$, endomorphisms and a polarization would not suffice.

### 2.4 Markings and adelic lattices

A rational marking is a $D$-linear symplectic similitude

$$
\alpha:V\xrightarrow{\sim}H_1(A,\mathbf Q).                       \tag{2.6}
$$

It transports $h_A$ to a point $h=\alpha^{-1}h_A\alpha\in X$. On finite adeles it compares the completed integral homology with $V(\mathbf A_f)$. A $K$-level structure is the $K$-orbit of such a comparison; relative to $\widehat\Lambda$ it is represented by some $g\in G(\mathbf A_f)$.

Changing $\alpha$ to $\alpha q^{-1}$ with $q\in G(\mathbf Q)$ changes the pair to

$$
(h,g)\longmapsto(qh,qg).                                           \tag{2.7}
$$

Changing the representative of the level orbit changes $g$ to $gk$ for $k\in K$. Thus a marked PEL object naturally determines a point of (1.1).

For later use, attach to $g$ the rational lattice

$$
L_g=V(\mathbf Q)\cap g\widehat\Lambda
\quad\text{inside }V(\mathbf A_f),                                \tag{2.8}
$$

where $V(\mathbf Q)$ is diagonally embedded. Every full lattice in $V(\mathbf Q)$ is recovered from its profinite completion, so

$$
\widehat{L_g}=g\widehat\Lambda
$$

with the evident identification. Formula (2.8) is unchanged by right multiplication by an element of $K$ and satisfies $L_{qg}=qL_g$ for $q\in G(\mathbf Q)$.

Here is the local-to-global lattice argument behind this assertion. Choose a reference basis identifying $V(\mathbf Q)$ with $\mathbf Q^n$. Any compact open lattice in $V(\mathbf A_f)$ equals $\mathbf Z_p^n$ for all but finitely many $p$. Its intersection with $\mathbf Q^n$ is therefore a finitely generated free subgroup spanning $\mathbf Q^n$, and localizing it at $p$ recovers the prescribed $p$-adic lattice. If two global lattices have the same completion at every $p$, their quotient inside a common over-lattice is a finite group with zero $p$-primary part for every $p$, hence is zero. This small lemma is what lets an adelic equality turn a quasi-isogeny into an isomorphism in Section 3.3.

## 3. The complex uniformization theorem

We now prove that the period construction is neither many-to-one nor missing components. The main care lies in separating the rational Shimura quotient from the integral PEL types that select a finite union of its components.

### 3.1 The period map from the PEL moduli problem

Let $Q_K^{\mathcal C}$ be the fine characteristic-zero PEL scheme on the chosen open-and-closed union of integral types. A complex point is a tuple $(A,\iota,\lambda,\eta_K)$. Choose a rational marking (2.6) compatible with the rational polarization class. Sections 2.1--2.4 give a pair $(h,g)$.

**Lemma 3.1.** The class $[h,g]$ is independent of every choice and depends only on the isomorphism class of the PEL object.

**Proof.** A second rational marking differs from the first by a unique $q\in G(\mathbf Q)$, producing the left relation (2.7). A second representative of the level orbit differs by $K$ on the right. An isomorphism of PEL objects induces the same rational Hodge marking after composition and therefore the same double coset. $\square$

We obtain the period map

$$
\operatorname{per}:Q_K^{\mathcal C}(\mathbf C)\longrightarrow
G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/K).                \tag{3.1}
$$

The locally constant integral invariants of the source show that its image lies in a union of connected components, denoted $\operatorname{Sh}_K^{\mathcal C}(\mathbf C)$.

Those invariants can be read without choosing complex coordinates. They include the genus of the $\mathcal O$-lattice, the finite symplectic module determined by the polarization kernel, and the multiplier or orientation class. In a connected analytic family they cannot jump: the relevant finite etale group schemes and lattice local systems are locally constant. Consequently the phrase “selected component union” is not an ad hoc deletion of points; it is the open-and-closed locus on which the integral PEL problem has one fixed type.

### 3.2 Reconstruction from a double coset

Take $[h,g]$ in the selected union. On $V_{\mathbf R}$ use the complex structure $J_h=h(i)$. Let $L_g$ be (2.8). Positivity of the PEL realization gives a positive rational Riemann form. By definition of the selected union $\mathcal C$, it has the required integral representative and polarization type on $L_g$. Set

$$
A_{h,g}=V_{\mathbf R}/L_g.                                         \tag{3.2}
$$

Proposition 2.2 makes this an abelian variety. The left $\mathcal O$-action preserves $L_g$ by the compatibility built into the level genus and therefore acts on $A_{h,g}$. Equation (2.5) gives the determinant condition, and the Riemann form gives the required polarization. The identification of $\widehat{L_g}$ with the adelic lattice represented by $g$ gives the $K$-level orbit.

If $(h,g)$ is replaced by $(h,gk)$, then $L_{gk}=L_g$ and only the representative of the same level orbit changes. If it is replaced by $(qh,qg)$, multiplication by $q$ identifies $L_g$ with $L_{qg}$, intertwines the complex structures, and preserves all rational PEL tensors. On the selected integral type it is an isomorphism of the reconstructed objects. Thus reconstruction depends only on the double coset.

### 3.3 Injectivity and the role of rational quasi-isogenies

Suppose two PEL objects have the same double coset. Choose markings so that their pairs are related by $(h',g')=(qh,qgk)$. The rational map induced by $q$ is a $D$-linear polarized quasi-isogeny by Proposition 2.1. The equality of adelic lattices

$$
g'\widehat\Lambda=qgk\widehat\Lambda=qg\widehat\Lambda
$$

shows that it carries completed integral homology isomorphically onto completed integral homology. A rational linear map carrying every $p$-adic lattice isomorphically carries the global lattice isomorphically: its cokernel is a finite abelian group whose completion at every prime is zero. Hence the quasi-isogeny is an isomorphism. It respects the level orbit and, because the polarization type and similitude component were fixed, the actual polarization. The period map is injective.

This argument explains why rational quasi-isogenies appear in the left action but do not identify too many fine moduli points. The finite adelic coordinate restores the integral lattice. Omitting $g$ would classify only rational Hodge structures up to isogeny.

### 3.4 Uniformization on the selected component union

**Theorem 3.2 (complex PEL uniformization).** Under the standing PEL-realizability and fine-level hypotheses, the period map is a biholomorphic isomorphism

$$
(Q_K^{\mathcal C})^{\mathrm{an}}
\xrightarrow{\sim}
G(\mathbf Q)\backslash
\bigl(X\times G(\mathbf A_f)/K\bigr)^{\mathcal C}.                \tag{3.3}
$$

It carries the universal abelian scheme to the family of polarized complex tori $A_{h,g}$ and is compatible with every inclusion of fine levels.

**Proof strategy.** The preceding sections prove the bijection on points. Holomorphicity is checked on one marked chart, where the period map is the usual holomorphic variation of a Hodge filtration. The inverse is the Riemann family attached to the tautological variation.

**Proof.** Choose a connected component $X^+\subset X$ and an adelic representative $g$. On that chart the stabilizer

$$
\Gamma_g=G(\mathbf Q)\cap gKg^{-1}
$$

acts properly discontinuously. The family

$$
(V_{\mathbf R}\times X^+)/L_g
$$

with complex structure varying through $h\in X^+$ is holomorphic; positivity makes every fiber algebraic. The PEL tensors and level are locally constant or holomorphic, so the fine moduli property gives a holomorphic map $\Gamma_g\backslash X^+\to(Q_K^{\mathcal C})^{\mathrm{an}}$. The period map is its inverse on points by Sections 3.1--3.3. Both maps are holomorphic on every chart, hence are inverse biholomorphisms. Level compatibility follows because forgetting level does not change $h$, $L_g$, or the underlying abelian variety. $\square$

The theorem does not claim that a single fixed polarization type covers every component of the rational Shimura variety. It says exactly which union it covers and gives a criterion, namely the integral invariants of $L_g$, for membership in that union.

In the split benchmark $F=\mathbf Q$ and $B=M_2(\mathbf Q)$, after passing through the usual Morita equivalence, (3.3) reduces to the classical description of elliptic curves with level:

$$
\Gamma\backslash\mathfrak H.
$$

The point $\tau$ gives $\mathbf C/(\mathbf Z+\tau\mathbf Z)$, and a finite adelic matrix records a commensurable lattice with its level marking. In the quaternion division case the same upper half-plane occurs, but there are no cusps and the abelian variety carrying the PEL structure usually has dimension larger than one. The dimension of the moduli curve is governed by the single active adjoint factor, not by the dimension of its universal abelian variety.

## 4. Stabilizers, smooth curves, and compactness

Uniformization identifies points, but the local geometry depends on stabilizers. This chapter distinguishes the three statements often compressed into the phrase “take sufficiently small level”: finiteness of inertia, its complete disappearance, and compactness of the quotient.

### 4.1 The exact stabilizer

The stabilizer of a representative $(h,gK)$ under the left rational action is

$$
I_{h,g}=G(\mathbf Q)\cap Z_{G(\mathbf R)}(h)\cap gKg^{-1}.          \tag{4.1}
$$

Its adjoint image is finite. Indeed, $Z_{G^{\mathrm{ad}}(\mathbf R)}(h)$ is compact, while the intersection of $G(\mathbf Q)$ with a compact-open finite adelic condition is discrete in the real factor. A discrete subgroup of a compact group is finite. The kernel of the adjoint map lies in the rational center and can still contain torsion acting on the PEL object.

**Proposition 4.1.** For the faithful PEL realization fixed in Chapter 1, the automorphism group of the PEL object corresponding to $[h,g]$ is canonically $I_{h,g}$. If one forgets the PEL object and looks only at the action on the analytic domain, the subgroup of rational central elements acting trivially on the domain becomes an ineffective kernel; it must not be divided out when computing stack inertia.

**Proof.** An automorphism induces a $D$-linear automorphism of rational homology commuting with $h$, preserving the polarization, and preserving the $K$-level orbit. These are exactly the three conditions in (4.1); on the selected integral component, the polarization normalization forces the actual, rather than merely similitude, compatibility. Conversely such a rational Hodge automorphism preserves the integral lattice because of the level condition, so Proposition 2.1 algebraizes it to an automorphism. Faithfulness of $V$ makes an element acting identically on homology equal to the identity in $G$. A nontrivial rational central element may act trivially on $X$ while acting nontrivially on $V$ and on the abelian variety. It is then genuine inertia, even though it is invisible on the coarse analytic orbit space. $\square$

### 4.2 Neatness and fine level

If $K$ is neat in a faithful representation that detects the center, $I_{h,g}$ is trivial. Its adjoint image is finite, so all its eigenvalues are roots of unity; neatness forces them to be $1$. The center-detecting representation then eliminates the remaining central torsion. Full principal level $N\ge3$ gives the same conclusion because an automorphism acting trivially on $A[N]$ is the identity.

Thus a neat center-detecting level has two simultaneous meanings: the arithmetic quotient has no orbifold stabilizers, and the PEL moduli problem is a fine set-valued functor. Adjoint neatness alone is insufficient because a scalar root of unity may act trivially on the domain but nontrivially on the universal abelian variety.

Level two supplies the standard warning. The automorphism $[-1]$ of a polarized abelian variety acts trivially on its two-torsion, so full level two does not remove it. On the symmetric domain the same scalar is central and acts trivially. The coarse point can therefore be perfectly smooth while the moduli object has inertia of order two. Full level at least three works because if an automorphism is the identity modulo $N\ge3$, the congruence argument forces every finite-order eigenvalue congruent to one modulo $N$ to equal one.

### 4.3 The one-dimensional analytic structure

Because $B$ is split at exactly $\tau_0$, the connected domain $X^+$ is a half-plane. Its tangent space is the unique $(-1,1)$ line in the adjoint Hodge structure. At fine level every chart is therefore

$$
\Gamma_g\backslash\mathfrak H,
$$

with $\Gamma_g$ torsion-free. It is a Riemann surface. The algebraic curve $Q_K^{\mathcal C}$ is smooth because its analytification is locally a complex disk; equivalently, the PEL local-model calculation gives one moving line in a rank-two space.

At arbitrary level the stabilizer acts on a local coordinate by a finite cyclic character. The analytic coarse quotient of a disk by such a group is again a disk, although the moduli stack retains inertia. Thus a coarse Shimura curve can be smooth as a curve even while no universal family exists on it. In higher dimension finite quotient singularities need not disappear; the one-dimensional conclusion should not be exported to Shimura surfaces.

### 4.4 Division algebras and absence of cusps

**Proposition 4.2.** The arithmetic quotient is compact if and only if the adjoint quaternionic group is anisotropic over $\mathbf Q$; for the basic group this is equivalent to $B$ being a division algebra.

**Proof strategy.** Noncompact ends of a rank-one arithmetic quotient are rational parabolic ends. A quaternion algebra has a rational parabolic exactly when it is split.

**Proof.** If $B\simeq M_2(F)$, the stabilizer of an $F$-line is a proper parabolic subgroup. Its rational unipotent radical produces cusps in every congruence quotient of the half-plane. Conversely, a proper rational parabolic of $PB^\times$ stabilizes a nonzero proper right ideal of $B$. A division algebra has no such ideal, so it has no rational parabolic. Reduction theory for rank-one arithmetic groups says that the quotient has a compact fundamental domain precisely when there is no rational parabolic. $\square$

In the division case, the smooth analytic curve is compact and hence the algebraic curve is proper. A smooth proper curve over a field is projective. In the split case, compactification requires cusp data and degenerating abelian varieties, which lie outside the quaternionic division setting of the later Hecke arguments.

## 5. Connected components

The symmetric domain has two half-planes, while the finite adelic coordinate has many cosets. Their interaction, not either factor separately, determines connected components. The safest formula is the exact nonabelian double quotient. Only after strong approximation has been applied may it be replaced by a class group.

### 5.1 The exact double-coset label

Fix the upper-half-plane component $X^+\subset X$ and put

$$
G(\mathbf Q)_+=\{q\in G(\mathbf Q):qX^+=X^+\}.                   \tag{5.1}
$$

Without any transitivity hypothesis there is always a natural orbit formula

$$
\pi_0\bigl(\operatorname{Sh}_K(G,X)(\mathbf C)\bigr)
\simeq
G(\mathbf Q)\backslash
\bigl(\pi_0(X)\times G(\mathbf A_f)/K\bigr).                    \tag{5.2a}
$$

Indeed a path keeps the finite adelic coordinate fixed and stays in one component of $X$, while the diagonal rational action gives exactly the displayed identifications. To replace (5.2a) by a single class set based at $X^+$, one needs rational transitivity on $\pi_0(X)$.

**Proposition 5.1.** Assume that $G(\mathbf Q)$ acts transitively on $\pi_0(X)$. Then there is a natural bijection

$$
\pi_0\bigl(\operatorname{Sh}_K(G,X)(\mathbf C)\bigr)
\simeq G(\mathbf Q)_+\backslash G(\mathbf A_f)/K.                 \tag{5.2}
$$

**Proof.** Rational transitivity moves the first coordinate of every representative into $X^+$. Once the first coordinate lies there, a continuous path cannot change the discrete finite adelic coset. Two such charts belong to the same component exactly when a rational element preserving $X^+$ and a right element of $K$ relate their finite coordinates. That is precisely (5.2). For the basic quaternionic group, the required transitivity is genuine prior mathematics: the rational reduced-norm theorem realizes every sign pattern allowed at the split real places and forces positivity only at Hamiltonian places. For a central modification it must be verified for that group and is not a consequence of equality of adjoint domains alone. $\square$

The label of $[h,g]$ is therefore the class of $g$, not its reduced norm until a theorem identifies those two descriptions.

### 5.2 Abelianization and strong approximation

Let

$$
\nu:G\longrightarrow T=G/G^{\mathrm{der}}
$$

be the maximal abelian quotient, and write

$$
T(\mathbf Q)^\dagger=\nu(G(\mathbf Q)_+).                         \tag{5.3}
$$

For the remainder of Sections 5.2--5.5, assume the rational transitivity used in Proposition 5.1. Also assume that $G^{\mathrm{der}}$ is simply connected and has a noncompact real factor. For the quaternionic curve this derived group is $\operatorname{Res}_{F/\mathbf Q}B^1$ in the basic case, and the split place $\tau_0$ supplies the required noncompact factor. A central modification must separately have the stated simply connected derived group. The rank-one strong-approximation theorem proved for these groups then makes $G^{\mathrm{der}}(\mathbf Q)$ dense in $G^{\mathrm{der}}(\mathbf A_f)$.

**Theorem 5.2 (component reduction).** Abelianization induces a bijection

$$
G(\mathbf Q)_+\backslash G(\mathbf A_f)/K
\xrightarrow{\sim}
T(\mathbf Q)^\dagger\backslash
\nu(G(\mathbf A_f))/\nu(K).                                      \tag{5.4}
$$

**Proof strategy.** If two adelic points have the same abelianized label, their quotient lies in the derived group after rational and level corrections. Strong approximation absorbs that quotient.

**Proof.** The map is visibly well defined and surjective onto the displayed image. Suppose $g_1$ and $g_2$ have the same image. There exist $q_0\in G(\mathbf Q)_+$ and $k_0\in K$ such that

$$
\nu(g_2)=\nu(q_0)\nu(g_1)\nu(k_0).
$$

Consequently

$$
d=q_0^{-1}g_2k_0^{-1}g_1^{-1}\in G^{\mathrm{der}}(\mathbf A_f).
$$

Let


$$
U=G^{\mathrm{der}}(\mathbf A_f)\cap g_1Kg_1^{-1},
$$

an open compact subgroup of the derived group. Strong approximation writes $d=q_du$ with $q_d\in G^{\mathrm{der}}(\mathbf Q)$ and $u\in U$. Since $u=g_1k_1g_1^{-1}$ for some $k_1\in K$, rearrangement gives

$$
g_2=q_0q_dg_1k_1k_0.
$$

The real group $G^{\mathrm{der}}(\mathbf R)$ is connected at the split $\operatorname{SL}_2(\mathbf R)$ factor and at every compact norm-one factor, so $q_d$ preserves $X^+$. Hence $q_0q_d\in G(\mathbf Q)_+$, and $g_1,g_2$ have the same class in (5.2). $\square$

Formula (5.4) deliberately retains $\nu(G(\mathbf A_f))$. Surjectivity on adelic points does not follow merely from surjectivity of algebraic groups when the kernel has finite central cohomology.

### 5.3 Reduced norms for the basic quaternionic group

For $G=\operatorname{Res}_{F/\mathbf Q}B^\times$, the abelianization is reduced norm

$$
\operatorname{Nrd}:B^\times\longrightarrow F^\times.             \tag{5.5}
$$

At every finite place, reduced norm $B_v^\times\to F_v^\times$ is surjective. Rationally, however, the image carries archimedean sign restrictions. Let $\operatorname{Ram}_\infty(B)$ be the real places where $B$ is Hamiltonian and put

$$
F_{B,+}^\times=
\{x\in F^\times:\tau(x)>0\text{ for }\tau\in
\operatorname{Ram}_\infty(B)\}.                                  \tag{5.6}
$$

The reduced-norm theorem for quaternion algebras gives

$$
\operatorname{Nrd}(B^\times)=F_{B,+}^\times.                     \tag{5.7}
$$

An element at a split real place preserves the upper half-plane exactly when its determinant, hence its reduced norm, is positive. Therefore

$$
\operatorname{Nrd}(G(\mathbf Q)_+)
=\operatorname{Nrd}(B^\times)\cap
\{x:\tau(x)>0\text{ at every split active }\tau\}.              \tag{5.8}
$$

All split real places are active in the basic quaternionic datum, and all ramified real places already occur in (5.6). Consequently

$$
\operatorname{Nrd}(G(\mathbf Q)_+)=F_+^\times,                   \tag{5.9}
$$

the totally positive elements of $F^\times$.

**Corollary 5.3 (basic quaternionic component formula).** For the basic group,

$$
\pi_0\bigl(\operatorname{Sh}_K(\mathbf C)\bigr)
\simeq
F_+^\times\backslash\mathbf A_{F,f}^\times/
\operatorname{Nrd}(K).                                            \tag{5.10}
$$

**Proof.** Combine (5.4), finite-local surjectivity of reduced norm, and (5.9). $\square$

The global reduced-norm statement used in (5.7) has no hidden finite-place obstruction. Necessity follows from the positive-definite Hamilton norm. For sufficiency, let $c\in F^\times$ have the required positive signs and consider the quadratic form

$$
q_c(x,t)=\operatorname{Nrd}(x)-ct^2
$$

on $B\oplus F$. At every finite place the local reduced norm is surjective; at a split real or complex place it is a determinant and is surjective; at a Hamiltonian place it represents precisely the positive elements. Hence $q_c$ is isotropic everywhere locally. The Hasse principle for quadratic forms in five variables makes it isotropic over $F$. A nonzero isotropic vector can be chosen with $t\ne0$: the projective quadric has a smooth local point with nonzero last coordinate everywhere, and weak approximation on a smooth quadric avoids the hyperplane $t=0$. Then $\operatorname{Nrd}(x/t)=c$. This proves (5.7) and shows explicitly why only real Hamilton signs survive globally.

If $\operatorname{Nrd}(K)=\widehat{\mathcal O}_F^\times$, formula (5.10) is the narrow ideal class group. Send a finite idele $x$ to the fractional ideal whose valuation at $\mathfrak p$ is $v_\mathfrak p(x_\mathfrak p)$. Right multiplication by units does not change the ideal, and left multiplication by a totally positive element changes it by a narrow principal ideal. More general $\operatorname{Nrd}(K)$ imposes congruence conditions and produces a narrow ray-type quotient. This is the concrete finite set indexing the analytic curves.

The intersection in (5.8) is a useful error check. The orientation condition alone imposes positivity at split active places, but a rational reduced norm is automatically positive at Hamiltonian places. Replacing the actual rational norm image by the orientation subgroup alone would erase a genuine narrow sign condition.

For example, if $F$ is real quadratic and $B$ is ramified at one real place and one finite place, then (5.10) uses totally positive principal elements. Positivity at the split place comes from preserving the chosen half-plane; positivity at the ramified place comes from the Hamilton norm. Both are necessary.

### 5.4 Central modifications and label discipline

Suppose $G^\natural$ is a connected central modification with the same adjoint datum and a rational PEL similitude representation. Its symmetric domain is still a half-plane, but its maximal abelian quotient $T^\natural$ need not be $\operatorname{Res}_{F/\mathbf Q}\mathbf G_m$. For a common-norm group it can be isogenous to $\mathbf G_m$ with a finite correction. The correct component set is

$$
T^\natural(\mathbf Q)^\dagger\backslash
\nu^\natural(G^\natural(\mathbf A_f))/\nu^\natural(K).          \tag{5.11}
$$

One may replace (5.11) by a simpler idele-class quotient only after proving both the image on finite adelic points and the image of $G^\natural(\mathbf Q)_+$. A central isogeny can create a finite cokernel at either place. Having the same adjoint group proves equality of domains, not equality of component labels.

If $f:G^\natural\to G$ is a central morphism inducing an adjoint isomorphism and $f(K^\natural)\subset K$, it gives a map of label sets through $\nu\circ f$. Its fibers are finite and are measured by the central adelic kernel modulo its rational and level subgroups. This finite discrepancy is exactly the one that must be retained when a PEL central modification is compared with the basic quaternionic curve.

### 5.5 How level change acts on labels

For $K'\subset K$, the level-forgetting map sends

$$
[g]_{K'}\longmapsto[g]_K                                          \tag{5.12}
$$

in the exact label sets (5.2), or equivalently reduces modulo the larger subgroup $\nu(K)$ in (5.4). It is surjective. The fiber over a label is not always $K/K'$: rational elements in the stabilizer of that component can identify nominal cosets.

At a normal inclusion $K'\triangleleft K$, the effective group acting on the components above $[g]_K$ is the image of $K/K'$ after quotienting by

$$
K\cap g^{-1}G(\mathbf Q)_+g.                                      \tag{5.13}
$$

The point stabilizer can be smaller than (5.13), because (5.13) only asks a rational element to preserve the domain component, not the point $h$. This distinction separates deck transformations of a connected cover from inertia at a point.

## 6. Canonical descent of components

The canonical model is defined over the reflex field $E$, but its geometric components need not be. Canonical reciprocity acts on the finite label set, and the stabilizer of a label determines the smallest field over which the corresponding component descends.

### 6.1 Ambient reciprocity

Pointwise CM reciprocity takes values in a Mumford--Tate torus that varies with the special point. Components cannot depend on that varying torus; they see only the fixed maximal abelian quotient of $G$. Ambient reciprocity is the universal projection of all special-point reciprocity maps to that quotient.

Let $T=G^{\mathrm{ab}}$. The abelianized Hodge cocharacter produces a morphism

$$
r_{(G,X)}:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m
\longrightarrow T.                                                 \tag{6.1}
$$

It sends the distinguished cocharacter of the reflex-field torus to $\nu\circ\mu_h$. If $h'$ is special with reflex field $E(h')$ and toric reciprocity map $r_{h'}$, functoriality of the cocharacter construction gives

$$
\nu\circ r_{h'}
=r_{(G,X)}\circ N_{E(h')/E}.                                      \tag{6.2}
$$

This equality is checked on the permutation basis of cocharacters: both sides send the distinguished basis element to the same Galois-orbit sum of $\nu\mu_{h'}$.

The norm in (6.2) is forced by the different reflex fields. A special point can have reflex field strictly larger than $E$. Restricting an automorphism from its abelian Galois group to $E$ corresponds, under class field theory, to taking the idele norm. Formula (6.2) says that the two algebraic torus maps already encode this compatibility before any idele is chosen.

### 6.2 Galois action on the label set

Let an Artin class be represented by $s\in\mathbf A_E^\times$ with positive component at every real place. Define

$$
[t]^{\operatorname{Art}_E(s)}
=[r_{(G,X)}(s_f)t]                                                  \tag{6.3}
$$

on the right side of (5.4). Principal ideles map to rational points and a sufficiently small open subgroup of finite ideles maps into $\nu(K)$, so (6.3) is well defined and factors through a finite ray class quotient.

Here the principal-idele assertion means **totally positive** principal ambiguity. The labelled-cocharacter construction of ambient reciprocity sends such an element into $T(\mathbf Q)^\dagger$. A general negative principal representative need not do so and can change a narrow component label; this is why the positivity convention of Chapter 1 is part of the formula, not an optional simplification.

**Theorem 6.1.** Under complex uniformization, the Galois action on geometric connected components of the canonical model is (6.3).

**Proof strategy.** Every component contains a special point. Compute Galois on that point by CM reciprocity and project to the abelianized label.

**Proof.** Special points are analytically, hence Zariski, dense in every component. Choose $x=[h',g]$ special in the component labelled by $[\nu(g)]$. Canonical reciprocity gives

$$
x^{\operatorname{Art}_{E(h')}(u)}=[h',r_{h'}(u_f)g].
$$

Its component label is multiplied by $\nu r_{h'}(u_f)$. Equation (6.2), together with norm functoriality of Artin reciprocity, identifies this with restriction of (6.3). Since component labels form a finite discrete set, equality on one point of each component proves the assertion. $\square$

For the basic group, (6.3) can be read in the narrow class quotient (5.10) through the reduced norm of $r_{(G,X)}(s_f)$. For a central modification it must be read in (5.11).

The action is a translation action on a finite abelian quotient. In particular, its kernel is independent of the chosen label: in (6.4) the factor $t$ cancels because $T$ is commutative. Different Galois orbits of components can still occur if the image of ambient reciprocity is a proper subgroup of the full label group, but every component has the same stabilizer under that translation subgroup. This observation is useful when deciding whether a union rather than one component is naturally defined over $E$.

### 6.3 Fields of definition of individual components

Let $c$ be a geometric component label represented by $t\in\nu(G(\mathbf A_f))$. Since $T$ is commutative, the factor $t$ cancels from its stabilizer condition. Define the open subgroup of the idele class group

$$
U_c=
E^\times
r_{(G,X)}^{-1}\bigl(T(\mathbf Q)^\dagger\nu(K)\bigr)
E_\infty^{\times,0}/E^\times
\subset\mathbf A_E^\times/E^\times,                             \tag{6.4}
$$

where the inverse image is taken on finite ideles and $E_\infty^{\times,0}$ is the identity component of the archimedean idele group. It is open of finite index. Let $E_c/E$ be the finite abelian extension corresponding to it under arithmetic class field theory. The notation retains $c$ to emphasize which component is descending, although the translation action makes the subgroup independent of the chosen label.

**Proposition 6.2.** The geometric component $C_c$ descends to $E_c$, and $E_c$ is its minimal field of definition inside $E^{\mathrm{ab}}$.

**Proof.** By Theorem 6.1, the stabilizer of $C_c$ in $\operatorname{Gal}(E^{\mathrm{ab}}/E)$ is exactly $\operatorname{Art}_E(U_c)$. The component is open and closed after base change, so it corresponds to a primitive idempotent in the finite etale algebra of global functions on the component scheme. That idempotent descends exactly under its Galois stabilizer. The fixed field is $E_c$, proving both descent and minimality. $\square$

If Galois permutes several components transitively, their union is defined over $E$ even though none of them is. Calling one of them “the component over $E$” without checking (6.4) is therefore incorrect.

Two extreme cases clarify the formula. If the component quotient is trivial, then $U_c$ is the whole idele class group and the curve is geometrically connected over $E$. If the ambient reciprocity image acts simply transitively on the label set, every component is defined over the same abelian extension $E_c$, and the base change to $E_c$ splits the full curve into individually defined components. Between these extremes, the label set is a disjoint union of translation orbits; each orbit is an $E$-defined open-and-closed union.

### 6.4 Descent of a stable component union

Let $\mathcal C$ be any union of labels stable under (6.3). The sum of the corresponding primitive idempotents is Galois fixed. Hence it cuts out an open-and-closed subcurve

$$
S_K^{\mathcal C}\subset S_K                                      \tag{6.5}
$$

over $E$. Conversely, if a component union descends to $E$, its label set is Galois stable. Thus stability of $\mathcal C$ is necessary and sufficient.

The PEL union selected by a polarization genus is often stable because the canonical Galois action transports the full PEL object, including its polarization module. When it is not stable, its Galois orbit is the smallest union admitting descent to $E$; an individual member descends only to the field determined by (6.4).

## 7. Fine, stacky, and coarse levels

The same analytic orbit set supports three algebraic objects. At fine level it is a scheme representing PEL objects. At arbitrary level it is a Deligne--Mumford quotient stack. Forgetting inertia gives a coarse curve. Hecke descent must say which of these carries a universal isogeny and which carries only its underlying correspondence.

### 7.1 Cofinal fine covers

An arbitrary level is best studied from above. A sufficiently deep normal level removes inertia while retaining a finite symmetry group that remembers how to return to the original curve. Cofinality ensures that no construction depends on one favored rigidification.

Given any compact open $K$, choose a normal principal congruence subgroup

$$
K'\triangleleft K
$$

which is neat, detects the center, and is contained in a principal congruence level of order at least three. Such subgroups are cofinal: embed $G$ faithfully in an integral general linear group away from finitely many primes and intersect with a sufficiently deep principal congruence kernel.

The curve $S_{K'}^{\mathcal C'}$ is fine on every PEL component union $\mathcal C'$ above $\mathcal C$. It carries a universal abelian scheme $\mathcal A_{K'}$ with its endomorphisms, polarization, determinant law, and level. The map to level $K$ is finite because a fixed abelian variety has only finitely many level structures modulo $K'$ above a $K$-orbit.

Normality is not needed merely to forget level, but it is what turns the finite cover into a group quotient. If a first congruence subgroup is not normal, intersect its finitely many $K$-conjugates. The intersection remains open, fine, and of finite index, and is now normal. This elementary refinement is what makes the cocycles in Chapters 9 and 12 honest group-action cocycles.

### 7.2 Nominal and effective level groups

The abstract quotient

$$
\widetilde\Delta_{K,K'}=K/K'                                     \tag{7.1}
$$

counts changes of a chosen marking. It is the **nominal level group**. Its action on the fine curve need not be faithful: a rational central element can act trivially on the analytic base while acting nontrivially on the universal abelian variety. That element is invisible to a coarse orbit space but remains genuine inertia in the moduli stack.

Let

$$
Z_{K,K'}/K'
=\ker\bigl(\widetilde\Delta_{K,K'}
\longrightarrow\operatorname{Aut}(S_{K'}^{\mathcal C'})\bigr),
$$

and define the **effective geometric group**

$$
\Delta_{K,K'}^{\mathrm{eff}}
=\widetilde\Delta_{K,K'}/(Z_{K,K'}/K').                          \tag{7.2}
$$

In the present faithful connected PEL setting, the kernel is accounted for by rational central elements whose right translation is already identified by the left rational action. The kernel should be removed when forming the coarse geometric quotient, but not when presenting the moduli stack.

More locally, the stabilizer of $[h,gK']$ in the nominal group consists of those $k$ for which

$$
q h=h,\qquad qgK'=gkK'                                             \tag{7.3}
$$

for some $q\in G(\mathbf Q)$. If the target level $K$ is fine, this stabilizer is trivial. At non-neat target level it is the automorphism group of the underlying $K$-level PEL object. The subgroup fixing every base point is the kernel in (7.2); its members still occur in every relevant stack stabilizer when they act nontrivially on the universal PEL object.

The distinction is already forced by level two. The scalar $-1$ can act trivially on the symmetric domain and on the coarse base while acting as $[-1]$ on every abelian fiber. Replacing the nominal group by its effective image in a quotient-stack presentation would delete precisely this inertia.

### 7.3 Quotient stacks and coarse curves

Define

$$
\mathscr S_K^{\mathcal C}=
[S_{K'}^{\mathcal C'}/\widetilde\Delta_{K,K'}],                  \tag{7.4}
$$

where $\mathcal C'$ is the full inverse image of $\mathcal C$. This quotient stack is independent of $K'$: two fine covers are dominated by their intersection, and the resulting action groupoids are equivalent.

The finite categorical quotient

$$
S_K^{\mathcal C,\mathrm{coarse}}
=S_{K'}^{\mathcal C'}/\Delta_{K,K'}^{\mathrm{eff}}              \tag{7.5}
$$

is the coarse canonical curve. Equivalently it is the finite categorical quotient by the nominal group, since an ineffectively acting kernel does not change invariant functions. It is independent of the cover because its function field on each component is the invariant field and normalization gives a unique normal curve. Its complex points are the orbit set (1.1) on $\mathcal C$.

If the quaternion algebra is division, both the stack (7.4) and the coarse curve (7.5) are proper. In dimension one the coarse curve is smooth over characteristic zero even at a cyclic quotient point, but the stack still records its nontrivial stabilizer.

### 7.4 What descends to which quotient

The universal PEL abelian scheme on $S_{K'}$ is equivariant for the nominal group and therefore descends to the quotient stack (7.4). It descends to the coarse curve if and only if every inertia group acts trivially on the fiber with all its PEL tensors. Indeed, a family pulled back from a coarse space has trivial inertia action, while the universal object's inertia action is the corresponding automorphism of the abelian variety. Thus coarse descent is equivalent to the fine condition.

The obstruction can be seen without stack language. Suppose a coarse point represents an object $A$ with a nontrivial automorphism $u$. A putative universal family over a neighborhood of that point would pull back to the same family along the two local branches related by $u$, but coarse descent would identify them through the identity on the fiber. The moduli descent datum identifies them through $u$. These data agree only if $u=1$. The quotient stack retains the choice of $u$ and therefore has no such contradiction.

The same rule applies to a universal isogeny. It exists on a fine Hecke space and on the corresponding quotient stack. The underlying pair of finite maps between coarse curves always descends because it does not require a universal object. A line bundle or a tensor power may descend under a weaker condition if inertia acts through a character killed by that power; this does not imply descent of the abelian scheme or isogeny.

## 8. Commensurable lattices and universal isogenies

An adelic element $a$ changes the integral lattice while leaving the rational Hodge structure fixed. Commensurable lattices define isogenous abelian varieties. This elementary observation is the geometric content of a Hecke operator.

### 8.1 The lattice attached to an adelic point

Recall $L_g=V(\mathbf Q)\cap g\widehat\Lambda$. For $a\in G(\mathbf A_f)$, the lattices $L_g$ and $L_{ga}$ are commensurable because $a\widehat\Lambda$ and $\widehat\Lambda$ are compact open lattices in the same finite adelic vector space. Hence

$$
L_g\cap L_{ga}
$$

has finite index in each. The identity on $V_{\mathbf R}$ therefore induces a canonical quasi-isogeny between $A_{h,g}$ and $A_{h,ga}$.

The quasi-isogeny becomes an honest isogeny after choosing an integral representative of the same rational central class. This choice affects the isogeny by a scalar multiplication but not the Hecke correspondence.

This construction is uniform in $h$. Hecke translation changes the finite lattice, not the archimedean Hodge homomorphism. Consequently the differential of the isogeny is an isomorphism in characteristic zero, the determinant law on the Lie algebra is unchanged, and all variation occurs in a finite etale kernel. This separation is why generic Hecke geometry is etale even though its integral extension at a residue characteristic dividing the kernel can be highly non-etale.

### 8.2 Integral representatives and the analytic isogeny

Because $a\widehat\Lambda$ is commensurable with $\widehat\Lambda$, there is an integer $m>0$ with

$$
ma\widehat\Lambda\subset\widehat\Lambda.                         \tag{8.1}
$$

The scalar $m$ lies in the rational center of the PEL similitude group. Left multiplication by it does not change the induced map of the rational Shimura quotient, so we may replace $a$ by $ma$ when constructing an honest isogeny. Under (8.1),

$$
L_{ga}\subset L_g.                                                  \tag{8.2}
$$

Indeed, membership in $ga\widehat\Lambda$ implies membership in $g\widehat\Lambda$. The identity on $V_{\mathbf R}$ descends to

$$
\phi_{a,h,g}:A_{h,ga}=V_{\mathbf R}/L_{ga}
\longrightarrow A_{h,g}=V_{\mathbf R}/L_g.                        \tag{8.3}
$$

Its kernel is $L_g/L_{ga}$ and its degree is the index $[L_g:L_{ga}]$.

The direction in (8.3) is forced by lattice inclusion. If one chooses the inverse integrality convention $\widehat\Lambda\subset a\widehat\Lambda$, the displayed isogeny reverses. The resulting correspondence is the same after replacing $a$ by $a^{-1}$ and transposing.

At a finite place where $B$ is split and the lattice is standard, take

$$
a_v=\begin{pmatrix}\varpi_v&0\\0&1\end{pmatrix}.
$$

Then $a_v\Lambda_v\subset\Lambda_v$ with quotient the residue field $k_v$ as an additive module. The associated isogeny has a kernel of order $q_v=|k_v|$ in the active rank-two factor. Away from $v$ the lattices agree, so the kernel is supported entirely at $v$. This local picture is the quaternionic analogue of a cyclic $\mathfrak p$-isogeny of elliptic curves.

The phrase “in the active rank-two factor” is essential. In a higher-dimensional PEL representation that factor can occur with a fixed multiplicity, and the order of the full kernel is then the corresponding power of $q_v$. The invariant general formula is the lattice index (8.10), not the elliptic-curve number $q_v$.

### 8.3 The intermediate level

A Hecke correspondence needs enough level to remember both the old lattice and the modified lattice. The intersection $K_a$ is the largest subgroup for which these two memories are simultaneously well defined; choosing a smaller subgroup only adds redundant rigidification.

Set

$$
K_a=K\cap aKa^{-1}.                                                 \tag{8.4}
$$

There are two maps

$$
p_1:S_{K_a}\longrightarrow S_K,
\qquad [h,gK_a]\longmapsto[h,gK],                                 \tag{8.5}
$$

and

$$
p_2:S_{K_a}\longrightarrow S_K,
\qquad [h,gK_a]\longmapsto[h,gaK].                                \tag{8.6}
$$

The second is well defined because $k\in K_a$ implies $a^{-1}ka\in K$. Notice that this check fixes the intersection in (8.4); using $K\cap a^{-1}Ka$ with the same right-translation formula would be wrong.

If $K$ and $K_a$ are fine and the component union is chosen so that both images are PEL unions, the two pullbacks of the universal family have fibers

$$
(p_1^*\mathcal A_K)_{[h,g]}=A_{h,g},
\qquad
(p_2^*\mathcal A_K)_{[h,g]}=A_{h,ga}.                              \tag{8.7}
$$

Thus (8.3) suggests a universal isogeny

$$
\Phi_a:p_2^*\mathcal A_K\longrightarrow p_1^*\mathcal A_K.       \tag{8.8}
$$

The domain of this isogeny is the family classified after applying $a$, while its codomain is the family before applying $a$. This may look opposite to the arrow $p_2$ on base curves, but it is exactly the covariance of quotienting a smaller lattice into a larger one. The Hecke span itself has no preferred arrow between its two endpoint curves; the lattice inclusion supplies the additional orientation of the universal isogeny.

### 8.4 Kernel, degree, and polarization multiplier

Under (8.1), define the finite lattice module

$$
C_a=\widehat\Lambda/a\widehat\Lambda.                             \tag{8.9}
$$

It is supported at finitely many rational primes. On the fine level cover, the universal adelic marking identifies the kernel of (8.8) with the locally constant finite subgroup of the source family determined by the transported module $gC_a$. Its geometric fiber is $L_g/L_{ga}$, canonically identified with the appropriate global realization of (8.9).

The index, hence the degree, is locally constant and independent of $h$ and $g$ on a fixed lattice genus:

$$
\deg\Phi_a=[\widehat\Lambda:a\widehat\Lambda].                  \tag{8.10}
$$

The $D$-action commutes with the identity on $V$, so $\Phi_a$ is $D$-linear. If $\nu(a)$ is the similitude multiplier, the rational alternating forms satisfy

$$
\psi(ax,ay)=\nu(a)\psi(x,y).                                     \tag{8.11}
$$

After the integral polarizations on the two component types are chosen, (8.11) becomes

$$
\Phi_a^*\lambda_1=c_a\lambda_2                                  \tag{8.12}
$$

for the positive rational scalar dictated by the chosen integral representative and polarization modules. It is an integer whenever both sides are actual homomorphisms and the chosen normalization makes $c_a\lambda_2$ integral. There is no universal formula $c_a=\nu(a)$ without first identifying the two polarization lattices; the idele $\nu(a)$ need not be a rational number.

The kernel and polarization are linked by an isotropy condition. If $q:A_2\to A_1$ and $q^*\lambda_1=c\lambda_2$, then $\ker q$ is isotropic for the commutator pairing attached to $c\lambda_2$. Conversely, an isotropic finite subgroup of the appropriate order lets $c\lambda_2$ descend uniquely to a polarization on the quotient. In the lattice model, isotropy is the statement that the alternating form on $L_{ga}$ takes integral values on $L_g$ after the factor $c_a$ is inserted. Thus (8.12) is not an extra decoration: it is the exact condition making the quotient family a PEL family of the target type.

## 9. Algebraic construction and descent of the universal isogeny

The lattice formula gives an isogeny on every complex fiber, but later arithmetic arguments need one algebraic morphism of abelian schemes. We construct it from its finite kernel. This also shows exactly why it descends through fine level and why it may fail on a coarse curve.

### 9.1 Construction from a finite subgroup

Assume first that the endpoint level $K$ is fine; then $K_a\subset K$ is fine as well, and both universal families in (8.7) exist on schemes. Choose an integer $N$ annihilating $C_a$ in (8.9). After passing temporarily to a normal finer level $K'\subset K_a$ contained in the principal level-$N$ subgroup and in an auxiliary principal level of order at least three, the universal level marking identifies $C_a$ with a finite subgroup

$$
\mathcal H_a\subset p_2^*\mathcal A_K[N].                         \tag{9.1}
$$

The subgroup is $\mathcal O$-stable because $a$ lies in the $D$-linear similitude group. It is finite etale over the characteristic-zero base.

The fppf quotient

$$
\mathcal B_a=(p_2^*\mathcal A_K)/\mathcal H_a                     \tag{9.2}
$$

exists and is an abelian scheme. Locally on the base it is the quotient of a projective group scheme by a finite free action; the quotient is proper and smooth, and its fibers are connected abelian varieties. The quotient map

$$
q_a:p_2^*\mathcal A_K\longrightarrow\mathcal B_a                 \tag{9.3}
$$

is a finite flat $D$-linear isogeny.

The construction does not actually depend on the chosen full-level refinement. The subgroup (9.1) is characterized fiberwise by the $K_a$-invariant relative lattice $L_g/L_{ga}$. If $k\in K_a$, then $a^{-1}ka\in K$, so replacing $g$ by $gk$ preserves both lattices in (8.7) and the quotient between them. Hence the descent action of the finite deck group preserves $\mathcal H_a$.

The quotient assertion used here can be proved directly. A finite locally free subgroup $H\subset A$ acts freely on the abelian scheme $A$. The fppf sheaf quotient is represented by a proper smooth scheme because this can be checked after a faithfully flat cover on which $H$ is constant and the finite orbit quotient is explicit. The group law descends, every geometric fiber is the quotient of an abelian variety by a finite subgroup, and hence is a connected abelian variety. The map $A\to A/H$ is finite locally free of rank $|H|$. This construction commutes with base change and with every endomorphism preserving $H$.

### 9.2 Identification with the translated universal family

**Proposition 9.1.** There is a unique PEL isomorphism

$$
\iota_a:\mathcal B_a\xrightarrow{\sim}p_1^*\mathcal A_K          \tag{9.4}
$$

whose complex fiber at $[h,g]$ is the identity-induced isomorphism

$$
A_{h,ga}/(L_g/L_{ga})\simeq A_{h,g}.                               \tag{9.5}
$$

Consequently $\Phi_a=\iota_a\circ q_a$ is the algebraic universal isogeny (8.8).

**Proof strategy.** Give the quotient family the PEL structure transported from the lattice quotient, then use the fine moduli property. Fiberwise uniformization identifies its classifying map with $p_1$.

**Proof.** The $D$-action descends through the $D$-stable subgroup. Equation (8.12) descends the appropriate polarization on the quotient, and the quotient of the level lattice by $C_a$ gives the $K$-level structure represented by $g$. The determinant law is unchanged because an isogeny in characteristic zero induces an isomorphism on Lie algebras. Thus $\mathcal B_a$ is a family of the PEL type classified by $S_K$.

More explicitly, the isotropy discussed in Section 8.4 descends the polarization by the quotient theorem for polarized abelian schemes. Positivity can be checked on one geometric fiber and is locally constant in a connected family; on every complex fiber it is the positive Riemann form of $A_{h,g}$. The Rosati identity descends because both sides become equal after pullback by the faithfully flat isogeny $q_a$. This supplies all PEL tensors before the fine moduli property is invoked.

On complex points, its classifying map sends $[h,gK_a]$ to the object with lattice $L_g$, hence to $[h,gK]$ by Theorem 3.2. It is therefore $p_1$. Fine representability supplies a unique isomorphism (9.4) respecting all universal data. Composing with (9.3) gives $\Phi_a$, and (9.5) proves that its analytification is (8.3). $\square$

This proof is algebraic and does not require compactness. In the division case one could alternatively algebraize the analytic homomorphism by proper GAGA, but the kernel construction also works for nonproper fine curves.

### 9.3 Descent from a rigidifying cover

Let $K'\triangleleft K_a$ be a rigidifying cover as above. The subgroup $\mathcal H_a$, its quotient, and $\Phi_a$ carry natural equivariant structures for the nominal level group $K_a/K'$. The cocycle is literal: two level changes act by composing their actions on the same lattice quotient. Because the target $K_a$ is fine in the present paragraph, this action has no stabilizer on the moduli object, and effective finite descent for abelian schemes and their homomorphisms gives (8.8) on the fine curve $S_{K_a}$.

At arbitrary $K_a$, the same equivariant object descends through the nominal level group to the quotient stack $\mathscr S_{K_a}$. Passing first to the effective geometric group would lose any central inertia acting trivially on the base. The isogeny descends to the coarse curve precisely when every inertia element acts trivially on the source family, target family, and the isogeny. Since an inertia element is already a nontrivial automorphism of a universal PEL object in the non-fine case, this condition generally fails.

The failure is not a defect in the Hecke theory. The coarse maps $p_1,p_2$ descend independently of universal families, and hence the coarse finite correspondence exists. What is lost is the ability to regard each coarse point as carrying one functorially chosen abelian variety and one functorially chosen isogeny.

### 9.4 Independence and composition

Replacing the integral representative $a$ by $ma$ for a positive rational central scalar changes the honest isogeny by a scalar multiplication. More precisely, on a common fine refinement the two rational quasi-isogenies differ by $[m]$. Their kernels and degrees differ, but their maps of Shimura curves are identical because $m\in G(\mathbf Q)$ acts on the left. Thus a double coset defines a canonical correspondence and a canonical universal quasi-isogeny; an honest universal isogeny additionally uses an integral normalization.

If $a$ and $b$ have integral representatives with

$$
ab\widehat\Lambda\subset a\widehat\Lambda\subset\widehat\Lambda,
$$

then on the common level where all three lattices are visible,

$$
A_{h,gab}\xrightarrow{\Phi_b}A_{h,ga}
\xrightarrow{\Phi_a}A_{h,g}                                     \tag{9.6}
$$

is the identity-induced isogeny for $ab$. Therefore

$$
\Phi_{ab}=\Phi_a\circ\Phi_b                                     \tag{9.7}
$$

after the evident pullbacks. The equality holds algebraically because it holds on every complex fiber and homomorphisms of abelian schemes are rigid.

For completeness, the rigidity used here has a simple form. If $A$ and $B$ are abelian schemes over a reduced connected base, the relative Hom functor is separated and unramified. Two sections agreeing on a dense set of geometric fibers agree on the whole base. Their difference is a section whose zero locus is both open and closed; density forces that locus to be all of the base.

## 10. Hecke correspondences at finite level

The universal isogeny lives over an intermediate level, while the Hecke operator is the span obtained by forgetting that intermediate structure in two different ways. This span depends only on the double coset $KaK$.

### 10.1 The double-coset span

For $a\in G(\mathbf A_f)$ define $K_a$ by (8.4). The Hecke correspondence is

$$
T(a)=
\left(
S_K\xleftarrow{\ p_1\ }S_{K_a}
\xrightarrow{\ p_2\ }S_K
\right),                                                          \tag{10.1}
$$

with $p_1$ and $p_2$ as in (8.5)--(8.6). If component unions are being selected, the middle term is restricted to the labels whose two images lie in the chosen source and target unions.

**Proposition 10.1.** Up to unique isomorphism of spans, $T(a)$ depends only on $KaK$.

**Proof.** Replacing $a$ by $k_1ak_2$ with $k_1,k_2\in K$ replaces the intermediate level by the conjugate $k_1K_ak_1^{-1}$. Right translation by $k_1$ identifies the two middle curves. Under that identification the first projection is unchanged in the quotient and the second differs by right multiplication by an element of $K$, hence is also unchanged. $\square$

One can equivalently decompose

$$
KaK=\coprod_{i=1}^d a_iK                                           \tag{10.2}
$$

and view $T(a)$ above a point $[h,g]$ as the multiset $[h,ga_i]$. The span formulation is canonical and retains automorphisms; the coset formula is useful for calculations.

### 10.2 Finiteness, etaleness, and degrees

Both $p_1$ and $p_2$ are finite. At fine levels they are etale because they forget finite etale characteristic-zero level data and have no stabilizers. Their total degrees are

$$
\deg p_1=[K:K_a],
\qquad
\deg p_2=[K:a^{-1}K_aa].                                          \tag{10.3}
$$

Now

$$
a^{-1}K_aa=K\cap a^{-1}Ka.
$$

The two indices in (10.3) are equal. Indeed, choose Haar measure on the unimodular locally compact group $G(\mathbf A_f)$ with $\operatorname{vol}(K)=1$. Conjugation preserves Haar measure, so

$$
[K:K\cap aKa^{-1}]
=[K:K\cap a^{-1}Ka].                                               \tag{10.4}
$$

At non-neat level, the coarse maps remain finite but their geometric ramification and pointwise fiber cardinality are altered by inertia. The stack degrees retain the index formula. On one connected component, the degree can split among several target components; the sum over all component routes is (10.3).

For the local element $a_v=\operatorname{diag}(\varpi_v,1)$ with $K_v=\operatorname{GL}_2(\mathcal O_v)$, the quotient $K_v/(K_v\cap a_vK_va_v^{-1})$ is the projective line over $k_v$. Hence the local degree is $q_v+1$. Its points correspond to rank-one quotients of the two-dimensional residue lattice, or equivalently to the $q_v+1$ cyclic subgroups that can occur as kernels. This example separates the degree of one universal isogeny, which is $q_v$, from the degree of the Hecke correspondence, which is $q_v+1$.

### 10.3 Action on connected components

Before using a Hecke operator on one connected curve, one must know where it lands. The component calculation turns that geometric routing question into multiplication in a finite abelian class group.

In the exact label set (5.2), the two projections send

$$
[g]_{K_a}\longmapsto[g]_K,
\qquad
[g]_{K_a}\longmapsto[ga]_K.                                      \tag{10.5}
$$

After abelianization the second label is

$$
[\nu(g)]\longmapsto[\nu(g)\nu(a)].                              \tag{10.6}
$$

Thus Hecke routing among components is right multiplication by $\nu(a)$. This formula is meaningful in the quotient (5.4); it must not be silently rewritten as ideal multiplication unless the basic reduced-norm identification (5.10) has been proved for the group in question.

For the basic group, (10.6) multiplies the narrow class of $\operatorname{Nrd}(g)$ by the finite idele $\operatorname{Nrd}(a)$. If this class is trivial modulo $F_+^\times\operatorname{Nrd}(K)$, the correspondence preserves every component label; otherwise it permutes them. A Hecke operator on one chosen component is therefore defined over its component field only when this routing and the Galois stabilizer are compatible.

If $\nu(a)$ is trivial in the component quotient, every middle component maps under $p_1$ and $p_2$ to the same endpoint component label. If it is nontrivial, $T(a)$ is naturally a correspondence between two different component factors. Summing over a full Galois-stable orbit of labels restores an endomorphism of the corresponding product of curves or Jacobians. This is why automorphic Hecke algebras are most naturally attached to the whole stable tower rather than to an arbitrarily chosen geometric component.

### 10.4 Transpose

Transpose forgets which endpoint was called the source. Since right translation by $a$ becomes right translation by $a^{-1}$ when the path is traversed backward, inversion is unavoidable.

Interchanging the two projections in (10.1) gives the correspondence attached to $a^{-1}$.

**Proposition 10.2.** There is an isomorphism

$$
T(a)^t\simeq T(a^{-1}).                                            \tag{10.7}
$$

**Proof.** Right translation by $a$ identifies $S_{K_a}$ with the intermediate curve for $a^{-1}$ because

$$
a^{-1}K_aa=K\cap a^{-1}Ka=K_{a^{-1}}.
$$

Under this identification $p_2$ becomes the first projection and $p_1$ becomes the second. $\square$

On universal quasi-isogenies, transpose replaces the lattice inclusion by its inverse rational map. On Jacobians, (10.7) becomes adjunction for the canonical principal polarizations.

For an integral representative, the inverse quasi-isogeny is usually not the dual isogeny without a scalar. If $\Phi_a^*\lambda_1=c_a\lambda_2$, then the polarized adjoint satisfies

$$
\Phi_a^\dagger\Phi_a=[c_a]
$$

in the rational isogeny category with the chosen normalization. Thus reversing a Hecke path and taking the polarized adjoint agree after the same scalar bookkeeping already present in Section 8.4. At the level of curve correspondences no scalar appears: transpose is exactly $T(a^{-1})$.

## 11. Composition and the Hecke algebra

Two Hecke operations compose by a fiber product of intermediate levels. That fiber product is generally disconnected. Its components, with their covering multiplicities, are exactly the terms in double-coset convolution.

### 11.1 Fiber products of spans

Composition of relations is not obtained by multiplying the two displayed adelic representatives and forgetting the middle point. Different middle level structures can lead to the same final double coset, and those repetitions are the multiplicities of the Hecke algebra. The fiber product retains them automatically.

Let $a,b\in G(\mathbf A_f)$. The composite of $T(a)$ followed by $T(b)$ is represented by

$$
S_{K_a}\times_{S_K,p_2,p_1}S_{K_b}.                               \tag{11.1}
$$

A complex point records a chain

$$
[h,g]\longmapsto[h,ga]\longmapsto[h,gab]
$$

together with the intermediate level choices. Decomposing those choices into $K$-orbits decomposes (11.1) into finite covers of intermediate curves $S_{K_c}$ for finitely many double cosets $KcK\subset KaKbK$.

The fiber product is taken as a scheme or stack before passing to its cycle. This retains nontransverse multiplicities and inertia. In characteristic zero at fine level all maps are etale, so the fiber product is reduced and the multiplicities count the number of components mapping to the same double-coset span.

Concretely, a point of (11.1) consists of points $x_a\in S_{K_a}$ and $x_b\in S_{K_b}$ with $p_2(x_a)=p_1(x_b)$. Choosing representatives makes this equality a rational-and-level relation, not literal equality of the two adelic coordinates. Absorbing that relation changes the representative $b$ by left and right elements of $K$. This is why all products $a_i b_j$, rather than only $ab$, appear in the final decomposition.

### 11.2 Multiplicity and double-coset convolution

Normalize Haar measure by $\operatorname{vol}(K)=1$. Let $1_{KaK}$ be the characteristic function of $KaK$. Its convolution with $1_{KbK}$ is

$$
1_{KaK}*1_{KbK}=\sum_c m(a,b;c)1_{KcK},                            \tag{11.2}
$$

where the finite sum runs over double cosets contained in $KaKbK$ and $m(a,b;c)$ is a nonnegative integer.

**Theorem 11.1 (geometric convolution).** As finite cycle correspondences,

$$
T(b)\circ T(a)=\sum_c m(a,b;c)T(c).                               \tag{11.3}
$$

**Proof strategy.** Use right-coset representatives to identify both sides with the same multiset of two-step paths. The number of intermediate representatives yielding one final double coset is the convolution coefficient.

**Proof.** Write $KaK=\coprod_i a_iK$ and $KbK=\coprod_j b_jK$. Over $[h,g]$, the composite multiset consists of $[h,ga_ib_j]$ for all pairs $(i,j)$. Group the products $a_ib_j$ by their $K$-double cosets. For a fixed $KcK$, the number of pairs after quotienting by the common right-$K$ ambiguity is precisely the integral defining the convolution coefficient of $1_{KcK}$. The same grouping decomposes the fiber product (11.1) into its finite etale components. Therefore the equality holds as cycles, including multiplicity. $\square$

Associativity of convolution is now geometric associativity of fiber products. No separate relation needs to be imposed on the correspondence algebra.

### 11.3 The universal-isogeny cocycle

Convolution should be compatible not only with endpoint curves but with the actual isogenies of PEL abelian varieties. The relevant coherence is a cocycle on every chain of commensurable lattices.

On a common fine refinement, the universal quasi-isogenies along a two-step path compose. The lattice chain gives

$$
\Phi_{a_ib_j}=\Phi_{a_i}\circ\Phi_{b_j}                            \tag{11.4}
$$

with the pullbacks and direction interpreted as in (9.6). When paths are grouped into the same double coset $KcK$, their universal quasi-isogenies are identified by the corresponding change-of-level isomorphisms. Thus the universal-isogeny construction is compatible with (11.3), not merely the maps of base curves.

If honest integral representatives are chosen independently, scalar multiplications can appear in (11.4). Passing to quasi-isogenies removes this artifact. Alternatively choose one common integer clearing all denominators in a finite convolution calculation; then every lattice lies in a single nested diagram and the equality is literal after the predictable common scalar.

For three elements $a,b,c$, the two parenthesizations of the composite both arise from the identity map on $V_{\mathbf R}$ and the same inclusion of the final lattice into the initial lattice. Hence the cocycle is associative without an additional scalar once quasi-isogenies are used. This coherence is essential when the Hecke algebra acts on a functorial construction made from the universal abelian scheme: there is one canonical composite, not merely equality of its effect on geometric points.

### 11.4 Correspondences on Jacobians

Assume the relevant component unions are smooth proper curves, as in the quaternion division case. Let $J_K$ be the product of their Jacobians. The span (10.1) acts by

$$
T(a)_J=p_{2*}p_1^*:J_K\longrightarrow J_K.                        \tag{11.5}
$$

The generic correspondence theory gives

$$
T(b)_J T(a)_J
=\sum_c m(a,b;c)T(c)_J,                                           \tag{11.6}
$$

and

$$
T(a)_J^\dagger=T(a^{-1})_J.                                      \tag{11.7}
$$

**Proof.** Formula (11.6) is the pull--norm composition theorem applied to the fiber product (11.1), whose cycle decomposition is (11.3). Formula (11.7) follows because pullback and norm are dual under the canonical polarizations and the transposed span is (10.7). $\square$

If a component is not preserved, (11.5) is a homomorphism between products of Jacobians indexed by source and target component unions. Restricting it to one factor without checking (10.6) is not well typed.

## 12. Descent of Hecke maps and correspondences

All constructions so far can be seen over $\mathbf C$. The canonical model is useful only if the level maps, Hecke spans, and universal isogenies descend to their correct number fields. The proof rests on the left--right commutation fixed in Chapter 1.

### 12.1 Right translation commutes with canonical reciprocity

The descent calculation is short because all normalization work has already been done. Its brevity should not obscure its content: it compares an arithmetic Galois action defined by CM theory with a geometric operation defined by changing finite level lattices.

Let $x=[h,g]$ be special. For an idele $s$ of its reflex field and $a\in G(\mathbf A_f)$,

$$
\begin{aligned}
R_a\bigl(x^{\operatorname{Art}(s)}\bigr)
&=R_a([h,r_h(s_f)g])\\
&=[h,r_h(s_f)ga]\\
&=R_a(x)^{\operatorname{Art}(s)}.
\end{aligned}                                                       \tag{12.1}
$$

No commutativity inside $G(\mathbf A_f)$ is being asserted. The two operations associate on different sides of $g$. If reciprocity or Hecke translation were written with the opposite variance, an inverse would be necessary.

The same identity works for a level-forgetting map by taking $a=1$ and changing only the right stabilizer. It also works for a chain of Hecke translations, because left multiplication remains outside the entire right-hand product. Consequently one descent check controls the whole tower and every convolution relation, rather than one operator at a time.

### 12.2 Descent at fine level

**Theorem 12.1.** Let $K_1,K_2$ be fine compact opens and let $a\in G(\mathbf A_f)$ satisfy $a^{-1}K_1a\subset K_2$. Then

$$
R_a:S_{K_1,\mathbf C}\longrightarrow S_{K_2,\mathbf C},
\qquad[h,g]\longmapsto[h,ga]                                      \tag{12.2}
$$

descends uniquely to the reflex field $E$. On stable component unions it restricts over $E$ exactly when its component routing maps the source union into the target union.

**Proof strategy.** Canonical descent is characterized on the dense set of special points. Equation (12.1) says that right translation commutes with that descent datum.

**Proof.** The analytic map is algebraic: on fine PEL unions it is the classifying map obtained from the quotient construction of Chapter 9, while on the full canonical curve it is the algebraic Hecke translation in the canonical tower. Equation (12.1) shows compatibility with Galois descent on every special point. Special points are Zariski dense in every component, so the conjugate of $R_a$ equals $R_a$ everywhere. Effective finite descent gives an $E$-morphism. Uniqueness follows after base change to $\mathbf C$. A stable component restriction descends precisely when its open-and-closed idempotent is preserved, which is the routing condition (10.6). $\square$

Applying the theorem to the inclusions and translation defining $p_1,p_2$ proves that the fine Hecke span (10.1) is defined over $E$.

### 12.3 Descent at coarse level

Coarse descent cannot be proved by pretending a non-neat moduli problem is fine. Instead one descends the fine equivariant diagram and only then forgets inertia by taking the finite categorical quotient.

Choose a common normal fine subgroup $K'\subset K_a\subset K$. The maps $p_1,p_2$ on $S_{K'}$ are equivariant for the appropriate nominal level groups. Quotienting by those groups gives a diagram of quotient stacks over $E$, with all ineffective central stabilizers retained. Taking finite categorical quotients, equivalently passing to the effective images on the base curves, gives

$$
S_K^{\mathrm{coarse}}
\xleftarrow{p_1}
S_{K_a}^{\mathrm{coarse}}
\xrightarrow{p_2}
S_K^{\mathrm{coarse}}                                             \tag{12.3}
$$

over $E$. Independence of $K'$ follows by domination with the intersection of two choices and uniqueness of normal finite quotients.

The cycle relation (11.3) also descends. It is an equality of finite algebraic cycles after base change to $\mathbf C$; faithful flatness of $\mathbf C/E$ makes the equality hold over $E$. Hence the $E$-rational Hecke correspondences realize the same convolution algebra as their analytic double cosets.

Normality is used twice. It makes the quotient curve independent of the chosen fine cover, and it makes a finite correspondence determined by its generic cycle together with the finite maps from its normalization. Without normalizing, two quotient presentations could retain different embedded structures at an orbifold point even though they have the same orbit set.

### 12.4 Descent of the universal isogeny

**Theorem 12.2.** On the fine intermediate PEL curve, the universal isogeny

$$
\Phi_a:p_2^*\mathcal A_K\longrightarrow p_1^*\mathcal A_K        \tag{12.4}
$$

and all its $D$-action and polarization compatibilities are defined over the field of definition of the component union. It descends to the Hecke quotient stack at arbitrary level. It descends to the coarse Hecke curve if and only if inertia acts trivially on the entire diagram.

**Proof strategy.** The finite kernel is defined by a relative adelic lattice quotient. Canonical Galois acts by left multiplication, which transports both lattices simultaneously and leaves their relative quotient unchanged.

**Proof.** On a special fiber $[h,g]$, Galois replaces $g$ by $r_h(s_f)g$. It carries the inclusion

$$
L_{ga}\subset L_g
$$

to

$$
L_{r_h(s_f)ga}\subset L_{r_h(s_f)g}.
$$

The identity-induced quotient map is transported to the identity-induced quotient map. Hence the conjugate descent of $\Phi_a$ and $\Phi_a$ agree on all special fibers. The relative Hom scheme between the two abelian schemes is separated and unramified, so density and rigidity make them equal globally. The $D$-linearity and polarization equation descend because they are equalities of homomorphisms. Effective descent gives (12.4) over the component field.

Equivariance under level deck transformations was proved in Section 9.3, giving the stack statement. A morphism pulled back from a coarse curve has trivial inertia action; conversely, trivial inertia makes the equivariant descent datum effective on the coarse quotient. This proves the last assertion. $\square$

The theorem distinguishes two meanings of “Hecke correspondence descends.” The finite span always descends to the coarse canonical curve. A universal isogeny descends only where universal PEL objects themselves make sense.

## 13. The complete uniformization and Hecke package

We can now state the result as one reusable theorem. Its hypotheses separate rational Shimura data, PEL representability, component selection, and fineness, because each controls a different conclusion.

### 13.1 Main theorem

**Theorem 13.1 (uniformization, components, and Hecke descent).** Let $(G,X)$ be a quaternionic Shimura datum of dimension one with reflex field $E$. Assume that:

1. $G$ is either $\operatorname{Res}_{F/\mathbf Q}B^\times$, where $B/F$ is split at exactly one real place, or a specified connected central modification with the same adjoint datum;
2. the chosen group $G$ itself is the connected similitude group of a genuine quaternionic PEL realization $(D,*,V,\psi,h_0)$, with compatible order, lattice, polarization data, determinant law, and compact open levels;
3. $G^{\mathrm{der}}$ is simply connected and satisfies strong approximation away from the noncompact real factor;
4. $G(\mathbf Q)$ acts transitively on $\pi_0(X)$ whenever the single-base-component formulas (5.2)--(5.4) are used;
5. every PEL component union under discussion is selected by explicit locally constant integral invariants and is stable under the relevant Galois action when descent to $E$ is claimed.

Then the following statements hold.

1. At fine level, the complex PEL curve is biholomorphic to its selected union in

   $$
   G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/K),
   $$

   and the universal family is the Riemann family with fiber $V_{\mathbf R}/L_g$.
2. Point stabilizers are (4.1). Neatness detecting the center kills them. At arbitrary level they are precisely the inertia groups of the quotient stack.
3. Connected components are canonically

   $$
   T(\mathbf Q)^\dagger\backslash
   \nu(G(\mathbf A_f))/\nu(K).
   $$

   For the basic group this is the narrow reduced-norm quotient

   $$
   F_+^\times\backslash\mathbf A_{F,f}^\times/\operatorname{Nrd}(K).
   $$

4. Arithmetic Galois acts on component labels by left multiplication with $r_{(G,X)}(s_f)$, where the Artin class is represented positively at every real place. The field of an individual component is the finite abelian extension cut out by (6.4).
5. Every arbitrary level is the quotient stack of a cofinal fine cover by the nominal level group $K/K'$, so ineffective central inertia is retained. Its coarse canonical curve is the normal finite categorical quotient, equivalently the quotient by the effective geometric image. The universal family descends to the stack and to the coarse curve exactly in the fine case.
6. For $a\in G(\mathbf A_f)$ and $K_a=K\cap aKa^{-1}$, the two finite maps (8.5)--(8.6) define the Hecke correspondence $T(a)$, depending only on $KaK$. At fine level an integral representative of $a$ gives the universal $D$-linear isogeny

   $$
   p_2^*\mathcal A_K\longrightarrow p_1^*\mathcal A_K
   $$

   with kernel determined by $\widehat\Lambda/a\widehat\Lambda$; without an integral normalization there is a canonical universal quasi-isogeny.
7. Hecke correspondences route components by multiplication with $\nu(a)$, transpose by $a^{-1}$, and compose with the double-coset convolution multiplicities.
8. Level maps, Hecke spans, their convolution relations, and universal isogenies on fine curves or quotient stacks descend over their canonical component fields. The coarse span always descends; the universal isogeny descends to a coarse curve only when inertia is trivial.
9. In the quaternion division case the curves are smooth projective. The Hecke span acts on their Jacobians by $p_{2*}p_1^*$, convolution becomes composition, and $T(a^{-1})$ is the polarized adjoint of $T(a)$.
10. If $G$ maps centrally to a different basic quaternionic group with the same adjoint datum, the induced map of canonical curves is a separate finite comparison. The component map is computed through the two actual abelian quotients. Universal families and universal isogenies descend across that comparison exactly when its inertia acts trivially; the coarse Hecke span needs no such hypothesis.

**Proof.** The complex classification is Theorem 3.2. Chapter 4 proves the stabilizer, smoothness, and compactness assertions. Theorem 5.2 and Corollary 5.3 compute components, while Chapter 6 proves their canonical Galois descent. Chapter 7 gives the fine, stacky, and coarse comparisons. Chapters 8 and 9 construct the universal isogeny. Chapter 10 constructs the Hecke span, and Chapter 11 proves convolution, transpose, and the Jacobian action. Theorems 12.1 and 12.2 prove canonical descent. $\square$

### 13.2 Hypothesis ledger

| Assertion | Required hypothesis | What fails without it |
|---|---|---|
| PEL uniformization of the chosen $G$ | genuine PEL realization, including positivity and determinant law | endomorphisms and a pairing may cut out a larger Shimura variety |
| actual polarized abelian variety from $[h,g]$ | selected integral lattice and polarization type | the rational point gives only a polarization class up to isogeny |
| injectivity of the period map | the full finite adelic level coordinate | rational Hodge structures classify only up to quasi-isogeny |
| trivial stabilizers | neatness plus detection of the rational center, or full level at least three | central automorphisms can survive adjoint neatness |
| single-base-component formula (5.2) | rational transitivity on $\pi_0(X)$ | one must retain the orbit formula (5.2a) |
| abelianized component formula | simply connected derived group and strong approximation | a residual derived class set can remain |
| basic narrow norm formula | $G=\operatorname{Res}_{F/\mathbf Q}B^\times$ and the rational reduced-norm theorem | a central modification can have a different torus and finite correction |
| component over the ambient reflex field | stability under (6.3) | Galois can permute geometric components |
| ambient component reciprocity | a positive-at-infinity idele representative and the connected archimedean factor in (6.4) | a negative principal idele can falsely move a narrow component |
| universal family on a scheme | fine level | inertia obstructs coarse descent |
| quotient-stack presentation | nominal level group, including any ineffective kernel | replacing it by the effective image erases central inertia |
| honest universal isogeny | an integral representative of the adelic lattice modification | only a quasi-isogeny is canonical; scalar normalization changes degree |
| descent from a PEL central cover | trivial inertia on the complete universal diagram | equality of adjoint data descends the coarse curve, not the universal object |
| formula $K_a=K\cap aKa^{-1}$ | right translation $g\mapsto ga$ | the other intersection does not make $p_2$ well defined with this convention |
| projectivity | quaternionic adjoint group anisotropic over $\mathbf Q$ | rational parabolics produce cusps |
| action on Jacobians | smooth proper component curves | an open curve requires generalized Jacobians or compactification data |
| coarse universal isogeny | trivial inertia on source, target, and morphism | the coarse space forgets nontrivial fiber automorphisms |

### 13.3 Normalization checks and failure tests

Several short tests detect nearly every variance error in this theory.

First, the rational action and reciprocity act on the left, while Hecke translation acts on the right:

$$
r_h(s_f)(ga)=(r_h(s_f)g)a.
$$

If a proposed descent proof needs $r_h(s_f)$ to commute with $a$, its conventions have already gone wrong.

For ambient component reciprocity over a field with real places, the Artin representative must also be positive at infinity. A negative principal idele is trivial under global Artin reciprocity but need not lie in $T(\mathbf Q)^\dagger$ on a narrow label set. Omitting the connected archimedean factor from (6.4) therefore makes the stated component field depend on a representative.

Second, the intermediate group must satisfy $a^{-1}K_aa\subset K$. With $K_a=K\cap aKa^{-1}$ this is immediate. This check is more reliable than remembering one of two visually similar intersections.

Third, if $a\widehat\Lambda\subset\widehat\Lambda$, then $L_{ga}\subset L_g$, so the isogeny points from $A_{h,ga}$ to $A_{h,g}$. A formula pointing the other way has either reversed the inclusion or silently replaced $a$ by $a^{-1}$.

Fourth, a component label belongs first to the exact set $G(\mathbf Q)_+\backslash G(\mathbf A_f)/K$. It may be pushed to a torus only by Theorem 5.2. In the basic quaternionic group, the rational norm image incorporates both upper-half-plane orientation at split real places and positivity of Hamilton norms at ramified real places. In the one-split-place case the result is total positivity, not a one-sign quotient.

Fifth, $T(a)^t=T(a^{-1})$. On Jacobians this must agree with polarized adjunction. If the proposed transpose retains $a$ instead of $a^{-1}$, the two projections have not actually been exchanged.

Finally, existence of a coarse Hecke span does not imply existence of a coarse universal isogeny. The span is a relation between orbit spaces; the isogeny is a morphism between universal objects. Inertia is invisible to the first and decisive for the second.

### 13.4 Conclusion

The quaternionic Shimura curve is now one object rather than four parallel descriptions. A point $[h,g]$ combines a weight-$-1$ Hodge structure with the adelic lattice

$$
L_g=V(\mathbf Q)\cap g\widehat\Lambda.
$$

The Riemann bilinear relations turn these data into a polarized abelian variety, the PEL tensors recover its endomorphisms and determinant law, and the finite adelic coordinate upgrades a rational quasi-isogeny class to an integral moduli point. At fine level this gives the complex uniformization of the represented curve and identifies its universal family fiber by fiber.

Connectedness is controlled by a different quotient. Strong approximation removes the simply connected derived coordinate and leaves the actual abelianized adelic image. For the basic quaternionic group, reduced norm turns this into a narrow idele class quotient: orientation contributes positivity at the split real place, and the Hamilton norm contributes positivity at every ramified real place. Central modifications retain their own torus quotient and finite corrections. Canonical reciprocity acts on these labels, so the stabilizer of a label gives the exact abelian field over which that geometric component is defined.

Level has three honest forms. A fine curve represents PEL objects and carries a universal abelian scheme. A quotient stack retains that universal object together with its inertia, so its presentation uses the full nominal level group. A coarse curve retains only the orbit geometry and generally loses the family; its faithful geometric action is the effective quotient of that group. Keeping those two groups distinct prevents a rational central automorphism from disappearing between the stack and the coarse curve.

Finally, right translation by $a$ changes $L_g$ to the commensurable lattice $L_{ga}$. On the intermediate level $K\cap aKa^{-1}$ this produces a universal quasi-isogeny, and after an integral normalization it produces an honest isogeny with explicit finite kernel. Forgetting the intermediate structure in two ways gives the Hecke span. Fiber products give double-coset convolution, inversion gives transpose, and pull--norm gives the corresponding action and adjunction on Jacobians.

The arithmetic descent is governed by one elementary but decisive identity: reciprocity multiplies on the left and Hecke translation on the right. Their associativity descends level maps, component routing, finite spans, convolution relations, and universal isogenies to the reflex or component field. The resulting package is the precise generic foundation for later integral models, cohomological Hecke actions, and local--global compatibility.
