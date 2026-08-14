# Toroidal Compactifications of Hilbert--Blumenthal Moduli

## Contents

- [1. The boundary problem](#1-the-boundary-problem)
  - [1.1 Why a compactification is part of the moduli theory](#11-why-a-compactification-is-part-of-the-moduli-theory)
  - [1.2 Standing Hilbert--Blumenthal data](#12-standing-hilbert--blumenthal-data)
  - [1.3 The order of proof](#13-the-order-of-proof)
  - [1.4 Three distinctions that govern the book](#14-three-distinctions-that-govern-the-book)
- [2. Raynaud extensions and polarized one-motives](#2-raynaud-extensions-and-polarized-one-motives)
  - [2.1 The semiabelian identity component](#21-the-semiabelian-identity-component)
  - [2.2 The period lattice](#22-the-period-lattice)
  - [2.3 Polarization and the period pairing](#23-polarization-and-the-period-pairing)
  - [2.4 The Hilbert--Blumenthal rank dichotomy](#24-the-hilbert--blumenthal-rank-dichotomy)
  - [2.5 Integral and logarithmic one-motives](#25-integral-and-logarithmic-one-motives)
  - [2.6 The Tate and mixed-Raynaud examples](#26-the-tate-and-mixed-raynaud-examples)
- [3. Cusps, Fourier lattices, and monodromy cones](#3-cusps-fourier-lattices-and-monodromy-cones)
  - [3.1 Rational boundary components](#31-rational-boundary-components)
  - [3.2 Cusp labels](#32-cusp-labels)
  - [3.3 The Fourier lattice](#33-the-fourier-lattice)
  - [3.4 Positive monodromy](#34-positive-monodromy)
  - [3.5 Nonnormal fibers and normalized stars](#35-nonnormal-fibers-and-normalized-stars)
- [4. Admissible decompositions and projective regular refinement](#4-admissible-decompositions-and-projective-regular-refinement)
  - [4.1 Fans and admissibility](#41-fans-and-admissibility)
  - [4.2 Projective fans from convex hulls](#42-projective-fans-from-convex-hulls)
  - [4.3 Marked rays and finite symmetries](#43-marked-rays-and-finite-symmetries)
  - [4.4 Equivariant regularization](#44-equivariant-regularization)
  - [4.5 Periodic decompositions for the universal family](#45-periodic-decompositions-for-the-universal-family)
- [5. Complete fine saturated logarithmic test pairs](#5-complete-fine-saturated-logarithmic-test-pairs)
  - [5.1 Saturated monoids and their completions](#51-saturated-monoids-and-their-completions)
  - [5.2 Toroidal test pairs, including nilpotents](#52-toroidal-test-pairs-including-nilpotents)
  - [5.3 The logarithmic period map](#53-the-logarithmic-period-map)
  - [5.4 Face restriction and base change](#54-face-restriction-and-base-change)
- [6. The Mumford construction](#6-the-mumford-construction)
  - [6.1 The periodic polyhedral algebra](#61-the-periodic-polyhedral-algebra)
  - [6.2 Gluing and the period quotient](#62-gluing-and-the-period-quotient)
  - [6.3 Flatness, properness, and the group locus](#63-flatness-properness-and-the-group-locus)
  - [6.4 Endomorphisms, polarization, and level](#64-endomorphisms-polarization-and-level)
  - [6.5 The family theta line](#65-the-family-theta-line)
- [7. Infinitesimal recognition](#7-infinitesimal-recognition)
  - [7.1 The intrinsic logarithmic structure of a semiabelic model](#71-the-intrinsic-logarithmic-structure-of-a-semiabelic-model)
  - [7.2 Why the unenhanced assertion is false](#72-why-the-unenhanced-assertion-is-false)
  - [7.3 Square-zero monomial recognition](#73-square-zero-monomial-recognition)
  - [7.4 Splitting the unit cocycle](#74-splitting-the-unit-cocycle)
  - [7.5 Induction through nilpotent thickenings](#75-induction-through-nilpotent-thickenings)
- [8. The inverse theorem and completed deformation rings](#8-the-inverse-theorem-and-completed-deformation-rings)
  - [8.1 Extraction on normal reduced bases](#81-extraction-on-normal-reduced-bases)
  - [8.2 Full faithfulness](#82-full-faithfulness)
  - [8.3 Essential surjectivity](#83-essential-surjectivity)
  - [8.4 Completed local rings](#84-completed-local-rings)
  - [8.5 Traits and boundary-supported Artin rings](#85-traits-and-boundary-supported-artin-rings)
- [9. Paired frames and Kummer normalization](#9-paired-frames-and-kummer-normalization)
  - [9.1 Torsion of the boundary one-motive](#91-torsion-of-the-boundary-one-motive)
  - [9.2 The refined Fourier lattice](#92-the-refined-fourier-lattice)
  - [9.3 Normalization before completion](#93-normalization-before-completion)
  - [9.4 Smoothness and descent of framed branches](#94-smoothness-and-descent-of-framed-branches)
- [10. Bounded normalization and conductor presentations](#10-bounded-normalization-and-conductor-presentations)
  - [10.1 The conductor square](#101-the-conductor-square)
  - [10.2 Uniform theta embeddings](#102-uniform-theta-embeddings)
  - [10.3 Bounded Hilbert and graph data](#103-bounded-hilbert-and-graph-data)
  - [10.4 Pushouts and nonnormal fibers](#104-pushouts-and-nonnormal-fibers)
- [11. A finite-type algebraic cusp atlas](#11-a-finite-type-algebraic-cusp-atlas)
  - [11.1 Construction from explicit monoid algebras](#111-construction-from-explicit-monoid-algebras)
  - [11.2 Algebraizing the conductor pushout](#112-algebraizing-the-conductor-pushout)
  - [11.3 Proof of the fine saturated charts](#113-proof-of-the-fine-saturated-charts)
  - [11.4 Comparison with the complete Mumford family](#114-comparison-with-the-complete-mumford-family)
  - [11.5 Why Fitting ideals do not suffice](#115-why-fitting-ideals-do-not-suffice)
- [12. Ramified conductor descent](#12-ramified-conductor-descent)
  - [12.1 The tensor square of a ramified trait](#121-the-tensor-square-of-a-ramified-trait)
  - [12.2 The actual conductor factorization map](#122-the-actual-conductor-factorization-map)
  - [12.3 Descent through the reduced pushout](#123-descent-through-the-reduced-pushout)
  - [12.4 Lifting across the nilradical and the cocycle](#124-lifting-across-the-nilradical-and-the-cocycle)
  - [12.5 fpqc descent of all structures](#125-fpqc-descent-of-all-structures)
- [13. Overlap equivalence and algebraization](#13-overlap-equivalence-and-algebraization)
  - [13.1 Common faces and changes of cusp](#131-common-faces-and-changes-of-cusp)
  - [13.2 Exhaustion of isomorphisms](#132-exhaustion-of-isomorphisms)
  - [13.3 Separated gluing](#133-separated-gluing)
  - [13.4 Properness from complete fans](#134-properness-from-complete-fans)
- [14. Poincare, theta, and determinant lines](#14-poincare-theta-and-determinant-lines)
  - [14.1 Three different lines](#141-three-different-lines)
  - [14.2 The normalized semiabelic theta line](#142-the-normalized-semiabelic-theta-line)
  - [14.3 Determinant of cohomology](#143-determinant-of-cohomology)
  - [14.4 Boundary transition characters](#144-boundary-transition-characters)
  - [14.5 Base change and conductor compatibility](#145-base-change-and-conductor-compatibility)
- [15. Positivity and projective gluing](#15-positivity-and-projective-gluing)
  - [15.1 Horizontal positivity](#151-horizontal-positivity)
  - [15.2 Vertical fan positivity](#152-vertical-fan-positivity)
  - [15.3 Mixed curves and a uniform domination bound](#153-mixed-curves-and-a-uniform-domination-bound)
  - [15.4 Descent of the ample line](#154-descent-of-the-ample-line)
- [16. The toroidal compactification theorem](#16-the-toroidal-compactification-theorem)
  - [16.1 Construction and completed-local comparison](#161-construction-and-completed-local-comparison)
  - [16.2 Smoothness, boundary, and universal objects](#162-smoothness-boundary-and-universal-objects)
  - [16.3 Projectivity and descent](#163-projectivity-and-descent)
  - [16.4 Independence under refinement](#164-independence-under-refinement)
- [17. Finite-type joining and the integral connecting slice](#17-finite-type-joining-and-the-integral-connecting-slice)
  - [17.1 Joining a formal cusp to the good interior](#171-joining-a-formal-cusp-to-the-good-interior)
  - [17.2 The finite-type joining theorem](#172-the-finite-type-joining-theorem)
  - [17.3 Relative slicing with a dense good open](#173-relative-slicing-with-a-dense-good-open)
  - [17.4 The stable connecting-slice theorem](#174-the-stable-connecting-slice-theorem)
  - [17.5 The exported interface](#175-the-exported-interface)
- [18. Hostile mathematical review](#18-hostile-mathematical-review)
  - [18.1 Infinitesimal and logarithmic attacks](#181-infinitesimal-and-logarithmic-attacks)
  - [18.2 Normalization, conductor, and descent attacks](#182-normalization-conductor-and-descent-attacks)
  - [18.3 Positivity and joining attacks](#183-positivity-and-joining-attacks)
  - [18.4 Final theorem chain](#184-final-theorem-chain)

## 1. The boundary problem

### 1.1 Why a compactification is part of the moduli theory

The moduli scheme of polarized abelian varieties with real multiplication is naturally open. An abelian scheme over the fraction field of a discrete valuation ring can acquire a torus in its limiting identity component, and the missing limit is not an abelian scheme. Adding arbitrary projective boundary points would prove properness of a topological space but would forget the periods, polarizations, torsion frames, and deformation parameters that make the boundary useful. The required boundary must itself be modular.

For Hilbert--Blumenthal moduli the correct objects are polarized semiabelic degenerations. Their smooth group loci are semiabelian schemes, their proper fibers are assembled from toric varieties, and their generic fibers are abelian varieties with the prescribed real multiplication. A fan records which positive period valuations are allowed in a chart. A periodic polyhedral decomposition records a projective model of the universal family over that chart. These are related constructions, but they are not the same: the first compactifies the moduli base, while the second compactifies the fibers of the universal semiabelian quotient.

This book constructs the two simultaneously. The proof must address phenomena invisible on normal traits. A geometric boundary fiber can be reducible and nonnormal. A test ring can contain nilpotents. A paired torsion frame can ramify at the boundary even when it is finite etale on the abelian locus. A splitting extension of a trait can be ramified, so its self-product is not a disjoint union of Galois graphs. Finally, a strictly convex function on a fan produces a line on the toric base, not the theta line on the universal semiabelic family. Each distinction will be preserved until the objects are compared by an actual theorem.

### 1.2 Standing Hilbert--Blumenthal data

Let $F$ be a totally real field of degree $d$, with ring of integers $\mathcal O_F$ and different $\mathfrak d_F$. Let $S_0$ be a regular excellent noetherian base on which the discriminant of $F$, the polarization degree, and a neat integer $N\geq3$ are invertible. Fix an invertible fractional ideal $I$ and put

$$
I^\dagger=\mathfrak d_F^{-1}I^{-1},
\qquad
\mathfrak c=\mathfrak d_F^{-1}I^{-2}.
\tag{1.1}
$$

The fine interior $H/S_0$ classifies abelian schemes $A$ of relative dimension $d$, an action

$$
\iota:\mathcal O_F\longrightarrow\operatorname{End}(A),
$$

the Hilbert determinant condition, an ordered $\mathfrak c$-polarization, and a neat prime-to-the-base level. The corrected level may be the cyclotomic-split source

$$
(I/NI)\oplus(I/NI)(1),
\tag{1.2}
$$

or an elliptic-source form with the same geometric lattice. Both are finite etale over $S_0$ and become the same fixed-pairing principal level after a finite etale coefficient extension.

We also allow finitely many paired frame levels at ideals $\mathfrak r$ invertible on $S_0$. On the interior they form a finite etale cover $Y\to H$. A frame includes its determinant-line isomorphism. Forgetting that isomorphism changes the twisting group and can change geometric connectedness.

All compactifications below are relative to a chosen finite union of geometric components stable under the coefficient descent action. Neatness removes stabilizers on the interior. At a cusp it will also remove stabilizers of nonzero cones after an equivariant subdivision.

### 1.3 The order of proof

The construction is deliberately linear.

First we extract Raynaud extensions and polarized one-motives from degenerating abelian varieties. We then define cusp and cone data and construct admissible regular projective fans. Next we build Mumford families over complete fine saturated logarithmic toroidal test pairs.

The inverse direction comes before algebraization. We recover the intrinsic logarithmic structure of a labelled semiabelic family, prove the square-zero recognition theorem, and deduce an equivalence with positive logarithmic one-motives on nilpotent as well as reduced tests. This determines completed deformation rings.

Only after that equivalence do we normalize for paired frames, bound normalization and conductor presentations, construct an explicit finite-type algebraic cusp atlas, and prove ramified conductor descent. Algebraic overlaps then glue the cusp atlas to the interior.

The line-bundle argument comes after effectivity. We construct the theta line on the universal family, its determinant of cohomology on the moduli base, and the separate fan line on the base. Horizontal, vertical, and mixed positivity make a common tensor combination ample. Projective toroidal gluing follows.

Finally we pass from a completed cusp branch to a finite-type projective model containing the good interior and cut a stable relative curve with a dense good special-fiber open. Thus no joining or slicing statement is used to prove the compactification on which it depends.

### 1.4 Three distinctions that govern the book

The first distinction is between an underlying degeneration and a logarithmically compatible degeneration. Over $k[\epsilon]/(\epsilon^2)$ the equation $XY=\epsilon$ is a flat smoothing of $XY=0$. It is a genuine underlying deformation. It is not a deformation over a fixed log chart whose smoothing generator maps to zero. A correct infinitesimal theorem must say this, not deny the existence of the smoothing.

The second distinction is between normal charts and nonnormal fibers. The monoid algebra of a saturated cone is normal. A periodic semiabelic fiber obtained by identifying faces of several toric pieces can be reducible and nonnormal. Its normalization and conductor are part of the moduli presentation, and all group and polarization maps must descend through their pushout.

The third distinction is between three line bundles. The fan support function defines a line on a toric chart of the moduli base. The Poincare biextension defines a theta line on the universal semiabelic family. Taking determinant of cohomology produces a line back on the moduli base. Confusing any two of these makes the positivity argument circular.

We fix the meaning of a semiabelic object. It is a tuple $(P,G,\mu,\Theta)$ in which $P$ is proper and flat with geometrically connected fibers, $G$ is a semiabelian scheme, $\mu:G\times P\to P$ is an action with a dense torsor orbit in every geometric fiber, and $\Theta$ is a relatively ample line with a cubical action linearization. The stabilizer of a point is a subtorus determined by the face containing its orbit. The reduction of a geometric fiber is seminormal, but it may be reducible and nonnormal. The PEL endomorphisms, polarization, and level act on the whole tuple, not only on $G$.

Over a nonreduced base the special-fiber normalization does not itself lift by taking integral closure. Instead a labelled semiabelic object includes the finite normalized-star cover and its conductor equivalence relation, flatly lifted from the reduction. Chapter 7 proves that over a fixed intrinsic log chart such a lift is determined by a one-motive. This is the category represented near the toroidal boundary.

Two tempting replacements fail. Keeping only $G$ forgets which proper orbit compactification and which ample line were chosen. Keeping only $P$ forgets the group law and cannot recover the period lattice functorially. The tuple, its normalized stars, and its conductor maps are the minimum data stable under degeneration and descent.

## 2. Raynaud extensions and polarized one-motives

### 2.1 The semiabelian identity component

Let $V$ be a complete excellent DVR with fraction field $K$. Suppose a polarized abelian variety $A/K$ has semistable reduction. The formal identity component of a semistable model has a canonical algebraic covering group $G$ fitting into

$$
0\longrightarrow T\longrightarrow G\longrightarrow B\longrightarrow0,
\tag{2.1}
$$

where $T/V$ is a torus and $B/V$ is an abelian scheme. This is the Raynaud extension. Here is the construction. The maximal connected affine subgroup of the special-fiber identity component is a torus after a semistable splitting extension. Smooth lifting gives a formal torus in the completion of the identity component. The quotient formal group is proper and smooth; an ample symmetric line algebraizes it to an abelian scheme $B$. The original formal group is then an extension of $B$ by the torus. The same homogeneous coordinates that algebraize $B$ algebraize the extension and its multiplication, and faithfully flat descent removes the splitting extension.

The extension can be described character by character. Pushing (2.1) out by $x\in X=X^*(T)$ gives a $\mathbf G_m$-extension of $B$. A rigidified $\mathbf G_m$-extension is the complement of the zero section in a line algebraically equivalent to zero: multiplication is exactly the biextension law. Hence it is a point $c(x)\in B^\vee(V)$. Addition of characters corresponds to tensor product of lines, so (2.1) is classified by a homomorphism

$$
c:X\longrightarrow B^\vee.
\tag{2.2}
$$

The construction is intrinsic. A homomorphism of semistable abelian varieties preserves the maximal affine subgroup of the identity component, hence acts on $T$, $G$, and $B$. It commutes with finite extension of complete traits and with Galois descent.

Uniqueness deserves emphasis. A second extension giving the same completed identity component agrees with the first on every infinitesimal neighborhood of the zero section. Translation covers $B$ by such neighborhoods, and separatedness makes the local identifications agree. Thus $G$ is recovered from the degeneration before a fan is selected.

For later tests over higher-dimensional bases, a Raynaud extension means (2.1) with $T$ a torus, $B$ an abelian scheme, and $c$ as in (2.2), all compatible with the PEL action. Over a complete local base the same definition is made level by level and algebraized by the ample-line theorem once the compatible polarization line is present.

### 2.2 The period lattice

The analytic generic fiber $G_K^{\mathrm{an}}$ contains a discrete lattice $Y$ of rank $\operatorname{rank}T$ and

$$
0\longrightarrow Y\xrightarrow{u}G_K^{\mathrm{an}}
\longrightarrow A_K^{\mathrm{an}}\longrightarrow0.
\tag{2.3}
$$

Discreteness means finite intersection with every quasi-compact analytic domain. Properness of the quotient is equivalent to fullness of the tropical map

$$
Y\longrightarrow\operatorname{Hom}(X,\mathbf Z),
\qquad
y\longmapsto\bigl(x\mapsto v(x(u(y)))\bigr).
\tag{2.4}
$$

Indeed, if the real span is not full, a nonzero linear functional constant on its image gives an unbounded annular direction in the quotient. Conversely, when the image is full, a bounded fundamental parallelotope meets every orbit, so the quotient satisfies the valuative criterion. This is the properness calculation behind the one-motive.

The pair

$$
M=[Y\xrightarrow{u}G]
\tag{2.5}
$$

is the Raynaud one-motive. Here $u$ is analytic on the generic fiber and logarithmic on a boundary base. Its torsion away from the residue characteristic has two exact sequences

$$
0\longrightarrow G[n]\longrightarrow M[n]\longrightarrow Y/nY\longrightarrow0,
\tag{2.6}
$$

and

$$
0\longrightarrow T[n]\longrightarrow G[n]\longrightarrow B[n]\longrightarrow0.
\tag{2.7}
$$

These expose the toric line selected by a paired frame and the division periods adjoined at a cusp.

We indicate how $Y$ is recovered without choosing analytic coordinates. Pull a sufficiently high symmetric theta line from $A$ to $G_K$. Its nonzero theta functions have translates whose ratios are characters on the torus. Two points of $G_K$ have the same image in $A_K$ precisely when every such ratio takes the same value; their differences form $Y$. Multiplication on $A$ makes it a subgroup, properness makes it discrete, and comparison of dimensions makes its rank equal to that of $T$. The valuation of a character on a difference gives (2.4). This description is invariant under all endomorphisms and hence recovers the $\mathcal O_F$-action on $Y$.

Conversely, suppose (2.1), a full lattice $Y$, and a positive period pairing are given. Choose a bounded fundamental parallelotope for (2.4). The theta series obtained by summing a character over $Y$ converges on it because the quadratic valuation tends to $+\infty$. Finitely many such series embed the quotient locally, their automorphy factors glue, and the bounded parallelotope proves properness. The resulting proper analytic group has an ample line and is algebraic: take the graded ring of theta sections, which is finite in each degree and generated in bounded degree by convexity, and recover the group as its Proj. Thus polarized Raynaud one-motives and semistable polarized abelian varieties over $K$ are inverse descriptions.

### 2.3 Polarization and the period pairing

A polarization supplies a homomorphism $\lambda_B:B\to B^\vee$, a lattice map

$$
\phi:Y\longrightarrow X,
\tag{2.8}
$$

and a trivialization of the pullback of the Poincare biextension along $Y\times X$. Evaluating it gives a multiplicative period pairing

$$
b:Y\times Y\longrightarrow K^\times,
\qquad
b(y,y')=\phi(y')(u(y)).
\tag{2.9}
$$

The polarization identities make $b$ symmetric. Its valuation

$$
q(y,y')=v(b(y,y'))
\tag{2.10}
$$

is positive definite. Symmetry alone would not be enough: the quotient of a torus by a full lattice can be proper analytically while a nonpositive descent line fails to be ample. Positivity is exactly what makes the theta series converge and its line relatively ample.

The quadratic form also detects the degeneration rank. If it has a kernel, the corresponding annular direction survives in the quotient and the theta line has degree zero on its orbit closure. If it has a negative direction, the purported theta series has terms of unbounded negative valuation. These are not defects removable by choosing another decomposition; they violate properness and ampleness at the one-motive level.

For a principal polarization, $\lambda_B$ and $\phi$ are isomorphisms. For an ordered $\mathfrak c$-polarization, the same statement is tensor-perfect after inserting $\mathfrak c$; in the totally toric Hilbert case it is the identity

$$
I\mathfrak c=I^\dagger.
\tag{2.11}
$$

### 2.4 The Hilbert--Blumenthal rank dichotomy

The real multiplication action preserves (2.1) and (2.3). Hence $X_*(T)_\mathbf Q$ and $Y_\mathbf Q$ are unital $F$-modules. If the toric rank is nonzero, their $\mathbf Q$-dimension is at least $[F:\mathbf Q]=d$. Since the toric rank is at most $\dim A=d$, it equals $d$. The abelian quotient $B$ then has dimension zero.

**Theorem 2.1 (Hilbert boundary dichotomy).** A semistable Hilbert--Blumenthal abelian variety of dimension $d$ either has good reduction or is totally toric. In the latter case its Raynaud datum is a positive one-motive

$$
[I_b\xrightarrow{u}T_b],
\tag{2.12}
$$

where $I_b$ is a projective rank-one $\mathcal O_F$-lattice and

$$
T_b=\underline{\operatorname{Hom}}_\mathbf Z(I_b^\dagger,\mathbf G_m).
\tag{2.13}
$$

**Proof.** Functoriality of the maximal torus gives the $F$-module structure. The dimension argument proves the dichotomy. In the nonzero case $B=0$, while the PEL lattice and ordered polarization identify $Y$ with an invertible ideal $I_b$ and $X^*(T_b)$ with its trace dual. The period pairing is balanced because every element of $\mathcal O_F$ is adjoint to itself for the Hilbert polarization. Positivity is inherited from the polarization of $A$. $\square$

This theorem is why Hilbert cusps have no positive-dimensional abelian base. We retain the general Raynaud notation because it clarifies the Poincare and determinant constructions and extends verbatim to other PEL data.

The argument is stable under ramified base change. Toric rank may become split only after extension, but its character space over $\mathbf Q$ still has an $F$-action and therefore has dimension divisible by $d$. Descent of the conclusion follows because the condition $B=0$ is geometric. Thus no hidden mixed Raynaud stratum appears after passing back to the original trait.

### 2.5 Integral and logarithmic one-motives

Let $(S,M_S)$ be a fine saturated logarithmic scheme. Write $\overline M_S=M_S/\mathcal O_S^\times$ and $M_S^{\mathrm{gp}}$ for groupification. A logarithmic period map for (2.12) is an $\mathcal O_F$-balanced homomorphism

$$
u:I_b\longrightarrow
\underline{\operatorname{Hom}}
(I_b^\dagger,M_S^{\mathrm{gp}}),
\tag{2.14}
$$

such that the order pairing

$$
(a,x)\longmapsto\overline{x(u(a))}
\tag{2.15}
$$

is symmetric after the polarization identification and lies in the selected positive cone. Its image in $\mathcal O_S$ on the locus where all boundary generators are invertible is the ordinary period map.

The unit part matters. Two periods can have the same order in $\overline M_S^{\mathrm{gp}}$ and different Kummer classes. Thus the one-motive consists of the monomial order and its leading unit, not just a monodromy homomorphism.

An integral one-motive over a complete toroidal pair is a compatible system over all nilpotent quotients. The torus and the two projective lattices lift uniquely. The deformation variables are precisely the monomial maps and their unit parts. This observation will give the completed monoid ring, but only after the inverse theorem proves that every logarithmically compatible PEL degeneration is of this form.

Morphisms are equally concrete. A morphism from $[Y_1\to G_1]$ to $[Y_2\to G_2]$ is a pair of homomorphisms on lattices and semiabelian schemes whose square with the period maps commutes in $M_S^{\mathrm{gp}}$. A polarized morphism also commutes with the duality maps and biextension trivializations. Since the lattices are locally constant and the semiabelian schemes are separated, an equality of such morphisms on a schematically dense open extends uniquely. The nilpotent analogue will follow from the weight calculation in Chapter 7.

### 2.6 The Tate and mixed-Raynaud examples

For the Tate curve the datum is

$$
[\mathbf Z\xrightarrow{1\mapsto q}\mathbf G_m].
\tag{2.16}
$$

The pairing is $b(m,n)=q^{mn}$ and its order is $v(q)mn$. The $n$-torsion sequence is

$$
0\longrightarrow\mu_n\longrightarrow E_q[n]
\longrightarrow\mathbf Z/n\mathbf Z\longrightarrow0.
\tag{2.17}
$$

Tensoring (2.16) with $I$ gives the tensor Hilbert cusp and the Fourier exponents $ax\in II^\dagger=\mathfrak d_F^{-1}$.

The standard $n$-gon illustrates what the one-motive remembers. If $v(q)=n$, a regular decomposition of the real line with vertices at the integers gives $n$ projective-line components modulo translation by $n$. Replacing $q$ by $uq$ with $u\in V^\times$ leaves the polygon and its dual graph unchanged but changes the gluing coordinate at the conductor. Thus the valuation form determines the combinatorics, while the unit period determines the actual semiabelic family.

In a general PEL problem with $B\ne0$, the extension class $c:X\to B^\vee$ and its dual $c^t:Y\to B$ are additional data. The Poincare biextension evaluated on $c^t\times c$ supplies the non-toric part of (2.9). Ignoring it produces the correct fan but the wrong theta automorphy factors. This mixed example anticipates why the family theta line cannot be replaced by the fan line.

## 3. Cusps, Fourier lattices, and monodromy cones

### 3.1 Rational boundary components

Fix the rational PEL module $L=I\oplus I$ with alternating form valued in $I^2$. A rational boundary component is determined by an isotropic $F$-line $W\subset L\otimes\mathbf Q$. Its stabilizer is a parabolic subgroup. The unipotent center is the vector group of symmetric $F$-balanced maps from the quotient lattice to $W$, and its character lattice is the Fourier lattice used below.

In rank two every isotropic $F$-line is maximal. Choosing one amounts to choosing the toric weight filtration

$$
0\subset W\subset W^\perp=L\otimes\mathbf Q.
\tag{3.1}
$$

The prime-to-the-base Tate module of a totally degenerate one-motive has the same filtration. It is intrinsic, so an isomorphism between two punctured degenerations must carry one cusp line to the other.

### 3.2 Cusp labels

A cusp label $b$ contains more than $W$. It records:

1. integral period and character lattices $I_b$ and $I_b^\dagger$;
2. the ordered polarization identification;
3. the corrected neat-level label;
4. the arithmetic component label; and
5. for each paired frame, the isotropic line mapped to the toric part of torsion and a complementary division lift.

There are finitely many cusp labels modulo the arithmetic group. The ideal data range through a narrow class group, and all remaining choices lie in finite level quotients. Let $\Gamma_b$ be the stabilizer after unipotent translations have been absorbed into the Fourier lattice. Its infinite part is a finite-index subgroup of the totally positive units.

Changes of label act on all lattices, cones, period maps, and theta factors. A construction made at one cusp descends only when it is compatible with these actions.

The stabilizer has a transparent matrix form. After choosing a splitting of the isotropic filtration, an element is

$$
\begin{pmatrix}a&b\\0&a^{-1}\end{pmatrix},
\tag{3.1a}
$$

where $a$ preserves the cusp ideal and $b$ lies in the integral unipotent lattice. The variable $b$ translates the Fourier torus and is absorbed into its character lattice; $a$ acts by a totally positive unit on the monodromy cone. This explains why admissibility is taken modulo $\Gamma_b$ rather than requiring a finite fan in the cone itself.

### 3.3 The Fourier lattice

For the unframed cusp define

$$
\mathfrak M_b^0=I_bI_b^\dagger
\tag{3.2}
$$

after inserting the denominators required by the corrected $N$-level. A character is written $Q^\xi$, $\xi\in\mathfrak M_b^0$. The universal period formula is

$$
x(u(a))=Q^{ax}.
\tag{3.3}
$$

Let

$$
N_b^0=\operatorname{Hom}(\mathfrak M_b^0,\mathbf Z).
\tag{3.4}
$$

A valuation of the periods is a point of $N_b^0\otimes\mathbf R$. The integral lattice depends on level. Replacing it by the coarser lattice before adding division periods can make a cone appear regular although the framed normalization is singular. Chapter 9 will compute the refined lattice before regularity is asserted.

The trace pairing realizes the duality explicitly. If $a\in I_b$ and $x\in I_b^\dagger$, then the exponent $ax$ is characterized by

$$
\langle \nu,ax\rangle
=v\bigl(x(u(a))\bigr).
\tag{3.4a}
$$

Balancedness under $r\in\mathcal O_F$ says that the right side is unchanged when $(a,x)$ is replaced by $(ra,x)$ or $(a,rx)$. Thus the Fourier lattice is exactly the lattice on which all integral period orders are linear.

### 3.4 Positive monodromy

The monodromy cone $C_b$ is the open cone of homomorphisms

$$
\nu:\mathfrak M_b^0\longrightarrow\mathbf R
\tag{3.5}
$$

for which the associated symmetric form on $I_b\otimes\mathbf R$ is positive definite. Its rational closure includes positive semidefinite boundary forms. In the Hilbert case trace duality identifies it with the totally positive cone in $F\otimes\mathbf R$.

The cone condition has two roles. It makes the analytic period quotient proper, and it makes the theta automorphy factor ample on the periodic family. A fan in a larger ambient vector space would add charts whose generic periods do not define polarized abelian varieties.

Faces of the closed cone correspond to partial vanishing of monodromy. In the Hilbert rank-two situation, real multiplication forces a nonzero geometric trait pairing to be positive in all embeddings, so a trait lands either at the origin or in the open cone. Higher-dimensional base points may lie on a rational face because some boundary monomials become units after localization. The face records the logarithmic stratum, not a forbidden intermediate toric rank on a geometric trait.

The tensor ray is generated by

$$
\nu_{\mathrm{ten}}(\xi)=\operatorname{Tr}_{F/\mathbf Q}(\xi).
\tag{3.6}
$$

It must be a ray of the fan, not necessarily the interior of a maximal regular cone. In degree greater than one the latter requirement can be impossible: if totally positive integral basis vectors expressed $1$ as a strictly positive integral combination, each would have all real embeddings between zero and one, contradicting integrality of its positive norm.

For a real quadratic field, write $F\otimes\mathbf R\simeq\mathbf R^2$. The cone is the first quadrant, but the positive unit group acts by $(x_1,x_2)\mapsto(ux_1,u^{-1}x_2)$. Taking logarithms of the ratio $x_1/x_2$ turns this into translation by a lattice. A compact interval is therefore a fundamental set for directions. This is the elementary picture behind finite fan orbit statements: infinitely many rational rays occur, but only finitely many meet a fixed logarithmic strip after the convex-hull decomposition.

### 3.5 Nonnormal fibers and normalized stars

A periodic polyhedral decomposition of $I_b\otimes\mathbf R$ gives toric pieces indexed by cells. Their face identifications can create a reducible seminormal fiber. Around a cell $\tau$, the invariant affine star has a normalization

$$
\operatorname{Spec}R[P_\tau],
\tag{3.7}
$$

where $P_\tau$ is a fine saturated monoid. Two normalized stars meet along unions of face schemes. The original star is their conductor pushout.

We therefore impose normality on the base monoid chart and on normalized stars, not on the semiabelic fiber. The conductor records the double locus. Its two maps are part of the presentation. This permits nodal polygons, cycles of toric varieties, and higher-dimensional stable toric fibers without falsely declaring them normal.

For the one-dimensional Tate model, the normalized special fiber of an $n$-gon is a disjoint union of $n$ copies of $\mathbf P^1$, while the conductor consists of the pairs $0,\infty$ that are glued cyclically. The fiber is seminormal and nonnormal. The same normalization--conductor description persists in every periodic cell quotient.

## 4. Admissible decompositions and projective regular refinement

### 4.1 Fans and admissibility

A fan $\Sigma_b$ is **admissible** if it is a locally finite rational polyhedral decomposition of $C_b\cup\{0\}$, is stable under $\Gamma_b$, and has finitely many $\Gamma_b$-orbits. A collection $(\Sigma_b)_b$ is admissible for descent if every change of cusp and every finite coefficient or frame symmetry transports one fan to the corresponding fan.

It is **regular** for a lattice $N$ if the primitive generators of every cone extend to a basis of $N$. It is **projective** if it admits an invariant integral strictly convex piecewise-linear support function. Regularity gives smooth monoid charts. Projectivity gives a base fan line. Neither condition implies the other.

Local finiteness and finite orbit type are independent requirements. Infinitely many translates of one cone may accumulate at an interior ray if local finiteness is omitted, producing a nonnoetherian quotient chart. A finite decomposition of one chosen fundamental sector may fail to match on its two unit-translated sides, producing no group action. Admissibility rules out both defects. Completeness means that the union is the whole closed positive cone; without it a valuation ray outside the union gives a punctured trait with no extension.

### 4.2 Projective fans from convex hulls

Let $N$ be any cusp cocharacter lattice and let $C$ be its positive cone. Form the closed convex hull

$$
\Pi=\operatorname{conv}(N\cap C).
\tag{4.1}
$$

Every positive ray meets the boundary of $\Pi$ nearest the origin. To see this, move its logarithmic direction into a compact fundamental set for the totally positive unit lattice. For a uniformly large scalar, the lattice parallelotope containing the point has all vertices in $C$, so the point lies in $\Pi$. A positive rational functional has a positive minimum on $N\cap C$, giving a lower radial bound.

Cone from the origin over the nearest faces of $\Pi$. These cones cover $C\cup\{0\}$ and meet along faces. Local finiteness follows because only finitely many lattice points occur below a fixed positive functional on a compact set of logarithmic directions. The same compactness proves that there are finitely many $\Gamma_b$-orbits of faces.

On a cone over a face contained in $\ell=1$, define $h=\ell$. The pieces agree, and the radial convexity of $\Pi$ makes $h$ strictly convex across distinct maximal cones. Clearing the finitely many denominators modulo $\Gamma_b$ makes $h$ integral. We have proved:

**Proposition 4.1.** Every Hilbert cusp cone admits a $\Gamma_b$-admissible projective rational polyhedral decomposition.

### 4.3 Marked rays and finite symmetries

Let $\Delta$ be the finite group generated by coefficient descent and the deck groups of all paired frame covers. Apply the convex-hull construction simultaneously to every $\Delta$-orbit of cusp data. The construction is intrinsic in $N\cap C$, so it is transported by $\Delta$.

There are only finitely many prescribed valuation rays modulo $\Gamma_b\rtimes\Delta$. Star-subdivide along the whole orbit of each ray. On a compact logarithmic fundamental set only finitely many members occur. Adding the transported rational tent functions makes the common refinement projective. Thus all chosen tensor or local valuation rays become one-dimensional cones.

Before resolving singularities, take the barycentric subdivision. A cone of this subdivision is a chain of faces with distinct dimensions. An element stabilizing the cone fixes every member of the chain and hence every ray. Thus the action has no inversions. This fact makes later orbitwise star subdivisions commute.

### 4.4 Equivariant regularization

For a simplicial cone $\sigma$ with primitive rays $e_1,\ldots,e_s$, define

$$
\mu(\sigma)=
[N\cap\operatorname{span}_\mathbf R(\sigma):
\mathbf Ze_1+\cdots+\mathbf Ze_s].
\tag{4.2}
$$

If $\mu(\sigma)>1$, choose a nonzero lattice point $w$ in the half-open fundamental parallelepiped and let $\tau$ be the smallest face containing its ray. Write

$$
w=\sum_{i\in I}a_ie_i,
\qquad 0<a_i<1.
\tag{4.3}
$$

Star subdivision at the primitive ray of $w$ replaces $\sigma$ by cones of multiplicity $a_im$, positive integers strictly smaller than $m$. Equivariance needs more than subdividing the orbit in an arbitrary order. Take every translate of the pair $(\tau,w)$, give the orbit one common height below the old support function, and take the lower convex subdivision. On a cone meeting several translates this is the common refinement of their star subdivisions. Its restriction to each translate of $\sigma$ contains only cones obtained by repeated insertion of lattice points from fundamental parallelepipeds.

For completeness, use the lexicographically ordered termination tuple

$$
(d,m_d,n_d,m_{d-1},n_{d-1},\ldots,m_2,n_2),
\tag{4.4}
$$

where $m_r$ is the largest multiplicity of an $r$-dimensional cone and $n_r$ is the number of its orbits. Choose $w$ first in the smallest face of a fundamental parallelepiped for which this tuple is maximal. The determinant calculation lowers the multiplicity of every affected maximal cone. New proper faces either already occurred or have smaller dimension, so their entries occur later in (4.4). Taking the common coherent orbit refinement cannot increase an earlier entry because each new cone is contained in one of the determinant-lowered cones. Thus the tuple decreases. It consists of nonnegative integers, and the process terminates with multiplicity one in every dimension.

The lower-height construction proves projectivity at every stage: add to the old support function a sufficiently small invariant rational convex function whose bend locus is the new orbit of rays. Finitely many inequalities modulo the group allow one common positive size. Clearing denominators at the end restores an integral strictly convex support function.

If an element of the neat cusp group stabilizes a nonzero regular cone, it fixes a primitive ray. Its infinite part is multiplication by a totally positive unit, and fixing one nonzero element forces that unit to be $1$. Its finite part is killed by neatness. Hence every nonzero cone has trivial stabilizer.

**Theorem 4.2 (simultaneous regular projective refinement).** For the finitely many cusp labels, refined level lattices, finite descent symmetries, and marked valuation rays, there is an equivariant admissible fan collection which is regular, projective, has trivial stabilizers on nonzero cones, and contains every marked ray.

### 4.5 Periodic decompositions for the universal family

The fan controls the base; a second decomposition controls the family. Fix a positive form in one cone. The lower faces of its rational quadratic function give an $I_b$-periodic rational polyhedral decomposition of $I_b\otimes\mathbf R$. A generic periodic rational perturbation gives a coherent triangulation. There are finitely many cell orbits.

Concretely, choose a rational positive quadratic function $Q$ and a small periodic rational function $\eta$ on the lattice. Lift every $x\in I_b$ to

$$
(x,Q(x)+\eta(x))\in I_b\otimes\mathbf R\times\mathbf R.
\tag{4.5}
$$

Project the lower faces of their convex hull. Translation by $y\in I_b$ changes $Q(x)$ by an affine function of $x$, so it preserves the projected decomposition. A generic choice of the finitely many values of $\eta$ modulo a period makes every lower face a simplex. The lower convex envelope is the support function $\varphi$ used in Chapter 6.

As the monodromy form varies, a finite set of lattice points becomes coplanar precisely on a rational linear wall. On a compact set of logarithmic directions, positivity bounds the diameter of a lower cell, so only finitely many lattice configurations and walls occur. This proves the finite-wall assertion used in the next paragraph; it is not an appeal to an infinite generic triangulation chosen independently at every base point.

Strict convexity of the perturbed support function is a finite collection of strict rational linear inequalities modulo $I_b$. It therefore persists on a rational neighborhood of the chosen form. Compactness of the logarithmic quotient supplies finitely many such neighborhoods modulo $\Gamma_b$. Refine the base fan by their walls and transport the decompositions under $\Delta$. On common faces take common coherent refinements. Later regular subdivisions only restrict an already chosen decomposition.

Thus each nonzero cone carries a compatible periodic decomposition whose polarization support function remains strictly convex for every monodromy form in that cone. This compatibility is the datum needed to glue the Mumford family across base faces.

## 5. Complete fine saturated logarithmic test pairs

### 5.1 Saturated monoids and their completions

Let $\sigma\subset N_\mathbf R$ be a rational polyhedral cone in a regular admissible fan and put

$$
P_\sigma=\sigma^\vee\cap M,
\qquad
M=\operatorname{Hom}(N,\mathbf Z).
\tag{5.1}
$$

The monoid $P_\sigma$ is finitely generated by Gordan's argument: intersect the cone with a rational affine hyperplane meeting all its rays, triangulate that compact rational polytope, and reduce every lattice point modulo the finitely many fundamental parallelepipeds. It is integral because it lies in a lattice. It is saturated because $nu\in P_\sigma$ for $n>0$ implies $u\in\sigma^\vee$, while $u\in M$ by hypothesis. Its group completion is the subgroup of $M$ generated by $P_\sigma$; after quotienting the lineality face this is the expected character lattice.

For a coefficient ring $S$, write

$$
S[P_\sigma]=\bigoplus_{p\in P_\sigma}S\,q^p,
\qquad
J_\sigma=(q^p:p\ne0),
\tag{5.2}
$$

and let $S[[P_\sigma]]$ denote the $J_\sigma$-adic completion. If $\sigma$ has a face $\tau$, restriction to the corresponding toric open inverts $q^p$ for $p\in P_\sigma\cap\tau^\perp$. The resulting monoid is

$$
P_{\sigma,\tau}=P_\sigma+(P_\sigma\cap\tau^\perp)^{\mathrm{gp}}.
\tag{5.3}
$$

Localization preserves integrality and saturation. Consequently every fan chart, every face overlap, and every completion along a toric stratum carries an fs logarithmic structure. The adjective fs will always mean fine and saturated.

Regularity of $\sigma$ gives more. If its primitive generators extend to a basis of $N$, then, after splitting the units of the face,

$$
S[P_{\sigma,\tau}]\simeq
S[t_1,\ldots,t_r,t_{r+1}^{\pm1},\ldots,t_d^{\pm1}].
\tag{5.4}
$$

Thus the toroidal boundary is locally a relative normal-crossings divisor whenever the coefficient base is regular. This conclusion comes from the monoid, not from a posterior examination of its boundary ideal.

Two basic charts will recur. For $P=\mathbf N$, the base is the completed disc $S[[q]]$ and the boundary is $q=0$. For $P=\mathbf N^2$, the base is $S[[q_1,q_2]]$ and the codimension-two stratum is $q_1=q_2=0$. A map to $k[\epsilon]/(\epsilon^2)$ may send $q_1$ to $\epsilon$ and $q_2$ to zero. This is a legitimate logarithmic deformation with one first-order smoothing direction; it is different from the strict boundary fiber in which both generators map to zero.

The log structure associated with a chart $P\to A$ is the sheafification of

$$
P\oplus_{\alpha^{-1}(A^\times)}A^\times\longrightarrow A.
\tag{5.4a}
$$

Its characteristic at a geometric point is $P$ modulo the face mapping to units there. Thus face localization is not a change of convention: it is the actual characteristic monoid seen on the corresponding stratum.

### 5.2 Toroidal test pairs, including nilpotents

A complete toroidal test pair over $S[P_\sigma]$ consists of a complete noetherian $S[P_\sigma]$-algebra $A$, an ideal of definition $I\subset A$, and the pullback logarithmic structure $M_A$, subject to the following conditions.

1. The image of $J_\sigma$ lies in $I$, and $A\simeq\varprojlim A/I^n$.
2. The reduced ring $A_{\mathrm{red}}$ is excellent and its normalization is finite.
3. On every irreducible component not contained in the boundary, the generic point lies in the locus where all nonzero $q^p$ are invertible.
4. The map $P_\sigma\to A$ is part of the data and all morphisms of test pairs are strict for the associated logarithmic structures.

Nilpotents are permitted. In particular $A$ may be an Artin ring supported entirely on the boundary, in which case there need be no ordinary dense generic fiber. This is essential: a completed moduli problem is determined by its values on nilpotent thickenings, not just on traits whose generic points are abelian.

When $A$ is reduced and normal, the values of a rational function are detected by height-one valuations:

$$
A=\bigcap_{\operatorname{ht}\mathfrak p=1}A_\mathfrak p
\quad\text{inside }\operatorname{Frac}(A)
\tag{5.5}
$$

componentwise. For a finite normalization the same statement holds after taking the product of the fraction fields. We will use (5.5) to extract periods from traits, but never to infer nilpotent information. Nilpotent information is supplied by the recognition theorem of Chapter 7.

The intersection property has a divisor-theoretic proof. Membership in every height-one localization means that the divisor of the rational function has no negative coefficient. On a normal noetherian domain, a rational function with no denominator divisor belongs to the domain because every principal ideal is the intersection of its height-one primary localizations. Applying the statement to the function and its inverse detects units.

### 5.3 The logarithmic period map

Let $X$ and $Y$ be the character and period lattices of a cusp, with $\mathcal O_F$-action, and let

$$
B:Y\times X\longrightarrow P_\sigma^{\mathrm{gp}}
\tag{5.6}
$$

be the integral bilinear form obtained by evaluating the universal monodromy form. A logarithmic period homomorphism over $A$ is a map

$$
\iota:Y\longrightarrow T_X^{\log}(A)
=\operatorname{Hom}\bigl(X,M_A^{\mathrm{gp}}\bigr)
\tag{5.7}
$$

whose characteristic part is $B$ and whose unit part is a homomorphism

$$
u:Y\times X\longrightarrow A^\times.
\tag{5.8}
$$

In coordinates,

$$
\iota(y)(x)=u(y,x)q^{B(y,x)}.
\tag{5.9}
$$

The polarization identifies $Y$ with a fractional ideal dual to $X$ and imposes symmetry

$$
B(y,\lambda(y'))=B(y',\lambda(y)),
\tag{5.10}
$$

together with the analogous equality for $u$. Positivity says that $B(y,\lambda(y))$ is positive on every nonzero $y$ after evaluation against every interior point of $\sigma$. Level structure fixes the required torsion trivializations of this logarithmic one-motive.

Formula (5.9) separates two phenomena that are often confused. The monomial $q^{B(y,x)}$ records contact with the base boundary. The unit $u(y,x)$ records extension data along the boundary stratum. A deformation may alter the latter without smoothing a node; it may alter the former only through the specified strict map $P_\sigma\to M_A$.

### 5.4 Face restriction and base change

If $\tau$ is a face of $\sigma$, localizing (5.9) at $P_\sigma\cap\tau^\perp$ produces the period map for the $\tau$-chart. If $A\to A'$ is a strict morphism of complete test pairs, applying $M_A^{\mathrm{gp}}\to M_{A'}^{\mathrm{gp}}$ gives the base-changed period map. These operations commute.

The periodic decomposition chosen in Section 4.5 has the same property: on a face it restricts to the common refinement assigned to that face. Therefore the construction below will satisfy canonical identities

$$
\operatorname{Mum}_\sigma(\iota)\times_A A'
\simeq \operatorname{Mum}_\sigma(\iota_{A'}),
\qquad
\operatorname{Mum}_\sigma(\iota)|_\tau
\simeq \operatorname{Mum}_\tau(\iota|_\tau).
\tag{5.11}
$$

The word canonical matters. Later descent needs equality of the induced arrows on triple overlaps, not merely existence of some isomorphism.

## 6. The Mumford construction

### 6.1 The periodic polyhedral algebra

Fix a coherent $Y$-periodic polyhedral decomposition $\mathscr P$ of $X_\mathbf R$ and an integral strictly convex support function $\varphi$. After replacing the polarization by a fixed positive power, assume that all vertices and all values of $\varphi$ are integral. Introduce a degree variable $z$. For a cell $C\in\mathscr P$, define the semigroup

$$
Q_C=\{(n,x,p):n\ge0, x\in nC\cap X, p-\varphi_C(x)\in P_\sigma\},
\tag{6.1}
$$

where $\varphi_C$ is the affine function agreeing with $\varphi$ on $C$. Its algebra over $A$ is generated by symbols

$$
z^n\vartheta_xq^p,
\qquad (n,x,p)\in Q_C,
\tag{6.2}
$$

with multiplication obtained by addition of triples. Gordan's argument again proves finite generation. Saturation of $P_\sigma$ and integrality of the cells imply that the saturation of $Q_C$ is the semigroup of lattice points in its rational cone. We use this saturation; it is precisely the normalization of the affine toric chart.

On $C\cap C'$ the localizations of $A[Q_C]$ and $A[Q_{C'}]$ agree. The difference $\varphi_C-\varphi_{C'}$ is an integral affine function vanishing on the common face, so the gluing map is multiplication by an invertible monomial. The resulting graded algebra

$$
\mathcal R(\mathscr P,\varphi)=
\bigoplus_{n\ge0}\mathcal R_n
\tag{6.3}
$$

is best regarded as a sheaf on the union of the affine toric base charts. Its relative Proj before taking periods is the normalized infinite model $\widetilde P$.

There is a useful basis description. On a fixed normalized star, $\mathcal R_n$ is the completed direct sum of the weights $\vartheta_x$ with $x\in nC\cap X$, and multiplication has the form

$$
\vartheta_x\vartheta_{x'}
=q^{\varphi(x)+\varphi(x')-\varphi(x+x')}\vartheta_{x+x'}.
\tag{6.4}
$$

Convexity makes the exponent lie in $P_\sigma$. Strict convexity makes it nonzero when the two weights do not belong to a common linearity cell. Thus the special fiber remembers exactly the incidence complex of $\mathscr P$.

In rank one take $X=Y=\mathbf Z$, cells $[i,i+1]$, and $\varphi(x)=x(x-1)/2$ at integral points. On two adjacent affine charts the degree-one weights give coordinates $X_i,Y_i$ with

$$
X_iY_i=q.
\tag{6.4a}
$$

At $q=0$ this is a node. Translation identifies the right end of one component with the left end of the next; quotienting by a period of valuation $n$ gives the $n$-gon. This example simultaneously displays the monomial base parameter, the normalized branches, and the nonnormal conductor gluing.

### 6.2 Gluing and the period quotient

The period lattice acts on weights by $x\mapsto x+n\lambda(y)$ in degree $n$. The required multiplier is determined by (5.9) and the quadratic refinement of the polarization. With $a(y)$ denoting that refinement, set

$$
y\cdot\vartheta_x
=u(y,x)u(y,a(y))^n
q^{B(y,x)+nB(y,a(y))}\vartheta_{x+n\lambda(y)}.
\tag{6.5}
$$

Symmetry of the period pairing is exactly the identity which makes (6.5) an action rather than a projective action. Changing the chosen quadratic refinement multiplies every degree-$n$ formula by a degreewise coboundary and therefore gives a canonically isomorphic Proj.

To check the action, apply first $y'$ and then $y$. The quotient of the resulting multiplier by the multiplier for $y+y'$ is the alternating part of the period pairing. It is one precisely when the polarization trivialization is symmetric. The quadratic refinement satisfies

$$
a(y+y')-a(y)-a(y')=B(y,y')
\tag{6.5a}
$$

after the standard identification of a bilinear form with its character exponent, so the monomial factors agree as well. This calculation proves the cocycle on triple period overlaps.

Choose finitely many cells representing $Y$-orbits. Glue their normalized stars along common faces and identify translated boundary faces by (6.5). Since only finitely many orbit representatives occur, the quotient

$$
P_A=\widetilde P/Y
\tag{6.6}
$$

is proper and of finite presentation once the base is noetherian. Its normalization is the disjoint union, with face gluings, of finitely many normalized stars; $P_A$ itself need not be normal. In fact the conductor identifications between translated outer faces are what create the familiar cycle of projective lines in the rank-one special fiber.

The quotient can also be described without taking a quotient of an infinite object. Choose a finite fundamental polytope, list its boundary-face pairings, and take the coequalizer of the two finite unions of face schemes. The coordinate ring on an affine patch is the equalizer of the two restriction maps. This finite presentation will be used in Chapter 10.

### 6.3 Flatness, properness, and the group locus

Every normalized affine star is flat over $A$. Indeed its coordinate algebra is a direct sum of copies of $A$ indexed by a saturated semigroup, and all gluing maps preserve that basis. The conductor face rings have the same property. For a finite face pushout the exact sequence

$$
0\longrightarrow\mathcal O_{P_A}
\longrightarrow\nu_*\mathcal O_{P_A^\nu}\oplus\mathcal O_C
\longrightarrow\nu_*\mathcal O_{C^\nu}
\longrightarrow0
\tag{6.7}
$$

shows flatness: all three terms to the right are $A$-flat and the last arrow is surjective on monomial bases. Tensoring (6.7) with an $A$-module remains exact.

The last surjectivity is visible weight by weight. A conductor face ring retains the weights in its face semigroup and sends every other weight to zero. Every retained weight has the same named lift in the adjacent star. The cokernel therefore vanishes in each weight, and the kernel is a direct summand after forgetting multiplication. This proves universal exactness of (6.7), including after a nonflat nilpotent base change.

Properness follows from the valuative criterion. Over a valuation ring, a point of the generic torus has a valuation vector in $X_\mathbf R$. Completeness of the periodic decomposition places it in some cell after translation by $Y$, and the corresponding toric chart gives an extension. Two extensions agree because their valuation vectors lie in a common face after passing to a common refinement. The same argument after finite extension handles nonsplit tori; descent gives the original extension.

Where every nonzero $q^p$ is invertible, all toric boundary divisors disappear. Formula (6.5) then gives the quotient of the Raynaud extension by its period lattice, hence the original abelian scheme. The smooth group locus extends across the base as the semiabelian scheme $G$ of Chapter 2 and acts on $P_A$. Each geometric fiber has finitely many $G$-orbits, with one orbit for every cell modulo $Y$.

The construction is separated before it is proper. If two star charts contain the same torus point over a valuation ring, their valuation vector belongs to the intersection of the two cells, and the face localization identifies the extensions. Thus the diagonal satisfies the valuative uniqueness criterion. Completeness of the cells supplies existence, so together they prove the full valuative criterion used above.

Connectedness follows from the cell complex. Every normalized star is connected, adjacent stars meet along a nonempty conductor face, and the periodic decomposition of the real vector space is connected. The quotient incidence complex is connected. Sequence (6.7) then shows that the only global idempotents are zero and one, also after geometric base change.

### 6.4 Endomorphisms, polarization, and level

The $\mathcal O_F$-action sends the weight $x$ to the weight $ax$ and transports cells by the chosen equivariant decomposition. It therefore acts on the normalized stars and respects every conductor pairing. The determinant condition holds on the dense abelian locus. Both sides of the determinant identity are coefficients of characteristic polynomials acting on a locally free Lie algebra; equality extends across a reduced base and then through nilpotents by the prescribed PEL deformation condition.

The symmetry (5.10) gives a cubical homomorphism from the one-motive to its dual. On the abelian locus it is the chosen polarization. On every normalized star it is represented by the integral support function $\varphi$, and strict convexity makes the associated line relatively ample. Compatibility of the support functions on paired faces lets this line descend to the nonnormal quotient.

The toric ampleness criterion has a direct proof. Sections of the line are the lattice weights under the graph of $\varphi$. If $\varphi$ is strictly convex, ratios of two such sections give every character on each orbit and separate adjacent orbits by a section vanishing on one face but not the other. A high power therefore gives a closed immersion. If $\varphi$ is linear across a wall, every section has equal normalized slope there and contracts the invariant curve of that wall. Strict convexity is consequently both necessary and sufficient.

Prime-to-residue-characteristic level structure extends uniquely over the semiabelian locus because finite etale torsion over a normal base is determined on a dense open. At the boundary, a paired frame records the toric and period parts of torsion separately. The Kummer refinement of Chapter 9 will make this assertion integral even when the original cusp lattice has denominators.

### 6.5 The family theta line

Let $\widetilde\Theta$ be the invertible sheaf associated with degree one in (6.3). Formula (6.5), including its multiplier, is a descent datum. Hence it gives an invertible sheaf

$$
\Theta_A\quad\text{on }P_A.
\tag{6.8}
$$

It is relatively ample: on the normalization this is the standard toric criterion of strict convexity, and finite surjective descent preserves relative ampleness. Explicitly, if $\nu:P_A^\nu\to P_A$ is finite and $\nu^*\Theta_A$ is ample, then some power separates points and tangent directions upstairs; taking norms of the finitely many local generators produces a power downstairs with the same property.

The line $\Theta_A$ lives on the universal semiabelic family. It is not the support-function line on the toroidal base and not the determinant of its cohomology. Those three lines will be compared only in Chapter 14.

## 7. Infinitesimal recognition

### 7.1 The intrinsic logarithmic structure of a semiabelic model

Let $P\to\operatorname{Spec}A$ be a flat proper semiabelic model having the same normalized-star combinatorics as a Mumford model. Write $\nu:P^\nu\to P$ for its finite normalization and $C^\nu\to C$ for the conductor. On a normalized star, let $j:T\hookrightarrow P^\nu$ be the open orbit. Define

$$
M_{P^\nu}=\mathcal O_{P^\nu}\cap j_*\mathcal O_T^\times
\quad\text{inside }j_*\mathcal O_T.
\tag{7.1}
$$

This is the sheaf of functions that are units on the torus. The order map along the toric prime divisors identifies its characteristic monoid with the saturated dual of the star cone. The two restrictions to $C^\nu$ agree under each conductor pairing: on a common face they are the same monomials, and the period multiplier is a unit. Thus the equalizer of their pushforwards descends to a logarithmic structure $M_P$ on $P$.

When $A$ has nilpotents, $P^\nu$ means the canonical finite star cover obtained by lifting the normalization of $P_{\mathrm{red}}$, not the integral closure of a nonreduced ring. The cover is part of the normalized-star type: its affine weight modules and conductor faces are flat over $A$. Theorem 7.1 will prove that this lift is unique. This convention prevents the meaningless operation of normalizing nilpotents while retaining the geometric information normalization is meant to expose.

The characteristic monoid can be read combinatorially. At the generic orbit it is zero. Crossing a toric divisor adds its primitive order functional. At an intersection, the functionals generate the dual star cone. Along a conductor face the two adjacent stars restrict to the same face cone, so their ghost sheaves glue. The resulting ghost sheaf recovers the entire cell complex and its face maps.

The base characteristic is recovered rather than imposed. A relation between adjacent star weights has the form

$$
e_xe_{x'}=a_{x,x'}e_{x+x'},
\tag{7.2}
$$

where the vanishing order of $a_{x,x'}$ is independent of trivializations. Associativity makes these orders additive on subdivisions. The resulting map from the monoid of convexity defects to $A/A^\times$ is the characteristic map

$$
\alpha_P:P_\sigma\longrightarrow A/A^\times.
\tag{7.3}
$$

Lifting a representative of each class gives an fs log structure on the base, unique up to unique strict isomorphism. Saturation follows locally from the saturated star monoids: if the $n$th power of a rational monomial has nonnegative order along every toric divisor, the monomial itself does too. Descent across the conductor introduces no new divisibility because a face of a saturated monoid is saturated.

The intrinsic log structure is compatible with arbitrary base change, including a square-zero one. This can be checked on (7.2): tensor the normalized-star and conductor equalizer diagrams with the new base, then take the same monomial-unit subsheaves. The flatness established by (6.7) prevents the creation of spurious annihilated monomials.

There is a local normal-crossing verification. At a codimension-$r$ orbit the completed star algebra has monomials $z_1,\ldots,z_r$ and relations whose products equal the base elements $\alpha(p_i)$. The orders of the $z_i$ freely generate the sharp characteristic. A base change replaces only the coefficients $\alpha(p_i)$; the exponent vectors and their saturated relations remain unchanged. Conductor equalizers are kernels between flat modules, so this calculation passes from stars to the nonnormal pushout.

An object over the fixed toroidal test pair $(A,M_A)$ will henceforth mean a semiabelic PEL object together with a strict identification

$$
(A,M_P^{\mathrm{base}})\simeq(A,M_A).
\tag{7.4}
$$

This is not extra decoration: it records which deformations preserve the chosen toroidal boundary chart.

### 7.2 Why the unenhanced assertion is false

Let $A=k[\epsilon]/(\epsilon^2)$ and give the base the log chart $\mathbf N\to A$ sending $1$ to $0$. The nodal algebra

$$
A[X,Y]/(XY)
\tag{7.5}
$$

has a deformation

$$
A[X,Y]/(XY-\epsilon).
\tag{7.6}
$$

They have the same reduction and the same generic combinatorial type; (7.6) is nevertheless not the base change of (7.5). Its intrinsic logarithmic parameter sends $1$ to $\epsilon$, while that of (7.5) sends $1$ to $0$. No unit can carry $0$ to $\epsilon$. Therefore no strict identification (7.4) exists for (7.6).

This example proves that an assertion about the underlying PEL scheme alone would be false. The correct recognition theorem concerns logarithmic semiabelic objects over a fixed strict toroidal test pair. It rules out (7.6) for an actual reason, rather than concealing it in a generic-fiber hypothesis that is empty on this Artin ring.

The same phenomenon occurs globally on an $n$-gon. Smoothing one node by $XY=\epsilon$ while leaving all base monodromy generators zero changes the intrinsic ghost-to-ring map at that node and breaks periodic compatibility with the other conductors. Smoothing every node coherently corresponds instead to a genuine map from the universal monodromy monoid. The completed toroidal ring includes the coherent smoothing and excludes only incoherent smoothings from a fixed strict fiber.

### 7.3 Square-zero monomial recognition

Suppose $A'\twoheadrightarrow A$ has square-zero kernel $I$, and let $P'$ be a logarithmic semiabelic object over $A'$ whose reduction is the Mumford object attached to $\iota$. Work first on one normalized star. The torus action decomposes its affine coordinate algebra into rank-one weight modules

$$
R'=\bigoplus_{x\in Q}L_x,
\tag{7.7}
$$

because the diagonalizable torus is linearly reductive in the elementary grading sense: a comodule over $A'[X]$ is the direct sum of the inverse images of its characters. Flatness and reduction to a free rank-one weight module imply that each $L_x$ is invertible. After choosing generators $e_x$, multiplication is

$$
e_xe_y=c(x,y)e_{x+y}.
\tag{7.8}
$$

Strict intrinsic-log compatibility determines the nonunit factor of $c(x,y)$. If

$$
d(x,y)=\varphi(x)+\varphi(y)-\varphi(x+y)\in P_\sigma,
\tag{7.9}
$$

then

$$
c(x,y)=\alpha_{A'}(d(x,y))v(x,y),
\qquad v(x,y)\in A'^\times.
\tag{7.10}
$$

This remains informative when $\alpha_{A'}(d)=0$. An additional square-zero smoothing would replace that zero by a nonzero member of $I$, changing the characteristic map recovered from (7.2), and would violate strictness. Thus (7.10) handles exactly the case missed by arguments which divide by boundary parameters.

Associativity gives

$$
v(x,y)v(x+y,z)=v(y,z)v(x,y+z).
\tag{7.11}
$$

Commutativity gives $v(x,y)=v(y,x)$, and the unit gives $v(0,x)=1$. The multiplication is therefore the standard monomial multiplication times a symmetric normalized unit $2$-cocycle.

The weight calculation also controls possible extra generators. Let $Q^{\mathrm{sat}}$ be the star semigroup. If a weight $x$ not in $Q^{\mathrm{sat}}$ appeared over $A'$, its reduction would vanish, so its weight module would be annihilated by the square-zero ideal and could not be flat. If an expected weight disappeared, flatness would fail after reduction. Thus the support semigroup itself is infinitesimally rigid. Only its multiplication coefficients can move, and (7.10) has classified those movements.

On an intersection of stars, localization in a face weight identifies the two gradings. The two choices of $e_x$ differ by units forming a character on the face lattice. Such characters are exactly changes of torus trivialization. On a conductor pair, the same comparison includes the period translation; this is where a unit period remains visible even when a local multiplication coefficient has zero monomial factor.

### 7.4 Splitting the unit cocycle

We need an explicit splitting, valid over rings with nilpotents. Let $L$ be a free lattice. Choose an ordered basis $b_1,\ldots,b_r$. Set $s(0)=1$, choose $s(b_i)=1$, and extend successively along each coordinate by

$$
s(x+b_i)=s(x)v(x,b_i)^{-1}.
\tag{7.12}
$$

For negative steps use the same formula solved for $s(x)$. Equation (7.11) and symmetry show that moving first in direction $b_i$ and then $b_j$ gives the same answer as the reverse order. Hence $s:L\to A'^\times$ is well defined and

$$
v(x,y)=s(x)s(y)s(x+y)^{-1}.
\tag{7.13}
$$

Replacing $e_x$ by $s(x)^{-1}e_x$ removes $v$. On a semigroup contained in $L$, apply this construction to its group completion; the chosen star generators restrict compatibly to faces.

There remains periodic gluing. Comparing a generator with its $Y$-translate produces units $u(y,x)$. Associativity with multiplication makes $u$ bilinear in $x$, while comparing two translations makes it a homomorphism in $y$. The characteristic part is already fixed by (7.10), so together they recover precisely the logarithmic period map (5.9). Polarization symmetry follows from the cubical structure on the theta line; level and $\mathcal O_F$-equivariance follow by applying the same comparison to the rigidified torsion sections and endomorphisms.

Changing the star generators changes $s$ by a character. Such a character is an automorphism of the torus and gives the unique corresponding isomorphism of one-motives. Thus the extraction is independent of choices at the groupoid level.

We also recover the action and the line, rather than just the underlying algebra. The coaction map is homogeneous and hence fixed by the weight labels. A lift of the theta line is a graded rank-one module; choosing its degree-one generator changes the preceding splitting by the same character, so the cubical rigidification removes the ambiguity. The $\mathcal O_F$-action permutes weights by $x\mapsto ax$. Compatibility with multiplication forces the extracted period map to be $\mathcal O_F$-balanced. Finally the polarization involution sends weight $x$ to the dual weight prescribed by $\lambda$, and its cubical identity gives symmetry of both the characteristic and unit pairings.

### 7.5 Induction through nilpotent thickenings

Let $A$ be complete with nilpotent ideal $K$. Filter it by square-zero extensions

$$
A/K\leftarrow A/K^2\leftarrow\cdots\leftarrow A/K^m=A.
\tag{7.14}
$$

At each step Sections 7.3 and 7.4 recover a unique lift of the period map and a unique isomorphism with its Mumford model, once the preceding reduction is fixed. Obstructions cannot hide on conductor intersections: the normalization-conductor sequence (6.7) is exact after tensoring with each square-zero kernel, so compatible star isomorphisms descend. Automorphisms reducing to the identity are characters $1+\delta_x$ with $\delta_{x+y}=\delta_x+\delta_y$; rigidification of the identity, polarization, and level force this character to be zero.

More explicitly, the differences between two local splittings form a Cech $1$-cocycle with values in the split torus $\operatorname{Hom}(X,1+I)$. The dual complex of a normalized star is contractible, so it is a coboundary there. Around a periodic loop its class is exactly a homomorphism $Y\times X\to1+I$, hence a deformation of the unit-period map rather than an obstruction. Once that period deformation is recorded, the cocycle vanishes and the star isomorphisms glue. The identity section prevents a remaining torus translation; neat level prevents a finite residual automorphism.

For an adic, not necessarily nilpotent, complete ring apply the result to $A/I^n$. The isomorphisms are unique and hence compatible. Taking the inverse limit gives the assertion over $A$ because all coordinate algebras and all Hom modules involved are finite over the complete base.

**Theorem 7.1 (infinitesimal recognition).** Over a fixed complete fs toroidal test pair, the Mumford construction is fully faithful on nilpotent thickenings and every logarithmic semiabelic PEL deformation with the prescribed normalized-star type is induced by a unique deformation of its polarized logarithmic one-motive. The statement includes Artin rings supported on the boundary. It excludes extra smoothing terms because strictness fixes the intrinsic characteristic map.

## 8. The inverse theorem and completed deformation rings

### 8.1 Extraction on normal reduced bases

Let $A$ be reduced and normal and let $P/A$ be a logarithmic semiabelic PEL object which is abelian away from the boundary. Over the fraction field of each component, the Raynaud construction of Chapter 2 gives its one-motive. For a height-one prime $\mathfrak p$, properness extends $P$ to the valuation ring $A_\mathfrak p$. The action on the normalized special fiber reads off the character lattice, and the orders of the period functions give

$$
v_\mathfrak p(\iota(y)(x))
=v_\mathfrak p\bigl(q^{B(y,x)}\bigr).
\tag{8.1}
$$

The quotient is a unit at every height-one prime after the monomial is removed. By (5.5) it belongs to $A^\times$. Hence

$$
\iota(y)(x)=u(y,x)q^{B(y,x)}
\tag{8.2}
$$

over $A$, not merely over its fraction field. The group law, symmetry, positivity, endomorphisms, and level identities hold in the fraction fields and therefore in $A$. This extracts a polarized logarithmic one-motive.

To justify the word unit, apply (5.5) both to the quotient and to its inverse. Equation (8.1) gives valuation zero at every height-one prime, so both belong to $A$. Positivity can also be checked traitwise: if an interior real functional made the quadratic form nonpositive, a rational functional arbitrarily close to it would define a height-one monomial trait with nonpositive Raynaud pairing, contradicting ampleness of the trait fiber.

If $A$ is reduced but not normal, perform the extraction on its finite normalization. On the conductor the two pullbacks agree because both are read from the same multiplication maps of $P$. The unit factors therefore lie in the equalizer defining $A$. This is the first appearance of conductor descent; Chapter 12 proves the more delicate ramified form needed for coefficient descent.

### 8.2 Full faithfulness

Let $f:P_1\to P_2$ be an isomorphism of logarithmic semiabelic PEL objects. On the open group orbit it induces an isomorphism of semiabelian schemes, hence of character lattices and Raynaud extensions. The pullback of normalized weight functions determines its effect on periods. Since a normalized star is the closure of its torus, that effect determines $f$ on the normalization. Since $P_i$ is the conductor pushout of its normalization, it determines $f$ everywhere.

Conversely, an isomorphism of polarized logarithmic one-motives transports the weight algebra (6.3), the period action (6.5), and every conductor pairing. It therefore induces an isomorphism of Mumford objects. The two constructions are inverse. Over a reduced base this follows from the preceding paragraph and density; over nilpotent thickenings it follows from Theorem 7.1. Thus full faithfulness holds on all complete test pairs, including those with no abelian generic point.

### 8.3 Essential surjectivity

For a normal reduced base, Section 8.1 extracts a one-motive and the construction of Chapter 6 produces a Mumford object $P^{\mathrm M}$. They agree over the fraction fields. On each normalized star their graded weight algebras have the same monomial orders and the same unit period factors, so they agree over $A$ by (5.5). The conductor face identifications are restrictions of those same period factors; hence $P^{\mathrm M}\simeq P$.

For a general reduced excellent base, descend this isomorphism from the finite normalization through its conductor equalizer. For a nilpotent thickening, apply Theorem 7.1 successively. For a complete adic base, pass to the inverse limit. Effectivity of compatible invertible sheaves and morphisms follows from finite presentation: an idempotent matrix, a finite list of algebra maps, and their relations all lift uniquely from the inverse system.

We have proved the promised equivalence, rather than assumed it.

**Theorem 8.1 (Mumford period equivalence).** For every complete fs toroidal test pair, polarized logarithmic one-motives of the fixed Hilbert--Blumenthal cusp type are equivalent to logarithmic semiabelic PEL objects of the chosen normalized-star type. The equivalence commutes with strict base change, restriction to fan faces, normalization, conductors, theta lines, and prime-to-residue-characteristic level structures.

### 8.4 Completed local rings

Fix a geometric boundary object $z$ with cone $\sigma$. Deformations of its abelian part, extension part, and rigidified level data are unobstructed smooth parameters; denote their complete coefficient ring by $S_z$. The monodromy parameters are exactly the monoid $P_\sigma$. Therefore the framed deformation functor is represented by

$$
R_z^{\mathrm{fr}}=S_z[[P_\sigma]].
\tag{8.3}
$$

Here representability is direct. A map $S_z[[P_\sigma]]\to A$ chooses the smooth Raynaud and unit-period parameters and a continuous chart $P_\sigma\to A$; Chapter 6 constructs the object. Theorem 8.1 recovers the same data from every object and identifies arrows. Thus the two functors are mutually inverse on all Artin quotients.

In the Hilbert boundary case $B=0$, so the smooth factor has a particularly transparent origin. The split torus and the projective rank-one lattices are locally constant. The unit periods range through a subtorus of

$$
\operatorname{Hom}_{\mathcal O_F}(Y\otimes X,\mathbf G_m),
\tag{8.3a}
$$

cut out by polarization symmetry, and the rigidified prime-to-residue-characteristic frames form a finite etale scheme. Completion at the chosen unit period is a power-series ring. On the good-reduction face, the deformation coordinates of the abelian object replace (8.3a); the standing invertibility hypotheses make the PEL determinant equations smooth. Thus $S_z$ is obtained from explicitly smooth factors, not from an unobstructedness assumption.

If a finite stabilizer $H_z$ remains before neat rigidification, the unframed completed local ring is the invariant ring

$$
R_z=(R_z^{\mathrm{fr}})^{H_z}.
\tag{8.4}
$$

In the regular neat charts of Theorem 4.2 the stabilizer of a nonzero cone is trivial. At the zero cone (8.3) reduces to the usual smooth deformation ring of the abelian object. Face localization in the monoid identifies the completed rings on overlaps.

### 8.5 Traits and boundary-supported Artin rings

For a trait $V$ with uniformizer $\pi$, a map $P_\sigma\to V$ is determined by nonnegative valuations $\ell(p)=v(q^p)$ and unit leading coefficients. The function $\ell$ lies in $\sigma$; after a finite Kummer extension it is integral. The extracted one-motive is the classical Raynaud one-motive, and Theorem 8.1 says its Mumford model is the unique extension.

For $A=k[\epsilon]/(\epsilon^n)$ with all positive monomials mapped to zero, no trait sees the higher nilpotents. Nevertheless (8.3) represents its deformations: the smooth parameters may move in the nilradical, while the monodromy parameters remain zero. A relation $XY=\epsilon$ would define a different chart and is absent. Hence traits and nilpotent boundary tests play complementary roles: traits determine integral orders on reduced normal bases, and infinitesimal recognition determines the completed functor transverse to them.

## 9. Paired frames and Kummer normalization

### 9.1 Torsion of the boundary one-motive

Let $N\ge3$ be the auxiliary level, prime to the residue characteristics under consideration. For the logarithmic one-motive $[Y\to G]$, multiplication by $N$ gives an exact sequence of fppf sheaves

$$
0\longrightarrow G[N]
\longrightarrow [Y\to G][N]
\longrightarrow Y/NY
\longrightarrow0.
\tag{9.1}
$$

The toric part of $G[N]$ is $\operatorname{Hom}(X,\mu_N)$. A frame of only one side of (9.1) does not rigidify the boundary: translating a lift of $Y/NY$ by toric torsion changes the period multiplier. A paired frame consists of

$$
\beta_X:X/NX\xrightarrow{\sim}X_0/NX_0,
\qquad
\beta_Y:Y/NY\xrightarrow{\sim}Y_0/NY_0,
\tag{9.2}
$$

together with the Weil-pairing compatibility induced by the polarization. The two frames determine each other after applying the polarization, but retaining both makes descent symmetries and denominators visible.

Because $N$ is invertible, the sheaves in (9.1) are finite etale over the semiabelian locus. The functor of paired frames is consequently a finite etale torsor there. Along the boundary, taking an $N$th root of a period monomial is generally ramified; this is the Kummer phenomenon.

### 9.2 The refined Fourier lattice

Suppose a framed period requires $q^{B(y,x)/N}$. Enlarge the Fourier lattice $M$ to

$$
M^{\mathrm{fr}}
=M+\left\langle N^{-1}B(y,x):x\in X,\ y\in Y\right\rangle
\subset M_\mathbf Q.
\tag{9.3}
$$

It is a finite-index over-lattice. For a cone $\sigma$, set

$$
P_\sigma^{\mathrm{fr}}=\sigma^\vee\cap M^{\mathrm{fr}}.
\tag{9.4}
$$

This monoid is again finitely generated and saturated. The inclusion $P_\sigma\subset P_\sigma^{\mathrm{fr}}$ is Kummer: for every $p'$ some positive multiple lies in $P_\sigma$. Hence

$$
S[P_\sigma]\longrightarrow S[P_\sigma^{\mathrm{fr}}]
\tag{9.5}
$$

is finite. To see finiteness, choose representatives for the finite quotient $M^{\mathrm{fr}}/M$; every monomial in the larger algebra is a monomial from the smaller algebra times one of finitely many representatives lying in a bounded fundamental parallelepiped. It is generically etale when $N$ is invertible, but it may ramify along the boundary.

The normalization of $S[P_\sigma]$ in the framed torus extension is exactly $S[P_\sigma^{\mathrm{fr}}]$. Indeed a monomial $q^{p'}$ in the latter is integral because a power belongs to the former. Conversely, an integral character has nonnegative valuation on every ray of $\sigma$, so its exponent belongs to $\sigma^\vee\cap M^{\mathrm{fr}}$. This valuation proof also works over an excellent normal coefficient ring.

The rank-one example is $q=s^N$. The interior map

$$
S[q,q^{-1}]\longrightarrow S[s,s^{-1}],
\qquad q\longmapsto s^N,
\tag{9.5a}
$$

is finite etale when $N$ is invertible. Its extension across $q=0$ is finite flat but totally ramified, and the normalized boundary chart is $S[s]$. Completing first and writing a purely symbolic $q^{1/N}$ would predict the same series ring, but would not prove that $s$ belongs to a finite algebraic chart or identify how its deck transformations meet at $s=0$.

### 9.3 Normalization before completion

Let $U_\sigma=\operatorname{Spec}S[P_\sigma]$ and let $U_\sigma^{\mathrm{fr}}$ be the normalization in the paired-frame cover of the interior. Section 9.2 proves

$$
U_\sigma^{\mathrm{fr}}
=\operatorname{Spec}S'[P_\sigma^{\mathrm{fr}}],
\tag{9.6}
$$

where $S'/S$ is the finite etale extension needed for the unit parts of the frames. Because the rings are excellent, finite normalization commutes with completion along the monomial boundary ideal. One elementary proof uses the finite module $B=S'[P_\sigma^{\mathrm{fr}}]$: its completion is finite over $\widehat A$, is normal by the regular monoid charts, and has the same total quotient algebra as the completed generic cover. The universal property of integral closure gives both inclusions.

Thus

$$
\widehat{U_\sigma^{\mathrm{fr}}}
\simeq
\operatorname{Spf}S'[[P_\sigma^{\mathrm{fr}}]].
\tag{9.7}
$$

The order is important. The framed branch is defined as a finite algebraic normalization and only then completed. Treating a root of a formal parameter as an isolated formal operation would supply no finite-type branch from which descent could begin.

If several division periods occur, Smith normal form reduces them to equations

$$
s_i^{n_i}=\zeta_iq^{p_i},
\qquad n_i\mid N^a.
\tag{9.7a}
$$

After a finite etale extension containing the roots of the constant units $\zeta_i$, rescale $s_i$ and apply the lattice argument one coordinate at a time. This proves that (9.6) accounts for all connected Kummer factors; the remaining finite constant factors are etale and lie in $S'$.

### 9.4 Smoothness and descent of framed branches

Refine the fan in the lattice dual to $M^{\mathrm{fr}}$ and regularize equivariantly as in Chapter 4. Then the framed chart is smooth over the smooth coefficient stratum, with boundary a relative normal-crossings divisor. The finite deck group $\Delta$ acts on paired frames, the refined lattice, the fan, and the Mumford family.

On the interior, forgetting the frame is a finite etale torsor. At the boundary it is finite Kummer and usually ramified. Ordinary etale descent is therefore insufficient. We retain the finite flat cover and descend through the tensor square in Chapter 12. The simultaneous equivariance of the fan ensures that every deck transformation carries a normalized star to a normalized star and preserves its conductor faces.

## 10. Bounded normalization and conductor presentations

### 10.1 The conductor square

For a reduced semiabelic family $P$ with finite normalization $\nu:P^\nu\to P$, let

$$
\mathfrak c
=\operatorname{Ann}_{\mathcal O_P}
(\nu_*\mathcal O_{P^\nu}/\mathcal O_P)
\tag{10.1}
$$

be the conductor ideal. Set $C=V(\mathfrak c)$ and $C^\nu=P^\nu\times_P C$. Affine locally, if $A\subset B$ is finite birational and $I$ is the conductor, then

$$
A=B\times_{B/I}A/I.
\tag{10.2}
$$

Indeed a pair $(b,\bar a)$ with equal images has $b-a\in I\subset A$, so $b\in A$. Thus the diagram

$$
\begin{matrix}
C^\nu&\longrightarrow&P^\nu\\
\downarrow&&\downarrow\nu\\
C&\longrightarrow&P
\end{matrix}
\tag{10.3}
$$

is both cartesian and a pushout. In a Mumford fiber, $P^\nu$ is the union of normalized stars and $C^\nu$ is the union of paired toric faces. This remains true when $P$ is nonnormal and reducible.

The conductor presentation contains more information than the normalization alone. A chain of normalized projective lines can be glued into a cycle, a chain, or a disconnected union using the same normalization; the two maps $C^\nu\rightrightarrows P^\nu$ distinguish them.

For the affine node $A=k[x,y]/(xy)$, the normalization is $B=k[x]\times k[y]$, the conductor is $(x,y)$, and

$$
A
=B\times_{k\times k}k,
\qquad c\longmapsto(c,c).
\tag{10.3a}
$$

Replacing the diagonal $k\to k\times k$ by two independent copies gives the disjoint normalization; pairing the conductor points in another order changes a polygon gluing. This elementary equalizer is the local model for every higher-dimensional face pairing.

### 10.2 Uniform theta embeddings

There are finitely many periodic cell types modulo the period lattice and finitely many cusp types. Choose one integer $m_0$ which simultaneously:

1. clears the denominators of every support function and cell vertex;
2. makes $\Theta^{m_0}$ very ample on every normalized toric star;
3. makes restriction of sections to every conductor face surjective; and
4. kills the finite projective multipliers of the frame and coefficient symmetries.

Such an $m_0$ exists by taking the least common multiple of the finitely many denominators and then a common sufficiently large multiple. The toric assertions are elementary. For a lattice polytope $Q$, a sufficiently large dilation $mQ$ is generated by lattice points in degree one, and lattice points on a face lift to lattice points of $mQ$; triangulating $Q$ reduces both statements to the standard simplex.

For a lattice simplex with vertices $v_0,\ldots,v_r$, reduce the barycentric coefficients of a lattice point modulo integers. The remainder lies in one of finitely many lattice points of the fundamental parallelepiped. Once the dilation exceeds the largest sum of the remainder coefficients, subtracting that remainder leaves a nonnegative integral sum of vertices. This proves generation in bounded degree. Apply the argument to a triangulation and use agreement on common faces. The same reduction within a face proves surjectivity to that face. Since there are finitely many cell types, one dilation works for all of them.

For every family in the fixed combinatorial collection, $\Theta^{m_0}$ gives a closed immersion

$$
P^\nu\hookrightarrow\mathbf P^R_A
\tag{10.4}
$$

with a single $R$. Add zero coordinates when a star uses fewer weights. The conductor $C^\nu$ is embedded by the corresponding face weights. Period identifications are graphs of monomial maps whose exponents belong to a fixed finite list.

### 10.3 Bounded Hilbert and graph data

The Hilbert polynomial of a normalized toric star embedded by $m_0Q$ is

$$
h_Q(n)=\#(nm_0Q\cap X)
\tag{10.5}
$$

for $n\ge0$. There are finitely many $Q$, hence finitely many such polynomials. The same holds for all conductor faces and their intersections.

For a nonnormal pushout, tensor (6.7) by $\Theta^{m_0n}$ and take Euler characteristics. We obtain

$$
\chi(P,\Theta^{m_0n})
=\chi(P^\nu,\nu^*\Theta^{m_0n})
+\chi(C,\Theta^{m_0n}|_C)
-\chi(C^\nu,\nu^*\Theta^{m_0n}|_{C^\nu}).
\tag{10.6}
$$

The right side ranges over a finite list because the number of star and face orbits is bounded by the chosen periodic decompositions. Thus the Hilbert polynomials of $P$, $P^\nu$, $C$, and $C^\nu$ belong to finite sets.

The multiplication tables are bounded as well. Choose the finite theta-weight generators in degrees at most a common $d$. Products are monomials times units, with exponents drawn from the finite set of differences of support-function values on representative cells. Conductor maps discard weights not lying on the relevant face and multiply the surviving ones by period units. Consequently a fixed finite list of generators and relations presents every normalization-conductor diagram.

This finite list gives an explicit parameter space. Take the product of the Hilbert schemes for $P^\nu$, $C^\nu$, and $C$ with the graph schemes for the two conductor arrows, using the polynomials just bounded. Incidence, finiteness, face-pairing, and the conductor equalizer are conditions on finitely many universal maps. Associativity and the cocycle are equality loci of morphisms between projective families; flatness and the prescribed Hilbert polynomial are open conditions. Thus the admissible diagrams occupy a finite union of locally closed finite-type subschemes.

The construction does not assert that every point of this parameter space is a Mumford object. It asserts that every Mumford object maps into it and that the universal monomial equations cut out a finite-type subspace containing all such points. Chapter 11 starts from that explicit subspace and then uses the inverse theorem to identify its completed moduli functor.

**Theorem 10.1 (bounded conductor presentation).** For fixed PEL data, level, paired frames, and admissible periodic decompositions, every cusp model admits a normalization-conductor presentation embedded in fixed projective spaces, with Hilbert polynomials, graph polynomials, degrees of finite maps, numbers of components, and degrees of defining equations drawn from finite lists. Formation of the presentation commutes with base change.

### 10.4 Pushouts and nonnormal fibers

Conversely, begin with a diagram $C^\nu\to P^\nu$ and $C^\nu\to C$ from the bounded list, with the first arrow a closed immersion and the second finite, satisfying the face-pairing equivalence relation. On affine patches form

$$
\mathcal O_P
=\mathcal O_{P^\nu}\times_{\mathcal O_{C^\nu}}\mathcal O_C.
\tag{10.7}
$$

Surjectivity of $\mathcal O_{P^\nu}\to\mathcal O_{C^\nu}$ makes these affine pushouts compatible with localization. They glue to a finite type proper scheme $P$. Exactness of (6.7) and the monomial-basis argument prove flatness over the parameter base. The torus action, PEL endomorphisms, and theta line descend when their two restrictions to $C^\nu$ agree.

The fiber may be nonnormal even though every star is normal. That is intended. Normalizing it again loses the periodic face identification and therefore loses the semiabelic object. All subsequent constructions retain the entire square (10.3).

## 11. A finite-type algebraic cusp atlas

### 11.1 Construction from explicit monoid algebras

Fix one framed cusp and one regular cone $\sigma$. Let $S$ be the finite-type smooth parameter ring for the abelian Raynaud part, the unit periods, rigidifications, and level data. Begin with the algebraic toric chart

$$
U_\sigma=\operatorname{Spec}S[P_\sigma],
\tag{11.1}
$$

In the Hilbert--Blumenthal boundary case this coefficient ring is explicit. Let $\Lambda$ be the quotient of $Y\otimes_{\mathcal O_F}X$ by the polarization-symmetry relations. Unit periods form the split torus $T_\Lambda=\operatorname{Hom}(\Lambda,\mathbf G_m)$. The rigidified frames are a finite etale scheme $E$ over the standing coefficient base. On an affine frame component,

$$
S=\mathcal O(E)[\Lambda],
\tag{11.1a}
$$

localized at the finitely many determinant and level units. It is smooth. For a general PEL cusp one tensors this ring with an affine smooth chart of the abelian and extension moduli. Thus no complete local ring is being silently treated as a finite-type coefficient ring.

not with a completed deformation functor. Over it, construct the finite collection of normalized star algebras $S[P_\sigma][Q_C]$ from (6.1). The theta algebra is generated in degrees at most $d$ by Theorem 10.1, so its relative Proj is of finite presentation. Glue stars along common face localizations and impose the finitely many period face pairings by the equalizer (10.7). This produces a projective finite-type family

$$
P_\sigma^{\mathrm{alg}}\longrightarrow U_\sigma.
\tag{11.2}
$$

All coefficients in its equations are either universal units from $S$ or explicit monomials $q^p$. Associativity, polarization symmetry, the $\mathcal O_F$-action, and level compatibility are finite polynomial identities and hold universally because they hold in the defining period algebra.

Varying the finitely many cusp, cone, and cell-orbit types and adjoining the finite paired-frame choices gives a finite disjoint union $U^{\mathrm{fr}}$. It is a finite-type atlas candidate before any moduli quotient is invoked.

### 11.2 Algebraizing the conductor pushout

The normalization $P^{\nu,\mathrm{alg}}_\sigma$ and the face union $C^{\nu,\mathrm{alg}}_\sigma$ are explicit projective toric families. The paired-face quotient $C^{\mathrm{alg}}_\sigma$ is of finite presentation, and the quotient map from $C^{\nu,\mathrm{alg}}_\sigma$ is finite because only finitely many face orbits are identified. On each invariant affine open define the equalizer algebra (10.7). Since the right restriction map is surjective and every algebra is finitely presented over $S[P_\sigma]$, the equalizer is finitely presented: take the generators of the normalization algebra together with lifts of generators of $C$, and impose the finite relations plus equality of their restrictions.

The affine equalizers glue, commute with arbitrary base change, and give (11.2). Properness follows either from its relative theta Proj presentation or from the valuative argument of Section 6.3. This is algebraic cusp effectivity: the complete Mumford object is the completion of a family already constructed over a finite-type base.

For the rank-one cusp the construction is visible without parameter schemes. Begin with $U=\operatorname{Spec}S[q]$. Take $n$ copies of the standard projective model covered by $S[q,X_i,Y_i]/(X_iY_i-q)$, normalize the special-fiber stars, and pair $Y_i=0$ with $X_{i+1}=0$ cyclically using the universal unit period. The finite equalizer produces a projective $n$-gon family over $S[q]$. Its completion at $q=0$ is the usual Tate--Mumford family, but its existence over $S[q]$ was proved directly. The higher-dimensional construction is the same finite operation indexed by cells and faces.

### 11.3 Proof of the fine saturated charts

We now prove the logarithmic chart assertion without using singularity ideals. At a point on the orbit indexed by a face $\tau\preceq\sigma$, the base has an open neighborhood

$$
\operatorname{Spec}S[P_{\sigma,\tau}].
\tag{11.3}
$$

Section 5.1 proved directly that $P_{\sigma,\tau}$ is finitely generated, integral, and saturated. Its sharp quotient is the dual monoid of $\sigma/\tau$ and is free because the fan is regular. Therefore the divisorial logarithmic structure is fs, and the map to the coefficient stratum is log smooth.

For the family, a normalized star at a cell face $D\preceq C$ has chart by the localized saturation

$$
Q_{C,D}^{\mathrm{sat}}
=Q_C^{\mathrm{sat}}+(Q_C^{\mathrm{sat}}\cap D^\perp)^{\mathrm{gp}}.
\tag{11.4}
$$

It is fs by the same lattice-cone proof. On a conductor face the two characteristic monoids identify with the same face submonoid; the period multiplier is a unit and does not change the characteristic. The pushout log structure is therefore the equalizer of fs face charts. Its stalk is the amalgam prescribed by the cell complex, and saturation can be checked in the common group completion: an element whose positive multiple lies in every adjacent saturated star monoid lies in each of them and hence in their intersection.

Thus the base and family charts are fs and saturated before any deformation-theoretic comparison. The constructed boundary ideal is the image of the positive elements of $P_\sigma$. It cuts out the expected union of toroidal strata and is compatible with every face map.

The saturation assertion also survives the conductor quotient. Suppose $r\gamma$ is represented by a descended monomial for some $r>0$. On every normalized star, saturation gives a monomial representative of $\gamma$. On a paired face, the two representatives have equal $r$th powers. Their quotient is an $r$-torsion unit. The paired-frame lattice contains precisely the required roots and the rigidification fixes that torsion unit to one. Hence the representatives descend to the pushout. This rules out a hidden nonsaturated characteristic created solely by nonnormal gluing.

### 11.4 Comparison with the complete Mumford family

Complete (11.1) along a stratum and, at a geometric point $z$, complete the smooth coefficient parameters. The result is $S_z[[P_\sigma]]$. Completion of the finitely generated star algebras gives exactly (6.3); finite conductor equalizers commute with completion because completion is exact on finite modules over a noetherian ring. Hence

$$
\widehat{P_\sigma^{\mathrm{alg}}}_z
\simeq P^{\mathrm M}_{S_z[[P_\sigma]]}.
\tag{11.5}
$$

Theorem 8.1 identifies the completed functor of the algebraic atlas with the full logarithmic semiabelic deformation functor. In particular the map from $U^{\mathrm{fr}}$ to the framed moduli groupoid is representable and formally etale. It is also locally of finite presentation by its explicit equations. The infinitesimal lifting criterion then makes it etale: for a finite presentation morphism, compatible unique lifts over square-zero extensions give vanishing relative differentials and flatness, and the Jacobian criterion on the smooth monoid charts yields etaleness.

After shrinking around the chosen cusp stratum, this map is an atlas because its completed map at every geometric cusp point is an isomorphism and the complement of its image would have a closed point. At such a point completion would again show that the point is in the image, a contradiction.

**Theorem 11.1 (algebraic cusp effectivity).** The framed cusp groupoid has a noncircular finite-type etale atlas built from the explicit algebras $S[P_\sigma]$ and their finite normalization-conductor presentations. Its completed family is the Mumford family, and its base and universal-family logarithmic charts are fs and saturated.

### 11.5 Why Fitting ideals do not suffice

The zeroth Fitting ideal of $\nu_*\mathcal O_{P^\nu}/\mathcal O_P$ locates the conductor support, and higher Fitting ideals stratify its rank. They do not determine the monoid law, its saturation, the paired-face maps, or the period units. For example, $k[t^2,t^3]$ and a reduced node both have singularity supported at one point, while their characteristic monoids and normalizations are different.

Our construction uses Fitting ideals only after the monomial atlas exists, to express bounded locally closed conditions inside Hilbert and graph schemes. The fs chart assertion comes from (11.3) and (11.4), and the nonnormal gluing comes from the explicit conductor maps. There is therefore no circular passage from an unknown compactification to its singularity strata and back to the charts meant to construct it.

## 12. Ramified conductor descent

### 12.1 The tensor square of a ramified trait

Let $V\to V'$ be a finite faithfully flat extension used to split a cusp and choose paired frames. It may be ramified. Put

$$
W=V'\otimes_VV',
\qquad
W_0=W_{\mathrm{red}},
\qquad
\widetilde W=\operatorname{Nor}(W_0).
\tag{12.1}
$$

If the generic extension is Galois with group $\Delta$, then $\widetilde W$ is the product of the trait normalizations indexed by generic embeddings, although several branches can meet over the closed point. Let

$$
\mathfrak d
=\operatorname{Ann}_{W_0}(\widetilde W/W_0),
\quad D=\operatorname{Spec}(W_0/\mathfrak d),
\quad \widetilde D=\operatorname{Spec}(\widetilde W/\mathfrak d).
\tag{12.2}
$$

Then

$$
W_0=\widetilde W\times_{\mathcal O_{\widetilde D}}\mathcal O_D.
\tag{12.3}
$$

The ordinary generic descent isomorphism gives, on each normalized component of $\widetilde W$, an isomorphism between the two pullbacks of the framed Mumford family. The issue is to prove that these componentwise isomorphisms factor through $W_0$, and then through the nilpotent thickening $W$.

For the model extension $V'=V[s]/(s^e-\pi)$, the tensor square has coordinates $s_1,s_2$ with $s_1^e=s_2^e$. Generically its components are the graphs $s_2=\zeta s_1$, but they all meet at $s_1=s_2=0$. In wild or nonsimple extensions nilpotents can occur as well. Thus a list of generic deck transformations gives neither a map at the meeting point nor a map through the nilradical. The next three sections supply these two extensions separately.

### 12.2 The actual conductor factorization map

Let $P_1$ and $P_2$ be the two pullbacks to $W_0$, and normalize them after base change to $\widetilde W$. On the component labelled by $g\in\Delta$, the fan-equivariant framed isomorphism sends a weight generator to

$$
\phi_g^\#(e_x)=u_g(x)e_{g x},
\qquad u_g(x)\in\widetilde W^\times.
\tag{12.4}
$$

Let $C_i\subset P_i$ and $C_i^\nu\subset P_i^\nu$ be their conductors. On a paired face $E$, the coordinate ring is spanned by precisely the weights $x$ lying in the face semigroup $Q_E$; weights outside $Q_E$ restrict to zero. Fan equivariance gives $gQ_E=Q_{gE}$, and the paired-frame period law gives

$$
u_g(x+y)=u_g(x)u_g(y)
\quad\text{on }Q_E,
\tag{12.5}
$$

including the prescribed monomial factor when the two representatives differ by a period. Therefore (12.4) restricts to an algebra homomorphism on every conductor face. On an intersection of faces the two restrictions agree, because both are restrictions of the same weight formula.

We now construct the missing factorization. On a face $E$, write its algebra over $D$ as

$$
A_{i,E,D}
=\bigoplus_{x\in Q_E}\mathcal O_D e_x
\big/\text{the monomial multiplication relations}.
\tag{12.6}
$$

The residues of the branch units $u_g(x)$ define elements $\bar u(x)\in\mathcal O_D^\times$ for $x\in Q_E$. To prove this descent assertion, split $u_g(x)$ into its smooth unit-period factor and its Kummer constant. The smooth factor already satisfies ordinary descent. A Kummer constant can differ between two normalized branches only by the root of unity attached to a fractional exponent. A weight surviving on their common conductor face has zero order in that fractional normal direction; its exponent is integral there, so the root-of-unity quotient is one. Weights with nonzero fractional normal order restrict to zero. Hence the tuples of coefficients agree over $\widetilde D$ exactly on all surviving weights and belong to the equalizer (12.3).

We obtain face algebra maps

$$
\theta_{E,D}^\#:A_{2,E,D}\longrightarrow A_{1,gE,D},
\qquad e_x\longmapsto\bar u(x)e_{gx}.
\tag{12.7}
$$

Equation (12.5) proves multiplicativity. Restriction to a smaller face discards the same nonface weights on both sides, so the maps (12.7) glue to a map $\theta_{C,D}$ on the conductor quotient.

Let $\overline P_i=P_i\times_{W_0}D$, let $\overline P_i^\star$ be its finite normalized-star cover, and let $\overline C_i^\star\to\overline C_i$ be its conductor diagram. On invariant affine opens the family pushout is the genuine equalizer

$$
\mathcal O_{\overline P_i}
=\mathcal O_{\overline P_i^\star}
\times_{\mathcal O_{\overline C_i^\star}}
\mathcal O_{\overline C_i}.
\tag{12.8}
$$

The maps $\phi_g$ restrict to $\overline P_i^\star\times_D\widetilde D$, while (12.7) gives the conductor map. Their restrictions to $\overline C_i^\star$ agree weight by weight. The universal property of (12.8) therefore gives the actual factorization map

$$
\psi_D^\#:
\mathcal O_{\overline P_2}
\longrightarrow
\mathcal O_{\overline P_1}.
\tag{12.9}
$$

Pulling (12.9) to $\widetilde D$ recovers the restriction of every $\phi_g$. Thus the normalized descent arrow really factors through the conductor base. Merely saying that the arrows agree generically would not imply this at a ramified closed point.

### 12.3 Descent through the reduced pushout

Use (12.3) on every finite coordinate module in the normalization-conductor presentation. The arrows $\phi_g$ over $\widetilde W$ and $\psi_D$ over $D$ agree over $\widetilde D$ by construction. Hence they give a unique arrow

$$
\psi_0:p_1^*P_{V'}|_{W_0}
\xrightarrow{\sim}
p_2^*P_{V'}|_{W_0}.
\tag{12.10}
$$

Apply the same equalizer to the inverse componentwise arrows to see that $\psi_0$ is an isomorphism. The $\mathcal O_F$-action, polarization, theta line, and level frame commute with (12.10), since their monomial formulas commute on $\widetilde W$ and on $D$.

On the triple tensor product, the two composites agree after normalization: there they are the deck transformations $gh$. They agree on its conductor by the multiplicative identity

$$
u_{gh}(x)=u_g(hx)u_h(x).
\tag{12.11}
$$

The pushout uniqueness then proves the cocycle over the reduced tensor cube.

### 12.4 Lifting across the nilradical and the cocycle

Let $J=\sqrt0\subset W$. Filter $W$ by $W/J^n$. Suppose the descent isomorphism has been constructed modulo $J^n$. The two pullbacks are logarithmic semiabelic objects over the same strict fs chart, and their reductions are identified. Theorem 7.1 lifts the isomorphism uniquely across the square-zero ideal $J^n/J^{n+1}$. Induction gives

$$
\psi:p_1^*P_{V'}\xrightarrow{\sim}p_2^*P_{V'}
\quad\text{over }W.
\tag{12.12}
$$

On the tensor cube, the two cocycle composites have the same reduction. Their quotient is an automorphism reducing to the identity. Full faithfulness in Theorem 8.1 says it comes from an automorphism of the framed one-motive; the paired frame and rigidification make that automorphism trivial. Therefore the cocycle holds over the entire nonreduced tensor cube.

### 12.5 fpqc descent of all structures

Finite faithfully flat descent is effective for schemes that are projective with a chosen ample line: descend the graded algebra

$$
\bigoplus_{n\ge0}f_*\Theta^{mn}
\tag{12.13}
$$

for a common sufficiently large $m$, then take relative Proj. Quasi-coherent algebras and invertible modules satisfy equalizer descent, and multiplication descends because it is a morphism of such modules. The action, $\mathcal O_F$-endomorphisms, polarization, level structure, conductor square, and logarithmic chart are all morphisms of finite presentation and descend with their identities.

The descended line is relatively ample: ampleness is fpqc local on the base for an invertible sheaf on a proper finitely presented morphism. Concretely, after the finite flat pullback some power gives a closed immersion; the norm of its evaluation determinants gives a power whose evaluation is surjective before pullback, hence everywhere.

**Theorem 12.1 (ramified conductor descent).** A framed algebraic cusp family with equivariant fan and paired-frame descent data descends effectively through any finite flat splitting extension, even when the tensor square is ramified and nonreduced. The descent is compatible with normalization, conductors, fs logarithmic charts, PEL structures, and the relatively ample family theta line.

## 13. Overlap equivalence and algebraization

### 13.1 Common faces and changes of cusp

Two cone charts for the same cusp overlap along unions of common faces. For $\tau=\sigma_1\cap\sigma_2$, both restrictions are obtained by localizing at the monomials vanishing on $\tau^\perp$, so (5.11) gives a canonical isomorphism. On triple intersections the isomorphisms are identities on the common localized period algebra and hence satisfy the cocycle.

Different cusp labels may describe the same degeneration. An isomorphism of cusp labels is an $\mathcal O_F$-linear isomorphism of the symplectic lattice carrying the isotropic ideal, polarization pairing, and level orbit of one label to those of the other. It induces

$$
X_b\xrightarrow{\sim}X_{b'},
\quad Y_b\xrightarrow{\sim}Y_{b'},
\quad M_b\xrightarrow{\sim}M_{b'},
\quad C_b\xrightarrow{\sim}C_{b'}.
\tag{13.1}
$$

The fan collection is equivariant, so a cone is carried to a cone after passing to a common subdivision. Formulae (5.9), (6.4), and (6.5) are invariant under (13.1). They give an algebraic isomorphism of cusp families, including their normalization-conductor diagrams and theta lines.

### 13.2 Exhaustion of isomorphisms

We prove that the preceding arrows are all the overlap arrows. Suppose geometric points in two cusp charts give isomorphic logarithmic semiabelic PEL objects. The identity component of the smooth locus recovers the semiabelian scheme. Its maximal torus recovers $X$, the quotient recovers the abelian part, and the group of periods recovers $Y$. The polarization recovers the pairing, while the level orbit recovers the cusp label modulo its declared arithmetic stabilizer.

The intrinsic base log structure recovers the face of the monodromy cone: precisely those $p$ mapping to units form the face orthogonal. The normalized-star incidence complex recovers the periodic decomposition restricted to that face. Therefore the two points are related by a cusp-label isomorphism and lie in the associated common-face overlap.

For families over a reduced base, the assertion follows fiberwise and then on an open neighborhood because the lattices and face types are locally constant. For nilpotent thickenings, Theorem 8.1 says an isomorphism is uniquely the one induced from the extracted one-motives. Thus the overlap groupoid is exhausted on all test rings, not only on geometric points.

This proof also gives quasi-finiteness of the overlap relation. Neatness removes stabilizers on nonzero cones, and the imposed level leaves only a finite group at the interior chart. The diagonal is unramified by full faithfulness and proper by the valuative uniqueness in Section 6.3; hence it is finite.

### 13.3 Separated gluing

Let $U$ be the disjoint union of the interior chart and the finite-type cusp atlases. Let $R\rightrightarrows U$ be the overlap relation just described. Both arrows are etale: on a common face they are toric localizations followed by lattice isomorphisms, and at completed local rings this is also immediate from (8.3). The relation is effective and its diagonal is finite.

The etale quotient $U/R$ is an algebraic space of finite type. With neat level it is a scheme. To see this without a general quotient assertion, choose on each fan a projective support function and take a large common power of the associated line. Its invariant sections give an affine neighborhood of every finite orbit: select a monomial section nonzero on that orbit and multiply its translates under the finite residual group. These invariant affine neighborhoods descend and cover the quotient.

Separatedness follows from the trait criterion. If two lifts of a trait agree on its generic point, their generic one-motives agree. The valuation vector lies in a unique smallest fan cone, and separatedness of the toric chart makes the monodromy extensions agree. Full faithfulness in Theorem 8.1 then identifies the complete semiabelic objects. Since the overlap relation already contains that cusp and face isomorphism, the two lifts coincide.

### 13.4 Properness from complete fans

Take a map from the fraction field $K$ of a valuation ring $V$ to the interior moduli space. After a finite faithfully flat extension $V'/V$, semi-stable reduction of the polarized abelian variety supplies a Raynaud extension and a polarized one-motive. The valuation pairing is a point of the closed positive cone. Completeness of the fan places it in some cone $\sigma$; if it lies on a wall, either adjacent chart gives the same point on their face overlap.

The Mumford construction produces an extension over $V'$. Theorem 12.1 descends it over $V$, including in the ramified case. Uniqueness follows from separatedness. Thus the quotient satisfies the valuative criterion for properness. Because it is of finite type over the noetherian coefficient base, it is proper.

At no point was a merely formal cusp attached directly to the interior. The cusp charts were first algebraized in Chapter 11, their ramified descent was proved in Chapter 12, and only then were they glued.

## 14. Poincare, theta, and determinant lines

### 14.1 Three different lines

Three invertible sheaves enter the projectivity argument.

1. The Poincare bundle $\mathcal P$ lives on $G\times G^\vee$ and represents the universal biextension.
2. The theta line $\Theta$ lives on the universal semiabelic family $f:P\to\overline{\mathcal M}$ and polarizes its fibers.
3. A fan support function $\psi$ defines a line $\mathcal B_\psi$ on the toroidal base $\overline{\mathcal M}$.

The determinant

$$
\mathcal D_m=\det Rf_*\Theta^m
\tag{14.1}
$$

is a fourth line, again on the base. Neither $\mathcal D_m$ nor $\mathcal B_\psi$ is the theta line itself. Confusing them would make the vertical positivity argument meaningless: a line on $P$ cannot be intersected directly with a curve on the base.

### 14.2 The normalized semiabelic theta line

Rigidify $\mathcal P$ along both zero sections and impose the cubical identity. For the polarization $\lambda:G\to G^\vee$, the pullback $(1,\lambda)^*\mathcal P$ has a canonical symmetric cubical structure. If $L$ is a symmetric rigidified polarization line on the abelian locus, the theorem of the square, proved by comparing the two cubical biextensions, gives

$$
(1,\lambda)^*\mathcal P\simeq L^{\otimes2}.
\tag{14.1a}
$$

We use this canonical even power and, after the uniform divisibility already imposed in Section 10.2, denote it by $\Theta$. No choice of a square root is needed at the boundary.

On a Raynaud extension, the biextension trivialization along $Y\times X$ is the unit-period part $u(y,x)$. Multiplying it by the monomial part $q^{B(y,x)}$ gives precisely the factor of automorphy (6.5). Thus the Poincare construction and the polyhedral construction yield the same line $\Theta$ on the normalized stars. The cubical identity is the cocycle condition for the period action, so $\Theta$ descends through paired conductor faces.

Normalize $\Theta$ along the identity section of the semiabelian locus. Any two extensions with the same normalization differ by a line pulled back from the base. The rigidification kills that line: its pullback to the identity is trivial with a specified trivialization. Hence the semiabelic theta line is unique and compatible with base change, face restriction, coefficient descent, and normalization-conductor pushout.

On a nonnormal fiber, uniqueness is checked on the conductor square. Two candidate lines agreeing on $P^\nu$ differ by descent scalars on $C^\nu$. The cubical period law makes those scalars characters of the period lattice; evaluation at the rigidified identity makes the character one. Thus the line, not merely its numerical class, descends uniquely.

### 14.3 Determinant of cohomology

For $m$ divisible by the integer $m_0$ of Section 10.2, $\Theta^m$ has no higher cohomology on every normalized toric star and on every conductor face. This follows from the lattice-point resolution associated with a regular triangulation. Weight by weight, the Cech complex is the augmented cellular cochain complex of the subcomplex of cells containing a fixed lattice point. That subcomplex is a convex star and is contractible. Hence the complex is exact in positive degree. Apply (6.7), or the full face resolution when more than two stars meet, to obtain the same vanishing on the nonnormal semiabelic fiber. The ranks are the finite lattice-point counts and are constant, so cohomology and base change make $f_*\Theta^m$ locally free.

Consequently

$$
\mathcal D_m=\det f_*\Theta^m.
\tag{14.2}
$$

If the normalized-star Cech resolution is used before taking determinants, one obtains the canonical formula

$$
\mathcal D_m
\simeq
\bigotimes_C\det f_{C*}\Theta_C^m
\otimes
\bigotimes_E(\det f_{E*}\Theta_E^m)^{-1}
\otimes\cdots,
\tag{14.3}
$$

where the alternating product runs over star intersections. This formula proves compatibility with nonnormal fibers rather than assuming normality.

The PEL endomorphisms act on the perfect complex $Rf_*\Theta^m$, and paired-frame symmetries permute its theta-weight basis. Taking determinants gives a genuine character after the fixed power $m_0$ has killed projective multipliers.

### 14.4 Boundary transition characters

On a cusp chart, choose the theta-weight basis $\{\vartheta_x\}$ in a fundamental polytope. On an overlap induced by a period $y$, (6.5) gives

$$
\vartheta_x\longmapsto
u(y,x)u(y,a(y))^m
q^{B(y,x)+mB(y,a(y))}
\vartheta_{x+m\lambda(y)}.
\tag{14.4}
$$

Taking the determinant over all representatives gives a unit times a monomial $q^{\kappa_m(y)}$. The exponent $\kappa_m(y)\in M$ is a quadratic polynomial in $m$ whose leading term is positive by the polarization. On a conductor face, weights outside that face vanish and the alternating determinant formula (14.3) cancels the missing weights. Hence the restriction of $\kappa_m$ is exactly the determinant exponent for the face.

If $S_m$ is the finite set of degree-$m$ weight representatives, the exponent is explicitly

$$
\kappa_m(y)
=\sum_{x\in S_m}
\bigl(B(y,x)+mB(y,a(y))\bigr).
\tag{14.4a}
$$

Changing the fundamental polytope permutes $S_m$ and adds a global linear character, which changes the local trivialization but not the line. On a fan wall the two sums restrict to the sum for the common face by the alternating cancellation just described. This proves, rather than presumes, that the exponents form a piecewise linear support datum.

The collection of these exponents is a piecewise linear function on the fan. Call it $\chi_m$. Twisting $\mathcal D_m$ by the base fan line associated with $-\chi_m$ removes its boundary transition monomials. What remains has unit transition functions and descends across all cusp overlaps. This calculation is the bridge between the determinant line and a line on the toroidal base; it does not identify either with the family theta line.

### 14.5 Base change and conductor compatibility

The determinant of a perfect complex commutes with arbitrary base change. In our range this is also visible from the locally free module $f_*\Theta^m$. For a conductor square, the exact triangle associated with (6.7) gives

$$
\det Rf_*\Theta^m
\simeq
\det Rf_*^\nu\nu^*\Theta^m
\otimes\det Rf_{C*}\Theta_C^m
\otimes(\det Rf_{C^\nu*}\Theta_{C^\nu}^m)^{-1}.
\tag{14.5}
$$

Every isomorphism in (14.5) is functorial. It therefore respects the ramified descent arrow (12.12) and its cocycle. The corrected determinant line

$$
\mathcal H_m=\mathcal D_m\otimes\mathcal B_{-\chi_m}
\tag{14.6}
$$

is a globally defined line whose boundary trivializations are units. It supplies the horizontal factor in the ample line constructed next.

## 15. Positivity and projective gluing

### 15.1 Horizontal positivity

On the interior, a sufficiently high theta power embeds every polarized abelian scheme in a fixed projective space after a finite theta-frame cover. The multiplication maps among theta functions determine the embedded group law and the $\mathcal O_F$-action. Hence the map to the relevant Hilbert-and-graph parameter scheme is quasi-finite: two points with the same embedded equations have the same rigidified polarized PEL object, and neat level removes automorphisms.

The Plucker line on the Hilbert parameter scheme pulls back to a positive tensor combination of determinant lines $\det f_*\Theta^m$. To verify this, present the degree-$m$ ideal as the kernel of the evaluation map from a fixed vector space to $f_*\Theta^m$; the determinant of the quotient is the Plucker coordinate. The finite theta-frame group is removed by tensoring all conjugates. Therefore a fixed positive tensor product $\mathcal H$ of corrected lines (14.6) has positive degree on every complete curve meeting the interior and not contracted by the PEL moduli map.

No curve in the interior is contracted: the polarized family with full neat level is recovered from its theta multiplication tables. Thus

$$
\deg_C\mathcal H>0
\tag{15.1}
$$

for every complete curve $C$ contained in the interior. The same construction is relatively ample over the affine coarse invariant parameter space, so it also separates horizontal tangent vectors.

### 15.2 Vertical fan positivity

Let $\psi$ be the integral strictly convex support function of the projective fan. The associated line $\mathcal B_\psi$ has, on $U_\sigma$, a generator whose transition to $U_{\sigma'}$ is the monomial with exponent $\psi_{\sigma'}-\psi_\sigma$. Its restriction to a toric fiber is the toric line of the support polytope.

For a torus-invariant curve corresponding to a codimension-one wall, its degree is the jump of the slopes of $\psi$ across that wall. Strict convexity makes this jump positive. Every effective curve contracted to a point of the cusp stratum is numerically a nonnegative combination of invariant curves: successively specialize it under one-parameter subgroups of the torus; properness of the Chow parameter space preserves its numerical class and ends in an invariant cycle. Hence

$$
\deg_C\mathcal B_\psi>0
\tag{15.2}
$$

for every nonzero vertical curve.

### 15.3 Mixed curves and a uniform domination bound

A mixed curve moves both in a cusp stratum and in toric directions. Neither (15.1) nor (15.2) alone controls it because a chosen extension of a horizontally positive line can have negative boundary degree.

On each of the finitely many projective cusp atlases, choose generators of the relative cone of curves from the finitely many normalized star and conductor types. Decompose a curve class as

$$
[C]=[C]_{\mathrm h}+[C]_{\mathrm v}
\tag{15.3}
$$

after mapping to the Hilbert-and-graph parameter space and the toric base. The kernel of both maps is zero: a curve with constant theta multiplication tables and constant monodromy chart is a constant logarithmic one-motive by Theorem 8.1.

The slice of the closed cone generated by effective curves on which

$$
\deg\mathcal H+\deg\mathcal B_\psi=1
\tag{15.4}
$$

is compact. On that slice, the negative part of either degree is bounded. Equivalently, for each chart there is an integer $c$ such that

$$
\deg_C(\mathcal H^c\otimes\mathcal B_\psi)>0
\tag{15.5}
$$

for every curve not purely vertical, while (15.2) handles purely vertical curves.

Here is a scheme-theoretic proof of the uniform bound. The bounded theta multiplication tables define a morphism $h$ from the projective cusp atlas to a projective Hilbert-and-graph scheme. The support-function monomials define a morphism $t$ to the projective toric scheme of the fan polytope. If a geometric fiber of $(h,t)$ had positive dimension, a curve in it would have constant theta algebra and constant monodromy. Theorem 8.1 would make its polarized logarithmic one-motive constant, while full faithfulness would make the universal family constant, contradicting the existence of the curve in a fine chart. Thus $(h,t)$ is proper and quasi-finite, hence finite.

For ample lines $O_H(1)$ and $O_T(1)$ on the two targets, every line

$$
h^*O_H(c)\otimes t^*O_T(1)
\tag{15.5a}
$$

is ample for all sufficiently large $c$: embed the product by $O_H(c)\boxtimes O_T(1)$ and pull it back by the finite morphism. The pullbacks differ from $\mathcal H^c$ and $\mathcal B_\psi$ only by fixed boundary characters already corrected in (14.6). Absorbing those finitely many characters increases $c$ by a bounded amount. This proves (15.5) and also separates higher-dimensional subschemes and tangent vectors, so the argument does not rely solely on a numerical curve criterion.

There are finitely many cusp-chart and overlap types, so take the maximum of their integers $c$. After also taking a common symmetry power, the line

$$
\mathcal A=\mathcal H^c\otimes\mathcal B_\psi
\tag{15.6}
$$

is positive on horizontal, vertical, and mixed curves and gives a closed immersion on every chart after one common power.

### 15.4 Descent of the ample line

On a framed cover, form the tensor product of all deck transforms of $\mathcal A$. Permutation of the factors gives a canonical linearization, and the cocycle is literal. The conductor determinant formula and the fan transition calculation show that the linearizations agree on normalized branches and on conductor faces. Theorem 12.1 therefore descends the line through ramified coefficient extensions and paired-frame quotients.

It is ample after descent. Indeed ampleness is fpqc local for a proper finitely presented morphism. Alternatively, choose a power which is very ample after the finite flat cover, take norms of a finite set of separating sections, and obtain a finite morphism to projective space downstairs; positivity on every fiber makes that morphism a closed immersion after another power.

The overlap isomorphisms of Chapter 13 preserve $\mathcal H$, $\mathcal B_\psi$, and their rigidifications. Hence the descended lines glue to a global ample line on the toroidal quotient. The quotient is therefore projective, not merely proper.

## 16. The toroidal compactification theorem

### 16.1 Construction and completed-local comparison

Let $\mathcal M$ be the Hilbert--Blumenthal moduli scheme for the standing PEL datum and neat level, and let $\Sigma$ be the equivariant regular projective fan collection of Theorem 4.2. Glue the interior to the algebraic cusp atlases of Theorem 11.1 using the exhaustive overlap equivalence of Chapter 13, and descend framed branches by Theorem 12.1. Denote the result by

$$
\mathcal M\hookrightarrow\mathcal M_\Sigma^{\mathrm{tor}}.
\tag{16.1}
$$

At a geometric point $z$ of the stratum indexed by $\sigma$, the completed local ring is

$$
\widehat{\mathcal O}_{\mathcal M_\Sigma^{\mathrm{tor}},z}
\simeq S_z[[P_\sigma]]^{H_z},
\tag{16.2}
$$

with $H_z=1$ on a nonzero cone under the neat regular hypothesis. Under this isomorphism the completed universal family is the Mumford family of the universal logarithmic one-motive. The statement holds on all nilpotent quotients of the completed ring, not only after reduction.

### 16.2 Smoothness, boundary, and universal objects

The monoid of a regular cone is free after removing its unit face. Since $S_z$ is smooth, (16.2) is a formal power-series ring in smooth parameters and boundary monomials. The algebraic chart of Section 11.3 is correspondingly smooth, and its boundary is a relative normal-crossings divisor. Thus $\mathcal M_\Sigma^{\mathrm{tor}}$ is smooth over every coefficient locus where the interior PEL problem is smooth.

The boundary strata are indexed by cusp labels and cone orbits, with closure relations given by face inclusion. The universal object is a proper flat semiabelic family

$$
f_\Sigma:P_\Sigma\longrightarrow\mathcal M_\Sigma^{\mathrm{tor}}
\tag{16.3}
$$

equipped with its semiabelian action, $\mathcal O_F$-action, polarization, level orbit, intrinsic fs logarithmic structure, and relatively ample normalized theta line. Its boundary fibers may be nonnormal. Their normalizations are the star unions and their original fibers are recovered from the full conductor square.

Every formation in (16.3) commutes with restriction to a boundary face, strict nilpotent base change, traits, and the finite flat coefficient changes used to split cusps.

### 16.3 Projectivity and descent

Chapter 13 proves properness and finite type. Chapter 15 constructs a global ample line by combining the corrected determinant line with the projective fan line and proves its fpqc descent. Therefore $\mathcal M_\Sigma^{\mathrm{tor}}$ is projective over the coefficient base.

We record the complete conclusion.

**Theorem 16.1 (toroidal compactification and gluing).** For every equivariant regular projective admissible fan collection $\Sigma$, the Hilbert--Blumenthal PEL moduli scheme with neat level has a smooth projective toroidal compactification $\mathcal M_\Sigma^{\mathrm{tor}}$. Its formal completion along every cusp is the corresponding framed Mumford quotient, its completed local rings are (16.2), and its universal semiabelic family, conductor presentation, PEL structures, intrinsic fs log structure, and theta line are compatible on all overlaps and under coefficient descent.

The proof has four logically prior inputs, all established above: complete logarithmic period equivalence, bounded conductor presentation, algebraic cusp effectivity, and ramified conductor descent. Projectivity additionally uses the determinant, fan, and mixed-positivity arguments of Chapters 14 and 15.

### 16.4 Independence under refinement

If $\Sigma'$ refines $\Sigma$, every monoid chart for $\Sigma'$ maps to the chart for $\Sigma$ by the identity on the common lattice. The normalized family map is the toric modification prescribed by subdivision. Its conductor restrictions respect paired faces, so it descends to a proper morphism

$$
\mathcal M_{\Sigma'}^{\mathrm{tor}}
\longrightarrow\mathcal M_\Sigma^{\mathrm{tor}}
\tag{16.4}
$$

which is the identity on $\mathcal M$. It is projective because the relative support function of the subdivision supplies a relatively ample fan line.

For two fans, take their common projective regular refinement by Chapter 4. The two compactifications are therefore canonically birational through projective toroidal modifications, and their universal semiabelic objects agree on common completed face charts. Boundary constructions that are invariant under such refinement are consequently independent of the chosen fan.

## 17. Finite-type joining and the integral connecting slice

### 17.1 Joining a formal cusp to the good interior

We place the final construction in a form useful beyond one arithmetic application. Let $R$ be a complete discrete valuation ring with fraction field $K$ and residue field $k$, let $Y/K$ be a geometrically connected finite PEL frame cover of the Hilbert--Blumenthal interior, and let

$$
y_{\mathrm{sp}}:\operatorname{Spec}K\longrightarrow Y
\tag{17.1}
$$

be a point with split semistable reduction of a selected cusp type. Its period valuations choose a ray $\rho$ in the positive monodromy cone. Assume only that the torsion frames appearing in $Y$ are defined over the given completion field. Their division monomials then define the paired-frame lattice of (9.3); no additional root is to be adjoined.

Choose the fan of Theorem 4.2 with $\rho$ marked. The paired-frame compactification constructed in Chapter 16 has an algebraic branch whose completion is

$$
\operatorname{Spf}S'[[P_{\sigma}^{\mathrm{fr}}]],
\tag{17.2}
$$

and the valuation homomorphism of $y_{\mathrm{sp}}$ is a continuous map from this ring to $R$. Because $\rho$ is a ray of the fan, the map meets a single boundary divisor transversely after dividing by the common valuation multiplicity. The Kummer units, enhanced theta rigidification, polarization sign, and exact frames are the universal ones on this branch.

Let $Z\subsetneq Y$ be a proper closed subset. The issue is not to algebraize (17.2) in isolation; that was already done in Chapter 11. The issue is to put its chosen section in the same finite-type projective model as the good interior and to use a power of the same global ample line. The global quotient of Chapters 13--16 does exactly this.

Take the closure of the geometrically connected component of $Y$ in the paired-frame toroidal compactification and then its smooth regular fan refinement. Denote the resulting $R$-model by $\overline{\mathcal Y}$. It is smooth and projective, contains the good-reduction locus $\mathcal Y^{\mathrm{good}}$ as an open, and carries a relatively ample line $\mathcal A_R$ obtained from the global line (15.6). A common power is relatively very ample and is the base change of the global finite-dimensional section space. The section (17.1) extends by properness, and its completed branch is (17.2) by (16.2).

There is no completion-field enlargement in this operation. Normalization was taken in exactly the paired-frame function algebra specified by $Y$. Section 9.3 identifies its algebraic normalization before completion, and Theorem 12.1 descends it through precisely the recorded finite flat splitting ring. Therefore the completion field, valuation shell, Kummer classes, and framed one-motive of $y_{\mathrm{sp}}$ remain unchanged.

### 17.2 The finite-type joining theorem

We verify the avoidance clause needed for slicing. Let $\overline Z$ be the schematic closure of $Z$ in $\overline{\mathcal Y}$. The special fiber of the selected component is geometrically integral because $\overline{\mathcal Y}/R$ is smooth with geometrically connected generic fiber; the etale scheme of connected components is constant, and a connected smooth fiber is regular and hence its irreducible components are disjoint, so it is integral.

At the generic point $\eta_s$ of the special fiber, the local ring is a discrete valuation ring with uniformizer $\pi$. The ideal $I_Z$ of the schematic closure is $\pi$-saturated:

$$
\pi f\in I_Z\quad\Longrightarrow\quad f\in I_Z,
\tag{17.3}
$$

because $I_Z$ is the contraction of its localization after inverting $\pi$. If $I_Z$ vanished at $\eta_s$, every member would be divisible by $\pi$ there. Saturation would permit repeated division. Krull intersection would then make $I_Z$ zero after inverting $\pi$, contrary to $Z\ne Y$. Thus $\overline Z$ contains no special-fiber component.

The boundary also contains no component of the good special fiber. It follows that

$$
U_k=\mathcal Y_k^{\mathrm{good}}\setminus\overline Z_k
\tag{17.4}
$$

is a nonempty dense open. It contains a closed point. Over a finite residue field that closed point need not be rational, a distinction retained below.

**Theorem 17.1 (finite-type joining).** With the data of Section 17.1, there is one smooth projective finite-type $R$-model $\overline{\mathcal Y}$ satisfying all of the following.

1. It contains the good interior $\mathcal Y^{\mathrm{good}}$, and a relatively very ample line is a power of the global determinant--fan line.
2. The selected semistable point extends to an $R$-section. The completion at its boundary branch is the normalized paired-frame Mumford chart, and the section retains its completion field, valuation and Kummer shells, theta rigidification, polarization sign, and exact frames.
3. The open (17.4) is nonempty and dense for every proper closed $Z\subset Y$.
4. Every coefficient and descent isomorphism of the PEL frame cover extends to the model and the ample line.

The theorem follows from Chapters 9--16 and the saturation argument (17.3). It is a finite-type joining theorem: both the global section space and the local completed comparison come from the same algebraic projective model.

### 17.3 Relative slicing with a dense good open

We recall the slicing argument in enough detail to expose its hypotheses. Suppose the relative dimension of $\overline{\mathcal Y}/R$ is $n\ge2$, and let $\mathcal L$ be the relatively very ample power in Theorem 17.1. We seek $n-1$ sections whose common zero scheme is a smooth proper relative curve, passes through the selected semistable section with prescribed independent first jets, and has special fiber meeting $U_k$.

First work over $k$. Fix the finite subscheme $E$ consisting of the marked semistable point, one closed point of $U_k$, and any other imposed finite packet, together with first-order neighborhoods recording transverse jets. For $m$ large, restriction is onto:

$$
H^0(\overline{\mathcal Y}_k,\mathcal L^m)
\longrightarrow H^0(E,\mathcal L^m|_E).
\tag{17.5}
$$

Choose a random section in the affine space of lifts of the prescribed jet. For a closed point $x\notin E$ of degree $e$, failure of smoothness at $x$ imposes $n+1$ independent linear conditions once $m$ is large relative to $e$; its proportion is $|k|^{-(n+1)e}$. The number of degree-$e$ points is at most a constant times $|k|^{ne}/e$. Hence the sum of bad proportions is bounded by a convergent tail

$$
\sum_e O(|k|^{-e}/e).
\tag{17.6}
$$

Low-degree points are handled by the exact linear conditions, and very high degree points are excluded by writing a section as

$$
s=s_0+\sum_{i=1}^n h_i^p t_i,
\tag{17.7}
$$

in residue characteristic $p$: the derivatives of the $h_i^p$ vanish, so independent choices of $t_i$ make the derivatives independent while $s_0$ controls values. The probability that the remaining zero-dimensional singular locus contains a high-degree point tends to zero. Thus a smooth geometrically integral hypersurface with the prescribed jets exists.

Repeat inside each smooth cut. At the last step Bertini connectedness follows from the exact sequence

$$
0\to\mathcal O_X(-D)\to\mathcal O_X\to\mathcal O_D\to0
\tag{17.8}
$$

and the vanishing of $H^1(X,\mathcal O_X(-D))$, dual to a high positive twist. We obtain a smooth geometrically connected curve $C_k$ meeting $U_k$ and containing the imposed points.

Lift the sections over $R$. For $m$ still larger, cohomology vanishing makes

$$
H^0(\overline{\mathcal Y},\mathcal L^m)
\longrightarrow H^0(\overline{\mathcal Y}_k,\mathcal L^m)
\tag{17.9}
$$

surjective, also for sections constrained along the marked $R$-sections. Lift the cuts one by one. A lift of a special-fiber nonzerodivisor is a relative nonzerodivisor, so every intermediate intersection is flat. Its nonsmooth locus is closed and proper over $R$ and has empty special fiber. If it were nonempty, its proper image would contain the generic point and then the closed point, a contradiction. The final intersection

$$
\mathcal C\longrightarrow\operatorname{Spec}R
\tag{17.10}
$$

is therefore smooth, proper, and geometrically connected.

Let $C^\circ\subset\mathcal C_K$ be the complement of its finite intersection with $Z$ and the toroidal boundary. Put

$$
W=\mathcal C_k\cap U_k.
\tag{17.11}
$$

The imposed closed point shows that $W$ is nonempty; on the smooth connected curve it is dense. A closed point of $C^\circ$ whose closure specializes in $W$ carries good reduction and all the descended PEL frames. The selected marked section may meet the boundary in the special fiber, which is how its prescribed semistable degeneration is retained.

Finally, the construction is stable in a congruence neighborhood of the cutting tuple. Smoothness of the fixed special curve and full rank of the marked Jacobians depend on finitely many coefficients modulo a power of $\pi$. For a nearby tuple, the implicit function theorem over the complete ring continues the marked sections, and the reduction of $W$ is unchanged. Thus the cuts remain in the same finite-dimensional global coefficient space and survive simultaneous coefficient approximation.

### 17.4 The stable connecting-slice theorem

**Theorem 17.2 (stable integral connecting slice).** In the setting of Theorem 17.1 there is a tuple of global cutting sections whose intersection is a smooth proper geometrically connected relative curve $\mathcal C/R$ such that:

1. its generic open $C^\circ$ lies in $Y\setminus Z$, contains a point in the assigned semistable neighborhood, and maps immersively near every marked point;
2. the special fiber contains a nonempty dense open $W$ mapping to the good locus and avoiding $\overline Z$;
3. the closure of every generic closed point specializing inside $W$ has good reduction and carries the same PEL level, component, and frame data; and
4. all conclusions persist for cutting tuples in a sufficiently small congruence neighborhood inside the same global section space.

If one demands a $K$-rational good section whose reduction lies in $W$, one must additionally assume

$$
U_k(k)\ne\varnothing.
\tag{17.12}
$$

Without (17.12), only the nonempty-open version is valid. Indeed, over a finite field choose, for every $k$-point of the good special fiber, a hyperplane through that point but not through the entire fiber. The product of their equations lifts to a proper generic hypersurface whose closure contains every good $k$-point. The complement remains a nonempty open with closed points of higher degree, but it has no $k$-point. The nonempty-open version of the theorem is the stable form used by integral moving arguments and requires no false rational-point assertion.

### 17.5 The exported interface

We now attach short labels to results already proved. They are outputs, not hypotheses.

- $({\rm IIT})$ is Theorem 7.1, with strict intrinsic-log compatibility and the square-zero smoothing distinction.
- $({\rm MPE})$ is Theorem 8.1 and the completed rings (8.3)--(8.4).
- $({\rm BCP})$ is Theorem 10.1.
- $({\rm AEC}_0)$ is Theorem 11.1, including the independently proved fs saturated monomial charts.
- $({\rm RCD})$ is Theorem 12.1, whose face map (12.7) gives the conductor factorization (12.9) before the nilpotent lift.
- $({\rm TDC})$ is the theta--determinant and horizontal, vertical, and mixed positivity package of Chapters 14 and 15.
- $({\rm ACE})$ is the conjunction of $({\rm BCP})$, $({\rm AEC}_0)$, $({\rm RCD})$, overlap effectivity, and $({\rm TDC})$.
- $({\rm TCG})_\Sigma$ is Theorem 16.1, including framed normalization, universal objects, completed comparisons, descent, and the ample line.
- $({\rm FTJ})_{v,Z}$ is Theorem 17.1 after base change to the selected place and frame component.
- $({\rm ICS})_{v,Z}$ is Theorem 17.2 in its nonempty-good-open form; its stronger rational-section form includes condition (17.12).

The proved implication chain is therefore

$$
({\rm IIT})\Longrightarrow({\rm MPE}),
\qquad
({\rm MPE})+({\rm ACE})
\Longrightarrow({\rm TCG})_\Sigma
\Longrightarrow({\rm FTJ})_{v,Z}
\Longrightarrow({\rm ICS})_{v,Z}.
\tag{17.13}
$$

Every arrow in (17.13) has been established in the displayed order. The last assertion is deliberately the nonempty-open statement, which is stable under finite residue extensions and is the one justified without an extra rational-point hypothesis.

## 18. Hostile mathematical review

### 18.1 Infinitesimal and logarithmic attacks

**Attack: the recognition theorem contradicts $XY=\epsilon$.** It would if it concerned underlying schemes over a base with no fixed logarithmic map. It does not. The intrinsic parameter of $XY=\epsilon$ is $1\mapsto\epsilon$, so this family is represented by the monoid deformation $q\mapsto\epsilon$ in $S[[q]]$. It is excluded only from the fiber of the strict test problem $q\mapsto0$. Thus the total completed ring retains the smoothing direction while a fixed boundary log fiber does not acquire a hidden one.

**Attack: the proof divides by a monomial which may be zero.** Equation (7.10) is a factorization in the intrinsic log structure, not a quotient in $A'$. When $\alpha(d)=0$, strictness says that the multiplication coefficient has that same characteristic element; adding a nonzero square-zero term would change the characteristic map. No cancellation is used.

**Attack: traits cannot detect nilpotent deformations.** They are not asked to. Height-one traits prove extraction over normal reduced bases in Section 8.1. The square-zero weight-algebra argument proves recognition over Artin thickenings, and (7.14) plus adic inverse limits handles general complete tests.

**Attack: an intrinsic log structure was simply declared.** Section 7.1 constructs it from the monomial-unit subsheaves on normalized stars, proves agreement on conductor faces, recovers the base characteristic from multiplication coefficients, and proves saturation in the common lattice. The atlas charts are independently constructed and proved fs in Section 11.3. The deformation theorem requires a strict identification with this recovered structure, which is exactly the datum that distinguishes toroidal deformations.

**Attack: the unit cocycle may carry a genuine obstruction.** For the free weight lattice, the ordered-basis recursion (7.12) explicitly splits every symmetric normalized cocycle. The remaining periodic part is not discarded; it is the unit part of the period homomorphism. Polarization and rigidification remove the residual character ambiguity.

### 18.2 Normalization, conductor, and descent attacks

**Attack: normal toric charts imply normal semiabelic fibers.** They do not. The manuscript always distinguishes the normalized stars from their periodic face pushout. Equations (6.7), (10.3), and (10.7) retain the conductor, and determinant formula (14.5) includes its correction.

**Attack: a formal Kummer root need not be algebraic.** Section 9.2 computes the integral closure as the finite monoid algebra $S'[P_\sigma^{\mathrm{fr}}]$, and Section 9.3 normalizes before completing. Excellence then identifies the completion. No root is introduced beyond the prescribed frame lattice.

**Attack: boundedness of normalization does not bound the gluing.** Theorem 10.1 bounds the conductor subschemes, both face arrows, their graph polynomials, the number of cell orbits, and the monomial multiplication tables. Formula (10.6) bounds the nonnormal Hilbert polynomial. Thus the entire pushout presentation, not just $P^\nu$, lies in finite-type parameter spaces.

**Attack: a Fitting stratum cannot prove an fs chart.** Agreed; it is never used for that purpose. The base chart is the explicitly saturated monoid (11.3), the family star chart is (11.4), and conductor saturation is checked in their common group completion. Fitting ideals serve only to impose bounded locally closed conditions after these charts exist.

**Attack: generic Galois arrows need not descend over a ramified self-product.** Section 12.2 writes the branch arrow as $e_x\mapsto u_g(x)e_{gx}$, restricts it to the shared face semigroups, and uses the multiplicative identity (12.5) to obtain (12.7) and the conductor factorization (12.9). The reduced conductor pushout gives (12.10); infinitesimal recognition uniquely lifts it through the nilradical, and the same uniqueness proves the cocycle.

**Attack: the ample line might fail to descend even if the scheme descends.** The line is included in the normalized and conductor descent data. Tensoring its deck transforms gives a literal linearization. Its section algebra descends fpqc, and relative ampleness is checked after the faithfully flat cover.

### 18.3 Positivity and joining attacks

**Attack: strict convexity of a fan says nothing about the universal theta line.** Correct. Strict convexity first gives $\mathcal B_\psi$ on the base. The universal theta line is constructed separately from the Poincare biextension and the Mumford factor of automorphy. Only its determinant of cohomology returns to the base, where the boundary character calculation permits comparison.

**Attack: determinant of cohomology may jump on a nonnormal fiber.** The normalized-star resolution and conductor exact triangle give (14.3) and (14.5). For the chosen uniform theta power, higher cohomology vanishes on stars and all their intersections, so the determinant is a base-compatible line.

**Attack: horizontal and vertical positivity do not imply mixed positivity.** Section 15.3 supplies the missing uniform bound. The combined map to the theta Hilbert parameter and the fan toric parameter is finite because constant image would mean constant monodromy and constant theta multiplication, hence a constant one-motive. Pulling back an ample product line and taking a maximum over finitely many chart types gives one global exponent.

**Attack: a complete formal cusp still does not meet the good interior.** Algebraic cusp effectivity places the completion in a finite-type chart; overlap gluing places that chart in the same projective scheme as the interior; the descended ample line is global. Theorem 17.1 then identifies the selected completed branch without altering its Kummer field. The joining is an output of the compactification, not an assumption used to construct it.

**Attack: a proper closed subset may occupy the whole special fiber.** Its naive closure could if vertical components were added, but the schematic closure of a generic closed subset has a uniformizer-saturated ideal. Repeated division and Krull intersection prove (17.3), so it contains no special-fiber component.

**Attack: a nonempty open over a finite field need not have a rational point.** Theorem 17.2 claims only a closed point unless (17.12) is assumed. The hyperplane-product counterexample shows why this qualification is necessary. Relative slicing works with the higher-degree closed point and still supplies a dense good open.

### 18.4 Final theorem chain

The construction survives every preceding attack in the following order.

1. Raynaud extensions, period lattices, and positive logarithmic one-motives encode degenerations.
2. Equivariant regular projective fans and coherent periodic decompositions encode the base and family combinatorics separately.
3. The Mumford construction works over complete fs test pairs, including nilpotent boundary tests.
4. Intrinsic-log infinitesimal recognition gives the inverse equivalence and completed deformation rings.
5. Paired-frame Kummer normalization is finite algebraically before completion.
6. Bounded normalization-conductor presentations produce an explicit finite-type cusp atlas with proved saturated monomial charts.
7. The displayed conductor weight map and infinitesimal uniqueness prove ramified fpqc descent.
8. Exhaustive overlaps algebraize and glue the cusps to the interior.
9. Poincare, theta, determinant, and fan lines give horizontal, vertical, and mixed positivity and a descended ample line.
10. The resulting smooth projective compactification supplies the finite-type joining model; relative slicing supplies the stable good-open connecting curve.

Thus Theorems 16.1, 17.1, and 17.2 are consequences of constructions and proofs internal to the preceding chapters. Boundary compatibility includes face restriction, normalized stars, nonnormal conductor pushouts, nilpotent base change, trait extraction, paired-frame normalization, ramified descent, and ample-line descent.
