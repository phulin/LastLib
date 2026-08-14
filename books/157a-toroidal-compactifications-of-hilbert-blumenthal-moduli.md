# Conditional Toroidal Compactifications of Hilbert--Blumenthal Moduli: A Minitextbook

**Status.** This is a conditional minitextbook. The Raynaud and fan theorems, the
explicit homogenized Mumford construction, finite Kummer normalization, BCP for
explicit charts, and the displayed chartwise conductor, determinant, and slicing
calculations are retained in their proved scopes. In degree $d\ge2$, five antecedents
are not proved: geometric cusp classification (GCC, Hypothesis 3.1), which occurs
before intrinsic recognition; Raw-DF-IIT (Hypothesis 7.1); coherent frame-root
descent across conductors (FRCD, Hypothesis 9.1); finite flatness of all Kummer
normalizations used for fppf descent (KFF, Hypothesis 9.2); and extension,
quasi-finiteness, and the exact line identity for the structured Hilbert map
(TDC-Ext, Hypothesis 15.1). Unframed IIT and
fixed-label MPE depend on Raw-DF-IIT, while their exact framed conductor-root forms
also use FRCD. Exhaustive AEC and the higher-rank global unframed space additionally
depend on GCC; subsequent framed fppf arguments also depend on KFF. TDC-Ext enters
only at projectivity: it is required by TDC and hence by the projective higher-rank
TCG, FTJ, and ICS chain. Higher-rank ICS also assumes that the residue field of the
complete DVR is finite, exactly for the finite-field Bertini step. In degree
$d=1$, the global compactification is imported only in the scope of Book 111,
Theorem 13.1, and Section 17 separately assumes the rank-one supplied-model
antecedent R1-FTJ before applying this manuscript's avoidance and slicing argument.
Thus the two branches of TCG, FTJ, and ICS have the distinct hypotheses displayed
in Theorems 16.1, 17.1, 17.2, and (17.13). Book 111, Theorem 13.1 is not cited for
arbitrary-$Z$ joining, avoidance, or ICS.

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
- [5. Complete bases and fine saturated toroidal charts](#5-complete-bases-and-fine-saturated-toroidal-charts)
  - [5.1 Saturated monoids and their completions](#51-saturated-monoids-and-their-completions)
  - [5.2 Ambient structured deformations and charted tests](#52-ambient-structured-deformations-and-charted-tests)
  - [5.3 The logarithmic period map](#53-the-logarithmic-period-map)
  - [5.4 Face restriction and base change](#54-face-restriction-and-base-change)
- [6. The Mumford construction](#6-the-mumford-construction)
  - [6.1 The periodic polyhedral algebra](#61-the-periodic-polyhedral-algebra)
  - [6.2 Gluing and the period quotient](#62-gluing-and-the-period-quotient)
  - [6.3 Flatness, properness, and the group locus](#63-flatness-properness-and-the-group-locus)
  - [6.4 Endomorphisms, polarization, and level](#64-endomorphisms-polarization-and-level)
  - [6.5 The family theta line](#65-the-family-theta-line)
- [7. The Raw-DF-IIT prerequisite](#7-the-raw-df-iit-prerequisite)
  - [7.1 The raw non-cancellative defect monoid](#71-the-raw-non-cancellative-defect-monoid)
  - [7.2 Why the quotient by units does not prove recognition](#72-why-the-quotient-by-units-does-not-prove-recognition)
  - [7.3 The exact Raw-DF-IIT hypothesis](#73-the-exact-raw-df-iit-hypothesis)
  - [7.4 Conditional reconstruction of all PEL data](#74-conditional-reconstruction-of-all-pel-data)
  - [7.5 Consequences for IIT and completion](#75-consequences-for-iit-and-completion)
- [8. The inverse problem and completed deformation rings](#8-the-inverse-problem-and-completed-deformation-rings)
  - [8.1 Extraction on normal reduced bases](#81-extraction-on-normal-reduced-bases)
  - [8.2 Full faithfulness](#82-full-faithfulness)
  - [8.3 Conditional essential surjectivity](#83-conditional-essential-surjectivity)
  - [8.4 Completed local rings](#84-completed-local-rings)
  - [8.5 Traits and boundary-supported Artin rings](#85-traits-and-boundary-supported-artin-rings)
- [9. Paired frames and Kummer normalization](#9-paired-frames-and-kummer-normalization)
  - [9.1 Torsion of the boundary one-motive](#91-torsion-of-the-boundary-one-motive)
  - [9.2 The refined Fourier lattice](#92-the-refined-fourier-lattice)
  - [9.3 Normalization before completion](#93-normalization-before-completion)
  - [9.4 Unframed-first normalization of paired frames](#94-unframed-first-normalization-of-paired-frames)
- [10. Bounded normalization and conductor presentations](#10-bounded-normalization-and-conductor-presentations)
  - [10.1 The conductor square](#101-the-conductor-square)
  - [10.2 Uniform theta embeddings](#102-uniform-theta-embeddings)
  - [10.3 Bounded Hilbert and graph data](#103-bounded-hilbert-and-graph-data)
  - [10.4 Pushouts and nonnormal fibers](#104-pushouts-and-nonnormal-fibers)
- [11. A finite-type algebraic Mumford chart](#11-a-finite-type-algebraic-mumford-chart)
  - [11.1 Construction from explicit monoid algebras](#111-construction-from-explicit-monoid-algebras)
  - [11.2 Algebraizing star gluing and the boundary conductor](#112-algebraizing-star-gluing-and-the-boundary-conductor)
  - [11.3 Fine saturated charts and conditional AEC](#113-fine-saturated-charts-and-conditional-aec)
  - [11.4 Comparison with the complete Mumford family](#114-comparison-with-the-complete-mumford-family)
  - [11.5 Why Fitting ideals do not suffice](#115-why-fitting-ideals-do-not-suffice)
- [12. Conditional ramified conductor compatibility](#12-conditional-ramified-conductor-compatibility)
  - [12.1 The tensor square of a ramified trait](#121-the-tensor-square-of-a-ramified-trait)
  - [12.2 Why framed-first descent is circular](#122-why-framed-first-descent-is-circular)
  - [12.3 The unframed-first normalization route](#123-the-unframed-first-normalization-route)
  - [12.4 Conditional conductor and nilpotent compatibility](#124-conditional-conductor-and-nilpotent-compatibility)
  - [12.5 Conditional RCD](#125-conditional-rcd)
- [13. Conditional algebraic overlaps and the proper toroidal space](#13-conditional-algebraic-overlaps-and-the-proper-toroidal-space)
  - [13.1 Common faces and changes of cusp](#131-common-faces-and-changes-of-cusp)
  - [13.2 Conditional exhaustion by the structured Isom scheme](#132-conditional-exhaustion-by-the-structured-isom-scheme)
  - [13.3 Conditional effective separated gluing](#133-conditional-effective-separated-gluing)
  - [13.4 Conditional properness from complete fans](#134-conditional-properness-from-complete-fans)
- [14. Poincare, theta, and determinant lines](#14-poincare-theta-and-determinant-lines)
  - [14.1 Three different lines](#141-three-different-lines)
  - [14.2 The normalized semiabelic theta line](#142-the-normalized-semiabelic-theta-line)
  - [14.3 Determinant of cohomology](#143-determinant-of-cohomology)
  - [14.4 Boundary transition characters](#144-boundary-transition-characters)
  - [14.5 Base change and conductor compatibility](#145-base-change-and-conductor-compatibility)
- [15. Conditional projectivity via structured graphs](#15-conditional-projectivity-via-structured-graphs)
  - [15.1 The interior structured map and TDC-Ext](#151-the-interior-structured-map-and-tdc-ext)
  - [15.2 Cartier fan data](#152-cartier-fan-data)
  - [15.3 The conditional proper quasi-finite structured graph route](#153-the-conditional-proper-quasi-finite-structured-graph-route)
  - [15.4 Conditional TDC](#154-conditional-tdc)
- [16. The conditional toroidal compactification and gluing theorem](#16-the-conditional-toroidal-compactification-and-gluing-theorem)
  - [16.1 Construction and completed-local comparison](#161-construction-and-completed-local-comparison)
  - [16.2 Smoothness, boundary, and universal objects](#162-smoothness-boundary-and-universal-objects)
  - [16.3 Projectivity and descent](#163-projectivity-and-descent)
  - [16.4 Independence under refinement](#164-independence-under-refinement)
- [17. Conditional finite-type joining and the integral connecting slice](#17-conditional-finite-type-joining-and-the-integral-connecting-slice)
  - [17.1 Joining a formal cusp to the good interior](#171-joining-a-formal-cusp-to-the-good-interior)
  - [17.2 The conditional finite-type joining theorem](#172-the-conditional-finite-type-joining-theorem)
  - [17.3 Relative slicing with a dense good open](#173-relative-slicing-with-a-dense-good-open)
  - [17.4 The conditional stable connecting-slice theorem](#174-the-conditional-stable-connecting-slice-theorem)
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

This book develops the two local constructions simultaneously and isolates the additional
steps needed to make them a global compactification. The first unproved step is the
classification of an arbitrary geometric semiabelic PEL fiber as one of the displayed
Mumford fibers; this is GCC, Hypothesis 3.1. Raw-DF-IIT, FRCD, and KFF are later,
separate hypotheses. All results that use them are labelled conditional. A geometric boundary fiber can be reducible and nonnormal. A test ring can
contain nilpotents. A paired torsion frame can ramify at the boundary even when it is
finite etale on the abelian locus. A splitting extension of a trait can be ramified,
so its self-product is not a disjoint union of Galois graphs. Finally, a strictly
convex function on a fan produces a line on the toric base, not the theta line on the
universal semiabelic family. The explicit constructions survive this audit; recognition
of arbitrary higher-rank boundary deformations and the higher-rank global closure remain conditional.

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

The inverse direction first requires GCC to put an arbitrary geometric fiber in a
labelled Mumford chart. For a fixed labelled Mumford fiber it is then reduced before
algebraization to Raw-DF-IIT. Chapter 7 explains
why passing multiplication coefficients to $A/A^\times$ neither permits cancellation nor
produces roots, and why periodic piecewise-linear data can have a secondary-fan kernel.
Hypothesis 7.1 states the raw, non-cancellative symmetric-monoidal result actually needed.
Assuming it gives IIT and the correctly dimensioned completed ring; without it, only the
already charted Mumford deformation functor is represented by that ring.

We next prove finiteness of Kummer normalization, bound every structure graph of an
explicit Mumford chart, and algebraize that chart. Neither coherent choices of roots
on paired conductor faces nor flatness of every finite normalization follows from
that finiteness; FRCD and KFF isolate those two inputs. Exhaustivity for arbitrary
boundary objects is conditional on GCC and Raw-DF-IIT.
Paired frames are handled in the noncircular order: construct the unframed compactification
first and normalize it in the finite generic paired-frame cover. Normalization extends the
deck action; structured conductor compatibility uses Raw-DF-IIT and FRCD, while fppf
descent through that finite map uses KFF.

The line-bundle chapters separately construct the family theta determinant and the
Cartier fan line. The remaining positivity route would use a proper quasi-finite map
from the structured theta-graph space to a projective Hilbert/graph parameter space.
The extension, quasi-finiteness, and exact Plucker-line identity for that map are not
consequences of the determinant computation; they are isolated as TDC-Ext. No finite
generation of a global effective cone is asserted.

For $d\ge2$, conditionally, the resulting projective compactification supplies the
global finite-type joining model used for avoidance and relative slicing. The rank-one case is not a new
closure theorem here: its global cusp compactification is imported in the precise
scope of Book 111, Theorem 13.1. Joining a selected cusp branch to the required fine
component still uses the separately stated supplied-model antecedent R1-FTJ, and the
avoidance of an arbitrary proper $Z$ is then proved by this manuscript's saturation
argument. Neither assertion is imported from Books 110--111.

### 1.4 Three distinctions that govern the book

The first distinction is between an intrinsic chart and an unrelated external chart.
Over $k[\epsilon]/(\epsilon^2)$ the equation $XY=\epsilon$ is a flat smoothing of
$XY=0$. Its intrinsic smoothing chart sends the generator to $\epsilon$; it is not a
deformation over a separately fixed chart sending that generator to zero. The
infinitesimal theorem recovers the first chart and never assumes the second.

The second distinction is between normal charts and nonnormal fibers. The monoid algebra of a saturated cone is normal. A periodic semiabelic fiber obtained by identifying faces of several toric pieces can be reducible and nonnormal. Its normalization and conductor are part of the moduli presentation, and all group and polarization maps must descend through their pushout.

The third distinction is between three line bundles. The fan support function defines a line on a toric chart of the moduli base. The Poincare biextension defines a theta line on the universal semiabelic family. Taking determinant of cohomology produces a line back on the moduli base. Confusing any two of these makes the positivity argument circular.

We fix the meaning of a semiabelic object. It is a tuple $(P,G,\mu,\Theta)$ in
which $P$ is proper and flat with geometrically connected fibers, $G$ is a smooth
group scheme whose identity component has semiabelian geometric fibers and whose
component group is finite, $\mu:G\times P\to P$ is an action for which $G\subset P$
is a dense open torsor, and $\Theta$ is a
relatively ample line with a cubical action linearization. The stabilizer of a point
is a subtorus determined by the face containing its orbit. The reduction of a
geometric fiber is seminormal, but it may be reducible and nonnormal. The PEL
endomorphisms, polarization, and level act on the whole tuple, not only on $G$.

Over a nonreduced base the special-fiber normalization does not itself lift by taking
integral closure. Instead a labelled semiabelic object includes invariant affine star
neighborhoods lifting the special orbit charts. Normalization and conductor are
retained after restriction to each fixed boundary stratum. Raw-DF-IIT is exactly the
missing assertion that multiplication on those neighborhoods intrinsically recovers
the unframed fixed-label monoid chart, with its leading units and period holonomy,
through nilpotents. It does not supply GCC, framed conductor roots, or flatness of a
finite normalization.

Two tempting replacements fail. Keeping only $G$ forgets which proper orbit
compactification and which ample line were chosen. Keeping only $P$ forgets the
group law and cannot recover the period lattice functorially. The tuple, its star
neighborhoods, and its boundary normalization-conductor diagrams are the minimum
data stable under degeneration and descent.

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

**Proof.** Functoriality of the maximal torus gives the $F$-module structure. The dimension argument proves the dichotomy. In the nonzero case the Raynaud abelian quotient $B$ is zero, while the PEL lattice and ordered polarization identify $Y$ with an invertible ideal $I_b$ and $X^*(T_b)$ with its trace dual. The period pairing is balanced because every element of $\mathcal O_F$ is adjoint to itself for the Hilbert polarization. Positivity is inherited from the polarization of $A$. $\square$

This theorem is why Hilbert cusps have no positive-dimensional abelian base. We retain the general Raynaud notation because it clarifies the Poincare and determinant constructions and extends verbatim to other PEL data.

The argument is stable under ramified base change. Toric rank may become split only after extension, but its character space over $\mathbf Q$ still has an $F$-action and therefore has dimension divisible by $d$. Descent of the conclusion follows because vanishing of the Raynaud abelian quotient $B$ is geometric. Thus no hidden mixed Raynaud stratum appears after passing back to the original trait.

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

For a fiber already known to have the Mumford orbit presentation, its data can be
read back as follows. Let $(P,G,\Theta)$ be a labelled geometric semiabelic PEL
fiber of the totally toric Hilbert cusp type. The identity component of $G$ is the
torus $T_X$ by Theorem 2.1. Normalize the closure of each $T_X$-orbit.
An affine invariant open in that normalization has a coordinate ring decomposed into
torus weights. The set of occurring weights is closed under addition and saturation:
if $n x$ occurs, normality makes the corresponding character integral and hence
forces $x$ to occur. Thus the open is the saturated semigroup algebra of a rational
cone, and the normalized orbit closure is a toric variety. Intersections of orbit
closures give common faces. The two conductor arrows record their incidence.

The finite component group of $G$ acts transitively on the repeated cells. Its kernel
on the character lattice is the period lattice $Y$, so lifting the finite incidence
complex to the universal cover gives a $Y$-periodic rational polyhedral decomposition
of $X_\mathbf R$. The weights of the rigidified line $\Theta$ on the toric
normalizations give integral affine functions on the cells. The cubical identity
makes their changes under $Y$ the quadratic automorphy factors (5.9c), and ampleness
makes the resulting support function strictly convex: equality of adjacent slopes
would contract their invariant wall curve. The $\mathcal O_F$, polarization, and
level graphs recover exactly the cusp label.

Conversely, Chapter 6 reconstructs the same normalized orbit closures, conductor
pairings, action, and theta weights from those data. This verifies recovery on the
explicit Mumford locus. It does not classify an arbitrary geometric semiabelic PEL
fiber: the definition in Section 1.4 does not itself prove that all normalized orbit
closures form a finite rational toric complex, that the component action lifts to a
$Y$-periodic complex, that the theta weights give one coherent integral support
function, or that the resulting cusp label is unique. We therefore isolate the
needed classification instead of calling the preceding recovery argument a proof.

**Hypothesis 3.1 (geometric cusp classification, GCC).** Every labelled geometric
semiabelic PEL fiber at a nonzero Hilbert cusp is a Mumford fiber for a unique cusp
label, periodic cell complex, and fan face, up to the declared arithmetic change of
label. Its normalized orbit stars and both conductor arrows are intrinsic, and this
identification is compatible with the PEL, level, action, and rigidified theta data.

GCC precedes Raw-DF-IIT logically. Raw-DF-IIT begins with a deformation of an
already labelled Mumford fiber and therefore cannot be used to prove that an
arbitrary geometric fiber has such a label.

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

Before resolving singularities, take the barycentric subdivision, equivalently the
successive equivariant stellar subdivisions at relative-interior barycenters in
decreasing dimension. This is a coherent simplicial refinement. A cone in it is a
chain of parent faces, with at most one parent face of each dimension. If a face and
one of its translates are both faces of one refined cone, their chains have the same
dimension pattern and hence are the same subchain. Thus no refined cone contains two
distinct translates of one face. In particular, a stabilizer fixes the chain and
every ray, so the action has no inversions. This regular-action property persists
after simultaneous stellar subdivision of an orbit whose distinct members lie in no
common cone: that subdivision is the pullback of one stellar subdivision of the
quotient conical complex.

### 4.4 Equivariant regularization

For a simplicial cone $\sigma$ with primitive rays $e_1,\ldots,e_s$, define

$$
\mu(\sigma)=
[N\cap\operatorname{span}_\mathbf R(\sigma):
\mathbf Ze_1+\cdots+\mathbf Ze_s].
\tag{4.2}
$$

If $\mu(\sigma)>1$, choose a nonzero lattice point $v$ in the half-open fundamental
parallelepiped, let $w$ be the primitive lattice generator of
$\mathbf R_{\ge0}v$, and let $\tau$ be the smallest face containing that ray. Write

$$
w=\sum_{i\in I}a_ie_i,
\qquad 0<a_i<1.
\tag{4.3}
$$

Star subdivision at $\mathbf R_{\ge0}w$ replaces every simplicial cone
$\eta\supset\tau$ by cones whose multiplicities are

$$
a_i\mu(\eta),\qquad i\in I.
\tag{4.4}
$$

These are positive integers strictly smaller than $\mu(\eta)$. To regularize
equivariantly, let $m>1$ be the largest multiplicity of any cone and choose $\sigma$
with $\mu(\sigma)=m$. Because the barycentric refinement has no inversions, the
stabilizer of $\tau$ fixes its rays and therefore fixes $w$. Distinct members of the
orbit of $(\tau,w)$ lie in no common cone, so the simultaneous stellar subdivisions
commute and are the pullback of a single stellar subdivision on the quotient conical
complex. This is the orbit-disjoint step missing from an arbitrary common-refinement
argument.

For every affected cone $\eta$, (4.4) lowers its multiplicity. Moreover, the
multiplicity of a face divides the multiplicity of every containing simplicial cone:
its finite lattice quotient injects into the quotient for the containing cone.
Consequently no new cone of multiplicity $m$ is created, while the chosen orbit of
$m$-cones disappears. There are finitely many cone orbits, and each orbit subdivision
creates only finitely many new orbits. Induction first on the maximal multiplicity and
then on the number of orbits having that multiplicity therefore terminates with every
cone regular. The regular-action property persists at each orbit-disjoint step.

Coherence is also preserved. On the finite quotient conical complex, a stellar
subdivision is induced by a rational tent function at its new ray. Pull it back and
add a sufficiently small invariant multiple to the old strictly convex support
function. There are only finitely many inequalities on the quotient, so one positive
rational size works. Clearing the finitely many denominators after termination gives
an invariant integral strictly convex support function. Marked rays are never
removed and, being one-dimensional, are already regular.

If an element of the neat cusp group stabilizes a nonzero regular cone, it fixes a primitive ray. Its infinite part is multiplication by a totally positive unit, and fixing one nonzero element forces that unit to be $1$. Its finite part is killed by neatness. Hence every nonzero cone has trivial stabilizer.

**Theorem 4.2 (simultaneous regular projective refinement).** For the finitely many cusp labels, refined level lattices, finite descent symmetries, and marked valuation rays, there is an equivariant admissible fan collection which is regular, projective, has trivial stabilizers on nonzero cones, and contains every marked ray.

Here simultaneous refers to the equivariant finite collection of fan refinements in
their respective lattices. The argument does not produce compatible lattice bases
for every inclusion between unframed, framed, and theta-framed lattices, nor does it
prove that the induced finite monoid-algebra maps are locally free. That stronger
statement is isolated as KFF in Hypothesis 9.2.

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

We impose one further finite refinement for testing infinitesimal recognition. For every
primitive generator $p$ of the regular sharp monoid
$P_{\sigma,\tau}^{\sharp}$, choose a small lattice parallelogram crossing a wall on
which an integral convex function has primitive bend $p$. Insert its whole
$Y$-orbit and all its faces. A sufficiently small invariant lower-height
perturbation retains coherence and does not change the base fan. Repeating this for
the finitely many primitive generators and face types gives a decomposition in which
every primitive base monomial occurs as the defect of a displayed elementary
product. Inserting entire finite descent orbits preserves equivariance.

This refinement controls the groupified bending lattice, not the raw coefficient
monoid. Crossing walls expresses the *sum* of bends as a sum of primitive bends, but
does not permit one to solve the corresponding product equality in a ring when a
factor is zero or nilpotent. Chapter 7 isolates the additional raw assertion needed
for intrinsic recognition.

Thus each nonzero cone carries a compatible periodic decomposition whose polarization support function remains strictly convex for every monodromy form in that cone. This compatibility is the datum needed to glue the Mumford family across base faces.

## 5. Complete bases and fine saturated toroidal charts

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
J_\sigma=(q^p:p\in P_\sigma\setminus P_\sigma^\times),
\tag{5.2}
$$

and let $S[[P_\sigma]]$ denote the $J_\sigma$-adic completion. If $\sigma$ has a face $\tau$, restriction to the corresponding toric open inverts $q^p$ for $p\in P_\sigma\cap\tau^\perp$. The resulting monoid is

$$
P_{\sigma,\tau}=P_\sigma+(P_\sigma\cap\tau^\perp)^{\mathrm{gp}}.
\tag{5.3}
$$

Localization preserves integrality and saturation. Consequently every fan chart, every face overlap, and every completion along a toric stratum carries an fs logarithmic structure. The adjective fs will always mean fine and saturated.

Regularity of $\sigma$ gives more. If its primitive generators extend to a basis of $N$
and $\tau$ has dimension $r$, then, after splitting the units of the face,

$$
S[P_{\sigma,\tau}]\simeq
S[t_1,\ldots,t_r,t_{r+1}^{\pm1},\ldots,t_d^{\pm1}].
\tag{5.4}
$$

Thus the toroidal boundary is locally a relative normal-crossings divisor whenever the coefficient base is regular. This conclusion comes from the monoid, not from a posterior examination of its boundary ideal.

The convention in (5.4) is used throughout: $r=\dim\tau$, not the codimension of
$\tau$. Thus there are exactly $r$ boundary parameters and $d-r$ invertible
Fourier, or period, parameters. The completed monoid has the same decomposition
$\mathbf N^r\oplus\mathbf Z^{d-r}$.

Two basic charts will recur. For $P=\mathbf N$, the base is the completed disc $S[[q]]$ and the boundary is $q=0$. For $P=\mathbf N^2$, the base is $S[[q_1,q_2]]$ and the codimension-two stratum is $q_1=q_2=0$. A map to $k[\epsilon]/(\epsilon^2)$ may send $q_1$ to $\epsilon$ and $q_2$ to zero. This is a legitimate logarithmic deformation with one first-order smoothing direction; it is different from the strict boundary fiber in which both generators map to zero.

The log structure associated with a chart $P\to A$ is the sheafification of

$$
P\oplus_{\alpha^{-1}(A^\times)}A^\times\longrightarrow A.
\tag{5.4a}
$$

Its characteristic at a geometric point is $P$ modulo the face mapping to units there. Thus face localization is not a change of convention: it is the actual characteristic monoid seen on the corresponding stratum.

### 5.2 Ambient structured deformations and charted tests

There are two categories here, and confusing them makes infinitesimal recognition
circular. A **complete base test** is a complete noetherian $S$-algebra $A$ with an
ideal of definition $I$, such that $A\simeq\varprojlim A/I^n$, the reduced ring is
excellent, and its normalization is finite. It carries no chosen map from
$P_\sigma$.

Fix a labelled geometric Mumford fiber $P_0$ at the stratum of $\sigma$. An
**ambient structured cusp deformation** of $P_0$ over $A$ consists of the following
commuting finite-presentation data.

1. A flat projective $A$-scheme $P$, its smooth open group locus $G\subset P$ with
   semiabelian identity component, its identity, multiplication, and inverse, and an action
   $G\times_A P\to P$, all reducing to the labelled data on $P_0$.
2. A finite labelled system of invariant affine star neighborhoods lifting the
   corresponding neighborhoods of $P_0$, with their weight decompositions. On the
   boundary fiber retain its finite normalization and the two conductor arrows. An
   affine open lifts uniquely through a nilpotent thickening because the underlying
   topological spaces agree; the labels choose the lifts on a general complete base.
   No multiplication coefficient is prescribed.
3. The $\mathcal O_F$-endomorphism graphs on $G$ and $P$, the relatively ample theta
   line with its cubical rigidification and polarization isomorphism, and the full
   finite prime-to-residue-characteristic level graphs.
4. The action, endomorphism, polarization, level, and theta data on the star
   neighborhoods, together with their equality on overlaps and after the two
   boundary conductor arrows.

Every item is actual scheme, morphism, invertible-sheaf, or graph data; in
particular “PEL-compatible” is not shorthand for a condition imposed only on the
generic fiber. Morphisms preserve all of it. The labelled star system is an atlas device,
not extra monomial information: no element of $A$, no logarithmic chart, and no
divisibility of a multiplication coefficient has been selected.

A **charted toroidal test** is instead a complete base test together with a
continuous map

$$
\alpha:P_\sigma\longrightarrow A,
\qquad \alpha(P_\sigma\setminus P_\sigma^\times)\subset I,
\tag{5.4b}
$$

and the associated fs log structure. The Mumford construction is initially a
functor from charted tests to ambient structured deformations. Conditional IIT would
give the converse: an ambient deformation would itself determine the DF chart,
uniquely up to its monoidal unit isomorphism. Strictness is therefore a conditional
conclusion, not a membership condition in the ambient deformation functor.

Nilpotents are permitted in both categories. In particular $A$ may be an Artin ring
supported entirely on the boundary, in which case there need be no ordinary dense
generic fiber. This is essential: a completed moduli problem is determined by its
values on nilpotent thickenings, not just on traits whose generic points are
abelian.

When $A$ is reduced and normal, the values of a rational function are detected by height-one valuations:

$$
A=\bigcap_{\operatorname{ht}\mathfrak p=1}A_\mathfrak p
\quad\text{inside }\operatorname{Frac}(A)
\tag{5.5}
$$

componentwise. For a finite normalization the same statement holds after taking the product of the fraction fields. We will use (5.5) to compare periods on reduced bases, but never to infer nilpotent information. Nilpotent information is read directly from multiplication in the labelled weight algebra in Chapter 7.
What remains conditional is the Raw-DF-IIT factorization that turns those raw
nilpotent multiplication maps into a Fourier DF chart.

The intersection property has a divisor-theoretic proof. Membership in every height-one localization means that the divisor of the rational function has no negative coefficient. On a normal noetherian domain, a rational function with no denominator divisor belongs to the domain because every principal ideal is the intersection of its height-one primary localizations. Applying the statement to the function and its inverse detects units.

### 5.3 The logarithmic period map

Let $X$ and $Y$ be the character and period lattices of a cusp, with $\mathcal O_F$-action, and let

$$
B:Y\times X\longrightarrow P_\sigma^{\mathrm{gp}}
\tag{5.6}
$$

be the integral bilinear form obtained by evaluating the universal monodromy form. Write
$q^m$ for the image in $M_A^{\mathrm{gp}}$ of $m\in
P_\sigma^{\mathrm{gp}}$. The notation includes the unit part of the chart image: after a
map $S[P_\sigma]\to A$, the element $q^m$ is an actual logarithmic section, not a
formal symbol to which an independent unit coordinate is to be adjoined.

A logarithmic period homomorphism over $A$ is a map

$$
\iota:Y\longrightarrow T_X^{\log}(A)
=\operatorname{Hom}\bigl(X,M_A^{\mathrm{gp}}\bigr)
\tag{5.7}
$$

whose characteristic part is $B$ and which, in the universal cusp chart, is

$$
\iota(y)(x)=q^{B(y,x)}.
\tag{5.9}
$$

If one changes a local splitting of the log structure, the right side is written
$u(y,x)q^{B(y,x)}$ with $u(y,x)\in A^\times$. That $u$ is the
change-of-splitting cocycle; it is not a second deformation torus. Treating it as
independent of the map $S[P_\sigma]\to A$ would count every Fourier coordinate twice.

The polarization supplies two differently typed maps. The lattice map is

$$
\lambda:Y\longrightarrow X,
\tag{5.9a}
$$

whereas a theta rigidification supplies a quadratic automorphy exponent

$$
A:Y\longrightarrow P_\sigma^{\mathrm{gp}}.
\tag{5.9b}
$$

They satisfy

$$
A(y+y')=A(y)+A(y')+B\bigl(y,\lambda(y')\bigr).
\tag{5.9c}
$$

Thus $A(y)$ is an exponent, not an element of $X$. The corresponding logarithmic
automorphy factor is $q^{A(y)}$. A change of theta rigidification multiplies these
factors by a character of $Y$ and gives an isomorphic polarized Proj.

The polarization identifies $Y$ with a fractional ideal dual to $X$ and imposes symmetry

$$
B(y,\lambda(y'))=B(y',\lambda(y)),
\tag{5.10}
$$

together with (5.9c). Positivity says that $B(y,\lambda(y))$ is positive on every nonzero $y$ after evaluation against every interior point of $\sigma$. Level structure fixes the required torsion trivializations of this logarithmic one-motive.

Formula (5.9) packages valuation and leading unit in one Fourier coordinate. A map from
the monoid algebra chooses both. This is why the rank-$d$ Fourier lattice gives $d$ cusp
parameters rather than $d$ monomial parameters plus another $d$ unit-period parameters.

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

Fix a coherent $Y$-periodic polyhedral decomposition $\mathscr P$ of
$X_\mathbf R$ and its integral strictly convex universal exponent-valued support
function $\varphi$; evaluation by a monodromy form recovers the scalar support
function of Section 4.5. Thus the affine values below lie in
$P_\sigma^{\mathrm{gp}}$ (or its real scalar extension). After
replacing the polarization by a fixed positive power, assume that the vertices and
all affine branches of $\varphi$ are integral. Introduce a degree variable $z$.
For a cell $C\in\mathscr P$, put

$$
\widehat C_{\mathbf Z}
=\{(n,x)\in\mathbf Z_{>0}\oplus X:x\in nC\}\cup\{(0,0)\}.
\tag{6.1a}
$$

If $\varphi_C(u)=\ell_C(u)+c_C$ is the affine branch on $C$, its homogeneous
extension to the cone over $C$ is

$$
\Phi_C(n,x)=\ell_C(x)+nc_C
=n\varphi_C(x/n)\quad(n>0),
\qquad \Phi_C(0,0)=0.
\tag{6.1b}
$$

Thus $\Phi_C$, unlike $x\mapsto\varphi_C(x)$ on $nC$, is additive in the
homogeneous variables. Define

$$
Q_C=\{(n,x,p)\in\widehat C_{\mathbf Z}\oplus P_\sigma^{\mathrm{gp}}:
p-\Phi_C(n,x)\in P_\sigma\}.
\tag{6.1}
$$

This is a semigroup. Indeed, if $(n,x,p)$ and $(m,x',p')$ belong to $Q_C$ and
$n+m>0$, convexity of $C$ gives

$$
\frac{x+x'}{n+m}
=\frac n{n+m}\frac xn+\frac m{n+m}\frac{x'}m\in C
$$

with the terms of zero degree omitted, while homogeneity gives

$$
(p+p')-\Phi_C(n+m,x+x')
=\bigl(p-\Phi_C(n,x)\bigr)
 +\bigl(p'-\Phi_C(m,x')\bigr)\in P_\sigma.
\tag{6.1c}
$$

The zero-degree case is the embedded copy
$p\mapsto(0,0,p)$ of $P_\sigma$. Moreover, $Q_C$ is the lattice-point monoid of
the rational polyhedral cone cut out by $(n,x)\in\widehat C$ and
$p-\Phi_C(n,x)\in\mathbf R_{\ge0}P_\sigma$. Since $P_\sigma$ is saturated and
$\Phi_C$ is integral, this description proves both saturation and, by Gordan's
lemma, finite generation. No unproved closure under addition and no subsequent
ad hoc saturation are being used.

Its monoid algebra is generated by symbols

$$
z^n\vartheta_xq^p,
\qquad (n,x,p)\in Q_C,
\tag{6.2}
$$

with multiplication obtained by addition of triples. The normalized star over a
charted base $S[P_\sigma]\to A$ is
$A\otimes_{S[P_\sigma]}S[Q_C]$. On $C\cap C'$ the corresponding face
localizations agree. The difference $\Phi_C-\Phi_{C'}$ is now an integral
homogeneous linear function vanishing on the cone over the common face, so the
gluing map on the corresponding localization is multiplication by an invertible
monomial. The resulting graded algebra

$$
\mathcal R(\mathscr P,\varphi)=
\bigoplus_{n\ge0}\mathcal R_n
\tag{6.3}
$$

is best regarded as a sheaf on the union of the affine toric base charts. Its relative Proj before taking periods is the normalized infinite model $\widetilde P$.

There is a useful basis description. Define the global conical extension
$\Phi(n,x)=n\varphi(x/n)$ for $n>0$ and $\Phi(0,0)=0$. On a fixed normalized
star, $\mathcal R_n$ is the completed direct sum of the weights
$\vartheta_{(n,x)}$ with $x\in nC\cap X$, and multiplication has the form

$$
\vartheta_{(n,x)}\vartheta_{(m,x')}
=q^{\delta((n,x),(m,x'))}\vartheta_{(n+m,x+x')},
\qquad
\delta=\Phi(n,x)+\Phi(m,x')-\Phi(n+m,x+x').
\tag{6.4}
$$

Convexity of $\varphi$ makes $\delta$ lie in $P_\sigma$. It vanishes when the
two normalized weights lie in a common linearity cell; strict convexity makes it
nonzero across an actual wall. Thus the special fiber remembers exactly the
incidence complex of $\mathscr P$.

In rank one take $X=Y=\mathbf Z$, cells $[i,i+1]$, and prescribe
$\varphi(i)=i(i-1)/2$ at integral vertices, extending linearly on every cell. Put
$u_i=\vartheta_{(1,i)}$. On the vertex star where $u_i$ is inverted, the
degree-zero coordinates

$$
X_i=\frac{u_{i+1}}{u_i},\qquad
Y_i=\frac{u_{i-1}}{u_i}
$$

satisfy, by the homogeneous product formula,

$$
X_iY_i=q.
\tag{6.4a}
$$

Indeed the exponent is the second difference
$\varphi(i+1)+\varphi(i-1)-2\varphi(i)=1$; both numerator and denominator
otherwise have homogeneous weight $(2,2i)$. This calculation would be mistyped if
$\varphi_C$ were evaluated directly at an element of $nC$.

At $q=0$ this is a node. Translation identifies the right end of one component with the left end of the next; quotienting by a period of valuation $n$ gives the $n$-gon. This example simultaneously displays the monomial base parameter, the normalized branches, and the nonnormal conductor gluing.

### 6.2 Gluing and the period quotient

The period lattice acts on weights by $x\mapsto x+n\lambda(y)$ in degree $n$. The
required multiplier is determined by the bilinear period exponent $B$ and the quadratic
automorphy exponent $A$ of (5.9b). Set

$$
y\cdot\vartheta_x
=q^{B(y,x)+nA(y)}\vartheta_{x+n\lambda(y)}.
\tag{6.5}
$$

Symmetry of the period pairing is exactly the identity which makes (6.5) an action rather than a projective action. Changing the chosen quadratic refinement multiplies every degree-$n$ formula by a degreewise coboundary and therefore gives a canonically isomorphic Proj.

Here every expression is typed: $B(y,x)$ and $A(y)$ both lie in
$P_\sigma^{\mathrm{gp}}$, while $x+n\lambda(y)$ lies in $X$. To check the action,
apply first $y'$ and then $y$. Bilinearity gives

$$
\begin{aligned}
&q^{B(y',x)+nA(y')}
 q^{B(y,x+n\lambda(y'))+nA(y)}\\
&\qquad =q^{B(y+y',x)+n(A(y)+A(y')+B(y,\lambda(y')))}\\
&\qquad =q^{B(y+y',x)+nA(y+y')},
\end{aligned}
\tag{6.5a}
$$

where the last equality is (5.9c). Symmetry
$B(y,\lambda(y'))=B(y',\lambda(y))$ makes this independent of the order of the two
translations. This calculation proves the cocycle on triple period overlaps without
identifying an exponent with a character-lattice element.

The exponent in (6.5) need not lie in $P_\sigma$ on one affine star. The formula is a map
from that star algebra to the algebra of its $y$-translate, localized along their common
face; the support-function inequalities make the displayed exponent regular on that overlap.
The inverse uses $-y$ on the reverse overlap. Thus (6.5) is an action on the glued periodic
model, not an assertion that every multiplier is a global element of one unlocalized monoid
algebra.

Choose finitely many cells representing $Y$-orbits. Glue their normalized stars along common faces and identify translated boundary faces by (6.5). Since only finitely many orbit representatives occur, the quotient

$$
P_A=\widetilde P/Y
\tag{6.6}
$$

is proper and of finite presentation once the base is noetherian. On a geometric
boundary stratum, the normalization of the fiber is the disjoint union, with face
gluings, of finitely many normalized stars; the fiber itself need not be normal.
The conductor identifications between translated outer faces create the familiar
cycle of projective lines in the rank-one special fiber. This is a fiberwise
statement. The total space can be normal even when its special fiber is not, as
$XY=q$ already shows.

The quotient can also be described without taking a quotient of an infinite object. Choose a finite fundamental polytope, list its boundary-face pairings, and take the coequalizer of the two finite unions of face schemes. The coordinate ring on an affine patch is the equalizer of the two restriction maps. This finite presentation will be used in Chapter 10.

### 6.3 Flatness, properness, and the group locus

Every affine star algebra is flat over $A$: before taking Proj, each graded weight
piece is a direct sum of copies of $A$, and localization at a homogeneous monomial
preserves that property. The finitely many standard Proj opens therefore give a flat
cover of $P_A$. Equivalently, the periodic theta algebra is degreewise $A$-flat and
its standard degree-zero localizations are $A$-flat. This proves flatness of the
total family without normalizing it.

After base change to a geometric boundary stratum, the normalization and conductor
of that fiber do satisfy the exact sequence

$$
0\longrightarrow\mathcal O_{P_{\bar s}}
\longrightarrow\nu_*\mathcal O_{P_{\bar s}^\nu}\oplus\mathcal O_C
\longrightarrow\nu_*\mathcal O_{C^\nu}
\longrightarrow0
\tag{6.7}
$$

where $C$ and $C^\nu$ now denote the conductor schemes of that fiber. The last arrow
is surjective on monomial bases.

The surjectivity is visible weight by weight. A conductor face ring retains the
weights in its face semigroup and sends every other weight to zero. Every retained
weight has the same named lift in the adjacent star. The cokernel therefore vanishes
in each weight. Sequence (6.7) may be pulled back along a map inside the fixed
boundary stratum; no assertion that normalization commutes with a smoothing base
change is made.

Properness follows from the valuative criterion. Over a valuation ring, a point of the generic torus has a valuation vector in $X_\mathbf R$. Completeness of the periodic decomposition places it in some cell after translation by $Y$, and the corresponding toric chart gives an extension. Two extensions agree because their valuation vectors lie in a common face after passing to a common refinement. The same argument after finite extension handles nonsplit tori; descent gives the original extension.

Where every nonzero $q^p$ is invertible, all toric boundary divisors disappear. Formula (6.5) then gives the quotient of the Raynaud extension by its period lattice, hence the original abelian scheme. The smooth group locus extends across the base as the semiabelian scheme $G$ of Chapter 2 and acts on $P_A$. Each geometric fiber has finitely many $G$-orbits, with one orbit for every cell modulo $Y$.

The construction is separated before it is proper. If two star charts contain the same torus point over a valuation ring, their valuation vector belongs to the intersection of the two cells, and the face localization identifies the extensions. Thus the diagonal satisfies the valuative uniqueness criterion. Completeness of the cells supplies existence, so together they prove the full valuative criterion used above.

Connectedness follows from the cell complex. Every star is connected, adjacent stars
meet along a nonempty face, and the periodic decomposition of the real vector space
is connected. On a nonnormal boundary fiber, (6.7) then shows that the only global
idempotents are zero and one. On the abelian locus this is clear, and the same
weight-basis calculation handles intermediate faces.

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

## 7. The Raw-DF-IIT prerequisite

This chapter works after a Mumford label has been fixed. It does not supply GCC and
cannot be the first missing step for an arbitrary geometric boundary object.

### 7.1 The raw non-cancellative defect monoid

Homogenize a theta weight as $a=(n,x)$ and let $W_C$ be the weight semigroup on a
labelled affine star. Begin with the free commutative monoid on a symbol $[a,b]$
for every multiplication map whose source and target occur on a common localized
star. Impose only relations actually supplied by the structure: multiplication
identity, commutativity and associativity; restriction to a face; period translation;
the two conductor arrows; $\mathcal O_F$-equivariance; and the polarization and
cubical-theta identities. In particular impose

$$
[a,0]=0,\qquad [a,b]=[b,a],\qquad
[a,b]+[a+b,c]=[b,c]+[a,b+c].
\tag{7.1}
$$

Do not cancel, group-complete, sharpen, or saturate this presentation. Denote the
resulting raw, generally non-cancellative monoid with its labelled period loops by
$D_{\mathscr P}^{\mathrm{raw}}$. This object is genuinely intrinsic to the displayed
star, face, period, conductor, endomorphism, and polarization diagrams. Passing at
once to piecewise-linear bends modulo affine functions loses precisely the
information that is in dispute.

For an ambient deformation over $A$, the torus grading on a star is

$$
R_C=\bigoplus_{a\in W_C}L_a,
\tag{7.2}
$$

where each expected $L_a$ is an invertible $A$-module after an affine localization.
Multiplication gives maps $L_a\otimes L_b\to L_{a+b}$. The invariant way to record
their defects is not a scalar modulo units. Let $\operatorname{Div}(A)$ be the
Picard groupoid whose objects are pairs $(L,s)$ consisting of an invertible
$A$-module and a section, whose arrows are isomorphisms carrying section to section,
and whose symmetric monoidal product is tensor product. A multiplication map gives
the object

$$
\bigl(L_a^{-1}\otimes L_b^{-1}\otimes L_{a+b},\;m_{a,b}\bigr)
\quad\text{in }\operatorname{Div}(A),
\tag{7.3}
$$

with the evident dual convention if multiplication is written in the opposite
direction. Associativity supplies the coherence arrows. Period loops retain their
unit automorphisms; these are the leading units and period holonomy that the quotient
$A/A^\times$ forgets.

For a framed cusp and a face $\tau$ of dimension $r$, the target Deligne--Faltings
(DF) monoid is

$$
P_{\sigma,\tau}^{\mathrm{fr}}
\simeq \mathbf N^r\oplus\mathbf Z^{d-r}.
\tag{7.4}
$$

Thus its sharp part has $r$ boundary generators and its unit group has $d-r$
period generators. Here and everywhere below $r=\dim\tau$, never the codimension of
$\tau$.

### 7.2 Why the quotient by units does not prove recognition

Choosing bases of the $L_a$ writes multiplication as
$e_ae_b=c(a,b)e_{a+b}$ and produces classes $[c(a,b)]$ in $A/A^\times$.
That quotient is useful bookkeeping but is not cancellative. For

$$
A=k[e,h]/(e,h)^2
\tag{7.5}
$$

one has $[e]^2=[h][e]=[0]$ although $[e]\ne[h]$. Thus an associativity equality
after multiplication by a vanishing defect does not identify the remaining defects.
The proposed wall-path proof did exactly this implicitly, even when it said that no
element was divided.

Nor can one pass from an even submonoid and choose roots. For
$A=k[e]/e^2$, the homomorphism $2\mathbf N\to A/A^\times$ sending
$2\mapsto[e]$ need not extend to $\mathbf N$: an extension would require a class
$x$ with $x^2=[e]$, while the square of a unit is a unit and the square of every
nonunit is $[0]$. Regularity or saturation of the abstract Fourier monoid does not
supply such a root in $A$.

There is also a potential secondary-fan kernel which the former bending argument did
not address before using the cubical and PEL relations.
Take $X=\mathbf Z$ and $Y=2\mathbf Z$. Give the integral vertices the periodic
piecewise-linear values

$$
f(n)=0\ \text{for even }n,\qquad f(n)=1\ \text{for odd }n,
\tag{7.6}
$$

and extend linearly on each unit interval. This is nonconstant and not globally
affine, but its $Y$-period change is zero. Hence its Fourier bilinear period datum is
zero although its alternating wall bends are not. This particular $f$ is not claimed
to satisfy convexity or every cubical PEL relation and is not an ambient deformation.
It proves only that the forgetful map from periodic PL data to period-change data has
a kernel before those additional relations are used. Polygon relations and quotienting
by global affine functions do not show that all the additional relations kill that
kernel in the raw, non-cancellative object.

These examples show that the former arguments did not prove
$D_{\mathscr P}^{\mathrm{sat}}\simeq P_\sigma$ or justify the subsequent lift from
$P_\sigma\to A/A^\times$ to a chart. They do not disprove Raw-DF-IIT and do not
invalidate the explicit Mumford construction of Chapter 6, where the DF chart is
supplied at the outset.

### 7.3 The exact Raw-DF-IIT hypothesis

**Hypothesis 7.1 (raw Deligne--Faltings intrinsic infinitesimal theorem,
Raw-DF-IIT).** Let $d\ge2$, fix a framed Hilbert--Blumenthal cusp, a regular cone
$\sigma$, a face $\tau$, the refined periodic decomposition of Section 4.5, and an
ambient structured cusp deformation over a complete noetherian ring $A$. Begin with
$D_{\mathscr P}^{\mathrm{raw}}$, without cancellation or saturation, using all the
multiplication, face, period-translation, conductor, $\mathcal O_F$, and polarization
relations. The following assertions are required simultaneously.

1. The intrinsic sharp quotient and the loop/unit group of the raw defect object
   identify, respectively, with
   $(P_{\sigma,\tau}^{\mathrm{fr}})^\sharp$ and
   $(P_{\sigma,\tau}^{\mathrm{fr}})^\times$, compatibly enough to reassemble the
   framed Fourier monoid $P_{\sigma,\tau}^{\mathrm{fr}}$ itself. No identification
   is obtained by cancellativizing $A/A^\times$.
2. The secondary-fan kernel vanishes after all the displayed structural relations
   are imposed: a periodic PL defect with trivial framed Fourier sharp data and
   trivial loop holonomy is already trivial in the raw defect object.
3. The multiplication data define a symmetric monoidal functor
   $P_{\sigma,\tau}^{\mathrm{fr}}\to\operatorname{Div}(A)$. It retains the actual
   leading units and period holonomy and yields a framed DF chart, including when
   sections vanish or are nilpotent.
4. If a DF chart was already supplied and the object is the corresponding Mumford
   construction, the recovered functor is canonically isomorphic to that supplied
   chart. Thus Raw-DF-IIT is a recognition theorem, not a second construction with
   an unrelated chart.
5. Recovery commutes with face restriction, both conductor arrows, arbitrary
   square-zero base change, and changes of cusp. The comparison isomorphisms satisfy
   the cocycle, and iteration over square-zero thickenings is compatible with adic
   completion. This compares conductor arrows already present in the labelled
   object; it does not choose roots after passage to a finite frame lattice. That
   separate $\mu_r$-coherence problem is FRCD, Hypothesis 9.1.

This hypothesis is exact: dropping the raw monoid, the $\operatorname{Div}(A)$-valued
functor, loop holonomy, or the secondary-kernel assertion recreates one of the gaps
in Section 7.2. No proof of the required higher-rank statement is contained in this
manuscript. Book 111, Theorem 13.1 is used only for its rank-one global
compactification; we do not attribute this exact arbitrary-ambient recognition
statement to that theorem or to Book 110.

### 7.4 Conditional reconstruction of all PEL data

Assume Raw-DF-IIT. Trivializing its DF lines on one affine star rewrites the recovered
symmetric monoidal functor as a monoid chart

$$
\alpha:P_{\sigma,\tau}^{\mathrm{fr}}\longrightarrow A,
\tag{7.7}
$$

but the functor, rather than this choice of scalars, is canonical. A different
trivialization changes $\alpha$ by a unit character while retaining its loop
holonomy. Assertion 4 of Raw-DF-IIT makes (7.7) equal to an already supplied Mumford
chart up to the unique DF isomorphism.

With compatible local generators the multiplication maps take the Mumford form

$$
e_ae_b=\alpha\bigl(\delta(a,b)\bigr)e_{a+b}.
\tag{7.8}
$$

This is now a consequence of the $\operatorname{Div}(A)$-valued factorization; it is
not deduced by cancelling scalar coefficients. Face compatibility glues the star
algebras, and conductor compatibility identifies their restrictions in the pushout
(6.7). Period holonomy recovers the multiplier

$$
y\cdot e_x
=q^{B(y,x)+nA(y)}e_{x+n\lambda(y)},
\tag{7.9}
$$

with $B:Y\times X\to(P_{\sigma,\tau}^{\mathrm{fr}})^{\mathrm{gp}}$,
$\lambda:Y\to X$, and

$$
A(y+y')=A(y)+A(y')+B(y,\lambda(y')).
\tag{7.10}
$$

The $\mathcal O_F$-graphs give balance of $B$, and the cubical polarization gives
$B(y,\lambda(y'))=B(y',\lambda(y))$. The identity and action graphs, theta
rigidification, polarization, and finite level graphs are then recovered weight by
weight exactly as in the explicit Mumford construction. Neat level removes residual
automorphisms. These reconstruction steps are formal once Raw-DF-IIT supplies the
DF functor; they do not prove that hypothesis.

### 7.5 Consequences for IIT and completion

Square-zero compatibility in Raw-DF-IIT permits iteration through
$A/K\leftarrow A/K^2\leftarrow\cdots\leftarrow A/K^m=A$. Its adic compatibility
then passes to $A\simeq\varprojlim A/I^n$. Finite presentation of the star algebras
and finiteness of the graph and line-bundle Hom modules make the inverse limits
effective. Conductor and cusp-change compatibility make the resulting isomorphisms
glue and satisfy their cocycles.

**Conditional Theorem 7.2 (intrinsic infinitesimal recognition, IIT).** For $d\ge2$,
assuming Raw-DF-IIT, the Mumford construction induces an equivalence between unframed
charted toroidal tests and unframed ambient structured cusp deformations of the
labelled fiber. Assuming FRCD as well, the equivalence extends to framed tests for
$P_{\sigma,\tau}^{\mathrm{fr}}$ with their exact conductor-root comparisons. The inverse recovers the DF chart,
semiabelian group, action, $\mathcal O_F$-endomorphisms, polarization, level, theta
line, and both conductor arrows. It commutes with faces, square-zero and complete
base change, conductor restriction, and cusp changes.

For $d\ge2$, IIT is not unconditional here: Conditional Theorem 7.2 is precisely
the formal consequence of the unproved Hypothesis 7.1. The separate rank-one global
compactification imported from Book 111, Theorem 13.1 is not asserted here to prove
this full equivalence of arbitrary ambient deformation groupoids.

## 8. The inverse problem and completed deformation rings

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

If $A$ is reduced but not normal and a DF chart and its conductor compatibility are
already supplied, perform the extraction on its finite normalization. The two
pullbacks then agree on the conductor by the supplied arrows, and the unit factors
lie in the equalizer defining $A$. Without a supplied chart, recognizing those
arrows is part of Raw-DF-IIT and is not a consequence of the normal calculation.

### 8.2 Full faithfulness

Let $f:P_1\to P_2$ be an isomorphism of Mumford-presented or toroidal PEL
objects. On the open group orbit it induces an isomorphism of semiabelian schemes, hence of
character lattices and Raynaud extensions. The pullback of normalized weight functions
determines its effect on periods. Since a star neighborhood is generated by its
labelled weight algebra, that effect determines $f$ on the star cover. The
neighborhoods cover the total family, so they determine $f$ everywhere; on a
nonnormal boundary fiber the same statement is recorded by its conductor pushout.

Conversely, an isomorphism of polarized logarithmic one-motives transports the weight
algebra (6.3), the period action (6.5), and every conductor pairing. It therefore induces
an isomorphism of explicitly charted Mumford objects. This proves full faithfulness on
the Mumford side. Extending the assertion to arbitrary ambient complete deformations is
conditional on Theorem 7.2, hence on Raw-DF-IIT.

### 8.3 Conditional essential surjectivity

For a normal reduced base with schematically dense puncture, Section 8.1 extracts a
one-motive and the construction of Chapter 6 produces a Mumford object $P^{\mathrm M}$.
They agree over the fraction fields. On each normalized star their graded weight algebras
have the same monomial orders and the same leading units, so they agree over $A$ by
(5.5). The conductor face identifications are restrictions of those same period factors;
hence $P^{\mathrm M}\simeq P$.

For a reduced excellent base with a supplied compatible DF chart, the same argument
descends the isomorphism from the finite normalization through the conductor equalizer
(10.2). For an arbitrary ambient object, both this conductor comparison and the
nilpotent step are Raw-DF-IIT assertions. Conditional Theorem 7.2 supplies them, and
finite presentation then passes the result to an adic inverse limit.

**Conditional Proposition 8.1 (Mumford period equivalence, MPE).** For $d\ge2$,
assuming Raw-DF-IIT, polarized logarithmic one-motives of the fixed unframed
Hilbert--Blumenthal cusp
type are equivalent to ambient structured cusp deformations. The equivalence commutes
with arbitrary complete base change, face restriction, theta lines, group and action
graphs, endomorphism and level graphs, cusp changes, and both conductor arrows.
For the framed statement with exact conductor roots, assume FRCD as well.

Without Raw-DF-IIT, the proved statement is the same equivalence with “ambient
structured cusp deformations” replaced by “objects already supplied with a compatible
DF chart”: that is the explicit Mumford construction and its fully faithful inverse.

### 8.4 Completed local rings

Fix a geometric point $z$ of a nonzero cusp orbit, corresponding to a prime
$\mathfrak p_z\subset S_0[P_\sigma]$. In the Hilbert--Blumenthal boundary case the
Raynaud abelian quotient is zero. The split torus, the two projective rank-one
$\mathcal O_F$-lattices, the ordered polarization, and prime-to-the-base rigidifications
are locally constant (the frame choices are finite etale). The only positive-dimensional
deformation datum is the Fourier homomorphism. Its leading units and its orders are the
same $d$ characters of the rank-$d$ Fourier lattice, as explained after (5.9).

Consequently the completed ring of the framed, already charted Mumford deformation
functor is

$$
R_{z,\mathrm M}^{\mathrm{fr}}
=\widehat{\bigl(S_0[P_\sigma^{\mathrm{fr}}]\bigr)_{\mathfrak p_z}}.
\tag{8.3}
$$

Here $P_\sigma^{\mathrm{fr}}$ is the Kummer-refined monoid when paired frames are
present and is $P_\sigma$ otherwise. A local map from (8.3) to an Artin algebra is
exactly a local Fourier-character map, and Chapter 6 constructs the associated Mumford
object. If $\sigma$ is regular and full-dimensional, the relative completed ring is a
power-series ring in $d$ variables. This agrees with Book 156: the interior Hilbert
moduli scheme is smooth of relative dimension $d$. There is no additional rank-$d$
unit-period factor.

If $\tau$ is a nonzero face of dimension $r$, its completed monoid is
$\mathbf N^r\oplus\mathbf Z^{d-r}$: localization leaves $r$ boundary parameters
and makes $d-r$ Fourier or period parameters units. The total relative dimension is
$d$. The integer $r$ is the dimension of $\tau$, not its codimension.
At the zero face one instead has the ordinary $d$-dimensional deformation ring of the
abelian object. Conditional Theorem 7.2 identifies (8.3) with the completed ring of
every labelled ambient structured semiabelic PEL deformation at $z$; without
Raw-DF-IIT, (8.3) represents only the supplied-DF/Mumford subfunctor.

If a finite stabilizer $H_z$ remains before neat rigidification, the unframed completed local ring is the invariant ring

$$
R_{z,\mathrm M}=(R_{z,\mathrm M}^{\mathrm{fr}})^{H_z}.
\tag{8.4}
$$

In the regular neat charts of Theorem 4.2 the stabilizer of a nonzero cone is trivial.
Face localization in the monoid identifies the completed deformation rings on overlaps.

### 8.5 Traits and boundary-supported Artin rings

For a trait $V$ with uniformizer $\pi$, a supplied map $P_\sigma\to V$ is determined by nonnegative valuations $\ell(p)=v(q^p)$ and unit leading coefficients. The function $\ell$ lies in $\sigma$; after a finite Kummer extension it is integral. The extracted one-motive is the classical Raynaud one-motive, and Chapter 6 identifies its explicitly charted Mumford model with the extension of the fixed periodic type.

For $A=k[\epsilon]/(\epsilon^n)$ no trait sees the higher nilpotents. Ring (8.3)
unconditionally represents the supplied-DF/Mumford functor on such tests. A relation
$XY=\epsilon$ is the supplied map $q\mapsto\epsilon$, whereas $XY=0$ is the supplied
map $q\mapsto0$. The assertion that arbitrary intrinsic multiplication data determine
these Artin directions is exactly the square-zero clause of Raw-DF-IIT.

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

This proves finiteness, not flatness. Flatness is a separate issue addressed in
Hypothesis 9.2 below.

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

### 9.4 Unframed-first normalization of paired frames

Refine the fan in the lattice dual to $M^{\mathrm{fr}}$ and regularize equivariantly as in Chapter 4. Then the framed chart is smooth over the smooth coefficient stratum, with boundary a relative normal-crossings divisor. The finite deck group $\Delta$ acts on paired frames, the refined lattice, the fan, and the Mumford family.

Regularity of the framed chart by itself says nothing about flatness of its finite
map to the unframed chart, and equality after taking a power says nothing about a
chosen root on a conductor. We isolate both points.

**Hypothesis 9.1 (frame-root and coherent conductor descent, FRCD).** For every
finite-index frame or theta-frame lattice used in the manuscript and every pair of
identified conductor faces, the rigidified frame datum includes an actual comparison
of the corresponding root lines with section. If two local comparisons have equal
$r$th powers, their possible discrepancy is a $\mu_r$-torsor (and, where a ratio is
defined, an element of $\mu_r$); the datum chooses the comparison itself, rather
than declaring that discrepancy to be one. These choices are compatible with face
restriction, both conductor arrows, period translation, compositions of nested
frame lattices, deck transformations, triple overlaps, coefficient extension, and
arbitrary nilpotent base change. They make the resulting conductor descent datum
effective and satisfy its cocycle.

The existence of the over-lattice $M^{\mathrm{fr}}$ does not prove FRCD. It records
which exponents are allowed, but it neither selects a point of each $\mu_r$-torsor
nor proves coherence of those selections.

**Hypothesis 9.2 (Kummer finite flatness, KFF).** After one common equivariant
refinement, for every inclusion among the unframed, paired-frame, theta-frame, and
combined frame lattices used below, every induced finite monoid-algebra map

$$
S_i[\sigma^\vee\cap M_i]\longrightarrow
S_j[\sigma^\vee\cap M_j]
\tag{9.8}
$$

is finite locally free, faithfully flat on the relevant components, and compatible
with face localization, composition of lattice inclusions, and coefficient base
change. The corresponding normalization of each global unframed chart in its
generic framed algebra is represented locally by (9.8), so that the later descent
maps are genuinely fppf.

Finiteness of normalization does not imply KFF. For example, over a field of
characteristic different from two,

$$
k[x^2,xy,y^2]\longrightarrow k[x,y]
\tag{9.9}
$$

is the finite integral closure in the indicated degree-two extension of function
fields, but it is not flat: the generic rank is two, whereas the fiber over the
vertex has $k$-basis $1,x,y$ and dimension three. A proof of KFF would therefore
have to establish simultaneous regularity for every nested lattice and deduce a
local finite-free monomial basis. No such simultaneous argument is given here.

On the interior, forgetting the frame is a finite etale cover. At the boundary it is
finite Kummer and usually ramified; it is finite flat only under KFF. The valid
global order is therefore not to build a
framed compactification and descend it by an IIT argument. One first constructs the
unframed compactification, conditionally on GCC and Raw-DF-IIT where unframed AEC is
used, and then takes its
normalization in the finite generic paired-frame cover. The universal property of
normalization extends every generic deck transformation to that normalization and
makes the group law automatic.

The explicit monoid calculation (9.6) identifies the completed branches of this
normalization. What normalization alone does not prove is compatibility of the
extended action with the labelled conductor arrows, coherent choice of roots on
those arrows, its behavior across nilpotent base change, or flatness over the
unframed chart. These are precisely the Raw-DF-IIT-, FRCD-, and KFF-dependent
assertions isolated in Chapter 12.

## 10. Bounded normalization and conductor presentations

### 10.1 The conductor square

For a reduced semiabelic fiber, or a family restricted to one fixed boundary
stratum, let $\nu:P^\nu\to P$ be its finite normalization and let

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

is both cartesian and a pushout. In a Mumford boundary fiber, $P^\nu$ is the union
of normalized stars and $C^\nu$ is the union of paired toric faces. The construction
is made separately on each of the finitely many monomial strata. We never identify
it with the normalization of the total smoothing family.

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

For every normalized-star family on a fixed boundary stratum in the combinatorial
collection, $\Theta^{m_0}$ gives a closed immersion

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

The right side ranges over a finite list because the number of star and face orbits
is bounded by the chosen periodic decompositions. Thus the Hilbert polynomials of the
boundary-stratum schemes $P$, $P^\nu$, $C$, and $C^\nu$ belong to finite sets. The
total smoothing family has its own fixed theta Hilbert polynomial and is parameterized
separately.

The multiplication tables are bounded as well. Choose the finite theta-weight generators in degrees at most a common $d$. Products are monomials times units, with exponents drawn from the finite set of differences of support-function values on representative cells. Conductor maps discard weights not lying on the relevant face and multiply the surviving ones by period units. Consequently a fixed finite list of generators and relations presents every normalization-conductor diagram.

The structure maps require separate parameter data; they are not recovered from the
Hilbert point of $P$. A fixed toric compactification would not suffice, because the
generic smooth group is an abelian variety rather than the cusp torus. Instead use the
theta embedding of $P$ itself and retain the following finite list.

1. Retain the identity section and the projective closures
   $$
   \overline\Gamma_m\subset P\times P\times P,
   \quad
   \overline\Gamma_i\subset P\times P,
   \quad
   \overline\Gamma_\mu\subset P\times P\times P
   \tag{10.6a}
   $$
   of multiplication, inverse, and the action on their smooth group domains. The
   common domain $G\subset P$ is retained as the open locus on which the appropriate
   graph projections are isomorphisms and the fibers are smooth. This is a locally
   closed finite-presentation condition: graph projection isomorphism is open in the
   finite-presentation locus, and smoothness is open. On the abelian locus, the
   cubical formula expresses the pullback of $\Theta$ under multiplication using the
   three projections and the Poincare factor, so the graph Hilbert polynomials depend
   only on the fixed polarization type. On boundary stars the equations are the
   bounded weight coactions. Hence one finite list controls both loci.
   Retain separately the local split-torus coaction graph on every labelled affine
   star; equality with the restriction of the global action is a closed graph
   identity.
2. For a fixed integral generating set of $\mathcal O_F$, retain the graph of each
   endomorphism of $P$ and of the smooth group locus. Its weight map is
   $x\mapsto ax$, so again only the fixed finite exponent list occurs. Impose the ring,
   action, and determinant identities as equality loci of composites of these graphs.
3. Retain the normalized theta line as a point of the relative Picard--Isom scheme in its
   fixed Hilbert-polynomial component, its rigidification, the cubical isomorphism on the
   action graph, and the symmetry isomorphism inducing the ordered polarization. The theorem
   of the square turns the cocycle and Rosati identities into equalities between morphisms of
   line bundles on fixed finite fiber products.
4. Retain every prime-to-the-base level section and pairing isomorphism as a graph from the
   fixed finite etale source. Its rank is fixed. The homomorphism, full-frame, determinant,
   and Weil-pairing conditions are respectively closed identities and open-and-closed rank
   conditions.
5. Retain both conductor arrows, the restriction of every preceding graph to the conductor,
   and the theta descent isomorphism between the two pullbacks to $C^\nu$. Include its
   cocycle on $C^\nu\times_C C^\nu\times_C C^\nu$.

Every ambient product here is projective, and every graph has
a Hilbert polynomial in a finite list because its defining monomial matrices use the same
bounded weights. Relative Hilbert schemes parameterize the closed graphs; the condition that
a graph project isomorphically to its source is locally closed. Relative Isom schemes of the
fixed line bundles parameterize the cubical, polarization, pairing, and conductor descent
maps. Thus these data really parameterize the semiabelian group, action, endomorphisms,
polarization, level, and theta descent rather than merely the underlying pushout.

This finite list gives an explicit parameter space. Take the product of the Hilbert
schemes for $P$, $P^\nu$, $C^\nu$, and $C$ with the multiplication, inverse, action,
endomorphism, level, and conductor graph schemes and the line-bundle Isom schemes just
listed. Incidence, the common smooth group domain, finiteness, face-pairing, and the
conductor equalizer are conditions on finitely many universal maps. Associativity and
every action, PEL, cubical, level, and descent cocycle are equality loci of morphisms
between projective families; flatness and the prescribed Hilbert polynomial are open
conditions. Thus the admissible structured diagrams occupy a finite union of locally
closed finite-type subschemes.

The universal equations define a finite-type scheme $\mathcal B_{\mathrm M}$ of
structured diagrams arising from the explicit Mumford charts. Conversely, its open
flatness, smoothness, ampleness, and full-level conditions together with its closed
group, action, PEL, cubical, and conductor identities describe exactly the explicit
bounded diagrams just listed. No structure is reconstructed from a Hilbert point.

The bounds are unconditional for these explicit Mumford families: their weights,
cells, conductor faces, and structure matrices were fixed before the parameter space
was formed. Claiming that every arbitrary ambient boundary deformation belongs to
the same finite list would first require GCC to classify its geometric fiber and
then Raw-DF-IIT (with FRCD for exact framed conductor roots) to recognize its
deformations. None may be used as an input to its own proof. We therefore make no
such circular claim.

**Proposition 10.1 (bounded explicit conductor presentations, BCP).** For fixed PEL
data, level, paired frames, and the finite admissible decompositions, every explicit
Mumford chart has the finite affine-star presentation above. After restriction to
each boundary stratum, its normalization-conductor diagram is embedded in the fixed
projective spaces. The identity, group, action, endomorphism, polarization, level,
cubical-line, conductor, and theta-descent graphs have polynomials and defining
degrees in finite lists, and $\mathcal B_{\mathrm M}$ is of finite type. The total
Mumford family and all its structure graphs commute with arbitrary charted base
change; the normalization-conductor square commutes with base change inside its fixed
monomial stratum.

For $d\ge2$, assuming GCC, Raw-DF-IIT, and, for framed conductor roots, FRCD, Conditional Theorem
7.2 recognizes an arbitrary labelled ambient boundary deformation as one of these
explicit objects and transports the same bounds to it. This conditional recognition
is not part of BCP.

### 10.4 Pushouts and nonnormal fibers

Conversely, on one boundary stratum begin with a diagram
$C^\nu\to P^\nu$ and $C^\nu\to C$ from the bounded list, with the first
arrow a closed immersion and the second finite, satisfying the face-pairing
equivalence relation. On affine patches form

$$
\mathcal O_P
=\mathcal O_{P^\nu}\times_{\mathcal O_{C^\nu}}\mathcal O_C.
\tag{10.7}
$$

Surjectivity of $\mathcal O_{P^\nu}\to\mathcal O_{C^\nu}$ makes these affine
pushouts compatible with localization. They glue to a finite type proper scheme $P$
over that stratum. Exactness of (6.7) and the monomial-basis argument prove flatness
along the stratum. The action, PEL endomorphisms, and theta line descend when their
two restrictions to $C^\nu$ agree. The smoothing transverse to the stratum is
constructed from the total monoid algebra in Chapter 11, not from this fiberwise
pushout.

The fiber may be nonnormal even though every star is normal. That is intended. Normalizing it again loses the periodic face identification and therefore loses the semiabelic object. All subsequent constructions retain the entire square (10.3).

## 11. A finite-type algebraic Mumford chart

### 11.1 Construction from explicit monoid algebras

Fix one framed cusp and one regular cone $\sigma$. In the Hilbert boundary case the
Raynaud abelian part is zero and there is no smooth unit-period torus. Let $S$ be the
standing coefficient ring after the finite etale extension that rigidifies the constant
prime-to-the-base data. Begin with the algebraic toric chart

$$
U_\sigma=\operatorname{Spec}S[P_\sigma],
\tag{11.1}
$$

rather than with a completed deformation functor.

The rigidified constant frame choices form a finite etale scheme $E$ over the standing
coefficient base. On an affine frame component,

$$
S=\mathcal O(E).
\tag{11.1a}
$$

It is etale over the coefficient base. For a general, non-Hilbert PEL cusp one would
tensor this ring with an affine chart of the abelian and extension moduli, but that
mixed case does not occur here by Theorem 2.1. Thus no complete local ring is being
silently treated as a finite-type coefficient ring and the relative dimension of
$U_\sigma$ is $d$.

Over it, construct the finite collection of normalized star algebras
$S[Q_C]$ from (6.1), viewed as $S[P_\sigma]$-algebras through
$p\mapsto(0,0,p)$. The theta algebra is generated in degrees at most a
fixed bound by Proposition 10.1, so its relative Proj is of finite presentation. Glue
stars along common face localizations and impose the finitely many period
identifications (6.5). On a boundary stratum their restriction is the conductor
equalizer (10.7). This produces a projective finite-type family

$$
P_\sigma^{\mathrm{alg}}\longrightarrow U_\sigma.
\tag{11.2}
$$

All coefficients in its equations are either universal units from $S$ or explicit monomials $q^p$. Associativity, polarization symmetry, the $\mathcal O_F$-action, and level compatibility are finite polynomial identities and hold universally because they hold in the defining period algebra.

Varying the finitely many cusp, cone, and cell-orbit types and adjoining the finite
paired-frame choices gives a finite disjoint union $U^{\mathrm{fr}}$ of explicit
algebraic charts. Section 11.4 identifies their completions with the supplied-DF
Mumford functor. The stronger assertion that their classifying morphism is etale and
exhaustive for arbitrary ambient deformations is conditional AEC.

### 11.2 Algebraizing star gluing and the boundary conductor

The total smoothing family is constructed from the finitely presented star algebras,
not by normalizing its fibers. Glue the affine star charts along the face
localizations of (5.3), then impose the finitely many period identifications (6.5)
on the resulting open overlaps. Equivalently, take the relative Proj of the finite
theta algebra generated in the bounded degrees of Section 10.2. Both descriptions
use finitely many generators and relations over $S[P_\sigma]$ and commute with
arbitrary base change. They give (11.2); properness follows from the relative Proj
or from Section 6.3.

Now restrict to a monomial boundary stratum. The fiber becomes the finite periodic
union of toric stars. Its normalization, conductor faces, and paired-face quotient
are explicit finite-presentation schemes, and on each invariant affine open their
coordinate rings satisfy the equalizer (10.7). Surjectivity to the face ring proves
that the equalizers glue and agree with the restriction of the total Proj. Thus the
conductor pushout is algebraized exactly where it exists, while the transverse
smoothing remains in the total monoid equations.

For the rank-one cusp this distinction is visible. Over
$U=\operatorname{Spec}S[q]$ the total affine equation is
$S[q,X,Y]/(XY-q)$, which is normal. At $q=0$ its fiber has normalization
$S[X]\times S[Y]$ and conductor the two origins. Periodically pairing these origins
produces the $n$-gon special fiber. Normalizing the total space would not produce
those two branches; restricting first and then using (10.7) does. The
higher-dimensional construction is the same finite operation indexed by monomial
strata, cells, and faces.

### 11.3 Fine saturated charts and conditional AEC

We now prove the logarithmic chart assertion without using singularity ideals. At a point on the orbit indexed by a face $\tau\preceq\sigma$, the base has an open neighborhood

$$
\operatorname{Spec}S[P_{\sigma,\tau}].
\tag{11.3}
$$

Section 5.1 proved directly that $P_{\sigma,\tau}$ is finitely generated, integral,
and saturated. If $r=\dim\tau$, its sharp quotient is the dual monoid of $\tau$ in
the quotient by $\tau^\perp$ and is $\mathbf N^r$ because the fan is regular; its
unit group is $\mathbf Z^{d-r}$. Therefore the divisorial logarithmic structure is
fs, and the map to the coefficient stratum is log smooth with $r$ boundary and
$d-r$ invertible period parameters.

For the family, a normalized star at a cell face $D\preceq C$ has chart by the localized saturation

$$
Q_{C,D}
=Q_C+(Q_C\cap D^\perp)^{\mathrm{gp}}.
\tag{11.4}
$$

It is fs by the same lattice-cone proof. On a conductor face the two characteristic
monoids identify with the same face submonoid; the period multiplier is a unit and
does not change the sharp characteristic. This gives the candidate equalizer of the
two fs face charts. It does not by itself give coherent descent of roots of its
monomial sections.

Thus the base and every normalized-star chart are unconditionally fs and saturated
before any deformation-theoretic comparison. The constructed boundary ideal is the
image of the positive elements of $P_\sigma$. It cuts out the expected union of
toroidal strata and is compatible with every face map. Saturation and effectivity
after the nonnormal conductor pushout additionally require FRCD.

Indeed, suppose $r\gamma$ is represented by a descended monomial for some $r>0$.
On every normalized star, saturation gives a monomial representative of $\gamma$.
On a paired face the two representatives have equal $r$th powers, but this leaves a
$\mu_r$-ambiguity; over a nonreduced base the corresponding root comparisons must
be treated as isomorphisms of lines with section, not cancelled as scalar ratios.
The existence of the paired-frame lattice does not select that isomorphism. Under
FRCD, the declared rigidification supplies compatible root comparisons on both
conductor arrows and their triple overlaps, so the representatives descend and the
candidate equalizer is saturated. Without FRCD, no such conductor-saturation claim
is made.

### 11.4 Comparison with the complete Mumford family

Complete (11.1) at the prime $\mathfrak p_z$ of a geometric boundary point. The result is
$\widehat{(S[P_\sigma])_{\mathfrak p_z}}$; there is no second set of smooth unit-period
parameters. Completion of the finitely generated star algebras gives exactly (6.3),
and the finite list of face-localization and period gluing maps commutes with
completion. On a completed boundary stratum its finite conductor equalizer also
commutes with completion because completion is exact on finite modules over a
noetherian ring. Hence

$$
\widehat{P_\sigma^{\mathrm{alg}}}_z
\simeq
P^{\mathrm M}_{\widehat{(S[P_\sigma])_{\mathfrak p_z}}}.
\tag{11.5}
$$

Equation (11.5) unconditionally identifies this completion with the complete,
already charted Mumford functor. Conditional Proposition 8.1 identifies it with the
full ambient structured deformation functor only under Raw-DF-IIT. The following
promotion to an algebraic atlas is therefore conditional.

Let $\mathscr D_{\mathrm M}$ be the groupoid of projective supplied-DF Mumford
families carrying all the graphs in Section 10.3. Proposition 10.1 presents its
explicit diagrams by the finite-type Hilbert and Isom schemes
$\mathcal B_{\mathrm M}$; hence the classifying morphism

$$
u_\sigma:U_\sigma\longrightarrow\mathscr D
\tag{11.6}
$$

is locally of finite presentation on that charted groupoid. It is representable there:
the identity, polarization, theta rigidification, and full neat level remove the
explicit Mumford automorphisms. Assuming Raw-DF-IIT, Conditional Theorem 7.2 gives
more than equality of tangent spaces for the unframed groupoid; FRCD adds the exact
rooted conductor comparisons in the framed groupoid. For every square-zero extension $A'\to A$, a
commutative lifting problem for (11.6) has one and only one solution, because the
DF functor gives the unique lifted map $P_\sigma\to\operatorname{Div}(A')$. Thus,
conditionally, (11.6) is
formally etale. A representable locally finitely presented formally etale morphism is
etale: on affine presentations, the lifting property kills the relative differentials
and gives flatness by applying it successively to quotients by finitely generated
ideals; finite presentation then turns infinitesimal flatness into flatness.

It remains to check exhaustivity, not merely infinitesimal agreement at points already
in the image. Let $P_0$ be any geometric boundary object. GCC supplies
its torus rank, paired frame, cell incidence, and conductor pairing, giving one of
the finitely many labels of Chapters 3, 4, and 10. The special monomial coefficients select a face point
$z\in U_\sigma$ with exactly that labelled fiber. Raw-DF-IIT and Conditional Theorem
7.2 identify the entire unframed structured object, including all graphs, with this
fiber; FRCD gives the exact framed conductor-root enhancement.
Hence, conditionally, every geometric boundary point lies in the image of some
$u_\sigma$. Because an etale image is open, the finite disjoint union of these maps
then covers an open neighborhood of the entire boundary.

On the locus where the positive monomials are invertible, Chapter 6 gives an abelian
scheme with the original $\mathcal O_F$-action, polarization, and level structure.
The fine moduli property of the interior scheme $H$ therefore gives an algebraic
classifying map

$$
U_\sigma[P_\sigma^{-1}]\longrightarrow H.
\tag{11.7}
$$

It agrees on faces because the period algebras do. Adding $H$ itself to the cusp
charts gives an etale cover of the whole degeneration groupoid.

**Proposition 11.1 (explicit algebraic Mumford charts).** The algebras
$S[P_\sigma]$, their normalized-star and conductor presentations, and every explicit
graph of Section 10.3 give finite-presentation algebraic cusp families. Their base
and normalized-star log charts are fs and saturated, their completions represent the
supplied-DF Mumford deformation functors, and their punctured opens map algebraically
to $H$.

**Conditional Theorem 11.2 (algebraic etale cusp charts, AEC).** For $d\ge2$,
assuming GCC and Raw-DF-IIT, the unframed classifying maps of Proposition 11.1 are representable
etale and jointly cover every labelled ambient boundary degeneration; with $H$ they
cover the unframed degeneration groupoid. Assuming FRCD as well gives the framed
version with exact conductor roots. Thus AEC is not an input to IIT and is not
proved unconditionally: GCC first places every geometric object in the Mumford list,
Raw-DF-IIT recognizes its deformations, and FRCD separately supplies coherent
framed conductor roots.

### 11.5 Why Fitting ideals do not suffice

The zeroth Fitting ideal of $\nu_*\mathcal O_{P^\nu}/\mathcal O_P$ locates the conductor support, and higher Fitting ideals stratify its rank. They do not determine the monoid law, its saturation, the paired-face maps, or the period units. For example, $k[t^2,t^3]$ and a reduced node both have singularity supported at one point, while their characteristic monoids and normalizations are different.

Our construction uses Fitting ideals only after the monomial atlas exists, to
express bounded locally closed conditions inside Hilbert and graph schemes. The fs
assertion for the base and normalized stars comes from (11.3) and (11.4); its
extension across the conductor uses FRCD. The nonnormal gluing comes from the
explicit conductor maps. There is therefore no circular passage from an unknown
compactification to its singularity strata and back to the charts meant to construct
it.

## 12. Conditional ramified conductor compatibility

### 12.1 The tensor square of a ramified trait

Let $V\to V'$ be a finite faithfully flat extension used to split a cusp and choose
paired frames. Put

$$
W=V'\otimes_VV',\qquad W_0=W_{\mathrm{red}},\qquad
\widetilde W=\operatorname{Nor}(W_0).
\tag{12.1}
$$

If the generic extension is Galois, $\widetilde W$ is the product of the normalized
generic graph closures, although their closed points can meet. With conductor
$\mathfrak d=\operatorname{Ann}_{W_0}(\widetilde W/W_0)$ one has

$$
W_0=\widetilde W\times_{\widetilde W/\mathfrak d}W_0/\mathfrak d.
\tag{12.2}
$$

For $V'=V[s]/(s^e-\pi)$ the generic graphs $s_2=\zeta s_1$ meet at
$s_1=s_2=0$; in more general tensor squares nilpotents can occur. Hence generic deck
maps alone do not give compatible arrows on every affine star, conductor branch, or
nilpotent thickening.

### 12.2 Why framed-first descent is circular

The rejected argument first built a framed compactification, formed a structured
Isom scheme over $W$, and invoked IIT on completed local rings to manufacture a
section through meeting branches and nilpotents. That IIT invocation was then used
inside AEC and the overlap construction needed to produce the compactification to
which the descent was supposed to apply. Moreover, full faithfulness gives uniqueness
of a descent arrow, not its existence, and the invalid $A/A^\times$ argument supplied
neither the conductor arrow nor the nilpotent lift.

One may still form

$$
\mathcal I=
\operatorname{Isom}^{\mathrm{str}}_W(p_1^*P,p_2^*P),
\tag{12.3}
$$

retaining every group, action, PEL, theta, affine-star, and conductor graph. BCP
places the explicit Mumford locus in a finite-type Hilbert/Isom parameter space.
But asserting that the generic section of $\mathcal I$ extends everywhere is exactly
the Raw-DF-IIT- and FRCD-dependent existence statement; the Isom scheme proves
neither intrinsic recognition nor coherent conductor roots.

### 12.3 The unframed-first normalization route

The valid order is the reverse. First construct the unframed toroidal
compactification $X$ using the unframed cusp charts and overlaps. This construction
is conditional on GCC and Raw-DF-IIT through unframed AEC, but it does not use
paired-frame fppf descent.
Let $Y\to X^\circ$ be the finite generic paired-frame cover of its dense interior and
define

$$
X^{\mathrm{fr}}=\operatorname{Nor}_Y(X),
\tag{12.4}
$$

the normalization of $X$ in the finite generic algebra of $Y$. Excellence makes
(12.4) finite. On each toroidal chart, the valuation calculation of Chapter 9
identifies it with $S'[P_\sigma^{\mathrm{fr}}]$ before completion, and hence with
$S'[[P_\sigma^{\mathrm{fr}}]]$ after completion.

Every generic deck transformation of $Y$ extends uniquely to $X^{\mathrm{fr}}$ by
the universal property of normalization. On affine opens it preserves the integral
closure, and the deck group law holds because the two composites agree on the dense
generic cover. Thus extension of deck actions requires no infinitesimal recognition
argument and no descent through the ramified tensor square.

### 12.4 Conditional conductor and nilpotent compatibility

Normalization does not finish the structured problem. It does not by itself say that
an extended deck action preserves the chosen affine-star labels, restricts to the two
specified conductor arrows on every nonnormal boundary stratum, or commutes with a
square-zero change of the unframed base. These are not consequences of equality on a
dense generic open when nilpotents are present.

Assuming Raw-DF-IIT and FRCD, the face, conductor, square-zero, and cusp-change clauses recover
the DF functor on both pullbacks to (12.1) and identify them with the restriction of
the normalized action. They produce compatible star and conductor arrows and make
the two cocycle composites equal. In that conditional setting, the generic section
of (12.3) extends to every completed local ring. The closure argument for a finite
structured Isom scheme may then algebraize the already established completed
sections, but it is a consequence of Raw-DF-IIT and FRCD rather than a proof of
either.

Under KFF, finite faithfully flat descent of a line and its graphs is standard once
this actual descent datum exists. Finiteness of normalization alone does not permit
that invocation. Even under KFF, descent cannot create the missing star, conductor,
root, or nilpotent arrows. The same distinction applies to the theta and cubical
structures.

### 12.5 Conditional RCD

**Conditional Theorem 12.1 (ramified conductor compatibility, RCD).** For $d\ge2$,
assume GCC, Raw-DF-IIT, FRCD, and KFF, and first construct the unframed toroidal space. Its
normalization in the finite generic paired-frame cover is finite locally free, has
the monoid charts of Chapter 9, and carries the uniquely extended deck action.
Raw-DF-IIT and FRCD make that action compatible
with all affine stars, face maps, boundary normalizations, both conductor arrows,
square-zero base changes, cusp changes, and the group, action, $\mathcal O_F$,
polarization, level, theta, and cubical graphs. The resulting structured descent data
satisfy the cocycle.

Once a suitable unframed excellent compactification is supplied, its finite
normalization and the extended deck action require none of the four hypotheses.
Flatness still requires KFF, however, and exact conductor-root compatibility and
nilpotent descent remain unproved without FRCD and Raw-DF-IIT. This manuscript's
higher-rank construction of the unframed space is itself conditional on GCC and
Raw-DF-IIT (and uses FRCD for the framed conductor form of AEC). RCD is therefore
conditional, and it is not used to construct the unframed compactification on which
the normalization route begins.

## 13. Conditional algebraic overlaps and the proper toroidal space

Throughout this higher-rank chapter assume $d\ge2$, GCC, and Raw-DF-IIT, and hence the unframed form of
Conditional Theorem 11.2. The
space constructed here is unframed. Only after it exists do we apply the normalization
route of Chapter 12 to a finite generic paired-frame cover.

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

### 13.2 Conditional exhaustion by the structured Isom scheme

We prove that the preceding arrows are all the overlap arrows. Suppose geometric points in two cusp charts give isomorphic logarithmic semiabelic PEL objects. The identity component of the smooth locus recovers the semiabelian scheme. Its maximal torus recovers $X$, the quotient recovers the abelian part, and the group of periods recovers $Y$. The polarization recovers the pairing, while the level orbit recovers the cusp label modulo its declared arithmetic stabilizer.

Conditional Theorem 7.2 recovers the intrinsic base DF structure and hence the face
of the monodromy cone: precisely those $p$ mapping to units form the orthogonal face.
The normalized-star incidence complex recovers the periodic decomposition restricted
to that face. Therefore, under the standing GCC and Raw-DF-IIT hypotheses, the two
points are related by a cusp-label
isomorphism and lie in the associated common-face overlap.

Let $R^{\mathrm{exp}}_{ij}$ be the finite union of these common-face and
cusp-change charts for $U_i$ and $U_j$. Finiteness of the union follows from local
finiteness of the fan and the use of finite fundamental cell sets; an arithmetic
translate meeting two fixed representatives belongs to one of finitely many bounded
sets. There is a natural map

$$
R^{\mathrm{exp}}_{ij}\longrightarrow
\operatorname{Isom}^{\mathrm{str}}_{U_i\times U_j}(P_i,P_j).
\tag{13.2}
$$

The target is separated and locally of finite presentation over $U_i\times U_j$.
It is unramified because neat level kills fiber automorphisms and Conditional Theorem 7.2 kills
infinitesimal automorphisms. It need not be proper over the whole product: a generic
isomorphism extends over a valuation ring exactly when its valuation vector lies in a
common fan face. This is why the explicit common-face locus, rather than a false
global finiteness claim, is essential.

The map (13.2) is an isomorphism. It is bijective on geometric points by the
recovery of $X,Y$, the cusp label, and the face just proved. More importantly, it is
an isomorphism on every completed local functor: Conditional Theorem 7.2 extracts the DF functor
and all structure graphs from an arbitrary nilpotent isomorphism, so that isomorphism
is the unique declared common-face change. Since (13.2) is locally of finite
presentation, this completed lifting property makes it etale: it is formally etale,
and the affine infinitesimal criterion gives flatness and vanishing relative
differentials. It is radicial by uniqueness. An etale radicial morphism is an open
immersion, as follows by applying the diagonal criterion on an etale affine chart.
Its image contains every geometric point of the target, so that open immersion is
surjective and hence an isomorphism. This proves (13.2), including nilpotent overlap
arrows.

For an interior chart and a cusp chart, the same Isom scheme is supported precisely
where all positive monomials are invertible. There it is the graph of the algebraic
map (11.7), by the fine moduli property of $H$; a boundary fiber cannot be isomorphic
to an abelian scheme because its smooth group has positive torus rank. Thus these are
also exhaustive algebraic overlaps. Composition is literal composition of label
changes and localization, so the relation satisfies the cocycle on triple products.

### 13.3 Conditional effective separated gluing

Let $U$ be the disjoint union of $H$ and the finite cusp charts. The exhaustive
relation $R\rightrightarrows U$ just constructed is etale: on cusp pieces it is face
localization followed by a lattice isomorphism, and on interior pieces it is the
etale classifying map of Conditional Theorem 11.2. It is an equivalence relation by the
structured Isom interpretation. Gluing the affine etale sheaves gives a finite-type
algebraic space

$$
X_\Sigma=U/R.
\tag{13.3}
$$

To see effectivity directly, for an etale $T\to U$ take invariant affine opens after
shrinking $T$ so that the finitely many arrows meeting it are affine; equalize their
coordinate rings. These equalizers glue because the relation cocycle is exact. This
constructs the etale sheaf quotient and its diagonal without presupposing a global
compactification.

The diagonal is proper. Given two extensions over a valuation ring with isomorphic
generic fibers, their one-motives have the same valuation vector. There is a smallest
fan face containing it, and the common-face weight formula gives a unique isomorphism
over the valuation ring. Conditional Theorem 7.2 gives the same conclusion after completion when
the closed fiber or base is nonreduced. Hence the diagonal satisfies valuative
existence and uniqueness; being already finite type and separated, it is proper.
Neatness makes it a monomorphism, so $X_\Sigma$ has no residual inertia.

### 13.4 Conditional properness from complete fans

Take a map from the fraction field $K$ of a valuation ring $V$ to the interior moduli space. After a finite faithfully flat extension $V'/V$, semi-stable reduction of the polarized abelian variety supplies a Raynaud extension and a polarized one-motive. The valuation pairing is a point of the closed positive cone. Completeness of the fan places it in some cone $\sigma$; if it lies on a wall, either adjacent chart gives the same point on their face overlap.

The unframed Raynaud datum and its valuation pairing descend independently of any
choice of paired frame. Raw-DF-IIT, through its base-change and cusp-change clauses,
identifies the corresponding unframed Mumford extensions after a splitting cover and
gives their descent cocycle. This constructs the extension over $V$ without invoking
RCD or a framed compactification. The common-face calculation makes it independent of
the cone chosen on a wall, and the trait argument of Section 13.3 gives uniqueness.
Thus, conditionally, $X_\Sigma$ satisfies the valuative criterion for properness.

For completeness, the usual reduction from arbitrary valuation rings to traits does
not hide an existence assertion here. All data are of finite presentation, so they
descend to a finitely generated subring of the valuation ring. A chain of prime
specializations can be treated one height at a time; the fan vector and the finite
explicit Mumford graph data stabilize because only finitely many cones and Hilbert polynomials occur
near the chosen point. The trait construction then extends along the chain, and
uniqueness glues the extensions. Hence $X_\Sigma$ is a proper finite-type algebraic
space containing $H$ as a dense open subspace.

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

On a Raynaud extension, evaluation of the biextension along $Y\times X$ is the full
logarithmic Fourier character $q^{B(y,x)}$; a chosen splitting writes its leading unit
separately but does not create another parameter. Together with the quadratic factor
$q^{A(y)}$ it gives precisely (6.5). Thus the Poincare construction and the polyhedral
construction yield the same line $\Theta$ on the normalized stars. For an explicit
unframed Mumford presentation, formula (6.5) supplies actual conductor comparison
isomorphisms and their cocycle. After a frame lattice introduces roots, the exact
rooted comparisons and their coherence are supplied only under FRCD.

Normalization together with identity rigidification does **not** determine a line
bundle on a nonnormal fiber. On a split geometric fiber, if $\Gamma$ is the
conductor incidence graph, fixing the line on the normalization still leaves the
edge-gluing quotient

$$
(\mathbf G_m)^{E(\Gamma)}/
\operatorname{im}\bigl((\mathbf G_m)^{V(\Gamma)}\bigr)
\simeq(\mathbf G_m)^{b_1(\Gamma)}.
\tag{14.1b}
$$

Identity rigidification removes the base-pullback ambiguity and at most fixes a
vertex gauge; it does not kill the holonomy around a conductor cycle. In particular,
a nodal cycle retains a $\mathbf G_m$ gluing parameter. Book 16, Section 8.1, and
Book 25, Section 12.1 are the elementary counterboundary.

The exact statement used here is conditional. Once the **actual conductor descent
datum** for $\Theta$ is supplied, including its cocycle and cubical PEL
compatibilities, effective descent through the conductor pushout determines the
descended line uniquely relative to that datum. Compatibility with base change,
face restriction, coefficient descent, and framed roots holds only when the supplied
data have those compatibilities; in the global argument these are part of FRCD and
RCD. An alternative would be a separately proved theorem that the full cubical PEL
data annihilate the graph-torus parameter. No such theorem is proved or assumed in
this manuscript, so normalization plus identity rigidification is never used as a
substitute for conductor descent data.

### 14.3 Determinant of cohomology

For $m$ divisible by the integer $m_0$ of Section 10.2, $\Theta^m$ has no higher cohomology on every normalized toric star and on every conductor face. This follows from the lattice-point resolution associated with a regular triangulation. Weight by weight, the Cech complex is the augmented cellular cochain complex of the subcomplex of cells containing a fixed lattice point. That subcomplex is a convex star and is contractible. Hence the complex is exact in positive degree. Apply (6.7), or the full face resolution when more than two stars meet, to obtain the same vanishing on the nonnormal semiabelic boundary fiber.

For completeness, the abelian fibers have the same vanishing. Choose an integer
$n$ invertible on the fiber. For a symmetric theta line,
$[n]^*\Theta^m\simeq\Theta^{mn^2}$. The trace divided by $n^{2d}$ splits
$\mathcal O_A\to[n]_*\mathcal O_A$, so projection formula injects

$$
H^i(A,\Theta^m)\hookrightarrow H^i(A,\Theta^{mn^2}).
$$

The group on the right is zero for $n$ large by the elementary Serre-vanishing
argument from a projective embedding. Hence the group on the left is zero for
$i>0$. The Hilbert polynomial is fixed in the flat total family, so the rank of
$H^0$ is constant on the abelian and boundary fibers. The fiberwise vanishing and
the finite free resolution of the theta algebra then show directly that
$f_*\Theta^m$ is locally free and commutes with base change.

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

Only theta-preserving automorphisms act on the fixed perfect complex
$Rf_*\Theta^m$: an automorphism $g$ must be equipped with a compatible
linearization $g^*\Theta^m\simeq\Theta^m$. This includes the paired-frame deck
symmetries when their theta linearizations and conductor compatibilities have been
supplied. An arbitrary PEL endomorphism $\iota(a)$ has no such action. Pullback gives
instead

$$
Rf_*\Theta^m\longrightarrow Rf_*\iota(a)^*\Theta^m,
\tag{14.3a}
$$

and the line on the right generally represents the $a^2$-twisted polarization rather
than a fixed tensor power of $\Theta$. For the scalar endomorphism $[n]$, the cubical
identity gives the correctly powered target
$[n]^*\Theta^m\simeq\Theta^{mn^2}$, as above. Thus only the theta-preserving
automorphism group yields a character on $\mathcal D_m$; no action of all of
$\mathcal O_F$ on one fixed determinant line is asserted.

### 14.4 Boundary transition characters

On a cusp chart, choose the theta-weight basis $\{\vartheta_x\}$ in a fundamental polytope. On an overlap induced by a period $y$, (6.5) gives

$$
\vartheta_x\longmapsto
q^{B(y,x)+mA(y)}
\vartheta_{x+m\lambda(y)}.
\tag{14.4}
$$

Taking the determinant over all representatives gives a unit times a monomial
$q^{\kappa_m(y)}$. Here $\kappa_m(y)$ is typed in
$P_\sigma^{\mathrm{gp}}\subset M$; it is not generally quadratic in $m$. On a
conductor face, weights outside that face vanish and the alternating determinant
formula (14.3) cancels the missing weights. Hence the restriction of $\kappa_m$ is
exactly the determinant exponent for the face.

If $S_m$ is the finite set of degree-$m$ weight representatives, the exponent is explicitly

$$
\kappa_m(y)
=\sum_{x\in S_m}
\bigl(B(y,x)+mA(y)\bigr).
\tag{14.4a}
$$

Let $\Delta\subset X_\mathbf R$ be the rational $d$-dimensional fundamental
polytope used for the theta weights, with a fixed half-open boundary convention and
lattice-normalized measure $du$. Thus $S_m$ is represented by $m\Delta\cap X$ for
the admissible values of $m$. Vector-valued weighted Ehrhart summation gives, on
every admissible congruence class of $m$,

$$
\kappa_m(y)
=m^{d+1}\int_\Delta\bigl(B(y,u)+A(y)\bigr)\,du+O(m^d)
\quad\text{in }M_\mathbf R.
\tag{14.4b}
$$

Accordingly $\kappa_m(y)$ is generally a degree-$d+1$ weighted Ehrhart
quasipolynomial, and a polynomial when the chosen polytope is integral; lower-degree
collapse can occur only if the displayed moments cancel. The positivity needed here
is only the positivity of its leading scalar order in an interior monodromy
direction. Indeed, for $\nu\in\sigma^\circ$ put
$b_\nu=\langle\nu,B\rangle$ and $a_\nu=\langle\nu,A\rangle$. Center $\Delta$
and absorb the translation-induced linear character into the local trivialization.
Then its first moment vanishes, and symmetry of the cubical theta datum gives
$2a_\nu(y)=b_\nu(y,\lambda(y))$. Hence, for $y\ne0$,

$$
\left\langle\nu,
\int_\Delta\bigl(B(y,u)+A(y)\bigr)\,du\right\rangle
=\frac{\operatorname{vol}(\Delta)}2\,
b_\nu(y,\lambda(y))>0
\tag{14.4c}
$$

by the polarization positivity in (5.10). Thus, for every nonzero period translate,
large admissible $m$ has positive scalar boundary order along every interior
monodromy valuation. No coefficientwise positivity in $M$ is asserted. For a
concrete $d=2$ check, take
$X=\mathbf Z^2$, a centered square, and odd $m$ with
$S_m=\{-(m-1)/2,\ldots,(m-1)/2\}^2$. Then
$\sum_{x\in S_m}x=0$, $|S_m|=m^2$, and
$\kappa_m(y)=m^3A(y)$: the leading behavior is cubic, not quadratic.

Changing the fundamental polytope permutes $S_m$ and adds a global linear character, which changes the local trivialization but not the line. On a fan wall the two sums restrict to the sum for the common face by the alternating cancellation just described. This proves, rather than presumes, that the exponents form a piecewise linear support datum.

On common faces these exponents give an integral piecewise-linear function $\chi_m$.
The Cartier construction (15.3) therefore gives a line $\mathcal B_{-\chi_m}$.
Twisting $\mathcal D_m$ by it removes the displayed boundary monomials. On a change
of cusp, (13.1) carries both $\kappa_m$ and the fan character to their counterparts,
so the corrected transition is a unit. On the punctured chart the fan character is
invertible and the corrected line is the determinant line of the abelian theta
family. Consequently the corrected lines agree across every overlap of Chapter 13.

Only the exact, correctly typed sum (14.4a) is used for this determinant correction.
Neither (14.4b) nor its positive leading coefficient is used to infer ampleness;
conditional ampleness comes separately from the proper quasi-finite structured-graph
morphism of Section 15.3 after TDC-Ext is supplied.

### 14.5 Base change and conductor compatibility

The determinant of a perfect complex commutes with arbitrary base change. In our
range this is also visible from the locally free module $f_*\Theta^m$. After
restriction to a fixed boundary stratum, the fiberwise conductor square (6.7) gives
the exact-triangle identity

$$
\det Rf_*\Theta^m
\simeq
\det Rf_*^\nu\nu^*\Theta^m
\otimes\det Rf_{C*}\Theta_C^m
\otimes(\det Rf_{C^\nu*}\Theta_{C^\nu}^m)^{-1}.
\tag{14.5}
$$

Every isomorphism in (14.5) is functorial on explicit Mumford charts. For $d\ge2$,
under GCC, Raw-DF-IIT, FRCD, and KFF, it also respects the ramified conductor compatibility of
Conditional Theorem 12.1. The corrected determinant line

$$
\mathcal H_m=\mathcal D_m\otimes\mathcal B_{-\chi_m}
\tag{14.6}
$$

has unit boundary trivializations. Conditionally, effective descent for invertible
modules and the exhaustive relation of Chapter 13 produce a global invertible sheaf
$\mathcal H_m$ on $X_\Sigma$. Its restriction to $H$ is $\det f_*\Theta^m$, and
formation of $\mathcal H_m$ commutes with coefficient base change. Unconditionally,
the same statement holds chart by chart for the explicit Mumford construction.

## 15. Conditional projectivity via structured graphs

Throughout this higher-rank chapter assume $d\ge2$, GCC, Raw-DF-IIT, FRCD, and KFF,
and hence the conditional proper space $X_\Sigma$ of Chapter 13 and the framed
descent of Chapter 12. The determinant and Cartier calculations on each explicit
Mumford chart are unconditional. They do not, even after conditional global gluing,
control every Plucker coordinate of the structured parameter map. Projectivity will
therefore use the separate TDC-Ext hypothesis below.

### 15.1 The interior structured map and TDC-Ext

Choose an auxiliary theta level $m$ invertible on $S_0$ and divisible by the integer
of Section 10.2. A symmetric theta structure identifies the finite Heisenberg group
of $\Theta^m$ with the standard one and gives its canonical weight basis up to one
common scalar. Its functor is finite etale on the interior and finite Kummer on the
boundary, exactly as in Chapter 9. Under KFF, Conditional Theorem 12.1 gives a
finite faithfully flat theta-framed cover

$$
\pi:X_\Sigma^\theta\longrightarrow X_\Sigma.
\tag{15.1a}
$$

Its flatness is precisely the KFF input. Regularity of the source and target charts
separately does not produce a basis of the larger monoid algebra over the smaller
one; that would require the simultaneous lattice argument explicitly left open in
Hypothesis 9.2. This is not the infinite $\operatorname{GL}$-torsor of arbitrary
vector-space frames.

In the canonical theta basis, the evaluation quotients and the group, action,
$\mathcal O_F$, polarization, level, cubical theta, normalized-star, and both
conductor graphs define a locally closed subscheme of a fixed product of
Grassmannians and Hilbert schemes. The normalization and conductor data are retained
as structured graph factors, not inferred from the underlying Hilbert point. Let $Q^\theta$ be
the projective closure of the theta-framed interior image in that product. This
constructs $Q^\theta$ before using the toroidal space.

Thus the theta-framed interior has a structured morphism

$$
h_H^\theta:H^\theta\longrightarrow Q^\theta.
\tag{15.1b}
$$

Formula (14.4a) computes the transition of the single determinant
$\det f_*\Theta^m$. A Plucker coordinate of an evaluation, multiplication, action,
or conductor graph is a maximal minor of a different matrix. Its valuation is not
the sum (14.4a) in general. Consequently (14.4a) proves neither regularity and
non-simultaneous vanishing of all boundary Plucker coordinates nor their exact
determinant-line identity. The following is a separate antecedent.

**Hypothesis 15.1 (structured Hilbert extension, TDC-Ext).** For the conditional
proper space $X_\Sigma$, its theta-framed cover, and the structured parameter space
$Q^\theta$ just constructed, the following three assertions hold compatibly with
coefficient base change, face restriction, cusp change, conductor descent, and the
finite theta-deck action.

1. The interior morphism $h_H^\theta$ extends to a morphism
   $$
   h^\theta:X_\Sigma^\theta\longrightarrow Q^\theta.
   \tag{15.1}
   $$
   Equivalently on each explicit cusp chart, all structured Plucker rational
   coordinates extend after their actual boundary corrections, have no common zero,
   satisfy the graph equations, and agree on every declared overlap.
2. The morphism $h^\theta$ is quasi-finite; equivalently, each of its geometric
   fibers is finite.
3. For a fixed ample tensor product $\mathcal O_{Q^\theta}(1)$ of the Plucker
   factors there are admissible theta powers $m_j$ and positive integers $a_j$ with
   a canonical isomorphism

   $$
   (h^\theta)^*\mathcal O_{Q^\theta}(1)
   \simeq\bigotimes_j\mathcal H_{m_j}^{\otimes a_j}=:\mathcal H^\theta,
   \qquad a_j>0,
   \tag{15.2}
   $$

   whose restriction to the interior is the universal Plucker determinant identity
   and whose boundary trivializations agree on faces, conductors, and cusp changes.

TDC-Ext is exact: it assumes extension, quasi-finiteness, and the line isomorphism,
not merely equality of numerical classes. The general Hilbert/Grassmannian
construction proves representability and boundedness of the listed graph data, but
does not prove these three assertions. A repository-wide alias check finds only such
general parameter-space results and downstream statements that retain TDC or
TDC-Ext as required; no theorem proves these three assertions under another name.

### 15.2 Cartier fan data

Let $\psi$ be the invariant integral strictly convex support function produced in
Chapter 4. For every cone $\sigma$, write $m_\sigma\in M$ for its linear part. On
$U_\sigma$ take a generator $s_\sigma$ and on an overlap put

$$
s_\sigma=q^{m_\sigma-m_\tau}s_\tau.
\tag{15.3}
$$

The exponent annihilates $\sigma\cap\tau$, so it is a unit on the overlap; the
differences telescope on triples. These are actual Cartier transition functions and
give

$$
D_\psi=-\sum_{\rho\in\Sigma(1)}\psi(v_\rho)D_\rho,
\qquad \mathcal B_\psi=\mathcal O(D_\psi).
\tag{15.4}
$$

Equivariance makes this line compatible with explicit cusp changes; conditionally,
Chapter 13 glues it globally and Conditional Theorem 12.1 gives its paired-frame
compatibility. It is trivialized on the interior.

Strict convexity computes positive degree on each elementary invariant wall curve of
an explicit toric normal slice. We record that local calculation but make no
finite-generation or generation assertion for an effective cone, local or global,
and do not use such an assertion for projectivity.

### 15.3 The conditional proper quasi-finite structured graph route

Assume TDC-Ext. The morphism $h^\theta$ is proper because
$X_\Sigma^\theta$ is proper and $Q^\theta$ is separated over $S_0$: its graph is
closed in $X_\Sigma^\theta\times_{S_0}Q^\theta$, and projection to $Q^\theta$ is
proper. Its quasi-finiteness is clause 2 of TDC-Ext, not a consequence merely of
Raw-DF-IIT, overlap exhaustion, or neatness. Those inputs identify the structured
moduli data already retained by a chart, but they do not show that the chosen finite
list of Plucker graph coordinates separates every boundary point.

A proper quasi-finite morphism is finite. It follows that
$\mathcal H^\theta=(h^\theta)^*\mathcal O_{Q^\theta}(1)$ is ample. Choose the theta
structure so that its generic deck cover is Galois with finite group $\Delta$.
Chapter 9 takes its finite normalization, and Conditional Theorem 12.1 supplies the
structured boundary action. The tensor product

$$
\bigotimes_{g\in\Delta}g^*\mathcal H^\theta
\tag{15.5}
$$

has the permutation linearization and descends to a line $\mathcal H$ on
$X_\Sigma$. Its pullback is ample. Under KFF, ampleness descends through the finite
faithfully flat cover: descend a sufficiently high evaluation quotient giving the framed closed
immersion. Hence $\mathcal H$ is ample on the proper algebraic space $X_\Sigma$.
An algebraic space with an ample invertible sheaf is a scheme: sufficiently high
sections have affine nonvanishing loci, and these loci cover. Thus $X_\Sigma$ is
already a projective scheme at this point.

This is the conditional positivity route once TDC-Ext is supplied: the proper quasi-finite
structured Hilbert/graph map supplies a globally ample line directly. No
finite-generation, effective-cone, or domination assertion is used.

### 15.4 Conditional TDC

**Conditional Theorem 15.2 (theta-determinant compatibility, TDC).** For $d\ge2$,
assuming GCC, Raw-DF-IIT, FRCD, KFF, and TDC-Ext, the structured Hilbert/graph map
(15.1) is proper and quasi-finite,
hence finite. Its Plucker line is ample on the theta-framed normalization, and the
tensor of its deck translates descends to an ample line on the unframed toroidal
space. Consequently that proper algebraic space is a projective scheme. The
determinant and Cartier fan lines retain the base-change and conductor compatibilities
proved in Chapter 14 and Section 15.2.

Without these hypotheses, the local determinant formulas, Cartier transitions, and
structured projective parameter space remain available, but GCC and Raw-DF-IIT are
needed for exhaustive global points and overlaps, FRCD for exact conductor-root
compatibility, and KFF for the fppf descent step. Even under those four hypotheses,
TDC-Ext is still needed for extension and quasi-finiteness of the structured map and
for the exact identity (15.2). TDC is therefore not proved.

## 16. The conditional toroidal compactification and gluing theorem

### 16.1 Construction and completed-local comparison

Sections 16.1--16.3 first treat the higher-rank branch $d\ge2$. The rank-one branch
is stated separately in Theorem 16.1 and is not obtained by applying Raw-DF-IIT.

Let $\mathcal M$ be the Hilbert--Blumenthal moduli scheme for the standing PEL datum and
neat level, and let $\Sigma$ be the equivariant regular projective fan collection of
Theorem 4.2. For $d\ge2$, assume GCC, Raw-DF-IIT, FRCD, KFF, and TDC-Ext. Conditional
Theorem 11.2 and Chapter 13 construct
and glue the exhaustive unframed algebraic cusp charts; Conditional Theorem 15.2
proves projectivity. Only then is a paired-frame compactification formed by
normalization in its finite generic cover, as in Chapter 12. Write

$$
\mathcal M\hookrightarrow\mathcal M_\Sigma^{\mathrm{tor}}.
\tag{16.1}
$$

for the resulting scheme. At a framed geometric point $z$ of the stratum indexed by
$\sigma$, its completed local ring is

$$
\widehat{\mathcal O}_{\mathcal M_\Sigma^{\mathrm{tor}},z}
\simeq
\widehat{\bigl(S_0[P_\sigma^{\mathrm{fr}}]\bigr)_{\mathfrak p_z}},
\tag{16.2}
$$

with no extra smooth unit-period factor. Before framing, the finite stabilizer invariants are
taken; at neat nonzero cones that stabilizer is trivial. The completed universal family is
the Mumford family by Conditional Theorem 7.2 and Proposition 11.1. If the face
$\tau$ has dimension $r$, (16.2) has $r$ boundary parameters and $d-r$ invertible
period parameters.

### 16.2 Smoothness, boundary, and universal objects

The monoid of a regular cone is free after removing its unit face. Thus (16.2) is a
relative formal power-series ring of total relative dimension $d$, with a
normal-crossings boundary. The etale charts of Conditional Theorem 11.2 therefore prove
smoothness and identify the boundary strata.

Descent of the chart families supplies the universal object

$$
f_\Sigma:P_\Sigma\longrightarrow\mathcal M_\Sigma^{\mathrm{tor}}
\tag{16.3}
$$

equipped with its semiabelian action, $\mathcal O_F$-action, polarization, level orbit,
intrinsic fs logarithmic structure, relatively ample normalized theta line, and all graphs
and conductor data of Section 10.3. Its boundary fibers may be nonnormal; their normalized-star
covers and original conductor pushouts are part of the datum.

### 16.3 Projectivity and descent

Conditional properness is Section 13.4. Under TDC-Ext, the descended structured
Plucker line of Section 15.3 makes the algebraic space a projective scheme. After the unframed scheme
exists, Chapter 12 normalizes it in the paired-frame cover; Conditional Theorem 12.1
supplies conductor and nilpotent compatibility for every universal graph.

**Theorem 16.1 (two-branch toroidal compactification and gluing, TCG).** The global
compactification statement has the following separate alternatives.

1. **Higher rank.** If $d\ge2$ and GCC, Raw-DF-IIT, FRCD, KFF, and TDC-Ext hold, then for the
   standing Hilbert--Blumenthal PEL datum, neat level, and a regular projective
   admissible fan collection there is a smooth projective toroidal compactification
   $\mathcal M_\Sigma^{\mathrm{tor}}$. Its boundary is a relative normal-crossings
   divisor with strata indexed by fan faces. Its completed rings are (16.2), of total
   relative dimension $d$, and its universal structured semiabelic family is (16.3).
   The unframed construction commutes with coefficient base change. Paired-frame
   normalization and its structured compatibility are as in Conditional Theorem
   12.1.
2. **Rank one.** If $d=1$, the global compactification is the compactified fine
   modular curve in the applicable good-level case of Book 111, Theorem 13.1. This
   alternative imports only the smooth proper/projective compactification and the
   universal rank-one object in the scope stated there; it does not invoke
   Raw-DF-IIT and does not import arbitrary-$Z$ joining, avoidance, or ICS. Use of
   this compactification in Chapter 17 requires the separate supplied-model
   antecedent R1-FTJ below.

### 16.4 Independence under refinement

In the higher-rank branch, if $\Sigma'$ refines $\Sigma$, every monoid chart for $\Sigma'$ maps to the chart for
$\Sigma$ by the identity
on the common lattice. The normalized family map is the toric modification prescribed by
subdivision. Its conductor restrictions respect paired faces, so it descends to a proper
morphism

$$
\mathcal M_{\Sigma'}^{\mathrm{tor}}
\longrightarrow\mathcal M_\Sigma^{\mathrm{tor}}
\tag{16.4}
$$

which is the identity on $\mathcal M$. Chartwise this is the explicit toric
modification. Its global existence and compatibility with the universal object are
conditional on GCC, Raw-DF-IIT, and FRCD, and its framed fppf form also uses KFF;
once it exists, the relative support function supplies
its relatively ample fan line.

For two fans, take their common projective regular refinement by Chapter 4. The two compactifications are therefore canonically birational through projective toroidal modifications, and their universal semiabelic objects agree on common completed face charts. Boundary constructions that are invariant under such refinement are consequently independent of the chosen fan.

## 17. Conditional finite-type joining and the integral connecting slice

### 17.1 Joining a formal cusp to the good interior

We place the final construction in a form useful beyond one arithmetic application. Let $R$
be a complete discrete valuation ring with fraction field $K$ and residue field $k$, let
$Y/K$ be the base change of a geometrically connected component of the global finite PEL
frame cover, and let

$$
y_{\mathrm{sp}}:\operatorname{Spec}K\longrightarrow Y
\tag{17.1}
$$

be a point with split semistable reduction of a selected cusp type. Its period valuations choose a ray $\rho$ in the positive monodromy cone. Assume only that the torsion frames appearing in $Y$ are defined over the given completion field. Their division monomials then define the paired-frame lattice of (9.3); no additional root is to be adjoined.

There are two distinct ways a global model enters. If $d\ge2$, assume GCC,
Raw-DF-IIT, FRCD, KFF, and TDC-Ext. Choose the fan of Theorem 4.2 with $\rho$ marked and
apply the higher-rank alternative of Theorem 16.1 to the fine paired-frame PEL datum
defining $Y$. Base change that projective compactification to $R$. Its algebraic
branch has completion

$$
\operatorname{Spf}S'[[P_{\sigma}^{\mathrm{fr}}]],
\tag{17.2}
$$

and the valuation homomorphism of $y_{\mathrm{sp}}$ is a continuous map from this
ring to $R$. Because $\rho$ is a ray of the fan, the map meets a single boundary
divisor; its intersection multiplicity is the integral length of the valuation vector
on the primitive ray. The Kummer units, enhanced theta rigidification, polarization
sign, and exact frames are the universal ones on this branch. Take the closure of the
selected geometrically connected component in the paired-frame compactification. For a proper
smooth morphism the sheaf of geometric connected components is finite etale: locally
constant idempotents of a fiber lift uniquely through smooth infinitesimal
neighborhoods and properness extends them. Since $R$ is henselian, the chosen generic
component therefore extends to an open-and-closed component. Denote it by
$\overline{\mathcal Y}$. It is smooth and projective over $R$, contains the
good-reduction locus $\mathcal Y^{\mathrm{good}}$, and carries the restriction of
the ample structured Plucker line of Section 15.3. A power is relatively very ample. The section (17.1) extends
by properness, and its completed branch is (17.2) by (16.2).

There is no completion-field enlargement. Normalization is taken in exactly the
paired-frame function algebra specified by $Y$; Section 9.3 constructs it before
completion, and Conditional Theorem 12.1 descends it through the recorded ramified splitting
ring. Hence the completion field, valuation shell, Kummer classes, and framed
one-motive of $y_{\mathrm{sp}}$ remain unchanged.

If $d=1$, Raw-DF-IIT is unavailable and is not inserted into this argument. Book
111, Theorem 13.1 supplies the applicable global rank-one compactification, but that
theorem alone is not a joining theorem for the selected fine branch. We therefore
state the extra input actually required.

**Rank-one supplied-model FTJ antecedent (R1-FTJ).** After base change to $R$ and
passage to the selected fine component, a smooth projective finite-type model
$\overline{\mathcal Y}/R$ with geometrically connected fibers is supplied such that:

1. its generic fiber is $Y$ and it contains the good-reduction locus
   $\mathcal Y^{\mathrm{good}}$;
2. $y_{\mathrm{sp}}$ extends to an $R$-section whose completed boundary branch is
   the prescribed framed Tate--Mumford branch, without enlarging the completion
   field or changing its valuation, Kummer, theta, polarization, or frame data; and
3. a relatively very ample line and every coefficient and PEL-frame descent
   isomorphism needed below extend to the model.

R1-FTJ contains no assertion about a proper closed subset $Z$. The arbitrary-$Z$
avoidance conclusion is deduced below from this supplied model. Neither Book 111,
Theorem 13.1 nor Book 110 is cited as a proof of R1-FTJ.

### 17.2 The conditional finite-type joining theorem

Under either the higher-rank construction above or R1-FTJ, let $Z\subsetneq Y$ be
a proper closed subset. We verify the avoidance clause needed for slicing. Let
$\overline Z$ be the schematic closure of $Z$ in $\overline{\mathcal Y}$. The
special fiber of the selected component is geometrically integral because
$\overline{\mathcal Y}/R$ is smooth with geometrically connected generic fiber; the
etale scheme of connected components is constant, and a connected smooth fiber is
regular and hence its irreducible components are disjoint, so it is integral.

At the generic point $\eta_s$ of the special fiber, the local ring is a discrete valuation ring with uniformizer $\pi$. The ideal $I_Z$ of the schematic closure is $\pi$-saturated:

$$
\pi f\in I_Z\quad\Longrightarrow\quad f\in I_Z,
\tag{17.3}
$$

because $I_Z$ is the contraction of its localization after inverting $\pi$. The
total space is integral: it is regular, and its geometrically connected generic and
special fibers make its irreducible components disjoint and then unique. Hence
$I_Z$ contains a nonzero element. If $\overline Z$ contained the special-fiber
component, then $(I_Z)_{\eta_s}\subset(\pi)$. Choose a nonzero element of this ideal
of minimal $\pi$-adic order. Saturation permits division by $\pi$ and produces an
element of smaller order, a contradiction. Thus $\overline Z$ contains no
special-fiber component.

The boundary also contains no component of the good special fiber. It follows that

$$
U_k=\mathcal Y_k^{\mathrm{good}}\setminus\overline Z_k
\tag{17.4}
$$

is a nonempty dense open. It contains a closed point. Over a finite residue field that closed point need not be rational, a distinction retained below.

**Conditional Theorem 17.1 (two-branch finite-type joining, FTJ).** With the data of
Section 17.1, assume one of the following separate alternatives:

1. $d\ge2$ and GCC, Raw-DF-IIT, FRCD, KFF, and TDC-Ext hold, so the higher-rank construction
   above supplies $\overline{\mathcal Y}$; or
2. $d=1$ and R1-FTJ holds for the supplied rank-one model.

Then there is one smooth projective finite-type $R$-model
$\overline{\mathcal Y}$ satisfying all of the following.

1. It contains the good interior $\mathcal Y^{\mathrm{good}}$. In the higher-rank
   alternative a relatively very ample line is a power of the descended structured
   Plucker line; in the rank-one alternative the relatively very ample line is part
   of R1-FTJ.
2. The selected semistable point extends to an $R$-section. The completion at its boundary branch is the normalized paired-frame Mumford chart, and the section retains its completion field, valuation and Kummer shells, theta rigidification, polarization sign, and exact frames.
3. The open (17.4) is nonempty and dense for every proper closed $Z\subset Y$.
4. Every coefficient and descent isomorphism of the PEL frame cover extends to the model and the ample line.

In the higher-rank alternative the model is constructed globally by Theorem 16.1,
not from the formal branch alone, and its completed comparison is (16.2). In the
rank-one alternative the model and completed branch are precisely the R1-FTJ input.
For both alternatives, and for every $Z$, the avoidance assertion is the manuscript's
saturation argument (17.3).

### 17.3 Relative slicing with a dense good open

We recall the slicing argument in enough detail to expose its hypotheses. Let $n=d$ be the
relative dimension of $\overline{\mathcal Y}/R$ and let $\mathcal L$ be the relatively very
ample power in Conditional Theorem 17.1.

If $d=1$, Book 111, Theorem 13.1 supplied only the global compactification used as
the starting boundary object; R1-FTJ separately supplied the selected finite-type
model and branch. The saturation argument of Section 17.2 then produced the
arbitrary-$Z$ dense open $U_k$. Take no cutting sections and set
$\mathcal C=\overline{\mathcal Y}$. Thus the slicing step is empty in rank one, but
FTJ and the resulting ICS statement remain conditional on R1-FTJ; no arbitrary-$Z$
FTJ, avoidance, or ICS theorem is delegated to Books 110--111.

Assume henceforth that $d=n\ge2$ and that the residue field $k$ is finite. The
finiteness of $k$ is used only in the closed-point density estimates (17.6) and the
high-degree finite-field Bertini argument; it was not needed for FTJ or for the
rank-one empty-slice case. We seek $n-1$ sections whose common zero scheme is a
smooth proper relative curve, passes through the selected semistable section with prescribed
independent first jets, and has special fiber meeting $U_k$.

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

### 17.4 The conditional stable connecting-slice theorem

**Conditional Theorem 17.2 (stable integral connecting slice, ICS).** Under either
alternative of Conditional Theorem 17.1, and additionally assuming that $k$ is
finite in the higher-rank alternative, there is a tuple of global cutting sections
(the empty tuple when $d=1$) whose intersection is a smooth proper geometrically connected relative curve
$\mathcal C/R$ such that:

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

The construction exports the following two-branch conditional chain.

$$
\begin{gathered}
\left.\begin{gathered}
({\rm Raw\text{-}DF\text{-}IIT})\Longrightarrow({\rm IIT})_{\rm unfr}
\Longrightarrow({\rm MPE})_{\rm unfr},\\
({\rm GCC})+({\rm Raw\text{-}DF\text{-}IIT})
\Longrightarrow({\rm AEC})_{\rm unfr}
\Longrightarrow(\text{unframed proper space}),\\
(\text{unframed proper space})+({\rm Raw\text{-}DF\text{-}IIT})
+({\rm FRCD})+({\rm KFF})\Longrightarrow({\rm RCD})_{\rm fppf},\\
(\text{unframed proper space})+({\rm RCD})_{\rm fppf}+({\rm TDC\text{-}Ext})
\Longrightarrow({\rm TDC})\Longrightarrow({\rm TCG})_\Sigma
\Longrightarrow({\rm FTJ})_{v,Z}
\xrightarrow{k\ {\rm finite}}({\rm ICS})_{v,Z}.
\end{gathered}\right\}\qquad(d\ge2),\\[4pt]
\bigl(\text{Book 111, Theorem 13.1}\bigr)+({\rm R1\text{-}FTJ})
\Longrightarrow({\rm FTJ})_{v,Z}
\xrightarrow[\text{empty slice}]{\text{avoidance }(17.3)}
({\rm ICS})_{v,Z}\qquad(d=1).
\end{gathered}
\tag{17.13}
$$

BCP, Proposition 10.1, is the unconditional boundedness input for explicit Mumford
charts; it does not recognize arbitrary ambient objects. IIT is Conditional Theorem
7.2; its framed conductor-root form also uses FRCD. MPE is Conditional Proposition
8.1 with the same qualification. GCC is Hypothesis 3.1, FRCD is Hypothesis 9.1,
KFF is Hypothesis 9.2, and TDC-Ext is Hypothesis 15.1. AEC is Conditional Theorem
11.2; RCD is Conditional Theorem 12.1 after the unframed space exists; TDC is
Conditional Theorem 15.2; the
higher-rank TCG alternative is Theorem 16.1(1); and FTJ and ICS are Conditional
Theorems 17.1 and 17.2. KFF is required
wherever the finite normalization is used as an fppf cover; mere finiteness is not
enough. The higher-rank chain is not promoted to an unconditional theorem in this
manuscript. TDC-Ext is required by higher-rank TDC, TCG, FTJ, and ICS, while a finite
residue field is required only for the higher-rank FTJ-to-ICS Bertini arrow. In rank
one, Book 111, Theorem 13.1 provides the global compactification
only in its stated scope; R1-FTJ is still required for the selected joining model,
after which (17.3) proves arbitrary-$Z$ avoidance and the empty-slice argument proves
ICS. Neither of those latter assertions is imported from Books 110--111. The last
theorem deliberately asserts a nonempty good open. A rational good section requires
the additional hypothesis (17.12).

## 18. Hostile mathematical review

### 18.1 Infinitesimal and logarithmic attacks

**Attack: the Mumford cell semigroup is not closed under addition.** This attack
succeeds against the former formula. Section 6.1 now uses
$\Phi_C(n,x)=n\varphi_C(x/n)$ on the cone over $C$. Formula (6.1c) proves closure,
and (6.4) uses the corresponding homogeneous convexity defect. The rank-one node is
recomputed as the second difference of vertex values.

**Attack: the equivariant fan regularization has no decreasing invariant.** This
attack succeeds against the former common-orbit-refinement argument. Section 4.4 now
uses the regular-action barycentric refinement from Book 157, Lemma 13.2B.2. Distinct
translates of the chosen face lie in no common cone, so their coherent stellar
subdivisions commute. The determinant calculation creates no cone of the old maximal
multiplicity and removes at least one orbit of such cones; induction on maximal
multiplicity and then its finite orbit count terminates. Thus Theorem 4.2 needs no
new antecedent.

**Attack: arbitrary geometric semiabelic PEL fibers were classified without a
proof.** This attack succeeds. The orbit-weight discussion in Section 3.5 proves
recovery only on the explicit Mumford locus. GCC, Hypothesis 3.1, now states the
classification of an arbitrary geometric fiber. It precedes Raw-DF-IIT, which starts
with an already labelled Mumford fiber.

**Attack: strictness was defined into the object.** Section 5.2 gives the ambient
object no chart and imposes no monomial divisibility. Chapter 7 now records the
actual multiplication maps as a symmetric monoidal diagram in
$\operatorname{Div}(A)$. Strictness would be a conclusion of Raw-DF-IIT, not a
membership condition.

**Attack: the defect symbols may define a larger monoid.** This attack succeeds.
The old proof computed only a cancellative bending lattice. It neither proved an
isomorphism of raw monoids nor killed the periodic secondary-fan kernel illustrated
by (7.6). Hypothesis 7.1 states both missing assertions explicitly.

**Attack: $A/A^\times$ loses nilpotent information.** This attack also succeeds.
For $k[e,h]/(e,h)^2$, $[e]^2=[h][e]=[0]$ without $[e]=[h]$; and the map
$2\mathbf N\to(k[e]/e^2)/(k[e]/e^2)^\times$ with $2\mapsto[e]$ need not extend
to $\mathbf N$. Thus cancellation and saturation are invalid over Artin rings.
Replacing scalars by the line-with-section groupoid preserves the information
but does not prove its factorization through the Fourier monoid. That factorization
is Raw-DF-IIT.

**Attack: $XY=\epsilon$ disproves intrinsic recognition.** It does not: a valid
intrinsic theorem would recover $1\mapsto\epsilon$, while $XY=0$ would recover
$1\mapsto0$. The example disproves compatibility with a separately fixed zero
chart. The unresolved higher-rank problem is the simultaneous raw factorization
around periodic wall circuits, not this rank-one node.

**Attack: the deformation ring counts periods twice.** Formula (8.3) has one
rank-$d$ Fourier monoid. At a face of dimension $r$ it has $r$ sharp parameters and
$d-r$ invertible Fourier parameters, still total dimension $d$. It represents the
supplied-DF/Mumford functor unconditionally and the full ambient functor only
conditionally on Raw-DF-IIT.

### 18.2 Normalization, conductor, and descent attacks

**Attack: normalization was made to commute with a smoothing.** It is not. Section
6.3 proves total-family flatness from the graded monomial algebra. Only after
restriction to a fixed boundary stratum are the fiber normalization and conductor
formed in (6.7), (10.3), and (10.7). The example $XY=q$ is kept explicit: its
total space is normal while its $q=0$ fiber is not. Formula (14.5) is likewise a
boundary-stratum restriction of the global determinant line.

**Attack: a formal Kummer root need not be algebraic.** Section 9.2 computes the integral closure as the finite monoid algebra $S'[P_\sigma^{\mathrm{fr}}]$, and Section 9.3 normalizes before completing. Excellence then identifies the completion. No root is introduced beyond the prescribed frame lattice.

**Attack: bounded normalization does not bound the structured gluing.** Section 10.3
separately retains the identity, group, action, endomorphism, polarization, level,
cubical, conductor, and theta-descent graphs. Proposition 10.1 proves uniform bounds
for every explicit Mumford chart. Transporting those bounds to every arbitrary
ambient degeneration is conditional on Raw-DF-IIT; the manuscript no longer uses
BCP to prove the recognition statement on which that transport depends.

**Attack: normalization and identity rigidification uniquely extend the theta
line.** This attack succeeds. On a conductor graph $\Gamma$, line bundles trivial
on the normalization retain the graph torus
$(\mathbf G_m)^{b_1(\Gamma)}$; a nodal cycle already retains one $\mathbf G_m$.
Identity rigidification fixes a base or vertex gauge, not the cycle holonomy. Book
16, Section 8.1, and Book 25, Section 12.1 give this counterboundary. Section 14.2 now
claims uniqueness only relative to an actual conductor descent datum, whose required
coherence is part of FRCD/RCD. No unproved theorem that cubical PEL data kills the
graph torus is smuggled into the argument.

**Attack: a Fitting stratum cannot prove an fs chart.** Agreed; it is never used for
that purpose. The base chart is the explicitly saturated monoid (11.3), and each
normalized family star has the saturated chart (11.4). Equality of powers on the
conductor does not prove root descent; saturation of the conductor pushout is stated
only under FRCD. Fitting ideals serve only to impose bounded locally closed
conditions after these charts exist.

**Attack: equality of $r$th powers leaves a $\mu_r$-ambiguity.** This attack
succeeds. A paired-frame over-lattice lists possible root exponents but does not
choose an isomorphism between roots on paired conductor faces. Hypothesis 9.1
requires the exact root comparisons and their face, deck, triple-overlap, and
nilpotent coherence. Section 11.3 no longer cancels the ambiguity.

**Attack: finite normalization was treated as flat.** This attack succeeds.
Hypothesis 9.2 isolates the finite-local-free statement for every nested frame
lattice. The finite map $k[x^2,xy,y^2]\to k[x,y]$ has generic rank two and a
three-dimensional fiber at the vertex, so finiteness of integral closure alone does
not authorize fppf descent. The former unsupported fundamental-parallelepiped basis
claim has been removed.

**Attack: generic Galois arrows need not descend over a ramified self-product.** The
valid route is to construct the unframed space first, conditionally in higher rank,
and only then take its finite normalization in the generic framed cover. Once the
unframed space exists, normalization and extension of the deck action are
unconditional, but they do not prove compatibility with labelled stars, exact
conductor roots, or nilpotents, and they do not make the normalization flat.
Conditional Theorem 12.1 uses Raw-DF-IIT, FRCD, and KFF for those further claims.
Full faithfulness is never presented as existence.

**Attack: the ample line might fail to descend even if the scheme descends.** On the
conditional global space, the
determinant formula (14.5) and the Cartier transitions (15.3) provide the line's descent
datum on every star and conductor face. Under FRCD the rooted conductor comparisons
are coherent, and under KFF the finite cover is actually fppf. Identifying the
resulting line with the structured Plucker pullback is separately TDC-Ext. Only with
that antecedent does tensoring deck transforms give the ample permutation-linearized
line used in Section 15.3.

**Attack: every PEL endomorphism acts on one fixed theta determinant.** This attack
succeeds. Section 14.3 restricts the action on $Rf_*\Theta^m$ to automorphisms
equipped with $g^*\Theta^m\simeq\Theta^m$. A general $\iota(a)$ maps instead to the
cohomology of $\iota(a)^*\Theta^m$; only $[n]$ has the displayed scalar-power formula
$[n]^*\Theta^m\simeq\Theta^{mn^2}$. No $\mathcal O_F$-action on a fixed
$\mathcal D_m$ is claimed.

### 18.3 Positivity and joining attacks

**Attack: strict convexity of a fan says nothing about the universal theta line.**
The manuscript keeps the lines separate. The universal theta line is on the family;
its determinant is on the base; and (15.3)--(15.4) define the fan line by Cartier data.
The chartwise calculation gives only the corrected determinant line (14.6). The
comparison (15.2) with the actual structured Plucker line is now clause 3 of
TDC-Ext, not a consequence of strict convexity.

**Attack: determinant of cohomology may jump on a nonnormal fiber.** The normalized-star resolution and conductor exact triangle give (14.3) and (14.5). For the chosen uniform theta power, higher cohomology vanishes on stars and all their intersections, so the determinant is a base-compatible line.

**Attack: the determinant exponent $\kappa_m$ is quadratic in $m$.** This attack
succeeds. Formula (14.4a) is a weighted lattice-point sum over a $d$-dimensional
polytope, so (14.4b) is generally a degree-$d+1$ Ehrhart quasipolynomial; in $d=2$
the centered example is $m^3A(y)$. The only retained positivity is the positive
interior-monodromy leading coefficient (14.4c). Determinant correction uses the
exact exponent in $P_\sigma^{\mathrm{gp}}\subset M$, while ampleness still comes
conditionally from the finite structured-graph morphism under TDC-Ext, not from this
asymptotic.

**Attack: (14.4a) controls every Plucker minor.** This attack succeeds. Formula
(14.4a) is the determinant transition for $f_*\Theta^m$; arbitrary evaluation,
multiplication, action, and conductor minors have different valuations. Hypothesis
15.1 therefore separately assumes extension without common zeros, quasi-finiteness,
and the exact line identity. The repository's general Hilbert/graph boundedness
results and the required TDC packages in Books 157--158 do not prove these assertions
under an alias.

**Attack: horizontal and vertical positivity do not imply mixed positivity.** Chapter
15 does not make that inference. The correct conditional route is the proper
quasi-finite structured Hilbert/graph map (15.1) to the projective parameter space
$Q^\theta$. It is finite, so its Plucker pullback is ample; the tensor of deck
translates descends. Properness uses the conditional global source, extension and
quasi-finiteness are TDC-Ext, and framed descent uses FRCD and KFF. GCC, Raw-DF-IIT,
and overlap exhaustion construct the source and its structured charts but do not
prove that the chosen Plucker coordinates separate all boundary points. No global
effective-cone finite-generation claim occurs, and Section 15.2 makes no cone-generation
assertion. The ample structured-graph line handles all curves directly.

**Attack: a complete formal cusp still does not meet the good interior.** The joining
model is not inferred from a completion. For $d\ge2$, Theorem 16.1(1) first
constructs the global projective compactification by algebraic overlaps, and
Conditional Theorem 17.1 then takes the open-and-closed closure of the selected
generic component in its paired-frame base change. For $d=1$, Book 111, Theorem
13.1 supplies only the global compactification and R1-FTJ separately supplies the
selected model and completed branch. In neither branch is the global model inferred
from the formal chart.

**Attack: a proper closed subset may occupy the whole special fiber.** Its naive
closure could if vertical components were added, but the schematic closure has a
uniformizer-saturated ideal. At the special-fiber generic DVR, a nonzero element of
minimal valuation cannot lie in $(\pi)$, because saturation would divide it by
$\pi$. Thus (17.3) excludes a special-fiber component.

**Attack: the slicing argument overstates what is known for $d=1$.** This attack
succeeds. Book 111, Theorem 13.1 is now cited only for its rank-one global
compactification. It is not cited for joining a selected branch to the good
component, avoiding an arbitrary proper $Z$, or congruence-stable ICS. R1-FTJ is
the separate supplied-model antecedent; once it holds, this manuscript proves
avoidance by (17.3), and the rank-one slicing tuple is empty. For $d\ge2$ the
higher-rank alternative has $d-1$ cuts. A rational good point still requires
(17.12).

**Attack: higher-rank Bertini was stated over an arbitrary residue field.** This
attack succeeds. The estimates (17.6) and the high-degree derivative argument are
finite-field Bertini. Section 17.3 and Conditional Theorem 17.2 now assume that $k$
is finite when $d\ge2$. FTJ itself and the rank-one empty-slice ICS argument do not
use that hypothesis.

### 18.4 Final theorem chain

The hostile checks identify five unproved higher-rank antecedents and a distinct
rank-one supplied-model antecedent. The exact dependency audit is as follows.

1. The cell algebra uses the homogeneous extension
   $\Phi_C(n,x)=n\varphi_C(x/n)$; (6.1c) proves semigroup closure, and (6.4) gives
   the correctly typed multiplication exponent. The Mumford action is typed by
   $B:Y\times X\to P^{\mathrm{gp}}$, $\lambda:Y\to X$, and
   $A:Y\to P^{\mathrm{gp}}$.
2. The fan regularization first removes inversions by barycentric subdivision and
   then uses coherent stellar subdivision on an orbit of faces whose distinct
   members lie in no common cone. Maximal multiplicity and the number of its cone
   orbits strictly decrease in succession. Theorem 4.2 is therefore proved, not an
   additional antecedent.
3. GCC is the first unproved antecedent for arbitrary geometric objects. It places
   such an object in a unique labelled Mumford fiber. Raw-DF-IIT cannot prove GCC
   because Raw-DF-IIT begins only after that label is fixed.
4. The completed Mumford ring (8.3) has exactly $d$ relative Fourier parameters.
   Its identification with the whole ambient deformation functor for $d\ge2$ is
   equivalent to the unproved Raw-DF-IIT factorization of actual
   $\operatorname{Div}(A)$-valued defects.
5. FRCD is independent of the existence of a frame over-lattice: it selects and
   coherently composes the $\mu_r$-ambiguous root comparisons on conductor faces.
   KFF is also independent: it makes every finite Kummer normalization used for
   descent finite locally free. Example (9.9) shows why finiteness is insufficient.
6. BCP unconditionally parameterizes every listed graph of the explicit Mumford
   atlas. Assuming GCC and Raw-DF-IIT, unframed AEC makes that atlas etale and
   exhaustive; its exact framed conductor-root enhancement also uses FRCD.
7. Under those hypotheses, AEC and algebraic overlap effectivity first construct the
   unframed proper space. Normalizing it in the generic paired-frame cover extends
   deck actions. Raw-DF-IIT and FRCD supply structured conductor and nilpotent
   compatibility, and KFF supplies the flat cover needed for fppf descent; together
   they give RCD.
   Once an unframed space is supplied, normalization and deck extension need no
   hypothesis, but flatness, root coherence, and nilpotent compatibility still do.
8. A theta line on the normalization plus identity rigidification does not determine
   conductor gluing: the residual parameter is the graph torus
   $(\mathbf G_m)^{b_1}$. Once an actual conductor descent datum is supplied, its
   effective descent is unique relative to that datum; the global compatibility
   asserted here is part of FRCD/RCD. No theorem killing this torus by the remaining
   cubical PEL data is claimed.
9. The determinant exponent is the exact element of
   $P_\sigma^{\mathrm{gp}}\subset M$ in (14.4a), generally a degree-$d+1$ weighted
   Ehrhart quasipolynomial with the positive leading scalar (14.4c), not a quadratic
   polynomial in $m$. The exact exponent supplies the Cartier correction for
   $\det f_*\Theta^m$ only; it does not control arbitrary Plucker minors. TDC-Ext is
   the separate fifth higher-rank antecedent supplying extension, quasi-finiteness,
   and the exact structured Plucker-line identity. With it, the finite structured
   Hilbert/graph map supplies a globally ample line directly; no positivity or
   finite-generation claim about an effective cone is used.
10. For $d\ge2$, GCC, Raw-DF-IIT, FRCD, KFF, and TDC-Ext feed the projective TCG
   model and then conditional FTJ. Higher-rank ICS additionally requires finite
   residue field for Bertini. For $d=1$, Book 111, Theorem 13.1 imports only the
   global compactification;
   R1-FTJ separately supplies the selected joining model and branch. The manuscript
   then proves arbitrary-$Z$ avoidance by (17.3) and ICS with the empty slicing
   tuple. Books 110--111 supply neither of those latter assertions.

Therefore the manuscript passes the hostile review only as a conditional
minitextbook. It is not ready as a proof of the higher-rank global compactification
or of the joining theorem in either rank branch. The higher-rank primitive gaps are
GCC (Hypothesis 3.1), Raw-DF-IIT (Hypothesis 7.1), FRCD (Hypothesis 9.1), KFF
(Hypothesis 9.2), and TDC-Ext (Hypothesis 15.1); higher-rank ICS also has the finite
residue-field antecedent. The rank-one joining gap is R1-FTJ, with dependencies
exactly as in (17.13). The explicit supplied-DF Mumford construction, its finite
normalization,
and BCP remain outside those recognition and descent gaps in their stated scopes.
The rank-one global compactification is imported from Book 111, Theorem 13.1, but
arbitrary-$Z$ rank-one FTJ and ICS are not. No unconditional higher-rank global
compactification or arbitrary-$Z$ joining theorem is claimed in this manuscript.
