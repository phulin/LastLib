# Cotangent Complexes, Perfect Complexes, and Determinant Lines

## Contents

- [1. Infinitesimal geometry needs a complex](#1-infinitesimal-geometry-needs-a-complex)
  - [1.1 The linear shadow of a ring map](#11-the-linear-shadow-of-a-ring-map)
  - [1.2 Conventions and scope](#12-conventions-and-scope)
  - [1.3 Three defects of ordinary differentials](#13-three-defects-of-ordinary-differentials)
  - [1.4 The road through the book](#14-the-road-through-the-book)
- [2. Derivations and Kähler differentials](#2-derivations-and-kähler-differentials)
  - [2.1 Derivations as first-order motion](#21-derivations-as-first-order-motion)
  - [2.2 The universal differential](#22-the-universal-differential)
  - [2.3 Polynomial, quotient, and localization calculations](#23-polynomial-quotient-and-localization-calculations)
  - [2.4 The conormal sequence](#24-the-conormal-sequence)
  - [2.5 The Jacobi--Zariski sequence](#25-the-jacobi--zariski-sequence)
  - [2.6 What differentials detect, and what they miss](#26-what-differentials-detect-and-what-they-miss)
- [3. Constructing the cotangent complex](#3-constructing-the-cotangent-complex)
  - [3.1 Free resolutions of algebras](#31-free-resolutions-of-algebras)
  - [3.2 The simplicial construction](#32-the-simplicial-construction)
  - [3.3 Independence and the universal property](#33-independence-and-the-universal-property)
  - [3.4 Presentation models and their limit](#34-presentation-models-and-their-limit)
  - [3.5 Basic calculations](#35-basic-calculations)
  - [3.6 Sheafification](#36-sheafification)
- [4. Transitivity and base change](#4-transitivity-and-base-change)
  - [4.1 Why compositions produce triangles](#41-why-compositions-produce-triangles)
  - [4.2 The transitivity triangle](#42-the-transitivity-triangle)
  - [4.3 Exact sequences in low degrees](#43-exact-sequences-in-low-degrees)
  - [4.4 Base change and Tor independence](#44-base-change-and-tor-independence)
  - [4.5 Localization, fibers, and completion](#45-localization-fibers-and-completion)
  - [4.6 A base-change failure](#46-a-base-change-failure)
- [5. Square-zero extensions and obstruction theory](#5-square-zero-extensions-and-obstruction-theory)
  - [5.1 Extensions are one degree beyond derivations](#51-extensions-are-one-degree-beyond-derivations)
  - [5.2 Classification of square-zero extensions](#52-classification-of-square-zero-extensions)
  - [5.3 Lifting maps across a square-zero ideal](#53-lifting-maps-across-a-square-zero-ideal)
  - [5.4 Deforming algebras and schemes](#54-deforming-algebras-and-schemes)
  - [5.5 Relative and constrained deformations](#55-relative-and-constrained-deformations)
  - [5.6 A node and a fat point](#56-a-node-and-a-fat-point)
- [6. Smooth, unramified, and étale morphisms](#6-smooth-unramified-and-étale-morphisms)
  - [6.1 Infinitesimal lifting criteria](#61-infinitesimal-lifting-criteria)
  - [6.2 Smoothness and degree zero](#62-smoothness-and-degree-zero)
  - [6.3 Unramifiedness and vanishing differentials](#63-unramifiedness-and-vanishing-differentials)
  - [6.4 Étaleness and a vanishing complex](#64-étaleness-and-a-vanishing-complex)
  - [6.5 Jacobians and standard smooth maps](#65-jacobians-and-standard-smooth-maps)
  - [6.6 Necessary finiteness warnings](#66-necessary-finiteness-warnings)
- [7. Local complete intersections](#7-local-complete-intersections)
  - [7.1 Regular sequences as independent equations](#71-regular-sequences-as-independent-equations)
  - [7.2 The two-term model](#72-the-two-term-model)
  - [7.3 The cotangent criterion for lci maps](#73-the-cotangent-criterion-for-lci-maps)
  - [7.4 Hypersurfaces and Jacobian maps](#74-hypersurfaces-and-jacobian-maps)
  - [7.5 Composition and flat base change](#75-composition-and-flat-base-change)
  - [7.6 Non-lci singularities](#76-non-lci-singularities)
- [8. Tor amplitude and perfect complexes](#8-tor-amplitude-and-perfect-complexes)
  - [8.1 Why bounded cohomology is not enough](#81-why-bounded-cohomology-is-not-enough)
  - [8.2 Perfect objects and strict models](#82-perfect-objects-and-strict-models)
  - [8.3 Tor amplitude](#83-tor-amplitude)
  - [8.4 Recognition by fibers](#84-recognition-by-fibers)
  - [8.5 Stability operations](#85-stability-operations)
  - [8.6 Perfect cotangent complexes](#86-perfect-cotangent-complexes)
- [9. Duality for perfect complexes](#9-duality-for-perfect-complexes)
  - [9.1 Dualizability](#91-dualizability)
  - [9.2 Evaluation, biduality, and tensor--Hom](#92-evaluation-biduality-and-tensor--hom)
  - [9.3 Amplitude under duality](#93-amplitude-under-duality)
  - [9.4 Euler characteristics and virtual rank](#94-euler-characteristics-and-virtual-rank)
  - [9.5 Self-dual complexes and parity](#95-self-dual-complexes-and-parity)
- [10. Graded lines and determinants](#10-graded-lines-and-determinants)
  - [10.1 Why ordinary top exterior powers are insufficient](#101-why-ordinary-top-exterior-powers-are-insufficient)
  - [10.2 The Picard groupoid of graded lines](#102-the-picard-groupoid-of-graded-lines)
  - [10.3 Determinant of a strict perfect complex](#103-determinant-of-a-strict-perfect-complex)
  - [10.4 Quasi-isomorphism invariance](#104-quasi-isomorphism-invariance)
  - [10.5 Shifts, duals, and tensor products](#105-shifts-duals-and-tensor-products)
  - [10.6 Base change and descent](#106-base-change-and-descent)
- [11. Determinants of exact sequences and triangles](#11-determinants-of-exact-sequences-and-triangles)
  - [11.1 The exact-sequence isomorphism](#111-the-exact-sequence-isomorphism)
  - [11.2 The triangle isomorphism](#112-the-triangle-isomorphism)
  - [11.3 Coherence and the octahedral test](#113-coherence-and-the-octahedral-test)
  - [11.4 Cohomology and canonical trivializations](#114-cohomology-and-canonical-trivializations)
  - [11.5 Two-term calculations](#115-two-term-calculations)
  - [11.6 Divisors from determinants](#116-divisors-from-determinants)
- [12. Determinant lines of cotangent complexes](#12-determinant-lines-of-cotangent-complexes)
  - [12.1 The cotangent determinant](#121-the-cotangent-determinant)
  - [12.2 Transitivity as multiplicativity](#122-transitivity-as-multiplicativity)
  - [12.3 Base change](#123-base-change)
  - [12.4 Lci presentations and adjunction](#124-lci-presentations-and-adjunction)
  - [12.5 Smooth and regular-immersion cases](#125-smooth-and-regular-immersion-cases)
  - [12.6 A complete-intersection calculation](#126-a-complete-intersection-calculation)
- [13. Smoothness calculations in PEL-type moduli](#13-smoothness-calculations-in-pel-type-moduli)
  - [13.1 The local deformation question](#131-the-local-deformation-question)
  - [13.2 Linear conditions and their complexes](#132-linear-conditions-and-their-complexes)
  - [13.3 Polarizations, endomorphisms, and determinant conditions](#133-polarizations-endomorphisms-and-determinant-conditions)
  - [13.4 A practical smoothness criterion](#134-a-practical-smoothness-criterion)
  - [13.5 Local models and the Jacobian determinant](#135-local-models-and-the-jacobian-determinant)
  - [13.6 Failure modes](#136-failure-modes)
- [14. Perfect complexes in patching](#14-perfect-complexes-in-patching)
  - [14.1 Why patch complexes rather than cohomology groups](#141-why-patch-complexes-rather-than-cohomology-groups)
  - [14.2 Minimal complexes over local rings](#142-minimal-complexes-over-local-rings)
  - [14.3 Amplitude, depth, and support](#143-amplitude-depth-and-support)
  - [14.4 Determinant bookkeeping through specialization](#144-determinant-bookkeeping-through-specialization)
  - [14.5 Presentation matrices and Fitting ideals](#145-presentation-matrices-and-fitting-ideals)
  - [14.6 A two-term patching calculation](#146-a-two-term-patching-calculation)
- [15. Reusable theorem packages](#15-reusable-theorem-packages)
  - [15.1 The lci package](#151-the-lci-package)
  - [15.2 The deformation package](#152-the-deformation-package)
  - [15.3 The determinant package](#153-the-determinant-package)
  - [15.4 The base-change protocol](#154-the-base-change-protocol)
  - [15.5 Final synthesis](#155-final-synthesis)

## 1. Infinitesimal geometry needs a complex

### 1.1 The linear shadow of a ring map

A family of algebraic objects can fail to be smooth for more than one reason. It may have too few first-order directions, equations among those directions, or relations among the equations themselves. Ordinary tangent and cotangent spaces see only the first layer. The central object of this book retains every layer that is relevant to the finite-presentation and complete-intersection problems occurring in arithmetic geometry.

Begin with a homomorphism of commutative rings $A\to B$. A first-order displacement of an $A$-algebra map out of $B$ is a derivation. Derivations are represented by the module $\Omega_{B/A}$ of Kähler differentials. If $B=A[x_1,\ldots,x_n]$, this module is free on $dx_1,\ldots,dx_n$, just as elementary calculus suggests. If $B=P/I$, the equations in $I$ contribute a map

$$
I/I^2\longrightarrow \Omega_{P/A}\otimes_P B.
$$

The cokernel is $\Omega_{B/A}$, but the kernel matters: it records dependencies among the first-order equations. A single module discards that kernel. The first improvement is therefore the two-term object

$$
[I/I^2\longrightarrow\Omega_{P/A}\otimes_PB]
$$

in degrees $-1$ and $0$. For a complete intersection this is the entire answer. For an arbitrary quotient there may be further information in degrees $-2,-3,\ldots$. Resolving the algebra itself by free algebras produces the full cotangent complex $L_{B/A}$.

The gain is conceptual as well as technical. Maps from $L_{B/A}$ into a $B$-module $M$ organize three questions in adjacent degrees:

$$
\begin{array}{c|c}
\text{degree}&\text{meaning}\cr\hline
0&\text{first-order changes and choices of lifts}\cr
1&\text{square-zero extensions and obstructions}\cr
\text{higher}&\text{higher dependencies among equations.}
\end{array}
$$

This is exactly the amount of homological structure needed below. We will not introduce a general theory of spaces built from arbitrary complexes; rings, schemes, modules, and their bounded complexes suffice.

### 1.2 Conventions and scope

All rings are commutative with identity. Complexes are cohomological: the differential raises degree, and

$$
(K[1])^i=K^{i+1},\qquad d_{K[1]}=-d_K.
$$

A module written without brackets occupies degree $0$. Thus $L_{B/A}$ has cohomology in nonpositive degrees in the situations considered here. We write

$$
D_i(B/A;M)=H^{-i}(L_{B/A}\otimes_B^LM)
$$

for cotangent homology and

$$
T^i(B/A;M)=\operatorname{Ext}^i_B(L_{B/A},M)
$$

for cotangent cohomology. In particular,

$$
T^0(B/A;M)=\operatorname{Der}_A(B,M).
$$

The notation $\det(E)$ will mean a graded determinant line, not the determinant of an endomorphism. For a finite projective module $P$ of constant rank $r$,

$$
\det(P)=\bigwedge^rP.
$$

On a scheme, all finiteness, amplitude, and complete-intersection conditions are local for the Zariski topology unless another topology is explicitly named. A morphism is **lci** when it is locally of finite presentation and locally factors as a regular closed immersion followed by a smooth morphism. No noetherian hypothesis is built into this definition; when a converse criterion needs noetherianity, it will be stated.

### 1.3 Three defects of ordinary differentials

The first defect is loss of relations. Let $B=k[x]/(x^2)$. The conormal map is

$$
(x^2)/(x^4)\longrightarrow B\,dx,\qquad x^2\longmapsto2x\,dx.
$$

If $\operatorname{char}k\ne2$, multiplication by $2x$ has kernel generated by the class of $x^3$. The cokernel $\Omega_{B/k}$ sees the permitted differentials, while the kernel already signals an obstruction layer. In characteristic $2$ the map is zero; the tangent behavior changes sharply although the defining equation has not disappeared.

The second defect is poor transitivity. For $A\to B\to C$, ordinary differentials give only a right-exact sequence

$$
\Omega_{B/A}\otimes_BC\longrightarrow\Omega_{C/A}
\longrightarrow\Omega_{C/B}\longrightarrow0.
$$

There is no visible term explaining failure of injectivity on the left. A triangle of cotangent complexes supplies it and continues in both directions.

The third defect is unreliable base change. Tensoring an exact sequence need not preserve exactness. The corrected statement uses derived tensor product and, for an ordinary cartesian square of rings, a Tor-independence hypothesis. This qualification will be decisive in singular fibers.

### 1.4 The road through the book

Chapters 2 and 3 pass from derivations to a presentation-independent complex. Chapters 4 and 5 establish the transitivity, base-change, and deformation mechanisms. Chapters 6 and 7 translate amplitude into smooth, étale, and lci geometry. Chapters 8 and 9 develop perfect complexes and their duals, the finite objects on which determinants behave well. Chapters 10--12 construct determinant lines with all signs and triangle compatibilities visible. The final two application chapters isolate the calculations used in PEL-type smoothness arguments and patching, and Chapter 15 gathers reusable statements with their exact hypotheses.

## 2. Derivations and Kähler differentials

### 2.1 Derivations as first-order motion

Let $M$ be a $B$-module. An $A$-derivation $d:B\to M$ is additive, vanishes on the image of $A$, and satisfies

$$
d(bb')=b\,d(b')+b'\,d(b).
$$

The rule is forced by first-order multiplication. Give $B\oplus M$ the square-zero product

$$
(b,m)(b',m')=(bb',bm'+b'm).
$$

An $A$-algebra section of $B\oplus M\to B$ has the form $b\mapsto(b,d(b))$, and it is multiplicative precisely when $d$ is a derivation. Thus derivations are not an analogy for infinitesimal motion; they literally classify sections of split first-order thickenings.

For $B=A[x_1,\ldots,x_n]$, a derivation is determined freely by $d(x_i)$. Hence

$$
\operatorname{Der}_A(B,M)\cong M^n.
$$

For $B=A[x]/(f)$, the choice $m=d(x)$ must satisfy $f'(x)m=0$ in $M$. This elementary Jacobian equation foreshadows the two-term complex of a hypersurface.

### 2.2 The universal differential

The module $\Omega_{B/A}$ is generated by symbols $db$, subject to additivity, $da=0$ for $a\in A$, and the Leibniz rule. Its universal derivation

$$
d_{B/A}:B\longrightarrow\Omega_{B/A}
$$

has the property that composition with it gives a natural isomorphism

$$
\operatorname{Hom}_B(\Omega_{B/A},M)
\xrightarrow{\sim}\operatorname{Der}_A(B,M).
$$

One concrete construction clarifies the geometry. Let $\mu:B\otimes_AB\to B$ be multiplication and $J=\ker\mu$. Then

$$
\Omega_{B/A}\cong J/J^2,\qquad db\longleftrightarrow 1\otimes b-b\otimes1.
$$

The diagonal map $\operatorname{Spec}B\to\operatorname{Spec}B\times_{\operatorname{Spec}A}\operatorname{Spec}B$ is cut out by $J$; its conormal module is therefore the module of differentials. This interpretation explains why smoothness of a map is reflected in the conormal geometry of its diagonal.

### 2.3 Polynomial, quotient, and localization calculations

For a polynomial algebra,

$$
\Omega_{A[x_1,\ldots,x_n]/A}
\cong\bigoplus_{i=1}^nA[x_1,\ldots,x_n]\,dx_i.
$$

The same formula holds for a polynomial algebra on an arbitrary set, with a direct sum. For a localization $S^{-1}B$,

$$
\Omega_{S^{-1}B/A}\cong S^{-1}\Omega_{B/A},
$$

because every derivation necessarily sends $b/s$ to

$$
d(b/s)=\frac{s\,d(b)-b\,d(s)}{s^2}.
$$

If $B=P/I$, every $A$-derivation of $P$ descending to $B$ kills $I$. The resulting presentation is

$$
I/I^2\xrightarrow{d}\Omega_{P/A}\otimes_PB
\longrightarrow\Omega_{B/A}\longrightarrow0,
$$

where $d(\bar f)=df\otimes1$. If $P=A[x_1,\ldots,x_n]$ and $I=(f_1,\ldots,f_r)$, the first arrow is represented by the Jacobian matrix

$$
\left(\frac{\partial f_i}{\partial x_j}\right)_{j,i}.
$$

The sequence need not be left exact. Treating it as short exact would erase precisely the singular information we seek.

### 2.4 The conormal sequence

Let $B\twoheadrightarrow C=B/I$. The quotient map gives an exact sequence

$$
I/I^2\longrightarrow\Omega_{B/A}\otimes_BC
\longrightarrow\Omega_{C/A}\longrightarrow0.
$$

Its proof is best read through universal properties. A $C$-linear map from the cokernel to a $C$-module $M$ is an $A$-derivation $B\to M$ that kills $I$, hence exactly an $A$-derivation $C\to M$. Representability identifies the cokernel with $\Omega_{C/A}$.

If $I$ is generated by a regular sequence $f_1,\ldots,f_r$, then $I/I^2$ is locally free over $C$ on the classes of the $f_i$. It does not follow that the conormal arrow is injective. For the hypersurface $k[x]/(x^2)$ it is multiplication by $2x$, which can have a kernel. Regularity of the immersion controls the module of equations; smoothness of the quotient additionally concerns their differentials.

### 2.5 The Jacobi--Zariski sequence

For $A\to B\to C$, derivations fit into

$$
0\longrightarrow\operatorname{Der}_B(C,M)
\longrightarrow\operatorname{Der}_A(C,M)
\longrightarrow\operatorname{Der}_A(B,M).
$$

Dualizing the representing modules gives the right-exact sequence

$$
\Omega_{B/A}\otimes_BC\longrightarrow\Omega_{C/A}
\longrightarrow\Omega_{C/B}\longrightarrow0.
$$

For polynomial maps this is the chain rule. For example, if $A=k$, $B=k[t]$, and $C=k[x]$ with $t\mapsto x^n$, then

$$
C\,dt\longrightarrow C\,dx,\qquad dt\longmapsto nx^{n-1}dx.
$$

The cokernel measures ramification. In characteristic dividing $n$, the map can vanish, illustrating that separability hypotheses cannot be omitted from differential criteria over fields.

### 2.6 What differentials detect, and what they miss

If $B$ is finitely presented over $A$, formal unramifiedness is equivalent to $\Omega_{B/A}=0$; finite presentation then makes the associated morphism unramified. If $B$ is smooth, $\Omega_{B/A}$ is finite projective. Neither converse holds without its missing hypotheses. A finite projective module of differentials does not by itself guarantee lifting, because hidden negative cotangent homology can contain obstructions.

An instructive boundary case is an inseparable field extension $K\subset L$ of characteristic $p$. If $L=K(u)$ with $u^p\in K$ but $u\notin K$, then $du$ is not forced to vanish and $\Omega_{L/K}\ne0$. A finite separable extension has zero differentials. Thus ordinary differentials distinguish separability for algebraic field extensions, but they do not organize the deformation data of a singular quotient. That requires the complex constructed next.

## 3. Constructing the cotangent complex

### 3.1 Free resolutions of algebras

A projective resolution of a module resolves additive relations. Here the relations concern multiplication itself, so we resolve $B$ by free $A$-algebras. A single polynomial presentation is not enough: relations among its equations require a second stage, relations among those relations a third, and so on.

The convenient bookkeeping device is a simplicial $A$-algebra $P_\bullet$ augmented to $B$. Each $P_n$ is polynomial over $A$, and the augmented simplicial set underlying $P_\bullet\to B$ is contractible in positive homotopical degrees. One constructs it inductively. Choose polynomial generators mapping onto $B$ in degree $0$; add degree-$1$ generators to kill the kernel; add degree-$2$ generators to kill relations among those generators; continue. Degeneracy maps insert repetitions, while face maps record sources, targets, and compositions of relations.

The important point is not a preferred resolution—there is none—but the abundance of free ones and the fact that any two admit comparison maps unique up to simplicial homotopy after refinement.

### 3.2 The simplicial construction

Apply Kähler differentials degreewise and then extend scalars to $B$:

$$
\Omega_{P_\bullet/A}\otimes_{P_\bullet}B.
$$

This is a simplicial $B$-module. Its normalized chain complex has homological degrees $0,1,2,\ldots$; place degree $n$ in cohomological degree $-n$. The resulting object is

$$
L_{B/A}.
$$

Normalization keeps the intersection of the kernels of all but one face map and uses the remaining face as differential. Degenerate simplices form a contractible summand, so normalization loses no homology. This construction immediately gives

$$
H^0(L_{B/A})\cong\Omega_{B/A}.
$$

The negative cohomology groups retain higher relations. Their tensor with a coefficient module gives cotangent homology.

### 3.3 Independence and the universal property

**Theorem (independence of resolution).** Let $P_\bullet\to B$ and $Q_\bullet\to B$ be free simplicial $A$-algebra resolutions. Then the normalized differential complexes obtained from them are canonically isomorphic in the derived category of $B$-modules. The isomorphism is functorial in $A\to B$.

**Proof strategy.** Free algebras lift against degreewise surjections. Use that lifting property inductively to construct comparison maps $P_\bullet\to Q_\bullet$ and $Q_\bullet\to P_\bullet$ over $B$. Any two lifts are joined by a simplicial homotopy. Applying differentials and normalization turns simplicial homotopies into cochain homotopies. The two composites are homotopic to the respective identities, so the normalized complexes are quasi-isomorphic. A common free refinement removes dependence on chosen comparisons. $\square$

There is also a characterization by derived derivations:

$$
R\operatorname{Hom}_B(L_{B/A},M)
$$

is the complex governing $A$-derivations from a free resolution of $B$ into $M$. Its degree-zero cohomology is ordinary derivations, and its first cohomology classifies square-zero extension data. This universal property is usually the most efficient route to functoriality.

### 3.4 Presentation models and their limit

Suppose $P\twoheadrightarrow B$ is a polynomial $A$-algebra with kernel $I$. Resolving the presentation through one relation stage gives a canonical identification after truncation in degrees at least $-1$:

$$
\tau_{\ge-1}L_{B/A}simeq
[I/I^2\longrightarrow\Omega_{P/A}\otimes_PB].
$$

One must not claim this two-term complex is always the full cotangent complex. It is full when the quotient is cut out by a regular sequence, and more generally under the lci hypotheses of Chapter 7. For an arbitrary ideal, higher syzygies can contribute below degree $-1$.

This limitation explains the role of the simplicial construction. A presentation supplies a fast low-degree calculation; the free resolution supplies an invariant object and remembers every higher relation.

### 3.5 Basic calculations

The construction gives the following anchors.

1. If $B=A[x_i]_{i\in I}$ is polynomial, then

   $$
   L_{B/A}\simeq\Omega_{B/A}[0]
   \cong\bigoplus_{i\in I}B\,dx_i.
   $$

2. If $A\to B$ is a localization, then $L_{B/A}\simeq0$. Indeed every $A$-derivation of $B$ is forced to vanish, and the localization has the unique lifting property against nilpotent ideals.

3. If $B=A/I$ and $I^2=0$, then the leading truncation is $I[1]$, which places $I$ in cohomological degree $-1$. More generally, for any quotient one has $\tau_{\ge-1}L_{B/A}\simeq(I/I^2)[1]$; this need not be the full complex unless the immersion has the required regularity.

4. If $K\subset L$ is a separable algebraic field extension, then $L_{L/K}\simeq0$. For finite separable extensions this follows from étaleness; the algebraic case follows by filtered colimits. For a purely inseparable extension, degree-zero differentials can be nonzero.

### 3.6 Sheafification

For a morphism of schemes $f:X\to S$, choose affine opens and form the ringwise complexes. Localization compatibility identifies them on overlaps, so they glue to an object $L_{X/S}$ of the derived category of quasi-coherent $\mathcal O_X$-modules. If $f$ is quasi-compact and quasi-separated and the affine constructions have quasi-coherent cohomology, all operations below remain inside quasi-coherent complexes.

The scheme-level notation suppresses no new construction. On $U=\operatorname{Spec}B$ mapping to $V=\operatorname{Spec}A$,

$$
L_{X/S}|_U\simeq\widetilde{L_{B/A}}.
$$

Consequently smoothness, lci amplitude, perfectness, and determinant lines may be checked on affine open covers. This local character is what makes the theory usable in moduli problems.

## 4. Transitivity and base change

### 4.1 Why compositions produce triangles

If $A\to B\to C$, an infinitesimal change of $C$ over $A$ has a part already visible in $B/A$ and a part relative to $B$. These parts need not split. The extension between them is encoded by a distinguished triangle, the homological replacement for the right-exact Jacobi--Zariski sequence.

At the level of derivations, restriction gives a map from $A$-derivations of $C$ to $A$-derivations of $B$. Its homotopy fiber consists of $B$-derivations of $C$. Representing this fiber sequence and reversing arrows produces the cotangent triangle.

### 4.2 The transitivity triangle

**Theorem (transitivity).** For homomorphisms $A\to B\to C$, there is a natural distinguished triangle of $C$-complexes

$$
L_{B/A}\otimes_B^LC\longrightarrow L_{C/A}
\longrightarrow L_{C/B}
\xrightarrow{+1}.
$$

It is functorial in commutative diagrams of triples and compatible with longer composites.

**Proof strategy.** Resolve $B$ freely over $A$, then resolve $C$ by algebras free over the chosen resolution of $B$. Degreewise Jacobi--Zariski sequences are split exact because polynomial variables over $A$ separate into variables used for $B$ and relative variables used for $C$. Normalization and scalar extension give a short exact sequence of representative complexes. Its cone triangle is the displayed triangle. Independence of free resolutions makes it canonical. $\square$

Two special cases are fundamental. If $B\to C$ is étale, then $L_{C/B}=0$, so

$$
L_{C/A}\simeq L_{B/A}\otimes_BC.
$$

If $A\to B$ is étale, then $L_{C/A}\simeq L_{C/B}$. Thus cotangent information is unchanged by adding or removing étale coordinates.

### 4.3 Exact sequences in low degrees

Taking cohomology of transitivity gives

$$
H^{-1}(L_{C/A})\to H^{-1}(L_{C/B})
\to\Omega_{B/A}\otimes_BC
\to\Omega_{C/A}\to\Omega_{C/B}\to0.
$$

The middle three terms recover Jacobi--Zariski, while $H^{-1}(L_{C/B})$ explains its possible failure on the left. Applying $R\operatorname{Hom}_C(-,M)$ reverses the triangle and yields a long exact sequence

$$
\cdots\to T^i(C/B;M)\to T^i(C/A;M)
\to T^i(B/A;M)\to T^{i+1}(C/B;M)\to\cdots,
$$

where $T^i(B/A;M)$ abbreviates $\operatorname{Ext}^i_C(L_{B/A}\otimes_B^LC,M)$. This is the main device for separating absolute deformations from those already present in a coefficient base.

### 4.4 Base change and Tor independence

Consider a pushout square of rings

$$
\begin{array}{ccc}
A&\longrightarrow&B\\
\downarrow&&\downarrow\\
A'&\longrightarrow&B'=B\otimes_AA'.
\end{array}
$$

There is always a natural comparison map

$$
L_{B/A}\otimes_B^LB'\longrightarrow L_{B'/A'}.
$$

**Theorem (ordinary base change).** If

$$
\operatorname{Tor}_i^A(B,A')=0\qquad(i>0),
$$

then the comparison map is an isomorphism. In particular, it is an isomorphism if either $B$ or $A'$ is flat over $A$.

**Proof strategy.** Base-change a free resolution of $B$ over $A$. Tor independence says its augmentation after tensoring with $A'$ still resolves the ordinary tensor product $B'$, rather than an object with extra negative homology. Differential modules of polynomial algebras commute with scalar extension degreewise. Normalize to obtain the comparison. $\square$

The hypothesis is not merely technical. Without it, the correct pushout retains higher Tor information, whereas the ordinary tensor product discards it.

### 4.5 Localization, fibers, and completion

Localization is flat, so for multiplicative sets $S\subset A$ and $T\subset B$ one obtains the expected formulas, for example

$$
L_{T^{-1}B/S^{-1}A}\simeq
L_{B/A}\otimes_B T^{-1}B
$$

when the maps are compatible. If $A\to k$ is a residue field and $B$ is flat over $A$, then for the fiber $B_k=B\otimes_Ak$,

$$
L_{B_k/k}\simeq L_{B/A}\otimes_B^LB_k.
$$

Thus amplitude and perfectness specialize exactly in flat families.

For adic completion, let $A\to B$ be a map of noetherian rings, let $J\subset B$, and suppose $B$ is essentially of finite type over $A$. Write $\widehat B$ for the $J$-adic completion. Flatness of noetherian completion and finite presentation of the cotangent data give

$$
L_{B/A}\otimes_B^L\widehat B\simeq L_{\widehat B/A}^{\mathrm{cont}}
$$

in the finite-type range, where the right side represents continuous derivations. If the base is completed as well, the ideals and topologies must be compatible. Without noetherianity, finite presentation, or derived completeness, ordinary completion can lose inverse-limit and Tor terms.

### 4.6 A base-change failure

Let $A=k[t]$, $B=k=A/(t)$, and $A'=k$. Then $B'=B\otimes_AA'=k$. The relative cotangent complex of the identity $k\to k$ is zero. On the other hand, $t$ is a regular element, so

$$
L_{k/k[t]}\simeq k[1]
$$

which places $k$ in cohomological degree $-1$ under our shift convention. Tensoring with $B'=k$ does not kill it. The comparison

$$
L_{k/k[t]}\otimes_k^Lk\longrightarrow L_{k/k}
$$

is therefore not an isomorphism. Correspondingly,

$$
\operatorname{Tor}_1^{k[t]}(k,k)\cong k.
$$

Geometrically, intersecting the closed point $t=0$ with itself is not transverse. The lost Tor group and the failed cotangent base change are two forms of the same excess intersection.

## 5. Square-zero extensions and obstruction theory

### 5.1 Extensions are one degree beyond derivations

Derivations classify splittings of the split extension $B\oplus M$. A nonsplit square-zero extension asks for an algebra $B'$ fitting into

$$
0\longrightarrow M\longrightarrow B'\longrightarrow B\longrightarrow0,
\qquad M^2=0,
$$

where multiplication by a lift of $b\in B$ on the ideal $M$ agrees with the given $B$-module structure. Choosing an additive splitting temporarily writes $B'$ as $B\oplus M$; its multiplication differs from the split one by a bilinear error. Associativity is a cocycle equation, and changing the splitting changes the error by a coboundary. This is why extensions occur one cohomological degree above derivations.

The cotangent complex packages the statement without requiring an additive splitting, which may not exist over the base ring.

### 5.2 Classification of square-zero extensions

**Theorem (square-zero extension classification).** Let $A\to B$ be a ring map and $M$ a $B$-module. Isomorphism classes of square-zero extensions of the $A$-algebra $B$ by $M$, with the identification of the kernel with $M$ fixed, are naturally in bijection with

$$
T^1(B/A;M)=\operatorname{Ext}^1_B(L_{B/A},M).
$$

The split extension represents zero. The automorphism group of any fixed extension inducing the identity on both $B$ and $M$ is

$$
T^0(B/A;M)=\operatorname{Der}_A(B,M).
$$

**Proof strategy.** Pull an extension back along a free simplicial resolution of $B$. Freeness permits degreewise splittings. Differences between compatible splittings form a degree-one cocycle in the Hom complex from $L_{B/A}$ to $M$; changing splittings adds a coboundary. Conversely, a cocycle twists multiplication and descent along the resolution. The cocycle equation supplies associativity, and coboundaries give isomorphic extensions. Degree-zero cocycles are exactly automorphisms. $\square$

For a polynomial algebra $P/A$, $L_{P/A}$ is projective in degree $0$, so $T^1(P/A;M)=0$. Every square-zero extension of $P$ by $M$ splits as an $A$-algebra. This is the infinitesimal lifting freedom of affine space.

### 5.3 Lifting maps across a square-zero ideal

Suppose $C'\twoheadrightarrow C$ is a surjection of $A$-algebras with square-zero kernel $J$, and $u:B\to C$ is an $A$-algebra map. Regard $J$ as a $B$-module through $u$. Pulling $C'$ back along $u$ produces a square-zero extension of $B$ by $J$, hence a class

$$
o(u,C')\in T^1(B/A;J).
$$

**Lifting theorem.** The map $u$ lifts to an $A$-algebra map $B\to C'$ if and only if $o(u,C')=0$. When lifts exist, their set is a torsor under

$$
T^0(B/A;J)=\operatorname{Der}_A(B,J).
$$

Indeed, a lift is precisely a splitting of the pulled-back extension. Two splittings differ by a derivation. The torsor may be empty; once a base lift is chosen, adding derivations identifies it noncanonically with the derivation group.

For a presentation $B=P/I$, choose arbitrary lifts to $C'$ of the images of polynomial generators of $P$. The equations in $I$ then land in $J$. Their values define a $B$-linear map $I/I^2\to J$. Its class modulo changes of generator lifts is exactly the obstruction computed from the two-term truncation. When $B/A$ is lci, no lower terms are missing and this Jacobian calculation is complete.

### 5.4 Deforming algebras and schemes

Let $A'\twoheadrightarrow A$ have square-zero kernel $J$, and let $B$ be an $A$-algebra. A flat deformation of $B$ to $A'$ is an $A'$-algebra $B'$ flat over $A'$ together with $B'\otimes_{A'}A\cong B$. The obstruction is not merely an arbitrary element of $T^1(B/A,-)$: the change of base supplies a canonical class through transitivity. Under standard flatness hypotheses, its vanishing is tested in

$$
\operatorname{Ext}^2_B(L_{B/A},B\otimes_AJ),
$$

while isomorphism classes of deformations, if nonempty, form a torsor under $\operatorname{Ext}^1$, and automorphisms reducing to the identity are $\operatorname{Ext}^0$. The shift relative to lifting a map comes from deforming the source algebra itself rather than splitting a fixed extension over it.

For schemes, replace Ext by global Ext:

$$
\operatorname{Ext}^i_X(L_{X/S},\mathcal M).
$$

The local-to-global spectral sequence

$$
H^p\bigl(X,\mathcal Ext^q(L_{X/S},\mathcal M)\bigr)
\Longrightarrow \operatorname{Ext}^{p+q}_X(L_{X/S},\mathcal M)
$$

separates local singularity obstructions from the obstruction to gluing local choices. Affine vanishing can eliminate the latter, but proper moduli problems often retain it.

### 5.5 Relative and constrained deformations

Suppose a deformation must preserve extra structure represented infinitesimally by a morphism of complexes

$$
L_{B/A}\longrightarrow Q.
$$

The allowed deformation complex is frequently the shifted fiber

$$
K=\operatorname{Fib}(L_{B/A}\to Q).
$$

Applying $R\operatorname{Hom}(-,M)$ yields a long exact sequence comparing unrestricted directions, variations of the constraint, and constrained directions. This construction must be justified for each moduli condition. Merely declaring a subset of deformations does not produce a fiber complex.

A determinant condition illustrates the linearization. For an endomorphism $1+\epsilon X$ of a rank-$n$ module,

$$
\det(1+\epsilon X)=1+\epsilon\operatorname{tr}(X).
$$

Thus fixing a determinant removes the trace direction when the trace map has the expected rank. If the residue characteristic divides $n$, scalar endomorphisms can have trace zero, so a naive decomposition into scalar and trace-zero parts fails. The complex and its actual trace map, rather than a dimension slogan, must be retained.

### 5.6 A node and a fat point

Let $B=k[x,y]/(xy)$. The hypersurface model is

$$
L_{B/k}\simeq[B\xrightarrow{(y,x)}B\,dx\oplus B\,dy].
$$

At the origin, tensoring with $k=B/(x,y)$ makes the differential zero. The fiber has one equation in degree $-1$ and two tangent covectors in degree $0$. The tangent space has dimension $2$, while the obstruction contribution records that the two directions cannot vary independently to all orders.

For $B=k[x]/(x^3)$,

$$
L_{B/k}\simeq[B\xrightarrow{3x^2}B\,dx].
$$

At the closed point the differential again vanishes, regardless of characteristic. Yet over $B$ the map is sensitive to whether $3=0$. The fiber records the embedding dimension and number of equations, while the full local complex records how the equation degenerates along the scheme. This distinction is essential in families: a constant fiber rank does not follow from a calculation at one point.

## 6. Smooth, unramified, and étale morphisms

### 6.1 Infinitesimal lifting criteria

An $A$-algebra $B$ is formally smooth if every map $B\to C/J$ lifts to $C$ for every square-zero ideal $J\subset C$. It is formally unramified if such a lift is unique whenever it exists, and formally étale if it exists uniquely. By Chapter 5, existence is controlled by $T^1$ and ambiguity by $T^0$.

Finite presentation turns these infinitesimal conditions into geometric ones:

$$
\begin{array}{c|c}
\text{finite-presentation condition}&\text{geometric condition}\cr\hline
\text{formally smooth}&\text{smooth}\cr
\text{formally unramified}&\text{unramified}\cr
\text{formally étale}&\text{étale.}
\end{array}
$$

Finite presentation cannot be dropped: lifting against nilpotent ideals controls infinitesimal behavior, while geometric smoothness also requires a finiteness condition.

### 6.2 Smoothness and degree zero

**Theorem (cotangent criterion for smoothness).** Let $A\to B$ be finitely presented. The following are equivalent:

1. $B$ is smooth over $A$;
2. $B$ is formally smooth over $A$;
3. $L_{B/A}$ is quasi-isomorphic to a finite projective $B$-module in degree $0$.

In this case that module is $\Omega_{B/A}$.

**Proof strategy.** Smoothness gives local standard-smooth presentations; the Jacobian criterion splits the conormal map and identifies the remaining differential module as finite projective. This collapses the cotangent complex to degree $0$. Conversely, if $L_{B/A}$ is projective in degree $0$, then $\operatorname{Ext}^1_B(L_{B/A},M)=0$ for every $M$, so every square-zero lifting obstruction vanishes. Finite presentation converts formal smoothness to smoothness. $\square$

The projectivity clause matters. Vanishing negative cohomology alone makes $L_{B/A}\simeq\Omega_{B/A}$, but if $\Omega_{B/A}$ is not projective, its first Ext can still obstruct lifting.

### 6.3 Unramifiedness and vanishing differentials

For any ring map,

$$
\operatorname{Der}_A(B,M)=0\text{ for all }M
\quad\Longleftrightarrow\quad\Omega_{B/A}=0.
$$

Thus a finitely presented map is unramified precisely when $\Omega_{B/A}=0$. Negative cotangent homology need not vanish. A regular closed immersion is unramified, but for $B=A/I$ its cotangent complex is $(I/I^2)[1]$, generally nonzero in degree $-1$. Unramified means uniqueness of lifts, not existence.

For a finite-type field extension $K\subset L$, unramifiedness is equivalent to finite separability. A transcendental separable extension has nonzero differentials, and a purely inseparable finite extension usually does as well.

### 6.4 Étaleness and a vanishing complex

**Theorem (cotangent criterion for étaleness).** If $A\to B$ is finitely presented, then it is étale if and only if

$$
L_{B/A}\simeq0.
$$

**Proof.** An étale map is smooth with $\Omega_{B/A}=0$, so the smoothness theorem gives the vanishing. Conversely, vanishing makes every square-zero lifting problem exist uniquely. Hence the map is formally étale, and finite presentation makes it étale. $\square$

This criterion is stable under arbitrary composition and under Tor-independent base change by the triangles of Chapter 4. It also explains why adjoining étale coordinates never changes a deformation complex.

### 6.5 Jacobians and standard smooth maps

Let

$$
B=A[x_1,\ldots,x_n]/(f_1,\ldots,f_r),
$$

and suppose the $f_i$ form a regular sequence. Then

$$
L_{B/A}\simeq
\left[B^r\xrightarrow{J}B^n\right],
\qquad
J=\left(\frac{\partial f_i}{\partial x_j}\right).
$$

If an $r\times r$ minor of $J$ is invertible, the map $B^r\to B^n$ is a split injection and its cokernel is finite projective of rank $n-r$. The cotangent criterion then proves smoothness of relative dimension $n-r$ on that open set.

Conversely, at a point of a complete-intersection fiber over a field, smoothness forces the Jacobian to have rank $r$. Thus the familiar Jacobian test is the assertion that a two-term cotangent complex collapses to a vector bundle in degree $0$.

### 6.6 Necessary finiteness warnings

Formal smoothness without finite presentation can be enormous. A polynomial algebra in infinitely many variables has the lifting property and free differentials of infinite rank, but its spectrum is not smooth in the finite-presentation sense. Similarly, $L_{B/A}=0$ for some filtered colimits of étale algebras, while the resulting map is not finitely presented and hence not étale by the geometric definition.

Flatness is also independent. The quotient $A\to A/I$ has $\Omega_{(A/I)/A}=0$, so it is unramified, but it is rarely flat. Vanishing of degree $0$ therefore cannot be substituted for vanishing of the whole complex. The degree $-1$ conormal module remembers the closed immersion.

## 7. Local complete intersections

### 7.1 Regular sequences as independent equations

A sequence $f_1,\ldots,f_r$ in a ring $P$ is regular if $(f_1,\ldots,f_r)\ne P$ and each $f_i$ is a non-zero-divisor on $P/(f_1,\ldots,f_{i-1})$. In a local ring the definition is taken inside the maximal ideal. Regularity means that equations cut successively with no hidden torsion at each stage.

If $I=(f_1,\ldots,f_r)$ is generated by a regular sequence, then

$$
I/I^2\cong\bigoplus_{i=1}^r(P/I)\bar f_i.
$$

The proof filters $I$ by the successive ideals. A relation $\sum a_if_i\in I^2$ can be reduced one coefficient at a time; non-zero-divisors force $a_i$ into $I$ modulo later terms. Thus the first-order equations are independent even though their differentials may fail to be.

### 7.2 The two-term model

**Theorem (complete-intersection model).** Let $P$ be smooth over $A$, let $I\subset P$ be locally generated by a regular sequence, and set $B=P/I$. Then

$$
L_{B/A}\simeq
\left[I/I^2\xrightarrow{d}\Omega_{P/A}\otimes_PB\right]
$$

in cohomological degrees $-1,0$. Both terms are finite locally free if $P/A$ and the regular sequence are of finite presentation. Consequently $L_{B/A}$ is perfect of Tor amplitude contained in $[-1,0]$.

**Proof strategy.** First handle a quotient by one non-zero-divisor. The free resolution has no higher relation homology, and transitivity identifies the quotient cotangent complex with $(I/I^2)[1]$. Add the equations one at a time. At each step transitivity extends the two-term complex by one locally free conormal summand. Regularity ensures no unexpected Tor term appears. Finally compose with the smooth map $A\to P$, whose cotangent complex is $\Omega_{P/A}$ in degree $0$. $\square$

The differential is still the Jacobian map. The theorem says that there are no terms further left; it does not say the Jacobian is injective.

### 7.3 The cotangent criterion for lci maps

**Theorem (lci criterion).** Let $f:X\to S$ be locally of finite presentation.

- If $f$ is lci, then $L_{X/S}$ is perfect of Tor amplitude contained in $[-1,0]$.
- Conversely, if $X$ and $S$ are locally noetherian and $f$ is essentially of finite type, then perfectness of $L_{X/S}$ with Tor amplitude in $[-1,0]$ implies that $f$ is lci.

Versions of the converse hold beyond the noetherian setting under finite-presentation and finite-presentation-of-relations hypotheses; the stated form is the one used here.

**Proof strategy for the converse.** Locally factor $f$ through affine space, so $B=P/I$ with $P$ smooth over $A$. Transitivity identifies the relative quotient part. The amplitude hypothesis forces $I/I^2$ to be finite projective and eliminates higher cotangent homology. In the noetherian local ring $P_\mathfrak p$, the resulting homological criterion implies that $I_\mathfrak p$ has finite projective dimension equal to its minimal number of generators and grade. The Auslander--Buchsbaum and depth criteria then show that a minimal generating set is a regular sequence. $\square$

This theorem turns a geometric factorization condition into an intrinsic statement. It is one of the principal reasons to retain Tor amplitude rather than just cohomology degrees.

### 7.4 Hypersurfaces and Jacobian maps

Let $B=P/(f)$ with $P/A$ smooth and $f$ a non-zero-divisor. Then

$$
L_{B/A}\simeq[B\bar f\xrightarrow{df}\Omega_{P/A}\otimes_PB].
$$

For $P=A[x]$ this is $[B\xrightarrow{f'}B]$. Its degree-$0$ cohomology is $B/(f')$, while degree $-1$ is the annihilator of $f'$. At a point of a fiber, the differential vanishes precisely when the hypersurface tangent space acquires an extra dimension.

Take $B=k[x]/(x^n)$. If the characteristic does not divide $n$, the differential is multiplication by $nx^{n-1}$. Its kernel is $(x)$ and its cokernel is $B/(x^{n-1})$. If the characteristic divides $n$, the differential is zero and both cohomology groups enlarge. The ring remains a hypersurface, so its cotangent complex keeps amplitude $[-1,0]$; lci does not mean smooth.

### 7.5 Composition and flat base change

If $X\to Y$ and $Y\to S$ are lci, then $X\to S$ is lci. The transitivity triangle combines two perfect complexes of amplitude $[-1,0]$, but a naive cone could have amplitude $[-2,0]$. The sharper assertion uses local factorizations: compose regular immersions after pulling back a smooth factorization, and use that regular sequences concatenate under the required flatness supplied by smooth maps. Thus geometry improves the coarse triangle bound.

An lci morphism remains lci after flat base change. Algebraically, a regular sequence stays regular after flat scalar extension; the two-term model then base-changes term by term. Under a merely Tor-independent base change, the cotangent complex still has amplitude $[-1,0]$, giving an intrinsic route to the same conclusion where the converse criterion applies.

A regular immersion followed by an arbitrary lci map also composes to an lci map when the evident Tor-independence conditions needed to preserve the regular sequence hold. Suppressing them can turn an intersection into a derived self-intersection and create excess homology.

### 7.6 Non-lci singularities

Let

$$
B=k[x,y]/(x^2,xy,y^2).
$$

The ideal has height $2$ but needs three generators. In the regular local ring $k[x,y]_{(x,y)}$, an ideal generated by a regular sequence of height $2$ would need exactly two minimal generators. Hence the origin is not lci. The presentation complex

$$
[I/I^2\to B\,dx\oplus B\,dy]
$$

still computes the degrees $-1$ and $0$ of $L_{B/k}$, but it is not the whole complex: relations such as

$$
y(x^2)-x(xy)=0,\qquad y(xy)-x(y^2)=0
$$

create further homology. This example is the standard warning against identifying an arbitrary presentation complex with the full cotangent complex.

## 8. Tor amplitude and perfect complexes

### 8.1 Why bounded cohomology is not enough

A bounded complex can behave unboundedly after tensoring if its terms are not flat. For instance, a module $M$ in degree $0$ is bounded, but $M\otimes_R^LN$ may have Tor in arbitrarily negative degrees as $N$ varies. Deformation and base-change arguments need uniform control under every scalar extension. Tor amplitude provides it.

A complex $K$ of $R$-modules has **Tor amplitude in $[a,b]$** if for every $R$-module $M$,

$$
H^i(K\otimes_R^LM)=0\qquad(i\notin[a,b]).
$$

It is not enough to test only $M=R$, which sees ordinary cohomology but not hidden nonflatness.

### 8.2 Perfect objects and strict models

A **strictly perfect complex** is a bounded complex of finite projective modules. A complex is **perfect** if it is locally quasi-isomorphic to a strictly perfect complex. Over a ring, this locality may be taken on a finite principal-open cover; over a scheme, it is Zariski local.

Every strictly perfect complex is K-flat, compact with respect to direct sums, and dualizable. Perfect complexes are stable under shifts, cones, direct summands, derived tensor products, and pullback. These closure properties are proved on strict local models and then descended.

Finite generation is indispensable. An infinite-rank free module is flat and has Tor amplitude $[0,0]$, but it has no determinant line and is not perfect. Conversely, a bounded complex with finitely generated cohomology need not be perfect over a singular ring; finite projective dimension is the missing condition.

### 8.3 Tor amplitude

If $P^\bullet$ is strictly perfect and $P^i=0$ outside $[a,b]$, then it has Tor amplitude in $[a,b]$. The converse holds locally for perfect complexes.

**Amplitude-shortening lemma.** Let $(R,\mathfrak m)$ be local and let $P^\bullet$ be a bounded complex of finite free modules. If $H^i(P^\bullet\otimes_RM)=0$ for every $M$ and every $i<a$, then $P^\bullet$ is homotopy equivalent to a complex vanishing below $a$. A dual statement holds above $b$.

**Proof strategy.** At the leftmost nonzero term, test against the residue field $k$. Vanishing says the reduced differential is injective in the needed position. A matrix minor is therefore a unit, so a free direct summand maps isomorphically onto a direct summand in the next degree. Split off this contractible pair. Repeat. The right endpoint is treated dually. $\square$

It follows that a perfect complex has Tor amplitude in $[a,b]$ exactly when locally it has a strict representative supported in those degrees.

### 8.4 Recognition by fibers

**Fiber criterion.** Let $R$ be a ring and $K$ a pseudo-coherent complex of finite Tor dimension. Then $K$ is perfect. If $R$ is local and $K$ is perfect, its Tor amplitude is the smallest interval containing the degrees in which

$$
H^i(K\otimes_R^Lk)
$$

is nonzero, where $k$ is the residue field.

Pseudo-coherence supplies finite free approximations on the left, while finite Tor dimension permits the amplitude-shortening argument to terminate on the right. Neither hypothesis alone suffices.

For a morphism of schemes and a point $x\in X$, the fiber

$$
L_{X/S}\otimes_{\mathcal O_X}^Lk(x)
$$

records the infinitesimal equations and tangent covectors at $x$. If the cotangent complex is perfect, its fiber dimensions vary upper semicontinuously, and constant ranks allow local strict models of fixed shape.

### 8.5 Stability operations

Let $K,L$ be perfect, with amplitudes $[a,b]$ and $[c,d]$. Then

$$
K\otimes_R^LL\text{ has amplitude }[a+c,b+d].
$$

If $K\to L\to M\to K[1]$ is a distinguished triangle and two terms are perfect, so is the third. Coarse amplitude bounds follow from the long exact Tor sequence; for example, if $K$ has $[a,b]$ and $L$ has $[c,d]$, then the cone has amplitude contained in

$$
[\min(c,a-1),\max(d,b)].
$$

Pullback preserves perfectness and amplitude because a bounded finite projective model remains such after scalar extension. Pushforward does not preserve perfectness without hypotheses; properness alone is insufficient over arbitrary bases. In the geometric situations used later, one assumes a proper perfect morphism and suitable finite Tor dimension before asserting that a pushforward is perfect.

### 8.6 Perfect cotangent complexes

For a finitely presented smooth map, $L$ is perfect of amplitude $[0,0]$. For an lci map, it is perfect of amplitude $[-1,0]$. A regular immersion has $L\simeq(I/I^2)[1]$, amplitude $[-1,-1]$. These three shapes are worth memorizing:

$$
\begin{array}{c|c|c}
\text{morphism}&L&\text{Tor amplitude}\cr\hline
\text{smooth}&\Omega[0]&[0,0]\cr
\text{regular immersion}&(I/I^2)[1]&[-1,-1]\cr
\text{lci}&[I/I^2\to\Omega]&[-1,0].
\end{array}
$$

Perfectness makes base change finite and determinant lines available. The amplitude distinguishes free parameters from equations. In a two-term lci model, the virtual rank

$$
\operatorname{rk}(L_{B/A})=operatorname{rk}\Omega_{P/A}\otimes B-operatorname{rk}I/I^2
$$

is the expected relative dimension.

## 9. Duality for perfect complexes

### 9.1 Dualizability

For a perfect complex $K$ over $R$, define

$$
K^\vee=R\operatorname{Hom}_R(K,R).
$$

On a strict model $P^\bullet$, this is the dual complex

$$
(P^\vee)^i=\operatorname{Hom}_R(P^{-i},R),
$$

with differential chosen so evaluation is a cochain map. Concretely, if $\phi$ has degree $i$, then

$$
d(\phi)=-(-1)^i\phi\circ d_P.
$$

Finite projectivity is exactly what lets termwise duality preserve quasi-isomorphisms and commute with localization.

### 9.2 Evaluation, biduality, and tensor--Hom

There are natural maps

$$
K^\vee\otimes_R^LK\longrightarrow R,
\qquad
K\longrightarrow K^{\vee\vee}.
$$

**Theorem (perfect duality).** If $K$ is perfect, biduality is an isomorphism, and for arbitrary complexes $L,M$ there are natural isomorphisms

$$
R\operatorname{Hom}_R(K,L)\simeq K^\vee\otimes_R^LL,
$$

$$
R\operatorname{Hom}_R(K\otimes_R^LL,M)
\simeq R\operatorname{Hom}_R(L,K^\vee\otimes_R^LM).
$$

**Proof.** For a finite projective module these are the ordinary dual-basis isomorphisms. They commute with shifts, finite direct sums, and cones. A bounded finite projective complex is assembled by those operations, so the assertions follow by induction; locality gives the general case. $\square$

The theorem can fail for an infinite free module: the natural map from its tensor dual to all homomorphisms need not be onto. Dualizability is therefore a genuine finiteness condition, not merely flatness.

### 9.3 Amplitude under duality

If $K$ is perfect of Tor amplitude $[a,b]$, then $K^\vee$ has amplitude $[-b,-a]$. A strict representative in degrees $[a,b]$ dualizes to one in the reflected interval. Consequently an lci cotangent complex has dual amplitude $[0,1]$. Its degree-$0$ part governs tangent directions; degree $1$ is the local obstruction layer.

For perfect $K$ and a module $M$,

$$
R\operatorname{Hom}_R(K,M)\simeq K^\vee\otimes_R^LM.
$$

Thus Tor-amplitude bounds immediately become Ext-amplitude bounds. This is the precise reason that lci deformation problems have no local cotangent cohomology above degree $1$ for module coefficients, even though global Ext may extend further through sheaf cohomology.

### 9.4 Euler characteristics and virtual rank

For a strict perfect complex $P^\bullet$ on a connected spectrum, define

$$
\operatorname{rk}(P^\bullet)=\sum_i(-1)^i\operatorname{rk}(P^i).
$$

Splitting an acyclic finite projective complex locally into elementary contractible pairs shows that this integer is invariant under quasi-isomorphism. It is additive in distinguished triangles and multiplicative under tensor product:

$$
\operatorname{rk}(K\otimes^LL)=\operatorname{rk}(K)\operatorname{rk}(L).
$$

If all cohomology modules are finite projective, then

$$
\operatorname{rk}(K)=\sum_i(-1)^i\operatorname{rk}H^i(K).
$$

Without projectivity of cohomology, the right side may not make sense pointwise as constant ranks, while the virtual rank of a perfect complex remains locally constant.

### 9.5 Self-dual complexes and parity

Suppose $K$ is perfect and carries an isomorphism

$$
K\simeq K^\vee[n].
$$

Then its fiber cohomology pairs degrees $i$ and $-n-i$. When the pairing is alternating on a middle cohomology group over a field of characteristic not $2$, that middle dimension is even. In characteristic $2$, alternating and skew-symmetric conditions separate, so parity conclusions require an actual alternating form.

Duality also acts on determinants. A self-duality identifies $\det(K)$ with a shifted dual of itself, often producing a square or a canonical trivialization after an orientation choice. Such a choice is additional data: self-duality alone need not select a square root, and signs from the virtual rank cannot be ignored. The next chapter builds the bookkeeping that makes these statements precise.

## 10. Graded lines and determinants

### 10.1 Why ordinary top exterior powers are insufficient

For a finite projective module $P$ of rank $r$, the top exterior power $\bigwedge^rP$ records changes of basis by their determinant. A complex contains modules in several degrees. Odd degrees must contribute inversely, because an acyclic two-term complex $P\xrightarrow{1}P$ should have trivial determinant. Moreover, interchanging two odd pieces contributes a sign. Ordinary ungraded line bundles remember the inverse but not the sign.

The remedy is modest: attach an integer degree to every line. The integer will be the virtual rank. Its parity controls commutativity. This is the smallest setting in which determinant isomorphisms for triangles can be canonical and coherent.

### 10.2 The Picard groupoid of graded lines

A **graded line** over a ring $R$ is a pair $(L,n)$, where $L$ is an invertible $R$-module and $n$ is a locally constant integer on $\operatorname{Spec}R$. Tensor product is

$$
(L,n)\otimes(M,m)=(L\otimes_RM,n+m).
$$

The commutativity isomorphism is

$$
\ell\otimes m\longmapsto(-1)^{nm}m\otimes\ell.
$$

The dual is $(L^\vee,-n)$. All morphisms preserve degree. These objects and their isomorphisms form a Picard groupoid: every object is tensor-invertible, and every morphism is an isomorphism.

For a finite projective module $P$ of locally constant rank $r$, define

$$
\operatorname{Det}(P)=(\bigwedge^rP,r).
$$

The capitalized symbol emphasizes the graded object; when only the line is at issue we write $\det(P)$. The grading is not cosmetic. If two modules of ranks $r$ and $s$ exchange order, top exterior powers acquire $(-1)^{rs}$, exactly the symmetry above.

### 10.3 Determinant of a strict perfect complex

For a bounded complex $P^\bullet$ of finite projective modules, set

$$
\operatorname{Det}(P^\bullet)
=\bigotimes_i\operatorname{Det}(P^i)^{(-1)^i}.
$$

Here exponent $-1$ means the dual graded line, and the factors are ordered by increasing $i$. Its degree is the virtual rank

$$
\sum_i(-1)^i\operatorname{rk}(P^i).
$$

For a two-term complex $E^{-1}\to E^0$,

$$
\det(P^\bullet)=\det(E^{-1})^{-1}\otimes\det(E^0).
$$

This convention agrees with the cohomological shift: moving a module from degree $0$ to degree $-1$ inverts its determinant.

### 10.4 Quasi-isomorphism invariance

To descend this construction from strict complexes to perfect objects, an acyclic strict complex must have a canonical trivialization. Locally, let

$$
Z^i=\ker(d:P^i\to P^{i+1}),\qquad
B^i=\operatorname{im}(d:P^{i-1}\to P^i).
$$

For an acyclic bounded complex of projectives, descending induction shows that the relevant cycles and boundaries are projective locally, and

$$
0\to Z^i\to P^i\to B^{i+1}\to0,\qquad Z^i=B^i.
$$

The exact-sequence exterior-power isomorphisms cancel every $\det(B^i)$ once positively and once negatively. The remaining line is canonically $R$. The signs are those dictated by graded commutativity.

If $P^\bullet\to Q^\bullet$ is a quasi-isomorphism, its cone is acyclic. The cone trivialization gives a canonical isomorphism

$$
\operatorname{Det}(P^\bullet)\xrightarrow{\sim}
\operatorname{Det}(Q^\bullet).
$$

Compatibility for composites follows by comparing the two filtrations of the iterated cone. Thus determinant descends to perfect complexes and is independent of strict representative.

### 10.5 Shifts, duals, and tensor products

The definitions yield a canonical identity

$$
\operatorname{Det}(K[1])\cong\operatorname{Det}(K)^{-1},
$$

and iterating gives

$$
\operatorname{Det}(K[n])\cong\operatorname{Det}(K)^{(-1)^n}.
$$

Duality requires a separate grading check. The underlying line satisfies

$$
\det(K^\vee)\cong\det(K)^\vee,
$$

but $K^\vee$ has the same virtual rank $r$ as $K$, whereas the tensor inverse of the graded line $\operatorname{Det}(K)$ has grade $-r$. Thus, as a graded line,

$$
\operatorname{Det}(K^\vee)
\cong\operatorname{Det}(K)^{-1}\otimes(R,2r).
$$

This harmless-looking grade correction is essential in parity arguments.

For perfect $K,L$ of locally constant virtual ranks $r,s$, multilinear algebra gives an isomorphism of underlying lines

$$
\det(K\otimes^LL)
\cong \det(K)^{\otimes s}\otimes\det(L)^{\otimes r}.
$$

For negative exponents one uses dual lines. The grade on the left is $rs$ and is recorded separately; putting the natural grades on both factors on the right would double-count it. The graded symmetry supplies the signs needed to make the line formula symmetric in $K$ and $L$. Writing it without recording an ordering can conceal a factor of $-1$.

### 10.6 Base change and descent

Let $R\to S$ and let $K$ be perfect over $R$. A finite projective representative base-changes termwise, and exterior powers commute with scalar extension. Hence

$$
\operatorname{Det}_S(K\otimes_R^LS)
\cong\operatorname{Det}_R(K)\otimes_RS.
$$

No flatness assumption is needed once $K$ is perfect: the strict representative is already flat. This is a major advantage of perfectness.

On a scheme, local determinant lines agree on overlaps because the quasi-isomorphism isomorphisms satisfy the cocycle condition. They therefore descend to an invertible sheaf with a locally constant grading. If a perfect complex carries descent data for a faithfully flat cover, its determinant inherits descent data. Effectivity for line bundles then produces the determinant downstairs.

## 11. Determinants of exact sequences and triangles

### 11.1 The exact-sequence isomorphism

For a short exact sequence of finite projective modules

$$
0\longrightarrow P'\longrightarrow P\longrightarrow P''\longrightarrow0,
$$

there is a canonical isomorphism

$$
\operatorname{Det}(P)\xrightarrow{\sim}
\operatorname{Det}(P')\otimes\operatorname{Det}(P'').
$$

Locally choose a basis $e_1,\ldots,e_r$ of $P'$ and lift a basis $\bar f_1,\ldots,\bar f_s$ of $P''$ to $f_j\in P$. Send

$$
e_1\wedge\cdots\wedge e_r\wedge f_1\wedge\cdots\wedge f_s
$$

to the tensor of the two displayed top wedges. Changing lifts adds columns from $P'$ and does not change the wedge; changing bases acts by the same determinants on both sides. Hence the map is canonical.

The order is part of the convention: subobject first, quotient second. Reversing them multiplies by $(-1)^{rs}$ in the graded category.

### 11.2 The triangle isomorphism

**Theorem (determinant of a triangle).** For every distinguished triangle of perfect complexes

$$
K\longrightarrow L\longrightarrow M\longrightarrow K[1],
$$

there is a functorial isomorphism

$$
\operatorname{Det}(L)\xrightarrow{\sim}
\operatorname{Det}(K)\otimes\operatorname{Det}(M).
$$

**Proof strategy.** Represent the triangle locally by the cone of a cochain map $K\to L$. Since

$$
\operatorname{Cone}(K\to L)^i=L^i\oplus K^{i+1},
$$

the defining alternating product cancels the shifted $K$ factors against the inverse of $\operatorname{Det}(K)$. Reorder factors using graded symmetry. Invariance under replacement of cone models follows from the canonical trivialization of acyclic cones. $\square$

Rotation is a useful sign test. Rotating gives

$$
L\to M\to K[1]\to L[1].
$$

The new determinant isomorphism must agree with the old one after dualizing the $K$ factor and applying graded commutativity. Treating the symmetry as sign-free fails this test.

### 11.3 Coherence and the octahedral test

Suppose $K\to L\to N$ are composable maps. Their three cones fit into the octahedral diagram. There are then two ways to express $\operatorname{Det}(\operatorname{Cone}(K\to N))$ in terms of the other determinant lines. Coherence asserts that they agree.

On strict cone models, both composites reorder the same list of module factors. Every transposition of ranks $r,s$ contributes $(-1)^{rs}$; the total permutations have the same parity. Therefore the two maps coincide. This check is decisive: pairwise triangle isomorphisms without octahedral coherence would make determinant calculations depend on how a long exact construction was parenthesized.

Consequently a filtration of a perfect complex with perfect graded pieces gives a canonical isomorphism

$$
\operatorname{Det}(K)\cong\bigotimes_p\operatorname{Det}(\operatorname{gr}^pK),
$$

ordered by the filtration. Refining the filtration does not change the result.

### 11.4 Cohomology and canonical trivializations

If every $H^i(K)$ is finite projective, the truncation triangles give

$$
\operatorname{Det}(K)cong
\bigotimes_i\operatorname{Det}(H^i(K))^{(-1)^i}.
$$

This isomorphism is canonical; no splitting of the complex into its cohomology is required. The finite projectivity assumption may be weakened whenever the individual cohomology objects themselves admit determinant lines, but it cannot simply be omitted.

If $K$ is acyclic, the right side is the unit graded line and recovers the canonical trivialization. If $K$ becomes acyclic only after inverting an element $f$, then its determinant line acquires a canonical trivialization over $R[1/f]$. Comparing that generic trivialization with an integral generator measures the torsion of $K$.

### 11.5 Two-term calculations

Let $d:E\to F$ be a map of finite projective modules of ranks $e,f$, and put $K=[E\to F]$ in degrees $-1,0$. Then

$$
\operatorname{Det}(K)=\det(E)^{-1}\otimes\det(F),
\qquad \operatorname{rk}(K)=f-e.
$$

If $e=f=r$, exterior power gives a canonical section

$$
\det(d)\in\det(E)^{-1}\otimes\det(F).
$$

Where this section is invertible, $d$ is an isomorphism and $K$ is acyclic. Thus the determinant section is exactly the comparison between the integral determinant line and its acyclic trivialization.

If $e\ne f$, there is no scalar determinant of $d$. Maximal minors define degeneracy ideals, but choosing one minor amounts to choosing subquotients or trivializations. The determinant line still exists and has virtual rank $f-e$; it should not be confused with a single Jacobian determinant.

### 11.6 Divisors from determinants

Let $R$ be a discrete valuation ring with uniformizer $\pi$, fraction field $K$, and let $d:R^r\to R^r$ become an isomorphism over $K$. Smith normal form gives bases in which

$$
d=\operatorname{diag}(\pi^{a_1},\ldots,\pi^{a_r})
$$

up to units, with $a_i\ge0$. Hence

$$
\operatorname{length}_R(\operatorname{coker}d)
=\sum_i a_i=v_R(\det d).
$$

The determinant section therefore records the total torsion length. Over a normal integral scheme, applying this calculation at each height-one point produces a Cartier divisor whenever the section is regular and generically nonzero. Without normality or a non-zero-divisor condition, a determinant section still defines a degeneracy subscheme, but it need not determine a Cartier divisor.

## 12. Determinant lines of cotangent complexes

### 12.1 The cotangent determinant

If $f:X\to S$ has perfect cotangent complex, define its **cotangent determinant line** or **virtual canonical line** by

$$
\omega_f^{\mathrm{vir}}=\det(L_{X/S}).
$$

Its grading is the virtual relative dimension. For a smooth morphism of relative dimension $d$,

$$
\omega_f^{\mathrm{vir}}=\bigwedge^d\Omega_{X/S},
$$

the usual relative canonical line. For a regular immersion $i:X\hookrightarrow Y$ with conormal bundle $N^*_{X/Y}=I/I^2$,

$$
\omega_i^{\mathrm{vir}}=\det(N^*_{X/Y})^{-1}.
$$

The inverse is forced by the placement of the conormal bundle in degree $-1$.

### 12.2 Transitivity as multiplicativity

Let $X\xrightarrow fY\xrightarrow gS$, and assume the three cotangent complexes are perfect. The transitivity triangle gives

$$
\omega_{g\circ f}^{\mathrm{vir}}
\cong f^*\omega_g^{\mathrm{vir}}
\otimes\omega_f^{\mathrm{vir}}.
$$

The factor order follows the triangle

$$
Lf^*L_{Y/S}\to L_{X/S}\to L_{X/Y}\to.
$$

Its grading says that virtual dimensions add. For a factorization of an lci map as a regular immersion $i:X\hookrightarrow P$ followed by a smooth map $p:P\to S$,

$$
\omega_{X/S}^{\mathrm{vir}}
\cong\det(I/I^2)^{-1}\otimes i^*\det(\Omega_{P/S}).
$$

Although the right side uses a factorization, transitivity and coherence show that the resulting line is intrinsic.

### 12.3 Base change

In a cartesian square

$$
\begin{array}{ccc}
X'&\longrightarrow&X\\
\downarrow&&\downarrow f\\
S'&\longrightarrow&S,
\end{array}
$$

assume the square is Tor-independent and $L_{X/S}$ is perfect. Cotangent base change and determinant base change give

$$
\omega_{X'/S'}^{\mathrm{vir}}
\cong\omega_{X/S}^{\mathrm{vir}}|_{X'}.
$$

Flat base change is the most common sufficient condition. If Tor independence fails, even the cotangent complexes can differ, as in Section 4.6, so no such determinant comparison is valid without an excess term. When an excess complex is itself perfect, its determinant measures the correction.

### 12.4 Lci presentations and adjunction

Let $X\hookrightarrow P$ be a regular immersion of codimension $r$, with $P\to S$ smooth of relative dimension $n$. Then

$$
L_{X/S}\simeq[N^*_{X/P}\to\Omega_{P/S}|_X]
$$

and

$$
\omega_{X/S}^{\mathrm{vir}}
\cong\det(N^*_{X/P})^{-1}\otimes\omega_{P/S}|_X.
$$

If $X/S$ is smooth on an open subset $U$, this line restricts to $\bigwedge^{n-r}\Omega_{U/S}$. Thus the lci formula extends the canonical line across singular complete-intersection fibers.

For a Cartier divisor $X=(f)\subset P$, $N^*_{X/P}\cong\mathcal O_X(-X)$. Therefore

$$
\omega_{X/S}^{\mathrm{vir}}
\cong\omega_{P/S}(X)|_X,
$$

which is the adjunction formula. The cotangent triangle explains both the twist and its sign.

### 12.5 Smooth and regular-immersion cases

Two extreme cases serve as consistency checks. If $f$ is étale, $L_{X/S}=0$ and $\omega_f^{\mathrm{vir}}$ is canonically trivial of grade $0$. If $i$ is the zero section of a vector bundle $V\to S$, then $N^*\cong V^\vee$ and

$$
\omega_i^{\mathrm{vir}}\cong\det(V^\vee)^{-1}\cong\det(V).
$$

Composing the zero section with the smooth projection gives the identity on $S$. Transitivity yields

$$
\det(V^\vee)\otimes\det(V)\cong\mathcal O_S,
$$

as required. This simple example detects an incorrect inversion convention immediately.

### 12.6 A complete-intersection calculation

Let

$$
B=A[[x_1,\ldots,x_n]]/(f_1,\ldots,f_r),
$$

where $A$ is noetherian complete, the $f_i$ form a regular sequence, and continuous differentials are used. The chosen equations and coordinates identify

$$
L_{B/A}\simeq[B^r\xrightarrow{J}B^n],
$$

so

$$
\omega_{B/A}^{\mathrm{vir}}
\cong\det(B^r)^{-1}\otimes\det(B^n)\cong B
$$

after these choices, with grade $n-r$. A change of equations by a matrix $U$ and coordinates by a Jacobian matrix $V$ changes the generator by

$$
\det(U)^{-1}\det(V).
$$

Thus the trivialization is coordinate-dependent even though the line is intrinsic.

When $n=r$, $\det(J)$ is a section of this line. At primes where it is a unit, the map is étale. Over a discrete valuation ring, if $J$ is generically invertible, the valuation of $\det(J)$ is the length of the cotangent cokernel. This is the determinant-line form of a congruence or ramification calculation.

## 13. Smoothness calculations in PEL-type moduli

### 13.1 The local deformation question

A PEL-type moduli problem classifies abelian objects equipped with a polarization, an action by a prescribed order, and a level or determinant condition. Smoothness at a point means that every object over a square-zero quotient lifts locally and that the space of choices has the expected constant dimension. The extra structures turn an unrestricted deformation space into the kernel of explicit linear maps.

The efficient procedure is therefore:

1. identify the complex governing unrestricted infinitesimal changes;
2. linearize each additional condition;
3. form the fiber complex of those linear maps;
4. prove vanishing of its obstruction group and local freeness of its tangent group;
5. invoke finite presentation to pass from formal smoothness to smoothness.

Each step has independent hypotheses. In particular, a dimension count at geometric points does not by itself prove that the tangent sheaf is locally free or that obstructions vanish in families.

### 13.2 Linear conditions and their complexes

Let $x$ be a point of a moduli scheme $M$ over a base $S$, and suppose the deformation problem at $x$ is represented by a perfect tangent complex

$$
\mathcal T_x=R\operatorname{Hom}(L_{M/S}|_x,k(x)).
$$

If $M/S$ is lci, this has amplitude $[0,1]$. Then

$$
H^0(\mathcal T_x)=\text{tangent space},
\qquad
H^1(\mathcal T_x)=\text{primary obstruction space}.
$$

Suppose an ambient smooth moduli problem has tangent bundle $E$, and the imposed structure is cut out infinitesimally by a map of vector bundles $E\to F$. The constrained tangent complex is

$$
[E\longrightarrow F]
$$

in degrees $0,1$, dual to the cotangent lci model. Surjectivity of $E\to F$ kills $H^1$ and leaves a vector-bundle kernel in degree $0$. This is the linear algebra behind the usual smoothness calculation.

### 13.3 Polarizations, endomorphisms, and determinant conditions

An endomorphism action requires the varying Hodge subbundle to be stable under the order. Infinitesimally, this restricts an ambient Hom space to equivariant homomorphisms. A polarization identifies a quotient with a dual subbundle and imposes an isotropy condition; its derivative is a symmetry or alternating condition on the corresponding bilinear map. At primes where the relevant order is semisimple and the polarization degree is invertible, idempotent decompositions and perfect pairings make these restrictions direct summands.

A determinant condition prescribes the characteristic polynomial of the order action on the Hodge bundle. Its first derivative is a collection of trace maps on the eigensummands. When the order is étale over the base and the signature ranks are locally constant, those trace maps split into the expected direct summands. At ramified primes or when a rank jumps, this splitting can fail; then the determinant condition may introduce obstruction or nonreduced structure.

These assertions are linear-algebraic once a deformation theorem identifies deformations of the abelian object with lifts of its Hodge filtration. Such an identification requires its own hypotheses—typically an appropriate nilpotent divided-power thickening, or a separately established infinitesimal deformation theorem. The cotangent calculation begins after that input and does not replace it.

### 13.4 A practical smoothness criterion

**Theorem (constrained smoothness criterion).** Let $M\to S$ be locally of finite presentation, and suppose that near a point $x$:

1. $L_{M/S}$ is perfect of amplitude $[-1,0]$;
2. its dual is represented by $[E\xrightarrow{\alpha}F]$ in degrees $0,1$, with $E,F$ finite locally free;
3. $\alpha$ is surjective on a neighborhood of $x$.

Then $M\to S$ is smooth near $x$, with relative tangent bundle $\ker\alpha$ and relative dimension $\operatorname{rk}E-\operatorname{rk}F$.

**Proof.** Surjectivity between vector bundles is locally split, so the dual cotangent complex is quasi-isomorphic to $\ker\alpha$ in degree $0$. Dualizing again identifies $L_{M/S}$ with the finite locally free dual of this kernel in degree $0$. The cotangent smoothness criterion and local finite presentation finish the proof. $\square$

In a PEL calculation, $E$ is the ambient Hodge-filtration deformation space and $F$ collects failures of equivariance, isotropy, and determinant conditions. The substantive work is to prove that the combined linearization $\alpha$ is surjective, not merely that source and target have favorable dimensions.

### 13.5 Local models and the Jacobian determinant

Often an affine chart of a local model has a complete-intersection presentation

$$
R=A[x_1,\ldots,x_n]/(f_1,\ldots,f_r).
$$

The dual tangent complex is the transpose Jacobian map

$$
R^n\xrightarrow{J^{\mathsf t}}R^r.
$$

Surjectivity at a point is equivalent to an invertible $r\times r$ minor of $J$. The determinant line

$$
\det(R^n)\otimes\det(R^r)^{-1}
$$

records how local coordinates and equations transform. If $n=r$, the determinant section cuts out the nonsmooth locus scheme-theoretically when the zeroth Fitting ideal of $\Omega_{R/A}$ is generated by $\det J$.

For $n>r$, all maximal minors are needed. A single chosen minor describes one standard-smooth chart, not the entire degeneracy locus. Gluing the charts is naturally expressed by the determinant line and the exterior-power map

$$
\bigwedge^rR^r\longrightarrow\bigwedge^rR^n.
$$

### 13.6 Failure modes

Three failures recur at bad primes. First, the order acting on the Hodge bundle may cease to be étale, so eigenspace projectors acquire denominators and equivariant summands are no longer direct. Second, a polarization pairing may degenerate when its degree is not invertible, so isotropy equations lose independent differentials. Third, the determinant condition may impose fewer first-order equations than higher-order equations, producing a non-lci or nonreduced local model.

The cotangent complex distinguishes them. Failure of the Jacobian map to be surjective leaves $H^1$ in the tangent complex. Failure of the equations to be a regular sequence produces cotangent homology below degree $-1$. Failure of flatness can invalidate fiberwise base change. These are different diagnoses and require different repairs.

## 14. Perfect complexes in patching

### 14.1 Why patch complexes rather than cohomology groups

In a tower of arithmetic spaces, cohomology may occupy several adjacent degrees and may acquire torsion after changing coefficients. Patching individual cohomology groups discards the extensions and Tor terms connecting those degrees. A bounded finite free complex retains them and behaves predictably under specialization:

$$
C^\bullet\otimes_R^LS
$$

is computed by ordinary tensor product when $C^\bullet$ is finite free. Its determinant line and amplitude survive the passage exactly.

The typical input is a perfect complex over a complete local ring or a completed group algebra, together with a commuting action of a deformation ring. The arguments below concern only its commutative coefficient algebra and finite free models; no broader geometric machinery is needed.

### 14.2 Minimal complexes over local rings

Let $(R,\mathfrak m,k)$ be local. A bounded complex $F^\bullet$ of finite free $R$-modules is **minimal** if

$$
d(F^i)\subseteq\mathfrak mF^{i+1}
$$

for every $i$. Equivalently, $F^\bullet\otimes_Rk$ has zero differential.

**Minimal-model theorem.** Every bounded finite free complex over $R$ is isomorphic in the homotopy category to a direct sum of a minimal complex and contractible complexes of the form $[R\xrightarrow{1}R]$. The ranks of the terms in the minimal complex are uniquely determined and equal

$$
\operatorname{rk}_RF^i=\dim_kH^i(F^\bullet\otimes_Rk).
$$

**Proof strategy.** If a differential matrix has a unit entry, elementary row and column operations isolate an identity summand $R\to R$. The condition $d^2=0$ makes this pair a direct contractible summand. Remove such pairs until every entry lies in $\mathfrak m$. Reduction modulo $\mathfrak m$ then has zero differential, proving both the rank formula and uniqueness. $\square$

Minimality makes amplitude visible on the special fiber. It also prevents artificial free summands from corrupting determinant or rank counts.

### 14.3 Amplitude, depth, and support

Suppose $(R,\mathfrak m)$ is noetherian local and a finite $R$-module $M$ has a finite free resolution of length $l$. If $R$ is Cohen--Macaulay and $M$ has finite projective dimension, the Auslander--Buchsbaum formula gives

$$
\operatorname{depth}_RM=\operatorname{depth}R-\operatorname{pd}_RM.
$$

Thus a short perfect resolution forces large depth. If $R$ is regular of dimension $d$ and $M$ has finite length, then $\operatorname{depth}M=0$, so every finite free resolution has length at least $d$.

The corresponding intersection statement for a nonzero perfect complex is: if all its homology has finite length over a noetherian local ring $R$, then the difference between the largest and smallest degrees of a minimal finite free representative is at least $\dim R$. Its proof reduces by improved intersection inequalities to the module case after suitable truncations. This result should be applied only when total homology is supported at the closed point; arbitrary support requires localization and a codimension computed at each prime.

In patching, an amplitude bound from topology and a depth bound from a large regular auxiliary ring can meet at equality. Equality is powerful: it can force concentration in one degree or maximal Cohen--Macaulay behavior. It is not automatic from determinant data alone.

### 14.4 Determinant bookkeeping through specialization

Let $R\to S$ be any homomorphism and $C$ a perfect $R$-complex. Then

$$
\operatorname{Det}_S(C\otimes_R^LS)
\cong\operatorname{Det}_R(C)\otimes_RS.
$$

If $R\to S$ is a quotient, higher Tor in the cohomology groups is already encoded by the specialized complex; one must not replace the left side with alternating determinants of $H^i(C)\otimes_RS$ unless cohomology base change has separately been proved.

Suppose a finite group $\Delta$ acts and $R$ is finite free over a group ring $\mathcal O[\Delta]$. Specializing by the augmentation $\mathcal O[\Delta]\to\mathcal O$ gives a determinant comparison for the specialized perfect complex. If freeness or finite Tor dimension over the group ring fails, ordinary coinvariants can have higher Tor and the same formula must be read with derived tensor product.

This distinction is central in patching: determinant lines commute with specialization because the complex is perfect, while individual cohomology modules may not.

### 14.5 Presentation matrices and Fitting ideals

Let

$$
R^m\xrightarrow{A}R^n\longrightarrow M\longrightarrow0
$$

be a finite presentation. The zeroth Fitting ideal $\operatorname{Fitt}_0(M)$ is generated by the $n\times n$ minors of $A$ when $m\ge n$, and is zero when $m<n$. It is independent of the presentation and commutes with arbitrary base change.

If $m=n$, then

$$
\operatorname{Fitt}_0(M)=(\det A).
$$

The map $A$ is also a section of the determinant line of $[R^n\xrightarrow A R^n]$. If it is generically invertible over a domain, this section measures the codimension-one torsion of $M$. Over a discrete valuation ring its valuation equals $\operatorname{length}M$.

For a nonsquare presentation, the determinant line alone does not generate the Fitting ideal. Exterior powers of the map supply all maximal minors. Claims equating a determinant with a Fitting ideal therefore require a square presentation or an explicitly chosen determinant of a perfect torsion complex.

### 14.6 A two-term patching calculation

Let $R$ be a complete noetherian local domain and

$$
C=[R^r\xrightarrow{A}R^r]
$$

in degrees $q,q+1$. Assume $A$ is invertible over the fraction field. Then $H^q(C)=0$ and $H^{q+1}(C)=M=\operatorname{coker}A$ if $A$ is injective over $R$; injectivity follows, for example, because $R^r$ is torsion-free and $A$ is generically injective. The determinant line is canonically trivial as a line after choosing the two standard bases, and its generic acyclic trivialization differs by

$$
(\det A)^{(-1)^{q+1}}
$$

according to the parity of the placement.

After a flat local base change $R\to S$, the same statements hold with $A$ replaced by $A\otimes S$, and

$$
\operatorname{Fitt}_0(M\otimes_RS)=(\det A)S.
$$

After a nonflat quotient, $C\otimes_R^LS$ is still the correct two-term complex, but its left cohomology may become

$$
\operatorname{Tor}_1^R(M,S).
$$

The determinant comparison survives; concentration in one degree may not. This small calculation is the model for the more elaborate specialization steps in patching arguments.

## 15. Reusable theorem packages

### 15.1 The lci package

Let $f:X\to S$ be locally of finite presentation. To use the lci package, verify locally a factorization

$$
X\xrightarrow{i}P\xrightarrow{p}S
$$

with $p$ smooth and $i$ cut out by a regular sequence. Then:

$$
L_{X/S}\simeq
[I/I^2\to i^*\Omega_{P/S}]
$$

in degrees $-1,0$; it is perfect of Tor amplitude $[-1,0]$; its virtual rank is $\dim(P/S)-\operatorname{codim}(X,P)$; and

$$
\omega_{X/S}^{\mathrm{vir}}
\cong\det(I/I^2)^{-1}\otimes i^*\det(\Omega_{P/S}).
$$

The package is stable under flat base change. Under Tor-independent base change, the intrinsic complex and determinant base-change correctly; a geometric lci conclusion follows wherever the converse cotangent criterion is available. For a composition, use transitivity and a geometric factorization rather than relying only on the coarse amplitude of a cone.

### 15.2 The deformation package

For $A\to B$ and a $B$-module $M$:

$$
T^i(B/A;M)=\operatorname{Ext}^i_B(L_{B/A},M).
$$

Then $T^0$ is derivations and acts simply transitively on lifts of a fixed map once a lift exists; $T^1$ classifies square-zero extensions and contains the obstruction to lifting a map across a square-zero ideal. For deformations of the algebra $B$ over a square-zero enlargement of the base, the automorphism, deformation, and obstruction groups occur in degrees $0,1,2$ respectively, subject to the flatness and base-change hypotheses that construct the canonical obstruction class.

For a scheme, use global Ext. Before concluding unobstructedness from local amplitude, inspect the local-to-global spectral sequence: sheaf Ext above degree $1$ may vanish for an lci morphism while global $H^p$ still creates higher total Ext.

For a constrained problem, prove that the constraint has a linearization map and use its fiber. Dimension subtraction is valid only after proving the map has constant rank or is locally split.

### 15.3 The determinant package

For every perfect complex $K$ there is a graded line $\operatorname{Det}(K)$ satisfying:

$$
\begin{aligned}
\operatorname{Det}(K[1])&\cong\operatorname{Det}(K)^{-1},\\
\det(K^\vee)&\cong\det(K)^\vee\quad\text{on underlying lines},\\
\operatorname{Det}(L)&\cong\operatorname{Det}(K)\otimes\operatorname{Det}(M)
\qquad(K\to L\to M\to),\\
\operatorname{Det}(K\otimes_R^LS)&\cong\operatorname{Det}(K)\otimes_RS.
\end{aligned}
$$

All tensor products of determinant factors are ordered, and exchanging factors of grades $r,s$ contributes $(-1)^{rs}$. Exact triangles are compatible with rotation, composition, and the octahedral diagram. If the cohomology modules are finite projective, determinant may be computed from their alternating product; otherwise compute from a strict perfect representative.

A generically acyclic perfect complex has a generic trivialization of its determinant. Converting that trivialization into a Cartier divisor requires codimension-one regularity assumptions. A square two-term presentation converts it into the ordinary determinant and zeroth Fitting ideal; a rectangular presentation requires maximal minors.

### 15.4 The base-change protocol

Base change is safest when the following questions are answered in order.

1. Is the new ring or fiber an ordinary tensor product, and are the two inputs Tor-independent over the base?
2. Is the complex being pulled back perfect, so its derived pullback is represented termwise by finite projectives?
3. Does the desired assertion concern the complex or its individual cohomology groups?
4. If it concerns cohomology, have the relevant Tor groups or a cohomology-and-base-change criterion been checked?
5. If completion is involved, are noetherianity, finite generation, continuity, and derived completeness available?

With Tor independence,

$$
L_{B/A}\otimes_B^LB'\simeq L_{B'/A'}.
$$

With perfectness,

$$
\operatorname{Det}(K\otimes^LS)
\simeq\operatorname{Det}(K)\otimes S.
$$

Neither statement says that $H^i(K)\otimes S\to H^i(K\otimes^LS)$ is an isomorphism. That last assertion is separate and is precisely where specialization torsion enters.

### 15.5 Final synthesis

The cotangent complex begins with the elementary rule $d(xy)=x\,dy+y\,dx$ and repairs three losses in ordinary differentials. It retains relations among equations, turns composition into an exact triangle, and exposes the Tor hypotheses behind base change. In the finite-presentation range its shape has immediate geometric meaning: degree $0$ and projectivity characterize smoothness, total vanishing characterizes étaleness, and perfect amplitude $[-1,0]$ characterizes local complete intersections under the stated hypotheses.

Perfect complexes are the finite carriers of this information. Their amplitude survives every scalar extension, their duals turn cotangent degrees into tangent and obstruction degrees, and their virtual ranks record expected dimension. Determinant lines compress a perfect complex further without losing additivity. The graded sign rule makes that compression coherent across shifts, exact triangles, filtrations, and duality.

In moduli calculations, these ideas reduce smoothness to surjectivity of a concrete linearized constraint map, while distinguishing bad rank, nonregular equations, and failed base change. In patching, they preserve extension and Tor information that separate cohomology groups would discard; minimal complexes reveal amplitude, and determinant sections recover Fitting ideals and codimension-one lengths under exact hypotheses. The resulting toolkit remains entirely within rings, schemes, modules, and bounded perfect complexes, yet reaches the deformation and determinant calculations needed in arithmetic geometry.
