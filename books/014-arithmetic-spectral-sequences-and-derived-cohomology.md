# Arithmetic Spectral Sequences and Derived Cohomology

## Contents

- [1. Cohomology as layered arithmetic information](#1-cohomology-as-layered-arithmetic-information)
  - [1.1 Why spectral sequences occur](#11-why-spectral-sequences-occur)
  - [1.2 The categorical setting](#12-the-categorical-setting)
  - [1.3 Conventions and boundedness](#13-conventions-and-boundedness)
  - [1.4 Four arithmetic prototypes](#14-four-arithmetic-prototypes)
- [2. Complexes, homotopies, and derived categories](#2-complexes-homotopies-and-derived-categories)
  - [2.1 Complexes and their cohomology](#21-complexes-and-their-cohomology)
  - [2.2 Cones and homotopy](#22-cones-and-homotopy)
  - [2.3 Quasi-isomorphisms and localization](#23-quasi-isomorphisms-and-localization)
  - [2.4 Truncations and the standard filtration](#24-truncations-and-the-standard-filtration)
  - [2.5 The standard t-structure and extension data](#25-the-standard-t-structure-and-extension-data)
- [3. Resolutions and derived functors](#3-resolutions-and-derived-functors)
  - [3.1 Classical resolutions](#31-classical-resolutions)
  - [3.2 K-injective complexes](#32-k-injective-complexes)
  - [3.3 K-flat complexes](#33-k-flat-complexes)
  - [3.4 Existence and uniqueness of replacements](#34-existence-and-uniqueness-of-replacements)
  - [3.5 K-flat replacement of an unbounded complex](#35-k-flat-replacement-of-an-unbounded-complex)
  - [3.6 K-injective replacement and homotopy limits](#36-k-injective-replacement-and-homotopy-limits)
  - [3.7 Derived functors and acyclicity criteria](#37-derived-functors-and-acyclicity-criteria)
  - [3.8 A replacement checklist](#38-a-replacement-checklist)
- [4. The three derived operations](#4-the-three-derived-operations)
  - [4.1 Derived global sections](#41-derived-global-sections)
  - [4.2 Derived tensor product](#42-derived-tensor-product)
  - [4.3 Derived internal Hom](#43-derived-internal-hom)
  - [4.4 Projection and tensor-Hom formulas](#44-projection-and-tensor-hom-formulas)
  - [4.5 Tor, Ext, and change of rings](#45-tor-ext-and-change-of-rings)
- [5. Filtered complexes and spectral objects](#5-filtered-complexes-and-spectral-objects)
  - [5.1 Filtrations and associated graded complexes](#51-filtrations-and-associated-graded-complexes)
  - [5.2 Exact couples](#52-exact-couples)
  - [5.3 Pages and differentials](#53-pages-and-differentials)
  - [5.4 The derived viewpoint](#54-the-derived-viewpoint)
  - [5.5 Filtrations from arithmetic geometry](#55-filtrations-from-arithmetic-geometry)
- [6. Convergence, filtrations, and edge maps](#6-convergence-filtrations-and-edge-maps)
  - [6.1 Strong convergence](#61-strong-convergence)
  - [6.2 Conditional convergence and its failures](#62-conditional-convergence-and-its-failures)
  - [6.3 Edge maps and five- and seven-term sequences](#63-edge-maps-and-five--and-seven-term-sequences)
  - [6.4 Comparison theorems](#64-comparison-theorems)
  - [6.5 Degeneration is not splitting](#65-degeneration-is-not-splitting)
- [7. Double complexes and hypercohomology](#7-double-complexes-and-hypercohomology)
  - [7.1 Totalization and signs](#71-totalization-and-signs)
  - [7.2 The two spectral sequences](#72-the-two-spectral-sequences)
  - [7.3 Hypercohomology](#73-hypercohomology)
  - [7.4 Acyclic resolutions and Cech models](#74-acyclic-resolutions-and-cech-models)
  - [7.5 Two model calculations](#75-two-model-calculations)
- [8. The Leray spectral sequence](#8-the-leray-spectral-sequence)
  - [8.1 Construction](#81-construction)
  - [8.2 Functoriality and edge maps](#82-functoriality-and-edge-maps)
  - [8.3 Degeneration criteria and examples](#83-degeneration-criteria-and-examples)
- [9. The Hochschild--Serre spectral sequence](#9-the-hochschild--serre-spectral-sequence)
  - [9.1 Equivariant sections](#91-equivariant-sections)
  - [9.2 Construction and convergence](#92-construction-and-convergence)
  - [9.3 Restriction, inflation, and descent](#93-restriction-inflation-and-descent)
- [10. Products and multiplicative spectral sequences](#10-products-and-multiplicative-spectral-sequences)
  - [10.1 Filtered differential graded products](#101-filtered-differential-graded-products)
  - [10.2 Products on pages and on the abutment](#102-products-on-pages-and-on-the-abutment)
  - [10.3 Derived cup products](#103-derived-cup-products)
- [11. Base change and arithmetic comparison](#11-base-change-and-arithmetic-comparison)
  - [11.1 The base-change morphism](#111-the-base-change-morphism)
  - [11.2 A spectral criterion for base change](#112-a-spectral-criterion-for-base-change)
  - [11.3 Coefficient change and derived completion](#113-coefficient-change-and-derived-completion)
- [12. Reusable comparison theorems](#12-reusable-comparison-theorems)
  - [12.1 The filtered comparison package](#121-the-filtered-comparison-package)
  - [12.2 The derived-composition package](#122-the-derived-composition-package)
  - [12.3 The arithmetic base-change package](#123-the-arithmetic-base-change-package)
  - [12.4 Final synthesis](#124-final-synthesis)

## 1. Cohomology as layered arithmetic information

### 1.1 Why spectral sequences occur

Arithmetic geometry repeatedly asks for a global invariant of an object assembled in stages. A sheaf on a space is first pushed down to a base and then global sections are taken. A sheaf on a geometric fiber carries a Galois action and invariants are then formed. A degeneration is first measured on the geometric generic fiber and then specialized. Each procedure is a composite of operations that are exact only on one side. The obstruction to commuting “take the composite” with “take cohomology” is precisely the information arranged by a spectral sequence.

The basic pattern is

$$
E_2^{p,q}=R^pF(R^qG(A))\Longrightarrow R^{p+q}(F\circ G)(A).
$$

This formula is not an automatic slogan. It requires enough objects on which the relevant functors become exact, a comparison between a resolution for $G$ and one for $F\circ G$, and a boundedness or completeness hypothesis ensuring that the pages really recover the target. Much of this book is devoted to stating those hypotheses exactly.

A spectral sequence should be thought of as a controlled loss of extension data. Its limiting page gives the graded pieces of a filtration on the target, not usually a direct-sum decomposition. Thus even a degenerate sequence can conceal nontrivial arithmetic extensions. For example, if only $E_\infty^{0,1}$ and $E_\infty^{1,0}$ contribute to $H^1$, one obtains

$$
0\longrightarrow E_\infty^{1,0}\longrightarrow H^1
\longrightarrow E_\infty^{0,1}\longrightarrow0,
$$

and there need be no canonical splitting. Remembering this filtration is essential in integral and torsion problems.

### 1.2 The categorical setting

An **abelian category** is an additive category with a zero object, kernels and cokernels, in which every monomorphism is a kernel and every epimorphism is a cokernel. Modules over a ring, sheaves of modules on a site, and equivariant sheaves of modules are the principal examples. We use the ordinary diagram lemmas of abelian categories, including the snake lemma and the $3\times3$ lemma; each follows by factoring maps through kernels and cokernels and chasing their universal properties.

A **Grothendieck abelian category** is an abelian category with all small coproducts, exact filtered colimits, and a generator. The category of sheaves of modules on any small ringed site is Grothendieck. Here is the relevant reason. Sheafification is exact for modules, and filtered colimits are obtained by sheafifying objectwise colimits. For each object $U$ of the site, sheafify the free presheaf module represented by $U$. The resulting set of objects detects nonzero sections, and its coproduct is a generator.

The one nonformal input we take from this axiomatics is Grothendieck's theorem that such categories are hospitable to injective resolutions.

**Enough injectives in a Grothendieck abelian category.** Every Grothendieck abelian category $\mathcal A$ has enough injectives: every object of $\mathcal A$ admits a monomorphism into an injective object.

This belongs to the standard theory of Grothendieck categories and is not reproved here. Everything in Chapter 3 that resolves an object or a bounded-below complex injectively rests on that statement, and on nothing further about the site.

_Commentary on the argument._ The proof runs through lifting properties rather than through a hand-built transfinite tower, and it is worth recording its shape once, since the same small-object mechanism reappears whenever a replacement has to be produced. Injectivity is first characterized by a lifting property: an object $I$ is injective exactly when $I\to0$ has the right lifting property with respect to all monomorphisms. The technical heart is that this apparently unbounded test class can be replaced by a set. If $G$ is a generator of $\mathcal A$, then a morphism has the right lifting property with respect to the inclusions of subobjects of $G$ if and only if it has it with respect to every monomorphism. One may therefore apply the small object argument to the set of inclusions of subobjects of $G$. Factoring $X\to0$ through it yields $X\to I\to0$ in which $I\to0$ has the required right lifting properties, hence $I$ is injective, and in which $X\to I$ is a transfinite composition of monomorphisms, hence itself a monomorphism because filtered colimits are exact. That last step is where the AB5 axiom is genuinely used, and it is the step a naive stationarity argument tends to leave unexamined.

We work on a ringed site $(X,\mathcal O_X)$ with category $\operatorname{Mod}(X)$ of sheaves of $\mathcal O_X$-modules. An **arithmetic sheaf category** in this book means one of the following: $\operatorname{Mod}(X)$; modules over a sheaf of algebras on $X$; discrete sheaves with an action of a profinite group; or the ambient abelian category of inverse systems of such sheaves when completeness is imposed explicitly on the objects. We do not silently replace that ambient category by a full subcategory of complete objects, which need not be abelian. Nothing about the topology beyond the stated exactness and acyclicity hypotheses is silently used.

### 1.3 Conventions and boundedness

Complexes are cohomological. A complex $K$ has differentials $d^n:K^n\to K^{n+1}$ and shift

$$
(K[r])^n=K^{n+r},\qquad d_{K[r]}^n=(-1)^r d_K^{n+r}.
$$

Its cohomology is $H^n(K)=\ker d^n/\operatorname{im}d^{n-1}$. We write $D(\mathcal A)$ for the unbounded derived category, $D^+(\mathcal A)$ for objects with cohomology bounded below, and similarly $D^-$ and $D^b$.

A decreasing filtration $F$ satisfies $F^{p+1}K\subseteq F^pK$. Our cohomological spectral sequences have

$$
d_r:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1}.
$$

The total degree is $p+q$. A first-quadrant sequence has $E_r^{p,q}=0$ unless $p,q\ge0$. In each total degree it then has only finitely many possible terms, which is the simplest source of strong convergence.

### 1.4 Four arithmetic prototypes

It is useful to see the four principal constructions before building them. First, for a map $f:X\to Y$, a class on $X$ can have a vertical part along the fibers and a horizontal part on $Y$. The Leray term $H^p(Y,R^qf_*\mathcal F)$ records those degrees separately. Its differentials measure the failure of fiberwise classes to fit together over the base.

Second, suppose a geometric object $\bar X$ descends through a group $G$. A class on the quotient is not merely a $G$-invariant geometric class: descent data have their own cohomology. The terms

$$
H^p(G,H^q(\bar X,\mathcal F))
$$

separate descent obstruction from geometric degree. In low degree, an invariant geometric torsor may fail to descend, and its failure lies in $H^2(G,H^0)$.

Third, hypercohomology treats a complex of sheaves whose cohomology sheaves occupy several degrees. A two-term complex $[\mathcal F\to\mathcal G]$ is not determined by the kernel and cokernel of its differential: the extension joining them can produce a nonzero spectral differential.

Fourth, a cartesian square asks whether cohomology computed before a change of base agrees with cohomology computed after it. The two higher direct-image spectral sequences attached to the square separate the derived pullback degree from the direct-image degree, and the discrepancy lives in specific bidegrees. A base-change isomorphism is proved by comparing whole pages, never by comparing abutments alone.

Each prototype therefore contains a tower, successive layers, an exact couple, and a filtered target. Only the arithmetic meaning of the layers changes.

## 2. Complexes, homotopies, and derived categories

### 2.1 Complexes and their cohomology

Complexes retain the maps responsible for cohomology. Keeping only the groups $H^n(K)$ discards extension and product data, so the correct domain for derived operations is a category of complexes.

A cochain map $f:K\to L$ is a family $f^n$ commuting with differentials. It is a **quasi-isomorphism** if every $H^n(f)$ is an isomorphism. Exactness of

$$
0\longrightarrow K\longrightarrow L\longrightarrow M\longrightarrow0
$$

degree by degree gives a long exact cohomology sequence. To see the connecting map, lift a cocycle $m\in M^n$ to $l\in L^n$. Then $dl$ comes from a unique element of $K^{n+1}$ modulo boundaries; its class is independent of the lift. This construction is natural because all choices differ by elements whose differentials change the answer by a boundary.

The brutal truncation $\sigma_{\le n}K$ simply discards degrees above $n$ and is generally not quasi-isomorphism invariant. The intelligent truncation is

$$
(\tau_{\le n}K)^i=
\begin{cases}
K^i,&i<n,\\
\ker(d^n),&i=n,\\
0,&i>n,
\end{cases}
$$

and dually $\tau_{\ge n}K$ uses $\operatorname{coker}(d^{n-1})$ in degree $n$. It preserves the desired cohomology and kills the rest.

### 2.2 Cones and homotopy

For $f:K\to L$, the mapping cone is

$$
\operatorname{Cone}(f)^n=L^n\oplus K^{n+1},\qquad
d(l,k)=(d_Ll+f(k),-d_Kk).
$$

The signs make $d^2=0$. There is a triangle

$$
K\xrightarrow f L\longrightarrow\operatorname{Cone}(f)
\longrightarrow K[1].
$$

Its long exact sequence shows that $f$ is a quasi-isomorphism exactly when $\operatorname{Cone}(f)$ is acyclic. This turns a property of a morphism into a property of one object and is the decisive bridge to localization.

Two maps $f,g:K\to L$ are **homotopic** if there are $h^n:K^n\to L^{n-1}$ with

$$
f-g=d_Lh+hd_K.
$$

Homotopic maps induce equal cohomology maps: on a cocycle $x$, their difference is the boundary $d_Lh(x)$. The homotopy category $K(\mathcal A)$ has complexes as objects and homotopy classes as morphisms. Contractible complexes become zero there, but acyclic complexes need not. An exact sequence that does not split degreewise supplies typical acyclic, noncontractible examples.

### 2.3 Quasi-isomorphisms and localization

The derived category $D(\mathcal A)$ is obtained from $K(\mathcal A)$ by making every quasi-isomorphism invertible. Concretely, a morphism may be represented by a roof

$$
K\xleftarrow{s}K'\xrightarrow fL,
\qquad s\text{ a quasi-isomorphism}.
$$

Two roofs agree after passage to a common refinement. Composition uses a homotopy pullback. The cone criterion and the calculus of fractions show that this construction has the universal property: every functor out of $K(\mathcal A)$ that inverts quasi-isomorphisms factors uniquely through $D(\mathcal A)$.

The distinguished triangles in $D(\mathcal A)$ are those isomorphic to cone triangles. Applying $H^n$ gives long exact sequences. Rotating a triangle changes a sign; without that sign, successive connecting maps would not compose to zero.

**Derived-isomorphism criterion.** A morphism of complexes becomes an isomorphism in $D(\mathcal A)$ if and only if it is a quasi-isomorphism.

**Proof.** The forward implication follows because cohomology factors through the localization. The reverse implication is built into the localization. Equivalently, the cone is acyclic, hence becomes zero, so the cone triangle forces the morphism to be invertible. $\square$

This criterion does not say that every isomorphism in the derived category has an inverse represented by an inverse cochain map. That stronger statement holds for homotopy equivalences, not arbitrary quasi-isomorphisms.

### 2.4 Truncations and the standard filtration

The maps $\tau_{\le n}K\to K$ and $K\to\tau_{\ge n+1}K$ form a distinguished triangle

$$
\tau_{\le n}K\longrightarrow K\longrightarrow\tau_{\ge n+1}K
\longrightarrow\tau_{\le n}K[1].
$$

Its cohomology proves the asserted truncation properties. The successive layers satisfy

$$
\operatorname{Cone}(\tau_{\le n-1}K\to\tau_{\le n}K)
\simeq H^n(K)[-n].
$$

Thus a complex is assembled from its cohomology objects by extensions. This **Postnikov tower** is the first spectral object: applying any cohomological functor to the tower gives a spectral sequence. It also explains why a derived object is more than the list of its cohomology objects—the gluing morphisms between layers matter.

### 2.5 The standard t-structure and extension data

The truncation subcategories

$$
D^{\le0}=\{K:H^n(K)=0\text{ for }n>0\},\qquad
D^{\ge0}=\{K:H^n(K)=0\text{ for }n<0\}
$$

form the standard t-structure. Thus $D^{\le0}[1]\subseteq D^{\le0}$, $D^{\ge0}[-1]\subseteq D^{\ge0}$, there are no morphisms from $D^{\le0}$ to $D^{\ge1}$, and every $K$ occurs in the truncation triangle of Section 2.4. For the vanishing assertion, replace the target by a bounded-below injective complex and remove its boundary pieces; there is then no degree-preserving component from degrees at most zero to degrees at least one. The truncation triangle gives the decomposition assertion.

The heart $D^{\le0}\cap D^{\ge0}$ is the original abelian category, embedded in degree zero. The t-structure therefore recovers ordinary sheaves and supplies the cohomology objects intrinsically.

Suppose $K$ has only $H^0(K)=A$ and $H^1(K)=B$. Its truncation triangle is

$$
A\longrightarrow K\longrightarrow B[-1]\xrightarrow{\kappa}A[1].
$$

The connecting morphism $\kappa$ belongs to $\operatorname{Ext}^2(B,A)$. If it vanishes, the triangle splits and $K\simeq A\oplus B[-1]$; if it does not, the same cohomology objects produce a genuinely different derived object. Spectral differentials are systematic shadows of such gluing morphisms.

## 3. Resolutions and derived functors

### 3.1 Classical resolutions

An object $I$ is injective if every map from a subobject extends across the ambient object. An injective resolution of $A$ is an exact complex

$$
0\longrightarrow A\longrightarrow I^0\longrightarrow I^1\longrightarrow\cdots
$$

with each $I^n$ injective. In a category with enough injectives it is constructed recursively: embed $A$ in $I^0$, embed the cokernel in $I^1$, and continue. Given $A\to B$, injectivity lifts it step by step to a map of resolutions. Any two lifts are homotopic: their difference vanishes on $A$, factors through the first cokernel, and the same argument recursively constructs a homotopy. Hence applying an additive functor and taking cohomology is independent of all choices.

For a left exact functor $F:\mathcal A\to\mathcal B$, define

$$
R^nF(A)=H^n(F(I^\bullet)).
$$

Then $R^0F\cong F$, injective objects have no higher derived functors, and a short exact sequence gives a long exact sequence. The last statement follows from choosing compatible resolutions whose degreewise sequence is split exact, applying $F$, and using the long exact cohomology sequence.

Classical resolutions suffice for bounded-below objects. Unbounded complexes require a condition on the whole complex rather than on each term.

### 3.2 K-injective complexes

A complex $I$ is **K-injective** if every map $A\to I$ from an acyclic complex is null-homotopic. Equivalently, $\operatorname{Hom}^\bullet(A,I)$ is acyclic for every acyclic $A$. Indeed, degree-$n$ cocycles of this Hom complex are maps $A\to I[n]$, and boundaries are null-homotopies; stability under shifts identifies all degrees.

**K-injective lifting theorem.** If $I$ is K-injective, then

$$
\operatorname{Hom}_{K(\mathcal A)}(K,I)
\xrightarrow{\sim}\operatorname{Hom}_{D(\mathcal A)}(K,I)
$$

for every $K$.

**Proof.** Represent a derived morphism by $K\xleftarrow{s}K'\xrightarrow fI$. The cone of $s$ is acyclic. Applying $\operatorname{Hom}_{K(-)}(-,I)$ to its triangle shows that precomposition by $s$ is bijective, because the two adjacent Hom groups from shifts of the cone vanish. Thus $f$ descends uniquely to a homotopy class $K\to I$. The same argument proves injectivity. $\square$

**Bounded-below criterion.** A bounded-below complex of injective objects is K-injective.

**Proof strategy.** Given $f:A\to I$ with $A$ acyclic, construct a homotopy upward from the lowest nonzero degree of $I$. At stage $n$, the equation already established one degree lower makes the remaining error vanish on boundaries of $A$. Exactness identifies cycles with boundaries, and injectivity of $I^n$ extends the required map from cycles to all of $A^{n+1}$. Induction produces $h$ with $f=dh+hd$. $\square$

The boundedness is real. An unbounded complex whose terms are injective can fail to be K-injective because the upward induction has no starting degree.

### 3.3 K-flat complexes

Let $(X,\mathcal O_X)$ be ringed. A complex $P$ of right $\mathcal O_X$-modules is **K-flat** if $P\otimes A$ is acyclic for every acyclic complex $A$ of left modules. This is the tensor-side analogue of K-injectivity.

**Bounded-above criterion.** A bounded-above complex of flat modules is K-flat.

**Proof.** First suppose $P$ is bounded on both sides. Its finite brutal filtration has successive quotients equal to flat modules placed in one degree. Tensoring each quotient with an acyclic complex $A$ is acyclic, because a flat module preserves the short exact kernel-image sequences defining the cohomology of $A$. Induction through the finite filtration shows that $P\otimes A$ is acyclic.

For a merely bounded-above $P$, let $P_m$ be the brutal truncation supported between degrees $-m$ and the fixed upper bound. The inclusions $P_m\to P_{m+1}$ form a filtered system with colimit $P$. Tensor product commutes with this colimit, and filtered colimits are exact in the module and sheaf-module categories under consideration. Hence

$$
P\otimes A=\varinjlim_m(P_m\otimes A)
$$

is a filtered colimit of acyclic complexes and is acyclic. $\square$

A useful counterexample explains the letter K. A termwise flat unbounded complex need not preserve acyclicity under tensor product; infinite diagonals in the total complex can defeat the finite-filtration argument. K-flatness is exactly the invariant condition needed.

### 3.4 Existence and uniqueness of replacements

A derived operation is only as strong as the supply of replacements that computes it, so before using one we must produce it. Three existence questions arise, and they are genuinely different from one another. Right-derived operations ask for K-injective replacements $K\to I$. Derived tensor products ask for K-flat replacements $P\to K$. The sheaf-valued internal Hom asks for more than either, because $\mathcal Hom(A,I)$ records morphisms over every object of the site at once, and the acyclicity of a complex of global morphisms says nothing about local ones.

This section answers all three questions for bounded-below complexes, which is what the Cartan--Eilenberg construction gives, and it isolates the local refinement that internal Hom requires. Sections 3.5 and 3.6 then pass to unbounded complexes, where the two sides of the theory diverge. On the flat side, sheafification manufactures free objects with a lifting property and K-flatness survives the filtered colimits out of which an unbounded complex is built; unbounded K-flat replacements exist with no restriction whatever. On the injective side there is no dual of sheafification, an unbounded complex is assembled from its truncations by an inverse limit rather than a colimit, and the construction goes through a homotopy limit whose cohomology is controlled exactly when countable products are exact.

Throughout, $\mathcal A$ is a Grothendieck abelian category, so injective objects are plentiful by Section 1.2.

**The Cartan--Eilenberg construction.** For every degree $n$ of a bounded-below complex $K$, consider

$$
0\to Z^nK\to K^n\to B^{n+1}K\to0,
\qquad
0\to B^nK\to Z^nK\to H^nK\to0.
$$

Choose injective resolutions of the boundary and cohomology objects. The horseshoe construction applied to the second exact sequence gives a compatible injective resolution of $Z^nK$; applying it to the first gives one of $K^n$. These choices give short exact sequences of resolution complexes lifting both displayed sequences. Define the horizontal differential on the resolution of $K^n$ as the quotient to the chosen resolution of $B^{n+1}K$, followed by its inclusion through the resolutions of $Z^{n+1}K$ and $K^{n+1}$. Two successive horizontal maps compose to zero because the quotient from the resolution of $K^{n+1}$ kills the resolution of $Z^{n+1}K$. The resulting double complex has injective entries, resolves $K$ in one direction, and resolves its cycles, boundaries, and cohomology compatibly in the other. This is a Cartan--Eilenberg injective resolution.

Each total diagonal is finite because $K$ is bounded below and the resolution degree is nonnegative. Hence direct-sum and product totalizations agree. The row-filtration spectral sequence shows that the map from $K$ to the total complex is a quasi-isomorphism. In each degree that map is the augmentation of one column followed by the inclusion of a direct summand, hence a monomorphism, so its cokernel is acyclic as well. Each term of the total complex is a finite direct sum of injectives, hence injective; it is bounded below and therefore K-injective by Section 3.2. We record the conclusion.

**Bounded-below replacement theorem.** Every bounded-below complex $K$ in a Grothendieck abelian category admits a degreewise monomorphic quasi-isomorphism $K\to I$ in which $I$ is a bounded-below complex of injective objects; such an $I$ is K-injective, and the cokernel $I/K$ is acyclic. Consequently every complex whose cohomology vanishes in all sufficiently negative degrees admits a K-injective replacement: if $H^n(K)=0$ for $n<n_0$, compose the quasi-isomorphism $K\to\tau_{\ge n_0}K$ with a replacement of the bounded-below complex $\tau_{\ge n_0}K$.

The construction dualizes verbatim. In an abelian category with enough projectives, every bounded-above complex $C$ admits a degreewise epimorphic quasi-isomorphism $P\to C$ with $P$ a bounded-above complex of projectives: resolve cycles, boundaries, and cohomology by projectives in the downward direction, splice them by the horseshoe lemma in the same pattern, and totalize by direct sums, which again meet every diagonal in finitely many places. Section 3.5 uses precisely that form of the statement.

We turn to the local refinement. Fix a ringed site $(X,\mathcal O_X)$ with small underlying category, and for an object $U$ write $X/U$ for the localized site and $F|_U$ for the restriction of a sheaf $F$. Two elementary functors organize everything. First, for a sheaf $F$ of $\mathcal O_X|_U$-modules on $X/U$ let $j_{U!}F$ be the sheafification of the presheaf

$$
V\longmapsto\bigoplus_{\varphi:V\to U}F(V,\varphi).
$$

The presheaf formula is exact in $F$ because direct sums and sections of presheaves are exact, and sheafification is exact; hence $j_{U!}$ is exact. Second, the Yoneda lemma identifies a morphism out of the displayed presheaf with a compatible family of sections, which gives the adjunction

$$
\operatorname{Hom}_{\mathcal O_X}(j_{U!}F,G)
=\operatorname{Hom}_{\mathcal O_X|_U}(F,G|_U).
$$

Restriction to $U$ is therefore a right adjoint of an exact functor, so it preserves injective objects. It is itself exact, since kernels and cokernels of sheaves on $X/U$ are computed by the same recipe as on $X$.

Two further properties of $j_{U!}$ will be used. It satisfies the projection formula

$$
j_{U!}(A\otimes F|_U)\cong j_{U!}A\otimes F,
$$

both sides being the sheafification of the presheaf $V\mapsto\bigoplus_{\varphi:V\to U}A(V,\varphi)\otimes_{\mathcal O_X(V)}F(V)$; and it detects zero objects, because the summand indexed by the identity of $U$ exhibits $A$ as a direct summand of $(j_{U!}A)|_U$. Consequently flatness and K-flatness restrict: if $P$ is K-flat on $X$ and $A$ is an acyclic complex on $X/U$, then $j_{U!}(A\otimes P|_U)\cong j_{U!}A\otimes P$ is acyclic because $j_{U!}$ is exact, hence $A\otimes P|_U$ is acyclic, so $P|_U$ is K-flat.

Say that a complex $J$ of $\mathcal O_X$-modules is **internally K-injective** if $J|_U$ is K-injective on $X/U$ for every object $U$ of the site. Taking $U=X$ shows that an internally K-injective complex is K-injective; the point of the definition is that the converse is not formal, and that the internal Hom of Section 4.3 needs the local statement. Unwinding the definition, if $J$ is internally K-injective then $\mathcal Hom(A,J)$ has acyclic complexes of sections over every object of the site for every acyclic $A$, and is therefore acyclic as a complex of sheaves.

**Internal K-injectivity criterion.** A bounded-below complex $I$ of injective $\mathcal O_X$-modules is internally K-injective. Consequently, for every acyclic complex $A$ and every complex $K$ of $\mathcal O_X$-modules, $\mathcal Hom(A,I)$ is acyclic, and $\mathcal Hom(K,-)$ carries acyclic internally K-injective complexes to acyclic complexes.

**Proof.** Restriction is exact and preserves injectives, so $I|_U$ is a bounded-below complex of injective $\mathcal O_X|_U$-modules and is K-injective by Section 3.2. That is the assertion. For the consequences, products of sheaves are computed sectionwise, so

$$
\mathcal Hom^n(A,I)(U)
=\prod_i\operatorname{Hom}_{\mathcal O_X|_U}(A^i|_U,I^{i+n}|_U)
=\operatorname{Hom}^n_{\mathcal O_X|_U}(A|_U,I|_U),
$$

compatibly with differentials. The complex on the right is acyclic because $A|_U$ is acyclic and $I|_U$ is K-injective. A complex of sheaves with acyclic complexes of sections over every object has vanishing cohomology presheaves, hence vanishing cohomology sheaves. Finally, if $J$ is acyclic and internally K-injective, then the identity of $J|_U$ is a map from an acyclic complex to a K-injective one, hence null-homotopic, so $J|_U$ is contractible; then $\operatorname{Hom}^\bullet(K|_U,J|_U)$ is contractible for every $K$, and $\mathcal Hom(K,J)$ is acyclic by the same sectionwise argument. $\square$

The last clause is what makes derived internal Hom well defined: it says that replacing the first variable by a quasi-isomorphic complex, or the second by a quasi-isomorphic internally K-injective one, does not change the answer.

Uniqueness costs nothing. If $K\to I$ and $K\to I'$ are K-injective replacements, the identity roof gives a unique isomorphism $I\simeq I'$ in the homotopy category compatible with $K$; by the lifting theorem of Section 3.2 a quasi-isomorphism between K-injective complexes is even a homotopy equivalence. This is the correct uniqueness: no canonical cochain-level choice is asserted, and none is needed, since every construction below is applied to a chosen replacement and transported by these comparison isomorphisms.

### 3.5 K-flat replacement of an unbounded complex

The bounded-above criterion of Section 3.3 does not reach the complexes that actually occur. A derived direct image, a totalization, or a derived completion is unbounded in both directions, and derived tensor products of such objects are needed already in Chapter 11. Fortunately the flat side of the theory is completely accessible, and this section proves the replacement statement in full.

Two observations drive the construction. First, K-flatness is stable under filtered colimits, because tensor products commute with colimits and filtered colimits are exact. Second, every complex is the increasing union of its truncations $\tau_{\le n}K$, each of which is bounded above, and a bounded-above complex of flat modules is K-flat by Section 3.3. If those resolutions can be chosen so that they map to one another strictly, and compatibly with the inclusions of the truncations, their colimit is the required replacement.

The compatibility is the only real difficulty, and it is instructive. To lift a map $P_n\to\tau_{\le n+1}K$ through a resolution $P_{n+1}\to\tau_{\le n+1}K$ on the nose, one needs the terms of $P_n$ to have a lifting property against degreewise epimorphisms. Flat sheaves have no such property; sheaves of modules generally have no projective objects at all. The remedy is to construct the tower one level below sheaves, in presheaves of modules, where the free objects attached to the site are projective, and to sheafify afterwards. Sheafification is exact and carries those free presheaves to flat sheaves, so nothing is lost in the descent.

**Colimit lemma.** A filtered colimit of K-flat complexes of $\mathcal O_X$-modules is K-flat, and a filtered colimit of flat modules is flat.

**Proof.** Let $P=\varinjlim_mP_m$ with each $P_m$ K-flat, and let $A$ be acyclic. Tensor products commute with colimits, so $P\otimes A=\varinjlim_m(P_m\otimes A)$ is a filtered colimit of acyclic complexes, hence acyclic because filtered colimits are exact. The statement for modules is the same computation applied to a short exact sequence. $\square$

Write $\operatorname{PMod}(X)$ for the category of presheaves of $\mathcal O_X$-modules. It is abelian with kernels, cokernels, and products formed sectionwise. For an object $U$ of the site, let $\mathcal O_U^{\mathrm{pre}}$ be the presheaf

$$
V\longmapsto\bigoplus_{V\to U}\mathcal O_X(V),
$$

the sum being over morphisms $V\to U$. The Yoneda lemma gives $\operatorname{Hom}_{\operatorname{PMod}}(\mathcal O_U^{\mathrm{pre}},P)=P(U)$, and evaluation at $U$ is exact on presheaves, so $\mathcal O_U^{\mathrm{pre}}$ is projective. For any presheaf $P$ the canonical map

$$
\bigoplus_{U,\,s\in P(U)}\mathcal O_U^{\mathrm{pre}}\longrightarrow P
$$

is surjective sectionwise. Thus $\operatorname{PMod}(X)$ has enough projectives, and every projective occurring below is a direct summand of a direct sum of the $\mathcal O_U^{\mathrm{pre}}$.

Sheafifying these free presheaves gives flat sheaves. Indeed $(\mathcal O_U^{\mathrm{pre}})^{\#}=j_{U!}(\mathcal O_X|_U)$; the tensor product of sheaves is by definition the sheafification of the presheaf tensor product, and sheafifying one factor beforehand does not change the outcome, so $A\otimes(\mathcal O_U^{\mathrm{pre}})^{\#}=(A\otimes^{\mathrm{pre}}\mathcal O_U^{\mathrm{pre}})^{\#}$, while

$$
(A\otimes^{\mathrm{pre}}\mathcal O_U^{\mathrm{pre}})(V)
=\bigoplus_{V\to U}A(V).
$$

A monomorphism of sheaves is injective on sections, because kernels are computed sectionwise; the displayed formula then shows that tensoring it with $\mathcal O_U^{\mathrm{pre}}$ stays injective on sections, and sheafification preserves injectivity. Hence $(\mathcal O_U^{\mathrm{pre}})^{\#}$ is flat, and so is every direct sum and every direct summand of such sheaves.

**Bounded-above criterion, projective form.** A bounded-above complex $P$ of projective objects satisfies $\operatorname{Hom}^\bullet(P,N)\simeq0$ for every acyclic $N$; that is, every map $P\to N$ into an acyclic complex is null-homotopic.

**Proof.** This is the dual of the bounded-below criterion of Section 3.2. Given $f:P\to N$, build a homotopy downward from the highest nonzero degree of $P$. At each stage the equation already solved one degree higher makes the remaining error a map into the cycles of $N$; exactness identifies cycles with boundaries, and projectivity of the term of $P$ lifts the map through the surjection onto those boundaries. $\square$

**Lifting lemma.** Let $P$ be a bounded-above complex of projectives, let $\pi:Y\to Z$ be a degreewise epimorphic quasi-isomorphism, and let $f:P\to Z$ be a chain map. Then there is a chain map $g:P\to Y$ with $\pi g=f$, not merely up to homotopy.

**Proof.** Let $N=\ker\pi$. The short exact sequence $0\to N\to Y\to Z\to0$ and the long exact cohomology sequence show that $N$ is acyclic. Because each term of $P$ is projective, applying $\operatorname{Hom}(P^i,-)$ preserves surjections, so

$$
0\to\operatorname{Hom}^\bullet(P,N)\to\operatorname{Hom}^\bullet(P,Y)
\to\operatorname{Hom}^\bullet(P,Z)\to0
$$

is a degreewise exact sequence of complexes of abelian groups. Choose a degree-zero element $g_0$ of $\operatorname{Hom}^0(P,Y)$ mapping to $f$; it need not be a chain map. Its differential $dg_0$ maps to $df=0$, so $dg_0$ lies in $\operatorname{Hom}^1(P,N)$, where it is a cocycle. By the projective criterion $\operatorname{Hom}^\bullet(P,N)$ is acyclic, so $dg_0=dh$ for some $h$ in $\operatorname{Hom}^0(P,N)$. Then $g=g_0-h$ satisfies $dg=0$, hence is a chain map, and $\pi g=\pi g_0=f$ because $h$ takes values in $N$. $\square$

**K-flat replacement theorem.** Let $(X,\mathcal O_X)$ be a ringed site. Every complex $K$ of $\mathcal O_X$-modules admits a quasi-isomorphism $P\to K$ with $P$ K-flat and termwise flat; moreover $P$ may be taken to be a filtered colimit of bounded-above complexes of flat modules. The same statement, with the same proof and no sheafification, holds for complexes of modules over an ordinary ring.

**Proof.** The truncations $\tau_{\le n}K$ are subcomplexes of $K$, they increase with $n$, and in each degree the chain is eventually equal to $K$; so $K=\varinjlim_n\tau_{\le n}K$, a filtered colimit. Because these truncations are formed using kernels, which are computed sectionwise, they are the same whether formed in sheaves or in presheaves, and the colimit of the presheaves is already a sheaf.

Work first in $\operatorname{PMod}(X)$. Each $\tau_{\le n}K$ is bounded above, so by the projective form of the Cartan--Eilenberg construction in Section 3.4 there is a degreewise epimorphic quasi-isomorphism of presheaves $\pi_n:P_n\to\tau_{\le n}K$ with $P_n$ a bounded-above complex of projective presheaves, whose terms may be taken to be direct sums of the free presheaves $\mathcal O_U^{\mathrm{pre}}$. Choose these resolutions independently, and then connect them: the lifting lemma applied to the composite $P_n\to\tau_{\le n}K\subseteq\tau_{\le n+1}K$ and to the degreewise epimorphic quasi-isomorphism $\pi_{n+1}$ produces $u_n:P_n\to P_{n+1}$ with $\pi_{n+1}u_n$ equal to that composite. Every square commutes exactly, which is what a colimit requires. This is the one step where the passage to presheaves is used, and it is used only for the projectivity of the free objects.

Now sheafify and pass to the colimit. Set $P=\varinjlim_nP_n^{\#}$. Each $P_n^{\#}$ is a bounded-above complex of flat sheaves, hence K-flat by Section 3.3, so $P$ is K-flat and termwise flat by the colimit lemma. Sheafification is exact, so each $\pi_n^{\#}$ is a quasi-isomorphism of complexes of sheaves; filtered colimits in $\operatorname{Mod}(X)$ are exact, hence commute with cohomology, so

$$
P=\varinjlim_nP_n^{\#}\longrightarrow\varinjlim_n\tau_{\le n}K=K
$$

is a quasi-isomorphism. $\square$

Three features of the argument deserve emphasis. No boundedness or finiteness is imposed on $K$: an arbitrary unbounded complex of sheaves of modules has a K-flat replacement. The replacement is termwise flat, but that is a byproduct; termwise flatness alone would not suffice, as the counterexample of Section 3.3 shows, and the substantive content is the K-flatness inherited from the bounded-above stages. Finally, the proof is genuinely constructive in its inputs: free presheaves attached to objects of the site, the horseshoe lemma, and exactness of sheafification and of filtered colimits.

The theorem removes every boundedness restriction from the tensor side of the theory. Derived tensor products in Section 4.2 are defined for arbitrary complexes, associativity and symmetry hold for arbitrary complexes, and the derived completions of Section 11.3 may be formed with unbounded coefficients.

### 3.6 K-injective replacement and homotopy limits

The right-derived side does not admit the argument just given. An unbounded complex is the colimit of the truncations $\tau_{\le n}K$, which is why the flat construction succeeded; it is the inverse limit of the tower $\tau_{\ge-n}K$, and inverse limits, unlike filtered colimits, are not exact in a sheaf category, so nothing guarantees that a limit of resolutions still resolves. Furthermore, no analogue of sheafification produces injective objects with a lifting property. What does survive is a homotopy limit: one resolves each truncation, assembles the resolutions into a single complex by the mapping-cone construction, and asks whether the assembly still computes $K$. The assembly is always K-injective; the question is whether the map from $K$ is a quasi-isomorphism, and the answer is affirmative as soon as countable products are exact.

Two closure properties hold with no hypothesis at all, and they are the reason a homotopy limit is a reasonable thing to form.

**Stability lemma.** Products of K-injective complexes are K-injective. Shifts of K-injective complexes, and cones of morphisms between K-injective complexes, are K-injective.

**Proof.** For a family $(I_j)$ and any complex $A$,

$$
\operatorname{Hom}^n\Bigl(A,\prod_jI_j\Bigr)
=\prod_i\operatorname{Hom}\Bigl(A^i,\prod_jI_j^{i+n}\Bigr)
=\prod_j\operatorname{Hom}^n(A,I_j),
$$

compatibly with differentials, so $\operatorname{Hom}^\bullet(A,\prod_jI_j)=\prod_j\operatorname{Hom}^\bullet(A,I_j)$ as complexes of abelian groups. Products of abelian groups are exact, so a product of acyclic complexes of abelian groups is acyclic; if every $I_j$ is K-injective and $A$ is acyclic, each factor is acyclic and the product is too. Note that no exactness of products in $\mathcal A$ is used: the product being formed is a product of Hom complexes, and those live in abelian groups. For cones, the defining sequence $0\to L\to\operatorname{Cone}(f)\to K[1]\to0$ is degreewise split, so applying $\operatorname{Hom}^\bullet(A,-)$ gives a degreewise split, hence exact, sequence of complexes; if the outer complexes are acyclic, the long exact sequence forces the middle one to be acyclic. Shifts are immediate from the definition. $\square$

**Definition.** Let $\cdots\to I_2\xrightarrow{f_1}I_1\xrightarrow{f_0}I_0$ be a tower of complexes and chain maps. Its **homotopy limit** is

$$
\operatorname{holim}_nI_n
=\operatorname{Cone}\Bigl(\prod_nI_n\xrightarrow{\,1-f\,}\prod_nI_n\Bigr)[-1],
\qquad
(f(x))_n=f_n(x_{n+1}).
$$

This is the same construction that represents a derived inverse limit in Section 6.2. By the stability lemma it is K-injective whenever every $I_n$ is, for any choice of the maps $f_n$ whatsoever.

Spelling out the cone convention of Section 2.2 and the shift, a chain map $K\to\operatorname{holim}_nI_n$ is the same thing as a family of chain maps $u_n:K\to I_n$ together with maps $h_n:K^\bullet\to I_n^{\bullet-1}$ satisfying

$$
dh_n+h_nd=f_nu_{n+1}-u_n.
$$

In words: a compatible family of maps to the tower, compatible not on the nose but through a chosen homotopy in each stage. That is exactly the flexibility the construction below needs, and it is why no strict tower of resolutions has to be built.

**Unbounded K-injective replacement theorem.** Let $\mathcal A$ be a Grothendieck abelian category in which countable products are exact. Then every complex $K$ of $\mathcal A$ admits a quasi-isomorphism $K\to I$ with $I$ K-injective.

**Proof strategy.** Resolve each truncation $\tau_{\ge-n}K$ by the bounded-below theorem of Section 3.4 and form the homotopy limit of the resulting tower. K-injectivity is automatic by the stability lemma. The cohomological comparison is where the hypothesis enters: exactness of products identifies the cohomology of $\prod_nI_n$ with the product of the $H^p(I_n)$, and in each fixed degree that tower is eventually the constant tower on $H^p(K)$, so the map $1-f$ is injective with kernel $H^p(K)$ and is surjective for the elementary reason that a difference of consecutive terms can be solved by partial sums.

**Proof.** For every $n\ge0$ choose a quasi-isomorphism $\tau_{\ge-n}K\to I_n$ with $I_n$ a bounded-below complex of injective objects, and let

$$
\iota_n:K\longrightarrow\tau_{\ge-n}K\longrightarrow I_n
$$

be the composite with the canonical projection onto the truncation. Each $I_n$ is K-injective by Section 3.2.

Next, connect the tower. Because $I_n$ is K-injective, the lifting theorem of Section 3.2 identifies homotopy classes of chain maps into $I_n$ with morphisms into $I_n$ in the derived category. Let $f_n:I_{n+1}\to I_n$ be a chain map representing the derived morphism obtained by inverting the quasi-isomorphism $\tau_{\ge-n-1}K\to I_{n+1}$ and composing with $\tau_{\ge-n-1}K\to\tau_{\ge-n}K\to I_n$. In the derived category $f_n\iota_{n+1}=\iota_n$; since both sides are chain maps from $K$ to the K-injective complex $I_n$, the identification of homotopy classes with derived morphisms makes them homotopic. Choose homotopies $h_n$ with $dh_n+h_nd=f_n\iota_{n+1}-\iota_n$.

Set $I=\operatorname{holim}_nI_n$. It is K-injective by the stability lemma, and the data $(\iota_n)$ and $(h_n)$ define a chain map $\iota:K\to I$ by the description of maps into a homotopy limit given above. It remains to prove that $\iota$ is a quasi-isomorphism.

The defining cone gives a triangle $I\to\prod_nI_n\xrightarrow{1-f}\prod_nI_n$, whose long exact cohomology sequence reads

$$
H^{p-1}\Bigl(\prod_nI_n\Bigr)\xrightarrow{1-f}
H^{p-1}\Bigl(\prod_nI_n\Bigr)\to H^p(I)\to
H^p\Bigl(\prod_nI_n\Bigr)\xrightarrow{1-f}
H^p\Bigl(\prod_nI_n\Bigr).
$$

Exactness of countable products identifies $H^p(\prod_nI_n)$ with $\prod_nH^p(I_n)$, and under this identification $1-f$ is the difference of the identity and the maps induced by the $f_n$. Fix $p$ and set $N=\max(0,-p)$. For $n\ge N$ the projection $K\to\tau_{\ge-n}K$ is an isomorphism on $H^p$, so $H^p(\iota_n)$ is an isomorphism $\theta_n:H^p(K)\to H^p(I_n)$; for $n<N$ we have $H^p(I_n)=H^p(\tau_{\ge-n}K)=0$. Applying $H^p$ to $f_n\iota_{n+1}\simeq\iota_n$ gives $H^p(f_n)\theta_{n+1}=\theta_n$, so the $\theta_n$ identify the part of the tower with $n\ge N$ with the constant tower on $H^p(K)$ with identity transition maps.

Under that identification, $1-f$ becomes $(x_n)\mapsto(x_n-x_{n+1})$ on $\prod_{n\ge N}H^p(K)$, together with the zero tower below $N$. Its kernel consists of the constant families, so the kernel is $H^p(K)$, embedded by $(\theta_n)$. It is surjective, because the morphism $s$ defined by $s(y)_n=0$ for $n\le N$ and

$$
s(y)_n=-(y_N+y_{N+1}+\cdots+y_{n-1})\qquad(n>N)
$$

has each component a finite sum of projections, hence is a genuine morphism, and satisfies $s(y)_n-s(y)_{n+1}=y_n$ for all $n\ge N$, while below $N$ there is nothing to solve. Thus $1-f$ is surjective on $H^{p}$ and on $H^{p-1}$, with kernel $H^p(K)$ in degree $p$.

The long exact sequence now degenerates: surjectivity in degree $p-1$ kills the left-hand contribution, so $H^p(I)\to\prod_nH^p(I_n)$ is injective with image the kernel of $1-f$, that is, an isomorphism onto $H^p(K)$. The composite of $H^p(\iota)$ with this isomorphism is the family $(H^p(\iota_n))=(\theta_n)$, which is precisely the embedding of $H^p(K)$ as the constant families. Hence $H^p(\iota)$ is an isomorphism for every $p$. $\square$

**Corollary.** In any Grothendieck abelian category, every complex whose cohomology vanishes in all sufficiently negative degrees admits a K-injective replacement, by the bounded-below theorem of Section 3.4. In a Grothendieck abelian category with exact countable products, every complex does.

Which categories satisfy the product hypothesis is a concrete question. Modules over a ring do: products are formed elementwise and a product of surjections of modules is surjective. So do categories of inverse systems of modules, whose products are formed levelwise, and more generally any abelian category whose products are computed by an exact formula. Sheaf categories generally do not. Products of sheaves are computed sectionwise, but epimorphisms of sheaves are only locally surjective, and an infinite family of local surjectivity witnesses need not admit a common refinement; the product of infinitely many epimorphisms of sheaves can therefore fail to be an epimorphism. The tower argument above then breaks at exactly one point, the identification of $H^p(\prod_nI_n)$ with $\prod_nH^p(I_n)$, and nothing in the construction repairs it.

The consequences for the rest of the book are stated once here and respected throughout. Right-derived operations on an arithmetic sheaf category are constructed on complexes with bounded-below cohomology; that is the classical range, it contains every complex to which Chapters 7 through 12 apply a spectral sequence, and within it the replacements are the unconditional ones of Section 3.4. Over a coefficient ring, the setting of Sections 4.5 and 11.3, the theorem above applies and right-derived operations are available on all of the derived category. The derived tensor product carries no restriction at all, by Section 3.5. Whenever a statement below concerns unbounded complexes, it says which of these three situations it is in.

### 3.7 Derived functors and acyclicity criteria

Let $F:\mathcal A\to\mathcal B$ be additive. If applying $F$ to quasi-isomorphisms between K-injective complexes again gives quasi-isomorphisms, define

$$
RF(K)=F(I),\qquad K\xrightarrow{\sim}I\text{ K-injective}.
$$

The lifting theorem gives functoriality and uniqueness. For a left exact functor, it is enough that $F$ send acyclic K-injective complexes to acyclic complexes.

The definition applies exactly where a replacement was produced. By Section 3.6 that means: on complexes with bounded-below cohomology in any Grothendieck abelian category, hence on $D^+(\mathcal A)$ always; and on arbitrary complexes, hence on $D(\mathcal A)$, when countable products in $\mathcal A$ are exact. We therefore construct right-derived operations on sheaf categories over $D^+$ and on module categories over all of $D$, and every statement below records which range it uses. Nothing in this convention affects left-derived operations built from K-flat replacements, which Section 3.5 supplies without restriction.

An object $A$ is **$F$-acyclic** if $R^nF(A)=0$ for $n>0$. A bounded-below resolution $A\to C^\bullet$ by $F$-acyclic objects computes $RF(A)$. To prove this, resolve each $C^q$ injectively. The resulting double complex has one spectral sequence with only its zeroth derived row and another computing the injective resolution of $A$; both identify the same total complex. This acyclic-resolution lemma is the workhorse behind flasque, soft, and Cech resolutions.

### 3.8 A replacement checklist

Three assertions are easily confused. A termwise injective resolution computes a right-derived functor for a bounded-below complex; the lower bound starts the homotopy induction. A K-injective replacement computes it for an unbounded complex; its terms need not themselves be injective if the K-injective property is known otherwise, as the homotopy limits of Section 3.6 illustrate. An $F$-acyclic resolution computes one particular derived functor and need not be K-injective.

On the tensor side, a bounded-above complex of flats is K-flat, and by Section 3.5 every complex, however unbounded, has a K-flat replacement. A general termwise flat unbounded complex is nevertheless not itself K-flat; termwise flatness is a property of the terms, K-flatness a property of the complex, and only the second computes a derived tensor product. If a complex is perfect—locally quasi-isomorphic to a bounded complex of finite projective modules—it is K-flat and dualizable. Perfect complexes are consequently safe coefficients for projection formulas and base change.

Finally, replacing the wrong variable can invalidate a calculation. For $K\otimes^LL$, replace at least one variable K-flatly. For global $R\operatorname{Hom}(K,L)$, replace $L$ K-injectively; in a category with enough projectives one may instead replace $K$ by a bounded-above complex of projectives. For sheaf-valued $R\mathcal Hom$, the replacement of the second variable must be internally K-injective in the sense of Section 3.4; a bounded-below complex of injectives is such a replacement, and so is $\mathcal Hom(P,I)$ for $P$ K-flat, as Section 4.4 uses. The local condition in that definition avoids pretending that a statement about global morphisms automatically controls every local object.

## 4. The three derived operations

### 4.1 Derived global sections

For a site $X$, global sections are

$$
\Gamma(X,\mathcal F)=\operatorname{Hom}(\mathcal O_X,\mathcal F)
$$

in the module case. They are left exact because limits of sheaves are computed sectionwise. Choose a K-injective replacement $\mathcal F\to I$ and set

$$
R\Gamma(X,\mathcal F)=\Gamma(X,I),\qquad
H^n(X,\mathcal F)=H^nR\Gamma(X,\mathcal F).
$$

For a morphism of sites $f:X\to Y$, direct image $f_*$ is also left exact, and

$$
Rf_*\mathcal F=f_*I,\qquad
R\Gamma(X,\mathcal F)\simeq R\Gamma(Y,Rf_*\mathcal F)
$$

under the acyclicity condition proved in Chapter 8.

A single sheaf sits in degree zero, so the replacement here is the bounded-below one of Section 3.4, and the same definition applies verbatim to any complex $K$ of sheaves whose cohomology vanishes in all sufficiently negative degrees: replace $K$ by $\tau_{\ge n_0}K$ and resolve. This is the range in which $R\Gamma$ and $Rf_*$ are used throughout the book. Over a coefficient ring, where countable products are exact, Section 3.6 extends both operations to arbitrary unbounded complexes; on a general sheaf category the unbounded extension is not claimed, and no statement below uses it.

If $X$ has a final object in its site and coverings split, global sections are exact and higher cohomology vanishes. At the opposite extreme, nontrivial gluings create higher cohomology; it measures failure of compatible local sections to glue globally.

### 4.2 Derived tensor product

Tensor product is right exact and does not preserve quasi-isomorphisms in either variable. Choose a K-flat replacement $P\to K$, which exists for every complex by Section 3.5 with no boundedness restriction, and define

$$
K\otimes_{\mathcal O_X}^{L}L=P\otimes_{\mathcal O_X}L.
$$

If both variables are replaced, the two answers agree: factor the comparison through $P\otimes Q$ and use K-flatness to see that both induced maps are quasi-isomorphisms. The cohomology sheaves of $A\otimes^L B$ recover Tor when $A,B$ lie in degree zero:

$$
H^{-n}(A\otimes^L B)=\operatorname{Tor}_n(A,B).
$$

The sign is caused by the cohomological placement of a flat resolution in nonpositive degrees.

Associativity, symmetry, and the unit isomorphism descend from complexes because K-flat replacements preserve the quasi-isomorphisms used in the coherence diagrams. Thus derived tensor is a symmetric monoidal operation, not merely a collection of objects defined up to unrelated isomorphism.

### 4.3 Derived internal Hom

For complexes $K,L$, the internal Hom complex is

$$
\mathcal Hom^n(K,L)=\prod_i\mathcal Hom(K^i,L^{i+n}),
$$

with differential $d(f)=d_Lf-(-1)^nfd_K$. For global derived Hom, a K-injective replacement of the second variable suffices. The sheaf-valued operation needs the internal notion of Section 3.4, and the criterion proved there supplies it whenever the second variable has bounded-below cohomology: choose a quasi-isomorphism $L\to I$ with $I$ a bounded-below complex of injective $\mathcal O_X$-modules, and put

$$
R\mathcal Hom(K,L)=\mathcal Hom(K,I).
$$

Both variables behave correctly. If $K\to K'$ is a quasi-isomorphism with cone $C$, then $C$ is acyclic, so $\mathcal Hom(C,I)$ is acyclic by the internal criterion and $\mathcal Hom(K',I)\to\mathcal Hom(K,I)$ is a quasi-isomorphism. If $J$ is any internally K-injective complex quasi-isomorphic to $L$, then a chain map $J\to I$ inducing the comparison exists because $I$ is K-injective, its cone is acyclic and internally K-injective, and the last clause of the criterion makes $\mathcal Hom(K,J)\to\mathcal Hom(K,I)$ a quasi-isomorphism. So $R\mathcal Hom(K,L)$ may be computed from any internally K-injective representative of the second variable, a freedom used in Section 4.4. Global derived Hom is

$$
R\operatorname{Hom}_X(K,L)=R\Gamma(X,R\mathcal Hom(K,L)).
$$

For modules in degree zero,

$$
H^nR\operatorname{Hom}_X(A,B)=\operatorname{Ext}^n_X(A,B).
$$

Negative Ext groups vanish in this case, but they need not vanish for general shifted complexes.

### 4.4 Projection and tensor-Hom formulas

The underived adjunction

$$
\mathcal Hom(K\otimes L,M)\cong
\mathcal Hom(K,\mathcal Hom(L,M))
$$

passes to derived objects once the two variables that need replacing are replaced correctly. Let $K$ and $L$ be arbitrary complexes and let $M$ have bounded-below cohomology. Choose a K-flat $P\to L$ by Section 3.5 and a bounded-below complex of injectives $M\to I$ by Section 3.4. The displayed adjunction, applied termwise and assembled with the usual signs, is an isomorphism of complexes

$$
\mathcal Hom(K\otimes P,I)\cong\mathcal Hom(K,\mathcal Hom(P,I)).
$$

The left side computes $R\mathcal Hom(K\otimes^LL,M)$, since $K\otimes P$ represents $K\otimes^LL$ and $I$ is internally K-injective. The right side computes $R\mathcal Hom(K,R\mathcal Hom(L,M))$: the complex $\mathcal Hom(P,I)$ represents $R\mathcal Hom(L,M)$, and it is itself internally K-injective, because restriction to an object $U$ carries it to $\mathcal Hom(P|_U,I|_U)$ and, for acyclic $A$ on $X/U$,

$$
\operatorname{Hom}^\bullet(A,\mathcal Hom(P|_U,I|_U))
\cong\operatorname{Hom}^\bullet(A\otimes P|_U,I|_U)
$$

is acyclic: $P|_U$ is K-flat because K-flatness restricts, as recorded in Section 3.4, and $I|_U$ is K-injective by the internal criterion. By the computation freedom established in Section 4.3 the right side therefore computes the iterated derived Hom, and

$$
R\mathcal Hom(K\otimes^L L,M)
\simeq R\mathcal Hom(K,R\mathcal Hom(L,M))
$$

for arbitrary $K$ and $L$ and for $M$ with bounded-below cohomology. The restriction on $M$ is the only one, and it is the same restriction under which the right-hand side was defined at all.

For $f:X\to Y$ there is always a derived projection morphism

$$
Rf_*K\otimes^L M\longrightarrow
Rf_*(K\otimes^L Lf^*M).
$$

It is an isomorphism, for example, if $M$ is represented by a bounded complex of finite locally free modules. Indeed, reduce through the finite filtration to one finite locally free module $E$. On any object of the site over which $E$ is free of finite rank, the projection morphism is the evident isomorphism between two copies of the same finite direct sum of $f_*K$. Since being an isomorphism of sheaves is local, the underived projection map is an isomorphism for $E$. The same local argument applied to an acyclic resolution shows that tensoring by $f^*E$ preserves the acyclicity needed to compute $Rf_*$. Exact triangles then rebuild the bounded complex. Without finite presentation or a suitable perfectness hypothesis, direct image need not commute with tensor, so the formula is not unconditional.

### 4.5 Tor, Ext, and change of rings

Let $R\to S$ be a homomorphism of commutative rings. Restriction of scalars is exact, while extension of scalars has left-derived functor $S\otimes_R^L-$. If $M$ is an $S$-module and $N$ an $R$-module, derived adjunction gives

$$
R\operatorname{Hom}_S(S\otimes_R^LN,M)
\simeq R\operatorname{Hom}_R(N,M).
$$

To prove it, choose a projective resolution of $N$. Ordinary tensor-Hom adjunction holds degree by degree, and its signs agree with the differential of the Hom complex.

Resolving the two tensor operations successively yields the change-of-rings sequence

$$
E^2_{p,q}=\operatorname{Tor}^{S}_p
\bigl(\operatorname{Tor}^{R}_q(S,N),M\bigr)
\Longrightarrow \operatorname{Tor}^{R}_{p+q}(N,M),
$$

where $N$ is an $R$-module and $M$ is an $S$-module, regarded also as an $R$-module. To construct it, resolve $N$ by projective $R$-modules. After extension to $S$ these remain projective $S$-modules, so they are acyclic for $-\otimes_S M$. A Cartan--Eilenberg resolution and the two filtrations of its total complex give the displayed $E^2$ page and the target $N\otimes_R^L M$. This also proves strong convergence in the first-quadrant indexing. Its Ext counterpart has the schematic form

$$
E_2^{p,q}=R^pF(R^qG(N))\Longrightarrow R^{p+q}(F\circ G)(N),
$$

for the two Hom functors supplied by restriction and coinduction. Writing this schematic form is safer than suppressing bimodule sides: Tor is covariant in the relevant variables, Ext is contravariant in its first variable, and an incorrect side changes the statement.

## 5. Filtered complexes and spectral objects

### 5.1 Filtrations and associated graded complexes

A filtered complex $(K,F)$ has subcomplexes

$$
\cdots\supseteq F^pK\supseteq F^{p+1}K\supseteq\cdots.
$$

Set $\operatorname{gr}^p_FK=F^pK/F^{p+1}K$. The filtration is **exhaustive** if $\bigcup_pF^pK=K$, **separated** if $\bigcap_pF^pK=0$, and finite in degree $n$ if only finitely many $\operatorname{gr}^pK^n$ are nonzero.

The first page attached to a decreasing filtered cochain complex is

$$
E_0^{p,q}=\operatorname{gr}^p_FK^{p+q},\qquad
E_1^{p,q}=H^{p+q}(\operatorname{gr}^p_FK).
$$

The differential on $E_0$ has bidegree $(0,1)$. A class surviving to $E_r$ is represented by $x\in F^pK^{p+q}$ with $dx\in F^{p+r}K$. Its $r$th differential is the class of $dx$ in bidegree $(p+r,q-r+1)$. This representative description proves both the bidegree and $d_r^2=0$.

### 5.2 Exact couples

The mechanism behind those formulas is an exact couple. From

$$
0\longrightarrow F^{p+1}K\longrightarrow F^pK
\longrightarrow\operatorname{gr}^p_FK\longrightarrow0
$$

take cohomology and sum over $p$. With

$$
D_1^{p,q}=H^{p+q}(F^pK),\qquad
E_1^{p,q}=H^{p+q}(\operatorname{gr}^p_FK),
$$

the long exact sequences give maps $i:D\to D$, $j:D\to E$, and $k:E\to D$ forming an exact triangle

$$
D\xrightarrow{i}D\xrightarrow{j}E\xrightarrow{k}D.
$$

Then $d=jk$ squares to zero because $kj=0$. Derive a new couple by replacing $D$ with $iD$ and $E$ with $\ker d/\operatorname{im}d$. Exactness of the derived couple follows directly: if a class in $iD$ maps to zero, lift it to $D$, use exactness in the original couple, and modify the lift by an element from $E$; the quotient by boundaries records precisely the ambiguity. Iteration constructs all pages.

### 5.3 Pages and differentials

For $r\ge0$, put $n=p+q$ and define the group of $r$-cycles at filtration $p$ by

$$
Z_r^{p,q}=F^pK^n\cap d^{-1}(F^{p+r}K^{n+1}).
$$

Thus $Z_0^{p,q}=F^pK^n$. For $r\ge1$ the page is the quotient

$$
E_r^{p,q}=
\frac{Z_r^{p,q}}
{Z_{r-1}^{p+1,q-1}+dZ_{r-1}^{p-r+1,q+r-2}}.
$$

Both denominator terms lie in $Z_r^{p,q}$: the first consists of deeper-filtration $r$-cycles, while an element $y$ of the second satisfies $y\in F^{p-r+1}K^{n-1}$ and $dy\in F^pK^n$. Equivalently, $E_r^{p,q}$ consists of representatives in $F^pK^n$ closed modulo $F^{p+r}$, modulo the deeper representatives and boundaries that themselves satisfy the required filtration condition. The representative formula gives

$$
E_{r+1}^{p,q}\cong H(E_r^{p,q},d_r).
$$

For large $r$, if the filtration is finite in total degrees $n-1$, $n$, and $n+1$, the conditions stabilize. The stable group is denoted $E_\infty^{p,q}$.

### 5.4 The derived viewpoint

A **spectral object** in a triangulated category is a tower $(X^p)$ with maps $X^{p+1}\to X^p$ and distinguished triangles

$$
X^{p+1}\longrightarrow X^p\longrightarrow G^p\longrightarrow X^{p+1}[1].
$$

Applying a cohomological functor gives an exact couple and hence a spectral sequence. A filtered complex produces such a tower with $X^p=F^pK$ and $G^p=\operatorname{gr}^pK$. Conversely, a finite spectral object can be realized inductively by extensions, though not canonically by literal subcomplexes.

This viewpoint has two advantages. First, it is invariant under filtered quasi-isomorphism. Second, it lets truncation towers, derived direct images, and the filtrations produced by derived completion enter the same machine even when no convenient pointwise filtration has been chosen.

### 5.5 Filtrations from arithmetic geometry

Three filtrations recur. The truncation filtration of a derived direct image has graded pieces $R^qf_*K[-q]$ and produces Leray after applying global sections. The filtration of a double complex by columns separates one derived operation from another. Extend an ideal-adic filtration to all integers by taking $F^pK=K$ for $p\le0$; for $p\ge0$ it has

$$
F^pK=I^pK,\qquad \operatorname{gr}^p_FK=I^pK/I^{p+1}K,
$$

and compares integral information with simpler residue-level layers.

For example, if $I=(\pi)$ and multiplication by $\pi$ is injective on every term of $K$, then $\operatorname{gr}^pK$ is identified, after multiplication by $\pi^p$, with $K/\pi K$. The associated sequence begins with repeated copies of the mod-$\pi$ cohomology. If $K$ has $\pi$-torsion, that identification fails: multiplication by $\pi^p$ has a kernel, and the graded pieces remember torsion of different orders. This elementary counterexample explains why flatness over the coefficient ring is routinely paired with filtered comparison.

A filtration may also arise geometrically from a closed-open decomposition. If $i:Z\hookrightarrow X$ and $j:U\hookrightarrow X$ are complementary, the localization triangle

$$
R\underline{\Gamma}_Z(K)\longrightarrow K\longrightarrow Rj_*j^*K
\longrightarrow R\underline{\Gamma}_Z(K)[1]
$$

is a two-step spectral object, where $R\underline{\Gamma}_Z$ is the sheaf-valued derived functor of sections supported on $Z$. Its long exact sequence is the simplest spectral sequence associated to a stratification. Iterating over finitely many strata produces a finite filtration whose graded layers are cohomology sheaves supported on individual strata; applying global sections then gives the corresponding groups with support.

## 6. Convergence, filtrations, and edge maps

### 6.1 Strong convergence

Pages alone do not identify a target. Convergence requires a relationship between the filtration on the complex and the induced filtration on cohomology. Define

$$
F^pH^n(K)=\operatorname{im}\bigl(H^n(F^pK)\to H^n(K)\bigr).
$$

The desired conclusion is

$$
E_\infty^{p,q}\cong
\operatorname{gr}^p_FH^{p+q}(K).
$$

**Finite-filtration convergence theorem.** Suppose that for every $n$ there are integers $a(n)\le b(n)$ such that $F^{a(n)}K^n=K^n$ and $F^{b(n)}K^n=0$. Then the spectral sequence of $(K,F)$ stabilizes in each bidegree and converges strongly to $H^*(K)$ with the filtration above.

**Proof.** Fix total degree $n$. Only finitely many filtration indices occur in degrees $n-1,n,n+1$. For sufficiently large $r$, the condition $dx\in F^{p+r}$ becomes $dx=0$, while the permitted source $F^{p-r+1}$ for boundaries becomes all of $K^{n-1}$. The stable representatives are therefore cocycles in $F^pK^n$, modulo cocycles in $F^{p+1}K^n$ and boundaries in $K^n$ that lie in $F^pK^n$. This quotient is exactly

$$
F^pH^n(K)/F^{p+1}H^n(K).
$$

The induced filtration is finite, hence exhaustive, separated, and complete. These facts are what the word “strongly” records. $\square$

First-quadrant and bounded-strip spectral sequences satisfy the hypothesis after totalization: each diagonal intersects the support in finitely many positions. A bounded-below double complex need not be first quadrant, but it still converges if each total diagonal has finitely many nonzero terms.

### 6.2 Conditional convergence and its failures

For an infinite decreasing filtration, completeness means

$$
K\xrightarrow{\sim}R\varprojlim_p K/F^pK
$$

in the derived sense, not merely degreewise. The obstruction is a derived inverse limit. For a countable tower $A_p$ of complexes of abelian groups or modules, there is a short exact Milnor sequence

$$
0\to R^1\varprojlim H^{n-1}(A_p)\to H^n(R\varprojlim A_p)
\to\varprojlim H^n(A_p)\to0.
$$

More generally the same statement holds in an abelian category with exact countable products; without that hypothesis, higher derived functors of product can add further terms. Under the stated hypothesis, the sequence follows by representing the derived limit as the cone, shifted by $-1$, of

$$
\prod_pA_p\xrightarrow{1-\mathrm{shift}}\prod_pA_p
$$

and taking its long exact sequence. Exactness of products identifies the cohomology of the product complex with the product of the cohomology groups. If the transition maps on cohomology are eventually surjective, the first derived limit vanishes: recursively choose corrections lifting the discrepancy at each stage. More generally stabilization of the images is the Mittag--Leffler criterion and has the same consequence for towers of abelian groups.

Thus a complete, exhaustive filtration with suitable derived-limit vanishing gives strong convergence. Without completeness, all pages can vanish while the target does not. One model is an infinitely deep filtration with $F^pK=K$ for every $p$: its associated graded object is zero, yet $H^*(K)$ may be nonzero. Without separatedness, the stable graded pieces see only $H/\bigcap_pF^pH$. Without exhaustive convergence, they see only the union of the filtered pieces. These are structural failures, not indexing nuisances.

### 6.3 Edge maps and five- and seven-term sequences

In a first-quadrant cohomological sequence, the filtration on $H^n$ begins

$$
0=F^{n+1}H^n\subseteq F^nH^n\subseteq\cdots
\subseteq F^0H^n=H^n.
$$

The horizontal edge map is $H^n\to E_2^{0,n}$, obtained by quotienting to $E_\infty^{0,n}$ and including the stable cycles into $E_2^{0,n}$. The vertical edge map is $E_2^{n,0}\to H^n$, obtained by projecting to $E_\infty^{n,0}$ and identifying it with $F^nH^n$. These descriptions determine direction and eliminate a common ambiguity.

Low degrees give the five-term exact sequence

$$
0\to E_2^{1,0}\to H^1\to E_2^{0,1}
\xrightarrow{d_2}E_2^{2,0}\to H^2.
$$

To prove exactness, note that $E_\infty^{1,0}=E_2^{1,0}$ and
$E_\infty^{0,1}=\ker(d_2:E_2^{0,1}\to E_2^{2,0})$; the two-step filtration on $H^1$ supplies the first three maps. In total degree two, the quotient of $E_2^{2,0}$ by incoming $d_2$ is $E_\infty^{2,0}$ and injects into $H^2$. Continuing the same filtration argument yields

$$
E_2^{0,1}\to E_2^{2,0}\to
\ker(H^2\to E_2^{0,2})\to E_2^{1,1}
\xrightarrow{d_2}E_2^{3,0},
$$

which is often called the seven-term refinement when joined to the first three terms. No map here requires a choice of splitting.

### 6.4 Comparison theorems

A morphism of filtered complexes induces maps on every page and on the filtered abutments.

**Spectral comparison theorem.** Let $f:(K,F)\to(L,F)$ be a morphism of filtered complexes whose spectral sequences converge strongly. Assume in addition that the abutment filtrations are finite in every degree, or that they are complete and separated and passage to the relevant inverse limits is exact. If $f_r:E_r(K)\to E_r(L)$ is an isomorphism for some page $r$, then $H^n(f)$ is an isomorphism for every $n$.

**Proof.** Taking homology page by page shows that every later $f_s$, hence $f_\infty$, is an isomorphism. Thus $H^n(f)$ induces an isomorphism on each associated graded piece. For a finite filtration, induction on its length and the short exact sequences

$$
0\to F^{p+1}H^n\to F^pH^n\to\operatorname{gr}^pH^n\to0
$$

show that $H^n(f)$ is an isomorphism. For complete infinite filtrations the same conclusion follows by passage to inverse limits, provided the relevant first derived limits vanish. $\square$

A useful range form has a precise one-degree buffer. If $f_r^{p,q}$ is an isomorphism for $p+q\le n$ and a monomorphism for $p+q=n+1$, then it has the same property on every later page: a differential raises total degree by one, so the isomorphism range controls boundaries entering it and the monomorphism one degree higher controls kernels leaving it. Under the same reconstruction hypotheses as in the theorem, $H^m(f)$ is an isomorphism for $m\le n$ and a monomorphism for $m=n+1$.

### 6.5 Degeneration is not splitting

A sequence **degenerates at $E_r$** if every $d_s$ for $s\ge r$ vanishes, so $E_r=E_\infty$. Support often forces this. A sequence contained in one row or one column degenerates immediately. If it occupies two rows $q=0,1$, then only $d_2$ can be nonzero; every $d_r$ with $r\ge3$ changes $q$ beyond the support. More generally, weights, parity, or incompatible group characters can force all possible differentials to vanish once those extra structures are known to be respected.

Degeneration produces a finite filtration with known graded pieces. It produces a direct-sum decomposition only if those extensions split, and a canonical decomposition only if the splittings are canonical and compatible. Over a field every short exact sequence of vector spaces splits, but usually not naturally. Over $\mathbf Z$, the filtration

$$
0\subset 2\mathbf Z/4\mathbf Z\subset\mathbf Z/4\mathbf Z
$$

has two graded pieces isomorphic to $\mathbf Z/2\mathbf Z$, yet its middle object is not their direct sum. This is exactly the kind of hidden extension retained by integral arithmetic cohomology.

## 7. Double complexes and hypercohomology

### 7.1 Totalization and signs

A double complex $C^{p,q}$ has $d_h:C^{p,q}\to C^{p+1,q}$ and $d_v:C^{p,q}\to C^{p,q+1}$. We take commuting raw differentials and define the total differential by

$$
d(x)=d_hx+(-1)^p d_vx,\qquad x\in C^{p,q}.
$$

The cross terms cancel, so $d^2=0$. One could instead require anticommuting differentials and omit the sign; mixing the conventions is fatal.

For a first-quadrant double complex set

$$
\operatorname{Tot}^nC=\bigoplus_{p+q=n}C^{p,q}.
$$

For an unbounded double complex, direct-sum and product totalizations can differ. We use direct sums when only finitely many terms lie on each diagonal or when filtered colimits justify them, and products for right-derived constructions built from unbounded injective columns. Any theorem involving an unbounded totalization will state which one is used.

### 7.2 The two spectral sequences

Filter $\operatorname{Tot}C$ by columns. The associated graded differential is vertical, giving

$$
{}'E_1^{p,q}=H_v^q(C^{p,\bullet}),\qquad
{}'E_2^{p,q}=H_h^pH_v^q(C).
$$

Filtering by rows gives

$$
{}''E_1^{p,q}=H_h^p(C^{\bullet,q}),\qquad
{}''E_2^{p,q}=H_v^qH_h^p(C).
$$

If the double complex is first quadrant, both converge strongly to $H^{p+q}(\operatorname{Tot}C)$. These two views are a proof technique: choose one filtration to identify the total object and the other to expose the desired $E_2$ page.

For example, if the horizontal cohomology of every row with $q\ne0$ vanishes, the row sequence is supported on $q=0$ and gives

$$
H^n(\operatorname{Tot}C)\cong H_h^n(C^{\bullet,0}).
$$

Dually, if the vertical cohomology vanishes away from degree zero, the column sequence identifies total cohomology with the cohomology of the horizontal complex $p\mapsto H_v^0(C^{p,\bullet})$. The other filtration can still compute that same target through nontrivial higher groups.

### 7.3 Hypercohomology

For a complex of sheaves $K$, its hypercohomology is

$$
\mathbb H^n(X,K)=H^nR\Gamma(X,K).
$$

Apply $R\Gamma$ to the truncation tower of $K$. Its graded layer in degree $q$ is $\mathcal H^q(K)[-q]$, so the spectral-object construction gives the **hypercohomology spectral sequence**

$$
E_2^{p,q}=H^p(X,\mathcal H^q(K))
\Longrightarrow\mathbb H^{p+q}(X,K).
$$

It converges strongly whenever $K$ is bounded below: after translating the lower bound, $p,q\ge0$, so every total diagonal is finite. A $K$ with cohomology unbounded below lies outside the range in which $R\Gamma$ was constructed for a sheaf category, by Section 3.6; where the operation is available, namely over a coefficient ring with exact countable products, convergence additionally requires a finite-cohomological-dimension bound making each relevant diagonal finite, or completeness of the truncation tower together with the derived-limit vanishing of Section 6.2.

There is a second sequence. For $K$ bounded below, resolve every $K^q$ by $\Gamma$-acyclic sheaves and take the resulting first-quadrant double complex. Filtering in the other direction gives

$$
E_1^{p,q}=H^q(X,K^p)\Longrightarrow\mathbb H^{p+q}(X,K),
$$

with $d_1$ induced by the differential of $K$. It is particularly effective when the terms, rather than the cohomology sheaves, have known cohomology.

If $K$ is concentrated in degree zero, both constructions recover ordinary sheaf cohomology. If every $K^p$ is $\Gamma$-acyclic, the second sequence has only row $q=0$, proving that $\Gamma(X,K)$ itself computes hypercohomology.

### 7.4 Acyclic resolutions and Cech models

Let $\mathfrak U=(U_i\to X)$ be a finite covering for which finite fiber products exist. The augmented Cech complex of a sheaf $\mathcal F$ has

$$
\check C^p(\mathfrak U,\mathcal F)=
\prod_{i_0,\ldots,i_p}
\mathcal F(U_{i_0}\times_X\cdots\times_XU_{i_p}),
$$

with alternating restriction maps. Suppose the sheafified augmented Cech complex is exact and every finite intersection $U_{i_0}\times_X\cdots\times_XU_{i_p}$ is acyclic for $\mathcal F$. Then this one cover computes global cohomology. Indeed, apply Cech cochains to an injective resolution of $\mathcal F$. In one direction the resolution computes the cohomology of each intersection, so the acyclicity assumption leaves only the Cech complex of $\mathcal F$. In the other direction the sheafified Cech augmentation is exact; locally a chosen member of the cover supplies a contracting homotopy. Its terms are acyclic for global sections because they are products of direct images from the acyclic intersections. The two strongly convergent spectral sequences therefore identify Cech and derived cohomology.

The acyclicity hypothesis cannot be omitted. A cover may have intersections with higher cohomology; then Cech cohomology for that single cover sees only the first stage of a hypercover calculation and can differ from sheaf cohomology.

### 7.5 Two model calculations

Let $K=[\mathcal F\xrightarrow u\mathcal G]$ occupy degrees $0,1$. Its only cohomology sheaves are $\ker u$ in degree zero and $\operatorname{coker}u$ in degree one. Hypercohomology gives

$$
E_2^{p,0}=H^p(X,\ker u),\qquad
E_2^{p,1}=H^p(X,\operatorname{coker}u).
$$

Only $d_2^{p,1}:E_2^{p,1}\to E_2^{p+2,0}$ can be nonzero. In low degree,

$$
0\to H^1(X,\ker u)\to\mathbb H^1(X,K)
\to H^0(X,\operatorname{coker}u)
\xrightarrow{d_2}H^2(X,\ker u).
$$

The last map is the obstruction to lifting a global cokernel section to a hypercohomology class. It is the two-extension class of $K$: lift the section locally to $\mathcal G$, take its discrepancy in $\operatorname{im}u$, lift again through $\mathcal F$, and the resulting double overlap cocycle lies in $\ker u$.

For a second calculation, let $0\to\mathcal F\to\mathcal I^0\to\mathcal I^1\to0$ be an acyclic resolution of length one. The termwise-cohomology sequence has only row zero, so

$$
H^n(X,\mathcal F)=H^n\bigl(\Gamma(X,\mathcal I^0)\to
\Gamma(X,\mathcal I^1)\bigr).
$$

In particular $H^n(X,\mathcal F)=0$ for $n>1$. The conclusion depends both on the length and on acyclicity; a short resolution by arbitrary sheaves gives no such bound.

## 8. The Leray spectral sequence

### 8.1 Construction

Let $f:X\to Y$ be a morphism of sites and $\mathcal F$ a sheaf, or a bounded-below complex of sheaves. Since

$$
\Gamma(Y,f_*\mathcal F)=\Gamma(X,\mathcal F),
$$

one expects the derived composite to be computed in two stages.

**Composition theorem.** Let $G:\mathcal A\to\mathcal B$ and $F:\mathcal B\to\mathcal C$ be left exact functors between abelian categories with enough injectives. Suppose $G$ sends injective objects to $F$-acyclic objects. Then there is a functorial first-quadrant spectral sequence

$$
E_2^{p,q}=R^pF(R^qG(A))\Longrightarrow R^{p+q}(F\circ G)(A).
$$

**Proof.** Choose an injective resolution $A\to I^\bullet$ and a Cartan--Eilenberg injective resolution of the complex $G(I^\bullet)$. After applying $F$, filter its first-quadrant total complex in the two directions. One filtration first takes cohomology of $G(I^\bullet)$, producing $R^qG(A)$, and then derives $F$, producing $R^pF(R^qG(A))$. For the other filtration, each object $G(I^q)$ is $F$-acyclic, so the resolution direction has cohomology only in degree zero. It therefore collapses to the complex $F(G(I^\bullet))$. Because $I^\bullet$ is an injective resolution, this complex computes $R(F\circ G)(A)$. First-quadrant convergence identifies the common abutment. Comparison of resolutions and homotopy uniqueness of lifts prove functoriality. $\square$

For $G=f_*$ and $F=\Gamma(Y,-)$, the required condition is that $f_*I$ be $\Gamma(Y,-)$-acyclic for every injective $I$ on $X$. It holds, in particular, when the left adjoint $f^*$ is exact: adjunction then shows that $f_*$ preserves injectives. It also holds for ordinary sheaves on spaces because injectives are flasque, direct image preserves flasqueness, and flasque sheaves are acyclic. For a general ringed-site morphism we retain the acyclicity condition rather than silently asserting exactness of module pullback. Under it we obtain

$$
E_2^{p,q}=H^p(Y,R^qf_*\mathcal F)
\Longrightarrow H^{p+q}(X,\mathcal F).
$$

For a complex $K$, the derived statement is

$$
E_2^{p,q}=H^p(Y,\mathcal H^q(Rf_*K))
\Longrightarrow\mathbb H^{p+q}(X,K),
$$

under the same boundedness conditions as hypercohomology.

### 8.2 Functoriality and edge maps

A map $\mathcal F\to\mathcal G$ induces a morphism of Leray sequences. A commutative square of sites induces one after choosing the base-change morphism of Chapter 11. These maps are independent of resolution choices because any two choices have a common comparison unique up to homotopy.

The edge maps have concrete meanings:

$$
H^n(X,\mathcal F)\longrightarrow
H^0(Y,R^nf_*\mathcal F)
$$

records the restrictions of a global cohomology class over the local objects of $Y$; identifying its values with fiber cohomology requires the relevant base-change theorem. The other edge map

$$
H^n(Y,f_*\mathcal F)\longrightarrow H^n(X,\mathcal F)
$$

is induced by the equality of underived global sections. In degree one the five-term sequence is

$$
0\to H^1(Y,f_*\mathcal F)\to H^1(X,\mathcal F)
\to H^0(Y,R^1f_*\mathcal F)
\to H^2(Y,f_*\mathcal F)\to H^2(X,\mathcal F).
$$

The middle arrow measures whether fiberwise torsors arise globally; its following obstruction lies on the base.

### 8.3 Degeneration criteria and examples

If $R^qf_*\mathcal F=0$ for $q>0$, Leray collapses and

$$
H^n(X,\mathcal F)\cong H^n(Y,f_*\mathcal F).
$$

If $Y$ has cohomological dimension at most one, only columns $p=0,1$ remain and all $d_r$ for $r\ge2$ vanish. The resulting short exact sequences

$$
0\to H^1(Y,R^{n-1}f_*\mathcal F)\to H^n(X,\mathcal F)
\to H^0(Y,R^nf_*\mathcal F)\to0
$$

need not split. This is a standard arithmetic situation over a one-dimensional base.

For the projection $X\times Y\to Y$ with coefficients pulled back from $X$, Leray organizes the cohomology of the product. A direct-sum Kunneth formula requires flatness or field coefficients; torsion coefficients introduce Tor extensions, which are naturally detected by derived tensor rather than by a naive tensor product of cohomology groups.

A finite morphism supplies a useful test. If $f_*$ is exact on the chosen sheaf category, then $R^qf_*=0$ for $q>0$ and Leray is an isomorphism from base cohomology with coefficients $f_*\mathcal F$ to cohomology upstairs. Exactness holds for sheaves of modules when sections over an object downstairs are a finite product of sections over its inverse-image components and coverings behave compatibly; finite products are exact in an abelian category. This proof also shows the boundary: if the inverse image is not a finite disjoint union in the relevant topology, exactness cannot be inferred from finiteness of the underlying point map alone.

At the opposite extreme, suppose only $R^0f_*$ and $R^1f_*$ are nonzero and $Y$ has cohomological dimension two. The sole potentially nonzero differential is

$$
d_2^{0,1}:H^0(Y,R^1f_*\mathcal F)
\longrightarrow H^2(Y,f_*\mathcal F).
$$

A fiberwise degree-one class globalizes precisely when this transgression vanishes, up to the ambiguity from $H^1(Y,f_*\mathcal F)$. This is more informative than a dimension count: it identifies both the obstruction group and the torsor of possible lifts.

## 9. The Hochschild--Serre spectral sequence

### 9.1 Equivariant sections

Let a group $G$ act on a site $\bar X$, and suppose $X$ is the corresponding quotient in the sense that sheaves on $X$ are identified with suitably descent-equipped sheaves on $\bar X$. For a $G$-equivariant sheaf $\mathcal F$,

$$
\Gamma(X,\mathcal F)=\Gamma(\bar X,\mathcal F)^G.
$$

For a profinite $G$ and discrete module $M$, invariants are left exact. Continuous cohomology is computed by the inhomogeneous cochains

$$
C^p_{\mathrm{cts}}(G,M)=\{\text{continuous maps }G^p\to M\}
$$

with differential

$$
\begin{aligned}
(dc)(g_1,\ldots,g_{p+1})={}&g_1c(g_2,\ldots,g_{p+1})\\
&+\sum_{r=1}^{p}(-1)^r
c(g_1,\ldots,g_rg_{r+1},\ldots,g_{p+1})\\
&+(-1)^{p+1}c(g_1,\ldots,g_p).
\end{aligned}
$$

Every term is continuous. Expanding $d(dc)$, the two ways of multiplying two adjacent entries cancel with opposite signs; the two ways involving the action cancel as well. Hence $d^2=0$, and the kernel in degree zero is $M^G$. Continuity and compactness imply that a cochain has finite image and is constant on the cosets of some open normal subgroup in each variable. Thus it factors through $(G/U)^p$ for a suitable open normal subgroup $U$ depending on the cochain.

For completeness, these cochains do calculate the right-derived functors of invariants. Let $B^p(M)=\operatorname{Map}_{\mathrm{cts}}(G^{p+1},M)$ with its diagonal $G$-action and the alternating differential that omits one entry. The augmented complex $M\to B^0(M)\to B^1(M)\to\cdots$ is exact on underlying modules: inserting $1$ as the first entry gives a contraction. Each $B^p(M)$ is coinduced, because its first variable identifies it with $\operatorname{Map}_{\mathrm{cts}}(G,N_p)$ for a suitable discrete module $N_p$. Coinduced modules are acyclic for invariants by the same insertion contraction.

The invariants $B^p(M)^G$ are the homogeneous continuous cochains, namely the functions satisfying

$$
f(gg_0,\ldots,gg_p)=g f(g_0,\ldots,g_p),
$$

and the differential is the alternating sum of the omission maps. Evaluation at $(1,g_1,g_1g_2,\ldots,g_1\cdots g_p)$ identifies this invariant complex with the inhomogeneous one above. The acyclic-resolution lemma of Section 3.7 therefore identifies the cohomology of $C^\bullet_{\mathrm{cts}}(G,M)$ with $R^p(-)^G(M)$.

### 9.2 Construction and convergence

Apply the composition theorem to global sections on $\bar X$ followed by invariants. The precise geometric hypothesis is that the global sections on $\bar X$ of every injective equivariant sheaf are acyclic for invariants. It holds in the standard quotient situation when the equivariant sheaf category has an exact forgetful functor with exact coinduction and the global-section functor carries the resulting coinduced injectives to coinduced discrete modules. On the module side, coinduction is

$$
M\longmapsto \operatorname{Map}_{\mathrm{cts}}(G,M),
$$

and its higher invariant cohomology vanishes by the contracting homotopy that inserts the identity element. Thus the stated geometric condition is not being inferred merely from the existence of coinduction: the compatibility with global sections is part of the quotient hypothesis. Under it, the composition theorem gives

$$
E_2^{p,q}=H^p_{\mathrm{cts}}
\bigl(G,H^q(\bar X,\mathcal F)\bigr)
\Longrightarrow H^{p+q}(X,\mathcal F).
$$

For a bounded-below equivariant complex $K$, replace $H^q$ by $\mathbb H^q$.

Strong convergence holds for a sheaf and, after translating the vertical index, for every bounded-below equivariant complex: both indices are then nonnegative and each total diagonal is finite. For a complex whose cohomology is unbounded below, the equivariant right-derived operations are available only in the range fixed in Section 3.6, and even there a finite-cohomological-dimension bound is needed to make the diagonals finite. For completed coefficients, the continuous cochain totalization and derived inverse limit must be retained; ordinary invariants of the inverse limit can miss a first derived-limit term.

### 9.3 Restriction, inflation, and descent

For a closed normal subgroup $N\triangleleft G$, invariants factor as

$$
(-)^G=\bigl((-)^N\bigr)^{G/N}.
$$

The same construction gives

$$
H^p_{\mathrm{cts}}(G/N,H^q_{\mathrm{cts}}(N,M))
\Longrightarrow H^{p+q}_{\mathrm{cts}}(G,M).
$$

Normality gives the inner cohomology groups a $G/N$-action, and discreteness follows from the finite-quotient description of continuous cochains.

Its five-term sequence begins

$$
0\to H^1_{\mathrm{cts}}(G/N,M^N)\xrightarrow{\mathrm{inf}}H^1_{\mathrm{cts}}(G,M)
\xrightarrow{\mathrm{res}}H^1_{\mathrm{cts}}(N,M)^{G/N}
\xrightarrow{\mathrm{tr}}H^2_{\mathrm{cts}}(G/N,M^N).
$$

The transgression sends an invariant $N$-extension to its obstruction to descent through $G/N$. Exactness is the general edge-map argument of Section 6.3. For a finite Galois cover $\bar X\to X$, the same sequence can be obtained from the Cech nerve of the cover: its iterated fiber products are indexed by tuples of elements of $G$, and the alternating Cech differential becomes the bar differential. This is descent along the cover; it should not be confused with a claim that the direct image of the finite map has nonzero higher derived functors.

When the order of a finite group $G$ is invertible on $M$, invariants are exact. Indeed, the averaging operator

$$
e_G(m)=\frac1{|G|}\sum_{g\in G}gm
$$

is an idempotent with image $M^G$. Given a surjection $M\to N$ and $n\in N^G$, lift $n$ to $m$ and average; $e_G(m)$ is an invariant lift. Therefore $H^p(G,M)=0$ for $p>0$, and Hochschild--Serre collapses to

$$
H^n(X,\mathcal F)\cong H^n(\bar X,\mathcal F)^G.
$$

The invertibility assumption matters. For the trivial action of a cyclic group of order $\ell$ on $\mathbf Z/\ell\mathbf Z$, the homomorphism sending a generator to $1$ defines a nonzero class in $H^1$. Averaging is impossible, and invariant geometric data may carry genuine descent obstructions.

## 10. Products and multiplicative spectral sequences

### 10.1 Filtered differential graded products

Suppose $K$ has a graded product satisfying

$$
d(xy)=d(x)y+(-1)^{|x|}x\,d(y),\qquad
F^pK\cdot F^{p'}K\subseteq F^{p+p'}K.
$$

Then the representative formula gives products

$$
E_r^{p,q}\otimes E_r^{p',q'}
\longrightarrow E_r^{p+p',q+q'}.
$$

If $x,y$ survive to page $r$, so does their product up to the required depth, and

$$
d_r(xy)=d_r(x)y+(-1)^{p+q}x\,d_r(y).
$$

Changing representatives changes the product by a boundary or a deeper-filtration term, so the operation is well defined. Passing to homology supplies the product on the next page.

### 10.2 Products on pages and on the abutment

Under strong convergence, the $E_\infty$ product is the associated graded of the product on $H^*(K)$ because cocycle multiplication respects the induced filtration. If the filtered differential graded product is graded commutative, or graded commutative through a filtration-preserving homotopy, then every page on which the product is defined is graded commutative with respect to total degree. Graded commutativity of the abutment alone would not imply graded commutativity on earlier pages.

Degeneration as groups does not determine the ring. Hidden multiplicative extensions remain: two classes represented in graded pieces may multiply into a deeper filtered piece invisible from their product in $E_\infty$. A claimed ring decomposition therefore needs a compatible splitting of the filtration, not merely vanishing differentials.

A useful vanishing principle follows from the derivation rule. If a page is generated as an algebra by permanent cycles, every differential on and after that page vanishes. Conversely, knowing differentials on algebra generators determines them on all products.

### 10.3 Derived cup products

Choose a K-flat resolution compatible with a multiplication, or use a functorial simplicial resolution whose total complex carries the shuffle product. The diagonal map and multiplication of coefficients give

$$
R\Gamma(X,A)\otimes^LR\Gamma(X,B)
\longrightarrow R\Gamma(X,A\otimes^LB).
$$

On cohomology this is the cup product. The shuffle signs prove graded commutativity: interchanging blocks of total degrees $m,n$ contributes $(-1)^{mn}$. Associativity follows from associativity of the diagonal and tensor constraints. The Leray, Hochschild--Serre, and hypercohomology filtrations respect these pairings, so their spectral sequences are multiplicative whenever the coefficient pairing is.

## 11. Base change and arithmetic comparison

### 11.1 The base-change morphism

Consider a cartesian square of ringed sites

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
\downarrow f'&&\downarrow f\\
Y'&\xrightarrow{g}&Y.
\end{array}
$$

Adjunction produces the underived map $g^*f_*\to f'_*g'^*$. Choose K-flat replacements for the inverse images, which Section 3.5 supplies for arbitrary complexes, and bounded-below injective replacements for the direct images, so that $K$ is taken with bounded-below cohomology as in the theorem of Section 12.3. This yields

$$
Lg^*Rf_*K\longrightarrow Rf'_*Lg'^*K.
$$

This morphism exists without a properness, flatness, or finiteness assumption; those hypotheses enter only when one asks whether it is an isomorphism.

Functoriality under pasting follows from the units and counits of adjunction: both maps around a pasted rectangle are adjoint to the same composite from the pulled-back object. Thus base-change maps can be compared without choices.

### 11.2 A spectral criterion for base change

Choose compatible double-complex models for the two sides of the base-change morphism and filter them by resolution degree. The source has the hyper-Tor sequence

$$
E_2^{-p,q}=L_pg^*(R^qf_*K)
\Longrightarrow \mathcal H^{q-p}(Lg^*Rf_*K),
$$

where $L_p$ denotes the $p$th left-derived functor. Resolving $K$ K-flatly before applying $g'^*$ and then using a direct-image resolution gives a corresponding sequence for the target. In the nonflat case, a map between the displayed source terms and the target terms is extra data supplied by a higher base-change theorem; it is not a formal consequence of the underived square. Once compatible resolutions provide a morphism of spectral sequences, the abstract comparison argument assembles the termwise information.

**Base-change criterion.** Assume the two spectral sequences converge strongly and their abutment filtrations satisfy the reconstruction hypotheses of Section 6.4. If, on some page $r$, the induced map is an isomorphism in total degrees at most $n$ and a monomorphism in total degree $n+1$, then the base-change map is an isomorphism on cohomology in degrees at most $n$ and a monomorphism in degree $n+1$. In particular, an isomorphism on the whole page gives a derived isomorphism.

**Proof.** Naturality of the compatible filtrations gives a morphism of filtered objects. Apply the range comparison theorem of Section 6.4. The one-degree monomorphism buffer controls the kernels of differentials leaving the isomorphism range. $\square$

When both $g^*$ and its base change $g'^*$ are exact, as happens for a flat base change of schemes, all higher inverse-image functors vanish. For bounded-below $K$, the criterion reduces to the familiar sheafwise maps

$$
g^*R^qf_*K\longrightarrow R^qf'_*g'^*K.
$$

If they are isomorphisms for every $q$, the base-change morphism induces an isomorphism on every cohomology sheaf and is therefore a derived isomorphism. This cleanly separates a geometric input—the sheafwise comparison—from the homological argument assembling all degrees.

### 11.3 Coefficient change and derived completion

For a ring map $\Lambda\to\Lambda'$, coefficient change is $K\mapsto K\otimes^L_\Lambda\Lambda'$. If $K$ is represented by a bounded complex of flat $\Lambda$-modules, then

$$
H^n(K\otimes^L\Lambda')
$$

is governed by the universal-coefficient sequence

$$
0\to H^n(K)\otimes_\Lambda\Lambda'
\to H^n(K\otimes^L_\Lambda\Lambda')
\to \operatorname{Tor}_1^\Lambda(H^{n+1}(K),\Lambda')\to0
$$

when $\Lambda'$ has Tor dimension at most one. Filter a flat replacement by truncations; only two Tor rows remain, so the spectral sequence yields this exact sequence. It need not split naturally.

For an ideal $I\subset\Lambda$, derived $I$-completion is

$$
R\widehat K=R\varprojlim_m(K\otimes^L_\Lambda\Lambda/I^m).
$$

There is a Milnor exact sequence

$$
0\to R^1\varprojlim H^{n-1}(K\otimes^L\Lambda/I^m)
\to H^n(R\widehat K)
\to\varprojlim H^n(K\otimes^L\Lambda/I^m)\to0.
$$

Consequently ordinary completion computes derived completion when the cohomology towers are Mittag--Leffler and Tor terms are controlled. This proviso is central for integral arithmetic coefficients.

Reduction modulo one element illustrates both phenomena. Assume that multiplication by $\pi$ is injective on $\Lambda$, so

$$
0\longrightarrow\Lambda\xrightarrow{\pi}\Lambda
\longrightarrow\Lambda/(\pi)\longrightarrow0
$$

is a flat resolution of $\Lambda/(\pi)$. Tensoring it with $K$ gives the triangle

$$
K\xrightarrow{\pi}K\longrightarrow K\otimes^L\Lambda/(\pi)
\longrightarrow K[1]
$$

whose long exact cohomology sequence gives

$$
0\to H^n(K)/\pi H^n(K)
\to H^n(K\otimes^L\Lambda/(\pi))
\to H^{n+1}(K)[\pi]\to0.
$$

Thus reduction commutes with cohomology exactly when the next cohomology group has no $\pi$-torsion. Iterating this statement controls the transition maps modulo $\pi^m$ when every $\pi^m$ is again a non-zero-divisor. If $\Lambda$ is noetherian and complete and $K$ is a bounded complex with finitely generated cohomology, the Artin--Rees stabilization of the relevant torsion and quotient systems gives the Mittag--Leffler condition. Without these finiteness hypotheses, inverse systems can retain infinitely receding torsion and ordinary completion need not recover the derived one.

## 12. Reusable comparison theorems

### 12.1 The filtered comparison package

The following theorem is designed for repeated use.

**Filtered derived comparison theorem.** Let $u:(K,F)\to(L,F)$ be a morphism of filtered complexes in an abelian category. Assume:

1. each filtration is exhaustive and either finite in every complex degree or derived complete and separated;
2. the two spectral sequences converge strongly, and in the infinite case the cohomology towers are Mittag--Leffler so that inverse limits reconstruct the abutments exactly;
3. the spectral sequences use the same differential convention;
4. $\operatorname{gr}^p(u)$ is a quasi-isomorphism for every $p$.

Then $u$ is a quasi-isomorphism. It induces an isomorphism of filtered cohomology objects, not merely of their underlying objects. Any pairing already defined as a morphism of filtered complexes remains compatible after passage to the abutment.

**Proof.** The fourth condition makes the $E_1$ pages isomorphic. Naturality makes every later page isomorphic. The first two conditions identify $E_\infty$ with the associated graded of the abutment filtrations. Finite induction, or inverse limits with vanishing first derived limit, reconstructs the filtered cohomology isomorphism. A pairing that is compatible before passage to graded pieces is compatible on representatives, hence on every page and after completion. Merely knowing that two pairings agree on associated graded objects would not suffice, because they could differ by a filtration-raising map. $\square$

The completeness clause is essential: an infinitely deep nonzero subobject has zero associated graded and would otherwise furnish a false comparison.

### 12.2 The derived-composition package

**Derived-composition theorem.** Let $F$ and $G$ be left exact functors between Grothendieck abelian categories, and work in a range in which all three of $RG$, $RF$, and $R(F\circ G)$ are defined by Section 3.7: complexes with bounded-below cohomology in general, or arbitrary complexes when the categories involved have exact countable products. There is a canonical comparison

$$
R(F\circ G)\longrightarrow RF\circ RG.
$$

It is an isomorphism under either of the following precise hypotheses:

- on complexes with bounded-below cohomology, where the replacements of Section 3.4 are available without further conditions, it suffices that $G$ take injective objects to $F$-acyclic objects;
- on arbitrary complexes, provided the source categories have exact countable products, so that Section 3.6 produces K-injective replacements of every complex, it suffices in addition that $G(I)$ be $F$-acyclic for every K-injective $I$ occurring, meaning that $F(G(I))\to RF(G(I))$ is a quasi-isomorphism.

For an object $A$ in degree zero, or more generally in a first-quadrant range, the truncation filtration yields

$$
R^pF(R^qG(A))\Longrightarrow R^{p+q}(F\circ G)(A).
$$

The sequence is natural in $A$ and in natural transformations of $F$ or $G$, multiplicative when the functors carry compatible lax monoidal structures, and strongly convergent under first-quadrant or finite-diagonal hypotheses.

**Proof.** In the bounded-below case, choose an injective resolution $A\to I$. The complex $F(G(I))$ computes $R(F\circ G)(A)$. To compute $RF(RG(A))$, take a bounded-below injective replacement $G(I)\to J$. It is K-injective by Section 3.2. The replacement map induces

$$
F(G(I))\longrightarrow F(J),
$$

which explains the direction of the canonical comparison. Since every $G(I^q)$ is $F$-acyclic, the Cartan--Eilenberg argument of Section 8.1 shows that this map is a quasi-isomorphism. In the second case the argument is identical, run on the replacements furnished by Section 3.6: $G(I)$ computes $RG(A)$, its $F$-acyclicity makes $F(G(I))$ compute $RF(RG(A))$, and the chosen replacement also computes the derived composite. Filtering the Cartan--Eilenberg model by one resolution degree gives the displayed pages; comparison uniqueness supplies naturality. The product and convergence statements follow from Chapters 10 and 6. $\square$

Leray and Hochschild--Serre are instances of this single result, as is any further composite of left exact functors satisfying the stated acyclicity condition.

### 12.3 The arithmetic base-change package

**Arithmetic comparison theorem.** In a cartesian square as in Section 11.1, let $K$ be a bounded-below complex of arithmetic sheaves. Assume:

1. finite Tor amplitude for the inverse-image operations on $K$;
2. finite cohomological amplitude, uniformly in each contributing total range, for the direct images of the cohomology sheaves of $K$;
3. compatible resolutions give a morphism between the two higher base-change spectral sequences, and the maps

   $$
   L_b g^*\bigl(R^a f_*\mathcal H^q(K)\bigr)
   \longrightarrow
   R^a f'_*\bigl(L_b g'^*\mathcal H^q(K)\bigr)
   $$

   identify every contributing term on one page;
4. both sequences converge strongly and, if coefficients are inverse systems, their cohomology towers are Mittag--Leffler.

Then

$$
Lg^*Rf_*K\xrightarrow{\sim}Rf'_*Lg'^*K.
$$

The isomorphism is compatible with composition of squares, with any coefficient pairings carried by the base-change construction, with truncation filtrations and edge maps, and with coefficient reduction formed by derived tensoring both sides.

**Proof.** Finite Tor and cohomological amplitudes make the relevant triple filtrations finite on every diagonal. The maps in item 3 identify a whole page, so filtered comparison proves the derived isomorphism. Pasting compatibility was proved from adjunction in Section 11.1. The base-change morphism respects coefficient pairings on the chosen K-flat and K-injective representatives, so Chapter 10 carries cup-product compatibility to the abutment. Truncation and edge-map compatibility are functorial. Coefficient reduction follows by derived tensoring the comparison; for completed coefficients, the Mittag--Leffler condition removes the inverse-limit obstruction. $\square$

The theorem deliberately separates formal homological conditions from geometric base-change input. For flat base change, $b=0$ is the only row in item 3, and the hypotheses reduce to the sheafwise maps of Section 11.2. In a nonflat application, the compatible higher maps in item 3 must actually be constructed; their existence is not hidden in the word “cartesian.” Identifying the coefficient-reduced right side with the direct image of reduced coefficients additionally requires the corresponding projection formula.

### 12.4 Final synthesis

The constructions of this book reduce layered arithmetic cohomology to a stable sequence of decisions. Replace complexes by objects on which the desired operation respects quasi-isomorphisms; Chapter 3 built those replacements rather than postulating them, producing K-flat replacements of arbitrary complexes from free presheaves and filtered colimits, K-injective replacements of bounded-below complexes from the Cartan--Eilenberg construction together with the internal criterion that the sheaf-valued Hom needs, and K-injective replacements of arbitrary complexes by homotopy limits wherever countable products are exact. Express a composite operation or a filtration as a spectral object. Identify its graded layers, verify finite-diagonal convergence or derived completeness, and retain the induced filtration and edge maps. When products, base change, or group actions are present, construct them before passing to pages so their compatibility survives to the target.

Three warnings remain permanent. A degenerate spectral sequence gives graded pieces, not a canonical splitting. A termwise injective or flat unbounded complex need not be an admissible replacement. An inverse limit can contribute a first derived-limit term. With these obstructions made explicit, hypercohomology, Leray, Hochschild--Serre, and base change become manifestations of one rigorous method. The comparison theorems above provide a closed toolkit for carrying that method into coherent, equivariant, torsion, and completed arithmetic sheaf theories.
