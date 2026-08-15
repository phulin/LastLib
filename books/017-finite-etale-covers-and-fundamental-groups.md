# Finite Étale Covers and Fundamental Groups

## Contents

1. [Covering theory in algebraic geometry](#1-covering-theory-in-algebraic-geometry)
   - [The problem and the guiding analogy](#11-the-problem-and-the-guiding-analogy)
   - [Standing conventions](#12-standing-conventions)
   - [Why finite étale rather than merely finite flat](#13-why-finite-étale-rather-than-merely-finite-flat)
2. [Étale morphisms](#2-étale-morphisms)
   - [Unramified, flat, and finitely presented](#21-unramified-flat-and-finitely-presented)
   - [Differentials and the diagonal](#22-differentials-and-the-diagonal)
   - [Standard étale algebras and the Jacobian criterion](#23-standard-étale-algebras-and-the-jacobian-criterion)
   - [Why standard charts exist](#24-why-standard-charts-exist)
   - [Finite criteria and counterexamples](#25-finite-criteria-and-counterexamples)
3. [Finite étale algebras and schemes](#3-finite-étale-algebras-and-schemes)
   - [Fields](#31-fields)
   - [Local and henselian rings](#32-local-and-henselian-rings)
   - [Henselizations and pointed neighborhoods](#33-henselizations-and-pointed-neighborhoods)
   - [Trace, discriminant, and idempotents](#34-trace-discriminant-and-idempotents)
   - [Operations and degree](#35-operations-and-degree)
4. [Geometric fibers](#4-geometric-fibers)
   - [Why geometric points are necessary](#41-why-geometric-points-are-necessary)
   - [The fiber functor](#42-the-fiber-functor)
   - [Connected components and constant degree](#43-connected-components-and-constant-degree)
   - [Morphisms detected on one fiber](#44-morphisms-detected-on-one-fiber)
5. [Connected and Galois covers](#5-connected-and-galois-covers)
   - [Deck transformations and simple transitivity](#51-deck-transformations-and-simple-transitivity)
   - [Domination and refinement](#52-domination-and-refinement)
   - [Galois closures](#53-galois-closures)
6. [Effective finite étale descent](#6-effective-finite-étale-descent)
   - [Descent data](#61-descent-data)
   - [Affine faithfully flat descent](#62-affine-faithfully-flat-descent)
   - [Gluing covers and morphisms](#63-gluing-covers-and-morphisms)
7. [The Galois category of a connected scheme](#7-the-galois-category-of-a-connected-scheme)
   - [The axioms](#71-the-axioms)
   - [Verification for finite étale covers](#72-verification-for-finite-étale-covers)
   - [The reconstruction theorem](#73-the-reconstruction-theorem)
8. [The étale fundamental group](#8-the-étale-fundamental-group)
   - [Definition and topology](#81-definition-and-topology)
   - [Profinite inverse limits](#82-profinite-inverse-limits)
   - [Classification of finite covers](#83-classification-of-finite-covers)
9. [Subgroups, pointed covers, and deck groups](#9-subgroups-pointed-covers-and-deck-groups)
   - [Connected covers and open subgroups](#91-connected-covers-and-open-subgroups)
   - [Normal subgroups and Galois covers](#92-normal-subgroups-and-galois-covers)
   - [Cofinal inverse systems](#93-cofinal-inverse-systems)
10. [Basepoints and étale paths](#10-basepoints-and-étale-paths)
    - [Paths as fiber-functor isomorphisms](#101-paths-as-fiber-functor-isomorphisms)
    - [Inner ambiguity](#102-inner-ambiguity)
    - [Basepoint-independent statements](#103-basepoint-independent-statements)
11. [Fields and absolute Galois groups](#11-fields-and-absolute-galois-groups)
    - [Finite étale algebras over a field](#111-finite-étale-algebras-over-a-field)
    - [Recovering the absolute Galois group](#112-recovering-the-absolute-galois-group)
    - [Arithmetic and geometric Frobenius conventions](#113-arithmetic-and-geometric-frobenius-conventions)
    - [Function fields and arithmetic schemes](#114-function-fields-and-arithmetic-schemes)
12. [The fundamental exact sequence](#12-the-fundamental-exact-sequence)
    - [Statement and basepoints](#121-statement-and-basepoints)
    - [Proof by finite sets](#122-proof-by-finite-sets)
    - [Arithmetic and geometric monodromy](#123-arithmetic-and-geometric-monodromy)
    - [The relative homotopy sequence](#124-the-relative-homotopy-sequence)
    - [Exactness criteria and failure modes](#125-exactness-criteria-and-failure-modes)
13. [Changing the ground field](#13-changing-the-ground-field)
    - [Separable extensions](#131-separable-extensions)
    - [Algebraic extensions and exact images](#132-algebraic-extensions-and-exact-images)
    - [Purely inseparable invariance](#133-purely-inseparable-invariance)
    - [Extension of algebraically closed fields](#134-extension-of-algebraically-closed-fields)
14. [Specialization over henselian discrete valuation rings](#14-specialization-over-henselian-discrete-valuation-rings)
    - [The direction of specialization](#141-the-direction-of-specialization)
    - [Smooth families](#142-smooth-families)
    - [Proper smooth families](#143-proper-smooth-families)
    - [What fails without the hypotheses](#144-what-fails-without-the-hypotheses)
    - [Boundaries, tame quotients, and semistable curves](#145-boundaries-tame-quotients-and-semistable-curves)
15. [Curves and explicit covers](#15-curves-and-explicit-covers)
    - [Affine and projective lines](#151-affine-and-projective-lines)
    - [Kummer covers of the punctured line](#152-kummer-covers-of-the-punctured-line)
    - [Artin–Schreier covers](#153-artinschreier-covers)
    - [Elliptic isogenies and inseparable maps](#154-elliptic-isogenies-and-inseparable-maps)
    - [Compactification, inertia, and tame covers](#155-compactification-inertia-and-tame-covers)
    - [Arithmetic curves and good reduction](#156-arithmetic-curves-and-good-reduction)
16. [Locally constant finite sheaves](#16-locally-constant-finite-sheaves)
    - [From descent data to monodromy](#161-from-descent-data-to-monodromy)
    - [Finite modules and representations](#162-finite-modules-and-representations)
    - [Lisse finite-coefficient sheaves](#163-lisse-finite-coefficient-sheaves)
    - [Permutation representations from covers](#164-permutation-representations-from-covers)
    - [Integral and rational adic representations](#165-integral-and-rational-adic-representations)
17. [The covering–monodromy dictionary](#17-the-coveringmonodromy-dictionary)
    - [The dictionary](#171-the-dictionary)
    - [A construction protocol](#172-a-construction-protocol)
    - [Conclusion](#173-conclusion)

## 1. Covering theory in algebraic geometry

### 1.1 The problem and the guiding analogy

Topology studies a connected space by looking at all of its finite covering spaces. A loop permutes the points above a basepoint, and the collection of these permutations remembers more than any single cover. Algebraic varieties carry an analogous theory, but ordinary local homeomorphisms are too coarse for the Zariski topology. The correct replacement is an étale morphism: algebraically, it has no infinitesimal ramification; geometrically, it looks locally like a disjoint union of copies of the base in a topology fine enough to see polynomial roots.

This book develops the finite part of that theory. For a connected scheme $X$ and a geometric point $\bar x$, every finite étale cover $Y\to X$ has a finite geometric fiber $Y_{\bar x}$. Symmetries compatible across all covers form a profinite group $\pi_1(X,\bar x)$. The central theorem is an equivalence

$$
\operatorname{FEt}(X)\simeq \operatorname{FinSet}_{\pi_1(X,\bar x)},
$$

where the right side consists of finite sets with continuous left action. This is not merely an analogy with topology. Over $\operatorname{Spec}K$ it recovers the absolute Galois group exactly, and over a variety over $K$ it separates geometric monodromy from arithmetic Galois action.

### 1.2 Standing conventions

All schemes are schemes in the usual sense. A **cover** in this book means a finite étale morphism; it need not be connected or surjective unless stated. We write $\operatorname{FEt}(X)$ for their category. A geometric point is a morphism $\bar x\colon\operatorname{Spec}\Omega\to X$ with $\Omega$ separably closed. Unless explicitly relaxed, schemes whose fundamental groups are considered are connected and locally noetherian. This gives the familiar path and Galois-category results without hidden quasi-compactness pathologies.

The geometric fiber functor is

$$
F_{\bar x}(Y)=\operatorname{Hom}_X(\bar x,Y).
$$

We define $\pi_1(X,\bar x)=\operatorname{Aut}(F_{\bar x})$. If $g$ is such an automorphism and $y\in F_{\bar x}(Y)$, write $g\cdot y=g_Y(y)$. Thus all monodromy sets carry **left** actions. With this convention a morphism of pointed connected covers corresponds to inclusion of stabilizers in the same direction; no inverse is silently inserted.

The local noetherian hypothesis is not part of the definition of finite étale. It enters the clean Galois-category proof, geometric connectedness arguments, and standard specialization results. We state stronger generalities only when they clarify, rather than obscure, the applications to curves and arithmetic bases.

### 1.3 Why finite étale rather than merely finite flat

Finite locally free maps already have constant finite fibers counted with multiplicity. But multiplicity is precisely what covering theory must exclude. The map

$$
\operatorname{Spec}k[t]/(t^2)\longrightarrow\operatorname{Spec}k
$$

has rank $2$ and only one geometric point. Likewise $t\mapsto t^n$ on the affine line is finite flat, yet ramifies at $0$ when $n>1$. A loop-like symmetry should permute distinct sheets, not nilpotent thicknesses or colliding branches.

Étaleness adds the condition that infinitesimal lifting be unique. A finite étale fiber over an algebraically closed field is a disjoint union of reduced points, and its cardinality equals its rank. This makes geometric fibers honest finite sets and makes descent rigid enough to reconstruct the cover from monodromy.

## 2. Étale morphisms

### 2.1 Unramified, flat, and finitely presented

Three independent problems must be controlled. Finite presentation prevents an infinite system of equations from masquerading as finite-dimensional geometry. Flatness says that relations do not appear upon specialization. Unramifiedness says that once a point is lifted, it has no infinitesimal directions relative to the base. Their conjunction is the right algebraic substitute for a local isomorphism.

A morphism $f\colon X\to S$ is **étale** if it is locally of finite presentation, flat, and unramified. For an affine map induced by $A\to B$, unramified means that $B$ is of finite type and the module of Kähler differentials $\Omega_{B/A}$ vanishes; with finite presentation already imposed, this is equivalent to the scheme-theoretic definition. A **finite étale** map is both finite and étale. Its algebra is consequently finite projective over the base: finite presentation plus flatness converts finite flatness into finite local freeness.

Each clause matters. The localization $A\to A_f$ is étale but usually not finite. The quotient $A\to A/I$ may have zero differentials and be finitely presented but is not flat unless its support splits appropriately. An infinite separable algebraic field extension is formally étale in an infinitesimal sense but is not of finite presentation, and therefore is not an étale morphism.

### 2.2 Differentials and the diagonal

Why does $\Omega_{B/A}=0$ express absence of ramification? For a $B$-module $M$, $A$-derivations $B\to M$ are represented by maps $\Omega_{B/A}\to M$. If the module of differentials vanishes, no nonzero first-order displacement fixes the base. Equivalently, for every square-zero extension $C\twoheadrightarrow C/J$, two $A$-algebra maps $B\to C$ agreeing modulo $J$ must coincide.

Geometrically, a morphism locally of finite type is unramified exactly when its diagonal

$$
\Delta_f\colon X\longrightarrow X\times_S X
$$

is an open immersion. If $f$ is separated—as every finite morphism is—the diagonal is also closed. For a finite étale cover, therefore, the diagonal is open and closed. This elementary fact drives the covering theory: two sections that agree at one geometric point agree on an open-and-closed locus, and distinct sheets can be separated.

The infinitesimal criterion combines uniqueness with existence. An étale morphism has the unique lifting property against nilpotent thickenings, locally on the source. In the finite case the local lifts glue uniquely, so finite étale algebras are insensitive to nilpotents in the base: if $I\subset A$ is nilpotent, reduction induces an equivalence between finite étale $A$-algebras and finite étale $A/I$-algebras.

There is also a useful local geometric formulation. If $f\colon X\to S$ is étale, $x\in X$ maps to $s\in S$, and $\bar s$ is a geometric point at $s$, then after passing to the strict henselization $\mathcal O^{\mathrm{sh}}_{S,\bar s}$ the part of $X$ through $x$ becomes a disjoint union of copies of the strictly henselian base. Thus étale maps really are local isomorphisms for the étale topology. The strict henselization remembers a chosen separable embedding of the residue field; this choice is the local ancestor of a geometric basepoint.

Unramified does not mean that the source has dimension zero. The identity of a curve is étale, and an open immersion is étale. It means relative dimension zero with no relative tangent directions. Flatness then makes that relative dimension stable. Smooth morphisms replace “relative dimension zero” by a fixed nonnegative relative dimension; étale morphisms are exactly the smooth morphisms of relative dimension zero.

### 2.3 Standard étale algebras and the Jacobian criterion

The most useful local model begins with one equation. If $f\in A[T]$ is monic, then

$$
B=A[T]/(f)
$$

is finite free. Since $\Omega_{B/A}\cong B\,dT/(f'(T)dT)$, it is finite étale precisely when the image of $f'$ is a unit in $B$. Equivalently, $(f,f')=A[T]$. Thus adjoining a root is étale exactly where that root is simple.

More generally, suppose

$$
B=A[T_1,\ldots,T_n]/(f_1,\ldots,f_n)
$$

and the determinant $J=\det(\partial f_i/\partial T_j)$ maps to a unit in $B$. Then $A\to B$ is standard étale after any needed localization, provided the presentation has the expected finite-presentation form. The Jacobian inverse solves infinitesimal lifting equations, while the presentation ensures there are only finitely many constraints. Every étale morphism is locally, on source and target, of this standard form.

For a finite algebra there is a particularly sharp criterion. If $B$ is finite projective over $A$, then the following are equivalent: $B$ is étale over $A$; $\Omega_{B/A}=0$; the multiplication map $B\otimes_A B\to B$ splits as a $B\otimes_A B$-module map; and every geometric fiber is a product of finite separable field extensions of the residue field. The splitting element is the separability idempotent. It is the algebraic shadow of the diagonal being an open-and-closed component.

Concretely, a separability idempotent is an element

$$
e=\sum_i x_i\otimes y_i\in B\otimes_AB
$$

with $\sum_i x_iy_i=1$ and $(b\otimes1)e=(1\otimes b)e$ for every $b\in B$. Multiplication maps $e$ to $1$, while $e$ cuts out the diagonal component of $\operatorname{Spec}(B\otimes_AB)$. This formula often proves étaleness without choosing a polynomial generator. It also shows stability under base change immediately: tensor the same identities with the new base ring.

For several equations the square Jacobian presentation is only a local normal form, not a demand that every global finite étale algebra be monogenic or globally a complete intersection in prescribed coordinates. Étale localization is what permits equations and variables to be adjusted. Confusing a local Jacobian criterion with a global presentation theorem is a frequent source of unjustified primitive-element claims over rings.

### 2.4 Why standard charts exist

The preceding charts are useful only if every étale morphism can be reached by them. The local structure theorem says precisely this. Let $A\to B$ be finitely presented, let $\mathfrak q\subset B$ lie over $\mathfrak p\subset A$, and suppose the map is étale at $\mathfrak q$. After localizing $A$ away from $\mathfrak p$ and $B$ away from $\mathfrak q$, there are a monic polynomial $f\in A[T]$ and an element $g$ in $A[T]/(f)$ such that

$$
B_g\cong (A[T]/(f))_g,
\qquad f'\text{ is invertible in }(A[T]/(f))_g.
$$

Such an algebra is called **standard étale**. One may replace the one-variable form by a square system of equations with invertible Jacobian determinant. The one-variable form emphasizes simple roots; the square form is often easier to extract from a given presentation.

Here is the proof mechanism. Choose a finite presentation

$$
B=A[T_1,\ldots,T_m]/I.
$$

At $\mathfrak q$, the conormal sequence

$$
I/I^2\longrightarrow
\bigoplus_{j=1}^m B\,dT_j
\longrightarrow \Omega_{B/A}\longrightarrow0
$$

ends in zero. Thus finitely many relations have differentials spanning the free module after localization. Flatness prevents hidden relations among the chosen equations. By adjoining harmless variables and eliminating the complementary ones, one obtains a square Jacobian matrix whose determinant is a unit. The adjugate matrix then solves every square-zero lifting problem uniquely. A further elementary elimination packages the resulting chart into one polynomial with simple derivative. Every operation is performed after inverting an element outside $\mathfrak q$, which explains why the theorem is local on both source and target rather than a global monogenicity statement.

The chart also proves that an étale morphism is open. In a standard chart, a point with residue-field root $a$ persists after sufficiently small base localization because $f'(a)$ stays invertible; the image contains a neighborhood of the base point. Passing through the local charts proves openness in general. Consequently an étale morphism that is also a monomorphism is an open immersion: its diagonal is an isomorphism, and each standard chart maps injectively onto an open subset.

Standard charts give a practical point-lifting principle. Given $s'\rightsquigarrow s$ in the base and a point $x$ over $s$ in an étale chart, a lift over $s'$ exists after a finite separable extension of the residue field whenever the simple-root equation acquires a root there; if it exists, henselianity later makes the lift unique in the chosen branch. Thus standard charts form the bridge between Jacobian algebra and henselian neighborhoods.

### 2.5 Finite criteria and counterexamples

Fiberwise reducedness alone needs care. For a finite locally free $A$-algebra $B$, $B$ is étale if and only if every geometric fiber $B\otimes_A\overline{\kappa(s)}$ is reduced. Finite presentation is built into finite local freeness, and the fiber condition detects vanishing of differentials. Without flatness, reduced fibers do not control the family.

The map $k[s]\to k[t]$, $s\mapsto t^n$, illustrates the characteristic dependence. Its differential relation is $n t^{n-1}dt=0$. Away from $t=0$, it is étale if $n$ is invertible in $k$. At $0$ it ramifies for $n>1$. If $\operatorname{char}k=p$ and $p\mid n$, the derivative can vanish identically, so even the restriction to $\mathbf G_m$ is not étale.

A second warning separates unramifiedness from flatness. Let $A=k[t]$ and $B=A/(t)$. Since $B$ is a quotient of $A$, $\Omega_{B/A}=0$, and the closed immersion is unramified. But $B$ is not flat over $A$, so the single point over $t=0$ is not a sheet extending over nearby points. In covering language, it appears only at one fiber. The definition of étale excludes exactly this behavior.

An étale morphism need not be surjective, proper, or finite: the open immersion $D(t)\hookrightarrow\operatorname{Spec}A$ is the basic counterexample to all three implications. Conversely, a finite map can be unramified at some points and ramified at others. The open subset on which a finitely presented flat map is étale is detected by the support of $\Omega_{B/A}$ and is therefore open.

Purely inseparable extensions give the field-level warning. For $K=k(u)$ of characteristic $p$ and $L=K(u^{1/p})$, the finite map $\operatorname{Spec}L\to\operatorname{Spec}K$ is flat, but $d(u^{1/p})$ survives because the defining derivative is zero. It is not étale. Separability is not decorative terminology: it is precisely the absence of this infinitesimal collapse.

## 3. Finite étale algebras and schemes

### 3.1 Fields

Let $K$ be a field. A finite $K$-algebra $A$ is étale if and only if

$$
A\cong L_1\times\cdots\times L_r
$$

with each $L_i/K$ finite separable. Indeed, an étale algebra is reduced and Artinian, hence a product of finite fields, and vanishing differentials says those extensions are separable. Conversely, finite separable extensions have nondegenerate separability idempotents, and products preserve étaleness.

After extension to a separable closure $K^s$ one obtains

$$
A\otimes_KK^s\cong (K^s)^N,
\qquad N=\dim_KA.
$$

The $N$ projections correspond to $K$-embeddings of the factors into $K^s$. The absolute Galois group permutes them. Already here the entire theory is visible: an algebra is replaced by its finite set of geometric points plus descent symmetry.

A finite field extension which is normal but inseparable is not étale. A finite separable extension need not be normal; its spectrum is nevertheless a connected finite étale cover. Galoisness concerns the size of its automorphism group, not étaleness itself.

### 3.2 Local and henselian rings

Over a local ring $A$, every finite étale algebra is finite free, but it need not be a product of copies of $A$. Its special fiber records residue extensions, and components can fail to lift unless the ring has a henselian property. This is the problem henselianity solves: it lifts simple roots, equivalently idempotents, uniquely from the residue field.

If $(A,\mathfrak m,k)$ is henselian, reduction gives an equivalence

$$
\operatorname{FEt}(A)\longrightarrow\operatorname{FEt}(k),
\qquad B\longmapsto B/\mathfrak mB.
$$

Thus every finite étale $A$-algebra is uniquely determined up to unique compatible isomorphism by a product of finite separable extensions of $k$. If $A$ is strictly henselian—henselian with separably closed residue field—every finite étale algebra is $A^n$. Hence a strictly henselian local scheme has trivial étale fundamental group.

The equivalence can be proved in three stages. First, an idempotent of a finite algebra lifts uniquely from the residue algebra, so the product decomposition of the special fiber lifts. Second, a simple residue-field generator has a monic minimal polynomial with invertible derivative, and Hensel's lemma lifts its factor and hence the corresponding étale algebra. Third, a morphism can be represented by a section of a suitable finite étale scheme; the henselian lifting property gives a unique section lifting its residue-field section. The result is categorical: it preserves products, morphisms, and automorphisms, not only isomorphism classes.

Here are the details hidden in the second and third steps. A finite separable field extension
$l/k$ has a primitive element with monic minimal polynomial $\overline f$. Lift $\overline f$ to a
monic $f\in A[T]$. Since $\overline f$ and $\overline f'$ are coprime, their resultant lifts to a
unit of $A$; hence $A[T]/(f)$ is finite étale and has special fiber $l$. Products treat an
arbitrary finite étale $k$-algebra. If $B$ and $C$ are finite étale over $A$, the functor

$$
D\longmapsto\operatorname{Hom}_{D\text{-alg}}(B\otimes_AD,C\otimes_AD)
$$

is represented by a finite étale $A$-scheme. This can be checked after a finite étale faithfully
flat extension splitting both algebras, where it is the constant finite scheme whose points are
maps between two finite sets; the representing scheme and its evaluation map descend by Chapter
6. A morphism between the special fibers is therefore a special-fiber point of a finite étale
$A$-scheme. Hensel's lemma lifts it uniquely. Thus reduction is full and faithful as well as
essentially surjective, proving the asserted equivalence without assuming that isomorphism
classes alone determine morphisms.

For a henselian DVR with finite residue field $\mathbf F_q$, connected finite étale covers of the spectrum are therefore the rings of integers in finite unramified extensions of the fraction field. Their residue fields are $\mathbf F_{q^n}$, and their deck groups are generated by residue Frobenius when the extension is Galois. Ramified extensions of the fraction field do not extend as étale covers of the DVR; the closed point detects the obstruction.

More generally, for any henselian local ring $(A,\mathfrak m,k)$ and compatible geometric points, reduction yields

$$
\pi_1(\operatorname{Spec}A)\cong G_k.
$$

This does not assert that the fraction field has the same absolute Galois group. For a henselian DVR, $G_K$ also contains inertia arising from extensions ramified along the closed point; passing to $\operatorname{Spec}A$ discards precisely those extensions and retains the unramified quotient $G_k$.

The word henselian cannot be omitted. Let $A=k[t]_{(t)}$ with $\operatorname{char}k\ne2$. The polynomial $X^2-X-t$ has two distinct roots modulo $t$, but those roots need not lie in $A$; the corresponding finite étale algebra near the closed point does not split as $A\times A$. Passing to the henselization supplies the roots and the splitting.

### 3.3 Henselizations and pointed neighborhoods

Henselian rings are most useful when attached canonically to an ordinary local ring. Let $(A,\mathfrak m,k)$ be local. Consider pairs $(B,\mathfrak n)$ in which $B$ is an étale $A$-algebra of finite presentation, $\mathfrak n$ lies over $\mathfrak m$, and the induced residue extension $k\to\kappa(\mathfrak n)$ is an isomorphism. Pointed maps between such pairs form a filtered system. Its filtered colimit is the **henselization** $A^h$.

The construction solves a universal problem: every local map $A\to C$ to a henselian local ring extends uniquely to a local map $A^h\to C$. To see existence, write each pointed neighborhood by a standard étale equation. Its distinguished residue root is simple, so Hensel's lemma gives a unique lift in $C$. Uniqueness on each chart makes the lifts compatible in the filtered system. Conversely the same simple-root argument proves that $A^h$ is henselian. The residue field remains $k$, and $A\to A^h$ is flat and local.

To retain all separable residue directions, choose a separable closure $k^s/k$ and allow pointed étale neighborhoods whose distinguished point has residue field inside $k^s$. Their filtered colimit is the **strict henselization** $A^{\mathrm{sh}}$. It is henselian with residue field $k^s$, hence strictly henselian. Different choices of $k^s$ yield noncanonical isomorphic rings; fixing a geometric point fixes the choice relevant to fundamental groups.

For a scheme $X$ and geometric point $\bar x$ above $x$, the affine schemes of the pointed étale neighborhoods form a cofiltered system, and

$$
\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{X,\bar x}
\simeq
\varprojlim_{(U,\bar u)} U
$$

in the sense that maps from the limit into a finitely presented affine scheme factor through one neighborhood. This is the **strict local neighborhood** of $\bar x$. It is not usually an open subscheme of $X$; it is a limit of increasingly accurate étale neighborhoods. That distinction matters whenever one informally says “shrink around a geometric point.”

Every finite étale cover $Y\to X$ splits over this strict local neighborhood:

$$
Y\times_X\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{X,\bar x}
\cong
\coprod_{y\in Y_{\bar x}}
\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{X,\bar x}.
$$

Indeed, the base is strictly henselian, so its finite étale algebras are products of copies of the base. The factors are labeled by their geometric special-fiber points. Because $Y$ is finitely presented, the finitely many idempotents defining this decomposition already occur over one pointed étale neighborhood. Thus a finite étale cover is not merely split on a formal limit: it becomes a disjoint union after one sufficiently small étale neighborhood of the chosen point.

This result gives the exact local intuition for the fiber functor used later. A point of $Y_{\bar x}$ chooses one local sheet, and uniqueness over a strictly henselian neighborhood prevents that sheet from merging with another. The global fundamental group measures the failure to label those local sheets compatibly while moving through all neighborhoods of $X$.

Henselization and completion should not be confused. For an excellent local ring the completion is often henselian and receives a map from the henselization, but completion carries additional infinitesimal limiting information. Finite étale covers are already controlled by the henselian property; no completeness hypothesis is needed. Nor does a strictly henselian local ring have to be algebraically closed as a ring or have algebraically closed fraction field. Its trivial fundamental group concerns covers of its spectrum, not finite separable extensions ramified away from the closed point.

### 3.4 Trace, discriminant, and idempotents

For a finite locally free algebra $B/A$, multiplication defines the trace pairing

$$
(x,y)\longmapsto \operatorname{Tr}_{B/A}(xy).
$$

The algebra is finite étale exactly when this pairing is perfect. Locally, a determinant of its matrix is the discriminant, so the étale locus is where that discriminant is invertible. This connects the geometric definition to the familiar arithmetic statement that primes dividing a discriminant are precisely the possible ramified primes.

Idempotents encode disjoint unions. In a finite étale algebra they behave exceptionally well under connected base change and henselian lifting. If the base $X$ is connected and $Y\to X$ is finite étale, each connected component of $Y$ is open and closed and maps surjectively to $X$. Consequently a nonempty connected finite étale cover has a well-defined positive degree.

As a worked arithmetic example, if $A=\mathbf Z[1/2]$ and $B=A[T]/(T^2-3)$, the derivative is $2T$. Since $T^2=3$ and both $2$ and $3$ are units only after also inverting $3$, this cover is étale over $\mathbf Z[1/6]$ but not over the prime above $3$. Its discriminant $12$ identifies exactly the excluded primes.

The trace criterion also distinguishes reducedness from separability. For $L=K(\alpha)$ with minimal polynomial $f$, the discriminant of the power basis is, up to sign, the norm of $f'(\alpha)$. It is nonzero precisely when $f$ has distinct roots, hence when $L/K$ is separable. In a family, “nonzero” is replaced by “invertible”: a discriminant may be nonzero in the generic field but vanish at a special prime, marking the point where formerly distinct sheets collide.

Not every finite étale algebra has constant rank on a disconnected base. If $A=A_1\times A_2$ and $B=B_1\times B_2$ with $B_i/A_i$ of ranks $n_i$, then the rank function equals $n_i$ on $\operatorname{Spec}A_i$. The locally constant rank function, rather than one global integer, is the invariant preserved by arbitrary base change.

### 3.5 Operations and degree

Finite étale morphisms are stable under arbitrary base change and composition. Finite disjoint unions are finite étale, as are fiber products over the base. If $Y\to X$ and $Z\to X$ have locally constant degrees $m$ and $n$, then $Y\times_XZ$ has degree $mn$, while $Y\amalg Z$ has degree $m+n$. A composition of constant degrees $m$ and $n$ has degree $mn$.

These assertions follow by translating to finite projective algebras. Base change preserves finite projectivity and differentials satisfy

$$
\Omega_{(B\otimes_AA')/A'}\cong \Omega_{B/A}\otimes_AA'.
$$

Composition uses the transitivity sequence for differentials together with flatness. Products of algebras correspond to disjoint unions, tensor products to fiber products.

Étaleness is fpqc-local on the base: if $S'\to S$ is faithfully flat and quasi-compact and the pullback of a finitely presented morphism $Y\to S$ is finite étale, then $Y\to S$ is finite étale. Finiteness, finite presentation, flatness, and vanishing of differentials all descend. Later we need the stronger effective statement that the cover itself, not merely its property, can be descended.

For number rings this gives a reusable construction. Let $L/K$ be a finite separable extension of number fields, let $\mathcal O_K\subseteq\mathcal O_L$ be their integer rings, and invert a finite set $S$ containing every prime that ramifies in $L$. Then

$$
\operatorname{Spec}\mathcal O_L[S^{-1}]
\longrightarrow
\operatorname{Spec}\mathcal O_K[S^{-1}]
$$

is finite étale. At a prime outside $S$, the residue fiber is a product of finite separable residue-field extensions, one for each prime above it. At a ramified prime the discriminant ceases to be a unit and the map is not étale. Deleting the branch locus turns an arithmetic finite map into a genuine cover.

As a geometric parallel, assume $2$ is invertible and consider $y^2=x(x-1)$ over

$$
X=\operatorname{Spec}k[x,x^{-1},(x-1)^{-1}].
$$

The element $y$ is a unit on the source, so the derivative $2y$ is invertible and the degree-two map is finite étale. Restoring either $x=0$ or $x=1$ restores a branch point. Étaleness is naturally a property over the open complement of a discriminant divisor.

## 4. Geometric fibers

### 4.1 Why geometric points are necessary

An ordinary rational point sees only sheets defined over its residue field. If $L/K$ is a nontrivial finite separable extension, then $\operatorname{Spec}L\to\operatorname{Spec}K$ is a genuine cover, but its fiber on $K$-rational points is empty unless $L=K$. A functor sending a cover to rational points would therefore erase most connected covers and could not be conservative.

A geometric point repairs this by passing to a separably closed field. For $\bar x\colon\operatorname{Spec}\Omega\to X$ and $Y\to X$ finite étale of degree $n$ near $x$, the base change $Y_{\bar x}$ is $n$ reduced $\Omega$-points. Thus

$$
F_{\bar x}(Y)=\operatorname{Hom}_X(\bar x,Y)
$$

is a finite set of exactly the correct cardinality. Enlarging $\Omega$ among separably closed fields changes this functor only by a noncanonical natural isomorphism.

The point $\bar x$ contains two pieces of information: an ordinary point $x\in X$ and an embedding of its residue field into a separably closed field. Over a nonclosed residue field, the second piece chooses all separable directions above $x$. Decomposition and inertia groups require additional local or global data, however. After choosing a point over $x$ in a connected Galois cover, its stabilizer is a decomposition group. For a cover étale at $x$, this stabilizer acts faithfully on the residue-field extension, so its inertia subgroup is trivial. Nontrivial inertia instead appears for a generically étale cover ramified at $x$, or equivalently in the Galois theory of a punctured local neighborhood; it is the kernel of the residue action. Thus these groups are not merely the automorphism group of a geometric point, and their embeddings in a global fundamental group depend on a lift or path up to conjugacy.

Using an algebraically closed field instead of a separably closed one gives the same finite étale fibers. Separably closed is conceptually sharper because purely inseparable enlargement creates no new étale points. In either case, a geometric point is not required to be a closed point; a geometric generic point is often the natural basepoint for an integral scheme.

### 4.2 The fiber functor

The fiber functor preserves the constructions needed for finite-set algebra:

$$
F_{\bar x}(Y\amalg Z)=F_{\bar x}(Y)\amalg F_{\bar x}(Z),
\qquad
F_{\bar x}(Y\times_XZ)=F_{\bar x}(Y)\times F_{\bar x}(Z).
$$

It sends the empty cover to the empty set and $X\to X$ to a singleton. It also preserves quotients by finite equivalence relations when those quotients are formed in finite étale covers.

Most importantly, it is conservative: if a morphism $Y\to Z$ of finite étale $X$-schemes induces a bijection on the fiber at $\bar x$, then it is an isomorphism, provided $X$ is connected. The reason is that the locus where a finite étale morphism has a specified fiberwise behavior is open and closed. A single nonempty fiber therefore controls every fiber.

The functor is also faithful. If two maps $a,b\colon Y\to Z$ agree on $F_{\bar x}(Y)$, their equalizer is open and closed in $Y$ because the diagonal of $Z/X$ is open and closed. It contains every component meeting the chosen fiber, hence all of $Y$.

### 4.3 Connected components and constant degree

For a finite étale map $Y\to X$, the degree function

$$
x\longmapsto \#Y_{\bar x}
$$

is locally constant. When $X$ is connected it is a single integer. Connected components of $Y$ are open and closed; under the locally noetherian hypothesis there are finitely many, and each nonempty component is a finite étale cover of $X$.

Consequently $Y$ is connected exactly when the eventual monodromy action on $F_{\bar x}(Y)$ is transitive. One direction is intuitive: an invariant subset of the fiber spreads to an open-and-closed subcover. Conversely, a decomposition of $Y$ gives an invariant partition of the fiber. This translation between connectedness and transitivity is the first line of the covering–group dictionary.

Connectedness of the base is indispensable. If $X=X_1\amalg X_2$, a finite étale cover may have degree $2$ over $X_1$ and degree $3$ over $X_2$; a basepoint on $X_1$ sees nothing over $X_2$. Fundamental groups therefore belong naturally to connected components.

### 4.4 Morphisms detected on one fiber

The fiber functor is not generally full before a group action is installed: an arbitrary map of underlying finite sets need not arise algebraically. The missing condition is compatibility with all monodromy permutations. Once $\pi_1$ is constructed, one proves

$$
\operatorname{Hom}_X(Y,Z)
\cong
\operatorname{Hom}_{\pi_1(X,\bar x)}(F_{\bar x}(Y),F_{\bar x}(Z)).
$$

This formula explains why the group is defined as automorphisms of the entire fiber functor rather than as permutations of one favored cover. Compatibility across all covers cuts the enormous symmetric groups down to the geometric symmetries that descend.

A useful special case is a section. Sections $X\to Y$ correspond to monodromy-fixed points of $F_{\bar x}(Y)$. Indeed, a section supplies one compatible point in every fiber, and a fixed geometric point spreads by descent to a component isomorphic to $X$. Thus the absence of fixed points is an exact obstruction to a global section.

More generally, the image of a morphism of covers can be read on one fiber. Factor the finite-set map into its image and coimage. The corresponding invariant subset spreads to an open-and-closed subcover of the target, while equal fiber points define an effective equivalence relation on the source. This is the geometric origin of image factorizations in a Galois category.

One should not confuse fiberwise existence with a section. Every nonempty finite étale cover has points over $\bar x$, but a section requires one point fixed by the entire fundamental group. For a connected cover of degree greater than one the action is transitive and has no fixed point, so no section exists.

## 5. Connected and Galois covers

### 5.1 Deck transformations and simple transitivity

For a connected cover $Y\to X$, its **deck group** is $\operatorname{Aut}_X(Y)$. Evaluation at a chosen $\bar y\in F_{\bar x}(Y)$ is injective: a deck transformation fixing $\bar y$ agrees with the identity on one geometric point and hence everywhere. Therefore

$$
|\operatorname{Aut}_X(Y)|\leq \deg(Y/X).
$$

The cover is **Galois** if equality holds. Equivalently, the deck group acts simply transitively on every geometric fiber; equivalently, $Y\times_XY$ is the disjoint union of the graphs of its deck transformations. This definition does not require choosing a point.

The equivalence deserves a proof. Injectivity of evaluation gives the inequality. If equality holds, the orbit of one point has the full size of the fiber, and the action is free, hence simply transitive. Conversely simple transitivity gives exactly one deck transformation taking a chosen point to each fiber point. The graph decomposition can be checked after the faithfully flat base change $Y\to X$, where the cover splits; effective descent then returns the global statement.

For $X=\operatorname{Spec}K$ and $Y=\operatorname{Spec}L$, connectedness says that $L$ is a field, étaleness says $L/K$ is finite separable, and the Galois-cover condition says $|\operatorname{Aut}_K(L)|=[L:K]$. It therefore recovers the usual meaning of a finite Galois extension.

For example, $L=\mathbf Q(\sqrt[3]{2})$ gives a connected degree-three cover of $\operatorname{Spec}\mathbf Q$, but it has no nontrivial deck transformation: the other two roots are not in the real cubic field. Its Galois closure $\mathbf Q(\sqrt[3]{2},\zeta_3)$ gives a degree-six Galois cover with deck group $S_3$ and dominates the cubic cover. The corresponding subgroup of $S_3$ has index three but is not normal. This one example displays connected, non-Galois, domination, and normal-core phenomena simultaneously.

Connectedness matters. The trivial cover $X\amalg X\to X$ has a transitive automorphism group on its two sheets, but calling it a connected Galois extension would corrupt the subgroup dictionary. We reserve “Galois cover” for connected covers satisfying the equivalent conditions above.

### 5.2 Domination and refinement

A pointed cover is a pair $(Y,\bar y)$ with $\bar y$ above $\bar x$. A pointed cover $(Z,\bar z)$ **dominates** $(Y,\bar y)$ if there is an $X$-map $Z\to Y$ carrying $\bar z$ to $\bar y$. For connected pointed covers such a map, if it exists, is unique and surjective. Domination orders covers by refinement: $Z$ distinguishes at least everything $Y$ distinguishes.

Two covers admit a common refinement. Take the connected component of $Y\times_XZ$ containing $(\bar y,\bar z)$. This cofiltered structure is what later permits inverse limits. It also makes clear why basepoints are useful: without them the product may contain several equally plausible connected components.

Automorphism groups run oppositely to refinement. A dominating pointed Galois cover $Z\to Y$ gives a surjection $\operatorname{Aut}_X(Z)\twoheadrightarrow\operatorname{Aut}_X(Y)$ when $Y$ is also Galois. The inverse limit of these finite quotient groups is therefore the natural receptacle for all finite monodromy.

### 5.3 Galois closures

Every connected finite étale cover of a connected locally noetherian scheme is dominated by a connected Galois cover. The construction is best understood fiberwise. Begin with the finite transitive permutation set attached to the cover. Its monodromy has finite image $G\subseteq S_n$; the cover corresponding to the regular $G$-set dominates the original one.

That description must not be used as a construction before the fundamental group exists. The
noncircular construction is the **frame cover**. If $Y/X$ has degree $n$, form the open-and-closed
subscheme

$$
\operatorname{Fr}(Y/X)\subseteq Y^n_X
$$

obtained by removing every diagonal $y_i=y_j$ for $i\ne j$. Its geometric fiber is the set of
orderings of the $n$ sheets, so it is a nonempty finite étale cover of degree $n!$. The symmetric
group $S_n$ acts freely on the right by permuting positions. Choose the connected component $P$
containing one frame. Every component of a finite étale cover maps onto connected $X$, and the
first projection $P\to Y$ is therefore a pointed domination after choosing the frame suitably.

It remains to prove that $P$ is Galois, rather than infer it from the dictionary still under
construction. Trivialize $Y$ after a finite étale faithfully flat base change. On overlaps the
labels of the sheets differ by a subgroup $M\subseteq S_n$. The connected components of the frame
cover are exactly the $M$-orbits on the set of frames. The subgroup of the right $S_n$-action
preserving the chosen orbit acts freely and transitively on that orbit: after identifying one
frame with the identity permutation, the orbit is $M$ itself and its preserving right
translations are the opposite regular action of $M$. Those translations commute with the overlap
permutations, so effective descent makes them deck transformations of $P$. There are exactly
$\deg(P/X)$ of them, and $P$ is Galois by §5.1.

The Galois closure is not usually unique as an unpointed object with extra choices, but the smallest normal subgroup it encodes is intrinsic up to conjugacy. This foreshadows a persistent theme: pointed objects yield literal subgroups; unpointed connected objects yield conjugacy classes.

## 6. Effective finite étale descent

### 6.1 Descent data

Base change is easy; reversing it is the substantive step. Suppose $S'\to S$ is faithfully flat and quasi-compact and $Y'\to S'$ is finite étale. Its two pullbacks to $S''=S'\times_SS'$ need not agree literally. To say that $Y'$ comes from $S$ is to give an isomorphism

$$
\varphi\colon p_1^*Y'\xrightarrow{\sim}p_2^*Y'
$$

whose three pullbacks to $S'\times_SS'\times_SS'$ satisfy

$$
p_{23}^*\varphi\circ p_{12}^*\varphi=p_{13}^*\varphi.
$$

This is a **descent datum**. The cocycle condition says that comparing the first copy to the third directly or through the second gives the same result. It is the exact compatibility required for gluing; omitting it leaves pairwise identifications that can contradict one another on triple overlaps.

### 6.2 Affine faithfully flat descent

Book 10 established effective faithfully flat descent for modules, finite projective algebras,
affine schemes, and their morphisms. That is exactly the applicable scheme-effectivity criterion
here: a finite étale morphism is affine. The finite étale case is a particularly clean
application, but it is worth displaying the equalizer because the same formula later becomes
finite-set invariance. Write $S=\operatorname{Spec}A$, $S'=\operatorname{Spec}A'$, with
$A\to A'$ faithfully flat, and $Y'=\operatorname{Spec}B'$. Put
$A''=A'\otimes_AA'$. A descent datum is an isomorphism between the two $A''$-algebras obtained
from $B'$ through the two maps $A'\rightrightarrows A''$, satisfying the cocycle equation.

The strategy is to recover the elements that agree under the two comparisons. Use the descent isomorphism to identify the two pullback algebras, and let $d_0,d_1$ be the resulting maps from $B'$ to that common algebra. Set

$$
B=\{b\in B':d_0(b)=d_1(b)\}.
$$

With either pullback algebra identified with $B'\otimes_AA'$, the usual faithfully flat equalizer sequence

$$
0\longrightarrow B\longrightarrow B'
\rightrightarrows B'\otimes_AA'
$$

is exact, and the canonical map $B\otimes_AA'\to B'$ is an isomorphism. Multiplication and the unit preserve the equalizer, so $B$ is an $A$-algebra, not merely a descended module. The cocycle identity is used precisely to prove surjectivity after tensoring.

Because finite projective modules descend faithfully flatly, $B$ is finite projective over $A$. Moreover

$$
\Omega_{B/A}\otimes_AA'\cong\Omega_{B'/A'}=0,
$$

and faithful flatness forces $\Omega_{B/A}=0$. Hence $B/A$ is finite étale. Uniqueness follows from the same equalizer. This proves that finite étale algebras, including their algebra structure, descend effectively.

### 6.3 Gluing covers and morphisms

For a general fpqc cover, apply the affine argument over an affine cover of $S$. The finite-reduction theorem of Book 10 permits a set-indexed covering family without replacing it by a possibly non-quasi-compact infinite coproduct. The descended finite algebras agree on overlaps because descent of morphisms is fully faithful, and relative spectra glue. Thus the pullback functor identifies $\operatorname{FEt}(S)$ with finite étale covers over $S'$ equipped with descent data.

Morphisms descend by an analogous equalizer. If $Y',Z'$ carry descent data, a map $Y'\to Z'$ descends exactly when its two pullbacks commute with those data. Faithful flatness ensures uniqueness. This fully faithful part is as important as existence: it is what permits a permutation of a split geometric fiber to descend when and only when it commutes with monodromy.

As a model, let $L/K$ be finite Galois. An $L$-scheme $Y'$ descends to $K$ when equipped with semilinear isomorphisms $\sigma^*Y'\to Y'$ satisfying the group law. For $Y'$ a finite disjoint union of points, this is simply a finite set with continuous $\operatorname{Gal}(L/K)$-action. General fpqc descent is the scheme-theoretic form of this familiar Galois descent.

Descent also explains why an isomorphism after base change need not descend by itself. If $Y_{S'}\cong Z_{S'}$, the chosen isomorphism must commute with the two descent data. Its failure to do so is measured by automorphisms of the pulled-back object. Thus “isomorphic after a cover” proves only local isomorphism; a compatible cocycle is the extra datum that proves global isomorphism.

In practice, finite étale descent can often be checked on geometric fibers. After refining $S'$ until both covers split, a morphism is a map of finite sets. The overlap identifications act as permutations, and the map descends precisely when it intertwines those permutations. The abstract equalizer proof is what guarantees that this finite combinatorics glues to an actual scheme morphism.

## 7. The Galois category of a connected scheme

### 7.1 The axioms

The fundamental group is reconstructed from a category that behaves like finite sets with an unknown symmetry group. A **Galois category** consists of a category $\mathcal C$ and a functor $F\colon\mathcal C\to\operatorname{FinSet}$ satisfying the following structural requirements. We state a concrete equivalent form suited to covers:

1. a terminal object, fiber products, and finite coproducts exist, and every object is a finite coproduct of connected objects;
2. every monomorphism identifies its source with a union of connected summands, and every morphism factors as a quotient onto its image followed by such a monomorphism;
3. quotients by finite group actions and by the finite effective equivalence relations needed below exist;
4. $F$ preserves the terminal object, fiber products, finite coproducts, quotients, and quotient maps, and it reflects isomorphisms;
5. every connected object is dominated by a connected Galois object.

Faithfulness follows from these clauses by applying $F$ to the equalizer of two arrows; we retain it
explicitly in calculations below. Several equivalent axiom systems occur. These conditions expose
the proof rather than conceal it: finite limits let us compare covers, coproducts encode
components, quotients encode orbit sets, and Galois domination supplies enough finite regular
objects to recover every permutation action.

### 7.2 Verification for finite étale covers

Let $X$ be connected and locally noetherian, and choose $\bar x$. We verify the axioms for $(\operatorname{FEt}(X),F_{\bar x})$.

Finite products are fiber products; equalizers are inverse images of the diagonal. Because a finite étale diagonal is open and closed, the equalizer is an open-and-closed subcover and remains finite étale. Coproducts are disjoint unions. Each cover has finitely many open-and-closed connected components, and each maps onto $X$. The same open-and-closed argument shows that a monomorphism is the inclusion of a union of components. For an arbitrary morphism, the fiberwise image is invariant under the overlap permutations after a splitting cover; descent gives an open-and-closed image subcover, and the source maps onto it as the quotient by the equivalence relation of having equal images.

If a finite group $G$ acts on $Y$, the affine-local invariant algebra constructs $Y/G$. After an étale cover splitting $Y$ into finitely many copies of the base, this is just the quotient of a finite set by $G$. Effective descent returns the quotient over $X$ and proves it finite étale. The same split calculation treats finite equivalence relations. Consequently the geometric fiber preserves quotients, products, equalizers, and coproducts.

Faithfulness and conservativity were proved from the open-and-closed diagonal and connectedness. Galois domination follows from the frame construction of §5.3. Every axiom has therefore been reduced either to finite-set algebra after an étale splitting cover or to effective descent. This is the decisive proof pattern of the subject.

### 7.3 The reconstruction theorem

Let $(\mathcal C,F)$ be a Galois category and $\Pi=\operatorname{Aut}(F)$. Give $\Pi$ the topology whose basic open neighborhoods of the identity fix pointwise $F(C)$ for finitely many objects $C$. Then $\Pi$ is profinite and $F$ lifts to an equivalence

$$
\mathcal C\simeq\operatorname{FinSet}_{\Pi}.
$$

Here is the proof strategy. Connected Galois objects $P$ have finite deck groups, and an element of $\Pi$ is determined by its compatible actions on their fibers. Thus $\Pi$ embeds into a product of finite groups. Compatibility conditions are closed, making $\Pi$ compact and totally disconnected. Galois domination shows that every object is detected at one of these finite levels.

More explicitly, point the connected Galois objects and order them by pointed domination. The
frame construction gives a common Galois refinement of any finite collection. If $G(P)$ denotes
the monodromy permutation group of $F(P)$, refinement gives a surjection $G(P')\to G(P)$.
Evaluation defines

$$
\Pi\longrightarrow\varprojlim_PG(P).
$$

It is injective because every object is dominated componentwise by some $P$. Given a compatible
tuple in the inverse limit, define its action on a point of $F(C)$ by choosing a pointed Galois
object dominating the connected component containing that point. A common refinement proves
independence of the choice, and the same argument proves naturality in $C$. The resulting natural
automorphism maps to the original tuple, proving surjectivity. Thus the displayed map is an
isomorphism, and in particular $\Pi$ is profinite.

For fullness, take a $\Pi$-equivariant map $u:F(C)\to F(D)$. Choose one pointed Galois object
$P$ dominating all connected components involved. Over $P$, both objects split, and $u$ is a map
between their finite sets of labels. Equivariance under $G(P)$ says exactly that its two pullbacks
to the overlap agree. Fully faithful descent produces a unique map $C\to D$.

For essential surjectivity, let $T$ be a finite continuous $\Pi$-set. Its action has an open
normal kernel $N$. By the definition of the topology, some finite collection of fibers has
pointwise stabilizer contained in $N$; choose one Galois object $P$ dominating that collection.
Then $T$ is a $G(P)$-set. Over $P$, take the constant object indexed by $T$ and glue it on the
overlap using this action. The group law is the cocycle condition, so effective descent gives an
object $C_T$ with $F(C_T)=T$. This also proves that every finite continuous action, not only a
transitive one, is realized. Faithfulness supplies uniqueness.

To make profiniteness explicit, for each finite collection of objects let $U$ be the subgroup acting trivially on all their fibers. Then $\Pi/U$ is finite, and naturality realizes $\Pi$ as the inverse limit of these finite images. The intersection of all $U$ is trivial because a natural automorphism trivial on every fiber is the identity. The inverse-limit topology is exactly the stabilizer topology, not merely a topology with the same open subgroups.

For essential surjectivity, continuity is decisive. If a finite $\Pi$-set $T$ were allowed a discontinuous action, its point stabilizers might not be open and no finite stage of the Galois system would detect it. A continuous action has an open normal kernel $N$, so it is a set for the finite group $\Pi/N$. A Galois object realizing this quotient, followed by the quotient construction for the relevant stabilizers, builds the desired object of $\mathcal C$.

This proof explains every hypothesis. Without effective quotients one could not realize orbit sets; without Galois domination finite actions might not occur; without conservativity reconstructed arrows could fail to be isomorphisms even when their fibers are.

## 8. The étale fundamental group

### 8.1 Definition and topology

For connected locally noetherian $X$ with geometric point $\bar x$, define

$$
\pi_1(X,\bar x)=\operatorname{Aut}(F_{\bar x}).
$$

An automorphism is a family of bijections of all finite geometric fibers, natural in the cover. We topologize the group by declaring the pointwise stabilizers of finite fibers to be open. Equivalently, stabilizers of individual points in fibers form a neighborhood basis at the identity.

This topology is not appended artificially. It is the weakest topology making every action on a geometric fiber continuous. Since a finite discrete set has open stabilizers, continuity means precisely that each finite piece of monodromy factors through a finite quotient. Composition and inversion are continuous because the neighborhood basis is stable under finite intersections and conjugation.

A morphism $f\colon(X,\bar x)\to(S,\bar s)$ of pointed connected schemes pulls covers of $S$ back to covers of $X$. The identification of fibers induces, by precomposition of natural automorphisms, a continuous homomorphism

$$
f_*\colon\pi_1(X,\bar x)\longrightarrow\pi_1(S,\bar s).
$$

Thus fundamental groups are covariant in pointed schemes, while covers are pulled back contravariantly.

### 8.2 Profinite inverse limits

Let $(Y,\bar y)$ range over connected pointed Galois covers of $(X,\bar x)$. The finite monodromy quotient acts regularly on $Y_{\bar x}$. Its left action commutes with the deck action, and a choice of $\bar y$ exhibits them as the two opposite regular actions. Pointed refinements induce surjections between the finite monodromy quotients. There is a canonical topological isomorphism

$$
\pi_1(X,\bar x)\cong
\varprojlim_{(Y,\bar y)}G(Y),
$$

where $G(Y)$ is the image of $\pi_1(X,\bar x)$ in $\operatorname{Sym}(Y_{\bar x})$. Each $G(Y)$ is canonically the monodromy quotient and, after using $\bar y$, is anti-isomorphic to the deck group. Equivalently one may identify it with the deck group by inserting inversion. Writing the limit in terms of $G(Y)$ keeps the chosen left-action convention honest.

The inverse limit is compact, Hausdorff, and totally disconnected; hence $\pi_1$ is profinite. Conversely, its open normal subgroups are kernels of actions on sufficiently large finite collections of fibers. The finite Galois covers form a cofinal system, so no finite monodromy is missed.

There is a mild handedness warning. On a Galois fiber, deck transformations act naturally and monodromy acts naturally, but these actions centralize one another and become opposite regular actions after choosing a point. Our classification always uses the declared left monodromy action. Statements identifying a quotient with a deck group are canonical only up to the corresponding opposite/conjugacy convention; the abstract finite group and exact sequences are unaffected.

### 8.3 Classification of finite covers

The reconstruction theorem gives the basic equivalence

$$
F_{\bar x}\colon\operatorname{FEt}(X)\xrightarrow{\sim}
\operatorname{FinSet}^{\mathrm{cont}}_{\pi_1(X,\bar x)}.
$$

It preserves fiber products, disjoint unions, quotients, and degree. A cover is connected precisely when its monodromy set is transitive. A section is a fixed point. A constant cover $\coprod_{a\in A}X$ corresponds to a finite set $A$ with trivial action.

As an immediate consequence, continuous homomorphisms between fundamental groups are best tested through restriction of finite actions. If $f\colon X\to S$, then pullback of a cover corresponds to restricting its $\pi_1(S)$-action along $f_*$. The map $f_*$ is surjective exactly when every connected finite étale cover of $S$ stays connected after pullback to $X$. It has dense image under the same condition; since its image is compact and hence closed, dense and surjective coincide.

Injectivity has a different flavor. A continuous homomorphism $\Pi'\to\Pi$ is injective if finite quotients of $\Pi'$ can be separated by restrictions of finite $\Pi$-sets. Geometrically, this asks whether covers of the source are dominated by components of pullbacks of covers of the target. It is therefore much stronger than preservation of connectedness and should never be inferred from surjectivity criteria.

The triviality criterion is especially useful: $\pi_1(X,\bar x)=1$ if and only if every finite étale cover is a finite disjoint union of copies of $X$. It is not enough that every cover possess a rational point unless one also knows how that point splits off and repeats over every connected component.

## 9. Subgroups, pointed covers, and deck groups

### 9.1 Connected covers and open subgroups

Let $\Pi=\pi_1(X,\bar x)$. A pointed connected cover $(Y,\bar y)$ determines the stabilizer

$$
H_{\bar y}=\{g\in\Pi:g\cdot\bar y=\bar y\}.
$$

It is open because the orbit is finite, and transitivity identifies $F_{\bar x}(Y)$ with the left $\Pi$-set $\Pi/H_{\bar y}$. Conversely every open subgroup $H$ gives a finite transitive set $\Pi/H$ and hence a pointed connected cover. Pointed isomorphism classes therefore correspond bijectively to open subgroups.

Changing the point above $\bar x$ conjugates the stabilizer. Thus unpointed connected covers correspond to conjugacy classes of open subgroups. This is not a defect: it records exactly the information forgotten when the lift of the basepoint is forgotten.

A pointed map $Z\to Y$ gives $H_{\bar z}\subseteq H_{\bar y}$. More generally, a $\Pi$-map $\Pi/H\to\Pi/K$ exists precisely when $H$ is contained in a conjugate of $K$; its choice is the choice of a coset satisfying that containment.

Degrees become subgroup indices. The degree of the cover attached to $H$ is $[\Pi:H]$, and if $H\subseteq K$ then the pointed map $\Pi/H\to\Pi/K$ has fiber size $[K:H]$. Accordingly,

$$
[\Pi:H]=[\Pi:K][K:H],
$$

which is exactly multiplication of degrees in a tower of finite étale covers. The elementary index formula is the monodromy shadow of finite locally free rank multiplication.

### 9.2 Normal subgroups and Galois covers

The connected cover attached to $H$ is Galois exactly when $H$ is normal. In that case $\Pi/H$ is itself a finite quotient group acting regularly on the fiber. With the left-monodromy convention, the geometric deck group is naturally the opposite of the group of left translations, or equivalently is identified with $\Pi/H$ after using right translations and the inversion isomorphism. One should remember which action is being used rather than suppress this harmless but real variance.

For arbitrary $H$, the deck group is

$$
\operatorname{Aut}_X(Y)\cong N_\Pi(H)/H,
$$

again with an opposite if one insists on identifying composition with a chosen side of coset multiplication. The cardinality is at most $[\Pi:H]$, with equality exactly when $H$ is normal. The Galois closure corresponds to the normal core

$$
\operatorname{core}_\Pi(H)=\bigcap_{g\in\Pi}gHg^{-1},
$$

an open normal subgroup because only finitely many conjugates occur.

### 9.3 Cofinal inverse systems

The universal pro-cover is not generally a scheme of finite type and should not be treated as an ordinary cover. It is the inverse system of all pointed connected finite étale covers. Its fiber is a profinite $\Pi$-torsor, and its finite quotients are the actual geometric covers.

For computations one may replace the full system by any cofinal family of pointed Galois covers. If $N$ ranges over open normal subgroups, then

$$
\Pi=\varprojlim_N\Pi/N.
$$

An equality or homomorphism between profinite groups can therefore be checked at every finite quotient. This finite-level principle underlies exact-sequence proofs and the passage from finite sheaves to continuous representations.

## 10. Basepoints and étale paths

### 10.1 Paths as fiber-functor isomorphisms

Topology uses a path to transport a fiber from one basepoint to another. In étale geometry there may be no literal arc, so the correct abstraction is retained: an **étale path** from $\bar x$ to $\bar x'$ is a natural isomorphism

$$
\gamma\colon F_{\bar x}\xrightarrow{\sim}F_{\bar x'}.
$$

For geometric points on the same connected locally noetherian scheme, such paths exist, although not canonically. This follows from the Galois-category connectedness theorem, or from choosing compatible points through the cofiltered system of connected covers.

Transport along $\gamma$ yields

$$
\gamma_*\colon\pi_1(X,\bar x)\xrightarrow{\sim}\pi_1(X,\bar x'),
\qquad g\longmapsto\gamma g\gamma^{-1}.
$$

The formula makes sense because $g$ acts naturally on $F_{\bar x}$ and $\gamma$ identifies that functor with the other fiber functor.

### 10.2 Inner ambiguity

If $\gamma'$ is another path, then $\gamma'^{-1}\gamma$ is an automorphism of $F_{\bar x}$. Hence the two induced group isomorphisms differ by an inner automorphism. There is therefore no canonical isomorphism between fundamental groups at two basepoints, only a canonical outer isomorphism class.

The same calculation explains pointed lifts. Let $Y\to X$ be connected and choose $\bar y$ above $\bar x$. Transporting $\bar y$ along a path to $\bar x'$ chooses a point above $\bar x'$. Replacing the path applies a monodromy element to that point, so the new stabilizer is conjugate to the old one. The conjugacy appearing in the open-subgroup classification is therefore exactly path ambiguity, not an unrelated group-theoretic accident.

This ambiguity propagates in a controlled way. An unpointed morphism $f\colon X\to S$ produces a homomorphism of fundamental groups only up to conjugation in the target, because one must choose a path between $f(\bar x)$ and the chosen $\bar s$. Kernels, surjectivity, openness of the image, and conjugacy classes of subgroups remain well defined.

For abelian quotients the ambiguity vanishes. Thus $\pi_1(X,\bar x)^{\mathrm{ab}}$ is canonically independent of the basepoint on a connected scheme. Likewise, the category of finite continuous actions is independent of basepoint up to a noncanonical equivalence whose ambiguity is naturally isomorphic to the identity.

### 10.3 Basepoint-independent statements

The phrase “$X$ is simply connected in the finite étale sense” means that every connected finite étale cover is trivial; equivalently, $\pi_1(X,\bar x)$ is trivial for one, hence every, geometric basepoint. Geometric connectedness, exactness of a sequence of fundamental groups, and the property that a cover is Galois are also basepoint-independent.

Individual elements of $\pi_1$ are usually not intrinsic. Frobenius at an unchosen geometric point, for example, is naturally a conjugacy class. Arithmetic statements should therefore use characteristic polynomials, traces, or conjugacy-stable subsets unless auxiliary paths and basepoints have been fixed.

There is a groupoid lurking behind these choices. Its objects are geometric points of $X$, and its morphisms are étale paths; the automorphism group at $\bar x$ is $\pi_1(X,\bar x)$. Working with the groupoid makes basepoint-independence literal, while choosing one object turns it into the more economical language of a single profinite group. For connected $X$ the two descriptions contain the same information.

## 11. Fields and absolute Galois groups

### 11.1 Finite étale algebras over a field

Fix a separable closure $K^s$ of a field $K$ and write

$$
G_K=\operatorname{Gal}(K^s/K)
$$

with its Krull topology. For a finite étale $K$-algebra $A$, define

$$
\Phi(A)=\operatorname{Hom}_{K\text{-alg}}(A,K^s).
$$

There is a left $G_K$-action by $(\sigma\cdot\iota)=\sigma\circ\iota$. It is continuous because each finite set of embeddings is defined over a finite separable subextension. Products of algebras become disjoint unions of sets, in accordance with the reversal between affine schemes and rings.

Conversely, if $T$ is a finite continuous left $G_K$-set, let

$$
A_T=\{f:T\to K^s\mid f(\sigma t)=\sigma f(t)\}.
$$

Pointwise operations make this a finite étale $K$-algebra. After tensoring with $K^s$, evaluation gives $(K^s)^T$. These constructions are quasi-inverse. On a transitive orbit $G_K/H$, the algebra is the fixed field $(K^s)^H$; it is a field. A normal $H$ yields a finite Galois extension.

For a nontransitive $T$, write it as a disjoint union of orbits. The associated algebra is the product of the fields attached to those orbits. Notice the reversal: disjoint union of Galois sets corresponds to product of algebras, whereas Cartesian product of sets corresponds to tensor product of algebras. This checks the variance of the construction and explains why a disconnected finite scheme has a product, not a direct sum, as its coordinate ring.

As a concrete example, let $K=\mathbf R$ and $K^s=\mathbf C$. The group $G_K$ has two elements. Its transitive finite sets are a singleton and the two-element set with complex conjugation interchanging the points. They correspond to $\mathbf R$ and $\mathbf C$. Every finite étale $\mathbf R$-algebra is consequently a product $\mathbf R^a\times\mathbf C^b$.

### 11.2 Recovering the absolute Galois group

Take the geometric point $\bar\eta=\operatorname{Spec}K^s\to\operatorname{Spec}K$. Its fiber on $\operatorname{Spec}A$ is naturally $\Phi(A)$. Every $\sigma\in G_K$ acts naturally on all such fibers, giving a continuous homomorphism

$$
G_K\longrightarrow\pi_1(\operatorname{Spec}K,\bar\eta).
$$

It is an isomorphism. Injectivity follows because a nontrivial $\sigma$ moves an element lying in some finite separable extension and hence moves a point of its Galois closure. Surjectivity follows by compatibility: an automorphism of all finite embedding sets determines compatible automorphisms of every finite Galois subextension, hence an element of $\varprojlim_L\operatorname{Gal}(L/K)=G_K$.

The topology agrees as well as the abstract group. The subgroup fixing the fiber of a finite Galois extension $L/K$ pointwise is $\operatorname{Gal}(K^s/L)$, and these subgroups form the usual Krull neighborhood basis. Hence the automorphism topology from the fiber functor is exactly the inverse-limit topology on $G_K$.

Thus finite separable extensions, finite Galois extensions, and finite continuous Galois sets are recovered without loss. Purely inseparable finite extensions do not appear as covers; they induce universal homeomorphisms and do not enlarge the separable closure. This is exactly why the fundamental group is an étale, rather than an algebraic, fundamental group.

### 11.3 Arithmetic and geometric Frobenius conventions

If $K=\mathbf F_q$, then $G_K\cong\widehat{\mathbf Z}$. The **arithmetic Frobenius** is

$$
\operatorname{Frob}_q^{\mathrm{arith}}\colon a\longmapsto a^q.
$$

Its inverse is the **geometric Frobenius**. Both topologically generate $G_K$, but they act with reciprocal eigenvalues in linear representations. We will always name the normalization rather than write an unqualified “Frobenius.”

The extension $\mathbf F_{q^n}/\mathbf F_q$ corresponds to the transitive $n$-element set on which arithmetic Frobenius acts as an $n$-cycle. The associated open subgroup is $n\widehat{\mathbf Z}$ and the quotient is $\mathbf Z/n\mathbf Z$. This makes the topology tangible: fixing $\mathbf F_{q^n}$ is an open condition, and the intersection of these fixing subgroups is trivial.

For a closed point $x$ on a scheme over $\mathbf F_q$, a choice of geometric point above $x$ and a path to the global basepoint embeds its decomposition group only up to conjugacy. Consequently its Frobenius in the global fundamental group is a conjugacy class. This is the group-theoretic source of the conjugacy invariance of Frobenius characteristic polynomials.

### 11.4 Function fields and arithmetic schemes

The comparison with an absolute Galois group extends from fields to integral schemes, but now one must impose the condition “unramified everywhere on the scheme.” Let $X$ be a connected normal integral scheme with function field $K$, and choose a separable closure $K^s$ and a geometric generic point $\bar\eta$. Restriction to the generic point sends a connected finite étale cover $Y\to X$ to a finite separable field extension $L/K$ inside $K^s$. Normality makes $Y$ the normalization of $X$ in $L$: a finite birational map between normal schemes is an isomorphism.

It follows that the structural map from the geometric generic point induces a continuous surjection

$$
G_K\longrightarrow\pi_1(X,\bar\eta).
$$

Its finite quotients are exactly the finite Galois extensions $L/K$ for which the normalization of $X$ in $L$ is finite étale over $X$. Surjectivity follows because every connected Galois cover supplies such an extension, and those covers are cofinal. Thus

$$
\pi_1(X,\bar\eta)
\cong
G_K/N_X,
$$

where $N_X$ is the intersection of the open normal subgroups corresponding to all finite extensions that extend étale over $X$. This formulation is valid without pretending that codimension-one valuations always detect every branch phenomenon. Finiteness of normalization is not automatic for a general noetherian scheme, and the source used for it throughout this book is Book 11, Chapter 3. Theorem 3.1 there proves that for a reduced noetherian Nagata scheme the normalization is finite, and more generally that the normalization of an irreducible component in a finite extension of its function field is finite; Theorem 3.2 proves that excellent rings are Nagata and that localizations and finite-type algebras over an excellent ring are again excellent, so that complete noetherian local rings, fields, and the usual arithmetic Dedekind bases all qualify; and Theorem 3.3 records the case invoked below, namely that a reduced scheme of finite type over an excellent Dedekind scheme has finite normalization, with properness and projectivity preserved. The identification of $Y$ with the normalization of $X$ in $L$ is a statement about a finite morphism exactly when $X$ falls under those hypotheses; for an $X$ outside them, finiteness must be assumed.

For a connected regular Dedekind scheme $S$ the quotient becomes concrete. For each closed point $v$, choose an extension of its discrete valuation to $K^s$. Let $D_v\subset G_K$ be the decomposition group and

$$
1\longrightarrow I_v\longrightarrow D_v
\longrightarrow G_{\kappa(v)}\longrightarrow1
$$

its inertia sequence. A finite separable extension of $K$ extends étale over $v$ exactly when every relevant inertia group acts trivially. Hence, for a nonempty open $U\subseteq S$,

$$
\pi_1(U,\bar\eta)
\cong
G_K\Big/
\overline{\left\langle I_v:\ v\in U\text{ closed}\right\rangle}^{\mathrm{normal}}.
$$

The bar means topological closure and the brackets mean normal generation. Inertia at a removed point is not killed: covers of $U$ may ramify there. For $S=\operatorname{Spec}\mathcal O_K$ of a number field, this says that finite quotients of $\pi_1(U)$ are precisely finite extensions unramified at every finite prime retained in $U$. Archimedean places are not points of this scheme and require separate conventions in arithmetic applications.

There are two proof directions. Given a finite étale cover of $U$, its generic extension is unramified at every closed point by base change to the corresponding DVR, so all $I_v$ act trivially. Conversely, if inertia is trivial at every retained point, the integral closure is a finite product of unramified extensions over each DVR and therefore is étale there. Since a finite morphism to a Dedekind scheme is tested at its generic and closed points, the normalization is finite étale over $U$. Passing over all finite Galois extensions identifies the profinite quotient.

For a smooth connected curve $U$ over a field, the same description applies after choosing its smooth proper compactification $C$ and using the valuations at closed points. A cover of $U$ is a separable function-field extension unramified at every point of $U$; ramification is permitted only at $C\setminus U$. The distinction between an arithmetic and a geometric curve then becomes visible in the quotient: over a nonclosed ground field the absolute Galois group of constants survives, while after separable closure only geometric function-field ramification remains.

## 12. The fundamental exact sequence

### 12.1 Statement and basepoints

Let $k$ be a field, choose a separable closure $k^s$, and let $X$ be a geometrically connected scheme of finite type over $k$. Choose a geometric point $\bar x\colon\operatorname{Spec}\Omega\to X_{k^s}$, where $\Omega$ is separably closed and the displayed map includes a chosen embedding $k^s\hookrightarrow\Omega$. The composite $\bar\eta_\Omega\colon\operatorname{Spec}\Omega\to\operatorname{Spec}k$ is the basepoint for the structural morphism. The chosen copy of $k^s$ identifies $\pi_1(\operatorname{Spec}k,\bar\eta_\Omega)$ with $G_k$. With these compatible basepoints there is an exact sequence of profinite groups

$$
1\longrightarrow\pi_1(X_{k^s},\bar x)
\longrightarrow\pi_1(X,\bar x)
\longrightarrow G_k
\longrightarrow1.
$$

Geometric connectedness is essential for surjectivity on the right. For example, if $X=\operatorname{Spec}L$ for a nontrivial finite separable extension $L/k$, then $X$ is connected but $X_{k^s}$ is disconnected; the image of $G_L\to G_k$ is an open proper subgroup when $L/k$ is not trivial.

Replacing $k^s$ by an algebraic closure does not change the group. Replacing basepoints changes the displayed sequence by compatible inner automorphisms. The kernel and quotient statements are therefore intrinsic.

If $X(k)\ne\varnothing$, choose $x\in X(k)$ and a geometric point above it. Functoriality of

$$
\operatorname{Spec}k\xrightarrow{x}X\longrightarrow\operatorname{Spec}k
$$

gives a continuous section $G_k\to\pi_1(X,\bar x)$. This section depends on the pointed rational point. Its existence turns the exact sequence into a semidirect product, but geometric monodromy generally remains nontrivial. A rational point splits arithmetic from geometric symmetry; it does not erase geometric coverings.

For a geometrically disconnected $X$, the correct replacement involves the action of $G_k$ on the finite set of geometric connected components. The image of $\pi_1$ in $G_k$ is the stabilizer of the chosen component. This observation diagnoses exactly why the right arrow in the displayed sequence can fail to be onto.

### 12.2 Proof by finite sets

The proof is clearest through what each term does to finite covers. Pullback along $X\to\operatorname{Spec}k$ sends a finite $G_k$-set to the corresponding constant-over-$X_{k^s}$ cover with arithmetic descent. Since $X_{k^s}$ is connected, a transitive $G_k$-set remains connected after pullback to $X$ exactly in the sense required by the surjectivity criterion; hence $\pi_1(X)\to G_k$ is surjective.

The composite

$$
\pi_1(X_{k^s})\longrightarrow\pi_1(X)\longrightarrow G_k
$$

is trivial because every cover pulled back from $k$ becomes constant over $k^s$. Thus the
geometric image lies in the kernel. There is no reverse “restriction” map from the kernel at this
stage; constructing one would already assume the desired exactness.

To see that this is an isomorphism, work at a finite level. The passage to a finite level is used
three times in this book — here, in §13.4, and in §14.3 — always in the same filtered-colimit
situation, so we prove it once.

**Limit descent lemma for covers.** Let $A_0$ be a ring, let $(A_i)_{i\in I}$ be a filtered
direct system of $A_0$-algebras with colimit $A=\varinjlim_iA_i$, and let $X_0$ be a
quasi-compact and quasi-separated $A_0$-scheme. Write $X_i=X_0\times_{A_0}A_i$ and
$X=X_0\times_{A_0}A$. Then pullback induces an equivalence

$$
\varinjlim_i\operatorname{FEt}(X_i)
\xrightarrow{\ \sim\ }
\operatorname{FEt}(X).
$$

Explicitly: every finite étale cover of $X$ is the pullback of a finite étale cover of some
$X_i$; for covers $Z_i,Z_i'$ of $X_i$ with pullbacks $Z,Z'$ to $X$, the natural map

$$
\varinjlim_{j\geq i}\operatorname{Hom}_{X_j}(Z_j,Z_j')
\longrightarrow\operatorname{Hom}_X(Z,Z')
$$

is bijective; and an action of a fixed finite group $G$ on a cover of $X$ by $X$-automorphisms
descends, with all of its composition relations, to some stage.

**Proof.** Two facts about a filtered colimit of rings $\varinjlim_iR_i$ are used throughout:
finitely many elements of the colimit all come from one index, and finitely many equations that
hold in the colimit already hold at one common larger index. Both follow from filteredness.

Choose a finite affine open cover $X_0=\bigcup_{a=1}^mU_a$. Quasi-separatedness makes each
$U_a\cap U_b$ quasi-compact, hence a finite union of affine opens, and the same for triple
intersections; fix such finite affine covers once and for all. The morphisms
$X_i\to X_0$ and $X\to X_0$ are affine, so these opens base change to compatible finite affine
covers of every $X_i$ and of $X$. For each affine $U$ in the resulting finite list,
$\mathcal O(U\times_{A_0}A_i)=\mathcal O(U)\otimes_{A_0}A_i$, and tensor products commute with
filtered colimits, so

$$
\mathcal O(U\times_{A_0}A)=\varinjlim_i\mathcal O(U\times_{A_0}A_i).
$$

Let $Z\to X$ be finite étale. It is affine, so $Z=\operatorname{Spec}_X\mathcal B$ for a finite
locally free $\mathcal O_X$-algebra $\mathcal B$. Refine the cover so that $\mathcal B$ is free on
each piece: over an affine open of $X$ a finite locally free sheaf is free on each member of a
covering by distinguished opens, and quasi-compactness selects finitely many of them. Each such
distinguished open is $D(g)$ for a single element $g$ of the corresponding ring, and those
finitely many elements come from one index $i_0$. Replacing $I$ by the cofinal subset
$\{i\geq i_0\}$ and $X_0$ by $X_{i_0}$ — which changes neither $A$ nor $X$ — we may assume that
the refined cover is already the base change of a finite affine cover of $X_0$, with finite
affine covers of its double and triple intersections.

Write $R_a=\mathcal O(U_a\times_{A_0}A)$ for the pieces of the refined cover. On $U_a$ the algebra
$\mathcal B$ is free with basis $b_{a,1},\ldots,b_{a,n_a}$, and its multiplication is recorded by
structure constants $c^{\,l}_{a;jk}\in R_a$ with $b_{a,j}b_{a,k}=\sum_lc^{\,l}_{a;jk}b_{a,l}$,
together with the coordinates of the unit. Commutativity, associativity and the unit axioms are
finitely many polynomial identities among these finitely many elements. Étaleness is, by §3.4,
invertibility of the determinant
$\delta_a=\det\bigl(\operatorname{Tr}(b_{a,j}b_{a,k})\bigr)_{j,k}\in R_a$, which is the single
equation $\delta_au_a=1$ for one further element $u_a$. On each of the finitely many affine opens
covering $U_a\cap U_b$ the two restrictions of $\mathcal B$ are identified by an invertible matrix
over the corresponding ring; that this matrix is an algebra isomorphism, that it has an inverse,
and that the cocycle identity holds on the finitely many affine opens covering the triple
intersections, are again finitely many polynomial identities among finitely many elements.

Choose one index $i$ at which all of these finitely many elements are defined and all of these
finitely many identities hold. Over $X_i$ they define a free algebra of rank $n_a$ on each piece
of the cover, with invertible trace determinant, together with a cocycle of algebra isomorphisms
on the overlaps. Relative spectra of quasi-coherent algebras glue along a Zariski cover, so this
produces a finite $X_i$-scheme $Z_i$, and §3.4 makes it étale. By construction the pullback of
$Z_i$ to $X$ has the same basis, the same structure constants and the same gluing matrices as
$Z$, so $Z_i\times_{X_i}X\simeq Z$.

Morphisms are handled identically. After passing to a common refinement of the two covers, a
morphism $Z\to Z'$ over $X$ is on each piece an algebra homomorphism between free modules, that
is, a matrix of elements of the relevant ring subject to finitely many identities; it therefore
comes from some stage and defines a morphism there. Two morphisms defined over $X_i$ whose
pullbacks to $X$ agree have matrices with equal images in the colimits, hence agree over some
$X_j$ with $j\geq i$. This is the asserted bijection on Hom sets, and applying it to isomorphisms
and their inverses descends isomorphisms. Finally, an action of a finite group $G$ is a finite
family $(\rho_\sigma)_{\sigma\in G}$ of automorphisms subject to the finitely many identities
$\rho_\sigma\rho_\tau=\rho_{\sigma\tau}$ and $\rho_1=\operatorname{id}$, so it descends together
with them. $\square$

Now apply the lemma. The scheme $X$ is of finite type over a field, hence noetherian and in
particular quasi-compact and quasi-separated, and $k^s$ is the filtered colimit of the finite
separable subextensions $k'/k$. Any finite étale cover $Z$ of $X_{k^s}$ therefore descends to
$Z'/X_{k'}$ for some finite separable $k'/k$. Enlarge $k'$ to a finite Galois extension. Form over
$X_{k'}$ the fiber product of the finitely many conjugates $\sigma Z'$. Permuting the factors
gives canonical descent data to $X$; effective descent produces a finite étale cover $W/X$.
After base change to $k^s$, the projection from $W_{k^s}$ to the factor $Z$ is a morphism. The
connected component of $W_{k^s}$ containing a chosen compatible point therefore dominates the
chosen component of $Z$. By the injectivity criterion of §8.3, covers obtained from $X$ separate
every finite quotient of $\pi_1(X_{k^s})$, so the map from the geometric group into
$\pi_1(X)$ is injective. Its image lies in the kernel; the following descent argument proves that
the two are equal.

For middle exactness, let a finite $\pi_1(X)$-set be trivial on the geometric subgroup, and let
$Y/X$ be its cover. Over $X_{k^s}$ it is a constant disjoint union indexed by a finite set $A$.
The descent datum inherited from $Y$ acts on these constant sheets. On every finite subextension
over which the trivialization is defined, the datum is a permutation cocycle; passing to the
limit gives a continuous action of $G_k$ on $A$. Conversely that action supplies the same
cocycle on the constant cover. Finite étale descent over $k^s/k$ identifies it with a finite
étale $k$-scheme $T$, and full faithfulness identifies $Y$ with $X\times_kT$. Thus a finite
$\pi_1(X)$-set is trivial on the geometric image exactly when it factors through $G_k$. Applied
to every finite quotient, this says that the image of the geometric group is precisely the
kernel.

The argument reveals the role of the finite-type hypothesis: quasi-compactness reduces the cover and all of its gluing maps to finitely much presentation data, which descend to one finite subextension. It also shows that exactness is a statement about all finite covers, not about abstract elements alone. Broader versions are possible under suitable quasi-compactness hypotheses, but the displayed form is the one needed here.

### 12.3 Arithmetic and geometric monodromy

Given a finite étale cover $Y\to X$, the action

$$
\rho_Y\colon\pi_1(X,\bar x)\longrightarrow
\operatorname{Sym}(Y_{\bar x})
$$

is its **arithmetic monodromy**. Restriction to $\pi_1(X_{k^s},\bar x)$ is its **geometric monodromy**. The geometric image is normal in the arithmetic image, and the quotient is a finite quotient of $G_k$.

Conversely, $G_k$ acts by outer automorphisms on $\pi_1(X_{k^s})$: lift $\sigma\in G_k$ to $\pi_1(X)$ and conjugate the kernel. Different lifts differ by an element of the kernel, so the resulting automorphism is well defined only modulo inner automorphism. On isomorphism classes of geometric covers this gives the continuous Galois action by transport of structure. A geometric cover descends to $k$ only when it admits compatible descent data; invariance of its isomorphism class is necessary but can leave an automorphism obstruction.

For a cover $Z\to X_{k^s}$, each $\sigma\in G_k$ produces a conjugate cover $Z^\sigma$. Continuity means that $Z$ and all of its defining maps descend to some finite $k'/k$, so an open subgroup of $G_k$ fixes its isomorphism class. To descend all the way to $k$, one needs isomorphisms $Z^\sigma\to Z$ whose composites satisfy the cocycle law. When the deck group is nontrivial, arbitrary choices of these isomorphisms can fail that law. This is the geometric content hidden behind the phrase “Galois-stable cover.”

For a connected cover $Y\to X$, let $G_{\mathrm{arith}}$ and $G_{\mathrm{geom}}$ be the images of the arithmetic and geometric fundamental groups in the symmetric group of the fiber. Exactness gives

$$
G_{\mathrm{geom}}\triangleleft G_{\mathrm{arith}},
\qquad
G_{\mathrm{arith}}/G_{\mathrm{geom}}
\ \text{a quotient of }G_k.
$$

Geometric connectedness of $Y_{k^s}$ is equivalent to transitivity of $G_{\mathrm{geom}}$, a stronger condition than connectedness of $Y$, which asks for transitivity of $G_{\mathrm{arith}}$. An arithmetically connected cover can split into conjugate components geometrically; a field extension pulled back from $k$ is the simplest example.

If the exact sequence has a section—for instance, a $k$-rational point together with a compatible geometric lift supplies one—then

$$
\pi_1(X,\bar x)\cong\pi_1(X_{k^s},\bar x)\rtimes G_k
$$

relative to that section. Different rational points or paths can give nonconjugate sections; no splitting should be asserted without such data.

### 12.4 The relative homotopy sequence

The field exact sequence is one instance of a relative principle. Let $f:X\to S$ be a proper smooth morphism of connected locally noetherian schemes with geometrically connected fibers. Choose a geometric point $\bar x$ of $X$, let $\bar s=f(\bar x)$, and write $X_{\bar s}$ for the geometric fiber. Then

$$
\pi_1(X_{\bar s},\bar x)
\longrightarrow
\pi_1(X,\bar x)
\xrightarrow{f_*}
\pi_1(S,\bar s)
\longrightarrow1
$$

is exact. Unlike the exact sequence over a field, no $1$ is placed at the left: the fiber map need not be injective in this general relative statement.

Surjectivity on the right has a transparent cover criterion. If $S'\to S$ is connected finite étale, then $X\times_SS'\to S'$ is proper smooth with geometrically connected fibers. Since $S'$ is connected and the morphism is open and surjective, its total space is connected: any decomposition into two open-and-closed pieces would give, fiber by fiber, a decomposition of a geometrically connected fiber, and openness would propagate the contradiction over $S'$. Thus every connected cover of $S$ remains connected on $X$, so $f_*$ is surjective.

For exactness in the middle, one direction is immediate: a loop lying in a geometric fiber acts trivially on every cover pulled back from $S$. Conversely, let $Y\to X$ be a connected finite étale cover on which the image of $\pi_1(X_{\bar s})$ acts trivially. Then

$$
Y_{\bar s}\cong\coprod_{a\in A}X_{\bar s}
$$

for a finite set $A$. We record why the relative connected components used now form a finite
étale scheme. For a proper, flat, finitely presented morphism with geometrically reduced fibers,
an open-and-closed component of one geometric fiber extends uniquely after an étale neighborhood
of the base point. On a finite affine Čech cover, the component is an idempotent in the kernel of
the first Čech differential. The equation $e^2-e=0$ has invertible derivative $2e-1$ at an
idempotent, so the standard-étale lifting argument extends it; flatness keeps it in the Čech
kernel. Properness makes the complement closed over the base, so after shrinking the étale
neighborhood the lifted idempotent cuts every fiber into the corresponding two open-and-closed
pieces. Uniqueness follows because two idempotents agreeing on one geometrically reduced fiber
agree near it. Repeating for the finitely many components and descending the permutations on
overlaps constructs a separated étale scheme $\pi_0(Y/S)$. Its fibers are finite, and properness
prevents a component from disappearing, so it is proper and quasi-finite over $S$, hence finite
étale.

Apply this construction to $Y/S$ and denote the resulting finite étale scheme by $T\to S$. The
natural map $Y\to X\times_ST$ is an isomorphism on the chosen geometric fiber. Both sides are
finite étale over $X$, so the isomorphism locus is open and closed; connectedness and fiberwise
degree show it is an isomorphism everywhere. Hence $Y$ is pulled back from $S$. In the language
of finite actions, every finite $\pi_1(X)$-set on which the fiber subgroup acts trivially factors
through $\pi_1(S)$, which is exactly middle exactness.

The argument works more generally for proper flat morphisms with geometrically connected and geometrically reduced fibers under hypotheses ensuring that relative components form a finite étale scheme. The proper smooth statement is the reusable version here: its geometric inputs are explicit and stable under base change.

A section $e:S\to X$ splits $f_*$ after compatible basepoints, but it does not generally make the first arrow injective. It gives

$$
\pi_1(X,\bar x)
\cong
\ker(f_*)\rtimes\pi_1(S,\bar s),
$$

while exactness identifies $\ker(f_*)$ only as the image, hence a quotient, of $\pi_1(X_{\bar s})$. The distinction is essential in a general base family.

### 12.5 Exactness criteria and failure modes

The relative proof isolates three separate conditions. Geometric connectedness of the fibers gives surjectivity onto the base group. Geometric reducedness prevents infinitesimal multiplicity from corrupting components. Properness ensures that a component visible in one fiber extends across the base rather than escaping through a boundary. Smoothness conveniently supplies flatness, geometric reducedness, and openness all at once.

If fibers are merely connected over their residue fields, surjectivity can fail after a separable extension disconnects them. The finite-field example $X=\operatorname{Spec}L\to\operatorname{Spec}k$ for a nontrivial finite separable $L/k$ already shows the issue: the source is connected, but the geometric fiber is a finite disconnected set, and $G_L\to G_k$ has proper image.

If properness is removed, a cover can have trivial monodromy on one fiber without descending from the base because its behavior changes at infinity. Families of punctured curves exhibit precisely this phenomenon. Adding a relative normal-crossings compactification repairs part of the statement only after one controls ramification at the boundary, usually through tame or prime-to-residue-characteristic quotients.

If geometric reducedness is removed, connected components can merge through nilpotents. The relative component object need no longer be étale over the base, so the descent step in the proof breaks. Flatness by itself does not rule this out.

Finally, exactness is not the same as local constancy of the fiber group. The sequence identifies the kernel of $\pi_1(X)\to\pi_1(S)$ as an image, but comparing fundamental groups of two different geometric fibers requires a specialization or transport theorem. That further question is the subject of Chapter 14.

## 13. Changing the ground field

### 13.1 Separable extensions

Let $K/k$ be an algebraic separable extension embedded in $k^s$, and let $X/k$ be geometrically connected and of finite type. Put $G_K=\operatorname{Gal}(k^s/K)$ when $K$ is viewed inside $k^s$; for an infinite extension this means the closed subgroup fixing $K$. Compatible basepoints give a commutative diagram with exact rows:

$$
\begin{array}{ccccccccc}
1&\to&\pi_1(X_{k^s})&\to&\pi_1(X_K)&\to&G_K&\to&1\\
 &&\Vert&&\downarrow&&\downarrow\\
1&\to&\pi_1(X_{k^s})&\to&\pi_1(X)&\to&G_k&\to&1.
\end{array}
$$

It follows that

$$
\pi_1(X_K)\xrightarrow{\sim}
\pi_1(X)\times_{G_k}G_K.
$$

In particular, $\pi_1(X_K)\to\pi_1(X)$ is injective with image the inverse image of $G_K$. If $K/k$ is finite separable, this image is open of index $[K:k]$ after the usual interpretation when $K/k$ is not Galois. If $K/k$ is infinite algebraic, the image is closed and need not be open.

The index assertion can be seen without group manipulation. The cover $X_K\to X$ attached to a finite separable $K/k$ has degree $[K:k]$ and is connected because $X$ is geometrically connected. The stabilizer of a chosen geometric lift is precisely the image of $\pi_1(X_K)$, so the orbit–stabilizer formula gives the index. Normality is equivalent to $K/k$ being Galois.

### 13.2 Algebraic extensions and exact images

The preceding formula is the clean image/kernel statement: the geometric kernel does not change, while the arithmetic quotient shrinks from $G_k$ to $G_K$. It can also be read categorically. A cover of $X$ pulled back to $X_K$ has monodromy obtained by restricting the $\pi_1(X)$-action to the preimage of $G_K$.

If $K/k$ is finite Galois, then $\pi_1(X_K)$ is an open normal subgroup of $\pi_1(X)$ and

$$
1\longrightarrow\pi_1(X_K)\longrightarrow\pi_1(X)
\longrightarrow\operatorname{Gal}(K/k)\longrightarrow1.
$$

For finite nonnormal $K/k$, the subgroup is open but generally not normal; its conjugacy class is determined without choosing the embedding $K\hookrightarrow k^s$.

Suppose $Y\to X$ is a connected finite étale cover and $K/k$ is algebraic separable. The connected components of $Y_K$ correspond to the orbits of

$$
\pi_1(X_K)=\pi_1(X)\times_{G_k}G_K
$$

on $Y_{\bar x}$. Scalar extension can therefore disconnect an arithmetically connected cover by shrinking the acting group, but it does not change the underlying finite geometric fiber. If $Y$ is geometrically connected, the geometric subgroup already acts transitively, so every algebraic separable base extension remains connected.

One must not extrapolate this to arbitrary transcendental field extensions. Invariance of the full geometric fundamental group under extension of algebraically closed fields requires additional hypotheses in wild, nonproper situations. The algebraic-separable statement above is the one used for arithmetic base change.

### 13.3 Purely inseparable invariance

If $K/k$ is purely inseparable, $\operatorname{Spec}K\to\operatorname{Spec}k$ is a universal homeomorphism. Base change induces an equivalence

$$
\operatorname{FEt}(X)\xrightarrow{\sim}\operatorname{FEt}(X_K)
$$

for every $k$-scheme $X$, and hence an isomorphism of fundamental groups after compatible basepoints. More generally, finite étale covers are invariant under universal homeomorphisms.

Here is the local proof of that invariance. A universal homeomorphism $q:X'\to X$ is integral,
surjective, and radicial. It gives a bijection on ordinary points, and the residue-field extension
at corresponding points is purely inseparable; hence chosen separable closures of the two residue
fields coincide. Standard étale charts show that pullback gives an equivalence between the
pointed étale neighborhoods at corresponding geometric points. Indeed, a pointed chart is a
simple-root equation, purely inseparable residue extension neither creates nor identifies a
separable root, and formal étaleness gives the unique lift in both directions. Passing to the
filtered limits, the two strict local neighborhoods have the same finite étale splitting data. A
finite étale cover on either one is therefore a finite disjoint union of copies of that
neighborhood, with the copies labeled by the same finite geometric fiber.

Choose actual pointed étale neighborhoods far enough down these filtered systems to split a given
finite cover and all of its finitely many transition maps. On pairwise overlaps, the cover is
described by locally constant permutations of these labels. Because $q$ is universally bijective,
it induces a bijection on the open-and-closed subsets of every overlap:
an open-and-closed subset pulls back, and its inverse image has a unique open-and-closed image since
integral surjections are closed and the underlying map is a homeomorphism. Thus exactly the same
permutation cocycles occur over $X$ and $X'$. Effective étale descent glues them, and the same
argument for equivariant maps proves full faithfulness. This gives the claimed equivalence. For
an arbitrary integral radicial map, each finite cover and its finite cocycle descend to a finite
radicial stage, so the finite-stage argument applies.

This does not make purely inseparable maps étale. It says the opposite sort of thing: radicial changes are invisible to étale covering theory. The Frobenius map on a characteristic-$p$ scheme can be a universal homeomorphism while having zero differential and being very far from étale.

### 13.4 Extension of algebraically closed fields

Algebraic extensions and purely inseparable extensions are not the only base changes encountered in geometry. Suppose $k\subset K$ is an extension of algebraically closed fields and $X$ is a connected proper scheme of finite type over $k$. Then pullback induces an equivalence

$$
\operatorname{FEt}(X)\xrightarrow{\sim}\operatorname{FEt}(X_K)
$$

and therefore an isomorphism

$$
\pi_1(X_K,\bar x_K)\xrightarrow{\sim}\pi_1(X,\bar x).
$$

The point is not merely that a cover over $K$ uses finitely many coefficients and hence descends to a finitely generated $k$-subalgebra. Such a descent initially lives in a family over a positive-dimensional parameter space, and a chosen special fiber might acquire extra components. Here is the rigidity argument that properness supplies.

First replace $X$ by $X_{\mathrm{red}}$; finite étale covers are unchanged by a nilpotent
thickening. Since $k$ is algebraically closed, it is perfect, so this reduced finite-type scheme
is geometrically reduced. The field $K$ is the filtered union of its finitely generated
$k$-subalgebras $A_i$, all of them domains, and $X$ is noetherian, hence quasi-compact and
quasi-separated. The limit descent lemma of §12.2, applied with $A_0=k$, $X_0=X$ and the system
$(A_i)$, therefore spreads a cover $Y_K/X_K$ and all its structure maps to a finite étale
cover $Y_S\to X\times_kS$ with $S=\operatorname{Spec}A_i$ for some $i$; such an $S$ is a nonempty
integral, hence connected, affine $k$-scheme of finite type whose function field is embedded in
$K$. Shrinking $S$ preserves finiteness and étaleness. The projection
$X\times_kS\to S$ is proper and flat with geometrically connected, geometrically reduced fibers,
so its relative component scheme is finite étale by the argument of §12.4.

We use the following consequence, whose proof is part of the same component calculation. If
$Y_1,Y_2$ are finite étale over $X\times_kS$, then

$$
\underline{\operatorname{Isom}}_{X\times S}(Y_1,Y_2)\longrightarrow S
$$

is finite étale. A map is its graph, an open-and-closed union of components of
$Y_1\times_{X\times S}Y_2$ whose projection to $Y_1$ is an isomorphism. The relative component
schemes of $Y_1$, $Y_2$, and their fiber product are finite étale over $S$. Their finite power-set
schemes parameterize unions of components, while the degree-one, bijection, and inverse conditions
select open-and-closed subschemes. The graph condition therefore represents the relative Hom
functor by a finite étale $S$-scheme, and imposing the inverse condition gives the displayed Isom
scheme. This construction may be checked after an étale base change of $S$ splitting the relative
component schemes, where it is ordinary finite-set algebra; descent removes that auxiliary
base change.

Choose a closed point $s\in S(k)$ and put $Z=Y_s$. The relative Isom scheme between $Y_S$ and
$Z\times_kS$ is finite étale over $S$ and has a point over $s$. Let $T$ be the connected component
of this Isom scheme through that point. Then $T\to S$ is finite étale and surjective and carries
the universal isomorphism $Y_T\simeq Z\times_kT$. The original map
$\operatorname{Spec}K\to S$ lifts to $T$ because $K$ is algebraically closed and the relevant
finite étale fiber is nonempty. Hence $Y_K\simeq Z_K$, proving essential surjectivity.

For full faithfulness, apply the relative Hom construction directly over $\operatorname{Spec}k$
to two finite étale covers of $X$. It is a finite étale $k$-scheme, hence a finite disjoint union
of $k$-points because $k$ is algebraically closed. Extension to algebraically closed $K$ neither
creates nor identifies its points, so the two Hom sets agree. No smoothness of $X$ has been
inserted: reduction supplied geometric reducedness, and properness supplied the relative
component theorem.

Properness cannot simply be deleted in positive characteristic. On an open variety, wild ramification at a boundary can depend on transcendental parameters introduced by the larger algebraically closed field. The full fundamental group may therefore change. For smooth curves, prime-to-$p$ covers are much more rigid: after compactification their ramification is tame, and the prime-to-$p$ quotient is invariant under algebraically closed extension. The full wild quotient requires separate hypotheses and is not claimed invariant here.

This theorem clarifies terminology. If $X/k$ is geometrically connected, one may compute its **geometric fundamental group** after any chosen algebraic closure of $k$; algebraic closures differ only by noncanonical field isomorphism, and purely inseparable changes are invisible. For proper $X$, even enlarging that algebraically closed field transcendently does not alter the group. For nonproper $X$ in positive characteristic, the chosen algebraically closed base must remain visible whenever the wild quotient matters.

## 14. Specialization over henselian discrete valuation rings

### 14.1 The direction of specialization

Let $R$ be a henselian DVR with fraction field $K$, residue field $k$, geometric generic point $\bar\eta$, and geometric special point $\bar s$. Suppose $f\colon X\to\operatorname{Spec}R$ is proper and smooth with geometrically connected fibers. After choosing a specialization of geometric points, there is a continuous homomorphism

$$
\operatorname{sp}\colon
\pi_1(X_{\bar\eta},\bar x_{\bar\eta})
\longrightarrow
\pi_1(X_{\bar s},\bar x_{\bar s}).
$$

The arrow goes from generic to special. The reason is contravariance of the classification: after
strict henselization and completion, a finite étale cover of the special fiber extends across the
proper family and can then be restricted to the geometric generic fiber. Proper base-field
invariance identifies that generic fiber with the original one. A functor from special covers to
generic covers induces a homomorphism from the generic fundamental group to the special one.

Changing the chosen specialization path conjugates the map. Its surjectivity and its induced maps on canonical quotients do not depend on that choice.

### 14.2 Smooth families

Smoothness supplies the local deformation theory. A finite étale cover of $X_{\bar s}$ lifts uniquely across nilpotent thickenings of the special fiber, because finite étale morphisms have unique infinitesimal lifting. Over the completed strict henselization of $R$, these compatible thickenings give a formal finite étale cover near the special fiber.

This local statement should not be overstated. If $X/R$ is smooth but not proper, a cover defined near the special fiber need not algebraize over all of $X$, and behavior at a missing boundary can change under specialization. A global homomorphism between full fundamental groups then requires extra structure, such as a proper smooth compactification with controlled normal-crossings boundary, and often naturally concerns tame rather than all covers.

Thus “smooth” explains rigidity and local lifting; “proper” prevents the lifted sheets from escaping through infinity. The two hypotheses play different roles.

### 14.3 Proper smooth families

We first prove the extension input rather than hide it in the word “proper.”

**Finite étale existence lemma.** Let $A$ be a complete noetherian local ring, let $I$ be its
maximal ideal, and let $V$ be proper and of finite presentation over $A$. If
$V_n=V\times_AA/I^{n+1}$, restriction gives an equivalence

$$
\operatorname{FEt}(V)\xrightarrow{\sim}
\varprojlim_n\operatorname{FEt}(V_n),
$$

and hence an equivalence $\operatorname{FEt}(V)\simeq\operatorname{FEt}(V_0)$.

To prove the lemma, nilpotent invariance first lifts a cover $Z_0/V_0$ uniquely to compatible
covers $Z_n/V_n$; it also lifts every morphism uniquely. Write
$\mathcal A_n=(Z_n)_*\mathcal O_{Z_n}$. These are compatible finite locally free
$\mathcal O_{V_n}$-algebras. We now establish the only effectivity point needed here. A compatible
system of finite locally free sheaves on the thickenings of a proper $A$-scheme comes from a
unique coherent sheaf on $V$. In the projective case, embed $V$ in some $\mathbf P^r_A$, so that
every $V_n$ is a closed subscheme of $\mathbf P^r_{A/I^{n+1}}$. The vanishing input is Serre's
theorem in the form proved in Book 8, §6.2: for $A$ noetherian and $\mathcal F$ coherent on
$\mathbf P^r_A$ there is an $n_0$ with $H^i(\mathbf P^r_A,\mathcal F(n))=0$ for all $i>0$ and
$n\geq n_0$, and with $\mathcal F(n)$ globally generated in that range; the same statement then
holds on every projective noetherian $A$-scheme, in particular on each $V_n$, and the
line-bundle calculation behind it is the one of Book 15, §2.2. A finite set of twists therefore
generates the special-fiber sheaf. The kernel of $\mathcal A_n\to\mathcal A_{n-1}$ is
$\mathcal A_0\otimes_{\mathcal O_{V_0}}(I^n\mathcal O_V/I^{n+1}\mathcal O_V)$, so the graded
object assembled from these kernels is a finitely generated graded module over the finitely
generated graded $\mathcal O_{V_0}$-algebra $\operatorname{gr}_I\mathcal O_V$; applying the
vanishing theorem to the finitely many coherent sheaves generating it gives one bound valid for
every $n$, and the exact sequences for successive thickenings together with Nakayama then show
that the corresponding spaces of sections form compatible finite $A/I^{n+1}$-modules. Their inverse limits
are finite $A$-modules. The direct sum over the twists is a finitely generated graded module over
the homogeneous coordinate ring; finite generation follows from the multiplication maps in all
sufficiently large degrees. Sheafification gives the desired coherent sheaf, and reduction of its
graded sections recovers every member of the system. Applying the same construction to internal
Hom identifies morphisms with inverse limits of their reductions.

For a proper $V$, the reduction to that projective calculation is a noetherian induction, which
we spell out. The modification it uses is Chow's lemma in the form proved in Book 15, §2.4 and
listed in that book's reusable package in §15.2. Its hypotheses hold here without further
comment. The base $S=\operatorname{Spec}A$ is noetherian and affine; $V\to S$ is proper, hence
separated and of finite type; and over an affine noetherian base every affine open of a
finite-type scheme is quasi-projective, which is precisely the covering hypothesis that Book 15
singles out as automatic for affine $S$. The lemma therefore yields an $S$-morphism
$p\colon V'\to V$ that is projective and surjective, together with a dense open
$V^\circ\subseteq V$ containing every generic point of $V$ over which $p$ is an isomorphism; and
since $V$ is proper over $S$, the scheme $V'$ is projective over $S$. The same clause applies at
every later stage of the induction, because the error terms below are supported on closed
subschemes of $V$, which are again proper over the same affine noetherian base. Proper direct image commutes with the adic
inverse limit: on a finite affine cover this is the assertion that completion commutes with the
cohomology of the finite Čech complex, proved by applying the Artin–Rees lemma to its images and
kernels. Algebraize the pulled-back system on $V'$ by the projective calculation and push it
forward. The comparison with the original system is an isomorphism on the chosen dense opens;
its kernel and cokernel are supported on proper closed subsets. Apply the induction hypothesis to
those two systems and use the resulting exact sequences to algebraize the original one. The same
argument applied to the graph, kernel, and cokernel of a compatible system of maps proves full
faithfulness. Support dimension drops at every induction step, so the process terminates. This
proves existence and full faithfulness for coherent sheaves in the particular adic system at hand.

Apply this result to the $\mathcal A_n$. Full faithfulness also algebraizes their multiplication
and unit. Associativity, commutativity, and the unit identities hold because they hold modulo
every $I^{n+1}$ and $A$ is separated. The resulting coherent algebra $\mathcal A$ is finite
locally free: the non-locally-free locus is closed, and properness would force any nonempty such
locus to meet the closed fiber, where it is empty. The same argument applied to
$\Omega_{\mathcal A/\mathcal O_V}$ shows that it vanishes. Thus
$Z=\operatorname{Spec}_V\mathcal A$ is finite étale. The inverse-limit description of morphisms
proves full faithfulness and uniqueness. This proves the lemma.

Return to the henselian DVR $R$. Replace it by its strict henselization and then complete; write
$\widehat R^{\mathrm{sh}}$ for the resulting complete DVR. Its residue field is the chosen
separable closure of $k$. The lemma extends every $Z_{\bar s}\to X_{\bar s}$ uniquely over
$X_{\widehat R^{\mathrm{sh}}}$. Restriction to an algebraic closure of the completed fraction
field gives a functor

$$
\operatorname{FEt}(X_{\bar s})\longrightarrow
\operatorname{FEt}(X_{\bar\eta}).
$$

Here §13.4 identifies the geometric generic fundamental group before and after completion, because
the generic fiber is proper and the two chosen algebraically closed fields have a common
algebraically closed overfield. Taking automorphisms of fiber functors reverses the displayed
arrow and yields $\operatorname{sp}$. A morphism between two proper smooth families gives a
commutative specialization square, up to the path-induced conjugacies.

Smoothness and geometric connectedness now prove surjectivity. The extension of a connected
special-fiber cover is again proper smooth. Its relative component scheme over the strictly
henselian complete DVR is finite étale. Its special fiber is a singleton, so the component scheme
is the base itself; consequently its geometric generic fiber is connected. The connected-cover
criterion of §8.3 says exactly that $\operatorname{sp}$ is surjective.

Full injectivity is subtler. If the residue characteristic is $p>0$, new $p$-primary covers may exist generically and disappear upon specialization. What is invariant is the prime-to-$p$ quotient, and for a family of relative dimension at most one the invariance is complete:

$$
\operatorname{sp}^{(p')}\colon
\pi_1(X_{\bar\eta})^{(p')}
\xrightarrow{\sim}
\pi_1(X_{\bar s})^{(p')}.
$$

Here the superscript denotes the maximal profinite quotient detected by finite groups of order
prime to $p$; when the residue characteristic is $0$ every finite group qualifies and the
displayed map is the full specialization map.

The restriction on the relative dimension is worth a word at once, since it is dictated by one
step of the proof. The argument builds a finite normal model of the generic cover over the
whole family and must then recognize it as étale from its behavior in codimension one; the model
lives on the total space, whose dimension exceeds the relative dimension by one. Over a discrete
valuation ring a relative curve gives a surface, and on a regular surface that recognition step
is a theorem, proved outright below from the depth theory of Book 11, Chapter 14: two-dimensional
normal local rings have depth two, and depth two over a regular local ring of the same dimension
forces freeness, which supplies the flatness, after which a trace determinant supplies the rest.
This book develops purity in
that dimension and no further, because that is the dimension its subject calls for: §14.5 and
§15.6 apply the theorem to smooth proper relative curves, and nothing later in the book asks for
a larger relative dimension.

So assume from now on that $X\to\operatorname{Spec}R$ is proper and smooth of relative dimension
at most one with geometrically connected fibers. The local input is the following.

**Purity lemma for surfaces.** Let $V$ be a connected regular noetherian scheme all of whose
local rings have dimension at most two, and let $\pi\colon W\to V$ be a finite morphism with $W$
normal such that every irreducible component of $W$ dominates $V$. If $\pi$ is étale over every
point of $V$ of codimension at most one, then $\pi$ is étale.

**Proof.** A regular scheme is normal, and a connected normal noetherian scheme is integral, so
$V$ is integral; write $K$ for its function field. Likewise $W$ is normal and noetherian, hence a
finite disjoint union of integral normal schemes, so every local ring $\mathcal O_{W,w}$ is a
normal noetherian local domain. Étaleness may be tested pointwise on $V$. Let $v\in V$. If
$\pi^{-1}(v)=\varnothing$ there is nothing to prove, and if $v$ has codimension at most one the
hypothesis applies directly; so assume $\dim\mathcal O_{V,v}=2$ and $\pi^{-1}(v)\neq\varnothing$.
Put $A=\mathcal O_{V,v}$, a two-dimensional regular local ring, and
$B=(\pi_*\mathcal O_W)_v=\prod_{w\mapsto v}\mathcal O_{W,w}$, a finite $A$-algebra because $\pi$
is finite.

Fix $w$ above $v$. Then $\mathcal O_{W,w}$ is a local $A$-algebra, module-finite over $A$ as a
direct factor of $B$, and a normal domain. The generic point $\zeta$ of the component of $W$
through $w$ maps to the generic point of $V$ by hypothesis, so the composite
$A\hookrightarrow K\to\kappa(\zeta)$ is injective and hence $A\to\mathcal O_{W,w}$ is injective.
By the remark following Book 11, Theorem 14.30, injectivity forces
$\dim\mathcal O_{W,w}=\dim A=2$, so that theorem applies exactly as stated: a module-finite local
algebra over a two-dimensional regular local ring which is a normal domain of dimension two is
free. Thus each $\mathcal O_{W,w}$, and therefore $B$, is a free $A$-module; write $n$ for its
rank. Equivalently, one may read the same conclusion through depth: Book 11, Theorem 14.23 gives
$\operatorname{depth}\mathcal O_{W,w}\geq2$ because it is a normal local domain of dimension two,
depth is insensitive to whether it is computed over $A$ or over $\mathcal O_{W,w}$, and Book 11,
Theorem 14.27 makes a finite module of depth two over a two-dimensional regular local ring free.

Choose an $A$-basis of $B$ and let $\delta\in A$ be the determinant of the trace pairing
$(x,y)\mapsto\operatorname{Tr}_{B/A}(xy)$ in that basis; a change of basis multiplies $\delta$ by
the square of a unit, so both the vanishing and the invertibility of $\delta$ are intrinsic. The
generic point of $V$ has codimension zero, so $\pi$ is étale there and $B\otimes_AK$ is a finite
étale $K$-algebra; by §3.4 its trace pairing is perfect and $\delta\neq0$. Suppose $\delta$ were
not a unit. A prime of $A$ minimal over $\delta A$ has height at most one by Krull's principal
ideal theorem and height at least one because $\delta\neq0$ in the domain $A$; so some height-one
prime $\mathfrak p$ contains $\delta$. It corresponds to a point of $V$ of codimension one, over
which $\pi$ is étale by hypothesis, so $B_{\mathfrak p}$ is finite étale over $A_{\mathfrak p}$
and §3.4 makes $\delta$ invertible in $A_{\mathfrak p}$ — contradicting
$\delta\in\mathfrak pA_{\mathfrak p}$. Hence $\delta\in A^\times$, the trace pairing of $B$ over
$A$ is perfect, and §3.4 makes $B$ finite étale over $A$. Since $\pi$ is finite over the
noetherian $V$, hence of finite presentation, and since flatness and unramifiedness at $w$ are
conditions on $\mathcal O_{W,w}$ over $\mathcal O_{V,v}$, this says precisely that $\pi$ is étale
at every point above $v$. As $v$ was arbitrary, $\pi$ is étale. $\square$

Note what the hypotheses do. Normality of $W$ is what produces depth two and hence freeness; it
is not a side condition, and no version of the lemma survives its removal. Dominance of the
components is what makes the generic trace determinant nonzero.

Now let $Y_{\bar\eta}\to X_{\bar\eta}$ be a connected Galois cover with group $G$ of order prime
to $p$; its degree is $|G|$. Write $R'=\widehat R^{\mathrm{sh}}$, $K'=\operatorname{Frac}R'$, and
$\bar\eta=\operatorname{Spec}\overline{K'}$. If the relative dimension is zero, then $X$ is
$\operatorname{Spec}R$ itself and both groups are trivial, so assume the relative dimension is
one.

Since $\overline{K'}$ is the filtered union of its finite subextensions $L/K'$ and $X_{K'}$ is
noetherian, the limit descent lemma of §12.2 descends the cover together with its $G$-action to a
finite étale $Y_L\to X_L$ carrying a $G$-action by $X_L$-automorphisms, for some finite $L/K'$.
The scheme $Y_L$ is connected because its base change $Y_{\bar\eta}$ is, and simple transitivity
of $G$ on a geometric fiber may be checked after base change, so $Y_L\to X_L$ is Galois with
group $G$ and of degree $|G|$.

Let $R_L$ be the integral closure of $R'$ in $L$. It is a complete discrete valuation ring: $R'$
is a complete noetherian local ring, hence excellent and therefore Nagata by Book 11, Theorem
3.2, so $R_L$ is finite over $R'$ by Book 11, Theorem 3.1; a one-dimensional normal noetherian
local domain is a discrete valuation ring, and $R_L$ is local because $R'$ is henselian. Put
$\mathcal X=X\times_{R'}\operatorname{Spec}R_L$. It is smooth and proper over the regular base
$R_L$, hence regular, of dimension two, with generic fiber $X_L$ and with integral special fiber,
since a smooth geometrically connected fiber is geometrically integral; it is connected because
it is proper over a local ring with connected special fiber, hence integral. Being of finite type
over the complete, therefore excellent, ring $R_L$, it is excellent and in particular Nagata, so
its normalization $\mathcal Y$ in the finite étale $X_L$-scheme $Y_L$ is finite over $\mathcal X$
by Book 11, Theorems 3.1 and 3.2. Functoriality of normalization extends the $G$-action to
$\mathcal Y$ over $\mathcal X$, and by construction every component of $\mathcal Y$ dominates
$\mathcal X$.

The codimension-one points of $\mathcal X$ are the codimension-one points of the generic fiber
$X_L$, over which $\mathcal Y\to\mathcal X$ is étale because $Y_L\to X_L$ is, together with the
single generic point $\xi$ of the special fiber. Since $\mathcal X$ is smooth over $R_L$, the
special fiber is the integral divisor cut out by a uniformizer $t$ of $R_L$, so
$\mathcal O_{\mathcal X,\xi}$ is a discrete valuation ring with uniformizer $t$. Let
$\mathcal O'$ be the semilocal ring of $\mathcal Y$ at the finitely many points above $\xi$: it is
the integral closure of $\mathcal O_{\mathcal X,\xi}$ in an étale algebra of degree $|G|$ over the
fraction field, hence finite and torsion free, hence free of rank $|G|$, and it is a product of
discrete valuation rings permuted transitively by $G$. All ramification indices are therefore one
integer $e$, all residue degrees one integer $f$, and counting ranks modulo the uniformizer gives
$efg=|G|$ with $g$ the number of factors. Both $e$ and $f$ divide $|G|$ and are prime to $p$. A
field extension of degree prime to $p$ has trivial inseparable degree, so the residue extensions
are separable and the extension at $\xi$ is tamely ramified of index $e$ prime to $p$.

Adjoin an $e$-th root of $t$. Let $M=L(t^{1/e})$, let $R_M$ be the integral closure of $R_L$ in
$M$ — again a complete discrete valuation ring, totally and tamely ramified of degree $e$ over
$R_L$ with unchanged residue field — put $\mathcal X_M=\mathcal X\times_{R_L}R_M$, and let
$\mathcal Y_M$ be the normalization of $\mathcal X_M$ in the finite étale cover
$Y_M=Y_L\times_LM$ of its generic fiber, finite again by Book 11, Theorems 3.1 and 3.2. The
scheme $\mathcal X_M$ is smooth over the discrete valuation ring $R_M$, hence regular, connected
and of dimension two, with the same integral special fiber; write $\xi_M$ for its generic point,
so that $\mathcal O_{\mathcal X_M,\xi_M}$ is a discrete valuation ring with uniformizer
$s=t^{1/e}$.

That this base change removes the vertical ramification is Abhyankar's lemma in the only case
needed, and in that case it is a short computation. Let $\mathcal O^{\mathrm{sh}}$ be a strict
henselization of $\mathcal O=\mathcal O_{\mathcal X,\xi}$, with fraction field $F^{\mathrm{sh}}$.
It is faithfully flat over $\mathcal O$, so étaleness may be tested after it; it preserves
ramification indices and residue separability; and since $\mathcal O$ is excellent, forming
integral closures commutes with it. Each local factor of
$\mathcal O'\otimes_{\mathcal O}\mathcal O^{\mathrm{sh}}$ is a discrete valuation ring, ramified
of index $e$ over $\mathcal O^{\mathrm{sh}}$ with separable — hence, the residue field of
$\mathcal O^{\mathrm{sh}}$ being separably closed, trivial — residue extension; so its fraction
field $F'$ has degree $e$ over $F^{\mathrm{sh}}$. Choose a uniformizer $\varpi$ of that factor and
write $\varpi^{\,e}=tu$ with $u$ a unit. The polynomial $X^e-\bar u$ is separable because
$p\nmid e$, so it has a root in the separably closed residue field, and Hensel's lemma lifts that
root: $u=w^e$ for a unit $w$. Then $(\varpi/w)^e=t$, so $F'$ contains an $e$-th root of $t$, whose
valuation is $1/e$ times that of $t$ and which therefore generates a subextension of degree $e$;
comparing degrees gives $F'=F^{\mathrm{sh}}(t^{1/e})$. Because $e$ is invertible and the residue
field is separably closed, $\mu_e\subset\mathcal O^{\mathrm{sh}}$, so $F'/F^{\mathrm{sh}}$ is
cyclic of degree $e$ and $F'\otimes_{F^{\mathrm{sh}}}F^{\mathrm{sh}}(s)$ is a product of $e$
copies of $F^{\mathrm{sh}}(s)$. The base change of $\mathcal O_{\mathcal X_M,\xi_M}$ along
$\mathcal O\to\mathcal O^{\mathrm{sh}}$ is $\mathcal O^{\mathrm{sh}}[s]/(s^e-t)$, a strictly
henselian discrete valuation ring with uniformizer $s$, and the integral closure of that ring in
the displayed split algebra is the corresponding product of copies of itself, which is étale over
it. Hence $\mathcal Y_M\to\mathcal X_M$ is étale at $\xi_M$.

So $\mathcal Y_M\to\mathcal X_M$ is finite with $\mathcal Y_M$ normal, every component dominates
the connected regular two-dimensional $\mathcal X_M$, and the map is étale over every
codimension-one point: over the generic fiber because $Y_M\to X_M$ is étale, and at $\xi_M$ by
the previous paragraph. The purity lemma for surfaces makes $\mathcal Y_M\to\mathcal X_M$ finite
étale.

Its special fiber is a finite étale cover of $X_s\times_{k^{\mathrm{s}}}\kappa$, where
$k^{\mathrm{s}}$ is the separably closed residue field of $R'$ and $\kappa$ is the residue field
of $R_M$, equal to that of $R_L$ and hence a finite, therefore purely inseparable, extension of
$k^{\mathrm{s}}$. By §13.3 such an extension is invisible to finite étale
covers, so the special fiber of $\mathcal Y_M$ comes from a finite étale cover $Z_{\bar s}$ of
$X_{\bar s}$. Extend $Z_{\bar s}$ over $X_{R'}$ by the finite étale existence lemma and call the
result $\mathcal Z$. Its base change to $R_M$ is finite étale over $\mathcal X_M$ with the same
special fiber as $\mathcal Y_M$, so the uniqueness clause of the existence lemma, applied over
the complete local ring $R_M$, identifies it with $\mathcal Y_M$. Restricting to $\overline{K'}$
therefore returns $Y_{\bar\eta}$. In other words, the specialization functor carries $Z_{\bar s}$
to the given generic cover.

Thus every finite quotient of order prime to $p$ of the generic group is detected by a special
cover. The injectivity criterion of §8.3 makes $\operatorname{sp}^{(p')}$ injective; surjectivity
was already proved, so it is an isomorphism. When $p=0$, every finite inertia group is tame and
the same argument applies to every finite quotient, giving the full isomorphism. This proof also
explains both qualifications: purity uses smoothness, and algebraization plus the fact that a
closed subset of a proper family meets the closed fiber uses properness.

It is worth seeing that individual covers can be transported in any relative dimension by direct
inspection, without the model-building above. Let $A/R$ be an abelian scheme of relative dimension
$g$. For $n$ invertible in $R$, multiplication by $n$ is finite étale on the whole family, and its
kernel has rank $n^{2g}$. One and the same cover therefore appears on the generic and on the
special fiber, so the monodromy of prime-to-$p$ torsion is transported unchanged whatever $g$ may
be. That is a computation with explicit covers rather than an instance of the theorem just proved;
it uses no purity at all, and by the same token it sees only the covers that torsion produces,
not the whole prime-to-$p$ group. Multiplication by $p$ in residue characteristic $p$ is not étale
on the special fiber and lies outside this argument.

At the arithmetic level, the two fibers map to $G_K$ and $G_k$. Relating those quotients requires decomposition data connecting a geometric generic point to a geometric special point and introduces inertia. This is why the clean specialization theorem is stated for geometric fundamental groups; an arithmetic formulation must record those additional choices.

As an instructive phenomenon, a smooth proper family of elliptic curves in characteristic $p$ can specialize from ordinary to supersingular. The étale part of $p$-power torsion changes, so the full pro-$p$ covering theory cannot be constant even though every prime-to-$p$ isogeny cover specializes perfectly.

### 14.4 What fails without the hypotheses

Dropping smoothness permits branch points or singularities to appear. The family $y^2=x(x-1)(x-t)$ over a trait approaching $t=0$ degenerates from smooth genus-one curves to a singular curve; its covering theory cannot be transported as though the fibers were all locally identical.

Dropping properness permits ramification to move to the boundary. Kummer covers of $\mathbf G_m$ and Artin–Schreier covers of $\mathbf A^1$ show that affine curves, especially in characteristic $p$, possess covers governed by behavior at infinity that a naive specialization can lose.

Dropping henselianity prevents unique extension from the closed fiber. Henselization is therefore not a cosmetic completion of the base: it is what turns a simple special-fiber factorization into actual disjoint étale sheets near that fiber.

### 14.5 Boundaries, tame quotients, and semistable curves

For a nonproper smooth curve, the correct replacement for properness is a compactification together with a ramification condition. Let $R$ be a strictly henselian DVR with residue characteristic $p\ge0$. Suppose $\overline X\to\operatorname{Spec}R$ is a smooth proper relative curve with geometrically connected fibers and $D\subset\overline X$ is a relative divisor that is finite étale over $R$. Put $X=\overline X\setminus D$. Then the points at infinity remain disjoint sections after an étale base change, so ramification orders along them can be compared from one fiber to the other.

A finite étale cover of $X_{\bar\eta}$ is **tame along $D_{\bar\eta}$** if, after normalizing $\overline X_{\bar\eta}$, every inertia group at a point over $D_{\bar\eta}$ has order prime to the residue characteristic there. Define the tame group $\pi_1^t(X_{\bar\eta})$ by retaining only such covers, and similarly on the special fiber. Specialization gives

$$
\pi_1^t(X_{\bar\eta})^{(p')}
\xrightarrow{\sim}
\pi_1^t(X_{\bar s})^{(p')}.
$$

Since every group of order prime to $p$ has only prime-to-$p$ inertia, the superscript may equally be read as the prime-to-$p$ fundamental group of the open curve. The proof uses Kummer charts at the boundary. After a strict henselian localization and a parameter $t$ for a boundary section, a tamely ramified cover is dominated by one obtained from $u^n=t$ with $(n,p)=1$ and an unramified cover. The derivative $nu^{n-1}$ is invertible away from the divisor, and the exponent $n$ is unchanged under specialization. These local extensions glue because their descent data are finite; properness of $\overline X$ controls the complement. Applying the proper smooth prime-to-$p$ theorem to the unramified pieces yields the isomorphism.

Two steps of that sketch are no longer sketches. The passage from a cover of $X_{\bar\eta}$ to a cover defined over a finite extension of the fraction field, carrying its group action with it, is the limit descent lemma of §12.2. The passage from the resulting finite normal model to a finite étale one is the purity lemma for surfaces of §14.3, whose hypotheses are met precisely because $\overline X$ has relative dimension one over $R$: every model occurring here is regular of dimension two, which is the case the lemma covers. The remaining boundary bookkeeping is the sketch it is announced to be.

No full tame isomorphism is asserted in residue characteristic $p$. A $p$-group cover unramified at the boundary is tame there but can still vary, just as the étale $p$-power torsion of a proper elliptic curve varies between ordinary and supersingular fibers. “Tame at infinity” excludes wild boundary inertia; it does not turn every finite group into one of order prime to $p$.

Semistable reduction lies on another boundary. If $\overline X/R$ has a nodal special fiber rather than a smooth one, vanishing cycles at the nodes change the geometric fundamental group. There is still a specialization theory for suitable tame quotients, described through the normalization of the special fiber, its marked preimages of nodes, and its dual graph, but it is not the smooth-proper isomorphism above. In particular, one must not conclude that the full or prime-to-$p$ group of a smooth generic curve equals that of the singular special curve. A loop pinched to a node can enter the specialization kernel.

For arithmetic schemes this gives a practical hierarchy:

$$
\begin{array}{c|c}
\text{family} & \text{safe specialization statement}\\
\hline
\text{proper smooth, residue characteristic }0 & \text{full geometric group is unchanged}\\
\text{proper smooth, residue characteristic }p>0 & \text{prime-to-}p\text{ geometric group is unchanged}\\
\text{smooth open with smooth relative boundary} & \text{prime-to-}p\text{ tame group is unchanged}\\
\text{semistable or singular special fiber} & \text{use a separate tame/vanishing-cycle analysis.}
\end{array}
$$

Every row of the table concerns a family of relative dimension at most one. That is the generality in which §14.3 proves the first two rows, and it is the generality the remaining rows and Chapter 15 draw on.

The hypotheses record actual geometry: properness controls escape, smoothness prevents nodes and collisions, tame conditions control the boundary, and the prime-to-$p$ restriction removes the covers most sensitive to characteristic $p$.

## 15. Curves and explicit covers

### 15.1 Affine and projective lines

We first prove the curve formula used here, since it is not part of the covering-category
formalism. For a smooth proper connected curve put
$g(C)=\dim H^1(C,\mathcal O_C)$. Let $h:C'\to C$ be a finite separable map of such curves over an
algebraically closed field. The differential map

$$
h^*\Omega^1_C\longrightarrow\Omega^1_{C'}
$$

is injective: it is injective at the generic point because the function-field extension is
separable, and both sheaves are line bundles. Its cokernel has finite length. If $d_y$ is its
length at $y\in C'$, taking degrees gives

$$
2g(C')-2=\deg(h)(2g(C)-2)+\sum_{y\in C'}d_y. \tag{15.1}
$$

For completeness, the identity $\deg\Omega^1_C=2g(C)-2$ entering this calculation has a short
divisor proof. Compute coherent cohomology on a finite affine Čech cover. Adding one closed point to a
divisor gives an exact sequence whose quotient has dimension one, so additivity yields

$$
\chi(\mathcal O_C(D))=\deg D+\chi(\mathcal O_C)
=\deg D+1-g(C).
$$

The residue pairing on that same Čech complex identifies
$H^1(C,\Omega^1_C)$ with $H^0(C,\mathcal O_C)^*$ and
$H^0(C,\Omega^1_C)$ with $H^1(C,\mathcal O_C)^*$. To verify perfectness directly, prescribe
finitely many principal parts. The only linear relation among their residues is that their sum
is zero: on $\mathbf P^1$ this is partial fractions, and on $C$ a separating rational function
reduces it to $\mathbf P^1$ by the field trace. Successively adding the supporting points then
shows, from the long exact sequences of the two-affine complexes, that the residue pairing has
zero kernel and cokernel. Hence

$$
\chi(\Omega^1_C)=g(C)-1,
$$

and comparison with the preceding degree formula gives $\deg\Omega^1_C=2g(C)-2$. This proves
the global degree step in (15.1), rather than assuming Riemann–Roch or duality.

The local term is equally explicit. For uniformizers $t$ at $h(y)$ and $u$ at $y$, write
$t=u^{e_y}a$ with $a$ a unit. The order of the coefficient of $du$ in $dt$ is $d_y$. It is
$e_y-1$ when $e_y$ is prime to the characteristic, and it is at least $e_y$ when wild
ramification makes the leading coefficient vanish. Thus $d_y=0$ at an étale point and, in the
tame case,

$$
2g(C')-2=\deg(h)(2g(C)-2)+\sum_y(e_y-1), \tag{15.2}
$$

which is the Riemann–Hurwitz formula in exactly the form used below.

Let $k$ be algebraically closed. The projective line has no nontrivial connected finite étale cover in any characteristic:

$$
\pi_1(\mathbf P^1_k)=1.
$$

Indeed, a connected finite étale cover $C\to\mathbf P^1$ is a smooth proper curve and the unramified Riemann–Hurwitz formula gives

$$
2g(C)-2=\deg(C/\mathbf P^1)(-2).
$$

Here $g(\mathbf P^1)=0$, as the two-standard-affine Čech complex computes directly. The left side
is at least $-2$, forcing degree $1$. Separability is automatic from étaleness, so the argument
remains valid in positive characteristic.

For the affine line the answer depends sharply on characteristic. If $\operatorname{char}k=0$, every finite étale cover of $\mathbf A^1_k$ is trivial. Compactifying and normalizing produces a cover $C'\to\mathbf P^1$ ramified at most over infinity. If its degree is $n$ and there are $r$ points over infinity, tameness gives $\sum(e_y-1)=n-r$, so (15.2) reads

$$
2g(C')-2=-n-r.
$$

The left side is at least $-2$, while $n,r\ge1$; hence $n=r=1$. If $\operatorname{char}k=p>0$, however, Artin–Schreier covers give many nontrivial covers. Thus it is correct to say that geometric $\mathbf P^1$ is étale-simply connected over an algebraically closed field, but incorrect to say the same of geometric $\mathbf A^1$ in positive characteristic.

Over a nonclosed field $k$, even $\mathbf P^1_k$ has arithmetic covers obtained from finite separable extensions of $k$. Since its geometric group is trivial, the fundamental exact sequence gives

$$
\pi_1(\mathbf P^1_k)\cong G_k
$$

after a compatible basepoint choice.

### 15.2 Kummer covers of the punctured line

Let $n\ge1$ be invertible in $k$. On $\mathbf G_m=\operatorname{Spec}k[t,t^{-1}]$, the map

$$
[n]\colon\mathbf G_m\longrightarrow\mathbf G_m,
\qquad t=u^n,
$$

is finite étale of degree $n$. Algebraically its source is

$$
k[t,t^{-1},u]/(u^n-t),
$$

and the derivative $nu^{n-1}$ is a unit because both $n$ and $u$ are units. If $k$ contains $\mu_n$, the transformations $u\mapsto\zeta u$ make it a Galois cover with deck group $\mu_n(k)$.

These covers are compatible under divisibility and exhibit the prime-to-$p$ procyclic quotient

$$
\widehat{\mathbf Z}^{(p')}=\prod_{\ell\ne p}\mathbf Z_\ell
$$

of $\pi_1(\mathbf G_{m,\bar k})$ in characteristic $p$, with the convention $p=0$ meaning all primes. In characteristic zero this is the full geometric fundamental group, canonically up to the choice of compatible roots. In positive characteristic the full group is much larger because wild covers of $p$-power order also occur.

If $p\mid n$, the same power map is not étale: its differential can vanish and its kernel group scheme is not étale. The invertibility condition on $n$ is therefore structural, not a convenient simplification.

### 15.3 Artin–Schreier covers

Let $k$ have characteristic $p>0$. The equation

$$
y^p-y=f(x)
$$

defines a finite étale cover of any affine scheme on which $f$ is regular. As a polynomial in $y$, its derivative is $-1$, a unit. The constant group $\mathbf Z/p\mathbf Z$ acts by $y\mapsto y+a$ for $a\in\mathbf F_p$.

For $f(x)=x$ on $\mathbf A^1_k$, the cover is connected: $x$ is not of the form $g^p-g$ in $k(x)$. Indeed, if $g$ has a pole, the pole order of $g^p-g$ is divisible by $p$, whereas $x$ has a pole of order one at infinity; if $g$ has no pole, it is constant. It is therefore a Galois degree-$p$ cover of the affine line. Its normalization over $\mathbf P^1$ is ramified wildly at infinity. This explains simultaneously why it does not contradict the triviality of $\pi_1(\mathbf P^1_{\bar k})$ and why arguments based only on the number of branch points fail in wild characteristic.

Two equations $y^p-y=f$ and $y^p-y=f'$ define isomorphic torsors when $f-f'=g^p-g$. This concrete quotient is the first glimpse of a cohomological classification, but the cohomology itself belongs to the next book.

### 15.4 Elliptic isogenies and inseparable maps

Let $E$ be an elliptic curve over a field $k$. If $n$ is prime to $\operatorname{char}k$, multiplication

$$
[n]\colon E\longrightarrow E
$$

is finite étale of degree $n^2$. Over a separable closure its deck transformations are translations by the $n^2$ points of $E[n]$. Thus $E[n]$ is simultaneously a geometric fiber, a deck group, and a finite $G_k$-module. Passing through compatible powers of a prime $\ell\ne\operatorname{char}k$ gives the familiar continuous action on the inverse system of $\ell^r$-torsion; its linear-algebraic completion is developed elsewhere.

In characteristic $p$, $[p]$ is never étale: its differential on the tangent space is multiplication by $p$, hence zero. The relative Frobenius $F\colon E\to E^{(p)}$ is finite and purely inseparable, so it too is not étale. For an ordinary elliptic curve the dual Verschiebung $V\colon E^{(p)}\to E$ is finite étale of degree $p$; for a supersingular curve it is inseparable, and the $p$-torsion has no nontrivial geometric étale points. These examples show why rank alone cannot measure sheets in characteristic $p$.

The affine map $x\mapsto x^p$ gives the simplest parallel counterexample. It is finite flat of degree $p$ over a perfect field, bijective on algebraically closed points, and has zero derivative. It is a universal homeomorphism, not a cover.

### 15.5 Compactification, inertia, and tame covers

Let $U$ be a smooth geometrically connected curve over an algebraically closed field $k$, and let $C$ be its smooth proper compactification. Write $D=C\setminus U$. Every connected finite étale cover $V\to U$ determines a finite separable extension $k(V)/k(U)$. Normalizing $C$ in this field gives a finite map $\overline V\to C$ that is étale over $U$ and may ramify only over $D$. Conversely every such generically separable map restricts to a finite étale cover of $U$. This is the function-field form of the covering theory of a curve.

Choose $x\in D$, a geometric point above it in $\overline V$, and a separable closure of the completed or henselian local field $k(C)_x$. The stabilizer in a Galois closure is the decomposition group $D_x$. Because $k$ is algebraically closed, the residue extension is trivial and $D_x=I_x$ is inertia. If $p=\operatorname{char}k>0$, inertia fits into

$$
1\longrightarrow P_x\longrightarrow I_x
\longrightarrow I_x^t\longrightarrow1,
$$

where $P_x$ is the wild inertia, a pro-$p$ group, and $I_x^t$ has all finite quotients of order prime to $p$. A cover is tame at $x$ precisely when $P_x$ acts trivially. In characteristic zero, all finite inertia is tame.

Locally, tame covers have a simple form. Over the strict henselization at $x$, choose a uniformizer $t$. A connected tamely ramified extension of degree $n$ prime to $p$ becomes, after an unramified change that is trivial here, a Kummer extension

$$
u^n=t.
$$

This statement follows by choosing a uniformizer upstairs, comparing valuations, and using Hensel's lemma to absorb the unit discrepancy into an $n$th power. It explains why tame inertia is procyclic away from $p$ and why compatible roots of a local parameter supply generators only up to inversion and conjugacy.

For $U=C\setminus D$, the tame fundamental group is the quotient of $\pi_1(U)$ obtained by killing every $P_x$ for $x\in D$. The proper group $\pi_1(C)$ is obtained by killing all of $I_x$. Thus there are natural surjections

$$
\pi_1(U)\twoheadrightarrow\pi_1^t(U)
\twoheadrightarrow\pi_1(C),
$$

and each step has a distinct meaning: the first forgets wild ramification at the boundary, while the second forgets tame ramification there as well.

The Riemann–Hurwitz formula gives a useful global check in the tame case. For a finite separable map $\overline V\to C$ of degree $n$ with tame ramification indices $e_y$,

$$
2g(\overline V)-2
=n(2g(C)-2)+\sum_y(e_y-1).
$$

The correction terms are nonnegative and record exactly the failure of the restriction to extend étale across $D$. In wild characteristic additional different exponents exceed $e_y-1$; substituting the tame formula for an Artin–Schreier cover would therefore give a false genus calculation.

### 15.6 Arithmetic curves and good reduction

Let $R$ be a henselian DVR with fraction field $K$ and residue field $k$, and let $X/R$ be a smooth proper relative curve with geometrically connected fibers. Good reduction means precisely that one has such a smooth proper model. The specialization theorem then identifies the prime-to-$p$ geometric covering theories of $X_{\bar K}$ and $X_{\bar k}$, where $p=\operatorname{char}k$.

This statement is geometric. The arithmetic groups sit in two exact rows,

$$
\begin{array}{ccccccccc}
1&\to&\pi_1(X_{\bar K})&\to&\pi_1(X_K)&\to&G_K&\to&1\\
 &&\downarrow&&\downarrow&&\downarrow\\
1&\to&\pi_1(X_{\bar k})&\to&\pi_1(X_k)&\to&G_k&\to&1,
\end{array}
$$

only after choosing compatible decomposition and specialization data. The right vertical map is not a homomorphism $G_K\to G_k$ on all of $G_K$ without qualification. One first chooses the decomposition group attached to the valuation; for a henselian field it is all of $G_K$, and then takes the quotient

$$
G_K\twoheadrightarrow G_k
$$

whose kernel is inertia. On prime-to-$p$ geometric groups, inertia acts through the outer action induced by the upper exact sequence. Good reduction gives constancy of the geometric group. A cover or sheaf that extends over the smooth proper model has the corresponding unramified specialization behavior, but an arbitrary representation on the generic fiber need not extend; unramifiedness must be checked for the particular arithmetic object.

For an open curve $U=X\setminus D$ with $D$ finite étale over $R$, the same comparison holds for prime-to-$p$ tame quotients. If marked points collide, if the model acquires nodes, or if $D$ is not relatively étale, the hypothesis fails exactly where new inertia can appear. A semistable model still organizes the change through its components and nodes, but good-reduction invariance no longer applies.

Connectedness also needs its geometric adjective. A smooth proper curve over $K$ may be connected while its scalar extension to $\bar K$ is not; then the arithmetic exact sequence ends in the stabilizer of a chosen geometric component rather than all of $G_K$. In arithmetic geometry “a curve with good reduction” is therefore normally required to be geometrically connected before its geometric fundamental group is compared across fibers.

## 16. Locally constant finite sheaves

### 16.1 From descent data to monodromy

Covers are geometric objects; sheaves package data that become constant after passing to a cover. The **finite étale site** of $X$ has objects finite étale $X$-schemes and covering families that are jointly surjective. For comparison with later cohomology, one also uses the small étale site, whose objects are arbitrary étale $X$-schemes. A sheaf of sets on the small étale site is **finite locally constant** if some étale covering makes it a constant sheaf associated with a finite set.

On a connected locally noetherian $X$, taking the stalk at $\bar x$ gives an equivalence

$$
\{\text{finite locally constant étale sheaves of sets on }X\}
\simeq
\operatorname{FinSet}^{\mathrm{cont}}_{\pi_1(X,\bar x)}.
$$

The reason is the same descent argument as for covers. A trivialization over a finite étale cover gives permutations on overlaps satisfying a cocycle condition; transporting around all refinements gives monodromy. Conversely a finite continuous action factors through a finite quotient, and the corresponding Galois cover glues the constant sheaf by those permutations.

There is no representability gap in this argument. If $\mathcal F$ is finite locally constant,
choose an étale covering $\{U_i\to X\}$ on which it is the constant sheaf attached to a finite
set $A_i$. On $U_i\times_XU_j$, the two trivializations differ by a locally constant permutation;
after decomposing the overlap into open-and-closed pieces, these permutations give descent
isomorphisms

$$
\coprod_{A_i}U_i\xrightarrow{\sim}\coprod_{A_j}U_j
$$

satisfying the cocycle. Effective set-indexed descent from Chapter 6 glues them to a scheme
$Y\to X$. Finiteness and étaleness are local on the base, so $Y$ is finite étale, and its
represented sheaf is $\mathcal F$. Conversely the represented sheaf of a finite étale cover is
locally constant because the cover splits over a strict local neighborhood. Thus finite locally
constant sheaves of sets and finite étale covers are the same category before either is identified
with monodromy sets.

The stalk is a filtered colimit over pointed étale neighborhoods $(U,\bar u)$ of $\bar x$. For a locally constant finite sheaf, one sufficiently small neighborhood already trivializes the sheaf, so the stalk is an ordinary finite set rather than an unwieldy limit. Transport along a pointed refinement identifies these local copies, and a closed chain of such identifications gives a monodromy permutation.

The finite étale site suffices for finite locally constant sheaves because the representing cover
just constructed is itself a finite étale trivializing object after passage to a Galois closure.
General constructible sheaves are different: they may change across strata and require the whole
small étale site.

Finite étale covers themselves represent finite locally constant sheaves:

$$
U\longmapsto\operatorname{Hom}_X(U,Y).
$$

The equivalence between covers and finite monodromy sets is therefore also an equivalence between finite étale representable sheaves and all finite locally constant sheaves of sets.

### 16.2 Finite modules and representations

Let $\Lambda$ be a finite ring. A locally constant sheaf of finite $\Lambda$-modules has stalk $M=\mathcal F_{\bar x}$ and monodromy

$$
\rho_{\mathcal F}\colon
\pi_1(X,\bar x)\longrightarrow\operatorname{Aut}_\Lambda(M).
$$

The target is finite and discrete. Continuity is equivalent to the kernel being open, or to the action factoring through a finite quotient. Conversely every finite $\Lambda$-module with continuous action produces a locally constant sheaf by descent. Exact sequences, tensor products, duals of finite projective modules, and internal Hom correspond to the same operations on monodromy modules.

For $X=\operatorname{Spec}k$, this is exactly a continuous finite Galois representation

$$
\rho\colon G_k\longrightarrow\operatorname{Aut}_\Lambda(M).
$$

For general $X/k$, a sheaf gives an arithmetic representation of $\pi_1(X)$. Restricting it to $\pi_1(X_{k^s})$ gives geometric monodromy. It gives a representation of $G_k$ itself only if the geometric subgroup acts trivially, or after choosing additional structure such as a section and then pulling back along that section. This qualification prevents a common but serious confusion between arithmetic monodromy on $X$ and a representation of the base-field Galois group.

If a rational point $x\in X(k)$ is chosen, pullback of $\mathcal F$ along $x$ is a locally constant sheaf on $\operatorname{Spec}k$. Its geometric stalk is the same module after a path choice, and its Galois action is the composite

$$
G_k\xrightarrow{x_*}\pi_1(X,\bar x)
\xrightarrow{\rho_{\mathcal F}}\operatorname{Aut}_\Lambda(M).
$$

This is the precise construction of the associated Galois representation from a pointed arithmetic local system. A different point can give a genuinely different representation, while a different path conjugates the same representation.

A finite étale commutative group scheme over $k$ supplies a basic example: its $k^s$-points form a finite abelian group with continuous $G_k$-action, and Galois descent reconstructs the group scheme. When the order is divisible by $\operatorname{char}k$, only the étale group schemes occur in this dictionary; infinitesimal group schemes have too few geometric points.

For $n$ invertible in $k$, the group scheme $\mu_n$ is finite étale. Choosing a primitive $n$th root identifies its geometric points with $\mathbf Z/n\mathbf Z$, but Galois acts through

$$
\chi_n\colon G_k\longrightarrow(\mathbf Z/n\mathbf Z)^\times,
\qquad
\sigma(\zeta)=\zeta^{\chi_n(\sigma)}.
$$

This is the mod-$n$ cyclotomic representation. The identification with $\mathbf Z/n\mathbf Z$ depends on $\zeta$, while the group scheme and its Galois module are canonical. By contrast, the constant group scheme $(\mathbf Z/n\mathbf Z)_k$ has trivial Galois action. They become isomorphic over $k^s$ but need not be isomorphic over $k$; descent data remember the difference.

For an elliptic curve $E/k$ and $n$ prime to $\operatorname{char}k$, the same construction applied to $E[n]$ gives

$$
\rho_{E,n}\colon G_k\longrightarrow
\operatorname{Aut}(E[n](k^s))
\cong\operatorname{GL}_2(\mathbf Z/n\mathbf Z)
$$

after choosing a basis. Changing the basis conjugates the matrix representation. This is a direct passage from a finite étale geometric object to a continuous Galois representation; no cohomology is involved.

### 16.3 Lisse finite-coefficient sheaves

A sheaf of $\Lambda$-modules is called **lisse** when it is locally constant with finite-type stalks in the relevant coefficient category. For a finite ring $\Lambda$, this is precisely finite locally constant module data. If one requires the stalk to be finite free, lisse sheaves correspond to continuous representations

$$
\pi_1(X,\bar x)\longrightarrow\operatorname{GL}_r(\Lambda).
$$

Changing the geometric basepoint conjugates the representation after choosing a path. Hence its isomorphism class, character, invariant submodules, and geometric-versus-arithmetic restrictions are intrinsic.

At this stage “lisse” is purely categorical and monodromic. We do not define derived global sections, higher étale cohomology, smooth or proper base change for cohomology, cup products, or Poincaré duality. Those constructions require a broader site and homological machinery and form the subject of the next book.

One can nevertheless see the future shape. A tower of finite coefficient sheaves may produce a representation on a profinite module, and scalar extension may produce an $\ell$-adic representation. The continuity and inverse-limit issues then require the topological coefficient conventions developed for profinite representations; they are not automatic consequences of the finite-level equivalence.

### 16.4 Permutation representations from covers

A cover first gives a finite set, but any coefficient ring turns that set into a linear representation. Let $Y\to X$ be finite étale, let $T=Y_{\bar x}$, and let $\Lambda$ be a commutative ring. The free module

$$
\Lambda[T]=\bigoplus_{t\in T}\Lambda[t]
$$

carries the permutation action

$$
g\left(\sum_ta_t[t]\right)
=\sum_ta_t[g t].
$$

If $\Lambda$ is finite, continuity follows because the action factors through the finite monodromy image in $\operatorname{Sym}(T)$. If $X=\operatorname{Spec}k$, this is a continuous Galois representation of $G_k$. For general $X/k$, it is a representation of $\pi_1(X)$; pulling back along a rational point, or requiring geometric monodromy to be trivial, produces a representation of $G_k$ as explained in Section 16.2.

The vector

$$
\mathbf 1_T=\sum_{t\in T}[t]
$$

is invariant. The augmentation map

$$
\varepsilon:\Lambda[T]\longrightarrow\Lambda,
\qquad \sum_ta_t[t]\longmapsto\sum_ta_t
$$

is equivariant, and its kernel is the augmentation representation. If the degree $n=|T|$ is invertible in $\Lambda$, averaging splits the sequence

$$
0\longrightarrow\ker\varepsilon
\longrightarrow\Lambda[T]
\xrightarrow{\varepsilon}\Lambda\longrightarrow0.
$$

If $n$ is not invertible, the sequence need not split. This is a first example of how a perfectly semisimple permutation of a set can yield a nonsemisimple modular representation.

For a connected Galois cover with group $G$, choosing a point of the fiber identifies $T$ with a regular $G$-set, up to the left/right convention. Thus $\Lambda[T]$ is the regular representation. For a non-Galois connected cover attached to an open subgroup $H\subset\Pi$, it is the induced permutation module $\Lambda[\Pi/H]$. Changing the chosen lift conjugates $H$ and produces an isomorphic module.

Conversely, not every linear representation comes from a single permutation set. It may be a subquotient of a permutation representation, or require several covers and linear relations. A lisse sheaf captures precisely the resulting finite module with monodromy, regardless of whether a basis is permuted. Covers and lisse sheaves therefore yield related but genuinely different kinds of representations.

A tower of covers can already produce an infinite representation. For an elliptic curve $E/k$ and a prime $\ell\ne\operatorname{char}k$, the covers $[\ell^n]:E\to E$ have kernels $E[\ell^n](k^s)$ and compatible transition maps. Their inverse limit

$$
T_\ell E=\varprojlim_n E[\ell^n](k^s)
$$

is a free $\mathbf Z_\ell$-module of rank $2$, and the finite Galois actions are compatible. They therefore define

$$
\rho_{E,\ell}:G_k\longrightarrow
\operatorname{GL}(T_\ell E)\cong\operatorname{GL}_2(\mathbf Z_\ell).
$$

Continuity is checked modulo every $\ell^n$: the stabilizer of the finite torsion field is open, and these congruence kernels form a neighborhood basis of the identity in the target.

### 16.5 Integral and rational adic representations

Fix a prime $\ell$. A **lisse $\mathbf Z_\ell$-sheaf of rank $r$** on connected $X$ can be described at this level as a compatible inverse system $(\mathcal F_n)_{n\ge1}$ in which $\mathcal F_n$ is lisse finite free over $\mathbf Z/\ell^n\mathbf Z$ and

$$
\mathcal F_{n+1}\otimes_{\mathbf Z/\ell^{n+1}\mathbf Z}
\mathbf Z/\ell^n\mathbf Z
\cong\mathcal F_n.
$$

Taking stalks gives finite free modules $M_n$ with compatible continuous actions. Their inverse limit

$$
M=\varprojlim_nM_n
$$

is finite free over $\mathbf Z_\ell$, and the actions assemble to a homomorphism

$$
\rho:\pi_1(X,\bar x)\longrightarrow\operatorname{GL}_r(\mathbf Z_\ell).
$$

It is continuous because reduction modulo $\ell^n$ has open kernel for every $n$, while the congruence subgroups

$$
1+\ell^nM_r(\mathbf Z_\ell)
$$

form a neighborhood basis at the identity. Conversely, a continuous representation on a finite free $\mathbf Z_\ell$-module reduces modulo $\ell^n$ to a finite continuous representation and hence to a lisse $\mathbf Z/\ell^n\mathbf Z$-sheaf. Compatibility of reduction reconstructs the inverse system. Thus

$$
\{\text{lisse }\mathbf Z_\ell\text{-sheaves of rank }r\}
\simeq
\{\text{continuous rank-}r\ \mathbf Z_\ell\text{-representations of }\pi_1(X)\}.
$$

Tensoring with $\mathbf Q_\ell$ produces a continuous $\mathbf Q_\ell$-representation. Conversely every continuous finite-dimensional $\mathbf Q_\ell$-representation of a profinite group admits a stable $\mathbf Z_\ell$-lattice. Indeed, begin with any lattice $L$. Its stabilizer in $\operatorname{GL}(V)$ is open; compactness of the image gives only finitely many translates of $L$. Their sum is again a lattice and is stable under the image. After choosing a basis of that stable lattice, the representation takes values in $\operatorname{GL}_r(\mathbf Z_\ell)$. A lisse $\mathbf Q_\ell$-sheaf may therefore be described by a lisse integral lattice up to isogeny. Different stable lattices give the same rational representation but can have different reductions modulo $\ell$.

Over $X=\operatorname{Spec}k$ these are continuous $\ell$-adic Galois representations. Over a variety $X/k$ they are initially representations of $\pi_1(X)$. There are three legitimate ways a $G_k$-representation arises:

1. pull the sheaf back along a chosen $k$-rational point $x:\operatorname{Spec}k\to X$;
2. prove that geometric monodromy is trivial, so the action factors through $G_k$;
3. start with a geometric object over $k$, such as the compatible torsion of an abelian variety, whose geometric points already form a $G_k$-module.

These constructions should not be conflated. A section in the arithmetic exact sequence lets one restrict a representation of $\pi_1(X)$ to $G_k$, but the result can depend on the section. Factorization through $G_k$ is a stronger, section-independent assertion.

Lisse adic sheaves constructed here are monodromy objects. Their cohomology, derived inverse limits, weights, and base-change theorems require additional machinery. None of those later results is needed to justify the continuous representation itself: it is already forced by compatible finite monodromy.

## 17. The covering–monodromy dictionary

### 17.1 The dictionary

The theory can now be summarized without collapsing its qualifications:

| Geometric or sheaf-theoretic object | Monodromy object |
|---|---|
| finite étale cover $Y\to X$ | finite continuous left $\pi_1(X,\bar x)$-set $Y_{\bar x}$ |
| degree of $Y/X$ | cardinality of the geometric fiber |
| connected cover | transitive action |
| pointed connected cover | open subgroup $H\subseteq\pi_1(X,\bar x)$ |
| unpointed connected cover | conjugacy class of open subgroups |
| connected Galois cover | open normal subgroup |
| deck group | $N(H)/H$, with the stated action-side convention |
| section of a cover | fixed point of its monodromy set |
| fiber product or disjoint union | product or disjoint union of sets |
| finite locally constant sheaf | finite continuous monodromy set |
| lisse finite $\Lambda$-sheaf | finite $\Lambda$-module with continuous action |
| lisse $\mathbf Z_\ell$-sheaf | finite free $\mathbf Z_\ell$-module with continuous action |
| object over $\operatorname{Spec}k$ | finite continuous $G_k$-set or module |
| geometric base change $X_{k^s}$ | restriction to geometric monodromy |
| arithmetic descent from $k^s$ | compatible $G_k$-descent data |
| normal arithmetic scheme with function field $K$ | quotient of $G_K$ by extensions ramified on the scheme |
| deletion of boundary points on a curve | permission for inertia at those points |
| tame quotient of an open curve | wild boundary inertia killed |

The entries involving subgroups require $X$ connected and a geometric basepoint. Removing the point replaces subgroups by conjugacy classes. The field and family exact sequences require the hypotheses stated in Chapters 12–14, not merely connectedness of the underlying topological space.

### 17.2 A construction protocol

Suppose a geometric construction is expected to yield a finite Galois representation. First verify that the morphism or sheaf is finite locally constant: for a finite morphism this means finite presentation, flatness, and unramifiedness, not just constant rank. Next choose a geometric basepoint and form its geometric fiber or stalk. Functorial transport produces a left continuous action of the appropriate fundamental group.

Then identify which group is actually acting. Over a field it is $G_k$. Over $X/k$ it is initially $\pi_1(X)$, with geometric restriction to $\pi_1(X_{k^s})$ and arithmetic quotient $G_k$. A $G_k$-representation follows only from factorization through the quotient or from a chosen section. Finally, record all basepoint choices: changing them conjugates the action, so invariant conclusions should be phrased accordingly.

For a tower, check compatibility at every finite level before taking an inverse limit. Profinite continuity means precisely that each finite quotient has open kernel. A $\mathbf Z_\ell$-representation is continuous when all reductions modulo $\ell^n$ are continuous, and a rational representation should be supplied with, or proved to possess, a stable lattice. For specialization, reverse the geometric functor when determining the group arrow, and distinguish full, prime-to-$p$, and tame statements.

### 17.3 Conclusion

Finite étale geometry turns algebraic covering problems into finite permutation theory without discarding arithmetic descent. Flatness keeps sheets from appearing or colliding, unramifiedness separates them infinitesimally, and finite presentation keeps the geometry controllable. Effective descent then makes a geometric fiber, together with all of its compatible symmetries, sufficient to reconstruct the cover.

The resulting fundamental group is not an auxiliary invariant placed beside the geometry. It is the automorphism group of the operation of taking every geometric fiber at once. Its open subgroups are connected covers, its normal open subgroups are Galois covers, and its finite modules are locally constant sheaves. Over a field it is the absolute Galois group; over a normal arithmetic scheme it is the quotient that kills ramification retained on the scheme; over a geometrically connected variety it contains geometric monodromy as the kernel of arithmetic monodromy. Basepoint paths explain the inevitable inner ambiguity, while henselian and proper-smooth specialization show exactly how the theory behaves in arithmetic families.

This dictionary is the entry point to étale cohomology. The next stage replaces a single stalk and its monodromy by global derived invariants, but the finite covering theory developed here remains the structural foundation beneath every resulting Galois action.
