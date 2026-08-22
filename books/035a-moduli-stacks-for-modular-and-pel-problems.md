# Moduli Stacks for Modular and PEL Problems

## Contents

1. [Why moduli problems form stacks](#1-why-moduli-problems-form-stacks)
   - [Objects, families, and symmetry](#11-objects-families-and-symmetry)
   - [Five levels of representability](#12-five-levels-of-representability)
   - [The base site and conventions](#13-the-base-site-and-conventions)
   - [Assumed inputs](#14-assumed-inputs)
2. [Categories fibered in groupoids](#2-categories-fibered-in-groupoids)
   - [Cartesian arrows](#21-cartesian-arrows)
   - [Pullback and coherence](#22-pullback-and-coherence)
   - [The fibered category attached to a moduli problem](#23-the-fibered-category-attached-to-a-moduli-problem)
   - [The pseudofunctor viewpoint](#24-the-pseudofunctor-viewpoint)
3. [Prestacks, stacks, and descent](#3-prestacks-stacks-and-descent)
   - [Descent of arrows](#31-descent-of-arrows)
   - [Descent of objects](#32-descent-of-objects)
   - [Why stackification is sometimes necessary](#33-why-stackification-is-sometimes-necessary)
   - [Moduli data are stacks](#34-moduli-data-are-stacks)
4. [Morphisms, diagonals, and inertia](#4-morphisms-diagonals-and-inertia)
   - [Two-fiber products](#41-two-fiber-products)
   - [Representable morphisms](#42-representable-morphisms)
   - [The diagonal as an isomorphism space](#43-the-diagonal-as-an-isomorphism-space)
   - [Inertia and stabilizers](#44-inertia-and-stabilizers)
   - [Separated and unramified diagonals](#45-separated-and-unramified-diagonals)
5. [Algebraic stacks and atlases](#5-algebraic-stacks-and-atlases)
   - [Definition and first consequences](#51-definition-and-first-consequences)
   - [Smooth atlases and finite flat presentations](#52-smooth-atlases-and-finite-flat-presentations)
   - [Parameter spaces and change of framing](#53-parameter-spaces-and-change-of-framing)
6. [Quotient stacks](#6-quotient-stacks)
   - [Torsors with equivariant maps](#61-torsors-with-equivariant-maps)
   - [The canonical quotient atlas](#62-the-canonical-quotient-atlas)
   - [The diagonal of a quotient stack](#63-the-diagonal-of-a-quotient-stack)
   - [Examples and warnings](#64-examples-and-warnings)
   - [An atlas criterion for the moduli problems of this book](#65-an-atlas-criterion-for-the-moduli-problems-of-this-book)
7. [Rigidification, finite quotients, and coarse spaces](#7-rigidification-finite-quotients-and-coarse-spaces)
   - [Removing a prescribed central stabilizer](#71-removing-a-prescribed-central-stabilizer)
   - [Finite group quotients](#72-finite-group-quotients)
   - [Coarse moduli spaces](#73-coarse-moduli-spaces)
   - [Base change and tame descent](#74-base-change-and-tame-descent)
8. [Generalized elliptic curves](#8-generalized-elliptic-curves)
   - [The boundary object](#81-the-boundary-object)
   - [The stack property and diagonal](#82-the-stack-property-and-diagonal)
   - [Contraction of bridge components](#82a-contraction-of-bridge-components)
   - [Decontractions and smoothing-parameter roots](#82b-decontractions-and-smoothing-parameter-roots)
   - [Weierstrass charts and contraction](#83-weierstrass-charts-and-contraction)
   - [Algebraicity and bounded boundary](#84-algebraicity-and-bounded-boundary)
9. [Modular level structures](#9-modular-level-structures)
   - [Drinfeld structures and ampleness](#91-drinfeld-structures-and-ampleness)
   - [Full, point, and cyclic level](#92-full-point-and-cyclic-level)
   - [Theta groups and pairings across the boundary](#93-theta-groups-and-pairings-across-the-boundary)
   - [When level produces a fine scheme](#94-when-level-produces-a-fine-scheme)
   - [Compactified modular stacks and coarse curves](#95-compactified-modular-stacks-and-coarse-curves)
10. [The common PEL framework](#10-the-common-pel-framework)
    - [The fixed PEL datum](#101-the-fixed-pel-datum)
    - [Abelian schemes with endomorphisms and polarization](#102-abelian-schemes-with-endomorphisms-and-polarization)
    - [The determinant condition](#103-the-determinant-condition)
    - [Prime-to-the-base level structures](#104-prime-to-the-base-level-structures)
    - [Stack, diagonal, and atlas theorems](#105-stack-diagonal-and-atlas-theorems)
11. [Hilbert moduli problems](#11-hilbert-moduli-problems)
    - [Real multiplication and polarization modules](#111-real-multiplication-and-polarization-modules)
    - [The Hilbert determinant condition](#112-the-hilbert-determinant-condition)
    - [Rigid level and coarse descent](#113-rigid-level-and-coarse-descent)
12. [Quaternionic moduli problems](#12-quaternionic-moduli-problems)
    - [Quaternionic multiplication](#121-quaternionic-multiplication)
    - [Rosati compatibility and determinant data](#122-rosati-compatibility-and-determinant-data)
    - [The resulting stack and its quotients](#123-the-resulting-stack-and-its-quotients)
13. [Coarse descent and synthesis](#13-coarse-descent-and-synthesis)
    - [Descending constructions through a coarse map](#131-descending-constructions-through-a-coarse-map)
    - [A comparison table](#132-a-comparison-table)
    - [The reusable theorem package](#133-the-reusable-theorem-package)
    - [Conclusion](#134-conclusion)

## 1. Why moduli problems form stacks

### 1.1 Objects, families, and symmetry

A moduli problem asks for a geometric space whose points classify geometric objects. This slogan is accurate only when the objects have no automorphisms. An elliptic curve $E$ has at least the involution $[-1]$ away from characteristic two, and an abelian variety with extra multiplication may have additional roots of unity acting on it. A set of isomorphism classes forgets these symmetries. That loss is not cosmetic: it destroys the correct rule for gluing families and changes intersection multiplicities, degrees of maps, and descent of line bundles.

The appropriate value of a moduli problem over a scheme $S$ is therefore a groupoid. Its objects are families over $S$ and its arrows are isomorphisms preserving every marked structure. Pulling a family back along $T\to S$ gives the value over $T$. The resulting object varying over all bases is a stack when compatible local families and compatible local isomorphisms glue.

Three examples show why each word matters.

- A sheaf of sets remembers at most one arrow between two objects. It can describe divisors or morphisms into a fixed scheme, but not an unrigidified elliptic curve.
- A stack remembers automorphisms and effective descent. It need not possess any atlas by a scheme, so it is not automatically geometric in the sense required for modular curves.
- An algebraic stack has a representable diagonal and a smooth surjective scheme atlas. It can therefore be studied by schemes while retaining stabilizers.

The goal of this book is not a theory of every possible stack. It is the exact package needed for modular and PEL moduli: descent, representable diagonals, explicit quotient atlases, controlled inertia, rigidification, finite quotients, and coarse spaces.

### 1.2 Five levels of representability

The phrase “the moduli space” often conceals five different objects.

1. A **set-valued functor** records isomorphism classes over each base. It may fail the sheaf condition because locally isomorphic objects need not be globally isomorphic in a unique way.
2. A **sheaf** is a set-valued functor satisfying local uniqueness and existence. It still has no place for stabilizers.
3. A **stack** is groupoid-valued and satisfies descent for arrows and objects.
4. An **algebraic stack** is a stack accessible by a smooth scheme atlas and with representable diagonal.
5. A **fine moduli scheme** represents the original groupoid by a discrete groupoid. It carries a universal family and forces all automorphism groups to be trivial.

A **coarse moduli space** lies in another direction. It receives a map from the stack, identifies geometric points exactly up to isomorphism, and is universal for maps from the stack to algebraic spaces. It generally carries no universal family. Thus “coarse” and “fine” are not two strengths of the same representation: the coarse space discards stabilizers, while a fine space exists only after stabilizers have already vanished.

For example, over a field of characteristic different from $2$ and $3$, the parameter $j$ classifies elliptic curves over an algebraic closure. Yet the affine $j$-line is not the fine moduli space of elliptic curves. At generic $j$ there remains the automorphism $[-1]$, and at $j=0,1728$ the stabilizer grows. The moduli stack remembers that jump; the $j$-line does not.

### 1.3 The base site and conventions

Fix a base scheme $S_0$. Unless stated otherwise, all test schemes are $S_0$-schemes and coverings
are fppf coverings. The fpqc topology gives the same stack assertions for the objects considered
here because their presentations retain one of Book 10's scheme-effectivity criteria: affine or
finite structure, quasi-affineness, or compatible relatively ample data. Morphisms, line bundles,
and group structures then descend by full faithfulness. We use fppf atlases because finite
presentation is essential in the geometric applications.

A fiber product of stacks is always a two-fiber product: an object over $T$ includes objects on the two sides and an isomorphism between their images. Equality of objects is never substituted for an isomorphism. A property of a morphism from a stack is called representable when every pullback along a scheme is represented by an algebraic space; in the explicit cases below it will in fact be a scheme.

We use “finite” for finite morphisms and “finite locally free” when flatness and constant local rank are intended. These differ at bad residue characteristics. A level structure of order $N$ is never called etale unless $N$ is invertible on the base.

### 1.4 Assumed inputs

This is a book about stacks. The geometry of abelian schemes, of finite flat group schemes, and of
projective parameter spaces enters as an input rather than as a subject. The following results are
quoted from earlier books, with the sections named, and are used below without reproof.

- Effective faithfully flat descent for affine, finite, quasi-affine, and compatibly polarized
  schemes, together with morphisms, quasi-coherent sheaves, vector bundles, affine or finite group
  objects, actions, and torsors in those cases, and the tables of properties that are fpqc local
  on the base: Book 10, Chapters 5–16. Descent of smoothness along a faithfully flat
  cover of the **source**, which is a different statement and is what the quotient atlas of
  Section 6.2 requires, is Book 10 §10.5.
- Relatively ample bundles, Hilbert polynomials, Hilbert and graph parameter schemes, and fpqc
  descent of ampleness: Book 8.
- Divisors, degrees, Riemann--Roch, and very ampleness on relative curves, including the nodal
  ones: Book 9.
- Cohomology of a proper flat family and its base change: when the fiber dimensions of $H^0$ and
  $H^1$ are constant, the pushforward is locally free of that rank and its formation commutes with
  arbitrary base change: Book 15.
- Finite locally free algebras and morphisms, their ranks, and their norms and traces: Book 26
  §§6, 10.
- Affine group schemes, closed subgroup schemes, actions and invariants, and the theorem that the
  quotient of an affine group scheme by a finite locally free closed subgroup is an affine scheme
  for which the projection is a finite locally free torsor: Book 27 §§5, 8, 9.4.
- Finite flat commutative group schemes, multiplication kernels, and etaleness of the kernel when
  the order is invertible: Book 28 §§4, 5.
- Cartier duality, perfect pairings of finite locally free group schemes, the group-scheme Weil
  pairing on the torsion of an abelian scheme, and its elliptic form
  $e_n:E[n]\times E[n]\to\mu_n$: Book 34 §§8, 14.2–14.5.
- Abelian schemes: the rigidity lemma and the homomorphism lemma, Book 35 §1.3; unramifiedness
  and separatedness of the homomorphism sheaf, so that a homomorphism is determined by any
  schematically dense restriction, Book 35 §4.1; the theorems of the square and the cube, Book 35
  §§2.2–2.3; the dual abelian scheme, the Poincare bundle, the dual homomorphism $f^\vee$, and
  biduality, Book 35 §§3.1–3.4; torsion $A[n]$ finite locally free of order $n^{2g}$ and etale
  when $n$ is invertible, Book 35 §4.3; quotients by finite locally free subgroup schemes, Book
  35 §5; Weil pairings and their perfectness in every characteristic, Book 35 §§7.1–7.3;
  polarizations, their symmetry, type and degree, and the induced alternating pairing
  $e_n^\lambda$ with its perfectness criterion, Book 35 §§8.1–8.5; the theta group
  $\mathcal G(L)$ of a rigidified ample bundle as a central extension of $K(L)=\ker\lambda_L$ by
  $\mathbf G_m$, and its commutator pairing, Book 35 §9.2.
- The Serre tensor construction: for a finitely generated projective module $M$ over a commutative
  ring $\mathcal O$ acting on an abelian scheme $A$, the fppf sheaf
  $T\mapsto A(T)\otimes_{\mathcal O}M$ is an abelian scheme $A\otimes_{\mathcal O}M$, of relative
  dimension $rg$ when $M$ has rank $r$, formed compatibly with arbitrary base change (Book 35
  §5.6, Theorem 5.3), functorial in $M$ and in $A$ (Proposition 5.4), and compatible with duality
  through $(A\otimes_{\mathcal O}M)^\vee\simeq A^\vee\otimes_{\mathcal O}M^\vee$, whose
  fractional-ideal case reads $(A\otimes\mathfrak c)^\vee\simeq A^\vee\otimes\mathfrak c^{-1}$
  (Theorem 5.6).
- Prime-adic Tate modules over a separably closed field $k$ with $\ell$ invertible in $k$:
  $T_\ell A=\varprojlim_mA[\ell^m](k)$ is free of rank $2g$ over $\mathbf Z_\ell$ with
  $T_\ell A/\ell^mT_\ell A\simeq A[\ell^m](k)$, functorially, so that an automorphism of $A$ acts
  through $\operatorname{GL}_{2g}(\mathbf Z_\ell)$: Book 35 §7.6, Theorem 7.3. The perfect limit
  Weil pairing is Proposition 7.4 there. For $g=1$ this is exactly the rank-two statement used in
  Section 9.4.
- Theta groups in standard form, for a relatively ample rigidified bundle $L$ on an abelian scheme
  whose polarization degree $d^2$ has $d$ invertible on the base: perfectness of the commutator
  pairing $c_L$ (Book 35 Proposition 9A.2); the symplectic normal form for a perfect alternating
  pairing on a finite abelian group (Lemma 9A.3) and the resulting etale-local identification of
  $K(L)$ with $K(\delta)\times K(\delta)^D$ for a locally constant type $\delta$ (Theorem 9A.4);
  rigidity of central extensions of a finite etale group of invertible order by $\mathbf G_m$
  (Theorem 9A.5); existence of theta structures etale-locally (Theorem 9A.6); the description of
  $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ as a finite etale group scheme of order
  $d^2|\!\operatorname{Sp}(\delta)|$ and of the theta structures as a torsor under it, represented
  by a finite etale scheme (Theorem 9A.7); the Stone--von Neumann theorem, that a module of
  central character one is $V(\delta)$ tensored with its weight-zero part and that a module of
  rank $d$ has endomorphism ring $\mathcal O_S$ (Theorem 9A.8, Corollary 9A.9); and theta
  coordinates, that $\pi_*L$ is such a module of rank $d$ and that a theta structure produces a
  basis $\{\theta_x\}$ unique up to one common unit and compatible with base change (Theorem
  9A.10, resting on the vanishing theorem and rank computation of Book 35 §8.6).

Two remarks fix the range of the last item, since it is used below at its boundary.
Chapter 9A of Book 35 assumes throughout that the order $d$ of the type is invertible on the base;
every use site below states the invertibility it needs rather than inheriting it silently. And
Chapter 9A is a chapter about abelian schemes, whereas the generalized elliptic curves of Chapter
9 acquire Neron polygons as fibers, which are singular, have disconnected smooth locus, and are
not abelian schemes at all. Nothing in Book 34 or Book 35 applies to them directly. The
theta group of an ample level bundle on a generalized elliptic curve, the perfectness of its
commutator, the resulting extension of the Weil pairing across the boundary, and the theta
coordinates it produces are therefore constructed and proved from scratch in Section 9.3, which
imports from Book 35 only those parts of Chapter 9A that are statements about central extensions
of finite etale group schemes and about their representations, and are not statements about
abelian schemes.

## 2. Categories fibered in groupoids

### 2.1 Cartesian arrows

Let $p:\mathcal X\to\mathcal C$ be a functor. Think of $\mathcal C$ as schemes and $\mathcal X$ as all families at once. Suppose $x$ lies over $S$ and $f:T\to S$. A morphism $\phi:y\to x$ over $f$ is **cartesian** if every morphism $z\to x$ whose base map factors as $U\xrightarrow{g}T\xrightarrow{f}S$ factors uniquely through $\phi$ by a morphism $z\to y$ over $g$.

The definition is a universal property because “pull back the family” must be characterized independently of coordinates. For an actual family $X\to S$, the arrow

$$
X\times_S T\longrightarrow X
$$

is cartesian. Given $U\to T$ and a map into $X$ compatible over $S$, the defining property of the ordinary fiber product supplies the unique map into $X\times_ST$.

A **category fibered in groupoids** over $\mathcal C$ is a category $\mathcal X$ with such a functor $p$ satisfying two conditions:

- every $f:T\to S$ and every $x$ over $S$ admit a cartesian arrow $f^*x\to x$ over $f$;
- every arrow lying over an identity is invertible.

The second condition makes each fiber $\mathcal X(S)$ a groupoid. It also implies that every arrow factors as a vertical isomorphism followed by a chosen cartesian arrow.

### 2.2 Pullback and coherence

Cartesian pullbacks are unique up to a unique vertical isomorphism. Indeed, if $y\to x$ and $y'\to x$ are cartesian over the same $f$, each universal property gives a vertical map to the other. Their composites factor the original arrows in the same way as the identity; uniqueness makes the composites identities.

This observation is the source of all coherence. Given $U\xrightarrow{g}T\xrightarrow{f}S$, both $g^*f^*x$ and $(fg)^*x$ are cartesian pullbacks of $x$ to $U$. Hence there is a canonical isomorphism

$$
c_{f,g}:g^*f^*x\xrightarrow{\sim}(fg)^*x.
$$

For three composable maps, the two composites built from the $c_{f,g}$ agree because both are vertical isomorphisms compatible with the same cartesian arrow. Likewise $\operatorname{id}_S^*x\simeq x$. Thus coherence is a theorem of uniqueness, not an extra collection of arbitrary equations.

A choice of one pullback for every pair $(f,x)$ is called a cleavage. It is convenient notation, not mathematical structure on the moduli problem. Different cleavages give equivalent descriptions.

### 2.3 The fibered category attached to a moduli problem

Suppose an object over $S$ is a scheme $X\to S$ equipped with finitely many structures that commute with base change: sections, morphisms, group laws, line bundles, pairings, or actions by a fixed ring. Form a category whose objects are all such families and whose arrows from an object over $T$ to one over $S$ are cartesian squares together with isomorphisms preserving the extra data.

Ordinary base change gives cartesian lifts. An arrow over the identity is precisely an isomorphism of structured families. Consequently this category is fibered in groupoids. The construction works for generalized elliptic curves and for PEL abelian schemes because all their defining structures pull back.

One must include the isomorphism in an arrow. A mere map of total spaces can fail to be cartesian and can change the object rather than transport it. For polarized abelian schemes, the arrow must commute with the action and carry the target polarization to the source polarization. If the polarization is specified only up to a scalar subgroup, that qualification must also appear in the arrow definition.

### 2.4 The pseudofunctor viewpoint

Equivalently, assign to $S$ a groupoid $\mathcal X(S)$ and to $f:T\to S$ a pullback functor $f^*:\mathcal X(S)\to\mathcal X(T)$. Composition is respected through the coherent isomorphisms $c_{f,g}$ rather than by literal equality. This is a contravariant pseudofunctor.

Starting with a fibered category and choosing pullbacks produces this pseudofunctor. Conversely, from a pseudofunctor one forms a total category: an arrow $(T,y)\to(S,x)$ consists of $f:T\to S$ and an isomorphism $y\simeq f^*x$. Coherence defines composition. These constructions are inverse up to equivalence.

The pseudofunctor language is efficient for descent calculations, while the fibered-category language makes representability and cartesian maps intrinsic. We pass between them without identifying equivalent groupoids literally.

## 3. Prestacks, stacks, and descent

### 3.1 Descent of arrows

Let $\{S_i\to S\}$ be an fppf cover, and write $S_{ij}=S_i\times_SS_j$. Fix $x,y\in\mathcal X(S)$. Their isomorphisms form a presheaf

$$
\underline{\operatorname{Isom}}_S(x,y)(T)
=\operatorname{Isom}_{\mathcal X(T)}(x_T,y_T).
$$

A fibered category is a **prestack** if every such presheaf is a sheaf. Explicitly, isomorphisms $\alpha_i:x_{S_i}\to y_{S_i}$ that agree on every $S_{ij}$ glue to a unique $\alpha:x\to y$.

This is descent of arrows, or full faithfulness of restriction to descent data. It says nothing yet about constructing an object from local objects. Book 10 proves it for schemes and structured schemes: morphisms descend uniquely, and equality can be checked after a faithfully flat cover. Since compatibility with a section, action, or pairing is an equality of morphisms, it descends as well.

The prestack condition is stronger than separatedness of a set-valued functor. It glues every isomorphism, including automorphisms. For a quotient problem, those automorphisms are precisely the local changes of trivialization that make the quotient meaningful.

### 3.2 Descent of objects

A descent datum consists of objects $x_i\in\mathcal X(S_i)$ and isomorphisms

$$
\theta_{ij}:x_j|_{S_{ij}}\xrightarrow{\sim}x_i|_{S_{ij}}
$$

such that $\theta_{ii}=1$, $\theta_{ji}=\theta_{ij}^{-1}$, and on $S_{ijk}$,

$$
\theta_{ij}\theta_{jk}=\theta_{ik}.
$$

A **stack** is a prestack for which every descent datum is effective: there is $x\in\mathcal X(S)$ and compatible isomorphisms $x|_{S_i}\simeq x_i$. The descended object is unique up to a unique isomorphism once the comparison maps are fixed.

The proof pattern for geometric objects is rigid. First verify an affine, finite, quasi-affine, or
compatible-polarization criterion and descend the underlying algebraic-space datum to a scheme.
Then descend line bundles and finite locally free modules. Descend all structure morphisms by full
faithfulness, check identities after pulling back to the cover, and finally descend geometric
properties such as properness, smoothness, or finite local freeness. This is precisely the order
established in Book 10.

For a family of abelian varieties, connectedness of geometric fibers is checked after residue-field extension; Book 35 §1.4 records that smoothness, properness, finite presentation, the group law, and geometric connectedness all survive base change and may be tested after a faithfully flat quasi-compact one. For a generalized elliptic curve, the polygonal fiber condition and the action on components are likewise geometric and fpqc local. Hence neither application requires a new general effectivity theorem.

### 3.3 Why stackification is sometimes necessary

A natural quotient construction may be a prestack but not a stack. Suppose one starts with the action groupoid $G(T)\times X(T)\rightrightarrows X(T)$. It sees only objects globally represented by points of $X(T)$. After a cover, however, local points may be related by transition elements of $G$ defining a nontrivial $G$-torsor. Such local data need not come from a global point of $X(T)$.

Stackification adds exactly these twisted objects. It does not arbitrarily add geometric points: it makes descent data effective while preserving the already correct isomorphism sheaves. For group actions, the resulting objects are $G$-torsors with equivariant maps to $X$.

By contrast, taking the sheafification of orbit sets loses stabilizers first and repairs only set-valued descent afterward. The two operations differ. The action of a finite group $G$ on a point gives a one-point orbit sheaf, while its quotient stack has automorphism group $G$ at that point.

### 3.4 Moduli data are stacks

**Structured-family stack theorem.** Let objects over $S$ be schemes of finite presentation equipped with a finite list of the following data: morphisms, sections, finite locally free group objects, actions, line bundles with rigidifications, finite locally free tensors and perfect pairings. Impose conditions that are equalities of maps or properties fpqc local on the base. If the underlying class of schemes has effective fpqc descent, then the resulting fibered category is an fpqc stack.

**Proof strategy.** Separate construction from properties. The theorem's hypothesis on the
underlying class, verified in applications by one of Book 10's explicit criteria, supplies scheme
effectivity; Book 10 also supplies descent for the sheaves and group objects and full faithfulness
for every structure map. Thus all data descend and their equations can be checked upstairs. The
remaining adjectives descend by their stated locality. For an ample polarization, use the
descended rigidified line bundle and fpqc descent of ampleness from Book 8. This constructs an
effective object. Uniqueness follows from descent of isomorphisms. $\square$

The theorem deliberately requires a finite list of fixed structures. An action by an order is still finite data because the order is finitely generated and its relations can be imposed on finitely many generators. A determinant condition is equality of finitely many coefficients in characteristic polynomials on a finite locally free Lie bundle.

## 4. Morphisms, diagonals, and inertia

### 4.1 Two-fiber products

Given $\mathcal X\to\mathcal Z\leftarrow\mathcal Y$, an object of
$\mathcal X\times_{\mathcal Z}\mathcal Y$ over $T$ is a triple

$$
(x,y,\alpha),\qquad
\alpha:F(x)\xrightarrow{\sim}G(y).
$$

An arrow $(x,y,\alpha)\to(x',y',\alpha')$ is a pair of arrows whose images make the evident square commute. The inserted isomorphism $\alpha$ is indispensable. If literal equality were required, the construction would depend on choices of representatives and fail to be invariant under equivalence.

Fiber products of stacks are stacks: descent is performed componentwise, and the comparison isomorphism descends because the target is a prestack. This gives the main mechanism for defining level substacks, fixed-determinant loci, and pullbacks of atlases.

### 4.2 Representable morphisms

A morphism $F:\mathcal X\to\mathcal Y$ is **representable by schemes** if for every scheme $T\to\mathcal Y$, the stack $T\times_{\mathcal Y}\mathcal X$ is represented by a scheme. It is representable by algebraic spaces if the same statement holds with algebraic spaces. A representable morphism is finite, smooth, proper, or etale when every such base change has that property.

This definition transports ordinary geometry to stacks without ambiguity. It also exposes a quick obstruction: a representable morphism is injective on stabilizers. Indeed, an automorphism of $x$ mapping to the identity at $F(x)$ becomes an automorphism of the corresponding object in a scheme fiber; schemes have no nontrivial object automorphisms.

The converse is false. Injectivity on stabilizers does not alone construct a representing space. In our applications representability is proved by an isomorphism functor, a Hilbert parameter space, or a finite level-structure scheme.

### 4.3 The diagonal as an isomorphism space

The diagonal

$$
\Delta_{\mathcal X}:\mathcal X\longrightarrow\mathcal X\times\mathcal X
$$

is the universal isomorphism problem. Pull it back along a scheme $T$ carrying two objects $x,y\in\mathcal X(T)$. The resulting fiber is precisely

$$
\underline{\operatorname{Isom}}_T(x,y).
$$

Therefore the diagonal is representable exactly when isomorphisms between two families are represented. This is often easier than representing the objects themselves. Graphs of maps, the fixed Hilbert polynomial, and preservation of tensors cut the isomorphism functor out of a scheme of morphisms constructed from Book 8.

For proper polarized curves or abelian schemes, an isomorphism preserves a fixed relatively ample bundle. A sufficiently high power embeds both objects into projective bundles. An isomorphism is then represented by the locally closed locus of projective transformations carrying one embedded family and all marked tensors to the other. Closed equations impose preservation; invertibility is open. Thus the isomorphism sheaf is separated and of finite presentation.

Two finiteness points are implicit here. The construction is local on the base, so the section
bundles may first be trivialized faithfully flatly and the resulting scheme then descended. Also
the graph Hilbert polynomial must be fixed. It is fixed in the polarized problem because the two
projections of a graph pull back the two prescribed ample bundles. Book 8 therefore supplies one
bounded graph Hilbert scheme. The graph condition and invertibility are open, while preservation
of the marked structures and the two inverse identities are closed equalities of morphisms. This
proves representability over an arbitrary test scheme without invoking morphisms of unbounded
degree.

### 4.4 Inertia and stabilizers

The **inertia stack** is

$$
I_{\mathcal X}
=\mathcal X\times_{\mathcal X\times\mathcal X}\mathcal X,
$$

where both maps are diagonals. Over an object $x\in\mathcal X(T)$ its fiber is the automorphism group sheaf $\underline{\operatorname{Aut}}_T(x)$. The identity automorphism gives a section $\mathcal X\to I_{\mathcal X}$.

Inertia measures the precise failure of the stack to be a sheaf of sets. The stack is equivalent to a sheaf exactly when every stabilizer is trivial. A coarse space can have no record of inertia: all elements of $\operatorname{Aut}(x)$ map to the identity of the same coarse point.

For $[X/G]$, a geometric point represented by $x\in X(k)$ has stabilizer

$$
G_x=\{g\in G:g\cdot x=x\}.
$$

The inertia is not usually the constant group $G$ over the quotient; it is the quotient of the stabilizer locus $\{(x,g):gx=x\}$ by conjugation. This distinction matters when stabilizers jump, as at special elliptic $j$-invariants.

### 4.5 Separated and unramified diagonals

An algebraic stack is called separated when its diagonal is proper, and it has finite diagonal when the diagonal is finite. A Deligne--Mumford stack is an algebraic stack whose diagonal is unramified; equivalently, it admits an etale atlas. We use the term only under these hypotheses.

Finite inertia alone does not imply a finite diagonal without quasi-compactness and separation of the isomorphism spaces. Conversely, a finite diagonal makes every stabilizer finite but does not make it trivial. For polarized abelian schemes the polarization forces the automorphism group to be finite. Rigidity for homomorphisms of abelian schemes shows that the homomorphism functor has no infinitesimal deformation once its value at the identity is fixed; this is Book 35 §4.1, where $\underline{\operatorname{Hom}}_S(A,B)$ is proved unramified and separated, together with the rigidity lemma and the homomorphism lemma of Book 35 §1.3. A high power of an inducing ample bundle embeds the abelian scheme, making the polarization-preserving automorphism scheme affine and of finite presentation. The valuative criterion extends a generic such automorphism: take the closure of its graph, use properness of the abelian schemes, and use the same rigidity, in the form that a homomorphism is determined by a schematically dense restriction, to extend the group identities and the inverse. The automorphism scheme is therefore proper as well as affine, hence finite. At a bad prime finite must still not be silently replaced by etale; the relevant unramifiedness assertion has to be checked in the chosen integral problem.

## 5. Algebraic stacks and atlases

### 5.1 Definition and first consequences

An fppf stack $\mathcal X$ is an **algebraic stack** if its diagonal is representable by algebraic spaces and there is a scheme $U$ with a representable, smooth, surjective morphism

$$
U\longrightarrow\mathcal X.
$$

Such a map is a smooth atlas. Pulling it back along itself gives an algebraic space

$$
R=U\times_{\mathcal X}U
$$

with source and target maps to $U$. The stack can be recovered from the groupoid $R\rightrightarrows U$ by allowing torsors and descent. Thus an atlas is not a bijective parametrization: distinct points of $U$ may represent isomorphic objects, and the fiber over one object records its frames.

If $R$ is a scheme in a presentation, the whole geometry is controlled by schemes. This will hold for all explicit quotient charts below. Properties local for the smooth topology may be checked on $U$, while stabilizer-sensitive properties remain encoded in $R$.

### 5.2 Smooth atlases and finite flat presentations

A **finite flat presentation** means a representable finite, flat, surjective map from a scheme.
It gives especially tight fppf control of the stack by a finite relation, but it is not a smooth
atlas unless it is also smooth, equivalently finite etale. Thus it is supplementary structure,
not a stronger instance of a smooth atlas. A finite surjective map that is not flat is not called
a finite flat presentation here.

For a quotient $[X/G]$, the canonical presentation $X\to[X/G]$ inherits the property of the group scheme $G\to S_0$: it is a smooth atlas if $G$ is smooth, finite etale if $G$ is etale and finite, and a finite flat presentation if $G$ is finite locally free. In the last case a separate smooth atlas is constructed in Section 6.2.

A fine moduli scheme has the identity as an atlas, but the existence of a finite flat presentation does not make a stack a scheme. The classifying stack of a nontrivial finite flat group has such a presentation by a point and still has that group as inertia.

### 5.3 Parameter spaces and change of framing

Moduli objects are made representable by adding frames. Choose a canonical relatively ample line bundle, take a sufficiently high power, and choose a basis of its pushforward. The basis embeds the family into a fixed projective space. Book 8 represents families with the required Hilbert polynomial by a Hilbert scheme. Group laws, sections, endomorphisms, and polarizations then occupy closed or locally closed loci; smoothness and nondegeneracy are open conditions.

Changing the basis acts through a general linear group. Consequently the unframed moduli problem is locally a quotient

$$
[H/\operatorname{GL}_r],
$$

where $H$ is a locally closed parameter scheme. The frame bundle of any family is a $\operatorname{GL}_r$-torsor, so the map $H\to\mathcal X$ is smooth and surjective. This is the standard atlas mechanism.

There is no circular use of a universal moduli space here. Book 8 constructs the parameter scheme, and Book 10 descends the family after changes of frame. The quotient stack packages precisely those changes.

## 6. Quotient stacks

### 6.1 Torsors with equivariant maps

Let a flat finitely presented group scheme $G\to S_0$ act on an $S_0$-scheme $X$. The quotient stack $[X/G]$ assigns to $T$ the groupoid of pairs

$$
(P,u),\qquad P\to T\text{ a right }G_T\text{-torsor},\qquad
u:P\to X_T,
$$

where $u(pg)=g^{-1}u(p)$. The inverse appears because the torsor acts on the right and $X$ on the left. An arrow is a $G_T$-equivariant isomorphism of torsors commuting with $u$.

This definition includes twisted forms automatically. The trivial torsor $G_T$ with map $g\mapsto g^{-1}x$ corresponds to $x\in X(T)$. Every torsor becomes trivial fppf-locally, so every quotient-stack object is locally of this form. Descent for torsors and equivariant morphisms, proved in Book 10, shows that $[X/G]$ is a stack.

The naive orbit presheaf $T\mapsto X(T)/G(T)$ sees only trivial torsors. Even its sheafification remembers no stabilizers. The quotient stack is therefore the correct moduli quotient whenever changes of frame may twist.

### 6.2 The canonical quotient atlas

There is a map $q:X\to[X/G]$ sending $x:T\to X$ to the trivial torsor with its equivariant map. It is representable. More precisely, for $(P,u)\in[X/G](T)$ there is a canonical isomorphism

$$
T\times_{[X/G]}X\simeq P.
$$

To see this, a point of the fiber product is a point $x$ of $X$ together with an isomorphism between its trivial torsor and $P$. Such an isomorphism is determined by the image of the identity section, a point $p\in P$, and compatibility forces $x=u(p)$. This construction is reversible and respects base change.

Since $P\to T$ is an fppf $G$-torsor, $q$ is flat, locally of finite presentation, and surjective. If $G$ is smooth, etale, or finite locally free, then $q$ has the same property. Thus:

**Quotient-atlas theorem.** If $G$ is smooth and finitely presented, $X\to[X/G]$ is a smooth atlas. If $G$ is finite locally free, it is a finite flat presentation. Under the locally noetherian, finite-presentation, and quasi-projective hypotheses used in this book, $[X/G]$ also admits a smooth scheme atlas.

For the last assertion, the regular representation on the rank-$r$ coordinate algebra of $G$, in
the matrix-coefficient form of Book 27 §19.2, is faithful and gives a closed immersion
$G\hookrightarrow\operatorname{GL}_r$. Give $X\times\operatorname{GL}_r$ the action

$$
g\cdot(x,h)=(gx,hg^{-1}).
$$

It is free because it is free on the second factor, and its scheme quotient is

$$
U=(X\times\operatorname{GL}_r)/G;
$$

the invariant-affine proof of Section 7.2 applies and uses no assertion about quotient stacks.
The induced map $U\to[X/G]$ is representable, and after pulling back to the finite flat
presentation $X\to[X/G]$ it becomes
$X\times(\operatorname{GL}_r/G)\to X$. The homogeneous space $\operatorname{GL}_r/G$ exists as an
affine scheme, and $\operatorname{GL}_r\to\operatorname{GL}_r/G$ is a finite locally free
$G$-torsor, by Book 27 §9.4. It is moreover smooth over the base, and that point needs care: it is
not an instance of the tables of Book 10 §§10.3–10.4, which descend a property of a morphism along
a faithfully flat cover of its **base**, whereas here $\operatorname{GL}_r$ is a faithfully flat
cover of the **source** $\operatorname{GL}_r/G$. The statement actually used is the source-descent
lemma of Book 10 §10.5, in its smooth-quotient form: over a locally noetherian base, a quotient of
a smooth group scheme by a finite locally free closed subgroup is smooth, the homogeneity
hypothesis of that lemma being supplied by left translation. Hence $U\to[X/G]$ is smooth and
surjective. This is the required smooth atlas even when $G$ itself is non-smooth.

The identification $T\times_{[X/G]}X\simeq P$, and hence the canonical presentation, is fully
local and does not assume that an orbit scheme exists. Only the additional smooth atlas in the
finite flat case uses the finite free quotient just constructed.

### 6.3 The diagonal of a quotient stack

Let $(P,u)$ and $(Q,v)$ be two objects over $T$. The pullback of the diagonal is the sheaf of equivariant isomorphisms $\phi:P\to Q$ satisfying $v\phi=u$. The sheaf $\underline{\operatorname{Isom}}_G(P,Q)$ is a twisted form of $G_T$ and is represented by a $G_T$-torsor. The additional equality cuts out an equalizer.

Assume $G$ is affine and finitely presented and $X$ is separated over $S_0$. The torsor of isomorphisms is affine and finitely presented over $T$. Because the diagonal of $X$ is closed, the equality $v\phi=u$ defines a closed subscheme. Hence the diagonal of $[X/G]$ is representable, separated, and finitely presented. If $G$ is finite, it is finite. If $G$ is unramified, the diagonal is unramified.

These hypotheses are sufficient rather than maximal. They are exactly what the parameter schemes and frame-change groups below provide. Without separatedness of $X$, the equalizer need not be closed. Without affineness of $G$, the isomorphism torsor need not be a scheme affine over $T$.

### 6.4 Examples and warnings

For $X=S_0$ with trivial action, $[X/G]=BG$, the classifying stack of $G$-torsors. Its canonical presentation $S_0\to BG$ has fiber $G$; it is a smooth atlas exactly when $G$ is smooth. Its coarse sheaf of orbits is just $S_0$, but its inertia is $G$ up to conjugation. This is the smallest counterexample to the claim that a quotient stack is its orbit space.

If $G=\mathbf G_m$ acts on $\mathbf A^1$ by scaling, the nonzero locus has trivial stabilizer and quotient a point, while the origin has stabilizer $\mathbf G_m$. The quotient stack is not separated because its diagonal is not proper. Stabilizer dimension can therefore jump even when the atlas is smooth.

A constant finite group scheme is finite etale over every base, so its quotient stack is
Deligne--Mumford and its canonical presentation is finite etale. If its order is invertible, it is
also linearly reductive and the quotient is tame. When the order is not invertible the constant
group is still etale, but naturally occurring group schemes such as $\mu_p$ are not etale in
characteristic $p$. “Finite stabilizer” must not be replaced by “etale stabilizer,” and
“finite etale” must not be replaced by “tame.”

### 6.5 An atlas criterion for the moduli problems of this book

**Framed-parameter atlas theorem.** Suppose a stack $\mathcal X$ classifies proper flat finitely presented schemes with a canonical relatively ample line bundle $\mathcal L$, and suppose:

1. a fixed power $\mathcal L^m$ has a base-change-compatible locally free pushforward of rank $r$ and gives a closed immersion;
2. the relevant Hilbert polynomial is fixed;
3. all additional structures are represented by locally closed conditions in the resulting parameter scheme;
4. isomorphisms preserving the structures are representable.

Then $\mathcal X$ is algebraic, with a smooth atlas by the scheme of objects framed by a basis of the pushforward.

**Proof.** The framed objects form a locally closed subscheme $H$ of the Hilbert parameter space. The frame-change group $G=\operatorname{GL}_r$ acts on $H$. A family in $\mathcal X(T)$ acquires a frame after the fppf cover given by its frame bundle, and a framed family gives a map to $H$. Changes between frames are exactly $G$-valued arrows. Hence $\mathcal X\simeq[H/G]$. The quotient-atlas theorem of Section 6.2 makes $H\to\mathcal X$ smooth and surjective; its proof uses only torsor descent and does not use the present atlas criterion. Representability of the diagonal follows from the assumed isomorphism spaces. $\square$

The first condition is applied only where the needed base-change statement is available. Here
explicit Weierstrass or level charts replace it when necessary; no broader cohomological
base-change statement is used.

## 7. Rigidification, finite quotients, and coarse spaces

### 7.1 Removing a prescribed central stabilizer

Sometimes a subgroup of automorphisms occurs in every object and acts trivially on the underlying coarse geometry. For polarized abelian schemes, scalar roots of unity can have this character. Adding level removes them, but another operation is useful when level should not be chosen.

Let $\mathcal X$ be a stack and let $H\to\mathcal X$ be a flat finitely presented subgroup of inertia such that $H_x\subseteq\operatorname{Aut}(x)$ is central and is preserved by every isomorphism. The **rigidification** $\mathcal X\mathbin{\!\sslash\!}H$ has the same objects locally, but its isomorphism sheaves are the fppf quotients

$$
\underline{\operatorname{Isom}}_{\mathcal X}(x,y)/H_x,
$$

followed by stackification. The map $\rho:\mathcal X\to\mathcal X\mathbin{\!\sslash\!}H$ sends

$$
\operatorname{Aut}_{\mathcal X}(x)\longrightarrow
\operatorname{Aut}_{\mathcal X\sslash H}(\rho x)
$$

with kernel $H_x$ and, fppf-locally, quotient the target.

Centrality is decisive: without it, composition of cosets is not well defined. Compatibility under isomorphism is what allows the local quotients to glue. Rigidification does not quotient the objects by an action on their underlying schemes; it quotients a specified part of their automorphism groups.

The construction has the following universal property, which also proves that it is independent of
the chosen local presentation. If $F:\mathcal X\to\mathcal Y$ sends every section of $H_x$ to the
identity of $F(x)$, then $F$ is constant on the displayed cosets. It therefore factors through the
quotient prestack and, because $\mathcal Y$ is a stack, uniquely through its stackification. Thus

$$
\operatorname{Hom}(\mathcal X\mathbin{\!\sslash\!}H,\mathcal Y)
\simeq
\{F:\mathcal X\to\mathcal Y:F(H)=1\}.
$$

To compute automorphisms, lift an arrow in the stackification to a cover on which it is represented
by an arrow of $\mathcal X$. Two lifts differ exactly by a section of $H$; descent of arrows then
gives the asserted quotient. In particular $\rho$ is an fppf gerbe banded by $H$, its relative
inertia is $H$, and the inertia after rigidification is $I_{\mathcal X}/H$. This verifies the
kernel statement rather than building it into the definition.

Locally the construction is transparent. If $\mathcal X=[X/G]$, a central subgroup $H\subseteq G$ acts trivially on $X$, and the flat quotient $G/H$ exists, then

$$
[X/G]\mathbin{\!\sslash\!}H\simeq[X/(G/H)].
$$

Indeed, both sides have the same local $X$-objects and changes of frame differing by $H$ become equal. These local identifications glue by the universal property. An atlas for $[X/G]$ is still an atlas after replacing $G$ by $G/H$; on overlaps the arrow scheme is the corresponding quotient. Consequently rigidification preserves algebraicity in the finite-flat and smooth-affine quotient charts used here.

### 7.2 Finite group quotients

Assume in this section that $S_0$ is locally noetherian and that $X$ is finitely presented. Let a finite locally free group scheme $G$ act on a quasi-projective $S_0$-scheme $X$. There is a quasi-projective categorical scheme quotient $Y=X/G$, and $X\to Y$ is finite and surjective. It is important that this is not called the fppf sheafification of $T\mapsto X(T)/G(T)$: with stabilizers or a non-linearly-reductive group, that sheaf need not be represented by the invariant scheme and would have the wrong base-change behavior.

**Proof strategy.** First produce $G$-stable affine neighborhoods. Choose a relatively ample bundle $L$. The norm of the pullback of $L$ along the finite locally free projection $G\times X\to X$ has a canonical $G$-linearization: coassociativity of the action identifies its two pullbacks on $G\times X$, and the norm is transitive on $G\times G\times X$. It is ample by the finite-norm argument of Book 10. Given a geometric orbit, a sufficiently high invariant section avoids that finite orbit; its nonvanishing locus is affine and $G$-stable. Faithfully flat descent and noetherian approximation spread this neighborhood from the geometric fiber to a neighborhood on the base. Such opens cover $X$.

If $X=\operatorname{Spec}A$, write the coaction as $\alpha:A\to A\otimes H$, where $H$ is finite locally free. Multiplication by $\alpha(a)$ on the finite locally free $A$-module $A\otimes H$ has a monic characteristic polynomial. Translation by the universal group element conjugates this multiplication operator; hence all characteristic coefficients are invariant. Cayley--Hamilton, followed by the counit $A\otimes H\to A$, shows that $a$ satisfies that monic polynomial over $A^G$. Thus $A$ is integral over $A^G$. Since finitely many generators of $A$ over the base also generate it as an $A^G$-algebra, $A$ is finite over $A^G$. The spectrum of $A^G$ has the universal property for invariant maps to affine schemes. The invariant affine opens agree on their invariant principal overlaps, so their quotients glue. A map to an arbitrary scheme, and then to an algebraic space after an etale cover of the target, factors on these opens and the factorizations agree by uniqueness. This proves the categorical universal property and finiteness.

Finally, the linearized norm bundle used to construct the invariant affine cover has canonical
multiplicative descent functions on every invariant affine overlap. If $r$ is the rank of $G$,
the image of any residual stabilizer character is a finite subgroup of $\mathbf G_m$ of rank at
most $r$; the power $r!$ kills every one of them. On invariant affine charts the resulting
transition functions lie in $(A^G)^\times$, satisfy the cocycle, and define an invertible sheaf
on $Y$. Its invariant nonvanishing sections have exactly the invariant affine opens constructed
above, so this sheaf is ample. A high power embeds $Y$ into a projective bundle, proving
quasi-projectivity. This is an explicit norm calculation, not an appeal to exactness of
invariants.
$\square$

Over an algebraically closed field, $Y(k)$ is the set of $G(k)$-orbits when $G$ is a constant finite group. For a nonreduced finite group scheme, geometric points do not see the infinitesimal part of the action; the invariant scheme, rather than an orbit presheaf, remains the correct quotient.

The quotient stack $[X/G]$ maps to $Y$. The map is generally not representable: its fiber at an orbit retains the stabilizer. It becomes an isomorphism exactly when the action is a torsor, equivalently when $X\to Y$ is fppf and

$$
G\times X\xrightarrow{\sim}X\times_YX.
$$

### 7.3 Coarse moduli spaces

A map $\pi:\mathcal X\to M$ to an algebraic space is a **coarse moduli map** if:

1. for every algebraically closed field $k$, the map from isomorphism classes in $\mathcal X(k)$ to $M(k)$ is bijective;
2. every map from $\mathcal X$ to an algebraic space factors uniquely through $M$.

The second property is categorical and prevents a set-theoretic orbit space from masquerading as a coarse space. It also makes $M$ unique up to unique isomorphism.

For the finite quotient above, $[X/G]\to X/G$ is coarse. A map $[X/G]\to Z$ pulls back to a $G$-invariant map $X\to Z$. On invariant affine neighborhoods, the universal property of $A^G$ gives a unique map from the quotient; these local factorizations glue. Geometric orbit classification proves the first clause, with the group-scheme orbit relation interpreted fppf-locally.

A coarse map does not usually carry a universal object. If a universal family existed on $M$, pulling it back would make all objects over one coarse point canonically isomorphic and would force their automorphisms to act trivially on the universal object. The elliptic $j$-line demonstrates the failure.

### 7.4 Base change and tame descent

Formation of invariants is an equalizer, so it commutes with flat base change. It need not commute with arbitrary base change. If $G$ is finite locally free and **linearly reductive**, meaning that taking $G$-invariants on quasi-coherent modules is exact, the Reynolds projection makes invariants a direct summand and coarse quotient formation commutes with arbitrary base change. For a constant finite group whose order is invertible, averaging

$$
m\longmapsto\frac1{|G|}\sum_{g\in G}gm
$$

provides this projection.

This is the tame boundary. In residue characteristic dividing the stabilizer order, invariants need not be exact, coarse formation may fail to commute with a nonflat base change, and a vector bundle on the stack need not descend to the coarse space. Flat base change remains safe.

A finite locally free sheaf $\mathcal F$ on a tame finite quotient stack descends through $\pi$ precisely when every geometric stabilizer acts trivially on its fibers. Necessity is immediate. For sufficiency, work on an invariant affine chart $X=\operatorname{Spec}A$ and let $M$ be the corresponding equivariant finite projective module. Exact invariants make $M^G$ a finite projective $A^G$-module. The adjunction

$$
A\otimes_{A^G}M^G\longrightarrow M
$$

may be tested on geometric fibers. On the fiber over an orbit it is the induction map from the stabilizer invariants; triviality of the stabilizer action makes it an isomorphism. Its kernel and cokernel therefore have empty support, so the map is an isomorphism. These local modules glue. The same criterion holds for finitely presented quasi-coherent sheaves that are flat over the coarse base. Without trivial stabilizer action no sheaf downstairs can pull back to $\mathcal F$, because every pulled-back sheaf has trivial inertia action.

## 8. Generalized elliptic curves

### 8.1 The boundary object

A smooth elliptic curve cannot specialize within the category of elliptic curves when its discriminant tends to zero. The correct compact boundary is a polygon, not a cusp. A **Néron $n$-gon** over an algebraically closed field is a cycle of $n$ copies of $\mathbf P^1$, with $\infty$ on one copy glued to $0$ on the next. Its smooth locus is

$$
\mathbf G_m\times\mathbf Z/n\mathbf Z,
$$

and translation rotates components and multiplies the $\mathbf G_m$ coordinate.

A **generalized elliptic curve** over $S$ is a proper flat finitely presented curve $E\to S$ with a section $e$ in the smooth locus, together with a commutative group law on $E^{\mathrm{sm}}$ and an action

$$
E^{\mathrm{sm}}\times_SE\longrightarrow E
$$

extending translation, such that every geometric fiber is either a smooth connected genus-one curve or a Néron polygon, and translation by the smooth group acts transitively on the components of each singular fiber.

The action is part of the definition. A cycle of projective lines with a marked smooth point does not by itself determine the required group structure in families. The transitivity condition rules out irrelevant components invisible to the group.

### 8.2 The stack property and diagonal

Generalized elliptic curves form an fpqc stack in the polarized presentations used here. Retain a
compatible finite effective divisor in the smooth locus meeting every geometric component; as in
Book 10 §16.1, a positive multiple is relatively ample and supplies scheme effectivity. Then
descend the proper flat curve, the section, the smooth open, the group law, and the action. Group
identities are equalities of maps. Smoothness of the indicated open and the geometric polygon
condition are reflected after faithfully flat field extension. The transitive action on
components can be checked on geometric fibers. This proves effectivity; descent of isomorphisms
proves the prestack condition.

The diagonal is representable and separated. Given $E,E'$ over $T$, pass fppf-locally on $T$ and
choose finite effective Cartier divisors $D\subset E^{\mathrm{sm}}$ and
$D'\subset E'^{\mathrm{sm}}$ meeting every component of every fiber. Such divisors exist: after
splitting the finitely many components near a chosen geometric point, choose one smooth section on
each component and spread the disjoint sections after an etale neighborhood. Their associated line
bundles are relatively ample, because they have positive degree on every irreducible component.
Common high powers embed both curves. Book 8 then represents maps by their graphs. The open locus
of graphs which are isomorphisms, preserve the identity, and intertwine the two group actions
represents $\underline{\operatorname{Isom}}(E,E')$. This construction is independent of the
auxiliary divisors and descends by the uniqueness of the represented isomorphism sheaf.
The graph polynomial is fixed: with the product polarization its degree is the sum of the two
fixed divisor degrees and its arithmetic genus is one.

For a fixed bound on the number of geometric components, the diagonal is quasi-finite and of
finite presentation. On a smooth genus-one fiber an automorphism fixing the identity is finite in
number; on an $n$-gon it is determined by its automorphism of
$\mathbf G_m\times\mathbf Z/n\mathbf Z$ preserving the cyclic incidence, again a finite set. The
component bound supplies one finite-presentation graph locus. The isomorphism scheme is separated:
it is an open subscheme of a graph Hilbert scheme, and the equalizer of two maps to the separated
target is closed. This argument also works over nonreduced test schemes, where agreement on a
dense open alone would not suffice.

It is generally not proper. Over a valuation ring the same generic elliptic curve can have
distinct polygonal contractions, and a generic isomorphism between them need not extend. Thus the
unlevelled bounded stack does not have finite diagonal. An ample level divisor removes precisely
this ambiguity in Chapter 9; finiteness is asserted only there.

### 8.2A Contraction of bridge components

Throughout this subsection $E\to S$ is a generalized elliptic curve in the sense of Section 8.1
over a locally noetherian base, and

$$
D\subset E^{\mathrm{sm}}
$$

is a finite effective Cartier divisor which meets every geometric component of every fiber; such
divisors exist fppf-locally on the base by Section 8.2. Put $\mathcal L=\mathcal O_E(D)$. A
geometric irreducible component $Y$ of a singular fiber is **invisible** when $Y\cap D=\emptyset$.
Every component of a Neron polygon is a projective line meeting its two neighbors in one node each,
so an invisible component is a rational bridge component: it carries

$$
\deg\bigl(\mathcal L^m|_Y\bigr)=0\quad\text{for all }m\geq0,
$$

while a visible component carries degree at least $m$. A maximal **bridge chain** is a maximal
connected union of invisible components joined by nodes; its ends meet visible components.

**Lemma 8.2A.1 (constancy along bridge chains).** Let $s$ be a global section of
$\mathcal L^m$ on a geometric singular fiber. Then $s$ restricts to a constant function along each
bridge chain, and the constants attained by the space of all sections along one fixed chain form a
one-dimensional subspace.

**Proof.** Work after base change to an algebraically closed field, where every node is split. On
an invisible component $Y\simeq\mathbf P^1$ the bundle $\mathcal L^m|_Y$ has degree zero, hence is
trivial because the Picard group of $\mathbf P^1$ is generated by $\mathcal O(1)$; under any
trivialization $s|_Y$ becomes a regular function on $\mathbf P^1$, that is, a constant, since
$H^0(\mathbf P^1,\mathcal O)=k$. If two components are glued at a node $q$, choose trivializations
near $q$ on the total space; their ratio is an invertible function there, whose restriction to each
branch of the special fiber is a nonzero constant. The normalization description of functions near
a node (Book 9, Section 10.2, sequence (10.2)) identifies sections with tuples of functions on the
branches agreeing at the preimages up to these unit factors. Hence the constants on consecutive
invisible components of one chain are linked by fixed nonzero scalars, so the restrictions of all
global sections to the chain form a one-dimensional family: any two sections restrict to constant
systems proportional to one another. $\square$

**Lemma 8.2A.2 (fiberwise generation and separation).** There is an integer $m_0$, locally bounded
on $S$ in terms of $\deg D$ alone, such that for all $m\geq m_0$ and every geometric fiber:

1. the values of global sections of $\mathcal L^m$ realize every vector in
   $\mathcal L^m|_x$ for every point $x$ of the fiber;
2. for any two points or branches not joined through a bridge chain, some section takes the value
   $1$ at one and $0$ at the other.

**Proof.** By base change to geometric fibers it suffices to work over an algebraically closed
field, where the singular fibers are $n$-gons with components $Y_i\simeq\mathbf P^1$ and nodes
$q_1,\dots,q_n$, $n\leq$ the component bound of the divisor data. Write
$d_i=|D\cap Y_i|\geq0$, so $\deg(\mathcal L^m|_{Y_i})=md_i$. Global sections correspond to tuples
$(s_i)$, $s_i\in H^0(Y_i,\mathcal L^m|_{Y_i})$, agreeing at the nodes; by the same normalization
sequence (Book 9, Section 10.2) the agreement conditions at distinct nodes are independent linear
conditions, so, writing $d=\deg D=\sum_i d_i$,

$$
h^0(E,\mathcal L^m)=\sum_i(md_i+1)-n=md.
$$

Here $n$, the number of components of the polygon, equals its number of nodes, so the per-component
summands $+1$ cancel exactly against the $n$ node conditions; this also matches the Euler
characteristic $\chi(\mathcal L^m)=\deg(\mathcal L^m)+1-p_a=md+1-1=md$.

On a visible component $Y_i$ the sections vanishing at both its nodes form the kernel of two more
independent conditions, a space of dimension $md_i-1$, which for $md_i\geq 3$ separates points and
tangent directions of $\mathbf P^1$ away from the nodes, being the complete linear system of
degree $md_i-2\geq 1$. Extending such a section by zero across every node glues, because the value
$0$ agrees with $0$; this realizes arbitrary prescribed jets simultaneously on all visible
components. At a point $p$ lying on any component, choose values at the finitely many nodes of the
dual graph consistently — possible since each node condition involves only equality of two freely
choosable numbers once the componentwise polynomials have enough degrees of freedom, which
$md_i\geq 3$ supplies on visible components and constancy supplies along chains. Concretely: fix a
nonzero constant system along each bridge chain, choose matching nonzero values at the adjacent
nodes of visible components, and interpolate on each visible component by a polynomial of degree
$md_i$ avoiding prescribed zeros; dimension $md_i+1$ exceeds the at most three imposed linear
conditions as soon as $md_i\geq 3$. This proves (1), and (2) follows by imposing value $1$ or $0$
among those conditions at the chosen points or branches, taking $m_0$ any integer with
$m_0\cdot\min_{\text{visible}}d_i\geq 3$, which depends only on $d=\deg D$ once the component bound
is fixed. $\square$

**Theorem 8.2A.3 (contraction).** Let $E\to S$ be a generalized elliptic curve and
$D\subset E^{\mathrm{sm}}$ a finite effective Cartier divisor meeting every geometric component.
Then there exist an $S$-scheme $C\to S$, flat of finite presentation with stable genus-one nodal
fibers, and an $S$-morphism

$$
c=c_D\colon E\longrightarrow C
$$

such that, over every geometric point of $S$, $c$ maps each maximal bridge chain onto a single
ordinary double point, is an isomorphism from the complement of the bridge chains onto the
complement of those points, and satisfies $c_*\mathcal O_E=\mathcal O_C$. Moreover $c$ is unique
up to unique isomorphism over $S$, and formation of $(C,c)$ commutes with arbitrary base change.

**Proof.** Fix $m\geq m_0$ as in Lemma 8.2A.2. On each geometric fiber the Euler characteristic
$\chi(\mathcal L^m)=md+1-1=md$ and $h^0=md$ are constant, and $h^1=0$ by Lemma 8.2A.2, which also
shows global generation. Since $E\to S$ is flat and proper, Book 15
Section 5.4 makes $V_m=f_*\mathcal L^m$ locally free of rank $md$ with formation commuting with
arbitrary base change. Lemmas 8.2A.1–8.2A.2 show that the evaluation of $V_m$ is globally
generated on every fiber and defines a morphism

$$
\varphi_m\colon E\longrightarrow\mathbf P(V_m)
$$

over $S$; being fiberwise given by a base-point-free linear system, it exists globally by Book 8
Sections 2.3 and 5.2. Let $C$ be the scheme-theoretic image of $\varphi_m$, so that
$\varphi_m=p\circ g$ is Stein-factored through $C\to S$ with $p_*\mathcal O_E=\mathcal O_C$ by
Book 9, Theorem 9.3, applied relative to $S$.

Fiberwise statements now descend. Over a geometric point of $S$: Lemma 8.2A.1 shows that $p$
collapses each bridge chain to one point; Lemma 8.2A.2 (2) shows $p$ separates all other points and
branches and is an immersion off the chains, being given on each visible component by the
subsystem of sections of degree $md_i\geq 3$ vanishing at its two nodes, which separates points. The local structure at an image point of a chain is
read off from the normalization: the preimage consists of the two end branch points, functions on
the image are functions on the union of the two end components constant along the collapsed chain,
and the conductor description of Book 9 Sections 4.2 and 10.2 identifies the completed local ring
with the fiber product of the two discrete valuation rings over their common residue field,

$$
\widehat{\mathcal O}_{C_y,q}\;\simeq\;\kappa(y)[[u]]\times_{\kappa(y)}\kappa(y)[[v]]
\;\simeq\;\kappa(y)[[u,v]]/(uv),
$$

an ordinary double point. Hence the geometric fibers of $C\to S$ are connected reduced nodal
curves of arithmetic genus one in which every smooth rational component meets the rest in at least
three special points — the components meeting $D$ keep their incident nodes plus a point of
$D$ — that is, stable genus-one curves. Their Hilbert polynomial under the embedding by
$\mathcal L^m$ is fixed by constancy of $h^0$ and of the degree, namely the polynomial with value
$md$ in degree zero shifted by the standard linear correction, so
flatness of $C\to S$ follows from Book 8 Section 8.2, constancy of the Hilbert polynomial forcing
flatness for a closed subscheme of the fixed projective bundle $\mathbf P(V_m)$.

Uniqueness: let $c'\colon E\to C'$ have the same three properties. Then $c'_*\mathcal O_E=
\mathcal O_{C'}$ forces $c'$ to factor uniquely through $p$ and conversely, since both collapse
exactly the same equivalence relation of being joined through a bridge chain; the induced maps
$C\leftrightarrows C'$ are mutually inverse over $S$ because they are isomorphisms on dense opens
and both targets are proper and reduced. Base change compatibility follows from uniqueness: for
any $T\to S$, the pullback pair $(E_T\to C\times_ST)$ again satisfies all three hypotheses over
$T$, flatness and stability of fibers being preserved under base change, so the uniqueness just
proved, applied over $T$, identifies $C\times_ST$ canonically with any contraction of $E_T$
constructed there, in particular with the reconstruction using the pulled-back locally free
pushforward. $\square$

**Lemma 8.2A.4 (thickness additivity).** Suppose moreover that $S=\operatorname{Spec}\Lambda$ for
a complete discrete valuation ring $\Lambda$ with uniformizer $\pi$, and that a node $q$ of the
special fiber has smoothing parameter $a=u\pi^{n}$ as in Book 9, Theorem 10.5. Contracting a
chain of $r$ consecutive edges of thicknesses $n_1,\dots,n_r$ through $q$'s place produces a node
with smoothing parameter of valuation exactly

$$
n_{\mathrm{new}}=n_1+\cdots+n_r. \tag{8.1}
$$

**Proof.** It suffices by induction to contract a single edge, i.e., one intervening rational
component $Y_0\simeq\mathbf P^1$ between end branches with parameters $x$ (left branch) and $w$
(right branch). Choose coordinates so that near the left node the completed total space is
$\Lambda[[x,t]]/(xt-\pi^{n_1})$ with $t$ a parameter on $Y_0$ at that node, and near the right
node $\Lambda[[u,w]]/(uw-\pi^{n_2})$ with $u$ the inverse-parameter on $Y_0$ there; rescaling $w$
absorbs the transition unit of the line-bundle gluing across $Y_0$, which restricts to a unit
times $u=t^{-1}$. On the overlap of the two charts of the total space along $Y_0$ we have
$t u=1+\pi h$. Eliminating $t$ and $u$: from $xt=\pi^{n_1}$ and $uw=\pi^{n_2}$,

$$
(xt)(uw)=\pi^{n_1+n_2}
\quad\Longrightarrow\quad
x w\,(tu)=\pi^{n_1+n_2},
$$

and substituting $tu=1+\pi h$, whose inverse lies in the completed ring, gives
$xw=\pi^{n_1+n_2}(1+\pi h)^{-1}$, a relation equivalent after a unit rescaling of $w$ to
$xw=\pi^{n_1+n_2}$. The contracted curve's completed local ring at the new node is precisely the
subalgebra of pairs constant along the eliminated component, which this computation exhibits as
$\Lambda[[x,w]]/(xw-\pi^{n_1+n_2})$; by Book 9, Theorem 10.5, the ideal cut out by the non-smooth
locus is intrinsic, so the valuation of the new smoothing parameter is $n_1+n_2$. Repeating the
single-edge contraction sums the thicknesses one at a time, proving (8.1); starting from a chain
of $r$ unit edges gives thickness $r$. $\square$

### 8.2B Decontractions and smoothing-parameter roots

Decontraction is the passage opposite to contraction: given a compactified object, insert the
components that an ample level divisor will need. On the Tate chart this insertion is carried by a
root of the smoothing parameter, and the finiteness of that operation is what Chapter 9 consumes.

**Lemma 8.2B.1 (root adjunction is finite locally free).** Let $B$ be any scheme, $a\in\Gamma(B,
\mathcal O_B)$ any section, and $r\geq1$. Then

$$
B'=\operatorname{Spec}_B\bigl(\mathcal O_B[t]/(t^r-a)\bigr)\longrightarrow B
$$

is finite locally free of rank $r$ with basis $1,t,\dots,t^{r-1}$, hence faithfully flat and
surjective, and its formation commutes with arbitrary base change.

**Proof.** The polynomial $t^r-a$ is monic, so the quotient is free over $\mathcal O_B$ on the
images of $1,t,\dots,t^{r-1}$: division with remainder by a monic polynomial leaves a unique
representative of degree less than $r$. Freeness gives finite presentation, flatness, and local
constancy of the rank; positive rank gives surjectivity. Pullbacks preserve monicity. $\square$

**Proposition 8.2B.2 (Tate chart decontraction).** Let $\Lambda$ be a complete discrete valuation
ring, let $E_q$ be a generalized elliptic curve over $\Lambda[[q]]$ whose generic fiber is a Tate
curve and whose special fiber is a $1$-gon with single node of smoothing parameter $q$, and fix
$e\geq1$. Put $B'=\operatorname{Spec}\Lambda[[s]]$, mapping to $\operatorname{Spec}\Lambda[[q]]$ by
$q\mapsto s^{e}$. Then:

1. the pullback $E_q\times_{\Lambda[[q]]}B'$ has a single node whose smoothing parameter is
   $s^{e}$, of thickness $e$;
2. the standard $e$-gon model $E'_e$ over $B'$ — the cycle of $e$ copies of $\mathbf P^1$ glued by
   unit-thickness nodes each carrying smoothing parameter $s$, with translation action rotating the
   cycle — is a generalized elliptic curve whose contraction $c_{D}(E'_e)$ for any divisor $D$ of
   degree one on each component is exactly $E_q\times B'$;
3. any generalized elliptic curve $G$ over $B'$ together with an isomorphism
   $c_D(G)\simeq E_q\times B'$ which is an isomorphism over the generic fiber is canonically
   isomorphic to $(E'_e,B')$ compatibly with its contraction.

**Proof.** (1) is immediate: base change preserves the completed local equation, giving
$s^{e}$ in place of $q$, and the thickness is the valuation $v(s^{e})=e$ by Book 9, Theorem 10.5.
For (2): Lemma 8.2A.4 applied to the chain of all $e$ components, contracted edge by edge, adds
thicknesses $1+\cdots+1=e$ to produce a one-gon whose smoothing parameter has valuation $e$,
namely $s^{e}$; the identity section, group law, and transitive rotation action descend along the
contraction because they are defined on the smooth loci, which contract compatibly. For (3):
contracting $G$ collapses its invisible components; since the target is a $1$-gon over $B'$, the
dual graph of $G$ contracts to the segment with self-node, so $G$ is a cycle of $e$ projective
lines. Each node of $G$ has some thickness $n_j\geq1$, and Lemma 8.2A.4 gives
$n_1+\cdots+n_e=v(s^{e})=e$, whence all $n_j=1$. The contraction isomorphism identifies the
normalizations away from the contracted locus, so $G$ is obtained from $E_q\times B'$ by cutting
the node into a cycle and redistributing the smoothing parameter as the product of the unit node
parameters; the resulting gluing data are unique up to the rescaling absorbed above, which is
exactly an automorphism of the cycle compatible with translation. Hence $G\simeq E'_e$ over $B'$,
canonically once the contraction identification is fixed. $\square$

**Theorem 8.2B.3 (finite decontraction cover).** Fix $m\geq1$. Let $E\to S$ be a generalized
elliptic curve whose singular geometric fibers have at most $m$ components. Consider the stack
$\mathcal D_m\to S$ of data $(S'\xrightarrow{f}S,\ E'\to S',\ \alpha)$ where $f$ is finite locally
free, $E'$ is a generalized elliptic curve with at most $m$ components on every geometric fiber,
and

$$
\alpha\colon c_D(E')\stackrel{\sim}{\longrightarrow}E\times_S S'
$$

is an isomorphism of generalized elliptic curves for some divisor $D$ meeting every component.
Then $\mathcal D_m$ is representable by an algebraic stack admitting a finite surjective
representable cover: locally on $S$, the objects of $\mathcal D_m$ are obtained from finitely many
root adjunctions as in Lemma 8.2B.1 on the smoothing parameters of the nodes, composed with the
finite etale choices of torsion generators, and the whole cover descends by Book 10.

**Proof.** Cover $S$ fppf-locally so that every polygon splits and a divisor $D$ meeting every
component exists (Section 8.2). On such a chart the combinatorial type of a decontraction is
bounded: inserting $j\leq m$ components distributes the smoothing parameters among at most $m$
unit nodes, and by Proposition 8.2B.2 each distribution is realized by adjoining roots of the
finitely many node parameters, one root adjunction per inserted edge, each finite locally free of
known rank by Lemma 8.2B.1; compositions of finite locally free morphisms are finite locally free.
The residual choices — generators of the cyclic component group realizing a given level orbit —
are finite etale over the chart, being torsion subschemes of the smooth group, by Book 28
Section 5 and Book 35 Section 4.3. Finitely many types, each contributing a finite surjective
chart, glue equivariantly under the splitting cover; the cocycle computations are equations
between contractions and descend by Book 10 Chapters 5–16, already invoked for the stack property
in Section 8.2. Surjectivity holds because every polygon admits a splitting and a root
adjunction recovering each admissible distribution. $\square$

### 8.3 Weierstrass charts and contraction

The line bundle $\mathcal O_E(3e)$ embeds a smooth elliptic curve as a cubic. For a polygon, a positive divisor must meet every component, so one first contracts the components disjoint from the chosen degree-three divisor; the contraction exists, is unique, and commutes with base change by Theorem 8.2A.3, and its singular fibers are one-gons by Lemma 8.2A.4. The result is a stable cubic with a smooth marked identity and fibers either smooth or nodal.

Locally on the base, a framed stable cubic has a Weierstrass equation

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6.
$$

Admissible coordinate changes are

$$
x=u^2x'+r,\qquad
y=u^3y'+u^2sx'+t,\qquad u\in\mathbf G_m.
$$

Let $W$ be the open in the affine coefficient space where every geometric cubic is smooth or nodal and the marked point at infinity is smooth. Let $G_W$ be the smooth affine group of these coordinate changes. Then the stack of Weierstrass cubics is $[W/G_W]$. The atlas $W\to[W/G_W]$ is smooth. This quotient chart describes the smooth and one-gon fibers. It is not asserted to remember an arbitrary polygon before the additional component data below are supplied.

An arbitrary polygon is not recovered from its contraction alone: contraction forgets how many components were inserted. Level structure or an explicit component marking supplies the missing finite data. This is why one cannot prove algebraicity of every boundary problem merely by writing one Weierstrass equation.

### 8.4 Algebraicity and bounded boundary

Fix $m\geq1$ and let $\mathcal E\!ll_{\leq m}$ be the full bounded substack in which singular geometric fibers have at most $m$ components. We now construct its atlas rather than treating the forgotten component data as automatic. Let $\mathcal V_m$ classify a generalized elliptic curve together with a relative effective Cartier divisor

$$
D\subset E^{\mathrm{sm}}
$$

of degree $m$ which meets every geometric component. Repetitions are permitted, so every polygon
with at most $m$ components admits such a divisor after an etale cover. The forgetful map
$\mathcal V_m\to\mathcal E\!ll_{\leq m}$ is represented by the open, component-meeting locus in
the relative degree-$m$ Hilbert scheme of the smooth locus. The divisor-chart calculation of
Book 8 shows that this morphism is smooth, and the preceding existence argument shows that it is
surjective.

The line bundle $\mathcal O_E(D)$ has positive degree on every component and is therefore
relatively ample. A fixed high power, depending only on $m$, embeds every such genus-one curve
with at most $m$ components and has one fixed Hilbert polynomial. Book 8 gives the corresponding
Hilbert parameter scheme. The marked identity and divisor are further Hilbert or incidence data.
The open conditions say that the curve is flat, nodal with the stated smooth locus, and that $D$
meets every component. The group law on the smooth locus and its action on the proper curve are
represented by taking graph closures in the fixed projective compactification and then imposing
that the projection over the smooth-domain open is an isomorphism. The component bound leaves
only finitely many graph polynomials. The identity, inverse, associativity, commutativity, and
transitivity conditions are equalities or open fiber conditions. They therefore cut out a
locally closed parameter scheme. Choosing a basis of the high-power section bundle gives a
general-linear frame torsor, so Section 6.5 supplies a smooth scheme atlas of $\mathcal V_m$.
Composing with the smooth surjection above gives a smooth atlas of
$\mathcal E\!ll_{\leq m}$.

Together with the diagonal argument of Section 8.2, this proves that
$\mathcal E\!ll_{\leq m}$ is an algebraic stack of finite presentation with separated
quasi-finite diagonal. The union over $m$ is a locally algebraic stack, generally not quasi-compact. Modular
level conditions below impose their own finite component bounds, so every compactified modular
stack used later lies in one algebraic finite-type piece.

This conclusion is deliberately narrower than a claim that every genus-one degeneration is allowed. Cuspidal cubics, nonreduced fibers, and cycles with tails are excluded: their smooth loci and deformation behavior do not satisfy the generalized elliptic axioms.

## 9. Modular level structures

### 9.1 Drinfeld structures and ampleness

At primes dividing $N$, a list of $N$ distinct torsion sections is the wrong definition of level. Sections can collide in the special fiber while their sum still defines the correct finite flat subgroup divisor. Let $G\subset E^{\mathrm{sm}}$ be a finite locally free commutative subgroup scheme of rank $|H|$ and let $H$ be a constant finite abelian group. A **Drinfeld $H$-structure** on $G$ is a homomorphism $\alpha:H\to G(T)$ for which

$$
\sum_{h\in H}[\alpha(h)]
$$

is the Cartier divisor $G\subset E^{\mathrm{sm}}$ in the ambient smooth curve. Thus the definition
includes both the homomorphism equations and equality with the entire finite locally free subgroup,
not merely equality of supports. It is stable under base change and meaningful in bad
characteristic.

On a generalized elliptic curve a level divisor must also be **ample**: it must meet every irreducible component of every geometric fiber. On a polygon, a divisor supported on the identity component is finite flat but cannot control the other components and gives no projective embedding of the whole curve. The ampleness clause is what makes level compactification finite and prevents invisible components.

When $N$ is invertible, the torsion is etale and a Drinfeld basis is an ordinary basis on geometric fibers. Thus the integral definition specializes to the familiar one without having been defined by that generic behavior.

### 9.2 Full, point, and cyclic level

A full $\Gamma(N)$-structure is a homomorphism, written as a pair $(P,Q)$,

$$
(\mathbf Z/N\mathbf Z)^2\longrightarrow E^{\mathrm{sm}}[N]
$$

for which the sum of the $N^2$ image sections equals the Cartier divisor
$E^{\mathrm{sm}}[N]$ and is ample on $E$. In particular, the equality itself forces
$E^{\mathrm{sm}}[N]$ to have rank $N^2$ on this locus. If a primitive $N$th root and a
symplectic convention are fixed, one may additionally require the Weil pairing of $P,Q$ to equal
that root. Over the elliptic locus this is the perfect alternating pairing
$e_N:E[N]\times E[N]\to\mu_N$ of Book 34 §14.5, equivalently the Weil pairing of Book 35 §§7.1–7.3
composed with the canonical principal polarization. Across a polygonal fiber neither book applies,
because a Neron polygon is not an abelian scheme; the pairing meant there is the one constructed
on all of $E^{\mathrm{sm}}[N]$ in Section 9.3, which is perfect and alternating over the whole
compactified problem and restricts to $e_N$ on the elliptic locus. Nothing in the present section
uses more about it than that it exists and is preserved by isomorphisms.

A $\Gamma_1(N)$-structure is a Drinfeld homomorphism $\mathbf Z/N\mathbf Z\to E^{\mathrm{sm}}[N]$, written $1\mapsto P$, with ample divisor $\sum_a[aP]$. A $\Gamma_0(N)$-structure is a finite locally free cyclic subgroup $C\subset E^{\mathrm{sm}}$ of rank $N$, locally generated by a Drinfeld point, whose Cartier subgroup divisor $C\subset E$ is ample.

The local-generation phrase for $\Gamma_0(N)$ is necessary. A finite flat group scheme may have no global generator. Requiring one would define a framed $\Gamma_1$-type cover rather than the cyclic subgroup problem.

These definitions are stable under pullback and have effective descent. The divisor equality, cyclicity after an fppf cover, and ampleness are all fppf local. To see representability of the forgetful map, work on the divisor-framed atlas of Chapter 8. Each possible section is a point of a finite torsion scheme; homomorphism, divisor-equality, and subgroup conditions are closed, while ampleness is open. Hence the level functor is represented by a locally closed subscheme of a finite scheme over that atlas. Descent gives a representable, separated, quasi-finite morphism of finite presentation. It need not be finite: a generic torsion divisor can specialize into too few components of a fixed polygon, so ampleness can fail in the special fiber. Proper compactified level maps require the decontractions used in Section 9.5. Over $\mathbf Z[1/N]$ the torsion is etale, so the forgetful map is etale over the smooth elliptic locus.

### 9.3 Theta groups and pairings across the boundary

Two things have been used above and will be used again in the next section, and neither is
supplied by any earlier book. The first is a Weil pairing on $E^{\mathrm{sm}}[N]$ that is defined,
alternating, and perfect also when the geometric fiber is a polygon. The second is a supply of
coordinates on a levelled generalized elliptic curve, canonical enough to embed the whole level
problem in one projective space, and again valid across the boundary. Book 34 builds the Weil
pairing out of the Poincare bundle of an abelian scheme, and Book 35 Chapter 9A puts the theta
group of an ample bundle on an abelian scheme into standard form. A Neron polygon is not an
abelian scheme: it is singular, its smooth locus is not proper, and the identity component of that
smooth locus is a torus and not an abelian variety. Neither theory applies to it. This section
builds both objects directly.

The first task is to choose the right line bundle, because the naive choice fails for a reason
worth seeing. Take the level divisor $D=E^{\mathrm{sm}}[N]$ itself, of degree $N^2$. On a smooth
fiber the associated kernel $K(\mathcal O_E(D))$ is $E[N^2]$, of order $N^4$. On an $N$-gon it is,
by the same method as the computation carried out below, the group
$\mu_{N^2}\times\mathbf Z/N\mathbf Z$, of order $N^3$. The kernel is not finite of constant order across the boundary, so the theta group of
$\mathcal O_E(D)$ is not a central extension of a finite etale group scheme, and no normal form for
it can exist. The missing points are visible in the degeneration: of the $N^4$ points of $E[N^2]$
only $N^3$ remain in the smooth locus of the limit, the rest escaping into the components that the
degeneration inserts. Restricting the theta group of $\mathcal O_E(D)$ to the subgroup
$E^{\mathrm{sm}}[N]$ does not repair this, because $E[N]=N\cdot E[N^2]$ is isotropic for the
commutator of a bundle of degree $N^2$ and the restricted extension is commutative.

What does work is a bundle of degree exactly $N$. On a smooth fiber the kernel is then $E[N]$
itself, of order $N^2$; and on an $N$-gon a bundle of degree one on every component has, again by
the computation below, kernel exactly $E^{\mathrm{sm}}[N]$, of the same order $N^2$. So the two
kernels agree, the extension is a central extension of a finite etale group scheme of order $N^2$
over the whole problem, and the machinery of Book 35 Chapter 9A that concerns such extensions
rather than abelian schemes becomes available. Producing such a bundle canonically is the role of
the following covering of the moduli problem by open pieces.

Throughout this section $N\geq1$ is invertible on the base, $E\to S$ is a generalized elliptic
curve, and $\alpha:(\mathbf Z/N\mathbf Z)^2\to E^{\mathrm{sm}}[N]$ is a $\Gamma(N)$-structure whose
divisor is ample.

**Boundary lemma.** Every singular geometric fiber of $E$ is a Neron $N$-gon; $\alpha$ is an
isomorphism onto $E^{\mathrm{sm}}[N]$, which is therefore finite etale of order $N^2$ over $S$ and
constant; and on a polygonal geometric fiber the canonical sequence of the smooth group restricts
to an exact sequence

$$
1\longrightarrow\mu_N\longrightarrow E^{\mathrm{sm}}[N]
\longrightarrow\mathbf Z/N\mathbf Z\longrightarrow0
$$

whose first term is the $N$-torsion of the identity component and whose last term is the group of
components.

**Proof.** Let the fiber be an $n$-gon, so that its smooth group is
$\mathbf G_m\times\mathbf Z/n\mathbf Z$. Since $N$ is invertible, the $N$-torsion of this group is
$\mu_N\times(\mathbf Z/n\mathbf Z)[N]$, etale of order $N\gcd(N,n)$, and its length as a Cartier
divisor equals that order. The Drinfeld equality says that this divisor is the sum of the $N^2$
sections $\alpha(h)$, of degree $N^2$; hence $\gcd(N,n)=N$, that is $N\mid n$. Ampleness says that
the divisor meets every component, so the composite
$E^{\mathrm{sm}}[N]\to\mathbf Z/n\mathbf Z$ is surjective; its image is
$(\mathbf Z/n\mathbf Z)[N]=\mathbf Z/\gcd(N,n)\mathbf Z$, so $n\mid N$. Thus $n=N$. Multiplication
by $N$ on the smooth commutative group scheme $E^{\mathrm{sm}}$ is etale, its differential at the
identity being multiplication by $N$ on the Lie algebra and translations acting transitively on
each geometric fiber; so $E^{\mathrm{sm}}[N]$ is etale over $S$, of order $N^2$ in every fiber by
the two cases just treated. A reduced divisor cannot be a sum of $N^2$ sections with a repetition,
so the sections $\alpha(h)$ are pairwise disjoint and exhaust $E^{\mathrm{sm}}[N]$; hence $\alpha$
is an isomorphism of $S$-group schemes and $E^{\mathrm{sm}}[N]$ is finite etale and constant of
order $N^2$. The
displayed sequence is the $N$-torsion of $1\to\mathbf G_m\to E^{\mathrm{sm}}\to\pi_0\to0$, exact
on the right because $\mathbf G_m$ is $N$-divisible over an algebraically closed field of
residue characteristic prime to $N$. $\square$

Next we record the elementary geometry of line bundles on a polygon, computed through the
normalization. Let $C$ be a Neron $n$-gon over an algebraically closed field $k$, with components
$C_j\simeq\mathbf P^1$ indexed by $j\in\mathbf Z/n\mathbf Z$, coordinate $u_j$, and $u_j=\infty$
glued to $u_{j+1}=0$. A point of $C^{\mathrm{sm}}$ is a pair $(t,j)$ with $t\in k^\times$ the
coordinate on $C_j$, and the group law is $(t,j)(t',j')=(tt',j+j')$.

**Polygon Picard lemma.** A line bundle on $C$ is determined by its multidegree $(d_j)$ together
with one further invariant in $k^\times$, and a divisor $\sum_kn_k[(t_k,j_k)]$ supported on
$C^{\mathrm{sm}}$ and of multidegree zero is principal if and only if $\prod_kt_k^{n_k}=1$.

**Proof.** Give a line bundle by its restrictions $\mathcal O(d_j)$ to the components together with
identifications of the fibers at the $n$ nodes; rescaling the $j$-th restriction by $c_j$ multiplies
one identification by $c_j$ and the adjacent one by $c_j^{-1}$, so the product of the $n$ gluing
scalars is the only invariant that survives, and it can be arbitrary. For the criterion, a rational
function on $C$ is a family $f_j$ of rational functions on the components, with no zero or pole at a
node and with $f_j(\infty)=f_{j+1}(0)$. If $\operatorname{div}(f_j)=\sum_kn_{jk}[t_k]$ with
$\sum_kn_{jk}=0$, then $f_j=c_j\prod_k(u_j-t_k)^{n_{jk}}$, so $f_j(\infty)=c_j$ and
$f_j(0)=c_j\prod_kt_k^{n_{jk}}$, the signs cancelling because the exponents sum to zero. The
matching conditions read $c_j=c_{j+1}\prod_kt_k^{n_{j+1,k}}$; multiplying them over $j$ gives
$\prod_{j,k}t_k^{n_{jk}}=1$, and conversely that identity allows the $c_j$ to be solved for
recursively around the cycle. $\square$

Now fix a cyclic subgroup $\Lambda\subset(\mathbf Z/N\mathbf Z)^2$ of order $N$; there are finitely many
such, and the list does not vary over $S$. Let $\mathcal M_\Lambda$ be the locus of the level problem on
which the divisor $\alpha(\Lambda)$, a finite locally free subgroup of $E^{\mathrm{sm}}$ of rank $N$, is
ample on $E$. Ampleness is an open condition, so $\mathcal M_\Lambda$ is an open substack.

**Ample generator cover.** The $\mathcal M_\Lambda$ cover the level problem. On $\mathcal M_\Lambda$ the line
bundle $\mathcal L_\Lambda=\mathcal O_E(\alpha(\Lambda))$ has degree $N$ on every geometric fiber, degree one on
every component of every polygonal fiber; $\pi_*\mathcal L_\Lambda$ is locally free of rank $N$ and its
formation commutes with arbitrary base change; and for $N\geq3$ the bundle $\mathcal L_\Lambda$ is
relatively very ample.

**Proof.** For the covering statement, argue on a geometric fiber. If the fiber is smooth, every
$\alpha(\Lambda)$ is an effective divisor of degree $N>0$ on an irreducible curve, hence ample. If it is
an $N$-gon, choose an element $g\in E^{\mathrm{sm}}[N]$ whose component index generates
$\mathbf Z/N\mathbf Z$; then $g$ has order $N$, the subgroup it generates has order $N$ and
surjects onto the component group, hence meets every component, and $\Lambda=\alpha^{-1}\langle g\rangle$
does the job. Ampleness holds on a neighbourhood of the chosen point of $S$, so the open substacks
$\mathcal M_\Lambda$ cover.

On a polygonal fiber, $\alpha(\Lambda)$ has $N$ points, surjects onto the group of $N$ components, and
has trivial kernel there by comparison of orders; so it meets each component exactly once and
$\mathcal L_\Lambda$ has multidegree $(1,\ldots,1)$. The Euler characteristic of a degree-$N$ bundle on a
curve of arithmetic genus one is $N$, and $h^1$ vanishes: on a smooth fiber because the degree is
positive, and on a polygon because $h^0$ is already $N$, as the following description shows. A
section of $\mathcal O_C(D)$ with $D=\sum_j[(a_j,j)]$ is a family
$f_j=\gamma_j+\beta_j/(u_j-a_j)$ subject to the matching conditions, which determine
$\beta_{j+1}=a_{j+1}(\gamma_{j+1}-\gamma_j)$ and leave the $\gamma_j$ free; so $h^0=N$. Constancy
of $h^0$ and of $h^1$ in the fibers makes $\pi_*\mathcal L_\Lambda$ locally free of rank $N$ with base
change, by the coherent base-change theorem of Book 15.

For very ampleness with $N\geq3$: on a smooth fiber a degree-$N$ bundle with $N\geq3$ is very
ample by Riemann--Roch on a relative curve, Book 9. On an $N$-gon, the displayed description shows
that the restriction of the linear system to $C_j$ consists of all functions
$A+B/(u_j-a_j)$, since $\beta_j=a_j(\gamma_j-\gamma_{j-1})$ and $\gamma_{j-1},\gamma_j$ are
independent coordinates when $N\geq2$; so each component is mapped isomorphically onto a line. In
the basis dual to the coordinates $\gamma_j$, the point $u_j=\infty$ goes to the $j$-th coordinate
point and the point $u_j=0$ to the $(j-1)$-st, so the image of $C_j$ is the line joining those two
coordinate points, and the two nodes of $C_j$ go to its two ends. For $N\geq3$ the $N$ lines so
obtained are distinct, two of them meet exactly in the coordinate point they share when their
index sets overlap and are disjoint otherwise, and a shared point is precisely the image of the
node joining the corresponding components. Hence the map is injective, is an immersion on each
component, and separates the two branches at each node: it is a closed immersion, realizing $C$ as
an $N$-gon of lines in $\mathbf P^{N-1}$. $\square$

We can now build the theta group. Since $E^{\mathrm{sm}}$ acts on $E$, translation $t_x$ by a
section $x$ of $E^{\mathrm{sm}}$ is an automorphism of $E$ over $S$, and the definition of Book 35
§9.2 can be copied verbatim: let $\mathcal G(\mathcal L_\Lambda)$ be the fppf sheaf whose $T$-points are
the pairs $(x,\varphi)$ with $x\in E^{\mathrm{sm}}[N](T)$ and
$\varphi:t_x^*\mathcal L_{\Lambda,T}\xrightarrow{\sim}\mathcal L_{\Lambda,T}$, multiplied by
$(x,\varphi)(y,\psi)=(x+y,\varphi\circ t_x^*\psi)$.

**Boundary theta theorem.** On $\mathcal M_\Lambda$ the sheaf $\mathcal G(\mathcal L_\Lambda)$ is a central
extension

$$
1\longrightarrow\mathbf G_m\longrightarrow\mathcal G(\mathcal L_\Lambda)
\longrightarrow E^{\mathrm{sm}}[N]\longrightarrow1,
$$

formed compatibly with base change. Its commutator
$c_{\mathcal L_\Lambda}:E^{\mathrm{sm}}[N]\times E^{\mathrm{sm}}[N]\to\mathbf G_m$ takes values in
$\mu_N$, is alternating and perfect, and does not depend on $\Lambda$. On a polygonal geometric fiber it
is given, in the notation of the boundary lemma, by

$$
c\bigl((\zeta,i),(\xi,l)\bigr)=\xi^{\,i}\zeta^{-l},
$$

and on a smooth geometric fiber it is the elliptic Weil pairing $e_N$ of Book 34 §14.5, up to the
inversion of one argument. Consequently the pairings on the various $\mathcal M_\Lambda$ glue to one
perfect alternating pairing on $E^{\mathrm{sm}}[N]$ over the whole compactified level problem,
restricting to $e_N$ over the elliptic locus.

**Proof strategy.** Everything except the two fiber formulas is formal: an extension by
$\mathbf G_m$ because the automorphisms of a line bundle on a proper family with geometrically
connected reduced fibers are the units of the base, and translation-invariance of
$\mathcal L_\Lambda$ because a line bundle trivial on all fibers and of rank-one pushforward is pulled
back from the base. The commutator can then be computed inside the action on sections, where the
polygon becomes an explicit calculation with rational functions and the smooth fiber is handled by
the identification already available in Book 35.

**Proof.** Since $E\to S$ is proper and flat with geometrically connected and reduced fibers,
$\pi_*\mathcal O_E=\mathcal O_S$ universally, so the automorphisms of $\mathcal L_{\Lambda,T}$ are exactly
$\mathbf G_m(T)$; this is the kernel of the projection, and it is central because an automorphism
of the bundle commutes with every $\varphi$. For surjectivity, let $x$ be a section of
$E^{\mathrm{sm}}[N]$ and put $M_x=t_x^*\mathcal L_\Lambda\otimes\mathcal L_\Lambda^{-1}$. On each geometric
fiber $M_x$ is trivial: on a smooth fiber because $\lambda_{\mathcal L_\Lambda}=\lambda_0\circ[N]$, the
homomorphism attached to a line bundle depending only on the fiberwise degree and vanishing on
algebraically trivial bundles (Book 35 §§2.5, 8.1), so that its kernel is $E[N]$; and on an
$N$-gon by the Picard lemma, since with $D=\sum_j[(a_j,j)]$ of multidegree one and
$x=(\zeta,i)$ the divisor $t_{-x}D-D$ has multidegree zero and invariant

$$
\prod_j\frac{a_{j+i}\zeta^{-1}}{a_j}=\zeta^{-N}=1 .
$$

A line bundle on $E$ trivial on every geometric fiber has invertible pushforward whose formation
commutes with base change, again by Book 15, and the evaluation
$\pi^*\pi_*M_x\to M_x$ is an isomorphism because it is one on fibers; so $M_x$ is pulled back from
$S$ and, Zariski-locally on $S$, is trivial. Hence the projection is surjective as a sheaf map and
the displayed sequence is a central extension. Base-change compatibility is clear from the
description of the points.

The extension acts on $\pi_*\mathcal L_\Lambda$ by $(x,\varphi)\cdot s=\varphi(t_x^*s)$; this is a group
action and the centre acts by scalars, by exactly the computation of Book 35 Theorem 9A.10(2),
which uses only that translation is an automorphism of the family and that the pushforward commutes
with base change, both verified above. Since $\mathbf G_m$ embeds in the automorphisms of
$\pi_*\mathcal L_\Lambda$, the commutator of two lifts may be computed in this action.

Do so on a polygonal fiber. Write $\mathcal L_\Lambda=\mathcal O_C(D)$ with
$D=\sum_j[(a_j,j)]$ of multidegree one, identify sections with rational functions $f$ satisfying
$\operatorname{div}(f)+D\geq0$, and choose for each $x\in C^{\mathrm{sm}}[N]$ a rational function
$h_x$ with $\operatorname{div}(h_x)=t_{-x}D-D$, which exists by the computation just made.
Multiplication by $h_x$ is an isomorphism $t_x^*\mathcal O(D)\to\mathcal O(D)$, so the corresponding
element of the theta group acts on sections by $U_xf=h_x\cdot(f\circ t_x)$. Since
$U_xU_y=\bigl(h_x\,(h_y\circ t_x)/h_{x+y}\bigr)U_{x+y}$ and the same with $x,y$ interchanged, the
commutator is the constant function

$$
c_{\mathcal L_\Lambda}(x,y)=\frac{h_x\,(h_y\circ t_x)}{h_y\,(h_x\circ t_y)} .
$$

For $x=(\zeta,i)$ the divisor condition gives
$h_{x,j}(u)=\kappa_j\,(u-a_{j+i}\zeta^{-1})/(u-a_j)$ on the component $C_j$, and the condition that
$h_x$ take equal values on the two branches at each node reads
$\kappa_j=\kappa_{j+1}a_{j+1+i}/(a_{j+1}\zeta)$. Extend $a$ periodically to all integers, lift the
indices to non-negative integers, and write $F(j)=\prod_{m=1}^ja_m$; the recursion then solves as
$\kappa_j=\kappa_0\,\zeta^{\,j}F(j)F(i)/F(i+j)$, and this is periodic in $j$, as it must be, because
$\zeta^N=1$ while $F(j+N)/F(j)$ and $F(i+j+N)/F(i+j)$ both equal $\prod_ma_m$. Now evaluate the
displayed commutator at the node $u_j=\infty$: there $h_{x,j}$ takes the value $\kappa_j$, while
$h_y\circ t_x$ takes the value of $h_{y,j+i}$ at its own node, because
$t_x$ carries the node between $C_j$ and $C_{j+1}$ to the node between $C_{j+i}$ and
$C_{j+i+1}$. With $y=(\xi,l)$ and the corresponding constants
$\nu_j=\nu_0\,\xi^{\,j}F(j)F(l)/F(l+j)$, the commutator is

$$
\frac{\kappa_j\,\nu_{j+i}}{\nu_j\,\kappa_{j+l}}
=\xi^{\,i}\zeta^{-l}\cdot
\frac{F(j)F(i)}{F(i+j)}\cdot\frac{F(j+i)F(l)}{F(l+j+i)}\cdot
\frac{F(l+j)}{F(j)F(l)}\cdot\frac{F(i+j+l)}{F(j+l)F(i)}
=\xi^{\,i}\zeta^{-l},
$$

every $F$-factor cancelling against one other. The answer is independent of the $a_j$, hence of
$\Lambda$; it is alternating; and it is perfect, since a pair $(\zeta,i)$ pairing trivially with
all of $\mu_N\times\mathbf Z/N\mathbf Z$ has $\xi^i=1$ for every $\xi\in\mu_N$ and $\zeta^l=1$ for
every $l$, forcing $i=0$ and $\zeta=1$, and an injective homomorphism between finite etale groups
of the same order $N^2$ is an isomorphism. It is also independent of the splitting used to write
the points: replacing $(\zeta,i)$ by $(\zeta\eta^{\,i},i)$ for a fixed $\eta\in\mu_N$ leaves
$\xi^{\,i}\zeta^{-l}$ unchanged.

On a smooth fiber, $\lambda_{\mathcal L_\Lambda}=\lambda_0\circ[N]$ as noted, so
$K(\mathcal L_\Lambda)=E[N]$ and Book 35 Proposition 9A.2 applies: the commutator is perfect, and
its proof identifies it, up to the inversion of one argument, with the canonical kernel pairing
$\langle\,,\rangle_f$ of Book 35 (6.2) for the isogeny $f=\lambda_{\mathcal L_\Lambda}$, the second
argument $y$ entering as its biduality image $\delta_E(y)\in\ker f^\vee$, which lies there because
$f$ is symmetric. That pairing is built in Book 35 §6.1 out of the character attached to a
trivialized pullback, and a pullback along $u\circ f$ is a pullback along $f$ of a pullback along
$u$; so for an isomorphism $u$ one has
$\langle x,z\rangle_{u\circ f}=\langle x,u^\vee z\rangle_f$. Taking $f=[N]$ and $u=\lambda_0$, and
using that the kernel pairing of $[N]$ is the Weil pairing (Book 34 §14.3) together with the
symmetry $\lambda_0^\vee\circ\delta_E=\lambda_0$, the value is $e_N(x,\lambda_0y)$: the elliptic
Weil pairing of Book 34 §14.5.

Finally, two morphisms of finite etale $S$-schemes agreeing on every geometric fiber are equal,
their equalizer being open and closed and containing every point. The pairings attached to two
choices $\Lambda,\Lambda'$ therefore agree on $\mathcal M_\Lambda\cap\mathcal M_{\Lambda'}$, and the
local pairings glue.
$\square$

The formula on the boundary is worth reading. The $\mu_N$ appearing there is intrinsic, being the
$N$-torsion of the identity component of the smooth group, and it is its own exact annihilator, so
it is a Lagrangian and the pairing descends to a perfect duality between it and the group of
components. On the boundary the two Lagrangian directions, toric and component, are therefore
canonically distinguished, whereas on a smooth fiber no Lagrangian is canonical. This is the
geometric reason why the boundary of a modular curve with full level looks
like a finite set of cusps labelled by the possible identifications of the toric and component
directions.

The extension is now in the range of the parts of Book 35 Chapter 9A that concern central
extensions rather than abelian schemes. Write $\delta=(N)$, so that $d=N$,
$K(\delta)=\mathbf Z/N\mathbf Z$, $K(\delta)^D=\mu_N$, and $\mathcal G(\delta)$ is the standard
Heisenberg group scheme of that type.

**Boundary theta coordinates.** Let $N\geq3$ be invertible on $S$ and let $(E,\alpha)$ be a
generalized elliptic curve with ample $\Gamma(N)$-structure over $S$, lying in $\mathcal M_\Lambda$.
Then:

1. theta structures, that is isomorphisms
   $\Theta:\mathcal G(\delta)\to\mathcal G(\mathcal L_\Lambda)$ restricting to the identity on the
   central $\mathbf G_m$, exist etale-locally on $S$;
2. they form a torsor under the finite etale group scheme
   $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$, of order $N^2|\!\operatorname{Sp}(\delta)|$,
   and are represented by a finite etale $S$-scheme of that rank;
3. a theta structure makes $\pi_*\mathcal L_\Lambda$ a $\mathcal G(\delta)$-module of central character
   one and of rank $N$, hence produces a basis $\{\theta_y\}_{y\in\mathbf Z/N\mathbf Z}$, unique up
   to one common unit and compatible with base change;
4. the resulting closed immersion $E\hookrightarrow\mathbf P^{N-1}_S$ is canonical: it depends on
   the theta structure but not on the remaining scalar.

**Proof.** By the boundary theorem the group $E^{\mathrm{sm}}[N]$ is finite etale of order $N^2$,
killed by $N$, with $N$ invertible, and carries a perfect alternating pairing. Etale-locally on $S$
it is constant, and $\mu_N$ is constant as well; the pairing becomes a perfect alternating pairing
of finite abelian groups, so Book 35 Lemma 9A.3 puts it in the standard symplectic form, which for
a group of order $N^2$ killed by $N$ is the type $\delta=(N)$. Thus $\mathcal G(\mathcal L_\Lambda)$ and
$\mathcal G(\delta)$ become, etale-locally, two central extensions of the same finite etale group
of invertible order by $\mathbf G_m$ with the same commutator; Book 35 Theorem 9A.5 is a statement
about exactly this situation and makes no reference to abelian schemes, so it produces an
isomorphism of extensions identical on the centre. That is assertion 1.

Assertion 2 is Book 35 Theorem 9A.7, parts 1 and 2, which describe
$\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ purely in terms of the standard model; the
torsor statement follows because precomposition acts simply transitively on theta structures and
assertion 1 makes the sheaf of theta structures locally nonempty, whence it is represented by a
scheme finite etale of the same rank.

For assertion 3, transport the action of $\mathcal G(\mathcal L_\Lambda)$ on $\pi_*\mathcal L_\Lambda$ along
$\Theta$. The centre acts by scalars and the rank is $N=d$ by the ample generator cover, so Book 35
Theorem 9A.8 and Corollary 9A.9, which are statements about modules over $\mathcal G(\delta)$ and
involve no geometry, identify $\pi_*\mathcal L_\Lambda$ with $V(\delta)$ tensored by an invertible module
and supply the basis, unique up to a common unit, compatibly with base change since every
ingredient is.

Assertion 4 follows because a common unit scaling all the $\theta_y$ does not change the induced
map to $\mathbf P^{N-1}$, and because $\mathcal L_\Lambda$ is relatively very ample for $N\geq3$ by the
ample generator cover, so the map is a closed immersion. $\square$

The point of assertion 4 is that adding a theta structure to a levelled generalized elliptic curve
adds no moduli, being a finite etale operation, and yet removes the entire general linear ambiguity
of a projective embedding. That combination is what the next section needs.

### 9.4 When level produces a fine scheme

An automorphism of a generalized elliptic curve preserving a full level basis acts trivially on the level divisor and on the component group it meets. For $N\geq3$, with $N$ invertible, it is the identity. On a smooth fiber its action on every prime-adic Tate module is faithful: the torsion subgroups $E[\ell^m]$ are finite locally free of order $\ell^{2m}$ and etale for $\ell$ invertible by Book 35 §4.3, their union is schematically dense, and a homomorphism of abelian schemes is determined by a schematically dense restriction by Book 35 §4.1. That action is a matrix action, because Book 35 §7.6, Theorem 7.3 with $g=1$ makes $T_\ell E$ free of rank two over $\mathbf Z_\ell$ with $T_\ell E/\ell^mT_\ell E\simeq E[\ell^m](k)$, so that an automorphism acts through $\operatorname{GL}_2(\mathbf Z_\ell)$ and its reduction modulo $\ell^m$ is its action on $E[\ell^m]$. If an odd prime $\ell$ divides $N$, the action lies in $1+\ell M_2(\mathbf Z_\ell)$; if $N$ has no odd divisor, then $4\mid N$ and it lies in $1+4M_2(\mathbf Z_2)$. These two congruence groups are torsion-free. Indeed, for an element $1+\ell^aB$ of prime order, the first nonzero term in its binomial expansion has valuation $a+1$ for odd $\ell$, and at least $a+1$ for $\ell=2$ with $a\geq2$, whereas all later terms have larger valuation. Reduction to a prime divisor of the order proves the claim. On a polygon, the ample basis meets and labels every component and determines the automorphism on the dense smooth locus; equality there extends to the proper curve.

Thus full level $N\geq3$ kills inertia over $\mathbf Z[1/N]$. The stack is then a sheaf, and an
algebraic stack whose inertia is trivial is an algebraic space. Scheme representability does not
follow from trivial inertia alone, and the remaining step is what Section 9.3 was built for.

Being a scheme is a Zariski-local property, and the open substacks $\mathcal M_\Lambda$ of the ample
generator cover exhaust $\overline{\mathcal M}(\Gamma(N))$; so it is enough to represent each of
them. Work on $\mathcal M_\Lambda$ and let $\mathcal L_\Lambda=\mathcal O_E(\alpha(\Lambda))$ be the canonical
degree-$N$ bundle of that chart, with its theta group. A theta structure $\Theta$ gives, by the
boundary theta coordinates, a basis $\{\theta_y\}$ of the rank-$N$ bundle $\pi_*\mathcal L_\Lambda$,
unique up to one common unit, hence a canonical closed immersion into $\mathbf P^{N-1}$ over the
base, and the Heisenberg relations say that the standard $\mathbf Z/N\mathbf Z$ permutes the
homogeneous coordinates cyclically while the standard $\mu_N$ scales them by roots of unity.

Theta-framed level curves are therefore classified by a locally closed subscheme $\mathcal H$ of a
Hilbert parameter scheme of $\mathbf P^{N-1}$. The Hilbert polynomial is fixed: the embedded curve
has degree $N$ and arithmetic genus one. The group law, its action on the whole curve, the $N^2$
level sections, the Drinfeld divisor equality, and the Heisenberg relations between the coordinates
and the translations by $\alpha$ are closed conditions; ampleness of $\alpha(\Lambda)$, smoothness of the
prescribed open locus, and invertibility conditions are open. Nothing is lost in passing to
$\mathcal H$: the embedded curve recovers $E$ and $\mathcal L_\Lambda$, the marked sections recover
$\alpha$, and the theta structure is recovered from the basis because the theta group acts
faithfully on $\pi_*\mathcal L_\Lambda$, an element acting trivially on the standard module being trivial.

Forgetting the theta frame is now a quotient by a finite etale group scheme. Indeed, by the
boundary theta coordinates the theta structures form a torsor under
$G=\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ with $\delta=(N)$, finite etale of order
$N^2|\!\operatorname{Sp}(\delta)|$ over $\mathbf Z[1/N]$, so $\mathcal H\to\mathcal M_\Lambda$ is a $G$-torsor
and $\mathcal M_\Lambda$ is the fppf quotient sheaf of $\mathcal H$ by $G$. Since $\mathcal H$ is
quasi-projective and of finite presentation over the locally noetherian base, Chapter 7 constructs
the invariant quotient $\mathcal H/G$ as a quasi-projective scheme, and it is a categorical quotient
for $G$-invariant maps to schemes and to algebraic spaces. The two quotients agree: the projection
$\mathcal H\to\mathcal H/G$ is $G$-invariant, hence factors through the quotient sheaf, while
$\mathcal H\to\mathcal M_\Lambda$ is $G$-invariant, hence factors through $\mathcal H/G$; the two
factorizations are mutually inverse by the uniqueness in either universal property. Because inertia
has already vanished, this quotient represents the level sheaf itself rather than only its orbit
functor.

Each $\mathcal M_\Lambda$ is therefore a quasi-projective scheme, and the finitely many of them glue to
exhibit $\overline{\mathcal M}(\Gamma(N))$ as a scheme. It is a fine moduli scheme and carries the
universal generalized elliptic curve with its level structure. Two side conditions were consumed
and should be named: $N\geq3$, without which the frame is not rigid and the degree-$N$ bundle is
not very ample, and $N$ invertible on the base, without which $E^{\mathrm{sm}}[N]$ is not etale
and no normal form for the theta group exists.

Smaller or weaker levels require a stabilizer check. Full level $2$ is preserved by $[-1]$ because $-P=P$ on $2$-torsion. A $\Gamma_1(N)$ point may leave special automorphisms at small $N$, and a cyclic subgroup is preserved by $[-1]$ for every $N$. Hence a $\Gamma_0(N)$ problem is normally a stack even for large $N$ unless an auxiliary rigid level is added.

### 9.5 Compactified modular stacks and coarse curves

Write $\overline{\mathcal M}(\Gamma)$ for the stack of generalized elliptic curves with an ample level structure of type $\Gamma$. The level divisor bounds the number of polygon components by its degree, so Chapter 8 makes this an algebraic stack of finite presentation. Its diagonal is now finite. Indeed, over a valuation ring an isomorphism of generic fibers preserving the level divisor extends to the common stable marked model: normalize the closures of the components and contract every rational component having only its two nodal branches as special points, using Theorem 8.2A.3. A component disjoint from the level divisor is exactly such a contractible component. Ampleness says that no component in either model is contracted, so both models equal the common stable marked model. The extension is unique by density of the smooth locus. Thus the diagonal is proper; it was already quasi-finite and finitely presented, hence is finite. The open substack $\mathcal M(\Gamma)$ classifies smooth elliptic curves.

Zariski-locally on the base choose an auxiliary integer $M\geq3$ which is invertible there. Such
choices cover every integral base: near residue characteristic $p$, take any $M\geq3$ prime to
$p$. On the smooth locus one simply adds a full level-$M$ basis. At a polygon this basis need not
exist on the same contraction, so the compactified cover must also remember a decontraction
$E'\to E$ on which full level $M$ is ample. This qualification is essential.

The possible decontractions and bases form a finite surjective cover. This is Theorem 8.2B.3,
applied to the level data: it may be checked after
splitting the polygon: its smooth group is
$\mathbf G_m\times\mathbf Z/n\mathbf Z$; inserting a fixed finite number of components makes the
component group receive the two level generators. Choices of torsion generators are finite etale;
the root parameters which decontract a nodal family are finite locally free adjunctions on the
smoothing parameters of the nodes, by Lemmas 8.2B.1 and 8.2B.2 — finite flat, and not etale, at
the boundary. The
cyclic incidence determines the decontraction uniquely from
this finite data. The construction is equivariant under change of basis and descends from the
split polygon by Book 10. Thus the compactified auxiliary-level space $\widetilde X_M$ is a fine
scheme, finite and surjective over $\overline{\mathcal M}(\Gamma)$, with an action of the finite
change-of-basis group $\Delta_M$; the compatible contraction is determined by the level orbit. Moreover,

$$
\overline{\mathcal M}(\Gamma)\simeq[\widetilde X_M/\Delta_M].
$$

Indeed, a quotient-stack object is a $\Delta_M$-torsor carrying an equivariant auxiliary-level
family; descending its contraction gives a $\Gamma$-object. Conversely a $\Gamma$-object acquires
a decontraction and full basis after an fppf cover, and two choices differ by a unique element of
$\Delta_M$. The overlap elements satisfy the torsor cocycle, so the two constructions are inverse.

The finite quotient theorem therefore constructs a local coarse modular curve

$$
\overline{\mathcal M}(\Gamma)\longrightarrow X(\Gamma).
$$

On overlaps two such quotients are canonically isomorphic because both satisfy the same categorical
coarse universal property. Those isomorphisms obey the cocycle by uniqueness, so the local schemes
glue to $X(\Gamma)$. This proves existence over the original base rather than only after inverting
one auxiliary integer. Over a tame base, formation of $X(\Gamma)$ commutes with arbitrary base
change and finite locally free sheaves with trivial stabilizer action descend. At primes dividing
residual stabilizer orders, only flat base change is automatic.

The universal generalized elliptic curve lives on the stack. It descends to the coarse curve only where inertia acts trivially on it, which is generally false. In contrast, suitable powers of the Hodge line

$$
\omega=e^*\Omega^1_{E^{\mathrm{sm}}/\overline{\mathcal M}(\Gamma)}
$$

can descend once every stabilizer acts trivially on their fibers.

## 10. The common PEL framework

### 10.1 The fixed PEL datum

PEL abbreviates polarization, endomorphisms, and level. Fix the following rational datum:

- a finite-dimensional semisimple $\mathbf Q$-algebra $B$ with a positive involution $b\mapsto b^*$;
- a $*$-stable order $\mathcal O\subset B$;
- a faithful left $B$-module $V$;
- a nondegenerate alternating form $\psi:V\times V\to\mathbf Q$ satisfying

$$
\psi(bv,w)=\psi(v,b^*w);
$$

- a Hodge type, equivalently a conjugacy class determining the dimensions of the eigenspaces on $V\otimes\mathbf C$;
- a lattice $\Lambda\subset V$ on which the required prime-to-bad-prime pairing is integral;
- a compact open level subgroup $K$ in the finite adelic similitude group.

The traces of $B$ on the prescribed Hodge subspace generate the reflex field $E$. Choose a localization $R$ of its ring of integers on which $\mathcal O$, the polarization type, and the chosen level are well behaved. Every assertion below names further inverted primes when it uses etaleness or smoothness.

Fixing this datum prevents dimension and determinant conditions from drifting between connected components. It also separates the rational Shimura datum from an integral moduli model; different lattices or parahoric choices at bad primes can give different integral stacks with the same generic fiber.

### 10.2 Abelian schemes with endomorphisms and polarization

Over an $R$-scheme $S$, a PEL object is a tuple

$$
(A,\iota,\lambda,\eta K)
$$

with:

- an abelian scheme $A\to S$ of the dimension prescribed by $V$;
- a ring homomorphism $\iota:\mathcal O\to\operatorname{End}_S(A)$;
- a polarization $\lambda:A\to A^\vee$ of the fixed degree or kernel type;
- a $K$-orbit of level trivializations $\eta$ away from the primes excluded on $R$.

The Rosati condition is

$$
\lambda\circ\iota(b)=\iota(b^*)^\vee\circ\lambda
\qquad(b\in\mathcal O).
$$

It says that the adjoint involution induced by the polarization restricts to the prescribed involution on $B$. It is an equality of homomorphisms and therefore descends. The dual abelian scheme $A^\vee$, the dual homomorphism $b\mapsto\iota(b)^\vee$, and biduality are those of Book 35 §§3.1–3.4; that $\lambda$ is a symmetric isogeny induced by an ample bundle, with finite kernel of prescribed type, is Book 35 §§8.1–8.3.

For integral descent, a polarization may be encoded either by the homomorphism together with the condition of being induced by a relatively ample rigidified line bundle, or by such a line bundle itself. Positivity is never defined merely fiberwise by a sign. The fixed kernel type is a finite locally free subgroup condition, in the sense of Book 35 §8.3, and includes separability only when its rank is invertible.

For the parameter arguments in this book we use the line-bundle presentation: an inducing
rigidified symmetric ample bundle is part of the object and its genuine cocycle is part of every
descent datum. We record why this differs only by finite data from the homomorphism presentation.

**Polarization-line lemma** (Book 35 §§2.2–2.3, 8.1–8.2). For a rigidified line bundle
$\mathcal L$ on an abelian scheme, the
rule

$$
x\longmapsto t_x^*\mathcal L\otimes\mathcal L^{-1}
$$

is a homomorphism $\lambda_{\mathcal L}:A\to A^\vee$. If $\mathcal L$ is ample, its kernel is
finite. Two rigidified symmetric ample bundles inducing the same homomorphism differ by a
two-torsion point of $A^\vee$.

**Proof.** This is the theorem of the cube together with the square theorem, and we recall the
argument in the form used here; the rigidity input is Book 35 §1.3. On $A^3$, compare the four pullbacks of $\mathcal L$ by sums of one or three variables
with the three pullbacks by sums of two variables. Their quotient is trivial whenever one
variable is the identity. Rigidity for a line bundle on a proper family with geometrically
connected fibers then makes the quotient trivial everywhere: trivialize along one coordinate,
observe that the resulting map to the relative group of rigidified line bundles is constant on
the other connected proper fibers, and repeat. The resulting cube identity, specialized in one
variable, is the square identity and proves additivity of $\lambda_{\mathcal L}$. Its kernel is
proper. A positive-dimensional subgroup in the kernel would make $\mathcal L$ translation
invariant along that subgroup, so its restriction there would have degree zero, contradicting
ampleness. The kernel is therefore proper and quasi-finite, hence finite. If two bundles give the
same homomorphism, their quotient is translation-invariant and lies in $A^\vee$; symmetry
identifies it with its inverse, so its square is trivial. The converse is immediate. $\square$

Thus the choices of inducing bundle form a finite torsor. One may construct the stack with the
bundle and then take this finite quotient. This supplies the ample bundle needed below and does
not assume that an arbitrarily chosen bundle descends.

An isomorphism $f:(A,\iota,\lambda,\eta K)\to(A',\iota',\lambda',\eta'K)$ satisfies

$$
f\iota(b)=\iota'(b)f,\qquad
f^\vee\lambda'f=\lambda,\qquad
f(\eta K)=\eta'K.
$$

If the moduli problem allows polarizations up to a specified similitude group, replace the middle equality by equality up to that multiplier; the multiplier is part of the arrow and not silently forgotten.

### 10.3 The determinant condition

The action of $\mathcal O$ on $A$ differentiates to an action on the locally free sheaf $\operatorname{Lie}(A)$. The rational PEL datum prescribes a polynomial $P_b(T)\in R[T]$ for each $b\in\mathcal O$. The **determinant condition** is

$$
\det\bigl(T-\iota(b)\mid\operatorname{Lie}(A)\bigr)=P_b(T).
$$

This apparently infinite family is a finite scheme-theoretic condition. Choose a
$\mathbf Z$-basis $b_1,\ldots,b_s$ of $\mathcal O$ and form the universal element
$b_{\mathrm{univ}}=\sum X_ib_i$. Equality of

$$
\det\bigl(T-\iota(b_{\mathrm{univ}})\mid\operatorname{Lie}(A)\bigr)
$$

with the prescribed universal polynomial is equality of finitely many coefficients in
$R[X_1,\ldots,X_s,T]$. Specialization gives the condition for every $b$, and the converse is
obtained by comparing polynomial coefficients. The determinant locus is therefore closed and
commutes with base change. Imposing the condition only on a ring-generating set would not by
itself control arbitrary linear combinations and is not the definition used here.

This condition controls the infinitesimal Hodge type, not merely the total dimension. Without it an $\mathcal O$-action can distribute its embeddings incorrectly among tangent directions. In ramified residue characteristic the determinant condition alone need not produce the desired flat integral model; wedge, spin, or local-model conditions may be needed. Those are additional closed conditions attached to a chosen integral datum. We make no claim that the naive determinant locus is flat at every bad prime.

### 10.4 Prime-to-the-base level structures

For an integer $N$ invertible on $S$, a full level structure is an $\mathcal O$-linear similitude

$$
\eta_N:\Lambda/N\Lambda\xrightarrow{\sim}A[N]
$$

carrying $\psi$ to the Weil pairing up to the prescribed multiplier. The pairing meant here is the
alternating pairing $e_N^\lambda(x,y)=e_N(x,\lambda y)$ induced by the polarization on $A[N]$,
constructed in Book 35 §8.5 from the Weil pairing of Book 35 §§7.1–7.3, and perfect exactly when
$\lambda[N]$ is an isomorphism. More generally, a $K$-level structure is a $K$-orbit of compatible prime-to-bad-prime trivializations. The orbit formulation prevents a basis choice from being mistaken for intrinsic structure.

This adelic notation is still finite-presentation data. After fixing the lattice, every compact
open $K$ contains a principal congruence subgroup of some level $N$. A $K$-orbit is therefore the
finite quotient of a full level-$N$ trivialization by the finite group
$K/K(N)$. All stack and parameter arguments impose this finite level condition; no infinite list
of torsion trivializations is treated as a finite type object.

When the level order is not invertible, one must specify finite flat subgroup schemes and integral pairing conditions rather than geometric bases. Such parahoric level problems depend on a lattice chain and local model. The abstract stack and descent arguments still apply, but etaleness and smoothness do not follow from the prime-to-level proof.

A level is **neat** if no nontrivial finite-order automorphism compatible with the rational tensors fixes it. A principal level $N\geq3$ is the standard sufficient example in the symplectic cases considered here. Neatness is the exact property used to remove inertia.

### 10.5 Stack, diagonal, and atlas theorems

We first isolate the final representability step.

**Rigid-level scheme lemma.** Let the base be locally noetherian and let the fixed integral
polarization type $\delta$ have order $d=d_1\cdots d_g$ invertible on it. Then polarized abelian
schemes of fixed dimension and that polarization type, with neat prime-to-base level, form a
quasi-projective scheme.

**Proof.** Zariski-locally on the base choose $n\geq3$ invertible there; such $n$ exist near every
point, as in Section 9.5. Replace the inducing rigidified symmetric ample bundle $\mathcal L$ by
$\mathcal L^n$, which is very ample, of type $n\delta$ and of order $n^gd$, again invertible on the
base. Its theta group is the central extension of $K(\mathcal L^n)=\ker\lambda_{\mathcal L^n}$ by
$\mathbf G_m$ obtained from pairs $(x,\phi)$ with $\phi:t_x^*\mathcal L^n\simeq\mathcal L^n$,
constructed with its commutator pairing in Book 35 §9.2; the polarization-line lemma above
identifies the kernel with the one attached to the polarization.

All of Book 35 Chapter 9A now applies, since it asks exactly that the order of the type be
invertible on the base, which the choice of $n$ has arranged. The commutator pairing is perfect (Proposition 9A.2); $K(\mathcal
L^n)$ is finite etale and, etale-locally, symplectically isomorphic to
$K(n\delta)\times K(n\delta)^D$ (Theorem 9A.4); theta structures, that is isomorphisms with the
standard Heisenberg extension of type $n\delta$ respecting the central $\mathbf G_m$, exist
etale-locally (Theorem 9A.6) and form a torsor under the finite etale group scheme
$\operatorname{Aut}_{\mathbf G_m}(\mathcal G(n\delta))$, represented by a finite etale scheme
(Theorem 9A.7); and the pushforward of $\mathcal L^n$ is locally free of rank $n^gd$ with base
change (Book 35 §8.6), hence is a module of central character one and of the standard rank, so a
theta structure produces a basis of it, unique up to one common unit and compatible with base
change (Theorems 9A.8 and 9A.10 with Corollary 9A.9). Since a common unit does not move the
induced projective embedding, a theta-framed object is a
locally closed point of the Hilbert parameter scheme: the group law, level sections,
endomorphisms, and polarization pairing are imposed by the graph and tensor equations already
constructed. It is therefore represented by a quasi-projective scheme. Forgetting the theta
frame is the quotient by the finite etale change-of-frame group. Chapter 7 constructs the
quasi-projective scheme quotient.
Neatness says that no residual automorphism of the abelian scheme
fixes the level, so this quotient represents the original sheaf and carries its universal
abelian scheme. Different auxiliary $n$ and local choices give canonically isomorphic schemes by
the representing property, and these glue over the base. $\square$

**PEL stack theorem.** For fixed integral PEL data, fixed polarization type, determinant condition, and finite-presentation integral level or local-model condition, PEL objects form an fpqc stack. Its diagonal is representable, separated, and finite, and it is an algebraic stack of finite presentation. After adding neat prime-to-base level, its inertia is trivial; and if in addition the order of the polarization type is invertible on the base, it is represented by a quasi-projective scheme, by the rigid-level scheme lemma.

**Proof.** Book 10 descends the abelian scheme, group law, endomorphisms, rigidified polarization, and finite level data. The determinant and Rosati conditions descend as equations; ampleness descends by Book 8. This proves the stack assertion.

For the diagonal, a polarization-preserving isomorphism belongs to the finite automorphism scheme of a polarized abelian scheme. Commuting with $\mathcal O$ and preserving level cut out closed subgroups or closed translates. Hence the diagonal is finite and separated.

Choose a sufficiently high power of the inducing line bundle. Book 8 gives projective embeddings and the required Hilbert parameter scheme locally on the noetherian base. Endomorphism graphs, the group law, Rosati compatibility, determinant equations, and the stated integral local-model conditions define locally closed loci. Their Hilbert polynomials and graph degrees are fixed by the dimension and polarization type. Frames form a general-linear torsor, so the framed-parameter theorem gives algebraicity and finite presentation.

Finally, a neat level forces every stabilizer to be trivial, and where the order of the
polarization type is invertible the rigid-level scheme lemma represents the resulting sheaf.
$\square$

The theorem separates three issues that are often conflated: descent proves stackhood and a parameter presentation proves algebraicity. Smoothness of an atlas comes from the frame torsor; smoothness of the stack over its arithmetic base is a different deformation statement and is not asserted here.

## 11. Hilbert moduli problems

### 11.1 Real multiplication and polarization modules

Let $F$ be a totally real field of degree $d$, with ring of integers $\mathcal O_F$. A Hilbert abelian scheme over $S$ is an abelian scheme $A/S$ of relative dimension $d$ with an embedding

$$
\iota:\mathcal O_F\hookrightarrow\operatorname{End}_S(A).
$$

A single principal polarization is often too restrictive and is not stable under all ideal-class operations. The intrinsic datum is the fppf sheaf of symmetric $\mathcal O_F$-linear homomorphisms

$$
\mathcal P(A)=
\operatorname{Hom}_{\mathcal O_F}^{\mathrm{sym}}(A,A^\vee),
$$

where symmetry means self-duality under the identification of Book 35 §3.4 and the sheaf is the
homomorphism sheaf of Book 35 §4.1, cut out by the $\mathcal O_F$-linearity and symmetry
equations,
with its positive cone of polarizations in the sense of Book 35 §8.2. It is not assumed in advance to be invertible;
invertibility is part of the condition below. Fix a fractional ideal $\mathfrak c$ and its totally positive cone $\mathfrak c^+$. A **$\mathfrak c$-polarization** is an isomorphism of ordered invertible $\mathcal O_F$-module sheaves

$$
\lambda:\mathfrak c\xrightarrow{\sim}\mathcal P(A)
$$

that carries $\mathfrak c^+$ to polarizations and for which the induced map

$$
A\otimes_{\mathcal O_F}\mathfrak c\longrightarrow A^\vee
$$

has the prescribed isomorphism or finite-kernel type. The tensor product is the abelian scheme
obtained by the Serre tensor construction of Book 35 §5.6: since $\mathfrak c$ is a finitely
generated projective $\mathcal O_F$-module of rank one, Theorem 5.3 there represents the fppf sheaf
$T\mapsto A(T)\otimes_{\mathcal O_F}\mathfrak c$ by an abelian scheme of the same relative dimension
$d$, formed compatibly with arbitrary base change; Proposition 5.4 makes the construction functorial
in the module and in the abelian scheme, so that $A\otimes\mathcal O_F\simeq A$ and
$(A\otimes\mathfrak a)\otimes\mathfrak b\simeq A\otimes\mathfrak a\mathfrak b$; and Theorem 5.6
gives the duality needed to say what self-duality of $\lambda$ means here, in the form
$(A\otimes_{\mathcal O_F}\mathfrak c)^\vee\simeq A^\vee\otimes_{\mathcal O_F}\mathfrak c^{-1}$.
A reader who prefers to fix one $c\in\mathfrak c^+$ may read the polarization condition at
that single $c$ using only Book 35 §§8.1–8.3, but then the ideal class is no longer visible, which
is precisely what the tensor construction is for: a nonprincipal class cannot be absorbed into an
isomorphism $A\otimes\mathfrak c\simeq A$.

This formulation records all compatible polarizations at once and makes ideal-class changes functorial. Choosing one $c\in\mathfrak c^+$ recovers a polarization $\lambda(c)$, but the choice of $c$ is auxiliary and should not enter the moduli problem.

An automorphism must commute with $\mathcal O_F$, preserve the ordered polarization-module isomorphism, and preserve level. Multiplication by a totally positive unit is not automatically an automorphism of the polarized object: its effect on $\mathcal P(A)$ must satisfy the stated equality.

### 11.2 The Hilbert determinant condition

For every $a\in\mathcal O_F$, require

$$
\det\bigl(T-\iota(a)\mid\operatorname{Lie}(A)\bigr)
=\prod_{\tau:F\hookrightarrow\overline{\mathbf Q}}(T-\tau(a)).
$$

The right side has rational integer coefficients and is interpreted on the chosen base. Over $\mathbf Z[1/\operatorname{disc}(F)]$, the algebra $\mathcal O_F\otimes\mathcal O_S$ is etale locally a product of $d$ copies of $\mathcal O_S$. The determinant condition is then equivalent to $\operatorname{Lie}(A)$ being locally free of rank one over $\mathcal O_F\otimes\mathcal O_S$: idempotents split the Lie bundle into $d$ line bundles, and the displayed characteristic polynomial forces each embedding to occur once.

At primes ramified in $F$, that equivalence fails. A module can have the correct characteristic polynomials without being locally free over the ramified algebra. One may impose the stronger Rapoport condition of rank-one local freeness, or use the polarization-module condition that gives the flat Deligne--Pappas model in the selected integral setting. These define related but not identical integral stacks. Their generic fibers agree; their special fibers need not.

This is an instructive counterexample to defining an integral moduli problem only by its characteristic-zero points. The exact integral condition is part of the name of the stack.

### 11.3 Rigid level and coarse descent

Fix an ideal $\mathfrak n\subset\mathcal O_F$ invertible on the base. A full level is an $\mathcal O_F$-linear symplectic similitude from a fixed rank-two module modulo $\mathfrak n$ to $A[\mathfrak n]$. Point and cyclic variants are defined by finite locally free $\mathcal O_F$-subgroups, with generators required only fppf-locally.

Let $\mathcal H_{\mathfrak c,K}$ denote the stack of Hilbert abelian schemes satisfying the chosen integral determinant condition, $\mathfrak c$-polarization, and $K$-level. The PEL stack theorem gives:

- $\mathcal H_{\mathfrak c,K}$ is an algebraic stack of finite presentation on the fixed integral locus;
- its diagonal is finite and separated;
- the frame map from the standard parameter scheme is a smooth atlas;
- for neat $K$, it is a fine quasi-projective scheme.

For a non-neat $K$, choose a normal neat subgroup $K'\triangleleft K$. The finite group $\Delta=K/K'$ acts on the fine scheme $H_{\mathfrak c,K'}$, and

$$
\mathcal H_{\mathfrak c,K}\simeq[H_{\mathfrak c,K'}/\Delta]
$$

when the moduli arrow convention uses exactly the $K$-orbit level. Its coarse space is the finite quotient $H_{\mathfrak c,K'}/\Delta$. Changing $K'$ does not change that coarse space, by its universal property.

The universal abelian scheme descends from $K'$ to the quotient stack by equivariance. It need not descend to the coarse Hilbert variety. A Hodge bundle or automorphic line bundle descends only when every residual stabilizer acts trivially on its fiber; on a tame locus, a tensor power killing all finite characters does descend.

## 12. Quaternionic moduli problems

### 12.1 Quaternionic multiplication

Let $F$ be totally real and let $B$ be a quaternion algebra over $F$, equipped with a positive involution $*$. Choose a $*$-stable order $\mathcal O_B$, a left $B$-module $V$, an alternating form compatible with $*$, and a lattice. The set of real places where $B$ splits and the chosen Hodge cocharacter determine the dimension of the associated moduli space; in the Shimura-curve case exactly one real place contributes a noncompact factor.

A quaternionic PEL object is an abelian scheme $A$ of the dimension dictated by $V$ with an action

$$
\iota:\mathcal O_B\longrightarrow\operatorname{End}_S(A),
$$

a polarization of fixed type whose Rosati involution restricts to $*$, and a level orbit. The order action is noncommutative, so it is not enough to specify commuting endomorphisms. Choose generators of $\mathcal O_B$ and impose their full multiplication table as equations of endomorphisms.

At primes where $B$ is split and the order is maximal, Morita equivalence can translate the datum into lower-rank linear algebra. At ramified primes that translation changes with the lattice chain and must not be used as though a global matrix algebra identification existed.

### 12.2 Rosati compatibility and determinant data

For $b\in\mathcal O_B$, Rosati compatibility is again

$$
\lambda\iota(b)=\iota(b^*)^\vee\lambda.
$$

The Hodge datum prescribes

$$
\det\bigl(T-\iota(b)\mid\operatorname{Lie}(A)\bigr)=P_b(T),
$$

where $P_b$ is formed from the reduced characteristic polynomial of $b$ with multiplicities determined by the selected real embeddings. Writing merely a power of the reduced norm without those multiplicities can define the wrong dimension, so $P_b$ belongs to the fixed PEL datum.

The determinant condition is closed. The condition that the alternating form induced by the polarization be perfect on the chosen prime-to-bad-prime Tate module is open-and-closed once its finite kernel type is fixed; at each finite level this is the perfectness criterion of Book 35 §8.5, namely that $\lambda[N]:A[N]\to A^\vee[N]$ be an isomorphism, and only that finite-level form is used. At a ramified prime, the correct integral model may additionally impose a lattice-chain, wedge, or local-model condition. These are finite-presentation tensor or rank conditions, so they preserve the stack proof, but smoothness must be decided for that particular local model.

### 12.3 The resulting stack and its quotients

Let $\mathcal Q_K$ denote the exact quaternionic PEL stack just specified. Effective descent follows in the order

$$
A\ ;\quad \iota\ ;\quad \lambda\ ;\quad
\text{determinant and local-model conditions}\ ;\quad \eta K.
$$

The order matters only logically: the later conditions are statements about structures already descended. The diagonal is the closed subgroup of polarization-preserving automorphisms commuting with $\mathcal O_B$ and fixing the level, hence is finite.

Framed polarized embeddings give a smooth atlas and $\mathcal Q_K$ is algebraic of finite presentation; this does not assert that its structural morphism is smooth at a ramified prime. If $K'$ is neat and normal in $K$, the fine scheme $Q_{K'}$ carries the finite action of $K/K'$ and

$$
\mathcal Q_K\simeq[Q_{K'}/(K/K')].
$$

The quotient scheme is coarse. Fixed points of the finite action do not disappear: they become inertia in the quotient stack and quotient singularities in the coarse space.

In the compact Shimura-curve case no cusps are added. The required hypothesis is that the
similitude group be anisotropic modulo its center—for example, in the rank-two case, that the
quaternion algebra be a division algebra at some finite place. Then there are no relevant rational
parabolic subgroups. If $B=M_2(F)$, this conclusion is false and one obtains a modular-type
noncompact curve. Geometric properness is different from stack separatedness: the latter follows
from the finite diagonal, while the former requires precisely this global anisotropy.

## 13. Coarse descent and synthesis

### 13.1 Descending constructions through a coarse map

Let $\pi:\mathcal X\to M$ be one of the finite-quotient coarse maps constructed above. There are three distinct descent questions.

First, a morphism $\mathcal X\to Z$ to an algebraic space always descends uniquely, by the defining universal property of $M$. Hecke maps defined between stacks therefore induce maps between coarse spaces once source and target levels are matched.

Second, a line bundle $\mathcal L$ descends only if inertia acts trivially on every fiber. Necessity is immediate because a pullback from $M$ has trivial stabilizer action. On a tame quotient chart $[X/G]$, sufficiency follows from exact invariants: the equivariant module of sections has invariant descent data, and the adjunction from the quotient pullback is an isomorphism after the finite cover. The local descended bundles glue uniquely.

Third, a family of curves or abelian schemes almost never descends merely because its isomorphism class defines the coarse point. Descent would require coherent identifications along the finite relation, and stabilizers would have to act trivially on the family. The universal object therefore belongs naturally to the stack.

These distinctions explain a standard phenomenon. Modular forms, viewed as sections of powers of the Hodge line, can often be interpreted on a coarse modular curve after taking a suitable power, even though the universal elliptic curve cannot.

### 13.2 A comparison table

| Object                     | Values over $T$          | Automorphisms retained? |            Local geometric chart? |                Universal family? |
| -------------------------- | ------------------------ | ----------------------: | --------------------------------: | -------------------------------: |
| Isomorphism-class presheaf | sets                     |                      no |                       not implied |                      not implied |
| Moduli sheaf               | sets                     |                      no |                       not implied |       only if represented finely |
| Moduli stack               | groupoids                |                     yes |                       not implied | yes, tautologically on the stack |
| Algebraic moduli stack     | groupoids                |                     yes |               smooth scheme atlas |                              yes |
| Coarse space               | sets of geometric orbits |                      no | an algebraic space or scheme here |                     generally no |
| Fine moduli scheme         | discrete groupoids       |     necessarily trivial |                    identity atlas |                              yes |

The table is not a hierarchy in which every move rightward improves the object. Passing from a stack to a coarse space deliberately forgets information. Passing from a stack to a fine scheme is possible only after level or another rigidification has removed inertia.

### 13.3 The reusable theorem package

The constructions of this book yield the following precise results for later modular and PEL geometry.

- Categories fibered in groupoids encode pullback intrinsically; chosen pullbacks form a coherent contravariant pseudofunctor because cartesian lifts are unique up to unique isomorphism.
- A prestack has descent for isomorphisms. A stack also has effective descent for objects. Generalized elliptic and fixed PEL data are fpqc stacks by the effective descent results of Book 10.
- Two-fiber products retain the comparison isomorphism. The diagonal represents isomorphisms, and inertia represents automorphisms.
- A representable morphism may be tested after every scheme base change. Finite, smooth, etale, and proper have this meaning for stack morphisms.
- A stack with representable diagonal and a smooth surjective scheme atlas is algebraic. Framing a sufficiently positive projective embedding produces the atlases needed here from the parameter spaces of Book 8.
- For a smooth affine finitely presented group acting on a separated scheme, the quotient stack has its canonical smooth atlas and representable diagonal. For a finite locally free group, the canonical map is a finite flat presentation; in the quasi-projective finite-presentation cases used here, induction through a general linear group supplies a genuine smooth scheme atlas. The smoothness of $\operatorname{GL}_r/G$ that this induction needs is source-descent of smoothness, Book 10 §10.5, and not the base-locality tables of Book 10 §§10.3–10.4.
- A compatible central flat subgroup of inertia can be rigidified; locally $[X/G]\sslash H=[X/(G/H)]$ when $H$ acts trivially.
- Over a locally noetherian base, a finite locally free group acting on a finitely presented quasi-projective scheme has a finite scheme quotient. The quotient-stack map to that scheme is coarse. Flat base change is safe; arbitrary base change and descent of finite locally free sheaves with trivial stabilizer action require linear reductivity.
- Generalized elliptic curves with bounded polygonal boundary form algebraic stacks with separated quasi-finite diagonal; the unlevelled diagonal need not be proper. Ample Drinfeld level bounds the boundary and makes the modular-stack diagonal finite. Full invertible level $N\geq3$ kills inertia and yields a fine scheme.
- Given a generalized elliptic curve with a divisor meeting every component, contraction of the
  components disjoint from it exists, is unique, commutes with arbitrary base change, and adds
  thicknesses along contracted chains (Theorem 8.2A.3, Lemma 8.2A.4). Conversely, decontractions
  inserting at most $m$ components are carried by finite locally free root adjunctions on node
  smoothing parameters together with finite etale torsion choices, and form a finite surjective
  representable cover (Lemmas 8.2B.1–8.2B.2, Theorem 8.2B.3); this is what Section 9.5 uses for
  $\widetilde X_M$ and the finite diagonal.
- Hilbert and quaternionic PEL objects are defined by an exact order action, Rosati-compatible polarization, determinant or stated integral local-model condition, and level orbit. Their stacks have finite diagonal and explicit framed atlases. Neat level produces fine quasi-projective schemes; removing it gives finite quotient stacks and coarse spaces.
- On a generalized elliptic curve with ample full level $N$, $N$ invertible, the singular
  geometric fibers are Neron $N$-gons, the group $E^{\mathrm{sm}}[N]$ is constant of order $N^2$,
  and the theta group of a degree-$N$ bundle of degree one on each component is a central extension
  of it by $\mathbf G_m$ whose commutator is perfect and alternating, is the elliptic Weil pairing
  on the smooth locus, and is $\xi^i\zeta^{-l}$ on the boundary in the intrinsic coordinates given
  by the toric and component directions. A theta structure then supplies theta coordinates across
  the boundary. This is Section 9.3, and it is the ingredient that the earlier books, which treat
  only abelian schemes, do not contain.

Every conclusion above is proved here or cited from an earlier book at its use site: Books 8, 9,
10, 15, 26, 27, 28, 34, and 35. Three of the inputs are worth naming because they are recent
additions and carry side conditions. The theta-framed fine schemes of Sections 9.4 and 10.5 use
the standard-form theory of Book 35 Chapter 9A, which requires the order of the polarization type
to be invertible on the base, and in the modular case they use the boundary theory of Section 9.3
in its place, since Chapter 9A says nothing about polygonal fibers. The polarization-module
formulation of Section 11.1 uses the Serre tensor construction of Book 35 §5.6. The matrix form of
the prime-adic argument of Section 9.4 uses the Tate module theorem of Book 35 §7.6.

Every conclusion retains its hypothesis. Smoothness of a frame atlas is not confused with
smoothness of the structural morphism at a ramified local model. A determinant condition is not
substituted for a stronger integral condition where they differ. Finite is not silently
strengthened to finite etale. A coarse space is never treated as though it carried the universal
family.

### 13.4 Conclusion

Moduli geometry begins where classification by points stops. A family must pull back coherently, its isomorphisms must glue, and its local presentations must remember the symmetries used in gluing. Categories fibered in groupoids express pullback; stacks express descent; diagonals and inertia isolate isomorphisms and automorphisms; atlases return the problem to schemes without discarding either.

For modular problems, generalized elliptic curves add exactly the polygonal boundary compatible with the group law, while ample Drinfeld structures control that boundary integrally. For PEL problems, the order action, polarization, determinant condition, and level orbit make the Hodge type and integral structure explicit. In both settings, sufficiently rigid level gives a fine scheme. Removing that auxiliary rigidity produces a finite quotient stack, and invariant theory produces its coarse space.

The resulting picture is stable under descent and honest about its losses. The stack carries the universal geometry and its stabilizers. The fine cover supplies coordinates and projective parameter spaces. The coarse space records geometric orbits and receives descended constructions only when inertia permits them. Keeping these three objects distinct is the foundation on which modular curves, Hilbert--Blumenthal moduli, quaternionic Shimura curves, their compactifications, and their arithmetic correspondences can be built.
