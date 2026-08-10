# Moduli Stacks for Modular and PEL Problems

## Contents

1. [Why moduli problems form stacks](#1-why-moduli-problems-form-stacks)
   - [Objects, families, and symmetry](#11-objects-families-and-symmetry)
   - [Five levels of representability](#12-five-levels-of-representability)
   - [The base site and conventions](#13-the-base-site-and-conventions)
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
   - [Smooth and finite atlases](#52-smooth-and-finite-atlases)
   - [Parameter spaces and change of framing](#53-parameter-spaces-and-change-of-framing)
   - [An atlas criterion for the moduli problems of this book](#54-an-atlas-criterion-for-the-moduli-problems-of-this-book)
6. [Quotient stacks](#6-quotient-stacks)
   - [Torsors with equivariant maps](#61-torsors-with-equivariant-maps)
   - [The canonical quotient atlas](#62-the-canonical-quotient-atlas)
   - [The diagonal of a quotient stack](#63-the-diagonal-of-a-quotient-stack)
   - [Examples and warnings](#64-examples-and-warnings)
7. [Rigidification, finite quotients, and coarse spaces](#7-rigidification-finite-quotients-and-coarse-spaces)
   - [Removing a prescribed central stabilizer](#71-removing-a-prescribed-central-stabilizer)
   - [Finite group quotients](#72-finite-group-quotients)
   - [Coarse moduli spaces](#73-coarse-moduli-spaces)
   - [Base change and tame descent](#74-base-change-and-tame-descent)
8. [Generalized elliptic curves](#8-generalized-elliptic-curves)
   - [The boundary object](#81-the-boundary-object)
   - [The stack property and diagonal](#82-the-stack-property-and-diagonal)
   - [Weierstrass charts and contraction](#83-weierstrass-charts-and-contraction)
   - [Algebraicity and bounded boundary](#84-algebraicity-and-bounded-boundary)
9. [Modular level structures](#9-modular-level-structures)
   - [Drinfeld structures and ampleness](#91-drinfeld-structures-and-ampleness)
   - [Full, point, and cyclic level](#92-full-point-and-cyclic-level)
   - [When level produces a fine scheme](#93-when-level-produces-a-fine-scheme)
   - [Compactified modular stacks and coarse curves](#94-compactified-modular-stacks-and-coarse-curves)
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
13. [Unitary moduli problems](#13-unitary-moduli-problems)
    - [CM actions and signatures](#131-cm-actions-and-signatures)
    - [Hermitian polarizations](#132-hermitian-polarizations)
    - [Level, inertia, and coarse spaces](#133-level-inertia-and-coarse-spaces)
14. [Coarse descent and synthesis](#14-coarse-descent-and-synthesis)
    - [Descending constructions through a coarse map](#141-descending-constructions-through-a-coarse-map)
    - [A comparison table](#142-a-comparison-table)
    - [The reusable theorem package](#143-the-reusable-theorem-package)
    - [Conclusion](#144-conclusion)

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

Fix a base scheme $S_0$. Unless stated otherwise, all test schemes are $S_0$-schemes and coverings are fppf coverings. The fpqc topology gives the same stack assertions for the objects considered here because Book 13 proves effective fpqc descent for their underlying schemes, morphisms, line bundles, and group structures. We use fppf atlases because finite presentation is essential in the geometric applications.

A fiber product of stacks is always a two-fiber product: an object over $T$ includes objects on the two sides and an isomorphism between their images. Equality of objects is never substituted for an isomorphism. A property of a morphism from a stack is called representable when every pullback along a scheme is represented by an algebraic space; in the explicit cases below it will in fact be a scheme.

We use “finite” for finite morphisms and “finite locally free” when flatness and constant local rank are intended. These differ at bad residue characteristics. A level structure of order $N$ is never called etale unless $N$ is invertible on the base.

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

This is descent of arrows, or full faithfulness of restriction to descent data. It says nothing yet about constructing an object from local objects. Book 13 proves it for schemes and structured schemes: morphisms descend uniquely, and equality can be checked after a faithfully flat cover. Since compatibility with a section, action, or pairing is an equality of morphisms, it descends as well.

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

The proof pattern for geometric objects is rigid. Descend the underlying schemes first. Descend line bundles and finite locally free modules. Descend all structure morphisms by full faithfulness. Check identities after pulling back to the cover. Finally descend geometric properties such as properness, smoothness, or finite local freeness. This is precisely the order established in Book 13.

For a family of abelian varieties, connectedness of geometric fibers is checked after residue-field extension. For a generalized elliptic curve, the polygonal fiber condition and the action on components are likewise geometric and fpqc local. Hence neither application requires a new general effectivity theorem.

### 3.3 Why stackification is sometimes necessary

A natural quotient construction may be a prestack but not a stack. Suppose one starts with the action groupoid $G(T)\times X(T)\rightrightarrows X(T)$. It sees only objects globally represented by points of $X(T)$. After a cover, however, local points may be related by transition elements of $G$ defining a nontrivial $G$-torsor. Such local data need not come from a global point of $X(T)$.

Stackification adds exactly these twisted objects. It does not arbitrarily add geometric points: it makes descent data effective while preserving the already correct isomorphism sheaves. For group actions, the resulting objects are $G$-torsors with equivariant maps to $X$.

By contrast, taking the sheafification of orbit sets loses stabilizers first and repairs only set-valued descent afterward. The two operations differ. The action of a finite group $G$ on a point gives a one-point orbit sheaf, while its quotient stack has automorphism group $G$ at that point.

### 3.4 Moduli data are stacks

**Structured-family stack theorem.** Let objects over $S$ be schemes of finite presentation equipped with a finite list of the following data: morphisms, sections, finite locally free group objects, actions, line bundles with rigidifications, finite locally free tensors and perfect pairings. Impose conditions that are equalities of maps or properties fpqc local on the base. If the underlying class of schemes has effective fpqc descent, then the resulting fibered category is an fpqc stack.

**Proof strategy.** Separate construction from properties. Book 13 supplies effectivity for the underlying schemes, sheaves, and group objects. It also supplies full faithfulness for every structure map. Thus all data descend and their equations can be checked upstairs. The remaining adjectives descend by their stated locality. For an ample polarization, use the descended rigidified line bundle and fpqc descent of ampleness from Book 8. This constructs an effective object. Uniqueness follows from descent of isomorphisms. $\square$

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

Finite inertia alone does not imply a finite diagonal without quasi-compactness and separation of the isomorphism spaces. Conversely, a finite diagonal makes every stabilizer finite but does not make it trivial. For polarized abelian schemes the polarization forces the automorphism group to be finite: after choosing a high symmetric power of the polarization line bundle, automorphisms act faithfully on a finite projective embedding, and the subgroup preserving the embedded abelian variety and its group law is proper and affine, hence finite. Its infinitesimal part may survive in bad characteristic, so unramifiedness must be checked separately.

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

### 5.2 Smooth and finite atlases

A **finite atlas** means a representable finite, flat, surjective map from a scheme. It is much stronger than a smooth atlas. Its relative dimension is zero, and it implies especially tight control of the stack by a finite equivalence relation. A finite surjective map that is not flat is not called a finite atlas here.

For a quotient $[X/G]$, the canonical atlas $X\to[X/G]$ inherits the property of the group scheme $G\to S_0$: it is smooth if $G$ is smooth, etale if $G$ is etale, and finite locally free if $G$ is finite locally free. Thus one quotient presentation can supply either kind of atlas.

A fine moduli scheme has the identity as an atlas, but the existence of a finite atlas does not make a stack a scheme. The classifying stack of a nontrivial finite flat group has a finite flat atlas by a point and still has that group as inertia.

### 5.3 Parameter spaces and change of framing

Moduli objects are made representable by adding frames. Choose a canonical relatively ample line bundle, take a sufficiently high power, and choose a basis of its pushforward. The basis embeds the family into a fixed projective space. Book 8 represents families with the required Hilbert polynomial by a Hilbert scheme. Group laws, sections, endomorphisms, and polarizations then occupy closed or locally closed loci; smoothness and nondegeneracy are open conditions.

Changing the basis acts through a general linear group. Consequently the unframed moduli problem is locally a quotient

$$
[H/\operatorname{GL}_r],
$$

where $H$ is a locally closed parameter scheme. The frame bundle of any family is a $\operatorname{GL}_r$-torsor, so the map $H\to\mathcal X$ is smooth and surjective. This is the standard atlas mechanism.

There is no circular use of a universal moduli space here. Book 8 constructs the parameter scheme, and Book 13 descends the family after changes of frame. The quotient stack packages precisely those changes.

### 5.4 An atlas criterion for the moduli problems of this book

**Framed-parameter atlas theorem.** Suppose a stack $\mathcal X$ classifies proper flat finitely presented schemes with a canonical relatively ample line bundle $\mathcal L$, and suppose:

1. a fixed power $\mathcal L^m$ has a base-change-compatible locally free pushforward of rank $r$ and gives a closed immersion;
2. the relevant Hilbert polynomial is fixed;
3. all additional structures are represented by locally closed conditions in the resulting parameter scheme;
4. isomorphisms preserving the structures are representable.

Then $\mathcal X$ is algebraic, with a smooth atlas by the scheme of objects framed by a basis of the pushforward.

**Proof.** The framed objects form a locally closed subscheme $H$ of the Hilbert parameter space. The frame-change group $G=\operatorname{GL}_r$ acts on $H$. A family in $\mathcal X(T)$ acquires a frame after the fppf cover given by its frame bundle, and a framed family gives a map to $H$. Changes between frames are exactly $G$-valued arrows. Hence $\mathcal X\simeq[H/G]$. The quotient theorem of the next chapter makes $H\to\mathcal X$ smooth and surjective. Representability of the diagonal follows from the assumed isomorphism spaces. $\square$

The first condition is applied only where the needed base-change statement is available. In later volumes more refined cohomological results enlarge its range. Here explicit Weierstrass or level charts can replace it when necessary.

## 6. Quotient stacks

### 6.1 Torsors with equivariant maps

Let a flat finitely presented group scheme $G\to S_0$ act on an $S_0$-scheme $X$. The quotient stack $[X/G]$ assigns to $T$ the groupoid of pairs

$$
(P,u),\qquad P\to T\text{ a right }G_T\text{-torsor},qquad
u:P\to X_T,
$$

where $u(pg)=g^{-1}u(p)$. The inverse appears because the torsor acts on the right and $X$ on the left. An arrow is a $G_T$-equivariant isomorphism of torsors commuting with $u$.

This definition includes twisted forms automatically. The trivial torsor $G_T$ with map $g\mapsto g^{-1}x$ corresponds to $x\in X(T)$. Every torsor becomes trivial fppf-locally, so every quotient-stack object is locally of this form. Descent for torsors and equivariant morphisms, proved in Book 13, shows that $[X/G]$ is a stack.

The naive orbit presheaf $T\mapsto X(T)/G(T)$ sees only trivial torsors. Even its sheafification remembers no stabilizers. The quotient stack is therefore the correct moduli quotient whenever changes of frame may twist.

### 6.2 The canonical quotient atlas

There is a map $q:X\to[X/G]$ sending $x:T\to X$ to the trivial torsor with its equivariant map. It is representable. More precisely, for $(P,u)\in[X/G](T)$ there is a canonical isomorphism

$$
T\times_{[X/G]}X\simeq P.
$$

To see this, a point of the fiber product is a point $x$ of $X$ together with an isomorphism between its trivial torsor and $P$. Such an isomorphism is determined by the image of the identity section, a point $p\in P$, and compatibility forces $x=u(p)$. This construction is reversible and respects base change.

Since $P\to T$ is an fppf $G$-torsor, $q$ is flat, locally of finite presentation, and surjective. If $G$ is smooth, etale, or finite locally free, then $q$ has the same property. Thus:

**Quotient-atlas theorem.** If $G$ is smooth and finitely presented, $X\to[X/G]$ is a smooth atlas. If $G$ is finite locally free, it is a finite flat atlas.

This proof is fully local and does not assume that an orbit scheme exists.

### 6.3 The diagonal of a quotient stack

Let $(P,u)$ and $(Q,v)$ be two objects over $T$. The pullback of the diagonal is the sheaf of equivariant isomorphisms $\phi:P\to Q$ satisfying $v\phi=u$. The sheaf $\underline{\operatorname{Isom}}_G(P,Q)$ is a twisted form of $G_T$ and is represented by a $G_T$-torsor. The additional equality cuts out an equalizer.

Assume $G$ is affine and finitely presented and $X$ is separated over $S_0$. The torsor of isomorphisms is affine and finitely presented over $T$. Because the diagonal of $X$ is closed, the equality $v\phi=u$ defines a closed subscheme. Hence the diagonal of $[X/G]$ is representable, separated, and finitely presented. If $G$ is finite, it is finite. If $G$ is unramified, the diagonal is unramified.

These hypotheses are sufficient rather than maximal. They are exactly what the parameter schemes and frame-change groups below provide. Without separatedness of $X$, the equalizer need not be closed. Without affineness of $G$, the isomorphism torsor need not be a scheme affine over $T$.

### 6.4 Examples and warnings

For $X=S_0$ with trivial action, $[X/G]=BG$, the classifying stack of $G$-torsors. Its atlas $S_0\to BG$ has fiber $G$. Its coarse sheaf of orbits is just $S_0$, but its inertia is $G$ up to conjugation. This is the smallest counterexample to the claim that a quotient stack is its orbit space.

If $G=\mathbf G_m$ acts on $\mathbf A^1$ by scaling, the nonzero locus has trivial stabilizer and quotient a point, while the origin has stabilizer $\mathbf G_m$. The quotient stack is not separated because its diagonal is not proper. Stabilizer dimension can therefore jump even when the atlas is smooth.

If a finite group of order invertible on the base acts, its constant group scheme is finite etale, so the quotient stack is Deligne--Mumford and has a finite etale atlas. If the order is not invertible, the same abstract group may define a finite etale constant group scheme, but naturally occurring group schemes such as $\mu_p$ are not etale in characteristic $p$. “Finite stabilizer” must not be replaced by “etale stabilizer.”

## 7. Rigidification, finite quotients, and coarse spaces

### 7.1 Removing a prescribed central stabilizer

Sometimes a subgroup of automorphisms occurs in every object and acts trivially on the underlying coarse geometry. For polarized abelian schemes, scalar roots of unity can have this character. Adding level removes them, but another operation is useful when level should not be chosen.

Let $\mathcal X$ be a stack and let $H\to\mathcal X$ be a flat finitely presented subgroup of inertia such that $H_x\subseteq\operatorname{Aut}(x)$ is central and is preserved by every isomorphism. The **rigidification** $\mathcal X\mathbin{\!\sslash\!}H$ has the same objects locally, but its isomorphism sheaves are the fppf quotients

$$
\underline{\operatorname{Isom}}_{\mathcal X}(x,y)/H_x,
$$

followed by stackification. The map $\rho:\mathcal X\to\mathcal X\mathbin{\!\sslash\!}H$ sends

$$
\operatorname{Aut}_{\mathcal X}(x)longrightarrow
\operatorname{Aut}_{\mathcal X\sslash H}(\rho x)
$$

with kernel $H_x$ and, fppf-locally, quotient the target.

Centrality is decisive: without it, composition of cosets is not well defined. Compatibility under isomorphism is what allows the local quotients to glue. Rigidification does not quotient the objects by an action on their underlying schemes; it quotients a specified part of their automorphism groups.

Locally the construction is transparent. If $\mathcal X=[X/G]$, a central subgroup $H\subseteq G$ acts trivially on $X$, and the flat quotient $G/H$ exists, then

$$
[X/G]\mathbin{\!\sslash\!}H\simeq[X/(G/H)].
$$

Indeed, both sides have the same local $X$-objects and changes of frame differing by $H$ become equal. These local identifications glue by uniqueness. Consequently rigidification preserves algebraicity in the finite-flat and smooth-affine cases used here.

### 7.2 Finite group quotients

Let a finite locally free group scheme $G$ act on a quasi-projective scheme $X$ over $S_0$. The fppf sheaf quotient is represented by a scheme $Y=X/G$, and $X\to Y$ is finite and surjective.

**Proof strategy.** First work on a $G$-stable affine open. Quasi-projectivity supplies such neighborhoods. Locally on the base, every finite orbit lies in an affine nonvanishing locus of a sufficiently high ample power. Remove the finite image of the complement of that locus under $G\times X\to X$; the remaining neighborhood is invariant. It is affine because it is obtained from finitely controlled affine intersections in the separated quasi-projective scheme. Equivalently, the norm of the pullback of the ample bundle along the finite locally free projection $G\times X\to X$ gives an invariant ample power and invariant affine nonvanishing loci.

If $X=\operatorname{Spec}A$, define $A^G$ as the equalizer of the coaction $A\rightrightarrows A\otimes\mathcal O(G)$. The finite-action integrality lemma says that $A$ is integral over $A^G$. Its proof applies Cayley--Hamilton to the finite locally free coaction module: the characteristic coefficients of the orbit operator are invariant, and the characteristic polynomial annihilates each $a\in A$. Finite presentation then makes $A$ finite over $A^G$. Thus $\operatorname{Spec}A\to\operatorname{Spec}A^G$ is finite and has the invariant-map universal property. The affine quotients agree on invariant overlaps and glue. Book 13 supplies the effective gluing. $\square$

Over an algebraically closed field, $Y(k)$ is the set of $G(k)$-orbits when $G$ is a constant finite group. For a nonreduced finite group scheme, geometric points alone do not see the infinitesimal action; the sheaf quotient remains the correct statement.

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

A quasi-coherent sheaf $\mathcal F$ on a tame stack descends through $\pi$ precisely when every geometric stabilizer acts trivially on its fibers; locally on $[X/G]$, equivariant descent to $X/G$ then follows by taking invariants and using exactness. Without trivial stabilizer action, no sheaf downstairs can pull back to $\mathcal F$, because a pulled-back sheaf has trivial inertia action.

## 8. Generalized elliptic curves

### 8.1 The boundary object

A smooth elliptic curve cannot specialize within the category of elliptic curves when its discriminant tends to zero. The correct compact boundary is a polygon, not a cusp. A **Neron $n$-gon** over an algebraically closed field is a cycle of $n$ copies of $\mathbf P^1$, with $\infty$ on one copy glued to $0$ on the next. Its smooth locus is

$$
\mathbf G_m\times\mathbf Z/n\mathbf Z,
$$

and translation rotates components and multiplies the $\mathbf G_m$ coordinate.

A **generalized elliptic curve** over $S$ is a proper flat finitely presented curve $E\to S$ with a section $e$ in the smooth locus, together with a commutative group law on $E^{\mathrm{sm}}$ and an action

$$
E^{\mathrm{sm}}\times_SE\longrightarrow E
$$

extending translation, such that every geometric fiber is either a smooth connected genus-one curve or a Neron polygon, and translation by the smooth group acts transitively on the components of each singular fiber.

The action is part of the definition. A cycle of projective lines with a marked smooth point does not by itself determine the required group structure in families. The transitivity condition rules out irrelevant components invisible to the group.

### 8.2 The stack property and diagonal

Generalized elliptic curves form an fpqc stack. Descend the proper flat curve, the section, the smooth open, the group law, and the action as in Book 13. Group identities are equalities of maps. Smoothness of the indicated open and the geometric polygon condition are reflected after faithfully flat field extension. The transitive action on components can be checked on geometric fibers. This proves effectivity; descent of isomorphisms proves the prestack condition.

The diagonal is representable and separated. Given $E,E'$ over $T$, choose an invariant effective Cartier divisor meeting every component, for instance the orbit of a sufficiently divisible multiple of the identity after an fppf cover. Its associated line bundle is relatively ample. A common high power embeds both curves. The scheme of projective transformations carrying the embedded curve, identity, multiplication, and action to their counterparts represents $\underline{\operatorname{Isom}}(E,E')$. Preservation is closed and invertibility is open.

For a fixed bound on the number of geometric components, the diagonal is finite. Fiberwise, an automorphism preserving the identity and group action is determined on the dense smooth locus and belongs to a finite group; the projective embedding makes the isomorphism scheme affine, while properness follows from extension across the nodal boundary. Proper and quasi-finite is finite. The component bound supplies quasi-compactness. Without it, one must not infer one global finite-type assertion from all individual polygons.

### 8.3 Weierstrass charts and contraction

The line bundle $\mathcal O_E(3e)$ embeds a smooth elliptic curve as a cubic. For a polygon, a positive divisor must meet every component, so one first contracts the components disjoint from the chosen degree-three divisor. The result is a stable cubic with a smooth marked identity and fibers either smooth or nodal.

Locally on the base, a framed stable cubic has a Weierstrass equation

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6.
$$

Admissible coordinate changes are

$$
x=u^2x'+r,qquad
y=u^3y'+u^2sx'+t,qquad u\in\mathbf G_m.
$$

Let $W$ be the open in the affine coefficient space where every geometric cubic is smooth or nodal and the marked point at infinity is smooth. Let $G_W$ be the smooth affine group of these coordinate changes. Then the stack of framed stable Weierstrass cubics is $[W/G_W]$. The atlas $W\to[W/G_W]$ is smooth.

An arbitrary polygon is not recovered from its contraction alone: contraction forgets how many components were inserted. Level structure or an explicit component marking supplies the missing finite data. This is why one cannot prove algebraicity of every boundary problem merely by writing one Weierstrass equation.

### 8.4 Algebraicity and bounded boundary

Fix $m\geq1$ and let $\mathcal E\!ll_{\leq m}$ be the full bounded substack in which singular geometric fibers have at most $m$ components. The contraction to a stable cubic, together with the finite data describing the cyclic component cover and its gluing, is represented over the Weierstrass chart by a finite-presentation parameter scheme. The component incidence equations are closed; the Neron condition and transitivity are open. Book 8 supplies the finite Hilbert loci and Book 13 glues them after changing the Weierstrass frame.

Therefore $\mathcal E\!ll_{\leq m}$ is an algebraic stack with separated finite diagonal and a smooth scheme atlas. The union over $m$ is a locally algebraic stack, generally not quasi-compact. Modular level conditions below impose their own finite component bounds, so every compactified modular stack used later lies in one algebraic finite-type piece.

This conclusion is deliberately narrower than a claim that every genus-one degeneration is allowed. Cuspidal cubics, nonreduced fibers, and cycles with tails are excluded: their smooth loci and deformation behavior do not satisfy the generalized elliptic axioms.

## 9. Modular level structures

### 9.1 Drinfeld structures and ampleness

At primes dividing $N$, a list of $N$ distinct torsion sections is the wrong definition of level. Sections can collide in the special fiber while their sum still defines the correct finite flat subgroup divisor. Let $G$ be a finite locally free commutative group scheme and $H$ a constant finite abelian group. A **Drinfeld $H$-structure** is a homomorphism $\alpha:H\to G(T)$ for which

$$
\sum_{h\in H}[\alpha(h)]
$$

is the full subgroup divisor of the prescribed rank. Equality is equality of effective Cartier divisors, so it is stable under base change and meaningful in bad characteristic.

On a generalized elliptic curve a level divisor must also be **ample**: it must meet every irreducible component of every geometric fiber. On a polygon, a divisor supported on the identity component is finite flat but cannot control the other components and gives no projective embedding of the whole curve. The ampleness clause is what makes level compactification finite and prevents invisible components.

When $N$ is invertible, the torsion is etale and a Drinfeld basis is an ordinary basis on geometric fibers. Thus the integral definition specializes to the familiar one without having been defined by that generic behavior.

### 9.2 Full, point, and cyclic level

A full $\Gamma(N)$-structure is a pair $(P,Q)$ defining a Drinfeld structure

$$
(\mathbf Z/N\mathbf Z)^2\longrightarrow E^{\mathrm{sm}}[N]
$$

whose associated orbit divisor is ample. If a primitive $N$th root and a symplectic convention are fixed, one may additionally require the Weil pairing of $P,Q$ to equal that root.

A $\Gamma_1(N)$-structure is a Drinfeld homomorphism $\mathbf Z/N\mathbf Z\to E^{\mathrm{sm}}[N]$, written $1\mapsto P$, with ample divisor $\sum_a[aP]$. A $\Gamma_0(N)$-structure is a finite locally free cyclic subgroup $C\subset E^{\mathrm{sm}}$ of rank $N$, locally generated by a Drinfeld point, with $\sum_{c\in C}[c]$ ample.

The local-generation phrase for $\Gamma_0(N)$ is necessary. A finite flat group scheme may have no global generator. Requiring one would define a framed $\Gamma_1$-type cover rather than the cyclic subgroup problem.

These definitions are stable under pullback and have effective descent. The divisor equality, cyclicity after an fppf cover, and ampleness are all fppf local. Consequently each level problem is a stack and its forgetful map to generalized elliptic curves is representable and finite in the bounded compactified range. Over $\mathbf Z[1/N]$ it is etale over the smooth elliptic locus.

### 9.3 When level produces a fine scheme

An automorphism of a generalized elliptic curve preserving a full level basis acts trivially on the level divisor and on the component group it meets. For $N\geq3$, with $N$ invertible, it is the identity. On a smooth fiber, the polarization-preserving automorphism group is finite and its faithful action on $N$-torsion lies in a congruence subgroup. The elementary congruence lemma says that a finite-order integral matrix congruent to $1$ modulo $N\geq3$ is $1$: applying the binomial expansion at a prime divisor of the order and comparing the first nonzero $N$-adic term gives a contradiction. On a polygon, the ample basis determines every component and the dense smooth locus; identity there extends to the proper curve.

Thus full level $N\geq3$ kills inertia over $\mathbf Z[1/N]$. The stack is then a sheaf. Its finite map to an algebraic stack and its local quasi-projective parameter construction show that it is represented by a scheme. It is a fine moduli scheme and carries the universal generalized elliptic curve.

Smaller or weaker levels require a stabilizer check. Full level $2$ is preserved by $[-1]$ because $-P=P$ on $2$-torsion. A $\Gamma_1(N)$ point may leave special automorphisms at small $N$, and a cyclic subgroup is preserved by $[-1]$ for every $N$. Hence a $\Gamma_0(N)$ problem is normally a stack even for large $N$ unless an auxiliary rigid level is added.

### 9.4 Compactified modular stacks and coarse curves

Write $\overline{\mathcal M}(\Gamma)$ for the stack of generalized elliptic curves with an ample level structure of type $\Gamma$. The level divisor bounds the number of polygon components by its degree, so Chapter 8 makes this an algebraic stack of finite presentation with finite diagonal. Its open substack $\mathcal M(\Gamma)$ classifies smooth elliptic curves.

Choose an auxiliary full level $M\geq3$, invert $M$, and impose it in addition to $\Gamma$. The resulting fine scheme $X(\Gamma\cap\Gamma(M))$ is finite over $\overline{\mathcal M}(\Gamma)$ and carries an action of the finite change-of-basis group. Locally the original stack is the corresponding finite quotient stack. The finite quotient theorem therefore constructs a coarse modular curve

$$
\overline{\mathcal M}(\Gamma)\longrightarrow X(\Gamma).
$$

This construction is independent of the auxiliary level: both candidates satisfy the same categorical coarse universal property. Over a tame base, formation of $X(\Gamma)$ commutes with arbitrary base change and sheaves with trivial stabilizer action descend. At primes dividing residual stabilizer orders, only flat base change is automatic.

The universal generalized elliptic curve lives on the stack. It descends to the coarse curve only where inertia acts trivially on it, which is generally false. In contrast, suitable powers of the Hodge line can descend once every stabilizer acts trivially on their fibers.

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

It says that the adjoint involution induced by the polarization restricts to the prescribed involution on $B$. It is an equality of homomorphisms and therefore descends.

For integral descent, a polarization may be encoded either by the homomorphism together with the condition of being induced by a relatively ample rigidified line bundle, or by such a line bundle itself. Positivity is never defined merely fiberwise by a sign. The fixed kernel type is a finite locally free subgroup condition and includes separability only when its rank is invertible.

An isomorphism $f:(A,\iota,\lambda,\eta K)\to(A',\iota',\lambda',\eta'K)$ satisfies

$$
f\iota(b)=\iota'(b)f,qquad
f^\vee\lambda'f=\lambda,qquad
f(\eta K)=\eta'K.
$$

If the moduli problem allows polarizations up to a specified similitude group, replace the middle equality by equality up to that multiplier; the multiplier is part of the arrow and not silently forgotten.

### 10.3 The determinant condition

The action of $\mathcal O$ on $A$ differentiates to an action on the locally free sheaf $\operatorname{Lie}(A)$. The rational PEL datum prescribes a polynomial $P_b(T)\in R[T]$ for each $b\in\mathcal O$. The **determinant condition** is

$$
\det\bigl(T-\iota(b)\mid\operatorname{Lie}(A)\bigr)=P_b(T).
$$

It suffices to impose this on finitely many generators of $\mathcal O$ together with the polynomial identities expressing the datum. The coefficients are polynomial functions of matrices on a finite locally free sheaf, so the condition is closed and commutes with base change.

This condition controls the infinitesimal Hodge type, not merely the total dimension. Without it an $\mathcal O$-action can distribute its embeddings incorrectly among tangent directions. In ramified residue characteristic the determinant condition alone need not produce the desired flat integral model; wedge, spin, or local-model conditions may be needed. Those are additional closed conditions attached to a chosen integral datum. We make no claim that the naive determinant locus is flat at every bad prime.

### 10.4 Prime-to-the-base level structures

For an integer $N$ invertible on $S$, a full level structure is an $\mathcal O$-linear similitude

$$
\eta_N:\Lambda/N\Lambda\xrightarrow{\sim}A[N]
$$

carrying $\psi$ to the Weil pairing up to the prescribed multiplier. More generally, a $K$-level structure is a $K$-orbit of compatible prime-to-bad-prime trivializations. The orbit formulation prevents a basis choice from being mistaken for intrinsic structure.

When the level order is not invertible, one must specify finite flat subgroup schemes and integral pairing conditions rather than geometric bases. Such parahoric level problems depend on a lattice chain and local model. The abstract stack and descent arguments still apply, but etaleness and smoothness do not follow from the prime-to-level proof.

A level is **neat** if no nontrivial finite-order automorphism compatible with the rational tensors fixes it. A principal level $N\geq3$ is the standard sufficient example in the symplectic cases considered here. Neatness is the exact property used to remove inertia.

### 10.5 Stack, diagonal, and atlas theorems

**PEL stack theorem.** For fixed integral PEL data, fixed polarization type, determinant condition, and finite-presentation level condition, PEL objects form an fpqc stack. Its diagonal is representable, separated, and finite. After restricting to a locus on which the prescribed deformation conditions admit the framed parameter chart, it is an algebraic stack of finite presentation. Over a good-prime locus with the standard smooth local model, it has a smooth atlas. After adding neat prime-to-base level, its inertia is trivial and it is represented by a quasi-projective scheme.

**Proof.** Book 13 descends the abelian scheme, group law, endomorphisms, rigidified polarization, and finite level data. The determinant and Rosati conditions descend as equations; ampleness descends by Book 8. This proves the stack assertion.

For the diagonal, a polarization-preserving isomorphism belongs to the finite automorphism scheme of a polarized abelian scheme. Commuting with $\mathcal O$ and preserving level cut out closed subgroups or closed translates. Hence the diagonal is finite and separated.

Choose a sufficiently high power of a line bundle representing a fixed multiple of the polarization. Book 8 gives projective embeddings and the required Hilbert parameter scheme in the range at hand. Endomorphism graphs, the group law, Rosati compatibility, and determinant equations define locally closed loci. Frames form a general-linear torsor, so the framed-parameter theorem gives algebraicity. Smoothness is asserted only where the corresponding parameter or local-model morphism is known smooth; it is not inferred from algebraicity.

Finally, a neat level forces every stabilizer to be trivial. The stack is then a sheaf; the quasi-projective framed quotient descends to a scheme by the descent results of Book 13. $\square$

The theorem separates three issues that are often conflated: descent proves stackhood, a parameter presentation proves algebraicity, and deformation or local-model calculations prove smoothness.

## 11. Hilbert moduli problems

### 11.1 Real multiplication and polarization modules

Let $F$ be a totally real field of degree $d$, with ring of integers $\mathcal O_F$. A Hilbert abelian scheme over $S$ is an abelian scheme $A/S$ of relative dimension $d$ with an embedding

$$
\iota:\mathcal O_F\hookrightarrow\operatorname{End}_S(A).
$$

A single principal polarization is often too restrictive and is not stable under all ideal-class operations. The intrinsic datum is the module of symmetric $\mathcal O_F$-linear homomorphisms

$$
\mathcal P(A)=
\operatorname{Hom}_{\mathcal O_F}^{\mathrm{sym}}(A,A^\vee),
$$

with its positive cone of polarizations. Fix a fractional ideal $\mathfrak c$ and its totally positive cone $\mathfrak c^+$. A **$\mathfrak c$-polarization** is an isomorphism of ordered invertible $\mathcal O_F$-modules

$$
\lambda:\mathfrak c\xrightarrow{\sim}\mathcal P(A)
$$

that carries $\mathfrak c^+$ to polarizations and for which the induced map

$$
A\otimes_{\mathcal O_F}\mathfrak c\longrightarrow A^\vee
$$

has the prescribed isomorphism or finite-kernel type. The tensor product is the abelian scheme obtained by the finite-projective Serre tensor construction.

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
- over the unramified good-level locus, the standard framed charts are smooth;
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

The determinant condition is closed. The condition that the alternating form induced by the polarization be perfect on the chosen prime-to-bad-prime Tate module is open-and-closed once its finite kernel type is fixed. At a ramified prime, the correct integral model may additionally impose a lattice-chain, wedge, or local-model condition. These are finite-presentation tensor or rank conditions, so they preserve the stack proof, but smoothness must be decided for that particular local model.

### 12.3 The resulting stack and its quotients

Let $\mathcal Q_K$ denote the exact quaternionic PEL stack just specified. Effective descent follows in the order

$$
A\ ;\quad \iota\ ;\quad \lambda\ ;\quad
\text{determinant and local-model conditions}\ ;\quad \eta K.
$$

The order matters only logically: the later conditions are statements about structures already descended. The diagonal is the closed subgroup of polarization-preserving automorphisms commuting with $\mathcal O_B$ and fixing the level, hence is finite.

On a good-prime locus, framed polarized embeddings give a smooth atlas and $\mathcal Q_K$ is algebraic of finite presentation. If $K'$ is neat and normal in $K$, the fine scheme $Q_{K'}$ carries the finite action of $K/K'$ and

$$
\mathcal Q_K\simeq[Q_{K'}/(K/K')].
$$

The quotient scheme is coarse. Fixed points of the finite action do not disappear: they become inertia in the quotient stack and quotient singularities in the coarse space.

In the compact Shimura-curve case no cusps are added, because the quaternion algebra prevents the relevant rational parabolic subgroups. This geometric properness is different from stack separatedness. The latter follows from the finite diagonal; the former is a property of the structural morphism and requires the global quaternionic hypothesis.

## 13. Unitary moduli problems

### 13.1 CM actions and signatures

Let $F$ be totally real, let $E/F$ be a CM extension, and let complex conjugation be $a\mapsto\bar a$. Fix an $E$-vector space of rank $n$ with a hermitian form and signatures

$$
(r_\tau,s_\tau),\qquad r_\tau+s_\tau=n,
$$

for the real embeddings $\tau:F\hookrightarrow\mathbf R$. The reflex field is generated by this signature data.

A unitary object is an abelian scheme $A$ of relative dimension $n[F:\mathbf Q]$ with $\mathcal O_E$-action, a polarization whose Rosati involution induces complex conjugation, and a level orbit. Its determinant condition is

$$
\det\bigl(T-\iota(a)\mid\operatorname{Lie}(A)\bigr)
=\prod_\tau
(T-\tau(a))^{r_\tau}
(T-\bar\tau(a))^{s_\tau},
$$

interpreted over the reflex base. The formula is shorthand for the universal polynomial whose coefficients lie in that base; it does not require every embedding to be individually defined there.

The signature belongs in the moduli definition. An $\mathcal O_E$-action plus total dimension cannot distinguish, for example, signature $(n,0)$ from $(n-1,1)$, although their moduli spaces have entirely different dimensions.

### 13.2 Hermitian polarizations

The polarization satisfies

$$
\lambda\iota(a)=\iota(\bar a)^\vee\lambda.
$$

On prime-to-bad-prime torsion, the alternating Weil pairing and the CM action combine into the prescribed hermitian similitude class. A level trivialization must preserve this class, not merely the underlying module.

Fixing the kernel of $\lambda$ is essential in integral families. “Principal” means that $\lambda$ is an isomorphism, while a polarization of degree $d$ has finite locally free kernel of rank $d$ under the degree convention. At primes dividing $d$, that kernel need not be etale. Isotropy and self-duality are conditions on finite flat subgroup schemes or lattice chains.

At a ramified prime of $E/F$, the determinant condition may again be too large. A wedge or spin condition selects the desired closure of the generic fiber in several standard signatures. The stack framework treats the chosen condition as part of the integral datum; it does not claim that all such choices coincide.

### 13.3 Level, inertia, and coarse spaces

Let $\mathcal U_K$ be the unitary PEL stack for fixed signature, polarization kernel, integral local conditions, and level. The common theorem gives stackhood, finite separated diagonal, and an algebraic finite-presentation atlas. On good unramified loci with the standard local model the atlas is smooth. A neat prime-to-base level kills the finite group of tensor-preserving polarized automorphisms and gives a fine quasi-projective scheme $U_{K'}$.

For normal neat $K'\subset K$,

$$
\mathcal U_K\simeq[U_{K'}/(K/K')],
\qquad
U_K^{\mathrm{coarse}}=U_{K'}/(K/K').
$$

This description proves the required atlas and coarse statements: $U_{K'}\to\mathcal U_K$ is finite etale where the finite change-of-level group is etale, and finite flat in the corresponding integral torsor setting. It also computes inertia as the stabilizer of the level-change action.

The universal abelian scheme and its $\mathcal O_E$-action exist on $\mathcal U_K$. On the coarse space, only constructions with trivial stabilizer action descend. In particular, the determinant of the Hodge bundle may descend even when the Hodge bundle itself does not, after taking a power divisible by the exponent of all stabilizer characters on the tame locus.

## 14. Coarse descent and synthesis

### 14.1 Descending constructions through a coarse map

Let $\pi:\mathcal X\to M$ be one of the finite-quotient coarse maps constructed above. There are three distinct descent questions.

First, a morphism $\mathcal X\to Z$ to an algebraic space always descends uniquely, by the defining universal property of $M$. Hecke maps defined between stacks therefore induce maps between coarse spaces once source and target levels are matched.

Second, a line bundle $\mathcal L$ descends only if inertia acts trivially on every fiber. Necessity is immediate because a pullback from $M$ has trivial stabilizer action. On a tame quotient chart $[X/G]$, sufficiency follows from exact invariants: the equivariant module of sections has invariant descent data, and the adjunction from the quotient pullback is an isomorphism after the finite cover. The local descended bundles glue uniquely.

Third, a family of curves or abelian schemes almost never descends merely because its isomorphism class defines the coarse point. Descent would require coherent identifications along the finite relation, and stabilizers would have to act trivially on the family. The universal object therefore belongs naturally to the stack.

These distinctions explain a standard phenomenon. Modular forms, viewed as sections of powers of the Hodge line, can often be interpreted on a coarse modular curve after taking a suitable power, even though the universal elliptic curve cannot.

### 14.2 A comparison table

| Object | Values over $T$ | Automorphisms retained? | Local geometric chart? | Universal family? |
|---|---|---:|---:|---:|
| Isomorphism-class presheaf | sets | no | not implied | not implied |
| Moduli sheaf | sets | no | not implied | only if represented finely |
| Moduli stack | groupoids | yes | not implied | yes, tautologically on the stack |
| Algebraic moduli stack | groupoids | yes | smooth scheme atlas | yes |
| Coarse space | sets of geometric orbits | no | an algebraic space or scheme here | generally no |
| Fine moduli scheme | discrete groupoids | necessarily trivial | identity atlas | yes |

The table is not a hierarchy in which every move rightward improves the object. Passing from a stack to a coarse space deliberately forgets information. Passing from a stack to a fine scheme is possible only after level or another rigidification has removed inertia.

### 14.3 The reusable theorem package

The constructions of this book yield the following precise results for later modular and PEL geometry.

- Categories fibered in groupoids encode pullback intrinsically; chosen pullbacks form a coherent contravariant pseudofunctor because cartesian lifts are unique up to unique isomorphism.
- A prestack has descent for isomorphisms. A stack also has effective descent for objects. Generalized elliptic and fixed PEL data are fpqc stacks by the effective descent results of Book 13.
- Two-fiber products retain the comparison isomorphism. The diagonal represents isomorphisms, and inertia represents automorphisms.
- A representable morphism may be tested after every scheme base change. Finite, smooth, etale, and proper have this meaning for stack morphisms.
- A stack with representable diagonal and a smooth surjective scheme atlas is algebraic. Framing a sufficiently positive projective embedding produces the atlases needed here from the parameter spaces of Book 8.
- For a smooth affine group acting on a separated scheme, the quotient stack has its canonical smooth atlas and representable diagonal. For a finite locally free group, that atlas is finite flat.
- A compatible central flat subgroup of inertia can be rigidified; locally $[X/G]\sslash H=[X/(G/H)]$ when $H$ acts trivially.
- A finite locally free group acting on a quasi-projective scheme has a finite scheme quotient. The quotient-stack map to that scheme is coarse. Flat base change is safe; arbitrary base change and exact sheaf descent require linear reductivity.
- Generalized elliptic curves with bounded polygonal boundary form algebraic stacks with finite diagonal. Ample Drinfeld level bounds the boundary. Full invertible level $N\geq3$ kills inertia and yields a fine scheme.
- Hilbert, quaternionic, and unitary PEL objects are defined by an exact order action, Rosati-compatible polarization, determinant or stated integral local-model condition, and level orbit. Their stacks have finite diagonal and explicit framed atlases. Neat level produces fine quasi-projective schemes; removing it gives finite quotient stacks and coarse spaces.

Every conclusion retains its hypothesis. Good-prime smoothness is not asserted at a ramified local model. A determinant condition is not substituted for a stronger integral condition where they differ. Finite is not silently strengthened to finite etale. A coarse space is never treated as though it carried the universal family.

### 14.4 Conclusion

Moduli geometry begins where classification by points stops. A family must pull back coherently, its isomorphisms must glue, and its local presentations must remember the symmetries used in gluing. Categories fibered in groupoids express pullback; stacks express descent; diagonals and inertia isolate isomorphisms and automorphisms; atlases return the problem to schemes without discarding either.

For modular problems, generalized elliptic curves add exactly the polygonal boundary compatible with the group law, while ample Drinfeld structures control that boundary integrally. For PEL problems, the order action, polarization, determinant condition, and level orbit make the Hodge type and integral structure explicit. In both settings, sufficiently rigid level gives a fine scheme. Removing that auxiliary rigidity produces a finite quotient stack, and invariant theory produces its coarse space.

The resulting picture is stable under descent and honest about its losses. The stack carries the universal geometry and its stabilizers. The fine cover supplies coordinates and projective parameter spaces. The coarse space records geometric orbits and receives descended constructions only when inertia permits them. Keeping these three objects distinct is the foundation on which modular curves, Shimura varieties, their compactifications, and their arithmetic correspondences can be built.
