# Shimura Data and Canonical Models in the FLT Cases

## Contents

1. [The bridge from real domains to arithmetic varieties](#1-the-bridge-from-real-domains-to-arithmetic-varieties)
   - [The organizing problem](#11-the-organizing-problem)
   - [Standing conventions](#12-standing-conventions)
   - [The three families](#13-the-three-families)
   - [What canonical means](#14-what-canonical-means)
2. [The Deligne torus and Hodge structures](#2-the-deligne-torus-and-hodge-structures)
   - [The real torus that records conjugation](#21-the-real-torus-that-records-conjugation)
   - [Representations and Hodge bidegrees](#22-representations-and-hodge-bidegrees)
   - [The Hodge cocharacter and weight](#23-the-hodge-cocharacter-and-weight)
   - [Polarized weight one](#24-polarized-weight-one)
3. [Shimura data](#3-shimura-data)
   - [The axioms and why they are necessary](#31-the-axioms-and-why-they-are-necessary)
   - [Hermitian symmetric domains](#32-hermitian-symmetric-domains)
   - [Morphisms, products, and central changes](#33-morphisms-products-and-central-changes)
   - [Failure tests](#34-failure-tests)
4. [Reflex fields](#4-reflex-fields)
   - [The conjugacy class of the Hodge cocharacter](#41-the-conjugacy-class-of-the-hodge-cocharacter)
   - [Field of definition and stabilizers](#42-field-of-definition-and-stabilizers)
   - [Products and morphisms](#43-products-and-morphisms)
   - [Computing by labelled embeddings](#44-computing-by-labelled-embeddings)
5. [Adelic quotients and finite level](#5-adelic-quotients-and-finite-level)
   - [The double quotient](#51-the-double-quotient)
   - [Arithmetic stabilizers](#52-arithmetic-stabilizers)
   - [Neat compact opens](#53-neat-compact-opens)
   - [Changing level and Hecke maps](#54-changing-level-and-hecke-maps)
6. [Connected components](#6-connected-components)
   - [From a domain component to an adelic quotient](#61-from-a-domain-component-to-an-adelic-quotient)
   - [The abelianization principle](#62-the-abelianization-principle)
   - [Galois action on components](#63-galois-action-on-components)
   - [A warning about geometric connectedness](#64-a-warning-about-geometric-connectedness)
7. [Hilbert modular data](#7-hilbert-modular-data)
   - [The group and its domain](#71-the-group-and-its-domain)
   - [Verification of the axioms](#72-verification-of-the-axioms)
   - [Reflex field and components](#73-reflex-field-and-components)
   - [Special points and reciprocity](#74-special-points-and-reciprocity)
8. [Quaternionic data](#8-quaternionic-data)
   - [Real ramification selects the domain](#81-real-ramification-selects-the-domain)
   - [Verification and dimension](#82-verification-and-dimension)
   - [Reflex field](#83-reflex-field)
   - [Components and the curve case](#84-components-and-the-curve-case)
   - [CM tori in a quaternion algebra](#85-cm-tori-in-a-quaternion-algebra)
9. [Unitary data](#9-unitary-data)
   - [Hermitian spaces and similitudes](#91-hermitian-spaces-and-similitudes)
   - [Signatures and the Hodge map](#92-signatures-and-the-hodge-map)
   - [Axiom verification and reflex field](#93-axiom-verification-and-reflex-field)
   - [Components and compact surfaces](#94-components-and-compact-surfaces)
10. [Reciprocity morphisms](#10-reciprocity-morphisms)
    - [The toric construction](#101-the-toric-construction)
    - [Special-point reciprocity](#102-special-point-reciprocity)
    - [Variance and normalization](#103-variance-and-normalization)
    - [Passage to components](#104-passage-to-components)
11. [Canonical models](#11-canonical-models)
    - [Definition by arithmetic special points](#111-definition-by-arithmetic-special-points)
    - [Uniqueness](#112-uniqueness)
    - [Existence in the three families](#113-existence-in-the-three-families)
    - [Effective descent](#114-effective-descent)
12. [Level descent and functoriality](#12-level-descent-and-functoriality)
    - [The tower over the reflex field](#121-the-tower-over-the-reflex-field)
    - [Finite quotients and non-neat level](#122-finite-quotients-and-non-neat-level)
    - [Morphisms and Hecke translations](#123-morphisms-and-hecke-translations)
    - [Descent of connected components](#124-descent-of-connected-components)
13. [The FLT package](#13-the-flt-package)
    - [Curves, surfaces, and the parity split](#131-curves-surfaces-and-the-parity-split)
    - [A reusable canonical-model theorem](#132-a-reusable-canonical-model-theorem)
    - [Hypothesis ledger](#133-hypothesis-ledger)
    - [Conclusion](#134-conclusion)

## 1. The bridge from real domains to arithmetic varieties

Shimura varieties begin with an apparently analytic object: a conjugacy class of homomorphisms from a real torus into a reductive group. Their arithmetic force comes from a second fact. The resulting quotient has a preferred field of definition, and Galois acts on its special points through class field theory. This book builds that bridge for the Hilbert, quaternionic, and unitary data that occur in the geometric route to Fermat's Last Theorem.

### 1.1 The organizing problem

Let $G$ be a connected reductive group over $\mathbf Q$. A symmetric domain for $G(\mathbf R)$ alone does not remember a number field, and an adelic double quotient alone does not say which complex structures its points carry. A Shimura datum joins the two. It selects homomorphisms

$$
h:\mathbb S\longrightarrow G_{\mathbf R}
$$

whose adjoint action has exactly the infinitesimal types needed for a Hermitian domain. Here $\mathbb S=\operatorname{Res}_{\mathbf C/\mathbf R}\mathbf G_m$ is the Deligne torus. The $G(\mathbf R)$-conjugacy class $X$ of $h$ becomes a finite union of Hermitian symmetric domains.

Finite adelic coordinates then record integral structures and level. For a compact open subgroup $K\subset G(\mathbf A_f)$ the complex points are

$$
\operatorname{Sh}_K(G,X)(\mathbf C)
=G(\mathbf Q)\backslash\bigl(X\times G(\mathbf A_f)/K\bigr),       \tag{1.1}
$$

with $q\in G(\mathbf Q)$ acting by $(x,gK)\mapsto(qx,qgK)$. This convention will remain fixed. It is compatible with the left multiplication formula for complex multiplication reciprocity established in Book 125.

Three questions govern the book.

First, why do the chosen real homomorphisms satisfy the Shimura axioms? This requires an explicit calculation on every split and compact real factor; a slogan about upper half-planes is not enough.

Second, which number field is intrinsic to the datum? The answer is the reflex field, obtained from the Galois orbit of the Hodge cocharacter. Its computation is especially transparent when embeddings of a totally real or CM field label the real factors.

Third, how does one descend (1.1) from $\mathbf C$ to that field? The normalization is fixed on special points by the main theorem of complex multiplication. Neat level removes stabilizers, density gives uniqueness, and effective Galois descent produces the model.

### 1.2 Standing conventions

All algebraic groups are affine of finite type. The symbol $G^{\mathrm{der}}$ denotes the derived group, $G^{\mathrm{ad}}=G/Z(G)$ the adjoint quotient, and

$$
G^{\mathrm{ab}}=G/G^{\mathrm{der}}
$$

the maximal torus quotient. For a real algebraic group $H$, $H(\mathbf R)^+$ is the identity component. We fix an algebraic closure $\overline{\mathbf Q}\subset\mathbf C$.

Arithmetic Artin reciprocity is used throughout:

$$
\operatorname{Art}_E:\mathbf A_E^\times/E^\times\longrightarrow
\operatorname{Gal}(E^{\mathrm{ab}}/E),                              \tag{1.2}
$$

and a uniformizer maps to arithmetic Frobenius. Only the finite part of an idele enters the displayed adelic translation. For the CM reflex field of a special point the archimedean group is connected, so no sign choice occurs. For an ambient reflex field with real places, however, we first choose an equivalent idele whose real components are positive. Two such representatives differ, on their finite parts, by a totally positive principal element and a connected archimedean element. This normalization is essential for narrow component quotients and is compatible with the conventions of Books 4 and 125.

If $h:\mathbb S\to G_{\mathbf R}$, then after identifying

$$
\mathbb S_{\mathbf C}\simeq\mathbf G_{m,\mathbf C}\times
\mathbf G_{m,\mathbf C},
$$

we define

$$
\mu_h(z)=h_{\mathbf C}(z,1).                                        \tag{1.3}
$$

Changing (1.3) to $h_{\mathbf C}(1,z)$ conjugates the cocharacter and can conjugate the embedded reflex field. We never make that change silently.

A **special point** is a point represented by $h\in X$ whose Mumford--Tate group is a torus. The reflex field of that toric datum will be denoted $E(h)$; it contains the reflex field $E(G,X)$ after the chosen embeddings are fixed.

### 1.3 The three families

Let $F$ be totally real of degree $d$.

The Hilbert family uses $\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_2$. Every real embedding contributes a copy of the upper or lower half-plane. Its domain has dimension $d$ and its reflex field is $\mathbf Q$.

The quaternionic family starts with a quaternion algebra $B/F$. Only the real places at which $B$ splits contribute noncompact factors. If $B$ splits at $r$ real places, the domain has dimension $r$. The curve case is $r=1$. The reflex field is the fixed field of the automorphisms of $\overline{\mathbf Q}$ preserving the labelled set of split places.

The unitary family starts with a CM extension $K/F$ and a two-dimensional Hermitian $K$-space. A real place of signature $(1,1)$ contributes a complex one-ball, while signatures $(2,0)$ and $(0,2)$ contribute points. Two indefinite places give the compact surfaces used when degree parity prevents the desired representation from occurring in curve cohomology. The reflex field remembers the full signature function, including the difference between $(2,0)$ and $(0,2)$.

The words Hilbert, quaternionic, and unitary describe the rational group. They do not by themselves specify a Shimura datum. The set of noncompact embeddings, the orientation at those embeddings, the central weight, and the level are part of the data.

### 1.4 What canonical means

A variety over some number field whose complex points happen to be (1.1) is not yet canonical. Canonicality fixes the Galois action on every special point. If $x=[h,g]$ and $s\in\mathbf A_{E(h)}^\times$, then the required rule is

$$
x^{\operatorname{Art}_{E(h)}(s)}
=[h,r_h(s_f)g],                                                       \tag{1.4}
$$

where $r_h$ is the reciprocity morphism associated with the toric Hodge cocharacter. Formula (1.4) simultaneously fixes the field, the Artin normalization, and the side on which the adelic element acts.

Book 124 constructed reflex norms from cocharacters. Book 125 proved that their adelic action equals Galois conjugation on CM abelian varieties, with the inverse already built into the lattice action. We use that theorem rather than re-prove CM reciprocity. What must be proved here is that the ambient Shimura data are correct, that (1.4) descends their analytic quotients, and that the result is independent of auxiliary symplectic realizations.

## 2. The Deligne torus and Hodge structures

The source $\mathbb S$ packages a complex vector space together with its conjugate. Understanding its characters removes much of the mystery from the Shimura axioms: those axioms are simply restrictions on the bidegrees occurring in the adjoint Hodge structure.

### 2.1 The real torus that records conjugation

For a real algebra $R$,

$$
\mathbb S(R)=(\mathbf C\otimes_{\mathbf R}R)^\times.
$$

Thus $\mathbb S(\mathbf R)=\mathbf C^\times$. Over $\mathbf C$ there is a canonical splitting

$$
\mathbf C\otimes_{\mathbf R}\mathbf C\simeq\mathbf C\times\mathbf C,
\qquad z\otimes w\mapsto(zw,\bar z w),
$$

under which complex conjugation exchanges the two factors. Consequently

$$
X^*(\mathbb S_{\mathbf C})=\mathbf Z p\oplus\mathbf Z q,
$$

where $p(z_1,z_2)=z_1$ and $q(z_1,z_2)=z_2$, and conjugation interchanges $p$ and $q$.

Two real subtori will recur. The weight inclusion is

$$
w:\mathbf G_{m,\mathbf R}\longrightarrow\mathbb S,
\qquad t\longmapsto t,
$$

which becomes $t\mapsto(t,t)$ over $\mathbf C$. The norm is

$$
N:\mathbb S\longrightarrow\mathbf G_{m,\mathbf R},
\qquad z\longmapsto z\bar z.
$$

The compact quotient $\mathbb S/w(\mathbf G_m)$ has real points the circle. Its element $i$ will produce the Cartan involution in the Shimura axioms.

### 2.2 Representations and Hodge bidegrees

Let $V$ be a real vector space and $\rho:\mathbb S\to\operatorname{GL}(V)$ an algebraic representation. Since $\mathbb S_{\mathbf C}$ is split,

$$
V_{\mathbf C}=\bigoplus_{a,b\in\mathbf Z}V^{a,b},                   \tag{2.1}
$$

where $(z_1,z_2)$ acts on $V^{a,b}$ by $z_1^{-a}z_2^{-b}$. Complex conjugation sends $V^{a,b}$ to $V^{b,a}$. This is a real Hodge structure; it is pure of weight $n$ when $a+b=n$ for every nonzero summand.

The minus signs in the character are a convention suited to homology. For a complex abelian variety,

$$
H_1(A,\mathbf C)=H^{-1,0}\oplus H^{0,-1}.
$$

Equivalently, $\mu_h$ acts with weights $1$ and $0$ on the two summands. The adjoint representation has weight zero, so its only permitted types in a Shimura datum will be $(-1,1)$, $(0,0)$, and $(1,-1)$.

The decomposition (2.1) is functorial. Tensor products add bidegrees, duals negate them, and $\operatorname{End}(V)$ contains $\operatorname{Hom}(V^{a,b},V^{c,d})$ in type $(c-a,d-b)$. This last formula explains why a weight-one structure with two adjacent types produces precisely the three adjoint types.

### 2.3 The Hodge cocharacter and weight

For $h:\mathbb S\to G_{\mathbf R}$ define $\mu_h$ by (1.3) and

$$
w_h=h\circ w:\mathbf G_{m,\mathbf R}\longrightarrow G_{\mathbf R}. \tag{2.2}
$$

If the adjoint Hodge structure has weight zero, $w_h$ acts trivially on $\operatorname{Lie}G$, hence lands in $Z(G)_{\mathbf R}$. For connected reductive $G$, triviality of the adjoint action is exactly centrality. Thus the weight is forced to be central; it is not an independent decoration.

Complex conjugation on cocharacters gives

$$
\mu_h+\bar\mu_h=w_h                                                   \tag{2.3}
$$

in additive cocharacter notation. Formula (2.3) is the abstract source of the CM weight identity

$$
r_h(s)\overline{r_h(s)}=N_{E(h)/\mathbf Q}(s)
$$

after passage to a torus representation with scalar weight.

Conjugating $h$ by $g\in G(\mathbf R)$ conjugates $\mu_h$ by $g$. Hence a conjugacy class $X$ determines one $G(\mathbf C)$-conjugacy class of cocharacters. That class, rather than any chosen $h$, defines the reflex field.

### 2.4 Polarized weight one

Let $(V,\psi)$ be a rational symplectic space and let

$$
h:\mathbb S\longrightarrow\operatorname{GSp}(V,\psi)_{\mathbf R}
$$

give $V$ types $(-1,0)$ and $(0,-1)$. The form is a polarization when

$$
(x,y)_h=\psi(x,h(i)y)                                                  \tag{2.4}
$$

is symmetric positive definite after the consistent sign choice.

**Proposition 2.1.** A polarized weight-$-1$ homomorphism into $\operatorname{GSp}(V,\psi)$ induces a Shimura datum on its reductive stabilizer, provided no rational adjoint factor receives the trivial homomorphism.

**Proof strategy.** Compute the adjoint bidegrees inside $\operatorname{End}(V)$, then identify conjugation by $h(i)$ with the adjoint involution for the positive form (2.4).

**Proof.** The two types on $V$ differ by $(1,-1)$. Therefore $\operatorname{End}(V)$ has only types $(-1,1)$, $(0,0)$, and $(1,-1)$, and the same is true of every stable Lie subalgebra. The weight acts as one scalar on $V$, hence trivially by conjugation. Let $u^{\dagger_h}$ denote adjoint for the positive form (2.4). On the adjoint symplectic Lie algebra, a direct calculation with $J=h(i)$ gives

$$
\operatorname{Int}(h(i))(u)=-u^{\dagger_h}.                         \tag{2.5}
$$

Indeed, $J^{-1}=-J$, and substituting the symplectic adjoint identity in $(x,y)_h=\psi(x,Jy)$ yields (2.5), modulo the scalar similitude direction. The involution $u\mapsto-u^{\dagger_h}$ is the standard Cartan involution: the trace form $\operatorname{Tr}(uu^{\dagger_h})$ is positive definite. Since $h(i)$ lies in the reductive stabilizer, its Lie algebra is stable under this involution, whose restriction is therefore Cartan. The stated nontriviality condition is the remaining axiom. $\square$

Book 123 supplies the symplectic representations and positivity choices for the quaternionic groups used below. For unitary groups, the trace of the imaginary part of a Hermitian form supplies $\psi$. Proposition 2.1 will often reduce a matrix calculation to a transparent weight-one calculation.

## 3. Shimura data

The axioms are designed to do three jobs at once: restrict infinitesimal variation to one complex direction, force the real stabilizer to be maximal compact modulo center, and exclude rational factors that contribute nothing to the domain. We state them in a form that makes each job visible.

### 3.1 The axioms and why they are necessary

A **Shimura datum** is a pair $(G,X)$ consisting of a connected reductive group $G/\mathbf Q$ and a $G(\mathbf R)$-conjugacy class $X$ of homomorphisms $h:\mathbb S\to G_{\mathbf R}$ satisfying:

1. under $\operatorname{Ad}\circ h$, the complex Lie algebra $\mathfrak g_{\mathbf C}$ has only Hodge types

   $$
   (-1,1),\quad(0,0),\quad(1,-1);                                    \tag{3.1}
   $$

2. conjugation by $h(i)$ is a Cartan involution of $G_{\mathbf R}^{\mathrm{ad}}$;
3. no nontrivial $\mathbf Q$-simple factor of $G^{\mathrm{ad}}$ receives the trivial projection of $h$.

Some formulations also require the central weight $w_h$ to be defined over $\mathbf Q$. We do not build that extra condition into the term *Shimura datum*: the basic mixed quaternionic datum has a perfectly valid adjoint Shimura datum even when its central weight is not rational. Whenever a polarized weight-one realization is asserted below, rationality of its scalar weight is imposed separately and explicitly. This distinction is the reason central modifications occur in the FLT constructions.

An involution $\theta$ of a real reductive group is Cartan when its fixed subgroup is maximal compact, equivalently when the Killing form modified by $\theta$ is positive definite on the semisimple Lie algebra. Axiom 2 permits compact adjoint factors: on a compact factor the identity is a Cartan involution. Axiom 3 does not say that every real factor must be noncompact. It says that a whole rational simple factor may not be invisible; restriction of scalars can have compact real factors as long as at least one conjugate real factor is active.

Axiom 1 makes the holomorphic tangent space the $(-1,1)$ part. If types $(2,-2)$ occurred, the orbit would generally not carry the invariant complex structure needed below. Axiom 2 gives positive curvature in the compact directions and negative curvature in the domain directions. Axiom 3 eliminates redundant adjoint factors and is essential for the arithmetic group to act faithfully on the domain modulo its center.

### 3.2 Hermitian symmetric domains

Fix $h\in X$, let $K_h\subset G^{\mathrm{ad}}(\mathbf R)$ be the centralizer of $h$, and let $G^{\mathrm{ad}}(\mathbf R)^+$ be the identity component. Then

$$
X^+=G^{\mathrm{ad}}(\mathbf R)^+/K_h^+                              \tag{3.2}
$$

is the connected component of $h$ in $X$.

**Theorem 3.1.** Every component $X^+$ of a Shimura datum is a Hermitian symmetric domain. Its complex tangent space at $h$ is the $(-1,1)$ subspace of $\mathfrak g_{\mathbf C}$.

**Proof strategy.** Use the Cartan decomposition supplied by $h(i)$, then use the Hodge grading to define the complex structure and verify integrability.

**Proof.** Write $\mathfrak g_{\mathbf R}^{\mathrm{ad}}=\mathfrak k\oplus\mathfrak p$ for the $+1$ and $-1$ eigenspaces of the Cartan involution $\operatorname{Int}(h(i))$. The stabilizer has Lie algebra $\mathfrak k$, so $T_hX^+=\mathfrak p$. Axiom 1 identifies

$$
\mathfrak p_{\mathbf C}=\mathfrak g^{-1,1}\oplus\mathfrak g^{1,-1},
$$

and multiplication by $i$ on $\mathfrak g^{-1,1}$ and by $-i$ on $\mathfrak g^{1,-1}$ defines an invariant almost-complex structure. The bracket respects bidegrees. Because type $(-2,2)$ is absent,

$$
[\mathfrak g^{-1,1},\mathfrak g^{-1,1}]=0.
$$

The invariant almost-complex structure is therefore integrable. The geodesic symmetry of the Riemannian symmetric space commutes with this complex structure, making (3.2) Hermitian symmetric. $\square$

The theorem also gives

$$
\dim_{\mathbf C}X^+=\dim_{\mathbf C}\mathfrak g^{-1,1}.             \tag{3.3}
$$

This dimension formula will distinguish curves from surfaces.

### 3.3 Morphisms, products, and central changes

A morphism $(G,X)\to(G',X')$ is a rational homomorphism $f:G\to G'$ with $f_{\mathbf R}\circ X\subseteq X'$. It sends $\mu_h$ to $\mu_{f\circ h}$ and induces maps at every compatible level.

Products are literal:

$$
(G_1,X_1)\times(G_2,X_2)=(G_1\times G_2,X_1\times X_2).
$$

All three axioms can be checked factor by factor. The reflex field of a product is the compositum of the reflex fields, because an automorphism fixes the product cocharacter class exactly when it fixes both factor classes.

Central isogenies require more care. If $f:G\to G'$ induces an isomorphism on adjoint groups and carries $X$ onto $X'$, then the symmetric domains agree, but finite adelic quotients need not. The kernel changes central class groups and therefore can change the set of connected components. Similarly, replacing $\operatorname{Res}_{F/\mathbf Q}B^\times$ by the common-norm similitude subgroup from Book 123 leaves the adjoint domain unchanged while changing the abelian quotient.

### 3.4 Failure tests

Several plausible-looking data fail the definition.

If $h$ is central, the adjoint action has type $(0,0)$ and $\operatorname{Int}(h(i))$ is the identity. This is a Shimura datum only when $G^{\mathrm{ad}}$ is trivial. A noncommutative group with central $h$ fails axiom 3.

For $G=\operatorname{SL}_2$ and the usual real rotation map, no algebraic homomorphism $\mathbb S\to\operatorname{SL}_{2,\mathbf R}$ has the required determinant on all of $\mathbf C^\times$: the standard map has determinant $z\bar z$. The correct group is $\operatorname{GL}_2$ or a suitable similitude group; the adjoint domain can still be $\operatorname{PGL}_2(\mathbf R)/\operatorname{PO}(2)$.

If a quaternion algebra is ramified at every real place and the rational adjoint group is simple, taking the trivial map at every factor violates axiom 3. Such a totally definite group gives a zero-dimensional adelic set only after the datum is formulated through a torus or after the vacuous adjoint part is removed; it does not yield a positive-dimensional quaternionic Shimura variety.

Finally, a homomorphism whose representation on $V$ has types $(-2,0)$ and $(0,-2)$ gives endomorphism types $(-2,2)$ and $(2,-2)$. It fails axiom 1 even though a complex decomposition exists. The adjacency of the two weight-one types is essential.

## 4. Reflex fields

The symmetric domain depends only on real conjugacy, but arithmetic conjugates all embeddings at once. The reflex field is the smallest field over which the complex conjugacy class of the Hodge cocharacter can be recognized. This definition works uniformly for Hilbert, quaternionic, unitary, and toric data.

### 4.1 The conjugacy class of the Hodge cocharacter

Choose $h\in X$. Its cocharacter $\mu_h:\mathbf G_{m,\mathbf C}\to G_{\mathbf C}$ determines a point of the set

$$
\mathcal C(G)=\{\text{$G(\mathbf C)$-conjugacy classes of cocharacters of $G_{\mathbf C}$}\}.
$$

The class $[\mu_h]$ is independent of $h\in X$: real conjugacy is complex conjugacy. The absolute Galois group acts on $\mathcal C(G)$ because $G$ is rational.

**Definition 4.1.** The reflex field $E(G,X)\subset\overline{\mathbf Q}$ is the fixed field of

$$
\Gamma_{(G,X)}=
\{\sigma\in\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q):
\sigma[\mu_h]=[\mu_h]\}.                                            \tag{4.1}
$$

The stabilizer is open. Indeed, a cocharacter and a conjugating element are defined over a finite extension, so the orbit is finite. Hence $E(G,X)$ is a number field.

### 4.2 Field of definition and stabilizers

The fixed-field definition agrees with the usual field-of-definition formulation.

**Proposition 4.2.** The $G(\overline{\mathbf Q})$-conjugacy class $[\mu_h]$ is defined over $E(G,X)$ and over no smaller subfield of $\overline{\mathbf Q}$.

**Proof strategy.** Replace the infinite conjugacy orbit by the finite Weyl-orbit datum in a split maximal torus. This avoids the false inference that a Galois-stable geometric isomorphism class automatically has effective descent.

**Proof.** Choose a finite Galois extension $L/\mathbf Q$ splitting $G$ and a split maximal torus $T\subset G_L$ to which $\mu_h$ is conjugate. Two cocharacters of $T$ are conjugate in $G_L$ exactly when they belong to the same Weyl-group orbit. Thus $[\mu_h]$ is represented by the finite subset

$$
W(G_L,T)\mu_h\subset X_*(T).
$$

Transporting $T$ back to itself after a Galois conjugation changes the resulting action only by the Weyl group. Consequently the subgroup of $\operatorname{Gal}(L/\mathbf Q)$ preserving this finite orbit is exactly the image of the stabilizer in (4.1). Finite Galois descent of the orbit datum defines the conjugacy class over its fixed field. Conversely, if the class were defined over a smaller field $L_0$, every element of $\operatorname{Gal}(\overline{\mathbf Q}/L_0)$ would preserve its Weyl orbit and hence lie in (4.1). The fixed-field correspondence would then force $E(G,X)\subseteq L_0$. $\square$

One must use conjugacy classes, not a chosen cocharacter. A chosen $\mu_h$ can require a splitting field of a maximal torus, while its conjugacy class may be rational. This is exactly what happens for the Hilbert datum: individual embedding coordinates are not rational, but their uniform collection is.

### 4.3 Products and morphisms

If $f:(G,X)\to(G',X')$ is a morphism, every automorphism fixing $[\mu_h]$ fixes $[f\circ\mu_h]$. Therefore

$$
E(G',X')\subseteq E(G,X)                                             \tag{4.2}
$$

inside the chosen algebraic closure, provided $X'$ is the conjugacy class of $f\circ h$. The inclusion can be strict: a representation can forget labels.

For a product, the stabilizer is the intersection of the two stabilizers, so

$$
E(G_1\times G_2,X_1\times X_2)=E(G_1,X_1)E(G_2,X_2).                \tag{4.3}
$$

For an adjoint quotient, the central part of $\mu$ disappears. Thus the adjoint reflex field can be smaller than the reflex field of a similitude datum. In the three families considered here the central weight is rational, so it creates no extra extension; the embedding labels in the derived factors determine the field.

### 4.4 Computing by labelled embeddings

Let $L/\mathbf Q$ be finite Galois and split $G_L$. Choose a maximal torus and identify the conjugacy class by a labelled tuple $(\mu_\tau)_\tau$, where $\tau$ ranges over embeddings of an auxiliary field into $L$. Galois acts by permuting labels and transporting each cocharacter. Therefore

$$
E(G,X)=L^H,
$$

where $H$ is the subgroup preserving the tuple up to the Weyl group at every label.

For a restriction of scalars of type $A_1$, the Weyl group at a label exchanges the two diagonal weights. An oriented upper-half-plane choice fixes which weight is holomorphic, but the $G(\mathbf C)$-conjugacy class already allows this local exchange. What survives is usually the set of active labels. For unitary groups, complex conjugation also interchanges the two embeddings over a real place; signatures $(2,0)$ and $(0,2)$ are therefore exchanged rather than identified unless an inner conjugacy in the specified similitude group performs that exchange.

This labelled-embedding procedure is the computational engine used in Chapters 7--9. It is also a reliable defense against a common mistake: the field of definition of the group and the reflex field of its Shimura datum answer different questions. A quaternion algebra may be defined over $F$, while its reflex field is $\mathbf Q$, $F$, or an intermediate conjugate field depending on its active real places.

Here is a concrete stabilizer calculation. Suppose $F/\mathbf Q$ is Galois with group $\Gamma$ and a quaternionic cocharacter is active on $\Sigma\subset\Gamma$. Then

$$
E(G,X)=F^{\{\gamma\in\Gamma:\gamma\Sigma=\Sigma\}}.                 \tag{4.4}
$$

If $\Sigma=\Gamma$, the stabilizer is all of $\Gamma$ and the field is $\mathbf Q$. If $\Sigma=\{1\}$, the stabilizer is trivial and the field is $F$. If $F/\mathbf Q$ is cyclic quartic and $\Sigma=\{1,\gamma^2\}$, the stabilizer is $\{1,\gamma^2\}$ and the reflex field is the quadratic subfield. The same rational group can therefore support cocharacters with three different reflex fields.

For a unitary example, let $K/F$ be CM and suppose $F$ is real quadratic. If the two real places have signatures $(1,1)$ and $(1,1)$, all four CM embedding labels have multiplicity one and the reflex field is $\mathbf Q$. If the signatures are $(1,1)$ and $(2,0)$, the second conjugate pair is oriented. An automorphism exchanging its two CM embeddings changes $(2,0)$ to $(0,2)$ and does not fix the cocharacter class. The reflex field is then the field fixed by the stabilizer of that orientation, generally a CM field. The complex dimension changed from two to one, but the definite place still affected the arithmetic field.

## 5. Adelic quotients and finite level

The real domain supplies complex geometry, while finite adèles supply integral comparison data. Their quotient is neither an arbitrary orbit space nor merely a convenient notation. Its stabilizers, components, and transition maps are the raw material from which the arithmetic tower is descended.

### 5.1 The double quotient

For a compact open subgroup $K\subset G(\mathbf A_f)$, define the set in (1.1). It decomposes more concretely after choosing representatives $(g_i)_{i\in I}$ for

$$
G(\mathbf Q)\backslash G(\mathbf A_f)/K.
$$

The index set need not be finite for a general reductive group, but in the Shimura cases the component calculation of Chapter 6 reduces the relevant quotient to a finite torus class group. For each representative put

$$
\Gamma_i=G(\mathbf Q)\cap g_iKg_i^{-1}.
$$

Then there is a disjoint union, refined by components of $X$,

$$
\operatorname{Sh}_K(G,X)(\mathbf C)
\simeq\coprod_i\Gamma_i\backslash X.                                \tag{5.1}
$$

Indeed, every adelic coordinate is $qg_ik$; applying $q^{-1}$ moves the point into the $i$th copy of $X$. Two points there become equal exactly under $\Gamma_i$. This argument also shows why $G(\mathbf Q)$ must act diagonally.

The quotient is given the complex analytic structure inherited from (5.1). For the data in this book the arithmetic groups are discrete and act properly discontinuously. Proper discontinuity follows from compactness of point stabilizers in the adjoint real group together with discreteness of $G(\mathbf Q)$ in the product of its real and finite adelic points.

### 5.2 Arithmetic stabilizers

The stabilizer of $(h,gK)$ is

$$
\operatorname{Stab}(h,gK)
=G(\mathbf Q)\cap Z_{G(\mathbf R)}(h)\cap gKg^{-1}.                  \tag{5.2}
$$

Modulo the rational center it is finite: the first and third conditions make it arithmetic, while the middle condition places its adjoint image in a compact group. A discrete subgroup of a compact group is finite. Central units can remain, so a separate level condition is needed to eliminate all torsion.

If the stabilizer is trivial, the quotient is a complex manifold. If it is merely finite, the quotient has finite quotient singularities and naturally behaves as an orbifold. This distinction matters for universal families but not for the set (1.1). We will first descend neat levels and then obtain arbitrary levels as finite quotients.

### 5.3 Neat compact opens

Fix a faithful rational representation $\rho:G\hookrightarrow\operatorname{GL}(V)$. For $\gamma\in G(\mathbf Q)$, let $\Lambda(\gamma)\subset\overline{\mathbf Q}^{\times}$ be the multiplicative subgroup generated by the eigenvalues of $\rho(\gamma)$. The element $\gamma$ is **neat** if $\Lambda(\gamma)$ is torsion-free. A compact open $K$ is neat if every element of every arithmetic subgroup

$$
G(\mathbf Q)\cap gKg^{-1},\qquad g\in G(\mathbf A_f),
$$

is neat.

This definition is independent of the faithful representation. Indeed, matrix coefficients of any rational representation occur in tensor constructions from one faithful representation and its dual. Hence a root of unity generated by eigenvalues in one representation appears, after taking an integral power, in the other. Torsion-freeness is therefore intrinsic.

**Proposition 5.1.** Every compact open subgroup contains a neat normal compact open subgroup of finite index.

**Proof strategy.** Put the group into integral matrices away from finitely many primes and impose one sufficiently deep principal congruence condition at an auxiliary prime.

**Proof.** After conjugating a lattice, $K$ preserves $\widehat\Lambda$ in $V(\mathbf A_f)$. Choose a rational prime $\ell\geq3$ at which the group and lattice are integral. The kernel

$$
K(\ell^n)=\ker\bigl(K\to\operatorname{GL}(\Lambda/\ell^n\Lambda)\bigr)
$$

is compact open, normal, and finite index. Let $\gamma\in G(\mathbf Q)\cap gK(\ell^n)g^{-1}$. Conjugation does not change eigenvalues. If $d=\dim V$, the characteristic polynomial of $\rho(\gamma)-1$ has its coefficient of degree $j$ divisible by $\ell^{n(d-j)}$; its Newton polygon therefore gives a lower bound tending to infinity with $n$, for example $v_\ell(\lambda-1)\geq n/d$ after normalizing valuations in a splitting field, for every eigenvalue $\lambda$. If a product of their integral powers is a root of unity $\zeta$, then $\zeta$ lies in the splitting field of a degree-$d$ characteristic polynomial and is likewise arbitrarily close to $1$ as $n$ grows. The degrees of these splitting fields are bounded by $d!$, so only finitely many roots of unity can occur. Taking $n$ larger than the finitely many possible valuations of $\zeta-1$ forces $\zeta=1$. Hence $\Lambda(\gamma)$ is torsion-free. The same argument works for every $g$, so sufficiently deep $K(\ell^n)$ is neat. $\square$

**Corollary 5.2.** At neat level, the image of every stabilizer (5.2) in $G^{\mathrm{ad}}(\mathbf Q)$ is trivial. Equivalently, the effective arithmetic group acting on $X$ is torsion-free.

**Proof.** The adjoint image of a stabilizer is finite. If its order is $m$, every eigenvalue of a faithful adjoint representation is an $m$th root of unity. Neatness forces the subgroup generated by those eigenvalues to be torsion-free, so every eigenvalue is $1$. A finite-order unipotent element in characteristic zero is the identity. $\square$

Neatness is stronger than torsion-freeness of the abstract subgroup $K$. The point is that a rational stabilizer becomes finite only after projection to the adjoint group; a central root of unity may survive even when no chosen local factor visibly has finite order. The eigenvalue definition detects it simultaneously in every representation. Conversely, neatness does not rule out nontrivial unipotent elements of a compact $p$-adic group: their eigenvalues are all $1$, so the subgroup they generate is torsion-free. Such an element cannot stabilize a point of $X$ in a finite adjoint stabilizer, which is why Corollary 5.2 remains valid.

Central stabilizers require separate bookkeeping. For example, totally positive units in the center of a Hilbert group can lie in $G(\mathbf Q)\cap K$ and act trivially on $X$; they are not torsion and neatness does not remove them. They form an ineffective kernel of the analytic action and therefore do not create quotient singularities. A fine PEL moduli problem kills its actual automorphisms by fixing a polarization and sufficiently deep rigid level, not by pretending that every central arithmetic unit has disappeared from the double-coset presentation.

For example, full level $N\geq3$ in a faithful integral representation is neat after possibly increasing $N$ by one auxiliary prime power. Level $2$ is not enough in general because $-1$ can act trivially modulo $2$. This is the same obstruction that makes full level at least three useful in the rigidified CM descent of Book 125.

### 5.4 Changing level and Hecke maps

If $K'\subset K$, there is a finite map

$$
\pi_{K',K}:\operatorname{Sh}_{K'}(G,X)(\mathbf C)
\longrightarrow\operatorname{Sh}_K(G,X)(\mathbf C),
\qquad[h,gK']\longmapsto[h,gK].                                     \tag{5.3}
$$

When $K'$ is normal in $K$ and both are neat, the effective deck group is the quotient of $K/K'$ by the subgroup whose right action is induced by rational central elements. This qualification is necessary: the right action of $K/K'$ can meet the left rational action, and the kernel can contain nontorsion central units even though the finite quotient $K/K'$ is of course finite.

For $a\in G(\mathbf A_f)$, right translation gives

$$
[h,gK]\longmapsto[h,ga(a^{-1}Ka)],                                  \tag{5.4}
$$

a map from level $K$ to level $a^{-1}Ka$. A double coset $KaK$ becomes a finite correspondence after passing through $K\cap aKa^{-1}$. These maps are defined without choosing connected components. Canonical descent must make all of them algebraic over the reflex field; otherwise the collection of individual varieties would not form the Shimura tower.

## 6. Connected components

Connected components are where the derived group and the center meet. The symmetric domain sees the identity component of the adjoint real group, while the finite adelic coordinate sees an abelian class group. Strong approximation for the simply connected derived group makes that meeting precise.

### 6.1 From a domain component to an adelic quotient

Fix a connected component $X^+\subset X$ and define

$$
G(\mathbf Q)_+=\{q\in G(\mathbf Q):qX^+=X^+\}.                      \tag{6.1}
$$

Assume first that $G(\mathbf Q)$ acts transitively on $\pi_0(X)$. Then every connected component of the double quotient has a representative with first coordinate in $X^+$. Two such representatives lie in the same connected component exactly when their finite adelic coordinates differ by $G(\mathbf Q)_+$ on the left and $K$ on the right. Thus

$$
\pi_0\bigl(\operatorname{Sh}_K(G,X)(\mathbf C)\bigr)
\simeq G(\mathbf Q)_+\backslash G(\mathbf A_f)/K.                  \tag{6.2}
$$

**Proof.** Transitivity supplies a rational element moving the first coordinate of any representative into $X^+$. Once there, a continuous path cannot change the discrete finite adelic coset. A rational identification between two representatives stays in $X^+$ exactly when its rational element belongs to $G(\mathbf Q)_+$. Conversely, a relation by $q\in G(\mathbf Q)_+$ and $k\in K$ identifies the two quotients of the connected space $X^+$. $\square$

Without transitivity the correct formula is

$$
\pi_0\bigl(\operatorname{Sh}_K(G,X)(\mathbf C)\bigr)
=G(\mathbf Q)\backslash
\bigl(\pi_0(X)\times G(\mathbf A_f)/K\bigr).                     \tag{6.2a}
$$

The Shimura axioms alone do not improve (6.2a) to (6.2). In the three families here, transitivity is a separate arithmetic verification. For Hilbert data, weak approximation chooses a determinant with any prescribed real sign pattern. For the basic quaternionic group, the Hasse--Schilling reduced-norm theorem gives arbitrary signs at the split real places and forces positivity only at Hamiltonian places; those are precisely the signs needed to move among the components of $X$. For the unitary similitude groups selected below, the determinant--multiplier torus and weak approximation give the required sign changes at the indefinite factors. Central modifications are required to satisfy the same transitivity statement before (6.2) is used for them.

Formula (6.2) is exact but not yet computable. The next step removes the nonabelian derived group.

### 6.2 The abelianization principle

Let $\nu:G\to T=G^{\mathrm{ab}}$ and put

$$
T(\mathbf Q)^\dagger=\nu(G(\mathbf Q)_+).
$$

We need the following rank-one form of strong approximation.

**Rank-one strong approximation theorem.** Let $H/F$ be $\operatorname{SL}_2$, the reduced-norm-one group of a quaternion algebra, or the special unitary group of a two-dimensional Hermitian space. Assume $H$ is simply connected and $H(F_v)$ is noncompact for at least one archimedean place $v$. Then the diagonal $H(F)$ is dense in $H(\mathbf A_{F,f})$.

**Proof strategy.** Strong approximation is an integral, not merely a weak, approximation assertion: outside a prescribed finite set the approximant must remain in a fixed compact open. We prove the split case with root subgroups. The other two groups are simply connected forms of type $A_1$; the norm-quadric approximation lemma below supplies the missing integrality and is the rank-one form of the standard strong-approximation argument.

**Proof.** For $\operatorname{SL}_2$, use the two root subgroups

$$
u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},
\qquad
u^-(y)=\begin{pmatrix}1&0\\y&1\end{pmatrix}.                       \tag{6.2c}
$$

Over every field these root subgroups generate $\operatorname{SL}_2$, and near any fixed local element a word of bounded length in $u(x)$ and $u^-(y)$ gives an open set; the usual row-reduction identities prove both assertions. Given finitely many local neighborhoods, choose the finitely many parameters in such words. Additive approximation supplies global parameters simultaneously close to them and integral at every finite place outside the chosen set. The resulting word lies in the required neighborhoods and in $\operatorname{SL}_2(\mathcal O_w)$ everywhere else. This proves density without invoking strong approximation for $\mathbf G_m$, which would be false.

We isolate the form of the norm-quadric argument that is actually needed. Let $Q$ be a nondegenerate four-dimensional quadratic form over $F$, let $Y:Q=1$, and suppose $Q$ is isotropic over one completion $F_v$ with $v$ outside a set $S$ of finite places. Then, for every smooth integral model $\mathcal Y$ away from a finite enlargement of $S$, the diagonal set $Y(F)$ is dense in

$$
\prod_{w\in S}Y(F_w)\times
\prod_{w\notin S\cup\{v\}}\mathcal Y(\mathcal O_w).             \tag{6.2b}
$$

To prove this integral approximation lemma, choose an isotropic pair $e,f$ at $v$ with $(e,f)=1$ and use projection from the rational point of $Y$ to obtain affine coordinates whose inverse has denominator $D$, a nonzero quadratic polynomial. Clear the finitely many coefficients of this chart once and for all. Additive approximation chooses the affine coordinates in the prescribed $w$-adic neighborhoods and integral away from a finite set. The remaining requirement is that $D$ be a unit away from that set. Replace one coordinate by $x+cM$ where $M$ is divisible by every prescribed finite modulus and $c\in F$ varies in the isotropic $e$-direction at $v$. For each new prime divisor $\mathfrak p$ of $D$, nondegeneracy makes the reduction of $D(x+cM)$ a nonzero polynomial of degree at most two in $c$; choose $c$ modulo $\mathfrak p$ away from its at most two roots. Chinese remaindering preserves all earlier choices. The norm of the part of $(D)$ supported outside the prescribed set strictly decreases after cancelling those prime factors from numerator and denominator. Induction on that nonnegative norm terminates and makes $D$ an outside unit. Substitution in the inverse chart proves (6.2b). Points outside the chosen chart are reached by first making an arbitrarily small local perturbation, permissible because the chart is dense and every local $Y(F_w)$ is smooth.

For $H=B^1$, reduced norm is such a four-dimensional $Q$, and $B$ split at the chosen archimedean place is exactly the required isotropy. Multiplication on the quadric identifies its integral points with the required compact-open conditions after enlarging $S$; conjugating lattices handles an arbitrary compact open. A two-dimensional special unitary group is a simply connected form of type $A_1$. Type $A_1$ has no outer forms, so the degree-two classification identifies it with $B'^1$ for a quaternion algebra $B'/F$; noncompactness at $v$ says that $B'$ splits there. The same norm-quadric argument applies. Restriction of scalars and finite products preserve density. $\square$

We may therefore assume that $G^{\mathrm{der}}$ is simply connected and satisfies this approximation theorem. This holds for the Hilbert, indefinite quaternionic, and indefinite unitary groups considered below: their derived groups are restrictions of scalars of $\operatorname{SL}_2$, $B^1$, and $\operatorname{SU}(V)$, respectively.

**Theorem 6.1.** Under that hypothesis, $\nu$ induces a bijection

$$
G(\mathbf Q)_+\backslash G(\mathbf A_f)/K
\xrightarrow{\sim}
T(\mathbf Q)^\dagger\backslash\nu(G(\mathbf A_f))/\nu(K).           \tag{6.3}
$$

If $\nu:G(\mathbf A_f)\to T(\mathbf A_f)$ is surjective, the middle term on the right is $T(\mathbf A_f)$.

**Proof strategy.** Equality in the torus quotient leaves an error in the derived group. Strong approximation absorbs that error into a rational element and the level.

**Proof.** The map is well defined. Suppose $g_1,g_2$ have the same image on the right. After multiplying $g_2$ by an element of $G(\mathbf Q)_+$ and an element of $K$, their quotient $d$ lies in $G^{\mathrm{der}}(\mathbf A_f)$. Strong approximation, applied with the compact open $K\cap G^{\mathrm{der}}(\mathbf A_f)$, writes

$$
d=qk_d,
\qquad q\in G^{\mathrm{der}}(\mathbf Q),\quad
k_d\in K\cap G^{\mathrm{der}}(\mathbf A_f).
$$

In the three rank-one families, $G^{\mathrm{der}}(\mathbf R)$ is a product of the connected groups $\operatorname{SL}_2(\mathbf R)$, compact $\operatorname{SU}(2)$, and indefinite $\operatorname{SU}(1,1)$ factors. It therefore preserves $X^+$, so $q\in G(\mathbf Q)_+$. Hence $g_1$ and $g_2$ give the same left double coset. Conversely, equality on the left plainly implies equality on the right. Surjectivity onto the displayed image follows from its definition. $\square$

The finiteness of (6.3) follows from the finiteness of the relevant torus class group. In the examples it is a quotient of an ordinary, narrow, or CM ray class group, whose finiteness is part of the adelic theory recalled in Book 4.

The strong-approximation hypothesis cannot simply be deleted. For a torus, the derived group is trivial and (6.3) says nothing beyond the original class quotient. For a semisimple group anisotropic at every place omitted from the adèles, rational points need not be dense enough to absorb the derived adelic coordinate. The residual finite set is a genuine class set. Our groups avoid this obstruction because their simply connected derived groups have a noncompact real factor: $\operatorname{SL}_2$ for Hilbert data, $B^1$ at a split quaternionic place, and $\operatorname{SU}(1,1)$ at an indefinite unitary place.

There is also a central-surjectivity issue. Even if $G\to T$ is surjective as an algebraic group, $G(\mathbf A_f)\to T(\mathbf A_f)$ need not be onto when a finite central kernel has nontrivial local cohomology. This is why (6.3) uses $\nu(G(\mathbf A_f))$ before stating the simpler surjective form. In the Hilbert determinant and quaternionic reduced-norm cases, local surjectivity is elementary. In the unitary case, retaining the image in (9.9) avoids an unjustified Hasse norm assertion.

### 6.3 Galois action on components

Let $E=E(G,X)$. The Hodge cocharacter induces, after abelianization, a morphism

$$
r_{(G,X)}:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m
\longrightarrow T.                                                    \tag{6.4}
$$

Its construction is given in Chapter 10. Choose an idele $s$ representing the desired Artin element with positive component at every real place of $E$. On the component quotient (6.3), arithmetic reciprocity acts by

$$
[t]^{\operatorname{Art}_E(s)}=[r_{(G,X)}(s_f)t].                     \tag{6.5}
$$

This action is well defined. If two positive-at-infinity representatives give the same Artin element, their finite parts differ by a totally positive principal element. The labelled-embedding formula for $r_{(G,X)}$ expresses every active real coordinate as a monomial in positive real coordinates; it therefore lifts to an element preserving $X^+$. Hence its image lies in $T(\mathbf Q)^\dagger=\nu(G(\mathbf Q)_+)$. More generally, an open subgroup fixing the given finite component set may be chosen to map into $\nu(K)$. Thus both principal ambiguity and level ambiguity disappear in (6.3). Without the positivity normalization this is false already for a negative rational principal idele acting on a Hilbert narrow-class quotient. Continuity implies that the action factors through a finite ray class quotient because the component set is finite and discrete.

The field of definition of one geometric component is therefore the abelian extension of $E$ corresponding to the open subgroup

$$
U_C=E^\times
r_{(G,X)}^{-1}\bigl(T(\mathbf Q)^\dagger\nu(K)\bigr)
E_\infty^{\times,0}/E^\times
\subseteq\mathbf A_E^\times/E^\times,                              \tag{6.6}
$$

where the inverse image is taken on finite ideles.

This is generally larger than $E$. A canonical model over $E$ need not have geometrically connected components defined over $E$ individually.

To see how the action becomes finite, choose a compact open $U\subset\mathbf A_{E,f}^\times$ mapped by $r_{(G,X)}$ into $\nu(K)$. The connected archimedean factor and $E^\times U$ lie in the kernel of the component action. The quotient is a ray class quotient for a modulus supported at the finitely many primes where $U$ is smaller than the maximal unit subgroup, with real signs included when $T(\mathbf Q)^\dagger$ imposes positivity. Book 4 proves that this quotient is finite. Thus the component field is not obtained from an abstract continuity argument alone; it is a concrete finite class field with level-controlled conductor.

### 6.4 A warning about geometric connectedness

Three notions must be separated:

- $X^+$ is connected as a complex manifold;
- its arithmetic quotient can be connected over $\mathbf C$;
- the corresponding component can require an abelian extension of $E$ for its field of definition.

Even when the whole canonical model is defined over $E$, Galois can permute its geometric components transitively. At neat level each component is a connected complex manifold and hence analytically irreducible. At arbitrary level it is a finite image of such a component and remains irreducible; the normal coarse model can acquire quotient singularities, but it does not acquire a second irreducible branch inside the same connected component. Field of definition, geometric connectedness, smoothness, and irreducibility are therefore four separate issues.

## 7. Hilbert modular data

The Hilbert datum is the split benchmark. Every real place is active, the reflex field collapses to $\mathbf Q$, and the components become a narrow ideal-class quotient. The calculation fixes all signs before inner and unitary forms are introduced.

### 7.1 The group and its domain

Let $F$ be totally real of degree $d$ and set

$$
G=\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_{2,F}.
$$

Then

$$
G(\mathbf R)=\prod_{\tau:F\hookrightarrow\mathbf R}
\operatorname{GL}_2(\mathbf R).
$$

For $z=a+bi\in\mathbf C^\times$, put

$$
h_0(z)=
\begin{pmatrix}a&b\\-b&a\end{pmatrix}.                              \tag{7.1}
$$

Let $h$ have component $h_0$ at every real embedding. The conjugacy class is

$$
X\simeq(\mathfrak H^\pm)^d,                                          \tag{7.2}
$$

where $\mathfrak H^\pm=\mathbf C\setminus\mathbf R$ and the sign records the orientation of the complex structure on $\mathbf R^2$. The component $X^+=(\mathfrak H)^d$ uses the upper half-plane at every embedding.

To see (7.2), a complex structure $J$ on an oriented real plane is conjugate to $h_0(i)$, and its stabilizer in $\operatorname{GL}_2(\mathbf R)$ is $\mathbf C^\times$. Thus

$$
\operatorname{GL}_2(\mathbf R)/\mathbf C^\times\simeq\mathfrak H^\pm.
$$

### 7.2 Verification of the axioms

The product of upper half-planes is visually plausible, but the datum is not certified until the Lie weights and Cartan involution are checked. The calculation at one embedding repeats at every label and becomes the template for the inner forms.

**Proposition 7.1.** The pair $(G,X)$ just defined is a Shimura datum of dimension $d$.

**Proof.** It is enough to work at one real factor. Over $\mathbf C$, choose eigenvectors of $h_0$ so that

$$
\mu_{h_0}(z)=\begin{pmatrix}z&0\\0&1\end{pmatrix}.                 \tag{7.3}
$$

Conjugation on $\mathfrak{gl}_2$ gives weights $1,0,-1$ on the upper off-diagonal, diagonal, and lower off-diagonal subspaces. With the Hodge convention of Chapter 2 these are exactly $(-1,1)$, $(0,0)$, and $(1,-1)$. Further,

$$
h_0(i)=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

Conjugation by this matrix is the usual Cartan involution on $\operatorname{PGL}_2(\mathbf R)$; its fixed group is $\operatorname{PO}(2)$. Every rational simple adjoint factor of the restriction of scalars becomes the collection of all embedding factors, and $h$ is nontrivial on each, so axiom 3 holds. There is one holomorphic tangent line at each of the $d$ real labels, giving dimension $d$. $\square$

The weight is scalar:

$$
w_h(t)=tI_2
$$

at every factor. It is defined over $\mathbf Q$ as the diagonal scalar in $G$, a fact used in the reflex-field computation.

### 7.3 Reflex field and components

The real domain treats every embedding uniformly, so its field should forget the labels; connected components do the opposite and retain their ideal-theoretic orientations. Computing both invariants side by side makes that contrast precise.

At every embedding $\tau$, the cocharacter has the same conjugacy type $(1,0)$. Galois merely permutes the labels, so it preserves the full tuple. Therefore

$$
E(G,X)=\mathbf Q.                                                     \tag{7.4}
$$

The determinant is the abelianization map

$$
\det:G\longrightarrow\operatorname{Res}_{F/\mathbf Q}\mathbf G_m.
$$

An element of $G(\mathbf Q)=\operatorname{GL}_2(F)$ preserves $X^+$ exactly when its determinant is totally positive. Strong approximation for $\operatorname{Res}_{F/\mathbf Q}\operatorname{SL}_2$ gives

$$
\pi_0(\operatorname{Sh}_K(G,X)(\mathbf C))
\simeq F_+^\times\backslash\mathbf A_{F,f}^\times/\det K,           \tag{7.5}
$$

where $F_+^\times$ is the group of totally positive elements.

For $K=\operatorname{GL}_2(\widehat{\mathcal O}_F)$, (7.5) is the narrow class group $\operatorname{Cl}^+(F)$. For principal congruence level it is a narrow ray quotient. The adjective narrow is forced by the choice of $X^+$; replacing $F_+^\times$ by $F^\times$ would incorrectly identify components related by an orientation-reversing matrix.

For $F=\mathbf Q$, the quotient

$$
\mathbf Q_{>0}^\times\backslash\mathbf A_f^\times/
\widehat{\mathbf Z}^{\times}
$$

is trivial: a finite idele determines a fractional ideal $(n)$, and multiplication by the positive rational $n^{-1}$ makes it a unit. Thus the full-level modular curve has one complex component after the upper-half-plane orientation is fixed. Its many cusps are not connected components; cusps belong to a compactification, whereas (7.5) concerns the open variety.

For a real quadratic field, the distinction between ordinary and narrow classes is already visible. If a unit realizes the missing real sign pattern, one can correct an orientation reversal and the narrow and ordinary class groups agree. Otherwise the narrow group can be larger. Formula (7.5), rather than the ordinary ideal class group, automatically records the correct alternative.

### 7.4 Special points and reciprocity

Let $K_0/F$ be a CM quadratic extension. Multiplication of $K_0$ on its two-dimensional $F$-space embeds

$$
K_0^\times\hookrightarrow\operatorname{GL}_2(F)=G(\mathbf Q).
$$

Choosing one complex embedding above each $\tau$ gives a CM type $\Phi$ and a toric Hodge map $h_\Phi:\mathbb S\to(\operatorname{Res}_{K_0/\mathbf Q}\mathbf G_m)_{\mathbf R}$. Its composite with $G$ is a special point.

The determinant of multiplication by $a\in K_0^\times$ is

$$
N_{K_0/F}(a)=a\bar a,                                                 \tag{7.6}
$$

so the torus lands in the correct similitude group. The reciprocity morphism is the reflex norm $r_\Phi$ followed by this embedding. By Book 125,

$$
[h_\Phi,g]^{\operatorname{Art}_{E(\Phi)}(s)}
=[h_\Phi,r_\Phi(s_f)g].                                              \tag{7.7}
$$

On determinants, (7.7) and the weight identity give the action (6.5) on the narrow class quotient. Thus special-point reciprocity and the independent component computation agree.

The ambient reflex field in (7.4) is $\mathbf Q$, but the CM point usually has reflex field $E(\Phi)$ strictly larger than $\mathbf Q$. There is no conflict. The whole Hilbert variety descends to $\mathbf Q$; one special point is defined over an abelian extension of its own CM reflex field. Norm compatibility (10.4) converts the latter Galois action into the former action on connected components.

## 8. Quaternionic data

Quaternionic data are inner forms of the Hilbert datum, but the real domain changes only at the ramified archimedean places. This makes them ideal for isolating weight-two automorphic information in one-dimensional geometry.

### 8.1 Real ramification selects the domain

Let $F$ be totally real and $B/F$ a quaternion algebra. Write

$$
\Sigma=\{\tau:F\hookrightarrow\mathbf R:B\otimes_{F,\tau}\mathbf R
\simeq M_2(\mathbf R)\}.
$$

Let $r=|\Sigma|>0$. For the basic datum take

$$
G=\operatorname{Res}_{F/\mathbf Q}B^\times.                          \tag{8.1}
$$

At $\tau\in\Sigma$, use $h_0$ from (7.1) after choosing a splitting. At a ramified real place, the adjoint group is compact and we use the trivial adjoint homomorphism. A lift through the center is part of the datum. Changing an existing lift by a central cocharacter does not change the domain, but existence of a lift with rational scalar weight is a genuine condition and may require a central modification of the group.

Thus

$$
X\simeq(\mathfrak H^\pm)^\Sigma.                                   \tag{8.2}
$$

and $X^+=\mathfrak H^\Sigma$. The description is independent of the chosen matrix splittings because two splittings differ by inner conjugacy.

Book 123 constructs the common-norm group

$$
G^\star=\{b\in\operatorname{Res}_{F/\mathbf Q}B^\times:
\operatorname{Nrd}(b)\in\mathbf G_m\}.                              \tag{8.3}
$$

and proves that it is connected reductive, with derived group $\operatorname{Res}_{F/\mathbf Q}B^1$, and that it has a faithful trace-pairing representation with rational multiplier. Its adjoint group agrees with that of (8.1), but this fact alone does not lift the Hodge map: the determinant at an active split factor and a central norm at a compact factor can have incompatible exponents. The common-norm group is used only when the chosen Hodge map actually lifts. Otherwise the tensor-corestriction construction, its hyperbolic enlargement, or another central modification with the same adjoint datum supplies the polarized realization. In every case both the lift and the two weight-one Hodge types must be checked.

### 8.2 Verification and dimension

At a compact real factor the identity Cartan involution is correct, whereas at a split factor the rotation involution is correct. The purpose of the verification is to show that these unlike local behaviors still assemble into one rational datum.

**Proposition 8.1.** For $r>0$, the pair $(G,X)$ is a Shimura datum of dimension $r$. The same holds for a connected central modification only when the adjoint Hodge map lifts to it; a polarized realization must additionally have types $(-1,0)$ and $(0,-1)$.

**Proof.** At a split place, the calculation is identical to Proposition 7.1. At a ramified place, $B_\tau^\times/\mathbf R^\times$ is compact, the adjoint Hodge structure is type $(0,0)$, and the identity is a Cartan involution. Thus axioms 1 and 2 hold factorwise.

For axiom 3, the rational adjoint group associated with a field factor of $F$ is obtained by restricting the norm-one inner form. Its real factors are permuted transitively by the Galois closure. Because $\Sigma$ is nonempty, the Hodge map is nontrivial on that rational factor. The central weight has trivial adjoint action and creates no new condition. Each split place contributes one $(-1,1)$ tangent line; compact places contribute none. Formula (3.3) gives dimension $r$. $\square$

If $r=1$, each connected component is a quotient of one upper half-plane and hence a Shimura curve. If $B$ is division at some finite or real place, the arithmetic quotient can be compact; more precisely, the quotient is compact exactly when the adjoint group is anisotropic over $\mathbf Q$, which for quaternion algebras means $B$ is a division algebra. The proof is the standard rational-parabolic criterion: cusps correspond to rational proper parabolics, and $PB^\times$ has one precisely when $B$ is split.

The condition is global. If $B=M_2(F)$, a rational upper-triangular subgroup is parabolic and its orbits produce cusps. If $B$ is division, a rational parabolic would provide a nonzero proper right ideal of $B$, contradicting division. Conversely, a proper right ideal in a split matrix algebra stabilizes a line and yields a parabolic. A quaternion algebra may therefore be split at the distinguished real place and still give a compact curve because it ramifies at another place.

### 8.3 Reflex field

Ramification of $B$ determines which real labels are silent in the Hodge cocharacter. The reflex field is therefore recovered by asking which Galois automorphisms preserve the active subset, not by taking the field of definition of $B$ on faith.

The cocharacter is noncentral exactly at the labels in $\Sigma$. Its local conjugacy class is uniform on that set and trivial on its complement. Hence

$$
E_B=\overline{\mathbf Q}^{H_\Sigma},
\qquad
H_\Sigma=\{\sigma:\sigma\Sigma=\Sigma\}.                           \tag{8.4}
$$

Here embeddings are viewed in a common Galois closure. This field is totally real because complex conjugation fixes every real embedding label.

Three cases are useful checks.

If $B$ is split at every real place, then $\Sigma$ is the full embedding set and $E_B=\mathbf Q$, recovering the Hilbert result. If $B$ is split at exactly one place $\tau_0$, then the stabilizer of $\Sigma$ is the stabilizer of $\tau_0$, so $E_B=\tau_0(F)$ inside $\overline{\mathbf Q}$. If $\Sigma$ is a proper Galois-stable union arising from an intermediate field, $E_B$ can be a proper intermediate field. Thus “the reflex field is $F$” is correct in the one-split-place curve case but false in general.

### 8.4 Components and the curve case

Inner twisting changes matrices but not the determinant character: reduced norm is the descended determinant. It therefore carries the entire component calculation once strong approximation removes the norm-one group.

For $G=\operatorname{Res}_{F/\mathbf Q}B^\times$, reduced norm gives the abelian quotient. An element of $B^\times$ preserves $X^+$ exactly when its reduced norm is positive at every $\tau\in\Sigma$. Put

$$
F_{B,+}^\times=
\{a\in F^\times:\tau(a)>0\text{ at every real place where }
B\text{ is Hamiltonian}\}.                                         \tag{8.5}
$$

The rational reduced-norm theorem says

$$
\operatorname{Nrd}(B^\times)=F_{B,+}^\times.
$$

A Hamiltonian reduced norm is positive definite, which proves the necessary sign condition. Conversely, let $c\in F^\times$ satisfy those signs and consider the five-variable quadratic form $\operatorname{Nrd}(x)-ct^2$ on $B\oplus F$. It is isotropic at every finite place by local surjectivity of reduced norm, at every split real place because determinant is surjective, and at every Hamiltonian place by the sign assumption. The Hasse principle makes it isotropic over $F$; weak approximation on the resulting smooth quadric permits an isotropic point with $t\ne0$, and then $\operatorname{Nrd}(x/t)=c$. Thus rational reduced norms already impose positivity at every ramified real place; this condition is independent of preservation of the chosen domain component.

For the basic datum every split real place belongs to $\Sigma$ and is active. Preservation of $X^+$ adds positivity at those split places. Since the split and Hamiltonian real places partition the real embeddings, the exact rational image is therefore

$$
\operatorname{Nrd}(G(\mathbf Q)_+)
=F_{B,+}^\times\cap
\{a:\tau(a)>0\text{ for every }\tau\in\Sigma\}
=F_+^\times,                                                        \tag{8.6}
$$

where $F_+^\times$ denotes the totally positive elements. Strong approximation for $B^1$ at a noncompact factor and surjectivity of reduced norm at every finite local field now give

$$
\pi_0\bigl(\operatorname{Sh}_K(G,X)(\mathbf C)\bigr)
\simeq F_+^\times\backslash
\mathbf A_{F,f}^\times/\operatorname{Nrd}(K).                        \tag{8.7}
$$

Thus (8.7) is a narrow ray-type quotient. The two sources of its signs must not be conflated: orientation of $X^+$ imposes positivity at split active places, while the rational reduced-norm image imposes positivity at Hamiltonian places even though those compact factors carry no orientation.

For example, let $F$ be real quadratic and let $B$ be ramified at one real place and one finite place. Its ramification set has even cardinality. It is split at the other real place and gives a compact Shimura curve. The reflex field is the embedded copy of $F$ singled out by that split place. Positivity at the split place comes from orientation, and positivity at the Hamiltonian place is automatic for every rational reduced norm. Components are therefore narrow ideal classes modulo the reduced norms of the level.

For a connected central modification $G^\natural$ with maximal abelian quotient $\nu^\natural:G^\natural\to T^\natural$, the exact formula remains

$$
T^\natural(\mathbf Q)^\dagger\backslash
\nu^\natural(G^\natural(\mathbf A_f))/\nu^\natural(K^\natural).     \tag{8.8}
$$

For the common-norm group $G^\star$, its rational multiplier can project (8.8) toward a quotient of $\mathbf Q_{>0}^\times\backslash\mathbf A_f^\times$; a finite kernel or cokernel coming from the central isogeny must be retained unless separately shown to vanish. One may neither substitute the basic narrow quotient (8.7) for (8.8) nor replace (8.8) by the multiplier quotient without proving the relevant rational and finite-adelic images. The common-norm condition deliberately changes the abelianized label set.

### 8.5 CM tori in a quaternion algebra

Let $K_0/F$ be CM quadratic. An $F$-embedding $K_0\hookrightarrow B$ exists exactly when no place ramified in $B$ splits in $K_0$. Necessity is local: a split quadratic algebra contains a nontrivial idempotent and cannot embed in a quaternion division algebra. Sufficiency follows from the local embedding criterion and the local-global theorem for quaternion embeddings.

Once embedded, $K_0^\times$ is a maximal torus of $B^\times$, and

$$
\operatorname{Nrd}_B(a)=N_{K_0/F}(a)=a\bar a.                       \tag{8.9}
$$

A CM type compatible with the chosen upper-half-plane orientations gives a special point $[h_\Phi,g]$. Its reciprocity morphism is

$$
\operatorname{Res}_{E(\Phi)/\mathbf Q}\mathbf G_m
\xrightarrow{r_\Phi}
\operatorname{Res}_{K_0/\mathbf Q}\mathbf G_m
\longrightarrow G.                                                    \tag{8.10}
$$

By Book 125, arithmetic reciprocity acts by left multiplication with (8.10). The quaternion algebra changes the admissible tori, the component quotient, and compactness; it does not introduce a new inverse into CM reciprocity.

## 9. Unitary data

Unitary groups make the Hodge labels more expressive. At each real place the signature records how many holomorphic directions occur above each of the two CM embeddings. This flexibility produces compact surfaces while retaining the same rank-two automorphic input.

### 9.1 Hermitian spaces and similitudes

Let $K/F$ be a CM quadratic extension with conjugation $c$, and let $V$ be a two-dimensional $K$-vector space with a nondegenerate Hermitian form

$$
\langle ax,by\rangle=a\langle x,y\rangle\bar b.
$$

We use the rational similitude group

$$
G(R)=\{g\in\operatorname{GL}_{K\otimes R}(V\otimes R):
\langle gx,gy\rangle=\nu(g)\langle x,y\rangle,
\ \nu(g)\in R^\times\}.                                             \tag{9.1}
$$

This is connected reductive. Its derived group is $\operatorname{Res}_{F/\mathbf Q}\operatorname{SU}(V)$, and its center is a subtorus of $\operatorname{Res}_{K/\mathbf Q}\mathbf G_m$ cut out by $a\bar a\in\mathbf G_m$. These assertions follow after base change to $\overline{\mathbf Q}$, where (9.1) becomes a product of general linear groups with one common scalar multiplier; connectedness and reductivity then descend.

Choose $\delta\in K$ with $\bar\delta=-\delta$ and signs arranged so that

$$
\psi(x,y)=\operatorname{Tr}_{K/\mathbf Q}
(\delta\langle x,y\rangle)                                           \tag{9.2}
$$

is alternating and has the desired positivity. Then $G$ embeds into $\operatorname{GSp}(V_\mathbf Q,\psi)$ with multiplier $\nu$. This makes the datum of Hodge type and links it to polarized abelian varieties.

### 9.2 Signatures and the Hodge map

For each real embedding $\tau:F\hookrightarrow\mathbf R$, choose an extension $\varphi:K\hookrightarrow\mathbf C$. Write

$$
(p_\tau,q_\tau),\qquad p_\tau+q_\tau=2,                             \tag{9.3}
$$

for the signature of the Hermitian form, with the convention that the $p_\tau$-dimensional subspace has positive sign. A Hodge map selects a negative $q_\tau$-plane on which $z$ acts and its positive complement on which $\bar z$ acts, with the convention adjusted globally to (1.3).

The local domain is

$$
\mathcal D_\tau=
\{\text{negative $q_\tau$-planes in }\mathbf C^2\}.                 \tag{9.4}
$$

For signatures $(2,0)$ or $(0,2)$ this is a point. For $(1,1)$ it is a complex one-ball, biholomorphic to the upper half-plane. Therefore

$$
X^+=\prod_{\tau}\mathcal D_\tau,
\qquad
\dim_{\mathbf C}X^+=\sum_\tau p_\tau q_\tau.                      \tag{9.5}
$$

In rank two this dimension is simply the number of places of signature $(1,1)$.

### 9.3 Axiom verification and reflex field

The signatures have two simultaneous meanings: they are dimensions of positive and negative subspaces, and they are multiplicities of Hodge weights. The first verifies the Cartan geometry; the second computes the Galois stabilizer.

**Proposition 9.1.** The homomorphisms determined by (9.3)--(9.4) form a Shimura datum, provided each rational simple adjoint factor is indefinite at one or more real places.

**Proof.** On $V_{\mathbf C}$ the Hodge map has types $(-1,0)$ and $(0,-1)$. Proposition 2.1 gives the first two axioms from (9.2) and positivity. Explicitly, maps between the two Hodge subspaces have types $(-1,1)$ and $(1,-1)$, while endomorphisms preserving each have type $(0,0)$. The stabilizer of the Hodge decomposition is $U(p_\tau)\times U(q_\tau)$ modulo center, a maximal compact subgroup of $PU(p_\tau,q_\tau)$. The final hypothesis is exactly axiom 3. Formula (9.5) follows by identifying the holomorphic tangent space with $\operatorname{Hom}(W^-,W^+)$, of dimension $p_\tau q_\tau$. $\square$

The reflex field is computed from the **signature function** on embeddings of $K$:

$$
r_\varphi=p_\tau,
\qquad r_{\bar\varphi}=q_\tau.                                      \tag{9.6}
$$

It is the fixed field of

$$
H_r=\{\sigma:r_{\sigma\varphi}=r_\varphi
\text{ for every }\varphi\}.                                       \tag{9.7}
$$

**Proof.** Over $\mathbf C$, the cocharacter on the factor labelled by $\varphi$ has $r_\varphi$ entries of weight one and $2-r_\varphi$ entries of weight zero. Two such cocharacters are conjugate exactly when these multiplicities agree. Galois permutes the labels, so its stabilizer is precisely (9.7). Definition 4.1 gives the claim. $\square$

If every signature is $(1,1)$, then $r_\varphi=r_{\bar\varphi}=1$ everywhere and the reflex field is $\mathbf Q$. If some definite places are oriented as $(2,0)$ rather than $(0,2)$, their CM labels survive and the reflex field can be CM. Forgetting those definite labels gives the wrong field even though those places contribute no complex dimension.

For $F=\mathbf Q$ and $K$ imaginary quadratic, signature $(1,1)$ gives the unitary upper half-plane. Its reflex field is $\mathbf Q$, although the Hermitian group is defined using $K$. Signature $(2,0)$ instead gives a zero-dimensional datum. Its cocharacter distinguishes the chosen embedding $K\hookrightarrow\mathbf C$, so its reflex field is $K$. The algebraic group alone therefore determines neither the domain dimension nor the reflex field.

For $[F:\mathbf Q]=3$, signatures $(1,1),(1,1),(2,0)$ give dimension two. The definite factor makes no tangent contribution, yet it selects one member of a CM embedding pair. This is the characteristic pattern of the auxiliary surfaces in parity-sensitive cases: two noncompact factors provide degree-two geometry, while a definite label retains arithmetic information in the Hodge cocharacter.

### 9.4 Components and compact surfaces

Let $T=G/G^{\mathrm{der}}$. Determinant together with the multiplier identifies it with the torus

$$
\{(a,c)\in\operatorname{Res}_{K/\mathbf Q}\mathbf G_m\times
\mathbf G_m:a\bar a=c^2\}
$$

subject to

$$
N_{K/F}(\det_K g)=\nu(g)^2.                                         \tag{9.8}
$$

Since $\operatorname{SU}(V)$ is simply connected and has a noncompact real factor, strong approximation gives

$$
\pi_0(\operatorname{Sh}_K(G,X)(\mathbf C))
\simeq T(\mathbf Q)^\dagger\backslash
\nu_T(G(\mathbf A_f))/\nu_T(K).                                     \tag{9.9}
$$

Writing only $\nu(g)$ in (9.9) can lose the determinant class; writing only $\det_K(g)$ can violate (9.8). The torus quotient is the invariant formulation.

When exactly two real places have signature $(1,1)$, (9.5) gives a surface. It is compact when $G^{\mathrm{ad}}$ is anisotropic over $\mathbf Q$. For a unitary group, isotropic rational lines give rational proper parabolics and hence cusps; anisotropy of the Hermitian space rules them out. Thus a Hermitian space can be chosen indefinite at two real places yet anisotropic over $F$, producing a compact complex surface. This is not contradictory: real isotropy and rational isotropy are different conditions.

The signatures and the finite local invariants of a Hermitian space obey one global product relation. They cannot be prescribed independently. In practice one fixes the two indefinite real signatures, chooses definite orientations at the remaining real places, and adjusts one finite local invariant so that the product relation holds and the global Hermitian space remains anisotropic. That adjustment changes the bad-prime set and permissible compact opens but not (9.5) or (9.7), which depend only on the archimedean cocharacter.

At a special point, a commutative CM algebra $L$ acts on $V$ compatibly with the involution. Its torus maps to $G$ only if every component has the same rational similitude multiplier. The componentwise weight identity from Book 124 proves this condition for reflex norms. Book 125 then supplies the special-point formula (1.4), including polarization and level.

## 10. Reciprocity morphisms

The reflex field of the ambient datum governs the whole variety; the larger reflex field of a special point governs its individual Galois orbit. Both actions arise from the same operation on cocharacters. This chapter constructs the relevant torus morphisms and proves their compatibility with the adelic quotient and its component set.

### 10.1 The toric construction

Let $(T,\{h\})$ be a toric Shimura datum. Since $T$ is commutative, the conjugacy class contains only $h$. Put $E=E(T,h)$. The cocharacter $\mu_h$ is fixed by $\Gamma_E$. As in the reflex-norm construction of Book 124, there is a unique Galois-equivariant map

$$
(r_h)_*:X_*\bigl(\operatorname{Res}_{E/\mathbf Q}\mathbf G_m\bigr)
\longrightarrow X_*(T)                                               \tag{10.1}
$$

that sends the basis cocharacter corresponding to the chosen embedding $E\hookrightarrow\mathbf C$ to $\mu_h$. It defines

$$
r_h:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m\longrightarrow T,   \tag{10.2}
$$

the **reciprocity morphism** of the special point.

Existence and uniqueness follow exactly from the permutation-lattice argument: every embedding is $\sigma$ times the chosen one, equivariance forces its image to be $\sigma\mu_h$, and this is independent of the lift because $\Gamma_E$ fixes $\mu_h$.

If $j:T\to G$ sends $h$ into $X$, the reciprocity morphism in $G$ is $j\circ r_h$. This functoriality is immediate from (10.1). In a CM realization it is precisely the reflex norm of the CM type followed by the ambient torus embedding.

For the ambient datum itself, apply the same construction after projecting to $G^{\mathrm{ab}}$. The conjugacy class of

$$
\mu^{\mathrm{ab}}=\nu\circ\mu_h
$$

is a single cocharacter because the quotient is commutative. Its field of definition is contained in $E(G,X)$, so corestriction from $E(G,X)$ gives (6.4). Equivalently, (6.4) sends the distinguished basis cocharacter to $\mu^{\mathrm{ab}}$.

The construction can be read directly in the three families. For the Hilbert datum, determinant sends every local cocharacter to weight one, so

$$
r_{(G,X)}:\mathbf G_m\longrightarrow
\operatorname{Res}_{F/\mathbf Q}\mathbf G_m
$$

is the diagonal embedding. On finite ideles, a rational idele is extended to every place of $F$. For the quaternionic datum, the exponent vector of the abelianized cocharacter is the characteristic vector of $\Sigma$; its Galois orbit sum defines a monomial map from the reflex-field torus to $\operatorname{Res}_{F/\mathbf Q}\mathbf G_m$. For the basic group this monomial acts on the narrow quotient (8.7): the cocharacter labels determine the translating idele, while the Hamiltonian sign restrictions enter separately through the exact rational subgroup $\operatorname{Nrd}(G(\mathbf Q)_+)=F_+^\times$. A central modification uses its own target torus and the quotient (8.8). For the unitary datum, the exponents are the signature multiplicities $r_\varphi$ and $2-r_\varphi$, followed by the determinant--multiplier torus (9.8). Thus the Hodge labels compute the reciprocity multiplier, while the exact abelianized quotient determines where that multiplier acts.

The ambient map generally contains less information than $r_h$ for a special point. Abelianization forgets the position of the CM torus inside the derived group. It is nevertheless exactly the information needed for connected components, because strong approximation has already erased the derived finite adelic coordinate there.

### 10.2 Special-point reciprocity

**Theorem 10.1.** Let $x=[h,g]\in\operatorname{Sh}_K(G,X)(\mathbf C)$ be special in one of the selected Hilbert, quaternionic, or unitary data, with its compatible PEL-exact realization directly or through the chosen central modification. Let $T=\operatorname{MT}(h)$ and let $E(h)$ be its reflex field. For $s\in\mathbf A_{E(h)}^\times$, the canonical Galois action is

$$
x^{\operatorname{Art}_{E(h)}(s)}
=[h,r_h(s_f)g].                                                       \tag{10.3}
$$

The right side depends only on the idele class and is compatible with changing level and with morphisms of Shimura data.

**Proof strategy.** Realize the torus as the Mumford--Tate torus of a polarized CM Hodge structure and invoke the CM comparison theorem, then check principal ideles and level directly.

**Proof.** In each selected family, the compatible PEL-exact realization, directly or on the chosen central modification, identifies $h$ with the Hodge structure on a polarized CM abelian variety, possibly with a product CM algebra and prescribed endomorphisms. Book 125 proves that arithmetic Artin acts on its finite adelic lattice by the reflex norm, giving exactly (10.3) in the quotient convention (1.1).

If $s$ is replaced by $as$ with $a\in E(h)^\times$, then $\operatorname{Art}(a)=1$. The toric reflex construction sends $a$ to $r_h(a)\in T(\mathbf Q)$, and left multiplication by that rational point identifies the two right-hand representatives. If $s$ changes within the open subgroup mapping into $gKg^{-1}\cap T(\mathbf A_f)$, the level coset is unchanged. Thus the formula depends only on the appropriate idele class. For a morphism $f:G\to G'$, applying $f$ to (10.3) and using $r_{f(h)}=f\circ r_h$ proves functoriality. Projection of $gK'$ to $gK$ proves level compatibility. $\square$

The theorem is not a definition disguised as a proof. The Galois action on the abelian variety is algebraic, whereas $r_h$ was built from a Hodge cocharacter. Their equality is the substantive CM reciprocity theorem proved in Book 125.

### 10.3 Variance and normalization

There are three equivalent ways to write (10.3), and mixing them causes an inverse error.

Our double quotient uses $G(\mathbf Q)$ on the left and the level coset on the right. A finite adelic element $t$ changes the lattice by the inverse transform, so the CM ideal action $t*A$ is represented by $[h,tg]$. Hence arithmetic Frobenius corresponds to $r_h(\pi)g$.

If one instead encodes a level structure as a right trivialization and lets $G(\mathbf A_f)$ act on the right, the same geometric operation is written $g\mapsto gt^{-1}$. Likewise, geometric Artin reciprocity replaces $s$ by $s^{-1}$. Either change introduces one inverse; making both changes introduces two and returns to the displayed direction.

The quickest test is a CM elliptic curve. For an unramified prime $\mathfrak p$ of its reflex field, arithmetic Frobenius sends the lattice class to the inverse reflex ideal, as in Book 125. Formula (10.3) has precisely that effect. A convention predicting the direct ideal instead has one inverse misplaced.

### 10.4 Passage to components

Special-point reciprocity lives in a maximal torus of $G$, while a component remembers only the maximal abelian quotient of $G$. Projecting the former to the latter must agree with the ambient reflex map, or pointwise and componentwise descent would conflict.

Project (10.3) through $\nu:G\to G^{\mathrm{ab}}$. For a special point $h$, functoriality of cocharacters gives

$$
\nu\circ r_h
=r_{(G,X)}\circ N_{E(h)/E(G,X)}                                     \tag{10.4}
$$

on ideles, with the evident interpretation if the fields are embedded conjugately.

**Proof.** Both sides are morphisms from $\operatorname{Res}_{E(h)/\mathbf Q}\mathbf G_m$ to $G^{\mathrm{ab}}$. Let $e_\tau$ be the cocharacter basis vector indexed by an embedding $\tau:E(h)\hookrightarrow\overline{\mathbf Q}$. The norm morphism sends

$$
(N_{E(h)/E})_*e_\tau=e_{\tau|_E};
$$

the sum over extensions occurs on the contravariant character lattice, not on this cocharacter basis. The right side of (10.4) therefore sends $e_\tau$ to $\tau(\nu\mu_h)$. By the defining equivariance of the special reciprocity map, the left side has the same value. Equality on every $e_\tau$ proves equality of torus morphisms. $\square$

Global reciprocity is norm-functorial, so (10.4) shows that the action of $\operatorname{Gal}(\overline{\mathbf Q}/E(h))$ on the component containing $x$ is the restriction of the ambient action (6.5). This agreement is crucial: canonical descent of points and canonical descent of components are not two unrelated prescriptions.

## 11. Canonical models

We now pass from a rule on CM points to an algebraic variety over the reflex field. The proof has two distinct parts. Density makes the rule unique. Existence comes from a symplectic algebraization and effective descent; CM reciprocity identifies the resulting descent datum with the required arithmetic rule.

### 11.1 Definition by arithmetic special points

Let $E=E(G,X)$. A **canonical model** of $\operatorname{Sh}_K(G,X)$ is a normal quasi-projective variety $S_K/E$ together with an isomorphism

$$
S_K\otimes_{E,\iota}\mathbf C
\simeq\operatorname{Sh}_K(G,X)(\mathbf C)                             \tag{11.1}
$$

of complex algebraic varieties such that for every special point $x=[h,g]$, every $\sigma\in\operatorname{Gal}(\overline{\mathbf Q}/E(h))$, and every idele $s$ with $\operatorname{Art}_{E(h)}(s)=\sigma|_{E(h)^{\mathrm{ab}}}$,

$$
\sigma(x)=[h,r_h(s_f)g].                                              \tag{11.2}
$$

The formula is interpreted after base change to $\overline{\mathbf Q}$. It determines the field of definition of $x$ from an open idele-class stabilizer. If $T=\operatorname{MT}(h)$, put

$$
C_{x,f}=r_h^{-1}\!\left(T(\mathbf Q)
\bigl(T(\mathbf A_f)\cap gKg^{-1}\bigr)\right)
\subset\mathbf A_{E(h),f}^{\times}
$$

and

$$
U_x=E(h)^\times C_{x,f}E(h)_\infty^{\times,0}/E(h)^\times
\subset\mathbf A_{E(h)}^\times/E(h)^\times.                       \tag{11.3}
$$

The connected archimedean factor is present because $r_h$ uses only $s_f$. By global class field theory, $U_x$ cuts out a finite abelian extension of $E(h)$.

Normality is part of the definition because the construction at coarse level uses normalization and because equality of rational maps is then controlled in codimension one. Quasi-projectivity permits effective finite Galois descent.

### 11.2 Uniqueness

A rule on a sparse set of algebraic points would not determine a variety. The decisive geometric input is that CM points are dense in these domains, so agreement with reciprocity propagates from special points to every algebraic morphism.

We need a density statement.

**Lemma 11.1 (density of special points).** In each Hilbert, quaternionic, or unitary domain considered here, special points are analytically dense in every connected component and hence Zariski dense in every algebraic component.

**Proof strategy.** Construct one special point in each component, then use rational conjugates. This makes both rationality and density explicit and avoids the unjustified claim that a nearby rational endomorphism automatically has a CM centralizer compatible with every prescribed tensor.

**Proof.** First choose a special point $h_0$ in the component. In the Hilbert case, choose a CM quadratic extension of $F$ with one complex embedding above each real embedding and let it act on its two-dimensional $F$-space. In the quaternionic case, choose a CM quadratic extension nonsplit at every ramified place of $B$ and with the orientations prescribed by $X^+$; weak approximation and the local quaternion embedding criterion give an embedding into $B$. In the unitary case, choose a maximal commutative CM algebra stable under the adjoint involution and choose its CM type with multiplicities equal to the signature function. The local sign conditions are open, and weak approximation in the self-adjoint subspace globalizes the choice. In every case the centralizer of the chosen regular element is a torus and the resulting Hodge map factors through it, so $h_0$ is special.

Now the groups occurring here have weak approximation at the archimedean places. For $\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_2$ and $\operatorname{Res}_{F/\mathbf Q}B^\times$ this is ordinary additive weak approximation in the ambient matrix or quaternion algebra, since invertibility is open. For the unitary group, the Cayley transform

$$
Y\longmapsto(1-Y)(1+Y)^{-1}
$$

is a rational chart from the skew-adjoint Lie algebra to a neighborhood of the identity; additive weak approximation in that Lie algebra gives density near the identity, and translates give density in the required real component. Hence $G(\mathbf Q)\cap G(\mathbf R)^+$ is dense in $G(\mathbf R)^+$. The rational conjugates $q h_0q^{-1}$ are still special and are dense in the orbit $X^+$. Repeating the construction in each component proves analytic density. An algebraic closed subset is analytically closed; if it contained all special points, analytic density would force it to contain the whole component. Thus the special points are Zariski dense as well. $\square$

**Theorem 11.2 (uniqueness).** A canonical model, if it exists, is unique up to a unique $E$-isomorphism compatible with (11.1).

**Proof.** Let $S$ and $S'$ be two models. Their chosen complex identifications give a complex-algebraic isomorphism $f_\mathbf C:S_\mathbf C\to S'_\mathbf C$. Every special point is $\overline{\mathbf Q}$-rational by (11.2), and $f_\mathbf C$ carries it to the correspondingly labelled special point. If $\tau\in\operatorname{Aut}(\mathbf C/\overline{\mathbf Q})$, then $f_\mathbf C$ and ${}^\tau f_\mathbf C$ agree on all special points. Lemma 11.1 makes those points dense, so the two morphisms agree. The graph of $f_\mathbf C$ is therefore fixed by $\operatorname{Aut}(\mathbf C/\overline{\mathbf Q})$ and descends to $\overline{\mathbf Q}$. Since its equations use finitely many algebraic coefficients, it is defined over a finite extension $L/E$.

For $\sigma\in\operatorname{Gal}(L/E)$, the maps $f$ and ${}^\sigma f$ have the same value on every special point: both values are forced by (11.2). Density gives ${}^\sigma f=f$. Faithfully flat Galois descent therefore produces an $E$-morphism $S\to S'$. Apply the same argument to $f_\mathbf C^{-1}$; the two descended composites become the identity over $\mathbf C$ and hence are the identity over $E$. Thus the descended map is an isomorphism. Any two such isomorphisms agree on the dense special set and are equal. $\square$

### 11.3 Existence in the three families

The existence argument uses the following algebraization lemma, proved here in the form needed.

**Lemma 11.3 (PEL-exact algebraization).** Let $(G,X)$ be one of the three data above. Suppose either that there is a faithful symplectic representation

$$
\rho:(G,X)\longrightarrow
(\operatorname{GSp}(V,\psi),\mathfrak H_g^\pm)                       \tag{11.4}
$$

whose Hodge types on $V$ are $(-1,0)$ and $(0,-1)$ and which is **PEL-exact** in the following sense: there are a semisimple rational algebra $D$, a positive involution $*$, and a determinant polynomial such that $G$ is exactly the group of $D$-linear similitudes of $(V,\psi)$ and $X$ is exactly the positive Hodge locus with that determinant polynomial. Alternatively, suppose $(G,X)$ admits a central modification $(G^\natural,X^\natural)$ with this property, the same adjoint datum and reflex field, and an isogeny on derived groups. At a sufficiently small neat level, $\operatorname{Sh}_K(G,X)(\mathbf C)$ has a normal quasi-projective algebraization. In the direct case it is an open-and-closed union in a fine PEL scheme; in the central-modification case it is obtained from finitely many such components by finite central quotients.

**Proof strategy.** First represent the exact PEL functor. Then prove that its analytic uniformization is the desired double quotient in both directions. Only after that identification may normalization and finite central descent be used.

**Proof.** Choose a $*$-stable order $\mathcal O\subset D$, a lattice $\Lambda\subset V$ stable under $\mathcal O$, and an integral multiple of $\psi$. Shrinking level, choose a full similitude level $N\geq3$. The PEL functor classifies polarized abelian schemes with $\mathcal O$-action, Rosati involution $*$, the prescribed characteristic polynomial on the Lie algebra, and level. Its diagonal is finite because polarized automorphisms are finite. A sufficiently high symmetric polarization power embeds every object in a fixed projective space; the Hilbert scheme represents the embedded family, while the group law, $\mathcal O$-action, Rosati equality, determinant polynomial, and level are closed or locally closed conditions. Quotienting the framing group after level has killed inertia gives a fine quasi-projective scheme.

Over $\mathbf C$, its points yield polarized Hodge structures

$$
(V_{\mathbf R}/\Lambda,J_h)
$$

with the prescribed level. Positivity gives the Riemann bilinear relations. PEL-exactness says that a Hodge structure occurring in this moduli problem factors through $G$ and belongs to $X$; conversely every $(h,g)$ supplies the lattice $g\widehat\Lambda\cap V(\mathbf Q)$, the stated endomorphisms, polarization, determinant multiplicities, and level. Changing the rational trivialization acts by $G(\mathbf Q)$ and changing the integral trivialization acts by $K$. These inverse constructions identify the selected open-and-closed union of complex points with

$$
G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/K).
$$

This two-sided verification is what the former phrase “the Hodge condition is algebraic” failed to supply: a faithful symplectic representation alone would not identify the tensor stabilizer with $G$.

There are two equivalent level conventions. A chosen primitive $N$th root of unity gives a symplectic basis and an ambient fine moduli scheme over $\mathbf Q(\zeta_N)$. Alternatively, a similitude level identifies the Weil pairing with the group scheme $\mu_N$ without selecting one generator and is defined over $\mathbf Q$. In the first convention, Galois permutes the cyclotomic components through the multiplier; taking their union gives the second convention. Thus the auxiliary cyclotomic field does not enlarge the reflex field.

In the central-modification case, the two groups have the same connected domain and commensurable arithmetic images in the common adjoint group. Indeed, the isogeny on derived groups has finite kernel and cokernel on each arithmetic lattice after shrinking level. Thus every connected component for $G$ is finitely dominated by a PEL component for $G^\natural$; the component sets themselves are finite by Chapter 6. Take the normal finite quotient of each dominating PEL component by its effective deck group and then take the finite disjoint union indexed by the components of $G$. Its analytification is the required quotient and it is quasi-projective. Two choices of central modification have a common refinement given by the connected fiber product over the adjoint group. The resulting finite birational comparisons between normal algebraizations are isomorphisms. $\square$

The final independence statement is important. A tensor-corestriction representation and a hyperbolically enlarged representation can land in Siegel spaces of different dimensions, and their ambient universal abelian schemes need not agree. The common-refinement argument in the proof, not equality of function fields by itself, gives finite birational maps in both directions; normality then makes them inverse. Canonical descent therefore belongs to $(G,X)$, not to the auxiliary representation.

For the common-norm Hilbert group, the rational multiplier makes the symplectic representation direct because every real factor is active with the same determinant. The full group $\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_2$ is treated by the central-modification clause. In the mixed quaternionic case, a common-norm lift is not automatic, as Section 8.1 explained. One instead uses a compatible trace-pairing or tensor-corestriction central modification supplied by the rank-two structure, and one must verify PEL-exactness rather than infer it from faithfulness. When a split corestriction gives the smaller tensor representation, odd tensor parity is symplectic and even tensor parity is repaired by the hyperbolic construction. This choice affects the auxiliary abelian dimension, not the adjoint Shimura datum or its canonical model.

For the realizations retained in the FLT route, that exactness is a calculation, not a new hypothesis hidden in terminology. In the Hilbert case the commutant of the $F$-action on $F^2$ gives precisely the common-determinant similitude group. In the quaternion trace-pairing construction, left and right multiplication are mutual commutants; imposing right-$B^{\mathrm{op}}$ linearity, the adjoint involution, and a rational multiplier recovers exactly the common-norm group of Book 123. A tensor-corestriction realization is used only after quotienting or detecting its recorded finite central kernel, so its stabilizer is the stated central modification rather than a larger orthogonal group. In the unitary case, $K$-linearity and preservation of the Hermitian adjoint recover (9.1) by definition. The determinant polynomial then selects exactly the Hodge conjugacy class computed in Chapters 7--9.

**Theorem 11.4 (existence of canonical models).** For every sufficiently small neat compact open $K$ and every Hilbert, quaternionic, or unitary datum of Chapters 7--9 satisfying the PEL-exact or central-modification hypothesis of Lemma 11.3, that algebraization admits a canonical model over $E(G,X)$. It satisfies (11.2).

**Proof strategy.** First descend over a finite Galois extension by transporting the algebraic tensor data. Then identify the descent action on a dense set of CM points using Book 125. The cocycle follows on that dense set and hence everywhere.

**Proof.** Choose a finite Galois extension $L/E(G,X)$ that splits the determinant labels, defines the finitely many geometric components, and dominates the fields used by the PEL-exact central modification. Lemma 11.3 gives a normal quasi-projective $L$-model $S_{K,L}$. We first construct algebraic descent maps without appealing to their desired values on points.

The moduli locus used in Lemma 11.3 is specified by two kinds of equations. The endomorphism, adjoint, and polarization tensors are rational and hence unchanged by Galois. The determinant condition says that for every element $a$ of the acting semisimple algebra, its characteristic polynomial on the Lie bundle is

$$
P_a(T)=\prod_{\varphi}(T-\varphi(a))^{r_\varphi},                   \tag{11.5}
$$

where the multiplicity tuple $(r_\varphi)$ is encoded by $\mu_h$. Its coefficients are fixed by the stabilizer of the cocharacter conjugacy class and hence lie in $E(G,X)$. For quaternionic data, the active-place indicator replaces $(r_\varphi)$ after a splitting. Thus Galois transports the PEL component union according to the same permutation of labels by which it transports the analytic component set.

Transport of the universal polarized abelian variety, its tensors, and its level gives algebraic isomorphisms on the PEL-exact cover. They commute with the finite effective deck groups used in Lemma 11.3, so normal finite quotient descent gives

$$
\phi_\sigma:S_{K,L}^\sigma\longrightarrow S_{K,L}.                 \tag{11.6}
$$

Because transport of coefficients is associative, these maps satisfy

$$
\phi_{\sigma\tau}=\phi_\sigma\circ{}^\sigma\!\phi_\tau           \tag{11.7}
$$

on the fine PEL scheme and therefore on its normal finite quotients. Thus they form an algebraic Galois descent datum on $S_{K,L}$.

It remains to identify this algebraically constructed datum as the canonical one. Let $x=[h,g]$ be special. Its symplectic realization is a polarized CM abelian variety with the tensors and level used above. Book 125 proves that transport by $\operatorname{Art}_{E(h)}(s)$ is the reflex transform $r_h(s_f)$, respecting precisely those tensors, the polarization multiplier, and the level. Hence (11.6) acts on every special point by (11.2). Lemma 11.1 shows that no different descent isomorphism could have the same property. Proposition 11.5 makes the descent effective, producing $S_K/E$. $\square$

There is no circular appeal to the desired canonical model in this proof. The initial algebraization comes from the complex moduli interpretation; CM reciprocity determines its Galois descent; density supplies equality and the cocycle; only then is the model over $E$ formed.

### 11.4 Effective descent

For completeness, we record the descent step used above.

**Proposition 11.5.** Let $L/E$ be finite Galois and let $Y/L$ be quasi-projective with isomorphisms

$$
\phi_\sigma:{}^\sigma Y\longrightarrow Y
$$

satisfying the cocycle identity. Then there is a quasi-projective $Y_0/E$, unique up to unique isomorphism, with $Y_0\otimes_E L\simeq Y$ and the prescribed descent datum. Normality and smoothness descend.

**Proof.** Choose an ample line bundle $\mathcal L$ on $Y$. The tensor product of its finitely many Galois transports, pulled back by the $\phi_\sigma$, has a natural linearization after taking a further positive tensor power to remove the scalar cocycle. A sufficiently large power embeds $Y$ equivariantly into a projective space over $L$ carrying a semilinear Galois action. Galois-invariant homogeneous coordinates descend the projective space and the invariant homogeneous ideal descends the closure of $Y$. An invariant affine complement descends as well, producing a quasi-projective $E$-scheme $Y_0$. Base change recovers $Y$ by faithful flatness. Local rings descend faithfully flatly, so integral closedness and smoothness descend. Uniqueness follows because morphisms satisfying the descent compatibility descend on affine covers. $\square$

Applied to Theorem 11.4, this proposition shows that the word “descent” is literal. It is not merely a prescription for Galois orbits of complex points.

## 12. Level descent and functoriality

A canonical model is most useful as part of a compatible tower. Level changes, finite quotients, morphisms of data, and Hecke translations must all descend. The reciprocity characterization makes the proof uniform.

### 12.1 The tower over the reflex field

Passing to a smaller compact open remembers more level structure. Canonical models should preserve this forgetful relation over the reflex field, not only after embedding into $\mathbf C$.

Let $K'\subset K$ lie in the cofinal system of sufficiently small neat levels covered by Theorem 11.4. The analytic map (5.3) sends a special point $[h,gK']$ to $[h,gK]$. By (10.3), Galois conjugation before or after this projection gives the same result. The uniqueness theorem therefore descends (5.3) to an $E(G,X)$-morphism

$$
S_{K'}\longrightarrow S_K.                                          \tag{12.1}
$$

For $K''\subset K'\subset K$, the two possible composites agree over $\mathbf C$ and hence over $E$. Thus the canonical models form an inverse system indexed by compact open levels.

The right action of $G(\mathbf A_f)$ also descends. For $a\in G(\mathbf A_f)$, (5.4) commutes with the left reciprocity multiplier because

$$
r_h(s_f)(ga)=(r_h(s_f)g)a.
$$

Uniqueness yields an $E$-morphism between the corresponding levels. This elementary associativity is why the side convention fixed in Chapter 1 matters.

### 12.2 Finite quotients and non-neat level

Let $K$ be arbitrary and choose a sufficiently small neat normal $K'\triangleleft K$ in the cofinal system of Theorem 11.4. The finite group $\Delta=K/K'$ acts algebraically on $S_{K'}$ over $E$ by the descended right action. Define

$$
S_K=S_{K'}/\Delta,                                                     \tag{12.2}
$$

taking the normal finite categorical quotient.

The result is independent of $K'$. If $K_1'$ and $K_2'$ are two choices, their intersection is neat and normal; quotienting first to either intermediate level and then by the remaining finite group gives the same normalization of the common function field. Its complex points are (1.1), including the finite stabilizers.

Formula (11.2) descends because the $\Delta$-action commutes with reciprocity. Thus (12.2) is the canonical model at non-neat level. It can have quotient singularities, and a universal abelian variety need not descend through stabilizers. The variety itself does descend; representability of a particular moduli functor is a separate assertion.

### 12.3 Morphisms and Hecke translations

Let

$$
f:(G,X)\longrightarrow(G',X')
$$

be a morphism and suppose $f(K)\subset K'$. Analytically it induces

$$
[h,g]\longmapsto[f\circ h,f(g)].                                     \tag{12.3}
$$

The reflex-field inclusion is $E(G',X')\subseteq E(G,X)$. After base change to $E(G,X)$, (12.3) descends canonically.

**Proof.** For a special $h$, functoriality gives $r_{f(h)}=f\circ r_h$. Applying (10.3) shows that (12.3) commutes with Galois on all special points. These are dense, so the analytic algebraic map is compatible with the descent data everywhere. Effective descent yields the required morphism. $\square$

The same proof applies to Hecke translations and to finite correspondences attached to $KaK$. Hence all Hecke correspondences in the generic Shimura tower are defined over the reflex field. This does not assert extension over integral models or a good-prime Eichler--Shimura relation; those require additional geometry.

### 12.4 Descent of connected components

The component formula (6.5) now has a geometric interpretation. Let $C$ be a geometric connected component of $S_K\otimes_E\overline{\mathbf Q}$. Its stabilizer in $\operatorname{Gal}(\overline{\mathbf Q}/E)$ is the inverse image, under Artin reciprocity, of the subgroup (6.6). Therefore $C$ descends to the corresponding finite abelian extension $E_C/E$.

**Proof.** Every component contains a special point by Lemma 11.1. For such a point, projection of special reciprocity to $G^{\mathrm{ab}}$ is (6.5) by (10.4). Hence an automorphism fixes the component exactly when its reciprocity element fixes the class in (6.3). The stabilizer is open, so its fixed field is finite. Since the component is open and closed after base change, its idempotent in the finite étale algebra of components is fixed by that stabilizer and descends to $E_C$. $\square$

For Hilbert data this recovers an action on narrow ideal classes. For the basic quaternionic group it gives the narrow quotient $F_+^\times\backslash\mathbf A_{F,f}^\times/\operatorname{Nrd}(K)$: orientation supplies the split-place signs and the rational norm theorem supplies the Hamiltonian signs. A quaternionic central modification instead uses its own exact quotient (8.8). For unitary data it gives the torus quotient subject to determinant--multiplier relation (9.8). In each case the connected canonical model over $E_C$ is obtained by selecting one idempotent, not by pretending the component was already defined over $E$.

## 13. The FLT package

The preceding constructions can now be read as one decision procedure. The parity of the totally real degree selects a quaternionic curve or a unitary surface; real ramification selects the domain; the Hodge cocharacter selects the reflex field; and reciprocity descends the entire adelic tower.

### 13.1 Curves, surfaces, and the parity split

Let $F$ be totally real. A quaternion algebra has an even total number of ramified places. To obtain a Shimura curve, choose $B/F$ split at exactly one real place and ramified at the other $d-1$ real places, adjusting finite ramification so the total is even. The resulting domain has dimension one and reflex field the embedded copy of $F$ singled out by the split place.

When the required global ramification and representation parity cannot be arranged in a curve without losing the desired automorphic packet, use a rank-two unitary group attached to a CM extension $K/F$. Choose signature $(1,1)$ at exactly two real places and definite signature elsewhere. The domain has dimension two. Choosing the Hermitian space anisotropic over $F$ makes the surface compact. The definite-place orientations are retained in the signature function and hence in its reflex field.

The symplectic representation has an independent parity issue. For a tensor of $d$ alternating two-dimensional representations, the tensor form is alternating when $d$ is odd and symmetric when $d$ is even. Book 123 proves this sign and supplies hyperbolic enlargement in the even case. That repair changes the auxiliary abelian variety but neither the adjoint domain nor the reciprocity morphism. Confusing geometric dimension with representation dimension is therefore a serious error: a one-dimensional Shimura curve can map to a high-dimensional Siegel space.

### 13.2 A reusable canonical-model theorem

**Theorem 13.1 (FLT Shimura package).** Let $(G,X)$ be one of the following:

1. the Hilbert datum for $\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_2$;
2. a quaternionic datum for $\operatorname{Res}_{F/\mathbf Q}B^\times$, or a connected central modification to which its adjoint Hodge map lifts, with at least one split real place;
3. a rank-two unitary similitude datum for a CM extension $K/F$, with at least one indefinite real place and with every rational simple adjoint factor active.

Assume in cases 2 and 3 that the selected rational group, or a central modification with the same adjoint datum and reflex field, carries the PEL-exact polarized weight-one realization specified by the algebra with involution, with rational multiplier. Assume also the rational transitivity on $\pi_0(X)$ verified in Section 6.1 when the simplified component formula is used. Then:

- $(G,X)$ is a Shimura datum and

  $$
  \dim X=\begin{cases}
  [F:\mathbf Q],&\text{Hilbert},\\
  |\Sigma|,&\text{quaternionic},\\
  \sum_\tau p_\tau q_\tau,&\text{unitary};
  \end{cases}                                                         \tag{13.1}
  $$

- its reflex field is respectively $\mathbf Q$, the stabilizer field of $\Sigma$, or the stabilizer field of the signature function;
- every compact open contains a neat normal compact open of finite index;
- at neat level the complex quotient is a smooth quasi-projective variety, and at arbitrary level it is a normal quasi-projective variety with finite quotient singularities;
- connected components are given by (6.3), with the explicit Hilbert formula (7.5), the basic quaternionic narrow formula (8.7), the exact central-modification formula (8.8), and the unitary torus formula (9.9);
- for every level there is a unique canonical model over the reflex field, characterized by

  $$
  [h,g]^{\operatorname{Art}_{E(h)}(s)}=[h,r_h(s_f)g]                  \tag{13.2}
  $$

  at every special point;
- level maps, morphisms of data, and Hecke translations descend over the appropriate reflex field;
- geometric components descend over the finite abelian extensions determined by the ambient reciprocity map on (6.3).

**Proof.** Propositions 7.1, 8.1, and 9.1 verify the axioms and dimensions. Sections 7.3, 8.3, and 9.3 compute the reflex fields from Definition 4.1. Proposition 5.1 gives neat levels. Lemma 11.3 gives algebraization, Theorem 11.4 and Proposition 11.5 give canonical descent, and Section 12 treats arbitrary level and functoriality. Theorem 6.1 computes components, while Section 12.4 identifies their fields of definition. Finally, Theorem 10.1 gives (13.2). $\square$

This theorem deliberately stops at the generic canonical model. Smooth or semistable integral models, extension of correspondences at bad primes, and cohomological realizations require local geometric hypotheses not present in a rational Shimura datum.

### 13.3 Hypothesis ledger

The central statements depend on different hypotheses, and none should be carried into another column silently.

| Assertion | Necessary input | What fails without it |
|---|---|---|
| Shimura axioms | connected reductive $G$, Hodge types (3.1), Cartan involution, active rational factors | the orbit need not be Hermitian or effective |
| quaternionic positive dimension | at least one split real place | the proposed $h$ is adjoint-trivial |
| unitary dimension formula | nondegenerate Hermitian form and fixed signatures | the domain and cocharacter are undefined |
| symplectic algebraization | PEL-exact polarized weight-one representation, directly or through a compatible central modification with the same reflex field | faithfulness alone does not identify the Shimura quotient with a PEL locus |
| component reduction | strong approximation for the simply connected derived group | the torus quotient may miss a derived obstruction |
| simplified component labels | transitivity of $G(\mathbf Q)$ on $\pi_0(X)$ | one must retain the orbit set (6.2a) |
| basic quaternionic narrow formula | rational reduced-norm theorem and every split real place active | Hamiltonian sign restrictions are lost, producing a false one-sign quotient |
| effective manifold at level $K$ | neatness of the adjoint arithmetic action | adjoint torsion produces quotient singularities; ineffective central units are separate |
| special reciprocity | arithmetic Artin convention and the CM comparison theorem | the Galois action or its inverse is undetermined |
| canonical descent | algebraization, density, reciprocity, effective finite descent | a rule on CM points alone is not a variety over $E$ |
| individual component over $E_C$ | openness of the stabilizer in (6.6) | a component need not be defined over the ambient reflex field |

Two boundary cases deserve emphasis. At non-neat level, a coarse canonical variety still exists, but universal objects can be obstructed by automorphisms. At a datum with compact real factors, those factors satisfy the Cartan axiom; they violate the nontriviality axiom only if an entire rational simple factor is invisible.

The dependency chain is now closed. Adèles and ray quotients provide the topology and finite class groups. Rank-two inner forms and symplectic representations provide the groups and polarized embeddings. CM types provide reflex norms, and CM reciprocity proves the special-point Galois formula. Every further conclusion in this book follows from those inputs and the descent arguments supplied here.

### 13.4 Conclusion

A Shimura datum is the precise interface between Hodge theory and arithmetic groups. The Deligne torus turns a complex structure into a cocharacter; the three Shimura axioms turn its real conjugacy class into a Hermitian symmetric domain. Finite adèles add level, and neatness turns arithmetic orbifolds into manifolds without changing the cofinal tower.

For the Hilbert datum every real embedding is active, so the domain is $(\mathfrak H^\pm)^d$, the reflex field is $\mathbf Q$, and components form a narrow class quotient. A quaternion algebra suppresses the ramified real factors in the domain: the active set $\Sigma$ determines the dimension and reflex field, while reduced norm computes the basic group’s components as a narrow quotient. The signs have two sources—orientation at split active places and positivity of rational reduced norms at Hamiltonian places. A quaternionic central modification retains its own abelianized quotient. A rank-two unitary group replaces the active-set indicator by a signature function; its $(1,1)$ places contribute dimension, and its definite orientations can still enlarge the reflex field. In all three families, strong approximation transfers the component problem from the derived group to an explicit torus quotient.

The arithmetic structure is fixed by one normalization. With arithmetic Artin reciprocity and the left adelic convention,

$$
[h,g]^{\operatorname{Art}_{E(h)}(s)}=[h,r_h(s_f)g].
$$

The reflex morphism is built from $\mu_h$, and the main theorem of complex multiplication identifies its lattice action with Galois conjugation. Special points are dense, so this rule uniquely determines descent. A symplectic algebraization supplies a quasi-projective complex variety, the CM rule supplies a cocycle, and effective descent produces the canonical model over $E(G,X)$. Level maps, Hecke translations, and morphisms commute with the same formula and therefore descend with it.

The resulting package is exactly what the FLT cases require: correctly typed Hilbert, quaternionic, and unitary Shimura data; explicit reflex fields; finite and computable component sets; cofinal neat levels; canonical models at every level; and a reciprocity law that controls both special points and geometric components. The analytic quotient, the adelic tower, and the Galois action are no longer separate constructions. They are three views of one canonical arithmetic variety.
