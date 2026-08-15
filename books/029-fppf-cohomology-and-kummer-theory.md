# fppf Cohomology and Kummer Theory

## Contents

1. [Cohomology as descent with obstructions](#1-cohomology-as-descent-with-obstructions)
   - [From gluing to derived invariants](#11-from-gluing-to-derived-invariants)
   - [The fppf site](#12-the-fppf-site)
   - [Sheaves and representable examples](#13-sheaves-and-representable-examples)
   - [Global sections and cohomology](#14-global-sections-and-cohomology)
2. [The elementary cohomological machine](#2-the-elementary-cohomological-machine)
   - [Complexes and low degrees](#21-complexes-and-low-degrees)
   - [Long exact sequences and boundaries](#22-long-exact-sequences-and-boundaries)
   - [Functoriality, base change, and products](#23-functoriality-base-change-and-products)
   - [Cech cochains and their limits](#24-cech-cochains-and-their-limits)
   - [Leray and descent spectral sequences](#25-leray-and-descent-spectral-sequences)
3. [Degree one and torsors](#3-degree-one-and-torsors)
   - [Torsors as twisted trivial objects](#31-torsors-as-twisted-trivial-objects)
   - [The classification theorem](#32-the-classification-theorem)
   - [The abelian group law](#33-the-abelian-group-law)
   - [The boundary of a short exact sequence](#34-the-boundary-of-a-short-exact-sequence)
4. [Line bundles and additive vanishing](#4-line-bundles-and-additive-vanishing)
   - [The Picard interpretation](#41-the-picard-interpretation)
   - [Quasi-coherent sheaves on affine schemes](#42-quasi-coherent-sheaves-on-affine-schemes)
   - [Consequences for affine descent](#43-consequences-for-affine-descent)
5. [The fppf Kummer sequence](#5-the-fppf-kummer-sequence)
   - [Roots of units in every characteristic](#51-roots-of-units-in-every-characteristic)
   - [Exactness as a sequence of sheaves](#52-exactness-as-a-sequence-of-sheaves)
   - [The fundamental Kummer exact sequence](#53-the-fundamental-kummer-exact-sequence)
   - [Explicit torsors and the boundary map](#54-explicit-torsors-and-the-boundary-map)
   - [Classification by a powered line bundle](#55-classification-by-a-powered-line-bundle)
6. [Kummer theory over fields and local rings](#6-kummer-theory-over-fields-and-local-rings)
   - [Fields](#61-fields)
   - [Local and semilocal rings](#62-local-and-semilocal-rings)
   - [Characteristic dividing the exponent](#63-characteristic-dividing-the-exponent)
   - [Comparison with the etale topology](#64-comparison-with-the-etale-topology)
7. [Higher Kummer classes and the Brauer group](#7-higher-kummer-classes-and-the-brauer-group)
   - [The cohomological Brauer group](#71-the-cohomological-brauer-group)
   - [The second Kummer segment](#72-the-second-kummer-segment)
   - [Azumaya algebras and projective linear torsors](#73-azumaya-algebras-and-projective-linear-torsors)
   - [Fields and central simple algebras](#74-fields-and-central-simple-algebras)
   - [Degree, period, and splitting](#75-degree-period-and-splitting)
8. [Cup products and symbol classes](#8-cup-products-and-symbol-classes)
   - [Tensor pairings and cup products](#81-tensor-pairings-and-cup-products)
   - [Kummer symbols](#82-kummer-symbols)
   - [Cyclic algebras](#83-cyclic-algebras)
   - [Formal identities](#84-formal-identities)
   - [Quaternion and norm examples](#85-quaternion-and-norm-examples)
9. [Cohomology of finite-flat group schemes](#9-cohomology-of-finite-flat-group-schemes)
   - [Why points are insufficient](#91-why-points-are-insufficient)
   - [Exact sequences and torsor fibers](#92-exact-sequences-and-torsor-fibers)
   - [Change of topology](#93-change-of-topology)
   - [Examples in residue characteristic](#94-examples-in-residue-characteristic)
10. [Isogenies and geometric Kummer maps](#10-isogenies-and-geometric-kummer-maps)
    - [The general isogeny sequence](#101-the-general-isogeny-sequence)
    - [Abelian schemes](#102-abelian-schemes)
    - [Picard varieties and divisor classes](#103-picard-varieties-and-divisor-classes)
    - [Naturality under morphisms](#104-naturality-under-morphisms)
11. [Descent boundaries in concrete form](#11-descent-boundaries-in-concrete-form)
    - [Lifting a section](#111-lifting-a-section)
    - [Lifting a torsor](#112-lifting-a-torsor)
    - [Central extensions and degree two](#113-central-extensions-and-degree-two)
    - [Compatibility diagrams](#114-compatibility-diagrams)
12. [Relative and base-change phenomena](#12-relative-and-base-change-phenomena)
    - [Restriction along a morphism](#121-restriction-along-a-morphism)
    - [Finite locally free norm and transfer](#122-finite-locally-free-norm-and-transfer)
    - [Norms and Kummer classes](#123-norms-and-kummer-classes)
    - [Descent and transitivity](#124-descent-and-transitivity)
13. [Calculational patterns](#13-calculational-patterns)
    - [Projective space and factorial schemes](#131-projective-space-and-factorial-schemes)
    - [Dedekind schemes](#132-dedekind-schemes)
    - [Strictly henselian local rings](#133-strictly-henselian-local-rings)
    - [Arithmetic in the coefficient](#134-arithmetic-in-the-coefficient)
    - [A hypothesis ledger](#135-a-hypothesis-ledger)
14. [Synthesis](#14-synthesis)
    - [The low-degree dictionary](#141-the-low-degree-dictionary)
    - [A reliable Kummer protocol](#142-a-reliable-kummer-protocol)
    - [Conclusion](#143-conclusion)

## 1. Cohomology as descent with obstructions

### 1.1 From gluing to derived invariants

Faithfully flat descent answers an existence question: compatible objects over a cover descend. Cohomology begins one step earlier and one step later. It asks how compatibility is recorded, how different gluings are distinguished, and what obstructs a partial gluing problem from being completed. In low degrees the answers have an especially geometric form:

$$
H^0=\text{global sections},\qquad
H^1=\text{torsors},\qquad
H^2=\text{central gluing obstructions}.
$$

The slogan is useful only after its terms are made precise. A section may exist locally without existing globally. Choices of local lifts then differ on double overlaps; those differences form a $1$-cocycle. If the differences themselves can only be chosen locally, their incompatibility on triple overlaps forms a $2$-cocycle. The connecting maps in long exact cohomology sequences turn this procedure into a canonical construction independent of all choices.

The fppf topology is the natural setting when finite group schemes need not be etale. For example, if the characteristic divides $n$, the roots-of-unity group scheme $\mu_n$ is nonreduced, but taking an $n$th root of a unit still becomes possible after a finite faithfully flat extension. Kummer theory therefore remains exact in the fppf topology without any invertibility hypothesis on $n$. That coefficient-uniform fact is the organizing result of this book.

The substantial geometric inputs are precise. Book 10 supplies effective faithfully flat descent
for affine and finite schemes, quasi-coherent sheaves, line bundles, affine group schemes, and
finite locally free torsors; these are the scheme-effectivity cases used below. Book 28 supplies
represented quotients and exact sequences of finite locally free commutative group schemes,
together with the theorem that multiplication by $n$ on an abelian scheme of relative dimension
$g$ is finite locally free and faithfully flat of degree $n^{2g}$. Neither source uses the
cohomological conclusions proved here: their torsor and root-cover calculations are obtained
directly from descent and finite projective Hopf algebras. We recall the parts needed to build the
cohomological argument and use no later Galois-cohomology or duality theorem.

### 1.2 The fppf site

Fix a scheme $X$. The **small fppf site** $X_{\mathrm{fppf}}$ has as objects morphisms $U\to X$ that are locally of finite presentation. A covering of $U$ is a family $\{U_i\to U\}$ of flat morphisms locally of finite presentation whose images jointly cover $U$. Fiber products supply pullbacks. All cohomology in this book is taken on this site. Thus no comparison with a differently sized site is being used silently.

The requirement that objects be locally of finite presentation is stable under base change and composition. A Zariski open cover is an fppf cover, and every etale cover is fppf. A finite locally free surjection of positive rank is fppf. Thus the topology sees ordinary gluing, separable algebraic gluing, and nonreduced finite-flat gluing at once.

The distinction between a covering family and a single faithfully flat map remains important. Locally on an affine target, any fppf family admits a finite affine refinement and may be represented by one faithfully flat algebra. This reduction permits explicit Cech computations, but the site itself remembers all refinements. Cohomology is independent of which convenient cover is initially chosen.

### 1.3 Sheaves and representable examples

A presheaf $F$ of sets on $X_{\mathrm{fppf}}$ assigns $F(U)$ to every $U\to X$ and restriction maps to arrows. It is a **sheaf** if, for every covering $\{U_i\to U\}$, the sequence

$$
F(U)\longrightarrow \prod_iF(U_i)
\rightrightarrows \prod_{i,j}F(U_i\times_UU_j)
$$

is an equalizer. For group-valued presheaves the equalizer is taken in groups. This says that compatible local sections glue uniquely.

Every $X$-scheme $Y$ represents an fppf sheaf

$$
h_Y(U)=\operatorname{Hom}_X(U,Y).
$$

Indeed, morphisms descend faithfully and effectively under fppf covers. Important abelian sheaves include

$$
\mathbf G_a(U)=\Gamma(U,\mathcal O_U),\qquad
\mathbf G_m(U)=\Gamma(U,\mathcal O_U)^\times,
$$

the constant sheaf associated with an abelian group, roots of unity $\mu_n=\ker([n]:\mathbf G_m\to\mathbf G_m)$, and the sheaf represented by any commutative group scheme over $X$. A quasi-coherent $\mathcal O_X$-module $\mathcal F$ gives the additive sheaf $U\mapsto\Gamma(U,f^*\mathcal F)$.

A sequence $F'\to F\to F''$ of sheaves is exact when its sheaf kernel and image agree. Equivalently, the kernel is computed sectionwise, while a section of $F''(U)$ belongs to the image sheaf exactly when it lifts after an fppf cover of $U$. Surjectivity as sheaves therefore means **local** liftability, not surjectivity on $U$-valued points. This distinction is indispensable for Kummer theory.

### 1.4 Global sections and cohomology

For an abelian sheaf $F$, define

$$
\Gamma(X,F)=F(X).
$$

The category of abelian sheaves has enough injectives, and $\Gamma(X,-)$ is left exact. Its right derived functors are the **fppf cohomology groups**

$$
H^q_{\mathrm{fppf}}(X,F)=R^q\Gamma(X,F),\qquad q\ge 0.
$$

Concretely, choose an injective resolution $F\to I^\bullet$ and take

$$
H^q_{\mathrm{fppf}}(X,F)=H^q(\Gamma(X,I^\bullet)).
$$

Different resolutions give canonically isomorphic groups. The abstract construction is valuable because it produces long exact sequences and functoriality automatically. Its geometric meaning in degrees $0$, $1$, and $2$ will be proved below.

We abbreviate $H^q(X,F)$ when the topology is clear. One must never infer that higher fppf cohomology vanishes merely because a cover trivializes a class: every cohomology class is locally zero on a sufficiently rich site in many common situations. The obstruction is whether those local trivializations glue.

## 2. The elementary cohomological machine

The purpose of this chapter is to isolate the formal mechanism used repeatedly later. Once boundary maps and their naturality are understood, Kummer theory becomes a precise conversion device: multiplication modulo $n$ in degree zero is converted into torsion in Picard and Brauer groups in higher degree.

### 2.1 Complexes and low degrees

A cochain complex $C^\bullet$ is a sequence

$$
C^0\xrightarrow{d^0}C^1\xrightarrow{d^1}C^2\longrightarrow\cdots,
\qquad d^{q+1}d^q=0.
$$

Its cocycles and coboundaries are $Z^q=\ker d^q$ and $B^q=\operatorname{im}d^{q-1}$, and $H^q=Z^q/B^q$. Degree zero contains elements satisfying a compatibility condition; degree one identifies compatible transition data modulo change of local trivialization; degree two measures failure of a proposed transition datum to satisfy the triple-overlap condition.

An injective sheaf is acyclic for global sections. Hence an injective resolution replaces $F$ by objects on which global sections retain enough exactness to expose all successive failures of exactness. This is the algebra behind the obstruction interpretation.

### 2.2 Long exact sequences and boundaries

Let

$$
0\longrightarrow F'\xrightarrow{i}F\xrightarrow{p}F''\longrightarrow0
$$

be a short exact sequence of abelian fppf sheaves. It induces a natural long exact sequence

$$
\begin{aligned}
0&\to H^0(X,F')\to H^0(X,F)\to H^0(X,F'')
\xrightarrow{\delta^0}H^1(X,F')\\
&\to H^1(X,F)\to H^1(X,F'')
\xrightarrow{\delta^1}H^2(X,F')\to\cdots.
\end{aligned}
$$

Here is the algebraic proof. Resolve the three sheaves compatibly by injectives so as to obtain a short exact sequence of complexes

$$
0\to I'^\bullet\to I^\bullet\to I''^\bullet\to0.
$$

Given a cocycle $c\in I''^q$, lift it to $b\in I^q$. Its differential maps to zero, so $db=i(a)$ for a unique $a\in I'^{q+1}$. Since $i(da)=d(i(a))=d^2b=0$, the element $a$ is a cocycle. Changing $b$ or the representative $c$ changes $a$ by a coboundary. Thus $[c]\mapsto[a]$ defines $\delta^q$. A direct diagram chase gives exactness at every term.

This construction already explains the geometry: lift locally, apply the compatibility operator, and record the resulting defect in the kernel.

### 2.3 Functoriality, base change, and products

A morphism $f:Y\to X$ induces a morphism of sites and a pullback map

$$
f^*:H^q(X,F)\longrightarrow H^q(Y,f^*F).
$$

For representable commutative groups this is ordinary base change of torsors in degree one. If a diagram of short exact sequences commutes, the induced maps commute with every connecting homomorphism. This **naturality of boundaries** follows either from the lifting construction or from functorial injective resolutions.

Finite products of abelian sheaves are biproducts, and derived global sections preserve them, so

$$
H^q(X,F_1\times\cdots\times F_r)
\simeq \prod_{j=1}^rH^q(X,F_j).
$$

Filtered colimits require additional hypotheses and will not be used implicitly. Nor will we assume that arbitrary base change commutes with cohomology; pullback always exists, but being an isomorphism is a separate theorem.

### 2.4 Cech cochains and their limits

For a single fppf cover $p:U\to X$, write $U^{[r]}$ for the $(r+1)$-fold fiber product over $X$. For an abelian sheaf $F$, the alternating pullbacks define the Cech complex

$$
F(U)\longrightarrow F(U^{[1]})\longrightarrow F(U^{[2]})\longrightarrow\cdots.
$$

In multiplicative notation, a $1$-cocycle $g\in F(U\times_XU)$ satisfies

$$
p_{23}^*g\,p_{12}^*g=p_{13}^*g
$$

on $U\times_XU\times_XU$. Replacing a local trivialization by $a\in F(U)$ changes $g$ by the coboundary $p_2^*a\,(p_1^*a)^{-1}$.

There is a canonical map from Cech cohomology for a fixed cover to derived cohomology. In degree one it gives exactly the torsor obtained by descent, and every torsor is represented after choosing a trivializing cover. Thus the colimit over all covers computes $H^1$ for abelian sheaves. A single cover need not compute all higher cohomology: its terms may themselves have cohomology. The Cech-to-derived spectral sequence

$$
E_1^{p,q}=H^q(U^{[p]},F)\Longrightarrow H^{p+q}(X,F)
$$

records the missing information. We use explicit Cech $2$-cocycles only when a cover has been chosen and verify that the resulting derived class is choice-independent.

### 2.5 Leray and descent spectral sequences

A map $f:Y\to X$ has two stages of taking sections: first over inverse images of objects of $X$, then over $X$ itself. Deriving this composite produces the Leray spectral sequence

$$
E_2^{p,q}=H^p(X,R^qf_*F)\Longrightarrow H^{p+q}(Y,F).
$$

Its low-degree edge sequence is

$$
0\to H^1(X,f_*F)\to H^1(Y,F)
\to H^0(X,R^1f_*F)\to H^2(X,f_*F)\to H^2(Y,F).
$$

The middle arrow asks whether a class on $Y$ is locally pulled back from $X$; the next arrow is its descent obstruction. This is the same local-to-global mechanism already seen in cocycles, now organized without choosing one fixed cover.

For a cover $U\to X$, form its Cech nerve $U^{[p]}$. Resolve $F$ injectively on each term and totalize the resulting double complex. Filtering by Cech degree gives

$$
E_1^{p,q}=H^q(U^{[p]},F)\Longrightarrow H^{p+q}(X,F).
$$

Filtering in the other direction recovers the augmented Cech complex. If every $U^{[p]}$ is $F$-acyclic, all rows with $q>0$ vanish and the ordinary Cech complex computes derived cohomology. This supplies the precise criterion that was missing from the naive assertion that one cover always computes cohomology.

For quasi-coherent additive coefficients on an affine scheme, one constructs an affine hypercover by repeatedly refining matching objects by affine fppf covers. Every row is an Amitsur complex for a faithfully flat algebra and is exact by the contracting-homotopy argument after faithful base change. The total complex is therefore exact in positive degree. This fills in the descent step in Theorem 4.2: the proof uses acyclic affine hypercovers, not the unsupported claim that an arbitrary fixed cover is automatically acyclic.

Spectral sequences will be used only through such edge maps and collapse criteria. Their role is bookkeeping: they distinguish cohomology of the cover from incompatibility among its pieces and prevent a local vanishing statement from being mistaken for global vanishing.

## 3. Degree one and torsors

Degree one is where cohomology becomes unmistakably geometric. The local zero object has automorphism group $G$; twisting its gluing maps by a $G$-cocycle produces a $G$-torsor. Effective descent then says that every cocycle really produces an object.

### 3.1 Torsors as twisted trivial objects

Let $G$ be a group sheaf on $X_{\mathrm{fppf}}$. A right $G$-torsor is a sheaf $P$ with a right action such that $P$ is locally nonempty and

$$
P\times G\longrightarrow P\times P,\qquad(p,g)\longmapsto(p,pg)
$$

is an isomorphism. When $G$ is represented by a flat group scheme locally of finite presentation, representable torsors are fppf-locally copies of $G$. For finite locally free $G$, descent proves that every sheaf torsor is represented by a finite locally free $X$-scheme of the same rank.

Choose a cover $U\to X$ and a section $s\in P(U)$. On $U\times_XU$, the two pullbacks $s_1,s_2$ differ uniquely by $g$: $s_2=s_1g$. On the triple overlap, uniqueness gives $g_{13}=g_{12}g_{23}$, with the order adjusted according to the chosen right-action convention. A new section changes $g$ by a coboundary. Thus a torsor determines a nonabelian Cech $1$-cohomology class.

This agrees with the descent convention of Book 10. There the transition from the $i$th right-torsor coordinate to the $j$th is left translation by $h_{ij}=g_{ij}^{-1}$, so

$$
h_{ik}=h_{jk}h_{ij}
$$

is exactly the inverse of $g_{ik}=g_{ij}g_{jk}$. We use the point-difference elements $g_{ij}$ below. For abelian coefficients the order disappears, while the projective-linear boundary in Section 7.3 retains the displayed convention explicitly.

### 3.2 The classification theorem

**Theorem 3.1 (torsor classification).** If $G$ is an abelian fppf sheaf on $X$, there is a natural bijection

$$
H^1_{\mathrm{fppf}}(X,G)
\simeq\{\text{isomorphism classes of $G$-torsors on $X$}\}.
$$

The trivial cohomology class corresponds to the trivial torsor $G$.

**Proof.** A torsor admits a trivializing fppf cover. The preceding construction yields a Cech cocycle, well defined modulo refinement and coboundary, hence a class in $H^1(X,G)$. Conversely, start with a cocycle $g$ on a cover $U\to X$. Take the trivial torsor $G_U$ and identify its two pullbacks over $U\times_XU$ by translation by $g$. The cocycle identity is exactly the descent condition on the triple overlap. Effective fppf descent produces a sheaf $P$, its $G$-action, and the torsor identity. If $G$ is representable in the standard finite-flat or affine situations, effective descent for schemes gives a representing scheme. Coboundary-equivalent cocycles produce isomorphic torsors, and an isomorphism of descended torsors yields such a coboundary after pullback. The two constructions are inverse. Finally, the identity cocycle descends the untwisted copy of $G$. $\square$

For a nonabelian $G$, the same argument gives a pointed set customarily denoted $H^1(X,G)$, but no natural group structure. Higher derived cohomology is used here only for abelian coefficients.

### 3.3 The abelian group law

When $G$ is commutative, the product of cocycles defines addition in $H^1$. Geometrically, if $P$ and $Q$ are $G$-torsors, their sum is the contracted product

$$
P\mathbin{\wedge^G}Q=(P\times_XQ)/G,
$$

where $h\in G$ acts by $(p,q)h=(ph,qh^{-1})$. Locally both torsors are trivial, and the quotient is another copy of $G$; descent therefore constructs the quotient without requiring a general quotient theorem. The inverse torsor uses the action through $g\mapsto g^{-1}$, and the trivial torsor is the identity.

This description proves that the torsor-classification bijection respects the abelian group law: local cocycles multiply exactly as contracted products do.

### 3.4 The boundary of a short exact sequence

Consider an exact sequence of abelian sheaves

$$
0\to A\to B\xrightarrow{q}C\to0.
$$

For $c\in C(X)$, form the sheaf of lifts

$$
P_c=X\times_{c,C,q}B.
$$

Local surjectivity of $q$ makes $P_c$ locally nonempty, and translation by $A$ is simply transitive. Hence $P_c$ is an $A$-torsor.

**Proposition 3.2.** Under Theorem 3.1, the connecting map sends

$$
\delta^0(c)=[P_c]\in H^1(X,A).
$$

In particular, $\delta^0(c)=0$ if and only if $c$ lifts to a global section of $B$.

**Proof.** Choose local lifts $b_i$. Their differences $b_j-b_i$ lie in $A$ and form the Cech cocycle of $P_c$. This is precisely the cocycle produced by the connecting-homomorphism construction. Triviality means that after modifying the $b_i$ by local $A$-sections they agree, hence descend to a global lift. $\square$

## 4. Line bundles and additive vanishing

The two most basic group sheaves behave strikingly differently. A $\mathbf G_m$-torsor is a line bundle and therefore carries genuine global geometry. A torsor under a quasi-coherent additive sheaf over an affine scheme is always trivial. These facts turn abstract low-degree cohomology into familiar algebra.

### 4.1 The Picard interpretation

Let $\operatorname{Pic}(X)$ be the group of isomorphism classes of invertible $\mathcal O_X$-modules under tensor product.

**Theorem 4.1.** There is a natural group isomorphism

$$
H^1_{\mathrm{fppf}}(X,\mathbf G_m)\simeq\operatorname{Pic}(X).
$$

**Proof.** From a line bundle $L$, take the sheaf $\operatorname{Isom}(\mathcal O_X,L)$ of frames. It is locally nonempty and scalar multiplication makes it a $\mathbf G_m$-torsor. Conversely, from a torsor $P$, form the contracted product

$$
P\mathbin{\wedge^{\mathbf G_m}}\mathbf A^1,
$$

where $\mathbf G_m$ acts on $\mathbf A^1$ by scalar multiplication. Locally this is the trivial rank-one bundle, and descent makes it a line bundle. A frame of the resulting bundle recovers $P$. Tensor product corresponds to contracted product, so the bijection is a group isomorphism. $\square$

The same proof works in the Zariski, etale, and fppf topologies because line bundles are already Zariski locally trivial. Consequently their degree-one $\mathbf G_m$-cohomology groups agree.

### 4.2 Quasi-coherent sheaves on affine schemes

**Theorem 4.2 (fppf acyclicity on affines).** Let $X=\operatorname{Spec}R$ and let $M$ be an $R$-module, viewed as the quasi-coherent additive sheaf $\widetilde M$. Then

$$
H^q_{\mathrm{fppf}}(X,\widetilde M)=0\qquad(q>0).
$$

**Proof strategy.** Faithfully flat descent gives exactness of the augmented Amitsur complex for a faithfully flat algebra. Affine fppf hypercovers reduce the derived calculation to such complexes in every simplicial degree, as explained in Section 2.5.

More explicitly, for $R\to S$ faithfully flat, the augmented complex

$$
0\to M\to S\otimes_RM\to S\otimes_RS\otimes_RM\to\cdots
$$

is exact. Exactness may be checked after tensoring with $S$, where an extra degeneracy inserting $1$ provides a contracting homotopy; faithful flatness reflects exactness. Resolve every matching object of an affine hypercover by another affine faithfully flat cover. The associated double complex has exact positive Amitsur rows, while its degree-zero equalizers recover the original quasi-coherent module by descent. The spectral sequence of the total complex therefore has cohomology only in degree zero, where it is $M$. Since such hypercovers calculate sheaf cohomology, the sheaf has no positive derived global sections. $\square$

In particular,

$$
H^q_{\mathrm{fppf}}(\operatorname{Spec}R,\mathbf G_a)=0\quad(q>0).
$$

The affine hypothesis is essential. For a nonaffine scheme, quasi-coherent cohomology can be nonzero; passage to the fppf site does not provide an affine-acyclicity argument on the whole scheme.

### 4.3 Consequences for affine descent

An additive torsor over an affine scheme has a global point and is therefore trivial. In elementary terms, affine-linear equations whose differences satisfy a faithfully flat cocycle can be solved globally. This is the cohomological shadow of effective descent for modules.

By contrast, $H^1(X,\mathbf G_m)=\operatorname{Pic}(X)$ may be nonzero even for affine $X$. Multiplicative gluing records projective rank-one modules, not merely elements of an additive module. This contrast foreshadows Kummer theory: an $n$th-root equation is multiplicative, and its failure to have a global solution can propagate into the Picard group.

## 5. The fppf Kummer sequence

Kummer theory starts from the elementary map $u\mapsto u^n$. Its force comes from reading this map as a morphism of sheaves rather than only as a homomorphism on global units. Globally, units need not possess $n$th roots. Fppf-locally, they always do. The kernel remembers all roots of unity scheme-theoretically, including nilpotents when the residue characteristic divides $n$.

Throughout this chapter $n\ge1$ is an integer. No assumption is made that $n$ is invertible on the base.

### 5.1 Roots of units in every characteristic

For an $X$-scheme $U$, multiplication by $n$ on $\mathbf G_m$ is

$$
[n]:\mathbf G_m(U)\longrightarrow\mathbf G_m(U),\qquad u\longmapsto u^n.
$$

Its scheme-theoretic kernel is

$$
\mu_n=\operatorname{Spec}_X\mathcal O_X[T]/(T^n-1).
$$

The residue classes $1,T,\ldots,T^{n-1}$ give a basis, so $\mu_n$ is finite locally free of rank $n$. If $n$ is invertible on $X$, the derivative $nT^{n-1}$ is a unit along $T^n=1$, and $\mu_n$ is finite etale. If $X$ has characteristic $p$ and $p\mid n$, it need not be reduced. For example,

$$
\mu_p=\operatorname{Spec}k[T]/((T-1)^p)
$$

over a field $k$ of characteristic $p$. Its single geometric point still has scheme-theoretic length $p$.

### 5.2 Exactness as a sequence of sheaves

**Theorem 5.1 (fppf Kummer sequence).** For every scheme $X$ and every $n\ge1$, the sequence of abelian fppf sheaves

$$
1\longrightarrow\mu_n\longrightarrow\mathbf G_m
\xrightarrow{[n]}\mathbf G_m\longrightarrow1
$$

is exact.

**Proof.** The first map identifies $\mu_n$ with the kernel by its defining equation. It remains to prove local surjectivity of $[n]$. Let $U=\operatorname{Spec}A$ and $a\in A^\times$. Set

$$
B=A[T]/(T^n-a).
$$

Because the polynomial is monic, $B$ is free over $A$ with basis $1,T,\ldots,T^{n-1}$. The image of $T$ is a unit, with inverse $a^{-1}T^{n-1}$. The morphism $\operatorname{Spec}B\to\operatorname{Spec}A$ is finite locally free of rank $n$ and surjective: a finite free module of positive rank is faithfully flat. Over it, $a=T^n$. Thus every unit has an $n$th root after an fppf cover. The argument is affine-local and proves sheaf surjectivity. $\square$

The proof also identifies the fiber of $[n]$ over $a$:

$$
P_a=\operatorname{Spec}A[T]/(T^n-a).
$$

Multiplication of $T$ by $\mu_n$ makes $P_a$ a $\mu_n$-torsor. The torsor identity may be checked after adjoining a root, where $P_a$ becomes $\mu_n$ itself. Notice that separability played no role.

### 5.3 The fundamental Kummer exact sequence

Applying fppf cohomology and using $H^1(X,\mathbf G_m)=\operatorname{Pic}(X)$ gives

$$
\begin{aligned}
1&\to\mu_n(X)\to\Gamma(X,\mathcal O_X)^\times
\xrightarrow{(\cdot)^n}\Gamma(X,\mathcal O_X)^\times\\
&\xrightarrow{\delta}H^1(X,\mu_n)
\to\operatorname{Pic}(X)\xrightarrow{n}\operatorname{Pic}(X)
\to H^2(X,\mu_n)\to\cdots.
\end{aligned}
$$

Exactness yields the central short exact sequence.

**Corollary 5.2 (degree-one Kummer calculation).** There is a natural exact sequence

$$
0\longrightarrow
\Gamma(X,\mathcal O_X)^\times/\Gamma(X,\mathcal O_X)^{\times n}
\longrightarrow H^1(X,\mu_n)
\longrightarrow\operatorname{Pic}(X)[n]
\longrightarrow0.
$$

The right-hand map sends a $\mu_n$-torsor to the associated $\mathbf G_m$-torsor, hence to a line bundle whose $n$th tensor power is trivial. The sequence need not split canonically. A splitting would require choosing roots or trivializations compatibly, and there is usually no natural way to do so.

### 5.4 Explicit torsors and the boundary map

The unit class of $a\in\Gamma(X,\mathcal O_X)^\times$ maps to the torsor of its roots

$$
P_a=\{t:t^n=a\}.
$$

This follows directly from Proposition 3.2: $P_a$ is the fiber of $[n]$ over $a$. It is trivial precisely when $a$ has a global $n$th root. Multiplication gives

$$
[P_a]+[P_b]=[P_{ab}],
$$

because the contracted product sends $(s,t)$ to $st$.

There is also an intrinsic description of every $\mu_n$-torsor. A pair $(L,\varphi)$ consisting of a line bundle $L$ and an isomorphism

$$
\varphi:L^{\otimes n}\xrightarrow{\sim}\mathcal O_X
$$

defines the graded algebra

$$
\mathcal A=\mathcal O_X\oplus L^{-1}\oplus\cdots\oplus L^{-(n-1)},
$$

where multiplication across degree $n$ uses the inverse of the dual of $\varphi$. Then $P=\operatorname{Spec}_X\mathcal A$ is a $\mu_n$-torsor. Conversely, decomposing the regular representation of a $\mu_n$-torsor by the character grading recovers $(L,\varphi)$. If a basis $e$ of $L$ has $\varphi(e^n)=c$, the corresponding root coordinate satisfies $T^n=c^{-1}$. Thus multiplying $\varphi$ by a unit multiplies the root parameter by its inverse. This realizes Corollary 5.2 geometrically: the underlying $n$-torsion line bundle is the right-hand invariant, while units measure the possible trivialized case and the ambiguity in $\varphi$.

The grading argument is valid even when $n$ is not invertible: diagonalizable group schemes are represented by group-graded algebras, and no decomposition into geometric eigenspaces is being assumed.

### 5.5 Classification by a powered line bundle

Because this description is used repeatedly, we prove it without appealing to geometric eigenspaces.

**Theorem 5.3.** The groupoid of $\mu_n$-torsors over $X$ is equivalent to the groupoid of pairs $(L,\varphi)$, where $L$ is an invertible sheaf and $\varphi:L^{\otimes n}\simeq\mathcal O_X$. A morphism $(L,\varphi)\to(L',\varphi')$ is an isomorphism $u:L\to L'$ satisfying $\varphi'\circ u^{\otimes n}=\varphi$.

**Proof.** The coordinate Hopf algebra of $\mu_n$ is the group algebra of $\mathbf Z/n\mathbf Z$. A $\mu_n$-action on an affine algebra is therefore the same as a $\mathbf Z/n\mathbf Z$-grading. This assertion follows directly from the coaction: if

$$
\rho(a)=\sum_{i=0}^{n-1}a_i\otimes T^i,
$$

the counit gives $a=\sum_i a_i$, and coassociativity gives $\rho(a_i)=a_i\otimes T^i$. Linear independence of the basis $1,T,\ldots,T^{n-1}$ makes the sum direct. No division by $n$ occurs.

Let $P\to X$ be a torsor and put $\mathcal A=p_*\mathcal O_P$. Its coaction supplies

$$
\mathcal A=\bigoplus_{i\in\mathbf Z/n\mathbf Z}\mathcal A_i.
$$

Fppf-locally, $P$ is $\mu_n$, so each $\mathcal A_i$ is locally free of rank one, multiplication gives isomorphisms $\mathcal A_i\otimes\mathcal A_j\simeq\mathcal A_{i+j}$, and $\mathcal A_0=\mathcal O_X$. These facts descend because they are statements about maps of finite locally free modules. Put $L^{-1}=\mathcal A_1$. Repeated multiplication gives an isomorphism $L^{-n}\simeq\mathcal O_X$; the inverse of its dual is the equivalent power trivialization $\varphi:L^n\simeq\mathcal O_X$.

Conversely, from $(L,\varphi)$ construct

$$
\mathcal A=\mathcal O_X\oplus L^{-1}\oplus\cdots\oplus L^{-(n-1)}
$$

with multiplication reduced modulo $n$ using the inverse of the dual map $\mathcal O_X\to L^{-n}$. Its grading defines a $\mu_n$-action on $P=\operatorname{Spec}_X\mathcal A$. After an fppf cover trivializing $L$ and its power trivialization, the algebra becomes $\mathcal O_X[T]/(T^n-1)$ with its regular action. Hence the torsor identity holds locally and therefore globally. The two constructions recover one another, and their effect on morphisms is exactly the displayed compatibility. $\square$

Under tensor product,

$$
(L,\varphi)+(M,\psi)=(L\otimes M,\varphi\otimes\psi).
$$

The forgetful map to $\operatorname{Pic}(X)[n]$ has fiber over $L$ equal to the set of power trivializations modulo automorphisms of $L$. Since automorphisms are global units and changing $u$ changes $\varphi$ by $u^n$, this fiber is a torsor under $\Gamma(X,\mathcal O_X)^\times/\Gamma(X,\mathcal O_X)^{\times n}$. This recovers every arrow in Corollary 5.2 at the level of objects.

## 6. Kummer theory over fields and local rings

The general exact sequence becomes especially transparent when the Picard group vanishes. Fields and local rings are therefore the basic computational laboratories. They also show why fppf Kummer theory is genuinely more uniform than its etale counterpart.

### 6.1 Fields

For a field $K$, every one-dimensional vector space is free, so $\operatorname{Pic}(K)=0$. Corollary 5.2 gives

$$
H^1_{\mathrm{fppf}}(K,\mu_n)\simeq K^\times/K^{\times n}
$$

for every $n\ge1$, in every characteristic. The class of $a$ is represented by $K[T]/(T^n-a)$ with its $\mu_n$-action.

If $n$ is prime to $\operatorname{char}K$, $\mu_n$ is finite etale. After choosing a primitive $n$th root of unity in a separable closure, its geometric points form a cyclic Galois module. The same group may then be calculated by Galois cohomology. If $\operatorname{char}K=p\mid n$, the polynomial $T^p-a$ can be purely inseparable and the corresponding torsor has only one geometric point. A calculation based only on the separable closure would miss it, whereas the fppf calculation remains $K^\times/K^{\times n}$.

As a concrete example, for $K=k(t)$ in characteristic $p$, the class of $t$ in $K^\times/K^{\times p}$ is nonzero because the $t$-adic valuation of a $p$th power is divisible by $p$. The torsor $z^p=t$ is purely inseparable and nontrivial over $K$, although it becomes trivial on an fppf cover; it is invisible as a nontrivial finite etale cover.

### 6.2 Local and semilocal rings

Every finitely generated projective module of rank one over a local ring is free. More generally, every line bundle over the spectrum of a semilocal ring is trivial: choose generators over the finitely many maximal ideals and combine them using the Chinese remainder theorem. Hence for a semilocal ring $R$,

$$
H^1_{\mathrm{fppf}}(\operatorname{Spec}R,\mu_n)
\simeq R^\times/R^{\times n}.
$$

This statement does not assert that a root lies in $R$; it classifies the obstruction to such a root and says that every $\mu_n$-torsor has a global root-equation presentation. Over a general scheme, an $n$-torsion line bundle may prevent a single global equation.

If $R$ is a discrete valuation ring with fraction field $K$, the restriction map sends the class of a unit $u$ to its class in $K^\times/K^{\times n}$. A general element of $K^\times$ has the form $\pi^rv$ with $v\in R^\times$. For $n>1$, its valuation modulo $n$ supplies an extra invariant not present among torsors over $R$: the equation $z^n=\pi$ defines a finite flat cover of $R$, but it is not a $\mu_n$-torsor. Indeed, on the special fiber the point $z=0$ is fixed by the whole rank-$n$ group scheme $\mu_n$, contradicting simple transitivity. This cleanly separates Kummer torsors from arbitrary root covers. For $n=1$, both the coefficient group and every Kummer quotient are trivial, as the general exact sequence already shows.

### 6.3 Characteristic dividing the exponent

Let $k$ be a field of characteristic $p$. Frobenius gives the fppf-exact sequence

$$
1\to\mu_p\to\mathbf G_m\xrightarrow{(\cdot)^p}\mathbf G_m\to1.
$$

Consequently $H^1(k,\mu_p)=k^\times/k^{\times p}$. If $k$ is perfect this group is zero, although $\mu_p$ is still nonreduced. If $k$ is imperfect it can be large.

There is an additive analogue, the Artin--Schreier sequence

$$
0\to\underline{\mathbf Z/p\mathbf Z}\to\mathbf G_a
\xrightarrow{F-1}\mathbf G_a\to0.
$$

It is already etale-exact because the derivative of $T^p-T-a$ is $-1$. On an affine $k$-scheme, additive acyclicity yields

$$
H^1(X,\underline{\mathbf Z/p\mathbf Z})
\simeq\Gamma(X,\mathcal O_X)/(F-1)\Gamma(X,\mathcal O_X).
$$

The contrast is instructive: multiplicative $p$-torsion is infinitesimal and requires fppf covers, while additive Artin--Schreier torsion is etale.

### 6.4 Comparison with the etale topology

There is a morphism from the fppf site to the etale site because every etale cover is fppf. For a smooth commutative group scheme $G$, fppf and etale torsors agree: a smooth surjective morphism has sections etale-locally, so a fppf $G$-torsor is etale-locally trivial. In particular,

$$
H^1_{\mathrm{et}}(X,G)\simeq H^1_{\mathrm{fppf}}(X,G)
$$

for smooth $G$.

The comparison extends to all cohomological degrees for smooth commutative coefficients:

**Proposition 6.1 (smooth change of topology).** If $G\to X$ is a smooth commutative group scheme, then the natural maps

$$
H^q_{\mathrm{et}}(X,G)\longrightarrow H^q_{\mathrm{fppf}}(X,G)
$$

are isomorphisms for every $q\ge0$.

**Proof.** Let $\epsilon:X_{\mathrm{fppf}}\to X_{\mathrm{et}}$ be the comparison morphism. The direct image satisfies $\epsilon_*G=G$. We use the local-effacement criterion for its higher derived images. Represent a positive-degree fppf class on a hypercover and construct a refinement one matching level at a time. At each fixed level, the choices that correct the cocycle form a torsor under a finite product of pullbacks of $G$. That torsor is smooth over the matching object. A nonempty smooth fiber has a point after a finite separable residue-field extension, and the smooth-coordinate presentation then extends that point to a section over an etale neighborhood. Thus every matching lift can be made after an etale refinement. Induction through the finitely many levels relevant to the given degree produces an etale hypercover on which the class is zero. This proves

$$
R^q\epsilon_*G=0\qquad(q>0).
$$

The Leray spectral sequence for $\epsilon$ then has only its row $q=0$, and its edge maps are the displayed comparison maps. $\square$

For $\mu_n$, smoothness holds exactly where $n$ is invertible. Thus the etale Kummer sequence is exact when $n\in\mathcal O_X^\times$. If $n$ is not invertible, its last map need not be locally surjective etale. Over a field of characteristic $p$, no etale extension can adjoin a purely inseparable $p$th root. The fppf topology is therefore not a technical embellishment but the minimal familiar topology in which Kummer exactness is coefficient-uniform.

## 7. Higher Kummer classes and the Brauer group

The next segment of the Kummer long exact sequence links $n$-torsion line bundles to degree-two classes. Degree two is where local matrix algebras can fail to glue to a global endomorphism algebra and where central simple algebras live over fields. Care is needed: the Azumaya Brauer group and the full cohomological group are related but are not identical by definition on arbitrary schemes.

### 7.1 The cohomological Brauer group

Define

$$
\operatorname{Br}'(X)=H^2_{\mathrm{fppf}}(X,\mathbf G_m)_{\mathrm{tors}},
$$

the **cohomological Brauer group**. We retain the torsion subscript in the definition because $H^2(X,\mathbf G_m)$ need not be known a priori to be torsion for an arbitrary scheme.

An **Azumaya algebra** on $X$ is an $\mathcal O_X$-algebra $A$ that is fppf-locally isomorphic to a matrix algebra $\operatorname{End}(\mathcal O_X^r)$. Two Azumaya algebras are Morita equivalent if, after tensoring with endomorphism algebras of vector bundles, they become isomorphic. Morita classes form the **Azumaya Brauer group** $\operatorname{Br}(X)$ under tensor product.

There is a natural injective homomorphism

$$
\operatorname{Br}(X)\hookrightarrow H^2(X,\mathbf G_m),
$$

whose image is torsion; hence it lands in $\operatorname{Br}'(X)$. Equality holds for fields and in many geometric settings, but we will not silently identify the two groups on an arbitrary scheme.

### 7.2 The second Kummer segment

Continuing the long exact sequence gives

$$
\operatorname{Pic}(X)\xrightarrow{n}\operatorname{Pic}(X)
\longrightarrow H^2(X,\mu_n)
\longrightarrow H^2(X,\mathbf G_m)\xrightarrow{n}H^2(X,\mathbf G_m).
$$

Therefore:

**Theorem 7.1 (degree-two Kummer sequence).** For every scheme $X$ and $n\ge1$ there is a natural short exact sequence

$$
0\longrightarrow\operatorname{Pic}(X)/n\operatorname{Pic}(X)
\longrightarrow H^2(X,\mu_n)
\longrightarrow H^2(X,\mathbf G_m)[n]
\longrightarrow0.
$$

Since the right term is $n$-torsion, it lies in $\operatorname{Br}'(X)[n]$. Thus one may write the last term as $\operatorname{Br}'(X)[n]$.

The left map is itself a boundary. A line bundle $L$ is sent to the gerbe of its $n$th roots: over $U\to X$, its objects are pairs $(M,\alpha)$ with $\alpha:M^{\otimes n}\simeq L_U$. Locally such roots exist after trivializing $L$ and adjoining an $n$th root of the transition unit. Automorphisms of any root form $\mu_n$. A global root exists exactly when the class vanishes.

### 7.3 Azumaya algebras and projective linear torsors

For $r\ge1$, scalar matrices give an exact sequence of fppf sheaves

$$
1\longrightarrow\mathbf G_m\longrightarrow\operatorname{GL}_r
\longrightarrow\operatorname{PGL}_r\longrightarrow1.
$$

This is a central extension. Although the outer groups are nonabelian, there is a boundary of pointed sets

$$
\partial:H^1(X,\operatorname{PGL}_r)\longrightarrow H^2(X,\mathbf G_m).
$$

A $\operatorname{PGL}_r$-torsor twists the matrix algebra $M_r(\mathcal O_X)$ under conjugation and produces an Azumaya algebra of degree $r$. Conversely, the sheaf of algebra isomorphisms from $M_r$ to an Azumaya algebra of degree $r$ is a $\operatorname{PGL}_r$-torsor. The class $\partial(P)$ is its Brauer class.

To see the boundary, use the right-torsor convention $g_{ik}=g_{ij}g_{jk}$ and choose local lifts $\widetilde g_{ij}\in\operatorname{GL}_r$ of the $\operatorname{PGL}_r$ cocycle. On triple overlaps their defect is scalar:

$$
\widetilde g_{ij}\widetilde g_{jk}\widetilde g_{ik}^{-1}
=c_{ijk}I_r,
\qquad c_{ijk}\in\mathbf G_m.
$$

Associativity makes $(c_{ijk})$ a $2$-cocycle. Changing lifts changes it by a coboundary. It vanishes precisely when the projective cocycle lifts to a vector bundle frame cocycle, equivalently when the Azumaya algebra is an endomorphism algebra.

Tensoring Azumaya algebras corresponds to addition of the resulting $H^2(\mathbf G_m)$ classes. Passing to Morita equivalence removes the matrix-size choice. The injection of $\operatorname{Br}(X)$ follows because a zero cohomology class supplies compatible linear lifts, producing a vector bundle $E$ with $A\simeq\operatorname{End}(E)$. The precise torsion bound is proved in Section 7.5.

### 7.4 Fields and central simple algebras

Over a field $K$, Azumaya algebras are finite-dimensional central simple algebras. Every such algebra is $M_r(D)$ for a unique central division algebra $D$, and the Brauer class is that of $D$. Fppf descent of matrix algebras and the preceding cocycle construction give

$$
\operatorname{Br}(K)\simeq H^2_{\mathrm{fppf}}(K,\mathbf G_m).
$$

Here is the essential surjectivity argument. Proposition 6.1 identifies fppf and etale cohomology for $\mathbf G_m$. Cohomology classes are locally effaceable, so a degree-two class is killed by an etale covering of $\operatorname{Spec}K$. Quasi-compactness reduces the cover to a finite separable $K$-algebra, and one finite Galois extension $L/K$ dominates all of its field factors. Put $\Gamma=\operatorname{Gal}(L/K)$.

The Cech-to-derived spectral sequence for $\operatorname{Spec}L\to\operatorname{Spec}K$ now makes the descent calculation explicit. Every term of the Cech nerve is a finite product of fields, so its Picard group is zero. Hence a degree-two class whose restriction to $L$ vanishes comes from a Cech $2$-cocycle. After identifying the components of the nerve by $\Gamma$, this is a map

$$
c:\Gamma\times\Gamma\longrightarrow L^\times,
$$

with

$$
\sigma(c(\tau,\rho))c(\sigma,\tau\rho)
=c(\sigma,\tau)c(\sigma\tau,\rho).
$$

Multiplying by a coboundary if necessary, take $c(1,\sigma)=c(\sigma,1)=1$. Form the crossed-product algebra

$$
A_c=\bigoplus_{\sigma\in\Gamma}Lu_\sigma,
\qquad
u_\sigma\ell=\sigma(\ell)u_\sigma,
\qquad
u_\sigma u_\tau=c(\sigma,\tau)u_{\sigma\tau}.
$$

The cocycle identity is exactly associativity. Elements commuting with $L$ lie in $L$, and commuting also with every $u_\sigma$ forces them into $K$, so the center is $K$. After tensoring with $L$, the algebra acts faithfully on the $L$-space of functions $\Gamma\to L$ by twisted translation; comparing dimensions shows

$$
A_c\otimes_KL\simeq M_{|\Gamma|}(L).
$$

Thus $A_c$ is central simple. Replacing $c$ by a coboundary rescales the $u_\sigma$ and gives an isomorphic algebra, while addition of cocycles corresponds to tensor product up to Morita equivalence. Its descent boundary is $[c]$. Hence every cohomology class comes from a central simple algebra, and the construction is inverse to the projective-frame cocycle map.

Proposition 7.2 below shows that the class of $A_c$ is killed by its degree. Thus the right side is already torsion. Consequently Theorem 7.1 becomes

$$
0\to 0\to H^2(K,\mu_n)\to\operatorname{Br}(K)[n]\to0,
$$

because $\operatorname{Pic}(K)=0$. Thus

$$
H^2_{\mathrm{fppf}}(K,\mu_n)\simeq\operatorname{Br}(K)[n]
$$

without assuming $n$ prime to $\operatorname{char}K$.

### 7.5 Degree, period, and splitting

The **degree** of an Azumaya algebra $A$ is the integer $r$ for which it is locally $M_r$. The **period** of its Brauer class is its order in $\operatorname{Br}(X)$. These invariants measure different things: degree is the size of a representative, while period is the order of its obstruction class.

**Proposition 7.2.** The Brauer class of an Azumaya algebra of degree $r$ is annihilated by $r$.

**Proof.** There is an fppf-exact central sequence

$$
1\to\mu_r\to\operatorname{SL}_r\to\operatorname{PGL}_r\to1.
$$

The last map is locally surjective. First lift a projective matrix fppf-locally to an invertible matrix $g$; then adjoin an $r$th root of $\det(g)^{-1}$ by a finite free cover. Multiplying $g$ by that root gives determinant one. Given the $\operatorname{PGL}_r$-torsor of trivializations of $A$, its boundary therefore lifts to $H^2(X,\mu_r)$. Its image under $\mu_r\hookrightarrow\mathbf G_m$ is the Brauer class of $A$, by naturality of the two central-extension boundaries. The Kummer long exact sequence shows that every element in this image is killed by $r$. $\square$

Thus the period divides the degree. Tensor powers have classes

$$
[A^{\otimes m}]=m[A],
$$

so the period is the least positive $m$ for which $A^{\otimes m}$ is Morita-trivial. A finite faithfully flat map $Y\to X$ **splits** $A$ if $A_Y\simeq\operatorname{End}(E)$ for some vector bundle $E$ on $Y$. Every Azumaya algebra is split by its own $\operatorname{PGL}_r$-torsor, but a splitting over $Y$ alone does not make the class zero on $X$: the descent data of $E$ may close only projectively, and its scalar triple-overlap defect is the original Brauer cocycle.

For a finite etale map of constant degree $d$, the transfer constructed in Section 12.2 satisfies that restriction followed by corestriction multiplies a Brauer class by $d$. Hence if the map splits $A$, then $d[A]=0$. This is a second period bound, arising from the size of a splitting cover rather than the matrix degree. It also illustrates why restriction can destroy a class without faithfully flatness being able to recover a chosen trivialization.

## 8. Cup products and symbol classes

Kummer classes become more informative when multiplied. A pair of units then yields a degree-two class, and over fields this class is represented by a familiar central simple algebra. Cup products are also the mechanism behind the bilinearity of norm-residue symbols.

### 8.1 Tensor pairings and cup products

A bilinear pairing of abelian sheaves

$$
F\times G\longrightarrow H
$$

induces cup products

$$
H^p(X,F)\times H^q(X,G)\longrightarrow H^{p+q}(X,H).
$$

On Cech representatives, one pulls the first cochain to the initial faces, the second to the final faces, and applies the pairing. The Leibniz rule for the differential proves that cocycles map to cocycles and that coboundaries give coboundaries. Derived tensor products give the intrinsic construction and prove independence from covers.

Cup products are functorial in $X$ and in the coefficient pairing. They satisfy graded commutativity after composing with the switch map:

$$
x\smile y=(-1)^{pq}y\smile x.
$$

Connecting homomorphisms satisfy the corresponding Leibniz rule. These formal properties allow symbol identities to be proved without choosing splitting fields repeatedly.

### 8.2 Kummer symbols

Assume for the moment that a chosen primitive $n$th root $\zeta$ identifies the etale sheaf $\mu_n$ with the constant cyclic sheaf $\mathbf Z/n\mathbf Z$; in particular, $n$ is invertible on $X$. The universal tensor pairing gives

$$
\mu_n\times\mu_n\longrightarrow\mu_n^{\otimes2},
\qquad (u,v)\longmapsto u\otimes v.
$$

For units $a,b$, define

$$
(a,b)_n=\delta(a)\smile\delta(b)
\in H^2(X,\mu_n^{\otimes2}).
$$

Without choosing a primitive root, the natural target is the Tate-twisted coefficient $\mu_n^{\otimes2}$; it must not be casually replaced by $\mu_n$. The chosen $\zeta$ fixes the coefficient isomorphism

$$
\beta_\zeta:\mu_n^{\otimes2}\xrightarrow{\sim}\mu_n,
\qquad
\zeta^i\otimes\zeta^j\longmapsto\zeta^{ij}.
$$

Over a field containing $\zeta$, applying $\beta_\zeta$ sends the symbol to an element of $H^2(K,\mu_n)\simeq\operatorname{Br}(K)[n]$. This convention fixes the sign of the cyclic algebra below.

Bilinearity follows immediately:

$$
(aa',b)_n=(a,b)_n+(a',b)_n,
\qquad
(a,bb')_n=(a,b)_n+(a,b')_n.
$$

It therefore depends only on the classes of $a$ and $b$ modulo $n$th powers.

### 8.3 Cyclic algebras

Let $K$ contain a primitive $n$th root $\zeta$. For $a,b\in K^\times$, the **symbol algebra**

$$
(a,b)_{n,\zeta}
=K\langle x,y\rangle/(x^n-a,\ y^n-b,\ yx-\zeta xy)
$$

has dimension $n^2$. After adjoining an $n$th root $\alpha$ of $a$, the element $x$ becomes diagonalizable and the algebra becomes a matrix algebra; explicitly, $x$ acts diagonally on a basis and $y$ acts by cyclic shift with the final step multiplied by $b$. Hence it is central simple.

For completeness, over a field containing $\alpha$, take a basis $e_0,\ldots,e_{n-1}$ and set

$$
xe_i=\alpha\zeta^{-i}e_i,\qquad
ye_i=e_{i+1}\ (i<n-1),\qquad
ye_{n-1}=be_0.
$$

Then $x^n=a$, $y^n=b$, and $yx=\zeta xy$. The distinct eigenvalues of $x$ give all diagonal matrix units, and $y$ cycles them, so these operators generate $M_n$. Both algebras have dimension $n^2$, proving that the symbol algebra becomes $M_n$ after a finite separable extension and is therefore central simple.

**Proposition 8.1.** Under $H^2(K,\mu_n)\simeq\operatorname{Br}(K)[n]$ and the coefficient isomorphism $\beta_\zeta$, the Kummer cup product $(a,b)_n$ is exactly the Brauer class of $(a,b)_{n,\zeta}$.

**Proof.** Trivialize the root torsor of $a$ and use the right-torsor cocycle $\sigma(\alpha)/\alpha=\zeta^{i(\sigma)}$. With the initial-face/final-face cup convention of Section 8.1 and the map $\beta_\zeta$, cup product with the root cocycle of $b$ produces the scalar factor set for the crossed product in which a lift $y$ satisfies

$$
y\alpha=\zeta\alpha y,\qquad y^n=b.
$$

These are $yx=\zeta xy$, $x^n=a$, and $y^n=b$. If the root torsor is disconnected, perform the same calculation on its finite etale coordinate algebra: after splitting that algebra, the cocycle permutes its $n$ primitive idempotents cyclically and gives the same diagonal-and-shift matrices. Descent then gives the displayed symbol algebra over $K$. Thus the stated coefficient and torsor conventions produce the class itself, not its inverse. $\square$

### 8.4 Formal identities

The symbol satisfies

$$
(a,b)_n=-(b,a)_n
$$

after identifying the two tensor twists, by graded commutativity. For $n=2$ this says symmetry because $-1=1$ in $2$-torsion, matching quaternion algebras.

A particularly important relation is the Steinberg identity

$$
(a,1-a)_n=0
$$

for $a,1-a\in K^\times$ when $n$ is invertible and the coefficient isomorphism $\beta_\zeta$ has been fixed. This includes the cases in which $a$ has smaller Kummer order. Put

$$
E=K[t]/(t^n-a).
$$

The algebra $E$ is finite etale of rank $n$. Let $\sigma(t)=\zeta t$ and define an operator on $E$ by

$$
Y=m_{1-t}\circ\sigma,
$$

where $m_{1-t}$ denotes multiplication by $1-t$. Since

$$
\prod_{i=0}^{n-1}(1-\zeta^it)=1-t^n=1-a,
$$

we have $Y^n=1-a$. If $X=m_t$, then $YX=\zeta XY$. The resulting action of $(a,1-a)_{n,\zeta}$ on the $n$-dimensional space $E$ becomes the diagonal-and-cyclic-shift action after a separable splitting field. It therefore identifies the symbol algebra with $\operatorname{End}_K(E)$, so its Brauer class is zero. By Proposition 8.1 this is exactly the Steinberg relation for the cup-product symbol, not merely a consequence of bilinearity.

### 8.5 Quaternion and norm examples

Assume $\operatorname{char}K\ne2$. Since $-1$ is the unique primitive square root of unity, no coefficient choice is needed for $n=2$. The symbol algebra is the quaternion algebra

$$
(a,b)_2=K\langle i,j\rangle/(i^2-a,\ j^2-b,\ ji+ij).
$$

It has basis $1,i,j,ij$. Its center is $K$: commuting with $i$ kills the $j$ and $ij$ components, and then commuting with $j$ kills the $i$ component. After adjoining $\sqrt a$, define

$$
i\longmapsto
\begin{pmatrix}\sqrt a&0\\0&-\sqrt a\end{pmatrix},
\qquad
j\longmapsto
\begin{pmatrix}0&b\\1&0\end{pmatrix}.
$$

The relations hold and the four basis elements span $M_2$, so the algebra splits over $K(\sqrt a)$ and is central simple over $K$.

The algebra already splits over $K$ exactly when $b$ is a norm from the quadratic etale algebra $L=K[T]/(T^2-a)$. One direction is explicit. If $b=N(x+y\sqrt a)=x^2-ay^2$, then the element $x+y i$ has reduced norm $b$, and conjugating the standard crossed-product representation produces a two-dimensional $K$-module. Conversely, a split quaternion algebra has a nonzero zero divisor. Writing such a vector in the $L\oplus Lj$ presentation and comparing its two components yields $b=z\sigma(z)$ for some $z\in L^\times$. Thus

$$
(a,b)_2=0\quad\Longleftrightarrow\quad
b\in N_{L/K}(L^\times).
$$

This criterion immediately gives $(a,-a)_2=0$, since $-a=N(\sqrt a)$, and $(a,1-a)_2=0$, since $1-a=N(1+\sqrt a)$. Bilinearity gives further identities such as

$$
(a,b)_2+(a,c)_2=(a,bc)_2.
$$

For general $n$ with a primitive root $\zeta_n\in K$, let $L=K(\sqrt[n]{a})$ when this is a cyclic extension of degree $n$. The symbol algebra has crossed-product form

$$
L\oplus Ly\oplus\cdots\oplus Ly^{n-1},
\qquad y\ell=\sigma(\ell)y,\quad y^n=b.
$$

If $b=N_{L/K}(z)$, replace $y$ by $z^{-1}y$; the new semilinear generator has $n$th power one and acts as $\sigma$ on the $K$-space $L$. Multiplication by $L$ together with this action identifies the algebra with $\operatorname{End}_K(L)$. Conversely, if the algebra is split, take its simple $n$-dimensional module $V$. Restriction to the degree-$n$ field $L$ makes $V$ one-dimensional over $L$. For an $L$-basis vector $v$, write $yv=zv$. Semilinearity gives

$$
y^nv=N_{L/K}(z)v,
$$

while the defining relation gives $y^nv=bv$. Hence $b=N_{L/K}(z)$. We have proved

$$
(a,b)_{n,\zeta}=0
\quad\Longleftrightarrow\quad
b\in N_{L/K}(L^\times).
$$

If $T^n-a$ does not define a field of degree $n$, one uses the corresponding cyclic etale algebra or reduces to the actual order of the Kummer class; stating the degree-$n$ field criterion without this hypothesis would be false as written. The cohomological symbol remains defined and bilinear in all cases where $n$ is invertible and the coefficient twist is retained.

## 9. Cohomology of finite-flat group schemes

Finite locally free commutative group schemes are the natural coefficients for integral arithmetic. Their rank remains constant while their geometric points may collide. Fppf cohomology respects that scheme structure because it tests triviality after flat covers, not only after separable field extensions.

### 9.1 Why points are insufficient

Suppose $G$ is finite locally free over $X$. A $G$-torsor $P\to X$ is finite locally free of the same rank: after the fppf cover that trivializes it, it is $G$, and finite local freeness descends. The torsor identity

$$
G\times_XP\simeq P\times_XP
$$

controls infinitesimal stabilizers as well as ordinary points.

Over a field of characteristic $p$, each of $\underline{\mathbf Z/p\mathbf Z}$, $\mu_p$, and $\alpha_p$ has rank $p$, but their geometry differs. The first is etale, the second is multiplicative and infinitesimal, and the third is additive and infinitesimal. Their torsors are respectively Artin--Schreier equations, $p$th-root equations for units, and equations $z^p=a$ under translation. A separable closure trivializes the first kind but generally cannot trivialize the latter two.

### 9.2 Exact sequences and torsor fibers

Let

$$
0\longrightarrow G'\xrightarrow{i}G\xrightarrow{q}G''\longrightarrow0
$$

be an fppf-exact sequence of finite locally free commutative group schemes. Exactness means that $G'$ is the scheme-theoretic kernel and $q$ is a $G'$-torsor, equivalently a faithfully flat quotient. It gives

$$
0\to G'(X)\to G(X)\to G''(X)
\xrightarrow{\delta}H^1(X,G')\to H^1(X,G)\to H^1(X,G'')\to\cdots.
$$

For $x\in G''(X)$,

$$
\delta(x)=[X\times_{x,G''}G].
$$

This fiber is a finite locally free $G'$-torsor. Thus exactness at $G''(X)$ has a concrete meaning: $x$ lifts globally to $G(X)$ exactly when its lift torsor is trivial. Surjectivity of $G\to G''$ as an fppf sheaf does not imply surjectivity on $X$-points.

If $G'$ and $G''$ are finite locally free, an extension torsor has a finite locally free middle term and ranks multiply:

$$
|G|=|G'|\,|G''|
$$

on every connected component. This rank identity is proved after a torsor trivialization, not by counting geometric points.

### 9.3 Change of topology

If $G$ is finite etale, its torsors are finite etale and are classified by continuous cocycles of the etale fundamental group acting on a geometric fiber. Thus etale and fppf $H^1$ agree for $G$. More generally they agree in degree one for any smooth group scheme.

When $G$ is not smooth, fppf torsors need not become trivial etale-locally. The comparison map

$$
H^1_{\mathrm{et}}(X,G)\longrightarrow H^1_{\mathrm{fppf}}(X,G)
$$

may fail to be surjective. It would be wrong to replace $G$ by its group of geometric points: that operation discards connected infinitesimal fibers. Finite-flat exactness and cohomology are compatible precisely because both are formulated sheaf-theoretically in the same topology.

### 9.4 Examples in residue characteristic

Over a characteristic-$p$ affine scheme $X=\operatorname{Spec}R$, the exact sequence

$$
0\to\alpha_p\to\mathbf G_a\xrightarrow{F}\mathbf G_a\to0
$$

is fppf-exact. The map $F$ sends $x$ to $x^p$; local surjectivity follows by adjoining a root through the finite free algebra $R[T]/(T^p-a)$. Additive acyclicity gives

$$
H^1(X,\alpha_p)\simeq R/R^p.
$$

The class of $a$ is the torsor $T^p=a$ under translations $T\mapsto T+s$, $s^p=0$.

Compare $H^1(X,\mu_p)$ and $H^1(X,\alpha_p)$. The former receives $R^\times/R^{\times p}$ and may also contain $p$-torsion line bundles; the latter is $R/R^p$ on affines. Multiplicative and additive infinitesimal group schemes therefore encode different failures of Frobenius. The distinction survives even though each has rank $p$ and one geometric point over an algebraically closed field.

## 10. Isogenies and geometric Kummer maps

Kummer theory is not confined to $\mathbf G_m$. Whenever a homomorphism of commutative group schemes is a faithfully flat quotient with finite-flat kernel, its fibers define cohomology classes. For abelian schemes, multiplication by $n$ has exactly this form, producing the Kummer maps used in descent.

### 10.1 The general isogeny sequence

Let $\varphi:G\to H$ be a homomorphism of commutative fppf sheaves, assume $\varphi$ is locally surjective, and put $K=\ker\varphi$. Then

$$
0\to K\to G\xrightarrow{\varphi}H\to0
$$

is exact and yields an injection

$$
H(X)/\varphi G(X)\hookrightarrow H^1(X,K).
$$

The image consists exactly of the $K$-torsors whose extension of structure group to $G$ is trivial. The class of $h\in H(X)$ is represented by

$$
G_h=X\times_{h,H,\varphi}G,
$$

the scheme of $\varphi$-preimages of $h$. If $K$ is finite locally free and $\varphi$ is a $K$-torsor, so is $G_h$. The phrase **Kummer map** refers to this boundary homomorphism. It is injective on the indicated quotient by exactness; no choice of coordinates is involved.

### 10.2 Abelian schemes

Let $A\to S$ be an abelian scheme of relative dimension $g$. For every $n\ge1$, multiplication by $n$ is finite locally free and surjective of degree $n^{2g}$, with finite locally free kernel $A[n]$. Therefore

$$
0\longrightarrow A[n]\longrightarrow A\xrightarrow{[n]}A\longrightarrow0
$$

is fppf-exact, even where $n$ is not invertible. Its long exact sequence gives

$$
0\longrightarrow A(S)/nA(S)
\longrightarrow H^1(S,A[n])
\longrightarrow H^1(S,A)[n]
\longrightarrow0.
$$

For $P\in A(S)$, the class $\delta_n(P)$ is the finite-flat torsor of points $Q$ with $nQ=P$. It is trivial precisely when $P$ is globally divisible by $n$. In residue characteristic dividing $n$, $A[n]$ may have connected and nonreduced parts; fppf cohomology retains them automatically.

The group $H^1(S,A)$ classifies $A$-torsors. Its $n$-torsion measures torsors that become trivial after contracted multiplication by $n$. The exact sequence separates two sources of an $A[n]$-torsor: division of an actual section and torsion in the torsor group of $A$.

### 10.3 Picard varieties and divisor classes

When a smooth proper family has a representable relative Picard functor, its identity component $\operatorname{Pic}^0_{X/S}$ is often an abelian scheme. Multiplication by $n$ then gives Kummer classes of algebraically trivial line bundles:

$$
\operatorname{Pic}^0_{X/S}(S)/n
\hookrightarrow H^1(S,\operatorname{Pic}^0_{X/S}[n]).
$$

This construction must be distinguished from the sheaf Kummer boundary

$$
\operatorname{Pic}(X)/n\operatorname{Pic}(X)
\hookrightarrow H^2(X,\mu_n).
$$

The first is cohomology on the base with coefficients in the torsion of a Picard group scheme; the second is cohomology on the total space with coefficients in roots of unity. Relative comparison maps can relate them, but they do not have the same source or degree.

### 10.4 Naturality under morphisms

Suppose a square of isogenies commutes:

$$
\begin{array}{ccc}
G&\xrightarrow{\varphi}&H\\
\downarrow u&&\downarrow v\\
G'&\xrightarrow{\varphi'}&H'.
\end{array}
$$

It induces $u_K:K\to K'$ on kernels. Naturality of the boundary gives

$$
(u_K)_*(\delta_\varphi(h))=\delta_{\varphi'}(v(h)).
$$

Geometrically, pushing the lift torsor $G_h$ out along $K\to K'$ gives the lift torsor for $v(h)$. For multiplication maps on abelian schemes, any homomorphism $f:A\to B$ therefore satisfies

$$
f[n]_*\delta_{A,n}(P)=\delta_{B,n}(f(P)).
$$

The same statement holds after every base change $S'\to S$. These compatibilities make Kummer classes usable in descent diagrams rather than as isolated invariants.

## 11. Descent boundaries in concrete form

Connecting maps are sometimes presented as formal arrows in a long exact sequence. In applications one needs to know exactly what they construct. Degrees zero, one, and two correspond respectively to a torsor of lifts, an obstruction to lifting a torsor, and a central associativity defect.

### 11.1 Lifting a section

For $0\to A\to B\to C\to0$ and $c\in C(X)$, the boundary $\delta^0(c)$ is the $A$-torsor of lifts. Choose a cover $U_i\to X$ and lifts $b_i\in B(U_i)$. On overlaps,

$$
a_{ij}=b_j-b_i\in A(U_{ij}).
$$

Then $a_{ij}+a_{jk}=a_{ik}$ on triple overlaps, so $(a_{ij})$ is a cocycle. A different lift replaces it by a coboundary. This elementary formula covers root torsors, division torsors on abelian schemes, and fibers of finite-flat quotients.

### 11.2 Lifting a torsor

Let $P$ be a $C$-torsor. One seeks a $B$-torsor $Q$ whose quotient by $A$ is $P$. Choose a cover trivializing $P$ and let $c_{ij}\in C(U_{ij})$ be its cocycle. Refine the cover so that each $c_{ij}$ lifts to $b_{ij}\in B(U_{ij})$. On triple overlaps,

$$
a_{ijk}=b_{ij}+b_{jk}-b_{ik}\in A(U_{ijk}).
$$

The calculation $da=0$ makes this a $2$-cocycle. Its class is $\delta^1([P])\in H^2(X,A)$. It vanishes exactly when the lifts may be modified by $A$-cochains so as to satisfy the cocycle identity, in which case they descend a $B$-torsor lifting $P$. Thus exactness at $H^1(X,C)$ is a genuine obstruction statement, not just formal algebra.

### 11.3 Central extensions and degree two

The preceding construction survives when $B$ and $C$ are nonabelian provided $A$ is central in $B$. Then $H^1(B)$ and $H^1(C)$ are pointed sets, but the defect $a_{ijk}$ lies in the abelian sheaf $A$ and determines a class in $H^2(A)$. This is the mechanism for

$$
1\to\mathbf G_m\to\operatorname{GL}_r\to\operatorname{PGL}_r\to1.
$$

Centrality is decisive: without it, conjugation changes the coefficient system, and the obstruction belongs to a twisted form of $A$, not to one fixed abelian group. Statements about a boundary into ordinary $H^2(X,A)$ must therefore include centrality.

### 11.4 Compatibility diagrams

Given a commutative diagram with exact rows

$$
\begin{array}{ccccccccc}
0&\to&A&\to&B&\to&C&\to&0\\
 &&\downarrow&&\downarrow&&\downarrow\\
0&\to&A'&\to&B'&\to&C'&\to&0,
\end{array}
$$

the induced long exact sequences form a commutative ladder. In particular, the boundary $H^q(C)\to H^{q+1}(A)$ commutes with the vertical coefficient maps. Pullback along $Y\to X$ gives another such ladder. For Kummer theory, a morphism of schemes therefore satisfies

$$
f^*\delta_X(a)=\delta_Y(f^*a),
$$

and a map of group schemes carries division torsors to division torsors. These equations are best proved by pulling back the actual torsor of lifts; the cocycle formula then becomes an immediate verification.

## 12. Relative and base-change phenomena

Cohomology is contravariant in the space, while arithmetic also needs covariant operations such as norms. The interaction between restriction, norm, and Kummer boundaries explains how root classes behave under finite extensions and finite locally free maps.

### 12.1 Restriction along a morphism

Every $f:Y\to X$ gives restriction

$$
\operatorname{res}_{Y/X}:H^q(X,F)\to H^q(Y,f^*F).
$$

For $F=\mu_n$, it sends the root torsor of a unit $a$ to the root torsor of $f^*a$. For $F=\mathbf G_m$, degree one sends a line bundle to its pullback, and degree two sends an Azumaya algebra to its scalar extension. Restriction is compatible with cup products and connecting maps.

If $Y\to X$ is itself an fppf cover, a class may become zero on $Y$ without being zero on $X$. Its descent cocycle records the difference among local trivializations. Faithful flatness detects equalities of morphisms and modules, but not the existence of a chosen global trivialization.

### 12.2 Finite locally free norm and transfer

Let $f:Y\to X$ be finite locally free of constant rank $d$. The determinant of multiplication defines a norm

$$
N_{Y/X}:f_*\mathbf G_m\to\mathbf G_m.
$$

On affine rings $R\to S$, it sends $u\in S^\times$ to the determinant of the $R$-linear map $m_u:S\to S$. Norms commute with base change and are transitive in towers. Applying the determinant construction to transition functions gives a norm of line bundles

$$
N_{Y/X}:\operatorname{Pic}(Y)\to\operatorname{Pic}(X).
$$

When $f$ is finite etale, these maps extend in every degree to transfer, or corestriction, maps

$$
\operatorname{cor}_{Y/X}:H^q(Y,\mathbf G_m)\to H^q(X,\mathbf G_m).
$$

Indeed, etale-locally on $X$, the scheme $Y$ is a disjoint union of $d$ copies of the base. On such a splitting cover, corestriction is the sum over the copies, and symmetry under their permutation makes it descend canonically. Consequently

$$
\operatorname{cor}_{Y/X}\circ\operatorname{res}_{Y/X}=d
$$

on $H^q(X,\mathbf G_m)$. For finite separable field extensions this is the usual corestriction on Brauer groups. For a general finite locally free map, the determinant norm on units and the norm functor on line bundles still exist, but the finite-etale splitting proof of higher corestriction does not apply; we make no unrestricted higher-degree assertion here.

### 12.3 Norms and Kummer classes

Since $N(u^n)=N(u)^n$ and the norm functor is monoidal, a pair $(L,\varphi:L^n\simeq\mathcal O_Y)$ is sent to

$$
\bigl(N_{Y/X}L,\,
N_{Y/X}(L)^n\simeq N_{Y/X}(L^n)
\xrightarrow{N(\varphi)}\mathcal O_X\bigr).
$$

Theorem 5.3 therefore turns the norm into a degree-one corestriction for $\mu_n$-torsors. Naturality of the root-torsor construction yields

$$
\operatorname{cor}_{Y/X}(\delta_Y(u))
=\delta_X(N_{Y/X}(u))
$$

in $H^1(X,\mu_n)$, where degree-one corestriction means this norm of torsors. Over finite locally free field extensions this says

$$
\operatorname{cor}_{L/K}[u]=[N_{L/K}(u)]
\quad\text{in }K^\times/K^{\times n}.
$$

For finite etale $f$, cup products satisfy the projection formula

$$
\operatorname{cor}_{Y/X}(\operatorname{res}x\smile y)
=x\smile\operatorname{cor}_{Y/X}(y),
$$

whenever the coefficient pairings are compatible. This converts norm identities into symbol identities and is often the cleanest proof that a cyclic algebra splits when one entry is a norm.

### 12.4 Descent and transitivity

For a tower $Z\xrightarrow{g}Y\xrightarrow{f}X$ of finite locally free maps, norms of units and line bundles are transitive:

$$
N_{Z/X}=N_{Y/X}\circ N_{Z/Y}.
$$

The identity follows from the determinant norm and the norm functor. It can be checked after a faithfully flat base change making the relevant modules free, where it is transitivity of determinants under restriction of scalars. If both maps are finite etale, higher corestriction is also transitive:

$$
\operatorname{cor}_{Z/X}=\operatorname{cor}_{Y/X}\circ\operatorname{cor}_{Z/Y}.
$$

This may be checked on a common etale cover splitting both maps into disjoint copies. Pullback and transfer also satisfy the usual base-change identity in a Cartesian square of finite etale maps.

These formulas show that Kummer boundaries are compatible not only with changing the base but also with returning classes by norm. They are the cohomological form of the elementary fact that the product of all conjugate $n$th roots is an $n$th root of the norm.

## 13. Calculational patterns

The general exact sequences become useful only after their outer terms are understood. This chapter develops reusable calculations in which units, divisor classes, and Brauer classes can be seen concretely. The examples also expose a frequent error: vanishing of the Picard group simplifies $H^1(\mu_n)$, while vanishing of the Brauer group is needed to simplify $H^2(\mu_n)$. Neither vanishing implies the other in general.

### 13.1 Projective space and factorial schemes

Let $k$ be a field and $r\ge1$. The global units on projective space are $k^\times$, and

$$
\operatorname{Pic}(\mathbf P^r_k)\simeq\mathbf Z,
$$

generated by $\mathcal O(1)$. The first statement follows because a regular function on projective space restricts to a polynomial on each standard affine chart and compatibility at infinity forces degree zero. For the second, the homogeneous coordinate ring $k[X_0,\ldots,X_r]$ is a unique factorization domain. Hence every prime divisor is cut out by an irreducible homogeneous polynomial $f$ of some degree $d$, and the rational function $f/X_0^d$ shows that this divisor is linearly equivalent to $d$ times the hyperplane $X_0=0$. Additivity handles every divisor and proves that the degree map identifies $\operatorname{Pic}(\mathbf P^r_k)$ with $\mathbf Z$. The omitted case $r=0$ is $\operatorname{Spec}k$, whose Picard group is zero and whose Kummer groups were computed in Section 6.1.

Since $\mathbf Z[n]=0$, degree-one Kummer theory gives

$$
H^1(\mathbf P^r_k,\mu_n)\simeq k^\times/k^{\times n}.
$$

Degree two gives

$$
0\to\mathbf Z/n\mathbf Z
\xrightarrow{c_1}H^2(\mathbf P^r_k,\mu_n)
\to\operatorname{Br}'(\mathbf P^r_k)[n]\to0.
$$

The image of $1$ is the mod-$n$ first Chern class of $\mathcal O(1)$, concretely the gerbe of its $n$th roots. Even when the Brauer term vanishes, $H^2(\mu_n)$ does not: divisor classes contribute.

Now let $R$ be a noetherian unique factorization domain. Every invertible ideal is principal: locally it is generated by one element, and the valuations at height-one primes assemble into a principal divisor because factorization is unique. Thus

$$
\operatorname{Pic}(\operatorname{Spec}R)=0
$$

and

$$
H^1(\operatorname{Spec}R,\mu_n)=R^\times/R^{\times n}.
$$

The same conclusion holds for any local ring, for a different reason: rank-one projective modules over a local ring are free. A locally factorial nonaffine scheme, however, can have a nonzero Picard group; projective space is the simplest warning. Factoriality of local rings makes Weil divisors Cartier, not globally principal.

### 13.2 Dedekind schemes

Let $R$ be a Dedekind domain with fraction field $K$ and $X=\operatorname{Spec}R$. Invertible sheaves correspond to nonzero fractional ideals modulo principal fractional ideals, so

$$
\operatorname{Pic}(X)\simeq\operatorname{Cl}(R).
$$

The degree-one Kummer sequence reads

$$
0\to R^\times/R^{\times n}
\to H^1(X,\mu_n)
\to\operatorname{Cl}(R)[n]\to0.
$$

This admits an elementary ideal-theoretic description. A class in $\operatorname{Cl}(R)[n]$ is represented by a fractional ideal $I$ such that

$$
I^n=(a)
$$

for some $a\in K^\times$. Division by $a$ is the power trivialization $I^{\otimes n}\simeq R$, so the pair $(I,a)$ determines a $\mu_n$-torsor. In the convention of Theorem 5.3 its generic root equation is $T^n=a$. Replacing $I$ by $bI$ changes $a$ to $b^na$; multiplying the power trivialization by a unit changes $a$ by the inverse unit. This is precisely the equivalence encoded by the exact sequence.

The generic restriction sends $(I,a)$ to the class of $a$ in $K^\times/K^{\times n}$. Which field classes extend over $R$? Write $v_{\mathfrak p}$ for normalized valuations. From $I^n=(a)$ one obtains

$$
v_{\mathfrak p}(a)\equiv0\pmod n
$$

for every nonzero prime $\mathfrak p$. Conversely, if all valuations of $a$ are divisible by $n$, define the fractional ideal

$$
I=\prod_{\mathfrak p}\mathfrak p^{\,v_{\mathfrak p}(a)/n}.
$$

Unique factorization of fractional ideals gives $I^n=(a)$ with no sign ambiguity. Hence the image of

$$
H^1(X,\mu_n)\to H^1(K,\mu_n)
$$

is exactly

$$
\{[a]\in K^\times/K^{\times n}:v_{\mathfrak p}(a)\equiv0\pmod n\text{ for all }\mathfrak p\}.
$$

This calculation explains the role of the class group. A field element with $n$-divisible valuation divisor need not be a unit times an $n$th power: dividing the divisor by $n$ may produce a nonprincipal ideal. The resulting ideal class is the $\operatorname{Cl}(R)[n]$ component of the torsor.

### 13.3 Strictly henselian local rings

Let $R$ be a strictly henselian local ring with residue field $k$. Then $\operatorname{Pic}(R)=0$, so for every $n$

$$
H^1(R,\mu_n)=R^\times/R^{\times n}.
$$

If $n$ is invertible in $R$, every unit has an $n$th root. Indeed, its residue has an $n$th root because $k$ is separably closed, and that root is simple for $T^n-u$; Hensel's lemma lifts it. Therefore

$$
H^1(R,\mu_n)=0\qquad(n\in R^\times).
$$

Equivalently, every finite etale $\mu_n$-torsor over a strictly henselian local scheme is trivial.

When the residue characteristic $p$ divides $n$, this conclusion can fail. Strict henselianity lifts simple roots, not multiple Frobenius roots. For example, in characteristic $p$ an imperfect strictly henselian ring may contain a unit not in $R^{\times p}$, yielding a nontrivial $\mu_p$-torsor. Even for a perfect residue field, nilpotent or mixed-characteristic structure can obstruct a $p$th root. The uniform formula $R^\times/R^{\times n}$ remains correct; only the shortcut by Hensel's lemma fails.

Every Azumaya algebra over a strictly henselian local ring is split. To prove this, reduce it modulo the maximal ideal. Over the separably closed residue field the central simple fiber is a matrix algebra. The scheme of isomorphisms with that matrix algebra is a smooth $\operatorname{PGL}_r$-torsor; the residue point lifts by henselianity, giving a global matrix-algebra trivialization. Thus $\operatorname{Br}(R)=0$. This proves a statement about Azumaya classes; identifying all of $H^2(R,\mathbf G_m)$ requires the appropriate cohomological comparison hypotheses and should not be inferred solely from the argument.

### 13.4 Arithmetic in the coefficient

The roots-of-unity schemes for varying exponents fit into exact sequences. For positive integers $m,n$, the power map gives

$$
1\to\mu_m\to\mu_{mn}\xrightarrow{(\cdot)^m}\mu_n\to1.
$$

The kernel is visibly $\mu_m$. Local surjectivity follows by adjoining an $m$th root of a given $n$th root, again using a finite free monic algebra. Thus the sequence is fppf-exact without invertibility assumptions. Its long exact sequence compares Kummer classes at levels $m$, $n$, and $mn$.

If $m$ and $n$ are coprime, choose integers $a,b$ with $am+bn=1$. The maps

$$
\mu_{mn}\longrightarrow\mu_m\times\mu_n,
\qquad z\longmapsto(z^n,z^m),
$$

and

$$
(x,y)\longmapsto x^b y^a
$$

are inverse after the exponents are interpreted modulo $m$ and $n$. Hence

$$
\mu_{mn}\simeq\mu_m\times\mu_n,
\qquad
H^q(X,\mu_{mn})\simeq H^q(X,\mu_m)\times H^q(X,\mu_n).
$$

It follows that calculations reduce to prime powers. This reduction is scheme-theoretic and remains valid in residue characteristics dividing one of the exponents.

For a prime $p$, the tower

$$
\mu_p\subset\mu_{p^2}\subset\cdots
$$

has transition maps and exact quotients controlled by the preceding sequence. The map on degree-one unit classes is the evident passage between

$$
\Gamma(X,\mathcal O_X)^\times/\Gamma(X,\mathcal O_X)^{\times p^r}.
$$

The Picard components track $p^r$-torsion line bundles together with compatible power trivializations. One must retain both pieces; inverse systems of unit quotients alone do not describe all $\mu_{p^r}$-torsors on a scheme with nontrivial Picard group.

### 13.5 A hypothesis ledger

The following implications summarize where the main assumptions enter.

| Statement | Required hypothesis | Reason |
|---|---|---|
| $1\to\mu_n\to\mathbf G_m\xrightarrow{n}\mathbf G_m\to1$ is fppf-exact | any scheme, $n\ge1$ | adjoining a root is finite free |
| the same sequence is etale-exact | $n$ invertible on the base | $\mu_n$ and root covers are etale |
| $H^1(X,\mu_n)=\Gamma(X,\mathcal O_X)^\times/(-)^n$ | $\operatorname{Pic}(X)[n]=0$ | degree-one Kummer sequence |
| $H^2(X,\mu_n)=\operatorname{Br}'(X)[n]$ | $\operatorname{Pic}(X)/n=0$ | degree-two Kummer sequence |
| $H^q(X,\widetilde M)=0$ for $q>0$ | $X$ affine, $\widetilde M$ quasi-coherent | Amitsur acyclicity |
| fppf and etale $H^q(X,G)$ agree for every $q$ | $G$ smooth and commutative | smooth change of topology |
| $A(S)/nA(S)\hookrightarrow H^1(S,A[n])$ | $A/S$ abelian, any $n$ | $[n]$ is finite locally free surjective |
| a finite group over a field is recovered from geometric points with descent action | coefficient group finite etale | connected infinitesimal structure must be absent |
| $\operatorname{Br}(X)=\operatorname{Br}'(X)$ | additional geometric hypotheses, or $X$ a field | not true by definition on arbitrary schemes |

The ledger is not merely a list of technicalities. Each hypothesis corresponds to a geometric mechanism: invertibility gives separability, affineness kills quasi-coherent gluing, smoothness produces etale sections, and finite flatness preserves infinitesimal torsion.

## 14. Synthesis

The theory can now be read as one continuous passage from local solvability to global obstruction. Fppf covers are broad enough to solve monic root equations in every characteristic. Torsors retain the ambiguity among those local solutions. Connecting homomorphisms promote the ambiguity to cohomology, and Kummer sequences identify the resulting groups with units, line bundles, and Brauer classes.

### 14.1 The low-degree dictionary

For an abelian fppf sheaf $G$:

| Degree | Cohomological object | Geometric meaning |
|---|---|---|
| $H^0(X,G)$ | global sections | solutions already defined on $X$ |
| $H^1(X,G)$ | $G$-torsor classes | locally chosen solutions differing by $G$ |
| $H^2(X,G)$ | abelian obstruction classes | failure of lifted transition maps on triple overlaps |

For $G=\mathbf G_m$, degree one is $\operatorname{Pic}(X)$ and torsion in degree two is $\operatorname{Br}'(X)$. For $G=\mu_n$, the two decisive sequences are

$$
0\to\mathcal O_X(X)^\times/\mathcal O_X(X)^{\times n}
\to H^1(X,\mu_n)\to\operatorname{Pic}(X)[n]\to0
$$

and

$$
0\to\operatorname{Pic}(X)/n
\to H^2(X,\mu_n)\to\operatorname{Br}'(X)[n]\to0.
$$

The first says that a root torsor is governed by a unit only after its underlying $n$-torsion line bundle has been trivialized. The second says that a degree-two Kummer class contains both a divisor-theoretic contribution and a Brauer contribution.

For an abelian scheme $A/S$, the parallel sequence

$$
0\to A(S)/nA(S)\to H^1(S,A[n])\to H^1(S,A)[n]\to0
$$

replaces roots of units by division points and line bundles by torsors under $A$. These are not analogies after the fact: all three are instances of the same long exact sequence.

### 14.2 A reliable Kummer protocol

A sound calculation proceeds in a fixed order.

1. Identify the coefficient as a group **scheme** or fppf sheaf, retaining connected and nonreduced fibers.
2. Prove local surjectivity of the defining map in the chosen topology. For $[n]$ on $\mathbf G_m$, use the finite free root algebra.
3. Write the relevant portion of the long exact sequence before simplifying it.
4. Compute units, Picard groups, or Brauer groups with their exact hypotheses.
5. Interpret the boundary as the torsor or gerbe of lifts.
6. Check naturality under base change, coefficient maps, and norms.

This order prevents the common mistakes of assuming an $n$th root exists globally, replacing fppf exactness by pointwise exactness, discarding Picard terms, or identifying the Azumaya and cohomological Brauer groups without justification.

### 14.3 Conclusion

Fppf cohomology turns faithfully flat descent into a calculus of ambiguity and obstruction. Its degree-one classes are concrete torsors, and its boundaries are concrete fibers of lifting problems. The Kummer sequence is exact for every positive integer because a monic root equation defines a finite free cover; this single fact carries the theory uniformly across mixed characteristic, equal characteristic, etale roots of unity, and infinitesimal roots of unity.

The resulting dictionary is both geometric and arithmetic. Units modulo powers describe root torsors when line bundles contribute no torsion. Torsion line bundles supply the additional degree-one classes. Their failure to possess roots contributes to degree two, alongside Brauer classes arising from projective linear descent. Finite-flat group schemes and torsion on abelian schemes fit the same pattern through their isogeny sequences. Restriction, norm, cup product, and connecting maps preserve the pattern and make it stable under the operations used in descent.

The essential lesson is that cohomology does not replace descent; it measures its choices and failures. Once exactness is understood locally in the correct topology, Kummer theory becomes a systematic method rather than a collection of root-extraction tricks.
