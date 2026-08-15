# Finite-Flat Galois Representations

## Contents

1. [The integral question behind a local representation](#1-the-integral-question-behind-a-local-representation)
   - [The local setting](#11-the-local-setting)
   - [Finite continuous modules](#12-finite-continuous-modules)
   - [From an integral group to its generic action](#13-from-an-integral-group-to-its-generic-action)
   - [What geometric points forget](#14-what-geometric-points-forget)
2. [Finite étale groups and Galois modules](#2-finite-étale-groups-and-galois-modules)
   - [The exact correspondence](#21-the-exact-correspondence)
   - [Where characteristic enters](#22-where-characteristic-enters)
   - [Morphisms, exactness, and variance](#23-morphisms-exactness-and-variance)
   - [Unramified modules over a henselian valuation ring](#24-unramified-modules-over-a-henselian-valuation-ring)
3. [Models and the finite-flat predicate](#3-models-and-the-finite-flat-predicate)
   - [Why a model includes an identification](#31-why-a-model-includes-an-identification)
   - [Existence as a property](#32-existence-as-a-property)
   - [The exponent and the order](#33-the-exponent-and-the-order)
   - [First examples and nonexamples](#34-first-examples-and-nonexamples)
4. [The generic-fiber functor](#4-the-generic-fiber-functor)
   - [Faithfulness](#41-faithfulness)
   - [Failure of fullness](#42-failure-of-fullness)
   - [Model groupoids and exact categories](#43-model-groupoids-and-exact-categories)
   - [Essential image and essential uniqueness](#44-essential-image-and-essential-uniqueness)
5. [Subrepresentations through schematic closure](#5-subrepresentations-through-schematic-closure)
   - [Why an ambient model changes the problem](#51-why-an-ambient-model-changes-the-problem)
   - [The closure theorem](#52-the-closure-theorem)
   - [Admissible subobjects and quotients](#53-admissible-subobjects-and-quotients)
   - [Kernels and images: the unsafe shortcuts](#54-kernels-and-images-the-unsafe-shortcuts)
6. [Exact sequences and extension classes](#6-exact-sequences-and-extension-classes)
   - [Faithfully flat exactness](#61-faithfully-flat-exactness)
   - [Passing an integral sequence to representations](#62-passing-an-integral-sequence-to-representations)
   - [Which generic extensions are finite flat](#63-which-generic-extensions-are-finite-flat)
   - [Pullbacks, pushouts, and Baer operations](#64-pullbacks-pushouts-and-baer-operations)
7. [A calculus of finite-flat representations](#7-a-calculus-of-finite-flat-representations)
   - [Sums, products, and primary parts](#71-sums-products-and-primary-parts)
   - [Subquotients and supplied extensions](#72-subquotients-and-supplied-extensions)
   - [Coefficient actions and restriction of scalars](#73-coefficient-actions-and-restriction-of-scalars)
   - [Extension of coefficient scalars](#74-extension-of-coefficient-scalars)
8. [Cartier duality and the Tate twist](#8-cartier-duality-and-the-tate-twist)
   - [Why the ordinary linear dual is not enough](#81-why-the-ordinary-linear-dual-is-not-enough)
   - [Dual models](#82-dual-models)
   - [Exactness and annihilators](#83-exactness-and-annihilators)
   - [Self-dual geometric representations](#84-self-dual-geometric-representations)
9. [Changing the local field](#9-changing-the-local-field)
   - [Restriction by base change](#91-restriction-by-base-change)
   - [Unramified and ramified extensions](#92-unramified-and-ramified-extensions)
   - [Faithfully flat descent](#93-faithfully-flat-descent)
   - [Why potential finite flatness is weaker](#94-why-potential-finite-flatness-is-weaker)
10. [Rigidity and multiplicity of models](#10-rigidity-and-multiplicity-of-models)
    - [Prime-to-residue-characteristic rigidity](#101-prime-to-residue-characteristic-rigidity)
    - [Constant and multiplicative models](#102-constant-and-multiplicative-models)
    - [An equal-characteristic lattice example](#103-an-equal-characteristic-lattice-example)
    - [Three distinct uniqueness statements](#104-three-distinct-uniqueness-statements)
11. [Geometric sources of finite-flat representations](#11-geometric-sources-of-finite-flat-representations)
    - [Good reduction and torsion](#111-good-reduction-and-torsion)
    - [Elliptic curves at the residue characteristic](#112-elliptic-curves-at-the-residue-characteristic)
    - [Abelian schemes and finite-flat subgroup closures](#113-abelian-schemes-and-finite-flat-subgroup-closures)
    - [Good reduction versus other reduction types](#114-good-reduction-versus-other-reduction-types)
12. [Coefficients and two-dimensional residual representations](#12-coefficients-and-two-dimensional-residual-representations)
    - [Actions by a finite coefficient ring](#121-actions-by-a-finite-coefficient-ring)
    - [Basis-independent representations](#122-basis-independent-representations)
    - [Changing lattices and changing coefficients](#123-changing-lattices-and-changing-coefficients)
    - [Determinants and pairings](#124-determinants-and-pairings)
13. [The local finite-flat condition](#13-the-local-finite-flat-condition)
    - [At a place above the coefficient characteristic](#131-at-a-place-above-the-coefficient-characteristic)
    - [Invariance and closure properties](#132-invariance-and-closure-properties)
    - [What the condition does not assert](#133-what-the-condition-does-not-assert)
    - [A practical verification protocol](#134-a-practical-verification-protocol)
14. [The four-level dictionary](#14-the-four-level-dictionary)
    - [Representation, model, existence, and uniqueness](#141-representation-model-existence-and-uniqueness)
    - [A reusable criterion](#142-a-reusable-criterion)
    - [Final synthesis](#143-final-synthesis)

## 1. The integral question behind a local representation

### 1.1 The local setting

A finite representation of a local Galois group is easy to state and surprisingly incomplete as an integral object. It records how a separable closure permutes finitely many torsion points, but it does not record how those points approach one another modulo the maximal ideal. When the torsion order is divisible by the residue characteristic, distinct generic points may collide into a connected, nonreduced special fiber. Finite-flat group schemes retain precisely this missing specialization data.

Throughout, $K$ is a nonarchimedean local field in the valuation-theoretic sense: it is complete for a nontrivial discrete valuation. We write

$$
R=\mathcal O_K,\qquad \mathfrak m=(\pi),\qquad k=R/\mathfrak m,
$$

choose a separable closure $K^s$, and put

$$
G_K=\operatorname{Gal}(K^s/K).
$$

When $k$ has positive characteristic, its characteristic will be denoted $p$. Statements about $p$-primary torsion tacitly begin with that hypothesis; if $k$ has characteristic zero, every positive integer is invertible in $R$ and only the rigid étale case remains. Neither finiteness nor perfection of $k$ is built into the words “complete discretely valued field.” Completeness implies that $R$ is henselian; perfection will be added only when connected--étale structure requires it. Most arithmetic applications have $K$ a finite extension of $\mathbf Q_p$, so $\operatorname{char}K=0$ and $k$ is finite, but equal characteristic $K=k((t))$ is kept visible because it exposes several otherwise hidden hypotheses.

There are three characteristics in the discussion, and confusing them destroys otherwise correct statements. The characteristic of $K$ governs whether a finite generic group is automatically étale. The characteristic of $k$ governs which orders can develop connected special fibers. The characteristic of a coefficient ring governs the torsion carried by a representation. In the central arithmetic case these are

$$
\operatorname{char}K=0,\qquad \operatorname{char}k=p,
\qquad \operatorname{char}\Lambda=\ell^a,
$$

and the difficult local condition occurs at a place with $p=\ell$. At a place with $p\ne\ell$, every $\ell$-power-order model is forced to be étale, so finite flatness reduces to unramifiedness. This dichotomy explains why the same phrase has a geometric meaning above $\ell$ and a rigid Galois-theoretic meaning away from $\ell$.

Book 2 supplies the valuation-theoretic facts used throughout: $R$ is henselian, the valuation extends uniquely to every finite extension, and the integral closure $R_L$ in a finite extension $L/K$ is a finite free $R$-module. Book 17 supplies finite étale descent and the finite-set description of absolute Galois actions. Books 28 and 34 supply finite-flat quotients, schematic closure over a DVR, and Cartier duality. We recall each imported statement at the point of use, including the hypothesis that makes it applicable, so that the argument remains readable without silently enlarging the dependency list.

The geometry used here is the category of finite locally free commutative $R$-group schemes. “Finite flat” will always mean finite locally free, including finite presentation. Over the DVR $R$ the coordinate algebra is therefore a finite free $R$-module. Its rank is constant and survives passage to both generic and special fibers.

### 1.2 Finite continuous modules

Before introducing integral geometry, we need a basis-free description of the generic datum. Matrices conceal changes of coefficients and invariant subgroups; a finite module with continuous action retains exactly the information that survives every change of basis.

A **finite continuous $G_K$-module** is a finite abelian group $M$ equipped with an action of $G_K$ such that

$$
G_K\times M\longrightarrow M
$$

is continuous when $M$ has the discrete topology. Because $M$ is finite, this is equivalent to any of the following:

- every element has an open stabilizer;
- the kernel of $G_K\to\operatorname{Aut}(M)$ is open;
- the action factors through a finite quotient of $G_K$.

No basis and no coefficient field are part of this definition. If $M$ is free of rank $d$ over a finite ring $\Lambda$, and the action is $\Lambda$-linear, a chosen basis writes it as a homomorphism

$$
\rho:G_K\longrightarrow\operatorname{GL}_d(\Lambda),
$$

but the module with its action is the invariant object. This distinction becomes important when finite flatness is required to be independent of a matrix presentation.

The topology is not decorative. Since $\operatorname{Aut}(M)$ is finite and discrete, continuity of the action is equivalent to continuity of the homomorphism

$$
\rho_M:G_K\longrightarrow\operatorname{Aut}(M).
$$

The singleton $\{1\}$ is open in the target, so continuity implies that $\ker\rho_M$ is open. Conversely an open kernel makes $\rho_M$ factor through the finite discrete quotient $G_K/\ker\rho_M$, and the action is continuous. Thus every finite representation is controlled by a finite Galois extension: after replacing the open kernel by its open normal core, there is a finite Galois extension $L/K$ such that $G_L$ acts trivially. This is what makes ordinary finite Galois descent sufficient on the generic fiber.

If $M$ is a finite $\Lambda$-module, continuity as an abelian-group representation and continuity as a $\Lambda$-linear representation are the same condition. Indeed $\operatorname{Aut}_\Lambda(M)$ is a subgroup of the same finite permutation group. Coefficient linearity is additional algebraic structure, not an additional topological constraint.

The adjective “absolute” refers to $G_K$, not to an algebraic closure fixed once and for all. Replacing $K^s$ by another separable closure conjugates $G_K$ and transports its modules through an equivalence. Nothing below depends on that auxiliary choice.

### 1.3 From an integral group to its generic action

The first direction of the dictionary is easy but foundational: an integral group should produce a generic representation. Isolating the hypothesis under which geometric points retain the whole generic group prevents connected infinitesimal groups from being mistaken for zero representations.

Let $\mathcal G$ be a finite-flat commutative $R$-group scheme. Its generic fiber

$$
\mathcal G_K=\mathcal G\times_R K
$$

is a finite commutative group scheme over $K$. If $\mathcal G_K$ is étale, its geometric points

$$
M(\mathcal G)=\mathcal G_K(K^s)
$$

form a finite continuous $G_K$-module. The action is the natural semilinear action on $K^s$-points. Rank becomes cardinality:

$$
|\mathcal G|=\dim_K\mathcal O(\mathcal G_K)
=|\mathcal G_K(K^s)|.
$$

The last equality deserves its étale hypothesis. Over $K^s$, a finite étale scheme of rank $r$ is a disjoint union of $r$ copies of $\operatorname{Spec}K^s$, so it has exactly $r$ geometric points. A nonétale scheme can have fewer points than its rank. The generic representation therefore exists in the present sense precisely on the full subcategory of finite-flat groups with étale generic fiber.

This construction is the bridge of the book. The representation is the generic shadow of an integral group. The special fiber $\mathcal G_k$ is not an extra representation: it is a finite group scheme that may have fewer geometric points, nilpotents, and a connected component of positive scheme-theoretic order.

When $\operatorname{char}K=0$, every finite group scheme over $K$ is étale, so every finite-flat $R$-group has such a generic module. More generally, a finite group scheme over a field is étale whenever its order is prime to the characteristic. In characteristic $p$, however, $\alpha_p$ and $\mu_p$ show that a finite group scheme of $p$-power order need not be étale. Thus in equal characteristic the expression $\mathcal G_K(K^s)$ can lose information and is not automatically the generic representation of $\mathcal G$.

### 1.4 What geometric points forget

Two examples now locate the exact boundary of the pointwise viewpoint. The mixed-characteristic example shows collision only after specialization; the equal-characteristic example shows that information may already be lost on the generic fiber.

The familiar mixed-characteristic example is

$$
\mu_p=\operatorname{Spec}R[T]/(T^p-1).
$$

Its generic fiber is étale because $p\ne0$ in $K$. Its special fiber satisfies

$$
T^p-1=(T-1)^p
$$

after passage to an algebraic closure of $k$. Thus $p$ generic points merge into one geometric special point of length $p$. The Galois module sees the generic roots of unity and their cyclotomic action; the integral model additionally records the collision.

In equal characteristic $p$, the warning is stronger. The group $\alpha_p=\operatorname{Spec}K[X]/(X^p)$ has only the zero geometric point, just as the trivial group does, although its scheme-theoretic order is $p$. Hence the functor of geometric points is not faithful on all finite group schemes. The finite étale hypothesis is the precise boundary at which points recover the scheme.

The distinction may also be read through coordinate algebras. For the constant group of order $p$, the coordinate algebra over an algebraic closure is a product of $p$ fields. For $\alpha_p$ it is the local algebra $K[X]/(X^p)$, whose nilpotent element $X$ is invisible under every map to a field. Geometric points see the reduced quotient of a finite algebra; finite-flat geometry must retain its nilpotents as well. This is why finite flatness is never defined by counting points of the special fiber.

This observation determines the architecture that follows. We first identify the generic finite étale object corresponding to a module. A finite-flat model will then mean an integral group whose generic fiber is identified with that étale object. The definition will never attempt to recover a nonétale generic group from its points.

## 2. Finite étale groups and Galois modules

### 2.1 The exact correspondence

The generic side of the theory is controlled by descent. Over $K^s$, every finite étale scheme is a disjoint union of points. Its entire descent datum is therefore an action of $G_K$ on that finite set. Requiring a commutative group law turns the set into a finite abelian group and the action into one by group automorphisms.

**Theorem 2.1 (finite étale--Galois correspondence).** For every field $F$ with separable closure $F^s$, the functor

$$
H\longmapsto H(F^s)
$$

is an equivalence from finite étale commutative $F$-group schemes to finite discrete abelian groups with continuous $G_F$-action.

**Proof strategy.** A finite étale group becomes constant over a finite separable extension, so its points and descent action reconstruct it. Conversely, continuity makes every finite module descend from a constant group over a finite Galois extension.

For the second direction, let $M$ be a finite continuous $G_F$-module. Choose an open normal subgroup acting trivially, corresponding to a finite Galois extension $L/F$. Over $L$ take the constant group $\underline M_L$. Its coordinate algebra is $L^M$, and $\operatorname{Gal}(L/F)$ acts semilinearly, permuting the factors according to its action on $M$. Galois descent produces a finite étale Hopf algebra over $F$. Increasing $L$ does not change the descended object. In the other direction, a finite étale group splits over some finite separable extension, and its descent datum is recovered from the action on its geometric points. These constructions are mutually inverse. $\square$

The descent algebra makes every part of the construction visible. If $f\in L^M$ is a function $M\to L$, define

$$
(\gamma f)(m)=\gamma\bigl(f(\gamma^{-1}m)\bigr).
$$

Then $(L^M)^{\operatorname{Gal}(L/F)}$ is the descended coordinate algebra. Addition on $M$ gives

$$
\Delta(f)(m_1,m_2)=f(m_1+m_2),
$$

while zero and inversion give the counit and antipode. These maps commute with the semilinear action and therefore descend. A map between two split constant groups is exactly a homomorphism of their indexing finite abelian groups, and it descends precisely when it is Galois equivariant. This verifies full faithfulness as well as essential surjectivity.

We denote the finite étale $K$-group associated with $M$ by $\mathcal E_K(M)$. The notation separates the abstract module from the scheme that represents it. There is a canonical identification

$$
\mathcal E_K(M)(K^s)\simeq M
$$

once the descent construction is fixed.

### 2.2 Where characteristic enters

The correspondence itself is characteristic-free, but applications often use the separate assertion that a given group scheme is étale. This section disentangles those statements so that an invertibility hypothesis is never smuggled into descent.

Theorem 2.1 has no restriction on the order of $M$. Even in characteristic $p$, a finite abstract $p$-group with continuous Galois action descends to a finite **étale** group scheme: after $F^s$ it is the constant disjoint union indexed by that group. What fails in characteristic $p$ is the converse claim that every finite group scheme arises this way.

There are therefore two different statements, with different hypotheses:

1. Every finite continuous $G_F$-module corresponds to a finite étale $F$-group scheme, in every characteristic.
2. Every finite commutative $F$-group scheme of order $n$ is étale if $n$ is prime to $\operatorname{char}F$; in particular every finite group scheme over a characteristic-zero field is étale.

Suppose $M$ is killed by an integer $n$. The associated $\mathcal E_F(M)$ is killed by $n$ with no condition on $n$. But to conclude that an arbitrary group scheme killed by $n$ is visible through geometric points, one requires $n$ invertible in $F$, or an independent proof of étaleness. This is the separability hypothesis that will accompany every use of generic geometric points.

### 2.3 Morphisms, exactness, and variance

An equivalence of objects is useful only if it transports maps and exact sequences with the correct arrow directions. Those compatibilities will later turn generic submodules into subgroup schemes and generic quotients into faithfully flat quotients.

The correspondence is covariant. A homomorphism $u:M\to N$ gives a morphism

$$
\mathcal E_F(u):\mathcal E_F(M)\longrightarrow\mathcal E_F(N).
$$

On coordinate algebras the arrow reverses, as it must:

$$
\mathcal O(\mathcal E_F(N))\longrightarrow
\mathcal O(\mathcal E_F(M)).
$$

This elementary variance check prevents a frequent mistake. Cartier duality will later reverse the group-scheme arrow; the geometric-point equivalence itself does not.

The equivalence is exact. If

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
$$

is exact, then

$$
0\longrightarrow\mathcal E_F(M')\longrightarrow
\mathcal E_F(M)\longrightarrow\mathcal E_F(M'')\longrightarrow0
$$

is faithfully flat exact. Conversely, geometric points of a faithfully flat exact sequence of finite étale groups form an exact sequence of modules. Surjectivity here is a statement after separable base change; it is not a claim that $F$-rational points surject.

Indeed, after extension to $F^s$ the groups are constant. A homomorphism between constant finite groups is faithfully flat exactly when the underlying homomorphism is surjective: on coordinate algebras it is the inclusion of products of copies of $F^s$ obtained by repeating a coordinate along every fiber. Faithful flatness descends, so exactness of the modules and faithfully flat exactness of the group schemes are equivalent. This calculation also explains why exactness on $F$-rational points is neither necessary nor expected.

### 2.4 Unramified modules over a henselian valuation ring

Completeness now has its first representation-theoretic consequence. Since $R$ is henselian, finite étale $R$-schemes are equivalent to finite étale $k$-schemes. Choose a separable closure $k^s$ and write $G_k=\operatorname{Gal}(k^s/k)$. After choosing compatible separable closures, the generic fibers are exactly the finite étale $K$-schemes on which inertia acts trivially.

**Theorem 2.2.** A finite continuous $G_K$-module $M$ admits a finite étale $R$-model if and only if inertia $I_K$ acts trivially. When it exists, the finite étale model, together with its generic identification, is unique up to unique isomorphism.

**Proof strategy.** Compare both sides with finite étale objects over the residue field. Henselianity lifts those objects and their morphisms uniquely, while the quotient $G_K\to G_k$ identifies residue Galois actions with generic actions trivial on inertia.

If $\mathcal G/R$ is finite étale, reduction gives a finite étale $k$-group. Its generic geometric points carry the inflated $G_k$-action, so $I_K$ acts trivially. Conversely, if $I_K$ acts trivially on $M$, the action factors through $G_K/I_K\simeq G_k$. Theorem 2.1 gives a finite étale $k$-group, and the henselian lifting equivalence gives a finite étale $R$-group with the desired generic module. Full faithfulness of both equivalences gives uniqueness of the object and of its generic identification. $\square$

Here inertia is the kernel in the exact sequence

$$
1\longrightarrow I_K\longrightarrow G_K
\longrightarrow G_k\longrightarrow1.
$$

The right-hand map comes from the action on the residue field of the integral closure of $R$ in $K^s$. Henselianity ensures that every finite separable extension of $k$ lifts uniquely to a finite unramified extension of $K$, which proves surjectivity. No finiteness or perfection hypothesis on $k$ is used. When $k$ is finite, $G_k$ is procyclic: arithmetic Frobenius $x\mapsto x^{|k|}$ topologically generates it, while geometric Frobenius is the inverse. We will never use an unqualified Frobenius normalization.

The phrase “unique” is deliberately confined to the finite étale category. A module can have this canonical étale model and also have a nonétale finite-flat model when $p$ divides its order. The constant and multiplicative example in Chapter 10 will make that distinction concrete.

If $k$ is finite, an unramified module is determined by the action of arithmetic Frobenius, subject to continuity. If $k$ is merely perfect, there is still a quotient $G_K/I_K\simeq G_k$, but no distinguished single Frobenius need topologically generate it. Perfectness is not needed for Theorem 2.2; henselianity is the essential hypothesis for the étale lifting equivalence.

## 3. Models and the finite-flat predicate

### 3.1 Why a model includes an identification

We can now state the central definition. The point is not merely to find an integral group with an isomorphic generic fiber. One must remember which generic isomorphism realizes the given module; otherwise automorphisms of the generic object obscure morphisms between models.

**Definition 3.1.** Let $M$ be a finite continuous $G_K$-module. A **finite-flat model of $M$ over $R$** is a pair $(\mathcal G,\iota)$ consisting of

- a finite locally free commutative $R$-group scheme $\mathcal G$;
- an isomorphism of finite étale $K$-group schemes

  $$
  \iota:\mathcal G_K\xrightarrow{\sim}\mathcal E_K(M).
  $$

In particular, the definition requires $\mathcal G_K$ to be étale. This is automatic in mixed characteristic but a genuine restriction in equal characteristic.

Equivalently, one may give a $G_K$-equivariant isomorphism $\mathcal G_K(K^s)\simeq M$, provided the generic fiber has first been proved étale. The scheme formulation is safer because it keeps the separability condition visible.

The word “model” means an object plus a generic identification. If one discards $\iota$, one obtains only an integral form of the isomorphism class of $M$. Both viewpoints are useful, but morphisms in a fiber over a fixed representation are most precise when the identification is retained.

Two models $(\mathcal G,\iota)$ and $(\mathcal H,\theta)$ of the same $M$ are isomorphic as models when an $R$-group isomorphism $u:\mathcal G\to\mathcal H$ satisfies

$$
\theta\circ u_K=\iota.
$$

An isomorphism of the underlying integral groups need not be an isomorphism of models if it changes the marking on the generic fiber. Conversely, a chosen generic isomorphism need not extend integrally. The marking eliminates an automorphism ambiguity but does not manufacture morphisms.

There is also a Hopf-lattice translation. Put $A_K=\mathcal O(\mathcal E_K(M))$. A model is equivalent to a finite free $R$-subalgebra $A\subset A_K$ that spans $A_K$ over $K$ and is stable under coproduct, counit, and antipode. Such an $A$ is an integral Hopf lattice. Different models of the same representation are different Hopf lattices inside one fixed generic Hopf algebra. A generic endomorphism extends exactly when its pullback preserves the chosen lattice.

### 3.2 Existence as a property

Arithmetic statements usually say that a representation “is finite flat,” without carrying a chosen model forever. We therefore separate the witness from the existential property it witnesses.

**Definition 3.2.** The module $M$ is **finite flat over $R$**, written informally

$$
\operatorname{FF}_R(M),
$$

if there exists a finite-flat model $(\mathcal G,\iota)$ of $M$.

Thus finite flatness of a representation is an existential predicate:

$$
\operatorname{FF}_R(M)\quad\Longleftrightarrow\quad
\exists(\mathcal G,\iota)\text{ as in Definition 3.1}.
$$

The integral group is evidence for the property, not part of the bare module. This logical distinction matters. A proof that $M$ is finite flat may choose one model and use it to construct subquotient models. It does not thereby produce a canonical model, nor does it permit comparing constructions made from two choices without an additional argument.

Finite flatness is invariant under $G_K$-module isomorphism. If $a:M\to N$ is an isomorphism and $(\mathcal G,\iota)$ models $M$, then $(\mathcal G,\mathcal E_K(a)\circ\iota)$ models $N$. This simple transport is what later makes the condition basis-independent.

The zero module has the trivial one-point group as its model. A finite product of models will later model a direct sum. These elementary cases matter logically: the predicate is a property of an object in an abelian representation category, but its witnesses live in an exact geometric category that is not abelian.

### 3.3 The exponent and the order

Two elementary integers impose different geometric constraints. Keeping exponent and order separate is essential for coefficient actions, ranks, duality, and extension categories.

Every finite module is killed by some positive integer $n$, and its associated finite étale group has order $|M|$. Any model therefore has constant rank $|M|$. Moreover, the model is itself killed by $n$: multiplication by $n$ vanishes generically and hence vanishes integrally by faithfulness. Explicitly, $[n]_{\mathcal G}$ and the zero morphism have the same generic fiber, and maps out of $\mathcal G$ are determined by their generic fibers because $\mathcal O(\mathcal G)$ is $R$-torsion-free. These integers play different roles. The exponent controls coefficient actions and duality targets; the order controls rank and étaleness criteria.

The exponent can be smaller than the order. For $M=(\mathbf Z/p\mathbf Z)^2$, every model has order $p^2$ and is killed by $p$. For $M=\mathbf Z/p^2\mathbf Z$, both order and exponent are $p^2$. This matters for extensions: an extension of two groups killed by $p$ can have middle term $\mathbf Z/p^2\mathbf Z$, so the middle term need not be killed by the same exponent as the endpoints.

Assume now that $k$ has characteristic $p>0$. If $|M|$ is prime to $p$, then every finite-flat model has order invertible in $R$ and is finite étale. Consequently

$$
\operatorname{FF}_R(M)\quad\Longleftrightarrow\quad M\text{ is unramified}
$$

for prime-to-$p$ modules, and the model is unique in the strong finite étale sense. The subtle theory is concentrated in the $p$-primary part. A module of mixed order decomposes canonically into primary components, and its prime-to-$p$ summand is rigid while its $p$-primary summand may have nonétale models.

In equal characteristic $p$, even a $p$-torsion Galois module still has an étale generic group $\mathcal E_K(M)$. A finite-flat model must have that group as generic fiber. Groups such as $\alpha_p$ over $R$ are finite flat objects, but they are not models of nonzero finite Galois modules because their generic fibers are not étale.

### 3.4 First examples and nonexamples

Examples must show both that the definition is populated and that it is restrictive. Constant and multiplicative groups give the basic models, while ramified prime-to-$p$ characters give a clean obstruction.

Every unramified finite module is finite flat: take its unique finite étale $R$-model. In particular, the trivial module $\mathbf Z/n\mathbf Z$ has the constant model $\underline{\mathbf Z/n\mathbf Z}_R$ for every $n$.

The cyclotomic module

$$
\mathbf Z/n\mathbf Z(1)=\mu_n(K^s)
$$

has the model $\mu_n$ whenever $n$ is invertible in $K$. In mixed characteristic this includes $n=p^r$. The model is finite flat even though its special fiber is nonétale when $p\mid n$. Thus a finite-flat representation at residue characteristic $p$ need not be unramified; the mod-$p$ cyclotomic character is the basic counterexample.

The qualification “$n$ is invertible in $K$” concerns the generic fiber. The group $\mu_n$ is finite locally free over $R$ for every $n$, because $R[T]/(T^n-1)$ is free with basis $1,T,\ldots,T^{n-1}$. Its generic fiber represents a Galois module exactly when it is étale, equivalently when $n\ne0$ in $K$. In mixed characteristic this always holds; in equal characteristic $p$, it fails for $p\mid n$.

Not every finite $G_K$-module is finite flat. Assume $k$ has characteristic $p>0$, choose an odd prime $q\ne p$, and suppose $K$ admits a ramified quadratic character

$$
\chi:G_K\to\{\pm1\}\subset\mathbf F_q^\times.
$$

Let $G_K$ act on the additive group $M=\mathbf F_q$ through $\chi$. Its order is $q$, prime to $p$. Every finite-flat model of order $q$ would be finite étale, and its generic module would be unramified. This contradicts the choice of $\chi$. Hence $M$ is not finite flat. The definition imposes a genuine integral ramification constraint, not just finiteness and continuity. At $p$-power order the constraints are subtler, and we will not replace them by an unproved classification.

More generally, if $q\ne p$ and $M$ is any finite $q$-primary module on which inertia acts nontrivially, then $M$ is not finite flat. A putative model would have order invertible in $R$, hence would be finite étale, and Theorem 2.2 would force inertia to act trivially. Thus the prime-to-$p$ part has already been completely characterized. The later geometric work is concentrated exactly where the order is not a unit on the base.

## 4. The generic-fiber functor

### 4.1 Faithfulness

Once models are viewed as integral lattices in a fixed generic object, the first categorical question is whether an integral morphism is determined generically. The answer is yes, and this modest rigidity will later enforce every identity constructed on a model.

Let $\mathrm{FFCG}(R)$ denote the category of finite locally free commutative $R$-group schemes. Generic base change defines

$$
(-)_K:\mathrm{FFCG}(R)\longrightarrow\mathrm{FCG}(K),
$$

where the target is the category of finite commutative $K$-group schemes. Restricting to objects with étale generic fiber and composing with geometric points gives finite continuous $G_K$-modules.

**Proposition 4.1.** The generic-fiber functor is faithful.

**Proof strategy.** Integral functions inject into generic functions because their coordinate algebras are torsion-free.

Suppose $f,g:\mathcal G\to\mathcal H$ have $f_K=g_K$. On coordinate algebras their difference is a map into $A=\mathcal O(\mathcal G)$. After tensoring with $K$ the difference vanishes. Since $A$ is finite free, the map $A\to A\otimes_RK$ is injective. Hence $f^*=g^*$ and $f=g$. $\square$

Faithfulness means that a generic map has at most one integral extension between fixed models. It says nothing about whether the extension exists. This “at most one” principle will repeatedly turn a generic equality into an integral equality after the relevant maps have been constructed.

### 4.2 Failure of fullness

Fullness would say that every generic morphism between generic fibers preserves the two integral Hopf lattices. That is false. Let $R=k[[t]]$ have characteristic $p$ and define primitive-coordinate groups

$$
\mathcal G_1=\operatorname{Spec}R[X]/(X^p-X),
$$

$$
\mathcal G_t=\operatorname{Spec}R[Y]/(Y^p-t^{p-1}Y).
$$

Both are finite flat of order $p$, and both generic fibers are étale because the derivatives of their defining additive polynomials are nonzero over $K=k((t))$. The substitution $Y=tX$ is a generic isomorphism. Its inverse requires $X=t^{-1}Y$ and does not preserve the integral coordinate lattice. The special fibers explain the obstruction: $(\mathcal G_1)_k$ is étale, whereas $(\mathcal G_t)_k\simeq\alpha_p$ is connected.

The equations really define subgroup schemes of the additive group. Give $X$ and $Y$ primitive coproducts,

$$
\Delta(X)=X\otimes1+1\otimes X,\qquad
\Delta(Y)=Y\otimes1+1\otimes Y.
$$

In characteristic $p$, the two defining polynomials are additive, so their ideals are Hopf ideals. Each quotient is free on the powers below $p$. Over $K$, the derivatives are $-1$ and $-t^{p-1}$, both nonzero, which proves étaleness. The integral map corresponds contravariantly to $Y\mapsto tX$. Modulo $t$ it sends $Y$ to zero, so it cannot be an isomorphism.

There is an integral morphism $\mathcal G_1\to\mathcal G_t$ whose generic fiber is the displayed isomorphism, but it is not an integral isomorphism. The inverse generic morphism has no integral extension. Hence the functor is not full, and an isomorphism on generic fibers need not be an isomorphism integrally.

### 4.3 Model groupoids and exact categories

Fix a module $M$. Its **groupoid of finite-flat models**, denoted $\mathrm{Mod}_R(M)$, has objects $(\mathcal G,\iota)$ as in Definition 3.1 and isomorphisms $f:\mathcal G\to\mathcal H$ satisfying

$$
\theta\circ f_K=\iota.
$$

Faithfulness implies that between two fixed objects there is at most one such isomorphism. The groupoid may be empty, may have one isomorphism class, or may have several disconnected isomorphism classes. It is a groupoid because it is designed to compare models of one fixed generic object, not to encode noninvertible morphisms with prescribed generic endomorphism.

For varying modules and exact constructions, fix an integer $n$ and let $\mathscr C_R(n)$ be the category of finite-flat commutative $R$-groups killed by $n$ whose generic fibers are étale. Its admissible short exact sequences are the faithfully flat exact sequences

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0.
$$

This is the appropriate exact-category structure. An admissible monomorphism is a finite-flat closed subgroup whose represented quotient lies in the category; an admissible epimorphism is the corresponding faithfully flat quotient. The category is not asserted to be abelian. Arbitrary kernels can fail to be flat, and arbitrary schematic images need not give faithfully flat image factorizations.

The fixed-exponent subcategory is also not closed under every extension formed in the larger finite-flat category. The constant sequence

$$
0\longrightarrow\mathbf Z/p\mathbf Z
\longrightarrow\mathbf Z/p^2\mathbf Z
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0
$$

has endpoints killed by $p$ and middle term killed only by $p^2$. Thus $\mathscr C_R(n)$ admits those faithfully flat exact sequences whose three terms already lie in it. This qualification is separate from the failure of flat kernels and images.

The generic-fiber functor from $\mathscr C_R(n)$ to finite étale $K$-groups killed by $n$ is faithful and exact on the declared exact sequences. Composing with geometric points gives a faithful exact functor to finite $G_K$-modules killed by $n$.

### 4.4 Essential image and essential uniqueness

The **essential image** consists of the finite $G_K$-modules for which some finite-flat model exists. It is exactly the class singled out by $\operatorname{FF}_R$. This is an existence statement.

By contrast, **essential uniqueness** would mean that the fiber groupoid $\mathrm{Mod}_R(M)$ has at most one isomorphism class. The examples above show that this fails in general. Faithfulness does not imply essential uniqueness: it controls maps after two models are fixed, not the number of possible integral Hopf lattices.

Four logically different assertions should therefore never be compressed into one phrase:

$$
\begin{array}{c|l}
\text{faithful}&\text{an integral map is determined by its generic fiber},\\
\text{full}&\text{every generic map extends integrally},\\
\text{essentially surjective onto a class}&\text{every object in that class has a model},\\
\text{essentially injective}&\text{two models of one generic object are isomorphic}.
\end{array}
$$

Only the first holds without qualification for the generic-fiber functor. Exactness holds on faithfully flat exact sequences. The other properties require additional hypotheses.

## 5. Subrepresentations through schematic closure

### 5.1 Why an ambient model changes the problem

The existential predicate alone does not choose a way to extend a submodule. Once a model of the ambient representation is fixed, however, a generic submodule sits inside a fixed finite-flat group. Over a DVR, schematic closure then supplies a canonical answer. This is the central mechanism behind the stability of finite flatness under subquotients.

Let $(\mathcal G,\iota)$ model $M$, and let $M'\subset M$ be a $G_K$-stable subgroup. The finite étale correspondence turns $M'$ into a closed subgroup

$$
\mathcal E_K(M')\hookrightarrow\mathcal E_K(M).
$$

Transporting by $\iota$ gives a closed subgroup $H_K\subset\mathcal G_K$. The problem is to extend $H_K$ without introducing vertical torsion. Taking arbitrary equations and clearing denominators is not enough: equations supported only on the special fiber can change the rank.

### 5.2 The closure theorem

The desired subgroup is forced by saturation. Proving this requires more than taking topological closure: one must construct a saturated Hopf ideal and verify flatness before descending the group identities.

**Theorem 5.1 (finite-flat closure).** Let $R$ be a DVR, let $\mathcal G$ be a finite-flat commutative $R$-group, and let $H_K\subset\mathcal G_K$ be a closed subgroup. Its schematic closure $\overline H\subset\mathcal G$ is a finite-flat closed subgroup. It is the unique finite-flat closed subgroup of this fixed $\mathcal G$ with generic fiber $H_K$.

**Proof strategy.** Contract the generic Hopf ideal to the integral coordinate algebra. Contraction makes the quotient torsion-free; over a DVR finite torsion-free modules are free. Only after flatness is established do the generic Hopf identities descend integrally.

Write $A=\mathcal O(\mathcal G)$ and let $I_K\subset A_K$ define $H_K$. Put

$$
I=A\cap I_K,\qquad C=A/I.
$$

The natural map $C\to A_K/I_K$ is injective, so $C$ is torsion-free. It is finite over $R$, hence free. To prove that $I$ is a Hopf ideal, observe that $C$ and $C\otimes_RC$ are torsion-free. Since the quotient $A\to C$ splits as a map of $R$-modules, the kernel of $A\otimes_RA\to C\otimes_RC$ is exactly $I\otimes_RA+A\otimes_RI$. The coproduct of an element of $I$ maps to zero after tensoring with $K$, hence already maps to zero in $C\otimes_RC$ and therefore lies in that kernel. Counit and antipode are handled similarly. Thus $\operatorname{Spec}C$ is a finite-flat subgroup.

If another finite-flat closed subgroup has the same generic ideal, its defining ideal is saturated because its coordinate quotient is torsion-free. A saturated submodule of $A$ is recovered by contraction from its generic extension, so its ideal is also $A\cap I_K$. This proves uniqueness. $\square$

The proof uses the one-dimensional valuation ring in a decisive way. Over a Dedekind domain it works locally and glues because finite torsion-free modules are projective. Over a higher-dimensional normal domain, torsion-free need not mean flat, so the same closure can fail to be a finite-flat model.

Closure also commutes with flat extensions of DVRs. Let $R\to R'$ be flat, with fraction field $K'$, and use primes for scalar extensions. Since

$$
0\longrightarrow I\longrightarrow A\longrightarrow C\longrightarrow0
$$

has flat cokernel, tensoring with $R'$ remains exact. The quotient $C\otimes_RR'$ is torsion-free and has generic fiber $(A_{K'}')/I_{K'}$. Hence $I\otimes_RR'$ is the contraction of the extended generic ideal, by uniqueness of saturated contraction. Therefore

$$
(\overline H)_{R'}=\overline{H_{K'}}^{\,\mathcal G_{R'}}.
$$

This compatibility is stronger than preservation of rank. It says that once the ambient model is fixed, forming an integral subrepresentation and extending the local field can be done in either order.

### 5.3 Admissible subobjects and quotients

Closure solves only half of the representation-theoretic problem: a submodule should also leave a quotient model. The finite-flat quotient theorem supplies that second half and turns saturation into an exact sequence.

Apply Theorem 5.1 to $M'\subset M$ and write $\mathcal G'$ for the closure. The represented quotient $\mathcal G/\mathcal G'$ is finite flat, and

$$
0\longrightarrow\mathcal G'\longrightarrow\mathcal G
\longrightarrow\mathcal G/\mathcal G'\longrightarrow0
$$

is faithfully flat exact. Its generic fiber is the exact sequence attached to

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M/M'\longrightarrow0.
$$

Consequently both $M'$ and $M/M'$ are finite flat. More precisely, a chosen model of $M$ induces a uniquely determined model of $M'$ **inside that ambient model**, and a corresponding quotient model of $M/M'$.

Let us justify that the quotient has the claimed generic module. Book 28 proves that a finite-flat closed subgroup of a finite-flat commutative group has a represented finite-flat quotient and that quotient formation commutes with arbitrary base change. Therefore

$$
(\mathcal G/\mathcal G')_K
\simeq\mathcal G_K/\mathcal G'_K.
$$

The finite étale--Galois equivalence is exact, so the geometric points of the right side are $M/M'$. The quotient map is faithfully flat, and the rank formula gives

$$
|\mathcal G/\mathcal G'|=\frac{|M|}{|M'|}=|M/M'|.
$$

No comparison of special-fiber point counts is used.

This proves an important closure statement without claiming that either subquotient has a unique abstract model. If a different model of $M$ is chosen, its closure of $M'$ may be a different integral group. Ambient uniqueness and absolute uniqueness are separate assertions.

The same reasoning handles a $G_K$-stable filtration

$$
0=M_0\subset M_1\subset\cdots\subset M_r=M.
$$

Closing each $M_i$ inside the one fixed $\mathcal G$ gives a filtration by finite-flat closed subgroups. Successive quotients model $M_i/M_{i-1}$. Intersections and sums should always mean the saturated closure of the corresponding generic intersection or sum inside a common ambient object. With that convention their ranks satisfy the expected formulas.

For two stable submodules $M_1,M_2\subset M$, the reliable rank identity is

$$
|\overline{M_1+M_2}|\,|\overline{M_1\cap M_2}|
=|\overline{M_1}|\,|\overline{M_2}|,
$$

where every bar denotes closure inside $\mathcal G$. The equality follows on the generic fiber from the elementary formula for finite abelian groups and then from preservation of rank under closure. It does not assert that the raw integral intersection or the raw image of the addition map is flat. Saturation is part of the construction.

### 5.4 Kernels and images: the unsafe shortcuts

It is tempting to say that the category is closed under all kernels and images because the generic representation category is abelian. This is false. For a morphism $f:\mathcal G\to\mathcal H$ of finite-flat groups, the scheme-theoretic kernel is finite but its coordinate algebra may have $R$-torsion. Likewise, closing the generic image inside $\mathcal H$ gives a finite-flat subgroup, but the induced map from $\mathcal G$ to that closure need not be faithfully flat.

The morphism $\mathcal G_1\to\mathcal G_t$ from §4.2 is decisive. It is an isomorphism generically and zero on the special fiber in the appropriate primitive coordinate. Its raw kernel has trivial generic fiber but a special fiber of order $p$, hence cannot be flat. Its generic image closure is all of $\mathcal G_t$, yet the map to that closure is not faithfully flat: equal finite rank would then force an isomorphism.

There is nevertheless a safe representation-theoretic construction. Given the generic kernel $\ker(f_K)\subset\mathcal G_K$, close it in $\mathcal G$. This produces a finite-flat subgroup modeling $\ker M(f)$. Quotienting $\mathcal G$ by it produces a model of the generic coimage. One must not identify these automatically with the raw scheme-theoretic kernel or with a categorical image of $f$ in all circumstances.

Thus “closed under subobjects and quotients” means closure of generic submodules inside a chosen model followed by represented finite-flat quotient. It does not mean that every finite-flat morphism admits all abelian-category constructions without a flatness check.

## 6. Exact sequences and extension classes

### 6.1 Faithfully flat exactness

Extensions are where finite flatness becomes a genuinely restrictive local condition. A short exact sequence of abstract Galois modules always exists in an abelian category. To model it integrally, the quotient map must be a torsor in the faithfully flat topology, not merely surjective on some collection of points.

A sequence of finite-flat commutative $R$-groups

$$
0\longrightarrow\mathcal G'\xrightarrow{i}\mathcal G
\xrightarrow{q}\mathcal G''\longrightarrow0
$$

is **finite-flat exact** when $i$ identifies $\mathcal G'$ with the scheme-theoretic kernel of $q$ and $q$ is faithfully flat. Equivalently, $\mathcal G''$ represents the faithfully flat sheaf quotient $\mathcal G/\mathcal G'$. This definition is stable under arbitrary base change, and ranks multiply:

$$
|\mathcal G|=|\mathcal G'|\,|\mathcal G''|.
$$

Pointwise surjectivity is neither required nor generally true. A torsor may acquire a section only after a faithfully flat extension of the test ring.

The standard roots-of-unity sequence illustrates the definition in every residue characteristic. For positive integers $a,b$,

$$
0\longrightarrow\mu_a\longrightarrow\mu_{ab}
\xrightarrow{[a]}\mu_b\longrightarrow0
$$

is finite-flat exact. The kernel equation is $T^a=1$, and locally for the faithfully flat topology an element of $\mu_b$ acquires an $a$th root, which is exactly the torsor condition. If the residue characteristic divides $a$, the map need not be surjective on points over a test ring, but it remains a faithfully flat quotient. When the generic characteristic does not divide $ab$, generic geometric points give the corresponding exact cyclotomic module sequence.

### 6.2 Passing an integral sequence to representations

The definition of exactness was chosen so that it survives to the generic module. This section verifies that promise and identifies the converse construction available when a middle model is already known.

**Proposition 6.1.** Suppose the generic fibers in a finite-flat exact sequence are étale. Then geometric generic points form an exact sequence of finite continuous $G_K$-modules.

**Proof strategy.** Base-change to $K^s$, where finite étale groups are constant. Faithfully flat exactness then becomes exactness of the finite abstract groups indexing their components.

After base change to $K$, exactness is preserved. Over $K^s$ all three groups are finite constant schemes. The kernel equality gives exactness at the first two terms, while the faithfully flat quotient becomes a surjection between the indexing finite groups. Descent makes all maps $G_K$-equivariant. $\square$

Conversely, if a finite-flat model $\mathcal G$ of the middle module $M$ is already supplied, closure of $M'\subset M$ produces an integral exact sequence modeling the given generic sequence. Thus every extension that already has a model automatically has compatible subobject and quotient models.

### 6.3 Which generic extensions are finite flat

Separate finite-flat models of two endpoints do not determine which extension classes have integral middle terms. We therefore distinguish realizability with fixed endpoint lattices from existential realizability with some endpoint lattices.

Fix finite-flat modules $M'$ and $M''$. An element

$$
\xi\in\operatorname{Ext}^1_{G_K}(M'',M')
$$

is represented by an exact sequence

$$
0\to M'\to M_\xi\to M''\to0.
$$

We call $\xi$ **finite flat relative to chosen endpoint models** $\mathcal G'$ and $\mathcal G''$ if there is a finite-flat exact sequence

$$
0\to\mathcal G'\to\mathcal G_\xi\to\mathcal G''\to0
$$

whose generic sequence represents $\xi$ under the chosen identifications. We call $\xi$ **finite-flat realizable** if such endpoint models and such a middle sequence exist.

These two notions should not be confused. A generic extension may extend for one choice of endpoint models but not for another. And even though $M'$ and $M''$ separately admit models, an arbitrary class $\xi$ need not admit any finite-flat middle term. Constructing the middle term is extra integral information.

One unconditional implication is useful:

$$
M_\xi\text{ finite flat}\quad\Longrightarrow\quad
M',M''\text{ finite flat},
$$

because closure inside a model of $M_\xi$ constructs the endpoint models and the exact integral sequence. The converse is false as a general principle. Finite flatness is not merely a condition on the Jordan--Hölder factors; it also restricts the extension class.

There is an equivalent formulation that starts from the middle term: $\xi$ is finite-flat realizable if and only if $M_\xi$ is finite flat. One direction is immediate from the integral extension. For the other, choose a model of $M_\xi$, close the embedded copy of $M'$ inside it, and take the represented quotient. Chapter 5 shows that the resulting integral sequence has generic fiber the original extension. This equivalence allows one to test existence without first fixing endpoint models, while the relative notion remembers which endpoint lattices are required.

The endpoint qualification is genuine. A module may have several models; an extension can be compatible with the quotient model induced from its middle term but incompatible with a separately chosen model of the same quotient representation. A generic isomorphism of endpoints does not repair this because it may not preserve the integral Hopf lattices.

The split class is always realizable relative to chosen models: its middle term is $\mathcal G'\times\mathcal G''$. Nonsplit classes occur naturally as well. Suppose $R$ has mixed characteristic $(0,p)$, is henselian, and has perfect residue field. If an elliptic scheme over $R$ has ordinary special fiber, the connected--étale sequence of its $p$-torsion is a finite-flat exact sequence. Because the generic fiber has characteristic zero, its two rank-$p$ terms are étale and give one-dimensional $\mathbf F_p$-representations of $G_K$. The integral middle term remembers how the connected and étale directions meet. The sequence need not split over $R$, even when its special or generic behavior becomes simpler after an extension. This geometric example shows why the allowed classes cannot be replaced by split extensions alone. In equal characteristic $p$, the connected generic term need not be étale, so the same sequence cannot automatically be read as an extension of two Galois modules in the sense of this book.

### 6.4 Pullbacks, pushouts, and Baer operations

For fixed endpoint models, integral extension classes have the expected algebra. Pulling an exact sequence back along a morphism $\mathcal H''\to\mathcal G''$ preserves finite flatness because a torsor remains a torsor after base change. Pushing out along $\mathcal G'\to\mathcal H'$ is formed as the quotient of $\mathcal G\times\mathcal H'$ by the finite-flat graph of $\mathcal G'$; the finite-flat quotient theorem supplies representability and exactness.

The Baer sum of two extensions with the same endpoints is obtained by taking their product, pulling back along the diagonal of $\mathcal G''$, and pushing out along addition on $\mathcal G'$. Every step is among the admissible operations just described. Negation comes from the automorphism $[-1]$ of $\mathcal G'$. Therefore the generic classes arising from extensions of two fixed endpoint models form a subgroup of

$$
\operatorname{Ext}^1_{G_K}(M'',M').
$$

This statement is deliberately categorical rather than cohomological. Computing that subgroup through local cohomology, tangent spaces, or deformation functors belongs later. Here the point is that the geometry supplies a class of extensions stable under the operations required of a local condition.

To check the subgroup assertion fully, the split product represents zero. Pullback and pushout preserve faithfully flat exactness, so the Baer construction stays among integral extensions. Pushing out along $[-1]$ gives the inverse. Associativity and commutativity follow from the corresponding identities for addition on $\mathcal G'$, and generic fiber carries these operations to the ordinary Baer operations. No claim about arbitrary generic extensions enters the proof.

## 7. A calculus of finite-flat representations

### 7.1 Sums, products, and primary parts

The previous chapters handled one subobject or extension at a time. We now assemble those constructions into a calculus that can be applied to decompositions, coefficients, and filtrations without silently assuming an abelian category.

Finite direct sums of modules correspond to finite products of their associated étale group schemes. If $(\mathcal G_i,\iota_i)$ models $M_i$ for $1\le i\le r$, then

$$
\prod_{i=1}^r\mathcal G_i
$$

models $\bigoplus_iM_i$. For a finite family, product and coproduct agree in the category of commutative group objects, so either notation expresses the biproduct. Ranks multiply as cardinalities do:

$$
\left|\prod_i\mathcal G_i\right|=\prod_i|M_i|.
$$

Hence the finite-flat predicate is stable under finite direct sums. The converse follows from subquotient stability: every summand of a finite-flat direct sum is a $G_K$-stable submodule and is finite flat.

If $M$ is killed by $n=\prod_qq^{a_q}$, the coprime idempotents supplied by the Chinese remainder theorem split $M$ into its primary parts $M_q$. The same idempotents act on any model, and their split kernels and images are finite flat. Thus

$$
M\text{ is finite flat}\quad\Longleftrightarrow\quad
M_q\text{ is finite flat for every }q.
$$

If $k$ has characteristic $p>0$, the $q$-primary part for $q\ne p$ is finite flat exactly when it is unramified. All model-theoretic flexibility is concentrated at $q=p$. When $k$ has characteristic zero, every primary part lies in the étale range.

Here is the integral splitting explicitly. Choose integers $e_q$ whose classes in $\mathbf Z/n\mathbf Z$ are the Chinese-remainder idempotents. Integer multiplication defines endomorphisms $[e_q]$ of every model, and

$$
[e_q]^2=[e_q],\qquad [e_q][e_{q'}]=0\ (q\ne q'),
\qquad\sum_q[e_q]=1.
$$

The product of the images of these idempotents maps isomorphically to the original group; the inverse is the tuple of projections. All identities hold integrally because they are identities between integer-multiplication morphisms. Thus no possibly nonflat raw image construction is being used: an idempotent has a split image and kernel, both direct factors of a finite locally free group.

### 7.2 Subquotients and supplied extensions

The closure properties proved so far can be summarized without overstating them.

**Theorem 7.1.** Over the DVR $R$, the class of finite-flat finite $G_K$-modules is stable under:

- finite direct sums and direct summands;
- $G_K$-stable submodules;
- quotients by $G_K$-stable submodules;
- middle terms of extensions for which a finite-flat exact integral sequence is supplied.

For the first three assertions, choose a model and use products or closure and quotient. The fourth is tautologically geometric but important: if

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0
$$

is finite-flat exact, then the generic middle representation is finite flat. What is not asserted is that every abstract extension of two finite-flat modules is finite flat.

This formulation is exactly strong enough for later local conditions. It provides closure under the admissible operations visible in an integral exact category while avoiding a false claim that the essential image is automatically extension-closed for arbitrary generic extension classes.

**Proof.** Products of finite locally free groups are finite locally free and have the direct-sum generic module. A direct summand is a stable submodule, so it is covered by the next case. For $M'\subset M$, choose a model $\mathcal G$ of $M$ and close $\mathcal E_K(M')$ inside $\mathcal G$. Theorem 5.1 makes the closure finite flat, and the finite-flat quotient theorem makes $\mathcal G/\mathcal G'$ a model of $M/M'$. Finally, the middle group in a supplied finite-flat exact sequence is itself a model, and Proposition 6.1 identifies its generic module with the desired extension. $\square$

### 7.3 Coefficient actions and restriction of scalars

Let $\Lambda$ be a finite commutative ring. A finite $\Lambda[G_K]$-module is a finite $G_K$-module $M$ together with a commuting $\Lambda$-action. To model the coefficient structure, one needs more than a model of the underlying abelian group.

**Definition 7.2.** A **$\Lambda$-linear finite-flat model** of $M$ is a finite-flat model $(\mathcal G,\iota)$ together with a ring homomorphism

$$
\Lambda\longrightarrow\operatorname{End}_R(\mathcal G)
$$

whose generic action corresponds under $\iota$ to the given action on $M$. Here addition in the endomorphism ring is pointwise addition of group homomorphisms and multiplication is composition.

The word “ring” includes the identity: $1\in\Lambda$ must act as the identity of $\mathcal G$. If $\Lambda$ has characteristic $n$, then the structure map $\mathbf Z/n\mathbf Z\to\Lambda$ agrees with integer multiplication on the model. This follows generically and hence integrally by faithfulness. Thus coefficient structure refines, rather than replaces, the underlying commutative group structure.

This condition cannot be replaced by saying that each scalar acts generically. A generic endomorphism need not extend to a chosen model. When the integral action is supplied, forgetting along a homomorphism $\Lambda_0\to\Lambda$ immediately gives a $\Lambda_0$-linear model. Thus restriction of coefficient scalars always preserves finite flatness.

The warning concerns a **chosen** model. At the level of the existential predicate, §7.4 will show that one may replace that model and recover any finite commuting coefficient action. Keeping these two levels separate prevents failure of generic fullness from being mistaken for an obstruction to coefficient-linear existence.

Restriction of the local **base ring** is a different operation and is not automatic: an $R'$-model need not descend to $R$. Chapter 9 treats that issue separately.

### 7.4 Extension of coefficient scalars

Let $\Lambda\to\Lambda'$ be a homomorphism of finite commutative rings, and let $M$ be a finite $\Lambda[G_K]$-module. At the representation level one can always form

$$
M_{\Lambda'}=\Lambda'\otimes_\Lambda M.
$$

An arbitrary raw kernel or image of integral scalar maps need not be flat. The ambient closure theorem avoids that obstruction and in fact gives scalar extension for every homomorphism of finite coefficient rings, not only for projective ones.

Choose a surjection of $\Lambda$-modules

$$
P=\Lambda^m\twoheadrightarrow\Lambda'.
$$

Tensoring with $M$ gives a $G_K$-equivariant surjection

$$
P\otimes_\Lambda M\simeq M^m
\longrightarrow\Lambda'\otimes_\Lambda M.
$$

Let $N$ be its kernel. Starting with a $\Lambda$-linear model $\mathcal G$ of $M$, close $\mathcal E_K(N)$ inside $\mathcal G^m$ and call the closure $\mathcal H$. The represented quotient

$$
\mathcal Q=\mathcal G^m/\mathcal H
$$

is finite flat and has generic module $\Lambda'\otimes_\Lambda M$. It remains to recover the $\Lambda'$-action, since generic fullness cannot simply be invoked.

The construction is independent of the chosen presentation at the level that matters here. Two presentations can be dominated by their direct sum. The induced quotient models need not be canonically isomorphic as unmarked integral groups, but each is a valid $\Lambda'$-linear witness for the same generic module. Since finite flatness is existential, no stronger presentation-independence is needed.

For $a\in\Lambda'$, multiplication by $a$ on $\Lambda'$ lifts through $P\twoheadrightarrow\Lambda'$ to a $\Lambda$-linear endomorphism of the free module $P$. The resulting matrix of $\Lambda$-scalars acts on $\mathcal G^m$. It preserves $\mathcal H$: generically it preserves $N$, and the defining ideal then vanishes on $\mathcal H$ by torsion-freeness. Hence it descends to an endomorphism of $\mathcal Q$. Two choices of lift induce the same generic endomorphism of $\mathcal Q$, so faithfulness makes them equal integrally. The unit, addition, and multiplication identities for these endomorphisms also hold generically and therefore integrally. They define the required ring homomorphism $\Lambda'\to\operatorname{End}_R(\mathcal Q)$.

The lifting step uses only that $P$ is free. If $q:P\to\Lambda'$ is the chosen surjection, then $m_a\circ q:P\to\Lambda'$ lifts to an endomorphism $T_a:P\to P$. For $x\in\ker q$, one has $q(T_ax)=a q(x)=0$, so $T_a$ preserves the relation module already before tensoring with $M$. Different lifts differ by a map landing in $\ker q$ and hence act trivially on the generic quotient. This proves both preservation of the closure and independence of choices without assuming that $\Lambda'$ is projective over $\Lambda$.

**Proposition 7.3.** For every homomorphism $\Lambda\to\Lambda'$ of finite commutative rings, scalar extension carries a $\Lambda$-linear finite-flat module $M$ to the $\Lambda'$-linear finite-flat module $\Lambda'\otimes_\Lambda M$.

For a quotient $\Lambda'=\Lambda/I$, the construction has a simpler description. Close the generic submodule $IM\subset M$ inside $\mathcal G$ and quotient by that closure. The $\Lambda$-action descends, while every element of $I$ acts as zero generically and hence as zero integrally; the action therefore factors through $\Lambda/I$. This uses the finite-flat closure of the **generic** relation subgroup, not a possibly nonflat raw scheme-theoretic image such as $I\mathcal G$ or a raw torsion kernel.

There is a useful consequence for actions that were initially visible only on the generic module.

**Corollary 7.4.** Let $M$ be a finite $\Lambda[G_K]$-module. Then $M$ has a $\Lambda$-linear finite-flat model if and only if its underlying abelian $G_K$-module is finite flat.

**Proof strategy.** One direction forgets scalars. For the other, enlarge an underlying model until the $\Lambda$-action is tautological, then recover $M$ as a quotient.

Let $n$ be the characteristic of $\Lambda$. The underlying module and every model of it are killed by $n$, so the model is automatically $\mathbf Z/n\mathbf Z$-linear. Proposition 7.3 gives a $\Lambda$-linear model of

$$
\Lambda\otimes_{\mathbf Z/n\mathbf Z}M.
$$

The action map $a\otimes m\mapsto am$ is a surjective $\Lambda[G_K]$-homomorphism onto $M$. Close its generic kernel in the supplied model and take the represented finite-flat quotient. Stability of the generic kernel under $\Lambda$ makes its closure $\Lambda$-stable, so the quotient is the required $\Lambda$-linear model of $M$. $\square$

This resolves an apparent tension. Generic fullness fails for a fixed model, so that particular model need not carry the desired scalars. The existential predicate is nevertheless insensitive to the failure: products, closure, and quotient construct another model on which the coefficient action is integral. Thus “this chosen model is $\Lambda$-linear” is extra data, whereas “the representation has some $\Lambda$-linear model” is equivalent to finite flatness of the underlying abelian module.

## 8. Cartier duality and the Tate twist

### 8.1 Why the ordinary linear dual is not enough

A pairing on a finite torsion representation naturally takes values in roots of unity, not in a trivial copy of its coefficient ring. This is why Cartier duality produces a Tate twist. Let $M$ be killed by $n$ and assume

$$
n\in K^\times.
$$

Equivalently, $\operatorname{char}K$ does not divide $n$. Then $\mu_n$ is finite étale over $K$, and define

$$
M^*(1)=\operatorname{Hom}_{\mathbf Z}
\bigl(M,\mu_n(K^s)\bigr)
$$

with action

$$
(\sigma f)(m)=\sigma\bigl(f(\sigma^{-1}m)\bigr).
$$

If $M$ is free over $\mathbf Z/n\mathbf Z$, this is the familiar ordinary module dual tensored with $\mathbf Z/n\mathbf Z(1)$. The displayed Hom formulation is canonical for arbitrary finite modules killed by $n$.

The construction does not depend on choosing the least possible annihilator. If $nM=0$ and $n\mid n'$, every homomorphism $M\to\mu_{n'}(K^s)$ lands in $\mu_n(K^s)$ because $f(m)^n=f(nm)=1$. Thus the character group is intrinsically

$$
\operatorname{Hom}\bigl(M,(K^s)^\times\bigr),
$$

and $\mu_n$ is simply a finite target through which every character factors. Its order equals $|M|$: after forgetting Galois action, the character group of a finite abelian group over a separably closed field of characteristic prime to its exponent has the same elementary divisors.

Choosing a primitive root identifies $\mu_n(K^s)$ with $\mathbf Z/n\mathbf Z$ as an abstract group, but transports the cyclotomic action to the target. Forgetting it would turn a Galois-equivariant evaluation pairing into a generally non-equivariant one. The twist is therefore forced by the geometry.

If $\operatorname{char}K$ divides $n$, the generic Cartier dual of an étale group can be nonétale. Its geometric points then need not encode the dual scheme. Cartier duality still exists, but the formula above does not furnish a dual finite Galois module of the same kind. This is why the invertibility hypothesis is explicit.

### 8.2 Dual models

Having identified the correct twisted generic dual, we now ask whether duality preserves integral realizability. Base-change compatibility of Cartier duality gives exactly the required bridge.

Let $(\mathcal G,\iota)$ be a finite-flat model of $M$, with $nM=0$ and $n\in K^\times$. Cartier duality produces a finite-flat commutative group $\mathcal G^D$, is compatible with arbitrary base change, and gives

$$
(\mathcal G^D)_K\simeq(\mathcal G_K)^D.
$$

The character description of the finite étale generic fiber identifies the right side with $\mathcal E_K(M^*(1))$. Hence:

**Theorem 8.1.** Let $nM=0$ and assume $n\in K^\times$. If $\mathcal G$ is a finite-flat model of $M$, then $\mathcal G^D$ is a finite-flat model of $M^*(1)$. In particular,

$$
M\text{ finite flat}\quad\Longleftrightarrow\quad M^*(1)\text{ finite flat}.
$$

The reverse implication follows from biduality. Notice that the theorem transports a **chosen** model to a chosen dual model. It does not say that all models of $M^*(1)$ arise uniquely this way without remembering generic identifications, though biduality does give an anti-equivalence between the corresponding model groupoids.

**Proof strategy.** Commute Cartier duality with the generic fiber, then read the characters of the resulting finite étale group on geometric points.

Finite local freeness of $\mathcal G$ makes its dual Hopf algebra finite locally free, so $\mathcal G^D$ is an allowed integral object. Base change gives $(\mathcal G^D)_K\simeq(\mathcal G_K)^D$. Because $n$ is invertible in $K$, both sides are finite étale, and evaluation into $\mu_n$ identifies the geometric points of the latter with $\operatorname{Hom}(M,\mu_n(K^s))$ carrying the displayed Galois action. This constructs the required generic identification. Applying the same argument to $\mathcal G^D$ and using $\mathcal G^{DD}\simeq\mathcal G$ proves the converse. $\square$

The Galois action formula follows from evaluation. If $f$ is a character and $m\in M$, equivariance of the evaluation pairing requires

$$
\langle\sigma f,\sigma m\rangle
=\sigma\langle f,m\rangle.
$$

Replacing $m$ by $\sigma^{-1}m$ gives precisely

$$
(\sigma f)(m)=\sigma(f(\sigma^{-1}m)).
$$

This derivation shows that the inverse on the argument is contragredience and the outer action is the Tate twist; neither is a convention that may be dropped.

If $\mathcal G$ carries an action of a commutative coefficient ring $\Lambda$, contravariance sends each scalar endomorphism to an endomorphism of $\mathcal G^D$. The scalar endomorphisms commute, so the reversed order of composition causes no ambiguity and gives a $\Lambda$-action on the dual. On generic points this is the contragredient coefficient action. Thus Theorem 8.1 also preserves coefficient-linear finite flatness, with the Tate twist retained.

### 8.3 Exactness and annihilators

Duality is most useful when it controls subquotients, not merely isolated objects. Exactness reverses a quotient sequence and identifies the integral closure of a generic annihilator.

Cartier duality reverses finite-flat exact sequences. From

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0
$$

one obtains

$$
0\to(\mathcal G'')^D\to\mathcal G^D\to(\mathcal G')^D\to0.
$$

On generic modules this is

$$
0\to(M'')^*(1)\to M^*(1)\to(M')^*(1)\to0.
$$

If $\mathcal H\subset\mathcal G$ is the closure of a generic submodule, its annihilator

$$
\mathcal H^\perp=\ker(\mathcal G^D\to\mathcal H^D)
$$

is finite flat and is the closure of the generic annihilator inside the fixed ambient dual model. Thus closure and annihilator commute. The qualification “inside the fixed ambient model” is again essential.

The proof is short but uses both prerequisite theorems in their exact forms. Cartier duality reverses the faithfully flat exact sequence

$$
0\to\mathcal H\to\mathcal G\to\mathcal G/\mathcal H\to0,
$$

so $\mathcal H^\perp\simeq(\mathcal G/\mathcal H)^D$ is finite flat. Its generic fiber is the character subgroup trivial on $\mathcal H_K$. It is therefore a finite-flat closed subgroup of $\mathcal G^D$ with the same generic fiber as the generic annihilator. Uniqueness of schematic closure inside $\mathcal G^D$ identifies the two. Biduality then gives the double-annihilator identity

$$
(\mathcal H^\perp)^\perp=\mathcal H.
$$

### 8.4 Self-dual geometric representations

Polarized abelian schemes provide the main source of perfect integral pairings. Their torsion explains both the Tate twist and the determinant constraint that recur in two-dimensional arithmetic representations. Retain the hypothesis $n\in K^\times$ when passing to generic Galois modules, although the integral group-scheme pairing itself exists without it.

Let $A/R$ be an abelian scheme. The Weil pairing and the dual abelian scheme give

$$
A[n]^D\simeq A^\vee[n].
$$

For an elliptic scheme $E/R$, the canonical principal polarization yields

$$
E[n]^D\simeq E[n].
$$

On the generic Galois module this becomes a perfect alternating pairing

$$
E[n](K^s)\times E[n](K^s)\longrightarrow\mu_n(K^s)
$$

and an isomorphism $E[n]\simeq E[n]^*(1)$. In rank two this forces the determinant to be cyclotomic. The integral statement is stronger than the pointwise one at residue characteristic: even when the special-fiber point pairing degenerates visibly, the scheme-theoretic Weil pairing remains perfect.

Here is the determinant calculation. Assume $n$ is invertible in $K$ and choose a basis $P,Q$ of the free rank-two module $E[n](K^s)$ such that $e_n(P,Q)$ is primitive. If $A_\sigma$ is the matrix of $\sigma$, bilinearity and alternation give

$$
e_n(\sigma P,\sigma Q)=e_n(P,Q)^{\det A_\sigma}.
$$

Galois equivariance gives the same left side as

$$
\sigma e_n(P,Q)=e_n(P,Q)^{\chi_n(\sigma)}.
$$

Primitivity yields $\det A_\sigma=\chi_n(\sigma)$ in $(\mathbf Z/n\mathbf Z)^\times$. Although a basis was used for the calculation, determinant and the cyclotomic character are intrinsic. When $n$ is not invertible on the special fiber, the calculation remains valid generically in mixed characteristic, while perfectness over $R$ is the stronger group-scheme statement supplied by Cartier duality.

## 9. Changing the local field

### 9.1 Restriction by base change

Local representations are often examined after enlarging the local field. The forward operation is geometric base change and is automatic; the reverse operation is descent and requires extra integral compatibility. This chapter separates those directions.

Let $L/K$ be a finite separable extension and let $R_L=\mathcal O_L$. Choose a $K$-embedding $L\hookrightarrow K^s$; then $K^s$ is also a separable closure of $L$, and $G_L$ identifies with a subgroup of $G_K$ up to conjugacy. If $(\mathcal G,\iota)$ models $M$, ordinary base change gives

$$
\mathcal G_{R_L}=\mathcal G\times_RR_L.
$$

The ring $R_L$ is finite free over $R$, and the generic fiber of this base change corresponds to the restricted module $M|_{G_L}$. Therefore

$$
\operatorname{FF}_R(M)\quad\Longrightarrow\quad
\operatorname{FF}_{R_L}(M|_{G_L}).
$$

Each hypothesis has a role. Separability permits $G_L$ to be read as a subgroup of $G_K$ and identifies generic scalar extension with restriction of the Galois action. Finiteness ensures, by the local extension theory of Book 2, that $R_L$ is finite free over $R$. Flatness then preserves finite local freeness, exact sequences, and ranks. A purely inseparable change has no subgroup interpretation of this form and is not the representation-theoretic scalar extension considered here.

Finite-flat exact sequences, coefficient actions, Cartier duals, and products all commute with this base change. Schematic closure of a generic subgroup also commutes with the flat extension of DVRs $R\to R_L$. Thus a model and every admissible construction made inside it can be transported coherently to $L$.

In particular, for $M'\subset M$ the two natural models after restriction agree:

# $$\left(\overline{\mathcal E_K(M')}^{\,\mathcal G}\right)_{R_L}

\overline{\mathcal E_L(M'|_{G_L})}^{\,\mathcal G_{R_L}}.
$$

Thus closing a subrepresentation and extending the local field may be done in either order.

This operation is restriction of the **Galois group** together with extension of the **valuation ring**. It should not be confused with restriction or extension of the coefficient ring $\Lambda$ from Chapter 7.

### 9.2 Unramified and ramified extensions

The preservation theorem does not require $L/K$ to be unramified. Nevertheless, ramification affects what can happen in the reverse direction.

If $L/K$ is unramified, the ramification index is one and the special fiber is changed by the separable residue extension $k_L/k$. Connectedness, étaleness, and rank of the special fiber behave by ordinary field base change. Inertia groups satisfy $I_L=I_K$ under the standard embedding, so an unramified extension cannot make a genuinely ramified prime-to-$p$ module unramified.

If $L/K$ is ramified, the uniformizer scale changes and new integral Hopf lattices can become available. Generic points that did not have the required integral behavior over $R$ may acquire it over $R_L$. Base change still preserves a model already present, but existence after ramified base change is strictly weaker than existence before it.

Here is a concrete representation-theoretic witness. Let $K$ have odd residue characteristic $p$, choose an odd prime $q\ne p$, and let

$$
\chi:G_K\longrightarrow\{\pm1\}\subset\mathbf F_q^\times
$$

be a ramified quadratic character. Give the additive group $M=\mathbf F_q$ the action $\sigma m=\chi(\sigma)m$. Its order is $q$, prime to $p$. If $M$ had a finite-flat $R$-model, that model would be finite étale, forcing $M$ to be unramified. Thus $M$ is not finite flat over $R$. Over the quadratic extension cut out by $\chi$, the restricted module is trivial and has the constant finite étale model. Hence potential finite flatness does not imply finite flatness.

### 9.3 Faithfully flat descent

Since $R_L/R$ is finite faithfully flat, affine finite-flat group schemes satisfy effective descent. But an object over $R_L$ descends only when it is equipped with descent data. In its most intrinsic form, this is an isomorphism

$$
p_1^*\mathcal H\xrightarrow{\sim}p_2^*\mathcal H
$$

over $R_L\otimes_RR_L$, satisfying the cocycle condition after a third base change. The Hopf operations and any coefficient action must be compatible with this isomorphism. Effective faithfully flat descent then produces a finite-flat $R$-group $\mathcal G$ whose base change is $\mathcal H$.

**Theorem 9.1 (descent criterion for a model).** Let $L/K$ be finite separable, put $R_L=\mathcal O_L$, and let $M$ be a finite continuous $G_K$-module. A finite-flat $R_L$-model $(\mathcal H,\eta)$ of $M|_{G_L}$ descends to an $R$-model of $M$ if and only if it carries effective descent data relative to $R_L/R$ preserving the group law, every coefficient action, and the generic marking $\eta$. The descended marked model is unique up to unique isomorphism.

**Proof strategy.** Descend the finite projective coordinate algebra and each Hopf map, and then descend the marking. Faithful flatness detects all identities.

Put $B=\mathcal O(\mathcal H)$. The datum descends the finite projective $R_L$-algebra $B$ to a finite projective $R$-algebra $A$. Compatibility descends multiplication, unit, coproduct, counit, antipode, and coefficient endomorphisms. Their identities may be checked after the faithfully flat base change, so $\operatorname{Spec}A$ is a finite-flat commutative $R$-group with the required scalars. The compatible generic marking descends to $\mathcal G_K\simeq\mathcal E_K(M)$. Full faithfulness of descent and generic-fiber faithfulness give uniqueness. Conversely, the base change of any downstairs marked model carries the canonical descent datum, compatible with every part of its structure. $\square$

When $L/K$ is Galois, one often describes such data as compatible semilinear isomorphisms $\gamma^*\mathcal H\simeq\mathcal H$ for $\gamma\in\operatorname{Gal}(L/K)$. In the ramified case this shorthand must still encode descent over the possibly nonreduced ring $R_L\otimes_RR_L$; a collection of actions on geometric points is not a substitute for scheme-theoretic descent data.

Suppose $M$ is already a $G_K$-module and $\mathcal H$ models $M|_{G_L}$. The generic identification supplies descent data on the generic fiber only. To descend the model, those generic isomorphisms must extend to the integral Hopf lattice. Generic-fiber faithfulness gives uniqueness of each extension if it exists, and then forces the cocycle identity. It does not give existence.

Consequently the cocycle is not the difficult check after integral extensions have been found. The two composites over a triple overlap have the same generic fiber, and faithfulness forces them to agree. The hard issue is whether each generic comparison preserves the integral Hopf lattice in the first place.

### 9.4 Why potential finite flatness is weaker

The failure of fullness from Chapter 4 is the model-theoretic obstruction to automatic descent. A generic isomorphism may fail to preserve an integral Hopf lattice. Descent asks for several such integral isomorphisms simultaneously. The equal-characteristic pair $\mathcal G_1,\mathcal G_t$ shows already that even one generic isomorphism between finite-flat models need not extend in both directions; knowing only the generic descent datum therefore cannot suffice.

There are two separate obstructions:

- the restricted representation may lose ramification, as in the quadratic prime-to-$p$ example, so no downstairs model can exist;
- even when a downstairs generic representation is fixed, a chosen upstairs model may not be stable under the required semilinear descent isomorphisms.

Descent is valid when the full integral datum exists. A base-changed model carries its canonical descent datum and descends back to the original model. More generally, an upstairs model with compatible effective descent datum descends, and its generic identification descends when it is compatible. Without that datum, “finite flat after extension” is only a potential property.

## 10. Rigidity and multiplicity of models

### 10.1 Prime-to-residue-characteristic rigidity

The simplest uniqueness theorem comes from étaleness. Let $M$ have order prime to $p$. Any finite-flat model $\mathcal G$ has invertible order over $R$. A finite locally free group scheme of invertible order is finite étale. Since $R$ is henselian, it follows that:

**Theorem 10.1.** Assume $\operatorname{char}k=p>0$. If $p\nmid|M|$, then the following are equivalent:

1. $M$ is finite flat over $R$;
2. $M$ is unramified;
3. $M$ has a finite étale $R$-model.

When these conditions hold, the model with its generic identification is unique up to unique isomorphism, and every generic morphism between such models extends uniquely.

**Proof strategy.** Show first that no connected infinitesimal special fiber can occur when the group order is invertible, then invoke henselian rigidity for finite étale objects.

If $\mathcal G$ models $M$, every geometric fiber has order $|M|$ invertible in its residue field. A finite group scheme over a field whose order is prime to the characteristic is étale. In particular the special fiber is étale, so the finite relative differential module has zero reduction. Nakayama's lemma makes it zero over the local ring $R$. Hence the finite locally free group $\mathcal G$ is finite étale, and Theorem 2.2 makes $M$ unramified. Conversely, an unramified $M$ has the finite étale model of Theorem 2.2. The same theorem supplies uniqueness and extension of morphisms. $\square$

The statement concerns the order, not merely the order of the image of $G_K$. A wildly ramified action on an abstract group of prime-to-$p$ order still cannot be finite flat, because any putative model would be étale. Conversely, unramifiedness gives the model by henselian étale lifting.

For $p$-power order, neither implication remains a general characterization. A finite-flat model may be connected or mixed on the special fiber, and its generic representation may be ramified. The cyclotomic module modeled by $\mu_{p^r}$ is the fundamental example.

### 10.2 Constant and multiplicative models

Prime-to-$p$ rigidity fails as soon as the special fiber can be nonétale. The simplest witness compares the two groups exchanged by Cartier duality and shows that even a trivial generic action need not force a unique integral specialization.

Let $R$ have mixed characteristic $(0,p)$ and suppose $K$ contains a primitive $p$th root of unity. Then the generic groups

$$
\underline{\mathbf Z/p\mathbf Z}_K
\quad\text{and}\quad
\mu_{p,K}
$$

are isomorphic. Both therefore model the same trivial $G_K$-module after a generic identification. Integrally they are not isomorphic. The constant group has an étale special fiber with $p$ geometric points, whereas $\mu_p$ has a connected nonreduced special fiber with one geometric point and length $p$.

Choose a primitive root $\zeta_p\in K$. The map

$$
\mathbf Z/p\mathbf Z\longrightarrow\mu_p(K),
\qquad a\longmapsto\zeta_p^a,
$$

identifies the two split finite étale generic groups. On the special fiber,

$$
T^p-1=(T-1)^p,
$$

so $\mu_{p,k}$ is connected, whereas the constant group is a disjoint union of $p$ copies of $\operatorname{Spec}k$. An integral isomorphism would preserve connected components after base change, which is impossible.

This example separates existence from uniqueness in the most economical way. The representation is split and trivial; nonuniqueness is not caused by a complicated Galois action. It is caused by two different ways for the same generic points to meet the special fiber.

The assumption about roots of unity is essential. Without it, the generic module of $\mu_p$ is the mod-$p$ cyclotomic module, not the trivial constant module. The two integral groups still exist, but they do not model the same $G_K$-module.

### 10.3 An equal-characteristic lattice example

Mixed characteristic is not responsible for nonuniqueness. An explicit additive family in equal characteristic shows how the valuation depth of a Hopf lattice can vary while the generic representation remains fixed.

The groups

$$
\mathcal G_1=\operatorname{Spec}R[X]/(X^p-X),\qquad
\mathcal G_t=\operatorname{Spec}R[Y]/(Y^p-t^{p-1}Y)
$$

over $R=k[[t]]$ give a second nonuniqueness mechanism. Their generic fibers are isomorphic finite étale groups under $Y=tX$, yet one special fiber is étale and the other is $\alpha_p$. In this displayed example the generic module is in fact split: the roots of $X^p-X$ are the elements of $\mathbf F_p\subset K$. Thus even a trivial generic module can acquire genuinely different integral Hopf lattices in equal characteristic.

The example also displays a partial order of lattices. The generic isomorphism extends in one direction as a nonisomorphic integral map. Such a map is neither an admissible monomorphism nor an admissible epimorphism merely because it is generically an isomorphism. Its failure of flat kernel measures the valuation depth between the two Hopf lattices.

There is in fact a chain of such lattices. For $i\ge0$ put

$$
\mathcal G_{t^i}
=\operatorname{Spec}R[Z_i]/(Z_i^p-t^{i(p-1)}Z_i).
$$

The substitution $Z_{i+1}=tZ_i$ gives

$$
\mathcal G_{t^0}\longrightarrow\mathcal G_{t^1}
\longrightarrow\cdots\longrightarrow\mathcal G_{t^r}.
$$

All generic fibers are the same split étale group. For every $i>0$ the special fiber is $\alpha_p$. The models are nevertheless pairwise nonisomorphic: the cotangent module at the identity is

$$
e^*\Omega_{\mathcal G_{t^i}/R}
\simeq R/(t^{i(p-1)})\,dZ_i,
$$

because differentiating the relation at the identity gives $-t^{i(p-1)}dZ_i=0$. Its $R$-length is $i(p-1)$, an isomorphism invariant. Hence even the pair consisting of generic and special isomorphism types does not classify a model; valuation depth in the Hopf lattice supplies additional integral information.

No attempt will be made to classify all lattices or all models. Even rank-$p$ classification depends delicately on ramification and on the base. The examples are used only to establish the structural facts needed later: nonuniqueness occurs, generic maps need not extend, and special-fiber type carries information absent from the representation.

### 10.4 Three distinct uniqueness statements

Several useful rigidity assertions remain valid, but each has its own domain.

1. **Uniqueness of a morphism.** Between fixed finite-flat models, a prescribed generic morphism has at most one integral extension. This is generic-fiber faithfulness.

2. **Uniqueness inside an ambient model.** A generic closed subgroup of a fixed finite-flat group has exactly one finite-flat closed extension, its schematic closure.

3. **Uniqueness of an abstract model.** A generic finite étale group may have only one finite-flat model in a specified subcategory, as happens for prime-to-$p$ models because all are étale.

The first two hold broadly over a DVR. The third fails at residue-characteristic torsion unless extra rigidity hypotheses are imposed. Saying simply “the model is unique” without naming which of these is intended is therefore mathematically ambiguous.

## 11. Geometric sources of finite-flat representations

### 11.1 Good reduction and torsion

The principal supply of finite-flat representations comes from abelian varieties with good reduction. Let $A/K$ be an abelian variety of dimension $g$ that extends to an abelian scheme $\mathcal A/R$. For every $n\ge1$, multiplication by $n$ on $\mathcal A$ is finite locally free and faithfully flat of degree $n^{2g}$. Its kernel

$$
\mathcal A[n]=\ker([n]:\mathcal A\to\mathcal A)
$$

is a finite-flat commutative $R$-group of order $n^{2g}$.

This finite-flatness is not obtained by inspecting only the generic fiber. On an abelian scheme the differential of $[n]$ is multiplication by $n$ on the tangent bundle. When $n$ is not a unit, this differential may vanish on the special fiber, so étaleness fails. Properness and the group structure instead show that $[n]$ is a finite faithfully flat isogeny; fiberwise its degree is $n^{2g}$, and its kernel is finite locally free of that rank. This is precisely the theorem from Book 28 that makes abelian schemes useful at residue-characteristic torsion.

If $\mathcal A[n]_K=A[n]$ is étale, then $\mathcal A[n]$ models the Galois module $A[n](K^s)$. This is automatic when $n$ is invertible in $K$, in particular for every $n$ when $K$ has characteristic zero. Thus over a $p$-adic field, all finite torsion representations of an abelian variety with good reduction are finite flat, including its $p$-power torsion.

At primes $q\ne p$, $n=q^r$ is invertible already over $R$, so $\mathcal A[q^r]$ is finite étale and the representation is unramified. At $n=p^r$ in mixed characteristic, the generic fiber is still étale but the integral group need not be. Good reduction gives finite flatness rather than unramifiedness. This is the precise refinement of the prime-to-$p$ specialization theorem.

**Proposition 11.1 (torsion from good reduction).** Assume $\operatorname{char}K=0$ and $A/K$ extends to an abelian scheme $\mathcal A/R$. Then for every $n\ge1$, the finite $G_K$-module $A[n](K^s)$ is finite flat over $R$. If $\operatorname{char}k=p>0$ and $p\nmid n$, it is unramified and its model is uniquely finite étale. If $p\mid n$, no unramifiedness conclusion follows. When $\operatorname{char}k=0$, every $n$ lies in the rigid étale range.

**Proof.** Characteristic zero makes $A[n]$ finite étale over $K$. The finite locally free group $\mathcal A[n]$ has this generic fiber, hence is a model. If $\operatorname{char}k=p>0$ and $p\nmid n$, Theorem 10.1 applies. If $\operatorname{char}k=0$, the order is a unit in $R$, so the same differential argument used in Theorem 10.1 makes the model finite étale. The cyclotomic example and ordinary elliptic torsion below show why unramifiedness cannot be concluded at $p$-power order. $\square$

### 11.2 Elliptic curves at the residue characteristic

Dimension one makes the geometry especially concrete. The ordinary and supersingular special fibers exhibit two radically different ways in which a rank-two generic torsion representation can specialize without losing scheme-theoretic rank.

For an elliptic curve $E/K$ with good reduction and elliptic scheme $\mathscr E/R$,

$$
\mathscr E[n]
$$

has order $n^2$. In mixed characteristic, $E[p^r](K^s)\simeq(\mathbf Z/p^r\mathbf Z)^2$, and $\mathscr E[p^r]$ is its finite-flat model. The special fiber explains why the associated $p$-adic or mod-$p$ representation can be ramified despite good reduction.

If the special elliptic curve is ordinary, its $p$-torsion has a connected multiplicative direction and an étale direction. Over an algebraic closure of the residue field there is an exact connected--étale pattern

$$
0\to\mu_p\to\mathscr E_k[p]
\to\underline{\mathbf Z/p\mathbf Z}\to0,
$$

without an automatic splitting over the original residue field or over $R$. If it is supersingular, the whole special $p$-torsion is connected of order $p^2$. In either case the generic module remains two-dimensional in mixed characteristic; special geometric points alone do not recover it.

In equal characteristic $p$, the qualification from Chapter 1 returns. The group scheme $E[p^r]$ can have a nonétale generic connected part. Its geometric points may have rank one in the ordinary case and be trivial in the supersingular case. Therefore $\mathscr E[p^r]$ is not, in general, a model of a rank-two finite Galois module under Definition 3.1. For $n$ prime to $p$, it is finite étale and the usual theory applies.

### 11.3 Abelian schemes and finite-flat subgroup closures

Torsion models become more useful when invariant subrepresentations are retained. Schematic closure turns a generic isogeny kernel into an integral kernel and simultaneously constructs its quotient.

Suppose again that $\operatorname{char}K=0$, let $V\subset A[n](K^s)$ be a $G_K$-stable subgroup, and identify it with a generic subgroup $H_K\subset\mathcal A[n]_K$. Its schematic closure

$$
\mathcal H=\overline{H_K}^{\,\mathcal A[n]}
$$

is finite flat and models $V$. The quotient $\mathcal A[n]/\mathcal H$ models $A[n](K^s)/V$. Moreover, the quotient abelian scheme $\mathcal A/\mathcal H$ exists, and the map $\mathcal A\to\mathcal A/\mathcal H$ extends the generic isogeny with kernel $H_K$.

For an elliptic curve, a $G_K$-stable line in $E[\ell](K^s)$ is the generic kernel of a cyclic $\ell$-isogeny. With good reduction, its closure inside $\mathscr E[\ell]$ is the integral kernel, even when $\ell=p$ and the special kernel becomes connected. This unifies three viewpoints developed earlier in the series:

- the abelian scheme supplies a smooth proper group over $R$ and its finite multiplication kernel;
- finite étale descent supplies the generic Galois representation and its invariant submodules;
- finite-flat group schemes and Cartier duality supply closure, quotients, and the Weil pairing.

In the prerequisite chain, Book 17 proves the finite étale--Galois dictionary, Book 28 proves integral torsion kernels, schematic closure, and represented quotients, and Book 34 proves the Weil pairing and its perfectness. The present book identifies their common output as a finite-flat Galois representation and proves which representation-theoretic operations preserve it.

The ambient torsion group is what makes the closure canonical. A bare invariant line need not possess a preferred model independently of this embedding.

### 11.4 Good reduction versus other reduction types

Good reduction is a strong sufficient source of finite-flat torsion, not a classification of all finite-flat representations. Conversely, one should not infer from the finite flatness of one torsion representation that the elliptic curve has good reduction without a separate theorem and its hypotheses.

For multiplicative reduction, the Tate-curve description gives extensions involving roots of unity and the Tate parameter. It is invaluable for computing the generic Galois action, but the proper smooth abelian model used above is absent. The closure argument inside $\mathscr E[n]$ cannot simply be repeated because there is no elliptic scheme $\mathscr E/R$ with that generic fiber. Some individual subquotients may have finite-flat models for independent reasons; the generic Tate sequence by itself does not provide the required integral exact sequence.

At additive reduction, coarse reduction type gives still less direct control. Potential good reduction after a field extension may yield potential finite flatness of torsion, but Chapter 9 shows that descent is a separate question. These cautions keep the geometric examples aligned with their exact hypotheses.

## 12. Coefficients and two-dimensional residual representations

### 12.1 Actions by a finite coefficient ring

Arithmetic representations usually carry more structure than an action on a finite abelian group. Let $\Lambda$ be a finite local commutative ring with residue characteristic $\ell$, and let $V$ be a finite $\Lambda$-module with continuous $\Lambda$-linear $G_K$-action. The appropriate structured predicate is:

$$
V\text{ is finite flat over }R
$$

if it has a $\Lambda$-linear finite-flat model in the sense of Definition 7.2.

The action is genuine structure on a chosen model. A model of the underlying group does not automatically admit every generic $\Lambda$-endomorphism, because generic fullness fails. For $\Lambda=\mathbf F_\ell$, the scalar action on any underlying model is generated by integer multiplication and is automatic. For a larger finite field or a nontrivial finite coefficient ring, one must either verify the action on the chosen model or replace it by the model constructed in Corollary 7.4. Consequently the **existence** of a $\Lambda$-linear model is equivalent to finite flatness of the underlying abelian module, even though the extra action on any particular witness is not automatic.

If $V$ is free of rank $d$ over $\Lambda$, the model has order

$$
|\mathcal G|=|\Lambda|^d.
$$

Finite local freeness here refers to $\mathcal O(\mathcal G)$ as an $R$-module. It does not mean that the group scheme itself is a module scheme represented by an affine space; the $\Lambda$-module structure is encoded by endomorphisms of the finite group scheme.

### 12.2 Basis-independent representations

Residual representations are usually displayed as matrices, but finite flatness must survive conjugation and must treat reducible extensions without choosing a splitting. The module formulation accomplishes both goals.

Let $\mathbf k$ be a finite field of characteristic $\ell$, and let $V$ be two-dimensional over $\mathbf k$. A basis writes its action as

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(\mathbf k).
$$

Changing basis conjugates $\bar\rho$. The statement that $\bar\rho$ is finite flat means that the underlying $\mathbf k[G_K]$-module $V$ has a $\mathbf k$-linear finite-flat model. It is invariant under conjugation because an isomorphism of $G_K$-modules transports the generic identification of a model.

This formulation also handles reducible representations without choosing an upper-triangular matrix. If $L\subset V$ is a $G_K$-stable line and $V$ has a model, closing $L$ inside that model produces a finite-flat line model and a finite-flat quotient. The extension class represented by

$$
0\to L\to V\to V/L\to0
$$

is therefore integrally realizable with those induced endpoint models. Knowing only that the two characters on the diagonal are finite flat would not suffice to recover this conclusion.

Consequently finite flatness passes from $V$ to its semisimplification. Choose a composition series by stable subspaces, close it inside one model, and model every simple factor by a successive quotient. Their direct sum models $V^{\mathrm{ss}}$. The converse is not automatic: semisimplification forgets precisely the extension classes isolated in Chapter 6. Thus the local condition is stronger than a condition on the multiset of Jordan--Hölder factors.

For a reducible two-dimensional representation one may, after identifying an invariant line, choose a basis and write

$$
\bar\rho(\sigma)=
\begin{pmatrix}
\chi_1(\sigma)&c(\sigma)\\
0&\chi_2(\sigma)
\end{pmatrix}.
$$

Finite flatness of $V$ implies finite flatness of both characters and integral realizability of the class encoded by $c$. The two character conditions alone do not imply finite flatness of the matrix representation. Changing a splitting changes the cocycle representative but not its extension class, so the geometric formulation remains basis independent.

### 12.3 Changing lattices and changing coefficients

A residual representation often arises by reducing a stable lattice in an $\ell$-adic representation. Different stable lattices can have nonisomorphic reductions. That phenomenon belongs to the representation before a finite-flat model is chosen and should not be confused with nonuniqueness of finite-flat group schemes modeling one fixed reduction.

Once a residual module $V$ is fixed, restriction and extension of coefficient scalars behave as in Chapter 7. In particular, for a finite field extension $\mathbf k'/\mathbf k$,

$$
V\text{ finite flat over }\mathbf k
\quad\Longleftrightarrow\quad
\mathbf k'\otimes_{\mathbf k}V\text{ finite flat over }\mathbf k'.
$$

The forward implication is Proposition 7.3. For the reverse implication, first restrict the coefficient action on a $\mathbf k'$-linear model to $\mathbf k$. The canonical map

$$
V\longrightarrow\mathbf k'\otimes_{\mathbf k}V,
\qquad v\longmapsto1\otimes v,
$$

is an injective $\mathbf k[G_K]$-map, so closing its image inside the restricted model gives a $\mathbf k$-linear model of $V$. This proves descent of the **existential predicate**; it does not descend the chosen $\mathbf k'$-linear model itself. Recovering that particular model over $\mathbf k$ would require coefficient descent data. Quotients of coefficient rings are also covered unconditionally by Proposition 7.3, provided one uses closure of the generic relation submodule and the represented finite-flat quotient rather than a potentially nonflat raw scheme-theoretic kernel or image.

### 12.4 Determinants and pairings

In rank two, a perfect alternating pairing compresses duality into one character: the determinant. The point is not merely a matrix identity; the integral pairing supplies information even when the special fiber has too few geometric points for matrices. Throughout this section assume $\operatorname{char}K\ne\ell$, so that $\mu_\ell$ is finite étale on the generic fiber and its geometric points form a one-dimensional $\mathbf F_\ell$-module.

For a two-dimensional $\mathbf k$-representation, put

$$
\mathbf k(1)=\mathbf k\otimes_{\mathbf F_\ell}\mu_\ell(K^s),
$$

with its cyclotomic $G_K$-action. The determinant

$$
\det V=\bigwedge^2_{\mathbf k}V
$$

is basis-independent. A perfect alternating $G_K$-equivariant pairing

$$
V\times V\longrightarrow\mathbf k(1)
$$

identifies $V$ with its Tate-twisted dual and forces $\det V$ to be the mod-$\ell$ cyclotomic character. Elliptic-curve torsion carries exactly this pairing.

Choose a basis and a nonzero element of the one-dimensional target. If $J$ is the alternating matrix, equivariance gives

$$
\bar\rho(\sigma)^{\mathsf t}J\bar\rho(\sigma)
=\bar\chi_\ell(\sigma)J.
$$

For a $2\times2$ matrix $A$, one has $A^{\mathsf t}JA=(\det A)J$. Hence

$$
\det\bar\rho(\sigma)=\bar\chi_\ell(\sigma).
$$

The chosen basis and target generator disappear from the equality of characters. If the pairing comes from a perfect group-scheme pairing, it survives on connected special fibers where a pointwise matrix calculation is unavailable.

One should not deduce general finite flatness of determinants from a nonexistent automatic tensor calculus on arbitrary finite-flat group schemes. Tensor products and exterior powers of the generic coefficient modules require representability and flatness on the integral side. In geometric situations the Weil pairing supplies the needed integral morphism directly. In other settings determinant conditions should be imposed or proved by an appropriate model construction.

## 13. The local finite-flat condition

### 13.1 At a place above the coefficient characteristic

The preceding structure now condenses into the local condition used in arithmetic. Its definition must be intrinsic, compatible with coefficients, and precise about why places above the coefficient characteristic differ from all other finite places.

Let $F$ be a number field, let $v\mid\ell$, and put

$$
K=F_v,\qquad R=\mathcal O_{F_v}.
$$

Let $\mathbf k$ be a finite field of characteristic $\ell$, and let $V$ be a finite-dimensional continuous $\mathbf k$-representation of $G_F$. The phrase

$$
V\text{ is finite flat at }v
$$

means that the restricted $\mathbf k[G_K]$-module $V|_{G_K}$ admits a $\mathbf k$-linear finite-flat model over $R$.

The choice of decomposition group is harmless. Two embeddings defining the place give conjugate subgroups of $G_F$, and conjugation transports the restricted module through an isomorphism. Since finite flatness is invariant under module isomorphism, the condition depends only on $v$.

Because $K$ has characteristic zero, the generic fiber of every finite-flat $R$-group is étale. No separability clause is hidden at this point. The subtlety lies entirely in extending the generic module across $R$, especially when its order is divisible by $\ell$.

For a finite local coefficient ring $A$ of residue characteristic $\ell$ and a finite free $A$-module $V_A$ with continuous $G_K$-action, the analogous statement requires a finite-flat $R$-group with integral $A$-action whose generic points identify with $V_A$. This sentence specifies the object that later deformation theory will use; it does not define a deformation functor, claim representability, or calculate a tangent space.

At a place $v\nmid\ell$, an $\ell$-power-order representation is finite flat exactly when it is unramified, by Theorem 10.1. The phrase “finite flat at places above $\ell$” singles out the places where the condition is not already ordinary unramifiedness.

**Theorem 13.1 (local characterization).** Let $K$ be a finite extension of $\mathbf Q_\ell$, put $R=\mathcal O_K$, let $\Lambda$ be a finite commutative ring of $\ell$-power characteristic, and let $M$ be a finite continuous $\Lambda[G_K]$-module. The following are equivalent:

1. $M$ is finite flat over $R$ as a $\Lambda$-linear representation.
2. The finite étale $K$-group $\mathcal E_K(M)$ is the generic fiber of a finite locally free commutative $R$-group carrying a compatible $\Lambda$-action.
3. The underlying abelian $G_K$-module has a finite-flat model.

Under these conditions the property is independent of bases and coefficient presentations, but it need not determine a unique model.

**Proof.** The equivalence of (1) and (2) is the definition with the generic marking explicit. Forgetting scalars gives (2)$\Rightarrow$(3). Corollary 7.4 constructs a possibly different $\Lambda$-linear model from any underlying model, giving (3)$\Rightarrow$(2). Transport along module isomorphisms proves basis independence, and Chapter 10 supplies nonunique models at $\ell$-power order. $\square$

### 13.2 Invariance and closure properties

The local condition has the formal properties needed for later use.

- It is invariant under isomorphism of coefficient-linear $G_K$-modules, hence under change of basis.
- It is preserved by finite extension of the local field, through base change of the model.
- It is preserved by finite direct sums and direct summands.
- It is preserved by $G_K$-stable submodules and quotients, using schematic closure in a chosen model.
- It is preserved under Tate-twisted duality when the torsion exponent is invertible in $K$, which is automatic here for finite $\ell$-power torsion because $\operatorname{char}K=0$.
- It is preserved by restriction of coefficient scalars and by extension along every homomorphism of finite coefficient rings. In particular it is preserved by coefficient reduction to a quotient ring.
- An extension is admitted whenever it is the generic fiber of a faithfully flat exact sequence of coefficient-linear finite-flat models.

The last point is intentionally phrased with integral data. It is the exact closure property established in Chapter 6. A later deformation problem may define its allowable extension classes by requiring precisely such a model, but their cohomological description is not part of the present book.

Two consequences sharpen the list. If $M$ is finite flat, every term and graded piece of a stable filtration is finite flat. If $M_1$ and $M_2$ are finite flat, their direct sum is finite flat, but an unspecified extension of $M_2$ by $M_1$ is not known to be finite flat until an integral middle model is produced. The proved closure properties therefore stop short of an unjustified Serre-subcategory slogan.

### 13.3 What the condition does not assert

Several tempting strengthenings are absent.

Finite flat at $v$ does not mean unramified at $v$ when $v\mid\ell$; $\mu_\ell$ already gives a ramified finite-flat representation. It does not choose a canonical model. It does not imply that every generic morphism extends between arbitrary chosen models. It does not say that every extension of two finite-flat modules is finite flat. It does not descend automatically from a ramified extension of $K$. And it does not classify the possible connected, étale, or mixed special fibers.

Nor does the predicate depend on a chosen basis, a chosen matrix representative, or a chosen separable closure. Those choices only present the coefficient-linear module. The existential model and its generic identification make the condition intrinsic.

### 13.4 A practical verification protocol

When checking finite flatness at a local place, the following order keeps the hypotheses visible.

1. Identify the finite coefficient-linear $G_K$-module $M$, independently of a basis.
2. Replace $M$ by the finite étale generic group $\mathcal E_K(M)$.
3. Produce a finite locally free commutative $R$-group $\mathcal G$ with the required coefficient action.
4. Verify an isomorphism $\mathcal G_K\simeq\mathcal E_K(M)$ respecting coefficients.
5. For submodules, close them inside this fixed $\mathcal G$; for quotients, use the represented finite-flat quotient.
6. For an extension, exhibit a faithfully flat exact integral sequence; do not infer it solely from its generic endpoints.
7. For a change of local field, base-change from $R$ to the larger valuation ring freely, but demand descent data before going back.
8. For a dual, retain the $\mu_n$ target and the Tate twist.
9. For coefficient base change, close the generic relation submodule in a finite product of the chosen model and take the represented quotient; do not use a raw kernel or image without a flatness check.

This is a criterion of construction, not a classification theorem. In many arithmetic examples Step 3 is supplied by $\mathcal A[n]$ for an abelian scheme with good reduction. In others it is the genuinely difficult step.

## 14. The four-level dictionary

### 14.1 Representation, model, existence, and uniqueness

The conclusions are easiest to reuse when the four logical levels of the theory are displayed side by side. This prevents a theorem about a chosen lattice from being mistaken for a theorem about every lattice or about existence alone.

The theory is most reliable when four levels are kept separate.

$$
\begin{array}{c|l|l}
\text{level}&\text{datum}&\text{typical question}\\
\hline
\text{representation}&M\text{ with continuous }G_K\text{-action}
&\text{what is the generic arithmetic?}\\
\text{chosen model}&(\mathcal G,\iota)
&\text{how do points specialize integrally?}\\
\text{existence}&\operatorname{FF}_R(M)
&\text{does at least one model exist?}\\
\text{uniqueness}&\mathrm{Mod}_R(M)\text{ has one class}
&\text{is the integral behavior forced?}
\end{array}
$$

A representation determines its finite étale generic group. A chosen model adds a finite projective Hopf lattice and a special fiber. The predicate forgets which model witnessed existence. Uniqueness is an additional theorem, true in the prime-to-$p$ étale range and false in general at $p$-power order.

Ambient closure inserts a useful intermediate statement. Given $M'\subset M$ and a chosen $\mathcal G$ modeling $M$, the model of $M'$ **inside $\mathcal G$** is unique. This does not collapse the last two rows of the table.

### 14.2 A reusable criterion

The conclusions of the book can be compressed into one criterion with explicit branches.

**Finite-flat criterion and dictionary.** Let $R$ be a complete DVR with fraction field $K$, residue characteristic $p>0$, and let $M$ be a finite continuous $G_K$-module, possibly with an action of a finite coefficient ring $\Lambda$.

1. Form the finite étale group $\mathcal E_K(M)$. Then $M$ is finite flat precisely when there exists a finite locally free commutative $R$-group $\mathcal G$, with compatible $\Lambda$-action when required, and an identification

   $$
   \mathcal G_K\simeq\mathcal E_K(M).
   $$

2. If $p\nmid|M|$, existence is equivalent to unramifiedness, and the model is uniquely finite étale.

3. If $p\mid|M|$, existence neither implies unramifiedness nor uniqueness. Constant and multiplicative models, and the equal-characteristic lattice pair, witness the failure.

4. After a model is chosen, every $G_K$-stable submodule has a unique finite-flat closure inside it, and the represented quotient models the module quotient.

5. A faithfully flat exact integral sequence gives an exact generic representation sequence. Conversely, a model of the generic middle term gives an integral exact sequence by closure. Separate models of the two endpoints do not by themselves model every generic extension class.

6. Generic base change to a finite extension $L/K$ preserves finite flatness. Descent requires compatible integral faithfully flat descent data; potential finite flatness is weaker.

7. Coefficient restriction and extension along any homomorphism of finite coefficient rings preserve finite flatness. For a quotient of coefficient rings, the safe construction closes the generic relation submodule and then takes its represented finite-flat quotient.

8. If $nM=0$ and $n\in K^\times$, Cartier duality carries a chosen model of $M$ to a chosen model of

   $$
   M^*(1)=\operatorname{Hom}(M,\mu_n(K^s)).
   $$

9. The generic-fiber functor is faithful and exact on admissible sequences, but it is not full and not essentially injective in general.

Every clause identifies both the conclusion and the data needed to obtain it. This is what makes the dictionary reusable: it tells us not only what is true, but where a choice, a flatness theorem, or a descent hypothesis enters.

### 14.3 Final synthesis

A finite Galois representation over a local field is the visible generic layer of a more delicate integral object. In the finite étale range, geometric points and descent recover the generic group exactly. Passing across the valuation ring asks for a finite projective Hopf lattice whose generic fiber is that group. At residue-characteristic torsion, the lattice permits points to merge without losing rank, and the special fiber records whether their limiting symmetry is étale, connected, multiplicative, or mixed.

The resulting notion of finite flatness is therefore existential but not vague. A chosen model has a rigid exact calculus: generic submodules close uniquely inside it, finite-flat quotients represent module quotients, faithfully flat exact sequences preserve the generic extension, and Cartier duality produces the Tate-twisted dual model. What fails is equally structural. Arbitrary kernels may acquire vertical torsion, arbitrary generic maps may not preserve integral lattices, models need not be unique, and an upstairs model does not descend without integral cocycle data.

Prime-to-$p$ torsion lies at the rigid edge of the theory: finite flat means unramified and the model is uniquely étale. Residue-characteristic torsion lies at its arithmetic center: $\mu_{p^r}$, ordinary and supersingular torsion, and closures inside abelian schemes show how ramification and connected specialization coexist with an étale generic representation. Good reduction supplies the fundamental geometric models, while invariant subgroup closures transport them to isogeny kernels and residual subquotients.

For a two-dimensional residual representation at a place $v\mid\ell$, “finite flat at $v$” now has an exact meaning independent of matrices: its restricted coefficient module is the generic fiber of some coefficient-linear finite-flat group over the local valuation ring. This condition is stable under the admissible operations required later, yet it carries no premature assertion about deformation functors, representability, or cohomological tangent spaces. Those later theories can therefore begin from a clean boundary: the representation is generic data, the model is chosen integral data, finite flatness is existence, and uniqueness is a separate rigidity theorem.
