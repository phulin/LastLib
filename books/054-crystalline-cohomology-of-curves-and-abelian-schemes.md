# Crystalline Cohomology of Curves and Abelian Schemes

## Contents

1. [From infinitesimal transport to cohomology](#1-from-infinitesimal-transport-to-cohomology)
   - [The arithmetic problem](#11-the-arithmetic-problem)
   - [Standing hypotheses and conventions](#12-standing-hypotheses-and-conventions)
   - [The theorem package to be proved](#13-the-theorem-package-to-be-proved)
2. [Derived crystalline direct images](#2-derived-crystalline-direct-images)
   - [The morphism of crystalline topoi](#21-the-morphism-of-crystalline-topoi)
   - [Functoriality, cup products, and projection formulas](#22-functoriality-cup-products-and-projection-formulas)
   - [Finite levels and completion](#23-finite-levels-and-completion)
3. [The crystalline Poincaré lemma](#3-the-crystalline-poincaré-lemma)
   - [Linearization of a module with connection](#31-linearization-of-a-module-with-connection)
   - [The local contracting homotopy](#32-the-local-contracting-homotopy)
   - [Comparison with a smooth lift](#33-comparison-with-a-smooth-lift)
   - [Independence of the lift](#34-independence-of-the-lift)
4. [Embedding systems and cohomological descent](#4-embedding-systems-and-cohomological-descent)
   - [Why one embedding does not suffice](#41-why-one-embedding-does-not-suffice)
   - [The simplicial de Rham model](#42-the-simplicial-de-rham-model)
   - [Descent and boundedness](#43-descent-and-boundedness)
5. [Finiteness and perfectness](#5-finiteness-and-perfectness)
   - [Perfect complexes at finite level](#51-perfect-complexes-at-finite-level)
   - [Derived base change](#52-derived-base-change)
   - [When cohomology modules commute with base change](#53-when-cohomology-modules-commute-with-base-change)
6. [Smooth proper curves](#6-smooth-proper-curves)
   - [The three cohomological degrees](#61-the-three-cohomological-degrees)
   - [The crystalline Hodge sequence](#62-the-crystalline-hodge-sequence)
   - [Finiteness and arbitrary PD base change](#63-finiteness-and-arbitrary-pd-base-change)
   - [Genus zero, genus one, and a warning](#64-genus-zero-genus-one-and-a-warning)
7. [Trace and Poincaré duality](#7-trace-and-poincaré-duality)
   - [Construction of the trace](#71-construction-of-the-trace)
   - [Perfect duality](#72-perfect-duality)
   - [Curves and the alternating degree-one form](#73-curves-and-the-alternating-degree-one-form)
   - [Adjointness for finite maps](#74-adjointness-for-finite-maps)
8. [The Künneth theorem](#8-the-künneth-theorem)
   - [The derived exterior product](#81-the-derived-exterior-product)
   - [Proof by local de Rham comparison](#82-proof-by-local-de-rham-comparison)
   - [The cohomological decomposition](#83-the-cohomological-decomposition)
9. [Frobenius](#9-frobenius)
   - [Semilinearity and twists](#91-semilinearity-and-twists)
   - [Construction without a global Frobenius lift](#92-construction-without-a-global-frobenius-lift)
   - [The Frobenius isogeny theorem](#93-the-frobenius-isogeny-theorem)
   - [Duality and Frobenius](#94-duality-and-frobenius)
10. [Completed crystalline cohomology](#10-completed-crystalline-cohomology)
    - [Passage through finite levels](#101-passage-through-finite-levels)
    - [Torsion-freeness and reduction](#102-torsion-freeness-and-reduction)
    - [The integral and rational objects](#103-the-integral-and-rational-objects)
11. [Abelian schemes: degree one](#11-abelian-schemes-degree-one)
    - [The first crystalline crystal](#111-the-first-crystalline-crystal)
    - [The crystalline Hodge extension](#112-the-crystalline-hodge-extension)
    - [Primitivity under the group law](#113-primitivity-under-the-group-law)
    - [Homomorphisms and isogenies](#114-homomorphisms-and-isogenies)
12. [The exterior algebra theorem](#12-the-exterior-algebra-theorem)
    - [The cup-product map](#121-the-cup-product-map)
    - [Proof of the exterior algebra theorem](#122-proof-of-the-exterior-algebra-theorem)
    - [Multiplication and ranks](#123-multiplication-and-ranks)
13. [Dual abelian schemes and polarizations](#13-dual-abelian-schemes-and-polarizations)
    - [The crystalline Poincaré class](#131-the-crystalline-poincaré-class)
    - [Perfect duality in degree one](#132-perfect-duality-in-degree-one)
    - [Polarization forms](#133-polarization-forms)
    - [Compatibility with Frobenius and isogenies](#134-compatibility-with-frobenius-and-isogenies)
14. [Curves, Jacobians, and correspondences](#14-curves-jacobians-and-correspondences)
    - [The Abel--Jacobi map in degree one](#141-the-abel--jacobi-map-in-degree-one)
    - [The Jacobian comparison](#142-the-jacobian-comparison)
    - [Correspondences and adjoints](#143-correspondences-and-adjoints)
15. [The structures used in finite-flat and PEL geometry](#15-the-structures-used-in-finite-flat-and-pel-geometry)
    - [Endomorphism actions and idempotent factors](#151-endomorphism-actions-and-idempotent-factors)
    - [Polarized linear algebra](#152-polarized-linear-algebra)
    - [Integral cautions at the residue prime](#153-integral-cautions-at-the-residue-prime)
16. [Synthesis](#16-synthesis)
    - [The complete crystalline package](#161-the-complete-crystalline-package)
    - [Hypothesis ledger](#162-hypothesis-ledger)
    - [Conclusion](#163-conclusion)

## 1. From infinitesimal transport to cohomology

Divided powers turn nilpotent thickenings into integral Taylor neighborhoods, and a crystal transports a module rigidly across those neighborhoods. That local language is only the beginning. Arithmetic geometry needs global objects which are finite, survive change of coefficients, carry products and traces, and remember Frobenius. The purpose of this book is to prove that package for smooth proper curves and abelian schemes.

### 1.1 The arithmetic problem

Let $k$ be a field of characteristic $p>0$ and let $X/k$ be smooth and proper. Ordinary algebraic de Rham cohomology $H^*_{\mathrm{dR}}(X/k)$ is finite, but the differential of absolute Frobenius is zero. It therefore cannot by itself retain an invertible linear shadow of Frobenius. Crystalline cohomology remedies this by evaluating $X$ on divided-power thickenings of $k$. Over the Witt ring $W(k)$ it produces an integral module

$$
H^i_{\mathrm{cris}}(X/W(k))
$$

with a semilinear Frobenius which becomes invertible after $p$ is inverted.

The word "integral" creates the main difficulty. Rationally, finite-dimensional linear algebra hides torsion. Integrally, ordinary tensor products may fail to compute coefficient change, inverse limits can have derived error terms, and a perfect pairing over the fraction field need not come from a perfect lattice. We shall therefore construct the derived object first. Ordinary cohomology and its base-change formulas will be consequences of perfectness and flatness, never substitutes for them.

For curves and abelian schemes the outcome is especially rigid. A genus-$g$ curve has crystalline ranks $1,2g,1$ and a perfect alternating form on degree one. An abelian scheme of relative dimension $g$ has

$$
H^n_{\mathrm{cris}}\simeq\bigwedge^n H^1_{\mathrm{cris}},
$$

and a principal polarization turns $H^1_{\mathrm{cris}}$ into a symplectic Frobenius module. These are the structures later moduli arguments actually use.

### 1.2 Standing hypotheses and conventions

A **nilpotent PD base** is a scheme $S$ with a quasi-coherent nilpotent ideal $J\subset\mathcal O_S$ and divided powers $\gamma$, with special fiber $S_0=V(J)$. We assume all schemes locally noetherian and all morphisms of finite presentation whenever finiteness is discussed. A **PD morphism** preserves the stated divided powers. The small crystalline site and its structure sheaf have the meaning established in Book 53.

For a morphism $f:X\to S_0$, write

$$
Rf_{\mathrm{cris},*}\mathcal E
$$

for its derived crystalline direct image with coefficients in a crystal $\mathcal E$. If $S=\operatorname{Spec}A$, its derived global sections are denoted

$$
R\Gamma_{\mathrm{cris}}(X/S,\mathcal E),
\qquad
H^i_{\mathrm{cris}}(X/S,\mathcal E)=H^iR\Gamma_{\mathrm{cris}}(X/S,\mathcal E).
$$

Coefficients are the structure crystal unless displayed. Complexes are cohomological. Tensor symbols in derived statements mean $\otimes^L$. A **perfect complex** is locally quasi-isomorphic to a bounded complex of finite locally free modules. This convention is vital: the cohomology modules of a perfect complex need not themselves be flat.

At finite Witt level we write $W_n(k)=W(k)/p^n$. If $k$ is perfect, $\sigma$ denotes Witt Frobenius. The notation $M(-r)$ means the same module with Frobenius multiplied by $p^r$; thus the rank-one object $W(k)(-r)$ has Frobenius $p^r\sigma$. This is a convention, not tensoring by an unconstructed line.

A **smooth proper curve** has geometrically connected fibers of pure dimension one. An abelian scheme has the definition of Book 38. For relative results about a smooth proper morphism $X\to B_0$ over a PD base $B$, the phrase "its crystalline cohomology crystal" refers to the assignment on a base thickening $(U,T)$

$$
(U,T)\longmapsto H^i_{\mathrm{cris}}(X_U/T).
$$

Proving that this assignment is finite locally free and crystalline is part of the work below.

### 1.3 The theorem package to be proved

The central results have four layers.

First, for smooth proper $X/S_0$, crystalline cohomology is represented by a bounded perfect complex and satisfies derived PD base change. Second, for curves and abelian schemes its individual cohomology modules are finite locally free, so derived base change descends to ordinary base change. Third, cup product, trace, duality, and Künneth are compatible and perfect. Fourth, in characteristic $p$, Frobenius is semilinear integrally and is an isomorphism after $p$ is inverted.

The order matters. For example, reduction modulo $p^n$ fits into

$$
0\to H^i/p^nH^i\to
H^i(K\otimes^LW_n)\to H^{i+1}[p^n]\to0. \tag{1.1}
$$

Consequently a finite-level equality cannot be obtained from an integral group until the next integral group is known to have no $p^n$-torsion. The curve and abelian-scheme theorems will provide exactly this missing flatness.

## 2. Derived crystalline direct images

The crystalline site is attached to a single scheme, but families demand a relative construction. The right object is a morphism of ringed topoi. Once it is in place, pullback, cup product, and coefficient change are consequences of general derived functoriality rather than separate ad hoc maps.

### 2.1 The morphism of crystalline topoi

Let $f:X\to Y$ be a morphism of schemes over $S_0$. On big crystalline sites, composition sends an $X$-scheme with a PD thickening to a $Y$-scheme with the same thickening. This defines a morphism of topoi

$$
f_{\mathrm{cris}}:(X/S)_{\mathrm{cris}}\longrightarrow(Y/S)_{\mathrm{cris}}.
$$

The small-site construction is obtained by passing through the big sites and restricting to opens. This detour is necessary because the image of an open of $X$ need not be open in $Y$.

**Proposition 2.1.** The assignments $X\mapsto(X/S)_{\mathrm{cris}}$ and $f\mapsto f_{\mathrm{cris}}$ are functorial up to the canonical coherence isomorphisms, and $Rf_{\mathrm{cris},*}$ carries bounded-below complexes to bounded-below complexes.

**Proof.** Composition on the big site is literal composition of the structural maps of thickenings. Associativity and identity diagrams give the coherence isomorphisms. The inverse-image functor of a geometric morphism is left exact, and the direct-image functor is left exact; resolving by injective sheaves therefore defines $Rf_{\mathrm{cris},*}$ on bounded-below complexes. Restriction from the big site respects composition, so the same statement holds on the small site. $\square$

For a structure morphism $a:X\to S_0$, the target crystalline topos is the crystalline topos of $S_0/S$. Its structure crystal evaluates on a base thickening $T$ as $\mathcal O_T$. Thus $Ra_{\mathrm{cris},*}\mathcal O_{X/S}$ is the relative cohomology object from which every evaluation $R\Gamma_{\mathrm{cris}}(X_T/T)$ will be recovered.

### 2.2 Functoriality, cup products, and projection formulas

A map $u:X'\to X$ gives contravariant pullback

$$
u^*:R\Gamma_{\mathrm{cris}}(X/S,\mathcal E)
\longrightarrow
R\Gamma_{\mathrm{cris}}(X'/S,u_{\mathrm{cris}}^*\mathcal E).
$$

The multiplication of the structure sheaf and the tensor product of crystals give a cup product

$$
Rf_*\mathcal E\otimes^LRf_*\mathcal F
\longrightarrow
Rf_*(\mathcal E\otimes^L\mathcal F). \tag{2.1}
$$

On cohomology it is graded commutative. The sign is $(-1)^{ij}$ for classes of degrees $i$ and $j$, because both the resolution degree and the de Rham degree contribute to total degree.

**Proposition 2.2 (projection formula).** If $P$ is a perfect complex on the base crystalline topos, then the natural map

$$
P\otimes^LRf_*K\longrightarrow
Rf_*(f^*P\otimes^LK) \tag{2.2}
$$

is an isomorphism whenever $f$ is quasi-compact and quasi-separated in the crystalline sense and $K$ has quasi-coherent evaluations.

**Proof.** The assertion is local on the base. Resolve $K$ by modules acyclic for $f_*$ and represent $P$ by a bounded complex of finite free modules. For one finite free module, (2.2) is the compatibility of direct image with finite direct sums. Passing through the bounded complex proves the claim by totalization. Finite locally free summands follow from finite free ones by splitting idempotents. $\square$

The perfectness requirement cannot be weakened to arbitrary coherence: tensoring an injective resolution by a nonflat module can create higher Tor and destroy acyclicity.

### 2.3 Finite levels and completion

Let $S_n=\operatorname{Spec}W_n(k)$. Reduction $S_{n+1}\to S_n$ is a PD morphism, so there is a derived comparison

$$
R\Gamma_{\mathrm{cris}}(X/S_{n+1})\otimes^L_{W_{n+1}}W_n
\longrightarrow R\Gamma_{\mathrm{cris}}(X/S_n). \tag{2.3}
$$

We shall prove in Chapter 5 that (2.3) is an isomorphism for smooth proper $X$. Until then it is only a natural map.

Define completed crystalline cohomology by the derived inverse limit

$$
R\Gamma_{\mathrm{cris}}(X/W(k))
=R\varprojlim_nR\Gamma_{\mathrm{cris}}(X/W_n(k)). \tag{2.4}
$$

This definition records the possible $R^1\varprojlim$ term. Once the finite-level complexes are represented compatibly by bounded finite free complexes, their transition maps can be chosen degreewise surjective. Then derived and ordinary inverse limits agree degree by degree. Chapter 10 will make this consequence explicit.

## 3. The crystalline Poincaré lemma

The crystalline site looks much larger than a de Rham complex. Smoothness collapses it. A smooth lift supplies local coordinates, divided-power envelopes supply integral Taylor expansion, and a contracting homotopy removes the added infinitesimal variables. This is the decisive local calculation behind every global theorem.

### 3.1 Linearization of a module with connection

Let $S=\operatorname{Spec}A$ be a nilpotent PD base, let $X/S_0$ be smooth affine, and choose a smooth lift $Y=\operatorname{Spec}R$ over $S$. A finite locally free crystal $\mathcal E$ evaluates on $Y$ as a finite projective $R$-module $M$ with integrable quasi-nilpotent connection

$$
\nabla:M\longrightarrow M\otimes_R\Omega^1_{R/A}.
$$

For an $R$-module $N$, its **crystalline linearization** $L(N)$ is the crystal obtained by pulling $N$ to each PD thickening through a local lift to $Y$ and using the diagonal PD envelope to compare two lifts. When $N=M\otimes\Omega^q_{R/A}$, the stratification of $M$ and the natural stratification of differentials make this construction canonical.

There is an augmented complex of crystals

$$
0\longrightarrow\mathcal E\longrightarrow L(M)
\xrightarrow{\nabla}L(M\otimes\Omega^1)
\xrightarrow{\nabla}\cdots. \tag{3.1}
$$

Integrability gives $\nabla^2=0$. The augmentation sends a transported section of the crystal to its value under the chosen lift.

### 3.2 The local contracting homotopy

**Theorem 3.1 (crystalline Poincaré lemma).** The augmented complex (3.1) is a quasi-isomorphism. If $Y/S$ has relative dimension $d$, it ends in degree $d$.

**Proof strategy.** Exactness may be checked on a crystalline object $(U,T)$ and locally on $T$. Smoothness lifts $T\to Y$ locally. After choosing étale coordinates, every competing lift differs by divided-power variables $\xi_1,\ldots,\xi_d$. The complex then separates into one-variable complexes, each of which has an integral contraction.

Choose coordinates $x_i$ and write the diagonal envelope as

$$
R\langle\xi_1,\ldots,\xi_d\rangle,
\qquad \xi_i=p_1(x_i)-p_2(x_i).
$$

Filter by the number of variables. In one variable the normalized complex has basis $\xi^{[n]}$ in degree zero and $\xi^{[n]}d\xi$ in degree one, with

$$
d(\xi^{[n+1]})=\xi^{[n]}d\xi. \tag{3.2}
$$

Define $h(\xi^{[n]}d\xi)=\xi^{[n+1]}$ and let $h$ vanish in degree zero. Then $dh+hd$ is the identity on every positive divided-power degree and zero on constants. No factorial is divided. Tensoring these contractions, with the usual Koszul signs, contracts the multivariable complex onto its constant term.

For coefficients, use the Taylor stratification to conjugate the differential to the tensor product differential. Quasi-nilpotence makes the conjugating Taylor sum finite on every nilpotent object. The constant survivors are precisely $\mathcal E$. Descent glues the local contractions up to homotopy, which suffices for a quasi-isomorphism. Since $\Omega^q_{R/A}=0$ for $q>d$, the complex has the asserted length. $\square$

The identity (3.2) is the arithmetic heart of the proof. An ordinary polynomial contraction would divide by $n+1$; divided powers have already absorbed that denominator.

### 3.3 Comparison with a smooth lift

Applying crystalline global sections to (3.1), the linearized terms are acyclic in the crystalline direction: their cohomology is ordinary Zariski cohomology on $Y$. Therefore:

**Theorem 3.2 (lift comparison).** Let $X/S_0$ be smooth and let $Y/S$ be a smooth lift. For a finite locally free crystal corresponding to $(M,\nabla)$ on $Y$, there is a functorial multiplicative quasi-isomorphism

$$
R\Gamma_{\mathrm{cris}}(X/S,\mathcal E)
\simeq
R\Gamma\bigl(Y,M\otimes\Omega^\bullet_{Y/S}\bigr). \tag{3.3}
$$

For the structure crystal this becomes

$$
R\Gamma_{\mathrm{cris}}(X/S)
\simeq R\Gamma(Y,\Omega^\bullet_{Y/S}). \tag{3.4}
$$

**Proof.** Resolve $\mathcal E$ by (3.1). On an object $(U,T)$, a linearized module is induced from a quasi-coherent module on $Y$, so its higher crystalline direct images vanish locally: the choices of a lift form the contractible PD groupoid used in Theorem 3.1, and Zariski descent is the only remaining cohomology. Thus the hypercohomology of (3.1) is the hypercohomology of the displayed de Rham complex. The construction respects wedge products and tensor connections, giving multiplicativity. $\square$

If $Y$ is affine, (3.3) is computed by the complex of global modules. If $Y$ is not affine, one must retain hypercohomology; global differential forms alone do not see coherent gluing classes.

### 3.4 Independence of the lift

Two smooth lifts $Y$ and $Y'$ need not be isomorphic. Their de Rham complexes nevertheless compute the same object.

**Proposition 3.3.** The comparison (3.3) is independent of the chosen smooth lift in the following precise sense: the PD envelope of $X$ in $Y\times_SY'$ induces a canonical zigzag of multiplicative quasi-isomorphisms between the two de Rham models, and three lifts satisfy the cocycle condition in the derived category.

**Proof.** The two projections from $Y\times_SY'$ give two maps from its PD envelope. Pulling a crystal to that envelope identifies both evaluations by crystallinity. Applying the Poincaré lemma to each projection gives the two quasi-isomorphisms. For three lifts, the comparisons are pulled back from the three pairwise projections of the envelope in $Y\times Y'\times Y''$. The cocycle is exactly transitivity of the crystal transition maps. $\square$

This is why the local lift model is a calculation, not extra structure on crystalline cohomology.

## 4. Embedding systems and cohomological descent

A smooth $X/S_0$ has local smooth lifts, but a global lift can fail to exist. Properness does not remove that obstruction. To globalize the Poincaré lemma, we replace one lift by a simplicial family of lifts and totalize its de Rham complexes.

### 4.1 Why one embedding does not suffice

Choose a finite affine open cover $X=\bigcup U_i$ when $X$ is quasi-compact. Each $U_i$ admits a closed immersion into a smooth affine $S$-scheme $Y_i$: lift a finite presentation and localize at a lifted Jacobian minor. On an intersection $U_{i_0\cdots i_r}$ use the product

$$
Y_{i_0}\times_S\cdots\times_SY_{i_r}
$$

and take the PD envelope of the intersection inside it. Face maps omit a factor and degeneracy maps repeat one. The universal property of PD envelopes makes the simplicial identities hold.

This construction is an **embedding system** $U_\bullet\hookrightarrow Y_\bullet$. At each finite nilpotent level its PD envelopes $D_\bullet$ are objects of the crystalline site. The cover is finite, so only finitely many Čech degrees contribute after normalization.

### 4.2 The simplicial de Rham model

Let $D_r$ be the appropriate PD envelope and let $\widehat D_r$ denote it only when a specified completion is being used. The structure crystal evaluates as $\mathcal O_{D_r}$. Attach the de Rham complex of the smooth ambient scheme, restricted to $D_r$:

$$
\mathcal O_{D_r}\to
\mathcal O_{D_r}\otimes\Omega^1_{Y_r/S}\to\cdots. \tag{4.1}
$$

The face maps give a cosimplicial complex. Its total differential is

$$
d_{\mathrm{tot}}=d_{\mathrm{dR}}+(-1)^q d_{\mathrm{Cech}}
$$

on de Rham degree $q$. This sign makes $d_{\mathrm{tot}}^2=0$.

**Theorem 4.1 (embedding-system comparison).** For smooth quasi-compact separated $X/S_0$, the natural augmentation is a multiplicative quasi-isomorphism

$$
R\Gamma_{\mathrm{cris}}(X/S)
\simeq
\operatorname{Tot}R\Gamma(D_\bullet,
\mathcal O_{D_\bullet}\otimes\Omega^\bullet_{Y_\bullet/S}). \tag{4.2}
$$

**Proof strategy and proof.** Resolve the structure crystal on every simplicial level by the linearized de Rham resolution of Theorem 3.1. The rows are crystalline-acyclic after passage to the chosen affine cover, while the augmented Čech columns are exact because crystals are sheaves for Zariski coverings. The resulting double augmentation gives two spectral sequences. Taking crystalline cohomology first collapses by the Poincaré lemma; taking Čech cohomology first collapses by descent. Both abut to the total complex, proving (4.2). Multiplication is levelwise wedge product combined with the Alexander--Whitney map, and the comparison respects it. $\square$

### 4.3 Descent and boundedness

If $X/S_0$ has relative dimension $d$, the intrinsic cohomology vanishes above degree $2d$ when $X$ is proper and smooth. The embedding complex itself can appear longer because the ambient schemes and Čech direction add degrees, so this vanishing needs proof.

**Proposition 4.2.** For smooth proper $X/S_0$ of relative dimension $d$, $H^i_{\mathrm{cris}}(X/S)=0$ for $i<0$ and $i>2d$.

**Proof.** The negative vanishing is immediate from a first-quadrant model. For the upper bound, the assertion is local on $S$ and stable under nilpotent base change. On a local smooth lift it follows from the Hodge-to-de Rham spectral sequence

$$
E_1^{a,b}=H^b(Y,\Omega^a_{Y/S})\Longrightarrow
H^{a+b}_{\mathrm{dR}}(Y/S),
$$

because $0\le a\le d$ and coherent cohomology of a proper relative $d$-fold vanishes for $b>d$. For a general embedding system, the comparisons on overlaps identify this local bound, and cohomological descent preserves it. $\square$

The argument uses properness in the coherent-cohomology bound. Nonproper crystalline cohomology can have a different finiteness theory.

## 5. Finiteness and perfectness

The embedding-system model is explicit but not yet finite. Its terms may contain large PD envelopes, and a Čech resolution depends on choices. Properness and smoothness together compress it to a perfect complex on the base. This is the point at which crystalline cohomology becomes usable in families.

### 5.1 Perfect complexes at finite level

**Theorem 5.1 (crystalline finiteness).** Let $(S,J,\gamma)$ be a locally noetherian nilpotent PD base and let $f:X\to S_0$ be smooth and proper of relative dimension $d$. Then

$$
Rf_{\mathrm{cris},*}\mathcal O_{X/S}
$$

is a perfect complex of amplitude contained locally in $[0,2d]$. With coefficients in a finite locally free crystal $\mathcal E$, the same conclusion holds.

**Proof strategy.** Perfectness is local on $S$. We use the embedding-system comparison, truncate in a range which already contains all cohomology, and replace proper coherent direct images by bounded finite projective resolutions. The subtle point is to prove that truncating the PD direction loses no cohomology.

Take a finite affine cover and its embedding system. Filter (4.2) by divided-power order in the envelope ideal. The graded pieces are finite sums of modules of the form

$$
\operatorname{Sym}^{[m]}(N)\otimes\Omega^a,
$$

where $N$ is the conormal bundle of a smooth local presentation. In any fixed total cohomological range, the contraction of Theorem 3.1 shows that all sufficiently high divided-power orders occur in contractible pairs. Thus the quotient by a sufficiently high order has the same cohomology through degree $2d$, and Proposition 4.2 says that no other degree matters.

At a fixed order every term is coherent and supported on the proper scheme $X$; its derived direct image is pseudo-coherent and bounded. Smoothness gives finite Tor dimension: locally the terms have finite resolutions by vector bundles, and the relative cotangent bundles are finite locally free. A bounded pseudo-coherent complex of finite Tor dimension is perfect. The same argument applies to $\mathcal E$, since its evaluations are finite locally free. The amplitude bound is Proposition 4.2. $\square$

The theorem claims perfectness of the total complex, not local freeness of each $H^i$. A two-term complex $[A\xrightarrow{p}A]$ is perfect over $A=\mathbf Z_p$ but has torsion cohomology. Additional geometry will rule this out for curves and abelian schemes.

### 5.2 Derived base change

Let $g:(S',J',\gamma')\to(S,J,\gamma)$ be a morphism of nilpotent PD bases, put $X'=X\times_{S_0}S'_0$, and let $Lg_{mathrm{cris}}^*$ denote derived scalar extension on the base crystalline topoi.

**Theorem 5.2 (proper smooth derived base change).** There is a canonical isomorphism

$$
Lg_{\mathrm{cris}}^*Rf_{\mathrm{cris},*}\mathcal E
\xrightarrow{\sim}
Rf'_{\mathrm{cris},*}Lg_{mathrm{cris}}^*\mathcal E. \tag{5.1}
$$

On an affine base this reads

$$
R\Gamma_{\mathrm{cris}}(X/S,\mathcal E)
\otimes_A^LA'
\xrightarrow{\sim}
R\Gamma_{\mathrm{cris}}(X'/S',\mathcal E'). \tag{5.2}
$$

**Proof strategy and proof.** Choose an embedding system and base-change it. The PD envelope after nonflat base change must be interpreted as the PD pushout, not blindly as an ordinary tensor product. The universal property gives the base-changed simplicial envelope. Apply the comparison (4.2) on both bases.

Replace the left-hand complex by a bounded finite locally free representative furnished by Theorem 5.1. Derived tensoring is then termwise tensoring. At each finite divided-power order, proper coherent derived base change identifies the base change of the simplicial de Rham term with its counterpart over $S'$. These identifications respect face maps and differentials. Passing through the finite totalization gives (5.2). Independence of the embedding system makes the isomorphism canonical, and sheafification gives (5.1). $\square$

No flatness is needed in this derived statement. Flatness becomes relevant only when removing the letter $L$ or taking cohomology before tensoring.

### 5.3 When cohomology modules commute with base change

For a perfect complex $K$ over a ring $A$ and an $A$-algebra $A'$, the base-change spectral sequence is

$$
\operatorname{Tor}^{A}_{-a}(H^b(K),A')
\Longrightarrow H^{a+b}(K\otimes_A^LA'). \tag{5.3}
$$

It yields the following criterion.

**Proposition 5.3.** If every $H^i(K)$ is finite locally free, then

$$
H^i(K)\otimes_AA'\xrightarrow{\sim}H^i(K\otimes_A^LA') \tag{5.4}
$$

for every $A'$. Conversely, if (5.4) holds for every residue field and the dimensions are locally constant, then each $H^i(K)$ is finite locally free.

**Proof.** Finite local freeness kills all higher Tor in (5.3), which proves the first assertion. For the converse, a perfect complex may locally be represented by finite free modules. The universal coefficient exact sequence shows that constancy of fiber dimensions and base change force the ranks of consecutive differentials to be locally constant. Matrices of locally constant rank can locally be reduced by invertible row and column operations to a block containing an identity and a zero block. Kernels and cokernels are then finite locally free, so the cohomology is finite locally free. $\square$

This criterion turns geometric rank calculations into arbitrary coefficient change. Chapters 6 and 12 will supply those calculations.

## 6. Smooth proper curves

For a curve only degrees $0,1,2$ can occur. The edge groups are controlled by connectedness and trace; the middle group is trapped between two rank-$g$ Hodge pieces. This small range lets one prove integral local freeness without a general degeneration theorem in higher dimension.

### 6.1 The three cohomological degrees

Let $f:C\to S_0$ be a smooth proper curve of genus $g$ over a nilpotent PD base $S$. Locally choose a smooth proper lift $\widetilde C/S$. Such a lift exists after passing to an étale cover of $S$: deformations of a smooth curve across a square-zero ideal are obstructed in

$$
H^2(C,T_{C/S_0})\otimes J,
$$

which vanishes because coherent cohomology on a curve has no degree two. Induction through a nilpotence filtration gives a lift across $J$; properness and smoothness algebraize the successive formal lifts at finite nilpotent level.

The comparison theorem gives

$$
R\Gamma_{\mathrm{cris}}(C/S)
\simeq R\Gamma(\widetilde C,
[\mathcal O_{\widetilde C}\xrightarrow d\Omega^1_{\widetilde C/S}]). \tag{6.1}
$$

Book 52 proved that the Hodge-to-de Rham spectral sequence of a smooth proper curve degenerates in every characteristic. Its proof uses constants, residues, and relative duality, so it remains valid over the nilpotent base $S$. Hence

$$
H^0_{\mathrm{cris}}(C/S)\simeq\mathcal O_S,
\qquad H^2_{\mathrm{cris}}(C/S)\simeq\mathcal O_S, \tag{6.2}
$$

and $H^i=0$ outside $0,1,2$.

The first isomorphism sends $1$ to $1$. The second becomes canonical only after choosing the trace normalization of Chapter 7; before that it is the identification with $R^1f_*\omega$ supplied by the de Rham spectral sequence.

### 6.2 The crystalline Hodge sequence

**Theorem 6.1 (curve Hodge sequence).** On every base thickening on which $C$ has a smooth proper lift $\widetilde C$, there is a canonical exact sequence

$$
0\longrightarrow f_*\Omega^1_{\widetilde C/S}
\longrightarrow H^1_{\mathrm{cris}}(C/S)
\longrightarrow R^1f_*\mathcal O_{\widetilde C}
\longrightarrow0. \tag{6.3}
$$

Its outer terms are dual finite locally free modules of rank $g$, and the sequence is compatible with change of the thickening.

**Proof.** Under (6.1), filter the two-term de Rham complex by form degree. The only possible differentials are the two considered in Book 52. The differential on $f_*\mathcal O$ is zero because proper geometrically connected fibers have only base functions. The differential

$$
R^1f_*\mathcal O\to R^1f_*\Omega^1
$$

is zero because its composite with the residue trace is zero on exact differentials, while the trace is an isomorphism. Thus the spectral sequence degenerates and yields (6.3). Relative duality identifies the outer terms and proves their rank. Naturality of the filtered de Rham comparison proves compatibility with PD base change and with comparisons between lifts. $\square$

The sequence need not split canonically. A splitting would choose a complement to the Hodge bundle, and in a varying family no such complement is generally horizontal.

### 6.3 Finiteness and arbitrary PD base change

**Theorem 6.2.** For a smooth proper curve, every $H^i_{\mathrm{cris}}(C/S)$ is finite locally free, of ranks

$$
1,\quad 2g,\quad 1
$$

in degrees $0,1,2$, and zero otherwise. For every PD base change $S'\to S$,

$$
H^i_{\mathrm{cris}}(C/S)\otimes_{\mathcal O_S}\mathcal O_{S'}
\xrightarrow{\sim}H^i_{\mathrm{cris}}(C_{S'_0}/S'). \tag{6.4}
$$

**Proof.** The outer terms of (6.3) are finite locally free. Locally the quotient is projective, so the short exact sequence splits as modules; hence the middle term is finite locally free of rank $2g$. Equation (6.2) handles degrees zero and two. Apply Theorem 5.2 and Proposition 5.3 to obtain (6.4), including nonflat base changes. The construction descends from the local lift cover because the crystalline object and its comparison maps satisfy the cocycle condition. $\square$

Equivalently, for a smooth proper family $C\to B_0$, the assignments

$$
(U,T)\longmapsto H^i_{\mathrm{cris}}(C_U/T)
$$

are finite locally free crystals on $B_0/B$. Crystallinity is exactly (6.4) applied to arrows of base thickenings.

### 6.4 Genus zero, genus one, and a warning

For $C=\mathbf P^1$, (6.3) has zero outer terms, so

$$
H^*_{\mathrm{cris}}(\mathbf P^1/S)
\simeq\mathcal O_S[h]/(h^2),\qquad |h|=2.
$$

The trace is normalized by $\operatorname{Tr}(h)=1$. Frobenius will send $h$ to $ph$.

For an elliptic curve, $H^1_{\mathrm{cris}}$ has rank two and contains the invariant-differential line as its Hodge submodule on every lift. Ordinary and supersingular elliptic curves have the same rank; their distinction lies in Frobenius, not in the size of cohomology.

Smoothness cannot be removed. On a nodal curve, ordinary differentials have torsion and are not the relative dualizing sheaf. The two-term de Rham argument above no longer proves crystalline comparison for the singular fiber. Logarithmic or semistable cohomology is a different theory.

## 7. Trace and Poincaré duality

Finiteness alone gives a lattice; duality gives its geometry. The trace turns top-degree cup product into a scalar, and smooth properness makes the resulting pairing perfect. We construct the trace locally in de Rham theory and use descent to show that it is intrinsic.

### 7.1 Construction of the trace

Let $f:X\to S_0$ be smooth proper of pure relative dimension $d$. On a smooth proper lift $\widetilde X/S$, relative duality gives

$$
R^df_*\Omega^d_{\widetilde X/S}\longrightarrow\mathcal O_S. \tag{7.1}
$$

The Hodge edge map sends top de Rham cohomology to this module. Define

$$
\operatorname{Tr}_{\mathrm{cris}}:
H^{2d}_{\mathrm{cris}}(X/S)\longrightarrow\mathcal O_S \tag{7.2}
$$

as the composite under crystalline--de Rham comparison.

**Proposition 7.1.** The trace (7.2) is independent of the lift, compatible with arbitrary PD base change, and normalized by

$$
\operatorname{Tr}_{\mathrm{cris}}(c_1(\mathcal O(1))^d)=1
$$

on $\mathbf P^d$.

**Proof.** A comparison between two lifts is induced from their product envelope. Relative duality trace is functorial under this comparison because it is characterized by evaluation against $1\in f_*\mathcal O$; hence the two local traces agree. The same characterization proves base change. On projective space, the Čech residue calculation sends the standard top logarithmic cocycle, which represents $c_1(\mathcal O(1))^d$, to $1$. $\square$

For a disconnected smooth proper scheme, the trace is the sum over connected components. We shall mainly use geometrically connected curves and abelian schemes.

### 7.2 Perfect duality

Cup product followed by trace defines

$$
H^i_{\mathrm{cris}}(X/S,\mathcal E)
\otimes H^{2d-i}_{\mathrm{cris}}(X/S,\mathcal E^\vee)
\longrightarrow\mathcal O_S. \tag{7.3}
$$

The derived form is cleaner.

**Theorem 7.2 (crystalline Poincaré duality).** For $f:X\to S_0$ smooth proper of relative dimension $d$ and $\mathcal E$ a finite locally free crystal, cup product and trace induce an isomorphism

$$
Rf_*\mathcal E
\xrightarrow{\sim}
R\mathcal Hom_S(Rf_*\mathcal E^\vee,\mathcal O_S)[-2d]. \tag{7.4}
$$

If the cohomology modules on either side are finite locally free, (7.3) is a perfect pairing in each degree.

**Proof strategy and proof.** The assertion is local on $S$ and compatible with derived base change. Choose an embedding system and compare with de Rham complexes on smooth lifts. There (7.4) is relative de Rham duality: wedge product

$$
(M\otimes\Omega^a)\otimes(M^\vee\otimes\Omega^{d-a})
\to\Omega^d
$$

is perfect termwise after reversing degrees, and relative Grothendieck duality identifies derived global sections of the resulting dual complex with the dual of derived global sections. The differentials are adjoint up to the total-complex sign, since

$$
d\langle\alpha,\beta\rangle
=\langle\nabla\alpha,\beta\rangle
+(-1)^{\deg\alpha}\langle\alpha,\nabla^\vee\beta\rangle.
$$

Thus the local map is a quasi-isomorphism. Comparisons between lifts respect wedge product and trace, so descent globalizes it. Taking cohomology of a dual perfect complex yields the final assertion when the cohomology modules are projective. $\square$

Derived duality remains true even when individual cohomology modules contain torsion. In that case Ext terms can join neighboring degrees, and one must not replace (7.4) by a collection of naive module dualities.

### 7.3 Curves and the alternating degree-one form

For a smooth proper geometrically connected curve, define

$$
\langle x,y\rangle_C=
\operatorname{Tr}_{\mathrm{cris}}(x\smile y). \tag{7.5}
$$

**Corollary 7.3.** The pairing (7.5) on $H^1_{\mathrm{cris}}(C/S)$ is perfect and alternating in every characteristic. The Hodge submodule $f_*\Omega^1_{\widetilde C/S}$ in (6.3) is Lagrangian.

**Proof.** Perfection follows from Theorems 6.2 and 7.2. Graded commutativity gives skew-symmetry. In characteristic two, skew-symmetry alone does not imply alternation. Use the two-column Čech--de Rham model: the square of a total degree-one cocycle is the boundary of its product correction, while the wedge of two relative one-forms vanishes because $\Omega^2_{C/S}=0$. Hence $x\smile x=0$ in top cohomology.

Two Hodge classes cup into filtration degree two, which is zero for a curve; the Hodge submodule is isotropic. Its rank is $g$, half the rank $2g$ of the ambient module, so perfection makes it Lagrangian. $\square$

### 7.4 Adjointness for finite maps

Let $u:C\to D$ be a finite locally free morphism of smooth proper curves. Trace of finite algebras on functions and relative-duality trace on one-forms commute with $d$, giving

$$
u_*:H^i_{\mathrm{cris}}(C/S)\to H^i_{\mathrm{cris}}(D/S).
$$

**Proposition 7.4.** For $x\in H^*_{\mathrm{cris}}(D/S)$ and $y\in H^*_{\mathrm{cris}}(C/S)$,

$$
u_*(u^*x\smile y)=x\smile u_*y, \tag{7.6}
$$

and $u_*u^*=(\deg u)$.

**Proof.** Both identities may be checked after crystalline--de Rham comparison. On functions they are the projection formula and the identity $\operatorname{Tr}(1)=\deg u$. On top forms they follow from transitivity of residues. Compatibility with $d$ makes these termwise identities identities of de Rham complexes, hence of hypercohomology. $\square$

Thus pullback and pushforward are adjoint for (7.5). No inverse to $\deg u$ is asserted integrally.

## 8. The Künneth theorem

Products are unavoidable for group schemes: addition on an abelian scheme has source $A\times A$. To identify primitive classes, one must know the cohomology of that product. The Künneth theorem supplies the identification without assuming beforehand that cohomology is flat.

### 8.1 The derived exterior product

For smooth proper $X,Y$ over $S_0$, the two projections and cup product give

$$
R\Gamma_{\mathrm{cris}}(X/S)\otimes^L_A
R\Gamma_{\mathrm{cris}}(Y/S)
\longrightarrow
R\Gamma_{\mathrm{cris}}(X\times_{S_0}Y/S). \tag{8.1}
$$

The derived tensor is essential. If the cohomology of either factor has torsion, the cohomology of the left side contains Tor terms which a direct sum of ordinary tensor products would miss.

### 8.2 Proof by local de Rham comparison

**Theorem 8.1 (derived Künneth).** The map (8.1) is a quasi-isomorphism. It is associative, graded commutative under interchange of factors, compatible with arbitrary PD base change, and compatible with trace.

**Proof strategy and proof.** Locally choose smooth lifts $\widetilde X,\widetilde Y$; their product lifts $X\times Y$. The de Rham complex of the product has the canonical decomposition

$$
\Omega^n_{\widetilde X\times\widetilde Y/S}
\simeq\bigoplus_{a+b=n}
\operatorname{pr}_X^*\Omega^a_{\widetilde X/S}
\otimes\operatorname{pr}_Y^*\Omega^b_{\widetilde Y/S}. \tag{8.2}
$$

The differential is $d_X\otimes1+(-1)^a1\otimes d_Y$. Proper projection formulas and the fact that the de Rham terms are finite locally free identify derived global sections of (8.2) with the derived tensor of the two de Rham hypercohomology complexes. This proves the local quasi-isomorphism. Embedding systems give the same proof when global lifts do not exist. The identities follow from the corresponding identities for exterior products of forms. Trace compatibility is Fubini for relative duality:

$$
\operatorname{Tr}_{X\times Y}(x\boxtimes y)
=\operatorname{Tr}_X(x)\operatorname{Tr}_Y(y).
$$

Finally, Theorem 5.2 supplies arbitrary derived base change. $\square$

### 8.3 The cohomological decomposition

If every cohomology module of both factors is finite locally free, the Tor terms vanish and Theorem 8.1 gives

$$
H^n_{\mathrm{cris}}(X\times Y/S)
\simeq\bigoplus_{a+b=n}
H^a_{\mathrm{cris}}(X/S)\otimes_AH^b_{\mathrm{cris}}(Y/S). \tag{8.3}
$$

In particular, for connected smooth proper $X$ and $Y$,

$$
H^1_{\mathrm{cris}}(X\times Y/S)
\simeq H^1_{\mathrm{cris}}(X/S)\oplus H^1_{\mathrm{cris}}(Y/S). \tag{8.4}
$$

The two summands are the images of the projection pullbacks. Formula (8.4) will make the word "primitive" precise for abelian schemes.

## 9. Frobenius

Crystalline cohomology was designed to retain Frobenius, but the construction is not simply pullback along a map of a chosen lift. A lift of $X$ need not carry a global Frobenius lift, and local Frobenius lifts are not unique. Crystallinity supplies the comparisons which make the resulting cohomological map canonical.

### 9.1 Semilinearity and twists

Let $k$ be perfect of characteristic $p$, let $W_n=W_n(k)$, and let $\sigma$ be Witt Frobenius. The absolute Frobenius $F_X:X\to X$ lies over Frobenius of $k$, not over its identity. Consequently its action on crystalline cohomology is $\sigma$-semilinear:

$$
F(ax)=\sigma(a)F(x). \tag{9.1}
$$

Equivalently, it is a linear map

$$
\Phi:\sigma^*H^i_{\mathrm{cris}}(X/W_n)
\longrightarrow H^i_{\mathrm{cris}}(X/W_n). \tag{9.2}
$$

When $k$ is not perfect, one must use the relative Frobenius $X\to X^{(p)}$ and retain the twist. We restrict the isogeny theorem below to perfect $k$ so that a single semilinear endomorphism may be displayed.

The twist convention is fixed by

$$
W(-r)=(W,p^r\sigma).
$$

Thus a Frobenius-compatible perfect pairing

$$
M\otimes N\to W(-d)
$$

means $\langle\Phi x,\Phi y\rangle=p^d\sigma\langle x,y\rangle$.

### 9.2 Construction without a global Frobenius lift

Choose an embedding system $X\hookrightarrow Y_\bullet$ over $W_n$. Smoothness gives local $\sigma$-semilinear Frobenius lifts $\varphi$ on $Y_r$: in étale coordinates send each coordinate to its $p$th power and lift through the étale map. Such a $\varphi$ maps the ideal of $X$ into itself modulo $p$ and therefore extends, by the universal property, to the PD envelopes.

Two lifts $\varphi$ and $\psi$ have the same reduction on $X$. The pair $(\varphi,\psi)$ consequently factors through the diagonal PD envelope. The stratification of the structure crystal identifies the two induced pullbacks. In the de Rham model, that identification is the Taylor homotopy between the two maps.

**Proposition 9.1.** The local maps induced by Frobenius lifts descend to a canonical semilinear endomorphism

$$
\Phi:R\Gamma_{\mathrm{cris}}(X/W_n)^{(\sigma)}
\longrightarrow R\Gamma_{\mathrm{cris}}(X/W_n). \tag{9.3}
$$

It is functorial in $X$, multiplicative, compatible with finite-level reduction, base change of perfect fields, Künneth, and trace.

**Proof.** On every simplicial lift, pullback by $\varphi$ is a map of de Rham models. The diagonal stratification supplies a chain homotopy between maps from two choices; the triple diagonal gives coherence among three choices. Hence the maps glue in the derived category and are independent of all choices. Pullback of functions and forms respects products and simplicial maps, proving functoriality, multiplicativity, and Künneth compatibility. All constructions commute with reduction of PD envelopes. Trace compatibility follows from functoriality of relative duality, with the factor $p^d$ computed in Section 9.4. $\square$

The differential $d\varphi$ is divisible by $p$ on a $p$-torsion-free lift. In degree $a$ there is therefore a divided pullback

$$
p^{-a}\varphi^*: \sigma^*\Omega^a_{Y/W}\longrightarrow\Omega^a_{Y/W}. \tag{9.4}
$$

This auxiliary map helps prove that $\Phi$ is an isogeny, but the canonical $\Phi$ itself uses the undivided pullback.

### 9.3 The Frobenius isogeny theorem

**Theorem 9.2 (Frobenius isogeny).** Let $X/k$ be smooth proper with $k$ perfect. Each

$$
H^i_{\mathrm{cris}}(X/W(k))
$$

is finite over $W(k)$, and its Frobenius becomes an isomorphism after inverting $p$:

$$
\Phi:\sigma^*H^i_{\mathrm{cris}}(X/W)[1/p]
\xrightarrow{\sim}H^i_{\mathrm{cris}}(X/W)[1/p]. \tag{9.5}
$$

If $H^i$ is torsion-free, $\Phi$ is injective and its cokernel is killed by a power of $p$.

**Proof strategy.** Filter the de Rham model by form degree. Divisibility of $d\varphi$ supplies divided Frobenius on each graded degree. Modulo $p$, the resulting graded map is the Cartier operator, which is an isomorphism for a smooth scheme. A filtered-map argument then proves rational invertibility.

More explicitly, on a smooth affine special fiber the Cartier isomorphism is

$$
C^{-1}:\Omega^a_{X^{(p)}/k}
\xrightarrow{\sim}\mathcal H^a(F_{X/k,*}\Omega^\bullet_{X/k}), \tag{9.6}
$$

characterized in coordinates by

$$
dx_{i_1}\wedge\cdots\wedge dx_{i_a}
\longmapsto
[x_{i_1}^{p-1}\cdots x_{i_a}^{p-1}
dx_{i_1}\wedge\cdots\wedge dx_{i_a}].
$$

To prove (9.6), reduce étale-locally to a polynomial algebra. Write every polynomial uniquely as a sum of monomials $x^\nu g_\nu(x^p)$ with $0\le\nu_i<p$. The de Rham complex becomes a tensor product of one-variable complexes. In one variable, all summands are exact except the constant in degree zero and $x^{p-1}dx$ in degree one. Tensoring gives precisely the displayed basis. Étale descent globalizes the calculation.

Now use (9.4). On form degree $a$, $p^{-a}\varphi^*$ reduces to $C^{-1}$. Hence the direct sum of the divided graded maps is a quasi-isomorphism modulo $p$. For the undivided map $\Phi$, multiplication by $p^a$ intervenes on the $a$th filtration layer. After $p$ is inverted these factors are units, so the associated graded map is a quasi-isomorphism. A finite filtered-complex comparison proves that $\Phi$ is a quasi-isomorphism after inverting $p$. Taking cohomology gives (9.5).

Finite generation follows from the inverse-limit perfect complex of Chapter 10, or directly from finite-level perfectness and compatible bounded finite free representatives. If $H^i$ is torsion-free, a map which becomes injective after inverting $p$ is injective. Its finite cokernel is $p$-power torsion and hence killed by some power of $p$. $\square$

The theorem does not say that $\Phi$ is integrally invertible. For $H^2_{\mathrm{cris}}(\mathbf P^1/W)=Wh$, one has $\Phi(h)=ph$.

### 9.4 Duality and Frobenius

**Proposition 9.3.** For $X/k$ smooth proper of dimension $d$,

$$
\operatorname{Tr}_{\mathrm{cris}}(\Phi z)
=p^d\sigma(\operatorname{Tr}_{\mathrm{cris}}z), \tag{9.7}
$$

and therefore

$$
\langle\Phi x,\Phi y\rangle
=p^d\sigma\langle x,y\rangle. \tag{9.8}
$$

**Proof.** It is enough to compute on a local smooth lift. Pullback by Frobenius on a top form is divisible by $p^d$. Modulo $p$, the divided top pullback is the top Cartier operator, whose residue trace agrees with Frobenius on scalars. Thus (9.7) holds modulo every $p^n$, and separatedness gives it over $W$. Equation (9.8) follows from multiplicativity of $\Phi$ and the definition of the pairing. $\square$

For a curve, the alternating form on $H^1$ therefore takes values in $W(-1)$. For an abelian variety of dimension $g$, top duality takes values in $W(-g)$, while the polarization form on degree one takes values in $W(-1)$.

## 10. Completed crystalline cohomology

Arithmetic applications use one $p$-adic lattice rather than an unrelated module at each finite level. The passage to the limit is safe because perfectness allows compatible finite free models and because the transition systems are surjective. This chapter isolates exactly what is gained, and what still requires torsion-freeness.

### 10.1 Passage through finite levels

Put

$$
K_n=R\Gamma_{\mathrm{cris}}(X/W_n(k)).
$$

Derived base change gives

$$
K_{n+1}\otimes^L_{W_{n+1}}W_n\simeq K_n. \tag{10.1}
$$

**Theorem 10.1.** If $X/k$ is smooth proper, there is a bounded complex $P$ of finite free $W(k)$-modules such that

$$
P\otimes^L_WW_n\simeq K_n
$$

compatibly for all $n$. Consequently

$$
R\varprojlim_nK_n\simeq P,
$$

so completed crystalline cohomology is a perfect $W$-complex.

**Proof strategy and proof.** Choose bounded finite free representatives for $K_n$ with the common amplitude $[0,2d]$. Assume $P_n$ has been chosen. Lift the matrices of its differentials to $W_{n+1}$. The relation $d^2=0$ may fail by a matrix divisible by $p^n$; the derived base-change isomorphism (10.1) and the vanishing of the resulting obstruction in the deformation group of the perfect complex allow a correction by a matrix divisible by $p^n$. Inductively obtain compatible $P_n$ with degreewise surjective transitions.

Taking inverse limits degreewise gives finite free $W$-modules because a compatible system of finite free $W_n$-modules of fixed rank is the reduction system of a finite free $W$-module. Surjectivity kills $R^1\varprojlim$ in every degree. The limit differential squares to zero and reduces to every $P_n$, proving the claim. $\square$

The correction argument is the usual idempotent-and-differential lifting for perfect complexes over the complete ring $W$. It would fail without the compatibility (10.1) or without a uniform bounded finite projective model.

### 10.2 Torsion-freeness and reduction

Let $H^i=H^i(P)$. From the triangle $P\xrightarrow{p^n}P\to P\otimes^LW_n$ one gets

$$
0\to H^i/p^nH^i\to H^i_{\mathrm{cris}}(X/W_n)
\to H^{i+1}[p^n]\to0. \tag{10.2}
$$

Thus:

**Proposition 10.2.** The reduction map

$$
H^i_{\mathrm{cris}}(X/W)\otimes_WW_n
\longrightarrow H^i_{\mathrm{cris}}(X/W_n) \tag{10.3}
$$

is an isomorphism if and only if $H^{i+1}_{\mathrm{cris}}(X/W)$ has no $p^n$-torsion. It is an isomorphism for all $i,n$ when all integral cohomology groups are torsion-free.

**Proof.** This is exactly (10.2). $\square$

For curves, duality and the rank calculation show that $H^0,H^1,H^2$ are finite free over $W$, so reduction is exact in every degree. The same will follow for abelian schemes from the exterior algebra theorem. For a general smooth proper variety, crystalline cohomology can contain torsion; perfectness alone does not remove the right term of (10.2).

### 10.3 The integral and rational objects

For a smooth proper curve or abelian variety over perfect $k$, write

$$
H^i_{\mathrm{cris}}(X/W)
$$

for the finite free integral lattice with semilinear Frobenius, and

$$
H^i_{\mathrm{cris}}(X/W)_{\mathbf Q}
=H^i_{\mathrm{cris}}(X/W)\otimes_WK_0,
\qquad K_0=W[1/p],
$$

for its isocrystal. Frobenius is an isomorphism on the latter.

Different lattices can lie in the same isocrystal. The integral crystalline lattice is distinguished because it is the derived inverse limit of the finite PD cohomologies, not because rational Frobenius determines it. This distinction is essential whenever finite-flat group schemes or integral moduli conditions are involved.

## 11. Abelian schemes: degree one

An abelian scheme adds a Hopf structure to crystalline cohomology. Degree one is primitive under addition, duality identifies it with the degree-one object of the dual abelian scheme, and every higher degree will be forced from it by exterior products.

### 11.1 The first crystalline crystal

Let $a:A\to S_0$ be an abelian scheme of relative dimension $g$ over a nilpotent PD base $S$. By Theorem 5.1, $Ra_{\mathrm{cris},*}\mathcal O$ is perfect. The group law, identity, inversion, and multiplication maps act contravariantly on it.

For a relative abelian scheme $A\to B_0$, define

$$
\mathbb H^1_{\mathrm{cris}}(A/B)
=R^1a_{\mathrm{cris},*}\mathcal O_{A/B}. \tag{11.1}
$$

At this point (11.1) is only a coherent cohomology sheaf. We shall prove it finite locally free by evaluating on local PD thickenings.

Deformations of an abelian scheme over a nilpotent thickening exist locally on the base. One route is to deform the identity-rigidified group law together with a relatively ample symmetric line bundle: the obstruction to deforming the line bundle is killed after a faithfully flat localization, the smooth proper scheme deforms formally, and rigidity extends the group law uniquely from the special fiber. The theorem of the cube verifies associativity. Thus every base point has a PD neighborhood $T$ on which $A$ has an abelian-scheme lift $\widetilde A/T$.

### 11.2 The crystalline Hodge extension

On such a lift, crystalline--de Rham comparison and Book 52 give

$$
0\longrightarrow\omega_{\widetilde A/T}
\longrightarrow H^1_{\mathrm{cris}}(A_T/T)
\longrightarrow R^1a_*\mathcal O_{\widetilde A}
\longrightarrow0. \tag{11.2}
$$

Book 38 identifies

$$
R^1a_*\mathcal O_{\widetilde A}
\simeq\omega_{\widetilde A^\vee/T}^{\vee}. \tag{11.3}
$$

Both outer terms have rank $g$. Comparisons between two abelian lifts carry their Hodge-filtered de Rham complexes to the same crystalline complex, so (11.2) is intrinsic to the evaluated crystal, although the displayed Hodge submodule depends on the chosen base lifting situation.

**Theorem 11.1.** The sheaf $\mathbb H^1_{\mathrm{cris}}(A/B)$ is a finite locally free crystal of rank $2g$. Its evaluation on a PD thickening admitting an abelian lift fits into (11.2)--(11.3), compatibly with PD base change.

**Proof.** The outer terms of (11.2) are finite locally free of rank $g$, so the middle term is locally free of rank $2g$. Theorem 5.2 and Proposition 5.3 give arbitrary base change. Therefore the evaluations along an arrow of base thickenings are related by scalar extension isomorphisms, which is exactly crystallinity. Descent from the local cover proves the global statement. $\square$

### 11.3 Primitivity under the group law

Let $m:A\times A\to A$ be addition and $p_1,p_2$ the projections. By Künneth,

$$
H^1_{\mathrm{cris}}(A\times A/S)
\simeq p_1^*H^1_{\mathrm{cris}}(A/S)
\oplus p_2^*H^1_{\mathrm{cris}}(A/S). \tag{11.4}
$$

**Proposition 11.2.** Every $x\in H^1_{\mathrm{cris}}(A/S)$ is primitive:

$$
m^*x=p_1^*x+p_2^*x. \tag{11.5}
$$

Moreover $[-1]^*x=-x$ and $[n]^*x=nx$.

**Proof.** Under (11.4), write $m^*x=(u,v)$. Pull back along $(1,e):A\to A\times A$. Since $m(1,e)=1$, $p_1(1,e)=1$, and $p_2(1,e)$ factors through the base, positive-degree cohomology of the second projection vanishes; hence $u=x$. Pulling back along $(e,1)$ gives $v=x$, proving (11.5).

The identity $m(1,[-1])=e$ and (11.5) give $x+[-1]^*x=0$. Induction using $[n+1]=m([n],1)$ gives $[n]^*x=nx$ for $n\ge0$, and inversion handles negative $n$. $\square$

This proof uses Künneth only in degree one and does not count points or assume that $n$ is invertible.

### 11.4 Homomorphisms and isogenies

A homomorphism $u:A\to B$ induces

$$
u^*:H^1_{\mathrm{cris}}(B/S)\to H^1_{\mathrm{cris}}(A/S), \tag{11.6}
$$

functorially and compatibly with Frobenius. On a lift it preserves the Hodge sequence and restricts on invariant forms to the cotangent map at the identity.

If $u$ is an isogeny of degree $d$, Book 38 supplies $u':B\to A$ with $u'u=[d]$ and $uu'=[d]$. Proposition 11.2 gives

$$
(u')^*u^*=d,
\qquad u^*(u')^*=d. \tag{11.7}
$$

**Corollary 11.3.** The map $u^*$ is an isomorphism after $d$ is inverted. Its kernel and cokernel integrally are killed by $d$. If $d$ is a unit on the base, it is an isomorphism of finite locally free crystals.

**Proof.** Equation (11.7) provides a two-sided inverse $d^{-1}(u')^*$ after localization and kills the integral kernel and cokernel. $\square$

For a $p$-isogeny in characteristic $p$, $u^*$ need not be an integral isomorphism: its map on invariant differentials may vanish. Isogeny invariance must therefore state which integer is inverted.

## 12. The exterior algebra theorem

The cohomology of an abelian scheme is not merely of the same rank as an exterior algebra. Cup product gives a canonical exterior-algebra map, the Hopf coproduct recognizes its primitive generators, and de Rham comparison proves that the map is an integral isomorphism.

### 12.1 The cup-product map

Alternation of cup product gives canonical maps

$$
\alpha_n:\bigwedge^nH^1_{\mathrm{cris}}(A/S)
\longrightarrow H^n_{\mathrm{cris}}(A/S). \tag{12.1}
$$

In characteristic two, graded commutativity only says $x\smile y=-y\smile x$, which becomes symmetry. To factor through the exterior power one also needs $x\smile x=0$. This may be checked after a faithfully flat cover admitting an abelian lift. Book 52 proved there that the full de Rham algebra is exterior on degree one, including characteristic two. Crystalline--de Rham comparison carries the assertion back to (12.1).

### 12.2 Proof of the exterior algebra theorem

**Theorem 12.1 (abelian exterior algebra).** For an abelian scheme $A/S_0$ of relative dimension $g$ over a nilpotent PD base,

$$
\alpha:\bigwedge
H^1_{\mathrm{cris}}(A/S)
\xrightarrow{\sim}H^*_{\mathrm{cris}}(A/S) \tag{12.2}
$$

is an isomorphism of graded Hopf algebras and finite locally free crystals. Consequently

$$
\operatorname{rank}H^n_{\mathrm{cris}}(A/S)=\binom{2g}{n}, \tag{12.3}
$$

and all cohomology vanishes outside $0\le n\le2g$.

**Proof strategy.** The assertion is local for the faithfully flat topology on the base. Choose an abelian lift $\widetilde A/S$. Theorem 3.2 identifies crystalline cohomology with de Rham cohomology, compatibly with products and the group law. Book 52 proved the de Rham exterior algebra theorem for abelian schemes by filtering both sides by the Hodge filtration and identifying their graded pieces.

For completeness, those graded pieces are

$$
\bigwedge^a\omega_{\widetilde A}
\otimes\bigwedge^bR^1a_*\mathcal O_{\widetilde A},
\qquad a+b=n. \tag{12.4}
$$

Translation identifies $\Omega^a_{\widetilde A/S}$ with $a^*\bigwedge^a\omega_{\widetilde A}$, and the coherent Hopf-algebra theorem gives

$$
R^ba_*\mathcal O_{\widetilde A}
\simeq\bigwedge^bR^1a_*\mathcal O_{\widetilde A}. \tag{12.5}
$$

Thus (12.4) is exactly $R^ba_*\Omega^a$, the Hodge graded piece of $H^n_{\mathrm{dR}}$. The degree-one Hodge differentials vanish by primitivity, and every later differential is a derivation compatible with the Hopf coproduct. An exterior Hopf algebra on primitive degree-one generators has no new primitive generator in higher degree: the coproduct of $x_1\wedge\cdots\wedge x_r$ contains nonzero mixed tensors for $r>1$. Hence all differentials vanish. The associated graded of $\alpha_n$ is the identity on (12.4), so finite filtered comparison makes it an isomorphism.

The local isomorphisms agree on overlaps because $\alpha$ is intrinsically cup product. Faithfully flat descent proves (12.2). The source is finite locally free by Theorem 11.1, giving (12.3), base change, and the crystal assertion. Compatibility with the coproduct follows from functoriality of cup product under addition. $\square$

The proof establishes integral exterior generation; it is stronger than a rank calculation after inverting $p$.

### 12.3 Multiplication and ranks

Combining Proposition 11.2 with (12.2) gives

$$
[n]^*=n^r\quad\text{on }H^r_{\mathrm{cris}}(A/S). \tag{12.6}
$$

For $n=p$, this is the action of the group-scheme multiplication map, not the arithmetic Frobenius. The two maps must not be confused. In characteristic $p$ the multiplication map factors as Verschiebung after relative Frobenius, and on cohomology their contravariant actions compose to $p^r$ in degree $r$.

The top cohomology is a line:

$$
H^{2g}_{\mathrm{cris}}(A/S)
\simeq\bigwedge^{2g}H^1_{\mathrm{cris}}(A/S).
$$

Trace identifies this line with $\mathcal O_S$, while Frobenius on it is $p^g\sigma$ after the trace normalization. This agrees with Proposition 9.3.

## 13. Dual abelian schemes and polarizations

The exterior algebra describes the size of abelian crystalline cohomology. The Poincaré bundle describes its duality. Its first crystalline Chern class pairs the degree-one objects of $A$ and $A^\vee$; a polarization then converts this evaluation pairing into an alternating form on one object.

Throughout this chapter, the base PD ideal is PD-nilpotent, or a prime $p$ is locally nilpotent on the base. The second condition is the one satisfied by the finite Witt bases. It ensures that the divided-power logarithms used to construct integral Chern classes terminate locally.

### 13.1 The crystalline Poincaré class

For a line bundle $L$ on a smooth $X/S_0$, choose local transition functions $g_{ij}$. On every PD thickening, lift the $g_{ij}$ locally to units $\widetilde g_{ij}$. If $u=1+x$ with $x$ in the nilpotent PD ideal, the divided-power logarithm

$$
\log_{\mathrm{PD}}(u)=
\sum_{n\ge1}(-1)^{n-1}(n-1)!x^{[n]} \tag{13.1}
$$

is a finite integral sum and satisfies $d\log_{\mathrm{PD}}(u)=u^{-1}du$. Under PD-nilpotence the high divided powers vanish; when $p^N=0$, the valuation of $(n-1)!$ tends to infinity and kills all high terms. The failure

$$
u_{ijk}=\widetilde g_{ij}\widetilde g_{jk}\widetilde g_{ki}
$$

lies in $1+I$. The total Čech--de Rham cocycle has one-form component $d\log\widetilde g_{ij}$ and function component $\log_{\mathrm{PD}}(u_{ijk})$. The identities for the divided-power logarithm verify the total cocycle condition. Changing the lifts changes this pair by a total coboundary. It defines

$$
c_1^{\mathrm{cris}}(L)\in H^2_{\mathrm{cris}}(X/S). \tag{13.2}
$$

Tensor product and pullback satisfy

$$
c_1(L\otimes M)=c_1(L)+c_1(M),
\qquad c_1(u^*L)=u^*c_1(L). \tag{13.3}
$$

These identities follow already on transition functions.

Let $\mathcal P$ be the normalized Poincaré bundle on $A\times A^\vee$ supplied by Book 38. By Künneth,

$$
H^2_{\mathrm{cris}}(A\times A^\vee/S)
\simeq H^2(A)\oplus
\bigl(H^1(A)\otimes H^1(A^\vee)\bigr)\oplus H^2(A^\vee). \tag{13.4}
$$

Normalization makes $\mathcal P$ trivial on $A\times e$ and $e\times A^\vee$, so its Chern class has zero components in the two outer summands. Hence it gives a tensor

$$
\eta_{\mathcal P}\in
H^1_{\mathrm{cris}}(A/S)\otimes
H^1_{\mathrm{cris}}(A^\vee/S). \tag{13.5}
$$

The two biextension laws imply that this tensor is primitive in each variable, agreeing with its degree-one placement.

### 13.2 Perfect duality in degree one

Put $V=H^1_{\mathrm{cris}}(A/S)$ and $V^\vee_A=H^1_{\mathrm{cris}}(A^\vee/S)$. The tensor (13.5) induces

$$
t_{\mathcal P}:V^*\longrightarrow V^\vee_A. \tag{13.6}
$$

**Theorem 13.1 (Poincaré duality for the dual abelian scheme).** The map (13.6) is an isomorphism of finite locally free crystals. It is compatible with arbitrary base change, biduality, and homomorphisms: for $u:A\to B$, the maps $u^*$ and $(u^\vee)^*$ are adjoint.

**Proof strategy and proof.** Work locally on a PD thickening admitting lifts of $A$ and $A^\vee$ together with the Poincaré biextension; the biextension lifts because its cubical rigidifications remove the obstruction and scalar ambiguity. Under crystalline--de Rham comparison, (13.6) is the de Rham Poincaré map of Book 52.

Its Hodge graded pieces are the evaluation isomorphisms

$$
\omega_A\simeq(R^1a^\vee_*\mathcal O_{A^\vee})^*,
\qquad
R^1a_*\mathcal O_A\simeq\omega_{A^\vee}^*. \tag{13.7}
$$

They follow from the tangent description of the dual abelian scheme in Book 38. Therefore the associated graded of (13.6) is an isomorphism, and finite filtered comparison proves the map itself is an isomorphism. The construction from the normalized Poincaré bundle is intrinsic, so it descends. Base change follows from Theorem 12.1. Finally,

$$
(u\times1)^*\mathcal P_B\simeq(1\times u^\vee)^*\mathcal P_A
$$

as normalized biextensions; taking Chern classes proves adjointness. $\square$

### 13.3 Polarization forms

Let $\lambda:A\to A^\vee$ be a polarization. Pullback gives

$$
\lambda^*:H^1_{\mathrm{cris}}(A^\vee/S)\longrightarrow V. \tag{13.8}
$$

If $\lambda$ is principal, combine (13.6) and (13.8) to identify $V^*$ with $V$. The inverse identification defines

$$
\psi_\lambda:V\otimes V\longrightarrow\mathcal O_S. \tag{13.9}
$$

**Theorem 13.2.** For a principal polarization, $\psi_\lambda$ is perfect and alternating, the Hodge submodule $\omega_A$ on every lift is Lagrangian, and all assertions commute with PD base change. For a polarization of degree $d$, the same construction is perfect after $d$ is inverted; integrally it is represented by the isogeny $V^*\to V$ induced by $\lambda$.

**Proof.** Perfection in the principal case follows because both (13.6) and $\lambda^*$ are isomorphisms. Book 38 proves that a polarization is symmetric under biduality. The transpose of the Poincaré tensor introduces the sign appropriate to two degree-one factors, so symmetry of $\lambda$ gives

$$
\psi_\lambda(x,y)=-\psi_\lambda(y,x).
$$

For genuine alternation in characteristic two, work after a local lift. The de Rham polarization form of Book 52 is alternating by its biextension commutator construction; comparison carries this equality back. On Hodge graded pieces, two invariant forms pair to zero, so $\omega_A$ is isotropic. It has rank $g$ inside a perfect module of rank $2g$, hence is Lagrangian.

For a general polarization, Book 38 gives a quasi-inverse after $d=\deg\lambda$ is inverted. Thus $\lambda^*$ becomes an isomorphism there. Integrally there is no reason for it to be unimodular, so the map $V^*\to V$ is the correct datum. $\square$

For an elliptic curve with its canonical principal polarization, (13.9) equals the curve pairing (7.5). Both pairings have the same Hodge graded evaluation and the same trace normalization, so their difference vanishes after comparison on a lift.

### 13.4 Compatibility with Frobenius and isogenies

For a line bundle on the special fiber,

$$
F_X^*L\simeq L^{\otimes p},
$$

because Frobenius raises transition functions to the $p$th power. Hence

$$
\Phi(c_1^{\mathrm{cris}}(L))=p\,c_1^{\mathrm{cris}}(L). \tag{13.10}
$$

Applying this to $\mathcal P$ proves that the degree-one Poincaré evaluation has Frobenius weight one. For a polarization form,

$$
\psi_\lambda(\Phi x,\Phi y)
=p\,\sigma(\psi_\lambda(x,y)). \tag{13.11}
$$

Thus a principally polarized abelian variety over a perfect field determines a symplectic $F$-crystal with pairing into $W(-1)$.

If $u:A\to B$ is an isogeny and principal polarizations $\lambda$ on $A$ and $\mu$ on $B$ satisfy

$$
u^\vee\mu u=n\lambda, \tag{13.12}
$$

define $u_*:H^1_{\mathrm{cris}}(A/S)\to H^1_{\mathrm{cris}}(B/S)$ as the adjoint of $u^*$ under the two perfect polarization forms. Poincaré adjointness then gives

$$
\psi_\mu(u_*x,u_*y)=n\,\psi_\lambda(x,y)
$$

in the variance where $u_*$ is adjoint to $u^*$. Equivalently, using only pullback and identifying duals,

$$
\psi_\lambda(u^*x,u^*y)=n\,\psi_\mu(x,y). \tag{13.13}
$$

The scalar is dictated by (13.12); it is not automatically the degree of $u$. All maps commute with Frobenius because they come from morphisms defined on the special fiber.

## 14. Curves, Jacobians, and correspondences

Curves and abelian schemes meet through the Jacobian. Their degree-one crystalline cohomologies are the same contravariant realization, while the theta polarization matches the curve trace pairing. This identification lets a correspondence on curves be read as an endomorphism of a polarized crystal.

### 14.1 The Abel--Jacobi map in degree one

Let $C/S_0$ be a smooth proper curve of genus $g$ with a section $c$. The relative Picard and Jacobian theory established earlier proves that $J=\operatorname{Pic}^0_{C/S_0}$ is an abelian scheme, constructs its canonical principal polarization compatibly with base change, and gives the Abel--Jacobi map

$$
j_c:C\longrightarrow J,
\qquad x\longmapsto\mathcal O_C(x-c). \tag{14.1}
$$

Changing $c$ translates $j_c$. Translation by a section acts trivially on degree-one crystalline cohomology: it is homotopic in the Hopf sense to the identity because

$$
t_a=m(a,1)
$$

and positive-degree pullback along the constant map $a$ vanishes. Thus the map

$$
j_c^*:H^1_{\mathrm{cris}}(J/S)\to H^1_{\mathrm{cris}}(C/S) \tag{14.2}
$$

is independent of the chosen section. If no global section exists, sections exist after a faithfully flat base change and the independent maps descend.

### 14.2 The Jacobian comparison

**Theorem 14.1.** The map (14.2) is an isomorphism of finite locally free crystals, compatible with Frobenius and arbitrary PD base change. Under the canonical principal polarization of the Jacobian, its polarization form corresponds to the curve cup-product trace form.

**Proof strategy and proof.** Work locally on a thickening where the curve, its section, and its Jacobian lift. Filter the de Rham pullback by the Hodge sequences. On the Hodge submodules, the map is

$$
H^0(J,\Omega^1_{J/S})\longrightarrow H^0(C,\Omega^1_{C/S}). \tag{14.3}
$$

Invariant one-forms on the Picard scheme are cotangent vectors at the identity. The tangent space of $J$ is $R^1f_*\mathcal O_C$, so relative duality identifies its cotangent space with $f_*\omega_C$. Under this identification (14.3) is the identity. On the quotients of the Hodge sequences, duality makes the induced map the dual identity. Hence the associated graded of (14.2) is an isomorphism, and finite filtered comparison proves (14.2).

The theta polarization is characterized by the Poincaré divisor and the Abel--Jacobi image. Pulling its Poincaré Chern class back along $j_c\times j_c$ gives the diagonal class minus the two base-point axes. The axes contribute nothing to degree $(1,1)$, while the diagonal acts as the identity under Poincaré duality. Consequently the induced alternating pairing is exactly cup product followed by the curve trace. Frobenius and base-change compatibility follow from functoriality. $\square$

This proof also explains why degree one is the natural meeting point: higher cohomology of $J$ is the exterior algebra on the curve's $H^1$, not the cohomology of the curve itself.

### 14.3 Correspondences and adjoints

Let $C,D$, and $Z$ be smooth proper curves and suppose both arrows in the correspondence

$$
C\xleftarrow{p}Z\xrightarrow{q}D
$$

are finite locally free.

Define its action by

$$
T_Z=q_*p^*:H^1_{\mathrm{cris}}(C/S)
\longrightarrow H^1_{\mathrm{cris}}(D/S). \tag{14.4}
$$

If $Z^t$ is the transposed correspondence, Proposition 7.4 gives

$$
\langle T_Zx,y\rangle_D
=\langle x,T_{Z^t}y\rangle_C. \tag{14.5}
$$

Composing correspondences by fiber product and proper pushforward corresponds to composing their cohomological actions. This follows from flat base change and the projection formula; when a fiber product is not flat, the derived intersection must be used and the naive formula is not asserted.

Via Theorem 14.1, a correspondence action agrees with the pull-push homomorphism it induces on Jacobians. Thus its adjoint under the theta polarizations is represented by the transposed correspondence.

## 15. The structures used in finite-flat and PEL geometry

PEL geometry imposes endomorphisms, a polarization, and a Hodge condition. Crystalline cohomology transports these nonlinear geometric structures into linear algebra without discarding the integral lattice. This chapter records the exact output and its limits.

### 15.1 Endomorphism actions and idempotent factors

Let $\mathcal O$ be a finite free $\mathbf Z$-algebra acting on an abelian scheme $A$ through

$$
\iota:\mathcal O\longrightarrow\operatorname{End}(A).
$$

Contravariance gives a right action on $H^1_{\mathrm{cris}}(A/S)$,

$$
x\cdot a=\iota(a)^*x. \tag{15.1}
$$

It commutes with Frobenius because every endomorphism is defined on the same special fiber. It preserves the Hodge submodule on lifts because pullback preserves invariant differentials.

If $e\in\mathcal O\otimes R$ is an idempotent over a coefficient ring $R$, then

$$
M_R=eM_R\oplus(1-e)M_R \tag{15.2}
$$

for $M=H^1_{\mathrm{cris}}$. Both summands are direct factors and hence finite projective. The decomposition commutes with Frobenius when $e$ is fixed by the coefficient Frobenius.

Denominators matter. An idempotent in $\mathcal O\otimes\mathbf Q_p$ decomposes the isocrystal, but need not preserve the integral lattice. It yields an integral direct summand only if it lies in the integral endomorphism order acting on $M$.

### 15.2 Polarized linear algebra

Suppose a principal polarization $\lambda$ has Rosati involution

$$
a\longmapsto a^\dagger
$$

on $\mathcal O$. Poincaré adjointness gives

$$
\psi_\lambda(x\cdot a,y)
=\psi_\lambda(x,y\cdot a^\dagger). \tag{15.3}
$$

Together with Frobenius, the degree-one package is therefore

$$
(M,\Phi,\psi,\iota), \tag{15.4}
$$

where $M$ is finite locally free of rank $2g$, $\Phi:\sigma^*M\to M$ is an isogeny, $\psi$ is perfect alternating with values in the weight-one line, and $\mathcal O$ acts with adjoint involution $\dagger$.

On a lift, the Hodge submodule $\omega_A\subset M$ is Lagrangian and $\mathcal O$-stable. A determinant or signature condition in a PEL moduli problem is a statement about the characteristic polynomial of $a$ on $\omega_A$, not merely on $M$. The exact sequence

$$
0\to\omega_A\to M\to\omega_{A^\vee}^{\vee}\to0 \tag{15.5}
$$

shows how the polarization pairs the two Hodge pieces.

**Proposition 15.1.** If an idempotent $e$ is self-adjoint, the two factors in (15.2) are orthogonal. If $e^\dagger=1-e$, each factor is totally isotropic and the pairing identifies one with the dual of the other.

**Proof.** For $x=e x$ and $y=(1-e)y$, (15.3) gives

$$
\psi(x,y)=\psi(x,e^\dagger(1-e)y).
$$

If $e^\dagger=e$, the right side is zero. If $e^\dagger=1-e$, the same calculation with two vectors in $eM$ gives zero, and likewise for $(1-e)M$. Perfection of $\psi$ and the direct-sum ranks then identifies the two factors as mutual duals. $\square$

### 15.3 Integral cautions at the residue prime

Three distinctions govern applications.

First, an isogeny of degree divisible by $p$ need not identify integral crystalline lattices. It identifies their isocrystals, and it identifies lattices only after its degree is inverted or a stronger integral argument is supplied.

Second, a polarization of degree divisible by $p$ need not give a perfect integral alternating form. The integral datum is the map $M^*\to M$ with finite cokernel; perfectness appears after the polarization degree is inverted.

Third, a Frobenius-stable rational direct summand need not meet $M$ in a direct summand. Saturation and local freeness of the intersection must be proved. A rational PEL decomposition therefore does not automatically produce the finite-level integral pieces needed for finite-flat geometry.

These cautions do not weaken the package. They identify precisely which assertions are integral and which live only in the isogeny category.

## 16. Synthesis

The local crystalline site has now produced a global, finite, functorial theory. The final task is to state the package without hiding the hypotheses which make each transition valid.

### 16.1 The complete crystalline package

For a smooth proper morphism $X\to S_0$ over a locally noetherian nilpotent PD base:

- $Rf_{\mathrm{cris},*}\mathcal O$ is perfect and satisfies arbitrary derived PD base change;
- crystalline--de Rham comparison holds on every smooth lift and descends through embedding systems;
- cup product, the derived Künneth isomorphism, trace, and derived Poincaré duality are compatible;
- over a perfect field of characteristic $p$, Frobenius is semilinear and becomes invertible after $p$ is inverted.

For a smooth proper genus-$g$ curve, the cohomology crystals are finite locally free of ranks $1,2g,1$. Degree one has a perfect alternating form, and every base change is ordinary because flatness has been proved.

For an abelian scheme of relative dimension $g$,

$$
H^*_{\mathrm{cris}}(A/S)
\simeq\bigwedge^*H^1_{\mathrm{cris}}(A/S),
$$

with ranks $\binom{2g}{n}$. The Poincaré bundle identifies the degree-one crystal of $A^\vee$ with the dual of that of $A$. A principal polarization gives a perfect alternating Frobenius-compatible pairing, and the Hodge submodule on every lift is Lagrangian. The Jacobian identifies the degree-one packages of a curve and its associated abelian scheme.

### 16.2 Hypothesis ledger

| Assertion | Hypotheses used | Failure prevented |
|---|---|---|
| local de Rham comparison | smooth lift and quasi-nilpotent crystal | Taylor transport may not converge or integrate |
| global comparison | embedding system and cohomological descent | a global lift may not exist |
| finite perfect direct image | smoothness, properness, finite presentation, noetherian base | nonproper cohomology need not be finite |
| arbitrary base change | derived tensor product | nonflat change creates Tor |
| ordinary base change on $H^i$ | finite local freeness, or the precise neighboring Tor vanishing | cohomology need not commute with reduction |
| degreewise perfect duality | locally free cohomology | derived duality may contain Ext between degrees |
| cohomological Künneth direct sum | flat cohomology modules | Tor terms can survive |
| Frobenius as one endomorphism | perfect base field, or a retained Frobenius twist | absolute Frobenius is semilinear |
| Frobenius isomorphism | coefficients rationalized | integral Frobenius can have $p$-power cokernel |
| completed cohomology as an ordinary limit | compatible bounded finite free models and surjective transitions | $R^1\varprojlim$ classes can appear |
| perfect polarization form | principal polarization, or inversion of its degree | a nonprincipal integral form can be nonunimodular |
| isogeny invariance | inversion of the isogeny degree | a residue-characteristic isogeny can kill differentials |
| integral idempotent factor | an idempotent preserving the integral lattice | a rational summand need not be saturated |

Every entry corresponds to an actual obstruction. The derived statements are the unconditional backbone; the curve and abelian-scheme geometry supplies the flatness which turns them into the clean integral formulas used later.

### 16.3 Conclusion

Crystalline cohomology begins with divided-power infinitesimal transport and ends with integral linear algebra. The Poincaré lemma converts the many objects of the crystalline site into de Rham complexes on smooth lifts. Embedding systems make that calculation independent of global lifting. Properness and smoothness compress the result to a perfect complex; derived base change, Künneth, trace, and duality then follow in a form which remains correct in the presence of torsion.

Curves and abelian schemes add enough geometry to remove that torsion ambiguity. A curve contributes a rank-$2g$ symplectic degree-one crystal between two rank-one edge groups. An abelian scheme contributes a rank-$2g$ primitive crystal generating its entire cohomology by exterior powers. The Poincaré bundle, dual abelian scheme, and polarizations turn these modules into self-dual structures, while Frobenius gives their arithmetic motion and becomes invertible in the isogeny category. Jacobians identify the curve and abelian descriptions, and correspondences act by adjoint operators.

The resulting package is exactly the one required by integral finite-flat and PEL geometry:

$$
\text{smooth proper geometry}
\longrightarrow
\text{perfect crystalline complex}
\longrightarrow
\text{finite integral degree-one crystal}
\longrightarrow
(\Phi,\text{ pairing},\text{ endomorphisms},\text{ Hodge submodule}).
$$

Each arrow has now been constructed with its hypotheses, compatibilities, and proof, so no finiteness, base-change, duality, Künneth, or Frobenius assertion remains implicit.
