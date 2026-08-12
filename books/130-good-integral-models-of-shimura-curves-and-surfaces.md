# Good Integral Models of Quaternionic Shimura Curves

## Contents

- [1. The good-reduction problem](#1-the-good-reduction-problem)
  - [1.1 The fixed direct-trace curve](#11-the-fixed-direct-trace-curve)
  - [1.2 Conventions and the meaning of good](#12-conventions-and-the-meaning-of-good)
  - [1.3 Dependency ledger](#13-dependency-ledger)
- [2. Good integral PEL data](#2-good-integral-pel-data)
  - [2.1 Orders, lattices, and hyperspecial level](#21-orders-lattices-and-hyperspecial-level)
  - [2.2 The active quaternionic packet](#22-the-active-quaternionic-packet)
  - [2.3 The determinant law and orientation](#23-the-determinant-law-and-orientation)
  - [2.4 The exact hypothesis ledger](#24-the-exact-hypothesis-ledger)
- [3. The integral PEL functor and its flat closure](#3-the-integral-pel-functor-and-its-flat-closure)
  - [3.1 Objects and arrows](#31-objects-and-arrows)
  - [3.2 Representability and the universal family](#32-representability-and-the-universal-family)
  - [3.3 Generic comparison and schematic flat closure](#33-generic-comparison-and-schematic-flat-closure)
- [4. The good odd local model](#4-the-good-odd-local-model)
  - [4.1 Integral filtration lifting](#41-integral-filtration-lifting)
  - [4.2 The framed local-model diagram](#42-the-framed-local-model-diagram)
  - [4.3 The projective-line calculation](#43-the-projective-line-calculation)
- [5. Smoothness and extension](#5-smoothness-and-extension)
  - [5.1 Smoothness and the selected component union](#51-smoothness-and-the-selected-component-union)
  - [5.2 The extension property](#52-the-extension-property)
  - [5.3 Uniqueness within the direct presentation](#53-uniqueness-within-the-direct-presentation)
- [6. Properness from the direct toric obstruction](#6-properness-from-the-direct-toric-obstruction)
  - [6.1 Raynaud degeneration and the rank obstruction](#61-raynaud-degeneration-and-the-rank-obstruction)
  - [6.2 The positive toric complex structure](#62-the-positive-toric-complex-structure)
  - [6.3 Auxiliary level and actual good reduction](#63-auxiliary-level-and-actual-good-reduction)
  - [6.4 Flat-closure projectivity](#64-flat-closure-projectivity)
- [7. Levels, quotients, and scalar extension](#7-levels-quotients-and-scalar-extension)
  - [7.1 Fine level changes](#71-fine-level-changes)
  - [7.2 Stack and coarse levels](#72-stack-and-coarse-levels)
  - [7.3 Base change](#73-base-change)
- [8. Prime-to-residue-characteristic Hecke correspondences](#8-prime-to-residue-characteristic-hecke-correspondences)
  - [8.1 Integral correspondence and universal isogeny](#81-integral-correspondence-and-universal-isogeny)
  - [8.2 Composition, adjoints, and component routes](#82-composition-adjoints-and-component-routes)
- [9. Smooth proper comparison](#9-smooth-proper-comparison)
  - [9.1 Finite and adic coefficients](#91-finite-and-adic-coefficients)
  - [9.2 Coefficient systems from the universal abelian scheme](#92-coefficient-systems-from-the-universal-abelian-scheme)
  - [9.3 Hecke-equivariant specialization](#93-hecke-equivariant-specialization)
  - [9.4 Frobenius and unramifiedness](#94-frobenius-and-unramifiedness)
- [10. Coherent and de Rham lattices](#10-coherent-and-de-rham-lattices)
  - [10.1 Coherent base change](#101-coherent-base-change)
  - [10.2 The Hodge bundle and Kodaira--Spencer line](#102-the-hodge-bundle-and-kodaira--spencer-line)
  - [10.3 Degree-one de Rham comparison](#103-degree-one-de-rham-comparison)
- [11. The dyadic and bad-level boundary](#11-the-dyadic-and-bad-level-boundary)
  - [11.1 What the torus argument still proves](#111-what-the-torus-argument-still-proves)
  - [11.2 What remains unproved at two](#112-what-remains-unproved-at-two)
  - [11.3 Parahoric level](#113-parahoric-level)
- [12. The good integral-model theorem](#12-the-good-integral-model-theorem)
  - [12.1 Statement](#121-statement)
  - [12.2 Proof architecture](#122-proof-architecture)
  - [12.3 Conclusion](#123-conclusion)

## 1. The good-reduction problem

The canonical model of a compact quaternionic Shimura curve is defined over its reflex field, but that fact alone does not produce the integral geometry needed at a finite place. A useful model must represent the exact PEL problem, carry its universal abelian scheme, extend prime-to-residue-characteristic correspondences, and have a special fiber as regular as the generic fiber. This book constructs that package for the direct quaternion-trace realization at the verified odd hyperspecial places.

Smoothness and properness have different proofs. The ambient determinant scheme is first shown smooth by an exact integral local-model calculation. Properness is proved separately for the schematic flat closure of the selected generic component union. In the latter argument a hypothetical semiabelian degeneration has a Raynaud torus whose rational cocharacters form a unital left module over the division quaternion algebra. Such a module is already too large to occur inside the direct rational homology. Keeping the two proofs separate prevents generic compactness from being mistaken for integral properness and prevents ambient flatness from being assumed in the boundary argument.

### 1.1 The fixed direct-trace curve

Let $F$ be totally real and let $B/F$ be a quaternion division algebra split at exactly one real place. Its adjoint group is

$$
G^{\mathrm{ad}}=\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B).
$$

The only faithful realization used here is the direct quaternion-trace datum of Book 127:

$$
D=V=B,
$$

with left $B$-action and alternating form

$$
\psi_\delta(x,y)=\operatorname{Tr}_{F/\mathbf Q}
\operatorname{Trd}_B(x\bar y\delta),
\qquad \bar\delta=-\delta,                                  \tag{1.1}
$$

where $\delta$ is chosen so that $b^*=\delta^{-1}\bar b\delta$ is positive and the Hodge map lifts to the similitude group. The selected determinant and orientation data leave one active rank-two alternating multiplicity plane. Its Hodge line is the single deformation direction, so the parameter scheme is a curve even though the universal abelian scheme can have much larger relative dimension.

All uniqueness, extension, universal-family, and coefficient-system statements below are typed to this direct presentation. No comparison with another faithful realization of the same adjoint datum is asserted.

### 1.2 Conventions and the meaning of good

Let $E$ be the reflex field, let $v\mid p$ be a finite place, and put

$$
R=\mathcal O_{E,v},\qquad k=k(v).
$$

The completion is denoted $E_v$ on the generic side. Chosen separable closures and a geometric specialization are written $\bar E_v\rightsquigarrow\bar k$. A trait is the spectrum of a discrete valuation ring. A level is $K=K_pK^p$, with $K_p$ the integral stabilizer at $p$.

A **good place in this book** satisfies all of the following:

1. $p$ is odd and $F$ is unramified at $p$;
2. $B$ is split at every place of $F$ above $p$;
3. the acting order is maximal and involution-stable at $p$;
4. the alternating lattice is self-dual and its similitude stabilizer is reductive;
5. the polarization degree is a unit in $R$;
6. the determinant polynomial, multiplier component, and orientation label extend over $R$; and
7. the chosen generic component union is stable under the decomposition group at $v$.

Thus $K_p=G_{\mathbf Z_p}(\mathbf Z_p)$ is hyperspecial. These are integral conditions on the exact datum, not consequences of rational unramifiedness alone.

Arithmetic reciprocity sends a uniformizer to arithmetic Frobenius. Geometric Frobenius is its inverse. Pullback makes cohomology contravariant, and a finite proper correspondence acts by pullback along its first leg followed by trace along its second.

### 1.3 Dependency ledger

Book 127 supplies the direct rational PEL datum, the selected generic canonical component union, its characteristic-zero Hodge chart, levels, and universal family. Book 60 supplies Grothendieck--Messing and Serre--Tate deformation theory. Book 40 supplies potential semistable reduction, Raynaud one-motives and their functorial filtration, the positive monodromy pairing, the congruence lemma, and the good-reduction criterion. Book 38 supplies abelian quotients and extension of homomorphisms and polarizations. Books 15, 18, and 22 supply coherent base change, formal algebraization with an ample line, and prime-to-residue-characteristic proper and smooth base change, respectively.

The exact direct dependency row is

$$
\boxed{130\mid 15,18,22,38,40,60,127}.                       \tag{1.2}
$$

There are seven direct dependencies. Every other assertion used below is proved in this book.

## 2. Good integral PEL data

### 2.1 Orders, lattices, and hyperspecial level

Let $\mathcal O\subset B$ be the fixed $*$-stable order and $\Lambda\subset V$ the fixed $\mathcal O$-stable lattice. After the global normalization already made in the direct datum, assume that (1.1) is integral and perfect on $\Lambda\otimes\mathbf Z_p$. For a $\mathbf Z_p$-algebra $S$, set

$$
G_{\mathbf Z_p}(S)=
\left\{g\in\operatorname{GL}_{\mathcal O\otimes S}(\Lambda\otimes S):
\psi_\delta(gx,gy)=\nu(g)\psi_\delta(x,y),
\nu(g)\in S^\times\right\}.                                \tag{2.1}
$$

At a good place this is a smooth reductive group scheme and

$$
K_p=G_{\mathbf Z_p}(\mathbf Z_p).
$$

Self-duality has two independent roles. It makes the polarization pairing perfect on de Rham homology, so isotropic direct summands lift cleanly, and it makes the stabilizer reductive. Replacing $\Lambda_p=\Lambda_p^\vee$ by a finite-index inclusion normally changes the stabilizer to a parahoric group and changes the local model.

### 2.2 The active quaternionic packet

For each $w\mid p$, goodness gives

$$
B_w\simeq M_2(F_w),\qquad
\mathcal O_w\simeq M_2(\mathcal O_{F_w}),
$$

with $F_w/\mathbf Q_p$ unramified. Passing to a full matrix idempotent removes the Azumaya factor. The unique moving packet becomes a free rank-two module $U$ with a perfect alternating form.

**Proposition 2.1 (the active integral plane).** After an unramified splitting extension, the active reduced lattice admits a symplectic basis, and every stable Hodge summand of the prescribed determinant type is obtained from a line direct summand $L\subset U$. Every such line is isotropic. All inactive packets are forced by their determinant and orientation labels.

**Proof.** Choose a primitive $e\in U$. Perfectness supplies $f$ for which $\langle e,f\rangle$ is a unit; rescale $f$ so that this value is $1$. Alternation gives zero diagonal entries, hence $(e,f)$ is symplectic. Morita equivalence identifies modules stable under the full matrix order with modules induced from the multiplicity plane. The determinant law has rank one on the active plane and rank zero or full rank on every inactive factor. Finally every line in an alternating plane is isotropic. $\square$

The proposition is stronger than a characteristic-zero dimension count: it identifies the integral lattice genus and the functor on rings with nilpotents.

### 2.3 The determinant law and orientation

For $b\in\mathcal O$, let $P_b(T)$ be the characteristic polynomial prescribed by the Hodge cocharacter. Goodness requires $P_b(T)\in R[T]$ compatibly as one polynomial law on $\mathcal O$. For an abelian scheme $A/S$, impose

$$
\det\!\left(T-\iota(b)\mid\operatorname{Lie}(A/S)\right)
=P_b(T).                                                       \tag{2.2}
$$

It is not enough to check (2.2) separately on a basis of $\mathcal O$: one imposes it on the universal linear combination of the basis elements so that all mixed coefficients agree. In this form the condition is closed and commutes with arbitrary base change.

The convention is fixed by the homological Hodge sequence

$$
0\longrightarrow\omega_{A^\vee}
\longrightarrow H_{1,\mathrm{dR}}(A/S)
\longrightarrow\operatorname{Lie}(A/S)\longrightarrow0.     \tag{2.3}
$$

The determinant law selects the ranks on the quotient in (2.3). The orientation is additional open-and-closed data selecting the direct packet; it is not implied by lattice isometry.

### 2.4 The exact hypothesis ledger

Fix $K^p\subset G(\mathbf A_f^p)$ and put $K=K_pK^p$. The construction uses this ledger:

- the rational PEL realization is exactly $D=V=B$ from Book 127, with $B$ division and split at one real place;
- the selected generic fine PEL component union has been identified with its canonical model over $E$;
- $K^p$ is neat, or a full level $N\ge3$ with $(N,p\deg\lambda)=1$ is imposed;
- every item in Section 1.2 holds for the order, lattice, polarization, determinant, multiplier, and orientation;
- the local model is formed from the single active plane of Proposition 2.1;
- a self-correspondence is claimed only for a Hecke double coset preserving the selected union; on the full canonical component union every prime-to-$p$ double coset is allowed; and
- $B$ is division, which is the hypothesis used in the toric-rank obstruction.

One first represents the ambient determinant-and-orientation functor. If a selected generic union is not already cut out by an integral idempotent, its integral model initially means its schematic flat closure. A single geometric component need not descend to $R$; one uses a decomposition-group-stable union or extends the reflex local ring to its component field.

## 3. The integral PEL functor and its flat closure

### 3.1 Objects and arrows

For an $R$-scheme $S$, an object is

$$
(A,\iota,\lambda,\bar\eta^p),                                \tag{3.1}
$$

where:

- $A/S$ is an abelian scheme of the dimension fixed by $V=B$;
- $\iota:\mathcal O\to\operatorname{End}_S(A)$ is an action;
- $\lambda:A\to A^\vee$ is a polarization of the fixed prime-to-$p$ type and satisfies $\lambda\iota(b)=\iota(b^*)^\vee\lambda$;
- $\bar\eta^p$ is the prescribed $K^p$-orbit of prime-to-$p$ adelic trivializations respecting the action and pairing up to the common multiplier; and
- the Lie action satisfies (2.2), including the multiplier component and direct orientation.

Arrows are isomorphisms preserving every structure. Quasi-isogenies are not arrows; they enter only in Hecke correspondences. At full level $N$ prime to $p\deg\lambda$, the level is an actual symplectic $\mathcal O/N\mathcal O$-linear trivialization of the finite étale group $A[N]$.

Descent is effective for the fppf topology. Abelian schemes, homomorphisms, polarizations, and finite étale levels descend, while the Rosati and determinant identities descend as equalities of morphisms. At neat level the sheaf of isomorphism classes is set-valued.

### 3.2 Representability and the universal family

**Theorem 3.1 (ambient representability).** Under Section 2.4, without assuming flatness, smoothness, or properness, the full fine integral PEL functor is represented by a quasi-projective $R$-scheme $\mathscr M_K^{\mathrm{amb}}$ of finite presentation. It carries a universal tuple

$$
(\mathcal A,\iota^{\mathrm{univ}},\lambda^{\mathrm{univ}},
\bar\eta^{p,\mathrm{univ}}).                                 \tag{3.2}
$$

Every integral open-and-closed determinant, multiplier, or orientation condition cuts out the corresponding open-and-closed subscheme.

**Proof.** Use a sufficiently high tensor power of an ample bundle inducing a fixed multiple of the polarization to embed every object in one Hilbert scheme. The group law and the action of a finite basis of $\mathcal O$ are closed conditions; the multiplication table, Rosati identity, and universal version of (2.2) are closed equations. The level is represented by a finite étale isomorphism scheme. Forgetting the action to a rigid Siegel problem is finite: rigidity gives quasi-finiteness, the Rosati norm bounds the possible actions, and extension of homomorphisms over a DVR gives properness. A finite algebraic space over a scheme is a scheme. Full level at least three kills automorphisms, and a neat level is a free finite quotient of a principal-level scheme. The identity morphism gives (3.2) by Yoneda. $\square$

Representability does not exclude vertical components of the determinant locus.

### 3.3 Generic comparison and schematic flat closure

Over $E$, the integral order and lattice recover the rational direct datum and $K_p$. Let $\mathscr M_{K,E}^{\mathrm{sel}}$ be the decomposition-stable union selected by the lattice genus, multiplier component, and orientation. Book 127 gives

$$
\mathscr M_{K,E}^{\mathrm{sel}}
\simeq\operatorname{Sh}_K(G,X)^{\mathrm{sel}}                 \tag{3.3}
$$

over $E$, with the same universal PEL abelian variety. Define

$$
\mathscr M_K^{\mathrm{fl}}
=\overline{\mathscr M_{K,E}^{\mathrm{sel}}}^{\,\mathrm{sch}}
\subset\mathscr M_K^{\mathrm{amb}}.                          \tag{3.4}
$$

Affine-locally, its coordinate ring is the image of the ambient ring in its localization at a uniformizer. It is therefore $R$-torsion-free, hence flat, and its generic fiber is (3.3). This formal construction does not prove smoothness or properness. The universal tuple restricts to (3.4).

## 4. The good odd local model

### 4.1 Integral filtration lifting

**Proposition 4.1 (PEL filtration lifting).** Let $S_0\hookrightarrow S$ be a square-zero thickening of local Artinian $R$-schemes and let a direct-trace PEL object be given over $S_0$. If $p$ is nilpotent on $S$, deformations are classified on a divided-power enlargement by direct-summand lifts of the Hodge filtration in the evaluated Dieudonne crystal, with the descent datum of Book 60. The action lifts exactly when the filtration is $\mathcal O$-stable, and the prime-to-$p$ polarization lifts exactly when it is isotropic for the evaluated perfect alternating form. Prime-to-$p$ level lifts uniquely. If $p$ is invertible on $S$, the characteristic-zero Hodge chart gives the same conclusion. Thus the framed PEL deformation functor is formally smooth over the completed stable-isotropic flag functor.

**Proof.** When $p$ is nilpotent, Grothendieck--Messing classifies lifts of the $p$-divisible group by filtration lifts on a divided-power evaluation. Serre--Tate reconstructs the abelian scheme and supplies descent to the original thickening. Morphisms in those classifications give precisely stability for the action and isotropy for the polarization; positivity persists through a nilpotent thickening. When $p$ is invertible, Book 127 identifies the completed PEL problem with its Hodge chart. Since $S$ is local Artinian, these two cases exhaust the possibilities. $\square$

The statement deliberately uses a divided-power evaluation when necessary; it does not postulate a canonical crystal evaluation on an arbitrary non-divided-power thickening.

### 4.2 The framed local-model diagram

Let $\widetilde{\mathscr M}_K^{\mathrm{amb}}$ classify an ambient PEL object together with an $\mathcal O\otimes R$-linear symplectic frame of its de Rham homology by $\Lambda\otimes R$. There is a diagram

$$
\mathscr M_K^{\mathrm{amb}}
\xleftarrow{\ \pi\ }
\widetilde{\mathscr M}_K^{\mathrm{amb}}
\xrightarrow{\ \varphi\ }M^{\mathrm{loc}}.                  \tag{4.1}
$$

The map $\pi$ is a torsor under the smooth group $G_R$. The map $\varphi$ records the framed Hodge subbundle and is smooth by Proposition 4.1. Finite presentation converts formal smoothness into smoothness. Hence $\mathscr M_K^{\mathrm{amb}}$ and $M^{\mathrm{loc}}$ have the same completed local singularities up to formally smooth variables.

Local nonemptiness of the frame torsor is part of the integral calculation: Proposition 2.1 identifies the active lattice, while the order, perfect polarization, determinant ranks, and orientation fix all other packets. The determinant polynomial alone would not establish the torsor statement.

### 4.3 The projective-line calculation

After an unramified etale splitting extension $R'/R$, the active part of $\Lambda\otimes R'$ is $W\otimes U$, where $W$ is the fixed simple matrix module and $U$ is the alternating plane of Proposition 2.1. A stable Hodge submodule is $W\otimes L$ for a line $L\subset U$, and every line is isotropic. Therefore

$$
M^{\mathrm{loc}}_{R'}\simeq\mathbf P(U)\simeq\mathbf P^1_{R'}. \tag{4.2}
$$

All inactive packets are fixed. At $L$, the tangent module is

$$
\operatorname{Hom}(L,U/L),                                   \tag{4.3}
$$

which is free of rank one. Descent gives a smooth projective $R$-form of this flag scheme. Equation (4.2) is an equality of the actual integral local-model functor, not merely of its generic fiber.

## 5. Smoothness and extension

### 5.1 Smoothness and the selected component union

**Theorem 5.1 (smoothness).** The ambient morphism

$$
\mathscr M_K^{\mathrm{amb}}\longrightarrow\operatorname{Spec}R
$$

is smooth of relative dimension one.

**Proof.** In (4.1), $\pi$ is smooth and surjective, $\varphi$ is smooth, and the local model is smooth over $R$ by (4.2). Smoothness descends through $\pi$. The frame directions occur on both sides, so the relative tangent direction is (4.3). $\square$

Thus the ambient scheme is regular and flat, with reduced smooth geometric fibers. In a regular noetherian scheme the irreducible components are disjoint and open. Every component dominates $R$, so the schematic closure (3.4) of a union of generic components is exactly the corresponding union of ambient components. Consequently

$$
\mathscr M_K^{\mathrm{fl}}\subset\mathscr M_K^{\mathrm{amb}}
$$

is open and closed, smooth of relative dimension one, and represents the restricted integral subfunctor. From now on write

$$
\mathscr M_K=\mathscr M_K^{\mathrm{fl}}.                      \tag{5.1}
$$

This does not identify $\mathscr M_K$ with the whole ambient scheme unless the selected generic union is the entire ambient generic fiber.

### 5.2 The extension property

Call an $R$-scheme $S$ **healthy regular** if it is regular and flat and every abelian scheme on an open containing the generic fiber and all codimension-one points extends uniquely over $S$. Healthiness is retained as a hypothesis rather than inferred from smoothness.

**Theorem 5.2 (extension property).** Let $S$ be healthy regular and flat over $R$. Restriction gives a bijection

$$
\operatorname{Hom}_R(S,\mathscr M_K)
\xrightarrow{\sim}
\operatorname{Hom}_E(S_E,\mathscr M_{K,E})                   \tag{5.2}
$$

provided the generic PEL abelian scheme has good reduction at every codimension-one point of $S$.

**Proof.** Good reduction extends the generic abelian scheme over each codimension-one DVR. Rigidity makes the extensions agree on overlaps, and healthiness extends their union to an abelian scheme $A/S$. Book 38 extends the action and polarization homomorphism uniquely over the normal base. The prime-to-$p$ kernel type and positivity persist. The scheme of level trivializations is finite etale; its generic section extends at codimension one, and its finite birational closure over normal $S$ is $S$. The finite etale orientation extends in the same way. Rosati and determinant identities hold by density. The resulting map to the ambient scheme factors through its open-and-closed selected union because $S_E$ is dense in every component of $S$. Separatedness gives uniqueness. $\square$

Chapter 6 removes the good-reduction qualification for the final curve model.

### 5.3 Uniqueness within the direct presentation

Suppose $\mathscr X$ and $\mathscr Y$ are smooth $R$-models of the same direct PEL generic fiber, their generic identity identifies the universal PEL abelian schemes, and both satisfy the extension property. Apply the proof of Theorem 5.2 to the universal family already living on $\mathscr X$ to extend the generic identity to $\mathscr X\to\mathscr Y$; reverse the roles to obtain $\mathscr Y\to\mathscr X$. The composites are generically the identity and hence are the identity by separatedness. Thus the isomorphism is unique.

No general healthiness theorem is needed in this comparison because the relevant abelian schemes already exist over both test models. The argument does not compare different PEL presentations.

## 6. Properness from the direct toric obstruction

### 6.1 Raynaud degeneration and the rank obstruction

Let $V_0$ be a henselian DVR over $R$ with fraction field $L$, and let $A_L$ be the abelian variety supplied by a generic point of $\mathscr M_K$. After a finite separable extension and normalization, Book 40 gives semistable reduction with connected special fiber

$$
0\longrightarrow T\longrightarrow G_s\longrightarrow A_0
\longrightarrow0.                                            \tag{6.1}
$$

Every PEL endomorphism and the polarization homomorphism acts functorially on the Raynaud data. In particular

$$
X_T=X_*(T)\otimes_{\mathbf Z}\mathbf Q                       \tag{6.2}
$$

is a unital left $B$-module, and $\dim_{\mathbf Q}X_T$ is the toric rank. Since $B$ is a division algebra, every nonzero unital left $B$-module has rational dimension at least $\dim_{\mathbf Q}B$. But

$$
g=\dim A_L=\frac12\dim_{\mathbf Q}V
=\frac12\dim_{\mathbf Q}B,
$$

and the toric rank is at most $g$. Therefore $X_T\ne0$ would imply

$$
2g\le \dim_{\mathbf Q}X_T\le g,
$$

a contradiction. Hence $T=0$, and every direct-trace degeneration has potential good reduction.

This argument is internal to $D=V=B$. It neither chooses coefficient-dependent subspaces of $V$ nor compares faithful realizations.

For later compatibility, the corresponding prime-to-$p$ filtration is also explicit. If $M_A=[Y_A\to G]$ is the Raynaud one-motive, then for $\ell\ne p$,

$$
0\subset W_{-2,\ell}\subset W_{-1,\ell}
\subset T_\ell A\otimes\mathbf Q_\ell,
\qquad
W_{-2,\ell}=X_*(T)\otimes\mathbf Q_\ell(1),                 \tag{6.3}
$$

and the filtration is stable under $B\otimes\mathbf Q_\ell$. The polarization annihilates $W_{-2,\ell}$ with itself and identifies $W_{-1,\ell}$ with its orthogonal complement.

### 6.2 The positive toric complex structure

The short rank proof has a polarized refinement which fixes the action variance and Hodge convention. Put

$$
X=X_*(T)_{\mathbf Q},\qquad Y=Y_A\otimes\mathbf Q.
$$

Let $e_\lambda:X\times Y\to\mathbf Q$ be the perfect outer pairing and let $\nu:Y\xrightarrow{\sim}X$ be the rational tropical map. The covariant left actions satisfy

$$
e_\lambda(bx,y)=e_\lambda(x,b^*y),\qquad
\nu(by)=b\nu(y).                                              \tag{6.4}
$$

On $H_T=X\oplus Y$, define

$$
\psi_T((x,y),(x',y'))
=e_\lambda(x,y')-e_\lambda(x',y),                            \tag{6.5}
$$

and, writing $q_\lambda(z,z')=e_\lambda(\nu z,z')$ for the positive symmetric monodromy form, define

$$
J_T(\nu z,y)=(-\nu y,z).                                     \tag{6.6}
$$

Then $J_T^2=-1$, it commutes with $B$, and

$$
\psi_T((\nu z,y),J_T(\nu z,y))
=q_\lambda(z,z)+q_\lambda(y,y)>0.                           \tag{6.7}
$$

Its $i$-eigenspace is

$$
H_T^{i}=\{(\nu z,-iz):z\in Y_{\mathbf C}\}
\simeq Y_{\mathbf C}.                                       \tag{6.8}
$$

Thus, in the convention selecting $H_T^{i}$, the toric determinant contribution at a complex packet $\tau$ is

$$
P^T_{b,\tau}(T)=\det(T-b\mid Y_\tau),                        \tag{6.9}
$$

with the conjugate packet used under the opposite quotient convention.

**Proof.** Functoriality of the Raynaud extension gives the covariant actions and the second identity in (6.4); polarization gives the first. Direct substitution proves (6.7), applying (6.6) twice gives $J_T^2=-1$, and

$$
J_T(b\nu z,by)=(-\nu(by),bz)=b(-\nu y,z)
$$

proves commutation with $B$. Solving $J_T(x,y)=i(x,y)$ gives (6.8), and differentiating cocharacters gives (6.9). $\square$

If $X\ne0$, the polarized block $X\oplus Y$ has dimension at least $2\dim_{\mathbf Q}B$, while all of $V$ has dimension $\dim_{\mathbf Q}B$. This is the positive-Hodge version of the same exclusion; it is recorded to preserve the determinant convention, not used to compare presentations.

### 6.3 Auxiliary level and actual good reduction

Potential good reduction need not descend automatically to the original trait. First pass to a normal principal-level cover contained in $K^p$ and divisible by an odd auxiliary prime $q\ne p$ chosen away from $\deg\lambda$ and the fixed bad set. Full level trivializes $A[q]$. Over an extension where good reduction exists, $T_qA$ is unramified, so inertia over $L$ has finite image. That image lies in the principal congruence kernel

$$
\ker\bigl(\operatorname{GL}(T_qA)\to\operatorname{GL}(A[q])\bigr).
$$

For odd $q$, Book 40's congruence lemma says this kernel has no nontrivial finite-order element. Inertia is therefore trivial, and the Neron--Ogg--Shafarevich criterion gives good reduction over the original henselian DVR. Completion and faithfully flat descent preserve the conclusion.

At an arbitrary neat fine level, one does not infer trivial inertia from an adelic orbit. Instead properness is first proved on the normal auxiliary-level cover. Its finite map to the neat flat closure is surjective because its closed image contains the whole selected generic union. Properness descends through that finite surjection. Pulling back the universal family along the valuative extension of a neat-level point then gives actual good reduction. At a non-neat coarse level, the base point can extend without a universal abelian scheme; no objectwise claim is made without a stack lift.

Once $A$ extends, Book 38 extends endomorphisms and the polarization homomorphism uniquely. Prime-to-$p$ torsion and level are finite etale, the determinant identity extends coefficientwise on $\operatorname{Lie}A$, and the orientation label cannot jump. An inducing ample line is not required merely to extend the polarization homomorphism.

### 6.4 Flat-closure projectivity

**Theorem 6.1 (properness and projectivity).** At every good odd place, the selected flat closure $\mathscr M_K$ is proper and projective over $R$. Combined with Chapter 5, it is the desired smooth projective fine integral PEL curve.

**Proof.** Work first at the normal full level used in Section 6.3. Embed the quasi-projective flat closure in its scheme-theoretic closure inside a projective space over $R$. The generic fiber is already closed because the compact quaternionic curve is proper. If a vertical boundary point remained, noetherian trait selection would give a mixed-characteristic DVR whose generic point lies in the PEL locus and whose closed point lies on the boundary. After completion, Sections 6.1 and 6.3 extend the entire PEL object over the original DVR. Every generic equation of the selected union vanishes in this torsion-free DVR, so the extension factors through the schematic flat closure. Separatedness of the projective closure contradicts the chosen boundary specialization. Thus the full-level flat closure equals its projective closure.

For a neat level, choose a normal full-level subgroup. Its finite map is surjective onto the selected flat closure, hence properness descends. A proper quasi-projective scheme over $R$ is projective. The open-and-closed smooth identification is independent of this argument and was proved in Section 5.1. $\square$

The final model therefore satisfies Theorem 5.2 without an extra good-reduction qualification and is unique as in Section 5.3. This is the precise integral-canonical property used later.

## 7. Levels, quotients, and scalar extension

### 7.1 Fine level changes

For neat $K_1^p\subset K_2^p$ with common $K_p$, forgetting part of the level gives

$$
f_{12}:\mathscr M_{K_pK_1^p}\longrightarrow
\mathscr M_{K_pK_2^p}.                                      \tag{7.1}
$$

This map is finite because refinements of a fixed prime-to-$p$ level form a finite etale isomorphism scheme. It is etale because finite etale level has unique infinitesimal deformation. If $K_1^p$ is normal in $K_2^p$, the effective deck group is the quotient of $K_2^p/K_1^p$ by central elements acting trivially on the moduli problem; at neat target level, (7.1) is its finite etale torsor.

### 7.2 Stack and coarse levels

At a level with stabilizers, choose a normal fine subgroup with effective deck group $\Delta$. The natural object is

$$
\mathscr M_{K_2}\simeq[\mathscr M_{K_1}/\Delta].             \tag{7.2}
$$

It is smooth and proper because these properties descend from the finite etale fine atlas. The coarse scheme can have quotient singularities at fixed points. The universal abelian scheme descends to the stack through its genuine PEL linearization. It descends to the coarse scheme exactly when every stabilizer acts trivially on the complete PEL object; a scalar such as $-1$ usually prevents this.

### 7.3 Base change

For an unramified extension $R\to R'$ compatible with a place above $v$, every ingredient commutes with base change and

$$
\mathscr M_K\otimes_RR'\simeq\mathscr M_{K,R'}.              \tag{7.3}
$$

The universal family, Hodge bundle, polarization, and prime-to-$p$ level pull back. Smoothness and properness persist. A ramified scalar extension of an already good model is still smooth, but it need not equal a new moduli problem built from a changed order or lattice chain; equality requires the entire integral datum to be pulled back.

## 8. Prime-to-residue-characteristic Hecke correspondences

### 8.1 Integral correspondence and universal isogeny

Let $g\in G(\mathbf A_f^p)$ and set

$$
K_g^p=K^p\cap gK^pg^{-1}.
$$

On the full selected component union there is a diagram

$$
\mathscr M_K
\xleftarrow{\ p_1\ }
\mathscr M_{K_pK_g^p}
\xrightarrow{\ p_2\ }
\mathscr M_K.                                                 \tag{8.1}
$$

For a smaller union, the right target is its Hecke translate unless $g$ preserves it. Both legs are finite etale by Chapter 7.

On the middle generic fiber there is a universal prime-to-$p$ quasi-isogeny $u_g$ satisfying

$$
u_g^\vee\lambda_2u_g=c_g\lambda_1,
\qquad c_g\in\mathbf Q_{>0}.                                \tag{8.2}
$$

Choose one positive integer $m_g$, prime to $p$, clearing the denominators of $u_g$, $u_g^{-1}$, and $c_g$ in the fixed integral lattices. The kernel of $m_gu_g$ on the generic fiber is then finite etale of order prime to $p$. Its schematic closure in the corresponding torsion group of the universal abelian scheme is finite etale. Quotienting by it and using Book 38 extends $m_gu_g$ as an isogeny on the integral middle model, with (8.2) after the same normalization. This construction records denominators; the unscaled quasi-isogeny need not be an integral morphism.

Conversely, a finite locally free $\mathcal O$-stable isotropic prime-to-$p$ kernel has an abelian quotient, and the appropriate multiple of the polarization descends. The quotient has the same $p$-divisible group, so it does not change the local deformation problem.

### 8.2 Composition, adjoints, and component routes

Composition of Hecke correspondences follows from fiber products of level refinements and composition of their normalized isogenies. Equality of generic graphs implies equality integrally: the graphs are finite etale, hence $R$-flat, and their ideals in the separated product are $R$-saturated.

Rosati duality sends the correspondence for $g$ to the transpose correspondence for $g^{-1}$, with the scalar in (8.2). A self-correspondence on a smaller selected union exists exactly when the double coset preserves that union. Otherwise the same construction is a correspondence between the union and its translate; no endomorphism of the smaller cohomology group is silently inferred.

## 9. Smooth proper comparison

### 9.1 Finite and adic coefficients

Let $f:\mathscr M_K\to\operatorname{Spec}R$ be the smooth projective curve. For $\ell\ne p$ and $n\ge1$, smooth proper base change gives

$$
H^i(\mathscr M_{K,\bar k},\mathbf Z/\ell^n)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E_v},\mathbf Z/\ell^n).               \tag{9.1}
$$

For each fixed $n$ these cohomology groups are finite. Hence the inverse systems satisfy the
Mittag--Leffler condition: for fixed $n$, the images of all later terms form a descending chain
of subgroups of one finite group and therefore stabilize. Derived inverse limit has no hidden
$\varprojlim^1$ term, so

$$
H^i(\mathscr M_{K,\bar k},\mathbf Z_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E_v},\mathbf Z_\ell).                 \tag{9.2}
$$

This is an integral lattice comparison, including torsion, and it respects cup products. For a geometrically connected fiber of genus $g_C$,

$$
H^0=\mathbf Z_\ell,\qquad
\operatorname{rank}H^1=2g_C,\qquad
H^2=\mathbf Z_\ell(-1).                                     \tag{9.3}
$$

The arithmetic information used later lies in degree one.

### 9.2 Coefficient systems from the universal abelian scheme

Let $a:\mathcal A\to\mathscr M_K$ be the universal abelian scheme. For any abelian scheme over a base on which $\ell$ is invertible, the fiberwise character calculation gives

$$
R^ja_*\mathbf Z_\ell
\simeq\bigwedge^jR^1a_*\mathbf Z_\ell,
\qquad
R^1a_*\mathbf Z_\ell
\simeq\underline{\operatorname{Hom}}(T_\ell\mathcal A,
\mathbf Z_\ell).                                            \tag{9.4}
$$

For completeness, the absolute calculation follows from the cofinal tower of multiplication-by-$\ell^r$ covers. Translation acts trivially on finite etale cohomology, the Cartan--Leray complex becomes the continuous cohomology of $T_\ell A$, and its Koszul resolution is the exterior algebra on the character module. The construction is functorial and therefore preserves endomorphisms and the polarization pairing. Stalkwise proper base change turns it into (9.4) over the entire curve.

Write

$$
\mathbb V_\ell=R^1a_*\mathbf Z_\ell.
$$

It is finite free, commutes with arbitrary base change, carries the $\mathcal O$-action, and has the cohomological polarization pairing

$$
\mathbb V_\ell\otimes\mathbb V_\ell\longrightarrow
\mathbf Z_\ell(-1),
$$

perfect when $\ell\nmid\deg\lambda$. Tensor products, duals, exterior powers, and integral idempotent summands yield lisse coefficient systems $\mathcal L_\ell$. For each such system,

$$
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E_v},\mathcal L_\ell).               \tag{9.5}
$$

A projector with an $\ell$-denominator cuts out only a $\mathbf Q_\ell$-summand. It does not canonically produce an integral direct summand or repair a nonsaturated lattice.

### 9.3 Hecke-equivariant specialization

For (8.1) and a coefficient ring $\Lambda$, define

$$
T_g=(p_2)_*p_1^*.                                            \tag{9.6}
$$

For a coefficient system from $\mathcal A$, insert the morphism of the required variance induced by the normalized universal isogeny. It is an integral isomorphism on a $\mathbf Z_\ell$-system only when its degree is prime to $\ell$, although pull--push itself remains integral.

**Theorem 9.1 (Hecke-equivariant specialization).** If $g$ preserves the selected component union, then (9.5) commutes with $T_g$. On the full component union this holds for the full prime-to-$p$ Hecke algebra.

**Proof.** Proper base change is functorial for pullback and compatible with finite proper trace. The normalized isogeny is defined over the integral middle model, so its maps on coefficient systems have the same two fiber restrictions. Composition proves the claim at finite level and passage to the derived $\mathbf Z_\ell$-limit proves it adically. $\square$

A rational projector $d^{-1}P(T_{g_1},\ldots,T_{g_r})$ acts on the integral lattice only when the denominator is an $\ell$-adic unit and the projector preserves that lattice.

### 9.4 Frobenius and unramifiedness

The lisse sheaves $R^if_*\mathbf Z_\ell$ on the trait have trivial inertia. Hence the generic groups in (9.2) and (9.5) are unramified at $v$, including their torsion. Under specialization, arithmetic Frobenius matches arithmetic Frobenius, while geometric Frobenius matches its inverse convention on the local Galois side.

Good reduction does not by itself prove Frobenius semisimplicity or determine weights; those require separate input.

## 10. Coherent and de Rham lattices

### 10.1 Coherent base change

For a coherent $R$-flat sheaf $\mathcal F$ on the proper curve, each $R^if_*\mathcal F$ is finite. The obstruction to ordinary special-fiber base change is visible in

$$
0\longrightarrow H^i(\mathcal F)\otimes_Rk
\longrightarrow H^i(\mathcal F_k)
\longrightarrow H^{i+1}(\mathcal F)[\pi]
\longrightarrow0.                                           \tag{10.1}
$$

Thus proper smoothness does not make every coherent cohomology module torsion-free. For $\mathcal F=\mathcal O_{\mathscr M_K}$ and geometrically connected fibers,

$$
f_*\mathcal O_{\mathscr M_K}=R,
$$

and $R^1f_*\mathcal O_{\mathscr M_K}$ is finite locally free and commutes with arbitrary base change. Relative duality identifies its dual with $f_*\Omega^1_{\mathscr M_K/R}$.

### 10.2 The Hodge bundle and Kodaira--Spencer line

For the universal abelian scheme, the Hodge bundle

$$
\omega_{\mathcal A}=a_*\Omega^1_{\mathcal A/\mathscr M_K}
$$

is locally free and commutes with base change. The unramified order idempotents split it integrally. Let $\mathcal U$ be the active reduced rank-two bundle, let $\mathcal L\subset\mathcal U$ be its Hodge line, and put $\mathcal M=\det\mathcal U$ with its determinant-and-multiplier character.

Proposition 4.1 identifies an infinitesimal deformation with a unique map $\mathcal L\to\mathcal U/\mathcal L$. The frame directions in (4.1) are exactly the vertical directions of the torsor, so descent gives

$$
T_{\mathscr M_K/R}
\simeq\operatorname{Hom}(\mathcal L,\mathcal U/\mathcal L).
$$

Dualizing yields the integral Kodaira--Spencer isomorphism

$$
\Omega^1_{\mathscr M_K/R}
\simeq\mathcal L^{\otimes2}\otimes\mathcal M^{-1}.          \tag{10.2}
$$

No trivialization of $\mathcal M$ is implicit. Equation (10.2) is frame-change equivariant and commutes with unramified scalar extension and fine level change.

### 10.3 Degree-one de Rham comparison

The relative de Rham complex is perfect and commutes with derived base change. For this smooth proper curve, the Hodge-to-de Rham sequence gives

$$
0\longrightarrow f_*\Omega^1_{\mathscr M_K/R}
\longrightarrow H^1_{\mathrm{dR}}(\mathscr M_K/R)
\longrightarrow R^1f_*\mathcal O_{\mathscr M_K}
\longrightarrow0.                                           \tag{10.3}
$$

All three modules are finite locally free, so degree-one de Rham cohomology is an unconditional integral lattice and commutes with generic and special base change. Hecke correspondences act on the derived de Rham complex by pullback and trace and therefore act compatibly on (10.3).

The theorem on formal functions gives, for every coherent $\mathcal F$,

$$
H^i(\mathscr M_K,\mathcal F)
\widehat\otimes_R\widehat R
\xrightarrow{\sim}
\varprojlim_nH^i(\mathscr M_K\otimes_RR/\pi^{n+1},\mathcal F_n). \tag{10.4}
$$

At the derived level all Tor terms are retained. Conversely, a polarized formal abelian scheme algebraizes by Book 18 when a compatible formal ample line is supplied, possibly after fppf descent. A polarization homomorphism on the special fiber alone is not such an ample-line system.

## 11. The dyadic and bad-level boundary

### 11.1 What the torus argument still proves

The dimension contradiction in Section 6.1 and the positive block in Section 6.2 are rational arguments and do not use odd integral lattice classification. At a dyadic place they still exclude a Raynaud torus for the direct datum. Consequently, once an integral moduli functor and a suitable full auxiliary level are independently available, the same trait argument proves properness of its selected flat closure.

This is only a properness statement. It does not manufacture the missing dyadic ambient functor or prove that such a functor is smooth.

### 11.2 What remains unproved at two

Book 127 does not verify the complete residue-characteristic-two package for the direct order, self-dual lattice, determinant orientation, frame torsor, and local model. A perfect alternating plane itself has a symplectic basis at two, but that elementary fact does not identify the entire PEL deformation functor. Moreover, reducing a merely skew-symmetric matrix at two does not force its diagonal to vanish; alternation must be part of the integral datum rather than inferred after reduction.

The smooth theorem therefore remains odd. Extending it to two requires a separate verification of the exact order, lattice, polarization, determinant-and-orientation law, and framed local model. Properness must not be conflated with that missing smoothness input.

### 11.3 Parahoric level

If the lattice is not self-dual or the level at $p$ stabilizes a chain, the Hodge filtration must be compatible with several vertices. The local model can have multiple components and nodes. Kernels of $p$-isogenies need not be etale, so the construction of Chapter 8 no longer applies. Smooth proper base change is replaced by nearby cycles and monodromy. This is the exact boundary treated by the subsequent semistable theory.

## 12. The good integral-model theorem

### 12.1 Statement

**Theorem 12.1 (good integral models of quaternionic Shimura curves).** Let $B/F$ be a quaternion division algebra split at exactly one real place, and let

$$
\mathscr D=(B,*,B,\psi_\delta,h)
$$

be the direct quaternion-trace PEL realization of Book 127. Let $E$ be its reflex field, let $v\mid p$, and assume the exact ledger of Section 2.4, in particular that $p$ is odd, $F$ is unramified at $p$, $B$ is split at every place above $p$, the order is maximal and involution-stable, the alternating lattice is self-dual, the polarization degree is a unit, the stabilizer is reductive and hyperspecial, and all determinant, multiplier, orientation, level, and component labels extend over $R=\mathcal O_{E,v}$.

Then the schematic flat closure $\mathscr C_K$ of the selected generic canonical component union in the ambient fine PEL scheme is open and closed in that ambient scheme and is smooth and projective of relative dimension one over $R$. It represents the selected integral PEL subfunctor, carries the universal abelian scheme and all PEL tensors, satisfies the healthy-regular extension property, and is unique within the direct presentation. It commutes with unramified base change.

Every prime-to-$p$ level change is finite etale. Every prime-to-$p$ Hecke double coset extends on the full component union to a finite correspondence, and a common-denominator multiple of its universal quasi-isogeny extends as an isogeny. On a smaller selected union it is a self-correspondence exactly when it preserves that union; otherwise its target is the integral model of the Hecke translate.

For every $\ell\ne p$ and every integrally defined PEL coefficient system $\mathcal L_\ell$, geometric specialization gives

$$
H^i(\mathscr C_{K,\bar k},\mathcal L_\ell)
\xrightarrow{\sim}
H^i(\mathscr C_{K,\bar E_v},\mathcal L_\ell),                \tag{12.1}
$$

compatible with products, pairings, tensors, level change, Frobenius, and the stabilizer Hecke algebra. On the full union it is equivariant for the full prime-to-$p$ Hecke algebra. The generic representation is unramified at $v$. In degree one, coherent Hodge and de Rham lattices commute with base change as in (10.3).

At $p=2$, the toric obstruction and auxiliary-level trait argument still prove flat-closure properness once the exact integral moduli functor is independently provided. They do not prove ambient smoothness, so the smooth theorem makes no dyadic claim.

### 12.2 Proof architecture

The proof has a fixed order.

1. The integral tensors define the ambient fine PEL scheme and its universal family; the chosen generic canonical union defines the schematic flat closure.
2. The framed deformation diagram reduces completed moduli rings to the actual integral local model. Morita reduction leaves one alternating line, so the local model is a smooth projective line and the flat closure is an open-and-closed smooth component union.
3. Potential semistable reduction gives a Raynaud torus. Its rational cocharacters form a unital left $B$-module, whose minimum dimension contradicts the abelian dimension. The positive $J_T$ calculation records the same obstruction with the correct action and determinant convention.
4. Full odd auxiliary level kills the finite residual inertia and gives actual good reduction over the original trait. The projective-closure argument proves properness of the flat closure, and finite descent handles arbitrary neat level.
5. The extension property and uniqueness follow from extension of the universal abelian scheme and its tensors. Prime-to-$p$ level modifications extend Hecke isogenies. Smooth proper base change and functorial trace yield (12.1).

None of these arrows reverses without new hypotheses: generic compactness does not prove integral properness, smoothness does not prove projectivity, rational unramifiedness does not identify the dyadic local model, and rational Hecke equivariance does not control integral denominators.

### 12.3 Conclusion

At a verified good odd prime, the direct quaternion-trace curve has one and only one moving integral Hodge line. That line makes the local model smooth; the division algebra makes every nonzero Raynaud cocharacter module too large; auxiliary level turns potential good reduction into actual good reduction; and the flat-closure trait argument turns that boundary exclusion into projectivity.

The resulting model retains the structures needed by the FLT blueprint: the exact PEL functor, universal abelian scheme, integral Kodaira--Spencer line, prime-to-$p$ Hecke tower, integral etale coefficient systems, smooth proper specialization, Frobenius action, and degree-one coherent and de Rham lattices. The next geometric regime begins when the hyperspecial lattice is replaced by an Iwahori chain, producing nodal reduction and monodromy.
