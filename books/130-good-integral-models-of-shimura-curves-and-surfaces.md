# Good Integral Models of Shimura Curves and Surfaces

## Contents

- [1. The good-reduction problem](#1-the-good-reduction-problem)
  - [1.1 From a canonical model to arithmetic geometry](#11-from-a-canonical-model-to-arithmetic-geometry)
  - [1.2 The direct curve, the surface, and the dependency boundary](#12-the-direct-curve-the-surface-and-the-dependency-boundary)
  - [1.3 Conventions and the meaning of good](#13-conventions-and-the-meaning-of-good)
- [2. Good integral PEL data](#2-good-integral-pel-data)
  - [2.1 A local datum at a finite place](#21-a-local-datum-at-a-finite-place)
  - [2.2 Unramified centers, self-dual lattices, and hyperspecial level](#22-unramified-centers-self-dual-lattices-and-hyperspecial-level)
  - [2.3 The reflex ring and determinant law](#23-the-reflex-ring-and-determinant-law)
  - [2.4 A hypothesis ledger for curves and surfaces](#24-a-hypothesis-ledger-for-curves-and-surfaces)
- [3. The integral moduli functor](#3-the-integral-moduli-functor)
  - [3.1 Objects, arrows, and level away from the residue prime](#31-objects-arrows-and-level-away-from-the-residue-prime)
  - [3.2 Polarizations and the integral determinant condition](#32-polarizations-and-the-integral-determinant-condition)
  - [3.3 Representability and the universal family](#33-representability-and-the-universal-family)
  - [3.4 Generic-fiber comparison](#34-generic-fiber-comparison)
- [4. The good local model](#4-the-good-local-model)
  - [4.1 Why a determinant equation is not enough](#41-why-a-determinant-equation-is-not-enough)
  - [4.2 The framed local-model diagram](#42-the-framed-local-model-diagram)
  - [4.3 The direct quaternionic curve packet](#43-the-direct-quaternionic-curve-packet)
  - [4.4 The two unitary lines](#44-the-two-unitary-lines)
- [5. Smoothness and extension properties](#5-smoothness-and-extension-properties)
  - [5.1 Formal smoothness from filtration lifting](#51-formal-smoothness-from-filtration-lifting)
  - [5.2 Dimensions, regularity, and flatness](#52-dimensions-regularity-and-flatness)
  - [5.3 The extension property](#53-the-extension-property)
  - [5.4 Uniqueness of the good model](#54-uniqueness-of-the-good-model)
- [6. Properness in the compact cases](#6-properness-in-the-compact-cases)
  - [6.1 Flat closure and the valuative criterion](#61-flat-closure-and-the-valuative-criterion)
  - [6.2 Semiabelian degeneration and the direct toric obstruction](#62-semiabelian-degeneration-and-the-direct-toric-obstruction)
  - [6.3 Direct boundary exclusion](#63-direct-boundary-exclusion)
  - [6.4 Actual good reduction and properness](#64-actual-good-reduction-and-properness)
- [7. Fine levels, quotient levels, and base change](#7-fine-levels-quotient-levels-and-base-change)
  - [7.1 Change of prime-to-$p$ level](#71-change-of-prime-to-p-level)
  - [7.2 Finite étale covers and quotient stacks](#72-finite-étale-covers-and-quotient-stacks)
  - [7.3 Universal families at coarse level](#73-universal-families-at-coarse-level)
  - [7.4 Extension of scalars](#74-extension-of-scalars)
- [8. Prime-to-residue-characteristic Hecke correspondences](#8-prime-to-residue-characteristic-hecke-correspondences)
  - [8.1 Integral Hecke data](#81-integral-hecke-data)
  - [8.2 Quotients by finite étale kernels](#82-quotients-by-finite-étale-kernels)
  - [8.3 The correspondence and its universal isogeny](#83-the-correspondence-and-its-universal-isogeny)
  - [8.4 Composition, adjoints, and descent](#84-composition-adjoints-and-descent)
- [9. Étale cohomology of the good models](#9-étale-cohomology-of-the-good-models)
  - [9.1 Finite coefficients and specialization](#91-finite-coefficients-and-specialization)
  - [9.2 Integral adic lattices](#92-integral-adic-lattices)
  - [9.3 Abelian comparison and PEL coefficient systems](#93-abelian-comparison-and-pel-coefficient-systems)
  - [9.4 Unramifiedness and Frobenius](#94-unramifiedness-and-frobenius)
- [10. Hecke action and cohomological base change](#10-hecke-action-and-cohomological-base-change)
  - [10.1 Pull-push on a proper correspondence](#101-pull-push-on-a-proper-correspondence)
  - [10.2 Compatibility with specialization](#102-compatibility-with-specialization)
  - [10.3 Integral invertibility and denominators](#103-integral-invertibility-and-denominators)
  - [10.4 Curve and surface degrees](#104-curve-and-surface-degrees)
- [11. Coherent and de Rham comparison](#11-coherent-and-de-rham-comparison)
  - [11.1 Proper coherent cohomology](#111-proper-coherent-cohomology)
  - [11.2 The Hodge bundles of the universal family](#112-the-hodge-bundles-of-the-universal-family)
  - [11.3 De Rham lattices and the torsion warning](#113-de-rham-lattices-and-the-torsion-warning)
  - [11.4 Completion and formal comparison](#114-completion-and-formal-comparison)
- [12. The quaternionic curve model](#12-the-quaternionic-curve-model)
  - [12.1 Construction theorem](#121-construction-theorem)
  - [12.2 The integral Kodaira--Spencer line](#122-the-integral-kodaira--spencer-line)
  - [12.3 Cohomology and good reduction](#123-cohomology-and-good-reduction)
- [13. The unitary surface model](#13-the-unitary-surface-model)
  - [13.1 Construction theorem](#131-construction-theorem)
  - [13.2 Two tangent directions and canonical bundles](#132-two-tangent-directions-and-canonical-bundles)
  - [13.3 Middle cohomology and auxiliary abelian schemes](#133-middle-cohomology-and-auxiliary-abelian-schemes)
- [14. Integral comparison package](#14-integral-comparison-package)
  - [14.1 The geometric comparison theorem](#141-the-geometric-comparison-theorem)
  - [14.2 Functoriality for tensors and correspondences](#142-functoriality-for-tensors-and-correspondences)
  - [14.3 Fixed-presentation scope](#143-fixed-presentation-scope)
- [15. Failure modes and the good-prime boundary](#15-failure-modes-and-the-good-prime-boundary)
  - [15.1 Ramified orders and non-self-dual lattices](#151-ramified-orders-and-non-self-dual-lattices)
  - [15.2 Parahoric level and singular local models](#152-parahoric-level-and-singular-local-models)
  - [15.3 Bad reduction and monodromy](#153-bad-reduction-and-monodromy)
- [16. The good integral-model theorem](#16-the-good-integral-model-theorem)
  - [16.1 Unified statement](#161-unified-statement)
  - [16.2 Proof architecture](#162-proof-architecture)
  - [16.3 Conclusion](#163-conclusion)

## 1. The good-reduction problem

The complex points of a Shimura curve or surface are described by a double quotient, and its canonical model supplies a variety over a number field. Neither description answers the question asked at a finite prime: is there a model over the local ring whose special fiber is as regular as the generic fiber, and do the moduli objects and correspondences survive reduction? This book constructs smooth proper integral PEL models for the direct quaternion-trace curve and the standard unitary surface at the odd good primes specified below; unramified integral tensors and hyperspecial level are necessary parts of that ledger, not its whole content.

The delicate part is properness. It is not enough to know that the generic Shimura variety is compact. A hypothetical degeneration of its universal abelian variety has a Raynaud torus, and one must exclude that torus inside the actual faithful PEL representation. For the direct trace realization $D=V=B$, the cocharacter group of a nonzero Raynaud torus would be a nonzero unital left $B$-module, too large to fit inside an abelian variety with rational homology $B$. Section 6 also records the associated positive $J_T$-block, so the variance and determinant content of this short obstruction remain explicit. For the standard two-active-place unitary surface of Book 129, the recorded anisotropic finite Hermitian localization supplies a separate elementary boundary obstruction.

Properness and smoothness enter through different schemes. Book 127 first gives an ambient quasi-projective determinant scheme. Section 6 proves directly that the **schematic flat closure** of the selected generic component union inside that ambient scheme is projective; it does not assume that the ambient scheme is flat or that the closure is smooth. Chapters 4--5 independently use the exact odd unramified local model to prove ambient smoothness. Only then may the flat closure be identified with an open-and-closed smooth union of ambient components. Keeping this order prevents integral properness from being inferred from generic compactness and prevents ambient flatness from being smuggled into the boundary theorem.

### 1.1 From a canonical model to arithmetic geometry

Let $E$ be the reflex field and $v$ a finite place of $E$ above the rational prime $p$. If $X/E$ is a canonical Shimura curve or surface, a model $\mathscr X/\mathcal O_{E,v}$ is useful only if it carries more than the same function field. We require it to be smooth, to have the correct moduli interpretation, and, in the compact cases considered here, to be proper. At fine level it should carry an abelian scheme

$$
 a:\mathcal A\longrightarrow\mathscr X
$$

with its prescribed order action, polarization, determinant law, and level structure. Prime-to-$p$ Hecke maps should extend to finite correspondences and their generic universal quasi-isogenies should become genuine isogenies after an explicit common denominator is chosen.

These geometric demands have a cohomological purpose. For every prime $\ell\ne p$, smooth proper base change should identify the integral $\mathbf Z_\ell$-cohomology of a geometric generic fiber with that of a geometric special fiber. The identification must respect cup products, the PEL tensors, coefficient systems, and Hecke operators. It then follows that the generic Galois representation is unramified at $v$ and that arithmetic Frobenius may be computed on the special fiber.

There are three possible logical shortcuts, and all are wrong. A smooth generic fiber does not force a smooth integral closure. A proper generic fiber does not by itself make a chosen integral moduli scheme proper. Finally, comparison with $\mathbf Q_\ell$-coefficients does not automatically preserve a preferred $\mathbf Z_\ell$-lattice. Each issue receives a separate proof below.

### 1.2 The direct curve, the surface, and the dependency boundary

There are two fixed geometric constructions in scope.

For the curve, let $B/F$ be a quaternion division algebra split at exactly one real place and let

$$
G^{\mathrm{ad}}=\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B).
$$

The curve datum is the **direct quaternion trace realization** of Book 127: $D=V=B$ with its left $B$-action and alternating form

$$
\psi_\delta(x,y)=\operatorname{Tr}_{F/\mathbf Q}
\operatorname{Trd}_B(x\bar y\delta),
\qquad \bar\delta=-\delta,
$$

for a choice for which the induced involution $b^*=\delta^{-1}\bar b\delta$ is positive and the Hodge map lifts. Its active split packet is a single rank-two alternating multiplicity plane, so the fine generic PEL space is a curve. No other faithful PEL realization of the same adjoint datum is claimed here.

The second construction is the **standard unitary surface** of Book 129, Definition 4.1 and Proposition 4.2, assumed PEL-exact in the sense of its Definition 5.2. For that surface $D=K$, $V=W$ is a binary Hermitian space with two active signature-$(1,1)$ places and one recorded anisotropic finite localization. Its parameter space has dimension two. In both constructions the universal abelian scheme can have dimension much larger than the base.

The direct prerequisites have distinct jobs. Book 127 supplies the direct quaternion-trace PEL datum, ambient fine functor, generic canonical-model comparison, characteristic-zero Hodge chart, levels, and universal family. Book 129 supplies the standard surface tensors, determinant orientation, anisotropic finite localization, and generic surface. Book 60 supplies Grothendieck--Messing and Serre--Tate deformation theory. Book 40 supplies potential semistable reduction, the Raynaud one-motive and its functorial weight filtration, and the Néron--Ogg--Shafarevich criterion. Books 38, 15, 18, and 22 supply, respectively, abelian quotients and extension of homomorphisms and polarizations, coherent base change, formal algebraization with an ample line, and prime-to-residue-characteristic proper and smooth base change. The arbitrary-dimensional abelian Betti--étale calculation used to identify universal coefficient systems is proved directly in Section 9.3.

Accordingly the exact direct dependency row is

$$
\boxed{130\mid 15,18,22,38,40,60,127,129.}
$$

There are eight direct dependencies.

The direct curve needs no comparison among faithful presentations. Its boundary obstruction is internal to $D=V=B$: the Raynaud cocharacters carry the covariant left $B$-action, and their rank already forces the torus to vanish. Section 6.2 retains the positive toric complex structure $J_T$ and its determinant interpretation as an independent check on that argument.

The bad-prime geometry is not part of the present construction. A parahoric lattice chain, a non-self-dual lattice, or a semiabelian special fiber gives nearby cycles and monodromy rather than the constant specialization proved here. Those phenomena belong after the good model has been isolated.

### 1.3 Conventions and the meaning of good

All schemes are locally noetherian when coherent or infinitesimal arguments are used. Write $R=\mathcal O_{E,v}$, so $\operatorname{Frac}(R)=E$; write $E_v$ for the completion of $E$ at $v$ and $k=k(v)$. The symbols $\bar E$ and $\bar k$ denote separable algebraic closures together with a chosen geometric specialization $\bar E\rightsquigarrow\bar k$; when a local Galois action is discussed, we base change through $E\hookrightarrow E_v$ and write $\bar E_v$. The fraction field is always denoted by $E$; a subscript $K$ on a moduli space denotes the compact-open level $K=K_pK^p$. A trait means the spectrum of a discrete valuation ring.

A **good PEL place in this book** is odd. For the direct quaternion-trace curve, the center $F$ is unramified at $p$, $B$ is split at every place above $p$, the order is maximal and involution-stable, the alternating lattice is self-dual with its hyperspecial stabilizer, the polarization degree is a unit, and the determinant and orientation labels extend over $R$. For the standard unitary surface it satisfies the analogous order, lattice, polarization, hyperspecial, determinant, and orientation conditions of Chapters 2 and 6, and $p$ lies below no place in Book 129's recorded exceptional set. In both cases Chapter 4 proves that the actual local model is the expected smooth flag variety.

Books 127 and 129 place $2$ in their bad sets, and we retain that boundary. The direct torus-rank proof of potential good reduction does not use odd integral lattice classification, but it does not supply the missing dyadic ambient local model. A smooth dyadic model therefore remains outside the conclusions below unless the exact dyadic order, lattice, determinant-orientation, and local-model smoothness are independently verified. Properness of the direct flat closure may then be recovered by the same auxiliary-level trait argument; it must not be conflated with smoothness of the ambient determinant scheme.

Arithmetic reciprocity sends a uniformizer to arithmetic Frobenius. Geometric Frobenius is its inverse. Pullback makes cohomology contravariant; a finite proper correspondence acts by pullback along its first projection and trace along its second.

## 2. Good integral PEL data

An integral model is determined locally by lattices and tensors, not just by a rational reductive group. This chapter states the conditions that turn the generic PEL functor into a smooth moduli problem over $R$.

### 2.1 A local datum at a finite place

Let

$$
\mathscr D=(D,*,V,\psi,h)
$$

be one of the fixed rational PEL realizations. Thus $D$ is a semisimple $\mathbf Q$-algebra with positive involution, $V$ is a faithful left $D$-module, and $\psi$ is a nondegenerate alternating form satisfying

$$
 \psi(bx,y)=\psi(x,b^*y).
$$

Choose a $*$-stable order $\mathcal O\subset D$ and an $\mathcal O$-stable lattice $\Lambda\subset V$. After scaling the form once globally, assume that $\psi$ is integral and perfect on $\Lambda\otimes\mathbf Z_p$. Put

$$
G_{\mathbf Z_p}(S)=
\{g\in\operatorname{GL}_{\mathcal O\otimes S}(\Lambda\otimes S):
\psi(gx,gy)=\nu(g)\psi(x,y),\ \nu(g)\in S^\times\}.
$$

The required local condition is that this functor is represented by a smooth reductive group scheme over $\mathbf Z_p$. Then

$$
K_p=G_{\mathbf Z_p}(\mathbf Z_p)
$$

is hyperspecial in $G(\mathbf Q_p)$. This equality records an integral stabilizer, rather than choosing an arbitrary maximal compact subgroup after the fact.

### 2.2 Unramified centers, self-dual lattices, and hyperspecial level

The words in the preceding definition have concrete content. We require:

1. the center of $D\otimes\mathbf Q_p$ is a product of unramified extensions of $\mathbf Q_p$;
2. $\mathcal O\otimes\mathbf Z_p$ is maximal hereditary, and every factor active in the local model is split over its unramified center, hence has a maximal Azumaya order there;
3. the involution preserves the full order and the determinant-orientation labels select the fixed direct-trace or standard-unitary packet;
4. the map $\Lambda_p\to\Lambda_p^\vee$ induced by $\psi$ is an isomorphism;
5. the prescribed polarization type has degree prime to $p$.

These conditions are sufficient in the curve and surface data used here because passage to a full idempotent reduces the deformation problem to one or two ordinary rank-two multiplicity modules. More generally, unramifiedness of the algebra and self-duality of the lattice do not alone prove that a determinant local model is smooth. Ramified unitary signatures and certain residue-characteristic-two forms show why smoothness of the actual local model remains a separate condition.

Self-duality has two roles. It makes the polarization pairing perfect on de Rham homology, so isotropic direct summands lift cleanly. It also makes the stabilizer reductive; an almost self-dual lattice typically has a parahoric, rather than hyperspecial, stabilizer. Thus replacing self-duality by a finite-index inclusion changes the geometry rather than merely its notation.

A split quaternionic factor gives the basic local example. Let $F_w/\mathbf Q_p$ be unramified, take $D_w=M_2(F_w)$ and $\mathcal O_w=M_2(\mathcal O_{F_w})$, and use the adjoint involution for a perfect alternating form. On a self-dual module, a full idempotent removes the matrix factor and leaves a free rank-two multiplicity module. Choosing its Hodge line gives $\mathbf P^1_{\mathcal O_{F_w}}$.

For the unitary example, let $K_w/F_w$ be an unramified quadratic étale algebra, either a field or the split algebra, and give $K_w^2$ the split Hermitian form with matrix

$$
\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

The lattice $\mathcal O_{K_w}^2$ is self-dual, its unitary similitude group is unramified, and a signature-$(1,1)$ determinant condition again selects one line. Two independent places or embedding packets of this form give the product of projective lines used for the surface.

The integral classification needed here is elementary at odd unramified places and must not be confused with rational classification of the underlying form.

**Proposition 2.1 (odd unramified moving packets).** At a good odd place for the direct quaternion-trace curve or the standard unitary surface, every moving factor becomes, after an unramified splitting extension and the standard idempotent reduction, one of the following:

1. a free rank-two module over an unramified discrete valuation ring with a perfect alternating form and a symplectic basis; or
2. the standard self-dual lattice in a split binary Hermitian space for an unramified quadratic étale algebra, with Gram matrix

   $$
   \begin{pmatrix}0&1\\1&0\end{pmatrix}.
   $$

In the first case all perfect alternating rank-two lattices are isometric. In the second case all self-dual lattices in the split rational plane are isometric under the full unitary group; when the quadratic algebra is split, its two idempotents give the evaluation packet $P\oplus P^\vee$. The determinant law selects a line in each moving multiplicity plane. Any ordered determinant orientation is additional open-and-closed data and is not a consequence of lattice isometry.

**Proof.** Each moving maximal unramified Azumaya factor becomes a product of matrix rings over unramified valuation rings. Passing to a full idempotent reduces the direct trace factor or either active surface factor to its rank-two multiplicity module and carries duality to an alternating or Hermitian form on that module.

For a perfect alternating plane, choose a primitive vector $e$. Perfectness gives $f$ with $\langle e,f\rangle$ a unit; rescale $f$ to make that value $1$. Alternation gives zero diagonal entries, so $(e,f)$ is a symplectic basis.

If the quadratic étale algebra is split, its two idempotents write a self-dual lattice as $P\oplus Q$. Adjointness makes both summands isotropic and pairs them perfectly, so $Q=P^\vee$; a basis of the free rank-two reduced module gives the displayed evaluation packet.

Now let $S/O$ be an unramified quadratic field extension of odd-residue-characteristic valuation rings and let $L$ be a self-dual lattice in a split Hermitian plane. Reduction modulo the uniformizer is a nondegenerate Hermitian plane over the quadratic residue-field extension. The finite-field norm is surjective, so this plane has a nonzero isotropic vector. The isotropic equation is smooth at such a vector: its differential is

$$
w\longmapsto h(w,e)+h(e,w)=\operatorname{Tr}_{S/O}h(w,e),
$$

which is onto because $h(-,e)$ and the unramified trace are onto. Hensel lifting gives a primitive isotropic $e\in L$. Self-duality gives $f\in L$ with $h(e,f)=1$. Choose $c\in S$ with $c+\bar c=h(f,f)$ and replace $f$ by $f-ce$; the new vector is isotropic and still pairs to $1$ with $e$. Thus $L=Se\oplus Sf$ has the displayed Gram matrix. The determinant and orientation assertions follow from the packet decomposition of the Hodge quotient: rank one is a Grassmannian condition, while choosing one of two ordered components is a separate idempotent condition. $\square$

The dyadic boundary is different for the surface. For a Hermitian lattice $L$, the scale ideal generated by all $h(x,y)$ and the norm ideal generated by the $h(x,x)$ are distinct integral invariants. Self-duality fixes the scale but need not fix the norm ideal at residue characteristic two; different parity types can therefore share the same rational Hermitian space, rank, and determinant norm-class. The direct alternating plane itself still has a symplectic basis in residue characteristic two, but Book 127 does not verify the complete dyadic direct-trace order and local-model package used here. Books 127 and 129 put $2$ in their bad sets, and so does the theorem below. A separately verified dyadic local model would be new input, not a consequence of the present dependency list.


### 2.3 The reflex ring and determinant law

Let $r$ be the Hodge multiplicity function of the PEL datum. For $b\in\mathcal O$, its action on the Hodge quotient in characteristic zero has a characteristic polynomial $P_b(T)$ with coefficients in $E$. Goodness at $v$ requires

$$
 P_b(T)\in R[T]
$$

for every $b$, compatibly as one polynomial law on $\mathcal O$. The integral determinant condition on an abelian scheme $A/S$ is

$$
 \det\bigl(T-\iota(b)\mid\operatorname{Lie}(A/S)\bigr)=P_b(T)
 \quad(b\in\mathcal O).                                      \tag{2.1}
$$

It is enough to impose (2.1) on a finite $\mathbf Z$-basis of $\mathcal O$ together with the universal linear combination: equality for separate basis elements would miss mixed coefficients. Written universally, (2.1) is closed and commutes with every base change on $R$.

At an unramified place the embeddings of the center form finite étale packets. Their idempotents split the de Rham module, and $r$ prescribes the rank of the Hodge quotient in every packet. The direct quaternion-trace curve has exactly one active reduced rank-two alternating plane. For the standard unitary surface exactly two Hermitian planes move. All remaining packets are fixed. This is the integral source of the one- and two-dimensional local models.

### 2.4 A hypothesis ledger for curves and surfaces

Fix a compact open level

$$
K^{p}\subset G(\mathbf A_f^p),\qquad K=K_pK^p.
$$

The good-model theorem will use the following ledger.

- The rational PEL realization is either the direct quaternion-trace realization $D=V=B$ of Book 127, with $B$ division and split at one real place, or the standard exact two-active-place unitary surface of Book 129. Its selected generic fine PEL component union has been identified with the corresponding canonical model.
- The level $K^p$ is neat, or a full level $N\ge3$ with $(N,p\deg\lambda)=1$ is imposed, so the moduli problem has no inertia and its polarization pairing modulo $N$ is perfect.
- The rational prime $p$ is odd. In the curve case $B$ is split at every place above $p$, and the direct trace order, self-dual lattice, alternating form, polarization type, determinant law, multiplier component, and orientation extend over $R$. In the surface case the order, lattice, form, polarization type, determinant polynomial, and orientation extend over $R$ as above.
- The group $G_{\mathbf Z_p}$ is reductive and the integral local model is the smooth product of the active projective lines.
- The selected generic component union is stable under the decomposition group at $v$. If it is not already cut out by an integral determinant or orientation invariant, its integral model initially means its schematic flat closure in the ambient fine PEL scheme. Chapters 4--6 prove that this closure is an open-and-closed smooth projective union.
- A Hecke operator on a selected component union is asserted only for a double coset that preserves that union. The full component union is preserved by every prime-to-$p$ Hecke correspondence; otherwise the same construction is a correspondence from the chosen union to its Hecke translate, not an endomorphism of its cohomology.
- In the curve case $B$ is division; no anisotropic localization of the faithful PEL module is required. In the surface case the standard Hermitian plane $W$ is anisotropic and retains the finite anisotropic localization constructed in Book 129.
- In the unitary case, the rational prime $p$ lies below no place in the recorded exceptional set, in particular not below the anisotropic localization. This ensures that the latter may be used at a coefficient prime different from the residue characteristic.
One always first constructs the ambient functor defined by the integral determinant and orientation data. An arbitrarily chosen geometric component need not descend to $R$. If neatness is omitted, the natural object is a Deligne--Mumford stack; its coarse scheme can acquire quotient singularities even at a good prime.

## 3. The integral moduli functor

We now spread the generic moduli problem over the reflex ring. Because every item is expressed by a morphism of finite locally free objects or by a closed polynomial condition, the definition survives arbitrary base change.

### 3.1 Objects, arrows, and level away from the residue prime

For an $R$-scheme $S$, an object is a tuple

$$
(A,\iota,\lambda,\bar\eta^p),                                  \tag{3.1}
$$

where:

- $A/S$ is an abelian scheme of the prescribed relative dimension;
- $\iota:\mathcal O\to\operatorname{End}_S(A)$ is a ring homomorphism;
- $\lambda:A\to A^\vee$ is a polarization of the fixed prime-to-$p$ type and satisfies $\lambda\iota(b)=\iota(b^*)^\vee\lambda$;
- $\bar\eta^p$ is the prescribed $K^p$-orbit of prime-to-$p$ adelic level trivializations, respecting the $\mathcal O$-action and the alternating pairing up to the common multiplier;
- the Lie action satisfies (2.1), including the selected orientation when the determinant law alone has more than one component.

An arrow is an isomorphism of abelian schemes preserving every structure. The integral problem uses isomorphisms, not prime-to-$p$ quasi-isogenies, as arrows. Quasi-isogenies enter Hecke correspondences later. At full level $N$ with $(N,p\deg\lambda)=1$, the level is an actual symplectic $\mathcal O/N\mathcal O$-linear trivialization of $A[N]$; the torsion group scheme is finite étale over $S$, and the polarization pairing on it is perfect.

Descent is effective. Abelian schemes, homomorphisms, polarizations, and finite étale level structures descend for the fppf topology. The Rosati identity and determinant polynomial descend because they are equalities of morphisms. Consequently (3.1) defines an fppf stack, and under neatness its sheaf of isomorphism classes is set-valued.

### 3.2 Polarizations and the integral determinant condition

The prime-to-$p$ condition on $\deg\lambda$ makes the alternating form on $H_{1,\mathrm{dR}}(A/S)$ perfect. It also ensures that the pairing on $A[\ell^n]$ is perfect whenever $\ell$ is prime to $p\deg\lambda$. None of this permits one to replace $\lambda$ by a bilinear form: positivity is a fiberwise ample-cone condition and is retained as part of the moduli datum.

Equation (2.1) is imposed on $\operatorname{Lie}A$, not on all de Rham homology. In the homology convention there is an exact Hodge sequence

$$
0\longrightarrow\omega_{A^\vee}
\longrightarrow H_{1,\mathrm{dR}}(A/S)
\longrightarrow\operatorname{Lie}(A/S)\longrightarrow0.       \tag{3.2}
$$

The order preserves this sequence. The determinant law selects the quotient ranks, while polarization makes the subbundle $\omega_{A^\vee}$ isotropic. Interchanging the two bundles changes the Hodge multiplicity function and can select the conjugate Shimura datum; the convention is therefore fixed once and used throughout.

### 3.3 Representability and the universal family

**Theorem 3.1 (ambient integral representability).** Under the integral and level hypotheses of Section 2.4, without any flatness or properness hypothesis, the full fine PEL functor defined by the integral determinant and orientation data is represented by a quasi-projective $R$-scheme $\mathscr M_K^{\mathrm{amb}}$ of finite presentation. Any union cut out by an explicit integral open-and-closed invariant is represented by the corresponding open-and-closed subscheme. The ambient scheme carries a universal tuple

$$
(\mathcal A,\iota^{\mathrm{univ}},\lambda^{\mathrm{univ}},
\bar\eta^{p,\mathrm{univ}}).                                   \tag{3.3}
$$

**Proof strategy.** One embeds the problem finitely over a Siegel moduli scheme with the same polarization type and a sufficiently rigid prime-to-$p$ level. The additional action and determinant conditions are algebraic and bounded.

**Proof.** A high tensor power of a relatively ample bundle inducing a fixed multiple of the polarization gives a uniform projective embedding of every object. The Hilbert scheme of the resulting fibers, together with the group-law equations, gives a finite-type framed atlas. Homomorphisms representing the action of a finite basis of $\mathcal O$ form closed subschemes; the multiplication table, Rosati relation, and universal determinant identity are closed equations. The fixed finite étale level is represented by a finite étale isomorphism scheme.

Forgetting the order action to the rigid Siegel scheme is finite. Quasi-finiteness follows from rigidity of homomorphisms and the Rosati norm bound; properness follows from extension of homomorphisms between abelian schemes over a DVR. A finite algebraic space over a scheme is a scheme. Full level at least three kills automorphisms, and an arbitrary neat level is a free finite quotient of such a principal-level scheme. Hence the result is a quasi-projective scheme of finite presentation. Its identity map is, by Yoneda, the universal object (3.3). $\square$

The theorem does not yet assert flatness, smoothness, or properness. In particular, representability does not exclude vertical components of the determinant locus.

### 3.4 Generic-fiber comparison

Base change of the ambient moduli problem from $R$ to $E$ recovers the previously constructed PEL functor, because the integral lattice and order become the rational tensors and the prime-to-$p$ level together with $K_p$ recovers the compact open subgroup. Let $\mathscr M_{K,E}^{\mathrm{sel}}$ be the open-and-closed Galois-stable union belonging to the chosen lattice genus, multiplier component, orientation, and canonical Shimura variety. Then

$$
 \mathscr M_{K,E}^{\mathrm{sel}}
 \simeq\operatorname{Sh}_K(G,X)^{\mathrm{sel}}.              \tag{3.4}
$$

For the direct quaternion-trace curve this is Book 127's comparison with the canonical model of that PEL-exact datum; for the surface it is Book 129's comparison. The isomorphism is over $E$, not merely over $\mathbf C$: both sides have canonical-model descent, and the complex moduli identification respects reciprocity on connected components.

Define the fine flat-closure model

$$
 \mathscr M_K^{\mathrm{fl}}
 =\overline{\mathscr M_{K,E}^{\mathrm{sel}}}^{\,\mathrm{sch}}
 \subset\mathscr M_K^{\mathrm{amb}}.                           \tag{3.5}
$$

Affine-locally its coordinate ring is the image of the ambient ring in its localization at the uniformizer, so $\mathscr M_K^{\mathrm{fl}}$ is $R$-flat and its generic fiber is (3.4). This formal property says nothing about smoothness or properness. The universal tuple on the ambient scheme restricts to (3.5), but (3.5) is not yet claimed to represent an independently described open-and-closed integral subfunctor. Chapter 5 will obtain that claim from ambient smoothness, while Chapter 6 obtains properness from the boundary theorem.

The universal object on the generic fiber agrees with the earlier universal PEL abelian variety. For the unitary modèles étranges surface, that universal abelian variety remains auxiliary: its endomorphism action realizes the required group, but its first cohomology is not automatically the desired rank-two automorphic representation.

## 4. The good local model

Representability reduces geometry to deformation theory. The decisive fact at a good prime is that the integral flag problem is already smooth; no singularity is hidden in reduction of the determinant equations.

### 4.1 Why a determinant equation is not enough

Let $x$ be a geometric point of characteristic $p$. A first-order deformation of its Hodge subbundle in (3.2) is a graph

$$
u:F\longrightarrow H/F.
$$

The conditions that $F$ be $\mathcal O$-stable, isotropic, and of the prescribed determinant type are linear to first order. Merely subtracting the number of equations from the dimension of a Grassmannian would assume that these linear equations have constant rank. At ramified primes they often do not.

Goodness supplies a stronger description. The unramified center splits étale-locally on $R$, a full idempotent removes the Azumaya matrix factor, and the determinant law fixes all multiplicity modules except the active rank-two planes. Thus the local model is visibly a product of Grassmannians of lines. This proves flatness, smoothness, and the tangent dimension at once.

### 4.2 The framed local-model diagram

The integral deformation input deserves an explicit statement because the characteristic-zero filtration theorem alone would not control the special fiber.

**Proposition 4.1 (integral Hodge-filtration lifting).** Let $S_0\hookrightarrow S$ be a square-zero thickening of local Artinian $R$-schemes, and let $A_0/S_0$ be an abelian scheme. If $p$ is nilpotent on $S$, deformations of $A_0$ are classified on a divided-power envelope of this thickening by locally direct-summand lifts of the Hodge filtration in the evaluated Dieudonné crystal, subject to the descent datum of Book 60, Theorem 7.1. An endomorphism lifts exactly when that filtration is stable, and a prime-to-$p$ polarization lifts exactly when it is isotropic for the evaluated perfect alternating form. Prime-to-$p$ level lifts uniquely. Consequently the morphism from the framed PEL deformation functor to the completed stable-isotropic flag scheme is formally smooth. The same conclusion holds when $p$ is invertible on $S$.

**Proof strategy.** In residue characteristic $p$, this is the Grothendieck--Messing classification followed by the Serre--Tate equivalence. In characteristic zero it is the Hodge chart of Book 127. The PEL structures are morphisms in those classifications, so stability and isotropy are exact lifting conditions rather than tangent-space counts.

**Proof.** Suppose first that $p$ is nilpotent on $S$. Book 60, Theorem 6.1, evaluates the Dieudonné crystal of $A_0[p^\infty]$ on a divided-power enlargement and classifies lifts of the $p$-divisible group by direct-summand lifts of its Hodge filtration. Its Theorem 7.1 proves that the classification, including its descent datum, is independent of the chosen divided-power presentation and identifies the resulting $p$-divisible-group deformation with a unique abelian-scheme deformation over the original nilpotent thickening. Thus the module on which the filtration is lifted lives on the divided-power evaluation; the theorem does not assert a canonical finite locally free evaluation over an arbitrary non-PD $S$.

The same theorems identify morphisms with filtration-preserving crystal maps. Book 60, Section 7.3, therefore shows that the $\mathcal O$-action lifts exactly when the evaluated filtration is stable and that the prime-to-$p$ polarization lifts exactly when it is isotropic. Positivity persists over a nilpotent thickening. Prime-to-$p$ level is finite étale and hence lifts uniquely. A lift of the framed flag over $S$ pulls back to a descent-compatible filtration on the divided-power envelope; smoothness of the frame torsor supplies a lifted frame. Grothendieck--Messing and Serre--Tate then reconstruct the PEL deformation. This is precisely formal smoothness of the framed map to the flag scheme.

If $p$ is invertible on $S$, Book 127, Theorem 11.1, identifies the completed characteristic-zero PEL moduli space with the completed stable isotropic flag scheme. It gives the same formal-smoothness conclusion, including the determinant and integral orientation conditions and unique lifting of level. Since $S$ is local Artinian, $p$ is either nilpotent or invertible. $\square$

At every geometric point of the ambient functor, the order action, perfect polarization form, determinant ranks, and selected labels put de Rham homology étale-locally in the fixed lattice genus. Proposition 2.1 gives this assertion on the direct curve's alternating plane and on the standard surface's Hermitian planes. Thus the frame functor below is locally nonempty. This is where integral lattice classification enters: the determinant polynomial alone would not make it a torsor under the selected hyperspecial group.

Let $\widetilde{\mathscr M}_K^{\mathrm{amb}}$ classify an ambient PEL object together with an $\mathcal O\otimes R$-linear symplectic frame of its de Rham homology by $\Lambda\otimes R$. There is a diagram

$$
\mathscr M_K^{\mathrm{amb}}\xleftarrow{\ \pi\ }
\widetilde{\mathscr M}_K^{\mathrm{amb}}
\xrightarrow{\ \varphi\ }M^{\mathrm{loc}}.                    \tag{4.1}
$$

Here $\pi$ is a torsor under the reductive smooth group $G_R$, and $\varphi$ sends a frame to the framed Hodge subbundle. Both maps are smooth. Smoothness of $\pi$ is the torsor property. Formal smoothness of $\varphi$ is the final assertion of Proposition 4.1: on a non-PD thickening the reconstruction is performed on a divided-power envelope and descended, not by postulating a de Rham evaluation over the thickening. Finite presentation turns formal smoothness into smoothness.

Since the schemes are finitely presented, formal smoothness is smoothness. Thus $\mathscr M_K^{\mathrm{amb}}$ and $M^{\mathrm{loc}}$ have the same completed local singularities up to formally smooth variables. This argument uses the integral deformation theorem for abelian schemes; it is not an inference from the generic local-model diagram.

### 4.3 The direct quaternionic curve packet

Let $D=V=B$ be the direct quaternion-trace datum. At a good place, every factor $B_w$ above $p$ is split and its maximal order is $M_2(\mathcal O_{F_w})$. Over an étale splitting ring $R'$, a full idempotent identifies the active part of $\Lambda\otimes R'$ with $W\otimes U$, where $W$ is the fixed simple module and $U$ is a self-dual alternating plane. A stable Hodge submodule is $W\otimes L$ for a line subbundle $L\subset U$, and every such line is isotropic. The determinant law and the chosen orientation fix every other summand. Consequently

$$
 M^{\mathrm{loc}}_{R'}\simeq\mathbf P(U)\simeq\mathbf P^1_{R'}. \tag{4.2}
$$

Descent from $R'$ gives the selected smooth projective $R$-form of this flag variety. Its tangent space at $L$ is

$$
\operatorname{Hom}(L,U/L),
$$

free of rank one. All inactive factors have a unique filtration of the prescribed labeled type and contribute no tangent direction. This conclusion is only for the direct datum $D=V=B$.

### 4.4 The two unitary lines

For the unitary surface, the two signature-$(1,1)$ packets give rank-two multiplicity modules $U_1,U_2$. After an étale splitting,

$$
 M^{\mathrm{loc}}\simeq\mathbf P(U_1)\times_R\mathbf P(U_2).   \tag{4.3}
$$

Its tangent space at $(L_1,L_2)$ is

$$
\operatorname{Hom}(L_1,U_1/L_1)
\oplus
\operatorname{Hom}(L_2,U_2/L_2),                               \tag{4.4}
$$

free of rank two. The polarization pairs conjugate idempotent packets and introduces no equation coupling the two active lines; the common rational similitude multiplier controls their determinant lines but not their tangent independence. Formula (4.3) is exactly where the orientation condition is used: without it, conjugate rank assignments can form a second open-and-closed local model.

## 5. Smoothness and extension properties

The local model proves regularity near every geometric point. The moduli interpretation then supplies an extension property strong enough to characterize the model uniquely.

### 5.1 Formal smoothness from filtration lifting

**Theorem 5.1 (smoothness).** The structural morphism

$$
\mathscr M_K^{\mathrm{amb}}\longrightarrow\operatorname{Spec}R
$$

is smooth. Its relative dimension is one for the direct quaternion-trace curve and two for the standard unitary surface.

**Proof.** In (4.1), $\pi$ is smooth and surjective, $\varphi$ is smooth, and $M^{\mathrm{loc}}/R$ is smooth by (4.2) or (4.3). Therefore $\widetilde{\mathscr M}_K^{\mathrm{amb}}/R$ is smooth. Smoothness descends through $\pi$, proving the assertion for the ambient scheme. Relative dimensions may be computed on completed local rings or after the étale splitting: the frame directions occur on both sides of (4.1), so the moduli tangent directions are those of the local model. They have ranks one and two by (4.2) and (4.4). $\square$

One can see the decisive infinitesimal step directly. Given a square-zero extension $S_0\hookrightarrow S$ and a PEL object over $S_0$, étale-locally on $S$ its Hodge filtration corresponds to one or two lines. A line direct summand of a free rank-two module lifts by lifting one unimodular generator, and it remains a direct summand because one coordinate stays a unit. The fixed central packets lift uniquely. The lifted line or lines reconstruct the PEL object, so there is no obstruction group.

### 5.2 Dimensions, regularity, and flatness

Smoothness over the DVR $R$ implies flatness and regularity. Every irreducible component of $\mathscr M_K^{\mathrm{amb}}$ has dimension two in the curve case and three in the surface case; every geometric fiber is smooth and pure of dimension one or two. The special fiber is reduced, and formation of the relative cotangent bundle commutes with arbitrary base change.

These conclusions do not require the ambient scheme to be connected. A regular locally noetherian scheme has disjoint open irreducible components, and flatness makes every such component dominate $R$. Its generic fiber is regular as well, so the generic irreducible and connected components are likewise disjoint. It follows that the schematic closure (3.5) of a union of generic components is exactly the union of the corresponding ambient components. Hence

$$
\mathscr M_K^{\mathrm{fl}}\subset\mathscr M_K^{\mathrm{amb}}
$$

is open and closed and is itself smooth of the stated relative dimension. From now on write

$$
\mathscr M_K:=\mathscr M_K^{\mathrm{fl}}.
$$

It represents the open-and-closed subfunctor obtained by restricting the ambient representing functor and carries the restricted universal tuple. This is the promised identification of flat closure with a smooth integral component union. It does not say that $\mathscr M_K^{\mathrm{amb}}=\mathscr M_K$ unless the selected generic union is the whole ambient generic fiber; other horizontal PEL components may remain. More importantly, this identification came from the local-model theorem, not from the properness argument of Chapter 6.

### 5.3 The extension property

The natural uniqueness principle for an integral canonical model tests maps from regular schemes on which abelian varieties cannot acquire a hidden codimension-one degeneration.

Call an $R$-scheme $S$ **healthy regular** if it is regular and flat over $R$, and every abelian scheme over an open $U\subset S$ containing the generic fiber and all codimension-one points extends uniquely over $S$. Healthiness is retained as a hypothesis: the assertion that every smooth mixed-characteristic $R$-scheme has this property is a separate purity theorem and is not needed below. In the uniqueness argument of Section 5.4, the relevant abelian schemes already extend over both test models, so the codimension-one condition can be checked directly.

**Theorem 5.2 (extension property).** If $S$ is healthy regular and flat over $R$, restriction induces a bijection

$$
\operatorname{Hom}_R(S,\mathscr M_K)
\xrightarrow{\sim}
\operatorname{Hom}_E(S_E,\mathscr M_{K,E}).                     \tag{5.1}
$$

provided the generic PEL abelian scheme has good reduction at every codimension-one point of $S$.

**Proof.** A generic map is a PEL abelian scheme over $S_E$. At each codimension-one point, the good-reduction hypothesis extends it over the corresponding DVR. Uniqueness over the overlaps glues these local extensions, after shrinking, to an abelian scheme over an open $U\subset S$ containing $S_E$ and every codimension-one point. Healthiness then extends it uniquely to an abelian scheme $A/S$.

The generic order action and polarization extend uniquely over the normal base $S$ by the extension theorem for homomorphisms of abelian schemes; positivity persists because the degree is constant and the ample chamber cannot change without degeneracy, and the prime-to-$p$ kernel type is locally constant. Once $A/S$ exists, the scheme of prime-to-$p$ level trivializations is finite étale over $S$. The generic level section extends at every codimension-one point by construction. Its schematic closure is finite and birational over the normal scheme $S$, hence is $S$; this extends the section without invoking an undeclared purity theorem. The finite étale orientation label extends by the same argument. The Rosati and determinant identities hold on the dense generic fiber and therefore everywhere. The resulting map to $\mathscr M_K^{\mathrm{amb}}$ factors through its open-and-closed subscheme $\mathscr M_K$: the generic fiber does, and flatness of $S/R$ makes that fiber dense in every component of $S$. Uniqueness follows from separatedness, or term by term from rigidity. $\square$

The good-reduction qualification is essential. The extension property does not turn a semistable generic abelian variety into an abelian scheme. Chapter 6 proves the qualification for the direct quaternion-trace curve by its torus-rank obstruction and for the standard surface by its anisotropic-localization obstruction.

### 5.4 Uniqueness of the good model

Suppose $\mathscr X$ and $\mathscr Y$ are smooth $R$-models of the same PEL generic fiber in one fixed presentation, the generic identity identifies their universal PEL abelian varieties, and both have the corresponding PEL extension property. To extend the generic identity from $\mathscr X$ to $\mathscr Y$, repeat the proof of Theorem 5.2 with test scheme $\mathscr X$. No general healthiness theorem for $\mathscr X$ is needed: the relevant generic abelian variety already extends as the universal abelian scheme on $\mathscr X$. Its PEL structures give a map $f:\mathscr X\to\mathscr Y$. Reversing the roles gives $g:\mathscr Y\to\mathscr X$. Both composites restrict to the identity generically, hence are the identity by separatedness. Thus $f$ is unique and is an isomorphism.

No uniqueness statement across different faithful PEL realizations is made. The preceding argument applies only when the generic identity identifies the fixed universal PEL family and all of its tensors.

This proof explains why a good model is canonical after its extension property is established. Normalization in the generic function field alone would allow many regular modifications of the special fiber; the extension property excludes them.

## 6. Properness in the compact cases

The generic quaternionic curves and unitary surfaces selected here are projective because their adjoint groups are anisotropic over $\mathbf Q$. To prove their integral models proper, one must rule out degeneration of the universal abelian variety at the closed point of a trait.

### 6.1 Flat closure and the valuative criterion

Let $S=\operatorname{Spec}V$ be a trait over $R$, with fraction field $L$, and let

$$
\operatorname{Spec}L\longrightarrow\mathscr M_K
$$

be a point. Separatedness gives uniqueness of an extension. Existence asks whether the PEL abelian variety $A_L$ has good reduction over $V$. Properness of the generic Shimura variety only extends the associated point after passing to some abstract proper $R$-model; it says nothing about extension of $A_L$ on the PEL moduli scheme. Nor would a trait argument through the selected generic union control an unrelated vertical component of $\mathscr M_K^{\mathrm{amb}}$. The correct object is therefore the flat closure $\mathscr M_K=\mathscr M_K^{\mathrm{fl}}$ from (3.5).

There are two direct ways to rule out the torus in the fixed realizations. For $D=V=B$, its cocharacter group is a unital $B$-module and a dimension count is decisive; the positive $J_T$-block below records the same obstruction in polarized Hodge-theoretic form. For the standard surface, one recorded anisotropic finite localization is decisive.

### 6.2 Semiabelian degeneration and the direct toric obstruction

After passing to a henselian completion, then making a finite separable extension of its fraction field and normalizing the valuation ring, Book 40, Theorem 9.7, gives semistable reduction. Thus the identity component of the Néron model has special fiber

$$
0\longrightarrow T\longrightarrow G_s\longrightarrow A_0\longrightarrow0, \tag{6.1}
$$

where $T$ is a torus and $A_0$ an abelian variety. Every order endomorphism and the polarization homomorphism extend functorially to the Néron--Raynaud data; only an inducing ample line bundle may require a harmless multiple. If $T\ne0$, its rational cocharacter group

$$
X_*(T)\otimes_{\mathbf Z}\mathbf Q
$$

is nonzero and is stable under the relevant semisimple algebra.

Every endomorphism of $A_L$ extends uniquely to its Néron model, so the PEL order preserves (6.1). Let $M_A=[Y_A\to G]$ be the Raynaud one-motive. For each prime $\ell\ne p$, Book 40 gives a canonical comparison

$$
T_\ell M_A\simeq T_\ell A
$$

and a functorial filtration

$$
0\subset W_{-2,\ell}\subset W_{-1,\ell}
\subset H_\ell:=T_\ell A\otimes\mathbf Q_\ell,               \tag{6.2}
$$

with

$$
W_{-2,\ell}=X_*(T)\otimes\mathbf Q_\ell(1).
$$

The filtration is stable under $D\otimes\mathbf Q_\ell$. The polarization pairing annihilates $W_{-2,\ell}$ with itself and identifies $W_{-1,\ell}$ with its orthogonal complement. These assertions are genuinely local in the coefficient field. They do not yet put one subspace inside the fixed rational PEL representation $V$.

The common rational object already present before any comparison with $V$ is the torus module

$$
X_T=X_*(T)\otimes_{\mathbf Z}\mathbf Q.                       \tag{6.3}
$$

It is a unital $D$-module and has dimension equal to the toric rank. This elementary observation gives two especially short exclusions for exact standard realizations.

**Proposition 6.1 (rank and finite-place obstructions).** A semistable degeneration has $T=0$ in either of the following cases.

1. The quaternionic PEL realization is the direct trace realization $D=B$, $V=B$, with $B/F$ a division quaternion algebra.
2. The unitary PEL realization is the standard realization of Book 129, Definition 4.1 and Proposition 4.2: $D=K$, $V=W$, and the binary Hermitian space $W$ has a recorded anisotropic finite localization $W_t$ away from the good residue prime.

**Proof.** In case 1, a nonzero unital left module over the division algebra $B$ has rational dimension at least $\dim_{\mathbf Q}B$. Here

$$
g=\frac12\dim_{\mathbf Q}V=\frac12\dim_{\mathbf Q}B,
$$

whereas $\dim_{\mathbf Q}X_T$ is the toric rank and is at most $g$. Thus $X_T\ne0$ would give $2g\leq\dim_{\mathbf Q}X_T\leq g$, a contradiction.

In case 2, a nonzero $X_T$ is a nonzero $K$-vector space. Let $\ell\ne p$ be the rational prime below the recorded finite place $t$ where $W_t$ is anisotropic. Choose a representative $\eta_\ell:V\otimes\mathbf Q_\ell\xrightarrow{\sim}H_\ell$ of the prime-to-$p$ PEL level. It identifies (6.2), including its $K\otimes\mathbf Q_\ell$-action and polarized alternating form, with the fixed realization up to a scalar similitude. The $t$-factor

$$
U_t=\bigl(\eta_\ell^{-1}W_{-2,\ell}\bigr)_t\subset V_t=W_t
$$

is nonzero because $X_T$ has positive constant rank as a $K$-module, and it is $K_t$-stable and alternating-isotropic. Write the alternating form locally as

$$
\psi_t(x,y)=\operatorname{Tr}_{K_t/\mathbf Q_\ell}
             (\alpha\Phi_t(x,y))
$$

with $\alpha\ne0$, as in Book 129, Section 5.1. For $x\in U_t$ and every $a\in K_t$, stability and isotropy give

$$
0=\psi_t(ax,x)
 =\operatorname{Tr}_{K_t/\mathbf Q_\ell}
   (\alpha a\Phi_t(x,x)).
$$

Nondegeneracy of the field-trace pairing forces $\Phi_t(x,x)=0$. The anisotropy of $W_t$ forces $x=0$, contradicting $U_t\ne0$. Hence $X_T=0$ in both cases, and the freeness of a torus cocharacter lattice gives $T=0$. $\square$

The qualifier “away from the good residue prime” is not extra luck. Proposition 4.2 of Book 129 puts every nonsplit finite localization in its recorded exceptional set, while the good-place ledger requires the chosen hyperspecial place to lie outside that set. The argument uses one actual $\ell$-adic Raynaud piece and the common $K$-module $X_T$; it never descends distinct $\ell$-adic subspaces to a subspace of $V$ over $\mathbf Q$.

The rank proof has a useful polarized refinement that fixes the action variance and Hodge convention explicitly.

**Proposition 6.2 (the direct toric block).** For a polarized Raynaud one-motive carrying the direct left $B$-action, let

$$
X=X_*(T)_{\mathbf Q},\qquad Y=Y_A\otimes\mathbf Q,
$$

let $e_\lambda:X\times Y\to\mathbf Q$ be the perfect outer pairing, and let
$\nu:Y\xrightarrow{\sim}X$ be the rational tropical map. The induced left $B$-actions satisfy

$$
e_\lambda(bx,y)=e_\lambda(x,b^*y).
$$

Functoriality of the Raynaud construction gives $\nu(by)=b\nu(y)$. Put

$$
H_T=X\oplus Y,\qquad
\psi_T((x,y),(x',y'))=
e_\lambda(x,y')-e_\lambda(x',y).                              \tag{6.4}
$$

If $q_\lambda(z,z')=e_\lambda(\nu z,z')$ is the positive symmetric monodromy form, then

$$
J_T(\nu z,y)=(-\nu y,z)                                       \tag{6.5}
$$

commutes with $B$, has square $-1$, and satisfies

$$
\psi_T((\nu z,y),J_T(\nu z,y))
=q_\lambda(z,z)+q_\lambda(y,y)>0.                             \tag{6.6}
$$

Its $i$-eigenspace is

$$
H_T^{\,i}=
\{(\nu z,-iz):z\in Y_{\mathbf C}\}
\simeq Y_{\mathbf C}.                                        \tag{6.7}
$$

Consequently the toric determinant contribution at a complex packet $\tau$ is not an unspecified rank term: in the convention selecting $H_T^{\,i}$ it is

$$
P^T_{b,\tau}(T)=
\det\!\left(T-b\mid Y_\tau\right),                        \tag{6.8}
$$

with the conjugate packet used if the opposite Hodge quotient convention is chosen.

For the direct datum $V=B$, any nonzero left $B$-module $X$ has $\mathbf Q$-dimension at least $\dim_{\mathbf Q}B$. Hence the polarized block $H_T=X\oplus Y$ would already have dimension at least $2\dim_{\mathbf Q}B$, while the whole rational homology $V$ has dimension $\dim_{\mathbf Q}B$. Thus $H_T$ cannot occur unless $T=0$. Equivalently, the shorter calculation in Proposition 6.1 compares $\dim_{\mathbf Q}X$ directly with the abelian dimension. The $J_T$ calculation is not being used to compare different PEL realizations; it records that the toric subquotient carries the correct positive direct-trace Hodge block and determinant convention.

**Proof.** Every order endomorphism acts functorially on the Raynaud extension and period lattice. Cocharacters and periods therefore carry covariant left $B$-actions. The polarization identity places the involution in the outer pairing, and functoriality of valuation gives $\nu(by)=b\nu(y)$. Symmetry and positivity of $q_\lambda$ are Book 40, Theorem 7.2. Direct substitution in (6.4) proves (6.6), while applying (6.5) twice gives $J_T^2=-1$. The tropical identity gives

$$
J_T(b\nu z,by)=(-\nu(by),bz)=b(-\nu y,z),
$$

so $J_T$ commutes with $B$. Solving $J_T(x,y)=i(x,y)$ gives $x=\nu z$ and $y=-iz$, proving (6.7). Differentiation of cocharacters identifies $X\otimes L$ with $\operatorname{Lie}T$ $B$-linearly, so (6.7) gives (6.8). The final dimension comparison is the one stated above. $\square$

### 6.3 Direct boundary exclusion

The boundary calculation now has exactly the scope of the two fixed faithful modules.

**Proposition 6.3 (boundary exclusion).** Under the ledger of Section 2.4:

1. every semistable degeneration belonging to the direct quaternion-trace curve has $T=0$;
2. every semistable degeneration belonging to the standard unitary surface has $T=0$.

Consequently every such generic PEL abelian variety has potential good reduction.

**Proof.** Clause 1 is Proposition 6.1(1); Proposition 6.2 supplies its polarized $J_T$ formulation. Clause 2 is Proposition 6.1(2). After the finite semistable extension, toric rank zero means that the connected special fiber is an abelian variety, hence the original abelian variety has good reduction over that extension. $\square$

### 6.4 Actual good reduction and properness

Potential good reduction is not yet good reduction over the original trait. Work first on a normal principal-level cover contained in the given prime-to-$p$ level and divisible by an odd auxiliary prime $q\ne p$ chosen away from the polarization degree and the fixed bad set. A point of this cover carries full level at $q$. Over a finite field extension where good reduction exists, $T_qA$ is unramified, so inertia over $L$ has finite image. Full level trivializes $A[q]$, putting that finite image in the principal congruence kernel of $\operatorname{GL}(T_qA)$. Book 40, Lemma 10.3, says this kernel has no nontrivial finite-order element. Inertia is therefore trivial, and Book 40, Theorem 10.2, gives good reduction over the original henselian DVR. Completion and faithfully flat descent do not change the conclusion.

At a general neat fine level, one should not infer trivial inertia merely from an adelic level orbit. Instead choose a normal principal refinement of odd auxiliary level. Properness is first proved on that cover by the preceding congruence argument. Its finite map to the neat flat closure is surjective: its closed image contains the entire generic component union, and the target is its schematic flat closure. Properness therefore descends. The valuative extension of a base point then pulls back the universal family on the fine neat model and yields actual good reduction there. At a non-neat coarse quotient, the base point can extend while a universal abelian scheme does not exist, so no objectwise good-reduction claim is made there without a stack lift.

Once the abelian scheme exists, the structures extend in the correct order. Endomorphisms and the polarization homomorphism extend uniquely by Book 38; positivity and the prescribed prime-to-$p$ kernel type persist. Prime-to-$p$ torsion is finite étale, so full level or an orbit level extends from trivial inertia. The determinant identity extends coefficientwise on $\operatorname{Lie}A$, and the finite étale orientation label cannot jump. A chosen inducing ample line bundle is not needed for extension of the polarization homomorphism.

**Theorem 6.4 (flat-closure properness and the good model).** Let $\mathscr M_K^{\mathrm{fl}}$ be (3.5).

1. For the direct quaternion-trace curve at every good odd place, $\mathscr M_K^{\mathrm{fl}}$ is proper and projective over $R$.
2. For the standard unitary surface under the good-place ledger, $\mathscr M_K^{\mathrm{fl}}$ is proper and projective over $R$.
3. Under the local-model hypotheses proved in Chapter 4, $\mathscr M_K^{\mathrm{fl}}=\mathscr M_K$ is the open-and-closed smooth component union identified in Section 5.2. It is therefore the desired smooth projective fine integral PEL model. The ambient scheme is proper only when its entire generic component union is selected or when properness is proved separately for every horizontal union.

**Proof.** Work first at a normal full level containing an odd auxiliary prime. Embed the quasi-projective flat closure in its scheme-theoretic closure inside a projective space over $R$. Its generic fiber is already closed because the selected compact Shimura variety is proper. If a vertical boundary point remained, the noetherian trait-selection lemma would produce a mixed-characteristic DVR with generic point in the selected PEL space and closed point on that boundary. After completion, Proposition 6.3 and the principal-level congruence argument extend the entire PEL object over the original DVR. Every generic equation of the selected component vanishes in that torsion-free DVR, so the extension factors through the schematic flat closure. Separatedness of the projective closure then contradicts the chosen boundary specialization. Thus the full-level flat closure equals its projective closure.

For an arbitrary neat level, choose a normal full-level subgroup inside it. The resulting finite map is surjective onto the selected flat closure, so properness descends. The flat closure is quasi-projective by Theorem 3.1, hence properness makes it projective. This proves clauses 1 and 2, using respectively the two clauses of Proposition 6.3. Clause 3 is Section 5.2 and does not enter the properness proof. Thus ambient smoothness and flat-closure properness remain logically independent. $\square$

Theorem 6.4 removes the good-reduction qualification in Theorem 5.2 for every final fine model. At principal auxiliary level, Proposition 6.3 and the congruence argument give good reduction directly. At a general neat level, properness extends the base point over each codimension-one trait and pullback of the universal abelian scheme gives good reduction there. Hence the final fine models satisfy the healthy-regular extension property and are unique within their fixed PEL presentation as in Section 5.4.

This is the sense in which $\mathscr M_K$ is the **integral canonical PEL model**: its generic canonical model, fine moduli interpretation, and healthy-regular extension property determine it uniquely within the fixed direct-trace or standard-unitary presentation.

For a smooth proper scheme, the étale sheaf of geometric connected components is finite étale over $R$. A decomposition-group-stable union of generic components therefore also determines, after properness, a unique open-and-closed integral union through its idempotent. This agrees with the flat closure already identified in Section 5.2. A single geometric component still need not be defined over $R$; it must first be replaced by its decomposition-stable union or the reflex local ring must be extended to its component field.

A noncompact PEL variety is different: its open moduli scheme can have a genuine semiabelian boundary and requires a compactification.

## 7. Fine levels, quotient levels, and base change

Good models occur in towers. The relation among their levels must be kept integral because later Hecke operators are built by moving between them.

### 7.1 Change of prime-to-$p$ level

Let $K_1^p\subset K_2^p$ be neat compact opens, with common hyperspecial $K_p$. Forgetting part of the level defines

$$
f_{12}:\mathscr M_{K_pK_1^p}\longrightarrow
\mathscr M_{K_pK_2^p}.                                          \tag{7.1}
$$

The map is finite: a compatible refinement of a fixed prime-to-$p$ level lies in a finite étale isomorphism scheme. It is étale because infinitesimal deformations of finite étale level are unique, so source and target have the same Hodge-filtration deformation functor. If $K_1^p$ is normal in $K_2^p$, the effective deck group is the quotient of $K_2^p/K_1^p$ by central elements acting trivially on the moduli problem.

### 7.2 Finite étale covers and quotient stacks

For an ordinary change of level within one fixed PEL presentation, if $K_1^p$ is normal in $K_2^p$ and the target level is neat, the effective deck group acts freely and (7.1) is a finite étale torsor. Without normality it is still finite étale but need not be a torsor. At arbitrary target level, choose a normal fine subgroup; the correct object is

$$
\mathscr{M}_{K_2}\simeq[\mathscr M_{K_1}/\Delta].               \tag{7.2}
$$

The stack is smooth because smoothness is smooth-local and the fine atlas is finite étale. Under the hypotheses of Theorem 6.4 it is also proper, since properness descends through its finite cover. The map from the fine-level scheme to the coarse quotient is finite; the coarse quotient itself has the same relative dimension over $R$ and can have quotient singularities at fixed points. Thus “good reduction at coarse level” cannot mean smoothness without a hypothesis killing stabilizers.

### 7.3 Universal families at coarse level

The fine scheme carries the universal abelian scheme. For an ordinary level quotient, its deck action is linearized by PEL isomorphisms, so it descends to the quotient stack and remains universal. It descends further to the coarse scheme exactly when every stabilizer acts trivially on the complete PEL object. Usually a scalar such as $-1$ acts trivially on the coarse moduli point and nontrivially on the abelian variety, so no universal family exists there.

Cohomological correspondences on the base may descend to the coarse scheme because their graphs and cycle classes are stabilizer-invariant. One must not infer descent of the universal abelian variety or of an integral coefficient system from descent of its base Hecke action.

### 7.4 Extension of scalars

Let $R\to R'$ be an unramified extension of discrete valuation rings compatible with a place $v'\mid v$ of the reflex field. Every ingredient of the functor commutes with base change, giving a canonical isomorphism

$$
\mathscr M_K\otimes_RR'\simeq\mathscr M_{K,R'}.                \tag{7.3}
$$

On a fine PEL model, the universal family, Hodge bundles, polarization, and prime-to-$p$ level pull back under (7.3). The local model becomes the corresponding split form after a sufficiently large unramified extension. Smoothness and properness are preserved.

For a ramified extension $R\to R'$, ordinary scalar extension of an already good model remains smooth, but it need not equal a newly formulated moduli problem based on a different ramified order or parahoric lattice. Equality holds only when the entire integral datum is the pullback of the old one.

## 8. Prime-to-residue-characteristic Hecke correspondences

A Hecke operator changes a prime-to-$p$ lattice. At a good prime this modification is finite étale on torsion and therefore extends over the integral model without altering its local deformation theory.

Throughout this chapter, $\mathscr M_K$ denotes a fine PEL flat-closure model for one of the two fixed data, either the full selected canonical component union or a smaller union preserved by the Hecke element under discussion. For a nonpreserving element, the identical construction has the Hecke translate of that union as its second target; it is then a correspondence between two integral models rather than a self-correspondence.

### 8.1 Integral Hecke data

Let $g\in G(\mathbf A_f^p)$. Put

$$
K_g^p=K^p\cap gK^pg^{-1}.
$$

There are generic maps from level $K_g^p$ to levels $K^p$ and $g^{-1}K^pg$, followed by the identification induced by $g$. On the middle space they carry a canonical prime-to-$p$ quasi-isogeny $u_g$ between the two universal abelian schemes. Since this is a PEL quasi-isogeny, there is a positive rational number $c_g$ such that

$$
u_g^\vee\lambda_2u_g=c_g\lambda_1
$$

on the generic fiber. Choose an integer $m\ge1$, prime to $p$, that clears the finitely many prime-to-$p$ denominators of $u_g$, its inverse, and $c_g$. Then $m u_g$ is a genuine prime-to-$p$ isogeny, its multiplier

$$
c(mg)=m^2c_g
$$

is a positive integer prime to $p$, and the corresponding map of prime-to-$p$ lattices is an inclusion with finite quotient. Applying the same construction to $g^{-1}$ gives an isogeny in the reverse direction; their composites are the recorded central multiplications. If $g$ changes the prime-to-$p$ polarization genus, the second generic map and its integral extension have the translated PEL type, exactly as in the component convention above.

The resulting correspondence is independent of $m$ at the rational Hecke level. Integral actions can differ by the explicit central multiplication factor, which must be retained whenever a coefficient prime divides $m$.

### 8.2 Quotients by finite étale kernels

Over a normal principal-level refinement of $\mathscr M_{K_g}$, the level structure identifies the finite lattice quotient determined by the chosen integral representative $mg$ with a finite locally free subgroup

$$
H_{mg}\subset\mathcal A[n],\qquad p\nmid n.                     \tag{8.1}
$$

The lattice quotient is $K_g^p$-stable, so this subgroup is invariant under the finite deck group and descends to $\mathscr M_{K_g}$. Because $n$ is invertible on the base, $\mathcal A[n]$ and $H_{mg}$ are finite étale. The quotient

$$
q_{mg}:\mathcal A\longrightarrow\mathcal A/H_{mg}.            \tag{8.2}
$$

exists as an abelian scheme and commutes with arbitrary base change. The $\mathcal O$-stability of the lattice inclusion makes $H_{mg}$ stable, so the order action descends. The dual-lattice relation in the PEL datum is precisely the finite-level isotropy condition for $c(mg)\lambda$; polarization descent therefore produces a unique polarization $\lambda'$ of the target PEL type (the translated type when $g$ changes the genus) satisfying

$$
q_{mg}^{\vee}\lambda' q_{mg}=c(mg)\lambda.                    \tag{8.3}
$$

Thus polarization type is not inferred from isotropy alone: it is fixed by the source and target PEL lattice genera and the explicit multiplier in (8.3).

Because $q_{mg}$ has degree prime to $p$, it is étale and induces an isomorphism on Lie algebras and on $p$-divisible groups. The descended $\mathcal O$-action therefore has the same determinant polynomial and ordered orientation packet, while the target prime-to-$p$ level is the one defined by the target lattice. Hence the quotient tuple satisfies every condition of the target integral PEL functor.

This is the point at which a rational quasi-isogeny becomes an integral morphism. Taking the schematic closure of its generic kernel would be unsafe over a higher-dimensional base; (8.1) constructs the kernel inside an already finite étale group scheme and proves flatness before quotienting.

### 8.3 The correspondence and its universal isogeny

The quotient tuple defines a second map, and we obtain

$$
\mathscr M_K
\xleftarrow{\ p_1\ }
\mathscr M_{K_g}
\xrightarrow{\ p_2\ }
\mathscr M_K.                                                     \tag{8.4}
$$

Both maps are finite étale at neat levels. Finiteness follows after the principal refinement from the finite set of level refinements and descends. Their completed deformation functors agree because a prime-to-$p$ isogeny identifies the $p$-divisible groups with all Hodge-filtration data, so the finite maps are étale. Over the middle space, (8.2) is the chosen integral multiple of the universal prime-to-$p$ Hecke quasi-isogeny between $p_1^*\mathcal A$ and $p_2^*\mathcal A$. Its generic fiber is $m u_g$; recovering $u_g$ rationally divides by the recorded central scalar $m$.

The graph of (8.4) is proper over both factors because the projections are finite. Hence (8.4) defines an integral algebraic correspondence even when the bases are not proper. Properness of the bases becomes necessary when one wants ordinary global cohomology to have specialization isomorphisms.

### 8.4 Composition, adjoints, and descent

If $g,h\in G(\mathbf A_f^p)$, pull the correspondences for $g$ and $h$ to the sufficiently small level

$$
K^p\cap gK^pg^{-1}\cap ghK^p(gh)^{-1}.
$$

The canonical quasi-isogenies compose as $u_hu_g=u_{gh}$. Chosen integral multiples compose with the product of their central denominators and may differ from a separately chosen normalization of $u_{gh}$ by an explicit central multiplication. After retaining that scalar, decomposing the finite fiber product into double cosets gives the usual convolution law. Thus the Hecke relations hold geometrically, while integral normalizations keep exactly the denominators already warned about in Section 8.1.

The polarization identifies the transpose of the $g$-isogeny, up to its explicit multiplier, with the correspondence for $g^{-1}$. Accordingly the cohomological adjoint of $T_g$ is the multiplier-normalized $T_{g^{-1}}$. Suppressing the multiplier would give an incorrect integral adjoint formula.

All constructions are equivariant under ordinary finite changes of level. There the universal isogeny descends to the quotient stack and descends to a coarse fine quotient when the universal object does. Hecke operators at $p$ are excluded: changing the hyperspecial $p$-lattice introduces $p$-power kernels, whose connected parts and parahoric local models require different geometry.

## 9. Étale cohomology of the good models

The geometric construction earns its name through specialization. Smoothness makes the family locally acyclic for prime-to-$p$ coefficients; properness prevents classes from escaping to infinity. Together they identify generic and special cohomology integrally.

### 9.1 Finite coefficients and specialization

Let $f:\mathscr M_K\to\operatorname{Spec}R$ be one of the proper models furnished by Theorem 6.4, let $\ell\ne p$, and put $\Lambda_n=\mathbf Z/\ell^n\mathbf Z$. Smooth proper base change gives lisse finite sheaves

$$
R^if_*\Lambda_n
$$

which become constant on the strictly henselian localization of $R$. They need not be free as $\Lambda_n$-modules when adjacent integral cohomology has $\ell$-torsion. Equivalently, a chosen geometric specialization gives canonical isomorphisms

$$
\operatorname{sp}_{n}^{i}:
H^i(\mathscr M_{K,\bar k},\Lambda_n)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E},\Lambda_n).                            \tag{9.1}
$$

The direction in (9.1) is from the closed geometric fiber to the geometric generic fiber because specialization of geometric points induces a map of étale topoi in that direction. Its inverse is often also called specialization; stating the displayed convention prevents ambiguity.

**Proof.** Proper base change identifies the geometric stalk of $R^if_*\Lambda_n$ at either point with the corresponding fiber cohomology. Smoothness makes $f$ universally locally acyclic relative to $\Lambda_n$, so the generization map between these stalks is an isomorphism. Combining the two identifications gives (9.1). $\square$

The theorem applies in every degree: $0\le i\le2$ for a curve and $0\le i\le4$ for a surface. It respects cup products because the base-change isomorphism is induced in the derived category before cohomology is taken.

### 9.2 Integral adic lattices

Passing from (9.1) to $\mathbf Z_\ell$ requires control of the inverse system. The groups at finite level are finite, the cohomological amplitude is uniformly bounded, and the transition maps arise from a normalized adic system. Therefore the derived inverse limit has no unwanted $R^1\varprojlim$ term, and

$$
\operatorname{sp}_{\ell}^{i}:
H^i(\mathscr M_{K,\bar k},\mathbf Z_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E},\mathbf Z_\ell).                      \tag{9.2}
$$

Here $H^i(-,\mathbf Z_\ell)$ means the cohomology of the derived inverse-limit coefficient system, not an unexamined inverse limit of abstract groups. Reduction modulo $\ell^n$ fits into the universal-coefficient exact sequence

$$
0\to H^i(\mathbf Z_\ell)/\ell^n
\to H^i(\Lambda_n)
\to H^{i+1}(\mathbf Z_\ell)[\ell^n]\to0.                       \tag{9.3}
$$

Thus $H^i(\Lambda_n)$ need not be the naive reduction of $H^i(\mathbf Z_\ell)$ when the next integral group has torsion. Isomorphism (9.2) remains valid because the entire derived systems are compared, not because torsion is assumed absent. Tensoring gives the corresponding $\mathbf Q_\ell$-comparison.

### 9.3 Abelian comparison and PEL coefficient systems

The universal abelian scheme can have arbitrary relative dimension, so a curve-only comparison theorem is not enough. We give the required calculation.

**Proposition 9.1 (abelian Betti--étale comparison in every dimension).** Let $A/\mathbf C$ be an abelian variety of dimension $g$. For every prime $\ell$, there are functorial cup-product-compatible isomorphisms

$$
H^j_{\mathrm{sing}}(A(\mathbf C),\mathbf Z_\ell)
\xrightarrow{\sim}
H^j_{\mathrm{\acute et}}(A,\mathbf Z_\ell)
\xrightarrow{\sim}
\bigwedge^j\operatorname{Hom}_{\mathbf Z_\ell}
(T_\ell A,\mathbf Z_\ell).
$$

They respect endomorphisms and polarization pairings. More generally, if $a:A\to S$ is an abelian scheme of relative dimension $g$ and $\ell$ is invertible on $S$, then

$$
R^ja_*\mathbf Z_\ell
\simeq
\bigwedge^jR^1a_*\mathbf Z_\ell,
\qquad
R^1a_*\mathbf Z_\ell
\simeq
\underline{\operatorname{Hom}}(T_\ell A,\mathbf Z_\ell),
$$

and these identifications commute with arbitrary base change on $S$.

**Proof.** Analytically, $A(\mathbf C)=W/\Gamma$, where $W\simeq\mathbf C^g$ is contractible and $\Gamma=H_1(A(\mathbf C),\mathbf Z)$ is free of rank $2g$. The cellular cochain complex of the real torus, equivalently the Koszul complex for a basis of $\Gamma$, gives

$$
H^j_{\mathrm{sing}}(A(\mathbf C),\mathbf Z/\ell^n)
\simeq
\bigwedge^j\operatorname{Hom}(\Gamma,\mathbf Z/\ell^n).
$$

On the algebraic side, every connected pointed finite étale cover of $A$ of $\ell$-power degree has a unique abelian-variety structure for which the covering map is an isogeny. Indeed translations lift after choosing a point above the origin, and rigidity makes the lifted addition, inverse, and identity laws unique and associative. Its finite $\ell$-primary kernel is killed by some $\ell^r$, so the multiplication covers $[\ell^r]:A\to A$ are cofinal among such covers.

This inverse tower is acyclic in positive degree for $\mathbf Z/\ell^n$-coefficients. Translation acts trivially on cohomology because the map from the connected variety $A$ to the finite automorphism group of a finite cohomology module is constant. Applying the cubical alternating-difference identity in $j+1$ variables then gives $[m]^*\alpha=m^j\alpha$ for $\alpha\in H^j$; with $m=\ell^r$ this vanishes once $rj\ge n$. The Cartan--Leray complex of the multiplication tower therefore computes étale cohomology as the continuous cohomology of $T_\ell A\simeq\mathbf Z_\ell^{2g}$ with trivial coefficients. The Koszul resolution of its commuting topological generators gives

$$
H^j_{\mathrm{\acute et}}(A,\mathbf Z/\ell^n)
\simeq
\bigwedge^j\operatorname{Hom}(A[\ell^n],\mathbf Z/\ell^n).
$$

The analytic points of $A[\ell^n]$ are $\ell^{-n}\Gamma/\Gamma$, so passage to the inverse limit identifies $T_\ell A$ with $\Gamma\otimes\mathbf Z_\ell$. The analytic and algebraic multiplication towers are the same finite covers, and their character maps agree in degree one. Their Koszul cup products therefore identify the two exterior algebras above. This proves Betti--étale comparison without restricting $g$. All constructions are functorial, so endomorphisms and the alternating form from a polarization are preserved.

The algebraic multiplication-tower argument used only that $\ell$ is invertible, so it applies over every separably closed field of characteristic different from $\ell$. For an abelian scheme, the finite-level character map and cup product define morphisms of constructible sheaves. Proper base change identifies every geometric stalk with that absolute calculation. Hence the morphisms are isomorphisms on every geometric stalk and therefore are isomorphisms of sheaves. Their finite free transition systems pass to $\mathbf Z_\ell$, and the stalk construction proves arbitrary base-change compatibility. $\square$

Let $a:\mathcal A\to\mathscr M_K$ be the universal abelian scheme on a fine PEL model. The lisse sheaf

$$
\mathbb V_\ell=R^1a_*\mathbf Z_\ell
\simeq\underline{\operatorname{Hom}}(T_\ell\mathcal A,\mathbf Z_\ell) \tag{9.4}
$$

is finite free and commutes with arbitrary base change. It carries the $\mathcal O$-action and, in this cohomological convention, an alternating form $\mathbb V_\ell\otimes\mathbb V_\ell\to\mathbf Z_\ell(-1)$ dual to the polarization pairing on $T_\ell\mathcal A$; this form is perfect when $\ell\nmid\deg\lambda$. Tensor products, duals, exterior powers, and direct summands cut out by integral idempotents produce lisse integral coefficient systems $\mathcal L_\ell$.

For each such system on the fine scheme and its finite reductions, smooth proper base change gives

$$
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E},\mathcal L_\ell).                    \tag{9.5}
$$

An idempotent with a denominator divisible by $\ell$ cuts out only a $\mathbf Q_\ell$-summand, not an integral direct summand. Integral comparison for that rational representation means comparison of a separately specified stable lattice, not automatic intersection with the ambient lattice.

The full cohomology of the universal abelian scheme also compares. Proper smoothness of the composite $\mathcal A\to\operatorname{Spec}R$ gives

$$
H^m(\mathcal A_{\bar k},\mathbf Z_\ell)
\simeq H^m(\mathcal A_{\bar E},\mathbf Z_\ell),                \tag{9.6}
$$

and the Leray spectral sequence has

$$
E_2^{ij}=H^i\left(\mathscr M_K,\bigwedge^j\mathbb V_\ell\right)
\Longrightarrow H^{i+j}(\mathcal A,\mathbf Z_\ell),
\qquad
R^ja_*\mathbf Z_\ell\simeq\bigwedge^j\mathbb V_\ell.          \tag{9.7}
$$

This identifies the terms controlling the Leray filtration; no integral degeneration or splitting of that spectral sequence is asserted. On an ordinary quotient stack with a genuine level linearization, the same formulas define lisse coefficient systems, but no separate stack-valued base-change theorem is imported here. If such a system descends to a smooth proper scheme quotient, the scheme theorem applies there.

### 9.4 Unramifiedness and Frobenius

The geometric generic cohomology in (9.2) carries an action of $\operatorname{Gal}(\bar E/E)$. After restriction to the chosen decomposition group at $v$, equivalently after base change to $E_v$, the lisse sheaf $R^if_*\mathbf Z_\ell$ on the trait has trivial inertia. Thus

$$
H^i(\mathscr M_{K,\bar E},\mathbf Z_\ell)
$$

is unramified at $v$, including its torsion. Under (9.2), arithmetic Frobenius on the generic representation corresponds to arithmetic Frobenius on the special fiber, and geometric Frobenius corresponds to its inverse.

This conclusion says neither that Frobenius is semisimple nor that its eigenvalues have a prescribed weight. Those assertions require separate purity results. Good reduction supplies the transport from Galois action to special-fiber geometry; it does not evaluate that geometry.

## 10. Hecke action and cohomological base change

The specialization isomorphism is useful only if it preserves the arithmetic operators used to isolate automorphic constituents. This chapter checks that compatibility at the level of correspondences.

### 10.1 Pull-push on a proper correspondence

For (8.4) and a finite coefficient ring $\Lambda$, define

$$
T_g=(p_2)_*p_1^*:
H^i(\mathscr M_{K},\Lambda)
\longrightarrow H^i(\mathscr M_{K},\Lambda).                  \tag{10.1}
$$

The pushforward is the finite étale trace. If the coefficient system comes from $\mathcal A$, insert between pullback and trace the morphism in the required variance induced by the normalized isogeny of Section 8.3. The isogeny is prime to $p$, but this morphism is an integral isomorphism on a $\mathbf Z_\ell$-system only when its degree is prime to $\ell$.

Formula (10.1) is defined in the derived category and hence respects long exact sequences and cup products with the usual projection formula. Its reduction to each fiber is the Hecke correspondence attached to the same double coset, since both projections and the normalized isogeny commute with base change.

### 10.2 Compatibility with specialization

**Theorem 10.1 (Hecke-equivariant specialization).** For every $g\in G(\mathbf A_f^p)$ that preserves the chosen component union, every $\ell\ne p$, and every integral PEL coefficient system on which the normalized universal isogeny acts, the square

$$
\begin{array}{ccc}
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)&\xrightarrow{T_g}&
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)\\
\downarrow\scriptstyle{\operatorname{sp}}&&\downarrow\scriptstyle{\operatorname{sp}}\\
H^i(\mathscr M_{K,\bar E},\mathcal L_\ell)&\xrightarrow{T_g}&
H^i(\mathscr M_{K,\bar E},\mathcal L_\ell)
\end{array}                                                       \tag{10.2}
$$

commutes.

**Proof.** Proper base change is functorial for pullback. It is also compatible with proper trace, as may be checked after strict localization where both traces are the sum over the same finite geometric fiber. The normalized isogeny and its map on coefficient systems are defined over the middle integral model, so their base changes appear in both rows. Composing these three compatible maps proves the square at finite level. Uniform boundedness and finiteness pass it to the derived $\mathbf Z_\ell$-limit. $\square$

### 10.3 Integral invertibility and denominators

Let $u:A\to B$ be an isogeny. On $T_\ell$, its determinant has $\ell$-adic valuation equal to the $\ell$-part of the kernel. Thus $u$ induces an isomorphism of integral cohomological local systems if $\ell\nmid\deg u$; for arbitrary $u$ it becomes an isomorphism only over $\mathbf Q_\ell$. The Hecke operator itself still acts integrally by pull-push, but a normalization involving $u^{-1}$ may introduce denominators.

Similarly, a rational projector $e=d^{-1}P(T_{g_1},\ldots,T_{g_r})$ cuts out an integral direct summand only if $d$ is a unit in $\mathbf Z_\ell$ and $e$ preserves the chosen lattice. Specialization commutes with $e$ whenever it is defined, but it cannot repair a nonintegral projector. This distinction is central when a two-dimensional Galois constituent is later extracted from a much larger cohomology group.

### 10.4 Curve and surface degrees

For a geometrically connected smooth proper curve $C$ of genus $g$,

$$
H^0(C,\mathbf Z_\ell)=\mathbf Z_\ell,
\qquad \operatorname{rank}H^1(C,\mathbf Z_\ell)=2g,
\qquad H^2(C,\mathbf Z_\ell)=\mathbf Z_\ell(-1).               \tag{10.3}
$$

The automorphic information of the quaternionic curve lies in degree one, while degrees zero and two carry the obvious component and orientation classes.

For a smooth proper surface $S$, the range is $0$ through $4$ and the middle degree is $2$. The unitary construction is designed so that the relevant parity occurs in $H^2$, but geometry alone does not isolate the desired packet. The Hecke-equivariant integral comparison preserves cup products and transports any projector that has already been constructed with controlled denominators. A perfect integral Poincaré-duality statement is not imported here, because Book 22 explicitly assigns that theorem to a later dependency.

## 11. Coherent and de Rham comparison

Prime-to-$p$ étale cohomology is the cleanest integral theory at a good prime. Coherent and de Rham cohomology also carry natural lattices, but their base-change behavior has additional hypotheses. Keeping the distinction visible prevents a false universal freeness claim.

### 11.1 Proper coherent cohomology

Let $f:\mathscr M_K\to\operatorname{Spec}R$ be proper and let $\mathcal F$ be a coherent sheaf flat over $R$. Properness makes every $R^if_*\mathcal F$ finite. For $R'=E$ or $k$, there is a base-change map

$$
(R^if_*\mathcal F)\otimes_RR'
\longrightarrow H^i(\mathscr M_{K,R'},\mathcal F_{R'}).        \tag{11.1}
$$

It is an isomorphism if the degree-$i$ base-change map is surjective; local freeness of $R^if_*\mathcal F$ additionally requires the adjacent degree condition. Over a DVR the universal-coefficient sequence makes the obstruction concrete:

$$
0\to H^i(\mathcal F)\otimes_R k
\to H^i(\mathcal F_k)
\to H^{i+1}(\mathcal F)[\pi]\to0.                              \tag{11.2}
$$

Thus torsion in the next coherent cohomology group creates special-fiber classes. Smooth properness of $f$ by itself does not eliminate that torsion for every $\mathcal F$.

For $\mathcal F=\mathcal O_C$ on the curve model with geometrically connected fibers, $f_*\mathcal O_C=R$ and $R^1f_*\mathcal O_C$ is finite locally free and commutes with arbitrary base change. Relative duality identifies its dual with $f_*\Omega^1_{C/R}$. This gives an unconditional integral Hodge lattice in degree one.

### 11.2 The Hodge bundles of the universal family

For the universal abelian scheme $a:\mathcal A\to\mathscr M_K$, invariant differentials form the locally free Hodge bundle

$$
\omega_{\mathcal A}=a_*\Omega^1_{\mathcal A/\mathscr M_K}.
$$

Its formation commutes with arbitrary base change, and the coherent cohomology algebra is

$$
R^ja_*\mathcal O_{\mathcal A}
\simeq\bigwedge^j R^1a_*\mathcal O_{\mathcal A}.
$$

The order action splits $\omega_{\mathcal A}$ into unramified idempotent packets. The active rank-one factors are line bundles $\mathcal L$ in the curve case and $\mathcal L_1,\mathcal L_2$ in the surface case. These decompositions are integral because the center is étale at $p$; at a ramified prime the required idempotents may exist only after inverting $p$.

The polarization identifies the complementary Hodge packets up to the similitude line. All these identifications commute with base change because they arise from the universal morphisms, not from choices of bases.

### 11.3 De Rham lattices and the torsion warning

The relative de Rham complex

$$
\Omega^\bullet_{\mathscr M_K/R}
$$

is a bounded complex of locally free sheaves. Since $f$ is proper smooth, its derived direct image

$$
Rf_*\Omega^\bullet_{\mathscr M_K/R}                             \tag{11.3}
$$

is perfect over $R$ and commutes with derived base change. Its cohomology modules

$$
H^i_{\mathrm{dR}}(\mathscr M_K/R)
=H^i\bigl(Rf_*\Omega^\bullet_{\mathscr M_K/R}\bigr)
$$

are therefore finite, but a cohomology module of a perfect complex over a DVR can have torsion. If the neighboring modules are torsion-free, ordinary base change yields

$$
H^i_{\mathrm{dR}}(\mathscr M_K/R)\otimes_RE
\simeq H^i_{\mathrm{dR}}(\mathscr M_{K,E}/E)                   \tag{11.4}
$$

and the analogous special-fiber isomorphism. Generic base change in (11.4) is always exact because $E/R$ is flat; integral comparison with $k$ requires the torsion test.

For curves, the Hodge-to-de Rham sequence gives an exact sequence of finite locally free modules

$$
0\to f_*\Omega^1_{C/R}
\to H^1_{\mathrm{dR}}(C/R)
\to R^1f_*\mathcal O_C\to0,                                   \tag{11.5}
$$

so degree-one de Rham cohomology is an unconditional lattice and commutes with base change. For surfaces, one must either verify the relevant coherent base-change conditions term by term or assume a degeneration theorem with its exact characteristic bound. We make no blanket assertion that all integral Hodge pieces of every surface are torsion-free.

Hecke correspondences act on (11.3) by pullback and coherent trace. Their actions commute with derived base change. Whenever ordinary cohomology is locally free, they therefore commute with the integral fiber comparison as well.

### 11.4 Completion and formal comparison

Let $\widehat R$ be the $v$-adic completion and $\mathscr M_n=\mathscr M_K\otimes_RR/\pi^{n+1}$. The theorem on formal functions gives, for every coherent $\mathcal F$,

$$
H^i(\mathscr M_K,\mathcal F)\widehat{\otimes}_R\widehat R
\xrightarrow{\sim}
\varprojlim_nH^i(\mathscr M_n,\mathcal F_n).                   \tag{11.6}
$$

At the derived level, (11.6) includes all Tor terms and is valid without assuming ordinary base change at each $n$. The universal objects considered here are already algebraic, so their completions automatically form compatible systems. Conversely, a polarized formal abelian scheme algebraizes by the ample-line criterion when its polarization is represented by a compatible formal ample line bundle, possibly after an fppf cover followed by descent. A polarization homomorphism on the special fiber alone does not supply such a compatible line and is not enough. Once the abelian scheme is algebraized, its group law, PEL endomorphisms, polarization morphism, and Hecke isogenies algebraize uniquely by proper full faithfulness.

This formal argument gives a second proof of uniqueness over $\widehat R$. It does not construct the model from the special fiber alone: an ample polarization and compatible deformation data on every thickening are essential.

## 12. The quaternionic curve model

We now collect the general construction in its one-dimensional form. The point is not just brevity; once properness is available, the curve case has stronger torsion-free coherent comparison and a single integral Kodaira--Spencer line.

### 12.1 Construction theorem

**Theorem 12.1 (direct quaternion-trace curve).** Let $B/F$ be a quaternion division algebra split at exactly one real place, and let $\mathscr D=(B,*,B,\psi_\delta,h)$ be the direct PEL realization of Book 127. Let $v\mid p$ be a good odd place for its exact integral data, let $K_p$ be the hyperspecial stabilizer of the selected self-dual lattice, and let $K^p$ be neat. Then the selected generic PEL curve has a smooth projective flat-closure model

$$
\mathscr C_K/\mathcal O_{E,v}
$$

of relative dimension one satisfying the healthy-regular extension property. It is unique within the fixed PEL presentation, represents the corresponding open-and-closed integral PEL subfunctor, and carries its universal abelian scheme. Every prime-to-$p$ change of level extends, as does every Hecke self-correspondence preserving the selected union; on the full component union this includes all prime-to-$p$ Hecke correspondences.

**Proof.** Theorem 3.1 constructs the ambient scheme and (3.5) its selected flat closure. Section 4.3 computes the direct datum's actual local model as $\mathbf P^1$. Theorem 5.1 and Section 5.2 therefore identify the flat closure with a smooth open-and-closed component union of relative dimension one. Proposition 6.3 excludes its Raynaud torus, and Theorem 6.4 gives projectivity. Theorem 5.2 gives the extension property and Section 5.4 gives uniqueness within this fixed PEL presentation. Universal and Hecke structures are built over the fine moduli scheme itself. $\square$

### 12.2 The integral Kodaira--Spencer line

Let $\mathcal U$ be the direct datum's active reduced rank-two bundle, let $\mathcal L\subset\mathcal U$ be its Hodge line, and put $\mathcal M=\det\mathcal U$ with its recorded determinant-and-multiplier character. The tangent calculation

$$
T_{\mathscr C_K/R}\simeq\operatorname{Hom}(\mathcal L,\mathcal U/\mathcal L)
$$

dualizes to the integral Kodaira--Spencer isomorphism

$$
\Omega^1_{\mathscr C_K/R}
\simeq\mathcal L^{\otimes2}\otimes\mathcal M^{-1}.             \tag{12.1}
$$

To prove (12.1), Proposition 4.1 first identifies the differential of the PEL deformation functor with the differential of its Hodge line: after a frame is chosen, an infinitesimal deformation is the graph of a unique map $\mathcal L\to\mathcal U/\mathcal L$. The frame directions are exactly the vertical tangent directions of the $G_R$-torsor $\pi$ in (4.1), so quotienting them identifies the tangent bundle of $\mathscr C_K$ with $\operatorname{Hom}(\mathcal L,\mathcal U/\mathcal L)$. This is the Kodaira--Spencer map; mere smoothness of the two arrows in (4.1) would not by itself make it an isomorphism. Dualizing on the framed space gives

$$
\Omega^1\simeq\mathcal L\otimes(\mathcal U/\mathcal L)^\vee
\simeq\mathcal L^{\otimes2}\otimes(\det\mathcal U)^{-1}.
$$

The construction is frame-change equivariant and identifies $\det\mathcal U$ with $\mathcal M$, so faithfully flat descent gives (12.1). A trivialization of $\mathcal M$ may be used only when the chosen determinant-and-multiplier level supplies one; no such trivialization is implicit.

Relative duality and (12.1) relate coherent degree-one cohomology to sections of an automorphic line. This relation is integral and base-change compatible because every bundle in (12.1) is locally free over $R$.

### 12.3 Cohomology and good reduction

Under Theorem 12.1, for every $\ell\ne p$, specialization gives a cup-product-compatible isomorphism equivariant for the Hecke algebra stabilizing the selected component union

$$
H^1(\mathscr C_{K,\bar k},\mathbf Z_\ell)
\xrightarrow{\sim}
H^1(\mathscr C_{K,\bar E},\mathbf Z_\ell).                      \tag{12.2}
$$

The right side is unramified. The same holds with every integral coefficient system constructed from the direct presentation's universal abelian scheme. Coherently, (11.5) compares the Hodge and de Rham lattices without an extra torsion hypothesis. Thus the fine direct-trace curve supplies an étale lattice, a de Rham lattice, and their Hecke actions. A comparison between the étale and de Rham lattices at the residue prime would require a separate integral $p$-adic comparison theorem and is not asserted here.

## 13. The unitary surface model

The surface construction shares the same formal architecture but has two active directions. Its middle cohomology is the geometric location needed by the parity repair in the modèles étranges construction.

### 13.1 Construction theorem

**Theorem 13.1.** Let $(G,X)$ be the standard compact unitary datum of Book 129, Definition 4.1 and Proposition 4.2, assume it is PEL-exact in the sense of Book 129, Definition 5.2, and require two signature-$(1,1)$ places and exact finite-adelic matching to the desired quaternionic inner form. Let $v\mid p$ be a good PEL place such that $p$ lies below no place in the recorded exceptional set, and let $K_p$ be hyperspecial and $K^p$ neat. Then the selected canonical unitary surface has a unique smooth projective model

$$
\mathscr S_K/\mathcal O_{E,v}
$$

of relative dimension two satisfying the extension property. It represents the integral unitary PEL functor, carries the auxiliary universal abelian scheme, and supports all prime-to-$p$ level maps and every Hecke self-correspondence preserving the selected union. On the full component union this includes all prime-to-$p$ Hecke correspondences.

**Proof.** Ambient representability and the generic comparison are Theorem 3.1 and (3.4), and (3.5) defines the selected flat closure. The integral local model is the product of the two active projective lines, so Theorem 5.1 and Section 5.2 identify that closure with a smooth open-and-closed surface. Book 129 constructs a finite place where the binary Hermitian plane is anisotropic; the good residue prime is outside that exceptional set. Proposition 6.3(2) therefore rules out the Raynaud torus, and Theorem 6.4 gives projectivity. The extension property, uniqueness within the fixed presentation, and the Hecke tower follow from the corresponding general theorems. $\square$

The finite-adelic matching remains indispensable for identifying the Hecke datum and the intended derived group. For the standard faithful $K$-module $V=W$, one anisotropic finite localization proves properness. No alternative faithful realization is included in Theorem 13.1.

### 13.2 Two tangent directions and canonical bundles

Choose a finite étale splitting extension $R'/R$. Over $R'$, let $\mathcal L_i\subset\mathcal U_i$ be the two active Hodge lines and $\mathcal M_i=\det\mathcal U_i$. Applying the filtration differential of Proposition 4.1 in both active packets gives

$$
\Omega^1_{\mathscr S_{K,R'}/R'}
\simeq
(\mathcal L_1^{\otimes2}\otimes\mathcal M_1^{-1})
\oplus
(\mathcal L_2^{\otimes2}\otimes\mathcal M_2^{-1}).            \tag{13.1}
$$

Taking determinants yields, over $R'$,

$$
\omega_{\mathscr S_{K,R'}/R'}
\simeq
\mathcal L_1^{\otimes2}\otimes\mathcal L_2^{\otimes2}
\otimes\mathcal M_1^{-1}\otimes\mathcal M_2^{-1}.             \tag{13.2}
$$

Galois can permute the two active packets, so neither $\mathcal L_i$ nor either summand in (13.1) need descend separately to $R$. Their direct sum is Galois invariant and descends as $\Omega^1_{\mathscr S_K/R}$; the product in (13.2) descends as $\omega_{\mathscr S_K/R}$. The common similitude condition can relate $\mathcal M_1$ and $\mathcal M_2$, but no simplification is made until such a relation is specified. These descended identifications commute with further unramified scalar extension and with prime-to-$p$ change of level.

### 13.3 Middle cohomology and auxiliary abelian schemes

Under Theorem 13.1, for $\ell\ne p$ there is an isomorphism equivariant for the Hecke algebra stabilizing the selected component union

$$
H^2(\mathscr S_{K,\bar k},\mathbf Z_\ell)
\xrightarrow{\sim}
H^2(\mathscr S_{K,\bar E},\mathbf Z_\ell).                     \tag{13.3}
$$

It preserves cup products and every pairing supplied by the integral PEL coefficient systems. The universal auxiliary abelian scheme produces lisse coefficient systems and endomorphism projectors, all transported by the same comparison when integrally defined. No independent perfect integral Poincaré-duality theorem is asserted from the present dependency list.

The word auxiliary remains mathematically important. Formula (13.3) compares the cohomology of the parameter surface. The exterior algebra of $R^1a_*\mathbf Z_\ell$ describes the fibers of the universal abelian scheme, not automatically the automorphic middle cohomology of $\mathscr S_K$. The later automorphic decomposition must use the acting group and Hecke algebra to isolate the desired rank-two packet.

Unlike the curve case, integral coherent Hodge groups of the surface can have torsion. Derived de Rham base change always holds, but an ordinary special-fiber Hodge decomposition requires the criteria of Section 11.3.

## 14. Integral comparison package

We can now state the reusable output without mixing the geometric, étale, and coherent hypotheses.

### 14.1 The geometric comparison theorem

**Theorem 14.1.** Let $\mathscr X$ be either the quaternionic curve $\mathscr C_K$ of Theorem 12.1 or the standard unitary surface $\mathscr S_K$ of Theorem 13.1. Then:

1. $\mathscr X/R$ is smooth and projective, of relative dimension one or two;
2. its generic fiber is the selected canonical Shimura variety;
3. at fine level it represents the PEL functor and carries the universal abelian scheme with all tensors;
4. it satisfies the healthy-regular extension property and is uniquely characterized by it within the fixed PEL presentation;
5. every prime-to-$p$ level map is finite étale, and every prime-to-$p$ Hecke double coset extends on the full component union to a finite correspondence on which a common-denominator multiple of the universal quasi-isogeny is an isogeny; on a smaller selected union it is a self-correspondence exactly when it preserves that union, and otherwise has the translated union as target;
6. for $\ell\ne p$, finite and adic étale cohomology of the base and of every integral PEL coefficient system satisfies smooth proper base change equivariantly for the stabilizer Hecke algebra (the full prime-to-$p$ Hecke algebra on the full component union);
7. coherent complexes that are flat over $R$, and the relative de Rham complex, satisfy proper finiteness and derived base change, while ordinary integral fiber comparison holds exactly under the adjacent-degree or torsion-freeness criteria of Chapter 11;
8. in the curve case, all these conclusions apply to the direct quaternion-trace realization specified in Theorem 12.1.

**Proof.** Statements 1--5 are Theorems 5.1, 6.4, 3.1, 5.2, and the constructions of Chapters 7--8. Statement 6 is (9.1)--(9.5) together with Theorem 10.1. Statement 7 follows from coherent cohomology and base change, perfection of the smooth proper de Rham complex, and the universal-coefficient sequence. Statement 8 is Theorem 12.1. $\square$

### 14.2 Functoriality for tensors and correspondences

Every comparison above is functorial for:

- the action of the integral order and its Rosati involution;
- the polarization pairing and Tate twist;
- cup products, Künneth morphisms, and Leray filtrations;
- integral idempotents and direct summands;
- finite étale changes of level;
- prime-to-$p$ Hecke pull-push maps and their transpose relations;
- unramified extension of the reflex local ring.

The proof is uniform. Each operation is a morphism in the relevant derived category over $R$. Base change is a natural transformation compatible with composition, tensor products, and proper trace. Checking equality after base change therefore reduces to equality before it. No choice of geometric basis enters.

### 14.3 Fixed-presentation scope

Every uniqueness, universal-family, coefficient-system, and extension-property assertion in this book is typed to one of the two fixed PEL data. For the curve this is the direct quaternion-trace realization; for the surface it is the standard realization of Book 129. The book makes no comparison with another faithful realization of either adjoint datum.

Within either fixed datum, prime-to-$p$ Hecke correspondences agree integrally when their generic graphs agree. Both graphs are finite étale over the base and hence $R$-flat; their ideals in the common separated product are $R$-saturated, so equality after inverting the uniformizer forces equality integrally. Constant-coefficient cohomology and the coefficient systems constructed from the fixed universal family are therefore functorial throughout the corresponding level tower.

## 15. Failure modes and the good-prime boundary

The construction is sharp enough to show what changes outside its hypotheses. These are not minor technical omissions: each failed condition produces a distinct geometric phenomenon.

### 15.1 Ramified orders and non-self-dual lattices

If $D\otimes\mathbf Q_p$ or its center is ramified, the order modulo $p$ can acquire nilpotents. Idempotent decompositions used to read off Hodge ranks disappear, and the determinant law may allow infinitesimal extensions between packets. The local model can be nonreduced or nonflat.

If $\Lambda_p\subsetneq\Lambda_p^\vee$, its stabilizer is generally parahoric. The Hodge submodule must then be compatible with a lattice chain, not a single self-dual lattice. The naive determinant model can have the wrong special fiber; wedge, spin, or refined determinant conditions may be required. None can be added uniformly without inspecting the exact datum.

For example, let $\Lambda=\mathbf Z_p^4$ and multiply a perfect rank-four symplectic form with matrix $J$ by $p$. Then $\Lambda^\vee=p^{-1}\Lambda$, so the stabilizer remembers a nontrivial lattice step. The naive local model asks for rank-two direct summands isotropic for $pJ$. Over $\mathbf Q_p$ this is the Lagrangian Grassmannian $\operatorname{LGr}(2,4)$, of dimension three, whereas reduction modulo $p$ annihilates the form and gives the whole $\operatorname{Gr}(2,4)$, of dimension four. Thus the naive model is not flat.

The rank-four example is essential: every line in an alternating plane is already isotropic, so scaling a rank-two pairing would not enlarge its line Grassmannian. The dimension jump above is the elementary local-model reason self-duality cannot be weakened silently.

At $p=2$, reduction of a skew-symmetry equation no longer forces zero diagonal in the special fiber, and unitary or orthogonal integral forms have additional parity and norm-ideal invariants. The present theorem excludes $p=2$. Section 2.2 explains why an independently verified perfect lattice and smooth local model would be genuinely new input rather than a consequence of rational unramifiedness.

### 15.2 Parahoric level and singular local models

A Hecke modification at $p$ changes the lattice chain. Its kernel can contain connected finite flat group schemes, so quotienting is no longer a finite étale operation. The corresponding local model often has several components meeting along singular strata. Even if the total space can be regularized, smooth proper base change is replaced by nearby cycles.

This explains why the prime-to-$p$ Hecke algebra acts integrally in this book while the $p$-Hecke correspondence has been excluded. The exclusion is geometric, not terminological.

### 15.3 Bad reduction and monodromy

If anisotropy fails or the chosen place is bad, a PEL abelian variety can acquire a toric part. The weight filtration in Section 6.2 is then nonzero, inertia acts nontrivially, and the specialization map

$$
H^i(X_{\bar k},\mathbf Z_\ell)
\longrightarrow H^i(X_{\bar E},\mathbf Z_\ell)
$$

need not be an isomorphism. Proper base change still identifies the special-fiber group with the stalk of the direct image, but smooth local acyclicity has failed. Nearby cycles record the missing classes and monodromy operator.

Similarly, for a nonproper Shimura variety, classes can enter through the boundary even when the open morphism is smooth. A smooth compactification with a controlled normal-crossings boundary can recover compactly supported comparison, but it is a different theorem. Proposition 6.3 excludes the boundary for the direct one-active-place quaternionic curve and for the standard unitary surface. If the quaternion algebra ceases to be division or the faithful module is changed, the direct rank argument no longer applies.

## 16. The good integral-model theorem

The separate arguments can now be assembled into one theorem with every hypothesis visible.

### 16.1 Unified statement

**Theorem 16.1 (good integral models of the selected Shimura curves and surfaces).** Let $(G,X)$ be either:

1. the direct quaternion-trace PEL realization $\mathscr D=(B,*,B,\psi_\delta,h)$ of Book 127, where $B/F$ is a quaternion division algebra split at exactly one real place; or
2. the standard compact unitary datum of Book 129, Definition 4.1 and Proposition 4.2, PEL-exact in the sense of its Definition 5.2, with exactly two active signature-$(1,1)$ factors.

Let $E$ be its reflex field, let $v\mid p$, and assume:

- the exact rational PEL realization and a decomposition-group-stable canonical component union are fixed;
- $p$ is odd;
- in case 1, $F$ is unramified at $p$, $B$ is split at every place above $p$, the direct trace order is maximal and involution-stable, the alternating lattice is self-dual, the polarization degree is a unit, the stabilizer is reductive and hyperspecial, and the determinant, multiplier-component, and orientation labels extend over $R$;
- in case 2, the center is unramified at $p$, the acting order is maximal and involution-stable, the alternating lattice is self-dual, the polarization degree is prime to $p$, the stabilizer is reductive and hyperspecial, the two active determinant-and-orientation packets are the split unitary planes of Chapter 4, and every definite packet retains its recorded fixed label;
- $K^p$ is neat or a full level $N\ge3$ with $(N,p\deg\lambda)=1$ is imposed;
- in case 2, the rational prime $p$ lies below no place in the recorded exceptional set containing the finite anisotropic localization.

Let $\mathscr M_K^{\mathrm{amb}}$ be the ambient fine PEL scheme and let $\mathscr M_K$ be the schematic flat closure of the selected generic union. Then $\mathscr M_K$ is an open-and-closed subscheme of $\mathscr M_K^{\mathrm{amb}}$ and is smooth and projective over $\mathcal O_{E,v}$, of relative dimension one in case 1 and two in case 2. It represents the corresponding open-and-closed integral PEL subfunctor, carries the universal abelian scheme and all PEL tensors, satisfies the healthy-regular extension property, and is unique within its fixed PEL presentation. It commutes with unramified base change. If the whole ambient generic fiber is selected, then $\mathscr M_K^{\mathrm{amb}}=\mathscr M_K$; otherwise no such equality is implicit.

For every $g\in G(\mathbf A_f^p)$, the Hecke correspondence extends on the full canonical component union, and a prime-to-$p$ common-denominator multiple of its universal quasi-isogeny extends on the fine middle space as an isogeny with the recorded similitude multiplier. It restricts to a self-correspondence of $\mathscr M_K$ exactly when $g$ preserves the selected union; otherwise it is a correspondence to the integral model of the Hecke translate. For every $\ell\ne p$ and every integrally defined PEL coefficient system $\mathcal L_\ell$ on the fine model, the chosen geometric specialization gives a canonical isomorphism

$$
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E_v},\mathcal L_\ell),                  \tag{16.1}
$$

compatible with products, pairings, tensors, level change, and the stabilizer Hecke algebra; for the full component union it is equivariant for the full prime-to-$p$ Hecke algebra. The generic representation is unramified at $v$. Derived cohomology of coherent $R$-flat sheaves, and relative de Rham cohomology, also commute with base change; ordinary integral coherent comparison is subject to the precise torsion criteria of Chapter 11, and is unconditional in degree one for the curve's structure sheaf and de Rham complex.

This is the unconditional scope supplied by the direct prerequisites: the direct Book 127 quaternion-trace curve and the standard Book 129 unitary surface. At $p=2$, the direct curve's torus-rank argument and the projective-closure trait proof still establish flat-closure properness once the required integral moduli functor and full auxiliary level are available. They do not establish ambient smoothness. The smooth good-model theorem above therefore remains odd unless the exact dyadic order, lattice, determinant-orientation, and local model are independently verified; the standard surface has the additional dyadic Hermitian-lattice issue described in Section 2.2.

### 16.2 Proof architecture

The proof has a strict order.

First, integral tensors define the ambient finite-type PEL scheme and its universal family, while the chosen generic canonical union defines its schematic flat closure. Second, the framed deformation diagram reduces the ambient completed local rings to the actual integral local model. The direct trace datum has one moving alternating projective line; the standard surface has two moving Hermitian lines. This proves ambient smoothness and identifies the flat closure with an open-and-closed smooth component union. It is logically separate from properness.

Third, Book 40 supplies potential semistable reduction and the Raynaud one-motive. For the direct curve, $X_*(T)_{\mathbf Q}$ is a unital left $B$-module; its dimension cannot fit inside the direct homology $V=B$. Proposition 6.2 records the same toric contribution as the positive $J_T$-block (6.5). For the standard surface, the recorded finite anisotropic localization gives the obstruction of Proposition 6.1. Full odd auxiliary level and the congruence lemma descend actual good reduction to the original trait.

Fourth, the projective-closure trait argument proves properness of the **flat closure** for both fixed data. Only after combining this with the independent local-model result do we obtain a smooth projective fine model. Extension of abelian schemes, homomorphisms, polarizations, determinant orientation, and finite étale level gives the extension property and uniqueness within the fixed presentation. Fifth, ordinary prime-to-$p$ lattice modifications extend the Hecke isogenies. Finally, smooth proper base change, Proposition 9.1, derived inverse limits, and functorial trace give (16.1) with its integral Hecke structure wherever the coefficient system is defined.

No arrow in this chain can be reversed without adding a hypothesis. Generic representability does not prove the local model smooth; smoothness does not prove properness; the rational direct-trace form does not by itself identify a dyadic integral lattice; and rational Hecke equivariance does not control denominators.

### 16.3 Conclusion

At a good odd prime, the direct quaternion-trace PEL curve and the standard unitary surface are not merely varieties with fortunate reduction. Their exact order, lattice, determinant, multiplier, and orientation data produce smooth flag local models. If the direct curve's universal abelian scheme tried to escape into a semiabelian boundary, its nonzero Raynaud cocharacter module would be too large to fit inside $V=B$; the positive $J_T$-block makes the same Hodge-theoretic obstruction explicit. For the surface, the torus would produce an isotropic vector at the recorded anisotropic localization. The fine flat-closure models are therefore smooth, projective, functorial in level, and uniquely characterized by extension within each fixed presentation.

This geometry carries its arithmetic structures intact. Universal abelian schemes, endomorphisms, polarizations, Hodge bundles, and prime-to-$p$ Hecke isogenies all live over the local reflex ring. Once properness is known, prime-to-$p$ étale cohomology specializes with its integral lattice and the stabilizer Hecke algebra, which is the full prime-to-$p$ Hecke algebra on the full component union; coherent and de Rham lattices specialize exactly when their visible torsion criteria permit it. The curve contributes its degree-one package, and the modèles étranges surface contributes its degree-two package.

The promised curve-and-surface good-reduction package is therefore complete for the two fixed faithful realizations. Bad primes begin precisely where a lattice chain, unresolved dyadic integral data, a genuine boundary, or nontrivial monodromy replaces this constant smooth picture.
