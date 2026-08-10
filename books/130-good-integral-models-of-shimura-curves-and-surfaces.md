# Good Integral Models of Shimura Curves and Surfaces

## Contents

- [1. The good-reduction problem](#1-the-good-reduction-problem)
  - [1.1 From a canonical model to arithmetic geometry](#11-from-a-canonical-model-to-arithmetic-geometry)
  - [1.2 The two families and the dependency boundary](#12-the-two-families-and-the-dependency-boundary)
  - [1.3 Conventions and the meaning of good](#13-conventions-and-the-meaning-of-good)
- [2. Good integral PEL data](#2-good-integral-pel-data)
  - [2.1 A local datum at a finite place](#21-a-local-datum-at-a-finite-place)
  - [2.2 Unramified algebras, self-dual lattices, and hyperspecial level](#22-unramified-algebras-self-dual-lattices-and-hyperspecial-level)
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
  - [4.3 The quaternionic line](#43-the-quaternionic-line)
  - [4.4 The two unitary lines](#44-the-two-unitary-lines)
- [5. Smoothness and extension properties](#5-smoothness-and-extension-properties)
  - [5.1 Formal smoothness from filtration lifting](#51-formal-smoothness-from-filtration-lifting)
  - [5.2 Dimensions, regularity, and flatness](#52-dimensions-regularity-and-flatness)
  - [5.3 The extension property](#53-the-extension-property)
  - [5.4 Uniqueness of the good model](#54-uniqueness-of-the-good-model)
- [6. Properness in the compact cases](#6-properness-in-the-compact-cases)
  - [6.1 The missing step in the valuative criterion](#61-the-missing-step-in-the-valuative-criterion)
  - [6.2 Semiabelian degeneration and isotropic subspaces](#62-semiabelian-degeneration-and-isotropic-subspaces)
  - [6.3 Potential good reduction](#63-potential-good-reduction)
  - [6.4 Descent and the properness theorem](#64-descent-and-the-properness-theorem)
- [7. Fine levels, quotient levels, and base change](#7-fine-levels-quotient-levels-and-base-change)
  - [7.1 Change of prime-to-$p$ level](#71-change-of-prime-to-p-level)
  - [7.2 Finite étale covers and quotient stacks](#72-finite-etale-covers-and-quotient-stacks)
  - [7.3 Universal families at coarse level](#73-universal-families-at-coarse-level)
  - [7.4 Extension of scalars](#74-extension-of-scalars)
- [8. Prime-to-residue-characteristic Hecke correspondences](#8-prime-to-residue-characteristic-hecke-correspondences)
  - [8.1 Integral Hecke data](#81-integral-hecke-data)
  - [8.2 Quotients by finite étale kernels](#82-quotients-by-finite-etale-kernels)
  - [8.3 The correspondence and its universal isogeny](#83-the-correspondence-and-its-universal-isogeny)
  - [8.4 Composition, adjoints, and descent](#84-composition-adjoints-and-descent)
- [9. Étale cohomology of the good models](#9-etale-cohomology-of-the-good-models)
  - [9.1 Finite coefficients and specialization](#91-finite-coefficients-and-specialization)
  - [9.2 Integral adic lattices](#92-integral-adic-lattices)
  - [9.3 Coefficient systems from the universal abelian scheme](#93-coefficient-systems-from-the-universal-abelian-scheme)
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
  - [14.3 Independence of the chosen good presentation](#143-independence-of-the-chosen-good-presentation)
- [15. Failure modes and the good-prime boundary](#15-failure-modes-and-the-good-prime-boundary)
  - [15.1 Ramified orders and non-self-dual lattices](#151-ramified-orders-and-non-self-dual-lattices)
  - [15.2 Parahoric level and singular local models](#152-parahoric-level-and-singular-local-models)
  - [15.3 Bad reduction and monodromy](#153-bad-reduction-and-monodromy)
- [16. The good integral-model theorem](#16-the-good-integral-model-theorem)
  - [16.1 Unified statement](#161-unified-statement)
  - [16.2 Proof architecture](#162-proof-architecture)
  - [16.3 Conclusion](#163-conclusion)

## 1. The good-reduction problem

The complex points of a Shimura curve or surface are described by a double quotient, and its canonical model supplies a variety over a number field. Neither description answers the question asked at a finite prime: is there a model over the local ring whose special fiber is as regular as the generic fiber, and do the moduli objects and correspondences survive reduction? This book answers that question at the primes where the PEL datum is unramified and the level is hyperspecial.

### 1.1 From a canonical model to arithmetic geometry

Let $E$ be the reflex field and $v$ a finite place of $E$ above the rational prime $p$. If $X/E$ is a canonical Shimura curve or surface, a model $mathscr X/mathcal O_{E,v}$ is useful only if it carries more than the same function field. We require it to be smooth, to have the correct moduli interpretation, and, in the compact cases considered here, to be proper. At fine level it should carry an abelian scheme

$$
 a:\mathcal A\longrightarrow\mathscr X
$$

with its prescribed order action, polarization, determinant law, and level structure. Prime-to-$p$ Hecke maps should extend to finite correspondences and their generic universal quasi-isogenies should become genuine isogenies after a harmless common denominator is chosen.

These geometric demands have a cohomological purpose. For every prime $\ell\ne p$, smooth proper base change should identify the integral $\mathbf Z_\ell$-cohomology of a geometric generic fiber with that of a geometric special fiber. The identification must respect cup products, the PEL tensors, coefficient systems, and Hecke operators. It then follows that the generic Galois representation is unramified at $v$ and that arithmetic Frobenius may be computed on the special fiber.

There are three possible logical shortcuts, and all are wrong. A smooth generic fiber does not force a smooth integral closure. A proper generic fiber does not by itself make a chosen integral moduli scheme proper. Finally, comparison with $\mathbf Q_\ell$-coefficients does not automatically preserve a preferred $\mathbf Z_\ell$-lattice. Each issue receives a separate proof below.

### 1.2 The two families and the dependency boundary

Two PEL realizations are fixed from the preceding constructions.

The first is quaternionic. Its adjoint real group has exactly one noncompact rank-one factor, so its generic moduli space is a curve. The second is the unitary PEL realization supplied by the modèles étranges construction. It has two active signature-$(1,1)$ factors, so its generic moduli space is a surface. In both cases the actual dimension of the universal abelian scheme can be much larger than the dimension of the parameter space.

We use the established representability theorem for a neat PEL level, the universal abelian family, the generic local-model calculation, extension of homomorphisms and polarizations between abelian schemes over normal bases, coherent cohomology in proper families, algebraization of proper formal schemes, and proper and smooth base change for finite and adic étale coefficients. We do not assume the conclusion of this book. In particular, generic smoothness from the earlier local model is not integral smoothness, and generic projectivity is not integral properness.

The bad-prime geometry is not part of the present construction. A parahoric lattice chain, a non-self-dual lattice, or a semiabelian special fiber gives nearby cycles and monodromy rather than the constant specialization proved here. Those phenomena belong after the good model has been isolated.

### 1.3 Conventions and the meaning of good

All schemes are locally noetherian when coherent or infinitesimal arguments are used. Write $R=\mathcal O_{E,v}$, $K=\operatorname{Frac}(R)$, and $k=k(v)$. The symbols $\bar K$ and $\bar k$ denote separable algebraic closures together with a chosen geometric specialization $\bar K\rightsquigarrow\bar k$. A trait means the spectrum of a discrete valuation ring.

A **good PEL place** is not merely a place at which the generic variety happens to have good reduction. It is a place satisfying the integral tensor conditions in Chapter 2. In particular, the acting algebra is unramified at $p$, the alternating lattice is self-dual, the polarization degree is a unit, the local group extends to a reductive group scheme, the $p$-level is hyperspecial, and the integral determinant local model is the expected smooth flag variety. We will sometimes invert $2$ to avoid confusing alternating and skew-symmetric integral forms; if $p=2$, goodness includes the stronger explicit perfect-alternating and smooth-local-model hypotheses.

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

### 2.2 Unramified algebras, self-dual lattices, and hyperspecial level

The words in the preceding definition have concrete content. We require:

1. the center of $D\otimes\mathbf Q_p$ is a product of unramified extensions of $\mathbf Q_p$;
2. $D\otimes\mathbf Q_p$ is split over those centers in the factors active in the local model, and $\mathcal O\otimes\mathbf Z_p$ is a maximal Azumaya order;
3. the involution preserves that order and is unramified;
4. the map $\Lambda_p\to\Lambda_p^\vee$ induced by $\psi$ is an isomorphism;
5. the prescribed polarization type has degree prime to $p$.

These conditions are sufficient in the curve and surface data used here because Morita equivalence reduces the deformation problem to one or two ordinary rank-two multiplicity modules. More generally, unramifiedness of the algebra and self-duality of the lattice do not alone prove that a determinant local model is smooth. Ramified unitary signatures and certain residue-characteristic-two forms show why smoothness of the actual local model remains a separate condition.

Self-duality has two roles. It makes the polarization pairing perfect on de Rham homology, so isotropic direct summands lift cleanly. It also makes the stabilizer reductive; an almost self-dual lattice typically has a parahoric, rather than hyperspecial, stabilizer. Thus replacing self-duality by a finite-index inclusion changes the geometry rather than merely its notation.

A split quaternionic factor gives the basic local example. Let $F_w/\mathbf Q_p$ be unramified, take $D_w=M_2(F_w)$ and $\mathcal O_w=M_2(\mathcal O_{F_w})$, and use the adjoint involution for a perfect alternating form. On a self-dual module, Morita equivalence removes the matrix factor and leaves a free rank-two multiplicity module. Choosing its Hodge line gives $\mathbf P^1_{\mathcal O_{F_w}}$.

For the unitary example, let $K_w/F_w$ be unramified quadratic and give $K_w^2$ the split Hermitian form with matrix

$$
\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

The lattice $\mathcal O_{K_w}^2$ is self-dual, its unitary similitude group is unramified, and a signature-$(1,1)$ determinant condition again selects one line. Two independent places or embedding packets of this form give the product of projective lines used for the surface.

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

At an unramified place the embeddings of the center form finite étale packets. Their idempotents split the de Rham module, and $r$ prescribes the rank of the Hodge quotient in every packet. For the quaternionic curve exactly one multiplicity plane has rank pattern $(1,1)$; for the unitary surface exactly two do. All remaining packets are fixed. This is the integral source of the one- and two-dimensional local models.

### 2.4 A hypothesis ledger for curves and surfaces

Fix a compact open level

$$
K^{p}\subset G(\mathbf A_f^p),\qquad K=K_pK^p.
$$

The good-model theorem will use the following ledger.

- The rational PEL realization is exactly the quaternionic datum or the unitary modèles étranges datum already identified with its canonical model.
- The level $K^p$ is neat, or a full level $N\ge3$ with $p\nmid N$ is imposed, so the moduli problem has no inertia.
- The order, lattice, form, polarization type, determinant polynomial, and orientation extend over $R$ as above.
- The group $G_{\mathbf Z_p}$ is reductive and the integral local model is the smooth product of the active projective lines.
- The selected union of generic connected components is stable under the decomposition group at $v$; the integral model means the corresponding open-and-closed union.
- For properness, the underlying adjoint datum is anisotropic over $\mathbf Q$ modulo center. This holds for the compact quaternionic and compact unitary cases selected here.

If the component condition is omitted, one still constructs the full moduli scheme, but an arbitrarily chosen geometric component need not descend to $R$. If neatness is omitted, the natural smooth object is a Deligne--Mumford stack; its coarse scheme can acquire quotient singularities even at a good prime.

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

An arrow is an isomorphism of abelian schemes preserving every structure. The integral problem uses isomorphisms, not prime-to-$p$ quasi-isogenies, as arrows. Quasi-isogenies enter Hecke correspondences later. At full level $N$, the level is an actual symplectic $\mathcal O/N\mathcal O$-linear trivialization of $A[N]$; since $p\nmid N$, this group scheme is finite étale over $S$.

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

**Theorem 3.1 (integral representability).** Under the ledger of Section 2.4, the fine PEL functor is represented by a quasi-projective $R$-scheme $\mathscr M_K$ of finite presentation. It carries a universal tuple

$$
(\mathcal A,\iota^{\mathrm{univ}},\lambda^{\mathrm{univ}},
\bar\eta^{p,\mathrm{univ}}).                                   \tag{3.3}
$$

**Proof strategy.** One embeds the problem finitely over a Siegel moduli scheme with the same polarization type and a sufficiently rigid prime-to-$p$ level. The additional action and determinant conditions are algebraic and bounded.

**Proof.** A high tensor power of a relatively ample bundle inducing a fixed multiple of the polarization gives a uniform projective embedding of every object. The Hilbert scheme of the resulting fibers, together with the group-law equations, gives a finite-type framed atlas. Homomorphisms representing the action of a finite basis of $\mathcal O$ form closed subschemes; the multiplication table, Rosati relation, and universal determinant identity are closed equations. The fixed finite étale level is represented by a finite étale isomorphism scheme.

Forgetting the order action to the rigid Siegel scheme is finite. Quasi-finiteness follows from rigidity of homomorphisms and the Rosati norm bound; properness follows from extension of homomorphisms between abelian schemes over a DVR. A finite algebraic space over a scheme is a scheme. Full level at least three kills automorphisms, and an arbitrary neat level is a free finite quotient of such a principal-level scheme. Hence the result is a quasi-projective scheme of finite presentation. Its identity map is, by Yoneda, the universal object (3.3). $\square$

The theorem does not yet assert smoothness or properness. It only constructs the correct algebraic carrier.

### 3.4 Generic-fiber comparison

Base change of the moduli problem from $R$ to $K$ recovers the previously constructed PEL functor, because the integral lattice and order become the rational tensors and the prime-to-$p$ level together with $K_p$ recovers $K$. Therefore

$$
 \mathscr M_K\otimes_RK\simeq\operatorname{Sh}_K(G,X),         \tag{3.4}
$$

for the chosen open-and-closed union of canonical components. The isomorphism is over $K=E_v$, not merely over $\mathbf C$: both sides have canonical-model descent, and the complex moduli identification respects the reciprocity action on connected components.

The universal object on the generic fiber agrees with the earlier universal PEL abelian variety. If the Shimura variety is described through the unitary modèles étranges construction, this abelian variety remains auxiliary: its endomorphism action realizes the required group, but its first cohomology is not automatically the desired rank-two automorphic representation.

## 4. The good local model

Representability reduces geometry to deformation theory. The decisive fact at a good prime is that the integral flag problem is already smooth; no singularity is hidden in reduction of the determinant equations.

### 4.1 Why a determinant equation is not enough

Let $x$ be a geometric point of characteristic $p$. A first-order deformation of its Hodge subbundle in (3.2) is a graph

$$
u:F\longrightarrow H/F.
$$

The conditions that $F$ be $\mathcal O$-stable, isotropic, and of the prescribed determinant type are linear to first order. Merely subtracting the number of equations from the dimension of a Grassmannian would assume that these linear equations have constant rank. At ramified primes they often do not.

Goodness supplies a stronger description. The unramified center splits étale-locally on $R$, the Azumaya order is removed by Morita equivalence, and the determinant law fixes all multiplicity modules except the active rank-two planes. Thus the local model is visibly a product of Grassmannians of lines. This proves flatness, smoothness, and the tangent dimension at once.

### 4.2 The framed local-model diagram

The integral deformation input deserves an explicit statement because the characteristic-zero filtration theorem alone would not control the special fiber.

**Proposition 4.1 (integral Hodge-filtration lifting).** Let $S_0\hookrightarrow S$ be a square-zero thickening of local Artinian $R$-schemes, and let $A_0/S_0$ be an abelian scheme. There is a finite locally free evaluation $H$ over $S$ reducing to $H_{1,\mathrm{dR}}(A_0/S_0)$ such that deformations of $A_0$ to $S$ are equivalent to locally direct-summand lifts

$$
F\subset H
$$

of $\omega_{A_0^\vee}\subset H_{1,\mathrm{dR}}(A_0/S_0)$. Under this equivalence, an endomorphism lifts exactly when $F$ is stable, and a prime-to-$p$ polarization lifts exactly when $F$ is isotropic for the lifted perfect alternating form. Prime-to-$p$ level lifts uniquely.

**Proof strategy.** At a closed point of characteristic $p$, square-zero thickenings carry the canonical divided powers, and one evaluates the covariant Dieudonné crystal of $A_0[p^\infty]$. At a characteristic-zero point, the universal vector extension gives the same statement. The PEL conditions are then read on the filtration.

**Proof.** Suppose first that $p$ is nilpotent on $S$. The square-zero ideal $I$ has divided powers $\gamma_1(x)=x$ and $\gamma_n(x)=0$ for $n\ge2$. Evaluate the covariant crystal of the $p$-divisible group $A_0[p^\infty]$ on $S_0\hookrightarrow S$; call the resulting module $H$. Crystalline rigidity identifies its reduction with de Rham homology and supplies the exact filtration on $S_0$. Locally lift a basis of the Hodge subbundle to $H$. Such a lift defines a direct summand precisely when its maximal minors generate the unit ideal.

To see effectivity rather than only necessity, work successively through a composition series of $I$. On a square-zero step, two lifts of the $p$-divisible group differ by a homomorphism from the Hodge subbundle to its quotient tensored with $I$. The same Hom module acts simply transitively on graph lifts of the filtration. Starting from one local lift, subtracting the graph difference makes its crystalline filtration equal to the prescribed $F$. The rigidity of homomorphisms of $p$-divisible groups makes these local lifts and their descent isomorphisms satisfy the cocycle. The deformation theorem for abelian schemes identifies deformations of $A_0$ with deformations of its $p$-divisible group over nilpotent thickenings, so the lifted group is effective as a unique abelian-scheme deformation.

If the local Artinian ring has characteristic-zero residue field, $p$ is invertible. The Lie algebra of the universal vector extension of $A_0$ is de Rham homology. Lifting its distinguished vector subgroup is again the choice of $F$, and quotienting reconstructs the abelian scheme. Thus the crystalline argument covers closed points above $p$, while the universal-extension argument covers the generic fiber.

An endomorphism acts on the crystal or universal extension and descends to the reconstructed quotient exactly when it preserves $F$. A polarization gives a perfect alternating form because its degree is a unit; its lift is a polarization exactly when $F$ is isotropic, while positivity is unchanged under a nilpotent thickening. Finally, finite étale schemes have a unique lift through nilpotent thickenings, proving the assertion about level. $\square$

Let $\widetilde{\mathscr M}_K$ classify a PEL object together with an $\mathcal O\otimes R$-linear symplectic frame of its de Rham homology by $\Lambda\otimes R$. There is a diagram

$$
\mathscr M_K\xleftarrow{\ \pi\ }
\widetilde{\mathscr M}_K
\xrightarrow{\ \varphi\ }M^{\mathrm{loc}}.                    \tag{4.1}
$$

Here $\pi$ is a torsor under the reductive smooth group $G_R$, and $\varphi$ sends a frame to the framed Hodge subbundle. Both maps are smooth. Smoothness of $\pi$ is the torsor property. For $\varphi$, Proposition 4.1 says that a lifted stable isotropic filtration with the determinant law reconstructs a unique local deformation of the abelian scheme with its endomorphisms and polarization. A frame lifts locally under the smooth group.

Since the schemes are finitely presented, formal smoothness is smoothness. Thus $\mathscr M_K$ and $M^{\mathrm{loc}}$ have the same completed local singularities up to formally smooth variables. This argument uses the integral deformation theorem for abelian schemes; it is not an inference from the generic local-model diagram.

### 4.3 The quaternionic line

In the quaternionic case, Morita equivalence makes the active piece of $\Lambda\otimes R'$ over an étale splitting ring $R'$ equal to $W\otimes U$, where $W$ is the fixed simple module and $U$ is free of rank two. A stable Hodge submodule is $W\otimes L$ for a line subbundle $L\subset U$. Every line in a rank-two alternating multiplicity plane is isotropic. Hence

$$
 M^{\mathrm{loc}}_{R'}\simeq\mathbf P(U)\simeq\mathbf P^1_{R'}. \tag{4.2}
$$

Descent from $R'$ gives a smooth projective $R$-form of this flag variety. Its tangent space at $L$ is

$$
\operatorname{Hom}(L,U/L),
$$

free of rank one. All inactive factors have a unique filtration of the prescribed type and contribute no tangent direction.

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
\mathscr M_K\longrightarrow\operatorname{Spec}R
$$

is smooth. Its relative dimension is one in the quaternionic case and two in the unitary case.

**Proof.** In (4.1), $\pi$ is smooth and surjective, $\varphi$ is smooth, and $M^{\mathrm{loc}}/R$ is smooth by (4.2) or (4.3). Therefore $\widetilde{\mathscr M}_K/R$ is smooth. Smoothness descends through the smooth surjection $\pi$, proving that $\mathscr M_K/R$ is smooth. Relative dimensions may be computed on completed local rings or after the étale splitting: the moduli tangent directions equal those of the local model because the frame directions occur on both sides of (4.1). They have ranks one and two by (4.2) and (4.4). $\square$

One can see the decisive infinitesimal step directly. Given a square-zero extension $S_0\hookrightarrow S$ and a PEL object over $S_0$, étale-locally on $S$ its Hodge filtration corresponds to one or two lines. A line direct summand of a free rank-two module lifts by lifting one unimodular generator, and it remains a direct summand because one coordinate stays a unit. The lifted lines reconstruct the PEL object. There is therefore no obstruction group.

### 5.2 Dimensions, regularity, and flatness

Smoothness over the DVR $R$ implies flatness and regularity. Every irreducible component of $\mathscr M_K$ has dimension two in the curve case and three in the surface case; every geometric fiber is smooth and pure of dimension one or two. The special fiber is reduced, and formation of the relative cotangent bundle commutes with arbitrary base change.

These conclusions do not require the model to be connected. The orientation and determinant conditions used in defining the functor select an open-and-closed integral union; after properness is known, the finite étale component sheaf shows directly that its geometric components vary locally constantly.

### 5.3 The extension property

The natural uniqueness principle for an integral canonical model tests maps from regular schemes on which abelian varieties cannot acquire a hidden codimension-one degeneration.

Call an $R$-scheme $S$ **healthy regular** if it is regular and flat over $R$, and every abelian scheme over an open $U\subset S$ containing the generic fiber and all codimension-one points extends uniquely over $S$. Smooth $R$-schemes are healthy regular in the range used here: purity extends prime-to-$p$ torsion, and a polarization algebraizes the compatible formal abelian schemes along the missing codimension-at-least-two set.

**Theorem 5.2 (extension property).** If $S$ is healthy regular and flat over $R$, restriction induces a bijection

$$
\operatorname{Hom}_R(S,\mathscr M_K)
\xrightarrow{\sim}
\operatorname{Hom}_K(S_K,\mathscr M_{K,K}).                     \tag{5.1}
$$

provided the generic PEL abelian scheme has good reduction at every codimension-one point of $S$.

**Proof.** A generic map is a PEL abelian scheme over $S_K$. By the stated codimension-one good-reduction condition and healthiness, its abelian scheme extends uniquely to $A/S$. The generic order action and polarization extend uniquely over the normal base $S$ by the extension theorem for homomorphisms of abelian schemes; positivity persists because the degree is constant and the ample chamber cannot change without degeneracy. Prime-to-$p$ level extends across codimension one by finite étale purity and across codimension at least two by purity for finite étale covers. The Rosati and determinant identities hold on the dense generic fiber and therefore everywhere. Thus the extended tuple defines a map to $\mathscr M_K$. Uniqueness follows from separatedness, or term by term from rigidity. $\square$

The good-reduction qualification is essential. The extension property does not turn a semistable generic abelian variety into an abelian scheme. For the compact Shimura varieties in this book, Chapter 6 proves this qualification automatically for maps from traits.

### 5.4 Uniqueness of the good model

Suppose $\mathscr X$ and $\mathscr Y$ are smooth $R$-models of the same generic Shimura variety and both satisfy (5.1) for smooth test schemes. Apply the extension property of $\mathscr Y$ to the generic identity on the smooth scheme $\mathscr X$ to obtain $f:\mathscr X\to\mathscr Y$. Reversing the roles gives $g:\mathscr Y\to\mathscr X$. Both composites restrict to the identity generically, hence are the identity by separatedness. Thus $f$ is unique and is an isomorphism.

This proof explains why a good model is canonical after its extension property is established. Normalization in the generic function field alone would allow many regular modifications of the special fiber; the extension property excludes them.

## 6. Properness in the compact cases

The generic quaternionic curves and unitary surfaces selected here are projective because their adjoint groups are anisotropic modulo center. To prove their integral models proper, one must rule out degeneration of the universal abelian variety at the closed point of a trait.

### 6.1 The missing step in the valuative criterion

Let $T=\operatorname{Spec}V$ be a trait over $R$, with fraction field $L$, and let

$$
\operatorname{Spec}L\longrightarrow\mathscr M_K
$$

be a point. Separatedness gives uniqueness of an extension. Existence asks whether the PEL abelian variety $A_L$ has good reduction over $V$. Properness of the generic Shimura variety only extends the associated point after passing to some abstract proper $R$-model; it says nothing about extension of $A_L$ on the moduli scheme. The connection is furnished by semiabelian reduction and anisotropy.

### 6.2 Semiabelian degeneration and isotropic subspaces

After a finite extension of $L$ and domination of $V$, the semistable reduction theorem gives a semiabelian scheme $G/V'$ extending $A_L$:

$$
0\longrightarrow T\longrightarrow G_s\longrightarrow B\longrightarrow0, \tag{6.1}
$$

where $T$ is a torus and $B$ an abelian variety. The order action and a multiple of the polarization extend to the semiabelian model. If $T\ne0$, its rational character group

$$
X=X^*(T)\otimes_{\mathbf Z}\mathbf Q
$$

is nonzero and is stable under the relevant semisimple algebra.

The polarization supplies the monodromy pairing between the character and cocharacter lattices. In the rational PEL representation, the weight filtration attached to (6.1) has a nonzero first step $W_{-2}$ arising from $X_*(T)$, and the alternating form annihilates $W_{-2}$ with itself. The $D$-stability of the degeneration makes $W_{-2}$ a nonzero $D$-stable isotropic subspace. Equivalently, it defines a proper rational parabolic subgroup of the PEL group: the stabilizer of the flag

$$
0\subset W_{-2}\subset W_{-1}\subset V.
$$

We record the conclusion as the degeneration lemma.

**Lemma 6.1.** A nontrivial toric part in a polarized PEL degeneration produces a proper rational parabolic of the adjoint PEL group. Conversely, if the adjoint group is anisotropic over $\mathbf Q$, every polarized PEL semiabelian degeneration has toric rank zero.

**Proof.** The construction above gives the parabolic. Conversely, anisotropy means that no proper rational parabolic exists. Thus $W_{-2}=0$, so $X_*(T)\otimes\mathbf Q=0$. A torus has a free character lattice, hence $T=0$. Then (6.1) is an abelian variety and the semiabelian model is an abelian scheme. $\square$

For the unitary datum, an isotropic flag is a $K/F$-Hermitian isotropic line. For the quaternionic datum it is the corresponding isotropic module in the symplectic realization. The exact matching hypotheses in the earlier PEL constructions ensure that a parabolic of the realization gives a parabolic of the intended adjoint group, rather than of an accidentally larger centralizer.

The familiar degeneration of elliptic curves illustrates the mechanism. A Tate curve has a rank-one torus in its semistable special fiber. Its character lattice produces an isotropic line in the standard two-dimensional symplectic representation, and the stabilizer of that line is a Borel subgroup of $\operatorname{PGL}_2$. Modular curves possess rational parabolics and therefore cusps. The compact quaternionic and anisotropic unitary data possess no such parabolic, so the same degeneration cannot occur inside their PEL moduli problem.

### 6.3 Potential good reduction

Lemma 6.1 shows that $A_L$ acquires good reduction after a finite extension $L'/L$. Potential good reduction is not yet good reduction over $V$. We must remove the extension.

Choose a prime $\ell\ne p$ that is also prime to the polarization degree and the auxiliary level. Over $V'$, the Tate module $T_\ell A$ is unramified. Hence inertia over $L$ acts through the finite group $\operatorname{Gal}(L'/L)$. By replacing the given prime-to-$p$ level with a normal full level $N\ge3$ dominating it, choose a prime divisor $q\mid N$ distinct from $p$. The level trivializes $A[q]$ and makes inertia act trivially modulo $q$. A finite-order automorphism of a free $\mathbf Z_q$-module that is congruent to the identity modulo $q$ is the identity when $q\ge3$; if only level at $2$ is present, take an auxiliary odd principal cover and descend afterward. Thus inertia acts trivially on $T_qA$.

The good-reduction criterion for abelian varieties over a henselian DVR now applies: an abelian variety has good reduction if and only if $T_qA$ is unramified for one $q\ne p$. Its proof takes the identity component of the Néron model; trivial inertia makes the toric and unipotent character modules vanish, so the special fiber is proper, hence the model is abelian. Therefore $A_L$ extends over $V$ itself.

This level argument is a convenient descent device, not a restriction on the final neat level. One proves properness on a cofinal principal-level cover and descends it through a finite morphism.

### 6.4 Descent and the properness theorem

**Theorem 6.2 (properness).** If the adjoint datum is anisotropic over $\mathbf Q$ modulo center, the good fine moduli scheme $\mathscr M_K$ is proper, hence projective, over $R$.

**Proof.** Work first at a normal full prime-to-$p$ level at least three. For every trait, Lemma 6.1 and Section 6.3 extend the generic abelian variety. Its order action and polarization extend uniquely; finite étale level extends because the trait is normal and the generic representation is unramified. The determinant identity extends from the generic point. Thus the valuative criterion gives properness. For a neat level, take a finite principal cover. Its proper source maps finitely and surjectively to the target, so the target is proper. Since $\mathscr M_K$ was quasi-projective over $R$, properness makes it projective. $\square$

The theorem is deliberately limited to compact data. A noncompact PEL variety needs a compactification by semiabelian objects; the open moduli scheme is not proper even at a good prime.

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

When the target level is neat, the deck group acts freely and (7.1) is a finite étale torsor. At arbitrary level the correct object is

$$
\mathscr{M}_{K_2}\simeq[\mathscr M_{K_1}/\Delta].               \tag{7.2}
$$

The stack is smooth and proper because these properties are smooth-local and descend through finite covers. Its coarse quotient is finite over $R$ but can have quotient singularities at fixed points. Thus “good reduction at coarse level” cannot mean smoothness without a hypothesis killing stabilizers.

### 7.3 Universal families at coarse level

The fine scheme carries the universal abelian scheme. On the quotient stack it descends equivariantly and remains universal. On the coarse scheme it descends if and only if every stabilizer acts trivially on the corresponding fiber together with its PEL structure. Usually a scalar automorphism such as $-1$ acts trivially on the coarse moduli point and nontrivially on the abelian variety, so no universal family exists there.

Cohomological correspondences on the base may nevertheless descend to the coarse scheme because their graphs and cycle classes are stabilizer-invariant. One must not infer descent of the universal abelian variety from descent of its Hecke action.

### 7.4 Extension of scalars

Let $R\to R'$ be an unramified extension of discrete valuation rings compatible with a place $v'\mid v$ of the reflex field. Every ingredient of the functor commutes with base change, giving a canonical isomorphism

$$
\mathscr M_K\otimes_RR'\simeq\mathscr M_{K,R'}.                \tag{7.3}
$$

The universal family, Hodge bundles, polarization, and prime-to-$p$ level pull back under (7.3). The local model becomes the corresponding split form after a sufficiently large unramified extension. Smoothness and properness are preserved.

For a ramified extension $R\to R'$, ordinary scalar extension of an already good model remains smooth, but it need not equal a newly formulated moduli problem based on a different ramified order or parahoric lattice. Equality holds only when the entire integral datum is the pullback of the old one.

## 8. Prime-to-residue-characteristic Hecke correspondences

A Hecke operator changes a prime-to-$p$ lattice. At a good prime this modification is finite étale on torsion and therefore extends over the integral model without altering its local deformation theory.

### 8.1 Integral Hecke data

Let $g\in G(\mathbf A_f^p)$. Put

$$
K_g^p=K^p\cap gK^pg^{-1}.
$$

There are generic maps from level $K_g^p$ to levels $K^p$ and $g^{-1}K^pg$, followed by the identification induced by $g$. To make the universal quasi-isogeny integral, choose an integer $m\ge1$, prime to $p$, such that both $mg$ and $mg^{-1}$ carry the chosen prime-to-$p$ lattices into one another. Multiplication by $m$ changes the quasi-isogeny by a central scalar but makes its kernel a finite subgroup of $\mathcal A[m^r]$ for some $r$.

The resulting correspondence is independent of $m$ at the rational Hecke level. Integral actions can differ by the explicit central multiplication factor, which must be retained whenever a coefficient prime divides $m$.

### 8.2 Quotients by finite étale kernels

Over $\mathscr M_{K_g}$, the level structure identifies the lattice quotient determined by $g$ with a finite locally free subgroup

$$
H_g\subset\mathcal A[n],\qquad p\nmid n.                        \tag{8.1}
$$

Because $n$ is invertible on the base, $\mathcal A[n]$ and $H_g$ are finite étale. The quotient

$$
q_g:\mathcal A\longrightarrow\mathcal A/H_g                  \tag{8.2}

$$

exists as an abelian scheme and commutes with arbitrary base change. The $\mathcal O$-stability of the lattice inclusion makes $H_g$ stable, so the order action descends. The pairing condition on $g$ makes the kernel isotropic for the appropriate multiple of the polarization pairing. Polarization descent across an isotropic kernel therefore gives the prescribed polarization on $\mathcal A/H_g$.

This is the point at which a rational quasi-isogeny becomes an integral morphism. Taking the schematic closure of its generic kernel would be unsafe over a higher-dimensional base; (8.1) constructs the kernel inside an already finite étale group scheme and proves flatness before quotienting.

### 8.3 The correspondence and its universal isogeny

The quotient tuple defines a second map, and we obtain

$$
\mathscr M_K
\xleftarrow{\ p_1\ }
\mathscr M_{K_g}
\xrightarrow{\ p_2\ }
\mathscr M_K.                                                     \tag{8.3}
$$

Both maps are finite étale at neat levels. Over the middle space, (8.2) is the universal prime-to-$p$ Hecke isogeny between $p_1^*\mathcal A$ and $p_2^*\mathcal A$, after the selected integral normalization. Its generic fiber is the canonical Hecke quasi-isogeny.

The graph of (8.3) is proper over both factors because the projections are finite. Hence (8.3) defines an integral algebraic correspondence even when the bases are not proper. Properness of the bases becomes necessary when one wants ordinary global cohomology to have specialization isomorphisms.

### 8.4 Composition, adjoints, and descent

If $g,h\in G(\mathbf A_f^p)$, pull the correspondences for $g$ and $h$ to the common refinement

$$
K^p\cap gK^pg^{-1}\cap ghK^p(gh)^{-1}.
$$

Successive quotient isogenies have the same lattice effect as $gh$, so their composition agrees with the $gh$ correspondence. Decomposing the finite fiber product into double cosets gives the usual convolution law. This proves the Hecke relations geometrically, not merely on complex points.

The polarization identifies the transpose of the $g$-isogeny, up to its explicit multiplier, with the correspondence for $g^{-1}$. Accordingly the cohomological adjoint of $T_g$ is the multiplier-normalized $T_{g^{-1}}$. Suppressing the multiplier would give an incorrect integral adjoint formula.

All constructions are equivariant under finite changes of level. They descend to quotient stacks and, as correspondences, to coarse schemes. Hecke operators at $p$ are excluded: changing the hyperspecial $p$-lattice introduces $p$-power kernels, whose connected parts and parahoric local models require different geometry.

## 9. Étale cohomology of the good models

The geometric construction earns its name through specialization. Smoothness makes the family locally acyclic for prime-to-$p$ coefficients; properness prevents classes from escaping to infinity. Together they identify generic and special cohomology integrally.

### 9.1 Finite coefficients and specialization

Let $f:\mathscr M_K\to\operatorname{Spec}R$ be one of the proper good models, let $\ell\ne p$, and put $\Lambda_n=\mathbf Z/\ell^n\mathbf Z$. Smooth proper base change gives lisse finite sheaves

$$
R^if_*\Lambda_n
$$

which become constant on the strictly henselian localization of $R$. They need not be free as $\Lambda_n$-modules when adjacent integral cohomology has $\ell$-torsion. Equivalently, a chosen geometric specialization gives canonical isomorphisms

$$
\operatorname{sp}_{n}^{i}:
H^i(\mathscr M_{K,\bar k},\Lambda_n)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar K},\Lambda_n).                            \tag{9.1}
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
H^i(\mathscr M_{K,\bar K},\mathbf Z_\ell).                      \tag{9.2}
$$

Here $H^i(-,\mathbf Z_\ell)$ means the cohomology of the derived inverse-limit coefficient system, not an unexamined inverse limit of abstract groups. Reduction modulo $\ell^n$ fits into the universal-coefficient exact sequence

$$
0\to H^i(\mathbf Z_\ell)/\ell^n
\to H^i(\Lambda_n)
\to H^{i+1}(\mathbf Z_\ell)[\ell^n]\to0.                       \tag{9.3}
$$

Thus $H^i(\Lambda_n)$ need not be the naive reduction of $H^i(\mathbf Z_\ell)$ when the next integral group has torsion. Isomorphism (9.2) remains valid because the entire derived systems are compared, not because torsion is assumed absent. Tensoring gives the corresponding $\mathbf Q_\ell$-comparison.

### 9.3 Coefficient systems from the universal abelian scheme

Let $a:\mathcal A\to\mathscr M_K$ be the universal abelian scheme. The lisse sheaf

$$
\mathbb V_\ell=R^1a_*\mathbf Z_\ell
\simeq\underline{\operatorname{Hom}}(T_\ell\mathcal A,\mathbf Z_\ell) \tag{9.4}
$$

is finite free and commutes with arbitrary base change. It carries the $\mathcal O$-action and the alternating form induced by the universal polarization. Tensor products, duals, exterior powers, and subquotients cut out by integral idempotents produce lisse integral coefficient systems $\mathcal L_\ell$.

For each such system and its finite reductions, smooth proper base change gives

$$
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar K},\mathcal L_\ell).                    \tag{9.5}
$$

An idempotent with a denominator divisible by $\ell$ cuts out only a $\mathbf Q_\ell$-summand, not an integral direct summand. Integral comparison for that rational representation means comparison of a separately specified stable lattice, not automatic intersection with the ambient lattice.

The full cohomology of the universal abelian scheme also compares. Proper smoothness of the composite $\mathcal A\to\operatorname{Spec}R$ gives

$$
H^m(\mathcal A_{\bar k},\mathbf Z_\ell)
\simeq H^m(\mathcal A_{\bar K},\mathbf Z_\ell),                \tag{9.6}
$$

and Leray identifies the filtration with the cohomology of the exterior powers

$$
R^ja_*\mathbf Z_\ell\simeq\bigwedge^j\mathbb V_\ell.
$$

### 9.4 Unramifiedness and Frobenius

The geometric generic cohomology in (9.2) carries an action of $\operatorname{Gal}(\bar K/K)$. Since $R^if_*\mathbf Z_\ell$ is lisse over the trait, inertia acts trivially. Thus

$$
H^i(\mathscr M_{K,\bar K},\mathbf Z_\ell)
$$

is unramified at $v$, including its torsion. Under (9.2), arithmetic Frobenius on the generic representation corresponds to arithmetic Frobenius on the special fiber, and geometric Frobenius corresponds to its inverse.

This conclusion says neither that Frobenius is semisimple nor that its eigenvalues have a prescribed weight. Those assertions require separate purity results. Good reduction supplies the transport from Galois action to special-fiber geometry; it does not evaluate that geometry.

## 10. Hecke action and cohomological base change

The specialization isomorphism is useful only if it preserves the arithmetic operators used to isolate automorphic constituents. This chapter checks that compatibility at the level of correspondences.

### 10.1 Pull-push on a proper correspondence

For (8.3) and a finite coefficient ring $\Lambda$, define

$$
T_g=(p_2)_*p_1^*:
H^i(\mathscr M_{K},\Lambda)
\longrightarrow H^i(\mathscr M_{K},\Lambda).                  \tag{10.1}
$$

The pushforward is the finite étale trace. If the coefficient system comes from $\mathcal A$, insert between pullback and trace the morphism in the required variance induced by the universal isogeny. The isogeny is prime to $p$, but this morphism is an integral isomorphism on a $\mathbf Z_\ell$-system only when its degree is prime to $\ell$.

Formula (10.1) is defined in the derived category and hence respects long exact sequences and cup products with the usual projection formula. Its reduction to each fiber is the Hecke correspondence attached to the same double coset, since both projections and the universal isogeny commute with base change.

### 10.2 Compatibility with specialization

**Theorem 10.1 (Hecke-equivariant specialization).** For every $g\in G(\mathbf A_f^p)$, every $\ell\ne p$, and every integral PEL coefficient system on which the normalized universal isogeny acts, the square

$$
\begin{array}{ccc}
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)&\xrightarrow{T_g}&
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)\\
\downarrow\scriptstyle{\operatorname{sp}}&&\downarrow\scriptstyle{\operatorname{sp}}\\
H^i(\mathscr M_{K,\bar K},\mathcal L_\ell)&\xrightarrow{T_g}&
H^i(\mathscr M_{K,\bar K},\mathcal L_\ell)
\end{array}                                                       \tag{10.2}
$$

commutes.

**Proof.** Proper base change is functorial for pullback. It is also compatible with proper trace, as may be checked after strict localization where both traces are the sum over the same finite geometric fiber. The universal isogeny and its map on coefficient systems are defined over the middle integral model, so their base changes appear in both rows. Composing these three compatible maps proves the square at finite level. Uniform boundedness and finiteness pass it to the derived $\mathbf Z_\ell$-limit. $\square$

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

For a smooth proper surface $S$, the range is $0$ through $4$ and the middle degree is $2$. Poincaré duality pairs $H^i$ with $H^{4-i}(2)$. The unitary construction is designed so that the relevant parity occurs in $H^2$, but geometry alone does not isolate the desired packet. The Hecke-equivariant integral comparison transports any projector that has already been constructed with controlled denominators.

## 11. Coherent and de Rham comparison

Prime-to-$p$ étale cohomology is the cleanest integral theory at a good prime. Coherent and de Rham cohomology also carry natural lattices, but their base-change behavior has additional hypotheses. Keeping the distinction visible prevents a false universal freeness claim.

### 11.1 Proper coherent cohomology

Let $f:\mathscr M_K\to\operatorname{Spec}R$ be proper and let $\mathcal F$ be a coherent sheaf flat over $R$. Properness makes every $R^if_*\mathcal F$ finite. For $R'=K$ or $k$, there is a base-change map

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
H^i_{\mathrm{dR}}(\mathscr M_K/R)\otimes_RK
\simeq H^i_{\mathrm{dR}}(\mathscr M_{K,K}/K)                   \tag{11.4}
$$

and the analogous special-fiber isomorphism. Generic base change in (11.4) is always exact because $K/R$ is flat; integral comparison with $k$ requires the torsion test.

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

We now collect the general construction in its one-dimensional form. The point is not just brevity; the curve case has stronger unconditional coherent comparison and a single integral Kodaira--Spencer line.

### 12.1 Construction theorem

**Theorem 12.1.** Let $(G,X)$ be the fixed quaternionic PEL datum whose adjoint group is split at exactly one real place and anisotropic modulo center. Let $v\mid p$ be a good PEL place, $K_p$ the hyperspecial stabilizer of the self-dual lattice, and $K^p$ neat. Then the selected canonical Shimura curve has a unique smooth projective model

$$
\mathscr C_K/\mathcal O_{E,v}
$$

of relative dimension one satisfying the extension property. It represents the integral PEL functor and carries its universal abelian scheme. Every prime-to-$p$ change of level and Hecke correspondence extends as in Chapters 7 and 8.

**Proof.** Theorem 3.1 constructs the model. The active Morita multiplicity plane makes its local model $\mathbf P^1$, so Theorem 5.1 gives smoothness and dimension one. Quaternionic anisotropy rules out toric degeneration by Lemma 6.1, so Theorem 6.2 gives projectivity. Theorem 5.2 gives the extension property and Section 5.4 gives uniqueness. Universal and Hecke structures are built over the moduli scheme itself. $\square$

### 12.2 The integral Kodaira--Spencer line

Let $\mathcal L$ be the active Hodge line and $\mathcal M$ the multiplier determinant line. The tangent calculation

$$
T_{\mathscr C_K/R}\simeq\operatorname{Hom}(\mathcal L,\mathcal U/\mathcal L)
$$

dualizes to the integral Kodaira--Spencer isomorphism

$$
\Omega^1_{\mathscr C_K/R}
\simeq\mathcal L^{\otimes2}\otimes\mathcal M^{-1}.             \tag{12.1}
$$

To prove (12.1), establish it on the framed space from the universal line on $\mathbf P(\mathcal U)$, where

$$
\Omega^1\simeq\mathcal L\otimes(\mathcal U/\mathcal L)^\vee
\simeq\mathcal L^{\otimes2}\otimes(\det\mathcal U)^{-1}.
$$

The frame-change action is equivariant and $\det\mathcal U$ descends as $\mathcal M$, so faithfully flat descent gives (12.1). The multiplier line may be trivialized at a symplectic level, but it cannot be omitted in a similitude formulation.

Relative duality and (12.1) relate coherent degree-one cohomology to sections of an automorphic line. This relation is integral and base-change compatible because every bundle in (12.1) is locally free over $R$.

### 12.3 Cohomology and good reduction

For every $\ell\ne p$, specialization gives a Hecke-equivariant, cup-product-compatible isomorphism

$$
H^1(\mathscr C_{K,\bar k},\mathbf Z_\ell)
\xrightarrow{\sim}
H^1(\mathscr C_{K,\bar K},\mathbf Z_\ell).                      \tag{12.2}
$$

The right side is unramified. The same holds with every integral coefficient system constructed from the universal abelian scheme. Coherently, (11.5) compares the Hodge and de Rham lattices without an extra torsion hypothesis. Therefore the curve model simultaneously supplies an étale lattice, a de Rham lattice, and their Hecke actions. A comparison between those two lattices at the residue prime would require a separate integral $p$-adic comparison theorem and is not being asserted here.

## 13. The unitary surface model

The surface construction shares the same formal architecture but has two active directions. Its middle cohomology is the geometric location needed by the parity repair in the modèles étranges construction.

### 13.1 Construction theorem

**Theorem 13.1.** Let $(G,X)$ be the compact unitary PEL datum with two signature-$(1,1)$ places and exact finite-adelic matching to the desired quaternionic inner form. At a good PEL place $v\mid p$ with hyperspecial $K_p$ and neat $K^p$, the selected canonical unitary surface has a unique smooth projective model

$$
\mathscr S_K/\mathcal O_{E,v}
$$

of relative dimension two satisfying the extension property. It represents the integral unitary PEL functor, carries the auxiliary universal abelian scheme, and supports all prime-to-$p$ level maps and Hecke correspondences.

**Proof.** Representability and the generic comparison are Theorem 3.1 and (3.4). The integral local model is the product of the two active projective lines, hence is smooth of dimension two. Anisotropy of the Hermitian plane rules out a rational isotropic line and therefore, by Lemma 6.1, a toric degeneration. Properness, the extension property, uniqueness, and the Hecke tower follow from the corresponding general theorems. $\square$

The finite-adelic matching is indispensable in the properness argument: it ensures that the parabolic detected by a degeneration belongs to the intended unitary group. The auxiliary central torus does not create a boundary because a torus has no proper parabolic.

### 13.2 Two tangent directions and canonical bundles

Let $\mathcal L_i\subset\mathcal U_i$ be the two active Hodge lines and $\mathcal M_i=\det\mathcal U_i$. The cotangent bundle splits étale-locally and descends as

$$
\Omega^1_{\mathscr S_K/R}
\simeq
(\mathcal L_1^{\otimes2}\otimes\mathcal M_1^{-1})
\oplus
(\mathcal L_2^{\otimes2}\otimes\mathcal M_2^{-1}).            \tag{13.1}
$$

Taking determinants yields

$$
\omega_{\mathscr S_K/R}
\simeq
\mathcal L_1^{\otimes2}\otimes\mathcal L_2^{\otimes2}
\otimes\mathcal M_1^{-1}\otimes\mathcal M_2^{-1}.             \tag{13.2}
$$

The common similitude condition can relate $\mathcal M_1$ and $\mathcal M_2$, but no simplification is made until such a relation is specified. Equations (13.1) and (13.2) commute with unramified scalar extension and with prime-to-$p$ change of level.

### 13.3 Middle cohomology and auxiliary abelian schemes

For $\ell\ne p$ there is a Hecke-equivariant isomorphism

$$
H^2(\mathscr S_{K,\bar k},\mathbf Z_\ell)
\xrightarrow{\sim}
H^2(\mathscr S_{K,\bar K},\mathbf Z_\ell).                     \tag{13.3}
$$

It preserves the intersection pairing and Poincaré duality. The universal auxiliary abelian scheme produces lisse coefficient systems and endomorphism projectors, all transported by the same comparison when integrally defined.

The word auxiliary remains mathematically important. Formula (13.3) compares the cohomology of the parameter surface. The exterior algebra of $R^1a_*\mathbf Z_\ell$ describes the fibers of the universal abelian scheme, not automatically the automorphic middle cohomology of $\mathscr S_K$. The later automorphic decomposition must use the acting group and Hecke algebra to isolate the desired rank-two packet.

Unlike the curve case, integral coherent Hodge groups of the surface can have torsion. Derived de Rham base change always holds, but an ordinary special-fiber Hodge decomposition requires the criteria of Section 11.3.

## 14. Integral comparison package

We can now state the reusable output without mixing the geometric, étale, and coherent hypotheses.

### 14.1 The geometric comparison theorem

**Theorem 14.1.** Let $\mathscr X$ be either $\mathscr C_K$ or $\mathscr S_K$ at a good PEL place. Then:

1. $\mathscr X/R$ is smooth and projective, of relative dimension one or two;
2. its generic fiber is the selected canonical Shimura variety;
3. at fine level it represents the PEL functor and carries the universal abelian scheme with all tensors;
4. it satisfies the healthy-regular extension property and is uniquely characterized by it;
5. every prime-to-$p$ level map is finite étale, and every prime-to-$p$ Hecke double coset extends to a finite correspondence carrying a universal isogeny;
6. for $\ell\ne p$, finite and adic étale cohomology of the base and of every integral PEL coefficient system satisfies Hecke-equivariant smooth proper base change;
7. coherent and de Rham complexes satisfy proper finiteness and derived base change, while ordinary integral fiber comparison holds exactly under the adjacent-degree or torsion-freeness criteria of Chapter 11.

**Proof.** Statements 1--5 are Theorems 5.1, 6.2, 3.1, 5.2, and the constructions of Chapters 7--8. Statement 6 is (9.1)--(9.5) together with Theorem 10.1. Statement 7 follows from coherent cohomology and base change, perfection of the smooth proper de Rham complex, and the universal-coefficient sequence. $\square$

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

### 14.3 Independence of the chosen good presentation

A rational Shimura datum may admit two integral PEL presentations at $v$. If they define smooth models with the same generic canonical variety and both satisfy the extension property, Section 5.4 gives a unique isomorphism between the models. Under that isomorphism, prime-to-$p$ Hecke correspondences agree because their generic graphs agree and finite closed subschemes of a flat separated scheme are determined by their dense generic fiber once flatness is known.

Universal abelian schemes from two genuinely different PEL embeddings need not be isomorphic; they may be related only by a prime-to-$p$ isogeny or by auxiliary factors. The base model and its canonical cohomology are independent, while coefficient systems are compared only after the relevant tensor or isogeny identification has been supplied. This is the correct strength of presentation independence.

## 15. Failure modes and the good-prime boundary

The construction is sharp enough to show what changes outside its hypotheses. These are not minor technical omissions: each failed condition produces a distinct geometric phenomenon.

### 15.1 Ramified orders and non-self-dual lattices

If $D\otimes\mathbf Q_p$ or its center is ramified, the order modulo $p$ can acquire nilpotents. Idempotent decompositions used to read off Hodge ranks disappear, and the determinant law may allow infinitesimal extensions between packets. The local model can be nonreduced or nonflat.

If $\Lambda_p\subsetneq\Lambda_p^\vee$, its stabilizer is generally parahoric. The Hodge submodule must then be compatible with a lattice chain, not a single self-dual lattice. The naive determinant model can have the wrong special fiber; wedge, spin, or refined determinant conditions may be required. None can be added uniformly without inspecting the exact datum.

For example, replace a perfect symplectic plane over $\mathbf Z_p$ by the lattice with pairing matrix

$$
\begin{pmatrix}0&p\\-p&0\end{pmatrix}.
$$

Its dual is $p^{-1}\Lambda$, so the stabilizer remembers a nontrivial lattice step. Reduction modulo $p$ annihilates the displayed form, and the equation “the Hodge line is isotropic” becomes vacuous. The resulting naive special fiber is larger than the generic flag variety. This elementary calculation is the local-model reason self-duality cannot be weakened silently.

At $p=2$, skew-symmetry does not imply alternation and orthogonal involutions have extra integral invariants. The present theorem includes $p=2$ only when perfect alternation, reductivity, and the smooth product-of-lines local model have been verified directly.

### 15.2 Parahoric level and singular local models

A Hecke modification at $p$ changes the lattice chain. Its kernel can contain connected finite flat group schemes, so quotienting is no longer a finite étale operation. The corresponding local model often has several components meeting along singular strata. Even if the total space can be regularized, smooth proper base change is replaced by nearby cycles.

This explains why the prime-to-$p$ Hecke algebra acts integrally in this book while the $p$-Hecke correspondence has been excluded. The exclusion is geometric, not terminological.

### 15.3 Bad reduction and monodromy

If anisotropy fails or the chosen place is bad, a PEL abelian variety can acquire a toric part. The weight filtration in Section 6.2 is then nonzero, inertia acts nontrivially, and the specialization map

$$
H^i(X_{\bar k},\mathbf Z_\ell)
\longrightarrow H^i(X_{\bar K},\mathbf Z_\ell)
$$

need not be an isomorphism. Proper base change still identifies the special-fiber group with the stalk of the direct image, but smooth local acyclicity has failed. Nearby cycles record the missing classes and monodromy operator.

Similarly, for a nonproper Shimura variety, classes can enter through the boundary even when the open morphism is smooth. A smooth compactification with a controlled normal-crossings boundary can recover compactly supported comparison, but it is a different theorem. The compact quaternionic curves and unitary surfaces here avoid this boundary by anisotropy.

## 16. The good integral-model theorem

The separate arguments can now be assembled into one theorem with every hypothesis visible.

### 16.1 Unified statement

**Theorem 16.1 (good integral models of the selected Shimura curves and surfaces).** Let $(G,X)$ be either:

1. a quaternionic PEL datum with exactly one active real factor; or
2. the compact unitary PEL datum with exactly two active signature-$(1,1)$ factors obtained by the modèles étranges construction.

Let $E$ be its reflex field, let $v\mid p$, and assume:

- the rational PEL realization and selected canonical components are fixed;
- the acting order is maximal and unramified at $p$, the involution is unramified, and the alternating lattice is self-dual;
- the polarization degree is prime to $p$;
- the stabilizer $G_{\mathbf Z_p}$ is reductive, $K_p=G_{\mathbf Z_p}(\mathbf Z_p)$ is hyperspecial, and the actual integral determinant local model is the product of one or two projective lines;
- $K^p$ is neat, and the selected component union is stable under the local reciprocity action;
- the adjoint datum is anisotropic modulo center.

Then there exists a unique smooth projective $\mathcal O_{E,v}$-scheme $\mathscr M_K$ with generic fiber $\operatorname{Sh}_{K_pK^p}(G,X)$ and the healthy-regular extension property. It represents the integral PEL functor, carries the universal abelian scheme and all PEL tensors, is compatible with unramified base change, and has relative dimension one in case 1 and two in case 2.

For every $g\in G(\mathbf A_f^p)$, its Hecke correspondence and normalized universal prime-to-$p$ isogeny extend integrally. For every $\ell\ne p$ and every integrally defined PEL coefficient system $\mathcal L_\ell$, specialization is a canonical Hecke-equivariant isomorphism

$$
H^i(\mathscr M_{K,\bar k},\mathcal L_\ell)
\xrightarrow{\sim}
H^i(\mathscr M_{K,\bar E_v},\mathcal L_\ell),                  \tag{16.1}
$$

compatible with products, pairings, tensors, and level change. The generic representation is unramified at $v$. Coherent and de Rham derived cohomology also commute with base change; ordinary integral coherent comparison is subject to the precise torsion criteria of Chapter 11, and is unconditional in degree one for the curve's structure sheaf and de Rham complex.

### 16.2 Proof architecture

The proof has a strict order.

First, integral tensors define a finite-type PEL scheme and its universal family. Second, the framed deformation diagram reduces all completed local rings to the actual integral local model. Morita equivalence identifies that model with $\mathbf P^1$ or $\mathbf P^1\times\mathbf P^1$, proving smoothness and dimension. Third, a hypothetical semiabelian degeneration produces a rational isotropic flag and therefore a proper parabolic; anisotropy rules it out, and level rigidity descends potential good reduction. This proves properness. Fourth, extension of abelian schemes, homomorphisms, polarizations, and finite étale level gives the extension property and uniqueness. Fifth, prime-to-$p$ lattice modifications are finite étale kernels, so their quotients extend Hecke isogenies. Finally, smooth proper base change, derived inverse limits, and functorial trace give (16.1) with its full integral Hecke structure.

No arrow in this chain can be reversed without adding a hypothesis. Generic representability does not prove the local model smooth; smoothness does not prove properness; properness does not identify integral lattices; and rational Hecke equivariance does not control denominators.

### 16.3 Conclusion

At a good prime, the selected quaternionic curve and unitary surface are not merely varieties with fortunate reduction. Their rational PEL tensors admit self-dual unramified lattices, those lattices produce smooth flag local models, and anisotropy prevents the universal abelian scheme from escaping into a semiabelian boundary. The resulting integral models are therefore smooth, projective, functorial in level, and uniquely characterized by extension.

This geometry carries its arithmetic structures intact. Universal abelian schemes, endomorphisms, polarizations, Hodge bundles, and prime-to-$p$ Hecke isogenies all live over the local reflex ring. Prime-to-$p$ étale cohomology specializes with its integral lattice and every Hecke operator; coherent and de Rham lattices specialize exactly when their visible torsion criteria permit it. The curve contributes its degree-one package, and the modèles étranges surface contributes its degree-two package. Bad primes begin precisely where a lattice chain, toric degeneration, boundary, or nontrivial monodromy replaces this constant smooth picture.
