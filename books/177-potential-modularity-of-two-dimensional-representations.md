# Potential Modularity of Two-Dimensional Representations

## Contents

1. [The residual potential-modularity problem](#1-the-residual-potential-modularity-problem)
   - [The endpoint](#11-the-endpoint)
   - [The two-prime bridge](#12-the-two-prime-bridge)
   - [Frobenius, covariance, and determinant](#13-frobenius-covariance-and-determinant)
   - [The boundary of the book](#14-the-boundary-of-the-book)
2. [The exact input datum](#2-the-exact-input-datum)
   - [The residual target](#21-the-residual-target)
   - [Pairings and coefficient change](#22-pairings-and-coefficient-change)
   - [The coefficient-prime local model](#23-the-coefficient-prime-local-model)
   - [The pre-specialization ledger](#24-the-pre-specialization-ledger)
3. [The dihedral automorphic seed](#3-the-dihedral-automorphic-seed)
   - [Quadratic induction and its determinant](#31-quadratic-induction-and-its-determinant)
   - [Choosing the auxiliary prime in the correct order](#32-choosing-the-auxiliary-prime-in-the-correct-order)
   - [Residual automorphy after an arbitrary point field](#33-residual-automorphy-after-an-arbitrary-point-field)
   - [The selected residual localization](#34-the-selected-residual-localization)
4. [The paired-frame realization space](#4-the-paired-frame-realization-space)
   - [The Hilbert--Blumenthal datum](#41-the-hilbert--blumenthal-datum)
   - [Twisted paired frames](#42-twisted-paired-frames)
   - [Fineness, smoothness, and dimension](#43-fineness-smoothness-and-dimension)
   - [One arithmetic component and product monodromy](#44-one-arithmetic-component-and-product-monodromy)
5. [Local models and nonempty opens](#5-local-models-and-nonempty-opens)
   - [One simultaneous local witness](#51-one-simultaneous-local-witness)
   - [Real places](#52-real-places)
   - [Places above the target prime](#53-places-above-the-target-prime)
   - [Places above the auxiliary prime](#54-places-above-the-auxiliary-prime)
   - [Semistable places](#55-semistable-places)
   - [From a local model to an open](#56-from-a-local-model-to-an-open)
6. [The controlled totally real specialization](#6-the-controlled-totally-real-specialization)
   - [The avoidance field](#61-the-avoidance-field)
   - [The Moret--Bailly step](#62-the-moret--bailly-step)
   - [Image preservation](#63-image-preservation)
   - [The exact field profile](#64-the-exact-field-profile)
7. [The specialized abelian variety](#7-the-specialized-abelian-variety)
   - [The two exact torsion frames](#71-the-two-exact-torsion-frames)
   - [Integral coefficient-prime models](#72-integral-coefficient-prime-models)
   - [The actual bad-place set](#73-the-actual-bad-place-set)
   - [Local membership is not automorphic support](#74-local-membership-is-not-automorphic-support)
8. [Cleanability and auxiliary-prime lifting](#8-cleanability-and-auxiliary-prime-lifting)
   - [The auxiliary-adic representation](#81-the-auxiliary-adic-representation)
   - [The residual automorphic localization](#82-the-residual-automorphic-localization)
   - [The exact cleanability record](#83-the-exact-cleanability-record)
   - [Component support](#84-component-support)
   - [The conditional lifting step](#85-the-conditional-lifting-step)
   - [Stopping over a further field](#86-stopping-over-a-further-field)
9. [Moving to the target coefficient prime](#9-moving-to-the-target-coefficient-prime)
   - [Common algebraic Frobenius polynomials](#91-common-algebraic-frobenius-polynomials)
   - [The selected special place supplies a curve carrier](#92-the-selected-special-place-supplies-a-curve-carrier)
   - [Chebotarev comparison](#93-chebotarev-comparison)
   - [The exact residual member](#94-the-exact-residual-member)
10. [The conditional potential-modularity theorem](#10-the-conditional-potential-modularity-theorem)
    - [Lifting-admissible paired specialization](#101-lifting-admissible-paired-specialization)
    - [Conditional residual potential modularity](#102-conditional-residual-potential-modularity)
    - [Exact field control](#103-exact-field-control)
    - [Why the geometric alternatives remain conditional](#104-why-the-geometric-alternatives-remain-conditional)
11. [Failure tests and boundary cases](#11-failure-tests-and-boundary-cases)
    - [Residual automorphy is localization-sensitive](#111-residual-automorphy-is-localization-sensitive)
    - [Smoothness is not component support](#112-smoothness-is-not-component-support)
    - [Semistability is not cleanability](#113-semistability-is-not-cleanability)
    - [Separate local points do not define one open condition](#114-separate-local-points-do-not-define-one-open-condition)
    - [Scalar extension has a direction](#115-scalar-extension-has-a-direction)
    - [Pairings fix determinants and signs](#116-pairings-fix-determinants-and-signs)
    - [Frobenius conventions cannot be mixed](#117-frobenius-conventions-cannot-be-mixed)
    - [A finite clean chain is a theorem, not notation](#118-a-finite-clean-chain-is-a-theorem-not-notation)
    - [Chebotarev gives semisimple comparison first](#119-chebotarev-gives-semisimple-comparison-first)
    - [Potential automorphy is not descent](#1110-potential-automorphy-is-not-descent)
12. [Dependencies, downstream handoff, and verdict](#12-dependencies-downstream-handoff-and-verdict)
    - [Exact prior inputs](#121-exact-prior-inputs)
    - [Acyclic proof order](#122-acyclic-proof-order)
    - [Downstream record](#123-downstream-record)
    - [Readiness verdict](#124-readiness-verdict)

## 1. The residual potential-modularity problem

Potential modularity enlarges the ground field so that a prescribed residual representation becomes the reduction of a parallel-weight-two cuspidal automorphic representation. The extension is part of the construction. It creates a point on a twisted moduli space, permits several local models to coexist on one abelian variety, and can be chosen disjoint from the finite fields that detect the residual image.

This book treats only that residual transfer. It does not prove automorphy of a separately chosen characteristic-zero lift. It also does not descend the resulting automorphic representation to the original field. Those are different problems with different local-component and descent hypotheses.

### 1.1 The endpoint

Let $F$ be totally real, let $\ell\geq7$, and let $k$ be a finite field of characteristic $\ell$. A continuous representation

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k) \tag{1.1}
$$

is **modular of parallel weight two over $F$** if there are a cuspidal parallel-weight-two automorphic representation $\Pi$ of $\operatorname{GL}_2(\mathbf A_F)$ equipped with a proved two-dimensional Galois realization, a coefficient place $\lambda\mid\ell$, and stable lattices such that, after extension to one common finite residue field $\kappa$,

$$
\bar\rho^{\mathrm{ss}}\otimes_k\kappa
\simeq
\bar\rho_{\Pi,\lambda}^{\mathrm{ss}}\otimes_{k_\lambda}\kappa. \tag{1.2}
$$

If $\bar\rho$ is absolutely irreducible, the semisimplification signs may be removed. The representation (1.1) is **potentially modular** if its restriction to some finite totally real extension is modular in this sense.

The theorem proved below has an explicit additional hypothesis: the abelian variety obtained after specialization must lie in a clean auxiliary-prime lifting datum. That hypothesis is not known from the present dependency chain for every residual target in the catalog range. The theorem is therefore a conditional residual potential-modularity theorem, and Section 10.4 isolates the exact first gap on each available lifting route.

### 1.2 The two-prime bridge

Choose a second rational prime $q\ne\ell$ and a totally real multiplication field $M$ with primes

$$
\lambda\mid\ell,
\qquad
\mathfrak q\mid q.
$$

The construction seeks a Hilbert--Blumenthal abelian variety $A$ over a finite totally real field $F'$ with paired identifications

$$
A[\lambda]\simeq
\bar\rho|_{G_{F'}}\otimes_k k_\lambda,
\qquad
A[\mathfrak q]\simeq
\bar\sigma|_{G_{F'}}\otimes_{k_q}k_{\mathfrak q}, \tag{1.3}
$$

where $\bar\sigma$ is a dihedral residual representation already known to be automorphic. The bridge is

$$
\begin{array}{ccccc}
\bar\sigma|_{G_{F'}}&\longleftarrow&A[\mathfrak q]&\longrightarrow&V_{\mathfrak q}(A)\\
\text{residually automorphic}&&&&\text{automorphic only after lifting}\\[2mm]
&&A&&\\[-1mm]
\bar\rho|_{G_{F'}}&\longleftarrow&A[\lambda]&\longleftarrow&V_\lambda(A).
\end{array} \tag{1.4}
$$

Only the upper-right arrow is a modularity-lifting step. The passage from the $\mathfrak q$-adic factor to the $\lambda$-adic factor goes through one automorphic packet and common algebraic Frobenius polynomials. There is no scalar extension from a $q$-adic completion to an $\ell$-adic completion.

### 1.3 Frobenius, covariance, and determinant

For a number field $K$, write $G_K=\operatorname{Gal}(\overline K/K)$. Arithmetic Frobenius is used at finite unramified places. Tate modules are covariant:

$$
T_\nu(A)=\varprojlim_n A[\nu^n](\overline K),
\qquad
V_\nu(A)=T_\nu(A)\otimes_{\mathcal O_{M,\nu}}M_\nu. \tag{1.5}
$$

Book 127 first constructs a cohomological representation in geometric-Frobenius normalization. In this book $\rho_{\Pi,\nu}$ denotes its covariant dual. When the finite central character is trivial,

$$
\det\rho_{\Pi,\nu}=\chi_\nu,
$$

and at a good place $v\nmid\nu$ its arithmetic-Frobenius polynomial is

$$
P_v(X)=X^2-a_v(\Pi)X+q_v. \tag{1.6}
$$

If a finite central character occurs, its placement must be derived from Book 127's component character and the dual convention. No finite character is absorbed into a polarization by notation. The main theorem uses the trivial finite-character, cyclotomic-determinant case.

### 1.4 The boundary of the book

The topic is one residual two-prime transfer in parallel weight two. The coefficient characteristics satisfy $\ell,q\geq7$. The target has cyclotomic determinant and an integral finite-flat model at every place above $\ell$. The auxiliary member has the corresponding properties at $q$. Every pairing, local model, moduli component, residual automorphic localization, component-support statement, and compact curve-carrier construction used in the proof is named.

No theorem is asserted in characteristic five. No arbitrary determinant is treated. No chosen characteristic-zero lift is made automorphic. No compatible system over the original field is constructed. No automorphy is descended from the potential-modularity field to $F$. In particular, no unitary-surface realization, surface comparison theorem, or central automorphic descent is used.

## 2. The exact input datum

The two-prime argument begins with a ledger rather than with a moduli point. This ordering is forced by the proof: the moduli space depends on determinant lines and coefficient fields, local nonemptiness depends on actual integral models, and modularity lifting depends on components and automorphic support that a torsion isomorphism does not create.

### 2.1 The residual target

Assume that (1.1) is absolutely irreducible and totally odd, and that

$$
\det\bar\rho=\bar\chi_\ell. \tag{2.1}
$$

We also require

$$
\bar\rho|_{G_{F(\zeta_\ell)}}
\text{ to be absolutely irreducible} \tag{2.2}
$$

and

$$
H^0\!\left(F,\operatorname{ad}^0\bar\rho(1)\right)=0. \tag{2.3}
$$

The two conditions have different roles. Condition (2.2), together with the characteristic bound and the precise image theorem being used, supplies the Taylor--Wiles adequacy input. Condition (2.3) is the adjoint cyclotomic invariant needed by the global deformation calculation. It is retained separately rather than inferred from the word “adequate.”

Absolute irreducibility always means geometric absolute irreducibility, after extension of the residue field to an algebraic closure. It ensures uniqueness of stable-lattice reduction and makes the eventual Hecke maximal ideal non-Eisenstein. Reducible, merely semisimple, and scalar targets lie outside this book.

### 2.2 Pairings and coefficient change

The determinant equality (2.1) is accompanied by a chosen Galois-equivariant isomorphism

$$
\delta_\ell:\bigwedge^2\bar\rho\xrightarrow{\sim}k(1). \tag{2.4}
$$

This choice matters. Multiplying $\delta_\ell$ by a nonsquare can move the frame to another symplectic component, even when the underlying Galois module is unchanged.

The coefficient construction supplies $M$, $\lambda\mid\ell$, and an embedding $k\hookrightarrow k_\lambda$. When the residue fields have been chosen isomorphic no enlargement is necessary; the slightly more flexible notation

$$
V_\ell=\bar\rho\otimes_k k_\lambda \tag{2.5}
$$

allows a declared finite scalar extension. This remains rank two over $k_\lambda$. Restriction of scalars is not used, because it would change the dimension. The pairing is extended to

$$
\bigwedge^2V_\ell\xrightarrow{\sim}k_\lambda(1). \tag{2.6}
$$

Every later coefficient enlargement is likewise an extension of scalars to one common coefficient field. No equality between representations over different local completions is written before such a field is chosen.

### 2.3 The coefficient-prime local model

For every $v\mid\ell$, the restriction $\bar\rho|_{G_{F_v}}$ is required to be the generic fiber of a paired coefficient-linear finite locally free group scheme $\mathcal G_v$. After the declared coefficient extension, there is a model $\mathcal G_{v,\lambda}$ with generic fiber $V_\ell|_{G_{F_v}}$.

The local field $F_v/\mathbf Q_\ell$ is unramified whenever the clean unramified finite-flat theorem is used. The named residual Schur and representability hypotheses are checked after coefficient extension. In a line-enhanced ordinary problem, the connected--etale filtration and its ordered characters are part of the model. In a local--local problem no ordinary line is introduced.

The phrase “finite flat” means more than Hodge--Tate weights. It means that every torsion quotient in the selected lift is represented by a compatible finite locally free group scheme. For the residual moduli problem it means that the exact group scheme $\mathcal G_{v,\lambda}$, with coefficient action, Cartier duality, and pairing, is to occur as $\lambda$-torsion of the local Hilbert--Blumenthal seed. A rational crystalline representation or an abstract generic-fiber isomorphism does not supply this model.

### 2.4 The pre-specialization ledger

A **pre-specialization two-prime datum** consists of the following information.

1. The target data of Sections 2.1--2.3, with $\ell\geq7$.
2. A distinct prime $q\geq7$ and a dihedral residual representation $\bar\sigma$ in characteristic $q$, with cyclotomic determinant pairing, cyclotomic absolute irreducibility, adequacy, adjoint vanishing, and the required paired finite-flat models at places above $q$.
3. The actual auxiliary coefficient field, a totally real multiplication field $M$, primes $\lambda\mid\ell$ and $\mathfrak q\mid q$, and declared residue-field identifications or scalar extensions.
4. An ordered polarization module, determinant-line generators at $\lambda$ and $\mathfrak q$, and a neat auxiliary level prime to $\ell q$.
5. One $F$-defined smooth geometrically connected component of the paired-frame twist, with full product geometric monodromy and a universal Hilbert--Blumenthal abelian variety.
6. At every place in one finite local set, an actual simultaneous local Hilbert--Blumenthal object on that same component, carrying both paired frames and every required integral or semistable model.
7. A finite Galois avoidance field containing the full residual cutout fields and every cyclotomic, component, pairing, and self-twist field whose intersection would invalidate a later step.
8. A selected auxiliary level-raising place satisfying the joint target, auxiliary, and constant-field Frobenius conditions of (3.7)--(3.8), with its lower residual automorphic class, invariant line, sign, determinant, and generic conductor-one special face.

Items 1--8 precede specialization. They are not consequences of the first three conditions on $\bar\rho$. Book 158 constructs the paired-frame space and its point-centered local-open package from its admissible moduli datum. Only that interior package and the split Moret--Bailly specialization are used below. Book 158 also records the regular symmetric normal-top refinement needed when the specialization field itself must be retained as a totally real Galois field disjoint from the full avoidance field; no toroidal compactification or singleton mixed packet is an antecedent of either split construction. The character, coefficient, and localization choices in items 2--4 and 8 are supplied explicitly below from Book 98 and the globally upstream finite-quotient prime-selection theorem; no conclusion of a later potential-modularity book is used. Post-specialization cleanability is not included here, because the actual bad-place set is known only after the specialized abelian variety exists. The curve carrier is likewise not assumed: once lifting has retained the selected special place, Section 9.2 constructs it from Books 104 and 127.

## 3. The dihedral automorphic seed

The target residual representation is not initially automorphic, so it cannot seed a lifting theorem. A dihedral representation is useful because its automorphy can be rebuilt over an arbitrary disjoint point field by automorphic induction, without asserting nonsolvable base change for a general cusp form.

### 3.1 Quadratic induction and its determinant

Let $K/F$ be a CM quadratic extension with nontrivial automorphism $c$. Choose an algebraic Hecke character $\Theta$ of $K$ of parallel CM type $(1,0)$ in Book 98's arithmetic normalization. Let $\mathcal O_q$ be the valuation ring of a finite $q$-adic field containing its values and let $k_q$ be the residue field. The $q$-adic avatar is

$$
\theta_q:G_K\longrightarrow\mathcal O_q^\times.
$$

Let $\bar\theta$ be its reduction and define

$$
\bar\sigma=\operatorname{Ind}_{G_K}^{G_F}\bar\theta. \tag{3.1}
$$

The conjugate-ratio condition

$$
\bar\theta\ne\bar\theta^c \tag{3.2}
$$

makes (3.1) absolutely irreducible. In a coset basis, an element outside $G_K$ exchanges the two character lines, so every real complex conjugation has eigenvalues $1$ and $-1$.

The determinant contains the quadratic sign. If $\epsilon_{K/F}$ is the quadratic character and $\operatorname{Ver}:G_F^{\mathrm{ab}}\to G_K^{\mathrm{ab}}$ is transfer, then

$$
\det\bar\sigma
=\epsilon_{K/F}\,(\bar\theta\circ\operatorname{Ver}). \tag{3.3}
$$

Book 98, Theorem 14.1, makes this character equal to $\bar\chi_q$ once the ray-unit and determinant compatibilities have been verified and finitely many auxiliary conductor places are allowed. Its proof extends one character of a subgroup of a finite ray class group, then excludes the finitely many coefficient primes that kill a chosen conjugate-ratio or inertial witness. The finite-flat coefficient-prime branch is not a consequence of ray-class extension: its paired group scheme is separately part of the pre-specialization datum. Equality of determinants is accompanied by a chosen pairing

$$
\delta_q:\bigwedge^2\bar\sigma\xrightarrow{\sim}k_q(1). \tag{3.4}
$$

Book 98 then gives a cuspidal parallel-weight-two automorphic induction $\Pi_0=\operatorname{AI}_{K/F}(\Theta)$. Cuspidality follows from noninvariance of $\Theta$, not from local supercuspidality. The residual lattice is the explicit induced lattice, and (3.2) removes any lattice ambiguity.

### 3.2 Choosing the auxiliary prime in the correct order

The order of construction prevents a coefficient-field circle.

First choose the CM extension, the finite ray data, and the protected determinant and irreducibility witnesses. Next choose $q\geq7$ outside the target ramification set and every finite exceptional set, and build $\Theta$ with the required finite-flat branches at $q$. Only then choose a place of the actual character-value field above $q$ and form $\bar\sigma$ over its actual residue field.

After both residual coefficient fields are fixed, choose the totally real multiplication field $M$, the primes $\lambda$ and $\mathfrak q$, and the inverse-different polarization line as part of Book 158's admissible two-prime coefficient datum. The residue maps must receive the two actual finite coefficient fields, the rational primes must be unramified in $M$, and the chosen levels must satisfy Book 158's full-product monodromy criterion. These are explicit algebraic conditions on the datum, not a conclusion imported from a later two-prime theorem. Choosing $M$ before the character-value field exists would silently change the residue field of the auxiliary representation.

At places above $q$, the local characters of $\Theta$ must give the named paired finite-flat model. At places above $\ell$, the auxiliary prime-to-$\ell$ module must occur on the same good-reduction seed that carries $\mathcal G_{v,\lambda}$. Conversely, the target module must be unramified at places above $q$ in the clean good-reduction construction and must match the actual prime-to-$q$ Frobenius module of the auxiliary local seed. These are simultaneous local-model conditions, not consequences of the inequality $q\ne\ell$.

### 3.3 Residual automorphy after an arbitrary point field

Let $F'/F$ be a finite extension with $F'\cap K=F$, and put $K'=KF'$. Then $K'/F'$ is CM quadratic. Mackey restriction gives

$$
\bar\sigma|_{G_{F'}}
\simeq
\operatorname{Ind}_{G_{K'}}^{G_{F'}}
\left(\bar\theta|_{G_{K'}}\right). \tag{3.5}
$$

Pull $\Theta$ back by the norm $\mathbf A_{K'}^\times\to\mathbf A_K^\times$. Book 98 supplies

$$
\Pi_0'=\operatorname{AI}_{K'/F'}
\left(\Theta\circ N_{K'/K}\right). \tag{3.6}
$$

Its residual representation is (3.5). It is cuspidal: if the pulled-back character were invariant, the residual induction would split, contrary to preservation of the absolutely irreducible image. Its infinity type remains parallel weight two, and transfer in the Cartesian quadratic square preserves the determinant equation (3.3).

This proof uses no solvability of $F'/F$. It does not base change a general rank-two automorphic representation through a nonsolvable field. It constructs the dihedral packet anew over $F'$. The same argument works over a further totally real field $E$ as long as $E$ remains disjoint from the quadratic and residual cutout fields.

### 3.4 The selected residual localization

Residual automorphy must occur in the Hecke localization required by lifting, not merely at almost all Frobenius elements. Choose a place $v_0\nmid\ell q$ at which the two auxiliary residual Frobenius roots satisfy the ordered conditions

$$
\alpha=q_{v_0}\beta,
\qquad
\beta=1,
\qquad
q_{v_0}\not\equiv1,-1\pmod q. \tag{3.7}
$$

At the same place require

$$
\bar\rho(\operatorname{Frob}_{v_0})=1,
\qquad
\bar\chi_\ell(\operatorname{Frob}_{v_0})=1. \tag{3.8}
$$

Require also the auxiliary-level, component, and determinant-line fields used by the local moduli point to split. Thus the ordered auxiliary roots are exactly $(q_{v_0},1)$, while the target roots are $(1,1)$. The pre-specialization ledger requires one compatible conjugacy class in the joint finite Galois quotient. The globally upstream finite-quotient Chebotarev theorem then supplies $v_0$. Separate applications to the individual quotients would not prove that their Frobenius requirements occur at one place.

The clean level-raising input retains the ordered root, invariant line, sign, determinant, and non-Eisenstein maximal ideal. Its lower face is the exact dihedral automorphic class, and its selected upper face is conductor-one special with nonzero monodromy. In the generic regime (3.7) this is the distinct-root face of Book 176, not the scalar-twist augmentation of Book 175. Saturated degeneracy maps, the primary and companion type lattices, and local--global compatibility are additional hypotheses of this localization; the congruences (3.7)--(3.8) alone do not produce them.

The conditions $q_{v_0}\not\equiv\pm1\pmod q$ are part of the clean selected theorem. Scalar and vexing residual Frobenius at later, specialization-dependent places are not thereby excluded. They are one reason the post-specialization lifting step requires a separate audit.

## 4. The paired-frame realization space

Moret--Bailly's theorem globalizes local points on a smooth geometrically connected variety. It does not create the variety, select an arithmetic component, or remove automorphisms. Those tasks belong to the paired-frame Hilbert--Blumenthal construction.

### 4.1 The Hilbert--Blumenthal datum

Let $g=[M:\mathbf Q]$. Fix the ordered inverse-different polarization datum and a neat auxiliary level of order prime to $\ell q$. A point of the untwisted fine space consists of

$$
(A,\iota,\lambda_A,\eta_N), \tag{4.1}
$$

where $A$ is an abelian variety of dimension $g$, $\iota:\mathcal O_M\hookrightarrow\operatorname{End}(A)$, $\lambda_A$ has the prescribed polarization type and positivity orientation, and $\eta_N$ is the rigidification. The determinant condition is

$$
\det(T-\iota(a)\mid\operatorname{Lie}A)
=\prod_{\tau:M\hookrightarrow\overline{\mathbf Q}}(T-\tau(a)). \tag{4.2}
$$

The neat level kills automorphisms. The ordered polarization fixes the narrow-class and real-orientation data needed to speak about one arithmetic component. These structures cannot be recovered from the abstract $\mathcal O_M$-action after the moduli point has been chosen.

At a prime $\nu$ not dividing the polarization degree, the polarization gives an alternating form on the rank-two $\nu$-factor with values in a one-dimensional coefficient line. The chosen inverse-different convention and a generator of that line identify it with $k_\nu(1)$. Changing the generator changes the symplectic coordinate, so the same choice is used in (2.6), (3.4), and every local seed.

### 4.2 Twisted paired frames

Add pairing-preserving isomorphisms

$$
\alpha_\ell:V_\ell\xrightarrow{\sim}A[\lambda],
\qquad
\alpha_q:V_q\xrightarrow{\sim}A[\mathfrak q], \tag{4.3}
$$

where $V_q=\bar\sigma\otimes_{k_q}k_{\mathfrak q}$. After both residual modules are split, these frames form a torsor under

$$
\operatorname{SL}_2(k_\lambda)
\times
\operatorname{SL}_2(k_{\mathfrak q}). \tag{4.4}
$$

The special linear groups, rather than the full general linear groups, appear because the pairing lines have been fixed. If the determinant cocycle landed only in a similitude group, it could permute the pairing components. Twisting the standard paired-frame cover by the product Galois cocycle gives a variety

$$
X=X(\bar\rho,\bar\sigma). \tag{4.5}
$$

An $L$-point of $X$ is an actual Hilbert--Blumenthal abelian variety over $L$ with the two equivariant paired frames. Fineness is essential: a point on a coarse space might represent only a geometric isomorphism class with a descent obstruction.

### 4.3 Fineness, smoothness, and dimension

Book 158 proves the fine-space theorem for the exact datum just described. The deformation calculation is worth recalling because it explains why the two frames do not overdetermine the problem. De Rham cohomology splits as

$$
H^1_{\mathrm{dR}}(A)=\bigoplus_\tau H_\tau,
\qquad
\dim H_\tau=2,
\qquad
\dim\omega_\tau=1. \tag{4.6}
$$

Across a square-zero extension, lifting the Hodge filtration amounts to lifting one line in each two-dimensional alternating plane. A lift of $\omega_\tau$ is the graph of a map

$$
\omega_\tau\longrightarrow(H_\tau/\omega_\tau)\otimes I, \tag{4.7}
$$

so there is one deformation parameter for every real embedding and no quadratic isotropy equation in that factor. The auxiliary level and the two coefficient-prime frames are finite etale on the characteristic-zero generic fiber, hence lift uniquely. Thus

$$
X/F\text{ is smooth of pure dimension }g. \tag{4.8}
$$

This argument says nothing about a full-level integral model in residue characteristic $\ell$ or $q$. Integral behavior at those primes is supplied by the local objects of Chapter 5.

### 4.4 One arithmetic component and product monodromy

The untwisted Hilbert--Blumenthal space can have several geometric and arithmetic components, indexed by polarization, orientation, and finite determinant data. The pre-specialization datum selects one component defined over the working totally real field and requires every local seed to lie on its twist. Local points on different components cannot be combined by intersecting their neighborhoods.

On the selected component, Book 158's monodromy hypothesis gives the full product (4.4). Connected components of the frame cover are the orbits of geometric fundamental-group monodromy on one fiber. Full product monodromy acts transitively, so the cover is geometrically connected. Separate surjectivity to the two factors would not suffice: a graph of a common quotient can project surjectively to both factors while having several orbits.

Twisting changes only arithmetic descent and becomes trivial over $\overline F$. Hence the selected twist remains geometrically connected. The exact geometric output is

$$
X/F\text{ smooth, geometrically connected, quasi-projective, fine,}
\quad \dim X=g>0, \tag{4.9}
$$

with a universal Hilbert--Blumenthal abelian variety. This is the whole geometric input to the arithmetic existence step. It does not include a number-field point or any automorphy statement.

## 5. Local models and nonempty opens

The local hypotheses are most easily misstated at the coefficient primes. A generic torsion representation does not determine its finite-flat model, and two separately realizable torsion modules need not occur on the same abelian variety. The proof therefore starts at every controlled place with one simultaneous local object carrying the complete moduli datum.

### 5.1 One simultaneous local witness

Let $S$ contain all real places, all places above $\ell q$, every place where either residual representation or the moduli datum is ramified, and every place at which a special reduction condition is prescribed. For each $v\in S$, the datum supplies a Hilbert--Blumenthal abelian variety

$$
B_v/F_v \tag{5.1}
$$

on the selected component, with its polarization, orientation, auxiliary level, and paired maps

$$
V_\ell|_{G_{F_v}}\xrightarrow{\sim}B_v[\lambda],
\qquad
V_q|_{G_{F_v}}\xrightarrow{\sim}B_v[\mathfrak q]. \tag{5.2}
$$

At a coefficient-prime place the relevant map extends over $\mathcal O_{F_v}$ as an isomorphism of coefficient-linear paired finite locally free group schemes. At a semistable place, (5.1) includes the semiabelian model, toric rank, Kummer parameter, invariant line, and sign. A local object obtained only after a finite extension belongs to the datum only if that exact completion algebra is carried into the Moret--Bailly input; the split version used below instead assumes the object over $F_v$ itself.

Only after (5.1)--(5.2) have been exhibited do we choose a neighborhood $\Omega_v$. Nonempty opens for separate conditions cannot be intersected without a point satisfying all of them.

### 5.2 Real places

At a real place, an odd two-dimensional representation in odd characteristic has a $+1$ line and a $-1$ line. A polarized real Hilbert--Blumenthal rank-two factor has the same involution type. Bases of the two eigenspaces can therefore be scaled to match the prescribed alternating pairing.

Oddness removes this linear-algebra obstruction, but it does not choose the polarization orientation or make an auxiliary rigidification real. The datum contains a real point on the selected orientation component with an auxiliary-level orbit compatible with conjugation. A constant full odd-order frame is not automatically compatible: it would ask complex conjugation to act trivially on a module on which it has eigenvalues $1$ and $-1$.

A small neighborhood in the real manifold $X(F_v)$ remains in the same orientation component. Requiring every conjugate of the global point to lie in that neighborhood is what later forces total reality with the correct real component.

### 5.3 Places above the target prime

Let $v\mid\ell$. The local seed extends to an abelian scheme $\mathcal B_v/\mathcal O_{F_v}$ with good reduction and carries an isomorphism

$$
\mathcal G_{v,\lambda}\xrightarrow{\sim}\mathcal B_v[\lambda] \tag{5.3}
$$

compatible with the $\mathcal O_M$-action, Cartier duality, and the polarization pairing. This is the exact local model used later. Finite flatness of the generic target alone does not construct (5.3).

For an ordinary seed, its connected--etale sequence has paired unramified twists of the schematic form

$$
0\longrightarrow
\mu_\ell\otimes_{\mathbf F_\ell}k_\lambda
\longrightarrow\mathcal B_v[\lambda]
\longrightarrow
(\mathbf Z/\ell\mathbf Z)\otimes_{\mathbf F_\ell}k_\lambda
\longrightarrow0, \tag{5.4}
$$

after the twists have been displayed. The ordered characters and extension class must match $\mathcal G_{v,\lambda}$. For a local--local seed, the connected height-two factor itself is part of the model and no ordinary line is asserted.

The $\mathfrak q$-torsion is prime to the residue characteristic. Good reduction makes it unramified, but its full Frobenius module still has to equal $V_q|_{G_{F_v}}$. A choice of basis cannot alter its eigenvalues. Thus (5.3) and the actual $\mathfrak q$-torsion comparison are simultaneous requirements on one $\mathcal B_v$.

### 5.4 Places above the auxiliary prime

Let $v\mid q$. Reverse the two roles. The auxiliary residual representation has a named paired finite locally free model $\mathcal H_{v,\mathfrak q}$, and the good-reduction seed carries

$$
\mathcal H_{v,\mathfrak q}\xrightarrow{\sim}\mathcal B_v[\mathfrak q]. \tag{5.5}
$$

The coefficient action is integral, so this is a finite-flat kernel, not the image of a rational idempotent with a $q$-denominator. The local field and the completion of $M$ are unramified in the range of the clean finite-flat theorem, and the residual Schur hypotheses are checked for the coefficient-extended model.

The $\lambda$-torsion is prime to $q$. In the good-reduction construction it is unramified and must match the full Frobenius module of $V_\ell|_{G_{F_v}}$. Consequently the auxiliary prime was chosen outside the ramification set of $\bar\rho$. If the target is ramified at $v$, a different semistable coefficient-prime theorem and a different local seed would be needed; this book does not infer such a variant from generic finite etaleness.

### 5.5 Semistable places

At a place $v\nmid\ell q$ where a special condition is prescribed, the seed has toric rank one on the relevant rank-two factor. In covariant normalization its Weil--Deligne representation has

$$
N\ne0,
\qquad
N^2=0, \tag{5.6}
$$

together with a selected invariant line and unramified sign. A Tate curve makes the shared-parameter constraint explicit. If $t\in F_v^\times$ with $v(t)>0$, then for $n$ prime to the residue characteristic,

$$
0\longrightarrow\mu_n
\longrightarrow E_t[n]
\longrightarrow\mathbf Z/n\mathbf Z
\longrightarrow0, \tag{5.7}
$$

and the extension class is the Kummer class of $t$ in $F_v^\times/(F_v^\times)^n$. The $\ell$- and $q$-torsion classes on one local object must therefore be the images of one $t$. Two arbitrary upper-triangular modules with incompatible Kummer classes cannot be installed on the same Tate object.

At the selected place $v_0$, the Tate parameter is chosen so that both residual Kummer classes vanish while the characteristic-zero monodromy remains nonzero. This puts the auxiliary residual system on the exact lower localization of Section 3.4 and the Tate module on its selected conductor-one special face.

### 5.6 From a local model to an open

The paired frames are already part of the twisted moduli space and persist on it. The integral and reduction properties require smaller neighborhoods.

For good reduction, take the residue tube of the chosen smooth integral point. For the finite-flat condition, use the named local-model theorem to keep the universal kernel on the selected finite-flat component. For ordinary reduction, remain in the Hasse-invariant open; for local--local reduction, remain in the tube of the fixed special point. For semistable reduction, work in a boundary chart and impose valuation and unit conditions on the degeneration parameter while avoiding deeper boundary intersections. Prime-to-residue-characteristic finite etale local systems are locally constant.

These arguments give a nonempty open

$$
\varnothing\ne\Omega_v\subset X(F_v) \tag{5.8}
$$

around the one simultaneous witness. The proof of nonemptiness is the witness; the proof of openness is the residue-tube, local-model, finite-etale, boundary, or real-manifold argument. Smoothness of the characteristic-zero moduli space alone proves neither assertion.

## 6. The controlled totally real specialization

Once the geometry and every local open have been verified, one arithmetic existence theorem chooses one field and one point simultaneously. Applying approximation separately at the two coefficient primes would produce unrelated fields and unrelated abelian varieties.

### 6.1 The avoidance field

Let $L_\rho/F$ and $L_\sigma/F$ be the finite Galois extensions fixed by the kernels of the two residual representations. Choose a finite Galois extension $D/F$ containing

- $L_\rho L_\sigma$ and the CM field $K$;
- the joint residual--cyclotomic cutout fields needed for (2.2)--(2.3) and their $q$-adic analogues;
- all component, pairing, and auxiliary-level descent fields; and
- every finite self-twist or image-detection field used by the residual automorphic localization and lifting datum.

The full matrix cutout fields are used, not only the projective fields. Taking $D/F$ Galois makes

$$
F'\cap D=F \tag{6.1}
$$

equivalent to linear disjointness. A nonnormal root field would not control intersections with its normal closure.

### 6.2 The Moret--Bailly step

Apply Book 154 to the smooth geometrically connected variety $X/F$, the finite set $S$, the nonempty opens $\Omega_v$, and the avoidance field $D$. In the split formulation, it produces a closed point with residue field $F'$ such that

$$
F'\otimes_FF_v\simeq F_v^{[F':F]}
\qquad(v\in S), \tag{6.2}
$$

every conjugate local point lies in $\Omega_v$, and $F'$ is linearly disjoint from $D$.

Choose the moving degree even. In Book 154's split moving-family proof the degree is sufficiently divisible rather than prescribed in advance; replacing the auxiliary ample bundle by its square makes every resulting divisor degree even without changing any local open. Hence we may and do require

$$
[F':F]\equiv0\pmod2,
\qquad [F':\mathbf Q]\text{ even}. \tag{6.2a}
$$

This parity choice is used only to construct the compact one-split curve carrier in Section 9.2.

All real places belong to $S$. Hence every embedding of $F'$ is real, so $F'/F$ is finite totally real. Complete splitting means every place $w\mid v$ has $F'_w=F_v$. This preserves the coefficient-prime local fields and makes the prescribed condition hold at every place above $v$, not at one favored completion.

The theorem uses a connected finite etale incidence fiber to make the residue algebra a field and a second Hilbert condition after base change to $D$ to impose disjointness. It does not make $F'/F$ Galois or solvable.

### 6.3 Image preservation

The group-theoretic step is elementary but load-bearing.

**Lemma 6.1.** Let $r:G_F\to H$ have finite image, let $L/F$ be the finite Galois extension fixed by $\ker r$, and let $E/F$ be finite. If $E\cap L=F$, then

$$
r(G_E)=r(G_F). \tag{6.3}
$$

**Proof.** Disjointness and normality give

$$
\operatorname{Gal}(EL/E)\xrightarrow{\sim}\operatorname{Gal}(L/F).
$$

The restriction map from $G_E$ onto the group on the left is surjective. Identifying the group on the right with $r(G_F)$ proves that every element of the original image occurs after restriction. The reverse inclusion is immediate. $\square$

Apply the lemma to both residual representations and to their joint actions with the residual cyclotomic characters. Then

$$
\bar\rho(G_{F'})=\bar\rho(G_F),
\qquad
\bar\sigma(G_{F'})=\bar\sigma(G_F), \tag{6.4}
$$

and the cyclotomic-restriction images are unchanged. Absolute irreducibility, adequacy, endomorphism rings, and the adjoint invariant calculations are therefore preserved for the exact reasons recorded in the datum.

### 6.4 The exact field profile

The basic field has precisely the following properties:

$$
\begin{array}{c|c}
\text{property}&\text{conclusion}\\ \hline
\text{finite and totally real over }F&\text{yes}\\
\text{even absolute degree}&\text{yes}\\
\text{split completely at every }v\in S&\text{yes}\\
\text{linearly disjoint from }D&\text{yes}\\
\text{Galois over }F&\text{not asserted}\\
\text{solvable over }F&\text{not asserted}\\
\text{normal closure disjoint from }D&\text{not asserted}.
\end{array} \tag{6.5}
$$

Passing to the normal closure requires a new disjointness proof. A further extension can shrink a residual image even though (6.4) holds over $F'$. Likewise, a field of solvable degree is not thereby a solvable extension. The proof below uses the dihedral reconstruction of Section 3.3 and therefore needs no general base change across $F'/F$.

## 7. The specialized abelian variety

Pulling the universal family back to the Moret--Bailly point turns the two-prime moduli problem into one arithmetic object. This chapter separates what the specialization actually gives from the automorphic information still missing.

### 7.1 The two exact torsion frames

Let $x\in X(F')$ be the point supplied in Chapter 6. Pullback gives a Hilbert--Blumenthal abelian variety

$$
(A,\iota,\lambda_A,\eta_N)/F' \tag{7.1}
$$

and pairing-preserving isomorphisms

$$
\alpha_\ell:
\bar\rho|_{G_{F'}}\otimes_k k_\lambda
\xrightarrow{\sim}A[\lambda], \tag{7.2}
$$

$$
\alpha_q:
\bar\sigma|_{G_{F'}}\otimes_{k_q}k_{\mathfrak q}
\xrightarrow{\sim}A[\mathfrak q]. \tag{7.3}
$$

These are exact representations, not only semisimplifications, because the frames are part of the fine moduli problem. The scalar extensions are displayed. The rank-two factors are the $\lambda$- and $\mathfrak q$-kernels selected by the integral $\mathcal O_M$-action, not the full $2g$-dimensional torsion modules.

The pairings give

$$
\det A[\lambda]=\bar\chi_\ell|_{G_{F'}},
\qquad
\det A[\mathfrak q]=\bar\chi_q|_{G_{F'}}, \tag{7.4}
$$

and, in the fixed polarization-line normalization,

$$
\det V_\lambda(A)=\chi_\ell,
\qquad
\det V_{\mathfrak q}(A)=\chi_q. \tag{7.5}
$$

### 7.2 Integral coefficient-prime models

For every $w\mid v\mid\ell$, complete splitting identifies $F'_w$ with $F_v$. Membership of the local point in $\Omega_v$ upgrades (7.2) to the chosen isomorphism

$$
\mathcal G_{v,\lambda}\xrightarrow{\sim}\mathcal A[\lambda]
\quad\text{over }\mathcal O_{F'_w}. \tag{7.6}
$$

Likewise, for $w\mid v\mid q$, one has the selected model

$$
\mathcal H_{v,\mathfrak q}\xrightarrow{\sim}\mathcal A[\mathfrak q]
\quad\text{over }\mathcal O_{F'_w}. \tag{7.7}
$$

The good-reduction abelian scheme provides all torsion levels $\mathcal A[\mathfrak q^n]$ and $\mathcal A[\lambda^n]$. Thus the two Tate factors satisfy the integral finite-flat condition of type $(0,1)$ at their respective coefficient primes. This conclusion comes from the abelian scheme and integral coefficient action; it is not deduced from the residual frame.

At every other place above $S$, the exact real, good, or semistable condition imposed in Chapter 5 holds. In particular, every place above the selected place $v_0$ retains its invariant line, sign, and nonzero characteristic-zero monodromy.

### 7.3 The actual bad-place set

The finite set of bad reduction places of $A$ is known only after $x$ has been chosen. Denote it by $B_A$. A useful safeguard is to include a full auxiliary level of order $N\geq3$, prime to $\ell q$, whose descent local system is unramified outside $S$. At a place outside $S$ the specialized full $N$-torsion is then unramified, and the semistable reduction criterion makes $A$ semistable there.

Consequently every new bad place in

$$
P_A=B_A\setminus S \tag{7.8}
$$

is semistable. On a rank-two coefficient factor the local representation is unramified or special with rank-one monodromy. This does not make the place clean. Residual Frobenius can be scalar, the congruence $q_w\equiv-1$ can make both signed Gram factors nonunits, monodromy can vanish after reduction, and an ordered invariant line can remain necessary.

For each $w\in P_A$, one must compute and record

$$
(\text{residual Frobenius},\ \text{line},\ \text{sign},\
\text{determinant},\ N_w,\ \text{local component}). \tag{7.9}
$$

Semistability proves only the coarse unramified-or-special alternative. It does not prove that the integral automorphic level-change theorem covers the displayed point.

### 7.4 Local membership is not automorphic support

The Galois representation $V_{\mathfrak q}(A)$ defines a point on a named product of local deformation components. This is the local half of a lifting datum. The automorphic half asks whether the faithful Hecke module meets that same product component and whether its integral structure survives every required augmentation.

At a newly discovered $w\in P_A$, the dihedral packet of Section 3.3 is normally unramified and supplies a lower-level residual class. The Tate module supplies the desired special component. Neither fact produces the mixed-level automorphic class. Required additional objects include the exact lower and intermediate face classes, saturated primary and companion lattices, the selected flags and signs, integral vanishing-cycle and branch corrections, and the faithful order-valued Galois representation factoring through the product local condition.

The same warning already applies to the controlled places above $v_0$. Complete splitting preserves their local models but creates one such place for every embedding of $F'$ over $F$. Individual selected localizations at those places do not supply joint support on their product.

Thus the implication

$$
\text{$V_{\mathfrak q}(A)$ lies on a represented local product}
\quad\Longrightarrow\quad
\text{that product has automorphic support} \tag{7.10}
$$

is false without a support theorem. Chapter 8 records that theorem as a hypothesis rather than building it into the word “semistable.”

## 8. Cleanability and auxiliary-prime lifting

The specialized auxiliary torsion is residually automorphic, but residual automorphy is only the entry condition for modularity lifting. The characteristic-zero Tate factor becomes automorphic only after every local, integral, support, and reciprocity hypothesis of the chosen Book 176 route has been checked over the actual field of application.

### 8.1 The auxiliary-adic representation

Write

$$
r_{A,q}:G_{F'}\longrightarrow
\operatorname{GL}_2(\mathcal O_{M,\mathfrak q}) \tag{8.1}
$$

for the action on $T_{\mathfrak q}(A)$. Then

$$
\det r_{A,q}=\chi_q, \tag{8.2}
$$

and

$$
\bar r_{A,q}\simeq
\bar\sigma|_{G_{F'}}\otimes_{k_q}k_{\mathfrak q} \tag{8.3}
$$

with the chosen pairing. By (6.4), the residual representation remains absolutely irreducible on the required cyclotomic subgroup, adequate in the stated characteristic range, and subject to the same adjoint-invariant calculation. At every $w\mid q$, (7.7) gives all-level finite-flat quotients over an unramified local field.

The ramification set of $r_{A,q}$ is finite. Its nonminimal comparison set includes every place above $v_0$ and the specialization-dependent set $P_A$ where monodromy is nonzero. A lifting theorem must use the actual set, not the smaller set known before the moduli point was chosen.

### 8.2 The residual automorphic localization

Section 3.3 produces a cuspidal parallel-weight-two packet $\Pi_0'$ over $F'$ whose residual representation is (8.3). This is exact residual automorphy over the patching field. It does not rely on solvable base change across the Moret--Bailly extension.

For lifting, the residual eigensystem must occur in a non-Eisenstein compact weight-two carrier with the precise local labels. At every $w\mid v_0$, the level-raising input must supply the generic conductor-one special face with its line and sign. At every place where $\Pi_0'$ has superfluous level, an independent integral level-lowering theorem is required. At every place where $r_{A,q}$ has more level, an independent integral level-raising or finite-set support theorem is required.

The lower residual class, its localized type module, and the faithful Hecke order are part of the cleanability record. Equality of good residual Frobenius polynomials would determine only the residual eigensystem; it would not place that eigensystem on the required integral component.

### 8.3 The exact cleanability record

Let $P_{\mathrm{act}}$ be the finite set of places of $F'$ at which the local condition of $r_{A,q}$ differs from the lower residual automorphic carrier. It contains every $w\mid v_0$ and every $w\in P_A$ at which the Tate factor has nonzero monodromy; any other controlled type change is added as well. Because $v_0$ splits completely in the split Moret--Bailly construction,

$$
\#\{w:w\mid v_0\}=[F':F].
$$

Thus the active set can have several places even when $P_A$ is empty. Call the specialization **auxiliary-prime cleanable** if the following facts are verified for $r_{A,q}$ and this actual set $P_{\mathrm{act}}$.

The face, type, residue, and augmentation clauses below are route-relative. On the direct
$({\rm IAV}_{P_{\mathrm{act}}})$ route, clauses that quantify over one-prime faces, cubical
shadows, switching residues, or their augmentations are vacuous; they are replaced by the
paired finite-set datum in item 8. The residual packet $\Pi_0'$, the represented target local
conditions, and the coefficient-prime conditions remain compulsory. On every geometric
route, all clauses belonging to each face or shadow actually used retain their literal force.

Here an **applicable Book 176 one-prime conclusion** means literal Theorem 7.1 on a retained nontrivial character fiber of its $q_w\equiv1\pmod q$ scalar-twist family, or the trivial-character conductor-one variant stated immediately after that theorem. At a generic unramified-to-special place $q_w\not\equiv\pm1\pmod q$, or for the $q_w\equiv-1\pmod q$ full block, it instead means the separately conditional reduced-image argument in Book 176, Section 7.1, after every named hypothesis has been independently proved for that exact represented problem. In particular, the places above $v_0$ are in the generic regime by (3.7); they are not literal instances of Book 176, Theorem 7.1.

1. The global fixed-determinant deformation problem is represented, with no local equation omitted and with coefficient characteristic $q\geq7$.
2. At every $w\mid q$, the local field is in the unramified finite-flat range, all Artinian quotients have compatible finite-flat models of weights $\{0,1\}$, and the residual Schur hypotheses hold after coefficient extension.
3. At every $w\nmid q$, the Tate-module point lies on a named represented component with its determinant, conductor, ordered line or characters, sign, and monodromy recorded. Passing between this book's arithmetic-Frobenius convention and Book 176's geometric-Frobenius convention inverts the Frobenius roots and the monodromy relation together.
4. On every one-prime face actually used, $({\rm AUT}_w)$ holds: the residual dihedral eigensystem occurs in the exact nonzero non-Eisenstein compact automorphic localization, with the actual primary and companion systems, local labels, stabilizer data, and Galois-attachment range from which the named components are reached.
5. Whenever the comparison uses constant-coefficient saturation or Book 139's corrected filtration, the full family $({\rm AIH}_{\mathscr F})$ holds for every vertex, edge, permutation, and adjoint-companion curve in the actual flag diagram, with every spectator tuple and auxiliary shadow. The required neat or prime-to-$q$ stabilizer descent, saturation, component-group control, and independent normalized-branch Smith correction are also supplied. Every lowering step additionally satisfies all six conditions of Book 176, Section 4.4: an adjoint-stable non-Eisenstein block with perfect adjoint pairing, zero residual monodromy on that full block, no residual component or branch torsion, the exact two-branch normalization middle term, and a nonzero block with no scalar, self-twist, or vexing identification merging it with an Eisenstein or different adjoint block.
6. On every actual primary and companion shadow, use the proved actual-row theorem $({\rm TPE}_w)$; the separate $({\rm TIC}_w)$ and $({\rm TIH}_{\mathscr F})$ hypotheses hold. In the nonbanal $q_w\equiv-1\pmod q$ range, Book 174's quotient-new injection (5.0d) and primitive filtered-cofiber comparison (6.0d) are retained as separate inputs. The type lattices are finite free and perfectly paired at base, mixed, and Taylor--Wiles levels; every one-prime degeneracy and type map and its two-term complex has the asserted saturation, exactness, and coefficient-algebra Tor control. No several-place mixed exactness is included in this clause; that is part of the route in item 8. The package also includes $({\rm PRI}_{\rm type})$ whenever an extreme coefficient-one residue is used, and $({\rm NU}_{\rm type})$ together with Book 140's enhanced flagged PEL node-groupoid classification (5.9a) whenever a carrier is switched to the definite side. Constant generic support and common-kernel equality are then conclusions of Book 140 from the corrected filtration and Book 125; under the preceding $({\rm AIH}_{\mathscr F})$, the displayed type and primitive-residue inputs, and Book 125 routing, the typed analogues are conclusions of Book 174.
7. Every one-prime face has the five-clause boundary-and-depth datum $({\rm SUP}_w)$, including the unresolved relative Cartier-switch transversality $({\rm BCD}_w)$ of Book 174, (8.2f), and Book 141's split-regular detector input in the marked finite shadows, together with the finite-carrier reciprocity package $({\rm REC}_w)$. Thus the faithful Hecke order is generated only by verified trace and structural operators, is torsion-free with reduced generic fiber, and carries a genuine two-dimensional Galois representation of determinant $\chi_q$ whose Artinian specializations satisfy the same finite-flat and prime-to-$q$ local component quotients as $r_{A,q}$.
8. One exact Book 176 route is exhibited.  The scope-minimal finite-set option is the direct
   Ihara-avoidance package $({\rm IAV}_{P_{\mathrm{act}}})$ of Book 176, Section 1.5, for
   $r_{A,q}$ and the automorphic lift attached to $\Pi_0'$, after any further solvable totally
   real base change used by that package.  The set is the whole $P_{\mathrm{act}}$, including
   every place above the distinguished dyadic place; no one-place subset may be substituted.
   This includes the paired desired/avoidance local rings, the proof that their patched
   specializations are component-bijective, synchronized automorphic Taylor--Wiles systems
   with their common mod-$\varpi$ module and proved avoidance full support, exact acting-image
   recovery, and the permitted stopping field of Section 8.6. Book 176, Theorem 1.1H and
   Corollary 1.1I supply support transfer.
   Alternatively, $P_{\mathrm{act}}$ is a singleton and the applicable one-prime conclusion
   above holds; or an ordered finite chain is given and every applicable one-prime hypothesis
   is verified anew on each intermediate carrier, with all previously changed places retained
   in the actual spectator datum; or the simultaneous route satisfies
   $({\rm FACE}_{P_{\mathrm{act}}})$, $({\rm CUBE}_{P_{\mathrm{act}}})$,
   $({\rm MIX}_{P_{\mathrm{act}}})$, $({\rm PROD}_{P_{\mathrm{act}}})$,
   $({\rm JSUP}_{P_{\mathrm{act}}})$, $({\rm AUG}_{P_{\mathrm{act}}})$, and
   $({\rm REC}_{P_{\mathrm{act}}})$ of Book 176, Theorem 9.1.
   For the one already named Tate-module point, the final alternative is Book 176, Theorem 9.2:
   construct one actual final component-routed cube and adjoint, form its canonical primary
   carrier $Q_{P_{\mathrm{act}}}^{\rm tf}$ with perfectly paired adjoint
   $K_{P_{\mathrm{act}}}^-$, verify on the primary carrier every simultaneous generic local
   and structural branch label, invoke Book 170 only
   afterward to obtain $({\rm REC}_{P_{\mathrm{act}},x_A})$, and prove that the one global
   component $\Xi_{x_A}$ through the Tate point lies in its support.  This pointed route does
   not assume $({\rm MIX})$ or $({\rm PROD})$ unless they are used to construct the final cube
   or to prove that component occurrence.
9. Every scalar step uses the effective strict global ray quotient and determinant-square twist identities $({\rm RAY}_w)$ constructed in Book 174, with every added conductor place retained in the spectator datum. Whenever an auxiliary patch is descended, the coherent auxiliary datum $({\rm AUX}_Q)$ supplies exact augmentation for represented rings, modules, pairings, complexes, and deformation actions. Book 175's full patched and finite $R=T$ theorem, and hence its proof of auxiliary acting-image injectivity, may be cited only when clean unpadded shadows with exactly the balanced number of ordered killing primes (the $q$ in Book 175, (5.6b), not the auxiliary rational prime of this book) exist at every depth; diagonal coherence does not construct those shadows. Exact auxiliary acting images otherwise require an independently proved full base $R=T$ theorem and are not an input to the direct reduced finite-level comparison. In the simultaneous route the stronger datum $({\rm AUG}_{P_{\mathrm{act}}})$ uses Book 176, Proposition 8.3's joint ray quotient and includes order-independent fixed-prime and Taylor--Wiles augmentation; the ray clause is vacuous when no scalar place occurs.
   In the pointed route, any such specialization is performed on the complete cube first and
   the torsion-free top carrier is defined anew afterward; its formation is not commuted
   through a nonflat character or diamond quotient.

This definition is a verification record, not a theorem. In particular, a “finite clean chain” is acceptable only if every stage is an applicable one-prime conclusion in the sense above, with all previously changed places retained in its permitted spectator datum. Book 176's statement does not become a finite-set theorem by induction on notation.

### 8.4 Component support

The support clause is logically independent of local representability and of the existence of a raised form at each separate prime. For the simultaneous route, let $R_q^{P_{\mathrm{act}}}$ be the represented global deformation ring for the product local condition and let $\mathbb T_q^{P_{\mathrm{act}}}$ be the faithful localized Hecke order. Finite-set reciprocity gives a surjection only after its integral hypotheses have been proved:

$$
R_q^{P_{\mathrm{act}}}\twoheadrightarrow\mathbb T_q^{P_{\mathrm{act}}}. \tag{8.4}
$$

The Tate module gives a point

$$
x_A:R_q^{P_{\mathrm{act}}}\longrightarrow\mathcal O_{M,\mathfrak q}. \tag{8.5}
$$

To prove automorphy, one must show that $x_A$ factors through the Hecke side. A support argument must show that the patched module meets the generic point of the product component containing $x_A$, not merely that its projections meet every one-place component. A determinant argument must compare the complete Fitting data, including cross-Tor and branch-correction terms.

For two active places $v,w$, separate saturation does not determine

$$
\operatorname{im}(d_v)\cap\operatorname{im}(d_w) \tag{8.6}
$$

inside the mixed-level module. Equivalently, filtering the two-place total degeneracy complex leaves a mixed obstruction in the quotient-new module at the second place. Vanishing of that obstruction and joint support on the product component are conclusions that require a genuine mixed theorem. They may not be inserted into the input under the name “clean semistability.”

The direct $({\rm IAV}_{P_{\mathrm{act}}})$ route does not use this incidence module. It
patches the complete desired local problem and the auxiliary Ihara-avoidance problem in
parallel. Full support on the irreducible avoidance side passes through their identified
special fibers and the desired-side component bijection by Book 176, Theorem 1.1H. This
proves that the point (8.5) lies on automorphic support without a separate product-component
occurrence theorem. The arithmetic input is the whole paired local-ring and synchronized
patched-module construction, including exact recovery; residual automorphy of $\Pi_0'$ and
minimal $R=T$ alone do not supply it.

An ordered one-prime chain uses successive one-place deformation rings and faithful orders instead. At each stage its characteristic-zero point must factor through that stage's reduced faithful Hecke image. Such a chain neither proves nor needs joint support for the simultaneous product ring; conversely, separate one-place factorizations on the original carrier do not constitute a validated chain.

For the simultaneous **pointed** route, Book 176, Proposition 8.2B starts with the one actual
final cube and forms

$$
M_{P_{\mathrm{act}},x_A}
=Q_{P_{\mathrm{act}}}^{\rm tf},
\tag{8.6a}
$$

This is finite free over the coefficient DVR even if the integral mixed obstruction is
nonzero; it has the perfectly paired adjoint carrier $K_{P_{\mathrm{act}}}^-$, and its generic
packet factorization contains the global multiplicity module only once. The required support
statement is then the genuinely joint but pointed assertion

$$
\mathfrak p_{\Xi_{x_A}}
\in\operatorname{Supp}_{R_q^{P_{\mathrm{act}}}}
(M_{P_{\mathrm{act}},x_A}),
\tag{8.6b}
$$

where $\Xi_{x_A}$ is one global irreducible component through (8.5), carrying the complete
tuple (7.9).  This is weaker than support on every component but stronger than all separate
one-place projections.  Once (8.6a), all simultaneous generic branch labels, carrier-specific
finite-set reciprocity, and (8.6b) have been proved, the carrier annihilator lies in
$\mathfrak p_{\Xi_{x_A}}\subseteq\ker x_A$, so (8.5) factors through the faithful Hecke
image.  Mixed exactness and iterated product residue are needed only if they are the chosen
route to constructing the actual final cube or proving (8.6b); they are not used again by this
pointed annihilator argument.

### 8.5 The conditional lifting step

Assume the complete cleanability record of Sections 8.2--8.3 and the route-appropriate support and factorization described in Section 8.4. The applicable comparison from Book 176 then makes the Tate-module point automorphic: by $({\rm IAV}_{P_{\mathrm{act}}})$, by the one-prime conclusion, successively along the validated chain, by conditional Theorem 9.1 in the all-point simultaneous case, or by Theorem 9.2 and (8.6a)--(8.6b) in the pointed simultaneous case. There are a cuspidal parallel-weight-two representation $\Pi_A$ over $F'$, a coefficient place $\widetilde{\mathfrak q}\mid q$, and a finite $q$-adic field $C_q$ receiving both coefficient completions such that

$$
V_{\mathfrak q}(A)\otimes_{M_{\mathfrak q}}C_q
\simeq
\rho_{\Pi_A,\widetilde{\mathfrak q}}
\otimes_{E_{\Pi_A,\widetilde{\mathfrak q}}}C_q. \tag{8.7}
$$

The proof mechanism is exact. In the direct case, paired patching proves full support for the
desired finite-set deformation problem and hence puts (8.5) on its automorphic locus. In the
all-point simultaneous case, the reduced comparison makes (8.5) factor through
$\mathbb T_q^{P_{\mathrm{act}}}$. In the pointed simultaneous case, (8.6b) puts the carrier
annihilator inside $\ker x_A$ and gives the same factorization without asserting mixed
exactness or a reduced ring comparison. In a chain the analogous factorization is made
successively through each one-place faithful order. A full scheme-theoretic $R=T$ or
reducedness of the deformation source is not required. Specializing the Hecke-valued Galois
representation gives the same traces and determinants as $r_{A,q}$ at good Frobenius
elements. Chebotarev and Brauer--Nesbitt identify the rational representations. Absolute
irreducibility of the common residual member makes their stable lattices homothetic, so the
selected integral local conditions agree.

Equation (8.7) is not a consequence of (8.3). The former is the modularity-lifting conclusion; the latter is only residual automorphy.

### 8.6 Stopping over a further field

If the cleanability record is verified only after a further finite totally real extension $E/F'$, the safest residual potential-modularity endpoint is $E$. Require $E$ to preserve the two residual images and the coefficient-prime local conditions, recompute the actual active set over $E$, and reconstruct the dihedral residual packet over $KE/E$ as in Section 3.3. Apply lifting over $E$, base change $A$ to $E$, and perform Chapter 9 there. In that case every occurrence of $F'$, $A$, and $P_{\mathrm{act}}$ in Chapter 9 is read after this base change.

No descent back to $F'$ is needed for residual potential modularity. A descent of the rational automorphic packet would require an exhibited cyclic solvable tower, descent-admissibility at every step, stepwise cuspidality, compatible local parameters and central characters, an extending irreducible Galois representation, and the quotient-character corrections of Book 109. This book neither assumes those facts nor claims that descent. In particular, there is never a descent from the final potential-modularity field to the original field $F$.

## 9. Moving to the target coefficient prime

Once (8.7) is available, the two coefficient primes communicate through the algebraic Frobenius endomorphisms of $A$ and the rational Galois realizations of the same automorphic packet. This is a comparison of compatible polynomials, not a tensor product of local coefficient fields.

### 9.1 Common algebraic Frobenius polynomials

Let $v$ be a place of good reduction for $A$ whose residue characteristic differs from $\ell q$. Frobenius commutes with the $\mathcal O_M$-action. On the selected rank-two $M$-factor it has one reduced characteristic polynomial

$$
P_{A,v}(X)=X^2-a_v(A)X+q_v\in M[X]. \tag{9.1}
$$

For every finite prime $\nu$ of $M$ away from the residue characteristic of $v$, the image of (9.1) in $M_\nu[X]$ is the arithmetic-Frobenius polynomial on $V_\nu(A)$. The determinant is $q_v$ by the polarization and the covariant convention. This remains true when Frobenius is scalar.

Equation (8.7) shows, after embedding the two number fields into a common algebraic field, that

$$
P_{A,v}(X)=X^2-a_v(\Pi_A)X+q_v \tag{9.2}
$$

for almost all $v$. Equality in one $q$-adic completion is equality of the underlying algebraic numbers because the coefficient embedding is injective.

### 9.2 The selected special place supplies a curve carrier

The curve carrier is a theorem here, not an additional admissibility clause. If the lifting theorem first produces a packet on the totally definite quaternion algebra, Book 104, Theorem 9.1, transfers it to the split group with the same good polynomials, central character, and selected local factors; denote that split packet by $\Pi_A$. By (6.2a), the working field has even absolute degree. The clean lifting record retains at every place above $v_0$ the selected conductor-one special component and its nonzero monodromy. In particular, choose one such place $w_0$. The local factor $(\Pi_A)_{w_0}$ is the selected unramified Steinberg twist recorded by the lifting theorem, so $w_0$ is eligible for inverse Jacquet--Langlands.

Fix a real place $\tau_0$ of $F'$ and take the odd nonempty set $W=\{w_0\}$. Book 104, Theorem 9.2, constructs the quaternion algebra $B/F'$ ramified at every real place except $\tau_0$ and at $w_0$, together with the unique noncharacter packet

$$
\Pi_B=\operatorname{JL}_B^{-1}(\Pi_A).
$$

The theorem preserves the central character and every good Hecke polynomial. The parity calculation is explicit: $B$ is ramified at $[F':\mathbf Q]-1+1=[F':\mathbf Q]$ places, an even number. Since it is ramified at a finite place and at all but one real place, it is a division algebra, so its Shimura curve is compact.

Book 127, Theorem 8.1, now places the complete finite packet block of $\Pi_B$ in constant-coefficient $H^1$ of that compact curve and extracts a rank-two weakly compatible family. The construction uses the actual reflex-field identification through $\tau_0$, the full component-routing orbit, and the basic-group determinant datum. It does not use a modular curve or a Shimura surface, and it does not infer a carrier from equality of almost-all eigenvalues.

At a place $\widetilde\lambda\mid\ell$, denote the covariant member, labeled through this transfer, by

$$
\rho_{\Pi_A,\widetilde\lambda}:
G_{F'}\longrightarrow
\operatorname{GL}_2(E_{\Pi_A,\widetilde\lambda}) \tag{9.3}
$$

with determinant $\chi_\ell$ in the present central-character normalization and good arithmetic-Frobenius polynomial (9.2). A stable lattice exists. No identification with the canonical cohomological lattice is assumed.

Thus the selected special place created before specialization closes the coefficient-changing carrier arrow after auxiliary-prime lifting. If one deleted that place, or if a purported lifting theorem forgot its special local factor, Books 104 and 127 would no longer apply. Under the ledger used here, however, there is no remaining curve-carrier hypothesis.

### 9.3 Chebotarev comparison

Choose a finite extension $C_\ell/\mathbf Q_\ell$ receiving $M_\lambda$ and $E_{\Pi_A,\widetilde\lambda}$. Equations (9.1)--(9.3) give equality of characteristic polynomials at a density-one set of places. Chebotarev density and Brauer--Nesbitt therefore give

$$
\left(V_\lambda(A)\otimes_{M_\lambda}C_\ell\right)^{\mathrm{ss}}
\simeq
\rho_{\Pi_A,\widetilde\lambda}
\otimes_{E_{\Pi_A,\widetilde\lambda}}C_\ell. \tag{9.4}
$$

The left side is irreducible. Indeed, a characteristic-zero invariant line would meet a stable lattice in a saturated rank-one submodule and reduce to a line in $A[\lambda]$, contradicting (7.2) and preservation of absolute irreducibility. Hence the semisimplification sign on the left can be removed, and (9.4) also makes the right side irreducible.

This argument uses Corollary 11.2 of the companion Chebotarev development, Book 142, which the critical proof spine declares globally upstream. Book 127 supplies the family and its Frobenius polynomials; it does not prove density. No theorem from Books 178--180, and in particular no compatible-system assembly or Brauer descent, is used.

### 9.4 The exact residual member

Let $\mathcal O_C$ be the valuation ring of $C_\ell$, with residue field $\kappa$. Transport stable lattices through (9.4). The following elementary lemma removes a possible extension ambiguity.

**Lemma 9.1.** Let an irreducible characteristic-zero representation have one stable lattice with absolutely irreducible reduction. Then any two stable lattices have isomorphic reductions.

**Proof.** Scale an intertwiner so that one lattice $L_1$ lies in the other $L_2$ but not in the maximal-ideal multiple of $L_2$. The image of $L_1$ in the residual space of $L_2$ is nonzero and Galois stable. Absolute irreducibility makes it the entire space. Nakayama's lemma gives $L_1=L_2$ after the scaling. $\square$

Reducing (9.4) and using (7.2) therefore gives the exact comparison

$$
\bar\rho|_{G_{F'}}\otimes_k\kappa
\simeq
A[\lambda]\otimes_{k_\lambda}\kappa
\simeq
\bar\rho_{\Pi_A,\widetilde\lambda}
\otimes_{k_{\widetilde\lambda}}\kappa. \tag{9.5}
$$

**Corollary 9.2 (nonzero upper target block).** Write $\varpi$ for a uniformizer of
$\mathcal O_C$. Retain the exact packet block used in
Section 9.2, before any attempt to remove the specialization-dependent bad places, and let
$L_{\Pi_A}$ be the intersection of that rational packet block with the integral curve
cohomology lattice after the declared coefficient extension. Let $\mathfrak m_{\ell,A}$ be
the maximal ideal in this carrier's commuting faithful Hecke image order obtained by reducing
the packet character. Then

$$
(L_{\Pi_A})_{\mathfrak m_{\ell,A}}/\varpi\ne0,                 \tag{9.6}
$$

and hence the ambient integral curve-cohomology localization at
$\mathfrak m_{\ell,A}$ is nonzero modulo $\varpi$.  Moreover, the associated rational
rank-two Galois factor admits a stable lattice whose residual
representation is (9.5).  No integral Morita extraction of that rank-two lattice from
$L_{\Pi_A}$ is asserted.

**Proof.** The intersection of a rational subspace with a finite free DVR lattice is
saturated. Choose a nonzero simultaneous packet eigenvector for the selected character and
scale it until it is primitive in that
intersection. Saturation makes its reduction inject into the ambient cohomology reduction.
It is nonzero and is killed by the reduction of every Hecke operator
minus its packet eigenvalue, so it survives in the localization at
$\mathfrak m_{\ell,A}$. Choose any stable lattice in the associated rational rank-two curve
factor.  It and the lattice transported from $T_\lambda(A)$ have the same irreducible
characteristic-zero representation by (9.4).  Lemma 9.1 and absolute irreducibility of (7.2)
identify their reductions, giving (9.5) for the associated factor. $\square$

This is an **upper-level** occurrence theorem. It is formal from the already automorphic
packet, its integral packet lattice, and the exact stable-lattice comparison. It does not say
that $\mathfrak m_{\ell,A}$ occurs after removing any extra special places of $A$, and it does
not verify the saturation, component, branch, or auxiliary-level hypotheses of the minimal
Book 173 localization. Those require an actual lowering path; equality of good Frobenius
polynomials alone would not even give (9.6) without the integral packet lattice.
Moreover, the particular compact carrier of Section 9.2 is ramified at $w_0$.  Book 140 cannot
be applied at $w_0$ on that carrier, because its changing place must be split in the
quaternion algebra.  Any later argument which must remove $w_0$ therefore needs a separate
path-compatible carrier, together with its own primitive packet lattice; Corollary 9.2 does
not supply that carrier switch.

This is residual modularity of the target. If $\bar\rho$ were reducible, good Frobenius polynomials would determine only a semisimplification and different stable lattices could reduce to different nonsplit extensions. That edge case is why absolute irreducibility appears at the beginning of the construction.

## 10. The conditional potential-modularity theorem

The preceding chapters separate construction from theorem use. This chapter packages their exact common domain and states only the residual conclusion that the argument proves.

### 10.1 Lifting-admissible paired specialization

A **lifting-admissible paired specialization** for $\bar\rho$ consists of the following data.

1. The target datum of Section 2.1, including absolute irreducibility after restriction to $F(\zeta_\ell)$, the adjoint-invariant vanishing required by the chosen lifting theorem, cyclotomic determinant, and the exact finite-flat models at every $v\mid\ell$.
2. The auxiliary prime, quadratic extension, and algebraic Hecke character of Chapter 3, with the induced residual representation absolutely irreducible, odd, cyclotomic-determinant, and cuspidally automorphic at the selected localization after every field extension actually used.
3. One fine, smooth, geometrically connected paired-frame moduli space as in Chapter 4, with both pairings, determinant identifications, and coefficient actions fixed on the same connected component.
4. One simultaneous system of local opens as in Chapter 5, witnessed at every place by a single local point of that same moduli problem.
5. A Moret--Bailly specialization $F'/F$ satisfying the field profile of Section 6.4 and a specialized abelian variety $A/F'$ satisfying Chapter 7.
6. A post-specialization cleanability record for the actual set $P_{\mathrm{act}}$, clause by clause as in Section 8.3, together with its direct $({\rm IAV}_{P_{\mathrm{act}}})$, exact one-prime, validated-chain, or simultaneous Book 176 lifting route.

The definition deliberately does not say merely that the two residual representations are ``of the right type.'' It records the integral local models, the selected automorphic localization, the actual component containing the characteristic-zero point, the primary and companion lattices, support, faithful orders, and augmentation maps needed by the lifting theorem. A curve realization is not an item in the definition: Section 9.2 proves it from the even-degree field and the retained selected special place.

### 10.2 Conditional residual potential modularity

**Theorem 10.1 (conditional residual potential modularity in the FLT range).** Let $F$ be totally real, let $\ell\ge 7$ be unramified in $F$, and let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{10.1}
$$

be continuous, odd, absolutely irreducible, and of cyclotomic determinant. Assume $\bar\rho|_{G_{F(\zeta_\ell)}}$ is absolutely irreducible, the precise adjoint-invariant hypothesis of the selected Book 176 lifting route holds, and the restrictions at places above $\ell$ are supplied by the finite-flat paired group schemes of Section 2.3. If $\bar\rho$ admits a lifting-admissible paired specialization, then there are

- a finite totally real extension $F^{\mathrm{pm}}/F$;
- a cuspidal parallel-weight-two automorphic representation $\Pi$ over $F^{\mathrm{pm}}$ in Book 127's rational curve-realizable range;
- a place $\widetilde\lambda\mid\ell$ of its coefficient field; and
- a finite residue-field extension $\kappa/k$

such that

$$
\bar\rho|_{G_{F^{\mathrm{pm}}}}\otimes_k\kappa
\simeq
\bar\rho_{\Pi,\widetilde\lambda}\otimes_{k_{\widetilde\lambda}}\kappa.
\tag{10.2}
$$

The determinant in (10.2) is the mod-$\ell$ cyclotomic character in the covariant arithmetic-Frobenius normalization.

**Proof.** Chapters 3--6 construct $F'$ and $A/F'$ with the two framed torsion identifications. Section 7.1 identifies $A[\mathfrak q]$ with the induced residual seed, while Sections 3.3 and 8.2 and the cleanability record place that seed in the exact selected automorphic localization. The post-specialization record applies the appropriate Book 176 comparison—direct paired finite-set patching, one-prime, successively along the validated chain, all-point finite-set, or pointed finite-set—to identify the $q$-adic Tate factor of $A$ with a cuspidal packet $\Pi_A$ on the component containing that factor. If this requires a further field $E$, Section 8.6 repeats the residual seed there and sets $F^{\mathrm{pm}}=E$; otherwise set $F^{\mathrm{pm}}=F'$.

Section 9.2 uses the retained special place and even field degree to construct the compact one-split packet by Book 104 and then applies Book 127 to obtain its $\ell$-adic member. Equality with the $\ell$-adic Tate factor follows from the common Frobenius polynomials and Chebotarev, as in (9.4). The stable-lattice argument of Lemma 9.1 and the target frame then give (10.2). $\square$

This theorem does **not** assert that a chosen characteristic-zero lift of $\bar\rho$ is automorphic. Book 127 constructs a weakly compatible packet family over the potential-modularity field, but this theorem uses only its $q$- and $\ell$-adic members and does not descend that family to $F$. It does not descend $\Pi$ to $F$, and it does not even descend it from a further field $E$ to the first Moret--Bailly field $F'$.

### 10.3 Exact field control

The unconditional field information furnished by the construction is:

$$
F'/F\text{ is finite and totally real},\qquad
\text{every }v\in S\text{ splits completely in }F',\qquad
F'\cap D=F,
\tag{10.3}
$$

for the prescribed finite local set $S$ and finite Galois avoidance field $D/F$ in the Moret--Bailly datum. Taking $D$ to contain the target and seed residual cutout fields proves the image equalities (6.4). Enlarging $S$ preserves further exact coefficient-prime local models when simultaneous local witnesses are supplied.

Neither Book 154 nor this construction makes $F'/F$ Galois, solvable, or cyclic. Any further field $E$ used in Section 8.6 has only the properties explicitly imposed there. Consequently none of these fields supports automorphic descent merely by how it was constructed.

### 10.4 Why the geometric alternatives remain conditional

For the FLT application, Book 176, Theorem 1.1H and Corollary 1.1I prove
$({\rm CIAV}_{P_{\mathrm{act}}})$ by the direct source-patching route. This construction
handles every place above $v_0$ at once and does not consume the abelian-Ihara, type-Ihara,
mixed-cube, product-residue, or pointed-occurrence gates below.

On the geometric level-change routes, the first failure in the declared proof dependencies
occurs inside the cleanability clause. Wherever the actual comparison invokes Book 139's
corrected constant-coefficient filtration, Book 176 requires the finite family of **abelian
Ihara conditions**

$$
({\rm AIH}_{\mathscr F}):\qquad
\left(H^1_{\mathrm{nc}}(\Gamma_D^w,k)^{\Delta_D}\right)_{\mathfrak m_D}=0
\quad\left(D\in\mathscr F_w(Q)\right).
\tag{10.4}
$$

Here $D$ runs through every constant-coefficient vertex, edge, permutation, and adjoint-companion curve in the actual flag diagram, with its actual spectator tuple, auxiliary shadow, routing quotient, and maximal ideal. Book 139 identifies each displayed group as the remaining localized noncongruence-character obstruction; it does not prove its vanishing from the geometric or residual hypotheses. Book 176 retains the full family wherever it uses constant saturation or the corrected component filtration. No prior accepted dependency of this book proves (10.4). Thus the auxiliary residual automorphy of Section 7.1 cannot presently be propagated through even the relevant one-prime nonminimal comparison when that comparison invokes those rows without adding an unproved hypothesis.

In Book 139's exact notation, (10.4) is the routed
$({\rm AC}^{\rm loc}_q)_{\mathscr R}$ gate, equivalently the displayed finite family of
$({\rm AIH}_{\mathscr F})$ vanishings on the actual routed rows. Kernel invariance across
spectator levels is not a substitute for this theorem.

Localized Ihara is the first gap in those constant rows, but it is not the whole one-prime ledger. On every actual shadow the type rows use the proved $({\rm TPE}_w)$ and separately require $({\rm TIC}_w)$ and $({\rm TIH}_{\mathscr F})$; the pointwise comparison requires $({\rm AUT}_w)$, $({\rm SUP}_w)$, and $({\rm REC}_w)$; a scalar step uses Book 174's constructed $({\rm RAY}_w)$ with its conductor spectators; and auxiliary descent adds the coherent datum $({\rm AUX}_Q)$. An extreme residue or switched carrier also adds the applicable $({\rm PRI}_{\rm type})$, $({\rm NU}_{\rm type})$, and Book 140 node-uniformization hypothesis. Book 140 proves the constant generic-support and common-kernel conclusions, and Book 174 proves their typed counterparts under the preceding type inputs; they are not extra hypotheses. Books 174--175 prove the named one-prime component-support and pointwise modularity consequences only under their stated integral comparison package; the existence of the Hilbert--Blumenthal point does not verify that package. A reduced faithful Hecke image and reduced comparison suffice for characteristic-zero pointwise modularity; reducedness of the deformation source is needed only for full scheme-theoretic $R=T$. This is **automorphic carrier support**, not the compact curve-carrier existence proved in Section 9.2.

There is a second, logically later obstruction on those routes. Book 176's literal Theorem 7.1 treats the $q_w\equiv1\pmod q$ scalar-twist family, whose nontrivial faces have conductor two and whose trivial augmentation face is conductor-one line-special. Its generic conductor-one and $q_w\equiv-1\pmod q$ full-block conclusions are only the separately conditional reduced-image argument stated after that theorem. In the split construction every place above $v_0$ is active and generic, so $\#P_{\mathrm{act}}\ge [F':F]$ even before the new bad places $P_A$ are added. Book 176 proves no unconditional simultaneous theorem: its conditional Theorem 9.1 requires the full $({\rm FACE})$, $({\rm CUBE})$, $({\rm MIX})$, $({\rm PROD})$, $({\rm JSUP})$, $({\rm AUG})$, and $({\rm REC})$ packages. One-place injectivity does not imply the mixed vanishing

$$
\operatorname{Ob}_{v,w}
=\ker\!\left(
N_{v\mid0,k}^{\oplus2}\longrightarrow N_{v\mid1,k}
\right)=0,
\tag{10.5}
$$

nor does separate support on the $v$- and $w$-components imply support on their product component. Exact primary and companion augmentation must also be proved simultaneously. No accepted prior dependency supplies those finite-set assertions.

Book 176 now identifies the integral content of (10.5) exactly at the final coefficient-DVR
level: it is equivalent to torsion-freeness of the top joint-new quotient, or saturation of
the sum of the two top old images.  Its split-edge DVR countermodel shows that all one-place
images can be primitive and the generic cube can be exact while this sum is not primitive.
For the product-residue route, distinct arithmetic fibers have empty intersection; the exact
missing geometry is therefore the parity-indexed iterated-switch Beck--Chevalley theorem,
including integral homotopies, Néron and branch-Smith terms, and three-face coherence.  Generic
packet-label commutation does not prove it.

Later diagnostic manuscripts and retired unitary-surface proposals are not dependencies and cannot be used to discharge these obligations. On the geometric routes, the exact first constant-row gap is (10.4). After it, the all-point route remains obstructed by construction of one global cube, (10.5) and all higher mixed exactness, the iterated-switch product-residue comparison, joint support, coherent joint ring--complex--module--action--pairing augmentation, and finite-set reciprocity for the actual multi-place set $P_{\mathrm{act}}$, unless a validated one-prime chain is exhibited. Fixed-prime faithful-order augmentation is formal once a strict product twist exists, while auxiliary acting-image injectivity follows only after full base $R=T$.

For the one Tate-module point used here, Book 176, Theorem 9.2 gives a shorter but still
unproved route.  After constructing the actual final cube, one forms the canonical carrier
(8.6a), verifies every simultaneous generic branch and structural label on that carrier,
applies Book 170 only then, and proves the pointed occurrence (8.6b).  Neither (10.5) nor
product residue is a formal premise of its annihilator step.  No accepted prior dependency,
however, proves (8.6b) for the specialization-dependent tuple $P_{\mathrm{act}}$, and separate
one-place support cannot do so.  This pointed joint-component occurrence, together with the
carrier-specific branch verification preceding reciprocity, is the first exact several-place
theorem on the shorter route.

There is no third curve-carrier gap in the stated range. The selected special place survives in the output of the clean lifting theorem, and the even-degree choice (6.2a) lets Book 104, Theorem 9.2, put the split packet on a compact one-split inner form. Book 127 then constructs its rank-two family. Older proposals to obtain the same family from unitary Shimura-surface $H^2$, or to infer an inverse transfer merely from matching spherical eigenvalues, are obsolete and are not used.

## 11. Failure tests and boundary cases

These tests are part of the theorem's usable statement. Each detects a tempting but invalid shortcut.

### 11.1 Residual automorphy is localization-sensitive

A global isomorphism

$$
A[\mathfrak q]\simeq\bar r_{\mathrm{dih}}
$$

does not alone give the residual automorphic source required by Book 176. The inducing character, determinant, cuspidality, local type, connected-component label, Hecke maximal ideal, and primary/companion coefficient systems must all match after restriction to the actual field. Changing the field can split the quadratic extension or destroy residual irreducibility; Chapter 3 prevents both by disjointness and then reconstructs the induced packet over the new field.

### 11.2 Smoothness is not component support

A smooth local deformation ring says that a chosen point deforms unobstructedly. It does not prove that the localized automorphic module meets that component. Likewise, a geometrically connected global moduli space permits simultaneous approximation but says nothing about the support of a Shimura-curve Hecke module. These are different spaces and different assertions.

### 11.3 Semistability is not cleanability

Semistability describes the local geometry of $A$. Cleanability additionally requires an allowed integral deformation component, a selected residual automorphic source, Ihara injectivity and saturation, primary/companion type occurrence, faithful-order comparison, and exact augmentation. A semistable bad prime at which Frobenius is scalar or $q_v\equiv\pm1\pmod q$ must use the enhanced chart and its proved integral comparison; deleting the prime from the ledger is not a remedy.

### 11.4 Separate local points do not define one open condition

At a place $v$, a target frame witnessed by one local abelian variety and an auxiliary frame witnessed by another need not lie on the same local point of the paired moduli space. Their neighborhoods therefore cannot simply be intersected. Section 5.1 requires a single simultaneous witness before any Moret--Bailly open is declared.

### 11.5 Scalar extension has a direction

If a frame is written only after extending the residue field, the represented group scheme is

$$
\mathcal G\otimes_k k',
$$

not a restriction of scalars from $k'$ to $k$. Reversing this variance changes ranks and pairings. All comparisons in (4.1), (7.2), and (7.3) are made only after a named common scalar extension.

### 11.6 Pairings fix determinants and signs

The Weil pairing is alternating, while the induced dihedral pairing carries the quadratic sign in (3.3). The twist in Section 4.2 is chosen before the moduli problem so that the two similitude characters agree with the polarization. Ignoring this sign can produce a residual isomorphism with determinant $\epsilon_{K/F}\bar\chi_q$ instead of $\bar\chi_q$.

### 11.7 Frobenius conventions cannot be mixed

The geometric construction uses covariant Tate modules and arithmetic Frobenius. Book 127's cohomological representation is dualized once. With these choices the good polynomial is $X^2-a_vX+q_v$. Book 176 states its good polynomial using geometric Frobenius and writes the enhanced special matrix using arithmetic Frobenius; at that interface the roots and the relation $FNF^{-1}=q_v^{-1}N$ are inverted together. A second dual or an isolated Frobenius inversion would invalidate (9.4) or select the wrong special line.

### 11.8 A finite clean chain is a theorem, not notation

Writing the active places as $v_1,\ldots,v_r$ does not allow a Book 176 one-prime conclusion to be applied $r$ times. After the first change, the automorphic lattice, companion lattice, faithful Hecke order, and spectator components have changed. The next step is valid only after every hypothesis of the applicable scalar or generic/vexing route has been reverified on the intermediate carrier. Book 176 supplies an all-point simultaneous finite-set conclusion only under every hypothesis of its conditional Theorem 9.1. Its pointed Theorem 9.2 is not an iteration shortcut: it requires one actual final cube, simultaneous branch data and reciprocity on its torsion-free top carrier, and support on the one global component through the named point.

The direct $({\rm IAV}_{P_{\mathrm{act}}})$ theorem is the separate finite-set alternative:
it patches the whole active set at once and therefore does not assert that a sequential chain
is automatic. Until that paired patching theorem is constructed, complete splitting of
$v_0$ leaves an unavoidable multi-place lifting gap.

### 11.9 Chebotarev gives semisimple comparison first

Equality of almost-all Frobenius polynomials yields (9.4), a characteristic-zero semisimple comparison. Irreducibility removes that semisimplification. Absolute residual irreducibility then makes the reduction independent of the stable lattice. Omitting either step would prove at most equality of residual semisimplifications.

### 11.10 Potential automorphy is not descent

The conclusion lives over $F^{\mathrm{pm}}$. Descent would need the exact Book 109 cyclic-tower hypotheses and the extending Galois representation that selects and corrects the descent fiber. Neither a totally real field nor a Moret--Bailly field is automatically such a tower. The residual theorem therefore stops over $F^{\mathrm{pm}}$.

## 12. Dependencies, downstream handoff, and verdict

### 12.1 Exact prior inputs

The proof uses the following earlier books, with no enlargement of their conclusions.

| Prior source | Result used | Boundary retained |
|---|---|---|
| Book 104 | transfer from the totally definite carrier to the split packet, followed by compact one-split inverse transfer for $\{w_0\}$ | requires even field degree and an eligible selected local factor; it supplies no Galois representation by itself |
| Book 98 | automorphic induction of an algebraic Hecke character, the determinant formula (3.3), the explicit residual induced lattice, and cuspidality | the quadratic extension must remain a field; the character quotient must remain nontrivial |
| Book 127 | compact-curve packet decomposition, rank-two extraction, determinant and Frobenius normalization, the weak family, and stable lattices | no surface realization or density theorem; integral finite-flat comparison is obtained from $A$, not from an arbitrary curve lattice |
| Book 176 | the direct finite-set Ihara-avoidance interface, Theorem 1.1H and Corollary 1.1I proving $({\rm CIAV}_S)$, plus the optional one-prime, all-point, and pointed geometric comparisons | the direct source-patching route is closed; the geometric routes retain their stated Ihara, cube, reciprocity, and occurrence hypotheses |
| Book 154 | Moret--Bailly specialization with local opens, total reality, splitting, and linear disjointness | no Galois or solvable conclusion |
| Book 158 | the fine smooth geometrically connected paired-frame moduli space, its admissible point-centered local opens, and the regular symmetric Galois-top refinement of the split specialization | both frames and both pairings must occur on the same object and component; nonsplit exact completion algebras still require Book 154's separate common-presentation hypothesis |
| Book 142, the globally upstream companion Chebotarev development | finite-quotient prime selection in Section 3.4 and Corollary 11.2 in Sections 8.5 and 9.3 | density recognizes existing data and supplies no carrier, lattice, or local compatibility |

Ordinary foundational inputs are finite-flat group schemes, polarization pairings, Schur's lemma, stable lattices, Nakayama's lemma, and elementary field-disjointness calculations. Book 109 is consulted only to state why descent is unavailable; no theorem from it enters Theorem 10.1. The source-closed direct row for the argument is therefore

$$
104,\ 98,\ 127,\ 176,\ 154,\ 158,\ 142. \tag{12.0}
$$

The current catalog row records exactly these seven sources. It omits Book 109, which is
consulted only for a negative descent boundary, and Book 178, whose later
potential-modularity assembly cannot be imported here.

### 12.2 Acyclic proof order

The order of dependence is:

$$
\text{dihedral residual packet}
\longrightarrow
\text{paired-frame specialization}
\longrightarrow
\text{auxiliary-prime lifting}
\longrightarrow
\text{one-split curve family}
\longrightarrow
\text{target residual packet}.
\tag{12.1}
$$

The automorphy of $A[\mathfrak q]$ is known before Book 176 is invoked. The automorphy of the target prime is obtained only after auxiliary-prime lifting and the curve construction of Books 104 and 127. Neither Book 178 nor any later potential-modularity, finite-set, compatible-system, unitary-surface, or descent manuscript is used upstream. This prevents the target conclusion from being smuggled into the seed.

### 12.3 Downstream record

A downstream FLT argument may use Theorem 10.1 only after recording:

1. the field $F^{\mathrm{pm}}$, every place required to split there, and disjointness from both residual cutout fields;
2. the automorphic packet $\Pi$, coefficient place $\widetilde\lambda$, determinant, and arithmetic-Frobenius convention;
3. the exact isomorphism (10.2), including its residue-field extension;
4. the finite-flat models above $\ell$ and the preservation of target image hypotheses;
5. the actual sets $P_A$ and $P_{\mathrm{act}}$, including every place above $v_0$, and the complete cleanability record used at every active place; and
6. the one-split compact-curve packet and transfer datum used to change coefficient prime.

That record supplies residual potential modularity only. A later argument for a chosen Frey lift must invoke its own modularity-lifting theorem and verify that lift's local components. It may not cite this book for rational automorphy descent, for automorphy of a chosen characteristic-zero lift, or for an unrestricted compatible system.

### 12.4 Readiness verdict

The advertised FLT-range lifting-admissible existence theorem is **READY**: Book 176,
Theorem 1.1H and Corollary 1.1I prove the direct finite-set
$({\rm CIAV}_{P_{\mathrm{act}}})$ theorem and treat all places above $v_0$ simultaneously.

On the geometric alternatives, the first unresolved constant-row dependency is the localized
abelian Ihara family (10.4), retained but not proved by Books 139 and 176. Book 122 and Book
174 supply the applicable actual-row typed parahoric extension, and Book 174 supplies the
one-place strict ray; even at one active place, the separate type-Ihara, type-incidence,
support, reciprocity, auxiliary-augmentation, primitive-residue, clean-lowering, and
carrier-comparison hypotheses must still be verified for the actual localization. For the
actual multi-place set $P_{\mathrm{act}}$, the all-point route additionally needs the global
cube, mixed exactness beginning with (10.5), the iterated-switch product-residue comparison,
full joint component support, coherent joint ring--complex--module--action--pairing
augmentation, and finite-set reciprocity, unless a validated one-prime chain is verified. The
pointed route still needs the actual final cube, simultaneous generic branch verification on
(8.6a), carrier-specific finite-set reciprocity, and the joint component occurrence (8.6b);
no accepted source proves that occurrence. Book 176 constructs the joint scalar ray and strict
product twist; auxiliary acting-image injectivity follows only after full base $R=T$ and is
not needed for either direct finite-level pointwise comparison. Complete splitting already
creates several active places above $v_0$ when $[F':F]>1$; the problem is not confined to
newly acquired bad reduction, and no sequential argument is being inferred from an ordering.

The curve carrier and change-of-prime step are ready once auxiliary-prime automorphy has been obtained: (6.2a), the selected special factor, Book 104, and Book 127 prove them without a surface. Thus they are not blockers in the readiness verdict.

The source-closed theorem of this book is precisely Theorem 10.1 under the lifting-admissible paired-specialization hypothesis, with endpoint over the constructed totally real field and with no rational automorphy descent. The bounded conditional topic is **READY**; the unrestricted catalog assertion for every target remains **NOT READY** at (10.4), followed by the multi-place obligations above.
