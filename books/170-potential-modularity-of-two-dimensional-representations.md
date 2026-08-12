# Potential Modularity of Two-Dimensional Representations

## Contents

1. [The bridge that potential modularity must build](#1-the-bridge-that-potential-modularity-must-build)
   - [From one residual representation to one geometric bridge](#11-from-one-residual-representation-to-one-geometric-bridge)
   - [Three meanings that must not be confused](#12-three-meanings-that-must-not-be-confused)
   - [Conventions and normalizations](#13-conventions-and-normalizations)
   - [The exact scope of this book](#14-the-exact-scope-of-this-book)
2. [The residual datum and its ledger](#2-the-residual-datum-and-its-ledger)
   - [A comparison lift outside the main theorem](#21-a-comparison-lift-outside-the-main-theorem)
   - [The residual target](#22-the-residual-target)
   - [Determinant, pairing, and polarization](#23-determinant-pairing-and-polarization)
   - [Conditions at the coefficient prime](#24-conditions-at-the-coefficient-prime)
   - [Conditions away from the coefficient prime](#25-conditions-away-from-the-coefficient-prime)
   - [Cyclotomic irreducibility and adjoint vanishing](#26-cyclotomic-irreducibility-and-adjoint-vanishing)
   - [The two-prime admissibility boundary](#27-the-two-prime-admissibility-boundary)
3. [Why two primes make a bridge](#3-why-two-primes-make-a-bridge)
   - [The switching diagram](#31-the-switching-diagram)
   - [Choosing the auxiliary prime](#32-choosing-the-auxiliary-prime)
   - [Constructing a known residual representation](#33-constructing-a-known-residual-representation)
   - [The four statements that do not follow automatically](#34-the-four-statements-that-do-not-follow-automatically)
4. [The realization space](#4-the-realization-space)
   - [When an elliptic curve is enough](#41-when-an-elliptic-curve-is-enough)
   - [When real multiplication is needed](#42-when-real-multiplication-is-needed)
   - [Symplectic level structures](#43-symplectic-level-structures)
   - [The fine elliptic moduli problem](#44-the-fine-elliptic-moduli-problem)
   - [The Hilbert--Blumenthal moduli problem](#45-the-hilbert--blumenthal-moduli-problem)
   - [Representability, smoothness, and dimension](#46-representability-smoothness-and-dimension)
   - [Geometric connectedness is a monodromy assertion](#47-geometric-connectedness-is-a-monodromy-assertion)
5. [Local points and local opens](#5-local-points-and-local-opens)
   - [The local design principle](#51-the-local-design-principle)
   - [Real places](#52-real-places)
   - [Places above the target prime](#53-places-above-the-target-prime)
   - [Places above the auxiliary prime](#54-places-above-the-auxiliary-prime)
   - [Good and semistable places away from both primes](#55-good-and-semistable-places-away-from-both-primes)
   - [Tate curves as explicit semistable comparison objects](#56-tate-curves-as-explicit-semistable-comparison-objects)
   - [Why the conditions are open](#57-why-the-conditions-are-open)
   - [The local nonemptiness ledger](#58-the-local-nonemptiness-ledger)
6. [The arithmetic existence step](#6-the-arithmetic-existence-step)
   - [The avoidance field](#61-the-avoidance-field)
   - [The Moret--Bailly input](#62-the-moret--bailly-input)
   - [The global point and its field](#63-the-global-point-and-its-field)
   - [A genuine disjointness lemma](#64-a-genuine-disjointness-lemma)
   - [What is and is not controlled about the field](#65-what-is-and-is-not-controlled-about-the-field)
7. [The auxiliary abelian variety](#7-the-auxiliary-abelian-variety)
   - [Pulling back the universal family](#71-pulling-back-the-universal-family)
   - [The two torsion identifications](#72-the-two-torsion-identifications)
   - [Duals and determinants](#73-duals-and-determinants)
   - [Preservation of residual images](#74-preservation-of-residual-images)
   - [The actual ramification record](#75-the-actual-ramification-record)
8. [Keeping the known side automorphic](#8-keeping-the-known-side-automorphic)
   - [The dihedral route over an arbitrary output field](#81-the-dihedral-route-over-an-arbitrary-output-field)
   - [The solvable-base-change route](#82-the-solvable-base-change-route)
   - [Cuspidality and self-twists](#83-cuspidality-and-self-twists)
   - [Why a nonsolvable output changes the argument](#84-why-a-nonsolvable-output-changes-the-argument)
9. [The first modularity-lifting step](#9-the-first-modularity-lifting-step)
   - [The auxiliary-adic Tate module](#91-the-auxiliary-adic-tate-module)
   - [The residual automorphic maximal ideal](#92-the-residual-automorphic-maximal-ideal)
   - [The coefficient-prime local hypotheses](#93-the-coefficient-prime-local-hypotheses)
   - [The away-from-the-coefficient-prime hypotheses](#94-the-away-from-the-coefficient-prime-hypotheses)
   - [The nonminimal infrastructure ledger](#95-the-nonminimal-infrastructure-ledger)
   - [Jacquet--Langlands and component switching](#96-jacquet--langlands-and-component-switching)
   - [Automorphy of the auxiliary-adic factor](#97-automorphy-of-the-auxiliary-adic-factor)
10. [Moving automorphic information to the target prime](#10-moving-automorphic-information-to-the-target-prime)
   - [Frobenius polynomials of a real-multiplication variety](#101-frobenius-polynomials-of-a-real-multiplication-variety)
   - [The automorphic coefficient field](#102-the-automorphic-coefficient-field)
   - [The target-adic representation attached to the same form](#103-the-target-adic-representation-attached-to-the-same-form)
   - [Chebotarev identifies the target-adic Tate module](#104-chebotarev-identifies-the-target-adic-tate-module)
   - [What changing the prime does not mean](#105-what-changing-the-prime-does-not-mean)
11. [A conditional second lifting step](#11-a-conditional-second-lifting-step)
   - [Residual modularity of the target](#111-residual-modularity-of-the-target)
   - [The characteristic-zero comparison point](#112-the-characteristic-zero-comparison-point)
   - [Determinant and coefficient-prime checks](#113-determinant-and-coefficient-prime-checks)
   - [Local components away from the target prime](#114-local-components-away-from-the-target-prime)
   - [The conditional application of the lifting theorem](#115-the-conditional-application-of-the-lifting-theorem)
   - [The residual stopping point](#116-the-residual-stopping-point)
12. [Solvable switching, inner forms, and descent](#12-solvable-switching-inner-forms-and-descent)
   - [A controlled further extension](#121-a-controlled-further-extension)
   - [Local component compatibility after restriction](#122-local-component-compatibility-after-restriction)
   - [The role of Jacquet--Langlands](#123-the-role-of-jacquet--langlands)
   - [Stopping over the larger field](#124-stopping-over-the-larger-field)
   - [Descending one cyclic layer at a time](#125-descending-one-cyclic-layer-at-a-time)
   - [Why there is no automatic descent to the original field](#126-why-there-is-no-automatic-descent-to-the-original-field)
13. [The theorem package](#13-the-theorem-package)
   - [Conditional residual potential modularity](#131-conditional-residual-potential-modularity)
   - [Conditional characteristic-zero potential automorphy](#132-conditional-characteristic-zero-potential-automorphy)
   - [The field-control theorem](#133-the-field-control-theorem)
   - [The elliptic-curve specialization](#134-the-elliptic-curve-specialization)
   - [Abstract geometric representations](#135-abstract-geometric-representations)
   - [Determinants with a finite-order factor](#136-determinants-with-a-finite-order-factor)
14. [Weight, level, and local type](#14-weight-level-and-local-type)
   - [Parallel weight two, determinant, and purity](#141-parallel-weight-two-determinant-and-purity)
   - [The conductor away from the coefficient prime](#142-the-conductor-away-from-the-coefficient-prime)
   - [Places above the coefficient prime](#143-places-above-the-coefficient-prime)
   - [The final local--global record](#144-the-final-local--global-record)
15. [Hostile diagnostics](#15-hostile-diagnostics)
   - [A pairing obstruction](#151-a-pairing-obstruction)
   - [An empty local moduli problem](#152-an-empty-local-moduli-problem)
   - [A local-component mismatch](#153-a-local-component-mismatch)
   - [Residual image lost under restriction](#154-residual-image-lost-under-restriction)
   - [A self-twist and noncuspidal base change](#155-a-self-twist-and-noncuspidal-base-change)
   - [A nonsolvable Moret--Bailly field](#156-a-nonsolvable-moret--bailly-field)
   - [A premature identification of coefficient primes](#157-a-premature-identification-of-coefficient-primes)
16. [The exported potential-modularity record](#16-the-exported-potential-modularity-record)
   - [The compatible-system interface](#161-the-compatible-system-interface)
   - [The descent and changing-prime interfaces](#162-the-descent-and-changing-prime-interfaces)
   - [The arithmetic interface](#163-the-arithmetic-interface)
   - [Dependency and conclusion audit](#164-dependency-and-conclusion-audit)
   - [Final synthesis](#165-final-synthesis)

## 1. The bridge that potential modularity must build

Potential modularity is an existence theorem with a carefully delimited endpoint. Starting from a residual two-dimensional representation over a totally real field, one is allowed to enlarge the field until the representation occurs in the reduction of a parallel-weight-two cuspidal automorphic representation. The enlargement is not a cosmetic device. It creates a rational point on a twisted moduli space, makes several local conditions simultaneously soluble, and preserves the residual images needed by modularity lifting.

The proof has four load-bearing pieces. A dihedral automorphic representation supplies a known residual system at an auxiliary prime. A determinant-compatible Hilbert--Blumenthal moduli space places that system and the prescribed residual representation on one polarized abelian variety. Moret--Bailly approximation supplies a totally real point field with the required local behavior and disjointness. A one-prime lifting theorem makes the auxiliary-adic Tate factor automorphic, after which weight-two Galois realization reads the same automorphic packet at the original coefficient prime.

Books 95, 168, and 169 supply the character-theoretic, arithmetic, and moduli ingredients. Book 156 supplies only its stated clean one-prime lifting range. Book 135 supplies weight-two Galois realizations only in its verified geometric range. Book 97 governs any separately supplied solvable ascent or descent. From Book 174 we use the controlled auxiliary seed, signed level-raising, clean augmentation, and exact two-prime admissibility boundary; its conditional final residual theorem is not used as a premise for the proof below. The argument retains every hypothesis at these interfaces.

### 1.1 From one residual representation to one geometric bridge

Let $F$ be totally real, let $\ell\geq7$, and let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
$$

be continuous, where $k$ is finite of characteristic $\ell$. Choose a second rational prime $q\geq7$, $q\ne\ell$, a totally real multiplication field $M$, and primes

$$
\lambda\mid\ell,
\qquad
\mathfrak q\mid q
$$

of $M$. The auxiliary representation $\bar\sigma$ in characteristic $q$ is chosen to be dihedral and residually automorphic. The desired Hilbert--Blumenthal abelian variety $A/F'$ carries exact paired frames

$$
A[\lambda]\simeq
\bar\rho|_{G_{F'}}\otimes_k k_\lambda,
\qquad
A[\mathfrak q]\simeq
\bar\sigma|_{G_{F'}}\otimes_{k_q}k_{\mathfrak q}. \tag{1.1}
$$

The bridge then has the form

$$
\begin{array}{ccccc}
\bar\sigma|_{G_{F'}}&\longleftarrow&A[\mathfrak q]&\longrightarrow&V_{\mathfrak q}(A)\\
\text{residually automorphic}&&&&\text{automorphic by clean lifting}\\[2mm]
&&A&&\\[-1mm]
\bar\rho|_{G_{F'}}&\longleftarrow&A[\lambda]&\longleftarrow&V_\lambda(A).
\end{array} \tag{1.2}
$$

There is only one modularity-lifting step in this residual theorem: it is the upper-right arrow at $q$. The lower-right arrow is instead a change of coefficient prime through the common Frobenius polynomials of $A$ and of the already automorphic packet. Reducing the resulting $\lambda$-adic comparison gives residual modularity of $\bar\rho|_{G_{F'}}$.

### 1.2 Three meanings that must not be confused

A residual representation $\bar r:G_K\to\operatorname{GL}_2(\overline{\mathbf F}_p)$ is **modular of parallel weight two over $K$** if there are a parallel-weight-two cuspidal automorphic representation $\pi$ of $\operatorname{GL}_2(\mathbf A_K)$, a coefficient place $\nu\mid p$, and a stable lattice such that

$$
\bar r^{\mathrm{ss}}\simeq\bar\rho_{\pi,\nu}^{\mathrm{ss}}.
$$

If $\bar r$ is absolutely irreducible, every stable lattice has isomorphic reduction and the semisimplification symbols may be removed.

A characteristic-zero representation is **automorphic over $K$** when it is isomorphic to the corresponding coefficient-adic realization of a cuspidal automorphic representation. A residual representation is **potentially modular** when its restriction to some finite totally real extension is modular. The theorem of this book proves the third statement. It does not assert that an arbitrary characteristic-zero lift of $\bar\rho$ is automorphic, and it does not descend the final automorphic representation to $F$.

### 1.3 Conventions and normalizations

For a number field $K$, write $G_K=\operatorname{Gal}(\overline K/K)$. Arithmetic Frobenius is used at finite unramified places. The $p$-adic cyclotomic character is $\chi_p$, and its reduction is $\bar\chi_p$. Tate modules are covariant:

$$
T_\nu(A)=\varprojlim_n A[\nu^n](\overline K),
\qquad
V_\nu(A)=T_\nu(A)\otimes_{\mathcal O_{M,\nu}}M_\nu.
$$

The geometric weight-two construction first gives a cohomological representation in geometric-Frobenius normalization, with inverse-cyclotomic determinant in the trivial-character case. Throughout this book $\rho_{\pi,\nu}$ denotes its **covariant dual**, so that it compares directly with a covariant Tate module. Thus, for trivial finite central character, its determinant is $\chi_p$. At an unramified place $v\nmid p$, the arithmetic-Frobenius polynomial is

$$
P_v(X)=X^2-a_vX+q_v, \tag{1.4}
$$

where $q_v$ is the residue cardinality. A finite central character $\psi$ changes the constant term to $\psi(v)q_v$ and the determinant to $\psi\chi_p$.

All pairings are alternating and Galois equivariant. For an elliptic curve the Weil pairing is

$$
e_{p^n}:A[p^n]\times A[p^n]\longrightarrow\mu_{p^n}.
$$

For a Hilbert--Blumenthal abelian variety, a chosen generator of the local polarization line turns the corresponding coefficient-prime pairing into the same form. Changing that generator changes the symplectic component, so it is recorded rather than suppressed.

### 1.4 The exact scope of this book

The conditional theorem applies to a **two-prime admissible weight-two residual datum**. In particular, $\ell\geq7$; $\bar\rho$ is totally odd, absolutely irreducible even after restriction to $F(\zeta_\ell)$, has cyclotomic determinant, has the required integral finite-flat models at places above $\ell$, and satisfies the named adjoint-twist vanishing. The auxiliary prime also satisfies $q\geq7$. The dihedral seed, the connected paired-frame component, all local comparison objects, the Moret--Bailly data, the post-specialization clean one-prime lifting datum, and the rational weight-two realization are parts of admissibility, not consequences of the first five residual conditions.

This scope is deliberately exact. No assertion is made for coefficient characteristic five. No arbitrary finite-order determinant is absorbed into a polarization. No broad modularity-lifting theorem is inferred from absolute irreducibility. No ordinary Moret--Bailly field is called Galois or solvable. The proved endpoint is residual potential modularity over a finite totally real field once the post-specialization cleanability clause has been verified. The present prerequisites do not prove that clause for every residual target in the catalog range.

## 2. The residual datum and its ledger

A potential-modularity argument should begin with a data sheet, not with the choice of an auxiliary curve. The eventual lifting theorem is sensitive to the coefficient field, determinant, local integral model, residual image, and named local components. If any of these is left vague at the start, the moduli construction can easily produce an object that cannot be used at the end.

This chapter gives the complete input record. The target representation in the residual theorem is only $\bar\rho$; the auxiliary, moduli, local, and lifting-admissibility data remain additional hypotheses. A characteristic-zero lift is discussed first only to explain why residual potential modularity does not automatically imply automorphy of a chosen lift.

### 2.1 A comparison lift outside the main theorem

Let $E/\mathbf Q_\ell$ be finite, with ring of integers $\mathcal O$, uniformizer $\varpi$, and residue field $k$. A possible characteristic-zero comparison lift is a continuous representation

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O) \tag{2.1}
$$

such that:

1. $\rho$ is unramified outside a finite set;
2. $\det\rho=\chi_\ell$;
3. for each real place $\tau$ and a corresponding complex conjugation $c_\tau$,
   $$
   \det\rho(c_\tau)=-1,
   \qquad
   \operatorname{tr}\rho(c_\tau)=0;
   $$
4. for every $v\mid\ell$, the lattice $\mathcal O^2$ is finite flat of type $(0,1)$ in the integral sense used in Book 156; and
5. away from $\ell$, the restriction at every ramified place lies on a named represented component admitted by the nonminimal lifting theorem.

In particular, for every embedding $\tau:F\hookrightarrow\overline{\mathbf Q}_\ell$ inducing $v\mid\ell$, the rational representation has Hodge--Tate multiset

$$
\operatorname{HT}_\tau(\rho)=\{0,1\}, \tag{2.1a}
$$

with the convention in which $\chi_\ell$ has weight $1$. The equality of the sum of these weights with the determinant weight is consistent with $\det\rho=\chi_\ell$.

The phrase “finite flat” in clause 4 means that every quotient $\mathcal O^2/\varpi^n$ is the generic fiber of a compatible finite locally free group scheme of the required type. Merely saying that $\rho$ is de Rham or crystalline with Hodge--Tate weights $\{0,1\}$ does not supply that integral system. Conversely, the finite-flat system gives the weight-two Hodge type in the range of the local theorem being used.

These conditions illustrate what a later lifting problem would require. They are not hypotheses of the residual theorem unless such a comparison lift is separately introduced, and no conclusion about (2.1) is claimed here.

### 2.2 The residual target

Choose the displayed lattice and let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k) \tag{2.2}
$$

be its reduction. The theorem starts directly from (2.2), without a chosen lift. We assume $\ell\geq7$, that $\bar\rho$ is absolutely irreducible and totally odd, and that

$$
\det\bar\rho=\bar\chi_\ell. \tag{2.3}
$$

At every $v\mid\ell$ it is the generic fiber of a named paired finite locally free group scheme of rank $|k|^2$. If $k\ne\mathbf F_\ell$, the coefficient structure is part of the model; forgetting it and restricting scalars changes the dimension. We further require

$$
\bar\rho|_{G_{F(\zeta_\ell)}}\text{ to be absolutely irreducible}. \tag{2.3a}
$$

Absolute irreducibility is geometric, not merely irreducibility over $k$. It asserts irreducibility after extending scalars to $\overline k$. This is the form preserved when the finite residual image is preserved, and it is the form required for stable-lattice uniqueness and the usual non-Eisenstein lifting argument.

### 2.3 Determinant, pairing, and polarization

For any rank-two module $V$, exterior product gives a perfect alternating map

$$
V\times V\longrightarrow\bigwedge^2V.
$$

Condition (2.3) permits a Galois-equivariant identification

$$
\delta_\ell:\bigwedge^2\bar\rho\xrightarrow{\sim}k(1). \tag{2.4}
$$

The choice of $\delta_\ell$ is part of the moduli datum. It is not determined by the equality of determinant characters: multiplying it by an element of $k^\times$ gives another symplectic coordinate. In the characteristic-zero setting, the same determinant gives

$$
\rho^\vee\simeq\rho\otimes\chi_\ell^{-1},
\qquad
\rho\simeq\rho^\vee(1). \tag{2.5}
$$

Thus the target has precisely the polarization expected of a weight-two rank-two factor.

For an elliptic curve $C$, the desired torsion isomorphism is not merely an isomorphism of $k[G_K]$-modules. It must make the square

$$
\begin{array}{ccc}
\bigwedge^2\bar\rho & \xrightarrow{\ \wedge^2\alpha_\ell\ } & \bigwedge^2 C[\ell]\\
\downarrow\delta_\ell && \downarrow e_\ell\\
k(1) & = & k(1)
\end{array} \tag{2.6}
$$

commute. For real multiplication, the lower row uses the chosen trivialization of the polarization line at $\lambda$. Every later determinant comparison is the shadow of this diagram.

### 2.4 Conditions at the coefficient prime

Fix $v\mid\ell$. The one-prime clean theorem used in this book has coefficient characteristic at least seven and assumes $F_v/\mathbf Q_\ell$ unramified at its coefficient-prime places. We therefore assume the relevant places are unramified and later force them to split completely in the potential-modularity field. This keeps the local field literally unchanged:

$$
F'_w=F_v\qquad(w\mid v). \tag{2.7}
$$

Let $\mathcal G_v$ be the paired finite locally free group scheme whose generic fiber is $\bar\rho|_{G_{F_v}}$. In an ordinary refinement it includes a chosen connected--étale filtration and ordinary line. In a local--local case it includes the actual Hilbert--Blumenthal seed realizing that finite-flat module. These are different local conditions; neither may be inferred from the other.

The residual Schur hypotheses used by the local deformation theorem are included explicitly. In one common formulation they require that the relevant residual endomorphism ring be $k$ and exclude exceptional extensions for which the finite-flat deformation functor has extra automorphisms. Since their exact expression depends on the local shape, the admissible datum records the named local theorem and verifies its hypotheses place by place.

In the clean unramified range the calculation is particularly sharp. If $f_v=[F_v:\mathbf Q_\ell]$ and

$$
\operatorname{End}_{k[G_{F_v}]}(\bar\rho_v)=k, \tag{2.7a}
$$

then the fixed-cyclotomic-determinant finite-flat deformation functor is represented by a formally smooth ring

$$
R_v^{\mathrm{fl}}\simeq
\mathcal O[[X_1,\ldots,X_{f_v}]], \tag{2.7b}
$$

and its framed version has three further frame variables. This is the local dimension used in the balanced global patching calculation. At a split residual representation the framed ring can remain smooth while a coarse unframed universal ring is unavailable; one then retains the frame or a line enhancement. Thus a convenient tangent dimension never licenses us to forget the precise representability hypothesis.

### 2.5 Conditions away from the coefficient prime

At $v\nmid\ell$, the target is allowed the controlled conditions established in Book 156. Typical cases are:

- unramified with fixed determinant;
- a fixed prime-to-$\ell$ finite inertial type on a named component;
- primitive Steinberg, including a chosen sign or stable-line branch and nonzero monodromy on the characteristic-zero point; or
- an enhanced ordered tame principal-series condition for which the integral type lattice and component theorem have been supplied.

The finite set of all such places is denoted $P_\rho$. At a Steinberg place the residual representation may be unramified even though $\rho$ has nonzero monodromy. This is exactly a nonminimal prime. At a finite-type place, equality of the generic inertial representation does not by itself say that two points lie on the same integral component.

For every $v\in P_\rho$, record:

$$
(\text{local functor},\ \text{component},\ \text{determinant},\
\text{conductor},\ \text{ordered data},\ \text{monodromy}). \tag{2.8}
$$

This record is later transported unchanged to every place above $v$ because those places will be split. If a further ramified extension is used for component switching, the record must instead be recomputed from the restricted Weil--Deligne representation.

### 2.6 Cyclotomic irreducibility and adjoint vanishing

Let

$$
W=\operatorname{ad}^0\bar\rho.
$$

Cyclotomic absolute irreducibility (2.3a) in characteristic at least seven supplies the adequacy conclusion used by the two-prime package. Separately, we assume

$$
H^0(F,W(1))=0. \tag{2.9}
$$

Adequacy is not a synonym for absolute irreducibility. It includes the group-theoretic vanishing and spanning conditions that make sufficiently many regular auxiliary Frobenius classes available. Small dihedral or exceptional images require a direct check; small coefficient primes often require a different theorem altogether.

Condition (2.9) excludes a cyclotomic self-twist in the adjoint representation. It is used in the balanced global deformation calculation. We assume both conditions for the target residual image and later preserve the entire image by disjointness. Since adequacy and (2.9) then depend on the same finite image and its cyclotomic action, the avoidance field will also contain the finite cyclotomic field needed to preserve the latter calculation.

### 2.7 The two-prime admissibility boundary

An **admissible weight-two residual target** consists of the following objects.

1. A totally real field $F$ and a prime $\ell\geq7$ unramified at the places where the unramified finite-flat theorem is used.
2. A residual representation (2.2), with (2.3), (2.3a), a pairing (2.4), total oddness, absolute irreducibility, and (2.9).
3. At each $v\mid\ell$, a paired finite locally free model $\mathcal G_v$, with every declared coefficient-extension model also satisfying the named local Schur hypotheses.
4. A full two-prime datum: a prime $q\geq7$, a controlled dihedral seed, a determinant-compatible connected paired-frame component, simultaneous local seeds, and the avoidance ledger.
5. After specialization, a one-prime clean lifting datum at $q$, or a finite clean chain changing one named prime at a time, including the conductor-one augmentation component, every newly appearing bad place, and every integral hypothesis of Book 156.
6. After the auxiliary lift, a verified rational weight-two geometric realization in the range of Book 135, with a stable lattice. The exact comparison with $A[\lambda]$ will be derived from the common Frobenius polynomials and absolute irreducibility, not assumed as an integral carrier comparison.

These last three clauses are the exact two-prime admissibility boundary of Book 174. Clauses 5--6 are post-specialization verification clauses, not inputs that ordinary Moret--Bailly approximation can guarantee and not consequences of absolute irreducibility. If the moduli space exists but the local seeds do not lie on one component, the proof stops before approximation. If the specialized auxiliary Tate module falls outside the clean local profile of Book 156, the proof stops before lifting. In particular, the current prerequisites do not supply the exact lower-face automorphic classes, flags, and integral vanishing-cycle data at every extra semistable prime that can appear only after specialization. If the automorphic packet lacks the rational geometric realization required by Book 135, the change-of-prime argument also stops.

## 3. Why two primes make a bridge

The target residual representation is not initially known to be modular, so it cannot seed a lifting theorem. The two-prime method inserts a second residual representation that is known to be modular and forces both residual representations to occur on one geometric object. This chapter explains how to choose that second side and why one exact lifting argument at the auxiliary prime is sufficient for the residual conclusion.

### 3.1 The switching diagram

Choose an odd prime $q\ne\ell$ and a residual representation

$$
\bar\sigma:G_F\longrightarrow\operatorname{GL}_2(k_q^{\mathrm{in}}). \tag{3.1}
$$

Here $k_q^{\mathrm{in}}$ is the finite input coefficient field of characteristic $q$; it need not yet be the residue field of a prime of the real-multiplication field used below. We reserve $\mathfrak q$ for the prime of that field above $q$ chosen after this input is fixed.

The construction is organized by

$$
\begin{array}{c}
\text{dihedral residual system at }q\\
\Downarrow\ \text{clean one-prime lifting}\\
V_{\mathfrak q}(A)\text{ is automorphic}\\
\Downarrow\ \text{common algebraic Frobenius polynomials}\\
V_\lambda(A)\text{ realizes the same packet}\\
\Downarrow\ A[\lambda]\simeq\bar\rho|_{G_{F'}}\\
\bar\rho|_{G_{F'}}\text{ is modular.}
\end{array} \tag{3.1a}
$$

Here the displayed Tate modules mean the rank-two factors at $\mathfrak q$ and $\lambda$, not the full Tate modules when $A$ has dimension greater than one. The middle arrow is not an isomorphism between a $q$-adic vector space and an $\ell$-adic vector space. It passes through one automorphic representation and its algebraic Frobenius polynomials. The diagram stops at the residual statement.

### 3.2 Choosing the auxiliary prime

The prime $q$ is chosen after the target data at $\ell$ are fixed but before the moduli space is constructed. It must satisfy several independent conditions:

1. $q\ne\ell$, $q\geq7$, and $q$ is unramified in $F$; in the clean good-reduction construction it is also outside the ramification set of $\bar\rho$;
2. the eventual residue field at $\mathfrak q$ contains the input field $k_q^{\mathrm{in}}$ and the declared scalar extension is fixed;
3. $\det\bar\sigma=\bar\chi_q$ after the chosen pairing normalization;
4. $\bar\sigma$ is absolutely irreducible, totally odd, and adequate for the first lifting theorem;
5. the associated global obstruction invariant $H^0(F,\operatorname{ad}^0\bar\sigma(1))$ vanishes;
6. at places above $q$, the auxiliary restriction admits the paired finite-flat model used in the moduli problem and its declared coefficient extension satisfies the residual Schur hypotheses, while the prime-to-$q$ target module is unramified with the exact Frobenius module on the same good-reduction comparison object;
7. at places above $\ell$, the auxiliary module is unramified in the clean good-reduction construction and its exact Frobenius module occurs on the comparison object carrying the target finite-flat model;
8. the automorphic representation producing $\bar\sigma$ has parallel weight two, has the characteristic-zero determinant and central character prescribed by the fixed-determinant problem, and lies in a non-Eisenstein block; and
9. all small-prime, vexing-prime, and integral type exclusions of the first lifting argument are satisfied.

There is no virtue in choosing $q$ small. In the controlled construction of Book 174, first choose the CM extension $K/F$ and then choose $q$ outside the target ramification set and the finite arithmetic exclusions, large enough for the ray-unit correction and the clean one-prime theorem. With $q$ fixed, construct the algebraic Hecke character so that its determinant, finite-flat local branches, and conjugate-ratio witnesses all survive modulo $q$; the correction characters and protected witnesses are chosen of order prime to $q$. Only then fix a place of its actual coefficient field above $q$, its residue field $k_q^{\mathrm{in}}$, the representation $\bar\sigma$, and its paired local models.

This order prevents circularity. The character-value field may enlarge while the ray-class problem is solved, so the totally real multiplication field $M$ is not chosen beforehand. Once $q$, $\bar\sigma$, its actual residue field, its pairing, and all local $q$-models are fixed, the simultaneous coefficient-realization theorem of Book 174 chooses $M$, $\lambda$, and $\mathfrak q$ to receive both residual coefficient fields and to make both primes unramified and monodromy-admissible. The moduli space comes last. If the local inspection fails, one returns to the character or to $q$; one may not alter the reduced local characters while pretending to retain the same global Hecke character.

The field $M$ is chosen so that its residue fields at $\lambda$ and $\mathfrak q$ are the declared scalar extensions of the two residual coefficient fields, and so that $\ell q$ is prime to the polarization and auxiliary level. Prescribing separable factorization at $\ell$ and $q$ and requiring all archimedean roots to remain real gives a totally real $M$. Nothing requires $M$ to be larger than necessary; its degree is both the dimension of the moduli space and the dimension of the auxiliary abelian variety.

### 3.3 Constructing a known residual representation

A robust choice is dihedral. Let $K/F$ be a totally imaginary quadratic extension and let $\Theta$ be an algebraic Hecke character of $K$ whose infinity type at every CM pair is $(1,0)$ in the normalization of Book 95, up to the common determinant normalization, so that its automorphic induction has parallel weight two and cyclotomic Galois determinant. Choose a $q$-adic coefficient field $E_{\Theta,q}$ whose ring of integers $\mathcal O_{\Theta,q}$ has residue field $k_q^{\mathrm{in}}$, enlarging the coefficient field before fixing the input if necessary. Let

$$
\theta_q:G_K\longrightarrow\mathcal O_{\Theta,q}^\times
$$

be its $q$-adic avatar and let $\bar\theta:G_K\to(k_q^{\mathrm{in}})^\times$ be its reduction. Put

$$
\bar\sigma=\operatorname{Ind}_{G_K}^{G_F}\bar\theta. \tag{3.2}
$$

The construction requires

$$
\bar\theta\ne\bar\theta^c, \tag{3.3}
$$

where $c$ is the nontrivial automorphism of $K/F$. This makes (3.2) absolutely irreducible. A complex conjugation interchanges the two induced lines, so its eigenvalues are $1$ and $-1$ and $\bar\sigma$ is odd.

The determinant is not automatic. If $\epsilon_{K/F}$ is the quadratic character and $\operatorname{Ver}:G_F^{\mathrm{ab}}\to G_K^{\mathrm{ab}}$ is transfer, then

$$
\det\bar\sigma
=\epsilon_{K/F}\,(\bar\theta\circ\operatorname{Ver}). \tag{3.4}
$$

The Hecke character is chosen so that (3.4) is $\bar\chi_q$ and so that the corresponding pairing

$$
\delta_q:\bigwedge^2\bar\sigma\xrightarrow{\sim}k_q^{\mathrm{in}}(1) \tag{3.5}
$$

is fixed. At $q$-adic places, its local characters are selected so that (3.2) has the required finite-flat model. Away from a controlled conductor it is unramified.

Automorphic induction gives a cuspidal parallel-weight-two representation $\pi_0$ over $F$. Cuspidality uses (3.3): if the character descended through the norm, the induction would be a sum of two characters. Choose the residual dihedral image of order prime to $q$ and absolutely irreducible. Maschke vanishing and the spanning of endomorphisms by semisimple image elements then give adequacy; the remaining adjoint cyclotomic invariant is checked separately.

The clean lifting theorem also needs one selected prime $v_0\nmid q$ at which the residual dihedral system occurs in an enhanced special localization. If the unramified residual Frobenius roots are $\alpha$ and $\beta$, choose $v_0$ so that, in an ordered normalization,

$$
\alpha=q_{v_0}\beta,
\qquad
q_{v_0}\not\equiv1,-1\pmod q. \tag{3.6}
$$

The first equality is the level-raising relation; the second keeps the two residual roots and the two signed Gram factors distinct. Saturated degeneracy maps, the non-Eisenstein localization, the primary and companion type lattices, and local--global compatibility then place the same residual system in the named minimal-special block with its invariant line and sign. The local Hilbert--Blumenthal seed at $v_0$ is split semistable with rank-one monodromy. Its $q$-adic Tate module lies on the conductor-one augmentation face, not on a nontrivial conductor-two tame-character face. The clean datum retains this distinction throughout.

### 3.4 The four statements that do not follow automatically

The two-prime slogan conceals four false implications.

First,

$$
A[\mathfrak q]\simeq
\bar\sigma|_{G_{F'}}\otimes_{k_q^{\mathrm{in}}}k_{\mathfrak q}
$$

does not imply that $V_{\mathfrak q}(A)$ is automorphic. It only identifies its reduction. The first lifting theorem is indispensable.

Second, automorphy of $V_{\mathfrak q}(A)$ does not identify $V_\lambda(A)$ by changing coefficient fields inside matrices. The two representations live over different local fields. They are related through the algebraic Frobenius polynomial of $A$ and the same automorphic representation.

Third,

$$
A[\lambda]\simeq
\bar\rho|_{G_{F'}}\otimes_k k_\lambda
$$

does not imply that an arbitrary lift $\rho$ is automorphic. The second lifting theorem must show that the particular characteristic-zero point defined by $\rho$ lies on automorphic support.

Fourth, none of these conclusions over $F'$ descends to $F$ merely because $F'/F$ is finite. Base change and descent have exact solvability, cuspidality, invariance, central-character, and twisting-fiber hypotheses.

## 4. The realization space

The arithmetic existence theorem can only globalize local points on a suitable variety. It does not create that variety, prove it smooth, choose a geometric component, or remove automorphisms. The moduli construction must therefore be audited before any approximation argument begins.

There are two realizations. An elliptic curve is the most economical object when both residual coefficient fields and all local comparison problems fit on one simultaneous full-level modular curve. A Hilbert--Blumenthal abelian variety is the robust replacement when coefficient fields or local flexibility require more room.

### 4.1 When an elliptic curve is enough

Assume first that

$$
k=\mathbf F_\ell,
\qquad
k_q^{\mathrm{in}}=\mathbf F_q,
$$

and that both determinants are cyclotomic with chosen pairings (2.4) and (3.5). A single elliptic curve $C$ can carry both levels:

$$
C[\ell]\simeq\bar\rho,
\qquad
C[q]\simeq\bar\sigma. \tag{4.1}
$$

Since $\ell$ and $q$ are coprime, this is equivalent to a suitably paired full level-$\ell q$ structure with twisted Galois descent. The resulting moduli space is a curve. Positive dimension is enough for Moret--Bailly; there is no theorem requiring dimension at least two.

An elliptic curve therefore suffices in the intended rank-two, cyclotomic-determinant setting when all of the following have been verified:

- the simultaneous twist has a fine geometrically connected component defined over $F$;
- that component has points in every required completion;
- its real component and auxiliary rigidification are compatible;
- the finite-flat local models at $\ell$ and $q$ occur on it; and
- its local semistable or good-reduction conditions have nonempty open neighborhoods.

The phrase “elliptic curves are one-dimensional” is not an obstruction. The obstruction is emptiness or disconnectedness of the particular twisted level curve. When those occur, increasing the dimension can make the local construction feasible.

### 4.2 When real multiplication is needed

Let $M$ be a totally real field of degree $g$, and choose primes

$$
\lambda\mid\ell,
\qquad
\mathfrak q\mid q
$$

and write

$$
k_\lambda=\mathcal O_M/\lambda,
\qquad
k_{\mathfrak q}=\mathcal O_M/\mathfrak q.
$$

Fix embeddings $k\hookrightarrow k_\lambda$ and $k_q^{\mathrm{in}}\hookrightarrow k_{\mathfrak q}$ realizing the declared scalar extensions, and put

$$
V_\ell=\bar\rho\otimes_k k_\lambda,
\qquad
V_q=\bar\sigma\otimes_{k_q^{\mathrm{in}}}k_{\mathfrak q}.
$$

A Hilbert--Blumenthal abelian variety $A$ of dimension $g$ with $\mathcal O_M$-action has rank-two factors

$$
A[\lambda],\qquad A[\mathfrak q].
$$

The moduli variety has dimension $g$, while imposing the two prime-level frames is finite etale on the characteristic-zero generic fiber. Thus the level conditions do not consume the $g$ deformation directions.

This higher-dimensional object is needed in three common situations. First, a residual coefficient field larger than the prime field cannot be realized as the coefficient ring of $C[\ell]$ without changing the meaning of dimension. Second, local conditions at $\ell$ and $q$ may be simultaneously realizable on an RM variety even when the corresponding twisted modular curve has no local point. Third, product monodromy and additional deformation directions can make it possible to select one geometrically connected component with the required local opens.

The present book covers HBAVs whose coefficient-prime Tate modules have rank two and whose polarization makes their determinant cyclotomic. It does not claim potential automorphy for arbitrary higher-dimensional abelian varieties or for rank greater than two.

### 4.3 Symplectic level structures

Let $V_\ell$ and $V_q$ denote the two paired residual modules. The moduli object includes isomorphisms

$$
\alpha_\ell:V_\ell\xrightarrow{\sim}A[\lambda],
\qquad
\alpha_q:V_q\xrightarrow{\sim}A[\mathfrak q], \tag{4.2}
$$

that preserve the chosen alternating forms. In rank two,

$$
\operatorname{GSp}_2=\operatorname{GL}_2,
\qquad
\text{multiplier}(g)=\det g,
$$

but this identity does not permit us to forget the multiplier. Fixing the pairing selects an open-and-closed determinant component, and the descent cocycle must land in

$$
\operatorname{SL}_2(k_\lambda)\times\operatorname{SL}_2(k_{\mathfrak q}). \tag{4.3}
$$

If the cocycle lands only in the similitude group, it permutes pairing components. One must then descend the correct union and prove that a selected geometric component is defined over $F$. Merely choosing a component after base change to $\overline F$ does not give an $F$-variety.

The pairings also control duals. From (4.2) one gets

$$
A[\lambda]^\vee\simeq A[\lambda](-1),
\qquad
A[\mathfrak q]^\vee\simeq A[\mathfrak q](-1), \tag{4.4}
$$

in the chosen polarization convention, and therefore the exact determinant characters needed by both lifting problems.

### 4.4 The fine elliptic moduli problem

In the elliptic case define $X$ to classify tuples

$$
(C,\alpha_\ell,\alpha_q,\eta_N), \tag{4.5}
$$

where $C$ is an elliptic curve, the two maps are the paired frames (4.2), and $\eta_N$ is a sufficiently deep auxiliary rigidification of order prime to $\ell q$. The rigidification is chosen with a descent form that has the required real and finite local points. A constant full odd-order frame is not automatically compatible with real conjugation.

Over a finite splitting field, $X$ becomes a fixed-pairing component of a full-level modular curve. Full level at primes at least three kills automorphisms; the auxiliary level makes this independent of small-level accidents and gives a universal elliptic curve. Descent along the product frame cocycle gives a fine affine curve over $F$.

The geometric connectedness statement is made for the selected fixed-pairing component. The union of all Weil-pairing values can be connected over $F$ while splitting geometrically. Such arithmetic connectedness is insufficient for Moret--Bailly.

We spell out the descent because it is the first place where the determinant does real geometric work. Over a finite Galois extension $L/F$ splitting $V_\ell$, $V_q$, and both root-of-unity lines, choose paired bases. The ordinary fixed-pairing full-level curve $Y_L$ carries a universal curve and universal frames. For $\gamma\in\operatorname{Gal}(L/F)$, compare the transported chosen bases with the original ones. The discrepancies give matrices

$$
c_{\ell,\gamma}\in\operatorname{SL}_2(\mathbf F_\ell),
\qquad
c_{q,\gamma}\in\operatorname{SL}_2(\mathbf F_q). \tag{4.5a}
$$

They have determinant one precisely because the chosen pairings are Galois equivariant. With one consistent right-action convention they satisfy

$$
c_{\gamma\delta}=c_\gamma\,{}^\gamma c_\delta.
$$

Use this cocycle to modify the ordinary Galois descent datum on $Y_L$. Effective descent applies to the quasi-projective curve and its universal family. An $R$-point of the descended curve, pulled back to $L$, is fixed by the modified action exactly when its two frames are equivariant for $V_\ell$ and $V_q$. This proves that rational points of the twist have the claimed moduli meaning.

Full ordered level at an odd prime eliminates $[-1]$, but the independent neat rigidification is retained for uniformity and to control quotient-level variants. Since the fixed-pairing level maps are finite etale over the characteristic-zero base, smoothness descends from the ordinary modular curve. Over $\overline F$ the cocycle is a coboundary, so the twist becomes the original geometric fixed-pairing component. Thus geometric connectedness is checked on that component, not on its arithmetic union.

### 4.5 The Hilbert--Blumenthal moduli problem

Fix a fractional polarization ideal $\mathfrak c$, a positivity orientation, and a neat auxiliary level $\mathfrak n$, all prime to $\ell q$ and to the relevant different. A point of the untwisted Hilbert--Blumenthal space is a tuple

$$
(A,\iota,\lambda_A,\eta_{\mathfrak n}) \tag{4.6}
$$

where $A$ has relative dimension $g$, $\iota:\mathcal O_M\hookrightarrow\operatorname{End}(A)$, and the determinant condition is

$$
\det(T-\iota(a)\mid\operatorname{Lie}A)
=\prod_{\tau:M\hookrightarrow\overline{\mathbf Q}}(T-\tau(a)). \tag{4.7}
$$

The polarization has the prescribed $\mathfrak c$-type and sends the positive cone to polarizations. The neat level kills every automorphism preserving the datum. A chosen narrow-class and orientation component is required to be geometrically connected and defined over $F$.

Add the paired frames (4.2). After splitting both residual modules, this is a finite etale frame cover of the fine Hilbert--Blumenthal space. Twisting by the product cocycle produces

$$
X=X(\bar\rho,\bar\sigma), \tag{4.8}
$$

and an $L$-point of $X$ is, by the moduli interpretation, an actual HBAV over $L$ with Galois-equivariant paired torsion identifications. It is not merely an isomorphism class over $\overline L$.

There are three component choices in (4.6), and they should not be conflated. The ideal $\mathfrak c$ fixes a polarization module up to the declared narrow class. Positivity chooses an orientation at every real embedding. Determinants of auxiliary and prime-level frames choose finite component coordinates. The absolute Galois group can permute any of these coordinates. Before twisting, one verifies that their combined stabilizer defines a geometrically connected component over $F$. If it is defined only over a preliminary totally real extension $F_0$, then $F_0$ must be introduced before the residual fixed fields and avoidance problem are chosen. Silently replacing $F$ by $F_0$ afterward could already have reduced a residual image.

The universal polarization induces, at a coefficient prime $\nu$ not dividing its degree, a form with values in a one-dimensional line $L_\nu(1)$. A generator of $L_\nu$ is chosen once. The target pairing is then an isomorphism

$$
\bigwedge^2V_\nu\xrightarrow{\sim}L_\nu(1). \tag{4.8a}
$$

Changing the convention from $\mathfrak c$ to $\mathfrak c^{-1}$ changes $L_\nu$ and the displayed duality simultaneously. It does not change the argument if every occurrence is changed; mixing the two conventions gives a false determinant comparison.

### 4.6 Representability, smoothness, and dimension

The fine-space theorem of Book 169 applies only after all of the preceding Hilbert--Blumenthal and level data have been fixed. It gives a quasi-projective scheme with a universal tuple. Smoothness is checked on the characteristic-zero generic fiber by deforming the Hodge filtration. After splitting $M$, one has

$$
H^1_{\mathrm{dR}}(A)=\bigoplus_\tau H_\tau,
\qquad
\dim H_\tau=2,
\qquad
\dim(\omega_A\cap H_\tau)=1. \tag{4.9}
$$

Lifting one line in each two-dimensional summand gives one parameter per real embedding. Consequently

$$
\dim X=[M:\mathbf Q]=g. \tag{4.10}
$$

The $\lambda$-, $\mathfrak q$-, and auxiliary levels are finite etale in characteristic zero, so they add no tangent directions and no infinitesimal obstructions. This proves smoothness of the generic moduli variety. It does not prove that a full-level integral model is smooth in residue characteristic $\ell$ or $q$. Local integral behavior at those primes is supplied by separate comparison objects and neighborhoods.

Representability and smoothness solve different problems. A smooth coarse quotient need not carry a universal abelian variety. Neatness eliminates stabilizers and produces a fine scheme; the Hodge-filtration calculation proves smoothness.

For completeness, the representability argument has four stages. Begin with a sufficiently rigid fine moduli scheme of polarized abelian varieties of the chosen degree. The equations expressing the $\mathcal O_M$-action and Rosati compatibility cut out a closed locus; polarization type and the determinant condition select locally closed strata. Neat level eliminates the remaining finite stabilizers. Finally, the two symplectic frame functors are finite etale torsors on the generic fiber, and fixed pairing selects open-and-closed subschemes. These operations preserve quasi-projectivity. Descent by the finite product cocycle preserves fineness because the universal tuple descends with the scheme.

The formal smoothness calculation can also be read as an obstruction calculation. For a square-zero thickening $R\twoheadrightarrow R/I$, a lift of the abelian scheme is equivalent to an $\mathcal O_M$-stable isotropic lift of its Hodge filtration. In the decomposition (4.9), a lift of the line $\omega_\tau$ is a graph of a map

$$
\omega_\tau\longrightarrow
(H_\tau/\omega_\tau)\otimes I. \tag{4.10a}
$$

This Hom module has rank one. Every line in a two-dimensional alternating plane is isotropic, so there is no quadratic obstruction in that factor and no equation linking different $\tau$. Prime-to-characteristic etale levels lift uniquely. Hence the completed local ring is a power-series ring in $g$ variables. This proves both formal smoothness and the dimension formula, while making no assertion about residue-characteristic full-level integral models.

### 4.7 Geometric connectedness is a monodromy assertion

Let $Y^\circ$ be the selected untwisted Hilbert--Blumenthal component. Its simultaneous paired frame cover has deck group

$$
G=\operatorname{SL}_2(k_\lambda)\times\operatorname{SL}_2(k_{\mathfrak q}). \tag{4.11}
$$

If the geometric monodromy representation of $\pi_1(Y^\circ_{\overline F})$ surjects onto $G$, the frame cover is geometrically connected: its connected components are the orbits of geometric monodromy on one fiber, and surjectivity makes that action transitive. Twisting by a cocycle in $G$ changes arithmetic descent but becomes trivial over $\overline F$, so the twist remains geometrically connected.

This argument must be made for the product image. Surjectivity to each factor separately does not always imply surjectivity to the product; a diagonal common quotient can remain. Because the two residue characteristics are distinct, the standard large monodromy hypotheses often exclude a common nontrivial quotient, but that exclusion is part of the proof.

We therefore carry forward the following geometric conclusion, and no weaker substitute:

$$
X/F\text{ is smooth, geometrically connected, quasi-projective,}
\quad \dim X>0, \tag{4.12}
$$

and $X$ carries the universal fine tuple. This is exactly the geometric input required by the arithmetic existence theorem.

Here is the orbit proof in detail. Pick a geometric point $y$ of $Y^\circ$ and a paired frame above it. The geometric fiber of the frame cover is a principal homogeneous $G$-set. Connected components of a finite etale cover correspond to orbits of the geometric fundamental group on that fiber. If the image is all of $G$, the action by translations is transitive, so the cover is connected. Since the base and cover are smooth, distinct geometric irreducible components would be disjoint open-and-closed subsets. Connectedness therefore implies geometric irreducibility as well.

A product-image check is indispensable. If the image were the graph of an isomorphism between nontrivial quotients of the two factors, each projection could be surjective while the action on the product frame set had several orbits. The distinct-characteristic hypothesis and the specific monodromy theorem of Book 169 rule out such a common quotient in the admitted datum. A twist has the same geometric cover after extending to $\overline F$, so it has the same orbit decomposition.

## 5. Local points and local opens

Moret--Bailly begins only after a nonempty open subset of $X(F_v)$ has been supplied at every relevant place. An abstract assertion that the residual modules are locally compatible is not enough. One must exhibit a local elliptic curve or HBAV carrying both level structures, place it on the selected global component, and show that the desired reduction and integral torsion properties persist in a neighborhood.

The local problem is intentionally asymmetric. At a place above $\ell$, the $\lambda$-torsion has residue-characteristic geometry while the $\mathfrak q$-torsion is prime to the residue characteristic. At a place above $q$, the roles reverse. Keeping that asymmetry visible is the simplest way to avoid treating a finite etale generic module as though it determined its integral model.

### 5.1 The local design principle

Let $S$ contain all real places, all places above $\ell q$, every place at which either residual representation is ramified, every place at which a particular reduction type is required, and every place at which the Hilbert--Blumenthal or auxiliary level has bad integral geometry. For each $v\in S$, the local datum consists of an object

$$
B_v/F_v
$$

of the same moduli type as the universal family, together with the same polarization, orientation, auxiliary rigidification, and paired level maps

$$
V_\ell|_{G_{F_v}}\xrightarrow{\sim}B_v[\lambda],
\qquad
V_q|_{G_{F_v}}\xrightarrow{\sim}B_v[\mathfrak q]. \tag{5.1}
$$

At residue-characteristic places, (5.1) is supplemented by an isomorphism of finite locally free group schemes over $\mathcal O_{F_v}$. At a semistable place it is supplemented by a named semiabelian model or boundary chart. The resulting moduli point must lie on the same selected component $X$, not merely on some component of the untwisted space.

Once such a point $x_v\in X(F_v)$ exists, the local open $\Omega_v$ is built around it. All simultaneous conditions at $v$ are intersected only after $x_v$ has been shown to satisfy them. Nonemptiness of the individual conditions does not imply nonemptiness of their intersection.

### 5.2 Real places

Let $v$ be real. Since the residual characteristics are odd, a totally odd two-dimensional module restricts to $G_{F_v}=\{1,c\}$ as the direct sum of a $+1$ line and a $-1$ line. A real polarized elliptic curve or HBAV has the same involution type on every rank-two coefficient-prime torsion factor. Thus oddness is the necessary linear-algebra compatibility.

It is not sufficient. The real point must also have the selected polarization orientation, narrow-class component, and auxiliary-level descent. In the elliptic case one may start with a real elliptic curve

$$
C_y:y^2=x^3-x
$$

and choose paired frames after identifying the $+1$ and $-1$ eigenspaces. The actual equation is inessential; its value is that it gives a concrete real polarized torus. The auxiliary rigidification must be chosen in an orbit on which conjugation has the same involution. A constant full odd-order frame would force conjugation to act trivially and can make the real moduli problem empty.

In the HBAV case one chooses a point of the correct component of the Hilbert modular real locus. Analytically the positive component is modeled on a quotient of $\mathfrak H^g$, but the existence of complex points does not imply the existence of a point fixed by the real descent datum. The admissible datum includes an actual $B_v$ and all its frames.

The linear-algebra part contains no hidden classification. Over $\mathbf R$, every odd two-dimensional representation over its finite coefficient field $\kappa$ is isomorphic to

$$
\kappa\oplus\kappa(\operatorname{sgn}).
$$

Choose a $+1$ vector $e$ and a $-1$ vector $f$. Replacing $f$ by $af$ changes $\langle e,f\rangle$ by $a$, so one can match any prescribed nonzero pairing value before the auxiliary level is fixed. This shows that oddness removes the torsion-involution obstruction. The orientation and rigidification conditions remain genuinely moduli-theoretic, which is why an actual real point remains part of the datum.

The real locus of a smooth variety is a real manifold near $x_v$. Choose a small open neighborhood $\Omega_v$ contained in the desired orientation component. Requiring every conjugate of the eventual global point to lie in this open is what proves that the output field is totally real.

### 5.3 Places above the target prime

Let $v\mid\ell$. The target residual module comes with a paired finite locally free model $\mathcal G_v$. Let $\mathcal G_{v,\lambda}$ be the chosen coefficient-extension model whose generic fiber is $V_\ell=\bar\rho\otimes_k k_\lambda$. In the main theorem the local comparison object is required to extend to an abelian scheme $\mathcal B_v/\mathcal O_{F_v}$ with good reduction and to carry an isomorphism

$$
\mathcal G_{v,\lambda}\xrightarrow{\sim}\mathcal B_v[\lambda] \tag{5.2}
$$

compatible with the coefficient action, Cartier duality, and the polarization pairing. Its generic fiber is the first map in (5.1), but (5.2) contains strictly more information.

A semistable comparison object at $v\mid\ell$ belongs only to a variant supplied with a coefficient-prime semistable lifting theorem and its integral local model. The clean finite-flat theorem used here does not accept it. The same restriction will be imposed at $q$ for the first lifting step.

There are two standard sources of such local points. For an ordinary model, begin with an ordinary special-fiber HBAV and use its Serre--Tate deformation space. For a split-normalized seed, the connected--etale sequence on the $\lambda$-torsion has the form

$$
0\longrightarrow\mu_\ell\otimes_{\mathbf F_\ell} k_\lambda
\longrightarrow\mathcal B_v[\lambda]
\longrightarrow(\mathbf Z/\ell\mathbf Z)\otimes_{\mathbf F_\ell} k_\lambda
\longrightarrow0. \tag{5.3}
$$

In general the two graded pieces carry paired unramified twists. If $\bar\psi_v$ is the character on the etale quotient, their generic characters are $\bar\psi_v$ and $\bar\chi_\ell\bar\psi_v^{-1}$. The local comparison must match those characters before deformation. The Serre--Tate parameter then varies the extension class while leaving the graded pieces fixed. A chosen lift realizing the extension class of $\mathcal G_{v,\lambda}$ is a local point, and a sufficiently small integral residue tube stays on the same ordinary finite-flat component. For a supersingular model, one instead begins with a supersingular special-fiber object and lifts its height-two connected factor on the named local model. No ordinary line is then asserted.

The $\mathfrak q$-torsion has order prime to the residue characteristic. If $\mathcal B_v$ has good reduction, it is finite etale and unramified, so its frame is determined by its actual unramified Frobenius module. A desired $V_q|_{G_{F_v}}$ with a different Frobenius polynomial cannot be installed by choosing a basis. In the semistable case the prime-to-$\ell$ torsion may have nontrivial unipotent inertia, which must match the second map of (5.1).

Thus the local existence assertion at $v\mid\ell$ is exactly: a paired integral object satisfying (5.2) and the actual $\mathfrak q$-torsion comparison has been constructed. Finite flatness of $V_\ell$ by itself does not construct it.

One useful source of HBAV comparison objects is the Serre tensor construction. Start with an elliptic curve $C/\mathcal O_{F_v}$ and a projective $\mathcal O_M$-lattice $P$ of rank one. Under the usual positivity and polarization compatibility, the tensor object

$$
P\otimes C
$$

is locally an abelian scheme isogenous to $C^g$ with $\mathcal O_M$-action satisfying the determinant condition. At a degree-one prime $\lambda\mid\ell$, its $\lambda$-torsion is the corresponding scalar extension of $C[\ell]$. This constructs many split ordinary and supersingular seeds and makes the pairings computable from the Weil pairing and the trace form on $P$.

It does not realize every local module. More general seeds come from an $\mathcal O_M$-linear isogeny or from lifting a special-fiber HBAV with the desired residue-characteristic and prime-to-$\ell$ data. The admissible local datum names the construction used. Once one seed exists, the formal deformation calculation supplies an analytic family; it is not used backward to infer the seed's existence.

### 5.4 Places above the auxiliary prime

Let $v\mid q$. Reverse the two roles. Let $\mathcal H_v^{\mathrm{in}}$ be the named paired finite locally free model of $\bar\sigma|_{G_{F_v}}$, and let $\mathcal H_{v,\mathfrak q}$ be its chosen coefficient-extension model with generic fiber $V_q$. The good-reduction abelian scheme $\mathcal B_v/\mathcal O_{F_v}$ carries

$$
\mathcal H_{v,\mathfrak q}\xrightarrow{\sim}\mathcal B_v[\mathfrak q]. \tag{5.4}
$$

The model is chosen so that the first lifting theorem recognizes $V_{\mathfrak q}(B_v)$ as finite flat of type $(0,1)$. In the dihedral construction this requirement is checked from the local characters of $\Theta$ and the splitting behavior of $K/F$ at $v$ before $q$ is fixed.

The $\lambda$-torsion is now prime to the residue characteristic. Under good reduction it is unramified and is matched by its full Frobenius module. Thus, in the clean good-reduction theorem, the target residual representation must be unramified at places above $q$ with the Frobenius module occurring on the chosen comparison object. If it is ramified there, one must use a semistable or otherwise suitable local comparison object whose actual $\lambda$-torsion has that inertia; this belongs only to a variant equipped with the corresponding coefficient-prime semistable lifting theorem and integral local model. The fact that $\ell\ne q$ makes the level finite etale on the generic fiber; it does not force unramifiedness.

As at $\ell$, ordinary and nonordinary components are distinguished. A generic finite-flat module need not have a unique integral model, and an abstract isomorphism of its geometric generic points need not extend to (5.4).

For a split $q$-adic CM place, the auxiliary induction restricts as a sum of two characters. Choosing the infinity-normalized character so that one local character has Hodge--Tate weight one and the other weight zero gives an ordinary finite-flat model of the form (5.3), with $q$ and $k_{\mathfrak q}$ in place of $\ell$ and $k_\lambda$, and with the paired unramified twists just described when they are nontrivial. At an inert place, the local representation is induced from a quadratic local extension and requires the corresponding height-two local model. These lie on different local components. The splitting behavior of $K/F$ at $q$ is therefore chosen to agree with the HBAV seed before the global moduli space is fixed.

### 5.5 Good and semistable places away from both primes

At $v\nmid\ell q$, both prime-level structures are finite etale. If both residual modules are unramified and their Frobenius data occur on a good-reduction local object $B_v$, then the required point lies in the good integral locus. The inverse image of its smooth reduction class is a nonempty $v$-adic open on which good reduction and the two finite etale local systems remain constant.

At a place where a Steinberg condition is required, choose a semistable comparison object of toric rank one on the relevant rank-two factor. Its Weil--Deligne representation has nonzero nilpotent monodromy

$$
N\ne0,
\qquad
N^2=0. \tag{5.5}
$$

The sign or unramified twist on the invariant line is also recorded. In a toroidal compactification this condition is imposed near a smooth point of a named boundary stratum. Valuation inequalities on one degeneration parameter and unit conditions on the others define an analytic open avoiding deeper boundary strata. Calling the entire boundary “semistable of rank one” would be wrong: intersections can change toric rank and splitting.

At finite-type places, start with a local abelian variety whose inertia action is the prescribed type. A sufficiently small analytic neighborhood keeps the prime-to-residue-characteristic torsion local systems constant. The component of the characteristic-zero deformation ring must still be named separately; constancy of inertia does not prove component equality.

### 5.6 Tate curves as explicit semistable comparison objects

For an elliptic local model, the Tate curve gives a useful calculation. Let $K_v$ be nonarchimedean and take $t\in K_v^\times$ with $0<|t|_v<1$. The Tate curve $C_t$ has split multiplicative reduction and, for $n$ prime to the residue characteristic, an exact sequence

$$
0\longrightarrow\mu_n
\longrightarrow C_t[n]
\longrightarrow\mathbf Z/n\mathbf Z
\longrightarrow0. \tag{5.6}
$$

Its extension class is the Kummer class of $t$ in $K_v^\times/(K_v^\times)^n$. In compatible coordinates the Weil pairing is

$$
e_n((\zeta,a),(\zeta',b))=\frac{(\zeta')^a}{\zeta^b}. \tag{5.7}
$$

Consequently a target local module of Tate-curve shape can be realized by choosing $t$ with the prescribed Kummer class. The valuation $v(t)>0$ gives nonzero monodromy; its reduction modulo the coefficient prime determines whether residual monodromy remains nonzero or drops to zero.

This supplies an honest local point for primitive Steinberg and level-raising situations. It also reveals a compatibility constraint: the same $t$ controls both $\ell$- and $q$-torsion extension classes. Two arbitrarily prescribed upper-triangular modules whose Kummer classes do not arise from one $t$ cannot be realized on the same Tate curve. In the HBAV case the corresponding semiabelian parameter is an $\mathcal O_M$-linear toric extension, and the same shared-parameter warning remains.

For example, suppose the target extension class is represented by $t_\ell\in K_v^\times/(K_v^\times)^\ell$ and the auxiliary class by $t_q\in K_v^\times/(K_v^\times)^q$. A common Tate curve exists precisely when there is $t\in K_v^\times$ mapping to both. Because $\ell$ and $q$ are coprime, the compatibility can be tested in

$$
K_v^\times/(K_v^\times)^{\ell q}. \tag{5.7a}
$$

Compatible classes combine by the Chinese remainder exponents, and a representative of positive valuation gives split multiplicative reduction. Formula (5.7) then verifies the pairing. If the prescribed valuation classes are inconsistent modulo $\ell$ and $q$, the simultaneous local moduli problem is empty.

### 5.7 Why the conditions are open

The generic paired level maps are built into $X$, so they persist everywhere on the twisted moduli space. The additional integral and reduction properties require smaller neighborhoods.

For good reduction, extend the universal object over a local integral chart and take the tube of the chosen smooth special-fiber point. For a finite-flat type at $\ell$ or $q$, use the local-model hypothesis: on an integral neighborhood of $x_v$, the relevant universal kernel is identified with the selected finite locally free model, or every point lies on its named finite-flat component. This constancy is an input from the local deformation calculation, not a general consequence of smoothness of the characteristic-zero variety.

For semistable reduction, use the boundary chart described in Section 5.5. For finite prime-to-residue-characteristic inertia, finite etale local systems are locally constant in the analytic topology. For real signs and orientations, stay inside one connected component of the real manifold.

After intersecting the neighborhoods around the one comparison point, we obtain

$$
\varnothing\ne\Omega_v\subset X(F_v). \tag{5.8}
$$

The proof of nonemptiness is the existence of $x_v$; the proof of openness is the appropriate local integral, etale, boundary, or real-manifold argument. These are separate claims.

At a finite place, choose etale coordinates

$$
U\longrightarrow\mathbf A^g_{F_v}
$$

near $x_v$. After shrinking, prime-to-residue-characteristic finite etale torsion sheaves are constant on a small residue polydisk. If the universal abelian variety extends over the integral chart, points reducing to the same smooth special-fiber point have good reduction. At a residue-characteristic prime, the local-model hypothesis cuts out residue tubes for the named finite-flat component. Selecting the tube through $x_v$ gives a nonempty open. This also explains why one rigid point is not enough: approximation moves the point, and the arithmetic property must survive the movement.

### 5.8 The local nonemptiness ledger

Before proceeding, every place in $S$ must have a completed row in the following ledger.

| Place | Required comparison object | Extra verification |
|---|---|---|
| $v\mid\infty$ | real polarized object on the selected component | odd involutions, orientation, and auxiliary-level descent |
| $v\mid\ell$ | integral object with (5.2) | Cartier pairing, finite-flat component, and actual $\mathfrak q$-torsion |
| $v\mid q$ | integral object with (5.4) | Cartier pairing, finite-flat component, and actual $\lambda$-torsion |
| prescribed good $v$ | smooth integral object | both finite etale Frobenius modules and an integral tube |
| prescribed Steinberg $v$ | named semiabelian or Tate object | nonzero monodromy, sign, toric rank, and boundary open |
| moduli- or level-bad $v$ | point on the actual generic moduli component | every rigidification and a verified analytic neighborhood |

If any row lacks an object, Moret--Bailly cannot repair it. The moduli choices, the auxiliary character, or the local prescription must be changed.

## 6. The arithmetic existence step

The geometric and local work now has a precise reward. A single invocation of the simultaneous totally real Moret--Bailly theorem produces one closed point meeting all local opens and avoiding all residual fixed fields. The theorem chooses the field along with the point; this is why it can succeed when $X(F)$ is empty.

The field-control statements must be read literally. The output is finite and totally real, selected places split completely, and a prescribed finite extension is avoided. It is not automatically Galois, solvable, or of a chosen parity.

### 6.1 The avoidance field

Let $L_\rho/F$ and $L_\sigma/F$ be the finite Galois extensions fixed by $\ker\bar\rho$ and $\ker\bar\sigma$. Let $D/F$ be a finite Galois extension containing:

- $L_\rho L_\sigma$;
- the CM field $K$ used in the dihedral auxiliary construction;
- the finite cyclotomic subextensions needed to preserve the adjoint condition (2.9) at $\ell$ and its $q$-analogue;
- every finite self-twist field whose accidental inclusion could spoil cuspidality or multiplicity one;
- all component and descent fields that the moduli twist must avoid; and
- any additional finite image-detecting fields used by the two lifting arguments.

Taking a Galois compositum is important. For a Galois $D/F$, linear disjointness of $F'$ and $D$ is equivalent to

$$
F'\cap D=F. \tag{6.1}
$$

Using a nonnormal root field in place of $D$ can miss an intersection with its normal closure and fail to preserve an image.

### 6.2 The Moret--Bailly input

We apply the theorem to the smooth geometrically connected quasi-projective variety $X/F$, the finite set $S$, the nonempty opens $\Omega_v$, and the avoidance field $D$. All real places are in $S$. We use the split local form at every $v\in S$, so the intended local algebra is a product of copies of $F_v$.

The hypotheses have now been established in the required order:

1. fineness gives a universal abelian variety rather than a coarse isomorphism class;
2. the Hodge-filtration calculation gives smoothness;
3. product monodromy gives geometric connectedness;
4. the comparison objects give nonempty local opens on that same component;
5. the real opens give an all-embeddings reality condition; and
6. the Hilbert condition after base change to $D$ gives disjointness.

The theorem first moves sufficiently large reduced local cycles in a common presentation, then uses Hilbert irreducibility to make the universal incidence algebra a field. This explains why a collection of local points is not by itself enough and why geometric connectedness cannot be replaced by arithmetic connectedness.

It is worth seeing how the split condition is encoded. Choose a common degree $d$ allowed by the moving-family theorem. In each $\Omega_v$, choose $d$ distinct nearby points. Their unordered sum defines a point of the reduced symmetric locus $Q_d(X)(F_v)$. Above $Q_d(X)$, the incidence scheme is finite etale of degree $d$. Weak approximation moves the local configurations to one global parameter, while a Hilbert condition forces the incidence fiber to be connected. A connected finite etale algebra of rank $d$ is a field, which becomes $F'$. At a split place the local incidence algebra stays $F_v^d$, giving (6.3); at a real place it stays $\mathbf R^d$, forcing every embedding to be real.

Disjointness is another Hilbert condition. After base change of the incidence cover to $D$, require its specialized fiber to remain connected in the way prescribed by the avoidance theorem. Because $X$ is geometrically connected, no constant subfield prevents that condition. This is the geometric point of the hypothesis: if $X$ contained a nontrivial field of constants, every residue field of a point could be forced to meet that constant field.

The construction globalizes all local conditions simultaneously. Applying it once for the $\ell$-adic places and again for the $q$-adic places would produce two unrelated fields and two unrelated moduli points. Taking their compositum would not repair the problem: it could destroy disjointness and would not put both level structures on one abelian variety.

### 6.3 The global point and its field

The conclusion is a closed point $x\in X$ with residue field

$$
F'=\kappa(x) \tag{6.2}
$$

such that:

1. $F'/F$ is finite and totally real;
2. $F'\cap D=F$;
3. every $v\in S$ splits completely in $F'$; and
4. for every $F$-embedding $\iota:F'\hookrightarrow F_v$, the conjugate point $x^\iota$ lies in $\Omega_v$.

Complete splitting means

$$
F'\otimes_FF_v\simeq F_v^{[F':F]}. \tag{6.3}
$$

Thus every place $w\mid v$ has $F'_w=F_v$, and every conjugate local object has the required condition. Obtaining one acceptable $w$ above $v$ would not be enough for the later lifting theorem, which is applied simultaneously at all places above the coefficient prime.

### 6.4 A genuine disjointness lemma

The image-preservation argument is short enough to prove rather than summarize.

**Lemma 6.1 (restriction with disjoint fixed field).** Let

$$
r:G_F\longrightarrow H
$$

have finite image, and let $L/F$ be the finite Galois extension fixed by $\ker r$. If $E/F$ is finite and $E\cap L=F$, then

$$
r(G_E)=r(G_F). \tag{6.4}
$$

**Proof.** The intersection hypothesis and the normality of $L/F$ give

$$
\operatorname{Gal}(EL/E)\xrightarrow{\sim}\operatorname{Gal}(L/F).
$$

The restriction map $G_E\twoheadrightarrow\operatorname{Gal}(EL/E)$ is surjective. Composing it with this isomorphism and the faithful identification of $\operatorname{Gal}(L/F)$ with $r(G_F)$ shows that every element of the original image occurs in $r(G_E)$. The reverse inclusion is immediate. $\square$

Apply the lemma with $E=F'$ and with both residual representations. Their full matrix images, not merely their projective images, are unchanged. Hence absolute irreducibility and adequacy are preserved. Because $D$ also contains the finite cyclotomic and self-twist fields used in the adjoint calculations, the vanishing conditions required by the lifting theorems remain valid as well.

The lemma concerns $F'$, not its Galois closure. Even if $F'\cap D=F$, the normal closure $\widetilde F'$ can meet $D$. Replacing $F'$ by $\widetilde F'$ therefore requires a new disjointness proof.

### 6.5 What is and is not controlled about the field

The basic output has the following exact profile:

$$
\begin{array}{c|c}
\text{property} & \text{conclusion}\\ \hline
\text{finite over }F & \text{yes}\\
\text{totally real} & \text{yes}\\
\text{split at every }v\in S & \text{yes}\\
\text{linearly disjoint from }D & \text{yes}\\
\text{Galois over }F & \text{not asserted}\\
\text{solvable over }F & \text{not asserted}\\
\text{degree of prescribed parity} & \text{not asserted}.
\end{array} \tag{6.5}
$$

An exact degree or degree parity can be added only by supplying compatible local rank-$d$ algebras, an admissible moving-family presentation, and the absence of an index obstruction. The flexible-degree theorem does not silently choose $d$ odd. In particular, parity needed for a quaternion algebra is usually handled by choosing its finite ramification set after $F'$ is known and adding an auxiliary discrete-series place if necessary, rather than by claiming that $[F':F]$ has a convenient parity.

If a disjoint Galois closure is genuinely needed, the moving family must be equipped with the stronger resolvent conditions controlling that closure. Ordinary disjointness of the root field is insufficient. If solvability is genuinely needed, a separate solvable field-construction theorem must be used. Moret--Bailly's conclusion alone supplies neither property.

Passing to the normal closure illustrates all three warnings. The normal closure of a totally real field is again totally real, because it is generated by real conjugates. If a place splits completely in $F'$, it also has trivial decomposition action on the conjugates generated in the local splitting field, so the prescribed split behavior can often persist in the normal closure. But neither fact controls the intersection with $D$. A new subgroup in the Galois closure can meet a residual fixed field even when the root field does not, and the residual image can shrink after the passage.

Likewise, solvability of a further extension $E/F'$ says nothing by itself about solvability of $E/F$. In a tower

$$
F\subset F'\subset E,
$$

the normal closure of $F'/F$ may already have a nonsolvable group. The later modularity argument uses solvable base change only on the upper leg $E/F'$. Statements about descent or base change on the lower leg remain unavailable.

Finally, degree parity and local splitting interact. Requiring one finite place to have a field completion of even local degree forces the global degree to be even, while complete splitting at that place imposes local degree one on every factor but does not determine the number of factors. Exact-degree variants must reconcile these ranks before approximation. The basic split theorem wisely leaves the common degree flexible.

Ramification control is also finite. Any finite list of places at which ramification of $F'/F$ would be harmful is placed in $S$ and forced to split completely, which is stronger than being unramified. More general prescribed unramified local algebras can be used when complete splitting is unnecessary. The theorem does not produce an extension unramified outside a preassigned finite set unless a separate integral construction proves that stronger statement; new ramified primes of $F'/F$ can occur.

This does not make an originally unramified Galois representation ramified after restriction: inertia in $G_{F'_w}$ maps into inertia in $G_{F_v}$. It can, however, alter conductor formulas for already ramified local parameters and complicate automorphic base change. That is why every target-sensitive place is put in the split set, while merely harmless new field ramification is recorded rather than denied.

## 7. The auxiliary abelian variety

The closed point now turns the abstract moduli problem into one geometric object over one arithmetic field. This chapter records exactly what is obtained. The paired torsion identifications and local reduction conditions are conclusions because they were built into the fine moduli problem and the local opens. Automorphy is not yet among the conclusions.

### 7.1 Pulling back the universal family

Pull the universal tuple on $X$ back along

$$
x:\operatorname{Spec}F'\longrightarrow X.
$$

In the elliptic case this gives

$$
(A,\alpha_\ell,\alpha_q,\eta_N)/F'.
$$

In the Hilbert--Blumenthal case it gives

$$
(A,\iota,\lambda_A,\eta_{\mathfrak n},\alpha_\ell,\alpha_q)/F'. \tag{7.1}
$$

Because $X$ is fine, $A$ is defined over $F'$ and the displayed structures are defined over $F'$. No descent obstruction remains. Had we used a coarse point, the corresponding object might have existed only over a gerbe or a further extension.

### 7.2 The two torsion identifications

The moduli interpretation gives isomorphisms of finite group schemes on the characteristic-zero field $F'$ and therefore of Galois modules

$$
\alpha_\ell:
\bar\rho|_{G_{F'}}\otimes_k k_\lambda
\xrightarrow{\sim}A[\lambda], \tag{7.2}
$$

$$
\alpha_q:
\bar\sigma|_{G_{F'}}\otimes_{k_q^{\mathrm{in}}}k_{\mathfrak q}
\xrightarrow{\sim}A[\mathfrak q]. \tag{7.3}
$$

The scalar extensions in (7.2)--(7.3) are shown when the original residue fields were enlarged to match primes of $M$. They preserve rank two. Restriction of scalars would produce a different representation and is not used.

At every $w\mid v\mid\ell$, the integral neighborhood upgrades (7.2) to the chosen isomorphism of finite locally free models over $\mathcal O_{F'_w}=\mathcal O_{F_v}$. The analogous statement holds for (7.3) at places above $q$. At every other $w$ above $S$, the corresponding good, semistable, finite-type, or orientation condition holds.

### 7.3 Duals and determinants

The isomorphisms (7.2)--(7.3) commute with the fixed pairing diagrams. Consequently

$$
\det A[\lambda]=\bar\chi_\ell|_{G_{F'}},
\qquad
\det A[\mathfrak q]=\bar\chi_q|_{G_{F'}}. \tag{7.4}
$$

At the integral and rational Tate-module levels, polarization gives

$$
T_\lambda(A)^\vee\simeq T_\lambda(A)(-1),
\qquad
V_\lambda(A)\simeq V_\lambda(A)^\vee(1), \tag{7.5}
$$

and the same formulas at $\mathfrak q$. Thus

$$
\det V_\lambda(A)=\chi_\ell,
\qquad
\det V_{\mathfrak q}(A)=\chi_q. \tag{7.6}
$$

These equalities use the selected generator of the Hilbert--Blumenthal polarization line. If a nontrivial coefficient or polarization character is retained, it must occur identically in the target pairings, the automorphic central character, and both deformation problems.

### 7.4 Preservation of residual images

By Lemma 6.1 and the choice of $D$,

$$
\bar\rho(G_{F'})=\bar\rho(G_F),
\qquad
\bar\sigma(G_{F'})=\bar\sigma(G_F). \tag{7.7}
$$

It follows that both restrictions remain absolutely irreducible and adequate. Their projective images, scalar subgroups, and endomorphism rings are unchanged. The residual maximal ideals they define are therefore non-Eisenstein.

The statement is stronger than the assertion that $F'$ does not contain the full fixed field. Since the fixed fields are Galois and lie in $D$, equation (6.1) gives genuine linear disjointness. A proper nontrivial intersection would replace the image by the corresponding proper subgroup and could make a dihedral representation reducible.

For the adjoint-twist condition, apply Lemma 6.1 to the joint finite representation

$$
G_F\longrightarrow
\operatorname{GL}(\operatorname{ad}^0\bar\rho)
\times k^\times,
\qquad
g\longmapsto(\operatorname{ad}^0\bar\rho(g),\bar\chi_\ell(g)). \tag{7.7a}
$$

Its fixed field was included in $D$. The joint image after restriction is therefore unchanged, so

$$
H^0(F',\operatorname{ad}^0\bar\rho(1))
=H^0(F,\operatorname{ad}^0\bar\rho(1)). \tag{7.7b}
$$

The same argument applies at $q$. Adequacy is a property of the finite matrix image; equality of that image preserves it verbatim. This is stronger and safer than trying to prove adequacy anew for an unspecified subgroup.

### 7.5 The actual ramification record

At all places above $S$, the reduction and torsion behavior is exactly the prescribed one. Outside $S$, the construction makes no infinite collection of local promises. The abelian variety $A$ has good reduction outside a finite set $B_A$, but $B_A$ is known only after $A$ has been constructed.

There is a useful global semistability safeguard. Choose the neat rigidifying level to contain full level at an integer $N\ge3$, prime to $\ell q$, with descent local system unramified outside $S$, and put all places dividing $N$ in $S$. At $v\notin S$, the specialized full $N$-torsion is unramified. The semistable reduction criterion then implies that $A$ has semistable reduction at every such $v$. In the elliptic case the full $\ell$-torsion already gives the same conclusion away from $\ell$ wherever $\bar\rho$ is unramified. For an HBAV, using the full auxiliary torsion rather than one $\lambda$-factor avoids a gap in the $2g$-dimensional criterion.

Thus one can arrange that every newly discovered bad place outside $S$ is semistable. On each rank-two coefficient factor its inertia is unipotent, so the local representation is unramified or Steinberg-shaped. Its residual Frobenius can still be scalar or vexing, and its monodromy can vanish after reduction. The corresponding enhanced local ring, integral newvector theorem, and component-support statement must therefore still be checked; global semistability does not prove the clean nonvexing hypotheses.

Before applying either lifting theorem, enlarge the finite bookkeeping set to

$$
S_A=S\cup B_A. \tag{7.8}
$$

At every new place in $B_A\setminus S$, compute the actual Weil--Deligne type of each rank-two factor and place it on a named controlled local component. For an elliptic curve, multiplicative reduction gives a Steinberg factor and potentially good additive reduction gives a finite inertia type; the relevant integral type and component theorem must still apply at the lifting prime. For an HBAV, the same audit is made on each $\mathcal O_M$-linear rank-two factor.

Membership of the Galois point in a named local component is only the local half of the clean datum. The automorphic side must also contain the exact lower-face class, saturated primary and companion lattices, flags and pairings, and coherent integral vanishing-cycle comparison required by the selected lifting route. At an extra bad place discovered only after specialization, none of these objects is produced merely by semistability or by the level-raising congruence. This is the unresolved post-specialization cleanability clause isolated in Book 174.

If a new place lies outside the controlled range, one has three honest choices: refine the integral moduli construction so that it cannot occur, pass to a carefully chosen further field where an applicable component theorem holds, or stop. The finite set of bad reduction places cannot be wished away by saying that $A$ is geometric.

## 8. Keeping the known side automorphic

The first lifting theorem needs residual automorphy over $F'$, not merely over $F$. If $F'/F$ were a solvable extension admitting the required base change, one could transport the known form. The Moret--Bailly field is not generally solvable. The dihedral choice was made precisely because it has a second, more robust route: reconstruct automorphic induction over $F'$ itself.

### 8.1 The dihedral route over an arbitrary output field

Recall the CM quadratic field $K/F$ and the character $\bar\theta$. Since $K\subset D$ and $F'\cap D=F$, one has

$$
F'\cap K=F. \tag{8.1}
$$

Therefore $K'=KF'$ is a quadratic totally imaginary extension of the totally real field $F'$. Mackey restriction gives

$$
\left(\operatorname{Ind}_{G_K}^{G_F}\bar\theta\right)|_{G_{F'}}
\simeq
\operatorname{Ind}_{G_{K'}}^{G_{F'}}
\left(\bar\theta|_{G_{K'}}\right). \tag{8.2}
$$

Let $\Theta'$ be the Hecke character of $K'$ obtained from $\Theta$ by norm pullback. Its $q$-adic avatar is $\theta_q|_{G_{K'}}$. Automorphic induction over $K'/F'$ gives

$$
\Pi_0'=\operatorname{AI}_{K'/F'}(\Theta'). \tag{8.3}
$$

The residual representation attached to (8.3) is the right side of (8.2), hence

$$
\bar\rho_{\Pi_0',\mathfrak q}
\simeq\bar\sigma|_{G_{F'}}. \tag{8.4}
$$

Here and only in this displayed shorthand, the fixed embeddings of residual coefficient fields are suppressed. After extension to $k_{\mathfrak q}$, (8.4) is exactly the representation in (9.3).

It is cuspidal. Indeed, (7.7) says that the residual induction remains absolutely irreducible. If $\Theta'$ were conjugation-invariant, its residual induction would split, contradicting that fact. Its infinity type is the pullback of the parallel CM type, so $\Pi_0'$ has parallel weight two. Its determinant remains cyclotomic by restriction of (3.4).

The determinant calculation commutes with this restriction. If $\epsilon_{K'/F'}$ is the quadratic character of $K'/F'$, transfer in the Cartesian compositum square gives

$$
\epsilon_{K'/F'}\,
(\bar\theta|_{G_{K'}}\circ\operatorname{Ver}_{F'}^{K'})
=\bar\chi_q|_{G_{F'}}. \tag{8.4a}
$$

Hence the residual lattice of $\Pi_0'$ lands on the same fixed-pairing component as $A[\mathfrak q]$. Equality only of the two determinant characters would not identify the chosen pairing scalar, but the norm-pulled Hecke character and the pulled polarization coordinate give the required compatible choice.

At a place $w$ of $F'$ above $v$ of $F$, local automorphic induction is computed from the etale quadratic algebra $K'\otimes_{F'}F'_w$. If $w$ lies over a split place and was itself forced to split completely in $F'/F$, the local representation is the same ordered pair of characters used to build the finite-flat comparison object. At inert and ramified places it is the corresponding local induction. Thus residual modularity over $F'$ includes the local type needed to locate the correct non-Eisenstein type module; it is not proved only at unramified Frobenius places.

This proof uses no solvability of $F'/F$. It constructs the automorphic representation anew from a character over the quadratic extension $K'/F'$.

### 8.2 The solvable-base-change route

There is a second route when the known residual source is an arbitrary weight-two cuspidal representation $\pi_0$ over $F$. Suppose, as an additional field hypothesis, that $F'/F$ admits a tower

$$
F=F_0\subset F_1\subset\cdots\subset F_r=F' \tag{8.5}
$$

of cyclic extensions to which the solvable base-change theorem of Book 97 applies. Iterated cyclic base change gives an isobaric representation

$$
\operatorname{BC}_{F'/F}(\pi_0).
$$

At every place its local parameter is the restriction of the parameter of $\pi_0$. The attached Galois representation, where the compatibility theorem applies, is therefore the restriction of $\rho_{\pi_0,q}$.

For the first lifting theorem we need a cuspidal representation. Cuspidality must be checked at each cyclic layer. If the endpoint were a sum of two characters, its $q$-adic representation would be reducible. Under local--global compatibility this contradicts preservation of the absolutely irreducible residual image in (7.7). Equivalently, the stepwise criterion of Book 97 says that no intermediate form may acquire a nontrivial norm-character self-twist.

This route is valid only under the tower hypothesis. A finite extension is not called solvable merely because its degree is a solvable integer, and a non-Galois field does not come with a solvable Galois group unless its normal closure has been analyzed.

### 8.3 Cuspidality and self-twists

At a cyclic step $L/K$, base change of a cusp form fails to be cuspidal precisely when the form is fixed by a nontrivial character in the norm-kernel character group. Such a character is quadratic, and the source is automorphically induced from the corresponding quadratic field. The base change becomes

$$
\xi\boxplus\xi^c. \tag{8.6}
$$

For a longer solvable tower, the test is stepwise. Absence of a bottom-field self-twist is not by itself the full noncyclic criterion. At every layer one either excludes the new self-twist or records the resulting isobaric boundary.

The avoidance field includes the finite fields that detect the chosen residual self-twists. This makes the residual irreducibility test robust. Nevertheless, a characteristic-zero packet can have additional finite-order self-twists invisible in one crude residual calculation. The automorphic block used for lifting must exclude or explicitly carry its finite twist group so that multiplicity and descent fibers remain controlled.

### 8.4 Why a nonsolvable output changes the argument

Suppose Moret--Bailly produces a field whose normal closure has nonsolvable Galois group. Book 97 does not define a general base change of $\pi_0$ to that field. The statement

$$
\bar\sigma|_{G_{F'}}\text{ is modular because }\bar\sigma\text{ is modular}
$$

is then unsupported for a general $\bar\sigma$.

There are exactly three legitimate repairs in the present framework:

1. use the dihedral construction of Section 8.1, which works over $F'$ directly;
2. strengthen the field-construction input so that $F'/F$ lies in the solvable base-change range and then perform the checks of Sections 8.2--8.3; or
3. assume a separate automorphic-restriction theorem for the particular nonsolvable extension.

The default dihedral construction uses the first repair. The theorem package also permits the second only under its explicit tower and cusp hypotheses. It never relabels the Moret--Bailly field as solvable.

## 9. The first modularity-lifting step

We now know that $A[\mathfrak q]$ is the reduction of a parallel-weight-two cuspidal automorphic representation over $F'$. This is the exact residual input for modularity lifting, but it is only the input. The goal of the first lift is to prove automorphy of the particular characteristic-zero representation $V_{\mathfrak q}(A)$.

Every hypothesis is checked over $F'$, the field on which patching is performed. Image preservation, complete splitting at $q$, and the local moduli conditions were designed for this moment.

### 9.1 The auxiliary-adic Tate module

Let $M$ be the real multiplication field and write

$$
r_{A,q}:G_{F'}\longrightarrow
\operatorname{GL}_2(\mathcal O_{M,\mathfrak q}) \tag{9.1}
$$

for the action on $T_{\mathfrak q}(A)$. In the elliptic case $M=\mathbf Q$ and this is the usual $q$-adic Tate module. Polarization gives

$$
\det r_{A,q}=\chi_q. \tag{9.2}
$$

Its reduction is, with the paired identification retained,

$$
\bar r_{A,q}\simeq
\bar\sigma|_{G_{F'}}\otimes_{k_q^{\mathrm{in}}}k_{\mathfrak q}. \tag{9.3}
$$

The representation is continuous, unramified outside the finite set consisting of the places above $q$ and the bad reduction places of $A$, and totally odd. At a real complex conjugation, the polarization and weight-one Hodge structure give eigenvalues $1$ and $-1$.

The target of the first lift is (9.1), not the full $2g$-dimensional rational Tate module. The $\mathcal O_M$-action cuts out a rank-two factor integrally at $\mathfrak q$.

### 9.2 The residual automorphic maximal ideal

Equation (8.4) places (9.3) in the Hecke eigensystem of the cuspidal representation $\Pi_0'$. Absolute irreducibility makes the corresponding maximal ideal non-Eisenstein. It also makes the reduction of a stable lattice independent of the lattice up to isomorphism.

The first lifting theorem needs the residual automorphic system at a level from which the target local components can be reached. At every prime where the residual automorphic source has superfluous level, apply the independent integral level-lowering theorem, including Ihara injectivity, saturation, and component-group control. At every prime where (9.1) has extra level, apply the independent level-raising or type-selection theorem for the exact desired branch. Neither operation is inferred from conductor inequalities.

Let $\mathfrak m_q$ denote the resulting non-Eisenstein weight-two Hecke maximal ideal. The input record includes a cuspidal localized module on which $\mathfrak m_q$ occurs and whose selected local type module is nonzero.

### 9.3 The coefficient-prime local hypotheses

Let $w\mid q$ in $F'$. Since the places above $q$ were in $S$ and split completely,

$$
F'_w=F_v
$$

for the place $v$ below $w$. In particular, $F'_w/\mathbf Q_q$ is unramified whenever the chosen base local field was unramified. The local comparison (5.4) and the good-reduction abelian scheme give compatible finite locally free group schemes

$$
\mathcal A[\mathfrak q^n]/\mathcal O_{F'_w}
$$

whose generic fibers are

$$
T_{\mathfrak q}(A)/\mathfrak q^nT_{\mathfrak q}(A). \tag{9.4}
$$

Thus $r_{A,q}|_{G_{F'_w}}$ is finite flat of type $(0,1)$ in the integral sense. The coefficient action is integral, so the rank-two $\mathfrak q$-factor is a finite-flat kernel rather than a rational projector with a $q$-denominator.

The paired residual model verifies the determinant and duality condition. The residual Schur hypotheses were imposed on $\mathcal H_{v,\mathfrak q}$ after the declared coefficient extension and are unchanged because the local field is unchanged. If the chosen local point is ordinary, the ordinary line and its character order are included; if it is supersingular, no ordinary filtration is invented.

### 9.4 The away-from-the-coefficient-prime hypotheses

At $w\nmid q$, classify the actual local representation (9.1). Good reduction gives an unramified condition. Split or nonsplit multiplicative reduction gives a primitive Steinberg condition with the actual unramified twist and nonzero monodromy. Potentially good reduction gives a finite inertial type when the required local comparison theorem applies. Any ordered tame condition records its two characters and Frobenius lines.

For each nonminimal place, choose a represented local functor and one component containing the point defined by $r_{A,q}|_{G_{F'_w}}$. The residual conductor can be smaller than the characteristic-zero conductor; such a prime is included in the fixed nonminimal set $P_q$. A nonzero monodromy condition is imposed on the generic locus of a closed special component, not as an Artinian “nonvanishing equation.”

At every place newly appearing in $B_A\setminus S$, the calculation of Section 7.5 must yield one of these controlled cases. In addition, the residual automorphic localization, exact lowering or type-selection maps, saturated lattices, and comparison complexes required by the chosen clean chain must be independently constructed there. The construction does not obtain those data from the local Galois classification. The determinant on every local functor is the restriction of $\chi_q$, matching (9.2).

### 9.5 The nonminimal infrastructure ledger

Book 156 separates three independent infrastructure packages. NM-I and NM-II are always required for the general controlled criterion. NM-III has two independent halves: clauses 1--4 belong to the relative determinant route, while clauses 5--6 belong to the component-support route; the sharp balanced route uses neither half. We record both halves below, but an application assumes only the half used by its selected route, together with that route's separate dimension, coverage, reducedness, nilpotent-control, or finiteness hypotheses.

**NM-I: integral level and type control.** The primary automorphic lattice and its adjoint companion must be finite free and perfectly paired at the base, mixed, and Taylor--Wiles levels. Degeneracy maps must satisfy integral Ihara injectivity and saturation; type selection must use saturated lattices rather than a projector with a $q$-divisible denominator. The multi-prime degeneracy/type cube must have an exact saturated total complex, with no unrecorded higher torsion. At every Taylor--Wiles prime the full Iwahori old image, its new quotient, the primary $U$-block, and the companion $V$-block must satisfy the splitness, saturation, vanishing, inverse-diamond duality, and group-algebra freeness clauses of Book 156 before any block is discarded. Module and faithful-order augmentation must both be exact. The selected local component must contain a nonzero characteristic-zero automorphic point, with Eisenstein boundary and unwanted self-twist packets excluded, and the ranks and presentation amplitudes must be uniformly bounded for finite-shadow patching.

**NM-II: integral reciprocity and local compatibility.** The localized Hecke algebra must carry a genuine two-dimensional Galois representation of determinant $\chi_q$. Every Artinian quotient at $w\mid q$ must be finite flat, and at every fixed nonminimal place the family must factor through the same local quotient as (9.1), with ordered characters and generic monodromy treated exactly as in Book 156. At Taylor--Wiles primes inertia must be the tautological diamond character and its inverse, becoming unramified after augmentation. If an inner form intervenes, the faithful integral Hecke orders and their Galois families must be identified before transfer. The Hecke order must be generated by the verified trace, determinant, diamond, and retained local data so that the deformation-to-Hecke map is surjective.

**NM-III: route-specific determinant lines or component support.** For the relative determinant route, the global problem and every local condition must be represented by the complete effective perfect complexes specified in Book 156. Their determinant lines must be identified with those of the primary--companion automorphic comparison complexes, with the stated one-prime factors and every higher $\operatorname{Tor}$ contribution retained. For the support route, the patched module must meet the generic point of every component claimed in the theorem. For a componentwise conclusion, component ideals must be compatible through the finite shadows and their augmentation must equal the independently defined finite component-closure quotient. These clauses are not interchangeable, and the applicable dimension, coverage, reducedness, or nilpotent-control hypotheses remain separate.

In addition, the global conditions are checked:

$$
\bar r_{A,q}\text{ is absolutely irreducible and adequate}, \tag{9.5}
$$

$$
H^0(F',\operatorname{ad}^0\bar r_{A,q}(1))=0, \tag{9.6}
$$

the fixed-determinant global problem is represented, and the applicable full, reduced, or componentwise comparison has its dimension, reducedness, and support hypotheses. Equations (9.5)--(9.6) follow from the original auxiliary checks and image preservation, not from the existence of $A$.

Because $q>2$, absolute irreducibility also gives
$H^0(F',\operatorname{ad}^0\bar r_{A,q})=0$ by Schur's lemma and the trace splitting. Thus both vanishing clauses in the standing Book 156 ledger have been checked.

To see how these inputs meet, let $R_q^P$ be the global fixed-determinant deformation ring for the local datum of $r_{A,q}$, and let $\mathbb T_q^P$ be the faithful localized Hecke order on the selected type module. NM-II constructs a surjection

$$
R_q^P\twoheadrightarrow\mathbb T_q^P. \tag{9.6a}
$$

The Tate module gives an $\mathcal O_{M,\mathfrak q}$-point

$$
x_A:R_q^P\longrightarrow\mathcal O_{M,\mathfrak q}. \tag{9.6b}
$$

NM-I supplies the paired Taylor--Wiles modules and exact augmentation. The selected Book 156 route then supplies the remaining comparison: sharp balance proves faithfulness directly, the support route uses NM-III clauses 5--6 and its independent coverage and nilpotent-control hypotheses, and the relative route uses NM-III clauses 1--4 together with a proved base equality and the numerical finiteness hypotheses. The resulting full, reduced, componentwise, or relative $R=T$ statement makes $x_A$ factor through the Hecke side. If only reduced equality is known, the factorization still holds because the target coefficient ring is a domain and kills nilpotents.

Specializing the Hecke-valued Galois representation at the resulting Hecke character produces a representation $r_{\Pi}$. Its traces and determinants agree with $r_{A,q}$ at all good Frobenius elements. Chebotarev and Brauer--Nesbitt identify their rational representations. Their common residual representation is absolutely irreducible, so the stable-lattice comparison upgrades the identification to the selected integral lattices. This is the mechanism behind the conclusion below; it is not a mere appeal to equal dimensions.

### 9.6 Jacquet--Langlands and component switching

The automorphic module used in NM-I may live on a quaternion algebra. Choose its ramification set so that the number of ramified places, including the real ones, is even and every desired finite ramified component is discrete series. If parity is wrong, add a finite auxiliary discrete-series place with independently controlled level; do not claim a convenient parity for $[F':F]$.

Characteristic-zero Jacquet--Langlands transfers the relevant packets, but NM-II requires more: the localized integral Hecke orders, saturated type lattices, pairings, Galois families, and determinant lines must be identified. Generic packet matching alone does not produce an integral deformation-to-Hecke map.

If the residual source and (9.1) do not initially lie on compatible local components, one may use the solvable switching method of Chapter 12. The local restriction map must send both points to the same named component after an admissible extension. Equality of inertial types after restriction is not enough. The immediate lifting conclusion then lives over the switching field $E$, not over $F'$. One either uses $E$ as the residual potential-modularity endpoint and replaces $F'$ by $E$ throughout the changing-prime step, or performs the full recursive descent of Section 12.5 using the representation $V_{\mathfrak q}(A)$ defined over $F'$. Merely switching components does not justify the $F'$-valued conclusion below.

### 9.7 Automorphy of the auxiliary-adic factor

Assume now that component support is available over $F'$, either directly or after the exact descent just described. All hypotheses of the controlled nonminimal lifting theorem hold for (9.1). Therefore there is a parallel-weight-two cuspidal automorphic representation $\Pi_A$ of $\operatorname{GL}_2(\mathbf A_{F'})$, a place $\widetilde{\mathfrak q}\mid q$ of its coefficient field, and a finite extension $C_q/\mathbf Q_q$ receiving both $M_{\mathfrak q}$ and $E_{\Pi_A,\widetilde{\mathfrak q}}$ such that

$$
V_{\mathfrak q}(A)\otimes_{M_{\mathfrak q}}C_q
\simeq
\rho_{\Pi_A,\widetilde{\mathfrak q}}
\otimes_{E_{\Pi_A,\widetilde{\mathfrak q}}}C_q. \tag{9.7}
$$

The central character is trivial in the cyclotomic-determinant normalization. At every finite place away from $q$ covered by NM-II and the stated local--global compatibility, the local component of $\Pi_A$ has the conductor, inertial type, ordered branch, and monodromy prescribed by the actual local representation of $A$. At places above $q$, the conclusion supplied here is the integral finite-flat Galois identification in (9.7); an automorphic local label there requires a separate $q$-adic local--global compatibility theorem.

This is the first modularity-lifting conclusion. It is stronger than residual modularity of $A[\mathfrak q]$ and weaker than automorphy of every coefficient-prime factor until the next chapter supplies the comparison.

## 10. Moving automorphic information to the target prime

The phrase “an abelian variety is modular” can obscure a coefficient-field issue. Equation (9.7) compares one $q$-adic rank-two factor with one automorphic Galois representation. The $\lambda$-adic factor lives over a different completion. We move between them through algebraic Frobenius polynomials and the Galois representations attached to the same automorphic representation.

This chapter provides the rigorous changing-prime step needed inside the two-prime argument. It is a special compatibility argument for one GL$_2$-type abelian variety and one automorphic representation; it is not the general compatible-system theory developed later.

### 10.1 Frobenius polynomials of a real-multiplication variety

Let $v$ be a finite place of $F'$ at which $A$ has good reduction and whose residue characteristic is different from $\ell q$. The reduction of $A$ has its Frobenius endomorphism commuting with $\mathcal O_M$. In the arithmetic-Frobenius convention fixed in Section 1.3, the corresponding rank-two $M$-linear characteristic polynomial is

$$
P_{A,v}(X)=X^2-a_v(A)X+q_v \in M[X]. \tag{10.1}
$$

The determinant is $q_v$ because of the polarization and the arithmetic-Frobenius convention. The element $a_v(A)\in M$ is the reduced trace of Frobenius. For every finite prime $\nu$ of $M$ away from the residue characteristic of $v$, the characteristic polynomial of arithmetic Frobenius on $V_\nu(A)$ is the image of (10.1) in $M_\nu[X]$.

This independence is geometric. Frobenius is one algebraic endomorphism of the reduction, and the different Tate modules are its different scalar realizations. In the elliptic case $a_v(A)\in\mathbf Z$ and this is the familiar polynomial $X^2-a_v(A)X+q_v$.

If $A$ has extra endomorphisms or the $M$-linear representation decomposes, we use the rank-two factor selected by the fixed embedding $M\hookrightarrow\operatorname{End}^0(A)$. The absolute irreducibility of its residual $\lambda$-factor ensures that the factor relevant to the target is not a sum of characters.

### 10.2 The automorphic coefficient field

Let $E_{\Pi_A}$ be a number field containing the algebraically normalized Hecke eigenvalues of $\Pi_A$. Equation (9.7), in the common field $C_q$, gives, for almost all $v$,

$$
X^2-a_v(\Pi_A)X+q_v
=P_{A,v}(X) \tag{10.2}
$$


after embedding both coefficient fields into $\overline{\mathbf Q}_q$. Since both sides come from algebraic numbers and the embedding is injective, the equality holds in a common number field containing $M$ and $E_{\Pi_A}$. We henceforth replace the coefficient field by that compositum and fix compatible places above $\mathfrak q$ and $\lambda$.

This coefficient enlargement changes neither dimension nor residual image after the declared scalar extension. It does not identify the completions $E_{\Pi_A,\widetilde{\mathfrak q}}$ and $E_{\Pi_A,\widetilde\lambda}$.

The common polynomial will be denoted

$$
P_v(X)=X^2-a_v(\Pi_A)X+q_v
=X^2-a_v(A)X+q_v. \tag{10.3}
$$

### 10.3 The target-adic representation attached to the same form

In its verified geometric range, Book 135 attaches to $\Pi_A$ a continuous cohomological representation at $\widetilde\lambda\mid\ell$. Taking its covariant dual in the convention of Section 1.3 gives

$$
\rho_{\Pi_A,\widetilde\lambda}:
G_{F'}\longrightarrow\operatorname{GL}_2(E_{\Pi_A,\widetilde\lambda}) \tag{10.4}
$$

provided the weight-two Hilbert or quaternionic curve realization and its local compatibility hypotheses are in place. At every good $v\nmid\ell$ outside the automorphic level,

$$
\det(X-\rho_{\Pi_A,\widetilde\lambda}(\operatorname{Frob}_v))=P_v(X). \tag{10.5}
$$

The determinant is $\chi_\ell$, the representation is totally odd, and it has a stable lattice. At places where the chosen geometric realization has established local comparison, its Weil--Deligne parameter agrees with that of $\Pi_{A,v}$.

The curve-realization hypothesis is part of the infrastructure ledger. It is automatic neither from the abstract definition of a cusp form nor from the existence of (9.7). In the intended parallel-weight-two Hilbert setting, one selects a modular or quaternionic Shimura curve realization with the parity and integral-level checks already described.

### 10.4 Chebotarev identifies the target-adic Tate module

Choose a finite extension $C_\lambda/\mathbf Q_\ell$ receiving both $M_\lambda$ and $E_{\Pi_A,\widetilde\lambda}$. After extending scalars to $C_\lambda$, equations (10.1), (10.3), and (10.5) give equality of characteristic polynomials at a density-one set of finite places:

$$
\det\!\left(X-
\left(V_\lambda(A)\otimes_{M_\lambda}C_\lambda\right)
(\operatorname{Frob}_v)\right)
=
\det\!\left(X-
\left(\rho_{\Pi_A,\widetilde\lambda}
\otimes_{E_{\Pi_A,\widetilde\lambda}}C_\lambda\right)
(\operatorname{Frob}_v)\right). \tag{10.6}
$$

Chebotarev density and Brauer--Nesbitt therefore identify their semisimplifications. The reduction of $V_\lambda(A)$ is the declared scalar extension of $\bar\rho|_{G_{F'}}$, which is absolutely irreducible. Hence $V_\lambda(A)$ is irreducible: a characteristic-zero invariant line would reduce, after intersecting a stable lattice and saturating, to a residual invariant line. The automorphic representation is cuspidal and its attached representation has the same irreducible residual representation. Thus semisimplification signs may be removed, and

$$
V_\lambda(A)\otimes_{M_\lambda}C_\lambda
\simeq
\rho_{\Pi_A,\widetilde\lambda}
\otimes_{E_{\Pi_A,\widetilde\lambda}}C_\lambda. \tag{10.7}
$$

Let $\kappa_\lambda$ be the residue field of $C_\lambda$, enlarged finitely if needed to receive the two residual coefficient fields. Choose stable lattices on both sides of (10.7). Their residual semisimplifications become equal after extension to $\kappa_\lambda$. Absolute irreducibility makes all stable-lattice reductions isomorphic, so

$$
A[\lambda]\otimes_{k_\lambda}\kappa_\lambda
\simeq
\bar\rho_{\Pi_A,\widetilde\lambda}
\otimes_{k_{\widetilde\lambda}}\kappa_\lambda
\simeq
\bar\rho|_{G_{F'}}\otimes_k\kappa_\lambda. \tag{10.8}
$$

Equation (10.8) is the residual modularity of the target.

The lattice assertion has a short proof. After scaling an intertwiner between the two rational representations, arrange that one stable lattice $L_1$ lies in the other $L_2$ but not in $\varpi L_2$. The image of $L_1$ in $L_2/\varpi L_2$ is a nonzero Galois-stable subspace. Absolute irreducibility makes it the entire residual space. Nakayama's lemma gives $L_1=L_2$. Thus the rational Chebotarev comparison cannot conceal a different nonsplit residual extension.

The same argument explains why absolute irreducibility was imposed before constructing the moduli space. If the residual semisimplification were a sum of characters, different stable lattices in one rational representation could reduce to different extensions. Equality of Frobenius polynomials would then determine only semisimplification and would not recover the particular torsion module in (7.2).

### 10.5 What changing the prime does not mean

No map has been constructed between $V_{\mathfrak q}(A)$ and $V_\lambda(A)$. Such a map would not even be linear over a common local field. Nor has one taken the matrix entries of (9.7) and embedded them from a $q$-adic field into an $\ell$-adic field.

The valid chain is

$$
V_{\mathfrak q}(A)
\longleftrightarrow
\Pi_A
\longrightarrow
\{P_v(X)\}_v
\longleftrightarrow
V_\lambda(A). \tag{10.9}
$$

Local integral properties at the new coefficient prime do not follow solely from (10.9). Finite flatness of $V_\lambda(A)$ comes from the good-reduction abelian scheme and its integral $\mathcal O_M$-action. Residual adequacy comes from (7.7). Exact local types come from the geometric representation and local--global compatibility, each in its stated range.

## 11. A conditional second lifting step

Under the post-specialization cleanability hypothesis, the first lift and the changing-prime argument have now produced an automorphic lift of $\bar\rho|_{G_{F'}}$, namely $V_\lambda(A)$. This completes the conditional residual theorem. It does not complete the unqualified catalog objective for every target. If an independent characteristic-zero comparison lift $\rho$ as in Section 2.1 has also been supplied, one may ask for a further conclusion. The present chapter records that conclusion only under a second complete clean lifting datum; it is not part of residual potential modularity.

This conditional step is logically independent of the first. Its coefficient prime is $\ell$, its local components are those of $\rho$, and its fixed nonminimal set need not equal the bad reduction set of $A$. Nothing in the residual theorem asserts that these extra hypotheses hold.

### 11.1 Residual modularity of the target

Equation (10.8) supplies a parallel-weight-two cuspidal residual automorphic system over $F'$. Let $\mathfrak m_\ell$ be its non-Eisenstein Hecke maximal ideal. Because

$$
\bar\rho(G_{F'})=\bar\rho(G_F), \tag{11.1}
$$

the residual representation remains absolutely irreducible and adequate, and its adjoint obstruction condition remains the one checked over $F$.

The residual automorphic source need not have the same level as $\rho$. To reach the target datum, use the exact integral level-lowering and level/type-raising theorems of Book 156. At a prime where the residual source and target lie on different components, the component-support hypothesis or the solvable switching method of Chapter 12 is required. Congruence of unramified traces does not choose a component.

### 11.2 The characteristic-zero comparison point

Restrict the original lift:

$$
r=\rho|_{G_{F'}}:
G_{F'}\longrightarrow\operatorname{GL}_2(\mathcal O). \tag{11.2}
$$

Its reduction is $\bar\rho|_{G_{F'}}$. Since every place in the original local set splits completely, for $w\mid v\in S$ one has

$$
r|_{G_{F'_w}}=\rho|_{G_{F_v}} \tag{11.3}
$$

under the chosen identification of local fields. Thus its finite-flat model at $\ell$, its ordinary refinement if present, and every named away-from-$\ell$ component are unchanged.

If the moduli construction enlarged the residual coefficient field from $k$ to $k_\lambda$, enlarge $E$ and $\mathcal O$ correspondingly and replace $r$ by scalar extension. Coefficient base change preserves the finite-flat models and the represented local conditions assumed in the datum. The representation remains rank two over the enlarged coefficient ring, and image adequacy is checked for the resulting scalar realization. No restriction of scalars is used.

The representation $r$ defines a characteristic-zero point of the fixed-determinant global deformation ring for exactly these local conditions. This is the point that must land in the Hecke algebra. The point defined by $V_\lambda(A)$ is used only to prove the residual maximal ideal is automorphic and to seed component support.

### 11.3 Determinant and coefficient-prime checks

Restriction preserves the determinant exactly:

$$
\det r=\chi_\ell|_{G_{F'}}. \tag{11.4}
$$

At every $w\mid\ell$, complete splitting gives an unramified local field $F'_w/\mathbf Q_\ell$ in the clean range. The compatible group schemes attached to the original lattice remain finite flat after base change, so $r|_{G_{F'_w}}$ is finite flat of type $(0,1)$. The named residual Schur hypotheses are identical to those over $F_v$.

Hodge--Tate weights alone would not verify this clause. The finite-flat deformation ring in Book 156 classifies integral torsion systems, and (11.2) is checked against that ring through the supplied models.

Total oddness is preserved because $F'$ is totally real. Every real place of $F'$ lies over a real place of $F$, and the corresponding complex conjugation is conjugate to one for which $\rho$ has determinant $-1$ and trace zero.

### 11.4 Local components away from the target prime

At a place $w\nmid\ell$ above an original prescribed place $v$, equation (11.3) puts $r_w$ on the same represented local component. At all other ramified places of $r$, which are simply the places above the finite ramification set of $\rho$, compute the actual restricted parameter. If the underlying $v$ was not required to split, ramified restriction could change conductor and split an irreducible type; in the main construction all target-sensitive places were included in $S$ precisely to avoid that ambiguity.

The local target record is

$$
\mathcal D_\ell(r)=
\{\text{finite flat at }w\mid\ell;
\ \text{named type and component at }w\nmid\ell\}. \tag{11.5}
$$

At a Steinberg place, the generic point has nonzero monodromy and the sign is the stable-line sign of $r_w$. At a tame principal-series place, the ordered characters are recorded integrally. At a finite-type place, its conductor is computed from the full inertia invariants rather than copied from the residual conductor.

### 11.5 The conditional application of the lifting theorem

Apply the controlled nonminimal lifting theorem over $F'$ to the residual automorphic maximal ideal $\mathfrak m_\ell$ and the point (11.2). Its hypotheses are now accounted for:

1. residual absolute irreducibility, adequacy, $H^0(F',\operatorname{ad}^0\bar\rho)=0$, and the adjoint cyclotomic invariant follow from (11.1), odd characteristic, and the avoidance construction;
2. residual modularity follows from (10.8);
3. determinant and total oddness are (11.4) and Section 11.3;
4. finite flatness and local Schur conditions hold at every $w\mid\ell$;
5. every away-from-$\ell$ place lies on a named controlled component;
6. the residual automorphic source is connected to the target level by independent integral level and type theorems; and
7. the $\ell$-adic versions of NM-I--NM-III, including component support, hold for the selected tuple.

The conclusion is a parallel-weight-two cuspidal automorphic representation $\Pi_\rho$ of $\operatorname{GL}_2(\mathbf A_{F'})$. After choosing a finite extension $C_\rho/\mathbf Q_\ell$ receiving both the target coefficient field $E$ and the relevant completion of $E_{\Pi_\rho}$, one has

$$
\left(\rho|_{G_{F'}}\right)\otimes_E C_\rho
\simeq
\rho_{\Pi_\rho,\widetilde\lambda}
\otimes_{E_{\Pi_\rho,\widetilde\lambda}}C_\rho. \tag{11.6}
$$

Its central character is trivial in the main normalization. At every finite place in the controlled range, its conductor, inertial type, ordered branch, and monodromy are exactly those of $\rho|_{G_{F'}}$.

Equation (11.6) is the characteristic-zero potential-automorphy conclusion. It is not inferred from the fact that $V_\lambda(A)$ is automorphic; it is the output of the second lifting theorem.

### 11.6 The residual stopping point

If the initial datum consists only of $\bar\rho$, there is no representation (11.2) and therefore no second lift to perform. Equations (10.7)--(10.8) still prove that

$$
\bar\rho|_{G_{F'}}
$$

is modular of parallel weight two. This is a complete residual potential-modularity theorem.

It does not assert that every characteristic-zero lift of $\bar\rho|_{G_{F'}}$ is automorphic. Each proposed lift must satisfy a represented determinant condition, the coefficient-prime integral condition, controlled away-from-prime components, and the relevant automorphic-support theorem.

## 12. Solvable switching, inner forms, and descent

The clean route arranges local components before applying Moret--Bailly. In practice, two lifts of the same residual representation can lie on different local components. A solvable totally real extension can sometimes make their restrictions component-compatible. Jacquet--Langlands can place discrete-series components on an automorphic space with better integral geometry. These are powerful repairs, but each has a precise boundary.

The simplest potential-automorphy conclusion stops over the field on which the repaired lifting theorem succeeds. Descent is an additional operation, not part of the repair itself.

### 12.1 A controlled further extension

Let $L=F'$ be the Moret--Bailly field. Suppose a further extension is needed. Choose a finite solvable totally real Galois extension

$$
E/L \tag{12.1}
$$

with a tower of cyclic prime-degree extensions. It is **admissible** for the switching problem if:

1. $E$ is linearly disjoint from the fixed fields of both residual representations and from the auxiliary cyclotomic and self-twist fields;
2. every place above $\ell$ and $q$ has the local behavior required by the two finite-flat theorems; in the clean unramified range this means complete splitting, while a ramified local extension is allowed only with a replacement coefficient-prime theorem valid over that ramified field;
3. at each problematic finite place, the specified local solvable extension sends the two points to one named local component;
4. no uncontrolled ramification is introduced elsewhere;
5. the base changes of the residual automorphic sources remain cuspidal at every cyclic step; and
6. NM-I--NM-III and the curve-realization input are available over each field where they are invoked; and
7. every upward cyclic step is ascent-admissible in the sense of Book 97, and every downward step actually used is descent-admissible with the required base-change, twisting, and arithmetic-realization compatibilities.

Such an extension is not supplied by Moret--Bailly. It is constructed separately, one cyclic layer at a time, with local compatibility and disjointness checked at every stage. The composite $E/F$ need not be Galois or solvable because $L/F$ need not be either. What is claimed is only that $E/L$ has the stated solvable Galois structure.

All representation isomorphisms in this chapter are taken after an explicitly chosen common coefficient extension, as in Sections 9.7 and 11.5. No isomorphism of unlike coefficient completions is being suppressed.

### 12.2 Local component compatibility after restriction

Let $u$ be a place of $L$ and $z\mid u$ a place of $E$. Restriction of local representations induces, with the contravariant ring convention, a map

$$
R_{E_z}^{\square,\mathcal D_z}
\longrightarrow
R_{L_u}^{\square,\mathcal D_u}. \tag{12.2}
$$

Two $L_u$-points become component-compatible over $E_z$ only if their induced $E_z$-points factor through the same named component quotient of the source of (12.2). Equality of restricted inertia characters or Weil--Deligne types does not prove this. Components can meet in the residual fiber and separate in characteristic zero.

A valid proof of compatibility uses one of three inputs: an explicit presentation of the local rings and their restriction map; a flat connectedness theorem whose hypotheses hold for the selected points; or an integral automorphic construction producing a path on that component. If no such input is available, component switching has not been proved.

At coefficient-prime places, finite-flat models base change to finite-flat models, but an ordinary line may cease to be distinguished if its two residual characters become equal. The ordinary component theorem must therefore be rechecked after restriction.

### 12.3 The role of Jacquet--Langlands

Suppose the selected local tuple includes discrete-series places. A quaternion algebra can be ramified at those finite places and at all but one real place, producing a curve whose cohomology realizes the desired weight-two packet. The ramification set must have even cardinality. If it does not, introduce one auxiliary discrete-series place for which residual level raising and later level lowering are both established.

Jacquet--Langlands supplies a bijection of the relevant characteristic-zero packets. For modularity lifting one additionally needs:

- saturated integral type lattices on both inner forms;
- equality of faithful localized Hecke orders, not merely commensurability after inverting the coefficient prime;
- compatible perfect pairings and determinant lines;
- transfer of the Hecke-valued Galois representation with exact local factorization; and
- preservation of the Taylor--Wiles deep-level system.

These are the integral inner-form clauses of NM-I--NM-III. A generic transfer cannot repair a missing component-support theorem.

### 12.4 Stopping over the larger field

Assume the component calculations succeed over $E$. Base change the known automorphic residual source from $L$ to $E$ along the solvable tower, checking cuspidality step by step. Image disjointness preserves adequacy and absolute irreducibility. Apply the appropriate lifting theorem over $E$.

For potential automorphy, it is enough to conclude

$$
\rho|_{G_E}\simeq\rho_{\Pi_E,\lambda} \tag{12.3}
$$

for a parallel-weight-two cuspidal $\Pi_E$. The final potential-modularity field is then $E$, not $L$. It remains finite and totally real over $F$. It is split at the places preserved through the construction and disjoint from the residual fixed fields by hypothesis.

Stopping here avoids every descent ambiguity. There is no reason to descend to $L$, much less to $F$, merely to make the statement look stronger.

### 12.5 Descending one cyclic layer at a time

If automorphy over $L$ is needed, use the fact that the target representation $\rho|_{G_L}$ already exists. Let

$$
L=L_0\subset L_1\subset\cdots\subset L_s=E
$$

be the cyclic tower. The top representation $\Pi_E$ is invariant because its Galois representation is the restriction of one defined over $L$. Under the descent-admissibility and compatibility hypotheses in Section 12.1, cyclic descent gives at least one cusp form $\pi_{s-1}$ over $L_{s-1}$. Its Galois representation and $\rho|_{G_{L_{s-1}}}$ have isomorphic irreducible restrictions to $G_E$.

Clifford theory gives a quotient character $\eta_{s-1}$ such that

$$
\rho_{\pi_{s-1}}
\simeq
\rho|_{G_{L_{s-1}}}\otimes\eta_{s-1}. \tag{12.4}
$$

Twist the automorphic descent by $\eta_{s-1}^{-1}$. This does not change its base change and makes its Galois representation equal to the desired restriction. Repeat at each layer. Determinant equality constrains $\eta_i^2$, while the full local comparison selects its localizations and restores the intended local types.

For a noncyclic solvable group, invariance of the top is not by itself a descent theorem. Arbitrary choices in successive cyclic descent torsors need not be compatible. The extending representation $\rho|_{G_L}$ supplies the coherent character correction at every stage and removes the projective obstruction. Without such an extending representation, one must prove the recursive fixed-point condition on the descent torsors directly.

### 12.6 Why there is no automatic descent to the original field

The preceding descent applies to $E/L$ because that extension was deliberately chosen solvable Galois and because $\rho|_{G_L}$ supplies compatible extension data. The Moret--Bailly extension $L/F$ is usually neither Galois nor solvable. Book 97 therefore does not provide a route from $L$ to $F$.

Even if $L/F$ happens to be solvable, one must verify:

- cuspidality at each upward base-change step;
- invariance and a compatible cyclic descent chain downward;
- the central-character square class;
- the quotient-character ambiguity at every layer;
- exact local type after the correcting twists; and
- irreducibility of the restricted arithmetic representation.

Only then can automorphy descend to $F$. The main potential-modularity theorem makes no such claim.

## 13. The theorem package

We can now state the results without hiding any of the bridge's load-bearing hypotheses. The residual theorem first requires a pre-specialization two-prime realization datum and then a separate verification that the resulting auxiliary Tate module belongs to the clean lifting range. The characteristic-zero theorem adds one particular lift on controlled local components. A separate field-control statement records exactly what the construction says about the extension.

The length of the hypotheses is useful. Each clause identifies either a local point, an image-preservation condition, a residual-automorphy input, or a lifting-theorem input. Together they are the two-prime admissibility conditions of Book 174, unpacked here so that none can be hidden behind the phrase “suitable representation.” Deleting a clause points to a specific logical gap rather than to a vague technicality.

### 13.1 Conditional residual potential modularity

Call a collection

$$
\mathscr R=(F,\ell,q,\bar\rho,\bar\sigma,M,\lambda,\mathfrak q,
X,S,(\Omega_v)_{v\in S},D) \tag{13.1}
$$

a **pre-specialization two-prime realization datum** if it has the following properties.

1. $F$ is totally real; $\ell\ne q$ satisfy $\ell,q\geq7$ and are unramified in $F$ at every place where the clean unramified finite-flat theorem is used.
2. $\bar\rho$ and $\bar\sigma$ are continuous, totally odd, absolutely irreducible rank-two representations in characteristics $\ell$ and $q$, with chosen cyclotomic determinant pairings.
3. Both representations remain absolutely irreducible on the relevant cyclotomic kernels; the resulting images are adequate in characteristic at least seven, and their adjoint cyclotomic invariant groups vanish separately.
4. $\bar\sigma$ is the reduction of a parallel-weight-two cuspidal automorphic representation in the required fixed-determinant and central-character block; in the default construction it is the dihedral induction (3.2) satisfying (3.3)--(3.5) with characteristic-zero cyclotomic determinant.
5. The elliptic or Hilbert--Blumenthal datum has matching coefficient residue fields, a fixed polarization and orientation, a locally compatible neat auxiliary level, and paired frames at $\lambda$ and $\mathfrak q$.
6. The chosen twisted fine space $X$ is smooth, geometrically connected, quasi-projective, positive-dimensional, and carries a universal family. Its connectedness is proved by product monodromy or by an equally explicit component calculation.
7. For every $v\in S$, an actual local comparison object on that same component supplies a nonempty open $\Omega_v$. At $\ell$ and $q$ it has good reduction and the comparison is integral and pairing-preserving; at real and away-from-$\ell q$ semistable places the orientation and boundary data are explicit.
8. The Galois avoidance field $D$ contains the two residual fixed fields and every finite cyclotomic, self-twist, component, and descent field needed to preserve the two lifting problems.
9. The auxiliary full-level descent is unramified outside $S$, so the semistable reduction criterion makes every new bad place of a specialization semistable. The prescribed special place $v_0$, its line and sign, its conductor-one augmentation face, and the coefficient-prime finite-flat comparisons are all built into the local ledger.

Clauses 1--9 allow Books 168--169 to produce a finite totally real Moret--Bailly field $F'/F$ and an abelian variety $A/F'$ with the paired frames (13.2). Call this specialization **lifting-admissible** only if the following additional facts have then been verified.

1. The actual representation $V_{\mathfrak q}(A)$, including every bad place in $B_A\setminus S$, lies in the exact one-prime clean datum of Books 156 and 174, or in a finite clean chain changing one named prime at a time. This includes the conductor-one augmentation component, the residual automorphic lower faces, all coefficient-prime finite-flat quotients, saturated primary and companion lattices, flags, pairings, and integral comparison complexes.
2. Over $F'$, the residual auxiliary source remains cuspidal and modular. This is proved either by the dihedral construction of Section 8.1 or by a genuinely applicable base-change theorem with its stepwise cusp checks.
3. The $q$-adic versions of NM-I and NM-II and the route-specific clauses of NM-III, together with the applicable global dimension, coverage, reducedness, nilpotent-control, and support hypotheses, hold for the component containing the auxiliary Tate module. The resulting packet has the rational Shimura-curve realization required by Book 135.

**Theorem 13.1 (conditional residual potential modularity).** Given a pre-specialization two-prime realization datum, let $F'/F$ and $A/F'$ be a Moret--Bailly specialization furnished by clauses 1--9. Thus $F'/F$ is finite and totally real and $A$ has the paired frames (13.2). If this specialization is lifting-admissible in the preceding sense, then there is a parallel-weight-two cuspidal automorphic representation $\Pi_A$ over $F'$ such that

$$
A[\lambda]\simeq
\bar\rho|_{G_{F'}}\otimes_k k_\lambda,
\qquad
A[\mathfrak q]\simeq
\bar\sigma|_{G_{F'}}
\otimes_{k_q^{\mathrm{in}}}k_{\mathfrak q} \tag{13.2}
$$

as paired modules, and

$$
V_\lambda(A)\otimes_{M_\lambda}C_\lambda
\simeq
\rho_{\Pi_A,\widetilde\lambda}
\otimes_{E_{\Pi_A,\widetilde\lambda}}C_\lambda \tag{13.3}
$$

for a finite common coefficient field $C_\lambda$ as in Section 10.4. In particular, after reduction in its residue field $\kappa_\lambda$,

$$
\bar\rho|_{G_{F'}}\otimes_k\kappa_\lambda
\simeq
\bar\rho_{\Pi_A,\widetilde\lambda}
\otimes_{k_{\widetilde\lambda}}\kappa_\lambda \tag{13.4}
$$

is modular of parallel weight two. The images of $\bar\rho$ and $\bar\sigma$ are unchanged after restriction.

**Proof strategy.** The moduli problem creates one variety carrying two universal torsion frames. Moret--Bailly finds a totally real disjoint point on it. Dihedral induction or valid base change keeps the $q$-residual frame modular. A $q$-adic lifting theorem makes the $\mathfrak q$-adic Tate factor automorphic. Algebraic Frobenius polynomials and the automorphic Galois representation at $\lambda$ identify the $\lambda$-adic Tate factor.

**Proof.** Clauses 5--7 and the theorem of Book 169 give the fine variety and all nonempty local opens. Apply the simultaneous totally real, disjoint theorem of Book 168 using $D$. This produces $F'$ and a point $x\in X(F')$ satisfying Sections 6.2--6.3. Pulling back the universal family gives $A$ and (13.2). Lemma 6.1 and clause 8 preserve both residual images.

Post-specialization clause 2 gives a cuspidal residual automorphic source for $A[\mathfrak q]$. The local integral models and post-specialization clauses 1 and 3 verify every input of the first controlled nonminimal lifting theorem, which gives (9.7). The reduced Frobenius polynomial of $A$ is independent of its coefficient prime, as in (10.1). Comparing it with the Hecke polynomial of $\Pi_A$, constructing $\rho_{\Pi_A,\widetilde\lambda}$, and applying Chebotarev yields (13.3). Reduction gives (13.4). $\square$

The proof does not use a characteristic-zero target at $\ell$. Thus Theorem 13.1 is a genuine residual transfer theorem rather than a disguised special case of the next result. It is nevertheless conditional: the current prerequisite chain does not prove post-specialization clause 1 for every target satisfying only the pre-specialization hypotheses. Extra semistable primes of $A$ are known only after the point is chosen, and no acyclic prior theorem presently constructs all of their exact automorphic lower-face and integral vanishing-cycle data.

### 13.2 Conditional characteristic-zero potential automorphy

Add to (13.1) a characteristic-zero comparison lift $\rho$ as in Section 2.1. Require in addition:

1. every place relevant to the local condition of $\rho$ belongs to the split set $S$;
2. the residual automorphic system (13.4) can be lowered and raised to the precise target datum by the independent integral theorems of Book 156;
3. the $\ell$-adic versions of NM-I--NM-III hold on the component tuple containing $\rho|_{G_{F'}}$; and
4. any required component switching is performed over an admissible further solvable totally real extension, with the resulting field used as the endpoint unless the exact descent hypotheses are verified.

Finally, require that this entire tuple is literally an instance of the one-prime theorem of Book 156: its selected special profile, coefficient-prime hypotheses, residual localization, integral level and type lattices, augmentation, and support statements must all match. The preceding list is bookkeeping for that requirement, not a broader replacement for it.

**Theorem 13.2 (controlled characteristic-zero potential automorphy).** Under these hypotheses, there are a finite totally real extension $F^{\mathrm{pm}}/F$, a parallel-weight-two cuspidal automorphic representation $\Pi_\rho$ of $\operatorname{GL}_2(\mathbf A_{F^{\mathrm{pm}}})$, and a finite extension $C_\rho/\mathbf Q_\ell$ receiving both coefficient completions such that

$$
\left(\rho|_{G_{F^{\mathrm{pm}}}}\right)\otimes_E C_\rho
\simeq
\rho_{\Pi_\rho,\widetilde\lambda}
\otimes_{E_{\Pi_\rho,\widetilde\lambda}}C_\rho. \tag{13.5}
$$

The determinant is cyclotomic, and at every finite place in the controlled range the automorphic local component has the same conductor, inertia type, ordered branch, and monodromy as the restricted target.

One may take $F^{\mathrm{pm}}=F'$ if the target component is already covered over the Moret--Bailly field. If switching is needed, one may take $F^{\mathrm{pm}}=E$ as in (12.1). No assertion is made that $F^{\mathrm{pm}}/F$ is Galois or solvable.

This conditional characteristic-zero theorem is not the catalog endpoint and is not used in the proof of Theorem 13.1. Without its final exact-instance hypothesis, one retains only the conditional residual statement of Theorem 13.1.

**Proof.** Theorem 13.1 gives residual modularity over $F'$. Complete splitting preserves every local field and every named local condition of $\rho$. Image preservation supplies absolute irreducibility, adequacy, and the global adjoint vanishing over $F'$. If the target component is covered there, the second controlled nonminimal lifting theorem gives (13.5) with $F^{\mathrm{pm}}=F'$.

Otherwise choose the admissible $E/F'$ in clause 4. Residual images remain unchanged, solvable base change carries the residual automorphic source upward with stepwise cuspidality, and the local restriction calculation puts the target on a covered component. Apply the lifting theorem over $E$ and stop there. This gives (13.5) with $F^{\mathrm{pm}}=E$. $\square$

The theorem is conditional exactly where Book 156 is conditional: the integral Hilbert or quaternionic level/type control, local Hecke-valued representation, determinant-line comparison, and component support must be established for the selected fields and components.

The logical provenance can be summarized without blurring it:

| Part of the argument | Status in this book |
|---|---|
| fine twisted elliptic or HBAV space, smoothness, product monodromy | imported from Book 169 after its hypotheses are verified here |
| totally real split point with disjoint residue field | imported from Book 168 after the local-open ledger is verified here |
| dihedral automorphic induction | imported from Book 95 and reapplied over $KF'/F'$ |
| cyclic and solvable base change or descent | imported from Book 97 only on the stated towers |
| automorphic Galois representations at each coefficient prime | imported from Book 135 in its curve-realizable range |
| the two nonminimal lifting steps | imported from Book 156 with NM-I--NM-II, the route-specific part of NM-III, and every associated clean or conditional comparison hypothesis |
| assembly of the field, torsion identifications, image lemma, two-prime switching, and theorem conclusion | proved in Chapters 6--13 |

This division matters for variants. Replacing the moduli space changes the first row. Enlarging the Hodge range changes the fifth and sixth rows. Neither alteration follows from the assembly argument alone.

### 13.3 The field-control theorem

Potential modularity is useful only when the auxiliary field retains the local and residual information needed downstream. We isolate that output.

**Theorem 13.3 (field-control package).** In Theorems 13.1--13.2, the basic Moret--Bailly field $F'$ may be chosen so that:

1. $F'/F$ is finite and totally real;
2. every place in the finite prescribed set $S$ splits completely;
3. $F'$ is linearly disjoint from the finite Galois avoidance field $D$;
4. every conjugate of the moduli point at a place of $S$ belongs to the prescribed local open;
5. both residual matrix images are unchanged; and
6. every named local finite-flat, ordinary, good, semistable, orientation, and level condition holds at every place above $S$.

The basic construction does not assert that $F'/F$ is Galois, solvable, or of odd or even degree. It does not assert that the Galois closure is disjoint from $D$. A further switching field $E/F'$ may be chosen solvable Galois when a separate cyclic-tower construction supplies it; then $E$ is still totally real and, in an admissible switch, is required to preserve the residual images, but $E/F$ need not be solvable or Galois.

**Proof.** Clauses 1--4 are the simultaneous split, real, and disjoint conclusions of Book 168 applied in Section 6. Clauses 5--6 follow from Lemma 6.1 and from membership of every conjugate local point in $\Omega_v$. The negative statements are not limitations of the proof's exposition: they are absent from the arithmetic existence theorem. $\square$

If an application requires exact degree parity, it must add an admissible exact-degree moving-family datum. If it requires a disjoint normal closure, it must add the appropriate resolvent Hilbert conditions. These strengthened inputs are compatible only after their local degree and monodromy constraints have been checked together.

### 13.4 The elliptic-curve specialization

Suppose $k=\mathbf F_\ell$ and $k_q^{\mathrm{in}}=\mathbf F_q$, both determinant pairings are cyclotomic, and the simultaneous twisted full-level elliptic moduli curve satisfies all geometric and local hypotheses. Then Theorems 13.1--13.2 can be carried out with an elliptic curve $A/F'$.

In this case

$$
T_\ell(A),\qquad T_q(A)
$$

are the full rank-two Tate modules. At a good place, the common polynomial has integral coefficient

$$
P_{A,v}(X)=X^2-a_v(A)X+q_v,
\qquad a_v(A)\in\mathbf Z. \tag{13.6}
$$

The coefficient-prime transfer of Chapter 10 is especially transparent.

This specialization does not say that every admissible pair of local torsion representations occurs on an elliptic curve. The simultaneous twisted curve can have an empty $F_v$-locus or the wrong geometric component. The HBAV construction is used precisely when the elliptic local realization ledger cannot be completed.

Now let $C/F$ itself be an elliptic curve and take

$$
\rho=T_\ell(C),
\qquad
\bar\rho=C[\ell]. \tag{13.6a}
$$

The Weil pairing gives the determinant and polarization automatically. If $C$ has good reduction at every $v\mid\ell$, its full compatible torsion system is finite flat there. At a multiplicative place $v\nmid\ell$, the Tate-curve sequence puts $T_\ell(C)$ on a Steinberg component. At a potentially good additive place, one must identify the finite inertial type and verify that it belongs to the integral controlled range.

**Corollary 13.4 (elliptic-curve variant).** Suppose $C/F$ admits a prime $\ell$ for which $C[\ell]$ is absolutely irreducible, adequate, totally odd, and satisfies the global adjoint and local Schur hypotheses. Suppose its local representations have the controlled types just described, there is a pre-specialization two-prime realization datum for $C[\ell]$ whose resulting specialization is lifting-admissible, and the full second-lift exact-instance hypotheses of Theorem 13.2 hold for $V_\ell(C)$. Then there exist a finite totally real field $F^{\mathrm{pm}}/F$, a parallel-weight-two cuspidal representation $\Pi$ over $F^{\mathrm{pm}}$, a coefficient place $\widetilde\lambda\mid\ell$ of $\Pi$, and a finite extension $C_\ell/\mathbf Q_\ell$ receiving $E_{\Pi,\widetilde\lambda}$ such that

$$
V_\ell(C)|_{G_{F^{\mathrm{pm}}}}\otimes_{\mathbf Q_\ell}C_\ell
\simeq
\rho_{\Pi,\widetilde\lambda}
\otimes_{E_{\Pi,\widetilde\lambda}}C_\ell
$$

**Proof.** The determinant, pairing, and finite-flat conditions come from the Weil pairing and the good-reduction abelian scheme. The hypotheses place every remaining local factor on a controlled component. Apply Theorem 13.2 to (13.6a). $\square$

The auxiliary curve produced by the moduli argument need not be $C_{F^{\mathrm{pm}}}$. It shares the residual $\ell$-torsion with $C$, and the second lifting theorem transfers residual automorphy to the particular Tate module of $C$. Confusing these two curves would erase the second lift.

### 13.5 Abstract geometric representations

The target need not be the Tate module of an elliptic curve over $F$. The characteristic-zero theorem applies to an abstract representation (2.1) provided it has all of the following concrete properties:

$$
\begin{array}{l}
\det\rho=\chi_\ell,\quad
\rho\text{ is totally odd and finitely ramified},\\
\rho|_{G_{F_v}}\text{ has an integral finite-flat type-}(0,1)
\text{ model for every }v\mid\ell,\\
\bar\rho\text{ is absolutely irreducible and adequate},\\
\rho_v\text{ lies on a named controlled component for every }v\nmid\ell,\\
\text{and the global lifting infrastructure covers that component tuple.}
\end{array} \tag{13.7}
$$

A geometric origin can help verify (13.7), but it is not a substitute for any line. A de Rham representation with weights $\{0,1\}$ may lack the required chosen integral finite-flat lattice. A potentially semistable local representation may lie on a component for which no integral automorphic type theorem is available.

Representations with weights $\{0,k-1\}$ for $k>2$ are outside the main theorem. Their realization and lifting would require higher-weight coefficient systems and a lifting theorem for the corresponding Hodge type. The auxiliary HBAV used here remains a weight-two bridge and cannot change the Hodge type of the target.

### 13.6 Determinants with a finite-order factor

Suppose instead

$$
\det\rho=\psi\chi_\ell
$$

with $\psi$ finite order. The elliptic Weil pairing still has determinant $\chi_\ell$, so this is not the same moduli problem. A clean reduction is available if there is a finite-order character

$$
\eta:G_F\longrightarrow\mathcal O^\times
$$

such that

$$
\eta^2=\psi^{-1}. \tag{13.8}
$$

Then

$$
\rho^\circ=\rho\otimes\eta
$$

has cyclotomic determinant. Apply Theorem 13.2 to $\rho^\circ$, after checking that the twist preserves finite flatness at $\ell$, the named away-from-$\ell$ local components, residual adequacy, and all local pairing data. Twisting the resulting automorphic representation by the Hecke character attached to $\eta^{-1}$ gives automorphy of $\rho$ with central character $\psi$.

If (13.8) has no solution, the datum lies outside the Hilbert--Blumenthal realization treated here. An arbitrary quadratic twist cannot repair the determinant because it changes a rank-two determinant by a square.

## 14. Weight, level, and local type

Potential automorphy is more useful when it remembers the automorphic representation's arithmetic invariants. The lifting theorem identifies the target representation itself, so local--global compatibility recovers more than almost-everywhere Hecke eigenvalues. This chapter records the exact conclusions and their boundaries.

### 14.1 Parallel weight two, determinant, and purity

At every embedding $\tau:F^{\mathrm{pm}}\hookrightarrow\mathbf R$, the target has Hodge type $\{0,1\}$. The automorphic representation $\Pi_\rho$ therefore has parallel cohomological weight two. In the main normalization,

$$
\det\rho_{\Pi_\rho,\lambda}=\chi_\ell,
$$

so the finite central character is trivial. At an unramified finite place $w\nmid\ell$,

$$
\det(X-\rho(\operatorname{Frob}_w))
=X^2-a_w(\Pi_\rho)X+q_w. \tag{14.1}
$$

In the square-twist variant of Section 13.6, the finite central character is $\psi$ and the constant term is $\psi(w)q_w$.

At every good place, both roots of (14.1) have complex absolute value $q_w^{1/2}$. Thus the covariant rank-two system is pure of weight one. This purity is supplied by the geometric weight-two realization in Book 135 and agrees with the Weil bounds for the abelian variety. It is not inferred from the determinant alone: the determinant fixes only the product of the two roots.

The weight conclusion uses the coefficient-prime local theorem, not the word “odd.” Oddness controls the archimedean sign; finite-flat Hodge type controls the cohomological weight. The determinant, purity, and Hodge type are three compatible but logically distinct assertions.

### 14.2 The conductor away from the coefficient prime

For $w\nmid\ell$, let $a_w(\rho)$ be the Artin conductor exponent of the restricted target. In every local regime where NM-II includes full local--global compatibility,

$$
a(\Pi_{\rho,w})=a_w(\rho). \tag{14.2}
$$

Thus the prime-to-$\ell$ conductor ideal is

$$
\mathfrak N^{(\ell)}(\Pi_\rho)
=\prod_{w\nmid\ell}w^{a_w(\rho)}. \tag{14.3}
$$

At an unramified place the exponent is zero. At a primitive Steinberg place it is one, the monodromy is nonzero, and the selected $U_w$ sign agrees with the stable line of $\rho_w$. At a principal-series place, the two ordered characters give the conductor through the sum of their character conductors. At a supercuspidal or finite-type place, (14.2) is asserted only when the corresponding exact local comparison theorem is among the inputs.

Residual conductor and characteristic-zero conductor are not interchangeable. A nonminimal Steinberg place can have $a_w(\bar\rho)=0$ and $a_w(\rho)=1$. This increase is precisely what the nonminimal deformation and congruence factors measure.

### 14.3 Places above the coefficient prime

At $w\mid\ell$, the automorphic representation has parallel weight two and its Galois representation is the integral finite-flat lift (11.2). The conclusion is

$$
T/\varpi^nT
\text{ is the generic fiber of a finite locally free group scheme}
\quad(n\ge1), \tag{14.4}
$$

for the selected stable lattice $T$. If the local datum is ordinary, the chosen filtration and its characters agree with the ordinary automorphic refinement. If it is supersingular finite flat, no ordinary refinement is claimed.

Good reduction at a coefficient-prime place does not mean unramifiedness: the cyclotomic determinant is ramified. Nor does (14.4) by itself identify an arbitrary crystalline Frobenius or a stronger potentially semistable type not included in the local theorem.

### 14.4 The final local--global record

Let

$$
\iota_\rho:E\hookrightarrow C_\rho,
\qquad
\iota_\Pi:E_{\Pi_\rho,\widetilde\lambda}\hookrightarrow C_\rho
$$

be the two coefficient embeddings used in (13.5). The useful output is the tuple

$$
\mathscr A(\rho,F^{\mathrm{pm}})=
\left(
F^{\mathrm{pm}},\Pi_\rho,E_{\Pi_\rho},\widetilde\lambda,
C_\rho,\iota_\rho,\iota_\Pi,
\{P_w(X)\}_{w\notin\Sigma},
\det\rho,
\mathfrak N^{(\ell)},
\{\mathrm{WD}_w,N_w,\mathcal C_w\}_{w\in\Sigma}
\right), \tag{14.5}
$$

where $\Sigma$ is the finite exceptional set and $\mathcal C_w$ is the named integral component. The record includes:

- the exact field and its splitting and disjointness properties;
- the parallel weight and central character;
- common algebraic Frobenius polynomials at good places;
- the exact prime-to-$\ell$ conductor in the established local range;
- finite-flat or ordinary data at $\ell$;
- monodromy and signs at Steinberg places; and
- every coefficient-field embedding used to compare realizations.

Later changing-prime arguments may use the polynomials in (14.5), but must recompute residual irreducibility, finite flatness at the new coefficient prime, and the set of nonminimal conductor drops.

## 15. Hostile diagnostics

The two-prime argument is short only after its infrastructure has been assembled correctly. Its most dangerous gaps are plausible statements that are locally or categorically false. We now run explicit failure diagnostics. Each one identifies the exact step at which the proof stops and the kind of repair that is legitimate.

### 15.1 A pairing obstruction

Let $V$ be an absolutely irreducible two-dimensional $k[G_F]$-module with determinant $\bar\chi_\ell$. Fix two Galois-equivariant alternating identifications

$$
\delta,\delta':\bigwedge^2V\xrightarrow{\sim}k(1),
\qquad
\delta'=u\delta. \tag{15.1}
$$

By Schur's lemma, every Galois automorphism of $V$ is scalar. A scalar $a$ changes the pairing by $a^2$. If $u\notin(k^\times)^2$, no Galois-equivariant automorphism carries $\delta$ to $\delta'$. Therefore two abstractly isomorphic torsion modules can belong to different symplectic frame torsors.

Suppose a local elliptic curve $C_v$ realizes $V$ abstractly but its Weil pairing corresponds to $\delta'$, while the global twist was defined using $\delta$. Then $C_v$ gives no point on the selected $X(F_v)$. The local open is empty. One may change the global pairing coordinate before all local data are fixed, replace the local comparison object, or enlarge the moduli problem to the correct union of components and redo geometric connectedness. One may not ignore the square class.

### 15.2 An empty local moduli problem

At $v\mid\ell$, suppose $V|_{G_{F_v}}$ is wildly ramified and admits no finite locally free model of the rank and pairing required by the fixed Hilbert--Blumenthal datum. An abelian scheme with good reduction has finite locally free $\lambda$-torsion, so it cannot realize this module. Thus the proposed good-reduction open is empty even if the generic twisted moduli space has points over $\overline F_v$.

A second form of emptiness occurs when the target and auxiliary prime-to-residue-characteristic Frobenius modules cannot occur on one local abelian variety. Choosing bases does not change Frobenius eigenvalues. A third occurs at a real place when a constant auxiliary frame asks complex conjugation to act trivially while the polarized torsion factor has eigenvalues $1$ and $-1$.

The diagnostic is always the same: write down the actual local object with every level and pairing. If it cannot be written down, change the local condition or the moduli datum before invoking Moret--Bailly.

### 15.3 A local-component mismatch

Let a residual representation in a ramified or enhanced coefficient-prime problem admit two characteristic-zero lifts with the same determinant and the same Hodge--Tate weights, one ordinary and one nonordinary. They can lie on different irreducible components of that refined potentially finite-flat deformation space. Suppose $V_\lambda(A)$ lies on the ordinary component while the target $\rho_v$ lies on the nonordinary component. The diagnostic concerns a ramified problem or an added refinement; it is not a claim about the full clean unramified finite-flat component.

Residual modularity furnished by $A[\lambda]$ does not put automorphic support on the target component. Equality of residual modules and equality of Hodge type do not connect the points. The second lifting argument stops at its component-support clause.

A valid repair proves that the automorphic module meets both components, constructs a congruent automorphic point on the target component, or passes to a solvable local extension for which the restrictions factor through one named component and verifies the map (12.2). Merely saying that both lifts are potentially finite flat is not a repair.

### 15.4 Residual image lost under restriction

Let

$$
\bar r=\operatorname{Ind}_{G_K}^{G_F}\bar\theta
$$

be an irreducible dihedral representation. If an output field $L$ contains $K$, then

$$
\bar r|_{G_L}
\simeq
\bar\theta|_{G_L}\oplus\bar\theta^c|_{G_L}. \tag{15.2}
$$

Absolute irreducibility, adequacy, and the non-Eisenstein Hecke block are all lost at once. The first lifting theorem cannot be applied.

Avoiding only some unrelated auxiliary field does not help. The Galois fixed field of $\ker\bar r$ must lie in $D$, and the output field must be linearly disjoint from it. Lemma 6.1 then proves equality of images. If one later passes to a Galois closure or another extension, the proof must be repeated for that field.

### 15.5 A self-twist and noncuspidal base change

Let $L/K$ be quadratic with norm character $\eta$, and suppose

$$
\pi\simeq\pi\otimes\eta.
$$

Then $\pi$ is automorphically induced from a character $\xi$ of $L$, and

$$
\operatorname{BC}_{L/K}(\pi)=\xi\boxplus\xi^c. \tag{15.3}
$$

The endpoint is not cuspidal. Its Galois parameter is reducible, so it cannot seed the absolutely irreducible non-Eisenstein lifting theorem used here.

In a solvable tower the first such failure can occur at an intermediate quadratic step even if no bottom-field character was initially noticed. The cure is a stepwise cusp check. In the default dihedral route, one induces anew from the CM quadratic compositum and proves noninvariance from preserved residual irreducibility.

### 15.6 A nonsolvable Moret--Bailly field

Suppose the residue field $F'$ of the moduli point has normal closure with Galois group $S_5$. This is compatible with Moret--Bailly's theorem. There is no solvable tower to which Book 97 can be applied, so an arbitrary modular residual representation over $F$ is not known from that theorem to remain modular over $F'$.

The proof stops before the first lift. Calling $F'$ “controlled” does not change its Galois group. The repairs are those of Section 8.4: choose a dihedral known side and re-induce over $KF'/F'$, impose a genuinely solvable field construction, or import a nonsolvable base-change theorem. The main argument takes the first route.

### 15.7 A premature identification of coefficient primes

Suppose (9.7) is known. It is tempting to write

$$
V_\lambda(A)=V_{\mathfrak q}(A)\otimes_{M_{\mathfrak q}}M_\lambda.
$$

There is no such tensor product: $M_\lambda$ is not naturally an $M_{\mathfrak q}$-algebra when $\lambda$ and $\mathfrak q$ have different residue characteristics. The displayed expression is meaningless.

The correct replacement is Chapter 10. One extracts $a_v(A)\in M$, identifies it with the algebraic Hecke eigenvalue, constructs the $\lambda$-adic Galois representation attached to the same automorphic form, and invokes Chebotarev. This route also exposes the necessary curve-realization and local--global compatibility hypotheses.

## 16. The exported potential-modularity record

Potential modularity is not an endpoint in isolation. Its main use is to place one representation inside an automorphic arithmetic family over a controlled field, after which compatible systems, Brauer induction, changing prime, and arithmetic classification can operate. The handoff must therefore include the field and local ledgers, not just the sentence “the representation is potentially modular.”

### 16.1 The compatible-system interface

The automorphic representation $\Pi_\rho$ supplies a number field $E_{\Pi_\rho}$ and algebraic polynomials

$$
P_w(X)=X^2-a_w(\Pi_\rho)X+\psi(w)q_w \tag{16.1}
$$

at all good places. These representations may then be organized into a compatible system once the required independence statements have been proved. The input from this book is:

1. the exact automorphic representation and coefficient field;
2. the determinant character $\psi\chi$;
3. the finite ramification and conductor set;
4. the established Weil--Deligne and monodromy data at bad places;
5. the polarization; and
6. the identity (13.5) with the original target after restriction.

The compatible-system construction must still prove its own independence statements. The one-prime comparison of Chapter 10 is enough for the two-prime bridge but is not a substitute for that general theory.

### 16.2 The descent and changing-prime interfaces

Any later Brauer-induction argument needs the precise field profile from Theorem 13.3. Since the basic field need not be solvable or Galois, it cannot be fed directly into a solvable descent statement. One instead works with separately prescribed Galois closures and solvable subgroups, rechecking intersections with residual fixed fields.

A later change of coefficient prime may use the common polynomials (16.1), but it must freshly verify:

$$
\bar\rho_{\lambda'}\text{ is absolutely irreducible and adequate}, \tag{16.2}
$$

$$
\rho_{\lambda'}\text{ has the required integral condition at }w\mid\lambda', \tag{16.3}
$$

and every conductor drop after reduction lies on a controlled local component. The nonminimal set can change with the coefficient prime.

### 16.3 The arithmetic interface

For later arithmetic applications, export the following checklist.

- **Field:** $F^{\mathrm{pm}}$ is finite totally real over $F$, with the exact split places and avoidance intersections recorded. Its Galois and solvability status is stated truthfully.
- **Representation:** in the residual theorem, the restricted residual target is identified with the reduction of a named parallel-weight-two cuspidal packet; only under Theorem 13.2 is a specified characteristic-zero target itself identified with the packet's coefficient-adic representation.
- **Determinant:** the cyclotomic or finite-character-times-cyclotomic determinant is exact.
- **Residual image:** the full residual matrix image after restriction is recorded, together with adequacy and adjoint vanishing.
- **Local coefficient-prime condition:** the integral finite-flat or ordinary model is named at every place above the coefficient prime.
- **Away-from-prime type:** conductor, inertia, monodromy, signs, and integral component labels are recorded.
- **Frobenius data:** the common algebraic polynomials at good places are fixed in one coefficient field.
- **Descent status:** no descent to $F$ is asserted unless the complete recursive descent and twist correction has been carried out.

For an elliptic-curve application, good reduction at the lifting prime and semistable reduction away from it often make the local record particularly simple. They do not remove the need to prove residual irreducibility, residual modularity, or integral level control.

For a Frey representation, separate arithmetic work must verify that the chosen residual representation and every multiplicative or additive prime fit the target datum of Section 2. Potential modularity supplies an automorphic realization over the potential-modularity field; it does not by itself prove rational-isogeny alternatives, discriminant bounds, or descent of the resulting form to the original field.

### 16.4 Dependency and conclusion audit

The dependency row for this book consists exactly of Books 95, 97, 135, 156, 168, 169, and 174. Their roles do not overlap.

| Prerequisite | Hypotheses retained here | Conclusion used here |
|---|---|---|
| Book 95 | CM quadratic extension, compatible ray-unit data, type $(1,0)$, the quadratic determinant factor, and a surviving conjugate-ratio witness | cuspidal weight-two automorphic induction and its residual dihedral representation |
| Book 97 | an exhibited ascent-admissible cyclic tower, stepwise cuspidality, compatible local parameters, and, for descent, a representation extending to the lower field | only the stated solvable base change or recursive descent; never base change across an arbitrary point field |
| Book 135 | a noncharacter parallel-weight-two packet in the Shimura-curve-realizable range | the covariant dual rational Galois realizations, common good Frobenius polynomials, determinant, oddness, purity, and existence of stable lattices; the exact comparison with $A[\lambda]$ is proved here |
| Book 156 | residue characteristic at least seven, cyclotomic irreducibility, adjoint vanishing, unramified finite-flat coefficient-prime data, the signed special place, NM-I--NM-II, and the hypotheses of the selected sharp, support, componentwise, or relative route | the clean selected lifting conclusion, or a conditional controlled conclusion only after its route-specific hypotheses; the conductor-one augmentation face is used only through the verified universal equality |
| Book 168 | a smooth geometrically connected variety, nonempty local opens, all real places, exact local cycles, and a finite avoidance extension | a finite totally real point field, complete splitting at selected places, and root-field linear disjointness; no Galois or solvable conclusion |
| Book 169 | good Hilbert--Blumenthal primes, ordered polarization, neat level, determinant-compatible paired frames, one arithmetic component, simultaneous local seeds, and full product monodromy | a smooth geometrically connected fine two-prime twist with a universal abelian variety; no global point or automorphy |
| Book 174 | the complete two-prime admissibility ledger, including the dihedral seed, simultaneous coefficient realization, signed level raising, local package, field ledger, and post-specialization cleanability clause | the controlled seed theorem, signed residual localization, clean augmentation interface, cross-prime comparison pattern, and the exact conditional characteristic-at-least-seven boundary |

The conditional final residual theorem of Book 174 is not invoked to prove Theorem 13.1. The proof uses its constituent auxiliary and lifting interfaces and then performs the moduli specialization, automorphy transfer, coefficient change, and lattice comparison explicitly. Its unresolved post-specialization cleanability clause is retained verbatim, so the dependency is neither circular nor stronger than the prerequisite.

This ledger resolves the principal failure modes.

- The Moret--Bailly field $F'$ is finite, totally real, split at the selected places, and disjoint from the chosen finite Galois avoidance field. Its normal closure is not claimed disjoint, Galois with a prescribed group, or solvable unless a separate refined datum supplies those properties.
- The moduli point is an $F'$-point of one fine geometrically connected paired-frame component. It therefore gives an actual abelian variety and exact equivariant torsion frames, rather than a coarse geometric isomorphism class or two unrelated local realizations.
- The two primes are used asymmetrically. At $q$ the dihedral member supplies residual automorphy and the clean lifting theorem applies. At $\ell$ the prescribed residual member is recovered from the same abelian variety after changing coefficient prime through algebraic Frobenius polynomials.
- Residual automorphy survives an arbitrary ordinary point field only because the known member is induced anew from the norm-pulled CM character. General solvable base change is not substituted at this step.
- Every coefficient enlargement is an extension of scalars in rank two. No completion at $q$ is tensored with a completion at $\ell$, and restriction of scalars is never used to disguise a dimension change.
- Determinants are fixed before the moduli space is formed. The quadratic sign in induction, the inverse-different polarization line, the covariant dual convention, and the finite central character all agree.
- Purity is the weight-one purity supplied by the geometric weight-two realization. It is not inferred from determinant or oddness.
- Exact residual comparison uses the rational packet realization, common algebraic Frobenius polynomials, the Tate lattice, and absolute irreducibility. Book 135 alone would canonically determine only a residual semisimplification without its own integral datum; here the comparison with $T_\lambda(A)$ makes every stable lattice homothetic and recovers the exact target module without assuming cross-carrier integral independence.
- Solvable descent is available only along a separately exhibited cyclic tower with compatible local data and coherent quotient-character corrections. Nothing descends across the ordinary Moret--Bailly extension merely because its degree happens to be a solvable integer.

The exact conditional conclusion currently proved is therefore

$$
\ell\geq7,\qquad
\bar\rho\text{ two-prime admissible}
\quad\Longrightarrow\quad
\exists F'/F\text{ finite totally real},\ \exists\Pi/F'
$$

with $\Pi$ cuspidal of parallel weight two and

$$
\bar\rho|_{G_{F'}}\otimes_k\kappa
\simeq
\bar\rho_{\Pi,\lambda}\otimes_{k_\lambda}\kappa
$$

for one finite common residue field $\kappa$. No unrestricted theorem for all odd residual representations, no characteristic-five theorem, and no descent to $F$ is contained in this statement.

This does not yet complete the unqualified catalog objective for every residual target in the stated range. That stronger conclusion requires an acyclic prior theorem constructing the exact clean automorphic and integral data at every uncontrolled extra semistable prime of the specialized auxiliary abelian variety.

### 16.5 Final synthesis

The two-prime method succeeds because it assigns one task to each piece of structure. The target residual representation determines a twisted symplectic level. The auxiliary residual representation supplies a known automorphic seed. A fine elliptic or Hilbert--Blumenthal moduli space places both levels on one geometric object. Its pairing components enforce the determinant; its Hodge deformation theory gives smoothness; its product monodromy gives geometric connectedness; and explicit local comparison objects give nonempty opens.

Moret--Bailly then chooses one closed point whose residue field is totally real, split at every sensitive place, and disjoint from every residual fixed field. The universal family at that point has the two torsion representations with their pairings intact. Disjointness preserves absolute irreducibility and adequacy. The known side remains modular either because a dihedral character can be induced anew over the output field or because a genuinely applicable solvable base change has passed every cuspidality check.

The one lifting theorem needed for the conditional residual result proves automorphy of the auxiliary-adic Tate factor. The real-multiplication Frobenius endomorphisms produce algebraic polynomials independent of coefficient prime, and the Galois representations attached to the resulting automorphic representation identify the target-adic Tate factor. This makes the target residual representation modular. A separate characteristic-zero comparison lift can be treated only under the second complete clean datum isolated in Chapter 11.

No final shortcut remains hidden. A torsion isomorphism respects the Weil pairing. A local open contains an actual point. A residual image is preserved by a proved disjointness statement. A residual automorphic representation becomes a characteristic-zero automorphic lift only through a lifting theorem. One coefficient prime communicates with another only through algebraic Frobenius polynomials and local--global compatibility. A solvable component switch is checked on local rings, and a descent is performed one cyclic layer at a time with its character ambiguity corrected. The auxiliary field is called Galois, solvable, or parity-controlled only when a separate construction has made it so.

When the post-specialization cleanability hypothesis is verified, the resulting record is exact: a controlled finite totally real field, a parallel-weight-two cuspidal automorphic representation, an identification of its residual covariant realization with the prescribed target after restriction, and a complete ledger of determinants, residual images, local types, purity, coefficient extensions, and field intersections. That is the strongest conditional residual potential-modularity statement justified by the stated prerequisites.
