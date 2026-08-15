# Deep-Level Quaternionic Modules and Diamond Actions

## Contents

1. [The deep-level problem](#1-the-deep-level-problem)
   - [What must be constructed](#11-what-must-be-constructed)
   - [Standing arithmetic data](#12-standing-arithmetic-data)
   - [The four kinds of compatibility](#13-the-four-kinds-of-compatibility)
2. [Exact quaternionic modules](#2-exact-quaternionic-modules)
   - [Finite class groupoids](#21-finite-class-groupoids)
   - [Weights and central characters](#22-weights-and-central-characters)
   - [A stabilizer formula](#23-a-stabilizer-formula)
   - [Integral dual modules](#24-integral-dual-modules)
3. [Local deep level](#3-local-deep-level)
   - [The oriented subgroup](#31-the-oriented-subgroup)
   - [Exact $\ell$-power quotients](#32-exact-ell-power-quotients)
   - [The local tower](#33-the-local-tower)
   - [Central and ineffective diamonds](#34-central-and-ineffective-diamonds)
4. [The global diamond tower](#4-the-global-diamond-tower)
   - [Auxiliary data of depth $N$](#41-auxiliary-data-of-depth-n)
   - [Global levels and quotient groups](#42-global-levels-and-quotient-groups)
   - [The action on class sets](#43-the-action-on-class-sets)
   - [The clean stabilizer condition](#44-the-clean-stabilizer-condition)
5. [Torsors of class groupoids](#5-torsors-of-class-groupoids)
   - [The fiber calculation](#51-the-fiber-calculation)
   - [Freeness of the effective action](#52-freeness-of-the-effective-action)
   - [Stabilizers at the two levels](#53-stabilizers-at-the-two-levels)
   - [What fails without cleanliness](#54-what-fails-without-cleanliness)
6. [Finite group rings](#6-finite-group-rings)
   - [Augmentation and inversion](#61-augmentation-and-inversion)
   - [The regular module](#62-the-regular-module)
   - [Coinvariants, invariants, and norm](#63-coinvariants-invariants-and-norm)
   - [Locality of $\mathcal O[\Delta]$](#64-locality-of-mathcal-odelta)
7. [Group-ring freeness](#7-group-ring-freeness)
   - [Functions on a torsor](#71-functions-on-a-torsor)
   - [The weighted theorem](#72-the-weighted-theorem)
   - [Rank and base change](#73-rank-and-base-change)
   - [Hecke-local summands](#74-hecke-local-summands)
8. [Exact augmentation](#8-exact-augmentation)
   - [Orbit sum rather than pullback](#81-orbit-sum-rather-than-pullback)
   - [The augmentation theorem](#82-the-augmentation-theorem)
   - [Invariants and the norm square](#83-invariants-and-the-norm-square)
   - [Coefficient reduction](#84-coefficient-reduction)
9. [Hecke and diamond operators](#9-hecke-and-diamond-operators)
   - [Right-translation normalization](#91-right-translation-normalization)
   - [Commutation away from the auxiliary set](#92-commutation-away-from-the-auxiliary-set)
   - [The oriented operator and diamonds](#93-the-oriented-operator-and-diamonds)
   - [Acting algebras and faithful images](#94-acting-algebras-and-faithful-images)
10. [Primary localization](#10-primary-localization)
    - [Residual factors](#101-residual-factors)
    - [A common finite Hecke algebra](#102-a-common-finite-hecke-algebra)
    - [Primary deep-level modules](#103-primary-deep-level-modules)
    - [Freeness and exact augmentation after localization](#104-freeness-and-exact-augmentation-after-localization)
11. [Refinements at an auxiliary prime](#11-refinements-at-an-auxiliary-prime)
    - [The unnormalized polynomial](#111-the-unnormalized-polynomial)
    - [Two distinct residual roots](#112-two-distinct-residual-roots)
    - [The old companion matrix](#113-the-old-companion-matrix)
    - [Primary and second-root branches](#114-primary-and-second-root-branches)
12. [Duality and the companion module](#12-duality-and-the-companion-module)
    - [Adjoint maximal ideals](#121-adjoint-maximal-ideals)
    - [The companion is not an informal copy](#122-the-companion-is-not-an-informal-copy)
    - [Perfect primary--companion duality](#123-perfect-primary--companion-duality)
    - [The root description of the companion](#124-the-root-description-of-the-companion)
13. [The group-ring-valued pairing](#13-the-group-ring-valued-pairing)
    - [Construction from a coefficient pairing](#131-construction-from-a-coefficient-pairing)
    - [Sesquilinearity](#132-sesquilinearity)
    - [Perfectness](#133-perfectness)
    - [Augmentation of the pairing](#134-augmentation-of-the-pairing)
14. [Transitions in a fixed tower](#14-transitions-in-a-fixed-tower)
    - [Quotient maps of diamond groups](#141-quotient-maps-of-diamond-groups)
    - [Trace and pullback](#142-trace-and-pullback)
    - [Exact base change](#143-exact-base-change)
    - [Transitivity, Hecke action, and pairings](#144-transitivity-hecke-action-and-pairings)
15. [The complete finite-level package](#15-the-complete-finite-level-package)
    - [Definition of a clean Taylor--Wiles datum](#151-definition-of-a-clean-taylor--wiles-datum)
    - [The construction theorem](#152-the-construction-theorem)
    - [Proof of the theorem](#153-proof-of-the-theorem)
    - [Independence of auxiliary choices](#154-independence-of-auxiliary-choices)
16. [Passage to minimal level](#16-passage-to-minimal-level)
    - [Why augmentation stops at oriented level](#161-why-augmentation-stops-at-oriented-level)
    - [The two degeneracy maps](#162-the-two-degeneracy-maps)
    - [A precise control criterion](#163-a-precise-control-criterion)
    - [Exact minimal-level augmentation](#164-exact-minimal-level-augmentation)
17. [Saturation and exceptional congruences](#17-saturation-and-exceptional-congruences)
    - [Saturation is an additional theorem](#171-saturation-is-an-additional-theorem)
    - [The Gram determinant](#172-the-gram-determinant)
    - [The cases $q\equiv1$ and $q\equiv-1$](#173-the-cases-qequiv1-and-qequiv-1)
    - [Small residue characteristics and stabilizers](#174-small-residue-characteristics-and-stabilizers)
18. [Compatible presentations without false transitions](#18-compatible-presentations-without-false-transitions)
    - [Unrelated auxiliary sets](#181-unrelated-auxiliary-sets)
    - [The common power-series source](#182-the-common-power-series-source)
    - [What presentation compatibility proves](#183-what-presentation-compatibility-proves)
    - [What it does not prove](#184-what-it-does-not-prove)
19. [Calculations and diagnostic examples](#19-calculations-and-diagnostic-examples)
    - [One diamond variable](#191-one-diamond-variable)
    - [A central-kernel failure](#192-a-central-kernel-failure)
    - [A nonfree stabilizer fiber](#193-a-nonfree-stabilizer-fiber)
    - [A primary--companion calculation](#194-a-primary--companion-calculation)
20. [Paired definite Taylor--Wiles modules](#20-paired-definite-taylor--wiles-modules)
    - [Two coefficient systems on one class groupoid](#201-two-coefficient-systems-on-one-class-groupoid)
    - [The intrinsic common residual module](#202-the-intrinsic-common-residual-module)
    - [Synchronized freeness and positive rank](#203-synchronized-freeness-and-positive-rank)
    - [Coinvariants, saturation, and minimal control](#204-coinvariants-saturation-and-minimal-control)
    - [Hecke operators, pairings, and partial frames](#205-hecke-operators-pairings-and-partial-frames)
    - [The paired definite module theorem](#206-the-paired-definite-module-theorem)
    - [Recovered actions and the saturation boundary](#207-recovered-actions-and-the-saturation-boundary)
    - [Three indispensable failure tests](#208-three-indispensable-failure-tests)
21. [Final synthesis](#21-final-synthesis)
    - [The structural theorem in compressed form](#211-the-structural-theorem-in-compressed-form)
    - [A dependency-closed proof chain](#212-a-dependency-closed-proof-chain)
    - [Normalization conventions](#213-normalization-conventions)

## 1. The deep-level problem

### 1.1 What must be constructed

Taylor--Wiles level is useful only when its extra symmetry is visible integrally. At a finite auxiliary set one wants a module carrying an action of a finite abelian $\ell$-group $\Delta$, and one wants much more than an action. The module must be free over the group ring $\mathcal O[\Delta]$; killing the augmentation ideal must recover the chosen lower-level module exactly; Hecke operators must commute with diamonds; duality must pair the chosen primary factor with the correct companion factor; and all these structures must agree as one moves through a genuinely nested tower.

Each adjective matters. A module can be free over $\mathcal O$ and fail to be projective over $\mathcal O[\Delta]$. Invariants can agree with lower level while coinvariants do not. A nonprojectivized residue quotient can collapse against the fixed center, and a projective nominal diamond group can still have arithmetic isotropy. Two auxiliary prime sets of the same cardinality can have isomorphic abstract group rings without admitting any map of arithmetic levels. The purpose of this book is to isolate exact hypotheses that prevent these failures and to prove the complete finite-level package from them.

The construction is quaternionic and finite. Because the quaternion algebra is totally definite, automorphic forms are functions on finite class groupoids. Deep-level freeness will therefore come from a torsor theorem, not from a dimension count. This gives a proof that remains valid with nontrivial algebraic weights and central character, provided stabilizers and the effective diamond quotient are treated correctly.

### 1.2 Standing arithmetic data

Fix the following data throughout.

- $F$ is a totally real field.
- $D/F$ is a quaternion algebra ramified at every real place.
- $\ell$ is a rational prime.
- $\mathcal O$ is a complete discrete valuation ring with uniformizer $\varpi$, fraction field $E$, and residue field $k$ of characteristic $\ell$.
- $W$ is a finite free $\mathcal O$-lattice in the chosen algebraic representation, with action $\rho$ of $D^\times$ through its archimedean components. The finite compact-open level acts trivially on $W$.
- $\chi_f:F_f^\times\to\mathcal O^\times$ is a finite-adelic central character compatible with the algebraic weight and trivial on the central part of every chosen compact-open level.

The last condition includes two different requirements. For $a\in F^\times$, the finite character and the algebraic central action must agree so that the transformation law is consistent. For $z\in U\cap F_f^\times$, one must have $\chi_f(z)=1$; otherwise right invariance by $U$ contradicts the central transformation law. A finite type lattice would require its own central compatibility and invariant-lattice theorem. It is not silently included in the present coefficient system.

We write $D_f^\times=(D\otimes_F\mathbb A_{F,f})^\times$. All level actions and double cosets use right translation. At a split unramified place $v$, the spherical polynomial is normalized as

$$
1-T_vX+q_vS_vX^2,
$$

where $q_v$ is the residue-field cardinality. No normalized factor of $q_v^{1/2}$ is inserted. At oriented level the forward operator is denoted $U_v$; its adjoint is generally a different operator.

### 1.3 The four kinds of compatibility

The argument will repeatedly distinguish four maps that are easy to conflate.

First, subgroup inclusion gives pullback from lower level to higher level. Second, finite fibers give orbit sum, or trace, from higher level to lower level. Third, the quotient $\Delta_m\twoheadrightarrow\Delta_n$ gives a ring map $\mathcal O[\Delta_m]\to\mathcal O[\Delta_n]$. Fourth, a chosen presentation of several abstract group rings gives maps from a common power-series ring.

Only the first three arise from a nested arithmetic tower. The fourth is algebraic bookkeeping and need not come from maps of class sets. This distinction will be built into every transition theorem.

## 2. Exact quaternionic modules

### 2.1 Finite class groupoids

Let $Z_f=F_f^\times$ be the finite adelic center. With a fixed central character, the relevant class groupoid has object set

$$
X_U^\chi=D^\times\backslash D_f^\times/(UZ_f),
$$

where the quotient by $Z_f$ carries the coefficient line on which $z$ acts through $\chi_f(z)$. This set is finite. Choose representatives $g_1,\ldots,g_h\in D_f^\times$. Their arithmetic stabilizers are the groups of transformations

$$
\widetilde\Gamma_i
=\{(\gamma,u,z)\in D^\times\times U\times Z_f:
\gamma g_iuz=g_i\},
$$

modulo the evident central redundancies. The groupoid language records the character line rather than treating the quotient as an unweighted set.

Finiteness follows from total definiteness. Modulo the center, $D^\times$ is anisotropic over $F$, so its adelic quotient is compact; quotienting by the open image of $U$ gives a finite set. This is the sole global compactness input needed below.

The groupoid language is not decoration. Deepening the level can make the map of underlying class sets look like a $\Delta$-cover while stabilizers still identify points inside a fiber. Group-ring freeness depends on the groupoid fiber being a genuine torsor after the ineffective central subgroup has been removed.

### 2.2 Weights and central characters

Define the exact integral quaternionic module by the convention

$$
M(U;W,\chi_f)
=\left\{f:D_f^\times\longrightarrow W:
f(\gamma guz)=\chi_f(z)\rho(\gamma)f(g)
\right\},
$$

where $\gamma\in D^\times$, $u\in U$, and $z\in F_f^\times$, embedded centrally. The central compatibility condition is

$$
\rho(a)=\chi_f(a_f)\quad(a\in F^\times),
$$

so the two ways of moving a rational scalar give the same value. If a finite central element belongs to $U$, the assumption $\chi_f|_{U\cap F_f^\times}=1$ gives the same consistency. The formula with $z=1$ is

$$
f(\gamma gu)=\rho(\gamma)f(g).
$$

The word exact means that this is the chosen integral lattice itself. Reduction $M(U;W,\chi_f)/\varpi$ need not equal a module newly formed over $k$ when stabilizer orders are divisible by $\ell$.

Evaluation at the representatives gives an injective map

$$
M(U;W,\chi_f)\longrightarrow\bigoplus_{i=1}^h W.
$$

Its image is cut out by the stabilizer equations. In particular the module is finite and $\mathcal O$-torsion-free, hence finite free. This conclusion does not require invariant formation to commute with reduction.

### 2.3 A stabilizer formula

For each representative $g_i$, let $W_i\subseteq W$ be the submodule cut out by every element of $\widetilde\Gamma_i$, written as a stabilizer presentation

$$
\gamma g_i u z=g_i,
\qquad
\gamma\in D^\times,\quad u\in U,\quad z\in F_f^\times.
$$

Explicitly,

$$
W_i=
\{w\in W:\chi_f(z)\rho(\gamma)w=w
\text{ for every such }(\gamma,u,z)\}.
$$

**Proposition 2.1.** There is a natural $\mathcal O$-module isomorphism

$$
M(U;W,\chi_f)\cong\bigoplus_{i=1}^h W_i.
$$

**Proof.** Evaluation sends a form to $(f(g_i))_i$. Every relation $\gamma g_iuz=g_i$ and the transformation law say precisely that $f(g_i)\in W_i$. Thus evaluation lands in the displayed direct sum.

Conversely, choose $w_i\in W_i$. Define

$$
f(\gamma g_iuz)=\chi_f(z)\rho(\gamma)w_i.
$$

If the same element has two presentations, their ratio is a stabilizer presentation of $g_i$, and the defining equation for $W_i$ makes the two values equal. Hence $f$ is well defined and satisfies the transformation law. The two constructions are inverse. $\square$

This formula explains both the strength and the limitation of the finite-set model. It proves coefficient freeness because every $W_i$ is a torsion-free submodule of $W$. It does not prove uniform rank under change of level: the groups $\Gamma_i$, and therefore the invariant lattices $W_i$, can change.

### 2.4 Integral dual modules

Let $W^\vee=\operatorname{Hom}_{\mathcal O}(W,\mathcal O)$ with contragredient action, and replace $\chi_f$ by $\chi_f^{-1}$. The dual automorphic module is

$$
M^\vee(U)=M(U;W^\vee,\chi_f^{-1}).
$$

There is a coefficient pairing $W\times W^\vee\to\mathcal O$. Summing it over class representatives gives a pairing of automorphic modules. To obtain a perfect integral pairing one must choose weights on orbits so that every stabilizer denominator is a unit, or work at a level with trivial effective stabilizers. We make this a stated hypothesis when duality is used:

$$
(\mathrm{PD})_U:\qquad
M(U;W,\chi_f)\times M^\vee(U)\longrightarrow\mathcal O
\text{ is perfect.}
$$

It is false in general that a mass pairing with factors $|\Gamma_i|^{-1}$ is integral. Under effective neatness, all $\Gamma_i$ are central and already removed, so the unweighted finite sum is perfect. If stabilizer orders are prime to $\ell$, the inverse orders are units in $\mathcal O$, and the usual weighted sum is also perfect.

## 3. Local deep level

### 3.1 The oriented subgroup

Let $v\nmid\ell$ be a finite place at which $D$ is split, and fix once and for all an identification

$$
D_v^\times\cong\mathrm{GL}_2(F_v).
$$

Let $\mathcal O_v$ be the integers, $\mathfrak p_v$ the maximal ideal, and $k_v$ the residue field. The oriented, or Iwahori, subgroup is

$$
K_0(v)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\mathrm{GL}_2(\mathcal O_v):c\in\mathfrak p_v
\right\}.
$$

There are two superficially similar residue quotients, and the central-character convention decides which one is usable. Lower-right reduction alone is the quotient used for ordinary $K_1$-level before a central character is fixed. On a fixed-central-character module it is scalar: the class of $\operatorname{diag}(1,d)$ differs from the scalar $dI$ by an element whose lower-right entry is one. It therefore cannot act faithfully, much less make a nonzero module free over its group ring.

The Taylor--Wiles quotient with fixed determinant is instead projective. Reduction modulo $\mathfrak p_v$ makes both diagonal entries nonzero, and we define

$$
\nu_v^{\mathrm{proj}}:K_0(v)\longrightarrow k_v^\times,
\qquad
\nu_v^{\mathrm{proj}}
\begin{pmatrix}a&b\\c&d\end{pmatrix}
=\bar d\,\bar a^{-1}.
$$

It is a surjective homomorphism. Modulo $\mathfrak p_v$, products of upper-triangular matrices multiply their two diagonal entries separately, so the ratios multiply; surjectivity follows from $\operatorname{diag}(1,d)$. Most importantly,

$$
\nu_v^{\mathrm{proj}}(zI)=1.
$$

Thus the quotient survives passage to the projective class groupoid and records the one independent tame character left after the determinant, hence the central character, has been fixed. At the auxiliary places under consideration the fixed determinant is unramified, so on residue units an ordered pair has the form $(\theta,\theta^{-1})$. Its character on $\operatorname{diag}(1,d)$ is $\theta^{-1}(d)$; the projective ratio therefore matches the inverse tame coordinate. Choosing the inverse ratio instead matches $\theta$ and merely inverts every diamond label, but it must be accompanied by the same change in reciprocity and pairing conventions.

### 3.2 Exact $\ell$-power quotients

Write $a_v=v_\ell(q_v-1)$. Since $k_v^\times$ is cyclic, its largest $\ell$-power quotient has order $\ell^{a_v}$. For $0\le n\le a_v$, let $\Delta_v(n)$ be its quotient of exact order $\ell^n$. Equivalently,

$$
\Delta_v(n)=k_v^\times/(k_v^\times)^{\ell^n}
$$

when $\ell^n\mid q_v-1$. Define

$$
K_1(v,n)=\ker\bigl(K_0(v)\xrightarrow{\nu_v^{\mathrm{proj}}}k_v^\times
\twoheadrightarrow\Delta_v(n)\bigr).
$$

Then $K_1(v,n)\triangleleft K_0(v)$ and

$$
K_0(v)/K_1(v,n)\cong\Delta_v(n)\cong\mathbb Z/\ell^n\mathbb Z.
$$

This is the exact-level convention. The group has order $\ell^n$, not merely order dividing $\ell^n$, and the level is the kernel of the chosen quotient rather than the kernel of all of $k_v^\times$.

### 3.3 The local tower

For $m\ge n$, the natural quotient $\Delta_v(m)\twoheadrightarrow\Delta_v(n)$ gives

$$
K_1(v,m)\subseteq K_1(v,n)\subseteq K_0(v).
$$

The quotient of the two deep subgroups is canonically the kernel of the group quotient:

$$
K_1(v,n)/K_1(v,m)
\cong\ker\bigl(\Delta_v(m)\to\Delta_v(n)\bigr).
$$

**Proof.** Both subgroups are inverse images under the same surjection $K_0(v)\to\Delta_v(m)$. The subgroup $K_1(v,n)$ is the inverse image of the kernel of $\Delta_v(m)\to\Delta_v(n)$, while $K_1(v,m)$ is the inverse image of the identity. The first isomorphism theorem gives the claim. $\square$

Thus a fixed prime with $a_v\ge N$ supplies a genuine tower through depth $N$. It does not supply levels deeper than $a_v$. To let $N$ grow without bound, one generally changes the auxiliary primes, and those changed prime sets are not nested.

### 3.4 Central and ineffective diamonds

The projective quotient removes the local center at the source: every scalar matrix has ratio one. This is not an optional cosmetic improvement. For the lower-right quotient, every residue class has a scalar representative, so after fixing a central character the whole putative diamond group acts through scalars. Twisting and then dividing by that scalar kernel would leave the trivial group, not the $\ell^n$-element group needed for Taylor--Wiles patching.

Projectivizing does not by itself remove global arithmetic isotropy. A noncentral element of $D^\times$ can still identify two lifts of a class, and its image in the projective residue quotient can stabilize a point. Let the **effective diamond group** be the quotient of the nominal group by the kernel of its action on the weighted class groupoid, meaning on both objects and coefficient lines. The torsor theorem will require more: every point stabilizer, not just the common kernel, must be trivial.

If the common kernel is nontrivial, the module cannot be free of positive rank over the nominal group ring. Indeed, if $1\ne\delta$ acts trivially, then $(\delta-1)M=0$, whereas multiplication by $\delta-1$ is nonzero on a free regular module. If a nonidentity diamond acts by a scalar $u\in\mathcal O^\times$, then $([\delta]-u)M=0$ gives the same obstruction. Every freeness theorem below therefore uses the effective group and separately states when the projective nominal action is fully effective.

## 4. The global diamond tower

### 4.1 Auxiliary data of depth $N$

Fix a finite set $Q$ of finite places and an integer $N\ge1$. We call $(Q,N)$ admissible for deep level if:

1. every $v\in Q$ lies outside the coefficient and ramification sets;
2. $D$ is split at every $v\in Q$;
3. the tame level away from $Q$ is hyperspecial at every $v\in Q$;
4. $q_v\equiv1\pmod{\ell^N}$ for every $v\in Q$;
5. compatible splittings $D_v^\times\cong\mathrm{GL}_2(F_v)$ and generators of the exact quotients have been fixed.

Write $q=|Q|$. The nominal group at depth $n\le N$ is

$$
\Delta_{Q,n}^{\mathrm{nom}}
=\prod_{v\in Q}\Delta_v(n)
\cong(\mathbb Z/\ell^n\mathbb Z)^q.
$$

The congruence condition is used only to guarantee the exact quotient. It does not itself imply freeness, perfectness, or minimal-level control.

### 4.2 Global levels and quotient groups

Let $U^Q\subset(D\otimes_F\mathbb A_{F,f}^Q)^\times$ be the fixed level away from $Q$. Set

$$
U_0(Q)=U^Q\prod_{v\in Q}K_0(v),
\qquad
U_n(Q)=U^Q\prod_{v\in Q}K_1(v,n).
$$

Then $U_n(Q)\triangleleft U_0(Q)$, with nominal quotient $\Delta_{Q,n}^{\mathrm{nom}}$. Let $C_{Q,n}$ be the kernel of its action on the class groupoid with central character, and define

$$
\Delta_{Q,n}=\Delta_{Q,n}^{\mathrm{nom}}/C_{Q,n}.
$$

The datum has **full effective diamond rank** when $C_{Q,n}=1$ for every $n\le N$. In that case

$$
\Delta_{Q,n}\cong(\mathbb Z/\ell^n\mathbb Z)^q.
$$

One must not infer full effective rank from the abstract local quotient. Projectivization has removed local scalar classes, but global arithmetic stabilizers can still make the action ineffective.

### 4.3 The action on class sets

Because $U_n(Q)$ is normal in $U_0(Q)$, right multiplication defines an action of $U_0(Q)/U_n(Q)$ on

$$
X_n^\chi=D^\times\backslash D_f^\times/(U_n(Q)Z_f).
$$

The quotient map

$$
\pi_{n,0}:X_n^\chi\longrightarrow X_0^\chi
\quad\text{with}\quad
X_0^\chi=D^\times\backslash D_f^\times/(U_0(Q)Z_f)
$$

is constant on diamond orbits. It is surjective because every double coset at level $U_0(Q)$ has the same representative at level $U_n(Q)$.

Surjectivity and orbit transitivity are formal; freeness is not. If $[g]\delta=[g]$, then there are $\gamma\in D^\times$, $u_n\in U_n(Q)$, and $z\in Z_f$ such that

$$
\gamma g\tilde\delta=gu_nz,
$$

where $\tilde\delta\in U_0(Q)$ represents $\delta$. Thus the extended stabilizer represented by $g^{-1}\gamma gz^{-1}\in U_0(Q)$ maps to $\delta^{-1}$ in the quotient. After projectivization, the remaining arithmetic stabilizers measure exactly the failure of free action.

### 4.4 The clean stabilizer condition

For $g\in D_f^\times$, let the extended stabilizer be

$$
\Gamma_0^\chi(g)
=\{(\gamma,u,z):\gamma gu z=g,
\gamma\in D^\times,\ u\in U_0(Q),\ z\in Z_f\},
$$

modulo central redundancies acting identically on the character line. Projection of the $U_0(Q)$-component through the projective quotient gives a map from $\Gamma_0^\chi(g)$ to the nominal diamond group. Call its image $I_n(g)$.

The datum is **clean through depth $N$** if:

1. $I_n(g)=1$ for every $g$ and every $n\le N$;
2. the stabilizer coefficient lattice at a lift of $[g]$ is the same as at $[g]$;
3. the effective diamond group has full rank;
4. the lower-level module and its dual satisfy the perfect-duality condition.

The projective quotient kills central stabilizers before this test. Item 1 concerns the remaining projective arithmetic stabilizers; item 2 records that their action on the algebraic coefficient line imposes no new equation at deep level. Item 1 already forces the common kernel $C_{Q,n}$ to be trivial; item 3 records the resulting exact numerical rank explicitly because that rank is used later in the power-series presentation.

In the present coefficient convention, the finite auxiliary level acts trivially on $W$, so item 2 follows from item 1: equality of the deep and oriented stabilizers gives literally the same equations on $W$. It remains in the definition because it is the exact coefficient hypothesis used by the proof and prevents an undeclared finite type from being inserted later.

A useful sufficient condition is that every effective projective arithmetic stabilizer has order prime to $\ell$. Its image in the $\ell$-group $\Delta_{Q,n}^{\mathrm{nom}}$ is then trivial.

Here is a practical version of the criterion. Let $\overline\Gamma_0(g)$ denote the effective projective image of $\Gamma_0^\chi(g)$. Suppose it is finite of order prime to $\ell$ for every class. Then the datum is clean on objects. Indeed, the stabilizer image is a quotient of $\overline\Gamma_0(g)$ and also a subgroup of an $\ell$-group. Its order divides both a number prime to $\ell$ and a power of $\ell$, so it is one.

The coefficient conclusion uses the standing trivial finite-level action. With a nontrivial auxiliary type, the kernel of the quotient can change type invariants, and the comparison would require an additional prior theorem not used here.

Cleanliness is stable under decreasing the depth. If the stabilizer image is trivial in $\Delta_{Q,N}$, its image in every quotient $\Delta_{Q,n}$ is trivial. Thus it is enough to verify the group-theoretic part at the deepest level, provided the effective quotients themselves have been chosen compatibly.

## 5. Torsors of class groupoids

### 5.1 The fiber calculation

We now turn the clean stabilizer condition into the geometric statement needed for algebra. Fix a class $[g]_0\in X_0^\chi$. Every point above it has the form $[g\tilde\delta]_n$ with $\delta\in\Delta_{Q,n}^{\mathrm{nom}}$. Hence the nominal diamond group acts transitively on the fiber.

Two such points are equal precisely when

$$
[g\tilde\delta]_n=[g\tilde\delta']_n.
$$

This holds if and only if there are $\gamma\in D^\times$, $u_n\in U_n(Q)$, and $z\in Z_f$ satisfying

$$
\gamma g\tilde\delta=g\tilde\delta'u_nz.
$$

After moving the central factor, one sees that $g^{-1}\gamma gz^{-1}\in U_0(Q)$ and that its image in the projective quotient is $\delta'\delta^{-1}$. Therefore the stabilizer of any point of the fiber is exactly the image $I_n(g)$.

This calculation is the essential arithmetic step. It replaces a misleading count of double cosets by an exact description of the isotropy group.

### 5.2 Freeness of the effective action

**Theorem 5.1 (diamond torsor theorem).** Suppose the datum is clean through depth $N$. For each $0\le n\le N$, the map

$$
\pi_{n,0}:X_n^\chi\longrightarrow X_0^\chi
$$

is a $\Delta_{Q,n}$-torsor. Thus every fiber has exactly $|\Delta_{Q,n}|$ points, and the diamond action on each fiber is simply transitive.

**Proof.** Surjectivity was proved in Section 4.3, and the action is transitive on each fiber by the representative calculation of Section 5.1. If $\delta$ fixes $[g]_n$, the same calculation realizes $\delta$ as the projective image of an arithmetic stabilizer. Cleanliness makes that image trivial, so $\delta=1$. A transitive free action is simply transitive. $\square$

When full effective rank holds, each fiber has $\ell^{nq}$ elements. This numerical consequence comes after the freeness proof; it cannot replace it.

### 5.3 Stabilizers at the two levels

Choose a lift $g\tilde\delta$ of $g$. The deep extended stabilizer is

$$
\Gamma_n^\chi(g\tilde\delta)
=\{(\gamma,u,z):\gamma g\tilde\delta u z=g\tilde\delta,
u\in U_n(Q)\}.
$$

Since $U_n(Q)\triangleleft U_0(Q)$, conjugating the $U_n(Q)$-component by $\tilde\delta$ does not change the group. Thus, after the same central identifications,

$$
\Gamma_n^\chi(g\tilde\delta)=\Gamma_n^\chi(g).
$$

It is a subgroup of $\Gamma_0^\chi(g)$. Under cleanliness, every element of $\Gamma_0^\chi(g)$ has trivial image in the quotient, so its $U_0(Q)$-component lies in $U_n(Q)$. Therefore

$$
\Gamma_n^\chi(g\tilde\delta)=\Gamma_0^\chi(g).
$$

This equality proves that the coefficient lattice $W_g$ is constant across every fiber. In particular, algebraic weights do not disturb the regular representation once the clean condition holds.

### 5.4 What fails without cleanliness

Suppose instead that a subgroup $H\subseteq\Delta_{Q,n}^{\mathrm{nom}}$ stabilizes a point. Its fiber is then a copy of $H\backslash\Delta_{Q,n}^{\mathrm{nom}}$, not a copy of the group. Functions on that fiber form a permutation module induced from the trivial $H$-module. If $H\ne1$ is an $\ell$-group, this permutation module is not free over $\mathcal O[\Delta_{Q,n}^{\mathrm{nom}}]$: its $\mathcal O$-rank is $|\Delta|/|H|$, not divisible by $|\Delta|$.

A projective arithmetic stabilizer of order prime to $\ell$ has trivial image in the diamond $\ell$-group, but it can still act nontrivially on the algebraic coefficient lattice. The fiber may then be a genuine torsor carrying the invariant lattice $W_i$ rather than all of $W$. The freeness proof remains valid when that same $W_i$ occurs at both levels, while coefficient reduction and perfect duality require their own invariant-lattice checks. The order of the point stabilizer $H\subseteq\Delta_{Q,n}^{\mathrm{nom}}$ itself, by contrast, is necessarily an $\ell$-power.

## 6. Finite group rings

### 6.1 Augmentation and inversion

Let $\Delta$ be a finite abelian $\ell$-group and set

$$
\Lambda=\mathcal O[\Delta].
$$

The augmentation is

$$
\epsilon:\Lambda\longrightarrow\mathcal O,
\qquad
\epsilon\left(\sum_{\delta}a_\delta[\delta]\right)=\sum_\delta a_\delta.
$$

Its kernel $\mathfrak a$ is generated by $[\delta]-1$ for $\delta\in\Delta$. The inversion involution is

$$
\iota:\Lambda\longrightarrow\Lambda,
\qquad
\iota([\delta])=[\delta^{-1}].
$$

For a left $\Lambda$-module $P$, the coinvariants are

$$
P_\Delta=P/\mathfrak aP
\cong\mathcal O\otimes_{\Lambda,\epsilon}P,
$$

and the invariants are $P^\Delta=\{x:[\delta]x=x\}$.

### 6.2 The regular module

The regular module $\Lambda$ has $\mathcal O$-basis $[\delta]$. Its coinvariants are free of rank one, generated by the common class of all basis elements. Its invariants are also free of rank one, generated by the norm element

$$
N_\Delta=\sum_{\delta\in\Delta}[\delta].
$$

**Lemma 6.1.** If $x=\sum a_\delta[\delta]\in\Lambda$ is invariant under left multiplication, all coefficients $a_\delta$ are equal. Hence $\Lambda^\Delta=\mathcal O N_\Delta$.

**Proof.** The coefficient of $[\eta]$ in $[\gamma]x$ is $a_{\gamma^{-1}\eta}$. Equality with $x$ for all $\gamma,\eta$ gives $a_{\gamma^{-1}\eta}=a_\eta$, so every coefficient equals $a_1$. The converse is immediate. $\square$

The augmentation of $N_\Delta$ is $|\Delta|$, usually a nonunit. Thus augmentation restricted to invariants is not the isomorphism between invariants and coinvariants.

### 6.3 Coinvariants, invariants, and norm

The norm map

$$
\operatorname{Nm}:P_\Delta\longrightarrow P^\Delta,
\qquad
\bar x\longmapsto\sum_{\delta\in\Delta}\delta x
$$

is well defined. If $x$ is replaced by $(\gamma-1)y$, its norm is zero by reindexing.

**Proposition 6.2.** If $P$ is finite free over $\Lambda$, then $\operatorname{Nm}:P_\Delta\to P^\Delta$ is an isomorphism.

**Proof.** It suffices to prove the claim for $P=\Lambda$, because invariants, coinvariants, and norm commute with finite direct sums. The class of $[1]$ generates $\Lambda_\Delta$, and its norm is $N_\Delta$, which generates $\Lambda^\Delta$ by Lemma 6.1. The map sends one basis to the other. $\square$

This proposition is valid for projective modules as well: a projective module is a direct summand of a free one, and the norm isomorphism respects the splitting.

### 6.4 Locality of $\mathcal O[\Delta]$

**Proposition 6.3.** The ring $\Lambda=\mathcal O[\Delta]$ is local, with maximal ideal

$$
\mathfrak m_\Lambda=(\varpi,\mathfrak a).
$$

**Proof.** Modulo $\varpi$, the augmentation ideal of $k[\Delta]$ is nilpotent. To see this, choose generators $\delta_i$ of cyclic factors. In characteristic $\ell$,

$$
([\delta_i]-1)^{\ell^{r_i}}=[\delta_i]^{\ell^{r_i}}-1=0.
$$

Thus $k[\Delta]$ has nilpotent augmentation ideal and quotient $k$; it is local. Any maximal ideal of $\Lambda$ contains $\varpi$ and maps to the unique maximal ideal of $k[\Delta]$, so it equals $(\varpi,\mathfrak a)$. $\square$

Every finite projective $\Lambda$-module is therefore free. This fact will turn Hecke idempotent summands of a free deep-level module into free group-ring modules.

The group ring also carries a symmetric Frobenius functional. Define

$$
\tau:\Lambda\longrightarrow\mathcal O,
\qquad
\tau\left(\sum_\delta a_\delta[\delta]\right)=a_1.
$$

Then

$$
\langle a,b\rangle_\Lambda=\tau(ab)
$$

is a perfect $\mathcal O$-pairing. In the group basis, $[\delta]$ pairs with $[\delta^{-1}]$, so its matrix is a permutation matrix and has unit determinant. Consequently

$$
\Lambda\xrightarrow{\sim}\operatorname{Hom}_{\mathcal O}(\Lambda,\mathcal O),
\qquad
a\longmapsto(b\mapsto\tau(ab)).
$$

This is the algebraic reason a coefficient-valued pairing can be repackaged as a $\Lambda$-valued pairing. Notice that $\tau$ is coefficient extraction, not augmentation. Augmentation sums all coefficients and is used for coinvariants; $\tau$ selects the identity coefficient and is used for duality.

**Lemma 6.4.** Let $P$ be finite free over $\Lambda$. Then

$$
\operatorname{Hom}_{\Lambda}(P,\Lambda)
\cong\operatorname{Hom}_{\mathcal O}(P,\mathcal O)
$$

as $\mathcal O$-modules, with the appropriate inversion twist on the group action.

**Proof.** For $P=\Lambda$, compose a $\Lambda$-linear map with $\tau$. The Frobenius isomorphism above proves that this is an isomorphism. Both Hom constructions carry finite direct sums to finite direct products, which agree here, so the result follows for $\Lambda^r$. Inversion enters because moving $[\delta]$ from the first argument of the coefficient pairing to the second replaces it by $[\delta^{-1}]$. $\square$

This lemma will be used implicitly in Chapter 13. It explains why perfectness over $\mathcal O$ and freeness over $\Lambda$ have the right ranks for perfectness over $\Lambda$, while also showing that rank equality alone is insufficient: the adjoint matrix must still have unit determinant.

## 7. Group-ring freeness

### 7.1 Functions on a torsor

Let $X\to Y$ be a finite $\Delta$-torsor. The group acts on functions by right translation:

$$
(\delta f)(x)=f(x\delta).
$$

Choose one lift $s(y)\in X$ for each $y\in Y$. For a function $f:X\to A$, define

$$
\Phi(f)_y=\sum_{\delta\in\Delta}f(s(y)\delta)[\delta^{-1}]
\in\mathcal O[\Delta]\otimes_{\mathcal O}A.
$$

The inverse sends a group-ring-valued tuple to its coefficients. A direct reindexing shows that $\Phi(\gamma f)=[\gamma]\Phi(f)$. Hence

$$
\operatorname{Map}(X,A)\cong
\Lambda\otimes_{\mathcal O}\operatorname{Map}(Y,A)
$$

as left $\Lambda$-modules, noncanonically because the section $s$ was chosen.

The conclusion of freeness is canonical even though this displayed trivialization is not. Replacing $s(y)$ by $s(y)\eta_y$ multiplies the $y$-component by the unit $[\eta_y]$.

### 7.2 The weighted theorem

**Theorem 7.1 (quaternionic group-ring freeness).** Let $(Q,N)$ be clean, and write

$$
M_n=M(U_n(Q);W,\chi_f),
\qquad
\Lambda_n=\mathcal O[\Delta_{Q,n}].
$$

Then, for every $n\le N$, $M_n$ is finite free over $\Lambda_n$. More precisely, after choosing one lift of each lower-level class,

$$
M_n\cong\Lambda_n\otimes_{\mathcal O}M_0
$$

as $\Lambda_n$-modules.

**Proof.** By Theorem 5.1, every lower-level class has a fiber which is a $\Delta_{Q,n}$-torsor. By Section 5.3, the arithmetic stabilizer and hence the allowed coefficient lattice $W_i$ is the same at every point of that fiber and equals the lattice at lower level. Proposition 2.1 therefore gives

$$
M_n\cong\bigoplus_{i=1}^h\operatorname{Map}(\Delta_{Q,n},W_i).
$$

Section 7.1 identifies the $i$th summand with $\Lambda_n\otimes W_i$. Summing and using $M_0\cong\bigoplus W_i$ proves the stated isomorphism. Since $M_0$ is finite free over $\mathcal O$, the right side is finite free over $\Lambda_n$. $\square$

The same decomposition propagates perfect coefficient duality rather than assuming it anew at every depth. Use on every point above a lower class the same unit stabilizer weight used at depth zero. The deep finite-sum pairing is then the orthogonal direct sum of $|\Delta_{Q,n}|$ copies of the corresponding lower coefficient-lattice pairing. Its matrix is block diagonal with unit-determinant blocks, so it is perfect over $\mathcal O$. Diamond translation permutes the blocks and has adjoint diamond inversion. Thus $(\mathrm{PD})_{U_0(Q)}$ and cleanliness prove $(\mathrm{PD})_{U_n(Q)}$ for all $n\le N$.

### 7.3 Rank and base change

If $r=\operatorname{rank}_{\mathcal O}M_0$, then

$$
\operatorname{rank}_{\Lambda_n}M_n=r,
\qquad
\operatorname{rank}_{\mathcal O}M_n=|\Delta_{Q,n}|r.
$$

Under full effective rank this becomes $\ell^{nq}r$. The first equality is stronger than the second. An $\mathcal O$-module of rank $|\Delta|r$ need not be free, or even projective, over $\mathcal O[\Delta]$.

If $A$ is a flat $\mathcal O$-algebra, tensoring gives

$$
M_n\otimes_{\mathcal O}A
\cong A[\Delta_{Q,n}]\otimes_A(M_0\otimes_{\mathcal O}A).
$$

For nonflat $A$, the abstract tensor identity still follows from the free presentation, but it should not be confused with a newly formed automorphic module over $A$ when stabilizer invariants fail to commute with base change.

There is also a choice-free rank argument. Let $y\in X_0^\chi$ and let $M_{n,y}$ be the submodule supported on the fiber above $y$. Pick any one point $x$ in the fiber. Evaluation at $x$ identifies the coefficient at that point with the lower stabilizer lattice $W_y$. Diamond translates of a vector supported at $x$ have disjoint support, so the map

$$
\Lambda_n\otimes_{\mathcal O}W_y\longrightarrow M_{n,y}
$$

is injective. Simple transitivity says that every point is a unique translate of $x$, so it is also surjective. A different $x$ changes this map by a group-ring unit. Hence the rank of the fiber module is intrinsic even before the fibers are assembled.

This observation also proves a useful converse. If a fiber module with a rank-one coefficient lattice is free of rank one over the nominal group ring, the nominal action on the fiber must be free. Otherwise a nonidentity stabilizer would annihilate a basis vector after translating it to the stabilized point, contradicting faithfulness of the regular representation. Thus, in the rank-one case, group-ring freeness detects hidden stabilizers.

### 7.4 Hecke-local summands

Let $e$ be an idempotent endomorphism of $M_n$ commuting with $\Lambda_n$. Then

$$
M_n=eM_n\oplus(1-e)M_n
$$

as $\Lambda_n$-modules. Hence $eM_n$ is finite projective over $\Lambda_n$, and Proposition 6.3 makes it finite free.

Its rank is determined after augmentation. Indeed, if $e$ is compatible with lower level, then

$$
\operatorname{rank}_{\Lambda_n}eM_n
=\operatorname{rank}_{\mathcal O}eM_0.
$$

This is the mechanism by which a primary Hecke factor inherits group-ring freeness. Localization alone is not invoked as a slogan; the finite complete Hecke algebra supplies an actual idempotent, and that idempotent commutes with diamonds.

## 8. Exact augmentation

### 8.1 Orbit sum rather than pullback

For $f\in M_n$, define the orbit sum

$$
c_{n,0}(f)(g)=\sum_{\delta\in\Delta_{Q,n}}f(g\tilde\delta),
$$

with the coefficient action included in the evaluation when necessary. Cleanliness makes this independent of the lift and gives a form at level $U_0(Q)$. It satisfies

$$
c_{n,0}(\delta f)=c_{n,0}(f),
$$

so it factors through coinvariants.

This is not pullback. Pullback sends a lower-level form to a function constant on each fiber and identifies lower level with invariants. Orbit sum sends a characteristic function of one point of the fiber to the characteristic function of the base point and identifies coinvariants with lower level. The composite “pull back, then orbit sum” is multiplication by $|\Delta_{Q,n}|$.

### 8.2 The augmentation theorem

**Theorem 8.1 (exact augmentation).** Under the hypotheses of Theorem 7.1, orbit sum induces an isomorphism

$$
\overline c_{n,0}:M_n/\mathfrak a_nM_n
\xrightarrow{\sim}M_0.
$$

Equivalently, the sequence

$$
0\longrightarrow\mathfrak a_nM_n
\longrightarrow M_n\xrightarrow{c_{n,0}}M_0
\longrightarrow0
$$

is exact.

**Proof.** Use the torsor trivialization of Theorem 7.1. On one fiber, a coefficient-valued function corresponds to

$$
\sum_{\delta} [\delta]\otimes w_\delta.
$$

Orbit sum sends this element to $\sum_\delta w_\delta$, which is exactly $\epsilon\otimes1$. Its kernel on $\Lambda_n\otimes W_i$ is $\mathfrak a_n\otimes W_i=\mathfrak a_n(\Lambda_n\otimes W_i)$, and it is surjective. Direct sum over lower-level classes proves the sequence. $\square$

The theorem is integral. It uses no division by $|\Delta|$, and so remains valid when $\ell\mid|\Delta|$.

### 8.3 Invariants and the norm square

Pullback gives an isomorphism

$$
p_{0,n}:M_0\xrightarrow{\sim}M_n^{\Delta_{Q,n}}.
$$

The norm isomorphism of Proposition 6.2 fits into the commutative diagram

$$
\begin{array}{ccc}
M_n/\mathfrak a_nM_n&\xrightarrow{\operatorname{Nm}}&M_n^{\Delta_{Q,n}}\\
\downarrow\scriptstyle{\overline c_{n,0}}&&\uparrow\scriptstyle{p_{0,n}}\\
M_0&\xrightarrow{\mathrm{id}}&M_0.
\end{array}
$$

To verify commutativity, take the class of a characteristic function at one lift. Orbit sum sends it to the base characteristic function; norm sends it to the constant characteristic function on the fiber, which is the pullback of the same base function.

By contrast,

$$
c_{n,0}\circ p_{0,n}=|\Delta_{Q,n}|\,\mathrm{id}_{M_0}.
$$

This factor is an important diagnostic. Any formula claiming that raw trace and raw pullback are inverse integrally is incorrectly normalized.

### 8.4 Coefficient reduction

Because $M_n$ is free over $\Lambda_n$, the exact augmentation sequence remains exact after tensoring with any $\mathcal O$-module in the form

$$
(M_n\otimes A)/\mathfrak a_n(M_n\otimes A)
\cong M_0\otimes A.
$$

This is a statement about reduction of the chosen exact lattices. It does not assert that $M_n\otimes k$ equals the automorphic module constructed directly with coefficient module $W\otimes k$ unless stabilizer invariant formation is known to commute with reduction. Effective projective arithmetic stabilizers of order prime to $\ell$ give that extra conclusion by the averaging idempotent; bad stabilizer primes do not.

## 9. Hecke and diamond operators

### 9.1 Right-translation normalization

For $a\in D_f^\times$, right translation is

$$
(R_af)(g)=f(ga).
$$

If a double coset decomposes into right cosets

$$
UaU=\coprod_i a_iU,
$$

the associated Hecke operator is

$$
[UaU]f=\sum_iR_{a_i}f.
$$

This convention fixes every commutation and adjoint formula below. Switching to left translation would invert the diamond labels and transpose several displayed identities.

### 9.2 Commutation away from the auxiliary set

Let $w\notin Q$ be a place at which a specified Hecke operator acts. Its representatives have trivial component at every $v\in Q$, while a diamond representative has trivial component away from $Q$. The representatives commute in the restricted product. Therefore

$$
T_w\langle\delta\rangle
=\langle\delta\rangle T_w,
\qquad
S_w\langle\delta\rangle
=\langle\delta\rangle S_w.
$$

The same componentwise argument proves that away Hecke operators commute with pullback and orbit sum. Thus the exact augmentation sequence is Hecke equivariant.

For completeness, write an away double coset as

$$
U_n(Q)aU_n(Q)=\coprod_{i=1}^r a_iU_n(Q),
$$

with every $a_i$ trivial at $Q$, and represent a diamond by $\widetilde\delta$ supported at $Q$. Then

$$
a_i\widetilde\delta=\widetilde\delta a_i.
$$

Consequently

$$
\begin{aligned}
T_a(\langle\delta\rangle f)(g)
&=\sum_i f(ga_i\widetilde\delta)\\
&=\sum_i f(g\widetilde\delta a_i)
=\langle\delta\rangle(T_af)(g).
\end{aligned}
$$

For orbit sum, the same rearrangement gives

$$
\begin{aligned}
c_{n,0}(T_af)(g)
&=\sum_{\delta}\sum_i f(g\widetilde\delta a_i)\\
&=\sum_i\sum_\delta f(ga_i\widetilde\delta)
=T_a(c_{n,0}f)(g).
\end{aligned}
$$

The proof uses right-coset representatives consistently. With left-coset representatives the formulas must be rewritten rather than copied.

### 9.3 The oriented operator and diamonds

At $v\in Q$, choose the forward oriented double coset defining $U_v$. A projective diamond has a representative $h_a=\operatorname{diag}(1,a)$, while the forward coset has representatives

$$
r_u=\begin{pmatrix}\pi_v&u\\0&1\end{pmatrix}.
$$

The identity

$$
h_ar_u=r_{ua^{-1}}h_a
$$

permutes the residue-class representatives as $u$ varies. Hence the two double-coset actions commute. This conclusion depends on the standard local model; it is not a statement that every element of a full Iwahori algebra is central.

The same representatives $r_u$ define the forward operator at every depth because conjugation by $\operatorname{diag}(\pi_v,1)$ preserves the projective diagonal ratio. Pullback between two depths therefore commutes term by term with $U_v$. The trace $c_{m,n}$ is a sum over the kernel diamonds, and the commutation just proved gives

$$
c_{m,n}U_v=U_vc_{m,n}.
$$

Thus the selected forward operators, as well as the away Hecke family, belong to the common transition-compatible algebra.

Under the coefficient pairing, a diamond has adjoint

$$
\langle\delta\rangle^*=\langle\delta^{-1}\rangle.
$$

The forward operator $U_v$ generally has a different adjoint, traditionally denoted $V_v$. Treating $U_v$ as self-adjoint loses the distinction between primary and companion branches.

### 9.4 Acting algebras and faithful images

Let $\mathbb T_n$ be the image in $\operatorname{End}_{\mathcal O}(M_n)$ of the specified commutative family consisting of away operators and the selected commuting $U_v$'s. It is a finite torsion-free $\mathcal O$-module, hence finite free. By definition its action is faithful.

The abstract algebra generated by formal symbols can have maximal ideals outside the support of $M_n$. All localization below is therefore performed in a finite image algebra acting on the direct sum of the relevant levels. This simultaneously guarantees that the primary factor occurs and that its idempotent acts compatibly at every level.

## 10. Primary localization

### 10.1 Residual factors

A primary system is a maximal ideal $\mathfrak m$ of the chosen finite image Hecke algebra containing $\varpi$. The word primary refers to the selected residual factor, not to a claim that the module is rank one or that the local algebra is reduced.

For a finite commutative $\mathcal O$-algebra $A$, completeness of $\mathcal O$ gives a product decomposition

$$
A\cong\prod_{\mathfrak n\mid\varpi}A_{\mathfrak n}.
$$

Let $e_{\mathfrak m}$ be the idempotent of the $\mathfrak m$-factor. For every finite $A$-module $P$,

$$
P_{\mathfrak m}=e_{\mathfrak m}P.
$$

Thus finite-level localization is an actual direct summand.

We record the proof because the idempotent is central to freeness. Since $A$ is finite over the complete local ring $\mathcal O$, it is complete for the $\varpi$-adic topology. The quotient $A/\varpi A$ is Artinian, so

$$
A/\varpi A\cong\prod_{\overline{\mathfrak n}}
(A/\varpi A)_{\overline{\mathfrak n}}.
$$

The identities of these factors are pairwise orthogonal idempotents. Idempotents lift uniquely through a nilpotent ideal: if $e^2-e$ is nilpotent, repeated correction of $e$ produces an idempotent, and uniqueness follows because two sufficiently close idempotents in a commutative ring coincide. Applying this successively modulo $\varpi^r$ and using completeness gives orthogonal idempotents in $A$ whose sum is one. The corresponding factors are local and equal to the localizations $A_{\mathfrak n}$.

It follows that localizing a finite $A$-module is exact for a particularly concrete reason:

$$
P=P_{\mathfrak m}\oplus\bigoplus_{\mathfrak n\ne\mathfrak m}P_{\mathfrak n}.
$$

No denominators from the fraction field occur. By contrast, a projector that separates two characteristic-zero branches meeting at the same residual maximal ideal need not lie in $A$; its denominator may be divisible by $\varpi$. Such a projector cannot be used in the integral freeness proof.

### 10.2 A common finite Hecke algebra

To compare all depths $0\le n\le N$, let $\mathbb T^{\mathrm{com}}$ be the image of the specified common Hecke family on

$$
\mathcal M=\bigoplus_{n=0}^NM_n.
$$

Every generator commutes with diamonds and with the maps between levels. Fix a maximal ideal $\mathfrak m\subset\mathbb T^{\mathrm{com}}$ occurring in $M_0$, and let $e=e_{\mathfrak m}$. Define

$$
M_n^{\mathrm{pri}}=eM_n.
$$

Using a common image algebra matters. Unrelated idempotents chosen separately in $\mathbb T_n$ need not be compatible with trace, even if they receive the same list of named eigenvalues.

### 10.3 Primary deep-level modules

The primary module is stable under $\Lambda_n$, because $e$ is built from Hecke operators commuting with diamonds. It is also stable under every common Hecke operator. At depth zero it is exactly the generalized residual summand

$$
M_0^{\mathrm{pri}}=(M_0)_{\mathfrak m}.
$$

No semisimplicity is imposed. Several characteristic-zero branches can meet at $\mathfrak m$, and nilpotent Hecke action may remain inside the primary module. The construction retains all of them.

### 10.4 Freeness and exact augmentation after localization

**Theorem 10.1.** For a clean datum and a common primary idempotent $e$, the module $M_n^{\mathrm{pri}}$ is finite free over $\Lambda_n$, and orbit sum induces

$$
M_n^{\mathrm{pri}}/\mathfrak a_nM_n^{\mathrm{pri}}
\xrightarrow{\sim}M_0^{\mathrm{pri}}.
$$

Its $\Lambda_n$-rank is $\operatorname{rank}_{\mathcal O}M_0^{\mathrm{pri}}$.

**Proof.** The idempotent $e$ commutes with $\Lambda_n$, so $eM_n$ is a direct summand of the free $\Lambda_n$-module $M_n$. It is projective and therefore free because $\Lambda_n$ is local. Applying $e$ to the exact sequence of Theorem 8.1 remains exact and gives

$$
0\to e\mathfrak a_nM_n\to eM_n\to eM_0\to0.
$$

Commutation gives $e\mathfrak a_nM_n=\mathfrak a_neM_n$. This proves exact augmentation. Finally a free $\Lambda_n$-module has rank equal to the $\mathcal O$-rank of its augmentation quotient. $\square$

## 11. Refinements at an auxiliary prime

### 11.1 The unnormalized polynomial

At a split hyperspecial place $v$, the spherical operators are normalized so that the polynomial in the reciprocal variable is

$$
P_v(X)=1-T_vX+q_vS_vX^2.
$$

Equivalently, the polynomial whose roots are the unnormalized $U_v$-eigenvalues is

$$
F_v(Y)=Y^2-T_vY+q_vS_v.
$$

The product of the two roots is $q_vS_v$, not $S_v$, and the sum is $T_v$. This normalization controls both the old companion matrix and the companion root under adjunction.

Let $\mathfrak m$ be a residual maximal ideal of the away Hecke algebra. Assume $S_v$ is a unit on the chosen factor. In the residue field $k(\mathfrak m)$, write

$$
\overline F_v(Y)
=Y^2-\bar t_vY+\overline{q_vs_v}.
$$

A refinement is a choice of one residual root $\bar\alpha_v$; the other is denoted $\bar\beta_v$.

### 11.2 Two distinct residual roots

The regular refinement hypothesis is

$$
\bar\alpha_v\ne\bar\beta_v,
\qquad
\bar\alpha_v\bar\beta_v=\overline{q_vs_v}\ne0.
$$

It implies that $\bar\alpha_v-\bar\beta_v$ is a unit in the residue field. After a finite unramified coefficient extension if necessary, both roots may be regarded as residue scalars. In the algebra acting on the degeneracy source, the two residual maximal ideals are distinguished by

$$
U_v-\bar\alpha_v
\quad\text{and}\quad
U_v-\bar\beta_v.
$$

They are distinct because their difference is the nonzero scalar $\bar\beta_v-\bar\alpha_v$, and both occur on the companion source computed in Section 11.3. Its finite image algebra therefore has orthogonal idempotents separating the two residual factors. On the full oriented module, either ideal is used only if it lies in the support; the finite acting-image convention then supplies its idempotent factor. No division by a characteristic-zero root difference is needed: coprimality in the special fiber supplies the integral idempotents.

For a set $Q$, a primary refinement is a tuple $\bar\alpha=(\bar\alpha_v)_{v\in Q}$. It determines the maximal ideal obtained by adjoining all relations $U_v-\bar\alpha_v$. Replacing every selected root by the other root gives the second-root refinement. Adjoint duality will identify which of these is the companion; it is not safe to declare this before accounting for $S_v$ and the dual central character.

### 11.3 The old companion matrix

Let $U^{\mathrm{hyp}}$ be hyperspecial at $v$, and let $U_0(v)$ be oriented level. The two degeneracy maps form

$$
d:M(U^{\mathrm{hyp}})\oplus M(U^{\mathrm{hyp}})\longrightarrow M(U_0(v)).
$$

On the old source, and with the right-translation convention, the forward operator has companion form

$$
A_v=
\begin{pmatrix}
T_v&q_vS_v\\
-1&0
\end{pmatrix}
$$

up to the harmless simultaneous change of the ordered degeneracy basis fixed at the outset. Direct multiplication gives

$$
A_v^2-T_vA_v+q_vS_vI=0.
$$

Indeed,

$$
A_v^2=
\begin{pmatrix}
T_v^2-q_vS_v&T_vq_vS_v\\
-T_v&-q_vS_v
\end{pmatrix},
$$

and subtracting $T_vA_v$ and adding $q_vS_vI$ gives zero entry by entry.

The entries have a double-coset explanation. Applying $U_v$ to the first degeneracy copy runs through the $q_v$ forward neighbors of the oriented edge together with the return term. Regrouping the forward neighbors at hyperspecial level gives $T_v$ times the first copy, while the return term is minus the second copy in the chosen oriented basis. Applying $U_v$ to the second copy traverses the central two-step path; its contribution is $q_vS_v$ times the first copy. Hence

$$
U_vd_0=T_vd_0-d_1,
\qquad
U_vd_1=q_vS_vd_0,
$$

which is exactly the displayed matrix when columns record the images of the two basis copies. The factor $q_v$ counts the forward residue classes, and $S_v$ records the central displacement after two steps. This proves the matrix formula from the right-coset normalization.

If one replaces $d_1$ by $-d_1$, the two minus signs move to different entries. The characteristic polynomial is unchanged. This is why branch statements should be expressed using $Y^2-T_vY+q_vS_v$, not by memorizing one matrix without its basis convention.

Modulo a regular residual ideal, the two factors $A_v-\bar\alpha_v$ and $A_v-\bar\beta_v$ are coprime. Bézout therefore splits the degeneracy source into two direct summands. Each source summand has the same coefficient rank as the original hyperspecial module: after extending scalars to the residue field, the companion matrix has two distinct eigenspaces, each obtained from one copy of the base module, and projectivity lifts the rank integrally. The corresponding assertion for the old **image** additionally requires injectivity of the degeneracy map. This distinction cannot be omitted over an integral ring.

### 11.4 Primary and second-root branches

**Proposition 11.1.** On the $2^{|Q|}$-fold degeneracy source, regular refinement at every $v\in Q$ gives a direct sum of $2^{|Q|}$ integral refined factors. Each source factor is isomorphic as an away-Hecke module to the original hyperspecial module after localization at $\mathfrak m$. The degeneracy map carries each source factor onto the correspondingly refined old-image factor; this map is an isomorphism if the localized degeneracy map is injective.

**Proof.** At one prime, the two coprime residual factors give complementary idempotents $e_{v,\alpha}$ and $e_{v,\beta}$ on the source. They commute with away Hecke operators. The companion-matrix calculation shows that each factor has one copy of the base module. More explicitly, over the local factor the cyclic algebra generated by $A_v$ is free of rank two over the base and splits as the product of its two local factors; tensoring its regular rank-one module with the base module yields one copy on each factor.

To justify the last sentence, let $A$ be the complete local base Hecke algebra. The polynomial $F_v(Y)\in A[Y]$ has two distinct simple roots modulo the maximal ideal. Hensel's lemma lifts its factorization uniquely to

$$
F_v(Y)=(Y-\alpha_v)(Y-\beta_v)
$$

with $\alpha_v-\beta_v\in A^\times$. Therefore

$$
A[Y]/(F_v)\cong A\times A
$$

by the Chinese remainder theorem. The companion source is

$$
\bigl(A[Y]/(F_v)\bigr)\otimes_A M_\mathfrak m,
$$

because $Y$ acts through the companion matrix. Each product idempotent therefore cuts out exactly one copy of $M_\mathfrak m$.

For completeness, the simple-root case of Hensel's lemma follows by successive approximation. If $a_r$ satisfies $F_v(a_r)\in\mathfrak n^r$, choose $h_r\in\mathfrak n^r$ solving

$$
F_v'(a_r)h_r\equiv-F_v(a_r)\pmod{\mathfrak n^{r+1}}.
$$

This is possible because $F_v'(a_r)$ reduces to $\bar\alpha_v-\bar\beta_v$, a unit. Taylor expansion gives $F_v(a_r+h_r)\in\mathfrak n^{r+1}$. Completeness produces a root $\alpha_v=\lim a_r$; division by the monic factor $Y-\alpha_v$ gives the other root. Their difference remains a unit because its residue is nonzero.

For several primes, the operators and idempotents commute because they occupy different local components. Products

$$
e_{1,\varepsilon_1}\cdots e_{q,\varepsilon_q},
\qquad \varepsilon_i\in\{\alpha,\beta\},
$$

are orthogonal and sum to one on the degeneracy source. Repeated application of the one-prime result identifies every product summand with the base localized module. The intertwining identities of Section 11.3 make the degeneracy map equivariant for these idempotents, hence identify their images with the refined old-image factors. If the degeneracy map is injective, its restriction to every factor is injective and therefore isomorphic onto that image. $\square$

This proposition splits the source before it identifies the old image. It neither supplies degeneracy injectivity nor states that the entire oriented-level module is old. Exact passage from the full oriented module to minimal level requires the control criterion proved in Chapter 16.

## 12. Duality and the companion module

### 12.1 Adjoint maximal ideals

Let $M_n$ and $M_n^\vee$ be paired exact modules, and suppose the pairing is perfect. For every specified Hecke operator $t$, let $t^*$ denote its adjoint on the dual module. This defines an isomorphism between the two finite image algebras,

$$
*:\mathbb T(M_n)\xrightarrow{\sim}\mathbb T(M_n^\vee),
$$

provided the generating families contain the adjoints.

If $\mathfrak m$ is a primary maximal ideal, define its **companion ideal** by

$$
\mathfrak m^*=\{t^*:t\in\mathfrak m\}.
$$

Equivalently, it is the kernel of the residual character $t^*\mapsto\bar\lambda(t)$. The companion module is

$$
M_n^{\mathrm{cmp}}=(M_n^\vee)_{\mathfrak m^*}.
$$

This definition automatically accounts for inverse central character, contragredient weight, inverse diamonds, and the fact that $U_v^*=V_v$ rather than $U_v$.

### 12.2 The companion is not an informal copy

It can happen that $W\cong W^\vee$, $\chi_f=\chi_f^{-1}$, and $\mathfrak m=\mathfrak m^*$. Only then may primary and companion be identified as the same module, and even then an explicit self-duality is required. In general they are distinct lattices at distinct maximal ideals.

The need for a companion is already visible in diamonds. If

$$
\langle\delta\rangle^*=\langle\delta^{-1}\rangle,
$$

then the character $\psi$ on the primary side pairs with $\psi^{-1}$ on the dual side. Pairing primary with another copy carrying $\psi$ would vanish unless $\psi^2=1$.

### 12.3 Perfect primary--companion duality

**Theorem 12.1.** Suppose

$$
b_n:M_n\times M_n^\vee\longrightarrow\mathcal O
$$

is perfect and every specified operator has an adjoint in the companion Hecke algebra. Then the restricted pairing

$$
b_n:M_n^{\mathrm{pri}}\times M_n^{\mathrm{cmp}}\longrightarrow\mathcal O
$$

is perfect. The primary summand is orthogonal to every dual Hecke factor other than the companion factor.

**Proof.** Let $e$ be the idempotent of $\mathfrak m$ and $e^*$ its adjoint. If $f$ is a different dual factor idempotent, then $e^*f=0$. For $x\in eM_n$ and $y\in fM_n^\vee$,

$$
b_n(x,y)=b_n(ex,y)=b_n(x,e^*y)=0.
$$

Thus $eM_n$ pairs only with $e^*M_n^\vee$. The perfect pairing identifies $M_n^\vee$ with $\operatorname{Hom}_{\mathcal O}(M_n,\mathcal O)$. Under the orthogonal idempotent decompositions, the dual of $eM_n$ is exactly $e^*M_n^\vee$. Hence the restricted pairing is perfect. $\square$

### 12.4 The root description of the companion

On a regular old factor, suppose $U_v$ has primary root $\alpha_v$ and the adjoint relation identifies

$$
V_v=q_vS_vU_v^{-1}
$$

on the invertible old quotient, with $S_v$ transferred to the inverse-character dual side. Then the adjoint root is

$$
\beta_v=\frac{q_vS_v}{\alpha_v}.
$$

Since $\alpha_v\beta_v=q_vS_v$, this is the other root of $Y^2-T_vY+q_vS_v$. Thus the companion ideal is the second-root ideal in this normalization.

The formula is a consequence, not a definition. If the adjoint convention or central operator is normalized differently, the safe definition remains $\mathfrak m^*$. This prevents an unnoticed scalar factor from sending the primary branch to the wrong dual factor.

## 13. The group-ring-valued pairing

### 13.1 Construction from a coefficient pairing

Let $P$ and $P'$ be modules with $\Delta$-actions and a pairing

$$
b:P\times P'\longrightarrow\mathcal O
$$

satisfying

$$
b(\delta x,y)=b(x,\delta^{-1}y).
$$

Define

$$
\mathcal H(x,y)
=\sum_{\delta\in\Delta}b(x,\delta y)[\delta]
\in\Lambda.
$$

This coefficient order is chosen to match left group-ring actions and the inversion involution. Reversing $\delta$ in either the argument or the basis element changes the sesquilinearity convention.

For quaternionic modules, take $P=M_n^{\mathrm{pri}}$, $P'=M_n^{\mathrm{cmp}}$, and let $b$ be the coefficient-valued primary--companion pairing. The adjoint formula for diamonds gives the required invariance.

### 13.2 Sesquilinearity

**Proposition 13.1.** The pairing $\mathcal H$ is $\Lambda$-linear in the first variable and $\iota$-linear in the second:

$$
\mathcal H(ax,y)=a\mathcal H(x,y),
\qquad
\mathcal H(x,ay)=\mathcal H(x,y)\iota(a).
$$

**Proof.** It is enough to take $a=[\gamma]$. Then

$$
\begin{aligned}
\mathcal H(\gamma x,y)
&=\sum_\delta b(\gamma x,\delta y)[\delta]\\
&=\sum_\delta b(x,\gamma^{-1}\delta y)[\delta].
\end{aligned}
$$

Put $\eta=\gamma^{-1}\delta$. Since $\Delta$ is abelian, $[\delta]=[\gamma][\eta]$, giving $\mathcal H(\gamma x,y)=[\gamma]\mathcal H(x,y)$. Similarly,

$$
\mathcal H(x,\gamma y)
=\sum_\delta b(x,\delta\gamma y)[\delta].
$$

With $\eta=\delta\gamma$, one has $[\delta]=[\eta][\gamma^{-1}]$, so this equals $\mathcal H(x,y)[\gamma^{-1}]$. Extend $\mathcal O$-linearly. $\square$

### 13.3 Perfectness

Call $\mathcal H$ perfect if the adjoint map

$$
P'\longrightarrow\operatorname{Hom}_{\Lambda}(P,\Lambda)^{\iota}
$$

is an isomorphism, where $\iota$ records the second-variable convention.

**Theorem 13.2.** For a clean datum satisfying perfect coefficient duality, the group-ring-valued pairing

$$
\mathcal H_n:M_n^{\mathrm{pri}}\times M_n^{\mathrm{cmp}}\longrightarrow\Lambda_n
$$

is perfect.

**Proof.** First consider one lower-level class with coefficient lattice $L$ paired perfectly with $L^\vee$. Choose one point in its diamond fiber. The corresponding deep modules are $\Lambda_n\otimes L$ and $\Lambda_n\otimes L^\vee$. On regular basis elements, the definition gives a unit group element times the coefficient pairing. After changing the chosen lift, this unit changes but remains invertible. Therefore the matrix of $\mathcal H_n$ is a block permutation matrix whose nonzero blocks are matrices of the perfect pairing $L\times L^\vee$. Its determinant is a unit of $\Lambda_n$.

Summing over classes proves perfectness on the full modules. The primary idempotent on the first side is adjoint to the companion idempotent on the second. The argument of Theorem 12.1 restricts the perfect $\Lambda_n$-duality to these two summands. $\square$

An alternative proof uses reduction modulo the maximal ideal $(\varpi,\mathfrak a_n)$ of $\Lambda_n$. The reduced pairing is the perfect lower-level pairing, so Nakayama's lemma makes the adjoint map surjective; equality of free ranks makes it an isomorphism.

Here are the details of that alternative. Write $P_n=M_n^{\mathrm{pri}}$ and $C_n=M_n^{\mathrm{cmp}}$, and let

$$
\Phi:C_n\longrightarrow\operatorname{Hom}_{\Lambda_n}(P_n,\Lambda_n)^\iota
$$

be the adjoint map. Both source and target are free of the same $\Lambda_n$-rank. Reducing modulo the maximal ideal of $\Lambda_n$ identifies the source with $C_0/\varpi C_0$ and the target with the dual of $P_0/\varpi P_0$. Section 13.4 identifies the reduced map with the reduction of the lower-level perfect pairing, so it is an isomorphism. Nakayama's lemma shows that the cokernel of $\Phi$ is zero. A surjection between finite free modules of equal rank has determinant a unit and is therefore an isomorphism.

This proof shows exactly which hypotheses are necessary. If augmentation of the pairing differs from the lower-level pairing by $|\Delta_n|$, its reduction is zero and Nakayama gives nothing. If $P_n$ is merely $\mathcal O$-free rather than $\Lambda_n$-free, the target rank need not match. If the lower pairing is nonperfect because of a stabilizer denominator, the defect persists at deep level.

### 13.4 Augmentation of the pairing

Applying $\epsilon:\Lambda_n\to\mathcal O$ gives

$$
\epsilon(\mathcal H_n(x,y))
=\sum_{\delta\in\Delta_{Q,n}}b_n(x,\delta y).
$$

This descends to coinvariants in both variables with the inversion convention. Under the orbit-sum identifications, it is the lower-level primary--companion pairing. This can be checked on one characteristic function in a fiber, where exactly one summand contributes.

Consequently perfectness survives augmentation:

$$
M_n^{\mathrm{pri}}/\mathfrak a_nM_n^{\mathrm{pri}}
\quad\text{is perfectly paired with}\quad
M_n^{\mathrm{cmp}}/\mathfrak a_nM_n^{\mathrm{cmp}},
$$

and these are identified with $M_0^{\mathrm{pri}}$ and $M_0^{\mathrm{cmp}}$. The raw coefficient pairing on pullbacks would instead introduce the factor $|\Delta_{Q,n}|$; the group-ring-valued normalization avoids it.

## 14. Transitions in a fixed tower

### 14.1 Quotient maps of diamond groups

Fix one admissible pair $(Q,N)$. For $m\ge n$, the local quotient maps give

$$
\rho_{m,n}:\Delta_{Q,m}\twoheadrightarrow\Delta_{Q,n}
$$

provided the effective kernels are compatible. Clean full-rank data have this property automatically. Let

$$
H_{m,n}=\ker(\rho_{m,n}),
\qquad
\rho_{m,n}:\Lambda_m\twoheadrightarrow\Lambda_n
$$

also denote the induced group-ring map. Its kernel is generated by $[h]-1$ for $h\in H_{m,n}$.

The level inclusion is

$$
U_m(Q)\subseteq U_n(Q),
$$

and $X_m^\chi\to X_n^\chi$ is an $H_{m,n}$-torsor.

### 14.2 Trace and pullback

Pullback

$$
p_{n,m}:M_n\longrightarrow M_m
$$

identifies $M_n$ with $M_m^{H_{m,n}}$. Orbit sum

$$
c_{m,n}:M_m\longrightarrow M_n,
\qquad
c_{m,n}(f)(x)=\sum_{h\in H_{m,n}}f(xh),
$$

identifies $H_{m,n}$-coinvariants with $M_n$. Both maps are Hecke equivariant. They satisfy

$$
c_{m,n}p_{n,m}=|H_{m,n}|\,\mathrm{id},
$$

while norm gives the inverse between coinvariants and invariants without dividing by $|H_{m,n}|$.

### 14.3 Exact base change

**Theorem 14.1 (transition base change).** For $m\ge n$, orbit sum induces canonical isomorphisms

$$
\Lambda_n\otimes_{\Lambda_m}M_m\xrightarrow{\sim}M_n,
$$

$$
\Lambda_n\otimes_{\Lambda_m}M_m^{\mathrm{pri}}
\xrightarrow{\sim}M_n^{\mathrm{pri}},
$$

and the analogous isomorphism for companion modules.

**Proof.** Tensoring with $\Lambda_n$ is quotienting by the ideal generated by $[h]-1$, $h\in H_{m,n}$. Thus the first source is $(M_m)_{H_{m,n}}$. The torsor proof of Theorem 8.1, applied to $X_m^\chi\to X_n^\chi$, identifies this coinvariant module with $M_n$ via orbit sum. The common primary and companion idempotents commute with the quotient, so applying them gives the other two isomorphisms. $\square$

This is stronger than equality of ranks: it identifies the lower-depth lattice with exact group-ring base change from the higher-depth lattice.

The kernel can be written explicitly:

$$
\ker(c_{m,n})
=\bigl([\!h\!]-1:h\in H_{m,n}\bigr)M_m.
$$

To prove the reverse inclusion beyond the evident containment, choose one point in each $H_{m,n}$-fiber. A function of orbit sum zero can be written as a sum of differences between its values at each point and at the chosen point. Each such difference is $(h-1)$ times a function supported at one point. Summing over fibers proves the formula. This proof is integral and never averages over $H_{m,n}$.

There is a useful Cartesian description of the tower. For $r\ge m\ge n$, a fiber of $X_r^\chi\to X_n^\chi$ is a torsor under $H_{r,n}$, and the intermediate quotient by $H_{r,m}$ is the fiber of $X_m^\chi\to X_n^\chi$. Thus

$$
H_{r,n}/H_{r,m}\cong H_{m,n}.
$$

This group identity is the geometric reason for transitivity of traces and associativity of group-ring base change.

### 14.4 Transitivity, Hecke action, and pairings

For $r\ge m\ge n$, summing first over $H_{r,m}$ and then over $H_{m,n}$ sums exactly once over $H_{r,n}$. Hence

$$
c_{m,n}\circ c_{r,m}=c_{r,n}.
$$

Pullbacks satisfy $p_{m,r}p_{n,m}=p_{n,r}$. Group-ring maps satisfy $\rho_{m,n}\rho_{r,m}=\rho_{r,n}$. All diagrams with away Hecke operators commute because their representatives occupy disjoint local components. The diagrams with the selected $U_v$ commute by the fixed-representative and diamond-sum calculation of Section 9.3.

The perfect pairing also descends by base change. Under the isomorphisms of Theorem 14.1,

$$
\mathcal H_n(c_{m,n}x,c_{m,n}y)
=\rho_{m,n}(\mathcal H_m(x,y)),
$$

where the notation means the bilinear map induced on the tensor products; changing representatives by an element of $H_{m,n}$ gives the same value because that element maps to one in $\Lambda_n$. Thus the entire primary--companion dual system is compatible through the fixed tower.

## 15. The complete finite-level package

### 15.1 Definition of a clean Taylor--Wiles datum

A **clean Taylor--Wiles datum of depth $N$** consists of:

1. the arithmetic and coefficient data of Section 1.2;
2. an auxiliary set $Q$ satisfying Section 4.1;
3. the standard nested levels $U_n(Q)$ for $0\le n\le N$;
4. full effective diamond groups $\Delta_{Q,n}\cong(\mathbb Z/\ell^n\mathbb Z)^q$;
5. the clean stabilizer and coefficient conditions of Section 4.4;
6. a perfect integral pairing with the dual coefficient system at oriented depth zero, with the stabilizer weights transported unchanged along every clean fiber;
7. a common adjoint-stable finite image Hecke algebra on all levels;
8. a primary residual maximal ideal $\mathfrak m$ and its adjoint companion $\mathfrak m^*$;
9. when root refinements are used, distinct nonzero residual roots at every $v\in Q$.

Every item is checkable at finite level. The definition contains no assertion about transitions to a different auxiliary set and no automatic identification with a hyperspecial minimal-level module.

### 15.2 The construction theorem

**Theorem 15.1 (deep-level quaternionic module theorem).** From a clean Taylor--Wiles datum of depth $N$, define

$$
P_n=M(U_n(Q);W,\chi_f)_{\mathfrak m},
$$

$$
C_n=M(U_n(Q);W^\vee,\chi_f^{-1})_{\mathfrak m^*},
$$

and $\Lambda_n=\mathcal O[\Delta_{Q,n}]$. Then, for every $0\le n\le N$:

1. $P_n$ and $C_n$ are finite free over $\Lambda_n$;
2. their ranks are independent of $n$ and equal the corresponding $\mathcal O$-ranks at $n=0$;
3. orbit sum gives exact augmentation isomorphisms

   $$
   P_n/\mathfrak a_nP_n\cong P_0,
   \qquad
   C_n/\mathfrak a_nC_n\cong C_0;
   $$

4. there is a perfect pairing

   $$
   \mathcal H_n:P_n\times C_n\longrightarrow\Lambda_n
   $$

   that is linear in the first variable and $\iota$-linear in the second;
5. diamonds commute with the specified away Hecke operators and selected oriented operators;
6. for $m\ge n$, exact base change gives

   $$
   \Lambda_n\otimes_{\Lambda_m}P_m\cong P_n,
   \qquad
   \Lambda_n\otimes_{\Lambda_m}C_m\cong C_n;
   $$

7. all transition maps are transitive, Hecke equivariant, adjoint compatible, and compatible with $\mathcal H_n$.

### 15.3 Proof of the theorem

**Proof.** The local exact quotients and global standard levels give the nested groups and levels of Chapters 3 and 4. Cleanliness turns every class-set fiber into a diamond torsor by Theorem 5.1 and keeps coefficient stabilizers constant by Section 5.3. Theorem 7.1 makes the full automorphic modules free over $\Lambda_n$.

The common Hecke algebra supplies compatible primary and companion idempotents. Their summands are projective over $\Lambda_n$, hence free because $\Lambda_n$ is local. This proves assertion 1. The exact augmentation theorem commutes with the idempotents, proving assertion 3; assertion 2 follows by taking ranks in the augmentation quotient.

Perfect coefficient duality and the adjoint idempotents give perfect primary--companion coefficient pairing by Theorem 12.1. Chapter 13 promotes it to the perfect sesquilinear $\Lambda_n$-valued pairing, proving assertion 4. Componentwise double-coset calculations prove assertion 5.

Finally, the maps $U_m(Q)\subseteq U_n(Q)$ form genuine torsors with kernel $H_{m,n}$. The transition base-change theorem proves assertion 6, and the summation and reindexing calculations of Section 14.4 prove assertion 7. $\square$

### 15.4 Independence of auxiliary choices

Changing a representative for a diamond class changes a torsor trivialization by a group element, hence by a unit of $\Lambda_n$. Changing the chosen lift of a lower-level class does the same independently in each direct summand. Therefore freeness, rank, exact augmentation, and perfectness do not depend on these choices.

Changing the splitting $D_v^\times\cong\mathrm{GL}_2(F_v)$, the orientation, or the generator of $\Delta_v(n)$ changes the labeled diamond action by an automorphism of the group. The resulting group rings are canonically isomorphic only after that automorphism is recorded. Formulas involving $U_v$, the projective diagonal ratio, and primary roots must all be transported together.

The primary maximal ideal is genuine data, not an auxiliary choice that disappears. A different residual root gives a different refined module. Adjoint duality dictates the companion factor and prevents arbitrary identification of the two.

## 16. Passage to minimal level

### 16.1 Why augmentation stops at oriented level

The quotient of $U_n(Q)$ by diamonds is $U_0(Q)$, not the original hyperspecial level. Therefore the unconditional conclusion of Theorem 15.1 is

$$
P_n/\mathfrak a_nP_n\cong P_0(Q),
$$

where $P_0(Q)$ is the chosen primary factor at oriented level at every place of $Q$. Replacing the right side by a module at hyperspecial level requires a second theorem.

This two-step structure is unavoidable. Diamonds remember the quotient

$$
K_0(v)/K_1(v,n),
$$

whereas the change from hyperspecial $K(v)=\mathrm{GL}_2(\mathcal O_v)$ to $K_0(v)$ is governed by two degeneracy maps and an old--new problem. The first step is a finite torsor calculation. The second step is an integral splitting and support calculation.

### 16.2 The two degeneracy maps

At one prime $v$, let $M$ be the hyperspecial module and $M_0(v)$ the oriented module. The two adjacent vertices to an oriented edge give maps

$$
d_0,d_1:M\longrightarrow M_0(v).
$$

Together they form

$$
d=(d_0,d_1):M\oplus M\longrightarrow M_0(v).
$$

Let

$$
r=(r_0,r_1)^t:M_0(v)\longrightarrow M\oplus M
$$

be the reverse correspondence: trace after the appropriate inverse translation. This map is defined on the same coefficient system as $d$. Under a declared self-dual pairing it is the adjoint $d^*$; for primary--companion pairings, adjunction instead relates it to the corresponding reverse map on the companion system. Keeping the notation $r$ avoids silently identifying a module with its dual.

In the standard unnormalized convention, the Gram operator on the source has the shape

$$
G_v=rd=
\begin{pmatrix}
q_v+1&T_v\\
S_v^{-1}T_v&q_v+1
\end{pmatrix},
$$

after identifying the dual central operator in the second off-diagonal entry. A change of degeneracy basis can conjugate this matrix, but its determinant remains

$$
D_v=(q_v+1)^2-S_v^{-1}T_v^2.
$$

The old image is $\operatorname{im}(d)$. For this same-coefficient control argument, the complementary kernel is $\ker(r)$, while the old quotient is $M_0(v)/\operatorname{im}(d)$. On the paired companion system, the adjoint kernel is the orthogonal new lattice. These notions agree only after the coefficient identifications, saturation, and perfectness required for that comparison have been proved.

We justify the Gram entries. The composite $r_id_i$ pulls a form to oriented level and traces it back along a fiber of size $q_v+1$, so

$$
r_id_i=(q_v+1)\operatorname{id}.
$$

For $i\ne j$, pulling along one endpoint and tracing along the other follows the length-one adjacency correspondence. With the first orientation this is $T_v$. Reversing the orientation changes the central displacement and gives $S_v^{-1}T_v$. Hence

$$
r_0d_1=T_v,
\qquad
r_1d_0=S_v^{-1}T_v.
$$

Putting these four composites into a $2$-by-$2$ matrix gives $G_v$. Its determinant is computed in the commutative away-Hecke algebra:

$$
\det(G_v)
=(q_v+1)^2-T_vS_v^{-1}T_v
=(q_v+1)^2-S_v^{-1}T_v^2.
$$

The asymmetry of the off-diagonal terms is expected. It records the central one-coset operator under right translation. If the pairing identifies $S_v$ with a scalar unit and one rescales a degeneracy map by a chosen square root, the matrix can be made symmetric, but that rescaling is not part of the integral normalization.

### 16.3 A precise control criterion

Fix a primary oriented maximal ideal $\mathfrak m_\alpha$ above a hyperspecial ideal $\mathfrak m$. Consider the following conditions.

1. The determinant $D_v$ is a unit on the localized source.
2. The selected oriented factor has no support in the old quotient:

   $$
   \bigl(M_0(v)/\operatorname{im}(d)\bigr)_{\mathfrak m_\alpha}=0.
   $$

   Equivalently, the $\mathfrak m_\alpha$-factor is generated by the old image.
3. The chosen root is regular, so the degeneracy source splits into its $\alpha$- and $\beta$-factors.

Condition 1 says the old lattice is a direct summand with no self-congruence at $v$. It already forces localized degeneracy injectivity and saturation; adding those as a separate hypothesis would be redundant. Condition 2 is the genuinely additional support theorem excluding an oriented packet outside the old image on the selected root branch. It is deliberately not strengthened to vanishing of every other oriented factor. Condition 3 selects one of the two old copies.

**Theorem 16.1 (minimal-level control criterion).** If Conditions 1--3 hold, then the selected degeneracy map induces a Hecke-equivariant isomorphism

$$
M_\mathfrak m\xrightarrow{\sim}M_0(v)_{\mathfrak m_\alpha}.
$$

**Proof.** Since $D_v$ is a unit, $G_v=rd$ is invertible. Therefore

$$
e_{\mathrm{old}}=dG_v^{-1}r
$$

is an idempotent on the localized oriented module. Its image is the old image: it is visibly contained there, and on an element $d(x)$ it gives

$$
dG_v^{-1}rd(x)=d(x).
$$

Also $G_vx=0$ whenever $d(x)=0$, so invertibility of $G_v$ makes $d$ injective. The displayed formula supplies a left inverse $G_v^{-1}r$ to $d$, proving at once that the old image is a direct summand and hence saturated. The kernel of $e_{\mathrm{old}}$ is $\ker(r)$. Thus

$$
M_0(v)_\mathfrak m
=\operatorname{im}(d)_\mathfrak m\oplus\ker(r)_\mathfrak m.
$$

Condition 2 says that localization at $\mathfrak m_\alpha$ identifies the oriented module with this old image. Condition 3 and Proposition 11.1 split the injectively embedded source into the two regular root factors, each isomorphic to $M_\mathfrak m$. Localization selects the $\alpha$-old factor. $\square$

The support condition is not a formal consequence of the unit determinant. The determinant controls the old lattice and its canonical complement; it does not prove that the complement has no Hecke support at $\mathfrak m_\alpha$. A Galois level-lowering theorem, a local representation-theoretic support theorem, or a direct finite-module calculation must supply that assertion in an application.

### 16.4 Exact minimal-level augmentation

Apply Theorem 16.1 successively at the primes of $Q$, with commuting root idempotents. If the three control conditions hold at every stage, there is an isomorphism

$$
P_0(Q)\cong M_{\mathfrak m},
$$

where $M_{\mathfrak m}$ is the minimal hyperspecial module localized at the original away system. Composing with Theorem 10.1 gives

$$
\boxed{
P_n/\mathfrak a_nP_n\cong M_{\mathfrak m}.}
$$

Assuming the corresponding support condition for the adjoint companion factor, the same argument there gives

$$
C_n/\mathfrak a_nC_n\cong M^\vee_{\mathfrak m^*}.
$$

**Corollary 16.2.** Under clean deep-level hypotheses and minimal-level control on both adjoint sides at every auxiliary prime, the primary and companion modules satisfy the full Taylor--Wiles augmentation property with a base module independent of $Q$.

**Proof.** The deep-to-oriented augmentation is canonical and exact by Theorem 10.1. Minimal-level control identifies the oriented primary factor with the same base factor at each prime. The maps commute because the local degeneracy correspondences occupy distinct adelic components. Their composite is therefore independent of the order in which the primes are removed. The dual statement follows by adjunction. $\square$

The corollary makes clear where each hypothesis enters. Torsor cleanliness proves group-ring freeness and deep-to-oriented augmentation. It does not prove minimal-level control. Conversely, an old--new theorem at oriented level does not prove that deeper class-set fibers are free diamond torsors.

## 17. Saturation and exceptional congruences

### 17.1 Saturation is an additional theorem

For a map of finite free $\mathcal O$-modules $f:A\to B$, the image is saturated when $B/f(A)$ is $\mathcal O$-torsion-free. Equivalently,

$$
f(A)=(f(A)\otimes E)\cap B
$$

inside $B\otimes E$. Generic injectivity does not imply saturation: multiplication by $\varpi$ on $\mathcal O$ is generically invertible but has nonsaturated image.

A geometric Ihara theorem can supply saturation for the two degeneracy maps on first cohomology of a compact quaternionic curve, but its full hypothesis list must travel with it. The quaternion algebra is a division algebra split at exactly one real place; the chosen proper component union is correspondence-stable and is represented at neat level or descended through a quotient of order prime to $\ell$; the changed prime is split, hyperspecial before the change, and away from $\ell$; the rank-two PEL datum there is unramified with self-dual lattice and the required flat incidence local model; $\mathcal O$ is finite over $\mathbb Z_\ell$ with $\ell\ge7$; the central character is trivial on the selected connected block; coefficients are constant; and the localization is non-Eisenstein. For a nontrivial local system, the arithmetic kernel consists of crossed homomorphisms rather than ordinary additive characters, so the constant-coefficient proof does not transfer formally.

Under precisely those curve hypotheses, residual injectivity of the combined two-map degeneracy morphism implies integral saturation. The implication is elementary once the residual theorem is known. Let $A$ be the source and $B$ the target, both finite free over $\mathcal O$. If the reduction of $A\to B$ is injective, Smith normal form over the DVR shows that every nonzero invariant factor is a unit: a factor divisible by $\varpi$ would create a residual kernel. Hence the integral map is injective and its cokernel is torsion-free. Localization at a Hecke idempotent preserves the conclusion because it takes direct summands.

Our totally definite class-set module is not that first-cohomology module. The geometric saturation theorem is therefore not silently transferred to it. In the regular Taylor--Wiles regime of Chapter 16, the unit Gram determinant gives a split injection and hence saturation directly. Outside that unit-determinant regime, saturation for definite modules must be proved by the finite groupoid calculation or by an explicit matrix argument; the curve theorem does not supply it. This boundary is part of dependency closure, not a technical inconvenience.

### 17.2 The Gram determinant

The determinant

$$
D_v=(q_v+1)^2-S_v^{-1}T_v^2
$$

measures failure of the old lattice to split orthogonally. Over a character on which $S_v$ has value $s_v$ and $T_v$ has value $t_v$, choose roots $\alpha_v,\beta_v$ with

$$
\alpha_v+\beta_v=t_v,
\qquad
\alpha_v\beta_v=q_vs_v.
$$

The identity

$$
s_vD_v=s_v(q_v+1)^2-(\alpha_v+\beta_v)^2
$$

is canonical, but in general it has no useful factorization purely in terms of the ordered roots without choosing further normalization. Signed factors are obtained from

$$
D_v=(q_v+1-S_v^{-1/2}T_v)(q_v+1+S_v^{-1/2}T_v)
$$

only after choosing a square root of $S_v$. The square root is not canonical. Consequently the determinant formula itself is the invariant integral statement; signed branch formulas require an explicit normalization and coefficient extension.

At a Taylor--Wiles prime $q_v\equiv1\pmod\ell$, reduction gives $q_v=1$ in $k$. Since $\bar s_v=\bar\alpha_v\bar\beta_v$, one obtains the canonical calculation

$$
\bar s_v\bar D_v
=4\bar\alpha_v\bar\beta_v-(\bar\alpha_v+\bar\beta_v)^2
=-(\bar\alpha_v-\bar\beta_v)^2.
$$

Thus distinct nonzero residual roots make $D_v$ a unit. This proves Condition 1 of Section 16.3 in the regular Taylor--Wiles situation. It does not prove the support-vanishing Condition 2.

### 17.3 The cases $q\equiv1$ and $q\equiv-1$

Two exceptional congruences must be separated.

When $q_v\equiv1\pmod\ell$, the two signed factors of a normalized Gram determinant can meet if the two roots coincide. The ordered local line is then not separated integrally, and the projector onto a chosen root requires division by $\alpha_v-\beta_v$. Regular distinct roots remove this failure, as the calculation above shows.

When $q_v\equiv-1\pmod\ell$, the diagonal term $q_v+1$ vanishes in the residue field. Both signed Gram factors can be nonunits, and branch-by-branch arguments that depend on one of $q_v+1\pm t$ being invertible can fail simultaneously. A full two-map saturation theorem may still remain valid, but it does not imply that either signed branch is integrally separated.

These facts are compatible rather than contradictory. Saturation of the combined map $d_0\oplus d_1$ is a statement about the whole old lattice. Integral separation of one root or sign is a stronger statement about an idempotent factor. The former can survive an exceptional congruence that destroys the latter.

### 17.4 Small residue characteristics and stabilizers

Finite quaternionic stabilizers can contain elements of orders $2$, $3$, $4$, $5$, or $6$, depending on the field and order, and this list is not exhaustive as the totally real base field varies. At any coefficient characteristic dividing an actual stabilizer order, that order is not a unit. Three consequences follow.

First, averaging over a stabilizer may be nonintegral, so invariant formation can fail to commute with reduction. Second, the mass pairing may have nonunit denominators and fail to be a perfect $\mathcal O$-pairing. Third, an effective stabilizer can map nontrivially to the diamond $\ell$-group, destroying the torsor.

There are three honest remedies: impose a neat level that removes effective stabilizers; pass to a projectively neat level while checking the central character; or state and verify directly that every effective stabilizer has order prime to $\ell$. Merely assuming that $\ell$ is odd does not exclude orders $3$ or $5$. Even $\ell\ge7$ is not a field-independent substitute for the stabilizer calculation: the exact projective stabilizers at the chosen level must be checked.

## 18. Compatible presentations without false transitions

### 18.1 Unrelated auxiliary sets

For each positive integer $N$, an auxiliary-prime construction may choose a set $Q_N$ with

$$
q_v\equiv1\pmod{\ell^N}
\qquad(v\in Q_N).
$$

There is usually no reason for $Q_N\subseteq Q_{N+1}$, and often the sets are deliberately chosen independently. Then the compact-open subgroups live at different adelic places. There is no inclusion

$$
U_{N+1}(Q_{N+1})\subseteq U_N(Q_N),
$$

no map of class sets, and no trace or pullback between the corresponding arithmetic modules.

An isomorphism

$$
\Delta_{Q_N,N}\cong(\mathbb Z/\ell^N\mathbb Z)^q
$$

does not change this. It identifies abstract finite groups after choosing generators; it does not identify local fields, level subgroups, or double cosets.

### 18.2 The common power-series source

Choose generators $\gamma_{i,N}$ of the $q$ cyclic diamond factors and put $z_i=[\gamma_{i,N}]-1$. There is a surjection

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]]
\twoheadrightarrow\Lambda_N
$$

with kernel

$$
\bigl((1+z_1)^{\ell^N}-1,\ldots,
(1+z_q)^{\ell^N}-1\bigr).
$$

**Proof.** The group ring of one cyclic factor is generated by $[\gamma]$ with relation $[\gamma]^{\ell^N}=1$. Writing $[\gamma]=1+z$ gives $(1+z)^{\ell^N}-1=0$. Tensoring the $q$ factors over $\mathcal O$ gives the displayed quotient. Completeness permits the map from the formal power-series ring, while the finite quotient makes every series reduce to a polynomial representative. $\square$

The exact exponent $\ell^N$ reflects the exact-level convention. Replacing it by an unspecified divisor would lose control of the augmentation cotangent directions.

### 18.3 What presentation compatibility proves

The common source puts every $\Lambda_N$-free module $P_N$ in the category of $S_\infty$-modules. It identifies the augmentation ideal with the image of $(z_1,\ldots,z_q)$, and it gives a common meaning to bounded numbers of generators and relations. In particular,

$$
P_N/(z_1,\ldots,z_q)P_N\cong P_N/\mathfrak a_NP_N.
$$

If exact minimal-level augmentation holds, this quotient is the fixed base module. Thus all finite modules share a common algebraic presentation even when their auxiliary places differ.

The generator choices are part of the presentation. Replacing $\gamma_{i,N}$ by a unit power changes $z_i$ by

$$
(1+z_i)^u-1,
$$

an automorphism of the formal group coordinate when $u\in\mathbb Z_\ell^\times$. The resulting source actions are equivalent after recording this coordinate change.

### 18.4 What it does not prove

The maps $S_\infty\twoheadrightarrow\Lambda_N$ do not give maps $P_{N+1}\to P_N$. Nor does a quotient map between the abstract groups, chosen after identifying both with standard products, give an arithmetic transition. A module map would require a correspondence between the underlying levels and compatibility with Hecke action and pairings.

Therefore there are two legitimate structures:

1. genuine transition maps $c_{m,n}$ inside one fixed $(Q,N)$-tower, as in Chapter 14;
2. compatible presentations over $S_\infty$ for independently chosen $Q_N$, with no claimed arithmetic transition.

Keeping these structures separate preserves all finite-level results while avoiding a fictitious inverse system.

## 19. Calculations and diagnostic examples

### 19.1 One diamond variable

Let $\Delta=\langle\gamma\rangle\cong\mathbb Z/\ell^n\mathbb Z$. Then

$$
\Lambda\cong\mathcal O[z]/((1+z)^{\ell^n}-1),
\qquad z=[\gamma]-1.
$$

Let a lower-level fiber carry a coefficient lattice $L$. Choose lifts $x_i=x_0\gamma^i$. A function is a tuple $(w_0,\ldots,w_{\ell^n-1})$, and the torsor isomorphism is

$$
(w_i)_i\longmapsto
\sum_{i=0}^{\ell^n-1}[\gamma^{-i}]\otimes w_i.
$$

The orbit sum is

$$
(w_i)_i\longmapsto\sum_iw_i.
$$

Its kernel is generated by neighboring differences. Indeed,

$$
(0,\ldots,w,-w,\ldots,0)
$$

is the translate of $(\gamma-1)$ times a one-point function, and every tuple of sum zero is a sum of such differences. This gives a concrete proof that the kernel is $zM$.

The invariant tuple is $(w,w,\ldots,w)$. Orbit sum sends it to $\ell^nw$, whereas norm sends the coinvariant class of $(w,0,\ldots,0)$ to that invariant tuple. This explicitly distinguishes augmentation, trace, pullback, and norm.

### 19.2 A central-kernel failure

Let $\Delta=C_\ell$ act nominally on a one-point class set, and suppose its generator is represented by a central scalar on which the fixed central character is trivial. Then the automorphic module is $M=\mathcal O$ with trivial $\Delta$-action.

If $M$ were free of positive rank $r$ over $\mathcal O[C_\ell]$, its $\mathcal O$-rank would be $\ell r$. Since $M$ has rank one, this is impossible. More intrinsically, $(\gamma-1)M=0$, while $\gamma-1\ne0$ in the group ring and does not annihilate a free module.

The effective diamond group is trivial in this example. Over its group ring $\mathcal O$, the module is free of rank one and exact augmentation is tautological. Thus passing to the effective group repairs the theorem but also lowers the number of diamond variables. Claiming the nominal rank would be false.

### 19.3 A nonfree stabilizer fiber

Let $\Delta=C_{\ell^2}$ and let $H\subset\Delta$ have order $\ell$. A fiber with stabilizer $H$ is $H\backslash\Delta$, which has $\ell$ points. Its function module has $\mathcal O$-rank $\ell$.

No nonzero free $\mathcal O[\Delta]$-module has this rank, because the regular module has $\mathcal O$-rank $\ell^2$. The permutation module is instead

$$
\operatorname{Ind}_H^\Delta\mathcal O
\cong\mathcal O[\Delta]\otimes_{\mathcal O[H]}\mathcal O.
$$

Its annihilator contains the norm relation coming from $H$, and its coinvariants have rank one just as a free rank-one module would. Thus correct augmentation rank alone does not detect the failure of group-ring freeness; the stabilizer calculation does.

### 19.4 A primary--companion calculation

Let $A$ be a complete local $\mathcal O$-algebra and suppose $t,s\in A$, with $s$ a unit. Let

$$
F(Y)=Y^2-tY+qs
$$

have roots $\alpha,\beta\in A$ satisfying $\alpha-\beta\in A^\times$. The projectors on a module where $F(U)=0$ are

$$
e_\alpha=\frac{U-\beta}{\alpha-\beta},
\qquad
e_\beta=\frac{U-\alpha}{\beta-\alpha}.
$$

One checks directly that

$$
e_\alpha+e_\beta=1,
\qquad
e_\alpha e_\beta=0,
\qquad
e_\alpha^2=e_\alpha.
$$

For the last identity,

$$
(U-\beta)^2-(\alpha-\beta)(U-\beta)
=(U-\alpha)(U-\beta)=F(U)=0.
$$

If the adjoint satisfies $U^*=qsU^{-1}$, then on the $\alpha$-factor it acts by $qs/\alpha=\beta$. Hence $e_\alpha^*=e_\beta$ on the dual module. A perfect pairing therefore restricts between the $\alpha$-primary module and the $\beta$-companion module, while the two primary $\alpha$-factors are orthogonal unless an additional self-duality identifies them.

This explicit formula is available only when actual roots in $A$ with unit difference have been chosen. The residual-idempotent construction of Chapter 11 works more generally and is the integral definition.

## 20. Paired definite Taylor--Wiles modules

The preceding construction treats one integral coefficient system and its adjoint companion.
There is a second situation, logically different from adjoint duality, in which two systems must
be carried at once.  Their characteristic-zero local types can differ, while their reductions
describe the same residual packet.  Principal-series and Iwahori coefficient lattices, or desired
and avoidance lattices, are typical examples.  A comparison can use the common special fiber
only if the common residual module is an actual identified module, rather than two vector spaces
of the same dimension.

This chapter proves the definite-module statement that makes such a paired construction
possible.  The proof has two independent ingredients.  Prime-to-$\ell$ stabilizers make taking
sections commute with coefficient reduction.  The free diamond action then makes each integral
system a regular group-ring module.  Their common residual packet synchronizes the two ranks and,
when nonzero, proves that the common rank is positive for the fixed auxiliary set.  Uniformity as
the auxiliary set varies is a separate conclusion proved only under the hypotheses of
Proposition 20.6.

### 20.1 Two coefficient systems on one class groupoid

Fix a finite active set $P$, disjoint from the Taylor--Wiles set $Q$.  The compact open away from
$Q$ is the same for both systems; in particular, the finite class groupoids

$$
\mathscr X_n=
[D^\times\backslash D_f^\times/(U_n(Q)Z_f)]
\tag{20.1}
$$

are common.  The brackets emphasize that isotropy and the central coefficient line are retained.

Before choosing either coefficient system, attach to an object $x$ represented by $g$ the
projective arithmetic stabilizer

$$
\Gamma_{x,n}^{\mathrm{proj}}
=\bigl(D^\times\cap gU_n(Q)Z_fg^{-1}\bigr)/F^\times.
$$

This is a finite group depending only on the quaternion algebra, the level, and the object.  It
does not depend on a central character or on an active coefficient lattice.  We assume

$$
\ell\nmid |\Gamma_{x,n}^{\mathrm{proj}}|
\quad\text{for every object and every depth under consideration.}
\tag{20.2}
$$

Effective neatness implies (20.2), but the prime-to-$\ell$ order is the exact hypothesis needed
for reduction of invariants.

Now index the two coefficient systems by $\varepsilon\in\{\mathrm d,\mathrm a\}$, for desired
and avoidance.

At every $v\in P$, let $L_v^\varepsilon$ be a finite free $\mathcal O$-lattice with a right action
of the active compact group.  Put

$$
L^\varepsilon=\bigotimes_{v\in P}L_v^\varepsilon,
\qquad
V^\varepsilon=W\otimes_{\mathcal O}L^\varepsilon.
\tag{20.3}
$$

The active compact acts on the second factor and commutes with the algebraic action on $W$.  It
acts trivially at the places of $Q$.  This last clause is what makes the coefficient lattice
constant along a diamond fiber.

Allow central characters $\chi_f^\varepsilon$ which can differ in characteristic zero but have a
common reduction $\bar\chi_f$.  With the right-action convention, an exact form satisfies

$$
f(\gamma g u z)
=\chi_f^\varepsilon(z)\rho(\gamma)
\bigl(f(g)\cdot u_P\bigr).
\tag{20.4}
$$

For $z_0\in U\cap Z_f$, consistency of the two presentations obtained from
$u=z_0,z=z_0^{-1}$ is exactly

$$
w\cdot z_{0,P}=\chi_f^\varepsilon(z_0)w.
\tag{20.5}
$$

Thus the central character is part of the coefficient system, not an operator added after
forming the class set.  The rational central compatibility with $\rho$ remains the one fixed in
Section 2.2.

Suppose now that there are marked isomorphisms

$$
\bar\iota_v:
L_v^{\mathrm d}/\varpi L_v^{\mathrm d}
\xrightarrow{\sim}
L_v^{\mathrm a}/\varpi L_v^{\mathrm a}
\qquad(v\in P).
\tag{20.6}
$$

They are required to intertwine the active compact actions, the reduced central characters, and
every selected active local intertwiner.  Tensoring them gives a common residual coefficient
lattice $\bar V$.  Equivalently, the two coefficient systems on $\mathscr X_n$ have a marked
isomorphism after reduction.  This formulation is intrinsic: replacing local tensor
factorizations by any two finite free coefficient systems with the same marked residual system
changes none of the arguments below.

For a tame principal-series lattice compared with its trivial-character companion, (20.6) is the
familiar phenomenon that the tame character becomes trivial modulo $\varpi$.  What matters here
is not the name of the local representations, but the equivariance of the marked reduction.  An
isomorphism of the underlying $k$-modules which forgets the active compact or the center is
insufficient.

The coefficient actions are applied only after the common group
$\Gamma_{x,n}^{\mathrm{proj}}$ has been fixed.  If
$\gamma gu z=g$, formula (20.4) defines

$$
\sigma_{x,n}^\varepsilon([\gamma])w
=\chi_f^\varepsilon(z)\rho(\gamma)(w\cdot u_P)
$$

on $V^\varepsilon$.  Changing $\gamma$ by a rational scalar does not change this operator by the
rational central compatibility, and changing the decomposition of the same stabilizer element
does not change it by (20.5).  Thus $\sigma_{x,n}^\varepsilon$ is a representation of the one
coefficient-independent projective group.  The two representations can differ integrally, while
(20.6) identifies their reductions.

### 20.2 The intrinsic common residual module

Let $\mathscr V_n^\varepsilon$ denote the coefficient system on $\mathscr X_n$ obtained from
$V^\varepsilon$, and let $\bar{\mathscr V}_n$ be their marked common reduction.  Define

$$
M_n^\varepsilon=H^0(\mathscr X_n,\mathscr V_n^\varepsilon),
\qquad
\bar M_n=H^0(\mathscr X_n,\bar{\mathscr V}_n).
\tag{20.7}
$$

The second module is the **common residual module**.  It is not defined by choosing one of the
two integral modules and declaring the other to be congruent to it.  It is the module of sections
of the common residual coefficient system on the common residual class groupoid.

**Proposition 20.1 (common residual sections).** Under (20.2), the marked local reductions induce
canonical isomorphisms

$$
M_n^{\mathrm d}/\varpi M_n^{\mathrm d}
\xrightarrow{\sim}\bar M_n
\xleftarrow{\sim}
M_n^{\mathrm a}/\varpi M_n^{\mathrm a}
\tag{20.8}
$$

at every depth $n$.  These isomorphisms respect the reduced central character and are independent
of class representatives.

**Proof.** Choose one representative for each isomorphism class in $\mathscr X_n$.  The stabilizer
formula of Proposition 2.1, with the active coefficient action included, gives

$$
M_n^\varepsilon
\cong\bigoplus_x(V^\varepsilon)^{\Gamma_{x,n}^{\mathrm{proj}}},
$$

where the action on the $\varepsilon$-summand is $\sigma_{x,n}^\varepsilon$.  Condition (20.2)
makes the Reynolds operator

$$
e_{x,n}^\varepsilon
=\frac{1}{|\Gamma_{x,n}^{\mathrm{proj}}|}
\sum_{\gamma\in\Gamma_{x,n}^{\mathrm{proj}}}
\sigma_{x,n}^\varepsilon(\gamma)
$$

an integral idempotent.  Hence
$(V^\varepsilon)^{\Gamma_{x,n}^{\mathrm{proj}}}=e_{x,n}^\varepsilon V^\varepsilon$ is a direct
summand, and idempotent base change gives

$$
(V^\varepsilon)^{\Gamma_{x,n}^{\mathrm{proj}}}\otimes_{\mathcal O}k
\xrightarrow{\sim}
(V^\varepsilon\otimes_{\mathcal O}k)^{\Gamma_{x,n}^{\mathrm{proj}}}.
$$

The map $\bar\iota=1_{\bar W}\otimes\bigotimes_v\bar\iota_v$ intertwines the stabilizer actions,
including the common reduced central line, and therefore identifies the two right sides.  Taking
the direct sum over $x$ proves (20.8).  A change of representative conjugates both the stabilizer
and its Reynolds idempotent, so the resulting isomorphism is intrinsic. $\square$

We next localize without losing the marked identification.  Choose a finite commutative family of
named Hecke and active intertwining operators which is defined on both systems and has the same
reduction under (20.8).  Let $\bar{\mathbb T}^{\mathrm{com}}$ be its image on
$\bigoplus_{n=0}^N\bar M_n$, and choose a maximal ideal $\bar{\mathfrak m}$ in the support of
$\bar M_0$.  Put

$$
\bar P_n=(\bar M_n)_{\bar{\mathfrak m}}.
\tag{20.9}
$$

On each integral side, let $\mathfrak m^\varepsilon$ be the inverse image of
$\bar{\mathfrak m}$ in the finite integral acting algebra on $\bigoplus_nM_n^\varepsilon$, and
let $e^\varepsilon$ be its primary idempotent.  Define

$$
P_n^\varepsilon=e^\varepsilon M_n^\varepsilon.
\tag{20.10}
$$

The reduction of either integral image algebra surjects onto
$\bar{\mathbb T}^{\mathrm{com}}$.  Its kernel is nilpotent.  To see this, pass to the
finite-dimensional commutative algebra modulo $\varpi$.  If the kernel were not nilpotent, its
image in the semisimple quotient would contain a nonzero idempotent.  Lifting that idempotent to
the complete integral image algebra would give an idempotent $e$ satisfying
$eM\subseteq\varpi M$.  But then $eM=e^2M\subseteq\varpi eM$, so Nakayama's lemma gives $eM=0$,
contrary to faithfulness of the image algebra.  Idempotents lift uniquely through this nilpotent
kernel and through the $\varpi$-adic filtration.  Thus $e^{\mathrm d}$ and $e^{\mathrm a}$ both
reduce to the idempotent of the $\bar{\mathfrak m}$-factor.  Proposition 20.1 now gives

$$
P_n^{\mathrm d}/\varpi P_n^{\mathrm d}
\xrightarrow{\sim}\bar P_n
\xleftarrow{\sim}
P_n^{\mathrm a}/\varpi P_n^{\mathrm a}.
\tag{20.11}
$$

Using the finite image on the direct sum of all depths is important.  It makes the idempotents
compatible with orbit sum and prevents separately chosen localizations from selecting different
residual packets.

### 20.3 Synchronized freeness and positive rank

The common reduction synchronizes ranks only after each integral module has been proved free over
the diamond algebra.  That freeness still comes from the class-set torsor.

**Proposition 20.2 (synchronized diamond freeness and positive rank).** Assume that the underlying
level datum is clean through depth $N$, that (20.2) holds, and that the active coefficient systems
are constant along the $Q$-diamond fibers.  Write

$$
\Lambda_n=\mathcal O[\Delta_{Q,n}].
$$

Then, for $\varepsilon\in\{\mathrm d,\mathrm a\}$, the localized module $P_n^\varepsilon$ is
finite free over $\Lambda_n$.  Both sides have the same fixed-$Q$ rank

$$
r_Q=\dim_k\bar P_0.
\tag{20.12}
$$

In particular, if one localized residual eigenpacket occurs, meaning $\bar P_0\ne0$, then
$r_Q>0$ and both integral systems have positive diamond rank.

**Proof.** For a lower-level class $x$, put

$$
L_x^\varepsilon=(V^\varepsilon)^{\Gamma_{x,0}^{\mathrm{proj}}}.
$$

Theorem 5.1 makes the fine fiber above $x$ a free $\Delta_{Q,n}$-orbit.  The coefficient system
is constant on that orbit, because the Taylor--Wiles level is disjoint from $P$ and acts trivially
on $V^\varepsilon$.  Consequently the orbit decomposition is

$$
M_n^\varepsilon
\cong\bigoplus_x
\operatorname{Map}(\Delta_{Q,n},L_x^\varepsilon)
\cong\Lambda_n\otimes_{\mathcal O}M_0^\varepsilon.
$$

Condition (20.2) makes each $L_x^\varepsilon$ an $\mathcal O$-direct summand of
$V^\varepsilon$, hence finite free.  The displayed decomposition therefore makes
$M_n^\varepsilon$ finite free over $\Lambda_n$.  Since the primary idempotent commutes with
diamonds, $P_n^\varepsilon=e^\varepsilon M_n^\varepsilon$ is a projective
$\Lambda_n$-module.  The ring $\Lambda_n$ is local by Proposition 6.3, so $P_n^\varepsilon$ is
free.

On every regular summand, orbit sum is $\epsilon\otimes1$ and has kernel the augmentation ideal
times that summand.  Applying $e^\varepsilon$ preserves this exact sequence and shows that the
$\mathcal O$-rank of the augmentation quotient is
$\operatorname{rank}_{\mathcal O}P_0^\varepsilon$.  A finite free $\Lambda_n$-module has
group-ring rank equal to the $\mathcal O$-rank of its augmentation quotient, so these two ranks
are equal.

Now (20.11) at depth zero gives

$$
\operatorname{rank}_{\mathcal O}P_0^\varepsilon
=\dim_k(P_0^\varepsilon/\varpi P_0^\varepsilon)
=\dim_k\bar P_0.
$$

This proves the common value (20.12).  If $\bar P_0$ is nonzero, its dimension is positive, so
both ranks are positive.  No generic-rank argument has been used: positivity comes from the one
marked residual packet which occurs on both sides. $\square$

The last point is essential in paired patching.  A characteristic-zero component can disappear
after localization, and a nonzero module on one side says nothing about the other side unless the
residual packet has been identified before localization.

### 20.4 Coinvariants, saturation, and minimal control

Let $c_{n,0}^\varepsilon:P_n^\varepsilon\to P_0^\varepsilon$ be orbit sum.  Since the same
diamond fiber is used on both sides, the two maps reduce to one residual orbit sum
$\bar c_{n,0}:\bar P_n\to\bar P_0$.

**Proposition 20.3 (exact paired augmentation).** Under the hypotheses of Proposition 20.2,
orbit sum gives exact sequences

$$
0\longrightarrow\mathfrak a_nP_n^\varepsilon
\longrightarrow P_n^\varepsilon
\xrightarrow{c_{n,0}^\varepsilon}P_0^\varepsilon
\longrightarrow0,
\tag{20.13}
$$

and the submodule $\mathfrak a_nP_n^\varepsilon$ is saturated as an $\mathcal O$-submodule.
Reduction of (20.13) is the common sequence

$$
0\longrightarrow\bar{\mathfrak a}_n\bar P_n
\longrightarrow\bar P_n
\xrightarrow{\bar c_{n,0}}\bar P_0
\longrightarrow0.
\tag{20.14}
$$

Thus the two augmentation isomorphisms

$$
P_n^\varepsilon/\mathfrak a_nP_n^\varepsilon
\xrightarrow{\sim}P_0^\varepsilon
\tag{20.15}
$$

commute with the marked common residual identification.

**Proof.** On the summand
$\operatorname{Map}(\Delta_{Q,n},L_x^\varepsilon)$, orbit sum is
$\epsilon\otimes1$.  Its kernel is the augmentation ideal times that regular module and its
image is $L_x^\varepsilon$.  Taking direct sums and applying the common primary idempotent proves
(20.13).  The quotient $P_0^\varepsilon$ is finite free over the DVR, so the kernel is saturated:

$$
(\mathfrak a_nP_n^\varepsilon\otimes_{\mathcal O}E)
\cap P_n^\varepsilon
=\mathfrak a_nP_n^\varepsilon.
$$

Reduction is therefore exact.  Proposition 20.1 identifies the reductions of the source and
target, and the orbit-sum formula is termwise identical on the two coefficient systems.  This
gives (20.14) and the compatibility of (20.15). $\square$

Pullback identifies $P_0^\varepsilon$ with $(P_n^\varepsilon)^{\Delta_{Q,n}}$, while the norm
identifies coinvariants with invariants.  These are two different identifications.  The composite
of raw pullback and raw orbit sum remains multiplication by $|\Delta_{Q,n}|$.  No averaging by
this nonunit is used.  This is precisely why the regular-module calculation proves integral
coinvariant control while a comparison of invariants alone would not.

The unconditional endpoint of (20.15) is the oriented module.  Suppose in addition that, for
each $\varepsilon$, the unit Gram determinant, regular root, and selected-support hypotheses of
Theorem 16.1 hold at every auxiliary prime, and suppose the resulting minimal coefficient
systems also have a marked common reduction.  Then the control isomorphisms

$$
P_0^\varepsilon\xrightarrow{\sim}P_{\min}^\varepsilon
\tag{20.16}
$$

commute with reduction.  Indeed, the degeneracy maps and their reverse correspondences are formed
from the same double-coset representatives, so the marked local lattice maps intertwine their
matrices.  If $A^\varepsilon$ is the selected degeneracy map and
$G^\varepsilon=(A^\varepsilon)^\vee A^\varepsilon$ is its Gram operator, Theorem 16.1 constructs
the inverse on selected support as
$(G^\varepsilon)^{-1}(A^\varepsilon)^\vee$.  The determinant of $G^\varepsilon$ is a unit, hence
matrix inversion commutes with reduction.  The two control isomorphisms therefore reduce to the
same residual isomorphism.
Composing (20.15) with (20.16) gives exact minimal-level augmentation on both sides and a common
residual minimal module.  Without the selected-support hypothesis, (20.15) remains exact but
(20.16) must not be inserted: diamond coinvariants stop at oriented level.

### 20.5 Hecke operators, pairings, and partial frames

The residual identification must carry all marked structure, not merely the underlying modules.
The following proposition records why the local hypotheses above are sufficient.

**Proposition 20.4 (compatibility of the marked structures).** Assume the hypotheses of
Proposition 20.2.  Suppose also that every active local comparison (20.6) intertwines the
reduction of the selected local intertwiners.  Then the isomorphisms (20.11) commute with:

1. every away Hecke operator in the common named family;
2. every selected active local intertwiner;
3. diamond operators, pullback, orbit sum, and norm; and
4. the minimal degeneracy maps whenever the extra hypotheses giving (20.16) hold.

If both integral systems have companion coefficient systems with perfect pairings, and the
primary and companion residual identifications are isometries for one common residual coefficient
pairing, then their group-ring-valued pairings reduce to one perfect pairing

$$
\bar{\mathcal H}_n:\bar P_n\times\bar C_n
\longrightarrow k[\Delta_{Q,n}].
\tag{20.17}
$$

The named Hecke adjoints agree under this identification.

**Proof.** An away Hecke operator is a finite sum of right translations by representatives whose
$P$- and $Q$-components are fixed.  Apply the residual lattice isomorphism to the value of a form
after each translation.  It commutes term by term with the sum.  At an active place the same
argument uses the assumed intertwining of the local lattice map.  Diamonds are right translations
at $Q$ and act trivially on the active coefficient lattice, so the two actions are literally the
same after reduction.  Pullback is precomposition, orbit sum and norm are sums over that same
action, and hence all three commute with reduction.  The assertion about degeneracy maps follows
from their common right-coset formulas.

For pairings, use on corresponding classes the common reduced coefficient pairing.  Every term in
the defining sum of Section 13.1 agrees after reduction, including the inverse diamond in the
second argument.  This gives (20.17).  Perfectness follows either by reducing the block-permutation
matrix of Theorem 13.2 or by base change of its adjoint isomorphism.  The equality of adjoints is
then forced by perfectness and the equality of the operator actions. $\square$

Partial frames do not alter this conclusion, but their role must be stated exactly.  Let

$$
\mathcal O_T=\mathcal O[[w_1,\ldots,w_c]]
\tag{20.18}
$$

be the power-series ring in the declared partial-frame coordinates, with the same ordered
coordinates on both systems.  Define the framed modules by genuine scalar extension:

$$
P_{n,T}^\varepsilon
=\mathcal O_T\widehat\otimes_{\mathcal O}P_n^\varepsilon,
\qquad
C_{n,T}^\varepsilon
=\mathcal O_T\widehat\otimes_{\mathcal O}C_n^\varepsilon.
\tag{20.19}
$$

Then $P_{n,T}^\varepsilon$ and $C_{n,T}^\varepsilon$ are free of rank $r_Q$ over
$\mathcal O_T[\Delta_{Q,n}]$, all augmentation and pairing statements base change exactly, and
modulo $\varpi$ the two framed systems have the common module
$k[[w_1,\ldots,w_c]]\widehat\otimes_k\bar P_n$.  The variables $w_i$ occur once; they are
smooth frame coordinates, not diamond variables.  A ring-level framed presentation without the
scalar-extension identity (20.19) would not imply any of these module statements.

### 20.6 The paired definite module theorem

We can now package the result in the form needed whenever two local deformation sources have one
residual special fiber.

**Theorem 20.5 (paired definite Taylor--Wiles module theorem).** Fix one Taylor--Wiles set $Q$.
Let two exact active coefficient systems on the common definite class groupoids (20.1) satisfy the marked residual comparison
(20.6), the central compatibility (20.5), and the prime-to-$\ell$ stabilizer condition (20.2).
Let a clean Taylor--Wiles level of depth $N$ be disjoint from the active set.  Choose one common
residual Hecke packet $\bar{\mathfrak m}$ with

$$
\bar P_0\ne0,
\tag{20.20}
$$

and form the compatible primary factors (20.10).  Suppose the declared companion coefficient
systems satisfy the same clean and marked residual hypotheses, and that the primary--companion
pairings are perfect integrally and after the marked reduction, as in Proposition 20.4.  For each
$n$ and $\varepsilon$, let $\mathbb T_n^\varepsilon$ be the finite $\mathcal O$-algebra which is
the image on $P_n^\varepsilon$ of $\Lambda_n$ together with the compatible named generators.

Then the desired and avoidance systems supply the following paired finite-level data.

1. Their reductions are the same intrinsic localized module $\bar P_n$, with the same reduced
   Hecke, active-intertwiner, diamond, and central-character actions.
2. Both $P_n^{\mathrm d}$ and $P_n^{\mathrm a}$ are free of the same positive rank
   $r_Q=\dim_k\bar P_0$ over $\Lambda_n$.
3. Orbit sum gives compatible exact and saturated module augmentations

   $$
   P_n^\varepsilon/\mathfrak a_nP_n^\varepsilon
   \xrightarrow{\sim}P_0^\varepsilon.
   $$

   If the separately stated minimal-level control hypotheses hold, $P_0^\varepsilon$ may be
   replaced by $P_{\min}^\varepsilon$ on both sides.
4. Each primary module is perfectly paired with its declared companion over $\Lambda_n$.  Thus
   the companion is also free of rank $r_Q$, its orbit-sum augmentation is exact and saturated, the
   two pairings reduce to (20.17), and all named Hecke operators have the declared adjoints.
5. The action on the recovered module $P_0^\varepsilon$ has finite image
   $\mathbb T_0^\varepsilon\subseteq\operatorname{End}_{\mathcal O}(P_0^\varepsilon)$.
   Compatible generators give a canonical surjection

   $$
   \mathbb T_n^\varepsilon/
   \mathfrak a_n\mathbb T_n^\varepsilon
   \twoheadrightarrow\mathbb T_0^\varepsilon,
   \tag{20.21}
   $$

   but no injectivity is asserted without the saturation condition of Section 20.7.
6. The same conclusions hold after the genuine partial-frame scalar extension (20.19), with no
   change in diamond rank and with the frame variables retained in the common residual marking.

**Proof.** Proposition 20.1 constructs the common residual sections and shows that localization
commutes with reduction.  Proposition 20.2 proves synchronized positive-rank diamond freeness from
the free fine-level action.  Proposition 20.3 proves exact saturated augmentation and states the
additional minimal-level criterion.  Proposition 20.4 supplies Hecke, diamond, pairing, adjoint,
and frame compatibility.

It remains only to justify the finiteness assertion.  The recovered module is finite free over
$\mathcal O$, so its endomorphism ring is finite free.  The image of the named commutative Hecke
family is an $\mathcal O$-submodule of that endomorphism ring and is therefore finite and
torsion-free.  The high-level generators act on coinvariants through their named recovered
operators, so their image is $\mathbb T_0^\varepsilon$; this proves the surjection (20.21).
$\square$

The theorem is deliberately a fixed-$Q$ statement.  Its formula
$r_Q=\dim_k\bar P_0(Q)$ does not compare $\bar P_0(Q)$ with
$\bar P_0(Q')$ for a different auxiliary set.  Uniformity across varying Taylor--Wiles sets
requires a separate argument.

**Proposition 20.6 (uniform ranks and retention for varying auxiliary sets).** Let
$Q_N$ be a sequence of ordered paired Taylor--Wiles sets of one fixed cardinality, with the common
exact diamond quotients and power-series source of Book 144, and apply Theorem 20.5 to $Q_N$
through depth $N$.  Suppose $\bar P_{Q_N,0}\ne0$ for every $N$, and put

$$
r_N
=\operatorname{rank}_{\Lambda_{Q_N,N}}P_{Q_N,N}^{\mathrm d}
=\operatorname{rank}_{\Lambda_{Q_N,N}}P_{Q_N,N}^{\mathrm a}
=\dim_k\bar P_{Q_N,0}.
\tag{20.22}
$$

The following are honest routes to the uniform-rank input of Book 144.

1. Let $U^{\mathrm{base}}$ be a fixed compact open containing every oriented level
   $U_0(Q_N)$.  Put

   $$
   b=\#\bigl(D^\times\backslash D_f^\times/(U^{\mathrm{base}}Z_f)\bigr),
   \qquad
   I_N=[U^{\mathrm{base}}:U_0(Q_N)],
   $$

   and let $d_V$ be the common $\mathcal O$-rank of $V^{\mathrm d}$ and
   $V^{\mathrm a}$.  Then

   $$
   1\le r_N\le d_VbI_N.
   \tag{20.23}
   $$

   In particular, a uniform bound on the level indices gives a uniform bound on the ranks.
2. Alternatively, suppose the conditional control isomorphisms (20.16) hold for every $Q_N$
   and identify the oriented modules with fixed minimal modules
   $P_{\min}^{\varepsilon}$ independent of $N$.  Then

   $$
   r_N=\operatorname{rank}_{\mathcal O}P_{\min}^{\varepsilon}
   $$

   for every $N$ and either value of $\varepsilon$; hence the ranks are already one fixed positive
   integer.
3. More generally, assume only that the positive integers $r_N$ are bounded.  Then there is a
   cofinal subsequence $N_1<N_2<\cdots$ on which $r_N$ is one fixed value $r\ge1$.  Suppose in
   addition that the uniform source-presentation hypotheses of Book 144, Proposition 10.1 hold,
   and that every pairing and exact sequence intended as a mark descends to the chosen finite
   truncations.  The subsequence can then be refined so that all paired residual identifications,
   diamond labels, partial frames, named Hecke operators, pairings, adjoints, and module
   augmentations occur in compatible finite marked shadows.  This refined sequence supplies the
   fixed-rank input of Book 144, Theorem 18.2.

**Proof.** The common residual identification at each $N$ proves all equalities in (20.22), and
nonvanishing proves the lower bound.  Projection from the oriented class set to the class set at
$U^{\mathrm{base}}$ has fibers of cardinality at most $I_N$.  Hence the oriented class groupoid
has at most $bI_N$ isomorphism classes of objects.  Evaluation embeds its full section module in
a direct sum of at most $bI_N$ copies of $V^\varepsilon$.  Localization is a direct summand, so

$$
r_N
=\operatorname{rank}_{\mathcal O}P_{Q_N,0}^\varepsilon
\le \operatorname{rank}_{\mathcal O}M_{Q_N,0}^\varepsilon
\le d_VbI_N,
$$

which proves (20.23).  This estimate also shows its own limitation: for standard Iwahori levels
the indices $I_N$ can grow with the norms of the primes in $Q_N$, so boundedness is not a formal
consequence of fixed cardinality of $Q_N$.

Under the hypotheses in part 2, fixed-$Q$ augmentation followed by (20.16) identifies
$P_{Q_N,N}^\varepsilon/\mathfrak a_NP_{Q_N,N}^\varepsilon$ with the fixed minimal module.
Taking ranks proves the displayed constant formula.  This use of minimal control is conditional
on the unit Gram determinant, regular-root, and selected-support hypotheses already stated in
Section 20.4.

For part 3, a bounded sequence of positive integers takes some value $r$ infinitely often; its
infinite level set is cofinal.  Restrict to that set.  At any fixed precision, rank-$r$ freeness
gives a uniform number of module generators, while the assumed source-presentation bounds give
fixed finite source quotients.  Over the finite residue field there are therefore only finitely
many paired diagrams with the prescribed marks.  Choose an infinite subset on which the
precision-one diagram is constant, then an infinite subset on which the precision-two diagram
and its reduction are constant, and continue.  The diagonal subsequence has compatible reduction
maps between its stabilized shadows.  By placing the first $d$ members of every countable named
family in the precision-$d$ diagram, every fixed mark is retained from some stage onward.
Pairings and exact sequences are included only under the descent hypothesis in the statement, so
the diagonal argument does not silently assert preservation under a nonflat truncation.  This is
the required synchronized fixed-rank family. $\square$

Thus exact auxiliary data from Book 143 may be combined with Theorem 20.5 at every level, but
Book 144 receives a Taylor--Wiles system only after Proposition 20.6 has supplied uniform rank
and the stated finite-shadow bounds.  The resulting maps between shadows are presentation maps;
they are not arithmetic transitions between unrelated sets $Q_N$.

### 20.7 Recovered actions and the saturation boundary

The module theorem gives enough information to identify the action seen at finite level.  It does
not turn topological support into scheme-theoretic faithfulness and does not make formation of an
acting image commute with augmentation.

**Proposition 20.7 (source support gives a nilpotent kernel).** Let $B^\varepsilon$ be a Noetherian
source ring acting on the recovered finite module $P_0^\varepsilon$, and let

$$
B^\varepsilon\longrightarrow\mathbb T_0^\varepsilon
\lhook\joinrel\longrightarrow
\operatorname{End}_{\mathcal O}(P_0^\varepsilon)
\tag{20.24}
$$

be the factorized action.  If a source-support theorem supplies

$$
\operatorname{Supp}_{B^\varepsilon}P_0^\varepsilon
=\operatorname{Spec}B^\varepsilon,
\tag{20.25}
$$

then the kernel of $B^\varepsilon\to\mathbb T_0^\varepsilon$ is nilpotent.

**Proof.** Faithfulness of the image algebra makes the kernel equal to
$\operatorname{Ann}_{B^\varepsilon}(P_0^\varepsilon)$.  Equation (20.25) says that the vanishing
set of this annihilator is the whole spectrum, so the annihilator lies in the nilradical.  A
nilradical in a Noetherian ring is nilpotent. $\square$

Thus an independent source-support theorem yields precisely a nilpotent kernel for the recovered finite
action.  It yields an injective action only after reducedness or another nilpotent-sensitive
criterion has been proved.

There is a clean stronger statement for the acting image itself.  Put

$$
\mathcal E_n^\varepsilon
=\operatorname{End}_{\Lambda_n}(P_n^\varepsilon).
$$

The augmentation-saturation condition is

$$
\mathbb T_n^\varepsilon\cap
\mathfrak a_n\mathcal E_n^\varepsilon
=\mathfrak a_n\mathbb T_n^\varepsilon.
\tag{20.26}
$$

This is the finite-level form of the criterion proved in Book 145, Section 7.3.

**Corollary 20.8 (exact acting-image augmentation under saturation).** Under the hypotheses of
Theorem 20.5, if (20.26) holds, then the surjection (20.21) is an isomorphism:

$$
\mathbb T_n^\varepsilon/
\mathfrak a_n\mathbb T_n^\varepsilon
\xrightarrow{\sim}\mathbb T_0^\varepsilon.
\tag{20.27}
$$

The same conclusion holds after partial-frame scalar extension when the corresponding framed
inclusion is saturated.

**Proof.** Freeness of $P_n^\varepsilon$ gives

$$
\mathcal O\otimes_{\Lambda_n}\mathcal E_n^\varepsilon
\xrightarrow{\sim}
\operatorname{End}_{\mathcal O}(P_0^\varepsilon).
$$

The image of the base-changed Hecke algebra is $\mathbb T_0^\varepsilon$.  The kernel of
(20.21) is therefore

$$
\frac{\mathbb T_n^\varepsilon\cap
\mathfrak a_n\mathcal E_n^\varepsilon}
{\mathfrak a_n\mathbb T_n^\varepsilon},
$$

which vanishes by (20.26).  Scalar extension proves the framed statement. $\square$

Without (20.26), Theorem 20.5 gives the module isomorphism (20.15), the finite recovered action,
and only the canonical surjection (20.21).  This is the exact boundary needed for paired source
patching: module control is unconditional under the definite hypotheses, while acting-image
control retains its separate saturation hypothesis.

### 20.8 Three indispensable failure tests

The hypotheses of Theorem 20.5 exclude three failures which no rank calculation can repair.

**A nonfree stabilizer orbit.**  Let $\Delta=C_{\ell^2}$ and let a subgroup
$H\simeq C_\ell$ stabilize a fine-level point.  The fiber is $H\backslash\Delta$ and its function
module has $\mathcal O$-rank $\ell$, whereas every nonzero free $\mathcal O[\Delta]$-module has
rank divisible by $\ell^2$.  Its coinvariants still have rank one.  Thus a plausible
augmentation quotient does not detect the hidden isotropy; the free-action calculation does.

**Loss of a residual component after localization.**  Let
$\bar A=k\times k$ and let the desired residual module be $k\oplus k$, while the avoidance
residual module is $0\oplus k$.  Both unlocalized systems are nonzero.  Localization at the first
maximal ideal leaves a nonzero desired module and kills the avoidance module.  Consequently
nonvanishing on one side, or equality of some unlocalized generic ranks, cannot prove paired
positivity.  The marked common residual module (20.9) rules out this example: the same nonzero
localized packet occurs in both reductions before either integral rank is computed.

**Coinvariants do not determine the acting image.**  Let

$$
\Lambda=\mathcal O[C_\ell],
\qquad s=[g]-1,
\qquad P=\Lambda^2,
$$

and let $u=sE_{12}\in\operatorname{End}_{\Lambda}(P)$.  The algebra
$\mathbb T=\Lambda[u]$ acts faithfully on $P$.  On $P/sP\simeq\mathcal O^2$, the operator $u$
acts as zero.  Nevertheless its class in $\mathbb T/s\mathbb T$ is nonzero.  Indeed, an equality
$u=s(a+bu)$ would imply $s(1-sb)=0$; since the annihilator of $s$ is generated over
$\mathcal O$ by the norm element, augmentation would give $1\in\ell\mathcal O$, an
impossibility.  Hence the algebraic coinvariant $\mathbb T/s\mathbb T$ contains a nonzero
nilpotent class invisible in the actual action on module coinvariants.  This is exactly the
defect measured by (20.26).

These examples separate the three necessary arguments.  Stabilizer cleanliness proves diamond
freeness, the common localized residual packet proves positive rank on both sides, and
augmentation saturation alone identifies the algebraic quotient of an acting image with the
image on coinvariants.

## 21. Final synthesis

### 21.1 The structural theorem in compressed form

The deep-level construction may be summarized by the following diagram, in which every arrow has now been defined and proved compatible:

$$
\begin{array}{ccccc}
P_m&\times&C_m&\xrightarrow{\ \mathcal H_m\ }&\Lambda_m\\
\downarrow&&\downarrow&&\downarrow\\
P_n&\times&C_n&\xrightarrow{\ \mathcal H_n\ }&\Lambda_n\\
\downarrow&&\downarrow&&\downarrow\epsilon\\
P_0&\times&C_0&\xrightarrow{\ b_0\ }&\mathcal O.
\end{array}
$$

The vertical maps in the first square are exact base change along $\Lambda_m\twoheadrightarrow\Lambda_n$; the bottom maps are augmentation. The modules in the first two columns are free over the ring in the last column of their row. Diamonds act on the primary side and inversely on the companion side. Every specified Hecke operator commutes with the transition maps and is adjoint to its declared companion operator.

If minimal-level control holds, $P_0$ and $C_0$ may be replaced by fixed minimal-level localized modules. Without that additional theorem, the diagram remains complete and correct with oriented-level bottom row.

For a paired desired--avoidance construction, Theorem 20.5 gives two such diagrams with one marked
residual bottom row at a fixed $Q$.  The same nonzero residual packet fixes their common positive
rank there, and all Hecke, diamond, pairing, and augmentation maps reduce to the corresponding
maps on that common row.  This is stronger than an equality of ranks and is exactly what permits
the two systems to be carried simultaneously.  Proposition 20.6 is the separate passage from
these fixed-$Q$ statements to a uniform varying-$Q_N$ family.

### 21.2 A dependency-closed proof chain

The proof chain has no hidden step.

1. Total definiteness makes the quaternionic class groupoid finite.
2. Exact integral forms decompose into stabilizer coefficient lattices.
3. Fixed-central-character level uses the projective diagonal-ratio quotient; the lower-right quotient would be scalar.
4. Exact $\ell$-power quotients give groups of order $\ell^n$ at depth $n$.
5. Projectivizing removes the local center, and clean projective stabilizers make every global fiber a genuine torsor.
6. Functions with constant coefficient lattice on a torsor are regular group-ring modules.
7. Orbit sum is augmentation on the regular module, giving an exact quotient.
8. The finite complete image Hecke algebra supplies compatible idempotent primary factors.
9. A direct summand of a free module over the local group ring is free.
10. Adjoint idempotents select the companion, and the coefficient pairing promotes to a perfect group-ring-valued pairing.
11. Nested subgroups at a fixed auxiliary set give genuine transitive trace maps and exact group-ring base change.
12. A unit Gram determinant supplies degeneracy injectivity and saturation; new-support vanishing and regular refinement are the remaining extra inputs for minimal-level control.
13. Independently chosen auxiliary sets share a power-series presentation but no arithmetic transition unless separate geometry provides one.
14. A marked residual coefficient lattice and prime-to-$\ell$ stabilizers identify reduction with sections for both coefficient systems.
15. At a fixed auxiliary set, one nonzero common localized residual packet fixes the same positive diamond rank on the two integral sides.
16. Across varying auxiliary sets, bounded ranks admit a cofinal constant-rank extraction retaining every prescribed finite mark; uniform minimal control gives constancy without this extraction.
17. Orbit sum gives saturated module augmentation, while acting-image augmentation retains the separate intersection criterion of (20.26).
18. Full source support annihilates the recovered module only through the nilradical, and therefore gives a nilpotent action kernel.

The prior-book boundary is exact:

| Prior book | Result used here | Boundary retained here |
|---|---|---|
| Book 143, Taylor--Wiles primes | exact auxiliary sets for a common residual deformation problem | it supplies no definite automorphic module and no diamond freeness statement |
| Book 144, Taylor--Wiles systems | exact-level diamond algebras, augmentation covariance, pairing conventions, and the distinction between presentations and transitions | it leaves diamond freeness, module control, and automorphic duality to the realization |
| Book 145, patching modules and rings | common finite shadows and the augmentation-saturation criterion used in (20.26) | it does not make acting-image augmentation automatic and supplies source support only after its own patching hypotheses are verified |
| Book 82, orders in quaternion algebras | finite definite class sets, projective stabilizers, and change-of-level fibers | it supplies no weighted automorphic module or Hecke action |
| Book 83, definite quaternionic forms | exact stabilizer-lattice description, central-character compatibility, pullback, trace, and integral pairings | bad stabilizer primes and perfectness remain explicit hypotheses |
| Book 84, quaternionic Hecke operators | right-coset normalization, $T_v,S_v,U_v$, degeneracy matrices, Gram determinant, and inverse-diamond adjunction | its lower-right diamond becomes scalar after fixing the center, so this book replaces it by the projective ratio rather than misusing it |
| Book 85, Hecke algebras and congruences | finite image algebras, residual idempotents, primary localization, adjoint factors, and formal old--new criteria | localization does not prove degeneracy injectivity or absence of new support |

Every conclusion in Theorems 15.1 and 20.5 is attached to the step that proves it. In particular, rank counts do not substitute for torsors, generic injectivity does not substitute for saturation, and a common abstract group ring does not substitute for a map of levels. The minimal-level corollary is explicitly conditional on new-support vanishing; no predecessor in the table proves that assertion for the definite module in the generality of this book.

### 21.3 Normalization conventions

The conventions used throughout are the following.

- Levels vary contravariantly: $U_m\subseteq U_n$ for $m\ge n$, so class sets and pullbacks go from level $n$ to level $m$.
- Forms and Hecke correspondences use right translation.
- The local diamond quotient is the lower-right-to-upper-left residue ratio on $K_0(v)$; it is trivial on scalars.
- The group at depth $n$ has exact order $\ell^n$ per auxiliary prime before any effective quotient.
- The group ring acts on the left, and its involution sends $[\delta]$ to $[\delta^{-1}]$.
- Orbit sum realizes coinvariants; pullback realizes invariants; norm identifies the two for projective modules.
- The spherical polynomial is $1-T_vX+q_vS_vX^2$, and the $U_v$-root polynomial is $Y^2-T_vY+q_vS_v$.
- The forward oriented operator need not be self-adjoint; its adjoint determines the companion factor.
- The primary module is a generalized residual idempotent summand, not an assumed eigenspace of multiplicity one.
- Perfectness is integral and is asserted only after stabilizer denominators and dual lattices have been checked.
- Genuine transition maps occur only inside an actual nested tower.
- Paired coefficient systems are identified through an intrinsic common residual section module, not by comparing ranks.
- Module augmentation is exact under the torsor hypotheses; acting-image augmentation additionally requires (20.26).

With these normalizations, the finite-level Taylor--Wiles modules have fixed positive group-ring rank inside each fixed auxiliary tower, exact augmentation, faithful diamond symmetry, primary--companion duality, and compatible transitions wherever arithmetic levels genuinely map to one another.  Theorem 20.5 supplies the same structures simultaneously for two coefficient systems with one marked residual packet, Proposition 20.6 isolates the additional uniformity needed when auxiliary sets vary, and Corollary 20.8 keeps exact acting-image augmentation at its proper saturation boundary.
