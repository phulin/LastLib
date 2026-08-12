# Modular and Shimura Curves

## Contents

1. [Curves born from classification problems](#1-curves-born-from-classification-problems)
   - [Why a moduli problem should make a curve](#11-why-a-moduli-problem-should-make-a-curve)
   - [Fine moduli, coarse moduli, and stacks](#12-fine-moduli-coarse-moduli-and-stacks)
   - [Rigidification as a design principle](#13-rigidification-as-a-design-principle)
   - [Standing conventions](#14-standing-conventions)
   - [Foundational inputs and logical scope](#15-foundational-inputs-and-logical-scope)
2. [Three kinds of elliptic level](#2-three-kinds-of-elliptic-level)
   - [Why characteristic changes the definition](#21-why-characteristic-changes-the-definition)
   - [Full level $N$](#22-full-level-n)
   - [$\Gamma_1(N)$ level](#23-gamma_1n-level)
   - [$\Gamma_0(N)$ level](#24-gamma_0n-level)
   - [Forgetting and quotienting](#25-forgetting-and-quotienting)
3. [The affine modular curves](#3-the-affine-modular-curves)
   - [Construction over the locus of invertible level](#31-construction-over-the-locus-of-invertible-level)
   - [The deformation calculation](#32-the-deformation-calculation)
   - [Degrees and stack-theoretic Galois groups](#33-degrees-and-stack-theoretic-galois-groups)
   - [When a quotient is genuinely Galois](#34-when-a-quotient-is-genuinely-galois)
4. [Determinants and connected components](#4-determinants-and-connected-components)
   - [The Weil pairing is the component coordinate](#41-the-weil-pairing-is-the-component-coordinate)
   - [$\Gamma_1$ and $\Gamma_0$ components](#42-gamma_1-and-gamma_0-components)
   - [A component calculation](#43-a-component-calculation)
5. [Complex uniformization](#5-complex-uniformization)
   - [From lattices to the upper half-plane](#51-from-lattices-to-the-upper-half-plane)
   - [Congruence quotients and level](#52-congruence-quotients-and-level)
   - [Orbifold points](#53-orbifold-points)
   - [Comparison with algebraic moduli](#54-comparison-with-algebraic-moduli)
   - [The first two examples](#55-the-first-two-examples)
6. [Why compactification needs new elliptic objects](#6-why-compactification-needs-new-elliptic-objects)
   - [The missing limits](#61-the-missing-limits)
   - [Stable level at the boundary](#62-stable-level-at-the-boundary)
   - [Cusps as moduli points](#63-cusps-as-moduli-points)
7. [Tate neighborhoods and properness](#7-tate-neighborhoods-and-properness)
   - [The Tate curve as a punctured neighborhood](#71-the-tate-curve-as-a-punctured-neighborhood)
   - [The valuative extension theorem](#72-the-valuative-extension-theorem)
   - [Proper compactified modular curves](#73-proper-compactified-modular-curves)
   - [Boundary maps and cusp widths](#74-boundary-maps-and-cusp-widths)
   - [Worked boundary examples](#75-worked-boundary-examples)
8. [Integral modular curves and their special fibers](#8-integral-modular-curves-and-their-special-fibers)
   - [Good primes](#81-good-primes)
   - [Why level primes are different](#82-why-level-primes-are-different)
   - [The $X_0(p)$ model with auxiliary rigidification](#83-the-x_0p-model-with-auxiliary-rigidification)
   - [Reduction maps needed later](#84-reduction-maps-needed-later)
   - [A regularity warning](#85-a-regularity-warning)
9. [Quaternion algebras with one split real place](#9-quaternion-algebras-with-one-split-real-place)
   - [Why another family of curves appears](#91-why-another-family-of-curves-appears)
   - [Orders and Eichler level](#92-orders-and-eichler-level)
   - [Positive norm and the chosen half-plane](#93-positive-norm-and-the-chosen-half-plane)
10. [The analytic Shimura curve](#10-the-analytic-shimura-curve)
    - [The adelic quotient](#101-the-adelic-quotient)
    - [Compactness and the absence of cusps](#102-compactness-and-the-absence-of-cusps)
    - [A compact example](#103-a-compact-example)
11. [PEL moduli for quaternionic curves](#11-pel-moduli-for-quaternionic-curves)
    - [Why the analytic quotient is not yet arithmetic geometry](#111-why-the-analytic-quotient-is-not-yet-arithmetic-geometry)
    - [The PEL datum](#112-the-pel-datum)
    - [Objects of the moduli problem](#113-objects-of-the-moduli-problem)
    - [The determinant condition](#114-the-determinant-condition)
    - [Polarization is structural, not decorative](#115-polarization-is-structural-not-decorative)
    - [Level and representability](#116-level-and-representability)
12. [Algebraic and canonical Shimura curves](#12-algebraic-and-canonical-shimura-curves)
    - [From complex points to a curve over the reflex field](#121-from-complex-points-to-a-curve-over-the-reflex-field)
    - [Properness](#122-properness)
    - [Coarse spaces and universal abelian schemes](#123-coarse-spaces-and-universal-abelian-schemes)
    - [Comparison of moduli and adelic descriptions](#124-comparison-of-moduli-and-adelic-descriptions)
13. [Reduced norms and components](#13-reduced-norms-and-components)
    - [Strong approximation isolates the obstruction](#131-strong-approximation-isolates-the-obstruction)
    - [Proof of the component formula](#132-proof-of-the-component-formula)
    - [A component calculation over $\mathbf Q$](#133-a-component-calculation-over-mathbf-q)
    - [Arithmetic versus geometric components](#134-arithmetic-versus-geometric-components)
14. [Integral models of Shimura curves](#14-integral-models-of-shimura-curves)
    - [What “good” means](#141-what-good-means)
    - [Good reduction is a property of datum and level](#142-good-reduction-is-a-property-of-datum-and-level)
    - [Split primes with Iwahori level](#143-split-primes-with-iwahori-level)
    - [The boundary at a ramified algebra place](#144-the-boundary-at-a-ramified-algebra-place)
    - [Specialization and cohomological scope](#145-specialization-and-cohomological-scope)
15. [Varying level and adelic actions](#15-varying-level-and-adelic-actions)
    - [A tower, not a single curve](#151-a-tower-not-a-single-curve)
    - [The right-action convention](#152-the-right-action-convention)
    - [Proof that the action respects level maps](#153-proof-that-the-action-respects-level-maps)
    - [Modular degeneracy maps](#154-modular-degeneracy-maps)
    - [Integral level change](#155-integral-level-change)
16. [Hecke correspondences from moduli and double cosets](#16-hecke-correspondences-from-moduli-and-double-cosets)
    - [Why correspondences are the right object](#161-why-correspondences-are-the-right-object)
    - [The prime-to-level modular correspondence](#162-the-prime-to-level-modular-correspondence)
    - [Level-prime correspondences](#163-level-prime-correspondences)
    - [Quaternionic isogeny correspondences](#164-quaternionic-isogeny-correspondences)
    - [Independence of representatives](#165-independence-of-representatives)
    - [The moduli correspondence equals the adelic double coset](#166-the-moduli-correspondence-equals-the-adelic-double-coset)
    - [Composition and convolution](#167-composition-and-convolution)
    - [Extension over good integral models](#168-extension-over-good-integral-models)
17. [From curves to Jacobians and $H^1$](#17-from-curves-to-jacobians-and-h1)
    - [The proper curve is the cohomological object](#171-the-proper-curve-is-the-cohomological-object)
    - [Correspondence variance](#172-correspondence-variance)
    - [Good reduction and unramified cohomology](#173-good-reduction-and-unramified-cohomology)
    - [What has and has not been extracted](#174-what-has-and-has-not-been-extracted)
    - [A genus-zero warning](#175-a-genus-zero-warning)
    - [The geometric Hecke modules](#176-the-geometric-hecke-modules)
18. [An atlas of examples](#18-an-atlas-of-examples)
    - [$X(1)$ revisited](#181-x1-revisited)
    - [$X_0(2)$ as cyclic isogenies](#182-x_02-as-cyclic-isogenies)
    - [$X_0(p)$ and the two projections](#183-x_0p-and-the-two-projections)
    - [A fixed-pairing full-level component](#184-a-fixed-pairing-full-level-component)
    - [A compact quaternionic curve and its component](#185-a-compact-quaternionic-curve-and-its-component)
19. [The geometric dictionary](#19-the-geometric-dictionary)
    - [From input data to a curve](#191-from-input-data-to-a-curve)
    - [From a curve to later arithmetic objects](#192-from-a-curve-to-later-arithmetic-objects)
    - [The exact endpoint of the construction](#193-the-exact-endpoint-of-the-construction)
    - [Conclusion](#194-conclusion)

## 1. Curves born from classification problems

### 1.1 Why a moduli problem should make a curve

An elliptic curve has one essential parameter: over an algebraically closed field its isomorphism class is usually determined by its $j$-invariant. Adding finitely many torsion data does not add a continuous parameter. One should therefore expect the classification of elliptic curves with a fixed kind of level structure to be one-dimensional. This expectation is the source of modular curves.

The word “classification” hides the central difficulty. If $S$ is a scheme, an elliptic curve over $S$ is not a list of equations but a smooth proper morphism $E\to S$ with geometrically connected genus-one fibers and a section. Isomorphisms between such families matter, and a family that becomes trivial after a cover need not be globally trivial. The correct input is consequently a functor of groupoids, not merely a function assigning sets.

For a level condition $\mathcal P$, write

$$
\mathcal M_{\mathcal P}(S)
=\{(E/S,\eta):\eta\text{ is a }\mathcal P\text{-structure on }E\},
$$

where arrows are isomorphisms of elliptic curves carrying one level structure to the other. Pullback along $T\to S$ makes this a fibered category. Descent for proper smooth curves, sections, and finite subgroup schemes makes it a stack for the étale topology.

This formulation solves three problems at once. It remembers families, it remembers twisting, and it remembers automorphisms. All three are lost if one records only isomorphism classes over fields.

### 1.2 Fine moduli, coarse moduli, and stacks

A **fine moduli scheme** for $\mathcal M_{\mathcal P}$ is a scheme $M$ together with a universal object $(\mathcal E,\eta_{\mathrm{univ}})$ such that every family is obtained, uniquely up to unique isomorphism, by pullback along a unique map to $M$. Equivalently, the groupoid-valued problem is represented by a sheaf of sets. This can happen only when every object has trivial automorphism group.

Indeed, if $(E,\eta)$ over a field had a nonidentity automorphism, it would be an automorphism of the pullback of the universal object along a point of $M$. But representability by a set-valued functor makes that pullback unique with no remembered stabilizer. Thus automorphisms are not a minor nuisance in constructing a universal family; they are an obstruction to the very meaning of fine representability.

An algebraic stack keeps stabilizers. The stack $\mathcal M_{\mathrm{ell}}$ of elliptic curves is smooth of relative dimension one over $\operatorname{Spec}\mathbf Z$. It is not a scheme: every elliptic curve has $[-1]$, and curves with $j=1728$ or $0$ have still larger geometric automorphism groups in the familiar characteristics, with additional phenomena in characteristics $2$ and $3$.

A **coarse moduli space** $M$ receives a map $\mathcal M_{\mathcal P}\to M$, is initial among maps to algebraic spaces, and induces a bijection on geometric isomorphism classes. It need not carry a universal family, and formation of a coarse space need not commute with arbitrary base change when stabilizers are not tame. Coarse space and stack have the same geometric points but not the same local geometry.

The basic example is decisive:

$$
\mathcal M_{\mathrm{ell}}\longrightarrow \mathbf A^1_{\mathbf Z},
\qquad E\longmapsto j(E).
$$

The affine line is the coarse space, customarily denoted $Y(1)$. It does not represent elliptic curves. A hypothetical universal elliptic curve over the $j$-line would contradict the generic automorphism $[-1]$.

### 1.3 Rigidification as a design principle

Level structure is introduced partly to record arithmetic and partly to kill automorphisms. Suppose $N$ is invertible on the base and an automorphism $u$ of $E$ fixes an ordered basis of $E[N]$. Then $u$ acts trivially on $E[N]$. For $N\geq3$, this forces $u=1$. One way to see the force of the condition is to note that $u-1$ has all $N^2$ torsion points in its kernel; a nonzero endomorphism of an elliptic curve has degree at least the size of its étale kernel, while the possible automorphisms have very small degree. The exceptional small levels are exactly where this argument cannot separate $u$ from the identity.

Rigidity thresholds depend on the moduli problem. Full level $N$ is fine over $\mathbf Z[1/N]$ for $N\geq3$. A point of exact order $N$ gives fine $\Gamma_1(N)$ level for $N\geq4$ over $\mathbf Z[1/N]$. A cyclic subgroup does not kill $[-1]$, because $[-1]$ preserves every subgroup. Thus bare $\Gamma_0(N)$ level is never a fine elliptic-curve moduli problem in the generic characteristic. It has a natural stack and a coarse curve; a universal generalized elliptic curve exists only after passing to the stack or adding auxiliary rigid level.

**Counterexample.** It is tempting to say that a “sufficiently large” cyclic subgroup rigidifies an elliptic curve. It does not. If $C\subset E$ is cyclic of any order, then $[-1](C)=C$. Size cannot replace the orientation supplied by a chosen generator or a full basis.

### 1.4 Standing conventions

For an integer $N\geq1$, bases on which $N$ is invertible are schemes over $\mathbf Z[1/N]$. The group scheme of $N$th roots of unity is $\mu_N$, and the constant group scheme attached to $\mathbf Z/N\mathbf Z$ is denoted simply $\mathbf Z/N\mathbf Z$. Geometric connectedness always means connectedness after extension to an algebraic closure; it is stronger than connectedness over the displayed ground field.

We distinguish the open moduli curve $Y$ of smooth elliptic curves from its compactification $X$. Script letters denote stacks, ordinary letters coarse spaces or fine schemes. When a fine problem is chosen, the distinction disappears and we say so explicitly. A subgroup called finite locally free has constant rank on each connected component of the base.

### 1.5 Foundational inputs and logical scope

A unified account is useful only if its foundations are visible. We shall repeatedly use the following established results, always with the hypotheses displayed here.

First, generalized elliptic curves and their ample Drinfeld level structures form algebraic stacks with finite separated diagonal. Finite subgroup quotients and canonical contractions exist, are unique, and commute with base change. Over the good-level base, where the level order is invertible, the standard compactified level stacks are smooth, proper, and flat. Zariski-locally on that base one may choose auxiliary full level of order at least three that is invertible there and obtain a projective fine cover; the resulting covers form a faithfully flat projective cover globally. Their Tate charts are complete: they describe every boundary deformation, not merely a dense family of examples. At a prime dividing the level, only the prime-depth integral model singled out in the next paragraph is taken as established; no arbitrary bad-level compactification theorem is being imported.

Second, at a prime $p$ occurring to squarefree $\Gamma_0$-depth one, after prime-to-$p$ rigidification the Deligne--Rapoport model is regular and semistable. Its supersingular completed local rings are

$$
W(k)[[x,y]]/(xy-p),
$$

and its two normalized components are the Frobenius and Verschiebung branches. No corresponding assertion will be made for deeper $p$-power level, for an unrigidified wild coarse quotient, or for arbitrary parahoric data.

Third, the quaternionic groups, their involutions, symplectic representations, and the PEL data used here have already been constructed. For a one-dimensional quaternionic PEL datum, neat level gives a smooth fine curve over the reflex field, complex uniformization identifies it with the selected adelic quotient, reduced norm computes the components of the basic group by strong approximation, and canonical reciprocity gives the descent action on those components. At an unramified self-dual hyperspecial place the integral PEL functor is represented by a smooth model. Properness of that integral model additionally requires either the direct quaternionic trace realization or the established boundary-rationality condition for every trait degeneration; anisotropy alone does not supply the missing rational boundary flag. At a split Iwahori place the rank-two local model is semistable only under the explicit unramified minuscule and flat-local-model hypotheses stated in Chapter 14.

Finally, for a smooth proper curve $X$, its Jacobian exists, finite correspondences act by pullback followed by norm, and the Kummer sequence identifies its Tate module with first étale cohomology in the variance used in Chapter 17. Smooth proper base change applies only to a smooth proper model. A regular semistable model instead brings component groups, nearby cycles, and monodromy into the picture.

These are not hidden conclusions of this volume. They are its construction materials. What is proved here is how they fit together: the precise modular and quaternionic moduli problems, their analytic and adelic realizations, the passage to compact and integral curves, the comparison of component labels, and the construction of one common geometric Hecke action. Each later invocation will point back to the relevant hypothesis rather than abbreviating it as “standard.”

## 2. Three kinds of elliptic level

### 2.1 Why characteristic changes the definition

If $N$ is invertible on $S$, multiplication by $N$ on an elliptic curve is finite étale of degree $N^2$, so étale-locally

$$
E[N]\simeq (\mathbf Z/N\mathbf Z)^2.
$$

Points and subgroup schemes then agree with the elementary picture of a rank-two module. In characteristic $p\mid N$, this picture fails. The group scheme $E[p]$ can be nonreduced, and an ordinary elliptic curve has geometric $p$-torsion points forming only a group of order $p$, while a supersingular curve can have only the identity as a geometric $p$-torsion point. A definition based on geometric points would discard most of the group scheme.

The right definitions therefore have two layers. Away from $N$, one uses bases, points, and cyclic subgroups in the ordinary étale sense. Over bases where level primes are not invertible, one uses Cartier divisors and finite locally free subgroup schemes. These definitions specialize to the familiar ones but continue to see infinitesimal torsion.

### 2.2 Full level $N$

Assume first that $N$ is invertible on $S$. A **full level-$N$ structure** on $E/S$ is an isomorphism

$$
\alpha:(\mathbf Z/N\mathbf Z)^2_S\xrightarrow{\sim}E[N]. \tag{2.1}
$$

Write $P=\alpha(1,0)$ and $Q=\alpha(0,1)$. The Weil pairing gives a primitive root of unity

$$
e_N(P,Q)\in\mu_N(S). \tag{2.2}
$$

Changing the basis by $g\in\operatorname{GL}_2(\mathbf Z/N\mathbf Z)$ changes this root by

$$
e_N(\alpha g(e_1),\alpha g(e_2))
=e_N(P,Q)^{\det g}. \tag{2.3}
$$

Thus the determinant is not bookkeeping external to the moduli problem. It controls the cyclotomic coordinate of the basis.

If $N$ is not invertible, a homomorphism

$$
\alpha:(\mathbf Z/N\mathbf Z)^2_S\longrightarrow E[N]
$$

is called a **Drinfeld full level structure** when the effective Cartier divisor formed by all its values equals the entire torsion divisor:

$$
\sum_{a\in(\mathbf Z/N\mathbf Z)^2}[\alpha(a)]=E[N]. \tag{2.4}
$$

This is a scheme-theoretic equality. Requiring only surjectivity on geometric points would be meaningless for connected torsion. On generalized elliptic curves one imposes the corresponding divisor condition on the smooth locus together with an ampleness condition ensuring that the chosen sections meet every irreducible component.

The divisor condition preserves the length of the torsion, but it does not preserve the rigidifying force of an ordinary basis. For example, on a supersingular elliptic curve in characteristic $p$, the zero homomorphism can satisfy the Drinfeld divisor condition for full $p$-level because the entire $p$-torsion divisor is supported at the identity. Automorphisms can then survive. Thus full level $N\geq3$ is a fine problem over $\mathbf Z[1/N]$; the same numerical inequality alone is not a representability criterion in fibers whose characteristic divides $N$.

### 2.3 $\Gamma_1(N)$ level

Away from $N$, a **$\Gamma_1(N)$-structure** is a section $P\in E(S)$ whose restriction to every geometric fiber has exact order $N$. Equivalently, the homomorphism

$$
\mathbf Z/N\mathbf Z\longrightarrow E[N],\qquad a\longmapsto aP,
$$

is a closed immersion. This records a generator, not merely the subgroup it spans.

In arbitrary characteristic the useful formulation is again divisorial: $P$ is a Drinfeld point of exact order $N$ if

$$
\sum_{a\in\mathbf Z/N\mathbf Z}[aP]
$$

is a finite locally free subgroup divisor of rank $N$ in $E$. Exact order on geometric points is not an adequate replacement.

For example, over an algebraically closed field of characteristic $p$, the group scheme $\mu_p$ has just one geometric point. Nevertheless it is finite locally free of rank $p$, and a Drinfeld generator can encode it through a nonreduced divisor. The example explains why “$p$ distinct multiples” is precisely the wrong condition at $p$.

### 2.4 $\Gamma_0(N)$ level

Away from $N$, a **$\Gamma_0(N)$-structure** is a cyclic finite étale subgroup $C\subset E[N]$ of rank $N$. Étale-locally it is generated by a point of exact order $N$. The word locally is essential: a rational subgroup need not possess a rational generator.

For general bases, one uses a finite locally free subgroup scheme $C\subset E^{\mathrm{sm}}$ of rank $N$ that is **cyclic in the Drinfeld sense**: locally for a suitable topology there is a section $P$ such that

$$
C=\sum_{a\in\mathbf Z/N\mathbf Z}[aP]
$$

as effective Cartier divisors. For a generalized elliptic curve one additionally requires $C$ to be ample, meaning that it meets every irreducible component of every geometric fiber. This prevents level structure from hiding entirely in the identity component of a degenerate polygon.

**Counterexample.** In characteristic $p$, the set $C(\bar k)$ does not determine a rank-$p$ subgroup scheme. On an ordinary elliptic curve, $\mu_p$ and the trivial reduced point have the same underlying geometric point but different lengths; only the former is a rank-$p$ subgroup. On a supersingular curve even more torsion is infinitesimal. Hence “a cyclic subgroup of the group of geometric points” cannot define the integral $\Gamma_0(p)$ problem.

### 2.5 Forgetting and quotienting

There are natural transformations

$$
\mathcal M(N)\longrightarrow\mathcal M_1(N)
\longrightarrow\mathcal M_0(N)
\longrightarrow\mathcal M_{\mathrm{ell}}, \tag{2.5}
$$

obtained by retaining the first basis vector, then its cyclic subgroup, then nothing. Away from $N$, the quotient $E/C$ is again an elliptic curve and $E\to E/C$ is an isogeny of degree $N$. Thus $\Gamma_0(N)$ may equally be viewed as a cyclic isogeny with source remembered. This alternate description will produce the most elementary Hecke correspondence later.

The arrows in (2.5) are not all Galois covers of coarse schemes. Before taking coarse spaces, full bases form a torsor under $\operatorname{GL}_2(\mathbf Z/N\mathbf Z)$ over the elliptic stack. Passing to a chosen determinant component reduces the group to $\operatorname{SL}_2$. Forgetting to a vector or a line corresponds to quotienting by its stabilizer. But coarse maps ramify at objects with extra automorphisms, even when the stack map is finite étale.

## 3. The affine modular curves

### 3.1 Construction over the locus of invertible level

The torsion group $E[N]$ in a family is finite étale when $N$ is invertible. Consequently the sheaf of its ordered bases is finite étale over the base. Applying this to the universal elliptic curve on the moduli stack constructs $\mathcal Y(N)$ as a finite étale cover of $\mathcal M_{\mathrm{ell},\mathbf Z[1/N]}$. The loci selecting one primitive vector or one direct-summand cyclic subgroup are finite étale quotients and give $\mathcal Y_1(N)$ and $\mathcal Y_0(N)$.

This construction is local on the base and descends because bases, sections, and subgroup schemes have effective descent. It proves more than existence: the level stacks are smooth of relative dimension one over $\mathbf Z[1/N]$, since finite étale morphisms preserve smoothness and dimension.

For the rigid ranges, one obtains schemes:

**Theorem 3.1 (fine affine modular curves).** Over $\mathbf Z[1/N]$, the stack $\mathcal Y(N)$ is represented by a smooth affine scheme for $N\geq3$, and $\mathcal Y_1(N)$ is represented by a smooth affine scheme for $N\geq4$. They carry universal elliptic curves with their indicated level structures.

**Proof strategy.** The level sheaf is finite étale over the elliptic stack. We must show that the stated level kills inertia, turn the resulting algebraic space into a scheme, and then prove affineness.

**Proof.** Let $(E,\alpha)$ be a geometric full-level object and let $u$ be an automorphism preserving $\alpha$. Then $u$ acts trivially on $E[N]$. We claim that $u=1$ for $N\geq3$. If $u\ne1$, the endomorphism $u-1$ is an isogeny and its kernel contains $E[N]$, so

$$
N^2\mid\deg(u-1). \tag{3.1a}
$$

The automorphism group of an elliptic curve acts faithfully on its prime-to-characteristic Tate module. Its possible finite-order characteristic polynomials have roots of unity of degree at most two, and therefore

$$
\deg(u-1)=\det(1-u\mid T_rE)\in\{1,2,3,4\}
$$

for an auxiliary prime $r$, unless $u=1$. Equality with $4$ occurs for $u=-1$, whose action on $E[N]$ is not the identity when $N\geq3$. The remaining cases cannot be divisible by $N^2$. Thus $u=1$. This argument remains valid in characteristics $2$ and $3$ because $N$ is invertible and the auxiliary Tate module detects the automorphism.

For a $\Gamma_1(N)$ object $(E,P)$, an automorphism fixing $P$ makes the cyclic subgroup generated by $P$ lie in $\ker(u-1)$. Since $N$ is invertible, this subgroup has rank $N$, so $N\mid\deg(u-1)$. The displayed degree list rules out $N\geq5$. If $N=4$, divisibility forces $\deg(u-1)=4$, hence the characteristic polynomial has trace $-2$ and $u=-1$ on the auxiliary Tate module. But $\ker(-1-1)=E[2]$ contains no point of exact order four. Thus $u=1$. The bound is sharp as a uniform statement: at smaller levels, $[-1]$ fixes every point of order two, and exceptional automorphisms survive at special $j$-values.

The level stacks have finite diagonal and are finite étale over the elliptic stack. Trivial geometric inertia makes each one an algebraic space. The established coarse-space theorem for finite level problems shows that the forgetful morphism to the coarse $j$-line is finite; equivalently, on Weierstrass charts the torsion coordinates satisfy the monic division equations and their invariant rings are integral over the $j$-ring. A finite algebraic space over a scheme is a scheme. Since a finite morphism to the affine scheme $\mathbf A^1_{\mathbf Z[1/N]}$ is affine, the resulting scheme is affine.

Smoothness follows from the finite étale map to the smooth elliptic stack, or equivalently from the deformation calculation in the next section. The universal object on the level stack becomes a universal elliptic curve on the representing scheme. $\square$

The compactified curve introduced later supplies the missing finite set of cusps. The proof also explains why the same statement cannot be transferred verbatim to bad characteristic: there the level sheaf need not be étale and full Drinfeld level need not kill inertia.

For $\Gamma_0(N)$, the stack has generic stabilizer $\{\pm1\}$, so its coarse space $Y_0(N)$ is a curve but does not carry a universal elliptic curve. After also inverting $6$, its quotient singularities are tame and the usual coarse curve is smooth over $\mathbf Z[1/6N]$. At characteristics $2$ and $3$ one should retain the smooth stack or verify the coarse local ring separately rather than infer smoothness from the stack. Adding an auxiliary full level $M\geq3$, with $MN$ inverted, produces a fine cover on which the universal object exists; descent from that cover constructs the coarse curve and many of its maps.

### 3.2 The deformation calculation

Why is the relative dimension exactly one? Let $k$ be algebraically closed with $\operatorname{char}k\nmid N$, and let $(E,\eta)$ be a level object. First-order deformations over $k[\epsilon]/(\epsilon^2)$ of $E$ are governed by

$$
H^1(E,T_E),
$$

which has dimension one because $T_E\simeq\mathcal O_E$. There is no obstruction on a curve. The finite étale group $E[N]$ lifts uniquely through a nilpotent thickening, so the level structure contributes no new tangent direction and no obstruction. Hence the completed local ring of a fine modular curve at the point is $k[[t]]$.

This argument also identifies the limit of the statement. If $\operatorname{char}k\mid N$, torsion is no longer étale and level structures can deform nontrivially or collide. Smoothness can fail. It is incorrect to carry the prime-to-level deformation argument into the bad fiber.

### 3.3 Degrees and stack-theoretic Galois groups

Over a geometric point of characteristic prime to $N$, the number of ordered bases of $E[N]$ is

$$
|\operatorname{GL}_2(\mathbf Z/N\mathbf Z)|
=N^4\prod_{p\mid N}(1-p^{-1})(1-p^{-2}). \tag{3.1}
$$

Thus $\mathcal Y(N)\to\mathcal M_{\mathrm{ell}}$ is a finite étale Galois cover of stacks with this group, using the right action $\alpha\mapsto\alpha\circ g$. The number of primitive points is

$$
N^2\prod_{p\mid N}(1-p^{-2}), \tag{3.2}
$$

and the number of cyclic direct summands of order $N$ is

$$
N\prod_{p\mid N}(1+p^{-1}). \tag{3.3}
$$

These are fiber degrees of the corresponding representable maps of stacks. On coarse curves the generic degrees agree, but special fibers over $j=0$ and $1728$ can have ramification because stabilizers have changed.

### 3.4 When a quotient is genuinely Galois

Let $H'\triangleleft H$ be congruence subgroups with the relevant level invertible and assume both moduli problems are fine. Then the map $Y_{H'}\to Y_H$ is finite étale Galois with group $H/H'$ if the action is free. Normality is indispensable. For example, $\Gamma_1(N)$ is not generally normal in $\operatorname{GL}_2(\mathbf Z/N\mathbf Z)$, so $Y_1(N)\to Y(1)$ is not a Galois cover merely because it forgets finite data.

There are two other frequent sources of false Galois assertions. Fixing the Weil pairing removes determinant-changing matrices, and passing to coarse moduli introduces branch points. A correct statement must specify the component, the acting group, and whether it concerns stacks or coarse schemes.

## 4. Determinants and connected components

### 4.1 The Weil pairing is the component coordinate

Over $\mathbf Z[1/N]$, a full basis has a Weil pairing value that is a primitive $N$th root of unity. This gives a morphism

$$
Y(N)\longrightarrow \mu_N^{\mathrm{prim}}
=\operatorname{Spec}\bigl(\mathbf Z[1/N,T]/(\Phi_N(T))\bigr), \tag{4.1}
$$

where the target is the finite étale scheme of primitive roots. Over $\mathbf C$, its fibers are the connected components of the full-level moduli scheme. Specifying

$$
e_N(P,Q)=\zeta_N \tag{4.2}
$$

selects the symplectic component $Y(N)_{\zeta_N}$.

**Theorem 4.1.** For $N\geq3$, each fixed-pairing complex curve $Y(N)_{\zeta}$ is connected, hence geometrically connected over $\mathbf Q(\zeta_N)$. The full curve over $\mathbf Q$ is connected in the arithmetic sense appropriate to its cyclotomic field of constants but is not geometrically connected; after base change to $\overline{\mathbf Q}$ it is the disjoint union indexed by primitive roots.

**Proof.** We give the uniformization argument here so that the component theorem does not depend on a later conclusion. Choose a primitive root $\zeta$. Every complex elliptic curve is $E_\tau=\mathbf C/(\mathbf Z\tau+\mathbf Z)$ for some $\tau\in\mathfrak H$. The two standard classes $1/N$ and $\tau/N$ form a basis of $E_\tau[N]$ whose pairing is a primitive root $\zeta_0$. There is a unique $b\in(\mathbf Z/N\mathbf Z)^\times$ with $\zeta_0^b=\zeta$, and the basis

$$
P=1/N,\qquad Q=b\tau/N
$$

has pairing $\zeta$. Conversely, relative to any oriented basis of $\Lambda$, a marked basis with the same pairing differs from the displayed one by an element of $\operatorname{SL}_2(\mathbf Z/N\mathbf Z)$. Surjectivity of

$$
\operatorname{SL}_2(\mathbf Z)\longrightarrow
\operatorname{SL}_2(\mathbf Z/N\mathbf Z)
$$

lifts that change of level basis to a change of oriented lattice basis. Two parameters $\tau$ and $\tau'$ therefore give isomorphic marked curves precisely when

$$
\tau'=\gamma\tau\qquad\text{for some }\gamma\in\Gamma(N).
$$

Thus $Y(N)_\zeta(\mathbf C)=\Gamma(N)\backslash\mathfrak H$. The continuous image of the connected space $\mathfrak H$ is connected. Since the quotient is a smooth complex algebraic curve, analytic connectedness is equivalent to algebraic connectedness.

For any $g\in\operatorname{GL}_2(\mathbf Z/N\mathbf Z)$, formula (2.3) changes the pairing by the exponent $\det g$. The determinant map is surjective, so these matrices act transitively on the primitive pairing values. Hence the geometric fibers of (4.1), and no smaller pieces, are the geometric connected components.

It remains to distinguish the ground fields. The finite étale target $\mu_N^{\mathrm{prim}}$ has coordinate algebra $\mathbf Q[T]/(\Phi_N)$, which is the field $\mathbf Q(\zeta_N)$ and is therefore connected over $\mathbf Q$. The total curve is connected because its components are permuted transitively by

$$
\operatorname{Gal}(\mathbf Q(\zeta_N)/\mathbf Q)\simeq(\mathbf Z/N\mathbf Z)^\times.
$$

After base change to $\overline{\mathbf Q}$ the cyclotomic algebra splits as a product indexed by primitive roots, and the curve splits accordingly. Over $\mathbf Q(\zeta_N)$ one chosen fiber is geometrically connected. $\square$

The theorem illustrates why “connected” is insufficient in arithmetic. A scheme can be connected over $\mathbf Q$ because Galois permutes its geometric components transitively.

### 4.2 $\Gamma_1$ and $\Gamma_0$ components

For the classical groups over $\mathbf Q$, the analytic curves $\Gamma_1(N)\backslash\mathfrak H$ and $\Gamma_0(N)\backslash\mathfrak H$ are connected. Their canonical algebraic models are geometrically connected over $\mathbf Q$. The disappearance of a visible cyclotomic component parameter reflects the fact that one has forgotten enough of the basis for determinant matrices to identify pairing values.

Here is the exact descent argument. The quotient map from a fixed full-level component to $Y_1(N)$ is induced by allowing changes of the second basis vector while retaining the first. Such changes realize every possible primitive Weil pairing with the fixed point, so the Galois orbit of full-level components maps onto a single complex component. The analytic quotient $\Gamma_1(N)\backslash\mathfrak H$ is connected because it is a continuous image of $\mathfrak H$. Its field of moduli is $\mathbf Q$: the point condition $P$ of exact order $N$ is defined without choosing a root of unity. The same argument after forgetting the generator but retaining its cyclic subgroup gives $Y_0(N)$. Thus connectedness is not inferred merely from forgetting data; it follows from connected analytic uniformization together with descent of the defining moduli condition.

This statement concerns the standard components attached to subgroups of $\operatorname{SL}_2(\mathbf Z)$. An adelic modular curve at a general compact open can have several components, controlled by the determinant quotient

$$
\mathbf Q_{>0}^{\times}\backslash\mathbf A_f^{\times}/\det K. \tag{4.3}
$$

For the usual $K_0(N)$ and $K_1(N)$, the determinant contains $\widehat{\mathbf Z}^{\times}$ and the quotient is trivial. For principal $K(N)$ it retains the cyclotomic residue-class information.

### 4.3 A component calculation

Take principal level $N=5$. A full basis $(P,Q)$ has pairing $\zeta_5^a$ with $a\in(\mathbf Z/5\mathbf Z)^\times$. Thus over $\mathbf C$ there are four components. A matrix of determinant $d$ sends the $a$-component to the $ad$-component. Over $\mathbf Q(\zeta_5)$ each component is defined and geometrically connected. Over $\mathbf Q$, Galois acts by

$$
\sigma_b(\zeta_5)=\zeta_5^b,
$$

and permutes the same four components. This is the simplest model for the norm-class component calculations on Shimura curves.

## 5. Complex uniformization

### 5.1 From lattices to the upper half-plane

Every complex elliptic curve is analytically $\mathbf C/\Lambda$ for a lattice $\Lambda$. After scaling, an oriented basis of $\Lambda$ has the form $(\tau,1)$ with

$$
\tau\in\mathfrak H=\{z\in\mathbf C:\operatorname{Im}z>0\}.
$$

Changing the oriented basis by $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\operatorname{SL}_2(\mathbf Z)$ replaces $\tau$ by

$$
\gamma\tau=\frac{a\tau+b}{c\tau+d}. \tag{5.1}
$$

Thus the complex moduli stack of elliptic curves is the analytic quotient stack

$$
\mathcal M_{\mathrm{ell}}(\mathbf C)^{\mathrm{an}}
\simeq[\operatorname{SL}_2(\mathbf Z)\backslash\mathfrak H]. \tag{5.2}
$$

The central element $-I$ acts trivially on $\mathfrak H$ but nontrivially as $[-1]$ on the universal elliptic curve. Quotienting the underlying topological space cannot remember this stabilizer; the stack quotient can.

### 5.2 Congruence quotients and level

The classical congruence subgroups are

$$
\begin{aligned}
\Gamma(N)&=\{\gamma\in\operatorname{SL}_2(\mathbf Z):\gamma\equiv I\pmod N\},\\
\Gamma_1(N)&=\left\{\gamma:\gamma\equiv
\begin{pmatrix}1&*\\0&1\end{pmatrix}\pmod N\right\},\\
\Gamma_0(N)&=\left\{\gamma:c\equiv0\pmod N\right\}.
\end{aligned} \tag{5.3}
$$

With compatible choices of which lattice vector represents the marked point, their quotients give the corresponding fixed complex component:

$$
Y(N)(\mathbf C)_{\zeta}\simeq\Gamma(N)\backslash\mathfrak H,
\quad
Y_1(N)(\mathbf C)\simeq\Gamma_1(N)\backslash\mathfrak H,
\quad
Y_0(N)(\mathbf C)\simeq\Gamma_0(N)\backslash\mathfrak H. \tag{5.4}
$$

For full level one may take $P=1/N$ and $Q=\tau/N$; the order and sign determine whether the pairing is $e^{2\pi i/N}$ or its inverse. This harmless convention must remain fixed when comparing determinant actions.

### 5.3 Orbifold points

A point of $\mathfrak H$ has nontrivial stabilizer in $\operatorname{PSL}_2(\mathbf Z)$ only in the orbits of $i$ and $e^{2\pi i/3}$. Their elliptic curves have $j=1728$ and $j=0$. Locally the coarse quotient looks like a disk modulo a cyclic rotation, so the map to the $j$-line is branched there.

If a congruence subgroup is torsion-free modulo its ineffective center, the quotient is an honest Riemann surface. Principal $\Gamma(N)$ is torsion-free for $N\geq3$. The group $\Gamma_1(N)$ is sufficiently rigid for $N\geq4$. By contrast, $-I$ acts trivially on $\mathfrak H$ and preserves every $\Gamma_0$ structure, reflecting the persistent stack stabilizer.

The distinction resolves an apparent contradiction. The coarse analytic space $\operatorname{PSL}_2(\mathbf Z)\backslash\mathfrak H$ is an ordinary Riemann surface isomorphic to the $j$-line, but there is no universal elliptic curve over it. The missing information is precisely the isotropy retained by (5.2).

### 5.4 Comparison with algebraic moduli

The analytic family $\mathbf C/(\mathbf Z\tau+\mathbf Z)$ descends over a torsion-free congruence quotient. Its algebraic invariants define a map from the analytic quotient to the analytification of the corresponding algebraic moduli curve. Both classify the same complex families, so the map is an isomorphism. In nonfine cases the correct comparison is between analytic and algebraic stacks, followed by an isomorphism of coarse spaces.

This comparison is not merely a pointwise bijection. It respects finite level maps, automorphism groups, connected components, and the algebraic structure of the quotient. It lets topology prove connectedness while algebraic geometry supplies descent and integral models.

### 5.5 The first two examples

For level one,

$$
Y(1)_{\mathbf C}\simeq\mathbf A^1_{\mathbf C}
$$

through $j$. Its compactification will add one cusp and become $X(1)\simeq\mathbf P^1$.

For $\Gamma_0(N)$, a complex point is a pair $(E,C)$ with $C$ cyclic of order $N$, equivalently a cyclic $N$-isogeny $E\to E/C$. The two maps

$$
(E,C)\longmapsto E,
\qquad
(E,C)\longmapsto E/C \tag{5.5}
$$

are the source and target maps to $Y(1)$. When $N=p$ is prime, the generic source fiber has $p+1$ points, the lines in $(\mathbf Z/p\mathbf Z)^2$. Branching at elliptic points and cusps means that this generic count is not a statement of étaleness for compact coarse curves.

## 6. Why compactification needs new elliptic objects

### 6.1 The missing limits

The quotient $\Gamma\backslash\mathfrak H$ is not compact. A sequence with $\operatorname{Im}\tau\to\infty$ makes one period infinitely long; the corresponding elliptic curves degenerate. Adding a point to the parameter curve without enlarging the objects would produce no universal limiting family. Compactification is therefore a moduli problem in its own right.

A **generalized elliptic curve** over $S$ is a proper flat finitely presented curve $E\to S$ whose geometric fibers are either smooth elliptic curves or Néron polygons, together with a group law on the smooth locus $E^{\mathrm{sm}}$ whose action extends to all of $E$ and rotates the components of every polygon. An $n$-gon consists of $n$ copies of $\mathbf P^1$ joined cyclically, the point $\infty$ on one copy meeting $0$ on the next. Its smooth locus fits into

$$
1\longrightarrow\mathbf G_m\longrightarrow E^{\mathrm{sm}}
\longrightarrow\mathbf Z/n\mathbf Z\longrightarrow0. \tag{6.1}
$$

The polygon is the stable group-theoretic replacement for a nodal cubic. A bare nodal cubic suffices for level one, but higher level may force several components so that the level subgroup meets them all.

### 6.2 Stable level at the boundary

A level structure on a generalized elliptic curve lies in $E^{\mathrm{sm}}$. The ampleness condition says that the divisor made from the level sections meets every component of every degenerate fiber. Without it, one could attach arbitrarily many unused components and uniqueness of limits would fail.

For $\Gamma_0(N)$ the condition is a cyclic finite locally free subgroup $C\subset E^{\mathrm{sm}}$ of rank $N$ whose divisor is ample. For $\Gamma_1(N)$ it is a Drinfeld generator whose generated divisor is ample. Full level is treated similarly, sometimes after allowing a controlled contraction of polygons. These formulations are stable under base change and remain meaningful at primes dividing $N$.

There is a subtlety: different integral compactification problems can agree on smooth generic fibers. One must specify both the generalized curves allowed and the ampleness/contraction convention. Throughout, $\mathcal X_H$ means the standard compactified stack of generalized elliptic curves with stable $H$-level; $X_H$ denotes its coarse space, or the representing scheme in a fine range.

### 6.3 Cusps as moduli points

Analytically, cusps are $\Gamma$-orbits in $\mathbf P^1(\mathbf Q)$. Algebraically, they are degenerate generalized elliptic curves with level structure. These descriptions agree. A matrix carrying $\infty$ to $a/c$ transports the standard degenerating lattice and its level data; two rational boundary points give the same cusp exactly when they lie in the same $\Gamma$-orbit.

For $\Gamma_0(N)$, cusps can be indexed more finely by divisor data in $N$ together with residue classes; the exact formula is less illuminating here than the principle that the level records how its cyclic subgroup distributes between the multiplicative identity component and the polygon component group. At level one there is a single cusp.

## 7. Tate neighborhoods and properness

### 7.1 The Tate curve as a punctured neighborhood

Let $R$ be complete for an ideal generated by $q$, with $q$ topologically nilpotent. Over $R[1/q]$, the Tate curve has the analytic presentation

$$
E_q=\mathbf G_m/q^{\mathbf Z}. \tag{7.1}
$$

It extends over $R$ as a generalized elliptic curve with nodal special fiber after the appropriate polygonal model is chosen. Torsion points are described by classes of

$$
\zeta_N^a q^{b/N}. \tag{7.2}
$$

Thus extracting an $N$th root of $q$ and adjoining roots of unity trivializes full level near a cusp. The exponent $b$ measures motion in the component direction; $a$ measures multiplicative torsion.

This book uses $q$ only for local geometry. It is a uniformizer transverse to the boundary, not an invitation to develop Fourier expansions. If a cusp has width $w$, the invariant local parameter is

$$
q_c=e^{2\pi i\tau/w}, \tag{7.3}
$$

or algebraically the corresponding parameter in the completed local ring. At a fine cusp in characteristic prime to the level, the completion is a power-series ring $R[[q_c]]$. Before rigidification it can be a quotient of such a disk by the cusp stabilizer.

### 7.2 The valuative extension theorem

**Theorem 7.1 (stable extension in the proved ranges).** Let $R$ be a discrete valuation ring with fraction field $K$. Fix either a standard level problem whose order is invertible in $R$, or the squarefree-depth-one $\Gamma_0(p)$ problem with the prime-to-$p$ rigidifying normalization branch used in Chapter 8. A smooth generic object extends, after a finite extension of $R$ if necessary, to the corresponding stable generalized elliptic object. Given two such extensions and an identification of their generic fibers, that identification extends uniquely after the canonical contractions required by the chosen compactification.

**Proof.** Potential semistable reduction gives, after finite base change, a proper regular model whose identity component is either an elliptic scheme or a multiplicative group and whose minimal semistable fiber is smooth or polygonal. The identity section selects the smooth group locus. The established contraction theorem then produces the generalized elliptic model selected by the retained level divisor.

When the level order is invertible, torsion is finite étale, so the generic level extends over the normal trait after the finite base change. The complete Tate charts show which polygon and contraction make its divisor ample; they also show that every boundary deformation is obtained in this way. In the selected $\Gamma_0(p)$ case, the integral extension is the proper normalized Deligne--Rapoport moduli problem: the subgroup is extended as the finite locally free cyclic divisor in that problem, and its two boundary charts are the multiplicative and component charts. This is precisely where the prime-depth hypothesis is used. A scheme-theoretic closure inside an arbitrary bad-level torsion group would not by itself prove flatness, cyclicity, or ampleness.

For uniqueness, the graph of a generic isomorphism extends across the stable marked model. Equivalently, both candidates are the canonical contractions selected by the same ample level divisor, so the contraction universal property identifies them uniquely. $\square$

The finite extension in the theorem is part of the stack-valued valuative criterion: for a proper Deligne--Mumford stack, extension after a finite extension of the trait is the relevant existence statement. It does not by itself descend the stable object to the original trait. Descent over the original DVR requires an effective descent datum, and a generic object can have a genuine stable-reduction obstruction before ramified base change. In particular, one must not replace the theorem by the false assertion that every elliptic curve already has semistable reduction over every DVR.

### 7.3 Proper compactified modular curves

**Theorem 7.2 (compactification in the proved ranges).** Over the base on which the level order is invertible, the standard compactified stack $\mathcal X_H$ is smooth, proper, and flat of relative dimension one. Its boundary

$$
\mathcal C_H=\mathcal X_H\setminus\mathcal Y_H
$$

is a relative effective Cartier divisor. As a stack over the base it is proper, flat, and quasi-finite; its pullback to every fine cover and its coarse image are finite. Where the whole problem is represented by a scheme, the boundary itself is finite over the base. Separately, the squarefree-depth-one $\Gamma_0(p)$ normalization with prime-to-$p$ rigidifying branch is projective, proper, normal, and flat; its cusps are Cartier, while its supersingular points have the nonsmooth semistable equation analyzed in Chapter 8. No corresponding assertion is made here for deeper $p$-power level or an arbitrary bad-level coarse quotient.

**Proof.** On the good-level base, boundedness and the stable extension theorem give finite presentation, separatedness, and properness. The elliptic deformation calculation and the complete Tate charts give formal smoothness of relative dimension one everywhere; smoothness supplies flatness. The Tate parameter cuts out the boundary by a non-zero-divisor. The selected prime-level assertions are the global consequences of its normalized integral moduli construction and its ordinary, supersingular, and cusp charts; Chapter 8 recalls the decisive local equation. $\square$

The scope matters. Smoothness is asserted on the good-level base. At a level prime, properness and flatness have been established here only for the selected prime-depth problem; even there smoothness fails at the supersingular crossings.

### 7.4 Boundary maps and cusp widths

The forgetful map $X_{H'}\to X_H$ is finite when $H'\subset H$. Away from cusps and level primes, it is finite étale under the same freeness hypotheses as before. At a cusp with widths $w'$ and $w$, the completed map has the form

$$
R[[q_c]]\longrightarrow R'[[q_{c'}]],
\qquad q_c\longmapsto u q_{c'}^{e}, \tag{7.4}
$$

for a unit $u$ and $e=w'/w$ after compatible choices. Thus compactification necessarily introduces ramification. Even a level map that is étale on $Y$ is generally ramified on $X$.

### 7.5 Worked boundary examples

For $X(1)$ a rigidified Tate chart has completed base $\mathbf Z[[q]]$. The unrigidified stack still remembers the automorphisms of the standard generalized elliptic curve, whereas its coarse completed local ring is a one-variable power-series ring. The coarse invariant $j$ has a pole of order one there, so $j^{-1}$ is a coarse local parameter. Consequently

$$
X(1)\simeq\mathbf P^1_{\mathbf Z},
$$

with the cusp at $j=\infty$.

For $X_0(p)$, the cusp $\infty$ can be represented on a Tate curve by the multiplicative subgroup $\mu_p$, while the other standard cusp is represented after adjoining $q^{1/p}$ by a subgroup generated in the component direction. The involution sending $(E,C)$ to $(E/C,E[p]/C)$ exchanges these two boundary behaviors. This is geometry of degenerating isogenies; no expansion of a modular form is required.

## 8. Integral modular curves and their special fibers

### 8.1 Good primes

Fix a level problem of total level $N$, and let $p\nmid N$. Over $\mathbf Z_p$, torsion of order $N$ is finite étale. In a fine range the compactified modular curve $X_H$ is smooth and proper over $\mathbf Z_p$; in general the compactified stack is smooth proper, and one may either retain it or pass to a sufficiently rigid auxiliary prime-to-$p$ cover before descending statements insensitive to stabilizers.

The special fiber is a smooth proper curve and the specialization map on geometric points is compatible with forgetting level. For every $\ell\ne p$, smooth proper base change gives an identification

$$
H^1(X_{H,\overline{\mathbf Q}_p},\mathbf Q_\ell)
\simeq
H^1(X_{H,\overline{\mathbf F}_p},\mathbf Q_\ell), \tag{8.1}
$$

equivariant for the decomposition group after the usual choice of geometric points. In particular inertia acts trivially. This is the precise good-reduction input later cohomological arguments need.

### 8.2 Why level primes are different

If $p\mid N$, the closure of an étale subgroup in a family need not remain étale, generators can coalesce, and the ordinary and supersingular loci behave differently. Drinfeld divisors guarantee a finite-flat moduli condition, but they do not guarantee smoothness. The local deformation ring now remembers both deformation of the elliptic curve and deformation of its connected torsion.

Three statements must therefore be kept separate:

1. the compactified moduli problem is proper and flat;
2. its total space is regular;
3. its special fiber has normal crossings.

None follows formally from the others, and all can be spoiled on a coarse space by small-characteristic automorphisms.

### 8.3 The $X_0(p)$ model with auxiliary rigidification

Let $p$ be any prime, and choose a prime-to-$p$ rigidifying normalization branch, for example the branch supplied by full level $M\geq3$ with $(M,p)=1$. At the boundary this is a label on the normalized auxiliary cover, not a second ample divisor on the same polygon. Consider the resulting fine Deligne--Rapoport $\Gamma_0(p)$ compactification over an unramified discrete valuation ring above $p$. Its geometric special fiber has exactly two components. On the ordinary locus, a cyclic subgroup of rank $p$ is either of multiplicative type or étale type. Forgetting the subgroup identifies the two normalized loci with the prime-to-$p$ modular curve, with the degeneracy maps given by identity and Frobenius in opposite orders. Their closures meet at supersingular points.

At a supersingular point the strict henselian completed local ring of the rigidified model has the semistable form

$$
W(\bar k)[[x,y]]/(xy-p) \tag{8.2}
$$

after a compatible choice of local parameters. Hence the total space is regular and the special fiber has an ordinary double point $xy=0$. This gives a semistable curve over $\mathbf Z_p$ in this exact squarefree Iwahori-level situation.

The auxiliary branch is not cosmetic: it removes automorphisms and makes the displayed local ring a scheme-local statement. Dropping it requires stack language or a quotient analysis. The same fine crossing theorem remains valid for $p=2$ and $p=3$ because no stabilizer quotient is taken. Allowing $p^2$ level or a general $\Gamma_1(p^r)$ structure changes the local problem and may require modifications or ramified base change; no blanket semistability claim is made in those cases.

### 8.4 Reduction maps needed later

At a good prime, reduction sends an integral level object to the same kind of level object on a smooth elliptic curve. At the $X_0(p)$ prime, it records which branch the subgroup occupies:

$$
\begin{array}{ccc}
\text{generic cyclic }p\text{-isogeny}&&\\
&\searrow&\text{multiplicative branch }(\ker F)\\
&\nearrow&\text{étale branch }(\ker V\text{ transported by duality}),
\end{array}
$$

with intersection at supersingular objects. More precisely, relative Frobenius $F:E\to E^{(p)}$ has connected kernel on an ordinary curve, while $V:E^{(p)}\to E$ has étale kernel; identifying the second branch on a fixed source uses the dual-isogeny or Frobenius-twist description. At a supersingular curve neither branch is separated by the ordinary connected--étale decomposition, causing the two components to meet.

For cohomology, (8.2) says exactly what good reduction no longer says: inertia need not act trivially, and comparison with the special fiber requires nearby-cycle or semistable methods. This book records the geometry but postpones the operator and Frobenius relations built from it.

### 8.5 A regularity warning

Normalization is not the same as regularization. If a coarse modular curve has a quotient singularity, normalizing removes nonnormal crossings but may leave a singular normal surface. Conversely, a regular total space can have a reducible singular special fiber, as (8.2) shows. Any later appeal to smooth proper base change must use the smooth model at a good prime, not merely a proper regular model at a level prime.

## 9. Quaternion algebras with one split real place

### 9.1 Why another family of curves appears

Modular curves arise from $\operatorname{GL}_2$ over $\mathbf Q$. Their noncompactness is tied to rational parabolic subgroups, visible geometrically as cusps. For arithmetic applications one also wants curves carrying essentially the same rank-one symmetric geometry but with compact complex fibers. Quaternion algebras supply them.

Let $F$ be a totally real field of degree $d$, and let $B$ be a quaternion algebra over $F$ split at exactly one real embedding

$$
\tau_0:F\hookrightarrow\mathbf R.
$$

Thus

$$
B\otimes_{F,\tau_0}\mathbf R\simeq M_2(\mathbf R),
\qquad
B\otimes_{F,\tau}\mathbf R\simeq\mathbf H
\quad(\tau\ne\tau_0). \tag{9.1}
$$

The split factor acts on the upper half-plane by fractional linear transformations. Every ramified real factor has compact projective unit group, so it contributes no noncompact symmetric direction. The resulting symmetric space is one-dimensional.

When $F=\mathbf Q$, “split at exactly one real place” means split at the unique real place. The algebra can still be division because of finite ramification. For instance, the quaternion algebra over $\mathbf Q$ ramified at two finite primes $r$ and $s$ is indefinite at infinity and division over $\mathbf Q$; it produces a compact Shimura curve.

### 9.2 Orders and Eichler level

Let $\mathfrak D_B$ be the product of finite primes where $B$ is ramified. At $v\nmid\mathfrak D_B$ choose an identification $B_v\simeq M_2(F_v)$. An Eichler order of level $\mathfrak N$, with $(\mathfrak N,\mathfrak D_B)=1$, is locally maximal at ramified places and at $v\mid\mathfrak N$ is conjugate to

$$
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in M_2(\mathcal O_{F_v}):c\in\mathfrak N\mathcal O_{F_v}
\right\}. \tag{9.2}
$$

Its completed unit group gives a compact open

$$
K_0(\mathfrak N)=\widehat{\mathcal O}^{\times}
\subset (B\otimes_F\mathbf A_{F,f})^{\times}. \tag{9.3}
$$

More general compact opens allow full, principal, or oriented level at selected split places. “Sufficiently small,” or **neat**, means that the arithmetic stabilizers contain no nontrivial finite-order elements in their action on the symmetric domain. Neatness plays the same role as rigid full level on a modular curve: it replaces an orbifold by a curve and permits a universal moduli object when a moduli interpretation is available.

### 9.3 Positive norm and the chosen half-plane

An element $b\in B^{\times}$ maps under $\tau_0$ to $\operatorname{GL}_2(\mathbf R)$, with determinant $\tau_0(\operatorname{nrd}b)$. Only positive determinant preserves $\mathfrak H$. Define

$$
B_+^{\times}=\{b\in B^{\times}:\tau_0(\operatorname{nrd}b)>0\}. \tag{9.4}
$$

For a finite adele $g\in B^{\times}(\mathbf A_{F,f})$ and compact open $K$, put

$$
\Gamma_g=B_+^{\times}\cap gKg^{-1}. \tag{9.5}
$$

After projecting the split real factor to $\operatorname{PGL}_2^+(\mathbf R)$, this is a discrete arithmetic subgroup. It acts properly discontinuously on $\mathfrak H$, with finite stabilizers unless $K$ is neat.

The adjective “split” must always refer to the selected real place in this construction. If $B$ were ramified at every real place, its symmetric space would be zero-dimensional and one would obtain a finite Shimura set, not a curve. If it split at two real places, the symmetric space would have complex dimension two.

## 10. The analytic Shimura curve

### 10.1 The adelic quotient

Let $G=\operatorname{Res}_{F/\mathbf Q}B^{\times}$. The Shimura datum selects the conjugacy class of the homomorphism at $\tau_0$ defining the complex structure on $\mathfrak H^{\pm}=\mathbf C\setminus\mathbf R$. For compact open $K\subset B^{\times}(\mathbf A_{F,f})$, define

$$
\operatorname{Sh}_K(B)(\mathbf C)
=B^{\times}\backslash
\bigl(\mathfrak H^{\pm}\times B^{\times}(\mathbf A_{F,f})/K\bigr). \tag{10.1}
$$

Here $B^{\times}=G(\mathbf Q)$ acts on both factors on the left. The use of both half-planes avoids imposing a positivity condition globally. Choosing the upper half-plane rewrites (10.1) as a finite disjoint union

$$
\operatorname{Sh}_K(B)(\mathbf C)
\simeq\coprod_{[g]}\Gamma_g\backslash\mathfrak H, \tag{10.2}
$$

where $[g]$ ranges through the appropriate reduced-norm classes and $\Gamma_g$ is as in (9.5).

Formula (10.2) already proves that the quotient is a complex curve. If $K$ is neat, each quotient is a smooth Riemann surface. Otherwise the honest object is an orbifold, or analytically a stack, and the displayed topological quotient is its coarse Riemann surface.

### 10.2 Compactness and the absence of cusps

**Theorem 10.1.** If $B$ is a division algebra over $F$, every component $\Gamma_g\backslash\mathfrak H$ is compact. Equivalently, the Shimura curve has no cusps.

**Proof.** The compactness criterion for arithmetic quotients of a rank-one symmetric domain says that $\Gamma\backslash\mathfrak H$ is noncompact exactly when the underlying adjoint group has a proper $F$-parabolic subgroup. In type $A_1$, such a parabolic is the stabilizer of an $F$-rational boundary point and its unipotent radical supplies a nonidentity $F$-rational unipotent. Conversely, a rational unipotent fixes a rational boundary point and produces a cusp neighborhood, so the criterion is an equivalence rather than merely a sufficient condition.

If $u\in B^\times$ is unipotent, then $(u-1)^2=0$ in the degree-two algebra. A division algebra has no nonzero nilpotents: if $x^2=0$ and $x\ne0$, multiplying by $x^{-1}$ gives $x=0$. Thus $u=1$, and $PB^\times$ has no proper rational parabolic. The compactness criterion applies to every arithmetic subgroup $\Gamma_g$, proving that every quotient in (10.2) is compact. $\square$

The proof exposes the structural contrast with modular curves. In $M_2(F)$ the upper triangular unipotent matrices fix rational boundary points and create cusps. In a division quaternion algebra no such matrices exist. Compactification adds nothing:

$$
X_K=Y_K=\operatorname{Sh}_K(B)
\qquad(B\text{ division}). \tag{10.3}
$$

If $B=M_2(\mathbf Q)$, (10.1) recovers adelic modular curves, and compactification is again necessary. Thus the absence of cusps is not a consequence of quaternion notation; it is a consequence of division.

### 10.3 A compact example

Let $B/\mathbf Q$ be ramified at the finite primes $2$ and $3$ and split at infinity. Its ramification set has even cardinality, so such a quaternion algebra exists, and it is division. Choose a maximal order $\mathcal O$ and a neat principal congruence subgroup

$$
K(M)=\{u\in\widehat{\mathcal O}^{\times}:u\equiv1\pmod{M\widehat{\mathcal O}}\}
$$

for $M\geq3$ prime to $6$. Then

$$
\bigl(B_+^{\times}\cap K(M)\bigr)\backslash\mathfrak H
$$

is a smooth compact Riemann surface. It has no cusp points to add and no Tate parameter. At the primes $2$ and $3$ the algebra is ramified, so the integral geometry is bad and requires separate local analysis; at primes away from $6M$ the PEL curve has a smooth integral model, which is proper under either additional alternative of Theorem 14.1.

This example is “explicit” at the conceptual level relevant here: the finite ramification set proves division and compactness, while the principal level proves rigidity. Computing its genus requires volume and elliptic-cycle formulas beyond the construction itself.

## 11. PEL moduli for quaternionic curves

### 11.1 Why the analytic quotient is not yet arithmetic geometry

The analytic quotient provides a Riemann surface, but later arguments require a curve over a number field, integral models, reduction maps, and algebraic correspondences. A moduli interpretation supplies these objects. The relevant abelian varieties carry endomorphisms by an order in a quaternionic algebra, a polarization compatible with an involution, a determinant condition selecting the desired complex signature, and finite level.

There is an important qualification. The bare pair $(F,B)$ does not by itself always define a PEL moduli problem with group exactly $B^{\times}$. Over $\mathbf Q$, an indefinite quaternion algebra has the familiar moduli of false elliptic curves, namely abelian surfaces with quaternionic multiplication. Over a general totally real field one often enlarges the datum, for example by an auxiliary CM extension, to obtain a PEL similitude group whose derived group is the one attached to $B^1$. The resulting PEL Shimura curve is a finite central modification of the quaternionic curve, with the same adjoint analytic components. We state the moduli construction under explicit PEL data and do not pretend that it is canonical from $B$ alone.

### 11.2 The PEL datum

Fix the following data:

- a finite-dimensional semisimple $\mathbf Q$-algebra $D$ with a positive involution $*$;
- a finite-dimensional left $D$-module $V$;
- a nondegenerate alternating form $\psi:V\times V\to\mathbf Q$ satisfying
  $$
  \psi(dx,y)=\psi(x,d^*y);
  $$
- a homomorphism $h:\mathbf C\to\operatorname{End}_D(V_{\mathbf R})$ such that $h(i)^2=-1$ and $(x,y)\mapsto\psi(x,h(i)y)$ is positive definite;
- a $*$-stable order $\mathcal O_D\subset D$ and a lattice $\Lambda\subset V$ on which $\psi$ is integral up to a fixed localization.

Let $G$ be the group of $D$-linear similitudes:

$$
G(R)=\left\{g\in\operatorname{Aut}_{D\otimes R}(V\otimes R):
\psi(gx,gy)=\nu(g)\psi(x,y),\ \nu(g)\in R^{\times}\right\}. \tag{11.1}
$$

Assume that the associated Hermitian symmetric domain has complex dimension one and that the derived adjoint datum is the quaternionic datum of Sections 9--10. Concretely, at the distinguished real place the signature is $(1,1)$ in the relevant two-dimensional factor, while every other real factor is definite. These are the **quaternionic PEL hypotheses** used below.

We also fix the integral data that make this one exact moduli problem: a polarization kernel type, a compatible lattice genus, the universal determinant polynomial law, and an open-and-closed component union stable under every asserted descent. If the PEL group is a nontrivial central modification of the basic quaternionic group, the PEL curve is a finite central cover; neither its component set nor its universal family is silently identified with that of the basic group.

The reflex field $E$ is the field of definition of the conjugacy class of the cocharacter determined by $h$. It need not equal $F$ and must not be silently replaced by $\mathbf Q$.

### 11.3 Objects of the moduli problem

For a connected $E$-scheme $S$, the PEL groupoid classifies tuples

$$
(A,\iota,\lambda,\bar\eta^K), \tag{11.2}
$$

where:

1. $A/S$ is an abelian scheme of relative dimension $\frac12\dim_{\mathbf Q}V$;
2. $\iota:\mathcal O_D\to\operatorname{End}_S(A)$ is an action;
3. $\lambda:A\to A^\vee$ is an actual polarization of the fixed kernel type, whose degree is invertible at every prime designated good and whose Rosati involution satisfies
   $$
   \iota(d)^\dagger=\iota(d^*);
   $$
4. $\bar\eta^K$ is a $K$-orbit of $D$-linear trivializations between $V\otimes\mathbf A_f$ and the rational adelic Tate module of $A$, carrying $\psi$ to the Weil pairing up to the same similitude factor;
5. the determinant condition below holds.

Isomorphisms respect the action, pull the target polarization back to the source polarization, and preserve the level orbit. A different PEL presentation may instead use a specified prime-to-a-set quasi-polarization category, but that is a different exact moduli problem whose arrows, lattice genus, and component set must be fixed before applying the representability theorem. Throughout this chapter the actual-polarization convention above is in force.

### 11.4 The determinant condition

An action on an abelian scheme is not enough to select the desired Shimura curve. The action induced on $\operatorname{Lie}A$ could have the wrong signature. The **Kottwitz determinant condition** requires, for every $d\in\mathcal O_D$,

$$
\det\bigl(T-\iota(d)\mid\operatorname{Lie}A\bigr)
=\det\bigl(T-d\mid V^{-1,0}\bigr), \tag{11.3}
$$

where the right side is the polynomial prescribed by the Hodge decomposition defined by $h$, interpreted over the reflex field.

At the split real place this forces the varying signature that contributes one tangent direction. At the ramified real places it forces the definite type and contributes none. Without (11.3), the same endomorphism algebra can act on abelian varieties belonging to components of different dimension or even to a different Shimura variety.

The deformation-theoretic meaning is equally useful. First-order deformations of $(A,\iota,\lambda)$ correspond to $\mathcal O_D$-stable isotropic lifts of the Hodge subbundle. Under the stated signature, the local model is one-dimensional and smooth at unramified hyperspecial primes. The determinant condition is therefore what turns a broad endomorphism problem into a curve.

### 11.5 Polarization is structural, not decorative

The polarization has three jobs. It cuts the endomorphism group down to a reductive similitude group, supplies the alternating form used to define level, and imposes positivity at infinity. If one classifies abelian varieties with an $\mathcal O_D$-action but no compatible polarization, the moduli space is usually too large and need not be proper.

In the classical indefinite quaternion case over $\mathbf Q$, choose a positive involution $*$ on $B$, often of the form

$$
b^*=\delta^{-1}\bar b\,\delta
$$

for a suitable pure quaternion $\delta$. A false elliptic curve is an abelian surface $A$ with an action of a maximal order $\mathcal O_B$ and a polarization whose Rosati involution induces $*$. The tangent representation satisfies the degree-two determinant condition. A sufficiently small prime-to-discriminant level kills the remaining automorphisms.

**Counterexample.** Canonical quaternionic conjugation is not automatically the positive involution required by a chosen PEL polarization at every real factor. Writing “Rosati equals conjugation” without verifying positivity can define no complex objects at all. The involution and $h$ are part of the datum.

### 11.6 Level and representability

At primes where the lattice is self-dual and the algebra is unramified, a hyperspecial compact open stabilizes $\Lambda\otimes\mathbf Z_p$. Away from those primes, level is a $K$-orbit of trivializations rather than a single basis. A sufficiently deep principal congruence level supported at primes invertible on the base is neat and kills automorphisms; in the standard integral matrix settings, level at least three is the familiar sufficient bound. The depth condition belongs to the chosen lattice and cannot be read from an abstract compact open without that integral structure.

**Theorem 11.1.** Under the quaternionic PEL hypotheses, the moduli problem (11.2) is a Deligne--Mumford stack of relative dimension one over its reflex field. For neat $K$ it is represented by a smooth quasi-projective curve and carries a universal abelian scheme with PEL structure. For nonneat $K$ it has a coarse algebraic curve, but the universal object exists naturally only on the stack. Its complex analytification is the PEL adelic quotient. In the direct case this is the selected quaternionic quotient of (10.1); for the fixed nontrivial central modification it maps finitely to that quotient through the specified effective central quotient.

**Proof.** Choose auxiliary full level $M\geq3$, prime to every fixed polarization degree. Polarized abelian varieties of the required dimension and degree with full $M$-level are represented by a quasi-projective scheme. An $\mathcal O_D$-action is the finite collection of endomorphisms associated with generators of the order, subject to its multiplication relations. Rosati compatibility is a closed equality of endomorphisms, the determinant condition is a closed polynomial identity on $\operatorname{Lie}A$, and the prescribed prime-to-$M$ level orbit is finite étale. Fixing the required open-and-closed determinant and component conditions therefore cuts out a quasi-projective fine scheme.

At a characteristic-zero geometric point, deformation theory identifies first-order deformations with $\mathcal O_D$-stable isotropic lifts of the Hodge subspace. All definite real factors have a unique lift, while the active signature-$(1,1)$ factor contributes the tangent line to a projective line. Thus the completed local ring is a one-variable power-series ring. There are no obstructions because the relevant Grassmannian local model is smooth. The fine scheme is consequently smooth of pure dimension one.

The finite group changing the auxiliary level acts on this scheme. Its quotient stack is Deligne--Mumford because polarizations give finite automorphism groups. If $K$ is neat, every stabilizer is trivial and the quotient is the desired fine scheme. Otherwise the finite-inertia quotient has a coarse algebraic curve, while its universal tuple remains on the stack. Finally, the polarized Hodge-lattice classification identifies its complex points and local period coordinates with the PEL adelic quotient; Proposition 12.2 gives the detailed inverse. In the nontrivial central-modification case, the effective finite central quotient fixed with the datum supplies the asserted finite comparison. $\square$

The theorem is intentionally conditional on a complete PEL datum. It does not identify every quaternionic canonical model with a naive moduli scheme of abelian varieties.

## 12. Algebraic and canonical Shimura curves

### 12.1 From complex points to a curve over the reflex field

For PEL data, Theorem 11.1 constructs the algebraic curve directly. For a bare quaternionic Shimura datum, the canonical-model theorem supplies a smooth algebraic curve $\operatorname{Sh}_K(B)$ over its reflex field, characterized by reciprocity on special points and compatibility across level. A PEL realization or central auxiliary construction compares this curve with an algebraic PEL curve by finite maps.

The word **canonical** concerns descent, not only existence. A complex algebraic curve can often be descended in several ways. The canonical model is the one whose Galois action on connected components and special points is prescribed by the Shimura reciprocity law. For the present book, its concrete consequences are:

- level-changing maps and right adelic actions are defined over their predicted fields;
- connected components descend with a norm-class Galois action;
- at good finite places, the canonical model agrees with the smooth PEL integral model when that moduli description is available.

### 12.2 Properness

**Theorem 12.1.** If $B$ is division, the canonical Shimura curve at any compact open level is proper over its reflex field. If $K$ is neat it is a smooth projective level curve. When a PEL realization has been fixed, the corresponding nonneat moduli stack is smooth proper with finite stabilizers; its coarse space is still a smooth projective curve in characteristic zero, although the stack-to-coarse map is ramified at elliptic points and a universal object need not descend.

**Proof.** The complex analytification is compact by Theorem 10.1. The algebraic curve is quasi-projective by construction. A smooth quasi-projective complex curve is proper exactly when its analytification is compact, so every complex base change is proper. Properness descends to the reflex field. $\square$

There is no boundary divisor and no $q$-parameter. Attempting to add cusps to a division-algebra Shimura curve would add points with no moduli-theoretic or analytic origin.

### 12.3 Coarse spaces and universal abelian schemes

Suppose $K$ is not neat. A geometric PEL object may have a finite automorphism group. The coarse curve still exists and is proper, but the universal abelian scheme does not generally descend to it. Cohomology of the coarse curve and the stack agree with prime-to-stabilizer rational coefficients in the tame setting, but integral statements can differ. The safe methods are to retain the stack or pass to a neat normal cover $K'\triangleleft K$, perform the construction there, and take invariants only after checking coefficient primes.

This is exactly parallel to $X_0(N)$. A coarse point records an isomorphism class, not an object with a chosen descent. Later correspondences may be defined on coarse curves even when universal abelian varieties are not.

### 12.4 Comparison of moduli and adelic descriptions

There are now two descriptions of the same curve, and it is worth proving their agreement rather than using identical notation as a substitute for a comparison. Fix a neat level $K$ and a connected union of PEL components selected by the central modification. The selected integral type includes an equivariant normalization of the polarization module: if the form on the lattice attached to $g$ is $c(g)\psi$, then

$$
c(qg)\nu(q)=c(g)
\qquad\bigl(q\in G(\mathbf Q)\text{ relating representatives in the selected union}\bigr). \tag{12.0}
$$

Without this condition the double quotient would classify only rational polarization classes, not the actual polarizations used in the moduli problem. The period map sends

$$
(A,\iota,\lambda,\bar\eta^K)
$$

to its rational homology $V_A=H_1(A(\mathbf C),\mathbf Q)$, its Hodge homomorphism $h_A$, and the finite-adelic marking supplied by $\bar\eta^K$. Choosing a $D$-linear similitude $V\simeq V_A$ produces a point $[h_A,g]$ of the adelic double quotient.

**Proposition 12.2 (period comparison).** Under the quaternionic PEL hypotheses and neatness, the period map is a biholomorphism from the complex PEL moduli curve onto the selected union of components of

$$
G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/K). \tag{12.1}
$$

It is compatible with level change, right translation, the reduced-norm component label, and the universal isogenies attached to commensurable adelic lattices.

**Proof strategy.** The crucial issue is not surjectivity on points but independence from choices and compatibility in families. We first construct the inverse pointwise from a polarized Hodge lattice, then use the variation of Hodge structures to identify the analytic structures.

**Proof.** If the comparison $V\simeq V_A$ is changed by $\gamma\in G(\mathbf Q)$, then $(h_A,g)$ changes to $(\gamma h_A\gamma^{-1},\gamma g)$ and represents the same double coset. Changing the representative of the level orbit replaces $g$ by $gk$ with $k\in K$. Hence the period map is well defined.

Conversely, choose $[h,g]$. The Hodge homomorphism gives

$$
V_{\mathbf C}=V^{-1,0}\oplus V^{0,-1}.
$$

The finite adele $g$ determines the lattice

$$
\Lambda_g=V(\mathbf Q)\cap g\widehat\Lambda
$$

inside $V(\mathbf A_f)$, after scaling centrally if needed to make the polarization integral. Positivity of $h$ and the alternating form makes the complex torus

$$
A_{h,g}(\mathbf C)=V_{\mathbf R}/\Lambda_g
$$

an abelian variety by the Riemann criterion. The $D$-action preserves the lattice, and the normalized integral multiple $c(g)\psi$ gives the required actual polarization of the selected type. The adele $g$ gives the $K$-level orbit, and the Hodge multiplicities are precisely the determinant condition. Thus $[h,g]$ reconstructs a PEL object.

Left multiplication by $q\in G(\mathbf Q)$ carries $\Lambda_g$ isomorphically onto $\Lambda_{qg}$. Together with (12.0), it therefore gives an isomorphism of the reconstructed integral PEL objects, although relative to one fixed reference lattice the same rational map is naturally described as a quasi-isogeny. Right multiplication by $K$ changes only the representative of level. Consequently reconstruction is inverse to the period map on isomorphism classes.

Locally on $X$, the Hodge filtration varies holomorphically. Its tangent space is

$$
\operatorname{Hom}_{\mathcal O_D}(\operatorname{Fil}^1,
H_{\mathrm{dR}}/\operatorname{Fil}^1)
$$

subject to the infinitesimal isotropy condition. In the one-active-place signature this space has dimension one and is the tangent line of the upper half-plane. The period map and its inverse therefore vary holomorphically and have inverse differentials. They are biholomorphic.

Changing $K$ merely forgets part of $g\widehat\Lambda$, so the construction commutes with level maps. Replacing $g$ by $ga$ replaces the lattice by the commensurable lattice $ga\widehat\Lambda$; inclusion after clearing denominators gives exactly the PEL isogeny used in the moduli correspondence. Finally, the component of $[h,g]$ is the abelianized class of $g$, which for the basic quaternionic group is its reduced-norm class. This proves every asserted compatibility. $\square$

The proposition also explains what a central modification changes. It can enlarge the polarization-similitude coordinate and split or join component labels, but it does not change the adjoint upper-half-plane quotient. Accordingly, one must compare a specified component union, not assert without qualification that every auxiliary PEL curve is literally the basic quaternionic curve.

## 13. Reduced norms and components

### 13.1 Strong approximation isolates the obstruction

Let $B^1$ be the reduced-norm-one group. Because $B$ is split at $\tau_0$, $B^1(F_{\tau_0})\simeq\operatorname{SL}_2(\mathbf R)$ is noncompact. Strong approximation for the simply connected group $B^1$ says that, away from the distinguished real place, its rational points are dense in the adelic norm-one group. Consequently the only obstruction to moving one finite adelic representative to another is reduced norm.

Because $B$ is ramified at every real place other than $\tau_0$, the Hasse--Schilling norm condition and preservation of the chosen upper half-plane together impose positivity at every real embedding. Define

$$
F_+^{\times}=F_{>0}^{\times}
=\{a\in F^{\times}:\tau(a)>0
\text{ for every real embedding }\tau:F\hookrightarrow\mathbf R\}. \tag{13.1}
$$

Then, for the upper-half-plane component convention,

$$
\pi_0\bigl(\operatorname{Sh}_K(B)(\mathbf C)\bigr)
\simeq
F_+^{\times}\backslash\mathbf A_{F,f}^{\times}/\operatorname{nrd}(K), \tag{13.2}
$$

up to the explicitly chosen central/similitude convention. The qualification is necessary for auxiliary PEL groups, whose multiplier can replace reduced norm by a closely related quotient.

### 13.2 Proof of the component formula

Map a point represented by $(z,g)$ to the class of $\operatorname{nrd}(g)$. Left multiplication by $b\in B^{\times}$ changes the norm by $\operatorname{nrd}(b)$, and right multiplication by $k\in K$ changes it by $\operatorname{nrd}(k)$. Choosing $z$ in the upper half-plane restricts the rational norm to the positive subgroup. Thus the map is well defined.

Surjectivity follows because local reduced norm $B_v^{\times}\to F_v^{\times}$ is surjective at every finite place. If $g_1$ and $g_2$ have the same norm class, alter $g_2$ on the left by a rational element and on the right by $K$ so that $g_2g_1^{-1}$ has norm one. Strong approximation for $B^1$ then moves it into the same analytic component. This proves injectivity.

The proof shows why an ordinary ideal class group is not always the answer. The quotient depends on $\operatorname{nrd}(K)$ and on positivity. It can be a narrow ray class quotient, and changing level can split components.

### 13.3 A component calculation over $\mathbf Q$

Let $F=\mathbf Q$ and let $K=\widehat{\mathcal O}^{\times}$ for a maximal order in an indefinite quaternion algebra. Local reduced norms satisfy

$$
\operatorname{nrd}(K)=\widehat{\mathbf Z}^{\times}.
$$

Therefore

$$
\mathbf Q_{>0}^{\times}\backslash\mathbf A_f^{\times}/
\widehat{\mathbf Z}^{\times}=1, \tag{13.3}
$$

because every finite idele is a positive rational number times a unit idele. The Shimura curve is connected. It is geometrically connected over its canonical field in this standard case.

At principal level $K(M)$, the norm subgroup is smaller, typically containing $1+M\widehat{\mathbf Z}$ rather than all units. The quotient acquires residue-class components. A determinant-changing adelic element permutes them, just as $\operatorname{GL}_2(\mathbf Z/N\mathbf Z)$ permutes Weil-pairing components of $Y(N)$.

### 13.4 Arithmetic versus geometric components

The finite set (13.2) describes complex connected components. The canonical model may have a smaller field of definition over which Galois permutes these components. A connected curve over the reflex field need not be geometrically connected if its field of constants is a nontrivial class field. Shimura reciprocity identifies the Galois permutation through the Artin map applied to the norm/multiplier class.

For later cohomology one usually either selects a geometrically connected component over its field of definition or takes the entire canonical curve and retains the component permutation. Silently treating (13.2) as a single component can change both $H^0$ and the induced Galois representation on $H^1$.

## 14. Integral models of Shimura curves

### 14.1 What “good” means

Let $v$ be a finite place of the reflex field above a rational prime $p$, and let $\mathfrak p$ be the corresponding place of $F$. A good PEL place satisfies all of the following:

- $D$ and its involution are unramified at $p$ in the relevant sense;
- the lattice is self-dual;
- $K_p$ is hyperspecial for the self-dual lattice;
- the polarization degree and auxiliary level are prime to $p$;
- the determinant local model is the unramified one dictated by the signature.

At such a place the same tuple (11.2), now over $\mathcal O_{E,v}$ with prime-to-$p$ level, defines the integral PEL model $\mathscr S_K$.

**Theorem 14.1 (good integral model with exact properness alternatives).** Under these hypotheses and with neat prime-to-$p$ level, the integral PEL functor is represented by a smooth quasi-projective scheme $\mathscr S_K$ of relative dimension one over $\mathcal O_{E,v}$. Its generic fiber is the canonical curve of the selected PEL-exact datum, and it carries the universal PEL abelian scheme. If the adjoint quaternionic datum is anisotropic and either

1. the selected PEL realization is the direct quaternionic trace realization $D=V=B$, or
2. every trait degeneration on a principal-level cover satisfies the established boundary-rationality condition,

then $\mathscr S_K$ is proper, hence projective. For a nontrivial central modification, this conclusion applies first to the PEL cover; a quotient model requires the effective quotient to be treated separately.

**Proof.** Integral representability follows by applying the same auxiliary-level construction as in Theorem 11.1 over $\mathcal O_{E,v}$: the unramified order acts on the self-dual lattice, the polarization is prime to $p$, and the determinant law has coefficients in the reflex ring. The generic fiber is therefore the PEL canonical model.

For smoothness, lift a geometric special-fiber point across a square-zero thickening. Deformation theory for abelian schemes with endomorphisms and polarization reduces the lift to an $\mathcal O_D$-stable isotropic lift of the Hodge filtration in relative de Rham homology. The self-dual hyperspecial lattice makes this module free, and the unramified determinant condition decomposes it into its embedding factors. Every definite factor has a unique filtration; the active factor asks for one direct-summand line in a free rank-two module. Its local model is $\mathbf P^1$, hence smooth of relative dimension one. Lifts exist across every square-zero thickening, so the integral moduli scheme is formally smooth, and finite presentation makes it smooth.

Properness is a separate step. In the direct trace realization, the common rational quaternionic module excludes a nonzero toric part by its module-dimension constraint. In the second case, boundary rationality turns a nonzero Raynaud torus into a nonzero rational isotropic subspace whose stabilizer has proper parabolic image; anisotropy then excludes it. After passing to a principal prime-to-$p$ level, level rigidity and the good-reduction criterion descend potential good reduction to the original trait. The action, polarization, and level extend uniquely, so the valuative criterion gives properness. Without either alternative, separate local Tate-module filtrations do not manufacture the rational boundary subspace, and the argument stops at smooth quasi-projective representability. $\square$

Under either properness alternative, the theorem prepares exactly the hypothesis used by smooth proper base change. For $\ell\ne p$,

$$
H^1(\operatorname{Sh}_{K,\overline E},\mathbf Q_\ell)
\simeq
H^1(\mathscr S_{K,\overline k_v},\mathbf Q_\ell), \tag{14.1}
$$

and inertia at $v$ acts trivially.

### 14.2 Good reduction is a property of datum and level

It is imprecise to say that a Shimura curve has good reduction at every prime not dividing the discriminant of $B$. The PEL algebra may include auxiliary ramification, the polarization lattice may fail to be self-dual, and the compact open may have nonhyperspecial level. The correct finite bad set includes ramification of the datum, non-self-duality, polarization degree, and level.

Conversely, a prime dividing an arbitrarily chosen equation need not be a bad prime of the canonical curve. Good reduction is detected by the integral moduli datum, not by denominators in a presentation.

### 14.3 Split primes with Iwahori level

Suppose $\mathfrak p\nmid\mathfrak D_B$, so $B_{\mathfrak p}\simeq M_2(F_{\mathfrak p})$, but replace hyperspecial level by an Eichler/Iwahori subgroup of squarefree depth one. Assume the actual parahoric datum satisfies the flat-local-model hypothesis: after Morita equivalence its determinant, isotropy, and any additional conditions cut out the rank-two incidence model. Under this hypothesis, neat auxiliary level, and the minuscule one-dimensional signature, the local model has two smooth branches crossing normally. The completions of the strict henselian local rings of the parahoric PEL space at crossing points have the form

$$
\widehat{\mathcal O^{\mathrm{sh}}}[[x,y]]/(xy-\varpi) \tag{14.2}
$$

in the basic semistable case.

This is the quaternionic analogue of (8.2). With either properness alternative of Theorem 14.1, the resulting curve is a proper regular semistable model. Without such an alternative the equation is still a local statement about the represented parahoric space, not a proof of projectivity. It is not a theorem for arbitrary parahoric level, ramified coefficient algebra, or nonminuscule signature.

### 14.4 The boundary at a ramified algebra place

When $\mathfrak p\mid\mathfrak D_B$, hyperspecial level for $B_{\mathfrak p}^{\times}$ does not exist, and the unramified rank-two local model of Sections 14.1--14.3 does not apply. The local foundational package used in this volume contains no ramified-place uniformization theorem. We therefore make no claim here about a regular or semistable model, rational components, or a dual graph at such a place. This is a genuine boundary of the construction, not a conclusion obtainable by replacing a split matrix algebra with a division algebra in (14.2).

### 14.5 Specialization and cohomological scope

At a good place, a PEL abelian scheme and its prime-to-$p$ level reduce without changing type. The reduction map sends geometric generic points extending over an unramified valuation ring to points of the smooth special fiber. Equality (14.1) transfers finite level maps and prime-to-$p$ correspondences to cohomology.

At a selected Iwahori place satisfying Section 14.3, the special fiber and its dual graph describe the failure of smoothness. Proper base change compares the cohomology of a proper generic fiber with nearby cycles only when the properness alternative has also been verified; smooth proper base change does not apply. Ramified algebra places remain outside the present integral construction.

## 15. Varying level and adelic actions

### 15.1 A tower, not a single curve

Automorphic symmetry is visible only when all levels are considered together. Let $G$ denote either $\operatorname{GL}_2$ in the modular setting or the quaternionic similitude group under discussion. For compact opens $K'\subset K\subset G(\mathbf A_f)$, forgetting part of the level gives a finite map

$$
\pi_{K',K}:X_{K'}\longrightarrow X_K. \tag{15.1}
$$

On open modular curves it is finite étale away from level primes when stabilizers act freely. On compactified modular curves it can ramify at cusps. On proper division-algebra Shimura curves there are no cusps, so for neat levels and prime-to-characteristic generic fibers it is finite étale. If either level is nonneat, this last assertion is safest as a representable map of stacks; coarse maps can branch at elliptic points.

The maps are transitive:

$$
\pi_{K'',K}=\pi_{K',K}\circ\pi_{K'',K'}
\qquad(K''\subset K'\subset K). \tag{15.2}
$$

If $K'$ is normal in $K$ and both levels are neat, then $X_{K'}\to X_K$ is Galois with deck group $K/K'$ after accounting for central elements acting trivially. Without normality it is merely finite. This qualification prevents the common error of calling every change-of-level map Galois.

### 15.2 The right-action convention

Represent an adelic point by $[z,g]_K$ in

$$
G(\mathbf Q)\backslash(X\times G(\mathbf A_f)/K).
$$

For $h\in G(\mathbf A_f)$ define

$$
R_h:\operatorname{Sh}_K\longrightarrow
\operatorname{Sh}_{h^{-1}Kh},
\qquad
[z,g]_K\longmapsto[z,gh]_{h^{-1}Kh}. \tag{15.3}
$$

This is well defined because $gk h=gh(h^{-1}kh)$. The order of composition is

$$
R_{h'}\circ R_h=R_{hh'}. \tag{15.4}
$$

Thus $h$ acts on the right. If one instead labels level structures as maps from a fixed lattice into torsion, precomposition can make the matrix formulas look like a left action or introduce inverses. Formula (15.3) is our governing convention; every moduli description is translated to it.

If $h$ normalizes $K$, then $R_h$ is an automorphism of $X_K$. If not, it changes the level. The full adelic group therefore acts on the inverse system $\{X_K\}_K$, not on each individual curve.

### 15.3 Proof that the action respects level maps

Take $K'\subset K$. Both routes in

$$
\begin{array}{ccc}
X_{K'}&\xrightarrow{R_h}&X_{h^{-1}K'h}\\
\downarrow&&\downarrow\\
X_K&\xrightarrow{R_h}&X_{h^{-1}Kh}
\end{array} \tag{15.5}
$$

send $[z,g]$ to $[z,gh]$ and then forget a right coset refinement. Hence the square commutes. The statement is elementary, but it is the foundation for defining a correspondence independently of an auxiliary common level.

Central finite ideles require care. They can change a polarization similitude or a component while acting trivially on the adjoint symmetric domain. Quotienting them too early loses the component action described by determinants or reduced norms.

### 15.4 Modular degeneracy maps

Suppose $M$ and $n$ are coprime. A point of $Y_0(Mn)$ is $(E,C_M\oplus C_n)$. There are two natural maps to $Y_0(M)$:

$$
\alpha(E,C_M,C_n)=(E,C_M),
$$

and

$$
\beta(E,C_M,C_n)=
(E/C_n,(C_M+C_n)/C_n). \tag{15.6}
$$

The first forgets $C_n$; the second quotients by it. Both extend to compactifications using generalized elliptic curves and stable cyclic subgroups, with canonical contractions where necessary. Their behavior at cusps is governed by (7.4), and at primes dividing $n$ their integral behavior is not étale.

These maps are an elementary preview of a double-coset correspondence. They also show why a Hecke operator cannot usually be a single endomorphism of the moduli curve: the source elliptic curve and its quotient are two different outputs of a larger moduli problem.

### 15.5 Integral level change

At a finite place $v$ where both local levels are hyperspecial and the global level change is supported away from the residue characteristic, (15.1) extends to a representable finite étale map of the good integral stacks. At neat fine levels this is a finite étale map of schemes. On nonfine coarse spaces one must still check stabilizers, since the coarse map can ramify where they change. If the level change is supported at the residue characteristic, the map may instead be finite flat, generically étale, and ramified or inseparable on the special fiber. The Drinfeld and PEL local-model formulations construct the map, but they do not improve its reduction.

This distinction is the geometric reason that prime-to-$p$ correspondences specialize cleanly at a good $p$, whereas $p$-power correspondences interact with Frobenius and the branches of the bad fiber.

## 16. Hecke correspondences from moduli and double cosets

### 16.1 Why correspondences are the right object

Given a curve $X$, an algebraic endomorphism is too rigid to encode “sum over all subgroups of order $\mathfrak l$.” The intermediate choices themselves form another curve $Z$, equipped with finite maps

$$
X\xleftarrow{\ p_1\ }Z\xrightarrow{\ p_2\ }X. \tag{16.1}
$$

The cycle $(p_1,p_2)_*[Z]\subset X\times X$ is a correspondence. Pullback along one projection and trace along the other produces an operator on cohomology or the Jacobian. Which projection is pulled back is a convention that later determines every formula.

The goal of this chapter is to identify three descriptions of one operator: a moduli space of isogenies, an adelic double coset, and a finite algebraic correspondence. We shall also prove the convolution law. A good-prime Frobenius polynomial is a more refined assertion about the reduction of that correspondence and is not needed to construct the geometric Hecke module.

### 16.2 The prime-to-level modular correspondence

Let $\ell\nmid N$ be prime and work over $\mathbf Z[1/N\ell]$. Define $Y_H(\ell)$ to classify an $H$-level elliptic curve $(E,\eta)$ together with a cyclic subgroup $D\subset E[\ell]$ of rank $\ell$. There are maps

$$
p_1(E,\eta,D)=(E,\eta), \tag{16.2}
$$

and

$$
p_2(E,\eta,D)=(E/D,\eta_D), \tag{16.3}
$$

where $\eta_D$ is transported through the isomorphism on $N$-torsion induced by the prime-to-$N$ isogeny $E\to E/D$.

There is a component qualification for fixed-pairing full level. If $\eta=(P,Q)$ satisfies $e_N(P,Q)=\zeta$, then the degree-$\ell$ isogeny $\phi:E\to E/D$ satisfies

$$
e_N(\phi P,\phi Q)=e_N(P,Q)^\ell=\zeta^\ell. \tag{16.3a}
$$

Thus $p_2$ routes the $\zeta$-component to the $\zeta^\ell$-component; it is an endomorphism of one fixed-pairing component only when that component is preserved. In this section $Y_H$ therefore means either the full Galois-stable union of pairing components or explicitly typed source and target components. For $\Gamma_1$ and $\Gamma_0$ level there is no omitted pairing coordinate.

Both maps are finite étale on the open fine curve. Geometrically, $E[\ell]$ has $\ell+1$ lines, so $p_1$ has degree $\ell+1$. The map $p_2$ has the same degree by dual isogeny. After compactification both maps are finite but can ramify at cusps.

**Proof of finiteness.** The choices of $D$ form a finite étale scheme over the open curve because $E[\ell]$ is finite étale and its rank-$\ell$ direct summands form a finite étale sheaf. The quotient elliptic curve exists and varies algebraically. Properness of the compactifications and the valuative uniqueness of stable extension extend the maps across the finite boundary; a proper quasi-finite map of curves is finite. $\square$

For $X(1)$, $Z=X_0(\ell)$. The two projections are exactly the source and target maps in (5.5). This single diagram contains the geometric seed of the usual $\ell$th operator.

### 16.3 Level-prime correspondences

If $\ell\mid N$, adding another cyclic subgroup need not be transverse to the existing level. The natural moduli problem instead remembers a compatible filtration or removes and restores one step of level. On $X_0(M\ell)$ with $\ell\nmid M$, the pair of degeneracy maps in (15.6) supplies the basic diagram.

Over characteristic $\ell$, these maps see connected and étale subgroup schemes and can factor through relative Frobenius on components. They are not finite étale there. Naming the resulting operator without recording this integral geometry would hide the distinction between prime-to-level and level-prime behavior, so detailed operator statements are deferred.

### 16.4 Quaternionic isogeny correspondences

Let $\mathfrak l$ be a finite place of $F$ at which $B$ is split, the PEL datum is unramified, and $K_{\mathfrak l}$ is hyperspecial. Choose

$$
h_{\mathfrak l}\sim
\begin{pmatrix}\varpi_{\mathfrak l}&0\\0&1\end{pmatrix}
\in B_{\mathfrak l}^{\times}. \tag{16.4}
$$

Set

$$
K'=K\cap h_{\mathfrak l}Kh_{\mathfrak l}^{-1}.
$$

Then inclusion of levels gives one leg, while right translation followed by forgetting level gives the other:

$$
\operatorname{Sh}_{K}
\xleftarrow{\ \pi\ }
\operatorname{Sh}_{K'}
\xrightarrow{\ \pi\circ R_{h_{\mathfrak l}}\ }
\operatorname{Sh}_{K} \tag{16.5}
$$

Indeed, $R_{h_{\mathfrak l}}$ first lands at level

$$
h_{\mathfrak l}^{-1}K'h_{\mathfrak l}
=h_{\mathfrak l}^{-1}Kh_{\mathfrak l}\cap K\subset K,
$$

and only then does the forgetful map land on $\operatorname{Sh}_K$. Suppressing this intermediate level would contradict the convention of (15.3).

The diagram (16.5) is the elementary double-coset correspondence. In the PEL interpretation, a point of the middle curve is an abelian variety with PEL structure together with an $\mathcal O_D$-stable finite subgroup of the type selected by $h_{\mathfrak l}$. The second map quotients by that subgroup and transports the action, the normalized target polarization prescribed by the routed component, the determinant condition, and prime-to-$\mathfrak l$ level.

The kernel is not an arbitrary subgroup of the underlying abelian variety. It must be stable under the endomorphism order and isotropic or self-dual to exactly the extent required for the quotient polarization. These conditions are the PEL analogue of cyclicity for an elliptic isogeny.

### 16.5 Independence of representatives

Replacing $h$ by $k_1hk_2$ with $k_i\in K$ changes the middle level by conjugacy and produces an isomorphic correspondence. Indeed, right multiplication by $k_2$ does not change a $K$-coset, while $k_1$ identifies the relevant intersection subgroups. Thus the diagram depends on the double coset $KhK$.

This observation makes the individual correspondence well defined. The next two sections prove that its composition law is the convolution law and explain which parts extend integrally.

### 16.6 The moduli correspondence equals the adelic double coset

Let $a\in G(\mathbf A_f)$ and put $K_a=K\cap aKa^{-1}$. Using the right-action convention, define the span

$$
[KaK]:\qquad
X_K\xleftarrow{\pi_1}X_{K_a}
\xrightarrow{\pi_2}X_K, \tag{16.6}
$$

where $\pi_1$ forgets from $K_a$ to $K$, while $\pi_2$ is $R_a$ followed by forgetting from $a^{-1}K_aa=a^{-1}Ka\cap K$ to $K$. This orientation matches (16.5).

**Theorem 16.1 (moduli--double-coset comparison).** Suppose the levels are neat, and work either on the full component union or with source and target unions explicitly routed by $a$. The analytic correspondence (16.6), the algebraic correspondence obtained by canonical descent, and the PEL moduli space of isogenies of type $KaK$ are canonically isomorphic spans. For modular curves at a prime $\ell\nmid N$, taking $a=\operatorname{diag}(\ell,1)$ gives the cyclic-$\ell$-subgroup correspondence of Section 16.2.

**Proof strategy.** We compare the two lattices encoded by a point of the intermediate level. The finite quotient of those lattices becomes the kernel of the universal isogeny.

**Proof.** A point of $X_{K_a}$ has an adelic marking modulo both $K$ and $aKa^{-1}$. Its first image forgets to the original $K$-orbit. Multiplication by $a$ replaces the corresponding adelic lattice by a commensurable lattice. After multiplying $a$ by one positive rational integer in the center, which does not change the map on the adjoint Shimura quotient, we may arrange an inclusion of lattices

$$
\widehat\Lambda\subset a\widehat\Lambda
$$

or the reverse inclusion, according to the chosen direction. The finite quotient of the larger lattice by the smaller one is stable under the prescribed order. Under the period comparison of Proposition 12.2, it becomes a finite subgroup of the universal abelian variety. Quotienting by that subgroup constructs the second PEL object, and its induced marking is represented by $ga$.

Changing the scalar or integral representative factors the honest isogeny through multiplication by an integer. The endpoint curves and their normalized actual polarizations are still the ones selected by the same adelic points, so the resulting span is canonically unchanged even though the degree of that chosen honest isogeny changes. Changing a representative of $KaK$ was handled in Section 16.5.

Conversely, a PEL isogeny of the required kernel type induces on rational Tate modules two commensurable integral lattices in $V\otimes\mathbf A_f$. Their relative position is the $K$-double coset of $a$. A compatible marking therefore lifts the isogeny to $K_a$-level. These constructions are inverse in families, since finite locally free kernels and their quotients commute with base change.

For $G=\operatorname{GL}_2$ and $a=\operatorname{diag}(\ell,1)$, relative position says that the quotient lattice has index $\ell$. Index-$\ell$ overlattices of a rank-two lattice correspond to lines in $E[\ell]$, hence to cyclic subgroup schemes of rank $\ell$. The source and quotient maps are (16.2)--(16.3). Algebraicity and descent follow because level maps and right translations are morphisms of canonical models. $\square$

The degree of either leg is a coset number. If

$$
KaK=\coprod_{i=1}^r a_iK,
$$

then $\deg(\pi_1)=r=[K:K\cap aKa^{-1}]$. The other degree is $[K:K\cap a^{-1}Ka]$. The adelic reductive groups used here are unimodular, so conjugation preserves Haar measure and these two indices are equal. For $\operatorname{diag}(\ell,1)$ in $\operatorname{GL}_2(\mathbf Q_\ell)$ with hyperspecial $K_\ell$, both degrees are $\ell+1$.

### 16.7 Composition and convolution

Let $\mathcal H(G(\mathbf A_f),K)$ be the free abelian group on compact double cosets, with convolution normalized by giving $K$ volume one. If

$$
KaK=\coprod_i a_iK,\qquad KbK=\coprod_j b_jK,
$$

then

$$
\mathbf 1_{KaK}*\mathbf 1_{KbK}
=\sum_c m(a,b;c)\mathbf 1_{KcK}, \tag{16.7}
$$

Write $r_c=[K:K\cap cKc^{-1}]$, the number of right $K$-cosets in $KcK$. Then

$$
m(a,b;c)=\frac{1}{r_c}
\#\{(i,j):a_i b_j\in KcK\}.
$$

Equivalently, $m(a,b;c)$ is the common multiplicity with which each right coset contained in $KcK$ occurs in the multiset $\{a_i b_jK\}_{i,j}$. Bi-$K$-invariance makes that multiplicity constant, and in particular proves that the displayed quotient is an integer.

**Theorem 16.2 (geometric convolution).** With the correspondence direction of (16.6), first applying $[KaK]$ and then $[KbK]$ gives

$$
[KbK]\circ[KaK]
=\sum_c m(a,b;c)[KcK]. \tag{16.8}
$$

Consequently

$$
v\cdot\mathbf 1_{KaK}:=(\pi_2)_*\pi_1^*v
$$

defines a right action of $\mathcal H(G(\mathbf A_f),K)$ on every contravariant theory admitting trace for these finite maps.

**Proof strategy.** Composition of spans is a fiber product. Its pieces are labelled by the same pairs of right cosets that occur in convolution.

**Proof.** Form $X_{K_a}\times_{X_K}X_{K_b}$, where the first factor maps to the middle curve through its second leg and the second factor through its first. Over a geometric point with trivial stabilizer, a point of this fiber product is a successive choice of a modification of relative position $KaK$ and one of relative position $KbK$. Right-coset representatives label it by a pair $(a_i,b_j)$, and the composite modification has relative position $Ka_i b_jK$. In ordinary function-composition notation this is $[KbK]\circ[KaK]$, since the $a$-correspondence is traversed first.

Partition the pairs according to the double coset $KcK$ containing $a_i b_j$. Within a fixed double coset, every one of its $r_c$ right cosets occurs with the same multiplicity $m(a,b;c)$. The common-level construction therefore gives $m(a,b;c)$ copies of the intermediate correspondence for $KcK$, not one copy for every pair. Normalizing the fiber product does not alter its generic cycle. Both sides are finite cycles between normal curves, so equality of generic cycles gives equality globally. This proves (16.8).

Pull--push is functorial: finite base change identifies pullback through the fiber product, and transitivity of trace identifies the two successive pushforwards with pushforward along the composite. Applying this to (16.8) proves the action statement. $\square$

The transpose of (16.6) is canonically the correspondence for $Ka^{-1}K$, with its legs interchanged. The projection formula makes these two operators adjoint for the Poincaré pairing on $H^1$ and for the canonical polarization on the Jacobian. No residue-cardinality factor appears in this geometric adjoint statement; such a factor enters only when generators are rescaled to a different automorphic normalization.

At an unramified split place $\mathfrak l$, the spherical local algebra is generated by the double coset of $\operatorname{diag}(\varpi_{\mathfrak l},1)$ together with central double cosets. At an Iwahori place the two oriented elementary modifications generate the local Iwahori algebra, and orientation matters. Atkin--Lehner involutions arise from elements normalizing an Eichler level, while diamond operators arise from level-normalizing unit or central classes. Each is therefore a special case of the same span construction.

### 16.8 Extension over good integral models

Let $v$ have residue characteristic $p$, and suppose the modular level or PEL datum is good at $v$. If $a_p=1$, so the double coset is supported away from $p$, the kernel in the moduli description has order prime to $p$. Its schematic closure in the universal abelian scheme is finite étale, and the quotient is again an abelian scheme with the required action, normalized target polarization, determinant condition, and prime-to-$p$ level. Hence both legs extend over the good model.

**Proposition 16.3 (integral extension and specialization).** Under the preceding good-place, neatness, and prime-to-$p$ support hypotheses, and assuming the relevant smooth integral model is proper, the correspondence $[KaK]$ extends uniquely over that model. Its generic- and special-fiber pull--push operators correspond under smooth proper base change. The same statement holds on quotient stacks with rational coefficients. On coarse schemes one must separately verify that the coarse model is smooth proper and that the finite legs descend with the required trace maps; this is not formal at a wild quotient.

**Proof.** The moduli quotient construction gives existence. Separatedness gives uniqueness because two extensions agreeing on the dense generic fiber are equal. On the smooth modular locus, finite étaleness follows from finite étaleness of the kernel-choice functor and from the fact that a prime-to-$p$ isogeny induces an isomorphism on the deformation theory of the $p$-divisible group. Properness extends the maps across modular cusps; their Tate descriptions give finite maps there, generally ramified according to cusp width. For a division-algebra Shimura curve there is no boundary, so at neat prime-to-$p$ level the legs remain finite étale everywhere.

Smooth proper base change is functorial for pullback. It is also functorial for finite trace, since trace is the counit of the finite pullback--pushforward adjunction and this adjunction commutes with base change. Therefore the pull--push endomorphisms correspond. $\square$

When $a$ has nontrivial $p$-component, none of the finite-étale conclusions follows. The kernel may be connected, the quotient map can be inseparable on a component, and a hyperspecial model may have to be replaced by an Iwahori model. For the elementary level-prime modifications represented by the moduli problems of Chapters 8 and 14, the correspondence exists under their stated semistable hypotheses and its special-fiber cycle involves Frobenius and Verschiebung branches. Its analysis is a monodromy calculation rather than an application of smooth proper base change. No extension theorem for an arbitrary deeper $p$-power double coset is asserted.

## 17. From curves to Jacobians and $H^1$

### 17.1 The proper curve is the cohomological object

Let $X$ be a smooth proper geometrically connected modular or Shimura curve over a field $k$, and let

$$
J_X=\operatorname{Pic}^0_{X/k}
$$

be its Jacobian. For a modular curve, $X$ means the compactification, not the open moduli curve $Y$. The boundary changes cohomology: $H^1_c(Y)$ contains cusp terms and fits into a localization sequence, whereas $H^1(X)$ is the cohomology identified with the Jacobian.

For $\ell\ne\operatorname{char}k$, the established convention gives

$$
T_\ell J_X\simeq H^1(X_{k^s},\mathbf Z_\ell(1)),
\qquad
(T_\ell J_X)^\vee\simeq H^1(X_{k^s},\mathbf Z_\ell). \tag{17.1}
$$

If $X$ has several geometric components, one forms the Jacobian of each component, or equivalently the identity component of the Picard scheme of the disjoint union. The $H^1$ of the whole curve is the direct sum over components, with arithmetic Galois permuting the summands.

### 17.2 Correspondence variance

For a finite correspondence

$$
X\xleftarrow{p_1}Z\xrightarrow{p_2}X,
$$

we use the cohomological action

$$
[Z]_*=(p_2)_*p_1^*:H^1(X_{k^s},\mathbf Q_\ell)
\longrightarrow H^1(X_{k^s},\mathbf Q_\ell). \tag{17.2}
$$

On Jacobians the same cycle induces

$$
(p_2)_*p_1^*:J_X\longrightarrow J_X, \tag{17.3}
$$

where pullback acts on line bundles and pushforward is the norm. Under (17.1), the actions agree, with the visible Tate twist. The transpose correspondence exchanges $p_1$ and $p_2$ and is adjoint for the principal polarization and Poincaré pairing.

These statements do not determine the conventional scalar attached to an automorphic operator. They merely guarantee that once a correspondence and a direction are fixed, it acts compatibly on the curve's two geometric realizations.

### 17.3 Good reduction and unramified cohomology

Suppose $X$ extends to a smooth proper curve $\mathscr X$ over a henselian DVR $R$ with residue characteristic $p\ne\ell$. Then its relative Jacobian $\mathscr J=\operatorname{Pic}^0_{\mathscr X/R}$ is an abelian scheme and

$$
H^1(X_{\bar K},\mathbf Q_\ell)
\simeq H^1(\mathscr X_{\bar k},\mathbf Q_\ell). \tag{17.4}
$$

Prime-to-$p$ level maps and correspondences extending over $R$ commute with this identification. Thus the good modular models of Section 8.1, and the good Shimura models of Section 14.1 whenever one of its properness alternatives holds, provide unramified cohomological spaces with geometrically defined endomorphisms.

At a semistable but nonsmooth model, the relative identity component of the Picard scheme is generally semiabelian rather than abelian, and (17.4) must be replaced by a monodromy-sensitive statement. Regularity alone is not enough. This is why the exact hypotheses on integral models were maintained throughout.

### 17.4 What has and has not been extracted

The vector space

$$
H^1(X_{\overline k},\mathbf Q_\ell)
$$

now carries commuting actions of the arithmetic Galois group and of every correspondence defined over $k$. The Jacobian carries the integral lattice $T_\ell J_X$ and the polarization pairing. These are the geometric Hecke modules promised by the construction.

No two-dimensional representation has yet been singled out. Chapter 16 constructs the geometric double-coset algebra and proves its convolution relations, but one must still compare it with automorphic eigensystems and analyze the corresponding cohomological summands. Nor have characteristic polynomials of Frobenius been identified with Hecke eigenvalues. Those are separate theorems, not formal consequences of having a curve.

### 17.5 A genus-zero warning

If $X$ has genus zero, then $J_X=0$ and $H^1(X_{\bar k},\mathbf Q_\ell)=0$. The moduli problem and its correspondences can still be rich, but this particular curve contributes no weight-two cohomology. For example $X(1)\simeq\mathbf P^1$ has many cyclic-isogeny correspondences through $X_0(\ell)$, yet its first cohomology vanishes. Geometry realizes automorphic modules only where the genus and coefficient system permit them.

### 17.6 The geometric Hecke modules

We can now state the output of the construction in a form reusable without revisiting the moduli problems. Let $S$ be a finite set containing the residue characteristics of bad reduction, the primes at which the level is not hyperspecial, and the primes needed to define the chosen PEL lattice and polarization. Let

$$
\mathbb T^{S}_{K,\mathbf Z}
\subset\operatorname{Corr}(X_K)
$$

be the commutative algebra generated by spherical double-coset correspondences outside $S$, together with whatever diamond or central operators preserve the selected component union. If one works on the full disconnected curve, no component-stability restriction is needed; the algebra then also records permutation of components.

**Theorem 17.1 (geometric Hecke modules).** Let $X_K$ be a smooth proper modular curve or a proper quaternionic Shimura curve over its canonical field $E$, at neat level or on a fixed tame stack with rational coefficients. For every prime $\ell$ the following are naturally right modules for the geometric Hecke algebra whenever the indicated coefficients make sense:

$$
J_K,\qquad T_\ell J_K,\qquad
H^1(X_{K,\overline E},\mathbf Z_\ell),\qquad
H^1(X_{K,\overline E},\mathbf Q_\ell). \tag{17.5}
$$

The right action on $T_\ell J_K$ corresponds to that on $H^1(X_{K,\overline E},\mathbf Z_\ell(1))$ under (17.1). It commutes with $\operatorname{Gal}(\overline E/E)$ for correspondences defined over $E$. Outside $S\cup\{\ell\}$ it is compatible with specialization to every good special fiber for which the smooth proper model has been established. Transposition corresponds to the polarization adjoint.

**Proof.** Every generator is a finite correspondence defined over the canonical field by Chapters 15--16. Pullback and norm give its endomorphism of $J_K$; functoriality of the Tate module gives the second action. Pullback and trace give the two cohomological actions. The Kummer sequence is natural for pullback and norm, so it intertwines the Jacobian and cohomological actions, including the Tate twist.

Because the defining maps are over $E$, their pullback and trace maps commute with the arithmetic Galois action. The convolution theorem proves that the assignments respect multiplication in the double-coset algebra rather than merely assigning unrelated endomorphisms to its generators. At a good place away from the support of the double coset, Proposition 16.3 and smooth proper base change identify the generic and special actions. Finally, the norm--pullback adjunction for the principal polarization is the same projection formula that gives adjointness for the Poincaré pairing. $\square$

There are two integral cautions. First, a rational projector onto an eigenspace need not preserve the lattice $T_\ell J_K$; the geometric algebra acts integrally, but a decomposition of its rational module can have denominators. Second, if a nonneat stack has stabilizers divisible by $\ell$, coarse and stack cohomology need not have the same integral lattice. Fine level or an explicit stabilizer calculation is then required.

The theorem constructs the promised modules but does not identify their irreducible constituents. A maximal ideal $\mathfrak m$ of $\mathbb T^S$ gives localizations

$$
H^1(X_{K,\overline E},\mathbf Z_\ell)_{\mathfrak m},
\qquad
T_\ell J_K{}_{\mathfrak m},
$$

provided the coefficient map places $\mathbb T^S$ in a suitable $\ell$-adic ring. Showing that such a localization contains a distinguished two-dimensional Galois representation, and identifying its Frobenius polynomial, requires an automorphic decomposition and an integral Eichler--Shimura theorem. Those are extra arithmetic results; the geometric Hecke module itself is now complete.

## 18. An atlas of examples

### 18.1 $X(1)$ revisited

The open stack $\mathcal M_{\mathrm{ell}}$ classifies elliptic curves, its coarse space is $Y(1)=\mathbf A^1_j$, and its compactification by generalized elliptic curves has coarse space

$$
X(1)=\mathbf P^1_j. \tag{18.1}
$$

The points $j=0$ and $1728$ are ordinary points of the coarse line but orbifold points of the stack. The point $j=\infty$ is the unique cusp. A Tate neighborhood identifies $j^{-1}$ as a local parameter up to a unit. Since the genus is zero, $J_0(1)=0$.

This example contains every categorical distinction in miniature: the stack has a universal generalized elliptic curve, the coarse line does not; automorphisms cause orbifold structure in the interior; and compactification adds a genuinely degenerate object.

### 18.2 $X_0(2)$ as cyclic isogenies

A point of $Y_0(2)$ is an elliptic curve with a subgroup of rank two. Away from characteristic two this is the same as a nonzero two-torsion point, because such a subgroup has a unique generator. The moduli stack still retains $[-1]$, although $[-1]$ fixes the generator automatically when it has order two. Over $\mathbf Q$, its coarse compactification is a genus-zero curve with two cusps, represented by the two distributions of the subgroup in the Tate degeneration.

At the prime $2$, the two-point description fails. An ordinary elliptic curve has a connected subgroup $\mu_2$ and an étale quotient direction; a supersingular elliptic curve brings the branches together. Thus the same simple coarse rational curve has nontrivial integral reduction. Genus and reduction complexity measure different things.

### 18.3 $X_0(p)$ and the two projections

For a prime $p$, the curve $X_0(p)$ maps twice to $X(1)$:

$$
\pi_1(E,C)=E,
\qquad
\pi_2(E,C)=E/C. \tag{18.2}
$$

Over characteristic different from $p$, each generic fiber of $\pi_1$ consists of the $p+1$ lines in $E[p]$. At the boundary, quotienting $E_q$ by $\mu_p$ changes the Tate parameter in one direction, while quotienting by a subgroup generated by a $p$th root of $q$ changes it in the other. In characteristic $p$, these become the Frobenius and Verschiebung branches of Section 8.3.

The example links three pictures without identifying them carelessly:

$$
\begin{array}{c|c|c}
\text{generic moduli}&\text{cusp neighborhood}&\text{special fiber at }p\\ \hline
\text{cyclic }p\text{-subgroup}&
\mu_p\text{ or component direction}&
\text{connected or étale branch}.
\end{array} \tag{18.3}
$$

### 18.4 A fixed-pairing full-level component

Fix $N=3$ and a primitive cube root $\zeta_3$. The fine curve $Y(3)_{\zeta_3}$ classifies triples $(E,P,Q)$ satisfying

$$
E[3]=\langle P,Q\rangle,\qquad e_3(P,Q)=\zeta_3.
$$

It is geometrically connected over $\mathbf Q(\zeta_3)$ and uniformized by $\Gamma(3)\backslash\mathfrak H$. Replacing $Q$ by $-Q$ moves to the component with pairing $\zeta_3^{-1}$. Over $\mathbf Q$, the two components are Galois conjugate. This is a concrete case in which the entire full-level scheme and one geometrically connected modular curve are not synonymous.

### 18.5 A compact quaternionic curve and its component

Return to the algebra $B/\mathbf Q$ ramified at $2$ and $3$. At maximal level, the norm quotient (13.3) is trivial, so its complex Shimura curve is connected. Passing to neat principal level $M$ gives a finite cover that may split according to the smaller norm subgroup; selecting a norm class selects a connected component. Every component is compact because division is unchanged by level.

At a prime $q\nmid6M$, the maximal local order is split and hyperspecial, so the PEL realization has smooth proper reduction when one of the properness alternatives of Theorem 14.1 holds. At $q=2$ or $3$, no integral conclusion is drawn here: these are division places, outside the proved local models. At $q\mid M$, the level itself is bad even though $B$ is split. The example separates the three sources of local behavior: algebra ramification, level, and auxiliary PEL data.

## 19. The geometric dictionary

### 19.1 From input data to a curve

The constructions can now be summarized without erasing their hypotheses.

| Input | Modular curve | Quaternionic Shimura curve |
|---|---|---|
| Basic object | elliptic curve $E$ | PEL abelian scheme $(A,\iota,\lambda)$, or canonical quaternionic datum |
| Level | basis, point, or cyclic finite locally free subgroup | compact-open orbit of Tate-module trivializations; equivalently stable PEL isogeny data locally |
| Rigidity | full $N\geq3$ or $\Gamma_1(N)\geq4$ away from $N$ | neat compact open |
| Nonfine case | stack plus coarse curve; $\Gamma_0$ retains $[-1]$ | stack plus coarse curve; universal abelian scheme remains on the stack |
| Complex domain | $\mathfrak H$ modulo a congruence group | $\mathfrak H$ from the unique split real place |
| Components | determinant and Weil-pairing data | reduced-norm or similitude class group |
| Boundary | cusps represented by Néron polygons | none when $B$ is division |
| Local boundary coordinate | Tate parameter $q_c$ determined by cusp width | not applicable |
| Good integral model | smooth proper over primes away from level | smooth at unramified self-dual hyperspecial places, and proper under Theorem 14.1's additional alternatives |
| Selected bad model | squarefree $\Gamma_0(p)$ gives two semistable branches under rigid hypotheses | split Iwahori local model under the flat rank-two hypotheses; ramified algebra places are not constructed here |

This table is a map, not a replacement for the construction. In particular, “level” means finite étale data only where its order is invertible; “good” includes every part of the datum; and a coarse curve never silently acquires a universal object.

### 19.2 From a curve to later arithmetic objects

For each geometrically connected smooth proper component $X$ the output chain is

$$
\begin{array}{ccccc}
\text{moduli datum}
&\longrightarrow&X
&\longrightarrow&J_X=\operatorname{Pic}^0_X\\
&&\downarrow&&\downarrow\\
&&H^1(X_{\bar k},\mathbf Q_\ell)
&\longleftrightarrow&T_\ell J_X\otimes\mathbf Q_\ell(-1),
\end{array} \tag{19.1}
$$

where the displayed twist is understood through (17.1). A level inclusion gives a finite map of curves and hence pullback and trace. A double coset gives a two-legged moduli correspondence. The same correspondence acts on $J_X$ and $H^1$, with transpose giving the polarization adjoint.

At a good finite place where the required proper integral model has been established, the chain extends over a smooth proper valuation ring model, so specialization preserves $H^1$ and inertia is trivial. At a selected semistable place, the special fiber and its dual graph replace this simple statement and signal monodromy. These alternatives are the exact geometric inputs needed when operator and Frobenius relations are studied.

### 19.3 The exact endpoint of the construction

The present volume has defined the curves, identified moduli isogenies with adelic double cosets, proved geometric convolution, and constructed the resulting Hecke modules. Three further arithmetic identifications remain logically distinct:

- comparing good-prime correspondences with Frobenius on special fibers;
- isolating eigensummands in $H^1$ or $T_\ell J$;
- proving that such summands are two-dimensional and determining their determinants, ramification, and local behavior.

The first concerns the arithmetic of reduction; the last two concern automorphic decomposition and Galois representations. None is smuggled into the words “modular,” “Shimura,” or “Hecke module.”

### 19.4 Conclusion

A modular curve begins with the failure of the $j$-invariant to be a universal classification. The remedy is not merely to add coordinates but to formulate families as a stack, preserve their automorphisms, and add level that is rigid enough for the desired purpose. Away from its order, level is finite étale linear algebra. At its characteristic, it must be expressed by finite locally free subgroup schemes and Drinfeld divisors. The Weil pairing then reveals that a full basis carries a cyclotomic component coordinate, so determinants govern both symmetry and connectedness.

Compactification forces another enlargement of viewpoint. An elliptic curve can approach the boundary only by becoming a generalized elliptic curve, and stable level must meet every polygon component. The Tate curve describes the resulting formal disk and its cusp width. The valuative criterion turns these local pictures into a proper curve. At good primes a proved smooth proper model makes cohomology specialize unchanged; at level primes the connected and étale directions can cross, and semistability is available only under the precise local hypotheses stated.

Quaternionic Shimura curves preserve the same one-dimensional symmetric geometry while changing its global source. A quaternion algebra split at exactly one real place contributes one upper half-plane; division removes rational unipotents and therefore removes cusps. Reduced norm replaces determinant as the component coordinate. A PEL realization turns the analytic quotient into a moduli curve only after polarization, positivity, determinant, and level conditions have been fixed. The distinction between the bare quaternionic datum and an auxiliary PEL datum is what keeps the construction canonical rather than accidental.

Across both families, changing level produces finite maps, while right adelic multiplication acts on the tower. A double coset becomes a moduli space of isogenies with two projections, and fiber products of these spans realize convolution. Compactified curves then have Jacobians and first cohomology, and every Hecke correspondence acts compatibly on both. The geometric stage is therefore complete: level, components, compactification, integral reduction, and the geometric Hecke algebra have been assembled on smooth proper curves where the hypotheses permit, and on controlled bad models where they do not. Their cohomology now carries commuting Hecke and arithmetic actions, while the boundary between this geometric module and the later extraction of individual representations remains exact.
