# Modular Jacobians, Néron Models, and Hecke Correspondences

## Contents

- [1. From modular curves to integral linear algebra](#1-from-modular-curves-to-integral-linear-algebra)
  - [1.1 The problem solved by a modular Jacobian](#11-the-problem-solved-by-a-modular-jacobian)
  - [1.2 The three integral layers](#12-the-three-integral-layers)
  - [1.3 Standing hypotheses and conventions](#13-standing-hypotheses-and-conventions)
  - [1.4 The dependency boundary](#14-the-dependency-boundary)
- [2. Modular curves, Jacobians, and differentials](#2-modular-curves-jacobians-and-differentials)
  - [2.1 The compactified curve and its Jacobian](#21-the-compactified-curve-and-its-jacobian)
  - [2.2 Pointed and unpointed Albanese maps](#22-pointed-and-unpointed-albanese-maps)
  - [2.3 Cotangent spaces and weight-two cusp forms](#23-cotangent-spaces-and-weight-two-cusp-forms)
  - [2.4 Polarization and the choice of variance](#24-polarization-and-the-choice-of-variance)
- [3. Generic Hecke correspondences](#3-generic-hecke-correspondences)
  - [3.1 The moduli span](#31-the-moduli-span)
  - [3.2 The action on divisor classes](#32-the-action-on-divisor-classes)
  - [3.3 Diamond and Atkin--Lehner operators](#33-diamond-and-atkin--lehner-operators)
  - [3.4 Composition, transpose, and Hecke relations](#34-composition-transpose-and-hecke-relations)
- [4. The integral Hecke action on Néron models](#4-the-integral-hecke-action-on-neron-models)
  - [4.1 Canonical extension](#41-canonical-extension)
  - [4.2 A global integral Hecke algebra](#42-a-global-integral-hecke-algebra)
  - [4.3 Connected fibers, components, and cotangent lattices](#43-connected-fibers-components-and-cotangent-lattices)
  - [4.4 What extension does not imply](#44-what-extension-does-not-imply)
- [5. Integral Albanese maps and specialization](#5-integral-albanese-maps-and-specialization)
  - [5.1 Extension over the smooth locus](#51-extension-over-the-smooth-locus)
  - [5.2 The divisor formula](#52-the-divisor-formula)
  - [5.3 Hecke equivariance and base-point corrections](#53-hecke-equivariance-and-base-point-corrections)
  - [5.4 Components detected by points](#54-components-detected-by-points)
- [6. The Hecke correspondence at its residue characteristic](#6-the-hecke-correspondence-at-its-residue-characteristic)
  - [6.1 Why the good generic correspondence degenerates](#61-why-the-good-generic-correspondence-degenerates)
  - [6.2 The two Deligne--Rapoport branches](#62-the-two-deligne--rapoport-branches)
  - [6.3 Specializing the correspondence cycle](#63-specializing-the-correspondence-cycle)
  - [6.4 Frobenius, Verschiebung, and diamond descent](#64-frobenius-verschiebung-and-diamond-descent)
- [7. The integral Eichler--Shimura relation](#7-the-integral-eichler--shimura-relation)
  - [7.1 The endomorphism identity](#71-the-endomorphism-identity)
  - [7.2 The quadratic polynomial](#72-the-quadratic-polynomial)
  - [7.3 Tate modules and Frobenius](#73-tate-modules-and-frobenius)
  - [7.4 Quotients and Galois extraction](#74-quotients-and-galois-extraction)
- [8. Néron models at a prime in the level](#8-neron-models-at-a-prime-in-the-level)
  - [8.1 The Deligne--Rapoport curve as a Picard model](#81-the-deligne--rapoport-curve-as-a-picard-model)
  - [8.2 The connected special fiber](#82-the-connected-special-fiber)
  - [8.3 The component group of the fine model](#83-the-component-group-of-the-fine-model)
  - [8.4 Coarse models and weighted nodes](#84-coarse-models-and-weighted-nodes)
- [9. Hecke operators on bad fibers](#9-hecke-operators-on-bad-fibers)
  - [9.1 The resolved pull--push calculation](#91-the-resolved-pull--push-calculation)
  - [9.2 The action on the two-vertex graph](#92-the-action-on-the-two-vertex-graph)
  - [9.3 Atkin--Lehner on components](#93-atkin--lehner-on-components)
  - [9.4 Adjoints, ideals, and saturation](#94-adjoints-ideals-and-saturation)
- [10. Monodromy of modular Jacobians](#10-monodromy-of-modular-jacobians)
  - [10.1 Why the graph pairing is monodromy](#101-why-the-graph-pairing-is-monodromy)
  - [10.2 The Tate-module filtration](#102-the-tate-module-filtration)
  - [10.3 The Picard--Lefschetz formula](#103-the-picard--lefschetz-formula)
  - [10.4 Hecke equivariance of monodromy](#104-hecke-equivariance-of-monodromy)
- [11. Differential and q-expansion realizations](#11-differential-and-q-expansion-realizations)
  - [11.1 The canonical cotangent lattice](#111-the-canonical-cotangent-lattice)
  - [11.2 Comparison with geometric Hecke operators](#112-comparison-with-geometric-hecke-operators)
  - [11.3 The residue characteristic and the dualizing lattice](#113-the-residue-characteristic-and-the-dualizing-lattice)
  - [11.4 Faithfulness and finite verification](#114-faithfulness-and-finite-verification)
- [12. Exact calculations](#12-exact-calculations)
  - [12.1 One supersingular edge](#121-one-supersingular-edge)
  - [12.2 Several unit edges](#122-several-unit-edges)
  - [12.3 Weighted quotient edges](#123-weighted-quotient-edges)
  - [12.4 A specialization calculation with cusps](#124-a-specialization-calculation-with-cusps)
- [13. Hypothesis ledger and failure modes](#13-hypothesis-ledger-and-failure-modes)
  - [13.1 Fine, stack, stable coarse, and regular coarse models](#131-fine-stack-stable-coarse-and-regular-coarse-models)
  - [13.2 Characteristic, level, and separability](#132-characteristic-level-and-separability)
  - [13.3 Integral versus rational decompositions](#133-integral-versus-rational-decompositions)
  - [13.4 A dependency-closed main theorem](#134-a-dependency-closed-main-theorem)
- [14. Conclusion](#14-conclusion)
  - [14.1 The complete modular-Jacobian package](#141-the-complete-modular-jacobian-package)
  - [14.2 The arithmetic meaning of the package](#142-the-arithmetic-meaning-of-the-package)

## 1. From modular curves to integral linear algebra

### 1.1 The problem solved by a modular Jacobian

A modular curve parametrizes elliptic curves together with level structure. That moduli interpretation makes points and isogenies concrete, but many arithmetic arguments require addition and subtraction. Two elliptic curves with level do not add to a third one. Degree-zero divisor classes on the compactified modular curve do add, and the Jacobian turns those classes into points of a proper commutative algebraic group. A finite isogeny correspondence on the modular curve then becomes an endomorphism of that group.

Over a field this passage is already powerful. Over an arithmetic base it must be refined. A modular curve can have nodal reduction at a prime in its level; its Jacobian can then have a torus and a nontrivial finite component group. A generic Hecke correspondence can specialize to a sum of Frobenius and Verschiebung branches. If one keeps only the generic endomorphism, these features disappear. If one keeps only a raw closure of the correspondence, vertical components and quotient singularities can make composition ambiguous.

The correct integral object is the Néron model of the modular Jacobian. Its mapping property extends every generic endomorphism uniquely, while a regular modular-curve model calculates the extension. Thus the same Hecke operator acts on four related objects:

$$
J,\qquad \mathcal J^0_k,\qquad \Phi_J,\qquad
\omega_{\mathcal J/R}=e^*\Omega^1_{\mathcal J/R}.
$$

The generic Jacobian carries the global divisor theory. The connected special fiber carries abelian and toric reduction. The component group measures the remaining integral lattice defect. The cotangent module is the lattice of regular differentials and, on a good modular model, the lattice of weight-two cusp forms.

The most important compatibility is the integral Eichler--Shimura relation. At a prime $p$ away from the fixed level, the auxiliary $p$-isogeny curve has two special-fiber components. One is the Frobenius branch and the other the Verschiebung branch. Their sum gives, as an equality of endomorphisms of the special Jacobian,

$$
T_p=F_p+\langle p\rangle V_p.
$$

Because $F_pV_p=V_pF_p=[p]$, this becomes

$$
F_p^2-T_pF_p+p\langle p\rangle=0.
$$

This is not merely a relation after tensoring with a field. It is an equality of homomorphisms of an abelian variety in characteristic $p$, hence acts on every finite subgroup scheme and every prime-to-$p$ Tate lattice. That integrality is what makes the relation useful both for Mazur-style specialization arguments and for extracting Galois representations from Hecke eigensystems.

### 1.2 The three integral layers

Three passages organize the book.

The first is from curves to Jacobians. If $X/K$ is a smooth proper geometrically connected modular curve and $c$ is a cusp, the pointed Abel--Jacobi map is

$$
j_c:X\longrightarrow J_X,\qquad x\longmapsto[\,x-c\,].
$$

The curve generates its Jacobian. Consequently identities between Jacobian homomorphisms can often be checked on divisors supported on modular points and cusps.

The second is from generic Jacobians to Néron models. A Hecke span

$$
X\xleftarrow{\alpha}H\xrightarrow{\beta}X
$$

acts by

$$
\beta_*\alpha^*:J_X\longrightarrow J_X.
$$

The Néron mapping property extends this homomorphism uniquely. Generic Hecke relations, transpose identities, and diamond commutation therefore remain true on the integral model without being reproved at every bad fiber.

The third is from regular models to lattices. If a semistable special fiber has dual graph $G$, put

$$
X_G=H_1(G,\mathbf Z),\qquad
q_G(a,b)=\sum_en_ea_eb_e,
$$

where $n_e$ is the thickness of the node. Then

$$
X^*(T)=X_G,\qquad
\Phi_J(\bar k)=X_G^\vee/q_GX_G.
$$

Resolved Hecke correspondences act on $X_G$ by harmonic pullback and pushforward. Transpose is adjoint for $q_G$, so the action descends to the discriminant group. The same map $q_G$ also controls tame inertia on the Tate module. Component groups and monodromy are therefore not separate accidents; they are the cokernel and the linearized Galois action attached to one integral pairing.

### 1.3 Standing hypotheses and conventions

The generic ground field has characteristic zero unless a statement explicitly begins over another field. An arithmetic base $S$ is an excellent connected Dedekind scheme with function field $K$. Local arguments use an excellent discrete valuation ring $R$, fraction field $K$, residue field $k$, and residue characteristic $p$. A superscript ${\rm sh}$ denotes strict henselization, and $k^s$ is a separable closure of $k$.

The modular curve $X=X_\Gamma/K$ is the smooth proper coarse curve or a projective fine modular curve attached to a compactified modular problem $\Gamma$. Whenever a universal generalized elliptic curve is used, the argument is made on the stack or on a rigidified fine cover. A coarse curve is used only for constructions, such as its Jacobian, that genuinely descend. Connected components are treated separately when the level problem is disconnected.

For a prime $p$ away from the level, $T_p$ denotes the normalized Hecke operator whose action on weight-$k$ expansions is

$$
a_n(T_pf)=a_{pn}(f)+p^{k-1}a_{n/p}(\langle p\rangle f).
$$

On Jacobians we choose the unique variance for which pullback on invariant differentials is this operator in weight two. Thus if $H$ classifies a cyclic subgroup and $\pi_1$ remembers its source while $\pi_2$ remembers its quotient, then

$$
T_p=(\pi_2)_*\pi_1^*.
$$

For a level automorphism $d_a:X\to X$, the diamond endomorphism of the Jacobian is

$$
\langle a\rangle_J=(d_a)_*=(d_a^{-1})^*.
$$

Its pullback on differentials is $d_a^*$, agreeing with the modular-form convention. On a cyclic-level curve where changing a generator is invisible, $\langle a\rangle$ is the identity unless an additional point-level or character datum has been retained.

For an abelian variety $A$ over a finite field, $F_A:A\to A^{(p)}$ is relative Frobenius and $V_A:A^{(p)}\to A$ is Verschiebung. After the coefficient and level identifications used in the modular problem, these become endomorphisms denoted $F_p$ and $V_p$. We use arithmetic Frobenius on prime-to-$p$ Tate modules: it acts as the $p$-power Frobenius endomorphism. A reader using geometric Frobenius must invert that operator and reverse the corresponding polynomial convention.

### 1.4 The dependency boundary

The construction rests on five established packages.

Relative Picard theory supplies Jacobians, Abel maps, principal polarizations, norm and pullback, and the fact that transpose correspondences are Rosati adjoints. Néron theory supplies existence, unique extension of homomorphisms, the separated Picard quotient, the intersection-matrix presentation of components, and the weighted graph pairing for semistable Jacobians. Integral correspondence theory proves that normalized resolved closures calculate the same canonical Néron homomorphism and that graph pullback and pushforward are adjoint. The Deligne--Rapoport model supplies the regular equation $xy=p$, its two Frobenius--Verschiebung components, degeneracy maps, cusps, and coarse-node thicknesses. Integral modular-form theory supplies the Hodge line, weight-two Kodaira--Spencer, q-expansion lattices, and the normalized Hecke formula.

We recall those results where needed, with their hypotheses. We do not assume a general monodromy theorem for semistable abelian varieties. The monodromy statements below are proved for Jacobians directly from the normalization sequence at the nodes, Kummer theory, and the graph pairing. This keeps the present argument inside its declared prerequisites.

## 2. Modular curves, Jacobians, and differentials

Before Hecke operators can be extended, the object on which they act must be fixed together with its variance. This chapter passes from the compactified modular curve to its Picard and Albanese objects and then identifies the cotangent realization. The point is not to repeat general Jacobian theory, but to isolate the exact structures later calculations must preserve: the Abel map, the canonical polarization, and the weight-two differential lattice.

### 2.1 The compactified curve and its Jacobian

Let $X/K$ be a smooth proper geometrically connected compactified modular curve. Its Jacobian is

$$
J=\operatorname{Pic}^0_{X/K}.
$$

It is an abelian variety of dimension $g(X)$ and carries the canonical principal polarization

$$
\lambda_X:J\xrightarrow{\sim}J^\vee.
$$

No rational cusp is required for the definition. The degree-zero Picard functor and its polarization descend intrinsically. A rational cusp is needed only to choose a pointed Abel map.

The cotangent space at the identity is canonically

$$
\omega_{J/K}=e^*\Omega^1_{J/K}
\simeq H^0(X,\Omega^1_{X/K}). \tag{2.1}
$$

To see the map, pull an invariant differential back along any pointed Abel map. Its independence of the base point follows because changing the base point translates the Abel map, and invariant differentials are translation invariant. It is an isomorphism because the tangent space of $J$ is $H^1(X,\mathcal O_X)$ and Serre duality identifies its dual with the right side.

The curve generates $J$. Indeed every degree-zero divisor class can, after adding a sufficiently large multiple of a chosen point, be written as a sum of classes $[x-c]$. Hence a homomorphism $u:J\to A$ to an abelian variety is determined by $u\circ j_c$. This generation principle will repeatedly turn an identity of homomorphisms into a calculation with divisors or modular isogenies.

### 2.2 Pointed and unpointed Albanese maps

Assume first that $c\in X(K)$. The Abel--Jacobi map

$$
j_c(x)=[\mathcal O_X(x-c)]. \tag{2.2}
$$

is initial among maps from $(X,c)$ to pointed abelian varieties. Explicitly, if $f:X\to A$ satisfies $f(c)=0$, there is a unique homomorphism $f_*:J\to A$ such that $f=f_*j_c$.

The proof explains why the Jacobian is also an Albanese. Pullback of algebraically trivial line bundles gives $f^*:A^\vee\to J$. Dualizing and composing with $\lambda_X$ gives

$$
f_*=(f^*)^\vee\lambda_X:J\longrightarrow A.
$$

The Poincaré bundle and the see-saw principle show that $f_*j_c=f$. Uniqueness follows from generation by $j_c(X)$.

If $X$ has no rational cusp, the correct target of a canonical map is the degree-one Picard torsor:

$$
a_1:X\longrightarrow\operatorname{Pic}^1_{X/K},\qquad x\longmapsto[\mathcal O_X(x)]. \tag{2.3}
$$

After a field extension and a choice of $c$, translation by $-c$ identifies this torsor with $J$ and (2.3) with (2.2). Changing $c$ translates both sides compatibly. Consequently every construction below has an unpointed form; a displayed $j_c$ is a convenient coordinate on the Albanese torsor, not evidence that every modular component has a rational cusp.

### 2.3 Cotangent spaces and weight-two cusp forms

Suppose the level is invertible on a coefficient ring $A$ and the compactified modular problem is fine or has linearly reductive stabilizers. Let $\lambda$ be the Hodge line and $D$ the reduced cusp divisor. Logarithmic Kodaira--Spencer gives

$$
\lambda^{\otimes2}\simeq\Omega^1_{X/A}(\log D),
\qquad
\lambda^{\otimes2}(-D)\simeq\omega_{X/A}. \tag{2.4}
$$

Thus

$$
S_2(\Gamma;A)=H^0(X,\lambda^2(-D))
\simeq H^0(X,\omega_{X/A}). \tag{2.5}
$$

Combining (2.1) and (2.5) on the generic fiber identifies weight-two cusp forms with invariant differentials on the modular Jacobian.

At a cusp of width $w$, write the unlevelled Tate parameter as $q=t^w$ and trivialize $\lambda$ by $du/u$. If

$$
f(t)=\sum_{n\geq1}a_nt^n,
$$

then Kodaira--Spencer sends $f(du/u)^2$ to

$$
w\left(a_1+a_2t+\cdots\right)dt.
$$

The vanishing of the constant term is exactly what removes the logarithmic pole. The factor $w$ is invertible under the good-level hypothesis. At a prime dividing the level it may not be a unit, so one must use the regular dualizing lattice directly; Section 11.3 handles that case without silently extending (2.4) beyond its hypotheses.

### 2.4 Polarization and the choice of variance

Let $f:X\to Y$ be finite. Pullback and norm give

$$
f^*:J_Y\to J_X,\qquad f_*:J_X\to J_Y,\qquad
f_*f^*=[\deg f]. \tag{2.6}
$$

They are adjoint under the canonical polarizations:

$$
(f^*)^\vee\lambda_X=\lambda_Yf_*.
$$

Consequently a span $X\xleftarrow{\alpha}H\xrightarrow{\beta}Y$ acts covariantly by

$$
u_H=\beta_*\alpha^*:J_X\to J_Y, \tag{2.7}
$$

and its transpose acts by the Rosati adjoint $u_H^\dagger=\alpha_*\beta^*$.

The pullback of (2.7) on invariant differentials is

$$
u_H^*=\alpha_*^{\rm tr}\,\beta^*, \tag{2.8}
$$

where $\alpha_*^{\rm tr}$ is the trace on regular differentials. Formula (2.8) follows either from duality or from the residue definition of trace. For the modular $p$-isogeny span, it is the pull--transport--trace operator used to define $T_p$ on weight-two cusp forms. This agreement fixes all later directions and prevents the common error of replacing $\beta_*\alpha^*$ by its adjoint.

## 3. Generic Hecke correspondences

A Hecke operator begins as a moduli relation, not as a formula on coefficients. This chapter constructs that relation on the generic modular curve, proves how it acts on divisors, and fixes the conventions for diamonds, transpose, and composition. Once these choices are settled generically, the Néron mapping property will transport the entire algebra integrally.

### 3.1 The moduli span

Let $m$ be prime to the fixed level. The auxiliary modular curve $H_m$ classifies a modular object $(E,\alpha)$ together with a cyclic finite locally free subgroup $C\subset E[m]$ of rank $m$. There are finite maps

$$
\begin{array}{ccc}
&H_m&\\
\pi_1\swarrow&&\searrow\pi_2\\
X&&X,
\end{array} \tag{3.1}
$$

where $\pi_1(E,\alpha,C)=(E,\alpha)$ and $\pi_2(E,\alpha,C)=(E/C,\alpha/C)$. Contraction of generalized elliptic curves makes both maps regular at the cusps. In characteristic zero the maps are finite locally free on the fine problem. On coarse curves they remain finite; when a direct norm calculation is needed, one passes to a fine cover or to the normalization of the correspondence.

For prime $\ell\nmid N$, a smooth elliptic curve has $\ell+1$ cyclic subgroups of rank $\ell$, so $\deg\pi_1=\ell+1$. The number $\ell+1$ is not the normalizing denominator in the modular-form convention. The trace operator is divided by $\ell$, because the $\ell$ nonmultiplicative Tate subgroups contribute a factor $\ell$ to the trace. On Jacobians no rational scalar is inserted: the integral pull--norm correspondence (2.7) already has the normalization whose differential is the usual $T_\ell$ on weight two.

If $q$ divides the level, the corresponding $U_q$ span is defined on the generic curve by chains of $q$-isogenies compatible with the retained level after removing the distinguished level direction. It is again a finite correspondence after normalization, but it is not the auxiliary good-prime span: one of the generic subgroup choices has already been built into the level. We include this generic $U_q$ in the Hecke algebra and extend it by the Néron property. We do not apply the two-branch Eichler--Shimura calculation to $U_q$; its action at the level prime must be read from its own resolved closure by Section 9.

### 3.2 The action on divisor classes

Define

$$
T_m=(\pi_2)_*\pi_1^*\in\operatorname{End}_K(J). \tag{3.2}
$$

For a degree-zero divisor $D$ on $X$,

$$
T_m[D]=[(\pi_2)_*\pi_1^*D]. \tag{3.3}
$$

This formula includes ramification indices in pullback and residue degrees in pushforward. If $D=\operatorname{div}(g)$, then

$$
(\pi_2)_*\pi_1^*D
=\operatorname{div}\!\left(
N_{K(H_m)/K(X)}(\pi_1^*g)
\right),
$$

so (3.3) is well defined on divisor classes.

For a point $x$ away from ramification, (3.3) is the transparent sum

$$
T_m[x-c]
=\sum_{z\in\pi_1^{-1}(x)}[\pi_2(z)]
-\sum_{z\in\pi_1^{-1}(c)}[\pi_2(z)], \tag{3.4}
$$

with residue multiplicities understood. Formula (3.4) is the Hecke-equivariant Albanese identity. It is valid without assuming that the Hecke orbit of $c$ is a single cusp.

### 3.3 Diamond and Atkin--Lehner operators

On a point-level modular curve, changing a chosen generator by $a\in(\mathbf Z/N\mathbf Z)^\times$ gives an automorphism $d_a$. We define

$$
\langle a\rangle_J=(d_a)_*.
$$

Because $d_a$ is an automorphism, $(d_a)_*=(d_a^{-1})^*$. Pullback of invariant differentials by $\langle a\rangle_J$ is $d_a^*$, exactly the diamond operator on modular forms. The identities

$$
\langle a\rangle\langle b\rangle=\langle ab\rangle,
\qquad T_m\langle a\rangle=\langle a\rangle T_m
$$

follow from the corresponding identities of moduli functors.

Suppose $q$ divides a cyclic level exactly once. The Atkin--Lehner involution sends a $q$-isogeny

$$
E\longrightarrow E/C
$$

to its dual isogeny, with the remaining level transported in the prescribed way. Denote the resulting curve automorphism by $w_q$. Its square is the appropriate diamond operator; on $X_0(q)$ with no retained generator,

$$
w_q^2=1. \tag{3.5}
$$

The Jacobian operator is $(w_q)_*$. Since $w_q$ reverses the defining correspondence, it is an isometry for the canonical polarization. In the involutive case it is self-adjoint.

### 3.4 Composition, transpose, and Hecke relations

Fiber products of the spans (3.1) classify chains of cyclic isogenies. Normalizing their one-dimensional components and retaining scheme-theoretic multiplicities gives composition of correspondences. The projection formula proves that this composition agrees with composition of the Jacobian endomorphisms.

Here is the local reason no multiplicity is missing. If a point lies above the middle curve in a composite, the local ring of the fiber product is a finite tensor product of discrete valuation extensions. The length of each one-dimensional branch is the intersection multiplicity of the two cycles. Pulling a local parameter through the first map and taking its field norm through the second records the same length as its valuation. Therefore the divisor obtained by composing pullback and norm has exactly the scheme-theoretic multiplicities of the composed cycle. This proves the composition law on divisors; principal divisors remain principal by transitivity of field norms.

For coprime $m,n$, the order-$m$ and order-$n$ parts of a cyclic subgroup of order $mn$ are unique, whence

$$
T_mT_n=T_{mn}. \tag{3.6}
$$

For a prime $\ell\nmid N$, sorting chains of an $\ell$-isogeny and an $\ell^r$-isogeny according to whether the composite kernel is cyclic gives

$$
T_\ell T_{\ell^r}
=T_{\ell^{r+1}}+\ell\langle\ell\rangle T_{\ell^{r-1}}
\quad\text{on }J. \tag{3.7}
$$

The scalar is $\ell$, rather than $\ell^{k-1}$, because the Jacobian realizes weight two. Pulling (3.7) back to differentials gives the weight-two coefficient relation.

For completeness, the exceptional term in (3.7) can be seen without an expansion formula. A chain of an $\ell$-isogeny followed by an $\ell^r$-isogeny contributes to $T_{\ell^{r+1}}$ when its composite kernel is cyclic. In every remaining chain the composite contains the full group $E[\ell]$ and factors as multiplication by $\ell$ followed by an $\ell^{r-1}$-isogeny. The induced map on degree-zero divisor classes contains the scalar $[\ell]$. Transport of prime-to-$\ell$ point or full level through the determinant-$\ell$ isogeny contributes $\langle\ell\rangle$. This gives the second term of (3.7), including both its integral scalar and its diamond.

The transpose of (3.1) acts by $(\pi_1)_*\pi_2^*$. Moduli duality identifies this transpose with the expected diamond twist of the original Hecke correspondence. In particular, with the standard point-level normalization,

$$
T_\ell^\dagger=\langle\ell\rangle^{-1}T_\ell. \tag{3.8}
$$

On cyclic level the diamond is invisible and this says that $T_\ell$ is self-adjoint. On a diamond eigenspace, the scalar twist must be retained unless the pairing also pairs the character with its inverse. More generally, it is safest to retain the exact transpose symbol. Every later component-pairing statement is

$$
\langle T x,y\rangle=\langle x,T^t y\rangle, \tag{3.9}
$$

which remains correct whether or not a generator happens to be self-adjoint.

## 4. The integral Hecke action on Néron models

The raw closure of a correspondence depends on the chosen integral curve model, while an arithmetic Hecke action must be canonical. The Néron model resolves this tension: its universal property defines the operator, and regular closures are reserved for calculation. This chapter establishes that canonical action and records exactly which integral subquotients it preserves.

### 4.1 Canonical extension

Let $\mathcal J/S$ be the Néron model of $J/K$. A generic Hecke endomorphism $T:J\to J$ extends uniquely to

$$
\mathcal T:\mathcal J\longrightarrow\mathcal J. \tag{4.1}
$$

Indeed $\mathcal J$ is smooth over $S$, so it is an admissible test scheme for the Néron mapping property of the target. The generic map extends as an $S$-morphism. It is a homomorphism because the two maps

$$
\mathcal T\circ m,\qquad
m\circ(\mathcal T\times\mathcal T)
$$

agree on the schematically dense generic fiber. Uniqueness then proves additivity, composition, and every relation inherited from generic correspondences.

This short argument is the source of the integral Hecke action. It does not require the Hecke correspondence itself to extend finitely over every bad prime. When a regular closure exists, that closure calculates (4.1); it does not define a competing operator.

### 4.2 A global integral Hecke algebra

Let $\mathbb T$ be the subring of $\operatorname{End}_K(J)$ generated by the generic $T_m$, the available $U_q$ at primes in the level, diamond operators, and Atkin--Lehner involutions. Then extension gives an injective ring map

$$
\mathbb T\hookrightarrow\operatorname{End}_S(\mathcal J). \tag{4.2}
$$

Injectivity follows by restriction to the generic fiber. Thus the same abstract ring acts at every closed point of $S$. If one begins instead with a free correspondence algebra before quotienting by its action on $J$, the map need not be injective: a nonzero correspondence can act trivially on the Jacobian. The Hecke algebra in (4.2) is, by definition, the image acting on $J$.

Localization commutes with this action. At a closed point $s$, the restriction of $\mathcal T$ to $\operatorname{Spec}\mathcal O_{S,s}$ is the unique local Néron extension. Finite unramified base change commutes with Néron models, so geometric special-fiber actions carry the natural residue Galois action. Ramified base change instead gives a canonical comparison morphism from the old base change to the new Néron model; Hecke operators commute with that comparison because the two composites agree generically.

### 4.3 Connected fibers, components, and cotangent lattices

Every $\mathcal T$ preserves the open identity subgroup $\mathcal J^0$. On the special fiber it therefore induces

$$
\mathcal T_k^0:\mathcal J_k^0\to\mathcal J_k^0,
\qquad
\Phi(T):\Phi_J\to\Phi_J. \tag{4.3}
$$

The proof is topological and scheme-theoretic: the image of a connected component containing the identity is connected and contains the identity. Quotienting by $\mathcal J_k^0$ gives the finite étale component map.

Differentiation at the identity gives an action on

$$
\operatorname{Lie}(\mathcal J/S),
$$

while pullback gives the contravariant action on the dual locally free module

$$
\omega_{\mathcal J/S}=e^*\Omega^1_{\mathcal J/S}. \tag{4.4}
$$

At a place of good reduction, $\mathcal J$ is the relative Jacobian and

$$
\omega_{\mathcal J/S}\simeq f_*\omega_{\mathcal X/S}.
$$

At a semistable place the same formula holds for the separated Picard/Néron model: invariant differentials on the generalized Jacobian are dualizing differentials on the nodal curve, with opposite residues at the two branches of every node. Consequently (4.4) remains a full integral lattice even when the Hodge-line presentation of modular forms requires extra care.

### 4.4 What extension does not imply

If a generic Hecke map is an isogeny, its Néron extension need not be finite, flat, or surjective on special fibers. An isogeny can change component groups at primes dividing its degree. The safe statement comes from a quasi-inverse. If $u,v$ satisfy

$$
vu=[n],\qquad uv=[n],
$$

then the kernel and cokernel of $\Phi(u)$ are killed by $n$. Away from primes dividing $n$, $\Phi(u)$ is an isomorphism on primary parts.

Nor does a rational idempotent in $\mathbb T\otimes\mathbf Q$ automatically cut out an integral direct factor of $\mathcal J$. Its denominator can create a nonsaturated intersection with the cotangent, toric, or component lattice. Integral quotients must be formed from actual ideals or finite flat subgroup schemes, with saturation checked separately. These cautions become central when an Eisenstein or maximal-ideal quotient is used.

## 5. Integral Albanese maps and specialization

Hecke operators become arithmetically useful when they can be evaluated on actual points. The Albanese map is the bridge from modular points and cusps to the Jacobian, while the component map records where those divisor classes land after reduction. This chapter proves that both bridges commute with resolved Hecke actions, including the base-point correction that is easily hidden by informal notation.

### 5.1 Extension over the smooth locus

Let $R$ be a discrete valuation ring and let $\mathcal X/R$ be a regular proper model of $X/K$. Choose a section $c:R\to\mathcal X$ through the smooth locus; a rational cusp on a regular modular model usually provides one. Write $\mathcal X^{\rm sm}$ for the relative smooth locus. The generic Abel map $j_c:X\to J$ extends uniquely to

$$
\mathfrak j_c:\mathcal X^{\rm sm}\longrightarrow\mathcal J. \tag{5.1}
$$

This is an immediate but important use of the Néron property: $\mathcal X^{\rm sm}$ is smooth over $R$, so the generic map is an admissible test morphism. It sends $c$ to the identity because the two sections agree generically.

There is also a direct Picard construction. For a test scheme $T\to\mathcal X^{\rm sm}$, the graph of $T\to\mathcal X$ is a relative Cartier divisor on $\mathcal X_T$ because it lies in the smooth locus. The line bundle

$$
\mathcal O_{\mathcal X_T}(\Gamma_T-c_T)
$$

has generic degree zero and defines a point of the relative Picard object. Passing to the separated quotient gives a point of $\mathcal J(T)$. This construction agrees with (5.1) on the generic fiber, hence everywhere by uniqueness.

One should not claim a morphism from all of $\mathcal X$ to $\mathcal J$ merely from (5.1). At a node the diagonal need not be a Cartier divisor relative to the base, and $\mathcal X$ is not smooth over $R$, so the Néron mapping property does not apply. A map may extend in a particular semistable model after extra choices, but the canonical statement is (5.1). The unpointed version maps the smooth locus to the integral degree-one Picard torsor.

### 5.2 The divisor formula

Let $P$ be a section of $\mathcal X^{\rm sm}/R$. Then

$$
\mathfrak j_c(P)=[P-c]\in\mathcal J(R). \tag{5.2}
$$

Suppose a finite generic correspondence $X\xleftarrow{\alpha}H\xrightarrow{\beta}X$ extends, after normalization and resolution, to

$$
\mathcal X\xleftarrow{a}\mathcal H\xrightarrow{b}\mathcal X.
$$

Move $P$ and $c$ away from the finitely many bad points of the resolved maps. Then the Néron extension satisfies

$$
\mathcal T\,\mathfrak j_c(P)
=\left[b_*a^*(P-c)\right]. \tag{5.3}
$$

The brackets mean the class in the separated Picard quotient. To prove (5.3), calculate on the generic fiber using pullback and norm. The closure of the generic pullback can differ from $a^*(P-c)$ by a vertical divisor, and proper pushforward can introduce another vertical divisor. Both lie in the schematic closure of the generic identity and vanish in the separated quotient. Thus the resolved formula gives the canonical Néron extension.

Formula (5.3) remains valid after replacing $P$ by a horizontal degree-zero divisor. It is often the most efficient route from a modular description of a Hecke orbit to a component-group calculation.

### 5.3 Hecke equivariance and base-point corrections

The Abel map is not literally Hecke equivariant unless the base divisor is treated correctly. Let $T=\beta_*\alpha^*$ and put

$$
d_T=\deg(\alpha),
\qquad
C_T=\beta_*\alpha^*[c],
$$

an effective divisor of degree $d_T$ on $X$. For a geometric point $x$ away from the branch locus,

$$
Tj_c(x)
=\left[\beta_*\alpha^*[x]-C_T\right]. \tag{5.4}
$$

If the correspondence defines a morphism from $X$ to a symmetric power, let

$$
h_T(x)=\beta_*\alpha^*[x]\in X^{(d_T)}.
$$

The degree-$d_T$ Abel map based at $c$ then gives

$$
Tj_c=j_c^{(d_T)}\circ h_T-j_c^{(d_T)}(C_T), \tag{5.5}
$$

where the second term is the base-point correction. More invariantly, the square is equivariant for the unpointed Albanese torsor, and choosing $c$ converts that affine equivariance into the correction $C_T-d_Tc$.

If $C_T$ is linearly equivalent to $d_Tc$, then the correction vanishes and the familiar pointed equivariance holds. This occurs for some normalized cusp correspondences, but it must be proved from Tate cusp formulas rather than assumed from a set-theoretic picture.

### 5.4 Components detected by points

Pass to a strict henselian base and write the reduced semistable special fiber as $\bigcup_{v\in V}Y_v$. If sections $P$ and $c$ specialize to smooth points of $Y_v$ and $Y_{v_0}$, then

$$
c_J([P-c])=[e_v-e_{v_0}]
\quad\text{in}\quad
\operatorname{Div}^0(G)/\Delta\mathbf Z^V. \tag{5.6}
$$

The proof is the intersection formula: the horizontal closure of $P-c$ meets $Y_v$ once, $Y_{v_0}$ with multiplicity $-1$, and all other components trivially. A principal divisor changes this vector by the vertical intersection matrix, so its class is intrinsic.

Combining (5.3) and (5.6) gives

$$
c_J(T[P-c])=\Phi(T)[e_v-e_{v_0}]. \tag{5.7}
$$

Thus modular points can detect component maps. They need not generate the entire component group over the ground field: residue Galois orbits and the failure of a rational component torsor to have a rational point can intervene. Over a separably closed residue field, horizontal sections after an étale extension realize every vertex divisor, and (5.6) generates the graph presentation.

## 6. The Hecke correspondence at its residue characteristic

The most delicate good-prime calculation occurs precisely where the auxiliary Hecke degree equals the residue characteristic. Generic étale subgroup choices collide into connected and étale directions, so a generic-fiber argument alone cannot identify the special operator. The Deligne--Rapoport crossing separates those directions with their correct multiplicities and makes Frobenius and Verschiebung visible.

### 6.1 Why the good generic correspondence degenerates

Fix a prime $p$ not dividing the original level. Over characteristic zero, the auxiliary $p$-isogeny curve in (3.1) is generically étale over the source modular curve. In characteristic $p$, a cyclic subgroup of rank $p$ can be connected. The $p+1$ generic lines in $E[p]$ do not remain $p+1$ disjoint choices.

For an ordinary elliptic curve there are exactly two integral types: the connected subgroup $\ker F_E$ and the étale subgroup that is dual to a Frobenius kernel. At a supersingular elliptic curve both directions specialize to the unique local-local subgroup $\alpha_p$. The isogeny deformation ring is

$$
W(k)[[x,y]]/(xy-p). \tag{6.1}
$$

Modulo $p$ the two directions become the branches $x=0$ and $y=0$. The total surface is regular because the equation has a nonzero linear term $-p$ in its maximal ideal, and the branches meet transversely. This geometry, rather than a count of geometric subgroup points, controls specialization of $T_p$.

### 6.2 The two Deligne--Rapoport branches

Work first on a prime-to-$p$ rigidified fine cover $X(\mathcal P)$. Let

$$
\mathscr H=X_0(p;\mathcal P)
$$

be the regular Deligne--Rapoport model of the auxiliary correspondence. Its special fiber is

$$
\mathscr H_k=C_F\cup C_V. \tag{6.2}
$$

Both components are smooth and are normalized by the base modular curve $X(\mathcal P)_k$, possibly after Frobenius twist. They meet exactly at the supersingular points. The two degeneracy maps restrict, after the appropriate twist identifications, as

$$
\begin{array}{c|cc}
&\pi_1&\pi_2\\ \hline
C_F&1&F_X\\
C_V&F_X&1.
\end{array} \tag{6.3}
$$

At a cusp the same statement is visible in parameters. On the multiplicative branch,

$$
(\pi_1^*q,\pi_2^*q)=(q,q^p),
$$

while on the component branch,

$$
(\pi_1^*q,\pi_2^*q)=(t^p,t).
$$

Thus the identity/Frobenius labels extend across the boundary and do not merely describe the ordinary elliptic open.

### 6.3 Specializing the correspondence cycle

Let $\Gamma_p$ be the generic cycle of the $p$-isogeny correspondence in $X\times X$. Its flat closure in the fine integral product has special cycle

$$
[\Gamma_p]_k=[\Gamma_{F}]+[\Gamma_{V}], \tag{6.4}
$$

where each component has multiplicity one.

The multiplicity assertion is essential. It follows from the local equation (6.1): the special-fiber equation is $xy=0$, whose two minimal primes $(x)$ and $(y)$ occur with length one at their generic points. No vertical third component exists because the total correspondence is flat over the discrete valuation ring, and the ordinary locus already exhausts its one-dimensional special-fiber components. Supersingular points are intersections of the two components, not additional one-cycles.

The action of a flat family of cycles on the relative Picard scheme specializes additively. Alternatively, use the integral correspondence theorem: normalize and resolve the closure, calculate pull--push on the two components, and pass to the separated quotient. Vertical excess at their intersection lies in the closure of the generic identity. Either route shows that the special endomorphism is the sum of the endomorphisms attached to the two rows of (6.3).

### 6.4 Frobenius, Verschiebung, and diamond descent

Let $X/k$ be smooth and proper. Relative Frobenius

$$
F_X:X\longrightarrow X^{(p)}
$$

induces two maps on Jacobians:

$$
(F_X)^*:J_{X^{(p)}}\to J_X,
\qquad
(F_X)_*:J_X\to J_{X^{(p)}}.
$$

They satisfy

$$
(F_X)_*(F_X)^*=[p]. \tag{6.5}
$$

The norm map $(F_X)_*$ is relative Frobenius on the Jacobian, and pullback $(F_X)^*$ is Verschiebung. This can be checked on divisor classes: the norm sends the class of $\sum n_iP_i$ to the class of $\sum n_iF_X(P_i)$, which is precisely relative Frobenius on the Picard variety. The norm--pullback relation gives the product $[p]$, so pullback is its dual isogeny, Verschiebung. The zero differential of the norm is a useful independent check. Hence

$$
(F_X)_*=F_J,\qquad (F_X)^*=V_J. \tag{6.6}
$$

When the level has a chosen generator or symplectic component, identifying the Frobenius twist with the original modular curve changes the level label by the determinant $p$. Descent therefore inserts the diamond operator on one branch. With the convention of Section 1.3, the two branch actions are

$$
F_p,\qquad \langle p\rangle V_p. \tag{6.7}
$$

On a cyclic-level problem where the unit action is invisible, $\langle p\rangle=1$. Formula (6.7) is invariant under changing the auxiliary rigidifying cover: both sides descend from the same generic correspondence, and equality can be checked after a faithfully flat cover.

The diamond deserves a more explicit check. On a full level structure $(P,Q)$, the Weil pairing satisfies

$$
e_N(FP,FQ)=e_N(P,Q)^p.
$$

Thus Frobenius carries a symplectic component labeled by a primitive root $\zeta_N$ to the component labeled by $\zeta_N^p$. Returning to the original component requires the unit action of determinant $p$. On $\Gamma_1(N)$ the same discrepancy is recorded by the transported generator, while on $\Gamma_0(N)$ rescaling a generator does not change the cyclic subgroup and the discrepancy disappears. This is precisely why the relation contains $\langle p\rangle$ in point or full level and no visible diamond on bare cyclic level.

There is no ambiguity from choosing arithmetic rather than geometric Frobenius in this geometric calculation. The morphism $F_X$ is relative $p$-power Frobenius. Its norm is relative Frobenius of the Picard variety, and its pullback is Verschiebung. Only when the resulting endomorphism is compared with a Galois element in Section 7.3 does a Frobenius convention enter.

## 7. The integral Eichler--Shimura relation

The preceding geometry is now converted into an endomorphism identity. The aim is stronger than obtaining a characteristic polynomial over a fraction field: the equality must hold on the special abelian variety, so that it survives on torsion lattices and Hecke quotients. We then distinguish carefully between the unconditional annihilating polynomial and the additional rank hypotheses needed to call it a characteristic polynomial.

### 7.1 The endomorphism identity

Let $p$ be a prime of good reduction for the fixed modular curve $X$ and its Jacobian $J$. Let $\mathcal J$ be the abelian scheme over the localization at $p$, and let $J_k$ be its special fiber. Then

$$
T_p=F_p+\langle p\rangle V_p
\quad\text{in }\operatorname{End}_k(J_k). \tag{7.1}
$$

**Proof.** Construct the auxiliary $p$-isogeny correspondence on a prime-to-$p$ rigidified fine cover. Its Deligne--Rapoport special fiber is the reduced sum of the two components (6.4). The first row of (6.3), inserted into the variance $(\pi_2)_*\pi_1^*$, acts by $(F_X)_*=F_p$. The second row acts by $(F_X)^*=V_p$ before level descent. The level identification contributes $\langle p\rangle$, giving the second term in (7.1). Additivity of cycle actions gives the equality on the fine Jacobian.

Every construction is equivariant for the finite change-of-level group. The equality of special correspondence cycles therefore descends before applying the Picard functor. Applying pull--norm on the descended curve gives the equality on the stack and on the coarse Jacobian. This argument does not require pullback from the coarse Jacobian to the fine Jacobian to be faithful. $\square$

The theorem is integral in two senses. No denominator occurs, and the equality holds as homomorphisms of abelian varieties, not merely on rational cohomology. It consequently remains true after applying any functorial finite subgroup scheme, Tate module away from $p$, cotangent space, or quotient by a Hecke-stable abelian subvariety.

### 7.2 The quadratic polynomial

Frobenius and Verschiebung satisfy

$$
F_pV_p=V_pF_p=[p]. \tag{7.2}
$$

They commute with diamond operators. Multiply (7.1) on the right by $F_p$:

$$
T_pF_p=F_p^2+\langle p\rangle V_pF_p
=F_p^2+p\langle p\rangle.
$$

Therefore

$$
F_p^2-T_pF_p+p\langle p\rangle=0
\quad\text{in }\operatorname{End}_k(J_k). \tag{7.3}
$$

The same calculation with $V_p$ gives

$$
\langle p\rangle V_p^2-T_pV_p+p=0,
$$

after moving the diamond factor according to the chosen component convention. Equation (7.3) is the form used most often.

It is important not to misstate (7.3) as an equality in $\operatorname{End}_K(J)$: $F_p$ is an endomorphism of the characteristic-$p$ special fiber. The integral Néron model provides the common specialization on which $T_p$ and $F_p$ can be compared.

### 7.3 Tate modules and Frobenius

Let $\ell\ne p$. Good reduction gives a canonical unramified identification

$$
T_\ell J_{\overline K}\simeq T_\ell J_{\bar k}. \tag{7.4}
$$

Arithmetic Frobenius in the residue Galois group acts on the right as the Frobenius endomorphism $F_p$. Applying $T_\ell$ to (7.3) yields

$$
\operatorname{Frob}_p^2
-T_p\operatorname{Frob}_p
+p\langle p\rangle=0
\quad\text{on }T_\ell J. \tag{7.5}
$$

To justify (7.4), note that for $\ell\ne p$ the finite group schemes $\mathcal J[\ell^n]$ are finite étale over the henselian good-reduction base. Finite étale objects are unchanged by passage between the generic unramified fiber and the special fiber. Taking inverse limits gives the identification and shows inertia acts trivially.

Equation (7.5) is an equality over $\mathbf Z_\ell$. It is stronger than the same equation after tensoring with $\mathbf Q_\ell$: reduction modulo $\ell^n$ gives the relation on every $J[\ell^n]$. If $\ell=p$, the prime-to-characteristic argument fails. Equation (7.3) still holds on the abelian variety and hence on its $p$-divisible group, but its connected and étale parts must be retained; geometric $p$-torsion points alone do not capture the assertion.

### 7.4 Quotients and Galois extraction

Let $I\subset\mathbb T$ be an ideal and let $A$ be a Hecke-stable abelian quotient of $J$ on which $\mathbb T$ acts. Functoriality carries (7.3) to $A_k$:

$$
F_{A,p}^2-T_pF_{A,p}+p\langle p\rangle=0. \tag{7.6}
$$

If $\mathfrak m$ is a maximal ideal of residue characteristic $\ell\ne p$, then on the $\mathfrak m$-torsion or on any rank-two eigenspace with character $\chi$,

$$
X^2-a_pX+p\chi(p) \tag{7.7}
$$

annihilates arithmetic Frobenius, where $a_p$ is the image of $T_p$ and $\chi(p)$ the image of $\langle p\rangle$. Thus the trace is $a_p$ and the determinant is $p\chi(p)$ whenever the module is free of rank two and the polynomial is its characteristic polynomial.

The freeness and rank conclusion do not follow from Eichler--Shimura alone. They require a separate multiplicity, torsion-freeness, or Gorenstein argument. What (7.6) supplies unconditionally is the annihilating polynomial and its compatibility at every good prime. This distinction prevents a circular construction of a two-dimensional representation by assuming in advance the dimension one is trying to prove.

## 8. Néron models at a prime in the level

At a prime in the level, the Deligne--Rapoport curve is no longer merely an auxiliary correspondence; it is the integral model of the modular curve itself. Its two components, supersingular intersections, and quotient thicknesses determine the connected Néron fiber and its components. This chapter translates the moduli picture into the Picard, graph, and finite-lattice descriptions used in specialization arguments.

### 8.1 The Deligne--Rapoport curve as a Picard model

Now let $q$ divide the cyclic level exactly once, and let $R$ be an unramified discrete valuation ring of residue characteristic $q$. On a prime-to-$q$ rigidified branch cover, the Deligne--Rapoport model

$$
\mathscr X=X_0(q;\mathcal P)/R
$$

is regular, proper, flat, and semistable. Its generic fiber has Jacobian $J$, and its special fiber is

$$
\mathscr X_k=C_F\cup C_V. \tag{8.1}
$$

Let $P^{[0]}$ be the relative Picard object whose generic restriction has degree zero, and let $E$ be the schematic closure of the generic identity. Then

$$
\mathcal J=P^{[0]}/E \tag{8.2}
$$

is the Néron model of $J$.

The quotient is necessary. The line bundle $\mathcal O_{\mathscr X}(C_F)$ is generically trivial but has special multidegree

$$
(C_F^2,C_F\cdot C_V)=(-s,s),
$$

where $s$ is the degree of the supersingular divisor on the fine base curve. Hence two line bundles can agree generically and differ by a nonzero special multidegree. Quotienting by $E$ removes exactly these vertical twists and makes the Picard object separated.

### 8.2 The connected special fiber

Let $Y_F$ and $Y_V$ be the two normalized components; each is a Frobenius twist of $X(\mathcal P)_k$. Let $G$ be the dual graph. The generalized Jacobian of the nodal special fiber gives

$$
0\longrightarrow T_G
\longrightarrow\mathcal J_k^0
\longrightarrow J(Y_F)\times J(Y_V)
\longrightarrow0, \tag{8.3}
$$

with

$$
X^*(T_G)=H_1(G,\mathbf Z). \tag{8.4}
$$

To prove (8.3), normalize the special fiber. A line bundle of multidegree zero is a pair of degree-zero line bundles on $Y_F,Y_V$ together with a nonzero scalar identifying the two fibers above every node. Rescaling the line bundle on either component changes all adjacent scalars by a vertex scalar. The quotient of edge scalars by vertex rescaling is the torus whose character group is the kernel of the graph boundary, namely $H_1(G,\mathbf Z)$. This gives exactness and identifies the torus.

If there are $r$ geometric supersingular nodes, $G$ has two vertices and $r$ parallel edges. Hence

$$
\operatorname{rank}T_G=r-1,
$$

and

$$
\dim J
=2g(X(\mathcal P)_k)+(r-1).
$$

The latter is the normalization genus formula and checks that no dimension is lost in (8.3).

### 8.3 The component group of the fine model

Assume the residue field is separably closed and the $r$ supersingular nodes are geometric. In the basis $(C_F,C_V)$, the intersection matrix is

$$
M=
\begin{pmatrix}
-r&r\\
r&-r
\end{pmatrix}. \tag{8.5}
$$

The degree-zero component lattice is

$$
\Lambda=\{(a,-a):a\in\mathbf Z\}.
$$

The image $M\mathbf Z^2$ is generated inside $\Lambda$ by $(r,-r)$. Therefore

$$
\Phi_J(k^s)\simeq\mathbf Z/r\mathbf Z. \tag{8.6}
$$

This calculation is equivalent to the graph critical group. Orient every edge from $C_F$ to $C_V$. Then

$$
X_G=\left\{(a_1,\ldots,a_r)\in\mathbf Z^r:
\sum_i a_i=0\right\}, \tag{8.7}
$$

with the ordinary dot product. This is the root lattice of type $A_{r-1}$; its dual quotient has order $r$ and is cyclic. The class of $e_F-e_V$ in the vertex presentation is a generator.

Over a nonclosed field, (8.6) is an assertion about geometric points with Galois action. Rational components are the invariants of the finite étale group scheme, not automatically all of $\mathbf Z/r\mathbf Z$. The integer $r$ must count geometric supersingular points with residue degrees, rather than only rational ones.

### 8.4 Coarse models and weighted nodes

On the modular stack the two components cross in a smooth chart. A tame coarse stabilizer of effective order $n_e$ changes a unit node into

$$
xy=\pi^{n_e}. \tag{8.8}
$$

The stable coarse fiber still has two principal components, but its node has length $n_e$. Resolving the surface inserts a chain of $n_e-1$ rational curves. The metrized cycle lattice is unchanged by this subdivision.

For a weighted two-vertex graph with edge lengths $n_1,\ldots,n_r$, the cycle lattice remains (8.7), while

$$
q(a,b)=\sum_{i=1}^r n_i a_i b_i. \tag{8.9}
$$

Thus

$$
\Phi_J(k^s)=X_G^\vee/qX_G. \tag{8.10}
$$

Its order is the weighted spanning-tree number

$$
|\Phi_J(k^s)|
=\sum_{i=1}^r\prod_{j\ne i}n_j. \tag{8.11}
$$

To prove (8.11), choose the basis $e_i-e_r$ for $1\le i<r$. Its Gram matrix has diagonal entries $n_i+n_r$ and off-diagonal entries $n_r$. The matrix determinant lemma gives

$$
\det q
=\left(\prod_{i<r}n_i\right)
\left(1+n_r\sum_{i<r}\frac1{n_i}\right)
=\sum_i\prod_{j\ne i}n_j.
$$

The determinant gives the order, not the invariant factors. Smith normal form of the Gram matrix is required to determine the group itself.

## 9. Hecke operators on bad fibers

Canonical extension proves that a Hecke operator exists at a bad place but does not display its matrix. To calculate it one must resolve the closure, retain all component and ramification multiplicities, and then descend through the vertical intersection relations. The graph form of the same calculation exposes adjunction, Atkin--Lehner signs, and the saturation phenomena attached to Hecke ideals.

### 9.1 The resolved pull--push calculation

Let $T$ be a Hecke correspondence on the generic modular curve and let $\mathscr X/R$ be a regular model at a bad place. The closure of the correspondence in $\mathscr X\times_R\mathscr X$ need not be regular, and either projection can contract a vertical curve. Normalize the closure and resolve it to obtain

$$
\mathscr X\xleftarrow{a}\mathscr H\xrightarrow{b}\mathscr X. \tag{9.1}
$$

The Néron operator is still $b_*a^*$, interpreted on separated Picard quotients. This gives an exact finite algorithm on components.

Write

$$
\mathscr X_k=\sum_i m_iX_i,\qquad
\mathscr H_k=\sum_a n_aH_a.
$$

Let $M_X$ and $M_H$ be the vertical intersection matrices. Define $D_a$ by the degrees with which $H_a$ dominates $X_i$ under $a$, and define $E_b$ by

$$
b^*X_i=\sum_a(E_b)_{ai}H_a. \tag{9.2}
$$

Then pullback on special multidegrees is $D_a$, while pushforward of horizontal intersection vectors is $E_b^t$. The component map is

$$
\Phi(T)=[E_b^tD_a] \tag{9.3}
$$

on the quotients

$$
\{d:\sum m_id_i=0\}/M_X\mathbf Z^{I_X}.
$$

The compatibility that makes (9.3) well defined is

$$
D_aM_X=M_HE_a,\qquad
M_XD_b^t=E_b^tM_H. \tag{9.4}
$$

For example, the first identity says that the degree on $H_a$ of the pulled-back vertical line bundle $\mathcal O(X_i)$ can be calculated either from multidegrees or from the Cartier divisor $a^*X_i$. The second is its transpose together with symmetry of intersection. Consequently matrix images map to matrix images.

Different resolutions give the same result. A point blowup adds one exceptional generator and one vertical relation; these cancel in the finite cokernel. More conceptually, pullback along a birational regular modification induces the identity on the generic Jacobian, so its Néron extension is an isomorphism. On a common domination, the two versions of (9.3) are conjugate by these canonical identifications.

### 9.2 The action on the two-vertex graph

For the Deligne--Rapoport fiber, a correspondence away from $q$ maps ordinary and supersingular moduli points by prime-to-$q$ isogenies. After a suitable fine cover and resolution it induces a harmonic correspondence of the geometric graph. There are two equivalent descriptions.

On vertex divisors, a degree-preserving self-correspondence has a matrix of the form

$$
A=\begin{pmatrix}a&b\\ b&a\end{pmatrix} \tag{9.5}
$$

whenever it commutes with interchange of the two Frobenius--Verschiebung components. It sends

$$
(1,-1)\longmapsto(a-b)(1,-1).
$$

Thus on the unit-edge component group (8.6),

$$
\Phi(T):x\longmapsto(a-b)x\pmod r. \tag{9.6}
$$

The row sum $a+b$ controls total degree and disappears from the degree-zero component quotient.

On cycles, the correspondence gives adjoint maps

$$
u_T:X_G\to X_G,\qquad v_T:X_G\to X_G
$$

for $T$ and its transpose. The edge pairing satisfies

$$
q(u_Tx,y)=q(x,v_Ty). \tag{9.7}
$$

The component map is induced on $X_G^\vee/qX_G$ by $v_T^\vee$. This apparent use of the transpose is a variance issue: $X_G$ is the character lattice of the torus, and a torus homomorphism acts contravariantly on characters. Equation (9.7) implies

$$
v_T^\vee q=qu_T,
$$

so the dual-lattice map descends.

### 9.3 Atkin--Lehner on components

The Atkin--Lehner involution $w_q$ interchanges the source and quotient of the universal $q$-isogeny. On the Deligne--Rapoport special fiber it exchanges $C_F$ and $C_V$ and permutes the supersingular nodes by dual isogeny. Therefore

$$
w_q(e_F-e_V)=-(e_F-e_V). \tag{9.8}
$$

For the fine unit-edge model, (9.8) proves

$$
\Phi(w_q)=-1
\quad\text{on }\Phi_J(k^s)\simeq\mathbf Z/r\mathbf Z. \tag{9.9}
$$

The possible permutation of supersingular edges does not alter this conclusion. In the cycle presentation $X_G=A_{r-1}$, every edge permutation acts trivially on the discriminant group $A_{r-1}^\vee/A_{r-1}$: the quotient is generated by the class of

$$
\frac1r(r-1,-1,\ldots,-1),
$$

and permuting coordinates changes this vector by an element of $A_{r-1}$. Interchanging the two vertices reverses every oriented edge and contributes the sign $-1$.

For a weighted coarse graph, edge permutation must preserve lengths to define an isometry. The vertex swap still contributes a sign, but a nontrivial action on the weighted discriminant can remain if duality permutes unequal-length Galois orbits only after base extension. The safe statement is that $w_q$ acts by the negative of the induced edge permutation; (9.9) is the exact fine unit-edge specialization.

### 9.4 Adjoints, ideals, and saturation

The discriminant pairing

$$
\langle\ ,\ \rangle_\Phi:
\Phi_J(k^s)\times\Phi_J(k^s)\to\mathbf Q/\mathbf Z \tag{9.10}
$$

is defined by

$$
\langle\bar x,\bar y\rangle_\Phi
=y(q^{-1}x)\bmod\mathbf Z,
\qquad x,y\in X_G^\vee. \tag{9.11}
$$

It is well defined because changing $x$ by $qz$ changes the value by the integer $y(z)$. It is perfect: if $q^{-1}x$ pairs integrally with every $y\in X_G^\vee$, then $q^{-1}x$ lies in the double dual $X_G$, so $x\in qX_G$.

Equation (9.7) descends to

$$
\langle\Phi(T)x,y\rangle_\Phi
=\langle x,\Phi(T^t)y\rangle_\Phi. \tag{9.12}
$$

Let $I\subset\mathbb T$ be an ideal and write $I^t$ for the ideal generated by transposes. Perfectness gives

$$
(I\Phi)^\perp=\Phi[I^t]. \tag{9.13}
$$

Indeed $x$ is orthogonal to every $ty$ exactly when $t^tx=0$ for every $t\in I$. This identity is integral. Replacing $I\Phi$ by its rational span would erase the saturation quotient and can change both sides.

If $I=I^t$, the annihilator and quotient are Pontryagin dual:

$$
(\Phi/I\Phi)^\vee\simeq\Phi[I]. \tag{9.14}
$$

No analogous statement about an integral direct summand follows from a rational eigenspace alone. A denominator in a projector can contribute precisely at the primes where component groups are arithmetically interesting.

## 10. Monodromy of modular Jacobians

The component group is only the cokernel of the graph pairing; monodromy remembers the pairing itself. Because no general semistable-abelian monodromy theorem is among the declared dependencies, this chapter derives the Jacobian case directly from node smoothing parameters and the normalization sequence. The result explains why Hecke actions on components and inertia are controlled by the same adjoint graph maps.

### 10.1 Why the graph pairing is monodromy

Let $R$ now be strictly henselian, with residue characteristic $p$, and let $\mathscr X/R$ be a regular semistable curve. Write $G$ for its geometric dual graph and

$$
X=H_1(G,\mathbf Z).
$$

At a node $e$, choose an étale local equation

$$
x_ey_e=u_e\pi^{n_e}. \tag{10.1}
$$

The integer $n_e$ measures how many times a loop crossing the node winds around the punctured annulus in a smoothing. For cycles $a=(a_e)$ and $b=(b_e)$, these local winding contributions add to

$$
q(a,b)=\sum_en_ea_eb_e. \tag{10.2}
$$

We now derive the two appearances of $q$: as the component discriminant and as the tame-inertia operator.

The first was established by the Picard quotient. Edge gluing parameters give a torus $T$ with $X^*(T)=X$, and vertical divisors impose the lattice map $q:X\hookrightarrow X^\vee$. Hence

$$
0\longrightarrow X\xrightarrow{q}X^\vee
\longrightarrow\Phi_J(k^s)\longrightarrow0. \tag{10.3}
$$

For the second appearance, a line bundle on the generic curve can acquire monodromy when transported around the Kummer covers $\pi^{1/\ell^m}$. At the annulus (10.1), changing a chosen root multiplies a gluing parameter by an $\ell^m$th root of unity raised to $n_e$. A cycle $a$ therefore produces, against a test cycle $b$, the exponent $\sum n_ea_eb_e$. This is exactly (10.2). The following sections turn this local observation into the full Tate-module statement.

### 10.2 The Tate-module filtration

Fix a prime $\ell\ne p$. Let $B=\prod_vJ(Y_v)$ be the product of the Jacobians of the normalized special components. There is a canonical inertia-stable filtration of $T_\ell J$ whose graded pieces are

$$
\operatorname{gr}_{-2}T_\ell J
\simeq X^\vee\otimes\mathbf Z_\ell(1), \tag{10.4}
$$

$$
\operatorname{gr}_{-1}T_\ell J
\simeq T_\ell B, \tag{10.5}
$$

$$
\operatorname{gr}_{0}T_\ell J
\simeq X\otimes\mathbf Z_\ell. \tag{10.6}
$$

Here $X^\vee=X_*(T)$ because $X=X^*(T)$, so (10.4) is the Tate module of the graph torus.

**Construction and proof.** Normalize the special curve and mark the two branches above every node. A degree-zero line bundle on the nodal fiber is a tuple of component line bundles plus edge gluing scalars, modulo vertex rescaling. Taking $\ell^m$th roots gives the exact connected part

$$
0\to T[\ell^m]\to\mathcal J_k^0[\ell^m]
\to B[\ell^m]\to0
$$

in the prime-to-$p$ étale topology. Passing to inverse limits gives (10.4) below (10.5).

The generic curve has, in addition, vanishing cycles that measure how a divisor can cross the nodes before specializing. The normalization exact sequence for the constant sheaf $\mathbf Z/\ell^m\mathbf Z$ gives a boundary term

$$
H_1(G,\mathbf Z/\ell^m\mathbf Z)
=X/\ell^mX.
$$

Equivalently, cut the smoothing along all node annuli. Cohomology of the normalized pieces supplies $B[\ell^m]$, the circle in each annulus supplies one edge generator, and the condition that boundaries cancel at every component is exactly the graph-cycle condition. Duality for the curve places this term above the component and torus terms. Taking inverse limits gives (10.6).

The ranks check the construction. If $g_v$ are the component genera and $b_1=\operatorname{rank}X$, then

$$
\operatorname{rank}T_\ell J
=b_1+2\sum_vg_v+b_1
=2\left(\sum_vg_v+b_1\right)
=2g(X_K).
$$

Thus the displayed graded pieces account for the entire Tate module.

### 10.3 The Picard--Lefschetz formula

Let

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell(1)
$$

be the tame character, normalized so that $\sigma(\pi^{1/\ell^m})/\pi^{1/\ell^m}$ is the reduction of $t_\ell(\sigma)$. There is a homomorphism

$$
N:T_\ell J\longrightarrow T_\ell J(-1) \tag{10.7}
$$

that kills the first two filtration steps and induces on the outer graded pieces the map

$$
q:X\otimes\mathbf Z_\ell
\longrightarrow X^\vee\otimes\mathbf Z_\ell. \tag{10.8}
$$

For every $\sigma\in I_K$,

$$
\sigma(v)=v+t_\ell(\sigma)N(v),
\qquad N^2=0. \tag{10.9}
$$

**Proof.** Choose a lift of a graph cycle $a$ to an $\ell^m$-division class on the generic Jacobian. On the normalization pieces it can be chosen inertia invariant, because the pieces and their prime-to-$p$ torsion are unramified over the strict henselian base. The only change under inertia occurs in the chosen roots of the node smoothing parameters. At node $e$, equation (10.1) contributes

$$
t_\ell(\sigma)n_ea_e
$$

to the toric gluing character. Evaluation on a second cycle $b$ gives

$$
t_\ell(\sigma)\sum_en_ea_eb_e
=t_\ell(\sigma)q(a,b).
$$

Thus the difference $\sigma(v)-v$ lies in the toric graded piece and is $t_\ell(\sigma)q(a)$. Classes from the torus and normalized-component Jacobians are invariant, so applying the difference a second time gives zero. This proves (10.8)--(10.9) modulo every $\ell^m$ and hence on the inverse limit. $\square$

The formula is independent of the chosen local coordinates: replacing $x_e$ or $y_e$ by a unit changes the Kummer class by an unramified unit and does not alter tame inertia. Reversing an edge changes both $a_e$ and $b_e$ by a sign, leaving $q$ unchanged.

Good reduction is the case $X=0$, so $N=0$ and inertia is trivial. A unit loop has nonzero $X$ and nonzero monodromy even though its component group can be trivial. This again shows that $\Phi_J$ alone does not determine reduction.

### 10.4 Hecke equivariance of monodromy

Let $T$ be a Hecke correspondence and $T^t$ its transpose. On graph cycles let

$$
u_T:X_C\to X_D,\qquad v_T:X_D\to X_C
$$

be the pull--push maps attached to $T$ and $T^t$. Edgewise projection gives

$$
q_D(u_Tx,y)=q_C(x,v_Ty). \tag{10.10}
$$

Consequently the maps induced by $T$ on the outer monodromy graded pieces form the commutative square

$$
\begin{array}{ccc}
X_C\otimes\mathbf Z_\ell&\xrightarrow{q_C}&X_C^\vee\otimes\mathbf Z_\ell\\
\downarrow u_T&&\downarrow v_T^\vee\\
X_D\otimes\mathbf Z_\ell&\xrightarrow{q_D}&X_D^\vee\otimes\mathbf Z_\ell.
\end{array} \tag{10.11}
$$

The maps on the normalized-component Jacobians are ordinary pullback and norm. Hence the entire filtration (10.4)--(10.6) is Hecke stable, and

$$
N_DT=TN_C \tag{10.12}
$$

with the evident Tate twist.

There are two proofs of (10.12). The local proof applies the projection formula to the node exponents in (10.2). The conceptual proof observes that the generic Hecke endomorphism commutes with the Galois action; insert (10.9), choose $\sigma$ with nonzero tame character, and compare the two sides. The local proof is needed to identify the resulting operator with the explicit graph pairing, while the conceptual proof verifies independence of every resolution.

For the Deligne--Rapoport graph with $r$ unit edges, monodromy is the inclusion of $A_{r-1}$ into its dual. Its cokernel is $\mathbf Z/r\mathbf Z$, exactly the component group. Thus the toric rank, the inertia operator, and the component group are three readings of one lattice:

$$
\operatorname{rank}A_{r-1}=r-1,
\qquad N=q,
\qquad\operatorname{coker}q=\mathbf Z/r\mathbf Z.
$$

## 11. Differential and q-expansion realizations

The Jacobian action has a cotangent realization that must agree with the familiar Hecke action on weight-two forms. At good level, Kodaira--Spencer and q-expansion provide the comparison. At a level prime, cusp widths can cease to be units, so the regular dualizing lattice must replace any unproved Hodge-line formula. This chapter gives one canonical lattice valid in both situations.

### 11.1 The canonical cotangent lattice

Let $R$ be a discrete valuation ring and $\mathcal J/R$ the Néron model of a modular Jacobian. The module

$$
\omega_{\mathcal J/R}=e^*\Omega^1_{\mathcal J/R} \tag{11.1}
$$

is finite free of rank $g$. It is canonical: no regular curve model or cusp is required to define it. If $\mathscr X/R$ is a Picard-admissible regular proper model, the Picard description gives

$$
\omega_{\mathcal J/R}\simeq H^0(\mathscr X,\omega_{\mathscr X/R}). \tag{11.2}
$$

For a smooth model this is the familiar cotangent formula. For a semistable model, a dualizing differential is a collection of meromorphic differentials on the normalized components with at worst simple poles at node branches and opposite residues on paired branches. Those residue directions are dual to the graph torus, so their inclusion is required for the rank in (11.2) to remain $g$.

To prove (11.2), identify the tangent space of the relative Picard object with $R^1f_*\mathcal O_{\mathscr X}$. Quotienting by the étale lattice of vertical components does not change the formal identity neighborhood. Relative duality identifies its dual with $f_*\omega_{\mathscr X/R}$. Both sides are finite free and the generic-fiber map is the standard Jacobian identification, so it is an isomorphism.

### 11.2 Comparison with geometric Hecke operators

Let $T=\beta_*\alpha^*$ be represented by a finite locally free correspondence over an open part of the base. On Jacobians it acts covariantly. On cotangent modules, pullback is

$$
T^*=\alpha_*^{\rm tr}\beta^*. \tag{11.3}
$$

Under (11.2), (11.3) is exactly pullback of a dualizing differential along $\beta$ followed by trace along $\alpha$.

**Proof.** The norm map $\beta_*$ is dual under the canonical polarization to $\beta^*$, so its pullback on invariant differentials is ordinary pullback along $\beta$. The pullback map $\alpha^*$ on Jacobians is dual to norm, so its pullback on differentials is trace along $\alpha$. Composition reverses under pullback, giving (11.3). The same result follows from residues: trace of differentials is characterized by

$$
\operatorname{res}_x\operatorname{Tr}_{H/X}(\eta)
=\sum_{y\mapsto x}\operatorname{Tr}_{\kappa(y)/\kappa(x)}
\operatorname{res}_y(\eta),
$$

including ramification multiplicities. $\square$

At good level, use Kodaira--Spencer to identify (11.3) with the normalized weight-two Hecke operator. The apparent factor $1/\ell$ in the modular-form trace formula is canceled by the factor $\ell$ with which the multiplicative quotient pulls back the Tate differential. The resulting operator on regular differentials is integral and equals the pullback of the integral Jacobian endomorphism.

### 11.3 The residue characteristic and the dualizing lattice

At a prime dividing the level, the good-level identity

$$
\lambda^2(-D)\simeq\omega
$$

cannot be imported without proof: in a cusp parameter $q=t^w$, the relation $dq/q=w\,dt/t$ can lose a unit when the residue characteristic divides $w$. The canonical object is therefore the right side of (11.2).

Define the integral weight-two differential lattice at such a place by

$$
S_2^{\rm can}(R)=H^0(\mathscr X,\omega_{\mathscr X/R}). \tag{11.4}
$$

Its generic fiber is the usual space of weight-two cusp forms. It is independent of the chosen regular model: a blowup of a closed point on a regular surface has

$$
r_*\omega_{\mathscr X'/R}=\omega_{\mathscr X/R}
$$

and no higher discrepancy in global regular differentials. Equivalently, both lattices identify with $\omega_{\mathcal J/R}$ by (11.2).

Every Hecke operator preserves (11.4), even when its raw curve correspondence is not finite on the chosen model. This follows immediately from its Néron extension and pullback on (11.1). A resolved curve calculation gives the same map by (11.3); exceptional and vertical terms do not alter regular dualizing forms after trace. Thus the canonical differential lattice supplies the correct replacement for an unproved bad-level Hodge-line formula.

### 11.4 Faithfulness and finite verification

At good level, q-expansion at cusps meeting every component injects the space of modular forms into a product of power-series rings. Hence an equality of Hecke operators on $S_2$ can be checked on q-expansions. The coefficient formula

$$
a_n(T_\ell f)=a_{\ell n}(f)
+\ell a_{n/\ell}(\langle\ell\rangle f) \tag{11.5}
$$

is the differential realization of the geometric correspondence.

Because $S_2$ is a finite projective lattice, coefficientwise integrality at every cusp recognizes the integral operator. If two endomorphisms of $S_2$ agree after inverting a prime and have the same integral q-expansions, their difference has zero expansions and is zero.

Only finitely many coefficients are needed. If a connected component has stack degree $\mu$, a weight-two form is determined by coefficients through

$$
\left\lfloor\frac{\mu}{6}\right\rfloor
$$

in a genuine cusp uniformizer. Applying this bound to the images of a basis of $S_2$ proves equality of endomorphisms from finitely many coefficients. This is a verification method, not a replacement for the geometric construction: the correspondence and Néron extension explain why the operator acts on every other integral layer as well.

## 12. Exact calculations

The abstract lattice formulas are easy to misread without examples: a trivial component group can coexist with nontrivial specialization, and equal group orders can conceal different invariant factors. The calculations here test the signs, weights, Smith forms, ramified scaling, and cusp specialization formulas in the smallest nontrivial Deligne--Rapoport graphs.

### 12.1 One supersingular edge

Suppose the fine Deligne--Rapoport fiber has two components joined at one supersingular point. The graph is a tree, so

$$
H_1(G,\mathbf Z)=0,\qquad T_G=0,\qquad\Phi_J=0.
$$

The connected special fiber is

$$
\mathcal J_k^0\simeq J(C_F)\times J(C_V).
$$

This is compact-type reduction. The special curve is singular, but its Jacobian has good reduction: there is neither graph torus nor component defect. Hecke operators still act nontrivially on the two component Jacobians. Thus trivial component action does not mean trivial specialization.

### 12.2 Several unit edges

Let there be $r\ge2$ supersingular points. The graph lattice is

$$
A_{r-1}=\{(a_i)\in\mathbf Z^r:\sum_i a_i=0\}
$$

with the dot product. Choose the basis $f_i=e_i-e_r$, $1\le i<r$. The Gram matrix is

$$
Q=
\begin{pmatrix}
2&1&\cdots&1\\
1&2&\cdots&1\\
\vdots&\vdots&\ddots&\vdots\\
1&1&\cdots&2
\end{pmatrix}. \tag{12.1}
$$

Subtract the first row from each later row and then perform the corresponding column operations. Its Smith normal form is

$$
\operatorname{diag}(1,\ldots,1,r).
$$

Hence $\Phi_J\simeq\mathbf Z/r\mathbf Z$. The monodromy map is the inclusion represented by $Q$. If a Hecke operator permutes the supersingular edges by a permutation $\sigma$, it acts on $A_{r-1}$ by the permutation matrix. Its component action is trivial, because all coordinate permutations act trivially on the cyclic discriminant. If it also exchanges the two vertices, the component action is $-1$.

For $r=2$, $X=\mathbf Z(e_1-e_2)$ and $q=[2]$. The toric rank is one and $\Phi_J=\mathbf Z/2\mathbf Z$. Atkin--Lehner acts by $-1$ on the torus character lattice but trivially on the order-two component group. These statements are compatible: reduction modulo the discriminant can erase a nontrivial toric action.

### 12.3 Weighted quotient edges

Take three coarse nodes of lengths $2,3,6$. With basis $f_1=e_1-e_3$, $f_2=e_2-e_3$, the Gram matrix is

$$
Q=\begin{pmatrix}8&6\\6&9\end{pmatrix}. \tag{12.2}
$$

Its determinant is

$$
72-36=36,
$$

agreeing with

$$
3\cdot6+2\cdot6+2\cdot3=36.
$$

The greatest common divisor of all entries is $1$, so the Smith normal form is $\operatorname{diag}(1,36)$ and

$$
\Phi_J\simeq\mathbf Z/36\mathbf Z.
$$

By contrast, lengths $2,2,2$ give

$$
Q=\begin{pmatrix}4&2\\2&4\end{pmatrix},
$$

whose Smith form is $\operatorname{diag}(2,6)$. The component group is

$$
\mathbf Z/2\mathbf Z\oplus\mathbf Z/6\mathbf Z,
$$

not cyclic, although its order is $12$. This pair of examples shows why the weighted spanning-tree number alone is insufficient.

Under ramified base change of index $e$, every length is multiplied by $e$, so $q$ becomes $eq$. If $b_1=r-1$, then

$$
0\to X/eX\xrightarrow{q}
\Phi_{J_{K'}}\to\Phi_J\to0,
$$

and

$$
|\Phi_{J_{K'}}|=e^{r-1}|\Phi_J|.
$$

The sequence need not split. Hecke operators preserve it because they commute with the scaled monodromy map.

### 12.4 A specialization calculation with cusps

Let $c_F$ be a cusp specializing to $C_F$ and $c_V$ a cusp specializing to $C_V$. Then

$$
[c_F-c_V]\longmapsto[1,-1]
$$

in the vertex-divisor presentation. For the unit-edge graph with $r$ nodes, this class generates $\Phi_J\simeq\mathbf Z/r\mathbf Z$.

The Atkin--Lehner involution exchanges the two cusp types, so

$$
w_q[c_F-c_V]=[c_V-c_F]=-[c_F-c_V].
$$

This divisor calculation independently verifies (9.9). If a Hecke operator $T$ away from $q$ sends the cusp difference to $a$ times itself modulo principal and connected classes, then $\Phi(T)$ is multiplication by $a$ modulo $r$.

Over a nonclosed residue field, replace each cusp by the sum of its geometric Galois orbit. A single nonrational cusp contributes its residue degree to the intersection vector. Forgetting this factor can turn a generator into a non-generator and produces a nonequivariant component map.

## 13. Hypothesis ledger and failure modes

The main constructions live on several related spaces and use different hypotheses at good, level, and wild primes. This chapter gathers those boundaries before the final theorem so that none is lost in the synthesis. It also separates integral conclusions from rational decompositions, a distinction essential when component groups or congruence ideals are present.

### 13.1 Fine, stack, stable coarse, and regular coarse models

The fine rigidified Deligne--Rapoport model is regular and has two components with unit nodes. The modular stack has the same statement in a smooth chart. A stable coarse quotient has two principal components but can have thick nodes. Its minimal regular resolution inserts exceptional chains and therefore can have more than two components.

Every graph calculation must name the version being used. On the fine model, count unit supersingular edges. On the stable coarse model, retain their lengths and residue fields. On the regular coarse resolution, include every exceptional component in the intersection matrix or contract each valence-two chain back to its total metric length. Mixing the two-vertex incidence graph with the unweighted regular intersection matrix gives a false component group.

At wild stabilizers, especially in residue characteristics two and three, the tame invariant equation $XY=\pi^e$ cannot be assumed. One must calculate the actual invariant ring and resolve it. The fine and stack statements remain valid after rigidification; a blanket coarse regularity statement does not.

### 13.2 Characteristic, level, and separability

The integral Eichler--Shimura proof requires $p$ to be away from the fixed level so that the base modular curve has good reduction at $p$ and the auxiliary $p$-isogeny curve is the Deligne--Rapoport correspondence. At a prime already in the level, the operator is a $U_p$-type correspondence and its special cycle has a different moduli interpretation. Equation (7.1) must not be transferred to it without a separate calculation.

Frobenius is purely inseparable even though it is bijective on geometric points over a perfect field. Its degree is $p$, its differential is zero, and its norm--pullback composite is $[p]$. Set-theoretic counting would miss the second term of Eichler--Shimura.

The Tate-module monodromy formula is stated for $\ell\ne p$. At $\ell=p$, Kummer covers of the node are not finite étale and the filtration must be replaced by the connected--étale and crystalline structure of the $p$-divisible group. The graph component formula remains valid, but it is not a substitute for $p$-adic monodromy.

### 13.3 Integral versus rational decompositions

The graph cycle lattice, cotangent lattice, and Tate module are integral. A rationally invertible Hecke operator can have a nonsaturated image on any of them. A rational idempotent can require a denominator. Therefore:

- rational eigenspaces do not determine component kernels or cokernels;
- the order of a component group does not determine its invariant factors;
- an isogeny of generic Jacobians need not extend to a finite flat map of Néron models;
- a quotient by a Hecke ideal must be distinguished from the image of a rational projector; and
- a rank-two characteristic polynomial cannot be inferred until rank two has been proved.

The perfect component pairing controls saturation through (9.13), but it does not create a direct summand. Likewise, Eichler--Shimura gives an integral annihilating polynomial on a Hecke quotient but does not by itself prove that the quotient is free or faithful.

### 13.4 A dependency-closed main theorem

We collect the exact result established in this book.

**Theorem 13.1 (modular Jacobian, Néron, Hecke, and monodromy package).** Let $X/K$ be a smooth proper geometrically connected compactified modular curve over the function field of an excellent Dedekind scheme $S$, and let $J$ be its Jacobian.

1. Every finite modular Hecke correspondence $X\xleftarrow{\alpha}H\xrightarrow{\beta}X$ acts by $\beta_*\alpha^*$ on $J$ and extends uniquely to the Néron model $\mathcal J/S$. All generic correspondence relations and transpose identities hold integrally.
2. The action preserves $\mathcal J^0$, the finite étale component groups, the Lie and cotangent lattices, and every unramified localization. A normalized resolved closure calculates the component action by integral intersection matrices.
3. A cusp $c$ gives an Albanese map on the generic curve and a canonical extension from the smooth locus of a regular model. For horizontal divisors, specialization commutes with every Hecke correspondence, with vertical discrepancies removed by the separated Picard quotient.
4. At a prime $p$ away from the fixed level, the special fiber of the auxiliary $p$-isogeny correspondence is the reduced sum of Frobenius and Verschiebung branches. Consequently

   $$
   T_p=F_p+\langle p\rangle V_p,
   \qquad
   F_p^2-T_pF_p+p\langle p\rangle=0
   $$

   as endomorphisms of the good special Jacobian.
5. For $\ell\ne p$, arithmetic Frobenius on $T_\ell J$ satisfies the same quadratic polynomial over $\mathbf Z_\ell$. Every Hecke-stable quotient inherits it; a rank-two eigenspace has trace $T_p$ and determinant $p\langle p\rangle$ after its rank and freeness are independently established.
6. At a prime $q$ occurring once in the cyclic level, the fine Deligne--Rapoport model has two normalized components joined at the supersingular points. Its connected Néron fiber is an extension of the two component Jacobians by the graph torus. With $r$ geometric unit nodes,

   $$
   X^*(T)=A_{r-1},\qquad
   \Phi_J(k^s)\simeq\mathbf Z/r\mathbf Z.
   $$

   Coarse stabilizers replace unit edges by their exact lengths and $\Phi_J=X_G^\vee/qX_G$.
7. Hecke correspondences act on graph cycles by harmonic pull--push, transpose is adjoint for $q$, and the dual transpose map induces the component action. On the fine unit-edge component group, $w_q$ acts by $-1$.
8. For $\ell\ne q$, the Tate module at a semistable level prime has graded pieces

   $$
   X^\vee\otimes\mathbf Z_\ell(1),
   \quad T_\ell\!\left(\prod_vJ(Y_v)\right),
   \quad X\otimes\mathbf Z_\ell,
   $$

   and tame inertia is $1+t_\ell N$, with $N^2=0$ and outer graded map $q:X\to X^\vee$. This monodromy filtration is Hecke stable.
9. The cotangent lattice of the Néron model is the lattice of regular dualizing differentials on a regular modular model. At good level it is the integral weight-two cusp-form lattice and the Hecke action agrees with the q-expansion operator. At a level prime, the dualizing lattice remains canonical without assuming an unproved Hodge-line extension.

**Proof.** Items 1--2 are Sections 4 and 9. Item 3 is Section 5. Items 4--5 are Sections 6--7. Item 6 is Section 8. Item 7 is Section 9. Items 8 and 9 are Sections 10 and 11. Every use of a fine cover descends because the constructions are equivariant and can be checked faithfully flatly; every coarse calculation retains stabilizer lengths and residue descent. $\square$

## 14. Conclusion

### 14.1 The complete modular-Jacobian package

The modular Jacobian converts a moduli curve into an additive arithmetic object. Its Abel--Jacobi map turns points and cusps into divisor classes, its principal polarization turns transpose into adjunction, and its cotangent space turns weight-two cusp forms into invariant differentials. Finite isogeny correspondences then act by pullback followed by norm with a fixed, verifiable variance.

The Néron model carries this action across every closed point. Its universal property makes extension and algebra relations canonical. Its Picard description makes them computable. Horizontal divisors specialize to vertex divisors, vertical line bundles become intersection-matrix relations, and the quotient is the component group. Thus the abstract integral Hecke action and the explicit bad-fiber calculation are two views of the same homomorphism.

At a good prime $p$, the auxiliary $p$-isogeny curve is not smooth but is regular semistable. Its two characteristic-$p$ components are Frobenius and Verschiebung. Their multiplicity-one sum proves the integral Eichler--Shimura relation

$$
T_p=F_p+\langle p\rangle V_p.
$$

The Frobenius polynomial follows inside the special endomorphism ring and therefore on every prime-to-$p$ Tate lattice and every Hecke-stable quotient.

At a prime in the level, the same Deligne--Rapoport geometry controls degeneration of the modular curve itself. The normalized component Jacobians give the abelian part of the connected Néron fiber. Supersingular edges give its torus. Their weighted cycle pairing gives both the finite component group and tame monodromy. Hecke pull--push is adjoint on this lattice, so it respects components, monodromy, and the discriminant pairing simultaneously.

### 14.2 The arithmetic meaning of the package

The resulting structure is integral at every stage:

$$
\begin{array}{c}
\text{modular correspondences}\\
\downarrow\\
\text{endomorphisms of }\mathcal J\\
\downarrow\\
\mathcal J_k^0,\ \Phi_J,\ \omega_{\mathcal J/R},\ T_\ell J\\
\downarrow\\
\text{Frobenius polynomials and monodromy lattices}.
\end{array}
$$

No rational projector is needed to define the arrows, and no graph picture is used without its lengths, multiplicities, and descent action. The good-prime relation supplies traces and determinants for Galois extraction. The bad-prime graph supplies component and inertia data for specialization arguments. The Albanese map connects both to actual modular points and cusps.

These are precisely the features that later arithmetic arguments need from a modular Jacobian: a canonical integral Hecke action, computable component groups, Hecke-equivariant monodromy, compatible Albanese specialization, and an integral Eichler--Shimura relation whose hypotheses and variance are explicit.
