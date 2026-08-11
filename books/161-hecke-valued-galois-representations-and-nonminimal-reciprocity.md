# Hecke-Valued Galois Representations and Nonminimal Reciprocity

## Contents

1. [From eigenpackets to one family](#1-from-eigenpackets-to-one-family)
   - [The gluing problem](#11-the-gluing-problem)
   - [Why traces can cross congruences](#12-why-traces-can-cross-congruences)
   - [The three conclusions](#13-the-three-conclusions)
   - [The logical route](#14-the-logical-route)
2. [The clean global datum](#2-the-clean-global-datum)
   - [Fields, coefficients, and Frobenius](#21-fields-coefficients-and-frobenius)
   - [The residual representation](#22-the-residual-representation)
   - [The automorphic level and its selected types](#23-the-automorphic-level-and-its-selected-types)
   - [The coefficient-prime condition](#24-the-coefficient-prime-condition)
   - [What clean means](#25-what-clean-means)
3. [Localized Hecke orders](#3-localized-hecke-orders)
   - [The faithful image order](#31-the-faithful-image-order)
   - [Completion is already present](#32-completion-is-already-present)
   - [Generic branches and reducedness](#33-generic-branches-and-reducedness)
   - [Trace orders and enlarged orders](#34-trace-orders-and-enlarged-orders)
   - [A model crossing](#35-a-model-crossing)
4. [Representations on the generic branches](#4-representations-on-the-generic-branches)
   - [Automorphic points of the order](#41-automorphic-points-of-the-order)
   - [Branchwise attachment](#42-branchwise-attachment)
   - [A common determinant](#43-a-common-determinant)
   - [Residual compatibility of the branches](#44-residual-compatibility-of-the-branches)
   - [The product representation](#45-the-product-representation)
5. [Frobenius density and interpolation](#5-frobenius-density-and-interpolation)
   - [The exact density statement](#51-the-exact-density-statement)
   - [Density for continuous class functions](#52-density-for-continuous-class-functions)
   - [Order-valued traces](#53-order-valued-traces)
   - [Characteristic polynomials over the order](#54-characteristic-polynomials-over-the-order)
   - [Why good-prime identities alone were not existence](#55-why-good-prime-identities-alone-were-not-existence)
6. [Trace-coordinate descent over an order](#6-trace-coordinate-descent-over-an-order)
   - [The descent theorem](#61-the-descent-theorem)
   - [A residual matrix basis](#62-a-residual-matrix-basis)
   - [Trace coordinates](#63-trace-coordinates)
   - [The rank-four algebra](#64-the-rank-four-algebra)
   - [Azumaya splitting](#65-azumaya-splitting)
   - [Continuity, determinant, and uniqueness](#66-continuity-determinant-and-uniqueness)
7. [Construction of the Hecke-valued representation](#7-construction-of-the-hecke-valued-representation)
   - [The construction theorem](#71-the-construction-theorem)
   - [Good-place reciprocity](#72-good-place-reciprocity)
   - [Minimality of the trace coefficient ring](#73-minimality-of-the-trace-coefficient-ring)
   - [Change of coefficients](#74-change-of-coefficients)
   - [Semisimplification and extensions](#75-semisimplification-and-extensions)
8. [Deformation conditions and a generic-point criterion](#8-deformation-conditions-and-a-generic-point-criterion)
   - [Represented local conditions](#81-represented-local-conditions)
   - [The reduced-order factorization lemma](#82-the-reduced-order-factorization-lemma)
   - [Application to all Artinian quotients](#83-application-to-all-artinian-quotients)
   - [Framed and unframed formulations](#84-framed-and-unframed-formulations)
   - [The nilpotent warning](#85-the-nilpotent-warning)
9. [The coefficient prime](#9-the-coefficient-prime)
   - [Finite flatness is integral](#91-finite-flatness-is-integral)
   - [Comparison of branch lattices](#92-comparison-of-branch-lattices)
   - [Finite-flat factorization](#93-finite-flat-factorization)
   - [Every Artinian quotient](#94-every-artinian-quotient)
   - [The exceptional coefficient-prime range](#95-the-exceptional-coefficient-prime-range)
10. [Local types away from the coefficient prime](#10-local-types-away-from-the-coefficient-prime)
    - [Type occurrence and Galois parameters](#101-type-occurrence-and-galois-parameters)
    - [Principal components](#102-principal-components)
    - [Special components](#103-special-components)
    - [Tame dihedral components](#104-tame-dihedral-components)
    - [Orderings, signs, and companion lattices](#105-orderings-signs-and-companion-lattices)
11. [Inertia in the Hecke-valued family](#11-inertia-in-the-hecke-valued-family)
    - [Prime-to-coefficient rigidity](#111-prime-to-coefficient-rigidity)
    - [The finite-type inertia theorem](#112-the-finite-type-inertia-theorem)
    - [The ordered principal inertia theorem](#113-the-ordered-principal-inertia-theorem)
    - [Base change to Artinian coefficients](#114-base-change-to-artinian-coefficients)
    - [What inertia does not determine](#115-what-inertia-does-not-determine)
12. [Monodromy over the Hecke order](#12-monodromy-over-the-hecke-order)
    - [The special branch formula](#121-the-special-branch-formula)
    - [Construction of the universal monodromy operator](#122-construction-of-the-universal-monodromy-operator)
    - [Frobenius and the invariant line](#123-frobenius-and-the-invariant-line)
    - [Vanishing after reduction](#124-vanishing-after-reduction)
    - [Monodromy ideals](#125-monodromy-ideals)
13. [Nonminimal reciprocity](#13-nonminimal-reciprocity)
    - [The global nonminimal deformation datum](#131-the-global-nonminimal-deformation-datum)
    - [The reciprocity map](#132-the-reciprocity-map)
    - [Surjectivity](#133-surjectivity)
    - [The main nonminimal theorem](#134-the-main-nonminimal-theorem)
    - [Compatibility with inner-form comparison](#135-compatibility-with-inner-form-comparison)
14. [Minimal and nonminimal levels](#14-minimal-and-nonminimal-levels)
    - [Two distinct deformation problems](#141-two-distinct-deformation-problems)
    - [When a comparison map exists](#142-when-a-comparison-map-exists)
    - [Level raising](#143-level-raising)
    - [Level lowering](#144-level-lowering)
    - [Faithfulness boundaries](#145-faithfulness-boundaries)
15. [Exceptional primes and failure modes](#15-exceptional-primes-and-failure-modes)
    - [Residual characteristic two](#151-residual-characteristic-two)
    - [Residual characteristics three and five](#152-residual-characteristics-three-and-five)
    - [Scalar and reducible residual systems](#153-scalar-and-reducible-residual-systems)
    - [Nonreduced generic fibers](#154-nonreduced-generic-fibers)
    - [Primitive wild types and missing local models](#155-primitive-wild-types-and-missing-local-models)
16. [The theorem package and dependency audit](#16-the-theorem-package-and-dependency-audit)
    - [The complete theorem](#161-the-complete-theorem)
    - [Exact dependency ledger](#162-exact-dependency-ledger)
    - [Hypothesis ledger](#163-hypothesis-ledger)
    - [Conclusion](#164-conclusion)

## 1. From eigenpackets to one family

### 1.1 The gluing problem

At a characteristic-zero automorphic eigenpacket, weight-two reciprocity produces a representation

$$
\rho_x:G_F\longrightarrow \operatorname{GL}_2(E_x).
$$

At a good finite place $v$, its geometric-Frobenius polynomial is

$$
X^2-a_v(x)X+q_v s_v(x).
\tag{1.1}
$$

This is a pointwise statement. A congruence problem asks for more. Several eigenpackets can have the same residual system, and the localized Hecke order remembers how their integral branches meet. We seek one representation whose coefficients lie in that order and whose specialization at every characteristic-zero branch is the attached representation.

The desired conclusion is not obtained by writing the matrices $\rho_x(g)$ next to one another. Their product lies over a product of fields, whereas the Hecke order is a local lattice inside that product. A matrix entry can be integral on every branch without belonging to the smaller order. Moreover the bases used to write the branch representations are unrelated. Only conjugacy-invariant data can be compared before a common basis has been constructed.

Trace is the decisive invariant. The good Hecke operators interpolate the traces of a dense collection of Frobenius classes. Density then forces the trace of every Galois element to lie in the Hecke order. Residual absolute irreducibility upgrades these scalar identities to matrices: four residual group matrices span the full matrix algebra, and the trace pairing expresses every other group matrix in their coordinates. This is the bridge from pointwise reciprocity to an order-valued family.

### 1.2 Why traces can cross congruences

Suppose two eigenpackets $x_1,x_2$ are congruent. Their coefficientwise product representation has trace

$$
g\longmapsto
(\operatorname{tr}\rho_{x_1}(g),\operatorname{tr}\rho_{x_2}(g)).
$$

The normalization of the Hecke order separates the two coordinates, but the order itself imposes congruence relations between them. At good Frobenius elements those relations hold because both coordinates arise from the single Hecke operator $T_v$. Continuity and Frobenius density show that they hold for every $g$.

This argument interpolates the character, not a preferred basis. That distinction is essential. A branch representation may be conjugated without altering a Hecke value. It is residual absolute irreducibility that later makes the character strong enough to choose a common rank-two module over the local order.

There are two genuine obstructions. If the residual representation is reducible, trace does not remember extension classes and need not determine a free rank-two realization. If the generic Hecke algebra is nonreduced, evaluation at its field-valued points cannot see nilpotent directions. Both obstructions will remain explicit throughout the book.

### 1.3 The three conclusions

The construction has three outputs.

First, it gives a continuous representation

$$
\rho_{\mathbb T}:G_{F,S}\longrightarrow
\operatorname{GL}_2(\mathbb T)
\tag{1.2}
$$

over a localized complete Hecke order $\mathbb T$, with the prescribed determinant and good Frobenius polynomials.

Second, it proves that every Artinian quotient of (1.2) satisfies the local deformation conditions named by the automorphic datum. At places above the coefficient prime this means finite flatness, not unramifiedness. At the fixed nonminimal places it means one of the controlled principal, special, or tame dihedral conditions, with all orderings, signs, and finite descent data retained.

Third, the representation defines a surjective reciprocity map

$$
R_{\mathcal D}\twoheadrightarrow\mathbb T
\tag{1.3}
$$

from the global deformation ring for that nonminimal datum. Surjectivity comes from the construction of $\mathbb T$ by good Hecke traces; it does not imply that (1.3) is injective. An equality of rings requires the numerical and patching arguments of later stages.

### 1.4 The logical route

The proof order prevents circular reasoning.

1. The acting Hecke order and its reduced generic branches are defined without a Galois representation over the order.
2. Weight-two reciprocity attaches a representation separately to every generic branch.
3. Frobenius density interpolates their traces into the order.
4. Trace-coordinate descent constructs the order-valued representation.
5. Representability and reducedness promote generic local compatibility to factorization through the exact integral local conditions.
6. Only then does universality produce (1.3).

No local condition is inferred merely from a conductor, and no order equality is inferred merely from equality after inverting the coefficient uniformizer. The integral level-change theorem is used precisely where it identifies faithful orders or supplies saturated type lattices.

## 2. The clean global datum

### 2.1 Fields, coefficients, and Frobenius

Let $F$ be a totally real field. Fix an odd prime $\ell$ and a finite extension $E/\mathbf Q_\ell$ with ring of integers $\mathcal O$, uniformizer $\varpi$, and finite residue field $k$. We enlarge $E$ at the outset so that $k$ is the residue field of the selected Hecke maximal ideal and so that every finite character and selected type lattice is defined over $\mathcal O$.

Let $S$ be a finite set containing the archimedean places, the places above $\ell$, the ramification of the residual representation and determinant, every level place, and every place at which a nonminimal condition is imposed. Write

$$
G_{F,S}=\operatorname{Gal}(F_S/F)
$$

for the Galois group of the maximal extension unramified outside $S$.

At a finite place $v\notin S$ we use geometric Frobenius $\Phi_v$. The cyclotomic character is normalized by

$$
\chi_\ell(\Phi_v)=q_v^{-1}.
\tag{2.1}
$$

Thus the untwisted weight-two cohomological representation has determinant $q_v$ in the trivial central-character case. Arithmetic Frobenius is $\Phi_v^{-1}$; its polynomial is obtained by inverting the roots and is not (1.1).

### 2.2 The residual representation

Fix a continuous representation

$$
\bar\rho:G_{F,S}\longrightarrow\operatorname{GL}_2(k)
\tag{2.2}
$$

which is absolutely irreducible. This hypothesis has four separate consequences.

First, $\operatorname{End}_{k[G_{F,S}]}(k^2)=k$, so the ordinary global deformation functor is representable. Second, equality of residual traces determines the residual semisimplification, which is already irreducible. Third, Burnside density gives

$$
k[\bar\rho(G_{F,S})]=M_2(k).
\tag{2.3}
$$

Fourth, two integral lattices in the same characteristic-zero representation whose reductions realize (2.2) differ only by an integral change of basis after a homothety. Each use will be made separately; the phrase “non-Eisenstein” is not used as a substitute for (2.2).

Fix also a determinant

$$
\delta:G_{F,S}\longrightarrow\mathcal O^\times
\tag{2.4}
$$

lifting $\det\bar\rho$. In the weight-two normalization it is

$$
\delta=\chi_\ell^{-1}\eta,
\tag{2.5}
$$

where $\eta$ is the finite central-component character. At every good place,

$$
\delta(\Phi_v)=q_v s_v.
\tag{2.6}
$$

The determinant is part of the deformation datum, not an invariant to be reconstructed later from traces. This is especially important in residual characteristic two, where the derivative of determinant is not modeled by simply discarding a scalar line.

### 2.3 The automorphic level and its selected types

Choose a proper weight-two quaternionic Shimura-curve realization, or a modular-curve realization in the corresponding established range. At each finite nonminimal place $w\in S$ away from $\ell$, choose one of the integral local data constructed previously:

- an ordered principal datum, including its two characters and its line ordering when reduction does not distinguish them;
- a special datum, including its sign, scalar finite inertia character when present, and the named closure of the nonzero-monodromy locus;
- a depth-zero or positive-depth tame dihedral datum, including the quadratic extension, inducing character up to the stated equivalence, and Frobenius intertwiner.

Each datum includes a primary compact type lattice, its companion lattice, a perfect adjoint pairing, and a represented local deformation condition. Primitive wild supercuspidal types are not silently added to this list.

The global automorphic module is cut out integrally by the corresponding type Hom, sign-new, or saturated multiplicity construction. At a changed Iwahori place the old image is required to be saturated and the new quotient torsion free. When an inner form is used, the localized curve-new and definite faithful orders are identified by the integral level-change and Jacquet--Langlands comparison theorem, with its normalizations unchanged.

### 2.4 The coefficient-prime condition

At every $w\mid\ell$, the residual restriction is finite flat and the determinant is the required cyclotomic-central character. The strongest clean form assumes:

$$
\ell>2,
\qquad F_w/\mathbf Q_\ell\text{ unramified},
\qquad\text{Hodge type }(0,1),
\tag{2.7}
$$

together with an integral weight-two realization datum for every characteristic-zero automorphic branch. Under these hypotheses the finite-flat local condition is represented and, in the fixed-determinant rank-two case, the framed ring is formally smooth of the dimension established by the finite-flat theory.

Only representedness and stability under coefficient quotients are needed for the factorization argument. Formal smoothness becomes important in later numerical comparisons, but it is not used to construct $\rho_{\mathbb T}$.

### 2.5 What clean means

The adjective **clean** will mean that all of the following hold.

1. The Hecke module is finite free over $\mathcal O$, the chosen away operators commute, and the localized acting order is faithful.
2. Its characteristic-zero Hecke action is semisimple, so the generic order is reduced.
3. Every generic branch is a noncharacter parallel-weight-two packet in the geometric attachment range.
4. The residual representation (2.2) is absolutely irreducible and is the residual representation of every branch.
5. The determinant normalization (2.5) is common to all branches.
6. Every bad-place local--global comparison uses a verified good, semistable, finite-descent, or tame-dihedral model with its Frobenius return data.
7. Every integral type selection is saturated, and every needed inner-form comparison identifies faithful orders rather than merely rational packet spaces.
8. The coefficient-prime integral realization datum is present.

For the full one-prime nonminimal theorem supplied by integral level change, we additionally retain $\ell\ge7$, neatness or prime-to-$\ell$ descent, a non-Eisenstein adjoint-stable maximal ideal, and the nonexceptional congruences required to separate signs. Some portions of the construction need less; Chapter 15 records exactly where the stronger restrictions enter.

## 3. Localized Hecke orders

### 3.1 The faithful image order

Let $M$ be the selected finite-free $\mathcal O$-module of automorphic forms or cohomological multiplicities. Fix the commuting away-from-$S$ operators $T_v$ and $S_v^{\pm1}$. The **acting Hecke algebra** is the image

$$
\mathbb T^{\mathrm{raw}}
=\mathcal O[T_v,S_v^{\pm1}:v\notin S]
\subseteq\operatorname{End}_{\mathcal O}(M).
\tag{3.1}
$$

It is finite free over $\mathcal O$: it is finite because it is a submodule of the finite free endomorphism module, and torsion free because it is an actual submodule. Let $\mathfrak m$ be the maximal ideal giving (2.2), and put

$$
\mathbb T=(\mathbb T^{\mathrm{raw}})_{\mathfrak m}.
\tag{3.2}
$$

The localized module $M_{\mathfrak m}$ is faithful over $\mathbb T$. This says that an element of the order is detected on the automorphic module. It does not say that $M_{\mathfrak m}$ is free over $\mathbb T$, that the order is Gorenstein, or that its special-fiber action is faithful after tensoring with $k$.

We fix the central character, so $q_vS_v=\delta(\Phi_v)$ is a scalar in $\mathcal O$. Consequently

$$
\mathbb T=\mathcal O[T_v:v\notin S].
\tag{3.3}
$$

If the central operator is allowed to vary, determinants must be retained among the generators and the deformation problem must permit the matching determinant variation.

### 3.2 Completion is already present

Because $\mathbb T$ is finite over the complete DVR $\mathcal O$, it is a complete Noetherian local ring for its maximal-ideal topology. More explicitly, if $\mathfrak n$ is its maximal ideal, then

$$
\mathbb T\xrightarrow{\sim}\varprojlim_r\mathbb T/\mathfrak n^r.
\tag{3.4}
$$

Thus “completed localized Hecke order” names the topology and deformation-theoretic category; it does not create a larger ring at this fixed level. The distinction matters when comparing with genuinely infinite inverse limits. No deep-level inverse limit is imported here.

The residue field is $\mathbb T/\mathfrak n=k$ after the coefficient enlargement already made. The images of the $T_v$ are the residual traces

$$
T_v\bmod\mathfrak n
=\operatorname{tr}\bar\rho(\Phi_v).
\tag{3.5}
$$

### 3.3 Generic branches and reducedness

Set

$$
\mathbb T_E=\mathbb T\otimes_{\mathcal O}E.
$$

Under the clean semisimplicity hypothesis, this is a finite reduced commutative $E$-algebra. Hence

$$
\mathbb T_E\simeq\prod_{i=1}^r E_i
\tag{3.6}
$$

for finite extensions $E_i/E$. The projections $\lambda_i:\mathbb T\to E_i$ are the generic eigencharacters. Since $\mathbb T$ is integral over $\mathcal O$ and every Hecke eigenvalue is integral, $\lambda_i(\mathbb T)$ lies in the valuation ring $\mathcal O_i$ of $E_i$.

The natural map

$$
\mathbb T\longrightarrow\prod_i\mathcal O_i
\tag{3.7}
$$

is injective. Indeed $\mathbb T$ is $\mathcal O$-torsion free, so it injects into $\mathbb T_E$, and (3.6) is faithful. The product on the right is a normalization large enough to separate the branches. The order $\mathbb T$ remembers their congruence gluing.

Reducedness of the generic fiber must be proved from the characteristic-zero automorphic action; it is not a formal consequence of finite flatness. In the clean Shimura-curve setting the commuting Hecke action is semisimple on the characteristic-zero packet decomposition. The faithful image therefore embeds into a product of packet fields and is reduced.

Here is the argument in detail. Over a splitting field $L/E$, the selected characteristic-zero automorphic module decomposes as

$$
M_L=\bigoplus_x M_L[x],
\tag{3.10}
$$

where $x$ ranges over the finitely many simultaneous Hecke characters in the localized support. Every $T_v$ acts on $M_L[x]$ by the scalar $a_v(x)$. Thus the image of $\mathbb T_E\otimes_EL$ is contained in

$$
\prod_xL
$$

acting diagonally on the decomposition. It is reduced. Faithfulness of $M_E$ implies that $\mathbb T_E$ injects into this image after scalar extension, and faithful flatness of $L/E$ descends reducedness.

This proof would fail if (3.10) were only a generalized-eigenspace decomposition with nilpotent Hecke action inside a characteristic-zero block. The clean automorphic packet decomposition rules that out. It does not rule out generalized residual eigenspaces: several distinct $x$ can reduce to the same $\mathfrak m$, and their integral gluing can make $\mathbb T/\varpi\mathbb T$ nonreduced.

### 3.4 Trace orders and enlarged orders

The construction naturally lands in the closed algebra generated by Galois traces. Define

$$
\mathbb T^{\mathrm{tr}}
=\overline{\mathcal O[T_v:v\notin S]}\subseteq\mathbb T.
\tag{3.8}
$$

At finite level the algebra is already finite and closed. Under (3.3), $\mathbb T^{\mathrm{tr}}=\mathbb T$. If extra operators $U_w$, diamond operators, orientation operators, or type endomorphisms have been adjoined, equality need not hold. Such an enlarged order may carry information not determined by a two-dimensional Galois character.

The correct statement in that case is a representation over $\mathbb T^{\mathrm{tr}}$. It extends to the enlarged order by scalar extension, but scalar extension does not prove that the larger order is the minimal coefficient ring or that a deformation map surjects onto it. Any claim for the full enlarged order therefore requires an independent generation theorem.

### 3.5 A model crossing

Let

$$
A=\{(a,b)\in\mathcal O\times\mathcal O:a\equiv b\pmod\varpi\}.
\tag{3.9}
$$

Then $A$ is local, finite free, and reduced, while

$$
A_E=E\times E.
$$

The two generic branches meet at one residual point. A pair $(x,y)\in\mathcal O^2$ is integral on both branches but belongs to $A$ only if $x\equiv y\pmod\varpi$. Thus branchwise integrality is weaker than order-valuedness.

If a dense set of Frobenius traces belongs to $A$, continuity forces every trace pair to satisfy the congruence. The descent theorem then constructs matrices over $A$, provided the common residual representation is absolutely irreducible. This toy order captures the exact role played by Frobenius density in the general argument.

It also displays why bases cannot be glued coordinatewise. Let $\rho_1$ and $\rho_2$ be integral lifts of the same absolutely irreducible residual representation, and conjugate $\rho_2$ by a matrix in $\operatorname{GL}_2(E)$ which does not preserve its chosen lattice. The pairs of individual matrix entries need not lie in $A$, even though

$$
(\operatorname{tr}\rho_1(g),\operatorname{tr}\rho_2(g))\in A
$$

for every $g$. Trace descent changes the second basis simultaneously for all $g$. Absolute irreducibility ensures that this one change of basis repairs every matrix entry; choosing a separate conjugator for each group element would destroy multiplication.

## 4. Representations on the generic branches

### 4.1 Automorphic points of the order

Every projection in (3.6) occurs in the characteristic-zero automorphic module. This is a consequence of faithfulness: a simple factor of a finite reduced algebra acting faithfully must occur in the module. Thus each $\lambda_i$ determines a noncharacter weight-two eigenpacket $\Pi_i$ with

$$
a_v(\Pi_i)=\lambda_i(T_v),
\qquad
s_v(\Pi_i)=s_v
\quad(v\notin S).
\tag{4.1}
$$

The selected type Hom or new quotient used to define $M$ ensures that $\Pi_i$ has the prescribed local occurrence at every nonminimal place. This is precisely where saturation and integral order comparison matter. A rational type projector with a nonunit denominator would not justify the same assertion about every branch of the integral order.

### 4.2 Branchwise attachment

The weight-two attachment theorem gives, for each $i$, a continuous semisimple representation

$$
\rho_i:G_{F,S}\longrightarrow\operatorname{GL}_2(E_i)
\tag{4.2}
$$

such that for $v\notin S$,

$$
\det(X-\rho_i(\Phi_v))
=X^2-\lambda_i(T_v)X+q_vs_v.
\tag{4.3}
$$

The representation is unramified at $v$. At a bad place away from $\ell$, the verified local--global compatibility theorem identifies its Frobenius-semisimple Weil--Deligne parameter, not merely its conductor. At a coefficient-prime place, the integral realization datum supplies a stable lattice all of whose finite coefficient quotients are finite flat.

Semisimplification in (4.2) is harmless because its residual representation will be absolutely irreducible. A reducible characteristic-zero representation could still have irreducible reduction only after choosing a lattice? It cannot: a stable characteristic-zero line would intersect a stable lattice in a nonzero proper residual submodule after saturation. Hence every $\rho_i$ is itself absolutely irreducible.

### 4.3 A common determinant

The determinant formula in weight-two cohomology gives

$$
\det\rho_i=\delta_{E_i}
\tag{4.4}
$$

for every $i$. This equality is global. It follows from the factored cohomological pairing and the common central-component character, not from matching (4.3) at a finite list of places.

At good places it gives the constant coefficient $q_vs_v$. Conversely, the good constant coefficients and density would identify two already constructed continuous determinant characters. We do not use that converse to manufacture the determinant: fixing (2.4) keeps the deformation problem and every local condition well typed from the beginning.

### 4.4 Residual compatibility of the branches

Choose a $G_{F,S}$-stable $\mathcal O_i$-lattice $L_i\subset E_i^2$. Its residual semisimplification has good Frobenius traces equal to (3.5) and determinant equal to $\det\bar\rho$. Density in finite quotients and character rigidity therefore give

$$
(L_i/\mathfrak m_iL_i)^{\mathrm{ss}}\simeq\bar\rho\otimes_k k_i.
\tag{4.5}
$$

After enlarging the common residue field, we suppress $k_i/k$. Since the right side is irreducible of dimension two, the left side cannot be a nontrivial extension with more than one composition factor. Thus the actual reduction is isomorphic to $\bar\rho$.

Choose such an isomorphism and a basis lifting it. Then

$$
\rho_i:G_{F,S}\longrightarrow\operatorname{GL}_2(\mathcal O_i)
\tag{4.6}
$$

reduces to the fixed matrix representation (2.2). Different choices are strictly conjugate after a scalar normalization. This compatibility of residual bases is what permits one trace-coordinate construction for all branches.

The residual character comparison used here can be proved without appealing to a characteristic-zero uniqueness statement. For every finite quotient $\Gamma$ of $G_{F,S}$, Theorem 5.1 below realizes each conjugacy class of $\Gamma$ by a good Frobenius class. Hence the residual traces of the branch lattice and of $\bar\rho$ agree on every element of $\Gamma$. The absolutely irreducible character-rigidity theorem identifies their semisimplifications. Passing through the finite quotient cut out by both residual actions gives (4.5). This proof also explains why it is not enough to compare Frobenius at a finite list of good places.

There is a harmless scalar ambiguity in the residual identification. Once a matrix basis for $\bar\rho$ is fixed, any two identifications differ by an element centralizing $\bar\rho(G_{F,S})$, hence by a scalar. Lifting that scalar and rescaling the branch basis makes all chosen reductions literally equal to the fixed matrices. The trace-coordinate algebra is independent of the lift of this scalar.

### 4.5 The product representation

Let

$$
Q=\mathbb T_E=\prod_iE_i.
$$

Taking the product of (4.2) gives

$$
\rho_Q:G_{F,S}\longrightarrow\operatorname{GL}_2(Q).
\tag{4.7}
$$

This notation means a tuple of matrices, one on each factor. Its trace and determinant are continuous functions

$$
t_Q:G_{F,S}\to Q,
\qquad d_Q:G_{F,S}\to Q^\times.
\tag{4.8}
$$

At good Frobenius elements,

$$
t_Q(\Phi_v)=T_v\in\mathbb T,
\qquad
d_Q(\Phi_v)=q_vS_v=\delta(\Phi_v)\in\mathcal O^\times.
\tag{4.9}
$$

The matrices in (4.7) do not yet lie in $M_2(\mathbb T)$. The next two chapters turn (4.9) into precisely that conclusion.

## 5. Frobenius density and interpolation

### 5.1 The exact density statement

We use the following finite-quotient consequence of Chebotarev.

**Theorem 5.1 (Frobenius selection).** Let $L/F$ be a finite Galois extension and let $C$ be a conjugacy class in $\operatorname{Gal}(L/F)$. Outside any prescribed finite set of places, there are infinitely many places $v$ unramified in $L$ whose geometric Frobenius class is $C$.

The density theorem already proved for finite Galois extensions gives positive lower Dirichlet density for the corresponding arithmetic class. Inversion carries an arithmetic conjugacy class to the desired geometric class and preserves positivity. Removing finitely many places changes neither positivity nor infinitude. This proves the stated form.

For the present construction, infinitude is more than enough. What matters is that every conjugacy class in every finite quotient of $G_{F,S}$ is represented by a good Frobenius class.

### 5.2 Density for continuous class functions

**Lemma 5.2.** Let $A$ be a Hausdorff topological ring and let

$$
f:G_{F,S}\longrightarrow A
$$

be a continuous class function. If $f(\Phi_v)$ belongs to a closed subset $C\subseteq A$ for every $v$ outside a finite set, then $f(g)\in C$ for every $g\in G_{F,S}$.

**Proof strategy.** Approximate $g$ in successively smaller finite quotients by conjugates of Frobenius. Conjugacy causes no ambiguity because $f$ is a class function.

**Proof.** Choose a descending sequence of open normal subgroups $U_n$ with intersection $1$. Let $L_n/F$ be the finite Galois extension cut out by $U_n$. The image of $g$ in $G_{F,S}/U_n$ has a conjugacy class. By Theorem 5.1, choose $v_n$ outside the prescribed set whose geometric Frobenius has that class. There is $h_n\in G_{F,S}$ such that

$$
h_n\Phi_{v_n}h_n^{-1}\in gU_n.
$$

Hence $h_n\Phi_{v_n}h_n^{-1}\to g$. Since $f$ is conjugacy invariant,

$$
f(h_n\Phi_{v_n}h_n^{-1})=f(\Phi_{v_n})\in C.
$$

Continuity and closedness give $f(g)\in C$. $\square$

The countable sequence is convenient because $G_{F,S}$ is second countable. A directed neighborhood argument gives the same conclusion without this observation.

### 5.3 Order-valued traces

The finite free $\mathcal O$-module $\mathbb T$ is closed in the finite-dimensional $E$-space $Q$. Indeed a finite lattice in a nonarchimedean vector space is complete, and a complete subgroup of a Hausdorff topological group is closed.

Apply Lemma 5.2 to $t_Q$. Equation (4.9) gives

$$
t_Q(g)\in\mathbb T
\qquad(g\in G_{F,S}).
\tag{5.1}
$$

Write this order-valued trace as $t(g)$. Similarly $d_Q=\delta_Q$ on a dense set of Frobenius classes, so continuity gives

$$
d_Q(g)=\delta(g)\in\mathcal O^\times
\qquad(g\in G_{F,S}).
\tag{5.2}
$$

The determinant conclusion could also be read directly from (4.4). The density proof confirms that all normalizations agree.

### 5.4 Characteristic polynomials over the order

For every $g\in G_{F,S}$, the product representation satisfies

$$
\rho_Q(g)^2-t(g)\rho_Q(g)+\delta(g)I=0
\tag{5.3}
$$

componentwise. Thus its characteristic polynomial has coefficients in $\mathbb T$:

$$
P_g(X)=X^2-t(g)X+\delta(g).
\tag{5.4}
$$

The functions $t$ and $\delta$ obey every two-dimensional character identity because they do so after the injective map $\mathbb T\hookrightarrow Q$. For example,

$$
t(gh)=t(hg),
\tag{5.5}
$$

and, using Cayley--Hamilton for $h$,

$$
t(g)t(h)=t(gh)+\delta(h)t(gh^{-1}).
\tag{5.6}
$$

These identities show that $(t,\delta)$ is a two-dimensional determinant law over $\mathbb T$. We will not invoke an abstract realization theorem. Instead we construct its matrix realization explicitly from trace coordinates.

### 5.5 Why good-prime identities alone were not existence

Equation (4.9) names only a dense family of scalars. It does not by itself give a homomorphism into $\operatorname{GL}_2(\mathbb T)$. Even (5.4) is still a character-valued statement. When the residual character is reducible, several nonisomorphic extensions have the same polynomials $P_g$.

The missing step is a matrix algebra over $\mathbb T$. Residual absolute irreducibility forces the residual group algebra to fill $M_2(k)$. Four group elements then provide coordinates in which all multiplication constants are traces. Those constants already lie in $\mathbb T$ by (5.1). This is the precise mechanism of descent.

## 6. Trace-coordinate descent over an order

### 6.1 The descent theorem

We isolate the algebraic result in a form reusable beyond automorphic applications.

**Theorem 6.1 (order-valued Carayol descent).** Let $(T,\mathfrak n,k)$ be a complete Noetherian local ring which is finite flat over a complete DVR $\mathcal O$. Assume $T_E=T\otimes_{\mathcal O}E$ is reduced, and write $T_E=\prod_iE_i$. Let $G$ be a compact topological group and

$$
\rho_Q:G\longrightarrow\operatorname{GL}_2(T_E)
$$

be continuous. Suppose:

1. $t(g)=\operatorname{tr}\rho_Q(g)$ belongs to $T$ for every $g$;
2. $d(g)=\det\rho_Q(g)$ belongs to $T^\times$ for every $g$;
3. the reductions of stable branch lattices give one fixed absolutely irreducible representation $\bar\rho:G\to\operatorname{GL}_2(k)$.

Then there is a continuous representation

$$
\rho_T:G\longrightarrow\operatorname{GL}_2(T)
$$

with trace $t$, determinant $d$, and reduction $\bar\rho$. Its scalar extension to each $E_i$ is isomorphic to the corresponding branch of $\rho_Q$. After the residual basis is fixed, any two such representations are strictly conjugate over $T$.

The proof occupies the next five sections. Its hypotheses differ slightly from the usual descent theorem: the initial representation lives over a reduced product of fields rather than a larger local ring. Trace coordinates remove that difference.

### 6.2 A residual matrix basis

By absolute irreducibility and Burnside density,

$$
k[\bar\rho(G)]=M_2(k).
$$

Choose $g_1,g_2,g_3,g_4\in G$ such that

$$
\bar x_i=\bar\rho(g_i)
\quad(1\le i\le4)
\tag{6.1}
$$

form a $k$-basis of $M_2(k)$. Put $x_i=\rho_Q(g_i)$.

Consider the trace Gram matrix

$$
\Gamma=(t(g_ig_j))_{i,j}=(\operatorname{tr}(x_ix_j))_{i,j}\in M_4(T).
\tag{6.2}
$$

The pairing $(x,y)\mapsto\operatorname{tr}(xy)$ on $M_2(k)$ is perfect in every characteristic. Since the $\bar x_i$ form a basis, $\det\bar\Gamma\ne0$. Therefore

$$
\det\Gamma\in T^\times.
\tag{6.3}
$$

No division by $2$ occurs. This is why the matrix step itself remains valid in residual characteristic two, even though determinant deformation theory there requires other corrections.

### 6.3 Trace coordinates

For $g\in G$, define

$$
c_i(g)=\sum_{j=1}^4(\Gamma^{-1})_{ij}t(gg_j)\in T.
\tag{6.4}
$$

Then

$$
\rho_Q(g)=\sum_{i=1}^4c_i(g)x_i.
\tag{6.5}
$$

To prove this, pair the difference with every $x_j$. Formula (6.4) makes all four traces zero. On each field factor $E_i$, the Gram determinant remains nonzero, so the $x_j$ form a basis of $M_2(E_i)$ and the trace pairing is nondegenerate. The difference is therefore zero on every factor, hence zero in $M_2(T_E)$.

This calculation has three important features. It uses traces of products $gg_j$, which are still traces of group elements. It expresses every group matrix using coefficients in $T$. And it makes those coefficients continuous functions of $g$, because $t$ is continuous and $\Gamma^{-1}$ is fixed.

### 6.4 The rank-four algebra

Define

$$
\mathscr E=\sum_{i=1}^4Tx_i\subseteq M_2(T_E).
\tag{6.6}
$$

The sum is direct. If $\sum a_ix_i=0$, pairing with the $x_j$ and multiplying by $\Gamma^{-1}$ gives every $a_i=0$. Hence $\mathscr E$ is finite free of rank four over $T$.

Formula (6.5) shows that $\rho_Q(G)\subseteq\mathscr E$. In particular, for every $i,j$, the product $x_ix_j=\rho_Q(g_ig_j)$ lies in $\mathscr E$. Thus $\mathscr E$ is a $T$-algebra, and

$$
\mathscr E\otimes_TE_i\simeq M_2(E_i)
\tag{6.7}
$$

on every generic branch.

Although $\mathscr E$ was written as a submodule of a product of matrix algebras, its special fiber is intrinsic. Write

$$
x_ix_j=\sum_m a_{ijm}x_m,
\qquad a_{ijm}\in T,
\tag{6.12}
$$

using (6.4). Reducing the trace formulas for $a_{ijm}$ gives the multiplication table of the residual matrices $\bar x_i\bar x_j$. Therefore the $k$-linear map

$$
\mathscr E/\mathfrak n\mathscr E\longrightarrow M_2(k),
\qquad \bar x_i\longmapsto\bar\rho(g_i),
\tag{6.13}
$$

is a well-defined algebra isomorphism. This justifies reduction even though the original tuple $x_i\in M_2(T_E)$ is not assumed entrywise to belong to $M_2(T)$.

Reduction gives a homomorphism

$$
\mathscr E/\mathfrak n\mathscr E\longrightarrow M_2(k)
$$

sending the basis $x_i$ to the basis $\bar x_i$. It is therefore an isomorphism. Consider now the multiplication map

$$
\mu:\mathscr E\otimes_T\mathscr E^{\mathrm{op}}
\longrightarrow\operatorname{End}_T(\mathscr E),
\qquad a\otimes b\mapsto(x\mapsto axb).
\tag{6.8}
$$

Both sides are finite free of rank sixteen. Modulo $\mathfrak n$, (6.8) is the standard isomorphism

$$
M_2(k)\otimes_kM_2(k)^{\mathrm{op}}
\simeq\operatorname{End}_k(M_2(k)).
$$

The determinant of a matrix for $\mu$ is therefore a unit, so $\mu$ is an isomorphism. Hence $\mathscr E$ is an Azumaya algebra over $T$ with split special fiber.

### 6.5 Azumaya splitting

The complete local ring $T$ is Henselian. The splitting theorem for an Azumaya algebra over a pro-Artinian local ring with split special fiber gives

$$
\theta:\mathscr E\xrightarrow{\sim}M_2(T).
\tag{6.9}
$$

For clarity, the decisive construction is as follows. A rank-one matrix idempotent in $M_2(k)=\mathscr E/\mathfrak n\mathscr E$ lifts compatibly through the quotients $T/\mathfrak n^m$. Its inverse limit is an idempotent $e\in\mathscr E$. The left module $P=\mathscr E e$ is finite projective of rank two over $T$, hence free because $T$ is local. Left multiplication gives

$$
\mathscr E\longrightarrow\operatorname{End}_T(P).
$$

It is an isomorphism after reduction and both sides have rank four, so it is an isomorphism. Choosing a basis of $P$ gives (6.9).

We may normalize the basis so that $\theta$ reduces to the fixed identification with $M_2(k)$. The ambiguity in this choice is conjugation by $\operatorname{GL}_2(T)$; after residual normalization it is strict conjugation.

To see the last assertion, let $\theta_1,\theta_2:\mathscr E\to M_2(T)$ be two splittings. Their comparison is a $T$-algebra automorphism of $M_2(T)$. Local Skolem--Noether makes it conjugation by some $u\in\operatorname{GL}_2(T)$. If the two splittings have the same residual normalization, the reduction of $u$ centralizes all of $M_2(k)$ and is therefore scalar. Multiplying $u$ by a lift of the inverse scalar produces

$$
u\equiv I\pmod{\mathfrak n}.
$$

This scalar correction is the source of strict, rather than ordinary, conjugacy.

### 6.6 Continuity, determinant, and uniqueness

Set

$$
\rho_T(g)=\theta(\rho_Q(g)).
\tag{6.10}
$$

Because $\rho_Q(G)\subseteq\mathscr E$, this is a homomorphism into $M_2(T)$. It lands in $\operatorname{GL}_2(T)$: its inverse is $\theta(\rho_Q(g^{-1}))$. Its coordinate functions in the basis $\theta(x_i)$ are the continuous functions (6.4), so it is continuous.

The algebra isomorphism preserves the reduced trace and reduced norm. On every generic factor these are ordinary matrix trace and determinant. Since $T\hookrightarrow T_E$,

$$
\operatorname{tr}\rho_T(g)=t(g),
\qquad
\det\rho_T(g)=d(g).
\tag{6.11}
$$

Scalar extension of (6.9) identifies (6.10) with every branch representation. Finally, two $T$-valued realizations with the same trace and absolutely irreducible reduction generate the same trace algebra. The strict-conjugacy descent theorem identifies them by a conjugator congruent to the identity. This completes the proof of Theorem 6.1. $\square$

## 7. Construction of the Hecke-valued representation

### 7.1 The construction theorem

**Theorem 7.1 (Hecke-valued representation).** For a clean datum of Chapter 2, there is a continuous representation

$$
\rho_{\mathbb T}:G_{F,S}\longrightarrow\operatorname{GL}_2(\mathbb T)
\tag{7.1}
$$

unique up to strict conjugacy, such that

$$
\rho_{\mathbb T}\bmod\mathfrak n=\bar\rho,
\qquad
\det\rho_{\mathbb T}=\delta,
\tag{7.2}
$$

and for every $v\notin S$,

$$
\det(X-\rho_{\mathbb T}(\Phi_v))
=X^2-T_vX+q_vS_v.
\tag{7.3}
$$

For each generic eigencharacter $\lambda_i$, the specialization of (7.1) to $E_i$ is isomorphic to $\rho_i$.

**Proof.** Chapters 4 and 5 construct the product representation $\rho_Q$ and prove that all its traces and determinants lie in $\mathbb T$. Its branches have the common absolutely irreducible reduction. Theorem 6.1 therefore produces (7.1), with trace and determinant as stated. Equation (7.3) follows from (4.9). Strict uniqueness is part of Theorem 6.1. $\square$

### 7.2 Good-place reciprocity

Equation (7.3) contains two statements. The representation is unramified at $v$ because it factors through $G_{F,S}$. Its geometric-Frobenius trace is the Hecke operator $T_v$, and its determinant is the fixed scalar $q_vS_v$.

There is no ambiguity at scalar Frobenius. Rank two and the independently fixed determinant make (7.3) the characteristic polynomial, not merely a quadratic annihilator. Nor is an arithmetic-Frobenius convention being mixed in: arithmetic Frobenius has inverse roots.

If $u/v$ is a place after ground-field extension of residue degree $f$, the roots at $u$ are the $f$th powers of those at $v$. One should not reuse $T_v$ as their trace unless $f=1$.

### 7.3 Minimality of the trace coefficient ring

The closed trace algebra of $\rho_{\mathbb T}$ is

$$
\overline{\mathcal O[\operatorname{tr}\rho_{\mathbb T}(g):g\in G_{F,S}]}.
$$

It contains every $T_v$ by (7.3), and these generate $\mathbb T$ by (3.3). Hence it equals $\mathbb T$. Consequently no strict conjugate of $\rho_{\mathbb T}$ can be defined over a proper closed $\mathcal O$-subalgebra of $\mathbb T$.

This is coefficient minimality, not faithfulness of $\rho_{\mathbb T}$ as a group homomorphism. Its kernel may be large. It is also not freeness of the automorphic module over $\mathbb T$. Three uses of the word “faithful” must remain separate:

- the Hecke order acts faithfully on its defining automorphic module;
- Galois traces generate the coefficient order;
- the abstract Galois group may or may not act faithfully.

### 7.4 Change of coefficients

Let $\mathcal O\to\mathcal O'$ be a finite flat extension and choose a local factor $\mathbb T'$ of $\mathbb T\otimes_{\mathcal O}\mathcal O'$ above $\mathfrak n$. Scalar extension gives

$$
\rho_{\mathbb T'}=\rho_{\mathbb T}\otimes_{\mathbb T}\mathbb T'.
\tag{7.4}
$$

If the residue basis is kept fixed, this agrees up to strict conjugacy with the representation reconstructed from the base-changed automorphic branches. This follows from equality of traces and strict-conjugacy uniqueness.

Coefficient extension can split generic fields or separate residue embeddings. It cannot repair a missing local type, turn a primitive wild packet into a tame dihedral one, or make a rational projector integral at a denominator prime.

### 7.5 Semisimplification and extensions

Every generic specialization of (7.1) is the semisimple cohomological representation. Since it is irreducible, it is already semisimple. The Artinian reductions of (7.1), however, can contain nontrivial extensions. Those extensions are genuine congruence information carried by $\mathbb T$.

Good Frobenius polynomials do not determine these Artinian extension classes without residual absolute irreducibility and the common trace algebra. Theorem 6.1 constructs one family because the residual matrix algebra is full. It does not assert that an arbitrary reducible pseudorepresentation has a unique matrix realization.

Two limiting examples clarify the result. If $\mathbb T=\mathcal O$ has one branch, the theorem recovers the familiar integral representation attached to a single packet; trace descent says that a representation written over a larger field can be conjugated to its trace ring. If $\mathbb T$ has two crossing branches as in (3.9), the representation contains both characteristic-zero packets and their common residual representation. Reducing modulo the maximal ideal does not select either branch. Quotienting by a branch ideal does, while quotienting by a thicker ideal can retain a nontrivial infinitesimal extension between their eigenvalue directions.

These extensions are not extensions of the two characteristic-zero representations as $G_{F,S}$-modules; the branches live over different factors after inverting $\varpi$. They are extensions in the coefficient geometry of the local order. The trace-coordinate basis is precisely what lets that coefficient geometry act on one free Galois module.

## 8. Deformation conditions and a generic-point criterion

### 8.1 Represented local conditions

Fix a place $w\in S$ and a residual local representation $\bar\rho_w$. A framed local deformation condition $\mathcal D_w$ is represented by a quotient

$$
R_w^\square\twoheadrightarrow R_w^{\square,\mathcal D_w}
=R_w^\square/J_w.
\tag{8.1}
$$

Membership is stable under every map of Artinian coefficient rings. The relevant conditions are:

- finite flatness at $w\mid\ell$;
- unramified or fixed prime-to-$\ell$ finite type at minimal places away from $\ell$;
- the ordered principal, enhanced special, and fixed tame-dihedral conditions at the selected nonminimal places.

When a line, ordering, or sign is part of the represented object, it must also be supplied on the automorphic side. Forgetting enhancement can replace a smooth component by a singular union.

The restriction of $\rho_{\mathbb T}$ gives a classifying map

$$
f_w:R_w^\square\longrightarrow\mathbb T
\tag{8.2}
$$

after choosing a local frame. We need to show $f_w(J_w)=0$.

### 8.2 The reduced-order factorization lemma

**Lemma 8.1 (generic points detect a quotient).** Let $A$ be finite flat over $\mathcal O$ and suppose $A_E$ is reduced. Let $f:R\to A$ be a homomorphism from a complete local $\mathcal O$-algebra, and let $J\subseteq R$ be an ideal. If for every field factor $L$ of $A_E$ the composite

$$
R\xrightarrow{f}A\longrightarrow A_E\longrightarrow L
$$

kills $J$, then $f(J)=0$.

**Proof.** Reducedness gives an injection

$$
A_E\hookrightarrow\prod_L L.
$$

The hypothesis implies that the image of every $j\in J$ is zero in every factor, hence zero in $A_E$. Since $A$ is $\mathcal O$-torsion free, $A\hookrightarrow A_E$. Therefore $f(j)=0$ in $A$. $\square$

This elementary lemma is the engine of nonminimal factorization. It uses no density of characteristic-zero points beyond the fact that every simple factor of the finite generic algebra is included.

### 8.3 Application to all Artinian quotients

Suppose every branch representation $\rho_i|_{G_{F_w}}$ lies in the generic fiber of $\mathcal D_w$. Equivalently, every branch classifying map kills $J_w$. Lemma 8.1 applied to (8.2) gives a factorization

$$
R_w^\square\longrightarrow R_w^{\square,\mathcal D_w}
\longrightarrow\mathbb T.
\tag{8.3}
$$

For every open ideal $I\subset\mathbb T$, base change gives

$$
\rho_{\mathbb T/I}|_{G_{F_w}}
\in\mathcal D_w(\mathbb T/I).
\tag{8.4}
$$

Thus a verification on all generic automorphic branches proves the exact condition on every Artinian quotient. The conclusion is not that each quotient has some unrelated local model. It is that all quotients arise by base change from one map through the represented local ring, so their transition maps are automatic.

It is worth spelling out the ideal calculation. If $J_w$ is generated topologically by elements $r_\alpha$, their images

$$
f_w(r_\alpha)\in\mathbb T
$$

vanish under every generic eigencharacter. Flatness embeds $\mathbb T$ into $\mathbb T[1/\varpi]$, and reducedness embeds the latter into the product of its fields. Hence each image is literally zero, not merely topologically nilpotent. The map (8.2) therefore kills the closed ideal generated by the $r_\alpha$ and descends continuously to the quotient.

Conversely, once (8.3) exists, membership after quotienting by $I$ follows from the functorial definition of the local condition. No new density argument is performed over $\mathbb T/I$, whose generic fiber may be zero. This point is important for quotients killed by a power of $\varpi$: they have no characteristic-zero points at all, yet they satisfy the local condition because the integral classifying map was established before reduction.

### 8.4 Framed and unframed formulations

The argument is most literal for framed rings. A different local frame conjugates (8.2), and the represented conditions are invariant under strict conjugacy. Hence the factorization is intrinsic.

Globally, absolute irreducibility makes the unframed deformation functor representable. The local residual centralizer can nevertheless be larger than the global centralizer. One should therefore build the global conditioned ring using framed local quotients and the standard fiber-product construction. No local unframed universal ring is needed at a scalar local residual point.

When an enhanced condition includes lines, those lines are genuine objects over $\mathbb T$. The forgetful image in the ordinary unframed deformation space can identify Weyl-conjugate branches. Factorization through the enhanced ring is stronger and requires the automorphic enhancement.

### 8.5 The nilpotent warning

Generic-point detection fails for a nonreduced generic algebra. Let

$$
A=E[\epsilon]/(\epsilon^2).
$$

Every field-valued point kills $\epsilon$, but $\epsilon\ne0$ in $A$. A relation can therefore vanish on every eigencharacter and still survive as a nilpotent operator.

Likewise, if an integral coefficient algebra has $\mathcal O$-torsion, a relation may vanish after inverting $\varpi$ without vanishing integrally. Lemma 8.1 deliberately assumes both generic reducedness and integral flatness. If either fails, one needs a direct construction of the local condition on the family, not a characteristic-zero point argument.

## 9. The coefficient prime

### 9.1 Finite flatness is integral

Let $w\mid\ell$. A free rank-two representation over an Artinian $\mathcal O$-algebra $A$ is finite flat when it is identified with the geometric points of the generic fiber of a finite locally free group scheme over $\mathcal O_{F_w}$ carrying the given $A$-action. This definition concerns the lattice and its coefficient action. It is stronger than any assertion about the characteristic-zero representation alone.

In particular, the following implications are invalid without further hypotheses:

$$
\text{crystalline of weights }\{0,1\}
\ \not\Longrightarrow\
\text{every stable lattice has finite-flat quotients},
$$

and

$$
\text{good Frobenius polynomials away from }\ell
\ \not\Longrightarrow\
\text{finite flatness at }w.
$$

The clean datum avoids both errors. Each automorphic branch comes with a marked integral cohomological lattice and compatible finite-flat models for all its coefficient quotients. The local finite-flat deformation functor is represented by a closed quotient of the framed local deformation ring and is stable under arbitrary coefficient base change.

### 9.2 Comparison of branch lattices

The branch of $\rho_{\mathbb T}$ along $\lambda_i:\mathbb T\to\mathcal O_i$ gives an integral representation on $\mathcal O_i^2$. The attachment theorem may have supplied a different canonical lattice $L_i^{\mathrm{geom}}$. We must compare them before importing finite flatness.

**Lemma 9.1 (integral conjugacy of irreducible lattices).** Let $K$ be a finite extension of $E$, with valuation ring $A$. Let $V$ be a two-dimensional $K$-representation of a group $G$. If two $G$-stable free $A$-lattices $L,L'$ have absolutely irreducible isomorphic reductions as $G$-modules, then, after multiplying one lattice by a scalar in $K^\times$, there is a $G$-equivariant isomorphism $L\simeq L'$ whose reduction is an isomorphism. Consequently their matrix representations are conjugate by $\operatorname{GL}_2(A)$.

**Proof.** Choose a nonzero $K[G]$-isomorphism between the two copies of $V$; Schur's lemma makes the space of such maps one-dimensional. Scale it so that $L$ maps into $L'$ but not into the maximal-ideal multiple of $L'$. Its reduction is a nonzero $k[G]$-map. Absolute irreducibility makes this reduction an isomorphism. Nakayama then makes the integral map surjective, and equality of ranks makes it an isomorphism. $\square$

Apply the lemma to the global group $G_{F,S}$, not to the decomposition group at $w$. The generic specialization of $\rho_{\mathbb T}$ and the geometric branch representation have the same global character, so they are isomorphic. Their global reductions are both $\bar\rho$, which is absolutely irreducible. The lemma therefore identifies their global lattices integrally. Restricting that integral conjugacy to $G_{F_w}$ shows that the branch lattice of $\rho_{\mathbb T}$ has the same finite-flat quotient property as the geometric lattice. No absolute irreducibility of the local restriction is asserted or needed. Finite flatness is invariant under integral change of basis.

### 9.3 Finite-flat factorization

Let

$$
R_w^\square\twoheadrightarrow R_w^{\square,\mathrm{fl}}
$$

represent the framed finite-flat condition, with the fixed determinant imposed if required. By the preceding comparison, every generic branch of the map

$$
R_w^\square\longrightarrow\mathbb T
$$

factors through $R_w^{\square,\mathrm{fl}}$. Lemma 8.1 gives a unique factorization

$$
R_w^\square\longrightarrow
R_w^{\square,\mathrm{fl}}
\longrightarrow\mathbb T.
\tag{9.1}
$$

This proof uses the closedness of the finite-flat locus through its representing quotient. It does not attempt to glue finite flat group schemes branch by branch. The factorization supplies exactly the coherent coefficient-level statement needed by global deformation theory.

There is a subtle distinction between an existential condition and a moduli problem with a chosen model. The framed finite-flat deformation functor records that a suitable coefficient-linear finite flat group exists; it does not necessarily retain that group as extra structure. Fiber-product membership and schematic closure prove representedness for this existential functor. Therefore (9.1) canonically determines the finite-flat deformation class, even if several integral group models realize the same generic representation outside a full-faithfulness range.

In the low-ramification range, integral full faithfulness and the coefficient normal-form theorem give uniqueness and compatible coefficient actions. Then one may strengthen the conclusion to a marked system of models. The nonminimal reciprocity map itself needs only the represented existential condition, so it remains logically separate from this stronger uniqueness.

### 9.4 Every Artinian quotient

Let $I\subset\mathbb T$ be any open ideal. Base change in (9.1) shows that

$$
\rho_{\mathbb T}/I
$$

is finite flat at $w$. If $I\subset J$, the model for the $J$-quotient is obtained from the $I$-level condition by coefficient quotient in the existential deformation functor. One should not infer a unique compatible tower of group schemes unless the marked geometric realization provides it; what is canonical here is the compatible tower of deformation classes.

For the principal ideals $I=(\varpi^n)$, the geometric branch data do provide marked finite-flat models with transitive transition maps. The order-valued factorization is compatible with those branch models after scalar extension. Over a general nonprincipal quotient $\mathbb T/I$, representedness supplies finite flatness even though there need not be a single branchwise geometric quotient from which it visibly descends.

### 9.5 The exceptional coefficient-prime range

The general framed finite-flat functor is represented for finite extensions of $\mathbf Q_\ell$. The particularly clean power-series description used in balanced rank-two deformation problems requires more: $\ell>2$, $F_w/\mathbf Q_\ell$ unramified, Hodge type $(0,1)$, and the fixed cyclotomic determinant. Under those hypotheses it is formally smooth.

If $F_w$ is ramified, if $\ell=2$, or if the weights leave $[0,1]$, the factorization argument remains valid only when a represented integral local condition and branchwise integral realization have independently been supplied. One may not replace them by the clean theorem. At $\ell=2$, the determinant tangent uses the trace-kernel complex, real places are not rigid, and the low-weight normal-form theorem invoked in the clean global package is unavailable.

## 10. Local types away from the coefficient prime

### 10.1 Type occurrence and Galois parameters

Fix $w\nmid\ell$ in $S$. The integral type lattice selects automorphic representations; the local--global compatibility theorem identifies their Galois parameters. These are different steps.

For every generic branch $i$, type occurrence gives a label for $\Pi_{i,w}$ in the selected principal, special, or tame-dihedral range. Local--global compatibility then gives

$$
\operatorname{WD}(\rho_i|_{G_{F_w}})^{\mathrm{F\!-!ss}}
\simeq D(\Pi_{i,w}).
\tag{10.1}
$$

The hypotheses include the actual geometric model, finite descent action, type projector on the stratum complex, monodromy comparison, and Frobenius return maps. Equality of conductors or inertial semisimplifications is not substituted for (10.1).

Each chosen local datum $\mathfrak D_w$ has a represented deformation ring

$$
R_w^{\square,\mathfrak D_w}.
$$

The compatibility theorem for type lattices says that the named characteristic-zero component has exactly the selected Weil--Deligne label, up to the ordering or unramified twist explicitly retained in the datum. Consequently every generic branch map lands on the named component, and Lemma 8.1 gives the integral factorization through $R_w^{\square,\mathfrak D_w}$.

### 10.2 Principal components

An ordered principal datum consists of two finite inertial characters $\theta_1,\theta_2$, two Frobenius-stable rank-one direct summands $L_1,L_2$, and a fixed determinant. In an adapted basis,

$$
\rho(\tau)=
\begin{pmatrix}
\theta_1(\tau)&0\\
0&\theta_2(\tau)
\end{pmatrix},
\qquad
\rho(\phi)=
\begin{pmatrix}a&0\\0&b\end{pmatrix},
\qquad ab=\delta(\phi),
\tag{10.2}
$$

where $\phi$ is arithmetic Frobenius and $\theta_j^q=\theta_j$.

When the residual characters are distinct and have prime-to-$\ell$ order, the two lines are recovered canonically by inertial idempotents. When they are congruent, the unordered matrix representation no longer remembers which lift is first. The line enhancement is then essential. If the automorphic module only detects the unordered principal type, the valid conclusion is factorization through the union of the two Weyl-conjugate components, not through either ordered component.

Congruence-tame diamond variation can also be represented by a line-enhanced ring. It is included only when the finite $\ell$-group quotient and its tautological character are part of the local datum. An away-Hecke trace order need not contain the diamond group algebra; adjoining it changes the coefficient-generation question of Section 3.4.

### 10.3 Special components

For a special datum, finite inertia is scalar, say $\xi$, and the Weil--Deligne monodromy has rank one at every selected characteristic-zero point. The represented enhanced special ring is the closure of this locus, together with its invariant line and sign. Closure is crucial: nonzero monodromy is an open condition and cannot itself define a quotient stable under arbitrary coefficient reduction.

The tame equations explain the closure. Use arithmetic Frobenius $\phi$ and a tame generator $t$, so that $\phi t\phi^{-1}=t^q$. After removing the scalar finite character, write

$$
\rho(t)=I+N.
$$

The special incidence equations include

$$
N^2=0,
\qquad
\operatorname{tr}N=0,
\qquad
\det N=0,
\qquad
\rho(\phi)N\rho(\phi)^{-1}=qN,
\tag{10.2a}
$$

together with the determinant and invariant-line equations. Over characteristic zero, the open condition $N\ne0$ forces rank one and gives a special parameter. Setting $N=0$ still satisfies every polynomial equation in (10.2a), so it lies in the closed represented space. In geometric-Frobenius notation the last relation becomes the inverse relation in (12.5).

Thus the integral factorization asserts the special incidence equations, the scalar finite inertia character, the Frobenius relation, and the chosen sign. It does not assert that monodromy remains nonzero modulo every ideal of $\mathbb T$. Chapter 12 measures its possible vanishing.

At a clean level-raising prime, the sign is separated by the hypotheses

$$
q_w\not\equiv\pm1\pmod\ell
$$

and by the normalized Iwahori operator. If the signs meet modulo $\ell$, a sign-selected characteristic-zero module can have a common residual point with its companion. The enhanced ring, rather than an unlabelled Steinberg slogan, records the intended branch.

### 10.4 Tame dihedral components

Let $L/F_w$ be a tame quadratic extension and let $\theta$ be a tame admissible character with $\theta\ne\theta^\sigma$. The selected parameter is

$$
\operatorname{Ind}_{W_L}^{W_{F_w}}\theta,
\qquad N=0.
\tag{10.3}
$$

The compact type recovers the pair up to Galois conjugation and the explicitly allowed unramified norm twist. The finite descent complex identifies inertia, while the Frobenius intertwiner removes the remaining unramified ambiguity. Under the clean prime-to-$\ell$ hypothesis the fixed finite-type framed ring is formally smooth of relative dimension three with fixed determinant.

Depth-zero and positive-depth tame types are both included. A ramified quadratic extension in residue characteristic two is not tame and is excluded. A primitive wild supercuspidal is not recovered from a quadratic pair and is also excluded.

### 10.5 Orderings, signs, and companion lattices

The primary type lattice determines occurrence. Its companion makes the adjunction integral. In the Steinberg case, for example, the quotient model and the augmentation submodule are distinct lattices even though they span dual characteristic-zero representations. Their perfect pairing is obtained without averaging.

This matters globally. A type multiplicity map is normalized by taking its saturated primitive image. Scaling a rational projector by a nonunit changes an integral image and can create a false congruence index. The clean automorphic module therefore remembers:

$$
(\text{primary lattice},\ \text{companion lattice},\
\text{primitive pairing},\ \text{ordering or sign}).
\tag{10.4}
$$

Only with this package does generic type occurrence imply membership in the intended local deformation component on every branch of the faithful order.

## 11. Inertia in the Hecke-valued family

### 11.1 Prime-to-coefficient rigidity

Let $H$ be a finite quotient of inertia of order prime to $\ell$. If $A$ is a complete local $\mathcal O$-algebra and two lifts

$$
\tau_1,\tau_2:H\longrightarrow\operatorname{GL}_2(A)
$$

have the same residual representation and become conjugate on every characteristic-zero branch, then they are strictly conjugate over $A$ under the clean fixed-type hypotheses.

The reason is that averaging is integral. For an infinitesimal ideal $I$ with $I^2=0$, the difference of two lifts is a cocycle in $Z^1(H,\operatorname{ad}\bar\tau\otimes I)$. Since $|H|$ is a unit,

$$
H^1(H,\operatorname{ad}\bar\tau\otimes I)=0
$$

by the usual averaged contracting homotopy. The conjugator therefore lifts through every small extension. Completeness gives a compatible inverse limit. Its ambiguity is the centralizer, exactly as in the fixed finite-type deformation chart.

This argument fails when $\ell\mid|H|$. In that case an integral type lattice may still exist, but inertia can acquire genuine deformation directions and reduction need not be semisimple.

For completeness, the averaged contracting homotopy can be written explicitly. If $c:H\to M$ is a one-cocycle, put

$$
X=-|H|^{-1}\sum_{h\in H}c(h).
\tag{11.0}
$$

Using $c(gh)=c(g)+g c(h)$ and permuting the summation index gives

$$
c(g)=gX-X.
$$

Conjugation by $1+X$ removes the infinitesimal difference between the two lifts. Iterating through the quotients by powers of the maximal ideal gives compatible strict conjugators. The same calculation shows that the obstruction groups in positive degree vanish for the finite inertia action.

### 11.2 The finite-type inertia theorem

**Theorem 11.1 (inertia over the Hecke order).** Let $w\nmid\ell$ carry a clean fixed finite-type or tame-dihedral datum. Let

$$
\tau_w:I_{F_w}\longrightarrow\operatorname{GL}_2(\mathcal O)
$$

be its fixed finite inertial representation, factoring through a group $H_w$ of order prime to $\ell$. Then, after a strict change of basis over $\mathbb T$,

$$
\rho_{\mathbb T}|_{I_{F_w}}=\tau_w\otimes_{\mathcal O}\mathbb T.
\tag{11.1}
$$

For a ramified special datum the corresponding formula is first applied to the scalar finite part $\xi_w$; the unipotent part is treated in Chapter 12.

**Proof.** Factorization through the represented fixed-type ring gives a lift of the fixed residual inertial action. Prime-to-$\ell$ rigidity makes it strictly conjugate to the constant lift. Alternatively, on every generic branch local--global compatibility identifies the same $\tau_w$; the rigidity lifting argument constructs compatible conjugators through $\mathbb T/\mathfrak n^r$. Their inverse limit gives (11.1). $\square$

The theorem identifies inertia, not Frobenius. In a dihedral orbit the return map of Frobenius is separate data; in a principal family unramified characters can vary without altering (11.1).

### 11.3 The ordered principal inertia theorem

**Theorem 11.2 (principal inertia with lines).** At an ordered principal place, the factorization through the enhanced local ring supplies rank-one direct summands

$$
\mathcal L_1,\mathcal L_2\subset\mathbb T^2,
\qquad
\mathbb T^2=\mathcal L_1\oplus\mathcal L_2,
\tag{11.2}
$$

stable under $G_{F_w}$, such that inertia acts on $\mathcal L_j$ through $\theta_j$. If $\bar\theta_1\ne\bar\theta_2$ and the finite inertia order is prime to $\ell$, these lines are determined by $\rho_{\mathbb T}$ itself. If $\bar\theta_1=\bar\theta_2$, they are additional structure and need not be determined by the underlying representation.

**Proof.** The universal enhanced principal deformation carries the two universal lines. Pulling them back along its map to $\mathbb T$ gives (11.2) and the character formula. In the distinct case the two integral inertial idempotents project onto the lines, proving uniqueness. In the congruent case those idempotents coincide after reduction, so the representation alone cannot recover an ordering. $\square$

### 11.4 Base change to Artinian coefficients

For every open ideal $I\subset\mathbb T$, Theorems 11.1 and 11.2 base change to $\mathbb T/I$. Finite inertia stays exactly constant in the prime-to-$\ell$ case. The principal lines remain direct summands because they were direct summands before quotienting.

This conclusion is stronger than saying that each characteristic-zero specialization has the right inertial type. It controls nilpotent coefficient directions and congruence intersections. It is weaker than asserting that the entire local Weil representation is constant: Frobenius eigenvalues and special monodromy can vary in the family.

### 11.5 What inertia does not determine

An inertial type forgets all unramified twists. It also forgets the difference between scalar $N=0$ and scalar $N\ne0$. Two tame dihedral representations with the same inertial characters can have different Frobenius return scalars. Two special parameters of opposite sign have the same trivial inertia and conductor one.

Therefore none of the following is a valid replacement for full local reciprocity:

- equality of inertia alone;
- equality of Artin conductors;
- occurrence of an unenhanced compact type at a scalar boundary;
- equality of the semisimplified restriction to inertia.

The local deformation datum retains the missing Frobenius, ordering, sign, and monodromy information.

## 12. Monodromy over the Hecke order

### 12.1 The special branch formula

Let $w\nmid\ell$ be a special place, with residue cardinality $q$. Fix geometric Frobenius $\Phi$ and a tame coordinate

$$
t_\ell:I_{F_w}\longrightarrow\mathbf Z_\ell(1)
$$

normalized so that

$$
t_\ell(\Phi\sigma\Phi^{-1})=q^{-1}t_\ell(\sigma).
\tag{12.1}
$$

Let $\xi:I_{F_w}\to\mathcal O^\times$ be the fixed Frobenius-stable scalar finite character. On every characteristic-zero branch the special Weil--Deligne formula is

$$
\rho_i(\sigma)=\xi(\sigma)
\exp(t_\ell(\sigma)N_i)
=\xi(\sigma)(1+t_\ell(\sigma)N_i),
\tag{12.2}
$$

where $N_i^2=0$ and $N_i\ne0$. The exponential truncates because the representation has rank two.

Choose $\sigma_0$ in tame inertia for which $t_\ell(\sigma_0)$ is an $\ell$-adic unit. Such an element exists after choosing a generator of the $\mathbf Z_\ell(1)$ quotient.

### 12.2 Construction of the universal monodromy operator

After the strict conjugation which makes the finite inertial character scalar, define

$$
N_{\mathbb T}
=t_\ell(\sigma_0)^{-1}
\bigl(\xi(\sigma_0)^{-1}\rho_{\mathbb T}(\sigma_0)-I\bigr)
\in M_2(\mathbb T).
\tag{12.3}
$$

**Theorem 12.1 (Hecke-valued monodromy).** For every $\sigma\in I_{F_w}$,

$$
\rho_{\mathbb T}(\sigma)
=\xi(\sigma)(I+t_\ell(\sigma)N_{\mathbb T}),
\tag{12.4}
$$

and

$$
N_{\mathbb T}^2=0,
\qquad
\rho_{\mathbb T}(\Phi)N_{\mathbb T}
\rho_{\mathbb T}(\Phi)^{-1}=q^{-1}N_{\mathbb T}.
\tag{12.5}
$$

The specialization of $N_{\mathbb T}$ to every generic branch is its nonzero Weil--Deligne monodromy operator.

**Proof strategy.** Equations (12.4)--(12.5) hold on every generic branch by local--global compatibility. The order injects into the product of those branches, so the equations hold integrally.

**Proof.** Formula (12.3) specializes to $N_i$ by (12.2). Hence, after mapping to every $E_i$, the difference between the two sides of (12.4) is zero, as are the entries of $N_{\mathbb T}^2$ and of the difference in (12.5). Since

$$
M_2(\mathbb T)\hookrightarrow\prod_iM_2(E_i),
$$

all these identities already hold over $\mathbb T$. $\square$

The operator depends on the chosen trivialization of the tame Tate module: rescaling $t_\ell$ rescales $N_{\mathbb T}$ by the inverse unit. Its vanishing, image, kernel, and entry ideal are independent of this choice.

The choice of $\sigma_0$ is harmless as well. If $\sigma_1$ has unit tame coordinate, formula (12.4), already proved by generic detection, gives

$$
t_\ell(\sigma_1)^{-1}
(\xi(\sigma_1)^{-1}\rho(\sigma_1)-I)
=N_{\mathbb T}.
$$

Thus every unit-coordinate generator produces the same operator for the fixed trivialization. Replacing $\Phi$ by $i\Phi$ with $i\in I_{F_w}$ changes its matrix but not the induced Frobenius-semisimple Weil--Deligne parameter; the conjugation identity continues to hold because inertia commutes with $N$ after the scalar finite part is removed.

The logarithmic definition is integral in rank two because the square of the unipotent part is zero. For a higher-dimensional family the logarithm could contain denominators such as $1/2$, and an integral monodromy operator would require divisibility checks. Nothing of that higher-rank form is being assumed here.

### 12.3 Frobenius and the invariant line

Let

$$
\mathcal K=\ker N_{\mathbb T}.
$$

On a generic branch, $\mathcal K$ is the one-dimensional invariant line and geometric Frobenius acts on it by the special scalar $\beta_i$. Over $\mathbb T$, the kernel need not be a direct summand unless the image of $N_{\mathbb T}$ is primitive. The enhanced special deformation condition therefore carries a line independently of this kernel construction.

On that universal line, geometric Frobenius acts by an element $\beta\in\mathbb T^\times$ fixed by the sign operator, and the quotient eigenvalue is $q\beta$. Thus generically

$$
\det(X-\rho_{\mathbb T}(\Phi))
=(X-\beta)(X-q\beta).
\tag{12.6}
$$

The determinant relation gives $q\beta^2=\delta(\Phi)$ in the geometric convention. If a different normalization uses arithmetic Frobenius, both eigenvalues and the conjugation relation in (12.5) invert. Mixing the two conventions changes the special parameter.

### 12.4 Vanishing after reduction

Although every generic $N_i$ is nonzero, $N_{\mathbb T}$ can become zero modulo a nonzero ideal. For example,

$$
N_{\mathbb T}=
\begin{pmatrix}0&a\\0&0\end{pmatrix}
$$

with $a\in\mathfrak n$ is nonzero over every characteristic-zero branch when $a$ is not a zero divisor in the generic fiber, but it vanishes modulo $(a)$.

Thus the closed special deformation condition contains a monodromy-zero boundary. The statement “the family is Steinberg” means that its generic branches lie in the open $N\ne0$ locus and that the whole family lies in its represented closure. It does not mean that every Artinian specialization has conductor one. Artin conductors are not constant under congruence specialization.

This boundary is arithmetically meaningful. Level lowering detects residual points at which monodromy vanishes, subject to component-group and normalization hypotheses. Declaring $N$ to be nonzero in every quotient would erase precisely those points.

### 12.5 Monodromy ideals

Define the **monodromy ideal**

$$
\mathfrak a_w
=\operatorname{Fitt}_{\mathbb T}
(\operatorname{coker}(N_{\mathbb T}:\mathbb T^2\to\mathbb T^2)).
\tag{12.7}
$$

Since $N_{\mathbb T}$ has generic rank one and determinant zero, the zeroth Fitting ideal vanishes; the useful rank-one ideal is the ideal generated by its entries, equivalently the first nonzero determinantal ideal. Denote it by

$$
\mathfrak m_w(N)=I_1(N_{\mathbb T}).
\tag{12.8}
$$

It is invariant under change of basis and under unit rescaling of the tame coordinate. For an ideal $I\subset\mathbb T$,

$$
N_{\mathbb T}\bmod I=0
\quad\Longleftrightarrow\quad
\mathfrak m_w(N)\subseteq I.
\tag{12.9}
$$

The ideal records the closed monodromy-zero locus. It should not be confused with the component group, the old--new Gram ideal, or a congruence ideal, although geometric theorems can relate them under additional hypotheses. Integral level change carefully keeps these modules separate.

## 13. Nonminimal reciprocity

### 13.1 The global nonminimal deformation datum

Let $\mathcal D^{\mathrm{nm}}$ consist of:

- the field $F$, controlling set $S$, coefficient ring $\mathcal O$, residual representation $\bar\rho$, and determinant $\delta$;
- the finite-flat condition at every $w\mid\ell$;
- the chosen minimal unramified or fixed prime-to-$\ell$ type condition at the remaining minimal places;
- the selected ordered principal, enhanced special, or tame-dihedral condition at every fixed nonminimal place;
- the odd conjugacy class at every real place.

Every finite local condition is represented in a framed category, is stable under arbitrary Artinian coefficient change, and has determinant $\delta|_{G_{F_w}}$. Since $\bar\rho$ is absolutely irreducible, the global unframed functor is represented by a complete Noetherian local ring

$$
R_{\mathcal D^{\mathrm{nm}}}.
\tag{13.1}
$$

Its universal representation is defined up to strict conjugacy. The fiber-product construction of the global ring retains framed local factors even when a local residual centralizer is nonscalar.

More explicitly, let $R_{F,S}^{\square_T}$ be a global deformation ring with frames at a nonempty collection $T$ containing the finite local factors, and let

$$
R_{\mathrm{loc}}^\square
=\widehat\bigotimes_{w\in T,\mathcal O}R_w^\square,
\qquad
R_{\mathrm{loc}}^{\square,\mathcal D}
=\widehat\bigotimes_{w\in T,\mathcal O}
R_w^{\square,\mathcal D_w}.
\tag{13.1a}
$$

Restriction of the global universal representation gives a map from the unrestricted local ring to the global framed ring. The conditioned framed global ring is

$$
R_{F,S}^{\square_T,\mathcal D}
=R_{F,S}^{\square_T}
\widehat\otimes_{R_{\mathrm{loc}}^\square}
R_{\mathrm{loc}}^{\square,\mathcal D}.
\tag{13.1b}
$$

This tensor product is the ring-theoretic reversal of a fiber product of functors. Removing the auxiliary frames produces (13.1) because the global residual endomorphisms are scalar. A local scalar centralizer does not obstruct this construction; it merely explains why the local quotient was kept framed.

The determinant compatibility is checked before forming (13.1b). If one local type has determinant different from $\delta|_{G_{F_w}}$, the fiber product is empty rather than a deformation condition with a surprising extra component.

### 13.2 The reciprocity map

Chapters 9--12 show that $\rho_{\mathbb T}$ satisfies every local condition in $\mathcal D^{\mathrm{nm}}$ on every Artinian quotient. Hence it is a $\mathbb T$-valued point of the global deformation functor. Universality gives a continuous local homomorphism

$$
\varphi_{\mathrm{nm}}:
R_{\mathcal D^{\mathrm{nm}}}\longrightarrow\mathbb T.
\tag{13.2}
$$

The direction is forced by variance: a representation over $\mathbb T$ is a point of the functor, so the universal coefficient ring maps to $\mathbb T$.

The universal representation specializes along (13.2) to $\rho_{\mathbb T}$ up to strict conjugacy. Therefore, at every good place,

$$
\varphi_{\mathrm{nm}}
(\operatorname{tr}\rho^{\mathrm{univ}}(\Phi_v))=T_v,
\tag{13.3}
$$

and

$$
\varphi_{\mathrm{nm}}
(\det\rho^{\mathrm{univ}}(\Phi_v))=q_vS_v.
\tag{13.4}
$$

### 13.3 Surjectivity

**Proposition 13.1.** The map (13.2) is surjective onto the trace Hecke order.

**Proof.** Its image is a closed $\mathcal O$-subalgebra of $\mathbb T$ because the source is compact and the target Hausdorff, or directly because the target is finite over $\mathcal O$. Equation (13.3) shows that the image contains every $T_v$ for $v\notin S$. These operators generate $\mathbb T$ by (3.3). Hence the image is all of $\mathbb T$. $\square$

If extra nontrace operators have been adjoined, the same proof reaches only $\mathbb T^{\mathrm{tr}}$. A separate integral generation theorem is required for surjectivity onto the enlarged order.

### 13.4 The main nonminimal theorem

**Theorem 13.2 (nonminimal reciprocity).** Under the clean datum, the Hecke-valued representation (7.1) defines a canonical strict-conjugacy class and a surjection

$$
R_{\mathcal D^{\mathrm{nm}}}\twoheadrightarrow\mathbb T
\tag{13.5}
$$

with the following properties.

1. It has residual representation $\bar\rho$ and determinant $\delta$.
2. It is unramified outside $S$ and satisfies (7.3) at every $v\notin S$.
3. At every $w\mid\ell$, all Artinian coefficient quotients are finite flat.
4. At a fixed finite-type or tame-dihedral place, inertia is the constant prescribed finite representation after strict conjugacy, and the Frobenius return datum lies on the named component.
5. At an ordered principal place, the two universal lines and characters exist over $\mathbb T$.
6. At a special place, the finite scalar inertia and the operator $N_{\mathbb T}$ satisfy (12.4)--(12.5); every generic branch has $N\ne0$, while its Artinian vanishing locus is (12.9).
7. Specialization to a generic automorphic branch recovers its attached weight-two representation and its full verified Weil--Deligne parameter.

**Proof.** The representation and good-place assertions are Theorem 7.1. Finite-flat factorization is (9.1). Type factorization follows from Chapter 10 and Lemma 8.1. The inertia and monodromy statements are Theorems 11.1, 11.2, and 12.1. These local factorizations make $\rho_{\mathbb T}$ a point of the global functor, producing (13.2); Proposition 13.1 proves surjectivity. Generic specialization was built into Theorem 6.1. $\square$

The theorem constructs the map required for a later comparison of deformation and Hecke rings. It does not use or prove a numerical equality, patching freeness, or injectivity of (13.5).

### 13.5 Compatibility with inner-form comparison

Suppose the automorphic module is a $w$-new Shimura-curve lattice and the same packets occur on the switched definite quaternion algebra. Under the clean hypotheses of integral level change, the two faithful localized Hecke orders are equal inside their common reduced generic eigenvalue algebra:

$$
\mathbb T_{\mathrm{curve}}^{w\text{-new}}
=\mathbb T_{\mathrm{def}}.
\tag{13.6}
$$

Both Hecke-valued Galois representations have the same traces at every good Frobenius. Their common residual representation is absolutely irreducible. Strict-conjugacy uniqueness therefore identifies them over the common order. Thus (13.5) is independent of which of the two clean integral carriers is used.

This argument uses equality of faithful orders, not merely rational Jacquet--Langlands. If the two orders were only commensurable, each could support a representation, but no conclusion would identify their integral coefficient rings or congruence ideals.

## 14. Minimal and nonminimal levels

### 14.1 Two distinct deformation problems

A minimal datum $\mathcal D^{\min}$ and a nonminimal datum $\mathcal D^{\mathrm{nm}}$ have the same residual representation and determinant but different local conditions at one or more places. Their universal rings are therefore distinct objects:

$$
R_{\mathcal D^{\min}},
\qquad
R_{\mathcal D^{\mathrm{nm}}}.
$$

Likewise the lower-level Hecke order and the selected new/type Hecke order need not be related by an isomorphism or even by a canonical map. A level-raising congruence gives a common residual point and a characteristic-zero raised branch; it does not identify the two whole local rings.

Both problems have their own reciprocity maps whenever their clean automorphic data are supplied:

$$
R_{\mathcal D^{\min}}\twoheadrightarrow\mathbb T^{\min},
\qquad
R_{\mathcal D^{\mathrm{nm}}}\twoheadrightarrow\mathbb T^{\mathrm{nm}}.
\tag{14.1}
$$

The construction of the second does not assume the first is an isomorphism.

### 14.2 When a comparison map exists

If, at every place, the functor $\mathcal D_1$ is a subfunctor of $\mathcal D_2$, then there is a quotient map of representing rings

$$
R_{\mathcal D_2}\twoheadrightarrow R_{\mathcal D_1}.
\tag{14.2}
$$

The direction reverses inclusion of functors. Such a map must be justified place by place.

For example, the unramified condition may lie on the monodromy-zero boundary of an enhanced special closure only when its Frobenius eigenvalue ratio and sign satisfy the special incidence equation. An arbitrary minimal unramified deformation is not thereby a special deformation. Hence there is no automatic map between the minimal ring and a sign-selected special ring.

When inclusions are present and the automorphic level maps are compatible, the reciprocity maps form a commutative diagram because both paths send universal Frobenius traces to the same Hecke operators. Residual absolute irreducibility then identifies the specialized representations by strict conjugacy.

### 14.3 Level raising

At a clean prime $w\nmid\ell$, the saturated degeneracy map has free new quotient. If

$$
T_w\equiv\varepsilon(q_w+1)\pmod{\mathfrak m},
\qquad
q_w\not\equiv\pm1\pmod\ell,
\tag{14.3}
$$

the signed Gram vector produces a nonzero residual $w$-new class of sign $\varepsilon$. Finite flatness of the Hecke order over $\mathcal O$ lifts its maximal ideal to a characteristic-zero raised packet. Integral Jacquet--Langlands transfers the branch without a hidden congruence index.

Applying Theorem 13.2 to the selected new order gives its nonminimal Galois family and reciprocity map. The level-raising theorem supplies occurrence and a branch; the trace-descent theorem supplies the family over the entire localized order. Neither theorem alone gives the other's conclusion.

On a primitive multiplicity-one branch with unit companion factor, the exact congruence ideal is generated by

$$
q_w+1-\varepsilon a_w.
\tag{14.4}
$$

At higher multiplicity the Smith module replaces this scalar. The existence of (13.5) does not force a principal congruence ideal.

### 14.4 Level lowering

Suppose a residual new block has zero monodromy. Integral level lowering shows that it occurs at hyperspecial level only under the additional hypotheses: the block is nonzero and adjoint stable, the normalization middle piece is controlled, the localized component group has no $\varpi$-torsion, and the exceptional congruences are excluded.

In terms of Chapter 12, zero monodromy means that the residual point lies in

$$
V(\mathfrak m_w(N)).
$$

This equation alone is insufficient. The component group is the cokernel of the graph monodromy pairing and can obstruct lowering even when the rational conductor drops. Once the lowering theorem applies, the residual Hecke system occurs in the lower faithful order, and its lower-level Galois representation has the same residual trace by construction.

Level raising and lowering are therefore asymmetric. Raising uses a failure of unimodularity in the old Gram map; lowering uses monodromy vanishing after component obstructions have been removed.

The three relevant finite modules should not be merged. The cokernel of the saturated degeneracy map is torsion free and defines the new lattice. The cokernel of the old Gram operator measures failure of integral old--new orthogonality. The cokernel of the graph monodromy pairing is the localized component group. A fourth congruence index between the curve-new and definite orders is absent only because the integral comparison theorem proves equality of their faithful kernels.

The monodromy ideal $I_1(N)$ belongs to the Galois family. The graph pairing belongs to the semistable geometric carrier. Local--global compatibility relates their generic ranks, while integral level lowering needs the stronger comparison of their integral images and cokernels. This is why an order-valued monodromy formula is necessary but not, by itself, a level-lowering theorem.

### 14.5 Faithfulness boundaries

Several boundaries are now visible.

**Automorphic faithfulness.** Defining $\mathbb T$ as an image makes $M_{\mathfrak m}$ faithful. A quotient of an abstract Hecke algebra outside its support has no such property.

**Trace generation.** The Galois representation is coefficient-minimal over $\mathbb T^{\mathrm{tr}}$. An order enlarged by local operators need not be trace generated.

**Component coverage.** Lemma 8.1 proves a local relation only if every generic factor of the faithful order satisfies it. Checking one automorphic branch does not control the other branches through the same residual point.

**Generic versus integral faithfulness.** Equality of generic kernels does not imply equality of integral orders unless torsion-freeness or saturation descends the equality. The integral level-change theorem supplies this step in its clean range.

**Deformation faithfulness.** Surjectivity $R\twoheadrightarrow\mathbb T$ says that Hecke generators are realized by universal traces. It does not say that $\mathbb T$ detects every deformation or that the kernel is zero.

**Monodromy faithfulness.** A nonzero generic $N_{\mathbb T}$ can vanish at a residual or Artinian specialization. Its entry ideal, not the generic word “Steinberg,” describes this locus.

## 15. Exceptional primes and failure modes

### 15.1 Residual characteristic two

The trace-coordinate descent of Chapter 6 does not divide by $2$ and remains algebraically valid in characteristic two. The global nonminimal theorem does not automatically extend there.

For $d=2$ in characteristic two, the scalar matrix lies in $\operatorname{ad}^0\bar\rho$. The fixed-determinant tangent is

$$
\frac{Z^1(G,\operatorname{ad}^0\bar\rho)}
{d(\operatorname{ad}\bar\rho)},
$$

not simply $H^1(G,\operatorname{ad}^0\bar\rho)$, and the dual coefficient is $\operatorname{ad}\bar\rho/kI$. At real places the residual signs coincide, the projectors $(1\pm c)/2$ do not exist, and positive-degree cohomology need not vanish.

The clean finite-flat normal form also assumes $\ell>2$. Ramified quadratic positive-depth types in residue characteristic two are not tame. Therefore a two-adic theorem requires new real local conditions, the trace-kernel deformation complex, and an appropriate integral coefficient-prime theorem. None is inferred from the present odd-prime construction.

### 15.2 Residual characteristics three and five

The representation construction itself uses only residual absolute irreducibility, generic reducedness, and the weight-two branch attachment. The full integral one-prime nonminimal package retains $\ell\ge7$ because the available level-change theorem assumes it.

At $\ell=3$ or $5$, finite quotient orders can fail to be banal, Steinberg signs can meet, stabilizer denominators can cease to be units, and the congruences $q_w\equiv\pm1\pmod\ell$ occur more frequently. Reduction of a type lattice can become reducible or nonsemisimple. These facts do not prove that reciprocity is false; they show that saturation, type selection, and component coverage must be reverified.

If an independent integral comparison establishes all eight clean conditions of Section 2.5 at such a prime, Lemma 5.2, Theorems 6.1 and 7.1, and the reduced-order factorization lemma apply verbatim. What may not be imported is the $\ell\ge7$ level-change conclusion with its hypothesis erased.

### 15.3 Scalar and reducible residual systems

If $\bar\rho$ is reducible, the residual group algebra need not be $M_2(k)$ and the Gram matrix (6.2) can be singular. Traces then do not choose extension classes. For example,

$$
\begin{pmatrix}\chi_1&*\\0&\chi_2\end{pmatrix}
$$

has trace $\chi_1+\chi_2$ independent of $*$. A Hecke-valued pseudorepresentation can still exist, but Theorem 6.1 does not turn it into a unique free rank-two representation.

A scalar residual representation is the extreme case: every residual group matrix spans only the scalar line. One needs an ordinary filtration, a Cayley--Hamilton module with additional structure, or a different geometric construction. The non-Eisenstein terminology is insufficient unless it has been proved to imply absolute irreducibility in the precise block under study.

### 15.4 Nonreduced generic fibers

If $\mathbb T_E$ has nilpotents, its field-valued eigencharacters do not detect them. The product representation sees only the reduced quotient

$$
(\mathbb T_E)_{\mathrm{red}}.
$$

Frobenius interpolation then constructs at most a representation over the integral trace order inside that reduced quotient. It cannot manufacture matrices in invisible nilpotent directions.

In the clean automorphic setting, characteristic-zero semisimplicity of the faithful Hecke action rules out this problem. A special fiber may still be nonreduced; that is harmless for Lemma 8.1 because $\mathbb T$ injects into its reduced generic fiber. Nilpotents supported only modulo $\varpi$ can record congruence thickness without being generic nilpotents.

### 15.5 Primitive wild types and missing local models

The selected local-type theory covers principal, special, depth-zero dihedral, and positive-depth tame dihedral packets. It does not classify primitive wild supercuspidals or construct their integral compact types. Nor does a tame semistable chart identify wild descent.

At a place outside the verified local--global compatibility range, good-place trace identities give no bad-place inertial or monodromy theorem. One may still construct $\rho_{\mathbb T}$ from good Frobenius traces, because that construction is global. What fails is factorization through a claimed local condition. The honest conclusion is then a representation unramified outside the chosen controlling set, with the bad local restriction left unrestricted.

## 16. The theorem package and dependency audit

### 16.1 The complete theorem

**Theorem 16.1 (Hecke-valued reciprocity package).** Let $F$ be totally real, let $\mathcal O$ be the integers of a finite extension of $\mathbf Q_\ell$, and let $\mathfrak m$ be a localized weight-two Hecke maximal ideal with residue field $k$. Assume:

1. $\bar\rho:G_{F,S}\to\operatorname{GL}_2(k)$ is absolutely irreducible;
2. the central-component determinant $\delta=\chi_\ell^{-1}\eta$ is fixed;
3. the selected automorphic module is finite free over $\mathcal O$ and faithful for its away-from-$S$ Hecke image $\mathbb T$;
4. $\mathbb T_E$ is reduced and every one of its factors is a noncharacter parallel-weight-two packet in the established attachment range;
5. every branch has the stated integral coefficient-prime realization;
6. every nonminimal local place belongs to the controlled principal, special, or tame-dihedral range, with its integral primary and companion lattices, enhancement, geometric local--global comparison, and represented deformation component;
7. every integral inner-form or level change used to define the module satisfies the clean hypotheses of the integral comparison theorem.

Then:

$$
\rho_{\mathbb T}:G_{F,S}\longrightarrow\operatorname{GL}_2(\mathbb T)
$$

exists and is unique up to strict conjugacy; its trace algebra is $\mathbb T$; its determinant is $\delta$; and its good geometric-Frobenius polynomial is

$$
X^2-T_vX+q_vS_v.
$$

Every Artinian quotient satisfies the exact named local conditions. At finite-type places inertia is constant after strict conjugacy. At ordered principal places the line decomposition exists over $\mathbb T$. At special places there is a canonical monodromy operator up to unit scaling of the tame coordinate, satisfying

$$
N^2=0,
\qquad
\rho(\Phi)N\rho(\Phi)^{-1}=q^{-1}N,
$$

whose generic specializations are nonzero and whose vanishing modulo $I$ is measured by $I_1(N)\subseteq I$. Finally there is a surjection

$$
R_{\mathcal D^{\mathrm{nm}}}\twoheadrightarrow\mathbb T.
$$

For the one-prime integral level-raising, level-lowering, and inner-form assertions as a single package, retain $\ell\ge7$ and every nonexceptional, saturation, component-group, neatness, and selected-type hypothesis of the integral level-change theorem.

**Proof.** The generic branch representations come from weight-two attachment. The finite Galois Frobenius-selection theorem and Lemma 5.2 put their product trace in $\mathbb T$. The trace-coordinate algebra of Chapter 6 produces $\rho_{\mathbb T}$. Local--global compatibility and integral type detection place every generic branch on the named local components. The reduced-order lemma promotes those generic statements to the family and all its Artinian quotients. The coefficient-prime comparison gives finite-flat factorization. The inertia and monodromy calculations give the asserted local formulas. Universality gives the deformation-to-Hecke map, and trace generation proves its surjectivity. $\square$

### 16.2 Exact dependency ledger

The proof uses only the permitted packages, with the following exact roles.

| Source | Result used here | Hypotheses retained |
|---|---|---|
| Book 63, *Pseudocompact Trace Algebras and Carayol Descent* | Burnside trace coordinates, Azumaya splitting over a complete local ring, local Skolem--Noether, strict uniqueness | common residue field, completeness, residual absolute irreducibility; no division by $2$ |
| Book 67, *Finite-Flat Deformation Conditions at $\ell$* | represented framed finite-flat quotient, arbitrary coefficient base change, fixed-determinant clean power-series theorem | general representedness for finite $F_w/\mathbf Q_\ell$; smooth rank-two formula only for $\ell>2$ and unramified base |
| Book 68, *Global Deformation Problems* | represented global conditioned ring, framed local fiber products, variance of the universal map | finite controlling set, compatible determinant, represented base-change-stable local conditions, global Schur hypothesis |
| Book 91, *Hecke Algebras and Congruences* | finite-flat faithful image orders, localization and completeness, occurrence of generic characters, trace-order generation boundary | actual image on a finite-free module; no automatic special-fiber faithfulness, Hecke freeness, or Gorensteinness |
| Book 135, *Galois Representations Attached to Weight-Two Automorphic Forms* | branchwise rank-two attachment, determinant, good polynomials, integral lattices and finite-flat quotients | noncharacter parallel weight two in the stated curve or fully cancelled surface range; integral conclusions only with the integral realization datum |
| Book 136, *Local--Global Compatibility for Weight-Two Galois Representations* | full good, special, finite-descent, and tame-dihedral Weil--Deligne comparison | $w\nmid\ell$, verified models and correspondences, type projectors, monodromy and Frobenius return maps; surface case only with local and global cancellation |
| Book 157, *Integral Local Types and Type Lattices* | primary and companion lattices, saturation, ordered principal, enhanced special, fixed finite-type deformation rings | $w\nmid\ell$, unit-valued labels, tame quadratic range, stated banality and sign hypotheses; no primitive wild types |
| Book 159, *Integral Level Change and Jacquet--Langlands Comparison* | saturated old map, free new quotient, equality of faithful inner-form orders, level raising and lowering | clean proper Shimura-curve datum, $\ell\ge7$, non-Eisenstein localization, component and nonexceptional hypotheses |
| Book 193, *The Chebotarev Density Theorem* | finite Galois Frobenius selection with positive Dirichlet density and closed-condition transport | finite Galois extension, removal of a finite set, continuity, and a closed target condition; geometric form obtained by inversion |

Book 193 is used only for the density and transport theorem whose consequence was proved explicitly in Lemma 5.2. No later-numbered deformation--Hecke, support, or patching theorem is used.

### 16.3 Hypothesis ledger

| Conclusion | Necessary input | Boundary without it |
|---|---|---|
| traces lie in $\mathbb T$ | all good Frobenius traces in $\mathbb T$, continuity, finite-quotient density, closedness | branchwise integral tuples may miss the order |
| matrices lie in $M_2(\mathbb T)$ | residual absolute irreducibility, complete local order, reduced generic product | a character may have no unique free realization |
| determinant is $\delta$ | common cohomological pairing and central-component character | trace does not fix the chosen determinant in exceptional settings |
| all components satisfy a local condition | every generic factor verified, $\mathcal O$-flatness, reduced generic fiber | one checked branch or field-valued points do not detect the full order |
| finite flatness of every quotient | represented finite-flat condition and integral branch lattices | rational crystallinity or a stable lattice is insufficient |
| fixed finite inertia | prime-to-$\ell$ finite quotient and fixed integral model | inertia can deform when its order is divisible by $\ell$ |
| ordered principal factorization | automorphic line enhancement, or distinct residual characters | Weyl-conjugate components merge |
| special factorization | enhanced special closure and sign | $N\ne0$ is open and not quotient-stable |
| tame-dihedral factorization | quadratic descent character and Frobenius return map | inertial type leaves an unramified ambiguity |
| equality across inner forms | equality of faithful integral orders from saturated comparison | rational transfer permits a congruence index |
| surjectivity $R\to\mathbb T$ | trace generation by the $T_v$ and fixed determinant | added local operators may lie outside the trace order |
| level lowering | residual $N=0$, normalization control, component-group cleanliness, adjoint stability | conductor drop alone does not produce lower level |
| full clean nonminimal package | $\ell\ge7$ in the available integral level-change theorem | small-prime type and sign arguments require reproof |

### 16.4 Conclusion

The localized Hecke order is more than a list of congruent eigenvalues. It is the integral space on which the eigenbranches meet. Weight-two geometry first attaches a rank-two representation to each separated generic branch. Chebotarev density then shows that their characters obey the same integral gluing relations as the Hecke operators. Residual absolute irreducibility turns those character relations into a rank-four Azumaya algebra, and Henselian splitting supplies the common rank-two module. This produces the representation

$$
\rho_{\mathbb T}:G_{F,S}\to\operatorname{GL}_2(\mathbb T)
$$

without choosing an eigenvector or assuming an equality of deformation and Hecke rings.

The local conclusions are equally integral. At the coefficient prime, represented finite flatness carries every Artinian quotient. Away from it, primary and companion type lattices identify the correct characteristic-zero packets, full local--global compatibility supplies inertia, Frobenius, and monodromy, and reducedness promotes those branchwise identities to the whole order. Finite inertia becomes constant in the rigid prime-to-$\ell$ cases. Special monodromy becomes an actual matrix over $\mathbb T$, with a determinantal ideal recording where it dies under congruence.

These structures place the family in the exact nonminimal global deformation problem. Universality therefore gives the surjection

$$
R_{\mathcal D^{\mathrm{nm}}}\twoheadrightarrow\mathbb T.
$$

Its strength and its limit are now precise. The map realizes every Hecke trace and every named local condition, but it does not prove injectivity, freeness over the Hecke order, or component coverage beyond the verified automorphic module. Minimal and nonminimal levels remain different deformation problems; level raising supplies new branches, while level lowering requires monodromy and component control. Exceptional primes, nonreduced generic fibers, reducible residual systems, and primitive wild types remain outside the theorem unless their missing integral inputs are independently established.
