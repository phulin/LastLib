# Galois Representations Attached to Parallel-Weight-Two Automorphic Forms in the Curve-Realizable Range

## Contents

1. [The reciprocity question](#1-the-reciprocity-question)
   - [Automorphic scalars and Galois matrices](#11-automorphic-scalars-and-galois-matrices)
   - [The range of the theorem](#12-the-range-of-the-theorem)
   - [Frobenius, twists, and covariance](#13-frobenius-twists-and-covariance)
   - [The proof architecture](#14-the-proof-architecture)
2. [Weight-two packets and their coefficient fields](#2-weight-two-packets-and-their-coefficient-fields)
   - [Parallel weight two](#21-parallel-weight-two)
   - [Hecke data and the packet field](#22-hecke-data-and-the-packet-field)
   - [Central and component characters](#23-central-and-component-characters)
   - [Conjugates and splitting fields](#24-conjugates-and-splitting-fields)
3. [The curve-realizable carriers](#3-the-curve-realizable-carriers)
   - [Modular curves](#31-modular-curves)
   - [Quaternionic Shimura curves](#32-quaternionic-shimura-curves)
   - [A curve realization datum](#33-a-curve-realization-datum)
4. [Extracting rank two](#4-extracting-rank-two)
   - [Commuting actions](#41-commuting-actions)
   - [Why an eigenspace is not enough](#42-why-an-eigenspace-is-not-enough)
   - [The curve multiplicity space](#43-the-curve-multiplicity-space)
5. [Continuity, semisimplification, and uniqueness](#5-continuity-semisimplification-and-uniqueness)
   - [Continuity from cohomology](#51-continuity-from-cohomology)
   - [The canonical semisimple representation](#52-the-canonical-semisimple-representation)
   - [Chebotarev uniqueness](#53-chebotarev-uniqueness)
   - [Irreducible and reducible cases](#54-irreducible-and-reducible-cases)
6. [The good-place polynomial](#6-the-good-place-polynomial)
   - [The complete good-place ledger](#61-the-complete-good-place-ledger)
   - [From a correspondence relation to a characteristic polynomial](#62-from-a-correspondence-relation-to-a-characteristic-polynomial)
   - [The trace and determinant formulas](#63-the-trace-and-determinant-formulas)
   - [Arithmetic Frobenius and the covariant Tate module](#64-arithmetic-frobenius-and-the-covariant-tate-module)
7. [Determinant, duality, and oddness](#7-determinant-duality-and-oddness)
   - [The factored pairing](#71-the-factored-pairing)
   - [The determinant character](#72-the-determinant-character)
   - [Total oddness](#73-total-oddness)
   - [Normalization checks](#74-normalization-checks)
8. [Local--global compatibility away from the coefficient prime](#8-local--global-compatibility-away-from-the-coefficient-prime)
   - [Weil--Deligne comparison](#81-weil--deligne-comparison)
   - [Good and Steinberg places](#82-good-and-steinberg-places)
   - [Finite and dihedral types](#83-finite-and-dihedral-types)
   - [Conductors and local factors](#84-conductors-and-local-factors)
9. [Compatible systems and purity](#9-compatible-systems-and-purity)
   - [Weak compatibility](#91-weak-compatibility)
   - [Strict compatibility](#92-strict-compatibility)
   - [Purity of weight one](#93-purity-of-weight-one)
   - [Independence of choices](#94-independence-of-choices)
10. [Integral packet lattices](#10-integral-packet-lattices)
    - [Saturation before projection](#101-saturation-before-projection)
    - [Integral multiplicity extraction](#102-integral-multiplicity-extraction)
    - [Canonicity and its limits](#103-canonicity-and-its-limits)
    - [Residual representations](#104-residual-representations)
11. [Finite-flat coefficient quotients](#11-finite-flat-coefficient-quotients)
    - [The coefficient-prime carriers](#111-the-coefficient-prime-carriers)
    - [All open ideals](#112-all-open-ideals)
    - [Transition maps and ranks](#113-transition-maps-and-ranks)
    - [Duality and base change](#114-duality-and-base-change)
12. [Examples and counterexamples](#12-examples-and-counterexamples)
    - [An elliptic curve packet](#121-an-elliptic-curve-packet)
    - [An old packet](#122-an-old-packet)
    - [A scalar Frobenius](#123-a-scalar-frobenius)
    - [A residual extension](#124-a-residual-extension)
13. [The attachment theorem](#13-the-attachment-theorem)
    - [Statement](#131-statement)
    - [Proof](#132-proof)
    - [The range used in the Fermat argument](#133-the-range-used-in-the-fermat-argument)
14. [Hypothesis and dependency audit](#14-hypothesis-and-dependency-audit)
    - [Exact hypothesis ledger](#141-exact-hypothesis-ledger)
    - [Use of the five direct prerequisites](#142-use-of-the-five-direct-prerequisites)
    - [What the theorem does not say](#143-what-the-theorem-does-not-say)
15. [Conclusion](#15-conclusion)
    - [The completed arithmetic package](#151-the-completed-arithmetic-package)

## 1. The reciprocity question

### 1.1 Automorphic scalars and Galois matrices

A weight-two eigenpacket first appears as a collection of scalars. At every unramified finite place $v$ there are Hecke values $t_v$ and $s_v$, and hence a quadratic polynomial

$$
P_v(X)=X^2-t_vX+q_vs_v,
$$

where $q_v$ is the residue cardinality. A two-dimensional Galois representation is a very different-looking object: it assigns a matrix to every element of a profinite group. The reciprocity problem asks whether the polynomial above is the characteristic polynomial of Frobenius on one such representation.

The question has three logically separate parts. One must first construct a two-dimensional space on which Galois acts. One must then identify the trace and determinant of Frobenius. Finally, one must show that the constructions made at different coefficient primes are realizations of a single algebraic system, with the predicted behavior at bad places and with integral models at the coefficient prime.

Almost-everywhere Hecke values give rigidity, but not existence. Curve geometry gives existence. Modular and quaternionic Shimura curves carry continuous cohomological Galois actions, and algebraic Hecke correspondences commute with them. Automorphic decomposition identifies the desired packet inside $H^1$. The central difficulty is to remove automorphic multiplicity without discarding Galois information; the curve multiplicity space has rank two.

This book carries out the whole passage in the curve-realizable range. Its endpoint is not merely one representation at one prime. Under the respective determinant, local, and integral hypotheses, it is a pure compatible rank-two system with determinant, oddness, local Weil--Deligne parameters in the verified geometric range, canonical cohomological lattices, and finite-flat models for every required coefficient quotient.

### 1.2 The range of the theorem

Let $F$ be totally real. The automorphic input is a noncharacter cuspidal packet $\Pi$ of parallel weight two in one of the established curve-realizable ranges:

1. when $F=\mathbf Q$, a cuspidal weight-two eigensystem in the parabolic first cohomology of a compactified modular curve;
2. a noncharacter parallel-weight-two packet on a quaternion algebra split at exactly one real place, occurring in the first cohomology of a compact Shimura curve;
3. a selected packet on a totally definite quaternion algebra only when the established global transfer, including every ramified local-image condition, carries it to a split packet already realized by one of the preceding curve constructions.

The third clause is the totally-definite transfer range used in the FLT route. Equality of spherical eigenvalues away from finitely many places is not a substitute for global transfer, and a local component outside the discrete-series image blocks the transfer claim.

Parallel weight two is essential here. Constant-coefficient $H^1$ of a curve has Hodge types $(1,0)$ and $(0,1)$ and motivic weight one. Higher algebraic weights require nonconstant coefficient systems and different integral comparison statements. They are outside the theorem. Character packets are also excluded: on a compact quaternionic quotient, norm characters can have familiar-looking Hecke eigenvalues but do not produce the desired cuspidal rank-two factor.

The theorem is formulated for semisimple representations. An actual cohomological multiplicity space exists before semisimplification, but its extension class can depend on choices and cannot be recovered from Frobenius polynomials. Whenever irreducibility is known, semisimplification changes nothing.

### 1.3 Frobenius, twists, and covariance

Fix a finite place $u$ of the field over which the geometric carrier is defined. We write

$$
\Phi_u\in W_{F_u}
$$

for geometric Frobenius. Thus $\Phi_u$ acts on the Tate twist $E_\lambda(1)$ by $q_u^{-1}$. The associated cyclotomic character satisfies

$$
\chi_\lambda(\Phi_u)=q_u^{-1}.
$$

This is the convention used in the cohomological extraction and local comparison theorems. Under the curve determinant datum, the good-place characteristic polynomial is

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_us_v(\Pi), \tag{1.1}
$$

where $v$ is the corresponding automorphic place and the displayed form assumes equal residue fields. If $u/v$ has residue degree $f$, the two roots are raised to the $f$th power.

We use untwisted cohomological $H^1$ for the main normalization. The covariant Tate module of a Jacobian is instead

$$
T_\lambda J\otimes E_\lambda
\simeq H^1(C_{\overline F},E_\lambda(1)).
$$

Passing between these realizations changes both Frobenius and the Tate twist. Arithmetic Frobenius is $\Phi_u^{-1}$; its roots are the reciprocals of the roots in (1.1). One must not carry the same polynomial unchanged through this conversion.

### 1.4 The proof architecture

The construction has a fixed order.

First, isolate the full rational Hecke block and split its finite simple algebra. Second, remove its level multiplicity by a Hom construction, obtaining rank two. Third, when the curve determinant datum is available, use duality to determine the determinant, and only then upgrade the good-place quadratic annihilator to a characteristic polynomial in the scalar case. Fourth, run the construction over every coefficient completion and compare the resulting local parameters. Fifth, return to integral cohomology: saturate the packet block, perform integral multiplicity extraction, and construct all finite-flat coefficient quotients inside a fixed geometric or filtered carrier.

The order prevents four common circularities. Dimension is not inferred from the degree of an annihilating polynomial. The determinant is not inferred from the same quadratic relation used to identify the trace. An integral summand is not inferred from a rational projector. A two-dimensional Galois factor is not obtained by choosing one oldvector or one Hodge line.

## 2. Weight-two packets and their coefficient fields

### 2.1 Parallel weight two

At every real place of $F$, a parallel-weight-two cuspidal representation has the minimal cohomological discrete-series type. On a quaternionic group split at exactly one real place, that active factor contributes one holomorphic and one antiholomorphic cohomology line. Compact real factors contribute no further cohomological degree. Consequently the automorphic multiplicity space in curve $H^1$ has dimension two.

This dimension is independent of the number of oldvectors. If $\Pi_f^K$ has dimension $r$, the complete packet block has dimension $2r$, but it factors as

$$
P_{\Pi,\lambda}\otimes W_{\Pi,\lambda},
\qquad
\dim P_{\Pi,\lambda}=r,
\qquad
\dim W_{\Pi,\lambda}=2. \tag{2.1}
$$

The first factor records finite-level automorphic multiplicity. Galois acts on the second. Confusing the product with the second factor produces a false higher-dimensional representation at old level.

For modular curves, the same two Hodge lines lie in parabolic cohomology. If $j:Y\hookrightarrow X$ is the compactification, the relevant group is

$$
H^1_!(Y)=\operatorname{im}\bigl(H^1_c(Y)\to H^1(Y)\bigr).
$$

In weight two it agrees with the cuspidal part of $H^1(X)$. This removes the boundary characters which otherwise imitate reducible degree-two systems.

### 2.2 Hecke data and the packet field

Choose a finite set $S$ containing the ramified group, level, central-character, component, and bad-model places. The abstract spherical Hecke algebra away from $S$ acts through a character on $\Pi$. At an unramified place, we use the raw cohomological normalization

$$
P_v(X)=X^2-t_vX+q_vs_v. \tag{2.2}
$$

The coefficient field $E_0$ is generated by all $t_v$, $s_v$, the finite central and component values, and the finitely many algebraic local-type and return-map values needed at bad places. Fixed-level algebraicity makes $E_0$ a number field.

It is important to use the full finite Hecke image when isolating a packet. The commutative algebra generated only by good spherical operators may fail to distinguish oldvectors, component characters, or two lifts through a central extension. Finitely many good operators separate distinct global packets by multiplicity one, but central, component, and local-type data are retained to name the intended geometric block.

The values $t_v$ and $s_v$ are algebraic integers in the integral packet module. Their polynomial is independent of a coefficient completion. This is the algebraic core from which compatibility is built.

### 2.3 Central and component characters

The determinant is controlled by more than the ordinary central character on the split group. Geometric connected components can be permuted by Galois and by central Hecke correspondences. The extraction theorem packages these actions in a finite character

$$
\eta_\Pi:G_F\longrightarrow E_0^\times.
$$

After embedding $E_0$ in $E_\lambda$, its local realization is denoted $\eta_{\Pi,\lambda}$. Under the curve determinant datum, the cohomological geometric-Frobenius convention gives

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_{\Pi,\lambda}. \tag{2.3}
$$

At a good place, under the same datum,

$$
q_us_v=\chi_\lambda(\Phi_u)^{-1}\eta_{\Pi,\lambda}(\Phi_u).
$$

This identity is a normalization condition, not a consequence of notation. In the familiar modular case with trivial nebentype and no component twist, $s_v=1$ and the product of geometric-Frobenius roots is $q_v$. The arithmetic-Frobenius product on untwisted $H^1$ is $q_v^{-1}$; on the covariant Tate module it returns to $q_v$ after the Tate twist and duality are accounted for.

### 2.4 Conjugates and splitting fields

The Hecke field need not split the full finite Hecke algebra. A simple rational block can have a Schur division algebra. We therefore choose one finite extension

$$
E/E_0
$$

which splits every simple packet factor under consideration and contains the local type data. For a finite place $\lambda$ of $E$, write $E_\lambda$ for the completion and $\mathcal O_\lambda$ for its valuation ring.

Every embedding $\iota:E\hookrightarrow\mathbf C$ produces a coefficient-conjugate packet. Its good polynomial is obtained by applying $\iota$ to (2.2), and the geometric decomposition contains this conjugate block. Thus changing a coefficient embedding changes all of $t_v$, $s_v$, $\eta_\Pi$, and the bad local data together.

The extension $E/E_0$ is a field of realization, not an assertion that $E_0$ was inadequate as a trace field. The semisimple system is determined over its trace field up to the usual descent obstruction. Enlarging $E$ does not change the underlying compatible system; it makes its multiplicity modules honest vector spaces and its local types simultaneously visible.

## 3. The curve-realizable carriers

### 3.1 Modular curves

Let $X/\mathbf Q$ be a compactified modular curve with sufficiently fine level and let $J$ be its Jacobian. Algebraic Hecke correspondences extend across the cusps, act on $J$, and commute with Galois. The weight-two cuspidal packet lies in parabolic $H^1$ and therefore in the Jacobian realization. In the theorem below this is the $F=\mathbf Q$ branch; base change of the curve alone is not asserted to realize an arbitrary packet over a larger totally real field.

The boundary must be removed before extraction. Ordinary cohomology of the open modular curve contains classes whose Hecke polynomials factor as characters. On the compactification, the cuspidal part is self-dual and carries the weight-one pairing. This is the correct receptacle for a cuspidal rank-two representation.

At a fine level, the correspondence legs are finite and the component action is literal. At coarse level, one passes through a fine normal cover. Rational invariants recover the desired block, but integral recovery requires the deck-group order and every averaging denominator to be units at $\lambda$, unless a direct integral comparison is supplied.

The modular carrier is especially useful at the coefficient prime. A quotient of $J$ with good reduction can extend to an abelian scheme, whose torsion supplies finite-flat models. Yet an isogeny factor cut out only by a rational idempotent need not extend integrally. The integral theorem therefore names the coefficient action and the unit-degree comparison as hypotheses.

**Proposition 3.1 (modular-curve realization).** Let $X/\mathbf Q$ be a compactified modular curve with sufficiently fine level, and let $\Pi$ be a cuspidal weight-two packet whose finite new line or specified type occurs in its parabolic cohomology. After the finite Hecke block is split, the $\Pi$-block factors as a finite automorphic module tensored with a continuous two-dimensional Galois module. Its Hodge types are $(1,0)$ and $(0,1)$, and its integral packet lattice is the saturated intersection with integral parabolic cohomology.

**Proof.** Over $\mathbf C$, harmonic representatives identify parabolic cohomology with the cuspidal discrete spectrum. The weight-two archimedean representation contributes one holomorphic differential and its antiholomorphic conjugate, hence two cohomological dimensions. Global multiplicity one gives one automorphic occurrence. Any dimension contributed by level raising remains in the finite fixed-vector module, so the complete block has the tensor shape (2.1).

The Hecke correspondences extend to the compactification and preserve the image of compactly supported cohomology. Their action is adjoint-stable under Poincaré duality, so the finite characteristic-zero image is semisimple. A finite coefficient extension splits its simple factor. The double-centralizer evaluation map then extracts the two-dimensional multiplicity space. Since every correspondence descends to the stated field, it commutes with Galois, and the multiplicity space is Galois stable and continuous.

Betti--de Rham comparison carries the two harmonic lines to Hodge types $(1,0)$ and $(0,1)$. Intersecting the rational block with the torsion-free integral cohomology lattice gives a primitive submodule, by the saturation argument of Section 10.1. Boundary characters do not enter because the extraction was performed in parabolic cohomology. $\square$

### 3.2 Quaternionic Shimura curves

Let $B/F$ be a quaternion division algebra split at exactly one real place, and let $C_K$ be a smooth projective, Galois-stable, Hecke-stable union of components of the associated Shimura curve. Compactness removes cusps. The automorphic decomposition of its constant-coefficient $H^1$ contains exactly the noncharacter parallel-weight-two packets.

After a splitting field is chosen, a packet block has the form (2.1). The finite simple module $P_{\Pi,\lambda}$ carries the Hecke and oldvector multiplicity; the rank-two space $W_{\Pi,\lambda}$ carries Galois. Poincaré duality pairs the packet with its adjoint, and the good special-fiber correspondence yields the quadratic relation used later.

Transfer to or from the split group is used only when every ramified local component lies in the established local packet. A maximal representation at a division place may transfer to a Steinberg representation on the split side. This explains how a geometrically compact carrier can produce nonzero monodromy at a split level place without making maximal level synonymous with unramifiedness.

The natural integral $H^1$ lattice is finite free and stable under Galois and Hecke. Its intersection with a rational packet block is saturated. This gives a canonical packet lattice relative to the chosen curve, but not yet a canonical rank-two Morita factor.

### 3.3 A curve realization datum

A **curve realization datum** for $\Pi$ consists of a modular or quaternionic curve with its cuspidal packet block, together with:

- a Galois- and Hecke-stable component union defined over the field on which the representation is claimed;
- the full finite adjoint-stable Hecke image and a splitting field;
- a simple finite Hecke module and an evaluation isomorphism producing a rank-two multiplicity space;
- the adjoint packet and the central-component character $\eta_\Pi$;
- for determinant and scalar-Frobenius conclusions, the curve determinant datum of Book 134: the descended component twist with its Galois covariance and a polarization-compatible symmetric pairing on the finite Hecke module;
- good integral models and normalized correspondences at the places where the good polynomial is claimed;
- the verified semistable, finite-descent, or dihedral geometric packages at bad places where full local comparison is claimed, including the passage from the raw cohomological multiplicity space to the chosen global semisimplification.

An **integral curve realization datum** adds a finite-free ambient lattice, split integral Hecke order, projective integral generator, integral evaluation and pairing, coefficient-prime carrier, and unit-degree comparison maps. These additions solve independent problems; none follows formally from the rational datum.


## 4. Extracting rank two

### 4.1 Commuting actions

Let $H_\lambda$ be the relevant cohomology over $E_\lambda$. Galois acts continuously, while algebraic correspondences give a finite Hecke image $A_\lambda$. Because the correspondences and component union descend to the ground field,

$$
g(ah)=a(gh)
\qquad
(g\in G_F,\ a\in A_\lambda,\ h\in H_\lambda). \tag{4.1}
$$

This commutation makes every central Hecke block Galois stable. It also makes the Hom space

$$
\operatorname{Hom}_{A_\lambda}(P_\lambda,H_\lambda)
$$

a Galois representation by

$$
(g\cdot f)(p)=g(f(p)). \tag{4.2}
$$

The formula is well typed precisely because Galois commutes with $A_\lambda$ and acts trivially on the chosen finite Hecke module $P_\lambda$.

It is not enough that automorphic forms and cohomology happen to have equal eigenvalues. The operators on cohomology must be the descended pull--trace correspondences representing the same double cosets. That geometric identification fixes variance, stabilizer multiplicities, central scalars, and the action on connected components.

### 4.2 Why an eigenspace is not enough

At characteristic zero, a semisimple finite Hecke algebra decomposes into blocks. Integrally, congruent branches can meet. If two characteristic-zero eigencharacters are congruent modulo $\lambda$, the rational projector separating them may have a nonunit denominator. The localized integral module contains both branches and possible nilpotent extensions.

Old level causes a different enlargement. If a newform is viewed one unramified level higher, two degeneracy vectors have the same Hecke values away from the new place. The total eigenspace is four-dimensional, even though the associated Galois representation remains two-dimensional. A local new quotient, a type operator, or the full finite simple Hecke module is required to remove this multiplicity.

Thus three constructions must remain distinct: the ordinary characteristic-zero eigenspace, the generalized eigenspace, and the localized integral congruence block. After scalar extension they can be compared inside one ambient cohomology space, but the integral localization is not literally another characteristic-zero eigenspace.

The rational attachment uses the complete simple block and its multiplicity space. The canonical integral construction begins with the saturated block, not an ordinary eigenline.

### 4.3 The curve multiplicity space

Let $e_\Pi$ be the rational central idempotent of the full finite Hecke image, let $A_{\Pi,\lambda}=e_\Pi A_\lambda$, and choose a simple left module $P_{\Pi,\lambda}$. Define

$$
W_{\Pi,\lambda}
=\operatorname{Hom}_{A_{\Pi,\lambda}}
(P_{\Pi,\lambda},e_\Pi H_\lambda). \tag{4.3}
$$

The automorphic decomposition gives an evaluation map

$$
P_{\Pi,\lambda}\otimes W_{\Pi,\lambda}
\longrightarrow e_\Pi H_\lambda,
\qquad p\otimes f\longmapsto f(p), \tag{4.4}
$$

and the double-centralizer theorem makes it an isomorphism. The archimedean calculation gives

$$
\dim_{E_\lambda}W_{\Pi,\lambda}=2. \tag{4.5}
$$

Continuity follows because the Hom equations are finitely many closed linear equations in a finite-dimensional continuous representation. This proves existence without choosing an automorphic eigenvector.

The construction is invariant under replacing $P$ by an isomorphic simple module. Changing a matrix splitting changes coordinates by an inner automorphism and hence gives an isomorphic Hom space. A finite extension of coefficients commutes with (4.3).

**Proposition 4.1 (rank-two curve extraction).** Under the curve realization hypotheses, (4.3) is a continuous two-dimensional Galois representation, and evaluation (4.4) is an isomorphism of Hecke--Galois bimodules.

**Proof.** After the finite semisimple algebra is split, its packet block is a sum of copies of one simple module $P$. Write it abstractly as $P^{\oplus m}$. Then

$$
\operatorname{Hom}_A(P,P^{\oplus m})
\simeq\operatorname{End}_A(P)^{\oplus m}.
$$

The splitting convention makes $\operatorname{End}_A(P)=E_\lambda$, and evaluation reconstructs $P^{\oplus m}$. Thus (4.4) is an isomorphism. The automorphic decomposition computes $m=2$: global multiplicity is one, while the unique active real factor supplies the two orientation classes. This also proves (4.5).

For Galois stability, if $f$ is $A$-linear, then for $a\in A$,

$$
(g\cdot f)(ap)=g(f(ap))=g(af(p))=a(g\cdot f)(p),
$$

using (4.1). Hence (4.2) remains in the Hom space. Its defining equations are closed, so the inherited action is continuous. Finally, evaluation is Galois equivariant because $g(f(p))=(g\cdot f)(p)$. $\square$

## 5. Continuity, semisimplification, and uniqueness

### 5.1 Continuity from cohomology

The ambient cohomology is the inverse limit of finite coefficient groups, with its natural adic topology, and Galois acts continuously. A central Hecke block is a closed subspace because it is the image of an idempotent. A multiplicity Hom space is closed because it is the kernel of finitely many maps expressing $A$-linearity. Hence the extracted Galois action is continuous.

Equivalently, choose any stable lattice $L$ in the extracted space. For each $n$, the action on $L/\varpi_\lambda^nL$ has finite image and open kernel. The original action is their inverse limit. This second description is useful integrally, but it should not be used to declare the chosen lattice canonical.

Finite ramification also comes from geometry. Outside the coefficient prime, level, group discriminant, component character, and bad-model places, smooth proper specialization kills inertia. The extracted subquotient is therefore unramified outside a finite set independent of the individual good place.

### 5.2 The canonical semisimple representation

The raw multiplicity space can have a nontrivial extension filtration. Its Jordan--Hölder semisimplification is canonical and preserves the trace and determinant of every Galois element. We define

$$
\rho_{\Pi,\lambda}:G_F\longrightarrow
\operatorname{GL}_2(E_\lambda)
$$

to be this continuous semisimple representation, after coefficient extension if required by the splitting field.

Semisimplification does not mean that every group element is diagonalizable. A semisimple representation of the global group may restrict nonsemisimply to a decomposition group, and at a Steinberg place its Weil--Deligne monodromy is deliberately nonzero.

On the other hand, passage from the raw global multiplicity space to its global semisimplification can erase monodromy when that monodromy is carried by a globally nonsplit extension. Local comparison is therefore first computed on the raw cohomological Hom space. A statement for $\rho_{\Pi,\lambda}$ retains the additional verification that the identified local parameter survives global semisimplification; global irreducibility is one sufficient case. This is distinct from Frobenius semisimplification of a Weil--Deligne pair, which retains $N$.

### 5.3 Chebotarev uniqueness

**Proposition 5.1.** Let $\rho_1$ and $\rho_2$ be continuous semisimple representations of $G_F$ over a characteristic-zero local field, unramified outside finite sets. If their characteristic polynomials agree at all but finitely many places, then $\rho_1\simeq\rho_2$.

**Proof.** Frobenius conjugacy classes outside a finite set are dense. Equality of their traces extends by continuity to equality of trace on all of $G_F$. The characteristic of a finite-dimensional characteristic-zero representation determines its semisimplification. Since both representations are semisimple, they are isomorphic. $\square$

This proposition compares modular-curve and quaternionic-curve realizations once their descent fields agree and their good polynomials agree on a dense set. It compares semisimple representations only. It does not compare integral lattices or nonsplit residual extensions.

### 5.4 Irreducible and reducible cases

The attachment theorem does not assume irreducibility. If

$$
\rho_{\Pi,\lambda}=\alpha_\lambda\oplus\beta_\lambda,
$$

the good polynomials determine the unordered pair of characters and, under the curve determinant datum, the determinant forces

$$
\alpha_\lambda\beta_\lambda
=\chi_\lambda^{-1}\eta_{\Pi,\lambda}.
$$

They do not determine an extension of one character by the other.

If $\rho_{\Pi,\lambda}$ is absolutely irreducible, its endomorphism algebra is the coefficient field. Descent from a splitting extension and independence of the chosen multiplicity coordinates are then especially transparent. Absolute residual irreducibility is stronger and has an integral consequence: all stable lattice reductions are isomorphic, whereas in the reducible case only their semisimplifications are canonical.

A single Frobenius polynomial irreducible over the residue field proves irreducibility over that field but not necessarily absolute irreducibility. Over the algebraic closure the polynomial splits. To prove absolute irreducibility one must exclude one common invariant line for the whole residual image, for example using two group elements with incompatible eigenlines.

## 6. The good-place polynomial

### 6.1 The complete good-place ledger

Let $u\nmid\ell$ be a place of the geometric field, corresponding to an automorphic place $v$. We call $u$ **good for the curve realization datum** only when all of the following hold:

- the group, order, polarization, and level are unramified and hyperspecial;
- the selected component union extends and remains stable under Frobenius and Hecke;
- the curve has the required smooth projective integral model;
- the two legs of the normalized Hecke correspondence extend as finite correspondences;
- the coefficient lattice is self-dual in the sense used by the model;
- the packet projector commutes with specialization;
- the central and component characters are unramified;

Under these hypotheses smooth proper base change gives trivial inertia. The special-fiber correspondence gives an operator identity. Neither conclusion follows merely from the word “hyperspecial” attached to the abstract automorphic representation.

At a modular cusp, one also checks that compactification and the extension of the correspondence preserve parabolic cohomology. At coarse level, descent from the fine cover is harmless rationally, while an integral assertion retains the denominator qualification.

### 6.2 From a correspondence relation to a characteristic polynomial

On the rank-two multiplicity space, the good correspondence gives

$$
\rho(\Phi_u)^2-t_v\rho(\Phi_u)+q_us_v=0. \tag{6.1}
$$

This says that $P_v$ annihilates Frobenius. An annihilating polynomial need not be the characteristic polynomial when Frobenius is scalar. Under the curve determinant datum, the determinant obtained independently from duality supplies the missing coefficient.

**Lemma 6.1.** Let $T$ be an invertible operator on a two-dimensional vector space. Suppose

$$
T^2-aT+d=0
$$

and $\det T=d$. Then the characteristic polynomial of $T$ is $X^2-aX+d$.

**Proof.** Write the characteristic polynomial as $X^2-cX+d$. Cayley--Hamilton gives $T^2-cT+d=0$. Subtracting the two relations yields $(c-a)T=0$. Since $T$ is invertible, $c=a$. $\square$

Under that datum, applying the lemma to (6.1) proves (1.1), including the repeated-root case. This order of proof is essential: the geometric relation alone does not identify the trace of a scalar Frobenius. Without the datum, (6.1) is already the characteristic polynomial when Frobenius is nonscalar and remains only an annihilator in the scalar case.

### 6.3 The trace and determinant formulas

Assume the curve determinant datum. At every good place with equal residue fields,

$$
\operatorname{tr}\rho_{\Pi,\lambda}(\Phi_u)=t_v,
\qquad
\det\rho_{\Pi,\lambda}(\Phi_u)=q_us_v. \tag{6.2}
$$

These values lie in $E$ before completion at $\lambda$. They are preserved by coefficient conjugation and by change of curve carrier. If $u/v$ has residue degree $f$ and the roots at $v$ are $\alpha_v,\beta_v$, then the polynomial at $u$ is

$$
(X-\alpha_v^f)(X-\beta_v^f). \tag{6.3}
$$

The determinant formula checks the central normalization. If $s_v=1$, the roots multiply to $q_v$, as weight-one geometric cohomology requires. Replacing $s_v$ by its inverse without also changing the Hecke convention would contradict the pairing.

The local Euler polynomial uses the same geometric-Frobenius convention:

$$
P_v^{\mathrm{loc}}(T)
=\det(1-\Phi_vT\mid(\ker N)^{I_v}). \tag{6.4}
$$

At a good place this is $1-t_vT+q_vs_vT^2$.

### 6.4 Arithmetic Frobenius and the covariant Tate module

Arithmetic Frobenius is $\Phi_v^{-1}$. If (1.1) has roots $\alpha_v,\beta_v$, then arithmetic Frobenius on the same untwisted cohomology has roots $\alpha_v^{-1},\beta_v^{-1}$ and polynomial

$$
X^2-\frac{t_v}{q_vs_v}X+\frac{1}{q_vs_v}. \tag{6.5}
$$

The covariant Tate module introduces the twist $(1)$ and the standard comparison with the dual. In the classical elliptic-curve normalization it has arithmetic-Frobenius polynomial

$$
X^2-a_vX+q_v.
$$

There is no contradiction: the two representations differ by the precise dual and twist appearing in the Jacobian comparison.

Three tests keep the convention stable. A Tate twist $(n)$ multiplies geometric-Frobenius roots by $q_v^{-n}$. Duality inverts roots. A finite character twist $\xi$ multiplies the trace by $\xi(\Phi_v)$ and the determinant by its square. Any conversion must pass all three tests.

## 7. Determinant, duality, and oddness

### 7.1 The factored pairing

Poincare duality pairs the curve packet block with its adjoint packet into $E_\lambda(-1)$. Factoring through the finite Hecke module therefore gives unconditionally a perfect pairing between the two multiplicity spaces. It does not by itself give an alternating self-pairing of $W_{\Pi,\lambda}$.

For the determinant assertions, retain the curve determinant datum of Book 134. Its descended component twist identifies the adjoint multiplicity space with $W_{\Pi,\lambda}\otimes\eta_{\Pi,\lambda}^{-1}$, and its polarization-compatible symmetric form on the finite module leaves the alternating sign on the multiplicity factor. Only under this datum do we obtain

$$
\langle\ ,\ \rangle_\Pi:
W_{\Pi,\lambda}\times W_{\Pi,\lambda}
\longrightarrow E_\lambda(-1)\otimes\eta_{\Pi,\lambda}. \tag{7.1}
$$

The symmetry clause matters at old level: the sign of a finite-module pairing cannot be inferred from its dimension. Likewise, equality of central eigenvalues does not replace the descended twisting correspondence and its Galois covariance.

### 7.2 The determinant character

For a two-dimensional vector space, the multiplier of a nondegenerate alternating similitude is its determinant. Under the curve determinant datum, applying this linear-algebra fact to (7.1) gives

$$
\boxed{\det\rho_{\Pi,\lambda}
=\chi_\lambda^{-1}\eta_{\Pi,\lambda}.} \tag{7.2}
$$

This proves the determinant on every Galois element, not only on good Frobenius classes. Conversely, evaluating (7.2) at a good place gives $q_vs_v$, and then Lemma 6.1 identifies the trace. Thus duality and the geometric correspondence audit one another without circularity.

The duality is

$$
\rho_{\Pi,\lambda}^\vee
\simeq
\rho_{\Pi,\lambda}(1)\otimes\eta_{\Pi,\lambda}^{-1}. \tag{7.3}
$$

This is essential self-duality, not ordinary self-duality. Scaling the pairing by a nonzero coefficient changes neither its multiplier nor (7.2).

### 7.3 Total oddness

Let $c_\tau$ be complex conjugation at a real place $\tau$ of $F$, and assume the individual coefficient block is preserved by the real descent action. The weight-two Hodge structure has one $(1,0)$ line and one $(0,1)$ line. Complex conjugation exchanges them. Therefore its eigenvalues on the rank-two realization are $1$ and $-1$, so

$$
\operatorname{tr}\rho_{\Pi,\lambda}(c_\tau)=0,
\qquad
\det\rho_{\Pi,\lambda}(c_\tau)=-1. \tag{7.4}
$$

When the preservation hypothesis holds at every real place, the representation is totally odd. It is also consistent with (7.2), because the parity of the finite component character is the one forced by the cohomological packet.

Oddness is not the assertion that complex conjugation acts by $-1$ on the whole space; that scalar has determinant $+1$. In residue characteristic two the two eigenvalues become equal, so oddness is first a characteristic-zero statement and is not detected by the residual determinant alone.

If the curve is initially defined over a reflex field larger than $F$, total oddness is claimed only after the component descent data produce a representation of $G_F$. Parity is not defined at a complex place.

### 7.4 Normalization checks

The following four calculations are decisive.

1. With trivial component character, geometric Frobenius has determinant $q_v$ and the global determinant is $\chi_\lambda^{-1}$.
2. Arithmetic Frobenius on untwisted cohomology has reciprocal roots; its determinant is $q_v^{-1}$.
3. Twisting by a finite character $\xi$ multiplies $t_v$ by $\xi(\Phi_v)$, $s_v$ by $\xi(\Phi_v)^2$, and the determinant character by $\xi^2$.
4. A Tate twist by $(n)$ changes the weight by $-2n$ in the geometric-Frobenius convention and multiplies the determinant by $\chi_\lambda^{2n}$.

These checks separate central inversion, Frobenius inversion, duality, and Tate twisting. No two should be silently combined.

## 8. Local--global compatibility away from the coefficient prime

### 8.1 Weil--Deligne comparison

Let $u\nmid\ell$. Quasi-unipotence of inertia associates to $\rho_{\Pi,\lambda}|_{G_{F_u}}$ a Frobenius-semisimple Weil--Deligne pair

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\text{-}ss}}
=(r_{u,\lambda},N_{u,\lambda}),
$$

with

$$
r(\Phi_u)N r(\Phi_u)^{-1}=q_u^{-1}N. \tag{8.1}
$$

Local--global compatibility means equality of this complete pair with the algebraically normalized local parameter of $\Pi_v$. Equality of conductor or inertial type alone is weaker. A finite type leaves an unramified Frobenius-return ambiguity, while conductor one does not distinguish finite tame ramification from nonzero monodromy.

The geometric proof uses the equivariant nearby-cycle complex. Hecke projectors commute with restriction, Gysin, finite descent, Frobenius, and monodromy. The curve Hom extraction passes through this complex on the raw multiplicity space. The local packages invoked below also retain the raw-to-global-semisimplification verification of Section 5.2 whenever the conclusion is stated for $\rho_{\Pi,\lambda}$.

### 8.2 Good and Steinberg places

At a good place, inertia is trivial, $N=0$, and the parameter is determined by (1.1). This is full unramified compatibility.

At a verified split strict semistable curve place, the dual graph controls monodromy on $H^1$. After packet extraction, $N^2=0$. If the packet graph line vanishes, the representation is unramified even when the whole model is singular. If it survives, $N$ has rank one. The normalized bad correspondence computes Frobenius on $\ker N$, and the pair is a special parameter

$$
\operatorname{St}(\beta_v).
$$

Under the model-level Steinberg hypotheses, $\beta_v$ equals the automorphic bad-Hecke scalar. Then the conductor exponent is one and

$$
P_v^{\mathrm{loc}}(T)=1-\beta_vT. \tag{8.2}
$$

Split and nonsplit multiplicative cases can have the same inertia and conductor but opposite $\beta_v$. The Frobenius scalar is therefore indispensable.

### 8.3 Finite and dihedral types

If strict semistability is achieved only after a finite Galois extension, the descent action on the entire stratum complex recovers finite inertia. A type projector identifies the inertial representation, and Frobenius return maps complete it to a Weil representation. When $N\ne0$, the same data give a ramified special parameter.

For a verified tame dihedral place, a quadratic cover and character projector produce

$$
D_v=\operatorname{Ind}_{W_L}^{W_{F_v}}\theta_v,
\qquad N=0. \tag{8.3}
$$

The quadratic extension, inducing character, vanishing of monodromy, and Frobenius return scalar are all hypotheses. Merely observing two tame inertial characters does not determine the induced parameter.

Wild inertia is included only when the full finite descent action with its ramification filtration is supplied. A tame chart cannot determine the Swan conductor.

### 8.4 Conductors and local factors

Once the pair $(r,N)$ is identified, the local invariants follow. The Euler factor is computed from $(\ker N)^{I_u}$ as in (6.4). The Artin conductor is

$$
a(r,N)=a(r)+\dim V^{I_u}-\dim(\ker N)^{I_u}. \tag{8.4}
$$

The Swan conductor is the wild part of $a(r)$. Epsilon factors agree after fixing the same additive character and self-dual measure on both sides.

These invariants are consequences of the complete parameter, not substitutes for it. Two local representations may have equal conductor and Euler factor but different finite inertia or different Frobenius return maps. The attachment theorem therefore asserts them only in the places covered by the complete geometric comparison package.

No statement in this chapter concerns $u\mid\ell$. Prime-to-residue-characteristic nearby cycles do not prove crystalline, semistable, or finite-flat properties at the coefficient prime.

## 9. Compatible systems and purity

### 9.1 Weak compatibility

Assume the curve determinant datum. For every finite place $\lambda$ of $E$, the multiplicity construction gives $\rho_{\Pi,\lambda}$. Choose a finite set $S$ containing every group, level, component, character, model, and correspondence exception. Then for $v\notin S$ and $v\nmid\ell(\lambda)$, the representation is unramified and

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_v))
=P_v(X)\in E[X]. \tag{9.1}
$$

The set $S$ and the polynomial do not depend on $\lambda$. This is weak compatibility. Several places $\lambda$ above the same rational prime are separate members; compatibility compares them through $E$, not through a canonical isomorphism of their local coefficient fields.

Coefficient conjugation also commutes with the construction. If $\sigma:E\hookrightarrow\overline{\mathbf Q}$, then the conjugate packet has polynomials $\sigma(P_v)$, and its $\sigma\lambda$-adic representation is the scalar-conjugate semisimple representation.

### 9.2 Strict compatibility

At a finite place $v$, suppose one of the uniform local geometric packages of Chapter 8 is supplied over $E$: unramified, special, finite descent, or tame dihedral, including the required passage to the global semisimplification. Let $D_v$ be the resulting algebraic Weil--Deligne parameter. Then for every $\lambda$ with $v\nmid\ell(\lambda)$,

$$
\operatorname{WD}_v(\rho_{\Pi,\lambda})^{\mathrm{F\text{-}ss}}
\simeq D_v\otimes_EE_\lambda. \tag{9.2}
$$

This is strict compatibility at $v$. If the selected packet range supplies such a package at every finite place, the family is strictly compatible everywhere away from the varying coefficient residue characteristic.

It follows that the prime-to-$\lambda$ conductor is obtained from one common conductor datum by omitting the factors above $\ell(\lambda)$. Euler factors, Swan conductors, monodromy ranks, and normalized epsilon factors are independent of $\lambda$ in the same range.

**Proposition 9.1 (assembly of the compatible family).** Suppose the curve realization datum, including its determinant datum, is available for every coefficient embedding and the local packages are defined over $E$. Then the representations $\{\rho_{\Pi,\lambda}\}_\lambda$ form a weakly compatible system, strictly compatible at every place carrying one of those local packages.

**Proof.** Fixed-level algebraicity puts all $t_v$ and $s_v$ in one number field and places every conjugate packet in the corresponding conjugate Hecke block. There are only finitely many places where the group, level, component character, carrier, or normalized correspondence is bad. Their union is a set $S$ independent of $\lambda$. For $v\notin S$ and $v\nmid\ell(\lambda)$, the good-place argument gives (9.1), proving weak compatibility.

At a fixed bad place away from $\ell(\lambda)$, the restriction--Gysin complex, finite descent action, bad correspondence, and return maps are algebraic correspondences or algebraic character data over $E$. Scalar extension to $E_\lambda$ therefore commutes with their kernels, images, monodromy, and packet Hom spaces. The local recognition argument identifies the result with $D_v\otimes_EE_\lambda$, proving (9.2). The local invariants are functorial expressions in $(r,N)$, so they are independent of $\lambda$. $\square$

### 9.3 Purity of weight one

At a good place, the rank-two curve factor is a direct multiplicity factor of smooth projective $H^1$. Every complex embedding of every root $\alpha_v$ of $P_v$ therefore satisfies

$$
|\alpha_v|=q_v^{1/2}. \tag{9.3}
$$

This is purity of weight one. It passes to coefficient conjugates because the statement concerns all complex embeddings.

At a verified bad place, purity is expressed by the monodromy filtration. For a special parameter the two Frobenius lines have weights differing by two and centered at one. Finite-monodromy parameters have the corresponding common absolute value after the local normalization. The nearby-cycle weight calculation proves this only under its stated semistability and degeneration hypotheses.

Purity gives the bound

$$
|\sigma(t_v)|\le 2q_v^{1/2}
$$

for every complex embedding $\sigma$. The determinant alone would give only the product of the two absolute values and cannot replace purity.

### 9.4 Independence of choices

The system is independent, up to isomorphism, of bases, matrix coordinates, splitting presentations, and scaling of the polarization. Morita functoriality handles the first three, and the determinant multiplier is unchanged by scaling the alternating form.

Independence from a geometric carrier is stronger. It follows rationally when both carriers descend to the same field, their good Frobenius polynomials agree on a dense set, and both rank-two extractions have been constructed. Proposition 5.1 then compares their semisimplifications. This argument does not identify their integral lattices.

Integral carrier independence requires correspondences whose two composites have coefficient-unit degree, or another direct integral identification. An isogeny of degree divisible by $\lambda$ can preserve the rational representation while changing the lattice and its residual extension.

## 10. Integral packet lattices

### 10.1 Saturation before projection

Let $H_{\mathcal O}$ be the finite-free integral cohomology lattice and $H_\Pi\subset H_{\mathcal O}\otimes E_\lambda$ the rational packet block. Define

$$
M_{\Pi,\lambda}=H_{\mathcal O}\cap H_\Pi. \tag{10.1}
$$

The intersection is saturated: if $ax\in M$ for a nonzero $a\in\mathcal O_\lambda$ and $x\in H_{\mathcal O}$, then $x\in H_\Pi$ because $H_\Pi$ is a vector subspace, hence $x\in M$. Over a discrete valuation ring, a saturated submodule of a finite-free module is finite free and has torsion-free quotient.

Because both the ambient lattice and rational block are Galois and Hecke stable, so is $M_{\Pi,\lambda}$. The construction depends only on the rational subspace and the named ambient integral carrier, not on a formula for its projector. It is compatible with flat coefficient extension.

Saturation does not make $M$ a direct summand for the Hecke action. A rational projector with nonunit denominator can have a primitive image whose Hecke complement fails to split. This is why integral multiplicity extraction requires more data.

### 10.2 Integral multiplicity extraction

Assume the localized packet order $\mathcal A_{\Pi,\lambda}$ is a split finite-free order, $\mathcal P_{\Pi,\lambda}$ is a projective generator, and the integral evaluation map is an isomorphism. Define

$$
T_{\Pi,\lambda}
=\operatorname{Hom}_{\mathcal A_{\Pi,\lambda}}
(\mathcal P_{\Pi,\lambda},M_{\Pi,\lambda}). \tag{10.2}
$$

Then evaluation gives

$$
\mathcal P_{\Pi,\lambda}\otimes_{\mathcal O_\lambda}
T_{\Pi,\lambda}
\overset\sim\longrightarrow M_{\Pi,\lambda}. \tag{10.3}
$$

After inverting the uniformizer, this is the rational factorization (4.4), so $T_{\Pi,\lambda}$ is finite free of rank two. Galois stability follows from commutation with the order.

The hypotheses cannot be shortened to “the generic algebra is a matrix algebra.” A nonsplit order or a nonprojective generator can give an evaluation map with finite cokernel. That defect changes the integral multiplicity lattice even though the rational Hom space is correct.

### 10.3 Canonicity and its limits

The lattice $T_{\Pi,\lambda}$ is canonical relative to the integral curve realization datum. This means independence of projector formulas, bases, matrix coordinates, and integral presentations connected by the verified unit-degree comparisons. It does not mean that the rational representation has one intrinsically distinguished stable lattice.

At coarse level, canonicity passes from a fine cover only if averaging and stabilizer denominators are units, or if a direct integral comparison replaces averaging. Between isogenous abelian carriers it passes only when the isogeny and its normalized dual have coefficient-unit composites. Between two curve carriers it requires a unit-degree integral comparison, not merely equality of rational Frobenius polynomials.

The factored pairing on $T$ is perfect only when its duality index is a unit. Rational self-duality does not imply integral self-duality. When perfectness holds, the coefficient involution and Tate twist must be retained on the dual lattice.

**Proposition 10.1 (canonical integral extraction).** Under the split-order, projective-generator, and integral-evaluation hypotheses, (10.2) is a canonical finite-free rank-two Galois lattice relative to the named integral carrier, and its generic fiber is $W_{\Pi,\lambda}$.

**Proof.** The saturated lattice $M$ is finite free. Because $\mathcal P$ is finite projective, $\operatorname{Hom}_{\mathcal A}(\mathcal P,M)$ is finite and torsion free over the coefficient DVR, hence free. Integral evaluation is an isomorphism by hypothesis. After tensoring with $E_\lambda$, it becomes (4.4), and therefore the Hom lattice has generic rank two.

Galois acts by (4.2); the same computation as in Proposition 4.1 shows that it preserves integral $\mathcal A$-linearity. Projector independence follows because $M$ was defined as an intersection with the rational subspace, not as the image of a chosen integral projector. An isomorphism of projective generators induces inverse Hom equivalences, so bases and matrix coordinates disappear. These observations give precisely the stated relative canonicity. $\square$

### 10.4 Residual representations

Reduction gives

$$
\overline\rho_{T}:G_F\longrightarrow
\operatorname{GL}_2(k_\lambda).
$$

For an arbitrary stable lattice its isomorphism class can vary, but its semisimplification is independent of the lattice. Indeed, every stable lattice gives the same integral characteristic polynomial for each group element; reduction and the residual character criterion identify the semisimplifications.

Under the curve determinant datum, or whenever Frobenius is already known to be nonscalar in characteristic zero, at a good place,

$$
\det(X-\overline\rho^{\mathrm{ss}}_{\Pi,\lambda}(\Phi_v))
\equiv X^2-t_vX+q_vs_v\pmod\lambda. \tag{10.4}
$$

If the residual semisimplification is absolutely irreducible, every stable-lattice reduction is isomorphic. If it is reducible, different lattices can realize different extensions with the same diagonal characters. The canonical cohomological lattice selects one extension relative to the carrier; good Frobenius polynomials alone do not.

## 11. Finite-flat coefficient quotients

### 11.1 The coefficient-prime carriers

Fix $u\mid\ell$. A rational representation and even a canonical stable lattice do not by themselves produce a finite-flat model. The integral curve realization datum must supply one of two carriers.

The geometric route uses a good-reduction abelian scheme over $\mathcal O_{F_u}$ with integral $\mathcal O_\lambda$-action and a unit-degree identification of its marked Tate lattice with $T_{\Pi,\lambda}$ in the stated dual-and-twist convention. Its torsion is finite flat.

The filtered route applies when $\ell>2$, $F_u=W(k)[1/\ell]$ with $k$ perfect, and a finite-free strongly divisible lattice of weights $[0,1]$ with integral coefficient action realizes $T_{\Pi,\lambda}$. The absolutely unramified base and the short weight interval are essential. No extension to $\ell=2$ or to ramified $F_u$ is implicit.


### 11.2 All open ideals

Let $I\subset\mathcal O_\lambda$ be an open ideal. Starting with a principal-level finite-flat carrier, take in its generic fiber the coefficient relation submodule $IT$. Close that subgroup schematically inside the fixed finite-flat group, and take the represented faithfully flat quotient. The resulting marked finite-flat group, denoted $\mathcal T_{\Pi,I}$, has generic module

$$
T_{\Pi,\lambda}/IT_{\Pi,\lambda}. \tag{11.1}
$$

This construction is safer than taking the kernel of an arbitrary coefficient endomorphism. A kernel of a nonflat coefficient relation need not be flat. Closure inside a supplied finite-flat carrier and represented quotient preserve flatness and retain the generic marking.

The coefficient action descends because the closed relation subgroup is stable. It factors through $\mathcal O_\lambda/I$. Every ideal of the coefficient DVR $\mathcal O_\lambda$ is principal, but phrasing the construction in terms of $I$ rather than a generator makes it canonical. More general coefficient orders require the additional admissibility hypotheses of the integral theory.

### 11.3 Transition maps and ranks

If $J\subset I$, then $JT\subset IT$. Closure and successive quotient produce a canonical faithfully flat map

$$
\mathcal T_{\Pi,J}\longrightarrow\mathcal T_{\Pi,I}. \tag{11.2}
$$

For $K\subset J\subset I$, the maps compose transitively. Their generic kernel is $IT/JT$, and the schematic kernel is its finite-flat closure. Thus the finite quotients form one compatible system rather than unrelated models chosen level by level.

Since $T$ has rank two over $\mathcal O_\lambda$, the generic fiber of $T/IT$ has cardinality $|\mathcal O_\lambda/I|^2$. Finite flatness makes this the rank of $\mathcal T_{\Pi,I}$ over the local base.

The inverse limit of the principal transition system recovers the original lattice and its continuous Galois action. This statement uses the common marked construction; abstract existence of a finite-flat model at each level would not determine compatible transition maps.

**Theorem 11.1 (finite-flat quotient system).** Let $T$ be the canonical rank-two lattice and suppose one of the coefficient-prime carriers of Section 11.1 is supplied. Then the groups $\mathcal T_I$ of Section 11.2 exist for every open ideal, are unique inside the marked carrier construction, are finite flat of rank $|\mathcal O_\lambda/I|^2$, and carry the transitive maps (11.2).

**Proof strategy.** One first constructs principal levels in a single compatible carrier, then imposes arbitrary coefficient relations on generic fibers, and only afterward takes schematic quotients. This order retains flatness and markings.

**Proof.** Abelian torsion supplies the principal levels in the geometric route. In the filtered route, the strongly divisible lattice and the weight-$[0,1]$ equivalence supply them and identify their transition maps. Choose a principal level large enough that $I$ kills its generic module. Inside this finite-flat group, the generic relation submodule determined by $I$ has a unique schematic closure which is finite flat over the DVR. The faithfully flat quotient by that closure is represented and has generic fiber $T/IT$.

Increasing the chosen principal level gives the same marked quotient: both constructions are quotients by the closure of the same generic relations inside a common higher level, and uniqueness of closure plus successive quotient identifies them. This proves existence and independence from the auxiliary principal level.

If $J\subset I$, the closure of the $J$-relations lies inside the closure of the $I$-relations. Successive quotient gives (11.2), and applying the same fact to three nested ideals proves transitivity. Rank can be checked on the generic fiber because a finite-flat group has constant rank; since $T$ is free of rank two, that rank is $|\mathcal O_\lambda/I|^2$. Stability of the relation subgroup makes the coefficient action descend and factor through $\mathcal O_\lambda/I$. $\square$

### 11.4 Duality and base change

Cartier duality sends $\mathcal T_I$ to a model of

$$
(T/IT)^*(1)
$$

and reverses the transition exact sequences. If the integral packet pairing is perfect and $I$ is stable under the coefficient involution, it identifies the quotient with the appropriate twisted dual quotient.

Finite extension of the local ground field base-changes the quotient system. Unramified base change in the filtered route agrees with scalar extension of the strongly divisible lattice under the same absolutely unramified hypotheses. Descent in the opposite direction requires compatible integral descent data; rational descent of the generic representation is insufficient.

Finite flat coefficient extension is governed by the trace-dual coefficient module, while nonflat coefficient quotients are governed by admissible annihilators in the filtered category. Treating both operations as naive tensor products loses duality and flatness.

## 12. Examples and counterexamples

### 12.1 An elliptic curve packet

Let $A/\mathbf Q$ be an elliptic curve of conductor $N$, and let $\Pi$ be its weight-two modular packet. The modular parametrization realizes its covariant member on $T_\ell A$. In untwisted cohomology, the geometric-Frobenius polynomial at $p\nmid N\ell$ is

$$
X^2-a_pX+p,
\qquad
a_p=p+1-\#A(\mathbf F_p). \tag{12.1}
$$

Thus $E=\mathbf Q$, $s_p=1$, and $\det\rho=\chi_\ell^{-1}$ in the convention of this book. The roots have absolute value $p^{1/2}$.

At a multiplicative prime, the local parameter is special with rank-one monodromy. Its conductor is one. At a prime above $\ell$ where $A$ has good reduction, every $A[\ell^n]$ is finite flat, although the $\ell$-adic representation is generally ramified. Good reduction at the coefficient prime must never be paraphrased as unramifiedness.

### 12.2 An old packet

Suppose a new packet of conductor $\mathfrak n$ is viewed at level $\mathfrak n v$ with $v\nmid\mathfrak n$. Its fixed-vector module can have dimension two. The total cohomological block then has dimension four:

$$
E_\lambda^2\otimes W_{\Pi,\lambda}.
$$

The Galois factor remains $W_{\Pi,\lambda}$ of dimension two. An eigenspace for Hecke operators away from $v$ sees all four dimensions. The Morita Hom construction removes the oldvector factor without choosing one degeneracy vector.

Integrally, the two degeneracy lattices can meet with finite index. A rational old/new projector may have a $\lambda$-denominator, so rational decomposition does not imply a direct integral decomposition.

### 12.3 A scalar Frobenius

Let Frobenius act as $\alpha I$ on a two-dimensional space. It is annihilated by every quadratic

$$
(X-\alpha)(X-\beta)
$$

with $\beta=\alpha$ only if it is to be the characteristic polynomial, but many quadratics vanish at the single operator after coefficient adjustment. Thus the geometric annihilator alone does not determine trace. Knowing $\det(\alpha I)=\alpha^2$ and applying Lemma 6.1 forces the correct polynomial $(X-\alpha)^2$.

This is why determinant and good correspondence are proved independently. The repeated-root case is not negligible: congruences can make distinct good roots coincide modulo $\lambda$ even when they are distinct in characteristic zero.

### 12.4 A residual extension

Let $V$ be an extension of characters

$$
0\longrightarrow E_\lambda(\alpha)
\longrightarrow V
\longrightarrow E_\lambda(\beta)
\longrightarrow0.
$$

Every group element has characteristic polynomial $(X-\alpha(g))(X-\beta(g))$, independent of the extension class. Rescaling one basis vector can change a stable lattice so that reduction changes from nonsplit to split. The residual semisimplification is fixed; the extension is not. This is why compatible Frobenius polynomials determine the semisimple system but not a preferred residual extension.

## 13. The attachment theorem

### 13.1 Statement

**Theorem 13.1 (attachment in the curve-realizable parallel-weight-two range).** Let $F$ be totally real and let $\Pi$ be a noncharacter cuspidal parallel-weight-two automorphic packet. Assume that $\Pi$ has a curve realization datum of Section 3.3, either on a modular curve when $F=\mathbf Q$, directly on a compact quaternionic Shimura curve, or through the selected totally-definite transfer range of Section 1.2. Let $E$ be a finite extension of the packet field splitting the finite Hecke algebra. Then for every finite place $\lambda$ of $E$ there is a continuous semisimple representation

$$
\rho_{\Pi,\lambda}:G_F\longrightarrow
\operatorname{GL}_2(E_\lambda)
$$

with the following properties.

1. **Finite ramification and conditional weak compatibility.** There is a finite set $S$, independent of $\lambda$, such that for $v\notin S$ and $v\nmid\ell(\lambda)$, $\rho_{\Pi,\lambda}$ is unramified and, under the determinant datum,

   $$
   \det(X-\rho_{\Pi,\lambda}(\Phi_v))
   =X^2-t_vX+q_vs_v\in E[X].
   $$

2. **Determinant and duality.** Under the curve determinant datum, for every $\lambda$,

   $$
   \det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_{\Pi,\lambda},
   \qquad
   \rho_{\Pi,\lambda}^\vee
   \simeq\rho_{\Pi,\lambda}(1)\otimes\eta_{\Pi,\lambda}^{-1}.
   $$

3. **Oddness.** If every real descent action preserves the individual coefficient block, then at each real place $\tau$ of $F$,

   $$
   \operatorname{tr}\rho_{\Pi,\lambda}(c_\tau)=0,
   \qquad
   \det\rho_{\Pi,\lambda}(c_\tau)=-1.
   $$

4. **Purity.** The system is pure of weight one at every good place. It is pure at verified bad places under the local weight hypotheses of the nearby-cycle comparison.

5. **Strict local compatibility.** At every $v\nmid\ell(\lambda)$ carrying one of the uniform good, Steinberg, finite-descent, or tame-dihedral packages, including its raw-to-global-semisimplification verification, its Frobenius-semisimple Weil--Deligne representation equals the algebraic local parameter of $\Pi_v$. Consequently the Euler factor, Artin and Swan conductors, monodromy rank, and normalized epsilon factor agree.

6. **Choice independence.** The system commutes with coefficient conjugation and extension and is independent of bases, matrix splittings, multiplicity coordinates, and polarization scaling. It is independent of the chosen curve carrier when the stated descent and rational curve-comparison hypotheses hold.

If an integral curve realization datum is also given, there is a canonical, relative to that datum, finite-free rank-two Galois lattice $T_{\Pi,\lambda}$. At every required $u\mid\ell$ and for every open ideal $I\subset\mathcal O_\lambda$, there is a marked coefficient-linear finite-flat group $\mathcal T_{\Pi,I}$ with generic module $T_{\Pi,\lambda}/IT_{\Pi,\lambda}$, rank $|\mathcal O_\lambda/I|^2$, and canonical transitive transition maps for inclusions of ideals. Cartier duality, the permitted base changes, and coefficient actions are compatible with this system.

Without the integral datum, only existence of a stable lattice and lattice-independent residual semisimplification is asserted. Without the curve determinant datum, the rank-two extraction, continuity, semisimplification, oddness, purity, saturation, and residual semisimplification remain; the good quadratic is an annihilator and is the characteristic polynomial at nonscalar Frobenius, but no determinant identification or scalar-Frobenius upgrade is asserted.

### 13.2 Proof

The rational packet projector and a splitting field produce the simple finite Hecke module. The automorphic decomposition of curve $H^1$ gives the evaluation isomorphism (4.4) and the two-dimensionality (4.5). Commutation with Galois defines the continuous action, and canonical semisimplification yields $\rho_{\Pi,\lambda}$.

Choose $S$ to contain all exceptions in the good-place ledger. At $v\notin S$ away from $\ell(\lambda)$, smooth proper specialization kills inertia. The normalized special-fiber correspondence gives the quadratic annihilator (6.1). Under the curve determinant datum, factored duality gives the alternating pairing (7.1), hence the determinant (7.2); Lemma 6.1 then turns the annihilator into the asserted characteristic polynomial, including scalar Frobenius. Without that datum, the proof stops at the annihilator, except that nonscalar Frobenius already has the displayed characteristic polynomial. The two Hodge lines are exchanged by each real complex conjugation preserving the coefficient block, proving total oddness in the stated range.

Under the determinant datum, the good polynomials lie in $E[X]$ before completion, and every conjugate packet occurs in curve cohomology. Repeating the construction at all $\lambda$ then proves weak compatibility and coefficient compatibility. Weight-one purity of curve $H^1$ passes to the Hom factor independently of that datum.

At a verified bad place, the equivariant nearby-cycle complex carries Hecke, finite descent, Frobenius, and monodromy. The curve Hom construction commutes with these operations on the raw multiplicity space. The retained raw-to-global-semisimplification clause and the local recognition theorems identify the complete Weil--Deligne pair of $\rho_{\Pi,\lambda}$. The formulas of Chapter 8 give the local invariants and their coefficient independence.

For the integral statement, intersect the rational block with integral curve cohomology. Section 10.1 proves saturation, finite freeness, and stability. The split order, projective generator, and integral evaluation hypotheses give the rank-two Hom lattice by Section 10.2. At a coefficient prime, the geometric or filtered carrier supplies principal finite-flat levels. Schematic closure of coefficient relations and represented quotient give every open-ideal quotient. Successive quotient proves the transition maps, generic rank gives the stated rank, and Cartier duality and the permitted base-change theorems give the final compatibilities. $\square$

### 13.3 The range used in the Fermat argument

In the applications motivating this volume, every automorphic packet is parallel weight two and is realized on a modular or compact quaternionic Shimura curve, either directly or through the selected totally-definite transfer with all local-image hypotheses checked. Every finite place used in a local claim belongs to one of the verified good, Steinberg, finite-descent, or tame-dihedral alternatives. The integral applications use fine minimal level or retain explicit split-order and evaluation hypotheses, and the coefficient-prime lattice is supplied by good-reduction abelian geometry or the absolutely unramified weight-$[0,1]$ filtered route.

Under exactly those conditions, Theorem 13.1 supplies the continuous semisimple rank-two family, the determinant-enhanced compatible system when the curve determinant datum is present, the verified local parameters, and the required integral and finite-flat objects. If a transfer, local model, determinant datum, integral Morita datum, or coefficient-prime carrier is missing, the conclusion stops at the last established layer.


## 14. Hypothesis and dependency audit

### 14.1 Exact hypothesis ledger

| Conclusion | Required hypotheses | Failure without them |
|---|---|---|
| rank-two curve factor | cuspidal parallel weight two, full finite Hecke block, splitting field, exact automorphic multiplicity | characters, oldvectors, or a Schur algebra inflate or obstruct the factor |
| modular-curve factor | parabolic cohomology of the compactification | boundary classes can mimic reducible systems |
| totally-definite transfer | global transfer and every ramified local-image condition | almost-all good eigenvalues do not create a curve realization |
| Galois action on a packet | descended correspondences and Galois-stable component union | an eigensystem need not define a stable subspace |
| good unramifiedness | complete smooth projective integral-model ledger and $v\nmid\ell$ | inertia or nearby cycles may survive |
| good characteristic polynomial | normalized correspondence, rank two, and independent determinant datum in the scalar case | the quadratic may be only an annihilator |
| determinant | Book 134 curve determinant datum | adjoint duality alone does not give an alternating self-pairing |
| oddness | weight-two Hodge types and preservation of the coefficient block by real descent | parity is undefined or unsupported |
| strict local compatibility | full local nearby-cycle, type, monodromy, return-map, and raw-to-global-semisimplification package | conductor or inertia alone does not identify the parameter, and global semisimplification can erase extension monodromy |
| pure compatible system | coefficient conjugates, common algebraic polynomials, and local weight hypotheses | one realization does not control all completions or bad weights |
| canonical rank-two lattice | saturation, split order, projective generator, integral evaluation | rational projectors can have nonunit denominators |
| integral perfect duality | unit duality index and coefficient involution | rational self-duality need not be integral |
| finite-flat quotients | marked geometric carrier, or $\ell>2$ absolutely unramified weights $[0,1]$ carrier | a stable lattice or rational crystallinity is insufficient |
| every open ideal and transitions | closure inside one carrier and represented successive quotients | raw kernels can be nonflat and levelwise models incompatible |
| curve-carrier independence integrally | unit-degree integral comparison | isogenous carriers can define different lattices |

### 14.2 Use of the five direct prerequisites

The exact direct dependency row is

$$
\boxed{135\mid 132,\ 134,\ 136,\ 137,\ 138.}
$$

**Book 132, Automorphic decomposition of Shimura-curve $H^1$.** It supplies the noncharacter parallel-weight-two curve range, exact factorization into a finite Hecke module and a two-dimensional multiplicity space, rational Hecke fields, Hodge types, adjoint pairings, good correspondence relation, saturated ambient lattice, and the exact boundary on the selected totally-definite transfer.

**Book 134, Galois representations from weight-two Shimura-curve cohomology.** It supplies continuous rank-two Hom spaces, canonical semisimplification, the conditional determinant and scalar-Frobenius upgrade, oddness, good Frobenius polynomials, and the saturation boundary. This book retains its curve determinant datum verbatim and does not repair the old-level pairing gap by another geometric carrier.

**Book 136, Local--global compatibility for weight-two Galois representations.** It supplies the complete good, split semistable, Steinberg, finite-descent, and tame-dihedral comparisons in the curve range. We retain $v\nmid\ell$, the verified model, extending correspondences, type projectors, Frobenius return maps, finite descent, and the requirement that the computed raw cohomological parameter is the parameter of the stated global semisimplification.

**Book 137, Compatible coefficient systems and purity.** It supplies the common coefficient field, all coefficient conjugates, weak and strict compatibility, good and bad purity, conductor independence, and rational curve-comparison criteria. It supplies stable and saturated lattices, not canonical rank-two integral factors.

**Book 138, Canonical Galois lattices and finite-flat quotients.** It supplies saturation, integral Morita extraction, canonicity relative to a curve carrier, split-order and evaluation hypotheses, the geometric and absolutely unramified filtered coefficient-prime routes, closure-and-quotient construction for all open ideals, transition maps, Cartier duality, and base change. We retain its exclusions at $\ell=2$, ramified filtered bases, and denominator primes.

These inputs fit without circularity. Rational extraction precedes local comparison; local comparison precedes strict compatibility; the compatible system precedes the integral refinement; and the coefficient-prime carrier is independent of prime-to-$\ell$ local compatibility.

### 14.3 What the theorem does not say

The theorem does not attach a rank-two representation to an arbitrary nonalgebraic or noncuspidal eigensystem. It does not treat higher weights. It does not remove a failure of global transfer by matching almost all Hecke values.

It does not identify nonsplit global or residual extensions from Frobenius polynomials. It does not assert absolute irreducibility. It does not claim that local inertia is determined by the automorphic conductor in places lacking the verified geometric comparison.

It does not assert a Weil--Deligne comparison at the coefficient residue characteristic. Good reduction there does not imply unramifiedness. Finite-flatness is asserted only for the named integral lattice and only through a supplied geometric or filtered carrier.

It does not make a rational projector integral, a saturated block a direct Hecke summand, or rational self-duality a perfect integral pairing. It does not identify canonical lattices across curve carriers without unit-degree integral comparison.


## 15. Conclusion

### 15.1 The completed arithmetic package

A parallel-weight-two automorphic packet in the curve-realizable range determines a rank-two multiplicity space in modular or quaternionic curve $H^1$. The same applies to a selected totally-definite packet only after the exact global transfer and local-image conditions place its split packet in that curve range. Hecke and Galois then act on the same cohomology, and the full finite Hecke module removes oldvectors without choosing an eigenline.

The good-place correspondence gives a quadratic relation. When the curve determinant datum is supplied, the factored pairing gives the independent determinant

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_{\Pi,\lambda},
$$

and the two inputs give the geometric-Frobenius polynomial $X^2-t_vX+q_vs_v$, even when Frobenius is scalar. Without that datum the determinant and scalar upgrade remain open. The Hodge lines give total oddness in the stated descent range, and every curve realization is pure of weight one. Under the determinant datum, repetition at every coefficient place produces the compatible system. At every verified bad place, the retained local package identifies the complete Weil--Deligne pair and hence the local factor, conductor, Swan term, monodromy, and epsilon factor.

The integral refinement begins with saturation, not a rational projector. A split Hecke order, projective generator, and exact integral evaluation remove automorphic multiplicity and produce the canonical rank-two lattice relative to the chosen curve carrier. A good-reduction abelian scheme or an absolutely unramified weight-$[0,1]$ filtered carrier then supplies finite-flat principal levels. Schematic closure and represented quotient extend them to every open coefficient ideal, with compatible transitions, duality, coefficient action, and allowed base change.

The boundaries are part of the result: semisimplification does not remember extensions, local types do not replace Frobenius return maps, rational compatibility does not synchronize lattices, and almost-all Hecke agreement does not replace a global transfer. With those distinctions preserved, the attachment theorem supplies precisely the parallel-weight-two arithmetic package used in the FLT route.
