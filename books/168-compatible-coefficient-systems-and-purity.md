# Compatible Coefficient Systems and Purity

## Contents

1. [One arithmetic object seen at many coefficient places](#1-one-arithmetic-object-seen-at-many-coefficient-places)
   - [The changing-prime problem](#11-the-changing-prime-problem)
   - [Standing fields and conventions](#12-standing-fields-and-conventions)
   - [What the preceding constructions provide](#13-what-the-preceding-constructions-provide)
   - [The logical route](#14-the-logical-route)
2. [Coefficient fields, embeddings, and places](#2-coefficient-fields-embeddings-and-places)
   - [The good-polynomial field, packet center, and realization field](#21-the-good-polynomial-field-packet-center-and-realization-field)
   - [Embeddings into local fields](#22-embeddings-into-local-fields)
   - [Conjugate packets](#23-conjugate-packets)
   - [Changing or enlarging the coefficient field](#24-changing-or-enlarging-the-coefficient-field)
3. [Weak and strict compatibility](#3-weak-and-strict-compatibility)
   - [Common Frobenius polynomials](#31-common-frobenius-polynomials)
   - [Weakly compatible systems](#32-weakly-compatible-systems)
   - [Strictly compatible systems](#33-strictly-compatible-systems)
   - [Why the distinction matters](#34-why-the-distinction-matters)
4. [Constructing the family from a weight-two packet](#4-constructing-the-family-from-a-weight-two-packet)
   - [The eligible curve carrier and family at coefficient places](#41-the-eligible-curve-carrier-and-family-at-coefficient-places)
   - [Continuity and semisimplicity](#42-continuity-and-semisimplicity)
   - [The good-place polynomial](#43-the-good-place-polynomial)
   - [Weak compatibility theorem](#44-weak-compatibility-theorem)
5. [Determinants, pairings, and polarizations](#5-determinants-pairings-and-polarizations)
   - [The common determinant character](#51-the-common-determinant-character)
   - [Alternating pairings in rank two](#52-alternating-pairings-in-rank-two)
   - [Independence of the polarization](#53-independence-of-the-polarization)
   - [Duality and reciprocal roots](#54-duality-and-reciprocal-roots)
6. [Purity at the good places](#6-purity-at-the-good-places)
   - [Weil numbers and system weight](#61-weil-numbers-and-system-weight)
   - [Purity inherited from curves](#62-purity-inherited-from-curves)
   - [Consequences for Hecke eigenvalues](#63-consequences-for-hecke-eigenvalues)
7. [Local Weil--Deligne compatibility](#7-local-weil--deligne-compatibility)
   - [The common local datum](#71-the-common-local-datum)
   - [Good and special places](#72-good-and-special-places)
   - [Finite and tame dihedral types](#73-finite-and-tame-dihedral-types)
   - [Strict compatibility theorem](#74-strict-compatibility-theorem)
   - [Ambient semisimplicity and uniform passage](#75-ambient-semisimplicity-and-uniform-passage)
8. [Purity at bad places](#8-purity-at-bad-places)
   - [The monodromy filtration](#81-the-monodromy-filtration)
   - [Special parameters](#82-special-parameters)
   - [Finite-monodromy parameters](#83-finite-monodromy-parameters)
   - [Local purity of the system](#84-local-purity-of-the-system)
9. [Conductors and local factors](#9-conductors-and-local-factors)
   - [Artin and Swan conductors](#91-artin-and-swan-conductors)
   - [Independence of the coefficient place](#92-independence-of-the-coefficient-place)
   - [Euler and epsilon factors](#93-euler-and-epsilon-factors)
   - [Diagnostic calculations](#94-diagnostic-calculations)
10. [Independence from embeddings and auxiliary choices](#10-independence-from-embeddings-and-auxiliary-choices)
    - [Changing an algebraic embedding](#101-changing-an-algebraic-embedding)
    - [Changing splittings and multiplicity modules](#102-changing-splittings-and-multiplicity-modules)
    - [Changing the geometric carrier](#103-changing-the-geometric-carrier)
    - [The exact meaning of independence](#104-the-exact-meaning-of-independence)
11. [Integral lattices and their limits](#11-integral-lattices-and-their-limits)
    - [Existence of stable lattices](#111-existence-of-stable-lattices)
    - [Saturated cohomological lattices](#112-saturated-cohomological-lattices)
    - [Congruence and projector denominators](#113-congruence-and-projector-denominators)
    - [What rational compatibility does not provide](#114-what-rational-compatibility-does-not-provide)
12. [The complete compatible-system theorem](#12-the-complete-compatible-system-theorem)
    - [Statement](#121-statement)
    - [Proof](#122-proof)
    - [Variants and edge cases](#123-variants-and-edge-cases)
    - [Dependency and hypothesis ledger](#124-dependency-and-hypothesis-ledger)
13. [The arithmetic package](#13-the-arithmetic-package)
    - [A worked synthesis](#131-a-worked-synthesis)
    - [A normalization audit](#132-a-normalization-audit)
    - [What has and has not been proved](#133-what-has-and-has-not-been-proved)
    - [Conclusion](#134-conclusion)

## 1. One arithmetic object seen at many coefficient places

### 1.1 The changing-prime problem

A single weight-two automorphic packet gives algebraic Hecke numbers. Choosing a finite place of their field turns those numbers into elements of a nonarchimedean field and permits a Galois representation to be extracted from cohomology. Repeating this construction at another coefficient place produces a representation on another topological vector space. There is no sensible linear isomorphism between those two spaces: their scalar fields may have different residue characteristics. The arithmetic assertion must therefore be phrased through data which exist before either completion is chosen.

At a good finite place $v$ of the base field, that common datum is the polynomial

$$
P_v(X)=X^2-t_vX+q_vs_v. \tag{1.1}
$$

Here $q_v$ is the residue cardinality, while $t_v$ and $s_v$ lie in one number field. After embedding that field into any allowed coefficient completion, $P_v$ becomes the characteristic polynomial of geometric Frobenius. This is **weak compatibility**.

At a bad place, a characteristic polynomial is not enough. Inertia can be finite, monodromy can be nonzero, and Frobenius acts on inertia-isotypic pieces. The common datum must be a Weil--Deligne representation defined over a number field. Requiring every allowed coefficient realization to be obtained from this one local datum is **strict compatibility**. It remembers exactly what weak compatibility forgets.

The purpose of this book is to assemble the representations attached to all coefficient conjugates of a weight-two packet into one weakly compatible system. We prove independence from the chosen algebraic embedding, from harmless enlargements of the coefficient field, from the scalar used to normalize a polarization, and, for semisimple members, from the eligible curve carrier. We prove good-place purity of weight one.

At bad places there are two different outputs. In the split one-step Iwahori special range, the preceding semistable-curve theorem actually constructs the graph line, nonzero monodromy, and raw unnormalized $U_v$ return scalar. By contrast, the tame principal, scalar-special after descent, and tame dihedral statements are recognition criteria: they identify a parameter only after the type lines, monodromy branch, and every Frobenius return map have been supplied. For a nonzero-monodromy raw parameter, passage to the globally semisimplified family requires the local-preservation identity below. Book 128 proves it automatically in every zero-monodromy row, since finite inertia and all local traces survive global semisimplification. At nonzero monodromy it follows at a coefficient place whose stable lattice has absolutely irreducible residual reduction, while its uniform version reduces to semisimplicity of the ambient curve cohomology. Book 41 proves the complete Tate stable-lattice reduction of that ambient statement to finite carrier-isogeny classes. Those classes are the exact arithmetic input; its displayed uniform source is the still-unproved Faltings--Shafarevich moduli-height package.

### 1.2 Standing fields and conventions

Let $F$ be the number field over which the global Galois representations are defined. In the curve applications $F$ is totally real. Let $\Pi$ be a noncharacter parallel-weight-two packet in the geometric range under consideration. Its raw good Hecke polynomial at a finite place $v$ is (1.1), with

$$
t_v=t_v(\Pi),\qquad s_v=s_v(\Pi).
$$

Let $E_0$ be the number field generated by the $t_v$, the $s_v$, and the finite central and component values. It is the **good-polynomial field**. Let $Z_\Pi$ be the center of the selected simple factor of the full finite Hecke image. One can have $E_0\subsetneq Z_\Pi$ when the good operators determine only a near-equivalence block. Choose once and for all a finite extension $E/E_0$ which contains every selected embedding of $Z_\Pi$, splits the resulting central simple factors, and contains all tame type data used below. The system is realized over $E$; its good polynomials and determinant descend to $E_0$. Enlarging $E$ later changes only scalars.

For a finite place $\lambda$ of $E$, write $E_\lambda$ for the completion, $\mathcal O_\lambda$ for its valuation ring, $k_\lambda$ for its residue field, and $\ell(\lambda)$ for its residue characteristic. A finite place $v$ of $F$ has residue characteristic $p(v)$ and residue cardinality $q_v$.

Galois acts arithmetically, but every displayed local polynomial uses **geometric Frobenius** $\Phi_v$. Thus

$$
\Phi_v\mid E_\lambda(1)=q_v^{-1}. \tag{1.2}
$$

The cyclotomic character satisfies

$$
\chi_\lambda(\Phi_v)=q_v^{-1}. \tag{1.3}
$$

If arithmetic Frobenius is used, its eigenvalues are the inverses of those occurring here. A Tate twist by $(n)$ multiplies geometric Frobenius eigenvalues by $q_v^{-n}$ and lowers weight by $2n$.

All representations are finite dimensional and continuous. The global family will be semisimple. At a local place $v\nmid\ell(\lambda)$, $\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\!-\!ss}}$ means Frobenius semisimplification of the associated Weil--Deligne pair; finite inertia and the nilpotent operator are retained.

### 1.3 What the preceding constructions provide

Four established inputs meet here.

First, the algebraic packet theory gives the number field $E_0$, algebraic-integral good Hecke values, all coefficient conjugates, and saturated eigenlattices. It also distinguishes the field of rationality from a field which splits the full simple Hecke algebra.

Second, cohomological extraction from a compact Shimura curve gives, for every $\lambda$, a continuous raw rank-two representation $\widetilde\rho_\lambda$ on the multiplicity space and its canonical global semisimplification

$$
\rho_\lambda=\widetilde\rho_\lambda^{\mathrm{ss}}:
G_F\longrightarrow\operatorname{GL}_2(E_\lambda). \tag{1.4}
$$

Their common determinant is

$$
\det\rho_\lambda=\chi_\lambda^{-1}\eta_\lambda, \tag{1.5}
$$

where $\eta$ is a finite central-component character with values in $E_0^\times$. At every place satisfying the full good-model hypotheses and with $v\nmid\ell(\lambda)$, the representation is unramified and has polynomial (1.1).

Third, the low-dimensional weight theorem proves that smooth proper curve $H^1$ is pure of weight one. Purity passes to correspondence summands and hence to the rank-two multiplicity space.

Fourth, the local comparison argument identifies the full Frobenius-semisimple Weil--Deligne parameter of the raw multiplicity representation at good places and at the verified split one-step Iwahori special places. It also gives recognition theorems for tame principal, scalar-special, and tame dihedral parameters when the complete descent and return-map data are separately present. Global Galois semisimplification need not preserve nonzero local monodromy or its conductor. Thus strict compatibility of $\rho_\lambda$ in a nonzero-monodromy row requires the identity

$$
\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\!-\!ss}}
\simeq
\operatorname{WD}_v(\widetilde\rho_\lambda)^{\mathrm{F\!-\!ss}}. \tag{1.6}
$$

We call (1.6) the **local-preservation condition** at $(v,\lambda)$; it is exactly $(\mathrm R_u)$ in the preceding local-comparison book, after matching the local place. Book 128, Lemma 3.2 proves (1.6) whenever the raw monodromy at $v$ is zero. For nonzero monodromy it follows if the raw global representation is already semisimple. More concretely, if a stable lattice in the two-dimensional member has absolutely irreducible residual reduction, then the characteristic-zero member is absolutely irreducible, the raw representation is already irreducible, and (1.6) holds at every $v\nmid\ell(\lambda)$. This closes the passage for the distinguished residual-irreducible FLT member. It is a place-by-place argument and supplies no uniform assertion for all $\lambda$. Book 128, Proposition 9.4 gives the coefficient-uniform alternative needed in the remaining nonzero-monodromy rows: semisimplicity of the ambient $H^1$ of each actual curve carrier makes every extracted raw multiplicity representation semisimple after every finite coefficient extension.

These inputs do not yet constitute a compatible-system theorem. We must organize coefficient embeddings, show that all local data have a common algebraic model, and separate rational compatibility from integral choices.

### 1.4 The logical route

The construction follows a strict order.

1. Fix the good-polynomial field, the full packet centers, and a common field of realization.
2. Index representations by finite places of that field, not by unnamed embeddings into algebraic closures.
3. Prove weak compatibility from the common good Hecke polynomial.
4. Identify the determinant and show that changing a polarization does not change it.
5. Deduce good-place purity from the geometric carrier.
6. Construct the split-Iwahori special raw parameter in the proved geometric range, and keep the other tame rows explicitly at the level of recognition criteria.
7. Deduce strict compatibility, conductors, and local factors for the semisimple family only where (1.6) is known; retain the separate weight normalization needed for bad-place purity.
8. Treat stable lattices only after the rational family is complete.

The order prevents three circular arguments. Purity is not inferred from reciprocal roots alone. A quadratic annihilator is not called a characteristic polynomial before the determinant is known. Equality of conductor is not used as a substitute for equality of Weil--Deligne parameters.

## 2. Coefficient fields, embeddings, and places

### 2.1 The good-polynomial field, packet center, and realization field

There are three coefficient layers. The coefficients of (1.1) naturally belong to $E_0$. The full separating Hecke block has center $Z_\Pi$, which can be larger. Finally, the rank-two multiplicity space can require $E$ because the simple factor over $Z_\Pi$ may be a nonsplit central simple algebra. Thus good-polynomial rationality, selection of a center embedding, and splitting of a Schur obstruction are distinct operations.

**Proposition 2.1 (finite common field).** There is a finite extension $E/E_0$ containing the relevant conjugates of every packet center, splitting every selected simple packet factor, and realizing every tame inertial type in the stated local range. The field $E$ may be chosen normal over $\mathbf Q$, so every embedding of $E_0$ extends to an automorphism of $E$ and all coefficient conjugates occur inside it.

**Proof strategy.** Each obstruction is finite-dimensional algebraic data, so each is killed by a finite extension; a compositum handles all of them simultaneously.

**Proof.** Each packet center is finite over $E_0$, and each central simple factor over that center has a finite splitting field. A finite inertial group has finitely many matrix entries in algebraic closures, and adjoining them gives a finite field. A tame inducing character used at one of the finitely many ramified places has finite-degree algebraic values. There are only finitely many bad places, so the compositum of these fields is finite over $E_0$. Taking its normal closure over $\mathbf Q$ gives the last assertion, and the extension theorem for embeddings extends every embedding of $E_0$ to an automorphism of that normal closure. $\square$

The word “common” does not mean minimal. A larger field may be convenient, and the system will be unchanged up to scalar extension. The genuinely intrinsic coefficient field for the displayed good polynomials remains $E_0$; this does not assert that the full packet block has center $E_0$.

### 2.2 Embeddings into local fields

An embedding

$$
\iota:E\hookrightarrow\overline{\mathbf Q}_\ell
$$

determines a place $\lambda$ of $E$ above $\ell$: pull back the valuation ring of $\overline{\mathbf Q}_\ell$. The embedding extends continuously to

$$
E_\lambda\hookrightarrow\overline{\mathbf Q}_\ell. \tag{2.1}
$$

Conversely, a place $\lambda\mid\ell$ together with an embedding of $E_\lambda$ into $\overline{\mathbf Q}_\ell$ gives such an $\iota$. Thus the invariant index is $\lambda$; the embedding into an algebraic closure is a way to display the completion.

If $\iota_1$ and $\iota_2$ induce the same place, the two scalar realizations become conjugate by an $E_\lambda$-embedding after passing to a common algebraically closed coefficient field. Every polynomial with coefficients in $E$ is transported coefficientwise. Consequently “independence of embedding” can never mean that $\iota_1(a)=\iota_2(a)$ as displayed algebraic numbers. It means that the construction commutes with the field isomorphism carrying one embedded copy of $E$ to the other.

**Lemma 2.2 (placewise scalar transport).** Let $V_\lambda$ be an $E_\lambda$-representation and let $j:E_\lambda\hookrightarrow\Omega$ be an embedding into an algebraically closed field of characteristic zero. Then

$$
\det(X-g\mid V_\lambda\otimes_{E_\lambda,j}\Omega)
=j\bigl(\det(X-g\mid V_\lambda)\bigr). \tag{2.2}
$$

Kernels, images, and ranks commute with this scalar extension. For semisimplification, the precise assertion is

$$
\bigl(V_\lambda^{\mathrm{ss}}\otimes_{E_\lambda,j}\Omega\bigr)^{\mathrm{ss}}
\simeq
\bigl(V_\lambda\otimes_{E_\lambda,j}\Omega\bigr)^{\mathrm{ss}}. \tag{2.2a}
$$

**Proof.** Choose a basis. The matrix after scalar extension is obtained by applying $j$ to every entry, so its determinant polynomial is obtained by applying $j$ to every coefficient. Flatness of field extension preserves exact sequences, hence kernels, images, and ranks. After passing to a finite splitting extension, scalar-extended Jordan--Holder factors may split further, but both sides of (2.2a) have the same resulting simple factors with the same multiplicities. $\square$

### 2.3 Conjugate packets

For an embedding $\sigma:E_0\hookrightarrow\mathbf C$, the conjugate packet $\Pi^\sigma$ has good polynomial

$$
P_v^\sigma(X)
=X^2-\sigma(t_v)X+q_v\sigma(s_v). \tag{2.3}
$$

The existence of $\Pi^\sigma$ is an algebraic statement about the finite Hecke module. For cuspidal $\mathrm{GL}_2$, the good polynomials determine a unique global conjugate representation; for a quaternionic module they first determine a near-equivalence block unless the prescribed isolating data distinguish one constituent.

The compatible family must include conjugation of the central-component character as well:

$$
\eta^\sigma(g)=\sigma(\eta(g)). \tag{2.4}
$$

Ignoring $s_v$ or $\eta$ would allow equal traces with different determinants. Raw algebraic normalization is therefore essential.

**Proposition 2.3 (conjugation of extracted data).** Suppose one rational conjugation-orbit packet block and its multiplicity construction are defined over $\mathbf Q$, and suppose $E$ is normal over $\mathbf Q$, contains the conjugate packet centers, and splits their selected factors. For every $\sigma\in\operatorname{Aut}(E/\mathbf Q)$ and every finite place $\lambda$ of $E$, scalar conjugation carries both the raw representation and its semisimplification attached to the $\sigma$-conjugate factor at $\lambda$ to the corresponding objects for the original factor at $\sigma^{-1}\lambda$. Their determinant and every verified raw local parameter are obtained by applying $\sigma$ to their algebraic coefficients. The same assertion for a semisimple local parameter requires (1.6).

**Proof.** The packet idempotents, simple modules, evaluation maps, pairings, and local type projectors are all defined by algebraic correspondences and finite-dimensional algebra. Applying $\sigma$ to their coefficients carries each defining identity to the corresponding identity for the conjugate block. The Hom multiplicity construction commutes with field automorphisms. The determinant target becomes $E_\lambda(-1)\otimes\eta^\sigma$, and the local Weil--Deligne matrices are conjugated coefficientwise. $\square$

### 2.4 Changing or enlarging the coefficient field

Let $E'/E$ be finite and let $\lambda'$ lie above $\lambda$. The natural notion of base change is

$$
\rho_{\lambda'}\simeq
\rho_\lambda\otimes_{E_\lambda}E'_{\lambda'}. \tag{2.5}
$$

At $v\nmid\ell(\lambda)$, formation of the Weil--Deligne pair, Frobenius semisimplification, inertia invariants, and the monodromy filtration all commute with this extension. The good polynomial becomes the image of $P_v$ in $E'_{\lambda'}[X]$.

**Proposition 2.4 (field-enlargement invariance).** Scalar extension of a weakly or strictly compatible $E$-system is a weakly or strictly compatible $E'$-system with the same exceptional places, weights, monodromy ranks, and conductor exponents. Conversely, if an $E'$-system is obtained placewise from representations over $E_\lambda$, its compatibility data descend to $E$ whenever all common local polynomials and Weil--Deligne pairs do.

**Proof.** Scalar extension preserves characteristic polynomials, finite inertia representations, nilpotent ranks, and dimensions of invariant spaces. The Artin conductor formula depends only on the latter data and on the Swan breaks, which are unchanged. For descent, choose $E$-models of the local pairs and use the stated placewise representations; extension recovers the $E'$-system. $\square$

This proposition lets us enlarge coefficients to split a type without pretending that the larger field is intrinsic.

## 3. Weak and strict compatibility

### 3.1 Common Frobenius polynomials

Let $S$ be a finite set of finite places of $F$. An $E$-rational collection of Frobenius polynomials of rank $n$ is a family

$$
P_v(X)\in E[X],\qquad v\notin S, \tag{3.1}
$$

of monic degree-$n$ polynomials with nonzero constant term. We use characteristic-polynomial normalization:

$$
P_v(X)=\det(X-\Phi_v). \tag{3.2}
$$

For Euler factors one instead writes

$$
L_v(T)=\det(1-T\Phi_v\mid V^{I_v})^{-1}. \tag{3.3}
$$

The two variables must not be confused. In rank two, if $P_v(X)=X^2-a_vX+b_v$, then the unramified Euler denominator is $1-a_vT+b_vT^2$.

For the weight-two packet, $S$ contains every place where the packet, level, central character, coefficient construction, or geometric carrier is outside the good ledger. It is independent of $\lambda$. At a place $v\notin S$ with $v\nmid\ell(\lambda)$, the polynomial is

$$
P_v(X)=X^2-t_vX+q_vs_v. \tag{3.4}
$$

### 3.2 Weakly compatible systems

**Definition 3.1 (weak compatibility).** An $E$-rational weakly compatible system of rank $n$ over $F$ consists of continuous semisimple representations

$$
\rho_\lambda:G_F\to\operatorname{GL}_n(E_\lambda)
$$

for finite places $\lambda$ of $E$, together with a finite set $S$ and polynomials (3.1), such that whenever $v\notin S$ and $v\nmid\ell(\lambda)$:

1. $\rho_\lambda$ is unramified at $v$;
2. $\det(X-\rho_\lambda(\Phi_v))$ is the image of $P_v(X)$ in $E_\lambda[X]$.

Semisimplicity is included because compatible good polynomials do not determine extension classes. One could define a weaker family of nonsemisimple representations, but then the common data would see only their semisimplifications. The present arithmetic applications use the canonical semisimplifications extracted from cohomology.

The exception $v\mid\ell(\lambda)$ is structural. The Weil--Deligne construction used here applies when the coefficient and residue characteristics differ. A family can have excellent properties at $v\mid\ell$, but those are additional $p$-adic Hodge-theoretic conditions, not consequences of weak compatibility.

### 3.3 Strictly compatible systems

Weak compatibility discards the places in $S$. To retain them, fix for every finite place $v$ of $F$ a Frobenius-semisimple Weil--Deligne representation

$$
D_v=(r_v,N_v) \tag{3.5}
$$

over $E$, or over a finite extension equipped with descent to $E$. The pair is understood up to $E$-linear isomorphism. At almost every $v$, it is unramified with $N_v=0$.

**Definition 3.2 (strict compatibility).** A weakly compatible system is **strictly compatible with local data $D_v$** if for every finite place $v$ and every $\lambda$ with $v\nmid\ell(\lambda)$,

$$
\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\!-\!ss}}
\simeq D_v\otimes_EE_\lambda. \tag{3.6}
$$

If $D_v$ is initially written over a finite extension $E_v/E$, (3.6) means that after passing to a common completion the two pairs are isomorphic and that the isomorphism class is invariant under descent. In the applications below, we enlarged $E$ at the outset so that every needed $D_v$ is already split.

At $v\notin S$, (3.6) recovers weak compatibility by taking $D_v$ to be unramified with Frobenius polynomial $P_v$. Strict compatibility is therefore a strengthening, not a competing convention.

Some authors reserve “strict” for the assertion that conductor and inertia are independent of $\lambda$. Definition 3.2 is stronger: it fixes the full Frobenius-semisimple Weil--Deligne pair. The weaker consequences will follow formally.

### 3.4 Why the distinction matters

Three pairs of local representations expose the gap.

First, $\operatorname{St}(1)$ and $\operatorname{St}(-1)$ both have conductor one and nonzero monodromy, but geometric Frobenius acts on their invariant lines by different signs. Second, a special parameter and the direct sum of a tamely ramified character with an unramified character can both have conductor one, but only the special parameter has $N\ne0$. Third, two tame dihedral representations can have the same inertial characters and conductor while differing by an unramified twist, hence by the Frobenius return scalar.

Weak compatibility says nothing at these bad places. Even the pair “inertial type plus conductor” does not distinguish them. The datum (3.5) does.

There is also an integral distinction. Two rationally isomorphic local representations can preserve nonisomorphic lattices. Strict compatibility as defined here is rational. It neither selects a lattice nor compares reductions modulo different coefficient primes.

## 4. Constructing the family from a weight-two packet

This chapter is an import boundary. Book 127, Theorem 8.1 owns the construction of the
curve-carried rank-two family, its common good polynomial, determinant, duality, total oddness,
good-place purity, existence of placewise stable lattices, and the exact integral and bad-place
limitations. Book 168 begins with that family and adds coefficient and local comparison results.

### 4.1 The eligible curve carrier and family at coefficient places

Assume exactly the one-split compact-curve packet datum of Book 127, Theorem 8.1. For a split
packet over a field of degree $d\ge2$, an eligible carrier is constructed from a selected finite
ramification set $W$ with $(d-1)+|W|$ even. Thus an odd nonempty eligible set is required in even
degree, whereas in odd degree one may take $W=\varnothing$.

### 4.2 Continuity and semisimplicity

Book 127 constructs, for every finite place $\lambda$ of one splitting field $E$, a continuous
semisimple representation

$$
\rho_{\Pi,\lambda}:G_F\longrightarrow\operatorname{GL}_2(E_\lambda).
\tag{4.1}
$$

Its raw multiplicity representation $\widetilde\rho_{\Pi,\lambda}$ and canonical
semisimplification are retained because the strictness problem at bad places depends on the map
from the raw object to (4.1).

**Lemma 4.1 (semisimplification and scalar extension).** Jordan--Holder makes the
semisimplification independent of a composition series and compatible with finite scalar
extension. This formal locator is retained from the earlier presentation.

### 4.3 The good-place polynomial

Outside one finite set independent of $\lambda$, and away from the coefficient residue
characteristic, Book 127 gives

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_v))
=X^2-t_vX+q_vs_v.
\tag{4.2}
$$

This is an actual base-field polynomial. Under a residue extension of degree $f$, its roots are
raised to the $f$th power; the middle coefficient is not left unchanged.

### 4.4 Weak compatibility theorem

**Theorem 4.2 (packet family at good places; compatibility alias).** This is the weak-family
portion of Book 127, Theorem 8.1. It supplies (4.1)--(4.2), total oddness, the determinant and
good-place purity recorded below, and no strict bad-place assertion.

**Corollary 4.3 (eligible split packet; compatibility alias).** This is the “moreover” clause of
Book 127, Theorem 8.1: in its selected local range a parity-compatible eligible set constructs the
one-split compact curve carrier and hence the weak family. In even degree this means an odd
nonempty set; in odd degree the empty set is allowed.

## 5. Determinants, pairings, and polarizations

### 5.1 The common determinant character

Book 127 proves, with geometric Frobenius and the untwisted cohomological normalization,

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_{\Pi,\lambda},
\qquad
\rho_{\Pi,\lambda}^{\vee}
\simeq\rho_{\Pi,\lambda}(1)\otimes\eta_{\Pi,\lambda}^{-1}.
\tag{5.1}
$$

The finite component character and its coefficient conjugates are part of the common algebraic
datum.

### 5.2 Alternating pairings in rank two

The perfect rational alternating similitude pairing that yields (5.1) is imported with Book
127's component-twist covariance and symmetric finite-module pairing hypotheses. It does not
select a perfect integral rank-two lattice.

**Proposition 5.1 (determinant compatibility; compatibility alias).** The characters in (5.1)
are coefficient realizations of the single algebraic character $\chi^{-1}\eta$; away from the
coefficient residue characteristic their inertia, conductor, and Frobenius values are independent
of $\lambda$.

**Corollary 5.2 (duality; compatibility alias).** The second identity in (5.1) is the imported
Book 127 duality statement.

### 5.3 Independence of the polarization

**Theorem 5.3 (polarization independence).** Rescaling the imported rational alternating pairing
does not change its multiplier in rank two. Hence it leaves (5.1), the good polynomials, and the
rational family unchanged. This is a formal consequence of Book 127's determinant package; it
does not identify integral lattices whose pairing indices differ.

### 5.4 Duality and reciprocal roots

At a good place the product of the two roots is $q_vs_v$, consistently with (5.1). The covariant
Tate normalization $\rho^{\rm cov}_\lambda=\rho_\lambda(1)$ has determinant
$\chi_\lambda\eta_\Pi$ and uses arithmetic Frobenius, exactly as in Book 127.

## 6. Purity at the good places

### 6.1 Weil numbers and system weight

A root of the common good polynomial has weight one when every complex embedding has absolute
value $q_v^{1/2}$.

### 6.2 Purity inherited from curves

**Theorem 6.2 (good-place purity; compatibility alias).** This is Book 127, Theorem 8.1(5).
The compact smooth curve carrier and Book 37's curve Weil theorem prove that the system of
Theorem 4.2 is pure of weight one at every good place.

### 6.3 Consequences for Hecke eigenvalues

Thus every conjugate of $t_v$ satisfies the usual weight-one bound and the roots of (4.2) have
the common absolute value. These good-place consequences will later be distinguished from
purity of a bad-place monodromy filtration, which is new work in Chapter 8.

**Corollary 6.3 (good Weil bounds; compatibility alias).** At every good place, the roots are
algebraic integers of weight one, $t_v$ satisfies the corresponding Weil bound, and $s_v$ has
finite order.

## 7. Local Weil--Deligne compatibility

### 7.1 The common local datum

Fix a finite place $v$ of $F$. For every $\lambda$ with $v\nmid\ell(\lambda)$, the raw local representation determines

$$
\operatorname{WD}_v(\widetilde\rho_\lambda)^{\mathrm{F\!-\!ss}}
=(r_{v,\lambda},N_{v,\lambda}). \tag{7.1}
$$

The local comparison argument supplies one algebraic pair $D_v=(r_v,N_v)$ whose scalar extensions are all the raw pairs (7.1) when its geometric hypotheses are uniform in $\lambda$. The strata, their incidence maps, finite descent group, Hecke and type projectors, and normalized Frobenius correspondences are geometric and algebraic; changing $\lambda$ changes only the coefficient realization. Strict compatibility of the semisimple family asks in addition that (1.6) hold.

The nilpotent operator has the typed form

$$
N_v:V_v\longrightarrow V_v(-1), \tag{7.2}
$$

and obeys

$$
r_v(\Phi_v)N_vr_v(\Phi_v)^{-1}=q_v^{-1}N_v. \tag{7.3}
$$

The pair is Frobenius semisimple: finite inertia and $N_v$ are not semisimplified away.

### 7.2 Good and special places

At a good place define $D_v$ to be the unramified pair with $N_v=0$ and

$$
\det(X-r_v(\Phi_v))=P_v(X). \tag{7.4}
$$

At a split strict semistable Steinberg place, let $\beta_v\in E^\times$ be the scalar of the raw unnormalized right-coset operator $U_v$ on the invariant graph line. Define $D_v=\operatorname{St}(\beta_v)$ on a basis $e_0,e_1$ by

$$
N_ve_1=e_0,\qquad N_ve_0=0, \tag{7.5}
$$

$$
r_v(\Phi_v)e_0=\beta_ve_0,
\qquad r_v(\Phi_v)e_1=q_v\beta_ve_1, \tag{7.6}
$$

with trivial finite inertia. The determinant condition forces

$$
\beta_v^2=s_v. \tag{7.7}
$$

When finite descent survives together with monodromy, inertia acts through a Frobenius-stable scalar character $\xi_v$. The common pair is $\operatorname{St}(\xi_v,\delta_v)$, obtained by replacing trivial inertia by $\xi_v$ and $\beta_v$ by the actual Frobenius eigenvalue $\delta_v$ on $\ker N_v$.

**Proposition 7.1 (the constructed special pair).** Assume the complete direct-quaternion split one-step Iwahori ledger: the quaternion algebra is split at $v$; the odd split or dyadically tensor-split PEL model exists; the component union and raw $U_v$ correspondence descend; and the characteristic-zero packet has the multiplicity-one and good-normalization support stated in the semistable-curve theorem. Then that theorem proves graph multiplicity one, nonzero rank-one monodromy, and the scalar equality $(\mathrm B_v)$ with $\beta_v$ equal to the raw unnormalized $U_v$ eigenvalue. Consequently the raw representation $\widetilde\rho_\lambda$ has local pair $\operatorname{St}(\beta_v)$ for every $\lambda$ away from $v$. The same assertion holds for $\rho_\lambda$ if (1.6) holds at $(v,\lambda)$.

**Proof.** Nearby cycles give $N^2=0$ and identify packet monodromy with the graph restriction--Gysin map. The good-normalization support kills the component-cohomology packet term; multiplicity two and the one-dimensional Iwahori new line then force both graph multiplicities to equal one. Strict semistability makes finite inertia trivial. The geometric $U_v$ calculation identifies Frobenius on $\ker N$ with the raw scalar $\beta_v$, and rank-two special recognition gives $\operatorname{St}(\beta_v)$. Every map is algebraic before completion, so the result holds at all coefficient places away from $v$. $\square$

**Proposition 7.2 (when a split special carrier can be constructed).** Let $F$ be totally real of degree $d\ge2$, let $\pi$ be a selected cuspidal parallel-weight-two split packet, and let $v$ be a selected special place at which the split-Iwahori comparison is desired. The compact one-split inverse theorem constructs a curve carrier split at $v$ whenever there is a set $W$ of eligible places with $(d-1)+|W|$ even and $v\notin W$. Applying Proposition 7.1 still requires its separate integral PEL ledger. In particular, at residue characteristic two Book 122's dyadically tensor-split ledger requires the resulting quaternion algebra to be split at **every** place above two, so one must have

$$
W\cap\{w:w\mid2\}=\varnothing. \tag{7.7a}
$$

If $d$ is odd, $W=\varnothing$ is parity-compatible. It gives a basic carrier split at every finite place and therefore clears the automorphic and tensor-splitting parts of the raw dyadic problem; Proposition 7.1 still requires the remaining dyadic PEL and component ledger. The current direct version of that ledger is not an available realization in mixed one-split signature: Book 118, Proposition 8.2 rules out its common-norm Hodge lift, as recorded in Book 122, Section 1.3. A different central modification therefore needs its own parahoric comparison. If $d$ is even, $W$ must be odd and nonempty. Consequently, in the controlled FLT SP situation where $2$ splits completely and every $v\mid2$ is selected special, another dyadic place cannot serve as the ramified singleton: doing so makes the quaternion algebra division at that dyadic factor and violates the complete tensor-splitting hypothesis. Even if there is an odd nonempty eligible set $W$ away from two, Proposition 7.1 applies only after a nonvacuous PEL realization and the remaining dyadic tensor and component ledger are supplied. If all eligible finite places lie above two, the prior books construct a weak curve carrier by choosing a dyadic singleton, but no dyadically split raw carrier.

**Proof.** If $W$ is parity-compatible, eligible, and avoids $v$, the compact inverse Jacquet--Langlands theorem constructs the quaternion algebra ramified at the inactive real places and at $W$; it is split at $v$. The curve decomposition and extraction theorems provide its raw rank-two packet. Proposition 7.1 applies only after its integral-model hypotheses are checked. At two, the first item of the dyadically tensor-split ledger requires

$$
B\otimes\mathbf Q_2\simeq
\prod_{w\mid2}M_2(\mathbf Q_2),
$$

which is equivalent here to excluding every dyadic place from $W$. When $d$ is odd, the empty set satisfies both the automorphic parity condition and this necessary splitting condition. When $d$ is even, a second dyadic eligible place solves the automorphic parity condition for a curve carrier but destroys the dyadic tensor ledger; it cannot solve the raw SP carrier problem. An odd nonempty eligible $W$ away from two satisfies both conditions in even degree. In either parity, the remaining hypotheses of Proposition 7.1 include an actual PEL-exact parahoric realization; the obstructed direct common-norm datum cannot supply it. Once a replacement and its full ledger are supplied, Proposition 7.1 gives the raw pair at every dyadic target. $\square$

### 7.3 Finite and tame dihedral types

Suppose monodromy vanishes after applying an algebraic type projector to the full equivariant stratum complex. Let $\tau_v$ be the resulting finite inertia representation over $E$. Frobenius permutes its isotypic pieces. On each orbit choose one representative and record the return map of the corresponding power of $\Phi_v$. These data determine a Frobenius-semisimple Weil representation, which we call $D_v$.

This assertion follows directly: decompose into inertia-isotypic components. Frobenius cycles the components in an orbit, and its return map determines the action after going once around the orbit. Inducing around all orbits reconstructs the representation. Thus inertia type alone is insufficient, but inertia type plus return maps is complete.

For a tame dihedral place, the datum has a more economical form. Let $K=F_v$, let $L_v/K$ be a quadratic extension, and let

$$
\theta_v:W_{L_v}\longrightarrow E^\times
$$

be a tame character with $\theta_v\ne\theta_v^\sigma$. Put

$$
D_v=\operatorname{Ind}_{W_{L_v}}^{W_K}\theta_v,
\qquad N_v=0. \tag{7.8}
$$

The value of $\theta_v$ on a Frobenius return element is part of the datum. In the unramified quadratic case geometric Frobenius exchanges the two inertia characters; in the ramified case the inertia subgroup itself has index two. These cases have different matrices and cannot be merged by a conductor calculation.

**Proposition 7.3 (recognition, not construction).** Suppose wild inertia is trivial on the selected packet part. If the tame finite descent complex, packet projector, type projector, monodromy-vanishing statement, and all Frobenius return maps are defined over $E$ and satisfy the selected principal or dihedral comparison hypotheses, then every raw local pair (7.1) is $D_v\otimes_EE_\lambda$. This includes the tame dihedral pair (7.8) when the quadratic cover and inducing character actually occur in the descent complex. The same statement holds for $\rho_\lambda$ without an additional hypothesis: Book 128, Lemma 3.2 proves (1.6) from the asserted vanishing of monodromy.

**Proof.** All differentials and projectors commute with coefficient extension. Hence the inertia decomposition and return maps on every $E_\lambda$-realization are scalar extensions of the common algebraic data. The finite-inertia reconstruction just described identifies the Weil representations. Monodromy vanishes on both sides, and Book 128, Lemma 3.2 passes the pair through global semisimplification. $\square$

### 7.4 Strict compatibility theorem

Let $S_{\mathrm{loc}}$ denote the finite places at which one of the verified local packages is needed; at places outside it the good package applies.

**Theorem 7.4 (common raw local pairs and the strictness criterion).** Assume that for every finite place $v$ of $F$, one of the following packages is available:

1. the complete smooth proper good-place ledger;
2. the complete constructed split-Iwahori special ledger of Proposition 7.1;
3. an equivariant tame semistable descent complex, with wild inertia trivial on the selected part, matching principal or scalar-special type projector, monodromy statement, and every Frobenius return map, supplied as recognition data;
4. the tame dihedral specialization of the recognition package in item 3.

Then the raw cohomological family has the common Frobenius-semisimple local pair $D_v$ at every allowed coefficient place. The pair is respectively unramified, special, finite type, or tame dihedral as described above. The zero-monodromy principal and dihedral rows already give the same pair on the semisimple family. If, in addition, (1.6) holds in every nonzero-monodromy bad row for every $\lambda$ with $v\nmid\ell(\lambda)$, then the semisimple weakly compatible family is strictly compatible in the sense of Definition 3.2; at good and zero-monodromy places (1.6) is automatic.

**Proof.** At a good place the smooth proper comparison and the imported polynomial (4.2) give (7.4) for every $\lambda$ away from $v$. Proposition 7.1 treats the constructed special case for $\widetilde\rho_\lambda$. Proposition 7.3 recognizes its tame principal, scalar-special, and dihedral types only from the complete supplied data. These identifications use one algebraic model and therefore hold for every allowed coefficient place. Book 128, Lemma 3.2 passes the zero-monodromy rows to $\rho_\lambda$; composing the remaining identifications with (1.6) gives (3.6). $\square$

The theorem has two independent boundaries. A common good polynomial at almost all places does not manufacture a finite-descent complex, type line, or return map at a remaining place. At nonzero monodromy a raw nearby-cycle calculation still does not prove (1.6); global semisimplification must be shown harmless by a separate argument. At zero monodromy Lemma 3.2 supplies that argument formally.

**Corollary 7.5 (residual-irreducible strictness at one coefficient place).** Let $\lambda$ be a coefficient place and suppose a stable lattice in $\rho_\lambda$, or in its covariant Tate twist, has absolutely irreducible residual reduction. Then $\widetilde\rho_\lambda\simeq\rho_\lambda$, so (1.6) holds for every $v\nmid\ell(\lambda)$. Every constructed or recognized raw comparison in Theorem 7.4 is therefore a comparison for $\rho_\lambda$.

**Proof.** Suppose first that $\rho_\lambda$ became reducible after scalar extension. Its invariant line is defined over some finite extension of $E_\lambda$. Extend the stable lattice and intersect it with that line. The intersection is rank one and saturated: if a uniformizer multiple of a lattice vector lies in the rational line, then the vector lies there too. Its reduction is therefore a nonzero proper stable line in the scalar extension of the residual representation, contradicting absolute residual irreducibility. Thus $\rho_\lambda$ is absolutely irreducible.

If the raw two-dimensional representation were reducible, a nonzero proper stable subspace would give at least two nonzero Jordan--Holder factors after semisimplification. But its semisimplification is $\rho_\lambda$, which is absolutely irreducible. Hence the raw representation is already irreducible and equals its semisimplification. Restriction to every decomposition group and formation of the Weil--Deligne pair preserve this global isomorphism, proving (1.6). Tate twist and duality preserve absolute irreducibility. $\square$

This corollary is not an independence-of-$\lambda$ theorem. Absolute irreducibility of one residual member does not prove it for the reductions at every other coefficient place.
No semisimplicity theorem for abelian varieties or for raw curve cohomology is being used here; in particular, the argument does not hide a Faltings input.

### 7.5 Ambient semisimplicity and uniform passage

The uniform problem has a precise ambient reduction. For the finite collection of actual smooth
projective curve carriers $C_i/E_i$ used to construct the packet family, impose

$$
\boxed{(\mathrm{SS}_{\mathrm{array}})\quad
H^1_{\mathrm{et}}((C_i)_{\overline E_i},\mathbf Q_\ell)
\text{ is semisimple as a }\mathbf Q_\ell[G_{E_i}]\text{-module}
\text{ for every relevant }i\text{ and }\ell.}
\tag{7.9}
$$

**Proposition 7.6 (uniform raw-to-global passage).** Under
$(\mathrm{SS}_{\mathrm{array}})$, every raw multiplicity representation extracted from these
carriers is globally semisimple after every displayed coefficient embedding. Hence (1.6)
holds for every $v\nmid\ell(\lambda)$, and every algebraic raw pair constructed in Theorem 7.4
is the full Frobenius-semisimple Weil--Deligne pair of the corresponding semisimple member.

**Proof.** Apply Book 128, Proposition 9.4 to each carrier and each coefficient
characteristic. Scalar extension, the rational packet idempotent, the selected split central
idempotent, and the Morita evaluation map preserve semisimplicity. Thus
$\widetilde\rho_\lambda\simeq\rho_\lambda$ globally for every realization. Restriction to a
decomposition group then preserves the actual representation, so formation of the
Weil--Deligne pair preserves finite inertia and the nilpotent operator $N$ as well as the
Frobenius return scalar. This does not make the local restriction semisimple: global
semisimplicity is compatible with unipotent local inertia and nonzero monodromy. $\square$

For each $C_i$, Book 36, (10.12) identifies the representation in (7.9) with
$V_\ell(\operatorname{Jac}(C_i))(-1)$ in the covariant convention, equivalently with its dual
through the principal polarization. Therefore the rational Tate-module
semisimplicity statement $(\mathrm{TS})$ isolated in Book 128, (9.6), is sufficient for
$(\mathrm{SS}_{\mathrm{array}})$. Book 41, Theorem 15.3 and Corollary 16.1 prove
$(\mathrm{TS})$ for these Jacobians from finiteness of their $K$-isogeny classes, and Section
16.2 proves the coefficient, idempotent, and multiplicity-space passage used here. Book 41 does
not prove those finite isogeny classes. Its standard uniform route still retains the
semistable-reduction, ramified Hodge-base-change, arithmetic toroidal compactification, and
integral metrized Hodge--theta interfaces, as well as the logarithmic-Hilbert and theta
upper-slope certificates; conditional on them, it proves the formal implication to (13.3r).
Book 41 does prove the subsequent finite polarized $K$-descent and Zarhin factor-cancellation
steps. Semisimplicity of the Hecke algebra and semisimplicity of the isogeny category do not
replace that gate.

This reduction is uniform over all embeddings above a fixed coefficient characteristic and
uses no local special-line argument, so it is noncircular. It also makes the raw global
$2$-adic representation semisimple if the ambient theorem is supplied at $\ell=2$. It does
not extend the prime-to-coefficient Weil--Deligne comparison to $v\mid\ell(\lambda)$; in
particular, at a dyadic base place the signed special pair is obtained here only from
coefficient places away from two.

## 8. Purity at bad places

### 8.1 The monodromy filtration

Purity for a ramified Weil--Deligne representation cannot mean that all eigenvalues of $r(\Phi_v)$ have the same absolute value. A special representation already has Frobenius eigenvalues differing by a factor $q_v$. The nilpotent operator explains the difference.

For a nilpotent $N$ on $V$, centered at an integer $w$, the monodromy filtration $M_\bullet$ is the unique increasing filtration satisfying

$$
N(M_i)\subseteq M_{i-2}(-1) \tag{8.1}
$$

and

$$
N^r:\operatorname{Gr}_{w+r}^M V
\xrightarrow{\sim}
\operatorname{Gr}_{w-r}^M V(-r) \tag{8.2}
$$

for all $r\ge0$ for which these groups occur.

**Definition 8.1 (Weil--Deligne purity).** A Frobenius-semisimple pair $(r,N)$ is pure of weight $w$ if every eigenvalue of geometric Frobenius on $\operatorname{Gr}_i^M V$ is a $q_v$-Weil number of weight $i$.

This convention makes (8.2) weight preserving: twisting by $(-r)$ raises weight by $2r$, taking weight $w-r$ to $w+r$.

When $N=0$, the filtration has only $\operatorname{Gr}_w^M=V$, so Definition 8.1 reduces to the familiar assertion that every Frobenius root has weight $w$.

### 8.2 Special parameters

Consider $D_v=\operatorname{St}(\beta_v)$ with $\beta_v$ of finite order. Set

$$
M_0=\operatorname{im}N=\ker N=Ee_0,
\qquad M_2=V. \tag{8.3}
$$

Centered at $w=1$, the nonzero graded pieces are

$$
\operatorname{Gr}_0^M=Ee_0,
\qquad
\operatorname{Gr}_2^M=V/Ee_0. \tag{8.4}
$$

Geometric Frobenius acts on them by $\beta_v$ and $q_v\beta_v$. Since a root of unity has weight zero, the two lines have weights zero and two. Moreover

$$
N:\operatorname{Gr}_2^M
\xrightarrow{\sim}\operatorname{Gr}_0^M(-1). \tag{8.5}
$$

Thus $\operatorname{St}(\beta_v)$ is pure of weight one.

For $\operatorname{St}(\xi_v,\delta_v)$, finite inertia does not alter weights. The pair is pure of weight one precisely when $\delta_v$ is a $q_v$-Weil number of weight zero. In the packet normalization this follows from the determinant once the special shape has been proved: the two Frobenius eigenvalues are $\delta_v$ and $q_v\delta_v$, while (5.1) gives determinant $q_v\eta(\Phi_v)$, so

$$
\delta_v^2=\eta(\Phi_v). \tag{8.5a}
$$

The right side has finite order, hence so does $\delta_v$. Thus special-type purity is closed by the matched determinant and local shape. For an arbitrary special pair without that determinant normalization, $N\ne0$ alone would not prove purity.

### 8.3 Finite-monodromy parameters

Suppose $N=0$ and inertia has finite image. Purity of weight one means that every eigenvalue of $r(\Phi_v)$, after taking a suitable Frobenius power preserving an inertia-isotypic component, has the absolute value dictated by residue degree and weight one.

For the finite types arising from the weight-two packet, this is a local algebraicity condition on the Frobenius return maps. The geometric local comparison identifies those maps with the automorphic ones, but the preceding local comparison book does not prove their complex absolute values. A weight-monodromy theorem or a direct return-map calculation must supply the weight-one normalization. The determinant fixes only the product of two roots and cannot replace this input.

For a dihedral parameter

$$
D_v=\operatorname{Ind}_{W_L}^{W_K}\theta_v, \tag{8.6}
$$

purity can be checked over $L$. If $f=[k_L:k_K]$ and $\Phi_L$ is geometric Frobenius over $L$, then $D_v$ is pure of weight one exactly when

$$
|\iota(\theta_v(\Phi_L))|=q_v^{f/2} \tag{8.7}
$$

for every complex embedding. Indeed, after restricting to $W_L$, the two characters are $\theta_v$ and $\theta_v^\sigma$; induction only permutes their Frobenius conjugates. Accordingly, a tame dihedral weight-two package proves purity only when it includes (8.7), not merely the algebraic inducing character.

Finite inertia by itself does not prove (8.7). An unramified twist can change the absolute values without changing inertia or conductor.

### 8.4 Local purity of the system

**Theorem 8.2 (purity of the common local pairs).** The semisimple packet system is pure of weight one at every good place. At a bad place its common raw Weil--Deligne pair is pure of weight one in the following cases:

1. special type with finite-order kernel scalar;
2. ramified special type with finite-order kernel scalar after removal of its stated finite inertia character;
3. tame principal type whose common Frobenius return maps satisfy the weight-one algebraic normalization;
4. tame dihedral type satisfying (8.7).

The conclusion is independent of $\lambda$. It applies to the local pair of $\rho_\lambda$ wherever (1.6) also holds.

**Proof.** Good-place purity is Theorem 6.2. Sections 8.2 and 8.3 verify the monodromy-graded weights of every listed common pair $D_v$. Its scalar realizations have the same algebraic eigenvalues viewed in different completions, so their complex absolute values do not depend on $\lambda$. Under (1.6), this pair is also $\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\!-\!ss}}$. $\square$

At a special place the two Frobenius eigenvalues of the Weil representation have weights zero and two. Calling the pair “pure of weight one” refers to the filtration (8.4), not to naive equal modulus. This is the most important normalization distinction at bad reduction.

## 9. Conductors and local factors

### 9.1 Artin and Swan conductors

Let $D=(r,N)$ be a Weil--Deligne representation of $W_{F_v}$ on $V$. Its conductor exponent is

$$
a(D)=a(r)+\dim V^{I_v}-\dim(\ker N)^{I_v}, \tag{9.1}
$$

where

$$
a(r)=\dim V-\dim V^{I_v}+\operatorname{Sw}(r). \tag{9.2}
$$

Combining the two formulas gives

$$
a(D)=\dim V-\dim(\ker N)^{I_v}+\operatorname{Sw}(r). \tag{9.3}
$$

The local Euler polynomial is

$$
P_v^{\mathrm{loc}}(T,D)
=\det(1-T,r(\Phi_v)\mid(\ker N)^{I_v}), \tag{9.4}
$$

and $L_v(T,D)=P_v^{\mathrm{loc}}(T,D)^{-1}$. These formulas show why neither the characteristic polynomial on all of $V$ nor the inertia representation alone determines the local factor.

The Swan conductor may be computed from the lower ramification filtration $J_i$ of a finite inertial quotient $J$:

$$
\operatorname{Sw}(r)
=\sum_{i\ge1}
\frac{|J_i|}{|J_0|}
\operatorname{codim}V^{J_i}. \tag{9.5}
$$

Equivalently, with upper numbering it is the integral $\int_0^\infty\operatorname{codim}V^{J^u}\,du$. Thus it depends on the filtered inertia representation, not merely on its abstract character.

### 9.2 Independence of the coefficient place

**Theorem 9.1 (conductor independence).** Let $\{\rho_\lambda\}$ be strictly compatible with common local pair $D_v$ at a finite place $v$. Then for every $\lambda$ with $v\nmid\ell(\lambda)$,

$$
a_v(\rho_\lambda)=a(D_v),
\qquad
\operatorname{Sw}_v(\rho_\lambda)=\operatorname{Sw}(r_v). \tag{9.6}
$$

In particular these integers are independent of $\lambda$.

**Proof strategy.** Strict compatibility identifies more than the numerical invariants: it identifies the entire pair after scalar extension. Dimensions of invariants, kernels, and ramification-fixed spaces are unchanged by extending a characteristic-zero field.

**Proof.** By (3.6), the local pair of $\rho_\lambda$ is $D_v\otimes_EE_\lambda$. Field extension preserves the ranks of $N$, $(\ker N)^{I_v}$, and $V^{J_i}$ for every ramification subgroup in the finite inertial quotient. Therefore (9.3) and (9.5) have the same value for every $\lambda$. $\square$

The qualification $v\nmid\ell(\lambda)$ cannot be omitted. At the coefficient residue characteristic, an Artin conductor may still be defined for the Galois representation, but the comparison with the prime-to-residue-characteristic Weil--Deligne construction used here requires additional theory.

There is also a converse warning. Equality of conductors for every $\lambda$ does not imply strict compatibility. Formulas (9.1)--(9.3) compress the local pair too severely.

### 9.3 Euler and epsilon factors

Because the common local pair is defined over $E$, formula (9.4) gives

$$
P_v^{\mathrm{loc}}(T)\in E[T] \tag{9.7}
$$

whose image in $E_\lambda[T]$ is the Euler polynomial of $\rho_\lambda$ for every allowed $\lambda$. Thus strict compatibility supplies coefficient-place independence of local Euler factors at bad places as well as good ones.

For epsilon factors, fix one algebraic additive character of specified conductor and the corresponding self-dual Haar measure, and enlarge $E$ to contain the finitely many roots of unity which occur. The epsilon factor of a Weil--Deligne pair depends on the finite Weil representation, $N$, the character, and the measure. Scalar extension transports the resulting algebraic epsilon factor to each completion. This is embedding-equivariance, not a numerical equality between unrelated displayed fields.

**Proposition 9.2.** In every strictly compatible local case, the Euler polynomial, conductor, Swan conductor, and monodromy rank are independent of $\lambda$. With the fixed algebraic auxiliary normalizations above, epsilon factors are transported coefficientwise from one algebraic value.

**Proof.** The first four invariants are algebraic constructions from $D_v$. The epsilon factor is functorial under scalar extension and is an invariant of the isomorphism class of $D_v$ once $\psi_v$ and the measure are fixed. $\square$

The additive character and measure must be held fixed. Changing them changes the epsilon factor by explicit determinant scalars even though the representation is unchanged.

### 9.4 Diagnostic calculations

The basic local types give quick checks on every formula.

**Unramified type.** Here $I_v=1$ and $N=0$. Thus $a(D_v)=0$ and

$$
P_v^{\mathrm{loc}}(T)=1-t_vT+q_vs_vT^2. \tag{9.8}
$$

**Special type.** For $\operatorname{St}(\beta_v)$, $\ker N$ is the line with Frobenius $\beta_v$. Hence

$$
a(D_v)=1,
\qquad
P_v^{\mathrm{loc}}(T)=1-\beta_vT. \tag{9.9}
$$

The other Frobenius eigenvalue $q_v\beta_v$ does not enter the Euler polynomial because it lies outside $\ker N$.

**Ramified special type.** For $\operatorname{St}(\xi_v,\delta_v)$, if $\xi_v$ is nontrivial on inertia, then $(\ker N)^{I_v}=0$, so the Euler polynomial is $1$. Because $\xi_v$ acts scalarly on both dimensions, (9.3) gives the exact formula

$$
a\bigl(\operatorname{St}(\xi_v,\delta_v)\bigr)=2a(\xi_v). \tag{9.9a}
$$

There is no additional monodromy term once the kernel has no inertia invariants.

**Tame dihedral type.** If neither inducing inertia character is trivial, then $V^{I_v}=0$, $N=0$, and

$$
P_v^{\mathrm{loc}}(T)=1,
\qquad a(D_v)=2 \tag{9.10}
$$

in the basic tame irreducible case. An unramified twist leaves (9.10) unchanged but alters the Frobenius return scalar. This is another demonstration that conductor independence is a consequence of strict compatibility, not a replacement for it.

## 10. Independence from embeddings and auxiliary choices

### 10.1 Changing an algebraic embedding

The packet has two kinds of embeddings. An embedding $E_0\hookrightarrow\mathbf C$ produces a coefficient-conjugate automorphic packet. An embedding $E\hookrightarrow\overline{\mathbf Q}_\ell$ selects a coefficient place and displays its local realization. Compatibility with both follows from algebraic scalar transport.

Let $\sigma:E\hookrightarrow E'$ be a field embedding. The $\sigma$-conjugate polynomial is obtained by applying $\sigma$ to $t_v$, $s_v$, and every matrix entry of $D_v$. The corresponding representation is

$$
{}^\sigma\rho_\lambda
=\rho_\lambda\otimes_{E_\lambda,\sigma}E'_{\lambda'}. \tag{10.1}
$$

**Theorem 10.1 (embedding independence).** The construction of the compatible system commutes with every coefficient embedding. More precisely:

1. conjugating the packet and then extracting its representation gives (10.1);
2. the good polynomial becomes $\sigma(P_v)$;
3. the determinant becomes $\chi^{-1}\eta^\sigma$;
4. the raw common local pair becomes $D_v^\sigma$, and the semisimple local pair does so under (1.6);
5. weights, conductor exponents, monodromy ranks, and dimensions of inertia invariants are unchanged.

**Proof.** Assertion 1 is Proposition 2.3. The next three follow by applying $\sigma$ to the algebraic identities defining the Hecke polynomial, pairing target, and local stratum actions. For assertion 5, a field embedding permutes complex embeddings and preserves dimensions and nilpotent ranks; Weil-number absolute values and conductor formulas are therefore unchanged. $\square$

This is the correct independence statement. It does not identify $\sigma(t_v)$ numerically with $t_v$ when $\sigma$ is nontrivial, and it does not apply $\sigma$ to transcendental periods.

### 10.2 Changing splittings and multiplicity modules

The representation (4.1) uses a splitting of a simple Hecke algebra and a choice of a standard simple module. Neither choice changes its isomorphism class.

Suppose

$$
A\otimes E\simeq M_d(E)
$$

in two ways. Any two such identifications differ by an inner automorphism after passing to an algebraic closure. Their standard modules are isomorphic. If $P$ and $P'$ are two simple modules, an isomorphism $u:P\to P'$ induces

$$
\operatorname{Hom}_A(P',H)
\longrightarrow\operatorname{Hom}_A(P,H),
\qquad f\longmapsto f\circ u. \tag{10.2}
$$

Changing $u$ by a scalar changes (10.2) by that scalar and not its isomorphism class as a Galois representation.

**Proposition 10.2.** The placewise rank-two representation is independent, up to unique isomorphism class and coefficient extension, of matrix coordinates, the standard simple module, and the chosen finite splitting field.

**Proof.** Morita equivalence identifies the multiplicity object with the module for the commutant of the simple factor. Inner changes of matrix coordinates give naturally isomorphic Hom objects. A larger splitting field extends all objects by scalars, as in Proposition 2.4. $\square$

The phrase “unique isomorphism class” does not select a preferred basis. Matrix representations related by conjugation describe the same family.

### 10.3 Changing the geometric carrier

Different eligible ramification sets can produce different one-split quaternion algebras and hence different curves. Their raw cohomological multiplicity spaces have no direct geometric comparison. Their semisimplifications can nevertheless be compared because both realize the same split cuspidal packet.

**Proposition 10.3 (semisimple carrier independence).** Let two eligible compact curve carriers realize the same split cuspidal packet, with the same coefficient embedding and determinant normalization. After one common finite coefficient extension, the semisimple representations extracted from the two carriers are isomorphic at every coefficient place. Hence they define the same weakly compatible system up to placewise isomorphism.

**Proof strategy.** The two representations already exist. Jacquet--Langlands gives them the same good Hecke polynomials. Chebotarev density and Brauer--Nesbitt then recognize the two semisimple representations; neither theorem is being used to manufacture a representation from polynomials.

**Proof.** Fix $\lambda$ and enlarge coefficients so that both representations are defined over one nonarchimedean field and the finite-dimensional algebra generated by their diagonal action on the direct sum is split. Outside the union of their finite bad sets, their Frobenius traces are the images of the same Hecke numbers $t_v$. Chebotarev density says that the conjugacy classes of these unramified Frobenius elements meet every open conjugacy-stable subset of $G_F$. The two trace functions are continuous class functions, so equality on those Frobenius classes implies equality on all of $G_F$.

For completeness, let $A$ be the finite-dimensional coefficient algebra generated by the diagonal image of $G_F$ in the endomorphisms of the direct sum. The two trace characters agree on the spanning subset coming from $G_F$, hence on $A$. They vanish on the radical of $A$, and the split semisimple quotient is a product of matrix algebras. The characters of its simple modules are linearly independent. Since both representations are semisimple, their simple constituents therefore occur with the same multiplicities. They are isomorphic. Repeating the argument at every $\lambda$ proves the assertion. $\square$

This proposition gives an isomorphism class, not a canonical intertwiner. It compares neither the raw representations nor their integral lattices. In particular, a raw special pair computed on one carrier passes to the common semisimple member only when (1.6) holds for that carrier and coefficient place.

### 10.4 The exact meaning of independence

It is useful to summarize what has become choice-free.

- The good-polynomial field $E_0$, good polynomials, finite character $\eta$, and good-place weights are intrinsic to the isolated packet. A bad algebraic pair is intrinsic once the constructed special ledger or the complete recognition data identify it; the raw global extension carrying it remains carrier dependent. The full packet center can be larger than $E_0$.
- A field of realization $E$ is auxiliary, but enlarging it only extends scalars.
- The representation at a place $\lambda$ is independent of bases, matrix coordinates, and splitting modules up to isomorphism.
- A perfect polarization pairing is unique only up to scalar, while its multiplier and determinant are intrinsic.
- Eligible curve carriers for the same split packet give the same semisimple system by Proposition 10.3; their raw cohomological extensions and integral lattices need not agree.
- Integral lattices remain dependent on their ambient integral realization until a stronger integral theorem identifies them.

These distinctions prevent the word “canonical” from carrying more content than the construction proves.

## 11. Integral lattices and their limits

This chapter records an imported boundary rather than rebuilding integral curve cohomology.
Book 127, Theorem 8.1(7) and Section 7.3 own the statements below.

### 11.1 Existence of stable lattices

Each continuous placewise representation has some stable $\mathcal O_\lambda$-lattice. The
choice is neither canonical nor synchronized across coefficient places.

**Lemma 11.1 (residual semisimplification).** Two stable full lattices in the same semisimple
$E_\lambda$-representation have reductions with the same semisimplified Jordan--Holder factors.
This formal fact does not identify their extension classes.

### 11.2 Saturated cohomological lattices

The raw rational packet block has a saturated intersection with integral curve cohomology.
Rational Morita extraction or global semisimplification does not turn that ambient lattice into
a canonical rank-two direct summand.

### 11.3 Congruence and projector denominators

Projector denominators, the discriminant of the Hecke order, coarse-level deck orders, and the
returned pairing index remain independent obstructions to integral splitting and self-duality.

### 11.4 What rational compatibility does not provide

Book 127 supplies no cross-$\lambda$ lattice, integral direct-summand projector, canonical
residual extension class, or coefficient-prime finite-flat quotient. Book 168's strict
compatibility is likewise rational and does not strengthen those conclusions.

## 12. The complete compatible-system theorem

### 12.1 Statement

We now collect the construction in the exact form available for the weight-two packets used in the arithmetic applications.

**Theorem 12.1 (compatible coefficient systems and purity).** Let $F$ be a totally real field and let $\Pi$ be a noncharacter parallel-weight-two packet with the following data.

1. The packet occurs in one finite algebraic Hecke module over $\mathbf Q$, stable under coefficient conjugation and equipped with a Hecke-stable full integral lattice, and has good-polynomial field

   $$
   E_0=\mathbf Q(t_v,s_v,\text{ central and component values}),
   $$

   All its coefficient conjugates occur in this module with isolating data sufficient to distinguish the desired constituent.
2. A compact Shimura-curve carrier in the proved one-split range realizes this conjugation-stable full finite Hecke block and admits multiplicity extraction of rank two at every coefficient place. For a split packet, such a carrier is constructed from a parity-compatible eligible set as in Corollary 4.3: odd and nonempty in even degree, and possibly empty in odd degree. Outside that range its existence is an explicit hypothesis.
3. The descended block has the component-twist covariance and polarization-compatible symmetric finite-module pairing required in the extraction theorem; after multiplicity extraction these data give the perfect alternating pairing with finite character $\eta$.
4. A finite extension $E/E_0$ contains the selected embeddings of the packet centers, splits the corresponding simple Hecke factors, and contains the finitely many tame local types.

Then for every finite place $\lambda$ of $E$ there is a continuous semisimple representation

$$
\rho_{\Pi,\lambda}:G_F\longrightarrow
\operatorname{GL}_2(E_\lambda) \tag{12.1}
$$

The same construction gives a raw cohomological representation $\widetilde\rho_{\Pi,\lambda}$ with $\rho_{\Pi,\lambda}=\widetilde\rho_{\Pi,\lambda}^{\mathrm{ss}}$. These objects have the following properties.

**Weak compatibility.** There is a finite set $S$, independent of $\lambda$, such that for every actual base-field place $v\notin S$ with $v\nmid\ell(\lambda)$ the representation is unramified and

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_v))
=X^2-t_vX+q_vs_v. \tag{12.2}
$$

**Determinant and duality.** For every $\lambda$,

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_\lambda,
\qquad
\rho_{\Pi,\lambda}^\vee
\simeq\rho_{\Pi,\lambda}(1)\otimes\eta_\lambda^{-1}. \tag{12.3}
$$

These identities are independent of the scalar normalization of the polarization.

**Good-place purity.** Every root of (12.2) has absolute value $q_v^{1/2}$ under every complex embedding. Thus the weakly compatible system is pure of weight one in the sense of Definition 6.1.

**Raw local compatibility.** Let $v$ be a finite place. If the constructed split-Iwahori special package of Proposition 7.1 is available, or if all the recognition data in one of the tame rows of Theorem 7.4 are supplied, then for every $\lambda$ with $v\nmid\ell(\lambda)$,

$$
\operatorname{WD}_v(\widetilde\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq D_v\otimes_EE_\lambda. \tag{12.4}
$$

Here $D_v$ is the algebraic unramified or special parameter constructed by the geometric theorem, or the tame principal, scalar-special, or tame dihedral parameter identified from the complete supplied recognition data. The latter three rows are not carrier-existence or return-map construction theorems.

**Strictness criterion.** If $N_v=0$, Book 128, Lemma 3.2 proves (1.6)
automatically. If $N_v\ne0$, retain (1.6) as a hypothesis. In either case,

$$
\operatorname{WD}_v(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq D_v\otimes_EE_\lambda. \tag{12.5}
$$

If one of these packages is available at every finite $v$ and (1.6) holds at every nonzero-monodromy bad $v$, the semisimple family is strictly compatible away from the varying coefficient residue characteristic. Corollary 7.5 supplies (1.6) at a coefficient place with absolutely irreducible residual reduction. Proposition 7.6 supplies it uniformly from $(\mathrm{SS}_{\mathrm{array}})$; Book 41 proves its reduction to finite carrier-isogeny classes but not the Faltings--Shafarevich moduli-height route supplying them uniformly. At a bad finite-monodromy place, purity of weight one also needs the separate return-map weight hypothesis of Theorem 8.2; the constructed special pair is already pure by Section 8.2.

**Local invariants.** In the range of (12.5), the local Euler polynomial, Artin and Swan conductor, and monodromy rank are independent of $\lambda$; normalized epsilon factors are coefficientwise realizations of one algebraic value. The global prime-to-$\lambda$ conductor ideal

$$
\mathfrak N(\rho_\lambda)
=\prod_{v\nmid\ell(\lambda)}
\mathfrak p_v^{a(D_v)} \tag{12.6}
$$

is obtained by omitting only the factors above $\ell(\lambda)$ from one common conductor datum.

**Coefficient and choice independence.** The construction commutes with coefficient embeddings and finite coefficient extension. It is independent, up to isomorphism, of bases, matrix splittings, simple-module coordinates, and polarization scaling. Eligible curve carriers for the same split packet yield the same semisimple system by Proposition 10.3. This does not compare their raw extensions or integral lattices.

**Integral structures.** Each $\rho_{\Pi,\lambda}$ has some stable lattice. The raw geometric carrier supplies a saturated lattice in the full cohomological packet block. Global semisimplification does not embed a new rank-two plane into that same lattice. No canonical integral rank-two direct summand, self-dual lattice, cross-$\lambda$ lattice, or finite-flat coefficient-prime quotient is asserted by this theorem.

### 12.2 Proof

Book 127, Theorem 8.1 supplies the raw family, its canonical semisimplification, the finite
exceptional set, (12.1)--(12.3), determinant and duality, total oddness, good-place purity, and
the lattice boundaries recorded in Chapter 11. Chapters 2 and 10 above prove that coefficient
conjugation, scalar extension, and carrier replacement preserve the resulting semisimple family.
Thus no curve-family or good-place argument is repeated here.

At a bad place, the local comparison argument computes the packet part of the equivariant nearby-cycle complex on the raw multiplicity space. For the complete split one-step Iwahori ledger, Book 122 identifies nonzero graph monodromy and the raw $U_v$ scalar, giving $\operatorname{St}(\beta_v)$ by Proposition 7.1. In the other tame rows, a common inertia representation and every Frobenius return map must first be supplied; Proposition 7.3 then recognizes the parameter. These data are algebraic over $E$ and commute with scalar extension, proving (12.4). Lemma 3.2 of Book 128 gives (12.5) in the zero-monodromy rows. In a nonzero-monodromy row, composing with (1.6) gives (12.5); Corollary 7.5 proves that identity at a residual-irreducible coefficient place, but no nearby-cycle calculation proves it uniformly over all coefficient places.

The monodromy filtrations in Chapter 8 prove local weight-one purity only under the listed return-map normalization hypotheses. The formulas of Chapter 9 read Euler factors, conductors, Swan terms, monodromy ranks, and normalized epsilon factors from the common $D_v$, proving the asserted transport and (12.6) wherever strict compatibility holds.

Propositions 2.3, 2.4, 10.2, 10.3, and Theorem 10.1 prove the coefficient, carrier, and auxiliary-choice assertions. The rank-two determinant identity shows that scaling a perfect alternating pairing cannot alter its multiplier. Finally, compactness gives some stable lattice, while intersection with integral cohomology gives a saturated lattice in the raw packet block. Sections 11.2--11.4 explain why none of the stronger integral conclusions follows without further hypotheses. $\square$

**Corollary 12.2 (the honest FLT SP output and carrier boundary).** Let $F$ be totally real of even degree, suppose $2$ splits completely in $F$, and let $\pi$ be a selected trivial-character parallel-weight-two packet which is special at every $v\mid2$.

Then the prior books construct the following data.

1. Choosing any dyadic singleton as the ramification set gives a compact curve carrier and hence a pure weight-one weakly compatible system with determinant $\chi_\lambda^{-1}$ in the untwisted geometric-Frobenius normalization.
2. Such a carrier is ramified at one dyadic factor and therefore does **not** satisfy Book 122's dyadically tensor-split ledger. Complete splitting of two and the existence of another dyadic special place do not by themselves construct a raw SP pair.

Assume in addition that there is an odd nonempty eligible set $W$ containing no place above two and that the resulting one-split carrier has an actual PEL-exact parahoric realization satisfying the dyadic tensor and component ledger of Proposition 7.1. This must be a replacement for the obstructed direct common-norm presentation, with its finite comparison to the basic carrier supplied. Away from the dyadic places, retain only the good or separately recognized local rows actually available for $\pi$. Then:

3. The single carrier attached to $W$ constructs, for every target $v\mid2$, the algebraic raw pair

   $$
   D_v=\operatorname{St}(\beta_v),
   \qquad \beta_v^2=1,
   $$

   at every coefficient place away from two. The pair is pure of weight one, has conductor one, and has Euler polynomial $1-\beta_vT$.
4. Its semisimple weak system is the same as that obtained from the dyadically ramified weak carriers in item 1, by Proposition 10.3.
5. At any coefficient place away from two whose stable lattice has absolutely irreducible residual reduction, Corollary 7.5 transfers every dyadic raw pair to the semisimple member. Thus that member has the full SP pair, sign, nonzero monodromy, and conductor one at every $v\mid2$.

In the covariant Tate normalization used by the FLT blueprint, put

$$
\rho^{\mathrm{cov}}_\lambda=\rho_\lambda(1).
$$

It has determinant $\chi_\lambda$ and, at a good place, arithmetic-Frobenius polynomial $X^2-t_vX+q_v$. At a dyadic special place the untwisted geometric eigenvalues are $\beta_v$ on $\ker N$ and $2\beta_v$ on the quotient. Since $\beta_v=\beta_v^{-1}$, arithmetic Frobenius on $\rho^{\mathrm{cov}}_\lambda$ acts by $\beta_v$ on the quotient and by $2\beta_v$ on the monodromy line. This is the SP sign and line convention consumed downstream.

The prior books supply neither the extra eligible set away from two from the dyadic hypotheses alone nor the replacement parahoric PEL comparison, and they do not prove item 5 simultaneously for every allowed coefficient place. Once the additional carrier just stated exists, Proposition 7.6 proves all formal reductions for an SP assertion at every coefficient embedding of residue characteristic different from two: it remains to supply $(\mathrm{SS}_{\mathrm{array}})$. Book 41 proves it from finite isogeny classes of the carrier Jacobians. Those classes are the exact arithmetic input; the standard uniform Faltings--Shafarevich source still needs its moduli-height part, while Book 41 proves finite polarized descent and Zarhin cancellation.

**Proof.** A dyadic singleton satisfies Book 104's odd nonempty selected ramification condition, so Theorem 12.1 gives item 1. Proposition 7.2 explains why that carrier fails the dyadic tensor ledger and proves item 2. Under the added away-from-two carrier hypothesis, Proposition 7.1 constructs every raw special pair, and Section 8.2 proves its purity from $\beta_v^2=1$. Proposition 10.3 identifies the semisimple systems obtained from the different eligible carriers. Corollary 7.5 proves the final transfer exactly at the residual-irreducible coefficient places. Twisting, then inverting geometric Frobenius, gives the final covariant formulas. $\square$

### 12.3 Variants and edge cases

Several boundary cases fit the theorem without changing its statement.

**Scalar good Frobenius.** The polynomial in (12.2) may have a repeated root. The determinant argument proves that it is still the characteristic polynomial, and purity fixes the modulus of the repeated root.

**Reducible semisimple systems.** The extraction theorem does not require absolute irreducibility for its determinant or good-polynomial conclusions. If

$$
\rho_\lambda=\chi_{1,\lambda}\oplus\chi_{2,\lambda},
$$

then trace and determinant record the unordered pair of characters at good places. The alternating pairing forces their product to be $\chi_\lambda^{-1}\eta_\lambda$. No extension class is claimed.

**Several places above one rational prime.** If $\lambda_1$ and $\lambda_2$ lie above the same $\ell$, they are separate members of the family. Their completions may have different ramification indices and residue degrees. Compatibility compares them through the same $E$-polynomials; it does not identify their underlying $\mathbf Q_\ell$-spaces.

**Residue extensions.** If a geometric place $u$ lies over the automorphic place $v$ with residue degree $f$, the common local pair is restricted from $W_{F_v}$ to $W_{F_u}$. Frobenius becomes $\Phi_v^f$ and the roots become $\alpha_v^f,\beta_v^f$. Every weight and conductor assertion must use the actual local extension.

**The coefficient residue characteristic.** For a fixed $\lambda$, equations (12.2), (12.4), and (12.5) deliberately omit $v\mid\ell(\lambda)$. Continuity of $\rho_\lambda$ remains true there, but crystalline, semistable, de Rham, Hodge--Tate, and finite-flat assertions require additional hypotheses and are outside this theorem.

**Wild finite descent.** The local comparison source explicitly excludes primitive wild parameters and does not identify a nontrivial wild descent action with an automorphic packet parameter. Accordingly the theorem above makes no wild compatibility claim. A tame chart cannot determine the filtered wild action or its Swan conductor.

**Nonminimal and old level.** Oldvectors enlarge $P_{\Pi,\lambda}$, not the rank of $W_{\Pi,\lambda}$. The full finite Hecke image is needed so that Morita extraction removes the whole level module. A sparse collection of spherical operators can leave an artificially large multiplicity space.

### 12.4 Dependency and hypothesis ledger

The proof uses the following prior mathematical packages. Book 127 is the direct source for the
weak curve-carried family, determinant, good-place purity, and integral boundary; its Books 37,
97, 104, 125, and 126 inputs are transitive here. Book 41 is the direct source for the
finite-isogeny-class-to-Tate-semisimplicity reduction used in Proposition 7.6 and for the exact
boundary of its Faltings--Shafarevich source. Book 118 is the direct source for the
common-norm Hodge-lift obstruction used in Proposition 7.2. Book 129 is only a later interface check and begins after a rational
member has been constructed.

| Conclusion in this book | Established source | Hypotheses retained here | Boundary |
|---|---|---|---|
| weak family, determinant, good-place purity, and lattice boundary | Book 127, Theorem 8.1 | one-split compact curve carrier, full component-routing block, selected center embedding and splitting field; for split packets, a parity-compatible selected set $W$ | in even degree no eligible place gives no carrier; strict bad-place compatibility, a canonical rank-two lattice, and a finite-flat quotient are not supplied |
| Weil-number calculus and good-place purity of curve $H^1$ | Book 37, *Weights and Weil Bounds for Curves and Abelian Varieties* | smooth proper curve over a finite field; geometric Frobenius; correspondence summand | it supplies no bad-place return-map weights |
| good-polynomial field, conjugate packets, and saturated eigenlattices | Book 97, *Algebraicity and Integral Structures of Weight-Two Packets* | one absolute $\mathbf Q$-algebraic conjugation-stable finite Hecke module; raw $T_v,S_v$ normalization; isolating data; intersection with a fixed integral module | a relative model gives only embeddings over its base field; the full packet center can exceed the field of good values; good eigenvalues can name only a near-equivalence block |
| eligible one-split packet | Book 104, *Global Jacquet--Langlands* | $F$ totally real of degree $d\ge2$; $(d-1)+|W|$ even; selected special or selected tame-dihedral factor at every $w\in W$ | in even degree no eligible place gives no carrier; a carrier for split-Iwahori geometry at $v$ must avoid $v$, while the dyadic tensor ledger further forces it to avoid every place above two; in odd degree $W=\varnothing$ clears these automorphic constraints |
| curve realization and multiplicity | Book 125, *Automorphic Decomposition of Shimura-Curve $H^1$* | actual one-split compact curve; full component-routing orbit; full finite Hecke image; separating component idempotent; multiplicity two | no surface or modular-curve substitute is supplied; the raw representation need not be semisimple |
| raw rank-two representations | Book 126, *Galois Representations from Weight-Two Shimura-Curve Cohomology* | full finite Hecke block, splitting field, common curve carrier, multiplicity two | oldspace dimension is not Galois rank; absolute irreducibility is not supplied |
| determinant and good polynomial | Book 126 | component-twist covariance, polarization-compatible symmetric finite-module pairing, full good-model ledger, and the actual residue-field comparison | a quadratic relation alone may only annihilate Frobenius; residue degree changes the middle coefficient |
| constructed raw split-Iwahori special pair | Book 122, *Semistable Models and Monodromy of Quaternionic Shimura Curves*, assembled in Book 128 | split quaternion algebra at $v$; a supplied PEL-exact parahoric realization with the complete odd-split or dyadically tensor-split ledger, including splitting at every dyadic factor in the latter case; component support; multiplicity one; raw unnormalized $U_v$ | the theorem proves $(\mathrm B_v)$ and rank-one $N$ on a supplied raw multiplicity space, but the direct common-norm realization is obstructed in mixed signature; a replacement finite comparison and raw-to-global passage are not constructed, and ramifying the carrier at another dyadic place violates the splitting ledger |
| tame principal, scalar-special, or dihedral parameter | Book 128, *Local--Global Compatibility for Weight-Two Galois Representations* | $v\nmid\ell$; the actual descent complex, type lines, monodromy branch, exchange maps, and every Frobenius return map | these are recognition criteria; they construct none of the missing tame return data for an arbitrary packet and cover no primitive wild row; raw-to-global passage is automatic only in the zero-monodromy principal and dihedral rows |
| strict bad parameter at one residual-irreducible coefficient place | Book 128, Lemmas 9.1--9.2 and Corollary 9.3 | a stable lattice with absolutely irreducible residual reduction at that $\lambda$ | the argument is coefficient-place by coefficient-place and gives no uniform all-$\lambda$ SP record |
| uniform nonzero-monodromy raw-to-global passage for the actual carrier array | Book 128, Proposition 9.4; Book 41, Theorem 15.3 and Corollary 16.1; and Proposition 7.6 | $(\mathrm{SS}_{\mathrm{array}})$; Book 41 derives it from finite isogeny classes of the carrier Jacobians | all coefficient extensions and packet factors are handled formally, but those finite isogeny classes remain unproved; Book 41's uniform Faltings--Shafarevich route lacks its moduli-height inputs, while finite polarized descent and Zarhin cancellation are proved; zero-monodromy passage needs none of this, and no comparison at $v\mid\ell$ follows |
| bad-place purity | Section 8 from the identified algebraic pair | special shape plus determinant closes the special row; finite-monodromy rows require the return-map absolute values such as (8.7) | determinant, finite inertia, and algebraicity do not prove finite-type weight one |
| semisimple carrier independence | Chebotarev density and Brauer--Nesbitt, applied in Proposition 10.3 | two already constructed semisimple representations with the same split-packet good polynomials | no raw extension, canonical intertwiner, or integral lattice is compared |

No theorem about later finite-flat quotients is used. Book 129 can construct a chosen all-level finite-flat tower only after a member has its own good-reduction abelian bridge and low-ramification hypotheses; it neither synchronizes coefficient places nor proves the SP pair. Book 183 therefore correctly retains a **controlled SP top datum** requiring the SP local object as well as local preservation at every coefficient place away from two. Books 184--185 propagate that datum through characteristic-zero effectivity and base-field assembly but do not create it. Book 187 likewise treats its SP family as an input and cannot repair its absence. Even degree and complete dyadic splitting provide several eligible dyadic places for the automorphic curve construction, but they do not close the raw geometric SP carrier problem: the ramification set must avoid two and a non-common-norm PEL-exact parahoric carrier with the full component comparison must be constructed. After such carriers are supplied, Proposition 7.6 reduces uniform prime-to-two raw-to-global preservation exactly to $(\mathrm{SS}_{\mathrm{array}})$; Book 41 reduces its arithmetic source further to finite carrier-isogeny classes, whose standard uniform Faltings--Shafarevich source remains unproved. The coefficient-prime integral bridge remains a separate boundary.

The downstream contract is therefore:

| Consumer | May use from this book | Must not infer |
|---|---|---|
| Book 129 | a rational raw packet plane, its semisimplification, determinant, and existence of placewise stable lattices | a canonical rank-two cohomological summand, coefficient-prime finite flatness, or one lattice across coefficient places |
| Book 183 | the constructed weak packet systems, coefficient conjugation, determinant, good purity, the conditional algebraic SP pair, and the reduction of uniform preservation to $(\mathrm{SS}_{\mathrm{array}})$ | the SP pair at every prime-to-two coefficient embedding unless its controlled top datum supplies preservation directly or supplies the missing ambient semisimplicity input |
| Books 184--185 | the packet systems and local objects already present in Book 183's controlled array | effectivity, base-field descent, or a new local comparison merely from good polynomials; those books prove their own characteristic-zero conclusions |
| Book 187 | a rational SP member only after Books 183--185 have actually produced it | the missing SP family, a three-adic good-reduction bridge, a stable lattice, or an all-level finite-flat tower |

## 13. The arithmetic package

### 13.1 A worked synthesis

Consider first a packet with trivial central-component character, so $s_v=1$ at every good place and

$$
\det\rho_\lambda=\chi_\lambda^{-1}. \tag{13.1}
$$

At a good place $v\nmid\ell(\lambda)$,

$$
P_v(X)=X^2-t_vX+q_v, \tag{13.2}
$$

and every conjugate of each root has modulus $q_v^{1/2}$. Hence every conjugate of $t_v$ lies in the interval allowed by

$$
|t_v|\le2q_v^{1/2}. \tag{13.3}
$$

At a split multiplicative place, the common raw pair is $\operatorname{St}(\beta_v)$ with $\beta_v=1$ or $-1$. It has

$$
N\ne0,\qquad a_v=1,\qquad
P_v^{\mathrm{loc}}(T)=1-\beta_vT. \tag{13.4}
$$

The sign distinguishes split from nonsplit multiplicative behavior while inertia and conductor remain the same. Its monodromy-graded Frobenius eigenvalues have weights zero and two, making the pair pure of center weight one.

At an irreducible tame dihedral place with no inertia invariants,

$$
D_v=\operatorname{Ind}_{W_L}^{W_{F_v}}\theta_v,
\qquad N=0, \tag{13.5}
$$

the local Euler polynomial is $1$ and the basic tame conductor is two. Nevertheless the inducing Frobenius value remains essential: changing it by an unramified scalar preserves both the Euler polynomial and conductor while changing the Weil representation. Strict compatibility retains that scalar.

For every coefficient place away from $v$, these local calculations are scalar realizations of the same algebraic raw data. The good polynomial and its purity survive a coefficient-prime change unconditionally. For the constructed special row, the bad-place weight follows from the determinant and $\beta_v^2=s_v$. Local type, monodromy, and conductor survive for the semisimple family only under (1.6); the finite-monodromy rows also need the return-map weight condition of Theorem 8.2.

### 13.2 A normalization audit

The following checks should accompany every use of the theorem.

1. $\Phi_v$ is geometric Frobenius and acts on $E_\lambda(1)$ by $q_v^{-1}$.
2. The good characteristic polynomial is $X^2-t_vX+q_vs_v$; the Euler denominator is $1-t_vT+q_vs_vT^2$.
3. Arithmetic Frobenius has the reciprocal-root polynomial of Book 127, Theorem 8.1(6).
4. The determinant is $\chi_\lambda^{-1}\eta_\lambda$, not $\chi_\lambda\eta_\lambda$.
5. Good-place purity means modulus $q_v^{1/2}$ for every complex conjugate; bad-place purity is the separate monodromy-graded assertion of Theorem 8.2.
6. A special parameter has Frobenius eigenvalues $\beta_v$ and $q_v\beta_v$, with $N$ mapping the second line to the first.
7. The local comparison computes the raw pair; strict compatibility of $\rho_\lambda$ also requires (1.6) and is asserted only for $v\nmid\ell(\lambda)$. Absolute residual irreducibility proves (1.6) at one coefficient place; $(\mathrm{SS}_{\mathrm{array}})$ proves it uniformly, and Book 41 proves that statement from finite carrier-isogeny classes, but neither those classes nor the Faltings--Shafarevich moduli-height route to them is supplied.
8. Inertial type plus conductor does not determine Frobenius return maps or monodromy.
9. Coefficient conjugation acts on $t_v$, $s_v$, $\eta$, and every local type value together.
10. A rational compatible system supplies stable lattices but not canonical integral direct summands.
11. A residue-degree change raises Frobenius roots to the corresponding power and changes the middle coefficient to their power sum.

These tests catch the most common sign, twist, and scope errors before they enter a global argument.

### 13.3 What has and has not been proved

The construction gives one coherent semisimple weakly compatible family. Its good Frobenius polynomials live in the good-polynomial field and survive every coefficient completion. Its determinant is fixed globally, and every complex conjugate of every good root has the expected absolute value. At every place covered by the geometric local comparison, the complete Frobenius-semisimple Weil--Deligne pair of the raw cohomological family is independent of the coefficient place.

Three load-bearing assertions remain logically separate. First, Book 122 does construct $(\mathrm B_v)$ and the raw special pair in its exact split one-step Iwahori range, whereas Book 128's tame principal, scalar-special, and dihedral rows merely recognize data that must already have been supplied. Second, Book 128 identifies the raw and globally semisimplified members formally when $N=0$ and, for nonzero monodromy, at a coefficient place with absolutely irreducible residual reduction. Proposition 7.6 proves every packet-theoretic reduction needed for uniform nonzero-monodromy passage. Book 41 proves the arithmetic implication from finite isogeny classes to $(\mathrm{SS}_{\mathrm{array}})$; those classes are the exact remaining input, and its standard uniform Faltings--Shafarevich source retains the moduli-height gap, although finite polarized descent and Zarhin cancellation are proved. Third, finite-monodromy return maps have not in general been proved to have the complex absolute values required for bad-place purity; the special row has no such gap because its shape and determinant force a finite-order kernel scalar.

For the FLT SP carrier problem, another dyadic special place supplies a compact basic curve carrier but not the dyadically tensor-split carrier required for the raw SP calculation: ramification at that auxiliary dyadic place violates Book 122's complete splitting hypothesis. Even with an odd nonempty eligible ramification set away from two, the raw stage still needs a non-common-norm PEL-exact parahoric realization and its finite component comparison, because Book 118 rules out the direct common-norm Hodge lift. After that geometry is supplied, the prime-to-two all-embedding SP record assumed by Book 183 remains conditional on $(\mathrm{SS}_{\mathrm{array}})$, because the residual-irreducibility argument applies only at the coefficient places where that residual hypothesis is known. This is now an exact arithmetic input rather than an unresolved coefficient-book reduction. The theorem also makes no comparison at the coefficient residue characteristic, constructs no globally canonical lattice, proves no integral self-duality at denominator primes, and produces no finite-flat quotient. It does not identify a quaternionic constituent from good eigenvalues unless the requisite isolating data are already present.

Thus the good-polynomial, determinant, conjugation, and weight-bound inputs are complete. The distinguished residual-irreducible member has the proved SP comparison only when the away-from-two eligible basic carrier, replacement PEL-exact parahoric comparison, and dyadic tensor ledger are supplied. Uniform strict SP compatibility at every coefficient place away from residue characteristic two follows formally from $(\mathrm{SS}_{\mathrm{array}})$, but that ambient semisimplicity input remains an explicit hypothesis for the later changing-prime assembly. The coefficient-two dyadic comparison is not part of this conclusion.

### 13.4 Conclusion

A weight-two packet satisfying the absolute rationality hypotheses determines a semisimple representation at every coefficient place. Its algebraic conjugates assemble into a single weakly compatible coefficient system. The common field records the raw Hecke polynomials and finite component character; the local geometric packages record the bad parameters of the raw multiplicity spaces.

The determinant and pairing organize the family globally:

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_\lambda,
$$

and the good Frobenius polynomial is

$$
X^2-t_vX+q_vs_v.
$$

Smooth proper geometry gives good-place weight one, including every complex conjugate of every root. Nearby-cycle geometry supplies the finer raw bad-place package: finite inertia, nilpotent monodromy, and Frobenius return maps. These data are algebraic before a coefficient place is chosen.

The boundary is exact. When the eligible carrier and complete split-Iwahori ledger are available, the special pair is geometrically constructed, and absolute residual irreducibility proves its passage to the semisimple member at the coefficient place where that residual condition holds. Proposition 7.6 proves passage at every allowed coefficient embedding from $(\mathrm{SS}_{\mathrm{array}})$. Book 41 proves the Tate lattice theorem needed after finite carrier-isogeny classes are known; those classes, not Hom--Tate or packet linear algebra, are the exact unsupplied input. Its standard uniform source is the still-missing Faltings--Shafarevich moduli-height package; finite polarized descent and Zarhin cancellation are proved. Finite-monodromy bad purity still requires the return-map weight. Rational compatibility does not synchronize integral lattices, and coefficient-residue-characteristic comparisons require separate hypotheses. Subject to these boundaries, coefficient embeddings, polarization scalars, splitting fields, and eligible curve carriers alter presentations but not the semisimple good compatible data.
