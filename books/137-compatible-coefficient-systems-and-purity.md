# Compatible Coefficient Systems and Purity

## Contents

1. [One arithmetic object seen at many coefficient places](#1-one-arithmetic-object-seen-at-many-coefficient-places)
   - [The changing-prime problem](#11-the-changing-prime-problem)
   - [Standing fields and conventions](#12-standing-fields-and-conventions)
   - [What the preceding constructions provide](#13-what-the-preceding-constructions-provide)
   - [The logical route](#14-the-logical-route)
2. [Coefficient fields, embeddings, and places](#2-coefficient-fields-embeddings-and-places)
   - [The Hecke field and a field of realization](#21-the-hecke-field-and-a-field-of-realization)
   - [Embeddings into local fields](#22-embeddings-into-local-fields)
   - [Conjugate packets](#23-conjugate-packets)
   - [Changing or enlarging the coefficient field](#24-changing-or-enlarging-the-coefficient-field)
3. [Weak and strict compatibility](#3-weak-and-strict-compatibility)
   - [Common Frobenius polynomials](#31-common-frobenius-polynomials)
   - [Weakly compatible systems](#32-weakly-compatible-systems)
   - [Strictly compatible systems](#33-strictly-compatible-systems)
   - [Why the distinction matters](#34-why-the-distinction-matters)
4. [Constructing the family from a weight-two packet](#4-constructing-the-family-from-a-weight-two-packet)
   - [The family at coefficient places](#41-the-family-at-coefficient-places)
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
13. [The complete compatible-system theorem](#13-the-complete-compatible-system-theorem)
    - [Statement](#131-statement)
    - [Proof](#132-proof)
    - [Variants and edge cases](#133-variants-and-edge-cases)
    - [Dependency and hypothesis ledger](#134-dependency-and-hypothesis-ledger)
14. [The arithmetic package](#14-the-arithmetic-package)
    - [A worked synthesis](#141-a-worked-synthesis)
    - [A normalization audit](#142-a-normalization-audit)
    - [What has and has not been proved](#143-what-has-and-has-not-been-proved)
    - [Conclusion](#144-conclusion)

## 1. One arithmetic object seen at many coefficient places

### 1.1 The changing-prime problem

A single weight-two automorphic packet gives algebraic Hecke numbers. Choosing a finite place of their field turns those numbers into elements of a nonarchimedean field and permits a Galois representation to be extracted from cohomology. Repeating this construction at another coefficient place produces a representation on another topological vector space. There is no sensible linear isomorphism between those two spaces: their scalar fields may have different residue characteristics. The arithmetic assertion must therefore be phrased through data which exist before either completion is chosen.

At a good finite place $v$ of the base field, that common datum is the polynomial

$$
P_v(X)=X^2-t_vX+q_vs_v. \tag{1.1}
$$

Here $q_v$ is the residue cardinality, while $t_v$ and $s_v$ lie in one number field. After embedding that field into any allowed coefficient completion, $P_v$ becomes the characteristic polynomial of geometric Frobenius. This is **weak compatibility**.

At a bad place, a characteristic polynomial is not enough. Inertia can be finite, monodromy can be nonzero, and Frobenius acts on inertia-isotypic pieces. The common datum must be a Weil--Deligne representation defined over a number field. Requiring every allowed coefficient realization to be obtained from this one local datum is **strict compatibility**. It remembers exactly what weak compatibility forgets.

The purpose of this book is to assemble the representations attached to all coefficient conjugates of a weight-two packet into such a system. We prove independence from the chosen algebraic embedding, from harmless enlargements of the coefficient field, and from the scalar used to normalize a polarization. We prove purity of weight one and independence of conductors. At every finite place away from the varying coefficient residue characteristic, we prove strict compatibility in the good, special, finite-type, and tame dihedral cases for which the geometric local comparison has already been established.

### 1.2 Standing fields and conventions

Let $F$ be the number field over which the global Galois representations are defined. In the curve applications $F$ is totally real. Let $\Pi$ be a noncharacter parallel-weight-two packet in the geometric range under consideration. Its raw good Hecke polynomial at a finite place $v$ is (1.1), with

$$
t_v=t_v(\Pi),\qquad s_v=s_v(\Pi).
$$

Let $E_0$ be the number field generated by the $t_v$, the $s_v$, and the finite central and component values. We call it the **Hecke field**. When a simple Hecke factor has a Schur obstruction, choose once and for all a finite extension $E/E_0$ which splits it and contains all finite type data used below. The system is realized over $E$; its polynomials and determinant descend to $E_0$. Enlarging $E$ later changes only scalars.

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

Second, cohomological extraction gives, for every $\lambda$, a continuous semisimple rank-two representation

$$
\rho_\lambda:G_F\longrightarrow\operatorname{GL}_2(E_\lambda) \tag{1.4}
$$

from a compact Shimura curve. Its determinant is

$$
\det\rho_\lambda=\chi_\lambda^{-1}\eta, \tag{1.5}
$$

where $\eta$ is a finite central-component character with values in $E_0^\times$. At every place satisfying the full good-model hypotheses and with $v\nmid\ell(\lambda)$, the representation is unramified and has polynomial (1.1).

Third, the low-dimensional weight theorem proves that smooth proper curve $H^1$ is pure of weight one. Purity passes to correspondence summands and hence to the rank-two multiplicity space.

Fourth, the local comparison theorem identifies the full Frobenius-semisimple Weil--Deligne parameter in the verified good, special, finite descent, and tame dihedral cases. It also proves equality of the corresponding Euler factors, conductors, and local constants.

These inputs do not yet constitute a compatible-system theorem. We must organize coefficient embeddings, show that all local data have a common algebraic model, and separate rational compatibility from integral choices.

### 1.4 The logical route

The construction follows a strict order.

1. Fix the Hecke field and a common field of realization.
2. Index representations by finite places of that field, not by unnamed embeddings into algebraic closures.
3. Prove weak compatibility from the common good Hecke polynomial.
4. Identify the determinant and show that changing a polarization does not change it.
5. Deduce good-place purity from the geometric carrier.
6. Package every verified bad local parameter over the common number field and deduce strict compatibility.
7. Read conductors, local factors, and monodromy purity from those common parameters.
8. Treat stable lattices only after the rational family is complete.

The order prevents three circular arguments. Purity is not inferred from reciprocal roots alone. A quadratic annihilator is not called a characteristic polynomial before the determinant is known. Equality of conductor is not used as a substitute for equality of Weil--Deligne parameters.

## 2. Coefficient fields, embeddings, and places

### 2.1 The Hecke field and a field of realization

The distinction between $E_0$ and $E$ solves two different descent problems. The coefficients of (1.1) naturally belong to $E_0$. The rank-two multiplicity space can require $E$ because a simple factor of the finite Hecke algebra may be a nonsplit central simple algebra over its center.

**Proposition 2.1 (finite common field).** There is a finite extension $E/E_0$ over which every simple packet factor and every finite inertial type in the stated local range splits. The field $E$ may be chosen normal over $\mathbf Q$, so every embedding of $E_0$ extends to an automorphism of $E$ and all coefficient conjugates occur inside it.

**Proof strategy.** Each obstruction is finite-dimensional algebraic data, so each is killed by a finite extension; a compositum handles all of them simultaneously.

**Proof.** A finite-dimensional central simple algebra has a finite splitting field. A finite inertial group has finitely many matrix entries in algebraic closures, and adjoining them gives a finite field. A tame inducing character used at one of the finitely many ramified places has finite-degree algebraic values. There are only finitely many bad places, so the compositum of these fields is finite over $E_0$. Taking its normal closure over $\mathbf Q$ gives the last assertion, and the extension theorem for embeddings extends every embedding of $E_0$ to an automorphism of that normal closure. $\square$

The word “common” does not mean minimal. A larger field may be convenient, and the system will be unchanged up to scalar extension. The genuinely intrinsic coefficient field for the good polynomials remains $E_0$.

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

Kernels, images, ranks, and semisimplification commute with this scalar extension.

**Proof.** Choose a basis. The matrix after scalar extension is obtained by applying $j$ to every entry, so its determinant polynomial is obtained by applying $j$ to every coefficient. Flatness of field extension preserves exact sequences, hence kernels, images, and ranks. A composition series extends to a composition series after a finite splitting extension, giving the assertion about semisimplification. $\square$

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

**Proposition 2.3 (conjugation of extracted data).** Suppose the full packet block and its multiplicity construction are defined over their algebraic Hecke data in $E_0$ and split over a field $E$ normal over $\mathbf Q$. For every $\sigma\in\operatorname{Aut}(E/\mathbf Q)$ and every finite place $\lambda$ of $E$, scalar conjugation carries the representation attached to the $\sigma$-conjugate block at $\lambda$ to the representation attached to the original block at $\sigma^{-1}\lambda$. Its determinant and every verified local parameter are obtained by applying $\sigma$ to their algebraic coefficients.

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

### 4.1 The family at coefficient places

Fix the field $E$ of Section 2.1. For each finite place $\lambda$ of $E$, choose the cohomological realization corresponding to the embedding $E\hookrightarrow E_\lambda$. In the curve case let $A_\lambda$ be the split finite Hecke block, $P_{\Pi,\lambda}$ its simple finite module, and $H_{\Pi,\lambda}$ the packet part of $H^1$. Define

$$
W_{\Pi,\lambda}
=\operatorname{Hom}_{A_\lambda}
(P_{\Pi,\lambda},H_{\Pi,\lambda}). \tag{4.1}
$$

Evaluation gives

$$
P_{\Pi,\lambda}\otimes_{E_\lambda}W_{\Pi,\lambda}
\xrightarrow{\sim}H_{\Pi,\lambda}. \tag{4.2}
$$

The multiplicity theorem gives $\dim W_{\Pi,\lambda}=2$. Galois commutes with the Hecke algebra, hence acts on the Hom factor. Put

$$
\rho_\lambda=igl(W_{\Pi,\lambda}\bigr)^{\mathrm{ss}}. \tag{4.3}
$$

At old level the finite module $P_{\Pi,\lambda}$ may have dimension greater than one. Formula (4.1) still extracts rank two. Choosing a single oldvector would not be canonical and is not part of the construction.

### 4.2 Continuity and semisimplicity

The space (4.1) is a closed subspace of a finite product of copies of cohomology: $A_\lambda$-linearity is expressed by finitely many closed linear equations. Therefore its Galois action is continuous. A Jordan--Holder semisimplification remains continuous and preserves characteristic polynomials, traces, determinants, inertia semisimplification, and the associated Frobenius-semisimple Weil--Deligne object.

**Lemma 4.1.** The isomorphism class of (4.3) is independent of a composition series and commutes with finite extension of $E_\lambda$.

**Proof.** Jordan--Holder gives the same multiset of simple factors for every composition series. Their direct sum therefore has a unique isomorphism class. Field extension is flat; after passing to a splitting field it extends the same simple factors with their multiplicities. $\square$

This semisimplicity is a definition of the extracted object, not a theorem that every cohomological extension splits. That distinction matters integrally and at the coefficient prime.

### 4.3 The good-place polynomial

Let $v\notin S$, $v\nmid\ell(\lambda)$, and suppose first that the place of the reflex field has the same residue field as $v$. Smooth proper specialization makes $\rho_\lambda$ unramified. The extended Hecke correspondence gives the operator relation

$$
\Phi_v^2-t_v\Phi_v+q_vs_v=0. \tag{4.4}
$$

The alternating pairing gives independently

$$
\det\rho_\lambda(\Phi_v)=q_vs_v. \tag{4.5}
$$

Subtracting (4.4) from Cayley--Hamilton yields

$$
(\operatorname{Tr}\rho_\lambda(\Phi_v)-t_v)\rho_\lambda(\Phi_v)=0.
$$

Frobenius is invertible, so its trace is $t_v$. Hence

$$
\det(X-\rho_\lambda(\Phi_v))
=X^2-t_vX+q_vs_v. \tag{4.6}
$$

This proof includes scalar Frobenius. A degree-two annihilator alone would not.

If the actual residue extension has degree $f$, geometric Frobenius upstairs is the $f$th power of the downstairs Frobenius and $q_u=q_v^f$. If $\alpha_v,\beta_v$ are the roots of (4.6), the upstairs polynomial is

$$
(X-\alpha_v^f)(X-\beta_v^f). \tag{4.7}
$$

One must not replace $q_v$ by $q_v^f$ while leaving the middle coefficient unchanged.

### 4.4 Weak compatibility theorem

**Theorem 4.2 (packet family at good places).** Let $\Pi$ be a noncharacter parallel-weight-two packet with a compact Shimura-curve realization satisfying the extraction hypotheses. Let $E$ split the packet block. Then the family $\{\rho_\lambda\}_\lambda$ of (4.3) is an $E$-rational weakly compatible system of rank two. Its exceptional set may be chosen independently of $\lambda$, and its common good polynomial is (3.4).

**Proof strategy.** Every coefficient realization is cut from the same algebraic Hecke packet. The good model supplies unramifiedness, while the Hecke relation and the common determinant identify the entire characteristic polynomial.

**Proof.** The packet construction and scalar transport give a continuous semisimple rank-two representation at every $\lambda$. Choose $S$ to contain the finitely many places excluded by the integral model, level, packet, component, and correspondence ledgers. For $v\notin S$ and $v\nmid\ell(\lambda)$, smooth proper base change gives unramifiedness. Equations (4.4)--(4.6) identify the characteristic polynomial with the image in $E_\lambda[X]$ of the polynomial in $E_0[X]$. These are precisely the conditions of Definition 3.1. $\square$

The theorem does not compare the vector spaces for two different $\lambda$. It compares their Frobenius polynomials through the common field $E_0$. That is the only field-independent comparison which is naturally available.

## 5. Determinants, pairings, and polarizations

### 5.1 The common determinant character

The constant term in (3.4) varies with $v$ in a controlled way. Let

$$
\eta:G_F\longrightarrow E_0^\times \tag{5.1}
$$

be the finite central-component character. Its image consists of roots of unity, and at every good place

$$
\eta(\Phi_v)=s_v. \tag{5.2}
$$

For each $\lambda$, composing (5.1) with $E_0\hookrightarrow E_\lambda$ gives $\eta_\lambda$. The determinant formula is

$$
\boxed{\det\rho_\lambda=\chi_\lambda^{-1}\eta_\lambda.} \tag{5.3}
$$

Because $\chi_\lambda(\Phi_v)=q_v^{-1}$, formula (5.3) gives $q_vs_v$ on geometric Frobenius. Thus the determinant itself forms a rank-one strictly compatible system away from coefficient residue characteristic.

**Proposition 5.1 (determinant compatibility).** The characters $\det\rho_\lambda$ are obtained from the single algebraic character $\eta$ and the compatible cyclotomic characters by (5.3). For every $v\nmid\ell(\lambda)$, their local Weil representations, inertia restrictions, conductors, and Frobenius values are independent of $\lambda$ after scalar extension.

**Proof.** The finite character $\eta$ factors through one finite quotient of $G_F$. Its representations over all completions are scalar extensions of the same $E_0$-line. The cyclotomic character is unramified away from $\ell$ and takes geometric Frobenius to $q_v^{-1}$ in every coefficient field. Products and inverses preserve compatibility. The conductor of the product is read from the same finite inertia character because the cyclotomic factor is unramified at $v\nmid\ell$. $\square$

### 5.2 Alternating pairings in rank two

Poincare duality on curve cohomology pairs the packet with its adjoint. Removing the finite Hecke module and using the central-component descent gives a perfect alternating pairing

$$
\psi_\lambda:W_{\Pi,\lambda}\times W_{\Pi,\lambda}
\longrightarrow E_\lambda(-1)\otimes\eta_\lambda. \tag{5.4}
$$

For a two-dimensional vector space $W$, every nonzero alternating form $\psi:W\times W\to M$ satisfies

$$
\psi(gx,gy)=\det(g)\psi(x,y). \tag{5.5}
$$

Indeed, both sides are alternating forms, and on a basis the scalar relating them is the determinant of the matrix of $g$. Galois equivariance of (5.4) therefore proves (5.3).

The factor $\eta$ is indispensable. The adjoint packet need not be literally the same finite Hecke packet; it differs by the component character dictated by the central action. Erasing the finite Hecke factor from the ambient pairing without tracking its adjoint would lose precisely this character.

**Corollary 5.2.** There is a Galois-equivariant isomorphism

$$
\rho_\lambda^\vee
\simeq \rho_\lambda(1)\otimes\eta_\lambda^{-1}. \tag{5.6}
$$

**Proof.** Send $x$ to the functional $y\mapsto\psi_\lambda(x,y)$. The target of the pairing gives

$$
W\simeq W^\vee\otimes E_\lambda(-1)\otimes\eta_\lambda.
$$

Rearranging yields (5.6). $\square$

### 5.3 Independence of the polarization

A polarization enters the construction by identifying the adjoint packet and by making the cohomological pairing perfect. It does not become an extra parameter of the resulting compatible system.

Suppose $\psi_\lambda$ and $\psi'_\lambda$ are two nonzero alternating pairings on the same two-dimensional absolutely irreducible representation, both with target $E_\lambda(-1)\otimes\eta_\lambda$. Their ratio is a Galois-invariant element of the one-dimensional space

$$
\operatorname{Hom}
(\textstyle\bigwedge^2W, E_\lambda(-1)\otimes\eta_\lambda),
$$

so they differ by a scalar in $E_\lambda^\times$. In the reducible semisimple case, the determinant identity (5.5) still shows directly that any nonzero alternating form with the stated target has the same multiplier.

**Theorem 5.3 (polarization independence).** Assume two geometric polarizations on the same extracted packet block induce perfect packet pairings with the same adjoint and central-component normalization. Then they yield the same determinant character (5.3), the same good Frobenius polynomials, and the same rational compatible system. Rescaling a polarization or its factor pairing changes only the chosen representative of $\psi_\lambda$.

**Proof.** The underlying multiplicity representation (4.1) is defined by the Hecke and Galois actions, not by the scale of the pairing. Each perfect alternating pairing has multiplier equal to $\det\rho_\lambda$ by (5.5). The target character is fixed by the Tate twist and $\eta$, so both give (5.3). The good polynomial is then determined by the Hecke annihilator and determinant as in Section 4.3. Thus none of the representation data changes. $\square$

The hypothesis “same adjoint and central-component normalization” is substantive. Reversing a right-action convention without conjugating the component character can replace $\eta$ by $\eta^{-1}$. That is a normalization error, not a new polarization.

At the integral level two polarizations can produce lattices with different duality indices at primes dividing their degrees. Theorem 5.3 is a rational assertion and does not erase that integral distinction.

### 5.4 Duality and reciprocal roots

Let $\alpha_v,\beta_v$ be the roots of (3.4). From their product,

$$
\alpha_v\beta_v=q_vs_v. \tag{5.7}
$$

Duality therefore sends the multiset of roots to

$$
\left\{\frac{q_vs_v}{\alpha_v},
\frac{q_vs_v}{\beta_v}\right\}
=\{\alpha_v,\beta_v\}. \tag{5.8}
$$

This reciprocal relation alone does not prove purity. The pair $R$ and $q_v/R$ has the same product for every positive real $R$, but the two numbers need not have modulus $q_v^{1/2}$. Positivity and the geometric weight theorem provide the missing assertion in Chapter 6.

For arithmetic Frobenius the roots are $\alpha_v^{-1},\beta_v^{-1}$ and the characteristic polynomial is

$$
X^2-\frac{t_v}{q_vs_v}X+\frac1{q_vs_v}. \tag{5.9}
$$

Formula (5.9) is a useful check: inversion changes both the middle and constant coefficients.

## 6. Purity at the good places

### 6.1 Weil numbers and system weight

An algebraic number $\alpha$ is a $q$-Weil number of weight $w$ if

$$
|\iota(\alpha)|=q^{w/2} \tag{6.1}
$$

for every embedding $\iota:\mathbf Q(\alpha)\hookrightarrow\mathbf C$. Testing one complex embedding is insufficient because the characteristic polynomial is algebraic and all of its conjugates occur in the coefficient packet.

**Definition 6.1 (pure compatible system).** A weakly compatible system with polynomials $P_v$ is **pure of weight $w$** if, for every $v$ outside its exceptional set, every root of $P_v$ is a $q_v$-Weil number of weight $w$.

The definition is independent of the choice of coefficient field. Enlarging $E$ neither changes the roots as algebraic numbers nor creates new complex absolute values. A Tate twist by $(n)$ changes the weight from $w$ to $w-2n$.

### 6.2 Purity inherited from curves

For a good place $v$, smooth proper specialization identifies the packet part of the generic Shimura-curve cohomology with a Frobenius-stable summand of the $H^1$ of a smooth proper curve over $\mathbf F_{q_v}$. The low-dimensional weight theorem says every Frobenius root on that $H^1$ has all complex absolute values $q_v^{1/2}$.

Under evaluation (4.2), Frobenius acts trivially on the finite Hecke module and through $\rho_\lambda(\Phi_v)$ on the multiplicity factor. Therefore every root of the rank-two factor occurs among the roots of the cohomology block. This proves:

**Theorem 6.2 (good-place purity).** The weakly compatible rank-two packet system of Theorem 4.2 is pure of weight one.

**Proof.** Choose one $\lambda$ with $v\nmid\ell(\lambda)$. The two roots of $P_v$ are the roots of geometric Frobenius on $\rho_\lambda$. By (4.2) they occur in smooth proper curve $H^1$, hence every complex conjugate has modulus $q_v^{1/2}$. Because $P_v\in E_0[X]$, this is a statement about the algebraic roots themselves and is independent of $\lambda$. Repeat for every $v\notin S$. $\square$

The proof is not circular. It derives the common polynomial from correspondences and determinant, then derives absolute values from geometry. It does not infer weight one merely from the constant term $q_vs_v$.

### 6.3 Consequences for Hecke eigenvalues

Let $\alpha_v,\beta_v$ be the roots of $P_v$. Purity and (5.7) give, under every complex embedding,

$$
|\alpha_v|=|\beta_v|=q_v^{1/2},
\qquad |s_v|=1. \tag{6.2}
$$

Therefore

$$
|\iota(t_v)|
=|\iota(\alpha_v+\beta_v)|
\le 2q_v^{1/2}. \tag{6.3}
$$

Since $s_v$ is an algebraic integer and all its conjugates have absolute value one, it is a root of unity. In the present construction this is also visible from the finite character $\eta$.

**Corollary 6.3.** For every good $v$, $t_v$ satisfies the weight-two Weil bound (6.3), $s_v$ has finite order, and the roots of $P_v$ are algebraic integers.

**Proof.** The bound and unit modulus follow from (6.2). Algebraic integrality of the roots follows because $P_v$ is monic with algebraic-integer coefficients: $t_v$ is integral by the stable Hecke lattice, and $q_vs_v$ is integral. $\square$

A repeated root is allowed. If $P_v=(X-c)^2$, then $|\iota(c)|=q_v^{1/2}$. Purity does not require regular semisimple Frobenius.

## 7. Local Weil--Deligne compatibility

### 7.1 The common local datum

Fix a finite place $v$ of $F$. For every $\lambda$ with $v\nmid\ell(\lambda)$, the local representation determines

$$
\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\!-\!ss}}
=(r_{v,\lambda},N_{v,\lambda}). \tag{7.1}
$$

Strict compatibility asks for one algebraic pair $D_v=(r_v,N_v)$ whose scalar extensions are all the pairs (7.1). The local comparison theorem supplies precisely such a pair when its geometric hypotheses are uniform in $\lambda$. The strata, their incidence maps, finite descent group, Hecke and type projectors, and normalized Frobenius correspondences are geometric and algebraic; changing $\lambda$ changes only the coefficient realization.

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

At a split strict semistable Steinberg place, let $\beta_v\in E^\times$ be the scalar of the normalized bad Hecke operator on the invariant graph line. Define $D_v=\operatorname{St}(\beta_v)$ on a basis $e_0,e_1$ by

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

**Proposition 7.1.** Under the verified strict semistable model, packet graph multiplicity one, extended normalized bad correspondence, and component-stability hypotheses, every $\lambda$ away from $v$ has local pair $\operatorname{St}(\beta_v)$. Under equivariant finite descent, the analogous assertion holds for $\operatorname{St}(\xi_v,\delta_v)$ when the type and kernel-Frobenius hypotheses are satisfied.

**Proof.** Nearby cycles give $N^2=0$ and identify the packet monodromy with the graph restriction--Gysin map. Graph multiplicity one makes its rank one. Strict semistability over $F_v$ makes finite inertia trivial, so rank-two special recognition gives $\operatorname{St}(\beta)$ for the eigenvalue $\beta$ on $\ker N$. The normalized bad correspondence identifies this eigenvalue with the algebraic scalar $\beta_v$, independently of $\lambda$. With finite descent, the finite inertia centralizing a nonzero rank-one nilpotent is scalar; the common type projector identifies it with $\xi_v$, and the Frobenius correspondence identifies the kernel scalar with $\delta_v$. $\square$

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

**Proposition 7.2.** If the finite descent complex, packet projector, type projector, monodromy-vanishing statement, and all Frobenius return maps are defined over $E$ and satisfy the local comparison hypotheses, then every local pair (7.1) is $D_v\otimes_EE_\lambda$. This includes the tame dihedral pair (7.8) when the quadratic cover and inducing character occur in the descent complex.

**Proof.** All differentials and projectors commute with coefficient extension. Hence the inertia decomposition and return maps on every $E_\lambda$-realization are scalar extensions of the common algebraic data. The finite-inertia reconstruction just described identifies the Weil representations. Monodromy vanishes on both sides. $\square$

### 7.4 Strict compatibility theorem

Let $S_{\mathrm{loc}}$ denote the finite places at which one of the verified local packages is needed; at places outside it the good package applies.

**Theorem 7.3 (strict compatibility in the geometric weight-two range).** Assume that for every finite place $v$ of $F$, one of the following uniform geometric packages is supplied:

1. the complete smooth proper good-place ledger;
2. the split strict semistable Steinberg ledger, including the normalized bad correspondence;
3. an equivariant finite semistable descent complex with matching type projector, monodromy statement, and Frobenius return maps;
4. the tame dihedral specialization of package 3.

Then the weakly compatible packet family is strictly compatible in the sense of Definition 3.2. The common $D_v$ is respectively unramified, special, finite type, or tame dihedral as described above.

**Proof.** At a good place the smooth proper comparison and (4.6) give (7.4) for every $\lambda$ away from $v$. Proposition 7.1 treats the two special cases. Proposition 7.2 treats finite and tame dihedral types. These identifications are made from the same algebraic model, correspondences, type data, and Frobenius return maps, so they hold for every allowed coefficient place. This is exactly (3.6). $\square$

The theorem is deliberately conditional at a place not covered by one of the four packages. A common good polynomial at almost all places does not manufacture a missing local model at the remaining place.

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

For $\operatorname{St}(\xi_v,\delta_v)$, finite inertia does not alter weights. The pair is pure of weight one precisely when $\delta_v$ is a $q_v$-Weil number of weight zero. In the weight-two geometric range the kernel line is an algebraic finite-character line, so this holds. If an arbitrary unramified scalar were allowed, purity would need to be imposed rather than inferred from $N\ne0$.

### 8.3 Finite-monodromy parameters

Suppose $N=0$ and inertia has finite image. Purity of weight one means that every eigenvalue of $r(\Phi_v)$, after taking a suitable Frobenius power preserving an inertia-isotypic component, has the absolute value dictated by residue degree and weight one.

For the finite types arising from the weight-two packet, this is a local algebraicity condition on the Frobenius return maps. The geometric local comparison identifies those maps with the automorphic ones. Their weight-one normalization is fixed globally by the determinant and by the cohomological normalization of the packet.

For a dihedral parameter

$$
D_v=\operatorname{Ind}_{W_L}^{W_K}\theta_v, \tag{8.6}
$$

purity can be checked over $L$. If $f=[k_L:k_K]$ and $\Phi_L$ is geometric Frobenius over $L$, then $D_v$ is pure of weight one exactly when

$$
|\iota(\theta_v(\Phi_L))|=q_v^{f/2} \tag{8.7}
$$

for every complex embedding. Indeed, after restricting to $W_L$, the two characters are $\theta_v$ and $\theta_v^\sigma$; induction only permutes their Frobenius conjugates. In the verified tame dihedral weight-two package, (8.7) is part of the algebraic normalization of the inducing character.

Finite inertia by itself does not prove (8.7). An unramified twist can change the absolute values without changing inertia or conductor.

### 8.4 Local purity of the system

**Theorem 8.2 (purity at every verified place).** The strictly compatible packet system is pure of weight one at every good place. At a bad place it is Weil--Deligne pure of weight one in the following cases:

1. special type with finite-order kernel scalar;
2. ramified special type with finite-order kernel scalar after removal of its stated finite inertia character;
3. finite type whose common Frobenius return maps satisfy the weight-one algebraic normalization;
4. tame dihedral type satisfying (8.7).

The conclusion is independent of $\lambda$.

**Proof.** Good-place purity is Theorem 6.2. Sections 8.2 and 8.3 verify the monodromy-graded weights of every listed common pair $D_v$. Since $\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\!-\!ss}}=D_v\otimes E_\lambda$, the eigenvalues are the same algebraic numbers viewed in different completions. Their complex absolute values therefore do not depend on $\lambda$. $\square$

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

The Swan conductor is computed from the upper ramification filtration of the finite inertial image. If the image factors through a finite quotient $J$, then

$$
\operatorname{Sw}(r)
=\sum_{u>0}
\frac{|J^u|}{|J^0|}
\operatorname{codim}V^{J^u}, \tag{9.5}
$$

with the standard interpretation as a finite sum over jumps. Thus it depends on the filtered inertia representation, not merely on its abstract character.

### 9.2 Independence of the coefficient place

**Theorem 9.1 (conductor independence).** Let $\{\rho_\lambda\}$ be strictly compatible with common local pair $D_v$ at a finite place $v$. Then for every $\lambda$ with $v\nmid\ell(\lambda)$,

$$
a_v(\rho_\lambda)=a(D_v),
\qquad
\operatorname{Sw}_v(\rho_\lambda)=\operatorname{Sw}(r_v). \tag{9.6}
$$

In particular these integers are independent of $\lambda$.

**Proof strategy.** Strict compatibility identifies more than the numerical invariants: it identifies the entire pair after scalar extension. Dimensions of invariants, kernels, and ramification-fixed spaces are unchanged by extending a characteristic-zero field.

**Proof.** By (3.6), the local pair of $\rho_\lambda$ is $D_v\otimes_EE_\lambda$. Field extension preserves the ranks of $N$, $(\ker N)^{I_v}$, and $V^{J^u}$ for every ramification subgroup in the finite inertial quotient. Therefore (9.3) and (9.5) have the same value for every $\lambda$. $\square$

The qualification $v\nmid\ell(\lambda)$ cannot be omitted. At the coefficient residue characteristic, an Artin conductor may still be defined for the Galois representation, but the comparison with the prime-to-residue-characteristic Weil--Deligne construction used here requires additional theory.

There is also a converse warning. Equality of conductors for every $\lambda$ does not imply strict compatibility. Formulas (9.1)--(9.3) compress the local pair too severely.

### 9.3 Euler and epsilon factors

Because the common local pair is defined over $E$, formula (9.4) gives

$$
P_v^{\mathrm{loc}}(T)\in E[T] \tag{9.7}
$$

whose image in $E_\lambda[T]$ is the Euler polynomial of $\rho_\lambda$ for every allowed $\lambda$. Thus strict compatibility supplies coefficient-place independence of local Euler factors at bad places as well as good ones.

For epsilon factors, fix once and for all a nontrivial additive character $\psi_v:F_v\to\mathbf C^\times$ of specified conductor and the self-dual Haar measure. The epsilon factor of a Weil--Deligne pair depends on the finite Weil representation, $N$, $\psi_v$, and the measure. Equality of the pairs gives equality of epsilon factors after applying the chosen coefficient embedding.

**Proposition 9.2.** In every strictly compatible local case, the Euler polynomial, conductor, Swan conductor, monodromy rank, and epsilon factor with fixed auxiliary normalizations are independent of $\lambda$.

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

**Ramified special type.** For $\operatorname{St}(\xi_v,\delta_v)$, if $\xi_v$ is nontrivial on inertia, then $(\ker N)^{I_v}=0$, so the Euler polynomial is $1$. Its conductor contains the conductor of the scalar finite character on two dimensions together with the monodromy correction in (9.1).

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
4. the local pair becomes $D_v^\sigma$;
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

Two curve realizations of the same full packet data can produce the same rank-two object because their multiplicity constructions are identified by the packet correspondences and the common adjoint pairing. If an actual descended correspondence identifies their multiplicity objects, this gives an isomorphism of the global representations without any density argument.

Without such a correspondence, equality of all good Frobenius polynomials establishes equality of their weak compatibility data but is not, within the present dependency range, used to manufacture a canonical global intertwiner. The compatible system is an isomorphism class of each independently constructed placewise representation together with its common local data; it is not a chosen web of cross-carrier maps.

**Proposition 10.3 (carrier independence at the level proved).** A change of curve carrier which is related by a descended multiplicity identification leaves the rank-two system unchanged up to isomorphism. If only common Hecke polynomials and local parameters are known, the two constructions define the same compatible-system data; no canonical comparison of their ambient cohomology or integral lattices is asserted.

This formulation avoids importing a global density theorem not required for constructing the family.

### 10.4 The exact meaning of independence

It is useful to summarize what has become choice-free.

- The Hecke field $E_0$, good polynomials, finite character $\eta$, weights, and common local isomorphism classes are intrinsic to the isolated packet.
- A field of realization $E$ is auxiliary, but enlarging it only extends scalars.
- The representation at a place $\lambda$ is independent of bases, matrix coordinates, and splitting modules up to isomorphism.
- A perfect polarization pairing is unique only up to scalar, while its multiplier and determinant are intrinsic.
- A rational geometric carrier is interchangeable only when the required descended comparison data exist.
- Integral lattices remain dependent on their ambient integral realization until a stronger integral theorem identifies them.

These distinctions prevent the word “canonical” from carrying more content than the construction proves.

## 11. Integral lattices and their limits

### 11.1 Existence of stable lattices

For every $\lambda$, continuity of $\rho_\lambda$ and compactness of $G_F$ give a stable $\mathcal O_\lambda$-lattice. Start with any lattice $M$. The compact image moves $M$ through finitely many lattices; their sum is full and stable.

Such a lattice proves that traces and determinants of all Galois elements are integral at $\lambda$. It is not canonical. Distinct stable lattices are commensurable, but their reductions can be nonsplit extensions in opposite directions.

**Lemma 11.1 (residual semisimplification).** If $L$ and $L'$ are two stable full lattices in the same semisimple $E_\lambda$-representation, then the semisimplifications of $L/\mathfrak m_\lambda L$ and $L'/\mathfrak m_\lambda L'$ have the same Jordan--Holder factors.

**Proof.** After scaling, arrange $L'\subseteq L$ with finite quotient. Filter $L/L'$ by powers of a uniformizer. Comparing the two reduction sequences and repeatedly using additivity of Jordan--Holder factors shows that the residual semisimplifications agree. $\square$

Thus a residual semisimplification is attached to the rational local representation, but a particular residual extension is not.

### 11.2 Saturated cohomological lattices

The geometric construction supplies a more natural lattice. Let $\Lambda_\lambda$ be the finite-free integral $H^1$ of the smooth proper curve and let $V_{\Pi,\lambda}$ be the rational packet block. Define

$$
\Lambda_{\Pi,\lambda}
=\Lambda_\lambda\cap V_{\Pi,\lambda}. \tag{11.1}
$$

It is Galois and Hecke stable and is saturated in $\Lambda_\lambda$. Indeed, if $0\ne a\in\mathcal O_\lambda$, $x\in\Lambda_\lambda$, and $ax$ lies in the rational subspace $V_{\Pi,\lambda}$, then $x=a^{-1}(ax)$ lies in that subspace too.

To extract an integral rank-two multiplicity lattice, choose an order $\mathcal A_\lambda$ in the split Hecke algebra and an $\mathcal A_\lambda$-stable lattice $\mathcal P_\lambda$ in the simple module. The candidate

$$
\mathcal W_\lambda
=\operatorname{Hom}_{\mathcal A_\lambda}
(\mathcal P_\lambda,\Lambda_{\Pi,\lambda}) \tag{11.2}
$$

spans the rational Hom factor after saturation. Integral evaluation is an isomorphism only if the order is Morita-split, $\mathcal P_\lambda$ is projective over it, and no index defect remains.

The rational compatible-system theorem does not imply these hypotheses. It guarantees a stable lattice, not a canonical integral tensor decomposition.

### 11.3 Congruence and projector denominators

Let $e_\Pi$ be the rational packet idempotent. It can fail to preserve $\Lambda_\lambda$ when its interpolation denominator is divisible by $\lambda$. For example, if two eigenvalues $a$ and $b$ are distinct in $E$ but congruent modulo $\lambda$, the formal projector

$$
e_a=\frac{T-b}{a-b} \tag{11.3}
$$

has a nonunit denominator. The two rational branches are separate, while their integral reductions meet.

There are several independent sources of denominators:

1. rational packet projectors;
2. descent from a fine level through a finite stabilizer group;
3. discriminants of integral Hecke orders;
4. type projectors containing the reciprocal of a finite group order;
5. nonprimitive restriction or Gysin images.

Inverting one denominator does not remove the others. Saturated intersection remains valid in their presence, but a direct summand or self-dual lattice does not.

### 11.4 What rational compatibility does not provide

The family $\{\rho_\lambda\}$ has common rational Frobenius and Weil--Deligne data. From this one may conclude:

- algebraic-integral good Frobenius polynomials;
- existence of a stable lattice at each $\lambda$;
- independence of residual semisimplification from the chosen stable lattice;
- common rational determinant and conductor away from coefficient residue characteristic.

One may not conclude:

- a single lattice living simultaneously over every $\mathcal O_\lambda$;
- freeness of the saturated packet lattice as a module over a global number ring;
- integral direct-summand projectors at congruence primes;
- perfectness of the alternating pairing on a chosen lattice;
- independence of residual extension classes;
- finite-flatness of coefficient-prime quotients.

Those assertions require a separate integral construction. Keeping this boundary visible is essential: rational strict compatibility is insensitive to the index of one lattice inside another.

## 13. The complete compatible-system theorem

### 13.1 Statement

We now collect the construction in the exact form available for the weight-two packets used in the arithmetic applications.

**Theorem 13.1 (compatible coefficient systems and purity).** Let $F$ be a number field and let $\Pi$ be a noncharacter parallel-weight-two packet with the following data.

1. The packet occurs in a finite algebraic Hecke module, has Hecke field

   $$
   E_0=\mathbf Q(t_v,s_v,\text{ central and component values}),
   $$

   and all its coefficient conjugates occur with the stated isolating data.
2. It has a compact Shimura-curve cohomological realization whose full finite Hecke block admits multiplicity extraction of rank two.
3. The adjoint packet and component descent give the perfect alternating multiplicity pairing with finite character $\eta$.
4. A finite extension $E/E_0$ splits the simple Hecke factors and contains the finitely many local types.

Then for every finite place $\lambda$ of $E$ there is a continuous semisimple representation

$$
\rho_{\Pi,\lambda}:G_F\longrightarrow
\operatorname{GL}_2(E_\lambda) \tag{13.1}
$$

with the following properties.

**Weak compatibility.** There is a finite set $S$, independent of $\lambda$, such that for $v\notin S$ and $v\nmid\ell(\lambda)$ the representation is unramified and

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_v))
=X^2-t_vX+q_vs_v. \tag{13.2}
$$

**Determinant and duality.** For every $\lambda$,

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_\lambda,
\qquad
\rho_{\Pi,\lambda}^\vee
\simeq\rho_{\Pi,\lambda}(1)\otimes\eta_\lambda^{-1}. \tag{13.3}
$$

These identities are independent of the scalar normalization of the polarization.

**Purity.** The system is pure of weight one: every root of (13.2) has absolute value $q_v^{1/2}$ under every complex embedding. At a verified bad place, its common Weil--Deligne pair is pure of weight one under the local normalization hypotheses of Theorem 8.2.

**Strict compatibility.** Let $v$ be a finite place and suppose the local geometry supplies one of the uniform packages in Theorem 7.3. For every $\lambda$ with $v\nmid\ell(\lambda)$,

$$
\operatorname{WD}_v(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq D_v\otimes_EE_\lambda, \tag{13.4}
$$

where $D_v$ is the algebraic unramified, special, finite-type, or tame dihedral parameter prescribed by the packet. If such a package is supplied at every finite $v$, the family is strictly compatible at every finite place away from the varying coefficient residue characteristic.

**Local invariants.** In the range of (13.4), the local Euler polynomial, Artin and Swan conductor, monodromy rank, and epsilon factor with fixed additive character and self-dual measure are independent of $\lambda$. The global prime-to-$\lambda$ conductor ideal

$$
\mathfrak N(\rho_\lambda)
=\prod_{v\nmid\ell(\lambda)}
\mathfrak p_v^{a(D_v)} \tag{13.5}
$$

is obtained by omitting only the factors above $\ell(\lambda)$ from one common conductor datum.

**Coefficient and choice independence.** The construction commutes with coefficient embeddings and finite coefficient extension. It is independent, up to isomorphism, of bases, matrix splittings, simple-module coordinates, and polarization scaling. A change of curve carrier preserves the system when accompanied by the descended multiplicity identification stated in Chapter 10.

**Integral structures.** Each $\rho_{\Pi,\lambda}$ has a stable lattice, and its geometric realization supplies a saturated packet lattice. No canonical integral rank-two direct summand, self-dual lattice, cross-$\lambda$ lattice, or finite-flat coefficient-prime quotient is asserted by this theorem.

### 13.2 Proof

The finite algebraic Hecke module gives $E_0$, integrality of $t_v$ and $s_v$, and the occurrence of every coefficient conjugate. A finite splitting extension $E$ exists by Proposition 2.1. At each $\lambda$, multiplicity extraction from curve $H^1$ gives the rank-two Hom space (4.1). Closedness of the Hom equations proves continuity, and Jordan--Holder gives the canonical semisimplification. This constructs (13.1).

Choose $S$ to contain all places excluded by the packet, level, component, integral-model, and correspondence hypotheses. At $v\notin S$ and away from the coefficient residue characteristic, smooth proper specialization gives unramifiedness. The common Hecke correspondence gives the quadratic annihilator (4.4). Factoring Poincare duality through the adjoint finite Hecke module gives (5.4), whose two-dimensional multiplier is the determinant. This proves (13.3) and evaluates the determinant at $\Phi_v$ as $q_vs_v$. Cayley--Hamilton then upgrades the annihilator to (13.2), including when Frobenius is scalar. Thus the family is weakly compatible.

The same special fiber is a smooth proper curve over a finite field. Weight-one purity of its $H^1$ passes through the correspondence summand and multiplicity factor, proving good-place purity. The alternating pairing confirms the normalization.

At a bad place, the local comparison theorem computes the packet part of the equivariant nearby-cycle complex. For split strict semistability it identifies nonzero graph monodromy and the bad-correspondence scalar, giving $\operatorname{St}(\beta_v)$. Finite descent supplies a common inertia representation and Frobenius return maps. In the tame dihedral case these data are the quadratic extension and inducing character. All are defined algebraically over $E$ and commute with scalar extension, so Propositions 7.1 and 7.2 give (13.4).

The monodromy filtrations in Chapter 8 prove local weight-one purity under the listed normalization hypotheses. The formulas of Chapter 9 read Euler factors, conductors, Swan terms, monodromy ranks, and epsilon factors from the common $D_v$, proving their independence and (13.5).

Propositions 2.3, 2.4, 10.2, and Theorem 10.1 prove the coefficient and auxiliary-choice assertions. The rank-two determinant identity shows that scaling a perfect alternating pairing cannot alter its multiplier. Finally, compactness gives some stable lattice and intersection with integral cohomology gives a saturated one. Sections 11.2--11.4 explain why none of the stronger integral conclusions follows without further hypotheses. $\square$

**Corollary 13.2 (the packet range used in the Fermat argument).** Suppose every finite place of $F$ is either good for the packet or is one of the verified Steinberg, finite-descent, or tame dihedral places, and suppose the corresponding component, type, return-map, and local weight normalization hypotheses have been established by the chosen curve carrier. Then (13.4) holds at every finite $v\nmid\ell(\lambda)$. Thus the packet gives a strictly compatible pure rank-two system at every place in this range, with coefficient-independent conductor and local factor.

**Proof.** Every finite place belongs to one of the four alternatives in Theorem 7.3. Apply that theorem place by place. Purity and independence of local invariants then follow from Theorems 8.2 and 9.1 and Proposition 9.2. $\square$

### 13.3 Variants and edge cases

Several boundary cases fit the theorem without changing its statement.

**Scalar good Frobenius.** The polynomial in (13.2) may have a repeated root. The determinant argument proves that it is still the characteristic polynomial, and purity fixes the modulus of the repeated root.

**Reducible semisimple systems.** The extraction theorem does not require absolute irreducibility for its determinant or good-polynomial conclusions. If

$$
\rho_\lambda=\chi_{1,\lambda}\oplus\chi_{2,\lambda},
$$

then trace and determinant record the unordered pair of characters at good places. The alternating pairing forces their product to be $\chi_\lambda^{-1}\eta_\lambda$. No extension class is claimed.

**Several places above one rational prime.** If $\lambda_1$ and $\lambda_2$ lie above the same $\ell$, they are separate members of the family. Their completions may have different ramification indices and residue degrees. Compatibility compares them through the same $E$-polynomials; it does not identify their underlying $\mathbf Q_\ell$-spaces.

**Residue extensions.** If a geometric place $u$ lies over the automorphic place $v$ with residue degree $f$, the common local pair is restricted from $W_{F_v}$ to $W_{F_u}$. Frobenius becomes $\Phi_v^f$ and the roots become $\alpha_v^f,\beta_v^f$. Every weight and conductor assertion must use the actual local extension.

**The coefficient residue characteristic.** For a fixed $\lambda$, equations (13.2) and (13.4) deliberately omit $v\mid\ell(\lambda)$. Continuity of $\rho_\lambda$ remains true there, but crystalline, semistable, de Rham, Hodge--Tate, and finite-flat assertions require additional hypotheses and are outside this theorem.

**Wild finite descent.** The finite-type clause includes wild inertia only when the entire finite descent action and its ramification filtration are supplied. A tame chart cannot determine a Swan conductor. When the wild filtered action is supplied algebraically over $E$, the proof of Theorem 9.1 applies unchanged.

**Nonminimal and old level.** Oldvectors enlarge $P_{\Pi,\lambda}$, not the rank of $W_{\Pi,\lambda}$. The full finite Hecke image is needed so that Morita extraction removes the whole level module. A sparse collection of spherical operators can leave an artificially large multiplicity space.

### 13.4 Dependency and hypothesis ledger

The proof uses exactly four prior mathematical packages.

| Conclusion in this book | Established source | Hypotheses retained here | Boundary |
|---|---|---|---|
| Weil-number calculus and purity of curve $H^1$ | the low-dimensional weight and Weil-bound theory | smooth proper curve over a finite field; geometric Frobenius | reciprocal roots alone do not prove purity |
| Hecke field and coefficient conjugates | algebraicity and integral structures of weight-two packets | finite integral Hecke module, reduced generic image, raw $T_v,S_v$ normalization | a quaternionic good block needs isolating data to name one constituent |
| saturated eigenlattices | the same packet theory | intersection with a fixed ambient integral module | rational projectors need not be integral |
| rank-two representations | extraction from weight-two Shimura cohomology | full finite Hecke block, splitting field, curve multiplicity two | oldspace dimension is not Galois rank |
| determinant and good polynomial | the same extraction theory | adjoint packet, component character, perfect pairing, full good-model ledger | a quadratic relation alone may only annihilate Frobenius |
| bad local parameters | local--global compatibility for weight-two representations | $v\nmid\ell$, verified semistable model, extending correspondences, type and return data | conductor or inertia alone does not identify a parameter |

No theorem about later canonical lattices or finite-flat quotients is used. No global comparison of two unrelated carriers is inferred from a numerical coincidence. The common system is built directly from the packet at every coefficient place, and bad-place compatibility is proved directly from the corresponding local geometric package.

## 14. The arithmetic package

### 14.1 A worked synthesis

Consider first a packet with trivial central-component character, so $s_v=1$ at every good place and

$$
\det\rho_\lambda=\chi_\lambda^{-1}. \tag{14.1}
$$

At a good place $v\nmid\ell(\lambda)$,

$$
P_v(X)=X^2-t_vX+q_v, \tag{14.2}
$$

and every conjugate of each root has modulus $q_v^{1/2}$. Hence every conjugate of $t_v$ lies in the interval allowed by

$$
|t_v|\le2q_v^{1/2}. \tag{14.3}
$$

At a split multiplicative place, the common pair is $\operatorname{St}(\beta_v)$ with $\beta_v=1$ or $-1$. It has

$$
N\ne0,\qquad a_v=1,\qquad
P_v^{\mathrm{loc}}(T)=1-\beta_vT. \tag{14.4}
$$

The sign distinguishes split from nonsplit multiplicative behavior while inertia and conductor remain the same. Its monodromy-graded Frobenius eigenvalues have weights zero and two, making the pair pure of center weight one.

At an irreducible tame dihedral place with no inertia invariants,

$$
D_v=\operatorname{Ind}_{W_L}^{W_{F_v}}\theta_v,
\qquad N=0, \tag{14.5}
$$

the local Euler polynomial is $1$ and the basic tame conductor is two. Nevertheless the inducing Frobenius value remains essential: changing it by an unramified scalar preserves both the Euler polynomial and conductor while changing the Weil representation. Strict compatibility retains that scalar.

For every coefficient place away from $v$, these three calculations are scalar realizations of the same algebraic data. This is the practical force of the system: one can change the coefficient prime without changing Frobenius polynomials, local type, monodromy, conductor, or purity.

### 14.2 A normalization audit

The following checks should accompany every use of the theorem.

1. $\Phi_v$ is geometric Frobenius and acts on $E_\lambda(1)$ by $q_v^{-1}$.
2. The good characteristic polynomial is $X^2-t_vX+q_vs_v$; the Euler denominator is $1-t_vT+q_vs_vT^2$.
3. Arithmetic Frobenius has reciprocal roots and polynomial (5.9).
4. The determinant is $\chi_\lambda^{-1}\eta_\lambda$, not $\chi_\lambda\eta_\lambda$.
5. Purity of weight one means modulus $q_v^{1/2}$ at good places and monodromy-graded weights at bad places.
6. A special parameter has Frobenius eigenvalues $\beta_v$ and $q_v\beta_v$, with $N$ mapping the second line to the first.
7. Strict compatibility is asserted only for $v\nmid\ell(\lambda)$.
8. Inertial type plus conductor does not determine Frobenius return maps or monodromy.
9. Coefficient conjugation acts on $t_v$, $s_v$, $\eta$, and every local type value together.
10. A rational compatible system supplies stable lattices but not canonical integral direct summands.
11. A residue-degree change raises Frobenius roots to the corresponding power.

These tests catch the most common sign, twist, and scope errors before they enter a global argument.

### 14.3 What has and has not been proved

The construction gives one coherent arithmetic family. Its good Frobenius polynomials live in the Hecke field and survive every coefficient completion. Its determinant is fixed globally. Its roots have the expected absolute values. At every place covered by the geometric local comparison, the complete Frobenius-semisimple Weil--Deligne pair is independent of the coefficient place. Conductors and local factors follow from that stronger statement.

Several nearby assertions remain logically separate. The theorem does not compare nonsemisimple global extension classes. It does not assert a local Weil--Deligne comparison at the coefficient residue characteristic. It does not construct a globally canonical lattice, prove integral self-duality at denominator primes, or produce finite-flat quotients. It does not identify a quaternionic constituent from good eigenvalues unless the requisite isolating data are already present.

These limits do not weaken the compatible-system theorem. They specify exactly which information is rational, which is local, and which is integral.

### 14.4 Conclusion

A weight-two packet now determines more than one representation for each chosen prime. Its algebraic conjugates assemble into a single compatible coefficient system. The common field records the raw Hecke polynomials, the finite component character, and the bad local types. Completion at $\lambda$ realizes those data on a continuous two-dimensional space, while changing $\lambda$ changes only the scalar topology.

The determinant and pairing organize the family globally:

$$
\det\rho_{\Pi,\lambda}=\chi_\lambda^{-1}\eta_\lambda,
$$

and the good Frobenius polynomial is

$$
X^2-t_vX+q_vs_v.
$$

Smooth proper geometry gives weight one, including every complex conjugate of every root. Nearby-cycle geometry supplies the finer bad-place package: finite inertia, nilpotent monodromy, and Frobenius return maps. Because that package is algebraic before a coefficient place is chosen, its Euler factor, conductor, Swan term, monodromy rank, and local constant are coefficient independent.

The theory also draws its own boundary sharply. Rational compatibility does not canonically synchronize integral lattices. At the coefficient residue characteristic, additional comparison conditions are required. Within these boundaries, however, the result is genuinely uniform: coefficient embeddings, polarization scalars, splitting fields, and verified curve carriers alter presentations but not the compatible arithmetic data.
