# Compatible Systems of Galois Representations

## Contents

1. [From one representation to an arithmetic family](#1-from-one-representation-to-an-arithmetic-family)
   - [Why one coefficient prime is not enough](#11-why-one-coefficient-prime-is-not-enough)
   - [The three levels of compatibility](#12-the-three-levels-of-compatibility)
   - [Standing conventions](#13-standing-conventions)
   - [The prerequisite boundary](#14-the-prerequisite-boundary)
2. [The two number fields and their places](#2-the-two-number-fields-and-their-places)
   - [Base field versus coefficient field](#21-base-field-versus-coefficient-field)
   - [Finite coefficient places](#22-finite-coefficient-places)
   - [Embeddings and comparison maps](#23-embeddings-and-comparison-maps)
   - [Fields of rationality and fields of definition](#24-fields-of-rationality-and-fields-of-definition)
3. [Weak compatible systems](#3-weak-compatible-systems)
   - [The definition](#31-the-definition)
   - [Determinants and compatible characters](#32-determinants-and-compatible-characters)
   - [Equivalence, enlargement, and semisimplification](#33-equivalence-enlargement-and-semisimplification)
   - [Chebotarev uniqueness](#34-chebotarev-uniqueness)
   - [What weak compatibility does not say](#35-what-weak-compatibility-does-not-say)
4. [Weil--Deligne parameters and strong compatibility](#4-weil--deligne-parameters-and-strong-compatibility)
   - [From quasi-unipotent inertia to a parameter](#41-from-quasi-unipotent-inertia-to-a-parameter)
   - [Frobenius-semisimplification and monodromy](#42-frobenius-semisimplification-and-monodromy)
   - [Inertial type and conductor](#43-inertial-type-and-conductor)
   - [Strict and strong systems](#44-strict-and-strong-systems)
   - [Principal series and Steinberg parameters](#45-principal-series-and-steinberg-parameters)
5. [Places above the coefficient prime](#5-places-above-the-coefficient-prime)
   - [Labelled Hodge--Tate weights](#51-labelled-hodge--tate-weights)
   - [De Rham, crystalline, and semistable representations](#52-de-rham-crystalline-and-semistable-representations)
   - [Hodge compatibility as the coefficient place varies](#53-hodge-compatibility-as-the-coefficient-place-varies)
   - [The coefficient-prime boundary](#54-the-coefficient-prime-boundary)
6. [Purity, parity, and polarization](#6-purity-parity-and-polarization)
   - [Purity and weights](#61-purity-and-weights)
   - [Complex conjugation and oddness](#62-complex-conjugation-and-oddness)
   - [Polarizations and essential self-duality](#63-polarizations-and-essential-self-duality)
   - [A coefficient-rational symmetry package](#64-a-coefficient-rational-symmetry-package)
7. [Integral lattices and residual members](#7-integral-lattices-and-residual-members)
   - [Stable lattices](#71-stable-lattices)
   - [Reduction and lattice independence](#72-reduction-and-lattice-independence)
   - [Residual determinants and ramification](#73-residual-determinants-and-ramification)
   - [Residual systems are a separate layer](#74-residual-systems-are-a-separate-layer)
   - [Two lattices with different reductions](#75-two-lattices-with-different-reductions)
8. [Algebraic operations on systems](#8-algebraic-operations-on-systems)
   - [Coefficient extension and coefficient restriction](#81-coefficient-extension-and-coefficient-restriction)
   - [Twists and Tate twists](#82-twists-and-tate-twists)
   - [Duals, sums, tensors, and symmetric powers](#83-duals-sums-tensors-and-symmetric-powers)
   - [Local data under tensor operations](#84-local-data-under-tensor-operations)
9. [Changing the base field and inducing](#9-changing-the-base-field-and-inducing)
   - [Restriction to a finite extension](#91-restriction-to-a-finite-extension)
   - [Good-prime polynomials after restriction](#92-good-prime-polynomials-after-restriction)
   - [Galois induction and its local polynomial](#93-galois-induction-and-its-local-polynomial)
   - [Automorphic induction and the dimension warning](#94-automorphic-induction-and-the-dimension-warning)
10. [The automorphic construction](#10-the-automorphic-construction)
    - [Regular algebraic cuspidal input](#101-regular-algebraic-cuspidal-input)
    - [One common polynomial at every good place](#102-one-common-polynomial-at-every-good-place)
    - [The weak automorphic system](#103-the-weak-automorphic-system)
    - [Hodge weights, determinant, and purity](#104-hodge-weights-determinant-and-purity)
    - [The strong automorphic system](#105-the-strong-automorphic-system)
11. [Local automorphic types in the system](#11-local-automorphic-types-in-the-system)
    - [Unramified and principal-series places](#111-unramified-and-principal-series-places)
    - [Steinberg places](#112-steinberg-places)
    - [Supercuspidal places and the comparison boundary](#113-supercuspidal-places-and-the-comparison-boundary)
    - [Central characters and reciprocity audit](#114-central-characters-and-reciprocity-audit)
12. [Systems from elliptic curves and abelian varieties](#12-systems-from-elliptic-curves-and-abelian-varieties)
    - [The elliptic-curve system](#121-the-elliptic-curve-system)
    - [A worked elliptic-curve diagnostic](#122-a-worked-elliptic-curve-diagnostic)
    - [Abelian varieties and coefficient factors](#123-abelian-varieties-and-coefficient-factors)
    - [Comparison with an automorphic system](#124-comparison-with-an-automorphic-system)
13. [Conditional potential automorphy and the downstream boundary](#13-conditional-potential-automorphy-and-the-downstream-boundary)
    - [What potential automorphy actually gives](#131-what-potential-automorphy-actually-gives)
    - [Why this does not descend the family](#132-why-this-does-not-descend-the-family)
    - [Downstream producers](#133-downstream-producers)
14. [Coefficient descent and conjugate systems](#14-coefficient-descent-and-conjugate-systems)
    - [Trace fields and enlargement](#141-trace-fields-and-enlargement)
    - [Galois conjugates](#142-galois-conjugates)
    - [Descent of coefficients](#143-descent-of-coefficients)
    - [Inner twists and the true rationality field](#144-inner-twists-and-the-true-rationality-field)
15. [What is genuinely independent of the coefficient prime](#15-what-is-genuinely-independent-of-the-coefficient-prime)
    - [Uniform invariants in a strong system](#151-uniform-invariants-in-a-strong-system)
    - [Conductor, type, and monodromy](#152-conductor-type-and-monodromy)
    - [Hodge data, determinant, and purity](#153-hodge-data-determinant-and-purity)
    - [Density-one and finite-exception conclusions](#154-density-one-and-finite-exception-conclusions)
16. [Residual image, adequacy, and the CM boundary](#16-residual-image-adequacy-and-the-cm-boundary)
    - [Why compatibility alone gives no large image](#161-why-compatibility-alone-gives-no-large-image)
    - [The finite-exception large-image wrapper](#162-the-finite-exception-large-image-wrapper)
    - [Adequacy outside a finite set](#163-adequacy-outside-a-finite-set)
    - [CM and dihedral systems](#164-cm-and-dihedral-systems)
    - [A worked CM diagnostic](#165-a-worked-cm-diagnostic)
17. [Solvable base change, descent, and self-twists](#17-solvable-base-change-descent-and-self-twists)
    - [Ascent of a compatible system](#171-ascent-of-a-compatible-system)
    - [Cuspidality and its first failure](#172-cuspidality-and-its-first-failure)
    - [Descent with a compatible arithmetic extension](#173-descent-with-a-compatible-arithmetic-extension)
    - [Automorphic induction in a solvable diagram](#174-automorphic-induction-in-a-solvable-diagram)
    - [Descent beyond solvable towers](#175-descent-beyond-solvable-towers)
18. [Changing the coefficient prime](#18-changing-the-coefficient-prime)
    - [What compatibility supplies](#181-what-compatibility-supplies)
    - [What Chebotarev adds](#182-what-chebotarev-adds)
    - [What a large-image theorem adds](#183-what-a-large-image-theorem-adds)
    - [Controlling local and residual behavior](#184-controlling-local-and-residual-behavior)
    - [The switching theorem](#185-the-switching-theorem)
19. [Hostile diagnostics](#19-hostile-diagnostics)
    - [Weak data with incompatible monodromy](#191-weak-data-with-incompatible-monodromy)
    - [A coefficient-embedding mismatch](#192-a-coefficient-embedding-mismatch)
    - [Residual collapse and coefficient-prime ramification](#193-residual-collapse-and-coefficient-prime-ramification)
    - [Restriction, induction, and self-twist failures](#194-restriction-induction-and-self-twist-failures)
    - [A Steinberg-place audit](#195-a-steinberg-place-audit)
20. [Scoped export and downstream handoff](#20-scoped-export-and-downstream-handoff)
    - [The generic ledger](#201-the-generic-ledger)
    - [The switching interface](#202-the-switching-interface)
    - [Descent is downstream](#203-descent-is-downstream)

## 1. From one representation to an arithmetic family

### 1.1 Why one coefficient prime is not enough

An individual $\ell$-adic representation is adapted to one prime. Its topology, its stable lattices, and its reduction all depend on $\ell$. Arithmetic objects, however, are rarely confined to one completion. An elliptic curve has a Tate module for every prime. A cohomological automorphic representation has Hecke eigenvalues in a number field, and every finite place of that number field gives a different adic realization. Potential modularity may identify a difficult representation at one prime with one realization of an automorphic form, after which an argument wants to move to a second prime where the residual image or local geometry is easier.

The bridge between these realizations is not a tensor product between fields of different residue characteristic. There is no meaningful expression such as

$$
V_\ell\otimes_{\mathbf Q_\ell}\mathbf Q_q
$$

when $q\ne\ell$. The bridge consists instead of algebraic data that exist before completion: characteristic polynomials of Frobenius, determinant characters, labelled Hodge data, and, when a local comparison theorem is available, Weil--Deligne parameters. Each completion reads the same algebraic record through a different embedding.

This is the idea of a compatible system. It is deliberately weaker than a single representation over one enormous topological field. The members do not share a topology or a common lattice. They share algebraic local invariants. That distinction is what makes changing the coefficient prime possible and also what prevents several common overclaims.

The theory has two goals. The first is organizational: it gives exact definitions of weak and strong compatibility and proves their basic functorial properties. The second is arithmetic: it assembles the representations constructed from automorphic forms into a family, records precisely what is independent of the coefficient prime, and isolates the extra hypotheses needed for residual irreducibility, adequacy, descent, and prime switching.

### 1.2 The three levels of compatibility

Three layers should be kept separate from the beginning.

At the **weak** layer, almost every base-field place $v$ has one polynomial $P_v(X)$ over a number field. Every member whose residue characteristic differs from that of $v$ is unramified there and has $P_v$ as its arithmetic-Frobenius polynomial. This layer determines semisimplified global members by Chebotarev.

At the **strong local** layer, every finite place $v$ away from the varying coefficient characteristic has one Weil--Deligne parameter. This records finite inertia, nilpotent monodromy, conductor, and the Frobenius action. It distinguishes a Steinberg representation from a semisimple sum with the same Frobenius eigenvalues. Weak compatibility does not imply this layer.

At the **coefficient-prime** layer, places $v$ whose residue characteristic equals the coefficient characteristic are described by $p$-adic Hodge theory. One asks for de Rham, crystalline, or semistable behavior and for Hodge--Tate weights indexed by embeddings of the base field. There is no unramified Frobenius class on the whole representation in general. Good reduction may make a representation crystalline while its cyclotomic determinant remains ramified.

The three layers meet in arithmetic examples, but no one of them formally creates the others. Common good-prime polynomials do not determine bad inertia. A Weil--Deligne parameter at $v\nmid\ell$ says nothing by itself about a place above $\ell$. Hodge--Tate weights do not determine an integral lattice. The definitions below retain these boundaries.

### 1.3 Standing conventions

Let $F$ be the **base number field** and put

$$
G_F=\operatorname{Gal}(\overline F/F).
$$

For a finite place $v$ of $F$, write $F_v$ for the completion, $k_v$ for its residue field, $q_v=|k_v|$, $D_v\subset G_F$ for a decomposition group, and $I_v\subset D_v$ for inertia. A choice of a place of $\overline F$ above $v$ identifies $D_v$ with $G_{F_v}$ up to conjugacy.

Arithmetic Frobenius is used throughout:

$$
\operatorname{Frob}_v:x\longmapsto x^{q_v}
$$

on residue fields. Thus, for $v\nmid\ell$,

$$
\chi_\ell(\operatorname{Frob}_v)=q_v, \tag{1.1}
$$

where $\chi_\ell$ is the $\ell$-adic cyclotomic character. The characteristic polynomial of an elliptic-curve Tate module at good reduction is therefore

$$
X^2-a_vX+q_v. \tag{1.2}
$$

Local reciprocity sends a uniformizer to arithmetic Frobenius. Consequently the adelic module character $|\cdot|$ corresponds to $\chi_\ell^{-1}$, while $|\cdot|^{-1}$ corresponds to $\chi_\ell$. Every later determinant and local-parameter formula is tested against (1.1)--(1.2).

We use covariant Tate modules. Our Hodge--Tate convention assigns weight $1$ to $\chi_\ell$. Thus an elliptic curve with good reduction has labelled Hodge--Tate multiset $\{0,1\}$. A Tate twist by $(r)$ adds $r$ to every Hodge--Tate weight and multiplies arithmetic-Frobenius eigenvalues away from $\ell$ by $q_v^r$.

All representations are continuous. A characteristic-zero member of a compatible system will normally be required to be semisimple. This is not a cosmetic choice: good Frobenius data determine only semisimplification. When a naturally occurring representation is not known to be semisimple, the system records its semisimplification unless extension data are separately retained.

### 1.4 The prerequisite boundary

This volume has three direct inputs, and only three:

$$
\boxed{179\mid 168,\ 141,\ 167.} \tag{1.3}
$$

Book 168 supplies the coefficient-indexed systems attached to already constructed
parallel-weight-two packets: common algebraic Frobenius polynomials, determinants, purity,
coefficient conjugation, and the full Frobenius-semisimple Weil--Deligne pair exactly in its
proved local range. Book 141 supplies the finite-subgroup classification and adequacy criteria
used by the large-image wrapper in Chapter 16. Book 167 supplies Chebotarev density and the
dense-Frobenius uniqueness step used throughout the compatibility calculus.

The arithmetic-Frobenius normalization is fixed here. If Book 168 writes geometric Frobenius
$\Phi_v$ and

$$
\det(X-\rho_\lambda(\Phi_v))=X^2-t_vX+q_vs_v,
\qquad \det\rho_\lambda=\chi_\lambda^{-1}\eta_\lambda,
$$

we use $\rho_\lambda^{\mathrm{arith}}=\rho_\lambda^\vee$ and
$\psi=\eta^{-1}$. Arithmetic Frobenius is $\Phi_v^{-1}$, so the displayed polynomial is
unchanged and

$$
\det\rho_\lambda^{\mathrm{arith}}=\chi_\lambda\psi_\lambda.
$$

Dualizing the local pair, including its monodromy operator, transports the verified local
compatibility without enlarging its range.

No descent theorem is an input here. Books 183--185 are downstream: they construct and verify a
particular elementary packet array, prove its effectivity, and assemble its members over the
base field. They may instantiate the definitions and switching interface developed here, but
none of their conclusions is used to prove anything in this volume. This direction avoids a
cycle and keeps the distinction between generic compatible-system calculus and one Brauer
application explicit.

Book 180 is likewise not a prerequisite. Its general integral Brauer, Clifford, effectivity,
and coefficient-descent toolkit is the reusable source for later descent applications; this
book does not reproduce that stack.

## 2. The two number fields and their places

### 2.1 Base field versus coefficient field

Compatible systems involve two number fields with entirely different jobs. Confusing them corrupts every local statement.

The base field $F$ is the field on which arithmetic lives. Its places are denoted $v,w$, its absolute Galois group acts, and its residue cardinalities $q_v$ occur in Frobenius polynomials. The coefficient field $E$ contains traces, determinants, Hecke eigenvalues, and the coefficients of common local parameters. Its finite places are denoted $\lambda$. A place $\lambda$ does not select a decomposition subgroup of $G_F$; it selects a topology on the scalars.

Thus the two localizations

$$
F\longrightarrow F_v,
\qquad
E\longrightarrow E_\lambda
$$

have different meanings. The first changes the Galois group from $G_F$ to $G_{F_v}$. The second leaves $G_F$ unchanged and changes the field in which its matrices live. If $v$ has residue characteristic $p$ and $\lambda$ has residue characteristic $\ell$, the local Weil--Deligne theory applies to $\rho_\lambda|_{G_{F_v}}$ when $p\ne\ell$. The coefficient-prime theory applies when $p=\ell$.

Accordingly, the shorthand $\lambda\nmid v$ or $v\nmid\lambda$ used below always means $\ell(\lambda)\ne\operatorname{char}(k_v)$. It does not assert divisibility between places of two different number fields.

This distinction is visible even over $\mathbf Q$. For an elliptic curve, $F=\mathbf Q$ and one may take $E=\mathbf Q$. The base prime $p$ indexes reduction of the curve; the coefficient prime $\ell$ indexes the Tate module. The assertion at a good pair is made for $p\ne\ell$. There is no symmetry interchanging $p$ and $\ell$.

### 2.2 Finite coefficient places

Let $E$ be a number field with ring of integers $\mathcal O_E$. A finite place $\lambda$ is equivalently a nonzero prime ideal $\mathfrak m_\lambda\subset\mathcal O_E$. Its residue characteristic is the rational prime

$$
\ell(\lambda)=\operatorname{char}(\mathcal O_E/\mathfrak m_\lambda).
$$

Write

$$
E_\lambda=\widehat E^{\,\lambda},\qquad
\mathcal O_\lambda=\mathcal O_{E_\lambda},\qquad
k_\lambda=\mathcal O_\lambda/\mathfrak m_\lambda\mathcal O_\lambda.
$$

Choose a uniformizer $\varpi_\lambda$ of $\mathcal O_\lambda$. The completion $E_\lambda$ is a finite extension of $\mathbf Q_\ell$, and $k_\lambda$ is a finite extension of $\mathbf F_\ell$. There can be several places of $E$ above the same rational prime. Their completions need not be canonically isomorphic.

The diagonal map $E\hookrightarrow E_\lambda$ lets one read a polynomial

$$
P_v(X)\in E[X]
$$

as a polynomial in $E_\lambda[X]$. This elementary map is the heart of weak compatibility. The polynomial itself is not recomputed for each $\lambda$; only its scalar interpretation changes.

One often enlarges $E$. If $E'/E$ is finite and $\lambda'\mid\lambda$, then $E_\lambda$ embeds in $E'_{\lambda'}$. A system over $E$ therefore produces one over $E'$ by scalar extension. The reverse direction is a descent problem. The fact that traces happen to lie in $E$ need not supply an $E_\lambda$-model of every representation without an additional field-of-definition argument.

### 2.3 Embeddings and comparison maps

A place is an equivalence class of absolute values; a comparison of algebraic and adic coefficients requires an embedding. Choose

$$
\iota_\lambda:\overline{\mathbf Q}\hookrightarrow
\overline{\mathbf Q}_\ell
$$

whose restriction to $E$ induces $\lambda$. It extends the map $E\to E_\lambda$ after choosing an embedding of $E_\lambda$ into $\overline{\mathbf Q}_\ell$.

At a good place, this means

$$
P_v(X)=X^2-a_vX+d_v
\quad\leadsto\quad
\iota_\lambda P_v(X)
=X^2-\iota_\lambda(a_v)X+\iota_\lambda(d_v). \tag{2.1}
$$

At a bad place, a Weil--Deligne parameter may first be defined over $\overline{\mathbf Q}$. Strong compatibility means that applying $\iota_\lambda$ to its matrix coefficients gives the parameter of the $\lambda$-adic member. Saying merely that the two parameters have coefficients in algebraic closures is incomplete: an embedding is needed to compare them.

The same issue is sharper for Hodge labels. An embedding

$$
\tau:F\hookrightarrow\overline{\mathbf Q}_\ell
$$

selects a place of $F$ above $\ell$. When algebraic weights are originally indexed by embeddings $\tau_0:F\hookrightarrow\overline{\mathbf Q}$, the comparison uses $\tau=\iota_\lambda\circ\tau_0$. Changing $\iota_\lambda$ can permute these labels. Independence of $\lambda$ means compatibility under this transport, not equality of two unlabelled lists written in unrelated orders.

### 2.4 Fields of rationality and fields of definition

Suppose a family has common traces $a_v$ and determinants $d_v$. The field

$$
E_{\mathrm{tr}}=\mathbf Q(a_v,d_v:v\text{ good}) \tag{2.2}
$$

is its trace-and-determinant field. For an automorphic representation, the analogous field is often called the Hecke field or field of rationality. It is canonical once the algebraic normalization is fixed.

A **field of definition** is stronger: it is a number field over which chosen models of all common algebraic data and all adic members can be made. A field of rationality fixes isomorphism classes under coefficient automorphisms; it need not by itself split every endomorphism algebra. A finite enlargement always preserves compatibility and is often harmless. Shrinking coefficients can encounter a Schur-index or descent obstruction.

There are consequently three honest ways to state coefficients.

1. Use the trace field and state separately that every member descends to its completion.
2. Enlarge once to a number field over which all required models and local types are defined.
3. Work with representations over finite extensions of the completions and regard the common trace data as the primary object.

The first two give ordinary compatible systems over a number field. The third gives a compatible collection after scalar extension, but should not be advertised as an $E_\lambda$-valued system until descent has been proved.

## 3. Weak compatible systems

### 3.1 The definition

The weak definition isolates exactly what almost all Frobenius elements can see. Let $E$ and $F$ be number fields, let $n\ge1$, and let $S$ be a finite set of finite places of $F$.

A **weakly compatible system of rank $n$ over $F$ with coefficients in $E$** consists of continuous semisimple representations

$$
\mathcal R=\{\rho_\lambda:G_F\longrightarrow
\operatorname{GL}_n(E_\lambda)\}_{\lambda}
$$

indexed by the finite places of $E$, together with monic polynomials

$$
P_v(X)\in E[X]
$$

for every finite $v\notin S$, such that whenever

$$
v\notin S,\qquad v\nmid\ell(\lambda),
$$

the representation $\rho_\lambda$ is unramified at $v$ and

$$
\det\bigl(X-\rho_\lambda(\operatorname{Frob}_v)\bigr)
=\iota_\lambda P_v(X). \tag{3.1}
$$

For a two-dimensional system we write

$$
P_v(X)=X^2-a_vX+d_v. \tag{3.2}
$$

The finite set $S$ is a common ramification set away from coefficient primes. Each individual member may also ramify at places above $\ell(\lambda)$. Thus the actual ramification set of $\rho_\lambda$ is contained in

$$
S\cup\{v:v\mid\ell(\lambda)\}. \tag{3.3}
$$

One may weaken (3.1) by allowing finitely many exceptional $\lambda$, or by indexing only a set $\Lambda$ of coefficient places. Such a family should be called an $E$-compatible system indexed by $\Lambda$, and the omitted places should be visible in the notation. The full definition above is the form needed for unrestricted prime switching.

Semisimplicity is included because the common polynomials cannot distinguish extensions. If a construction naturally gives a nonsemisimple $\rho_\lambda$, replacing it by $\rho_\lambda^{\mathrm{ss}}$ preserves (3.1). Retaining the original extension is additional structure, not part of weak compatibility.

### 3.2 Determinants and compatible characters

The constant terms $d_v$ form a rank-one shadow of the system. A **compatible character system** is a collection

$$
\{\delta_\lambda:G_F\to E_\lambda^\times\}_\lambda
$$

for which there is a finite set $S_\delta$ and elements $d_v\in E^\times$ satisfying

$$
\delta_\lambda(\operatorname{Frob}_v)=\iota_\lambda(d_v)
$$

whenever $v\notin S_\delta$ and $v\nmid\ell(\lambda)$. For a rank-two system, (3.1) implies that $\det\rho_\lambda$ has these values. Chebotarev then identifies it with any independently constructed compatible character having the same good values.

In arithmetic examples the determinant usually has the form

$$
\det\rho_\lambda=\psi_\lambda\chi_{\ell(\lambda)}^m, \tag{3.4}
$$

where $m\in\mathbf Z$ and $\psi$ is a finite-order algebraic Hecke character with $\lambda$-adic avatar $\psi_\lambda$. With arithmetic reciprocity,

$$
d_v=\psi(v)q_v^m. \tag{3.5}
$$

A twist test verifies the exponent. Tensoring a two-dimensional representation by a character $\eta_\lambda$ multiplies its trace once and its determinant twice:

$$
a_v\longmapsto\eta(v)a_v,
\qquad
d_v\longmapsto\eta(v)^2d_v. \tag{3.6}
$$

Any proposed formula that multiplies both coefficients by the same power has lost a dimension.

The determinant should be recorded as a character, not only through the numbers $d_v$. The character controls complex conjugation and coefficient-prime ramification, neither of which is represented by a good finite-place polynomial.

### 3.3 Equivalence, enlargement, and semisimplification

Two weak systems over the same $F$ and $E$ are **isomorphic** if their members are isomorphic for every $\lambda$ and their common polynomials agree outside a finite set. They are **weakly equivalent** if their common polynomials agree outside a finite set, even before memberwise isomorphisms are specified.

For semisimple systems these notions nearly coincide. Fix $\lambda$. Equality of the common polynomials at all but finitely many $v$ implies, by Chebotarev, that the two $\lambda$-adic members are isomorphic. Thus weak equivalence supplies memberwise isomorphism, although not a coherent choice of bases across $\lambda$.

Enlarging $S$ does not change the system. It merely forgets finitely many asserted unramified identities. Shrinking $S$ is a theorem: for every newly admitted $v$, one must prove unramifiedness for every $\lambda\nmid v$ and the common polynomial identity.

If the starting representations are not semisimple, equality of common polynomials defines equivalence only after semisimplification. For example, all extensions

$$
0\longrightarrow E_\lambda(\alpha)
\longrightarrow V_c
\longrightarrow E_\lambda(\beta)
\longrightarrow0 \tag{3.7}
$$

have the same characteristic-polynomial function as $E_\lambda(\alpha)\oplus E_\lambda(\beta)$. The class $c\in H^1(G_F,E_\lambda(\alpha\beta^{-1}))$ is invisible in (3.1).

### 3.4 Chebotarev uniqueness

The uniqueness theorem is the reason weak compatibility is useful.

**Theorem 3.1 (Chebotarev uniqueness).** Let $K$ be a characteristic-zero local field, and let

$$
r_1,r_2:G_F\longrightarrow\operatorname{GL}_n(K)
$$

be continuous representations unramified outside finite sets. If

$$
\det(X-r_1(\operatorname{Frob}_v))
=\det(X-r_2(\operatorname{Frob}_v)) \tag{3.8}
$$

for all but finitely many $v$, then

$$
r_1^{\mathrm{ss}}\simeq r_2^{\mathrm{ss}}. \tag{3.9}
$$

**Proof.** Equation (3.8) gives equality of traces on the indicated Frobenius conjugacy classes. Chebotarev says that these conjugacy classes are dense in $G_F$. Continuity extends trace equality to every $g\in G_F$. Over characteristic zero, the character of a finite-dimensional representation determines its semisimplification. Hence (3.9) follows. $\square$

The theorem compares representations over one common local field. If the two representations begin over completions of the same residue characteristic, they must first be embedded into one common algebraically closed adic field. This is precisely where the maps of Section 2.3 enter. Completions of different residue characteristics cannot be compared in this way: one applies Chebotarev separately at each coefficient characteristic after first identifying the algebraic polynomials, rather than applying the theorem directly to an $\ell$-adic and a $q$-adic representation.

Chebotarev does not identify a stable lattice. It does not recover the extension class in (3.7), a filtration at a coefficient-prime place, or a nonsemisimple Frobenius operator that has been replaced by its semisimple part. It is a powerful uniqueness theorem with a sharply defined output.

### 3.5 What weak compatibility does not say

It is tempting to infer every omitted local invariant from the density of good Frobenius elements. That inference is false. Density identifies the global semisimplified representation for one coefficient prime, but it does not calculate its restriction to inertia at an omitted place or exhibit that restriction through algebraic data independent of the coefficient prime.

There is an important logical distinction here. If two semisimple representations over the same local field have the same good polynomials, Theorem 3.1 makes them globally isomorphic, so their actual local restrictions are isomorphic as well. Weak compatibility nevertheless supplies no common algebraic formula for those restrictions as $\lambda$ varies. A local comparison theorem is needed to prove that the separately constructed restrictions arise from one embedding-aware parameter $D_v$. For nonsemisimple global representations, even the global extension class remains invisible.

Weak compatibility also gives no Hodge--Tate weights. It gives no purity unless bounds on the algebraic roots of $P_v$ have been proved. It gives no residual irreducibility: reducing an irreducible characteristic-zero member can be reducible at exceptional coefficient primes. It gives no canonical residual extension, because it gives no canonical lattice.

The correct implication chart is

$$
\begin{array}{c}
\text{common good Frobenius polynomials}
\\ \Downarrow
\\
\text{uniqueness of each semisimplified member}
\end{array}
$$

and not

$$
\text{good Frobenius data}
\Longrightarrow
\text{bad inertia, monodromy, Hodge filtration, and lattices}.
$$

The missing arrows are the substance of strong compatibility and geometric comparison.

## 4. Weil--Deligne parameters and strong compatibility

### 4.1 From quasi-unipotent inertia to a parameter

Fix a finite place $v$ of $F$ of residue characteristic $p$, and let $\lambda\nmid p$. A continuous $\lambda$-adic representation of $G_{F_v}$ has quasi-unipotent inertia in the arithmetic situations considered here: after restricting to an open subgroup of $I_v$, its action is unipotent. The finite part and the unipotent part should be separated. A Weil--Deligne parameter performs exactly that separation.

Let $W_{F_v}$ be the Weil group. Write $\nu:W_{F_v}\to\mathbf Z$ for the homomorphism sending arithmetic Frobenius to $1$, and put

$$
\|w\|_v=q_v^{\nu(w)}. \tag{4.1}
$$

This is the inverse of the usual local absolute value transported by arithmetic reciprocity. A Weil--Deligne representation over a characteristic-zero field $K$ is a pair $(r,N)$, where

$$
r:W_{F_v}\longrightarrow\operatorname{GL}(V)
$$

has open kernel on inertia, $N\in\operatorname{End}_K(V)$ is nilpotent, and

$$
r(w)Nr(w)^{-1}=\|w\|_vN. \tag{4.2}
$$

In particular,

$$
r(\operatorname{Frob}_v)N
r(\operatorname{Frob}_v)^{-1}=q_vN. \tag{4.3}
$$

Formula (4.3) matches the covariant Tate-curve representation: arithmetic Frobenius acts with eigenvalues $q_v$ and $1$, while $N$ maps the second line to the first.

Choose a nonzero $\ell$-adic tame character

$$
t_\lambda:I_v\longrightarrow E_\lambda
$$

with the conjugation law dictated by (4.3). On a sufficiently small inertia subgroup, write

$$
\rho_\lambda(\sigma)=
\exp(t_\lambda(\sigma)N). \tag{4.4}
$$

Removing this exponential gives the finite-inertia representation $r$. Changing the tame character rescales $N$ and gives an isomorphic Weil--Deligne pair. Thus the isomorphism class

$$
\operatorname{WD}_v(\rho_\lambda)=(r_{v,\lambda},N_{v,\lambda}) \tag{4.5}
$$

is intrinsic once the convention (4.1)--(4.2) is fixed.

### 4.2 Frobenius-semisimplification and monodromy

The Frobenius operator $r(\operatorname{Frob}_v)$ need not be semisimple. Its Jordan decomposition has a semisimple part and a commuting unipotent part. **Frobenius-semisimplification** replaces Frobenius by its semisimple part, modifies $r$ compatibly on the Weil group, and retains $N$:

$$
\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\text{-}ss}}
=(r_{v,\lambda}^{\mathrm{F\text{-}ss}},N_{v,\lambda}). \tag{4.6}
$$

The notation in (4.6) is a pair. It includes the nilpotent operator. This point deserves emphasis because the phrase “semisimplified local parameter” is sometimes used imprecisely for the Weil representation $r^{\mathrm{ss}}$ alone. Omitting $N$ loses monodromy.

In dimension two, the contrast is immediate. Consider

$$
r(w)e_1=\theta(w)\|w\|_ve_1,\qquad
r(w)e_2=\theta(w)e_2. \tag{4.7}
$$

The pair with $N=0$ and the pair with

$$
N(e_2)=e_1,\qquad N(e_1)=0 \tag{4.8}
$$

have the same semisimple Weil representation. The first is a two-character parameter; the second is special or Steinberg. Their conductors and inertia on the original $\ell$-adic representation differ. Thus Frobenius eigenvalues together with $r|_{I_v}$ do not recover the monodromy extension. The operator $N$ must be part of the common datum.

Frobenius-semisimplification with $N$ retained is the local object used by the usual local correspondence. It can still forget the unipotent part of Frobenius that commutes with the parameter. A claim about the full, non-Frobenius-semisimplified pair is therefore stronger and should be named separately.

### 4.3 Inertial type and conductor

The **inertial type** of a Weil--Deligne pair is the isomorphism class

$$
\tau_v(r,N)=r|_{I_v}. \tag{4.9}
$$

Because $r(I_v)$ is finite, this is a finite-image representation. It does not include $N$. For a Steinberg parameter with unramified twist, the inertial type is trivial even though monodromy is nonzero. Consequently inertial type and monodromy rank must be recorded separately.

The conductor exponent of $(r,N)$ is

$$
a_v(r,N)=a_v(r)+\dim V^{I_v}
-\dim(\ker N)^{I_v}, \tag{4.10}
$$

where $a_v(r)$ is the Artin conductor of the finite-inertia Weil representation. Formula (4.10) passes the basic tests:

- if $r$ is unramified and $N=0$, the conductor is $0$;
- if $r$ is unramified in dimension two and $N$ has rank one, the conductor is $1$;
- if $r=\theta\|\cdot\|\oplus\theta$ with ramified scalar character $\theta$, then $V^{I_v}=0$ and the conductor is $2a_v(\theta)$.

The local Euler polynomial only uses a suitable Frobenius action on an invariant kernel such as $(\ker N)^{I_v}$. Its degree can be $2$, $1$, or $0$. It cannot replace (4.9)--(4.10). Two parameters with the same local Euler polynomial can have different conductors or inertial types.

### 4.4 Strict and strong systems

The terminology in the literature is not completely uniform, so we fix it explicitly.

A weakly compatible system $\mathcal R$ is **strictly compatible away from coefficient primes**, or equivalently **strongly compatible** in this book, if, for every finite place $v$ of $F$, there is an algebraic Frobenius-semisimple Weil--Deligne pair

$$
D_v=(r_v,N_v) \tag{4.11}
$$

over a finite extension of $E$ such that for every $\lambda$ with $v\nmid\ell(\lambda)$ and every compatible embedding into $\overline{\mathbf Q}_{\ell(\lambda)}$,

$$
\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\text{-}ss}}
\simeq \iota_\lambda D_v. \tag{4.12}
$$

The field in (4.11) may be enlarged once to define all matrix coefficients at the finitely many bad places. If every $D_v$ is defined over $E$ itself, we call the system **$E$-rationally strongly compatible**.

A system is **unsemisimplified-locally compatible at $v$** if (4.12) holds before Frobenius-semisimplification, after the exact choices needed to compare full parameters have been made. This stronger condition is useful only when the nonsemisimple Frobenius extension is itself canonical. Most arithmetic applications require strict compatibility in the preceding sense: the Frobenius-semisimple pair with $N$ retained.

Strong compatibility immediately makes the following data independent of $\lambda$ for $\lambda\nmid v$:

$$
\tau_v,\qquad \operatorname{rank}N_v,\qquad
a_v(\rho_\lambda), \tag{4.13}
$$

as well as the local Euler polynomial. Weak compatibility supplies none of these conclusions at $v\in S$.

One also encounters the term **strictly compatible system** for a weak system whose local Euler polynomials on inertia invariants are independent of $\lambda$. That condition is weaker than (4.12) if it does not include the inertial type and $N$. Here both “strict” and “strong” mean the full pair displayed in (4.11); a statement about Euler factors alone will be named explicitly as such.

### 4.5 Principal series and Steinberg parameters

The two most important bad local types show why the full definition is needed. Let $\theta_1,\theta_2$ be algebraic local characters with adic avatars under arithmetic reciprocity.

For a principal-series parameter,

$$
D_v=(\theta_1\oplus\theta_2,0). \tag{4.14}
$$

Its inertial type is $\theta_1|_{I_v}\oplus\theta_2|_{I_v}$ and

$$
a_v(D_v)=a_v(\theta_1)+a_v(\theta_2). \tag{4.15}
$$

At the reducibility boundary of normalized parabolic induction, the two constituents do not have the same parameter. The character-type constituent has the relevant two-character parameter with $N=0$, while the special constituent has $N\ne0$. A local representation must therefore be identified as a constituent before its monodromy is named. For a cuspidal global representation of $\operatorname{GL}_2$, finite local components are generic, so the constituent appearing at this boundary is the special one and belongs to the next paragraph.

For a special parameter, define

$$
\operatorname{Sp}_2(\theta)
=\bigl(\theta\|\cdot\|_v\oplus\theta,N\bigr), \tag{4.16}
$$

with $N$ as in (4.8). Then

$$
\det r=\theta^2\|\cdot\|_v,\qquad
\operatorname{rank}N=1. \tag{4.17}
$$

If $\theta$ is unramified, (4.10) gives conductor exponent $1$. This is the parameter of an unramified twist of Steinberg in the covariant arithmetic normalization. Its Weil semisimplification is the same sum of two characters as in (4.14) with $\theta_1=\theta\|\cdot\|_v$ and $\theta_2=\theta$, but $N$ distinguishes the two cases.

At a Steinberg place of an elliptic curve, the original inertia action is unipotent, its invariant subspace has dimension one, and $N$ has rank one. Split versus nonsplit multiplicative reduction changes the unramified quadratic twist $\theta$; it does not change the monodromy rank or conductor exponent.

## 5. Places above the coefficient prime

### 5.1 Labelled Hodge--Tate weights

Let $\lambda\mid\ell$, let $u\mid\ell$ be a place of $F$, and let

$$
\rho_\lambda:G_{F_u}\longrightarrow\operatorname{GL}(V_\lambda)
$$

be a de Rham representation. The field $F_u$ can have several embeddings into $\overline{E}_\lambda$. Hodge--Tate weights must be indexed by them.

For every embedding

$$
\tau:F_u\hookrightarrow\overline{E}_\lambda,
$$

the $\tau$-labelled multiset $\operatorname{HT}_\tau(V_\lambda)$ records the graded jumps in the corresponding de Rham filtration. Our convention gives

$$
\operatorname{HT}_\tau(E_\lambda(1))=\{1\}. \tag{5.1}
$$

Thus

$$
\operatorname{HT}_\tau(V(r))
=\{h+r:h\in\operatorname{HT}_\tau(V)\}. \tag{5.2}
$$

If $V$ has dimension two and labelled weights $\{h_{1,\tau},h_{2,\tau}\}$, then

$$
\operatorname{HT}_\tau(\det V)
=\{h_{1,\tau}+h_{2,\tau}\}. \tag{5.3}
$$

This sum is an efficient determinant audit.

For a cohomological automorphic weight described by integers $a_{\tau_0}\ge b_{\tau_0}$, with

$$
k_{\tau_0}=a_{\tau_0}-b_{\tau_0}+2,\qquad
w=a_{\tau_0}+b_{\tau_0}, \tag{5.4}
$$

the algebraicity condition requires the sum defining the central weight $w$ to be independent of $\tau_0$. The expected covariant labelled weights are

$$
\{b_{\tau_0},a_{\tau_0}+1\}. \tag{5.5}
$$

Their sum is $w+1$, matching the determinant $\psi_\lambda\chi_\ell^{w+1}$. In parallel weight two, $a=b=0$ and (5.5) becomes $\{0,1\}$.

An unlabelled multiset can be misleading when the weights vary with $\tau_0$. Even when all embeddings have the same pair, the labelled formulation is the one stable under base change and coefficient conjugation.

### 5.2 De Rham, crystalline, and semistable representations

The coefficient-prime local categories measure how close an $\ell$-adic representation is to coming from good or semistable geometry.

A representation is **de Rham** if its de Rham period module has the full expected dimension:

$$
\operatorname{rank}_{F_u\otimes_{\mathbf Q_\ell}E_\lambda}
D_{\mathrm{dR}}(V)=\dim_{E_\lambda}V. \tag{5.6}
$$

Its filtered module gives the labelled weights. It is **crystalline** if its crystalline period module has full dimension, and **semistable** if its semistable period module has full dimension. There are implications

$$
\text{crystalline}\Longrightarrow
\text{semistable}\Longrightarrow
\text{de Rham}. \tag{5.7}
$$

Potentially crystalline and potentially semistable mean that the property holds after a finite extension of $F_u$.

Crystalline does not mean unramified. The cyclotomic character is crystalline and ramified at $\ell$. An elliptic curve with good reduction gives a crystalline $V_\ell E$ with weights $\{0,1\}$; an elliptic curve with multiplicative reduction gives a semistable noncrystalline representation with nonzero monodromy. These examples explain why the coefficient-prime place cannot be forced into the good-prime definition.

The semistable period module also carries a Frobenius and a monodromy operator. Its monodromy is the coefficient-prime analogue of the $N$ at a place away from $\ell$, but it belongs to a different comparison category. Strong compatibility away from coefficient primes does not by itself identify these modules as $\lambda$ varies.

### 5.3 Hodge compatibility as the coefficient place varies

To state independence correctly, begin with algebraic labels. Let

$$
\Sigma_F=\operatorname{Hom}(F,\overline{\mathbf Q}).
$$

A **labelled Hodge datum** of rank $n$ is a multiset $H_{\tau_0}$ of $n$ integers for every $\tau_0\in\Sigma_F$, compatible with the coefficient field required to define the algebraic weight.

A weak system is **Hodge compatible** with datum $H$ if, for every $\lambda\mid\ell$ and every $u\mid\ell$, the restriction $\rho_\lambda|_{G_{F_u}}$ is de Rham and, for every embedding $\tau_0:F\hookrightarrow\overline{\mathbf Q}$ inducing $u$ after composition with $\iota_\lambda$,

$$
\operatorname{HT}_{\iota_\lambda\circ\tau_0}
(\rho_\lambda|_{G_{F_u}})=H_{\tau_0}. \tag{5.8}
$$

A system that is Hodge compatible in this de Rham, integral-labelled sense will be called **algebraic**. It is **regular** when the integers in each $H_{\tau_0}$ are distinct. These adjectives concern the de Rham realizations and their labelled weights; the mere fact that $P_v(X)$ has coefficients in a number field is not the same algebraicity assertion.

If the coefficient automorphism used to change $\lambda$ also conjugates the automorphic weight, it transports both the coefficient values and the label $\tau_0$. Formula (5.8) is therefore equivariant, not invariant under an unexplained relabeling.

One may similarly ask that $\rho_\lambda$ be crystalline at every $u\mid\ell$ outside a fixed set of geometric bad places, or semistable at all such $u$. These are uniform comparison theorems, not consequences of the polynomials $P_v$. In an automorphic construction they must come from the relevant coefficient-prime local--global comparison. In a geometric construction they come from good or semistable reduction.

### 5.4 The coefficient-prime boundary

Four distinctions prevent overstatement at $u\mid\ell$.

First, no arithmetic-Frobenius conjugacy class in $G_{F_u}$ is defined modulo trivial inertia unless the representation is unramified. A crystalline Frobenius lives on a period module, not as an arbitrary lift of residue Frobenius acting on $V_\lambda$.

Second, Hodge--Tate weights concern the rational representation. They do not choose a stable lattice. Two lattices in the same de Rham representation can have different residual extensions.

Third, a crystalline representation with weights $\{0,1\}$ need not automatically supply the particular compatible tower of finite-flat group schemes demanded by an integral deformation problem. For a Tate module of an abelian scheme, the geometric lattice supplies that tower. For an abstract representation, it is extra integral data.

Fourth, the phrase “independent of $\ell$ at places above $\ell$” never means that the local fields $F_u$ are canonically the same as $\ell$ varies. It means that the algebraically labelled weights and the prescribed comparison category follow a common rule. The coefficient-prime places themselves move.

These limits are productive. They identify exactly what a changing-prime theorem must recheck at the new prime: labelled Hodge type, crystalline or semistable status, and whatever integral lattice condition the next argument actually uses.

## 6. Purity, parity, and polarization

### 6.1 Purity and weights

Compatibility says that Frobenius polynomials are algebraic. Purity adds an archimedean size condition on their roots. It is a theorem of geometry or automorphic analysis, not a formal consequence of algebraicity.

A weak system is **pure of weight $m$** if, for every $v$ outside a finite set and every root $\alpha$ of $P_v(X)$, one has

$$
|\sigma(\alpha)|=q_v^{m/2} \tag{6.1}
$$

for every embedding $\sigma:\overline{\mathbf Q}\hookrightarrow\mathbf C$. The quantifier over all complex embeddings is essential. Bounding the roots in one preferred embedding is not coefficient-field rational purity.

For a rank-two pure system,

$$
P_v(X)=X^2-a_vX+d_v
$$

has roots of absolute value $q_v^{m/2}$ and hence

$$
|\sigma(d_v)|=q_v^m. \tag{6.2}
$$

If $d_v=\psi(v)q_v^m$ with $\psi$ finite order, (6.2) is automatic for the determinant, but it does not prove the corresponding bound for each root. The trace bound

$$
|\sigma(a_v)|\le2q_v^{m/2} \tag{6.3}
$$

is necessary and, together with the determinant and the appropriate conjugate pairing, often sufficient in dimension two.

Purity behaves predictably under operations. A Tate twist by $(r)$ changes weight $m$ to $m+2r$. The tensor product of pure systems of weights $m_1,m_2$ is pure of weight $m_1+m_2$. The dual has weight $-m$. Restriction to a finite extension preserves the weight because $q_w=q_v^{f(w/v)}$ and the restricted Frobenius roots are $f(w/v)$-th powers.

None of these statements creates purity when it was absent. A weak system assembled from arbitrary continuous representations may have algebraic common polynomials with roots of unrelated complex sizes.

### 6.2 Complex conjugation and oddness

Suppose $F$ is totally real. For every real embedding $\tau:F\hookrightarrow\mathbf R$, choose a complex conjugation $c_\tau\in G_F$, well defined up to conjugacy. A two-dimensional characteristic-zero representation is **odd at $\tau$** if

$$
\det\rho_\lambda(c_\tau)=-1. \tag{6.4}
$$

Since $c_\tau^2=1$, its eigenvalues are $\pm1$. If the representation is odd, they are $1$ and $-1$, so

$$
\operatorname{tr}\rho_\lambda(c_\tau)=0. \tag{6.5}
$$

It is **totally odd** if this holds at every real place.

For a determinant

$$
\det\rho_\lambda=\psi_\lambda\chi_\ell^m,
$$

oddness is the parity identity

$$
\psi(c_\tau)(-1)^m=-1. \tag{6.6}
$$

This formula audits the finite central character at infinity. Oddness is not the assertion that $c_\tau$ acts by $-1$ on both dimensions; that scalar action would have determinant $+1$.

Modulo $2$, the eigenvalues $1$ and $-1$ coincide. Thus residual determinant alone does not detect oddness in characteristic two. Oddness is first a characteristic-zero condition, even when it later enters a residual modularity theorem through the existence of an odd lift.

If $F$ has complex places, there is no corresponding conjugacy class of real complex conjugations at those places. One should not extend the word “odd” to them by analogy without defining a different polarization condition.

### 6.3 Polarizations and essential self-duality

A **polarization** of a system is a compatible character system $\mu=\{\mu_\lambda\}$ together with perfect pairings

$$
\langle\ ,\ \rangle_\lambda:
V_\lambda\times V_\lambda\longrightarrow E_\lambda(\mu_\lambda)
$$

such that

$$
\langle\rho_\lambda(g)x,\rho_\lambda(g)y\rangle_\lambda
=\mu_\lambda(g)\langle x,y\rangle_\lambda. \tag{6.7}
$$

Equivalently,

$$
\rho_\lambda^\vee\simeq
\rho_\lambda\otimes\mu_\lambda^{-1}. \tag{6.8}
$$

This is called essential self-duality. In rank two the exterior product always gives an alternating pairing with multiplier $\det\rho_\lambda$, and linear algebra gives

$$
V_\lambda^\vee\simeq
V_\lambda\otimes(\det V_\lambda)^{-1}. \tag{6.9}
$$

Thus the existence of some essential self-duality is tautological in dimension two. Its arithmetic content lies in identifying the multiplier as one compatible algebraic character, choosing an integral pairing when needed, and matching it with the automorphic central character.

For an elliptic curve, the Weil pairing gives

$$
V_\ell E\simeq(V_\ell E)^\vee(1),
\qquad
\mu_\ell=\chi_\ell. \tag{6.10}
$$

For a regular algebraic automorphic system of central weight $w$ and finite central character $\psi$,

$$
\mu_\lambda=\psi_\lambda\chi_\ell^{w+1}. \tag{6.11}
$$

Calling (6.10) or (6.11) ordinary self-duality would omit the multiplier and reverse later determinant twists.

### 6.4 A coefficient-rational symmetry package

The most useful symmetry statement is algebraic before completion. Suppose there are an integer $m$, a finite-order algebraic Hecke character $\psi$, and a pure system $\mathcal R$ such that

$$
\det\rho_\lambda=\psi_\lambda\chi_\ell^m,\qquad
\rho_\lambda^\vee\simeq
\rho_\lambda\otimes(\psi_\lambda\chi_\ell^m)^{-1}. \tag{6.12}
$$

At every good $v$, if $\alpha_v,\beta_v$ are the roots of $P_v$, then

$$
\alpha_v\beta_v=\psi(v)q_v^m. \tag{6.13}
$$

Duality replaces them by $\alpha_v^{-1},\beta_v^{-1}$; twisting by the inverse determinant returns the same unordered pair. Purity pairs each root with the appropriate complex-conjugate reciprocal of size $q_v^{m/2}$.

This record is coefficient-rational when $\psi$, $m$, and the $P_v$ are defined over $E$ and every coefficient conjugation transports the whole package. It is stronger than observing a self-duality after choosing one completion. It is the form stable under changing $\lambda$ and under automorphic conjugation.

## 7. Integral lattices and residual members

### 7.1 Stable lattices

Residual arithmetic begins with an integral choice that the rational compatible system does not make. Let

$$
\rho_\lambda:G_F\longrightarrow\operatorname{GL}(V_\lambda)
$$

be a continuous finite-dimensional representation over $E_\lambda$. A **stable lattice** is a full $\mathcal O_\lambda$-lattice $T_\lambda\subset V_\lambda$ satisfying

$$
\rho_\lambda(g)T_\lambda=T_\lambda
\qquad(g\in G_F). \tag{7.1}
$$

Such a lattice exists. Choose any lattice $L_0$. The image of the compact group $G_F$ is bounded, so all translates of $L_0$ lie in one bounded fractional lattice. Their $\mathcal O_\lambda$-span is finitely generated, full, and stable.

Geometry often supplies a preferred lattice, such as $T_\ell E$ or a coefficient factor in the Tate module of an abelian variety. Preferred does not mean canonical in the rational isomorphism class. Isogenous varieties, different integral projectors, or different embeddings into ambient cohomology can produce nonhomothetic lattices in the same $V_\lambda$.

A compatible system of rational representations therefore does not automatically contain an integral compatible system. To obtain one, one must choose $T_\lambda$ for every $\lambda$, preferably by a uniform geometric or automorphic construction, and record any integral pairings and local models those choices carry.

### 7.2 Reduction and lattice independence

Reducing a stable lattice gives a continuous residual representation

$$
\bar\rho_{T_\lambda}:G_F\longrightarrow
\operatorname{GL}_n(k_\lambda). \tag{7.2}
$$

Its isomorphism class can depend on $T_\lambda$. Its semisimplification does not.

**Theorem 7.1 (lattice-independent residual semisimplification).** If $T$ and $T'$ are stable lattices in the same characteristic-zero representation $V$, then, after extending the residue field if necessary,

$$
(T/\varpi T)^{\mathrm{ss}}\simeq
(T'/\varpi T')^{\mathrm{ss}}. \tag{7.3}
$$

**Proof.** Every $g\in G_F$ preserves both lattices, so its characteristic polynomial on $V$ has coefficients in $\mathcal O_\lambda$. Reduction gives the characteristic polynomial of $g$ on either residual lattice. Thus the two residual representations have the same characteristic-polynomial function. The Brauer--Nesbitt theorem over the residue field identifies their semisimplifications. $\square$

We may therefore write

$$
\bar\rho_\lambda^{\mathrm{ss}}
$$

without naming a lattice. We may not write an unqualified nonsplit residual extension without naming one.

If $\bar\rho_\lambda^{\mathrm{ss}}$ is absolutely irreducible, every reduction is already irreducible and the reductions of all stable lattices are isomorphic. In that case stable lattices are homothetic under the usual irreducibility hypotheses. At reducible primes, extension directions can change.

### 7.3 Residual determinants and ramification

For a chosen stable lattice, determinant commutes with reduction:

$$
\det\bar\rho_{T_\lambda}
=\overline{\det\rho_\lambda}. \tag{7.4}
$$

Hence a determinant of the form (3.4) gives

$$
\det\bar\rho_\lambda
=\bar\psi_\lambda\bar\chi_\ell^m. \tag{7.5}
$$

At a good place $v\nmid\ell$,

$$
\det(X-\bar\rho_\lambda^{\mathrm{ss}}(\operatorname{Frob}_v))
\equiv P_v(X)\pmod\lambda. \tag{7.6}
$$

Residual ramification is subtler. If $\rho_\lambda$ is unramified, every stable lattice reduction is unramified. The converse fails: nontrivial integral inertia can become trivial modulo $\lambda$. At a multiplicative place $v\nmid\ell(\lambda)$ of an elliptic curve, inertia has the form

$$
\begin{pmatrix}1&m_vt_\ell(\sigma)\\0&1\end{pmatrix}, \tag{7.7}
$$

For the geometric Tate lattice, its generally nonsemisimple reduction is unramified precisely when $\ell(\lambda)$ divides the relevant monodromy thickness $m_v$. This is a statement about that chosen integral lattice, not a lattice-independent nonsplit extension claim. The characteristic-zero conductor remains one.

In particular, for the common bad set $S$ of (3.3), every residual member is unramified outside

$$
S\cup\{v:v\mid\ell(\lambda)\}. \tag{7.7a}
$$

Reduction can remove ramification inside this set, but it cannot create ramification at a place where the chosen characteristic-zero lattice action was already trivial.

Finite inertial characters can also collapse on reduction when their order is divisible by $\ell$. Thus strong characteristic-zero compatibility does not make residual conductors constant. If the chosen lattices come from one uniform algebraic integral model, fixed finite-inertia distinctions and fixed nonzero integral monodromy certificates survive outside finitely many coefficient primes; without that uniform model there is no such conclusion. At the exceptional primes the residual local data must be recomputed.

### 7.4 Residual systems are a separate layer

A **residual member** is one semisimplified representation $\bar\rho_\lambda^{\mathrm{ss}}$ in characteristic $\ell(\lambda)$. A **residual compatible family** means a chosen collection of such members, usually together with specified lattices or finite-level geometric objects, whose good Frobenius polynomials satisfy (7.6).

There is no single coefficient ring containing all residual members. Their characteristics vary. Congruences modulo two different primes are not scalar extensions of one another. The common algebraic polynomial $P_v$ is again the bridge.

Residual properties can be uniform only after a theorem. Statements such as

$$
\bar\rho_\lambda\text{ is absolutely irreducible},
\qquad
\bar\rho_\lambda(G_F)\text{ is adequate} \tag{7.8}
$$

may hold for a density-one set of $\lambda$, for all but finitely many $\lambda$, or only for a selected $\lambda$. The definition of weak compatibility chooses none of these outcomes.

Likewise, a compatible rational determinant gives residual determinants at all $\lambda$, but a compatible integral local condition at $v\mid\ell$ requires chosen integral models. A rational de Rham family is not by itself a family of finite-flat residual representations.

### 7.5 Two lattices with different reductions

An explicit calculation shows exactly what lattice independence does and does not mean. Let $\Gamma\simeq\mathbf Z_\ell$ be topologically generated by $\gamma$, let $K/\mathbf Q_\ell$ have uniformizer $\varpi$, and consider

$$
\rho(\gamma)=
\begin{pmatrix}1&0\\0&1+\varpi\end{pmatrix} \tag{7.9}
$$

on $V=Ke_1\oplus Ke_2$. Continuity extends (7.9) to $\Gamma$.

The standard lattice

$$
T_0=\mathcal Oe_1\oplus\mathcal Oe_2
$$

is stable, and its reduction is the split trivial representation. Now put

$$
f_2=\frac{e_2-e_1}{\varpi},\qquad
T_1=\mathcal Oe_1\oplus\mathcal Of_2. \tag{7.10}
$$

Since $e_2=e_1+\varpi f_2$,

$$
\rho(\gamma)f_2=e_1+(1+\varpi)f_2. \tag{7.11}
$$

Thus $T_1$ is stable and

$$
\bar\rho_{T_1}(\gamma)=
\begin{pmatrix}1&1\\0&1\end{pmatrix}, \tag{7.12}
$$

a nonsplit self-extension of the trivial character. The reductions of $T_0$ and $T_1$ are not isomorphic, while both have semisimplification $1\oplus1$. Their characteristic polynomials are identical for every group element.

This example is the integral version of the limitation of Chebotarev. Traces and determinants see the diagonal characters. A lattice chooses how congruent characters are glued.

## 8. Algebraic operations on systems

### 8.1 Coefficient extension and coefficient restriction

Compatible systems should survive the operations used in later arguments. Coefficient extension is the simplest. Let $E'/E$ be finite. For every $\lambda'\mid\lambda$, define

$$
\rho_{\lambda'}'=\rho_\lambda
\otimes_{E_\lambda}E'_{\lambda'}. \tag{8.1}
$$

Regard $P_v$ as a polynomial over $E'$. Then $\{\rho'_{\lambda'}\}$ is weakly compatible. Strong local parameters and labelled Hodge data extend by scalars. Purity is unchanged.

Several places $\lambda'$ can lie above one $\lambda$; coefficient extension repeats the scalar realization at each of them. It does not create new arithmetic Frobenius eigenvalues. Residual representations can change their field of definition, and absolute irreducibility should be tested after algebraic residue-field extension.

Coefficient restriction is not automatic. Suppose the $P_v$ lie in a subfield $E_0\subset E$. To descend the system to $E_0$, one needs $E_{0,\lambda_0}$-models whose scalar extensions recover all members above $\lambda_0$, compatibly with conjugation. Equality of traces can determine a semisimple representation over an algebraic closure but need not split its endomorphism algebra over $E_{0,\lambda_0}$. Thus

$$
P_v\in E_0[X]\quad\not\Longrightarrow\quad
\rho_\lambda\text{ has an }E_{0,\lambda_0}\text{-model}. \tag{8.2}
$$

When an absolutely irreducible member has a proved descent datum satisfying the cocycle condition, Schur's lemma makes the remaining ambiguity scalar and ordinary descent produces the smaller model. That is a theorem, not a change of notation.

### 8.2 Twists and Tate twists

Let $\mathcal R$ be a rank-$n$ compatible system and let $\Theta=\{\theta_\lambda\}$ be a compatible character system with good values $c_v$. The twist

$$
\mathcal R\otimes\Theta
=\{\rho_\lambda\otimes\theta_\lambda\}_\lambda \tag{8.3}
$$

has good polynomial

$$
P_v^{\Theta}(X)
=\prod_{i=1}^n(X-c_v\alpha_{v,i}), \tag{8.4}
$$

where the $\alpha_{v,i}$ are the roots of $P_v$. In rank two,

$$
X^2-a_vX+d_v
\longmapsto
X^2-c_va_vX+c_v^2d_v. \tag{8.5}
$$

At $v\nmid\ell$, the Weil--Deligne parameter is $D_v\otimes\theta_v$ and $N$ becomes $N\otimes1$. A ramified twist can change inertial type and conductor in ways not determined by the two separate conductor exponents; equal-depth characters can cancel.

A Tate twist by $(r)$ is the special case $\theta_\lambda=\chi_\ell^r$. It changes good roots by $q_v^r$, Hodge--Tate weights by $r$, and purity weight by $2r$. For a rank-$n$ representation, the determinant is multiplied by $\chi_\ell^{nr}$.

Finite-order twists preserve purity weight and the differences between Hodge--Tate weights, but they can change archimedean signs and finite local types. A quadratic twist preserves a rank-two determinant because the determinant changes by the square of the twisting character; it does not preserve every conductor.

### 8.3 Duals, sums, tensors, and symmetric powers

If $P_v$ has roots $\alpha_{v,1},\ldots,\alpha_{v,n}$, then the dual system has good roots

$$
\alpha_{v,1}^{-1},\ldots,\alpha_{v,n}^{-1}. \tag{8.6}
$$

The direct sum of systems has the product of their polynomials. The tensor product has roots

$$
\alpha_{v,i}\beta_{v,j}, \tag{8.7}
$$

and rank equal to the product of ranks. The $m$-th symmetric power of a two-dimensional system has roots

$$
\alpha_v^m,\alpha_v^{m-1}\beta_v,\ldots,
\alpha_v\beta_v^{m-1},\beta_v^m \tag{8.8}
$$

and rank $m+1$.

These formulas prove weak compatibility because symmetric polynomials in algebraic roots lie in the coefficient field. If necessary one may define the operation on each member and then take semisimplification; the good characteristic polynomial is unchanged.

Hodge labels obey the same linear algebra. Dual weights are the negatives of the original weights. Tensor weights are pairwise sums. Symmetric-power weights are the sums occurring in (8.8). Purity weights negate, add, and multiply by $m$ respectively.

These operations generally change dimension. A tensor product of two rank-two systems has rank four; a symmetric square has rank three. Later arguments that require a two-dimensional residual representation cannot silently apply to them.

### 8.4 Local data under tensor operations

Strong compatibility is stable under the standard tensor operations because the Weil--Deligne construction is tensorial. For two pairs $(r_1,N_1)$ and $(r_2,N_2)$,

$$
(r_1,N_1)\otimes(r_2,N_2)
=\left(r_1\otimes r_2,
N_1\otimes1+1\otimes N_2\right). \tag{8.9}
$$

For the dual,

$$
N^\vee(f)=-f\circ N. \tag{8.10}
$$

Direct sums use block-diagonal monodromy, and symmetric powers use the derivation induced by $N$.

The conductor of a direct sum is additive. There is no comparably simple formula for the conductor of a tensor product using only the two original conductor exponents. One must compute inertia fixed spaces, breaks, and the operator in (8.9). Likewise, knowing only the ranks of $N_1$ and $N_2$ does not determine the rank of the tensor monodromy; the full Jordan types entering the sum in (8.9) matter.

An integral tensor operation requires stable lattices. The tensor product and dual of chosen lattices are natural, but a direct summand cut out by a rational idempotent can introduce denominators. Residual symmetric powers can acquire new invariant subspaces. Rational compatibility survives; desired residual or finite-flat properties require separate checks.

## 9. Changing the base field and inducing

### 9.1 Restriction to a finite extension

Let $F'/F$ be finite. Restriction gives

$$
\rho_\lambda|_{G_{F'}}:G_{F'}\longrightarrow
\operatorname{GL}_n(E_\lambda). \tag{9.1}
$$

The rank does not change. Continuity and semisimplicity are preserved after taking semisimplification if needed. A common ramification set is obtained from places above $S$ together with any places at which one wants to avoid a ramified polynomial calculation.

Restriction can make an irreducible representation reducible. The basic example is

$$
\rho_\lambda=\operatorname{Ind}_{G_M}^{G_F}\theta_\lambda
$$

for a quadratic extension $M/F$. Then

$$
\rho_\lambda|_{G_M}\simeq
\theta_\lambda\oplus\theta_\lambda^\sigma. \tag{9.2}
$$

Thus absolute irreducibility and adequacy must be rechecked after every base-field extension. Linear disjointness from a residual fixed field is a standard way to preserve the residual image, but it is a hypothesis with a proof, not a consequence of finite degree.

At places away from the coefficient prime, strong local data restrict:

$$
(r_v,N_v)\longmapsto
(r_v|_{W_{F'_w}},N_v). \tag{9.3}
$$

The operator $N_v$ is unchanged, while inertia can shrink and make a finite type trivial. Conductors can rise or fall because upper ramification depths are reindexed. No formula involving only $[F'_w:F_v]$ and the old conductor is valid in general.

At coefficient-prime places, de Rham, crystalline, and semistable representations remain so after restriction to a finite local extension, with the appropriate base-changed filtered modules. Hodge labels pull back along embeddings $F'\hookrightarrow\overline{\mathbf Q}_\ell$.

### 9.2 Good-prime polynomials after restriction

Suppose $v$ is unramified in $F'/F$, $w\mid v$, and $\rho_\lambda$ is unramified at $v$. Let

$$
f=f(w/v)=[k_w:k_v].
$$

Arithmetic Frobenius over $F'_w$ maps to the $f$-th power of arithmetic Frobenius over $F_v$. If $P_v$ has roots $\alpha_{v,1},\ldots,\alpha_{v,n}$, then the restricted polynomial is

$$
P_w^{F'}(X)=
\prod_{i=1}^n(X-\alpha_{v,i}^{f}). \tag{9.4}
$$

It lies in $E[X]$ because it is obtained from $P_v$ by symmetric polynomial operations. In rank two, put $A_f=\alpha_v^f+\beta_v^f$. Then

$$
A_0=2,\qquad A_1=a_v,\qquad
A_f=a_vA_{f-1}-d_vA_{f-2}, \tag{9.5}
$$

and

$$
P_w^{F'}(X)=X^2-A_fX+d_v^f. \tag{9.6}
$$

The ramification index does not replace $f$ in these formulas. If $F'_w/F_v$ is ramified but the original parameter is unramified, (9.4) still holds: the restricted inertia acts trivially and the arithmetic Frobenius degree is still $f$.

Purity is preserved because

$$
|\alpha_{v,i}^{f}|=q_v^{fm/2}=q_w^{m/2}. \tag{9.7}
$$

This is the correct weight calculation under base change.

### 9.3 Galois induction and its local polynomial

Induction goes in the opposite direction and changes rank. If $F'/F$ has degree $d$ and $V_\lambda$ has rank $n$, then

$$
\operatorname{Ind}_{G_{F'}}^{G_F}V_\lambda
$$

has rank $nd$. Continuity follows because $G_{F'}$ is open of finite index. The determinant contains the determinant of the coset permutation representation; omitting that sign character gives the wrong answer already when $V$ is trivial.

Let $\Delta_{F'/F}$ be the determinant of the permutation representation of $G_F$ on $G_F/G_{F'}$, and let $\operatorname{Ver}_{F'/F}:G_F^{\mathrm{ab}}\to G_{F'}^{\mathrm{ab}}$ be transfer. The precise formula is

$$
\det\operatorname{Ind}_{G_{F'}}^{G_F}V
=\Delta_{F'/F}^{\,n}
\bigl((\det V)\circ\operatorname{Ver}_{F'/F}\bigr). \tag{9.7a}
$$

Consequently, inducing every member of a weak compatible system over $F'$ gives a weak compatible system of rank $nd$ over $F$. Its common bad set contains the primes below the old bad set and the primes ramified in $F'/F$. The algebraic good polynomials are computed below, so this assertion is independent of choices of coset bases.

At a finite place $v$, Mackey decomposition gives

$$
\left.\operatorname{Ind}_{G_{F'}}^{G_F}V\right|_{G_{F_v}}
\simeq
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{F'_w}}^{G_{F_v}}V|_{G_{F'_w}}. \tag{9.8}
$$

Assume $v$ is unramified in $F'/F$ and all local representations are unramified. If $A_w=\rho(\operatorname{Frob}_w)$ and $f_w=f(w/v)$, the characteristic polynomial of arithmetic Frobenius on the induced representation is

$$
P_v^{\operatorname{Ind}}(X)
=\prod_{w\mid v}\det(X^{f_w}I_n-A_w). \tag{9.9}
$$

To prove (9.9), choose coset bases around each Frobenius orbit. Frobenius cyclically permutes the $f_w$ copies, and its $f_w$-th power acts on the first copy as $A_w$. The companion-block determinant is $\det(X^{f_w}I_n-A_w)$. Multiplying the orbits proves the formula.

If the original system is strongly compatible, induction preserves strong compatibility in the range where local induction of Weil--Deligne parameters is available. The common parameter is

$$
D_v^{\operatorname{Ind}}
=\bigoplus_{w\mid v}
\operatorname{Ind}_{W_{F'_w}}^{W_{F_v}}D_w. \tag{9.9a}
$$

The nilpotent operator is induced together with the Weil action; it is not discarded. Conductors of (9.9a) include the local extension and discriminant terms and should be computed by the induction formula for Artin conductors, not by multiplying the old exponent by $d$.

For a character and an inert quadratic prime, (9.9) becomes

$$
X^2-\theta(\operatorname{Frob}_w). \tag{9.10}
$$

Its trace is zero. For a rank-two input, the same quadratic field induction has rank four, not rank two.

### 9.4 Automorphic induction and the dimension warning

When $M/F$ is quadratic and $\theta$ is an algebraic Hecke character of $M$, automorphic induction gives a representation

$$
\operatorname{AI}_{M/F}(\theta)
$$

of $\operatorname{GL}_2(\mathbf A_F)$. Its Galois system is

$$
\rho_\lambda=
\operatorname{Ind}_{G_M}^{G_F}\theta_\lambda. \tag{9.11}
$$

It is cuspidal exactly when $\theta\ne\theta^\sigma$. The determinant is

$$
\det\rho_\lambda
=\eta_{M/F,\lambda}(\theta_\lambda\circ\operatorname{Ver}), \tag{9.12}
$$

matching the automorphic central character

$$
\eta_{M/F}\,\theta|_{C_F}. \tag{9.13}
$$

The factor $\eta_{M/F}$ is the determinant of the permutation action on two cosets.

For a cyclic extension $M/F$ of degree $d$, induction of a character produces a rank-$d$ system and, when the cyclic automorphic-induction theorem applies, a representation of $\operatorname{GL}_d$. Induction of a two-dimensional system produces rank $2d$ and would correspond to higher-rank automorphic induction, not to a new $\operatorname{GL}_2$ form.

This distinction matters in descent arguments. Base change of a $\operatorname{GL}_2$ representation is restriction and remains two-dimensional. Automorphic induction from a quadratic character is a special rank-one-to-rank-two construction. The words “induce the system” do not preserve dimension.

## 10. The automorphic construction

### 10.1 Regular algebraic cuspidal input

The principal source of two-dimensional compatible systems in this setting is a regular algebraic cuspidal automorphic representation

$$
\pi=\bigotimes_v'\pi_v
$$

of $\operatorname{GL}_2(\mathbf A_F)$, with $F$ totally real. Let its cohomological weight be described by $((k_{\tau_0}),w)$, or equivalently by pairs $(a_{\tau_0},b_{\tau_0})$ satisfying (5.4). Let $\psi_\pi$ be the finite-order part of its algebraic central character.

The construction used here is exactly the curve-realizable construction established earlier. Thus one assumes that $\pi$ occurs in the appropriate parabolic cohomology of a modular curve, or transfers to a noncharacter representation on a quaternion algebra split at exactly one real place and occurs in the first cohomology of the corresponding Shimura curve with its algebraic coefficient system. The chosen newvector or local-type line and archimedean cohomological type must have the required multiplicity one. In higher weight, the coefficient system and its Hecke correspondences must extend over every integral model at which a polynomial is asserted.

These hypotheses are structural. Regular algebraicity supplies an algebraic coefficient system. Cuspidality removes Eisenstein character blocks. Curve realization supplies the Galois action. Multiplicity one isolates two dimensions. None follows from the existence of formal Hecke eigenvalues alone.

Let $E_\pi$ contain the algebraically normalized Hecke eigenvalues and the values of $\psi_\pi$. After one finite enlargement needed to define the selected cohomological factors, assume the construction gives, for every finite $\lambda$ of $E_\pi$,

$$
\rho_{\pi,\lambda}:G_F\longrightarrow
\operatorname{GL}_2(E_{\pi,\lambda}). \tag{10.1}
$$

If a particular realization is initially obtained only after a further local scalar extension, coefficient descent must be supplied before calling (10.1) an $E_\pi$-valued system.

### 10.2 One common polynomial at every good place

Let $S_\pi$ contain the automorphic conductor, ramification of the finite central character, quaternionic discriminant, coefficient-system bad reduction, and any auxiliary level that has not been removed. For $v\notin S_\pi$, define

$$
P_{\pi,v}(X)
=X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}
\in E_\pi[X]. \tag{10.2}
$$

For every $\lambda\nmid v$, the geometric construction and the arithmetic-Frobenius conversion give

$$
\det\bigl(X-\rho_{\pi,\lambda}(\operatorname{Frob}_v)\bigr)
=\iota_\lambda P_{\pi,v}(X). \tag{10.3}
$$

The exponent $w+1$ is the motivic weight. For a classical form of weight $k$, $w=k-2$ and (10.2) is

$$
X^2-a_v(f)X+\varepsilon(v)q_v^{k-1}. \tag{10.4}
$$

For weight two with trivial nebentype, it is $X^2-a_vX+q_v$.

The central scalar must be on the displayed side. In the geometric correspondence convention where the scalar operator is $S_v=\langle v\rangle^{-1}$, passage from geometric Frobenius on untwisted cohomology to arithmetic Frobenius on the covariant realization replaces $S_v$ by $S_v^{-1}$. Thus the determinant is $\varepsilon(v)q_v$, not $\varepsilon(v)^{-1}q_v$.

### 10.3 The weak automorphic system

**Theorem 10.1 (automorphic weak system).** Under the hypotheses of Section 10.1, assume the representations (10.1) are semisimple and defined over the stated completions. Then

$$
\mathcal R(\pi)=\{\rho_{\pi,\lambda}\}_\lambda \tag{10.5}
$$

with the polynomials (10.2) is a rank-two weakly compatible system over $F$ with coefficients in $E_\pi$. Its determinant is

$$
\det\rho_{\pi,\lambda}
=\psi_{\pi,\lambda}\chi_{\ell(\lambda)}^{w+1}. \tag{10.6}
$$

It is totally odd and polarized with multiplier (10.6).

**Proof.** The construction of each member gives continuity and ramification only at the places in $S_\pi$ together with places above $\ell(\lambda)$. Equation (10.3) supplies the common polynomial. These are precisely the clauses of weak compatibility. The constant term of (10.3) agrees at a dense set with the character on the right of (10.6), so Chebotarev proves the determinant identity. Cohomological complex conjugation has eigenvalues $1,-1$, giving total oddness. Poincaré duality and the coefficient-system pairing give the polarization; in dimension two its multiplier agrees with the determinant. $\square$

The proof does not use local behavior at $S_\pi$. It therefore does not prove strong compatibility there. That is a separate comparison statement.

### 10.4 Hodge weights, determinant, and purity

Assume the coefficient-prime comparison theorem for the chosen geometric realization. Then at a place $u\mid\ell(\lambda)$ and label $\tau_0:F\hookrightarrow\overline{\mathbf Q}$ inducing $u$ through $\iota_\lambda$,

$$
\operatorname{HT}_{\iota_\lambda\tau_0}
(\rho_{\pi,\lambda})
=\{b_{\tau_0},a_{\tau_0}+1\}. \tag{10.7}
$$

Their sum is $w+1$, which matches (10.6). At places where the relevant integral model has good reduction and the comparison theorem applies, the representation is crystalline. In semistable geometric regimes it is semistable, with the predicted monodromy. No such assertion is included outside the established comparison range.

Assume also the purity theorem for the cohomological automorphic representation. Every complex embedding of every root of (10.2) then has absolute value

$$
q_v^{(w+1)/2}. \tag{10.8}
$$

Thus $\mathcal R(\pi)$ is pure of weight $w+1$. Algebraicity alone would not prove (10.8); it enters as an independent theorem about the automorphic or geometric realization.

For parallel weight two, (10.7) becomes $\{0,1\}$, (10.6) is $\psi\chi_\ell$, and purity has weight one. If an integral abelian-scheme factor exists at $u\mid\ell$, its chosen Tate lattice has finite-flat quotients. An arbitrary stable lattice in the same rational representation is not automatically the generic fiber of that same integral factor.

### 10.5 The strong automorphic system

Local--global compatibility is what upgrades Theorem 10.1. For every finite $v$, let

$$
D(\pi_v)=(r(\pi_v),N(\pi_v)) \tag{10.9}
$$

be the algebraically normalized local parameter, expressed with arithmetic reciprocity and the convention (4.2).

**Theorem 10.2 (automorphic strong system).** In addition to Theorem 10.1, assume that for every finite $v$ and every $\lambda\nmid v$, the chosen geometric realization satisfies full local--global compatibility in the form

$$
\operatorname{WD}_v(\rho_{\pi,\lambda})^{\mathrm{F\text{-}ss}}
\simeq\iota_\lambda D(\pi_v), \tag{10.10}
$$

including its nilpotent operator. Then $\mathcal R(\pi)$ is strongly compatible. At every fixed $v$, its inertial type, monodromy rank, and conductor exponent are independent of $\lambda\nmid v$.

**Proof.** The algebraicity and coefficient-conjugation compatibility of the local correspondence define $D(\pi_v)$ over a finite extension of $E_\pi$. After one finite coefficient enlargement for the finitely many ramified places, (10.10) is exactly (4.12). Formula (4.9) gives common inertial type, the common operator gives monodromy rank, and (4.10) gives common conductor. $\square$

The hypothesis in (10.10) cannot be replaced by Theorem 10.1 or strong multiplicity one. Earlier geometric results prove (10.10) in their stated unramified and semistable regimes and at every further place for which a local comparison theorem has been established. If a realization supplies only those cases, the conclusion is strong compatibility only in that recorded range. Calling it strong at all places would silently add a theorem.

## 11. Local automorphic types in the system

### 11.1 Unramified and principal-series places

The abstract theorem becomes useful only after its local parameters can be read. At an unramified place $v$, let $\alpha_v,\beta_v$ be the algebraically normalized Satake roots. Then

$$
D(\pi_v)=
\left(
\begin{pmatrix}\alpha_v&0\\0&\beta_v\end{pmatrix},0
\right), \tag{11.1}
$$

where the displayed matrix is the value of $r$ on arithmetic Frobenius and inertia is trivial. The common polynomial is

$$
(X-\alpha_v)(X-\beta_v). \tag{11.2}
$$

This is full unramified compatibility: both inertia and Frobenius are identified.

Now suppose the local parameter is principal series,

$$
D(\pi_v)=(\theta_1\oplus\theta_2,0). \tag{11.3}
$$

The characters are viewed through arithmetic local reciprocity. At every $\lambda\nmid v$, their algebraic values are transported through $\iota_\lambda$. Strong compatibility gives

$$
\tau_v=\theta_1|_{I_v}\oplus\theta_2|_{I_v},\qquad
a_v=a_v(\theta_1)+a_v(\theta_2). \tag{11.4}
$$

If one character is unramified and the other ramified, the local Euler factor has degree one. If both are ramified, it can have degree zero. Neither degree determines the full type in (11.4).

At the normalized-induction reducibility boundary, the character-type and special constituents must be separated. The former has a two-character parameter of the form (11.3) and $N=0$; the latter has the same adjacent semisimple Weil characters but $N\ne0$. Because a finite local component of a cuspidal global $\operatorname{GL}_2$ representation is generic, the boundary constituent relevant here is the special constituent treated in Section 11.2. Calling it principal series would erase its monodromy.

### 11.2 Steinberg places

Suppose

$$
\pi_v\simeq\operatorname{St}\otimes\theta_v
$$

in the algebraic normalization. The common local parameter is

$$
D(\pi_v)=\operatorname{Sp}_2(\theta_v)
=\bigl(\theta_v\|\cdot\|_v\oplus\theta_v,N_v\bigr),
\qquad \operatorname{rank}N_v=1. \tag{11.5}
$$

When $\theta_v$ is unramified,

$$
a_v(D(\pi_v))=1,\qquad
\tau_v=1\oplus1. \tag{11.6}
$$

Thus trivial inertial type does not imply unramifiedness of the original representation. The exponential of $N_v$ produces nontrivial unipotent inertia. The invariant line is $\ker N_v$, and the local newvector eigenvalue records the unramified twist on the appropriate stable line.

When $\theta_v$ is ramified, the scalar inertial character appears twice and

$$
a_v(D(\pi_v))=2a_v(\theta_v). \tag{11.7}
$$

The formula is not $2a_v(\theta_v)+1$ because $V^{I_v}=0$, so the monodromy correction in (4.10) vanishes. This is a useful check against blindly adding the unramified Steinberg exponent.

In weight two, an elliptic curve with split multiplicative reduction has $\theta_v=1$; nonsplit multiplicative reduction has the unramified quadratic twist. Both have conductor exponent one and rank-one monodromy. On a chosen integral Tate lattice, their residual inertia can nevertheless become trivial at exceptional coefficient primes, because the integral extension parameter can vanish modulo $\lambda$.

### 11.3 Supercuspidal places and the comparison boundary

A supercuspidal local representation of $\operatorname{GL}_2(F_v)$ has an irreducible two-dimensional Weil representation and $N=0$:

$$
D(\pi_v)=(r_v,0). \tag{11.8}
$$

Its conductor is the Artin conductor of $r_v$, and its inertial type can have tame or wild finite image. In dihedral cases, $r_v$ is induced from a character of a quadratic extension of $F_v$; in primitive cases it is not. These distinctions are invisible in the good polynomials away from $v$.

If (10.10) is known, every $\lambda\nmid v$ realizes the same $r_v$ through its coefficient embedding. In particular, wild breaks, Swan conductor, and finite inertia character are independent of $\lambda$. If the geometric construction proves only finite ramification at $v$, one may not import the automorphic conductor merely because $\pi_v$ is known. The equality is the content of local--global compatibility.

The same caution applies to a quaternionic realization. A one-dimensional norm character on a division algebra can transfer to an unramified Steinberg twist on the split group. The split-side conductor rises from zero in the division newvector convention to one because $N$ appears. A higher-dimensional division representation transfers to a discrete series, often supercuspidal. The local parameter, rather than the superficial dimension of a fixed-vector space, controls the Galois conductor.

### 11.4 Central characters and reciprocity audit

The determinant of $D(\pi_v)$ must equal the algebraic local central character in the same normalization as (10.6). At an unramified good place,

$$
\alpha_v\beta_v=\psi_\pi(v)q_v^{w+1}. \tag{11.9}
$$

At a Steinberg place, (11.5) gives

$$
\det r_v=\theta_v^2\|\cdot\|_v. \tag{11.10}
$$

Since $\|\operatorname{Frob}_v\|_v=q_v$, this matches the covariant cyclotomic direction. Replacing arithmetic by geometric Frobenius would invert every unramified value and require changing (4.1), (11.1), and (11.10) simultaneously.

Four tests expose normalization errors.

1. In weight two with trivial finite central character, the good determinant is $q_v$.
2. A finite-order twist multiplies the determinant by the square of its value.
3. A Tate twist by $(r)$ multiplies a rank-two determinant by $q_v^{2r}$.
4. In $\operatorname{Sp}_2(\theta)$, the two Frobenius eigenvalues differ by the factor $q_v$ forced by (4.3).

A formula passing only one of these tests is not reliable. Central character, Frobenius direction, covariance, and Tate twist form one normalization ledger.

## 12. Systems from elliptic curves and abelian varieties

### 12.1 The elliptic-curve system

Geometry supplies the most concrete compatible system. Let $A/F$ be an elliptic curve. For every rational prime $\ell$, put

$$
V_\ell(A)=T_\ell(A)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell. \tag{12.1}
$$

The semisimplicity theorem for rational Tate modules of abelian varieties over number fields supplies the semisimplicity required in Section 3.1. This is a genuine input. Without it, the good Frobenius polynomials would still define a compatible collection, but the collection would meet our definition only after taking global semisimplifications, and the original geometric lattices would have to be retained separately.

The coefficient field is $\mathbf Q$, so there is one coefficient place for every $\ell$. Let $S_A$ be the finite set of bad-reduction places. At $v\notin S_A$ and $v\nmid\ell$, good reduction gives unramifiedness and

$$
P_{A,v}(X)=X^2-a_v(A)X+q_v,\qquad
a_v(A)=q_v+1-\#A(k_v). \tag{12.2}
$$

The integer polynomial (12.2) is independent of $\ell$. The Weil pairing gives

$$
\det V_\ell(A)=\chi_\ell,\qquad
V_\ell(A)^\vee\simeq V_\ell(A)(-1). \tag{12.3}
$$

At a real place, complex conjugation has eigenvalues $1,-1$. The system is pure of weight one by the Weil bounds.

At a place $u\mid\ell$ of good reduction, $V_\ell(A)$ is crystalline with labelled weights $\{0,1\}$, and the canonical lattice $T_\ell(A)$ has finite-flat quotients $A[\ell^n]$. At semistable reduction it is semistable; at multiplicative reduction its monodromy has rank one.

For elliptic curves, the local reduction classification and the Tate-curve description give strong compatibility away from coefficient primes. At good places $N=0$. At multiplicative places the parameter is the split or nonsplit unramified twist of $\operatorname{Sp}_2(1)$. An additive potentially multiplicative place is described by the corresponding ramified quadratic twist of this special parameter. At potentially good additive places the finite inertial representation is determined by the corresponding geometric action, with wild qualifications in residue characteristics $2$ and $3$. One still proves these statements from the curve's local geometry; weak compatibility alone would not suffice.

### 12.2 A worked elliptic-curve diagnostic

Consider

$$
A:\quad y^2+y=x^3-x^2-10x-20. \tag{12.4}
$$

Its discriminant is $-11^5$ and its conductor is $11$. At every $p\ne11,\ell$,

$$
\det(X-\rho_{A,\ell}(\operatorname{Frob}_p))
=X^2-a_pX+p. \tag{12.5}
$$

At $p=2$, both values $x=0,1$ give two solutions of $y^2+y=0$, and the point at infinity supplies a fifth point. Hence

$$
\#A(\mathbf F_2)=5,\qquad a_2=-2,\qquad
P_{A,2}(X)=X^2+2X+2. \tag{12.6}
$$

Every coefficient prime $\ell\ne2$ reads this same polynomial in $\mathbf Q_\ell[X]$, including $\ell=11$. Its roots have complex absolute value $\sqrt2$, its determinant audits the cyclotomic convention, and its reduction modulo $\ell$ gives the residual Frobenius polynomial.

At $11$, the curve has multiplicative reduction. For every $\ell\ne11$, the characteristic-zero local parameter has rank-one monodromy and conductor exponent one. This conclusion is independent of $\ell$. It is not obtained from (12.6), nor from the good polynomials at all $p\ne11$ by a local calculation; it comes from Tate uniformization. Here the minimal-discriminant thickness is $5$, so among $\ell\ne11$ the unipotent inertia on the reduced geometric Tate lattice disappears exactly at $\ell=5$. The characteristic-zero conductor remains one there, illustrating the difference between characteristic-zero and integral residual conductor.

At $u=\ell$ where the curve has good reduction, $V_\ell(A)$ is crystalline rather than generally unramified. Its weights are $\{0,1\}$ and $A[\ell^n]$ is finite flat. This single example therefore tests all three compatibility layers.

### 12.3 Abelian varieties and coefficient factors

Let $B/F$ be an abelian variety of dimension $g$. The full Tate module gives a rank-$2g$ system

$$
\{V_\ell(B)\}_\ell. \tag{12.7}
$$

At a good $v\nmid\ell$, the common polynomial

$$
P_{B,v}(X)=
\det(X-\operatorname{Frob}_v\mid V_\ell(B))
\in\mathbf Z[X] \tag{12.8}
$$

is determined by the zeta function of the reduction and is independent of $\ell$. It is pure of weight one. A polarization gives a symplectic similitude pairing with multiplier $\chi_\ell$, so

$$
\det V_\ell(B)=\chi_\ell^g. \tag{12.9}
$$

At a good coefficient-prime place the labelled weights consist of $g$ zeros and $g$ ones.

Suppose a number field $M$ acts on $B$ through $F$-rational endomorphisms. To obtain a rank-two $M$-coefficient system, assume that the $M\otimes\mathbf Q_\ell$-linear Tate module has rank two for every $\ell$ and that, at every good $v$, its $M$-linear Frobenius characteristic polynomial is one polynomial

$$
Q_{B,v}(X)\in M[X] \tag{12.9a}
$$

independent of $\ell$. Then $g=[M:\mathbf Q]$, a place $\lambda\mid\ell$ of $M$ cuts out a rank-two factor $V_\lambda(B)$ with polynomial $\iota_\lambda Q_{B,v}$, and

$$
P_{B,v}(X)=
\prod_{\tau:M\hookrightarrow\overline{\mathbf Q}}
\tau Q_{B,v}(X). \tag{12.9b}
$$

It is not enough to choose an unrelated quadratic factor of (12.8) separately at each $\ell$.

Likewise, (12.9) determines only the product of the determinants of the coefficient factors. A cyclotomic determinant and polarization on each rank-two factor require the $M$-action to be compatible with the polarization, together with the corresponding rank-one determinant identification. In the Hilbert--Blumenthal setting this is part of the real-multiplication and polarization datum; it does not follow from an arbitrary $M$-action.

The coefficient idempotent must be integral if one wants a corresponding finite-flat lattice. A rational idempotent gives a rational factor, but denominators divisible by $\lambda$ can prevent its intersection with $T_\ell(B)$ from being a direct summand. Thus

$$
\text{rational coefficient factor}
\not\Longrightarrow
\text{integral finite-flat coefficient factor}. \tag{12.10}
$$

When the coefficient order acts integrally and the $\lambda$-primary kernel is finite flat, the factors defined by the common polynomials $Q_{B,v}$ also carry the required integral models. This is the geometric model used in two-prime potential-modularity arguments.

### 12.4 Comparison with an automorphic system

Suppose the elliptic curve or coefficient factor is known to be associated with a regular algebraic cuspidal automorphic representation $\pi$. At almost every $v$ its geometric polynomial equals $P_{\pi,v}$. For each fixed $\lambda$, Chebotarev gives

$$
V_\lambda(B)^{\mathrm{ss}}\simeq
\rho_{\pi,\lambda}^{\mathrm{ss}} \tag{12.11}

$$

after embedding both coefficient fields into a common local field. If the representations are irreducible, the semisimplification signs may be removed.

Equation (12.11) identifies the global rational representations. It does not identify a chosen geometric lattice with a chosen cohomological lattice. Nor does its proof compare bad local parameters directly. Once the representations are globally isomorphic, their actual restrictions to $G_{F_v}$ are isomorphic, so a local property proved on one side transfers to the other. But if one starts only with a semisimplified identity, local extension data and integral models remain outside the conclusion.

When both sides have proved strong local compatibility, their common Weil--Deligne parameters agree with $D(\pi_v)$ at every $v\nmid\lambda$. This is a consistency theorem among geometry, automorphic local correspondence, and Chebotarev. The local comparison input cannot be deleted merely because the good-prime comparison is dense.

## 13. Conditional potential automorphy and the downstream boundary

### 13.1 What potential automorphy actually gives

Assume a representation $\rho:G_F\to\operatorname{GL}_2(L)$ satisfies a named
potential-automorphy theorem, including all of that theorem's residual-image, determinant,
Hodge, local-component, and field-avoidance hypotheses. Its usable output has the form

$$
\rho|_{G_{F'}}\otimes C\simeq \rho_{\Pi,\lambda'}\otimes C,
\tag{13.1}
$$

where $F'/F$ is finite, $\Pi$ is an automorphic packet over $F'$, and $C$ aligns the local
coefficient fields. Book 168 then attaches the coefficient-indexed packet system
$\{\rho_{\Pi,\nu}\}_\nu$ over $F'$. The system has the common good polynomials, determinant,
purity, Hodge data, and local pairs in Book 168's proved range.

This is a conditional interface, not a new potential-automorphy theorem. A residual congruence
alone does not identify a prescribed characteristic-zero lift with (13.1), and the hypotheses
of the chosen lifting theorem must remain attached to the conclusion.

### 13.2 Why this does not descend the family

Equation (13.1) selects one member after restriction. It does not construct representations of
$G_F$ at the other coefficient places. Even when $F'/F$ is Galois and every restricted member
is invariant up to isomorphism, intertwiners can carry a nontrivial Clifford factor set; a
virtual Brauer identity can also have negative multiplicities; and an effective constituent
over an algebraic closure can still have a coefficient-field Schur obstruction.

Those are not gaps in the definition of compatibility. They are separate descent problems.
The reusable integral Brauer, Clifford, norm-one, and coefficient-descent mechanisms are kept in
Book 180. This volume uses none of them as a premise.

### 13.3 Downstream producers

Books 183--185 implement one controlled application of that toolkit. Book 183 constructs the
SP elementary-packet array and proves its nonnormal overlap identities. Book 184 verifies the
application-specific Gram matrix and norm-one positivity. Book 185 kills the remaining
coefficient obstruction and assembles the actual base-field family, including restriction
recovery, purity, and the proved SP local record.

Thus a downstream theorem may feed an already assembled family back into Chapters 14--18 for
coefficient operations or prime switching. It may not be read backward as a prerequisite for
the definitions, uniqueness results, image wrapper, or switching theorem proved here.

## 14. Coefficient descent and conjugate systems

### 14.1 Trace fields and enlargement

The natural coefficient field of an automorphic system is generated by the algebraically normalized good Hecke data. Let

$$
E_\pi^{\mathrm{rat}}
=\mathbf Q\bigl(a_v(\pi),\psi_\pi(v):v\notin S_\pi\bigr). \tag{14.1}
$$

Strong multiplicity one shows that these data determine the automorphic representation, but it does not say that every cohomological projector or local type is defined over exactly (14.1). A finite field of definition $E_\pi$ may be larger.

Enlarging $E_\pi$ preserves every common polynomial, local parameter, determinant, Hodge label, and purity assertion. It can split endomorphism algebras and make local types rational. It also refines coefficient places: one old place may have several extensions. Nothing arithmetic is lost, but statements about the exact residue field or full residual image can change and must be rephrased after enlargement.

A minimal coefficient field is useful for image theorems because inner twists can force the image to be defined over a proper subfield. It is not necessary for the existence of the compatible system. Correctness takes priority over minimizing coefficients.

### 14.2 Galois conjugates

Let $\sigma:E\hookrightarrow\overline{\mathbf Q}$ be an embedding. Apply $\sigma$ to every common polynomial:

$$
P_v^\sigma(X)=\sigma(P_v(X)). \tag{14.2}
$$

If $\mathcal R$ comes from $\pi$, these are the polynomials of the conjugate automorphic representation $\pi^\sigma$. For compatible coefficient places, scalar conjugation gives

$$
{}^\sigma\rho_{\pi,\lambda}^{\mathrm{ss}}
\simeq
\rho_{\pi^\sigma,\sigma\lambda}^{\mathrm{ss}}. \tag{14.3}
$$

The left side means transport of scalar structure through the chosen isomorphism of completions. It is not entrywise application of $\sigma$ to arbitrary $\ell$-adic numbers.

Strong local parameters conjugate in the same way:

$$
D(\pi_v)^\sigma=D(\pi_v^\sigma). \tag{14.4}
$$

Hodge labels are transported together with the embedding of $F$. Purity is invariant because (6.1) already quantifies over every complex embedding.

Field conjugation on the base is different. If $F'/F$ is Galois and $g\in\operatorname{Gal}(F'/F)$, conjugating a representation of $G_{F'}$ changes the subgroup argument. Coefficient conjugation changes scalars. In CM induction the two operations can interact, but they are never the same definition.

### 14.3 Descent of coefficients

Let $E/E_0$ be finite Galois. A coefficient descent of a semisimple system requires isomorphisms

$$
c_\sigma:{}^\sigma\mathcal R\xrightarrow{\sim}\mathcal R
\qquad(\sigma\in\operatorname{Gal}(E/E_0)) \tag{14.5}
$$

satisfying

$$
c_{\sigma\tau}=c_\sigma\,{}^\sigma c_\tau. \tag{14.6}
$$

If all common polynomials lie in $E_0$, Chebotarev supplies memberwise isomorphisms like (14.5) after scalar extension. It does not choose them or prove (14.6). For an absolutely irreducible member, two choices differ by a scalar, so the obstruction to (14.6) is a scalar $2$-cocycle. Its vanishing gives an $E_{0,\lambda_0}$-model.

When residual absolute irreducibility is available, integral descent is often more rigid, but a stable lattice still has to be preserved. Descending a rational representation and descending its chosen finite-flat model are separate problems. The latter requires integral descent data, not only generic isomorphisms.

Thus the correct descent principle is:

$$
\text{traces in }E_0
+\text{vanishing descent obstruction}
\Longrightarrow
\text{an }E_0\text{-valued system}. \tag{14.7}
$$

The first summand alone is insufficient.

### 14.4 Inner twists and the true rationality field

An **inner twist** of a rank-two system is a pair $(\sigma,\eta)$, with $\sigma$ a coefficient automorphism and $\eta$ a compatible finite-order character, such that

$$
{}^\sigma\rho_\lambda\simeq
\rho_{\sigma\lambda}\otimes\eta_{\sigma\lambda}. \tag{14.8}
$$

At good places this says

$$
\sigma(a_v)=\eta(v)a_v,\qquad
\sigma(d_v)=\eta(v)^2d_v. \tag{14.9}
$$

The subgroup of coefficient automorphisms occurring in inner twists fixes a field often smaller than the Hecke field. Large-image theorems naturally see this inner-twist field: residual images may contain $\operatorname{SL}_2$ over the residue field of that smaller field rather than over all of $k_\lambda$.

A quadratic CM self-twist is the central example. If

$$
\rho_\lambda\simeq\rho_\lambda\otimes\eta_{M/F}
$$

for every $\lambda$, the system is induced from the quadratic field $M$ under the usual irreducibility hypotheses. Such a self-twist controls cuspidality under base change and forces projective images into Cartan normalizers. Treating it as a harmless coefficient symmetry would produce false large-image conclusions.

## 15. What is genuinely independent of the coefficient prime

### 15.1 Uniform invariants in a strong system

The phrase “independent of $\ell$” is useful only when its quantifiers are visible. Fix a strong compatible system $\mathcal R$ over $F$ with coefficients in $E$. There are three kinds of assertion.

An invariant can be uniform for every coefficient place $\lambda$ for which it is defined. The determinant character and common good polynomials have this form. An invariant at a fixed base place $v$ can be uniform for every $\lambda\nmid v$; Weil--Deligne data have this form. A residual property can hold on a density-one set or outside a finite exceptional set; this requires an image theorem.

For every $v\notin S$ and every $\lambda\nmid v$, the following are literally the scalar images of one algebraic record:

$$
P_v(X),\qquad a_v,\qquad d_v. \tag{15.1}
$$

For every fixed finite $v$, strong compatibility gives one pair

$$
D_v=(r_v,N_v) \tag{15.2}
$$

whose scalar extensions describe all $\lambda\nmid v$. Consequently every invariant functorially determined by this pair is independent of $\lambda$ in that range.

This does not compare $D_v$ with a representation whose coefficient characteristic equals the residue characteristic of $v$. At that coefficient place, the relevant object is a filtered period module. A theorem relating its semistable parameter to (15.2) is an additional local compatibility statement.

### 15.2 Conductor, type, and monodromy

Fix $v$ of residue characteristic $p$. For every $\lambda\nmid p$, (15.2) gives

$$
\begin{aligned}
\tau_v(\rho_\lambda)&=r_v|_{I_v},\\
\operatorname{rank}N(\rho_\lambda)&=\operatorname{rank}N_v,\\
a_v(\rho_\lambda)&=a_v(r_v,N_v).
\end{aligned} \tag{15.3}
$$

Thus the prime-to-coefficient conductor ideal

$$
\mathfrak N(\mathcal R)=
\prod_v v^{a_v(r_v,N_v)} \tag{15.4}
$$

is well defined when the strong local parameters exist at every finite $v$. For a fixed member $\rho_\lambda$, the factor at $v\mid\ell(\lambda)$ is not computed from (15.2); one either omits it from the prime-to-$\ell$ conductor or uses the coefficient-prime local theory.

Frobenius-semisimplification in (15.2) does not undermine the conclusion about $N$, because $N_v$ is retained. If only $r_v^{\mathrm{ss}}$ were common, neither monodromy rank nor the correction term in (4.10) would follow. This is precisely why the definition of strong compatibility used a pair.

Residual conductor is not included in (15.3). Reduction can merge finite inertia characters or kill an integral monodromy class. Outside finitely many coefficient primes certified by a fixed integral model, these collapses disappear, but the finite exceptional set depends on the local integral data.

### 15.3 Hodge data, determinant, and purity

Suppose the system is Hodge compatible with labelled datum $H_{\tau_0}$. Then for every $\lambda$ and every coefficient-prime place, (5.8) identifies the labelled Hodge--Tate multiset. This is an all-$\lambda$ conclusion within the range of the coefficient-prime comparison theorem.

Crystalline or semistable behavior can also be uniform when it comes from a uniform geometric or automorphic theorem. The precise statement is normally:

$$
\rho_\lambda|_{G_{F_u}}
\text{ is crystalline for every }u\mid\ell(\lambda)
\text{ outside a fixed geometric bad set}. \tag{15.5}
$$

It is not a statement that the inertia groups at different rational primes are identified.

The determinant is independent in the stronger character sense:

$$
\det\rho_\lambda=\psi_\lambda\chi_{\ell(\lambda)}^m \tag{15.6}
$$

for every $\lambda$. Its Hodge weight is $m$ at every label on which $\psi$ is finite order. Purity of weight $m$ means that the common good roots satisfy (6.1); once proved, it is automatically read by every member because the roots are algebraic before completion.

These conclusions still require hypotheses. An arbitrary weak system need not be de Rham. An algebraic determinant does not force purity. A geometric origin must be accompanied by the relevant comparison and weight theorem rather than used as a slogan.

### 15.4 Density-one and finite-exception conclusions

Residual conclusions come in two common strengths.

A general semisimple compatible system with connected algebraic monodromy may have a density-one set of coefficient places at which the residual monodromy is as large as predicted. Such a theorem permits an exceptional set of density zero that can still be infinite. It should not be paraphrased as “all sufficiently large primes.”

For rank-two systems arising from a non-CM regular algebraic cuspidal representation, a stronger open-image theorem can give a finite-exception result. Under the hypotheses made precise in the next chapter, residual members are absolutely irreducible and adequate for all but finitely many $\lambda$.

There is also an elementary finite-exception principle for preserving one fixed algebraic distinction. If $x,y\in\mathcal O_E$ and $x\ne y$, then

$$
x\not\equiv y\pmod\lambda \tag{15.7}
$$

for all but finitely many $\lambda$. Thus one Frobenius element certifying that two algebraic characters differ continues to certify their residual difference outside finitely many primes. Similarly, a fixed nonzero minor certifying monodromy rank remains nonzero outside finitely many primes once one uniform algebraic integral model has been fixed.

This principle does not prove global residual irreducibility for a general system: a reducible residual representation need not be exposed by one preselected Frobenius polynomial. A large-image or irreducibility theorem supplies the missing uniform global argument.

No stronger quantifier is implicit. It is often conjectured that additional invariants or image properties are uniform at every sufficiently large coefficient prime, but a density-one theorem leaves open an infinite exceptional set, and a fixed-place strong-compatibility theorem says nothing at the moving places $v\mid\ell(\lambda)$. In particular, this chapter has not proved residual irreducibility for every $\lambda$, equality of residual conductors for every $\lambda$, or an all-$\lambda$ comparison between $D_v$ and coefficient-prime period data.

## 16. Residual image, adequacy, and the CM boundary

### 16.1 Why compatibility alone gives no large image

Common Frobenius polynomials constrain traces and determinants but permit radically different image sizes. A system of two characters is compatible and reducible at every coefficient prime. A dihedral system can be irreducible while its projective image lies in the normalizer of a Cartan for every $\lambda$. A finite-image Artin system can have uniformly bounded image. None contains large special linear groups.

Throughout this chapter $\bar\rho_\lambda$ means the canonical semisimplified residual member. Once it is absolutely irreducible, every stable-lattice reduction is isomorphic to it, so image language is then unambiguous up to conjugacy.

Large image therefore begins with structural hypotheses. For a rank-two automorphic system, the decisive exclusion is the CM or dihedral case, equivalently automorphic induction from a quadratic character in the regular algebraic setting. One must also account for inner twists: they can make the natural field over which the derived image is large smaller than the displayed coefficient field.

Let $E^{\mathrm{it}}\subseteq E$ be the field fixed by the coefficient automorphisms occurring in inner twists. For a place $\lambda$ of $E$, let $\lambda_0$ be its restriction to $E^{\mathrm{it}}$ and let $k_{\lambda_0}$ be the corresponding residue field. The honest large-image conclusion generally concerns

$$
\operatorname{SL}_2(k_{\lambda_0}) \tag{16.1}
$$

inside the residual image after a choice of coordinates, not necessarily $\operatorname{SL}_2(k_\lambda)$.

### 16.2 The finite-exception large-image wrapper

The group theory is imported from Book 141 rather than reproved here. The compatible-system
input needed to apply it can be stated cleanly.

**Theorem 16.1 (finite-exception large-image wrapper).** Let $F$ be totally real and let
$\mathcal R(\pi)$ be a strongly compatible rank-two system attached to a regular algebraic
cuspidal packet. Assume:

1. the system is not dihedral, equivalently the packet is not automorphically induced from a
   character of a quadratic extension;
2. all finite-order self-twists have been absorbed into the inner-twist field
   $E^{\mathrm{it}}$;
3. the characteristic-zero derived monodromy group is the expected $\operatorname{SL}_2$ after
   restriction of scalars from $E^{\mathrm{it}}$; and
4. an integral specialization theorem bounds the conductors of residual Cartan-normalizer
   characters and identifies the residual projective trace field with
   $k_{\lambda_0}$, where $\lambda_0=\lambda|_{E^{\mathrm{it}}}$.

Then outside a finite set of coefficient places, $\bar\rho_\lambda$ is absolutely irreducible
and its image contains a conjugate of

$$
\operatorname{SL}_2(k_{\lambda_0}). \tag{16.2}
$$

**Justification.** Book 141 reduces a finite subgroup of $\operatorname{PGL}_2$ to the Borel,
Cartan-normalizer, bounded exceptional, or subfield special-linear cases. Hypothesis 3 plus
integral specialization excludes the Borel and bounded exceptional loci outside finitely many
places. Hypotheses 1, 2, and the conductor bound in hypothesis 4 turn infinitely many
Cartan-normalizer occurrences into one characteristic-zero quadratic self-twist, a
contradiction. The projective-trace-field clause then identifies the field in the remaining
special-linear case. This is exactly the Book 141 classification/adequacy input combined with
the family-specific integral specialization input; compatibility alone proves neither part.

The conclusion concerns the inner-twist residue field, not automatically the full displayed
$k_\lambda$, and the determinant can still restrict the full image. The theorem is therefore a
wrapper: every application must separately cite or assume the integral specialization and
moving-prime conductor statements in clause 4.

### 16.3 Adequacy outside a finite set

Adequacy is the image condition used by global deformation theory. In dimension two, a convenient sufficient criterion is that the residual image contain $\operatorname{SL}_2(k_0)$ for a finite field $k_0$ of characteristic $\ell>5$, with the representation absolutely irreducible. The small characteristics and a short list of small projective images are excluded because their adjoint cohomology can have exceptional classes.

**Corollary 16.2 (finite-exception adequacy).** Under Theorem 16.1, enlarge $B_{\mathrm{img}}$ to contain all places of residue characteristic at most $5$ and the finitely many coefficient and determinant exceptions. Then

$$
\bar\rho_\lambda(G_F)
\text{ is adequate} \tag{16.4}
$$

for every $\lambda\notin B_{\mathrm{img}}$.

**Proof.** The group-theoretic adequacy criterion for two-dimensional representations says that an absolutely irreducible subgroup containing $\operatorname{SL}_2(k_0)$ is adequate when $\operatorname{char}k_0>5$. Theorem 16.1 supplies precisely this containment with $k_0=k_{\lambda_0}$. $\square$

The conservative bound $\ell>5$ avoids small-image casework. A sharper application may inspect $\ell=3$ or $5$ directly. It may not simply call those primes adequate because all larger primes are.

### 16.4 CM and dihedral systems

Let $M/F$ be quadratic and let $\Theta=\{\theta_\lambda\}$ be a compatible character system of $G_M$. Put

$$
\rho_\lambda=\operatorname{Ind}_{G_M}^{G_F}\theta_\lambda. \tag{16.5}
$$

Then

$$
\rho_\lambda|_{G_M}\simeq
\theta_\lambda\oplus\theta_\lambda^\sigma, \tag{16.6}
$$

and

$$
\rho_\lambda\otimes\eta_{M/F,\lambda}\simeq\rho_\lambda. \tag{16.7}
$$

The system is irreducible over $F$ precisely when $\theta_\lambda\ne\theta_\lambda^\sigma$. If the algebraic characters differ, choose a good prime $w$ at which their values differ. Their reductions remain different outside the finitely many $\lambda$ dividing that nonzero difference. Therefore

$$
\bar\rho_\lambda\text{ is absolutely irreducible for all but finitely many }\lambda \tag{16.8}
$$

over the original field $F$. After a base change $L/F$, the corresponding conclusion requires both that $ML/L$ remain quadratic and that the restrictions of the two conjugate algebraic characters to $G_{ML}$ remain distinct. Disjointness from $M$ alone does not imply the second condition for an arbitrary character system, although distinct regular Hodge labels often do. Both conditions must be checked again.

The projective image in (16.8) is nevertheless dihedral: it lies in the normalizer of a Cartan and generally not in the Cartan. It never contains the large special linear groups of Theorem 16.1 for sufficiently large residue fields. At an exceptional $\lambda$ where

$$
\bar\theta_\lambda=\bar\theta_\lambda^\sigma, \tag{16.9}
$$

the residual semisimplification becomes a sum of two extensions of a character from $G_M$ to $G_F$, after residue-field enlargement. In characteristic two those two extensions can coincide and nonsplit self-extensions can occur before semisimplification.

After restriction to $G_M$, every member is reducible by (16.6), in characteristic zero and residually. More generally, after base change the system can remain irreducible only while the quadratic induction remains nontrivial and its two restricted inducing characters remain distinct. Thus “CM systems are residually irreducible for almost all primes” must always name the base field and verify both conditions.

Some irreducible dihedral residual images can be adequate when their orders and residual characteristic satisfy the adequacy criterion. They are not large in the sense of containing $\operatorname{SL}_2$, and adequacy must be checked rather than inferred from the non-CM theorem.

### 16.5 A worked CM diagnostic

Let $M/F$ be a CM quadratic extension of a totally real field and let $\theta$ be a regular algebraic Hecke character with $\theta\ne\theta^\sigma$. The automorphic induction

$$
\pi=\operatorname{AI}_{M/F}(\theta) \tag{16.10}
$$

is cuspidal and gives the system (16.5). At a good split prime $v=ww^\sigma$,

$$
P_v(X)=
\bigl(X-\theta(\operatorname{Frob}_w)\bigr)
\bigl(X-\theta^\sigma(\operatorname{Frob}_w)\bigr). \tag{16.11}
$$

At a good inert prime, with unique $w$ and residue degree two,

$$
P_v(X)=X^2-\theta(\operatorname{Frob}_w). \tag{16.12}
$$

The trace is zero, and the determinant sign comes from $\eta_{M/F}(\operatorname{Frob}_v)=-1$. Equations (16.11)--(16.12) exhibit the self-twist: multiplying traces by $\eta_{M/F}(v)$ changes nothing.

Choose a split $w$ for which $\theta(\operatorname{Frob}_w)\ne\theta^\sigma(\operatorname{Frob}_w)$. Outside finitely many $\lambda$, the two residual characters differ and the induction is irreducible. Yet restriction to $G_M$ is always the sum in (16.6). This diagnostic simultaneously catches three false claims: irreducibility need not survive restriction, almost-all residual irreducibility does not imply non-CM large image, and a quadratic self-twist can destroy cuspidality after base change to its defining field.

## 17. Solvable base change, descent, and self-twists

This chapter is an interface, not an additional transfer theorem. Every automorphic assertion
below is conditional on a named base-change, descent, or automorphic-induction theorem whose
cuspidality, selector, and local-compatibility hypotheses have been verified.

### 17.1 Ascent of a compatible system

If an available solvable base-change theorem constructs
$\Pi=\operatorname{BC}_{L/F}(\pi)$, its expected local interface is

$$
D(\Pi_w)=D(\pi_v)|_{W_{L_w}}, \tag{17.1}
$$

with the same monodromy operator, and

$$
\omega_\Pi=\omega_\pi\circ N_{L/F}. \tag{17.2}
$$

On the Galois side this is ordinary restriction of the compatible system. At unramified places,
Frobenius roots are raised to the residue degree; at ramified places, the full Weil--Deligne
pair must be restricted. The interface does not infer the conductor by extending an ideal and
does not enlarge the proved local range of the attachment theorem.

### 17.2 Cuspidality and its first failure

A solvable base change may be isobaric rather than cuspidal. At a quadratic layer with quotient
character $\eta$, the warning signal is the self-twist

$$
\pi_i\simeq\pi_i\otimes\eta. \tag{17.3}
$$

In the induced case the next restriction splits into the two conjugate characters. The check is
stepwise: a self-twist can first appear over an intermediate field even when none is visible at
the bottom. This criterion is recorded here only to audit whether a supplied automorphic
interface remains in the cuspidal rank-two range.

### 17.3 Descent with a compatible arithmetic extension

Suppose a descent theorem is available along a solvable tower and a representation
$r:G_F\to\operatorname{GL}_2(\overline{\mathbf Q}_\ell)$ already extends the selected
irreducible top member. Then $r$ selects the quotient twist at each cyclic layer. The desired
interface is

$$
\operatorname{BC}_{L/F}(\pi)\simeq\Pi_L,\qquad
\rho_{\pi,\ell}^{\mathrm{ss}}\simeq r. \tag{17.4}
$$

The extension $r$ is essential data, not a consequence of invariant traces. Without it, a
Clifford factor set and a torsor of quotient twists remain. Book 180 develops that general
obstruction theory for downstream descent arguments; it is not used as a premise here. Once a
bottom automorphic packet has actually been constructed, Book 168 attaches its coefficient
system and the generic calculus of this book applies.

### 17.4 Automorphic induction in a solvable diagram

A supplied automorphic-induction theorem must match the Galois induction and its local Mackey
formula. If a quadratic inducing field becomes contained in the base-change field, the induced
rank-two object splits; in a disjoint compositum it remains a quadratic induction precisely
when the conjugate characters remain distinct.

Dimension is the decisive audit. Induction of a character across a degree-$d$ extension has
rank $d$, while induction of a rank-two system has rank $2d$. Solvable base change does not by
itself provide the corresponding higher-rank automorphic induction. No interchange of
$\operatorname{BC}$ and $\operatorname{AI}$ is asserted without the required local-parameter
theorem.

### 17.5 Descent beyond solvable towers

For a nonsolvable top, inducing one rank-two member has the wrong dimension. The general Brauer,
Clifford, norm-one, and coefficient-descent mechanisms belong to Book 180. Books 183--185 are a
downstream SP application: they build the elementary packet diagram, verify every intersection
and Gram entry, prove effectivity, descend coefficients, and recover one base-field compatible
system with its local record.

This book imports none of those conclusions. Its role begins again once an honest base-field
system has been produced: coefficient operations, inner-twist bookkeeping, the large-image
wrapper, and the switching theorem can then be applied to that system.

## 18. Changing the coefficient prime

### 18.1 What compatibility supplies

Suppose a rank-two system contains a modular member at a place $\lambda\mid\ell$, and one wants to work at a place $\nu\mid q$ with $q\ne\ell$. The first step is to list what the system itself supplies.

Weak compatibility supplies a continuous semisimple representation

$$
\rho_\nu:G_F\longrightarrow\operatorname{GL}_2(E_\nu) \tag{18.1}
$$

and the same algebraic polynomials $P_v(X)$ at every $v$ away from the common bad set and from $q$. It also supplies the compatible determinant if that character was included in the system. Purity follows if it was proved for the algebraic polynomials.

Strong compatibility supplies, at every fixed $v\nmid q$,

$$
\operatorname{WD}_v(\rho_\nu)^{\mathrm{F\text{-}ss}}
\simeq\iota_\nu D_v. \tag{18.2}

$$

Thus characteristic-zero conductor, inertial type, and monodromy at $v$ survive the change. In particular, a place above the old prime $\ell$ is now away from the new coefficient prime and is governed by (18.2), provided the system is strong there.

This last statement does not by itself identify $D_v$ with the filtered semistable or crystalline module of the old $\lambda$-adic member when $v\mid\ell$. Strong compatibility compares $D_v$ only with members whose coefficient characteristic differs from that of $v$. To transfer a local property known only from the old coefficient-prime member, one additionally needs a comparison between its period-module parameter and $D_v$, or an independently specified common local datum.

Hodge compatibility supplies the labelled weights at places above $q$. A uniform coefficient-prime theorem can supply crystalline or semistable behavior there. It does not identify the $q$-adic representation with an $\ell$-adic tensor product, and it does not automatically supply a finite-flat lattice.

Compatibility alone gives no assertion about $\bar\rho_\nu$. Its reducibility, adequacy, and residual ramification must be established by additional arguments.

### 18.2 What Chebotarev adds

Assume the $\lambda$-adic member is automorphic:

$$
\rho_\lambda^{\mathrm{ss}}\simeq
\rho_{\pi,\lambda}^{\mathrm{ss}} \tag{18.3}

$$

for a regular algebraic cuspidal $\pi$, after placing the coefficient fields in one local field. At almost every $v$, (18.3) identifies the common polynomial $P_v$ with $P_{\pi,v}$. Hence, at the new coefficient place,

$$
\det(X-\rho_\nu(\operatorname{Frob}_v))
=P_{\pi,v}(X) \tag{18.4}
$$

for almost every $v\nmid q$. Chebotarev gives

$$
\rho_\nu^{\mathrm{ss}}\simeq
\rho_{\pi,\nu}^{\mathrm{ss}} \tag{18.5}

$$

after a common coefficient extension.

Thus one automorphic member makes every member automorphic after semisimplification, provided the system and the automorphic family are both defined at the new place with aligned coefficient embeddings. If $\rho_\nu$ is irreducible, the superscript can be removed.

Chebotarev adds uniqueness, not local comparison. Equation (18.5) identifies actual semisimple global representations, so any local property already proved for one side transfers. But if the automorphic construction at $v$ is known only through a predicted local parameter rather than a proved one, Chebotarev does not supply the missing theorem. It also says nothing about chosen lattices.

### 18.3 What a large-image theorem adds

Under the non-CM hypotheses of Theorem 16.1, there is a finite exceptional set $B_{\mathrm{img}}$ such that

$$
\bar\rho_\nu\text{ is absolutely irreducible and adequate}
\qquad(\nu\notin B_{\mathrm{img}}), \tag{18.6}
$$

after the small residue characteristics are excluded. This is exactly the input needed to use a residual member in a modularity-lifting or deformation argument.

The theorem does not choose a particular rational prime $q$ inside the finite exceptional set. A changing-prime argument is free to choose $q$ only after excluding the rational primes below $B_{\mathrm{img}}$. If an application insists on $q=3$ or $5$, adequacy and irreducibility require a direct calculation or a theorem tailored to that small image.

In the CM case, Theorem 16.1 is unavailable. The explicit induction criterion (16.9) decides residual irreducibility, and the projective image remains dihedral. One may still change primes, but every later theorem must accept that image or verify adequacy directly.

### 18.4 Controlling local and residual behavior

Fix a finite set $T$ of base-field places. Characteristic-zero local behavior at $v\in T$ is controlled by strong compatibility whenever $v\nmid q$. Residual behavior needs integral certificates.

For a finite inertial type, choose finitely many inertia elements and algebraic matrix coefficients that distinguish the desired characters. Only finitely many coefficient primes divide their nonzero differences. Outside those primes, the residual inertial characters remain distinct and nontrivial.

For monodromy, one needs an integral Weil--Deligne model tied to the actual tame-inertia action on the chosen stable lattices. To obtain one finite exceptional set as $\lambda$ varies, these models must come from one algebraic integral datum after inverting one fixed nonzero ideal $\mathfrak a$ of $\mathcal O_E$; unrelated integral normalizations chosen separately at each $\lambda$ give no uniform conclusion. After a harmless coefficient enlargement, this means a finite free $\mathcal O_E[1/\mathfrak a]$-lattice carrying the finite-inertia action and $N_v$, together with comparisons identifying its $\lambda$-adic completions with the local data of the chosen $T_\lambda$. Record a nonzero maximal minor of the resulting integral operator. Outside the primes dividing $\mathfrak a$ and that minor, reduction has the same monodromy rank. At a Steinberg place this makes the residual unipotent class visible. Merely choosing coordinates in which the rational operator $N_v$ has an entry equal to $1$ is not a certificate: a rational change of basis can erase the arithmetic thickness of the lattice.

At a principal-series place, avoiding primes dividing

$$
\theta_1(t)-\theta_2(t) \tag{18.7}
$$

for a witnessing inertia element $t$ preserves distinct residual characters. At a CM place, the analogous difference between $\theta$ and $\theta^\sigma$ preserves residual induction irreducibility.

At places above the new coefficient prime $q$, a separate local theorem is needed. If the system comes from an elliptic curve with good reduction, the canonical $T_q$ lattice has finite-flat quotients and weights $\{0,1\}$. If it comes from an automorphic form, one needs the crystalline or semistable comparison and, for an integral finite-flat conclusion, an integral abelian factor or another theorem producing the required group schemes. De Rham weights alone do not suffice.

### 18.5 The switching theorem

We can now state the exact changing-prime result.

**Theorem 18.1 (controlled coefficient-prime switch).** Let

$$
\mathcal R=\{\rho_\lambda\}_\lambda
$$

be a rank-two semisimple compatible system over $F$ with coefficients in $E$. Assume:

1. $\mathcal R$ is strongly compatible away from coefficient primes, Hodge compatible, pure, and has determinant $\psi_\lambda\chi_{\ell(\lambda)}^m$;
2. one member $\rho_{\lambda_*}$ is associated with a regular algebraic cuspidal automorphic representation $\pi$ in the curve-realizable range;
3. after one fixed common coefficient enlargement aligning the system's polynomials with those of $\pi$, the representations $\rho_{\pi,\nu}$ exist at every finite $\nu$ of that common field and have the local and coefficient-prime comparison properties being claimed;
4. for every desired residual local condition at the finite set $T$, the stable lattices are tied to a uniform algebraic integral model after inverting one fixed ideal of $\mathcal O_E$, and a nonzero integral certificate as in Section 18.4 has been fixed.

Then there is a finite set $B_{\mathrm{loc}}$ of coefficient places such that, for every $\nu\notin B_{\mathrm{loc}}$ of residue characteristic $q$, the following arithmetic and local conclusions hold.

1. After a finite common coefficient extension,
   $$
   \rho_\nu^{\mathrm{ss}}\simeq\rho_{\pi,\nu}^{\mathrm{ss}}.
   $$
   If either side is irreducible, they are isomorphic without further semisimplification.
2. The member $\rho_\nu$ has the common good polynomials, determinant, purity weight, polarization, and labelled Hodge--Tate weights of $\mathcal R$.
3. For every $v\in T$ with $v\nmid q$, its Frobenius-semisimple Weil--Deligne parameter, including $N_v$, is the common $D_v$. Thus characteristic-zero conductor, inertial type, and monodromy rank are controlled.
4. At every $v\in T$ with $v\nmid q$, the residual local distinctions certified in hypothesis 4 survive. No uncertified residual extension or conductor equality is included.
5. At $u\mid q$, the common coefficient-prime comparison gives the stated de Rham, crystalline, or semistable property. A finite-flat conclusion is included only when the chosen integral construction supplies compatible finite-flat quotients.

There are two distinct image addenda.

- If the non-CM hypotheses of Theorem 16.1 hold, there is a further finite set $B_{\mathrm{img}}$ such that $\bar\rho_\nu$ is absolutely irreducible and adequate for every $\nu\notin B_{\mathrm{loc}}\cup B_{\mathrm{img}}$.
- Without that theorem, a particular proposed place $\nu_0\notin B_{\mathrm{loc}}$ may be used only after absolute irreducibility and adequacy of $\bar\rho_{\nu_0}$ have been verified directly. Such a one-prime verification has no conclusion for the other coefficient places.

**Proof.** Weak compatibility and the modular identity at $\lambda_*$ give equality of $P_v$ with the automorphic polynomials at almost every $v$. Chebotarev proves clause 1. The algebraic definitions of determinant, purity, polarization, and Hodge compatibility give clause 2. Strong compatibility gives clause 3. By the uniformity required in hypothesis 4, each residual local certificate is controlled by finitely many nonzero algebraic integers and one fixed denominator ideal. Only finitely many coefficient places divide them; their union is $B_{\mathrm{loc}}$ and proves clause 4. Clause 5 is exactly the coefficient-prime comparison and integral hypothesis. The first image addendum is Theorem 16.1 and Corollary 16.2; the second merely records the scope of a direct calculation. $\square$

The theorem separates its sources on purpose. Compatibility constructs the new member and transfers algebraic invariants. Chebotarev identifies it with the automorphic member. The image theorem supplies residual adequacy. Integral local certificates control reduction. No one of these four mechanisms replaces another.

## 19. Hostile diagnostics

### 19.1 Weak data with incompatible monodromy

Take the two local Weil--Deligne pairs of Section 4.2 with common semisimple Weil representation

$$
r=\theta\|\cdot\|_v\oplus\theta.
$$

One has $N=0$ and the other has rank-one $N$. If $\theta$ is unramified, their inertial types are both trivial and their semisimple Frobenius eigenvalues are the same. Yet their conductor exponents are respectively $0$ and $1$ after the appropriate principal-series boundary is interpreted, and only the second has Steinberg monodromy.

This is the local obstruction behind the warning about weak systems. A table of good $P_v$ outside one place contains neither pair. A claim that it determines the bad local parameter has inserted $N$ without evidence.

For globally semisimple representations, Chebotarev makes two members with the same almost-everywhere character globally isomorphic, so their actual local restrictions agree. The failure is epistemic and cross-coefficient: weak compatibility does not prove that the separately constructed members share an algebraic bad-place parameter. For nonsemisimple global extensions, even the actual extension class can vary while the semisimplification remains fixed.

### 19.2 A coefficient-embedding mismatch

Let $E$ have two places $\lambda_1,\lambda_2$ above the same rational prime $\ell$. There need be no canonical isomorphism

$$
E_{\lambda_1}\simeq E_{\lambda_2}. \tag{19.1}
$$

Writing $\rho_{\lambda_1}=\rho_{\lambda_2}$ is therefore meaningless. Their common statement is that both characteristic polynomials are images of $P_v\in E[X]$ under their own completion maps.

The same error occurs with labels. Suppose two real embeddings $\tau_1,\tau_2$ carry different weights. A coefficient automorphism can exchange the embeddings. Comparing the first entry of an unlabelled list at $\lambda_1$ with the first entry of a separately ordered list at $\lambda_2$ can falsely report a change of Hodge type. The invariant assertion is (5.8), which transports the label together with $\iota_\lambda$.

At a bad place, writing $D_{v,\lambda_1}=D_{v,\lambda_2}$ without a common algebraic $D_v$ and two embeddings has the same defect. Strong compatibility is an embedding-aware scalar-extension statement.

### 19.3 Residual collapse and coefficient-prime ramification

Residual irreducibility can fail at an exceptional coefficient prime even when every characteristic-zero member is irreducible. Congruent inducing characters in (16.9), a rational isogeny on an elliptic curve, or a small exceptional projective image can cause the failure. No definition of compatibility rules it out.

Residual ramification can also collapse. At a fixed place $v\nmid\ell(\lambda)$, roots of unity of $\ell$-power order in a finite inertia type reduce to $1$. At a multiplicative elliptic place, the nonzero characteristic-zero monodromy thickness can be divisible by $\ell$ and disappear in (7.7). Therefore

$$
a_v(\bar\rho_\lambda)
\le a_v(\rho_\lambda) \tag{19.2}
$$

can be strict; even this inequality is best read for a chosen lattice and its actual inertia action rather than treated as a universal conductor formula.

At $v\mid\ell$, good reduction does not imply unramifiedness. The determinant already contains the ramified cyclotomic character. Crystalline and finite flat are the appropriate rational and integral notions. A switching argument that declares the new member unramified at its coefficient prime because the original system was unramified at almost every fixed $v$ has confused moving and fixed primes.

### 19.4 Restriction, induction, and self-twist failures

Restriction can destroy irreducibility, as (9.2) shows. It can also kill finite inertia and lower conductor. A potential-modularity field chosen without disjointness from the residual fixed field can therefore destroy adequacy before a lifting theorem is applied.

Induction changes dimension. If $L/F$ is quadratic and $V$ has dimension two, then

$$
\dim\operatorname{Ind}_{G_L}^{G_F}V=4. \tag{19.3}
$$

Only induction of a character has dimension two. Applying a theorem about two-dimensional odd representations to the left side of (19.3) is a category error.

A quadratic self-twist can make solvable base change noncuspidal. If

$$
\pi\simeq\pi\otimes\eta_{L/F},
$$

then $\pi$ is induced from $L$ and its base change is a two-character isobaric sum. Continuing to call it a cuspidal automorphic source invalidates residual irreducibility and the non-Eisenstein lifting input.

Finally, potential automorphy over $F'$ does not descend merely because the system's traces look invariant. One needs a compatible cyclic descent chain or an arithmetic representation over $F$ selecting the twists. If $F'/F$ is nonsolvable, the solvable theorem does not start.

### 19.5 A Steinberg-place audit

Let $v\nmid\ell$ and let the local member be an unramified twist of Steinberg by $\theta$. Choose a basis $e_1,e_2$ with

$$
r(\operatorname{Frob}_v)=
\begin{pmatrix}
\theta(\operatorname{Frob}_v)q_v&0\\
0&\theta(\operatorname{Frob}_v)
\end{pmatrix},
\qquad
N(e_2)=e_1. \tag{19.4}
$$

The hostile audit is short and decisive.

- Conjugating $N$ by Frobenius multiplies it by $q_v$, agreeing with (4.3).
- The determinant is $\theta(\operatorname{Frob}_v)^2q_v$, agreeing with the central character.
- The inertial type of $r$ is trivial.
- The monodromy rank is one.
- Formula (4.10) gives conductor exponent $1$.
- Omitting $N$ changes the parameter to a zero-monodromy two-character parameter.
- Reducing a chosen integral lattice can kill the unipotent extension at finitely many coefficient primes, but cannot change the characteristic-zero rank of $N$.

Every item must survive a claimed base change or coefficient-prime switch. Under base change, the unramified twist is pulled back by the norm, Frobenius values are raised by the residue degree, and $N$ stays nonzero. Under coefficient change, the algebraic scalar is embedded into the new completion and the same $N$ is transported.

## 20. Scoped export and downstream handoff

### 20.1 The generic ledger

The output of this book is the compatible-system ledger

$$
\mathscr C=
\left(F,E,S,\{\rho_\lambda\}_\lambda,
\{P_v\}_{v\notin S},\delta,
\{D_v\}_{v\in\mathcal V_{\mathrm{str}}},
\{H_{\tau_0}\}_{\tau_0},m,\mu,B\right). \tag{20.1}
$$

It keeps the base and coefficient fields separate; records the weak good-prime polynomials;
records full Frobenius-semisimple Weil--Deligne pairs only on the proved strong range
$\mathcal V_{\mathrm{str}}$; and carries determinant, Hodge, purity, parity, polarization, and
inner-twist data. The exception ledger $B$ distinguishes integral-local exceptions from image
exceptions. Chosen lattices are placewise auxiliary data, not one lattice shared across
coefficient characteristics.

The constructions proved here are the generic calculus: coefficient extension and restriction,
coefficient conjugation and inner twists, Tate and finite-order twists, duals, sums, tensors and
symmetric powers, base-field restriction and finite induction, and conditional attachment from
an automorphic packet in Book 168's range. Book 167 supplies the dense-Frobenius uniqueness
step; Book 141 supplies the finite-group and adequacy input for the large-image wrapper.

### 20.2 The switching interface

For a new coefficient place $\nu$, compatibility transports

$$
P_v,\quad \delta_\nu,\quad
D_v\ (v\in\mathcal V_{\mathrm{str}},\ v\nmid\ell(\nu)),\quad
H_{\tau_0},\quad m,\quad\mu_\nu. \tag{20.2}
$$

It does not transport an old residual extension, stable lattice, or finite-flat model. Theorem
18.1 gives the genuinely generic all-but-finitely-many switch once its uniform integral
certificates and large-image hypotheses are supplied. Without those certificates, the rational
algebraic invariants still switch, but residual local extension and conductor statements do
not.

### 20.3 Descent is downstream

There is intentionally no omnibus theorem combining automorphic attachment, potential
automorphy, Brauer effectivity, coefficient descent, and switching. A system already produced
over the base field—whether directly from Book 168 or downstream by Books 183--185—may be
inserted into this ledger and switching interface. The construction of the latter descended
system is not repeated here and is not a premise of this book.

This scoped endpoint prevents three common overclaims: weak compatibility is not strong local
compatibility; rational cancellation is not integral cancellation; and potential automorphy
over a top field is not a compatible family over the original field.
