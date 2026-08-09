# Changing the Prime

## Contents

1. [The prime-switching problem](#1-the-prime-switching-problem)
   - [Two meanings of prime](#11-two-meanings-of-prime)
   - [The switching square](#12-the-switching-square)
   - [What can and cannot cross the square](#13-what-can-and-cannot-cross-the-square)
   - [Standing conventions](#14-standing-conventions)
2. [The compatible-system input ledger](#2-the-compatible-system-input-ledger)
   - [Fields, members, and common polynomials](#21-fields-members-and-common-polynomials)
   - [Determinant, purity, Hodge labels, and polarization](#22-determinant-purity-hodge-labels-and-polarization)
   - [Weak, strong, and coefficient-prime compatibility](#23-weak-strong-and-coefficient-prime-compatibility)
   - [Integral models and local certificates](#24-integral-models-and-local-certificates)
   - [The complete switching datum](#25-the-complete-switching-datum)
3. [Choosing the new coefficient place](#3-choosing-the-new-coefficient-place)
   - [A rational prime and a place above it](#31-a-rational-prime-and-a-place-above-it)
   - [Splitting and residue degree](#32-splitting-and-residue-degree)
   - [Coefficient enlargement and its limits](#33-coefficient-enlargement-and-its-limits)
   - [Chebotarev selection conditions](#34-chebotarev-selection-conditions)
   - [A fixed small prime is a different problem](#35-a-fixed-small-prime-is-a-different-problem)
4. [The new adic member](#4-the-new-adic-member)
   - [Construction by selection](#41-construction-by-selection)
   - [Comparison at good base places](#42-comparison-at-good-base-places)
   - [Chebotarev and global identification](#43-chebotarev-and-global-identification)
   - [Determinant, oddness, polarization, and purity](#44-determinant-oddness-polarization-and-purity)
5. [Stable lattices and residual members](#5-stable-lattices-and-residual-members)
   - [Existence without canonicity](#51-existence-without-canonicity)
   - [The canonical semisimplification](#52-the-canonical-semisimplification)
   - [Reducibility and absolute irreducibility](#53-reducibility-and-absolute-irreducibility)
   - [Adequacy and exceptional images](#54-adequacy-and-exceptional-images)
   - [The image exceptional set](#55-the-image-exceptional-set)
6. [Local invariants away from the new coefficient prime](#6-local-invariants-away-from-the-new-coefficient-prime)
   - [Transport of Weil--Deligne data](#61-transport-of-weil--deligne-data)
   - [Conductor, inertial type, and monodromy](#62-conductor-inertial-type-and-monodromy)
   - [Strong versus almost-all conclusions](#63-strong-versus-almost-all-conclusions)
   - [The old coefficient prime after the switch](#64-the-old-coefficient-prime-after-the-switch)
7. [Integral reduction of local ramification](#7-integral-reduction-of-local-ramification)
   - [Finite inertia and character collision](#71-finite-inertia-and-character-collision)
   - [Tame unipotent inertia](#72-tame-unipotent-inertia)
   - [When monodromy disappears](#73-when-monodromy-disappears)
   - [Residual conductors and local certificates](#74-residual-conductors-and-local-certificates)
   - [Ramification away from the common bad set](#75-ramification-away-from-the-common-bad-set)
8. [Places above the new coefficient prime](#8-places-above-the-new-coefficient-prime)
   - [The missing comparison](#81-the-missing-comparison)
   - [Crystalline, semistable, and ordinary members](#82-crystalline-semistable-and-ordinary-members)
   - [Finite flatness is integral](#83-finite-flatness-is-integral)
   - [An all-prime local compatibility certificate](#84-an-all-prime-local-compatibility-certificate)
9. [The Fontaine--Laffaille threshold](#9-the-fontaine--laffaille-threshold)
   - [The exact range](#91-the-exact-range)
   - [The type-zero-one criterion](#92-the-type-zero-one-criterion)
   - [Proof of the criterion](#93-proof-of-the-criterion)
   - [Weights outside the range and ramified bases](#94-weights-outside-the-range-and-ramified-bases)
   - [Ordinary and nonordinary finite-flat objects](#95-ordinary-and-nonordinary-finite-flat-objects)
10. [Designing a controlled switch](#10-designing-a-controlled-switch)
    - [The finite exceptional-set ledger](#101-the-finite-exceptional-set-ledger)
    - [Local survival conditions](#102-local-survival-conditions)
    - [Flexible-prime selection theorem](#103-flexible-prime-selection-theorem)
    - [What density does not prove](#104-what-density-does-not-prove)
11. [Automorphy across coefficient primes](#11-automorphy-across-coefficient-primes)
    - [One automorphic representation, every member](#111-one-automorphic-representation-every-member)
    - [Potential automorphy over an extension](#112-potential-automorphy-over-an-extension)
    - [Solvable descent with an extending member](#113-solvable-descent-with-an-extending-member)
    - [The descent failure test](#114-the-descent-failure-test)
12. [Passage to the rational prime 3](#12-passage-to-the-rational-prime-3)
    - [Coefficient places above 3](#121-coefficient-places-above-3)
    - [Residual image possibilities](#122-residual-image-possibilities)
    - [Adequacy in characteristic 3](#123-adequacy-in-characteristic-3)
    - [Reducible and dihedral branches](#124-reducible-and-dihedral-branches)
13. [Integral local structure at 3](#13-integral-local-structure-at-3)
    - [Finite-flat type zero one](#131-finite-flat-type-zero-one)
    - [Tame inertia weights](#132-tame-inertia-weights)
    - [Ordinary and supersingular shapes](#133-ordinary-and-supersingular-shapes)
    - [The 3-adic local checklist](#134-the-3-adic-local-checklist)
14. [The hardly ramified package](#14-the-hardly-ramified-package)
    - [Definition and conductor record](#141-definition-and-conductor-record)
    - [Local break and different bounds at 3](#142-local-break-and-different-bounds-at-3)
    - [The global root-discriminant bound](#143-the-global-root-discriminant-bound)
    - [Degree and auxiliary-prime refinements](#144-degree-and-auxiliary-prime-refinements)
    - [What is exported to the discriminant argument](#145-what-is-exported-to-the-discriminant-argument)
15. [Four hostile diagnostics](#15-four-hostile-diagnostics)
    - [A Steinberg parameter vanishing modulo the new prime](#151-a-steinberg-parameter-vanishing-modulo-the-new-prime)
    - [A CM or dihedral system](#152-a-cm-or-dihedral-system)
    - [Residue degree greater than one](#153-residue-degree-greater-than-one)
    - [A successful elliptic-curve switch to 3](#154-a-successful-elliptic-curve-switch-to-3)
16. [The prime-switching theorem package](#16-the-prime-switching-theorem-package)
    - [Controlled switching theorem](#161-controlled-switching-theorem)
    - [The 3-adic companion theorem](#162-the-3-adic-companion-theorem)
    - [The hardly ramified corollary](#163-the-hardly-ramified-corollary)
    - [Proof architecture and source ledger](#164-proof-architecture-and-source-ledger)
17. [Failure modes and audit protocol](#17-failure-modes-and-audit-protocol)
    - [Prime, place, and embedding failures](#171-prime-place-and-embedding-failures)
    - [Residual and monodromy failures](#172-residual-and-monodromy-failures)
    - [Hodge and finite-flat failures](#173-hodge-and-finite-flat-failures)
    - [Compatibility and descent failures](#174-compatibility-and-descent-failures)
    - [A hostile audit checklist](#175-a-hostile-audit-checklist)
18. [Interfaces and conclusion](#18-interfaces-and-conclusion)
    - [Interface to the classification of hardly ramified representations](#181-interface-to-the-classification-of-hardly-ramified-representations)
    - [Interface to the modular-method synthesis](#182-interface-to-the-modular-method-synthesis)
    - [Final perspective](#183-final-perspective)

## 1. The prime-switching problem

An adic representation is built for one coefficient topology. Its matrices, stable lattices, reduction, and coefficient-prime local theory all live over one completion. Arithmetic applications often demand a different topology. A residual image may be too small at the original prime, a local lifting theorem may be available only at another prime, or a final classification may be organized around characteristic $3$. The purpose of changing the prime is to move to a different member of one arithmetic family without pretending that the two local coefficient fields communicate directly.

The reliable bridge is algebraic. Frobenius traces and determinants at good places lie in a number field before any completion is chosen. Stronger input may put bad-place Weil--Deligne parameters, Hodge labels, determinant characters, and polarizations in the same algebraic ledger. Integral and residual information is more delicate: it requires lattices and certificates that do not belong to the rational compatible system by definition.

This chapter fixes the two-prime language and displays the logical shape of the argument. Every later transfer will be traced to one entry of the ledger rather than to the vague phrase “independence of the prime.”

### 1.1 Two meanings of prime

Let $F$ be the base number field and $E$ the coefficient field. A finite place $v$ of $F$ is a place where the representation is localized. Its residue characteristic will be denoted

$$
p(v)=\operatorname{char}k_v.
$$

A finite place $\lambda$ of $E$ is a choice of coefficient topology. Its residue characteristic is

$$
\ell(\lambda)=\operatorname{char}k_\lambda.
$$

These places have different jobs. Passing from $G_F$ to $G_{F_v}$ changes the Galois group being studied. Passing from $E$ to $E_\lambda$ leaves $G_F$ unchanged and changes the scalar field of its matrices. The assertion $v\nmid\ell(\lambda)$ means only that $p(v)\ne\ell(\lambda)$.

Suppose the original member is indexed by $\lambda_0\mid\ell_0$ and the desired member by $\nu\mid q$. The switch changes $\lambda_0$ to $\nu$. It does not move any base place. A fixed $v\mid\ell_0$ remains the same place of $F$; it merely changes from a coefficient-prime place for $\rho_{\lambda_0}$ to an away-from-coefficient place for $\rho_\nu$ when $q\ne\ell_0$. Conversely, every $u\mid q$ becomes a coefficient-prime place for the new member.

This distinction is especially important when $q=3$. The rational number $3$, a base place $u\mid3$, and a coefficient place $\nu\mid3$ are three related but unequal objects.

### 1.2 The switching square

The basic argument has the following form.

```text
 original member rho_{lambda_0}  <---->  algebraic compatible data
             |                                  |
             | automorphic identification       | completion at nu
             v                                  v
      one automorphic pi             ---->   new member rho_nu
```

There is no horizontal scalar-extension arrow from the upper left to the lower right. If $q\ne\ell_0$, the expression

$$
\rho_{\lambda_0}\otimes_{E_{\lambda_0}}E_\nu
$$

is meaningless because $E_\nu$ is not naturally an $E_{\lambda_0}$-algebra. Instead, the original member identifies the common algebraic Frobenius polynomials with those of an automorphic representation. The automorphic representation has its own $\nu$-adic realization. Chebotarev then identifies that realization with the semisimple new member.

When the system is already geometric, the automorphic vertex is not required to construct the new member: an elliptic curve has a $q$-adic Tate module directly. It remains useful for transferring automorphy. In either route, the common algebraic record is the bridge.

### 1.3 What can and cannot cross the square

The following data can cross when the corresponding compatibility has been proved:

- common good-place characteristic polynomials;
- a compatible determinant character;
- purity and its weight;
- a compatible polarization and total oddness;
- labelled Hodge--Tate weights under the chosen embeddings;
- at a fixed $v\nmid q$, a common Frobenius-semisimple Weil--Deligne pair, including its monodromy operator.

The following data do not cross from the rational system alone:

- a stable lattice;
- a nonsplit residual extension;
- residual irreducibility or adequacy;
- the reduction of a tame monodromy parameter;
- crystalline, semistable, finite-flat, or ordinary behavior at $u\mid q$;
- a comparison between the old coefficient-prime period module at a fixed place and the away-from-coefficient Weil--Deligne datum there;
- descent of potential automorphy from an auxiliary base field.

Each missing item has a different remedy. Compactness gives some stable lattice, but not a preferred one. A large-image theorem or a direct calculation gives residual irreducibility. A uniform integral local model gives reduction certificates. Coefficient-prime comparison gives crystalline or semistable behavior. Finite-flat geometry gives the integral model. Descent requires a coherent field-theoretic argument.

### 1.4 Standing conventions

Arithmetic Frobenius is used throughout. If $v\nmid\ell(\lambda)$ and $\rho_\lambda$ is unramified at $v$, then

$$
P_v(X)=\det\bigl(X-\rho_\lambda(\operatorname{Frob}_v)\bigr).
$$

The cyclotomic character satisfies

$$
\chi_{\ell(\lambda)}(\operatorname{Frob}_v)=Nv.
$$

We use covariant realizations and assign Hodge--Tate weight $1$ to the cyclotomic character. Thus a weight-two geometric member has labelled weights $\{0,1\}$. All characteristic-zero members are taken semisimple unless an extension is explicitly retained. A residual representation without a named lattice always means its lattice-independent semisimplification.

For a coefficient place $\lambda$, write

$$
E_\lambda,\qquad \mathcal O_\lambda,\qquad
\varpi_\lambda,\qquad k_\lambda
$$

for its completion, valuation ring, a uniformizer, and residue field. Put

$$
f_\lambda=[k_\lambda:\mathbf F_{\ell(\lambda)}].
$$

Coefficient embeddings are part of every comparison. A choice

$$
\iota_\lambda:\overline{\mathbf Q}
\hookrightarrow\overline{\mathbf Q}_{\ell(\lambda)}
$$

induces $\lambda$ on $E$ and transports algebraic coefficients and Hodge labels. Equality across distinct completions will always mean scalar extension of one algebraic datum through the relevant embeddings.

## 2. The compatible-system input ledger

Prime switching is safe only when its inputs are inventoried before the new prime is chosen. The ledger separates rational data, local comparison data, and integral data. This prevents a proof of one layer from being silently used as a proof of another.

### 2.1 Fields, members, and common polynomials

The first layer consists of:

$$
F,\qquad E,\qquad S,\qquad
\mathcal R=\{\rho_\lambda\}_\lambda,\qquad
\{P_v(X)\}_{v\notin S}.
$$

Here $S$ is a finite set of base-field places and

$$
\rho_\lambda:G_F\longrightarrow
\operatorname{GL}_2(E_\lambda)
$$

is continuous and semisimple for every finite place $\lambda$ of $E$. For $v\notin S$ and $p(v)\ne\ell(\lambda)$, the member is unramified and

$$
\det\bigl(X-\rho_\lambda(\operatorname{Frob}_v)\bigr)
=\iota_\lambda P_v(X).
$$

Write

$$
P_v(X)=X^2-a_vX+d_v,\qquad a_v,d_v\in E.
$$

Then the comparison between two members is not $a_v$ viewed in one common local field. It is the pair of statements

$$
\operatorname{tr}\rho_{\lambda_0}(\operatorname{Frob}_v)
=\iota_{\lambda_0}(a_v),
$$

$$
\operatorname{tr}\rho_\nu(\operatorname{Frob}_v)
=\iota_\nu(a_v),
$$

and similarly for $d_v$. This embedding-aware formulation survives even when the completions are nonisomorphic.

### 2.2 Determinant, purity, Hodge labels, and polarization

A useful rank-two system carries a compatible determinant of the form

$$
\det\rho_\lambda=\psi_\lambda
\chi_{\ell(\lambda)}^m,
$$

where $\psi$ is a finite-order algebraic character and $m$ is fixed. At a good place,

$$
d_v=\psi(v)(Nv)^m.
$$

The determinant does more than check the constant term. It transports oddness and constrains the Hodge labels. If $F$ is totally real and $c_\tau$ is complex conjugation at a real place, total oddness is

$$
\det\rho_\lambda(c_\tau)
=\psi(c_\tau)(-1)^m=-1.
$$

This identity is independent of the coefficient place in characteristic zero.

Purity of weight $m$ means that for every root $\alpha$ of every good $P_v$ and every complex embedding $\sigma$,

$$
|\sigma(\alpha)|=(Nv)^{m/2}.
$$

Because purity is a property of the algebraic roots, it transfers to every completion once proved. It does not follow from the existence of the common polynomials.

For coefficient-prime places one needs a labelled Hodge datum

$$
H=\{H_{\tau_0}\}_{\tau_0:F\hookrightarrow\overline{\mathbf Q}}.
$$

If $u\mid\ell(\lambda)$ and $\tau=\iota_\lambda\circ\tau_0$ induces $u$, Hodge compatibility asserts

$$
\operatorname{HT}_\tau
(\rho_\lambda|_{G_{F_u}})=H_{\tau_0}.
$$

The label moves with the coefficient embedding. Comparing unlabelled lists after unrelated reorderings is not a compatibility statement.

A polarization is recorded as a compatible multiplier $\mu_\lambda$ and pairings

$$
V_\lambda\times V_\lambda\longrightarrow E_\lambda(\mu_\lambda).
$$

In rank two the rational alternating pairing with multiplier $\det\rho_\lambda$ is linear algebra, but an arithmetic compatible multiplier and an integral perfect pairing carry additional information. Primes dividing the discriminant of an integral pairing belong in the exceptional set whenever residual self-duality is needed.

### 2.3 Weak, strong, and coefficient-prime compatibility

Weak compatibility is the almost-everywhere statement of Section 2.1. It controls good Frobenius polynomials and determines global semisimplifications by Chebotarev. It does not determine the local parameter at a member of $S$ from its definition alone.

Strong compatibility at a fixed base place $v$ supplies one algebraic Frobenius-semisimple Weil--Deligne pair

$$
D_v=(r_v,N_v)
$$

such that, for every $\lambda$ with $p(v)\ne\ell(\lambda)$,

$$
\operatorname{WD}_v(\rho_\lambda)^{\mathrm{F\text{-}ss}}
\simeq\iota_\lambda D_v.
$$

The nilpotent operator is retained. Consequently the inertial type $r_v|_{I_v}$, the rank of $N_v$, and the characteristic-zero conductor exponent are common in this range. If strong compatibility has been proved only for a declared set $\mathcal V_{\mathrm{str}}$ of base places, no omitted place may be inserted later.

Coefficient-prime compatibility is separate. It may assert that the members are de Rham with the labelled weights $H$, crystalline at places of good reduction, semistable at semistable places, or related to a common filtered module. These are comparison theorems or geometric facts. They are not consequences of the away-from-coefficient pairs $D_v$.

The phrase “fully compatible” will therefore mean that all three ledgers have been supplied with their exact ranges. It will never mean that weak compatibility has somehow absorbed the other two.

### 2.4 Integral models and local certificates

For each coefficient place at which residual information is needed, choose a stable lattice

$$
T_\lambda\subset V_\lambda.
$$

A list of unrelated lattices is enough to define individual residual members. It is not enough to prove that a residual local distinction survives outside one finite set of coefficient places. Such a finite-exception assertion requires a uniform algebraic integral model.

At a fixed bad place $v$, a **local certificate** consists of:

1. a finite free module over $\mathcal O_E[1/\mathfrak a]$ for one nonzero ideal $\mathfrak a$;
2. an integral finite-inertia action and, when relevant, an integral monodromy or tame-extension parameter;
3. comparisons with the completions of the chosen $T_\lambda$ outside the primes dividing $\mathfrak a$; and
4. one or more nonzero algebraic integers whose nonvanishing expresses the desired residual distinction.

For two inertial characters, a certificate may be

$$
\theta_1(t)-\theta_2(t)\ne0
$$

for a witnessing inertia element $t$. For rank-one monodromy it is a nonzero maximal minor of the integral operator tied to the lattice. The rational normalization $N(e_2)=e_1$ is not itself a certificate: a rational change of basis can hide the integral thickness that reduction sees.

At a coefficient-prime place, the certificate is a chosen integral model: a finite-flat group scheme, a compatible tower of such schemes, an integral Fontaine--Laffaille object, or a geometric Tate lattice. A rational assertion about Hodge--Tate weights is not an integral certificate.

### 2.5 The complete switching datum

We package the input as

$$
\mathscr S=
\left(
F,E,S,\mathcal V_{\mathrm{str}},
\{\rho_\lambda\},\{P_v\},
\psi,m,H,\mu,
\{T_\lambda\},\mathscr I,\mathscr C
\right).
$$

Here $\mathscr I$ records coefficient-prime comparison and integral hypotheses, while $\mathscr C$ records the finite collection of away-from-coefficient local certificates. Some applications use only part of this tuple. The point of displaying it is to make every conclusion traceable:

| conclusion | required source |
|---|---|
| good traces and determinants | weak compatibility |
| bad-place type, conductor, and $N$ away from the coefficient prime | strong compatibility at that place |
| Hodge labels | Hodge compatibility |
| crystalline or semistable status | coefficient-prime comparison |
| finite-flat residual module | chosen integral model |
| residual local extension or conductor equality | chosen lattice and local certificate |
| residual irreducibility and adequacy | image theorem or direct computation |
| automorphy of every member | one automorphic member, the automorphic family, and Chebotarev |
| descent to the original base field | an independent descent theorem |

This table is the control panel for the rest of the book.

## 3. Choosing the new coefficient place

When the new rational prime is flexible, it can be selected to avoid denominators, split in coefficient fields, and satisfy auxiliary congruences. When it is fixed in advance, especially when it is $3$, none of that freedom is available. This chapter separates those two situations.

### 3.1 A rational prime and a place above it

Choose a rational prime $q$. A coefficient place above it is a prime ideal

$$
\nu\subset\mathcal O_E,\qquad \nu\mid q.
$$

The factorization is

$$
q\mathcal O_E=\prod_{i=1}^g\nu_i^{e_i},
$$

with residue degrees

$$
f_i=[\mathcal O_E/\nu_i:\mathbf F_q],
$$

and

$$
[E:\mathbf Q]=\sum_{i=1}^g e_if_i.
$$

Choosing $q$ does not choose $\nu$. Different places above the same rational prime can give nonisomorphic completions and different residual representations. Every theorem about “the $q$-adic member” must either specify $\nu$ or prove that all choices have the required property.

The residue representation attached to $\nu$ is two-dimensional over

$$
k_\nu\simeq\mathbf F_{q^{f_\nu}}.
$$

It is two-dimensional over $\mathbf F_q$ only when $f_\nu=1$ and a field-of-definition statement has been made. Restriction of scalars from $k_\nu$ to $\mathbf F_q$ changes the dimension to $2f_\nu$.

### 3.2 Splitting and residue degree

If $q$ splits completely in $E$, then every $e_i=f_i=1$, and

$$
E_{\nu_i}\simeq\mathbf Q_q,\qquad k_{\nu_i}=\mathbf F_q.
$$

For selection it is convenient to require $q$ to split completely in the Galois closure $E^{\mathrm{gal}}$. This condition implies complete splitting in $E$ and avoids ambiguity about non-Galois factorization.

Complete splitting is stronger than residue degree one. A ramified place can have $f_\nu=1$ while $E_\nu/\mathbf Q_q$ is ramified. If the next argument needs only matrices over $\mathbf F_q$, residue degree one may suffice. If it needs an unramified coefficient ring or a canonical identification with $\mathbf Q_q$, ramification must also be excluded.

The base field has a separate condition. If $q$ is unramified in $F$, then every completion $F_u/\mathbf Q_q$ for $u\mid q$ is unramified, although its residue degree may exceed one. This is precisely the base-field hypothesis in the clean Fontaine--Laffaille range. Splitting of $q$ in the coefficient field says nothing about ramification of $q$ in the base field.

### 3.3 Coefficient enlargement and its limits

One often enlarges $E$ to a field $E'$ that contains all automorphic eigenvalues and defines every bad-place parameter. If $\nu'\mid\nu$, then

$$
f(\nu'/q)=f(\nu'/\nu)f(\nu/q).
$$

Thus coefficient enlargement cannot turn a place of residue degree greater than one into a degree-one place. It can preserve the degree or increase it. Likewise, enlargement made after choosing a split prime can destroy the statement that the final residue field is $\mathbf F_q$.

The correct order for a flexible-prime argument is:

1. make every coefficient enlargement required by the construction;
2. take a Galois closure of the final selection field;
3. choose $q$ with the desired Frobenius class there;
4. choose a place $\nu\mid q$ in the final coefficient field.

For a fixed prime such as $3$, enlargement is still allowed for comparison of characteristic-zero representations, but its residue-field consequences must be recorded. If $k_\nu=\mathbf F_{3^f}$ with $f>1$, no later sentence may silently replace it by $\mathbf F_3$.

Coefficient descent is a different operation. If all traces happen to lie in a smaller field $E_0$, a two-dimensional $E_{0,\nu_0}$-model requires a vanishing Schur or cocycle obstruction and compatible descent data. Trace containment alone does not lower the residue degree.

### 3.4 Chebotarev selection conditions

Let $L_{\mathrm{sel}}/\mathbf Q$ be a finite Galois extension containing the Galois closure of the final coefficient field and every finite extension used to encode splitting or congruence conditions. Let

$$
C\subseteq\operatorname{Gal}(L_{\mathrm{sel}}/\mathbf Q)
$$

be a conjugacy-stable set. Chebotarev gives a set of unramified rational primes with

$$
\operatorname{Frob}_q\in C
$$

of density

$$
\frac{|C|}{[L_{\mathrm{sel}}:\mathbf Q]}.
$$

For complete splitting, $C=\{1\}$ and the density is

$$
\frac1{[L_{\mathrm{sel}}:\mathbf Q]}.
$$

Deleting finitely many rational primes preserves this density. Thus one may simultaneously avoid:

- primes below integral denominators and local certificates;
- primes ramified in $F$, $E$, or a chosen auxiliary field;
- primes below a finite residual-image exceptional set;
- small primes excluded by a group-theoretic adequacy theorem;
- residue characteristics of finitely many base places at which an away-from-coefficient condition must remain available.

Congruence conditions such as $q\equiv a\pmod m$ are encoded in $\mathbf Q(\zeta_m)$. They can be combined with splitting conditions only if the proposed Frobenius restrictions agree on intersections of the selection fields. A nonempty condition must be proved nonempty; writing down incompatible congruences does not create a Chebotarev class.

Residual largeness as $q$ varies is usually not itself a Frobenius condition in one fixed number field. It comes from an open-image or finite-exception theorem for the compatible system. Chebotarev then selects among the primes left after those image exceptions are removed.

### 3.5 A fixed small prime is a different problem

If the endpoint demands $q=3$, density has no role. One must inspect the actual factorization

$$
3\mathcal O_E=\prod_{\nu\mid3}\nu^{e_\nu}
$$

and check at least one chosen $\nu$ directly. The checks include:

- the residue degree and coefficient ramification;
- absolute irreducibility of $\bar\rho_\nu$;
- adequacy or the precise small-image substitute;
- finite flatness of a named lattice at every $u\mid3$;
- Hodge labels and crystalline or semistable comparison;
- every desired residual conductor drop or survival away from $3$.

There is always at least one coefficient place above $3$. There need not be one of residue degree one, and none is guaranteed to lie outside an image exceptional set. A theorem that produces a $3$-adic companion must therefore take these checks as hypotheses or prove them from the particular arithmetic source.

## 4. The new adic member

Once $\nu$ is chosen, construction is conceptually simple: the compatible system already contains its $\nu$-adic member. The work lies in proving that this member retains the exact rational, local, residual, and automorphic information required downstream.

### 4.1 Construction by selection

Define

$$
\rho_\nu:G_F\longrightarrow\operatorname{GL}_2(E_\nu)
$$

to be the $\nu$-member of $\mathcal R$. In a geometric system this may be a coefficient factor in a $q$-adic Tate module. In an automorphic system it is the representation attached to the same automorphic representation at the place $\nu$. In an abstract compatible system it is part of the input family.

These constructions must not be mixed without comparison. A rational coefficient factor of an abelian variety requires one algebraic factor polynomial independent of the rational prime. An automorphic factor requires a field-of-definition and local realization theorem. An abstract member is not automatically geometric or automorphic.

The representation is over $E_\nu$, not over $E$ and not over the old completion. If a comparison uses a larger local field $C_\nu$, the scalar extension

$$
\rho_\nu\otimes_{E_\nu}C_\nu
$$

must be displayed. Enlarging this local field does not change the coefficient place already selected, but it can enlarge the residual field of a chosen integral model.

### 4.2 Comparison at good base places

Let $v\notin S$ with $p(v)\ne q$. Then

$$
\det\bigl(X-\rho_\nu(\operatorname{Frob}_v)\bigr)
=\iota_\nu P_v(X)
=X^2-\iota_\nu(a_v)X+\iota_\nu(d_v).
$$

For the original member, provided $p(v)\ne\ell_0$,

$$
\det\bigl(X-\rho_{\lambda_0}(\operatorname{Frob}_v)\bigr)
=\iota_{\lambda_0}P_v(X).
$$

Thus the two traces and determinants are scalar images of the same algebraic coefficients. There is no claim that the two trace values are equal as elements of one topological field.

At a base place $v\mid q$, this good-place comparison is not asserted for the new member, even if $v\notin S$. The representation can be crystalline and ramified. At a place $v\mid\ell_0$, the new member is away from its coefficient prime when $q\ne\ell_0$, so strong local compatibility may now describe it even though the good-polynomial formula did not describe the old member there.

### 4.3 Chebotarev and global identification

Suppose one member is associated with a regular algebraic cuspidal automorphic representation $\pi$ and the automorphic family $\{\rho_{\pi,\lambda}\}$ is defined over a common coefficient field. Equality at the original place gives equality of $P_v(X)$ with the automorphic good polynomials for almost every $v$. Hence

$$
\det\bigl(X-\rho_\nu(\operatorname{Frob}_v)\bigr)
=\det\bigl(X-\rho_{\pi,\nu}(\operatorname{Frob}_v)\bigr)
$$

at a density-one set of base places after aligning coefficient embeddings. Chebotarev and the characteristic-zero character criterion give

$$
\rho_\nu^{\mathrm{ss}}
\simeq\rho_{\pi,\nu}^{\mathrm{ss}}
$$

after a finite common local coefficient extension.

If both sides are already semisimple, this is the desired isomorphism. If a naturally constructed representation has not been assumed semisimple, only its semisimplification has been identified. If the common residual semisimplification is absolutely irreducible, the characteristic-zero members are irreducible and the qualifier can be removed.

Chebotarev does not identify chosen lattices. It does not prove local--global compatibility at a bad place. It does not create a finite-flat model. It proves global semisimple uniqueness from dense Frobenius data, and nothing stronger is hidden in the argument.

### 4.4 Determinant, oddness, polarization, and purity

The compatible determinant specializes directly:

$$
\det\rho_\nu=\psi_\nu\chi_q^m.
$$

At every real place of a totally real base,

$$
\det\rho_\nu(c_\tau)=\psi(c_\tau)(-1)^m=-1.
$$

Thus total oddness survives the switch in characteristic zero. Reduction modulo $2$ would lose the sign distinction, but no such loss occurs in the characteristic-zero $3$-adic companion.

The rational polarization specializes with multiplier $\mu_\nu$. If the next step needs a perfect pairing on $T_\nu/\varpi_\nu T_\nu$, one must choose an integral lattice on which the pairing is perfect. Coefficient places dividing the index of the dual lattice are excluded or treated directly.

Purity also survives because its roots are the roots of the algebraic $P_v$. The Hodge labels survive under the separate Hodge-compatibility hypothesis. None of determinant, oddness, polarization, or purity implies residual irreducibility; each occupies its own line in the ledger.

## 5. Stable lattices and residual members

The new rational member is only half of a prime switch. Most modularity and classification arguments begin with its reduction. Passing to that reduction introduces an integral choice and a new exceptional set, so the lattice layer must be developed before any claim about image or ramification is made.

### 5.1 Existence without canonicity

The image of $G_F$ in $\operatorname{GL}_2(E_\nu)$ is compact. Begin with any full $\mathcal O_\nu$-lattice $L_0$. The translates $\rho_\nu(g)L_0$ lie in one bounded fractional lattice, and their span

$$
T_\nu=\sum_{g\in G_F}\rho_\nu(g)L_0
$$

is full, finitely generated, and stable. Thus a stable lattice always exists.

There is generally no canonical choice. Geometry can provide a distinguished lattice such as a Tate module, but an isogenous variety can change it. An automorphic realization may provide a saturated cohomological lattice, but congruent eigenbranches can obstruct an integral projector. Even in a fixed rational representation, nonhomothetic stable lattices can give different residual extensions.

Consequently a statement such as

$$
\bar\rho_\nu:G_F\longrightarrow\operatorname{GL}_2(k_\nu)
$$

must mean one of two things. Either a lattice $T_\nu$ has been named, in which case the full reduction is intended, or only the semisimplification is meant. A switching theorem must say which.

### 5.2 The canonical semisimplification

Let $T$ and $T'$ be two stable lattices in $V_\nu$. For every $g\in G_F$, the characteristic polynomial of $\rho_\nu(g)$ has coefficients in $\mathcal O_\nu$, and reducing it gives the characteristic polynomial on either lattice quotient. Hence the two residual representations have the same characteristic-polynomial function. The residual character criterion gives

$$
(T/\varpi_\nu T)^{\mathrm{ss}}
\simeq
(T'/\varpi_\nu T')^{\mathrm{ss}}
$$

after extending the residue field if necessary.

This proves the lattice independence of

$$
\bar\rho_\nu^{\mathrm{ss}}.
$$

It does not identify nonsplit extensions. For example, two congruent characteristic-zero characters can be glued by a stable lattice in either extension direction, or can reduce as a split sum. Traces and determinants cannot select among these possibilities.

The determinant does reduce without ambiguity:

$$
\det\bar\rho_\nu
=\bar\psi_\nu\bar\chi_q^m.
$$

At every good $v\nmid q$,

$$
\det\bigl(X-\bar\rho_\nu^{\mathrm{ss}}(\operatorname{Frob}_v)\bigr)
\equiv P_v(X)\pmod\nu.
$$

These congruences determine the residual semisimplification globally. They do not determine how a reducible semisimplification is extended on a chosen lattice.

### 5.3 Reducibility and absolute irreducibility

Residual irreducibility has three levels.

1. The representation may have no invariant line over $k_\nu$.
2. It may remain irreducible over every finite extension of $k_\nu$.
3. Its projective image may additionally satisfy the cohomological conditions required by a lifting theorem.

The second is **absolute irreducibility**. The first does not imply the second: a nonsplit Cartan can act irreducibly over $k_\nu$ but split over a quadratic residue-field extension.

One Frobenius polynomial irreducible over $k_\nu$ proves irreducibility over $k_\nu$, not absolute irreducibility. A practical absolute test uses two elements. Find $g$ whose eigenvalues are distinct over $\overline{k}_\nu$, and find $h$ that preserves neither eigenline of $g$. Then the group has no invariant line over $\overline{k}_\nu$.

Equivalently, for the residual semisimplification one may compute

$$
\operatorname{End}_{\overline{k}_\nu[G_F]}
(\bar V_\nu^{\mathrm{ss}}\otimes_{k_\nu}\overline{k}_\nu).
$$

For a semisimple residual representation, absolute irreducibility is equivalent to this endomorphism ring being $\overline{k}_\nu$. Without semisimplicity, a scalar endomorphism ring is only a Schur condition and does not rule out a nonsplit extension of distinct characters. For a chosen nonsemisimple lattice reduction one must separately rule out an invariant line. A direct image calculation, a two-Frobenius certificate, or an open-image theorem can prove absolute irreducibility. Compatibility alone cannot.

If $\bar\rho_\nu^{\mathrm{ss}}$ is absolutely irreducible, every stable-lattice reduction is already isomorphic to it. In the irreducible characteristic-zero representation, stable lattices are then homothetic. This is the precise situation in which a rational comparison can be upgraded to a comparison of residual lattices after scaling an intertwiner.

### 5.4 Adequacy and exceptional images

Adequacy is stronger than absolute irreducibility and weaker than demanding the largest possible image. For a finite subgroup $H\subseteq\operatorname{GL}(V)$ over a field $k$ of characteristic $q$, the useful form of the condition asks for:

$$
H^0(H,\operatorname{ad}^0V)=0,
$$

$$
H^1(H,k)=0,
\qquad
H^1(H,\operatorname{ad}^0V)=0,
$$

and that the semisimple elements of $H$ span $\operatorname{End}_k(V)$ after scalar extension. Equivalent formulations are often used, but every application must match the version required by its lifting theorem.

If $H$ contains $\operatorname{SL}_2(k_0)$ for a sufficiently large subfield $k_0$ and the residual characteristic is greater than $5$, the standard group-theoretic criterion gives adequacy. This is why a non-CM open-image theorem is so useful for flexible switching primes.

The criterion deliberately excludes the small characteristics. It does not prove inadequacy there; it says that the generic shortcut is unavailable. At $q=3$ the cohomology and spanning conditions must be calculated for the actual image, or a theorem specifically covering that image must be invoked.

An absolutely irreducible group of order prime to $q$ is often easy: averaging kills positive-degree cohomology, and irreducibility plus the matrix-algebra theorem makes its semisimple elements span. Dihedral and other small images still require the exact check because scalar kernels, projective quotients, and the requested adequacy convention can matter.

### 5.5 The image exceptional set

For a non-CM regular algebraic rank-two automorphic system, a finite-exception image theorem may provide a finite set

$$
B_{\mathrm{img}}
$$

of coefficient places such that outside it the residual image is absolutely irreducible and contains the predicted special linear group over the inner-twist residue field. Enlarging this set by all residue characteristics at most $5$ then gives adequacy by the safe large-characteristic criterion.

The hypotheses of such a theorem matter. One must account for inner twists, exclude the quadratic induction case, identify the correct projective trace field, and have the moving-prime conductor control needed to rule out infinitely varying Cartan-normalizer characters. Strong compatibility alone proves none of these image-theorem inputs.

If only a density-one image theorem is available, the exceptional set may be infinite of density zero. It cannot be relabeled finite. If no uniform theorem is available, a proposed $\nu$ may still be used after a direct absolute-irreducibility and adequacy calculation, but that calculation has no conclusion for other coefficient places.

In a CM system the large-image theorem is the wrong tool. The residual induction criterion will often give absolute irreducibility outside a finite set, while the projective image remains dihedral. That branch is treated explicitly in Chapter 12 and in the hostile diagnostic of Chapter 15.

## 6. Local invariants away from the new coefficient prime

The most robust transfer in changing prime occurs at a fixed base place whose residue characteristic differs from $q$. Strong compatibility identifies an entire algebraic Weil--Deligne pair there. This chapter records exactly what follows and exposes the places where only an almost-all statement is available.

### 6.1 Transport of Weil--Deligne data

Fix a finite place $v$ of $F$ with $p(v)\ne q$. Suppose $v\in\mathcal V_{\mathrm{str}}$ and let

$$
D_v=(r_v,N_v)
$$

be the common algebraic parameter. Then

$$
\operatorname{WD}_v(\rho_\nu)^{\mathrm{F\text{-}ss}}
\simeq\iota_\nu(r_v,N_v).
$$

This is a scalar-extension statement. Matrix coefficients of $r_v$ and $N_v$ are transported through $\iota_\nu$, and the resulting pair is considered up to isomorphism. There is no comparison of arbitrary matrices chosen independently in two completions.

Frobenius-semisimplification does not discard $N_v$. It replaces the Frobenius operator by its semisimple part while retaining the nilpotent operator. A statement that keeps only $r_v^{\mathrm{ss}}$ is weaker and cannot distinguish a Steinberg parameter from the adjacent two-character parameter.

At a place outside $S$, the common pair is unramified with $N_v=0$. At a bad place, the parameter can be principal series, special, or supercuspidal. The local Euler factor alone need not determine which.

### 6.2 Conductor, inertial type, and monodromy

The inertial type is

$$
\tau_v=r_v|_{I_v}.
$$

It records the finite part of inertia and does not include $N_v$. The conductor exponent is

$$
a_v(r_v,N_v)
=a_v(r_v)+\dim V^{I_v}
-\dim(\ker N_v)^{I_v}.
$$

Therefore strong compatibility gives, for every coefficient place away from $p(v)$,

$$
\tau_v(\rho_\lambda)=\iota_\lambda\tau_v,
$$

$$
\operatorname{rank}N(\rho_\lambda)
=\operatorname{rank}N_v,
$$

$$
a_v(\rho_\lambda)=a_v(r_v,N_v).
$$

For an unramified twist of Steinberg, the finite inertial type is trivial, $N_v$ has rank one, and the conductor exponent is one. Trivial inertial type is therefore not the same as an unramified representation.

The prime-to-coefficient conductor of the new member is obtained by multiplying these fixed factors over $v\nmid q$ in the strong range. The factor at $u\mid q$ is not computed by this formula. If the common system is strong at every finite place, one obtains one algebraic conductor ideal for the away-from-coefficient members; each individual member still requires separate treatment at its own coefficient-prime places.

### 6.3 Strong versus almost-all conclusions

Weak compatibility gives local information only for $v\notin S$ and $v\nmid q$. Thus it proves that the new member is unramified outside

$$
S\cup\{u:u\mid q\}.
$$

It says nothing about inertia at a member of $S$. A conductor or type at such a place can be imported only if one of the following is available:

- strong compatibility at that place;
- a global isomorphism with a representation whose actual local restriction has been proved to have the desired property;
- an independent geometric local calculation.

Even a global semisimple Chebotarev identification must be read correctly. If both global representations are semisimple and isomorphic, their actual local restrictions are isomorphic, so a proved local property transfers. But Chebotarev does not prove the local property on either side. A predicted automorphic type without local--global compatibility remains a prediction.

An all-place strong system gives all-place away-from-coefficient conclusions. A system strong only at semistable places gives conclusions only there. An almost-all good-polynomial statement cannot be promoted to either form by rhetoric.

### 6.4 The old coefficient prime after the switch

Let $w\mid\ell_0$ be a base place. For the original member $\rho_{\lambda_0}$, $w$ was a coefficient-prime place, described by de Rham or finite-flat theory. For the new member $\rho_\nu$, assuming $q\ne\ell_0$, it is an away-from-coefficient place.

If the system has a common $D_w$, strong compatibility gives

$$
\operatorname{WD}_w(\rho_\nu)^{\mathrm{F\text{-}ss}}
\simeq\iota_\nu D_w.
$$

It does not follow that $D_w$ is the Weil--Deligne parameter extracted from the old coefficient-prime period module. That identification is an additional all-prime local compatibility theorem. A crystalline old member may correspond to an unramified filtered Frobenius parameter, and a semistable old member may have a period monodromy operator, but neither comparison is supplied by strong compatibility away from coefficient primes alone.

Thus even the old coefficient prime illustrates the central rule: changing the coefficient prime changes which local theory applies at a fixed base place, but it does not move or erase that base place.

## 7. Integral reduction of local ramification

Characteristic-zero type and conductor can be common while residual ramification changes with the coefficient place. Reduction can merge characters or kill an integral unipotent parameter. This behavior is not an error; it is often the point of choosing a new prime. The task is to control it by integral certificates.

### 7.1 Finite inertia and character collision

Suppose the characteristic-zero inertial type at $v\nmid q$ factors through a finite group $H_v$. If $q\nmid|H_v|$, averaging makes the integral representation semisimple, prime-to-$q$ roots of unity reduce injectively, and invariant ranks are preserved under good integral reduction. In that range the finite type and its conductor survive.

If $q\mid|H_v|$, the tame $q$-primary part can collapse. Two algebraic characters $\theta_1$ and $\theta_2$ that are distinct in characteristic zero may satisfy

$$
\bar\theta_1=\bar\theta_2.
$$

To prevent this, choose $t\in I_v$ with

$$
c_{v,t}=\theta_1(t)-\theta_2(t)\ne0.
$$

Outside the coefficient places dividing $c_{v,t}$ and the denominators of the integral type, the two residual characters remain distinct. Finitely many witnesses control finitely many desired distinctions.

This argument proves only the distinctions witnessed. It does not prove global residual irreducibility, and it does not make the entire residual type constant when the integral model has not been fixed uniformly.

### 7.2 Tame unipotent inertia

Let $p=p(v)\ne q$. After killing finite scalar inertia, a rank-two special representation has tame action of the form

$$
\rho_\nu(\sigma)
=1+t_q(\sigma)N_{T,\nu},
$$

where

$$
t_q:I_v\longrightarrow\mathbf Z_q(1)
$$

is the $q$-primary tame character and $N_{T,\nu}$ is a square-zero integral operator tied to the chosen lattice. In a suitable integral basis one may write

$$
N_{T,\nu}=
\begin{pmatrix}0&c_{v,\nu}\\0&0\end{pmatrix}.
$$

The rational Weil--Deligne operator has rank one whenever $c_{v,\nu}\ne0$ in $E_\nu$. Its residual unipotent class is nonzero precisely when

$$
c_{v,\nu}\not\equiv0\pmod\nu.
$$

To make this statement uniform in $\nu$, the $c_{v,\nu}$ must arise from one algebraic integral parameter $c_v$ after inverting one fixed denominator ideal. Then the exceptional coefficient places are those dividing that ideal or $c_v$.

The scalar $c_v$ depends on the integral lattice and its normalization. The rational pair alone permits $N$ to be rescaled by a change of basis. Therefore the phrase “reduce $N$ modulo $\nu$” is meaningful only after an integral comparison with the actual inertia action has been supplied.

### 7.3 When monodromy disappears

Suppose $N_v\ne0$ in characteristic zero but $c_v\equiv0\pmod\nu$. Then the residual inertia on the chosen lattice can become trivial. The characteristic-zero statements remain unchanged:

$$
\operatorname{rank}N_v=1,
\qquad a_v(\rho_\nu)=1
$$

for an unramified Steinberg twist. The residual conductor can be zero.

This is an exceptional divisibility phenomenon, not a contradiction to strong compatibility. Strong compatibility concerns the rational parameter. The divisibility of $c_v$ concerns an integral lattice. At a finite set of coefficient places the two layers can behave differently.

In some applications one excludes these places in order to preserve a Steinberg component. In a hardly ramified construction one may deliberately choose a place where the residual monodromy vanishes. Either use is legitimate if the divisibility is checked. Treating nonzero rational monodromy as automatically nonzero residual monodromy is not.

### 7.4 Residual conductors and local certificates

Let $T_\nu$ be fixed. At $v\nmid q$, reduction cannot create inertia where the characteristic-zero action on the lattice is trivial. It can remove tame characters or unipotent extension classes. Under a uniform finite-type or tame-unipotent model, one obtains

$$
a_v(\bar\rho_{T_\nu})
\le a_v(\rho_\nu),
$$

with equality outside the coefficient places dividing the relevant certificates. This inequality is a conclusion of the explicit integral local analysis; it is not used as an unsupported universal conductor-semicontinuity theorem.

For a finite type of order prime to $q$, averaging preserves the ranks of invariants under every ramification subgroup, so the Artin and Swan terms are equal before and after reduction. For rank-one tame unipotent inertia, nonvanishing of the integral parameter makes the invariant space one-dimensional and the residual conductor one. Vanishing makes the inertia action trivial and the conductor zero.

At deeper wild places, one records the actual finite quotient, its filtration, and integral invariant ranks. A single conductor exponent does not determine enough data to prove that reduction preserves it.

### 7.5 Ramification away from the common bad set

For every chosen stable lattice, weak compatibility gives

$$
\bar\rho_{T_\nu}
\text{ unramified outside }
S\cup\{u:u\mid q\}.
$$

At a place outside this set, the characteristic-zero inertia action is the identity, so its reduction is the identity. No lattice ambiguity arises.

Inside $S$, define

$$
S_{\mathrm{res}}(\nu)
=\{v\in S:v\nmid q,
\ \bar\rho_{T_\nu}|_{I_v}\ne1\}.
$$

This residual bad set can be smaller than $S$. It is computed, not inferred from the common characteristic-zero conductor. A controlled prime switch records for every $v\in S$ whether ramification is required to survive, allowed to disappear, or irrelevant to the next argument.

## 8. Places above the new coefficient prime

The switch is most delicate precisely where it is meant to help: at base places above the new rational prime. Away-from-coefficient Weil--Deligne compatibility stops there. Hodge theory and integral geometry must take over, and neither is forced by the good Frobenius polynomials.

### 8.1 The missing comparison

Fix $u\mid q$. For every coefficient place $\lambda$ with $\ell(\lambda)\ne q$, strong compatibility may provide a common pair $D_u$. For the new member $\rho_\nu$, the local representation

$$
\rho_\nu|_{G_{F_u}}
$$

is a $q$-adic representation at residue characteristic $q$. The Weil--Deligne construction used away from the coefficient prime does not apply directly to it. If it is semistable, its period module has its own Frobenius and monodromy; if it is crystalline, that monodromy is zero.

The assertion

$$
\operatorname{WD}
\bigl(D_{\mathrm{st}}(\rho_\nu|_{G_{F_u}})\bigr)^{\mathrm{F\text{-}ss}}
\simeq\iota_\nu D_u
$$

is an additional comparison theorem. It is not part of strong compatibility away from coefficient primes. Without it, behavior at the base place that has become the coefficient prime is not determined by the common away-from-coefficient parameter.

This logical gap persists even if all good Frobenius polynomials are known. Those polynomials determine the global semisimple member once it has been constructed; they do not prove that its local period module belongs to a chosen comparison category.

### 8.2 Crystalline, semistable, and ordinary members

A $q$-adic representation is crystalline when its crystalline period module has full dimension. It is semistable when its semistable period module has full dimension. There are implications

$$
\text{crystalline}
\Longrightarrow
\text{semistable}
\Longrightarrow
\text{de Rham}.
$$

Crystalline does not mean unramified. The cyclotomic character is crystalline and ramified at $q$. A good-reduction elliptic curve has a crystalline Tate module with weights $\{0,1\}$. A multiplicative elliptic curve has a semistable noncrystalline Tate module with rank-one period monodromy.

Ordinarity is additional structure. In the weight-two rank-two setting it asks for a $G_{F_u}$-stable filtration

$$
0\longrightarrow V^+\longrightarrow V
\longrightarrow V^-\longrightarrow0
$$

whose labelled Hodge weights and unramified twists occur in the prescribed order, typically with a cyclotomic-type line and an unramified quotient after a finite-order twist. A crystalline representation need not be ordinary; supersingular good reduction is the basic counterexample.

Accordingly, a switching theorem can transfer “crystalline,” “semistable,” or “ordinary” only from a coefficient-prime comparison theorem that asserts that property for the new member. Hodge weights alone do not determine any of the three categories.

### 8.3 Finite flatness is integral

Finite flatness concerns a chosen torsion lattice. Let $T_\nu$ be stable. The desired conclusion at $u\mid q$ is that, for every $n$, the finite module

$$
T_\nu/\varpi_\nu^nT_\nu
$$

is the generic fiber of a finite locally free commutative group scheme over $\mathcal O_{F_u}$ with the required coefficient action, compatibly in $n$ when a tower is needed.

This conclusion follows from a good-reduction abelian scheme when $T_\nu$ is the integral coefficient factor and the coefficient idempotent is integral. It can also follow from an integral Fontaine--Laffaille object in its exact range. It does not follow merely from:

- strong compatibility at places away from $q$;
- de Rham or crystalline status of the rational representation;
- the labelled weights $\{0,1\}$ without a lattice theorem;
- the existence of some stable lattice;
- finite flatness of a different coefficient-prime member.

An arbitrary stable lattice in a rational representation is not automatically the Tate lattice of the geometric factor used to prove finite flatness. When the downstream argument needs a finite-flat deformation condition or a discriminant bound, the actual model is part of the hypothesis.

### 8.4 An all-prime local compatibility certificate

For a fixed base place $u$, the strongest useful certificate has three parts.

1. **Away from $q$:** an algebraic pair $D_u=(r_u,N_u)$ describes every member whose coefficient characteristic differs from $q$.
2. **At $q$:** the new member is de Rham, crystalline, or semistable with the declared labelled weights, and its period parameter agrees with $D_u$ when such an agreement is claimed.
3. **Integrally:** a named stable lattice belongs to the required finite-flat, ordinary, or semistable integral category.

Only the first part comes from strong compatibility away from coefficient primes. The second is a rational coefficient-prime comparison. The third is an integral theorem. A proof may use any subset, but it must not let one part impersonate another.

For the weight-two passage to $3$, the standard clean certificate is: $3$ is unramified in $F$; the $3$-adic member is crystalline with labelled weights $\{0,1\}$ at every $u\mid3$; and the chosen lattice is supplied by compatible finite-flat group schemes or by the integral classification of the next chapter.

## 9. The Fontaine--Laffaille threshold

Low weights over an unramified base admit an exact integral linear-algebra description. This is the cleanest route from a crystalline weight-two member to finite-flat torsion, but its hypotheses are sharp enough that they must be displayed. In particular, the theory used here does not cover a ramified base merely because the ramification is mild, and it does not turn arbitrary Hodge weights into type $(0,1)$.

### 9.1 The exact range

Let $K/\mathbf Q_q$ be unramified of residue degree $d$, and assume

$$
q>2.
$$

The Fontaine--Laffaille full-faithfulness interval has length at most

$$
q-2.
$$

After a Tate twist, rational Hodge weights in

$$
[0,q-2]
$$

lie in the low-weight comparison range. The endpoint is included. For a weight-two representation with weights $\{0,1\}$, the inequality is

$$
1\le q-2,
$$

which is equivalent to $q\ge3$. Thus $q=3$ is allowed and is the smallest allowed odd prime.

Two restrictions must be separated. The interval condition is the range for the filtered comparison. Finite-flat group schemes correspond to the specific normalized weights $0$ and $1$. A crystalline representation of weights $\{0,2\}$ at $q=5$ lies within the broad interval but is not thereby a finite-flat type-$(0,1)$ representation. Likewise, a Tate twist that normalizes rational weights may change the integral group-scheme problem and the determinant.

The coefficient ring may be the ring of integers $\mathcal O$ in a finite extension of $\mathbf Q_q$, with residue field larger than $\mathbf F_q$. The unramified hypothesis concerns the local base $K$, not the coefficient field. Coefficient actions are endomorphisms of the integral object and must be included in its structure.

### 9.2 The type-zero-one criterion

Let $T$ be a free rank-two $\mathcal O$-module with continuous $G_K$-action, and put $V=T\otimes_{\mathcal O}\operatorname{Frac}(\mathcal O)$. We say that $T$ is a **Fontaine--Laffaille lattice of type $(0,1)$** if it is obtained from a strongly divisible integral object whose filtration, in every unramified embedding factor, is concentrated in degrees $0$ and $1$.

The integral criterion is the following.

**Theorem 9.1 (exact low-weight finite-flat criterion).** Assume that $K/\mathbf Q_q$ is unramified and $q>2$. For a rank-two lattice $T$, the following two packages are equivalent.

1. The quotients $T/\varpi^nT$ are supplied, compatibly in $n$, by coefficient-linear finite-flat commutative group schemes over $\mathcal O_K$, and their classified filtered modules have weights $0$ and $1$.
2. The lattice $T$ is the Galois realization of a compatible integral Fontaine--Laffaille system of type $(0,1)$.

Under either package, $V$ is crystalline with labelled Hodge--Tate weights contained in $\{0,1\}$. If in addition

$$
\det T\simeq\mathcal O(1),
$$

then at every embedding label the two weights are exactly

$$
\{0,1\},
$$

and the filtered rank-one step has rank one.

Conversely, the rational assertion

$$
V\text{ is crystalline with weights }\{0,1\}
$$

implies the finite-flat conclusion for $T$ only after an integral comparison theorem places that chosen $T$ in the Fontaine--Laffaille essential image. The rational assertion alone does not name the required integral object.

This final sentence is part of the criterion. It is the distinction between an exact integral theorem and a slogan about low Hodge weights.

### 9.3 Proof of the criterion

The proof is a passage through the established integral classification, and each direction uses a different part of it.

Assume first that the compatible finite-flat group schemes in package 1 are given. Raynaud full faithfulness applies because

$$
e(K)=1<q-1.
$$

It makes their models and coefficient actions rigid through the prescribed generic identifications. The covariant torsion Fontaine--Laffaille classification sends each finite-flat quotient to an exact filtered divided-Frobenius module of weights $0$ and $1$. Compatibility of the group-scheme quotients under $n$ gives compatibility of these filtered modules. Their inverse system is precisely the integral object in package 2.

Conversely, start with package 2. At every coefficient level, reduce the integral filtered object modulo $\varpi^n$. The exact covariant classification produces a coefficient-linear finite-flat group scheme, and functoriality with coefficient quotients makes these models compatible. Their generic Galois modules are $T/\varpi^nT$. This gives package 1.

It remains to prove the exact rank statement under cyclotomic determinant. Exterior multiplication gives a perfect alternating generic pairing

$$
T/\varpi^nT\times T/\varpi^nT
\longrightarrow(\mathcal O/\varpi^n)(1).
$$

Raynaud full faithfulness extends it uniquely to the finite-flat models. Under the covariant classification, Cartier duality with the Tate twist sends a filtration step of rank $r_\tau$ in a rank-two factor to one of rank

$$
2-r_\tau.
$$

The determinant pairing identifies the object with this dual, so

$$
r_\tau=2-r_\tau.
$$

Hence $r_\tau=1$ for every label. The two normalized weights are therefore one $0$ and one $1$ at every embedding. Passing through all $n$ proves the assertion for $T$, and rational comparison gives crystallinity and the labelled weights of $V$.

No part of this proof applies an away-from-$q$ Weil--Deligne parameter at $q$. The input is integral classification over the unramified local base.

### 9.4 Weights outside the range and ramified bases

If the normalized weight span exceeds $q-2$, the preceding classification cannot be invoked. For example, weights $\{0,q-1\}$ lie just outside the interval. Reducing a crystalline lattice in that range can exhibit phenomena not controlled by the low-weight category. One must use a different integral theory and state its hypotheses.

If $K/\mathbf Q_q$ is ramified, Raynaud full faithfulness may still hold when

$$
e(K)<q-1,
$$

but the explicit unramified Fontaine--Laffaille classification used in Theorem 9.1 has not thereby been supplied. Model uniqueness is not the same as model existence or classification. In particular, none of the power-series or type-$(0,1)$ conclusions from the unramified theory is imported merely from this inequality.

A geometric group scheme can still prove finite flatness over a ramified base. If an elliptic curve has good reduction over $K$, its $q^n$-torsion is finite flat for every $n$, independently of whether the clean Fontaine--Laffaille description is being used. The distinction is between a direct geometric source and an unavailable classification shortcut.

Potential finite flatness after a ramified extension is weaker than finite flatness over $K$. Descent requires compatible integral descent data. It is not obtained by restricting the generic Galois module back to $G_K$.

### 9.5 Ordinary and nonordinary finite-flat objects

The type-$(0,1)$ category contains both ordinary and nonordinary objects. In the ordinary case, a stable rank-one subobject has one weight and the quotient has the other. In the standard orientation the generic residual representation has the form

$$
0\longrightarrow k(1)\otimes\bar\alpha
\longrightarrow\bar V
\longrightarrow k\otimes\bar\beta
\longrightarrow0,
$$

with unramified characters $\bar\alpha,\bar\beta$ after the appropriate finite-order twist. The permitted extension classes are the unit, or peu ramifiée, Kummer classes. A valuation-direction Kummer class is not a finite-flat residual base point in the clean unramified odd range.

In the nonordinary or supersingular case, there need be no stable line over the base residue field. The object is still finite flat and has one filtration line in each Fontaine--Laffaille factor; that filtration line is not the same thing as a $G_K$-stable ordinary line.

Therefore the implications are

$$
\text{ordinary finite flat}
\Longrightarrow
\text{finite flat of type }(0,1),
$$

but not conversely. A prime switch meant for an ordinary lifting theorem must carry an ordinary certificate in addition to finite flatness.

## 10. Designing a controlled switch

The preceding chapters identified several finite exceptional sets, each with a different source. A useful selection theorem must keep them separate until the end. This chapter assembles them and proves that a flexible rational prime can satisfy all compatible conditions simultaneously.

### 10.1 The finite exceptional-set ledger

After making the final coefficient enlargement, define the following sets of coefficient places.

**Denominator set $B_{\mathrm{den}}$.** These places divide the fixed ideal inverted to define common integral local models, coefficient actions, or bad-place parameters.

**Local-collision set $B_{\mathrm{loc}}$.** These places divide a nonzero difference of inertial characters, a nonzero monodromy minor, a Tate thickness, or another local survival certificate.

**Pairing set $B_{\mathrm{pair}}$.** These places divide the index of a chosen lattice in its dual or a denominator in the integral polarization.

**Image set $B_{\mathrm{img}}$.** This is the finite exceptional set of an explicitly stated non-CM image theorem. If the available theorem is only density one, this symbol must instead be marked density-zero and is not included in a finite union.

**Small-characteristic set $B_{\mathrm{small}}$.** For the safe generic adequacy criterion this contains every coefficient place of residue characteristic at most $5$.

**Automorphic comparison set $B_{\mathrm{aut}}$.** These are the finitely many places at which the selected integral automorphic realization, coefficient projector, or local comparison theorem is unavailable, when the relevant theorem has such a finite-exception range.

Put

$$
B=B_{\mathrm{den}}\cup B_{\mathrm{loc}}
\cup B_{\mathrm{pair}}\cup B_{\mathrm{img}}
\cup B_{\mathrm{small}}\cup B_{\mathrm{aut}}.
$$

Every set in this union must be proved finite. The coefficient places above rational primes ramified in $F$ or in a selection field can also be excluded, but it is often clearer to put their underlying rational primes in a separate rational set

$$
P_{\mathrm{field}}.
$$

For a fixed prime $3$, one does not exclude $B_{\mathrm{small}}$. One replaces its generic adequacy conclusion by a direct calculation and checks whether the selected place belongs to every other part of $B$.

### 10.2 Local survival conditions

Fix a finite set $T$ of base places and divide it into three disjoint parts:

$$
T=T_{\mathrm{keep}}\sqcup
T_{\mathrm{kill}}\sqcup T_{\mathrm{rat}}.
$$

At $T_{\mathrm{keep}}$, a residual type, character distinction, or nonzero monodromy class must survive. The corresponding nonzero certificates enter $B_{\mathrm{loc}}$.

At $T_{\mathrm{kill}}$, the next argument requires residual ramification to disappear. This is not achieved by avoiding a finite set. It is a divisibility condition at the proposed coefficient place, such as

$$
c_v\equiv0\pmod\nu.
$$

For a flexible prime, simultaneous divisibility at several fixed nonzero algebraic integers usually permits only finitely many choices rather than a positive-density set. A construction that needs deliberate conductor drop is therefore an arithmetic search among divisors, not an application of Chebotarev.

At $T_{\mathrm{rat}}$, only the characteristic-zero parameter is needed. Strong compatibility supplies it for $v\nmid q$ without an integral survival condition.

This three-way division resolves an apparent contradiction. The same monodromy-divisibility phenomenon is a failure when a Steinberg component must be preserved and a feature when a hardly ramified residual representation is desired.

### 10.3 Flexible-prime selection theorem

We can now state the selection result.

**Theorem 10.1 (selection of a flexible coefficient prime).** Let $\mathscr S$ be a rank-two switching datum over $F$ and $E$. Assume:

1. every coefficient enlargement and every uniform integral model has already been made;
2. $B$ of Section 10.1 is finite;
3. the non-CM finite-exception image theorem used to define $B_{\mathrm{img}}$ applies;
4. $T\subseteq\mathcal V_{\mathrm{str}}$, and the desired local residual conditions are survival conditions at the finite set $T_{\mathrm{keep}}$, certified as in Chapters 2 and 7;
5. the system has a uniform coefficient-prime theorem in the desired weight range, and an integral finite-flat conclusion is requested only where that theorem or geometry supplies the chosen lattice; and
6. the proposed splitting and congruence conditions define a nonempty conjugacy-stable Chebotarev set in a finite Galois selection field $L_{\mathrm{sel}}/\mathbf Q$.

Then there are infinitely many rational primes $q$ and places $\nu\mid q$ such that:

- $q$ avoids the rational primes below $B$ and every field-discriminant exception;
- $q$ has the prescribed Frobenius class in $L_{\mathrm{sel}}$;
- if complete splitting was prescribed, then $E_\nu\simeq\mathbf Q_q$ and $k_\nu=\mathbf F_q$;
- $q$ is different from the residue characteristics of all places in $T$;
- $\bar\rho_\nu$ is absolutely irreducible and adequate;
- every certified residual distinction at $T_{\mathrm{keep}}$ survives;
- every common rational local parameter at $T$ transfers to $\rho_\nu$; and
- at $u\mid q$, the new member has exactly the coefficient-prime rational and integral properties supplied by hypothesis 5.

The set of such rational primes has the Chebotarev density of the prescribed class after deleting finitely many primes.

**Proof.** Form the finite rational set consisting of the primes below $B$, the primes ramified in $F$ or $L_{\mathrm{sel}}$, the residue characteristics of $T$, and the finitely many weight-range or geometric exceptions. Chebotarev supplies the desired Frobenius class outside this set with the stated density. Complete splitting gives the coefficient conclusion. Avoidance of $B_{\mathrm{img}}$ gives absolute irreducibility and adequacy; avoidance of $B_{\mathrm{loc}}$ and $B_{\mathrm{den}}$ makes every integral certificate remain nonzero; strong compatibility gives the rational local parameters; and the uniform coefficient-prime theorem gives the final local assertion at $q$. Each conclusion has therefore been supplied by its own hypothesis. $\square$

The theorem does not include $T_{\mathrm{kill}}$. Deliberately forcing fixed algebraic parameters to vanish modulo $\nu$ is normally incompatible with a positive-density selection statement and must be handled by direct divisibility.

### 10.4 What density does not prove

Several tempting conclusions lie outside Theorem 10.1.

Chebotarev does not prove that $\bar\rho_\nu$ is large; it merely supplies primes after an image theorem has declared all but finitely many places large. It does not prove coefficient-prime crystallinity or finite flatness. It does not compare period modules. It does not make a local monodromy parameter divisible by $\nu$ unless the chosen prime divides that parameter.

Complete splitting in $E$ does not make $q$ split in $F$. Avoiding the discriminant of $F$ makes the local bases unramified, which is enough for Theorem 9.1, but their residue degrees can still exceed one.

Finally, positive density is irrelevant to a prescribed small prime. The fixed point $q=3$ either passes the ledger or it does not. No abundance theorem can replace that calculation.

## 11. Automorphy across coefficient primes

Prime switching is often described as transferring modularity. The precise mechanism is more rigid: one automorphic representation has realizations at every coefficient place, and common Frobenius polynomials identify the compatible-system members with those realizations. Potential automorphy over an auxiliary base field is a different statement and remains over that field until descent is proved.

### 11.1 One automorphic representation, every member

Let $\pi$ be a regular algebraic cuspidal automorphic representation with coefficient field contained in the final $E$. Assume its Galois representations

$$
\rho_{\pi,\lambda}:G_F\longrightarrow
\operatorname{GL}_2(E_\lambda)
$$

exist at every finite coefficient place in the required realization range. Suppose for one place $\lambda_0$,

$$
\rho_{\lambda_0}^{\mathrm{ss}}
\simeq\rho_{\pi,\lambda_0}^{\mathrm{ss}}.
$$

Then the good polynomials of $\mathcal R$ and $\pi$ agree algebraically at almost every base place. For every $\nu$, Chebotarev gives

$$
\rho_\nu^{\mathrm{ss}}
\simeq\rho_{\pi,\nu}^{\mathrm{ss}}
$$

after aligning coefficients. Thus one automorphic representation supplies automorphy of the entire semisimple compatible system.

This is not a new modularity-lifting argument at every prime. It is uniqueness inside an already constructed automorphic family. The local properties available at $\nu$ are exactly those proved for $\rho_{\pi,\nu}$ or independently for $\rho_\nu$; good-polynomial equality does not strengthen the local--global comparison theorem.

If the system's member and the automorphic realization are irreducible, the semisimplification notation can be removed. If residual absolute irreducibility is needed to align chosen lattices, it must be checked at $\nu$.

### 11.2 Potential automorphy over an extension

Suppose instead that one begins with

$$
\rho_{\lambda_0}:G_F\longrightarrow
\operatorname{GL}_2(E_{\lambda_0})
$$

and proves only that, for a finite totally real extension $L/F$,

$$
\rho_{\lambda_0}|_{G_L}
\simeq\rho_{\Pi,\widetilde\lambda_0}
$$

for an automorphic representation $\Pi$ over $L$. The family attached to $\Pi$ is a compatible system of representations of $G_L$. It produces a new member

$$
\rho_{\Pi,\widetilde\nu}:G_L
\longrightarrow\operatorname{GL}_2(E_{\Pi,\widetilde\nu}),
$$

not automatically a representation of $G_F$.

If an independent compatible system $\mathcal R$ over $F$ already exists, restriction and common polynomials can identify

$$
\rho_\nu|_{G_L}^{\mathrm{ss}}
\simeq\rho_{\Pi,\widetilde\nu}^{\mathrm{ss}}.
$$

This proves potential automorphy of the new $G_F$-member. It still does not prove automorphy over $F$.

If no system over $F$ has been constructed, potential automorphy at $\lambda_0$ alone does not manufacture $G_F$-representations at the other coefficient primes. The system lives over $L$, and that field status is part of the conclusion.

### 11.3 Solvable descent with an extending member

Descent is available under exact extra hypotheses. Let $L/F$ be solvable Galois with a tower

$$
F=F_0\subset F_1\subset\cdots\subset F_r=L
$$

of cyclic extensions. Suppose an irreducible arithmetic representation

$$
r_\nu:G_F\longrightarrow\operatorname{GL}_2(\overline{\mathbf Q}_q)
$$

has restriction associated with a cuspidal $\Pi/L$. The extending representation supplies coherent descent data.

At the top cyclic step, choose an automorphic descent. Its Galois representation and $r_\nu|_{G_{F_{r-1}}}$ have isomorphic irreducible restrictions to $G_{F_r}$. Clifford theory says that they differ by a character of the cyclic quotient. Twist the automorphic descent by the inverse character. The corrected descent now has the desired Galois representation. Repeat down the tower.

This produces a cuspidal automorphic representation over $F$ whose $\nu$-adic realization is $r_\nu$, provided cuspidality, local type, and central character survive every step. The bottom automorphic representation then supplies its entire compatible system.

The extending $r_\nu$ is what selects coherent twists. Without it, invariance of the top automorphic representation gives a descent torsor, not a canonical compatible chain. If a restriction becomes reducible, scalar Clifford theory no longer applies and the dihedral branch must be analyzed explicitly.

### 11.4 The descent failure test

Before claiming descent, ask:

1. Is $L/F$ Galois and solvable, or is a different descent theorem available?
2. Does the automorphic representation remain cuspidal at every base-change layer?
3. Is there a quadratic self-twist causing the first failure of cuspidality?
4. Does an irreducible representation over the lower field select the quotient-character correction?
5. Do those corrections preserve determinant, polarization, and every local type?
6. Are the coefficient embeddings and fields aligned throughout?

A negative answer to any question stops the descent. In particular, a general potential-modularity field need not be Galois or solvable. Passing to its Galois closure can change residual images and local fields. Prime switching may continue over the field where the compatible system is known, but descent to the original base is a separate theorem.

## 12. Passage to the rational prime 3

The rational prime $3$ lies inside the exact weight-two Fontaine--Laffaille range and is small enough for powerful global classifications. It is also too small for generic residual-image shortcuts. A successful passage to $3$ therefore combines an especially clean integral local condition with an especially careful image calculation.

### 12.1 Coefficient places above 3

Let

$$
3\mathcal O_E=\prod_{\nu\mid3}\nu^{e_\nu}.
$$

For each choice $\nu$,

$$
k_\nu\simeq\mathbf F_{3^{f_\nu}},
\qquad
E_\nu/\mathbf Q_3
\text{ has ramification index }e_\nu.
$$

The system provides one $3$-adic member for every such $\nu$. Their good Frobenius polynomials are conjugate scalar realizations of the same $P_v$, but their residual images can differ. A proof may compare all choices and select one; it may not speak of a unique $3$-adic member unless the coefficient field has a unique place above $3$ or the choice is immaterial for a proved reason.

If $f_\nu=1$, the residual representation can be written over $\mathbf F_3$ after its field of definition has been verified. If $f_\nu>1$, it is two-dimensional over $\mathbf F_{3^{f_\nu}}$. Viewing it over $\mathbf F_3$ makes it $2f_\nu$-dimensional and leaves the rank-two theory.

An enlargement $E'/E$ cannot lower $f_\nu$. For a place $\nu'\mid\nu$,

$$
f(\nu'/3)=f(\nu'/\nu)f_\nu.
$$

Thus a degree-one coefficient place at $3$ is a genuine arithmetic input. It cannot be arranged after the fact by adjoining more coefficients.

There is a different descent possibility. If the residual trace and determinant functions lie in $\mathbf F_3$ and the absolutely irreducible representation has a proved scalar descent datum with vanishing cocycle obstruction, it may admit an $\mathbf F_3$-model. This is coefficient descent, not coefficient enlargement, and it must be proved.

### 12.2 Residual image possibilities

Put $k=\mathbf F_{3^f}$ and let

$$
H=\bar\rho_\nu(G_F)\subseteq\operatorname{GL}_2(k).
$$

The projective image gives a useful first division.

1. **Reducible or Borel case.** Over $\overline k$, the group fixes a line. The residual semisimplification is a sum of two characters.
2. **Cartan-normalizer case.** A group contained in a Cartan is absolutely reducible. A group contained in its normalizer but not the Cartan can be absolutely irreducible and has dihedral projective image.
3. **Exceptional case.** The projective image can be one of $A_4$, $S_4$, or $A_5$ when the field permits the corresponding embedding.
4. **Defining-characteristic or subfield case.** The projective image contains a group $\operatorname{PSL}_2(k_0)$, or lies between the corresponding projective special and general linear groups, for a subfield $k_0\subseteq k$.

The remaining subgroups with nontrivial normal $3$-subgroup lie in a Borel and hence belong to the reducible branch. This is the rank-two projective subgroup classification in the form needed for image auditing.

When $f=1$, small coincidences occur:

$$
|\operatorname{GL}_2(\mathbf F_3)|=48,
$$

$$
\operatorname{PGL}_2(\mathbf F_3)\simeq S_4,
\qquad
\operatorname{PSL}_2(\mathbf F_3)\simeq A_4.
$$

Thus a label such as “contains the special linear group” no longer guarantees that the image lies in a stable large-characteristic regime. The group is simultaneously a defining-characteristic group and an exceptional small group.

The determinant restricts which full inverse images can occur. In the weight-two cyclotomic case,

$$
\det\bar\rho_\nu=\bar\chi_3,
$$

whose image over a totally real field contains the sign $-1$ at complex conjugation. The determinant does not determine the projective image and does not prove absolute irreducibility.

### 12.3 Adequacy in characteristic 3

No finite-exception theorem that proves adequacy only after excluding residue characteristics at most $5$ says anything at $3$. The actual group $H$ must be checked.

First verify that $H$ has no invariant line over $\overline k$. After this separate absolute-irreducibility check, a direct adequacy audit consists of four computations:

$$
\operatorname{End}_{\overline k[H]}(\overline k^2)
=\overline k,
$$

$$
H^1(H,\overline k)=0,
$$

$$
H^1(H,\operatorname{ad}^0\overline k^2)=0,
$$

and verification that semisimple elements span

$$
\operatorname{End}_{\overline k}(\overline k^2).
$$

Given absolute irreducibility, the first records the scalar centralizer, equivalently the required $H^0$-vanishing in this odd-characteristic rank-two setting. Without the separate irreducibility check, a scalar centralizer alone would not suffice for a nonsemisimple representation. The next two computations detect small quotient and adjoint-cohomology exceptions. The last prevents all semisimple elements from lying in a proper linear subspace of the matrix algebra.

If $|H|$ is prime to $3$ and the representation is absolutely irreducible, averaging gives both cohomology vanishings, every element is semisimple, and the matrix-algebra theorem gives the spanning condition. This supplies an elementary adequate branch. It must be applied to the full image, not merely to the projective group.

If $3\mid|H|$, no such averaging argument applies. Full image, projective $A_4$ or $S_4$, and subfield special-linear cases require their own calculation. The result may be adequate or inadequate; the word “large” is not a proof in characteristic $3$.

When adequacy fails, the prime switch itself remains valid. What fails is a downstream lifting theorem whose hypotheses include adequacy. A specialized small-image lifting theorem or the explicit classification of the next stage may replace it, but that replacement must be named.

### 12.4 Reducible and dihedral branches

If

$$
\bar\rho_\nu^{\mathrm{ss}}
=\bar\alpha\oplus\bar\beta,
$$

then a chosen lattice may reduce as a split sum or as a nonsplit extension in either direction. The compatible system determines only the two characters. An ordinary argument can use a selected stable line when the integral local and global hypotheses supply it. An irreducible modularity-lifting theorem cannot be applied.

For an elliptic curve over $F$, a $G_F$-stable line in $E[3]$ is a rational cyclic subgroup of order $3$ and hence a rational $3$-isogeny. Absence of such an isogeny proves irreducibility over $\mathbf F_3$ but does not by itself exclude a nonsplit-Cartan representation that becomes reducible over $\mathbf F_9$. Absolute irreducibility still needs the endomorphism or two-element test.

In the dihedral case there is a quadratic extension $M/F$ and a residual character $\bar\theta$ such that

$$
\bar\rho_\nu
\simeq\operatorname{Ind}_{G_M}^{G_F}\bar\theta.
$$

It is absolutely irreducible precisely when

$$
\bar\theta\ne\bar\theta^\sigma.
$$

Its projective image remains dihedral. Some such images are adequate by the prime-to-$3$ argument; others require direct checking. In every case the non-CM large-image theorem is irrelevant, and restriction to $G_M$ makes the representation reducible. Automorphic induction and self-twist bookkeeping replace the generic branch.

## 13. Integral local structure at 3

At $3$, the weight-two interval is exactly $[0,1]$. This gives a sharp local classification when the base is unramified, but it does not choose the coefficient place, the lattice, or the residual image. This chapter states the complete local package to be checked after those choices have been made.

### 13.1 Finite-flat type zero one

Assume $3$ is unramified in $F$. For every $u\mid3$,

$$
F_u/\mathbf Q_3
$$

is unramified. Let $T_\nu$ be a chosen stable lattice in the new member. The clean type-$(0,1)$ conclusion is:

$$
T_\nu/\varpi_\nu^nT_\nu
$$

has a compatible coefficient-linear finite-flat model over $\mathcal O_{F_u}$ for every $n$, and the classified filtration has one weight $0$ and one weight $1$ at every embedding.

There are two standard proofs.

- If the system comes from an elliptic curve or an integral rank-two factor of a good-reduction abelian scheme, use its $3$-power torsion group schemes. The coefficient action and projector must be integral.
- If an integral comparison theorem identifies $T_\nu$ with a Fontaine--Laffaille lattice, apply Theorem 9.1. The equality $1=3-2$ shows that the endpoint is permitted.

The determinant audit is

$$
\det T_\nu\simeq\mathcal O_\nu(1)
$$

up to the declared finite-order character. With a nontrivial finite-order factor at $3$, one must check that its integral model and Hodge weight are compatible with the claimed type. It cannot simply be erased from the determinant.

If $3$ is ramified in $F$, the clean classification invoked above is unavailable. Direct good-reduction geometry can still give finite flatness, and the later discriminant bound then uses the actual local ramification index. A proof based only on the phrase “weights $\{0,1\}$” fails.

### 13.2 Tame inertia weights

Finite-flat type $(0,1)$ constrains the tame inertia weights of the residual representation. Let $F_u/\mathbf Q_3$ be unramified of residue degree $d$. After extending the coefficient residue field, the tame characters are expressed in fundamental characters indexed by the $d$ residue embeddings.

In a reducible tame semisimplification one can write

$$
\bar\rho_\nu|_{I_u}^{\mathrm{ss}}
=\bar\eta_1\oplus\bar\eta_2,
$$

and, up to unramified twists,

$$
\bar\eta_j
=\prod_{i=0}^{d-1}\omega_{d,i}^{a_{j,i}},
\qquad a_{j,i}\in\{0,1\}.
$$

Cyclotomic determinant and type $(0,1)$ force

$$
\{a_{1,i},a_{2,i}\}=\{0,1\}
$$

at every label. These are the tame weight digits.

In an irreducible or supersingular shape, restriction to the unramified quadratic extension splits into two Frobenius-conjugate characters of niveau $2d$. Their base-$3$ digits are again the $0$--$1$ digits supplied by the classified filtered object, and their product is the cyclotomic tame character. The precise cyclic arrangement of the digits is part of that object; finite flatness does not select one universal arrangement for all $d$.

For $d=1$, the two familiar possibilities, up to unramified twist and semisimplification, are

$$
1\oplus\omega
$$

in the ordinary case and

$$
\omega_2\oplus\omega_2^3
$$

in the irreducible supersingular case, where $\omega$ is the niveau-one fundamental character and $\omega_2$ has niveau two. Their determinants are both $\omega$.

This is a statement about tame inertia and semisimplification. Wild inertia at $3$ and nonsplit extension classes are not determined by the tame digits alone. A classification argument requiring those data must read the full finite-flat object.

### 13.3 Ordinary and supersingular shapes

For a good ordinary elliptic curve, the connected--étale sequence of the $3$-divisible group gives a local filtration whose residual form is, after unramified twists,

$$
0\longrightarrow k_\nu(1)
\longrightarrow E[3]\otimes k_\nu
\longrightarrow k_\nu\longrightarrow0.
$$

The extension may be split or nonsplit. In the clean unramified range, a finite-flat extension class lies in the unit Kummer subspace; a valuation class is excluded. A chosen ordinary line is integral data and can matter to a deformation problem.

For good supersingular reduction, no $G_{F_u}$-stable ordinary line need exist. The finite-flat group scheme has connected height two special fiber, and the residual representation can be irreducible. In the clean unramified Fontaine--Laffaille range it still has type $(0,1)$ and the same cyclotomic determinant.

At multiplicative reduction over a place above $3$, the Tate module is semistable noncrystalline. Its generic extension class is controlled by the Tate parameter. It is not covered by the good-reduction finite-flat assertion, and a valuation-direction class can obstruct a finite-flat model of the full residual extension. Semistable is not a substitute for finite flat.

### 13.4 The 3-adic local checklist

For every base place $u\mid3$, record:

1. whether $F_u/\mathbf Q_3$ is unramified;
2. the chosen coefficient place $\nu$ and its coefficient ramification and residue degree;
3. the labelled weights of $\rho_\nu|_{G_{F_u}}$;
4. whether the rational representation is crystalline, semistable noncrystalline, or only de Rham;
5. the source of the chosen lattice $T_\nu$;
6. the finite-flat models of its quotients, when claimed;
7. the ordinary line or supersingular shape, when relevant;
8. the determinant and integral pairing; and
9. any comparison between its period parameter and the common away-from-$3$ datum at $u$.

Passing this checklist at every $u\mid3$ is the coefficient-prime part of producing a controlled $3$-adic companion. None of the entries is supplied by the factorization of $3$ in the coefficient field alone.

## 14. The hardly ramified package

The phrase “hardly ramified” is useful only after it is made numerical. The relevant object for the discriminant argument is the finite residual module and the field cut out by its kernel, not the infinite $3$-adic representation by itself. This chapter defines the package and derives the exact bounds that follow from finite flatness and the local ledger.

### 14.1 Definition and conductor record

Let $T_\nu$ be a chosen stable lattice in a $3$-adic member and put

$$
M=T_\nu/\varpi_\nu T_\nu.
$$

Let $S_0$ be a finite set of base places away from $3$, and choose real numbers $R_v\ge0$ for $v\in S_0$. We say that $M$ carries a **hardly ramified package relative to $(S_0,\{R_v\})$** if:

1. $M|_{G_{F_u}}$ has a finite-flat model for every $u\mid3$;
2. $M$ is unramified outside $S_0\cup\{u:u\mid3\}$;
3. for $v\in S_0$, the local field cut out by $M$ has last upper ramification break at most $R_v$; and
4. its determinant, oddness source, coefficient field, dimension, and actual residual image are recorded.

The package is **strictly hardly ramified** when $S_0$ is empty. If ramification at $v\in S_0$ is tame, record its inertia order $e_v(M)$ as a sharper substitute for $R_v=0$.

The prime-to-$3$ conductor ledger follows from direct local data. At every finite place outside $S_0$ and the places above $3$, the exponent is zero. At a tame $v\in S_0$, it is

$$
a_v(M)=\operatorname{codim}M^{I_v},
$$

so it is $1$ for nonzero rank-one unipotent inertia and at most $2$ in rank two. At a place with last upper break $R_v$, the fixed-space formula gives the coarse bound

$$
a_v(M)\le2(1+R_v).
$$

Whenever an exact residual type has been computed, its exact conductor replaces this coarse inequality.

Weak compatibility proves clause 2 with $S_0$ initially replaced by the common bad set $S$. Integral local calculations decide which places can be removed. Strong compatibility supplies characteristic-zero types, while local certificates determine their residual survival or collapse. Thus strict hardly ramified behavior never follows from the good polynomials alone.

### 14.2 Local break and different bounds at 3

Fix $u\mid3$ and write

$$
e_u^0=v_u(3)=e(F_u/\mathbf Q_3).
$$

Also write

$$
f_u^0=[k_u:\mathbf F_3]=f(F_u/\mathbf Q_3).
$$

Let $L_u/F_u$ be the local extension cut out by $M$. Since $3\in\varpi_\nu\mathcal O_\nu$, the module $M=T_\nu/\varpi_\nu T_\nu$ is killed by $3$. Together with its finite-flat model, the finite-flat ramification theorem gives

$$
G_{F_u}^r\text{ acts trivially on }M
\quad\text{for every}
\quad
r>e_u^0\left(1+\frac12\right)-1.
$$

Thus the last upper break is at most

$$
R_u^{\mathrm{ff}}=\frac{3e_u^0}{2}-1.
$$

If $e(L_u/F_u)$ is the relative ramification index and $d(L_u/F_u)$ the different exponent upstairs, then

$$
d(L_u/F_u)
\le
e(L_u/F_u)\frac{3e_u^0}{2}-1,
$$

and hence

$$
\frac{d(L_u/F_u)}{e(L_u/F_u)}
<\frac{3e_u^0}{2}.
$$

When $F_u/\mathbf Q_3$ is unramified, this becomes

$$
R_u^{\mathrm{ff}}=\frac12,
\qquad
\frac{d(L_u/F_u)}{e(L_u/F_u)}<\frac32.
$$

The rank-two conductor bound obtained from the upper cutoff is

$$
a_u(M)\le2\left(1+R_u^{\mathrm{ff}}\right)=3e_u^0.
$$

Here $a_u(M)$ denotes the fixed-space ramification number obtained by integrating codimensions along the finite image filtration. It is not a prime-to-$3$ automorphic conductor factor, which by convention omits places above the coefficient prime. The inequality is intentionally coarse. The different bound is the decisive one for root discriminants and is independent of the rank and image size.

Finite flatness, not crystallinity alone, is what proves these ramification bounds. The theorem uses the integral group law and applies to any chosen finite-flat model; it does not require uniqueness of that model.

### 14.3 The global root-discriminant bound

Let

$$
L=F(M)
$$

be the finite Galois extension cut out by the full residual action. The local bounds at all places above $3$, together with the upper cutoffs at $S_0$, give

$$
\boxed{
\operatorname{rd}(L)
<\operatorname{rd}(F)\,
3^{3/2}
\prod_{v\in S_0}
(Nv)^{(1+R_v)/[F:\mathbf Q]}.
}
$$

If $S_0$ is empty, this is

$$
\boxed{
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\,3^{3/2}.
}
$$

The proof is short because the local work has already been done. At $u\mid3$, the normalized different contribution is strictly less than $3e_u^0/2$. Since

$$
\sum_{u\mid3}e_u^0f_u^0=[F:\mathbf Q],
$$

the local norm powers combine to $3^{3/2}$. At $v\in S_0$, the last-break estimate gives normalized contribution less than $1+R_v$. Multiplying the local contributions and retaining the base factor $\operatorname{rd}(F)$ gives the displayed inequality.

The clean factor $3^{3/2}$ remains valid even when $3$ ramifies in $F$, provided the finite-flat models over the actual $\mathcal O_{F_u}$ exist. The local ramification indices cancel in the global degree sum. What fails over a ramified base is the automatic use of the unramified Fontaine--Laffaille criterion, not the finite-flat discriminant theorem.

### 14.4 Degree and auxiliary-prime refinements

If $k_\nu=\mathbf F_{3^f}$, then

$$
[F(M):F]\le
|\operatorname{GL}_2(\mathbf F_{3^f})|
=(3^{2f}-1)(3^{2f}-3^f).
$$

For $f=1$, this gives

$$
[F(M):F]\le48.
$$

The actual residual image gives the exact degree and should replace this bound whenever known. A reducible or dihedral image can cut out a much smaller field, while restriction of scalars to $\mathbf F_3$ does not improve the field and changes the represented dimension.

At a tame auxiliary place $v$, use the exact normalized different contribution

$$
1-\frac1{e_v(M)}
$$

instead of the coarse $1+R_v=1$. The global bound improves to

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)3^{3/2}
\prod_{v\in S_0}
(Nv)^{(1-1/e_v(M))/[F:\mathbf Q]}
$$

when every auxiliary place is tame.

If a place in $S$ becomes residually unramified because an integral monodromy parameter vanishes, remove it from $S_0$ entirely. Retaining a tame factor there is valid but weaker. If residual ramification has not been computed, it may not be removed merely because a characteristic-zero conductor is small.

### 14.5 What is exported to the discriminant argument

The hardly ramified record passed forward is

$$
\mathscr H_3=
\left(
F,M,k_\nu,\operatorname{im}\bar\rho_\nu,
S_0,\{R_v\},
\{\mathcal G_u\}_{u\mid3},
\det M,
\operatorname{rd}_{\max}
\right),
$$

where $\mathcal G_u$ is a chosen finite-flat model and $\operatorname{rd}_{\max}$ is the explicit right side of Section 14.3 or its tame refinement.

Book 64 supplies the upper-break, different, and root-discriminant inequalities just used. Book 65 compares such upper bounds with global discriminant lower bounds, and Book 66 analyzes the surviving hardly ramified $3$-adic and residual possibilities. Their lower-bound and classification conclusions are exported to, not proved in, this book.

The export must retain the field $F$, its root discriminant and signature, the exact degree or image bound, and every auxiliary local contribution. Writing only “small discriminant” loses the numerical statement needed for classification.

## 15. Four hostile diagnostics

Abstract ledgers are most useful when they survive examples designed to break them. The four diagnostics in this chapter isolate the main failure mechanisms: integral monodromy divisibility, quadratic induction, residue-field growth, and a complete successful switch from an elliptic curve to its $3$-adic member.

### 15.1 A Steinberg parameter vanishing modulo the new prime

Let $v$ have residue characteristic $p$, and consider a compatible system with an unramified Steinberg twist at $v$. For every coefficient place $\lambda$ with $\ell(\lambda)\ne p$, the rational parameter has

$$
D_v=\bigl(\theta\|\cdot\|_v\oplus\theta,N_v\bigr),
\qquad \operatorname{rank}N_v=1.
$$

Its inertial type is scalar, and if $\theta$ is unramified its conductor exponent is one.

Suppose the system comes from an elliptic curve with multiplicative reduction at $v$. Let $q_{E,v}$ be a Tate parameter and put

$$
m_v=v(q_{E,v})=v(\Delta_{\min}).
$$

For a coefficient prime $q\ne p$, the geometric Tate lattice has tame inertia, after a suitable basis, of the form

$$
\rho_{E,q}(\sigma)=
\begin{pmatrix}
1&m_vt_q(\sigma)\\
0&1
\end{pmatrix}.
$$

The rational monodromy is nonzero for every $q\ne p$. Reduction modulo $q$ gives trivial inertia exactly when

$$
q\mid m_v.
$$

Thus at such a coefficient prime

$$
a_v(V_qE)=1,
\qquad
a_v(E[q])=0.
$$

Strong compatibility has not failed. It correctly keeps rank-one rational monodromy. The integral thickness $m_v$ is the separate datum that vanishes on reduction.

This diagnostic has two opposite readings. If the next lifting problem requires a Steinberg residual component, every coefficient place dividing $m_v$ is exceptional. If the goal is a residual representation unramified away from $3$, divisibility $3\mid m_v$ removes $v$ from the residual bad set. Both conclusions require the displayed calculation.

### 15.2 A CM or dihedral system

Let $M/F$ be quadratic and let $\Theta=\{\theta_\lambda\}$ be a compatible character system of $G_M$. Put

$$
\rho_\lambda=
\operatorname{Ind}_{G_M}^{G_F}\theta_\lambda.
$$

Then

$$
\rho_\lambda|_{G_M}
\simeq\theta_\lambda\oplus\theta_\lambda^\sigma
$$

and

$$
\rho_\lambda\otimes\eta_{M/F}
\simeq\rho_\lambda.
$$

The common quadratic self-twist forces the projective image into a Cartan normalizer. No non-CM large-image theorem applies.

Choose a base prime $w$ of $M$ for which

$$
\theta(\operatorname{Frob}_w)
-\theta^\sigma(\operatorname{Frob}_w)\ne0.
$$

After clearing the fixed denominators of a common integral character model, outside the finitely many coefficient places dividing those denominators or this nonzero difference, the residual inducing characters remain distinct and the induction is absolutely irreducible over $F$. At a place dividing every available distinction, the residual induction can become reducible. This is the exact exceptional-divisibility test.

Even at a good residual place, restriction to $G_M$ is reducible. A base change containing $M$ destroys cuspidality of the automorphic induction and destroys residual irreducibility. A potential-modularity field must therefore be checked for intersection with $M$ and for distinction of the restricted characters.

At a coefficient place above $3$, adequacy is a separate group calculation. If the full dihedral image has order prime to $3$, absolute irreducibility and averaging give adequacy. If a scalar or character quotient contributes $3$-torsion, the four conditions of Section 12.3 must be checked directly. The correct branch is explicit induction, not generic special-linear image.

### 15.3 Residue degree greater than one

Suppose $3$ is inert and unramified in a quadratic coefficient field $E$. There is one place $\nu\mid3$, with

$$
E_\nu/\mathbf Q_3
\text{ unramified quadratic},
\qquad
k_\nu=\mathbf F_9.
$$

The companion is

$$
\rho_\nu:G_F\longrightarrow
\operatorname{GL}_2(E_\nu),
$$

and its residual member is two-dimensional over $\mathbf F_9$. The elementary degree bound is

$$
[F(\bar\rho_\nu):F]
\le|\operatorname{GL}_2(\mathbf F_9)|
=(81-1)(81-9)=5760.
$$

There is no two-dimensional $\mathbf F_3$-representation in this statement. Restriction of scalars gives dimension four, while adjoining more coefficients leaves the residue degree divisible by two. If a later classification accepts only subgroups of $\operatorname{GL}_2(\mathbf F_3)$, the switch has not reached its input.

To repair the situation, one needs a genuine $\mathbf F_3$ coefficient descent. It requires the residual character values to lie in $\mathbf F_3$, an absolutely irreducible field-of-definition theorem, and vanishing of the descent cocycle. None follows from inertness, from compatibility, or from characteristic-zero coefficient enlargement.

All rational conclusions remain valid. The member has the common good polynomials, determinant, purity, and strong local parameters in the established range. The failure is exactly the residual coefficient field.

### 15.4 A successful elliptic-curve switch to 3

Consider the elliptic curve over $\mathbf Q$

$$
A:\qquad y^2+y=x^3-x.
$$

Its discriminant is

$$
\Delta_A=37.
$$

Thus it has good reduction at $3$ and multiplicative reduction at $37$. Its compatible system has coefficient field $\mathbf Q$, so there is one coefficient place above every rational prime and no residue-degree ambiguity.

The $3$-adic companion is the covariant Tate module

$$
\rho_{A,3}:G_{\mathbf Q}
\longrightarrow\operatorname{GL}_2(\mathbf Z_3).
$$

At every $p\ne3,37$,

$$
\det\bigl(X-\rho_{A,3}(\operatorname{Frob}_p)\bigr)
=X^2-a_p(A)X+p,
$$

the same polynomial read by every Tate module. The determinant is $\chi_3$, the representation is odd and pure of weight one, and $V_3A=T_3A\otimes\mathbf Q_3$ is crystalline with weights $\{0,1\}$ at $3$. The finite-flat models for the lattice quotients are the group schemes

$$
\mathcal A[3^n]
$$

of the good-reduction elliptic scheme over $\mathbf Z_3$.

The $x$-coordinate $3$-division polynomial is

$$
\psi_3(x)=3x^4-6x^2+3x-1.
$$

Modulo $2$ it is $x^4+x+1$, which is irreducible. A cubic resolvent is

$$
3z^3+6z^2+4z+5;
$$

the rational-root test makes it irreducible. Finally,

$$
\operatorname{disc}(\psi_3)
=-3^3\,37^2
$$

is not a square. The Galois group of $\psi_3$ is therefore $S_4$. Since it is the projective action on the four cyclic subgroups of $A[3]$, the projective residual image is

$$
\operatorname{PGL}_2(\mathbf F_3)\simeq S_4.
$$

The determinant is surjective and the central extension does not split, so

$$
\bar\rho_{A,3}(G_{\mathbf Q})
=\operatorname{GL}_2(\mathbf F_3).
$$

Indeed, an index-two complement to the scalar center would give a second nontrivial character of $\operatorname{GL}_2(\mathbf F_3)$; its abelianization is generated by determinant, whose kernel projects only to $A_4$. Hence no such complement exists. The image is absolutely irreducible. A direct finite-group adequacy calculation passes: its abelianization has no quotient of order $3$, the cocycle equations on elementary and diagonal matrices give

$$
H^1\bigl(\operatorname{GL}_2(\mathbf F_3),
\operatorname{ad}^0\mathbf F_3^2\bigr)=0,
$$

and its semisimple matrices span $M_2(\mathbf F_3)$. This is a small-image calculation, not an application of the large-characteristic criterion.

At $37$, the Tate thickness is

$$
v_{37}(\Delta_A)=1,
$$

so the residual monodromy does not disappear modulo $3$. The residual inertia is tame unipotent of order $3$, with conductor exponent one. Hence the hardly ramified package has

$$
S_0=\{37\}
$$

and the tame refinement gives

$$
\operatorname{rd}(\mathbf Q(A[3]))
<3^{3/2}37^{2/3}.
$$

The degree is exactly $48$. Every step of the switch is now certified: coefficient place, common polynomials, determinant, oddness, finite flatness at $3$, residual image, adequacy, and the one auxiliary tame place. This is what a successful elliptic-curve switch looks like when no hypothesis is hidden.

## 16. The prime-switching theorem package

We now assemble the book into reusable statements. The first theorem treats a flexible or preselected coefficient place with an explicit exceptional ledger. The second specializes to $3$ and replaces generic largeness by direct hypotheses. The third extracts the hardly ramified residual field and its numerical bounds.

### 16.1 Controlled switching theorem

**Theorem 16.1 (controlled change of coefficient prime).** Let $F$ be a number field and let

$$
\mathcal R=\{\rho_\lambda\}_\lambda
$$

be a rank-two semisimple compatible system over a final coefficient field $E$. Let $\lambda_0\mid\ell_0$ be an original coefficient place and $\nu\mid q$ a new one, with $q\ne\ell_0$. Assume:

1. the weak compatible-system data consist of one finite bad set $S$ and common polynomials $P_v(X)\in E[X]$;
2. the determinant is $\psi_\lambda\chi_{\ell(\lambda)}^m$, and purity, a polarization, total oddness when defined, and labelled Hodge data have been proved in their stated ranges;
3. strong compatibility has been proved at every place in a declared set $\mathcal V_{\mathrm{str}}$;
4. one member $\rho_{\lambda_0}$ is associated with a regular algebraic cuspidal automorphic representation $\pi$, and the realizations $\rho_{\pi,\lambda}$ exist over the aligned coefficient field at all coefficient places under consideration;
5. for a finite set $T$ of base places, every desired residual local distinction is represented by a uniform algebraic integral model and a nonzero certificate;
6. at every $u\mid q$, a coefficient-prime theorem gives the claimed de Rham, crystalline, semistable, or ordinary property, and a finite-flat conclusion is requested only for a named lattice with the required compatible integral models; and
7. either $\nu$ lies outside the explicit finite image exceptional set of an applicable non-CM theorem and has residue characteristic in that theorem's adequacy range, or absolute irreducibility and adequacy at this particular $\nu$ have been checked directly. In a CM or dihedral system, replace this clause by the explicit induction and image calculation.

Let

$$
B_{\mathrm{sw}}
=B_{\mathrm{den}}\cup B_{\mathrm{loc}}
\cup B_{\mathrm{pair}}\cup B_{\mathrm{img}}
\cup B_{\mathrm{aut}}
$$

be the finite set attached to these hypotheses, with $B_{\mathrm{img}}$ omitted from this union when the direct image-calculation or explicit CM/dihedral branch of hypothesis 7 is used. If $\nu\notin B_{\mathrm{sw}}$, except for a deliberately imposed and separately verified conductor-drop divisibility, then:

1. the new member $\rho_\nu$ exists and, after a common local coefficient extension,
   $$
   \rho_\nu^{\mathrm{ss}}
   \simeq\rho_{\pi,\nu}^{\mathrm{ss}};
   $$
2. at every $v\notin S$ with $v\nmid q$, its Frobenius polynomial is $\iota_\nu P_v(X)$;
3. it has determinant $\psi_\nu\chi_q^m$ and, in the ranges stated in hypothesis 2, the common purity weight, polarization, total oddness, and labelled Hodge data;
4. for $v\in\mathcal V_{\mathrm{str}}$ with $v\nmid q$, its Frobenius-semisimple Weil--Deligne pair is $\iota_\nu D_v$, including $N_v$, so its characteristic-zero inertial type, monodromy rank, and conductor exponent are the common ones;
5. for $v\in T$ with $v\nmid q$, every residual local distinction certified in hypothesis 5 survives; an intentionally vanishing certificate gives exactly the separately computed conductor drop;
6. the chosen residual semisimplification is absolutely irreducible and adequate under hypothesis 7; and
7. at $u\mid q$, the new member has exactly the rational and integral local properties in hypothesis 6, no more.

If $\rho_\nu$ and $\rho_{\pi,\nu}$ are irreducible, the semisimplification signs in clause 1 can be removed. If a full residual extension or finite-flat model is used, its chosen lattice remains part of the conclusion.

**Proof.** Selection of $\rho_\nu$ is part of the compatible system. Weak compatibility proves clause 2. Equality with the automorphic good polynomials at $\lambda_0$, followed by Chebotarev at $\nu$, proves clause 1. The compatible determinant, weight, polarization, parity, and Hodge ledgers prove clause 3. Strong compatibility proves clause 4. Avoidance of the finitely many denominators and nonzero certificates proves the survival assertion in clause 5; a vanishing assertion is instead the stated direct divisibility calculation. The image theorem or direct group calculation proves clause 6. The coefficient-prime comparison and integral model prove clause 7. No clause is inferred from another. $\square$

### 16.2 The 3-adic companion theorem

**Theorem 16.2 (controlled $3$-adic companion).** In Theorem 16.1 fix a coefficient place $\nu_3\mid3$. Assume additionally:

1. its residue field $k_{\nu_3}=\mathbf F_{3^f}$ and coefficient ramification are explicitly recorded; if a two-dimensional $\mathbf F_3$ endpoint is required, assume $f=1$ or prove coefficient descent;
2. for every $u\mid3$, either $F_u/\mathbf Q_3$ is unramified and the chosen lattice $T_{\nu_3}$ is an integral Fontaine--Laffaille lattice of type $(0,1)$, or compatible direct geometric finite-flat models for all quotients $T_{\nu_3}/\varpi_{\nu_3}^nT_{\nu_3}$ are supplied over the actual local base;
3. the rational member is crystalline with labelled weights $\{0,1\}$ at every $u\mid3$, this rational assertion being recorded separately from the integral models in hypothesis 2;
4. $\bar\rho_{\nu_3}$ is absolutely irreducible, and adequacy is verified by the four-condition characteristic-$3$ calculation, or a named reducible, dihedral, or small exceptional branch is retained for separate treatment;
5. every desired away-from-$3$ residual local behavior has been checked on $T_{\nu_3}$, including every monodromy parameter meant to survive or vanish; and
6. the automorphic family and coefficient alignment are those of hypothesis 4 of Theorem 16.1.

Then $\rho_{\nu_3}$ is a controlled $3$-adic companion of $\rho_{\lambda_0}$. At every $v\notin S$ with $v\nmid3$, it has the common good Frobenius polynomial; it has the compatible determinant and, in their proved ranges, oddness, polarization, purity, and Hodge labels; it has the common strong local parameters at every declared place away from $3$; it has a finite-flat lattice at $3$ precisely under hypothesis 2, which is a Fontaine--Laffaille lattice of type $(0,1)$ in the unramified branch of that hypothesis; and it has the residual image and away-from-$3$ ramification explicitly recorded in hypotheses 4--5. The companion is the $3$-adic realization of the same automorphic representation over $F$ as in Theorem 16.1.

**Proof.** The nonimage arguments of Theorem 16.1 apply with $q=3$. In the absolutely irreducible adequate branch, hypothesis 4 supplies the required characteristic-$3$ replacement for its generic image clause. In a named reducible, dihedral, or small exceptional branch, clause 6 of Theorem 16.1 is omitted and only the explicitly recorded image conclusion above is retained. Theorem 9.1 proves the type-$(0,1)$ conclusion in the unramified local branch, while direct geometry proves the alternative branch. Chapter 7 proves exactly the recorded residual behavior away from $3$. $\square$

There is a separate potential-only variant. Under hypotheses 1--5 above, suppose instead that the compatible system $\mathcal R$ has already been constructed over $F$, while its restriction to a named finite extension $L/F$ is identified with the compatible family of an automorphic representation $\Pi/L$. The same local, residual, and finite-flat conclusions hold for the $G_F$-member $\rho_{\nu_3}$, and Chebotarev after restriction identifies $\rho_{\nu_3}|_{G_L}^{\mathrm{ss}}$ with the $\nu_3$-adic realization of $\Pi$. The automorphy conclusion is then over $L$, not $F$. It descends to $F$ only when the solvable-Galois, extending-member, irreducibility, cuspidality, and twist-control hypotheses of Section 11.3 are fulfilled.

The theorem does not assert that such a place $\nu_3$ has residue degree one, that its residual image is adequate, or that finite flatness follows from strong compatibility. Those are hypotheses because $3$ is fixed.

### 16.3 The hardly ramified corollary

**Corollary 16.3 (hardly ramified residual companion).** Under Theorem 16.2, put

$$
M=T_{\nu_3}/\varpi_{\nu_3}T_{\nu_3}.
$$

Assume the local audit produces a finite set $S_0$ away from $3$ such that $M$ is unramified outside $S_0\cup\{u:u\mid3\}$, and an upper cutoff $R_v$ at every $v\in S_0$. Then $M$ has the hardly ramified package of Chapter 14. For $L=F(M)$,

$$
[L:F]\le
(3^{2f}-1)(3^{2f}-3^f),
$$

and

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)3^{3/2}
\prod_{v\in S_0}
(Nv)^{(1+R_v)/[F:\mathbf Q]}.
$$

At a tame $v$, replace its factor by

$$
(Nv)^{(1-1/e_v(M))/[F:\mathbf Q]}.
$$

If $S_0$ is empty, then

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)3^{3/2}.
$$

At each $u\mid3$, the last upper break is at most

$$
\frac{3e(F_u/\mathbf Q_3)}2-1,
$$

and the normalized different exponent is strictly less than

$$
\frac{3e(F_u/\mathbf Q_3)}2.
$$

**Proof.** Weak compatibility and the chosen local calculations give the ramification set. Finite flatness gives the local bounds at $3$. The residual image gives the degree bound. The global finite-flat discriminant formula with the recorded auxiliary cutoffs gives the root-discriminant inequality. $\square$

### 16.4 Proof architecture and source ledger

The theorem package has five independent engines.

```text
common algebraic polynomials  --->  new rational member
            |
            +--------------->  Chebotarev automorphic identification

strong local parameters      --->  rational type, conductor, monodromy
integral local certificates  --->  residual survival or conductor drop
coefficient-prime geometry   --->  crystalline and finite-flat data at q
residual image theorem       --->  irreducibility and adequacy
```

The arrows cannot be interchanged. Good polynomials do not prove bad-place compatibility. Strong rational monodromy does not prove residual monodromy. Crystallinity does not select a finite-flat lattice. A large characteristic-zero monodromy group does not prove adequacy at $3$. Potential automorphy does not prove descent.

The explicit exceptional set is correspondingly modular. A denominator exception can obstruct integral comparison without affecting residual image. An image exception can leave every local parameter intact. A monodromy divisor can deliberately remove one residual conductor factor. Keeping these causes separate is what makes the theorem reusable.

## 17. Failure modes and audit protocol

A prime switch can look correct at almost every Frobenius class while failing at the single local or integral point needed by the application. The safest final step is a hostile audit: assume each ambiguous noun has been used in its strongest possible sense, then demand the hypothesis that justifies that strength.

### 17.1 Prime, place, and embedding failures

**Coefficient residue degree greater than one.** If $k_\nu=\mathbf F_{q^f}$ with $f>1$, the residual member is not two-dimensional over $\mathbf F_q$. Coefficient enlargement cannot lower $f$, and restriction of scalars changes dimension.

**Unspecified place above $q$.** A rational prime can have several coefficient places with different completions and residual images. “Choose $q$” is incomplete until $\nu\mid q$ is named.

**Base place confused with coefficient place.** Changing from $\lambda_0$ to $\nu$ does not move $v$. It changes whether $p(v)$ equals the coefficient characteristic. Every local statement must display both $v$ and $\ell(\lambda)$ when ambiguity is possible.

**Coefficient embedding omitted.** The equality of local polynomials across completions means that both are images of $P_v\in E[X]$. Bad-place parameters and Hodge labels likewise require compatible embeddings. An entrywise comparison of arbitrary local matrices is meaningless.

**Coefficient enlargement made too late.** A prime split in $E$ need not split in a later $E'$. Flexible selection must occur after the final field is fixed. At $3$, every enlargement consequence is audited directly.

### 17.2 Residual and monodromy failures

**Residual reducibility.** Compatibility does not prevent $\bar\rho_\nu^{\mathrm{ss}}$ from being a sum of characters. One irreducible Frobenius polynomial over $k_\nu$ does not prove absolute irreducibility. Use a two-element test, or apply the endomorphism test to the semisimplification; scalar endomorphisms of a nonsemisimple reduction alone do not suffice.

**Lattice treated as canonical.** Only residual semisimplification is lattice independent. A nonsplit extension, stable line, ordinary orientation, or exact inertia matrix belongs to a named lattice.

**Adequacy inferred at a small prime.** The large-characteristic sufficient criterion excludes $3$. Compute the actual image cohomology and semisimple span, or retain a named exceptional branch.

**CM system fed into a non-CM theorem.** A quadratic self-twist forces a dihedral projective image. Residual irreducibility is decided by the inducing characters, and restriction to the quadratic field makes every member reducible.

**Monodromy reduced without an integral model.** The rational operator $N_v$ can be rescaled. Its residual nonvanishing is meaningful only through an integral tame action tied to the chosen lattice.

**Monodromy vanishing overlooked.** At a Steinberg place, a coefficient prime dividing the integral thickness can make residual inertia trivial while rational conductor remains one. This can invalidate a minimal Steinberg condition or improve a hardly ramified package.

**Residual conductor copied from characteristic zero.** Equality needs invariant-rank or monodromy certificates. Without them, compute the residual action itself.

### 17.3 Hodge and finite-flat failures

**Hodge weights outside the Fontaine--Laffaille range.** After normalization, the span must be at most $q-2$. Type $(0,1)$ requires the actual weights $0$ and $1$, not merely some weights inside the broad interval.

**Ramified local base.** The explicit criterion of Theorem 9.1 assumes $F_u/\mathbf Q_q$ unramified and $q>2$. Raynaud uniqueness under $e<q-1$ does not supply the missing unramified classification. Direct geometry may still supply finite flatness.

**Crystalline confused with unramified.** The cyclotomic character is the standard counterexample. Good reduction at a coefficient-prime place gives crystalline, generally ramified, cohomology.

**Crystalline weights confused with an integral lattice.** A rational type does not select a stable lattice or compatible finite-flat quotients. Name the integral comparison or group scheme.

**Semistable confused with finite flat.** Multiplicative reduction gives a semistable noncrystalline Tate module, and its valuation-direction residual extension need not be finite flat.

**Finite flat confused with ordinary.** In the unramified Fontaine--Laffaille range, supersingular good reduction is finite flat of type $(0,1)$ without an ordinary stable line.

**Old coefficient-prime period data copied to the new away member.** The common $D_v$ and the old period module agree only under an all-prime local comparison certificate.

### 17.4 Compatibility and descent failures

**Weak compatibility at a bad place.** Common good polynomials do not determine the chosen bad-place inertial type or monodromy from the definition. A local comparison theorem or geometry is required.

**Strong compatibility promoted beyond its range.** If it is known only at semistable places, no supercuspidal or deep-type place is added. If it is all-place away from coefficient primes, it still stops at the moving coefficient-prime places.

**Chebotarev used as local--global compatibility.** Chebotarev identifies global semisimplifications. It does not prove the predicted local parameter or identify lattices.

**One automorphic lift confused with all lifts.** An automorphic representation supplies its own compatible family. A different characteristic-zero lift of the same residual representation requires a modularity-lifting theorem to become automorphic.

**Potential automorphy descended without control.** A system constructed over $L$ remains over $L$. Descent needs a suitable field tower, cuspidality, coherent character corrections, local control, and usually an extending irreducible arithmetic representation.

**Restriction assumed to preserve image.** Restriction can make a dihedral representation reducible and can shrink any residual image if the extension meets its fixed field. Disjointness must be proved.

### 17.5 A hostile audit checklist

Before declaring a switch complete, verify the following list line by line.

1. **Fields:** Are the base field, final coefficient field, and all auxiliary fields fixed before $q$ is selected?
2. **Places:** Are $v$ of $F$, $\lambda_0$ of $E$, $\nu$ of $E$, and their rational residue characteristics never conflated?
3. **Embeddings:** Does every cross-completion comparison pass through one algebraic datum and named embeddings?
4. **Good data:** Are the common Frobenius polynomials stated only at places away from the relevant coefficient characteristic?
5. **Strong range:** Is the exact set $\mathcal V_{\mathrm{str}}$ visible?
6. **Monodromy:** Is $N$ retained after Frobenius-semisimplification, and is any reduction of it tied to an integral lattice?
7. **Conductor:** Is each characteristic-zero or residual conductor identified by the correct local theorem?
8. **Lattice:** Is every nonsplit residual extension or stable line attached to a named lattice?
9. **Image:** Is absolute irreducibility proved over the algebraic residue field? Is adequacy proved in the actual characteristic?
10. **Coefficient prime:** At every $u\mid q$, are Hodge labels, crystalline or semistable status, ordinarity, and finite flatness separately sourced?
11. **Weight range:** Are $q>2$, unramified local base, and type $(0,1)$ all present when Theorem 9.1 is used?
12. **Residue degree:** Is $k_\nu$ stated, and is a required $\mathbf F_q$-model proved rather than assumed?
13. **Exceptional set:** Is each set finite for a stated reason, with density-zero sets not mislabeled finite?
14. **Automorphy:** Is the automorphic representation defined at the new coefficient place, and is Chebotarev used only for semisimple identification?
15. **Descent:** Is the field where automorphy is proved the field named in the conclusion?
16. **Hardly ramified record:** Are the finite module, image, ramification set, local cutoffs, degree, base root discriminant, and strict numerical upper bound all retained?

Passing this audit is stronger than producing an attractive commutative diagram. It certifies that every arrow in the diagram has a theorem behind it.

## 18. Interfaces and conclusion

The controlled $3$-adic companion is not the final arithmetic conclusion. It is a precisely prepared input for two later stages: classification of small-ramification $3$-adic representations and the final modular-method synthesis. This last chapter states what those stages receive and what remains for them to prove.

### 18.1 Interface to the classification of hardly ramified representations

Book 66, the next classification stage, receives the tuple

$$
\left(
F,E_{\nu_3},\mathcal O_{\nu_3},\varpi_{\nu_3},
\rho_{\nu_3},T_{\nu_3},M,
k_{\nu_3},\operatorname{im}\bar\rho_{\nu_3},
\det\rho_{\nu_3},
\{H_{\tau_0}\},
\mathscr G_3,
S_0,\{R_v\},
\operatorname{rd}_{\max}
\right).
$$

Here $\mathscr G_3$ records, for every $u\mid3$, the source and compatible finite-flat models for the quotients $T_{\nu_3}/\varpi_{\nu_3}^nT_{\nu_3}$, together with the Fontaine--Laffaille object only in the unramified branch. Retaining $E_{\nu_3}$, $\mathcal O_{\nu_3}$, and $\varpi_{\nu_3}$ keeps the coefficient ramification and the relation between the $3$-power and $\varpi_{\nu_3}$-power filtrations visible.

Its entries have already been proved to satisfy:

- oddness or the exact polarization parity over the totally real base;
- determinant $\psi_{\nu_3}\chi_3^m$;
- the common good Frobenius polynomials and purity;
- compatible finite-flat model towers at places above $3$ only under the exact local hypotheses, and Fontaine--Laffaille type $(0,1)$ only in the unramified Fontaine--Laffaille branch;
- a directly calculated residual image, with coefficient residue degree visible;
- an explicit residual ramification set and conductor record away from $3$;
- the local upper-break and different bounds at $3$; and
- the strict global root-discriminant upper bound.

The classification stage may combine this input with global discriminant lower bounds, finite-group analysis, and arithmetic restrictions on reducible or dihedral images. It must not assume a smaller residue field, a smaller ramification set, or a stronger finite-flat category than the tuple provides.

In particular, the upper bound

$$
\operatorname{rd}(F(M))
<\operatorname{rd}(F)3^{3/2}
\prod_{v\in S_0}
(Nv)^{(1+R_v)/[F:\mathbf Q]}
$$

is exported, not reproved or analytically interpreted here. The later conclusion that only certain fields or representations can occur belongs to that classification.

### 18.2 Interface to the modular-method synthesis

Book 71, the final modular-method stage, receives two linked but distinct objects.

First, it receives the original member and its arithmetic origin: for a Frey-type curve this includes its cyclotomic determinant, good and multiplicative local behavior, residual representation, and the exact field over which automorphy or potential automorphy has been proved.

Second, it receives the controlled $3$-adic companion and the identification through the compatible system. At good places,

$$
P_v(X)
=X^2-a_vX+\psi(v)(Nv)^m
$$

belongs to both members through their coefficient embeddings. At fixed bad places away from $3$, the strong parameters agree in the declared range. At $3$, the companion carries the separately proved finite-flat or semistable local package. Its residual image enters the small-prime classification.

The final synthesis may then combine:

- modularity or potential modularity of the compatible family;
- the $3$-adic classification just described;
- rational-isogeny alternatives when a residual representation is reducible;
- level lowering or lifting with the exact residual local components; and
- the Diophantine properties of the original curve.

Changing the coefficient prime does not itself prove any rational-isogeny theorem, any discriminant lower bound, or the final contradiction. It ensures that the representation fed into those arguments is genuinely a member of the same arithmetic family and retains exactly the local and global data they require.

If the compatible family is known only after restriction to a potential-modularity field, the final stage must either work over that field or invoke a valid descent mechanism. The prime switch does not improve the descent status.

### 18.3 Final perspective

Changing the prime is not an operation on matrix entries. It is a passage through algebraic arithmetic data. The original and new completions read the same Frobenius polynomials, determinant character, purity, polarization, and labelled weight record. Strong compatibility adds a common Weil--Deligne parameter at each fixed place away from the moving coefficient characteristic. Chebotarev identifies semisimple global realizations of one automorphic representation.

The power of the method comes from respecting what remains outside that common record. Lattices are choices. Residual extensions can change with those choices. Residual irreducibility and adequacy have exceptional primes and small-image branches. Integral monodromy can vanish even when rational monodromy has rank one. At the new coefficient prime, crystalline periods and finite-flat group schemes require their own comparison and integral theorems. Potential automorphy remains over its auxiliary field until descent is performed.

With those boundaries fixed, the passage to $3$ becomes exact. One chooses an actual place above $3$, records its residue field, constructs the corresponding member, checks its characteristic-$3$ image directly, and verifies finite flatness at every place above $3$, through a type-$(0,1)$ Fontaine--Laffaille lattice in the unramified odd range or through direct geometry over the actual local base. Away from $3$, integral certificates decide which ramification survives. The residual field cut out by the chosen lattice then has an explicit degree, upper-break record, conductor, and root-discriminant bound.

The enduring output is therefore not the slogan that the prime has changed. It is a certified companion: the same algebraic arithmetic family in a new topology, equipped with a fresh lattice, a freshly checked residual image, a separate coefficient-prime local model, an honest exceptional-set ledger, and numerical ramification bounds ready for classification. That is the form in which changing the prime can carry an argument without carrying an error with it.
