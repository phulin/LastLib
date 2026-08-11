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
12. [The chosen hardly-ramified family](#12-the-chosen-hardly-ramified-family)
    - [The distinguished lift](#121-the-distinguished-lift)
    - [The assembled family over the base field](#122-the-assembled-family-over-the-base-field)
    - [The exact prime-switching question](#123-the-exact-prime-switching-question)
13. [The rational three-adic companion](#13-the-rational-three-adic-companion)
    - [Choosing a coefficient place above three](#131-choosing-a-coefficient-place-above-three)
    - [Common Frobenius polynomials and determinant](#132-common-frobenius-polynomials-and-determinant)
    - [Automorphic identification and coefficient covariance](#133-automorphic-identification-and-coefficient-covariance)
    - [Crystallinity and Hodge type at three](#134-crystallinity-and-hodge-type-at-three)
14. [All-level finite-flatness at three](#14-all-level-finite-flatness-at-three)
    - [From a crystalline space to one good lattice](#141-from-a-crystalline-space-to-one-good-lattice)
    - [Strong divisibility in weights zero and one](#142-strong-divisibility-in-weights-zero-and-one)
    - [Every open coefficient ideal](#143-every-open-coefficient-ideal)
    - [Changing the lattice without losing finite flatness](#144-changing-the-lattice-without-losing-finite-flatness)
15. [The prime two: type, conductor, and the special line](#15-the-prime-two-type-conductor-and-the-special-line)
    - [The exact rational dyadic parameter](#151-the-exact-rational-dyadic-parameter)
    - [Why the conductor is two](#152-why-the-conductor-is-two)
    - [Integral degeneration in characteristic three](#153-integral-degeneration-in-characteristic-three)
    - [The decomposition-group-stable special line](#154-the-decomposition-group-stable-special-line)
    - [A simultaneous global lattice](#155-a-simultaneous-global-lattice)
16. [The full torsion tower](#16-the-full-torsion-tower)
    - [Ramification away from two and three](#161-ramification-away-from-two-and-three)
    - [Finite-flat objects over the punctured integer ring](#162-finite-flat-objects-over-the-punctured-integer-ring)
    - [Transition maps, determinant, and duality](#163-transition-maps-determinant-and-duality)
    - [What the tower remembers](#164-what-the-tower-remembers)
17. [The companion theorem and hostile audit](#17-the-companion-theorem-and-hostile-audit)
    - [The exact three-adic companion theorem](#171-the-exact-three-adic-companion-theorem)
    - [Proof ledger](#172-proof-ledger)
    - [Hostile mathematical audit](#173-hostile-mathematical-audit)
    - [Dependency-boundary audit](#174-dependency-boundary-audit)
18. [Conclusion](#18-conclusion)

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

In a CM system the large-image theorem is the wrong tool. The residual induction criterion will often give absolute irreducibility outside a finite set, while the projective image remains dihedral. Such a branch must be retained explicitly in the switching ledger; it cannot be merged into the non-CM large-image branch.

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

An arbitrary stable lattice in a rational representation is not automatically the Tate lattice of the geometric factor used to prove finite flatness. When the downstream argument needs an integral torsion tower, the actual model is part of the hypothesis.

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

## 12. The chosen hardly-ramified family

The general theory now meets the fixed arithmetic object for which this volume was designed. Up to this point the base field, the old coefficient prime, and the bad set have been allowed to vary. In the application they are no longer variables. Fixing them removes several generic exceptional-set questions and replaces them by exact local statements.

The adjective “hardly ramified” will be used only as a name for the chosen lift and its inherited local package. No discriminant estimate or classification is part of the present argument. What matters here is that the lift is ramified only where stated, that its dyadic type is known as a full Weil--Deligne representation, and that its coefficient-prime lattice has already been selected.

### 12.1 The distinguished lift

Let $\ell\ge 7$, let $L_0/\mathbf Q_\ell$ be finite, and let

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(L_0)
\tag{12.1}
$$

be the chosen balanced, minimally ramified lift. Its established properties are:

1. $\rho$ is continuous and absolutely irreducible;
2. $\det\rho=\chi_\ell$;
3. $\rho$ is unramified outside $\{2,\ell\}$;
4. at $2$, wild inertia is trivial, the monodromy operator is zero, and tame inertia has primitive order three;
5. a stable lattice at $\ell$ has already been chosen, together with its coefficient-linear finite-flat quotient system.

The dyadic assertion in item 4 means more than conductor exponent two. If $t_2$ is a tame generator acting through the order-three quotient, then

$$
t_2^2+t_2+1=0
\tag{12.2}
$$

on the two-dimensional space, and $t_2\ne1$. The two eigencharacters over a splitting field are inverse primitive cubic characters. Frobenius conjugates $t_2$ to $t_2^2$. These relations will determine both the rational conductor and the residual special line after the prime is changed.

The chosen lattice at $\ell$ is not carried across to characteristic three. It belongs to the old completion. Its role in the earlier construction was to retain the original integral deformation condition and to anchor the distinguished member. The three-adic member will require a new lattice.

### 12.2 The assembled family over the base field

The descent results of the preceding volumes provide a number field $E$, a place
$\lambda_0\mid\ell$, and an $E$-rational family

$$
\mathcal R=\{r_\lambda\}_{\lambda\in\operatorname{Pl}_f(E)}
\tag{12.3}
$$

of continuous, semisimple, absolutely irreducible rank-two representations of $G_{\mathbf Q}$.
After one common finite scalar extension,

$$
r_{\lambda_0}\simeq\rho.
\tag{12.4}
$$

For every rational prime $p\notin\{2,\ell\}$ there is a polynomial

$$
P_p(X)=X^2-a_pX+p\in E[X]
\tag{12.5}
$$

such that, whenever $p$ is different from the residue characteristic of $\lambda$,

$$
r_\lambda\text{ is unramified at }p,\qquad
\det(X-r_\lambda(\operatorname{Frob}_p))=P_p(X).
\tag{12.6}
$$

Every root of $P_p$ is a Weil number of weight one under every complex embedding. For every finite $p$ there is an algebraic Frobenius-semisimple Weil--Deligne pair $D_p$ over $E$ satisfying

$$
\operatorname{WD}_p(r_\lambda)^{\mathrm{F\text{-}ss}}
\simeq D_p\otimes_EE_\lambda
\tag{12.7}
$$

whenever the coefficient characteristic is not $p$. At $p=2$ the pair $D_2$ has exactly the type described by (12.2), trivial wild inertia, and $N_2=0$. At every $p\notin\{2,\ell\}$ it is unramified. At $p=\ell$, it is the common away-from-$\ell$ parameter; no identification with the period module of the distinguished $\ell$-adic member is being inserted.

For every coefficient place,

$$
\det r_\lambda=\chi_\lambda,\qquad
r_\lambda^\vee\simeq r_\lambda\otimes\chi_\lambda^{-1}.
\tag{12.8}
$$

The family is independent of the Brauer relation and of the auxiliary presentation used to construct it. This independence is rational. Each member has a stable lattice by compactness, but no integral Brauer cancellation and no common lattice over $\mathcal O_E$ has been proved.

### 12.3 The exact prime-switching question

Choose a place $\nu\mid3$ of $E$. The rational representation

$$
V=r_\nu:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(K),
\qquad K=E_\nu,
\tag{12.9}
$$

already exists. The problem is to endow it with the following exact package:

- the common good Frobenius polynomials and cyclotomic determinant;
- the same full dyadic rational type as $\rho$;
- crystallinity at $3$ with Hodge--Tate weights $\{0,1\}$;
- a globally stable lattice $T\subset V$ whose quotient by every open coefficient ideal is finite flat at $3$;
- compatible transition maps among all these quotient models;
- primitive tame order-three action at $2$ whose first residual reduction is a nontrivial unipotent block;
- the resulting decomposition-group-stable special line;
- unramifiedness outside $\{2,3\}$; and
- compatible determinant pairings and Cartier duality.

The prime $\ell$ deserves attention. It was a bad prime in the weak presentation of the family only because it was the coefficient prime of the distinguished lift. For $V$, whose coefficient prime is $3$, the place $\ell$ is away from coefficient characteristic. The strict parameter $D_\ell$ applies. The exact assembled family proves that $V$ is unramified there. Thus the three-adic companion is unramified outside $\{2,3\}$, not merely outside $\{2,3,\ell\}$.

No assertion about the residual image being adequate is needed for this construction. Absolute irreducibility of the rational member is already part of the assembled family; its reduction may be reducible. The later use of the torsion tower must therefore retain the actual finite-flat objects and their extension structure rather than presuppose an image theorem at the small prime.

## 13. The rational three-adic companion

### 13.1 Choosing a coefficient place above three

Factor

$$
3\mathcal O_E=\prod_{\nu\mid3}\nu^{e_\nu}.
\tag{13.1}
$$

A choice of $\nu$ determines

$$
K=E_\nu,\qquad
\mathcal O=\mathcal O_K,\qquad
\mathfrak m=(\varpi),\qquad
k=\mathcal O/\mathfrak m.
\tag{13.2}
$$

There can be several such choices. The corresponding representations need not be isomorphic over one local field, because the completions can differ. The correct common statement is that each reads the same algebraic record through its own embedding $E\hookrightarrow E_\nu$.

The residue field can be $\mathbf F_{3^f}$ with $f>1$. Nothing in the construction requires $f=1$. The lattice $T$ will be free of rank two over $\mathcal O$, and $T/\mathfrak mT$ will be two-dimensional over $k$. Viewed over $\mathbf F_3$ it has dimension $2f$. We never replace this statement by an unsupported two-dimensional $\mathbf F_3$ model.

A coefficient enlargement is harmless when every object, ideal, model, and transition map is extended together. It cannot lower the residue degree. The companion is therefore indexed by an actual place $\nu$, not by the rational prime $3$ alone.

### 13.2 Common Frobenius polynomials and determinant

For every $p\notin\{2,3,\ell\}$, equations (12.5)--(12.6) give

$$
\det(X-V(\operatorname{Frob}_p))
=X^2-\iota_\nu(a_p)X+p.
\tag{13.3}
$$

The strict local comparison at $\ell$ removes the apparent exceptional prime $\ell$: since $D_\ell$ is unramified for the effective complement, $V$ is unramified at $\ell$ as well. Hence (after defining the corresponding local polynomial from $D_\ell$) the three-adic member is unramified at every $p\ne2,3$.

The determinant identity is literal:

$$
\det V=\chi_3.
\tag{13.4}
$$

At arithmetic Frobenius this gives determinant $p$. It also gives the rational alternating isomorphism

$$
V\xrightarrow{\sim}V^\vee(1).
\tag{13.5}
$$

An integral perfect pairing does not yet follow. Once a lattice is chosen, the determinant isomorphism must be rescaled so that $\bigwedge^2T$ maps isomorphically, rather than merely with finite index, to $\mathcal O(1)$.

Purity transports through the algebraic roots of $P_p$. It is not inferred from the product of the roots. If $\alpha_p\beta_p=p$, the two absolute values could still be unequal; the established weight-one purity theorem is what gives

$$
|\sigma(\alpha_p)|=|\sigma(\beta_p)|=p^{1/2}
\tag{13.6}
$$

for every complex embedding $\sigma$.

### 13.3 Automorphic identification and coefficient covariance

The family arose from effective Brauer descent of weight-two automorphic packets. At every coefficient embedding the signed Brauer class was proved to be one actual irreducible rank-two representation, and multiplicity one descended it to the corresponding completion. Thus $V$ is not a virtual representation and not merely a collection of Frobenius traces.

If $\Pi$ denotes the automorphic packet used to display the family over an auxiliary elementary field, restriction of $V$ to that field has the same almost-everywhere Frobenius polynomials as the $\nu$-adic realization of $\Pi$. Chebotarev identifies their semisimplifications. Actual effectivity and absolute irreducibility identify the intended constituent. The descent theorem then assembles this constituent over $\mathbf Q$.

This order matters:

$$
\text{automorphic packets}
\longrightarrow
\text{effective constituent}
\longrightarrow
\text{coefficient descent}
\longrightarrow
V.
\tag{13.7}
$$

Chebotarev recognizes an existing representation; it does not create the constituent or descend its coefficient field. Nor does it choose a lattice. Coefficient conjugation sends $a_p$, $D_p$, and $\nu$ together. It does not compare matrices in unrelated completions entry by entry.

### 13.4 Crystallinity and Hodge type at three

Strict compatibility stops at the coefficient prime. Although $D_3$ is unramified when read by members of coefficient characteristic different from $3$, that statement does not prove that $V$ is crystalline. A separate coefficient-prime bridge is required.

The displaying weight-two packet factors at $3$ occur in degree-one good-reduction geometry. Their three-adic realizations are crystalline, and their Hodge filtrations have steps only in degrees $0$ and $1$. The effective cancellation is an actual characteristic-zero direct sum

$$
R_3^+\simeq V\oplus R_3^-.
\tag{13.8}
$$

Both displaying terms are crystalline. The crystalline category is closed under direct summands, so $V$ is crystalline. Applying the exact filtered period functor to (13.8) and subtracting the equal auxiliary contributions yields

$$
\dim_KD_{\mathrm{cris}}(V)=2,
\tag{13.9}
$$

$$
\dim\operatorname{gr}^0D_{\mathrm{cris}}(V)
=\dim\operatorname{gr}^1D_{\mathrm{cris}}(V)=1.
\tag{13.10}
$$

Consequently the Hodge--Tate multiset is $\{0,1\}$. The determinant is compatible with this calculation: its Hodge weight is $1$, the sum of the two weights.

The use of actual cancellation in (13.8) is rational. It is legitimate because crystalline representations form an exact subcategory and rational projectors define subobjects. The same projector need not preserve any integral packet lattice. That is why crystallinity is proved here while the finite-flat lattice is constructed separately in the next chapter.

## 14. All-level finite-flatness at three

The phrase “finite flat at three” is sometimes used for a residual representation alone. That is insufficient here. The desired object is a single lattice whose quotients at every coefficient level have finite-flat models, with maps compatible as the level changes. This stronger statement is what makes the infinite lattice recoverable from its torsion tower.

### 14.1 From a crystalline space to one good lattice

Put

$$
D=D_{\mathrm{cris}}(V).
\tag{14.1}
$$

It is a two-dimensional weakly admissible filtered Frobenius module with

$$
\operatorname{Fil}^0D=D,\qquad
\dim\operatorname{Fil}^1D=1,\qquad
\operatorname{Fil}^2D=0.
\tag{14.2}
$$

Rational admissibility alone does not name an integral lattice. We seek a coefficient-linear lattice $M\subset D$ such that

$$
F_M=M\cap\operatorname{Fil}^1D
\tag{14.3}
$$

is saturated of rank one and the ordinary and divided Frobenius images generate $M$.

Choose a basis $e_0,e_1$ with $F_M=\mathcal Re_1$, where $\mathcal R$ is the unramified base ring with the coefficient action. Strong divisibility asks that

$$
\varphi_0(e_0)=ae_0+ce_1,\qquad
\varphi_1(e_1)=be_0+de_1
\tag{14.4}
$$

have normal matrix

$$
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(\mathcal R).
\tag{14.5}
$$

The divided map on the weight-one line accounts for the factor of $3$. The invertibility of (14.5) is the integral condition hidden by the rational Hodge numbers.

### 14.2 Strong divisibility in weights zero and one

**Theorem 14.1 (strongly divisible lattice).** The module $D$ contains a coefficient-linear strongly divisible lattice of Hodge type $(0,1)$.

**Proof strategy.** Start with a lattice $M_0$ whose intersection with the Hodge line is saturated. Form the normal image

$$
\Phi(M_0,F_0)=\varphi(M_0)+3^{-1}\varphi(F_0),
\qquad F_0=M_0\cap\operatorname{Fil}^1D.
\tag{14.6}
$$

After a homothety this is another lattice. Repeat the operation and saturate the new Hodge intersection. The relative elementary divisors of two consecutive lattices can be normalized to $(0,d_i)$.

If the integers $d_i$ were unbounded, the long directions would converge in the projective line to a Frobenius-stable line $D'\subset D$. According to whether this direction repeatedly lies in the Hodge line or its complement, the iteration would force either

$$
t_N(D')<t_H(D')
\quad\text{or}\quad
t_N(D/D')<t_H(D/D').
\tag{14.7}
$$

Both inequalities contradict weak admissibility. Thus only finitely many normalized relative positions occur. A pair repeats; taking the finite sum around the resulting cycle and saturating the Hodge intersection gives a fixed pair satisfying

$$
M=\varphi(M)+3^{-1}\varphi(F_M).
\tag{14.8}
$$

This is strong divisibility. The coefficient action commutes with every operation, so it is retained. $\square$

The theorem produces one lattice, not a canonical one. Ordinary and nonordinary shapes are both possible. In an ordinary shape the normal matrix may be triangular modulo $\mathfrak m$; in a local--local shape its diagonal entries may vanish while the off-diagonal entries are units. Finite flatness does not imply a stable ordinary line.

The integral realization of $M$ gives a $G_{\mathbf Q_3}$-stable lattice $T_{\mathrm{ff}}\subset V$ whose torsion quotients lie in the weight interval $[0,1]$.

### 14.3 Every open coefficient ideal

Let $I\subset\mathcal O$ be a nonzero open ideal. Integral low-weight theory produces a finite-flat commutative group scheme

$$
\mathcal G_{I,3}/\mathbf Z_3
\tag{14.9}
$$

with $\mathcal O/I$-action and a marked identification

$$
\mathcal G_{I,3}(\overline{\mathbf Q}_3)
\simeq T_{\mathrm{ff}}/IT_{\mathrm{ff}}.
\tag{14.10}
$$

This is asserted for every open ideal, not merely $(3^n)$. If $\mathcal O/\mathbf Z_3$ is ramified and $3=u\varpi^e$, the quotients by $(3^n)$ omit many $\varpi$-power levels. An all-level theorem stated only for $3^n$ would therefore lose part of the coefficient filtration.

For nested ideals $J\subset I$, the generic quotient

$$
T_{\mathrm{ff}}/JT_{\mathrm{ff}}
\twoheadrightarrow
T_{\mathrm{ff}}/IT_{\mathrm{ff}}
\tag{14.11}
$$

extends to a faithfully flat morphism

$$
Q_{J,I}:\mathcal G_{J,3}\longrightarrow\mathcal G_{I,3}.
\tag{14.12}
$$

If $K\subset J\subset I$, then

$$
Q_{J,I}\circ Q_{K,J}=Q_{K,I}.
\tag{14.13}
$$

The direction is worth auditing: the realization from filtered objects is contravariant, so the surjection of Galois modules corresponds to an inclusion on the filtered side. Reversing that arrow gives the wrong kernel.

The models form one quotient system. Separately producing some model at each level would not imply (14.12)--(14.13).

### 14.4 Changing the lattice without losing finite flatness

The lattice that makes the dyadic type visible need not be $T_{\mathrm{ff}}$. We therefore need a transfer theorem.

**Proposition 14.2 (commensurability transfer).** Let $T$ and $T'$ be stable $\mathcal O$-lattices in the same local representation. If every open-ideal quotient of $T$ has a finite-flat model, then the same is true of $T'$.

**Proof.** Choose $c\ge0$ with

$$
\varpi^cT\subset T'\subset\varpi^{-c}T.
\tag{14.14}
$$

For $I=(\varpi^n)$, place $T'/\varpi^nT'$ inside a sufficiently deep quotient of $\varpi^{-c}T$. More precisely, let $A$ be the image of $T'$ and $B$ the image of $\varpi^nT'$ in

$$
\varpi^{-c}T/\varpi^{n+c}T.
\tag{14.15}
$$

Because $\varpi^{n+c}T\subset\varpi^nT'$, one has

$$
A/B\simeq T'/\varpi^nT'.
\tag{14.16}
$$

Take the schematic closure of $A$ in the available finite-flat ambient model and then the represented quotient by the closure of $B$. This gives the desired finite-flat model. The same argument applies to an arbitrary open ideal. $\square$

The proposition uses closure under stable subobjects and represented quotients, not a false assertion that finite flatness follows from rational crystallinity for every lattice. It is the hinge allowing integral Hodge theory at $3$ and integral type theory at $2$ to be satisfied by one global lattice.

## 15. The prime two: type, conductor, and the special line

### 15.1 The exact rational dyadic parameter

Since $2\ne3$, strict compatibility applies to $V|_{G_{\mathbf Q_2}}$. The common pair is

$$
D_2=(r_2,N_2),
\qquad
N_2=0,
\qquad
r_2(P_2)=1,
\tag{15.1}
$$

and a tame generator $t_2$ acts by an operator $A$ satisfying

$$
A^2+A+1=0,\qquad A\ne1.
\tag{15.2}
$$

Arithmetic Frobenius $\phi_2$ satisfies

$$
r_2(\phi_2)A r_2(\phi_2)^{-1}=A^2.
\tag{15.3}
$$

Over a field containing a primitive cube root $\zeta$, inertia has eigencharacters $\zeta$ and $\zeta^{-1}$, while Frobenius exchanges their lines. Thus the local Weil representation is not an arbitrary direct sum of two tame characters. The Frobenius interchange is part of the local type.

### 15.2 Why the conductor is two

Wild inertia is trivial, so the Swan conductor is zero. The primitive tame action has no invariant vector in characteristic zero:

$$
V^{I_2}=0.
\tag{15.4}
$$

Since $N_2=0$, the Artin conductor is

$$
a_2(V)=\operatorname{codim}V^{I_2}+\operatorname{Sw}_2(V)
=2+0=2.
\tag{15.5}
$$

This is conductor two at the prime two. It is not Steinberg. A Steinberg parameter has nonzero rank-one monodromy; here monodromy is zero and finite tame inertia moves both dimensions. The integer (15.5) is a consequence of the full pair (15.1)--(15.3), not a replacement for it.

### 15.3 Integral degeneration in characteristic three

Choose a vector $e$ such that $e,Ae$ span $V$. In the basis $(e,Ae)$, the tame operator is

$$
[A]=
\begin{pmatrix}
0&-1\\
1&-1
\end{pmatrix}.
\tag{15.6}
$$

This matrix preserves the lattice $\mathcal Oe+\mathcal OA e$. Modulo $\mathfrak m$,

$$
X^2+X+1=(X-1)^2.
\tag{15.7}
$$

The reduced matrix is not the identity, because

$$
A-1=
\begin{pmatrix}
-1&-1\\
1&-2
\end{pmatrix},
\qquad
\det(A-1)=3.
\tag{15.8}
$$

Therefore

$$
(\overline A-1)^2=0,\qquad
\overline A-1\ne0.
\tag{15.9}
$$

The residual tame action is one nontrivial unipotent Jordan block. Its semisimplification is trivial on inertia and hence forgets the dyadic ramification completely. This is the decisive example showing why residual semisimplification, though lattice independent, is not enough for the torsion argument.

### 15.4 The decomposition-group-stable special line

For a type-adapted lattice $T$, put $\overline T=T/\mathfrak mT$ and define

$$
\mathscr L_2
=\ker(\overline A-1)
=\operatorname{im}(\overline A-1).
\tag{15.10}
$$

The two spaces agree because $\overline A-1$ is a nonzero square-zero operator of rank one. Thus $\mathscr L_2$ is one-dimensional over $k$.

Replacing $t_2$ by its inverse does not change the line:

$$
\overline A^{-1}-1
=-\overline A^{-1}(\overline A-1).
\tag{15.11}
$$

Frobenius preserves it because Frobenius conjugates $\overline A$ to $\overline A^2$. Hence $\mathscr L_2$ is stable under the entire decomposition group $G_{\mathbf Q_2}$, not only inertia.

There is an exact residual sequence

$$
0\longrightarrow\mathscr L_2
\longrightarrow\overline T
\longrightarrow\overline T/\mathscr L_2
\longrightarrow0.
\tag{15.12}
$$

Both endpoints are trivial on tame inertia, but the sequence is nonsplit as an inertia module. It is this middle extension that cuts out the tame cubic action.

The line is a first-level object. At higher coefficient levels $\ker(A-1)$ need not be a free rank-one direct summand because $\det(A-1)=3$ up to a unit. What persists at every level is the action of the same cyclic order-three tame group and the filtration

$$
0\subset(A-1)T_I
\subset\ker(A-1\mid T_I)
\subset T_I.
\tag{15.13}
$$

We do not promote $\mathscr L_2$ to a fictitious free fixed line throughout the tower.

### 15.5 A simultaneous global lattice

**Proposition 15.1 (simultaneous lattice).** There is a globally $G_{\mathbf Q}$-stable lattice $T\subset V$ such that:

1. every $T/IT$ is finite flat at $3$ for every open $I\subset\mathcal O$;
2. its dyadic restriction is type adapted and reduces as the nontrivial block (15.9);
3. its first residual level contains the special line (15.10).

**Proof.** Begin with the cyclic dyadic lattice of (15.6). Saturate its orbit under the compact global image to obtain a global stable lattice without replacing the primitive $\mathcal O[A]$-structure by the nonsaturated scalar order. The resulting lattice is commensurable with $T_{\mathrm{ff}}$. Proposition 14.2 transfers all-level finite flatness at $3$ to it. Equations (15.7)--(15.10) give the dyadic conclusions. $\square$

The proposition is a simultaneous selection theorem, not a uniqueness theorem. Once $T$ is fixed, its special line is intrinsic. Another stable lattice could carry a different residual extension even though its residual semisimplification is the same.

## 16. The full torsion tower

### 16.1 Ramification away from two and three

For $p\ne2,3$, strict compatibility identifies the local parameter of $V$ with the common unramified $D_p$. This includes the old coefficient prime $\ell$. Hence inertia acts trivially on $V$, on $T$, and on every quotient

$$
T_I=T/IT.
\tag{16.1}
$$

Thus every $T_I$ is unramified outside $\{2,3\}$. At $2$, wild inertia is trivial and tame inertia factors through $C_3$. At $3$, the quotient has its finite-flat model.

The distinction between rational and modular conductors remains important. The rational conductor at $2$ is exactly two by (15.5). Modulo $\mathfrak m$, the tame action becomes unipotent, and semisimplification would have conductor zero. The safe datum at the torsion level is the actual $C_3$-action and its special line, not a conductor copied from characteristic zero.

### 16.2 Finite-flat objects over the punctured integer ring

At $3$, $T_I$ has the model $\mathcal G_{I,3}$ constructed above. At every $p\ne2,3$, its unramified generic fiber has a unique finite étale extension over $\mathbf Z_p$. These marked local models glue over the Dedekind base with $2$ removed.

**Theorem 16.1 (global finite-flat model).** For every open ideal $I\subset\mathcal O$, there is a finite-flat commutative group scheme

$$
\mathcal G_I/\mathbf Z[1/2]
\tag{16.2}
$$

with $\mathcal O/I$-action and generic geometric points $T_I$.

**Proof strategy.** Spread the generic finite étale Hopf algebra away from finitely many primes. At $3$ use the prescribed finite-flat Hopf order. At the remaining primes use the unique finite étale orders. Intersect these finitely many local Hopf orders inside the common generic Hopf algebra. Over a Dedekind domain the intersection is finite projective, and the Hopf operations preserve it because they preserve every localization. Its localizations recover the marked local models. $\square$

Removing $2$ is necessary. A finite-flat group scheme of $3$-power order over $\mathbf Z_2$ is finite étale, so its generic fiber would be unramified. Our generic fiber has nontrivial tame order-three inertia at $2$.

### 16.3 Transition maps, determinant, and duality

For $J\subset I$, the maps $Q_{J,I}$ at $3$ and the unique finite étale maps away from $3$ glue to faithfully flat morphisms

$$
Q_{J,I}:\mathcal G_J\longrightarrow\mathcal G_I.
\tag{16.3}
$$

They compose transitively. Thus $\{\mathcal G_I,Q_{J,I}\}$ is one all-level quotient system.

Rescale the rational determinant isomorphism so that

$$
\bigwedge_{\mathcal O}^2T\simeq\mathcal O(1).
\tag{16.4}
$$

Wedge product then gives a perfect alternating pairing

$$
T_I\times T_I\longrightarrow(\mathcal O/I)(1).
\tag{16.5}
$$

To compare coefficient-linear duality with Cartier duality over $\mathbf Z_3$, retain the coefficient dualizing module

$$
\mathcal O^\dagger
=\operatorname{Hom}_{\mathbf Z_3}(\mathcal O,\mathbf Z_3).
\tag{16.6}
$$

It is the inverse different as a fractional $\mathcal O$-ideal. The invariant duality statement is

$$
\mathcal G_I^D
\simeq
\mathcal G_I\otimes_{\mathcal O/I}(\mathcal O/I)^\dagger.
\tag{16.7}
$$

Choosing a generator of $\mathcal O^\dagger$ identifies the right side with $\mathcal G_I$, compatibly in $I$, but this identification is noncanonical up to a unit. Suppressing the inverse different when $K/\mathbf Q_3$ is ramified would turn a rationally perfect trace pairing into an integrally imperfect one.

### 16.4 What the tower remembers

The inverse limit of the generic points of $\mathcal G_{\mathfrak m^n}$ recovers $T$. The tower retains:

- the rank-two $\mathcal O$-module and its $G_{\mathbf Q}$-action;
- the cyclotomic determinant and alternating pairing;
- finite flatness at $3$ at every coefficient level;
- exact transition maps and successive kernels;
- unramifiedness outside $\{2,3\}$;
- the full tame $C_3$-action at $2$;
- the nonsplit residual orientation recorded by $\mathscr L_2$.

It does not classify the simple factors of the finite-flat objects, split the residual extension, or assert a free fixed line at every higher level. Those would be new theorems, not consequences of changing coefficient prime.

## 17. The companion theorem and hostile audit

### 17.1 The exact three-adic companion theorem

**Theorem 17.1 (three-adic companion of the chosen hardly-ramified lift).** Let $\rho$ be the chosen lift (12.1), and let $\mathcal R$ be the effective compatible family (12.3) containing it at $\lambda_0\mid\ell$. Fix any coefficient place $\nu\mid3$, put $K=E_\nu$, and let $V=r_\nu$.

Then:

1. $V$ is continuous and absolutely irreducible, with $\det V=\chi_3$.
2. For every $p\ne2,3$, $V$ is unramified and has the polynomial obtained from the common algebraic $P_p$ through $E\hookrightarrow K$.
3. At every fixed prime away from coefficient characteristic, its Frobenius-semisimple Weil--Deligne pair is the scalar extension of the common $D_p$. In particular, at $2$ it has trivial wild inertia, $N=0$, primitive tame order-three type, and Artin conductor two.
4. At $3$, $V$ is crystalline with Hodge--Tate weights $\{0,1\}$.
5. There is a globally stable rank-two $\mathcal O$-lattice $T\subset V$ such that every $T/IT$ has a compatible coefficient-linear finite-flat model over $\mathbf Z_3$ for every open ideal $I\subset\mathcal O$.
6. The lattice can be chosen so that modulo $\mathfrak m$ the dyadic tame generator acts as a nontrivial unipotent block with the decomposition-group-stable special line
   $$
   \mathscr L_2=\ker(t_2-1)=\operatorname{im}(t_2-1).
   $$
7. The quotients $T/IT$ are unramified outside $\{2,3\}$ and glue to a compatible finite-flat system over $\mathbf Z[1/2]$.
8. The system has cyclotomic determinant and the compatible Cartier duality (16.7).

This $V$ is the three-adic companion of $\rho$: it is not obtained by extending scalars from $L_0$ to $K$, but by reading one algebraic compatible family at the place $\nu$.

**Proof.** The effective base-field family gives clauses 1--3 and removes the old auxiliary prime $\ell$ from the ramification set. Actual weight-two cancellation in the crystalline category gives clause 4. The strongly divisible lattice and arbitrary-open-ideal construction give clause 5. Commensurability transfer permits the simultaneous type-adapted global lattice, giving clause 6. Strict compatibility away from $3$ and gluing of marked local models give clause 7. The rescaled determinant lattice and inverse-different normalization give clause 8. $\square$

### 17.2 Proof ledger

Each conclusion has one precise source.

| conclusion | mechanism | forbidden shortcut |
|---|---|---|
| new rational member | effective compatible family | tensoring two unrelated completions |
| common good polynomials | algebraic $P_p\in E[X]$ | comparing local matrices |
| determinant | actual Brauer determinant transfer | normalizing by a late twist |
| dyadic rational type | strict local compatibility | reconstructing type from conductor |
| crystallinity at $3$ | good weight-two coefficient-prime comparison | using the away-from-$3$ pair $D_3$ |
| one good integral lattice | strong divisibility in weights $0,1$ | claiming rational crystallinity chooses a lattice |
| every quotient level | arbitrary-open-ideal integral theory | checking only $3^n$ |
| type-adapted lattice | cyclic lattice and saturation | averaging by an order divisible by $3$ |
| finite flatness after replacement | schematic subquotient transfer | assuming it for every crystalline lattice |
| special line | nontrivial unipotent reduction | residual semisimplification |
| global models | gluing marked Hopf orders | potential descent from an unspecified field |
| Cartier duality | determinant lattice plus inverse different | raw trace self-duality |

The ledger also shows why the four prerequisites are complementary. The general compatible-system theory supplies the language and prime-switching boundary. Brauer descent supplies an actual effective constituent. The base-field assembly supplies one coherent family with exact local pairs. The fixed-three integral theory supplies precisely the lattice, finite-flat tower, and special line absent from rational compatibility.

### 17.3 Hostile mathematical audit

**Prime versus place.** The companion is $r_\nu$ for a named $\nu\mid3$. No uniqueness among all places above $3$ is claimed, and the residue field $k$ is retained.

**No cross-completion tensor product.** There is no expression
$\rho\otimes_{L_0}K$. The common objects are $P_p$, $D_p$, and the determinant character over the algebraic coefficient field.

**Semisimplification boundary.** The rational family is semisimple and absolutely irreducible. Reduction of a stable lattice has a lattice-independent semisimplification, but the dyadic line belongs to the selected lattice. The theorem never attributes that line to $\overline V^{\mathrm{ss}}$.

**Coefficient-prime boundary.** Strict compatibility at $3$ for other members does not prove crystallinity of $V$. The weight-two geometric comparison and actual crystalline cancellation do.

**Integral projector boundary.** The rational projector defining $V$ inside $R_3^+$ is used only in characteristic zero. The finite-flat lattice is constructed inside $D_{\mathrm{cris}}(V)$; it is not cut out by an allegedly integral Brauer projector.

**All-level meaning.** Every nonzero open ideal of $\mathcal O$ is included. Transition maps are part of the assertion. A ramified coefficient ring therefore loses no intermediate $\varpi$-level.

**Commensurability argument.** The transfer of finite flatness uses a finite-flat ambient object and schematic subquotients. It does not rest on extension closure without a supplied middle object.

**Conductor at two.** The equality $a_2(V)=2$ comes from zero invariants and zero Swan conductor. Monodromy remains zero. The word “special” in “special line” refers to the residual unipotent line, not a Steinberg parameter.

**Nonbanal reduction.** Since the tame order is three and the coefficient characteristic is three, semisimplicity fails. The companion matrix proves that the reduction is nontrivial, so it is not silently replaced by the identity.

**Higher-level line.** Only the bottom special line is free of rank one. At higher levels the full $C_3$-action and filtration (15.13) are retained.

**Old coefficient prime.** The three-adic member is unramified at $\ell$ by the exact local complement in the assembled family. This is not inferred from the old $\ell$-adic period module.

**Pairing.** The exterior pairing is made integral by rescaling, and Cartier duality retains the coefficient dualizing module. Ramification of $K/\mathbf Q_3$ is not ignored.

**No later conclusions.** No discriminant bound, torsion-field classification, extension-group calculation, or final reducibility statement has been used or asserted.

Every central implication in Theorem 17.1 survives these tests.

### 17.4 Dependency-boundary audit

The imported results are exactly the following.

From the compatible-system theory we use common Frobenius polynomials, strong local pairs away from coefficient characteristic, determinant transport, stable-lattice existence, lattice independence of residual semisimplification, and the warning that none of these provides new coefficient-prime integral data.

From effective Brauer descent we use the actual rank-two constituent at every coefficient embedding, determinant and local Mackey compatibility, and identification of the distinguished constituent. We do not turn its rational cancellation into integral cancellation.

From the base-field assembly we use one number field $E$, actual absolutely irreducible members $r_\lambda$, the polynomials $P_p$, the pairs $D_p$, exact dyadic type, purity, cyclotomic determinant, removal of auxiliary ramification, coefficient covariance, and retention of the original member. We respect its explicit statement that it supplies no new finite-flat lattice at $3$.

From the fixed-three integral theory we use the coefficient-prime crystalline bridge, the strongly divisible lattice, arbitrary-open-ideal finite-flat models, commensurability transfer, the type-adapted global lattice, the dyadic companion calculation, the special line, gluing over $\mathbf Z[1/2]$, transition maps, determinant pairings, and inverse-different Cartier duality.

No conclusion is strengthened at an import boundary:

- “stable lattice exists” is not read as “canonical lattice exists”;
- “residual semisimplification is independent” is not read as “residual extension is independent”;
- “strict compatibility” is not extended to equal coefficient and residue characteristic;
- “crystalline of weights $\{0,1\}$” is not read as “every lattice is finite flat”;
- “conductor two” is not read as “the full dyadic type is determined”;
- “finite flat at each level” is used together with, not in place of, compatible transition maps.

This closes the dependency audit without drawing on any later volume.

## 18. Conclusion

Changing coefficient prime is a reconstruction from common algebraic data, not a scalar extension between local fields. The distinguished $\ell$-adic lift and its three-adic companion live in different completions. They belong together because their good Frobenius polynomials, determinant, purity, and away-from-coefficient local parameters are realizations of the same algebraic ledger.

For the chosen hardly-ramified lift, the rational passage is exact. The effective Brauer construction produces an actual member at every coefficient place; coefficient descent places those members over completions of one number field; the base-field assembly identifies the original lift and retains the primitive dyadic type. Choosing $\nu\mid3$ therefore produces a genuine two-dimensional three-adic representation, unramified outside $\{2,3\}$, with cyclotomic determinant and the same conductor-two tame type at $2$.

The integral passage requires new work. Good weight-two comparison proves crystallinity with weights $\{0,1\}$ at the coefficient prime. Strong divisibility produces one lattice, and the arbitrary-open-ideal theory produces compatible finite-flat models at every coefficient level. Commensurability then allows the lattice to be replaced by one adapted to dyadic inertia without losing finite flatness.

At $2$, the primitive cubic characters merge modulo $3$. On the selected lattice they do not become trivial: they form one nontrivial unipotent Jordan block. Its common kernel and image is the decomposition-group-stable special line. This line is invisible in residual semisimplification and cannot be reconstructed from the conductor integer. It is precisely why the lattice and its nonsplit residual extension must travel with the companion.

The final object is the certified tower

$$
\boxed{
V=r_\nu,\quad
T\subset V,\quad
\{\mathcal G_I/\mathbf Z[1/2]\}_I,\quad
\det T=\mathcal O(1),\quad
\mathscr L_2=\ker(t_2-1)=\operatorname{im}(t_2-1).
}
\tag{18.1}
$$

Every arrow is now accounted for: algebraic compatibility changes the coefficient prime; coefficient-prime comparison proves crystallinity; integral low-weight theory builds the torsion models; saturation preserves the dyadic type; and gluing assembles the global finite-flat tower. No arithmetic information requested in the passage from the chosen lift to its three-adic companion is lost at a completion, semisimplification, lattice, or local-theory boundary.
