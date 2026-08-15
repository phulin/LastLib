# Mazur–Raynaud Admissible Group Schemes

## Contents

1. [The integral problem behind Eisenstein torsion](#1-the-integral-problem-behind-eisenstein-torsion)
   - [Two primes and three fibers](#11-two-primes-and-three-fibers)
   - [Why generic representations are insufficient](#12-why-generic-representations-are-insufficient)
   - [The Eisenstein atoms](#13-the-eisenstein-atoms)
   - [Conventions and scope](#14-conventions-and-scope)
2. [The exact category over the punctured arithmetic line](#2-the-exact-category-over-the-punctured-arithmetic-line)
   - [Finite flat objects over $S$](#21-finite-flat-objects-over-s)
   - [Admissible exact sequences](#22-admissible-exact-sequences)
   - [Schematic closure and saturation](#23-schematic-closure-and-saturation)
   - [Closure of a generic flag](#24-closure-of-a-generic-flag)
   - [Base change and localization](#25-base-change-and-localization)
3. [Constant and multiplicative constituents](#3-constant-and-multiplicative-constituents)
   - [The two atomic groups](#31-the-two-atomic-groups)
   - [Cartier duality and characters](#32-cartier-duality-and-characters)
   - [Constant type and multiplicative type](#33-constant-type-and-multiplicative-type)
   - [What constituent does and does not mean](#34-what-constituent-does-and-does-not-mean)
4. [The local structure at the Eisenstein prime](#4-the-local-structure-at-the-eisenstein-prime)
   - [Connected–étale structure over $\mathbf Z_\ell$](#41-connectedétale-structure-over-mathbf-z_ell)
   - [The maximal multiplicative subgroup](#42-the-maximal-multiplicative-subgroup)
   - [Order-$\ell$ rigidity for odd $\ell$](#43-order-ell-rigidity-for-odd-ell)
   - [Local devissage from integral atoms](#44-local-devissage-from-integral-atoms)
   - [The dyadic failure of character separation](#45-the-dyadic-failure-of-character-separation)
5. [The admissible category](#5-the-admissible-category)
   - [Filtration definition](#51-filtration-definition)
   - [Independence of a chosen filtration](#52-independence-of-a-chosen-filtration)
   - [Subobjects, quotients, and extensions](#53-subobjects-quotients-and-extensions)
   - [Primary decomposition and coefficient actions](#54-primary-decomposition-and-coefficient-actions)
   - [Separated admissible objects](#55-separated-admissible-objects)
6. [Yoneda extensions and torsor fibers](#6-yoneda-extensions-and-torsor-fibers)
   - [Extensions in an exact category](#61-extensions-in-an-exact-category)
   - [The fiber above one](#62-the-fiber-above-one)
   - [A low-degree extension sequence](#63-a-low-degree-extension-sequence)
   - [Baer sum and pull–push operations](#64-baer-sum-and-pullpush-operations)
7. [The flat Kummer calculation](#7-the-flat-kummer-calculation)
   - [$S$-units and the Picard group](#71-s-units-and-the-picard-group)
   - [Odd Eisenstein primes](#72-odd-eisenstein-primes)
   - [Explicit root torsors](#73-explicit-root-torsors)
   - [Localization of the Kummer class](#74-localization-of-the-kummer-class)
   - [The two-primary calculation](#75-the-two-primary-calculation)
8. [Extensions of a constant atom by a multiplicative atom](#8-extensions-of-a-constant-atom-by-a-multiplicative-atom)
   - [Classification for odd $\ell$](#81-classification-for-odd-ell)
   - [The carry parameter](#82-the-carry-parameter)
   - [Splitness and restriction](#83-splitness-and-restriction)
   - [Duality of extension classes](#84-duality-of-extension-classes)
   - [What this calculation does not classify](#85-what-this-calculation-does-not-classify)
9. [Devissage with exact hypotheses](#9-devissage-with-exact-hypotheses)
   - [Length and multiplicities](#91-length-and-multiplicities)
   - [Induction through an admissible flag](#92-induction-through-an-admissible-flag)
   - [The separated filtration theorem](#93-the-separated-filtration-theorem)
   - [Homomorphisms detected on constituents](#94-homomorphisms-detected-on-constituents)
   - [Annihilation and rank bounds](#95-annihilation-and-rank-bounds)
10. [Cartier duality, pairings, and self-dual objects](#10-cartier-duality-pairings-and-self-dual-objects)
    - [Dual admissibility](#101-dual-admissibility)
    - [Annihilator filtrations](#102-annihilator-filtrations)
    - [Perfect pairings](#103-perfect-pairings)
    - [A height-two self-dual pattern](#104-a-height-two-self-dual-pattern)
11. [Schematic closure in arithmetic torsion](#11-schematic-closure-in-arithmetic-torsion)
    - [The fixed ambient model principle](#111-the-fixed-ambient-model-principle)
    - [Closing an Eisenstein line](#112-closing-an-eisenstein-line)
    - [Quotients and flat images](#113-quotients-and-flat-images)
    - [Intersections of constant and multiplicative lines](#114-intersections-of-constant-and-multiplicative-lines)
12. [The prime-level Eisenstein application](#12-the-prime-level-eisenstein-application)
    - [Cuspidal and Shimura input](#121-cuspidal-and-shimura-input)
    - [Localization at an Eisenstein prime](#122-localization-at-an-eisenstein-prime)
    - [The admissibility criterion for a selected quotient](#123-the-admissibility-criterion-for-a-selected-quotient)
    - [The control theorem](#124-the-control-theorem)
    - [What passes to completed Hecke pieces](#125-what-passes-to-completed-hecke-pieces)
13. [Exceptional primes and boundary cases](#13-exceptional-primes-and-boundary-cases)
    - [The level prime cannot be an Eisenstein prime](#131-the-level-prime-cannot-be-an-eisenstein-prime)
    - [Levels with trivial Eisenstein index](#132-levels-with-trivial-eisenstein-index)
    - [The prime three](#133-the-prime-three)
    - [The full two-primary boundary](#134-the-full-two-primary-boundary)
    - [A failure ledger](#135-a-failure-ledger)
14. [The admissible-group-scheme package](#14-the-admissible-group-scheme-package)
    - [Main theorem](#141-main-theorem)
    - [Dependency closure](#142-dependency-closure)
    - [Exact scope boundaries](#143-exact-scope-boundaries)
    - [Conclusion](#144-conclusion)

## 1. The integral problem behind Eisenstein torsion

### 1.1 Two primes and three fibers

Prime-level Eisenstein arguments involve two primes with quite different jobs. The **level prime** $N$ is removed from the base because the modular Jacobian has bad reduction there. An **Eisenstein prime** $\ell$ divides the relevant Eisenstein index and is therefore the residue characteristic at which a finite group scheme may cease to be étale. Confusing these two primes obscures the entire argument.

Throughout the book, unless a statement says otherwise,

$$
N\text{ is prime},\qquad
S=\operatorname{Spec}\mathbf Z[1/N],\qquad
n_N=\operatorname{num}\left(\frac{N-1}{12}\right)
=\frac{N-1}{\gcd(N-1,12)},
$$

and $\ell$ is a prime divisor of $n_N$. In particular $\ell\ne N$. We write

$$
\Gamma=\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q),
\qquad
\overline\chi_\ell:\Gamma\longrightarrow\mathbf F_\ell^\times
$$

for the mod-$\ell$ cyclotomic character.

A finite flat group over $S$ has three faces. Its generic fiber is a finite étale group over $\mathbf Q$, hence a finite Galois module. Its fiber at a prime $r\ne N$ is a finite group scheme over $\mathbf F_r$. Between them lies an integral Hopf algebra, which remembers how generic points collide. At $r\ne\ell$ an $\ell$-primary group is automatically étale. At $r=\ell$ it may have connected multiplicative or local-local structure. There is no fiber at $N$ in $S$; ramification there is permitted and carries the level information.

This geometry is exactly suited to the Eisenstein pair of characters

$$
1,\qquad \overline\chi_\ell.
\tag{1.1}
$$

The constant group $\underline{\mathbf Z/\ell\mathbf Z}$ realizes the first, while $\mu_\ell$ realizes the second. Their extensions record the integral ambiguity that remains after the two diagonal characters have been identified.

### 1.2 Why generic representations are insufficient

Over $\mathbf Q$ both $\underline{\mathbf Z/\ell\mathbf Z}$ and $\mu_\ell$ are étale. Their geometric points are the one-dimensional modules $\mathbf F_\ell$ and $\mathbf F_\ell(1)$. For odd $\ell$ these modules are distinguished by inertia at $\ell$. Yet even then a reducible two-dimensional representation with these constituents contains extension data not visible in its semisimplification.

At $\ell=2$ the problem is sharper:

$$
\mathbf F_2^\times=\{1\},\qquad \overline\chi_2=1.
$$

Thus the generic fibers of $\underline{\mathbf Z/2\mathbf Z}$ and $\mu_2$ are isomorphic, although their special fibers over $\mathbf F_2$ are respectively étale and connected. A generic line does not say which integral endpoint it closes to. The ambient finite-flat group and schematic closure must make that choice.

Nor is every kernel or image of a morphism between finite-flat groups flat. The correct setting is therefore not an abelian category. One works with faithfully flat short exact sequences, finite-flat closed subgroups, represented quotients, and saturated schematic closures. Every devissage in this book is built from those operations.

### 1.3 The Eisenstein atoms

The constant and multiplicative atoms are Cartier dual:

$$
\left(\underline{\mathbf Z/\ell\mathbf Z}\right)^D\simeq\mu_\ell,
\qquad
\mu_\ell^D\simeq\underline{\mathbf Z/\ell\mathbf Z}.
\tag{1.2}
$$

The reason these particular groups occur is arithmetic, not merely categorical. Book 133 constructs on the generic fiber of $J_0(N)$ a constant cuspidal subgroup

$$
C_{N,\mathbf Q}\simeq\underline{\mathbf Z/n_N\mathbf Z}_{\mathbf Q}
$$

and a diagonalizable Shimura subgroup

$$
\Sigma_{N,\mathbf Q}\simeq\mu_{n_N,\mathbf Q}
$$

noncanonically, both annihilated by the prime-level Eisenstein ideal. Passing to an $\ell$-primary layer produces the two atoms in (1.2), possibly repeated through higher powers.

The present task is to develop the exact category in which those layers can be propagated through subgroups, quotients, duals, and extensions. The object ultimately used in Eisenstein descent is selected by additional Hecke and Jacobian geometry. We build the group-scheme theorem that such an object must satisfy once its generic constituents and its finite-flat ambient model have been verified.

### 1.4 Conventions and scope

All group schemes are commutative. “Finite flat” means finite locally free. Exactness of group schemes means exactness as fppf sheaves, with the first map a finite-flat closed immersion and the second a faithfully flat represented quotient. The order $|G|$ is the locally constant rank of $\mathcal O_G$; over the connected scheme $S$ it is an integer.

We use **constant** for an actual constant group scheme, **finite étale** for the wider class corresponding to possibly nontrivial unramified monodromy over the base, and **constant type** for an object admitting a filtration by constant order-$\ell$ factors. Likewise, **multiplicative type** has its usual intrinsic meaning: after a faithfully flat base change the group is diagonalizable. A filtration by copies of $\mu_\ell$ is a more restrictive assertion and will be stated explicitly.

No claim is made here that every finite-flat $\ell$-group over $S$ is admissible, that every extension between the two atoms is classified by one Kummer group, or that every admissible object has a canonical global product decomposition. Each of those statements is false without further hypotheses. The distinction between a filtration and a splitting will be maintained throughout.

## 2. The exact category over the punctured arithmetic line

### 2.1 Finite flat objects over $S$

Let $\mathcal F_\ell(S)$ be the category of finite flat commutative $S$-groups of $\ell$-power order. We do not require an object to be killed by $\ell$. Thus $\underline{\mathbf Z/\ell^2\mathbf Z}$ belongs to the category and is an extension of two groups killed by $\ell$, but it is not itself killed by $\ell$.

The generic-fiber functor

$$
G\longmapsto G_{\mathbf Q}(\overline{\mathbf Q})
\tag{2.1}
$$

is faithful: two maps out of a flat finite scheme that agree on the dense generic fiber agree everywhere. It is neither generally full nor essentially injective. Fullness can fail because a generic map need not preserve the chosen Hopf lattices. Essential injectivity already fails for the two order-two endpoints over $\mathbf Z_2$.

It is useful to see the lattice issue algebraically. A finite-flat affine group is represented by a finite projective Hopf algebra $B$. Its generic fiber remembers $B\otimes\mathbf Q$, but an integral model remembers the particular Hopf lattice $B$ inside that rational algebra. A generic homomorphism is a Hopf-algebra map after tensoring with $\mathbf Q$. It extends precisely when it carries the target lattice into the source lattice. A denominator in that map can disappear generically and reappear as a vertical kernel after reduction.

This description also explains faithfulness. If two integral Hopf-algebra maps agree after tensoring with $\mathbf Q$, their difference has image killed by a nonzero integer. The target coordinate algebra is torsion-free, so the difference is zero. Existence is difficult; uniqueness is automatic.

For every $r\ne N,\ell$, the order of $G$ is invertible over $\mathbf Z_r$, so $G_{\mathbf Z_r}$ is finite étale. All nonétale structure is concentrated at $\ell$. This observation is elementary but crucial: a global finite-flat assertion can be checked by combining étale extension away from $\ell$ with genuine integral structure over $\mathbf Z_\ell$.

### 2.2 Admissible exact sequences

A sequence

$$
0\longrightarrow G'\longrightarrow G\longrightarrow G''\longrightarrow0
\tag{2.2}
$$

in $\mathcal F_\ell(S)$ is **admissibly exact** if $G'\to G$ is a finite-flat closed subgroup, $G\to G''$ is faithfully flat, and $G''$ represents the quotient fppf sheaf. Then $G\to G''$ is a $G'$-torsor and

$$
|G|=|G'|\,|G''|.
\tag{2.3}
$$

The rank identity follows after an fppf cover trivializing the torsor, where $G$ becomes $G'\times G''$ as a scheme over the quotient. It is not a count of geometric points; in characteristic $\ell$, $\mu_\ell$ has only one geometric point.

Admissible sequences are stable under base change. Pulling back an admissible quotient remains a torsor. Pushing out an admissible subgroup along a homomorphism also exists in the finite-flat category. These two operations underlie restriction of extensions, Baer addition, and every induction below.

Arbitrary scheme-theoretic kernels are excluded. A morphism may be generically an isomorphism while having a nonflat special-fiber kernel. Whenever we use a kernel, image, or quotient, its flatness will either follow from an admitted exact sequence or from schematic closure in a fixed ambient object.

### 2.3 Schematic closure and saturation

Let $A$ be a Dedekind domain with fraction field $K$, let $G=\operatorname{Spec}B$ be finite flat over $A$, and let $H_K\subset G_K$ be a closed subgroup with Hopf ideal $I_K\subset B_K$. Define

$$
I=B\cap I_K\subset B_K,
\qquad
H=\operatorname{Spec}(B/I).
\tag{2.4}
$$

The contraction $I$ is saturated: if $0\ne a\in A$ and $ab\in I$, then $b\in I$. Hence $B/I$ is finite torsion-free over $A$, and therefore finite projective because $A$ is Dedekind. Contraction respects the coproduct, counit, and antipode, so $I$ is a Hopf ideal.

**Theorem 2.1 (finite-flat closure).** Let $A$ be Dedekind and $G/A$ finite flat. Every closed generic subgroup $H_K\subset G_K$ has a unique finite-flat closed subgroup $H\subset G$ with generic fiber $H_K$. It is given by (2.4). Formation of $H$ commutes with localization and with flat extensions of Dedekind domains for which the generic open remains dense.

**Proof.** The preceding saturation argument proves finite flatness and Hopf stability. If $H'$ were another finite-flat closed subgroup with the same generic fiber, its coordinate quotient would be torsion-free, so its defining Hopf ideal would be saturated and recovered by contraction from $I_K$. Thus $H'=H$. Localization commutes with contraction. Under a flat extension, the saturated exact sequence

$$
0\to I\to B\to B/I\to0
$$

remains exact with torsion-free quotient; both the base-changed closure and the newly computed closure have the same generic fiber, so uniqueness identifies them. $\square$

Uniqueness is relative to the chosen $G$. It does not say that an abstract generic group has a unique finite-flat model.

### 2.4 Closure of a generic flag

Suppose $V=G_{\mathbf Q}(\overline{\mathbf Q})$ has a $\Gamma$-stable flag

$$
0=V_0\subset V_1\subset\cdots\subset V_m=V.
\tag{2.5}
$$

Each $V_i$ determines a generic subgroup of $G_{\mathbf Q}$. Let $G_i$ be its closure in $G$. Inclusions among the $V_i$ give inclusions among the $G_i$, and represented successive quotients yield

$$
0=G_0\subset G_1\subset\cdots\subset G_m=G.
\tag{2.6}
$$

**Proposition 2.2 (integral flag).** The filtration (2.6) is the unique filtration inside $G$ with generic flag (2.5). Every $G_i$ and every $G_i/G_{i-1}$ is finite flat, and

$$
|G_i/G_{i-1}|=|V_i/V_{i-1}|.
$$

It commutes with localization and flat base change as in Theorem 2.1.

**Proof.** The closure theorem gives the subgroups and their uniqueness. The quotient of a finite-flat group by a finite-flat closed subgroup is represented and finite flat. Generic base change identifies it with the expected quotient, so its rank is the generic dimension as a finite scheme. Compatibility follows term by term. $\square$

This proposition is the main bridge from a reducible generic representation to an integral devissage. It requires a stable flag over $\mathbf Q$, not merely a flag after extending scalars, and it requires a pre-existing finite-flat middle model.

### 2.5 Base change and localization

Write $S_r=\operatorname{Spec}\mathbf Z_r$ for $r\ne N$. Localization sends (2.2) to an admissible exact sequence over $S_r$. Conversely, a generic subgroup extends over all of $S$ by Theorem 2.1; no separate gluing choice is made at each prime.

Completion at $r$ is faithfully flat. Equality of two finite-flat subgroups can therefore be checked after completion. Properties such as finite étaleness, multiplicative type, and faithful flatness descend under this base change. Connectedness of the special fiber is read over $\mathbf F_r$ and is unaffected by completion.

Removing $N$ matters. A group finite flat over $S$ can have a generic Galois module ramified at $N$. There is no integral fiber there to constrain it. Consequently “finite flat over $S$” is not synonymous with “unramified everywhere,” and a finite étale group over $S$ need not be constant.

## 3. Constant and multiplicative constituents

### 3.1 The two atomic groups

For a finite abelian group $A$, the constant group $\underline A_S$ is the disjoint union of copies of $S$ indexed by $A$. It is finite étale. For a finite abelian group $M$, the diagonalizable group $D(M)$ represents

$$
T\longmapsto\operatorname{Hom}(M,\Gamma(T,\mathcal O_T^\times)).
$$

In particular

$$
D(\mathbf Z/\ell\mathbf Z)=\mu_\ell.
$$

The special fibers at $\ell$ exhibit the contrast:

$$
\underline{\mathbf Z/\ell\mathbf Z}_{\mathbf F_\ell}
\text{ is étale},
\qquad
(\mu_\ell)_{\mathbf F_\ell}
=\operatorname{Spec}\mathbf F_\ell[t]/((t-1)^\ell)
\text{ is connected}.
\tag{3.1}
$$

Over $\mathbf Q$, geometric points give $\mathbf F_\ell$ with characters $1$ and $\overline\chi_\ell$. The integral distinction in (3.1) survives even when the two characters coincide at $\ell=2$.

### 3.2 Cartier duality and characters

Cartier duality is an exact contravariant anti-equivalence on finite-flat commutative groups. It exchanges constant and diagonalizable groups and reverses every admissible sequence. On generic Galois modules,

$$
G^D(\overline{\mathbf Q})
\simeq\operatorname{Hom}\bigl(G(\overline{\mathbf Q}),\overline{\mathbf Q}^{\times}\bigr),
\tag{3.2}
$$

so for an $\ell$-torsion module $V$ the dual is $V^\vee(1)$. Thus a character $\psi$ is sent to $\overline\chi_\ell\psi^{-1}$, which exchanges the two characters in (1.1).

If $H\subset G$ is finite flat, its annihilator

$$
H^\perp=\ker(G^D\to H^D)
$$

is finite flat and fits into

$$
0\to H^\perp\to G^D\to H^D\to0.
\tag{3.3}
$$

When $H$ is a schematic closure, $H^\perp$ is the closure of the generic annihilator. Both groups have the same generic fiber, and closure uniqueness supplies the equality.

### 3.3 Constant type and multiplicative type

An object $C\in\mathcal F_\ell(S)$ is of **constant $\ell$-type** if it has an admissible filtration whose factors are $\underline{\mathbf Z/\ell\mathbf Z}$. It need not be an actual constant group. For example, a nontrivial finite étale extension of one constant atom by another can carry unipotent monodromy around the removed prime $N$.

An object $M$ is of **split multiplicative $\ell$-type** if it has an admissible filtration whose factors are $\mu_\ell$. Such an object is of multiplicative type, but the adjective “split” records that its character groups have constant composition factors. Cartier duality gives an anti-equivalence

$$
\{\text{constant $\ell$-type objects}\}^{\mathrm{op}}
\longleftrightarrow
\{\text{split multiplicative $\ell$-type objects}\}.
\tag{3.4}
$$

If the object is killed by $\ell$ and has rank $\ell^a$, its generic semisimplification is respectively $1^{\oplus a}$ or $\overline\chi_\ell^{\oplus a}$. The converse from semisimplification alone is false: generic extension data may carry ramification at $N$, and integral models at $2$ may differ.

### 3.4 What constituent does and does not mean

A **constituent** is a factor in an admissible finite filtration. It is not automatically a subgroup. In an extension

$$
0\to A\to E\to B\to0,
$$

$A$ is a subgroup and $B$ a quotient, but a different composition series can place isomorphic factors in another order only when a new subgroup has actually been constructed. Reordering symbols in a list is not an exact-category argument.

Likewise, “constant constituent” does not mean that all its geometric points are rational inside the middle object. It says that the corresponding subquotient is the constant group scheme. “Multiplicative constituent” does not mean a collection of visible roots of unity on the special fiber; $\mu_\ell$ has only the identity geometric point there.

The safe operations are closure of a stable generic submodule, quotient by the resulting finite-flat subgroup, and Cartier annihilator. These operations, rather than a Jordan–Hölder theorem for an abelian category, will carry the devissage.

## 4. The local structure at the Eisenstein prime

### 4.1 Connected–étale structure over $\mathbf Z_\ell$

Let $R=\mathbf Z_\ell$ and let $G/R$ be finite flat. Since $R$ is complete henselian with perfect residue field, there is a functorial exact sequence

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0,
\tag{4.1}
$$

where $G^0$ has connected special fiber and $G^{\mathrm{et}}$ is finite étale. The quotient is maximal among finite étale quotients.

The sequence need not split. It is a filtration of the integral model, not a product decomposition. Its generic fiber is an exact sequence of étale groups, but $G^0_{\mathbf Q_\ell}$ is generally disconnected after algebraic closure: the superscript refers to the connected special fiber.

For an admissible group whose factors are the two atoms, every constant factor contributes to the étale direction and every multiplicative factor contributes to the connected direction. Proving that those factors assemble exactly into (4.1) is the local devissage carried out below.

### 4.2 The maximal multiplicative subgroup

Apply (4.1) to $G^D$ and dualize its étale quotient. Define

$$
G^{\mathrm{mult}}=\bigl((G^D)^{\mathrm{et}}\bigr)^D\subset G.
\tag{4.2}
$$

It is the maximal finite-flat subgroup of multiplicative type. Indeed, if $M\subset G$ is multiplicative, dualizing $M\subset G$ gives a quotient $G^D\twoheadrightarrow M^D$ with finite étale target. Maximality of $(G^D)^{\mathrm{et}}$ forces the quotient to factor through it, and dualizing back gives $M\subset G^{\mathrm{mult}}$.

For a general $\ell$-group there can be a local-local layer

$$
0\subset G^{\mathrm{mult}}\subset G^0\subset G.
\tag{4.3}
$$

The middle quotient has connected special fiber, and so does its dual. Admissibility by the two Eisenstein atoms will rule out order-$\ell$ local-local factors over the unramified ring $\mathbf Z_\ell$; it does not rule out a higher-height local-local group with no integral order-$\ell$ filtration.

### 4.3 Order-$\ell$ rigidity for odd $\ell$

The ramification index of $\mathbf Z_\ell$ is $e=1$. The Oort–Tate classification says that an order-$\ell$ finite-flat group over a mixed-characteristic DVR has a valuation exponent $r$ satisfying $0\le r\le e$. Thus here $r=0$ or $1$. The first endpoint is finite étale and the second multiplicative.

In Oort–Tate parameters one chooses $a,b\in\mathbf Z_\ell$ with

$$
ab=w_\ell,
\qquad v_\ell(w_\ell)=1.
\tag{4.4}
$$

The exponent is $r=v_\ell(a)$. Since $r$ is integral, the interval $0\le r\le1$ has no interior. At $r=0$ the cotangent space vanishes and the group is étale. At $r=1$ the dual parameter has exponent zero, so the Cartier dual is étale and the original group is multiplicative. This argument excludes an order-$\ell$ local-local factor over $\mathbf Z_\ell$.

For odd $\ell$ one has

$$
e=1<\ell-1.
$$

Low-ramification rigidity therefore implies that every generic map between order-$\ell$ finite-flat groups extends uniquely over $\mathbf Z_\ell$. In particular, an order-$\ell$ group with generic character $1$ is the constant endpoint, and one with generic character $\overline\chi_\ell$ is the multiplicative endpoint, up to the unramified twists already visible in the generic character.

**Proposition 4.1 (endpoint recognition).** Let $\ell$ be odd and $H/\mathbf Z_\ell$ finite flat of order $\ell$.

1. If $H_{\mathbf Q_\ell}(\overline{\mathbf Q}_\ell)$ has trivial character, then $H\simeq\underline{\mathbf Z/\ell\mathbf Z}$.
2. If its character is $\overline\chi_\ell$, then $H\simeq\mu_\ell$.

**Proof.** The indicated standard endpoint has the same generic character. The generic isomorphism extends uniquely by height-one low-ramification rigidity. Its inverse also extends, and uniqueness makes the two composites identities. $\square$

The proposition uses the full local character, not merely the tame-inertia exponent. This excludes unnoticed unramified twists.

The inequality is the decisive point in the rigidity proof. If two Oort–Tate exponents $r,r'$ have isomorphic generic characters, then

$$
r-r'\equiv0\pmod{\ell-1}.
\tag{4.5}
$$

Both lie in $\{0,1\}$. For odd $\ell$, their difference has absolute value at most one and cannot be a nonzero multiple of $\ell-1$, so $r=r'$. The ratio of their parameters is then an $(\ell-1)$st power of a unit, which is precisely the integral coordinate change. At $\ell=2$, congruence modulo one says nothing.

### 4.4 Local devissage from integral atoms

**Theorem 4.2 (local Eisenstein filtration).** Let $\ell$ be any prime and let $G/\mathbf Z_\ell$ admit an admissible filtration whose factors are integrally identified as $\underline{\mathbf Z/\ell\mathbf Z}$ or $\mu_\ell$. Then

$$
G^{\mathrm{mult}}=G^0,
$$

$G^0$ has a filtration by copies of $\mu_\ell$, and $G^{\mathrm{et}}$ has a filtration by copies of $\underline{\mathbf Z/\ell\mathbf Z}$. In particular the local-local quotient in (4.3) is zero.

**Proof strategy.** Reduce a chosen filtration to the perfect residue field and use exactness of connected components for finite group schemes over a perfect field. Each atomic factor then contributes its entire rank to exactly one side. Lift the resulting open-and-closed subgroups back to the henselian ring.

**Proof.** Over a perfect field, an exact sequence of finite group schemes induces exact connected and étale rows. To see the rank assertion directly, base change to an algebraic closure. Every component is a translate of the identity component. A torsor quotient maps components transitively onto components, its fiber over the identity has the components of the kernel, and hence

$$
|G^0|=|H^0|\,|Q^0|,
\qquad
|G^{\mathrm{et}}|=|H^{\mathrm{et}}|\,|Q^{\mathrm{et}}|.
$$

The induced maps on identity components and component groups have the corresponding ranks and are faithfully flat, which gives exactness. This argument takes place over a field, where every closed subgroup is flat.

Apply this fact successively to the reduction modulo $\ell$ of an atomic filtration of $G$. A factor $\underline{\mathbf Z/\ell}$ contributes rank $\ell$ to the étale row and rank one to the connected row; a factor $\mu_\ell$ contributes rank $\ell$ to the connected row and rank one to the étale row.

Here is the integral lifting step in detail. For every term $G_i$ of the chosen filtration, let $G_i^0$ be its henselian connected subgroup. Functoriality sends $G_i^0$ into $G^0$ and sends $G_i^0$ into $G_{i+1}^0$; because $G_i^0$ is an open-and-closed finite-flat subgroup of $G_i$, these are finite-flat closed immersions. If the next atom is constant, exactness of connected and étale ranks on the special fiber gives

$$
G_i^0=G_{i+1}^0,
\qquad
G_{i+1}^{\mathrm{et}}/G_i^{\mathrm{et}}
\simeq\underline{\mathbf Z/\ell}.
$$

If the next atom is $\mu_\ell$, the same rank calculation gives

$$
G_{i+1}^0/G_i^0\simeq\mu_\ell,
\qquad
G_i^{\mathrm{et}}=G_{i+1}^{\mathrm{et}}.
$$

The displayed maps are induced integrally by the original atomic quotient. After reduction they are the exact connected and étale rows. Surjectivity on the indicated special-fiber quotient, together with equality of finite-flat ranks, makes the integral map faithfully flat by Nakayama's lemma on coordinate algebras; its kernel is the displayed connected subgroup. In the equality cases, the finite-flat closed immersion has equal rank and is an isomorphism. Removing repeated terms therefore gives a filtration of $G^0$ by copies of $\mu_\ell$, while the nontrivial component quotients filter $G^{\mathrm{et}}$ by copies of $\underline{\mathbf Z/\ell}$.

A group filtered by $\mu_\ell$ is of multiplicative type: after Cartier duality it is filtered by finite étale groups, and extensions of finite étale groups are finite étale. Hence $G^0$ is multiplicative. Its maximality in (4.2) gives $G^{\mathrm{mult}}=G^0$. $\square$

The proof uses the existence of an admissible atomic filtration. A general height-two local-local group need not possess one, so the conclusion is not a classification of all finite-flat $\ell$-groups.

### 4.5 The dyadic failure of character separation

Over $\mathbf Z_2$ the Oort–Tate interval still has only the two exponents $0$ and $1$, so every order-two group is either the constant endpoint or $\mu_2$. But their generic characters are both trivial. Low-ramification rigidity requires $e<\ell-1$, which becomes $1<1$ and fails.

The two models can be written explicitly:

$$
\underline{\mathbf Z/2}
\quad\text{and}\quad
\mu_2=\operatorname{Spec}\mathbf Z_2[t]/(t^2-1).
\tag{4.6}
$$

After setting $x=t-1$, the second coordinate algebra is

$$
\mathbf Z_2[x]/(x^2+2x).
$$

Its special fiber is $\mathbf F_2[x]/(x^2)$, supported at one point. The constant model has coordinate algebra $\mathbf Z_2\times\mathbf Z_2$ and special fiber two reduced points. Over $\mathbf Q_2$, both are the split group with two points because $t^2-1=(t-1)(t+1)$. This calculation exhibits in one line what the generic character forgets.

Consequently Proposition 4.1 has no dyadic analogue. A generic order-two submodule can close to either endpoint depending on the ambient Hopf lattice. Cartier duality exchanges them, and the connected–étale sequence distinguishes them, but generic representation theory does not.

The local devissage theorem therefore remains true at $2$ when the integral filtration is known and its factors are identified as group schemes. What fails is recognition of those factors from their generic characters. Every two-primary application must therefore carry one additional piece of integral information: connectedness, multiplicative type, Cartier-dual étaleness, or an explicitly specified closure in an ambient group.

## 5. The admissible category

### 5.1 Filtration definition

We can now isolate the exact class required in prime-level Eisenstein arguments.

**Definition 5.1.** An object $G\in\mathcal F_\ell(S)$ is **Eisenstein-admissible** if it possesses an admissible filtration

$$
0=G_0\subset G_1\subset\cdots\subset G_m=G
\tag{5.1}
$$

such that every quotient $G_i/G_{i-1}$ is isomorphic to either

$$
\underline{\mathbf Z/\ell\mathbf Z}
\quad\text{or}\quad
\mu_\ell.
\tag{5.2}
$$

The integer $m$ is the **admissible length**. If $a$ factors are constant and $b$ are multiplicative, the pair $(a,b)$ is the **constituent multiplicity**.

Rank multiplicativity immediately gives

$$
|G|=\ell^{a+b},\qquad m=a+b.
\tag{5.3}
$$

The definition includes groups not killed by $\ell$. For instance, $\underline{\mathbf Z/\ell^r\mathbf Z}$ has a filtration by constant atoms, and $\mu_{\ell^r}$ has a filtration by multiplicative atoms. It also includes nonsplit extensions. Admissibility is an exact-filtration property, not a product presentation.

### 5.2 Independence of a chosen filtration

For odd $\ell$, the multiplicities in Definition 5.1 do not depend on the chosen admissible filtration. Restrict to $\mathbf Z_\ell$ and use Theorem 4.2. Every multiplicative atom contributes one factor to the connected subgroup, and every constant atom contributes one factor to the étale quotient. Hence

$$
|G^0_{\mathbf Z_\ell}|=\ell^b,
\qquad
|G^{\mathrm{et}}_{\mathbf Z_\ell}|=\ell^a.
\tag{5.4}
$$

These ranks are intrinsic, so $a$ and $b$ are intrinsic.

At $\ell=2$, the same conclusion holds if the filtration factors are identified integrally: constant atoms have étale special fiber and multiplicative atoms connected special fiber. It cannot be recovered from the generic semisimplification, which is trivial of dimension $a+b$ in either case.

**Proposition 5.2 (intrinsic multiplicities).** The constituent multiplicity $(a,b)$ of an admissible object is independent of the chosen integral atomic filtration. For odd $\ell$ it can be read from the generic representation as the multiplicities of $1$ and $\overline\chi_\ell$; for $\ell=2$ it must be read from the connected–étale ranks over $\mathbf Z_2$.

**Proof.** Equation (5.4) proves filtration independence in every case. When $\ell$ is odd, the two generic characters are distinct on inertia at $\ell$, so the Jordan–Hölder multiplicities equal the two ranks. When $\ell=2$, both characters are trivial and this final inference is unavailable. $\square$

### 5.3 Subobjects, quotients, and extensions

An extension of admissible objects is admissible: concatenate a filtration of the subgroup with the inverse images of a filtration of the quotient. The more useful inheritance statement begins with a stable generic submodule.

For example, the constant sequence

$$
0\to\underline{\mathbf Z/\ell\mathbf Z}
\xrightarrow{\ell^{r-1}}
\underline{\mathbf Z/\ell^r\mathbf Z}
\longrightarrow\underline{\mathbf Z/\ell^{r-1}\mathbf Z}
\to0
$$

is admissibly exact and inductively proves that $\underline{\mathbf Z/\ell^r}$ has constant length $r$. Dually, $\mu_{\ell^r}$ has the chain

$$
1\subset\mu_\ell\subset\mu_{\ell^2}\subset\cdots\subset\mu_{\ell^r},
$$

whose successive quotients are $\mu_\ell$. These examples are not products of their factors: a cyclic group of order $\ell^r$ is not a product of $r$ cyclic groups of order $\ell$. They are the simplest warning that filtration length and exponent are independent invariants.

A mixed split example is

$$
\mu_{\ell^b}\times\underline{\mathbf Z/\ell^a\mathbf Z},
$$

which has an evident separation. A Kummer class from Chapter 7 produces a mixed nonsplit example of rank $\ell^2$. The two have the same constituent multiplicity $(1,1)$ and the same generic semisimplification, but their middle group laws differ.

**Theorem 5.3 (inheritance).** Let $G$ be Eisenstein-admissible, let

$$
V=G_{\mathbf Q}(\overline{\mathbf Q}),
$$

and let $W\subset V$ be $\Gamma$-stable. Assume that $W$ and $V/W$ possess composition series whose factors, with their closures inside the corresponding successive ambient quotients of $G$, are the two atoms in (5.2). Then the closure $H\subset G$ of $W$ and the quotient $G/H$ are Eisenstein-admissible.

**Proof strategy.** Refine a composition series of $W$ to a stable flag of $V$ using the inverse images of a series for $V/W$. Closing that flag produces the required integral factors.

**Proof.** Choose

$$
0=W_0\subset\cdots\subset W_r=W
$$

with the stated closure property, choose the asserted composition series of $V/W$, and pull the latter back to $V$. The resulting stable flag passes through $W$. Proposition 2.2 closes it inside $G$. By hypothesis the factors below $W$ and above it are the appropriate atoms. Thus $H$ and $G/H$ have admissible filtrations. $\square$

The closure hypothesis in the theorem is automatic for odd $\ell$ when the generic factors are exactly $1$ and $\overline\chi_\ell$, by Proposition 4.1. At $2$ it is not automatic from the generic character. Proposition 11.1 will prove, using the integral order-two classification over $\mathbf Z_2$ and global lattice gluing, that over this particular base every such closure is nevertheless one of the two atoms. What remains unavailable at $2$ is a generic rule labeling which atom occurred.

### 5.4 Primary decomposition and coefficient actions

If a finite-flat group $G/S$ is killed by an integer $m$ prime to $N$, its primary subgroups are the images of Bezout idempotents. More concretely, for $m=ab$ with $(a,b)=1$, choose $u,v$ with $ua+vb=1$ and use the commuting endomorphisms $ua$ and $vb$. This gives a canonical product decomposition

$$
G\simeq G[a]\times G[b].
\tag{5.5}
$$

No flat-kernel difficulty occurs: the two idempotent images are direct summands of a finite locally free Hopf algebra and hence finite flat.

Suppose a finite ring $R$ acts on $G$. Idempotents of $R$ similarly cut out finite-flat direct factors. Localization at a maximal ideal is implemented at finite level by an idempotent whenever the acting quotient ring is Artinian and decomposed into its local factors. This is the legitimate route from a global Hecke-torsion group to an Eisenstein-primary piece.

An arbitrary endomorphism kernel need not be flat, so the notation $G[\mathfrak a]$ requires care. It is safe when it is a direct summand, when it is the kernel of an isogeny known to be finite flat, or when it is defined as a schematic closure inside a fixed finite-flat torsion group and flatness has been proved. A string of Hecke equations by itself does not establish flatness.

### 5.5 Separated admissible objects

The Kummer extensions used in descent have multiplicative type below and constant type above. We therefore make the orientation part of the structure.

**Definition 5.4.** An admissible object $G$ is **separated** if it fits into an admissible exact sequence

$$
0\longrightarrow M\longrightarrow G\longrightarrow C\longrightarrow0,
\tag{5.6}
$$

where $M$ is of split multiplicative $\ell$-type and $C$ is of constant $\ell$-type. A chosen sequence (5.6) is a **Mazur–Raynaud separation**.

The word does not mean split. It means that the two kinds of constituents have been placed on the correct sides of one exact sequence. Locally over $\mathbf Z_\ell$, every admissible object has such a separation, namely (4.1), by Theorem 4.2. Globally, the connected subgroup at one fiber need not spread to a global multiplicative subgroup, and finite étale constant-type objects can have monodromy at $N$. Thus a global separation must be constructed or hypothesized.

If a separation exists with $M$ the maximal split multiplicative subgroup of $G$, it is unique. Indeed any other split multiplicative subgroup lies in $M$ by maximality; equality of ranks forces equality. We will use “the separation” only under this maximality condition.

## 6. Yoneda extensions and torsor fibers

### 6.1 Extensions in an exact category

For finite-flat $S$-groups $A$ and $B$, write

$$
\operatorname{Ext}^1_S(B,A)
$$

for equivalence classes of admissible extensions

$$
0\to A\to E\to B\to0.
\tag{6.1}
$$

Two extensions are equivalent if there is an isomorphism of their middle terms inducing the identity on the endpoints. The Baer sum is formed by taking the product of two extensions, pulling back along the diagonal $B\to B\times B$, and pushing out along addition $A\times A\to A$. All maps occur among admissible pullbacks and pushouts, so the result remains finite flat.

This Yoneda group classifies integral middle terms with fixed endpoint identifications. It is finer than the extension group of generic Galois modules. Restriction to the generic fiber gives a homomorphism

$$
\operatorname{Ext}^1_S(B,A)
\longrightarrow
\operatorname{Ext}^1_\Gamma(B(\overline{\mathbf Q}),A(\overline{\mathbf Q})),
\tag{6.2}
$$

which need be neither injective nor surjective without a full-faithfulness theorem. Integral classes can become generically split, and generic extensions can fail to admit the prescribed finite-flat endpoints.

### 6.2 The fiber above one

Consider an extension

$$
0\to A\to E\xrightarrow{q}\underline{\mathbf Z/n\mathbf Z}\to0.
\tag{6.3}
$$

The fiber

$$
P=q^{-1}(1)
\tag{6.4}
$$

is an $A$-torsor. Addition in $E$ identifies the contracted product of $i$ copies of $P$ with the fiber above $i$. The $n$-fold contracted product is the fiber above zero, hence is identified with $A$ as a torsor, but the identification retains one element of $A(S)$: the “carry” obtained by adding a local lift of $1$ to itself $n$ times.

Thus an extension determines two pieces of data:

1. a torsor class $[P]\in H^1(S,A)$ killed by $n$;
2. a global carry, defined modulo $nA(S)$.

The first is geometric failure to choose a lift of $1$. The second remains even when a lift exists; it is the familiar distinction between the split group $\mathbf Z/n\times A$ and a cyclic extension such as $\mathbf Z/n^2$ in ordinary abelian groups.

### 6.3 A low-degree extension sequence

The preceding description is made exact by resolving the constant sheaf $\mathbf Z/n\mathbf Z$ as the cokernel of multiplication by $n$ on $\mathbf Z$. Applying derived Hom into an abelian fppf sheaf $A$ gives the low-degree sequence

$$
0\longrightarrow A(S)/nA(S)
\longrightarrow \operatorname{Ext}^1_S(\underline{\mathbf Z/n\mathbf Z},A)
\longrightarrow H^1(S,A)[n]
\longrightarrow0.
\tag{6.5}
$$

Here the middle group is computed in abelian fppf sheaves. When the endpoint and middle sheaves are represented by finite-flat groups, the classes under consideration are precisely the admissible finite-flat extensions: an $A$-torsor over the finite-flat quotient is finite flat, and the group law descends.

**Theorem 6.1 (torsor–carry sequence).** For finite-flat commutative $A/S$, extensions of $\underline{\mathbf Z/n\mathbf Z}$ by $A$ fit into (6.5). The right map sends an extension to the fiber above $1$, and the left map sends $a\in A(S)$ to the extension with a global lift $x$ satisfying $nx=a$.

**Proof.** Apply $R\operatorname{Hom}(-,A)$ to

$$
0\to\mathbf Z\xrightarrow{n}\mathbf Z\to\mathbf Z/n\mathbf Z\to0.
$$

Since $R\operatorname{Hom}(\mathbf Z,A)=R\Gamma(S,A)$, the long exact sequence begins

$$
A(S)\xrightarrow{n}A(S)\to\operatorname{Ext}^1(\mathbf Z/n,A)
\to H^1(S,A)\xrightarrow{n}H^1(S,A).
$$

Taking cokernel and kernel gives (6.5). Pulling an extension back along $1:S\to\underline{\mathbf Z/n}$ identifies the connecting map with the torsor fiber. If that torsor is trivial, choose a lift $x$; then $nx\in A(S)$, and replacing $x$ by $x+a'$ changes the carry by $na'$. This identifies the kernel with $A(S)/nA(S)$. $\square$

The short exact sequence need not split naturally. A splitting would require choosing compatible group laws on root torsors or compatible lifts of $1$.

There is one further formal consequence that matters at the dyadic boundary. The group

$$
\operatorname{Ext}^1_S(\underline{\mathbf Z/n\mathbf Z},A)
$$

is killed by $n$. Indeed multiplication by $n$ on an Ext group can be computed by pullback along multiplication by $n$ on its first argument, and that endomorphism of $\underline{\mathbf Z/n\mathbf Z}$ is zero. Pullback along the zero map gives the split extension. Thus (6.5) is an exact sequence of $\mathbf Z/n\mathbf Z$-modules, even though it generally has no preferred splitting.

There is also a direct construction behind the derived argument. Let $P$ be an $A$-torsor whose class is killed by $n$. Write $P^{\wedge i}$ for its $i$-fold contracted product. The disjoint union

$$
E=P^{\wedge0}\sqcup P^{\wedge1}\sqcup\cdots\sqcup P^{\wedge(n-1)}
\tag{6.6}
$$

maps to the $n$ components of $\underline{\mathbf Z/n}$. Contracted product defines addition until the indices cross $n$; to reduce an index modulo $n$, choose a trivialization of $P^{\wedge n}$. Two trivializations differ by an element of $A(S)$. Associativity follows from associativity of contracted product, and changing the trivialization by $na'$ gives an isomorphic extension after translating the chosen lift by $a'$. This recovers the left term of (6.5).

Conversely, the fibers of an extension form exactly the contracted powers of $P=E_1$. Addition in $E$ supplies a trivialization of $P^{\wedge n}$ and hence the carry. The two constructions are inverse. This hands-on model proves representability: each $P^{\wedge i}$ is a finite-flat $A$-torsor over $S$, so their finite disjoint union is finite flat, and all structure maps are morphisms of schemes by descent.

### 6.4 Baer sum and pull–push operations

Under Theorem 6.1, Baer addition multiplies torsor classes when $A$ is written multiplicatively and adds carry parameters. Pullback along multiplication by $u$ on $\mathbf Z/n$ sends the fiber class $[P]$ to $u[P]$. Pushout along an endomorphism $v$ of $A$ sends it to $v[P]$.

If $n=\ell$ and $A=\mu_\ell$, scalar multiplication by $u\in\mathbf F_\ell$ on the quotient and by $v$ on the kernel sends a Kummer class $[a]$ to

$$
[a]^{uv}=[a^{uv}].
\tag{6.7}
$$

This explains how changing generators of the two endpoints changes a numerical extension parameter. A class may be canonical only up to multiplication by $\mathbf F_\ell^\times$ unless endpoint generators have been fixed geometrically.

## 7. The flat Kummer calculation

### 7.1 $S$-units and the Picard group

The fppf Kummer sequence is exact for every $n\ge1$:

$$
1\to\mu_n\to\mathbf G_m\xrightarrow{(·)^n}\mathbf G_m\to1.
\tag{7.1}
$$

No invertibility hypothesis on $n$ is needed; an $n$th root of a unit is obtained after the finite free cover defined by $T^n-a$.

Since $\mathbf Z[1/N]$ is a localization of a principal ideal domain,

$$
\operatorname{Pic}(S)=0.
\tag{7.2}
$$

Indeed every invertible $\mathbf Z[1/N]$-module is represented by a fractional ideal. Clearing a power of $N$ identifies it with the localization of an ideal of $\mathbf Z$, and every such ideal is principal. Localization therefore leaves no ideal class.

Its units are

$$
\mathbf Z[1/N]^\times=\{\pm N^m:m\in\mathbf Z\}
\simeq\{\pm1\}\times N^{\mathbf Z}.
\tag{7.3}
$$

To verify (7.3), write a unit as $a/N^r$ in lowest terms. Its inverse is $b/N^s$, so $ab=N^{r+s}$. Unique factorization forces $a$ and $b$ to be signed powers of $N$. Conversely every signed power of $N$ is visibly a unit.

The degree-one Kummer sequence therefore gives

$$
H^1(S,\mu_n)\simeq
\mathbf Z[1/N]^\times/\mathbf Z[1/N]^{\times n}.
\tag{7.4}
$$

The class of a unit $a$ is represented by the finite-flat $\mu_n$-torsor

$$
P_a=\operatorname{Spec}\mathbf Z[1/N,T]/(T^n-a),
\tag{7.5}
$$

with $\mu_n$ acting by multiplication on $T$.

### 7.2 Odd Eisenstein primes

For odd $\ell$, $-1=(-1)^\ell$ is an $\ell$th power. Equations (7.3)–(7.4) give

$$
H^1(S,\mu_\ell)\simeq
\langle[N]\rangle\simeq\mathbf Z/\ell\mathbf Z.
\tag{7.6}
$$

Moreover $\mu_\ell(S)$ is trivial: the only rational roots of unity are $\pm1$, and $-1$ does not have odd order. The torsor–carry sequence becomes an isomorphism.

**Theorem 7.1 (odd atomic extension calculation).** If $\ell$ is odd, then

$$
\operatorname{Ext}^1_S
(\underline{\mathbf Z/\ell\mathbf Z},\mu_\ell)
\simeq H^1(S,\mu_\ell)
\simeq\mathbf Z/\ell\mathbf Z,
\tag{7.7}
$$

and the class of $N$ is a generator.

**Proof.** Put $n=\ell$ and $A=\mu_\ell$ in (6.5). Multiplication by $\ell$ is zero on $A$, but $A(S)=1$, so the left term vanishes. Every element of $H^1(S,\mu_\ell)$ is killed by $\ell$, giving the first isomorphism. Equation (7.6) gives the second and its generator. $\square$

This is the central flat-cohomology calculation. It classifies one orientation only: multiplicative kernel and constant quotient.

The calculation is especially concrete at level $N=11$. Here $n_{11}=5$, so $\ell=5$ and

$$
\operatorname{Ext}^1_{\mathbf Z[1/11]}
(\underline{\mathbf Z/5},\mu_5)
=\{e_1,e_{11},e_{11^2},e_{11^3},e_{11^4}\}.
$$

The first class is split. The fiber above $1$ in the other four is respectively
$T^5=11^j$, $1\le j\le4$. Their generic classes are distinct because their $11$-adic valuations are distinct modulo $5$. Rescaling the constant generator by $j^{-1}$ carries each nonsplit class to $T^5=11$, but with the cusp generator fixed the four exponents remain distinct.

### 7.3 Explicit root torsors

Let $e_a$ denote the extension class corresponding to $[a]\in S^\times/S^{\times\ell}$. Its fiber over $1$ is $P_a$. The extension is split if and only if $P_a(S)$ is nonempty, equivalently if and only if $a$ is an $\ell$th power in $S^\times$.

For $a=N^j$, the classes satisfy

$$
e_{N^i}+e_{N^j}=e_{N^{i+j}},
\qquad
u\cdot e_N=e_{N^u}\quad(u\in\mathbf F_\ell).
\tag{7.8}
$$

Thus every nonsplit class is a generator of the cyclic extension group after changing one endpoint generator. With fixed cuspidal and Shimura generators, however, the exponent $j$ carries meaningful normalization data and should not be discarded.

The equation $T^\ell=N$ is a torsor over $S$ because $N$ is a unit there. It would not be a $\mu_\ell$-torsor over $\operatorname{Spec}\mathbf Z$: its right side vanishes on the fiber at $N$. This is exactly why the level prime is removed.

### 7.4 Localization of the Kummer class

At a prime $r\ne N$, restriction sends $[N]$ to

$$
[N]\in\mathbf Z_r^\times/\mathbf Z_r^{\times\ell}.
\tag{7.9}
$$

At $r\ne\ell$, the torsor is finite étale because $\ell$ is invertible. Its class measures ordinary unramified Frobenius data. At $r=\ell$, it is finite flat but may be ramified as a cover; fppf cohomology is essential.

There is a useful local splitness test away from $\ell$. Reduce $N$ in the residue field $\mathbf F_r^\times$. If its residue is not an $\ell$th power, then $T^\ell=N$ has no section over $\mathbf Z_r$ and the localized extension is nonsplit. If the residue is an $\ell$th power and $\ell$ is invertible mod $r$, Hensel's lemma lifts a simple root, so the extension splits over $\mathbf Z_r$. At $r=\ell$, reduction is not a simple-root test because the derivative $\ell T^{\ell-1}$ vanishes modulo $\ell$.

At the removed prime $N$, the generic Kummer field has ramification detected by valuation. This is why a global class may be nontrivial even when it becomes split at many primes of $S$.

Over the generic field,

$$
[N]\in\mathbf Q^\times/\mathbf Q^{\times\ell}
$$

is nonzero because the $N$-adic valuation of an $\ell$th power is divisible by $\ell$, whereas $v_N(N)=1$. Thus the generator in (7.7) does not become split generically. More generally $[N^j]$ is generically trivial exactly when $j\equiv0\pmod\ell$.

This valuation argument proves injectivity of the restriction of the cyclic subgroup generated by $[N]$ without any assertion that generic-fiber restriction is injective on all finite-flat extension groups.

### 7.5 The two-primary calculation

For $\ell=2$, the sign is no longer a square and

$$
H^1(S,\mu_2)\simeq
S^\times/S^{\times2}
\simeq(\mathbf Z/2\mathbf Z)[-1]
\oplus(\mathbf Z/2\mathbf Z)[N].
\tag{7.10}
$$

Also

$$
\mu_2(S)=\{\pm1\}\simeq\mathbf Z/2\mathbf Z,
$$

and multiplication by $2$ on it is zero. Therefore (6.5) gives

$$
0\to\mathbf Z/2\mathbf Z
\to\operatorname{Ext}^1_S
(\underline{\mathbf Z/2\mathbf Z},\mu_2)
\to(\mathbf Z/2\mathbf Z)^2\to0.
\tag{7.11}
$$

In particular the extension group has eight elements. The kernel is the carry class: its fiber above $1$ is the trivial $\mu_2$-torsor, but a chosen lift $x$ satisfies $2x=-1\in\mu_2(S)$ rather than $2x=1$.

The observation following Theorem 6.1 shows that the middle group is also killed by $2$. Consequently

$$
\operatorname{Ext}^1_S
(\underline{\mathbf Z/2\mathbf Z},\mu_2)
\simeq(\mathbf Z/2\mathbf Z)^3
\tag{7.12}
$$

as an abstract group. This isomorphism is not canonical: (7.11) gives a canonical one-dimensional carry subspace and a canonical two-dimensional torsor quotient, but it chooses no complementary lift of that quotient. Thus $[-1]$ and $[N]$ are canonical coordinates only after passage to the torsor quotient; choosing extension classes above them is an additional, noncanonical splitting choice.

The dyadic extension problem is therefore larger in two distinct ways: the two atomic generic characters coincide, and the atomic extension group has three binary parameters rather than one cyclic parameter.

At level $N=17$, one has $n_{17}=4$. The first atomic two-primary layer therefore sees

$$
S^\times/S^{\times2}
=\{[1],[-1],[17],[-17]\}.
$$

Above each of these four torsor classes lie two extension classes distinguished by the carry. Thus even before one studies how two atomic layers assemble into order four endpoints, there are eight possible mixed order-four extensions with fixed order-two endpoints. Treating the dyadic problem as the odd calculation with $\ell=2$ would retain only the classes $[1]$ and $[17]$ and lose both the sign and the carry.

## 8. Extensions of a constant atom by a multiplicative atom

### 8.1 Classification for odd $\ell$

Fix odd $\ell$. An admissible extension

$$
0\longrightarrow\mu_\ell\longrightarrow E
\longrightarrow\underline{\mathbf Z/\ell\mathbf Z}
\longrightarrow0
\tag{8.1}
$$

is determined, with the endpoint identifications fixed, by a unique exponent $j\in\mathbf F_\ell$ such that the fiber above $1$ is

$$
T^\ell=N^j.
\tag{8.2}
$$

It is split precisely when $j=0$. Every nonzero $j$ becomes $1$ after rescaling one endpoint, but not after an equivalence fixing both endpoints.

**Corollary 8.1.** There are exactly $\ell$ equivalence classes of (8.1). One is split, and $\ell-1$ are nonsplit. The nonsplit classes form one orbit under either endpoint automorphism group $\mathbf F_\ell^\times$.

**Proof.** This is Theorem 7.1 together with the scalar action (6.7). $\square$

The middle group has rank $\ell^2$ and is killed by $\ell$. Indeed $[\ell]_E$ is zero on the kernel and on the quotient, hence factors as a homomorphism $\underline{\mathbf Z/\ell}\to\mu_\ell$; such a homomorphism is the same as a global $\ell$th root of unity, and there is none for odd $\ell$. This is special to the atomic odd-prime calculation. An arbitrary extension of two objects killed by $\ell$ need only be killed by $\ell^2$.

### 8.2 The carry parameter

For general $n$ and $A$, a trivial fiber torsor does not force a split extension. Choose $x\in E(S)$ over $1$. The obstruction is

$$
nx\in A(S)/nA(S).
\tag{8.3}
$$

Changing $x$ changes this by $nA(S)$, and it vanishes exactly when $x$ can be adjusted to a homomorphic section.

For $A=\mu_\ell$ over $S$, the carry disappears at odd $\ell$ because there is no nontrivial global $\ell$th root of unity. At $2$, $-1$ supplies a nonzero carry. This is not the Kummer sign torsor $T^2=-1$: the latter has no global lift of $1$, while the carry extension has a global lift whose double is the nontrivial kernel point. The two classes map to different terms of (7.11).

### 8.3 Splitness and restriction

An extension can be tested after faithfully flat base change: it splits over $S'$ if and only if its class restricts to zero in the corresponding Ext group. For the odd class $e_{N^j}$, adjoining an $\ell$th root of $N^j$ trivializes the torsor fiber and hence the extension, because there is no carry.

Restriction from $S$ to the generic point preserves nonsplitness of every $e_{N^j}$ with $j\ne0$, by the $N$-adic valuation argument. Restriction to $S_r$ can kill it for some $r$: this merely says that $N^j$ has an $\ell$th root in $\mathbf Z_r^\times$. Local splitness at one prime does not imply global splitness.

Conversely, a generic extension with the correct two characters need not be one of (8.1). It must first admit a finite-flat model over every $r\ne N$ with the prescribed endpoints. Theorem 7.1 classifies the integral extensions after that condition has been met; it does not turn every generic cohomology class into an integral one.

### 8.4 Duality of extension classes

Dualizing (8.1) gives

$$
0\longrightarrow
(\underline{\mathbf Z/\ell\mathbf Z})^D
\longrightarrow E^D\longrightarrow(\mu_\ell)^D\longrightarrow0,
$$

which, using (1.2), is again an extension of the form (8.1). Thus Cartier duality induces an involution

$$
D:\operatorname{Ext}^1_S
(\underline{\mathbf Z/\ell\mathbf Z},\mu_\ell)
\longrightarrow
\operatorname{Ext}^1_S
(\underline{\mathbf Z/\ell\mathbf Z},\mu_\ell).
\tag{8.4}
$$

It is additive because duality reverses the pullback–pushout construction symmetrically. After fixing dual generators of the endpoints, it acts by multiplication by a unit of $\mathbf F_\ell$ on the cyclic group (7.7). The unit depends on the convention identifying each endpoint with its bidual. Arguments needing its exact sign must fix the evaluation pairing; arguments needing only split versus nonsplit do not.

For a self-dual middle group with a specified perfect pairing, the induced endpoint identifications remove this ambiguity and constrain the class to the appropriate eigenspace of $D$.

### 8.5 What this calculation does not classify

The group in (7.7) does not classify:

- extensions $0\to\underline{\mathbf Z/\ell}\to E\to\mu_\ell\to0$ in the opposite orientation;
- extensions between two constant-type objects of higher length;
- extensions between two multiplicative-type objects of higher length;
- generic Galois extensions lacking finite-flat endpoint models;
- finite-flat groups with local-local constituents;
- higher $\ell$-power extensions without a chosen atomic filtration.

These omissions are mathematical boundaries. In particular, reversing an extension is not the same as Cartier dualizing it: duality preserves the orientation “multiplicative kernel, constant quotient” because it exchanges both endpoints while reversing the arrows. Any proof that needs to place a constant subgroup below a multiplicative quotient must supply a separate vanishing or construction.

## 9. Devissage with exact hypotheses

### 9.1 Length and multiplicities

For an admissible $G$ with constituent multiplicity $(a,b)$, define

$$
\operatorname{len}(G)=a+b,
\qquad
\operatorname{len}_{\mathrm c}(G)=a,
\qquad
\operatorname{len}_{\mathrm m}(G)=b.
\tag{9.1}
$$

Every admissible exact sequence

$$
0\to G'\to G\to G''\to0
$$

is additive for these three functions whenever two of the objects are equipped with compatible admissible filtrations. Indeed ranks multiply, and after localization at $\ell$ the connected and étale ranks multiply separately. Thus

$$
\begin{aligned}
\operatorname{len}_{\mathrm c}(G)
&=\operatorname{len}_{\mathrm c}(G')+
\operatorname{len}_{\mathrm c}(G''),\\
\operatorname{len}_{\mathrm m}(G)
&=\operatorname{len}_{\mathrm m}(G')+
\operatorname{len}_{\mathrm m}(G'').
\end{aligned}
\tag{9.2}
$$

These identities are often more useful than a chosen composition series. They give an invariant check that a proposed multiplicative subgroup or constant quotient has the expected full rank.

### 9.2 Induction through an admissible flag

Let $P$ be a property of admissible objects satisfying:

1. $P$ holds for $\underline{\mathbf Z/\ell}$ and $\mu_\ell$;
2. in every admissible sequence, $P(G')$ and $P(G'')$ imply $P(G)$.

Then $P$ holds for every admissible object, by induction along (5.1). This elementary principle becomes substantive only after the extension step has been proved. Examples include finite flatness after a permitted base change, annihilation by a fixed ideal acting trivially on every successive extension rather than merely on each factor, and compatibility of a pairing filtration.

Annihilation illustrates a common trap. If $x$ kills $G'$ and $G''$, then $xG$ lands in $G'$ and a second application kills it, so only

$$
x^2G=0
\tag{9.3}
$$

is automatic. To prove $xG=0$, one must show the induced map $G''\to G'$ vanishes. Constituentwise annihilation alone does not suffice.

For odd $\ell$, cross maps between the two atoms vanish:

$$
\operatorname{Hom}_S(\underline{\mathbf Z/\ell},\mu_\ell)=0,
\qquad
\operatorname{Hom}_S(\mu_\ell,\underline{\mathbf Z/\ell})=0.
\tag{9.4}
$$

The first group is $\mu_\ell(S)$, which is trivial. A map in the second direction is generically a map from character $\overline\chi_\ell$ to $1$, hence zero; faithfulness of the generic fiber then makes it zero integrally. At $2$ the first vanishing fails.

### 9.3 The separated filtration theorem

**Theorem 9.1 (separated devissage).** Let $G$ have a Mazur–Raynaud separation

$$
0\to M\to G\to C\to0
\tag{9.5}
$$

of multiplicities $(a,b)$. Then:

1. $M$ has rank $\ell^b$ and $C$ has rank $\ell^a$;
2. localization at $\ell$ identifies $M$ with $G^0=G^{\mathrm{mult}}$ and $C$ with $G^{\mathrm{et}}$;
3. Cartier duality gives a separated sequence

   $$
   0\to C^D\to G^D\to M^D\to0;
   \tag{9.6}
   $$

4. every filtration of $M$ and $C$ by their atoms concatenates to an admissible filtration of $G$;
5. if $M$ is maximal among split multiplicative subgroups, then (9.5) is unique.

**Proof.** The rank statements follow from the definitions and (5.3). Over $\mathbf Z_\ell$, $M$ is connected multiplicative and $C$ finite étale, so functorial maximality in (4.1) and (4.2) gives the identifications in item 2; equality follows from the matching ranks. Exact Cartier duality gives (9.6) and exchanges the endpoint types. Pulling back a filtration of $C$ to $G$ and placing it above a filtration of $M$ proves item 4. For item 5, every competing split multiplicative subgroup lies in the maximal one; matching rank forces equality, and represented quotients are then canonically equal. $\square$

The theorem packages consequences of a global separation; it does not assert that the local subgroup $G^0_{\mathbf Z_\ell}$ descends globally. In applications, a global Shimura subgroup or a closure of a cyclotomic generic line supplies $M$.

One can visualize the filtration as a rectangle of lengths rather than a direct sum:

$$
\begin{array}{ccccccccc}
0&\subset&M_1&\subset&\cdots&\subset&M_b=M&\subset&G\\
&&\mu_\ell&&\cdots&&\mu_\ell&&\\[-2mm]
&&&&&&&\twoheadrightarrow&C,\\
&&&&&&&&0\subset C_1\subset\cdots\subset C_a=C .
\end{array}
$$

The lower row is lifted to $G$ by inverse image. Nothing in this diagram provides complements for the inclusions. Its content is exactness and rank, not a choice of coordinates on $G$.

For instance, an object fitting into

$$
0\to\mu_{\ell^2}\to G\to
\underline{\mathbf Z/\ell^3}\to0
$$

has multiplicity $(3,2)$ and rank $\ell^5$. Its multiplication-by-$\ell$ filtration may meet the separation in a nontrivial way, and the extension class is not determined by five atomic Kummer parameters: extensions within $\mu_{\ell^2}$ and within the constant quotient have already been assembled, while compatibility of lifts across powers of $\ell$ imposes further conditions. Atomic devissage gives bounds and successive invariants, not an automatic classification at height five.

### 9.4 Homomorphisms detected on constituents

Let $f:G\to H$ be a morphism of separated admissible objects that preserves the chosen multiplicative subgroups. It induces maps

$$
f_{\mathrm m}:M_G\to M_H,
\qquad
f_{\mathrm c}:C_G\to C_H.
$$

If both are zero, $f$ factors as

$$
G\twoheadrightarrow C_G\xrightarrow{\bar f}M_H\hookrightarrow H.
\tag{9.7}
$$

Thus $f=0$ whenever $\operatorname{Hom}(C_G,M_H)=0$. For odd $\ell$, this vanishing holds when both objects are killed by $\ell$ and their endpoint filtrations split into the atoms with no same-type intermediate monodromy: devissage using (9.4) kills each atomic map. For higher exponent or nonsplit constant-type objects, the Hom group must be checked rather than assumed.

This observation is the clean way to strengthen constituentwise annihilation. If a Hecke operator $x$ kills both endpoint objects in (9.5), then $x_G$ has the factorization (9.7). A vanishing theorem for $\operatorname{Hom}(C,M)$ makes $x$ kill $G$; without it, only a square-zero conclusion is justified.

### 9.5 Annihilation and rank bounds

Suppose an ideal $\mathfrak a$ of a commutative ring acts on a length-$m$ admissible object and kills every atomic quotient. Repeatedly applying the observation leading to (9.3) gives

$$
\mathfrak a^mG=0.
\tag{9.8}
$$

This bound is crude but unconditional. If the action respects a separation and cross Hom groups vanish, it improves to the maximum of the nilpotence exponents on $M$ and $C$. If the ideal kills the endpoints themselves and $\operatorname{Hom}(C,M)=0$, it kills $G$.

Rank supplies an independent control. A nonzero map between order-$\ell$ atoms at odd $\ell$ is an isomorphism when the types match, and is zero when they differ. Hence a morphism that is generically injective on every successive constituent has full generic rank. It becomes an isomorphism integrally only after its image has been shown finite flat and of equal rank. Equal generic rank alone does not rule out a nonflat special kernel.

## 10. Cartier duality, pairings, and self-dual objects

### 10.1 Dual admissibility

Dualizing an admissible flag reverses it. If

$$
0=G_0\subset G_1\subset\cdots\subset G_m=G,
$$

then the annihilators give

$$
0=G_m^\perp\subset G_{m-1}^\perp\subset\cdots
\subset G_0^\perp=G^D,
\tag{10.1}
$$

and

$$
G_{i-1}^\perp/G_i^\perp\simeq(G_i/G_{i-1})^D.
\tag{10.2}
$$

Thus $G^D$ is admissible with multiplicity $(b,a)$ if $G$ has multiplicity $(a,b)$. Duality preserves total length and exchanges the connected and étale ranks at $\ell$.

The statement uses annihilators in admissible exact sequences. It does not dualize a nonflat scheme-theoretic kernel as though it were finite flat.

### 10.2 Annihilator filtrations

Let $H\subset G$ be a finite-flat subgroup and suppose $G$ carries a perfect pairing

$$
e:G\times G\longrightarrow\mu_{\ell^r}.
\tag{10.3}
$$

The pairing identifies $G$ with the appropriate Cartier dual, and the annihilator

$$
H^\perp=\{g:e(g,H)=1\}
$$

is finite flat. Perfectness gives the rank formula

$$
|H|\,|H^\perp|=|G|.
\tag{10.4}
$$

If $H$ is the closure of a generic subspace, then $H^\perp$ is the closure of its generic orthogonal. Consequently isotropy can often be checked generically: if $e$ is trivial on $H_{\mathbf Q}\times H_{\mathbf Q}$, it is trivial on $H\times H$ because the source is flat and the target separated.

### 10.3 Perfect pairings

Assume $G$ is killed by $\ell$ and (10.3) takes values in $\mu_\ell$. On generic geometric points it is an $\mathbf F_\ell$-bilinear pairing

$$
V\times V\to\mathbf F_\ell(1).
$$

If it is perfect, then

$$
V\simeq V^\vee(1),
\tag{10.5}
$$

and the multiset of generic characters is stable under
$\psi\mapsto\overline\chi_\ell\psi^{-1}$. For the Eisenstein atoms this simply exchanges $1$ and $\overline\chi_\ell$, so a self-dual admissible object has equal constant and multiplicative multiplicities.

At $\ell=2$ equality of generic characters does not prove equality of integral multiplicities. The pairing does: Cartier self-duality exchanges the connected and étale ranks and therefore forces them to agree.

### 10.4 A height-two self-dual pattern

Let $G/S$ be finite flat of order $\ell^2$, killed by $\ell$, with a perfect alternating pairing $G\times G\to\mu_\ell$. Suppose the generic module has a stable line $W$, and let $H$ be its closure. Alternation makes $W$ isotropic. Hence $H\subset H^\perp$, while (10.4) gives

$$
|H^\perp|=\frac{\ell^2}{\ell}=\ell=|H|.
$$

Both are closures of the same generic line, so $H=H^\perp$. Therefore

$$
0\longrightarrow H\longrightarrow G\longrightarrow H^D\longrightarrow0.
\tag{10.6}
$$

For odd $\ell$, if $W$ has character $\overline\chi_\ell$, Proposition 4.1 identifies $H$ with $\mu_\ell$ locally at $\ell$ and hence globally with $\mu_\ell$ once the generic character is globally cyclotomic. The quotient is constant. Thus $G$ is one of the $\ell$ classes in Theorem 7.1.

If $W$ has trivial character, then $H$ is constant and the quotient multiplicative. This is the opposite orientation and is not classified by Theorem 7.1. A polarization does not by itself change that orientation. At $2$, even the integral type of $H$ must be supplied by the ambient closure.

## 11. Schematic closure in arithmetic torsion

### 11.1 The fixed ambient model principle

Let $A/S$ be an abelian scheme and let $m$ be any positive integer. Multiplication by $m$ is finite flat, so

$$
A[m]=\ker([m]:A\to A)
$$

is finite flat of order $m^{2\dim A}$. If $W\subset A[m]_{\mathbf Q}(\overline{\mathbf Q})$ is a stable subgroup, its closure inside $A[m]$ is finite flat by Theorem 2.1.

The ambient group $A[m]$ is essential. Closing $W$ merely as a subset of the proper scheme $A$ does not prove flatness. Factoring through the finite torsion group converts the question into saturation of a finite Hopf algebra.

Likewise, two isomorphic generic groups can acquire different closures in two different abelian schemes or in two different integral quotients. Closure is canonical inside a fixed ambient model, not across all possible models.

### 11.2 Closing an Eisenstein line

**Proposition 11.1 (global endpoint recognition and dyadic dichotomy).** Let $\ell$ be prime, let $G/S$ be finite flat, and let $W\subset G_{\mathbf Q}(\overline{\mathbf Q})$ be a stable line of order $\ell$. Let $H$ be its closure.

1. If $\ell$ is odd and $W\simeq\mathbf F_\ell$ as a global $\Gamma$-module, then $H\simeq\underline{\mathbf Z/\ell\mathbf Z}$.
2. If $\ell$ is odd and $W\simeq\mathbf F_\ell(1)$, then $H\simeq\mu_\ell$.
3. If $\ell=2$, then $H$ is isomorphic to exactly one of $\underline{\mathbf Z/2\mathbf Z}$ and $\mu_2$. It is the constant endpoint when its special fiber at $2$ is étale and the multiplicative endpoint when that fiber is connected.

**Proof strategy.** Compare $H$ with a standard model at every height-one point of $S$. Away from $\ell$ uniqueness of finite étale extension applies. At an odd $\ell$ use low-ramification rigidity; at $2$ use the two-endpoint Oort–Tate classification and inspect connectedness. Then recover the global Hopf lattice as the intersection of its localizations.

**Proof.** Suppose first that $\ell$ is odd. Fix a global generic isomorphism from $H_{\mathbf Q}$ to the appropriate standard endpoint. For $r\ne N,\ell$, both integral groups are finite étale models of the same unramified generic representation, so that particular generic isomorphism extends uniquely over $\mathbf Z_r$. At $r=\ell$, Proposition 4.1 and height-one full faithfulness extend the same generic isomorphism.

Now let $\ell=2$. Every one-dimensional $\mathbf F_2$-module is trivial, so $H_{\mathbf Q}$ is the split group of order two. Over the unramified dyadic DVR $\mathbf Z_2$, the Oort–Tate interval has only its two endpoints. Thus $H_{\mathbf Z_2}$ is constant if its special fiber is étale and is $\mu_2$ if its special fiber is connected. Let $E$ be that standard global endpoint. The generic isomorphism $H_{\mathbf Q}\simeq E_{\mathbf Q}$ is unique because the group of order two has no nontrivial automorphism. For every $r\ne N,2$, both local groups are finite étale models of this split generic group, so the same isomorphism extends uniquely over $\mathbf Z_r$; by construction it also extends over $\mathbf Z_2$.

In either case, view both coordinate Hopf algebras as finite projective $\mathbf Z[1/N]$-lattices in one fixed generic Hopf algebra. The local extensions say that their localizations agree at every nonzero prime. A projective lattice over a Dedekind domain is the intersection of these localizations inside its generic vector space. The two global Hopf lattices are equal, which gives the required global isomorphism. The two dyadic endpoints cannot both occur because their special fibers have different connectedness. $\square$

At $2$, what fails is character recognition, not the endpoint dichotomy. The globally trivial generic line does not say which of the two models occurs; the connectedness of its actual closure does.

### 11.3 Quotients and flat images

If $H$ is the closure of $W$ in $G$, the quotient $G/H$ is represented and finite flat, and its generic module is $V/W$. If $W'\supset W$ is another stable subgroup, successive quotient gives

$$
(G/H)/(H'/H)\simeq G/H'.
\tag{11.1}
$$

This identity is an identity of represented fppf quotients, not of pointwise cosets.

For a generic homomorphism $f_{\mathbf Q}:G_{\mathbf Q}\to G'_{\mathbf Q}$, define the **flat image** to be the closure of its generic image in $G'$. The original integral map, if it exists, need not be faithfully flat onto that closure. A flat-image factorization therefore requires a separate check that the coimage maps to the closure as a torsor. Equal generic images do not supply that check.

In Eisenstein applications the safest construction is to begin with a stable generic submodule of an already finite-flat torsion group, close it, and take its represented quotient. This automatically supplies an admissible sequence.

### 11.4 Intersections of constant and multiplicative lines

Let $C,M\subset G$ be finite-flat subgroups isomorphic to the constant and multiplicative atoms. For odd $\ell$, their generic intersection is zero because the characters differ. The flat closure of that generic intersection is therefore the trivial group. Hence the **flat intersection** is zero.

The raw scheme-theoretic intersection can nevertheless carry vertical nonflat structure. It must not be used as an admissible subgroup until flatness is proved. If it is finite flat, closure uniqueness forces it to be trivial.

At $2$, the generic subgroups may coincide because the two characters are the same. Distinct integral closures of that common generic line cannot both lie inside one fixed finite-flat ambient group: uniqueness of closure would identify them. Thus, inside a fixed $G$, a given stable generic line has exactly one of the two endpoint types. This fact is the basic replacement for character separation at the dyadic boundary.

## 12. The prime-level Eisenstein application

### 12.1 Cuspidal and Shimura input

Book 133 establishes the following prime-level generic package. The cuspidal divisor

$$
c=[0]-[\infty]\in J_0(N)(\mathbf Q)
$$

has exact order $n_N$, and its generated generic subgroup is constant:

$$
C_{N,\mathbf Q}\simeq\underline{\mathbf Z/n_N\mathbf Z}_{\mathbf Q}.
\tag{12.1}
$$

The auxiliary Shimura kernel is diagonalizable cyclic of the same order on the generic fiber:

$$
\Sigma_{N,\mathbf Q}\simeq\mu_{n_N,\mathbf Q}
\tag{12.2}
$$

noncanonically. Both are annihilated by the Eisenstein ideal $I$, and the Hecke action on the cuspidal generator is

$$
T_r c=(1+r)c\quad(r\ne N),\qquad U_Nc=c.
\tag{12.3}
$$

The word “noncanonically” in (12.2) matters. A generator of the character group is needed to identify $\Sigma_{N,\mathbf Q}$ with a particular $\mu_{n_N,\mathbf Q}$. Statements invariant under endpoint automorphisms do not require that choice; a numerical Kummer exponent does.

### 12.2 Localization at an Eisenstein prime

Let

$$
e=v_\ell(n_N).
$$

Let $\mathcal J/S$ be the abelian scheme obtained by restricting the Néron model of $J_0(N)$ to its good-reduction locus. Close the primary pieces of (12.1)–(12.2) inside $\mathcal J[\ell^e]$ and denote them by $\mathcal C_{N,\ell}$ and $\mathcal\Sigma_{N,\ell}$. Schematic closure makes both finite flat. If $\ell$ is odd, close their canonical generic cyclic filtrations. Global endpoint recognition gives

$$
\begin{aligned}
0=\mathcal C_0&\subset\mathcal C_1\subset\cdots\subset
\mathcal C_e=\mathcal C_{N,\ell},
&\mathcal C_i/\mathcal C_{i-1}&\simeq\underline{\mathbf Z/\ell},\\
0=\mathcal\Sigma_0&\subset\mathcal\Sigma_1\subset\cdots\subset
\mathcal\Sigma_e=\mathcal\Sigma_{N,\ell},
&\mathcal\Sigma_i/\mathcal\Sigma_{i-1}&\simeq\mu_\ell.
\end{aligned}
\tag{12.4}
$$

Thus the closures are of constant type and split multiplicative type of length $e$. This conclusion does not identify the entire higher-power model with $\underline{\mathbf Z/\ell^e}$ or $\mu_{\ell^e}$; such an identification would require a higher-height rigidity theorem.

The closures remain Hecke-stable. If $T$ preserves a generic subgroup $H_{\mathbf Q}$, then $T$ carries its closure into another finite-flat subgroup with generic fiber contained in $H_{\mathbf Q}$. Closure uniqueness forces the image to lie in the original closure. If an element of the Eisenstein ideal is zero on $H_{\mathbf Q}$, its restriction to the closure is zero because the generic-fiber functor is faithful. Thus the annihilation proved generically in Book 133 passes to these particular closures without taking a potentially nonflat Hecke kernel.

The two filtrations in (12.4) are also Hecke-stable: their generic terms are the unique subgroups of each order in a cyclic generic group, hence stable under every endomorphism preserving the whole group. Uniqueness of closure then propagates stability integrally.

Since $\ell\mid n_N$, one has $\ell\mid N-1$ and hence $\ell\ne N$. No claim about the intersection of these closures inside $\mathcal J$ is needed for this book, and no full Shimura-subgroup intersection theorem is used. At $\ell=2$, Proposition 11.1 shows that every successive closure is one of the two atoms, so both primary closures are admissible. What is not inferred from the generic identifications is the named orientation displayed in (12.4): proving specifically that the cuspidal factors are constant and the Shimura factors multiplicative requires an integral connectedness or duality check.

The Hecke eigenvalues on the two generic atoms explain the Eisenstein trace. At a prime $r\nmid N\ell$, Frobenius acts by $1$ on the constant line and by $r$ on the cyclotomic line, so the trace is

$$
1+r\pmod\ell
\tag{12.5}
$$

and the determinant is $r$. This matches (12.3). The converse requires care: these trace and determinant values determine the semisimplification of a two-dimensional representation once the characteristic polynomials are known densely enough, but the group-scheme criterion requires a stable line and hence actual reducibility.

### 12.3 The admissibility criterion for a selected quotient

The following theorem is the precise bridge from generic Eisenstein data to finite-flat admissibility.

**Theorem 12.1 (Eisenstein closure criterion).** Let $G/S$ be a finite-flat $\ell$-primary group contained in the torsion of a fixed abelian scheme over $S$. Suppose its generic Galois module $V$ has a stable composition series whose factors are $\mathbf F_\ell$ or $\mathbf F_\ell(1)$.

Then $G$ is Eisenstein-admissible for every $\ell$. For odd $\ell$, the generic character labels each factor as constant or multiplicative. For $\ell=2$, each factor is still one of the two atoms, but its label is determined only after taking its integral closure.

**Proof.** Close the stable composition series inside $G$ by Proposition 2.2. For odd $\ell$, Proposition 11.1 identifies every order-$\ell$ closure with the standard endpoint dictated by its generic character. For $\ell=2$, the dyadic part of the same proposition identifies every order-two closure as one of the two standard endpoints, with its type read from connectedness at $2$. Thus in every case the closure filtration is admissible. $\square$

The theorem assumes an actual stable series, not just a trace congruence. In a two-dimensional representation, trace $1+\overline\chi_\ell$ and determinant $\overline\chi_\ell$ determine the semisimplification but do not by themselves produce a stable line. Reducibility, or a geometrically supplied subgroup, is a separate input.

### 12.4 The control theorem

**Theorem 12.2 (atomic Eisenstein control).** Let $\ell$ be odd and let $G/S$ be finite flat of order $\ell^2$. Suppose there is an admissible sequence

$$
0\longrightarrow\mathcal\Sigma_1
\longrightarrow G\longrightarrow\mathcal C_e/\mathcal C_{e-1}
\longrightarrow0,
\tag{12.6}
$$

with chosen identifications of the endpoints. Then a unique $j\in\mathbf F_\ell$ determines $G$, and the fiber over the chosen cuspidal generator is

$$
T^\ell=N^j.
\tag{12.7}
$$

The sequence splits if and only if $j=0$. After forgetting endpoint generators, there are only two possibilities: split and nonsplit.

**Proof.** Under (12.4), the endpoints in (12.6) are $\mu_\ell$ and $\underline{\mathbf Z/\ell}$. Replace them by these standard models using the chosen identifications, take the fiber above the chosen constant generator, and apply Theorem 7.1 and Corollary 8.1. $\square$

At $N=19$, one has $n_{19}=3$. Any height-two separated layer with the indicated endpoints is therefore one of

$$
T^3=1,\qquad T^3=19,\qquad T^3=19^2.
\tag{12.8}
$$

The first is split and the last two are equivalent after changing an endpoint generator, though distinct with the cuspidal generator fixed.

At $N=73$, one has $n_{73}=6$. The odd primary piece at $\ell=3$ has the same three-class pattern with $73$ replacing $19$. The two-primary piece must instead use the eight-class dyadic sequence. Primary decomposition separates these calculations because $2$ and $3$ are coprime; it does not identify or compare their extension parameters.

For higher length, choose filtrations of $\mathcal\Sigma_{N,\ell}$ and $\mathcal C_{N,\ell}$. Pulling and pushing a separated object through successive layers reduces questions about it to atomic extensions, same-type extensions, and compatibility among the layers. Every mixed atomic layer in the orientation of (12.6) has a Kummer parameter in the one-dimensional group generated by $[N]$. Same-type layers are not classified by that statement and must remain part of the Hecke-module data.

### 12.5 What passes to completed Hecke pieces

Suppose a later construction produces a finite-flat Hecke-stable group $G_r/S$ at each $\ell$-power level, together with compatible transition maps, and verifies the hypotheses of Theorem 12.1. Then the following conclusions pass level by level:

- every generic Eisenstein stable flag closes to an admissible integral flag;
- constant and multiplicative lengths are detected at $\mathbf Z_\ell$;
- Cartier duality reverses the flag and exchanges the two lengths;
- a global Shimura-type subgroup supplies the multiplicative side of a separation;
- a cuspidal-type quotient supplies the constant side;
- every atomic mixed extension is governed by the Kummer calculation of Chapter 7;
- at $2$, each endpoint requires an integral label independent of its generic character.

Taking an inverse limit is not needed to prove any finite-level assertion above. Construction of a completed Hecke piece, proof that all transition maps have the required flat kernels, and control of a resulting $\ell$-divisible group belong to the next stage. The present theorem supplies the finite devissage that stage may invoke.

## 13. Exceptional primes and boundary cases

### 13.1 The level prime cannot be an Eisenstein prime

If $\ell\mid n_N$, then $\ell\mid N-1$, so $\ell<N$ and $\ell\ne N$. This elementary inequality guarantees that the residue-characteristic prime where finite flatness is delicate remains on the base $S$, while the bad-reduction level prime has been removed.

The distinction also controls Kummer theory. The element $N$ is a unit on $S$, so $T^\ell=N$ is a $\mu_\ell$-torsor there. At the omitted prime $N$ it would be ramified along the closed fiber and would no longer be a torsor under $\mu_\ell$. The single removed prime is exactly the source of the one-dimensional odd Kummer group.

### 13.2 Levels with trivial Eisenstein index

For $N=2,3$, Book 133 proves that the Jacobian, cuspidal group, and component group under discussion are trivial, and $n_N=1$. For

$$
N=5,7,13,
$$

one also has $n_N=1$. There is then no Eisenstein prime $\ell$ and no nonzero primary piece (12.4). All admissibility statements applied to the selected Eisenstein torsion are vacuous.

The first nontrivial examples include

$$
n_{11}=5,\qquad n_{17}=4,\qquad n_{19}=3,\qquad n_{37}=3,\qquad n_{73}=6.
\tag{13.1}
$$

They display three different regimes: an ordinary odd prime $5$, a purely two-primary group, and simultaneous primes $2$ and $3$.

### 13.3 The prime three

The prime $3$ is exceptional in formulas involving the denominator $12$ and the elliptic point of order three on the modular curve. Those exceptional automorphisms have already been incorporated into the exact integer $n_N$ by Book 133. Once $3\mid n_N$ is fixed, the local finite-flat theory at $3$ is not at the low-ramification boundary:

$$
e(\mathbf Z_3)=1<3-1.
$$

Thus Proposition 4.1, global endpoint recognition, and the cyclic Kummer calculation all apply without change. The two generic characters $1$ and $\overline\chi_3$ are distinct on inertia at $3$.

One must still avoid replacing $n_N$ by $(N-1)/12$ when that rational number is not integral. The numerator normalization is responsible for the correct $3$-adic length. The group-scheme theory begins only after that length has been computed correctly.

### 13.4 The full two-primary boundary

For odd prime $N$, write $d=v_2(N-1)$. Since $v_2(12)=2$,

$$
v_2(n_N)=\max(d-2,0).
\tag{13.2}
$$

Thus $2$ is an Eisenstein prime exactly when $N\equiv1\pmod 8$. The two-primary cuspidal and Shimura groups have order $2^{d-2}$, hence atomic length $d-2$.

Four changes occur at once.

1. The generic characters $1$ and $\overline\chi_2$ coincide.
2. Height-one low-ramification rigidity is unavailable because $1<2-1$ is false.
3. The two integral endpoints over $\mathbf Z_2$ remain distinct: one is étale and one connected multiplicative.
4. The atomic extension group has the three-step exact description (7.11), involving $[-1]$, $[N]$, and a carry class.

These facts dictate the correct dyadic protocol. Begin with a fixed finite-flat ambient group. Close each stable generic line inside the successive quotient. Determine its endpoint by special-fiber connectedness or Cartier duality, not by its generic character. For every extension of a constant atom by a multiplicative atom, first record its two root-torsor coordinates in the quotient of (7.11), and then record its position in the two-element fiber governed by the carry subspace. Turning those data into three coordinates requires a noncanonical splitting of (7.11). Only after these checks may one use the same filtration and rank arguments as at odd primes.

**Theorem 13.1 (dyadic admissibility and integral labels).** Let $G/S$ be a finite-flat $2$-primary group in a fixed ambient torsion group. If its generic module has a stable flag with one-dimensional factors, then closing that flag makes $G$ Eisenstein-admissible. Every successive closure is $\underline{\mathbf Z/2}$ or $\mu_2$; its type is constant exactly when its special fiber at $2$ is étale and multiplicative exactly when that fiber is connected. The numbers of the two factors are intrinsic and equal the étale and connected lengths over $\mathbf Z_2$.

**Proof.** Every one-dimensional $\mathbf F_2$-factor is generically trivial. Proposition 2.2 closes the flag, and the dyadic part of Proposition 11.1 identifies every successive order-two closure as one of the two standard endpoints. This is an admissible filtration. Proposition 5.2 and the connected–étale sequence prove the intrinsic rank description. $\square$

The theorem is a generic criterion for admissibility only because the base at $2$ is the unramified ring $\mathbf Z_2$ and order-two groups have no nontrivial automorphism twists. It is not a generic criterion for the **labels** of the factors: connectedness of the actual integral closures remains indispensable.

### 13.5 A failure ledger

The following implications are unsafe without the added hypothesis in the right column.

| Tempting implication                                                     | Obstruction                                  | Required repair                                                |
| ------------------------------------------------------------------------ | -------------------------------------------- | -------------------------------------------------------------- |
| generic subgroup $\Rightarrow$ abstract canonical model                  | different Hopf lattices                      | close inside a fixed finite-flat ambient group                 |
| generic map $\Rightarrow$ integral map                                   | lattice incompatibility                      | use low-height rigidity or prove extension                     |
| scheme-theoretic kernel $\Rightarrow$ finite flat                        | vertical torsion                             | prove flatness or use an admissible kernel                     |
| equal generic image $\Rightarrow$ faithfully flat image                  | coimage–image failure                        | verify the torsor factorization                                |
| semisimplification $1\oplus\overline\chi_\ell$ $\Rightarrow$ stable line | semisimplification forgets reducibility data | supply reducibility or a geometric subgroup                    |
| all constituents Eisenstein $\Rightarrow$ global separation              | local connected part need not globalize      | construct a multiplicative subgroup and constant-type quotient |
| factors killed by $x$ $\Rightarrow$ middle killed by $x$                 | $x$ can map quotient to subgroup             | prove the cross Hom group vanishes                             |
| extension list can be reordered                                          | the category is not abelian                  | construct the new subgroup or prove a vanishing theorem        |
| $\ell=2$ generic line labels its endpoint                                | $1=\overline\chi_2$                          | inspect connectedness or duality                               |
| odd Kummer calculation applies at $2$                                    | sign and carry survive                       | use the exact sequence (7.11)                                  |
| constant type $\Rightarrow$ constant                                     | monodromy around $N$                         | distinguish filtered étale objects from constant groups        |
| multiplicative semisimplification $\Rightarrow$ multiplicative model     | integral type is extra                       | prove Cartier-dual étaleness                                   |

This ledger is not merely defensive. Each repair identifies the positive theorem needed to continue an Eisenstein argument without loss of integral information.

## 14. The admissible-group-scheme package

### 14.1 Main theorem

We gather the results in a form suitable for later use.

**Theorem 14.1 (Mazur–Raynaud admissible package).** Let $N$ be prime,

$$
S=\operatorname{Spec}\mathbf Z[1/N],\qquad
n_N=\frac{N-1}{\gcd(N-1,12)},
$$

and let $\ell\mid n_N$ be prime.

1. The category of finite-flat commutative $\ell$-primary $S$-groups carries the exact structure of faithfully flat short exact sequences. Schematic closure of a generic subgroup inside a fixed object is finite flat, unique, compatible with localization, and has a represented finite-flat quotient.

2. The Eisenstein atoms are

   $$
   \underline{\mathbf Z/\ell\mathbf Z},\qquad\mu_\ell,
   $$

   with generic characters $1$ and $\overline\chi_\ell$, and Cartier duality exchanges them.

3. An Eisenstein-admissible object is one filtered by these atoms. Its constant and multiplicative multiplicities are intrinsic and are measured by the étale and connected ranks over $\mathbf Z_\ell$. It need not split, be killed by $\ell$, or possess a canonical global separation.

4. For odd $\ell$, every stable generic flag with factors $1$ and $\overline\chi_\ell$ in a fixed finite-flat ambient group closes to an admissible integral flag. This follows from schematic closure and height-one low-ramification rigidity over $\mathbf Z_\ell$.

5. At $\ell=2$, the two generic characters coincide. Over $S$, every order-two closure is nevertheless one of the constant and multiplicative endpoints, so every stable generic flag closes to an admissible flag. The actual integral closure, through its connectedness at $2$, supplies the label; generic representation theory cannot recover the two multiplicities by itself.

6. A separated admissible object is an extension

   $$
   0\to M\to G\to C\to0
   $$

   of constant type by split multiplicative type. Locally at $\ell$ this is the connected–étale sequence. Globally its existence requires a constructed subgroup, such as a Shimura-type line, or another explicit separation argument.

7. For odd $\ell$,

   $$
   \operatorname{Ext}^1_S
   (\underline{\mathbf Z/\ell\mathbf Z},\mu_\ell)
   \simeq\langle[N]\rangle\simeq\mathbf F_\ell.
   $$

   With fixed endpoint generators, the class $j$ has fiber equation $T^\ell=N^j$ and is split exactly for $j=0$.

8. At $\ell=2$ there is an exact sequence

   $$
   0\to\mu_2(S)
   \to\operatorname{Ext}^1_S
   (\underline{\mathbf Z/2\mathbf Z},\mu_2)
   \to S^\times/S^{\times2}\to0,
   $$

   whose outer terms have dimensions $1$ and $2$ over $\mathbf F_2$. It records a canonical carry subspace and a torsor quotient generated by the sign and level-unit classes.

   The middle group is killed by $2$, so it is abstractly $\mathbf F_2^3$. The exact sequence canonically distinguishes the carry subspace from the two-dimensional torsor quotient but does not canonically split them into three coordinates.

9. Book 133 supplies generic cyclic groups

   $$
   C_{N,\ell,\mathbf Q}\simeq\underline{\mathbf Z/\ell^e\mathbf Z}_{\mathbf Q},
   \qquad
   \Sigma_{N,\ell,\mathbf Q}\simeq\mu_{\ell^e,\mathbf Q},
   \qquad e=v_\ell(n_N),
   $$

   as the constant and multiplicative prime-level Eisenstein constituents. Their closures are filtered by the standard atoms at every $\ell$. At $2$, the named claim that the cuspidal closure is constant and the Shimura closure multiplicative still requires the dyadic connectedness or duality check. Any selected finite-flat quotient whose generic module has the required stable Eisenstein flag is admissible by item 4 or item 5. A height-two separated layer is controlled by item 7 or item 8.

**Proof.** Item 1 is the exact structure supplied by Book 28 together with Theorem 2.1. Item 2 is exact Cartier duality. Items 3–5 are Proposition 5.2, Theorem 12.1, and Theorem 13.1. Item 6 is Theorem 9.1 together with its stated global boundary. Items 7–8 are Theorem 7.1 and (7.11)–(7.12). Item 9 combines the prime-level package of Book 133 with Theorems 12.1 and 12.2. $\square$

### 14.2 Dependency closure

Every imported theorem has been used within its established hypotheses.

Book 28 supplies the exact category of finite-flat commutative group schemes, represented faithfully flat quotients, rank multiplication, finite étaleness when the order is invertible, and schematic closure over DVRs and Dedekind domains. We apply the Dedekind closure theorem to $\mathbf Z[1/N]$, and we never treat an arbitrary nonflat kernel as admissible.

Book 34 supplies exact Cartier duality, the exchange of constant and diagonalizable groups, annihilators, closure–annihilator compatibility, and the Tate-twisted generic module dual. Every use occurs in an admissible finite-flat sequence or for a finite-flat subgroup.

Book 29 supplies the fppf Kummer sequence in every characteristic, the calculation

$$
0\to S^\times/S^{\times n}\to H^1(S,\mu_n)
\to\operatorname{Pic}(S)[n]\to0,
$$

and the interpretation of boundary classes as torsor fibers. Here $S$ is affine with trivial Picard group, so the unit calculation applies exactly. The torsor–carry sequence is proved in Chapter 6 from the same low-degree cohomological formalism.

Book 51 supplies the henselian connected–étale sequence, the maximal multiplicative subgroup, the three-step local filtration, the Oort–Tate endpoint classification, low-ramification rigidity when $e<\ell-1$, prime-order closure filtrations, and the explicit dyadic boundary. We use rigidity over $\mathbf Z_\ell$ only for odd $\ell$, where $e=1<\ell-1$, and explicitly withhold it at $2$.

Book 133 supplies the exact integer $n_N$, the generic constant cuspidal group, the generic diagonalizable cyclic Shimura kernel, their Hecke annihilation, and the trivial exceptional levels. We pass to integral closures using the fixed abelian ambient model and prove only the atomic identifications justified by rank-one rigidity. We use no theorem about the intersection of the two closures.

Ordinary background used directly consists of projective lattices over a Dedekind domain, the unit group and Picard group of $\mathbf Z[1/N]$, and elementary homological algebra for the constant sheaf resolution. The last is proved explicitly in Theorem 6.1 in the precise form needed.

### 14.3 Exact scope boundaries

This book proves a finite-level group-scheme theorem. It does not prove complete multiplicity one for the Eisenstein maximal ideal, construct a completed Hecke algebra piece, establish flatness of every Hecke kernel, or build an Eisenstein $\ell$-divisible group. Those tasks require additional Hecke and abelian-scheme input.

It does not determine the full rational torsion subgroup of $J_0(N)$, calculate the complete intersection of cuspidal and Shimura subgroups, or classify every finite-flat group over $\mathbf Z[1/N]$. The only extension group completely calculated is the mixed atomic group with multiplicative kernel and constant quotient. Opposite-orientation, same-type, and higher-power extensions remain outside that calculation unless reduced to it by an actual admissible filtration.

It also does not infer reducibility from a trace congruence, a global separation from local connectedness, or an integral model from a generic representation at the dyadic prime. These are precisely the extra assertions later geometry must verify for its selected quotient.

### 14.4 Conclusion

The admissible category isolates the integral content of the Eisenstein pair. The generic characters

$$
1\quad\text{and}\quad\overline\chi_\ell
$$

become the finite-flat atoms

$$
\underline{\mathbf Z/\ell\mathbf Z}
\quad\text{and}\quad
\mu_\ell.
$$

Schematic closure carries a genuine stable generic flag into a unique flag inside a fixed integral torsion group. Connected–étale structure records how many atoms point in each direction. Cartier duality exchanges them and controls annihilators. A global Shimura line and cuspidal quotient, when present, orient the filtration into a Mazur–Raynaud separation.

The remaining mixed extension is arithmetic. For odd $\ell$, the punctured arithmetic line has one Kummer direction:

$$
H^1(\mathbf Z[1/N],\mu_\ell)
=\langle[N]\rangle.
$$

Thus every atomic separated layer is measured by the root torsor $T^\ell=N^j$. At two, the coincidence of generic characters, the sign unit, and the carry class force a larger integral record. That boundary is not an imperfection of the theory; it is the exact information forgotten by generic points.

The resulting package is deliberately finite, exact, and conditional only where geometry must intervene. It controls the constant and multiplicative constituents required by the selected prime-level Eisenstein quotient without asserting full multiplicity one or unrelated rational torsion. In that form it is strong enough for completed Hecke pieces and Eisenstein descent, while preserving every flatness, orientation, and exceptional-prime hypothesis on which those later arguments depend.
