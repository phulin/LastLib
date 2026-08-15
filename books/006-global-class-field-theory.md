# Global Class Field Theory

## Contents

1. [The global reciprocity problem](#1-the-global-reciprocity-problem)
   - [One Galois action seen at every place](#11-one-galois-action-seen-at-every-place)
   - [Conventions at finite and infinite places](#12-conventions-at-finite-and-infinite-places)
   - [Four kinds of norm assertion](#13-four-kinds-of-norm-assertion)
   - [The architecture of the proof](#14-the-architecture-of-the-proof)
2. [Local symbols and the global Artin map](#2-local-symbols-and-the-global-artin-map)
   - [Decomposition groups from a chosen place](#21-decomposition-groups-from-a-chosen-place)
   - [Unramified and ramified Artin symbols](#22-unramified-and-ramified-artin-symbols)
   - [Multiplying the local maps](#23-multiplying-the-local-maps)
   - [Why principal ideles act trivially](#24-why-principal-ideles-act-trivially)
3. [Norms of ideles and classes](#3-norms-of-ideles-and-classes)
   - [Constructing the global norm](#31-constructing-the-global-norm)
   - [Norm groups are open and have finite index](#32-norm-groups-are-open-and-have-finite-index)
   - [Local norm tests and the global kernel](#33-local-norm-tests-and-the-global-kernel)
   - [An index preview](#34-an-index-preview)
4. [The global class formation](#4-the-global-class-formation)
   - [Why cohomology is the right accounting system](#41-why-cohomology-is-the-right-accounting-system)
   - [The Brauer--idele exact sequence](#42-the-brauer--idele-exact-sequence)
   - [Construction of the fundamental class](#43-construction-of-the-fundamental-class)
   - [The two class-formation lemmas](#44-the-two-class-formation-lemmas)
   - [Restriction, corestriction, and invariant normalizations](#45-restriction-corestriction-and-invariant-normalizations)
   - [Cup products and the local trace](#46-cup-products-and-the-local-trace)
   - [The global trace and the duality pairing](#47-the-global-trace-and-the-duality-pairing)
   - [Norms, induction, and Shapiro compatibility](#48-norms-induction-and-shapiro-compatibility)
5. [Finite global reciprocity](#5-finite-global-reciprocity)
   - [The reciprocity isomorphism](#51-the-reciprocity-isomorphism)
   - [Frobenius, decomposition, and inertia](#52-frobenius-decomposition-and-inertia)
   - [Compatibility in quotients and towers](#53-compatibility-in-quotients-and-towers)
   - [A first explicit calculation over the rationals](#54-a-first-explicit-calculation-over-the-rationals)
6. [The global existence theorem](#6-the-global-existence-theorem)
   - [Why reciprocity does not yet give existence](#61-why-reciprocity-does-not-yet-give-existence)
   - [The finite local--global character sequence](#62-the-finite-local--global-character-sequence)
   - [Constructing the global character](#63-constructing-the-global-character)
   - [Classification by open subgroups](#64-classification-by-open-subgroups)
7. [Moduli and ray class fields](#7-moduli-and-ray-class-fields)
   - [Why a modulus has a finite and an infinite part](#71-why-a-modulus-has-a-finite-and-an-infinite-part)
   - [Ideal-theoretic ray classes](#72-ideal-theoretic-ray-classes)
   - [Conductors of extensions and characters](#73-conductors-of-extensions-and-characters)
   - [Existence and maximality of ray class fields](#74-existence-and-maximality-of-ray-class-fields)
   - [The ray exact sequence and the role of units](#75-the-ray-exact-sequence-and-the-role-of-units)
   - [The conductor--discriminant formula](#76-the-conductor--discriminant-formula)
8. [Splitting laws and the Hilbert class field](#8-splitting-laws-and-the-hilbert-class-field)
   - [Congruence becomes Frobenius](#81-congruence-becomes-frobenius)
   - [The Hilbert class field](#82-the-hilbert-class-field)
   - [Imaginary and real quadratic examples](#83-imaginary-and-real-quadratic-examples)
   - [Cyclotomic fields as ray class fields](#84-cyclotomic-fields-as-ray-class-fields)
   - [Quadratic reciprocity as a product formula](#85-quadratic-reciprocity-as-a-product-formula)
9. [Norm principles and their limits](#9-norm-principles-and-their-limits)
   - [The knot between local and global norms](#91-the-knot-between-local-and-global-norms)
   - [The Hasse norm theorem for cyclic extensions](#92-the-hasse-norm-theorem-for-cyclic-extensions)
   - [Why cyclicity cannot be dropped](#93-why-cyclicity-cannot-be-dropped)
   - [Norm limitation, correctly stated](#94-norm-limitation-correctly-stated)
10. [Infinite reciprocity](#10-infinite-reciprocity)
    - [Passing over all finite abelian extensions](#101-passing-over-all-finite-abelian-extensions)
    - [The connected component of the idele class group](#102-the-connected-component-of-the-idele-class-group)
    - [Infinite decomposition groups](#103-infinite-decomposition-groups)
    - [Kronecker--Weber revisited](#104-kronecker--weber-revisited)
11. [Hecke characters](#11-hecke-characters)
    - [Adelic characters and their local factors](#111-adelic-characters-and-their-local-factors)
    - [Finite-order characters and Galois characters](#112-finite-order-characters-and-galois-characters)
    - [Quasicharacters and the module direction](#113-quasicharacters-and-the-module-direction)
    - [Algebraic infinity types](#114-algebraic-infinity-types)
    - [The ell-adic avatar](#115-the-ell-adic-avatar)
    - [Norms, restriction, and conjugation of characters](#116-norms-restriction-and-conjugation-of-characters)
    - [Dirichlet and CM character models](#117-dirichlet-and-cm-character-models)
    - [The quadratic induction interface](#118-the-quadratic-induction-interface)
    - [Induction through a general finite extension](#119-induction-through-a-general-finite-extension)
12. [The global reciprocity dictionary](#12-the-global-reciprocity-dictionary)
    - [Fields, subgroups, and quotients](#121-fields-subgroups-and-quotients)
    - [Local multiplicative data and global Galois data](#122-local-multiplicative-data-and-global-galois-data)
    - [Moduli, ramification, and splitting](#123-moduli-ramification-and-splitting)
    - [Norms without ambiguity](#124-norms-without-ambiguity)
    - [Characters at a glance](#125-characters-at-a-glance)
    - [Conclusion](#126-conclusion)

## 1. The global reciprocity problem

### 1.1 One Galois action seen at every place

Let $K$ be a number field, let $\mathbf A_K$ be its adele ring, let $\mathbf I_K=\mathbf A_K^\times$ be its idele group, and put

$$
C_K=\mathbf I_K/K^\times.
$$

We recall the topology that will matter throughout. The multiplicative restricted product is

$$
\mathbf I_K=
\prod_v'(K_v^\times,\mathcal O_v^\times),
$$

with restriction only at finite places. A basic open subgroup allows arbitrary prescribed open subgroups at finitely many places and uses $\mathcal O_v^\times$ at every other finite place. The diagonal $K^\times$ is discrete and closed, so $C_K$ is locally compact and Hausdorff. The idele module

$$
|x|_{\mathbf A_K}=\prod_v|x_v|_v
$$

is trivial on $K^\times$ by the product formula. Its kernel $C_K^1$ in the class group is compact, while $C_K/C_K^1\cong\mathbf R_{>0}$. These facts explain both why finite quotients of $C_K$ are manageable and why $C_K$ itself is not compact.

The preceding adelic theory showed that $C_K$ simultaneously remembers fractional ideals, local units, real signs, and archimedean size. Local class field theory showed that $K_v^\times$ controls the finite abelian extensions of each completion $K_v$. The global problem is to determine which collections of local abelian actions come from one extension of $K$.

There must be a compatibility. A global element $a\in K^\times$ gives an element of every $K_v^\times$, but it has no independent global Galois effect: changing local data by the diagonal idele $(a)_v$ should change nothing. Thus the expected source is not $\mathbf I_K$ but $C_K$. Global reciprocity will construct a continuous map

$$
\operatorname{Art}_K:C_K\longrightarrow G_K^{\mathrm{ab}},
$$

where $G_K=\operatorname{Gal}(K^s/K)$. At finite level, for every finite abelian extension $L/K$, it will give an isomorphism

$$
C_K/N_{L/K}C_L\xrightarrow{\sim}\operatorname{Gal}(L/K).
$$

This statement contains three assertions that must not be conflated. The product of the local maps is trivial on $K^\times$; its kernel at level $L$ is exactly an idelic norm group; and every open finite-index subgroup of $C_K$ occurs as such a norm group. Reciprocity, the norm theorem, and existence are logically distinct parts of the theory.

### 1.2 Conventions at finite and infinite places

At every nonarchimedean place $v$, local reciprocity is normalized arithmetically:

$$
\operatorname{rec}_{K_v}(\pi_v)|_{K_v^{\mathrm{nr}}}
=\operatorname{Frob}_{v}^{\mathrm{arith}},
\qquad x\longmapsto x^{q_v}
$$

on residue fields. Consequently, if $L/K$ is unramified at $v$ and $w\mid v$, the global Artin symbol of a prime uniformizer will be arithmetic Frobenius. Authors using geometric Frobenius obtain the inverse of every Artin map in this book. Mixing the two conventions is the most common source of erroneous inverses.

At a complex place, $K_v=\mathbf C$ has no nontrivial finite extension and its local reciprocity map is trivial. At a real place, local reciprocity is

$$
\mathbf R^\times/\mathbf R_{>0}\xrightarrow{\sim}
\operatorname{Gal}(\mathbf C/\mathbf R),
$$

with a negative number mapping to complex conjugation. Thus the connected component $\mathbf R_{>0}$ is always killed. Infinite ramification means precisely that a real place becomes complex; complex places never ramify. A modulus may include a real place, but never needs a complex place.

At a finite place we use the filtration

$$
U_v^0=\mathcal O_v^\times,
\qquad
U_v^n=1+\mathfrak p_v^n\quad(n\geq1).
$$

We use $N_{L/K}\mathbf I_L$ for the image of the componentwise idele norm and $N_{L/K}C_L$ for its image in $C_K$. The latter is

$$
N_{L/K}C_L=K^\times N_{L/K}\mathbf I_L/K^\times.
$$

It is generally larger than the image of $N_{L/K}\mathbf I_L$ viewed inside $\mathbf I_K$, because multiplication by a principal idele is permitted after passage to classes.

### 1.3 Four kinds of norm assertion

The notation $N$ hides several genuinely different questions. For $a\in K^\times$ and a finite extension $L/K$, consider:

1. **element norm:** $a=N_{L/K}(y)$ for some $y\in L^\times$;
2. **local element norm:** $a$ is a norm from the étale $K_v$-algebra $L\otimes_KK_v=\prod_{w\mid v}L_w$ for every $v$;
3. **idele norm:** the principal idele of $a$ belongs to $N_{L/K}\mathbf I_L$;
4. **class norm:** a class $c\in C_K$ belongs to $N_{L/K}C_L$.

For a principal idele, conditions 2 and 3 are equivalent: collect the local preimages into an idele; integrality of suitable preimages holds at almost every unramified place. Condition 1 implies them, but the converse is the Hasse norm principle and fails for general extensions. For cyclic extensions it holds; for noncyclic biquadratic extensions it can fail. In a Galois extension all factors above $v$ have the same norm subgroup, but for a non-Galois extension one must retain the product-algebra formulation. Condition 4 is different again, since it allows multiplication by an arbitrary element of $K^\times$.

These distinctions prevent two overclaims. Global reciprocity identifies the kernel on the **idele class group** with a class norm group; it does not by itself assert that every locally normic element is a field norm. Nor does norm limitation for Galois extensions identify element norm groups in general.

### 1.4 The architecture of the proof

The proof has a local layer, a global obstruction layer, and an existence layer. At the local layer, each $K_v^\times$ acts through local reciprocity. At the global layer, the Brauer invariant sequence

$$
0\longrightarrow\operatorname{Br}(K)
\longrightarrow\bigoplus_v\operatorname{Br}(K_v)
\xrightarrow{\sum_v\operatorname{inv}_v}\mathbf Q/\mathbf Z
\longrightarrow0
$$

forces the product of the local actions of a principal element to be one. The sum, rather than any individual invariant, is the global mechanism.

For a finite Galois extension, passing from the local invariant sequence to a
fundamental class in $H^2(G,C_L)$ requires Tate's canonical $S$-unit sequence.
That sequence is not constructed in the preceding books or in this one; Section
4.3 isolates its exact content as Hypothesis TS. Conditional on TS, capping with
the resulting class identifies $G^{\mathrm{ab}}$ with $C_K/N C_L$. Finally, the
existence argument proves that the norm subgroups obtained this way exhaust all
open finite-index subgroups of $C_K$. This last step also uses the finite
local--global duality sequence for the Cartier-dual pair $\mathbf Z/n\mathbf Z$
and $\mu_n$; it cannot be replaced by merely counting extensions already known
to exist.

There is a second, independent global-cohomological boundary. Books 1--5 supply
local reciprocity, local Brauer invariants, Kummer theory, ideles, units,
divisors, and ideal classes, but they do not construct compactly supported
global Galois cohomology or prove its perfect duality theorem. Section 4.2
therefore isolates the exact finite Artin--Verdier input as **Hypothesis FD**.
A result marked **[FD]** is conditional on that input; a label such as
**[FD,TC,TS]** records the other independent inputs as well. Hypothesis FD is
not obtained from the later Poitou--Tate volume, which would violate the reading
order. The labels below keep the unresolved input visible instead of disguising
a global duality theorem as an elementary units-and-divisors count.

## 2. Local symbols and the global Artin map

### 2.1 Decomposition groups from a chosen place

Let $L/K$ be finite Galois, with group $G$, and let $v$ be a place of $K$. Choose a place $w$ of $L$ above $v$. The decomposition group

$$
D_w=\{\sigma\in G:\sigma w=w\}
$$

identifies canonically with $\operatorname{Gal}(L_w/K_v)$. At a finite place its inertia subgroup $I_w$ is the kernel of the action on residue fields, and there is an exact sequence

$$
1\longrightarrow I_w\longrightarrow D_w
\longrightarrow\operatorname{Gal}(k_w/k_v)\longrightarrow1.
$$

If $L/K$ is abelian, $D_w$ and $I_w$ do not depend on the choice of $w$: a second choice is $\tau w$, and its decomposition group is $\tau D_w\tau^{-1}=D_w$. This is one reason the global abelian theory has canonical local symbols without repeated choices.

Local reciprocity for $L_w/K_v$ gives

$$
K_v^\times\longrightarrow D_w^{\mathrm{ab}}.
$$

When $L/K$ is abelian, $D_w$ already is abelian and inclusion $D_w\hookrightarrow G$ defines the **local Artin map at $v$**

$$
\operatorname{Art}_{L/K,v}:K_v^\times\longrightarrow G.
$$

Its kernel is $N_{L_w/K_v}(L_w^\times)$, its image is $D_w$, and the image of $\mathcal O_v^\times$ is $I_w$ at a finite place.

If $L/K$ is Galois but not abelian, local reciprocity still maps to $D_w^{\mathrm{ab}}$, and inclusion induces $D_w^{\mathrm{ab}}\to G^{\mathrm{ab}}$. Changing $w$ conjugates the construction, which has no effect in $G^{\mathrm{ab}}$. Thus there is a canonical abelianized local map in the nonabelian Galois case as well. This is the version used in norm limitation.

### 2.2 Unramified and ramified Artin symbols

Assume throughout this subsection that $L/K$ is abelian. Suppose $v$ is finite and unramified in $L$. Then $I_w=1$, and the local norm is surjective on units. Hence $\operatorname{Art}_{L/K,v}(x)$ depends only on $\operatorname{ord}_v(x)$:

$$
\operatorname{Art}_{L/K,v}(x)
=\operatorname{Frob}_v^{\operatorname{ord}_v(x)}.
$$

Here $\operatorname{Frob}_v$ is the unique element of $D_w$ acting by $z\mapsto z^{q_v}$ on $k_w$. If $\mathfrak p_v$ denotes the prime ideal, one also writes

$$
\left(\frac{L/K}{\mathfrak p_v}\right)=\operatorname{Frob}_v.
$$

At a ramified place there is no single canonical element attached to the prime ideal: the residue Frobenius determines only a coset in $D_w/I_w$. A choice of uniformizer yields a lift through local reciprocity, but changing the uniformizer by a unit multiplies that lift by inertia. The full local symbol $K_v^\times\to D_w$, not an alleged “Frobenius at a ramified prime,” is the canonical object.

For example, in a quadratic extension and at a finite unramified prime, the symbol is $1$ exactly when the prime splits, and is the nontrivial involution exactly when it remains prime. At a ramified prime the uniformizer and units together describe the decomposition group, while the ideal symbol is deliberately left undefined.

### 2.3 Multiplying the local maps

Continue with $L/K$ finite abelian. For $x=(x_v)\in\mathbf I_K$, define

$$
\operatorname{Art}_{L/K}(x)
=\prod_v\operatorname{Art}_{L/K,v}(x_v).
$$

This product is finite. Only finitely many places ramify; outside those and outside the finite support of the valuation vector of $x$, the extension is unramified and $x_v$ is a unit, so the local factor is $1$. Since $G$ is abelian, the order of the factors does not matter.

The map is continuous. Its restriction to each local factor is continuous, and its kernel contains a standard open subgroup: take local norm groups at the finitely many ramified places and local units elsewhere. Surjectivity is not assumed at this stage. It will follow in Theorem 5.1 from the global class-formation calculation, without using a prime-distribution theorem.

If $v$ splits completely, then $D_w=1$, so the entire factor $K_v^\times$ is killed. Conversely, for a Galois extension, triviality of $D_w$ is equivalent to complete splitting. This turns splitting into a kernel condition.

### 2.4 Why principal ideles act trivially

The decisive global statement is the **product formula for local norm-residue symbols**:

**Theorem 2.1 [FD].** If $L/K$ is finite abelian and $a\in K^\times$, then

$$
\prod_v\operatorname{Art}_{L/K,v}(a)=1.
$$

**Proof strategy.** Reduce to cyclic quotients and express each local symbol by a cyclic algebra. A principal element gives localizations of one global Brauer class. The sum of its local invariants is zero, and a character of the cyclic Galois group reads that sum as the product of symbols.

**Proof.** It is enough to prove that every character $\chi:G\to\mathbf Q/\mathbf Z$ vanishes on the displayed product. Let $E$ be the fixed field of $\ker\chi$; then $E/K$ is cyclic, say of degree $n$, and $\chi$ identifies its Galois group with a subgroup of $\frac1n\mathbf Z/\mathbf Z$. Choose a generator $\sigma$ compatible with this identification.

Form the cyclic algebra $A=(E/K,\sigma,a)$. Its localization at $v$ is the product of the cyclic algebras attached to the completions $E_w/K_v$. Local cyclic reciprocity, with the arithmetic normalization, gives

$$
\operatorname{inv}_v(A_v)
=\chi\bigl(\operatorname{Art}_{E/K,v}(a)\bigr).
$$

At split factors both sides are zero. The degree-two localization row in FD gives

$$
0=\sum_v\operatorname{inv}_v(A_v)
=\chi\left(\prod_v\operatorname{Art}_{E/K,v}(a)\right).
$$

The local maps for $E/K$ are the quotients of those for $L/K$. Thus every character of $G$ kills the product. Characters separate points of a finite abelian group, so the product is $1$. $\square$

Therefore $\operatorname{Art}_{L/K}$ factors uniquely through $C_K$. This is the global explanation for the quotient by principal ideles. It is not a formal consequence of the ordinary product formula $\prod_v|a|_v=1$, though both statements share the same local-to-global shape.

## 3. Norms of ideles and classes

### 3.1 Constructing the global norm

Let $L/K$ be finite. Under the decomposition

$$
L\otimes_KK_v\cong\prod_{w\mid v}L_w,
$$

define the $v$-component of the idele norm by

$$
(N_{L/K}y)_v=\prod_{w\mid v}N_{L_w/K_v}(y_w).
$$

At almost every finite $v$, the extension is unramified, every $y_w$ is a unit, and each local norm is a unit. Thus these components form an idele. The map $N_{L/K}:\mathbf I_L\to\mathbf I_K$ is continuous and is transitive in towers.

For $b\in L^\times$, the norm of its principal idele is the principal idele of the field norm $N_{L/K}b$. Hence the norm descends to a continuous homomorphism $C_L\to C_K$. On the module maps it satisfies

$$
|N_{L/K}y|_{\mathbf A_K}=|y|_{\mathbf A_L},
$$

with the normalized absolute values used in the adelic volume. This identity is particularly useful for separating the noncompact real direction from the compact norm-one class group.

### 3.2 Norm groups are open and have finite index

The local norm group is open at every place. At almost every unramified finite place, the local
norm maps the integral-unit subgroup onto the base integral-unit subgroup. Consequently $N_{L/K}\mathbf I_L$ contains a basic open subgroup of $\mathbf I_K$ and is open. Its image $N_{L/K}C_L$ is therefore open in $C_K$.

Finite index is subtler: openness alone does not imply finite index in a noncompact group. The norm map is surjective on the positive real module direction: at one archimedean coordinate its restriction is either a positive power map on $\mathbf R_{>0}$ or the map $z\mapsto |z|^2$, and both have image $\mathbf R_{>0}$. Combined with the module identity, this shows that every class modulo $N_{L/K}C_L$ has a representative in the compact group $C_K^1$. The quotient is therefore a quotient of $C_K^1$ by an open subgroup. An open subgroup of a compact group has finite index. Hence

$$
[C_K:N_{L/K}C_L]<\infty.
$$

The same argument also shows that $N_{L/K}C_L$ is closed. This topological fact is indispensable when passing from finite reciprocity to profinite completion.

One must not replace $N C_L$ by $N\mathbf I_L$ in this index. The quotient $\mathbf I_K/N\mathbf I_L$ retains a diagonal obstruction and generally is not the finite Galois group. Passage to $C_K$ is essential.

### 3.3 Local norm tests and the global kernel

Compatibility of local reciprocity with norms gives

$$
\operatorname{Art}_{L/K}(N_{L/K}y)=1
\qquad(y\in\mathbf I_L)
$$

when $L/K$ is abelian. At a place $v$, the $v$-component is a product of local norms, each killed by local reciprocity; conjugate places cause no ambiguity because the target is abelian. Thus

$$
N_{L/K}C_L\subseteq\ker(\operatorname{Art}_{L/K}).
$$

Under [FD,TS,TC], the reverse inclusion is the global norm theorem and emerges
from the class-formation deduction. It is not obtained by checking one coordinate
at a time: an idele class in the kernel may have non-norm components whose
combined global obstruction cancels after multiplication by a principal idele.

For a principal element $a$, being an idele norm is coordinatewise local. By contrast, its class in $C_K$ is always the identity and hence always a class norm. This extreme example shows why a class-norm assertion cannot be read as an element-norm assertion.

### 3.4 An index preview

If $L/K$ is finite abelian, the main finite theorem will, under [FD,TS,TC],
prove the exact equality

$$
[C_K:N_{L/K}C_L]=[L:K]
$$

and identify the quotient with $\operatorname{Gal}(L/K)$. If $L/K$ is finite Galois but not abelian and $M=L^{[G,G]}$, the correct limitation statement is

$$
N_{L/K}C_L=N_{M/K}C_M,
\qquad
[C_K:N_{L/K}C_L]=[M:K].
$$

This is an idelic class statement. An analogous equality for the element norm groups $N_{L/K}L^\times$ and $N_{M/K}M^\times$ is false in general; the local book's norm limitation theorem concerns local fields, where the cohomological situation is different.

## 4. The global class formation

### 4.1 Why cohomology is the right accounting system

The local Artin maps already suggest the answer, but proving that their product has exactly the norm kernel requires a mechanism that can detect a global relation among local norm obstructions. Tate cohomology provides that mechanism. For a finite Galois extension $L/K$ with group $G$, the group

$$
\widehat H^0(G,C_L)=C_K/N_{L/K}C_L
$$

is the norm quotient we seek, while

$$
\widehat H^{-2}(G,\mathbf Z)=G^{\mathrm{ab}}.
$$

A class $u_{L/K}\in H^2(G,C_L)$ would connect them by cap product. Producing it
with the required behavior after restriction to every subgroup is precisely the
global input isolated as Hypothesis TS in Section 4.3.

### 4.2 The Brauer--idele exact sequence

We first isolate the global input.

**Theorem 4.1 (Brauer invariant sequence) [FD].** For a number field $F$, localization and local invariant maps form an exact sequence

$$
0\longrightarrow\operatorname{Br}(F)
\longrightarrow\bigoplus_u\operatorname{Br}(F_u)
\xrightarrow{\sum_u\operatorname{inv}_u}\mathbf Q/\mathbf Z
\longrightarrow0.
$$

Here $\operatorname{Br}(\mathbf C)=0$, $\operatorname{Br}(\mathbf R)=\frac12\mathbf Z/\mathbf Z$, and $\operatorname{Br}(F_u)\cong\mathbf Q/\mathbf Z$ at a finite place. Only finitely many localizations of a global class are nonzero.

The proof of this theorem and of the degree-one local--global sequence below requires a
finite global duality theorem which is not available in Books 1--5. We state the precise
input rather than replacing it by an order count on units and ideal classes. Such an order
count does not construct the relevant filtered complexes, prove compatibility of their
pairings, or justify descent through $F(\mu_n)/F$ when its degree is not invertible modulo
$n$.

We retain one independent elementary separation fact used later. A finite extension
$E/F$ which splits at all but finitely many completions is trivial. Indeed, Minkowski's
bound and the unit
lattice give

$$
A_F(X)=\#\{\mathfrak a\subseteq\mathcal O_F:N\mathfrak a\leq X\}
=\kappa_FX+O_F(X^{1-1/[F:\mathbf Q]})
$$

for some $\kappa_F>0$ (with a bounded error in degree one). Partial summation shows that
$\zeta_F(s)$ has a simple pole at $s=1$. If a degree-$d$ extension split at every
completion, then outside finitely many Euler factors one would have
$\zeta_E(s)=\zeta_F(s)^d$; the two sides have poles of orders one and $d$. Hence $d=1$.
This argument uses no global reciprocity or global duality.

Fix $n\geq1$ and a finite set $S$ containing the archimedean places and the places above
$n$. Let $G_{F,S}$ be the Galois group of the maximal extension of $F$ unramified outside
$S$, and put

$$
A_n=\mathbf Z/n\mathbf Z,
\qquad A_n^D=\mu_n.
$$

At a nonarchimedean place use the continuous local cochain complex. At a real place use the
complete Tate cochain complex, including its degree-zero norm quotient; this is the
modification that retains the $2$-primary sign term. At a complex place use the zero
modified complex, equivalently the Tate complex of the trivial decomposition group. With
these conventions set

$$
C_{S,c}^\bullet(A)=
\operatorname{Cone}\left(
C^\bullet(G_{F,S},A)\longrightarrow
\bigoplus_{u\in S}C^\bullet(F_u,A)
\right)[-1].
$$

**Hypothesis FD (finite Artin--Verdier duality for $A_n$ and $\mu_n$).** For every number
field $F$, every $n\geq1$, and every such $S$, the following data and assertions are
available.

1. Continuous cup products and the sum of the normalized local invariant maps define a
   trace

   $$
   \operatorname{tr}_{F,S}:H^3(C_{S,c}^\bullet(\mu_n))
   \xrightarrow{\sim}\tfrac1n\mathbf Z/\mathbf Z
   $$

   and pairings

   $$
   H^i(C_{S,c}^\bullet(A_n))\times
   H^{3-i}(G_{F,S},\mu_n)
   \longrightarrow\tfrac1n\mathbf Z/\mathbf Z
   \tag{4.1}
   $$

   for $0\leq i\leq3$, together with the pairings obtained by interchanging $A_n$ and
   $\mu_n$. More precisely, these pairings are induced by cochain maps

   $$
   C_{S,c}^\bullet(A_n)\longrightarrow
   \operatorname{Hom}\!\left(
   C^{3-\bullet}(G_{F,S},\mu_n),
   \tfrac1n\mathbf Z/\mathbf Z
   \right)
   $$

   and its swapped analogue, with the standard dual-complex differential, and FD asserts
   that these maps are quasi-isomorphisms in the displayed degree range.
2. All groups in these pairings are finite, and each pairing identifies either factor with
   the full Pontryagin dual of the other. The identification is compatible with the long
   exact localization sequences, connecting maps, cup products, and the transition maps as
   $S$ grows.
3. Restriction and corestriction are adjoint, including at real places. Descent through any
   finite extension, in particular through $F(\mu_n)/F$, is integral: it is induced on the
   relevant Hochschild--Serre total complexes and does not divide by the extension degree.
   Thus the assertion includes the case in which $[F(\mu_n):F]$ and $n$ have a common
   factor.
4. The degree-two localization row is

   $$
   0\longrightarrow H^2(F,\mu_n)
   \longrightarrow\bigoplus_u H^2(F_u,\mu_n)
   \longrightarrow
   \operatorname{Hom}(H^0(F,A_n),\mathbf Q/\mathbf Z)
   \longrightarrow0,
   $$

   where the middle arrow is the sum of local invariants. For a finite $S$, the
   degree-one row identifies the cokernel of

   $$
   H^1(F,A_n)\longrightarrow\prod_{u\in S}H^1(F_u,A_n)
   $$

   with the dual of the subgroup of $H^1(F,\mu_n)$ whose localization vanishes outside
   $S$, under the sum of local cup-product invariants.

This is the exact bounded finite Poitou--Tate, or finite Artin--Verdier, input used in this
book. It asserts no global Artin map, no global existence theorem, and no ray class field.
Conversely, the elementary exact sequence

$$
0\longrightarrow
\mathcal O_{F,S}^\times/\mathcal O_{F,S}^{\times n}
\longrightarrow H^1(G_{F,S},\mu_n)
\longrightarrow \operatorname{Cl}(\mathcal O_{F,S})[n]
\longrightarrow0
\tag{4.2}
$$

and its local analogues do not prove FD: they describe some groups but do not supply the
dual complexes, annihilator equalities, or integral Hochschild--Serre descent. We therefore
use FD as an explicit unresolved hypothesis, not as a theorem proved by the preceding
paragraphs and not by circular reference to a later volume.

**Proof of Theorem 4.1, conditional on FD.** The degree-two row of FD is

$$
0\longrightarrow H^2(F,\mu_n)\longrightarrow
\bigoplus_u H^2(F_u,\mu_n)\longrightarrow
\operatorname{Hom}(H^0(F,A_n),\mathbf Q/\mathbf Z)
\longrightarrow0.
\tag{4.3}
$$

The direct sum is legitimate because an unramified degree-two class vanishes at almost every finite place. Hilbert 90 and the Kummer sequence identify

$$
H^2(F,\mu_n)=\operatorname{Br}(F)[n],
\qquad
H^2(F_u,\mu_n)=\operatorname{Br}(F_u)[n].
$$

Since $H^0(F,A_n)=A_n$, the last term is canonically
$\frac1n\mathbf Z/\mathbf Z$, and the middle arrow is exactly the sum of the local
invariants. Thus (4.3) is the Brauer invariant sequence on $n$-torsion. Every Brauer class
and every finitely supported family of local invariants has finite exponent, so taking the
directed union over $n$ proves the theorem. $\square$

We record the degree-one consequence in the form needed later. This also makes precise
where the Grunwald--Wang condition lives. Let $S$ be a finite set of places, use Tate
groups at its real places, and put

$$
\begin{aligned}
\mathcal L_{n,S}&=\prod_{v\in S}H^1(K_v,A_n),\\
D_{n,S}&=\ker\left(
H^1(K,\mu_n)\longrightarrow
\prod_{v\notin S}H^1(K_v,\mu_n)
\right)\\
&=\frac{P(n,S)}{K^{\times n}},
\qquad
P(n,S)=\{a\in K^\times:a\in K_v^{\times n}\text{ for every }v\notin S\}.
\end{aligned}
\tag{4.W1}
$$

For $c_S=(c_v)_{v\in S}$ define

$$
\Omega_{n,S}(c_S)([a])
=\sum_{v\in S}\operatorname{inv}_v(c_v\smile a_v).
\tag{4.W2}
$$

The value is independent of the representative of $[a]$. Assuming FD, the degree-one
localization row is the exact sequence

$$
H^1(K,A_n)\longrightarrow\mathcal L_{n,S}
\xrightarrow{\ \Omega_{n,S}\ }
\operatorname{Hom}(D_{n,S},\mathbf Q/\mathbf Z)
\longrightarrow0.
\tag{4.W3}
$$

Equivalently, the image of global localization is the explicitly defined subgroup

$$
\mathcal L_{n,S}^{\mathrm{glob}}
=\left\{c_S:\sum_{v\in S}\operatorname{inv}_v(c_v\smile a_v)=0
\text{ for every }[a]\in D_{n,S}\right\},
\tag{4.W4}
$$

and the induced pairing

$$
\mathcal L_{n,S}/\mathcal L_{n,S}^{\mathrm{glob}}
\ \times\ D_{n,S}\longrightarrow\mathbf Q/\mathbf Z
$$

is perfect. Thus the perfectness assertion is about this quotient and this annihilator;
it is not an assertion that arbitrary degree-one local data are global.

Here is the elementary calculation of $D_{n,S}$. It is included both to identify the
exceptional class and to fix all hypotheses. Choose compatible primitive $2^r$th roots
of unity and write

$$
\eta_r=\zeta_{2^r}+\zeta_{2^r}^{-1}\qquad(r\geq2).
$$

There is a largest $s=s(K)\geq2$ for which $\eta_s\in K$, because $K$ has finite
degree. Set

$$
b_K=2+\eta_s,
\qquad
S_0(K)=\{v:-1,b_K,-b_K\notin K_v^{\times2}\}.
\tag{4.W5}
$$

The set $S_0(K)$ consists only of places above $2$. Indeed,

$$
K(\zeta_{2^{s+1}})=K(i,\sqrt{b_K}),
$$

so the three displayed square classes are the three quadratic subfields of this first
cyclotomic layer. At a nondyadic finite place the layer is unramified and its local
decomposition group is cyclic, not the Klein four group; at a real place $b_K$ is
positive under the corresponding embedding, and at a complex place every element is
a square. Thus at every place outside $2$ at least
one of the three elements is a square.

Write $n=2^\nu m$ with $m$ odd. We call $(K,n,S)$ **Wang-special** precisely when

$$
\nu\geq s+1,
\qquad
-1,b_K,-b_K\notin K^{\times2},
\qquad
S_0(K)\subseteq S.
\tag{4.W6}
$$

The first two conditions in (4.W6) are equivalently the familiar cyclotomic
hypothesis that $K(\zeta_{2^\nu})/K$ is noncyclic; the formulation in square
classes also identifies the bottom noncyclic layer and the relevant local places.

In that case put

$$
a_W(n)=b_K^{n/2}.
\tag{4.W7}
$$

The exact power-defect calculation is

$$
D_{n,S}=
\begin{cases}
\{1\},& (K,n,S)\text{ is not Wang-special},\\[2mm]
\{1,[a_W(n)]\},& (K,n,S)\text{ is Wang-special}.
\end{cases}
\tag{4.W8}
$$

We prove the calculation. First suppose (4.W6) holds. Since
$a_W(n)^2=b_K^n$, its class has order at most two. If $v\notin S_0(K)$,
at least one of the following three explicit $n$th roots exists:

$$
\begin{array}{c|c}
\text{square available in }K_v&\text{an }n\text{th root of }a_W(n)\\
\hline
b_K&r,\quad r^2=b_K,\\
-b_K&r,\quad r^2=-b_K,\\
-1&1+\zeta_{2^s}.
\end{array}
\tag{4.W9}
$$

For the second row, $n/2$ is even. For the third, $i\in K_v$ and
$\eta_s\in K_v$ imply $\zeta_{2^s}\in K_v$, while

$$
(1+\zeta_{2^s})^2=\zeta_{2^s}b_K,
\qquad
2^s\mid n/2;
$$

hence $(1+\zeta_{2^s})^n=b_K^{n/2}$. This proves that $[a_W(n)]$ is
locally trivial off $S_0(K)$. It is nontrivial globally and at every
$v\in S_0(K)$. For if $x^n=b_K^{n/2}$, then

$$
\xi=x^2/b_K\in\mu_{n/2}.
$$

The odd-order part of $\xi$ is a square. Because $-1$ is not a square, the
$2$-primary roots of unity in the field in question are only $\{\pm1\}$.
Consequently the square class of $\xi$ is $1$ or $-1$, which would make
$b_K$ or $-b_K$ a square, a contradiction.

It remains to show that there is no other class. Let $a\in P(n,S)$ and pass to
$K'=K(\mu_n)$. The element $a$ is an $n$th power in almost every completion
of $K'$. Since $\mu_n\subset K'$, the Kummer extension
$K'(a^{1/n})/K'$ therefore splits at almost every place. The simple-pole
separation argument proved above forces it to be trivial: deleting finitely many
Euler factors, all nonzero at $s=1$, does not change the order of the zeta pole. Choosing
$\beta^n=a$ in $K'$ gives the cocycle

$$
z_\sigma=\sigma(\beta)/\beta\in\mu_n
\qquad(\sigma\in\operatorname{Gal}(K'/K)).
\tag{4.W10}
$$

Thus the remaining question is a finite cyclotomic descent calculation. We spell it
out. Split (4.W10) into its prime-primary parts. For an odd prime $p$, adjoining
$\zeta_p$ has degree prime to $p$, so taking the norm kills the first descent
obstruction. Above it the successive $p$-power cyclotomic layers are cyclic. Their
intermediate root fields are therefore linearly ordered; the local-power hypothesis
makes the smallest one split at almost every place, and the simple-pole separation
argument makes it trivial. For $p=2$, all layers above
$K(\zeta_{2^{s+1}})$ have cyclic kernel. If $\nu\leq s$, the entire relevant
cyclotomic extension is cyclic and the ordered-root-field argument already finishes
the descent. We may therefore assume $\nu\geq s+1$; the same argument removes the
cyclic kernel above $K(\zeta_{2^{s+1}})$. At that bottom layer, the Galois group
is cyclic if one of $-1,b_K,-b_K$ is a square, and the ordered-root-field argument
then finishes. Otherwise it is the Klein four group. Let $c$ be cyclotomic
inversion, $c(\zeta_{2^{s+1}})=\zeta_{2^{s+1}}^{-1}$, and let $t$ send
$\zeta_{2^{s+1}}$ to
$-\zeta_{2^{s+1}}$. After a coboundary has normalized the cyclic layers, it is
enough to calculate on $\mu_{2^{s+1}}$. Put $\zeta=\zeta_{2^{s+1}}$ and write
$z_c=\zeta^r$, $z_t=\zeta^q$. The actions are

$$
c(\zeta)=\zeta^{-1},
\qquad
t(\zeta)=\zeta^{1+2^s}.
$$

The cocycle relations for $t^2=1$ and $ct=tc$ say respectively

$$
q(2+2^s)\equiv0,
\qquad
2q+2^sr\equiv0
\pmod {2^{s+1}}.
$$

Because $1+2^{s-1}$ is odd, these congruences say $q\in\{0,2^s\}$ and
$r$ is even. A coboundary defined by $\zeta^h$ changes

$$
(r,q)\longmapsto(r-2h,q+2^sh).
$$

Choose $h$ to make $r=0$. The remaining coboundaries that preserve $r=0$
do not change $q$, so exactly the following two classes remain:

$$
\begin{array}{c|c|c|c}
&z_c&z_t&\text{Kummer representative}\\
\hline
\text{trivial}&1&1&1,\\
\text{Wang}&1&-1&b_K^{n/2}.
\end{array}
\tag{4.W11}
$$

For the last row take $\beta=\sqrt{b_K}=\eta_{s+1}$; it is fixed by $c$,
negated by $t$, and satisfies $\beta^n=b_K^{n/2}$. The congruence calculation
shows conversely that multiplication by a coboundary reduces every solution to
one of the two rows. This is the entire noncyclic
calculation; the cyclic kernels already removed above introduce no further row.
The second row restricts nontrivially precisely where the bottom decomposition group
is Klein four, namely at the places in $S_0(K)$. It therefore survives localization
away from $S$ exactly when $S_0(K)\subseteq S$. This proves (4.W8), including all
nonexceptional alternatives.

Finally, conditional on FD, (4.W3) follows directly from the degree-one perfect pairing:
the annihilator
of the global image in the finite local product is the localization of $D_{n,S}$,
and finite perfect duality identifies the cokernel with its character group. This
derivation uses local reciprocity, Kummer theory, and Hypothesis FD, but not the
global existence theorem.

### 4.3 Construction of the fundamental class

For $L/K$ finite Galois, the local fundamental classes do not simply form a direct sum and descend. When $G$ is noncyclic, their denominators can have least common multiple smaller than $|G|$. The missing information lies one degree farther along the cohomology sequence. A correct construction must retain both local invariants and the global divisor relation.

Choose a finite $G$-stable set $S_L$ of places of $L$ containing the archimedean places, all places ramified over $K$, and finite primes whose classes generate $\operatorname{Cl}(L)$. Such primes can be obtained without a prime-distribution theorem: choose finitely many integral ideals generating the class group and include all their prime divisors. Also require that the decomposition groups of the places in $S_L$ generate $G$. This is possible because the subgroup generated by all decomposition groups has a fixed field that splits at every completion of $K$; the separation argument of Section 4.2 makes that fixed field equal to $K$, and finiteness of $G$ leaves a finite generating set of places. The ideal-class condition makes the ring of $S_L$-integers have trivial class group. Put

$$
Y_S=\mathbf Z[S_L],
\qquad
X_S=\ker\left(Y_S\xrightarrow{\sum}\mathbf Z\right),
$$

and let $U_{L,S}$ be the group of $S_L$-units. The valuation sequence is then exact:

$$
1\longrightarrow U_{L,S}\longrightarrow L^\times
\xrightarrow{(v_w)_{w\notin S_L}}
\bigoplus_{w\notin S_L}\mathbf Z\longrightarrow0.
$$

The surjectivity is precisely why we enlarged $S_L$ until the $S_L$-class group vanished.

The local two-extensions, the valuation sequence, and the Brauer relation indicate
what the desired object must be, but they do not by themselves construct its
middle modules or prove their cohomological triviality. In particular, the phrase
"take the mapping cone" is not a proof unless the complexes, comparison maps,
and subgroup restrictions are supplied. We therefore make the missing global
input explicit.

**Hypothesis TS (Tate's canonical $S$-unit sequence).** For every finite Galois
extension $L/K$ with group $G$, and every $S_L$ as above, the following data and
compatibilities are available.

1. There are specified $G$-homomorphisms in an exact sequence

   $$
   0\longrightarrow U_{L,S}\xrightarrow{i_S}A_S
   \xrightarrow{d_S}B_S\xrightarrow{p_S}X_S\longrightarrow0.
   \tag{TS1}
   $$

   Thus $i_S$ is injective, $p_S$ is surjective, and
   $\ker d_S=\operatorname{im}i_S$ and
   $\ker p_S=\operatorname{im}d_S$. For every subgroup $H\subseteq G$ and
   every $r\in\mathbf Z$,

   $$
   \widehat H^r(H,A_S)=\widehat H^r(H,B_S)=0.
   \tag{TS2}
   $$

   Cohomological triviality in (TS2) is part of the input; it is not inferred
   merely from an unspecified kernel between induced modules.

2. The Yoneda class

   $$
   \tau_{L/K,S}=[\text{(TS1)}]
   \in\operatorname{Ext}^2_{\mathbf Z[G]}(X_S,U_{L,S})
   \tag{TS3}
   $$

   comes with comparison maps to the valuation sequence outside $S_L$ and to
   the induced local fundamental two-extensions. For each $w\in S_L$, with
   $v=w|_K$, restriction to $D_w$ followed by the $w$-coordinate comparison is
   the local fundamental class

   $$
   u_{L_w/K_v}\in H^2(D_w,L_w^\times),
   \qquad
   \operatorname{inv}_v(u_{L_w/K_v})=\frac1{|D_w|}.
   \tag{TS4}
   $$

   This clause includes the commutativity of the localization, valuation, and
   augmentation diagrams; equality only of unnamed extension classes is not
   sufficient. A place outside the chosen $S_L$ is handled by first enlarging
   $S_L$ to contain its $G$-orbit and then using the transition identity below.

3. If $S_L\subseteq S'_L$ are admissible sets, write $j_U:U_{L,S}\to
   U_{L,S'}$ and $j_X:X_S\to X_{S'}$ for the natural maps. The extension
   classes satisfy the precisely typed transition identity

   $$
   (j_U)_*\tau_{L/K,S}=(j_X)^*\tau_{L/K,S'}
   \quad\text{in}\quad
   \operatorname{Ext}^2_{\mathbf Z[G]}(X_S,U_{L,S'}).
   \tag{TS4a}
   $$

   After adding split two-extensions with induced middle modules when needed,
   this equality is represented by a morphism of the exact sequences (TS1).
   The comparison morphisms can be chosen transitively for
   $S_L\subseteq S'_L\subseteq S''_L$ and compatibly with every local
   comparison in (TS4). Consequently all admissible $S_L$ give the same
   spliced class below.

4. Splicing (TS1), through the comparison maps in clause 2, with the valuation
   sequence outside $S_L$ and
   $1\to L^\times\to\mathbf I_L\to C_L\to1$ gives a specified exact
   two-extension

   $$
   0\longrightarrow C_L\longrightarrow A_{L/K}
   \longrightarrow B_{L/K}\longrightarrow\mathbf Z\longrightarrow0,
   \tag{TS5}
   $$

   whose two middle modules remain cohomologically trivial after restriction to
   every subgroup of $G$. Its class

   $$
   u_{L/K}\in H^2(G,C_L)
   \tag{TS6}
   $$

   is independent of $S_L$ and of the choices of places above $S_K$. If
   $H\subseteq G$ and $E=L^H$, then restriction of (TS5) represents the
   canonical sequence for $L/E$ and

   $$
   \operatorname{inv}_E\bigl(\operatorname{res}^G_Hu_{L/K}\bigr)
   =\frac1{|H|}.
   \tag{TS7}
   $$

   These identifications are transitive in chains of subgroups and are
   compatible with the local restriction and corestriction formulas of Section
   4.5.

TS is the exact global canonical-sequence theorem needed here. Books 1--5 provide
the valuation sequences, local fundamental classes, and local invariant
normalizations, but not TS. The global localization compatibility required in
clauses 2--4 uses the input [FD] isolated in Section 4.2; complete Tate
cohomology, Yoneda extensions, cap products, and dimension shifting are the
input [TC] isolated in Book 5. Neither [FD] nor [TC] constructs (TS1)--(TS5),
so TS is an independent prerequisite rather than a consequence of their
conjunction.

The discarded mapping-cone outline still explains the shape of TS: inducing the
local classes accounts for $Y_S$, pulling back along $X_S\hookrightarrow Y_S$
imposes total degree zero, and the valuation sequence accounts for $U_{L,S}$.
What it did not establish are exactly the data and compatibilities now listed in
(TS1)--(TS7).

Conditional on TS, (TS6) is the **global fundamental class**. The dependency
persists in the degree-two part of Lemma 4.3, Lemma 4.4, Theorem 5.1 and all of
its norm-kernel and tower consequences, the norm-subgroup clause of Lemma 6.2,
Theorem 6.3 as stated, formula (9.1), Theorem 10.1 as derived here, and the
finite-reciprocity assertions in the closing dictionaries. Results using only
local invariants or [FD], such as Theorem 6.1 and the cyclic-algebra proof of
Theorem 9.1, do not depend on TS.

### 4.4 The two class-formation lemmas

The cap-product argument needs two inputs: degree-one vanishing and a normalized cyclic group in degree two.

**Lemma 4.3 [FD,TS].** For every subgroup $H\subseteq G$,

$$
H^1(H,C_L)=0,
\qquad
H^2(H,C_L)=\langle\operatorname{res}^G_Hu_{L/K}\rangle
\cong\frac1{|H|}\mathbf Z/\mathbf Z.
$$

**Proof.** Put $E=L^H$. From

$$
1\longrightarrow L^\times\longrightarrow\mathbf I_L
\longrightarrow C_L\longrightarrow1
$$

and Hilbert 90, the relevant connecting map embeds $H^1(H,C_L)$ into $H^2(H,L^\times)$. Under localization, $H^2(H,L^\times)$ is the relative Brauer group $\operatorname{Br}(L/E)$, while $H^2(H,\mathbf I_L)$ is the direct sum of the relative local Brauer groups, by Shapiro. The Brauer invariant sequence says that a global class whose localizations vanish is zero. Thus $H^1(H,C_L)=0$.

For degree two, restrict (TS5) to $H$. By (TS2) and clause 4 of TS, its
middle terms remain cohomologically trivial. The connecting map therefore
identifies

$$
\widehat H^0(H,\mathbf Z)=\mathbf Z/|H|\mathbf Z
$$

with $H^2(H,C_L)$. It sends $1$ to $\operatorname{res}^G_Hu_{L/K}$, so the latter is a generator and the group has order $|H|$. $\square$

This calculation retains the real summands $\frac12\mathbf Z/\mathbf Z$ when a real place complexifies. Dropping them changes the total-invariant cokernel and gives a false power of two.

**Lemma 4.4 (class-formation lemma) [FD,TS,TC].** Cap product with
$u_{L/K}$ induces isomorphisms

$$
\widehat H^{r-2}(H,\mathbf Z)
\xrightarrow{\sim}
\widehat H^r(H,C_L)
$$

for every subgroup $H\subseteq G$ and every integer $r$.

**Proof.** Represent the restricted fundamental class by a two-extension

$$
0\to C_L\to A_1\to A_0\to\mathbf Z\to0
$$

with $A_0,A_1$ the cohomologically trivial modules supplied by (TS5). The
connecting map sends $1\bmod |H|$ in
$\widehat H^0(H,\mathbf Z)$ to the restricted fundamental class, a generator of
$H^2(H,C_L)$ by Lemma 4.3. It is therefore an isomorphism in degree two. The
neighboring map is an isomorphism because $H^1(H,C_L)=0$. Dimension shifting
through the two-extension now propagates the two consecutive isomorphisms in both
directions: the Tate cohomology of each middle module is zero, so every connecting
map shifts degree by one. By [TC], these connecting maps are cap products with
$u_{L/K}$. $\square$

Thus Lemma 4.4 is a formal deduction from TS, [FD], and [TC], not a construction
of the canonical sequence. This distinction prevents the dimension-shifting
argument from being read circularly as a proof of its own cohomologically trivial
resolution.

### 4.5 Restriction, corestriction, and invariant normalizations

Hypothesis TS requires Brauer invariants to normalize the fundamental class.
Duality arguments use the same invariants in a second role: they are the trace
maps that turn cup products into numbers. That use is unforgiving about degrees.
We therefore record the normalization, including archimedean places and products
of local fields, before proceeding to reciprocity.

For every place $v$ of a number field $F$, write

$$
\operatorname{inv}_v:\operatorname{Br}(F_v)\longrightarrow\mathbf Q/\mathbf Z.
$$

At a finite place this is the local invariant normalized in Book 5: an unramified cyclic algebra

$$
(E/F_v,\operatorname{Frob}^{\mathrm{arith}},\pi_v)
$$

of degree $d$ has invariant $1/d$. At a real place the nonsplit quaternion algebra has invariant $1/2$, so the image is $\frac12\mathbf Z/\mathbf Z$. At a complex place the Brauer group is zero. Thus the same target may be used everywhere, but the image depends on the place.

Let $E/F_v$ be a finite extension of local fields. Restriction and corestriction satisfy

$$
\operatorname{inv}_E(\operatorname{res}_{E/F_v}\alpha)
=[E:F_v]\operatorname{inv}_v(\alpha),
\tag{4.4}
$$

and

$$
\operatorname{inv}_v(\operatorname{cor}_{E/F_v}\beta)
=\operatorname{inv}_E(\beta).
\tag{4.5}
$$

For nonarchimedean fields, (4.4) is the restriction formula for the local invariant. To prove (4.5), choose $\alpha\in\operatorname{Br}(F_v)$ restricting to $\beta$; such an $\alpha$ exists because multiplication by $[E:F_v]$ is onto on $\mathbf Q/\mathbf Z$. Then

$$
\operatorname{cor}_{E/F_v}(\beta)
=\operatorname{cor}_{E/F_v}\operatorname{res}_{E/F_v}(\alpha)
=[E:F_v]\alpha,
$$

and the two invariant formulas agree. At $\mathbf R$ and $\mathbf C$ the assertions follow directly from the two possible Brauer classes and the fact that restriction from $\mathbf R$ to $\mathbf C$ kills the quaternion class. Transitivity of restriction and corestriction proves the formulas in every local tower.

A completion of a global extension is often a product rather than one field. If

$$
E=\prod_{i=1}^r E_i
$$

is a finite étale $F_v$-algebra, set

$$
\operatorname{Br}(E)=\bigoplus_i\operatorname{Br}(E_i),
\qquad
\operatorname{cor}_{E/F_v}(\beta_i)
=\sum_i\operatorname{cor}_{E_i/F_v}(\beta_i).
$$

Then (4.5) becomes the indispensable sum formula

$$
\operatorname{inv}_v\!\left(
\operatorname{cor}_{E/F_v}(\beta_i)_i
\right)
=\sum_i\operatorname{inv}_{E_i}(\beta_i).
\tag{4.6}
$$

Likewise,

$$
\sum_i\operatorname{inv}_{E_i}
(\operatorname{res}_{E_i/F_v}\alpha)
=\left(\sum_i[E_i:F_v]\right)\operatorname{inv}_v(\alpha).
\tag{4.7}
$$

For $E=L\otimes_FF_v$, the degree sum in (4.7) is $[L:F]$. These identities explain why one must sum over every $w\mid v$ in an adelic norm or trace. Selecting one completion would lose exactly the factors that make global restriction and corestriction compatible.

The global invariant sequence of Theorem 4.1 now reads

$$
0\longrightarrow\operatorname{Br}(F)
\longrightarrow\bigoplus_v\operatorname{Br}(F_v)
\xrightarrow{(\alpha_v)\mapsto\sum_v\operatorname{inv}_v(\alpha_v)}
\mathbf Q/\mathbf Z\longrightarrow0.
\tag{4.8}
$$

The direct sum is literal: a global central simple algebra is split at all but finitely many places. Exactness says both that every global class has total invariant zero and that this is the only relation among finitely supported local classes. The real summands are part of (4.8). Omitting them can turn a true total-invariant-zero statement into a false one at the prime $2$.

### 4.6 Cup products and the local trace

Let $n\geq1$, let $M$ be a finite module for the absolute Galois group of a local field $F$, and suppose $nM=0$. Its Tate dual is

$$
M^D=\operatorname{Hom}(M,\mu_n),
$$

with the contragredient Galois action. Evaluation $M\otimes M^D\to\mu_n$ and cup product give

$$
H^r(F,M)\times H^{2-r}(F,M^D)
\longrightarrow H^2(F,\mu_n)
\longrightarrow\operatorname{Br}(F)[n].
$$

Composing with the local invariant gives the numerical pairing

$$
\langle x,y\rangle_F
=\operatorname{inv}_F(x\smile y)
\in\tfrac1n\mathbf Z/\mathbf Z.
\tag{4.9}
$$

At a real place, Tate cohomology is used in every degree; at a complex place the pairing is zero. This convention is what permits one formula to include finite and infinite places.

The compatibility needed in every descent argument is adjointness of restriction and corestriction. If $E/F$ is finite, $x\in H^r(F,M)$, and $y\in H^{2-r}(E,M^D)$, the projection formula for cup products says

$$
\operatorname{cor}_{E/F}
(\operatorname{res}_{E/F}x\smile y)
=x\smile\operatorname{cor}_{E/F}y.
$$

Taking invariants and using (4.5) proves

$$
\langle\operatorname{res}_{E/F}x,y\rangle_E
=\langle x,\operatorname{cor}_{E/F}y\rangle_F.
\tag{4.10}
$$

If $E$ is a product of fields, the left side is the sum over its factors. Formula (4.10), not a degree-adjusted variant of it, is the normalization used in global duality. The degree already appears in restriction of Brauer classes through (4.4); inserting another degree would count it twice.

The case used in the existence theorem can be proved directly from local reciprocity. Take

$$
M=A_n=\mathbf Z/n\mathbf Z,
\qquad M^D=\mu_n.
$$

Kummer theory gives

$$
H^1(F,\mu_n)=F^\times/F^{\times n},
$$

while local reciprocity identifies $H^1(F,A_n)$ with the continuous $\mathbf Z/n\mathbf Z$-valued characters of $F^\times$. We fix the cup-product sign by requiring

$$
\operatorname{inv}_F(c\smile a)
=\frac{c(\operatorname{rec}_F(a))}{n}
\quad\text{in }\tfrac1n\mathbf Z/\mathbf Z.
\tag{4.11}
$$

Here the residue class $r\in A_n$ on the right is sent to
$r/n\in\frac1n\mathbf Z/\mathbf Z$. Equivalently, after the fixed embedding

$$
\jmath_n:A_n\longrightarrow\mu_n(\mathbf C),
\qquad
r\longmapsto e^{2\pi i r/n},
$$

exponentiating (4.11) gives

$$
\exp\!\left(2\pi i\operatorname{inv}_F(c\smile a)\right)
=\jmath_n\!\left(c(\operatorname{rec}_F(a))\right).
$$

For a cyclic character, the exponentiated identity is the cyclic norm-residue symbol: the two
characters have the same kernel, namely the norm group of the cyclic extension cut out by $c$,
and they send an unramified uniformizer to the chosen arithmetic Frobenius value. Cyclic
decomposition and bilinearity prove (4.11) in general.

This pairing is perfect. Indeed, local reciprocity identifies

$$
F^\times/F^{\times n}
$$

with a finite abelian quotient of exponent dividing $n$, and $H^1(F,A_n)$ is its full character group. Evaluation gives finite Pontryagin duality. Thus the special local duality used in Chapter 6 is already a consequence of local class field theory and Kummer theory; no global existence assertion enters its proof.

### 4.7 The global trace and the duality pairing

Now let $F$ be a number field and let $M$ be a finite $G_F$-module annihilated by $n$. For global classes

$$
x\in H^r(F,M),
\qquad y\in H^{2-r}(F,M^D),
$$

the localized cup products vanish at almost every place. To see this, enlarge a finite set until both modules and both classes are unramified outside it and all primes dividing $n$ lie inside it. At a remaining finite place both classes inflate from the procyclic unramified quotient; that quotient has cohomological dimension one for finite torsion of order prime to the residue characteristic, so their degree-two cup product is zero. Hence the following sum is finite.

The global Brauer reciprocity law gives

$$
\sum_v\langle\operatorname{loc}_v x,
\operatorname{loc}_v y\rangle_{F_v}
=\sum_v\operatorname{inv}_v
(\operatorname{loc}_v(x\smile y))
=0.
\tag{4.12}
$$

This is the exact form in which global reciprocity enters Tate duality: two diagonal global classes are orthogonal under the sum of all local invariant pairings. It is stronger than the product formula for absolute values and more general than the quadratic Hilbert-symbol product formula, but both are shadows of the same total-trace-zero principle.

It is useful to place the degree shift in plain view. Fix a finite set $S$ containing the archimedean places, the places above $n$, and the places where $M$ is ramified. Define the compact-support complex

$$
C_{S,c}^\bullet(M)=
\operatorname{Cone}\!\left(
C^\bullet(G_{F,S},M)
\longrightarrow\bigoplus_{v\in S}C^\bullet(G_{F_v},M)
\right)[-1],
\tag{4.13}
$$

with Tate cochains at real places. The local invariant sum and (4.8) induce a trace

$$
\operatorname{tr}_F:H^3(C_{S,c}^\bullet(\mu_n))
\longrightarrow\tfrac1n\mathbf Z/\mathbf Z.
\tag{4.14}
$$

Why degree three? A local Brauer class has degree two, while the cone in (4.13) shifts the local term upward by one. Why is the trace well defined? Changing a representative by a localized global degree-two cocycle changes the proposed value by the sum of the invariants of one global Brauer class, which is zero by (4.8). Conversely, exactness of (4.8) shows that no further relation has been imposed.

Cup product of a compactly supported cochain with an ordinary cochain, followed by (4.14), gives

$$
H^r(C_{S,c}^\bullet(M))
\times H^{3-r}(G_{F,S},M^D)
\longrightarrow\tfrac1n\mathbf Z/\mathbf Z.
\tag{4.15}
$$

This is the trace-and-pairing layer used in Poitou--Tate arguments. The assertion that (4.15) is perfect for every finite module is a further global duality theorem; it is not needed to prove reciprocity here. For the pair $A_n,\mu_n$ used in Theorems 4.1 and 6.1, the required perfectness is exactly Hypothesis FD; the units--divisors--ideal-classes sequence (4.2) alone does not prove it. Separating the trace construction from the perfectness input prevents global reciprocity and global duality from being used to prove one another.

Restriction and corestriction preserve the global trace with no hidden degree. If $E/F$ is finite and $(z_w)_w$ is a family of local degree-two classes over $E$, then (4.6) gives

$$
\sum_v\operatorname{inv}_v
\left(\sum_{w\mid v}\operatorname{cor}_{E_w/F_v}z_w\right)
=\sum_w\operatorname{inv}_w(z_w).
\tag{4.16}
$$

Together with the projection formula, this makes global restriction adjoint to global corestriction under (4.15). Formula (4.16) is the bookkeeping identity behind every norm-compatible local condition.

### 4.8 Norms, induction, and Shapiro compatibility

The same maps have three languages, and later arguments move among them quickly. We make the identifications explicit.

For the multiplicative module, degree-zero corestriction is the field norm:

$$
H^0(E,\mathbf G_m)=E^\times
\xrightarrow{\operatorname{cor}_{E/F}=N_{E/F}}
F^\times=H^0(F,\mathbf G_m).
\tag{4.17}
$$

In degree two it is Brauer corestriction. Locally, the square

$$
\begin{array}{ccc}
\operatorname{Br}(E)&\xrightarrow{\operatorname{cor}_{E/F}}&\operatorname{Br}(F)\\
\downarrow&&\downarrow\\
\displaystyle\bigoplus_w\operatorname{Br}(E_w)&
\xrightarrow{(\beta_w)\mapsto
(\sum_{w\mid v}\operatorname{cor}_{E_w/F_v}\beta_w)_v}&
\displaystyle\bigoplus_v\operatorname{Br}(F_v)
\end{array}
\tag{4.18}
$$

commutes. For crossed products this follows by inducing the semilinear algebra from $G_E$ to $G_F$; in general it follows after passage to a common splitting field and additivity in the Brauer group. Applying invariants to the bottom row is exactly (4.16).

At the adelic degree-zero level, (4.17) becomes

$$
(y_w)_w\longmapsto
\left(\prod_{w\mid v}N_{E_w/F_v}(y_w)\right)_v.
\tag{4.19}
$$

Thus cohomological corestriction is the idele norm, including the product over all branches. On a diagonal element $y\in E^\times$, (4.19) is the diagonal idele of $N_{E/F}y$; principal ideles are therefore preserved. This is the precise compatibility that lets the norm descend from ideles to idele classes.

For a finite $G_E$-module $A$, induction and coinduction agree because $G_E$ has finite index in $G_F$. Shapiro's isomorphism is

$$
H^r(F,\operatorname{Ind}_{E/F}A)
\xrightarrow{\sim}H^r(E,A).
\tag{4.20}
$$

Evaluation on coset representatives shows that the cup product of an induced class with a class over $F$ corresponds under (4.20) to the cup product after restriction to $E$. Taking the trace then gives the same adjointness as (4.10). Consequently the following four statements are one compatibility expressed at different levels:

- norm on multiplicative groups is corestriction in degree zero;
- norm on ideles is the product of all local corestrictions;
- restriction is adjoint to corestriction under local and global invariant pairings;
- Shapiro identifies induced cohomology with the cohomology over the extension field without changing the trace.

The degree factors have now all been located: restriction of a local Brauer class multiplies its invariant by the local degree, while corestriction preserves the invariant and sums over branches. Norms therefore require no extra degree correction. This convention is the one used by the reciprocity diagrams in Section 5.3 and by the character-induction formulas in Chapter 11.

## 5. Finite global reciprocity

Every assertion in this chapter that identifies an Artin kernel with an
idele-class norm group, or derives tower compatibility from the global
fundamental class, is under [FD,TS,TC]. The local Artin maps and their product
from Chapter 2 are defined independently of TS.

### 5.1 The reciprocity isomorphism

We can now identify the norm quotient without guessing its order.

**Theorem 5.1 (finite global reciprocity) [FD,TS,TC].** Let $L/K$ be
finite Galois with group $G$. Cap product with the fundamental class gives a
canonical isomorphism

$$
G^{\mathrm{ab}}\xrightarrow{\sim}C_K/N_{L/K}C_L.
$$

Its inverse is the global Artin map constructed as the product of the local arithmetic reciprocity maps. In particular, if $L/K$ is abelian,

$$
\operatorname{Art}_{L/K}:C_K/N_{L/K}C_L
\xrightarrow{\sim}\operatorname{Gal}(L/K).
$$

**Proof.** Apply the conditional Lemma 4.4 with $H=G$ and $r=0$. The source is

$$
\widehat H^{-2}(G,\mathbf Z)=H_1(G,\mathbf Z)=G^{\mathrm{ab}},
$$

and the target is $\widehat H^0(G,C_L)=C_K/N C_L$. It remains to identify the inverse with the product of local maps. Localization of $u_{L/K}$ is the local fundamental class at every decomposition group. Naturality of cap product and Shapiro's lemma therefore make the restriction to $K_v^\times$ equal to local reciprocity followed by $D_w^{\mathrm{ab}}\to G^{\mathrm{ab}}$. Outside the finite ramification set both maps kill the local unit group. Every idele is therefore congruent modulo their common unit tail to a finite product of single-coordinate ideles, on which the maps agree. $\square$

This simultaneously proves surjectivity, the kernel formula, and the exact index statement

$$
[C_K:N_{L/K}C_L]=|G^{\mathrm{ab}}|.
$$

For abelian $L/K$ this is $[L:K]$. The theorem also proves the idelic norm-limitation formula announced earlier: if $M=L^{[G,G]}$, the maps for $L$ and $M$ have the same target and the same local quotient maps, whence

$$
N_{L/K}C_L=N_{M/K}C_M.
$$

### 5.2 Frobenius, decomposition, and inertia

Assume in this section that $L/K$ is finite abelian. Then the decomposition and inertia groups are actual subgroups of the global Artin target, rather than only images in an abelianization.

Embed $K_v^\times$ in $\mathbf I_K$ at the $v$-coordinate. Finite reciprocity and local compatibility give

$$
\operatorname{Art}_{L/K}(K_v^\times)=D_w,
\qquad
\operatorname{Art}_{L/K}(\mathcal O_v^\times)=I_w
$$

at a finite place. More deeply, for the filtration fixed in Section 1.2,

$$
\operatorname{Art}_{L/K}(U_v^n)=D_w^n
$$

for the upper-numbering ramification group. Thus every local ramification invariant sits visibly inside the global map.

At an unramified place,

$$
\operatorname{Art}_{L/K}(\pi_v)=\operatorname{Frob}_v^{\mathrm{arith}}.
$$

It follows that $v$ splits completely precisely when the class of an idele uniformizer at $v$ lies in $N C_L$. More generally, the residue degree of $v$ equals the order of its Frobenius in $G$, and the number of primes above $v$ is $|G|/|D_w|$.

At a real place $v$, the image of $\mathbf R^\times$ is trivial if every place above $v$ is real, and has order two if $v$ becomes complex. The positive half-line is always in the kernel. This is the archimedean analogue of inertia, although it is better described as the component group than as a valuation filtration.

### 5.3 Compatibility in quotients and towers

Let $E/K$ and $L/K$ be finite abelian extensions in a common separable closure. When $E\subseteq L$, restriction of automorphisms and the identity map on $C_K$ give a commutative square

$$
\begin{array}{ccc}
C_K&\xrightarrow{\operatorname{Art}_{L/K}}&\operatorname{Gal}(L/K)\\
\Vert&&\downarrow\operatorname{res}\\
C_K&\xrightarrow{\operatorname{Art}_{E/K}}&\operatorname{Gal}(E/K).
\end{array}
$$

Hence $E\subseteq L$ implies the reverse inclusion of norm subgroups. Conversely, if the
norm-subgroup inclusion holds, apply finite reciprocity to the abelian compositum $EL/K$: the
subgroup fixing $E$ contains the subgroup fixing $L$, so $E\subseteq L$. Therefore

$$
E\subseteq L
\quad\Longleftrightarrow\quad
N_{L/K}C_L\subseteq N_{E/K}C_E.
$$

Now let $L/K$ be any finite extension, in a common separable closure. Finite reciprocity already
assembles, over the finite abelian quotients, maps $C_F\to G_F^{\mathrm{ab}}$ for
$F=K,L$; this assembly does not use the existence theorem or assert surjectivity. Chapter 10
will identify its topology after existence has been proved. With that interpretation, the idele
norm corresponds to inclusion of Galois groups:

$$
\begin{array}{ccc}
C_L&\xrightarrow{\operatorname{Art}_L}&G_L^{\mathrm{ab}}\\
N_{L/K}\downarrow&&\downarrow i_*\\
C_K&\xrightarrow{\operatorname{Art}_K}&G_K^{\mathrm{ab}}.
\end{array}
$$

Here $i_*$ is induced by $G_L\hookrightarrow G_K$. In the opposite direction, scalar inclusion $\mathbf I_K\to\mathbf I_L$ corresponds to group-theoretic transfer:

$$
\begin{array}{ccc}
C_K&\xrightarrow{\operatorname{Art}_K}&G_K^{\mathrm{ab}}\\
\downarrow&&\downarrow\operatorname{Ver}_{L/K}\\
C_L&\xrightarrow{\operatorname{Art}_L}&G_L^{\mathrm{ab}}.
\end{array}
$$

The first vertical map sends $(x_v)$ to the idele whose $w$-component is $x_v$ for $w\mid v$. These crossed directions mirror local reciprocity. Norms and inclusions compose transitively, as do restriction and transfer.

The field lattice becomes particularly transparent. If $E/K$ and $F/K$ are finite abelian, then

$$
N_{EF/K}C_{EF}=N_{E/K}C_E\cap N_{F/K}C_F,
$$

because an idele class acts trivially on the compositum exactly when it acts trivially on both fields. Similarly,

$$
N_{E\cap F/K}C_{E\cap F}
=N_{E/K}C_E\,N_{F/K}C_F.
$$

The product on the right is already open and hence closed. To prove the second identity, quotient $C_K$ by the product. Its character group consists of characters trivial on both norm subgroups, hence of Galois characters factoring through both $E$ and $F$; these are exactly the characters factoring through $E\cap F$. Finite character duality then identifies the kernels. These formulas give the concrete meaning of inclusion reversal beyond a single tower.

### 5.4 A first explicit calculation over the rationals

Let $m\geq1$ and consider $L=\mathbf Q(\zeta_m)$. For a prime $p\nmid m$, arithmetic Frobenius satisfies

$$
\operatorname{Frob}_p(\zeta_m)=\zeta_m^p.
$$

Thus the identification

$$
\operatorname{Gal}(L/\mathbf Q)\cong(\mathbf Z/m\mathbf Z)^\times
$$

sends the Artin symbol of $p$ to $p\bmod m$. A rational prime splits completely exactly when $p\equiv1\pmod m$. At primes dividing $m$, the ideal Frobenius is not defined; local units and higher units measure tame and wild inertia.

For $m=8$, the three nontrivial quadratic characters of $(\mathbf Z/8\mathbf Z)^\times$ cut out $\mathbf Q(i)$, $\mathbf Q(\sqrt2)$, and $\mathbf Q(\sqrt{-2})$. The same ray quotient therefore records several fields at once. This foreshadows the existence theorem: subgroups, rather than individual congruence characters, are the natural objects classified by fields.

## 6. The global existence theorem

### 6.1 Why reciprocity does not yet give existence

Theorem 5.1 begins with $L$ and identifies its norm subgroup. The converse begins with an open finite-index subgroup $H\subseteq C_K$ and must construct $L$. There is no formal reason that the already existing norm groups exhaust all open subgroups. We now prove that they do.

Since $C_K/H$ is finite abelian, its characters separate its points. It is therefore enough to realize every finite-order continuous character of $C_K$ as a Galois character. Taking the compositum of the resulting cyclic fields then recovers the intersection of their kernels, which is $H$.

### 6.2 The finite local--global character sequence

The clean existence argument does not assume that $K$ contains roots of unity. Fix $n\geq1$, let

$$
A_n=\mathbf Z/n\mathbf Z
$$

with trivial Galois action, and let its Cartier dual be $A_n^\vee=\mu_n$. Local cup product and the local Brauer invariant give a perfect pairing

$$
H^1(K_v,A_n)\times H^1(K_v,\mu_n)
\longrightarrow \tfrac1n\mathbf Z/\mathbf Z,
\qquad
(c,a)\longmapsto\operatorname{inv}_v(c\smile a).
$$

Here $H^1(K_v,\mu_n)=K_v^\times/K_v^{\times n}$ by Kummer theory, whether or not $\mu_n\subset K_v$. At a real place the same formula uses Tate cohomology; at a complex place both groups vanish. At almost every finite place there are distinguished unramified subgroups. We write

$$
\prod_v' H^1(K_v,A_n)
$$

for the restricted product with respect to them.

**Theorem 6.1 (finite local--global duality) [FD].** The sequence

$$
H^1(K,A_n)
\xrightarrow{\operatorname{loc}}
\prod_v' H^1(K_v,A_n)
\xrightarrow{\lambda}
\operatorname{Hom}\bigl(H^1(K,\mu_n),\mathbf Q/\mathbf Z\bigr)
$$

is exact at the middle term, where

$$
\lambda((c_v))(a)
=\sum_v\operatorname{inv}_v(c_v\smile a_v).
$$

The sum is finite. The localization map on the left is injective.

**Proof, conditional on FD.** Choose a finite set $S$ containing the archimedean places, the places above $n$, and the ramified places of the local family under consideration. Apply the pairing and localization compatibility asserted by FD to the degree-one portion of the long exact compact-support sequence. Perfectness says that the annihilator of the image of the global group is exactly the kernel of the dual localization functional. Written out, this is

$$
\operatorname{im}\left(
H^1(G_{K,S},A_n)\longrightarrow
\prod_{v\in S}H^1(K_v,A_n)
\right)
=\ker\lambda_S.
$$

Enlarging $S$ adds the unramified local terms on both sides. Passing to the directed limit gives the displayed restricted-product sequence. This step is why the target is a restricted product rather than an unrestricted product.

It remains to prove injectivity on the left. If a global character is trivial in every completion, the cyclic extension $E/K$ that it cuts out has every decomposition group trivial. The split-everywhere separation fact proved in Section 4.2 gives $E=K$. Hence the character is trivial and localization is injective. $\square$

We can now state the exact Grunwald--Wang alternative rather than merely warn that
one exists. Let $S$ be finite, let

$$
c_v\in H^1(K_v,A_n)\qquad(v\in S),
$$

and suppose that the least common multiple of the orders of the $c_v$ is $n$.
Via local reciprocity these are the additive forms of prescribed local cyclic
characters. If $(K,n,S)$ is Wang-special in the precise sense of (4.W6), define
the **Wang sign at $v$** by

$$
\epsilon_v(c_v)
=\exp\left(2\pi i\operatorname{inv}_v
\bigl(c_v\smile a_W(n)_v\bigr)\right)\in\{+1,-1\}.
\tag{6.W1}
$$

The value is a sign because $[a_W(n)]$ has order two. It is $+1$ away from
$S_0(K)$, and local reciprocity gives the equally concrete formula

$$
\epsilon_v(c_v)
=\jmath_n\!\left(c_v(\operatorname{rec}_{K_v}(a_W(n)))\right).
\tag{6.W2}
$$

The complete alternative is as follows.

- If $(K,n,S)$ is not Wang-special, every prescribed tuple $(c_v)_{v\in S}$
  is the localization of a class in $H^1(K,A_n)$.

- If $(K,n,S)$ is Wang-special, such a class exists if and only if

  $$
  \prod_{v\in S_0(K)}\epsilon_v(c_v)=+1.
  \tag{6.W3}
  $$

- If the product in (6.W3) is $-1$, no exponent-$n$ global character has the
  prescribed localizations. After the canonical inclusion
  $A_n\hookrightarrow A_{2n}$, $x\mapsto2x$, the same local characters are the
  localizations of a global $A_{2n}$-valued character. Every such character has
  order exactly $2n$. Thus the exceptional replacement is degree $2n$, not an
  unspecified failure or an unspecified extra class.

Taking fixed fields translates this verbatim into the extension form: the resulting
field is cyclic of degree $n$ in the unobstructed case and of degree $2n$ in the
obstructed case, and its completion at $v\in S$ is the cyclic extension cut out by
$\ker c_v$.

Indeed, the finite-support exact sequence (4.W3) says that the only functionals
to test are the classes in $D_{n,S}$. Formula (4.W8) makes that group either zero
or $\langle[a_W(n)]\rangle$, and (6.W1) turns its single nonzero functional into
the product (6.W3). In the obstructed case the exceptional class at level $2n$ is

$$
a_W(2n)=b_K^n=a_W(n)^2.
$$

Every embedded local character therefore evaluates trivially on it: its Wang sign
is the square of the old sign. Applying (4.W3) at level $2n$ produces the global
class. Its order is a multiple of the least common multiple $n$ of the local
orders and divides $2n$; it cannot have order $n$, by the failed sign test, so its
order is $2n$.

This proof is not using the existence theorem that follows. It uses the finite
duality calculation of Section 4.2, the explicit cyclotomic descent (4.W8), and
local reciprocity. In particular, for $K=\mathbf Q$, $n=8$, and $S=\{2\}$ one
has $s=2$, $b_K=2$, $S_0(K)=\{2\}$, and

$$
a_W(8)=2^4=16.
$$

Thus the familiar obstruction is exactly the sign obtained by evaluating the
prescribed $2$-adic character on $16$.

The all-place family used in our existence argument has a different and simpler
source. It comes from an idele class character. For every $a\in K^\times$, the
product of its local evaluations is the value of that character on the principal
idele $(a)_v$, hence is $1$. Equivalently,
$\lambda((c_v))(a)=0$ for every global Kummer class $a$. This proves automatic
orthogonality directly; it does not assume that the Wang class is absent, nor does
it appeal to the global field whose existence is about to be proved.

### 6.3 Constructing the global character

Let $\chi:C_K\to\mathbf C^\times$ be continuous of finite order, and choose $n$ annihilating its image. Then $\operatorname{im}\chi\subseteq\mu_n(\mathbf C)$. Use the fixed embedding $\jmath_n$ from Section 4.6. For every place $v$, define the unique local additive character

$$
c_v\in H^1(K_v,A_n)
$$

given by the character form of local reciprocity and the identity

$$
\jmath_n\!\left(c_v(\operatorname{rec}_{K_v}(x))\right)
=\chi_v(x)
\qquad(x\in K_v^\times).
$$

Continuity of $\chi$ says that $c_v$ is unramified for almost every $v$, so $(c_v)$ belongs to the restricted product in Theorem 6.1.

For $a\in H^1(K,\mu_n)=K^\times/K^{\times n}$, compatibility of local reciprocity with the cup-product definition of the local norm-residue symbol gives

$$
\exp\left(2\pi i\operatorname{inv}_v(c_v\smile a_v)\right)
=\chi_v(a).
$$

Multiplying over all places yields $1$, because $\chi$ is trivial on the principal idele $a$. Hence $\lambda((c_v))=0$. Theorem 6.1 supplies a unique global class

$$
c\in H^1(K,A_n)=\operatorname{Hom}_{\mathrm{cont}}(G_K,A_n)
$$

whose localization is every $c_v$. Let $L$ be the fixed field of $\ker c$, and let $\bar c:\operatorname{Gal}(L/K)\hookrightarrow A_n$ be the induced faithful additive character. The complex Galois character is

$$
\chi^{\mathrm{Gal}}=\jmath_n\circ\bar c:
\operatorname{Gal}(L/K)\longrightarrow\mathbf C^\times.
$$

The field $L/K$ is cyclic. The images of all decomposition groups generate
$\operatorname{Gal}(L/K)$: otherwise their generated subgroup would have a nontrivial fixed
field split at every completion, contrary to the separation argument of Section 4.2. Therefore
the common local restrictions generate both $\operatorname{im}c$ and
$\operatorname{im}\chi$, and $\jmath_n$ identifies these two images. In particular,
$[L:K]=|\operatorname{im}\chi|$. The product of the local restrictions of
$\chi^{\mathrm{Gal}}\circ\operatorname{Art}_{L/K}$ is $\chi$, so

$$
\chi=\chi^{\mathrm{Gal}}\circ\operatorname{Art}_{L/K}.
$$

Assuming TS, finite reciprocity for the constructed field gives

$$
\ker\chi=N_{L/K}C_L.
$$

We have proved the needed character form of existence:

**Lemma 6.2 (character existence) [FD,TS,TC].** Every continuous finite-order character of
$C_K$ comes from a unique intrinsic complex-valued finite-image character of
$G_K$. The auxiliary integer $n$, the embedding $\jmath_n$, and the corresponding
$A_n$-coordinate are choices in the construction; uniqueness of that coordinate
is asserted only after they are fixed. Its fixed field is cyclic of degree equal
to the order of its image. Assuming TS, its kernel is the idele-class norm
subgroup of that field.

When $\mu_n\subset K$, the dual sequence is self-dual after choosing a primitive $n$th root of unity. The construction then reduces to the familiar product of local Hilbert symbols and produces Kummer fields $K(\sqrt[n]{a})$. Without roots of unity, the dual module is genuinely $\mu_n$ and the cyclic field need not admit one radical equation over $K$. The formulation above retains the twisting automatically rather than hiding it in an informal descent.

### 6.4 Classification by open subgroups

**Theorem 6.3 (global existence in norm-subgroup form) [FD,TS,TC].** The
assignments

$$
L\longmapsto N_{L/K}C_L,
\qquad
H\longmapsto L_H
$$

give inverse inclusion-reversing bijections between finite abelian extensions $L/K$ inside $K^s$ and open finite-index subgroups $H\subseteq C_K$. Moreover

$$
C_K/H\xrightarrow{\sim}\operatorname{Gal}(L_H/K),
\qquad
[C_K:H]=[L_H:K].
$$

**Proof.** Starting with $H$, let $X=\operatorname{Hom}(C_K/H,\mathbf C^\times)$. By Lemma 6.2, each $\chi\in X$ cuts out a cyclic extension $L_\chi/K$. Let $L_H$ be their compositum. Its Galois group embeds in the product of the cyclic images and hence is abelian. An idele class acts trivially on $L_H$ exactly when it lies in every $\ker\chi$. Finite character duality gives

$$
\bigcap_{\chi\in X}\ker\chi=H.
$$

Conditional finite reciprocity now says $N_{L_H/K}C_{L_H}=H$. Conversely, an
abelian extension is recovered from its norm subgroup because the reciprocity
quotient recovers every automorphism, and the fixed field of its kernel is the
original field. Inclusion reversal and the index formula follow at once.
$\square$

The theorem is topological. Abstract finite-index subgroups that are not open are not classified. In the locally compact group $C_K$, the kernels of continuous finite quotients are exactly the open finite-index subgroups relevant to finite extensions.

For the remainder of the book, **[FD,TS,TC]** is understood on every assertion that uses
finite reciprocity or global existence: this includes the existence and maximality of ray
class fields, the Hilbert and cyclotomic class-field identifications, the inverse-limit Artin
isomorphism, and the passage between finite-order Hecke characters and finite-image Galois
characters. Statements that concern an already given extension and use only local
ramification or character algebra, such as Theorem 7.1, do not acquire this label merely by
appearing later.

## 7. Moduli and ray class fields

### 7.1 Why a modulus has a finite and an infinite part

A finite abelian extension is ramified at only finitely many places. At a finite place, ramification is measured by how deeply the local Artin map remains nontrivial on principal units. At a real place, the only possible ramification is complexification and is detected by sign. A **modulus** packages these two kinds of data:

$$
\mathfrak m=\mathfrak m_0\mathfrak m_\infty,
$$

where $\mathfrak m_0=\prod_{v<\infty}\mathfrak p_v^{n_v}$ is an integral ideal and $\mathfrak m_\infty$ is a set of real places. Complex places are never included.

Define the open subgroup of ideles

$$
U(\mathfrak m)=
\prod_{v\nmid\mathfrak m_0,\,v<\infty}\mathcal O_v^\times
\times\prod_{v\mid\mathfrak m_0}U_v^{n_v}
\times\prod_{v\in\mathfrak m_\infty}\mathbf R_{>0}
\times\prod_{v\mid\infty,\,v\notin\mathfrak m_\infty}K_v^\times.
$$

Its image in $C_K$ is open. The quotient

$$
\operatorname{Cl}_{\mathfrak m}(K)
=C_K/\operatorname{im}U(\mathfrak m)
\cong\mathbf I_K/K^\times U(\mathfrak m)
$$

is the **ray class group**. The image is already open and closed, so no extra topological closure is intended.

### 7.2 Ideal-theoretic ray classes

Let $I(\mathfrak m_0)$ be the group of fractional ideals prime to $\mathfrak m_0$. Let $P_{1,\mathfrak m}$ consist of principal ideals $(a)$ with

$$
a\equiv1\pmod{\mathfrak p_v^{n_v}}
\quad(v\mid\mathfrak m_0),
\qquad
a>0\quad(v\in\mathfrak m_\infty).
$$

The congruence is interpreted in $K_v^\times$: after choosing $a$ prime to $\mathfrak m_0$, it means $a\in1+\mathfrak p_v^{n_v}\mathcal O_v$. The valuation map on finite ideles induces

$$
\operatorname{Cl}_{\mathfrak m}(K)
\cong I(\mathfrak m_0)/P_{1,\mathfrak m}.
$$

Weak approximation moves every ray class to an idele trivial at the places dividing the modulus and at infinity, proving surjectivity. Its kernel is exactly the stated congruence-and-sign subgroup. This also proves finiteness, since the ray quotient fits into an exact sequence with the ordinary ideal class group and the finite groups $(\mathcal O_K/\mathfrak m_0)^\times$ and $\{\pm1\}^{|\mathfrak m_\infty|}$, modulo the image of global units.

When $\mathfrak m=(1)$ and no real place is included, this is the ordinary class group. When $\mathfrak m_0=(1)$ and all real places are included, it is the narrow class group. These coincide exactly when the needed sign patterns can be supplied by global units. For $K=\mathbf Q$, the unit $-1$ supplies its unique sign; in the real quadratic case $-1$ together with a unit of norm $-1$ supplies all four sign patterns, but one norm-$-1$ unit does not suffice in arbitrary higher degree.

### 7.3 Conductors of extensions and characters

For a finite abelian extension $L/K$, define the finite conductor exponent at $v$ to be the least $n_v\geq0$ with

$$
U_v^{n_v}\subseteq N_{L_w/K_v}(L_w^\times).
$$

It is $0$ exactly when $v$ is unramified, $1$ for nontrivial tame ramification, and at least $2$ for wild ramification. Include a real place in the conductor precisely when it becomes complex. The resulting modulus $\mathfrak f(L/K)$ is the **conductor**. Local compatibility gives

$$
U(\mathfrak f(L/K))\subseteq\ker\operatorname{Art}_{L/K}.
$$

It is the smallest modulus, ordered by divisibility and inclusion of real places, with this property.

For a finite-order idele class character $\chi$, its conductor is defined similarly: $n_v$ is the least integer for which $\chi_v(U_v^{n_v})=1$, and a real place occurs exactly when $\chi_v(-1)\ne1$. If $L/K$ is abelian, then

$$
\mathfrak f(L/K)=\operatorname{lcm}_{\chi\in\widehat{\operatorname{Gal}(L/K)}}\mathfrak f(\chi).
$$

This character formula follows because the intersection of all character kernels is trivial. It also makes roots of unity visible: global units, including torsion units, impose relations among local characters, so arbitrary local conductor data need not define a global character.

For a ramified one-dimensional local character, if $b_v$ is its largest upper-numbering break, then

$$
n_v=b_v+1.
$$

Indeed, local reciprocity sends $U_v^r$ onto the upper ramification group $D_w^r$, and the character becomes trivial at the first integer strictly beyond its last nontrivial break. The unramified convention is $n_v=0$. Thus a global ray-conductor bound is exactly an upper-break cutoff at each finite place, with the shift by one made explicit.

### 7.4 Existence and maximality of ray class fields

The image of $U(\mathfrak m)$ in $C_K$, equivalently
$K^\times U(\mathfrak m)/K^\times$, is open of finite index. The existence theorem therefore supplies a unique finite abelian extension $K_{\mathfrak m}/K$ such that

$$
\operatorname{Gal}(K_{\mathfrak m}/K)
\cong\operatorname{Cl}_{\mathfrak m}(K).
$$

It is the **ray class field of modulus $\mathfrak m$**. It is unramified outside the finite primes dividing $\mathfrak m_0$ and the real places in $\mathfrak m_\infty$, and its local conductor exponents are at most those of $\mathfrak m$.

It is maximal with this property: if $L/K$ is finite abelian and $\mathfrak f(L/K)\mid\mathfrak m$, then $U(\mathfrak m)$ lies in the Artin kernel for $L$, so

$$
N_{K_{\mathfrak m}/K}C_{K_{\mathfrak m}}
\subseteq N_{L/K}C_L.
$$

Inclusion reversal yields $L\subseteq K_{\mathfrak m}$. Conversely every subextension has conductor dividing $\mathfrak m$. Thus the ray class field is not merely one extension satisfying congruence restrictions; it contains all finite abelian extensions satisfying them.

The local subgroups are visible in the ray quotient itself. For a place $w$ of $K_{\mathfrak m}$ above a finite $v$, the image of $K_v^\times$ in $\operatorname{Cl}_{\mathfrak m}(K)$ is $D_w$, the image of $\mathcal O_v^\times$ is $I_w$, and the image of $U_v^r$ is the upper ramification group $D_w^r$. In particular, $v\nmid\mathfrak m_0$ has trivial inertia, while $U_v^{n_v}$ is killed when $\mathfrak p_v^{n_v}\mid\mathfrak m_0$. This is the exact local interface used when ray-group computations impose ramification cutoffs.

### 7.5 The ray exact sequence and the role of units

The finiteness proof becomes computational through the exact sequence

$$
\mathcal O_K^\times
\longrightarrow
(\mathcal O_K/\mathfrak m_0)^\times
\times\{\pm1\}^{\mathfrak m_\infty}
\longrightarrow
\operatorname{Cl}_{\mathfrak m}(K)
\longrightarrow
\operatorname{Cl}(K)
\longrightarrow1.
$$

The first map records residue classes and signs. The middle map chooses, by weak approximation, an element with the given residues and signs and sends the corresponding principal ideal, with its congruence defect retained, to a ray class. Two choices with the same residue and sign data have ray-trivial quotient and therefore define the same ray class. Global units instead describe the kernel of this middle map. Forgetting congruence and sign gives the last map, and its surjectivity follows by representing an ideal class with an ideal prime to $\mathfrak m_0$.

Exactness can be checked directly. A ray class maps trivially to $\operatorname{Cl}(K)$ exactly when it is represented by $(a)$. Its remaining information is the residue of $a$ modulo $\mathfrak m_0$ and its selected real signs. It is trivial as a ray class precisely when those data can be corrected to $(1,+)$ by a unit. Thus the units are not a nuisance quotient: they are the global compatibility among finite congruences and real signs.

For $K=\mathbf Q$, the unit group is $\{\pm1\}$. Including infinity prevents $-1$ from identifying opposite residue classes and gives $(\mathbf Z/m\mathbf Z)^\times$; omitting infinity permits that identification and gives the quotient by $\{\pm1\}$. For a field with positive unit rank, the image can be much larger and substantially reduce the ray class number.

### 7.6 The conductor--discriminant formula

The conductor records characters one at a time, whereas the discriminant records the extension as a whole. For an abelian extension they determine one another through a clean product.

**Theorem 7.1 (conductor--discriminant formula).** If $L/K$ is finite abelian with character group $X$, then the relative discriminant ideal satisfies

$$
\mathfrak d_{L/K}=\prod_{\chi\in X}\mathfrak f_0(\chi),
$$

where $\mathfrak f_0(\chi)$ is the finite part of the character conductor. The trivial character contributes the unit ideal.

**Proof.** It is enough to compare exponents at a finite place $v$. Let $D_i$ be the lower ramification groups of a completion $L_w/K_v$, beginning with inertia $D_0$. The different formula gives

$$
v_w(\mathfrak D_{L_w/K_v})=\sum_{i\geq0}(|D_i|-1).
$$

On the other hand, the Artin conductor is additive on direct sums. Restrict the regular representation of $G=\operatorname{Gal}(L/K)$ to the decomposition group $D=D_w$; it is $[G:D]$ copies of the regular representation of $D$. The latter has $|D|/|D_i|$ invariant vectors under $D_i$. Substitution in the Artin conductor formula, together with the residue-degree factor converting the different to its ideal norm, gives exactly $v(\mathfrak d_{L/K})$. Since $G$ is abelian, its regular representation is the direct sum of all characters in $X$. Additivity identifies the discriminant exponent with $\sum_{\chi\in X}a_v(\chi)$. Localizing and multiplying over $v$ proves the formula. $\square$

Infinite conductor places do not occur in the ideal $\mathfrak d_{L/K}$; they instead change the signature. Keeping the finite subscript in $\mathfrak f_0(\chi)$ prevents a real sign character from being mistaken for a prime-ideal factor.

## 8. Splitting laws and the Hilbert class field

### 8.1 Congruence becomes Frobenius

Let $L/K$ be abelian of conductor dividing $\mathfrak m$. For an ideal $\mathfrak a$ prime to $\mathfrak m_0$, choose an idele whose finite valuation divisor is $\mathfrak a$ and whose remaining components are $1$. The Artin map gives a surjective homomorphism

$$
I(\mathfrak m_0)\longrightarrow\operatorname{Gal}(L/K),
\qquad
\mathfrak p\longmapsto\operatorname{Frob}_{\mathfrak p}^{\mathrm{arith}}.
$$

Its kernel contains $P_{1,\mathfrak m}$, so it factors through the ray class group. For the full ray class field, this factor is an isomorphism.

Consequently a prime $\mathfrak p\nmid\mathfrak m_0$ splits completely in $K_{\mathfrak m}$ exactly when its ray class is trivial, equivalently when

$$
\mathfrak p=(a),\qquad
a\equiv1\pmod{\mathfrak m_0},\qquad
a>0\text{ at every place in }\mathfrak m_\infty.
$$

In a subfield $L$, complete splitting means that the ray class of $\mathfrak p$ lies in the subgroup corresponding to $L$. This is the precise bridge between congruence and decomposition.

### 8.2 The Hilbert class field

Take the trivial finite modulus and omit all real places. The corresponding field $H_K$ is the **Hilbert class field**. Its Galois group is the ordinary ideal class group:

$$
\operatorname{Gal}(H_K/K)\cong\operatorname{Cl}(K).
$$

It is the maximal finite abelian extension unramified at every finite place and in which every real place stays real. The last clause is sometimes expressed by saying “unramified also at infinity.” If one allows real places to become complex, the maximal abelian extension unramified at finite places is instead the narrow Hilbert class field, with Galois group $\operatorname{Cl}^+(K)$.

### 8.3 Imaginary and real quadratic examples

For an imaginary quadratic field $K$, there are no real places, so ordinary and narrow class fields coincide. If $\operatorname{Cl}(K)$ is cyclic of order $h$, then $H_K/K$ is cyclic of degree $h$. A prime ideal splits completely in $H_K$ exactly when it is principal.

Take $K=\mathbf Q(\sqrt{-5})$. Minkowski's bound says that every ideal class contains an integral ideal of norm at most

$$
\frac2\pi\sqrt{20}<3.
$$

Thus only a prime above $2$ can represent a nontrivial class. The ramified prime $\mathfrak p=(2,1+\sqrt{-5})$ has $\mathfrak p^2=(2)$, but it is not principal: an element of norm $2$ would give an integral solution of $a^2+5b^2=2$, which does not exist. Hence $\operatorname{Cl}(K)\cong\mathbf Z/2\mathbf Z$.

The Hilbert class field is

$$
H_K=K(\sqrt5)=\mathbf Q(i,\sqrt5).
$$

Indeed, the three quadratic subfields of this biquadratic field have discriminants $-4$, $5$, and $-20$, so

$$
|d_{H_K/\mathbf Q}|=(-4)(5)(-20)=400=|d_{K/\mathbf Q}|^2.
$$

The discriminant tower formula gives $N_{K/\mathbf Q}(\mathfrak d_{H_K/K})=1$, hence the relative discriminant is the unit ideal. Thus $H_K/K$ is quadratic and unramified at every finite place, and maximality identifies it with the Hilbert class field.

For a real quadratic field, ordinary and narrow class fields may differ. If there is a unit of norm $-1$, its two real signs differ and the sign map is large enough to identify ordinary and narrow classes. If no such unit exists, the narrow class number is twice the ordinary class number. The narrow Hilbert class field is then a quadratic extension of the ordinary Hilbert class field; it is unramified at finite places but complexifies the real embeddings. This example shows why “everywhere unramified” must specify whether infinite places count.

### 8.4 Cyclotomic fields as ray class fields

Over $\mathbf Q$, the ordinary class group is trivial, but ray class groups are not. For $m>2$, include the real place in the modulus $m\infty$. Then

$$
\operatorname{Cl}_{m\infty}(\mathbf Q)\cong(\mathbf Z/m\mathbf Z)^\times,
$$

and the ray class field is $\mathbf Q(\zeta_m)$. The positivity condition removes the ambiguity between a rational generator and its negative. If infinity is omitted, the quotient also identifies $a$ with $-a$ and the corresponding field is the maximal real subfield $\mathbf Q(\zeta_m)^+$, subject to the familiar small-modulus coincidences.

Here is the field identification rather than only a comparison of group orders. The extension $\mathbf Q(\zeta_m)/\mathbf Q$ is abelian, is unramified away from primes dividing $m$, and its local Artin map at a prime $p\mid m$ is trivial on $1+p^{v_p(m)}\mathbf Z_p$. Its real place complexifies, so its conductor divides $m\infty$. Ray-field maximality gives

$$
\mathbf Q(\zeta_m)\subseteq\mathbf Q_{m\infty}.
$$

The left degree is $\varphi(m)$, while the ray group calculation gives

$$
[\mathbf Q_{m\infty}:\mathbf Q]
=|(\mathbf Z/m\mathbf Z)^\times|=\varphi(m).
$$

The inclusion is therefore equality. If infinity is omitted, the same argument uses the quotient by $\{\pm1\}$ and the fixed field of complex conjugation. This proof also covers the cases $m\equiv2\pmod4$, where the written modulus need not be the minimal conductor.

This example recovers the congruence splitting law

$$
p\text{ splits completely in }\mathbf Q(\zeta_m)
\quad\Longleftrightarrow\quad p\equiv1\pmod m
$$

for $p\nmid m$. It also illustrates maximality: every abelian extension of $\mathbf Q$ occurs in a cyclotomic field, because every finite abelian extension has some conductor modulus and the corresponding ray class field is cyclotomic. This last conclusion is the Kronecker--Weber theorem as a consequence of global existence plus the explicit calculation of the rational ray fields.

### 8.5 Quadratic reciprocity as a product formula

For a quadratic extension $K(\sqrt d)/K$, the Artin character is the product of local quadratic Hilbert-symbol characters. Over $\mathbf Q$, at an odd prime $p\nmid2d$, its value on a uniformizer is the Legendre symbol

$$
\left(\frac d p\right).
$$

Thus splitting of $p$ in $\mathbf Q(\sqrt d)$ is detected by a congruence character whose modulus is the discriminant of the quadratic field, including the correct power of $2$ and the real sign when $d<0$.

The classical quadratic reciprocity law is the principal-idele relation in this example. For distinct odd primes $p,q$, apply the Hilbert product formula to $(p,q)_v$. All factors away from $2,p,q,\infty$ are one. The local computations give

$$
(p,q)_p=\left(\frac q p\right),
\qquad
(p,q)_q=\left(\frac p q\right),
$$

and

$$
(p,q)_2=(-1)^{\frac{p-1}{2}\frac{q-1}{2}},
\qquad
(p,q)_\infty=1.
$$

Their product is one, hence

$$
\left(\frac p q\right)\left(\frac q p\right)
=(-1)^{\frac{p-1}{2}\frac{q-1}{2}}.
$$

Taking one entry to be $-1$ or $2$ gives the supplementary laws. This calculation is the smallest nontrivial model of global reciprocity: every local factor is explicit, and the global theorem is exactly their product relation.

## 9. Norm principles and their limits

### 9.1 The knot between local and global norms

Let $L/K$ be finite. The obstruction to turning local norm preimages into one global preimage is measured by the **knot group**

$$
\mathfrak K(L/K)=
\frac{K^\times\cap N_{L/K}\mathbf I_L}{N_{L/K}L^\times}.
$$

The intersection is taken inside $\mathbf I_K$ using the diagonal copy of $K^\times$. Its numerator consists of elements that are norms in every completion; its denominator consists of actual field norms. Thus the Hasse norm principle for $L/K$ is exactly the assertion $\mathfrak K(L/K)=1$.

Reciprocity computes a different quotient,

$$
C_K/N C_L
=\mathbf I_K/K^\times N\mathbf I_L.
$$

The position of $K^\times$ has changed from an intersection in the numerator to a product in the denominator. No formal manipulation turns one quotient into the other. This is why the global norm theorem for idele classes does not settle the Hasse norm principle for arbitrary extensions.

### 9.2 The Hasse norm theorem for cyclic extensions

**Theorem 9.1 (Hasse norm theorem) [FD].** If $L/K$ is a cyclic extension of number fields and $a\in K^\times$, then

$$
a\in N_{L/K}L^\times
\quad\Longleftrightarrow\quad
a\in N_{L_w/K_v}L_w^\times
\text{ for every place }v.
$$

At a split place the local algebra is a product, and the displayed condition means norm from that product; equivalently one may choose any $w\mid v$ in the Galois case.

**Proof strategy.** A cyclic algebra converts a norm equation into a splitting question. Local norm hypotheses split the algebra at every completion; the Brauer invariant sequence then splits it globally.

**Proof.** Choose a generator $\sigma$ of $\operatorname{Gal}(L/K)$ and form $A=(L/K,\sigma,a)$. The cyclic-algebra criterion says

$$
A\text{ is split over }K
\quad\Longleftrightarrow\quad
a\in N_{L/K}L^\times.
$$

After extension to $K_v$, the algebra is the product-compatible cyclic algebra for $L\otimes_KK_v/K_v$. It is split if and only if $a$ is a local norm. Under the hypothesis, every localization $A_v$ is split. Injectivity in the Brauer invariant sequence forces $A$ to be split, so $a$ is a global norm. The converse is immediate by completion. $\square$

The proof includes ramified places, infinite places, and arbitrary cyclic degree. At a real place complexified in a quadratic extension, the local norm group is $\mathbf R_{>0}$; hence positivity there is a necessary part of the hypothesis.

### 9.3 Why cyclicity cannot be dropped

For a general Galois extension, there is no single cyclic algebra whose splitting is equivalent to being a norm. The obstruction group $\mathfrak K(L/K)$ can be nontrivial; already biquadratic extensions furnish examples. Under [FD,TS,TC], the precise cohomological relation, for $G=\operatorname{Gal}(L/K)$, is Pontryagin duality

$$
\mathfrak K(L/K)^\vee
\cong
\ker\left(H^3(G,\mathbf Z)\longrightarrow
\prod_v H^3(D_w,\mathbf Z)\right).
\tag{9.1}
$$

To derive it, apply Tate cohomology to

$$
1\longrightarrow L^\times\longrightarrow\mathbf I_L
\longrightarrow C_L\longrightarrow1.
$$

Hilbert 90 identifies the degree-one local terms, Shapiro changes the cohomology of $\mathbf I_L$ into the product of the cohomology of the decomposition groups, and the global fundamental class shifts the cohomology of $C_L$ by two degrees. The kernel measuring failure of a principal idele norm to be an element norm is then dual to the displayed localization kernel. Every arrow is the localization or norm arrow already used in the class-formation proof, so (9.1) is independent of choices of places.

This gives a concrete counterexample. Put

$$
L=\mathbf Q(\sqrt{13},\sqrt{17}).
$$

Its Galois group is $(\mathbf Z/2\mathbf Z)^2$. The quadratic discriminants are $13$, $17$, and $13\cdot17$, so only $13$ and $17$ can ramify. At every unramified prime the decomposition group is generated by one Frobenius element and is cyclic. At $13$, the congruence $17\equiv4\pmod {13}$ and Hensel's lemma show that $17$ is a square in $\mathbf Q_{13}$. At $17$, the congruence $8^2\equiv13\pmod {17}$ gives the corresponding square in $\mathbf Q_{17}$. At $2$, the criterion that an odd $2$-adic unit is a square exactly when it is $1$ modulo $8$ also shows directly that $17$ is a square in $\mathbf Q_2$. Both radicands are positive at infinity. Hence the local degree is at most two at every place where it is not already forced to be cyclic, proving the claim about decomposition groups.

For $G=(\mathbf Z/2\mathbf Z)^2$, the Kunneth calculation gives

$$
H^3(G,\mathbf Z)\cong\mathbf Z/2\mathbf Z,
$$

whereas $H^3(C,\mathbf Z)=0$ for every cyclic subgroup $C\subseteq G$. The kernel in (9.1) is therefore nonzero, so $\mathfrak K(L/\mathbf Q)$ has order two. In particular, some rational number is a norm from $L\otimes\mathbf Q_v$ at every place but is not a norm from $L$ itself. The cohomology proves existence of the element; no unsupported choice of a purported explicit norm is being made.

Thus cyclicity in Theorem 9.1 is essential. Even “finite abelian” is not enough. This counterexample also differs from the Grunwald--Wang issue: Wang concerns globalization of prescribed cyclic local characters in a special $2$-primary situation, while the present obstruction concerns an element norm from an already fixed biquadratic field.

### 9.4 Norm limitation, correctly stated

There are three safe limitation statements.

Under [FD,TS,TC], the first two limitation statements are available. For a finite
Galois extension $L/K$ with maximal abelian subextension $M/K$,

$$
N_{L/K}C_L=N_{M/K}C_M.
$$

Second, the resulting class index is

$$
[C_K:N_{L/K}C_L]=[M:K]=|\operatorname{Gal}(L/K)^{\mathrm{ab}}|.
$$

Independently of TS, at each completion local norm limitation gives

$$
N_{L_w/K_v}L_w^\times
=N_{M_w^{\mathrm{loc}}/K_v}(M_w^{\mathrm{loc}})^\times
$$

when the local extension is Galois and $M_w^{\mathrm{loc}}=L_w^{[D_w,D_w]}$ is its maximal abelian subextension. This local field need not be the completion of the global maximal abelian subextension $M=L^{[G,G]}$. These statements do not combine into a general equality of global element norm groups. The diagonal condition connecting the places is precisely where the knot group lives.

For a non-Galois extension there is no canonical “maximal abelian subextension” that controls its norm group. Passing to a Galois closure changes both the field norm and its degree. Any norm-limitation claim in that setting requires a separate hypothesis and proof.

## 10. Infinite reciprocity

### 10.1 Passing over all finite abelian extensions

Let $K^{\mathrm{ab}}$ be the compositum of all finite abelian extensions of $K$. Compatibility under restriction lets the finite Artin maps assemble into

$$
\operatorname{Art}_K:C_K\longrightarrow
\operatorname{Gal}(K^{\mathrm{ab}}/K).
$$

For every finite abelian $L/K$, composition with restriction to $L$ is $\operatorname{Art}_{L/K}$. The map is continuous because every finite quotient is continuous.

The natural topology on the target is profinite. The relevant topology on $C_K$ is therefore not its full locally compact topology but the topology generated by open finite-index subgroups. Its profinite completion is

$$
\widehat{C_K}=\varprojlim_H C_K/H,
$$

where $H$ runs over open finite-index subgroups. Finite reciprocity and existence identify the same inverse system with the finite Galois quotients of $K^{\mathrm{ab}}/K$.

**Theorem 10.1 (infinite reciprocity) [FD,TS,TC].** Global Artin reciprocity induces an isomorphism

$$
\widehat{C_K}\xrightarrow{\sim}
\operatorname{Gal}(K^{\mathrm{ab}}/K).
$$

This follows directly by taking inverse limits of the conditional finite
isomorphisms. Unlike a bare inverse-limit assertion, it also records which
topology is being completed.

### 10.2 The connected component of the idele class group

Let $C_K^0$ be the identity component. Every continuous map from a connected group to a finite discrete group is trivial, so $C_K^0$ lies in every open finite-index subgroup. Conversely, choose one archimedean coordinate and a continuous positive one-parameter subgroup on which the idele module is the identity. It splits the exact sequence

$$
1\longrightarrow C_K^1\longrightarrow C_K
\xrightarrow{|\cdot|}\mathbf R_{>0}\longrightarrow1.
$$

Thus $C_K$ is topologically a product of the compact group $C_K^1$ and the connected group $\mathbf R_{>0}$. The latter lies in $C_K^0$, so $C_K/C_K^0$ is a quotient of $C_K^1$ and is compact. The quotient of a locally compact group by its identity component is totally disconnected. A compact totally disconnected group is profinite, because its open normal subgroups form a neighborhood basis at the identity.

This proves the converse containment in the kernel of completion. If $c\notin C_K^0$, its image in the profinite group $C_K/C_K^0$ is nontrivial. Some finite continuous quotient of that profinite group detects it. Pulling the kernel back to $C_K$ gives an open finite-index subgroup that does not contain $c$. Therefore

$$
\bigcap_{H\subset C_K\text{ open, finite index}}H=C_K^0.
$$

Moreover, a compact profinite group is already complete for the topology of its finite quotients. The map from $C_K/C_K^0$ to $\widehat{C_K}$ has dense image because the completion map does, and its image is closed because its source is compact. It is therefore onto; the intersection formula makes it injective. Hence it is an isomorphism, not merely a dense embedding.

Combining this identification with Theorem 10.1 gives

$$
\ker\operatorname{Art}_K=C_K^0
$$

and that the map $C_K\to\operatorname{Gal}(K^{\mathrm{ab}}/K)$ is surjective. Thus

$$
C_K/C_K^0\xrightarrow{\sim}\operatorname{Gal}(K^{\mathrm{ab}}/K)
$$

as topological groups.

This differs from the local nonarchimedean situation. There, $K_v^\times\to G_{K_v}^{\mathrm{ab}}$ has dense image but is generally not surjective before completion, because the valuation copy of $\mathbf Z$ maps densely to $\widehat{\mathbf Z}$. Globally, the idele class group contains enough compact directions that quotienting by its identity component already yields the complete profinite group.

Thus the three frequently quoted formulations have different scopes. The map $C_K\to G_K^{\mathrm{ab}}$ is surjective with kernel $C_K^0$; the induced map on profinite completions is an isomorphism; and each local subgroup $K_v^\times$ generally has only dense image in its own infinite local abelian Galois group. Replacing one statement by another loses essential topology.

### 10.3 Infinite decomposition groups

For each place $v$, the embedding $K_v^\times\to C_K$ followed by infinite reciprocity agrees with local reciprocity and the map induced by a decomposition-group embedding:

$$
\begin{array}{ccc}
K_v^\times&\xrightarrow{\operatorname{rec}_{K_v}}&G_{K_v}^{\mathrm{ab}}\\
\downarrow&&\downarrow\\
C_K&\xrightarrow{\operatorname{Art}_K}&G_K^{\mathrm{ab}}.
\end{array}
$$

The right vertical map depends on an embedding $K^s\hookrightarrow K_v^s$, but changing it conjugates the decomposition group; conjugation disappears after abelianization. Units map to global inertia, and a finite-place uniformizer maps to arithmetic Frobenius in the maximal unramified quotient.

This compatibility is stronger than matching Frobenius at almost all primes. It controls ramification at every finite prime, the complexification of real places, and the behavior of characters under restriction to a completion.

### 10.4 Kronecker--Weber revisited

For $K=\mathbf Q$, calculation of rational ray class fields gives

$$
\mathbf Q^{\mathrm{ab}}=\bigcup_{m\geq1}\mathbf Q(\zeta_m).
$$

On Galois groups,

$$
\operatorname{Gal}(\mathbf Q^{\mathrm{ab}}/\mathbf Q)
\cong\varprojlim_m(\mathbf Z/m\mathbf Z)^\times
=\widehat{\mathbf Z}^{\times}.
$$

The archimedean sign is not an extra missing factor: complex conjugation corresponds to $-1\in\widehat{\mathbf Z}^{\times}$. The positive real component of $C_{\mathbf Q}$ lies in the kernel, exactly as Theorem 10.1 predicts.

For a general number field no comparably elementary family such as roots of unity generates every abelian extension. Ray class fields, indexed by all moduli, are the correct replacement:

$$
K^{\mathrm{ab}}=\bigcup_{\mathfrak m}K_{\mathfrak m}.
$$

Every finite abelian extension is contained in the ray class field of its conductor modulus.

## 11. Hecke characters

### 11.1 Adelic characters and their local factors

A **Hecke character** of $K$ is a continuous homomorphism

$$
\chi:C_K\longrightarrow\mathbf C^\times.
$$

Equivalently, it is a continuous character of $\mathbf I_K$ trivial on diagonally embedded $K^\times$. Restriction to the $v$-coordinate gives a local character $\chi_v:K_v^\times\to\mathbf C^\times$, and

$$
\chi(x)=\prod_v\chi_v(x_v).
$$

For a given idele, almost all factors are $1$. More precisely, continuity makes $\chi_v$ unramified for almost all finite $v$, meaning trivial on $\mathcal O_v^\times$. The value

$$
\alpha_v=\chi_v(\pi_v)
$$

is then independent of the choice of uniformizer and is the unramified parameter. Whenever $\chi$ has a finite-order or $\ell$-adic Galois avatar, arithmetic reciprocity identifies this with its value on arithmetic Frobenius. Under geometric normalization it would be the inverse Frobenius value.

The condition of being trivial on $K^\times$ is global and strong. One cannot choose the $\chi_v$ independently: for every $a\in K^\times$,

$$
\prod_v\chi_v(a)=1.
$$

Roots of unity give immediate constraints. If $\zeta\in\mu(K)$, the product of the local values on $\zeta$ must be one. Such constraints account for many apparent failures when one tries to prescribe local characters by inspection.

### 11.2 Finite-order characters and Galois characters

If $\chi$ has finite order, its kernel is open of finite index. Global existence supplies a finite abelian extension $L/K$, and finite reciprocity gives a unique character

$$
\chi^{\mathrm{Gal}}:\operatorname{Gal}(L/K)\longrightarrow\mathbf C^\times
$$

such that

$$
\chi=\chi^{\mathrm{Gal}}\circ\operatorname{Art}_{L/K}.
$$

Passing to the inverse limit yields a natural bijection

$$
\operatorname{Hom}_{\mathrm{cont}}(G_K,\mathbf C^\times)_{\mathrm{finite\ image}}
\cong
\operatorname{Hom}_{\mathrm{cont}}(C_K,\mathbf C^\times)_{\mathrm{finite\ order}}.
$$

In fact every continuous character from a profinite group to $\mathbf C^\times$ has finite image. Its image is compact, hence lies in the unit circle; a compact totally disconnected quotient of a profinite group cannot be the whole circle, and every proper closed subgroup of the circle is finite cyclic. Thus the finite-image label on the Galois side is automatic for complex characters with the usual topology. It ceases to be automatic for $\ell$-adic targets, which contain infinite profinite subgroups such as $1+\ell\mathbf Z_\ell$.

For finite-order $\chi$, the conductor defined in Chapter 7 is exactly the Artin conductor of its one-dimensional Galois character. At a finite $v$,

$$
a_v(\chi)=\min\{n\geq0:\chi_v(U_v^n)=1\}.
$$

The equality follows from local reciprocity and the upper ramification filtration. Hence conductor computations can be made entirely with local multiplicative characters.

### 11.3 Quasicharacters and the module direction

Not every Hecke character has finite order. The idele module gives the basic family

$$
x\longmapsto |x|^s
\qquad(s\in\mathbf C),
$$

where $t^s=e^{s\log t}$ for $t>0$. These characters are trivial on $K^\times$ by the product formula. A unitary Hecke character has image in the unit circle. Since $C_K^1$ is compact, the positive character $|\chi|$ is trivial there and hence factors through the idele module. Consequently a general character has a unique decomposition

$$
\chi=\chi_0|\cdot|^\sigma
$$

with $\chi_0$ unitary and $\sigma\in\mathbf R$. Here $|\cdot|$ is the module descended from $|\cdot|_{\mathbf A_K}$. The imaginary character $|\cdot|^{it}$ remains part of $\chi_0$. If instead one requires the residual character to be trivial on a chosen positive module section, then the corresponding complex exponent $s=\sigma+it$ is unique for that section.

At an archimedean place, every continuous character has an explicit form. On $\mathbf R^\times$ it is

$$
x\longmapsto\operatorname{sgn}(x)^\epsilon |x|^s,
\qquad \epsilon\in\{0,1\},\ s\in\mathbf C,
$$

and on $\mathbf C^\times$ it is

$$
z\longmapsto\left(\frac z{|z|}\right)^m|z|^{2s},
\qquad m\in\mathbf Z,\ s\in\mathbf C.
$$

The square on the complex absolute value matches the normalized adelic convention. These continuous parameters have no direct finite Galois analogue; finite Galois characters see only the component group at real places and nothing at complex places.

### 11.4 Algebraic infinity types

Fix the set $\Sigma_K$ of embeddings $\tau:K\hookrightarrow\mathbf C$. A Hecke character is **algebraic** if there are integers $n_\tau$ such that on the identity component of $K_\infty^\times$ its archimedean component is

$$
\chi_\infty(x)=\prod_{\tau\in\Sigma_K}\tau(x)^{-n_\tau}.
$$

For a complex conjugate pair this means $z^{-p}\bar z^{-q}$ with integers $p,q$; for a real embedding it means $x^{-n}$ on $\mathbf R_{>0}$, with a separately chosen sign character on $\mathbf R^\times/\mathbf R_{>0}$. The tuple $(n_\tau)$ is the **infinity type**.

The character is of type $A_0$ when there is an integer $w$ with

$$
n_\tau+n_{\bar\tau}=w
$$

for every complex pair, with the analogous $2n_\tau=w$ at real embeddings after the chosen normalization. This purity condition is stronger than algebraicity. It is the form naturally compatible with pure one-dimensional arithmetic representations; it should not be inserted into the definition of every continuous Hecke character.

Global units restrict possible infinity types. Since $\chi$ is trivial on $K^\times$, its algebraic archimedean value on a global unit must be cancelled by a finite-order value from the finite places. On a sufficiently deep congruence subgroup of units the finite part is trivial, so

$$
\prod_\tau\tau(u)^{n_\tau}=1.
$$

Dirichlet's unit theorem translates these equations into linear relations among the $n_\tau$. For fields with a real embedding, they force parallel behavior after removal of a norm power; CM fields allow the richer pairs $(p,q)$ used in theta series and automorphic induction.

### 11.5 The ell-adic avatar

Before passing from a global Hecke character to Galois, we isolate the elementary
local-algebraicity condition used in this book. Let
$L/\mathbf Q_\ell$ and $E/\mathbf Q_\ell$ be finite extensions, enlarging $E$ so that it
contains the images of all embeddings
$\tau:L\hookrightarrow\overline{\mathbf Q}_\ell$. A continuous character

$$
\xi:G_L\longrightarrow E^\times
$$

is **locally algebraic** when, under arithmetic local reciprocity, there are integers $n_\tau$
and an open subgroup $U\subseteq\mathcal O_L^\times$ on which

$$
\xi(\operatorname{rec}_L(u))
=\prod_{\tau:L\hookrightarrow E}\tau(u)^{n_\tau}.
$$

Changing arithmetic to geometric reciprocity changes every $n_\tau$ by a sign; it does not
change the condition. A finite-order or unramified factor is invisible on a sufficiently small
$U$ and is therefore allowed.

The condition has a completely elementary infinitesimal test.

**Proposition 11.1 (logarithmic criterion for local algebraicity).** After replacing the
principal-unit group by a sufficiently deep open subgroup, there are unique scalars
$c_\tau\in E$ such that

$$
\log\bigl(\xi(\operatorname{rec}_L(\exp x))\bigr)
=\sum_{\tau:L\hookrightarrow E}c_\tau\tau(x).             \tag{11.1a}
$$

The character $\xi$ is locally algebraic if and only if every $c_\tau$ is an integer.
In that case the integers $c_\tau$ are exactly the exponents in the defining formula,
with their signs reversed if geometric rather than arithmetic reciprocity is used.

**Proof.** Continuity lets us choose $r,s$ such that
$\exp:\mathfrak p_L^r\to1+\mathfrak p_L^r$ and
$\log:1+\mathfrak p_E^s\to\mathfrak p_E^s$ are mutually inverse and $\xi$ carries the
first group into the second. The left side of (11.1a) is then a continuous homomorphism
from the additive group $\mathfrak p_L^r$ to $E$. For $a\in\mathbf Z_\ell$ it satisfies
$f(ax)=af(x)$ first for integers and then, by density and continuity, for every $a$; after
division by a power of $\ell$ it extends uniquely to a $\mathbf Q_\ell$-linear map
$f:L\to E$.

Because $L/\mathbf Q_\ell$ is separable and $E$ contains the images of all embeddings, the
Dedekind independence lemma says that the embeddings $\tau:L\hookrightarrow E$ are
linearly independent. Their number is $[L:\mathbf Q_\ell]$, the dimension of
$\operatorname {Hom}_{\mathbf Q_\ell}(L,E)$ over $E$, so they form a basis. This proves
existence and uniqueness of the $c_\tau$.

If $\xi$ is locally algebraic, applying logarithm to its defining formula gives
$c_\tau=n_\tau\in\mathbf Z$. Conversely suppose the $c_\tau$ are integers and divide
$\xi\circ\operatorname {rec}_L$ by $u\mapsto\prod_\tau\tau(u)^{c_\tau}$. Its logarithm
vanishes on a sufficiently deep principal-unit group. The logarithm is injective there,
so the quotient itself is one. This is precisely local algebraicity. $\square$

Coefficient extension causes no ambiguity. If $E$ initially omits some embeddings, test
the criterion after one finite extension containing them. Linear independence shows that
the resulting exponent tuple is independent of the chosen enlargement. Period-theoretic
notions are not used in this book; relating this elementary criterion to such notions
belongs only after their period rings and comparison functors have been constructed.

Choose an isomorphism $\iota:\overline{\mathbf Q}\hookrightarrow\overline{\mathbf Q}_\ell$. An algebraic Hecke character whose finite values are algebraic has an $\ell$-adic avatar. On finite ideles, transport its algebraic values through $\iota$ and correct at the places above $\ell$ by the algebraic infinity type. Explicitly, for $x_f\in\mathbf A_{K,f}^\times$, put

$$
\chi_\ell(x_f)=
\iota(\chi_f(x_f))
\prod_{\tau\in\Sigma_K}
(\iota\circ\tau)(x_{v(\tau)})^{-n_\tau},
$$

where $v(\tau)$ is the $\ell$-adic place induced by $\iota\circ\tau$ and the product is interpreted through the corresponding embeddings $K_{v(\tau)}\hookrightarrow\overline{\mathbf Q}_\ell$. The correction makes $\chi_\ell$ trivial on $K^\times$; algebraicity is exactly what makes the exponents integral and the character locally algebraic at $v\mid\ell$.

Infinite reciprocity then gives a continuous character

$$
\rho_{\chi,\ell}:G_K^{\mathrm{ab}}\longrightarrow
\overline{\mathbf Q}_\ell^\times.
$$

For $v\nmid\ell\mathfrak f(\chi)$,

$$
\rho_{\chi,\ell}(\operatorname{Frob}_v^{\mathrm{arith}})
=\iota(\chi_v(\pi_v)),
$$

with the correction factor absent away from $\ell$.

Conversely, let

$$
\rho:G_K\longrightarrow\overline{\mathbf Q}_\ell^\times
$$

be continuous, unramified outside finitely many places, and locally algebraic at every $v\mid\ell$. Compose $\rho$ with global reciprocity. At a place above $\ell$, local algebraicity writes its restriction on an open subgroup of units as a product of integral powers of the embeddings $K_v\hookrightarrow\overline{\mathbf Q}_\ell$. Divide by those algebraic factors. At $v\nmid\ell$, continuity and finite ramification make the residual character trivial on some $U_v^{n_v}$, and it is trivial on $\mathcal O_v^\times$ for almost every $v$. The principal-idèle relation for $\rho\circ\operatorname{Art}_K$ gives exactly the unit relations needed for the chosen integral exponents. The residual character therefore factors through one finite ray class group and has finite image. Transport that finite character through $\iota^{-1}$ and restore the archimedean monomial. This constructs an algebraic Hecke character whose avatar is $\rho$.

Thus a continuous one-dimensional $\ell$-adic Galois character comes from an algebraic Hecke character precisely under these two conditions. Arbitrary continuous $\ell$-adic characters can fail either one. The assertion also depends on the chosen $\iota$, although its compatible algebraic data do not.

For finite-order characters all $n_\tau$ are zero, the correction disappears, and this construction reduces to the finite reciprocity dictionary. Under our arithmetic Artin convention, the adelic module character $|\cdot|$ takes a prime uniformizer to $q_v^{-1}$ and therefore corresponds to the inverse of the $\ell$-adic cyclotomic character; $|\cdot|^{-1}$ corresponds to the cyclotomic character itself.

### 11.6 Norms, restriction, and conjugation of characters

Let $M/K$ be finite. If $\chi$ is a Hecke character of $K$, then

$$
\chi_M=\chi\circ N_{M/K}:C_M\longrightarrow\mathbf C^\times
$$

corresponds on the Galois side to restriction from $G_K$ to $G_M$. Its local component at $w\mid v$ is $\chi_v\circ N_{M_w/K_v}$, and its conductor is bounded by the local conductor-discriminant transformation; equality need not hold under ramified base change.

The exact local statement behind that bound is

$$
a_w(\chi\circ N_{M/K})
=\min\left\{r\geq0:
N_{M_w/K_v}(U_w^r)\subseteq\ker\chi_v\right\}.
$$

For an unramified local extension, norms are onto on every unit layer and this equals $a_v(\chi)$. In a ramified extension, the Herbrand norm theorem converts the displayed minimum into the corresponding upper-numbering bound; cancellation can make a naive equality false.

If $M/K$ is Galois and $\theta$ is a character of $C_M$, define

$$
\theta^\sigma(x)=\theta(\sigma^{-1}x)
\qquad(\sigma\in\operatorname{Gal}(M/K)).
$$

The stabilizer of $\theta$ measures descent. The exact quadratic induction, conductor, and Frobenius formulas are recorded in Section 11.8.

### 11.7 Dirichlet and CM character models

Over $\mathbf Q$, a finite-order Hecke character of conductor dividing $m\infty$ is the same as a Dirichlet character

$$
\psi:(\mathbf Z/m\mathbf Z)^\times\longrightarrow\mathbf C^\times.
$$

At a prime $p\nmid m$, its local value on $p$ is $\psi(p)$. The real local component satisfies

$$
\chi_\infty(-1)=\psi(-1),
$$

because the principal idele $-1$ must have total value one; depending on whether one defines the finite component using an inverse residue convention, both displayed values are inverted together. With the ideal convention of this book, arithmetic Frobenius has eigenvalue $\psi(p)$. Primitivity of the Dirichlet character is exactly minimality of the conductor modulus. The associated Galois character factors through $\mathbf Q(\zeta_m)$ and sends arithmetic Frobenius at $p$ to $\psi(p)$.

An imaginary quadratic field $M/\mathbf Q$ supplies the first genuinely nonparallel algebraic examples. Choose integers $p,q$ and a finite conductor $\mathfrak f$. A character on ideals prime to $\mathfrak f$ has infinity type $(p,q)$ when, for every principal ideal $(a)$ with $a\equiv1\pmod{\mathfrak f}$,

$$
\theta((a))=a^p\bar a^q.
$$

This rule is well defined only if every unit congruent to $1$ modulo $\mathfrak f$ satisfies $u^p\bar u^q=1$. Since the unit group of an imaginary quadratic field is finite, enlarging $\mathfrak f$ removes the obstruction. Extending from principal ray ideals to all ray ideals amounts to extending a character from a subgroup of a finite abelian ray class group, which is always possible because $\mathbf C^\times$ is divisible. The resulting ideal character is the finite description of an algebraic Hecke character whose adelic infinity component is $z^{-p}\bar z^{-q}$.

If $p\ne q$, complex conjugation changes the infinity type and therefore $\theta\ne\theta^\sigma$. Its $\ell$-adic avatar and its conjugate are distinct, so induction from $G_M$ to $G_{\mathbf Q}$ is irreducible. If $p=q$ and the finite part is conjugation-invariant, the character is the norm pullback of either of two extensions to $\mathbf Q$, and induction is reducible. These two models explain why finite ray characters and algebraic infinity types are both needed in later dihedral constructions.

### 11.8 The quadratic induction interface

Let $M/K$ be quadratic, let $s$ denote its nontrivial automorphism, and let $\theta$ be a finite-order or algebraic Hecke character of $M$. Fix an $\ell$-adic avatar $\theta_\ell$, which exists automatically in the finite-order case. Put

$$
\rho=\operatorname{Ind}_{G_M}^{G_K}\theta_\ell.
$$

Restriction to $G_M$ and the index-two coset decomposition give

$$
\rho|_{G_M}\cong\theta_\ell\oplus\theta_\ell^s.
\tag{11.1}
$$

If the two characters in (11.1) are distinct, their two eigenspaces are the only $G_M$-stable lines and an element outside $G_M$ exchanges them; hence no line is $G_K$-stable and $\rho$ is irreducible. If they are equal, choose a lift $t\in G_K\setminus G_M$. An extension of $\theta_\ell$ to $G_K$ is obtained by choosing a square root of $\theta_\ell(t^2)$ for its value at $t$. There are exactly two choices, differing by the quadratic character $\varepsilon_{M/K}$, and

$$
\rho\cong\widetilde\theta_\ell
\oplus\widetilde\theta_\ell\varepsilon_{M/K}.
\tag{11.2}
$$

This proves both the irreducibility criterion and the descent assertion; no unstated extension obstruction remains over the algebraically closed coefficient field.

For a finite-order $\theta$, the representation $\rho$ has finite image, so its Artin conductor
is defined at every finite place. For an algebraic $\theta$, the raw $\ell$-adic avatar includes
the locally algebraic correction at places above $\ell$ and can have infinite inertia there; in
that case we assert the Artin-conductor formula only away from $\ell$. If
$\mathfrak a^{(\ell)}$ denotes the part of an ideal prime to the places above $\ell$, put

$$
\mathfrak f_0^{(\ell)}(\rho)
=\prod_{v\nmid\ell}\mathfrak p_v^{a_v(\rho)}.
$$

The precise statement is

$$
\begin{aligned}
\mathfrak f_0(\rho)
&=\mathfrak d_{M/K}\,
N_{M/K}\bigl(\mathfrak f_0(\theta)\bigr)
&&\text{if }\theta\text{ has finite order},\\
\mathfrak f_0^{(\ell)}(\rho)
&=\left(
\mathfrak d_{M/K}\,
N_{M/K}\bigl(\mathfrak f_0(\theta)\bigr)
\right)^{(\ell)}
&&\text{for algebraic }\theta.
\end{aligned}
\tag{11.3}
$$

Indeed, at every $v$ in the first case, and at every $v\nmid\ell$ in the second, the local induction formula from the ramification theory gives

$$
a_v(\rho)
=\sum_{w\mid v}f(w/v)a_w(\theta)
+v(\mathfrak d_{M/K}).
$$

The first term is the exponent of the normed conductor, and the second is the discriminant exponent. This includes split, inert, tame, and wild places.

There are equally explicit unramified Euler factors. Assume that $\rho$ is unramified at $v$;
for an algebraic character of nonfinite order, assume in particular that $v\nmid\ell$. If
$v=ww^s$ splits and neither local character is ramified, then

$$
\det\!\left(X-\rho(\operatorname{Frob}_v^{\mathrm{arith}})\right)
=
\bigl(X-\theta_\ell(\operatorname{Frob}_w^{\mathrm{arith}})\bigr)
\bigl(X-\theta_\ell(\operatorname{Frob}_{w^s}^{\mathrm{arith}})\bigr).
\tag{11.4}
$$

If $v$ is inert and unramified, then $\operatorname{Frob}_v^{\mathrm{arith}}\notin G_M$ and its square is $\operatorname{Frob}_w^{\mathrm{arith}}$. In the two coset basis it acts off-diagonally, so

$$
\operatorname{tr}\rho(\operatorname{Frob}_v^{\mathrm{arith}})=0,
\qquad
\det\!\left(X-\rho(\operatorname{Frob}_v^{\mathrm{arith}})\right)
=X^2-\theta_\ell(\operatorname{Frob}_w^{\mathrm{arith}}).
\tag{11.5}
$$

Finally, norm pullback and Galois restriction agree:

$$
\eta\circ N_{M/K}
\quad\longleftrightarrow\quad
\eta_\ell|_{G_M}.
\tag{11.6}
$$

Such a character is $s$-invariant. Conversely, an $s$-invariant finite-order character, or an $s$-invariant algebraic avatar, has the two extensions just constructed; on the Hecke side these are the two characters of $K$ whose norm pullback is $\theta$.

Two further identities prevent the norm and diagonal maps from being confused. If $\eta$ is a character of $K$, then

$$
\operatorname{Ind}_{G_M}^{G_K}
\bigl(\theta_\ell\cdot(\eta_\ell|_{G_M})\bigr)
\cong \rho\otimes\eta_\ell.
\tag{11.7}
$$

On the other hand, the determinant uses the diagonal inclusion $C_K\to C_M$, or equivalently transfer on Galois groups:

$$
\det\rho
\quad\longleftrightarrow\quad
\varepsilon_{M/K}\,\theta|_{C_K}.
\tag{11.8}
$$

For an element of $G_M$, this follows from the two diagonal entries $\theta_\ell$ and $\theta_\ell^s$; for an element in the other coset, the induction matrix has determinant $-\theta_\ell(t^2)$, producing the quadratic sign. Together, equations (11.1)--(11.8) are the precise global interface needed for quadratic dihedral induction.

### 11.9 Induction through a general finite extension

Quadratic induction is the most visible case, but norm and induction must remain compatible in arbitrary degree. Let $M/K$ be finite separable of degree $d$, let $\theta$ be a finite-order or algebraic Hecke character of $M$, and let $\theta_\ell$ be its avatar. Put

$$
R=\operatorname{Ind}_{G_M}^{G_K}\theta_\ell.
$$

This is a $d$-dimensional representation. Its definition uses a coset basis, but its isomorphism class and all formulas below do not.

Norm pullback is Galois restriction:

$$
\eta\circ N_{M/K}
\quad\longleftrightarrow\quad
\eta_\ell|_{G_M}.
\tag{11.9}
$$

The tensor identity for induction therefore becomes

$$
\operatorname{Ind}_{G_M}^{G_K}
\bigl(\theta_\ell\cdot\eta_\ell|_{G_M}\bigr)
\cong R\otimes\eta_\ell.
\tag{11.10}
$$

On the Hecke side, the character inside the induction is $\theta(\eta\circ N_{M/K})$. This is why norms, rather than diagonal inclusions, occur when a twist is pulled from the base field.

If $M/K$ is Galois with group $\Gamma$, Mackey decomposition gives

$$
R|_{G_M}\cong
\bigoplus_{\sigma\in\Gamma}\theta_\ell^\sigma.
\tag{11.11}
$$

Indeed, the cosets of $G_M$ in $G_K$ are indexed by $\Gamma$, and the $\sigma$-coset line is acted on through $\theta_\ell^\sigma$. The intertwining calculation gives

$$
\dim\operatorname{End}_{G_K}(R)
=|\{\sigma\in\Gamma:\theta_\ell^\sigma=\theta_\ell\}|.
$$

It follows that

$$
R\text{ is irreducible}
\quad\Longleftrightarrow\quad
\theta_\ell^\sigma\ne\theta_\ell
\text{ for every }1\ne\sigma\in\Gamma.
\tag{11.12}
$$

Here is the irreducibility argument, including the converse implicit in the endomorphism count. If all conjugates are distinct, finitely many commuting diagonal actions of $G_M$ separate the coset lines. Interpolation in their eigenvalues produces the projector onto each line. Hence every $G_M$-stable subspace is a sum of coset lines. Since $G_K$ permutes those lines transitively, a $G_K$-stable sum is either zero or all of $R$.

Conversely, put

$$
\Gamma_\theta
=\{\sigma\in\Gamma:\theta_\ell^\sigma=\theta_\ell\}.
$$

If $\Gamma_\theta$ is nontrivial, induction from $G_M$ to its inverse image in $G_K$ is the regular module of a twisted group algebra of $\Gamma_\theta$. In characteristic zero that finite-dimensional algebra is semisimple, and its regular module has a proper simple summand when $\Gamma_\theta\ne1$. Inducing that summand to $G_K$ gives a proper summand of $R$. This proves (11.12).

The argument does not require $\theta_\ell$ to have finite image: the twisted group algebra comes from the finite stabilizer quotient, while a nonzero intertwiner between two one-dimensional characters exists exactly when the characters agree. When the stabilizer is nontrivial, induction is analyzed in stages through its fixed field; a quadratic two-summand formula does not extend unchanged to a larger stabilizer.

The determinant uses the other idele map. Let

$$
j_{M/K}:C_K\longrightarrow C_M
$$

be diagonal scalar extension, and let

$$
\delta_{M/K}=\det\operatorname{Ind}_{G_M}^{G_K}\mathbf 1.
$$

The latter is the quadratic Galois character, possibly trivial, given by the sign of the permutation action on the $d$ embeddings of $M$; we use the same symbol for its finite-order Hecke character under reciprocity. Then

$$
\det R
\quad\longleftrightarrow\quad
\delta_{M/K}\,\bigl(\theta\circ j_{M/K}\bigr).
\tag{11.13}
$$

To prove this, choose right coset representatives. An element $g\in G_K$ permutes the coset basis, contributing its permutation sign. The product of the nonzero matrix entries is $\theta_\ell(\operatorname{Ver}_{M/K}g)$ by the coset formula for transfer. Reciprocity identifies transfer with $j_{M/K}$. In degree two, $\delta_{M/K}=\varepsilon_{M/K}$ and this is (11.8). Thus determinants use diagonal inclusion and transfer, whereas twist pullbacks use norm and restriction.

Use the conductor convention of Section 11.8: all finite places are included when $\theta$ has
finite order, while only $v\nmid\ell$ is asserted for a general algebraic $\theta$. At every
place in that range, the local induction formula gives

$$
a_v(R)=v(\mathfrak d_{M/K})
+\sum_{w\mid v}f(w/v)a_w(\theta).
\tag{11.14}
$$

Here $a_w(\theta)$ is the conductor exponent of the finite local component of the Hecke character; in the stated range it is also the Artin conductor of the avatar. To prove the formula, pass to a common finite Galois extension on which the relevant inertia characters factor and use

$$
a(V)=\sum_{i\geq0}\frac{|G_i|}{|G_0|}
\operatorname{codim}V^{G_i}.
$$

For the induced coset representation, double-count the pairs consisting of a ramification element and a coset it fixes. The contribution with trivial character is the conductor of the permutation representation, which is the discriminant exponent. On the orbit belonging to $w$, the remaining character contribution is $f(w/v)a_w(\theta)$ after Herbrand reindexing. This proves (11.14), including the tame and wild terms. Multiplying over the applicable finite places yields

$$
\begin{aligned}
\mathfrak f_0(R)
&=\mathfrak d_{M/K}\,
N_{M/K}\bigl(\mathfrak f_0(\theta)\bigr)
&&\text{if }\theta\text{ has finite order},\\
\mathfrak f_0^{(\ell)}(R)
&=\left(
\mathfrak d_{M/K}\,
N_{M/K}\bigl(\mathfrak f_0(\theta)\bigr)
\right)^{(\ell)}
&&\text{for algebraic }\theta.
\end{aligned}
\tag{11.15}
$$

No Galois hypothesis on $M/K$ is required. Formula (11.3) is the quadratic specialization.

There is also a uniform Frobenius formula. Suppose $v$ is unramified in $M$, $\theta$ is
unramified at every $w\mid v$, and $R$ is unramified at $v$; for an algebraic character of
nonfinite order, assume in particular that $v\nmid\ell$. Arithmetic Frobenius permutes the coset
basis in cycles indexed by the $w$. The cycle for $w$ has length $f(w/v)$, and the product of its
matrix entries is $\theta_\ell(\operatorname{Frob}_w^{\mathrm{arith}})$. Therefore

$$
\det\!\left(X-R(\operatorname{Frob}_v^{\mathrm{arith}})\right)
=\prod_{w\mid v}
\left(
X^{f(w/v)}-
\theta_\ell(\operatorname{Frob}_w^{\mathrm{arith}})
\right).
\tag{11.16}
$$

The degrees add to $d$. At a split place this is a product of linear factors. At an inert unramified place it is one factor of degree $d$, so all intermediate coefficients vanish. Equations (11.4) and (11.5) are the degree-two cases.

Induction and norms are both transitive. If $K\subseteq M\subseteq E$, then

$$
\operatorname{Ind}_{G_M}^{G_K}
\operatorname{Ind}_{G_E}^{G_M}\vartheta
\cong
\operatorname{Ind}_{G_E}^{G_K}\vartheta,
\qquad
N_{E/K}=N_{M/K}\circ N_{E/M}.
\tag{11.17}
$$

The twist, determinant, conductor, and Frobenius formulas respect these identities. Hence an induced term may be reorganized through intermediate fields without altering its local data.

Finally, an integer combination

$$
\sum_i n_i\operatorname{Ind}_{G_{M_i}}^{G_K}\theta_{i,\ell}
\tag{11.18}
$$

is initially a virtual character. Global reciprocity supplies every one-dimensional term from a Hecke character, and (11.9)--(11.17) control restriction, conjugation, determinants, conductors, and Frobenius values term by term. Class field theory alone does not prove that negative coefficients in (11.18) cancel to give an actual representation. It does provide the exact norm--transfer dictionary needed to test such an effectivity assertion without reversing any arrow.

## 12. The global reciprocity dictionary

The entries in this dictionary that use finite or infinite global reciprocity,
norm-subgroup classification, or global Galois avatars are under [FD,TS,TC], as
declared after Theorem 6.3. Purely local entries retain only their earlier local
prerequisites.

### 12.1 Fields, subgroups, and quotients

The classification may be read in either direction:

$$
\begin{array}{c|c}
\text{finite abelian extension }L/K
&\text{open finite-index subgroup }N_{L/K}C_L\subset C_K\\
\text{Galois group }\operatorname{Gal}(L/K)
&\text{quotient }C_K/N_{L/K}C_L\\
E\subseteq L
&N C_L\subseteq N C_E\\
K^{\mathrm{ab}}
&\widehat{C_K}=C_K/C_K^0.
\end{array}
$$

All arrows reverse at the field--subgroup boundary. Degree is index. Compositum corresponds to intersection of norm subgroups, while intersection of fields corresponds to the product of norm subgroups, followed by closure when an infinite family is involved.

For a nonabelian finite Galois extension, reciprocity sees only its maximal abelian subextension. Its class norm subgroup has index $|G^{\mathrm{ab}}|$, not $|G|$. This is a feature, not a defect: the source $C_K$ is abelian.

### 12.2 Local multiplicative data and global Galois data

At a finite place $v$ of an abelian extension $L/K$,

$$
\begin{array}{c|c}
K_v^\times&D_w\\
\mathcal O_v^\times&I_w\\
U_v^n&D_w^n\text{ in upper numbering}\\
\pi_v&\operatorname{Frob}_v^{\mathrm{arith}}\text{ modulo inertia}\\
N_{L_w/K_v}L_w^\times&\text{local Artin kernel}.
\end{array}
$$

At an unramified place, the uniformizer maps to an actual canonical Frobenius and units map to one. At a ramified place, a uniformizer chooses only a lift of residue Frobenius; multiplying it by a unit changes the lift by inertia. At a real place, $\mathbf R_{>0}$ maps to one and $-1$ maps to complex conjugation exactly when the place complexifies. At a complex place the local map is trivial.

### 12.3 Moduli, ramification, and splitting

A modulus records principal-unit depth at finite places and signs at selected real places. Its ray class field is the maximal abelian extension whose conductor divides that modulus. For a prime away from the finite conductor,

$$
\mathfrak p\mapsto\operatorname{Frob}_{\mathfrak p}^{\mathrm{arith}}.
$$

The prime splits completely precisely when its ray class lies in the subgroup defining the field. In the Hilbert class field this says “split completely if and only if principal”; over $\mathbf Q$ in a cyclotomic field it says $p\equiv1\pmod m$.

Ordinary class fields discard all real signs. Narrow class fields retain them. The two agree only when global units supply the necessary sign patterns. Complex places add no modulus condition, and roots of unity impose compatibility relations rather than extra infinite primes.

### 12.4 Norms without ambiguity

The reusable implications are

$$
a=N_{L/K}(y)
\Longrightarrow
a\text{ is a norm in every }K_v,
$$

and, when $L/K$ is cyclic, the converse. For arbitrary abelian or Galois extensions the converse can fail. Under [FD,TS,TC], the idele-class reciprocity statement is instead

$$
\ker(C_K\to\operatorname{Gal}(L/K))=N_{L/K}C_L
$$

for finite abelian $L/K$. Idele norms, class norms, local element norms, and global element norms should always be named rather than inferred from a bare symbol $N$.

In towers, norm on idele classes corresponds to inclusion of Galois groups, scalar inclusion of ideles corresponds to transfer, and quotient fields correspond to restriction. On Brauer groups, corestriction preserves local invariants and sums over the places above a fixed place, while restriction multiplies an invariant by the local degree. These directions remain correct under either reciprocity normalization, but every isolated Frobenius is inverted if one switches from arithmetic to geometric convention.

### 12.5 Characters at a glance

Finite-order Hecke characters are exactly finite-image one-dimensional complex Galois characters. Their local conductor exponents equal their Galois conductor exponents, and their unramified local values are arithmetic Frobenius eigenvalues. General continuous Hecke characters also have an archimedean module direction and need not be Galois characters with finite image.

Algebraic Hecke characters have integral infinity types. After choosing a complex-to-$\ell$-adic identification and applying the local algebraic correction at primes above $\ell$, they correspond exactly to one-dimensional $\ell$-adic Galois characters that are unramified outside finitely many places and locally algebraic above $\ell$. Norm pullback of Hecke characters matches restriction of Galois characters. For induction through a finite extension, twists use norm pullback, determinants use diagonal inclusion and transfer, conductors acquire the relative discriminant, and Frobenius polynomials are assembled from residue-degree cycles. The quadratic split and inert formulas (11.4) and (11.5) are the first instances of this general interface.

### 12.6 Conclusion

Global class field theory begins with local actions that appear independent. A unit at one prime detects inertia, a uniformizer detects Frobenius, a real sign detects complex conjugation, and an archimedean magnitude seems unrelated to all three. The idele class group assembles them, while the diagonal copy of $K^\times$ imposes the one global relation. Under FD, the Brauer invariant sequence proves that local symbols of a principal element multiply to one; under TS and TC, no further finite abelian obstruction survives beyond a norm subgroup.

Under [FD,TS,TC], the resulting correspondence is exact at every finite level.
Finite abelian extensions are open finite-index subgroups of $C_K$; Galois groups
are norm quotients; ramification is unit depth; conductors are moduli; and
Frobenius turns prime ideals into congruence classes. The Hilbert class field
converts ideal classes into automorphisms, while ray class fields organize every
bounded-ramification abelian extension. Independently, the [FD]-conditional
cyclic-algebra argument shows that cyclic norm equations satisfy a local--global
principle, and the failure beyond cyclic extensions identifies precisely where
global arithmetic contains more than its separate completions.

The invariant formalism retains the same coherence in cohomological degree two. Restriction multiplies local invariants by degree, corestriction preserves them and sums over branches, and the sum of all local invariants of a global class is zero. Hypothesis FD packages the unresolved step from these normalizations to the compact-support trace and perfect pairing; the manuscript no longer treats that passage as an elementary consequence of units, divisors, and ideal classes.

Under the same hypotheses, passing to all levels removes only the connected
component of the idele class group and yields $G_K^{\mathrm{ab}}$. Passing to
characters translates the same theorem into a language suited to representation
theory: finite-order characters are Galois characters, algebraic infinity types
produce locally algebraic $\ell$-adic characters, norm pullback becomes Galois
restriction, and induction is controlled by transfer, discriminants, and
Frobenius cycles. Conditional global reciprocity therefore does more than
enumerate abelian fields. It makes the abelianized Galois action of a number field
readable in its ideals, congruences, local units, signs, Brauer invariants, and
adelic characters as parts of one coherent arithmetic object.
