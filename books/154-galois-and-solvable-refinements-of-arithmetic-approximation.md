# Galois and Solvable Refinements of Arithmetic Approximation

## Contents

1. [Why ordinary approximation is not enough](#1-why-ordinary-approximation-is-not-enough)
   - [The three fields in the problem](#11-the-three-fields-in-the-problem)
   - [The failure of taking a normal closure afterward](#12-the-failure-of-taking-a-normal-closure-afterward)
   - [What a genuine refinement must remember](#13-what-a-genuine-refinement-must-remember)
   - [Standing conventions](#14-standing-conventions)
2. [Normal closures and field intersections](#2-normal-closures-and-field-intersections)
   - [Linear disjointness in its reliable form](#21-linear-disjointness-in-its-reliable-form)
   - [Root fields and their closures](#22-root-fields-and-their-closures)
   - [Disjointness of several Galois fields](#23-disjointness-of-several-galois-fields)
   - [Preservation of finite images](#24-preservation-of-finite-images)
3. [Local data inside a global Galois extension](#3-local-data-inside-a-global-galois-extension)
   - [Decomposition, inertia, and completion](#31-decomposition-inertia-and-completion)
   - [Subfields and double cosets](#32-subfields-and-double-cosets)
   - [Complete splitting propagates downward](#33-complete-splitting-propagates-downward)
   - [Total reality propagates through the diagram](#34-total-reality-propagates-through-the-diagram)
4. [Chebotarev prime selection](#4-chebotarev-prime-selection)
   - [Dirichlet density and Frobenius classes](#41-dirichlet-density-and-frobenius-classes)
   - [The analytic character lemma](#42-the-analytic-character-lemma)
   - [The abelian density theorem](#43-the-abelian-density-theorem)
   - [Reduction from a conjugacy class to a cyclic subgroup](#44-reduction-from-a-conjugacy-class-to-a-cyclic-subgroup)
   - [Chebotarev's theorem and its selection forms](#45-chebotarevs-theorem-and-its-selection-forms)
5. [Specialization homomorphisms](#5-specialization-homomorphisms)
   - [A Galois cover as a family of homomorphisms](#51-a-galois-cover-as-a-family-of-homomorphisms)
   - [Connected fibers and full monodromy](#52-connected-fibers-and-full-monodromy)
   - [Equivariant local constancy](#53-equivariant-local-constancy)
   - [Resolvents and base-changed connectedness](#54-resolvents-and-base-changed-connectedness)
6. [Galois approximation data](#6-galois-approximation-data)
   - [The definition and the role of each clause](#61-the-definition-and-the-role-of-each-clause)
   - [Local realizability](#62-local-realizability)
   - [Avoidance fields and constant fields](#63-avoidance-fields-and-constant-fields)
   - [Solvable bridge data](#64-solvable-bridge-data)
7. [The Galois-refined approximation theorem](#7-the-galois-refined-approximation-theorem)
   - [Statement](#71-statement)
   - [Proof](#72-proof)
   - [Exact local completions](#73-exact-local-completions)
   - [Why this is stronger than Moret--Bailly](#74-why-this-is-stronger-than-moret--bailly)
8. [Totally real and split refinements](#8-totally-real-and-split-refinements)
   - [Archimedean specialization data](#81-archimedean-specialization-data)
   - [The totally real Galois theorem](#82-the-totally-real-galois-theorem)
   - [Prescribed finite splitting](#83-prescribed-finite-splitting)
   - [Ramified local prescriptions](#84-ramified-local-prescriptions)
9. [Solvable bridges to the normal closure](#9-solvable-bridges-to-the-normal-closure)
   - [Point stabilizers and the upper extension](#91-point-stabilizers-and-the-upper-extension)
   - [Prime-cyclic towers](#92-prime-cyclic-towers)
   - [The symmetric quintic bridge](#93-the-symmetric-quintic-bridge)
   - [The exact limitation of the quintic method](#94-the-exact-limitation-of-the-quintic-method)
10. [Elementary subfields](#10-elementary-subfields)
    - [Elementary groups and solvability](#101-elementary-groups-and-solvability)
    - [The direction-reversing field dictionary](#102-the-direction-reversing-field-dictionary)
    - [Solvable upper towers](#103-solvable-upper-towers)
    - [Conjugate subgroups and conjugate fields](#104-conjugate-subgroups-and-conjugate-fields)
11. [The compatible family attached to one top field](#11-the-compatible-family-attached-to-one-top-field)
    - [What compatibility means](#111-what-compatibility-means)
    - [Intersections and composita of fixed fields](#112-intersections-and-composita-of-fixed-fields)
    - [Local compatibility throughout the family](#113-local-compatibility-throughout-the-family)
    - [Characters and cyclic layers](#114-characters-and-cyclic-layers)
12. [Mutually disjoint top fields](#12-mutually-disjoint-top-fields)
    - [Inductive avoidance](#121-inductive-avoidance)
    - [Product Galois groups](#122-product-galois-groups)
    - [Simultaneous specialization](#123-simultaneous-specialization)
    - [Infinite sequences and their exact scope](#124-infinite-sequences-and-their-exact-scope)
13. [The universal symmetric family](#13-the-universal-symmetric-family)
    - [Generic symmetric monodromy](#131-generic-symmetric-monodromy)
    - [Local coefficient neighborhoods](#132-local-coefficient-neighborhoods)
    - [Disjoint symmetric specializations](#133-disjoint-symmetric-specializations)
    - [Why a map to the target variety is additional geometry](#134-why-a-map-to-the-target-variety-is-additional-geometry)
14. [Constructing and checking bridge presentations](#14-constructing-and-checking-bridge-presentations)
    - [Evaluation families](#141-evaluation-families)
    - [Shrinking to the good locus](#142-shrinking-to-the-good-locus)
    - [A finite verification procedure](#143-a-finite-verification-procedure)
    - [Changing the presentation](#144-changing-the-presentation)
15. [Failures that delimit the theory](#15-failures-that-delimit-the-theory)
    - [A disjoint root field with a nondisjoint closure](#151-a-disjoint-root-field-with-a-nondisjoint-closure)
    - [Locally acceptable root data with unacceptable closure data](#152-locally-acceptable-root-data-with-unacceptable-closure-data)
    - [Solvable degree is not a solvable extension](#153-solvable-degree-is-not-a-solvable-extension)
    - [Pairwise conditions are not family compatibility](#154-pairwise-conditions-are-not-family-compatibility)
16. [The Brauer-descent field package](#16-the-brauer-descent-field-package)
    - [The input ledger](#161-the-input-ledger)
    - [The packaged existence theorem](#162-the-packaged-existence-theorem)
    - [Proof and dependency audit](#163-proof-and-dependency-audit)
    - [How to read the output](#164-how-to-read-the-output)
17. [Synthesis](#17-synthesis)
   - [The field diagram](#171-the-field-diagram)
   - [The order of construction](#172-the-order-of-construction)
   - [Conclusion](#173-conclusion)

## 1. Why ordinary approximation is not enough

Arithmetic approximation becomes substantially more delicate when the field produced by a
specialization is only the first layer of a later descent argument. The ordinary local-open
theorem of Book 153 is designed to produce a closed point. Its residue field has the prescribed
local behavior and can be made linearly disjoint from a fixed extension. It is deliberately not
a theorem about the normal closure of that residue field. This book develops the extra structure
needed when the normal closure, its subgroup fields, and its local decomposition groups are the
objects ultimately used.

The guiding principle is simple but easy to violate: every field that matters later must already
be visible in the specialization problem. A property of a root field does not automatically
become a property of its normal closure, and a property of several separately chosen fields does
not automatically become a compatible property of their compositum. We shall replace these
unsafe inferences by one Galois cover, one specialization homomorphism, and one diagram of fixed
fields.

### 1.1 The three fields in the problem

The first section fixes the vocabulary because three extensions are often hidden behind the
phrase “the auxiliary field.” Let $K$ be a number field and let a closed point on a
$K$-variety have residue field $L$. Let $M$ be the normal closure of $L/K$ in a fixed algebraic
closure. Finally, let $D/K$ be a finite Galois extension containing all fields that must be
avoided. We have

$$
K\subset L\subset M,
\qquad
K\subset D.
$$

The fields have different roles.

- The point itself is defined over $L$.
- The finite group used for subgroup induction is
  $$
  G=\operatorname{Gal}(M/K).
  $$
- Preservation of a finite Galois image is usually guaranteed by
  $$
  M\cap D=K,
  $$
  not merely by $L\cap D=K$.

If $J=\operatorname{Gal}(M/L)$, then $L=M^J$. The extension from the point field to the top
field is

$$
M/L\quad\text{with group }J.
$$

It is this upper group $J$, rather than the total group $G$ or the degree $[L:K]$, that decides
whether a known theory along solvable towers can carry an object from $L$ to $M$.

### 1.2 The failure of taking a normal closure afterward

This section explains the book's central warning. Suppose ordinary arithmetic approximation has
produced $L$ with $L\cap D=K$. It is tempting to replace $L$ by $M$ and continue. That step can
fail in two independent ways.

First, $M$ can meet $D$. Let $L/K$ be a non-Galois cubic with Galois group $S_3$ in its normal
closure. The unique quadratic subfield $Q$ of $M$ is fixed by $A_3$. Since $[L:K]=3$ and
$[Q:K]=2$, one has $L\cap Q=K$, but $Q\subset M$. Taking $D=Q$ gives

$$
L\cap D=K,
\qquad
M\cap D=D.
$$

Thus restriction to $L$ can preserve a finite image while restriction to $M$ shrinks it.

Second, $M/L$ need not be solvable. In the generic degree-$n$ situation one has

$$
G\simeq S_n,
\qquad
J\simeq S_{n-1}.
$$

For $n\ge6$, the stabilizer $S_{n-1}$ is not solvable. No information about the integer
$[M:L]=(n-1)!$ repairs this: solvability is a property of a group, not of the prime factors of
its order.

Local data can fail as well. The tensor product $L\otimes_KK_v$ records the orbits of a local
decomposition group on $G/J$. It need not determine the decomposition subgroup inside $G$ up to
conjugacy. Two nonconjugate subgroups can have the same orbit lengths in one permutation action.
Consequently, a factorization pattern for the root field need not determine the completions of
the normal closure or of every intermediate field.

These are genuine mathematical failures. The solution is not a more careful argument after the
fact; it is a stronger specialization datum before the field is chosen.

### 1.3 What a genuine refinement must remember

A refined construction must remember four kinds of information simultaneously.

1. A finite étale family whose connected fiber is the desired point field.
2. A finite étale Galois closure of that family with a specified generic group $G$.
3. At each controlled place, the entire local $G$-torsor, or equivalently a local
   homomorphism into $G$ up to conjugacy.
4. A connectedness condition after base change to $D$, so the specialized top field, not only
   the root field, is disjoint from $D$.

When a solvable bridge is required, there is a fifth item:

5. the stabilizer $J$ of one sheet in the chosen transitive $G$-set must be solvable.

The resulting diagram is then determined before specialization:

~~~text
                         M
                    /    |    \
             solvable    |     solvable
                /        |        \
             L=M^J     M^{H_1}   M^{H_2}
                    \    |    /
                         K
~~~

The groups $H_i$ used later may be elementary subgroups of $G$. Their upper extensions
$M/M^{H_i}$ are solvable because the $H_i$ are solvable. Nothing here says that the lower
extensions $M^{H_i}/K$ are solvable or Galois.

### 1.4 Standing conventions

We now set conventions that keep later statements unambiguous. All number fields are embedded in
one algebraic closure of the base when intersections and composita are written. A variety is
separated and of finite type. All finite covers are restricted to their finite étale loci before
specialization. Arithmetic Frobenius acts on a residue field by

$$
x\longmapsto x^{N\mathfrak p}.
$$

For a finite Galois extension $M/K$, a prime $w$ of $M$ above $v$ has decomposition and inertia
groups $D_w$ and $I_w$. Replacing $w$ by a conjugate conjugates both groups. Hence a local datum
inside $G$ is always understood up to simultaneous $G$-conjugacy unless a labeling has explicitly
been chosen.

Book 2 supplies the completed tensor-product formula, uniqueness of valuations on local fields,
and the identification of a decomposition group with a completed Galois group. Book 152 supplies
Hilbert irreducibility with finite local approximation, preservation of generic monodromy, and
equivariant local constancy of finite étale fibers. Book 153 supplies the moving-family
construction that turns locally prescribed configurations on a smooth geometrically connected
variety into a finite étale incidence family. Book 6 supplies finite global Artin reciprocity,
finite-character existence, and the dictionary between finite-order Hecke characters and
finite-image one-dimensional Galois characters. It supplies no prime-distribution theorem used
here: Chapter 4 proves the required Chebotarev theorem from theta series, Poisson summation,
Mellin transforms, and that reciprocity dictionary. We shall recall every form that enters a
proof and shall state the additional hypotheses precisely.

## 2. Normal closures and field intersections

Before using geometry, we need a reliable field-theoretic ledger. This chapter separates linear
disjointness, trivial intersection, and disjointness of normal closures. The distinctions are
elementary, but nearly every later compatibility statement depends on them.

### 2.1 Linear disjointness in its reliable form

Let $A/K$ and $B/K$ be finite extensions. They are **linearly disjoint over $K$** if the natural
map

$$
A\otimes_KB\longrightarrow AB
$$

is injective. Since the target is a field, this is equivalent to $A\otimes_KB$ being a field,
and also to

$$
[AB:K]=[A:K][B:K].
$$

Trivial intersection is not equivalent in complete generality. The clean form used here is the
following.

**Proposition 2.1.** If at least one of $A/K$ and $B/K$ is Galois, then the following are
equivalent:

1. $A$ and $B$ are linearly disjoint over $K$;
2. $A\cap B=K$;
3. $[AB:B]=[A:K]$;
4. $[AB:A]=[B:K]$.

**Proof strategy.** When $A/K$ is Galois, restriction identifies the Galois group of $AB/B$ with
the subgroup fixing $A\cap B$. Degrees then translate the intersection into linear
disjointness.

**Proof.** Assume $A/K$ is Galois. The extension $AB/B$ is Galois, and restriction gives

$$
\operatorname{Gal}(AB/B)
\simeq
\operatorname{Gal}(A/A\cap B).
$$

Indeed, an $A\cap B$-automorphism of $A$ extends to $AB$ by acting trivially on $B$, while every
$B$-automorphism restricts in the indicated way. Therefore

$$
[AB:B]=[A:A\cap B].
$$

This equals $[A:K]$ exactly when $A\cap B=K$. The degree product criterion for linear
disjointness gives the equivalence with 1. Symmetry gives 4. $\square$

The proposition is why an avoidance field is normally replaced by its Galois closure. It turns
the intersection condition into a safe degree statement. It does not say that disjointness of a
non-Galois root field controls its normal closure.

### 2.2 Root fields and their closures

Let $L/K$ be finite separable, let $M/K$ be its normal closure, and put

$$
G=\operatorname{Gal}(M/K),
\qquad
J=\operatorname{Gal}(M/L).
$$

The $K$-embeddings of $L$ into $M$ are naturally the left cosets $G/J$. The action is faithful
exactly when

$$
\operatorname{core}_G(J)
=\bigcap_{g\in G}gJg^{-1}
=1.
$$

For a normal closure it is faithful: an element fixing every conjugate $g(L)$ fixes the
compositum of those conjugates, namely $M$.

**Proposition 2.2.** Let $D/K$ be finite Galois. The following are equivalent:

1. $M\cap D=K$;
2. $M$ and $D$ are linearly disjoint over $K$;
3. the normal closure of $LD/D$ has Galois group $G$ in the same action on $G/J$;
4. every subgroup resolvent for the transitive extension $L/K$ retains its generic degree after
   base change to $D$.

**Proof.** The equivalence of 1 and 2 is Proposition 2.1. If they hold, then

$$
\operatorname{Gal}(MD/D)\xrightarrow{\sim}\operatorname{Gal}(M/K)=G
$$

by restriction, and $LD$ is fixed by the same subgroup $J$. This proves 3. Conversely, 3 gives
$[MD:D]=|G|=[M:K]$, so 1 follows.

For 4, the fixed field $M^H$ of a subgroup $H\le G$ has degree $[G:H]$. A primitive-element
polynomial for $M^H$ is the corresponding subgroup resolvent. Retaining its degree after base
change to $D$ is equivalent to

$$
M^H\cap D=K.
$$

If this holds for the trivial subgroup, it is exactly $M\cap D=K$. If $M\cap D=K$, it holds for
every $M^H\subset M$. $\square$

The last equivalence explains why full-closure avoidance is a finite Hilbert condition. A finite
group has only finitely many conjugacy classes of subgroups, and in fact connectedness of the
Galois closure after base change to $D$ already enforces all the subgroup resolvents at once.

### 2.3 Disjointness of several Galois fields

Pairwise disjointness is not always enough for a whole family. Three quadratic fields can be
pairwise distinct, hence pairwise intersect only in $K$, while the third lies in the compositum
of the first two. The correct inductive condition is stronger.

**Definition 2.3.** Finite extensions $M_1,\ldots,M_r$ of $K$ are **mutually linearly
disjoint** if the natural map

$$
M_1\otimes_K\cdots\otimes_KM_r
\longrightarrow M_1\cdots M_r
$$

is injective.

**Proposition 2.4.** Suppose every $M_i/K$ is finite Galois. The following are equivalent:

1. the fields are mutually linearly disjoint;
2. for every $i>1$,
   $$
   M_i\cap(M_1\cdots M_{i-1})=K;
   $$
3. restriction induces an isomorphism
   $$
   \operatorname{Gal}(M_1\cdots M_r/K)
   \simeq
   \prod_{i=1}^r\operatorname{Gal}(M_i/K).
   $$

**Proof.** Induct on $r$. The compositum of the first $r-1$ fields is Galois. Proposition 2.1
shows that condition 2 at the last stage is equivalent to linear disjointness of $M_r$ from that
compositum, hence to multiplication of the degrees. Iterating proves 1. Under the same
condition, restriction to the factors is injective and both sides have order
$\prod_i[M_i:K]$, proving 3. Conversely, 3 gives the degree product and hence 1. $\square$

This proposition will support an induction: after constructing $M_1,\ldots,M_{r-1}$, put their
compositum into the next avoidance field. Ordinary pairwise avoidance would not suffice.

### 2.4 Preservation of finite images

The practical reason for closure-level disjointness is often the preservation of several finite
Galois representations. We record the exact statement.

**Lemma 2.5 (image preservation).** Let

$$
\rho:G_K\longrightarrow A
$$

be a continuous homomorphism with finite image, and let $D_\rho/K$ be the finite Galois
extension fixed by its kernel. If $E/K$ is finite and $E\cap D_\rho=K$, then

$$
\rho(G_E)=\rho(G_K).
$$

**Proof.** Since $D_\rho/K$ is Galois, Proposition 2.1 gives

$$
\operatorname{Gal}(ED_\rho/E)
\simeq
\operatorname{Gal}(D_\rho/K).
$$

The left side is a quotient of $G_E$, and the right side identifies faithfully with
$\rho(G_K)$. Hence the image of $G_E$ contains every element of $\rho(G_K)$. The reverse
inclusion is automatic. $\square$

For finitely many representations, take $D$ to be the compositum of their fixed fields and then
its Galois closure, which is the same compositum if every fixed field was already Galois. If
$M\cap D=K$, Lemma 2.5 applies not only over the root field $L\subset M$ but over every
intermediate field $F$ with $K\subset F\subset M$: one has $F\cap D=K$.

## 3. Local data inside a global Galois extension

The normal closure is useful because all local completions can be read from subgroups of one
finite group. This chapter develops that dictionary in a form that works simultaneously for
every elementary fixed field. The double-coset formula is the central result: it turns one local
decomposition subgroup at the top into the complete tensor product for every subfield.

### 3.1 Decomposition, inertia, and completion

Let $M/K$ be finite Galois with group $G$, let $v$ be a finite place of $K$, and choose a place
$w$ of $M$ above $v$. Define

$$
D=D_w=\{g\in G:g(w)=w\},
$$

and let $I=I_w$ be the kernel of the action of $D$ on the residue field at $w$. Book 2 proves
the canonical identification

$$
D\simeq\operatorname{Gal}(M_w/K_v)
$$

and the exact sequence

$$
1\longrightarrow I\longrightarrow D
\longrightarrow
\operatorname{Gal}(\kappa(w)/\kappa(v))
\longrightarrow1.
$$

The quotient is cyclic, generated by arithmetic Frobenius when the residue fields are finite.
The global tensor product is

$$
M\otimes_KK_v\simeq\prod_{G/D}M_{gw},
$$

where all factors are conjugate to $M_w$. In particular, the number of factors is $[G:D]$ and
each has degree $|D|$.

The subgroup $D$ records the entire completed Galois extension. The inertia subgroup $I$ records
the ramified part. At an unramified place $I=1$ and the conjugacy class of a generator of $D$ is
the Frobenius class. At a ramified place a lift of residue Frobenius is not canonical, so local
data must retain the full homomorphism from the local absolute Galois group, not just one chosen
element.

### 3.2 Subfields and double cosets

Let $H\le G$ and put $F=M^H$. We want the whole algebra $F\otimes_KK_v$, not merely one
completion. The answer is controlled by the action of $D$ on the embeddings $G/H$.

**Theorem 3.1 (double-coset completion formula).** With the notation above, the places of
$F=M^H$ above $v$ are naturally indexed by the double cosets

$$
D\backslash G/H.
$$

For a representative $g\in G$, the corresponding completion is, up to the natural conjugate
identification,

$$
F_{v,g}\simeq M_w^{D\cap gHg^{-1}}.
$$

Consequently

$$
F\otimes_KK_v
\simeq
\prod_{DgH\in D\backslash G/H}
M_w^{D\cap gHg^{-1}},
$$

and the degree of the factor indexed by $DgH$ is

$$
[D:D\cap gHg^{-1}].
$$

**Proof strategy.** The embeddings of $F$ into $M$ are cosets $G/H$. The local group $D$ groups
these embeddings into orbits, one orbit for each completion. Stabilizers give the completed
degrees and fixed fields.

**Proof.** A $K$-embedding $F\hookrightarrow M$ is the restriction of some $g\in G$, and two
elements give the same embedding exactly when they differ on the right by an element of $H$.
Thus the embedding set is $G/H$. The decomposition group $D$ acts on this set on the left. Two
embeddings induce the same place of $F$ above $v$ exactly when they differ by an automorphism of
the chosen completed algebraic closure over $K_v$, equivalently when they lie in the same
$D$-orbit. The orbit set is $D\backslash G/H$.

The stabilizer in $D$ of $gH$ is

$$
\{d\in D:dgH=gH\}=D\cap gHg^{-1}.
$$

Under $D\simeq\operatorname{Gal}(M_w/K_v)$, the image of the completion of $g(F)$ inside $M_w$
is therefore the fixed field of this stabilizer. Its degree over $K_v$ is the orbit size
$[D:D\cap gHg^{-1}]$. The completed tensor-product decomposition from Book 2 now gives the
displayed product. $\square$

The theorem is the compatibility mechanism required later. Once $M$, $D$, and $I$ are fixed,
the completion of every $M^H$ is forced. No separate local choices for different $H$ are needed,
and indeed arbitrary separate choices might be incompatible.

**Corollary 3.2.** Put

$$
Q=D\cap gHg^{-1}.
$$

For the factor $E=M_w^Q$, the ramification index and residue degree over $K_v$ are

$$
e(E/K_v)=[I:I\cap Q],
\qquad
f(E/K_v)=[D:IQ].
$$

The inertia group of the upper Galois extension $M_w/E$ is $I\cap Q$, while the image of $Q$
in $D/I$ controls the residue field of $E$.

**Proof.** Apply the inertia exact sequence in the tower

$$
M_w/M_w^{D\cap gHg^{-1}}/K_v.
$$

The top extension $M_w/K_v$ is Galois with group $D$ and inertia group $I$. The upper extension
$M_w/E$ is Galois with group $Q$, and its inertia group is $I\cap Q$: an element of $Q$ acts
trivially on the residue field of $M_w$ exactly when it lies in $I$. Hence multiplicativity of
ramification indices in the tower gives

$$
e(E/K_v)
=\frac{e(M_w/K_v)}{e(M_w/E)}
=\frac{|I|}{|I\cap Q|}
=[I:I\cap Q].
$$

Similarly,

$$
f(M_w/K_v)=|D/I|
$$

and

$$
f(M_w/E)=|Q/(I\cap Q)|=|IQ/I|.
$$

Multiplicativity of residue degrees therefore gives

$$
f(E/K_v)
=\frac{|D/I|}{|IQ/I|}
=[D:IQ].
$$

In particular, the image of $Q$ in $D/I$ is $IQ/I$ and controls the residue field of $E$.
The two formulas are consistent because

$$
[I:I\cap Q][D:IQ]=[D:Q]=[E:K_v],
$$

as required. $\square$

### 3.3 Complete splitting propagates downward

Complete splitting is the cleanest local condition because it erases every decomposition group.

**Proposition 3.3.** For a finite Galois extension $M/K$ and a place $v$ of $K$, the following
are equivalent:

1. $v$ splits completely in $M$;
2. $D_w=1$ for one, hence every, $w\mid v$;
3. $M_w=K_v$ for every $w\mid v$;
4. $M\otimes_KK_v\simeq K_v^{[M:K]}$.

If these conditions hold, $v$ splits completely in every intermediate field $M^H$.

**Proof.** The equivalence follows from

$$
[M_w:K_v]=|D_w|
$$

and the completed tensor-product formula. When $D=1$, Theorem 3.1 gives one degree-one factor
for every element of $G/H$, hence

$$
M^H\otimes_KK_v\simeq K_v^{[G:H]}.
$$

$\square$

There is also an upward statement that is special to normal closures.

**Proposition 3.4.** Let $L/K$ be finite separable with normal closure $M$. If $v$ splits
completely in $L$, then it splits completely in $M$.

**Proof.** Choose a defining irreducible polynomial $f\in K[X]$ for $L$ and a place away from
the denominators of the chosen generator. Complete splitting gives

$$
L\otimes_KK_v\simeq K_v^{[L:K]}.
$$

Thus every $K$-embedding of $L$ into an algebraic closure of $K_v$ has image in $K_v$. The
normal closure $M$ is generated by these conjugate images, so its image in the local algebraic
closure is already $K_v$. Hence every decomposition group in $M/K$ is trivial. Equivalently,
one can use the faithful action of $D$ on $G/J$: complete splitting says every $D$-orbit is a
singleton, so $D$ acts trivially; faithfulness of the normal-closure action forces $D=1$.
$\square$

This proposition is safe because complete splitting gives every conjugate root. A general local
factorization pattern does not determine $D$ faithfully.

### 3.4 Total reality propagates through the diagram

The archimedean analogue is equally clean. Suppose $K$ is totally real and $L/K$ is finite
totally real. Every $K$-conjugate $g(L)$ is again contained in $\mathbf R$ under each embedding
of $K$ into $\mathbf R$. Since the normal closure is the compositum of these conjugates, it is
totally real.

**Proposition 3.5.** If $K$ is totally real and $L/K$ is totally real, then the normal closure
$M/K$ and every intermediate field $M^H$ are totally real.

**Proof.** Fix an embedding $\iota:K\hookrightarrow\mathbf R$ and extend it to an embedding of
the common algebraic closure into $\mathbf C$. Every $K$-embedding of $L$ has real image by total
reality. The field $M$ is generated by these images, hence lies in $\mathbf R$. Thus every
extension of every real embedding of $K$ to $M$ is real. Subfields of a totally real field are
totally real. $\square$

Unlike disjointness, total reality may safely be checked on the root field and propagated to the
normal closure. This contrast will recur: archimedean generation behaves monotonically, whereas
intersection with an avoidance field need not.

## 4. Chebotarev prime selection

Refined approximation uses auxiliary primes for two purposes: to witness elements of a finite
Galois group and to keep those primes away from all previously controlled places. Existence of
one suitable prime is enough for specialization, but the strongest and cleanest statement gives
the exact Dirichlet density of every Frobenius class. We develop that statement here so that no
prime-selection step rests on an unproved density assertion.

We do not take a Chebotarev theorem, a prime-ideal theorem, or analytic properties of Artin
$L$-functions as an input. We prove exactly what is needed. The analytic ingredients are the
ordinary Poisson summation formula for a lattice in a Euclidean space, the elementary Mellin
integral for a Gaussian, and the unit-lattice theorem. Book 6 enters only after that analysis,
to attach a cyclic field to a finite-order Hecke character, to identify finite abelian Galois
characters with such Hecke characters, and to match their values at unramified primes with
arithmetic Frobenius.

### 4.1 Dirichlet density and Frobenius classes

Let $K$ be a number field. For a set $S$ of nonzero prime ideals of $\mathcal O_K$, define

$$
P_S(s)=\sum_{\mathfrak p\in S}(N\mathfrak p)^{-s},
\qquad s>1.
$$

We say $S$ has **Dirichlet density** $\delta$ if

$$
\lim_{s\to1^+}
\frac{P_S(s)}{\log(1/(s-1))}
=\delta.
$$

Finite sets have density zero because their prime sums stay bounded as $s\to1^+$. The set of all
primes has density one. Indeed Step 4 of Lemma 4.1 below proves directly from a theta series that
$\zeta_K$ has a simple pole at $1$ with positive residue. Its Euler product then gives

$$
\log\zeta_K(s)
=\sum_{\mathfrak p}(N\mathfrak p)^{-s}+O(1),
$$

because the terms of prime-power exponent at least two form a bounded sum for $s$ near $1$, and
the simple pole of $\zeta_K$ gives

$$
\log\zeta_K(s)=\log(1/(s-1))+O(1).
$$

Now let $M/K$ be finite Galois with group $G$. Outside the finite ramified set, a prime
$\mathfrak p$ determines a conjugacy class

$$
\operatorname{Frob}_{\mathfrak p}\subset G.
$$

For a conjugacy class $C\subset G$, write $S_C(M/K)$ for the unramified primes whose arithmetic
Frobenius class is $C$.

### 4.2 The analytic character lemma

The abelian case is a character-orthogonality calculation once one knows that nontrivial
finite-order characters contribute no logarithmic singularity at $1$.

**Lemma 4.1 (finite-order Hecke character prime sum).** Let $\chi$ be a finite-order Hecke
character of a number field $K$, with the finitely many conductor primes omitted. Then, as
$s\to1^+$,

$$
\sum_{\mathfrak p}
\chi(\mathfrak p)(N\mathfrak p)^{-s}
=
\begin{cases}
\log(1/(s-1))+O(1),&\chi=1,\\
O(1),&\chi\ne1.
\end{cases}
$$

**Proof strategy.** We first prove, rather than cite, the required analytic statement. For every
narrow ray class we write its partial zeta function as a sum of $|N_{K/\mathbf Q}\alpha|^{-s}$
over one affine lattice, modulo the ray-unit group. A Gaussian theta series on that lattice is
integrated over the positive archimedean scalings modulo units. Unfolding gives the partial zeta
function times explicit gamma factors. Poisson summation gives its continuation. Its zero dual
frequency gives the pole at $1$; the covolume formula makes the residue independent of the ray
class and visibly positive. Character orthogonality then gives holomorphy at $1$. Finally, a
prime-by-prime cyclic factorization of a Dedekind zeta function proves nonvanishing. Taking the
Euler-product logarithm finishes the prime-sum calculation.

**Proof.** We give all parts of the analytic argument.

**Step 1: ray partial zeta functions as unit-orbit sums.** Enlarge a conductor modulus for
$\chi$, if necessary, so that it has the form

$$
\mathfrak m=\mathfrak m_0\mathfrak m_\infty,
$$

where $\mathfrak m_\infty$ contains every real place of $K$. Let $I_{\mathfrak m}$ be the group
of fractional ideals prime to $\mathfrak m_0$, and let

$$
P_{\mathfrak m,1}
=\{(\alpha):\alpha\equiv1\pmod{\mathfrak m_0},
\ \sigma(\alpha)>0\text{ for every real }\sigma\}.
$$

The narrow ray class group is

$$
C_{\mathfrak m}=I_{\mathfrak m}/P_{\mathfrak m,1}.
$$

This group is finite: its map to the ordinary ideal class group has finite target, and its kernel
is a quotient of the finite residue-and-sign group
$(\mathcal O_K/\mathfrak m_0)^\times\times\{\pm1\}^{r_1}$.

For $c\in C_{\mathfrak m}$ define

$$
\zeta_c(s)
=\sum_{\substack{\mathfrak b\subset\mathcal O_K,
\ (\mathfrak b,\mathfrak m_0)=1\\[2pt]
[\mathfrak b]=c}}
(N\mathfrak b)^{-s},
\qquad \Re(s)>1.
\tag{4.1}
$$

Choose an integral ideal $\mathfrak a$, prime to $\mathfrak m_0$, whose ray class is $c^{-1}$.
Such a representative exists. Start with a fractional ideal $\mathfrak a'$ in the class.
Because $\mathfrak a'$ is prime to $\mathfrak m_0$, the localization of
$(\mathfrak a')^{-1}$ at every prime dividing $\mathfrak m_0$ is the local integer ring. The
Chinese remainder theorem therefore makes the reduction map from $(\mathfrak a')^{-1}$ onto
$\mathcal O_K/\mathfrak m_0$ surjective. Choose a preimage $\alpha$ of $1$; adding a
sufficiently large positive rational integer lying in
$\mathfrak m_0(\mathfrak a')^{-1}\cap\mathfrak m_0$ makes every real embedding of $\alpha$
positive. Such integers exist after clearing the denominators of that fractional ideal, and
arbitrary positive multiples remain in the intersection. Then
$\alpha\mathfrak a'$ is integral and prime to $\mathfrak m_0$, and multiplication by the ray
principal ideal $(\alpha)$ does not change the ray class.
An ideal $\mathfrak b$ occurring in (4.1) satisfies

$$
\mathfrak b\mathfrak a=(\alpha)
$$

for an $\alpha\in\mathfrak a$ with

$$
\alpha\equiv1\pmod{\mathfrak m_0},
\qquad
\sigma(\alpha)>0\quad(\sigma:K\hookrightarrow\mathbf R).
\tag{4.2}
$$

Conversely, every such $\alpha$ gives the integral ideal

$$
\mathfrak b=(\alpha)\mathfrak a^{-1}
$$

in the class $c$. Two elements give the same ideal exactly when they differ by an element of

$$
U_{\mathfrak m}
=\{u\in\mathcal O_K^\times:u\equiv1\pmod{\mathfrak m_0},
\ \sigma(u)>0\text{ at every real place}\}.
$$

Moreover,

$$
N\mathfrak b=\frac{|N_{K/\mathbf Q}\alpha|}{N\mathfrak a}.
$$

The elements of $\mathfrak a$ satisfying the finite congruence in (4.2) form an affine lattice

$$
A_{\mathfrak a}=\alpha_0+\mathfrak m_0\mathfrak a
\tag{4.3}
$$

in the Minkowski space. To justify (4.3), localize at a finite prime. At primes dividing
$\mathfrak m_0$ one has $\mathfrak a_{\mathfrak p}=\mathcal O_{K,\mathfrak p}$ and obtains the
stated congruence; away from $\mathfrak m_0$, multiplication by $\mathfrak m_0$ is a unit and
both sides impose only membership in $\mathfrak a_{\mathfrak p}$. The Chinese remainder theorem
supplies $\alpha_0$. When $\mathfrak m_0=(1)$, (4.3) means simply
$A_{\mathfrak a}=\mathfrak a$.

Choose a torsion-free subgroup $U\subset U_{\mathfrak m}$ of finite index

$$
h=[U_{\mathfrak m}:U].
$$

The unit action on nonzero elements is free. Hence a $U_{\mathfrak m}$-orbit is the disjoint
union of $h$ $U$-orbits. Writing a superscript $/U$ for a sum over one representative of each
$U$-orbit, (4.1) becomes

$$
\zeta_c(s)
=\frac{(N\mathfrak a)^s}{h}
\sum_{\substack{\alpha\in A_{\mathfrak a},\ \alpha\ne0\\
\sigma(\alpha)>0\ \forall\sigma}}^{/U}
|N_{K/\mathbf Q}\alpha|^{-s}.
\tag{4.4}
$$

This formula is an exact parametrization, not an asymptotic comparison.

**Step 2: the theta kernels and Poisson summation.** Write

$$
K_\infty=K\otimes_{\mathbf Q}\mathbf R
\simeq\mathbf R^{r_1}\times\mathbf C^{r_2}.
$$

For an archimedean place $v$, put $d_v=1$ if $v$ is real and $d_v=2$ if it is complex. For
$t=(t_v)_v\in T=(\mathbf R_{>0})^{r_1+r_2}$ set

$$
q(t)=\prod_{v\mid\infty}t_v^{d_v},
\qquad
d^\times t=\prod_{v\mid\infty}\frac{dt_v}{t_v}.
$$

For a parity vector $\epsilon=(\epsilon_v)_{v\text{ real}}\in\{0,1\}^{r_1}$, define the
Schwartz function

$$
\Phi_\epsilon(x)
=\prod_{v\text{ real}}x_v^{\epsilon_v}e^{-\pi x_v^2}
\prod_{v\text{ complex}}e^{-2\pi|x_v|^2}
\quad(x\in K_\infty).
\tag{4.5}
$$

Coordinatewise multiplication is denoted $tx$. Attach to the affine lattice (4.3) the theta
series

$$
\Theta_{\mathfrak a,\epsilon}(t)
=\sum_{\alpha\in A_{\mathfrak a}}\Phi_\epsilon(t\alpha).
$$

If $0\in A_{\mathfrak a}$, subtract its term, and write the result as
$\Theta^*_{\mathfrak a,\epsilon}$. Thus the star always means that the zero vector is omitted.

We recall the lattice Poisson formula in exactly the form used. If $L\subset K_\infty$ is a
full lattice, $x_0+L$ an affine translate, and $L^\vee$ the dual for the trace pairing, then

$$
\sum_{x\in x_0+L}\Phi_\epsilon(tx)
=\frac{q(t)^{-1}}{\operatorname{covol}(L)}
\sum_{y\in L^\vee}
e^{2\pi i\langle y,x_0\rangle}
\widehat\Phi_\epsilon(t^{-1}y).
\tag{4.6}
$$

Indeed, ordinary Poisson summation gives the formula at $t=1$. Under the change of variables
$x\mapsto tx$, Lebesgue measure is multiplied by $q(t)$ and the Fourier variable changes by
$t^{-1}$, giving (4.6). The one-dimensional Fourier transform of a Gaussian, and its derivative
when $\epsilon_v=1$, show that $\widehat\Phi_\epsilon$ is again a polynomial times a Gaussian.
In particular,

$$
\widehat\Phi_\epsilon(0)=0\quad(\epsilon\ne0),
\qquad
\widehat\Phi_0(0)>0.
\tag{4.7}
$$

Under the standard Minkowski measure there is a fixed positive constant $c_K$ such that

$$
\operatorname{covol}(\mathfrak b)=c_KN\mathfrak b
\tag{4.8}
$$

for every integral ideal $\mathfrak b$; with the usual unscaled complex Lebesgue measure,
$c_K=2^{-r_2}|d_K|^{1/2}$. Hence

$$
\operatorname{covol}(\mathfrak m_0\mathfrak a)
=c_KN\mathfrak m_0N\mathfrak a.
\tag{4.9}
$$

The equality (4.8) follows by writing an integral basis in the Minkowski embedding: the square
of the real determinant, after pairing each complex embedding with its conjugate, is the field
discriminant. Multiplication by an ideal changes the lattice index by its ideal norm. Thus the
covolume normalization and its positivity have both been accounted for.

**Step 3: Mellin unfolding modulo the units.** Dirichlet's unit theorem says that

$$
u\longmapsto(\log|u|_v)_{v\mid\infty}
$$

maps $U$ to a full lattice in the hyperplane

$$
\sum_{v\mid\infty}d_vy_v=0.
$$

It acts on $T$ by $t_v\mapsto|u|_vt_v$. The function $q(t)$ and the measure
$d^\times t$ are invariant, and the quotient of each hypersurface $q(t)=q$ by $U$ is compact.
Choose a fundamental parallelepiped for the logarithmic unit lattice. It follows that
$T/U$ is the product of a compact shape space and the radial coordinate $q\in\mathbf R_{>0}$;
for a positive constant choice of shape measure,

$$
d^\times t=\frac{dq}{q}\,dy.
\tag{4.10}
$$

For $\Re(s)>1$, put

$$
J_{\mathfrak a,\epsilon}(s)
=\int_{T/U}\Theta^*_{\mathfrak a,\epsilon}(t)q(t)^s\,d^\times t.
\tag{4.11}
$$

The theta series is $U$-invariant: replacing $t$ by $|u|t$ replaces the summation variable
$\alpha$ by $u\alpha$; at a complex place the harmless phase $u_v/|u_v|$ disappears because
the complex kernel in (4.5) is radial. Unfolding a $U$-orbit across a fundamental domain gives

$$
J_{\mathfrak a,\epsilon}(s)
=G_\epsilon(s)
\sum_{\substack{\alpha\in A_{\mathfrak a},\ \alpha\ne0}}^{/U}
\left(\prod_{v\text{ real}}\operatorname{sgn}(\alpha_v)^{\epsilon_v}\right)
|N_{K/\mathbf Q}\alpha|^{-s},
\tag{4.12}
$$

where the separate one-variable Gaussian integrals give

$$
G_\epsilon(s)
=\prod_{v\text{ real}}
\left(
\frac12\pi^{-(s+\epsilon_v)/2}
\Gamma\!\left(\frac{s+\epsilon_v}{2}\right)
\right)
\prod_{v\text{ complex}}
\left(
\frac12(2\pi)^{-s}\Gamma(s)
\right).
\tag{4.13}
$$

For example, at a real place,

$$
\int_0^\infty(t\alpha)^\epsilon e^{-\pi t^2\alpha^2}t^s\frac{dt}{t}
=\frac12\pi^{-(s+\epsilon)/2}
\Gamma\!\left(\frac{s+\epsilon}{2}\right)
\operatorname{sgn}(\alpha)^\epsilon|\alpha|^{-s}.
$$

This proves (4.12), including every archimedean normalization. For completeness, fix a Euclidean
norm on $K_\infty$. A full lattice has $O(R^{[K:\mathbf Q]})$ points of norm at most $R$,
because translates of one sufficiently small ball around its lattice points are disjoint and
fit inside a ball of radius $R+O(1)$. The same estimate holds for an affine translate. On a
compact shape set, the absolute value of every kernel in (4.5) is bounded by a polynomial times
$\exp(-c q^{2/[K:\mathbf Q]}\|\alpha\|^2)$. Splitting the affine lattice into the shells
$j\le\|\alpha\|<j+1$ shows uniformly in the shape variable that the sum of the absolute kernels
is $O(q^{-1})$ for $0<q\le1$ and, after omitting zero, is exponentially decreasing for
$q\ge1$. Thus its product with $q^{\Re(s)}dq/q$ is integrable exactly in the range needed,
$\Re(s)>1$. Tonelli applied to the absolute values therefore justifies the unfolding and all
interchanges of sum and integral.

For a nonzero $\alpha$, positivity at all real places has the finite Fourier expansion

$$
1_{\{\alpha_v>0\ \forall v\text{ real}\}}
=2^{-r_1}\sum_{\epsilon\in\{0,1\}^{r_1}}
\prod_{v\text{ real}}\operatorname{sgn}(\alpha_v)^{\epsilon_v}.
\tag{4.14}
$$

Combining (4.4), (4.12), and (4.14) gives the exact Mellin formula

$$
\zeta_c(s)
=\frac{2^{-r_1}(N\mathfrak a)^s}{h}
\sum_{\epsilon\in\{0,1\}^{r_1}}
\frac{J_{\mathfrak a,\epsilon}(s)}{G_\epsilon(s)}.
\tag{4.15}
$$

**Step 4: continuation, equal residues, and positivity.** We now analyze (4.11) at the two
radial ends. On a fixed compact shape space, every $t_v$ is a bounded positive multiple of
$q^{1/[K:\mathbf Q]}$. The lattice-point estimate just proved, applied on successive Euclidean
shells, shows that as $q\to\infty$ the original theta sum with the zero term removed is a
polynomial times $e^{-c q^{2/[K:\mathbf Q]}}$, uniformly in the shape variable.

As $q\to0$, apply (4.6) with $L=\mathfrak m_0\mathfrak a$. The same lattice-point estimate on
the dual lattice shows that the sum of its nonzero terms is a polynomial times
$e^{-c q^{-2/[K:\mathbf Q]}}$, uniformly on the compact shape space. The zero dual vector gives

$$
\Theta^*_{\mathfrak a,\epsilon}(t)
=\frac{\widehat\Phi_\epsilon(0)}
{\operatorname{covol}(\mathfrak m_0\mathfrak a)}q^{-1}
-\delta_{0\in A_{\mathfrak a}}\Phi_\epsilon(0)
+O(e^{-cq^{-2/[K:\mathbf Q]}})
\tag{4.16}
$$

after allowing an irrelevant polynomial factor inside the exponentially decreasing error. The
constant $c>0$ can be chosen uniformly on the shape space. Equations (4.7) and (4.16) are the
entire singularity calculation.

Split the radial integral at $q=1$. On $(0,1)$ subtract the two displayed elementary terms; on
$(1,\infty)$ use exponential decay. The remainders have entire Mellin transforms. Thus
$J_{\mathfrak a,\epsilon}(s)$ continues meromorphically to the plane, with possible simple poles
only at $s=1$ and $s=0$. At $s=1$, only $\epsilon=0$ has a pole. If $V_U>0$ is the volume of
the compact shape fundamental domain, then

$$
\operatorname*{res}_{s=1}J_{\mathfrak a,0}(s)
=\frac{V_U\widehat\Phi_0(0)}
{\operatorname{covol}(\mathfrak m_0\mathfrak a)}.
\tag{4.17}
$$

The number in (4.17) is positive. Since $G_0(1)>0$, (4.9), (4.15), and (4.17) give

$$
\operatorname*{res}_{s=1}\zeta_c(s)
=R_{K,\mathfrak m}
=\frac{2^{-r_1}V_U\widehat\Phi_0(0)}
{hG_0(1)c_KN\mathfrak m_0}>0.
\tag{4.18}
$$

Most importantly, $R_{K,\mathfrak m}$ is independent of $c$: the factor
$N\mathfrak a$ in (4.15) cancels the factor $N\mathfrak a$ in the lattice covolume. Formula
(4.18) is both the equal-residue calculation and the proof of residue positivity. It also shows
that the sum of all ray partial zeta functions, namely the Dedekind zeta function with the
primes dividing $\mathfrak m_0$ omitted, has a simple pole at $1$ with positive residue. Taking
$\mathfrak m_0=(1)$, while retaining all real places in $\mathfrak m_\infty$, gives the same
conclusion for $\zeta_K(s)$ itself. No prime-distribution statement has entered.

**Step 5: holomorphy and nonvanishing of finite-order $L$-functions.** By the finite-order
Hecke-character dictionary of Book 6, $\chi$ factors through some $C_{\mathfrak m}$. With the
finite conductor primes omitted, its ideal $L$-series is

$$
L_{\mathfrak m}(s,\chi)
=\sum_{c\in C_{\mathfrak m}}\chi(c)\zeta_c(s).
\tag{4.19}
$$

If $\chi\ne1$, character orthogonality gives

$$
\sum_{c\in C_{\mathfrak m}}\chi(c)=0.
$$

The equal residues in (4.18) therefore cancel in (4.19), so
$L_{\mathfrak m}(s,\chi)$ is holomorphic at $s=1$. For the trivial character, (4.18) gives one
simple pole with positive residue.

We next prove, rather than assume, nonvanishing at $1$. Suppose $\chi$ has order $m>1$. Lemma
6.2 of Book 6, together with its arithmetic-Frobenius normalization in Section 8.1, attaches to
it a cyclic extension $F/K$ of degree $m$ and a faithful character of
$\operatorname{Gal}(F/K)$ whose value at every unramified prime is $\chi(\mathfrak p)$. Choose
a finite set $S$ containing all primes ramified in $F$ and all primes omitted from (4.19), and
omit the primes of $F$ above $S$ as well. For $\Re(s)>1$ one has the Euler-factor identity

$$
\zeta_{F,S_F}(s)
=\prod_{j=0}^{m-1}L_S(s,\chi^j).
\tag{4.20}
$$

Here is the prime-by-prime verification. If $\mathfrak p\notin S$ has Frobenius of order $d$,
then it has $m/d$ primes in $F$, all of residue degree $d$, so its factor on the left is

$$
(1-(N\mathfrak p)^{-ds})^{-m/d}.
$$

Because $\chi$ is faithful, the numbers $\chi(\operatorname{Frob}_{\mathfrak p})^j$ run through
all $d$th roots of unity, each $m/d$ times. Hence the product of the factors on the right is the
same, using

$$
\prod_{\zeta^d=1}(1-\zeta X)=1-X^d.
$$

This proves (4.20) without any assertion about how often a Frobenius element occurs.

Every factor $L_S(s,\chi^j)$ for $1\le j<m$ is holomorphic at $1$ by (4.19). The theta
calculation applied over $F$ and over $K$ shows that both $\zeta_{F,S_F}$ and
$L_S(s,1)=\zeta_{K,S}$ have simple poles with positive residues. Dividing (4.20) by its trivial
factor and taking $s\to1$ gives

$$
\prod_{j=1}^{m-1}L_S(1,\chi^j)
=\frac{\operatorname*{res}_{s=1}\zeta_{F,S_F}(s)}
{\operatorname*{res}_{s=1}\zeta_{K,S}(s)}>0.
\tag{4.21}
$$

No factor on the left can therefore vanish. In particular,

$$
L_S(1,\chi)\ne0.
\tag{4.22}
$$

Adding back or deleting finitely many Euler factors multiplies the value at $1$ by nonzero
numbers, so (4.22) has exactly the conductor-omitted form required in the lemma.

**Step 6: pass from $L$-functions to prime sums.** For $\Re(s)>1$, the absolutely convergent
Euler product gives

$$
\log L_S(s,\chi)
=\sum_{\mathfrak p\notin S}\sum_{r\ge1}
\frac{\chi(\mathfrak p)^r}{r(N\mathfrak p)^{rs}}.
\tag{4.23}
$$

The terms with $r\ge2$ are uniformly bounded for real $s\ge1$, because

$$
\sum_{\mathfrak p}\sum_{r\ge2}
\frac1{r(N\mathfrak p)^r}<\infty.
\tag{4.24}
$$

Indeed, the left side of (4.24) is at most

$$
2\sum_{\mathfrak p}(N\mathfrak p)^{-2}
\le 2\sum_{\mathfrak a\ne0}(N\mathfrak a)^{-2}<\infty;
$$

the last convergence also follows from the lattice estimate in Step 3. If $\chi\ne1$,
holomorphy and (4.22) give a nonvanishing neighborhood of $1$, so an analytic logarithm of
$L_S(s,\chi)$ is bounded there. Equations (4.23)--(4.24) give

$$
\sum_{\mathfrak p\notin S}
\chi(\mathfrak p)(N\mathfrak p)^{-s}=O(1).
$$

For $\chi=1$, the positive residue calculation gives

$$
L_S(s,1)=\frac{R}{s-1}+O(1),
\qquad R>0,
$$

and hence

$$
\log L_S(s,1)=\log(1/(s-1))+O(1).
$$

Using (4.23)--(4.24) again proves the trivial-character line. The finite omitted set contributes
only $O(1)$. This completes the proof of the lemma. $\square$

The proof uses no unproved holomorphy of general Artin $L$-functions. Only one-dimensional
finite-order characters occur. Poisson summation and Mellin unfolding prove their behavior at
$1$; Book 6 is used only for finite-character existence and the translation between Hecke
characters and cyclic Galois characters.

### 4.3 The abelian density theorem

Let $M/K$ be finite abelian with group $G$. For an unramified prime, Frobenius is an element of
$G$, not merely a conjugacy class.

**Theorem 4.2 (abelian Chebotarev).** For every $g\in G$, the set of unramified primes with
$\operatorname{Frob}_{\mathfrak p}=g$ has Dirichlet density $1/|G|$.

**Proof.** Character orthogonality gives the indicator identity

$$
1_{\{g\}}(h)
=\frac1{|G|}\sum_{\chi\in\widehat G}
\overline{\chi(g)}\chi(h).
$$

Finite Artin reciprocity and the finite-character dictionary of Book 6 identify each character
of $G$ with a finite-order Hecke character of $K$ whose value at an unramified prime is
$\chi(\operatorname{Frob}_{\mathfrak p})$. Summing the indicator identity over primes yields

$$
P_{S_g}(s)
=\frac1{|G|}\sum_{\chi\in\widehat G}
\overline{\chi(g)}
\sum_{\mathfrak p}
\chi(\mathfrak p)(N\mathfrak p)^{-s}+O(1),
$$

where the $O(1)$ absorbs the finite ramified set. Lemma 4.1 shows that only the trivial
character contributes a logarithmic singularity. Therefore

$$
P_{S_g}(s)
=\frac1{|G|}\log(1/(s-1))+O(1),
$$

which is the claimed density. $\square$

The density is positive, so every Frobenius element occurs at infinitely many primes and outside
every prescribed finite set.

### 4.4 Reduction from a conjugacy class to a cyclic subgroup

The nonabelian theorem follows by passing to the cyclic subgroup generated by one element of the
desired class. The only subtlety is counting degree-one primes in the intermediate field.

Let $M/K$ be Galois with group $G$, choose $g\in G$, let $H=\langle g\rangle$, and put
$E=M^H$. Then $M/E$ is cyclic. A prime $\mathfrak q$ of $E$ unramified in $M$ with
$\operatorname{Frob}_{\mathfrak q}=g$ lies over a prime $\mathfrak p$ of $K$. If
$f(\mathfrak q/\mathfrak p)=1$, functoriality of arithmetic Frobenius says that the Frobenius at
$\mathfrak p$, viewed in $G$, is conjugate to $g$.

Primes of $E$ having residue degree at least two over $K$ have Dirichlet density zero when
measured by their norms in $E$. Indeed, if $\mathfrak q\mid\mathfrak p$ has residue degree at
least two, then

$$
N_E\mathfrak q\ge (N_K\mathfrak p)^2,
$$

and at most $[E:K]$ primes of $E$ lie above one $\mathfrak p$. Hence their prime sum is bounded
by

$$
[E:K]\sum_{\mathfrak p}(N_K\mathfrak p)^{-2s},
$$

which is bounded at $s=1$. Thus degree-one primes account for the whole logarithmic term.

We also need the multiplicity. Fix an unramified $\mathfrak p$ with Frobenius class $C$ of $g$.
Choose a prime $w$ of $M$ above $\mathfrak p$ whose Frobenius is exactly $g$; then its
decomposition group is $H$. The primes of $E$ above $\mathfrak p$ correspond to the $H$-orbits
on $G/H$. A degree-one prime is a fixed coset $xH$, and at the prime $x^{-1}w$ above it the
relative Frobenius in $M/E$ is $x^{-1}gx$. Thus it equals the chosen element $g$ exactly when

$$
x^{-1}gx=g.
$$

The number of such cosets is

$$
\frac{|C_G(g)|}{|H|}.
$$

Indeed the set of $x$ satisfying the displayed equation is $C_G(g)$, and right multiplication
by $H$ gives the same prime of $E$. It preserves the equation because
$H=\langle g\rangle$ centralizes $g$. Thus the division by $|H|$ is exact.

Combining the degree estimate and this multiplicity gives the prime-sum identity

$$
\sum_{\substack{\mathfrak q\text{ prime of }E\text{ unramified in }M\\
\operatorname{Frob}_{\mathfrak q}=g}}
(N_E\mathfrak q)^{-s}
=\frac{|C_G(g)|}{|H|}P_{S_C(M/K)}(s)+O(1)
\qquad(s\to1^+).
\tag{4.25}
$$

The $O(1)$ consists exactly of the finitely many ramified primes and the
residue-degree-at-least-two primes already bounded above.

### 4.5 Chebotarev's theorem and its selection forms

We can now state the form used throughout the book.

**Theorem 4.3 (Chebotarev density theorem).** Let $M/K$ be a finite Galois extension with group
$G$, and let $C\subset G$ be a conjugacy class. Then

$$
\delta(S_C(M/K))=\frac{|C|}{|G|}.
$$

**Proof.** Choose $g\in C$, set $H=\langle g\rangle$, and $E=M^H$. By Theorem 4.2 applied to
the cyclic extension $M/E$, primes $\mathfrak q$ of $E$ with Frobenius $g$ have density
$1/|H|$. Removing the residue-degree-at-least-two primes changes the prime sum by a bounded
amount. Formula (4.25), including its converse multiplicity count and the equality of norms at
residue degree one, therefore gives

$$
\frac1{|H|}
=\frac{|C_G(g)|}{|H|}\,\delta(S_C(M/K)).
$$

Therefore

$$
\delta(S_C(M/K))=\frac1{|C_G(g)|}=\frac{|C|}{|G|}.
$$

$\square$

Four selection corollaries will be used repeatedly.

**Corollary 4.4 (avoidance of finitely many places).** Every conjugacy class occurs at
infinitely many unramified primes outside any prescribed finite set.

**Proof.** The density in Theorem 4.3 is positive, while a finite set has density zero.
$\square$

**Corollary 4.5 (simultaneous splitting and Frobenius).** Let $A/K$ and $B/K$ be finite Galois
extensions with $A\cap B=K$. Given a conjugacy class $C\subset\operatorname{Gal}(A/K)$, there
are infinitely many primes that split completely in $B$ and have Frobenius class $C$ in $A$.

**Proof.** Linear disjointness gives

$$
\operatorname{Gal}(AB/K)
\simeq
\operatorname{Gal}(A/K)\times\operatorname{Gal}(B/K).
$$

Apply Theorem 4.3 to the conjugacy class $C\times\{1\}$. $\square$

**Corollary 4.6 (generation by Frobenius witnesses).** Let $G$ be a finite group. Choose
conjugacy classes $C_1,\ldots,C_r$ such that no proper subgroup of $G$ meets all of them up to
conjugacy. For a Galois extension $M/K$ with group $G$, one may choose distinct unramified primes
$v_i$ with $\operatorname{Frob}_{v_i}\in C_i$. Any subgroup of $G$ containing representatives
of all the resulting classes is $G$.

**Proof.** Choose the primes successively using Corollary 4.4. The final assertion is exactly the
defining property of the classes. $\square$

**Corollary 4.7 (compatible fixed-field and character selection).** Let $M/K$ be finite Galois
with group $G$, choose $c\in G$, and fix finitely many pairs $(H,\theta)$ with

$$
H\le G,
\qquad
\theta:H\longrightarrow\mathbf C^\times
$$

one-dimensional. Outside any prescribed finite set, there are infinitely many primes
$\mathfrak p$ with Frobenius class $[c]$. For each one, choose a prime $w$ of $M$ above
$\mathfrak p$ whose arithmetic Frobenius is exactly $c$; such a choice is possible because the
Frobenius elements above $\mathfrak p$ form $[c]$. Then, simultaneously for all $H$:

1. the primes of $M^H$ above $\mathfrak p$ are the orbits of $\langle c\rangle$ on $G/H$;
2. the residue degree of the prime indexed by the orbit of $xH$ is its orbit length $f$;
3. the orbit of $xH$ corresponds to the prime
   $\mathfrak q=x^{-1}w|_{M^H}$, and, at the prime $x^{-1}w$ of $M$ above it, arithmetic
   Frobenius in the upper extension $M/M^H$ is
   $$
   x^{-1}c^fx\in H,
   $$
   and the corresponding character value is
   $$
   \theta(x^{-1}c^fx).
   $$
4. if $H_1\le H_2$ occur in the list, the natural map
   $G/H_1\to G/H_2$ sends each orbit to the restricted prime in
   $M^{H_2}\subset M^{H_1}$. If the two orbit lengths are $f_1$ and $f_2$, then
   $f_2\mid f_1$ and
   $$
   \left(x^{-1}c^{f_2}x\right)^{f_1/f_2}=x^{-1}c^{f_1}x,
   $$
   which is the tower-compatibility relation for the two relative Frobenius elements.

If $B/K$ is finite Galois and $M\cap B=K$, the same primes may additionally be required to split
completely in $B$.

**Proof.** The first assertion is Corollary 4.4. With the chosen $w$, the decomposition group is
$\langle c\rangle$, so Theorem 3.1 says that its orbits on $G/H$ give the primes and their
lengths give residue degrees. The orbit of $xH$ is the embedding description of
$x^{-1}w|_{M^H}$. If $f$ is its length, then $c^fxH=xH$, hence
$x^{-1}c^fx\in H$. Since $N\mathfrak q=(N\mathfrak p)^f$, functoriality of arithmetic
Frobenius in the residue-field tower identifies $x^{-1}c^fx$ with the relative Frobenius at
$x^{-1}w$ in $M/M^H$; applying $\theta$ gives the displayed value. Replacing the chosen prime
above $\mathfrak q$ conjugates this element inside $H$, which does not change a one-dimensional
character value. For $H_1\le H_2$, the map of coset sets is exactly the localization of the
field inclusion by Theorem 3.1. Its image orbit length $f_2$ divides $f_1$, and the displayed
power identity follows immediately; it is also the usual Frobenius law in the corresponding
residue-field tower. For the final assertion, apply Corollary 4.5 to $M$ and $B$, using the
class $[c]\times\{1\}$ in the product Galois group. $\square$

For Hilbert specialization one often chooses one class avoiding each conjugacy class of maximal
proper subgroups. The derangement argument in Book 152 constructs such classes, while
Chebotarev chooses arithmetic primes that realize them in a fixed Galois extension. These are
different uses of Frobenius and should not be conflated with the finite-field point-counting
step inside the proof of Hilbert irreducibility.

## 5. Specialization homomorphisms

We now return from fixed extensions to moving covers. A Galois cover packages far more than an
irreducible polynomial: every rational point of the base produces a homomorphism from an
absolute Galois group to the generic deck group. Surjectivity controls the normal closure, while
restriction to local absolute Galois groups controls completions. This is the mechanism that
ordinary root-field approximation does not retain.

### 5.1 A Galois cover as a family of homomorphisms

Let $K$ be a number field, let $H$ be a geometrically integral $K$-variety, and let

$$
\widetilde T\longrightarrow H
$$

be a connected finite étale Galois cover with deck group $G$. For $h\in H(K)$, the geometric
fiber $\widetilde T_{\bar h}$ is a simply transitive $G$-set. Choose a point $\tilde t$ in the
fiber. The absolute Galois group acts on the fiber and commutes with the deck action, so there is
a unique continuous homomorphism

$$
\rho_h:G_K\longrightarrow G
$$

such that

$$
\sigma(\tilde t)=\rho_h(\sigma)\tilde t.
$$

Changing $\tilde t$ conjugates $\rho_h$. Thus the intrinsic datum is the conjugacy class of the
homomorphism. Let

$$
G_h=\rho_h(G_K).
$$

The finite étale fiber is connected if and only if $G_K$ acts transitively on its geometric
points. Since the deck action is simply transitive, this is equivalent to $G_h=G$. In that case
the coordinate algebra of the fiber is a Galois field $M_h/K$ with group $G$.

Now let $J\le G$. The quotient

$$
T=\widetilde T/J\longrightarrow H
$$

is finite étale of degree $[G:J]$, and its geometric fiber is the $G$-set $G/J$. If
$\rho_h$ is surjective, then $T_h$ is connected and is the spectrum of

$$
L_h=M_h^J.
$$

The normal closure of $L_h/K$ inside the coordinate field of $\widetilde T_h$ is all of $M_h$
exactly when the action on $G/J$ is faithful, or equivalently

$$
\operatorname{core}_G(J)=1.
$$

This core-free condition will be included whenever $T_h$ is called the root field of the top
fiber.

### 5.2 Connected fibers and full monodromy

A connected fiber of $T\to H$ says only that $G_h$ acts transitively on $G/J$. It need not say
$G_h=G$. The difference is essential. For instance, $A_n$ is transitive in the natural
$S_n$-action, so an irreducible polynomial can have Galois group $A_n$ rather than $S_n$.

Book 152 proves that full monodromy is a Hilbert condition. We recall the argument because it
will be combined with base change. For each conjugacy class of maximal proper subgroups
$Q\subsetneq G$, form the quotient cover

$$
\widetilde T/Q\longrightarrow H.
$$

If $G_h$ were contained in a conjugate of $Q$, it would fix a point of $G/Q$, and the
specialized quotient fiber would have a $K$-rational component. Conversely, requiring suitable
resolvent fibers to remain connected rules out every maximal proper subgroup. There are only
finitely many $Q$, so the intersection of the resulting Hilbert conditions is again a Hilbert
subset.

**Proposition 5.1 (full-monodromy specialization).** Let $H$ be a nonempty open of affine
space over $K$, and let $\widetilde T\to H$ be a geometrically connected finite étale Galois
cover with group $G$. Given finitely many places $v$ and nonempty opens $V_v\subset H(K_v)$,
there is an $h\in H(K)$ lying in every $V_v$ for which $\widetilde T_h$ is connected. The set of
such $h$ is dense in the product of the $V_v$.

**Proof.** Apply the simultaneous-cover form of Hilbert irreducibility from Book 152 to the
finite list of maximal-subgroup resolvent covers. A specialization satisfying all the resolvent
conditions has image in no maximal proper subgroup, hence its image is $G$. Local approximation
is part of the same theorem. $\square$

The hypothesis that the cover is geometrically connected removes constant-field obstructions.
If the field of constants were $C\supsetneq K$, every specialized top field would contain a copy
of $C$, and disjointness from a field containing $C$ would be impossible.

### 5.3 Equivariant local constancy

The local completion of a specialized Galois field is determined by the restriction of
$\rho_h$ to $G_{K_v}$. The restriction is locally constant in $h$.

**Proposition 5.2 (equivariant local constancy).** Let $k$ be a completion of a number field,
let $H/k$ be a smooth variety, and let $\widetilde T\to H$ be a finite étale $G$-torsor. For
every $b\in H(k)$ there is an open neighborhood $V$ of $b$ such that the fibers
$\widetilde T_h$ and $\widetilde T_b$ are isomorphic as finite étale $G$-schemes for every
$h\in V$.

**Proof strategy.** Étale morphisms are locally products in the nonarchimedean and real analytic
topologies. Because the fiber is finite, the neighborhoods can be intersected over all sheets,
and uniqueness makes the local identifications respect the $G$-action.

**Proof.** At a nonarchimedean place, choose étale coordinates around $b$ and around every point
of the finite fiber after passing to a finite splitting extension. Each sheet is cut out by a
simple system of equations. Hensel's lemma continues that sheet uniquely for $h$ in a small
neighborhood. Shrinking once makes the continued sheets disjoint and exhausts the degree of the
cover. If a deck transformation carries one sheet to another at $b$, uniqueness of the Hensel
continuation makes it carry the continued sheet to the corresponding continued sheet. The
identification is therefore $G$-equivariant and descends from the splitting extension.

At a real place the same proof uses the inverse function theorem; nonreal sheets occur in
conjugate pairs and cannot change type away from a collision. At a complex place finite étale
fibers are already split and ordinary analytic continuation applies. $\square$

Choose a geometric point in the local fiber. Proposition 5.2 says that on $V$ the local
homomorphisms

$$
\rho_h|_{G_k}:G_k\longrightarrow G
$$

are conjugate. Hence the image $D$, the image of inertia $I$, the completed Galois field, and the
local algebras of every quotient $G/H$ are constant. This is much stronger than preservation of
one factorization partition.

### 5.4 Resolvents and base-changed connectedness

Let $D/K$ now denote a finite extension to be avoided; to prevent conflict with decomposition
groups we shall sometimes call it $D_{\mathrm{av}}$. Since
$\widetilde T\to H$ is geometrically connected, its base change to $D$ remains connected. Book
152's descent of Hilbert conditions shows that the set of $K$-points $h$ for which

$$
\widetilde T_h\otimes_KD
$$

is connected is a Hilbert subset of $H(K)$. When $\widetilde T_h=\operatorname{Spec}M_h$, this
connectedness means that $M_h\otimes_KD$ is a field, hence that $M_h$ and $D$ are linearly
disjoint.

**Proposition 5.3 (closure-level avoidance).** In Proposition 5.1 one may additionally require
that the specialized Galois field $M_h$ be linearly disjoint from any prescribed finite
extension $D/K$.

**Proof.** Replace $D$ by its normal closure. Add to the full-monodromy Hilbert conditions the
connectedness condition for $\widetilde T_D\to H_D$, descended to $K$. The finite intersection
is a Hilbert subset and therefore meets the prescribed local box. The specialized top fiber
remains connected over $D$, which is the required linear disjointness. $\square$

This proposition controls the normal closure because the Galois closure was present in the
family before specialization. Applying the root-cover condition after ordinary Moret--Bailly
would control only $L_h\otimes_KD$.

## 6. Galois approximation data

We can now isolate the precise extra input required for a Galois refinement. The definition may
look elaborate, but every clause answers one of the failures from Chapter 1. Its advantage is
that the main theorem becomes a direct and verifiable application of Hilbert irreducibility.

### 6.1 The definition and the role of each clause

Let $X/K$ be a variety. A **Galois approximation datum for $X$** consists of:

1. a nonempty open $H\subset\mathbf A^N_K$;
2. a geometrically connected finite étale Galois cover
   $$
   \widetilde T\longrightarrow H
   $$
   with finite group $G$;
3. a core-free subgroup $J\le G$ and the quotient
   $$
   T=\widetilde T/J;
   $$
4. a $K$-morphism
   $$
   e:T\longrightarrow X;
   $$
5. for every controlled place $v$, a point $b_v\in H(K_v)$ and a nonempty neighborhood
   $V_v\subset H(K_v)$ on which both the local $G$-torsor and the evaluated points have the
   required behavior.

The datum has **degree** $n=[G:J]$. The quotient fiber $T_h$ will become the chosen field of
definition of the evaluated point, the top fiber $\widetilde T_h$ its normal closure, and $e$
the point on $X$. We often call that chosen field the **point field**, but this terminology does
not assert that it is the minimal residue field of the image point. If exact residue degree is
needed, the presentation must also ensure that the evaluated point does not descend to a proper
subfield; this is a separate evaluation check recorded in Section 14.3. Core-freeness ensures
that the normal closure of the quotient field is genuinely the top field rather than a proper
quotient of it.

For a local point $b_v$, choose a geometric point of the top fiber and let

$$
\phi_v:G_{K_v}\longrightarrow G
$$

be the resulting local homomorphism, defined up to conjugacy. Its image and inertia image will
be denoted

$$
D_v=\phi_v(G_{K_v}),
\qquad
I_v=\phi_v(I_{K_v}).
$$

The local root algebra is the finite étale algebra attached to the $D_v$-set $G/J$. The full
top algebra is attached to the regular $D_v$-set $G$. Thus the datum records both at once.

### 6.2 Local realizability

An abstract pair $I_v\triangleleft D_v\le G$ is not enough. Local Galois groups satisfy strong
constraints: $D_v/I_v$ is cyclic; tame inertia has a constrained semidirect action by
Frobenius; wild inertia is a residue-characteristic group; and the desired point must exist on
every field factor of the quotient algebra. The point $b_v$ is the certificate that all these
conditions are simultaneously realizable in the chosen family.

More explicitly, the local fiber gives a finite étale $K_v$-algebra

$$
(T_{b_v})=
\prod_{D_vgJ\in D_v\backslash G/J}
E_{v,g},
$$

where

$$
[E_{v,g}:K_v]
=[D_v:D_v\cap gJg^{-1}].
$$

The evaluation map supplies a point of

$$
X(T_{b_v})=\prod_gX(E_{v,g}).
$$

A required local condition is **realized** if this point belongs to the desired open subset and
if the top $G$-torsor has the intended conjugacy class of $\phi_v$. Proposition 5.2 then
produces $V_v$ on which both facts persist.

At a split place, take $\phi_v$ trivial. Then both the top and every quotient fiber are split,
and $V_v$ may be chosen so that all evaluated conjugates lie in one prescribed open
$\Omega_v\subset X(K_v)$.

### 6.3 Avoidance fields and constant fields

Let $D_{\mathrm{av}}/K$ be the finite Galois compositum of every field that the top closure must
avoid. No separate generic-disjointness hypothesis is needed when $\widetilde T$ is geometrically
connected: its function field is regular over $K$, so

$$
K(\widetilde T)\otimes_KD_{\mathrm{av}}
$$

is a field. This is precisely the generic connectedness needed for the base-changed Hilbert
condition.

If the cover is connected but not geometrically connected, let $C$ be the algebraic closure of
$K$ in $K(\widetilde T)$. Then $C\ne K$ is contained in every sufficiently good top
specialization. Avoidance of a field containing $C$ is impossible. One can sometimes replace
$K$ by $C$ or separate the constant quotient, as in Book 152, but the simple theorem below uses
geometric connectedness to avoid hidden constants altogether.

### 6.4 Solvable bridge data

A Galois approximation datum is a **solvable bridge datum** if the sheet stabilizer $J$ is
solvable. This condition concerns the upper extension

$$
M_h/L_h
$$

because its Galois group is $J$. It places no solvability condition on $G$ or on $L_h/K$.

The distinction is deliberate. Brauer descent is most useful when $G$ is nonsolvable; it then
uses elementary subgroups $H\le G$. At the same time, one may need to move an object already
known over $L_h$ up to $M_h$ through cyclic steps. Solvability of $J$ supplies exactly that
upper path.

**Lemma 6.1.** If $J$ is finite solvable, there is a chain

$$
J=J_0\triangleright J_1\triangleright\cdots\triangleright J_r=1
$$

such that every $J_i/J_{i+1}$ is cyclic of prime order. The reversed fixed-field chain

$$
L_h=M_h^{J_0}
\subset M_h^{J_1}\subset\cdots\subset M_h^{J_r}=M_h
$$

is therefore a tower of cyclic Galois extensions of prime degree.

**Proof.** Suppose $J\ne1$, and choose a maximal proper normal subgroup $N\triangleleft J$.
The quotient $J/N$ is nontrivial, simple, and solvable. A nontrivial simple solvable group is
abelian: otherwise its commutator subgroup would be the whole group, so its derived series could
never reach $1$. A finite simple abelian group is cyclic of prime order. Thus

$$
J/N\simeq C_p
$$

for some prime $p$. The subgroup $N$ is again solvable and has smaller order. Induction on
$|J|$ gives a subnormal series for $N$ with cyclic prime-order quotients; adjoining $J$ at the
front gives the required series for $J$. Galois correspondence reverses its normal inclusions
and identifies each successive Galois group with the corresponding quotient. $\square$

Thus “solvable bridge” has a concrete operational meaning. It is not shorthand for a field of
solvable degree.

## 7. The Galois-refined approximation theorem

We now prove the central theorem. All difficult geometry is isolated in the existence of the
Galois approximation datum, just as Book 153 isolates its geometry in a simultaneous moving
presentation. Once the datum exists, local topology, full monodromy, and closure-level
disjointness are compatible Hilbert conditions on one affine parameter space.

### 7.1 Statement

**Theorem 7.1 (Galois-refined arithmetic approximation).** Let $K$ be a number field, let
$X/K$ be a variety, and let

$$
(H,\widetilde T,G,J,T,e)
$$

be a Galois approximation datum for $X$. Let $S$ be a finite set of places. At every $v\in S$,
choose a realized local point $b_v\in H(K_v)$ and a sufficiently small nonempty neighborhood
$V_v$ on which the local $G$-torsor and the evaluated point condition are constant. Let
$D_{\mathrm{av}}/K$ be finite.

Then there exists $h\in H(K)$ such that, writing

$$
\widetilde T_h=\operatorname{Spec}M,
\qquad
T_h=\operatorname{Spec}L,
$$

the following hold.

1. $M/K$ is Galois with a specified isomorphism
   $$
   \operatorname{Gal}(M/K)\simeq G.
   $$
2. $L=M^J$, $[L:K]=[G:J]$, and $M$ is the normal closure of $L/K$.
3. The evaluation map gives a point
   $$
   x\in X(L).
   $$
4. $M$ is linearly disjoint from $D_{\mathrm{av}}$ over $K$.
5. For every $v\in S$, the restriction homomorphism
   $$
   G_{K_v}\longrightarrow G
   $$
   is conjugate to the prescribed $\phi_v$. Hence the top completion, the root algebra
   $L\otimes_KK_v$, and the localized point all have the prescribed isomorphism class.

The set of such $h$ is dense in $\prod_{v\in S}V_v$ and is not thin in $H(K)$.

If $J$ is solvable, then $M/L$ is solvable Galois and comes with a prime-cyclic tower as in
Lemma 6.1.

### 7.2 Proof

**Proof strategy.** There are three independent requirements on the parameter. Membership in
$V_v$ is local and open. Surjectivity of the specialization homomorphism is a Hilbert condition
detected by the finite list of maximal-subgroup resolvents. Disjointness of the top field from
$D_{\mathrm{av}}$ is connectedness of the top fiber after base change. Book 152 allows their
finite intersection to meet every local box.

**Proof.** Replace $D_{\mathrm{av}}$ by its normal closure. Let $\mathcal H_G\subset H(K)$ be
the Hilbert subset on which the top fiber has full monodromy $G$, supplied by Proposition 5.1.
Because $\widetilde T$ is geometrically connected, the base-changed cover

$$
\widetilde T_{D_{\mathrm{av}}}\longrightarrow H_{D_{\mathrm{av}}}
$$

is connected. Let $\mathcal H_D$ be the Hilbert subset, descended to $K$, on which its
specialized fiber remains connected. By finite-intersection stability,

$$
\mathcal H=\mathcal H_G\cap\mathcal H_D
$$

is a Hilbert subset of $H(K)$. Hilbert irreducibility with local approximation gives

$$
h\in\mathcal H\cap\bigcap_{v\in S}V_v.
$$

Since $h\in\mathcal H_G$, the top fiber is a connected finite étale $G$-torsor over $K$.
Therefore it is $\operatorname{Spec}M$ for a Galois field $M/K$ with group $G$. Quotienting the
fiber by $J$ gives

$$
T_h=\operatorname{Spec}M^J,
$$

so put $L=M^J$. Core-freeness of $J$ says that the action of $G$ on $G/J$ is faithful, hence
the conjugates of $L$ generate $M$. Thus $M$ is the normal closure of $L$.

The specialized evaluation map

$$
T_h\longrightarrow X
$$

is exactly an $L$-point $x$ of $X$. Since $h\in\mathcal H_D$, the algebra

$$
M\otimes_KD_{\mathrm{av}}
$$

is connected and finite étale, hence a field. Thus $M$ and $D_{\mathrm{av}}$ are linearly
disjoint.

Finally, $h\in V_v$ for every $v$. Equivariant local constancy identifies the local top fibers
as $G$-torsors, so the local homomorphism is conjugate to $\phi_v$. Passing to the quotient by
$J$ identifies the root algebras and the evaluated points. This proves all five conclusions.

Density follows by beginning with arbitrary smaller local neighborhoods. To see that the set is
not thin, suppose it were thin. Book 152's thin--Hilbert dictionary provides finitely many
additional connected-cover conditions avoiding it. Intersect those with $\mathcal H$ and the
same local boxes. Hilbert approximation would produce a parameter having all conclusions but
outside the supposed set of all such parameters, a contradiction.

If $J$ is solvable, Galois correspondence and Lemma 6.1 give the asserted tower. $\square$

### 7.3 Exact local completions

The local conclusion deserves to be read at all levels. Fix $v\in S$ and choose a place $w$ of
$M$ above $v$. If the prescribed local homomorphism has image $D_v$ and inertia image $I_v$,
then

$$
\operatorname{Gal}(M_w/K_v)\simeq D_v,
\qquad
I(M_w/K_v)\simeq I_v.
$$

For the point field,

$$
L\otimes_KK_v
\simeq
\prod_{D_vgJ\in D_v\backslash G/J}
M_w^{D_v\cap gJg^{-1}}.
$$

The evaluated point $x$ has one component over each factor, and local constancy puts the entire
tuple in the prescribed open of $X(L\otimes_KK_v)$. For every further subgroup $H\le G$, the
same top completion gives

$$
M^H\otimes_KK_v
\simeq
\prod_{D_vgH\in D_v\backslash G/H}
M_w^{D_v\cap gHg^{-1}}.
$$

Thus the theorem does not merely preserve a completion of $L$; it preserves the compatible
completion diagram of every fixed field.

At an unramified prescribed place, $I_v=1$ and a Frobenius element $c_v\in D_v$ is defined up to
conjugacy. Its cycle structure on $G/J$ gives the factorization partition of $L$, while its
cycle structure on $G/H$ gives the partition in $M^H$. One conjugacy class therefore controls
all quotient fields simultaneously.

After the specialization has fixed $M$, the same conclusion is available at new auxiliary
places rather than only at the places built into the local box. Corollary 4.7 selects infinitely
many primes outside $S$ with any prescribed class $[c]\subset G$ and gives, in one calculation,
the factors and upper character values for every fixed field in a finite subgroup list.
Corollary 4.6 lets finitely many such primes witness the full group. If an auxiliary prime must
also split in a Galois field $B$ disjoint from $M$, Corollary 4.5 imposes that condition at the
same time. None of these prime choices is used to construct or vary $M$.

### 7.4 Why this is stronger than Moret--Bailly

Book 153 starts from local points on a smooth geometrically connected variety and constructs a
moving incidence cover. Connectedness of its specialized degree-$d$ fiber produces $L$ and
connectedness after base change produces $L\cap D=K$. The generic Galois closure of that
incidence cover need not have a prescribed group, its sheet stabilizer need not be solvable, and
the theorem does not impose connectedness of the specialized Galois closure after base change.

Theorem 7.1 starts only after a stronger geometric presentation is supplied. It controls the
top Galois fiber itself. Therefore the implication

$$
\text{ordinary Moret--Bailly datum}
\Longrightarrow
\text{Galois approximation datum}
$$

is not asserted and is false without additional hypotheses. Exact degree can be obstructed by
the index of $X$; prescribed monodromy can be absent from the moving family; and a solvable
stabilizer can fail for group-theoretic reasons. The refinement is powerful precisely because
it states these extra inputs rather than hiding them.

## 8. Totally real and split refinements

Many applications need a totally real top field and complete splitting at all places carrying
delicate local conditions. These requirements fit especially well with Galois refinement:
trivial local torsors remain trivial in every quotient, and real split fibers force the top
field itself to be totally real.

### 8.1 Archimedean specialization data

Assume $K$ is totally real. At a real place $v$, the absolute Galois group has order two. A
local homomorphism

$$
G_{K_v}\simeq\{1,c\}\longrightarrow G
$$

is determined up to conjugacy by an element of $G$ of order at most two. The top algebra is
fully real exactly when this homomorphism is trivial. If it is nontrivial, the regular $G$-set
has no fixed points under its image, so the top algebra contains complex factors.

For total reality we therefore require a point $b_v\in H(\mathbf R)$ at which the top torsor is
split:

$$
\widetilde T_{b_v}\simeq\coprod_{g\in G}\operatorname{Spec}\mathbf R.
$$

The quotient fiber is then $\mathbf R^{[G:J]}$. If the evaluation of every quotient sheet lies
in a prescribed open $\Omega_v\subset X(\mathbf R)$, Proposition 5.2 preserves both splitness
and the open condition on a neighborhood $V_v$.

It is not enough that the quotient root algebra be real if one has not verified faithfulness.
In a genuine normal-closure datum core-freeness makes the action faithful, so trivial action on
all root sheets forces the top complex conjugation element to be trivial.

### 8.2 The totally real Galois theorem

**Theorem 8.1 (totally real Galois refinement).** In Theorem 7.1 assume that $K$ is totally
real, include every real place in $S$, and prescribe a split top fiber at each one. Then $M$,
$L$, and every intermediate field $M^H$ are totally real. Every real conjugate of the point
$x\in X(L)$ lies in its prescribed local open.

**Proof.** The local conclusion of Theorem 7.1 makes the restriction of the specialized
homomorphism to every real decomposition group trivial. Hence

$$
M\otimes_{K,v}\mathbf R\simeq\mathbf R^{|G|}
$$

for every real $v$ of $K$. This is exactly total reality of $M$. Subfields are totally real by
Proposition 3.5. The quotient $G/J$ identifies the real embeddings of $L$ with the evaluated
local sheets, all of which lie in the chosen open. $\square$

This proof is stronger than first showing that $L$ is totally real and then invoking
Proposition 3.5: it also labels the real top torsor and thereby controls every fixed field in the
same specialization.

### 8.3 Prescribed finite splitting

At a finite place $v$, complete splitting in $M$ is represented by the trivial local
homomorphism. It is locally realizable only if the chosen $G$-torsor has a split fiber over some
$b_v\in H(K_v)$. When it does, Theorem 7.1 gives

$$
M\otimes_KK_v\simeq K_v^{|G|}.
$$

Theorem 3.1 then gives, simultaneously for all $H\le G$,

$$
M^H\otimes_KK_v\simeq K_v^{[G:H]}.
$$

**Corollary 8.2.** Let $S_{\mathrm{split}}$ be a finite set of places at which a Galois
approximation datum has realized split top fibers. The specialized top field in Theorem 7.1 may
be chosen so that every $v\in S_{\mathrm{split}}$ splits completely in the top field and in
every member of its fixed-field family.

**Proof.** Include $S_{\mathrm{split}}$ among the controlled places and choose the local
neighborhoods supplied by Proposition 5.2 around the realized split fibers. Theorem 7.1 then
makes the specialized local homomorphism trivial at every such place. Hence the top field splits
completely there, and Proposition 3.3 propagates complete splitting to every fixed subfield.
$\square$

The corollary is not a consequence of Chebotarev: Chebotarev finds primes with a desired
Frobenius class after a field is fixed. Here the primes are fixed first and the field is varied.
Local realizability plus Hilbert approximation is the relevant mechanism.

Conversely, once the specialized $M$ is fixed, an *additional* prime may be required both to
have a chosen class in $M/K$ and to split completely in a Galois field $B/K$ with $M\cap B=K$;
that is precisely Corollary 4.5. The two assertions have opposite orders of quantifiers.

### 8.4 Ramified local prescriptions

Complete splitting is often stronger than needed. A ramified local condition can also be
preserved, but it must be specified at the top. Choose a local $G$-torsor whose homomorphism
$\phi_v$ has the desired image $D_v$ and inertia image $I_v$. Theorem 7.1 preserves its
isomorphism class. The completions of all subfields then follow from Theorem 3.1.

This formulation automatically enforces necessary compatibility. For example:

- $I_v\triangleleft D_v$;
- $D_v/I_v$ is cyclic;
- wild inertia is a residue-characteristic subgroup;
- the quotient action on $G/J$ gives a rank-$[G:J]$ algebra;
- the point exists on every factor of that algebra.

Writing down abstract subgroups with these elementary properties is still not sufficient: there
may be no local extension or no point in the selected family realizing them. The actual local
fiber remains part of the input.

If only an unramified factorization pattern in the root field is required, one may choose a
Frobenius class $C\subset G$ whose cycle lengths on $G/J$ give that partition. Two classes can
have the same cycle lengths, however, and can act differently on an elementary coset space
$G/H$. To control the full family, the class itself must be selected, not merely its cycle type
in one quotient.

The selection theorems of Chapter 4 apply only at primes unramified in the already fixed top
field. They cannot create a new ramified local homomorphism after specialization; the ramified
set of $M/K$ is already determined. Ramified requirements therefore belong in the local torsor
input of Theorem 7.1, exactly as above.

## 9. Solvable bridges to the normal closure

The purpose of a solvable bridge is to transport data upward from the point field to the Galois
top field through a sequence of cyclic extensions. This chapter identifies the controlling
group, proves the tower statement, and explains why the symmetric quintic action is the largest
generic symmetric action with a solvable point stabilizer.

### 9.1 Point stabilizers and the upper extension

Let $M/K$ be Galois with group $G$, and let $L=M^J$. The direction of Galois correspondence
gives

$$
\operatorname{Gal}(M/L)=J,
\qquad
[L:K]=[G:J].
$$

The extension $L/K$ is Galois exactly when $J$ is normal in $G$, in which case its group is
$G/J$. This is unrelated to whether $J$ is solvable. In the applications of this chapter,
$J$ is often not normal, so $L/K$ is non-Galois even though the upper extension $M/L$ is Galois
and solvable.

**Proposition 9.1.** The following are equivalent:

1. $M/L$ is solvable Galois;
2. $J$ is a solvable group;
3. there exists a tower
   $$
   L=L_0\subset L_1\subset\cdots\subset L_r=M
   $$
   in which every $L_{i+1}/L_i$ is cyclic Galois of prime degree.

**Proof.** The equivalence of 1 and 2 is the identification
$\operatorname{Gal}(M/L)=J$. Lemma 6.1 proves that 2 implies 3. Conversely, the Galois group of
the normal closure of a tower already contained in the Galois extension $M/L$ has a subnormal
series with cyclic prime quotients, so it is solvable; here that group is $J$ itself. More
directly, the fixed fields in the tower correspond to a subnormal chain in $J$, and the cyclic
prime steps give cyclic prime quotients. $\square$

The proposition shows why one must inspect the stabilizer. The degree $[L:K]$ is the index of
$J$, while solvability concerns $J$ itself.

### 9.2 Prime-cyclic towers

For later use, the tower should be compatible with conjugation and with local splitting. Choose
a subnormal series

$$
J=J_0\triangleright J_1\triangleright\cdots\triangleright J_r=1.
$$

Put $L_i=M^{J_i}$. Every $L_{i+1}/L_i$ is cyclic Galois of prime degree. If a place $v$ splits
completely in $M$, it splits completely in every $L_i$. If the top field is totally real, every
$L_i$ is totally real. If $M\cap D_{\mathrm{av}}=K$, then every $L_i\cap D_{\mathrm{av}}=K$.

These conclusions are simultaneous because all $L_i$ lie inside the already controlled $M$.
They need not remain true if one independently chooses a cyclic extension at each step and then
takes a compositum. The subgroup series makes the tower part of the fixed-field diagram from the
start.

At a non-split controlled place, the completion of each $L_i$ is determined by the double cosets
$D_v\backslash G/J_i$. Thus a local condition that must survive each cyclic layer can be checked
before specialization on this finite list of local algebras.

There is also a compatible auxiliary-prime statement for the whole tower. For each quotient
$J_i/J_{i+1}$ choose a faithful character and inflate it to

$$
\vartheta_i:J_i\longrightarrow\mu_{[J_i:J_{i+1}]},
\qquad \ker\vartheta_i=J_{i+1}.
$$

After $M$ is fixed, apply Corollary 4.7 once to the finite pairs $(J_i,\vartheta_i)$. A selected
top Frobenius class then determines simultaneously the primes and residue degrees in every
$L_i$, and the formula

$$
\vartheta_i(x^{-1}c^fx)
$$

is the Frobenius value in the cyclic layer $L_{i+1}/L_i$. Thus no separate Chebotarev choice
over the successive, generally different, base fields is required, and the chosen primes may be
kept outside every previously controlled place.

### 9.3 The symmetric quintic bridge

The most important example is the natural action of $S_5$ on five letters. Let

$$
G=S_5,
\qquad
J=S_4
$$

with $J$ the stabilizer of one letter. Then $J$ is core-free and solvable. Indeed

$$
1\triangleleft V_4\triangleleft A_4\triangleleft S_4
$$

can be refined to a subnormal series with cyclic prime quotients. If a specialization has root
field $L$ and symmetric normal closure $M$, then

$$
[L:K]=5,
\qquad
\operatorname{Gal}(M/K)=S_5,
\qquad
\operatorname{Gal}(M/L)=S_4.
$$

Thus the total group is nonsolvable, as desired for a nontrivial Brauer decomposition, while the
upper leg from the point field is solvable.

One convenient prime-cyclic chain in $S_4$ is obtained by refining

$$
S_4\triangleright A_4\triangleright V_4\triangleright C_2\triangleright1.
$$

The quotients have orders $2,3,2,2$. Reversing fixed fields produces extensions of those prime
degrees. No claim is made that the quintic root field is solvable over $K$; its normal closure
has group $S_5$.

**Corollary 9.2 (quintic solvable bridge).** Suppose a Galois approximation datum has
$(G,J)=(S_5,S_4)$ in the natural action. Then Theorem 7.1 produces a degree-five point field
$L$, an $S_5$ normal closure $M$, and a solvable Galois extension $M/L$. All prescribed top
local data, total reality, and closure-level disjointness hold simultaneously.

**Proof.** Apply Theorem 7.1 and the group calculation above. $\square$

### 9.4 The exact limitation of the quintic method

For the natural symmetric action of degree $n$, the point stabilizer is $S_{n-1}$. It is
solvable exactly when $n-1\le4$, hence when $n\le5$. For $n\ge6$, the subgroup contains
$A_{n-1}$, which is nonabelian simple, so it is not solvable.

Degree five is therefore the largest generic symmetric bridge. This does not prove that every
smooth geometrically connected variety admits a quintic bridge presentation. A variety can have
index not dividing five, so it may have no degree-five closed point at all. Even when it has such
points, a chosen moving family may have monodromy smaller than $S_5$ or may fail to realize the
required local torsors.

Book 153 obtains flexibility by allowing the degree of a moving zero-cycle to become large. That
freedom cannot be reconciled automatically with the fixed degree five. A quintic Galois
refinement therefore requires additional geometry: an actual degree-five evaluation family with
generic $S_5$ monodromy and the desired local fibers. Corollary 9.2 is conditional on precisely
that check and is not a consequence of ordinary Moret--Bailly alone.

## 10. Elementary subfields

The Galois top field serves a second purpose beyond normality: it provides one finite group on
which Brauer induction can be performed. Brauer's theorem uses elementary subgroups. The
arithmetic construction must therefore provide all their fixed fields with compatible local
data and solvable upper extensions. This chapter proves that the single top field already does
so.

### 10.1 Elementary groups and solvability

Fix a prime $p$. A finite group $H$ is **$p$-elementary** if

$$
H=C\times P,
$$

where $C$ is cyclic of order prime to $p$ and $P$ is a finite $p$-group. A group is
**elementary** if it is $p$-elementary for some $p$.

The direct-product condition is stronger than solvability. For example, $S_3$ is solvable but
is not elementary. The point of elementary groups is character-theoretic, but their
field-theoretic advantage is immediate.

**Proposition 10.1.** Every elementary group is solvable. More precisely, it has a subnormal
series with cyclic prime-order quotients.

**Proof.** A finite $p$-group has nontrivial center. Repeatedly choose a central subgroup of
order $p$ in a nontrivial quotient and take its inverse image. This gives a central series of
$P$ with factors of order $p$. The cyclic group $C$ has a series obtained by successively
dividing its order by prime factors. Taking products of the stages, or concatenating the two
series because the factors commute, gives a subnormal series for $C\times P$ with cyclic
prime-order quotients. Hence it is solvable. $\square$

Every subgroup of a $p$-elementary group is again $p$-elementary. Indeed, if
$h=(c,u)\in C\times P$, its prime-to-$p$ and $p$-parts are powers of $h$, so both belong to any
subgroup containing $h$. A subgroup $D$ therefore decomposes as

$$
D=(D\cap C)\times(D\cap P).
$$

This closure under subgroups is useful when local decomposition groups meet an elementary
subgroup inside the double-coset formula.

### 10.2 The direction-reversing field dictionary

Let $M/K$ be finite Galois with group $G$. For every subgroup $H\le G$, put

$$
F_H=M^H.
$$

Then

$$
\operatorname{Gal}(M/F_H)=H,
\qquad
[F_H:K]=[G:H].
$$

Inclusions reverse:

$$
H_1\le H_2
\quad\Longrightarrow\quad
F_{H_2}\subset F_{H_1}.
$$

The lower extension $F_H/K$ is Galois exactly when $H$ is normal in $G$, in which case its
group is $G/H$. If $H$ is not normal, the normal closure of $F_H/K$ inside $M$ has group

$$
G/\operatorname{core}_G(H),
\qquad
\operatorname{core}_G(H)=\bigcap_{g\in G}gHg^{-1}.
$$

This quotient can be nonsolvable even when $H$ is elementary. Therefore the phrase “the
elementary extension $F_H/K$” is misleading. What is elementary, and hence solvable, is the
upper Galois extension

$$
M/F_H.
$$

The lower field is used as a separate base field; it need not lie on a solvable path from $K$.

### 10.3 Solvable upper towers

**Theorem 10.2.** For every elementary subgroup $H\le G$, the extension $M/F_H$ admits a tower

$$
F_H=E_0\subset E_1\subset\cdots\subset E_r=M
$$

in which every step is cyclic Galois of prime degree. If $M$ is totally real, split at a set
$S$, and disjoint from $D_{\mathrm{av}}$, then every $E_i$ has the same three properties in the
appropriate sense: it is totally real, every $v\in S$ splits completely in it, and
$E_i\cap D_{\mathrm{av}}=K$.

**Proof.** Proposition 10.1 gives a subnormal series of $H$ with cyclic prime quotients. Reverse
it by Galois correspondence. Total reality and splitting descend to subfields by Propositions
3.3 and 3.5. Since $E_i\subset M$, one has

$$
E_i\cap D_{\mathrm{av}}\subset M\cap D_{\mathrm{av}}=K.
$$

$\square$

The last intersection is stated over $K$, even though the upper tower starts at $F_H$. If an
application needs disjointness relative to $F_H$ from the compositum $F_HD_{\mathrm{av}}$, the
same condition gives it: since $M$ and $D_{\mathrm{av}}$ are linearly disjoint over $K$, the
extensions $M/F_H$ and $F_HD_{\mathrm{av}}/F_H$ are linearly disjoint. This follows by comparing
degrees after base change.

If auxiliary Frobenius values are needed on this elementary upper tower, choose its subnormal
prime-cyclic series and apply the simultaneous tower statement of Section 9.2. The actual prime
is selected once in $K$ by Corollary 4.7; all primes and character values over the intermediate
fields are then forced by the common top field.

### 10.4 Conjugate subgroups and conjugate fields

Brauer relations are invariant under conjugating a subgroup and its character. The field
construction has the same symmetry. If $H'=gHg^{-1}$, then

$$
F_{H'}=g(F_H)
$$

inside $M$. The fields need not be equal, but they are $K$-isomorphic through $g$. Their local
completion diagrams are conjugate: replacing $H$ by $gHg^{-1}$ merely reindexes the double
cosets in Theorem 3.1.

It is therefore enough to choose one representative of each $G$-conjugacy class of elementary
subgroups when listing fields for a Brauer relation. If an actual relation contains several
conjugate terms with different characters, their coefficient and character labels must still be
retained; the underlying field isomorphism does not identify those labels automatically.

For a one-dimensional character

$$
\theta:H\longrightarrow\mathbf C^\times,
$$

inflation along

$$
G_{F_H}\twoheadrightarrow\operatorname{Gal}(M/F_H)=H
$$

gives a finite-order Galois character of $F_H$. Its kernel corresponds to an intermediate cyclic
extension of $M/F_H$ when the image is cyclic, as it always is for a one-dimensional character.
Thus the field on which the twist becomes trivial is already a member of the same fixed-field
diagram.

## 11. The compatible family attached to one top field

The word “family” must mean more than a list of individually existing fields. Later induction
and restriction formulas compare inclusions, intersections, conjugates, local completions, and
characters. All of those comparisons become canonical when every field is defined as a fixed
field inside one $M$. This chapter makes that compatibility explicit.

### 11.1 What compatibility means

Let $\mathcal H$ be a finite collection of subgroups of $G$ containing every subgroup used in a
chosen Brauer relation, together with all intersections, generated subgroups, conjugates, and
character kernels needed in later comparisons. Because $G$ is finite, closing a finite list
under these operations still gives a finite list.

The associated **fixed-field family** is

$$
\mathcal F(M,\mathcal H)=\{F_H=M^H:H\in\mathcal H\}.
$$

It is compatible in four senses.

1. **Order:** inclusions of groups reverse to inclusions of fields.
2. **Lattice operations:** generated subgroups and intersections become intersections and
   composita of fields.
3. **Conjugation:** conjugate subgroups give conjugate embedded fields.
4. **Localization:** one top local homomorphism determines every completed tensor product.

No choice of primitive elements enters this definition. Primitive elements may be used to
compute a field, but compatibility belongs to the subgroup lattice.

### 11.2 Intersections and composita of fixed fields

The Galois correspondence exchanges the basic lattice operations as follows.

**Proposition 11.1.** For subgroups $H_1,H_2\le G$,

$$
M^{\langle H_1,H_2\rangle}
=M^{H_1}\cap M^{H_2},
$$

and

$$
M^{H_1\cap H_2}
=M^{H_1}M^{H_2}.
$$

**Proof.** An element of $M$ is fixed by the group generated by $H_1$ and $H_2$ exactly when it
is fixed by both groups, proving the first formula. For the second, the compositum on the right
is fixed by $H_1\cap H_2$, so it lies in the left side. The subgroup fixing the compositum must
fix each $M^{H_i}$ and therefore lies in each $H_i$; it is exactly $H_1\cap H_2$. Equality
follows from Galois correspondence. $\square$

These formulas show why independently selected fields are inadequate. If fields called
$F_{H_1}$ and $F_{H_2}$ were chosen in unrelated algebraic closures, there would be no reason
for their intersection or compositum to represent the correct subgroup operation.

For several subgroups,

$$
\bigcap_iM^{H_i}=M^{\langle H_i:i\rangle},
\qquad
\prod_iM^{H_i}=M^{\cap_iH_i}.
$$

In particular, if the intersection of the chosen subgroups is trivial, their fixed fields
generate the whole top field.

### 11.3 Local compatibility throughout the family

Fix a controlled finite place $v$ and a local top homomorphism

$$
\phi_v:G_{K_v}\longrightarrow G
$$

with image $D_v$. For every $H\in\mathcal H$, the local algebra of $F_H$ is the finite étale
algebra attached to the $D_v$-set $G/H$. If $H_1\le H_2$, the natural $G$-map

$$
G/H_1\longrightarrow G/H_2
$$

induces the localization of the field inclusion

$$
F_{H_2}\subset F_{H_1}.
$$

Thus the completion maps are not merely abstract isomorphisms; after fixing one top fiber they
commute with all global inclusions.

At an unramified place with Frobenius $c_v$, the factors of $F_H\otimes_KK_v$ are the orbits of
$\langle c_v\rangle$ on $G/H$. If an orbit has length $f$, the corresponding factor is the
unramified degree-$f$ extension of $K_v$. Hence a single element $c_v$ gives a table of local
partitions for the entire family.

At a ramified place, replace the cyclic group by $D_v$ and retain $I_v$. An orbit determines a
completion, its stabilizer determines the embedding in the top local field, and intersection
with $I_v$ determines ramification. The resulting maps are automatically compatible with
intersection and compositum because they arise by taking fixed fields inside $M_w$.

### 11.4 Characters and cyclic layers

Let $H\in\mathcal H$ be elementary and let $\theta:H\to\mu_m$ be a one-dimensional character.
Write $H_\theta=\ker\theta$. Then

$$
F_H\subset F_{H_\theta}\subset M,
$$

and

$$
\operatorname{Gal}(F_{H_\theta}/F_H)
\simeq H/H_\theta=\operatorname{im}\theta,
$$

which is cyclic. The character is the faithful character of this quotient followed by its
chosen embedding into roots of unity.

If two characters have kernels $H_\theta$ and $H_\psi$, then their product has kernel containing
$H_\theta\cap H_\psi$, and all three corresponding cyclic fields lie in the same diagram. This
is the field-theoretic content behind multiplication of character twists. It does not identify
coefficient embeddings of roots of unity; those are additional labels carried by the
characters.

The place of $F_H$ indexed by $D_vgH$ has decomposition subgroup

$$
g^{-1}D_vg\cap H
$$

inside $H=\operatorname{Gal}(M/F_H)$. Thus its local character is the restriction of $\theta$
to that subgroup. Equivalently, if

$$
Q=D_v\cap gHg^{-1}
$$

is the subgroup used in the fixed-field description inside the chosen top completion, the
character on $Q$ is

$$
q\longmapsto\theta(g^{-1}qg).
$$

Thus ramification and Frobenius values of every Brauer character are determined by the top local
homomorphism. Prescribing local torsors at the top is exactly what makes all later twists
locally compatible.

For an auxiliary place not prescribed during specialization, this compatibility is an existence
statement as well as a dictionary. Given $c\in G$, Corollary 4.7 supplies infinitely many primes
outside the controlled set with top Frobenius class $[c]$. At the factor indexed by the orbit of
$gH$, of length $f$, let $\mathfrak q=g^{-1}w|_{F_H}$. The Frobenius at the prime below
$g^{-1}w$ in the cyclic extension $F_{H_\theta}/F_H$ is the class of
$g^{-1}c^fg$ in $H/H_\theta$; under its faithful character, this gives

$$
\operatorname{Frob}_{F_{H_\theta}/F_H}
\longmapsto
\theta(g^{-1}c^fg).
$$

It does so simultaneously for every $(H,\theta)$ in the finite family. In particular, one does
not make independent prime choices in the elementary fixed fields or in their cyclic character
layers.

## 12. Mutually disjoint top fields

Some constructions need several potential-automorphy packages, several coefficient primes, or
an inductive sequence of auxiliary fields. Pairwise disjoint root fields are not enough. This
chapter proves two safe methods: inductive avoidance for a sequence, and simultaneous
specialization for a finite family.

### 12.1 Inductive avoidance

Suppose a fixed Galois approximation datum can be applied repeatedly. After constructing top
fields $M_1,\ldots,M_{r-1}$, let

$$
D_r=D_{\mathrm{av}}M_1\cdots M_{r-1}.
$$

This is finite Galois over $K$. Apply Theorem 7.1 with avoidance field $D_r$ to obtain $M_r$.
Then

$$
M_r\cap(M_1\cdots M_{r-1})=K.
$$

By Proposition 2.4, the top fields are mutually linearly disjoint. Each root field and each
elementary subfield lies in its corresponding top field, so it is disjoint from the compositum
of all earlier top fields as well.

**Theorem 12.1 (independent sequence).** If a Galois approximation datum has nonempty prescribed
local boxes, then it has infinitely many specializations with mutually linearly disjoint top
fields, all satisfying the same finite local conditions. Any fixed finite avoidance field may be
avoided by every member.

**Proof.** Begin with the fixed avoidance field and apply the preceding induction. At every
stage only a finite extension is added to the avoidance field, so Theorem 7.1 remains applicable.
Proposition 2.4 gives mutual linear disjointness of every finite initial segment, which is the
definition for the infinite family. $\square$

The theorem imposes the same finite set of local conditions at every stage. It does not impose
infinitely many new local conditions on one field. Those are different quantifiers.

### 12.2 Product Galois groups

If $M_1,\ldots,M_r$ are mutually linearly disjoint finite Galois extensions with groups
$G_1,\ldots,G_r$, then

$$
\operatorname{Gal}(M_1\cdots M_r/K)
\simeq
G_1\times\cdots\times G_r.
$$

At an unramified prime, Frobenius in the compositum is the tuple of the individual Frobenius
classes. Theorem 4.3 applied to the compositum therefore gives every product conjugacy class
$C_1\times\cdots\times C_r$ density

$$
\frac{|C_1|\cdots|C_r|}{|G_1|\cdots|G_r|}>0,
$$

so it permits simultaneous auxiliary-prime conditions across all top fields, outside any finite
set. Corollary 4.7, applied after projection to each factor or directly to product subgroups,
then supplies the compatible fixed-field factors and cyclic-character values in every family.
If a further Galois field $B$ is disjoint from the compositum, Corollary 4.5 also makes the same
prime split completely in $B$.

At a controlled place built into all approximation data, local homomorphisms combine as

$$
G_{K_v}\longrightarrow G_1\times\cdots\times G_r.
$$

The image need not be the product of the individual images; the same local absolute Galois
group maps to every factor. If the fields are also locally linearly disjoint at $v$, it is the
fiber product dictated by the local compositum. Complete splitting avoids this complication by
making every local image trivial.

### 12.3 Simultaneous specialization

For finitely many different Galois approximation data over the same affine parameter space
$H$, one can specialize them at one parameter. Let

$$
\widetilde T_i\longrightarrow H
$$

have group $G_i$. Suppose their generic Galois function fields are mutually linearly disjoint over
$K(H)$. Suppose also that, at every controlled place, the local requirements for the several
covers are realized on one common nonempty open subset of $H(K_v)$. Then the fiber product is
geometrically connected and Galois with group
$\prod_iG_i$.

**Theorem 12.2 (simultaneous independent specialization).** Under the generic disjointness and
common local-realizability hypotheses above, one may choose $h\in H(K)$ such that every top fiber
has full group $G_i$, the top fields are mutually linearly disjoint over $K$, all prescribed
local torsors occur, and their compositum avoids a fixed finite extension.

**Proof.** Apply the proof of Theorem 7.1 to the connected product Galois cover

$$
\widetilde T_1\times_H\cdots\times_H\widetilde T_r\longrightarrow H
$$

with group $\prod_iG_i$: impose its maximal-subgroup resolvents and connectedness after base
change to the avoidance field, and intersect the local neighborhoods for all factors. Hilbert
irreducibility supplies one parameter. Full monodromy of
the product fiber gives a compositum Galois group of order $\prod_i|G_i|$, which is mutual
linear disjointness. Connectedness after base change gives avoidance for the compositum. Taking
the separately specified quotients by $J_i$ recovers each desired root point and its evaluation
map and local condition. $\square$

If the generic fields intersect, requiring each individual fiber to have full group does not
make the specialized fields disjoint. One must compute the generic intersection and either
accept the corresponding fiber-product group or alter the families.

### 12.4 Infinite sequences and their exact scope

Theorem 12.1 constructs an infinite sequence by infinitely many finite operations. Each field
satisfies a fixed finite local package, and every new top field avoids the finite compositum of
its predecessors. It does not produce one parameter satisfying countably many Hilbert
conditions.

The same finite-stage restriction applies to prime selection. Theorem 4.3 applies to the
compositum of any fixed finite subcollection and therefore realizes a finite tuple of Frobenius
classes. It makes no assertion that one prime realizes an arbitrarily prescribed infinite tuple
across the entire sequence.

Likewise, Theorem 12.2 handles only finitely many covers at once. A countable fiber product need
not be a finite-type variety, and a countable intersection of Hilbert subsets need not be
covered by Hilbert irreducibility. When an application seems to require infinitely many
avoidance conditions for one bounded-degree field, it must first prove that only finitely many
subextensions can occur, as in Book 152's bounded-degree criterion.

The finite-stage formulation is sufficient for Brauer descent. A finite group has finitely many
subgroups, a Brauer relation uses finitely many of them, and every local or character kernel
needed for that relation adds only finitely many fields.

## 13. The universal symmetric family

The abstract datum of Chapter 6 is concrete on coefficient space. The universal monic
polynomial has generic symmetric Galois group, local polynomial neighborhoods preserve its
complete Galois algebra, and Hilbert specialization produces disjoint symmetric closures. This
chapter proves those statements and then isolates the one feature coefficient space cannot
supply by itself: an evaluation map to an arbitrary target variety.

### 13.1 Generic symmetric monodromy

Fix an integer $n\ge2$. Let

$$
\mathcal P_n=\operatorname{Spec}K[a_1,\ldots,a_n]
$$

be the coefficient space of monic degree-$n$ polynomials, with universal polynomial

$$
f(X)=X^n+a_1X^{n-1}+\cdots+a_n.
$$

Remove the discriminant divisor and call the resulting open $H_n$. Let $T_n\to H_n$ be the
degree-$n$ root cover and $\widetilde T_n\to H_n$ its ordered-root cover.

**Proposition 13.1.** The ordered-root cover is geometrically connected and Galois with group
$S_n$. The root cover is its quotient by the point stabilizer $S_{n-1}$.

**Proof.** Let $x_1,\ldots,x_n$ be algebraically independent over $K$, and let
$e_1,\ldots,e_n$ be their elementary symmetric functions, with the signs chosen to match the
coefficients. The symmetric group acts faithfully on

$$
K(x_1,\ldots,x_n)
$$

by permuting the variables, and its fixed field is

$$
K(e_1,\ldots,e_n).
$$

The fixed-field assertion follows by the fundamental theorem of symmetric rational functions:
write an invariant rational function as a quotient, multiply numerator and denominator by all
conjugates of the denominator, and express the resulting symmetric polynomials in the
$e_i$. Hence the extension is Galois with group $S_n$. Algebraic independence remains after
base change to an algebraic closure of $K$, so the extension is regular and the cover is
geometrically connected.

Choosing one root $x_1$ fixes exactly the permutations of the other $n-1$ roots, namely
$S_{n-1}$. The corresponding quotient is the universal root cover. Removing the discriminant
makes all covers finite étale. $\square$

For $n=5$, this is the universal symmetric quintic solvable bridge. For $n\ge6$, it remains a
Galois approximation datum but not a solvable bridge datum.

### 13.2 Local coefficient neighborhoods

Let $k$ be a completion of $K$ and let $p(X)\in k[X]$ be monic and separable of degree $n$.
Book 2's simple-root stability and Krasner's lemma give a neighborhood of the coefficient vector
on which the finite étale root algebra is constant. Passing to the splitting field and retaining
the permutation of all roots gives the equivariant strengthening.

**Proposition 13.2.** There is a coefficient neighborhood $V_p\subset H_n(k)$ such that for
every $q\in V_p$, the root algebra $k[X]/(q)$, the ordered-root finite étale algebra, and the
associated local homomorphism

$$
G_k\longrightarrow S_n
$$

are isomorphic to those of $p$, up to conjugacy in $S_n$. The ordered-root algebra is generally
a product of copies of the splitting field; it is the local fiber of the top $S_n$-torsor, not
necessarily one field.

**Proof.** In a finite splitting field of $p$, choose disjoint small balls around its roots.
Hensel stability gives one root of every nearby $q$ in each ball. Krasner's lemma, applied in
both directions after shrinking, shows that corresponding clusters generate the same field
extensions. The action of $G_k$ on the labeled balls is locally constant, because a continuous
action on a finite discrete set cannot change under the unique root continuation. Thus the
permutation homomorphism is conjugate to the original one. Taking orbits recovers the root
algebra. The regular $S_n$-set attached to the homomorphism recovers the ordered-root algebra,
and each connected factor is a copy of the splitting field. $\square$

Examples include:

- If $p$ has $n$ distinct roots in $k$, the local homomorphism is trivial and nearby polynomials
  split completely.
- If $p$ is unramified irreducible, the image is generated by an $n$-cycle.
- If $p$ is a product of distinct unramified irreducibles of degrees
  $n_1,\ldots,n_r$, Frobenius has cycle type $(n_1,\ldots,n_r)$.
- A separable ramified $p$ supplies the full pair of local decomposition and inertia images,
  not merely a repeated factorization modulo the residue characteristic.

### 13.3 Disjoint symmetric specializations

Combine Propositions 13.1 and 13.2 with Theorem 7.1.

**Theorem 13.3 (symmetric specialization package).** Let $S$ be a finite set of places of $K$.
For every $v\in S$, choose a monic separable degree-$n$ polynomial $p_v\in K_v[X]$. Let
$D_{\mathrm{av}}/K$ be finite. Then there is a monic polynomial $p\in K[X]$ such that:

1. $p$ is irreducible;
2. its normal closure $M/K$ has group $S_n$ in the natural action;
3. $M$ is linearly disjoint from $D_{\mathrm{av}}$;
4. at every $v\in S$, the local root algebra and its labeled Galois closure are those of $p_v$.

If $K$ is totally real and every real $p_v$ has $n$ distinct real roots, then $M$ is totally
real. If every $p_v$ at a finite place splits completely, that place splits completely in $M$.
For $n=5$, the extension from the quintic root field to $M$ is solvable.

**Proof.** Use the universal symmetric datum and the coefficient neighborhoods of Proposition
13.2. Theorem 7.1 supplies the coefficient vector with full monodromy and closure-level
avoidance. The archimedean and split statements are Theorem 8.1 and Corollary 8.2. The quintic
statement is Corollary 9.2. $\square$

This theorem is unconditional because the target is the affine line and the chosen root itself
is the evaluated point. It is the field-construction laboratory for every abstract assertion in
the book.

### 13.4 Why a map to the target variety is additional geometry

For a general variety $X$, choosing a polynomial on coefficient space gives a field $L$ but no
point of $X(L)$. Conversely, Moret--Bailly gives an $L$-point by specializing an incidence cover,
but that cover need not be the universal quintic root cover. To combine the conclusions, one
needs an evaluation family

$$
T\longrightarrow X
$$

whose Galois closure has the desired group and stabilizer.

Taking an independently constructed quintic field $L_1$ and a Moret--Bailly point over $L_2$ does
not solve the problem by passing to $L_1L_2$. The point descends from $L_2$, so the actual
residue field has not become the quintic root field; the normal closure group becomes a product
or fiber product; and the upper stabilizer generally contains the unknown stabilizer from
$L_2$. Solvability can be lost.

The evaluation map in Definition 6.1 is therefore indispensable. It binds the arithmetic field
and the geometric point in one connected fiber. Constructing it is the geometric work addressed
in the next chapter.

## 14. Constructing and checking bridge presentations

The main theorems deliberately separate arithmetic specialization from geometric presentation.
This chapter explains how a presentation can arise, what must be checked, and which operations
preserve it. The aim is not to claim a bridge for every variety, but to make the verification of
one finite and transparent when a moduli construction supplies it.

### 14.1 Evaluation families

An **evaluation family of degree $n$** on $X$ is a diagram

$$
T\xrightarrow{e}X,
\qquad
T\xrightarrow{f}H,
$$

where $H$ is a rational parameter space and $f$ is finite étale of degree $n$. A fiber
$T_h=\operatorname{Spec}L_h$ then evaluates to a point $x_h\in X(L_h)$. The family becomes a
Galois approximation datum after its Galois closure over $H$ is shown to be geometrically
connected with a specified group $G$ and the sheet stabilizer is identified.

There are several natural sources.

1. A finite morphism from a geometrically integral curve $C\subset X$ to an affine line. The
   open obtained by deleting branch values gives a finite étale evaluation family.
2. A finite étale incidence family over a moving linear system, as in Book 153. Here the points
   of a divisor evaluate on $X$.
3. A fine moduli cover carrying a universal object, followed by a finite map to a rational chart
   of its base.
4. A fiber product of existing families, provided the generic function fields and the resulting
   evaluation map have been checked.

The degree, monodromy, and stabilizer depend on the chosen family, not only on $X$. Changing the
linear system or projection can change the generic Galois group even though the target variety
is unchanged.

### 14.2 Shrinking to the good locus

Most natural families begin generically finite rather than finite étale. The first task is to
remove every locus where the specialization dictionary can fail. Starting with a dominant
generically finite separable morphism $T\to H$, one performs the following finite sequence.

1. Normalize $H$ in $K(T)$, so the function-field extension is represented by a finite map
   after shrinking.
2. Remove the branch locus and the singular locus of the base, obtaining a finite étale map.
3. Form the normal closure of $K(T)/K(H)$ and normalize again; remove its branch locus.
4. Remove every locus where the evaluation map lands outside the desired open of $X$ or where a
   moduli object degenerates.
5. If several covers or resolvents are used, intersect all remaining opens.

All removed sets are proper closed subsets when the generic hypotheses hold. The resulting
$H$ is still a nonempty open of an affine space if the original rational parameter chart was
chosen correctly.

Geometric connectedness must then be checked after extending constants to an algebraic closure.
For a function field this means

$$
\overline K\cap K(\widetilde T)=K
$$

inside a common overfield, or equivalently that $K$ is algebraically closed in the generic top
field. Arithmetic connectedness alone is insufficient for closure-level avoidance.

### 14.3 A finite verification procedure

Suppose an intended application proposes a finite family. The following checks are enough to
justify Theorem 7.1.

**Generic checks.**

1. Compute the generic degree $n$ and prove separability.
2. Compute the Galois group $G$ of the generic normal closure, not merely a subgroup containing
   it.
3. Identify the sheet stabilizer $J$ and verify
   $$
   [G:J]=n,
   \qquad
   \operatorname{core}_G(J)=1.
   $$
4. Prove geometric connectedness of the top cover.
5. If an upper solvable path is needed, give a subnormal cyclic-prime series for $J$.

**Evaluation checks.**

6. Construct the actual morphism $e:T\to X$ or to the intended fine moduli space.
7. Verify that the residue field of a connected fiber is the field over which the evaluated
   object is genuinely defined; an object descending to a smaller field must be excluded when
   exact degree matters.
8. Remove all closed degeneracy loci before choosing local points.

**Local checks.**

9. At every controlled place, exhibit a point $b_v\in H(K_v)$.
10. Compute the local homomorphism $\phi_v:G_{K_v}\to G$ and verify the desired point condition
    on every quotient factor.
11. At every real place needed for total reality, verify that the top torsor is split, not merely
    that one root is real.
12. Shrink to one equivariant constancy neighborhood $V_v$ supporting all conditions.

**Avoidance checks.**

13. Put every finite residual, cyclotomic, self-twist, component, and previously constructed top
    field into one finite Galois field $D_{\mathrm{av}}$.
14. Impose connectedness of the top cover after base change to that field.

Each item has a definite failure mode. A missing local point is not repaired by Hilbert
irreducibility. A wrong monodromy group is not repaired by shrinking. A nonsolvable stabilizer
is not repaired by the solvability of some quotient. A constant field cannot be removed by
choosing a more general rational parameter.

### 14.4 Changing the presentation

Sometimes the first presentation fails one check while another presentation succeeds. Four
operations are common.

**Shrinking the base.** This preserves the generic group, stabilizer, and geometric
connectedness, while removing bad local or geometric loci. It cannot create a missing local
fiber.

**Pullback along a rational map.** Let $H'\to H$ be dominant. The generic top cover after
pullback is connected exactly when $K(H')$ is linearly disjoint from $K(\widetilde T)$ over
$K(H)$. Without this check the monodromy can shrink. Local points can improve because the new
parameter space may meet a desired neighborhood.

**Changing the finite projection.** A different rational function on the same curve changes the
degree and generic monodromy. A sufficiently general simply branched primitive cover often has
symmetric monodromy, but both simple branching and primitivity must be proved. A transitive
subgroup generated by transpositions is $S_n$: the graph whose edges are those transpositions
is connected by transitivity, and edge transpositions of a connected graph generate the full
symmetric group. This gives a useful monodromy criterion.

**Taking a product family.** If two top generic fields are linearly disjoint, the product cover
has product group. The stabilizer of a product sheet is the product of the stabilizers. It is
solvable exactly when both stabilizers are solvable. Thus product families preserve a solvable
bridge only when every factor already has one; adding an arbitrary Moret--Bailly incidence
factor can destroy the desired property.

These operations show how geometry can be adjusted while keeping the arithmetic theorem fixed.
They also explain why the existence of a suitable presentation belongs in the input ledger of a
later application.

## 15. Failures that delimit the theory

A robust theorem is defined as much by the conclusions it refuses to assert as by those it
proves. This chapter collects counterexamples and diagnostic failures. Each one corresponds to a
specific clause in the Galois approximation datum or the final package.

### 15.1 A disjoint root field with a nondisjoint closure

Let $L/K$ be a non-Galois cubic whose normal closure $M$ has group $S_3$. Let $Q=M^{A_3}$ be
the quadratic resolvent. Then

$$
L\cap Q=K
$$

by coprime degrees, but $M\cap Q=Q$. If a finite representation has fixed field $Q$, restriction
to $G_L$ preserves its image while restriction to $G_M$ kills the quadratic quotient.

The example proves that root-field connectedness after base change cannot replace top-cover
connectedness. It also shows that passing to the normal closure is not an innocuous enlargement
in an image-preservation argument.

### 15.2 Locally acceptable root data with unacceptable closure data

Let $G$ act faithfully and transitively on $G/J$. A local root algebra records the orbit
decomposition of a subgroup $D\le G$ on that set, together with the field structure within each
orbit. If only the degrees of the factors are retained, different subgroups can become
indistinguishable.

For a simple group-theoretic model, in $S_4$ both a subgroup generated by a double transposition
and a subgroup generated by a transposition have order two, but their natural cycle types are
$(2,2)$ and $(2,1,1)$ and so are distinguished. In other permutation representations, however,
nonconjugate subgroups can have the same orbit-size multiset. Even within $S_n$, two elements can
have the same action on one quotient $G/J$ after the action has a nontrivial kernel, while acting
differently on another quotient $G/H$.

The invariant datum is therefore the conjugacy class of the local homomorphism into a faithful
top group. A partition in one root field is enough only when the application genuinely uses no
other quotient and a separate argument proves uniqueness of the relevant class.

### 15.3 Solvable degree is not a solvable extension

Every positive integer has a composition into prime factors, but not every finite Galois group
of that order is solvable. The smallest standard obstruction is $A_5$, of order $60$. Thus the
phrase “an extension of solvable degree” has no useful group-theoretic meaning.

Nor does solvability of $L/K$ in some informal nonnormal sense control the upper extension to its
normal closure. The exact statement is always made using a Galois group:

$$
M/L\text{ is solvable Galois}
\quad\Longleftrightarrow\quad
\operatorname{Gal}(M/L)=J\text{ is solvable}.
$$

For an $S_5$ quintic, $J=S_4$ is solvable. For an $S_6$ sextic, $J=S_5$ is not. Both root
degrees are small integers; only the stabilizer calculation decides the issue.

### 15.4 Pairwise conditions are not family compatibility

Let $a,b$ represent independent square classes in $K^\times/K^{\times2}$. The three quadratic
fields

$$
K(\sqrt a),
\qquad
K(\sqrt b),
\qquad
K(\sqrt{ab})
$$

are pairwise linearly disjoint, but their compositum has degree four rather than eight. The third
lies in the compositum of the first two. Thus pairwise disjointness does not give mutual
disjointness.

Similarly, choosing fields separately for subgroups $H_1$ and $H_2$ does not ensure

$$
F_{H_1}F_{H_2}=F_{H_1\cap H_2}
$$

or

$$
F_{H_1}\cap F_{H_2}=F_{\langle H_1,H_2\rangle}.
$$

Those identities follow only when all fields are fixed fields in one top Galois extension.

Local compatibility has the same issue. Two local algebras may each be realizable, yet their
chosen compositum may have a smaller-than-expected degree or a conflicting inertia action. One
top local torsor resolves all quotient data at once and is therefore the correct input.

## 16. The Brauer-descent field package

We now assemble the theory in the form needed before a Brauer descent argument begins. The
theorem is purely arithmetic and field-theoretic. It does not assert automorphy, construct a
Brauer character identity, or perform analytic descent. Its job is to provide the one coherent
field diagram on which those later arguments can operate.

### 16.1 The input ledger

Let $K$ be totally real and $X/K$ a variety carrying the objects to be specialized. The required
input consists of the following finite ledger.

1. **Bridge presentation.** A solvable Galois approximation datum
   $$
   (H,\widetilde T,G,J,T,e)
   $$
   with $J$ core-free and solvable.
2. **Real places.** For every real $v$ of $K$, a point of $H(K_v)$ with split top torsor and a
   neighborhood on which every evaluated root sheet lies in the desired real open of $X(K_v)$.
3. **Split finite places.** At every place where all later fields must have the unchanged local
   base, a locally realized split top torsor and the desired evaluated open.
4. **General local places.** At every remaining controlled place, a locally realized top
   homomorphism $\phi_v:G_{K_v}\to G$ and a point condition on the quotient fiber.
5. **Avoidance.** One finite Galois extension $D_{\mathrm{av}}/K$ containing every finite field
   whose intersection could shrink an image or create a forbidden twist or component.
6. **Subgroup list.** A finite collection $\mathcal H$ containing the elementary subgroups and
   character kernels occurring in the intended Brauer relation, closed under the finite lattice
   operations that will be used.

The ledger is deliberately stronger than a list of local points on $X$. Items 1 and 4 are the
Galois refinement, item 5 is closure-level avoidance, and item 6 makes the later family explicit.

### 16.2 The packaged existence theorem

**Theorem 16.1 (Brauer-descent field package).** Given the ledger of Section 16.1, there exist
a finite Galois extension $M/K$, a subfield $L\subset M$, and a point $x\in X(L)$ such that:

1. there is a specified isomorphism
   $$
   \operatorname{Gal}(M/K)\simeq G;
   $$
2. $L=M^J$, the normal closure of $L/K$ is $M$, and
   $$
   \operatorname{Gal}(M/L)=J
   $$
   is solvable;
3. $M$, $L$, and every $M^H$ for $H\in\mathcal H$ are totally real;
4. $M\cap D_{\mathrm{av}}=K$, so every intermediate field preserves all finite images encoded
   in $D_{\mathrm{av}}$;
5. every prescribed split place splits completely in $M$ and in every $M^H$;
6. at a general controlled place, the top decomposition and inertia images are the prescribed
   pair $(D_v,I_v)$, and every fixed-field completion is given by
   $$
   M^H\otimes_KK_v
   \simeq
   \prod_{D_vgH\in D_v\backslash G/H}
   M_w^{D_v\cap gHg^{-1}};
   $$
7. the localized components of $x$ satisfy every prescribed point condition;
8. for every elementary $H\in\mathcal H$, the upper extension $M/M^H$ has a prime-cyclic
   tower, and the same is true of $M/L$;
9. all inclusions, intersections, composita, conjugations, localizations, and character-kernel
   fields in the family are those dictated by the subgroup lattice of $G$.
10. after $M$ is fixed, any finite list of auxiliary Frobenius classes can be realized at
    distinct primes outside the controlled set; at each such prime, all fixed-field factors and
    character values are simultaneously those of Corollary 4.7. The primes may additionally be
    required to split completely in any Galois subextension $B/K$ of $D_{\mathrm{av}}/K$.

Moreover, one can construct infinitely many such packages whose top fields are mutually
linearly disjoint and all avoid the same initial $D_{\mathrm{av}}$.

### 16.3 Proof and dependency audit

**Proof strategy.** Apply the Galois-refined approximation theorem once, then take fixed fields
inside its top fiber. Every compatibility statement is a consequence of Galois correspondence
or the double-coset completion theorem; no field is chosen separately.

**Proof.** Include all real and controlled finite places in the finite set $S$. Apply Theorem
7.1 to the prescribed local neighborhoods and $D_{\mathrm{av}}$. The result supplies a Galois
top field $M$ with group $G$, the root field $L=M^J$, the evaluated point $x$, exact local top
torsors, and $M\cap D_{\mathrm{av}}=K$.

The split real torsors imply total reality by Theorem 8.1. Split finite torsors give complete
splitting in every fixed field by Proposition 3.3. At every general controlled place, Theorem
3.1 supplies the displayed local formula, and Corollary 3.2 supplies inertia. Equivariant local
constancy proves the point conditions.

Solvability of $J$ gives the prime-cyclic tower from $L$ to $M$ by Proposition 9.1. Every
elementary $H$ is solvable by Proposition 10.1, so Theorem 10.2 gives the upper tower from
$M^H$ to $M$. Proposition 11.1 and the conjugation discussion of Section 10.4 prove every
field-family compatibility. Since every member is a subfield of $M$, closure-level avoidance
implies preservation of every finite image by Lemma 2.5.

For the auxiliary-prime assertion, choose the finitely many primes successively with
Corollaries 4.4 and 4.7, adjoining each chosen prime to the finite set to keep them distinct.
The orbit and relative-Frobenius calculation of Corollary 4.7 gives all fixed-field and character
data at once. If splitting in $B\subset D_{\mathrm{av}}$ is requested, then
$M\cap B=K$, so Corollary 4.5 imposes it simultaneously.

For infinitely many packages, use Theorem 12.1: at stage $r$, add the compositum of all previous
top fields to the avoidance field. Proposition 2.4 gives mutual linear disjointness. $\square$

Let us record exactly where the substantial inputs enter.

- The completed tensor-product, decomposition-group, inertia, and Krasner statements are the
  local field results of Book 2.
- Hilbert density in finite local boxes, full generic monodromy through resolvents, disjoint
  specialization after base change, and equivariant local constancy are established in Book
  152.
- Book 153 supplies moving incidence presentations for ordinary local-open approximation and
  explains how a point is evaluated from a connected fiber. It does not supply the bridge datum;
  that stronger presentation is hypothesis 1 of the ledger and must be proved in the geometric
  application.
- Finite global reciprocity, finite-character existence, and the finite-order Hecke-character
  dictionary used in the abelian step are supplied by Book 6. Chebotarev prime selection,
  including the density theorem used to choose auxiliary Frobenius witnesses, was then proved in
  Chapter 4 from the one-dimensional analytic lemma and the cyclic reduction.
- All normal-closure, solvable-stabilizer, elementary-field, mutual-disjointness, and compatible
  family conclusions are proved in this book.

This audit is the logical boundary of the theorem. No result about an ordinary Moret--Bailly
field is silently promoted to its normal closure.

### 16.4 How to read the output

The output supports three different paths, and their directions must remain distinct.

First, an object defined over the point field $L$ may be carried upward through the solvable
tower

$$
L\subset\cdots\subset M.
$$

Second, for each elementary $H$, an object at the top may be descended along the solvable upper
extension

$$
M/M^H.
$$

Third, the several objects over the fields $M^H$ can be assembled by a Brauer relation over
$G$. There is no asserted solvable path from $K$ to $M^H$, and none is needed for the
field-theoretic Brauer construction.

The geometry and local conditions are controlled before these paths begin. If a place splits in
$M$, every field in every path has the same completion $K_v$ at each branch. For general local
data, the double-coset formula tells exactly which completion occurs. Closure-level disjointness
ensures that finite residual images survive in all fields simultaneously.

The theorem does not construct a Galois approximation datum for a particular moduli space. It
does not prove that an object remains automorphic on moving from $L$ to $M$, nor that solvable
descent is available for its precise local type. It does not prove Brauer induction or the
effectivity of a resulting virtual family. Those are separate geometric, automorphic, and
character-theoretic tasks. What it supplies is the arithmetic field diagram they require.

## 17. Synthesis

The final chapter gathers the theory into one picture and one order of operations. The point is
to ensure that normal closures, local completions,
solvable towers, and elementary fixed fields are never again selected by incompatible separate
arguments.

### 17.1 The field diagram

The complete output has the following shape:

~~~text
                                      M
                       _______________|_______________
                      /               |               \
             solvable upper     solvable upper    solvable upper
                  tower               tower             tower
                   /                   |                 \
               L=M^J              M^{H_1}            M^{H_2}
                  |                    |                  |
                  |         no solvability asserted      |
                   \___________________|_________________/
                                      K
                                      |
                            disjoint from D_av
~~~

Here $J$ is the point stabilizer and is required to be solvable. Each $H_i$ is elementary and is
therefore solvable. The total group $G$ may be nonsolvable. All fields are subfields of the same
top field, so conjugation, intersections, composita, and local completion maps are automatic
consequences of the subgroup lattice.

At a controlled place $v$, one homomorphism

$$
\phi_v:G_{K_v}\longrightarrow G
$$

controls the entire diagram. Its image $D_v$ and inertia image $I_v$ give the top local field.
The action on $G/J$ gives the point-field algebra. The action on $G/H_i$ gives every elementary
subfield algebra. If $\phi_v$ is trivial, every field splits completely. At a real place this
triviality is total reality.

### 17.2 The order of construction

The safe order is now forced by the proofs.

1. **Build the geometry.** Construct an evaluation family, compute its generic Galois group and
   stabilizer, prove geometric connectedness, and verify solvability of the stabilizer.
2. **Realize the local torsors.** Exhibit actual local parameters and actual evaluated points;
   then shrink by equivariant local constancy.
3. **Assemble the avoidance field.** Take one finite Galois compositum containing every field
   whose intersection would cause trouble, including earlier top fields when mutual
   disjointness is required.
4. **Specialize once.** Intersect the local boxes with the full-monodromy and base-changed
   connectedness Hilbert conditions.
5. **Take fixed fields afterward.** Define every elementary, character-kernel, and cyclic-layer
   field inside the resulting top field by Galois correspondence.
6. **Use Chebotarev only after fields are fixed.** Select auxiliary primes with desired
   Frobenius classes, outside the finite controlled set, using Theorem 4.3 and Corollary 4.4.
   Read all induced fixed-field factors, solvable-layer Frobenius elements, and character values
   from the single top choice by Corollary 4.7; use Corollary 4.5 when simultaneous splitting in
   a disjoint auxiliary field is required.

Changing this order causes the familiar failures. Taking the normal closure after imposing only
root-field avoidance can introduce an intersection. Choosing subgroup fields separately can
break the lattice. Selecting abstract local subgroups before showing local realizability can
produce impossible data. Using Chebotarev to vary a field confuses prime selection with field
specialization.

### 17.3 Conclusion

Arithmetic approximation has two complementary kinds of freedom. Local topology permits a
parameter to move without changing a finite étale fiber. Hilbert irreducibility permits that
parameter to retain the full generic monodromy and avoid fixed constant extensions. A Galois
approximation datum joins those freedoms to one geometric point: its quotient fiber evaluates
on the target variety, while its top fiber remembers the normal closure.

Once the top fiber is specialized, the difficult compatibility questions become finite group
theory. A point stabilizer controls the upper extension from the point field. Elementary
subgroups control solvable upper towers from their fixed fields. Double cosets control every
local tensor product. Subgroup intersections and generated subgroups control composita and
intersections of fields. Conjugation controls the symmetry of the family. Closure-level
disjointness preserves all finite images throughout the diagram.

The symmetric quintic action displays the design particularly clearly: $S_5$ is nonsolvable,
its point stabilizer $S_4$ is solvable, and its elementary subgroups provide the fixed fields
used in Brauer induction. But the arithmetic theorem applies only after an actual quintic
evaluation family with the required local fibers has been constructed. Flexible-degree
Moret--Bailly approximation does not manufacture that datum, and this book never treats it as if
it did.

The resulting field package is therefore both strong and exact. It supplies controlled normal
closures, exact local completion data, solvable bridges, elementary subfields, mutually
disjoint repetitions, and one compatible fixed-field family. It also identifies the remaining
work honestly: geometry must construct the bridge presentation, and later automorphic theory
must act along the supplied towers. Within those boundaries, the arithmetic approximation step
is complete and no result is lost between a non-Galois point field and the Galois family needed
for descent.
