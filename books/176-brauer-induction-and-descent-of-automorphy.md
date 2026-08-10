# Brauer Induction and Descent of Automorphy

## Contents

1. [What descent is allowed to conclude](#1-what-descent-is-allowed-to-conclude)
   - [Potential automorphy starts upstairs](#11-potential-automorphy-starts-upstairs)
   - [Three conclusions that must not be merged](#12-three-conclusions-that-must-not-be-merged)
   - [Standing conventions](#13-standing-conventions)
   - [The infrastructure ledger](#14-the-infrastructure-ledger)
2. [Characters and representation rings](#2-characters-and-representation-rings)
   - [Characters and semisimplicity](#21-characters-and-semisimplicity)
   - [The character inner product](#22-the-character-inner-product)
   - [Grothendieck groups and virtual representations](#23-grothendieck-groups-and-virtual-representations)
   - [Rational values and rational models](#24-rational-values-and-rational-models)
   - [Permutation characters](#25-permutation-characters)
3. [Induction, restriction, and Mackey theory](#3-induction-restriction-and-mackey-theory)
   - [Induced characters](#31-induced-characters)
   - [Frobenius reciprocity and the projection formula](#32-frobenius-reciprocity-and-the-projection-formula)
   - [Transitivity and conjugation](#33-transitivity-and-conjugation)
   - [The Mackey formula](#34-the-mackey-formula)
   - [A cyclic calculation](#35-a-cyclic-calculation)
4. [Artin induction and its denominators](#4-artin-induction-and-its-denominators)
   - [Rational conjugacy](#41-rational-conjugacy)
   - [A triangular family of permutation characters](#42-a-triangular-family-of-permutation-characters)
   - [Artin induction](#43-artin-induction)
   - [Clearing denominators honestly](#44-clearing-denominators-honestly)
   - [Why Artin induction is not yet enough](#45-why-artin-induction-is-not-yet-enough)
5. [Brauer induction proved integrally](#5-brauer-induction-proved-integrally)
   - [Elementary subgroups](#51-elementary-subgroups)
   - [Why their irreducible characters are monomial](#52-why-their-irreducible-characters-are-monomial)
   - [The local integrality lemma](#53-the-local-integrality-lemma)
   - [Brauer's character criterion](#54-brauers-character-criterion)
   - [The integral induction theorem](#55-the-integral-induction-theorem)
   - [The trivial-character form](#56-the-trivial-character-form)
   - [Signs, positivity, and effectivity](#57-signs-positivity-and-effectivity)
6. [Finite-group diagnostics](#6-finite-group-diagnostics)
   - [A cyclic group](#61-a-cyclic-group)
   - [The character table of $S_3$](#62-the-character-table-of-s_3)
   - [A negative-coefficient Brauer identity](#63-a-negative-coefficient-brauer-identity)
   - [What the dimension equation detects](#64-what-the-dimension-equation-detects)
7. [Galois closures and subgroup fixed fields](#7-galois-closures-and-subgroup-fixed-fields)
   - [The closure diagram](#71-the-closure-diagram)
   - [The direction-reversing dictionary](#72-the-direction-reversing-dictionary)
   - [Solvable towers above fixed fields](#73-solvable-towers-above-fixed-fields)
   - [A nonsolvable total group is not a problem](#74-a-nonsolvable-total-group-is-not-a-problem)
   - [What does not survive passage to a Galois closure](#75-what-does-not-survive-passage-to-a-galois-closure)
   - [The admissible top-field hypothesis](#76-the-admissible-top-field-hypothesis)
8. [Artin formalism for local and global factors](#8-artin-formalism-for-local-and-global-factors)
   - [Local Weil--Deligne factors](#81-local-weil--deligne-factors)
   - [The unramified induction polynomial](#82-the-unramified-induction-polynomial)
   - [Conductors and discriminants](#83-conductors-and-discriminants)
   - [Archimedean and epsilon factors](#84-archimedean-and-epsilon-factors)
   - [Global induction](#85-global-induction)
   - [Virtual quotients](#86-virtual-quotients)
9. [Compatible systems and Brauer operations](#9-compatible-systems-and-brauer-operations)
   - [Restriction and induction of systems](#91-restriction-and-induction-of-systems)
   - [Coefficient fields and roots of unity](#92-coefficient-fields-and-roots-of-unity)
   - [The virtual Brauer system](#93-the-virtual-brauer-system)
   - [Projection back to the base](#94-projection-back-to-the-base)
   - [Local compatibility of the virtual identity](#95-local-compatibility-of-the-virtual-identity)
   - [The effectivity boundary](#96-the-effectivity-boundary)
10. [The automorphic operations](#10-the-automorphic-operations)
    - [Automorphic induction of Hecke characters](#101-automorphic-induction-of-hecke-characters)
    - [Cyclic induction of characters and conditional iteration](#102-cyclic-induction-of-characters-and-conditional-iteration)
    - [Cyclic and solvable base change](#103-cyclic-and-solvable-base-change)
    - [Transitivity, twists, and Mackey compatibility](#104-transitivity-twists-and-mackey-compatibility)
    - [Central characters and conductors](#105-central-characters-and-conductors)
    - [The cuspidal boundary](#106-the-cuspidal-boundary)
11. [Auxiliary automorphic representations over fixed fields](#11-auxiliary-automorphic-representations-over-fixed-fields)
    - [The top automorphic input](#111-the-top-automorphic-input)
    - [Solvable descent to $M^H$](#112-solvable-descent-to-mh)
    - [Twisting by the Brauer character](#113-twisting-by-the-brauer-character)
    - [Galois induction versus automorphic induction](#114-galois-induction-versus-automorphic-induction)
    - [The Brauer $L$-function identity](#115-the-brauer-l-function-identity)
    - [The $S_3$ field diagram](#116-the-s_3-field-diagram)
12. [Descent data, cocycles, and self-twists](#12-descent-data-cocycles-and-self-twists)
    - [Invariance is only the first condition](#121-invariance-is-only-the-first-condition)
    - [The scalar $H^2$ obstruction](#122-the-scalar-h2-obstruction)
    - [The $H^1$ obstruction in a solvable tower](#123-the-h1-obstruction-in-a-solvable-tower)
    - [Character ambiguity and self-twists](#124-character-ambiguity-and-self-twists)
    - [Central characters do not remove the obstruction](#125-central-characters-do-not-remove-the-obstruction)
    - [A self-twisted dihedral representation](#126-a-self-twisted-dihedral-representation)
13. [Constructing a system over the original field](#13-constructing-a-system-over-the-original-field)
    - [The descent datum to be constructed](#131-the-descent-datum-to-be-constructed)
    - [The coherent-cocycle route](#132-the-coherent-cocycle-route)
    - [The determinant-effectivity route](#133-the-determinant-effectivity-route)
    - [Common Frobenius polynomials](#134-common-frobenius-polynomials)
    - [Coefficient descent and Galois conjugates](#135-coefficient-descent-and-galois-conjugates)
    - [Independence of the Brauer decomposition](#136-independence-of-the-brauer-decomposition)
    - [The effective compatible-system theorem](#137-the-effective-compatible-system-theorem)
14. [Analytic continuation and functional equations](#14-analytic-continuation-and-functional-equations)
    - [The quotient construction](#141-the-quotient-construction)
    - [The induced functional equation](#142-the-induced-functional-equation)
    - [Zeros in denominators and uncancelled poles](#143-zeros-in-denominators-and-uncancelled-poles)
    - [When holomorphy follows](#144-when-holomorphy-follows)
    - [What a converse theorem would still need](#145-what-a-converse-theorem-would-still-need)
15. [When automorphy itself descends](#15-when-automorphy-itself-descends)
    - [The solvable descent theorem](#151-the-solvable-descent-theorem)
    - [Why elementary fixed fields do not glue automatically](#152-why-elementary-fixed-fields-do-not-glue-automatically)
    - [Strong multiplicity one as recognition](#153-strong-multiplicity-one-as-recognition)
    - [Independent descent and converse-theorem routes](#154-independent-descent-and-converse-theorem-routes)
    - [The exact hierarchy of conclusions](#155-the-exact-hierarchy-of-conclusions)
16. [Arithmetic invariants under induction and descent](#16-arithmetic-invariants-under-induction-and-descent)
    - [Determinants and polarizations](#161-determinants-and-polarizations)
    - [Parity and archimedean type](#162-parity-and-archimedean-type)
    - [Purity and weights](#163-purity-and-weights)
    - [Local types and monodromy](#164-local-types-and-monodromy)
    - [Integral and residual data](#165-integral-and-residual-data)
17. [Failure modes and hostile checks](#17-failure-modes-and-hostile-checks)
    - [Negative coefficients](#171-negative-coefficients)
    - [Noncuspidal induction](#172-noncuspidal-induction)
    - [Incoherent descent](#173-incoherent-descent)
    - [Coefficient mismatch](#174-coefficient-mismatch)
    - [A quotient with poles](#175-a-quotient-with-poles)
    - [Wrong subgroup and field directions](#176-wrong-subgroup-and-field-directions)
    - [Equality at good places](#177-equality-at-good-places)
18. [The final theorem package](#18-the-final-theorem-package)
    - [The analytic Brauer theorem](#181-the-analytic-brauer-theorem)
    - [The virtual compatible-system theorem](#182-the-virtual-compatible-system-theorem)
    - [The effective descent theorem](#183-the-effective-descent-theorem)
    - [The automorphic descent theorem](#184-the-automorphic-descent-theorem)
    - [The exported descent record](#185-the-exported-descent-record)
    - [Conclusion](#186-conclusion)

## 1. What descent is allowed to conclude

Potential automorphy changes the field on which a representation is known to be
automorphic. The central discipline of this book is to track what can be brought
back to the original field, and which extra theorem is responsible for each
strengthening of the conclusion.

### 1.1 Potential automorphy starts upstairs

Let $F$ be a totally real number field and let

$$
\rho_{\lambda_0}:G_F\longrightarrow
\operatorname{GL}_n(E_{\lambda_0})
$$

be a continuous semisimple representation. Potential automorphy supplies a finite
totally real extension $K/F$ and an automorphic representation over $K$ whose
Galois representation is

$$
\rho_{\lambda_0}|_{G_K}.
$$

This is a theorem over $K$. It is not an automorphy theorem over $F$. The distinction
does not disappear when the Frobenius traces happen to come from a representation
already defined on $G_F$. The automorphic object lives upstairs, while its proposed
descent requires a separate global construction.

The first temptation is to replace $K$ by its Galois closure $M$ over $F$. This gives
a convenient finite group

$$
G=\operatorname{Gal}(M/F),
$$

but it creates no automorphic base change from $K$ to $M$. The extension $M/K$ may
be nonsolvable. The representation $\rho_{\lambda_0}|_{G_M}$ certainly exists, but
its automorphy is a new assertion. Thus the Brauer argument begins only after an
honest top-field automorphy hypothesis has been verified.

Once such a Galois top field is available, Brauer induction decomposes the trivial
character of $G$ into induced one-dimensional characters from solvable subgroups.
The corresponding fixed fields need not be solvable over $F$. What is solvable is
the extension from each fixed field up to $M$. This reversal is the mechanism that
makes a nonsolvable $G$ usable.

### 1.2 Three conclusions that must not be merged

The descent argument has three possible endpoints.

The weakest is an identity in a Grothendieck group. It yields an identity of Euler
products and, after automorphic input over auxiliary fields, a meromorphic
continuation and functional equation. Negative coefficients become denominators.
Nothing in this statement produces an actual representation or an automorphic
object over $F$.

The second endpoint is an actual compatible system over $F$. Reaching it requires
effectivity: the virtual class must be represented by honest semisimple
representations at every coefficient place. A coherent descent datum is one source
of effectivity. An independently constructed determinant of the correct dimension
is another. Brauer induction by itself supplies neither.

The strongest endpoint is automorphy over $F$. It requires a theorem that constructs
an automorphic representation over $F$: solvable descent with coherent choices, an
independent nonsolvable descent theorem, or a converse theorem with all of its
analytic hypotheses. Strong multiplicity one can identify such a representation
once it exists. It cannot manufacture it from a virtual quotient.

The logical chain is therefore

~~~text
Brauer identity in a Grothendieck group
                 |
                 v
virtual compatible class and quotient of L-functions
                 |
                 | effectivity or coherent descent data
                 v
actual compatible system over the base
                 |
                 | automorphic descent or converse theorem
                 v
actual automorphic representation over the base
~~~

Every theorem in this book states where it stops in this diagram.

### 1.3 Standing conventions

For a number field $L$, write $G_L=\operatorname{Gal}(\overline L/L)$ and
$C_L=L^\times\backslash\mathbf A_L^\times$. Local and global reciprocity send a
uniformizer to arithmetic Frobenius. Thus

$$
\chi_\ell(\operatorname{Frob}_v)=q_v
$$

for the cyclotomic character at $v\nmid\ell$.

All finite-group representations in Chapters 2--6 are finite-dimensional complex
representations. Their Grothendieck group is denoted $R(G)$. A virtual character is
an element of $R(G)$, not a representation with a negative-dimensional vector space.

For a finite extension $L/K$, restriction of Galois representations goes upward in
fields,

$$
G_L\subset G_K,
$$

while a Hecke character goes upward by pullback through the norm
$N_{L/K}:C_L\to C_K$. Induction goes in the opposite direction and multiplies rank
by $[L:K]$.

Local Euler factors are written in the covariant arithmetic normalization. If
$D_v=(r_v,N_v)$ is a Weil--Deligne representation, then

$$
L_v(s,D_v)=
\det\left(1-q_v^{-s}r_v(\operatorname{Frob}_v)
\mid(\ker N_v)^{I_v}\right)^{-1}.
$$

Completed functional equations are written in the unitary variable as

$$
\Lambda(s,D)=\varepsilon(D)\Lambda(1-s,D^\vee).
$$

An algebraic normalization is converted to this one before the formula is applied.

### 1.4 The infrastructure ledger

A descent argument must record the following data before using Brauer induction.

| layer | required record |
|---|---|
| finite group | $G$, the elementary subgroups $H_i$, the characters $\theta_i$, and the signed integers $n_i$ |
| fields | the Galois top field $M/F$, each fixed field $M^{H_i}$, and the exact cyclic tower from $M^{H_i}$ to $M$ |
| top automorphy | a named cuspidal automorphic representation over $M$ and the precise member of its compatible system |
| descent | invariance, the chosen intertwiners or cyclic descent chain, all twisting ambiguities, and the relevant $H^1$ or $H^2$ class |
| coefficients | one number field containing Hecke data and all values of the $\theta_i$, together with every coefficient embedding used |
| local data | arithmetic Frobenius, Weil--Deligne parameters, conductors, archimedean factors, and the proved local--global compatibility range |
| conclusion | virtual identity, actual system, meromorphic continuation, holomorphy, or automorphy, with no stronger word substituted |

The ledger is not administrative decoration. Each row blocks a specific false
shortcut: a wrong fixed-field direction, a nonexistent nonsolvable base change, an
uncancelled cocycle, an addition of representations over unrelated coefficient
fields, or an assertion of holomorphy from a quotient.

## 2. Characters and representation rings

Brauer induction is first of all a statement about a lattice of characters. We
therefore need to distinguish actual representations from signed classes, rational
values from rational models, and integral coefficients from positive ones before
any arithmetic object enters the discussion.

### 2.1 Characters and semisimplicity

Let $G$ be finite. A complex representation $V$ has character

$$
\chi_V(g)=\operatorname{tr}(g\mid V).
$$

The character is constant on conjugacy classes. Maschke's averaging argument makes
every $G$-stable subspace admit a $G$-stable complement: if $p:V\to W$ is any
projection onto a stable subspace, then

$$
p_G=\frac1{|G|}\sum_{g\in G}gpg^{-1}
$$

is a $G$-equivariant projection. Hence every representation is a direct sum of
irreducibles.

Two semisimple representations are isomorphic if and only if their characters are
equal. Indeed, the multiplicity of an irreducible representation can be recovered
by the inner product below. This is the finite-group prototype of the later
Chebotarev and Brauer--Nesbitt uniqueness statements: character data identify a
semisimplification, not an extension class.

If $V$ is defined over a characteristic-zero field embedded in $\mathbf C$, its
character values are algebraic integers. For $g$ of order $m$, every eigenvalue of
$g$ is an $m$-th root of unity. Thus $\chi_V(g)$ lies in a cyclotomic integer ring.
This elementary integrality will remove denominators in the proof of Brauer's
character criterion.

### 2.2 The character inner product

For class functions $f,h:G\to\mathbf C$, put

$$
\langle f,h\rangle_G
=\frac1{|G|}\sum_{g\in G}f(g)\overline{h(g)}.
$$

If $V,W$ have characters $\chi_V,\chi_W$, averaging an arbitrary linear map
$V\to W$ gives

$$
\langle\chi_V,\chi_W\rangle_G
=\dim_\mathbf C\operatorname{Hom}_G(V,W).
$$

Schur's lemma therefore gives the orthonormality of irreducible characters. If
$\operatorname{Irr}(G)$ denotes their set, every class function has an expansion

$$
f=\sum_{\chi\in\operatorname{Irr}(G)}
\langle f,\chi\rangle_G\chi.
$$

A class function is a character of an actual representation exactly when all these
coefficients are nonnegative integers. It is a generalized, or virtual, character
exactly when they are arbitrary integers. Integrality and positivity are separate
conditions. Brauer induction proves the first kind of statement and usually
violates the second.

Complex conjugation may be replaced by inversion on characters:

$$
\overline{\chi(g)}=\chi(g^{-1}).
$$

This makes the inner product algebraic and permits its Galois behavior to be
calculated in a cyclotomic field.

### 2.3 Grothendieck groups and virtual representations

The representation ring $R(G)$ is the free abelian group on
$\operatorname{Irr}(G)$. Addition comes from direct sum and multiplication from
tensor product. An element has a unique expression

$$
x=\sum_{\chi\in\operatorname{Irr}(G)}m_\chi[\chi],
\qquad m_\chi\in\mathbf Z.
$$

It is effective if every $m_\chi\ge0$. The dimension map

$$
\dim:R(G)\longrightarrow\mathbf Z
$$

is a ring homomorphism, but a positive dimension does not imply effectivity. For
example $2[1]-[\varepsilon]$ has dimension one for any nontrivial linear character
$\varepsilon$, yet it is not an actual representation.

The character map embeds $R(G)$ into the lattice of class functions. The inner
product makes this lattice self-dual:

$$
R(G)=
\{f\in R(G)\otimes_\mathbf Z\mathbf Q:
\langle f,R(G)\rangle_G\subset\mathbf Z\}.
\tag{2.1}
$$

Formula (2.1) is the final lattice step in the proof of Brauer induction. It also
explains why rational spanning is insufficient: a full-rank sublattice can have
nontrivial finite index.

### 2.4 Rational values and rational models

A character is **rational-valued** if $\chi(g)\in\mathbf Q$ for every $g$. This does
not mean that the representation has a model over $\mathbf Q$. A rational-valued
irreducible character can have a nontrivial Schur index, so its smallest field of
definition may be larger.

Three groups should therefore be distinguished:

$$
R(G),\qquad
R(G)_{\mathbf Q\text{-val}},\qquad
R_\mathbf Q(G).
$$

The middle group consists of virtual complex characters with rational values. The
last is the Grothendieck group of finite-dimensional $\mathbf Q[G]$-modules. There is
a character map

$$
R_\mathbf Q(G)\longrightarrow R(G)_{\mathbf Q\text{-val}},
$$

but it need not be onto integrally.

Artin induction concerns rational-valued characters as class functions. Brauer
induction concerns the full integral group $R(G)$. Later coefficient descent has the
same distinction: rational Frobenius traces do not automatically supply a model over
the rational trace field.

### 2.5 Permutation characters

For a subgroup $H\le G$, the permutation representation on $G/H$ is

$$
\mathbf C[G/H]=\operatorname{Ind}_H^G1_H.
$$

Its character is

$$
\operatorname{Ind}_H^G1_H(g)
=\#\{xH\in G/H:g xH=xH\}.
\tag{2.2}
$$

Equivalently,

$$
\operatorname{Ind}_H^G1_H(g)
=\frac1{|H|}\#\{x\in G:x^{-1}gx\in H\}.
\tag{2.3}
$$

Permutation characters are actual and rational-valued. Their degrees are the
indices $[G:H]$. Artin induction says that they span the rational-valued character
space after rational scalars when $H$ ranges over cyclic subgroups. It does not say
that the required coefficients are nonnegative or integral.

## 3. Induction, restriction, and Mackey theory

The later field manipulations are shadows of four finite-group operations:
restriction, induction, conjugation, and tensor product. Writing their formulas
now prevents a field inclusion or local component from being reversed when the
same operations reappear for Galois and automorphic representations.

### 3.1 Induced characters

Let $H\le G$ and let $W$ be an $H$-representation. The induced representation is

$$
\operatorname{Ind}_H^G W
=\mathbf C[G]\otimes_{\mathbf C[H]}W.
$$

Choose representatives $x$ for the left cosets $G/H$. As a vector space it is the
direct sum of copies $x\otimes W$. An element $g\in G$ permutes these copies and acts
inside a fixed copy only when $x^{-1}gx\in H$. Taking traces gives

$$
\operatorname{Ind}_H^G\theta(g)
=\frac1{|H|}
\sum_{\substack{x\in G\\x^{-1}gx\in H}}
\theta(x^{-1}gx).
\tag{3.1}
$$

In particular,

$$
\dim\operatorname{Ind}_H^G W=[G:H]\dim W.
\tag{3.2}
$$

Restriction is simpler: $\operatorname{Res}_H^GV$ is the same vector space with the
action restricted to $H$. Both operations are additive and hence act on
Grothendieck groups.

### 3.2 Frobenius reciprocity and the projection formula

There is a natural isomorphism

$$
\operatorname{Hom}_G(\operatorname{Ind}_H^GW,V)
\simeq
\operatorname{Hom}_H(W,\operatorname{Res}_H^GV).
$$

On characters this is Frobenius reciprocity:

$$
\langle\operatorname{Ind}_H^G\theta,\chi\rangle_G
=\langle\theta,\operatorname{Res}_H^G\chi\rangle_H.
\tag{3.3}
$$

The projection formula is equally important:

$$
V\otimes\operatorname{Ind}_H^GW
\simeq
\operatorname{Ind}_H^G(\operatorname{Res}_H^GV\otimes W).
\tag{3.4}
$$

An explicit map sends

$$
v\otimes(x\otimes w)
\longmapsto
x\otimes(x^{-1}v\otimes w).
$$

It is well defined under the $H$-relation and is $G$-equivariant. Formula (3.4) is
the exact reason that a Brauer identity for $1_G$ becomes an identity for an
arbitrary representation. It is also the group-theoretic source of the later
formula

$$
\rho\otimes\operatorname{Ind}\theta
=\operatorname{Ind}(\rho|\otimes\theta).
$$

### 3.3 Transitivity and conjugation

For $D\le H\le G$,

$$
\operatorname{Ind}_H^G\operatorname{Ind}_D^H
\simeq\operatorname{Ind}_D^G,
\qquad
\operatorname{Res}_D^H\operatorname{Res}_H^G
=\operatorname{Res}_D^G.
\tag{3.5}
$$

If $g\in G$ and ${}^gH=gHg^{-1}$, the conjugate character is

$$
{}^g\theta(ghg^{-1})=\theta(h),
$$

and

$$
\operatorname{Ind}_{{}^gH}^G({}^g\theta)
=\operatorname{Ind}_H^G\theta.
\tag{3.6}
$$

Thus conjugate subgroups give the same induced character. In the field dictionary,
they give conjugate fixed fields. A Brauer decomposition may be organized by
conjugacy classes of pairs $(H,\theta)$ without changing its meaning.

### 3.4 The Mackey formula

Let $K,H\le G$. Choose representatives $x$ for the double cosets $K\backslash G/H$.
The $K$-set $G/H$ is the disjoint union of the orbits $KxH/H$, and the stabilizer of
$xH$ is

$$
K\cap xHx^{-1}.
$$

Decomposing the induced representation along these orbits gives the Mackey formula

$$
\operatorname{Res}_K^G\operatorname{Ind}_H^GW
\simeq
\bigoplus_{x\in K\backslash G/H}
\operatorname{Ind}_{K\cap xHx^{-1}}^K
\operatorname{Res}_{K\cap xHx^{-1}}^{xHx^{-1}}({}^xW).
\tag{3.7}
$$

Every subgroup in (3.7) is an actual intersection. Replacing it by $K\cap H$ drops
the conjugation and is generally wrong. This formula later controls base change of
an automorphic induction: the double cosets record the components of a tensor
product of fields.

The Mackey formula also implies the restriction--corestriction relation in
characters. When $K$ is normal, the double cosets simplify, but the conjugates of
$W$ remain. Normality removes an indexing complication; it does not make every
conjugate representation identical.

### 3.5 A cyclic calculation

Let $G=C_m=\langle c\rangle$. Every irreducible character is one-dimensional:

$$
\theta_j(c)=\zeta_m^j,
\qquad 0\le j<m.
$$

Hence

$$
R(C_m)=\bigoplus_{j=0}^{m-1}\mathbf Z[\theta_j].
$$

There is no induction problem to solve: each irreducible is already induced from
the elementary subgroup $G$ itself. If $D=C_d\le C_m$ and $\phi$ is a character of
$D$, then

$$
\operatorname{Ind}_D^{C_m}\phi
=\sum_{\substack{\theta\in\widehat{C_m}\\\theta|_D=\phi}}\theta.
\tag{3.8}
$$

Formula (3.8) follows immediately from Frobenius reciprocity. It is the finite-group
version of the twisting fiber in cyclic base change: all extensions of one character
differ by characters of $C_m/D$.

## 4. Artin induction and its denominators

Permutation characters from cyclic subgroups already span the rational character
space. That fact explains why induction can control $L$-functions, but its
denominators also expose why Artin induction alone cannot construct a single
descent object.

### 4.1 Rational conjugacy

Let $e$ be the exponent of $G$ and let $K=\mathbf Q(\zeta_e)$. For an integer $a$
prime to $e$, let $\sigma_a\in\operatorname{Gal}(K/\mathbf Q)$ send
$\zeta_e$ to $\zeta_e^a$. Every character satisfies

$$
\sigma_a(\chi(g))=\chi(g^a).
\tag{4.1}
$$

Indeed, both sides are obtained by raising every eigenvalue of $g$ to the $a$-th
power.

Two elements $g,h$ are **rationally conjugate** if $h$ is conjugate to $g^a$ for
some $a$ prime to $|g|$. Equivalently, the cyclic subgroups $\langle g\rangle$ and
$\langle h\rangle$ are conjugate and $h$ corresponds to a generator after that
conjugation. A rational-valued character is constant on rational conjugacy classes
by (4.1).

Conversely, a rational-valued class function satisfying (4.1) is determined by one
value on each conjugacy class of cyclic subgroups, evaluated at a generator. Thus
the vector space of rational class functions satisfying the character Galois law
has dimension equal to the number of conjugacy classes of cyclic subgroups.

### 4.2 A triangular family of permutation characters

Choose one cyclic subgroup $C$ from each conjugacy class and a generator $c_C$.
Put

$$
u_C=\operatorname{Ind}_C^G1_C.
$$

By (2.3),

$$
u_C(c_D)\ne0
\quad\Longleftrightarrow\quad
D\text{ is conjugate to a subgroup of }C.
\tag{4.2}
$$

If $D=C$, then an element $x$ contributes precisely when it normalizes $C$, so

$$
u_C(c_C)=\frac{|N_G(C)|}{|C|}>0.
\tag{4.3}
$$

Order the cyclic subgroups by nondecreasing order. The matrix

$$
\bigl(u_C(c_D)\bigr)_{D,C}
$$

is triangular with nonzero diagonal after subgroups of equal order are grouped by
conjugacy. Indeed, containment between equal-order cyclic groups is equality up to
conjugacy. The functions $u_C$ are therefore linearly independent. Their number is
the dimension found in Section 4.1, so they form a basis over $\mathbf Q$.

This proof does more than count dimensions. It displays the denominator matrix.
Any denominator bound comes from inverting this integral triangular matrix; it
should be recorded rather than suppressed.

### 4.3 Artin induction

**Theorem 4.1 (Artin induction).** If $\chi$ is a rational-valued virtual character
of $G$, then there are rational numbers $a_C$ such that

$$
\chi=\sum_C a_C\operatorname{Ind}_C^G1_C,
\tag{4.4}
$$

where $C$ ranges over cyclic subgroups up to conjugacy.

**Proof.** The character $\chi$ obeys (4.1), and rationality makes it constant on
rational conjugacy classes. It therefore belongs to the vector space in Section 4.1.
The triangular basis of Section 4.2 gives the unique expansion (4.4). $\square$

For an arbitrary virtual character $\psi$, multiply (4.4), with $\chi=1_G$, by
$\psi$ and apply the projection formula:

$$
\psi
=\sum_C a_C
\operatorname{Ind}_C^G(\operatorname{Res}_C^G\psi).
\tag{4.5}
$$

Every character of a cyclic group is a sum of linear characters. Hence induced
linear characters from cyclic subgroups span $R(G)\otimes\mathbf Q$. This full-rank
statement will be used in the lattice proof of Brauer induction.

### 4.4 Clearing denominators honestly

Let $A_G$ be the triangular integer matrix in Section 4.2. Its determinant is
nonzero. A common multiple of the denominators of the entries of $A_G^{-1}$ gives
an integer $d_G>0$ such that

$$
d_G\chi=\sum_C b_C\operatorname{Ind}_C^G1_C,
\qquad b_C\in\mathbf Z
\tag{4.6}
$$

for every integral rational-valued character $\chi$. The determinant
$|\det A_G|$ is one valid common multiple after the basis lattices have been fixed,
though it is rarely minimal.

No later argument needs a minimal denominator. What matters is that (4.6) has
multiplied the left side. Dividing it back is legitimate in
$R(G)\otimes\mathbf Q$, not in $R(G)$.

The coefficients $b_C$ need not be positive. Evaluating (4.6) at the identity gives

$$
d_G\chi(1)=\sum_C b_C[G:C].
\tag{4.7}
$$

This degree equation is a necessary audit, not a proof of the character identity.
Values on all rational conjugacy classes are required.

### 4.5 Why Artin induction is not yet enough

Artin induction has two limitations for descent.

First, the rational denominators in (4.4) would produce fractional powers of
$L$-functions. Such powers are not canonically single-valued meromorphic functions.
Clearing denominators proves an identity for $L(s,\rho)^{d_G}$, not for
$L(s,\rho)$ itself, unless a root is independently specified.

Second, an integral relation obtained after clearing denominators still has
$d_G1_G$ on the left. The projection formula then reconstructs $d_G[\rho]$, not
$[\rho]$. For actual compatible systems this distinction is decisive.

Brauer induction removes the denominator by enlarging the permitted subgroups from
cyclic groups to elementary groups and by allowing nontrivial one-dimensional
characters. It does not remove negative signs.

## 5. Brauer induction proved integrally

Descent needs the coefficient of the original object to be exactly one, not a
positive multiple. The purpose of this chapter is to remove Artin's denominators
prime by prime and to prove the integral theorem rather than use it as a slogan.

### 5.1 Elementary subgroups

Fix a prime $p$. A finite group $E$ is **$p$-elementary** if

$$
E=C\times P,
\tag{5.1}
$$

where $C$ is cyclic of order prime to $p$ and $P$ is a $p$-group. A group is
**elementary** if it is $p$-elementary for some $p$.

Every elementary group is solvable. The cyclic factor is abelian, while a finite
$p$-group has a central series whose successive factors can be refined to groups of
order $p$. Moreover, every subgroup of a $p$-elementary group is again
$p$-elementary. To see this, let $D\le C\times P$. Every element of $D$ has commuting
$p$-part and prime-to-$p$ part, each of which is a power of that element and hence
lies in $D$. Therefore

$$
D=(D\cap C)\times(D\cap P).
\tag{5.2}
$$

The direct-product requirement in (5.1) is stronger than solvability. The group
$S_3$ is solvable but is not elementary. Brauer induction uses elementary
subgroups because their character theory is monomial and because they detect
integrality prime by prime.

### 5.2 Why their irreducible characters are monomial

A character is monomial if it is induced from a one-dimensional character of a
subgroup. We first prove the needed fact for $p$-groups.

**Lemma 5.1.** Every irreducible character of a finite $p$-group $P$ is monomial.

**Proof.** Induct on $|P|$. Linear characters need no argument. For a nonlinear
irreducible character $\psi$, quotient by its kernel; induction in the quotient and
inflation reduce us to the case that $\psi$ is faithful.

The group $P$ is then nonabelian. The center of $P/Z(P)$ is nontrivial, so the
preimage of a subgroup of order $p$ in that center is an abelian normal subgroup
$A$ properly containing $Z(P)$. Choose a linear constituent $\lambda$ of
$\operatorname{Res}_A^P\psi$, and let

$$
I=\{g\in P:{}^g\lambda=\lambda\}
$$

be its inertia group. If $I=P$, Clifford theory says that $A$ acts on the irreducible
space through the scalar character $\lambda$. Then every commutator $[P,A]$ acts
trivially. Faithfulness gives $[P,A]=1$, so $A\subset Z(P)$, a contradiction.
Thus $I<P$.

Clifford theory now gives an irreducible character $\phi$ of $I$ above $\lambda$
such that

$$
\psi=\operatorname{Ind}_I^P\phi.
$$

By induction, $\phi=\operatorname{Ind}_D^I\theta$ for a linear character $\theta$
of a subgroup $D\le I$. Transitivity yields

$$
\psi=\operatorname{Ind}_D^P\theta.
$$

$\square$

If $E=C\times P$ is $p$-elementary, every irreducible character is
$\alpha\otimes\psi$, with $\alpha$ linear on $C$ and $\psi$ irreducible on $P$.
Write $\psi=\operatorname{Ind}_D^P\theta$ by Lemma 5.1. Then

$$
\alpha\otimes\psi
=\operatorname{Ind}_{C\times D}^{C\times P}(\alpha\otimes\theta).
\tag{5.3}
$$

Thus every irreducible character of an elementary group is induced from a linear
character of an elementary subgroup.

### 5.3 The local integrality lemma

The denominator-removal step is local at a rational prime. Write $\mathbf Z_{(p)}$
for the rationals with denominator prime to $p$.

**Lemma 5.2 (the $p$-section integrality lemma).** Let $f$ be a class function on
$G$ with values in a cyclotomic field. Assume:

1. for every integer $a$ prime to the exponent of $G$,
   $$
   \sigma_a(f(g))=f(g^a);
   $$
2. the restriction of $f$ to every $p$-elementary subgroup is a generalized
   character.

Then, for every character $\chi$ of $G$,

$$
\langle f,\chi\rangle_G\in\mathbf Z_{(p)}.
\tag{5.4}
$$

**Proof.** Every $g\in G$ has a unique commuting factorization

$$
g=su=us,
$$

where $s$ has order prime to $p$ and $u$ has $p$-power order. Partition the character
sum into the $p$-sections determined by the conjugacy class of $s$. For a fixed
$s$, put $C_s=C_G(s)$. Its contribution is

$$
b_s=
\frac1{|C_s|}
\sum_{\substack{u\in C_s\\u\text{ a }p\text{-element}}}
f(su)\overline{\chi(su)}.
\tag{5.5}
$$

We need one finite averaging fact. If $C$ is finite and $A$ is a
conjugacy-invariant function on its $p$-elements, then

$$
\frac1{|C|}\sum_{u\text{ a }p\text{-element}}A(u)
$$

is a $\mathbf Z_{(p)}$-linear combination of averages

$$
\frac1{|Q|}\sum_{u\in Q}A(u)
\tag{5.6}
$$

over $p$-subgroups $Q\le C$.

Here is a direct proof. Let $P$ be a Sylow $p$-subgroup of $C$ and let

$$
\upsilon_P=\operatorname{Ind}_P^C1
$$

be the permutation character of $C/P$. If $x$ is not a $p$-element, then $x$
fixes no coset and $\upsilon_P(x)=0$. If $x$ is a $p$-element, it lies in a Sylow
subgroup, so $\upsilon_P(x)>0$. More precisely, $\upsilon_P(x)$ is
$[N_C(P):P]$ times the number of Sylow
$p$-subgroups containing $x$. The first factor is prime to $p$. The cyclic
$p$-group $\langle x\rangle$ acts by conjugation on the set of Sylow subgroups;
its fixed points are exactly the Sylow subgroups containing $x$. All nonfixed
orbits have size divisible by $p$, while the total number of Sylow subgroups is
congruent to $1$ modulo $p$. Hence

$$
p\nmid\upsilon_P(x)
\qquad(x\text{ a }p\text{-element}).
$$

Let $a_1,\ldots,a_r$ be the distinct nonzero values taken by $\upsilon_P$. They are units
of $\mathbf Z_{(p)}$. The polynomial

$$
P_p(T)=1-\prod_{j=1}^r\left(1-\frac{T}{a_j}\right)
\in\mathbf Z_{(p)}[T]
$$

has zero constant term and satisfies

$$
P_p(\upsilon_P(x))=
\begin{cases}
1,&x\text{ a }p\text{-element},\\
0,&x\text{ otherwise}.
\end{cases}
$$

Every power $\upsilon_P^m$ is the permutation character of the diagonal action on
$(C/P)^m$. Its orbits are transitive $C$-sets $C/Q$, where $Q$ is an intersection
of conjugates of $P$ and hence a $p$-subgroup. Since $P_p$ has no constant term,
the characteristic function of the $p$-elements is consequently a
$\mathbf Z_{(p)}$-linear combination of the characters
$\operatorname{Ind}_Q^C1$. Pairing this identity with the extension of $A$ by zero
off the $p$-elements and using Frobenius reciprocity gives (5.6). This proves the
finite averaging fact without a denominator divisible by $p$.

Apply (5.6) to

$$
A(u)=f(su)\overline{\chi(su)}.
$$

For every $Q$ occurring there, $\langle s\rangle\times Q$ is $p$-elementary.
Expand the two restrictions on this direct product as

$$
f|_{\langle s\rangle\times Q}
=\sum_{\alpha,\phi}m_{\alpha,\phi}\,\alpha\otimes\phi,
$$

$$
\chi|_{\langle s\rangle\times Q}
=\sum_{\beta,\psi}n_{\beta,\psi}\,\beta\otimes\psi,
$$

with integral coefficients in the first line and nonnegative integral coefficients
in the second. Orthogonality on $Q$ gives

$$
\frac1{|Q|}\sum_{u\in Q}f(su)\overline{\chi(su)}
=\sum_{\alpha,\beta,\phi}
m_{\alpha,\phi}n_{\beta,\phi}
\alpha(s)\overline{\beta(s)}.
\tag{5.7}
$$

The right side is an algebraic integer. Thus every $b_s$ is integral at every prime
of the cyclotomic field above $p$, and so is their sum
$\langle f,\chi\rangle_G$.

Finally, the Galois law for $f$ and the same law for $\chi$ show that the inner
product is fixed by every automorphism of the cyclotomic field: apply $\sigma_a$ to
the sum and use the bijection $g\mapsto g^a$. Hence the inner product is rational.
A rational number integral at all primes above $p$ belongs to $\mathbf Z_{(p)}$.
This proves (5.4). $\square$

The role of the elementary subgroup is now visible. The prime-to-$p$ element $s$
generates the cyclic factor, and a $p$-subgroup of its centralizer supplies the other
factor. Solvable subgroups without this direct-product structure do not arise from
the $p$-section calculation.

### 5.4 Brauer's character criterion

**Theorem 5.3 (Brauer's character criterion).** A cyclotomic-valued class function
$f$ on $G$ satisfying the character Galois law is a generalized character if and
only if its restriction to every elementary subgroup is a generalized character.

**Proof.** The forward implication follows because restriction preserves virtual
characters. Conversely, fix an irreducible character $\chi$ of $G$. For every prime
$p$, the restrictions to all $p$-elementary subgroups satisfy Lemma 5.2, so

$$
\langle f,\chi\rangle_G\in\mathbf Z_{(p)}.
$$

The Galois argument in that lemma shows that this inner product is rational. A
rational number lying in $\mathbf Z_{(p)}$ for every prime $p$ is an integer. Hence
all irreducible-character coefficients of $f$ are integers, and $f$ is a generalized
character. $\square$

The Galois-law hypothesis is automatic in the application below because the class
function belongs to $R(G)\otimes\mathbf Q$. It is stated explicitly here so that the
criterion is not falsely applied to an arbitrary cyclotomic-valued class function.

This theorem is an integrality test. It does not test nonnegativity. A class function
can restrict to virtual characters everywhere and still have negative irreducible
multiplicities.

### 5.5 The integral induction theorem

Let $L(G)\subset R(G)$ be the subgroup generated by

$$
\operatorname{Ind}_H^G\theta,
\tag{5.8}
$$

where $H$ is elementary and $\theta$ is one-dimensional.

**Theorem 5.4 (Brauer induction).** One has

$$
L(G)=R(G).
\tag{5.9}
$$

Equivalently, every virtual character $\chi$ has an expression

$$
\chi=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i,
\qquad n_i\in\mathbf Z,
\tag{5.10}
$$

with $H_i$ elementary and $\theta_i$ one-dimensional.

**Proof.** Artin induction and the projection formula (4.5) show that induced linear
characters from cyclic subgroups span $R(G)\otimes\mathbf Q$. Since cyclic groups
are elementary, $L(G)$ has full rank in $R(G)$.

Assume $L(G)\ne R(G)$. Because both are full-rank lattices and $R(G)$ is self-dual,
there is

$$
f\in R(G)\otimes\mathbf Q
$$

such that

$$
\langle f,L(G)\rangle_G\subset\mathbf Z,
\qquad
f\notin R(G).
\tag{5.11}
$$

Let $E\le G$ be elementary. To prove that $\operatorname{Res}_E^Gf$ is a generalized
character, pair it with an irreducible character $\phi$ of $E$. By Section 5.2,

$$
\phi=\operatorname{Ind}_D^E\theta
$$

for a linear character $\theta$ of an elementary subgroup $D\le E$. Frobenius
reciprocity and transitivity give

$$
\begin{aligned}
\langle\operatorname{Res}_E^Gf,\phi\rangle_E
&=\langle\operatorname{Res}_D^Gf,\theta\rangle_D\\
&=\langle f,\operatorname{Ind}_D^G\theta\rangle_G
\in\mathbf Z.
\end{aligned}
\tag{5.12}
$$

Thus every elementary restriction of $f$ is a generalized character. Theorem 5.3
implies $f\in R(G)$, contradicting (5.11). Therefore $L(G)=R(G)$. $\square$

The proof has four load-bearing parts: Artin gives full rank, elementary groups are
monomial, the local lemma removes one prime at a time, and self-duality of the
character lattice turns local integrality into equality of lattices. Omitting any
one of them leaves only a rational or unproved assertion.

### 5.6 The trivial-character form

Applying Theorem 5.4 to $1_G$ gives the form used in descent:

$$
\boxed{
1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i.}
\tag{5.13}
$$

Tensoring with any $G$-representation $V$ and using (3.4) yields

$$
[V]=\sum_i n_i
\left[
\operatorname{Ind}_{H_i}^G
(\operatorname{Res}_{H_i}^GV\otimes\theta_i)
\right]
\quad\text{in }R(G).
\tag{5.14}
$$

For a general rational-valued character, Theorem 5.4 still gives an integral
decomposition (5.10). The individual summands may take values in cyclotomic fields
even when their signed sum is rational. If termwise coefficient rationality is
needed, one must group Galois-conjugate terms or enlarge the coefficient field. Such
grouping can reintroduce a common multiple if it is done by averaging, so the exact
integral identity should be retained before any descent of coefficients is attempted.

Evaluating (5.13) at the identity gives the rank audit

$$
1=\sum_i n_i[G:H_i].
\tag{5.15}
$$

For an $n$-dimensional $V$, (5.14) has dimension

$$
n=\sum_i n_i\,n[G:H_i].
$$

### 5.7 Signs, positivity, and effectivity

Suppose every $n_i$ in (5.13) were nonnegative. Every induced linear character has
positive degree $[G:H_i]$. Equation (5.15) would force a single term of degree one,
so $H_i=G$, $n_i=1$, and $\theta_i=1_G$. If $G$ is not elementary, this term is not
permitted. Hence negative coefficients are unavoidable for every non-elementary
group.

This simple degree argument has far-reaching consequences. Formula (5.14) is an
identity in $R(G)$ because $V$ already exists. If analogous terms are constructed
at a different coefficient prime without a known $V$, their signed sum is merely a
virtual representation. The fact that its total dimension is positive does not make
it effective.

Likewise,

$$
\prod_i L_i(s)^{n_i}
$$

is a quotient when some $n_i<0$. It is not the standard $L$-function of an
isobaric sum, since isobaric multiplicities are nonnegative. Brauer induction removes
denominators in the character identity by accepting negative multiplicities; it does
not convert subtraction into an automorphic operation.

## 6. Finite-group diagnostics

Abstract induction formulas are easy to misread because a rank equation can remain
correct after the character itself has changed. Cyclic groups and $S_3$ provide
small, fully computable tests for signs, character placement, and subgroup indices.

### 6.1 A cyclic group

For $G=C_m$ with $m>1$, the group itself is elementary: for any prime $p\mid m$,
it is the direct product of its prime-to-$p$ part and its cyclic Sylow
$p$-subgroup. The trivial group is $p$-elementary for every $p$ by taking both
factors trivial. The Brauer identity can therefore be taken to be

$$
1_G=\operatorname{Ind}_G^G1_G.
\tag{6.1}
$$

There are no negative coefficients and no auxiliary fixed field. This does not
contradict Section 5.7, because $G$ is elementary.

The complete character ring is generated by the linear characters
$\theta_j(c)=\zeta_m^j$. Restriction to a subgroup and induction back are given by
(3.8). If $M/F$ is cyclic with group $C_m$, these characters correspond by class
field theory to the finite-order Hecke characters of $F$ that are trivial after
norm pullback from $M$. They form the twisting group of a cyclic descent fiber.

This diagnostic checks three conventions at once. Characters of the quotient
$G_F/G_M$ live on the lower field $F$, their pullbacks are trivial on $G_M$, and
twisting by them does not change base change to $M$.

### 6.2 The character table of $S_3$

Let $t$ be a transposition and $c$ a three-cycle. The irreducible character table is

| character | $1$ | $t$ | $c$ |
|---|---:|---:|---:|
| $1$ | $1$ | $1$ | $1$ |
| $\operatorname{sgn}$ | $1$ | $-1$ | $1$ |
| $\operatorname{std}$ | $2$ | $0$ | $-1$ |

Let $C_2=\langle t\rangle$ and $C_3=\langle c\rangle$. Frobenius reciprocity gives

$$
\operatorname{Ind}_{C_2}^{S_3}1
=1+\operatorname{std},
\tag{6.2}
$$

because $\operatorname{std}|_{C_2}=1\oplus\operatorname{sgn}_{C_2}$. If
$\zeta$ is either nontrivial character of $C_3$, then

$$
\operatorname{Ind}_{C_3}^{S_3}\zeta
=\operatorname{std},
\tag{6.3}
$$

because $\operatorname{std}|_{C_3}=\zeta\oplus\zeta^{-1}$.

Both $C_2$ and $C_3$ are elementary. The group $S_3$ is solvable, but it is not a
direct product of its Sylow subgroups and therefore is not elementary.

### 6.3 A negative-coefficient Brauer identity

Subtracting (6.3) from (6.2) gives

$$
\boxed{
1_{S_3}
=\operatorname{Ind}_{C_2}^{S_3}1
-\operatorname{Ind}_{C_3}^{S_3}\zeta.}
\tag{6.4}
$$

At the three conjugacy classes, the right side is

$$
(3,1,0)-(2,0,-1)=(1,1,1).
$$

The degree equation is

$$
1=[S_3:C_2]-[S_3:C_3]=3-2.
\tag{6.5}
$$

The negative sign is not an artifact of a poor choice. Section 5.7 shows that every
elementary-subgroup decomposition of $1_{S_3}$ must contain a negative coefficient.

Although $\zeta$ takes values in $\mathbf Q(\zeta_3)$, its induction is the
rational-valued standard character. This is the smallest example of coefficient
enlargement followed by cancellation. One must carry the cyclotomic coefficient
field while constructing the term, even though the final identity is rational.

### 6.4 What the dimension equation detects

The dimension equation detects a wrong subgroup index immediately. It does not
detect a wrong character. For example,

$$
\operatorname{Ind}_{C_2}^{S_3}\operatorname{sgn}_{C_2}
-\operatorname{Ind}_{C_3}^{S_3}\zeta
=\operatorname{sgn}
$$

also has degree one. Confusing it with (6.4) would pass the degree test and fail at
a transposition.

Every later Brauer identity therefore has three audits:

1. the subgroup indices give the correct total rank;
2. values on every conjugacy class give the character identity;
3. the characters are placed on the subgroups, not on their fixed-field quotients.

For a large group, Theorem 5.4 proves the second audit abstractly, but a computed
decomposition should still be checked by the character table or by restriction to a
class-function basis.

## 7. Galois closures and subgroup fixed fields

Brauer pairs become arithmetic only after subgroups are translated into fixed
fields. Since the correspondence reverses arrows, this translation is also where
the most damaging solvability mistake occurs: the solvable extension lies above a
fixed field, not generally below it.

### 7.1 The closure diagram

Let $K/F$ be a finite extension and let $M/F$ be its Galois closure. Put

$$
G=\operatorname{Gal}(M/F),
\qquad
J=\operatorname{Gal}(M/K).
$$

Then $K=M^J$. The field diagram is

~~~text
                         M
                        / \
          solvable only if  \  Galois over F
             J is solvable  \
                      K       F_H=M^H
                        \     /
                           F
~~~

The diagram records two different upper extensions. Automorphy over $K$ can be
carried to $M$ by the established solvable base-change theory only when $M/K$ lies
in its cyclic-tower range. The fact that $M/F$ is Galois does not imply this.

If a potential-automorphy theorem directly supplies a Galois $M/F$ with automorphy
over $M$, the problem disappears. If it supplies only $K$, passage to $M$ is a
separate hypothesis or theorem.

### 7.2 The direction-reversing dictionary

For every subgroup $H\le G$, put

$$
F_H=M^H.
$$

Then

$$
\operatorname{Gal}(M/F_H)=H,
\qquad
[F_H:F]=[G:H].
\tag{7.1}
$$

If $H_1\le H_2$, fixed fields reverse inclusion:

$$
M^{H_2}\subset M^{H_1}.
\tag{7.2}
$$

The extension $F_H/F$ is Galois exactly when $H$ is normal in $G$, in which case

$$
\operatorname{Gal}(F_H/F)\simeq G/H.
$$

When $H$ is not normal, the normal closure of $F_H/F$ inside $M$ has Galois group

$$
G/\operatorname{core}_G(H),
\qquad
\operatorname{core}_G(H)=\bigcap_{g\in G}gHg^{-1}.
\tag{7.3}
$$

This quotient can be nonsolvable even when $H$ is solvable. Thus the phrase
“the solvable fixed field $F_H/F$” is generally wrong. What is solvable is
$M/F_H$ when $H$ is solvable.

A character $\theta:H\to\mathbf C^\times$ becomes a finite-order character of
$G_{F_H}$ by

$$
G_{F_H}\twoheadrightarrow
\operatorname{Gal}(M/F_H)=H
\xrightarrow{\theta}\mathbf C^\times.
\tag{7.4}
$$

Class field theory turns (7.4) into a Hecke character of $F_H$. It is not a
character of $F$ unless it extends through $G$.

### 7.3 Solvable towers above fixed fields

Suppose $H$ is solvable. Choose a subnormal series

$$
H=H_0\triangleright H_1\triangleright\cdots
\triangleright H_r=1
$$

whose factors have prime order. Fixed fields reverse this series:

$$
F_H=M^{H_0}\subset M^{H_1}\subset\cdots
\subset M^{H_r}=M.
\tag{7.5}
$$

Every step is cyclic Galois, with

$$
\operatorname{Gal}(M^{H_{j+1}}/M^{H_j})
\simeq H_j/H_{j+1}.
\tag{7.6}
$$

Thus cyclic base change and descent can be iterated from $F_H$ to $M$. Intermediate
fields in a different cyclic tower need not be Galois over $F_H$, but the series
(7.5) obtained from normal subgroups of successive groups has exactly the
stepwise Galois property required.

For an elementary $H=C\times P$, solvability is explicit. Refine the cyclic factor
by its prime divisors and refine a central series of $P$ to order-$p$ factors.
No assertion about the solvability of $G$ is involved.

### 7.4 A nonsolvable total group is not a problem

Let $G$ be nonsolvable, for example $A_5$. Brauer induction never asks for solvable
base change along $M/F$. It chooses elementary subgroups $H_i\le G$ and uses the
solvable upper extensions

$$
M/M^{H_i}.
$$

The lower extensions $M^{H_i}/F$ can have nonsolvable normal closures. They are used
as separate base fields for automorphic representations and $L$-functions, not as
steps in one solvable tower from $F$.

This is the central field-theoretic point of the method:

~~~text
                         M
                /        |        \
        solvable          |          solvable
          /               |               \
       M^{H_1}          M^{H_2}          M^{H_3}
                \         |         /
                  no asserted solvable path
                           |
                           F
~~~

The auxiliary representations over the fields $M^{H_i}$ are combined virtually.
They are not descended independently through the lower arrows.

### 7.5 What does not survive passage to a Galois closure

Suppose potential automorphy over $K$ was proved while preserving a residual image
by the disjointness condition

$$
K\cap D=F
$$

for a finite Galois avoidance field $D/F$. The normal closure $M$ can satisfy

$$
M\cap D\ne F.
$$

Hence restriction from $G_K$ to $G_M$ can shrink the residual image, destroy
absolute irreducibility, or reveal a self-twist. The disjointness lemma must be
applied again to $M$.

Likewise, a local place split completely in $K$ may have controlled behavior in
$M$, but the full decomposition and inertia groups must be recomputed. Total reality
does survive: a normal closure generated by real conjugates is totally real. This
archimedean fact supplies no solvability or disjointness.

Finally, automorphy over $K$ does not automatically survive. If $M/K$ is not in the
established base-change range, there is no upward automorphic object to which
solvable descent from $M$ can later be applied.

### 7.6 The admissible top-field hypothesis

The later construction uses the following exact input.

An **admissible Galois automorphy field** for a representation
$\rho_{\lambda_0}$ over $F$ is a finite Galois extension $M/F$ such that:

1. $M$ has the required archimedean type, usually totally real;
2. $\rho_{\lambda_0}|_{G_M}$ is irreducible;
3. it is associated with a named regular algebraic cuspidal automorphic
   representation $\Pi_M$;
4. $\Pi_M$ supplies a compatible system over a fixed number field $E$ in the stated
   weak or strong local range;
5. the residual images and local conditions needed later have been rechecked over
   $M$; and
6. the conjugation action of $G$ on the top system and its coefficient field is
   recorded.

Book 170 supplies a finite totally real potential-automorphy field, but its basic
field theorem does not assert that the field is Galois or that automorphy persists
to its normal closure. Therefore the existence of an admissible Galois automorphy
field is a stronger variant or an additional input. All results below say explicitly
when they require it.

## 8. Artin formalism for local and global factors

A character identity affects an arithmetic $L$-function only through exact local
induction. This chapter follows that identity through Frobenius polynomials,
monodromy, conductors, archimedean parameters, epsilon factors, and finally the
global Euler product.

### 8.1 Local Weil--Deligne factors

Let $K$ be a nonarchimedean local field with residue cardinality $q_K$. For a
Frobenius-semisimple Weil--Deligne representation $D=(r,N)$ over a
characteristic-zero field, define

$$
L_K(s,D)=
\det\left(
1-q_K^{-s}r(\operatorname{Frob}_K)
\mid(\ker N)^{I_K}
\right)^{-1}.
\tag{8.1}
$$

The degree of this polynomial can be smaller than $\dim D$. A Steinberg parameter
with unramified twist has a one-dimensional space $(\ker N)^{I_K}$, while an
unramified two-character parameter has a two-dimensional invariant space. Keeping
$N$ is therefore essential.

For virtual parameters, local factors are multiplicative:

$$
L_K(s,[D_1]-[D_2])
=\frac{L_K(s,D_1)}{L_K(s,D_2)}.
\tag{8.2}
$$

This is a definition on the Grothendieck group. The quotient need not be the local
factor of an actual representation. Its reciprocal is a rational function in
$q_K^{-s}$, not necessarily a polynomial with constant term one.

Let $L/K$ be finite. Local induction satisfies

$$
L_K\left(s,\operatorname{Ind}_{W_L}^{W_K}D\right)
=L_L(s,D).
\tag{8.3}
$$

A proof can be read from Frobenius orbits. Induction decomposes into the cosets of
$W_L$ in $W_K$; inertia invariants and $\ker N$ break into orbits indexed by the
embeddings of residue fields. On each orbit, the $f$-th power of arithmetic
Frobenius is the arithmetic Frobenius of $L$. The determinant of the companion
block is the determinant appearing on the right. The same argument applies when
$N\ne0$ because induction carries $N$ on every coset and $\ker N$ is induced
accordingly.

### 8.2 The unramified induction polynomial

Let $E/F$ be a finite extension of number fields, let $v$ be unramified in $E$, and
let $w\mid v$. Suppose a rank-$n$ representation over $E$ is unramified at every
$w$ and write

$$
A_w=\rho(\operatorname{Frob}_w),
\qquad
f_w=f(w/v).
$$

Mackey decomposition gives

$$
\left.\operatorname{Ind}_{G_E}^{G_F}\rho\right|_{G_{F_v}}
\simeq
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{E_w}}^{G_{F_v}}\rho_w.
$$

Choose a coset basis around one Frobenius orbit. Arithmetic Frobenius cyclically
permutes $f_w$ copies, and its $f_w$-th power acts on the first copy by $A_w$.
Therefore

$$
\det\left(X-\operatorname{Frob}_v
\mid\operatorname{Ind}_{G_E}^{G_F}\rho\right)
=
\prod_{w\mid v}\det(X^{f_w}I_n-A_w).
\tag{8.4}
$$

This formula carries three audits.

First, the total degree is

$$
\sum_{w\mid v}nf_w=n[E:F]
$$

at an unramified place. Second, the exponent is the residue degree $f_w$, not the
ramification index or the global degree. Third, if $n=1$ and $v$ is inert quadratic,
the polynomial is

$$
X^2-\theta(\operatorname{Frob}_w),
$$

so the induced trace is zero.

For restriction rather than induction, if a polynomial over $F$ has roots
$\alpha_1,\ldots,\alpha_n$, then the polynomial at $w$ has roots
$\alpha_1^{f_w},\ldots,\alpha_n^{f_w}$. Confusing these two formulas reverses the
operation and usually changes the rank.

### 8.3 Conductors and discriminants

The Artin conductor depends on inertia breaks and monodromy. It is additive in
direct sums and hence extends to a signed integer on the Grothendieck group.

For a local extension $L/K$ and a rank-$n$ representation $D$ of $W_L$, induction
has the conductor-ideal formula

$$
\mathfrak f_K(\operatorname{Ind}_{W_L}^{W_K}D)
=
\mathfrak D_{L/K}^{\,n}
N_{L/K}\bigl(\mathfrak f_L(D)\bigr).
\tag{8.5}
$$

Here $\mathfrak D_{L/K}$ denotes the relative discriminant ideal on the $K$ side.
If $d_{L/K}=v_K(\mathfrak D_{L/K})$ and
$a_L(D)$ is the exponent of the prime of $L$, then

$$
a_K(\operatorname{Ind}D)
=nd_{L/K}+f(L/K)a_L(D).
\tag{8.6}
$$

Formula (8.6) uses the local residue degree in the norm of the conductor. Writing
$[L:K]a_L(D)$ would be wrong in a ramified extension.

Globally,

$$
\mathfrak f_F(\operatorname{Ind}_{G_E}^{G_F}\rho)
=
\mathfrak D_{E/F}^{\,n}
N_{E/F}\bigl(\mathfrak f_E(\rho)\bigr).
\tag{8.7}
$$

For a virtual difference, (8.7) becomes a quotient of ideals or a signed divisor
until effectivity is known. If the virtual class equals an actual representation,
the signed exponents necessarily combine to the nonnegative conductor exponents of
that representation. Positivity of the final exponent is a consequence of
effectivity, not a termwise property of the Brauer formula.

### 8.4 Archimedean and epsilon factors

At an archimedean place, local factors are defined from representations of
$W_\mathbf R$ or $W_\mathbf C$. With

$$
\Gamma_\mathbf R(s)=\pi^{-s/2}\Gamma(s/2),
\qquad
\Gamma_\mathbf C(s)=2(2\pi)^{-s}\Gamma(s),
$$

a character of $W_\mathbf C=\mathbf C^\times$ contributes a shifted
$\Gamma_\mathbf C$, while a one-dimensional or induced two-dimensional parameter
of $W_\mathbf R$ contributes the corresponding $\Gamma_\mathbf R$ factors. The
precise shifts are determined by the algebraic or unitary normalization chosen at
the start.

Induction is compatible with these factors:

$$
L_K(s,\operatorname{Ind}_{W_L}^{W_K}D)=L_L(s,D)
\tag{8.8}
$$

for $K=\mathbf R$ and $L=\mathbf C$ as well. Thus the archimedean factors in a
Brauer identity must be included; an equality only of finite Euler products is not
yet an equality of completed functions.

Local epsilon factors obey the induction formula

$$
\varepsilon_K(s,\operatorname{Ind}_{W_L}^{W_K}D,\psi_K)
=
\lambda(L/K,\psi_K)^{\dim D}
\varepsilon_L(s,D,\psi_K\circ\operatorname{Tr}_{L/K}),
\tag{8.9}
$$

where $\lambda(L/K,\psi_K)$ is the factor attached to
$\operatorname{Ind}_{W_L}^{W_K}1$. For the canonical global additive character, the
product of the local lambda factors satisfies the global compatibility needed for
Artin formalism. Suppressing the local lambda factor and then multiplying arbitrary
local formulas can give the wrong root number.

### 8.5 Global induction

Let $E/F$ be finite and let $\rho$ be a finite-dimensional representation of
$G_E$, unramified outside finitely many places. Multiplying (8.3) over all places,
including the archimedean ones, gives

$$
L_F\left(s,\operatorname{Ind}_{G_E}^{G_F}\rho\right)
=L_E(s,\rho).
\tag{8.10}
$$

In a right half-plane this is an identity of absolutely convergent Euler products.
If one side has a meromorphic continuation, (8.10) transports it to the other. For
completed functions, the conductor, gamma factors, and epsilon factors match through
(8.7)--(8.9).

Now let $M/F$ be finite Galois with group $G$, let $H\le G$, and let
$F_H=M^H$. A character $\theta$ of $H$ is inflated to $G_{F_H}$ through
$\operatorname{Gal}(M/F_H)$. If $\rho$ is a representation of $G_F$, the projection
formula gives

$$
\rho\otimes\operatorname{Ind}_{G_{F_H}}^{G_F}\theta
\simeq
\operatorname{Ind}_{G_{F_H}}^{G_F}
(\rho|_{G_{F_H}}\otimes\theta).
\tag{8.11}
$$

Consequently,

$$
L_F\left(
s,\rho\otimes\operatorname{Ind}_{H}^{G}\theta
\right)
=
L_{F_H}(s,\rho|_{G_{F_H}}\otimes\theta).
\tag{8.12}
$$

Equation (8.12) is the exact bridge from a finite-group character identity to
$L$-functions over subgroup fixed fields.

### 8.6 Virtual quotients

Apply (8.12) to the Brauer identity

$$
1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i.
$$

For every representation $\rho$ of $G_F$,

$$
\boxed{
L_F(s,\rho)=
\prod_i
L_{F_i}\left(
s,\rho|_{G_{F_i}}\otimes\theta_i
\right)^{n_i},}
\qquad
F_i=M^{H_i}.
\tag{8.13}
$$

The identity first holds in a common half-plane of absolute convergence. It includes
all local factors if the full local representations are used. Under only weak
compatibility, the safe assertion is equality outside the union of the finite bad
sets.

Negative $n_i$ make (8.13) a quotient. There is no ambiguity of fractional powers
because Brauer's coefficients are integers. There can still be poles from zeros of
denominator factors. The equality of Euler products in a right half-plane does not
prove that those poles cancel after continuation.

## 9. Compatible systems and Brauer operations

Repeating the Brauer construction at every coefficient prime introduces a new
problem: a compatible signed family need not be an actual family. The local
formulas remain exact, but effectivity and coefficient descent must be supplied
separately.

### 9.1 Restriction and induction of systems

Let

$$
\mathcal R_E=\{\rho_{E,\lambda}:G_E\to
\operatorname{GL}_n(E_\lambda)\}_\lambda
$$

be a weakly compatible system over a number field $E$; to avoid overloading notation,
write $Q$ for its coefficient field in this chapter. Restriction to a finite
extension $L/E$ preserves rank and weak compatibility. At an unramified place the
roots are raised to the residue degree. Strong local parameters restrict by

$$
(r_w,N_w)=
(r_v|_{W_{L_w}},N_v).
\tag{9.1}
$$

The operator $N_v$ is unchanged, while finite inertia can shrink.

Induction from $L$ to $E$ produces a system of rank $n[L:E]$. Its good polynomials
are given by (8.4), and its strong local parameter is

$$
D_v^{\operatorname{Ind}}
=
\bigoplus_{w\mid v}
\operatorname{Ind}_{W_{L_w}}^{W_{E_v}}D_w.
\tag{9.2}
$$

The determinant is

$$
\det\operatorname{Ind}_{G_L}^{G_E}V
=
\Delta_{L/E}^{\,n}
\bigl((\det V)\circ\operatorname{Ver}_{L/E}\bigr),
\tag{9.3}
$$

where $\Delta_{L/E}$ is the determinant of the permutation representation on
$G_E/G_L$. The factor $\Delta_{L/E}^{\,n}$ is present even when $V$ has trivial
determinant.

Restriction and induction preserve purity of weight $m$. For induction, the roots
over a Frobenius orbit are $f$-th roots of a number of complex size
$q_w^{m/2}=q_v^{fm/2}$, so each has size $q_v^{m/2}$. This statement concerns an
actual induced system. A signed virtual sum has no positivity statement until it is
effective.

### 9.2 Coefficient fields and roots of unity

Fix a Brauer decomposition with characters $\theta_i$. Let $Q_{\mathrm{top}}$ be the
coefficient field of the top automorphic system. Choose one number field $Q$
containing

$$
Q_{\mathrm{top}},
\qquad
\{\theta_i(h):i,\ h\in H_i\},
$$

and the fields of definition of every auxiliary automorphic representation and
local type. All systems are extended to $Q$ before they are added or subtracted.

This common enlargement is indispensable. Two representations over unrelated
completions cannot be combined in one Grothendieck group. After enlargement, a
finite place $\lambda$ of $Q$ selects compatible embeddings of every smaller
coefficient field into $Q_\lambda$.

Coefficient automorphisms act on the Brauer terms:

$$
\sigma\left(
\operatorname{Ind}_{H_i}^G\theta_i
\right)
=
\operatorname{Ind}_{H_i}^G\theta_i^\sigma.
\tag{9.4}
$$

The sum in (5.13) is fixed even if individual terms are not. If one wants a system
over a subfield $Q_0$, the common Frobenius polynomials must lie in $Q_0$ and the
coefficient descent cocycle must vanish. Galois invariance of traces alone does not
split a Schur index.

### 9.3 The virtual Brauer system

Suppose that for every term of a Brauer decomposition there is a compatible system

$$
\mathcal R_i=
\{\rho_{i,\lambda}:G_{F_i}\to
\operatorname{GL}_n(Q_\lambda)\}_\lambda
$$

and let $\theta_{i,\lambda}$ be the $\lambda$-adic avatar of $\theta_i$. Define

$$
\mathcal V_\lambda
=
\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_F}
(\rho_{i,\lambda}\otimes\theta_{i,\lambda})
\right]
\tag{9.5}
$$

in the Grothendieck group of continuous semisimple $Q_\lambda$-representations of
$G_F$.

The ranks in (9.5) give

$$
\operatorname{rank}\mathcal V_\lambda
=
n\sum_i n_i[G:H_i]=n.
\tag{9.6}
$$

Each induced term is a compatible system by Section 9.1. Addition and subtraction
of their characteristic-polynomial roots produce a **virtual compatible system**:
its trace functions and local Euler factors are compatible, and its total rank is
$n$. The adjective “virtual” cannot be dropped from this conclusion.

Suppose, more specifically, that every $\rho_{i,\lambda}$ restricts to the same
$G$-invariant top member $R_\lambda$ over $M$. Mackey restriction gives

$$
\operatorname{Res}_{G_M}^{G_F}
\operatorname{Ind}_{G_{F_i}}^{G_F}
(\rho_{i,\lambda}\otimes\theta_{i,\lambda})
\simeq
\bigoplus_{g\in G/H_i}{}^gR_\lambda.
$$

The Brauer character is trivial on $G_M$, and every conjugate is isomorphic to
$R_\lambda$. Hence

$$
\operatorname{Res}_{G_M}^{G_F}\mathcal V_\lambda=[R_\lambda]
$$

in the Grothendieck group. Even this stronger identity does not prove effectivity.
If $W$ is one extension of $R_\lambda$ and $\eta$ is a nontrivial character of
$G_F/G_M$, then

$$
2[W]-[W\otimes\eta]
$$

has rank $n$ and also restricts to $[R_\lambda]$, but it is not effective when
$W\not\simeq W\otimes\eta$. Restriction forgets precisely the quotient-character
direction in which descent choices vary.

At a good finite place $v$, the trace of $\mathcal V_\lambda(\operatorname{Frob}_v)$
is the signed sum of the traces computed from (8.4). These traces are images of one
algebraic number in $Q$. Determinants of virtual objects are more delicate:
the multiplicative determinant on $K_0$ gives a genuine one-dimensional character
by inverting the determinant characters of negative terms, but it does not by
itself give the degree-$n$ characteristic polynomial of an actual representation.

### 9.4 Projection back to the base

Assume for the moment that an actual compatible system

$$
\mathcal R_F=\{\rho_{F,\lambda}\}_\lambda
$$

already exists over $F$, and take

$$
\rho_{i,\lambda}
=\rho_{F,\lambda}|_{G_{F_i}}.
$$

Tensoring the Brauer identity with $\rho_{F,\lambda}$ gives

$$
[\rho_{F,\lambda}]
=
\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_F}
(\rho_{F,\lambda}|_{G_{F_i}}\otimes\theta_{i,\lambda})
\right].
\tag{9.7}
$$

Thus the virtual expression is exactly the class of the actual member. Formula
(9.7) proves independence of the chosen Brauer decomposition after the descended
system is known.

The logical direction matters. One cannot reverse the sentence and infer that
(9.5) is actual merely because (9.7) would hold if an extension existed. The
projection formula recognizes an existing descent; it does not create one.

### 9.5 Local compatibility of the virtual identity

At a finite place $v$, Mackey theory decomposes every induced term in (9.5) over the
places of $F_i$ above $v$. If the systems are strongly compatible there, the local
virtual parameter is

$$
\mathcal D_v^{\mathrm{virt}}
=
\sum_i n_i
\bigoplus_{w\mid v}
\operatorname{Ind}_{W_{(F_i)_w}}^{W_{F_v}}
(D_{i,w}\otimes\theta_{i,w}).
\tag{9.8}
$$

Its local factor, epsilon factor, and signed conductor are the corresponding
products and sums. If (9.5) is known to be an actual representation, (9.8) is its
Frobenius-semisimple parameter in the proved local range.

At coefficient-prime places, no Weil--Deligne induction formula replaces the
filtered local category automatically. Hodge--Tate weights of an actual induced
representation are obtained by inducing embeddings: every label of $F_i$ above a
label of $F$ contributes its weights. A virtual difference gives a signed Hodge
multiset, which is not a Hodge structure unless effectivity is established.

### 9.6 The effectivity boundary

There are three reliable ways to cross from (9.5) to an actual system.

The first is a coherent descent datum on the top compatible system. It constructs
each $\rho_{F,\lambda}$ directly, after which (9.7) identifies the Brauer expression.

The second is a continuous determinant, or pseudorepresentation, of dimension $n$
whose trace and characteristic polynomials are those of (9.5). Over a
characteristic-zero local field, such a determinant is represented by a unique
semisimple representation after scalar extension. The determinant identities,
continuity, and dimension are additional assertions; a virtual trace does not
automatically satisfy them.

The third is an independent geometric or automorphic construction over $F$ whose
good Frobenius polynomials agree with the virtual ones. Chebotarev then identifies
its semisimplification with the desired class.

The following implications are invalid:

$$
\operatorname{rank}\mathcal V_\lambda=n>0
\quad\Longrightarrow\quad
\mathcal V_\lambda\text{ is effective},
$$

and

$$
\mathcal V_{\lambda_0}\text{ is effective for one }\lambda_0
\quad\Longrightarrow\quad
\mathcal V_\lambda\text{ is effective for every }\lambda.
$$

The second statement needs a uniform descent or determinant theorem. Compatible
good traces do not compare irreducible multiplicities in representation categories
over different residue characteristics.

## 10. The automorphic operations

Automorphic base change and induction mirror restriction and induction of
parameters only within established functorial ranges. The mirror is powerful but
not unlimited, so rank changes, cuspidality, twists, and central characters must be
tracked at every use.

### 10.1 Automorphic induction of Hecke characters

Let $L/K$ be quadratic and let $\psi$ be an algebraic Hecke character of $L$.
Automorphic induction gives

$$
\operatorname{AI}_{L/K}(\psi)
$$

on $\operatorname{GL}_2(\mathbf A_K)$ with local parameter

$$
\operatorname{Ind}_{W_{L_w}}^{W_{K_v}}\psi_w
$$

at every place. Its compatible Galois system is

$$
\operatorname{Ind}_{G_L}^{G_K}\psi_\lambda.
\tag{10.1}
$$

The representation is cuspidal exactly when

$$
\psi\ne\psi^\sigma,
\tag{10.2}
$$

where $\sigma$ is the nontrivial automorphism of $L/K$. If $\psi=\mu\circ N_{L/K}$,
then

$$
\operatorname{AI}_{L/K}(\psi)
=
\mu\boxplus\mu\eta_{L/K}.
\tag{10.3}
$$

Thus automorphic induction always produces an automorphic isobaric object, but it
does not always produce a cusp form.

The central character is

$$
\omega_{\operatorname{AI}_{L/K}(\psi)}
=
\eta_{L/K}\,\psi|_{C_K}.
\tag{10.4}
$$

On the Galois side this is

$$
\det\operatorname{Ind}_{G_L}^{G_K}\psi_\lambda
=
\eta_{L/K,\lambda}
(\psi_\lambda\circ\operatorname{Ver}_{L/K}).
\tag{10.5}
$$

The quadratic factor is the determinant of the permutation action on two cosets.

### 10.2 Cyclic induction of characters and conditional iteration

If $L/K$ is cyclic of degree $d$, automorphic induction of a Hecke character lies on
$\operatorname{GL}_d(\mathbf A_K)$. It is cuspidal exactly when the orbit of the
character under $\operatorname{Gal}(L/K)$ has size $d$. A nontrivial stabilizer
gives an isobaric decomposition determined by the smaller orbit.

If $L/K$ merely admits a cyclic tower, the character theorem just stated does not
by itself construct automorphic induction through the whole tower. After the first
step, the object being induced generally has rank greater than one. Books 95 and 97
do not supply that higher-rank induction: Book 95 supplies cyclic induction from
$\operatorname{GL}_1$, while Book 97 supplies solvable base change for
$\operatorname{GL}_2$. If a separate cyclic automorphic-induction theorem is
available for every intermediate rank, then it may be iterated, and transitivity
reads

$$
\operatorname{AI}_{L/K}(\psi)
\simeq
\operatorname{AI}_{M/K}
\left(\operatorname{AI}_{L/M}(\psi)\right)
\tag{10.6}
$$

whenever each operation in the formula is available in the required rank. The
intermediate object in (10.6) need not remain cuspidal.

Automorphic induction changes rank. Inducing a rank-two compatible system from a
quadratic extension gives rank four. The character theorem (10.1) does not provide
automorphic induction of a $\operatorname{GL}_2$ representation to
$\operatorname{GL}_4$ unless a separate higher-rank theorem is assumed.

### 10.3 Cyclic and solvable base change

Let $L/K$ admit a cyclic tower and let $\pi$ be cuspidal on
$\operatorname{GL}_2(\mathbf A_K)$. Solvable base change constructs an isobaric
representation

$$
\operatorname{BC}_{L/K}(\pi)
$$

whose local parameter is restriction:

$$
D(\operatorname{BC}_{L/K}(\pi)_w)
=
D(\pi_v)|_{W_{L_w}}.
\tag{10.7}
$$

It preserves rank. Its central character is

$$
\omega_{\operatorname{BC}_{L/K}(\pi)}
=
\omega_\pi\circ N_{L/K}.
\tag{10.8}
$$

At an unramified place, a Satake pair $\{\alpha_v,\beta_v\}$ becomes

$$
\{\alpha_v^{f(w/v)},\beta_v^{f(w/v)}\}.
\tag{10.9}
$$

The exponent in (10.9) is the residue degree. At a ramified place one restricts the
full Weil--Deligne parameter; extending the conductor ideal mechanically is not a
local base-change formula.

A solvable Galois extension has a prime cyclic tower, but the numerical degree of a
finite extension says nothing comparable about its Galois closure. A non-Galois
extension lies in this base-change range only when an actual cyclic tower has been
supplied.

### 10.4 Transitivity, twists, and Mackey compatibility

Base change is transitive because restriction of local parameters is transitive.
Automorphic induction is transitive because induction of Weil representations is
transitive. The twist formulas are

$$
\operatorname{BC}_{L/K}(\pi\otimes\mu)
=
\operatorname{BC}_{L/K}(\pi)
\otimes(\mu\circ N_{L/K}),
\tag{10.10}
$$

and

$$
\operatorname{AI}_{L/K}
\bigl(\psi(\mu\circ N_{L/K})\bigr)
=
\operatorname{AI}_{L/K}(\psi)\otimes\mu.
\tag{10.11}
$$

For a quadratic $M/K$ and a further extension $L/K$, Mackey theory computes

$$
\operatorname{BC}_{L/K}\operatorname{AI}_{M/K}(\psi).
\tag{10.12}
$$

If $M\subset L$, the result is the two-character sum obtained by restricting to
$M$. If $M$ and $L$ are disjoint in the required sense, it is automorphic induction
from $ML/L$ of the norm-pulled character. If the tensor product $M\otimes_KL$
splits, the formula is interpreted componentwise. There is no single symbolic
interchange rule that ignores these cases.

### 10.5 Central characters and conductors

For cyclic induction of a character,

$$
\omega_{\operatorname{AI}_{L/K}(\psi)}
=
\delta_{L/K}\,\psi|_{C_K},
\tag{10.13}
$$

where $\delta_{L/K}$ is the determinant of the coset permutation representation.
For a general rank-$n$ Galois representation, the determinant formula is (9.3), so
the permutation factor occurs to the $n$-th power.

The conductor formula for character induction is

$$
\mathfrak f\bigl(\operatorname{AI}_{L/K}(\psi)\bigr)
=
\mathfrak D_{L/K}\,
N_{L/K}\bigl(\mathfrak f(\psi)\bigr).
\tag{10.14}
$$

For rank $n$, the discriminant exponent becomes $n$ as in (8.7). Twisting by a
character can lower a conductor when two ramified characters cancel; conductor
exponents are not simply additive under tensor product.

A rank-two twist changes the central character by a square:

$$
\omega_{\pi\otimes\mu}=\omega_\pi\mu^2.
\tag{10.15}
$$

Consequently a prescribed central character selects a square class inside a descent
fiber. It does not select a unique descent and does not prove that a descent exists.

### 10.6 The cuspidal boundary

At one cyclic step, a cuspidal $\operatorname{GL}_2$ representation loses
cuspidality exactly when it has a nontrivial self-twist by a character killed by
base change. Such a self-twist is quadratic. The source is automorphically induced
from the corresponding quadratic extension, and its base change becomes a sum of
two characters.

In a solvable tower the test is stepwise. The first failure occurs at a quadratic
layer, but the relevant quadratic character can live over an intermediate field.
Absence of a bottom-field quadratic self-twist is not a complete criterion for a
noncyclic tower.

Once a representation becomes isobaric, later base change remains isobaric. It
cannot recover cuspidality. Any construction using an irreducible top Galois
representation must therefore verify that no first bad step occurs.

## 11. Auxiliary automorphic representations over fixed fields

The elementary subgroups from Brauer's theorem give solvable upper extensions on
which the top automorphic representation can be descended. The resulting objects
live over several fixed fields; their Galois inductions can be combined over the
base even when no corresponding automorphic induction is known there.

### 11.1 The top automorphic input

Let $\rho_{\lambda_0}$ be a rank-two representation of $G_F$, and let $M/F$ be an
admissible Galois automorphy field with group $G$. Thus

$$
\rho_{\lambda_0}|_{G_M}
\simeq
\rho_{\Pi_M,\lambda_0}
\tag{11.1}
$$

for a regular algebraic cuspidal representation $\Pi_M$ of
$\operatorname{GL}_2(\mathbf A_M)$, after a stated common coefficient extension.
Assume this restricted representation is irreducible.

For $g\in G$, the two representations

$$
\rho_{\lambda_0}|_{G_M}
\quad\text{and}\quad
{}^g(\rho_{\lambda_0}|_{G_M})
$$

are isomorphic because both are restrictions of $\rho_{\lambda_0}$. Their good
Frobenius polynomials are therefore equal. Strong multiplicity one gives

$$
\Pi_M^g\simeq\Pi_M.
\tag{11.2}
$$

Equation (11.2) proves invariance of the automorphic isomorphism class. The
restriction of $\rho_{\lambda_0}$ supplies more: it gives coherent extension data at
the distinguished coefficient place. This extra datum will select the correct
cyclic descents.

Let

$$
1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i
\tag{11.3}
$$

be a fixed Brauer decomposition, and put $F_i=M^{H_i}$. Each $H_i$ is elementary
and hence solvable.

### 11.2 Solvable descent to $M^H$

Fix one elementary subgroup $H$. The extension

$$
M/F_H
$$

is solvable Galois with group $H$. Choose a prime cyclic series as in (7.5). At the
top, $\Pi_M$ is invariant under the first cyclic group. Cyclic automorphic descent
gives a nonempty finite fiber of cusp forms one field lower.

For the arithmetic selection made below, assume at every layer that the candidate
regular algebraic descents lie in the range of the attached-representation theorem,
and that attachment is compatible with cyclic base change and finite-order twists.
This is the same extra compatibility required in the solvable descent theorem of
Book 97; cyclic automorphic descent alone does not manufacture it.

An arbitrary member of that fiber need not be invariant at the next stage. The
representation

$$
\rho_{\lambda_0}|_{G_{F_H}}
$$

selects the correct member. At one cyclic step, any two irreducible extensions of
the same irreducible top restriction differ by a character of the cyclic quotient.
Twist the arbitrary automorphic descent by the inverse of that character. Its
Galois representation now equals the restriction of $\rho_{\lambda_0}$ to the
lower field. It is consequently invariant at the next step. Repeating gives a
cuspidal automorphic representation $\Pi_H$ over $F_H$ such that

$$
\operatorname{BC}_{M/F_H}(\Pi_H)\simeq\Pi_M
\tag{11.4}
$$

and

$$
\rho_{\Pi_H,\lambda_0}^{\mathrm{ss}}
\simeq
\rho_{\lambda_0}|_{G_{F_H}}.
\tag{11.5}
$$

Irreducibility of the restriction to $G_M$ keeps the cyclic descent in the
cuspidal, scalar-endomorphism range. If that restriction were reducible, the
extension comparison could involve a two-character multiset rather than one
quotient character.

The construction uses solvable descent only along $M/F_H$. It makes no base-change
or descent assertion along $F_H/F$.

### 11.3 Twisting by the Brauer character

Inflate $\theta:H\to\mathbf C^\times$ to $G_{F_H}$ as in (7.4), and let the same
symbol denote the corresponding finite-order Hecke character of $F_H$. Define

$$
\Pi_{H,\theta}=\Pi_H\otimes\theta.
\tag{11.6}
$$

Its distinguished Galois member is

$$
\rho_{\Pi_{H,\theta},\lambda_0}
\simeq
\rho_{\lambda_0}|_{G_{F_H}}\otimes\theta_{\lambda_0}.
\tag{11.7}
$$

The central character changes by

$$
\omega_{\Pi_{H,\theta}}
=
\omega_{\Pi_H}\theta^2.
\tag{11.8}
$$

The twist leaves algebraic weights and purity unchanged, but it can change the
finite conductor and inertial type. Those changes must be computed from the full
local characters; a finite-order twist need not be unramified.

If $\Pi_H$ lies in the curve-realizable range of Books 135 and 175, or if a separate
Galois-representation theorem applies to this precise weight and local profile, then
after enlarging one coefficient field to contain the Hecke field and the values of
$\theta$, the representation $\Pi_{H,\theta}$ supplies a compatible system

$$
\mathcal R(\Pi_{H,\theta})
=
\{\rho_{\Pi_{H,\theta},\lambda}\}_\lambda.
\tag{11.9}
$$

Coefficient conjugation sends this system to the one attached to
$\Pi_H^\sigma\otimes\theta^\sigma$.

Solvable automorphic descent by itself does not prove this curve-realization or
Galois-representation hypothesis. Without it, $\Pi_{H,\theta}$ still supplies the
automorphic $L$-function used in Chapter 14, but it supplies no auxiliary compatible
system for (9.5). This distinction is part of the input to Theorems 13.1 and 18.2.

### 11.4 Galois induction versus automorphic induction

The Galois representation

$$
\operatorname{Ind}_{G_{F_H}}^{G_F}
\rho_{\Pi_{H,\theta},\lambda}
\tag{11.10}
$$

always exists and has rank $2[G:H]$. It forms a compatible system and satisfies
Artin formalism.

An automorphic representation over $F$ corresponding to (11.10) is a different
matter. It would require automorphic induction of a $\operatorname{GL}_2$ object
from $F_H$ to $F$, generally to $\operatorname{GL}_{2[G:H]}$. The extension
$F_H/F$ may be non-Galois and may have a nonsolvable normal closure. The
automorphic-induction results for Hecke characters and the solvable base-change
results for $\operatorname{GL}_2$ do not provide this higher-rank object.

Thus the phrase “induce the auxiliary automorphic representation back to $F$” has
two meanings:

- its Galois system can always be induced, producing (11.10);
- an automorphic induction exists only under a separate theorem covering the rank
  and field extension in question.

The Brauer $L$-function argument needs only the first meaning, because (8.10)
expresses the induced $L$-function as the standard automorphic $L$-function over
$F_H$.

### 11.5 The Brauer $L$-function identity

Apply (8.13) to (11.3). In the half-plane of absolute convergence,

$$
L_F(s,\rho_{\lambda_0})
=
\prod_i
L_{F_i}\left(
s,\rho_{\lambda_0}|_{G_{F_i}}\otimes\theta_i
\right)^{n_i}.
\tag{11.11}
$$

By (11.7) and local--global compatibility in the established range,

$$
L_F(s,\rho_{\lambda_0})
=
\prod_i
L\left(s,\Pi_{H_i}\otimes\theta_i\right)^{n_i}.
\tag{11.12}
$$

The same formula holds for completed functions after the conductor, archimedean,
and epsilon normalizations are aligned. Every factor on the right is automorphic
over its own field $F_i$. No automorphic representation over $F$ has been produced.

If some $\Pi_{H_i}\otimes\theta_i$ is noncuspidal in a reducible variant, its
standard $L$-function is the product of the factors of its isobaric constituents.
A trivial Hecke-character constituent can contribute a pole. The formula remains a
meromorphic identity; the analytic conclusion becomes weaker, not false.

### 11.6 The $S_3$ field diagram

Let $M/F$ be Galois with group $S_3$. Use the identity (6.4):

$$
1_{S_3}
=
\operatorname{Ind}_{C_2}^{S_3}1
-
\operatorname{Ind}_{C_3}^{S_3}\zeta.
$$

Put

$$
L_3=M^{C_2},
\qquad
L_2=M^{C_3}.
$$

Then

$$
[L_3:F]=3,
\qquad
[L_2:F]=2.
$$

The field $L_3/F$ is generally non-Galois, while $L_2/F$ is quadratic Galois. The
upper extensions are

$$
[M:L_3]=2,
\qquad
[M:L_2]=3,
$$

and both are cyclic. The Brauer formula is

$$
L_F(s,\rho)
=
\frac{
L_{L_3}(s,\rho|_{G_{L_3}})
}{
L_{L_2}(s,\rho|_{G_{L_2}}\otimes\zeta)
}.
\tag{11.13}
$$

The dimension audit is

$$
2=3\cdot2-2\cdot2.
$$

Formula (11.13) is a quotient even though $S_3$ itself is solvable. One could use
solvable descent directly along $M/F$ when all coherence hypotheses hold, but the
Brauer identity deliberately illustrates what survives without replacing the
quotient by an actual bottom automorphic form.

## 12. Descent data, cocycles, and self-twists

An invariant isomorphism class is only the visible part of descent. Actual descent
requires coherent intertwiners, and their failures are measured by factor sets,
character torsors, and self-twist stabilizers.

### 12.1 Invariance is only the first condition

Let $M/F$ be Galois with group $G$, and let $\Pi_M$ be an irreducible automorphic
representation over $M$. A necessary condition for descent is

$$
\Pi_M^g\simeq\Pi_M
\qquad(g\in G).
\tag{12.1}
$$

This is a statement about isomorphism classes. A descent datum requires actual
isomorphisms

$$
I_g:\Pi_M^g\longrightarrow\Pi_M
\tag{12.2}
$$

that compose coherently. When $\Pi_M$ is cuspidal, its equivariant endomorphisms are
scalars, so any two choices of $I_g$ differ by a scalar. Scalar ambiguity makes the
obstruction computable; it does not make it vanish.

There is a second, weaker symmetry that must not be confused with (12.1):

$$
\Pi_M^g\simeq\Pi_M\otimes\chi_g.
\tag{12.3}
$$

Here conjugation invariance holds only up to a Hecke-character twist. The characters
$\chi_g$ must themselves satisfy a cocycle law modulo the self-twist group before
one can correct them. An inner-twist orbit is not a descent datum.

### 12.2 The scalar $H^2$ obstruction

Choose isomorphisms (12.2). Their failure to compose is a scalar:

$$
I_g\,{}^g I_h
=
a(g,h)I_{gh},
\qquad
a(g,h)\in k^\times,
\tag{12.4}
$$

where $k$ is an algebraically closed coefficient field. Associativity gives

$$
a(g,h)a(gh,r)
=
a(g,hr)a(h,r),
\tag{12.5}
$$

so $a$ is a $2$-cocycle. Replacing $I_g$ by $b(g)I_g$ changes $a$ by the coboundary

$$
a(g,h)\longmapsto
\frac{b(g)b(h)}{b(gh)}a(g,h).
$$

Thus

$$
[a]\in H^2(G,k^\times)
\tag{12.6}
$$

is independent of the chosen intertwiners. It vanishes exactly when the $I_g$ can
be rescaled to satisfy the cocycle condition.

For a supplied irreducible Weil or Galois parameter, this is the exact obstruction
to extending that parameter. It is not, by itself, an image criterion for an
automorphic isomorphism class under noncyclic base change. A generic automorphic
representation has Whittaker-normalized field intertwiners that can be made
coherent on its automorphic realization, but this does not construct a
representation over the lower field. The unconditional automorphic criterion in
the solvable range remains the recursive cyclic descent chain and its $H^1$ torsor
checks. Thus no class in (12.6) is to be attached to an automorphic isomorphism
class as its complete descent obstruction unless a compatible global parameter has
also been supplied.

For a Galois representation on $G_M$, one must include the factor from a section of
the group extension. Choose representatives $s(g)\in G_F$ and write

$$
s(g)s(h)=c(g,h)s(gh),
\qquad c(g,h)\in G_M.
\tag{12.7}
$$

If $R$ is the representation of $G_M$ and $A_g$ intertwines $R$ with its
$s(g)$-conjugate, an extension to $G_F$ requires

$$
A_gA_h=R(c(g,h))A_{gh}.
\tag{12.8}
$$

Arbitrary intertwiners satisfy (12.8) only up to a scalar cocycle. This is the exact
extension obstruction.

An actual representation already defined on $G_F$ supplies $A_g=\rho(s(g))$ and
makes (12.8) automatic. That is why a bottom arithmetic representation is such a
powerful source of coherent solvable descent.

### 12.3 The $H^1$ obstruction in a solvable tower

Consider two adjacent cyclic layers

$$
K\subset L\subset M
$$

and assume $M/K$ is Galois. Suppose a cuspidal representation over $M$ descends to
$L$. Its descents form a torsor $D$ under the character group

$$
X(M/L)=\widehat{C_L/N_{M/L}(C_M)}.
$$

Let $Q=\operatorname{Gal}(L/K)$ act on this torsor. Relative to a chosen descent
$d\in D$, write

$$
q(d)=c(q)\cdot d,
\qquad c(q)\in X(M/L).
\tag{12.9}
$$

The affine action law gives

$$
c(qr)=c(q)\,q(c(r)),
$$

so $c$ is a $1$-cocycle. A different origin changes $c$ by a coboundary. The torsor
has a $Q$-fixed member exactly when

$$
[c]=0\in H^1(Q,X(M/L)).
\tag{12.10}
$$

Only then can one choose a descent to $L$ that is invariant for the next cyclic
step.

A general subnormal tower need not make every two-layer composite Galois. In that
case there is no quotient action on one fixed torsor and no class (12.10) to write
down. The correct test is recursive: enumerate the cyclic descents and check which
are invariant at the next stage. Writing an $H^1$ group without a genuine action
does not create one.

### 12.4 Character ambiguity and self-twists

Suppose an irreducible representation $R$ of $G_M$ extends to $G_F$. If
$\widetilde R_1$ and $\widetilde R_2$ are two extensions, then

$$
\operatorname{Hom}_{G_M}(\widetilde R_1,\widetilde R_2)
$$

is one-dimensional. Conjugation by $G_F$ on this line gives a character of

$$
G_F/G_M\simeq G,
$$

and

$$
\widetilde R_2\simeq\widetilde R_1\otimes\eta.
\tag{12.11}
$$

Thus, when the top restriction is irreducible, extension classes form a torsor
under $\widehat{G^{\mathrm{ab}}}$. The action is free: a self-twist of an extension
would restrict to a scalar intertwiner of the irreducible top member and would force
the quotient character to be trivial. If the top restriction is reducible, this
argument fails and self-twists can identify different characters.

On the automorphic side, when $M/F$ is solvable and a cuspidal descent exists, its
fiber under solvable base change is controlled by

$$
X(M/F)=\widehat{C_F/N_{M/F}(C_M)}
\simeq\widehat{G^{\mathrm{ab}}}.
\tag{12.12}
$$

At an isobaric endpoint, the action can have a stabilizer

$$
S_M(\pi)=
\{\eta\in X(M/F):\pi\otimes\eta\simeq\pi\}.
\tag{12.13}
$$

The orbit then has size $|X(M/F)|/|S_M(\pi)|$, and the full extension fiber can
contain further reducible data. Calling every fiber a torsor silently assumes
cuspidality and scalar endomorphisms.

### 12.5 Central characters do not remove the obstruction

If two rank-two descents differ by $\eta$, their central characters differ by
$\eta^2$:

$$
\omega_{\pi\otimes\eta}
=\omega_\pi\eta^2.
\tag{12.14}
$$

Therefore a prescribed central character restricts the descent ambiguity to a
square class. If one descent has central character $\omega_0$, a desired
$\omega$ occurs exactly when

$$
\omega/\omega_0\in X(M/F)^2.
\tag{12.15}
$$

When it occurs, the remaining ambiguity is controlled by $X(M/F)[2]$ modulo any
self-twist stabilizer.

Equation (12.15) is not a descent existence theorem. An invariant central character
can coexist with a nonzero $H^1$ torsor obstruction or, for a supplied compatible
parameter, a nonzero $H^2$ extension obstruction. It records determinants of
possible descents, not coherent intertwiners or a recursive automorphic descent
chain.

### 12.6 A self-twisted dihedral representation

Let $L/F$ be quadratic with character $\eta=\eta_{L/F}$, and let
$\vartheta$ be an algebraic Hecke character of $L$. Write
$\theta_\ell:G_L\to\overline{\mathbf Q}_\ell^\times$ for its $\ell$-adic avatar,
and assume $\theta_\ell\ne\theta_\ell^\sigma$. Put

$$
r=\operatorname{Ind}_{G_L}^{G_F}\theta_\ell.
\tag{12.16}
$$

Then $r$ is irreducible and

$$
r\otimes\eta\simeq r.
\tag{12.17}
$$

Restriction exposes the two lines:

$$
r|_{G_L}\simeq\theta_\ell\oplus\theta_\ell^\sigma.
\tag{12.18}
$$

Automorphically,

$$
\pi=\operatorname{AI}_{L/F}(\vartheta)
$$

is cuspidal, while

$$
\operatorname{BC}_{L/F}(\pi)
=\vartheta\boxplus\vartheta^\sigma
\tag{12.19}
$$

is not.

Conjugation on (12.18) exchanges the two lines. In a suitable basis, a descent
intertwiner is a scalar multiple of

$$
A=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
$$

Rescaling $A$ changes its cocycle scalar. Once the cocycle is normalized, the two
quotient-character choices differ by $\eta$, but (12.17) identifies the resulting
representations. The self-twist stabilizer has collapsed the naive two-element
fiber.

This diagnostic shows four failures at once: base change can be noncuspidal,
scalar-endomorphism arguments fail for the top isobaric sum, the twist action need
not be free, and an invariant unordered constituent set is not the same as a
chosen coherent exchange map.

## 13. Constructing a system over the original field

The virtual Brauer system becomes an arithmetic object only after an effectivity
mechanism is supplied uniformly in the coefficient prime. This chapter gives two
such mechanisms and isolates the separate obstruction to descending the
coefficient field.

### 13.1 The descent datum to be constructed

Let $M/F$ be an admissible Galois automorphy field and let

$$
\mathcal R_M=
\{R_\lambda:G_M\to\operatorname{GL}_n(Q_\lambda)\}_\lambda
\tag{13.1}
$$

be the compatible system attached to the top automorphic representation. The goal
is to construct

$$
\mathcal R_F=
\{\rho_\lambda:G_F\to\operatorname{GL}_n(Q_\lambda)\}_\lambda
\tag{13.2}
$$

such that

$$
\rho_\lambda|_{G_M}\simeq R_\lambda
\tag{13.3}
$$

for every $\lambda$.

The following conditions are necessary before one invokes Brauer induction:

1. every $R_\lambda$ is invariant under $G=\operatorname{Gal}(M/F)$;
2. its extension obstruction vanishes;
3. one choice among the character-twist extensions is made compatibly in $\lambda$;
4. the resulting Frobenius polynomials lie in one number field before completion;
5. the local and coefficient descent data respect Galois conjugation.

Potential automorphy at one coefficient place proves none of conditions 2--5 for
the other places by itself.

### 13.2 The coherent-cocycle route

Choose a section $s:G\to G_F$ and the factor $c(g,h)$ of (12.7). Suppose that for
every $\lambda$ there are matrices $A_{g,\lambda}$ satisfying

$$
A_{g,\lambda}R_\lambda(x)A_{g,\lambda}^{-1}
=
R_\lambda(s(g)xs(g)^{-1})
\qquad(x\in G_M)
\tag{13.4}
$$

and

$$
A_{g,\lambda}A_{h,\lambda}
=
R_\lambda(c(g,h))A_{gh,\lambda}.
\tag{13.5}
$$

Define

$$
\rho_\lambda(xs(g))
=
R_\lambda(x)A_{g,\lambda}.
\tag{13.6}
$$

Every element of $G_F$ has a unique expression $xs(g)$, and
(13.4)--(13.5) prove that (13.6) is a homomorphism. Continuity follows because
$G_M$ is open and only finitely many coset matrices have been added.

To make the family compatible, the data $A_{g,\lambda}$ must arise from one
coefficient-rational descent datum. Concretely, after one finite enlargement of
$Q$, traces of every Frobenius-coset operator occurring in (13.6) must be the
$\lambda$-adic images of algebraic numbers and must commute with coefficient
conjugation. This requirement is automatic when the descent comes from an
algebraic geometric object over $F$ or from a bottom automorphic representation. It
is not automatic for independently chosen local intertwiners.

If the obstruction classes are known to be the scalar extensions of one algebraic

$$
o\in H^2(G,\overline{\mathbf Q}^{\,\times}),
\tag{13.7}
$$

then vanishing at one embedding implies $o=0$. Indeed, for finite $G$ the relevant
Schur-multiplier class is finite torsion and is represented by roots of unity; an
embedding cannot send a nontrivial root of unity to $1$. The premise that all local
classes come from the one class (13.7) is essential.

### 13.3 The determinant-effectivity route

Sometimes the Brauer construction is available before coherent intertwiners. For
each $\lambda$, form the virtual class $\mathcal V_\lambda$ of (9.5). Suppose one
can construct a continuous multiplicative polynomial law

$$
D_\lambda:Q_\lambda[[G_F]]\longrightarrow Q_\lambda
\tag{13.8}
$$

of degree $n$ such that

$$
D_\lambda(1-Xg)
=
1-t_\lambda(g)X+\cdots+(-1)^nd_\lambda(g)X^n,
\tag{13.9}
$$

where $t_\lambda$ is the virtual trace supplied by $\mathcal V_\lambda$, and such
that the coefficients at good Frobenius elements are images of common algebraic
numbers.

Over characteristic zero, a continuous degree-$n$ determinant is represented,
after finite scalar extension, by a unique semisimple representation

$$
\rho_\lambda:G_F\to\operatorname{GL}_n(\overline{Q_\lambda}).
\tag{13.10}
$$

This makes the virtual class effective at the level of semisimplification. If the
determinant is absolutely irreducible, its field of traces together with the
vanishing of the coefficient descent obstruction gives a model over the stated
completion.

The hypothesis (13.8) is stronger than knowing a trace and a rank. The trace of a
difference of representations need not satisfy the degree-$n$ determinant
identities. Verifying those polynomial identities is precisely the effectivity
work.

### 13.4 Common Frobenius polynomials

Assume the coherent route, and choose the auxiliary descents $\Pi_{H_i}$ so that
their compatible systems agree with $\rho_\lambda|_{G_{F_i}}$ for every $\lambda$.
Then the projection formula gives

$$
[\rho_\lambda]
=
\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_F}
(\rho_{\Pi_{H_i},\lambda}\otimes\theta_{i,\lambda})
\right].
\tag{13.11}
$$

At a good place, every trace on the right is algebraic and independent of
$\lambda$. Hence

$$
\operatorname{tr}\rho_\lambda(\operatorname{Frob}_v)
=\iota_\lambda(a_v)
\tag{13.12}
$$

for one $a_v\in Q$. Each auxiliary good polynomial also determines, uniformly in
$\lambda$, the power sums of its Frobenius roots. Applying the induction formula
to those power sums gives common values for
$\operatorname{tr}\rho_\lambda(\operatorname{Frob}_v^m)$ for $1\le m\le n$.
Newton's identities recover the elementary symmetric functions of the eigenvalues
and therefore a polynomial

$$
P_v(X)\in Q[X]
\tag{13.13}
$$

whose image in every $Q_\lambda[X]$ is

$$
\det(X-\rho_\lambda(\operatorname{Frob}_v)).
$$

The use of powers is essential in rank greater than two: trace and determinant
alone do not determine all coefficients. In rank two, $m=1,2$ or an independently
known determinant suffices.

Under the determinant route, common polynomials are part of (13.8)--(13.9).
Chebotarev then makes each semisimple member unique.

### 13.5 Coefficient descent and Galois conjugates

Let $Q/Q_0$ be finite Galois. Common polynomials in $Q_0[X]$ give isomorphisms

$$
{}^\sigma\rho_\lambda
\simeq
\rho_{\sigma\lambda}
\tag{13.14}
$$

after scalar extension, but they do not choose them coherently. For an absolutely
irreducible member, chosen intertwiners have a scalar factor set. After a finite
enlargement that defines the intertwiners, it may be written

$$
b(\sigma,\tau)\in Q^\times,
$$

whose class in

$$
H^2(\operatorname{Gal}(Q/Q_0),Q^\times)
\tag{13.15}
$$

is the coefficient descent obstruction; here the coefficient Galois group acts on
$Q^\times$ in the natural way, so this is the corresponding relative Brauer-group
class, not cohomology with a silently trivial action. Only after it vanishes can the
system be modeled over the completions of $Q_0$.

The base-field cocycle (12.6) and the coefficient cocycle (13.15) are different.
The first asks whether a representation of $G_M$ extends to $G_F$. The second asks
whether its scalars descend. Either can vanish while the other does not.

A safe coefficient package chooses one finite $Q$ containing all Hecke fields,
Brauer-character values, local types, and intertwiners. Minimality can be studied
after the system exists. Shrinking prematurely risks adding representations that
are not defined over a common completion.

### 13.6 Independence of the Brauer decomposition

Let

$$
1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i
=\sum_j m_j\operatorname{Ind}_{K_j}^G\phi_j
\tag{13.16}
$$

be two Brauer decompositions.

If an actual descended system $\mathcal R_F$ exists and every auxiliary system is
normalized as its restriction and twist, the projection formula identifies both
virtual expressions with $[\rho_\lambda]$. Thus they are equal in the
Grothendieck group for every $\lambda$.

If effectivity is obtained from determinants, independence requires a little more
than separate effectivity of the two expressions: both determinant packages must
interpolate the same common algebraic polynomials $P_v$, normalized by the
distinguished member. Under that hypothesis, Chebotarev identifies the resulting
semisimple representations. Without the common normalization, two unrelated
effective determinants need not agree away from the distinguished coefficient.

Without normalized auxiliary descents or an effective determinant, two collections
of arbitrary cyclic descent choices can differ by incompatible characters. In that
case independence has not been proved. The finite-group identity is canonical; the
assignment of automorphic objects to its terms may not be.

Any two actual extensions of one irreducible top member differ by a character of
$G^{\mathrm{ab}}$. Therefore canonicity means uniqueness after fixing this
character ambiguity by the distinguished member, determinant, local types, or a
chosen descent datum. It never means that the ambiguity was absent.

### 13.7 The effective compatible-system theorem

**Theorem 13.1 (effective descent of a potentially automorphic system).** Let $F$ be
totally real, let $M/F$ be an admissible Galois automorphy field, and let
$\mathcal R_M$ be the rank-$n$ compatible system attached to the top automorphic
representation. Assume:

1. every top member is absolutely irreducible, $G$-invariant, and strongly
   compatible in a declared local range;
2. a Brauer decomposition (11.3) has been fixed, the solvable descents
   $\Pi_{H_i}$ have been constructed, and the curve-realization or other
   Galois-representation theorem needed to attach their compatible systems is
   available in the declared local range;
3. all coefficients have been enlarged to one number field $Q$;
4. either the top system has a coefficient-rational coherent descent datum
   (13.4)--(13.5), compatible with the auxiliary automorphic descents, or the virtual
   Brauer system has coefficient-compatible continuous degree-$n$ determinants as
   in (13.8), whose associated semisimple representations restrict to $R_\lambda$
   and whose common polynomials are normalized by the distinguished member;
5. one character-twist extension fiber has been normalized compatibly at every
   coefficient place; and
6. every claimed coefficient-field descent has vanishing cocycle (13.15).

Then there is a rank-$n$ semisimple compatible system

$$
\mathcal R_F=\{\rho_\lambda\}_\lambda
$$

over $F$ such that $\rho_\lambda|_{G_M}\simeq R_\lambda$. Its good Frobenius
polynomials are (13.13). It has the determinant and polarization explicitly
specified by the descent package, and it is strongly compatible at every place
where the coherent local descent and the auxiliary local--global comparisons have
been proved. It is independent of the Brauer decomposition up to the normalized
character ambiguity.

**Proof.** Under the coherent route, (13.6) constructs each member. Under the
determinant route, (13.10) constructs its semisimplification. Equation (13.11), or
the matching determinant data, gives the common good polynomials. Continuity and
finite ramification come from the constructed representations and the finite union
of auxiliary bad sets. Restriction to $G_M$ follows directly in the coherent route
and is part of the determinant-effectivity hypothesis in the second. Strong local
compatibility follows from (9.8) only in the declared range. Section 13.5 gives the
coefficient models, and Section 13.6 gives independence and uniqueness. $\square$

The theorem does not assert automorphy of $\mathcal R_F$. It constructs an actual
compatible system. If hypothesis 4 is omitted, the conclusion is only the virtual
system of Section 9.3.

## 14. Analytic continuation and functional equations

Effectivity is not required to multiply and divide meromorphic functions by
integral powers. Brauer induction therefore has an analytic payoff before it has a
representation-theoretic one, but negative powers force the conclusion to remain
meromorphic until cancellation is proved independently.

### 14.1 The quotient construction

Retain the hypotheses of Chapter 11. Each automorphic factor

$$
L(s,\Pi_{H_i}\otimes\theta_i)
$$

has analytic continuation in the range of the standard automorphic theory. Define

$$
L^{\mathrm{Br}}_F(s,\rho)
=
\prod_i
L(s,\Pi_{H_i}\otimes\theta_i)^{n_i}.
\tag{14.1}
$$

Because the exponents are integers, (14.1) is a single-valued meromorphic function.
In a right half-plane, (11.12) gives

$$
L^{\mathrm{Br}}_F(s,\rho)=L_F(s,\rho).
\tag{14.2}
$$

Thus (14.1) is a meromorphic continuation of the original Euler product. Uniqueness
of meromorphic continuation shows that a second Brauer decomposition gives the same
meromorphic function, provided its auxiliary automorphic representations have been
normalized compatibly and both products agree with the same Euler product in a
nonempty connected half-plane.

This independence is analytic, not termwise. The numerator and denominator can
look completely different for two decompositions. They represent the same
meromorphic function because both continue (14.2).

For an incomplete $L$-function, enlarge one finite set $S$ to contain every ramified
place of $M/F$, every bad place of the compatible systems, and every conductor of a
Brauer character. Then

$$
L_F^S(s,\rho)
=
\prod_i
L_{F_i}^{S_i}(s,\Pi_{H_i}\otimes\theta_i)^{n_i}
\tag{14.3}
$$

with $S_i$ the places above $S$. Restoring the omitted factors requires the full
local identity (9.8). One cannot restore them by copying the good polynomial.

### 14.2 The induced functional equation

Let

$$
\Lambda_i(s)=\Lambda(s,\Pi_{H_i}\otimes\theta_i)
$$

in one common unitary normalization. Put

$$
\Lambda_F^{\mathrm{Br}}(s,\rho)
=
\prod_i\Lambda_i(s)^{n_i}.
\tag{14.4}
$$

Each factor satisfies

$$
\Lambda_i(s)
=
\varepsilon_i
\Lambda_i^\vee(1-s).
$$

Multiplying with signed exponents gives

$$
\Lambda_F^{\mathrm{Br}}(s,\rho)
=
\varepsilon^{\mathrm{Br}}(\rho)
\Lambda_F^{\mathrm{Br}}(1-s,\rho^\vee),
\tag{14.5}
$$

where

$$
\varepsilon^{\mathrm{Br}}(\rho)
=
\prod_i\varepsilon_i^{n_i}.
\tag{14.6}
$$

The dual identity follows by dualizing the Brauer projection formula. At each local
place the induction lambda constants in (8.9) and the signed discriminant
contributions combine according to the same character identity. With the canonical
global additive character, the global product gives (14.5).

In an algebraic normalization, the involution in (14.5) is shifted by the purity
weight. One must first account for the Tate twist that converts algebraic Frobenius
roots to unitary roots. Mixing the two normalizations can move the center of the
functional equation by an integer or half-integer.

If the descended system is polarized with multiplier $\mu$, then

$$
\rho^\vee\simeq\rho\otimes\mu^{-1}
$$

and the right side of (14.5) may be rewritten as the appropriately twisted original
function. This rewriting requires the actual multiplier character, not only a
numerical determinant at good places.

### 14.3 Zeros in denominators and uncancelled poles

Write (14.1) as

$$
L_F^{\mathrm{Br}}(s,\rho)
=
\frac{
\prod_{n_i>0}L_i(s)^{n_i}
}{
\prod_{n_i<0}L_i(s)^{-n_i}
}.
\tag{14.7}
$$

Even if every $L_i$ is entire, a zero of a denominator factor gives a pole unless
the numerator vanishes to at least the same order. At a point $s_0$,

$$
\operatorname{ord}_{s=s_0}L_F^{\mathrm{Br}}(s,\rho)
=
\sum_i n_i\operatorname{ord}_{s=s_0}L_i(s).
\tag{14.8}
$$

There is no positivity in (14.8). Brauer induction supplies the signed sum, not the
inequality needed for holomorphy.

A pole can also come from a positive-exponent factor. If an auxiliary descent is
isobaric and contains the trivial character, its standard $L$-function contains a
Dedekind zeta factor. Conversely, a pole of a numerator can be cancelled by a pole
of a denominator. The final order is determined only after all terms are combined.

The equality with the original Euler product in a right half-plane does not settle
these cancellations elsewhere. Beyond that half-plane, the original Euler product
does not already define a holomorphic function to which one could appeal. Analytic
continuation is precisely what is being constructed.

### 14.4 When holomorphy follows

Holomorphy follows under an additional theorem in any of the following forms.

1. An actual cuspidal automorphic representation $\pi/F$ is constructed with
   $L(s,\pi)=L_F(s,\rho)$ at almost every place. In the established cuspidal
   standard-$L$ range, its $L$-function supplies holomorphy; the trivial
   one-dimensional representation retains its familiar pole.
2. An independent theorem proves that $\rho$ has an entire Artin or motivic
   $L$-function. The Brauer quotient then represents that entire function.
3. A zero-divisibility theorem proves from the individual factors that every
   negative contribution in (14.8) is cancelled with sufficient multiplicity.
4. A converse theorem constructs an automorphic object after all its own
   holomorphy, functional equation, and growth hypotheses have been verified.

The mere irreducibility of $\rho$ is not among these reasons. Artin's holomorphy
conjecture predicts a strong conclusion for many irreducible finite-image
representations, but a Brauer quotient alone proves only meromorphy.

For a one-dimensional nontrivial character, class field theory supplies holomorphy
except at the trivial character. For higher-dimensional induced monomial
representations, automorphic induction of the character can supply it in the cyclic
degree covered by Book 95, or in a larger range only after the corresponding
automorphic-induction theorem is separately assumed. These are effectivity results
in special cases, not consequences of the signs disappearing.

### 14.5 What a converse theorem would still need

A converse theorem does not take one meromorphic standard $L$-function and return an
automorphic representation. In a typical rank-$n$ setting it needs a family of
twisted functions, their functional equations, holomorphy in prescribed regions,
boundedness in vertical strips, and suitable local data.

The Brauer construction can be repeated after twists when induction and the
auxiliary automorphic theory control those twists. It may supply meromorphic
continuations and functional equations. Negative coefficients still obstruct the
holomorphy hypotheses. Bounds can also be lost at poles.

Therefore the phrase “apply a converse theorem” must be followed by a ledger:

$$
\{\text{twists}\},\quad
\{\text{completed local factors}\},\quad
\{\text{holomorphy regions}\},\quad
\{\text{growth bounds}\}.
$$

Until that ledger is complete, a converse theorem is a possible route, not an
established descent.

## 15. When automorphy itself descends

An actual compatible system over the base is still not an automorphic
representation. This chapter identifies the solvable case where recursive descent
constructs one and the nonsolvable cases where a separate existence theorem is
indispensable.

### 15.1 The solvable descent theorem

The clean automorphic case occurs when the whole top extension is solvable.

**Theorem 15.1 (solvable automorphic descent selected by an extension).** Let $M/F$
be finite solvable Galois, let

$$
r:G_F\to\operatorname{GL}_2(\overline{\mathbf Q}_\ell)
$$

be continuous semisimple, and suppose $r|_{G_M}$ is irreducible and associated with
a regular algebraic cuspidal automorphic representation $\Pi_M$. Assume the
established compatibility of automorphic Galois representations with cyclic base
change and finite-order twists at every step. Then there is a regular algebraic
cuspidal representation $\pi/F$ such that

$$
\operatorname{BC}_{M/F}(\pi)\simeq\Pi_M
\tag{15.1}
$$

and

$$
\rho_{\pi,\ell}^{\mathrm{ss}}\simeq r.
\tag{15.2}
$$

**Proof.** Choose a prime cyclic tower from $F$ to $M$. The representation $r|_{G_M}$
is conjugation invariant, so strong multiplicity one makes $\Pi_M$ invariant at the
top cyclic step. Choose a cyclic automorphic descent. Its Galois representation and
$r$ restricted to the next field have isomorphic irreducible restrictions to
$G_M$. Clifford theory says that they differ by a character of the cyclic quotient.
Correct the automorphic descent by the inverse character. It is now associated with
the restriction of $r$, hence invariant for the next step. Iterate to $F$.
Irreducibility at the top keeps every selected representation cuspidal.
Transitivity proves (15.1), and equality of good Frobenius polynomials proves
(15.2). $\square$

The extending representation supplies both the $H^2$ coherence and the compatible
choices in every $H^1$ torsor. Without it, one must verify a recursive descent chain
directly.

### 15.2 Why elementary fixed fields do not glue automatically

Now let $G=\operatorname{Gal}(M/F)$ be nonsolvable. For every elementary subgroup
$H_i$, Theorem 15.1 applies to the solvable extension $M/M^{H_i}$ and constructs
$\Pi_{H_i}$. These representations agree after base change to $M$, up to the
prescribed twists.

There is no theorem saying that the collection $\{\Pi_{H_i}\}$ glues to a
$\operatorname{GL}_2$ representation over $F$. Their fields are not arranged in
one tower, and their intersections are controlled by Mackey formulas with conjugate
subgroups. The Brauer coefficients are signed, so even perfect overlap
compatibility gives a virtual object rather than a positive isobaric sum.

The finite-group identity says that the induced Galois classes combine to rank two.
It does not say that the automorphic inductions exist, that their signed combination
is effective, or that an automorphic descent category has subtraction. These are
three distinct missing steps.

### 15.3 Strong multiplicity one as recognition

Suppose an actual cuspidal automorphic representation $\pi/F$ has been constructed
by another method and that, for almost every $v$,

$$
L_v(s,\pi_v)=L_v(s,\rho).
\tag{15.3}
$$

Then the compatible Galois system attached to $\pi$ has the same good polynomials as
the effective descended system. Chebotarev identifies the semisimplified Galois
members. If another cuspidal representation $\pi'/F$ has the same almost-all local
components, strong multiplicity one gives

$$
\pi'\simeq\pi.
$$

This is the correct use of strong multiplicity one: it proves uniqueness and
recognizes a candidate that already exists.

A virtual quotient is not a cuspidal automorphic representation. Strong
multiplicity one has no input object on which to act. Likewise, a table of local
parameters that is not known to be automorphic cannot be promoted by a uniqueness
theorem into an existence theorem.

For isobaric representations, the corresponding multiplicity-one statement
recognizes the unordered multiset of cuspidal constituents with nonnegative
multiplicity. A signed Brauer expression need not be such a multiset.

### 15.4 Independent descent and converse-theorem routes

For a nonsolvable $M/F$, automorphy over $F$ follows if one supplies one of the
following additional inputs.

- A nonsolvable automorphic descent theorem applies to $\Pi_M$, including the
  cocycle, self-twist, central-character, and local hypotheses.
- A geometric construction over $F$ produces an automorphic representation with the
  descended system.
- A trace formula or functorial transfer constructs a candidate over $F$ and proves
  its local compatibility.
- A converse theorem applies after the complete ledger in Section 14.5 has been
  verified.

Once a candidate exists, strong multiplicity one and Chebotarev perform the
identification. Brauer induction remains useful for calculating its $L$-function and
for proving meromorphic continuation before the stronger theorem is available.

If the top extension is not Galois, one can descend through a supplied solvable
tower but cannot speak of invariance under one total Galois group. Passing to a
normal closure is legitimate only after top automorphy and all image conditions have
been re-established there.

### 15.5 The exact hierarchy of conclusions

The hypotheses and conclusions can be summarized as follows.

| available input | justified conclusion |
|---|---|
| top automorphy and a Brauer decomposition | virtual identities of Galois classes and Euler factors |
| automorphic descents over every elementary fixed field | quotient of automorphic $L$-functions; meromorphic continuation and functional equation |
| coherent top descent datum or effective determinants | actual semisimple compatible system over $F$ |
| solvable total extension plus extending irreducible representation | actual cuspidal automorphic descent to $F$ |
| nonsolvable independent descent or a completed converse theorem | actual automorphy over $F$ |
| equality of almost-all factors with an existing candidate | identification by Chebotarev and strong multiplicity one |
| equality of almost-all factors without a candidate | no automorphic existence conclusion |

This table is the conclusion-strength audit for every application.

## 16. Arithmetic invariants under induction and descent

A descended system is useful only with its arithmetic structure intact. The
determinant, pairing, parity, weights, local monodromy, and integral lattices obey
different functorial rules, so none should be inferred from the rank alone.

### 16.1 Determinants and polarizations

For a finite extension $L/K$ and a rank-$n$ representation $V$ of $G_L$,

$$
\det\operatorname{Ind}_{G_L}^{G_K}V
=
\Delta_{L/K}^{\,n}
\bigl((\det V)\circ\operatorname{Ver}_{L/K}\bigr).
\tag{16.1}
$$

For a character, this recovers the central-character factor in automorphic
induction. The permutation determinant takes values in $\{\pm1\}$, so in rank two
its square is trivial. It should nevertheless be written before simplification,
because it survives in odd rank and records the normalization of transfer.

If

$$
V^\vee\simeq V\otimes\mu|_{G_L}^{-1},
$$

then

$$
(\operatorname{Ind}V)^\vee
\simeq
\operatorname{Ind}(V^\vee)
\simeq
\operatorname{Ind}V\otimes\mu^{-1}.
\tag{16.2}
$$

Thus induction preserves essential self-duality when the multiplier descends to
$G_K$. A nondegenerate induced pairing can be written by summing the original
pairing orthogonally over cosets; when one common multiplier descends, this
construction preserves the symmetry sign. In a more general conjugate-self-dual
induction, cosets can instead be paired by an involution and the sign must be
computed from that involution. The permutation determinant in (16.1) is not, by
itself, a polarization sign.

On descent, the top multiplier must be the restriction of a bottom character. This
is a rank-one descent problem. An invariant multiplier need not have a norm
antecedent, and two antecedents can differ by a character killed by restriction.
For rank two, twisting a proposed descent by $\eta$ changes the multiplier and
determinant by $\eta^2$.

A virtual Brauer class has a virtual determinant but no honest nondegenerate pairing.
Polarization is not additive under subtraction. It becomes meaningful only after an
actual descended representation has been constructed.

### 16.2 Parity and archimedean type

If $F$ and $M$ are totally real, every real place of $F$ splits into real places of
$M$. Restriction of a totally odd two-dimensional representation remains odd at
every upper real place. The top signs still do not select a unique bottom
extension. Indeed, complex conjugation fixes the totally real field $M$, so it lies
in $G_M$; every character of $G_F/G_M$ is trivial on it. All twists in the descent
fiber therefore have the same archimedean parity.

For an actual rank-two descent $\rho_\lambda$, oddness is

$$
\det\rho_\lambda(c_\tau)=-1,
\qquad
\operatorname{tr}\rho_\lambda(c_\tau)=0
\tag{16.3}
$$

at every real place $\tau$ of $F$. This must be checked on the selected extension.
For a totally real top extension, neither this determinant nor the trace separates
the quotient-character twists, because those twists are even at infinity. In a
different archimedean field profile, a quadratic twist can interchange the two
signs while its square leaves the rank-two determinant unchanged.

Automorphic induction from a CM quadratic field to a totally real field gives an
odd representation when the infinity type has the correct conjugate asymmetry.
Induction from a totally real field has a different archimedean parameter and a
higher-dimensional sign condition. The word “odd” should not be transferred from
rank two without stating the relevant polarization sign.

Archimedean gamma factors in a Brauer quotient obey induction exactly. A signed
gamma quotient can simplify to the gamma factor of an actual descent, but the
simplification is an identity of virtual Weil parameters. It does not prove the
existence of the bottom archimedean automorphic representation.

### 16.3 Purity and weights

Restriction preserves purity. If $\alpha$ is a Frobenius root of size
$q_v^{w/2}$, then at a place of residue degree $f$ the restricted root
$\alpha^f$ has size

$$
q_v^{fw/2}=q_w^{w/2}.
$$

Induction also preserves purity, as explained in Section 9.1. Finite-order Brauer
twists have weight zero. Therefore every term in the virtual Brauer construction
has the same purity weight as the top system.

A virtual pure class is only a signed statement about roots. Once effectivity is
proved, the actual descended member is pure of that weight because its good
polynomial is the effective polynomial reconstructed from those roots.

Hodge--Tate labels restrict by composition of embeddings. For induction, the labels
over an embedding of the lower field are the union of labels over all embeddings of
the upper field extending it. For descent, the top labelled weights must be constant
on the appropriate Galois orbits. This necessary invariance does not remove the
cocycle obstruction.

Tate twists shift every Hodge--Tate weight by the twist integer and change purity
weight by twice that integer. A finite-order twist changes neither. These tests
audit the normalization of every auxiliary $\theta_i$.

### 16.4 Local types and monodromy

At $v\nmid\ell$, restriction sends

$$
(r_v,N_v)\longmapsto(r_v|_{W_{L_w}},N_v).
\tag{16.4}
$$

Finite inertia can become smaller, an irreducible Weil representation can split,
and conductor breaks are reindexed. The operator $N_v$ remains the same linear
operator. In particular, nonzero Steinberg monodromy remains nonzero after scalar
extension and restriction, though the surrounding Weil representation changes.

Induction sends local parameters by (9.2). Its conductor includes the discriminant
term. At an unramified place its Frobenius polynomial is (8.4). These two formulas,
not the global extension degree, determine the local type.

Descent is not determined by restriction. A top local parameter can admit several
extensions to $W_{F_v}$, differing by characters of the local quotient. They can
have different conductors, Frobenius eigenvalues, or constituent characters.
A global coherent representation over $F$ selects one extension. Abstract
invariance of the top local parameter does not.

If strong local--global compatibility is known only outside a set, the descended
system is strong only in the transported range. Almost-all Frobenius equality
identifies the global semisimplification once both global representations exist,
but it does not manufacture a coefficient-independent description of bad inertia.

### 16.5 Integral and residual data

A rational compatible system does not carry canonical stable lattices. Induction of
a chosen lattice is integral and stable, but a virtual difference of induced
lattices is not a lattice. Coherent descent of a rational representation likewise
does not automatically descend a finite-flat group scheme or an integral pairing.

Residual semisimplifications are canonical for chosen rational members, but
reducible extension classes depend on lattices. Negative Brauer coefficients cannot
be reduced modulo $\lambda$ as negative finite group schemes. If a residual
application is intended, first construct the actual descended member, then choose
or descend a lattice, and only then reduce.

Restriction can shrink a residual image. The disjointness condition that preserved
the image over the first potential-automorphy field must be rechecked for the
Galois top field and every later extension. Brauer induction does not repair
absolute irreducibility lost by restriction.

At a coefficient-prime place, de Rham or crystalline descent is a filtered
comparison problem. An integral finite-flat conclusion requires compatible integral
descent data. It does not follow from a virtual Hodge multiset or from equality of
good Frobenius polynomials.

## 17. Failure modes and hostile checks

A descent argument is most reliable when every tempting shortcut is tested on a
small case. This chapter turns the recurrent logical errors into diagnostics. Each
diagnostic has three parts: the asserted implication, the reason it fails, and the
extra datum that repairs it.

### 17.1 Negative coefficients

The first failed implication is

$$
\text{virtual rank }n
\quad\Longrightarrow\quad
\text{an actual rank-}n\text{ object}.
\tag{17.1}
$$

Return to the integral identity

$$
1_{S_3}
=
\operatorname{Ind}_{C_2}^{S_3}1
-
\operatorname{Ind}_{C_3}^{S_3}\zeta,
\tag{17.2}
$$

where $\zeta$ is either nontrivial character of $C_3$. Let $M/F$ have Galois group
$S_3$, let $F_2=M^{C_2}$ and $F_3=M^{C_3}$, and let $\rho$ have rank $n$ over
$F$. The projection formula gives

$$
[\rho]
=
\left[
\operatorname{Ind}_{G_{F_2}}^{G_F}
  \rho|_{G_{F_2}}
\right]
-
\left[
\operatorname{Ind}_{G_{F_3}}^{G_F}
  \bigl(\rho|_{G_{F_3}}\otimes\zeta\bigr)
\right].
\tag{17.3}
$$

The two terms have ranks $3n$ and $2n$. Their difference has virtual rank $n$.
There is no canonical injection of the second induced representation into the
first, and character theory does not assert that such an injection exists. Even if
an injection happened to exist at one coefficient place, its cokernel would have to
be shown compatible in the coefficient prime and with all local data.

On the automorphic side, the formal analogue of (17.3) is a quotient

$$
L_F(s,\rho)
=
\frac{
  L_{F_2}(s,\Pi_2)
}{
  L_{F_3}(s,\Pi_3\otimes\zeta)
}.
\tag{17.4}
$$

There is no operation of subtracting an isobaric representation. Positive virtual
rank does not turn (17.4) into the standard $L$-function of a
$\operatorname{GL}_n$ representation.

The repair for (17.1) is effectivity. One must provide a coherent extension of the
top representation, an effective degree-$n$ determinant, or an independently
constructed rank-$n$ object whose class equals (17.3). A dimension calculation is
then a consistency test, not the construction.

### 17.2 Noncuspidal induction

The second failed implication is

$$
\text{automorphic input is cuspidal}
\quad\Longrightarrow\quad
\text{every induction or base change used later is cuspidal}.
\tag{17.5}
$$

Let $L/K$ be cyclic and let $\chi$ be a Hecke character of $L$. Automorphic
induction $\operatorname{AI}_{L/K}(\chi)$ is cuspidal only when the Galois orbit of
$\chi$ has the full expected size. If $\chi$ is fixed by a nontrivial subgroup, the
induction decomposes isobarically through an intermediate field. The associated
induced Galois representation is reducible for the same Clifford-theoretic reason.

The quadratic dihedral example makes the reverse operation equally visible. For
$\theta\ne\theta^\sigma$,

$$
\pi=\operatorname{AI}_{L/F}(\theta)
$$

is cuspidal, but

$$
\operatorname{BC}_{L/F}(\pi)
=
\theta\boxplus\theta^\sigma
\tag{17.6}
$$

is not. Moreover $\pi\simeq\pi\otimes\eta_{L/F}$. Thus a self-twist can signal that
a cuspidal representation is induced and that its base change will split.

This matters twice in a Brauer argument. An auxiliary automorphic induction may be
isobaric rather than cuspidal, and a top representation obtained by base change may
have nonscalar endomorphisms. Strong multiplicity one must then be used in its
isobaric form, and the scalar-cocycle calculation of Section 12.2 no longer applies
without replacing scalars by the full automorphism group of the isobaric object.

The repair is to calculate the stabilizer of every inducing datum, record whether
the output is cuspidal or isobaric, and use a descent theorem stated for that
category. Irreducibility of the relevant Galois restriction is a useful sufficient
cuspidality test only where local--global compatibility and the induction theorem
identify the two sides.

### 17.3 Incoherent descent

The third failed implication is

$$
{}^gR\simeq R\text{ for every }g
\quad\Longrightarrow\quad
R\text{ descends}.
\tag{17.7}
$$

A two-generator parameter-side diagnostic isolates the error. Let the quotient
group be

$$
G=C_2\times C_2=\langle a,b\rangle.
$$

Suppose an absolutely irreducible top Weil or Galois parameter is invariant and
chosen intertwiners $A_a,A_b$ satisfy, after normalizing their squares and dividing
out the fixed section factors from (12.8),

$$
A_aA_b=-A_bA_a.
\tag{17.8}
$$

Each cyclic subgroup $\langle a\rangle$, $\langle b\rangle$, and
$\langle ab\rangle$ admits coherent descent after a scalar rescaling of its one
intertwiner. In this corrected split model, simultaneous descent would require the
intertwiners for $a$ and $b$ to commute. Equation (17.8) prevents this. For a
nonsplit group extension, “commute” is replaced by the exact two versions of
(12.8); their quotient gives the same scalar commutator test.

Rescaling $A_a$ and $A_b$ does not change their commutator. The sign in (17.8)
therefore represents the nontrivial alternating part of a scalar factor set in

$$
H^2(C_2\times C_2,\overline{\mathbf Q}^{\,\times}).
\tag{17.9}
$$

Cyclic restrictions fail to see it. This is why compatible descents along several
cyclic subgroups do not automatically glue across the whole group.

There is a second incoherence even after the $H^2$ class vanishes. At consecutive
cyclic stages, one may choose descents differing by quotient characters. A choice
that is invariant at one stage need not be invariant at the next. The resulting
failure is the $H^1$ torsor problem. In a solvable tower, the choices must be made
recursively, with the representation already known to extend serving as the
normalization.

The parameter-side repair for (17.7) is a family of intertwiners satisfying the
exact multiplication law (13.5), together with compatible character choices. On
the automorphic side the unconditional repair in the solvable range is a recursive
chain of cyclic descents with compatible twist normalization. When a compatible
global parameter is supplied, its cocycle can select that chain; without such a
parameter, one does not promote (17.9) to the complete obstruction of the
automorphic isomorphism class. A list of invariant isomorphism classes is not a
descent chain.

### 17.4 Coefficient mismatch

The fourth failed implication is

$$
\text{the final character is rational-valued}
\quad\Longrightarrow\quad
\text{every auxiliary term is defined over the rational field}.
\tag{17.10}
$$

Again consider $C_3\triangleleft S_3$. A nontrivial character $\zeta$ takes values
in $\mathbf Q(\zeta_3)$, while

$$
\operatorname{Ind}_{C_3}^{S_3}\zeta
=
\operatorname{Ind}_{C_3}^{S_3}\zeta^{-1}
$$

has rational character values and a rational model. Rationality appears only after
the two conjugate character lines are assembled by induction.

At a coefficient prime $\lambda$, the twist by $\zeta$ requires a chosen embedding

$$
\mathbf Q(\zeta_3)\hookrightarrow\overline{\mathbf Q}_\lambda.
$$

Coefficient conjugation sends it to the inverse twist. If the auxiliary system at
$\lambda$ uses $\zeta$ while the purported conjugate system at $\sigma\lambda$ is
also labeled by $\zeta$ rather than $\zeta^{-1}$, the family need not satisfy

$$
{}^\sigma \mathcal V_\lambda\simeq\mathcal V_{\sigma\lambda}.
\tag{17.11}
$$

The rationality of the induced character cannot correct an incoherent choice made
before induction.

A larger coefficient field containing all Brauer-character values is harmless.
The error is to confuse a common field with a descended field of definition. To
shrink from $Q$ to $Q_0$, common Frobenius polynomials are necessary, and the
coefficient cocycle of (13.15) must vanish. A rational trace does not alone produce
a rational model; Schur-index and factor-set obstructions are precisely the missing
information.

The repair is to close the coefficient field under all character values and Hecke
eigenvalues, pair every construction with all of its coefficient conjugates, and
only then perform coefficient descent. The embedding $\iota_\lambda$ is part of the
data, not silent notation.

### 17.5 A quotient with poles

The fifth failed implication is

$$
\text{all factors in a quotient are entire}
\quad\Longrightarrow\quad
\text{the quotient is entire}.
\tag{17.12}
$$

In the $S_3$ diagnostic, write

$$
\Lambda_F^{\mathrm{Br}}(s)
=
\frac{\Lambda_2(s)}{\Lambda_3(s)}.
\tag{17.13}
$$

If $\Lambda_3$ has a zero of order $m>0$ at $s_0$ and $\Lambda_2(s_0)\ne0$, then

$$
\operatorname{ord}_{s=s_0}\Lambda_F^{\mathrm{Br}}=-m,
$$

so the Brauer continuation has a pole of order $m$. Both numerator and denominator
may be entire. Their quotient is only meromorphic.

Replacing the completed functions by incomplete Euler products does not remove the
problem. It merely discards finitely many explicit local factors. Nor does the
functional equation prove cancellation: it transports zeros and poles to their
dual locations.

A second danger comes from isobaric factors. A positive-exponent factor may itself
have a pole, while a negative-exponent factor may cancel it. The signed order
formula (14.8), not the analytic behavior of the terms one at a time, gives the
answer.

The repair is an independent holomorphy theorem, an actual cuspidal automorphic
realization of the quotient, or a proved zero-divisibility statement. Without one
of these, the exact conclusion is meromorphic continuation and a meromorphic
functional equation.

### 17.6 Wrong subgroup and field directions

The sixth failed implication comes from reading the Galois correspondence in the
same direction as subgroup inclusion. For

$$
F_H=M^H,\qquad H\le G=\operatorname{Gal}(M/F),
$$

the complete dictionary is

$$
\operatorname{Gal}(M/F_H)=H,
\qquad
[F_H:F]=[G:H].
\tag{17.14}
$$

If $H_1\le H_2$, then

$$
F_{H_2}\subseteq F_{H_1}.
\tag{17.15}
$$

Inside $M$, intersections and composita satisfy

$$
F_{H_1}F_{H_2}=M^{H_1\cap H_2},
\qquad
F_{H_1}\cap F_{H_2}=M^{\langle H_1,H_2\rangle}.
\tag{17.16}
$$

Conjugation sends $H$ to $gHg^{-1}$ and $F_H$ to $g(F_H)$. These formulas are the
field-theoretic content behind the double cosets in the Mackey formula.

The subgroup $H$ being solvable proves that $M/F_H$ is solvable. It says nothing by
itself about $F_H/F$. The latter is Galois only when $H$ is normal, in which case
its Galois group is $G/H$. If $G$ is nonsolvable, $F_H/F$ can be nonsolvable or
nongalois even though $H$ is elementary.

A subnormal series

$$
H=H_0\triangleright H_1\triangleright\cdots
\triangleright H_r=1
$$

with cyclic prime-order quotients produces the reversed field tower

$$
F_H=M^{H_0}\subset M^{H_1}\subset\cdots\subset M^{H_r}=M.
\tag{17.17}
$$

This is the tower on which cyclic base change and descent operate. Applying
solvable base change to $M/F$ would instead require $G$ itself to be solvable.

Finally,

$$
\operatorname{Ind}_{H}^{G}
\quad\longleftrightarrow\quad
\operatorname{Ind}_{G_{F_H}}^{G_F},
\tag{17.18}
$$

whereas restriction from $F$ to $F_H$ corresponds to
$\operatorname{Res}_{H}^{G}$. Reversing either arrow changes ranks, local residue
degrees, and conductor terms, so it cannot be repaired by notation later.

### 17.7 Equality at good places

The seventh failed implication is

$$
\text{matching almost-all Euler factors}
\quad\Longrightarrow\quad
\text{automorphy and complete local equality}.
\tag{17.19}
$$

Let $\rho_1$ and $\rho_2$ be continuous semisimple $\ell$-adic representations of
$G_F$, unramified outside finite sets. If their characteristic polynomials agree at
almost every Frobenius element, Chebotarev density and the characteristic-zero
Brauer--Nesbitt theorem give

$$
\rho_1\simeq\rho_2.
\tag{17.20}
$$

This is a powerful uniqueness statement, but both representations must already
exist. It identifies semisimplifications. It does not recover a discarded extension
class, a stable lattice, or a residual extension.

Likewise, if two isobaric automorphic representations already exist and their
unramified local components agree almost everywhere, strong multiplicity one
identifies them. A rational function assembled from signed Euler factors is not an
automorphic representation, so it is not an input to that theorem.

Good factors also omit monodromy, ramified inertia, conductor exponents, and the
choice among local extensions of an invariant top parameter. Equality in (17.20)
does imply equality of the ramified semisimple global representation once both
global representations exist, but a local--global compatibility statement at a bad
place still has to identify the associated Weil--Deligne parameter, including its
monodromy operator.

For two existing representations over one characteristic-zero coefficient field,
equality of traces on the dense set of good Frobenius classes already suffices for
(17.20). By contrast, a bare cross-coefficient table containing one algebraic trace
at each $v$ does not itself exhibit common degree-$n$ characteristic polynomials in
rank greater than two. In the compatible-system construction one therefore uses
the auxiliary local polynomials to control traces of powers, or supplies the full
determinant law. The repair is to state exactly which data agree, invoke
Chebotarev only for existing semisimple representations, invoke strong multiplicity
one only for existing automorphic representations, and keep bad-place
compatibility as a separate assertion.

## 18. The final theorem package

The preceding chapters separate four outputs that are often compressed into the
word “descent.” The following theorems are designed to be quoted independently.
Their hypotheses deliberately repeat the pieces that cannot be inferred from
Brauer induction.

### 18.1 The analytic Brauer theorem

**Theorem 18.1 (analytic continuation by a Brauer quotient).** Let $F$ be a number
field, let

$$
\rho:G_F\longrightarrow\operatorname{GL}_n(\overline{\mathbf Q}_\ell)
$$

be continuous and semisimple, fix an identification
$\iota:\overline{\mathbf Q}_\ell\simeq\mathbf C$ for its algebraic Frobenius data,
and let $M/F$ be finite Galois with group $G$. Assume:

1. the restriction $\rho|_{G_M}$ corresponds to an automorphic representation
   $\Pi_M$ on $\operatorname{GL}_n(\mathbf A_M)$ with the required local--global
   compatibility;
2. there is an integral Brauer identity

   $$
   1_G=\sum_i n_i\operatorname{Ind}_{H_i}^{G}\theta_i
   $$

   with $H_i$ elementary and $\theta_i$ one-dimensional;
3. for $F_i=M^{H_i}$, the solvable extension $M/F_i$ admits automorphic descent of
   $\Pi_M$ to $\Pi_i/F_i$, selected so that
   $\rho_{\Pi_i,\ell}^{\mathrm{ss}}\simeq\rho|_{G_{F_i}}$;
4. twisting $\Pi_i$ by the finite-order character attached to $\theta_i$ is
   available and its Galois and automorphic local factors agree in the stated
   compatibility range; and
5. all incomplete factors omit one common finite set containing every ramified and
   incompatible place.

Then, in a right half-plane,

$$
L_F^S(s,\rho)
=
\prod_i
L_{F_i}^{S_i}(s,\Pi_i\otimes\theta_i)^{n_i}.
\tag{18.1}
$$

The right side gives meromorphic continuation of the left side and a meromorphic
functional equation. If full local--global compatibility is known at the omitted
places, the completed identity includes the precise finite conductors,
archimedean gamma factors, and epsilon factors determined by local induction.

The conclusion is independent of the chosen Brauer identity as a meromorphic
function, because every correctly normalized product agrees with the same Euler
product in the initial half-plane.

**Proof.** Tensor the Brauer identity with $\rho$ and use the projection formula.
Galois Artin formalism changes the $L$-function of each induced term over $F$ into
the $L$-function of its restriction and twist over $F_i$. Local--global
compatibility identifies that function with the standard automorphic $L$-function
of $\Pi_i\otimes\theta_i$; no automorphic induction from $F_i$ to $F$ is needed.
Analytic continuation and functional equations of the auxiliary automorphic factors
persist under integral signed products. Uniqueness of meromorphic continuation
gives independence. Negative $n_i$ become denominators, so the proof supplies no
cancellation theorem. $\square$

The theorem asserts neither holomorphy nor automorphy of $\rho$. If an auxiliary
descent is isobaric, its isobaric standard $L$-function is used. If local
compatibility is known only away from $S$, the theorem makes no claim about the
missing local factors.

### 18.2 The virtual compatible-system theorem

**Theorem 18.2 (Brauer construction of a virtual compatible system).** Let $M/F$
be finite Galois, let $\mathcal R_M=\{R_\lambda\}_\lambda$ be a rank-$n$ compatible
system over $M$, and fix an integral Brauer identity as in Theorem 18.1. Suppose
that for every $i$ there is a compatible system
$\mathcal R_i=\{R_{i,\lambda}\}_\lambda$ over $F_i=M^{H_i}$ whose restriction to
$G_M$ is isomorphic to $\mathcal R_M$, with the restriction isomorphisms and cyclic
twist choices fixed compatibly. Suppose all character twists and coefficient
conjugates are defined over one finite coefficient field $Q$.

For every $\lambda$, set

$$
\mathcal V_\lambda
=
\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_F}
  (R_{i,\lambda}\otimes\theta_{i,\lambda})
\right].
\tag{18.2}
$$

Then $\{\mathcal V_\lambda\}_\lambda$ is a virtual compatible system over $F$ of
virtual rank $n$. It is unramified outside a finite set independent of $\lambda$.
At every place in the declared compatibility range, its local Weil--Deligne class
and Euler factor are the signed induction expressions of (9.8). At a good place
$v$, its reciprocal Euler expression is the rational function

$$
P_v^{\mathrm{vir}}(X)
=
\prod_i
P_{i,v}(X)^{n_i}\in Q(X),
\tag{18.3}
$$

where $P_{i,v}$ is the reciprocal Euler polynomial of the induced $i$-th term,
computed over the places above $v$ by the residue-degree formula (8.4). The virtual
local factor is
$P_v^{\mathrm{vir}}(q_v^{-s})^{-1}$. This rational function is independent of
$\lambda$ after applying the chosen embedding of $Q$.

If the auxiliary descents are normalized by one coherent top descent datum, the class
(18.2) is independent of the Brauer decomposition in the Grothendieck group. If a
distinguished representation $\rho_{\lambda_0}$ over $F$ restricts to
$R_{\lambda_0}$ and selects the auxiliary descents, then

$$
\mathcal V_{\lambda_0}=[\rho_{\lambda_0}].
\tag{18.4}
$$

**Proof.** Restriction, finite-order twist, and induction preserve compatible
virtual local data, while the union of their bad sets is finite. The rank is

$$
\sum_i n_i[G:H_i]n=n.
$$

Mackey theory gives the local identities. Coefficient compatibility follows only
after adjoining and conjugating all values of the $\theta_i$. Independence follows
by tensoring either finite-group identity with the same normalized descent datum.
Equation (18.4) is the projection formula at the distinguished member. $\square$

The rational function (18.3) need not be a polynomial in general. If the
distinguished member (18.4) exists and all terms are transported from the one field
$Q$, then at a good place its image in $Q_{\lambda_0}(X)$ is a polynomial. Injectivity
of $Q\hookrightarrow Q_{\lambda_0}$ then shows that (18.3) already lies in $Q[X]$.
Even this termwise cancellation at every good Frobenius does not, without a
determinant or coherent descent theorem, prove that the global virtual class is
effective at a new $\lambda$. Thus the theorem still constructs no
$\rho_\lambda$ at the new coefficient places and does not assert that (18.2) is the
class of an actual representation.

### 18.3 The effective descent theorem

**Theorem 18.3 (two effectivity routes).** Retain the hypotheses of Theorem 18.2.
Assume that every top member is absolutely irreducible and $G$-invariant, and that
one of the following two packages is supplied.

**Coherent-cocycle package.** For every $\lambda$, there are intertwiners
$A_{g,\lambda}$ satisfying (13.4)--(13.5); they arise from one algebraic coefficient
datum, commute with coefficient conjugation, and select the same character-twist
fiber as the auxiliary descents.

**Determinant-effectivity package.** For every $\lambda$, the virtual traces and
higher characteristic coefficients in (18.2) extend to a continuous degree-$n$
determinant of $G_F$; these determinants have common algebraic Frobenius
polynomials, their associated semisimple representations restrict to $R_\lambda$,
and the coefficient descent cocycles vanish.

Then there is an actual rank-$n$ semisimple compatible system

$$
\mathcal R_F=\{\rho_\lambda\}_\lambda
$$

over $F$ with

$$
\rho_\lambda|_{G_M}\simeq R_\lambda.
\tag{18.5}
$$

Its good Frobenius polynomials lie in one number field, and its semisimplified
members are unique after fixing the character ambiguity
$\widehat{G^{\mathrm{ab}}}$. It is independent of the Brauer decomposition after
that normalization.

In the coherent-cocycle package, the formula

$$
\rho_\lambda(xs(g))=R_\lambda(x)A_{g,\lambda}
$$

constructs each member. In the determinant-effectivity package, characteristic-zero
effectivity constructs the unique semisimple member. Common Frobenius polynomials
give compatibility, while Chebotarev gives uniqueness and independence.

Determinants, polarizations, parity, purity, and local types descend only to the
extent encoded in the supplied datum:

- the determinant must satisfy the transfer and quotient-character normalization;
- a polarization requires coherent descended pairings and the stated multiplier;
- archimedean parity requires an actual extension at every real decomposition group;
- purity follows for the effective good Frobenius polynomials;
- strong local compatibility holds only where the descended local parameters and
  local--global comparison have been constructed; and
- integral or residual structures require separate stable-lattice descent.

The conclusion is a compatible system, not automorphy. A positive virtual rank,
polynomial-looking good factors, or vanishing of the obstruction at one coefficient
place without a common algebraic cocycle is not a substitute for either package.

### 18.4 The automorphic descent theorem

**Theorem 18.4 (exact automorphic endpoints).** Let the effective system
$\mathcal R_F$ of Theorem 18.3 have top automorphic representation $\Pi_M$. The
following are distinct sufficient routes to an automorphic representation over
$F$.

1. Suppose $M/F$ is solvable, cyclic base change and descent are available in the
   relevant degree, $\Pi_M$ is cuspidal, and a member $\rho_{\lambda_0}$ of
   $\mathcal R_F$ selects compatible descents at every cyclic stage. If its
   restrictions used in the tower remain irreducible, recursive solvable descent
   produces a cuspidal $\pi/F$ with

   $$
   \operatorname{BC}_{M/F}(\pi)\simeq\Pi_M,
   \qquad
   \rho_{\pi,\lambda}^{\mathrm{ss}}\simeq\rho_\lambda
   $$

   throughout the established compatible-system range.

2. Suppose $M/F$ is arbitrary and an independent nonsolvable descent theorem,
   functorial transfer, trace-formula construction, or geometric automorphy theorem
   produces an automorphic candidate $\pi/F$ with the required almost-all local
   factors. Then Chebotarev identifies its compatible system with
   $\mathcal R_F$, and strong multiplicity one identifies $\pi$ among existing
   isobaric candidates.

3. Suppose a converse theorem in the relevant degree applies to the complete
   family of twists of the Brauer quotient, with all required holomorphy, functional
   equations, local specifications, and vertical-strip bounds verified. Then its
   output is an automorphic representation over $F$, which is identified with the
   effective system by its good factors.

In the first route, the extending member kills the cyclic $H^1$ ambiguities and
supplies coherent choices. Under the stated irreducibility hypothesis the twist
action is free. If that hypothesis is weakened, self-twists can identify nominally
different descents and the result can become isobaric. Central characters are
obtained from the determinant formula and may leave a residual square-class
ambiguity until the extending member fixes it.

If $G=\operatorname{Gal}(M/F)$ is nonsolvable and neither route 2 nor route 3 is
available, elementary subgroup fixed fields do not furnish an automorphic
representation over $F$. The valid conclusions stop at Theorem 18.1 or, with
effectivity, Theorem 18.3.

**Proof.** Route 1 is recursive cyclic descent, with the extending Galois
representation choosing the correct twist at each stage; transitivity gives the
bottom base change. Routes 2 and 3 contain the missing existence theorem in their
hypotheses. Once a candidate exists, almost-all local compatibility, Chebotarev,
and strong multiplicity one give the claimed identifications. None of those
uniqueness principles is used to create the candidate. $\square$

### 18.5 The exported descent record

A later application should carry the following record rather than the bare phrase
“by Brauer induction.”

| entry | data that must be recorded |
|---|---|
| base datum | the field $F$, the rank, the distinguished coefficient member, and the reciprocity normalization |
| top field | the totally real finite Galois extension $M/F$, proof of top automorphy over $M$, and any image or disjointness conditions rechecked over $M$ |
| finite group | $G=\operatorname{Gal}(M/F)$ and the verified integral identity $\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i=1_G$ |
| fixed fields | $F_i=M^{H_i}$, the equalities $\operatorname{Gal}(M/F_i)=H_i$, and explicit solvable towers from $F_i$ to $M$ |
| auxiliary automorphy | $\Pi_M$, every selected descent $\Pi_i/F_i$, every finite-order twist, and whether each object is cuspidal or isobaric |
| coefficients | one field $Q$ containing Hecke data and character values, all embeddings $\iota_\lambda$, coefficient conjugates, and the coefficient descent cocycle |
| local scope | a common bad set, good Euler polynomials, conductor and discriminant terms, archimedean factors, monodromy, and the exact range of local--global compatibility |
| virtual output | formula (18.2), virtual rank, signed Euler product, and the analytic conclusion of Theorem 18.1 |
| effectivity | either coherent intertwiners with their $H^2$ law and recursive $H^1$ choices, or a degree-$n$ determinant with the restriction property |
| ambiguity | quotient characters, central-character constraints, self-twist stabilizers, and the normalization selecting one descent |
| arithmetic structure | determinant, multiplier, polarization, parity, purity, Hodge--Tate labels, local types, and any integral lattice data actually descended |
| final strength | one of: virtual class, meromorphic $L$-function, actual compatible system, isobaric automorphy, or cuspidal automorphy |
| canonicity | independence of the Brauer identity and uniqueness only after the stated character and coefficient normalizations |

This record exposes the two places where canonicity can fail. Different Brauer
identities give the same finite-group class, but arbitrary auxiliary descent choices
can differ by characters. Different coefficient embeddings give conjugate systems,
but coherent models over a smaller field require the coefficient cocycle to vanish.
Canonicity is therefore a proved consequence of normalization and uniqueness, not a
property of a displayed quotient.

It also separates the roles of the fields. The top field is where automorphy is
known. The fixed fields are where solvable descent is performed. The base field is
where an actual object is sought. These three roles can coincide in a solvable
example, but they must remain distinct in a nonsolvable one.

### 18.6 Conclusion

Brauer induction solves an integral character-theoretic problem. It replaces the
trivial character of an arbitrary finite group by a signed sum of characters
induced from one-dimensional characters of elementary subgroups. The signs are
essential, and the fixed-field correspondence turns the solvability of those
subgroups into solvable towers above their fixed fields.

Artin formalism carries the identity to local factors, conductors, archimedean
terms, epsilon factors, and global $L$-functions. Automorphic base change and
descent make the auxiliary terms automorphic. The immediate output is a virtual
class and a meromorphic quotient.

Two additional boundaries remain. Effectivity is needed to turn the virtual class
into a compatible system, and a genuine automorphic existence theorem is needed to
turn that system into an automorphic representation. Cocycles, character torsors,
self-twists, coefficient fields, and local types are the data controlling those
boundaries.

With those data supplied, the construction is canonical up to its explicitly
normalized character ambiguity and is independent of the chosen Brauer
decomposition. Without them, the conclusion must stop where the proof stops:
meromorphic rather than entire, virtual rather than effective, or potentially
automorphic rather than automorphic over the original field.
