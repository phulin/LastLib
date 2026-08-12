# Brauer Induction for Automorphy Families

## Contents

1. [One finite packet array](#1-one-finite-packet-array)
   - [The obstruction at the ground field](#11-the-obstruction-at-the-ground-field)
   - [The controlled-top datum](#12-the-controlled-top-datum)
   - [The packet-array theorem](#13-the-packet-array-theorem)
   - [Conventions and boundaries](#14-conventions-and-boundaries)
   - [The order of construction](#15-the-order-of-construction)
2. [Induction, restriction, and double cosets](#2-induction-restriction-and-double-cosets)
   - [Virtual representations](#21-virtual-representations)
   - [Finite-index induction and the tensor identity](#22-finite-index-induction-and-the-tensor-identity)
   - [Frobenius reciprocity](#23-frobenius-reciprocity)
   - [Mackey decomposition](#24-mackey-decomposition)
   - [Fixed fields, composita, and completions](#25-fixed-fields-composita-and-completions)
   - [Determinants of induced representations](#26-determinants-of-induced-representations)
3. [Elementary groups and integral Brauer induction](#3-elementary-groups-and-integral-brauer-induction)
   - [Elementary groups](#31-elementary-groups)
   - [Monomiality](#32-monomiality)
   - [The local projector and restriction criterion](#33-the-local-projector-and-restriction-criterion)
   - [The integral relation](#34-the-integral-relation)
   - [A diagnostic relation](#35-a-diagnostic-relation)
4. [Prime-cyclic towers inside elementary groups](#4-prime-cyclic-towers-inside-elementary-groups)
   - [The normalizer condition](#41-the-normalizer-condition)
   - [Subnormal prime-cyclic refinement](#42-subnormal-prime-cyclic-refinement)
   - [The reversed fixed-field tower](#43-the-reversed-fixed-field-tower)
   - [Admissibility is an arithmetic condition](#44-admissibility-is-an-arithmetic-condition)
   - [Comparing two extensions across one cyclic layer](#45-comparing-two-extensions-across-one-cyclic-layer)
5. [Constructing the elementary packets](#5-constructing-the-elementary-packets)
   - [Descent selected by the extending representation](#51-descent-selected-by-the-extending-representation)
   - [Cuspidality and independence of the chain](#52-cuspidality-and-independence-of-the-chain)
   - [Conjugation compatibility](#53-conjugation-compatibility)
   - [What complete splitting preserves](#54-what-complete-splitting-preserves)
6. [The finite coefficient ledger](#6-the-finite-coefficient-ledger)
   - [Intrinsic fields and realization fields](#61-intrinsic-fields-and-realization-fields)
   - [Constructing, rather than assuming, the coefficient systems](#62-constructing-rather-than-assuming-the-coefficient-systems)
   - [Determinants and coefficient conjugation](#63-determinants-and-coefficient-conjugation)
   - [Field conjugation and coefficient conjugation](#64-field-conjugation-and-coefficient-conjugation)
   - [The rational and integral boundary](#65-the-rational-and-integral-boundary)
7. [Exact identities on every overlap field](#7-exact-identities-on-every-overlap-field)
   - [The admissible-tower identity](#71-the-admissible-tower-identity)
   - [The Frobenius-power comparison](#72-the-frobenius-power-comparison)
   - [The unconditional semisimple overlap theorem](#73-the-unconditional-semisimple-overlap-theorem)
   - [Conjugate intersections and the Hom-ready identity](#74-conjugate-intersections-and-the-hom-ready-identity)
   - [Why agreement only over the top is insufficient](#75-why-agreement-only-over-the-top-is-insufficient)
8. [The signed induced array](#8-the-signed-induced-array)
   - [Brauer characters and their Hecke avatars](#81-brauer-characters-and-their-hecke-avatars)
   - [The actual induced terms](#82-the-actual-induced-terms)
   - [Recovery of the chosen member](#83-recovery-of-the-chosen-member)
   - [Rank and determinant](#84-rank-and-determinant)
   - [Restriction back to the top field](#85-restriction-back-to-the-top-field)
   - [The Mackey Gram input](#86-the-mackey-gram-input)
9. [Frobenius powers and the common virtual polynomial](#9-frobenius-powers-and-the-common-virtual-polynomial)
   - [Power traces without choosing roots](#91-power-traces-without-choosing-roots)
   - [The local cyclic-block determinant](#92-the-local-cyclic-block-determinant)
   - [The algebraic signed Euler factor](#93-the-algebraic-signed-euler-factor)
   - [Polynomiality from the distinguished member](#94-polynomiality-from-the-distinguished-member)
   - [Purity and coefficient covariance](#95-purity-and-coefficient-covariance)
10. [Local records, especially the SP place](#10-local-records-especially-the-sp-place)
    - [Local Mackey decomposition](#101-local-mackey-decomposition)
    - [The common dyadic special object](#102-the-common-dyadic-special-object)
    - [The invariant line, sign, and conductor](#103-the-invariant-line-sign-and-conductor)
    - [Other finite places and the coefficient-prime boundary](#104-other-finite-places-and-the-coefficient-prime-boundary)
    - [Archimedean places](#105-archimedean-places)
11. [The exported packet-array package](#11-the-exported-packet-array-package)
    - [Complete statement](#111-complete-statement)
    - [Proof](#112-proof)
    - [Structural audit](#113-structural-audit)
    - [Dependency audit](#114-dependency-audit)
    - [Conclusion](#115-conclusion)

## 1. One finite packet array

### 1.1 The obstruction at the ground field

Let $M/\mathbf Q$ be a finite totally real Galois extension with group

$$
\Gamma=\operatorname{Gal}(M/\mathbf Q).
$$

Suppose a chosen two-dimensional representation of $G_{\mathbf Q}$ is automorphic after
restriction to $G_M$. If $\Gamma$ is nonsolvable, cyclic descent cannot move the top
automorphic representation directly to $\mathbf Q$. Inducing that top representation is not a
substitute: induction multiplies its dimension by $[M:\mathbf Q]$.

Brauer induction replaces the missing nonsolvable descent by a finite array. For an elementary
subgroup $H\leq\Gamma$, the upper extension $M/M^H$ is solvable. The top packet can therefore
be descended to the fixed field

$$
F_H=M^H
$$

provided the prime-cyclic steps lie in the proved transfer range. An integral character
identity then combines Galois inductions from the several $F_H$ with positive and negative
coefficients.

This strategy creates a new problem. The next character-norm calculation compares two induced
terms on fields

$$
M^{H\cap xJx^{-1}}=F_H\,x(F_J).
$$

Such a compositum is usually nonnormal over either smaller fixed field. Agreement of two
packet realizations after further restriction to $G_M$ is not enough: the two realizations can
differ on the intersection field by a character of the finite quotient. The central task of
this book is therefore not effectivity. It is to construct the finite elementary-subfield
packet array and to prove its exact semisimple identities on every one of these overlap fields.

### 1.2 The controlled-top datum

Fix a prime $\ell\geq7$, a finite extension $L_0/\mathbf Q_\ell$, and a continuous absolutely
irreducible representation

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(L_0)
\tag{1.1}
$$

with

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ unramified outside }\{2,\ell\}.
\tag{1.2}
$$

No lattice is part of the datum. We assume that $\rho|_{G_M}$ remains absolutely irreducible.
This one rational hypothesis implies the absolute irreducibility of
$\rho|_{G_{F'}}$ for every intermediate field $F'\subseteq M$, because an invariant line for
the larger group would also be invariant under $G_M$.

The extension $M/\mathbf Q$ is assumed totally real and Galois. The primes $2$ and $\ell$
split completely in $M$. More generally, any finite collection of sensitive places may be
required to split completely; all statements below then apply to it in the same way.

At $2$, the chosen representation has the SP local record. In the arithmetic-Frobenius
normalization its Frobenius-semisimple Weil--Deligne pair is

$$
\mathscr D_2=(r_2,N_2),
\qquad
N_2^2=0,
\qquad
N_2\ne0,
\qquad
\operatorname{rank}N_2=1,
\tag{1.3}
$$

with trivial finite inertia and

$$
r_2(F_2)N_2r_2(F_2)^{-1}=2N_2.
\tag{1.4}
$$

The line and sign are part of the label:

$$
\mathscr L_2=\ker N_2=\operatorname{im}N_2,
\tag{1.5}
$$

and, for one $\varepsilon_2\in\{1,-1\}$, arithmetic Frobenius acts on the quotient by
$\varepsilon_2$ and on $\mathscr L_2$ by $2\varepsilon_2$. Thus the label is the full special
pair, not merely its conductor.

Finally, assume there is a selected parallel-weight-two cuspidal automorphic representation
$\pi_M$ such that, for one algebraic coefficient embedding $\iota_0$ into
$\overline{\mathbf Q}_\ell$,

$$
r_{\pi_M,\iota_0}\simeq\rho|_{G_M}.
\tag{1.6}
$$

The word **selected** has an exact role. For every elementary $H\leq\Gamma$, the datum includes
at least one prime-cyclic chain from $M$ to $F_H$. Recursively at every downward step, the
current cusp form is selected and trace-comparable, its local extension fibers are
antecedent-complete selected, and the reverse comparison has a strongly cuspidal factor. The
source fiber is saturated under the finite quotient-character twists that can occur, so the
correction selected by $\rho$ remains selected and trace-comparable. These are precisely the
descent-admissibility and fiber-saturation conditions of the cyclic and solvable transfer
theorems; mere invariance of the packet is not being substituted for them.

Every corrected packet thereby obtained is also required to lie in the established
parallel-weight-two curve-attachment range, including its coefficient conjugates. At every
dyadic place its special comparison package is assumed uniformly: the raw packet monodromy has
rank one; Frobenius on the raw invariant graph line is the selected special scalar; and the raw
local pair agrees with the pair of the globally semisimplified realization at every coefficient
place away from residue characteristic two. These are respectively the special scalar and
local-preservation hypotheses isolated in Books 136--137. The return scalar and pair are
required to have one algebraic model before completion. Thus the later all-embedding SP record
is an exact attachment hypothesis, not an inference from the distinguished realization or from
conductor one.

We call (1.1)--(1.6), complete splitting, and these exact range hypotheses a
**controlled SP top datum**. The arithmetic problem of producing such a datum is prior to this
book. The theorem here begins once the chosen lift is already automorphic over the controlled
top.

### 1.3 The packet-array theorem

The endpoint is a finite algebraic array, not a base-field compatible family.

**Theorem 1.1 (finite elementary-packet array).** From a controlled SP top datum one can
construct, for every elementary subgroup $H\leq\Gamma$, a parallel-weight-two cuspidal packet
$\pi_H$ over $F_H=M^H$ with the following properties.

1. At the distinguished embedding,

   $$
   r_{H,\iota_0}\simeq\rho|_{G_{F_H}},
   \qquad
   \operatorname{BC}_{M/F_H}(\pi_H)\simeq\pi_M.
   \tag{1.7}
   $$

2. The packet is independent of the admissible prime-cyclic chain used to descend it and is
   compatible with conjugation in $\Gamma$.
3. There is one finite Galois number field $K$ containing the Hecke, realization, local-type,
   and finite-character fields of every packet in the array. For every coefficient embedding
   $\tau:K\hookrightarrow\Omega$ into an algebraically closed characteristic-zero
   nonarchimedean field, the packet theorem constructs a continuous semisimple realization

   $$
   r_{H,\tau}:G_{F_H}\longrightarrow\operatorname{GL}_2(\Omega).
   \tag{1.8}
   $$

4. For every $D\leq H$ with $D$ and $H$ elementary,

   $$
   r_{H,\tau}|_{G_{F_D}}^{\mathrm{ss}}simeq r_{D,\tau}
   \tag{1.9}
   $$

   for every $\tau$. This identity is proved even if no admissible automorphic base-change
   tower from $F_H$ to the nonnormal field $F_D$ is available.
5. There is one algebraic SP pair whose distinguished realization is (1.3)--(1.5). At every
   dyadic place and every coefficient embedding of residue characteristic different from two,
   the full local pair is a scalar extension of that algebraic pair. In particular its
   monodromy is nonzero of rank one, its invariant line and sign are retained, and its Artin
   conductor exponent is one.
6. For any integral Brauer relation for $1_\Gamma$, the twisted packet realizations give a
   signed induced class of virtual rank two and virtual determinant cyclotomic. At $\iota_0$
   it is exactly $[\rho]$. Its good Frobenius characteristic series is one algebraic quadratic
   polynomial, independent of the coefficient embedding.
7. For every pair of Brauer terms and every Mackey double coset, the two restrictions to the
   corresponding intersection field are twists of the same $r_{D,\tau}$. Their Hom space is
   therefore the self-twist space for one explicitly oriented quotient character.

Nothing in the theorem says that the signed class at a general $\tau$ is effective. It does
not produce a two-dimensional representation over $\mathbf Q$ at that embedding, a coherent
base-field compatible system, or an integral lattice.

### 1.4 Conventions and boundaries

Arithmetic Frobenius is used throughout. Thus

$$
\chi_\tau(\operatorname{Frob}_v)=q_v
$$

and a weight-two good polynomial is

$$
X^2-a_vX+q_v.
\tag{1.10}
$$

The reciprocal characteristic series is

$$
\det(1-\operatorname{Frob}_vT)=1-a_vT+q_vT^2.
\tag{1.11}
$$

Induction of Galois representations is unnormalized finite induction. Automorphic twisting by
a Hecke character is through the determinant. All global Galois representations used in
Grothendieck groups are semisimple. Local Weil--Deligne pairs are Frobenius semisimple; their
finite inertia and monodromy operator are retained.

Books 96--97 state their transfer ledger with geometric Frobenius. Whenever that ledger is used
here, Frobenius is inverted and the attached rank-two representation is put in the arithmetic
covariant normalization. Restriction of parameters, norm pullback, twisting, cuspidality, and
the admissibility conditions are unchanged by this translation; the displayed roots and the
monodromy return relation are translated once and then kept arithmetic.

Likewise, Books 135--137 first display the raw curve realization with geometric Frobenius.
Here $r_{H,\tau}$ denotes its covariant Tate realization. Thus its determinant is cyclotomic
times the arithmetic avatar of the inverse finite geometric multiplier, and its arithmetic
good polynomial is the corresponding covariant polynomial. Section 6.3 proves that this finite
multiplier is trivial for the selected packets, after which the formulas reduce to (1.10).

Three words are kept separate.

- A **packet system** is the coefficient system attached to one already existing automorphic
  packet over one field $F_H$.
- The **packet array** is the finite collection of these systems as $H$ varies.
- A **base-field compatible family** would be a collection of actual rank-two representations
  of $G_{\mathbf Q}$ indexed coherently by coefficient places. No such object is assumed or
  constructed here.

The distinction is especially important at the coefficient prime. A rational packet
realization may be de Rham or crystalline under an established comparison theorem, but no
stable lattice, finite-flat quotient, or integral projector is inferred in this volume.

### 1.5 The order of construction

The proof has six stages.

First, Chapters 2--3 prove the finite-group identities, including integral Brauer induction,
Mackey decomposition, Frobenius reciprocity, and the determinant transfer formula. Second,
Chapter 4 proves that every subgroup of an elementary group is reachable by a subnormal
prime-cyclic chain and separates this group fact from automorphic admissibility. Third,
Chapter 5 descends the top packet to every elementary fixed field, with the extending
representation $\rho$ selecting the correct twist at every layer.

Fourth, Chapter 6 applies the earlier packet attachment theorem separately to the finitely many
new packets and places them in one coefficient ledger. Fifth, Chapter 7 proves every overlap
identity. When an admissible ascent tower exists, the identity is automorphic. In all cases it
is proved semisimply by comparing algebraic residue-degree Frobenius polynomials of two already
existing packet realizations. Finally, Chapters 8--10 insert a Brauer relation and verify the
rank, determinant, Frobenius, conjugation, and SP local records needed by the next character-norm
argument.

## 2. Induction, restriction, and double cosets

The packet array will be substituted into an identity in a character ring. Before arithmetic
enters, every operation in that substitution must be fixed: which cosets are used, how
conjugation acts, where determinant signs occur, and which subgroup appears in a Hom space.

### 2.1 Virtual representations

Let $A$ be a characteristic-zero field and let $G$ be a finite group. The Grothendieck group
$R_A(G)$ is generated by finite-dimensional $A[G]$-modules with the relation

$$
[V\oplus W]=[V]+[W].
$$

After extension to a splitting field, Maschke's theorem makes the category semisimple and the
irreducible characters form an orthonormal basis. Hence the character map on $R_A(G)$ is
injective. A virtual class can have negative irreducible multiplicities; its dimension and
trace remain defined by additivity.

For actual representations $V,W$, put

$$
\langle V,W\rangle_G=\dim_A\operatorname{Hom}_G(V,W).
\tag{2.1}
$$

Over a splitting field this extends bilinearly to $R_A(G)$ and makes the irreducible classes
orthonormal. The next volume will use this form to test effectivity. Here we construct the exact
Mackey entries to which it will be applied.

The same Grothendieck notation is used for finite-dimensional continuous representations of a
profinite group. Only open subgroups occur in induction, so every coset set is finite.

### 2.2 Finite-index induction and the tensor identity

For an open subgroup $H\leq G$ and a continuous $H$-representation $W$, define

$$
\operatorname{Ind}_H^GW=A[G]\otimes_{A[H]}W.
\tag{2.2}
$$

Choosing left-coset representatives gives a direct sum of $[G:H]$ copies of $W$. The group
permutes the finitely many copies and acts inside each copy through $W$, so the induced action
is continuous and

$$
\dim\operatorname{Ind}_H^GW=[G:H]\dim W.
\tag{2.3}
$$

If $V$ is a $G$-representation, there is a natural projection formula

$$
V\otimes\operatorname{Ind}_H^GW
\simeq
\operatorname{Ind}_H^G(V|_H\otimes W).
\tag{2.4}
$$

An explicit map is

$$
v\otimes(g\otimes w)\longmapsto
g\otimes(g^{-1}v\otimes w).
\tag{2.5}
$$

If $h\in H$, the images of $v\otimes gh\otimes w$ and $v\otimes g\otimes hw$ agree by
the balancing relation. The inverse sends $g\otimes(v\otimes w)$ to
$gv\otimes(g\otimes w)$. This proves (2.4), for finite and profinite groups alike.

Induction is transitive. If $J\leq H\leq G$, then

$$
\operatorname{Ind}_H^G\operatorname{Ind}_J^HW
\simeq\operatorname{Ind}_J^GW,
\tag{2.6}
$$

through $g\otimes(h\otimes w)\mapsto gh\otimes w$. This is a statement about Galois or
finite-group induction. It does not assert the existence of an automorphic induction.

### 2.3 Frobenius reciprocity

Evaluation on $1\otimes W$ gives

$$
\operatorname{Hom}_G(\operatorname{Ind}_H^GW,V)
\simeq\operatorname{Hom}_H(W,V|_H).
\tag{2.7}
$$

Indeed, a $G$-map is sent to $w\mapsto f(1\otimes w)$. Conversely an $H$-map
$a:W\to V$ gives

$$
g\otimes w\longmapsto ga(w).
$$

The two constructions are inverse. At finite index, induction and coinduction agree because a
finite direct sum is also a finite direct product. Thus there is also a right-adjoint form

$$
\operatorname{Hom}_G(V,\operatorname{Ind}_H^GW)
\simeq\operatorname{Hom}_H(V|_H,W).
\tag{2.8}
$$

The two adjunctions are valid for the continuous finite-coset model without a finite-image
hypothesis on $V$ or $W$.

We shall also use semisimplicity across finite index.

**Lemma 2.1 (finite-index semisimplicity).** Let $N\triangleleft G$ be open. If
$V|_N$ is semisimple, then $V$ is semisimple. Conversely, the restriction of a semisimple
$G$-representation to any open subgroup is semisimple.

**Proof.** If $W\subseteq V$ is $G$-stable, choose an $N$-equivariant projection $p:V\to W$
and average its conjugates over $G/N$:

$$
p_G=\frac1{[G:N]}\sum_{g\in G/N}gpg^{-1}.
$$

It is a $G$-equivariant projection onto $W$, proving the first assertion.

For the converse, reduce to irreducible $V$ and let $N$ be the normal core of the given open
subgroup $H$. The $N$-socle of $V$ is nonzero and is $G$-stable, hence is all of $V$.
Therefore $V|_N$ is semisimple. Apply the averaging argument to $N\triangleleft H$ to conclude
that $V|_H$ is semisimple. Direct sums prove the general case. $\square$

### 2.4 Mackey decomposition

For $x\in G$ and an $H$-representation $W$, define the $xHx^{-1}$-representation
${}^xW$ by

$$
{}^xW(xhx^{-1})=W(h).
\tag{2.9}
$$

The map $g\otimes w\mapsto gx^{-1}\otimes{}^xw$ gives

$$
\operatorname{Ind}_{xHx^{-1}}^G({}^xW)
\simeq\operatorname{Ind}_H^GW.
\tag{2.10}
$$

Now let $H,J\leq G$ be open and choose representatives for $H\backslash G/J$.

**Theorem 2.2 (Mackey decomposition).** For a $J$-representation $W$,

$$
\operatorname{Res}_H^G\operatorname{Ind}_J^GW
\simeq
\bigoplus_{x\in H\backslash G/J}
\operatorname{Ind}_{H\cap xJx^{-1}}^H
({}^xW)|_{H\cap xJx^{-1}}.
\tag{2.11}
$$

**Proof.** Decompose the $(H,J)$-biset $G$ as the disjoint union of $HxJ$. Put
$D_x=H\cap xJx^{-1}$. On the summand belonging to $x$, the map

$$
A[H]\otimes_{A[D_x]}{}^xW
\longrightarrow A[HxJ]\otimes_{A[J]}W,
\qquad
h\otimes{}^xw\longmapsto hx\otimes w
\tag{2.12}
$$

is well defined. If $d=xjx^{-1}\in D_x$, then
$hdx\otimes w=hxj\otimes w=hx\otimes jw$. It is surjective, and the source and target have
the same finite dimension. Summing (2.12) proves the formula. The proof uses only finitely many
cosets and therefore also proves the profinite statement. $\square$

Combining (2.7), (2.11), and (2.8) gives the Hom form

$$
\begin{aligned}
&\operatorname{Hom}_G
(\operatorname{Ind}_H^GU,\operatorname{Ind}_J^GW)\\
&\quad\simeq
\bigoplus_{x\in H\backslash G/J}
\operatorname{Hom}_{H\cap xJx^{-1}}
(U|_{H\cap xJx^{-1}},{}^xW|_{H\cap xJx^{-1}}).
\end{aligned}
\tag{2.13}
$$

This is the precise formula needed by a character norm. Restriction merely to one common
normal subgroup would forget the quotient compatibility imposed in each summand of (2.13).

### 2.5 Fixed fields, composita, and completions

Let $M/\mathbf Q$ have group $\Gamma$ and put $F_H=M^H$. For subgroups $H,J\leq\Gamma$,
Galois correspondence gives

$$
M^{H\cap xJx^{-1}}=F_H\,x(F_J).
\tag{2.14}
$$

Indeed, the compositum is fixed by the intersection, and an automorphism fixing the compositum
lies in both subgroups. Distinct double cosets remain distinct Mackey summands even when the
resulting composita are abstractly isomorphic.

For a rational place $v$, choose a place $\widetilde v$ of $M$ and let
$\Delta_v\leq\Gamma$ be its decomposition group. The places $w$ of $F_H$ above $v$ are indexed
by

$$
\Delta_v\backslash\Gamma/H.
\tag{2.15}
$$

If $x$ represents the orbit, then inside $M_{\widetilde v}$ the completion is

$$
(F_H)_w\simeq M_{\widetilde v}^{\Delta_v\cap xHx^{-1}}.
\tag{2.16}
$$

Applying Mackey to a decomposition group gives

$$
\left.\operatorname{Ind}_{G_{F_H}}^{G_{\mathbf Q}}W\right|_{G_{\mathbf Q_v}}
\simeq
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{(F_H)_w}}^{G_{\mathbf Q_v}}
W|_{G_{(F_H)_w}}.
\tag{2.17}
$$

Equations (2.14) and (2.17) are two uses of the same double-coset theorem: the first governs
global overlaps, and the second governs local types and Euler factors.

### 2.6 Determinants of induced representations

Determinants retain a sign that rank calculations do not see. Let $W$ have dimension $d$.
For $g\in G$, decompose its permutation of $G/H$ into cycles. Multiplying the internal $H$-actions
around each cycle defines the transfer of the character $\det W$. A block determinant gives

$$
\det\operatorname{Ind}_H^GW
=\operatorname{sgn}_{G/H}^{\,d}\operatorname{Ver}_H^G(\det W).
\tag{2.18}
$$

To verify the formula, order a coset basis cycle by cycle. A cycle of length $m$ contributes a
block companion matrix. Its determinant is $(-1)^{d(m-1)}$ times the determinant of the
product around the cycle. Multiplying the signs over all cycles gives the sign of the coset
permutation to the $d$th power, and multiplying the internal products is the transfer.

If $\chi$ is already a character of $G$, then every cycle of length $m$ contributes
$\chi(g)^m$, so

$$
\operatorname{Ver}_H^G(\chi|_H)=\chi^{[G:H]}.
\tag{2.19}
$$

For a virtual class $[V]-[W]$, define its determinant line as
$\det V\otimes(\det W)^{-1}$. Thus (2.18) can be applied to a signed Brauer expression before
that expression is known to be effective.

## 3. Elementary groups and integral Brauer induction

The fixed fields that can be reached from the top by solvable descent must also be numerous
enough to generate the trivial character integrally. Brauer's theorem identifies the right
subgroups. Its integrality is indispensable: rational coefficients would require fractional
representations and fractional powers of Euler factors.

### 3.1 Elementary groups

For a prime $p$, a finite group $H$ is **$p$-elementary** if

$$
H=C\times P,
\tag{3.1}
$$

where $C$ is cyclic of order prime to $p$ and $P$ is a $p$-group. A group is
**elementary** if it is $p$-elementary for some $p$.

Every subgroup of an elementary group is elementary. Let $D\leq C\times P$. If
$d=(c,u)\in D$, coprimality of $|C|$ and $|P|$ provides exponents that extract $(c,1)$ and
$(1,u)$ as powers of $d$. Therefore

$$
D=(D\cap C)\times(D\cap P),
\tag{3.2}
$$

and $D\cap C$ is cyclic. In particular, every Mackey intersection of two elementary
subgroups is elementary.

Elementary groups are nilpotent: all their Sylow subgroups are normal and the group is their
direct product. Hence they are solvable. The converse fails; $S_3$ is solvable but not
elementary.

### 3.2 Monomiality

An irreducible character is **monomial** if it is induced from a linear character of a
subgroup.

**Lemma 3.1.** Every irreducible character of an elementary group is monomial.

**Proof.** An irreducible representation of $C\times P$ is $\alpha\otimes\tau$, with
$\alpha$ linear on $C$ and $\tau$ irreducible on $P$. We prove by induction on $|P|$ that
$\tau$ is monomial.

Quotient by the kernel of $\tau$; an inducing character on the quotient can later be pulled
back. We may therefore assume $\tau$ faithful. Schur's lemma makes $Z(P)$ act by scalars, and
faithfulness then makes $Z(P)$ cyclic. If $P$ is abelian, $\tau$ is linear. Otherwise choose
$xZ(P)$ of order $p$ in the nontrivial center of $P/Z(P)$ and put

$$
A=\langle x,Z(P)\rangle.
$$

Then $A$ is abelian, normal, and properly contains $Z(P)$. Choose a linear constituent
$\lambda$ of $\tau|_A$ and let $I$ be its stabilizer in $P$. The $\lambda$-isotypic space and
its translates give

$$
\tau\simeq\operatorname{Ind}_I^P\tau_0
\tag{3.3}
$$

for an irreducible $\tau_0$ of $I$. The stabilizer is proper. If $I=P$, the unique
$\lambda$-isotypic decomposition would make $A$ act by scalars. Then every commutator
$[P,A]$ would lie in the kernel of $\tau$, so faithfulness would force $A\subseteq Z(P)$,
a contradiction.

By induction, $\tau_0=\operatorname{Ind}_B^I\mu$ for a linear $\mu$. Transitivity gives
$\tau=\operatorname{Ind}_B^P\mu$. Finally,

$$
\alpha\otimes\tau
=\operatorname{Ind}_{C\times B}^{C\times P}(\alpha\otimes\mu),
$$

whose inducing character is linear. $\square$

### 3.3 The local projector and restriction criterion

Write $\mathbf Z_{(p)}$ for the localization of $\mathbf Z$ at the prime $(p)$. The
integrality proof begins with a projector onto $p$-elements.

**Lemma 3.2 ($p$-element projector).** Let $A$ be finite and let $P$ be a Sylow $p$-subgroup.
There is a $\mathbf Z_{(p)}$-linear combination of permutation characters induced from
$p$-subgroups whose value is one on $p$-elements and zero on all other elements.

**Proof.** Put $u=\operatorname{Ind}_P^A1$, the permutation character of $A/P$. If $a$ is
not a $p$-element, it fixes no coset. If $a$ is a $p$-element, $\langle a\rangle$ acts on
$A/P$, whose cardinality is prime to $p$. Nontrivial orbits have cardinality divisible by
$p$, so

$$
u(a)=|(A/P)^{\langle a\rangle}|
\equiv[A:P]\not\equiv0\pmod p.
$$

Let $b_1,\ldots,b_s$ be the distinct nonzero values of $u$ on $p$-elements and set

$$
Q(X)=1-\prod_{j=1}^s(1-X/b_j).
\tag{3.4}
$$

Every $b_j$ is a unit in $\mathbf Z_{(p)}$, $Q(0)=0$, and $Q(b_j)=1$. The character $u^m$
is the permutation character of $(A/P)^m$. Its point stabilizers are intersections of
conjugates of $P$, hence $p$-groups. Expanding $Q(u)$ proves the claim. $\square$

**Theorem 3.3 (Brauer restriction criterion).** Let $\varphi$ be a rational linear
combination of irreducible characters of a finite group $G$. Then $\varphi$ is a generalized
character if and only if $\varphi|_E$ is a generalized character for every elementary
subgroup $E\leq G$.

**Proof.** Only the converse requires proof. Write

$$
\varphi=\sum_{\chi\in\operatorname{Irr}(G)}a_\chi\chi,
\qquad a_\chi\in\mathbf Q.
$$

It suffices to prove $a_\chi\in\mathbf Z_{(p)}$ for every rational prime $p$, since the
intersection of these localizations is $\mathbf Z$.

Fix $p$. Every $g\in G$ has a unique commuting decomposition $g=su$, where $s$ has order
prime to $p$ and $u$ has $p$-power order. Partition the inner product
$a_\chi=\langle\varphi,\chi\rangle_G$ by the conjugacy class of $s$. If
$A=C_G(s)$, the contribution of this $p$-section is

$$
\frac1{|A|}
\sum_{\substack{u\in A\\u\text{ a }p\text{-element}}}
\varphi(su)\chi((su)^{-1}).
\tag{3.5}
$$

By Lemma 3.2, the indicator of the $p$-elements of $A$ is

$$
\sum_Qc_Q\operatorname{Ind}_Q^A1,
\qquad c_Q\in\mathbf Z_{(p)},
\tag{3.6}
$$

where $Q$ runs through $p$-subgroups. Expanding the induced character and changing
$u$ to $xqx^{-1}$ gives for the $Q$-term

$$
\frac{c_Q}{|Q|}\sum_{q\in Q}
\varphi(sq)\chi((sq)^{-1}).
\tag{3.7}
$$

There is no remaining factor $|A|^{-1}$: the sum over $x\in A$ cancels it because the
function in (3.5) is invariant under conjugation by $A$.

Put $C=\langle s\rangle$. Since $C$ centralizes $Q$ and $|C|$ is prime to $p$, Fourier
inversion on $C$ expresses evaluation at $s$ as

$$
\mathbf1_{\{s\}}(t)
=\frac1{|C|}\sum_{\alpha\in\widehat C}\alpha(ts^{-1}).
\tag{3.8}
$$

Insert (3.8) into (3.7). The factor $|C|^{-1}|Q|^{-1}$ becomes the normalization of the
character inner product on $C\times Q$. With $\alpha$ inflated from $C$ to $C\times Q$, the
exact identity is

$$
c_Q\sum_{\alpha\in\widehat C}\alpha(s)
\left\langle
\varphi|_{C\times Q},
\chi|_{C\times Q}\otimes\alpha
\right\rangle_{C\times Q}.
\tag{3.9}
$$

The group $C\times Q$ is elementary. Its restriction of $\varphi$ is a generalized
character by hypothesis, so the inner product in (3.9) is an integer. Let $L$ be a cyclotomic
field containing all character values and let $\mathfrak p\mid p$. The external coefficients
in (3.9) are $p$-integral: $c_Q\in\mathbf Z_{(p)}$ and the remaining factors are roots of
unity. Hence every section contribution lies in $\mathcal O_{L,\mathfrak p}$ for every
$\mathfrak p\mid p$.

The sum of the sections is the rational number $a_\chi$. Therefore

$$
a_\chi\in
\mathbf Q\cap\bigcap_{\mathfrak p\mid p}\mathcal O_{L,\mathfrak p}
=\mathbf Z_{(p)}.
$$

This holds for every $p$, so $a_\chi\in\mathbf Z$. The forward implication is immediate from
restriction. $\square$

The proof deliberately used permutation characters for the $p$-part. Linear characters of a
nonabelian $p$-group do not separate all of its elements, so Fourier inversion on that group
would not prove the criterion.

### 3.4 The integral relation

Let $R(G)$ be the integral character lattice and let $X\subseteq R(G)$ be generated by

$$
\operatorname{Ind}_H^G\theta
$$

with $H$ elementary and $\theta$ linear.

**Theorem 3.4 (integral Brauer induction).** One has $X=R(G)$. In particular, there are
elementary subgroups $H_i$, linear characters $\theta_i$, and integers $n_i$ such that

$$
\boxed{
1_G=\sum_{i=1}^t n_i\operatorname{Ind}_{H_i}^G\theta_i.}
\tag{3.10}
$$

**Proof.** Define

$$
X^\vee=
\{\varphi\in R(G)\otimes\mathbf Q:
\langle\varphi,x\rangle_G\in\mathbf Z\text{ for every }x\in X\}.
$$

Take $\varphi\in X^\vee$. If $H$ is elementary and $\xi$ is irreducible on $H$, Lemma 3.1
writes $\xi=\operatorname{Ind}_D^H\theta$ for a linear character on a subgroup $D\leq H$.
By (3.2), $D$ is elementary. Frobenius reciprocity and transitivity give

$$
\langle\varphi|_H,\xi\rangle_H
=\langle\varphi,\operatorname{Ind}_D^G\theta\rangle_G
\in\mathbf Z.
$$

Thus every elementary restriction of $\varphi$ is a generalized character. Theorem 3.3 gives
$\varphi\in R(G)$, so $X^\vee=R(G)$. The irreducible basis makes $R(G)$ self-dual. A proper
full-rank sublattice has a strictly larger dual, and a lower-rank subgroup has a non-discrete
dual inside $R(G)\otimes\mathbf Q$. Hence $X=R(G)$. Applying this to $1_G$ proves (3.10).
$\square$

Evaluation at the identity gives the rank identity

$$
\sum_i n_i[G:H_i]=1.
\tag{3.11}
$$

Tensoring (3.10) with any $G$-representation $V$ and applying (2.4) gives

$$
[V]=\sum_i n_i
\left[\operatorname{Ind}_{H_i}^G(V|_{H_i}\otimes\theta_i)\right].
\tag{3.12}
$$

This is the formal identity that recovers $\rho$ at the distinguished coefficient embedding.

### 3.5 A diagnostic relation

For $G=S_3$, let $C_2$ be generated by a transposition, let $C_3=A_3$, and let $\omega$ be a
nontrivial character of $C_3$. On the conjugacy classes represented by
$1,(12),(123)$,

$$
\operatorname{Ind}_{C_2}^{S_3}1=(3,1,0),
\qquad
\operatorname{Ind}_{C_3}^{S_3}\omega=(2,0,-1).
$$

Therefore

$$
1_{S_3}
=\operatorname{Ind}_{C_2}^{S_3}1
-\operatorname{Ind}_{C_3}^{S_3}\omega.
\tag{3.13}
$$

After tensoring by a rank-two representation, the positive term has dimension six and the
negative term dimension four. Their signed dimension is two, but this does not prove that the
four-dimensional term is a direct summand of the six-dimensional term. The example separates
the present virtual construction from the later effectivity theorem.

## 4. Prime-cyclic towers inside elementary groups

Brauer's theorem produces elementary subgroups, while Mackey produces their arbitrary
intersections. To move automorphic data between the associated fixed fields one needs more than
solvability of the endpoint group: one needs an actual sequence of normal inclusions whose
quotients are cyclic of prime order.

### 4.1 The normalizer condition

**Lemma 4.1.** If $D$ is a proper subgroup of a finite nilpotent group $H$, then

$$
D<N_H(D).
\tag{4.1}
$$

**Proof.** Write $H=\prod_pH_p$ as the direct product of its Sylow subgroups. Taking primary
parts of elements gives $D=\prod_pD_p$, where $D_p=D\cap H_p$. Choose $p$ with
$D_p<H_p$.

Let $D_p$ act by left multiplication on $H_p/D_p$. Its fixed cosets are exactly
$N_{H_p}(D_p)/D_p$. Orbit counting gives

$$
[H_p:D_p]\equiv[N_{H_p}(D_p):D_p]\pmod p.
$$

The left side is divisible by $p$. The right side counts at least the identity coset, so it
cannot equal one; hence $N_{H_p}(D_p)>D_p$. An element in this larger normalizer, placed in the
$p$-factor of $H$, commutes with all other Sylow factors and normalizes $D$. It is not in $D$.
$\square$

### 4.2 Subnormal prime-cyclic refinement

**Proposition 4.2.** If $D\leq H$ and $H$ is elementary, there is a chain

$$
D=D_0\triangleleft D_1\triangleleft\cdots\triangleleft D_m=H
\tag{4.2}
$$

in which every quotient $D_{j+1}/D_j$ is cyclic of prime order.

**Proof.** An elementary group is nilpotent. Repeatedly replace a proper subgroup by its
normalizer. Lemma 4.1 gives a strictly increasing subnormal chain terminating at $H$. For one
normal inclusion $A\triangleleft B$ in this chain, the quotient $B/A$ is a quotient of a
nilpotent group and is therefore solvable. Refine it by a composition series. Every simple
factor of a finite solvable group is cyclic of prime order. Pulling the composition series back
to $B$ and performing this refinement for every normalizer step proves (4.2). $\square$

The word subnormal is exact. The original $D$ need not be normal in $H$; normality is asserted
only one adjacent step at a time.

### 4.3 The reversed fixed-field tower

Put $F_A=M^A$. Reversing (4.2) gives

$$
F_H=F_{D_m}\subset F_{D_{m-1}}\subset\cdots\subset F_{D_0}=F_D.
\tag{4.3}
$$

Because $D_j\triangleleft D_{j+1}$,

$$
F_{D_j}/F_{D_{j+1}}
$$

is cyclic Galois with group $D_{j+1}/D_j$, hence has prime degree. Thus the possibly
nonnormal extension $F_D/F_H$ is an exhibited composite of prime-cyclic Galois layers.

For descent from $M$ to $F_H$, start instead from a chain

$$
1=H_0\triangleleft H_1\triangleleft\cdots\triangleleft H_s=H.
\tag{4.4}
$$

Then

$$
M=F_{H_0}\supset F_{H_1}\supset\cdots\supset F_{H_s}=F_H,
\tag{4.5}
$$

and $F_{H_j}/F_{H_{j+1}}$ is cyclic Galois of prime degree. The directions in (4.3) and
(4.5) are opposite because the former is used for base change from $F_H$ up to an overlap,
while the latter is used to descend the top packet.

### 4.4 Admissibility is an arithmetic condition

Proposition 4.2 proves that the fields in (4.3) exist. It does not prove that automorphic base
change is available at every layer. A tower is **ascent-admissible** for a packet when, at every
upward step, the selected local extension-complete range, cohomological archimedean range, and
strongly cuspidal selector required by cyclic base change are present. It is
**descent-admissible** when, at every downward step, the upper cusp form is selected and
trace-comparable, all of its local norm-antecedent fibers are antecedent-complete selected, and
the reverse comparison has a strongly cuspidal factor. In the construction below we also
require fiber saturation under the finite quotient-character group, because the correction
selected after one arbitrary descent must remain inside the admitted packet range.

Complete splitting of a sensitive rational prime in $M$ makes every local extension at that
prime trivial throughout the tower. This verifies the local restriction at that prime, but it
does not by itself prove the global trace-selector hypotheses or admissibility at other places.
Accordingly, we use the following rule.

- The packet $\pi_H$ is constructed only along a descent-admissible chain supplied by the
  controlled datum.
- An automorphic identity between $\pi_H$ and $\pi_D$ is asserted only when an
  ascent-admissible chain (4.3) is available.
- The semisimple Galois overlap needed for Mackey theory is proved separately in Chapter 7 and
  therefore does not depend on automorphic admissibility of the nonnormal composite.

This separation is what prevents a group-theoretic tower from being mistaken for a transfer
theorem.

### 4.5 Comparing two extensions across one cyclic layer

The chosen representation $\rho$ selects the correct point in each cyclic descent fiber.

**Lemma 4.3 (extension comparison).** Let $N\triangleleft G$ with finite cyclic quotient, and
work over an algebraically closed characteristic-zero field. Let $V$ and $V'$ be
finite-dimensional irreducible representations of $G$ whose restrictions to $N$ are
irreducible and isomorphic. Then

$$
V'\simeq V\otimes\eta
\tag{4.6}
$$

for a character $\eta$ of $G/N$.

**Proof.** The line $\operatorname{Hom}_N(V,V')$ is one-dimensional by Schur's lemma. The
group $G$ acts on it by

$$
(g\cdot f)=V'(g)fV(g)^{-1}.
$$

Elements of $N$ act trivially because $f$ is $N$-equivariant. Thus the action is a character
$\eta$ of $G/N$. A nonzero $f$ satisfies
$V'(g)f=\eta(g)fV(g)$, which is exactly an intertwiner between $V'$ and
$V\otimes\eta$. $\square$

The same proof works for absolute Galois groups of a cyclic extension. Global class field
theory identifies $\eta$ with a finite-order Hecke character killed by base change to the
upper field. This is the correction used in the next chapter.

## 5. Constructing the elementary packets

We now descend the one top packet separately through every elementary subgroup. The extending
representation $\rho$ supplies coherence which the abstract automorphic descent torsors would
not possess on their own.

### 5.1 Descent selected by the extending representation

Fix an elementary $H\leq\Gamma$ and a descent-admissible chain (4.4). Put
$K_j=F_{H_j}$, so $K_0=M$ and $K_s=F_H$. We construct a cuspidal packet $\pi_j$ over $K_j$
such that

$$
r_{\pi_j,\iota_0}\simeq\rho|_{G_{K_j}}.
\tag{5.1}
$$

Start with $\pi_0=\pi_M$. Suppose $\pi_j$ has been constructed. It is invariant under
$\operatorname{Gal}(K_j/K_{j+1})$. Indeed, conjugating (5.1) by a lift in $G_{K_{j+1}}$
gives an isomorphic representation: the intertwiner is the corresponding matrix of $\rho$.
Thus $\pi_j$ and its conjugate have equal good Hecke polynomials, and strong multiplicity one
identifies them.

The prime-cyclic descent theorem supplies a cuspidal descent $\pi_{j+1}^0$ over $K_{j+1}$.
Its distinguished Galois realization and $\rho|_{G_{K_{j+1}}}$ have isomorphic restrictions
to $G_{K_j}$. Those restrictions are absolutely irreducible because they contain
$\rho|_{G_M}$. Lemma 4.3 gives a finite character $\eta_j$ of
$\operatorname{Gal}(K_j/K_{j+1})$ such that

$$
r_{\pi_{j+1}^0,\iota_0}
\simeq\rho|_{G_{K_{j+1}}}\otimes\eta_j.
$$

Let the same symbol denote its finite-order Hecke avatar and set

$$
\pi_{j+1}=\pi_{j+1}^0\otimes\eta_j^{-1}.
\tag{5.2}
$$

Compatibility of twisting with Galois realization proves (5.1) at the next layer.
The character $\eta_j$ is killed by restriction to $G_{K_j}$, so base change of (5.2) is
still $\pi_j$. Fiber saturation in the controlled datum guarantees that (5.2) remains in the
selected range. Induction on $j$ constructs $\pi_H=\pi_s$ and proves
$\operatorname{BC}_{M/F_H}(\pi_H)\simeq\pi_M$.

### 5.2 Cuspidality and independence of the chain

Every packet produced in Chapter 5 is cuspidal because the prime-cyclic descent theorem starts
from a cuspidal invariant packet and produces a cuspidal descent. There is also an arithmetic
check. A two-character isobaric representation would have reducible semisimple Galois
realization, while (5.1) is absolutely irreducible.

Suppose two admissible chains produce endpoints $\pi_H$ and $\pi_H'$. At the distinguished
embedding both have realization $\rho|_{G_{F_H}}$. Their good Hecke polynomials therefore
agree outside a finite set. Strong multiplicity one gives

$$
\pi_H\simeq\pi_H'.
\tag{5.3}
$$

Thus the packet is independent of the chain as an automorphic isomorphism class. No coherent
choice of the intermediate intertwiners is asserted or needed.

The same reasoning proves uniqueness among all selected descents satisfying (1.7). A descent
of $\pi_M$ can differ from $\pi_H$ by a finite quotient character, but requiring its
distinguished realization to be the literal restriction of $\rho$ selects one point of that
twisting fiber, modulo genuine self-twists which do not change the packet isomorphism class.

### 5.3 Conjugation compatibility

Let $x\in\Gamma$. Conjugation transports $F_H$ to

$$
x(F_H)=F_{xHx^{-1}}.
$$

The conjugate packet ${}^x\pi_H$ has distinguished realization

$$
{}^x(\rho|_{G_{F_H}})simeq\rho|_{G_{x(F_H)}}.
$$

The isomorphism again comes from the matrix $\rho(\widetilde x)$ for a lift
$\widetilde x\in G_{\mathbf Q}$. By uniqueness (5.3),

$$
\boxed{{}^x\pi_H\simeq\pi_{xHx^{-1}}.}
\tag{5.4}
$$

Changing the lift of $x$ conjugates by an element of $G_M$ and does not change the isomorphism
class. Equation (5.4) is field conjugation: it moves the base field and its places. It does not
apply an automorphism to Hecke eigenvalues.

### 5.4 What complete splitting preserves

If a rational prime $v$ splits completely in $M$, its decomposition group in $\Gamma$ is
trivial. It therefore splits completely in every $F_H$, and every completion $(F_H)_w$ above
$v$ is canonically isomorphic to $\mathbf Q_v$ after a compatible choice of places.

At such a place, every quotient character used in (5.2) is locally trivial: it factors through
a subgroup of $\Gamma$, while the local decomposition group has trivial image. Cyclic descent
therefore neither twists nor restricts the local parameter. All $\pi_H$ have the same local
component as $\pi_M$ at the corresponding places.

In particular, the dyadic component of every $\pi_H$ is the selected special component with
the same sign $\varepsilon_2$. It is not identified merely because its conductor equals one;
complete splitting retains the whole local Weil--Deligne parameter and the named Frobenius
line.

## 6. The finite coefficient ledger

The packet array is finite, but its members initially come with different Hecke fields and
different choices of embeddings. A character-norm calculation can compare them only after
those choices have been put into one algebraic ledger.

### 6.1 Intrinsic fields and realization fields

For each elementary $H$, let $E_H^{\mathrm{good}}$ be the field generated by the good Hecke
polynomials of $\pi_H$. The center of the full selected packet block can be larger, and a field
over which its Galois multiplicity representation is defined can be larger still because a
central simple algebra may need to be split. The finite local-type data can require another
finite extension.

There are only finitely many subgroups of $\Gamma$. For every $H$, regard its packet and
realization fields as actual subfields of $\overline{\mathbf Q}_\ell$ through the algebraic
embedding singled out by (5.1), and take their compositum in that fixed algebraic closure.
Adjoin:

- every good-polynomial field;
- every packet center and one finite splitting field for its selected simple factor;
- every finite local-type and central-character value;
- the values of every cyclic correction character used in Chapter 5 and every linear
  character of every elementary subgroup of $\Gamma$; and
- the same data for every elementary intersection subgroup.

The resulting compositum is a number field. Taking its normal closure inside the fixed
algebraic closure gives one finite Galois field $K/\mathbf Q$ and preserves the simultaneous
distinguished embeddings. Write the resulting inclusion as

$$
\iota_0:K\hookrightarrow\overline{\mathbf Q}_\ell
\tag{6.1}
$$

extending all distinguished packet embeddings. The field $K$ is a common container, not a
minimal trace field.

### 6.2 Constructing, rather than assuming, the coefficient systems

Apply the established weight-two packet attachment theorem separately to each automorphic
packet $\pi_H$. In the arithmetic covariant normalization, it constructs for every finite
place of a suitable realization field a rank-two semisimple Galois representation. After the
common enlargement to $K$, an embedding

$$
\tau:K\hookrightarrow\Omega
\tag{6.2}
$$

into an algebraically closed characteristic-zero nonarchimedean field gives

$$
r_{H,\tau}:G_{F_H}\longrightarrow\operatorname{GL}_2(\Omega).
\tag{6.3}
$$

At almost every finite place $w$ of $F_H$, this representation is unramified and its arithmetic
Frobenius polynomial is the $\tau$-image of the algebraic Hecke polynomial of $\pi_H$.
Coefficient enlargement and a different display of the same completion give scalar extensions
of the same member.

This is a construction from each $\pi_H$, not an assumption that $\rho$ already belongs to a
compatible system. Nor have the representations (6.3) been assembled into a system on
$G_{\mathbf Q}$. They live on different Galois groups and are linked only by the identities
proved below.

The distinguished member satisfies

$$
r_{H,\iota_0}\simeq\rho|_{G_{F_H}}
\tag{6.4}
$$

after one finite scalar extension. We suppress that harmless common extension in the notation.

### 6.3 Determinants and coefficient conjugation

The packet theorem expresses the determinant of $r_{H,\tau}$ as cyclotomic times the
$\tau$-adic avatar of an algebraic finite central multiplier $\eta_H$:

$$
\det r_{H,\tau}=\chi_\tau\eta_{H,\tau}.
\tag{6.5}
$$

At $\iota_0$, equations (6.4) and (1.2) give $\eta_{H,\iota_0}=1$ as a Galois character.
The values of $\eta_H$ are algebraic roots of unity and $\iota_0$ is injective. Therefore
$\eta_H=1$ before completion. Hence

$$
\boxed{\det r_{H,\tau}=\chi_\tau|_{G_{F_H}}}
\tag{6.6}
$$

for every $H$ and every $\tau$. This proves determinant compatibility algebraically; it is not
an inference from the constant term of one unramified polynomial.

Let $\sigma\in\operatorname{Gal}(K/\mathbf Q)$. Coefficient conjugation sends the good
polynomial $P_{H,w}(X)$ to $\sigma P_{H,w}(X)$ and the packet to its coefficient conjugate
$\pi_H^\sigma$. The attached realizations satisfy

$$
r_{\pi_H^\sigma,\tau}
\simeq r_{H,\tau\circ\sigma}
\tag{6.7}
$$

after scalar extension. Every central value and local-type scalar is conjugated at the same
time. Equation (6.6) is fixed because the cyclotomic character has rational values.

### 6.4 Field conjugation and coefficient conjugation

Field conjugation by $x\in\Gamma$ and coefficient conjugation by $\sigma$ act on different
coordinates of the array. Equation (5.4) and functoriality of attachment give

$$
r_{xHx^{-1},\tau}
\simeq{}^x r_{H,\tau}
\tag{6.8}
$$

as representations of $G_{x(F_H)}$. Coefficient conjugation leaves $F_H$ fixed and changes
the eigenvalues as in (6.7). Applying the two operations in either order gives the same
algebraic good polynomials, hence the same semisimple realization. Thus they commute on
isomorphism classes.

No based intertwiner satisfying a cocycle condition is chosen. Mackey theory and the later Hom
calculation need only the isomorphism classes and the dimensions of their Hom spaces.

### 6.5 The rational and integral boundary

The construction through this chapter is entirely characteristic zero. At the distinguished
embedding we remember the isomorphism (6.4), but no stable lattice is included in the input or
output. At a general coefficient embedding we do not compare reductions, finite-flat models,
or integral monodromy classes.

This boundary is structural. A rational packet projector can have denominators, a rational
direct summand need not meet an ambient module in a saturated summand, and semisimple
characteristic-zero cancellation can fail after reduction. None of these questions is needed
to prove the overlap identities or the next characteristic-zero effectivity theorem.

## 7. Exact identities on every overlap field

This chapter closes the delicate part of the construction. We distinguish an automorphic
overlap obtained by actual base change from a semisimple Galois overlap obtained by recognition.
The second is what the Mackey norm needs and is proved for every elementary intersection.

### 7.1 The admissible-tower identity

Let $D\leq H$ be elementary. Suppose the tower (4.3) is ascent-admissible for $\pi_H$. Iterated
prime-cyclic base change then exists. Its distinguished realization is

$$
r_{H,\iota_0}|_{G_{F_D}}
\simeq\rho|_{G_{F_D}}.
$$

The endpoint is cuspidal. If an intermediate base change were a two-character isobaric sum,
its semisimple Galois realization would be reducible, whereas the restriction of $\rho$ remains
absolutely irreducible. The selected endpoint and $\pi_D$ have the same distinguished
realization, so strong multiplicity one gives

$$
\boxed{
\operatorname{BC}_{F_D/F_H}(\pi_H)\simeq\pi_D.}
\tag{7.1}
$$

Compatibility of packet realizations with prime-cyclic base change then gives

$$
r_{H,\tau}|_{G_{F_D}}^{\mathrm{ss}}simeq r_{D,\tau}
\tag{7.2}
$$

for every $\tau$. The endpoint is independent of the admissible chain because every such
endpoint is $\pi_D$.

Equation (7.1) is not asserted if one of the cyclic steps leaves the selected transfer range.
The group chain still exists, but the automorphic arrow has not been constructed.

### 7.2 The Frobenius-power comparison

The semisimple identity (7.2) can be proved without (7.1). This is essential for a nonnormal
overlap whose group-theoretic tower is not known to be automorphically admissible.

Let $u$ be a finite place of $F_D$ above a place $w$ of $F_H$. Suppose $r_{H,\tau}$ is
unramified at $w$ and write its algebraic polynomial as

$$
P_{H,w}(X)=X^2-a_{H,w}X+b_{H,w}.
\tag{7.3}
$$

Put $f=f(u/w)$. If $\alpha,\beta$ are its roots, restriction to $G_{F_D}$ has roots
$\alpha^f,\beta^f$ at $u$. Define polynomials $A_f(a,b)$ by

$$
A_0=2,
\qquad A_1=a,
\qquad A_f=aA_{f-1}-bA_{f-2}\quad(f\geq2).
\tag{6.4b}
$$

Then $A_f(a,b)=\alpha^f+\beta^f$, so the restricted polynomial is

$$
P_{H,w}^{[f]}(X)
=X^2-A_f(a_{H,w},b_{H,w})X+b_{H,w}^{\,f}.
\tag{6.4c}
$$

Formula (6.4b) proves that (6.4c) lies in the original coefficient field without choosing the
roots. The residue degree, not the ramification index or the global degree, is the exponent.

At $\iota_0$, both $r_{H,\iota_0}|_{G_{F_D}}$ and $r_{D,\iota_0}$ are the actual
representation $\rho|_{G_{F_D}}$. Therefore, at every place outside one finite set,

$$
\iota_0(P_{H,w}^{[f]}(X))
=\iota_0(P_{D,u}(X)).
\tag{7.6}
$$

Both polynomials have coefficients in $K$, and $\iota_0$ is injective. Hence

$$
P_{H,w}^{[f]}(X)=P_{D,u}(X)
\quad\text{in }K[X].
\tag{6.4d}
$$

Applying any $\tau$ gives equality of the characteristic polynomials of the two existing
semisimple representations at almost every $u$.

### 7.3 The unconditional semisimple overlap theorem

The next proposition retains the interface number used by the succeeding character-norm
theorem. Its proof belongs here, after the coefficient ledger and the Frobenius-power
calculation; the stable number is not an assertion that the proof occurred earlier.

**Proposition 6.2 (elementary overlap; stable interface label).** For every inclusion
$D\leq H$ of elementary subgroups and every coefficient embedding $\tau$,

$$
\boxed{
r_{H,\tau}|_{G_{F_D}}^{\mathrm{ss}}simeq r_{D,\tau}.}
\tag{6.4a}
$$

This holds whether or not an ascent-admissible automorphic tower from $F_H$ to $F_D$ has been
verified.

**Proof.** Lemma 2.1 shows that the restriction on the left is semisimple. By (6.4d), the two
representations have equal characteristic polynomials at all finite places outside one finite
set. The prior density theorem says that these arithmetic Frobenius conjugacy classes are dense
in $G_{F_D}$. Their trace functions are continuous, so the traces agree on all of $G_{F_D}$.

For completeness, Brauer--Nesbitt applies as follows. Let $B$ be the finite-dimensional algebra
generated by the image of $G_{F_D}$ in the endomorphisms of the direct sum of the two
representations. After scalar extension, its semisimple quotient is a product of matrix
algebras. The trace of a central idempotent in one factor is its simple dimension times the
multiplicity of that simple module. Equality of trace functionals on group elements extends
linearly to $B$, so all simple multiplicities agree. The two semisimple representations are
isomorphic. $\square$

The proof recognizes two representations that already exist over $F_D$. It neither constructs
an effective base-field representation nor assumes a compatible family for $\rho$. No
integral comparison is made.

Because (6.4a) is a global isomorphism over $G_{F_D}$, its restriction to every decomposition
group is an isomorphism as well. Away from the coefficient residue characteristic, the
associated Frobenius-semisimple Weil--Deligne pairs therefore agree with their finite inertia
and monodromy operators intact. This bad-place compatibility is a consequence of the global
recognition theorem applied to already attached representations; it is not reconstructed from
the good polynomials used in the proof. At the coefficient residue characteristic, only the
characteristic-zero local Galois isomorphism is asserted here.

### 7.4 Conjugate intersections and the Hom-ready identity

Let $H,J\leq\Gamma$ be elementary and let $x\in\Gamma$. Put

$$
D_x=H\cap xJx^{-1},
\qquad
L_x=M^{D_x}=F_H\,x(F_J).
\tag{7.9}
$$

The subgroup $D_x$ is elementary. Apply Proposition 6.2 to $D_x\leq H$ and, after conjugation, to
$D_x\leq xJx^{-1}$. Equation (6.8) gives

$$
\boxed{
r_{H,\tau}|_{G_{L_x}}^{\mathrm{ss}}
\simeq r_{D_x,\tau}
\simeq{}^xr_{J,\tau}|_{G_{L_x}}^{\mathrm{ss}}.}
\tag{6.4e}
$$

Now let $\theta:H\to K^\times$ and $\eta:J\to K^\times$ be finite linear characters. On
$D_x$ define

$$
\alpha_x=\theta|_{D_x},
\qquad
\beta_x=({}^x\eta)|_{D_x},
\qquad
\delta_x=\beta_x\alpha_x^{-1}.
\tag{6.4f}
$$

Here the three characters are inflated through $G_{L_x}\twoheadrightarrow D_x$ and then
transported by $\tau$. Restoring the twists in (6.4e) gives

$$
\begin{aligned}
\left((r_{H,\tau}\otimes\theta_\tau)|_{G_{L_x}}\right)^{\mathrm{ss}}
&\simeq r_{D_x,\tau}\otimes\alpha_{x,\tau},\\
\left({}^x(r_{J,\tau}\otimes\eta_\tau)|_{G_{L_x}}\right)^{\mathrm{ss}}
&\simeq r_{D_x,\tau}\otimes\beta_{x,\tau}\\
&\simeq
(r_{D_x,\tau}\otimes\alpha_{x,\tau})\otimes\delta_{x,\tau}.
\end{aligned}
\tag{6.4g}
$$

Tensoring both Hom arguments by $\alpha_x^{-1}$ gives

$$
\begin{aligned}
&\operatorname{Hom}_{G_{L_x}}
((r_{H,\tau}\otimes\theta_\tau)|_{G_{L_x}},
{}^x(r_{J,\tau}\otimes\eta_\tau)|_{G_{L_x}})\\
&\qquad\simeq
\operatorname{Hom}_{G_{L_x}}
(r_{D_x,\tau},r_{D_x,\tau}\otimes\delta_{x,\tau}).
\end{aligned}
\tag{6.4h}
$$

The isomorphism depends on choices of the two overlap intertwiners, but its dimension does not.
The orientation of the quotient character is fixed: it is target twist divided by source twist,
$\beta_x\alpha_x^{-1}$.

### 7.5 Why agreement only over the top is insufficient

If two irreducible representations of $G_{L_x}$ become isomorphic on $G_M$, Lemma 4.3 shows
that they can differ by a character of

$$
G_{L_x}/G_M\simeq D_x.
$$

Such a character changes the Hom space in (6.4h). Restricting every induced term directly to
$G_M$ therefore erases exactly the information needed by the Mackey Gram matrix.

Proposition 6.2 removes that ambiguity on $G_{L_x}$ itself. When automorphic ascent is admissible,
equation (7.1) gives the stronger packet identity. When it is not, the algebraic
Frobenius-power proof still gives the exact semisimple identity required for effectivity. The
two routes have been separated rather than silently equated.

## 8. The signed induced array

We may now insert one integral Brauer relation. Every summand is an actual induced
representation; only their signed combination is virtual.

### 8.1 Brauer characters and their Hecke avatars

Fix

$$
\mathfrak B=\{(H_i,\theta_i,n_i)\}_{i=1}^t,
\qquad
1_\Gamma=\sum_i n_i\operatorname{Ind}_{H_i}^{\Gamma}\theta_i,
\tag{8.1}
$$

with $H_i$ elementary, $\theta_i$ linear of finite image, and $n_i\in\mathbf Z$. By the
choice in Section 6.1, every value of every $\theta_i$ already lies in $K$.

The quotient

$$
G_{F_i}/G_M\simeq H_i,
\qquad F_i=F_{H_i},
\tag{8.2}
$$

inflates $\theta_i$ to a finite Galois character of $G_{F_i}$. Arithmetic global reciprocity
gives a finite-order Hecke character $\psi_i$ with the same unramified Frobenius values. Thus

$$
\psi_{i,\tau}(\operatorname{Frob}_w)
=\theta_{i,\tau}(\operatorname{Frob}_w)
\tag{8.3}
$$

at every unramified place. The character is trivial on $G_M$ and at every place of $F_i$ above
a rational prime split completely in $M$.

The quotient characters used to correct cyclic descents in Chapter 5 are not the characters
$\theta_i$ in (8.1). The former select the untwisted packet $\pi_{H_i}$; the latter are inserted
afterward by the Brauer relation.

### 8.2 The actual induced terms

For a coefficient embedding $\tau$, define

$$
U_{i,\tau}=r_{H_i,\tau}\otimes\theta_{i,\tau}
\tag{8.4}
$$

and

$$
A_{i,\tau}
=\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}U_{i,\tau}.
\tag{8.5}
$$

This is actual finite Galois induction of dimension $2[\Gamma:H_i]$. There is no assertion of
a global automorphic induction of $\pi_{H_i}$ from the generally nonnormal field $F_i$ to
$\mathbf Q$.

The representation $A_{i,\tau}$ is semisimple. Its restriction to the normal open subgroup
$G_M$ is a direct sum of conjugates of $r_{1,\tau}$, the realization of $\pi_M$. Those
representations are semisimple, and Lemma 2.1 promotes semisimplicity back to
$G_{\mathbf Q}$.

Write $n_i=n_i^+-n_i^-$ with $n_i^\pm\geq0$ and set

$$
R_{\mathfrak B,\tau}^\pm
=\bigoplus_i A_{i,\tau}^{\oplus n_i^\pm}.
\tag{8.6}
$$

The signed class is

$$
\mathcal R_{\mathfrak B,\tau}
=[R_{\mathfrak B,\tau}^+]-[R_{\mathfrak B,\tau}^-].
\tag{8.7}
$$

No quotient or complement is selected in (8.7).

### 8.3 Recovery of the chosen member

At $\iota_0$, equation (6.4) identifies every term with induction of a restricted copy of
$\rho$. Inflating (8.1) from $\Gamma$ to $G_{\mathbf Q}$ and applying the tensor identity
gives

$$
\begin{aligned}
\mathcal R_{\mathfrak B,\iota_0}
&=\sum_i n_i
\left[\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(\rho|_{G_{F_i}}\otimes\theta_i)\right]\\
&=[\rho]\cdot
\sum_i n_i[\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}\theta_i]\\
&=\boxed{[\rho]}.
\end{aligned}
\tag{8.8}
$$

This is an equality in the semisimple Grothendieck group. It uses no density theorem and no
effectivity at another coefficient embedding.

### 8.4 Rank and determinant

Equation (3.11) gives

$$
\dim\mathcal R_{\mathfrak B,\tau}
=2\sum_i n_i[\Gamma:H_i]=2.
\tag{8.9}
$$

For the determinant, first apply the determinant map to the one-dimensional relation (8.1).
Formula (2.18) gives

$$
\prod_i
\left(
\operatorname{sgn}_{\Gamma/H_i}
\operatorname{Ver}_{H_i}^{\Gamma}\theta_i
\right)^{n_i}=1.
\tag{8.10}
$$

Squaring removes all permutation signs:

$$
\prod_i
(\operatorname{Ver}_{H_i}^{\Gamma}\theta_i)^{2n_i}=1.
\tag{8.11}
$$

By (6.6),

$$
\det U_{i,\tau}
=\chi_\tau|_{G_{F_i}}\theta_{i,\tau}^2.
$$

The rank of $U_{i,\tau}$ is two, so the permutation sign in its induction is squared and
disappears. Equations (2.18)--(2.19), (8.11), and (3.11) give

$$
\begin{aligned}
\det\mathcal R_{\mathfrak B,\tau}
&=\chi_\tau^{\sum_i n_i[\Gamma:H_i]}
\prod_i(\operatorname{Ver}_{H_i}^{\Gamma}\theta_i)^{2n_i}\\
&=\boxed{\chi_\tau}.
\end{aligned}
\tag{8.12}
$$

This is the determinant line of a virtual class. It becomes the determinant of an actual
rank-two representation only after effectivity is proved elsewhere.

### 8.5 Restriction back to the top field

Because $\theta_i$ is trivial on $G_M$, normal-subgroup Mackey decomposition gives

$$
A_{i,\tau}|_{G_M}
\simeq
\bigoplus_{x\in\Gamma/H_i}{}^xr_{1,\tau}.
\tag{8.13}
$$

Conjugation compatibility identifies every summand with $r_{1,\tau}$. Therefore

$$
\mathcal R_{\mathfrak B,\tau}|_{G_M}
=\left(\sum_i n_i[\Gamma:H_i]\right)[r_{1,\tau}]
=[r_{1,\tau}].
\tag{8.14}
$$

This is a useful consistency check, but not an overlap theorem and not effectivity. It forgets
the finite quotient action above $G_M$.

### 8.6 The Mackey Gram input

For two terms $A_{i,\tau}$ and $A_{j,\tau}$, formula (2.13), the quotient by $G_M$, and
equation (6.4h) give

$$
\boxed{
\begin{aligned}
\dim\operatorname{Hom}_{G_{\mathbf Q}}(A_{i,\tau},A_{j,\tau})
=\sum_{x\in H_i\backslash\Gamma/H_j}
\dim\operatorname{Hom}_{G_{L_{ij}(x)}}
(r_{D_{ij}(x),\tau},
r_{D_{ij}(x),\tau}\otimes\delta_{ij,x,\tau}),
\end{aligned}}
\tag{8.15}
$$

where

$$
D_{ij}(x)=H_i\cap xH_jx^{-1},
\qquad
L_{ij}(x)=M^{D_{ij}(x)},
\tag{8.16}
$$

and

$$
\delta_{ij,x}
=({}^x\theta_j)|_{D_{ij}(x)}
(\theta_i|_{D_{ij}(x)})^{-1}.
\tag{8.17}
$$

Every representation in (8.15) already exists over an elementary fixed field. The formula is
therefore ready for a coefficient-independence calculation of self-twists, without assuming
the effective base-field constituent whose existence that calculation is meant to prove.

## 9. Frobenius powers and the common virtual polynomial

Good-prime data enter the construction through finite cyclic blocks. The residue-degree power
is the feature most likely to be lost if induction is treated only at the level of global
degrees.

### 9.1 Power traces without choosing roots

For a monic quadratic polynomial

$$
P(X)=X^2-aX+b
$$

with roots $\alpha,\beta$, define $A_f(a,b)$ by (6.4b). Cayley--Hamilton gives

$$
\alpha^f+\beta^f=A_f(a,b)
\tag{9.1}
$$

for every $f\geq0$. Hence the $f$th-power transform is

$$
P^{[f]}(X)=X^2-A_f(a,b)X+b^f.
\tag{9.2}
$$

The construction is integral in $a,b$. It commutes with every coefficient embedding and is
transitive:

$$
(P^{[f]})^{[g]}=P^{[fg]}.
\tag{9.3}
$$

This is exactly the polynomial law for restriction through a tower with successive residue
degrees $f$ and $g$.

### 9.2 The local cyclic-block determinant

Let $L/K$ be a finite unramified extension of nonarchimedean local fields of residue degree
$f$, and let $U$ be an unramified $d$-dimensional representation of $G_L$. Arithmetic
Frobenius of $K$ permutes the $f$ coset blocks cyclically. Its $f$th power returns to the
initial block and acts there as arithmetic Frobenius of $L$. A cyclic block determinant
therefore gives

$$
\det(1-\operatorname{Frob}_KT\mid\operatorname{Ind}_{G_L}^{G_K}U)
=\det(1-\operatorname{Frob}_LT^f\mid U).
\tag{9.4}
$$

For a ramified $L/K$, formula (9.4) is instead an identity on inertia invariants after the
usual local-induction analysis; it is not an identity on the whole induced space. We do not
need that variant. The finite set below excludes every rational prime ramified in $M$, so all
local extensions in the good-prime calculation are unramified.

For a global fixed field $F_i$ and a rational prime $p$ unramified in $M$, local Mackey
decomposition sums one such block over every $w\mid p$. If

$$
P_{i,w}(X)=X^2-a_{i,w}X+Nw
\tag{9.5}
$$

is the packet polynomial and $\zeta_{i,w}=\theta_i(\operatorname{Frob}_w)$, then, whenever
the residue characteristic of $\tau$ differs from $p$, the characteristic series of
$A_{i,\tau}$ at $p$ is the $\tau$-image of

$$
D_{i,p}(T)=
\prod_{w\mid p}
\left(
1-a_{i,w}\zeta_{i,w}T^{f(w/p)}
+\zeta_{i,w}^2Nw\,T^{2f(w/p)}
\right).
\tag{9.6}
$$

The formula uses no chosen Satake roots.

### 9.3 The algebraic signed Euler factor

Choose one finite set $S_0$ containing $2$, $\ell$, every rational prime ramified in $M$, and
every prime below the finite ramification or excluded local-comparison set of a packet or a
Brauer character. For $p\notin S_0$, define

$$
D_{\mathfrak B,p}(T)
=\prod_iD_{i,p}(T)^{n_i}\in K(T)^\times.
\tag{9.7}
$$

At an embedding $\tau$ whose residue characteristic is different from $p$, this is exactly

$$
\frac{
\det(1-\operatorname{Frob}_pT\mid R_{\mathfrak B,\tau}^+)
}{
\det(1-\operatorname{Frob}_pT\mid R_{\mathfrak B,\tau}^-)
}.
\tag{9.8}
$$

At this point (9.7) is only a rational function. Its signed degree is two by (8.9), but degree
does not imply polynomiality and polynomiality would not imply effectivity.

### 9.4 Polynomiality from the distinguished member

At $\iota_0$, equation (8.8) turns (9.8) into the characteristic series of $\rho$:

$$
\iota_0(D_{\mathfrak B,p}(T))
=\det(1-\rho(\operatorname{Frob}_p)T)
=1-\operatorname{tr}\rho(\operatorname{Frob}_p)T+pT^2.
\tag{9.9}
$$

The embedding $K(T)\hookrightarrow\overline{\mathbf Q}_\ell(T)$ is injective. Write
$D_{\mathfrak B,p}=A/B$ with coprime $A,B\in K[T]$. Equation (9.9) says that
$\iota_0(B)$ divides $\iota_0(A)$ in
$\overline{\mathbf Q}_\ell[T]$; coprimality forces $B$ to be constant. Thus
$D_{\mathfrak B,p}\in K[T]$, and comparison with (9.9) shows that the trace there belongs to
$\iota_0(K)$. Define $a_p\in K$ by

$$
\iota_0(a_p)=\operatorname{tr}\rho(\operatorname{Frob}_p).
$$

Then

$$
\boxed{
D_{\mathfrak B,p}(T)=1-a_pT+pT^2\in K[T].}
\tag{9.10}
$$

Applying any $\tau$ of residue characteristic different from $p$ gives the same virtual
characteristic series with coefficients transported by $\tau$. At an embedding of residue
characteristic $p$, equation (9.10) remains an algebraic polynomial identity, but it is not
interpreted here as the characteristic polynomial of an unramified $p$-adic representation at
$p$. This is propagation of an algebraic identity, not propagation of an effective
representation from $\iota_0$.

The polynomial is independent of conjugating a Brauer term, because conjugation only permutes
the places and cyclic blocks in (9.6). If another Brauer relation is used, the same distinguished
calculation shows that its rational function is again (9.10). Thus the good virtual polynomial
is relation-independent before effectivity.

### 9.5 Purity and coefficient covariance

Although purity is not used to prove effectivity, the array retains the correct weight record.
Let $\alpha_p,\beta_p$ be the roots of (9.10). Choose a place $w$ of $M$ above $p$ with residue
degree $f$. At $\iota_0$, restriction of $\rho$ to $G_M$ shows that the roots of the top packet
polynomial at $w$ are $\alpha_p^f$ and $\beta_p^f$. The top weight-two packet is pure of weight
one, so for every complex embedding

$$
|\alpha_p^f|=|\beta_p^f|=(p^f)^{1/2}.
$$

Taking positive real $f$th roots gives

$$
|\alpha_p|=|\beta_p|=p^{1/2}.
\tag{9.11}
$$

Applying the same argument to coefficient-conjugate top packets proves the assertion for every
conjugate root. Thus (9.10) is pure of weight one as an algebraic polynomial record.

If $\sigma\in\operatorname{Gal}(K/\mathbf Q)$, coefficient conjugation sends it to

$$
1-\sigma(a_p)T+pT^2.
\tag{9.12}
$$

Field conjugation inside $M$ leaves (9.10) unchanged after permuting the local factors. These
two covariance statements agree with the distinction made in Section 6.4.

## 10. Local records, especially the SP place

The good polynomial does not determine ramification or monodromy. Local compatibility must be
carried through the actual induced summands and through the algebraic local objects attached to
the elementary packets.

### 10.1 Local Mackey decomposition

For a rational place $v$, formula (2.17) gives the actual identity

$$
\left.A_{i,\tau}\right|_{G_{\mathbf Q_v}}
\simeq
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{(F_i)_w}}^{G_{\mathbf Q_v}}
(r_{H_i,\tau}|_{G_{(F_i)_w}}\otimes\theta_{i,\tau,w}).
\tag{10.1}
$$

Away from the coefficient residue characteristic, the Weil--Deligne functor commutes with
direct sums, finite restriction, finite induction, and finite-order twisting. Thus (10.1)
produces a signed local Weil--Deligne class for $\mathcal R_{\mathfrak B,\tau}$ which retains
finite inertia and monodromy.

The local intersection groups $\Delta_v\cap xH_ix^{-1}$ in (2.16) are elementary because
they are subgroups of the elementary group $xH_ix^{-1}$. No packet indexed by them is
required, however: (10.1) is restriction of an already existing global induced representation,
and the associated completion is read from (2.16). This is different from the global Mackey
Gram calculation, where the packet over the global fixed field of an elementary intersection
is used and Proposition 6.2 applies.

### 10.2 The common dyadic special object

Because $2$ splits completely in $M$, it splits completely in every $F_H$. Every completion
above $2$ is $\mathbf Q_2$, and every finite quotient character used in the packet descent or
in the Brauer relation is locally trivial.

The uniform special scalar and local-preservation hypotheses in the controlled datum supply one
algebraic local object over $K$ in the arithmetic covariant normalization,

$$
\mathscr D_{2,K}=(r_{2,K},N_{2,K}),
\tag{10.2}
$$

whose realization under $\iota_0$ is (1.3)--(1.5). The operator $N_{2,K}$ is nonzero because
an injective coefficient embedding cannot send a nonzero matrix to zero. It has rank one, and

$$
\mathscr L_{2,K}=\ker N_{2,K}=\operatorname{im}N_{2,K}
\tag{10.3}
$$

is a $K$-line. Its arithmetic Frobenius quotient eigenvalue is the rational sign
$\varepsilon_2$, while the eigenvalue on the line is $2\varepsilon_2$.

Concretely, the raw geometric special block of Books 136--137 has Frobenius eigenvalue
$\varepsilon_2$ on its monodromy kernel and $2\varepsilon_2$ on its quotient. Passing to the
covariant Tate realization and inverting geometric Frobenius gives the ordered arithmetic pair
$(\varepsilon_2,2\varepsilon_2)$ on quotient and line. This accounts for both the factor two in
(1.4) and the cyclotomic determinant; no sign is chosen from a square after completion.

For every $H$, every dyadic place $w$ of $F_H$, and every coefficient embedding $\tau$ whose
residue characteristic is not two,

$$
\operatorname{WD}_w(r_{H,\tau})^{\mathrm{F\text{-}ss}}
\simeq\mathscr D_{2,K}\otimes_{K,\tau}\Omega.
\tag{10.4}
$$

This follows from Section 5.4 on the automorphic side and the special local--global comparison
on the packet side. It is equality of the full pair, not an inference from a conductor or a
finite inertial polynomial.

### 10.3 The invariant line, sign, and conductor

The local object (10.4) has trivial finite Weil inertia and nonzero rank-one monodromy. In the
associated $\ell$-adic Galois representation, inertia acts through the monodromy exponential;
its fixed space is therefore exactly (10.3) after scalar extension. Equivalently, in
Weil--Deligne notation the relevant space is $(\ker N_2)^{I_2}=\ker N_2$, not the whole
two-dimensional space on which finite Weil inertia is trivial. The Frobenius return relation is

$$
r_2(F_2)N_2r_2(F_2)^{-1}=2N_2,
$$

and the quotient/line eigenvalues retain the ordered pair

$$
(\varepsilon_2,2\varepsilon_2).
\tag{10.5}
$$

The Swan conductor is zero. The Weil--Deligne conductor formula gives

$$
a_2
=\dim V-\dim(\ker N_2)^{I_2}
=2-1=1.
\tag{10.6}
$$

Thus every elementary packet has the SP record: nonzero rank-one monodromy, the named invariant
line, the split/nonsplit sign, and conductor exponent one.

At the level of the signed induced array, local Mackey gives $[\Gamma:H_i]$ copies of
$\mathscr D_{2,K}$ in the $i$th term. Hence

$$
[\mathscr D_2(\mathcal R_{\mathfrak B,\tau})]
=\left(\sum_i n_i[\Gamma:H_i]\right)
[\mathscr D_{2,K}\otimes_{K,\tau}\Omega]
=[\mathscr D_{2,K}\otimes_{K,\tau}\Omega].
\tag{10.7}
$$

Equation (10.7) is still a virtual local equality. It supplies the exact local class to which
characteristic-zero effectivity and cancellation may later be applied.

### 10.4 Other finite places and the coefficient-prime boundary

For a finite $v\ne2$ whose residue characteristic differs from that of $\tau$, the packet
array retains exactly the local Weil--Deligne pairs in the proved attachment range. Restriction
through a field extension keeps the monodromy operator and restricts the Weil action. Finite
twisting multiplies the Weil action and leaves the nilpotent operator unchanged. Finite
induction is governed by (10.1).

At a place outside $S_0$ every summand is unramified. At a prime in $S_0$, the full local
Mackey expression, rather than the good polynomial, is the record. Auxiliary ramification in
positive and negative terms is not declared canceled: cancellation is an effectivity question.

If the local residue characteristic equals the coefficient residue characteristic, the
prime-to-coefficient Weil--Deligne comparison does not apply. The packet theorem may separately
supply de Rham or crystalline rational data, but this book makes no such conclusion merely from
the signed array. In particular, it constructs no integral finite-flat object at a new
coefficient prime.

### 10.5 Archimedean places

Every $F_H$ is totally real. At a real place, the decomposition group in the totally real top
is trivial, so every quotient character is locally trivial. Each parallel-weight-two packet
has the same odd rank-two archimedean parameter. Local Mackey and (3.11) therefore leave one
virtual copy of that parameter at the ground real place.

Equivalently, complex conjugation has virtual trace zero and virtual determinant $-1$, agreeing
with the cyclotomic determinant in (8.12). This is an archimedean consistency check on the
packet array, not a proof of an actual base-field representation at a general coefficient
embedding.

## 11. The exported packet-array package

### 11.1 Complete statement

We collect the precise output in a form that can be used by a character-norm theorem.

**Theorem 11.1 (Brauer--Mackey packet-array package).** Let (1.1)--(1.6) be a controlled SP
top datum. Then there are:

- a selected cuspidal packet $\pi_H$ over $F_H=M^H$ for every elementary $H\leq\Gamma$;
- one finite Galois coefficient field $K$ and semisimple realizations $r_{H,\tau}$ for every
  coefficient embedding $\tau$;
- conjugation identities (5.4), (6.8), and exact overlap identities
  (6.4a), (6.4e)--(6.4h) on every
  elementary intersection field;
- for every integral Brauer datum $\mathfrak B$, actual semisimple induced terms
  $A_{i,\tau}$ and a signed class $\mathcal R_{\mathfrak B,\tau}$;
- the rank, determinant, and distinguished identities

  $$
  \dim\mathcal R_{\mathfrak B,\tau}=2,
  \qquad
  \det\mathcal R_{\mathfrak B,\tau}=\chi_\tau,
  \qquad
  \mathcal R_{\mathfrak B,\iota_0}=[\rho];
  \tag{11.1}
  $$

- the Hom-ready Mackey formula (8.15), with quotient character
  $\delta=\beta\alpha^{-1}$;
- common good virtual characteristic series

  $$
  1-\tau(a_p)T+pT^2
  \tag{11.2}
  $$

  computed by the residue-degree formula (9.6) at coefficient embeddings of residue
  characteristic different from $p$, together with the Frobenius-power recurrence (6.4b);
  and
- at $2$, the common algebraic SP pair with nonzero rank-one monodromy, invariant line,
  sign $\varepsilon_2$, and conductor exponent one, as a virtual local record for every
  coefficient embedding away from residue characteristic two.

If $D\leq H$ and an ascent-admissible prime-cyclic tower is available, the overlap is the
actual automorphic identity (7.1). Without that admissibility, no automorphic base change to
$F_D$ is claimed, but the semisimple identity (6.4a) is still proved by algebraic
Frobenius-power comparison and recognition.

The theorem asserts neither that $\mathcal R_{\mathfrak B,\tau}$ is effective nor that the
classes for varying $\tau$ form a base-field compatible family. It asserts no integral
structure.

### 11.2 Proof

Integral Brauer induction is Theorem 3.4. The tensor identity, determinant transfer, Frobenius
reciprocity, and Mackey decomposition are proved in Chapter 2. Proposition 4.2 supplies a
prime-cyclic subgroup chain for every elementary group and every elementary intersection.

Using a descent-admissible chain, Chapter 5 constructs $\pi_H$ one cyclic layer at a time. The
extension comparison lemma and the fact that $\rho$ is already defined downstairs select the
unique quotient twist whose distinguished realization is $\rho|_{G_{F_H}}$. Strong
multiplicity one proves chain independence and conjugation compatibility.

Chapter 6 applies the earlier packet theorem separately to the finitely many $\pi_H$ and forms
one coefficient ledger. The distinguished determinant forces every algebraic central
multiplier to be trivial, giving (6.6). Chapter 7 proves the overlap by two routes. Actual
base change gives (7.1) on an admissible tower. In every case, equality at $\iota_0$, the
residue-degree recurrence, injectivity of $\iota_0$, density, and Brauer--Nesbitt give (6.4a).
This yields the Hom-ready conjugate intersection formula.

Chapter 8 inserts the Brauer characters. The tensor identity gives $[\rho]$ at $\iota_0$;
evaluation at the identity gives rank two; determinant transfer and the squared determinant of
the one-dimensional Brauer relation give the cyclotomic virtual determinant. Mackey and the
overlap theorem give (8.15).

Finally, cyclic-block determinants give the explicit good Euler factor. Its value at
$\iota_0$ is the characteristic series of $\rho$, and injectivity makes it the common
algebraic quadratic polynomial. Complete splitting at two makes every packet and every quotient
character locally identical there. The established special comparison therefore gives the
common nonzero-monodromy pair and conductor-one calculation of Chapter 10. All clauses follow.
$\square$

### 11.3 Structural audit

The construction survives the following hostile tests.

**A nonnormal overlap is not treated as one cyclic extension.** It is reached group-theoretically
by the tower (4.3). Automorphic base change is used only if every step is admissible. The
semisimple identity needed by Mackey is separately proved in Proposition 6.2.

**Top-field agreement is not used as overlap agreement.** Equation (8.14) forgets finite
quotient characters. The proof works on $G_{M^{H\cap xJx^{-1}}}$ and retains the explicit
ratio $\beta\alpha^{-1}$.

**One distinguished realization is not called a compatible family.** It selects every
automorphic descent. The coefficient realizations are then constructed from the resulting
packets by the earlier attachment theorem. No member of $G_{\mathbf Q}$ at another coefficient
embedding is assumed.

**A virtual rank or polynomial is not called effective.** The actual objects are the large
induced terms $A_{i,\tau}$. Their signed class can have negative multiplicities. Equations
(8.9), (8.12), and (9.10) do not remove those multiplicities.

**The dyadic record is not inferred from its conductor.** The common algebraic object retains
$N_2\ne0$, its rank, the line $\ker N_2=\operatorname{im}N_2$, the Frobenius-return equation,
and the sign. Conductor one is derived afterward.

**Coefficient embeddings do not transport matrices between unrelated completions.** They
transport algebraic polynomials, local pairs, and isomorphism classes. A common finite field is
chosen because the array is finite; no minimal field of definition is claimed.

**No rational cancellation is reduced modulo a prime.** The construction contains no lattice,
integral projector, or residual representation. The coefficient-prime boundary is explicit in
Section 10.4.

**No later effectivity or assembly theorem is used.** The overlap compares already existing
elementary-field packet realizations. The desired base-field constituent never appears as a
premise.

### 11.4 Dependency audit

The substantial earlier inputs are used in the following exact forms.

| Source | Input used here | Strengthening not made |
|---|---|---|
| Book 95, Hecke-character theory | finite Galois characters and finite-order Hecke avatars, with arithmetic reciprocity, norm pullback, and conjugation | no higher-rank automorphic induction across $F_H/\mathbf Q$ |
| Books 96--97, cyclic and solvable base change | selected prime-cyclic descent, antecedent-complete fibers, fiber saturation, all-place parameter restriction, and tower independence inside the admissible range, translated from geometric to arithmetic Frobenius | no transfer along an inadmissible tower and no nonsolvable descent |
| Books 135--137, weight-two attachment and local--global compatibility | coefficient realizations of each constructed packet, algebraic determinants and good polynomials, and the conditional special package once its scalar and raw-to-semisimple local-preservation hypotheses are supplied | no unverified bad-place comparison or coefficient-prime integral conclusion |
| Book 171, Galois refinement and density | one controlled fixed-field diagram, preservation by complete splitting, and density of good Frobenius classes | no claim that field-theoretic towers alone satisfy automorphic selector hypotheses |
| Book 186, the preceding chosen-lift audit | the exact conditional format of $\rho$, the controlled top $M$, the SP record, and the already-automorphic identity (1.6) | Book 186 does not unconditionally construct the controlled SP seed; the present theorem assumes that seed has already been supplied |

Finite-group Brauer induction, Mackey theory, determinant transfer, elementary subnormality,
the cyclic extension-comparison lemma, and Brauer--Nesbitt recognition are proved in this book
rather than hidden in an interface. The earlier discussions of compatible systems and Brauer
descent in Books 175--176 are used only to audit normalizations and logical boundaries; no
pointwise effectivity,
coefficient descent, or integral cancellation result is imported.

The SP local conclusion depends on the special scalar equality and the raw-to-semisimple
local-preservation identity being supplied for every constructed packet and every coefficient
place away from two. Books 136--137 explicitly leave those inputs conditional. If either is
absent, distinguished $\ell$-adic SP behavior alone does not determine monodromy or its sign at
another coefficient embedding. That is the exact local boundary, and it is included in the
controlled-top datum rather than smuggled in through a conductor equality.

### 11.5 Conclusion

The nonsolvable top has been replaced by a finite and exact diagram. Every elementary subgroup
gives one fixed field, one selected cuspidal packet, and one algebraic coefficient system. The
extending representation chooses the descent twists, strong multiplicity one removes dependence
on the chosen descent chain, and conjugation organizes the packets into the same subgroup
symmetry as the Galois top.

Mackey theory then identifies the fields on which two induced terms meet. Elementary
nilpotence supplies prime-cyclic towers to those fields, but the proof does not confuse their
existence with automorphic admissibility. Where admissibility holds, the packet identity is an
actual base-change identity. Everywhere, the distinguished realization and the exact
Frobenius-power recurrence prove the required semisimple overlap directly. The quotient
character left in a Hom space is consequently the explicit Brauer ratio and no hidden descent
twist.

The signed induced array now has every invariant it can legitimately possess before
effectivity: rank two, cyclotomic determinant line, the original chosen member at the
distinguished embedding, common pure quadratic good-prime series, conjugation covariance, and
the full dyadic SP record with nonzero rank-one monodromy, invariant line, sign, and conductor
one. It has no asserted positive constituent, no assembled compatible family over
$\mathbf Q$, and no integral lattice. Those absences are the precise boundary of the topic,
not unfinished steps inside it.
