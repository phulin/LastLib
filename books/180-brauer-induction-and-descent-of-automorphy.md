# Brauer Induction and Descent of Automorphy

## Contents

1. [Why Brauer descent is virtual](#1-why-brauer-descent-is-virtual)
   - [Potential automorphy and the nonsolvable gap](#11-potential-automorphy-and-the-nonsolvable-gap)
   - [Four different endpoints](#12-four-different-endpoints)
   - [The scope of this book](#13-the-scope-of-this-book)
   - [Conventions](#14-conventions)
2. [Elementary groups and integral Brauer relations](#2-elementary-groups-and-integral-brauer-relations)
   - [Elementary groups](#21-elementary-groups)
   - [Monomiality](#22-monomiality)
   - [The restriction criterion](#23-the-restriction-criterion)
   - [Integral Brauer induction](#24-integral-brauer-induction)
   - [Two diagnostic relations](#25-two-diagnostic-relations)
3. [Induction, reciprocity, and Mackey theory](#3-induction-reciprocity-and-mackey-theory)
   - [Finite-index induction](#31-finite-index-induction)
   - [The tensor identity and determinants](#32-the-tensor-identity-and-determinants)
   - [Frobenius reciprocity](#33-frobenius-reciprocity)
   - [Mackey decomposition](#34-mackey-decomposition)
   - [Fixed fields and local places](#35-fixed-fields-and-local-places)
4. [Elementary intersections and solvable towers](#4-elementary-intersections-and-solvable-towers)
   - [Subgroups of elementary groups are subnormal](#41-subgroups-of-elementary-groups-are-subnormal)
   - [Prime-cyclic towers to an overlap field](#42-prime-cyclic-towers-to-an-overlap-field)
   - [A conditional overlap principle](#43-a-conditional-overlap-principle)
   - [Why top-field agreement is not enough](#44-why-top-field-agreement-is-not-enough)
5. [Clifford theory and factor sets](#5-clifford-theory-and-factor-sets)
   - [Homogeneous restriction](#51-homogeneous-restriction)
   - [The inertia group and the Clifford correspondence](#52-the-inertia-group-and-the-clifford-correspondence)
   - [The projective multiplicity representation](#53-the-projective-multiplicity-representation)
   - [Extension, obstruction, and twisting ambiguity](#54-extension-obstruction-and-twisting-ambiguity)
   - [Cyclic and solvable descent](#55-cyclic-and-solvable-descent)
6. [Substituting arithmetic data into a Brauer relation](#6-substituting-arithmetic-data-into-a-brauer-relation)
   - [A coefficient-indexed diagram](#61-a-coefficient-indexed-diagram)
   - [Finite characters and termwise operations](#62-finite-characters-and-termwise-operations)
   - [The signed base-field class](#63-the-signed-base-field-class)
   - [Rank and determinant](#64-rank-and-determinant)
   - [Frobenius blocks and formal Euler factors](#65-frobenius-blocks-and-formal-euler-factors)
7. [What can make a virtual class effective](#7-what-can-make-a-virtual-class-effective)
   - [The character norm](#71-the-character-norm)
   - [The Mackey Gram matrix](#72-the-mackey-gram-matrix)
   - [The abstract norm-one criterion](#73-the-abstract-norm-one-criterion)
   - [Coefficient descent and the Schur obstruction](#74-coefficient-descent-and-the-schur-obstruction)
   - [What Brauer induction does not prove](#75-what-brauer-induction-does-not-prove)
8. [Automorphic meaning and its boundary](#8-automorphic-meaning-and-its-boundary)
   - [Solvable packet descent](#81-solvable-packet-descent)
   - [No nonsolvable automorphic induction is hidden](#82-no-nonsolvable-automorphic-induction-is-hidden)
   - [Local parameters and monodromy](#83-local-parameters-and-monodromy)
   - [Recognition is not existence](#84-recognition-is-not-existence)
9. [The reusable descent package](#9-the-reusable-descent-package)
   - [The abstract theorem](#91-the-abstract-theorem)
   - [Prerequisites and application boundary](#92-prerequisites-and-application-boundary)
   - [Failure tests](#93-failure-tests)
   - [Conclusion](#94-conclusion)

## 1. Why Brauer descent is virtual

### 1.1 Potential automorphy and the nonsolvable gap

Let $M/F$ be a finite Galois extension of number fields with group $\Gamma$, and suppose that
an arithmetic object over $F$ becomes automorphic after restriction to $M$. If $\Gamma$ is
solvable and the automorphic packet lies in the established transfer range, cyclic descent can
be iterated down a prime-cyclic tower. If $\Gamma$ is not solvable, that theorem does not apply
to $M/F$ as a whole.

Brauer induction changes the question. For an elementary subgroup $H\leq\Gamma$, the upper
extension

$$
M/M^H
$$

is solvable. One may therefore try to construct an automorphic packet over each elementary fixed
field $F_H=M^H$, twist it by a finite-order character of $H$, and induce its Galois realization
from $G_{F_H}$ to $G_F$. An integral character identity for $1_\Gamma$ then gives a signed sum
of such induced representations.

The word **signed** is the central warning. The positive terms and negative terms are honest
representations of large rank, but their difference initially lives only in a Grothendieck
group. Brauer's theorem does not supply an inclusion of the negative part in the positive part.
It does not create a rank-two quotient, a lattice, or a compatible family. The purpose of the
general theory is to say exactly what is formal, what is obstructed, and which additional inputs
can turn the virtual identity into an actual object.

### 1.2 Four different endpoints

Four conclusions often called “descent” must be separated.

1. **Solvable automorphic descent** constructs an actual automorphic representation down an
   admissible solvable tower. Its ambiguity is a torsor under quotient characters, and coherent
   choices are required at successive steps.
2. **Virtual Brauer descent** constructs a class

   $$
   \mathcal R=[R^+]-[R^-]
   $$

   on the base-field Galois group. Traces, virtual determinant, and formal local factors make
   sense, but $\mathcal R$ need not be effective.
3. **Characteristic-zero effectivity** proves that $\mathcal R=[r]$ for one actual
   representation $r$, equivalently that $R^+\simeq r\oplus R^-$ after semisimplification.
   This is a positivity theorem, not a consequence of virtual rank.
4. **Coefficient and family descent** gives models over the completions of one number field,
   coherent place indexing, and a compatible-system structure. An invariant isomorphism class
   over an algebraic closure can still have a Schur or scalar-cocycle obstruction.

A fifth assertion is stronger again: the effective base-field representation may itself be
automorphic. Signed Euler products and strong multiplicity one do not prove existence of such a
packet. One needs an independent automorphic descent or converse theorem.

### 1.3 The scope of this book

This book proves the reusable algebra behind these distinctions:

- integral Brauer induction from linear characters of elementary subgroups;
- finite-index induction, determinant transfer, Frobenius reciprocity, and Mackey theory;
- the fixed-field and local double-coset dictionaries;
- prime-cyclic subnormal towers inside elementary groups;
- Clifford theory, its factor set, and the extension obstruction in degree two cohomology;
- construction of a signed arithmetic class, including its rank, determinant, and local
  Frobenius blocks; and
- abstract norm-one and multiplicity-one criteria which are sufficient for effectivity and
  coefficient descent once their hypotheses have been verified.

It does not construct the controlled elementary packet array used in the FLT argument. It does
not verify the application-specific Mackey Gram matrix or prove that that signed array is
effective. It does not assemble the resulting representations over the base field into one
place-indexed compatible system. Those are separate downstream theorems. This division is not
merely editorial: using any of those conclusions here would make the dependency graph circular.

The arithmetic portions below are consequently conditional on a displayed diagram of packet
realizations. The finite-group and Clifford results are unconditional. Whenever an automorphic
overlap is mentioned, every cyclic step is explicitly required to lie in the admissible range of
the established cyclic and solvable transfer theorems. A group-theoretic tower alone is never
promoted to an automorphic theorem.

### 1.4 Conventions

All representation fields have characteristic zero. Finite-group representations are taken over
a splitting field unless a smaller field is explicitly named. Representations of profinite
groups are finite dimensional and continuous; a Grothendieck group below is the free group on
continuous irreducible semisimple classes, not the Grothendieck group of all possibly
nonsemisimple continuous representations.

Every $H^1$ or $H^2$ below is the cohomology of the displayed finite quotient with its
displayed coefficient action, so continuity of cochains is automatic. The Clifford quotient
$I/N$ acts trivially on the scalar group $k^\times$, whereas the coefficient-descent group
$\operatorname{Gal}(k'/k)$ acts naturally on $(k')^\times$. These two coefficient actions are
part of the distinction between the two obstructions.

Induction from an open subgroup is unnormalized finite induction. On $\mathrm{GL}_d$,
automorphic twisting by a Hecke character acts through the determinant, so the central character
is multiplied by the $d$-th power of the twisting character (the square in rank two). Unless a
quoted packet theorem uses another convention, Frobenius in the arithmetic formulas is arithmetic
Frobenius. Thus

$$
\chi_\ell(\operatorname{Frob}_v)=q_v.
$$

The Weil--Deligne and solvable-transfer inputs are stated in a geometric-Frobenius ledger.
When they are used here, the named Frobenius is inverted once; the underlying Weil
representation, inertia action, and monodromy operator are unchanged. The finite-character and
covariant packet ledgers already use the arithmetic convention displayed above.

For a finite local extension $L/K$, the Frobenius-cycle length is the residue degree
$f(L/K)$, not the ramification index or the global degree. Local Weil--Deligne data always
retain the nilpotent operator $N$. No default value of $N$, no special inertial type, and no
integral local condition is built into the general theory.

## 2. Elementary groups and integral Brauer relations

### 2.1 Elementary groups

For a prime $p$, a finite group is $p$-elementary if it has the form

$$
H=C\times P,
\tag{2.1}
$$

where $C$ is cyclic of order prime to $p$ and $P$ is a $p$-group. A group is
elementary if it is $p$-elementary for some $p$.

Elementary groups are nilpotent. Indeed, $C$ is the direct product of its Sylow subgroups,
as is $P$, and all Sylow subgroups of $C\times P$ are normal. They are therefore solvable.
The direct-product condition is essential: a semidirect product $C\rtimes P$ need not be
elementary.

Every subgroup $D\leq C\times P$ is elementary. To see this, let $m=|C|$ and
$|P|=p^a$. If $d=(c,u)\in D$, choose integers $r,s$ with

$$
r\equiv1\pmod m,\quad r\equiv0\pmod{p^a},
\qquad
s\equiv0\pmod m,\quad s\equiv1\pmod{p^a}.
$$

Then $d^r=(c,1)\in D$ and $d^s=(1,u)\in D$. Hence

$$
D=(D\cap C)\times(D\cap P),
\tag{2.2}
$$

and $D\cap C$ is cyclic.

### 2.2 Monomiality

An irreducible character is monomial if it is induced from a linear character of a subgroup.

**Proposition 2.1.** Every irreducible character of an elementary group is monomial.

**Proof.** Let $H=C\times P$. An irreducible representation is
$\alpha\otimes\tau$, where $\alpha$ is linear on $C$ and $\tau$ is irreducible on
$P$. It is enough to prove that irreducible representations of finite $p$-groups are
monomial.

Proceed by induction on $|P|$. Divide by the kernel of $\tau$; an inducing character on
the quotient pulls back, so assume $\tau$ faithful. Schur's lemma makes $Z(P)$ act by
scalars, and faithfulness makes $Z(P)$ cyclic. If $P$ is abelian, $\tau$ is linear.
Otherwise choose a central subgroup of order $p$ in the nontrivial $p$-group
$P/Z(P)$, generated by $xZ(P)$, and put $A=\langle x,Z(P)\rangle$. Then $A$ is
abelian, normal, and properly contains $Z(P)$. Choose a linear
constituent $\lambda$ of $\tau|_A$, and let $I<P$ be its stabilizer. The inequality is
strict, for if $I=P$, then $A$ acts by scalars and faithfulness forces
$[P,A]=1$, contradicting $A\not\subseteq Z(P)$.

The sum of the conjugate $\lambda$-isotypic spaces is the whole representation, and the
action on one such space gives an irreducible representation $\tau_0$ of $I$ with

$$
\tau\simeq\operatorname{Ind}_I^P\tau_0.
$$

By induction, $\tau_0=\operatorname{Ind}_J^I\mu$ for a linear $\mu$. Transitivity gives
$\tau=\operatorname{Ind}_J^P\mu$. Finally,

$$
\alpha\otimes\tau
\simeq\operatorname{Ind}_{C\times J}^{C\times P}(\alpha\otimes\mu),
$$

which is monomial. $\square$

### 2.3 The restriction criterion

The integrality step in Brauer induction is local at each rational prime. Write
$\mathbf Z_{(p)}$ for the localization of $\mathbf Z$ at $p$.

**Lemma 2.2.** Let $A$ be finite and $P$ a Sylow $p$-subgroup. There is a
$\mathbf Z_{(p)}$-linear combination of permutation characters induced from $p$-subgroups
whose value is $1$ on $p$-elements and $0$ on all other elements.

**Proof.** Put $u=\operatorname{Ind}_P^A1$. It counts fixed points on $A/P$. If $a$ is
not a $p$-element, it fixes no coset. If $a$ is a $p$-element, the cyclic group
$\langle a\rangle$ acts on $A/P$, whose cardinality is prime to $p$; its nontrivial
orbits have $p$-power cardinality, so

$$
u(a)\equiv[A:P]\not\equiv0\pmod p.
$$

Let $b_1,\ldots,b_s$ be the nonzero values of $u$ on $p$-elements and set

$$
Q(X)=1-\prod_{j=1}^s(1-X/b_j).
$$

Every $b_j$ is a unit in $\mathbf Z_{(p)}$, $Q(0)=0$, and $Q(b_j)=1$. Powers of $u$
are permutation characters of Cartesian powers of $A/P$; their stabilizers are
intersections of conjugates of $P$, hence $p$-groups. Expanding $Q(u)$ proves the
claim. $\square$

**Theorem 2.3 (Brauer restriction criterion).** A rational linear combination $\varphi$ of
irreducible characters of a finite group $G$ is a generalized character if and only if its
restriction to every elementary subgroup is a generalized character.

**Proof.** Only the converse needs proof. Write

$$
\varphi=\sum_{\chi\in\operatorname{Irr}(G)}a_\chi\chi,\qquad a_\chi\in\mathbf Q.
$$

It is enough to prove $a_\chi\in\mathbf Z_{(p)}$ for every $p$, because the intersection
of these localizations is $\mathbf Z$.

Fix $p$. Split the inner product
$a_\chi=\langle\varphi,\chi\rangle_G$ into $p$-sections according to the conjugacy class
of the prime-to-$p$ part $s$. In $A=C_G(s)$, Lemma 2.2 replaces the indicator of
$p$-elements by a $\mathbf Z_{(p)}$-linear combination of permutation characters induced
from $p$-subgroups $Q\leq A$. Fourier inversion on the cyclic group
$\langle s\rangle$, whose order is prime to $p$, rewrites each section as a linear
combination of inner products on

$$
\langle s\rangle\times Q.
$$

This group is elementary. By hypothesis the restriction of $\varphi$ to it is a
generalized character, so all those inner products are integers. The only denominators are
the $p$-units from Lemma 2.2 and $|\langle s\rangle|$. Thus
$a_\chi\in\mathbf Z_{(p)}$. Since this holds for every $p$, $a_\chi\in\mathbf Z$.
$\square$

Here is the change of variables in that argument. The contribution of the section of $s$
is

$$
\frac1{|C_G(s)|}
\sum_{\substack{u\in C_G(s)\\u\text{ a }p\text{-element}}}
\varphi(su)\chi((su)^{-1}).
\tag{2.3a}
$$

Write the $p$-element indicator as
$\sum_Qc_Q\operatorname{Ind}_Q^{C_G(s)}1$, with
$c_Q\in\mathbf Z_{(p)}$. Expanding the induced character replaces the sum over $u$ by
sums over conjugates $xqx^{-1}$, $q\in Q$. Since $x$ centralizes $s$, the product
$sxqx^{-1}$ is conjugate to $sq$. Now insert

$$
\mathbf 1_{\{s\}}(t)
=\frac1{|\langle s\rangle|}
\sum_{\alpha\in\widehat{\langle s\rangle}}
\alpha(ts^{-1})
\tag{2.3b}
$$

on the cyclic factor. The pairs $tq$ run through
$\langle s\rangle\times Q$, and the resulting sum is, up to a root of unity and the
displayed $p$-unit denominators, an inner product

$$
\left\langle
\varphi|_{\langle s\rangle\times Q},
\chi|_{\langle s\rangle\times Q}\otimes\alpha
\right\rangle.
\tag{2.3c}
$$

The roots of unity are integral. The calculation therefore places each section in the
localization of a cyclotomic integer ring at every prime above $p$. The total
$a_\chi$ is rational, so intersecting those localizations with $\mathbf Q$ gives
$\mathbf Z_{(p)}$. This supplies the arithmetic detail hidden by the phrase “Fourier
inversion rewrites.”

The proof has not used linear characters of a nonabelian $p$-group to separate its elements;
they cannot do so. Permutation characters provide the $p$-element projector, and
monomiality enters only afterward.

### 2.4 Integral Brauer induction

Let $R(G)$ be the integral character lattice with its orthonormal basis
$\operatorname{Irr}(G)$. Let $X$ be the sublattice generated by

$$
\operatorname{Ind}_H^G\theta
\tag{2.3}
$$

for elementary $H$ and linear $\theta$.

**Theorem 2.4 (integral Brauer induction).** One has $X=R(G)$. In particular, there are
elementary subgroups $H_i$, linear characters $\theta_i$, and integers $n_i$ such that

$$
\boxed{1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i.}
\tag{2.4}
$$

**Proof.** Define the dual lattice

$$
X^\vee=\{\varphi\in R(G)\otimes\mathbf Q:
\langle\varphi,x\rangle_G\in\mathbf Z\text{ for all }x\in X\}.
$$

Take $\varphi\in X^\vee$. If $H$ is elementary and $\xi$ is irreducible on $H$,
Proposition 2.1 writes $\xi=\operatorname{Ind}_D^H\theta$, where $D\leq H$ is elementary.
Frobenius reciprocity gives

$$
\langle\operatorname{Res}_H^G\varphi,\xi\rangle_H
=\langle\varphi,\operatorname{Ind}_D^G\theta\rangle_G\in\mathbf Z.
$$

Thus every elementary restriction of $\varphi$ is a generalized character.
Theorem 2.3 gives $\varphi\in R(G)$, so $X^\vee=R(G)$. The lattice $R(G)$ is self-dual.
A proper full-rank sublattice has a strictly larger dual, while a lower-rank subgroup has a
nonlattice dual. Hence $X=R(G)$. Apply this to $1_G$. $\square$

Evaluating (2.4) at the identity gives the indispensable rank identity

$$
\sum_i n_i[G:H_i]=1.
\tag{2.5}
$$

The coefficients cannot all be nonnegative when $G$ is not elementary. Otherwise (2.5)
would force a nonzero term with $H_i=G$, contrary to the allowed subgroup class.

The precise form of Theorem 2.4 is what arithmetic needs. A decomposition using arbitrary
irreducible characters of the subgroups would not turn term by term into finite-order twists;
linearity of $\theta_i$ is what permits inflation to a one-dimensional Galois character and
passage through class field theory to a Hecke character. Elementary subgroups are simultaneously
large enough to generate the whole integral character lattice and small enough to be solvable.
Both features are essential.

Integrality is equally structural. A rational character identity can be cleared of
denominators, but the result is then an identity for a positive multiple $m1_G$, not for
$1_G$. Substitution would produce $m[r]$ at the distinguished place. Dividing its traces or
Euler factors by $m$ would leave the integral Grothendieck group, and a norm calculation would
no longer have integral irreducible coefficients. The passage from norm one to one coefficient
$\pm1$ in Chapter 7 would fail. Brauer induction is therefore stronger than the assertion that
$1_G$ lies in the rational span of induced linear characters.

The relation is not canonical. Different elementary subgroup lists and different characters
can represent $1_G$. Formal rank and determinant are relation independent because both are
homomorphisms out of the representation ring. Effectivity and the isomorphism class of an
effective constituent require the cross-relation Gram comparison of Corollary 7.3; they do not
follow merely because the two relations represent the same finite-group character before
arithmetic data are substituted.

### 2.5 Two diagnostic relations

For $S_3$, let $C_2$ be generated by a transposition, let $C_3=A_3$, and let
$\omega$ be a nontrivial character of $C_3$. On the classes
$1,(12),(123)$,

$$
\operatorname{Ind}_{C_2}^{S_3}1=(3,1,0),
\qquad
\operatorname{Ind}_{C_3}^{S_3}\omega=(2,0,-1).
$$

Therefore

$$
1_{S_3}=\operatorname{Ind}_{C_2}^{S_3}1-
\operatorname{Ind}_{C_3}^{S_3}\omega.
\tag{2.6}
$$

After tensoring by rank two, a six-dimensional positive term minus a four-dimensional term
has virtual rank two. No dimension argument proves that the four-dimensional term occurs
inside the six-dimensional term.

More generally, for

$$
D_{2p}=\langle r,s:r^p=s^2=1,\ srs=r^{-1}\rangle
$$

with $p$ odd and $\theta_j(r)=\zeta_p^j$,

$$
1_{D_{2p}}=
\operatorname{Ind}_{\langle s\rangle}^{D_{2p}}1-
\sum_{j=1}^{(p-1)/2}
\operatorname{Ind}_{\langle r\rangle}^{D_{2p}}\theta_j.
\tag{2.7}
$$

At a reflection the first term has value one and the others vanish. At $r^k\neq1$,
the sum of the induced characters is
$\sum_{j=1}^{p-1}\zeta_p^{jk}=-1$. At the identity the right side is
$p-(p-1)=1$. This proves the relation and displays both the negative signs and the required
cyclotomic coefficient field.

## 3. Induction, reciprocity, and Mackey theory

### 3.1 Finite-index induction

Let $J$ be an open subgroup of a profinite group $G$, and let $W$ be a finite-dimensional
continuous representation of $J$ over a characteristic-zero field $L$. Define

$$
\operatorname{Ind}_J^GW=L[G]\otimes_{L[J]}W.
\tag{3.1}
$$

Only finitely many cosets occur. Choosing representatives identifies the induced space with
$[G:J]$ copies of $W$; the $G$-action is a locally constant permutation of the copies
followed by the continuous $J$-action. Hence the induction is continuous and

$$
\dim\operatorname{Ind}_J^GW=[G:J]\dim W.
\tag{3.2}
$$

If $W$ is semisimple and its restriction to an open subgroup
$N\triangleleft G$ contained in $J$ is semisimple, then the induced representation is
semisimple. Its restriction to $N$ is a
finite direct sum of conjugates of $W|_N$. Any $N$-equivariant projection onto a
$G$-stable subspace can be averaged over $G/N$, in characteristic zero, to give a
$G$-equivariant projection.

### 3.2 The tensor identity and determinants

For a $G$-representation $V$,

$$
V\otimes\operatorname{Ind}_J^GW
\simeq
\operatorname{Ind}_J^G(V|_J\otimes W).
\tag{3.3}
$$

The map

$$
v\otimes(g\otimes w)\longmapsto g\otimes(g^{-1}v\otimes w)
$$

is well defined, $G$-equivariant, and has the evident inverse. This is the projection
formula that will recover the distinguished member.

For determinants, let $r=\dim W$. Decompose the permutation of $G/J$ made by $g$ into
cycles. If a cycle has representative $tJ$ and length $d$, its internal product is
$t^{-1}g^dt\in J$. A block determinant gives

$$
\det\operatorname{Ind}_J^GW
=\operatorname{sgn}_{G/J}^{\,r}\operatorname{Ver}_J^G(\det W),
\tag{3.4}
$$

where the transferred character is the product of the internal values over all cycles.
In particular, for a character $\chi$ of $G$,

$$
\operatorname{Ver}_J^G(\chi|_J)=\chi^{[G:J]}.
\tag{3.5}
$$

The same finite block proof applies to open subgroups of profinite groups.

### 3.3 Frobenius reciprocity

Evaluation at $1\otimes W$ gives

$$
\operatorname{Hom}_G(\operatorname{Ind}_J^GW,V)
\simeq\operatorname{Hom}_J(W,V|_J).
\tag{3.6}
$$

The inverse sends a $J$-map $a$ to $g\otimes w\mapsto ga(w)$. At finite index,
induction and coinduction agree, so there is also

$$
\operatorname{Hom}_G(V,\operatorname{Ind}_J^GW)
\simeq\operatorname{Hom}_J(V|_J,W).
\tag{3.7}
$$

These adjunctions are the mechanism that converts the norm of a base-field induced
representation into Hom spaces over intersection fields.

### 3.4 Mackey decomposition

For open $H,J\leq G$, choose representatives of $H\backslash G/J$. Then

$$
\operatorname{Res}_H^G\operatorname{Ind}_J^GW
\simeq
\bigoplus_{x\in H\backslash G/J}
\operatorname{Ind}_{H\cap xJx^{-1}}^H
({}^xW)|_{H\cap xJx^{-1}}.
\tag{3.8}
$$

Indeed, decompose the $(H,J)$-biset $G$ into $HxJ$. For
$D=H\cap xJx^{-1}$, the map

$$
L[H]\otimes_{L[D]}{}^xW\longrightarrow
L[HxJ]\otimes_{L[J]}W,\qquad
h\otimes{}^xw\longmapsto hx\otimes w
$$

is well defined and is an isomorphism by dimension. Summing proves (3.8).

Combining (3.6), (3.8), and (3.7) gives the Hom form

$$
\begin{aligned}
\operatorname{Hom}_G(\operatorname{Ind}_H^GU,\operatorname{Ind}_J^GW)
\simeq
\bigoplus_{x\in H\backslash G/J}
\operatorname{Hom}_{H\cap xJx^{-1}}
(U,{}^xW).
\end{aligned}
\tag{3.9}
$$

All restrictions in the last line are implicit. Formula (3.9), not a pointwise
characteristic polynomial, sees the multiplicities needed for effectivity.

### 3.5 Fixed fields and local places

Let $M/F$ be finite Galois with group $\Gamma$, and let $F_H=M^H$. For
$H,J\leq\Gamma$ and $x\in\Gamma$,

$$
M^{H\cap xJx^{-1}}=F_H\,xF_J.
\tag{3.10}
$$

Thus the Mackey intersections are composita of conjugate fixed fields.

If $v$ is a place of $F$, choose a place $\widetilde v$ of $M$ and let
$D_v\leq\Gamma$ be its decomposition group. The places $w$ of $F_H$ above $v$ are
indexed by

$$
D_v\backslash\Gamma/H,
\tag{3.11}
$$

and for the place represented by $x$,

$$
(F_H)_w\simeq M_{\widetilde v}^{D_v\cap xHx^{-1}}.
\tag{3.12}
$$

Applying Mackey to decomposition groups yields

$$
\left.\operatorname{Ind}_{G_{F_H}}^{G_F}W\right|_{G_{F_v}}
\simeq
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{(F_H)_w}}^{G_{F_v}}W|_{G_{(F_H)_w}}.
\tag{3.13}
$$

This one formula controls prime counting, residue-degree Frobenius blocks, inertia,
monodromy, and local character twists.

## 4. Elementary intersections and solvable towers

### 4.1 Subgroups of elementary groups are subnormal

Mackey theory compares two induced terms on

$$
D=H_i\cap xH_jx^{-1}.
\tag{4.1}
$$

Any arithmetic comparison must therefore take place over $F_D=M^D$. The fact that $D$ need
not be normal in $H_i$ obstructs a one-step cyclic argument, but not the construction of a
prime-cyclic subnormal tower.

**Lemma 4.1.** Every subgroup of a finite elementary group admits a subnormal series to the
whole group with prime cyclic successive quotients.

**Proof.** First let $Q\leq P$ for a finite $p$-group. A proper subgroup of a finite
$p$-group is properly contained in its normalizer unless it is the whole group. To prove
this normalizer condition, let $Q$ act by left multiplication on the cosets $P/Q$.
The fixed cosets are precisely $N_P(Q)/Q$. The orbit congruence gives

$$
[P:Q]\equiv[N_P(Q):Q]\pmod p.
$$

If $Q<P$, the left side is divisible by $p$, and the identity coset is fixed; hence the
number of fixed cosets cannot be one and $N_P(Q)>Q$. Iterating normalizers gives

$$
Q=Q_0\triangleleft Q_1\triangleleft\cdots\triangleleft Q_s=P.
$$

Refine each $p$-group quotient by a composition series to obtain prime-order cyclic
quotients.

Now let $H=C\times P$ and $D=C'\times Q$ as in (2.2). Enlarge $C'$ to $C$ through
its cyclic composition series while keeping $Q$ fixed, then enlarge $Q$ to $P$ through
the series above while keeping $C$ fixed. Centrality of $C$ and normality at each
$p$-step give the required subnormal series. $\square$

### 4.2 Prime-cyclic towers to an overlap field

Let

$$
D=D_0\triangleleft D_1\triangleleft\cdots\triangleleft D_s=H
\tag{4.2}
$$

be the series from Lemma 4.1. Fixed fields reverse it:

$$
F_H=M^H\subset M^{D_{s-1}}\subset\cdots\subset M^{D_0}=F_D.
\tag{4.3}
$$

Each step is cyclic Galois of prime degree. This group-theoretic fact is not by itself an
automorphic theorem. If a packet $\pi_H$ is to be carried along (4.3), suppose separately
that the tower is ascent-admissible in the exact sense of the solvable theorem: every cuspidal
intermediate input remains in the selected local and trace-comparable range, while an allowed
two-character isobaric output is transported through later steps by character pullback. The
solvable base-change theorem then applies. Its endpoint is independent of the chosen
_admissible_ subnormal series and has, at every place, the restricted local parameter of
$\pi_H$.

This is the exact group-theoretic repair required by Mackey theory. The false obstruction was
to demand $D\triangleleft H$ and one Galois step. Elementary groups are nilpotent, so their
arbitrary subgroups admit a prime-cyclic tower. The arithmetic admissibility of that tower is
a separate hypothesis and must not be inferred from nilpotence.

### 4.3 A conditional overlap principle

**Theorem 4.2 (conditional intersection-field overlap).** Let $H\leq\Gamma$ be elementary and
$D\leq H$. Suppose cuspidal $\mathrm{GL}_2$ packets $\pi_H$ over $F_H$ and $\pi_D$ over
$F_D$ have already been constructed. Assume that one tower (4.3) is ascent-admissible for
$\pi_H$, that both packets have compatible semisimple Galois realizations, and that a fixed
two-dimensional representation $r$ of $G_F$ selects both packets at one coefficient place:

$$
r_{\pi_H,\lambda_0}\simeq r|_{G_{F_H}},
\qquad
r_{\pi_D,\lambda_0}\simeq r|_{G_{F_D}}.
\tag{4.3a}
$$

Assume also that $r|_{G_{F_D}}$ is absolutely irreducible and that strong multiplicity one
and compatibility of Galois realization with base change hold in the selected packet range.
Assume in addition that the algebraic good Hecke polynomials of the two packets have been placed
in one common number field and that $\lambda_0$ is induced by a fixed injective embedding of
that field. Then

$$
\boxed{\operatorname{BC}_{F_D/F_H}(\pi_H)\simeq\pi_D.}
\tag{4.4}
$$

Consequently, for every coefficient embedding $\tau$,

$$
\boxed{r_{\pi_H,\tau}|_{G_{F_D}}^{\mathrm{ss}}
\simeq r_{\pi_D,\tau}.}
\tag{4.5}
$$

**Proof.** Lemma 4.1 constructs a prime-cyclic tower, and the additional hypothesis makes it
admissible, so the left side of (4.4) exists. At the distinguished coefficient place,
compatibility of Galois realization with base change
gives

$$
r_{\operatorname{BC}_{F_D/F_H}(\pi_H),\lambda_0}
\simeq r|_{G_{F_D}}.
\tag{4.6}
$$

The left side is initially an automorphic isobaric representation. It is in fact cuspidal. If
it were a two-character isobaric sum, its associated
semisimple Galois representation would be a sum of two characters. But
$r|_{G_{F_D}}$ is absolutely irreducible by hypothesis. This contradiction proves
cuspidality.

The selected packet $\pi_D$ has the same realization by (4.3a). Hence their good Hecke
polynomials agree: equality after the distinguished injective coefficient embedding is equality
of the algebraic coefficients. Strong multiplicity one identifies them, proving (4.4).

Compatibility of attached Galois representations with solvable base change now proves (4.5)
for every $\tau$; no density theorem is needed. $\square$

For a conjugation-compatible packet diagram and two elementary groups $H_i,H_j$, suppose that
the two required towers are admissible and
apply the theorem twice to $D=H_i\cap xH_jx^{-1}$, once inside $H_i$ and once inside
$xH_jx^{-1}$. The two routes to $F_D$ therefore meet at the same selected packet
$\pi_D$. An arithmetic construction may instead prove the semisimple overlap identity
directly, without asserting automorphic base change along either nonnormal route. The abstract
arguments below accept such an identity as an input.

### 4.4 Why top-field agreement is not enough

Suppose two irreducible representations of $G_{F_D}$ have the same **irreducible** restriction
to $G_M$. They can differ by a character of the finite quotient

$$
G_{F_D}/G_M\simeq D.
\tag{4.7}
$$

Thus equality only over $M$ does not determine the Hom space in Mackey's formula. Theorem
4.2 removes precisely this quotient-character ambiguity before the Brauer twists are inserted.
It does so by actual solvable base change on the intersection field, not by an identity after
further restriction to the top.

From this point onward, the **overlap hypothesis** means that (4.5), with its conjugate form,
holds for every intersection $H\cap xJx^{-1}$ occurring in the chosen Brauer datum and at every
coefficient embedding. Theorem 4.2 supplies it under its displayed automorphic hypotheses; a
separately proved comparison theorem may supply it instead. Elementary group theory and
top-field agreement alone do not.

## 5. Clifford theory and factor sets

Brauer induction organizes subgroups; Clifford theory organizes irreducible representations
relative to a normal subgroup. The two theories meet when all induced terms restrict to copies
of one top-field representation. Restriction remembers the common block but forgets how the
finite quotient acts on its multiplicity space. The missing action is projective in general, and
its factor set is the precise obstruction.

### 5.1 Homogeneous restriction

Let $G$ be a group, let $N\triangleleft G$ have finite index, and let $k$ be an
algebraically closed field of characteristic zero. The discussion applies to a profinite group
and an open normal subgroup because all coset sets remain finite. Let $V$ be a
finite-dimensional irreducible $k$-representation of $G$.

Choose an irreducible $N$-subrepresentation $T\subset V$. Such a subrepresentation exists by
minimal dimension. For $g\in G$, the translate $gT$ is an irreducible
$N$-representation isomorphic to the conjugate

$$
{}^gT,\qquad {}^gT(n)=T(g^{-1}ng).
$$

The sum of the translates is $G$-stable and nonzero, hence is all of $V$. A sum of simple
submodules is semisimple, so $V|_N$ is semisimple. Its irreducible constituents form one
$G$-orbit, and conjugation transports multiplicity spaces isomorphically. We obtain the
homogeneous restriction formula

$$
V|_N\simeq
e\bigoplus_{g\in G/I}{}^gT,
\tag{5.1}
$$

where

$$
I=I_G(T)=\{g\in G:{}^gT\simeq T\}
\tag{5.2}
$$

is the inertia, or stabilizer, group of the isomorphism class of $T$, and $e\geq1$ is a
common multiplicity.

This is the first form of Clifford's theorem. It has two useful consequences. First, an
irreducible representation need not remain irreducible on a normal subgroup. Second, if
$T$ is $G$-invariant, then

$$
V|_N\simeq T^{\oplus e}.
\tag{5.3}
$$

The integer $e$ is not automatically one. It measures a projective quotient action which
restriction to $N$ cannot see.

The argument did not invoke complete reducibility of the whole category of continuous
representations of a profinite group. That category need not be semisimple over a $p$-adic
field: continuous unipotent representations exist. Semisimplicity of (5.1) follows instead from
the irreducibility of $V$, normality of $N$, and finite index.

### 5.2 The inertia group and the Clifford correspondence

Let $V_T$ be the $T$-isotypic part of $V|_N$, the sum of all $N$-submodules
isomorphic to $T$. It is stable under $I$. Denote it by $U$ when regarded as an
$I$-representation. Then

$$
U|_N\simeq T^{\oplus e}.
\tag{5.4}
$$

The translates of $U$ indexed by $G/I$ are the distinct isotypic pieces in (5.1). Therefore
the natural map

$$
\operatorname{Ind}_I^G U\longrightarrow V,\qquad
g\otimes u\longmapsto gu,
\tag{5.5}
$$

is an isomorphism. Moreover, $U$ is irreducible as an $I$-representation. An
$I$-subrepresentation would induce to a nonzero proper $G$-subrepresentation of $V$.

Conversely, suppose $U$ is an irreducible $I$-representation whose restriction to $N$
is a positive multiple of $T$. Mackey theory gives

$$
\operatorname{End}_G(\operatorname{Ind}_I^G U)
\simeq
\bigoplus_{x\in I\backslash G/I}
\operatorname{Hom}_{I\cap xIx^{-1}}(U,{}^xU).
\tag{5.6}
$$

For $x\notin I$, the two restrictions contain nonisomorphic $N$-constituents $T$ and
${}^xT$, so the corresponding Hom space vanishes. The identity double coset contributes
$\operatorname{End}_I(U)=k$. Thus the induced representation has scalar endomorphisms.
Its restriction to $N$ is semisimple, so Section 3.1 makes the induced representation
semisimple. A nontrivial semisimple decomposition would have at least two independent
idempotents; (5.6) therefore forces irreducibility. This gives
the **Clifford correspondence**:

$$
\left\{
\begin{array}{c}
\text{irreducible $G$-representations}\\
\text{whose restriction contains $T$}
\end{array}
\right\}
\longleftrightarrow
\left\{
\begin{array}{c}
\text{irreducible $I$-representations}\\
\text{lying over $T$}
\end{array}
\right\},
\tag{5.7}
$$

with induction and passage to the $T$-isotypic component as inverse operations.

Formula (5.7) is often more useful than a character table. It separates orbit motion, controlled
by $G/I$, from multiplicity over the invariant block, controlled by $I/N$.

### 5.3 The projective multiplicity representation

Assume now that $T$ is invariant under $I$, which is automatic by the definition of $I$.
Choose representatives $s(q)$ for $q\in I/N$, with $s(1)=1$, and choose intertwiners
$P_{s(q)}:T\to T$, with $P_{s(1)}=1$, satisfying

$$
P_{s(q)}T(n)P_{s(q)}^{-1}=T(s(q)ns(q)^{-1})
\qquad(n\in N),
\tag{5.8}
$$

Put $P_{s(q)n}=P_{s(q)}T(n)$. This fixes the interaction with $N$. For
$q,r\in I/N$, write the right-section defect as

$$
\begin{aligned}
s(q)s(r)&=s(qr)\nu(q,r),\qquad \nu(q,r)\in N,\\
P_{s(q)}P_{s(r)}
&=\alpha(q,r)P_{s(qr)}T(\nu(q,r)).
\end{aligned}
\tag{5.9}
$$

The second equality holds for a unique scalar $\alpha(q,r)\in k^\times$, because both sides
implement conjugation by $s(q)s(r)$ on $T(N)$. Equivalently, the extension of the $P$'s above
satisfies $P_gP_h=\alpha(\bar g,\bar h)P_{gh}$ for arbitrary $g,h\in I$, where bars denote
classes in $I/N$. Associativity gives

$$
\alpha(q,r)\alpha(qr,t)
=\alpha(r,t)\alpha(q,rt).
\tag{5.10}
$$

Thus $\alpha$ is a normalized two-cocycle on $I/N$, with the trivial action on
$k^\times$. Replacing $P_{s(q)}$ by $b(q)P_{s(q)}$ replaces $\alpha$ by

$$
\alpha'(q,r)=
\frac{b(q)b(r)}{b(qr)}\alpha(q,r).
\tag{5.11}
$$

Thus the cohomology class

$$
[\alpha_T]\in H^2(I/N,k^\times)
\tag{5.12}
$$

depends only on the invariant isomorphism class of $T$. It is the **Clifford obstruction**.

Now let $U$ be the $I$-representation in (5.4) and put

$$
W=\operatorname{Hom}_N(T,U).
\tag{5.13}
$$

Evaluation gives an $N$-equivariant isomorphism $T\otimes W\simeq U$. To make evaluation
$I$-equivariant, $W$ must carry a projective action with inverse factor set:

$$
Q_qQ_r=\alpha(q,r)^{-1}Q_{qr}.
\tag{5.14}
$$

Then $P_g\otimes Q_{\bar g}$ is an honest action on $T\otimes W$. In particular,

$$
e=\dim W.
\tag{5.15}
$$

This explains the multiplicity in Clifford theory. The quotient need not act honestly on the
top block $T$ or on the multiplicity space $W$; the two projective errors cancel.

Equivalently, $W$ is a module for the twisted group algebra
$k^{\alpha^{-1}}[I/N]$. The multiplication in this algebra is

$$
[u_q][u_r]=\alpha(q,r)^{-1}[u_{qr}].
\tag{5.16}
$$

Irreducible representations lying over $T$ correspond to irreducible modules for this twisted
group algebra. Ordinary characters of $I/N$ act by tensor product on the set of such modules,
but they need not act transitively when the multiplicity dimension exceeds one.

### 5.4 Extension, obstruction, and twisting ambiguity

An **extension** of $T$ to $I$ is an honest $I$-representation $\widetilde T$ on the
same vector space whose restriction to $N$ is $T$.

**Proposition 5.1 (extension criterion).** The invariant representation $T$ extends to $I$
if and only if $[\alpha_T]=0$ in $H^2(I/N,k^\times)$. When extensions exist, their
isomorphism classes form a torsor under

$$
\operatorname{Hom}(I/N,k^\times).
\tag{5.17}
$$

**Proof.** If $[\alpha_T]=0$, choose $b$ in (5.11) so that the new factor set is one.
Then $g\mapsto b(g)P_g$ is an honest representation extending $T$. Conversely, an extension
itself supplies intertwiners with factor set one, so the class vanishes.

If $\widetilde T$ and $\widetilde T'$ are two extensions, then
$\widetilde T'(g)\widetilde T(g)^{-1}$ commutes with $T(N)$. Schur's lemma makes it a
scalar $\chi(g)$. The representation laws make $\chi$ a character, and it is trivial on
$N$. Conversely every such twist is another extension. The action is free and transitive.
$\square$

A cyclic quotient is a useful special case. For algebraically closed $k$, every element has
an $n$-th root, and the usual cyclic presentation shows

$$
H^2(C_n,k^\times)=0.
\tag{5.18}
$$

Thus an invariant irreducible representation extends across one cyclic layer. Its extensions
differ by characters of that cyclic quotient. This algebraic fact is the representation-theoretic
shadow of the twisting fiber in cyclic automorphic descent. It does not prove the automorphic
existence theorem, whose analytic and local hypotheses remain separate.

For a noncyclic quotient the obstruction can be nonzero. Let $G=Q_8$, let
$N=\{\pm1\}$, and let $T$ be the character with $T(-1)=-1$. It is $G$-invariant.
It cannot extend to a one-dimensional character of $Q_8$, because every such character kills
the commutator subgroup $\{\pm1\}$. Hence its class in

$$
H^2(Q_8/N,k^\times)=H^2(C_2\times C_2,k^\times)
$$

is nonzero. The usual two-dimensional irreducible representation of $Q_8$ nevertheless
restricts to $T^{\oplus2}$. Its two-dimensional multiplicity space carries the inverse
projective action. This example proves two warnings at once:

- invariance of $T$ does not imply extension; and
- the existence of an honest representation restricting to $T^{\oplus e}$ does not force
  the obstruction of $T$ to vanish when $e>1$.

If $e=1$, however, the multiplicity projective representation is one dimensional. Its inverse
factor set is a coboundary, so $[\alpha_T]=0$. An irreducible representation whose restriction
is exactly $T$ is therefore an actual extension of $T$.

### 5.5 Cyclic and solvable descent

The factor-set calculation clarifies, but does not replace, solvable automorphic descent. At one
cyclic step, an invariant irreducible Galois representation has extensions and they differ by
quotient characters. Global class field theory turns those finite Galois characters into
finite-order Hecke characters. The cyclic automorphic descent theorem constructs a nonempty
descent fiber only in its admissible range; compatibility with Galois realization then selects
the twist matching a prescribed extension.

Through a solvable tower, making an arbitrary choice at each step can fail. A choice at one
layer must be invariant under the next quotient. When that quotient acts on the same descent
torsor, the displacement is a one-cocycle, and a fixed point exists precisely when its
cohomology class vanishes. The projective intertwiners of an invariant arithmetic parameter
give the related two-cocycle (5.12). These are different obstructions:

- $H^1$ measures a fixed point in a torsor of already existing descents;
- $H^2$ measures whether an invariant irreducible object admits coherent linear
  intertwiners.

An arithmetic representation already defined over the bottom field supplies coherent
intertwiners and selects compatible twists. Without it, one must verify the recursive descent
criterion directly. Full invariance at the top is not a substitute for those compatible
choices.

## 6. Substituting arithmetic data into a Brauer relation

The preceding chapters are purely representation theoretic. We now explain the exact formal
output obtained when coefficient-indexed Galois representations and automorphic packets are
available over elementary fixed fields. This is a template, not the construction of the
FLT-specific packet array.

### 6.1 A coefficient-indexed diagram

Let $M/F$ be finite Galois with group $\Gamma$, and put $F_H=M^H$. Fix a positive
integer $d$. Suppose that for every elementary subgroup $H$ in a finite conjugation-stable
list, enlarged to contain the intersections used below, and every coefficient embedding $\tau$,
there is a continuous semisimple representation

$$
V_{H,\tau}:G_{F_H}\longrightarrow\operatorname{GL}_d(\Omega_\tau).
\tag{6.1}
$$

The following pieces of structure are logically independent and should be listed separately.

1. **Field conjugation:** $V_{xHx^{-1},\tau}\simeq{}^xV_{H,\tau}$.
2. **Common determinant:** there is a character $\delta_\tau:G_F\to\Omega_\tau^\times$
   such that $\det V_{H,\tau}=\delta_\tau|_{G_{F_H}}$.
3. **Algebraic good data:** outside a fixed finite set, Frobenius polynomials are obtained from
   one algebraic coefficient ledger by applying $\tau$.
4. **Overlap:** for every $D=H\cap xJx^{-1}$ that occurs in Mackey theory, the two
   restrictions over $F_D$ are identified semisimply with one displayed representation.
5. **Distinguished member:** for one $\tau_0$, there is a semisimple representation
   $r_0:G_F\to\operatorname{GL}_d(\Omega_{\tau_0})$ with
   $V_{H,\tau_0}\simeq r_0|_{G_{F_H}}$.

Only item 5 is needed to recover the virtual class at $\tau_0$. The overlap item is needed
for Hom calculations at other embeddings. Algebraic good data are needed for common formal
Euler factors. None of the items implies the others.

In automorphic applications, a packet $\pi_H$ gives $V_{H,\tau}=r_{\pi_H,\tau}$.
Constructing all such packets, proving overlap on nonnormal intersection fields, and verifying
uniform local data are arithmetic theorems outside this template. In particular, this abstract
descent starts from the semisimple $V_{H,\tau}$ and supplied local objects; it has no operation
which recovers a nilpotent monodromy operator erased when a raw geometric representation is
globally semisimplified.

### 6.2 Finite characters and termwise operations

Choose an integral Brauer relation

$$
1_\Gamma=\sum_i n_i\operatorname{Ind}_{H_i}^{\Gamma}\theta_i,
\qquad n_i\in\mathbf Z,
\tag{6.2}
$$

where $H_i$ is elementary and $\theta_i$ is linear. Enlarge the common algebraic coefficient
field once, if necessary, to contain the values of
the finitely many $\theta_i$. Inflate $\theta_i$ along

$$
G_{F_i}\twoheadrightarrow
G_{F_i}/G_M\simeq H_i,
\qquad F_i=F_{H_i}.
\tag{6.3}
$$

After embedding its root-of-unity values by $\tau$, this gives a finite Galois character
$\theta_{i,\tau}$. Global class field theory gives a finite-order Hecke character
$\psi_i$ with the same unramified Frobenius values. Twisting compatibility, when available,
identifies

$$
r_{\pi_{H_i}\otimes\psi_i,\tau}
\simeq
V_{H_i,\tau}\otimes\theta_{i,\tau}.
\tag{6.4}
$$

Define the actual induced term

$$
A_{i,\tau}=
\operatorname{Ind}_{G_{F_i}}^{G_F}
\bigl(V_{H_i,\tau}\otimes\theta_{i,\tau}\bigr).
\tag{6.5}
$$

It has dimension $d[\Gamma:H_i]$. This induction is an honest Galois operation. On the
automorphic side, $\pi_{H_i}\otimes\psi_i$ is an honest packet over $F_i$. No global
automorphic representation over $F$ is produced by (6.5) when $F_i/F$ is nonnormal or when
only rank-two cyclic transfer is available.

### 6.3 The signed base-field class

Put

$$
\mathcal R_{\mathfrak B,\tau}
=\sum_i n_i[A_{i,\tau}]
\tag{6.6}
$$

in the semisimple Grothendieck group of $G_F$. If $n_i=n_i^+-n_i^-$, then

$$
R_\tau^\pm=\bigoplus_i A_{i,\tau}^{\oplus n_i^\pm},
\qquad
\mathcal R_{\mathfrak B,\tau}=[R_\tau^+]-[R_\tau^-].
\tag{6.7}
$$

At the distinguished embedding, the tensor identity gives

$$
\begin{aligned}
\mathcal R_{\mathfrak B,\tau_0}
&=\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_F}
(r_0|_{G_{F_i}}\otimes\theta_i)
\right]\\
&=[r_0]\cdot
\sum_i n_i
[\operatorname{Ind}_{G_{F_i}}^{G_F}\theta_i]
=[r_0].
\end{aligned}
\tag{6.8}
$$

The finite quotient $G_F/G_M$ identifies the last sum with (6.2). This is an equality of
semisimple virtual classes. No density theorem is needed.

At another coefficient embedding there is usually no representation $r_0$ to factor out.
Equation (6.8) therefore does not transport effectivity between embeddings. It supplies one
distinguished value against which a later, separately proved invariant such as a Gram matrix
may be compared.

The $S_3$ relation (2.6) is a compact diagnostic. Let $K_2$ and $K_3$ be the fixed fields of
a transposition subgroup and the alternating subgroup. For rank-$d$ source representations
$V_2$ and $V_3$, the formal expression is

## $$\operatorname{Ind}_{G_{K_2}}^{G_F}V_2

\operatorname{Ind}_{G_{K_3}}^{G_F}(V_3\otimes\omega).
\tag{6.8a}
$$

The positive term has rank $3d$, the negative term rank $2d$, and the virtual rank is $d$.
At a distinguished embedding where $V_2$ and $V_3$ are restrictions of one $r_0$, the tensor
identity proves that (6.8a) is $[r_0]$. At any other embedding, the dimension calculation says
only $3d-2d=d$. It gives no map from the negative term to the positive term. In the Gram
matrix, the cross term is computed over the top field because

$$
C_2\cap xC_3x^{-1}=1.
$$

The self-pairing of the cubic-field term also has a nontrivial double coset with trivial
intersection. Thus even this smallest example requires comparisons on every Mackey overlap;
checking only the two parent fields or only the diagonal endomorphism rings misses the
cancellation mechanism.

### 6.4 Rank and determinant

Evaluating (6.2) at the identity gives

$$
\sum_i n_i[\Gamma:H_i]=1.
\tag{6.9}
$$

Consequently

$$
\dim\mathcal R_{\mathfrak B,\tau}=d.
\tag{6.10}
$$

This is virtual dimension. It says neither that the negative terms cancel nor that an actual
$d$-dimensional representation exists.

The determinant calculation is stronger but still virtual. For a finite-index subgroup
$J\leq G$ and a rank-$d$ representation $W$,

$$
\det\operatorname{Ind}_J^G W
=\operatorname{sgn}_{G/J}^{\,d}
\operatorname{Ver}_J^G(\det W).
\tag{6.11}
$$

Applying determinant to the one-dimensional identity (6.2) gives

$$
\prod_i
\left(
\operatorname{sgn}_{\Gamma/H_i}
\operatorname{Ver}_{H_i}^{\Gamma}\theta_i
\right)^{n_i}
=1.
\tag{6.12}
$$

Because

$$
\det(V_{H_i,\tau}\otimes\theta_i)
=\delta_\tau|_{G_{F_i}}\theta_i^d,
$$

formulas (6.9), (6.11), and (6.12) yield

$$
\begin{aligned}
\det\mathcal R_{\mathfrak B,\tau}
&=
\delta_\tau^{\sum_i n_i[\Gamma:H_i]}
\prod_i
\left(
\operatorname{sgn}_{\Gamma/H_i}
\operatorname{Ver}_{H_i}^{\Gamma}\theta_i
\right)^{dn_i}\\
&=\boxed{\delta_\tau}.
\end{aligned}
\tag{6.13}
$$

The formula works in every rank $d$; the permutation sign and transfer character cancel
together because they are the determinant of the original induced character. Separating them
and forgetting one is a common source of a spurious quadratic character.

Until effectivity is proved, (6.13) is a determinant character of a virtual class: determinants
of positive terms are divided by determinants of negative terms. It is not yet the determinant
of an actual rank-$d$ representation.

### 6.5 Frobenius blocks and formal Euler factors

Let $v$ be a finite place of $F$ at which the extension, source representations, and
characters in one term are unramified. For $w\mid v$ in $F_i$, let
$f_w=f(w/v)$, and let $\alpha_{i,w,1},\ldots,\alpha_{i,w,d}$ be the arithmetic-Frobenius
eigenvalues of $V_{H_i,\tau}\otimes\theta_{i,\tau}$ at $w$.

On the coset block belonging to $w$, $\operatorname{Frob}_v$ acts in a cycle of length
$f_w$, and its $f_w$-th power acts internally as $\operatorname{Frob}_w$. Hence

# $$\det(1-\operatorname{Frob}_vT\mid A_{i,\tau})

\prod_{w\mid v}\prod_{j=1}^d
(1-\alpha_{i,w,j}T^{f_w}).
\tag{6.14}
$$

For an inert quadratic place, only powers $T^2$ occur and the trace of
$\operatorname{Frob}_v$ on the induced term is zero. The source trace belongs to
$\operatorname{Frob}_v^2$. Ramification affects inertia and conductors; it does not replace
the residue degree in (6.14).

Taking the signed product gives a rational function

$$
D_{v,\mathfrak B,\tau}(T)=
\prod_i
\det(1-\operatorname{Frob}_vT\mid A_{i,\tau})^{n_i}.
\tag{6.15}
$$

If the local factors arise from one algebraic coefficient field, this is the image under
$\tau$ of an algebraic rational function. At the distinguished embedding, (6.8) identifies
it with the characteristic series of $r_0$. Injectivity of the coefficient embedding may then
show that the algebraic rational function is actually a degree-$d$ polynomial.

Polynomiality is still not effectivity. A quotient of determinants can cancel to a polynomial
while the negative representation has an irreducible constituent absent from the positive one.
Likewise, the associated equality of partial Euler products is Artin formalism for a virtual
class, not the construction of an automorphic representation over $F$.

## 7. What can make a virtual class effective

Brauer induction supplies integrality but not positivity. This chapter proves the general
criteria which can bridge that gap. Their arithmetic hypotheses—especially the comparison of
every Mackey intersection—must be verified elsewhere in each application.

### 7.1 The character norm

Let $\Omega$ be algebraically closed of characteristic zero. In the semisimple Grothendieck
group of a group $G$, write

$$
X=\sum_S c_S[S],
\qquad c_S\in\mathbf Z,
\tag{7.1}
$$

where $S$ runs over continuous irreducible representations occurring in the finite list under
consideration. Define

$$
\langle[V],[W]\rangle_G
=\dim_\Omega\operatorname{Hom}_G(V,W)
\tag{7.2}
$$

and extend bilinearly. Schur's lemma gives

$$
\langle X,X\rangle_G=\sum_S c_S^2.
\tag{7.3}
$$

This nonnegative integer is the **character norm** of $X$. It is an algebraic Hom
calculation; no averaging over an infinite profinite group is involved.

**Lemma 7.1 (norm-one sign lemma).** If $\langle X,X\rangle=1$, then
$X=[S]$ or $X=-[S]$ for one irreducible $S$. If also $\dim X=d>0$, then
$X=[S]$ and $\dim S=d$.

**Proof.** The integer squares in (7.3) sum to one, so exactly one coefficient is $1$ or
$-1$. Positive virtual dimension excludes the negative sign and determines the dimension.
$\square$

The lemma is deliberately conditional. Virtual dimension $d$, determinant $\delta$, and
degree-$d$ Frobenius polynomials do not imply norm one.

There is already a finite-group warning in rank one. Let $G=C_2$ and let $\varepsilon$ be its
nontrivial character. The virtual class

$$
X=2[1]-[\varepsilon]
\tag{7.3a}
$$

has positive virtual dimension one and virtual determinant $\varepsilon$, exactly the
determinant of the actual character $\varepsilon$. Nevertheless $X\ne[\varepsilon]$ and is
not effective: its irreducible coefficient vector is $(2,-1)$ and its norm is five. Rank and
determinant therefore cannot see the negative multiplicity even in the smallest character
ring.

### 7.2 The Mackey Gram matrix

For the terms (6.5), define

$$
G_\tau(i,j)=
\dim\operatorname{Hom}_{G_F}(A_{i,\tau},A_{j,\tau}).
\tag{7.4}
$$

Then

# $$\langle\mathcal R_{\mathfrak B,\tau},\mathcal R_{\mathfrak B,\tau}\rangle

\sum_{i,j}n_in_jG_\tau(i,j).
\tag{7.5}
$$

Frobenius reciprocity and Mackey decomposition give the exact entrywise formula

$$
\begin{aligned}
G_\tau(i,j)=
\sum_{x\in H_i\backslash\Gamma/H_j}
\dim\operatorname{Hom}_{G_{F_{D_x}}}\bigl(
&V_{H_i,\tau}|_{G_{F_{D_x}}}\otimes
\theta_{i,\tau}|_{D_x},\\
&{}^xV_{H_j,\tau}|_{G_{F_{D_x}}}\otimes
{}^x\theta_{j,\tau}|_{D_x}
\bigr),
\end{aligned}
\tag{7.6}
$$

where

$$
D_x=H_i\cap xH_jx^{-1}.
\tag{7.7}
$$

Suppose the overlap hypothesis identifies both untwisted restrictions with one irreducible
$V_{D_x,\tau}$. Put

$$
\delta_{ij,x}=

({}^x\theta_j)|_{D_x}\,
(\theta_i|_{D_x})^{-1}.
\tag{7.8}
$$

Then (7.6) becomes

$$
G_\tau(i,j)=
\sum_x
\dim\operatorname{Hom}_{G_{F_{D_x}}}
\left(
V_{D_x,\tau},
V_{D_x,\tau}\otimes\delta_{ij,x,\tau}
\right).
\tag{7.9}
$$

If the overlap representation is absolutely irreducible, each summand is zero or one. It is
one precisely when $\delta_{ij,x,\tau}$ is a self-twist. Determinants show that a self-twist
of a rank-$d$ representation satisfies $\delta^d=1$, but that necessary condition is not
sufficient.

Formula (7.9) locates all the arithmetic work. Agreement only on $G_M$ cannot replace it,
because quotient characters of $D_x$ disappear on $G_M$. A comparison of diagonal terms
cannot replace it, because the cross terms are where positive and negative summands cancel.
Good Frobenius polynomials can identify two already existing semisimple representations when a
density and recognition theorem applies; they do not manufacture the Hom spaces by themselves.

### 7.3 The abstract norm-one criterion

The most reusable effectivity statement is now formal.

**Theorem 7.2 (abstract effectivity criterion).** Let $T$ be a set of coefficient embeddings.
For each $\tau\in T$, let

$$
X_\tau=\sum_i n_i[A_{i,\tau}]
$$

be an integral virtual semisimple representation, with the same integers $n_i$. Assume:

1. $\dim X_\tau=d>0$ for every $\tau$;
2. every Gram entry
   $\dim\operatorname{Hom}(A_{i,\tau},A_{j,\tau})$ is independent of $\tau$; and
3. for one distinguished $\tau_0$, $X_{\tau_0}=[r_0]$ with $r_0$ irreducible.

Then for every $\tau$ there is a unique irreducible isomorphism class $r_\tau$ of
dimension $d$ such that

$$
X_\tau=[r_\tau].
\tag{7.10}
$$

If $X_\tau=[R_\tau^+]-[R_\tau^-]$, then

$$
R_\tau^+\simeq r_\tau\oplus R_\tau^-
\tag{7.11}
$$

as semisimple representations.

**Proof.** By the Gram formula, the norm of $X_\tau$ is independent of $\tau$. At
$\tau_0$ it is $\dim\operatorname{End}(r_0)=1$. Lemma 7.1 and positive dimension give
(7.10). Equality in a free abelian group on irreducible classes is equality of multiplicities,
which gives (7.11). $\square$

Theorem 7.2 does not assert that its hypotheses hold for a potential-automorphy construction.
In the FLT chain, proving overlap, identifying self-twists, and showing entrywise coefficient
independence are the effectivity theorem's work, not formal consequences imported here.

The same idea compares two Brauer presentations.

**Corollary 7.3 (conditional presentation independence).** Let $X_\tau$ and $Y_\tau$ be two
integral virtual constructions. If every Gram entry in the combined list of their summands is
independent of $\tau$, and $X_{\tau_0}=Y_{\tau_0}$, then
$X_\tau=Y_\tau$ for every $\tau$.

**Proof.** Apply the combined Gram calculation to $X_\tau-Y_\tau$. Its norm is independent of
$\tau$ and is zero at $\tau_0$. Positive definiteness of (7.3) makes the difference zero.
$\square$

Again, cross-relation overlap is a hypothesis. Independence of one relation does not compare
two different lists automatically.

### 7.4 Coefficient descent and the Schur obstruction

Effectivity over an algebraic closure is not a model over the desired coefficient field. We now
prove the general multiplicity-one lemma which explains when a signed equality does kill that
obstruction.

Let $k$ be a characteristic-zero field, let $\bar k$ be an algebraic closure, and let
$V^+,V^-$ be finite-dimensional semisimple $k$-representations of a group $G$. The image
of $k[G]$ in $\operatorname{End}_k(V^+\oplus V^-)$ is a finite-dimensional algebra $A$.
After quotienting its radical, Wedderburn theory writes

$$
A/\operatorname{rad}(A)
\simeq
\prod_a M_{n_a}(D_a),
\tag{7.12}
$$

where $D_a$ is a division algebra finite over its center.

After scalar extension to $\bar k$, a simple $k$-module yields a Galois orbit of absolutely
simple modules. Each orbit member occurs with a common multiplicity $m_a$, the Schur index of
the corresponding division algebra. Therefore every class obtained by scalar extension from
the $k$-Grothendieck group has two properties:

- its coefficient is constant on each Galois orbit of absolutely simple modules; and
- that common coefficient is divisible by the corresponding Schur index.

**Theorem 7.4 (multiplicity-one coefficient descent).** Suppose

$$
[V^+\otimes_k\bar k]-[V^-\otimes_k\bar k]=[S]
\tag{7.13}
$$

for one absolutely irreducible $\bar k$-representation $S$. Then $S$ has a
$k$-model $S_0$, unique up to $k$-isomorphism, and

$$
V^+\simeq S_0\oplus V^-
\tag{7.14}
$$

as semisimple $k$-representations.

**Proof.** In (7.13), $S$ has coefficient one and every other absolutely simple module has
coefficient zero. Orbit constancy forces the Galois orbit of $S$ to have one element.
Schur-index divisibility forces its Schur index to divide one, hence to be one. Thus the
corresponding factor in (7.12) is split and supplies a $k$-model $S_0$.

Scalar extension is injective on the semisimple Grothendieck group after the orbit and Schur
multiplicities are retained. Hence (7.13) descends to
$[V^+]-[V^-]=[S_0]$, which is (7.14). Uniqueness follows from the unique simple factor in
that class. $\square$

There is a cocycle interpretation. If the isomorphism class of $S$ is Galois invariant,
choose semilinear intertwiners $u_\sigma:{}^\sigma S\to S$. Their products satisfy

$$
u_\sigma\,{}^\sigma u_\tau
=c(\sigma,\tau)u_{\sigma\tau}.
\tag{7.15}
$$

The scalar class of $c$ is the Schur obstruction. Theorem 7.4 says that coefficient one in a
virtual class already defined over $k$ forces this obstruction to vanish. After rescaling the
$u_\sigma$, they satisfy the descent cocycle condition.

The hypotheses are essential. A pointwise effective representation over every algebraic closure
need not be the scalar extension of a signed class over one completion. An invariant isomorphism
class can have nontrivial Schur index. The theorem supplies no canonical matrices, no preferred
descent intertwiners, and no coherence between different coefficient places. Those choices are
part of compatible-family assembly.

Two factor sets have appeared and should not be confused. The Clifford factor set (5.12) lies
in

$$
H^2(I/N,\bar k^\times).
\tag{7.15a}
$$

Its quotient is a group of field automorphisms of the top extension, and it asks whether an
irreducible representation of the normal subgroup extends to a larger arithmetic group. The
coefficient factor set (7.15) instead lies in

$$
H^2(\operatorname{Gal}(k'/k),(k')^\times)
\tag{7.15b}
$$

after a finite Galois field of definition $k'/k$ has been chosen. It asks whether matrices
already defined over $k'$ descend to $k$. The first changes the group acting on a fixed scalar space;
the second changes the scalars while keeping the arithmetic group fixed.

Either obstruction may vanish while the other survives. A representation can extend from
$G_M$ to $G_F$ over an algebraic closure and still have a nontrivial coefficient Schur class.
Conversely, a top-field representation can be defined over a small coefficient field while its
Clifford class prevents extension across the base-field quotient. Brauer's relation addresses
neither class merely by being integral. The norm-one argument produces an effective
algebraically closed constituent; Theorem 7.4 kills the coefficient obstruction only after a
smaller-field signed equality is available; an actual base-field arithmetic representation or
vanishing of (7.15a) handles the group-extension obstruction.

This separation also explains why “coefficient covariance” is weaker than coefficient descent.
Covariance says that applying a scalar automorphism transports one isomorphism class to its
conjugate. Descent asks for intertwiners satisfying the triple-overlap equation, which is
exactly the assertion that (7.15b) is a coboundary. A list of pairwise isomorphisms is not enough.

### 7.5 What Brauer induction does not prove

The results of this chapter can be summarized by a chain of strict implications:

$$
\begin{aligned}
&\text{integral Brauer identity}\\
&\quad\Longrightarrow
\text{integral virtual base-field class}\\
&\quad\not\Longrightarrow
\text{norm one}\\
&\quad\not\Longrightarrow
\text{a coefficient-field model without a $k$-defined signed equality}\\
&\quad\not\Longrightarrow
\text{a coherent compatible family}.
\end{aligned}
\tag{7.16}
$$

Even after (7.11), integral cancellation has not been proved. Over a finite extension of
$\mathbf Q_q$, the effective constituent has some stable lattice because its image is
compact. But a semisimple splitting need not preserve chosen lattices, and reducing (7.11)
modulo a uniformizer is not legitimate without an integral projector. Finite flatness,
crystallinity of a chosen lattice, and persistence of a residual monodromy class require
separate integral local theorems.

## 8. Automorphic meaning and its boundary

The phrase “descent of automorphy” is useful only if the automorphic and Galois operations are
kept distinct. Brauer induction organizes automorphically sourced Galois terms; it does not
silently enlarge the known range of automorphic transfer.

### 8.1 Solvable packet descent

Let $H\leq\Gamma$ be elementary. Since $M/F_H$ is solvable, the top packet may be
descended to $F_H$ when the exact hypotheses of solvable descent hold. These include an
admissible prime-cyclic tower, the required local extension fibers, control of cuspidality at
each step, and coherent choices in the successive twisting torsors.

An arithmetic representation already defined over $F_H$ can select the correct twists. At
one cyclic step, two irreducible extensions of the same irreducible top representation differ by
a quotient character, by Proposition 5.1. Twisting the arbitrary automorphic descent by the
corresponding finite-order Hecke character aligns its Galois realization with the prescribed
extension. Repeating this works only because the prescribed arithmetic representation extends
farther down and hence makes the selected descent invariant at the next layer.

If no extending arithmetic representation is supplied, automorphic data alone can still prove
descent, but each finite descent fiber must be checked recursively. Invariance of the top packet
under the full solvable group is not by itself a compatible chain.

The construction of a prime-cyclic subgroup chain in Chapter 4 proves none of these analytic
or packet-theoretic hypotheses. It merely provides the only possible shape of a solvable route.

### 8.2 No nonsolvable automorphic induction is hidden

For one term $A_{i,\tau}$, the local parameter at a place $v$ of $F$ is

$$
\bigoplus_{w\mid v}
\operatorname{Ind}_{W_{(F_i)_w}}^{W_{F_v}}
\operatorname{rec}_{(F_i)_w}
((\pi_{H_i}\otimes\psi_i)_w).
\tag{8.1}
$$

Artin formalism gives the partial standard $L$-function identity

# $$L_F^S(A_{i,\tau},s)

L_{F_i}^{S_{F_i}}(\pi_{H_i}\otimes\psi_i,s).
\tag{8.2}
$$

Equations (8.1)--(8.2) are honest local and Galois statements. They do not construct a global
automorphic representation of
$\operatorname{GL}_{d[F_i:F]}(\mathbf A_F)$. In particular, quadratic automorphic
induction of a character, cyclic base change for $\operatorname{GL}_2$, and induction of a
rank-$d$ Galois representation are three different operations.

After inserting the Brauer coefficients, one obtains a signed product

$$
\prod_i
L_{F_i}^{S_{F_i}}(\pi_{H_i}\otimes\psi_i,s)^{n_i}.
\tag{8.3}
$$

Before effectivity this is a quotient of $L$-functions. After effectivity its good factors
belong to an actual Galois representation. Neither stage produces a cuspidal packet over $F$.
A converse theorem would require analytic continuation, functional equations, boundedness, and
local data in a range not supplied by the character identity.

### 8.3 Local parameters and monodromy

Local Mackey theory is exact:

# $$\mathcal R_{\mathfrak B,\tau}|_{G_{F_v}}

\sum_i n_i\sum_{w\mid v}
\left[
\operatorname{Ind}_{G_{(F_i)_w}}^{G_{F_v}}
\left(
V_{H_i,\tau,w}\otimes\theta_{i,\tau,w}
\right)
\right].
\tag{8.4}
$$

Away from the coefficient residue characteristic, restriction, direct sum, finite induction,
and finite-order twist have corresponding operations on Frobenius-semisimple Weil--Deligne
pairs. The nilpotent operator is carried block by block. A finite-order scalar twist changes
the Weil action and leaves the displayed linear map $N$ unchanged; restriction and induction
do not authorize setting $N$ to zero.

If $v$ splits completely in $M$, every local field in (8.4) is $F_v$, and every
inflated quotient character is locally trivial. All terms then have the same local block,
provided the packet diagram actually supplies that block at every coefficient embedding. If an
effectivity theorem later gives an actual global cancellation, semisimple local cancellation
can recover one copy of the block. The nature of that block is an input: it may be unramified,
have a prescribed finite inertial type, or be special with nonzero rank-one $N$. The general
theorem favors none of these branches.

At a place above the coefficient residue characteristic, a Weil--Deligne slogan cannot replace
$p$-adic Hodge theory. A finite-order twist can alter crystallinity, and a stable
characteristic-zero lattice does not automatically have finite-flat quotients. No
coefficient-prime integral conclusion follows from (8.4).

### 8.4 Recognition is not existence

For completeness, we record the representation-recognition theorem used after actual
representations have been constructed.

**Theorem 8.1 (Brauer--Nesbitt).** Let $V,W$ be finite-dimensional representations of an
arbitrary group over a characteristic-zero field. If

$$
\operatorname{tr}V(g)=\operatorname{tr}W(g)
\qquad(g\in G),
\tag{8.5}
$$

then $V^{\mathrm{ss}}\simeq W^{\mathrm{ss}}$.

**Proof.** Extend scalars to an algebraic closure and let $A$ be the image of the group
algebra in $\operatorname{End}(V\oplus W)$. It is finite dimensional even when $G$ is
infinite. Its radical kills semisimple modules, and

$$
A/\operatorname{rad}(A)\simeq\prod_jM_{d_j}(k).
$$

Let $e_j$ be the central idempotent of the $j$-th factor. If the corresponding simple
module occurs with multiplicity $m_j$ in $V^{\mathrm{ss}}$, then
$\operatorname{tr}_V(e_j)=m_jd_j$. Trace equality on group elements extends linearly to
$A$, so the same number is obtained from $W$. Every multiplicity agrees. $\square$

For continuous representations of a profinite group, equality on a dense subset suffices by
continuity of trace. Applying this to Frobenius elements requires a density theorem and a common
finite exceptional set. The theorem compares two existing semisimple representations. It does
not turn a rational function of Euler factors or a virtual trace into a representation.

Strong multiplicity one has the same logical direction on the automorphic side. It recognizes
two existing cuspidal or isobaric representations from almost all local components. It does not
construct a base-field packet from a signed product.

## 9. The reusable descent package

### 9.1 The abstract theorem

We can now state the exact general result without importing any special packet array.

**Theorem 9.1 (abstract Brauer descent package).** Let $M/F$ be a finite Galois extension
with group $\Gamma$, and let $\mathfrak B$ be an integral elementary Brauer relation
(6.2). Suppose a finite coefficient-indexed diagram (6.1) has been supplied for every subgroup
and intersection occurring in $\mathfrak B$, with field conjugation, common determinant,
algebraic good data, and a distinguished representation $r_0$ as in Section 6.1. Then:

1. every subgroup intersection occurring in Mackey theory is elementary and admits a
   prime-cyclic subnormal tower to either parent;
2. the twists and finite Galois inductions form an integral virtual class
   $\mathcal R_{\mathfrak B,\tau}$ of virtual dimension $d$;
3. its virtual determinant is the common determinant $\delta_\tau$;
4. its unramified characteristic series is the signed product of the explicit
   residue-degree blocks (6.14);
5. at the distinguished embedding,
   $\mathcal R_{\mathfrak B,\tau_0}=[r_0]$;
6. the full Mackey Gram matrix is given by (7.6), and under the overlap hypothesis by the
   self-twist formula (7.9);
7. if those Gram entries are coefficient independent and $r_0$ is irreducible, Theorem 7.2
   makes the class effective at every embedding; and
8. if, at one coefficient completion, the signed equality is defined over that completion with
   multiplicity one after algebraic closure, Theorem 7.4 kills the Schur obstruction there.

Clauses 1--6 are formal consequences of the stated diagram. Clauses 7--8 are conditional
criteria, not automatic outputs of Brauer induction. No clause constructs the diagram,
verifies its overlaps, computes its self-twists, assembles its coefficient places, produces an
integral lattice cancellation, or constructs an automorphic representation over $F$.

**Proof.** Integral Brauer induction is Theorem 2.4. Finite-index induction, tensor identity,
determinant transfer, Frobenius reciprocity, Mackey theory, and the field dictionary are Chapter
3. Lemma 4.1 supplies the subgroup chains. Chapters 6--8 prove the remaining assertions in the
order stated. $\square$

### 9.2 Prerequisites and application boundary

The direct mathematical prerequisites of this general volume are narrow.

- Continuous cohomology supplies the language of one- and two-cocycles and their change by
  coboundaries.
- Weil--Deligne theory supplies restriction, finite induction, twisting, and retention of the
  monodromy operator in the local discussion.
- Finite-order Hecke characters and global reciprocity supply the avatars of the Brauer
  characters.
- Solvable base change and descent supply the automorphic operation along an _admissible_
  prime-cyclic tower, including its twisting ambiguity and local-parameter compatibility.
- The weight-two packet-system theorem supplies, when an application lies in its proved range,
  coefficient-indexed Galois realizations with algebraic good data. It does not supply an
  arbitrary elementary packet diagram or all of its overlaps.

Local coefficient fields, lattices, and finite-dimensional semisimple algebra provide
background, but the conditional arithmetic template uses only the compatible packet-system
output described above. Bad-place and integral local properties remain separate inputs when an
application asserts them. Likewise, geometric approximation, moduli constructions, and
residual potential automorphy are not premises of the abstract Brauer argument; in particular,
ordinary or Galois-refined approximation does not prove the automorphic selector hypotheses of
Section 8.1.

An FLT application still requires a controlled residual automorphic seed. For raw-to-global
preservation, semisimplicity of the ambient $H^1$ for every actual curve carrier, denoted
$(\mathrm{SS}_{\mathrm{array}})$, transfers the full signed SP pair, including $N$, at every
allowed coefficient embedding. Rational Tate-module semisimplicity $(\mathrm{TS})$ for the
carrier Jacobians is sufficient, but it is not established by the prerequisites here. The
abstract Brauer formalism cannot supply that arithmetic theorem, and it gives no Weil--Deligne
comparison at a base place equal to the coefficient residue characteristic. These are missing
inputs to the diagram of Section 6.1, not conclusions of the abstract theory.

A later application must therefore construct the controlled elementary-subfield packet array
and its nonnormal intersection identities, verify the self-twist Gram matrix and norm-one
effectivity, apply the Brauer--Nesbitt and rank-two trace criteria, and prove coefficient descent
over the actual completions. None of those conclusions is a premise of Theorem 9.1.

### 9.3 Failure tests

The theory is safe only if the following tests remain visible.

**A group-theoretic tower is not an automorphic tower.** Elementary nilpotence gives a
prime-cyclic chain. Every step must still satisfy the selected base-change hypotheses.

**Top agreement is not intersection agreement.** Two representations can agree on $G_M$ and
differ over $G_{F_D}$ by a character of $D$. Mackey Hom spaces see that character.

**Invariance is not descent data.** An invariant irreducible object has a factor set. It extends
only when its $H^2$-class vanishes.

**An honest representation above $T^{\oplus e}$ need not extend $T$.** A projective
multiplicity action can cancel a nontrivial factor set, as the $Q_8$ example shows.

**A rational Brauer relation is insufficient.** Denominators destroy the integral
multiplicity argument. Theorem 2.4 supplies an integral relation.

**Virtual rank and determinant are not positivity.** They know only two additive or
multiplicative invariants, not every irreducible coefficient.

**Polynomial cancellation is not a representation.** Negative Euler factors can cancel
algebraically before any negative constituent cancels.

**Norm one is not formal.** It requires every diagonal and cross Hom entry. The distinguished
embedding alone does not transport it.

**Pointwise effectivity is not coefficient descent.** A Galois-invariant isomorphism class can
have a Schur obstruction. Multiplicity one kills it only inside a signed class already defined
over the smaller coefficient field.

**Characteristic-zero cancellation is not integral cancellation.** Stable lattices exist
placewise, but no preferred lattice, finite-flat quotient, or residual extension follows.

**Recognition is not existence.** Brauer--Nesbitt, Chebotarev, and strong multiplicity one
compare objects that already exist.

**Galois effectivity is not base-field automorphy.** A signed automorphic $L$-function identity
does not supply a cuspidal packet or the analytic hypotheses of a converse theorem.

### 9.4 Conclusion

Brauer induction solves one problem and deliberately creates another. It replaces a
nonsolvable quotient by solvable elementary upper extensions, but it pays for that replacement
with negative coefficients. Integral character theory makes the subtraction exact; it does not
make it positive.

Mackey theory shows where positivity must be tested. Two induced terms meet over fixed fields of
subgroups $H\cap xJx^{-1}$. Elementary group theory supplies prime-cyclic routes to those
fields, while the arithmetic theory must separately prove that the relevant packet comparisons
exist. Clifford theory explains why restriction to the top field is too weak: quotient actions
survive as projective multiplicity representations, and their factor sets record genuine
descent obstructions.

Once an exact overlap diagram is available, every Gram entry becomes a finite Hom or self-twist
calculation. If those entries are independent of the coefficient embedding and one distinguished
class is irreducible, the common norm is one. Integrality and positive dimension then force one
actual irreducible constituent. If the signed equality is already defined over a smaller
coefficient field with multiplicity one, the same coefficient forces the Schur index and scalar
descent cocycle to vanish.

These are criteria, not a hidden construction of the FLT family. The elementary packet array,
its norm-one verification, and its coefficient-place assembly remain three downstream
achievements. Keeping them separate gives Brauer induction its correct reusable form: a precise
virtual descent mechanism, a complete account of its Clifford and cocycle obstructions, and
sharp hypotheses under which later arithmetic input can make the virtual class honest.
