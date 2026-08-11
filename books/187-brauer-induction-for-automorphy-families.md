# Brauer Induction for Automorphy Families

## Contents

1. [The descent problem and the exact endpoint](#1-the-descent-problem-and-the-exact-endpoint)
   - [Why ordinary descent is unavailable](#11-why-ordinary-descent-is-unavailable)
   - [The controlled input](#12-the-controlled-input)
   - [The virtual-family theorem](#13-the-virtual-family-theorem)
   - [Conventions](#14-conventions)
   - [Architecture of the proof](#15-architecture-of-the-proof)
2. [Characters, induction, and virtual linear algebra](#2-characters-induction-and-virtual-linear-algebra)
   - [Grothendieck groups and generalized characters](#21-grothendieck-groups-and-generalized-characters)
   - [Restriction and induction](#22-restriction-and-induction)
   - [The tensor identity](#23-the-tensor-identity)
   - [Ranks, determinant lines, and characteristic series](#24-ranks-determinant-lines-and-characteristic-series)
   - [Adjunction and transitivity](#25-adjunction-and-transitivity)
3. [Conjugation and Mackey decomposition](#3-conjugation-and-mackey-decomposition)
   - [Transport by conjugation](#31-transport-by-conjugation)
   - [The double-coset formula](#32-the-double-coset-formula)
   - [Normal subgroups and restriction to the top field](#33-normal-subgroups-and-restriction-to-the-top-field)
   - [The fixed-field translation](#34-the-fixed-field-translation)
   - [Two concrete Mackey calculations](#35-two-concrete-mackey-calculations)
   - [Worked decomposition groups and completed fixed fields](#36-worked-decomposition-groups-and-completed-fixed-fields)
   - [Two fixed fields and their composita](#37-two-fixed-fields-and-their-composita)
4. [Elementary subgroups and Brauer relations](#4-elementary-subgroups-and-brauer-relations)
   - [The correct elementary groups](#41-the-correct-elementary-groups)
   - [The local induction lemma](#42-the-local-induction-lemma)
   - [Integral Brauer induction](#43-integral-brauer-induction)
   - [Examples and nonexamples](#44-examples-and-nonexamples)
   - [A dihedral family of Brauer relations](#45-a-dihedral-family-of-brauer-relations)
5. [Refining a Brauer datum for arithmetic use](#5-refining-a-brauer-datum-for-arithmetic-use)
   - [Coefficient fields and one-dimensional avatars](#51-coefficient-fields-and-one-dimensional-avatars)
   - [Conjugate data](#52-conjugate-data)
   - [Determinants in a Brauer relation](#53-determinants-in-a-brauer-relation)
   - [Changing the relation](#54-changing-the-relation)
   - [Hecke fields, fields of definition, and centers](#55-hecke-fields-fields-of-definition-and-centers)
   - [A worked determinant cancellation](#56-a-worked-determinant-cancellation)
   - [Stabilizers of conjugate packet data](#57-stabilizers-of-conjugate-packet-data)
6. [The controlled field family from potential automorphy](#6-the-controlled-field-family-from-potential-automorphy)
   - [The Galois top and its fixed fields](#61-the-galois-top-and-its-fixed-fields)
   - [Automorphic packets over elementary fixed fields](#62-automorphic-packets-over-elementary-fixed-fields)
   - [Prime-cyclic descent and uniqueness](#63-prime-cyclic-descent-and-uniqueness)
   - [The local, coefficient, and overlap ledgers](#64-the-local-coefficient-and-overlap-ledgers)
   - [Automorphic restriction, twisting, and formal induction](#65-automorphic-restriction-twisting-and-formal-induction)
   - [A nonabelian elementary descent tower](#66-a-nonabelian-elementary-descent-tower)
   - [Sensitive places in the controlled top](#67-sensitive-places-in-the-controlled-top)
   - [Elementary subgroups inside the symmetric top](#68-elementary-subgroups-inside-the-symmetric-top)
7. [The induced virtual Galois family](#7-the-induced-virtual-galois-family)
   - [Construction at every coefficient place](#71-construction-at-every-coefficient-place)
   - [Recovery of the chosen member](#72-recovery-of-the-chosen-member)
   - [Rank and determinant](#73-rank-and-determinant)
   - [Continuity and semisimplification](#74-continuity-and-semisimplification)
   - [The S3 pattern over number fields](#75-the-s3-pattern-over-number-fields)
   - [Restriction back to the Galois top](#76-restriction-back-to-the-galois-top)
   - [Scalar extension and field-of-definition independence](#77-scalar-extension-and-field-of-definition-independence)
8. [Automorphic Euler data and Frobenius polynomials](#8-automorphic-euler-data-and-frobenius-polynomials)
   - [Local induction at a good prime](#81-local-induction-at-a-good-prime)
   - [The virtual Euler product](#82-the-virtual-euler-product)
   - [Polynomiality from the distinguished member](#83-polynomiality-from-the-distinguished-member)
   - [Coefficient conjugation](#84-coefficient-conjugation)
   - [Purity of the polynomial record](#85-purity-of-the-polynomial-record)
   - [Cubic splitting patterns in an induced Euler factor](#86-cubic-splitting-patterns-in-an-induced-euler-factor)
   - [The virtual L-function and its analytic boundary](#87-the-virtual-l-function-and-its-analytic-boundary)
   - [Frobenius powers and trace recurrences](#88-frobenius-powers-and-trace-recurrences)
9. [Lattices and integral bookkeeping](#9-lattices-and-integral-bookkeeping)
   - [Induced lattices](#91-induced-lattices)
   - [What a virtual lattice does and does not mean](#92-what-a-virtual-lattice-does-and-does-not-mean)
   - [The distinguished integral cancellation](#93-the-distinguished-integral-cancellation)
   - [Reduction and its boundary](#94-reduction-and-its-boundary)
   - [A characteristic-three lattice warning](#95-a-characteristic-three-lattice-warning)
   - [Determinant lattices and dual lines](#96-determinant-lattices-and-dual-lines)
10. [Local types through the Brauer construction](#10-local-types-through-the-brauer-construction)
    - [Restriction of Weil--Deligne data](#101-restriction-of-weil--deligne-data)
    - [The dyadic tame type](#102-the-dyadic-tame-type)
    - [Coefficient-prime finite-flat data](#103-coefficient-prime-finite-flat-data)
    - [Auxiliary ramification and the common bad set](#104-auxiliary-ramification-and-the-common-bad-set)
    - [Archimedean parameters and gamma factors](#105-archimedean-parameters-and-gamma-factors)
    - [Conductors under local induction](#106-conductors-under-local-induction)
    - [A type-by-type local ledger](#107-a-type-by-type-local-ledger)
11. [The complete virtual automorphy package](#11-the-complete-virtual-automorphy-package)
    - [Statement](#111-statement)
    - [Proof](#112-proof)
    - [Independence at the virtual level](#113-independence-at-the-virtual-level)
    - [Invariant-by-invariant verification](#114-invariant-by-invariant-verification)
12. [Failure modes, boundary, and conclusion](#12-failure-modes-boundary-and-conclusion)
    - [A virtual class is not an actual representation](#121-a-virtual-class-is-not-an-actual-representation)
    - [A polynomial is not effectivity](#122-a-polynomial-is-not-effectivity)
    - [Dependency audit](#123-dependency-audit)
    - [Conclusion](#124-conclusion)

## 1. The descent problem and the exact endpoint

### 1.1 Why ordinary descent is unavailable

Potential automorphy gives an automorphic representation only after passing to a finite totally
real extension. If that extension were solvable over the ground field, cyclic descent could be
applied one prime-degree layer at a time. The controlled field produced in Book 186 is instead
Galois with group

$$
\Gamma\simeq S_d\times C_2,
\qquad d\ge 5.
$$

The symmetric factor is deliberately large: it supplies closure-level disjointness and precise
local decomposition groups. It also prevents a solvable descent from the top field to
$\mathbf Q$. Ignoring this obstruction would hide the central difficulty.

Brauer induction changes the question. Rather than descending the top packet through the whole
group, it uses fixed fields $F_H=M^H$ for certain solvable subgroups $H\leq\Gamma$. The extension
$M/F_H$ is then solvable, so the exact packet over $M$ descends to $F_H$. A finite-group identity
reassembles the restrictions to these fields as a signed, induced object over $\mathbf Q$.

The word *signed* is decisive. An expression

$$
[V^+]-[V^-]
$$

in a Grothendieck group need not be represented by an honest two-dimensional representation,
even when its virtual dimension is two and its Frobenius characteristic series is a quadratic
polynomial. This book constructs and controls precisely that virtual object. It does not prove
positivity, irreducibility, or effectivity.

### 1.2 The controlled input

Fix a prime $\ell\ge 7$, a finite extension $E/\mathbf Q_\ell$ with ring of integers
$\mathcal O$, and the chosen representation of Book 186

$$
\rho:G_{\mathbf Q}\longrightarrow \operatorname{GL}_2(\mathcal O),
\qquad \det\rho=\chi_\ell.
\tag{1.1}
$$

It is unramified outside $\{2,\ell\}$, has the selected coefficient-linear finite-flat lattice
at $\ell$, and at $2$ has trivial wild inertia, zero monodromy, and tame inertia satisfying

$$
T^2+T+1=0.
\tag{1.2}
$$

Here $T$ is the image under $\rho$ of a chosen topological generator of the tame inertia
quotient at $2$. Replacing the generator by its inverse exchanges the two primitive
order-three eigenvalues and leaves the polynomial $T^2+T+1$ unchanged.

Book 186 constructs a totally real Galois extension $M/\mathbf Q$, disjoint from the prescribed
avoidance field, and a parallel-weight-two cuspidal packet $\pi_M$ such that

$$
\rho|_{G_M}\simeq r_{\pi_M,\lambda_0}
\tag{1.3}
$$

over a common finite extension of $\mathbf Q_\ell$. For every elementary subgroup
$H\leq\Gamma=\operatorname{Gal}(M/\mathbf Q)$ it also gives a uniquely selected packet $\pi_H$
over $F_H=M^H$ with

$$
\operatorname{BC}_{M/F_H}(\pi_H)=\pi_M,
\qquad
r_{\pi_H,\lambda_0}\simeq \rho|_{G_{F_H}}.
\tag{1.4}
$$

The selection includes central character, determinant, coefficient embeddings, stable lattices,
local types, and conjugation compatibility. These are inputs, not conclusions reconstructed from
good-prime traces. The simultaneous family has one further consequence that will be proved in
Section 6.4. If $D\leq H$ are elementary, then for every coefficient embedding $\tau$,

$$
\left(r_{\pi_H,\tau}|_{G_{M^D}}\right)^{\mathrm{ss}}
\simeq r_{\pi_D,\tau}.
\tag{1.4a}
$$

This is an identification over the intersection field $M^D$, not merely after a further
restriction to $G_M$.

### 1.3 The virtual-family theorem

The endpoint can now be stated without suggesting more than is proved.

**Theorem 1.1 (virtual automorphy family over the ground field).** There are elementary
subgroups $H_i\leq\Gamma$, one-dimensional finite-image characters
$\theta_i:H_i\to K^\times$, and integers $n_i$ such that

$$
1_\Gamma=\sum_i n_i\operatorname{Ind}_{H_i}^{\Gamma}\theta_i
\tag{1.5}
$$

in the character ring of $\Gamma$. Here $K$ is one number field containing all character values
and all coefficient fields of the finitely many packets involved. Let $\psi_i$ be the finite
order Hecke character of $F_i=F_{H_i}$ corresponding to $\theta_i$ through the quotient
$G_{F_i}\twoheadrightarrow H_i$ and global reciprocity. For every finite place $\lambda$ of
$K$, put

$$
\mathcal R_\lambda=
\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
\bigl(r_{\pi_{H_i},\lambda}\otimes\psi_{i,\lambda}\bigr)
\right]
\tag{1.6}
$$

in the Grothendieck group of continuous semisimple $\overline K_\lambda$-representations of
$G_{\mathbf Q}$.

This family has virtual rank two and determinant $\chi_\lambda$, where $\chi_\lambda$ is the
$\lambda$-adic cyclotomic character in the weight-two normalization. At the distinguished place
$\lambda_0\mid\ell$,

$$
\mathcal R_{\lambda_0}=[\rho\otimes_E\overline K_{\lambda_0}].
\tag{1.7}
$$

There is a finite set $S_0$ of rational primes, containing $2,\ell$ and every prime ramified in $M$
or in the packet levels, such that, whenever $p\notin S_0$ and $p$ differs from the residue
characteristic of $\lambda$, the virtual characteristic series of
$\mathcal R_\lambda(\operatorname{Frob}_p)$ is the image under
$K\hookrightarrow\overline K_\lambda$ of

$$
P_p^*(T)=1-a_pT+pT^2.
\tag{1.8a}
$$

Equivalently, its monic Frobenius characteristic polynomial is

$$
P_p(X)=X^2-a_pX+p\in K[X].
\tag{1.8}
$$

The two variables are reciprocal:
$P_p^*(T)=T^2P_p(T^{-1})$. Keeping this distinction is essential when an Euler factor is
obtained by substituting $T=p^{-s}$.

It is computed from the Hecke polynomials of the twisted packets over the $F_i$ by the explicit
residue-degree formula of Chapter 8. The formula is compatible with conjugating $H_i$, $F_i$,
$\pi_{H_i}$, $\theta_i$, and the coefficient embedding. At $2$ and $\ell$, the distinguished
member retains exactly the local records of (1.1)--(1.2). For general $\lambda$, the construction
retains the corresponding local data as a virtual induced record, with no assertion that it is
carried by an actual rank-two lattice.

After enlarging $K$ to contain the data of the finitely many elementary intersections of
conjugates of the $H_i$, formula (1.4a) holds for all of them and every embedding of $K$ into an
algebraically closed characteristic-zero nonarchimedean field. In particular, if

$$
D=H_i\cap xH_jx^{-1},\qquad L=M^D,
$$

then

$$
\left(r_{\pi_{H_i},\tau}|_{G_L}\right)^{\mathrm{ss}}
\simeq r_{\pi_D,\tau}
\simeq
\left({}^x r_{\pi_{H_j},\tau}|_{G_L}\right)^{\mathrm{ss}}.
\tag{1.8b}
$$

No assertion that $L/F_{H_i}$ or $L/x(F_{H_j})$ is Galois is made or needed.

### 1.4 Conventions

All representations are continuous and finite-dimensional over characteristic-zero fields. A
finite-group character is the trace of such a representation. The Grothendieck group uses direct
sum as addition. Induction is unnormalized on the Galois and finite-group sides. Automorphic
local parameters are translated to one convention before entering a formula. Book 95 and the
Frobenius records of Book 186 use arithmetic reciprocity, whereas the final transfer package of
Books 96--97 is stated with geometric reciprocity and geometric Frobenius. We make the
translation

$$
\operatorname{Frob}^{\mathrm{arith}}_v
=\left(\operatorname{Frob}^{\mathrm{geom}}_v\right)^{-1}
\tag{1.9}
$$

once and then use the arithmetic convention. Restriction of a Weil parameter is unchanged as
an operation; only the named Frobenius element is inverted. Thus a residue-degree-$f$ place
still uses the $f$th power, and finite-order twisting agrees on the Galois and automorphic
sides after this translation.

Arithmetic Frobenius is used throughout. Thus a weight-two representation with cyclotomic
determinant has good-prime characteristic polynomial $X^2-a_pX+p$. For $L/K$ a finite extension
of number fields and $w\mid v$, $f(w/v)$ denotes the residue degree.

### 1.5 Architecture of the proof

The argument has four logically distinct layers.

The first is finite-group theory. It proves an integral identity for $1_\Gamma$ using linear
characters of elementary subgroups. Integrality is essential because the output must live in a
Grothendieck group; a rational identity would require dividing a representation or taking
fractional powers of Euler factors. Mackey theory, transfer, and the tensor identity explain how
that finite relation behaves after restriction, induction, determinant, and conjugation.

The second layer is arithmetic input. For every elementary $H$, Book 186 supplies a packet
$\pi_H$ over $F_H$, selected so that its distinguished Galois realization is
$\rho|_{G_{F_H}}$. The finite character of $H$ becomes a Hecke character of $F_H$. This layer
is where solvability is used: $M/F_H$ admits a prime-cyclic tower, although
$F_H/\mathbf Q$ need not be normal or solvable in any useful sense.

The third layer substitutes the compatible Galois realizations of these twisted packets into the
Brauer expression at every coefficient place. Rank and determinant are formal consequences of
the finite relation. At $\lambda_0$, every summand is literally induced from a restriction of
$\rho$, so the tensor identity proves that the virtual class is $[\rho]$. At an arbitrary
$\lambda$, restriction back to $G_M$ is the actual top packet, but descent to
$G_{\mathbf Q}$ remains virtual.

The fourth layer compares Frobenius. At first, negative Brauer coefficients give a rational
function. The distinguished member shows that this rational function is one quadratic
polynomial in an embedded number field. Injectivity brings the equality back to the number
field and then forward to every coefficient completion. The same algebraic comparison, now
applied to two already existing packet realizations over an elementary intersection field,
gives equal almost-everywhere Frobenius polynomials there. Chebotarev and the
Brauer--Nesbitt character argument proved in Section 6.4 then give (1.4a). This recognizes
existing semisimple representations; it is not a constituent-by-constituent cancellation of the
virtual base-field family.

Each later compatibility follows one of these routes. Determinants use transfer, finite places
use local Mackey, real places use identical weight-two blocks, lattices are retained on the
actual summands, and coefficient conjugation acts on the algebraic record. None of these routes
contains a positivity theorem. That missing step is the exact boundary of the book.

## 2. Characters, induction, and virtual linear algebra

Brauer induction is an identity in a representation ring, so its arithmetic application is only
as reliable as the algebra of that ring. This chapter isolates four operations that will recur:
forming signed classes, inducing through a finite-index subgroup, tensoring an induced class by
a representation already defined downstairs, and taking determinant or Frobenius data of a
virtual class. The tensor identity is the bridge from a finite-group relation to the chosen
two-dimensional Galois representation; determinant lines and characteristic series are the
invariants that survive even before effectivity.

### 2.1 Grothendieck groups and generalized characters

Let $A$ be a field of characteristic zero and $G$ a finite group. The category of finite
dimensional $A[G]$-modules is semisimple after enlarging $A$ to a splitting field. Its
Grothendieck group $R_A(G)$ is generated by symbols $[V]$ subject to

$$
[V\oplus W]=[V]+[W].
$$

Tensor product makes $R_A(G)$ a ring. After passage to a splitting field, the character map

$$
R_A(G)\longrightarrow\{\text{class functions }G\to\overline A\}
$$

is injective.

Indeed, if $V=\bigoplus m_jV_j$ and $W=\bigoplus n_jV_j$ for pairwise nonisomorphic
irreducibles, character orthogonality gives

$$
m_j-n_j=\frac1{|G|}\sum_{g\in G}
(\chi_V(g)-\chi_W(g))\chi_{V_j}(g^{-1}).
$$

Equality of characters therefore gives equality of every multiplicity. An element of $R_A(G)$
is a **virtual representation**; its trace is a **generalized character**. Negative irreducible
multiplicities are legal in $R_A(G)$ but cannot occur in an actual representation.

The rank map

$$
\operatorname{rk}:R_A(G)\to\mathbf Z,
\qquad [V]-[W]\mapsto\dim V-\dim W
\tag{2.1}
$$

is evaluation of the generalized character at the identity.

### 2.2 Restriction and induction

For $H\leq G$, restriction is immediate. Induction can be modeled as

$$
\operatorname{Ind}_H^G W=A[G]\otimes_{A[H]}W.
\tag{2.2}
$$

Choose left-coset representatives $t_1,\ldots,t_m$ for $G/H$. Then
$t_j\otimes W$ gives a vector-space decomposition, proving

$$
\dim\operatorname{Ind}_H^GW=[G:H]\dim W.
\tag{2.3}
$$

The construction is additive and hence acts on Grothendieck groups. Its character is

$$
\chi_{\operatorname{Ind}_H^GW}(g)
=\frac1{|H|}\sum_{\substack{x\in G\\x^{-1}gx\in H}}
\chi_W(x^{-1}gx).
\tag{2.4}
$$

To prove (2.4), use the coset decomposition above. The trace of $g$ receives a contribution
from the summand $t_j\otimes W$ only when $gt_jH=t_jH$; on that summand the action is
$t_j^{-1}gt_j\in H$. Replacing the sum over fixed cosets by a sum over all their $|H|$
representatives gives the displayed formula.

### 2.3 The tensor identity

The identity that makes Brauer induction useful for a pre-existing two-dimensional
representation is

$$
V\otimes\operatorname{Ind}_H^GW
\simeq
\operatorname{Ind}_H^G(\operatorname{Res}_H^GV\otimes W).
\tag{2.5}
$$

An explicit isomorphism is

$$
v\otimes(g\otimes w)\longmapsto
g\otimes(g^{-1}v\otimes w).
\tag{2.6}
$$

For $h\in H$, the two representatives $gh\otimes w$ and $g\otimes hw$ have images

$$
gh\otimes(h^{-1}g^{-1}v\otimes w)
=g\otimes(g^{-1}v\otimes hw),
$$

so the map is well defined. It is visibly $G$-equivariant and has inverse
$g\otimes(v\otimes w)\mapsto gv\otimes(g\otimes w)$. Thus (2.5) holds for actual modules and,
by additivity, in $R_A(G)$.

Exactly the same proof works for an open subgroup $G_L\leq G_K$ of a profinite group because
the coset set is finite. In particular,

$$
V\otimes\operatorname{Ind}_{G_L}^{G_K}\theta
\simeq
\operatorname{Ind}_{G_L}^{G_K}(V|_{G_L}\otimes\theta).
\tag{2.7}
$$

For a quadratic extension $L/K$, this can be seen in matrices. Choose
$s\in G_K\setminus G_L$. If $\theta$ is one dimensional, then on the two coset lines

$$
\operatorname{Ind}_{G_L}^{G_K}\theta(h)
=
\begin{pmatrix}
\theta(h)&0\\
0&\theta(shs^{-1})
\end{pmatrix}
\qquad(h\in G_L),
\tag{2.7a}
$$

while $s$ exchanges the lines, with the product around the two-cycle equal to $\theta(s^2)$.
Tensoring by $V$ replaces each scalar entry by its action on the corresponding conjugate of
$V|_{G_L}$. The map (2.6) is exactly the change of basis that identifies this block matrix with
induction of $V|_{G_L}\otimes\theta$.

This example also displays the permutation sign in the determinant. The coset swap contributes
$(-1)^{\dim V}$; it disappears for our rank-two packets but would matter for odd-dimensional
summands.

### 2.4 Ranks, determinant lines, and characteristic series

For an actual representation $V$, write $\det V=\bigwedge^{\dim V}V$. Determinants extend
multiplicatively to the Grothendieck group:

$$
\det([V]-[W])=\det(V)\otimes\det(W)^{-1}.
\tag{2.8}
$$

This is well defined because the determinant of a direct sum is the tensor product of the
determinants. It is a one-dimensional character even when the virtual object is not effective.

For $g\in G$, define the virtual characteristic series

$$
D_g([V]-[W];T)
=\frac{\det(1-gT\mid V)}{\det(1-gT\mid W)}\in A(T)^\times.
\tag{2.9}
$$

It is multiplicative under addition in $R_A(G)$. Its order at $T=0$ is zero and the difference
between numerator and denominator degrees is the virtual rank. The fact that (2.9) happens to
be a polynomial does not force $[V]-[W]$ to be effective: it tests one element at a time, while
effectivity is a simultaneous nonnegativity statement for all irreducible multiplicities.

### 2.5 Adjunction and transitivity

Two structural identities justify later changes of subgroup. First, for an $H$-module $W$ and
a $G$-module $V$, restriction and induction are adjoint:

$$
\operatorname{Hom}_G(\operatorname{Ind}_H^GW,V)
\simeq
\operatorname{Hom}_H(W,\operatorname{Res}_H^GV).
\tag{2.10}
$$

Given a $G$-map $\Phi$, send it to $w\mapsto\Phi(1\otimes w)$. Conversely, from an $H$-map
$f:W\to V$ define

$$
\Phi_f(g\otimes w)=g f(w).
\tag{2.11}
$$

The relation $gh\otimes w=g\otimes hw$ is respected because
$ghf(w)=gf(hw)$. These constructions are inverse. Taking traces of endomorphism projectors, or
simply decomposing into irreducibles in characteristic zero, gives the inner-product identity

$$
\langle\operatorname{Ind}_H^G\alpha,\beta\rangle_G
=
\langle\alpha,\operatorname{Res}_H^G\beta\rangle_H.
\tag{2.12}
$$

This is the adjunction expanded directly in the proof of Theorem 4.4. Its use there concerns
integral spanning, not positivity of the later arithmetic virtual character.

Second, if $J\leq H\leq G$, induction is transitive:

$$
\operatorname{Ind}_H^G\operatorname{Ind}_J^HW
\simeq
\operatorname{Ind}_J^GW.
\tag{2.13}
$$

In the tensor model the isomorphism is

$$
g\otimes(h\otimes w)\longmapsto gh\otimes w.
\tag{2.14}
$$

Both balancing relations are respected, and the inverse is obtained after choosing coset
representatives. Restriction is plainly transitive. For open subgroups of a profinite group,
the same proofs work in continuous induction because all coset sets are finite.

On fields, (2.13) says that inducing from $L$ to $K$ through an intermediate field gives the
same Galois representation as direct induction. It does not say that an automorphic induction
exists through either route. Conversely, transitivity of automorphic base change is restriction
of local parameters and belongs to Books 96--97. Keeping these two variances separate avoids
turning a Galois identity into an unproved automorphic transfer.

## 3. Conjugation and Mackey decomposition

One induced representation simultaneously remembers every embedding of its source field into a
Galois closure. Restricting it to another subgroup therefore cannot be described by one
intersection: different embeddings meet that subgroup differently. Mackey's formula organizes
these encounters by double cosets. In arithmetic, the same double cosets index primes, local
completions, and conjugate packets, so the finite-group formula is also the local-global
bookkeeping theorem for the construction.

### 3.1 Transport by conjugation

For $x\in G$ and an $H$-module $W$, let ${}^xW$ be the $xHx^{-1}$-module with

$$
(xhx^{-1})\cdot {}^xw={}^x(hw).
\tag{3.1}
$$

The map $g\otimes w\mapsto gx^{-1}\otimes{}^xw$ proves

$$
\operatorname{Ind}_{xHx^{-1}}^G({}^xW)
\simeq\operatorname{Ind}_H^GW.
\tag{3.2}
$$

Thus an induced term depends only on the conjugacy class of the pair $(H,W)$. This elementary
observation is the source of field-conjugation compatibility later.

### 3.2 The double-coset formula

Restriction of an induced representation is not usually induction from the intersection
$H\cap K$ alone. Every double coset contributes.

**Theorem 3.1 (Mackey formula).** For $H,K\leq G$ and an $H$-module $W$,

$$
\operatorname{Res}_K^G\operatorname{Ind}_H^GW
\simeq
\bigoplus_{x\in K\backslash G/H}
\operatorname{Ind}_{K\cap xHx^{-1}}^K
\operatorname{Res}_{K\cap xHx^{-1}}^{xHx^{-1}}({}^xW).
\tag{3.3}
$$

**Proof.** As a $(K,H)$-biset, $G$ is the disjoint union of its double cosets $KxH$.
Consequently

$$
A[G]\otimes_{A[H]}W
=\bigoplus_x A[KxH]\otimes_{A[H]}W.
$$

Fix $x$ and put $J=K\cap xHx^{-1}$. The map

$$
A[K]\otimes_{A[J]}{}^xW\longrightarrow
A[KxH]\otimes_{A[H]}W,
\qquad k\otimes{}^xw\longmapsto kx\otimes w
$$

is well defined: if $j=xhx^{-1}\in J$, then $kjx\otimes w=kx h\otimes w=kx\otimes hw$.
It is $K$-equivariant and surjective. Both sides have dimension
$[K:J]\dim W$, since the left $K$-orbits in $KxH/H$ are indexed by $K/J$; hence it is an
isomorphism. Summing over double cosets proves (3.3). $\square$

**Theorem 3.2 (profinite Mackey formula).** Formula (3.3) remains valid when $G$ is profinite,
$H$ and $K$ are open subgroups, and $W$ is any finite-dimensional continuous
representation of $H$. No finite-image hypothesis on $W$ is required.

**Proof.** Use the continuous induction model

$$
\operatorname{Ind}_H^GW
=
\{f:G\to W:\ f(gh)=h^{-1}f(g),\ f\text{ continuous}\},
\tag{3.3a}
$$

with the left action $(g_0f)(x)=f(g_0^{-1}x)$. Because $H$ is open, $G/H$ is finite and a
function is determined by finitely many values. On each open coset its values are obtained from
one value by the continuous $H$-action, so it is continuous; no quotient through which $W$
factors is involved.

The finite double-coset space $K\backslash G/H$ decomposes the induction space into the
$K$-stable subspaces of functions supported on $KxH$. Put $J_x=K\cap xHx^{-1}$. Evaluation
on representatives of the right-coset space $K/J_x$ identifies the $x$-supported subspace with

$$
\operatorname{Ind}_{J_x}^K
\operatorname{Res}_{J_x}^{xHx^{-1}}({}^xW).
\tag{3.3b}
$$

Explicitly, send an $x$-supported function $f$ to $F(k)=f(kx)$. If
$j=xhx^{-1}\in J_x$, then

$$
F(kj)=f(kjx)=f(kxh)=h^{-1}f(kx)=j^{-1}\cdot F(k),
\tag{3.3c}
$$

where the last action is on ${}^xW$. Thus $F$ is in the right-covariant model of the
induction in (3.3b). Conversely, set $f(kxh)=h^{-1}F(k)$. Equation (3.3c) proves this is
independent of the presentation of an element of $KxH$. These maps are inverse and
$K$-equivariant. All sums are finite, and the maps are continuous because they are assembled
from the continuous action on finitely many copies of $W$. Summing (3.3b) proves the result.
$\square$

### 3.3 Normal subgroups and restriction to the top field

If $N\triangleleft G$ and $N\leq H$, then $N\backslash G/H=G/H$ and
$N\cap xHx^{-1}=N$. Formula (3.3) becomes

$$
\operatorname{Res}_N^G\operatorname{Ind}_H^GW
\simeq\bigoplus_{x\in G/H}\operatorname{Res}_N^{xHx^{-1}}{}^xW.
\tag{3.4}
$$

On Galois groups, take $G=G_{\mathbf Q}$, $H=G_{F_H}$, and $N=G_M$. These are open subgroups
in precisely the places needed by Theorem 3.2, and $N$ is normal in $G$. The packet
representation on $W$ can have infinite image; this causes no problem. Restricting an induced
term from $F_H$ to $M$ therefore produces the direct sum of all conjugates indexed by embeddings
of $F_H$ into $M$.

This is why compatible conjugate packets are necessary. Without them, restriction of the
Brauer expression to the top field would be a list of unrelated summands rather than a coherent
orbit.

### 3.4 The fixed-field translation

Let $M/K$ be finite Galois with group $G$, and let $F_H=M^H$. The quotient

$$
G_{F_H}/G_M\simeq H
\tag{3.5}
$$

turns a character $\theta$ of $H$ into a finite-image Galois character
$\widetilde\theta$ of $G_{F_H}$. If $x\in G$, then $xF_H=F_{xHx^{-1}}$, and conjugation sends
$\widetilde\theta$ to the avatar of ${}^x\theta$.

For a place $v$ of $K$, the double cosets

$$
D_v\backslash G/H
\tag{3.6}
$$

index places $w$ of $F_H$ above $v$, where $D_v$ is a decomposition group of a chosen place of
$M$ above $v$. The local version of Mackey gives

$$
\left.
\operatorname{Ind}_{G_{F_H}}^{G_K}W
\right|_{G_{K_v}}
\simeq
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{(F_H)_w}}^{G_{K_v}}W|_{G_{(F_H)_w}}.
\tag{3.7}
$$

The proof is (3.3) applied to decomposition groups, followed by the identification (3.6).
Formula (3.7) will control both local types and residue-degree Euler factors.

### 3.5 Two concrete Mackey calculations

The smallest nontrivial examples show why the intersection and the sum over double cosets are
both indispensable. Take $G=S_3$, $H=C_3=A_3$, and $K=C_2=\langle(12)\rangle$. Since
$G=KH$, there is one double coset and $K\cap H=1$. For a nontrivial character $\omega$ of
$C_3$, Mackey gives

$$
\operatorname{Res}_{C_2}^{S_3}
\operatorname{Ind}_{C_3}^{S_3}\omega
\simeq\operatorname{Ind}_{1}^{C_2}1.
\tag{3.8}
$$

The left side is the two-dimensional irreducible representation restricted to a transposition;
the right side is $1\oplus\operatorname{sgn}$. Its trace is therefore $0$ at the
transposition, exactly as the induced-character formula predicts.

Now take $H=K=C_2$. There are two double cosets: the identity coset has intersection $C_2$,
while a double coset represented by a $3$-cycle has trivial intersection. Thus

$$
\operatorname{Res}_{C_2}^{S_3}
\operatorname{Ind}_{C_2}^{S_3}1
\simeq
1\oplus\operatorname{Ind}_{1}^{C_2}1
\simeq 1^{\oplus2}\oplus\operatorname{sgn}.
\tag{3.9}
$$

The dimensions are $3=1+2$, and the trace at the nontrivial element is $1=1+0$. Replacing the
double-coset sum by one intersection would miss an entire regular summand.

The arithmetic version is identical. If a rational decomposition group plays the role of
$K$, the two double cosets in (3.9) are two primes of the fixed field above the rational prime.
The corresponding local induced representation is the direct sum of the two local
contributions. Mackey theory is therefore not decorative group theory: it is the mechanism
that counts primes and attaches the correct completion to each one.

### 3.6 Worked decomposition groups and completed fixed fields

The completion formula (6.1b) is worth seeing before it is used in the controlled family.
First let $\Gamma=V_4=\{1,a,b,c\}$ and suppose a place of the ground field has decomposition
group $D=\langle a\rangle$. Take $H=\langle a\rangle$. Since the group is abelian,

$$
D\backslash\Gamma/H=\{H,bH\}.
\tag{3.10}
$$

There are two primes of $F_H$ above the ground-field place. For both representatives, the
intersection $D\cap H$ is $D$, so each completed fixed field is
$M_{\widetilde v}^{D}$, the ground local field. In splitting language, the degree-two field
$F_H$ is split at this place.

Now take $H=\langle b\rangle$. There is one double coset because $DH=\Gamma$, and
$D\cap H=1$. Thus $F_H$ has one prime above the ground place and

$$
(F_H)_w\simeq M_{\widetilde v}.
\tag{3.11}
$$

The same global degree two is now locally inert. The difference between (3.10) and (3.11) is
not visible from the orders of $D$ and $H$ separately; their intersection and double-coset
position matter.

A nonabelian example gives a mixed factorization. Let $\Gamma=S_3$ and
$H=\langle(12)\rangle$, so $F_H$ is a non-Galois cubic field. If
$D=\langle(12)\rangle=H$, then

$$
D\backslash S_3/H
=\{H,\ H(123)H\}.
\tag{3.12}
$$

For the first representative the intersection is $D$, giving a completion of degree one. For
the second it is trivial, giving a completion of degree two inside the local quadratic top.
Thus the factorization pattern is $(1,2)$, exactly the pattern of a transposition acting on
three letters.

If instead $D=C_3=A_3$, then $DH=S_3$, there is one double coset, and $D\cap H=1$. The cubic
field has one prime of local degree three. If $D=1$, there are three double cosets and the
prime splits completely. We have recovered all three unramified splitting types of a cubic
field from the same formula:

$$
1^3,\qquad 1\cdot2,\qquad 3.
\tag{3.13}
$$

On representations, these cases become respectively three degree-one Frobenius blocks, one
degree-one plus one degree-two block, and one degree-three block. Chapter 8 will write their
characteristic polynomials explicitly.

### 3.7 Two fixed fields and their composita

Mackey also describes what happens when an induced base-field term is restricted not all the
way to $M$, but to another fixed field. Let $H,J\leq\Gamma$. Apply profinite Mackey with
$G=G_{\mathbf Q}$, $K=G_{F_J}$, and $H$ replaced by $G_{F_H}$. The double cosets are
$J\backslash\Gamma/H$, and the intersection subgroup attached to $\gamma$ fixes the compositum

$$
M^{J\cap\gamma H\gamma^{-1}}
=F_J\,\gamma(F_H).
\tag{3.14}
$$

Hence

$$
\begin{aligned}
\operatorname{Res}_{G_{F_J}}^{G_{\mathbf Q}}
\operatorname{Ind}_{G_{F_H}}^{G_{\mathbf Q}}W
\simeq
\bigoplus_{\gamma\in J\backslash\Gamma/H}
\operatorname{Ind}_{G_{F_J\gamma(F_H)}}^{G_{F_J}}
\left({}^\gamma W|_{G_{F_J\gamma(F_H)}}\right).
\end{aligned}
\tag{3.15}
$$

The field identity follows from Galois correspondence: the compositum of fixed fields is fixed
by the intersection. Formula (3.15) records multiplicities correctly even when two composita
are abstractly isomorphic; distinct double cosets represent distinct embeddings into $M$.

Suppose $H$ and $J$ are elementary. Their intersection is elementary, but
$J\cap\gamma H\gamma^{-1}$ need not be normal in $J$. Consequently
$F_J\gamma(F_H)/F_J$ need not be Galois, and Books 96--97 do not automatically provide base
change along it. Galois restriction and induction in (3.15) remain valid. This is another place
where one must not upgrade a Galois Mackey formula to an automorphic transfer theorem.

There is nevertheless a packet-level Galois identification on every term of this Mackey sum.
Put

$$
D_\gamma=J\cap\gamma H\gamma^{-1},
\qquad
L_\gamma=M^{D_\gamma}=F_J\gamma(F_H).
\tag{3.15a}
$$

Section 6.4 will prove, for every coefficient embedding $\tau$,

$$
\left(r_{\pi_J,\tau}|_{G_{L_\gamma}}\right)^{\mathrm{ss}}
\simeq r_{\pi_{D_\gamma},\tau}
\simeq
\left({}^{\gamma}r_{\pi_H,\tau}|_{G_{L_\gamma}}\right)^{\mathrm{ss}}.
\tag{3.15b}
$$

Consequently, for $W=r_{\pi_H,\tau}\otimes\theta_{H,\tau}$, formula (3.15) has the
Mackey-ready form

$$
\begin{aligned}
&\left(\operatorname{Res}_{G_{F_J}}^{G_{\mathbf Q}}
\operatorname{Ind}_{G_{F_H}}^{G_{\mathbf Q}}
(r_{\pi_H,\tau}\otimes\theta_{H,\tau})\right)^{\mathrm{ss}}\\
&\qquad\simeq
\bigoplus_{\gamma\in J\backslash\Gamma/H}
\operatorname{Ind}_{G_{L_\gamma}}^{G_{F_J}}
\left(r_{\pi_{D_\gamma},\tau}\otimes
({}^{\gamma}\theta_H|_{D_\gamma})_\tau\right).
\end{aligned}
\tag{3.15c}
$$

Distinct double cosets remain distinct summands in (3.15c), even when their fields or packet
representations happen to be isomorphic. Formula (3.15b) is proved from common Frobenius
polynomials and not from automorphic base change along the generally non-Galois extension
$L_\gamma/F_J$.

At the top field $J=1$, every intersection is trivial and (3.15) becomes the direct sum of
conjugates in (3.4). At the ground field $J=\Gamma$, there is one double coset and (3.15) is
the original induction. Between these extremes the formula measures exactly how much of the
finite quotient action survives after restriction.

For local decomposition groups, replace $J$ by $D_v$. Then (3.15) becomes (3.7), and the
composita become completions. Thus global fixed-field intersections, local prime decomposition,
and restriction of induced Galois representations are three forms of the same double-coset
identity.

## 4. Elementary subgroups and Brauer relations

The full Galois group is not solvable, while solvable descent reaches fixed fields of solvable
subgroups. Brauer's theorem makes this mismatch manageable by proving that elementary
subgroups—not arbitrary solvable subgroups—integrally generate the character lattice under
induction from linear characters. The word integrally matters: rational coefficients would
produce fractional powers of Euler factors, not a virtual representation. The proof below
therefore tracks localization at every prime before using self-duality to recover an integral
relation.

### 4.1 The correct elementary groups

For a prime $p$, a finite group $E$ is **$p$-elementary** if

$$
E=C\times P,
\tag{4.1}
$$

where $C$ is cyclic of order prime to $p$ and $P$ is a $p$-group. A group is **elementary** if
it is $p$-elementary for some $p$. Elementary groups are solvable, but not every solvable group
is elementary. For example, $S_3$ is solvable but is neither a direct product of its cyclic
$3$-part with a $2$-group nor of its cyclic $2$-part with a $3$-group.

The direct product condition is essential. A semidirect product $C\rtimes P$ is not generally
$p$-elementary, because the Fourier projectors on $C$ need to commute with the $p$-part in the
local induction argument.

### 4.2 The local induction lemma

The safest proof does not pretend that linear characters of a nonabelian $p$-group separate
its elements. They do not. Instead, a permutation character isolates all $p$-elements at once,
and a restriction criterion converts that sectionwise statement into an integral theorem.

For example, $D_8$ has four linear characters, all trivial on its commutator
$\langle r^2\rangle$. They cannot distinguish $1$ from $r^2$. Its remaining irreducible
character has degree two and takes values $2,-2,0$ on the relevant classes. Any proof that
uses only Fourier inversion on the linear characters of the $2$-group has therefore already
lost information. Lemma 4.1 uses permutation characters of all stabilizer intersections
instead; Lemma 4.3 later handles the nonlinear irreducible by monomial induction.

Write $\mathbf Z_{(p)}$ for the localization of $\mathbf Z$ at $(p)$. If $A$ is a finite group
and $P$ is a Sylow $p$-subgroup, put

$$
u_P=\operatorname{Ind}_P^A1.
\tag{4.2}
$$

This is the permutation character of $A/P$.

**Lemma 4.1 (the $p$-element projector).** There is a polynomial
$Q_{A,p}(X)\in\mathbf Z_{(p)}[X]$ with zero constant term such that

$$
Q_{A,p}(u_P)(a)=
\begin{cases}
1,&a\text{ has }p\text{-power order},\\
0,&\text{otherwise}.
\end{cases}
\tag{4.3}
$$

Moreover $Q_{A,p}(u_P)$ is a $\mathbf Z_{(p)}$-linear combination of permutation characters
$\operatorname{Ind}_Q^A1$ with $Q$ a $p$-subgroup.

**Proof.** An element $a$ fixes a coset $xP$ precisely when $x^{-1}ax\in P$. Hence
$u_P(a)=0$ if $a$ is not a $p$-element. If $a$ is a $p$-element, the cyclic $p$-group
$\langle a\rangle$ acts on $A/P$, whose cardinality is prime to $p$. Every nontrivial orbit has
cardinality divisible by $p$, so

$$
u_P(a)=|(A/P)^{\langle a\rangle}|
\equiv[A:P]\not\equiv0\pmod p.
\tag{4.4}
$$

Let $b_1,\ldots,b_s$ be the distinct nonzero values taken by $u_P$ on $p$-elements and define

$$
Q_{A,p}(X)=1-\prod_{j=1}^s\left(1-\frac{X}{b_j}\right).
\tag{4.5}
$$

Every $b_j$ is a unit of $\mathbf Z_{(p)}$, so the polynomial has coefficients there. It is
zero at $0$ and one at each $b_j$, proving (4.3).

It remains to interpret its powers. The product of permutation characters is the character of
the Cartesian product of the corresponding sets. Thus $u_P^m$ is the permutation character of
$(A/P)^m$. The stabilizer of a point is an intersection of conjugates of $P$, hence a
$p$-subgroup. Decomposing the finite $A$-set into orbits writes every positive power of $u_P$
as a sum of $\operatorname{Ind}_Q^A1$. Since (4.5) has no constant term, the final assertion
follows. $\square$

For $g\in G$, write $g=g_{p'}g_p=g_pg_{p'}$, with the indicated prime-to-$p$ and $p$-power
orders. The conjugacy class of $g_{p'}$ is its $p$-section. The preceding lemma applied in
$A=C_G(g_{p'})$ gives an exact indicator of the $p$-elements that may multiply $g_{p'}$.

**Lemma 4.2 (Brauer's restriction criterion).** Let $\varphi$ be a rational linear combination
of irreducible characters of $G$. Then $\varphi$ is a generalized character of $G$ if and only
if $\operatorname{Res}_E^G\varphi$ is a generalized character for every elementary subgroup
$E\leq G$.

**Proof.** The forward implication is restriction. For the converse, write

$$
\varphi=\sum_{\chi\in\operatorname{Irr}(G)}a_\chi\chi,
\qquad a_\chi\in\mathbf Q.
\tag{4.6}
$$

It suffices to show $a_\chi\in\mathbf Z_{(p)}$ for every prime $p$, because
$\bigcap_p\mathbf Z_{(p)}=\mathbf Z$.

Fix $p$ and partition the inner product
$a_\chi=\langle\varphi,\chi\rangle_G$ into $p$-sections. Choose a representative $s$ of
prime-to-$p$ order and put $A=C_G(s)$. Only elements $su$ with $u$ a $p$-element of $A$ occur
in this section. More precisely, the contribution is

$$
\frac1{|A|}
\sum_{\substack{u\in A\\u\text{ a }p\text{-element}}}
\varphi(su)\chi((su)^{-1}).
\tag{4.6a}
$$

Indeed, the conjugates of $s$ are indexed by $G/A$, and after choosing the prime-to-$p$ part
there is one commuting $p$-part $u$. Multiplication by $|G/A|$ and division by $|G|$ in the
global inner product gives (4.6a). Lemma 4.1 replaces the indicator of those $u$ by a
$\mathbf Z_{(p)}$-linear combination of $\operatorname{Ind}_Q^A1$, with $Q\leq A$ a
$p$-group.

For each such $Q$, the subgroup $\langle s\rangle\times Q$ is elementary: $s$ centralizes
$A$, the two factors have coprime orders, and their intersection is trivial. Fourier inversion
on the cyclic group $\langle s\rangle$ expresses evaluation at $s$ as

$$
\delta_s(t)=\frac1{|\langle s\rangle|}
\sum_{\alpha\in\widehat{\langle s\rangle}}\alpha(ts^{-1}).
\tag{4.7}
$$

The denominator is prime to $p$. Substituting (4.3) and (4.7) into the section sum and using
the induced-character formula (2.4) rewrites the contribution of the section as a
linear combination, with coefficients in localized cyclotomic integers, of inner products

$$
\left\langle
\operatorname{Res}_{\langle s\rangle\times Q}^G\varphi,\,
\operatorname{Res}_{\langle s\rangle\times Q}^G\chi
\otimes\alpha
\right\rangle_{\langle s\rangle\times Q}.
\tag{4.8}
$$

Here is the substitution in more detail. Lemma 4.1 provides coefficients
$c_Q\in\mathbf Z_{(p)}$ such that the $p$-element indicator on $A$ is

$$
\mathbf 1_{A,p}
=\sum_Qc_Q\operatorname{Ind}_Q^A1.
\tag{4.7a}
$$

Insert (4.7a) in (4.6a) and expand an induced character:

$$
\operatorname{Ind}_Q^A1(u)
=\frac1{|Q|}
\#\{x\in A:x^{-1}ux\in Q\}.
\tag{4.7b}
$$

Interchange the sums over $u$ and $x$. Replacing $u$ by $xqx^{-1}$ leaves $s$ fixed because
$x\in A=C_G(s)$. The contribution becomes a sum over $q\in Q$ of values at $sq$, repeated with
the exact coset multiplicity in (4.7b). More precisely, the factor $|A|^{-1}$ in (4.6a)
cancels the sum over $x\in A$, and the $Q$-term is

$$
\frac{c_Q}{|Q|}\sum_{q\in Q}
\varphi(sq)\chi((sq)^{-1}).
\tag{4.7c}
$$

Now insert the Fourier identity (4.7) on $C=\langle s\rangle$. Since $C$ centralizes $Q$, the
pairs $tq$ range over the direct product $C\times Q$. With the inner-product convention (4.9),
(4.7c) becomes exactly

$$
c_Q\sum_{\alpha\in\widehat C}\alpha(s)^{-1}
\left\langle
\operatorname{Res}_{C\times Q}^G\varphi,
\operatorname{Res}_{C\times Q}^G\chi\otimes\alpha^{-1}
\right\rangle_{C\times Q}.
\tag{4.7d}
$$

Replacing $\alpha$ by $\alpha^{-1}$ gives the equivalent convention used in (4.8). This proves
(4.8) without assuming that a linear character of $Q$ separates its elements.

Here a harmless conjugate of $\alpha$ may occur, depending on the chosen inner-product
convention. Both restrictions in (4.8) are generalized characters by hypothesis and by
restriction of $\chi$, so their inner product is an integer. Notice the important denominator
point: although $|Q|$ is a power of $p$, the factor $|Q|^{-1}$ in (4.7c) is not left as an
external coefficient. Together with the Fourier factor $|C|^{-1}$ it is exactly the normalized
factor $|C\times Q|^{-1}$ inside the integer inner product in (4.7d). The external coefficients
are only $c_Q\in\mathbf Z_{(p)}$ and roots of unity. Thus no division by a nonunit at a prime
above $p$ remains.

The section contribution can still contain roots of unity from Fourier inversion; it need not
itself be rational. Let $L$ be a cyclotomic field containing every character value and let
$\mathfrak p\mid p$. Formula (4.7d) proves that every section contribution lies in the
localized ring of integers $\mathcal O_{L,\mathfrak p}$. Hence their sum $a_\chi$ lies in
$\mathcal O_{L,\mathfrak p}$ for every $\mathfrak p\mid p$. But $a_\chi\in\mathbf Q$ by
(4.6). Therefore

$$
a_\chi\in
\mathbf Q\cap\bigcap_{\mathfrak p\mid p}\mathcal O_{L,\mathfrak p}
=\mathbf Z_{(p)}.
\tag{4.8a}
$$

For completeness, formula (4.8) is not an appeal to an unstated reciprocity theorem. Expanding
both sides from the definition

$$
\langle f,h\rangle_J=\frac1{|J|}\sum_{x\in J}f(x)h(x^{-1})
\tag{4.9}
$$

and using (2.4), every conjugate of $su$ appears exactly $|C_G(su)|$ times; these factors cancel
the class-size denominators in the original section sum. This is precisely the change of
variables behind induction--restriction adjunction. Hence the calculation is valid in the
localized cyclotomic integer ring $\mathcal O_{L,\mathfrak p}$ for every
$\mathfrak p\mid p$. Individual $p$-sections are asserted to be algebraic integral at all
primes above $p$, not rational. This means $\mathfrak p$-integral for every
$\mathfrak p\mid p$, not necessarily an algebraic integer at primes away from $p$, since the
$c_Q$ may have prime-to-$p$ denominators. Only after summing the sections and using the
rationality of $a_\chi$ do we intersect with $\mathbf Q$ in (4.8a) and obtain
$\mathbf Z_{(p)}$. This is the exact algebraic-integrality step; it proves integral character
coefficients but no positivity of any later Brauer multiplicity. The criterion follows.
$\square$

### 4.3 Integral Brauer induction

We now turn the restriction criterion into an induction theorem. The remaining ingredient is
that irreducible characters of elementary groups are monomial.

**Lemma 4.3 (monomiality for elementary groups).** If $E=C\times P$ is elementary, every
irreducible character of $E$ is induced from a linear character of a subgroup of $E$.

**Proof.** An irreducible character of $E$ is $\alpha\otimes\tau$, with $\alpha$ linear on
$C$ and $\tau$ irreducible on the $p$-group $P$. We prove by induction on $|P|$ that $\tau$ is
monomial.

First quotient by the kernel of $\tau$; pulling an inducing character back from the quotient
will recover the original character, so we may suppose $\tau$ faithful. Schur's lemma embeds
$Z(P)$ into the scalar roots of unity, so $Z(P)$ is cyclic. If $P$ is nonabelian, choose a
central subgroup of order $p$ in $P/Z(P)$ and let $A$ be its inverse image. Equivalently,
choose $xZ(P)$ of order $p$ in the center of $P/Z(P)$ and put
$A=\langle x,Z(P)\rangle$. Then $A$ is abelian, normal, and properly contains $Z(P)$.

Choose a linear constituent $\lambda$ of $\tau|_A$. Let $I$ be its
stabilizer. The $\lambda$-isotypic space is stable under $I$, and the translates of that space
by $P/I$ are the distinct isotypic spaces. Their direct sum is the representation space, so
the action map gives

$$
\tau\simeq\operatorname{Ind}_I^P\tau_0
\tag{4.10}
$$

for an irreducible $\tau_0$ of $I$. This statement follows directly by choosing one isotypic
space: matrices outside $I$ permute the spaces transitively, while matrices in $I$ act on the
chosen one.

The inertia group cannot equal $P$. If it did, $\lambda$ would be invariant and every element
of $A$ would act as the scalar $\lambda(a)$. Then every commutator $[g,a]$, with $g\in P$ and
$a\in A$, would act trivially. Faithfulness would force $[P,A]=1$, so $A\subseteq Z(P)$,
contrary to its construction. Hence $I<P$. Induction on $|I|$ writes
$\tau_0=\operatorname{Ind}_D^I\mu$ with $\mu$ linear; transitivity of induction gives
$\tau=\operatorname{Ind}_D^P\mu$. If $P$ was abelian from the start, $\tau$ itself was linear.
This completes the induction.

Finally, if $\tau=\operatorname{Ind}_D^P\mu$, then

$$
\alpha\otimes\tau
=\operatorname{Ind}_{C\times D}^{C\times P}(\alpha\otimes\mu).
\tag{4.11}
$$

The inducing character is linear. $\square$

Every subgroup of an elementary group is elementary. Indeed, if $D\leq C\times P$, taking
the prime-to-$p$ and $p$-parts of each element shows
$D=(D\cap C)\times(D\cap P)$, with $D\cap C$ cyclic.

**Theorem 4.4 (Brauer induction for the trivial character).** For every finite group $G$ there
are elementary subgroups $H_i$, linear characters $\theta_i$, and integers $n_i$ satisfying

$$
1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i.
\tag{4.12}
$$

**Proof.** Let $R(G)$ be the integral character lattice, with irreducible characters as an
orthonormal basis for (4.9). Let $X\subseteq R(G)$ be the subgroup generated by
$\operatorname{Ind}_E^G\theta$ for elementary $E$ and linear $\theta$. Define the dual lattice

$$
X^\vee=\{\varphi\in R(G)\otimes\mathbf Q:
\langle\varphi,x\rangle_G\in\mathbf Z\text{ for every }x\in X\}.
\tag{4.13}
$$

Take $\varphi\in X^\vee$. For an elementary $E$ and an irreducible character $\xi$ of $E$,
Lemma 4.3 writes $\xi=\operatorname{Ind}_D^E\theta$ for a linear character of a subgroup
$D\leq E$. The subgroup $D$ is elementary, and expanding (2.4) in the inner product gives
induction--restriction adjunction:

$$
\langle\operatorname{Res}_E^G\varphi,\xi\rangle_E
=\langle\operatorname{Res}_D^G\varphi,\theta\rangle_D
=\langle\varphi,\operatorname{Ind}_D^G\theta\rangle_G
\in\mathbf Z.
\tag{4.14}
$$

Thus $\operatorname{Res}_E^G\varphi$ has integral inner product with every irreducible
character of $E$, so it is a generalized character. Lemma 4.2 now implies
$\varphi\in R(G)$. We have proved $X^\vee=R(G)$.

The lattice $R(G)$ is self-dual because its irreducible basis is orthonormal. If $X$ were a
proper sublattice of $R(G)$ of finite index, its dual would strictly contain $R(G)$; if it had
smaller rank, its dual inside $R(G)\otimes\mathbf Q$ would not be a lattice at all. Both
possibilities contradict $X^\vee=R(G)$. Hence $X=R(G)$, and in particular $1_G\in X$, which is
(4.12). $\square$

Tensoring (4.12) with any $G$-module $V$ and using (2.5) yields the form used in arithmetic:

$$
[V]=\sum_i n_i
\left[\operatorname{Ind}_{H_i}^G
(V|_{H_i}\otimes\theta_i)\right].
\tag{4.15}
$$

We only need the theorem for $1_G$: tensoring by $V$ produces (4.15) for every $V$ without any
extra induction theorem for arbitrary characters.

### 4.4 Examples and nonexamples

If $G$ itself is elementary, the one-term datum $H_1=G$, $\theta_1=1$, $n_1=1$ is valid.
Brauer induction is then tautological; its arithmetic content comes only when the full Galois
group is not elementary.

For $G=S_3$, let $C_2$ be generated by a transposition and let $C_3=A_3$. Choose a nontrivial
character $\omega:C_3\to\mu_3$. On the conjugacy classes represented by
$1,(12),(123)$, respectively,

$$
\operatorname{Ind}_{C_2}^{S_3}1=(3,1,0),
\qquad
\operatorname{Ind}_{C_3}^{S_3}\omega=(2,0,-1).
\tag{4.16}
$$

The second value $-1$ is $\omega((123))+\omega((132))$. Hence the genuine elementary Brauer
relation is

$$
1_{S_3}
=\operatorname{Ind}_{C_2}^{S_3}1
-\operatorname{Ind}_{C_3}^{S_3}\omega.
\tag{4.17}
$$

At the identity this reads $1=3-2$; at a transposition it reads $1=1-0$; and at a $3$-cycle it
reads $1=0-(-1)$. This small example already contains every feature used later: two different
fixed fields, a finite-order twist, and a negative coefficient.

Negative coefficients cannot generally be avoided. If every $n_i$ were nonnegative, evaluating
(4.12) at the identity would give

$$
1=\sum_i n_i[G:H_i].
$$

Every nonzero term would then have $H_i=G$. For a non-elementary $G$ this is impossible. Thus
the signed nature of the later family is structural, not an artifact of a poor decomposition.

### 4.5 A dihedral family of Brauer relations

The $S_3$ calculation is the first member of a uniform family. Let $p$ be an odd prime and

$$
G=D_{2p}=\langle r,s:r^p=s^2=1,\ srs=r^{-1}\rangle.
\tag{4.18}
$$

The group is solvable but not elementary: its order-$p$ subgroup and order-$2$ subgroup form a
nontrivial semidirect product. Let $\zeta$ be a primitive $p$th root of unity. For
$1\le j\le(p-1)/2$, define $\theta_j(\,r\,)=\zeta^j$. The two characters
$\theta_j$ and $\theta_{p-j}$ are conjugate under $s$, so their inductions are isomorphic.

We claim

$$
1_G
=\operatorname{Ind}_{\langle s\rangle}^{G}1
-\sum_{j=1}^{(p-1)/2}
\operatorname{Ind}_{\langle r\rangle}^{G}\theta_j.
\tag{4.19}
$$

There are three kinds of elements to check. At the identity, the right side has value

$$
p-\frac{p-1}{2}\cdot2=1.
\tag{4.20}
$$

At a reflection, $\operatorname{Ind}_{\langle s\rangle}^{G}1$ has value one: exactly one coset
is fixed. Every term induced from $\langle r\rangle$ has value zero, because a reflection is
not conjugate into that subgroup. At a nontrivial rotation $r^k$, the first term is zero and

$$
\sum_{j=1}^{(p-1)/2}
\chi_{\operatorname{Ind}_{\langle r\rangle}^{G}\theta_j}(r^k)
=
\sum_{j=1}^{(p-1)/2}(\zeta^{jk}+\zeta^{-jk})
=\sum_{j=1}^{p-1}\zeta^{jk}=-1.
\tag{4.21}
$$

The minus sign in (4.19) therefore gives value one. This proves the relation on every
conjugacy class.

Tensoring (4.19) with a rank-two representation $V$ gives one positive term of dimension
$2p$ and $(p-1)/2$ negative terms of dimension four. Their signed dimension is

$$
2p-\frac{p-1}{2}\cdot4=2.
\tag{4.22}
$$

Arithmetic translation produces one packet over the degree-$p$ fixed field of a reflection and
twisted packets over the quadratic fixed field of $\langle r\rangle$. The relation shows
concretely why a large positive induction and many negative quadratic inductions may encode a
rank-two object. It also shows why adjoining all character values to the coefficient field is
unavoidable: the twists use $\mathbf Q(\zeta_p)$ even when the final trivial character is
rational.

## 5. Refining a Brauer datum for arithmetic use

A bare character identity has forgotten the data arithmetic needs: a field containing character
values, embeddings into coefficient completions, reciprocity avatars, determinant signs, and
the distinction between field and coefficient conjugation. This chapter restores that data to
each term of one Brauer relation. The relation is not canonical, but every chosen relation can
be made into a finite, internally compatible ledger.

### 5.1 Coefficient fields and one-dimensional avatars

Fix a Brauer datum

$$
\mathfrak B=\{(H_i,\theta_i,n_i)\}_{i=1}^t
\tag{5.1}
$$

for $\Gamma$. Every value of $\theta_i$ is a root of unity of order dividing $|\Gamma|$.
Choose a number field $K$ containing these roots of unity, the Hecke fields of all $\pi_{H_i}$,
their finite local-type values, and their central-character values. There are only finitely many
objects, so one finite extension suffices.

For every $i,j$ and $x\in\Gamma$, also adjoin the Hecke fields, central characters, and finite
local-type values of

$$
\pi_{H_i\cap xH_jx^{-1}}.
$$

Only finitely many elementary subgroups occur, and an intersection of elementary subgroups is
elementary, so this remains one finite enlargement. It is this enlarged field that is used in
the overlap comparison of Section 6.4. If two Brauer data are compared, take the same
enlargement for the union of their terms and intersections.

For the complete export in Theorem 11.1, we make the harmless once-for-all enlargement that
contains the same data for every elementary subgroup of the finite group $\Gamma$. A
relation-specific calculation needs only the smaller finite list above, but the larger choice
lets the overlap clause be stated without changing coefficient fields when the Brauer datum is
changed.

At the distinguished prime, first place all Book-186 packet coefficient fields in the chosen
algebraic closure of $\mathbf Q_\ell$ using their selected embeddings, and form their compositum
there. We may and do replace that compositum by its Galois closure over $\mathbf Q$ inside the
same algebraic closure, and fix the resulting embedding
$\tau_0:K\hookrightarrow\overline{\mathbf Q}_\ell$. Thus the equalities with $\rho$ used below
hold in one common local overfield; $\tau_0$ is not chosen independently for the different
packets. This enlargement is harmless: Hecke polynomials and character values are merely viewed
in a larger field, while equality of representations can be checked after faithful scalar
extension. For each finite place $\lambda$ fix an embedding

$$
\iota_\lambda:K\hookrightarrow\overline{\mathbf Q}_{q_\lambda},
\tag{5.1a}
$$

where $q_\lambda$ is the residue characteristic. These choices are part of the coefficient
ledger. Without them, the expression $r_{\pi_H,\lambda}$ is ambiguous: an abstract Hecke field
can have several completions over the same rational prime.

Inflation through $G_{F_i}\twoheadrightarrow H_i$ gives a finite-order Galois character
$\widetilde\theta_i$. Global reciprocity gives the matching finite-order Hecke character
$\psi_i$ of $F_i$. The convention from Book 95 ensures that for every finite place $\lambda$ of
$K$, the $\lambda$-adic avatar $\psi_{i,\lambda}$ equals $\widetilde\theta_i$ after the chosen
embedding. It has a canonical stable lattice because all its values are roots of unity and
hence units.

The phrase “canonical stable lattice” here is rank-one and should not be overread. It means the
free line generated by one basis vector on which the character acts through units. The
rank-two packet lattice can be unique only up to homothety under residual irreducibility, and a
virtual difference of induced lattices has no canonical underlying module.

### 5.2 Conjugate data

For $\gamma\in\Gamma$, put

$$
H_i^\gamma=\gamma H_i\gamma^{-1},
\qquad
\theta_i^\gamma(\gamma h\gamma^{-1})=\theta_i(h).
\tag{5.2}
$$

Then $F_{H_i^\gamma}=\gamma F_{H_i}$, and Book 186 supplies

$$
{}^\gamma\pi_{H_i}\simeq\pi_{H_i^\gamma}.
\tag{5.3}
$$

The Hecke character attached to $\theta_i^\gamma$ is ${}^\gamma\psi_i$. Equations (3.2) and
(5.3) show that replacing a term of $\mathfrak B$ by its conjugate changes neither its induced
Galois class nor its local Euler contribution after transporting places.

A coefficient embedding $\sigma:K\hookrightarrow\mathbf C$ sends $\theta_i$ to
$\theta_i^\sigma$ and $\pi_{H_i}$ to $\pi_{H_i}^\sigma$. Applying $\sigma$ to (4.12) gives another
valid Brauer relation because $1_\Gamma$ is rational valued. Field conjugation and coefficient
conjugation are different operations; the former moves fixed fields, while the latter changes
eigenvalues.

They nevertheless commute. If $\gamma\in\Gamma$ and $\sigma\in\operatorname{Gal}(K/\mathbf Q)$,
then

$$
{}^\gamma(\pi_H^\sigma)\simeq({}^\gamma\pi_H)^\sigma,
\qquad
{}^\gamma(\theta^\sigma)=({}^\gamma\theta)^\sigma.
\tag{5.3a}
$$

Both identities follow by applying the two operations to local Hecke polynomials. The first
changes the place $w$ to $\gamma w$; the second applies $\sigma$ to its coefficients. Since
these actions address different entries of the record, their order is immaterial.

### 5.3 Determinants in a Brauer relation

We require one finite-group calculation. If $W$ has dimension $r$ and $H\leq G$, then

$$
\det\operatorname{Ind}_H^GW
=\operatorname{sgn}_{G/H}^{r}
\operatorname{Ver}_H^G(\det W).
\tag{5.4}
$$

Here $\operatorname{sgn}_{G/H}$ is the sign of the permutation action on $G/H$, and
$\operatorname{Ver}_H^G$ is multiplicative transfer in the following direction: it sends a
character $\varphi:H\to A^\times$ to a character of $G$. To evaluate it at $g$, decompose the
permutation of $G/H$ by $g$ into cycles. If a cycle has representative $tH$ and length $d$, its
factor is

$$
\varphi(t^{-1}g^dt),
\tag{5.4a}
$$

and $\operatorname{Ver}_H^G\varphi(g)$ is the product over the cycles. Changing $t$ conjugates
the element inside $H$, which does not change the one-dimensional character.

To prove (5.4), choose coset representatives compatible with these cycles. The matrix of $g$
is a block permutation matrix. Each cycle contributes its permutation sign to the $r$th power,
and the determinant of the product of the internal $H$-actions is (5.4a) applied to
$\det W$. Multiplying cycles proves the formula.

If $\chi:G\to A^\times$ is already a character, then

$$
\operatorname{Ver}_H^G(\chi|_H)(g)
=\prod_{\text{cycles}}\chi(t^{-1}g^dt)
=\prod_{\text{cycles}}\chi(g)^d
=\chi(g)^{[G:H]}.
\tag{5.4b}
$$

This is the restriction--transfer identity used below.

The same determinant formula holds for a profinite group $G$, an open subgroup $H$, and a
finite-dimensional continuous $H$-representation $W$. The proof uses the finitely many cosets
$G/H$, so its block matrices are identical to the finite-group matrices. For a continuous
character $\varphi:H\to A^\times$, define
$\operatorname{Ver}_H^G\varphi(g)$ by the finite cycle product (5.4a). Each factor depends
continuously on $g$ on a sufficiently small open neighborhood on which the coset permutation
is constant, so the transferred character is continuous. Thus

$$
\det\operatorname{Ind}_H^GW
=\operatorname{sgn}_{G/H}^{\dim W}
\operatorname{Ver}_H^G(\det W)
\tag{5.4c}
$$

as continuous characters of $G$. Likewise,
$\operatorname{Ver}_H^G(\chi|_H)=\chi^{[G:H]}$ for every continuous character $\chi$ of $G$.
This profinite form, with $G=G_{\mathbf Q}$ and $H=G_{F_i}$, is the formula actually used in
Section 7.3; the finite-group relation supplies only the quotient characters $\theta_i$.

Apply determinant to (4.12). Since the determinant of the one-dimensional trivial
representation is trivial,

$$
\prod_i
\left(\operatorname{sgn}_{G/H_i}\operatorname{Ver}_{H_i}^G\theta_i\right)^{n_i}=1.
\tag{5.5}
$$

Squaring removes every sign:

$$
\prod_i\left(\operatorname{Ver}_{H_i}^G\theta_i\right)^{2n_i}=1.
\tag{5.6}
$$

Also, evaluating (4.12) at the identity gives

$$
\sum_i n_i[G:H_i]=1.
\tag{5.7}
$$

If each two-dimensional $W_i$ has determinant $\chi|_H$, formulas (5.4)--(5.7) imply

$$
\det\left(\sum_i n_i
[\operatorname{Ind}_{H_i}^G(W_i\otimes\theta_i)]\right)=\chi.
\tag{5.8}
$$

Indeed, the cyclotomic contribution is $\chi^{\sum n_i[G:H_i]}=\chi$, the permutation signs
occur to the even power two, and the twist contribution is (5.6).

### 5.4 Changing the relation

Two Brauer data need not have the same subgroups, coefficient field, or number of terms. Their
difference is a relation

$$
0=\sum_j m_j\operatorname{Ind}_{J_j}^{\Gamma}\eta_j.
\tag{5.9}
$$

For a representation $V$ already defined on $G_{\mathbf Q}$, tensoring (5.9) with $V$ makes
the two resulting virtual expressions equal by (2.7). For a collection of independently
constructed compatible systems over the $F_J$, equality is not formal away from the
distinguished coefficient place. Section 11.3 will prove it by algebraic Frobenius comparison
and Lemma 6.1, rather than by pretending that all packet systems are restrictions of one
base-field representation.

### 5.5 Hecke fields, fields of definition, and centers

Several fields occur, and replacing all of them by the phrase “the coefficient field” obscures
real descent issues.

For a packet $\pi_H$, its **Hecke field** is generated by good Hecke eigenvalues and central
character values. It is a field of rationality for the unramified isomorphism class. A
**field of definition** is a number field over which chosen local type lines, pairings, and a
model of every Galois realization can be written. The field of definition may be larger:
individual Satake roots, finite-type characters, and intertwining operators need not lie in the
field generated by symmetric Hecke traces.

The Brauer character $\theta_i$ introduces a third field, the cyclotomic field generated by its
values. If $H_i=C\times P$, a linear character can be nontrivial on the abelianization of both
factors, so its values can have prime-power and prime-to-prime orders simultaneously. Since the
Brauer datum is finite, adjoining all these values and all packet fields still gives one number
field $K$. Taking a Galois closure ensures that every coefficient conjugate is again visible
inside the ledger.

For a finite place $\lambda$ of $K$, the embedding (5.1a) determines a completion
$K_\lambda$. A packet representation may initially be defined over a further finite extension
$C_\lambda/K_\lambda$. This does not damage compatibility. We form all induced terms after
embedding them into one finite extension $C_\lambda$; equality of characteristic polynomials
over $K$ can be checked there because

$$
K\hookrightarrow K_\lambda\hookrightarrow C_\lambda
\tag{5.10}
$$

is injective. If two finite extensions are needed for different summands, their compositum in
$\overline{\mathbf Q}_{q_\lambda}$ is again finite. There is no need to choose one infinite
coefficient field globally.

Centers and determinants must also be distinguished. For a $\mathrm{GL}_2$ packet,
twisting by $\psi_i\circ\det$ changes its central character by

$$
\omega_{\pi_{H_i}\otimes\psi_i}
=\omega_{\pi_{H_i}}\psi_i^2.
\tag{5.11}
$$

The attached two-dimensional Galois representation has the matching determinant
$\det r_{i,\lambda}\,\psi_{i,\lambda}^2$. This equality is local and global, and it is stable
under coefficient conjugation. But after induction to $\mathbf Q$, the determinant is not
obtained by merely norming (5.11); the permutation sign and transfer in (5.4c) intervene.
Rank two makes the sign disappear for each induced packet, while (5.6) cancels the transferred
squares only after all Brauer terms are multiplied.

A central-character identity is weaker than an isomorphism of packets. Cyclic descent fibers
can contain several twists whose centers differ by squares, and in a two-torsion fiber even the
center may fail to distinguish them. Book 186 selects a descent using the extending Galois
representation, not the center alone. Our conjugate packet notation retains that selection.

Finally, coefficient conjugation acts on all three levels:

$$
a_w\longmapsto\sigma(a_w),\qquad
\theta_i(h)\longmapsto\sigma(\theta_i(h)),\qquad
\omega_{\pi_H}\longmapsto\omega_{\pi_H}^{\sigma}.
\tag{5.12}
$$

It preserves the formal identities because they are polynomial identities over $K$. It need
not preserve a chosen $\lambda$-adic lattice: $\sigma$ may carry $\lambda$ to a different
place. The compatible object across coefficient places is therefore the algebraic Frobenius and
local-type record, not one literal module transported by every automorphism of $K$.

### 5.6 A worked determinant cancellation

Return to

$$
1_{S_3}
=\operatorname{Ind}_{C_2}^{S_3}1
-\operatorname{Ind}_{C_3}^{S_3}\omega.
\tag{5.13}
$$

The permutation representation on $S_3/C_2$ has determinant $\operatorname{sgn}$: it is the
usual permutation action on three letters. The two-dimensional induction from $C_3$ also has
determinant $\operatorname{sgn}$. Its coset permutation has that sign, while its transfer
character is trivial. For a rotation $r$ the transfer value is

$$
\omega(r)\omega(r^{-1})=1,
\tag{5.14}
$$

and for a reflection $s$ the single length-two coset cycle contributes $\omega(s^2)=1$.
Applying determinant to (5.13) therefore gives
$\operatorname{sgn}/\operatorname{sgn}=1$.

Now let $V$ be two dimensional with determinant $\chi$. The positive induced term
$\operatorname{Ind}_{C_2}^{S_3}(V|_{C_2})$ has determinant $\chi^3$: the permutation sign is
squared and disappears, while restriction--transfer gives the third power. The negative term
$\operatorname{Ind}_{C_3}^{S_3}(V|_{C_3}\otimes\omega)$ has determinant $\chi^2$: transfer of
$\omega^2$ is trivial and transfer of $\chi|_{C_3}$ gives $\chi^2$. Therefore

$$
\det\left(
[\operatorname{Ind}_{C_2}^{S_3}V|_{C_2}]
-
[\operatorname{Ind}_{C_3}^{S_3}(V|_{C_3}\otimes\omega)]
\right)
=\chi^3\chi^{-2}=\chi.
\tag{5.15}
$$

This calculation exposes why two separate sign statements occur in the general proof. The sign
in the one-dimensional Brauer relation is needed to prove the transfer-square identity (5.6).
The permutation sign in induction of a rank-two packet vanishes term by term. Confusing those
two facts can lose a quadratic character.

On the automorphic side, the positive packet center is transferred with exponent three and the
negative twisted packet center with exponent two. Formula (5.15) says only that their
determinant lines have the cyclotomic signed quotient. It does not produce a central character
of an actual base-field packet, because no such packet has yet been constructed.

### 5.7 Stabilizers of conjugate packet data

The conjugation orbit of a subgroup can be smaller than its index in $\Gamma$. Its stabilizer is
the normalizer

$$
N_\Gamma(H)=\{\gamma\in\Gamma:\gamma H\gamma^{-1}=H\}.
\tag{5.16}
$$

Elements of $N_\Gamma(H)$ act as automorphisms of $F_H$. Because the selected packet is
associated with $\rho|_{G_{F_H}}$ at $\lambda_0$, and $\rho$ is defined over $\mathbf Q$, its
conjugate by such an element has the same good polynomials. Strong multiplicity one and the
fixed central character give

$$
{}^\gamma\pi_H\simeq\pi_H
\qquad(\gamma\in N_\Gamma(H)).
\tag{5.17}
$$

This is invariance of an isomorphism class, not a chosen system of intertwining operators
satisfying a cocycle condition. No descent of $\pi_H$ to $F_H^{N_\Gamma(H)/H}$ is inferred.

The pair $(H,\theta)$ has the smaller stabilizer

$$
N_\Gamma(H,\theta)
=\{\gamma\in N_\Gamma(H):\theta^\gamma=\theta\}.
\tag{5.18}
$$

Conjugates outside this subgroup leave $\pi_H$ fixed up to transport but change the finite-order
twist. All pairs in the orbit nevertheless have isomorphic induction to $\Gamma$ by (3.2).
Thus a Brauer datum can be grouped by orbits of pairs, with the same integer coefficient on
each chosen occurrence, without losing field information.

Coefficient conjugation introduces a different stabilizer:

$$
\operatorname{Gal}(K/K_{\pi_H,\theta})
=\{\sigma:\pi_H^\sigma\simeq\pi_H,\ \theta^\sigma=\theta\}.
\tag{5.19}
$$

There is no reason for (5.18) and (5.19) to be isomorphic. A field automorphism moves embeddings
of $F_H$ inside $M$; a coefficient automorphism moves roots of unity and Hecke values. The two
actions commute by (5.3a), giving a rectangular array of conjugate packet data. This array is
what is meant by a conjugate-compatible family.

At the top field, the row indexed by a coefficient embedding $\sigma$ base changes to
$\pi_M^\sigma$, not literally to $\pi_M$, and every quotient twist becomes trivial. Within
that fixed $\sigma$-row, field-conjugate entries identify with the corresponding transports of
$\pi_M^\sigma$. At a good rational prime, field conjugation permutes the factors in (8.4),
whereas coefficient conjugation applies $\sigma$ to all their coefficients. These two checks
prove that the rectangular array is coherent without confusing its two actions, choosing
intertwiners, or asserting a descent through the normalizer.

## 6. The controlled field family from potential automorphy

Finite-group induction becomes arithmetic only after every subgroup is attached to a fixed
field and every linear character to a Hecke character. Book 186 provides much more than
isolated automorphy statements: one Galois top, all elementary fixed fields, compatible
conjugates, selected descents, and prescribed local completions. We recall exactly that
interface here and explain how the solvable transfer theorems of Books 96--97 act inside it.

### 6.1 The Galois top and its fixed fields

Retain the field $M$ of Section 1.2 and put $F_H=M^H$. Galois correspondence gives

$$
F_{H_1}F_{H_2}=F_{H_1\cap H_2},
\qquad
F_{H_1}\cap F_{H_2}=F_{\langle H_1,H_2\rangle},
\tag{6.1}
$$

and $\gamma(F_H)=F_{\gamma H\gamma^{-1}}$. Every $F_H$ is totally real. The closure-level
disjointness built into $M$ preserves the residual image and the residual-cyclotomic image on
every $G_{F_H}$.

This is stronger than choosing unrelated potential-automorphy fields for the finitely many
$H_i$. Mackey decomposition needs all fixed fields inside one Galois closure, and conjugation
needs the packets to arise from one top packet.

The controlled-completion statement can be written purely in group language. Fix a place
$\widetilde v$ of $M$ above a rational place $v$ and let $D_v\leq\Gamma$ be its decomposition
group. The places of $F_H$ above $v$ are indexed by

$$
D_v\backslash\Gamma/H.
\tag{6.1a}
$$

For the place represented by $\gamma$, there is an isomorphism

$$
(F_H)_{w_\gamma}
\simeq
M_{\widetilde v}^{\,D_v\cap\gamma H\gamma^{-1}}.
\tag{6.1b}
$$

To prove it, replace the embedding $F_H\hookrightarrow M$ by its $\gamma$-conjugate. Its image
is $F_{\gamma H\gamma^{-1}}$. Inside the local Galois extension
$M_{\widetilde v}/\mathbf Q_v$, an element fixes the completed subfield precisely when it lies
both in $D_v$ and in $\gamma H\gamma^{-1}$, giving (6.1b). Two representatives yield the same
place exactly when they differ on the left by $D_v$ and on the right by $H$, giving (6.1a).

Thus the “all completions” clause of Book 186 passes automatically to every elementary fixed
field. It does not merely control the number of primes or their residue degrees: it identifies
the actual completed field as the fixed field of an explicit intersection subgroup. Formula
(3.7) is the representation-theoretic version of this same statement.

The local subgroup $D_v\cap\gamma H\gamma^{-1}$ in (6.1b) need not be elementary, because a
decomposition group $D_v$ need not be elementary. It indexes a completed field and a local
Mackey block, not automatically a packet in the elementary family. The overlap theorem below
is applied instead to global intersections of two elementary subgroups. This distinction keeps
the completion formula valid without inventing an unavailable packet for an arbitrary local
intersection.

### 6.2 Automorphic packets over elementary fixed fields

If $H$ is $p$-elementary, it is solvable and admits a subnormal series

$$
1=H_0\triangleleft H_1\triangleleft\cdots\triangleleft H_r=H
\tag{6.2}
$$

with prime-order quotients. Reversing fixed fields gives a tower

$$
M=F_{H_0}\supset F_{H_1}\supset\cdots\supset F_{H_r}=F_H
\tag{6.3}
$$

of prime cyclic extensions. Books 96--97 therefore apply at every step.

Book 186 uses this tower only after automorphy of the chosen lift over $M$ has been proved. It
produces a cuspidal parallel-weight-two packet $\pi_H$ with cyclotomic determinant and exact
base change $\pi_M$. Its selected $\lambda_0$-adic realization is the actual restriction of
$\rho$, not merely a representation with the same residual reduction.

### 6.3 Prime-cyclic descent and uniqueness

At one step $L'/L$ in (6.3), the packet upstairs is invariant under
$\operatorname{Gal}(L'/L)$ because its good Hecke polynomials come from a Galois representation
already extending to $G_L$. Cyclic descent gives packets downstairs differing by characters of
$\operatorname{Gal}(L'/L)$. The extending representation selects the unique twist whose good
traces and determinant match it. Strong multiplicity one then gives uniqueness of the packet.

Iterating proves

$$
r_{\pi_H,\lambda_0}\simeq\rho|_{G_{F_H}}.
\tag{6.4}
$$

Independence of the series (6.2) follows because two endpoints have the same good Hecke
polynomials and fixed central character. Residual-image preservation rules out a noncuspidal
endpoint: a two-character isobaric sum would have reducible Galois semisimplification.

This argument also explains why arbitrary solvable descent is insufficient. Without the
extension (6.4), cyclic descent leaves a finite twisting torsor at each layer, and unrelated
choices need not be compatible around two different towers.

### 6.4 The local, coefficient, and overlap ledgers

The family $\{\pi_H\}$ comes with the following simultaneous records.

- At places above $2$, the top extension is split in the prescribed construction. The packets
  carry the same primitive tame order-three type, trivial wild inertia, and zero monodromy.
- At places above $\ell$, every completion is the prescribed unramified extension and the
  selected coefficient-linear finite-flat lattice restricts without changing its labeled
  component.
- Away from $2\ell$, the distinguished Galois realizations are unramified; good Frobenius
  polynomials are related by the correct Frobenius powers when residue degrees exceed one.
- One number field contains the good eigenvalues, central characters, and finite type values of
  the finitely many packets needed by $\mathfrak B$.
- Conjugation carries $\pi_H$ to $\pi_{\gamma H\gamma^{-1}}$ with all pairing, orientation, and
  lattice labels transported.

These clauses will be used individually. In particular, the Frobenius-power clause prevents the
common error of assigning the same trace to a prime and to a residue-degree-$f$ prime above it.

We now extract the overlap compatibility that is not supplied merely by restriction to the top
field. First record the recognition theorem in exactly the form needed.

**Lemma 6.1 (Chebotarev--Brauer--Nesbitt comparison).** Let $L$ be a number field, let $C$ be a
characteristic-zero nonarchimedean local field, and let

$$
s_1,s_2:G_L\longrightarrow\operatorname{GL}_n(C)
$$

be continuous representations unramified outside finite sets. If their Frobenius characteristic
polynomials agree at all but finitely many finite places of $L$, then

$$
s_1^{\mathrm{ss}}\simeq s_2^{\mathrm{ss}}
$$

after a common finite scalar extension. Equality of traces at all but finitely many places is
already sufficient.

**Proof.** The Chebotarev theorem of Book 171, Theorem 4.3, applied in every finite Galois
quotient of $G_L$, says that the unramified Frobenius conjugacy classes outside a prescribed
finite set are dense for continuous class functions on $G_L$. Thus equality of the displayed
polynomials gives equality of the continuous trace functions on all of $G_L$.

For completeness, the remaining step is the Brauer--Nesbitt argument, not a further imported
recognition theorem. After extending scalars, let $A$ be the finite-dimensional algebra generated
by the image of $C[G_L]$ in
$\operatorname{End}(s_1^{\mathrm{ss}}\oplus s_2^{\mathrm{ss}})$. Equality on every group
element makes the two trace functionals on $A$ equal by linearity. Both modules are semisimple,
so they factor through $A/\operatorname{rad}(A)$. Over an algebraic closure this quotient is a
product of matrix algebras; the traces of its simple modules are linearly independent on the
central matrix idempotents. The two modules therefore have the same simple multiplicities and
are isomorphic. $\square$

**Proposition 6.2 (semisimple compatibility on elementary intersections).** Let $D\leq H$ be
elementary subgroups of $\Gamma$, put

$$
F=F_H=M^H,
\qquad
L=F_D=M^D,
$$

and use the common Galois coefficient field $K$ of Section 5.1, enlarged to contain the packet
data for $H$ and $D$. Write

$$
r_{H,\tau}:=r_{\pi_H,\tau}
$$

for the realization selected by an embedding. For every embedding

$$
\tau:K\hookrightarrow\Omega
$$

into an algebraically closed characteristic-zero nonarchimedean field,

$$
\boxed{
\left(r_{H,\tau}|_{G_{F_D}}\right)^{\mathrm{ss}}
\simeq r_{D,\tau}.}
\tag{6.4a}
$$

The isomorphism is understood after placing the two finite local fields of definition inside one
common finite subextension of $\Omega$.

**Proof.** Exclude the finitely many places at which $L/F$ is ramified, either packet is
ramified, local--global compatibility is not in the ledger, or the residue characteristic is
the coefficient characteristic. Let $u$ be any remaining place of $L$, let $v$ be the place of
$F$ below it, and put $f=f(u/v)$. Write the algebraic Hecke polynomial of $\pi_H$ at $v$ as

$$
Q_{H,v}(X)=X^2-a_{H,v}X+d_{H,v}\in K[X].
$$

Define

$$
A_0(a,d)=2,\qquad A_1(a,d)=a,\qquad
A_m(a,d)=aA_{m-1}(a,d)-dA_{m-2}(a,d).
\tag{6.4b}
$$

If the roots of $Q_{H,v}$ are $\alpha,\beta$, then
$A_f(a_{H,v},d_{H,v})=\alpha^f+\beta^f$. Hence restriction from $G_F$ to $G_L$ has at $u$
the algebraic Frobenius polynomial

$$
Q_{H,v}^{[f]}(X)
=X^2-A_f(a_{H,v},d_{H,v})X+d_{H,v}^{\,f}\in K[X].
\tag{6.4c}
$$

This is only the functoriality of arithmetic Frobenius in a residue-field tower: an arithmetic
Frobenius at $u$ maps to the $f$th power of one at $v$, up to inertia and conjugacy. It does not
require $L/F$ to be Galois.

At the distinguished embedding $\tau_0$, Book 186 gives the exact identifications

$$
r_{\pi_H,\tau_0}\simeq\rho|_{G_F},
\qquad
r_{\pi_D,\tau_0}\simeq\rho|_{G_L}.
$$

Both $\tau_0(Q_{H,v}^{[f]})$ and the image of the Hecke polynomial $Q_{D,u}$ are therefore
$\det(X-\rho(\operatorname{Frob}_u))$. Since
$\tau_0:K\hookrightarrow\overline{\mathbf Q}_\ell$ is injective,

$$
Q_{D,u}(X)=Q_{H,v}^{[f]}(X)
\quad\text{in }K[X].
\tag{6.4d}
$$

Apply any $\tau$. Local--global compatibility for the two already existing packet
representations turns (6.4d) into equality of the Frobenius characteristic polynomials of
$r_{H,\tau}|_{G_L}$ and $r_{D,\tau}$ at every $u$ outside a finite set. Lemma 6.1 now
proves (6.4a). No cyclic or solvable base change over $L/F$ has entered the argument. $\square$

Several parts of the conclusion must be kept explicit.

First, equality only after restriction to $G_M$ could leave a character of
$G_L/G_M=D$ between two extensions of the top realization. Proposition 6.2 compares Frobenius
on $G_L$ itself. Thus any quotient character still relating two descriptions must be a genuine
self-twist of $r_{D,\tau}$ and produces the same semisimple isomorphism class; there is no
uncontrolled quotient-character ambiguity. The proposition neither declares that self-twist
character trivial nor chooses an intertwiner or a compatible cocycle.

Second, the polynomial equality (6.4d) lies in the one algebraic field $K$. It therefore
survives every coefficient embedding and commutes with coefficient conjugation. Field
conjugation carries the entire statement to the corresponding conjugate subgroups and places.

Third, restriction from $G_F$ to its finite-index subgroup $G_L$ preserves semisimplicity in
characteristic zero, by the normal-core and finite-quotient averaging argument written out in
Section 7.4. Thus the superscript in (6.4a) records the safe convention rather than hiding an
extension class. The global isomorphism restricts at every place of $L$. Away from the coefficient
characteristic it identifies the actual local Weil--Deligne representations, including inertia
and monodromy; at the coefficient characteristic it identifies the characteristic-zero local
Galois representations and hence their Hodge--Tate and crystalline properties whenever those
are supplied by the packet ledger. A finite-flat **lattice** assertion remains separate and is
addressed in the next paragraph. This conclusion follows after the global
semisimple isomorphism has been proved. It does not reconstruct a common algebraic bad-place
parameter from the good Frobenius polynomials alone, nor does it choose a pairing-, orientation-,
or type-line-preserving local intertwiner at a general coefficient embedding.

Finally, (6.4a) is a characteristic-zero statement. At $\tau_0$, the named Book-186
identifications with $\rho|_{G_L}$ make the restricted $H$-packet lattice and the $D$-packet
lattice homothetic after the common coefficient enlargement, by residual irreducibility; their
selected local labels and finite-flat quotient records are the restrictions of the same named
record. At a general $\tau$, Brauer--Nesbitt supplies no lattice, homothety, integral
intertwiner, or residual identification.

Here is the form used in every pairwise Mackey calculation. For elementary $H,J\leq\Gamma$ and
$x\in\Gamma$, put

$$
D=H\cap xJx^{-1},
\qquad
L=M^D=F_H\,x(F_J).
$$

The group $D$ is elementary because it is a subgroup of the elementary group $H$.

Applying Proposition 6.2 twice, and using conjugation compatibility, gives

$$
\boxed{
\left(r_{H,\tau}|_{G_L}\right)^{\mathrm{ss}}
\simeq r_{D,\tau}
\simeq
\left({}^x r_{J,\tau}|_{G_L}\right)^{\mathrm{ss}}.}
\tag{6.4e}
$$

If $\theta_H$ and $\theta_J$ are the corresponding Brauer characters, set

$$
\alpha=\theta_H|_D,
\qquad
\beta=({}^x\theta_J)|_D,
\qquad
\delta=\beta\alpha^{-1}.
\tag{6.4f}
$$

Then the two twisted restrictions on this particular double coset are

$$
\begin{aligned}
\left((r_{H,\tau}\otimes\theta_{H,\tau})|_{G_L}\right)^{\mathrm{ss}}
&\simeq r_{D,\tau}\otimes\alpha_\tau,\\
\left({}^x(r_{J,\tau}\otimes\theta_{J,\tau})|_{G_L}\right)^{\mathrm{ss}}
&\simeq r_{D,\tau}\otimes\beta_\tau
\simeq (r_{D,\tau}\otimes\alpha_\tau)\otimes\delta_\tau.
\end{aligned}
\tag{6.4g}
$$

Here $\alpha_\tau$, $\beta_\tau$, and $\delta_\tau$ mean inflation through
$G_L\twoheadrightarrow D$ followed by $\tau$. Their root-of-unity values lie in $K$, and each
has its canonical free rank-one unit lattice. This integral rank-one fact does not upgrade the
rank-two comparison in (6.4e) to a lattice comparison.

Tensoring both arguments by $\alpha_\tau^{-1}$ gives the downstream Hom-ready identity

$$
\begin{aligned}
&\operatorname{Hom}_{G_L}\!\left(
(r_{H,\tau}\otimes\theta_{H,\tau})|_{G_L},
{}^x(r_{J,\tau}\otimes\theta_{J,\tau})|_{G_L}\right)\\
&\qquad\simeq
\operatorname{Hom}_{G_L}\!\left(
r_{D,\tau},r_{D,\tau}\otimes\delta_\tau\right).
\end{aligned}
\tag{6.4h}
$$

Thus the ratio is $\delta=\beta\alpha^{-1}$ in this direction, not its inverse. The displayed
vector-space isomorphism uses choices of the semisimple overlap intertwiners, but its dimension
does not; no coherent system of intertwiners is part of the export.

The subgroup $D$, the field $L$, and the character ratio $\delta$ must be recomputed for each
representative in $H\backslash\Gamma/J$; no two distinct double-coset contributions are merged.
Equations (6.4e)--(6.4h) are the complete semisimple overlap export.

### 6.5 Automorphic restriction, twisting, and formal induction

There are three operations in the construction, and they should not be conflated.

First, **automorphic restriction** means base change. At a prime cyclic step $L'/L$, the local
Langlands parameter of $\operatorname{BC}_{L'/L}(\pi)$ at $w\mid v$ is

$$
\operatorname{rec}_{L'_w}
\bigl(\operatorname{BC}_{L'/L}(\pi)_w\bigr)
=
\operatorname{rec}_{L_v}(\pi_v)|_{W_{L'_w}}.
\tag{6.5}
$$

Books 96--97 prove that these local restrictions assemble globally through the solvable tower,
that the endpoint is independent of its prime refinement, and that weights, contragredients,
central characters, and coefficient conjugation commute with the operation. In our direction,
$\pi_H$ base changes upward to $\pi_M$.

Second, **automorphic twisting** is an operation over one field:

$$
\pi_H\longmapsto\pi_H\otimes(\psi_H\circ\det).
\tag{6.6}
$$

Its Galois realization is $r_{\pi_H,\lambda}\otimes\psi_{H,\lambda}$, its central character is
$\omega_{\pi_H}\psi_H^2$, and its local parameter is the tensor product by the local character.
Finite-order twisting preserves algebraicity and parallel weight two. It may change conductor
where $\psi_H$ ramifies and changes determinant by the square of the character; both changes
are retained in the ledger.

Third, **Galois induction** from $G_{F_H}$ to $G_{\mathbf Q}$ is always defined because the
subgroup has finite index, even when $F_H/\mathbf Q$ is nonnormal. It produces a representation
of dimension $2[\Gamma:H]$ and the local formula (3.7).

There is no corresponding global automorphic induction theorem for a general rank-two packet
over an arbitrary nonnormal $F_H/\mathbf Q$ among our inputs. We therefore use the phrase
*formal automorphic induction* only for an incomplete Euler-factor identity. Let $S$ contain
the residue characteristic of $\lambda$, every rational prime ramified in $M$, every prime
below the conductor of $\pi_H$ or $\psi_H$, and every place at which local--global
compatibility has not been entered in the ledger. Write $L^S_{\mathbf Q}$ for the product over
$v\notin S$ and $L^{S_{F_H}}_{F_H}$ for the product over places of $F_H$ not above $S$. Then

$$
L^S_{\mathbf Q}\left(
\operatorname{Ind}_{G_{F_H}}^{G_{\mathbf Q}}
(r_{\pi_H,\lambda}\otimes\psi_{H,\lambda}),s\right)
=
L^{S_{F_H}}_{F_H}(\pi_H\otimes\psi_H,s).
\tag{6.7}
$$

Formula (6.7) is good-place Artin formalism, proved by multiplying the cyclic-block identity
(8.2) over $v\notin S$. No equality of omitted bad local factors is asserted here; their full
virtual Weil--Deligne record is retained in Chapter 10 instead. The incomplete identity
identifies the available Euler data; it does not manufacture an
automorphic representation on $\mathrm{GL}_{2[F_H:\mathbf Q]}(\mathbf A_{\mathbf Q})$.

This separation is what allows the **automorphic-operation** part of the argument to use only
Books 95--97. Automorphic operations occur along solvable extensions above $F_H$ and as twists
over $F_H$; the only induction across the potentially nonsolvable bottom is on the Galois and
Euler-factor sides. The distinct Galois recognition step in Proposition 6.2 uses the
Chebotarev input of Book 171 recorded in Lemma 6.1.

The elementary-intersection row below is a comparison of two already constructed Galois
realizations, not a fourth automorphic operation. In particular, the notation $r_{\pi_D}$ in
that row does not mean that $\pi_H$ has been base changed to $M^D$.

The complete dictionary is:

| Operation | Galois realization | Automorphic datum | Required warning |
|---|---|---|---|
| prime-cyclic base change $L'/L$ | restrict from $G_L$ to $G_{L'}$ | $\operatorname{BC}_{L'/L}$ | cuspidality can fail at a self-twist |
| selected cyclic descent | extend from $G_{L'}$ to $G_L$ using the named representation | invariant packet with its twist selected | invariance alone leaves quotient-character ambiguity |
| elementary intersection $M^D/F_H$ | restrict an existing $r_{\pi_H,\tau}$ and identify it semisimply with $r_{\pi_D,\tau}$ by Proposition 6.2 | the already existing packet $\pi_D$ | no automorphic base change is asserted when $D$ is nonnormal in $H$ |
| finite-order twist | tensor by $\psi_\lambda$ | $\pi\otimes(\psi\circ\det)$ | center and determinant change by $\psi^2$ |
| coefficient conjugation | apply $\sigma$ to matrix coefficients | $\pi^\sigma$ | this does not move the number field |
| field conjugation | conjugate the subgroup and local decomposition groups | the conjugate packet | this permutes places and fixed fields |
| induction from $F_H/\mathbf Q$ | finite Galois induction | only formal induced Euler data | no global higher-rank automorphic induction is invoked |

At a finite place away from the coefficient characteristic, the same rows can be read through
Weil--Deligne parameters. Base change is restriction of the Weil group, twisting is tensor
product by a one-dimensional parameter, and Galois induction is Weil-group induction followed
by the direct sum over places in (3.7). Monodromy restricts and induces with the representation;
a finite-order twist has monodromy zero and therefore cannot create a nonzero $N$, although it
can change inertia.

### 6.6 A nonabelian elementary descent tower

Elementary does not mean abelian. Consider

$$
H=C_3\times D_8,
\qquad
D_8=\langle r,s:r^4=s^2=1,\ srs=r^{-1}\rangle.
\tag{6.8}
$$

This is $2$-elementary: the prime-to-$2$ factor is cyclic and the $2$-factor is a nonabelian
$2$-group. A prime-order subnormal series is

$$
1
\triangleleft\langle r^2\rangle
\triangleleft\langle r\rangle
\triangleleft D_8
\triangleleft C_3\times D_8.
\tag{6.9}
$$

The successive quotient orders are $2,2,2,3$. If $H$ occurs in $\Gamma$ and
$F_H=M^H$, reversing (6.9) produces the tower

$$
M=L_0\supset L_1\supset L_2\supset L_3\supset L_4=F_H
\tag{6.10}
$$

with cyclic degrees $2,2,2,3$. At each step the packet over $L_{j-1}$ is invariant because its
$\lambda_0$-adic representation extends to $G_{L_j}$. Cyclic descent offers finitely many
twists. Comparing with $\rho|_{G_{L_j}}$ selects one; then the next step begins with that
selected packet rather than with an arbitrary point in the previous descent fiber.

A linear Brauer character of $H$ factors through

$$
H^{\mathrm{ab}}\simeq C_3\times C_2\times C_2.
\tag{6.11}
$$

It can therefore carry independent cubic and quadratic values. Its Hecke avatar over $F_H$
is not assembled by choosing unrelated characters at the four cyclic stages. It is the single
character attached by reciprocity to $G_{F_H}/G_M=H$, and its restrictions to the stages are
automatically compatible. This distinction prevents an overcount by the product of all
stepwise character groups.

Suppose another subnormal series passes first through a reflection subgroup of $D_8$. The
intermediate packets can differ, but both endpoints are selected by the same extending
representation. Their good polynomials and central characters agree, so strong multiplicity
one identifies the two packets over $F_H$. Thus tower independence is a theorem about selected
endpoints, not a claim that the intermediate towers coincide.

At a controlled rational prime $v$, formula (6.1b) computes every completion in (6.10) by
intersecting the fixed decomposition group $D_v$ successively with the groups in (6.9). Hence
local degrees in the tower can be $1$ even when the global step has degree $2$ or $3$; the
correct local parameter operation is governed by those intersections, not by the global list
$2,2,2,3$.

### 6.7 Sensitive places in the controlled top

Three kinds of rational places illustrate how the Book-186 field control enters the Brauer
family.

At $2$, the decomposition group $D_2$ is trivial. Formula (6.1b) gives

$$
(F_H)_v=\mathbf Q_2
\tag{6.12}
$$

for every $v\mid2$ and every $H$. There are $[\Gamma:H]$ such places. The quotient
$G_{F_H}\to H$ is locally trivial, so every $\theta_H$ is trivial there. The primitive
order-three tame type is therefore copied without twisting.

At $\ell$, the local top $M_{\widetilde v}/\mathbf Q_\ell$ is one of the prescribed unramified
extensions. Its decomposition group $D_\ell$ is cyclic, generated by Frobenius. For the place
of $F_H$ represented by $\gamma$,

$$
(F_H)_{v_\gamma}
=M_{\widetilde v}^{\,D_\ell\cap\gamma H\gamma^{-1}}.
\tag{6.13}
$$

Every such subextension is unramified. The quotient character $\theta_H$ can be nontrivial on
Frobenius, but it is trivial on inertia. Hence it preserves finite-flatness and Hodge--Tate
weights while translating Frobenius and determinant, exactly as described in Section 10.3.

At an auxiliary rational prime ramified in $M$, the decomposition group can contain inertia
$I_v$. The local character $\theta_H$ is trivial on inertia precisely when

$$
I_v\cap\gamma H\gamma^{-1}
\subseteq\ker(\theta_H^\gamma)
\tag{6.14}
$$

for the chosen place. If this containment fails, the twist contributes finite inertial type.
Even if the packet representation itself is unramified over $(F_H)_{v_\gamma}$, induction to
$\mathbf Q_v$ may have permutation ramification from the extension and character ramification
from $\theta_H$. These primes belong to $S_0$; no good-prime polynomial is used there.

The three cases clarify the phrase “controlled family.” It does not mean every intermediate
field has the same completion. It means every completion is computed from a named local top
and an explicit intersection, so one knows in advance which type is unchanged, unramifiedly
translated, or genuinely ramified.

### 6.8 Elementary subgroups inside the symmetric top

The abstract Brauer theorem applies to
$\Gamma=S_d\times C_2$, but it is helpful to picture some of its elementary subgroups. A
$p$-elementary subgroup has the form $C\times P$, where the cyclic prime-to-$p$ group $C$
centralizes the $p$-group $P$. In a symmetric group this often comes from disjoint supports.

For instance, when $d\ge7$, let a $3$-cycle act on $\{1,2,3\}$ and let a copy of $D_8$ act on
$\{4,5,6,7\}$ as the symmetries of a square. Their actions commute, giving

$$
C_3\times D_8\leq S_d.
\tag{6.15}
$$

This is the group used in Section 6.6. One can multiply either factor by the external $C_2$ in
$\Gamma$ when the direct-product condition remains satisfied. Its fixed field is usually
nonnormal over $\mathbf Q$, but the top extension over it has solvable group
$C_3\times D_8$.

Another source is a cyclic subgroup generated by a permutation with several disjoint cycles.
Every cyclic group is elementary: choose any prime dividing its order, split the cyclic group
as the product of its prime-to-$p$ part and its $p$-primary part. Thus the cyclic subgroups
appearing in ordinary Artin induction already lie in the Brauer family. Brauer's improvement is
that adding centralizing $p$-groups removes all denominators and gives integer coefficients.

Not every solvable subgroup of $S_d$ is elementary. The natural $S_3$ on three letters and the
dihedral groups $D_{2p}$ are semidirect products, not direct products. Their worked Brauer
relations decompose them further into cyclic elementary pieces. More complicated solvable
subgroups may themselves contain the elementary subgroups used by the global relation, but
Brauer induction never asks us to descend to the fixed field of the whole solvable subgroup
unless it actually occurs as an elementary term.

Since $\Gamma$ is finite, there are only finitely many subgroups and linear characters.
Theorem 4.4 chooses a finite relation, and only the corresponding finite list of packet fields
is needed. We do not form an infinite collection indexed by all possible characters. This
finiteness is what permits one coefficient field, one exceptional set of primes, and one
simultaneous conjugation ledger.

Finally, all fixed fields remain totally real regardless of subgroup shape. Solvability controls
the descent tower $M/F_H$; total reality controls the archimedean packet. These are independent
advantages of the controlled top and should not be merged into one hypothesis.

## 7. The induced virtual Galois family

We now replace the abstract two-dimensional module in (4.15) by compatible rank-two Galois
representations supplied over different fixed fields. At the distinguished coefficient place
they are all restrictions of one representation, so the tensor identity applies literally. At
other coefficient places they are related through automorphic compatibility rather than by a
known common base-field representation. That one change is why the output is virtual and why
the distinguished member plays a special role.

### 7.1 Construction at every coefficient place

For each finite place $\lambda$ of $K$, let

$$
r_{i,\lambda}:G_{F_i}\longrightarrow
\operatorname{GL}_2(\overline K_\lambda)
\tag{7.1}
$$

be the semisimple Galois representation attached to $\pi_{H_i}$, and let
$\theta_{i,\lambda}$ be the $\lambda$-adic avatar of $\theta_i$. Define $\mathcal R_\lambda$ by
(1.6).

Each induction has finite index, hence is continuous: with coset representatives fixed, its
matrix entries are entries of $r_{i,\lambda}$ multiplied by finite permutation matrices and
root-of-unity values. Semisimplifying before entering the Grothendieck group changes no class
in characteristic zero.

The virtual rank is

$$
\operatorname{rk}\mathcal R_\lambda
=\sum_i n_i\,2[\Gamma:H_i]=2
\tag{7.2}
$$

by (5.7).

### 7.2 Recovery of the chosen member

At $\lambda_0$, equation (6.4) gives

$$
r_{i,\lambda_0}\otimes\theta_{i,\lambda_0}
\simeq
\rho|_{G_{F_i}}\otimes\widetilde\theta_i.
$$

Inflate the finite-group relation (4.12) from $\Gamma$ to $G_{\mathbf Q}$. The tensor identity
(2.7) gives

$$
\begin{aligned}
\mathcal R_{\lambda_0}
&=\sum_i n_i
[\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(\rho|_{G_{F_i}}\otimes\widetilde\theta_i)]\\
&=[\rho]\cdot
\sum_i n_i[\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}\widetilde\theta_i]
=[\rho].
\end{aligned}
\tag{7.3}
$$

Because $\rho$ is absolutely irreducible, the final class is effective and represented by the
chosen representation. This effectivity uses the pre-existing $\rho$ and holds only at the
distinguished member; it is not a positivity argument for the other $\lambda$.

### 7.3 Rank and determinant

Every $r_{i,\lambda}$ has determinant $\chi_\lambda|_{G_{F_i}}$. Applying (5.4) to its twist by
$\theta_{i,\lambda}$ and multiplying with exponents $n_i$ gives

$$
\det\mathcal R_\lambda
=\chi_\lambda^{\sum_i n_i[\Gamma:H_i]}
\prod_i(\operatorname{Ver}_{H_i}^{\Gamma}\theta_i)^{2n_i}.
$$

Here the actual determinant calculation uses transfer from the open subgroup
$G_{F_i}\leq G_{\mathbf Q}$. The cycle definition (5.4a) shows that transfer of the inflated
character $\widetilde\theta_i$ is the inflation along
$G_{\mathbf Q}\twoheadrightarrow\Gamma$ of
$\operatorname{Ver}_{H_i}^{\Gamma}\theta_i$; the coset permutations are literally the same.
This justifies the finite-quotient notation in the displayed formula.

Equations (5.6)--(5.7) reduce this to

$$
\boxed{\det\mathcal R_\lambda=\chi_\lambda.}
\tag{7.4}
$$

This is a determinant-line identity in the Grothendieck group. It does not assert that a
two-dimensional vector space realizing $\mathcal R_\lambda$ exists.

### 7.4 Continuity and semisimplification

Write $n_i=n_i^+-n_i^-$ with $n_i^\pm\ge0$, and set

$$
R_\lambda^\pm=
\bigoplus_i
\left(
\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(r_{i,\lambda}\otimes\theta_{i,\lambda})
\right)^{\oplus n_i^\pm}.
\tag{7.5}
$$

Then $\mathcal R_\lambda=[R_\lambda^+]-[R_\lambda^-]$ with both sides actual continuous
semisimple representations. This presentation is useful for traces and determinants, but it is
not canonical: adding the same representation to $R_\lambda^+$ and $R_\lambda^-$ changes the
presentation without changing the class.

Here semisimplicity of induction deserves justification because the ambient profinite
representation category is not itself semisimple. Let $H$ be an open subgroup of a profinite
group $G$, let $W$ be semisimple over a characteristic-zero field, and put
$N=\bigcap_{g\in G}gHg^{-1}$. This normal core is open. If $W$ is irreducible over $H$, choose
an irreducible $N$-submodule $U$. The sum of its finitely many $H$-conjugates is an $H$-stable
semisimple submodule, hence is all of $W$; therefore $W|_N$ is semisimple. The same follows for
semisimple $W$ by direct sum. Formula (3.4) now shows that
$\operatorname{Ind}_H^GW|_N$ is a direct sum of conjugates of $W|_N$, hence semisimple.

Finally, if $A$ is a $G$-submodule of this induction, choose an $N$-equivariant projection
$p$ onto $A$. Averaging over the finite group $G/N$ gives

$$
\overline p=\frac1{[G:N]}\sum_{g\in G/N}gpg^{-1}.
\tag{7.5a}
$$

Every summand maps into $A$ and restricts to the identity on $A$, so $\overline p$ is a
$G$-equivariant projection onto $A$. Thus the induced representation is semisimple. Its
continuity follows from the finite-coset model (3.3a).

Character equality determines a virtual semisimple class. It does not determine extensions
inside a nonsemisimple lattice. Accordingly, every equality in this chapter is a
characteristic-zero semisimple equality unless an integral lattice is explicitly named.

### 7.5 The S3 pattern over number fields

The relation (4.17) gives a transparent model of (1.6). Suppose for this paragraph that
$M/\mathbf Q$ has group $S_3$. Let

$$
F_2=M^{C_2},\qquad [F_2:\mathbf Q]=3,
\qquad
F_3=M^{C_3},\qquad [F_3:\mathbf Q]=2.
\tag{7.6}
$$

The character $\omega$ of $C_3$ becomes a cubic Hecke character of the quadratic field $F_3$.
For compatible rank-two packets $\pi_2$ over $F_2$ and $\pi_3$ over $F_3$, the virtual class is

$$
\mathcal R_\lambda
=
\left[\operatorname{Ind}_{G_{F_2}}^{G_{\mathbf Q}}r_{\pi_2,\lambda}\right]
-
\left[\operatorname{Ind}_{G_{F_3}}^{G_{\mathbf Q}}
(r_{\pi_3,\lambda}\otimes\omega_\lambda)\right].
\tag{7.7}
$$

The two actual terms have dimensions six and four, so the virtual rank is two. If both packets
at the distinguished place are restrictions of $\rho$, the tensor identity turns (7.7) into

$$
[\rho]\left(
[\operatorname{Ind}_{C_2}^{S_3}1]
-[\operatorname{Ind}_{C_3}^{S_3}\omega]\right)
=[\rho].
\tag{7.8}
$$

The negative term is four-dimensional; it is not a small correction that can be discarded.
At another coefficient place, nothing in the dimension calculation says that its constituents
occur inside the six-dimensional positive term. This is a concrete version of the effectivity
boundary.

The fixed fields also illustrate why solvable top descent and nonsolvable bottom induction play
different roles. Both $C_2$ and $C_3$ are elementary, so $\pi_M$ descends through
$M/F_2$ and $M/F_3$. The cubic field $F_2$ is not Galois over $\mathbf Q$, but the Galois
induction in the first term of (7.7) remains perfectly well defined.

### 7.6 Restriction back to the Galois top

Although $\mathcal R_\lambda$ need not be effective over $\mathbf Q$, its restriction to
$G_M$ is completely controlled at every coefficient place. Profinite Mackey gives

$$
\operatorname{Res}_{G_M}^{G_{\mathbf Q}}
\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(r_{i,\lambda}\otimes\theta_{i,\lambda})
\simeq
\bigoplus_{\gamma\in\Gamma/H_i}
{}^\gamma(r_{i,\lambda}|_{G_M}).
\tag{7.9}
$$

The quotient character disappears because it is inflated from
$G_{F_i}/G_M$: its restriction to $G_M$ is trivial. Moreover,
$\operatorname{BC}_{M/F_i}(\pi_{H_i})=\pi_M$. Local--global compatibility and strong
multiplicity one give

$$
r_{i,\lambda}|_{G_M}\simeq r_{\pi_M,\lambda}
\tag{7.10}
$$

after semisimplification and scalar extension. Conjugation compatibility of the top packet
identifies every summand in (7.9) with $r_{\pi_M,\lambda}$. Consequently

$$
\begin{aligned}
\operatorname{Res}_{G_M}^{G_{\mathbf Q}}\mathcal R_\lambda
&=
\sum_i n_i[\Gamma:H_i]\,[r_{\pi_M,\lambda}]\\
&=[r_{\pi_M,\lambda}]
\end{aligned}
\tag{7.11}
$$

by (5.7).

Equation (7.10) is the case $D=1$ of Proposition 6.2. The full proposition is strictly
stronger: for every elementary $D\leq H_i$ it stops at $G_{M^D}$ and identifies the restricted
packet with $r_{\pi_D,\lambda}$ there. Thus the specialization (3.15c) is available for each
intermediate Mackey double coset, while (7.9)--(7.11) are the top-field specialization in which
all $D$ are trivial.

This identity has several uses. It checks that the virtual family has the correct top-field
member for every $\lambda$, not only at $\lambda_0$. It proves that all auxiliary quotient
twists disappear after returning to $M$. It also explains conjugate-packet coherence: the
coset summands in Mackey are not merely isomorphic by coincidence; each is the corresponding
conjugate realization of the one packet $\pi_M$.

Yet (7.11) does not descend effectivity. Restriction can identify distinct irreducible
representations and can turn a negative global multiplicity into cancellation among identical
top-field constituents. A virtual class can restrict to an actual representation on a finite
index subgroup without being actual on the full group; extension data and the action of the
finite quotient are precisely what restriction forgets.

### 7.7 Scalar extension and field-of-definition independence

The construction is often written over $\overline K_\lambda$, but every finite list of summands
is defined over a finite extension $C_\lambda/K_\lambda$. If
$C'_\lambda/C_\lambda$ is further finite, scalar extension sends

$$
\mathcal R_{\lambda,C_\lambda}
\longmapsto
\mathcal R_{\lambda,C_\lambda}\otimes_{C_\lambda}C'_\lambda.
\tag{7.12}
$$

Ranks, determinant characters, traces, and characteristic series commute with this operation.
If two virtual semisimple classes over $C_\lambda$ become equal over $C'_\lambda$, their
characters were already equal over $C_\lambda$ because the scalar embedding is injective;
characteristic-zero semisimplicity then gives equality of classes. Thus none of our virtual
equalities depends on choosing a needlessly large local field.

A model over the Hecke completion itself can fail to be available before a finite extension:
an irreducible representation can have a field-of-definition obstruction even when its
character values lie in the smaller field. We avoid asserting such descent. The coefficient
ledger chooses one finite field supporting the packet realizations, and the final polynomial
$P_p$ descends to $K$ because its coefficients are explicitly in the rational function (8.4)
and polynomiality is checked through an injective embedding.

At $\lambda_0$, the chosen representation is originally defined over $E$, while packet
realizations and Brauer characters may be defined over different finite extensions. Embed all
of them into one finite extension $C/E$ inside $\overline{\mathbf Q}_\ell$. Equation (7.3) is
an equality after scalar extension to $C$. Because $\rho$ is fixed in advance, this does not
replace its $\mathcal O$-lattice by a packet lattice over $C$; it only compares
characteristic-zero representations.

If $\sigma\in\operatorname{Gal}(K/\mathbf Q)$ sends $\lambda$ to $\lambda'$, it identifies the
algebraic Frobenius record at the two places after applying $\sigma$. It does not canonically
identify the topological fields $K_\lambda$ and $K_{\lambda'}$ inside one algebraic closure,
nor the chosen lattices. This is why compatibility is stated through the $K$-polynomials and
transported local types rather than through a single module carrying all coefficient
embeddings simultaneously.

## 8. Automorphic Euler data and Frobenius polynomials

The virtual family becomes useful only if its good-prime data are algebraic and independent of
the coefficient completion. Each induced summand has a higher-degree local polynomial, and
negative Brauer coefficients initially give a rational function. The key cancellation is
witnessed at the distinguished place, where the whole expression is the chosen rank-two
representation. Injectivity of the coefficient embedding then promotes that one cancellation
to an algebraic polynomial identity before any new representation is claimed.

### 8.1 Local induction at a good prime

Let $p$ be a rational prime unramified in $M$, in every $r_{i,\lambda}$, and in every
$\theta_i$. For a place $w\mid p$ of $F_i$, write

$$
Q_{i,w}(X)=
X^2-a_{i,w}\theta_i(\operatorname{Frob}_w)X
+\theta_i(\operatorname{Frob}_w)^2Nw.
\tag{8.1}
$$

This is the Hecke polynomial of $\pi_{H_i}\otimes\psi_i$ at $w$. If its roots are
$\alpha_{i,w},\beta_{i,w}$, local induction contributes the characteristic series

$$
\det(1-\operatorname{Frob}_pT\mid
\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}r_{i,\lambda}\theta_i)
=\prod_{w\mid p}
(1-\alpha_{i,w}T^{f(w/p)})(1-\beta_{i,w}T^{f(w/p)}).
\tag{8.2}
$$

To prove (8.2), apply (3.7). On the summands indexed by the $f=f(w/p)$ embeddings in one
Frobenius orbit, $\operatorname{Frob}_p$ cyclically permutes the summands. Its $f$th power acts
on one summand as $\operatorname{Frob}_w$. For an eigenvalue $\alpha$ of that action, the cyclic
block has characteristic polynomial $1-\alpha T^f$. Multiplying the two eigenvalues and all
places proves the formula.

More explicitly, choose basis vectors $e_0,\ldots,e_{f-1}$ along one eigenline in the coset
blocks so that

$$
\operatorname{Frob}_p e_j=e_{j+1}\quad(0\le j<f-1),
\qquad
\operatorname{Frob}_p e_{f-1}=\alpha e_0.
\tag{8.2c}
$$

The matrix is the companion matrix of $X^f-\alpha$, whence

$$
\det(1-\operatorname{Frob}_pT)=1-\alpha T^f.
\tag{8.2d}
$$

Applying the same calculation to the second eigenvalue $\beta$ gives
$1-(\alpha+\beta)T^f+\alpha\beta T^{2f}$. The argument does not require diagonalizability:
the determinant identity holds after scalar extension to a splitting field, hence over the
original coefficient field by injectivity. It also does not require $F_i/\mathbf Q$ to be
Galois; the Frobenius orbit on embeddings is exactly the place $w$.

If several places lie above $p$, their Frobenius orbits on $\Gamma/H_i$ are disjoint, so their
blocks form a direct sum and their determinants multiply. This proves both the product over
$w\mid p$ and the absence of cross terms between distinct places.

For a quadratic field $F/\mathbf Q$, this gives two visibly different patterns. If
$p=ww'$ splits, both residue degrees are one and an induced rank-two representation over $F$
contributes

$$
Q_w^\ast(T)Q_{w'}^\ast(T),
\qquad
Q_w^\ast(T)=1-a_w\theta(\operatorname{Frob}_w)T
+\theta(\operatorname{Frob}_w)^2pT^2.
\tag{8.2a}
$$

If $p$ is inert, there is one place $w$ of residue degree two and the contribution is

$$
1-a_w\theta(\operatorname{Frob}_w)T^2
+\theta(\operatorname{Frob}_w)^2p^2T^4.
\tag{8.2b}
$$

In the inert case the coefficient of $T$ is zero because Frobenius exchanges the two coset
blocks. The trace of its square is encoded by $a_w$. Thus using $a_w$ as the trace of
$\operatorname{Frob}_p$ would be wrong by exactly one Frobenius power.

### 8.2 The virtual Euler product

Define

$$
D_{p,\mathfrak B}(T)=
\prod_i\prod_{w\mid p}
\left[
(1-\alpha_{i,w}T^{f(w/p)})
(1-\beta_{i,w}T^{f(w/p)})
\right]^{n_i}.
\tag{8.3}
$$

The line break in (8.3) is typographical: the bracket denotes the product of the two displayed
factors. Equivalently, and without chosen roots,

$$
D_{p,\mathfrak B}(T)=
\prod_i\prod_{w\mid p}
\left(1-a_{i,w}\theta_i(\operatorname{Frob}_w)T^{f(w/p)}
+\theta_i(\operatorname{Frob}_w)^2Nw\,T^{2f(w/p)}\right)^{n_i}.
\tag{8.4}
$$

Negative $n_i$ initially make this an element of $K(T)^\times$. Formula (8.2) proves that its
image in $\overline K_\lambda(T)$ is exactly

$$
D_{\operatorname{Frob}_p}(\mathcal R_\lambda;T).
\tag{8.5}
$$

This is the precise automorphic meaning of the virtual object: each factor in (8.4) is a
standard local Euler factor of an actual twisted $\mathrm{GL}_2$ packet over an elementary
fixed field. We do not assert an automorphic induction of that packet from the generally
non-Galois field $F_i$ to $\mathbf Q$.

### 8.3 Polynomiality from the distinguished member

At $\lambda_0$, equation (7.3) turns (8.5) into

$$
D_{p,\mathfrak B}(T)
=\det(1-\rho(\operatorname{Frob}_p)T)
=1-a_pT+pT^2
\tag{8.6}
$$

inside $\overline K_{\lambda_0}(T)$. The left side belongs to $K(T)$, and the embedding
$K\hookrightarrow\overline K_{\lambda_0}$ is injective. Hence the rational function already
equals a polynomial in $K[T]$. Define

$$
P_p(X)=X^2-a_pX+p.
\tag{8.7}
$$

The polynomial that occurs as a characteristic series is instead

$$
P_p^*(T):=1-a_pT+pT^2=T^2P_p(T^{-1}).
\tag{8.7a}
$$

For every $\lambda$, equations (8.5)--(8.6) give

$$
D_{\operatorname{Frob}_p}(\mathcal R_\lambda;T)
=1-\iota_\lambda(a_p)T+pT^2.
\tag{8.8}
$$

Thus the Frobenius polynomials are independent of $\lambda$ and are determined by automorphic
data over elementary fixed fields. The proof of polynomiality is algebraic cancellation inside
$K(T)$, witnessed by the distinguished member. It is not a construction of kernels or
cokernels between $R_\lambda^+$ and $R_\lambda^-$.

### 8.4 Coefficient conjugation

Let $\sigma:K\hookrightarrow\mathbf C$. Applying $\sigma$ to (8.4) replaces
$\pi_{H_i}$ by $\pi_{H_i}^\sigma$ and $\theta_i$ by $\theta_i^\sigma$. Therefore

$$
D_{p,\mathfrak B^\sigma}(T)=\sigma(D_{p,\mathfrak B}(T)),
\qquad
P_p^\sigma(X)=X^2-\sigma(a_p)X+p.
\tag{8.9}
$$

If $\gamma\in\Gamma$ conjugates the field datum instead, places $w$ are permuted, residue
degrees and norms are unchanged, and (3.2) identifies each induced summand. Hence
$D_{p,\mathfrak B}$ is unchanged. This cleanly separates coefficient conjugation from field
conjugation.

### 8.5 Purity of the polynomial record

Book 186 records purity of weight one for every packet in the elementary family. We now check
that the base-field polynomial inherits it, without treating the virtual class as effective.
Let $\alpha_p,\beta_p$ be the roots of $P_p$. Choose a place $w$ of $M$ above $p$ of residue
degree $f$. At the distinguished member, restriction from $G_{\mathbf Q_p}$ to $G_{M_w}$ sends
the eigenvalues of arithmetic Frobenius to

$$
\alpha_p^f,\qquad\beta_p^f.
\tag{8.10}
$$

The top packet has parallel weight two, so every complex embedding satisfies

$$
|\iota(\alpha_p^f)|=|\iota(\beta_p^f)|=(p^f)^{1/2}.
\tag{8.11}
$$

Taking positive real $f$th roots gives

$$
|\iota(\alpha_p)|=|\iota(\beta_p)|=p^{1/2}.
\tag{8.12}
$$

For a coefficient conjugate $\sigma(P_p)$, repeat the argument with the conjugate packet
$\pi_M^\sigma$, whose purity is part of the same weight-two realization theorem. Hence every
coefficient conjugate of $P_p$ is pure of weight one.

Purity is a property of the common polynomial record. It still does not prove that
$\mathcal R_\lambda$ is an actual representation: absolute values of roots say nothing about
the signs of irreducible multiplicities in a virtual character.

### 8.6 Cubic splitting patterns in an induced Euler factor

Let $F/\mathbf Q$ be a non-Galois cubic subfield of an $S_3$-extension, and let
$r:G_F\to\operatorname{GL}_2(K_\lambda)$ be unramified above $p$. Write

$$
Q_w^\ast(T)=1-a_wT+Nw\,T^2
\tag{8.13}
$$

for its arithmetic local factor, suppressing a finite-order twist to keep the notation short.
The three splitting patterns of Section 3.6 give three different degree-six induced factors.

If $p$ splits completely, say $p=w_1w_2w_3$, then

$$
D_p(T)=Q_{w_1}^\ast(T)Q_{w_2}^\ast(T)Q_{w_3}^\ast(T).
\tag{8.14}
$$

All Frobenius blocks have length one. If the splitting pattern is $(1,2)$, write $w_1$ for the
degree-one place and $w_2$ for the degree-two place. Then

$$
D_p(T)
=Q_{w_1}^\ast(T)
\left(1-a_{w_2}T^2+p^2T^4\right).
\tag{8.15}
$$

The second factor is not $Q_{w_2}^\ast(T)$: local induction replaces its variable by $T^2$.
Finally, at an inert prime of residue degree three,

$$
D_p(T)=1-a_wT^3+p^3T^6.
\tag{8.16}
$$

The coefficients of $T$ and $T^2$ vanish because arithmetic Frobenius cyclically permutes
three coset blocks. Its cube acts inside one block as $\operatorname{Frob}_w$.

Return now to the $S_3$ Brauer relation (7.7). The cubic-field induction contributes one of the
degree-six polynomials (8.14)--(8.16). The quadratic-field twisted induction contributes a
degree-four polynomial in the denominator. At the distinguished coefficient place their
quotient is

$$
\frac{D_{p,F_2}(T)}{D_{p,F_3,\omega}(T)}
=1-a_pT+pT^2.
\tag{8.17}
$$

The degrees already match the virtual rank calculation $6-4=2$, but degree matching alone does
not prove the quotient polynomial. Equation (8.17) uses the tensor identity with $\rho$.
Afterward, injectivity of $K\hookrightarrow\overline K_{\lambda_0}$ proves it algebraically for
every coefficient embedding. This example separates the three logical steps: local block
calculation, virtual degree, and genuine polynomial cancellation.

With a twist $\theta$, replace $a_w$ in (8.13)--(8.16) by
$a_w\theta(\operatorname{Frob}_w)$ and $Nw$ by
$\theta(\operatorname{Frob}_w)^2Nw$. The residue-degree substitution remains unchanged.

### 8.7 The virtual L-function and its analytic boundary

Fix a Brauer datum and a finite set $S$ large enough for every term, as in Section 6.5. The
automorphic source defines the signed incomplete product

$$
\mathcal L_{\mathfrak B}^S(s)
=
\prod_i
L_{F_i}^{S_{F_i}}(\pi_{H_i}\otimes\psi_i,s)^{n_i}.
\tag{8.18}
$$

Each factor is the standard $L$-function of an actual cuspidal $\mathrm{GL}_2$ packet twisted
by a finite-order character. At a rational prime $p\notin S$, Artin formalism and (8.4) give

$$
\mathcal L_{\mathfrak B,p}(s)
=P_p^*(p^{-s})^{-1}
=\left(1-a_p\,p^{-s}+p^{1-2s}\right)^{-1}.
\tag{8.19}
$$

Thus (8.18) has the Euler product expected of the common degree-two polynomial record.

The signs $n_i$ matter analytically. If $n_i<0$, the corresponding entire automorphic
$L$-function occurs in the denominator. The resulting function is a priori meromorphic, and
zeros of a denominator can become poles. Polynomial cancellation of each good local factor
does not prove cancellation of global zeros. Nor does the Euler product alone identify
$\mathcal L_{\mathfrak B}^S$ with the $L$-function of an automorphic representation over
$\mathbf Q$.

Each completed packet $L$-function has a functional equation. Multiplying those equations with
exponents $n_i$ yields a formal functional equation for the signed product. Its archimedean
factor is the single $\Gamma_{\mathbf C}(s)$ of (10.10). The finite conductor and root number
are signed products of the individual conductors and epsilon factors:

$$
\mathcal N_{\mathfrak B}
=\prod_i\left(\lvert D_{F_i}\rvert^2
N_{F_i/\mathbf Q}(\mathfrak n_i)\right)^{n_i},
\qquad
\varepsilon_{\mathfrak B}
=\prod_i\varepsilon(\pi_{H_i}\otimes\psi_i)^{n_i}.
\tag{8.20}
$$

Here $D_{F_i}$ is the absolute discriminant and $\mathfrak n_i$ is the conductor of the
twisted rank-two packet; the square of the discriminant is the contribution of writing a
degree-two $F_i$-function as a function over $\mathbf Q$. These expressions are nonzero
rational or algebraic quantities, but negative exponents can
make $\mathcal N_{\mathfrak B}$ look fractional before cancellation. At the distinguished
member, local equality with $\rho$ identifies the virtual conductor data place by place. For a
general coefficient member, a genuine positive integral conductor belongs only to an actual
effective representation.

We therefore retain three levels of conclusion:

1. the good monic Frobenius polynomials are $P_p$, equivalently the Euler denominators are
   $P_p^*(p^{-s})$;
2. the signed automorphic product gives meromorphic continuation and a formal signed functional
   equation wherever the individual standard $L$-functions do; and
3. neither entireness nor base-field automorphy is claimed for the signed product.

This analytic boundary is parallel to the representation-theoretic one. Ratios of actual
automorphic objects provide powerful evidence and continuation, but a ratio is not itself an
automorphic representation.

### 8.8 Frobenius powers and trace recurrences

The common polynomial determines all residue-degree transforms without choosing its roots.
Write

$$
P_p(X)=X^2-a_pX+p
\tag{8.21}
$$

and let $A_{p,f}$ be the sum of the $f$th powers of its roots. Then

$$
A_{p,0}=2,\qquad A_{p,1}=a_p,\qquad
A_{p,f}=a_pA_{p,f-1}-pA_{p,f-2}.
\tag{8.22}
$$

The recurrence follows because each root $\alpha$ satisfies
$\alpha^2=a_p\alpha-p$. It proves inductively that $A_{p,f}\in K$ and commutes with every
coefficient embedding.

If $w$ is an unramified place of residue degree $f$ in a field to which the chosen
representation restricts, then

$$
\operatorname{tr}\rho(\operatorname{Frob}_w)=A_{p,f},
\qquad
\det\rho(\operatorname{Frob}_w)=p^f.
\tag{8.23}
$$

For an elementary inclusion $D\leq H$, take the downstairs place in $F_H$ and the upstairs
place in $F_D=M^D$. The same recurrence is exactly (6.4b)--(6.4c); comparison with the
$D$-packet at $\tau_0$ gives the algebraic identity (6.4d) used in Proposition 6.2. No
normality of $F_D/F_H$ enters this residue-degree calculation.

For example,

$$
A_{p,2}=a_p^2-2p,\qquad
A_{p,3}=a_p^3-3pa_p.
\tag{8.24}
$$

These are the quadratic and cubic base-change trace formulas. They explain why the trace at a
degree-two place is not $a_p$ and why the degree-three formula in a cyclic-block computation
contains $a_p^3-3pa_p$ when one starts downstairs.

Conversely, if one knows the packet polynomial at a place $w$ of degree $f$, it records the
$f$th powers of the downstairs roots. Recovering the roots themselves requires choosing an
$f$th root and is not canonical. The Brauer product avoids that inverse problem: it combines
the upstairs polynomials by induction and uses the distinguished downstairs representation to
identify the resulting quadratic polynomial.

Twisting by a finite-order value $\zeta_w$ replaces the roots at $w$ by
$\zeta_w\alpha^f$ and $\zeta_w\beta^f$. Thus its trace is $\zeta_wA_{p,f}$ and determinant is
$\zeta_w^2p^f$. This formula is compatible with (8.4) and makes the determinant-square in
Section 5.3 visible at every Frobenius element.

## 9. Lattices and integral bookkeeping

Characteristic-zero semisimplicity makes virtual subtraction easy; integral representation
theory does not. Stable lattices remember extensions, saturation, and finite-flat group schemes,
none of which is visible in a character. We therefore construct lattices for every actual
summand, record their formal $K_0$-difference, and state precisely where the Book-186 chosen
lattice enters independently of the Brauer relation.

### 9.1 Induced lattices

Fix $\lambda$ and let $\mathcal O_\lambda$ be a finite coefficient DVR containing all relevant
values. We first justify the stable-lattice assertion used throughout.

**Lemma 9.1 (stable lattice for compact image).** Let $C$ be a finite extension of
$\mathbf Q_q$, with valuation ring $\mathcal O_C$ and uniformizer $\varpi$. Every continuous
representation

$$
r:J\longrightarrow\operatorname{GL}_n(C)
\tag{9.1a}
$$

of a compact group $J$ admits a $J$-stable $\mathcal O_C$-lattice.

**Proof.** Begin with $L_0=\mathcal O_C^n$. The image $r(J)$ is compact. The valuations of all
matrix entries of $r(g)$ are therefore bounded below uniformly in $g$, so for some $m\ge0$,

$$
r(g)L_0\subseteq\varpi^{-m}L_0
\qquad(g\in J).
\tag{9.1b}
$$

Set

$$
L=\sum_{g\in J}r(g)L_0.
\tag{9.1c}
$$

Although the sum is indexed by an infinite group, it is an $\mathcal O_C$-submodule of the
finitely generated module $\varpi^{-m}L_0$. Since $\mathcal O_C$ is noetherian, $L$ is finitely
generated. It contains $L_0$, so it spans $C^n$ and is torsion free; over the DVR it is a free
lattice of rank $n$. Finally,

$$
r(h)L=\sum_{g\in J}r(hg)L_0=L
\qquad(h\in J),
\tag{9.1d}
$$

so it is stable. $\square$

Apply the lemma to each $r_{i,\lambda}$. After one finite coefficient enlargement, obtain a
stable lattice $L_{i,\lambda}$. The finite-order character $\theta_{i,\lambda}$ has the
rank-one lattice $\mathcal O_\lambda$ because all its values are units. Then

$$
\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(L_{i,\lambda}\otimes\mathcal O_\lambda(\theta_i))
\tag{9.1}
$$

is finite free of rank $2[\Gamma:H_i]$ and stable under $G_{\mathbf Q}$. Choosing coset
representatives displays it as a direct sum of copies of $L_{i,\lambda}$, so no denominator is
introduced by induction.

At the elementary-field level, the lattices supplied by Book 186 are compatible with
conjugation and, at $\lambda_0$, unique up to homothety because the residual representation is
absolutely irreducible. If $L'$ and $L$ are stable lattices, scale until
$L'\subset L$ but $L'\not\subset\varpi L$. The image of $L'$ in $L/\varpi L$ is a nonzero
stable subspace, hence all of $L/\varpi L$; Nakayama gives $L'=L$. This proves the claim.

At a general coefficient place, residual irreducibility may fail and uniqueness need not hold.
Lemma 9.1 gives existence, but two lattices can yield different nonsplit residual extensions
with the same semisimplification. Conjugation compatibility of packet polynomials therefore
does not canonically choose compatible lattices around an entire coefficient orbit. We choose
one lattice for each actual summand, and every claim independent of that choice is phrased
through characteristic zero, determinant lines, or residual semisimplification.

Induction introduces no new choice beyond coset representatives. Changing representatives
conjugates the block model by an integral permutation-and-action matrix, so the induced lattice
is canonically isomorphic. Changing the original $L_{i,\lambda}$ can still change the induced
residual extension; finite induction does not erase that dependence.

### 9.2 What a virtual lattice does and does not mean

Using $n_i^\pm$ as in (7.5), the induced lattices form two actual lattices
$\mathcal L_\lambda^+$ and $\mathcal L_\lambda^-$. Their formal difference defines a class in

$$
K_0(\mathcal O_\lambda[G_{\mathbf Q}])
\tag{9.2}
$$

in the exact category of finite free continuous modules. It supports additive invariants such as
rank and trace, and determinant-line invariants such as (7.4).

There is, however, no canonical map
$\mathcal L_\lambda^-\to\mathcal L_\lambda^+$. Consequently there is no canonical quotient
lattice of rank two, no canonical residual representation obtained by subtracting reductions,
and no right to impose a finite-flat condition on such a quotient. The notation
$\mathcal L_\lambda^+-\mathcal L_\lambda^-$ is bookkeeping, not linear algebra on a literal
negative module.

### 9.3 The distinguished integral cancellation

At $\lambda_0$, characteristic-zero cancellation gives $[\rho]$ by (7.3). The chosen lattice
$L_\rho$ remains an independent part of the input. The Brauer equality does not construct it;
Book 186 already identifies its restrictions with the selected lattices of the $\pi_H$.

Thus the correct integral statement is

$$
\mathcal R_{\lambda_0}=[L_\rho\otimes_{\mathcal O}E]
\quad\text{in characteristic zero},
\tag{9.3}
$$

together with the separately supplied integral facts that every finite quotient of $L_\rho$ is
finite flat at $\ell$ and that $L_\rho$ has the primitive tame type at $2$. It would be false
bookkeeping to claim an isomorphism
$\mathcal L_{\lambda_0}^+\simeq L_\rho\oplus\mathcal L_{\lambda_0}^-$ over the integral group
ring merely from equality of characteristic-zero characters.

This warning is especially sharp when the residue characteristic divides $|\Gamma|$. The
semisimplicity used for characteristic-zero finite-group characters then disappears after
reduction: an integral Brauer relation can acquire extensions, torsion kernels, and failures of
saturatedness. Equality in the characteristic-zero representation ring therefore gives no
integral lattice equality at such a prime. Even when the residue characteristic does not divide
$|\Gamma|$, it gives at most an existence statement after choosing semisimple constituents, not
the canonical finite-flat lattice required by the arithmetic application.

### 9.4 Reduction and its boundary

Every individual induced lattice can be reduced modulo $\lambda$, and its semisimplified trace
at good primes is the reduction of the corresponding automorphic trace. The formal difference
therefore has a well-defined class in a modular Grothendieck group. But reduction can merge
irreducibles, erase prime-power roots of unity, and change conductor. More importantly,
nonnegativity in characteristic zero would still not provide a preferred integral lattice.

Accordingly, this book makes no rank-two residual representation from $\mathcal R_\lambda$ for
general $\lambda$. Any later use requiring a finite-flat rank-two quotient must first prove that
the characteristic-zero virtual class is effective and then choose and control an actual stable
lattice.

### 9.5 A characteristic-three lattice warning

The $S_3$ relation gives a small integral model of the obstruction. Work over a DVR
$\mathcal O$ containing a primitive cube root $\zeta_3$, and let the residue characteristic be
$3$. In characteristic zero,

$$
1_{S_3}\oplus
\operatorname{Ind}_{C_3}^{S_3}\omega
\simeq
\operatorname{Ind}_{C_2}^{S_3}1,
\tag{9.5}
$$

because this is the rearranged character identity (4.17). The right side has the permutation
lattice $\mathcal O[S_3/C_2]$ of rank three. The left side has the direct sum of a trivial line
and the induced cyclotomic lattice.

Modulo the prime above $3$, $\zeta_3\equiv1$, so $\omega$ reduces to the trivial character of
$C_3$. In the modular Grothendieck group, both reductions have composition factors

$$
1,\quad1,\quad\operatorname{sgn}.
\tag{9.6}
$$

Nevertheless the reduced lattices need not be isomorphic. The permutation module
$k[S_3/C_2]\simeq k^3$ has augmentation map

$$
(x_1,x_2,x_3)\longmapsto x_1+x_2+x_3.
\tag{9.7}
$$

In characteristic three the invariant vector $(1,1,1)$ lies in the augmentation kernel. This
produces a nontrivial filtration and witnesses the failure of semisimplicity. By contrast, the
formal left side of (9.5) presents its trivial line separately. Equality of characteristic-zero
characters has controlled the semisimplified composition factors, not the extension class of
the reduced permutation lattice.

This phenomenon is exactly what can happen when the residue characteristic divides
$|\Gamma|$. A change of stable lattice can alter the residual extension while leaving the
characteristic-zero representation fixed. Saturated inclusions cannot be read from the
Grothendieck class. Thus even if one eventually proves that the virtual characteristic-zero
class is effective, a separate integral argument is still required to obtain the lattice with
the desired finite-flat quotients.

### 9.6 Determinant lattices and dual lines

Determinants behave better integrally because they require no quotient between positive and
negative lattices. For a free stable lattice $L$ of rank $d$, the top exterior power
$\bigwedge^dL$ is a stable rank-one lattice. If
$\mathcal L^+-\mathcal L^-$ is a virtual lattice, define its determinant line by

$$
\det(\mathcal L^+-\mathcal L^-)
=\bigwedge^{d_+}\mathcal L^+
\otimes
\left(\bigwedge^{d_-}\mathcal L^-\right)^\vee.
\tag{9.8}
$$

This is an actual free rank-one module with continuous action. Changing either lattice within
its homothety class rescales the displayed generator but not the character. Therefore the
cyclotomic identity (7.4) has a genuine integral determinant line after a finite coefficient
enlargement.

What is not canonical is a trivialization of all transfer factors at once. The one-dimensional
Brauer relation gives an isomorphism of characteristic-zero determinant characters, but chosen
integral models can differ by fractional ideals. Over a DVR every fractional ideal is free of
rank one, so this discrepancy disappears after choosing a basis; the choice is not compatible
with a nonexistent rank-two quotient lattice.

Duality also respects induction. If $H$ is open in a profinite group $G$, then

$$
\left(\operatorname{Ind}_H^GL\right)^\vee
\simeq\operatorname{Ind}_H^G(L^\vee)
\tag{9.9}
$$

after inserting the natural coset pairing. In the finite-index setting induction and
coinduction coincide: pair functions supported on the same coset and sum their $H$-pairings.
This gives a perfect $G$-equivariant pairing on the induced lattice whenever $L$ has one.

For the Book-186 distinguished member, the alternating pairing on $L_\rho$ identifies its
determinant lattice with the cyclotomic line. Equation (9.8) recovers the same line from the
Brauer summands, but it does not recover the alternating rank-two pairing itself. Pairing,
finite-flat quotients, and the primitive dyadic type remain attached to the named lattice
$L_\rho$.

## 10. Local types through the Brauer construction

Good Frobenius polynomials do not determine bad local behavior without a separate recognition
theorem. The controlled top field already carries exact dyadic and coefficient-prime records,
and local Mackey decomposition transports them to the virtual family. This chapter keeps
inertia, monodromy, determinants, and finite-flat structures separate, because formal
subtraction interacts differently with each.

Proposition 6.2 is the limited recognition case: it first identifies two already existing
global semisimple representations, so their local restrictions are then isomorphic. It does not
create a bad-place record for the signed virtual base-field class.

### 10.1 Restriction of Weil--Deligne data

For a finite place $v$ of $\mathbf Q$, equation (3.7) gives the local virtual class

$$
\mathcal R_\lambda|_{G_{\mathbf Q_v}}
=\sum_i n_i\sum_{w\mid v}
\left[
\operatorname{Ind}_{G_{(F_i)_w}}^{G_{\mathbf Q_v}}
(r_{i,\lambda}|_{G_{(F_i)_w}}\otimes\theta_i)
\right].
\tag{10.1}
$$

Away from the coefficient residue characteristic, the Weil--Deligne functor commutes with
restriction, finite direct sums, finite-image twists, and finite induction. Hence (10.1) records
inertia and monodromy without reconstructing them from Frobenius traces. Negative coefficients
again mean that this is a virtual Weil--Deligne object.

The local Mackey intersections behind (10.1) have the form
$D_v\cap\gamma H_i\gamma^{-1}$ and need not be elementary. Proposition 6.2 is not applied to
those subgroups, and no packet indexed by them is presumed. When the global restriction target
is another elementary fixed field $F_J$, the relevant intersections are instead the elementary
groups $J\cap\gamma H_i\gamma^{-1}$, one for every double coset; equations
(3.15a)--(3.15c) and (6.4e)--(6.4g) then identify the existing overlap packet before its actual
local restrictions are taken. This separates the two occurrences of Mackey without dropping or
merging any double-coset term.

The induction in (10.1) is induction of Weil representations, not parabolic induction of
representations of $\mathrm{GL}_2$. If $(r,N)$ is a local Weil--Deligne representation over
$(F_i)_w$, the induced object has representation
$\operatorname{Ind}_{W_{(F_i)_w}}^{W_{\mathbf Q_v}}r$ and monodromy obtained by placing the
conjugates of $N$ on the corresponding coset summands. Consequently:

- $N=0$ in every summand if and only if the induced $N$ is zero;
- an unramified summand induced through an unramified extension is unramified;
- a ramified extension can give nontrivial permutation inertia even when $r$ itself is
  unramified; and
- an unramified twist changes Frobenius but not inertia or monodromy.

Conductors must therefore be computed summand by summand. A conductor is not obtained by
formally subtracting nonnegative integers and then declaring the result to be the conductor of
a rank-two representation. At a good place all conductors vanish and the polynomial formula is
enough; at a bad place the full virtual Weil--Deligne record is the invariant we retain.

At a place where $M/\mathbf Q$ is unramified, every $\theta_i$ is unramified on inertia because
it factors through $M/F_i$. Twisting changes only Frobenius eigenvalues. At a place ramified in
$M$, the characters may contribute finite inertial type, which is why all such rational primes
belong to the common exceptional set.

### 10.2 The dyadic tame type

Book 186 arranges that $2$ split completely in $M$. Every decomposition group in $\Gamma$ at
$2$ is therefore trivial. It follows that the quotient characters $\theta_i$ are trivial on
each local Galois group above $2$, and every completion $(F_i)_w$ is $\mathbf Q_2$. Thus each
local summand carries the same two-dimensional type as the corresponding packet:

$$
N=0,
\qquad I_2^{\mathrm{wild}}=1,
\qquad T^2+T+1=0.
\tag{10.2}
$$

At $\lambda_0$ the Brauer expression equals $\rho$, so (10.2) is the actual local type of the
chosen member. For a general $\lambda$, (10.1) is only a signed sum of copies of compatible
local types; one may not infer an actual two-dimensional inertial representation from it.

There is also no hidden twist at $2$. Since the decomposition group of every chosen place of
$M$ above $2$ is trivial, its intersection with every $H_i$ is trivial. The local quotient
$G_{(F_i)_w}\to H_i$ is therefore trivial, so

$$
\theta_i|_{G_{(F_i)_w}}=1.
\tag{10.2a}
$$

The number of places $w$ above $2$ still depends on $[\,\Gamma:H_i\,]$, but Mackey simply
produces that many transported copies. The signed rank identity (5.7) reduces their virtual
total to rank two at the distinguished member.

### 10.3 Coefficient-prime finite-flat data

At the original coefficient prime $\ell$, the completions of $M$ were chosen unramified and the
finite-flat component was fixed before specialization. Because every $\theta_i$ factors through
the unramified extension $M/F_i$, it is unramified at places above $\ell$. Restriction and
unramified twisting preserve inertia, Hodge--Tate weights, crystallinity, and finite-flatness of
each individual packet lattice: the twisting lattice is finite etale. They can nevertheless
change Frobenius eigenvalues and multiply the determinant by $\theta_i^2$. Therefore a twisted
summand need not remain on the same labeled **fixed-determinant** component. The untwisted
packet has the Book-186 component label; the twisted packet has its unramified translate, and
the determinant-line calculation of Section 7.3 reassembles the total cyclotomic determinant
only virtually.

The actual chosen lattice $L_\rho$ therefore retains its coefficient-linear finite locally free
quotient system after the Brauer identity is applied. This conclusion comes from the equality
with the pre-existing member and the Book-186 lattice comparison, not from closure of
finite-flat group schemes under formal subtraction.

The determinant distinction can be seen on one summand. Before twisting,

$$
\det r_{i,\lambda_0}=\chi_\ell|_{G_{F_i}}.
\tag{10.3}
$$

After twisting it is

$$
\det(r_{i,\lambda_0}\otimes\theta_i)
=\chi_\ell|_{G_{F_i}}\theta_i^2.
\tag{10.4}
$$

The latter is still crystalline of weights $\{0,1\}$ at an unramified place above $\ell$, but
it is not the fixed cyclotomic determinant unless $\theta_i^2=1$ locally. Only after induction
and signed multiplication do (5.5)--(5.7) cancel all $\theta_i^2$ and recover the determinant
line $\chi_\ell$.

For a different coefficient place $\lambda\mid q$, each packet has its usual weight-two local
realization at places above $q$. If $q$ ramifies in $M$, quotient characters can be ramified and
local induction need not preserve a clean crystalline or finite-flat type. The virtual family
records the actual local types of its summands and makes no uniform clean-type assertion at
such a $q$.

### 10.4 Auxiliary ramification and the common bad set

Choose a fixed finite set $S_0$ to contain:

- $2$ and the distinguished coefficient prime $\ell$;
- every rational prime ramified in $M$;
- every prime below a ramified local component of one of the finitely many $\pi_{H_i}$;
- every prime needed for the finite type and coefficient ledgers.

For a particular $\lambda$, put $S_\lambda=S_0\cup\{q_\lambda\}$, where $q_\lambda$ is its
residue characteristic. Outside $S_\lambda$, all extensions, packet realizations, and quotient
characters in (10.1) are unramified, so Chapter 8 applies. At primes in $S_\lambda$, one retains
the full individual local parameters and their Mackey sum. Enlarging $S_0$ is harmless.
Shrinking it without checking every summand is not.

The distinguished member is much cleaner than a general presentation: the auxiliary
ramification introduced by $M$ and the $\theta_i$ cancels in characteristic zero because it is
literally $\rho$, which is unramified outside $\{2,\ell\}$. That cancellation cannot be promoted
to an integral or effective cancellation at other coefficient places in this book.

### 10.5 Archimedean parameters and gamma factors

The infinite places are not part of the finite exceptional set and should not be hidden inside
the phrase “parallel weight two.” Every field $F_H$ is totally real because it is a subfield of
the totally real field $M$. If $v$ is a real place of $F_H$ and $\widetilde v$ is an extension
to $M$, then

$$
(F_H)_v=M_{\widetilde v}=\mathbf R.
\tag{10.5}
$$

Thus the local extension at infinity is trivial. Equivalently, the decomposition group of
$\widetilde v$ in $\operatorname{Gal}(M/F_H)=H$ is trivial. It follows that every quotient
character used in the Brauer relation satisfies

$$
\theta_i|_{G_{(F_i)_v}}=1,
\qquad
\psi_{i,v}=1.
\tag{10.6}
$$

There is no sign character hidden in the finite-order twist.

The archimedean component of $\pi_{H}$ is the discrete series of weight two at every real
embedding. In Weil-parameter language it is the two-dimensional parameter

$$
\operatorname{Ind}_{W_{\mathbf C}}^{W_{\mathbf R}}
\left(z\longmapsto z/|z|\right)
\tag{10.7}
$$

after the standard weight-two normalization. On the Galois side, complex conjugation has
eigenvalues $1$ and $-1$, so the determinant is $-1$, matching the cyclotomic determinant.
Coefficient conjugation does not change these integer weights or the two eigenvalues.

Now apply profinite Mackey at the real decomposition group. Since every real completion of
$F_i$ is $\mathbf R$, restriction of the induced summand to $G_{\mathbf R}$ is the direct sum
of $[F_i:\mathbf Q]=[\Gamma:H_i]$ copies of the same odd two-dimensional block. Therefore the
archimedean virtual class is

$$
\sum_i n_i[\Gamma:H_i]\,[1\oplus\operatorname{sgn}]
=[1\oplus\operatorname{sgn}]
\tag{10.8}
$$

by (5.7). This particular local virtual class is effective for a simple reason: every summand
has the same real parameter. It does not imply global effectivity, where the finite-prime and
global irreducible constituents are not identical term by term.

In the arithmetic, weight-one normalization of the Euler factors used in Chapter 8, define

$$
\Gamma_{\mathbf C}(s)=2(2\pi)^{-s}\Gamma(s).
\tag{10.9}
$$

The standard archimedean factor of a parallel-weight-two packet over $F_i$ is
$\Gamma_{\mathbf C}(s)^{[F_i:\mathbf Q]}$. Hence the signed gamma-factor identity is

$$
\prod_i
L_\infty(\pi_{H_i}\otimes\psi_i,s)^{n_i}
=
\Gamma_{\mathbf C}(s)^{\sum_i n_i[\Gamma:H_i]}
=\Gamma_{\mathbf C}(s).
\tag{10.10}
$$

If one uses the unitary normalization, every argument is shifted uniformly by $1/2$; the
exponent identity is unchanged. Formula (10.10), like the finite Euler identity, is a virtual
factor identity. It supplies the correct degree-two archimedean factor but does not supply a
global automorphic representation over $\mathbf Q$.

### 10.6 Conductors under local induction

The conductor ledger is most transparent for one finite separable extension of nonarchimedean
local fields $L/K$. Normalize $v_K$ by $v_K(\varpi_K)=1$ and define

$$
d(L/K):=v_K\!\left(N_{L/K}\mathfrak D_{L/K}\right)
\quad\text{so that}\quad
N_{L/K}(\mathfrak D_{L/K})=\mathfrak p_K^{d(L/K)},
\tag{10.10a}
$$

where $\mathfrak D_{L/K}$ denotes the different ideal in $\mathcal O_L$; its norm is the
discriminant ideal in $\mathcal O_K$. Thus $d(L/K)$ is the exponent of the discriminant ideal
in $K$, not the exponent of the different measured by $v_L$. Let $f(L/K)$ be the residue degree,
and let $r$ be a finite-dimensional Weil representation of $W_L$ with finite inertial image.
The induction formula for Artin conductors is

$$
a_K(\operatorname{Ind}_{W_L}^{W_K}r)
=
\dim(r)\,d(L/K)+f(L/K)a_L(r).
\tag{10.11}
$$

Here $a_L(r)$ uses the valuation and ramification filtration normalized over $L$. We prove the
formula, including both normalization factors.

First suppose that $r$ has finite image. Choose a finite Galois extension $E/K$ containing $L$
through which $r$ factors, and put $G=\operatorname{Gal}(E/K)$ and
$H=\operatorname{Gal}(E/L)$. Thus $r$ is genuinely an $H$-representation in the calculation
below. Enlarging $E$ does not change any conductor. For $g\ne1$, set

$$
i_E(g)=\min_{x\in\mathcal O_E}v_E(gx-x).
\tag{10.11a}
$$

The Artin character for $E/K$ is the class function

$$
\mathfrak a_{E/K}(g)=-f(E/K)i_E(g)\quad(g\ne1),
\qquad
\mathfrak a_{E/K}(1)=f(E/K)\sum_{g\ne1}i_E(g).
\tag{10.11b}
$$

Its pairing with the inertial character of a representation is exactly the tame
codimension-plus-Swan definition of its Artin conductor: grouping the elements with
$i_E(g)\ge j+1$ recovers the lower ramification-group sum. Thus
$a_K(V)=\langle\mathfrak a_{E/K},\chi_V\rangle_G$. This also shows directly that an
unramified change in Frobenius does not affect the conductor.

We need the restriction identity

$$
\operatorname{Res}_H^G\mathfrak a_{E/K}
=f(L/K)\mathfrak a_{E/L}+d(L/K)\operatorname{Reg}_H.
\tag{10.11c}
$$

For $h\ne1$, the two sides agree because
$f(E/K)=f(L/K)f(E/L)$ and the regular character vanishes away from $1$. At the identity, the
difference between the first two terms is

$$
f(E/K)\sum_{g\in G\setminus H}i_E(g).
\tag{10.11d}
$$

To identify it, the different formula gives

$$
v_E(\mathfrak D_{E/K})=\sum_{g\ne1}i_E(g),
\qquad
v_E(\mathfrak D_{E/L})=\sum_{h\ne1}i_E(h).
\tag{10.11e}
$$

Transitivity of the different subtracts these equations, so
$\sum_{g\notin H}i_E(g)=e(E/L)v_L(\mathfrak D_{L/K})$. Taking the norm from $L$ to $K$ says
$d(L/K)=f(L/K)v_L(\mathfrak D_{L/K})$. Since
$|H|=e(E/L)f(E/L)$, expression (10.11d) is exactly $|H|d(L/K)$, the value at $1$ of
$d(L/K)\operatorname{Reg}_H$. This proves (10.11c).

Finally Frobenius reciprocity and (10.11c) give

$$
\begin{aligned}
a_K(\operatorname{Ind}_{W_L}^{W_K}r)
&=\langle\mathfrak a_{E/K},\operatorname{Ind}_H^G\chi_r\rangle_G\\
&=\langle\operatorname{Res}_H^G\mathfrak a_{E/K},\chi_r\rangle_H\\
&=f(L/K)a_L(r)+d(L/K)\dim r,
\end{aligned}
\tag{10.11f}
$$

because $\langle\operatorname{Reg}_H,\chi_r\rangle_H=\dim r$. This proves the formula for
finite-image $r$.

Now let only the inertial image of $r$ be finite. The ramification-group definition shows that
$a_L(r)$ depends solely on the finite representation $r|_{I_L}$. The same is true on the left:
Mackey restriction of $\operatorname{Ind}_{W_L}^{W_K}r$ to $I_K$ involves only restrictions of
$r$ to groups

$$
I_K\cap xW_Lx^{-1}\subseteq xI_Lx^{-1},
\tag{10.11g}
$$

so no value of $r$ on a Frobenius element enters its Artin conductor. One may therefore repeat
the preceding Artin-character pairing on a finite quotient killing $\ker(r|_{I_L})$; all terms
away from inertia have $i_E(g)=0$, while the identity term uses only $\dim r$. The restriction
identity (10.11c) and its pairing are unchanged. Thus (10.11f), and hence (10.11), hold for
every finite-inertia Weil representation. This is not an assertion that $r$ itself factors
through the finite Galois group: only the conductor calculation does.

The Weil representations attached to the controlled Book-186 packets have finite inertial
image and $N=0$, so (10.11) applies exactly as stated. For a general Weil--Deligne pair
$(r,N)$, (10.11) computes the Artin conductor of the Weil representation $r$; the
Weil--Deligne conductor has the additional monodromy correction
$\dim V^{I}-\dim(\ker N)^{I}$. Induction carries $N$ blockwise as described after (10.1), so
that correction can also be recorded term by term, but it vanishes in the controlled family
and no cancellation of nonzero monodromy is asserted here.

For our rank-two local summand, twisting first gives

$$
a_L(r_{i,\lambda}\otimes\theta_i).
\tag{10.12}
$$

There is no universal formula replacing (10.12) by the maximum of
$a_L(r_{i,\lambda})$ and $2a_L(\theta_i)$: characters on the last nontrivial inertia layer can
cancel. Once the twisted conductor is known from the actual local parameter, (10.11) gives the
induced conductor exactly.

If $L/K$ is unramified of residue degree $f$ and the twisted representation is unramified, both
terms on the right of (10.11) vanish. This is the setting of the good-prime polynomial
calculation. If $r$ is unramified but $L/K$ is ramified, then

$$
a_K(\operatorname{Ind}r)=2d(L/K),
\tag{10.13}
$$

so permutation inertia alone creates conductor. If $L/K$ is unramified but $\theta_i$ has
conductor $c$, then the result is $f\,a_L(r\otimes\theta_i)$; in particular, for an unramified
$r$ and a scalar character, it is $2fc$.

For a rational place $v$ and a global induction from $F_i$, local Mackey gives one term for
each $w\mid v$, so the conductor exponent of the actual induced summand is the sum of the
quantities (10.11) over those $w$. The Brauer expression then forms the signed integer

$$
\sum_i n_i\sum_{w\mid v}
a_{\mathbf Q_v}\left(
\operatorname{Ind}_{(F_i)_w/\mathbf Q_v}
(r_{i,\lambda,w}\otimes\theta_{i,w})\right).
\tag{10.14}
$$

This is useful bookkeeping and agrees with the conductor of $\rho$ at the distinguished member,
where actual cancellation is known. The Artin conductor is additive under direct sums, so
(10.14) is a well-defined virtual integer. For a general $\lambda$, however, it can have no
interpretation as the nonnegative conductor of an actual rank-two representation until
effectivity is proved. We therefore retain both the signed integer and the individual
nonnegative conductor profiles together with the full local parameters.

### 10.7 A type-by-type local ledger

It is useful to summarize exactly what each local operation preserves.

**Unramified type.** Suppose $(r,N)$ has $N=0$ and inertia acts trivially, and suppose both
$L/K$ and $\theta$ are unramified. Then
$\operatorname{Ind}_{W_L}^{W_K}(r\otimes\theta)$ is unramified. Frobenius acts by a cyclic
block, giving

$$
\det(1-\operatorname{Frob}_KT)
=\det(1-r(\operatorname{Frob}_L)\theta(\operatorname{Frob}_L)T^f).
\tag{10.15}
$$

If $L/K$ is ramified, this conclusion fails even when $r$ and $\theta$ are unramified:
inertia permutes embeddings of $L$ and produces the discriminant term in (10.11).

**Finite tame type.** Suppose $N=0$ and inertia has finite image of order prime to the residue
characteristic. Restriction to an unramified extension leaves the same inertia group, while a
finite-order scalar twist multiplies every inertial eigencharacter by the same character.
Consequently the ratio of two eigencharacters is unchanged, and distinct eigencharacters
remain distinct. One must nevertheless record the actual character pair, not merely the order
of the inertia image, because the common scalar factor itself is part of the local type. At $2$
the twists are trivial, so the two primitive order-three characters remain unchanged.

**Special or Steinberg type.** A special parameter has nonzero monodromy $N$ of rank one.
Finite-order twisting changes the Weil action but leaves $N$ nonzero. Restriction can split the
Weil representation but cannot turn a nonzero $N$ into zero, and induction places conjugates of
$N$ on every block. No special type occurs in the chosen Book-186 representation, whose
monodromy is zero everywhere, but this boundary explains why good traces alone could not be
used to assert that fact.

**Coefficient-prime type.** At a place above the residue characteristic of $\lambda$, a
Weil--Deligne parameter alone does not encode the integral finite-flat quotient system.
Unramified weight-zero twisting preserves Hodge--Tate weights and finite-flatness, but changes
Frobenius and determinant. A ramified finite-order twist can still have numerical
Hodge--Tate weight zero, yet fail to be crystalline or finite-flat and leave the named
fixed-determinant component. Hence Section 10.3 makes a clean assertion only for the
distinguished $\ell$-adic member and keeps general coefficient-prime data on the individual
packet lattices.

**Archimedean type.** At a real place, the quotient twist is trivial and every packet has the
same discrete-series parameter. This is the only bad-place category in which the virtual local
sum visibly collapses to one actual rank-two block at every coefficient embedding.

The ledger can be expressed compactly as

| Input operation | Inertia | Monodromy | Frobenius | Integral component |
|---|---|---|---|---|
| unramified twist | unchanged | unchanged | multiplied by a unit | unramified translate |
| ramified finite twist | multiplied characterwise | unchanged | changed | may change |
| unramified field restriction | unchanged subgroup | restricted | raised by residue degree | base-changed |
| elementary-overlap identification | same local isomorphism class after restriction | same where Weil--Deligne is defined | equal by (6.4d) at good places | homothetic named lattices only at $\tau_0$ |
| ramified field induction | permutation inertia added | conjugate blocks | cycle action | no formal rank-two lattice |
| real induction | repeated odd blocks | zero | not applicable | not an integral finite-place condition |

Every row applies to an actual summand. Taking the signed Brauer sum preserves trace,
determinant line, and virtual conductor, but only the distinguished member is known to package
those records into one actual local rank-two representation at all places.

## 11. The complete virtual automorphy package

All ingredients can now be assembled without changing their logical strength. The theorem below
is deliberately redundant: its clauses list rank, determinant, distinguished realization,
elementary-overlap compatibility, Frobenius compatibility, conjugation, local data, and lattice
limitations separately so that a later argument can cite exactly the interface it needs without
silently importing effectivity.

### 11.1 Statement

We collect the construction in a form suitable for later use.

**Theorem 11.1 (Brauer package for the controlled elementary family).** Let $\rho$, $M$, and
$\{\pi_H\}$ be the controlled data of Book 186 recalled in Chapter 6. Fix any integral Brauer
datum $\mathfrak B$ for $\Gamma=\operatorname{Gal}(M/\mathbf Q)$ and a common Galois coefficient
field $K$ containing the data of every elementary packet in the controlled family. Then:

1. formula (1.6) defines, for every finite $\lambda$ of $K$, a continuous semisimple virtual
   Galois representation $\mathcal R_\lambda$ of rank two;
2. $\det\mathcal R_\lambda=\chi_\lambda$ as a determinant-line character;
3. the distinguished member is the actual chosen representation $\rho$;
4. for every $\lambda$, restriction to $G_M$ is the actual top realization
   $[r_{\pi_M,\lambda}]$;
5. for every pair of elementary subgroups $H,J$, every $x\in\Gamma$, and every coefficient
   embedding $\tau$, if $D=H\cap xJx^{-1}$ and $L=M^D$, then

   $$
   \left(r_{H,\tau}|_{G_L}\right)^{\mathrm{ss}}
   \simeq r_{D,\tau}
   \simeq
   \left({}^x r_{J,\tau}|_{G_L}\right)^{\mathrm{ss}},
   $$

   with the twisted and Hom-ready formulas (6.4f)--(6.4h) and the double-coset formula
   (3.15c); this uses no automorphic base change along the possibly non-Galois intersection
   extension;
6. for every good rational prime $p$, the virtual characteristic series is
   $\iota_\lambda(P_p^*(T))$ for $P_p^*(T)=1-a_pT+pT^2$ computed by (8.4), or equivalently the monic Frobenius
   characteristic polynomial is $P_p(X)=X^2-a_pX+p$;
7. conjugating a fixed field, packet, and Brauer character together does not change the induced
   class, while coefficient conjugation sends $a_p$ to its conjugate;
8. restriction at a finite place is the Mackey sum (10.1), so residue degrees, inertia,
   monodromy, and local twists are all retained;
9. at infinity the signed local class is one odd weight-two block and the signed gamma factor
   is $\Gamma_{\mathbf C}(s)$;
10. the dyadic and $\ell$-adic records of the distinguished member are exactly the primitive
   tame order-three and selected finite-flat records of Book 186; and
11. induced stable lattices give a virtual integral class, but the overlap comparison itself is
   only characteristic zero away from the distinguished member, and no actual rank-two lattice or
   residual representation is asserted for a general $\lambda$.

The automorphic input consists only of the actual twisted packets
$\pi_{H_i}\otimes\psi_i$ over elementary fixed fields. No nonsolvable automorphic induction and
no automorphic representation over $\mathbf Q$ are asserted.

### 11.2 Proof

Brauer induction supplies $\mathfrak B$ by Theorem 4.4. The field $F_i=M^{H_i}$ is totally real,
and $H_i$ is solvable, so Chapter 6 supplies the selected cuspidal packet $\pi_{H_i}$ and all its
conjugates. Section 5.1 supplies the matching finite-order twists over one coefficient field.

Finite Galois induction and additivity define $\mathcal R_\lambda$; equations (5.7) and (7.2)
give rank two. The determinant calculation is (5.8), yielding (7.4). At $\lambda_0$, the exact
restriction identity (6.4), the tensor identity, and the inflated Brauer relation give (7.3).
At every $\lambda$, profinite Mackey and base change to the top give (7.11).
Proposition 6.2 compares the algebraic residue-degree transforms at the distinguished embedding,
uses injectivity to obtain (6.4d) in $K[X]$, and applies Lemma 6.1 at every coefficient embedding.
This proves the elementary-overlap clause, including its conjugate and twisted forms, without a
transfer theorem over the intersection field.

At a good prime, local Mackey decomposition and the cyclic-block determinant calculation give
(8.4). Equality with $\rho$ at $\lambda_0$ proves that this rational expression is the
quadratic polynomial (8.6) over $K$, and injectivity of every coefficient embedding gives the
same polynomial at all $\lambda$. Equations (3.2), (5.2)--(5.3), and (8.9) prove the two kinds
of conjugation compatibility.

Formula (10.1) proves the all-place local assertion. Sections 10.2--10.3 apply the exact splitting
and unramified-completion clauses of the controlled field, while Chapter 9 supplies the lattice
statements and their limitations. Section 10.5 proves the real-parameter and gamma-factor
identity. These arguments establish every clause. $\square$

### 11.3 Independence at the virtual level

There are two different independence statements.

At the distinguished place, every Brauer datum gives $[\rho]$ by the tensor identity. Hence the
result is independent of the relation in the strongest possible characteristic-zero sense.
The good-prime polynomial $P_p$ is then also independent of the relation: every expression
(8.4) equals the same polynomial of $\rho$ in the embedded field, and therefore in a common
number-field overfield.

For a general $\lambda$, equality of the good-prime polynomials for two Brauer data gives
equality of virtual traces on a dense set of Frobenius elements. The comparison needed to pass
from that statement to virtual classes is now available in Lemma 6.1. Place both relations in
one Galois number-field overfield and, for a fixed $\lambda$, write

$$
\mathcal R_{\mathfrak B,\lambda}=[R^+]-[R^-],
\qquad
\mathcal R_{\mathfrak B',\lambda}=[S^+]-[S^-].
$$

At every prime good for both presentations, equality of the virtual Frobenius characteristic
series can be cross-multiplied as

$$
D_{\operatorname{Frob}_p}(R^+;T)
D_{\operatorname{Frob}_p}(S^-;T)
=
D_{\operatorname{Frob}_p}(R^-;T)
D_{\operatorname{Frob}_p}(S^+;T).
$$

The two sides are the characteristic series of the actual semisimple representations
$R^+\oplus S^-$ and $R^-\oplus S^+$. Their dimensions agree because both virtual ranks are
two. Lemma 6.1 therefore gives

$$
R^+\oplus S^-\simeq R^-\oplus S^+,
$$

and hence

$$
\mathcal R_{\mathfrak B,\lambda}
=\mathcal R_{\mathfrak B',\lambda}
$$

in the semisimple Grothendieck group. Thus both the algebraic polynomial record and the virtual
$\lambda$-adic class are independent of the chosen integral Brauer relation. The isomorphism
between the two enlarged positive presentations is noncanonical and carries no lattice data.

This boundary is important: polynomial compatibility and representation-theoretic effectivity
are separate questions. Brauer--Nesbitt recognizes a virtual class; it supplies no inequality
between its irreducible multiplicities.

### 11.4 Invariant-by-invariant verification

A useful way to audit Theorem 11.1 is to ask what kind of equality proves each invariant.

**Rank.** This uses only the value of the finite-group relation at the identity. Every packet
has rank two, finite induction multiplies rank by $[\Gamma:H_i]$, and (5.7) gives two. No
automorphic theorem enters.

**Determinant.** This is not the rank calculation repeated multiplicatively. It uses the
profinite transfer formula (5.4c), the square of the determinant twist, the determinant of the
one-dimensional Brauer relation, and the restriction--transfer identity. The conclusion is an
actual continuous cyclotomic line, even while the rank-two class remains virtual.

**Restriction to $M$.** Profinite Mackey and automorphic base change identify every coset
summand with a conjugate of $r_{\pi_M,\lambda}$. The quotient characters vanish on $G_M$.
Equation (5.7) then leaves one copy. This works for every $\lambda$ and is stronger than merely
matching good traces over $M$.

**Elementary overlaps.** For $D\leq H$, restriction to $G_M$ alone would forget a possible
character of $D=G_{M^D}/G_M$. At almost every place of $M^D$, the residue-degree transform of
the $H$-packet polynomial equals the $D$-packet polynomial at the distinguished embedding
because both are the polynomial of $\rho$. Injectivity makes this an equality in $K[X]$, and
Chebotarev--Brauer--Nesbitt gives (6.4a) at every embedding. For
$D=H\cap xJx^{-1}$, conjugation gives the second identification in (6.4e), while the two
quotient characters remain separately visible as $\alpha$, $\beta$, and
$\delta=\beta\alpha^{-1}$ in (6.4f)--(6.4h). This is done for every double coset, not only for
one representative field up to abstract isomorphism.

**The distinguished member.** Here one uses more: the packet over every $F_H$ is the exact
restriction of the already chosen $\rho$. The tensor identity applies before taking traces and
gives equality in the semisimple representation ring of $G_{\mathbf Q}$. Absolute
irreducibility identifies the effective representative with $\rho$.

**Good finite primes.** Local Mackey partitions primes, the cyclic-block determinant inserts the
residue-degree powers, and automorphic local--global compatibility identifies the block
polynomials. The result initially lies in $K(T)^\times$. Equality with $\rho$ at one completion
and injectivity of $K$ prove polynomiality in $K[T]$.

**Bad finite primes.** Each actual packet supplies a local Weil--Deligne or coefficient-prime
record; profinite Mackey induces and sums those records, without reconstructing the virtual
local ledger from good traces. For the separate overlap assertion, Lemma 6.1 first proves a
global semisimple isomorphism, whose restriction then identifies the actual local Galois and
Weil--Deligne representations. At $2$, splitting makes all twists trivial. At $\ell$,
unramified twisting preserves finite-flatness of summands but can move the fixed-determinant
component. The chosen lattice supplies the actual rank-two integral statement only at
$\lambda_0$; the overlap recognition at a general embedding supplies no integral model.

**Infinite places.** Total reality and trivial local quotient characters make every summand a
repeated weight-two discrete-series block. The rank relation collapses the virtual real
parameter and gamma factor to one copy. This local simplification has no global positivity
consequence.

**Coefficient conjugation.** All good polynomials, finite character values, centers, and local
types are placed in one number field. Applying an embedding acts coefficientwise. Field
conjugation instead permutes fixed fields and places. Their commuting actions give the
conjugate packet array of Section 5.7.

**Lattices.** Compactness gives a stable lattice for every summand; finite induction preserves
freeness and stability. Positive and negative sums therefore define a virtual integral class
and an actual determinant line. No map from the negative lattice to the positive lattice is
provided, so no rank-two quotient or residual representation is constructed.

This list also locates every imported theorem. Books 95--97 enter in characters, twists,
solvable transfer, and local parameter compatibility. Book 171 supplies the finite-quotient
Chebotarev density theorem used in Lemma 6.1; the Brauer--Nesbitt algebra argument is proved in
that lemma. Book 186 enters in the exact selected packets and the controlled field/local
ledgers. Every passage from those inputs to a signed base-field statement is proved in Chapters
2--10. There is no unlisted recognition or effectivity step.

For later use, the safest citation protocol is therefore invariant-specific. A good-prime
calculation should cite (8.4) and polynomiality, a top-field comparison should cite (7.11), an
elementary intersection-field comparison should cite Proposition 6.2 and (6.4e)--(6.4h), a
determinant calculation should cite (7.4), and an integral local claim about the chosen member
should cite Sections 9.3 and 10.2--10.3. Citing Theorem 11.1 without naming the relevant clause
must not be used to pass from a virtual class to an actual representation. The theorem packages
several compatible records; it does not conflate their different kinds of equality.

Similarly, Section 11.3 now makes a change of Brauer relation harmless for the entire virtual
$\lambda$-adic semisimple class, not only for the distinguished member and common polynomial
record. This remains a virtual equality and has no effectivity consequence. A change of
coefficient overfield is harmless by faithful scalar extension, while a change of stable
lattice is harmless only after semisimplification unless residual irreducibility gives
homothety uniqueness. These distinctions are part of the interface, not cautions external to
the theorem.

## 12. Failure modes, boundary, and conclusion

The last audit is mathematical rather than editorial. Each attractive shortcut below would turn
a signed family into a base-field compatible system without proving the missing positivity
statement. By isolating why those shortcuts fail, we locate the exact boundary of Brauer
induction and verify that no later theorem has entered the construction.

### 12.1 A virtual class is not an actual representation

Suppose $V$ and $W$ are nonisomorphic irreducible representations. The class
$[V]-[W]$ has a perfectly good trace, determinant line, and characteristic series, but its
coefficient of $W$ is negative. Adding a two-dimensional rank condition does not repair that
negative multiplicity. Likewise, writing $\mathcal R_\lambda=[R_\lambda^+]-[R_\lambda^-]$
does not produce an injection $R_\lambda^-\hookrightarrow R_\lambda^+$.

The usual words “cancel the common terms” are therefore justified only after actual common
irreducible constituents have been identified with sufficient multiplicity. No such positivity
calculation is part of the present construction.

There are three tempting substitutes, and none works. Virtual rank two records only the value
of the character at the identity. A cyclotomic determinant records only the top exterior-power
line. Agreement with an actual representation at one coefficient place uses the special
restriction identity (6.4), not a deformation argument that automatically propagates to all
coefficient places. These invariants are necessary consistency checks, but irreducible
multiplicities contain more information than all three together.

Nor can one choose a Brauer relation with nonnegative coefficients. Section 4.4 showed that a
nonnegative relation for $1_\Gamma$ would force a term induced from $\Gamma$ itself. When
$\Gamma$ is not elementary, that term is forbidden. Signed coefficients are the very device
that allows elementary fixed fields to see a nonsolvable group.

### 12.2 A polynomial is not effectivity

For every good $p$, the signed determinant expression is a quadratic polynomial. This is much
stronger than a mere rational Euler factor and is exactly what compatibility with the chosen
member provides. At one prime it remains an elementwise statement. Lemma 6.1 assembles the
almost-everywhere identities and thereby determines the virtual semisimple class, but that
recognition still records signed multiplicities rather than proving them nonnegative.

Consequently this book does not claim:

- an actual two-dimensional $\lambda$-adic representation for arbitrary $\lambda$;
- irreducibility or positivity of the signed character;
- a canonical stable rank-two lattice or finite-flat quotient system;
- an automorphic representation over $\mathbf Q$; or
- that Chebotarev--Brauer--Nesbitt recognition of the virtual class forces its multiplicities
  to be nonnegative.

Those remaining conclusions require effectivity and, for automorphy, a separate automorphic
recognition theorem. The present output is exactly the relation-independent semisimple virtual
family, its determinant line, its local Mackey records, its common algebraic Frobenius
polynomials, and the actual semisimple packet identifications over every elementary intersection
field. None of these statements makes the signed base-field class effective.

The distinction survives even when a density argument determines the virtual class uniquely.
For a virtual character

$$
\xi=\sum_jm_j\chi_j,
\qquad m_j\in\mathbf Z,
\tag{12.1}
$$

effectivity is the collection of inequalities $m_j\ge0$. Traces determine the integers $m_j$
only after pairing with every irreducible character:

$$
m_j=\frac1{|G|}\sum_{g\in G}\xi(g)\chi_j(g^{-1}).
\tag{12.2}
$$

Pointwise degree-two determinant identities do not visibly impose those inequalities. This is
why neither the finite-group inner-product calculation used to prove Brauer induction nor the
Brauer--Nesbitt recognition in Lemma 6.1 can be recycled as a positivity proof: the former
establishes integral spanning and the latter identifies semisimple multiplicities, but neither
changes their signs after arithmetic packets replace restrictions of one common representation.

The same warning applies to Euler products. The signed product

$$
\prod_iL_{F_i}(\pi_{H_i}\otimes\psi_i,s)^{n_i}
\tag{12.3}
$$

has good local denominators $P_p^*(p^{-s})$, equivalently monic Frobenius polynomials $P_p$,
by Chapter 8. A meromorphic or even entire
function with such factors is not, by that fact alone, the standard $L$-function of a cuspidal
representation over $\mathbf Q$. The construction is an automorphic *source* for the factors,
not a converse theorem.

### 12.3 Dependency audit

The finite-group arguments of Chapters 2--5 are proved here. Book 95 supplies finite-order
Hecke characters, their Galois avatars, twisting, coefficient fields, and stable rank-one
lattices. Book 96 supplies prime-cyclic base change and selected descent with its local,
central-character, and coefficient compatibilities. Book 97 supplies iteration through solvable
towers, tower independence after an extending representation selects the twists, and compatible
local restriction at every place.

Book 186 supplies the only potential-automorphy input: the chosen $\rho$, one controlled Galois
top $M$, automorphy over that top, elementary fixed-field packets, closure-level image
preservation, prescribed completions, coefficient fields, lattices, Frobenius data, purity, and
conjugation compatibility. This book neither reconstructs that geometry nor uses potential
automorphy over a new field.

Book 171, Theorem 4.3, supplies Chebotarev density in finite Galois quotients. Lemma 6.1 derives
the needed density statement for continuous class functions on $G_L$ and proves the
Brauer--Nesbitt step in-book. It is used only to compare already constructed semisimple
representations over one coefficient characteristic and, in Section 11.3, two actual
positive presentations of a virtual relation. It constructs no new representation.

The normalization audit is equally explicit. Finite-order Hecke characters use the arithmetic
reciprocity convention of Book 95. The geometric-Frobenius statement of solvable base change in
Books 96--97 is translated by (1.9) before comparison with the arithmetic Frobenius polynomials
of Book 186. Residue degree, not ramification index or global degree, controls the Frobenius
power. Twists act through the determinant, so centers and Galois determinants both acquire the
square of the character.

The field audit uses only the one top $M$ from Book 186. Fixed fields are obtained by Galois
correspondence, their completions by (6.1b), and their packets by the selected solvable descent
already proved there. No new Hilbert irreducibility, local approximation, modularity lifting,
or automorphic incidence argument is inserted. In particular, the nonsolvable extension
$M/\mathbf Q$ is crossed only by finite Galois induction and formal Euler data.

For an elementary inclusion $D\leq H$, the extension $M^D/F_H$ is not assumed Galois. Its
packet comparison is Proposition 6.2: ordinary restriction of an unramified Galois
representation raises Frobenius roots by the residue degree, the distinguished representation
makes that equality algebraic, and Lemma 6.1 recognizes the two existing representations over
$M^D$. Neither Book 96 nor Book 97 is invoked along this extension.

The coefficient audit distinguishes the algebraic field $K$, its completion $K_\lambda$, a
finite local field of definition $C_\lambda$, and the original $\ell$-adic coefficient field
$E$. Equalities are checked after embedding into finite common overfields and descend only when
injectivity or faithful scalar extension justifies it. Integral homothety, finite-flat quotient
systems, and labeled components are not descended from characteristic-zero character
equalities.

No theorem asserting positivity, effectivity, or construction of a base-field compatible system
is used. Chebotarev--Brauer--Nesbitt recognition is used in the sharply limited form proved in
Lemma 6.1, for representations that already exist. In particular, equality at the distinguished
place is proved directly from the pre-existing representation and the tensor identity; it is not
inferred from a later effectivity theorem.

The interface audit also rules out four quieter circularities. We never base change a packet
through the nonsolvable extension $M/\mathbf Q$; only the solvable upper extensions
$M/F_H$ occur. We never select a cyclic descent merely from invariance; the extending
representation fixes its twist. The overlap comparison uses good Frobenius traces to prove a
global semisimple isomorphism of two existing representations; only then are their local
restrictions identified. The independent algebraic bad-place labels still come from the
Book-186 local ledger and local Mackey formula. Finally, we never infer an integral lattice
equality from either a characteristic-zero Brauer relation or Brauer--Nesbitt, particularly at
primes dividing $|\Gamma|$.

### 12.4 Conclusion

Brauer induction resolves a mismatch of shapes. The available automorphy lies over fixed fields
of elementary subgroups, while the desired arithmetic object lives over the ground field and the
full Galois group is nonsolvable. The integral character relation replaces impossible direct
descent by a signed sum of finite inductions. Mackey theory then keeps that sum honest at every
completion and under every field conjugation.

The controlled construction of Book 186 is exactly what makes the formal relation arithmetic.
All elementary fixed fields lie in one Galois top; all packets descend from one top packet; one
extending representation selects every cyclic descent; coefficient fields and local labels are
shared; and the distinguished member turns a priori rational Euler expressions into one family
of algebraic quadratic Frobenius polynomials.

The same distinguished comparison supplies the full elementary-overlap interface. For every
Mackey subgroup $D=H\cap xJx^{-1}$ and every coefficient embedding, both restricted packet
realizations identify semisimply with $r_{\pi_D}$ over $M^D$, while the two quotient characters
and their ratio remain explicit. This is unconditional even when $M^D/F_H$ is non-Galois,
because it uses algebraic Frobenius comparison and Chebotarev--Brauer--Nesbitt rather than an
unavailable base-change theorem.

What emerges is a virtual rank-two family with cyclotomic determinant, exact recovery of the
chosen $\ell$-adic representation, compatible conjugate packets, controlled local records, and
integral summands. What does not yet emerge is an honest rank-two representation at every
coefficient place. Keeping that final distinction visible is the point of the construction:
Brauer induction has assembled all compatible arithmetic evidence, while leaving the genuinely
new positivity problem untouched.
