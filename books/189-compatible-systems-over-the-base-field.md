# Compatible Systems over the Base Field

## Contents

1. [From effective members to one arithmetic family](#1-from-effective-members-to-one-arithmetic-family)
   - [The last descent problem](#11-the-last-descent-problem)
   - [The repaired input](#12-the-repaired-input)
   - [The base-field theorem](#13-the-base-field-theorem)
   - [Conventions and boundaries](#14-conventions-and-boundaries)
   - [The order of construction](#15-the-order-of-construction)
2. [The intersection-field repair](#2-the-intersection-field-repair)
   - [Elementary groups are nilpotent](#21-elementary-groups-are-nilpotent)
   - [Subgroups admit prime-cyclic subnormal chains](#22-subgroups-admit-prime-cyclic-subnormal-chains)
   - [The fixed-field tower](#23-the-fixed-field-tower)
   - [Identification of the overlap packet](#24-identification-of-the-overlap-packet)
   - [The repaired export](#25-the-repaired-export)
3. [One algebraic coefficient ledger](#3-one-algebraic-coefficient-ledger)
   - [Intrinsic fields and fields of realization](#31-intrinsic-fields-and-fields-of-realization)
   - [Globalizing the distinguished completion](#32-globalizing-the-distinguished-completion)
   - [A common field for every elementary term](#33-a-common-field-for-every-elementary-term)
   - [Places rather than unnamed embeddings](#34-places-rather-than-unnamed-embeddings)
   - [The positive and negative representations](#35-the-positive-and-negative-representations)
4. [Multiplicity-one descent of an effective constituent](#4-multiplicity-one-descent-of-an-effective-constituent)
   - [The descent obstruction](#41-the-descent-obstruction)
   - [The multiplicity divisibility lemma](#42-the-multiplicity-divisibility-lemma)
   - [Descent from a signed equality](#43-descent-from-a-signed-equality)
   - [Why the Schur obstruction vanishes here](#44-why-the-schur-obstruction-vanishes-here)
   - [Descent of isomorphisms](#45-descent-of-isomorphisms)
5. [Construction at every coefficient place](#5-construction-at-every-coefficient-place)
   - [The effective constituent over a completion](#51-the-effective-constituent-over-a-completion)
   - [Continuity and absolute irreducibility](#52-continuity-and-absolute-irreducibility)
   - [Independence of the displaying embedding](#53-independence-of-the-displaying-embedding)
   - [Scalar extension](#54-scalar-extension)
   - [What coherence means](#55-what-coherence-means)
6. [Independence of Brauer decomposition](#6-independence-of-brauer-decomposition)
   - [Two relations in one ledger](#61-two-relations-in-one-ledger)
   - [Norm-zero comparison](#62-norm-zero-comparison)
   - [Independence over the completion](#63-independence-over-the-completion)
   - [Independence of presentation and conjugate terms](#64-independence-of-presentation-and-conjugate-terms)
   - [The intrinsic member](#65-the-intrinsic-member)
7. [Common Frobenius polynomials](#7-common-frobenius-polynomials)
   - [The algebraic polynomial](#71-the-algebraic-polynomial)
   - [Unramifiedness of the effective constituent](#72-unramifiedness-of-the-effective-constituent)
   - [Weak compatibility](#73-weak-compatibility)
   - [Removing auxiliary bad primes](#74-removing-auxiliary-bad-primes)
   - [Purity](#75-purity)
   - [Frobenius powers](#76-frobenius-powers)
8. [Determinant, duality, and the original member](#8-determinant-duality-and-the-original-member)
   - [The actual determinant](#81-the-actual-determinant)
   - [Duality](#82-duality)
   - [Identification at the distinguished place](#83-identification-at-the-distinguished-place)
   - [The original local records](#84-the-original-local-records)
9. [Strict local compatibility](#9-strict-local-compatibility)
   - [The algebraic local Mackey object](#91-the-algebraic-local-mackey-object)
   - [Krull--Schmidt cancellation](#92-krull--schmidt-cancellation)
   - [A common Weil--Deligne pair](#93-a-common-weil--deligne-pair)
   - [The dyadic type](#94-the-dyadic-type)
   - [The prime of the original lift](#95-the-prime-of-the-original-lift)
   - [Conductors and local factors](#96-conductors-and-local-factors)
10. [Coefficient covariance and family-level descent](#10-coefficient-covariance-and-family-level-descent)
    - [Coefficient conjugation](#101-coefficient-conjugation)
    - [Changing the common field](#102-changing-the-common-field)
    - [Descent data without chosen matrices](#103-descent-data-without-chosen-matrices)
    - [The global compatible family](#104-the-global-compatible-family)
11. [Stable lattices and the integral boundary](#11-stable-lattices-and-the-integral-boundary)
    - [Existence place by place](#111-existence-place-by-place)
    - [The distinguished lattice](#112-the-distinguished-lattice)
    - [Why characteristic-zero cancellation does not descend integrally](#113-why-characteristic-zero-cancellation-does-not-descend-integrally)
    - [Residual semisimplification](#114-residual-semisimplification)
    - [The exact boundary](#115-the-exact-boundary)
12. [The complete base-field compatible-system theorem](#12-the-complete-base-field-compatible-system-theorem)
    - [Statement](#121-statement)
    - [Proof](#122-proof)
    - [Dependency and interface audit](#123-dependency-and-interface-audit)
    - [Hostile failure audit](#124-hostile-failure-audit)
    - [Conclusion](#125-conclusion)

## 1. From effective members to one arithmetic family

### 1.1 The last descent problem

The preceding two books solve two different problems. Brauer induction first expresses the
desired ground-field object as a signed sum of actual induced representations coming from
elementary fixed fields. The character-norm argument then proves that, after placing the
coefficients in an algebraic closure of a nonarchimedean completion, that signed class is one
honest irreducible representation of dimension two.

This is not yet a compatible system. An algebraic closure contains many copies of the same
finite extension, and a representation whose isomorphism class is invariant under coefficient
automorphisms need not automatically have matrices over the smaller field. The obstruction is
the familiar Schur obstruction: an invariant absolutely irreducible representation can descend
only to a module over a division algebra. Moreover, even if every coefficient place separately
admits some finite field of definition, an arbitrary list of those fields is not one number
field indexed coherently by its finite places.

The last rational construction must therefore accomplish four things at once.

1. Put every elementary packet, every Brauer character, and every local type into one algebraic
   coefficient ledger.
2. Prove that the unique effective constituent descends from an algebraic closure to the
   corresponding completion of that one field.
3. Prove that changing a Brauer relation, an auxiliary splitting field, or an embedding used to
   display a completion does not change the descended member.
4. Assemble the common Frobenius polynomials and bad-place Weil--Deligne pairs into one weakly
   and strictly compatible family over the ground field.

The decisive new observation is that effectivity occurs with multiplicity exactly one inside a
difference of representations already defined over the completion. A nontrivial Schur index
would force that multiplicity to be divisible by an integer greater than one. Multiplicity one
therefore kills the coefficient descent obstruction.

### 1.2 The repaired input

Let

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(L_0)
\tag{1.1}
$$

be the chosen representation of Book 186, where $L_0/\mathbf Q_\ell$ is finite and
$\ell\ge 7$. It is absolutely irreducible,

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ is unramified outside }\{2,\ell\},
\tag{1.2}
$$

and it comes with its selected stable lattice. At $2$ it has trivial wild inertia, zero
monodromy, and primitive tame order-three type; at $\ell$ its lattice has the selected
coefficient-linear finite locally free quotient system.

Let $M/\mathbf Q$ be the controlled totally real Galois extension of Book 186 and put

$$
\Gamma=\operatorname{Gal}(M/\mathbf Q).
\tag{1.3}
$$

For every elementary subgroup $H\leq\Gamma$, write $F_H=M^H$. The repaired interface from
Books 187--188 supplies a selected parallel-weight-two cuspidal packet $\pi_H$ over $F_H$, all
of its coefficient realizations, and compatibility with conjugation and with restriction to
every elementary intersection field. More precisely, if $D\leq H$ is elementary, then

$$
r_{H,\lambda}|_{G_{F_D}}^{\mathrm{ss}}
\simeq r_{D,\lambda}
\tag{1.4}
$$

for every coefficient place after scalar extension to a common realization field. The same
statement holds after conjugating $H$ and $D$ inside $\Gamma$.

The draft preceding the repair stopped with equality only after restriction to $G_M$. That is
not enough for the character-norm proof: two extensions from $G_M$ to $G_{F_D}$ can differ by a
character of $D$. Chapter 2 proves independently that (1.4) follows from the elementary nature
of $H$ and the selected prime-cyclic descent. Thus the remainder of this book uses the intended
repaired export, not the weaker unrepaired sentence.

Fix an integral Brauer relation

$$
1_\Gamma=\sum_i n_i\operatorname{Ind}_{H_i}^{\Gamma}\theta_i,
\qquad n_i\in\mathbf Z,
\tag{1.5}
$$

with elementary $H_i$ and finite-order linear characters $\theta_i$. Books 187--188 then give,
at every coefficient embedding $\tau$, the effective absolutely irreducible representation

$$
r_{\mathfrak B,\tau}:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\Omega_\tau)
\tag{1.6}
$$

whose class is the signed induced Brauer class. They prove its determinant, common good
Frobenius polynomials, local Mackey record, recovery of $\rho$, and independence of the Brauer
relation after scalar extension. Our task is to descend and assemble those isomorphism classes.

### 1.3 The base-field theorem

The endpoint is best stated now, before the auxiliary coefficient field is chosen.

**Theorem 1.1 (compatible system over the base field).** There are a number field $E$, a place
$\lambda_0\mid\ell$ of $E$, a finite set $S=\{2,\ell\}$, and, for every finite place $\lambda$
of $E$, a continuous absolutely irreducible representation

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda)
\tag{1.7}
$$

with the following properties.

For every rational prime $p\notin S$ there is a polynomial

$$
P_p(X)=X^2-a_pX+p\in E[X]
\tag{1.8}
$$

such that, if $p$ differs from the residue characteristic of $\lambda$, then $r_\lambda$ is
unramified at $p$ and

$$
\det(X-r_\lambda(\operatorname{Frob}_p))=P_p(X).
\tag{1.9}
$$

Every root of every $P_p$ is a $p$-Weil number of weight one. For every finite $p$ there is a
Frobenius-semisimple rank-two Weil--Deligne representation $D_p$ over $E$, after one harmless
finite enlargement made once for the finitely many bad places, such that

$$
\operatorname{WD}_p(r_\lambda)^{\mathrm{F\!-\!ss}}
\simeq D_p\otimes_EE_\lambda
\tag{1.10}
$$

whenever $p$ differs from the residue characteristic of $\lambda$. At $p\notin S$, $D_p$ is
unramified with polynomial $P_p$. At $2$ it has zero monodromy, trivial wild inertia, and the
primitive tame order-three type.

For every $\lambda$,

$$
\det r_\lambda=\chi_\lambda,
\qquad
r_\lambda^\vee\simeq r_\lambda\otimes\chi_\lambda^{-1}.
\tag{1.11}
$$

After embedding $L_0$ and $E_{\lambda_0}$ into one finite extension of $\mathbf Q_\ell$,

$$
r_{\lambda_0}\simeq\rho.
\tag{1.12}
$$

The isomorphism class of every $r_\lambda$, every $P_p$, and every $D_p$ is independent of the
integral Brauer relation, of a positive-minus-negative presentation, of conjugating Brauer
terms, and of harmless coefficient enlargement. The family is covariant under coefficient
conjugation.

Each $r_\lambda$ admits a stable lattice. The theorem does not choose those lattices
compatibly, does not derive an integral cancellation from the Brauer relation, and does not
assert finite-flatness or a prescribed integral local structure for a new coefficient member.
At $\lambda_0$ the original selected lattice and all of its integral local properties are
retained unchanged.

### 1.4 Conventions and boundaries

Arithmetic Frobenius is used. Thus

$$
\chi_\lambda(\operatorname{Frob}_p)=p
\tag{1.13}
$$

when $p$ differs from the residue characteristic of $\lambda$, and the weight-two polynomial
is $X^2-a_pX+p$. If geometric Frobenius is desired, its eigenvalues are the inverses of the
displayed roots.

All global representations in the final family are semisimple and in fact absolutely
irreducible. At a finite place away from coefficient characteristic, $\operatorname{WD}$ means
the Frobenius-semisimple Weil--Deligne object: finite inertia and the monodromy operator are not
discarded. Strict compatibility makes no assertion at the varying coefficient prime.

Four levels of structure remain distinct throughout:

$$
\begin{array}{c}
\text{signed equality in a Grothendieck group}\cr
\Downarrow\ \text{character-norm effectivity}\cr
\text{one actual semisimple representation over an algebraic closure}\cr
\Downarrow\ \text{multiplicity-one coefficient descent}\cr
\text{one representation over a coefficient completion}\cr
\Downarrow\ \text{common polynomial and local data}\cr
\text{one compatible family of rational representations.}
\end{array}
\tag{1.14}
$$

No arrow in (1.14) is an integral arrow. Stable lattices form a fifth layer and are treated
only after the rational compatible family is complete.

### 1.5 The order of construction

We first close the repaired intersection-field interface. We then choose a common number field
large enough to realize every actual induced summand and to contain one globalization of the
distinguished $\ell$-adic completion. The signed expression is consequently defined over each
completion $E_\lambda$, even though its unique effective constituent is initially known only
over an algebraic closure.

Chapter 4 proves the descent lemma that removes this discrepancy. Chapters 5--6 construct the
members and prove all choice independence over $E_\lambda$, rather than merely after scalar
extension. Chapters 7--9 assemble the good and bad local data. Only then do we call the result
a compatible system. Lattices come last, because no characteristic-zero cancellation theorem
controls the saturation or reduction of a chosen integral summand.

## 2. The intersection-field repair

### 2.1 Elementary groups are nilpotent

For a prime $q$, a $q$-elementary group has the form

$$
H=C\times Q,
\tag{2.1}
$$

where $C$ is cyclic of order prime to $q$ and $Q$ is a $q$-group. Decompose $C$ into its Sylow
subgroups. Every Sylow subgroup of $H$ is then normal, and $H$ is their direct product. Hence
$H$ is finite nilpotent.

The relevant property of a finite nilpotent group is stronger than solvability.

**Lemma 2.1.** Every proper subgroup $D$ of a finite nilpotent group $H$ is properly contained
in its normalizer:

$$
D<N_H(D).
\tag{2.2}
$$

**Proof.** Write $H=\prod_qH_q$ as the direct product of its Sylow groups and put
$D_q=D\cap H_q$. Taking the primary components of each element shows
$D=\prod_qD_q$. If $D\ne H$, choose $q$ with $D_q\ne H_q$. It is enough to prove the claim in
the finite $q$-group $H_q$.

Let a finite $q$-group $P$ act by left multiplication on the cosets $P/D_q$. The fixed points
of the subgroup $D_q$ are the cosets $xD_q$ with $x\in N_P(D_q)$. Hence their number is
$[N_P(D_q):D_q]$. Orbit counting for the $D_q$-action gives

$$
[P:D_q]\equiv[N_P(D_q):D_q]\pmod q.
\tag{2.3}
$$

Since $D_q$ is proper, $[P:D_q]$ is divisible by $q$. The normalizer index in (2.3) is
therefore divisible by $q$ and cannot equal one. Choose an element of
$N_P(D_q)\setminus D_q$ and insert it in the $q$-factor of $H$; it normalizes every other
$D_{q'}$ because the Sylow factors commute. This proves (2.2). $\square$

### 2.2 Subgroups admit prime-cyclic subnormal chains

**Proposition 2.2 (prime-cyclic refinement).** If $D\leq H$ and $H$ is elementary, there is a
chain

$$
D=D_0\triangleleft D_1\triangleleft\cdots\triangleleft D_m=H
\tag{2.4}
$$

such that every quotient $D_{j+1}/D_j$ is cyclic of prime order.

**Proof.** Repeatedly replace a proper subgroup by its normalizer. Lemma 2.1 gives a strictly
increasing subnormal chain from $D$ to $H$. Each quotient in that chain is a finite nilpotent,
hence solvable, group. Refine one normal inclusion $A\triangleleft B$ by pulling back a
composition series of the solvable quotient $B/A$. Every composition factor of a finite
solvable group is cyclic of prime order. The inverse images remain normal in the next group,
so performing this refinement at every step gives (2.4). $\square$

The proposition is exactly stronger than the observation that an intersection subgroup need
not be normal in $H$. It need not be normal in one step; it is nevertheless subnormal through
prime-cyclic steps. That is all solvable base change requires.

### 2.3 The fixed-field tower

Reverse (2.4) under Galois correspondence. Since $F_J=M^J$, inclusions reverse and give

$$
F_H=F_{D_m}\subset F_{D_{m-1}}\subset\cdots\subset F_{D_0}=F_D.
\tag{2.5}
$$

Because $D_j\triangleleft D_{j+1}$,

$$
F_{D_j}/F_{D_{j+1}}
\tag{2.6}
$$

is cyclic Galois with group $D_{j+1}/D_j$, hence of prime degree. Thus the possibly non-Galois
extension $F_D/F_H$ is a composite of extensions lying one by one in the exact transfer range
of the prime-cyclic base-change theorem.

This also treats Mackey intersections. If

$$
D=H_i\cap xH_jx^{-1},
\tag{2.7}
$$

then $D$ is a subgroup of the elementary group $H_i$ and of the elementary group
$xH_jx^{-1}$. Proposition 2.2 gives a prime-cyclic tower from either fixed field to
$F_D=F_i\,xF_j$.

### 2.4 Identification of the overlap packet

**Theorem 2.3 (elementary overlap identity).** Let $D\leq H\leq\Gamma$ with $H$ elementary.
The iterated prime-cyclic base change of $\pi_H$ through (2.5) is the selected packet $\pi_D$.
Consequently, for every coefficient place $\lambda$,

$$
r_{H,\lambda}|_{G_{F_D}}^{\mathrm{ss}}
\simeq r_{D,\lambda}.
\tag{2.8}
$$

**Proof.** Apply prime-cyclic base change at every step of (2.5). Local parameter restriction
is transitive, so the endpoint $\Pi$ over $F_D$ base changes to $\pi_M$ and has the local
restrictions obtained from $\pi_H$.

At the distinguished coefficient place, Book 186 selected both packets by the same extending
representation:

$$
r_{H,\lambda_0}\simeq\rho|_{G_{F_H}},
\qquad
r_{D,\lambda_0}\simeq\rho|_{G_{F_D}}.
\tag{2.9}
$$

Compatibility of Galois realizations with prime-cyclic base change gives
$r_{\Pi,\lambda_0}\simeq\rho|_{G_{F_D}}$. The endpoint $\Pi$ and $\pi_D$ therefore have the
same good Hecke polynomials and the same selected central character. Strong multiplicity one
identifies them. This also removes any character ambiguity accumulated along the tower: a
nontrivial quotient twist would change the selected realization, and the self-twist exclusions
in the controlled field ledger rule out two different selected endpoints.

Once $\Pi\simeq\pi_D$ automorphically, compatibility of coefficient realizations with base
change gives (2.8) at every $\lambda$, not merely at $\lambda_0$. The construction is
independent of the chain (2.4), because any two endpoints are both $\pi_D$ by the same
argument. $\square$

No density theorem is used. The proof remains inside the prime-cyclic transfer, selected
descent, Galois realization, and strong-multiplicity-one interfaces already present in Books
186--187.

### 2.5 The repaired export

For $D=H_i\cap xH_jx^{-1}$, apply Theorem 2.3 once to $D\leq H_i$ and once to
$D\leq xH_jx^{-1}$. Conjugation compatibility gives

$$
r_{H_i,\lambda}|_{G_{F_D}}^{\mathrm{ss}}
\simeq r_{D,\lambda}
\simeq{}^xr_{H_j,\lambda}|_{G_{F_D}}^{\mathrm{ss}}.
\tag{2.10}
$$

After the Brauer characters are inserted, the two sides differ only by the explicit ratio

$$
\delta_{ij,x}
=({}^x\theta_j)|_D\,(\theta_i|_D)^{-1}.
\tag{2.11}
$$

This is exactly the overlap hypothesis used by the Mackey Gram calculation in Book 188.
Therefore its norm-one effectivity theorem, relation-independence theorem, and local
cancellation theorem are unconditional after the repair. Nothing in Chapters 3--12 below is
used to prove (2.10), so the interface is noncircular.

## 3. One algebraic coefficient ledger

### 3.1 Intrinsic fields and fields of realization

For each elementary packet $\pi_H$, let $K_H$ be the field generated by its good Hecke
eigenvalues, its central character, and the finite local-type values used in the controlled
family. The polynomial data are intrinsic to $K_H$. A rank-two multiplicity module or a local
type can require a finite extension of $K_H$ to split a simple algebra. We call any field over
which all those objects have models a field of realization.

Only finitely many subgroups occur in a fixed Brauer relation, and only finitely many
intersection subgroups occur in its Mackey Gram matrix. To compare two relations, take the
union of their two finite lists. Adjoin:

- every $K_H$ in the list;
- every value of every Brauer character;
- splitting fields for the finite packet algebras and finite local types; and
- the coefficients of the finitely many bad-place local comparison objects.

The compositum is a number field. Taking its normal closure over $\mathbf Q$ makes coefficient
conjugation visible without changing any isomorphism class after scalar extension.

We initially call this field $K$. It contains the algebraic Frobenius polynomials but need not
yet have a completion receiving the original coefficient field $L_0$.

### 3.2 Globalizing the distinguished completion

We use a standard approximation fact in a precise form.

**Lemma 3.1 (globalization of a local extension).** Let $K$ be a number field, let $v$ be a
finite place, and let $C/K_v$ be finite. There are a finite extension $E/K$ and a place
$\lambda_0\mid v$ such that

$$
E_{\lambda_0}\simeq C
\tag{3.1}
$$

as extensions of $K_v$.

**Proof.** By the primitive element theorem write $C=K_v(\alpha)$, with monic minimal
polynomial $f\in K_v[X]$. Separability makes the roots of $f$ distinct. Choose a sufficiently
small coefficient neighborhood of $f$ such that every monic polynomial in that neighborhood
has, by Krasner's lemma, one root generating an extension isomorphic to $C$.

The diagonal copy of $K$ is dense in $K_v$. Approximate the coefficients of $f$ by elements
of $K$ and obtain a monic $g\in K[X]$ in that neighborhood. Let $\beta$ be the root of $g$ in
the prescribed local root neighborhood and set $E=K(\beta)$. The place induced by the chosen
embedding $E\hookrightarrow\overline K_v$ has completion $K_v(\beta)\simeq C$. If $g$ has
extraneous global factors, replace $E$ by the field generated by the selected root; the local
conclusion is unchanged. $\square$

Choose a finite extension $C/K_v$ containing the completion used by every packet at the
distinguished embedding and the original field $L_0$. Apply Lemma 3.1. Enlarge the resulting
$E$ further, if necessary, by the finite splitting fields from Section 3.1 and take a normal
closure. Choose a place above the original $\lambda_0$ and retain the same notation. Its
completion embeds in a finite local overfield containing $L_0$; exact equality of completions
is no longer needed after the later harmless enlargement.

### 3.3 A common field for every elementary term

After the preceding enlargement, the compatible-system theorem of Book 137 gives, for every
elementary $H$ in the ledger and every finite place $\lambda$ of $E$, a continuous semisimple
representation

$$
r_{H,\lambda}:G_{F_H}\longrightarrow\operatorname{GL}_2(E_\lambda).
\tag{3.2}
$$

If an intrinsic packet field embeds in $E$ in several ways, the coefficient-conjugate packet is
used for the corresponding embedding. Thus (3.2) is an $E_\lambda$-model, not an unnamed
representation over $\overline{\mathbf Q}_{q_\lambda}$.

For a Brauer character $\theta_i:H_i\to E^\times$, inflation through
$G_{F_i}/G_M\simeq H_i$ gives an $E$-valued finite character. Its $\lambda$-adic realization
preserves the obvious free rank-one $\mathcal O_{E_\lambda}$-lattice. Define

$$
A_{i,\lambda}
=\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(r_{H_i,\lambda}\otimes\theta_{i,\lambda}).
\tag{3.3}
$$

Finite induction is defined over $E_\lambda$: after coset representatives are chosen, its
matrices contain only packet matrices, permutation matrices, and values of $\theta_i$. A change
of representatives conjugates the result over $E_\lambda$.

### 3.4 Places rather than unnamed embeddings

Let $q_\lambda$ be the residue characteristic of $\lambda$. An embedding

$$
\tau:E\hookrightarrow\overline{\mathbf Q}_{q_\lambda}
\tag{3.4}
$$

induces $\lambda$ exactly when it extends continuously to
$E_\lambda\hookrightarrow\overline{\mathbf Q}_{q_\lambda}$. Two embeddings inducing the same
place merely display the same completion in two ways. Therefore the member to be constructed
must first live over $E_\lambda$; only then can embedding independence be a formal scalar
transport statement.

This is stronger than choosing one embedding for every rational prime. A number field can have
several places above the same prime, and they are distinct members of a compatible system. The
common comparison is made through the polynomials in $E[X]$, not by identifying their
topological vector spaces.

### 3.5 The positive and negative representations

Write $n_i=n_i^+-n_i^-$ with $n_i^\pm\ge0$ and put

$$
R_\lambda^+=\bigoplus_iA_{i,\lambda}^{\oplus n_i^+},
\qquad
R_\lambda^-=\bigoplus_iA_{i,\lambda}^{\oplus n_i^-}.
\tag{3.5}
$$

Both are actual continuous semisimple $E_\lambda$-representations. Semisimplicity follows from
the normal-core argument of Book 187: restriction to $G_M$ is a direct sum of semisimple
conjugates of the top packet, and averaging a projection over the finite quotient promotes a
$G_M$-stable complement to a $G_{\mathbf Q}$-stable complement.

For any embedding $j:E_\lambda\hookrightarrow\Omega$ into an algebraically closed field,
Book 188, now unconditional by Chapter 2, proves

$$
[R_\lambda^+\otimes_j\Omega]
-[R_\lambda^-\otimes_j\Omega]
=[S_{\lambda,j}],
\tag{3.6}
$$

where $S_{\lambda,j}$ is absolutely irreducible of dimension two. Equation (3.6) is the exact
input for coefficient descent.

## 4. Multiplicity-one descent of an effective constituent

### 4.1 The descent obstruction

Suppose an absolutely irreducible representation $S$ over an algebraic closure $\overline F$ is
fixed up to isomorphism by $\operatorname{Aut}(\overline F/F)$. It does not follow in general
that $S$ has an $F$-model. The intertwiners between $S$ and its conjugates can compose only up
to scalars, producing a class in a Brauer group. Equivalently, the corresponding simple
$F$-module can have a division algebra as endomorphism ring. After scalar extension, such a
module contains several copies of $S$; their common multiplicity is the Schur index.

Our situation contains more information than invariance. The class $[S]$ is the difference of
two semisimple representations already defined over $F$. The coefficient of $S$ in that
difference is exactly one. The next two lemmas show that this coefficient is incompatible with
a nontrivial orbit or Schur index.

### 4.2 The multiplicity divisibility lemma

**Lemma 4.1 (orbit and Schur multiplicity).** Let $F$ be a characteristic-zero field, let $G$
be a group, and let $T$ be a finite-dimensional simple $F$-representation of $G$. Let
$\overline F$ be an algebraic closure. Then the semisimplification of
$T\otimes_F\overline F$ has the form

$$
(T\otimes_F\overline F)^{\mathrm{ss}}
\simeq m\bigoplus_{\sigma\in\mathcal O}S^\sigma,
\tag{4.1}
$$

where $S$ is absolutely irreducible, $\mathcal O$ is one finite Galois orbit of pairwise
nonisomorphic conjugates, and $m\ge1$ is independent of $\sigma$.

**Proof.** Let $B$ be the image of $F[G]$ in $\operatorname{End}_F(T)$. It is a
finite-dimensional $F$-algebra, and $T$ is a simple $B$-module. Its endomorphism ring

$$
\Delta=\operatorname{End}_B(T)
\tag{4.2}
$$

is a finite-dimensional division algebra. The center $Z$ of $\Delta$ is finite over $F$.
After extending to a normal closure of $Z/F$ and then splitting $\Delta$, the simple module
decomposes into absolutely irreducible modules indexed by the embeddings of the relevant
center. Galois permutes these constituents transitively because $T$ was simple over $F$.
The matrix degree of the split division algebra is the same at every conjugate embedding and
is the common multiplicity $m$. Further scalar extension to $\overline F$ gives (4.1).
$\square$

The lemma has an immediate divisibility consequence: in the scalar extension of any virtual
integral combination of simple $F$-modules, the coefficient of every $S^\sigma$ is an integer
multiple of the corresponding Schur multiplicity $m$ and is constant on the orbit
$\mathcal O$.

### 4.3 Descent from a signed equality

**Theorem 4.2 (multiplicity-one descent).** Let $V^+$ and $V^-$ be finite-dimensional
semisimple $F$-representations of a group $G$. Suppose that over $\overline F$

$$
[V^+_{\overline F}]-[V^-_{\overline F}]=[S]
\tag{4.3}
$$

for one absolutely irreducible representation $S$. Then there is a unique isomorphism class of
absolutely irreducible $F$-representation $V$ such that

$$
V\otimes_F\overline F\simeq S
\tag{4.4}
$$

and

$$
V^+\simeq V\oplus V^-.
\tag{4.5}
$$

**Proof.** Decompose $V^+$ and $V^-$ into simple $F$-modules. Apply Lemma 4.1 to each simple
module. The coefficient function of the left side of (4.3), on absolutely irreducible
$\overline F$-representations, is constant on every Galois orbit and divisible on that orbit by
its Schur multiplicity.

The right side has coefficient one at $S$ and zero everywhere else. It follows first that the
orbit of $S$ is a singleton: otherwise every conjugate $S^\sigma$ would also have coefficient
one. It follows next that the Schur multiplicity is one, because it divides the coefficient
one. Thus the unique simple $F$-module $V$ in the corresponding block satisfies (4.4), and its
coefficient in $[V^+]-[V^-]$ is one. Every other simple $F$-module has coefficient zero.
Therefore

$$
[V^+]-[V^-]=[V]
\tag{4.6}
$$

in the semisimple Grothendieck group over $F$. Equality of simple multiplicities gives the
actual semisimple isomorphism (4.5). The module $V$ is absolutely irreducible by (4.4), and
uniqueness follows from the unique simple decomposition. $\square$

### 4.4 Why the Schur obstruction vanishes here

Apply Theorem 4.2 with

$$
F=E_\lambda,
\qquad V^\pm=R_\lambda^\pm.
\tag{4.7}
$$

Book 188 provides (4.3). Consequently its algebraically closed effective member has an
$E_\lambda$-model, and the cancellation already occurs over $E_\lambda$.

This proof is stronger than saying that the trace field is $E_\lambda$. Character values do not
by themselves kill a quaternionic Schur obstruction. The obstruction vanishes because an
$E_\lambda$-defined virtual class has geometric multiplicity one. A division algebra of index
$m>1$ would make that multiplicity divisible by $m$.

It is also stronger than choosing a finite local extension separately at every place. No new
local extension is needed after the common packet realization field $E$ has been fixed. The
member descends to the completion $E_\lambda$ itself.

### 4.5 Descent of isomorphisms

We will repeatedly know that two $E_\lambda$-representations become isomorphic after scalar
extension. The following observation brings the comparison back down.

**Lemma 4.3 (faithful descent of an intertwiner).** Let $V$ and $W$ be finite-dimensional
$F$-representations of a group $G$, and let $F'/F$ be a field extension. If

$$
V\otimes_FF'\simeq W\otimes_FF',
\tag{4.8}
$$

then $V\simeq W$ provided both are absolutely irreducible.

**Proof.** Equivariance is a system of homogeneous linear equations in
$\operatorname{Hom}_F(V,W)$. Their common kernel commutes with flat scalar extension, so

$$
\operatorname{Hom}_G(V,W)\otimes_FF'
\simeq\operatorname{Hom}_G(V\otimes F',W\otimes F').
\tag{4.9}
$$

The right side is nonzero by (4.8), hence the left factor
$\operatorname{Hom}_G(V,W)$ is nonzero. A nonzero map between irreducible representations is
an isomorphism. $\square$

Only finitely many group elements are needed in the kernel calculation: the subspace spanned by
the equations stabilizes inside the finite-dimensional Hom space. Thus the lemma applies to
profinite Galois groups without a finite-image assumption.

## 5. Construction at every coefficient place

### 5.1 The effective constituent over a completion

**Definition 5.1.** For a finite place $\lambda$ of $E$, let

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda)
\tag{5.1}
$$

be the unique representation supplied by Theorem 4.2 from the signed equality (3.6).

Equivalently, $r_\lambda$ is characterized by either of the following two conditions:

$$
R_\lambda^+\simeq r_\lambda\oplus R_\lambda^-,
\tag{5.2}
$$

or, after any embedding $E_\lambda\hookrightarrow\Omega$ into an algebraically closed field,

$$
r_\lambda\otimes_{E_\lambda}\Omega
\simeq r_{\mathfrak B,\tau}.
\tag{5.3}
$$

The first characterization constructs the member over the completion. The second identifies it
with the effective member of Book 188.

### 5.2 Continuity and absolute irreducibility

**Proposition 5.2.** The representation $r_\lambda$ is continuous and absolutely irreducible.

**Proof.** Equation (5.2) realizes $r_\lambda$ as a $G_{\mathbf Q}$-stable direct summand of
the finite-dimensional continuous representation $R_\lambda^+$. A linear subspace over a
nonarchimedean local field is closed, and restricting a continuous action to a closed stable
subspace is continuous. Absolute irreducibility follows from (5.3), because scalar extension to
an algebraic closure is the irreducible member proved effective in Book 188. $\square$

Continuity is therefore a consequence of actual characteristic-zero cancellation. It is not
inferred from continuity of the Frobenius trace function.

### 5.3 Independence of the displaying embedding

Let $j_1,j_2:E_\lambda\hookrightarrow\Omega$ be two embeddings into a common algebraically
closed field. Each scalar extension of $r_\lambda$ is the unique effective constituent of the
corresponding scalar extension of the same signed $E_\lambda$-class. Hence the two displayed
representations are carried into one another by scalar transport.

More concretely, every matrix coefficient of $R_\lambda^\pm$ is transported by $j_a$, the
norm-one theorem selects the unique irreducible class in each transported signed expression,
and uniqueness makes that selection commute with $j_a$. Thus the invariant index is the place
$\lambda$, not the auxiliary embedding.

### 5.4 Scalar extension

Let $E'/E$ be finite and let $\lambda'$ lie above $\lambda$. Construct the family using the
scalar-extended elementary packet ledger over $E'$. Then

$$
R_{\lambda'}^\pm
\simeq R_\lambda^\pm\otimes_{E_\lambda}E'_{\lambda'}.
\tag{5.4}
$$

Scalar extension of (5.2) gives one effective complement. Uniqueness gives

$$
r_{\lambda'}
\simeq r_\lambda\otimes_{E_\lambda}E'_{\lambda'}.
\tag{5.5}
$$

Thus enlarging the common coefficient field refines the indexing by places and extends scalars;
it does not change the arithmetic family.

### 5.5 What coherence means

Representations over different completions are not compared by a linear isomorphism. Their
scalar fields can have different residue characteristics. Coherence means instead:

- one number field $E$ indexes every member by its finite places;
- every member has matrices over the corresponding completion $E_\lambda$;
- good Frobenius polynomials lie in $E[X]$ before completion;
- bad local Weil--Deligne objects lie over $E$ before completion; and
- coefficient embeddings, field enlargement, and Brauer decomposition commute with the
  construction.

These are precisely the data of a compatible system. No chosen web of inter-completion vector
space maps is either available or required.

## 6. Independence of Brauer decomposition

### 6.1 Two relations in one ledger

Let

$$
\mathfrak B=\{(H_i,\theta_i,n_i)\},
\qquad
\mathfrak B'=\{(J_j,\eta_j,m_j)\}
\tag{6.1}
$$

be two integral Brauer relations for $1_\Gamma$. Enlarge $E$ once to realize every packet,
character, intersection packet, and bad local type in the union of the two finite ledgers. This
is a harmless scalar extension by (5.5).

For a coefficient place $\lambda$, let $\mathcal R_{\mathfrak B,\lambda}$ and
$\mathcal R_{\mathfrak B',\lambda}$ be the two virtual classes over $E_\lambda$. Their
difference is represented by one combined signed list.

### 6.2 Norm-zero comparison

Book 188 applies the Mackey Gram calculation to that combined list. Every cross term is
computed on a subgroup

$$
H_i\cap xJ_jx^{-1},
\tag{6.2}
$$

which is elementary and satisfies the repaired overlap identity of Chapter 2. The resulting
Gram matrix is independent of the coefficient embedding.

At the distinguished embedding, the tensor identity identifies both Brauer expressions with
$[\rho]$. Their difference is zero, so its character norm is zero. The same Gram matrix at any
other embedding has the same quadratic value. Positive definiteness of the integral Hom norm
therefore gives

$$
\mathcal R_{\mathfrak B,\lambda}\otimes\overline E_\lambda
=\mathcal R_{\mathfrak B',\lambda}\otimes\overline E_\lambda
\tag{6.3}
$$

in the semisimple Grothendieck group.

### 6.3 Independence over the completion

Both sides of (6.3) are effective and absolutely irreducible. Let their descended
$E_\lambda$-models be $r_{\mathfrak B,\lambda}$ and
$r_{\mathfrak B',\lambda}$. They become isomorphic over $\overline E_\lambda$, so Lemma 4.3
gives

$$
r_{\mathfrak B,\lambda}
\simeq r_{\mathfrak B',\lambda}
\tag{6.4}
$$

over $E_\lambda$ itself.

This is the desired independence of Brauer decomposition. It is stronger than equality of good
Frobenius polynomials and does not use a density theorem. The norm calculation compares the
entire semisimple classes; multiplicity-one descent then returns the comparison to the chosen
completion.

### 6.4 Independence of presentation and conjugate terms

Changing $n_i=n_i^+-n_i^-$ only adds the same summand to $R_\lambda^+$ and
$R_\lambda^-$. The signed class is unchanged, so its unique descended effective constituent is
unchanged.

Replacing $(H_i,\theta_i,\pi_{H_i})$ by a conjugate triple replaces (3.3) by an isomorphic
induced representation. Indeed, conjugation transports the fixed field and packet, and the map
$g\otimes v\mapsto gx^{-1}\otimes{}^xv$ gives the induction isomorphism. Thus field
conjugation permutes a presentation without changing $r_\lambda$.

Changing coset representatives in finite induction, bases in packet modules, polarizations by
nonzero scalars, or split-matrix coordinates conjugates actual summands and therefore leaves the
unique complement unchanged. The rational independence statements of Book 137 pass through the
construction term by term.

### 6.5 The intrinsic member

Because of (6.4), we now suppress $\mathfrak B$ and write simply $r_\lambda$. The notation
denotes an isomorphism class over $E_\lambda$. Choosing a relation remains useful for proving
properties: it presents $r_\lambda$ as a complement inside explicit induced automorphic
representations. It is not part of the resulting family.

## 7. Common Frobenius polynomials

### 7.1 The algebraic polynomial

Fix a rational prime $p$ outside the finite good-place exclusions of the elementary packet
ledger. For a Brauer term indexed by $H_i$, let $w$ run over the places of $F_i$ above $p$ and
let $f_w=f(w/p)$. If

$$
X^2-a_{i,w}X+Nw
\tag{7.1}
$$

is the arithmetic-Frobenius polynomial of $\pi_{H_i}$ at $w$, twisting by $\theta_i$ and
inducing locally gives the characteristic series

$$
\prod_{w\mid p}
\left(
1-a_{i,w}\theta_i(\operatorname{Frob}_w)T^{f_w}
+\theta_i(\operatorname{Frob}_w)^2Nw\,T^{2f_w}
\right).
\tag{7.2}
$$

The power $T^{f_w}$ is forced by the Frobenius cycle on the embeddings of $F_i$ in $M$. If
$\alpha$ is an eigenvalue of $\operatorname{Frob}_w$, the corresponding cyclic block of
$\operatorname{Frob}_p$ has determinant $1-\alpha T^{f_w}$. This proves (7.2) without a
choice of Satake roots.

Taking the signed product over the Brauer relation gives an element

$$
D_{p,\mathfrak B}(T)\in E(T)^\times.
\tag{7.3}
$$

At the distinguished place, the tensor identity identifies the virtual class with $\rho$, so

$$
D_{p,\mathfrak B}(T)
=\det(1-\rho(\operatorname{Frob}_p)T)
=1-a_pT+pT^2
\tag{7.4}
$$

inside a finite $\ell$-adic overfield. The embedding of $E(T)$ in that overfield is injective.
Thus (7.4) is already an equality in $E(T)$, and its right side lies in $E[T]$. Define

$$
P_p(X)=X^2-a_pX+p.
\tag{7.5}
$$

By Chapter 6, using another Brauer relation gives the same representation at the distinguished
place and hence the same polynomial. Thus $P_p$ is intrinsic to the assembled family.

### 7.2 Unramifiedness of the effective constituent

**Lemma 7.1.** Let $I$ be a subgroup of $G$, let $V=W\oplus U$ be a direct sum of
$G$-representations, and suppose $I$ acts trivially on $V$. Then $I$ acts trivially on both
$W$ and $U$.

**Proof.** The action on each stable summand is the restriction of the identity action on
$V$. $\square$

Let $q_\lambda$ be the residue characteristic of $\lambda$. At a rational prime $p$ outside
the common exceptional set and with $p\ne q_\lambda$, every elementary packet, quotient
character, and extension entering $R_\lambda^\pm$ is unramified. Hence $R_\lambda^+$ is
unramified. Equation (5.2) and Lemma 7.1 imply that $r_\lambda$ is unramified.

Taking determinants of $1-\operatorname{Frob}_pT$ in (5.2) gives

$$
\det(1-r_\lambda(\operatorname{Frob}_p)T)
=D_{p,\mathfrak B}(T)
=1-a_pT+pT^2.
\tag{7.6}
$$

Equivalently,

$$
\det(X-r_\lambda(\operatorname{Frob}_p))=P_p(X).
\tag{7.7}
$$

This is now the characteristic polynomial of an actual two-dimensional representation, not a
rational determinant of a virtual class.

### 7.3 Weak compatibility

**Theorem 7.2 (weak compatibility before shrinking the bad set).** There is a finite set
$S_0$ of rational primes, independent of $\lambda$, such that the collection
$\{r_\lambda\}_\lambda$ is an $E$-rational weakly compatible system of rank two with common
polynomials $P_p$ for $p\notin S_0$.

**Proof.** Choose $S_0$ to contain every rational prime ramified in $M$, every prime below a
ramified elementary packet or Brauer character, the primes in the finite local-type ledger,
and $2,\ell$. Outside $S_0\cup\{q_\lambda\}$ all summands in (3.5) are unramified. Section 7.2
gives unramifiedness and (7.7). The set and polynomials do not depend on $\lambda$. $\square$

The theorem already constructs a compatible system. The next section uses the original member
and strict local compatibility to remove auxiliary primes introduced only by the Galois top and
the Brauer presentation.

### 7.4 Removing auxiliary bad primes

Let $p\in S_0\setminus\{2,\ell\}$. Since $p\ne\ell$, the local Weil--Deligne comparison at
the distinguished place is available. The original representation $\rho$ is unramified at
$p$. Chapter 9 will construct a common local object $D_p$ whose realization at $\lambda_0$ is
$\operatorname{WD}_p(\rho)$. It follows that $D_p$ is unramified. Define $P_p$ at these
formerly auxiliary primes to be the characteristic polynomial of Frobenius on $D_p$. Its
coefficients lie in $E$, and its realization at $\lambda_0$ is
$\det(X-\rho(\operatorname{Frob}_p))=X^2-a_pX+p$. Every $r_\lambda$ with
$q_\lambda\ne p$ is therefore unramified at $p$ and has this same Frobenius polynomial.

This argument cancels auxiliary ramification at the level of the actual effective
representation. It does not claim that inertia cancels term by term inside the positive and
negative Brauer presentations. Once Chapter 9 is established, the weakly compatible exceptional
set can be reduced to

$$
S=\{2,\ell\}.
\tag{7.8}
$$

At the varying coefficient prime $q_\lambda$, weak compatibility deliberately makes no
unramifiedness assertion, even if that prime lies outside $S$.

### 7.5 Purity

**Theorem 7.3 (weight-one purity).** For every $p\notin\{2,\ell\}$, every root $\alpha_p$ of
$P_p$ is a $p$-Weil number of weight one:

$$
|\iota(\alpha_p)|=p^{1/2}
\tag{7.9}
$$

for every embedding $\iota:\overline{\mathbf Q}\hookrightarrow\mathbf C$.

**Proof.** Choose a place $w$ of $M$ above $p$ and let $f=f(w/p)$. Restriction of the
unramified representation $r_{\lambda_0}\simeq\rho$ from $G_{\mathbf Q_p}$ to $G_{M_w}$
raises arithmetic-Frobenius eigenvalues to their $f$th powers. Thus the roots of the top packet
polynomial at $w$ are

$$
\alpha_p^f,\qquad\beta_p^f.
\tag{7.10}
$$

The parallel-weight-two packet $\pi_M$ is pure of weight one by the compatible-system and
purity theorem of Book 137. Therefore every complex embedding has

$$
|\iota(\alpha_p^f)|=(p^f)^{1/2}.
\tag{7.11}
$$

Taking the positive real $f$th root gives (7.9). Applying the same argument to every
coefficient-conjugate top packet proves the assertion for every conjugate of every root.
$\square$

The proof uses the actual restriction of the original member to $M$. It does not infer purity
from the product $\alpha_p\beta_p=p$, which by itself would allow unequal absolute values.

### 7.6 Frobenius powers

The common polynomial determines every unramified residue-degree transform. If
$\alpha_p,\beta_p$ are its roots, put

$$
A_{p,f}=\alpha_p^f+\beta_p^f.
\tag{7.12}
$$

Then

$$
A_{p,0}=2,
\qquad A_{p,1}=a_p,
\qquad A_{p,f}=a_pA_{p,f-1}-pA_{p,f-2}.
\tag{7.13}
$$

The recurrence follows by applying
$x^2=a_px-p$ to both roots. It proves $A_{p,f}\in E$ without choosing the roots. At a place of
residue degree $f$, the restricted polynomial is

$$
X^2-A_{p,f}X+p^f.
\tag{7.14}
$$

Formula (7.14) is the common base-change record. Reusing $a_p$ at a degree-$f$ place would be a
Frobenius-normalization error.

## 8. Determinant, duality, and the original member

### 8.1 The actual determinant

Book 187 computes the determinant of the signed class using the determinant of finite
induction. For a rank-two representation $u$ of an open subgroup $H\leq G$,

$$
\det\operatorname{Ind}_H^Gu
=\operatorname{sgn}_{G/H}^{,2}\operatorname{Ver}_H^G(\det u)
=\operatorname{Ver}_H^G(\det u).
\tag{8.1}
$$

Twisting by a linear character $\theta$ multiplies $\det u$ by $\theta^2$. The determinant of
the one-dimensional Brauer relation cancels the transferred squares, while evaluation of that
relation at the identity gives

$$
\sum_i n_i[\Gamma:H_i]=1.
\tag{8.2}
$$

Consequently the virtual determinant line is $\chi_\lambda$. Substituting the actual equality
(5.2) turns the line identity into

$$
\boxed{\det r_\lambda=\chi_\lambda.}
\tag{8.3}
$$

No determinant-normalizing twist is chosen afterward. Such a twist would change the common
Frobenius and local records. Equation (8.3) is inherited from the complete Brauer transfer
calculation.

### 8.2 Duality

For every two-dimensional representation $V$, the map

$$
V\longrightarrow V^\vee\otimes\det V,
\qquad
x\longmapsto(y\mapsto x\wedge y)
\tag{8.4}
$$

is an isomorphism. Applying (8.3) gives

$$
r_\lambda^\vee
\simeq r_\lambda\otimes\chi_\lambda^{-1}.
\tag{8.5}
$$

This is a rational duality statement. At $\lambda_0$, the selected alternating pairing on the
original lattice realizes it integrally. At a new coefficient place, (8.5) does not choose a
self-dual lattice or control the index of a lattice in its dual.

At a good $p$, (8.3) gives

$$
\alpha_p\beta_p=p,
\tag{8.6}
$$

which agrees with (7.5) and arithmetic Frobenius. For geometric Frobenius the product is
$p^{-1}$.

### 8.3 Identification at the distinguished place

The number field $E$ and its place $\lambda_0$ were chosen so that all distinguished packet
realizations and $\rho$ embed into one finite extension $C/\mathbf Q_\ell$. At that embedding,
the tensor identity for the Brauer relation gives

$$
[R_{\lambda_0}^+\otimes C]-[R_{\lambda_0}^-\otimes C]
=[\rho\otimes_{L_0}C].
\tag{8.7}
$$

The right side is absolutely irreducible. The unique effective complement therefore satisfies

$$
r_{\lambda_0}\otimes_{E_{\lambda_0}}C
\simeq\rho\otimes_{L_0}C.
\tag{8.8}
$$

This identifies the original member itself, not merely its semisimplification at good
Frobenius elements. Both sides are already semisimple and absolutely irreducible.

### 8.4 The original local records

Equation (8.8) retains every rational local property of $\rho$. More importantly, the selected
lattice of $\rho$ is not discarded and reconstructed from (8.8). It remains the named integral
model of the $\lambda_0$ member. Thus:

- every quotient of that lattice has the selected coefficient-linear finite locally free model
  at $\ell$;
- at $2$ its wild inertia is trivial, its monodromy is zero, and a tame generator satisfies
  $T^2+T+1=0$;
- it is unramified away from $2$ and $\ell$; and
- its determinant pairing is the original cyclotomic pairing.

The common compatible family contains this member exactly. It does not replace the original
lattice by a lattice cut from the large induced representations.

## 9. Strict local compatibility

### 9.1 The algebraic local Mackey object

Fix a finite rational prime $p$. For every elementary packet $\pi_{H_i}$ and every place
$w\mid p$ of $F_i$, Book 137 supplies, away from coefficient characteristic, an algebraic
Frobenius-semisimple Weil--Deligne object

$$
D_{i,w}
\tag{9.1}
$$

over a finite extension of its Hecke field. The common field $E$ was chosen to contain models
of the finitely many bad local objects. At good places $D_{i,w}$ is unramified and is determined
by its Hecke polynomial.

Finite-order twisting, finite local induction, and direct sum are algebraic operations on
Weil--Deligne representations. Define the local positive and negative objects

$$
\mathscr D_{p,E}^\pm
=\bigoplus_i\bigoplus_{w\mid p}
\left(
\operatorname{Ind}_{W_{(F_i)_w}}^{W_{\mathbf Q_p}}
(D_{i,w}\otimes\theta_{i,w})
\right)^{\oplus n_i^\pm}.
\tag{9.2}
$$

Their signed difference is the **algebraic local Mackey class**. It records the finite inertia
action, the Frobenius return maps, and the monodromy operator. It is stronger than a conductor
or an inertial type.

For a place $\lambda$ with $q_\lambda\ne p$, local--global compatibility of every elementary
packet and local Mackey decomposition identify

$$
\mathscr D_{p,E}^\pm\otimes_EE_\lambda
\simeq\operatorname{WD}_p(R_\lambda^\pm)^{\mathrm{F\!-\!ss}}.
\tag{9.3}
$$

Applying $\operatorname{WD}$ to (5.2) gives

$$
\mathscr D_{p,E}^+\otimes_EE_\lambda
\simeq
\operatorname{WD}_p(r_\lambda)^{\mathrm{F\!-\!ss}}
\oplus
\mathscr D_{p,E}^-\otimes_EE_\lambda.
\tag{9.4}
$$

### 9.2 Krull--Schmidt cancellation

We need to know that the remaining local object in (9.4) is determined before $\lambda$ is
chosen. Weil--Deligne representations over a characteristic-zero field form a finite-length
Krull--Schmidt category for direct sums: every object is a finite direct sum of indecomposables,
and the multiset of indecomposable summands is unique.

For completeness, let $D$ be one Weil--Deligne representation. The algebra generated by its
finite inertia image, one Frobenius operator and its inverse, and $N$ inside
$\operatorname{End}(D)$ is finite dimensional. Direct-sum decompositions of $D$ are exactly
module decompositions for this finite-dimensional algebra. The endomorphism ring of an
indecomposable finite-length module is local, and the usual exchange argument gives uniqueness
of indecomposable multiplicities. Thus

$$
U\oplus C\simeq V\oplus C
\quad\Longrightarrow\quad U\simeq V.
\tag{9.5}
$$

The same statement applies to Frobenius-semisimplified objects; semisimplifying Frobenius does
not remove finite inertia or $N$.

### 9.3 A common Weil--Deligne pair

**Theorem 9.1 (strict compatibility).** After one finite enlargement of $E$ that splits the
finitely many bad local complements, for every finite prime $p$ there is a rank-two
Frobenius-semisimple Weil--Deligne representation $D_p$ over $E$ such that

$$
\mathscr D_{p,E}^+\simeq D_p\oplus\mathscr D_{p,E}^-
\tag{9.6}
$$

and, for every $\lambda$ with $q_\lambda\ne p$,

$$
\operatorname{WD}_p(r_\lambda)^{\mathrm{F\!-\!ss}}
\simeq D_p\otimes_EE_\lambda.
\tag{9.7}
$$

**Proof.** First work over an algebraic closure $\overline E$. Choose one coefficient place
$\lambda$ away from $p$ and an embedding $\overline E\hookrightarrow\overline E_\lambda$.
Equation (9.4) proves that every indecomposable multiplicity in
$[\mathscr D_{p,E}^+]-[\mathscr D_{p,E}^-]$ is nonnegative after scalar extension, because the
difference is represented by the actual local object of $r_\lambda$. Faithful scalar extension
and Krull--Schmidt uniqueness bring those multiplicities back to $\overline E$. Their total
rank is two. Let $D_{p,\overline E}$ be the resulting complement.

At all but finitely many $p$, the original local summands are unramified and the complement is
the unramified pair determined by $P_p$; it has an $E$-model. At the finitely many remaining
places, every matrix and decomposition idempotent is algebraic. Adjoin their finitely many
coefficients to $E$. Then all $D_{p,\overline E}$ descend simultaneously to $E$ and (9.6)
holds. Scalar extension of (9.6), comparison with (9.4), and cancellation (9.5) prove (9.7).
$\square$

Changing the Brauer relation does not change $D_p$. The global representations obtained from
two relations are isomorphic over every completion by (6.4), so their local Weil--Deligne
objects agree. A faithful coefficient embedding and Krull--Schmidt uniqueness then identify the
two algebraic complements after the common harmless enlargement.

### 9.4 The dyadic type

The prime $2$ splits completely in $M$. Therefore every completion of every elementary fixed
field above $2$ is $\mathbf Q_2$, and every quotient character $\theta_i$ is locally trivial.
All elementary packet local objects are copies of the same rank-two pair

$$
D_2^{\mathrm{top}},
\qquad
N=0,
\qquad
I_2^{\mathrm{wild}}=1,
\qquad
T^2+T+1=0.
\tag{9.8}
$$

Local Mackey gives

$$
[\mathscr D_{2,E}^+]-[\mathscr D_{2,E}^-]
=\left(\sum_i n_i[\Gamma:H_i]\right)[D_2^{\mathrm{top}}]
=[D_2^{\mathrm{top}}].
\tag{9.9}
$$

Thus $D_2\simeq D_2^{\mathrm{top}}$. For every coefficient place of residue characteristic
different from two, the member $r_\lambda$ has exactly the primitive tame order-three
Weil--Deligne type. This is equality of the full pair, not inference from conductor two or from
the characteristic polynomial of tame inertia alone.

At a two-adic coefficient place, (9.7) is outside the prime-to-coefficient Weil--Deligne range.
The global representation still exists and is continuous, but no two-adic Hodge-theoretic or
integral dyadic assertion is made here.

### 9.5 The prime of the original lift

At $p=\ell$, Theorem 9.1 gives a common $D_\ell$ for every coefficient place whose residue
characteristic is not $\ell$. It is computed from the elementary automorphic local records and
is independent of the Brauer relation.

The member $r_{\lambda_0}$ has coefficient characteristic $\ell$, so (9.7) does not compare
its local representation with $D_\ell$. Its correct local datum is instead the selected
finite-flat lattice of $\rho$. Relating that lattice to $D_\ell$ by crystalline or semistable
comparison would be an additional coefficient-prime theorem. It is neither needed for strict
compatibility in the usual varying-prime sense nor proved here.

This separation prevents the rational local family from silently acquiring the integral local
theory reserved for the next stage of the critical spine.

### 9.6 Conductors and local factors

For $p\ne q_\lambda$, strict compatibility makes the following invariants independent of
$\lambda$:

$$
\begin{aligned}
P_p^{\mathrm{loc}}(T)
&=\det(1-T\operatorname{Frob}_p\mid(\ker N_p)^{I_p}),\cr
a_p^{\mathrm{Art}}
&=\dim D_p-\dim(\ker N_p)^{I_p}+\operatorname{Sw}(D_p),\cr
\operatorname{rank}N_p,&\qquad
\operatorname{Sw}(D_p).
\end{aligned}
\tag{9.10}
$$

Indeed, all are invariants of the common pair $D_p$, and scalar extension preserves kernels,
invariants, nilpotent ranks, and the finite ramification filtration. With a fixed additive
character and Haar measure, the same applies to the epsilon factor.

At $p\notin\{2,\ell\}$, the distinguished member is available in the prime-to-coefficient
range and is unramified. Hence $D_p$ is unramified, $N_p=0$, $a_p^{\mathrm{Art}}=0$, and

$$
P_p^{\mathrm{loc}}(T)=1-a_pT+pT^2.
\tag{9.11}
$$

This proves the shrinking of the weak exceptional set asserted in Section 7.4. Auxiliary
discriminant and character ramification cancel in the effective local complement even though
they remain visible in a chosen Brauer presentation.

## 10. Coefficient covariance and family-level descent

### 10.1 Coefficient conjugation

Assume $E/\mathbf Q$ is Galois, as arranged in Chapter 3. For
$\sigma\in\operatorname{Gal}(E/\mathbf Q)$, a place $\lambda$ is carried to
$\sigma\lambda$, and $\sigma$ extends to a topological field isomorphism

$$
\sigma:E_\lambda\xrightarrow{\sim}E_{\sigma\lambda}.
\tag{10.1}
$$

Applying $\sigma$ to every elementary packet coefficient and Brauer-character value carries
$R_\lambda^\pm$ to the positive and negative representations for the conjugate ledger at
$\sigma\lambda$. Multiplicity-one descent commutes with this scalar transport. Therefore

$$
{}^\sigma r_\lambda
\simeq r^{\sigma}_{\sigma\lambda},
\tag{10.2}
$$

where the superscript on the right indicates the coefficient-conjugate polynomial record. At a
good prime,

$$
P_p^\sigma(X)=X^2-\sigma(a_p)X+p,
\tag{10.3}
$$

and at a bad prime the common local object is $D_p^\sigma$.

Coefficient conjugation does not move the number fields $F_H$ inside $M$. Field conjugation
moves those fields and their places but leaves the induced ground-field term isomorphic.
Because the two actions address different entries of the packet ledger, they commute.

### 10.2 Changing the common field

Let $E'/E$ be finite. The scalar-extended family has members

$$
r'_{\lambda'}
=r_\lambda\otimes_{E_\lambda}E'_{\lambda'}
\qquad(\lambda'\mid\lambda),
\tag{10.4}
$$

common polynomials viewed in $E'[X]$, and local pairs
$D_p\otimes_EE'$. Equation (5.5) proves that reconstructing the family from the enlarged
Brauer ledger yields exactly (10.4).

Conversely, the multiplicity-one theorem already gives models over $E_\lambda$, so the
extension $E'$ is not part of the intrinsic construction unless it is needed to display a
finite set of local types. Even then, the system over $E'$ is merely scalar extension of the
one over $E$ after those local objects are descended. No minimal coefficient field is claimed.

### 10.3 Descent data without chosen matrices

A compatible system is naturally a family of isomorphism classes, not a family of preferred
bases. The descent proved here consists of:

1. an $E_\lambda$-model of every effective algebraically closed member;
2. uniqueness of that model as the complement in (5.2);
3. covariance under every coefficient embedding and field enlargement; and
4. common algebraic polynomial and local data.

No semilinear intertwiner is chosen for every automorphism of $E$, and no cocycle of matrices is
needed. Such intertwiners would describe a particular based descent. The representation over
$E_\lambda$ already is the descended object.

The Schur obstruction was a genuine possible obstruction to this conclusion. Chapter 4 killed
it by multiplicity divisibility, not by suppressing the need for descent data.

### 10.4 The global compatible family

**Theorem 10.1 (family-level assembly).** The collection

$$
\mathcal R_E=\{r_\lambda\}_{\lambda\in\operatorname{Pl}_f(E)}
\tag{10.5}
$$

together with the polynomials $P_p$ for $p\notin\{2,\ell\}$ and the local pairs $D_p$ is an
$E$-rational, pure, strictly compatible system of rank two over $\mathbf Q$. It is independent
of the Brauer relation and contains the original representation at $\lambda_0$.

**Proof.** The members and their continuity are Proposition 5.2. Relation-independence is
Chapter 6. Weak compatibility with exceptional set $\{2,\ell\}$ is Chapters 7.2--7.4. Purity
is Theorem 7.3. Determinant and duality are Chapter 8. Strict compatibility is Theorem 9.1.
The distinguished identification is (8.8), and coefficient covariance and field enlargement
are Sections 10.1--10.2. These are exactly the defining and choice-independence clauses of the
stated compatible system. $\square$

The theorem is the point at which the phrase “the family over the base field” becomes
justified. Before coefficient descent, there were effective representations over algebraic
closures; before effectivity, there was a virtual class; before Brauer induction, there were
only elementary-field systems. The theorem does not identify those stages retroactively.

## 11. Stable lattices and the integral boundary

### 11.1 Existence place by place

Let $V$ be a finite-dimensional $E_\lambda$-representation of a profinite group with continuous
action. Its image is compact. Starting from any lattice $L_0$, compactness bounds all matrix
entries and their inverses, so the sum

$$
L=\sum_{g\in G_{\mathbf Q}}gL_0
\tag{11.1}
$$

lies between two scalar multiples of $L_0$. It is a finitely generated torsion-free
$\mathcal O_{E_\lambda}$-module spanning $V$, hence a lattice, and it is stable by
construction.

Apply this to $r_\lambda$.

**Proposition 11.1.** Every member $r_\lambda$ has a stable
$\mathcal O_{E_\lambda}$-lattice.

Existence uses only continuity. It supplies no preferred lattice and no relation between
lattices at different coefficient places.

### 11.2 The distinguished lattice

At $\lambda_0$, retain the lattice $L_\rho$ chosen in Book 185 and carried through Book 186.
After the common finite scalar extension used in (8.8), it is a stable lattice for
$r_{\lambda_0}$. Its residual representation is absolutely irreducible, so any other stable
lattice with the same coefficient field is homothetic: scale $L'$ until
$L'\subset L_\rho$ but $L'\not\subset\varpi L_\rho$; its image modulo $\varpi$ is a nonzero
stable subspace and hence the whole residual space, so Nakayama gives equality.

This uniqueness is local to the distinguished member and depends on residual irreducibility.
It validates retention of the chosen finite-flat quotient system. It does not make the Brauer
positive and negative lattices cancel integrally.

### 11.3 Why characteristic-zero cancellation does not descend integrally

Choose stable lattices $\mathcal R_\lambda^\pm$ in $R_\lambda^\pm$. Equation (5.2) gives a
characteristic-zero isomorphism

$$
R_\lambda^+\simeq r_\lambda\oplus R_\lambda^-.
\tag{11.2}
$$

There is no reason for an isomorphism in (11.2) to carry
$\mathcal R_\lambda^+$ onto a direct sum of a stable rank-two lattice and
$\mathcal R_\lambda^-$. Its matrix can have denominators. The intersection of the rational
summand $r_\lambda$ with $\mathcal R_\lambda^+$ can fail to be a direct summand, and the
quotient can have torsion.

The obstruction is unavoidable when the residue characteristic divides $|\Gamma|$.
Characteristic-zero finite-group representations are semisimple, while their reductions can
have nonsplit extensions. A permutation lattice can contain an invariant line inside its
augmentation submodule after reduction even though the characteristic-zero representation is a
direct sum. Thus equality of integral Grothendieck classes controls composition factors at best;
it does not supply a saturated injection from the negative lattice to the positive lattice.

Consequently no lattice for $r_\lambda$ is defined by “subtracting” induced lattices.

### 11.4 Residual semisimplification

For a fixed rational representation $r_\lambda$, the semisimplification of the reduction of a
stable lattice is independent of the lattice. To see this, scale two lattices until one is
contained in the other and filter their finite quotient by powers of the uniformizer.
Additivity of Jordan--Hölder multiplicities in the successive reduction sequences gives the
same residual simple factors.

Thus

$$
\overline r_\lambda^{\mathrm{ss}}
\tag{11.3}
$$

is attached to the rational member. A nonsplit residual extension is not. Neither the common
characteristic-zero Frobenius polynomials nor strict rational local compatibility chooses such
an extension.

### 11.5 The exact boundary

The present construction proves:

- one rational rank-two representation over every $E_\lambda$;
- a stable lattice for each member;
- the original selected lattice at $\lambda_0$;
- an actual cyclotomic determinant line;
- common rational Frobenius and Weil--Deligne data; and
- lattice-independent residual semisimplification at each fixed $\lambda$.

It does not prove:

- one finite free module over the ring of integers of $E$ whose completions give all members;
- compatible integral projectors for the effective constituent;
- self-duality of an arbitrary stable lattice;
- equality of residual extension classes for different lattices;
- finite-flatness, crystallinity of a selected lattice, or compatible finite locally free
  quotients at a new coefficient prime; or
- the transition maps and local integral structure required by the later fixed-three theory.

These are not missing details of coefficient descent. They are different integral assertions
that rational representation theory cannot see.

## 12. The complete base-field compatible-system theorem

### 12.1 Statement

We now collect the result in a reusable form.

**Theorem 12.1 (complete compatible system over the base field).** Let $\rho$ be the chosen
balanced minimally ramified lift of Book 186, and let $M/\mathbf Q$ and the elementary packets
$\pi_H$ be its controlled potential-automorphy family. Assume the repaired Books 187--188
export, namely the intersection-field identity (2.8), and no stronger conclusion from a later
book.

Then there is a number field $E$, which may be chosen Galois over $\mathbf Q$, a place
$\lambda_0\mid\ell$, and a family

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda)
\qquad(\lambda\in\operatorname{Pl}_f(E))
\tag{12.1}
$$

such that:

1. **Existence and continuity.** Every $r_\lambda$ is continuous, semisimple, and absolutely
   irreducible.
2. **Brauer independence.** Its $E_\lambda$-isomorphism class is independent of the integral
   Brauer relation, its positive-minus-negative presentation, conjugation of its terms, bases,
   coset representatives, packet splitting coordinates, and harmless coefficient enlargement.
3. **Weak compatibility.** For every rational prime $p\notin\{2,\ell\}$ there is
   $P_p(X)=X^2-a_pX+p\in E[X]$ such that, for
   $p\ne q_\lambda$, $r_\lambda$ is unramified at $p$ and has arithmetic-Frobenius polynomial
   $P_p$.
4. **Purity.** Every root of $P_p$ and every coefficient conjugate of that root has complex
   absolute value $p^{1/2}$.
5. **Determinant and duality.** For every $\lambda$,

   $$
   \det r_\lambda=\chi_\lambda,
   \qquad
   r_\lambda^\vee\simeq r_\lambda\otimes\chi_\lambda^{-1}.
   $$

6. **Strict compatibility.** For every finite $p$ there is an algebraic rank-two
   Frobenius-semisimple Weil--Deligne pair $D_p$ over $E$ such that

   $$
   \operatorname{WD}_p(r_\lambda)^{\mathrm{F\!-\!ss}}
   \simeq D_p\otimes_EE_\lambda
   $$

   whenever $p\ne q_\lambda$. The pair is unramified with polynomial $P_p$ for
   $p\notin\{2,\ell\}$; at $2$ it has zero monodromy, trivial wild inertia, and primitive
   tame order-three type.
7. **Local invariants.** Away from coefficient characteristic, local Euler polynomials, Artin
   and Swan conductors, monodromy ranks, and epsilon factors with fixed auxiliary
   normalizations are independent of $\lambda$.
8. **Original member.** In a finite common $\ell$-adic overfield,

   $$
   r_{\lambda_0}\simeq\rho.
   $$

   The selected lattice of $\rho$, its finite-flat quotient system at $\ell$, its dyadic type,
   and its unramified local records are retained.
9. **Coefficient covariance.** Coefficient conjugation applies to $a_p$, $D_p$, and the member
   at the conjugate place together. Finite enlargement of $E$ gives exactly the scalar-extended
   family.
10. **Integral boundary.** Every $r_\lambda$ has a stable lattice, but no coherent global
    lattice, integral Brauer cancellation, new finite-flat quotient system, or canonical
    residual extension is asserted.

The family (12.1) is therefore the global compatible family over the base field
$\mathbf Q$. It is a family of actual rank-two representations, not a virtual family, and it
is defined over completions of one number field, not merely over unrelated algebraic closures.

### 12.2 Proof

Proposition 2.2 gives a prime-cyclic subnormal chain from every Mackey intersection to either
elementary group containing it. Prime-cyclic base change through the reversed fixed-field tower
and the extending representation identify the endpoint with the selected intersection packet.
This proves the repaired overlap identity without using effectivity or this book's coefficient
descent.

Choose one number field containing the finite elementary packet, Brauer character, intersection,
and local-type ledgers. Lemma 3.1 globalizes the distinguished local coefficient field, and the
finite common-field theorem of Book 137 supplies $E_\lambda$-models for all elementary packet
systems. Finite induction constructs the actual positive and negative representations
$R_\lambda^\pm$ over every completion.

The repaired overlap makes the Mackey Gram matrix coefficient independent. At the distinguished
embedding the signed class is the original absolutely irreducible $\rho$, so its norm is one.
The integral norm-one argument of Book 188 makes the signed class one absolutely irreducible
rank-two representation after scalar extension to an algebraic closure.

Theorem 4.2 then supplies the step not contained in effectivity alone. Since that constituent
has coefficient one inside a virtual difference defined over $E_\lambda$, its Galois orbit and
Schur multiplicity are both one. It descends to $E_\lambda$, actual cancellation holds over the
completion, and Proposition 5.2 proves continuity. Applying the combined Gram calculation to
two Brauer relations and then descending the resulting isomorphism proves the full independence
statement.

Local cyclic-block determinants and the distinguished tensor identity give the polynomials
$P_p$ in $E[X]$. Actual cancellation gives unramifiedness and makes these polynomials the
characteristic polynomials of $r_\lambda$. Restriction to the pure top packet proves weight-one
purity. The determinant-transfer calculation becomes the actual determinant after effectivity,
and two-dimensional exterior algebra gives duality. At $\lambda_0$, uniqueness of the effective
constituent identifies the member with $\rho$.

For local compatibility, form the algebraic local Mackey objects from the strictly compatible
elementary packet pairs. Global cancellation restricts locally, and Krull--Schmidt cancellation
extracts one rank-two complement independent of the coefficient place. A finite enlargement
descends the finitely many bad complements to $E$; good complements are already defined by
$P_p$. This proves strict compatibility and independence of local invariants. Comparison at the
distinguished member removes every auxiliary bad prime other than $2$ and $\ell$. Complete
splitting at $2$ identifies the common dyadic pair directly.

Finally, compactness supplies a stable lattice to each member, while Chapter 11 proves that no
integral cancellation follows. All ten clauses are established. $\square$

### 12.3 Dependency and interface audit

The proof uses exactly the four direct prerequisites assigned to this book.

| Source | Imported interface | Use here | Boundary retained |
|---|---|---|---|
| Book 137 | common realization fields; weak and strict compatible systems of weight-two packets; determinant, purity, local Weil--Deligne data; scalar and embedding transport; stable-lattice boundary | models for every elementary packet over $E_\lambda$, algebraic good polynomials and bad local pairs, purity | no canonical integral packet summand or coefficient-prime finite-flat conclusion is imported |
| Book 186 | the fixed $\rho$ and its lattice; controlled Galois top $M$; selected elementary packets; conjugation, cyclic descent, local completions, and identification with restrictions of $\rho$ | distinguished member, overlap selection, removal of auxiliary bad primes, exact dyadic and $\ell$-adic records | no Books 187--189 result is used inside its construction |
| Book 187, repaired | integral Brauer relation; induced virtual family; tensor identity at $\lambda_0$; determinant transfer; common Frobenius rational function; local Mackey record; lattice warning | construction of $R_\lambda^\pm$, virtual determinant and polynomials, local algebraic presentation | virtual equality is not called effectivity or integral cancellation |
| Book 188, repaired | Hom-norm and Gram invariance on elementary intersections; norm-one effectivity; actual local cancellation; relation-independence after scalar extension; Brauer--Nesbitt recognition | existence and absolute irreducibility over algebraic closures, comparison of two relations | effectivity is not called coefficient descent or a compatible family |

The only defect explicitly reported by the current drafts of Books 187--188 is the
intersection-field overlap. Chapter 2 verifies the intended repair from their existing
prime-cyclic interfaces: elementary groups are nilpotent, their subgroups are subnormal, and
the subnormal chain refines to cyclic prime-order quotients. Thus the overlap is not an extra
hypothesis on the arithmetic representation and does not require a new dependency.

Book 137 uses geometric Frobenius in its displayed general theory, whereas Books 186--188 use
arithmetic Frobenius in the chosen-lift spine. This book translates once and consistently uses
arithmetic Frobenius. The determinant $\chi_\lambda$ therefore takes $\operatorname{Frob}_p$
to $p$, and weight one means roots of absolute value $p^{1/2}$.

No density theorem is used to prove effectivity, relation-independence, overlap compatibility,
or coefficient descent. Strong multiplicity one is used only between already existing
automorphic packets on the same elementary field. No nonsolvable automorphic induction from an
elementary fixed field to $\mathbf Q$ is asserted; induction across the bottom is Galois and
Weil-group induction.

### 12.4 Hostile failure audit

We finish by testing the construction against the shortcuts most likely to invalidate it.

**Top-field equality is not overlap equality.** Restriction to $G_M$ forgets characters of the
finite quotient $D$. The repair uses a prime-cyclic tower to identify the packet on $F_D$;
it does not infer the identity from top restriction alone.

**Virtual polynomiality is not existence.** The rational Brauer determinant becomes a
quadratic polynomial at every coefficient embedding before an actual member is known. The
character norm, not the polynomial degree, proves effectivity.

**Effectivity over an algebraic closure is not coefficient descent.** A Galois-stable
irreducible can have nontrivial Schur index. Theorem 4.2 kills that index using the coefficient
one in an $E_\lambda$-defined virtual difference.

**Relation-independent Frobenius is not relation-independent representation theory.** Two
relations are compared by one combined Mackey Gram matrix. Norm zero gives equality of the full
semisimple classes, and Lemma 4.3 descends the isomorphism to $E_\lambda$.

**Global cancellation is not local identification by traces.** The actual global direct-sum
isomorphism restricts to decomposition groups. Weil--Deligne functoriality and Krull--Schmidt
cancellation retain inertia and monodromy. Conductor equality is a consequence, not a
substitute.

**Auxiliary ramification does not vanish term by term.** It vanishes from the common effective
local complement because the distinguished member is unramified. No assertion is made about a
map between the ramified positive and negative integral summands.

**A completion model is not a global matrix representation over $E$.** A compatible system
requires $E_\lambda$-models indexed by places and common algebraic local data. It does not
require one two-dimensional $E$-vector space carrying a continuous action of $G_{\mathbf Q}$.

**A stable lattice is not an integral compatible system.** Compactness gives existence at each
place. It does not give compatible projectors, saturation, self-duality, finite-flatness, or
transition maps. None of the integral theory of the next book has been imported.

Every implication used in Theorem 12.1 survives these tests.

### 12.5 Conclusion

The elementary-field systems have now become one system over the base field. The route was
necessarily indirect. The nonsolvable top prevented ordinary descent, so Brauer induction
replaced descent by a signed expression. Mackey theory exposed the exact intersection fields on
which its character norm had to be computed. The nilpotence of elementary groups supplied the
missing prime-cyclic towers to those intersections, making the norm calculation unconditional.
Norm one then turned the signed character into one irreducible rank-two member at every
coefficient embedding.

That was still not enough. A compatible family needs coefficient fields, not only algebraic
closures. The effective constituent occurred with multiplicity one in a virtual class already
defined over $E_\lambda$. Galois orbits and Schur indices multiply geometric multiplicities;
neither can divide one except trivially. This forced descent to the completion itself and made
the member independent of the embedding used to display it.

The resulting family is therefore honest in every rational sense:

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda),
\qquad
\det r_\lambda=\chi_\lambda,
\tag{12.2}
$$

with common pure polynomials

$$
X^2-a_pX+p
\tag{12.3}
$$

and common local Weil--Deligne pairs away from the varying coefficient prime. It is independent
of the Brauer decomposition, covariant under coefficient conjugation, unchanged by harmless
field enlargement, and contains the original chosen lift with its original lattice.

The final boundary is integral and deliberate. The rational constituent has stable lattices,
but the Brauer subtraction supplies no saturated integral complement and no coherent family of
finite locally free quotients. Virtual equality, semisimple effectivity, coefficient descent,
compatible-family assembly, and integral structure have remained separate at every step.

With the single intersection-field repair of Books 187--188 made as proved in Chapter 2, the
dependency and interface audit is **READY**.
