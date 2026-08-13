# Compatible Systems over the Base Field

## Contents

1. [From effective members to an arithmetic family](#1-from-effective-members-to-an-arithmetic-family)
   - [The assembly problem](#11-the-assembly-problem)
   - [The exact input from the packet and effectivity theorems](#12-the-exact-input-from-the-packet-and-effectivity-theorems)
   - [The theorem to be proved](#13-the-theorem-to-be-proved)
   - [Conventions and logical boundaries](#14-conventions-and-logical-boundaries)
   - [The order of construction](#15-the-order-of-construction)
2. [One algebraic coefficient ledger](#2-one-algebraic-coefficient-ledger)
   - [Trace fields, realization fields, and places](#21-trace-fields-realization-fields-and-places)
   - [Simultaneous models for the elementary packets](#22-simultaneous-models-for-the-elementary-packets)
   - [The induced positive and negative representations](#23-the-induced-positive-and-negative-representations)
   - [The imported overlap theorem](#24-the-imported-overlap-theorem)
   - [Why no base-field family has been assumed](#25-why-no-base-field-family-has-been-assumed)
3. [Multiplicity-one coefficient descent](#3-multiplicity-one-coefficient-descent)
   - [The Schur obstruction](#31-the-schur-obstruction)
   - [Orbit and Schur multiplicities](#32-orbit-and-schur-multiplicities)
   - [Descent from a signed equality](#33-descent-from-a-signed-equality)
   - [Cocycle effectivity](#34-cocycle-effectivity)
   - [Effectivity on coefficient overlaps](#35-effectivity-on-coefficient-overlaps)
4. [Construction at every coefficient place](#4-construction-at-every-coefficient-place)
   - [The descended member](#41-the-descended-member)
   - [Continuity and absolute irreducibility](#42-continuity-and-absolute-irreducibility)
   - [Independence of the displaying embedding](#43-independence-of-the-displaying-embedding)
   - [Scalar extension](#44-scalar-extension)
   - [What coherence does and does not mean](#45-what-coherence-does-and-does-not-mean)
5. [Independence of the Brauer relation](#5-independence-of-the-brauer-relation)
   - [Two relations in one ledger](#51-two-relations-in-one-ledger)
   - [The norm-zero comparison](#52-the-norm-zero-comparison)
   - [Descent of the comparison isomorphism](#53-descent-of-the-comparison-isomorphism)
   - [Presentation, conjugate-term, and coordinate independence](#54-presentation-conjugate-term-and-coordinate-independence)
   - [The intrinsic member](#55-the-intrinsic-member)
6. [Restriction recovery and the two conjugation actions](#6-restriction-recovery-and-the-two-conjugation-actions)
   - [Restricting the signed expression](#61-restricting-the-signed-expression)
   - [Recovery on every elementary fixed field](#62-recovery-on-every-elementary-fixed-field)
   - [Recovery over the controlled top](#63-recovery-over-the-controlled-top)
   - [Field conjugation](#64-field-conjugation)
   - [Coefficient conjugation](#65-coefficient-conjugation)
7. [Common Frobenius polynomials, determinant, and purity](#7-common-frobenius-polynomials-determinant-and-purity)
   - [The algebraic quadratic polynomial](#71-the-algebraic-quadratic-polynomial)
   - [Unramifiedness of the descended constituent](#72-unramifiedness-of-the-descended-constituent)
   - [Weak compatibility](#73-weak-compatibility)
   - [The actual determinant and duality](#74-the-actual-determinant-and-duality)
   - [Weight-one purity](#75-weight-one-purity)
   - [Frobenius powers after restriction](#76-frobenius-powers-after-restriction)
8. [Local effectivity and the SP record at two](#8-local-effectivity-and-the-sp-record-at-two)
   - [The algebraic local Mackey class](#81-the-algebraic-local-mackey-class)
   - [An effective local complement](#82-an-effective-local-complement)
   - [The proved strong-compatibility range](#83-the-proved-strong-compatibility-range)
   - [The common special pair](#84-the-common-special-pair)
   - [Monodromy line, sign, and conductor](#85-monodromy-line-sign-and-conductor)
   - [Identification of the chosen SP member](#86-identification-of-the-chosen-sp-member)
   - [The integral boundary](#87-the-integral-boundary)
9. [The complete base-field assembly theorem](#9-the-complete-base-field-assembly-theorem)
   - [Statement](#91-statement)
   - [Proof](#92-proof)
   - [The exact interface to prime switching](#93-the-exact-interface-to-prime-switching)
10. [Dependency, hostile, and final audits](#10-dependency-hostile-and-final-audits)
    - [Dependency audit](#101-dependency-audit)
    - [Hostile mathematical audit](#102-hostile-mathematical-audit)
    - [Scope and format audit](#103-scope-and-format-audit)
    - [Conclusion](#104-conclusion)

## 1. From effective members to an arithmetic family

### 1.1 The assembly problem

The preceding two books begin with one representation over the ground field and an automorphic
packet only after restriction to a controlled totally real Galois extension. Book 183 replaces
the unavailable nonsolvable descent by a finite array over elementary fixed fields. It then
forms, for each coefficient embedding, a signed sum of actual induced representations. Book
184 proves, under its explicit coefficient-two hypothesis $(\mathrm{AI}_2)$, that the signed
class has norm one and positive dimension two at every coefficient embedding. Consequently it
is represented by one actual absolutely irreducible rank-two representation over an
algebraically closed nonarchimedean field. Without $(\mathrm{AI}_2)$, this effectivity statement
is available only away from coefficient residue characteristic two.

That conclusion is pointwise effectivity. It is not yet the standard object called a compatible
system. A compatible system is indexed by the finite places of one number field. Its member at
a place $\lambda$ must have a model over the completion at that place, and its Frobenius and
local records must be algebraic before completion. In contrast, an embedding-indexed member

$$
r_{\mathfrak B,\tau}:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\Omega_\tau)
\tag{1.1}
$$

initially lives only over an algebraically closed field $\Omega_\tau$. Invariance of its trace
under automorphisms of $\Omega_\tau$ does not alone give matrices over a smaller completion.
The familiar obstruction is a Schur class: the trace can be rational while the representation
is defined only over a division algebra.

There is a second coherence problem. Different Brauer relations give different positive and
negative presentations. Book 184 proves that their effective members agree after scalar
extension, but a compatible-system construction must show that the descended models agree over
the completion itself. Likewise, two embeddings inducing the same coefficient place must be
recognized as two displays of one member rather than as two separately chosen representations.

This book solves precisely those assembly problems. Its key input is stronger than trace
invariance: the effective constituent occurs with multiplicity one in a difference of two
semisimple representations already defined over the completion. Galois orbits and Schur
indices multiply geometric multiplicities. Since neither can divide one nontrivially, the
coefficient cocycle is effective and the constituent descends.

### 1.2 The exact input from the packet and effectivity theorems

We begin with the **controlled SP top datum** of Book 183. It includes a prime $\ell\geq7$, a
finite extension $L_0/\mathbf Q_\ell$, and a continuous absolutely irreducible representation

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(L_0)
\tag{1.2}
$$

such that

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ is unramified outside }\{2,\ell\}.
\tag{1.3}
$$

There is a finite totally real Galois extension $M/\mathbf Q$ with

$$
\Gamma=\operatorname{Gal}(M/\mathbf Q),
\tag{1.4}
$$

the primes $2$ and $\ell$ split completely in $M$, and $\rho|_{G_M}$ is absolutely
irreducible. The selected top packet over $M$ realizes this restriction at one distinguished
coefficient embedding. This controlled SP top datum is an explicit hypothesis of the present
assembly theorem. The current Book 182 does not construct it unconditionally: that book isolates
a missing controlled exact SP residual seed and the bridge-readiness data needed to carry the
chosen lift to the controlled top. Thus the arguments below prove the rational assembly once
the datum has been supplied; they do not close those upstream arithmetic gaps.

For every elementary subgroup $H\leq\Gamma$, put

$$
F_H=M^H.
\tag{1.5}
$$

Book 183 constructs a selected parallel-weight-two cuspidal packet $\pi_H$ over $F_H$, together
with its embedding-indexed rank-two realizations $r_{H,\tau}$. These are packet systems over the
elementary fields, not members of a family over $\mathbf Q$. At the distinguished embedding
$\tau_0$,

$$
r_{H,\tau_0}\simeq\rho|_{G_{F_H}}.
\tag{1.6}
$$

The packet array is compatible with field conjugation and coefficient conjugation. Most
importantly, Book 183 proves the exact elementary-overlap theorem. If $D\leq H$ are elementary,
then for every coefficient embedding

$$
\left(r_{H,\tau}|_{G_{F_D}}\right)^{\mathrm{ss}}
\simeq r_{D,\tau}.
\tag{1.7}
$$

For two elementary groups $H,J$ and $x\in\Gamma$, the corresponding statement holds over

$$
F_{H\cap xJx^{-1}}=F_H\,x(F_J).
\tag{1.8}
$$

This theorem already covers nonnormal intersection fields. Its proof in Book 183 uses the
correct residue-degree Frobenius comparison and recognition of two already existing packet
representations. It does not assert that every group-theoretic prime-cyclic tower is
automorphically admissible. Equation (1.7) is an imported proved theorem; this book neither
reconstructs it nor replaces it by an automatic solvable-descent claim.

Book 184's all-place effectivity theorem has one further hypothesis that is not contained in
the controlled SP top datum. Write $q(\tau)$ for the residue characteristic of the
nonarchimedean target of $\tau$. We retain explicitly the hypothesis

$$
\boxed{
r_{1,\tau}:G_M\longrightarrow\operatorname{GL}_2(\Omega_\tau)
\text{ is absolutely irreducible whenever }q(\tau)=2.}
\tag{$\mathrm{AI}_2$}
$$

This is a rational characteristic-zero hypothesis about the coefficient-two realization of the
top packet. Book 183 does not prove it: its prime-to-coefficient SP pair proves the required
irreducibility only when $q(\tau)\ne2$. Under $(\mathrm{AI}_2)$, Book 184 proves effectivity at
every embedding. Without it, Book 184 and the construction below apply only at places of
residue characteristic different from two and do not produce an all-finite-place compatible
system. Thus $(\mathrm{AI}_2)$ is a standing hypothesis whenever this book says ``every
coefficient place.''

The name “all-place” must not obscure the logical role of this hypothesis. The elementary
top-packet realization at a place above two already exists and is continuous and semisimple;
$(\mathrm{AI}_2)$ asserts its characteristic-zero absolute irreducibility. It is used in Book
184 to make the coefficient-two Mackey Gram calculation effective, after which this book
descends the surviving constituent to the completion. It is not a scalar-extension map from an
odd completion, a coefficient-prime local--global compatibility theorem, or a statement about
the reduction of any lattice. Book 184 records the exact relation-specific norm-one gate
$(\mathrm N_2(\mathfrak B))$, the structured finite Hom condition
$(\mathrm G_2(\mathfrak B))$ used to prove it, and the sufficient but presently missing
coefficient-prime SP comparison $(\mathrm{CP\!\!-SP}_2)$.

Fix for the moment an integral Brauer relation

$$
\mathfrak B=\{(H_i,\theta_i,n_i)\}_{i=1}^t,
\qquad
1_\Gamma=\sum_i n_i\operatorname{Ind}_{H_i}^{\Gamma}\theta_i,
\tag{1.9}
$$

where every $H_i$ is elementary, every $\theta_i$ is a finite-order linear character, and
$n_i\in\mathbf Z$. Book 183 forms the signed induced class. Under $(\mathrm{AI}_2)$, Book 184
proves that, at every coefficient embedding $\tau$, it is represented by an actual continuous
absolutely irreducible two-dimensional representation (1.1). It also proves
relation-independence after scalar extension, common good Frobenius polynomials, the cyclotomic
determinant, exact local characteristic-zero cancellation, and recovery of $\rho$ at $\tau_0$.

No family over $\mathbf Q$ is included in this input. No stable lattice is included either.
The objects to be assembled are exactly the effective embedding-indexed isomorphism classes
(1.1).

### 1.3 The theorem to be proved

Under the standing controlled-datum and $(\mathrm{AI}_2)$ hypotheses, the endpoint can now be
stated informally. We shall construct a finite Galois number field $E$, a distinguished place
$\lambda_0\mid\ell$, and, for every finite place $\lambda$ of $E$, an absolutely irreducible
continuous representation

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda).
\tag{1.10}
$$

After scalar extension to an algebraic closure, this is the effective member of Book 184. The
isomorphism class over $E_\lambda$ will be independent of the Brauer relation and every
auxiliary display.

Outside one finite set $S$, there will be polynomials

$$
P_p(X)=X^2-a_pX+p\in E[X]
\tag{1.11}
$$

such that $r_\lambda$ is unramified at $p\ne\ell(\lambda)$ and has arithmetic-Frobenius
polynomial $P_p$. Their roots will be pure of weight one, and

$$
\det r_\lambda=\chi_{\ell(\lambda)}.
\tag{1.12}
$$

Restriction to every elementary fixed field will recover its packet member. Coefficient and
field conjugation will retain their distinct, correct meanings. At the distinguished place,
$r_{\lambda_0}$ will recover the chosen representation $\rho$ after one common scalar
extension.

At the rational prime $2$, the family carries one algebraic SP pair. For every coefficient
place away from $2$, its scalar extension is the full Frobenius-semisimple Weil--Deligne pair
of $r_\lambda|_{G_{\mathbf Q_2}}$. Its monodromy is nonzero of rank one, its named line and
sign are retained, and its conductor exponent is one. These are rational local data. Choosing
an integral lattice and constructing a compatible quotient tower are deliberately not part of
the theorem.

### 1.4 Conventions and logical boundaries

Arithmetic Frobenius is used throughout. Therefore

$$
\chi_{\ell(\lambda)}(\operatorname{Frob}_p)=p
\tag{1.13}
$$

when $p\ne\ell(\lambda)$, and the reciprocal characteristic series associated with (1.11) is

$$
1-a_pT+pT^2.
\tag{1.14}
$$

All global characteristic-zero representations are semisimple. The final members are
absolutely irreducible. Finite Galois induction is unnormalized. A Frobenius-semisimple
Weil--Deligne pair always retains finite inertia and its nilpotent operator $N$.

The following stages are distinct:

$$
\begin{array}{c}
\text{elementary-field packet systems}
\\ \Downarrow\ \text{Brauer induction}
\\ \text{signed base-field classes}
\\ \Downarrow\ \text{character-norm effectivity}
\\ \text{effective members over algebraically closed local fields}
\\ \Downarrow\ \text{multiplicity-one coefficient descent}
\\ \text{members over the completions of one number field}
\\ \Downarrow\ \text{common algebraic records}
\\ \text{the base-field compatible system.}
\end{array}
\tag{1.15}
$$

No arrow in (1.15) is an integral arrow. In particular, characteristic-zero cancellation does
not choose a saturated integral complement. The later integral theory must start by choosing a
lattice in one selected member and must prove its own local properties.

We use neither the changing-prime theorem nor the fixed-three integral theorem. Those books are
consumers of the family constructed here. The compatible family is never assumed in a
hypothesis of its own construction.

### 1.5 The order of construction

Chapter 2 places all elementary packet systems and finite Brauer characters in one algebraic
ledger. This makes the positive and negative induced representations actual objects over each
completion $E_\lambda$. Chapter 3 proves the multiplicity-one descent theorem and interprets it
as effectivity of the coefficient cocycle. Chapter 4 applies the theorem place by place and
proves continuity.

Chapter 5 compares two Brauer relations by one combined Mackey Gram matrix and descends the
resulting comparison to $E_\lambda$. Chapter 6 proves the stronger restriction-recovery
identity using Mackey theory and the already proved elementary-overlap theorem. Chapters 7--8
assemble the global and local algebraic records, including the complete SP object at $2$.
Chapter 9 states the final theorem, and Chapter 10 subjects the construction to the two review
rubrics and the main hostile failure tests.

## 2. One algebraic coefficient ledger

### 2.1 Trace fields, realization fields, and places

The coefficient field of a polynomial and a field over which matrices exist are not the same
notion. For a packet $\pi_H$, its good Hecke polynomials generate an intrinsic field of
rationality. A chosen simple packet factor can nevertheless have a nontrivial endomorphism
algebra, and a finite local type can require a splitting field. Calling the trace field a field
of definition without checking these algebras would merely move the Schur problem into the
hypotheses.

There are only finitely many elementary subgroups of the finite group $\Gamma$. There are also
only finitely many linear characters of all of those groups. Book 183 already chooses a common
number field containing their values and the algebraic good and local packet data. Enlarge that
field once to split every finite-dimensional coefficient algebra used to realize every
elementary packet and every elementary intersection packet. Take its normal closure over
$\mathbf Q$ and call the result $E$.

This is a finite enlargement because the packet array is finite. It is deliberately made before
a Brauer relation is selected. Consequently two relations can later be compared inside the same
ledger, rather than by choosing a new coefficient field for each relation.

A finite place $\lambda$ of $E$ is the correct index. Write

$$
E_\lambda=\widehat E^{\,\lambda},
\qquad
q_\lambda=\ell(\lambda).
\tag{2.1}
$$

Several places may lie above the same rational prime, and their completions need not be
canonically isomorphic. An embedding $E\hookrightarrow\overline{\mathbf Q}_{q_\lambda}$
induces $\lambda$ precisely when it extends continuously to $E_\lambda$. Thus an embedding is
a display of the place, not a replacement for it.

The distinguished algebraic embedding from Book 183 induces a place
$\lambda_0\mid\ell$. The two local fields $E_{\lambda_0}$ and $L_0$ embed in one finite
extension of $\mathbf Q_\ell$. No assertion that they are equal is needed.

### 2.2 Simultaneous models for the elementary packets

The packet attachment theorem, already applied term by term in Book 183, gives compatible
coefficient systems for the finitely many $\pi_H$. Because $E$ splits their realization
algebras, every elementary $H$ and every finite place $\lambda$ of $E$ have a model

$$
r_{H,\lambda}:G_{F_H}\longrightarrow\operatorname{GL}_2(E_\lambda)
\tag{2.2}
$$

whose scalar extension under an embedding inducing $\lambda$ is $r_{H,\tau}$. These are
continuous semisimple representations. Under the standing $(\mathrm{AI}_2)$ hypothesis they
are absolutely irreducible. More precisely, Book 184, Proposition 5.1 proves this from the
nonzero SP monodromy when $q_\lambda\ne2$, and from $(\mathrm{AI}_2)$ together with top-field
restriction when $q_\lambda=2$. Cuspidality and good Frobenius polynomials alone are not used as
a proof of Galois irreducibility.

If $D\leq H$ are elementary, equation (1.7) becomes, after scalar extension,

$$
r_{H,\lambda}|_{G_{F_D}}^{\mathrm{ss}}
\otimes_{E_\lambda}\overline E_\lambda
\simeq
r_{D,\lambda}\otimes_{E_\lambda}\overline E_\lambda.
\tag{2.3}
$$

Both sides are absolutely irreducible after restriction in the cases used below, and in all
cases their semisimple classes are already the exact overlap classes needed by Mackey theory.
Chapter 6 will show that the relevant comparisons descend over $E_\lambda$ whenever an actual
isomorphism over the completion is required.

For a finite-order character $\theta:H\to E^\times$, inflate it through

$$
G_{F_H}/G_M\simeq H.
\tag{2.4}
$$

Its $\lambda$-adic avatar $\theta_\lambda$ is an $E_\lambda$-valued continuous character. It
is trivial on $G_M$. Although global reciprocity also gives a finite-order Hecke avatar, the
construction in this book uses only its Galois avatar.

### 2.3 The induced positive and negative representations

For the relation (1.9), put

$$
A_{i,\lambda}
=
\operatorname{Ind}_{G_{F_{H_i}}}^{G_{\mathbf Q}}
(r_{H_i,\lambda}\otimes\theta_{i,\lambda}).
\tag{2.5}
$$

This is actual finite Galois induction. It is defined over $E_\lambda$: in a coset basis, its
matrices consist of packet matrices, permutation blocks, and the values of $\theta_i$. There is
no automorphic induction from the generally nonnormal field $F_{H_i}$ to $\mathbf Q$ in this
statement.

Write $n_i=n_i^+-n_i^-$ with $n_i^\pm\geq0$ and define

$$
R_{\mathfrak B,\lambda}^+
=\bigoplus_i A_{i,\lambda}^{\oplus n_i^+},
\qquad
R_{\mathfrak B,\lambda}^-
=\bigoplus_i A_{i,\lambda}^{\oplus n_i^-}.
\tag{2.6}
$$

Both are actual continuous semisimple $E_\lambda$-representations. To see semisimplicity, first
restrict an induced term to the normal open subgroup $G_M$. Normal-subgroup Mackey decomposition
makes that restriction a finite direct sum of conjugates of the semisimple top packet member.
If a $G_{\mathbf Q}$-stable subspace is given, choose a $G_M$-equivariant projection and average
its conjugates over the finite quotient $\Gamma$. Characteristic zero permits division by
$|\Gamma|$, producing a $G_{\mathbf Q}$-equivariant complement.

For an embedding $j:E_\lambda\hookrightarrow\Omega$ into an algebraically closed
nonarchimedean field, Book 184 gives an absolutely irreducible rank-two representation
$S_{\mathfrak B,\lambda,j}$ such that

$$
[R_{\mathfrak B,\lambda}^+\otimes_j\Omega]
-[R_{\mathfrak B,\lambda}^-\otimes_j\Omega]
=[S_{\mathfrak B,\lambda,j}].
\tag{2.7}
$$

This is the multiplicity-one signed equality from which coefficient descent will be proved.

### 2.4 The imported overlap theorem

The norm calculation behind (2.7) compares two induced summands on a field

$$
L_x=M^{H_i\cap xH_jx^{-1}}.
\tag{2.8}
$$

Book 183 identifies both untwisted restrictions there with the packet attached to
$D_x=H_i\cap xH_jx^{-1}$. After the Brauer characters are restored, the Hom space becomes

$$
\operatorname{Hom}_{G_{L_x}}
(r_{D_x,\tau},r_{D_x,\tau}\otimes\delta_{ij,x,\tau}),
\tag{2.9}
$$

where the orientation is

$$
\delta_{ij,x}
=({}^x\theta_j)|_{D_x}\,(\theta_i|_{D_x})^{-1}.
\tag{2.10}
$$

Book 184 proves that the dimension of (2.9) is the coefficient-independent indicator of an
actual finite-order automorphic self-twist. These entrywise identities make the entire Mackey
Gram matrix independent of the coefficient embedding.

This exact interface matters twice in the present book: it underlies relation-independence in
Chapter 5, and it gives restriction recovery in Chapter 6. We do not infer (2.9) merely from
agreement over $G_M$. Such an inference would lose a quotient character of $D_x$.

Nor do we declare every prime-cyclic subgroup chain to be an admissible automorphic transfer
chain. Elementary nilpotence supplies a group-theoretic chain, but arithmetic admissibility is
separate. Book 183's proved tower-independent semisimple overlap theorem is what closes the
interface, relative throughout to the conditional controlled SP top datum.

### 2.5 Why no base-field family has been assumed

Every object constructed so far has one of three forms:

- a packet system $r_{H,\lambda}$ on $G_{F_H}$;
- an induced representation $A_{i,\lambda}$ on $G_{\mathbf Q}$; or
- an embedding-indexed effective constituent $S_{\mathfrak B,\lambda,j}$ over an algebraic
  closure.

The first objects come from already existing automorphic packets over elementary fields. The
second are ordinary finite inductions. The third are conclusions of the norm-one theorem. None
is a family of rank-two representations on $G_{\mathbf Q}$ indexed by the places of $E$.

This distinction prevents a circular shortcut. One cannot say that the
$S_{\mathfrak B,\lambda,j}$ are compatible and then use compatibility to descend them. The descent will come
from the signed equality (2.7), and compatibility will be proved afterward from algebraic
Frobenius and local records.

## 3. Multiplicity-one coefficient descent

Book 180, Section 7.4 is the general source for orbit/Schur multiplicities, the coefficient
factor set, and multiplicity-one descent. This chapter instantiates that theorem in the one
completion-valued signed equality furnished by the SP packet array.

### 3.1 The Schur obstruction

An absolutely irreducible $\overline k$-representation fixed up to isomorphism by
$\operatorname{Aut}(\overline k/k)$ need not have a $k$-model. Semilinear intertwiners have a
scalar factor set

$$
c(\sigma,\tau)=u_\sigma\,{}^\sigma u_\tau\,u_{\sigma\tau}^{-1}. \tag{3.1}
$$

Book 180 explains why this coefficient-field obstruction is distinct from the Clifford
obstruction for extending a representation across a quotient of arithmetic groups.

### 3.2 Orbit and Schur multiplicities

The scalar extension of a simple $k$-module has the form

$$
(T\otimes_k\overline k)^{\mathrm{ss}}
\simeq m\bigoplus_{S'\in\mathcal O}S', \tag{3.2}
$$

where $\mathcal O$ is one Galois orbit and $m$ is its Schur multiplicity. Consequently any
integral virtual class defined over $k$ has coefficients constant on each orbit and divisible by
the corresponding $m$.

### 3.3 Descent from a signed equality

We use the following result exactly as proved in Book 180.

**Theorem 3.2 (multiplicity-one coefficient descent; Book 180, Theorem 7.4).** If $V^+,V^-$
are semisimple $k$-representations and

$$
[V^+\otimes_k\overline k]-[V^-\otimes_k\overline k]=[S] \tag{3.4}
$$

for one absolutely irreducible $S$, then $S$ has a unique absolutely irreducible $k$-model
$V$, and

$$
V^+\simeq V\oplus V^-. \tag{3.6}
$$

In the SP application take $k=E_\lambda$ and
$V^\pm=R_{\mathfrak B,\lambda}^\pm$. Book 184 supplies (3.4) after embedding
$E_\lambda$ into an algebraic closure, while Chapter 2 ensures both signed terms are already
defined over $E_\lambda$. Therefore the coefficient-one constituent descends over the desired
completion itself; no trace-field shortcut is used.

### 3.4 Cocycle effectivity

The coefficient one in (3.4) forces its Galois orbit to be a singleton and its Schur
multiplicity to be one. Equivalently, the class of (3.1) vanishes, so the intertwiners may be
rescaled to satisfy

$$
u_{\sigma\tau}=u_\sigma\,{}^\sigma u_\tau. \tag{3.8}
$$

This proves existence of the completion-valued isomorphism class, not a preferred basis or a
canonical family of matrices.

### 3.5 Effectivity on coefficient overlaps

The same Book 180 theorem is stable under finite scalar extension. If two realization fields or
two displays of one completion are embedded in a common overfield, both descended models become
the scalar extension of the unique $E_\lambda$-model. The underlying Hom-base-change identity
is

$$
\operatorname{Hom}_G(V_1,V_2)\otimes_k k'
\simeq\operatorname{Hom}_G(V_1\otimes k',V_2\otimes k'). \tag{3.9}
$$

Thus coefficient-place overlap is a consequence of multiplicity one. It is logically different
from Book 183's elementary-field overlap theorem, which is an input to the Gram calculation
before effectivity.

## 4. Construction at every coefficient place

### 4.1 The descended member

Fix a finite place $\lambda$ of $E$. Apply Theorem 3.2 to (2.7) with

$$
k=E_\lambda,
\qquad
V^\pm=R_{\mathfrak B,\lambda}^\pm.
\tag{4.1}
$$

**Definition 4.1.** The **descended effective member** associated with $\mathfrak B$ at
$\lambda$ is the unique representation

$$
r_{\mathfrak B,\lambda}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(E_\lambda)
\tag{4.2}
$$

for which

$$
R_{\mathfrak B,\lambda}^+
\simeq
r_{\mathfrak B,\lambda}\oplus R_{\mathfrak B,\lambda}^-.
\tag{4.3}
$$

For every embedding $j:E_\lambda\hookrightarrow\Omega$ into an algebraically closed field,

$$
r_{\mathfrak B,\lambda}\otimes_j\Omega
\simeq S_{\mathfrak B,\lambda,j}.
\tag{4.4}
$$

Equation (4.3) is stronger than an equality in a Grothendieck group. It is a noncanonical
direct-sum isomorphism over the completion itself. The representation (4.2), however, is unique
up to $E_\lambda$-linear isomorphism.

### 4.2 Continuity and absolute irreducibility

**Proposition 4.2.** The representation $r_{\mathfrak B,\lambda}$ is continuous and
absolutely irreducible.

**Proof.** It is a $G_{\mathbf Q}$-stable direct summand of the continuous representation
$R_{\mathfrak B,\lambda}^+$. A finite-dimensional linear subspace of a nonarchimedean vector
space is closed. Restricting the continuous action on $R_{\mathfrak B,\lambda}^+$ to that
closed stable subspace proves continuity.

After extension to an algebraic closure, (4.4) identifies the member with Book 184's absolutely
irreducible constituent. Hence the descended member is absolutely irreducible. $\square$

Continuity is not inferred from a trace function on Frobenius elements. It follows from an
actual invariant subspace of an already continuous representation. This distinction is
important because a compatible list of traces does not by itself supply an action law.

### 4.3 Independence of the displaying embedding

Let $j_1,j_2:E_\lambda\hookrightarrow\Omega$ be two embeddings into one algebraically closed
field. Scalar extension of (4.3) through $j_a$ gives the signed expression used by Book 184 at
that embedding. Its effective constituent is unique. Therefore

$$
r_{\mathfrak B,\lambda}\otimes_{j_a}\Omega
\simeq S_{\mathfrak B,\lambda,j_a}
\tag{4.5}
$$

for $a=1,2$, compatibly with scalar transport.

Nothing identifies $j_1$ and $j_2$ as maps. Instead, they display the same $E_\lambda$-model.
This is exactly the place-indexed coherence missing from the embedding-indexed output of Book
184.

### 4.4 Scalar extension

Let $E'/E$ be finite, let $\lambda'\mid\lambda$, and enlarge the elementary packet ledger by
scalars. Then

$$
R_{\mathfrak B,\lambda'}^\pm
\simeq
R_{\mathfrak B,\lambda}^\pm
\otimes_{E_\lambda}E'_{\lambda'}.
\tag{4.6}
$$

Scalar extension of (4.3) exhibits
$r_{\mathfrak B,\lambda}\otimes E'_{\lambda'}$ as an effective complement. Uniqueness in
Theorem 3.2 gives

$$
r_{\mathfrak B,\lambda'}
\simeq
r_{\mathfrak B,\lambda}\otimes_{E_\lambda}E'_{\lambda'}.
\tag{4.7}
$$

Thus a harmless coefficient enlargement refines the set of places and extends scalars. It does
not create a new arithmetic representation.

### 4.5 What coherence does and does not mean

Representations over $E_\lambda$ and $E_\mu$ for coefficient places of different residue
characteristics cannot be compared by tensoring one into the other. There is usually no field
map between the two completions. Coherence means instead that

- one number field $E$ indexes all members;
- the member at $\lambda$ is defined over $E_\lambda$;
- the Frobenius and declared bad-local objects exist over $E$ before completion;
- two displays of the same place give scalar transports of one model; and
- finite enlargement commutes with construction.

No web of linear maps between different completions is part of the definition. Attempting to
choose such maps would add meaningless structure rather than strengthen compatibility.

## 5. Independence of the Brauer relation

### 5.1 Two relations in one ledger

Let

$$
\mathfrak B=\{(H_i,\theta_i,n_i)\},
\qquad
\mathfrak B'=\{(J_j,\eta_j,m_j)\}
\tag{5.1}
$$

be two integral Brauer relations for $1_\Gamma$. The field $E$ was chosen using the complete
finite elementary packet and character ledger, so both relations and every cross-intersection

$$
H_i\cap xJ_jx^{-1}
\tag{5.2}
$$

already have models in the same coefficient field. No relation-specific change of coefficients
is required.

At a place $\lambda$, form the virtual difference

$$
\mathcal D_\lambda
=
\bigl([R_{\mathfrak B,\lambda}^+]-[R_{\mathfrak B,\lambda}^-]\bigr)
-
\bigl([R_{\mathfrak B',\lambda}^+]-[R_{\mathfrak B',\lambda}^-]\bigr).
\tag{5.3}
$$

It is an integral virtual class defined over $E_\lambda$.

### 5.2 The norm-zero comparison

This is the SP instantiation of Book 180, Corollary 7.3. Its extra work is to verify the
combined cross-relation Gram hypotheses from the actual packet array.

Expand the Hom norm of (5.3) using the union of the two induced lists and coefficient vector
$(n_i,-m_j)$. Frobenius reciprocity and Mackey decomposition express each Gram entry as a sum
over the double cosets in $H_i\backslash\Gamma/J_j$. Book 183's exact intersection theorem
identifies the two untwisted restrictions with one elementary packet. Book 184's self-twist
criterion then makes every summand, including every cross term, independent of the coefficient
embedding.

At the distinguished embedding, the tensor identity for either Brauer relation gives the same
class:

$$
[R_{\mathfrak B,\lambda_0}^+]-[R_{\mathfrak B,\lambda_0}^-]
=[\rho]
=[R_{\mathfrak B',\lambda_0}^+]-[R_{\mathfrak B',\lambda_0}^-]
\tag{5.4}
$$

after passage to one common $\ell$-adic overfield. Thus the norm of the difference is zero at
the distinguished embedding. Since the combined Gram matrix is embedding independent,

$$
\|\mathcal D_\lambda\otimes\overline E_\lambda\|^2=0
\tag{5.5}
$$

at every $\lambda$. The Hom norm is positive definite on the integral semisimple
Grothendieck group, so

$$
\mathcal D_\lambda\otimes\overline E_\lambda=0.
\tag{5.6}
$$

This proves equality of the full semisimple classes. Equality of their common good Frobenius
polynomials would be weaker and is not substituted for the norm calculation.

### 5.3 Descent of the comparison isomorphism

By Theorem 3.2, the two signed classes in (5.3) are represented over $E_\lambda$ by
$r_{\mathfrak B,\lambda}$ and $r_{\mathfrak B',\lambda}$. Equation (5.6) makes their scalar
extensions isomorphic. The Hom-base-change identity (3.9) produces a nonzero
$E_\lambda$-linear intertwiner. Absolute irreducibility makes it an isomorphism:

$$
\boxed{
r_{\mathfrak B,\lambda}\simeq r_{\mathfrak B',\lambda}.}
\tag{5.7}
$$

Thus Brauer-relation independence holds over the completion itself, not only after embedding
the completion into an algebraic closure.

### 5.4 Presentation, conjugate-term, and coordinate independence

Replacing $n_i=n_i^+-n_i^-$ by another positive-minus-negative presentation adds the same
semisimple representation to both sides of (4.3). It does not change the unique complement.

Replacing a term $(H_i,\theta_i,r_{H_i,\lambda})$ by its field conjugate under $x\in\Gamma$
also does not change its induction. The explicit map

$$
g\otimes v\longmapsto gx^{-1}\otimes{}^xv
\tag{5.8}
$$

identifies the two induced representations. Changing coset representatives, bases, or splitting
coordinates conjugates the matrices of an actual summand over $E_\lambda$ and leaves the
isomorphism class of the complement unchanged.

These statements concern the output, not the noncanonical cancellation map. The isomorphism in
(4.3) can change when coordinates change; the remaining rank-two isomorphism class cannot.

### 5.5 The intrinsic member

We may now suppress the Brauer relation and write

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda).
\tag{5.9}
$$

A relation remains a useful device for proving properties because it displays $r_\lambda$ as a
complement inside induced automorphic realizations. It is no longer part of the definition of
the member. This is the first point at which the family can be indexed intrinsically by places
of $E$.

## 6. Restriction recovery and the two conjugation actions

### 6.1 Restricting the signed expression

Effectivity over $\mathbf Q$ should recover the packet members from which the signed expression
was built. This is stronger than the top-field consistency check alone and is proved directly
in the representation ring.

Fix an elementary subgroup $H\leq\Gamma$ and work first over an algebraic closure of
$E_\lambda$. Put $G_H=G_{F_H}$. Applying Book 180's Mackey decomposition and tensor identity
to one induced term (2.5) gives

$$
\begin{aligned}
\operatorname{Res}_{G_H}^{G_{\mathbf Q}}A_{i,\lambda}
\simeq
\bigoplus_{x\in H\backslash\Gamma/H_i}
\operatorname{Ind}_{G_{F_{D_x}}}^{G_H}
\left({}^x(r_{H_i,\lambda}\otimes\theta_{i,\lambda})
|_{G_{F_{D_x}}}\right),
\end{aligned}
\tag{6.1}
$$

where

$$
D_x=H\cap xH_ix^{-1}.
\tag{6.2}
$$

The group $D_x$ is elementary. Book 183's overlap theorem identifies

$$
{}^xr_{H_i,\lambda}|_{G_{F_{D_x}}}^{\mathrm{ss}}
\simeq r_{D_x,\lambda}
\simeq r_{H,\lambda}|_{G_{F_{D_x}}}^{\mathrm{ss}}.
\tag{6.3}
$$

Restoring the finite character and applying the tensor identity for induction turns the
$x$-summand of (6.1) into

$$
r_{H,\lambda}\otimes
\operatorname{Ind}_{D_x}^{H}
\left(({}^x\theta_i)|_{D_x}\right).
\tag{6.4}
$$

Here the finite-group representation in (6.4) is inflated through $G_H/G_M\simeq H$. The
same double-coset formula is the restriction of the finite-group induced character
$\operatorname{Ind}_{H_i}^{\Gamma}\theta_i$ to $H$.

### 6.2 Recovery on every elementary fixed field

Sum (6.4) with coefficients $n_i$. Restricting the Brauer identity (1.9) from $\Gamma$ to
$H$ gives

$$
\sum_i n_i
\operatorname{Res}_{H}^{\Gamma}
\operatorname{Ind}_{H_i}^{\Gamma}\theta_i
=1_H.
\tag{6.5}
$$

Consequently, in the semisimple Grothendieck group over $\overline E_\lambda$,

$$
\operatorname{Res}_{G_H}^{G_{\mathbf Q}}
\left(
[R_{\mathfrak B,\lambda}^+]-[R_{\mathfrak B,\lambda}^-]
\right)
=[r_{H,\lambda}].
\tag{6.6}
$$

Substitute the actual effective class $[r_\lambda]$ from Chapter 4. Restriction of a
semisimple characteristic-zero representation to a finite-index subgroup is semisimple: pass
to the normal core, use its socle, and average projections over the finite quotient. Therefore
(6.6) is equality of two actual semisimple representations after scalar extension.

**Theorem 6.1 (restriction recovery).** For every elementary $H\leq\Gamma$ and every finite
place $\lambda$ of $E$,

$$
\boxed{
r_\lambda|_{G_{F_H}}\simeq r_{H,\lambda}.}
\tag{6.7}
$$

**Proof.** The preceding Mackey calculation gives the isomorphism after extension to
$\overline E_\lambda$. Both sides of (6.7) are $E_\lambda$-representations. The right side is
absolutely irreducible, so the left side is as well. Hom base change as in (3.9) descends the
intertwiner to $E_\lambda$. $\square$

This proof is relation independent because its output is the intrinsic member of Chapter 5.
It uses the exact intersection comparison (6.3), not only restriction to $G_M$.

### 6.3 Recovery over the controlled top

Take $H=1$ in Theorem 6.1. Since $F_1=M$,

$$
r_\lambda|_{G_M}\simeq r_{1,\lambda},
\tag{6.8}
$$

the coefficient member of the selected top packet. This is the expected recovery statement
over the controlled automorphy field.

Equation (6.8) is not itself a proof of effectivity: it is obtained only after the rank-two
member has been constructed. Nor would (6.8) alone recover (6.7), because two extensions from
$G_M$ to $G_{F_H}$ can differ by a character of $H$. The Mackey calculation retains exactly
that finite-quotient information.

At the distinguished place, (1.6) and (6.7) give

$$
r_{\lambda_0}|_{G_{F_H}}
\simeq \rho|_{G_{F_H}}
\tag{6.9}
$$

after placing the coefficient fields in one finite $\ell$-adic overfield. The global
identification with $\rho$ will be proved in Section 8.6.

### 6.4 Field conjugation

Let $x\in\Gamma$. It carries $F_H$ to $F_{xHx^{-1}}$. Conjugation of the packet array gives

$$
{}^xr_{H,\lambda}\simeq r_{xHx^{-1},\lambda}.
\tag{6.10}
$$

Theorem 6.1 makes this compatibility intrinsic to the assembled member. Choose a lift
$\widetilde x\in G_{\mathbf Q}$. The matrix $r_\lambda(\widetilde x)$ intertwines the
conjugate of $r_\lambda|_{G_{F_H}}$ with its restriction to
$G_{F_{xHx^{-1}}}$. Combined with (6.7), this gives (6.10). Changing the lift multiplies by
an element of $G_M$ and does not change the isomorphism class.

Field conjugation moves number fields and their places. It does not apply an automorphism to
Hecke eigenvalues. This action was already built into the Mackey double cosets and should not
be confused with coefficient conjugation.

### 6.5 Coefficient conjugation

Because $E/\mathbf Q$ is Galois, an automorphism $\sigma\in\operatorname{Gal}(E/\mathbf Q)$
carries a place $\lambda$ to $\sigma\lambda$ and induces a topological field isomorphism

$$
\sigma:E_\lambda\xrightarrow{\sim}E_{\sigma\lambda}.
\tag{6.11}
$$

Apply $\sigma$ to every packet coefficient and finite-character value in a Brauer
presentation. This produces the coefficient-conjugate packet ledger and another integral
Brauer relation. Scalar transport of (4.3) is its descended cancellation at
$\sigma\lambda$. Relation-independence then gives

$$
{}^\sigma r_\lambda
\simeq r^{\sigma}_{\sigma\lambda},
\tag{6.12}
$$

where the superscript on the right means the member of the coefficient-conjugate system. At a
good prime its polynomial is

$$
P_p^\sigma(X)=X^2-\sigma(a_p)X+p.
\tag{6.13}
$$

Equation (6.12) is covariance, not invariance. Unless all $a_p$ lie in the fixed field of
$\sigma$, one must not identify $r^{\sigma}_{\sigma\lambda}$ with the member of the original
system carrying the un-conjugated polynomial. Field conjugation and coefficient conjugation
commute because they act on different coordinates of the finite packet ledger.

## 7. Common Frobenius polynomials, determinant, and purity

### 7.1 The algebraic quadratic polynomial

Let $S_0$ be the common finite exceptional set in the Book 183 packet array. It contains $2$,
$\ell$, every rational prime ramified in $M$, and the finitely many packet and character
exceptions. For $p\notin S_0$, Book 183 computes the local cyclic blocks of each induced term.
If $w\mid p$ is a place of $F_{H_i}$, $f_w=f(w/p)$, and

$$
X^2-a_{i,w}X+Nw
\tag{7.1}
$$

is the packet polynomial, then the reciprocal characteristic series for the $i$th induced
term is

$$
D_{i,p}(T)
=
\prod_{w\mid p}
\left(
1-a_{i,w}\theta_i(\operatorname{Frob}_w)T^{f_w}
+\theta_i(\operatorname{Frob}_w)^2Nw\,T^{2f_w}
\right).
\tag{7.2}
$$

The exponent is the residue degree, not the ramification index or the global degree. It comes
from the cycle by which arithmetic Frobenius permutes the local induction blocks.

The signed product

$$
D_{\mathfrak B,p}(T)=\prod_iD_{i,p}(T)^{n_i}
\tag{7.3}
$$

is initially a rational function in $E(T)$. At the distinguished embedding, the tensor
identity turns it into the characteristic series of $\rho$:

$$
D_{\mathfrak B,p}(T)=1-a_pT+pT^2
\tag{7.4}
$$

after applying the injective map into a finite $\ell$-adic overfield. Injectivity implies that
(7.4) already holds in $E(T)$, so the rational function is a polynomial in $E[T]$. Define

$$
P_p(X)=X^2-a_pX+p\in E[X].
\tag{7.5}
$$

The same distinguished calculation for another Brauer relation gives the same $P_p$.
Alternatively, this follows from the relation-independent member of Chapter 5. Polynomiality
precedes coefficient descent, but only after coefficient descent does $P_p$ become the
characteristic polynomial of a place-indexed member.

### 7.2 Unramifiedness of the descended constituent

Fix $p\notin S_0$ with $p\ne q_\lambda$. Every elementary packet and finite character in
$R_{\mathfrak B,\lambda}^+$ is unramified at $p$, and the extensions used in its local
induction are unramified there. Thus inertia at $p$ acts trivially on
$R_{\mathfrak B,\lambda}^+$.

Equation (4.3) realizes $r_\lambda$ as a stable direct summand of this representation. The
restriction of the identity action to a stable summand is the identity, so $r_\lambda$ is
unramified at $p$. Taking characteristic series in (4.3) and canceling the negative factor
gives

$$
\det(1-r_\lambda(\operatorname{Frob}_p)T)
=1-a_pT+pT^2.
\tag{7.6}
$$

Equivalently,

$$
\det(X-r_\lambda(\operatorname{Frob}_p))=P_p(X).
\tag{7.7}
$$

This proves unramifiedness from an actual direct summand, not from formal cancellation of
inertial characters.

### 7.3 Weak compatibility

**Theorem 7.1 (weak compatibility).** The collection

$$
\mathcal R_E=\{r_\lambda\}_{\lambda\in\operatorname{Pl}_f(E)}
\tag{7.8}
$$

is an $E$-rational weakly compatible system of rank two over $\mathbf Q$, with common
exceptional set $S_0$ and common polynomials (7.5).

**Proof.** Proposition 4.2 gives continuous semisimple rank-two members over the correct
completions. Sections 7.1--7.2 prove that, whenever $p\notin S_0$ and
$p\ne q_\lambda$, the member is unramified and has the scalar image of $P_p$. These are
exactly the defining conditions. $\square$

At the coefficient prime $p=q_\lambda$, no unramifiedness statement is implicit. The
coefficient-prime local representation belongs to $p$-adic Hodge theory and cannot be read from
(7.7).

### 7.4 The actual determinant and duality

Book 183 computes the determinant line of the signed class. For a rank-two representation $u$
of an open subgroup, the determinant of finite induction contains a coset-permutation sign
squared, hence trivial, and the transfer of $\det u$. Twisting $u$ by $\theta_i$ multiplies
its determinant by $\theta_i^2$. Applying the determinant to the one-dimensional Brauer
relation cancels the transferred character squares, while evaluation of (1.9) at the identity
gives

$$
\sum_i n_i[\Gamma:H_i]=1.
\tag{7.9}
$$

The resulting virtual determinant is $\chi_{q_\lambda}$. Taking determinants in the actual
isomorphism (4.3) yields

$$
\boxed{\det r_\lambda=\chi_{q_\lambda}.}
\tag{7.10}
$$

No determinant-normalizing twist is chosen after effectivity. Such a twist would alter the
Frobenius and SP records.

Two-dimensional exterior algebra gives a canonical isomorphism

$$
V^\vee\simeq V\otimes(\det V)^{-1}.
\tag{7.11}
$$

Therefore

$$
r_\lambda^\vee\simeq r_\lambda\otimes\chi_{q_\lambda}^{-1}.
\tag{7.12}
$$

This is a rational duality. It does not choose a self-dual integral lattice.

### 7.5 Weight-one purity

**Theorem 7.2 (purity).** For every $p\notin S_0$, every root $\alpha$ of $P_p$ and every
complex embedding $\iota:\overline{\mathbf Q}\hookrightarrow\mathbf C$ satisfy

$$
|\iota(\alpha)|=p^{1/2}.
\tag{7.13}
$$

**Proof.** Let $\alpha,\beta$ be the roots of $P_p$ and choose a place $w$ of $M$ above $p$,
with residue degree $f=f(w/p)$. Restriction recovery (6.8) identifies the restriction of the
assembled member with the selected top packet. At the distinguished embedding, restriction of
arithmetic Frobenius raises the two roots to the $f$th powers. Thus the top packet polynomial at
$w$ has roots

$$
\alpha^f,\qquad\beta^f.
\tag{7.14}
$$

The parallel-weight-two top packet is pure of weight one, so for every complex embedding

$$
|\iota(\alpha^f)|=(p^f)^{1/2}.
\tag{7.15}
$$

Taking the positive real $f$th root gives (7.13). Coefficient conjugation of the top packet
proves the statement for every conjugate root, not merely for the distinguished complex
embedding. $\square$

The determinant equality $\alpha\beta=p$ alone would not prove purity: two algebraic numbers
can have product $p$ and unequal complex absolute values. The top packet's weight theorem is
the decisive input.

### 7.6 Frobenius powers after restriction

The polynomial $P_p$ determines its restriction to every unramified residue-degree extension
without choosing its roots. Define

$$
A_0=2,
\qquad A_1=a_p,
\qquad A_f=a_pA_{f-1}-pA_{f-2}\quad(f\geq2).
\tag{7.16}
$$

If $\alpha,\beta$ are the roots, then $A_f=\alpha^f+\beta^f$. Hence the restricted
polynomial at residue degree $f$ is

$$
P_p^{[f]}(X)=X^2-A_fX+p^f.
\tag{7.17}
$$

All coefficients lie in $E$, and

$$
(P_p^{[f]})^{[g]}=P_p^{[fg]}.
\tag{7.18}
$$

Equation (7.17) agrees with the packet polynomial under restriction recovery. Reusing $a_p$
unchanged at a degree-$f$ place would be a Frobenius-normalization error.

## 8. Local effectivity and the SP record at two

### 8.1 The algebraic local Mackey class

Good Frobenius polynomials do not determine monodromy. To obtain a common SP record, we return
to the full algebraic local objects in the packet array.

Fix a rational prime $v$. At every place $w\mid v$ of an elementary fixed field
$F_{H_i}$, let $D_{i,w}$ be the algebraic Frobenius-semisimple Weil--Deligne pair supplied in
the proved local-compatibility range of the packet attachment theorem. After the one common
finite coefficient enlargement already allowed in Chapter 2, the finitely many bad local
objects have models over $E$.

Finite twisting and Weil-group induction are algebraic operations on Weil--Deligne pairs. Put

$$
\mathscr D_{v,E}^\pm
=
\bigoplus_i\bigoplus_{w\mid v}
\left(
\operatorname{Ind}_{W_{(F_{H_i})_w}}^{W_{\mathbf Q_v}}
(D_{i,w}\otimes\theta_{i,w})
\right)^{\oplus n_i^\pm}.
\tag{8.1}
$$

For a coefficient place $\lambda$ with $q_\lambda\ne v$, local--global compatibility and
local Mackey decomposition identify

$$
\mathscr D_{v,E}^\pm\otimes_E\overline E_\lambda
\simeq
\operatorname{WD}_v(R_{\mathfrak B,\lambda}^\pm)^{\mathrm{F\text{-}ss}}.
\tag{8.2}
$$

Applying the Weil--Deligne functor to (4.3) gives an actual direct-sum cancellation

$$
\mathscr D_{v,E}^+\otimes_E\overline E_\lambda
\simeq
\operatorname{WD}_v(r_\lambda)^{\mathrm{F\text{-}ss}}
\oplus
\mathscr D_{v,E}^-\otimes_E\overline E_\lambda.
\tag{8.3}
$$

Both finite inertia and $N$ are present in (8.3). It is not an equality of conductor integers
or local Euler factors.

Equation (8.2) is an upstream input, not a consequence of the assembled family. For the SP
packet terms it is supplied by Book 183's direct local-preservation certificates or by its
ambient-semisimplicity reduction. The cancellation in (8.3) and the Krull--Schmidt argument
below can transport and cancel already identified full pairs; they cannot be used backward to
prove that a raw packet pair survived global semisimplification.

### 8.2 An effective local complement

Weil--Deligne representations form a Krull--Schmidt category for direct sums. For the finitely
many objects under consideration, take the finite-dimensional algebra generated by finite
inertia, Frobenius and its inverse, and $N$. Direct-sum decompositions are module
decompositions for this algebra, and indecomposable multiplicities are unique. Hence

$$
U\oplus C\simeq V\oplus C
\quad\Longrightarrow\quad U\simeq V.
\tag{8.4}
$$

Work first over $\overline E$. Equation (8.3) shows that the difference between the
indecomposable multiplicities of $\mathscr D_{v,E}^+$ and $\mathscr D_{v,E}^-$ is
nonnegative and has total rank two. Let $D_{v,\overline E}$ be the resulting rank-two
complement. This object is independent of the coefficient place used in (8.3), because its
indecomposable multiplicities were calculated from the one algebraic pair
$\mathscr D_{v,E}^\pm$.

Outside the finite packet exceptional set, the complement is unramified and is defined over
$E$ by $P_v$. At the finitely many remaining places, the matrices and decomposition idempotents
of $D_{v,\overline E}$ are algebraic. Enlarge $E$ once by their finitely many coefficients.
Then there is an algebraic pair $D_v$ over $E$ such that

$$
\mathscr D_{v,E}^+\simeq D_v\oplus\mathscr D_{v,E}^-
\tag{8.5}
$$

and, throughout the proved packet local-compatibility range,

$$
\operatorname{WD}_v(r_\lambda)^{\mathrm{F\text{-}ss}}
\simeq D_v\otimes_EE_\lambda
\qquad(q_\lambda\ne v).
\tag{8.6}
$$

The finite enlargement does not alter previously constructed members: Section 4.4 identifies
the reconstruction over the enlarged field with scalar extension. A second Brauer relation
gives the same $D_v$, because the corresponding global members are isomorphic and
Krull--Schmidt cancellation identifies their algebraic local complements after a common
faithful scalar extension.

### 8.3 The proved strong-compatibility range

Equation (8.6) is asserted exactly where the elementary packet attachment theorem supplies the
local pairs $D_{i,w}$. In the controlled packet array this includes the designated SP place
$2$ and the other finite places in the established local--global comparison range. No omitted
bad-place theorem is manufactured from good Frobenius traces.

At a good $v\notin S_0$, the pair $D_v$ is unramified, has $N=0$, and its Frobenius
polynomial is $P_v$. If $v$ lies in the finite auxiliary set and the distinguished member is
available there away from its coefficient characteristic, (8.6) can compare $D_v$ with the
actual local pair of $\rho$. In particular, whenever that local representation is unramified,
$D_v$ is unramified and the auxiliary prime is certified absent from the common support. Its
Frobenius characteristic polynomial is then a common
$X^2-a_vX+v\in E[X]$ by (7.10) and (8.6). Removing it also from the exceptional set used for
the pure compatible-polynomial ledger requires the
weight-one purity of that polynomial to be in the proved packet local-purity range or to be
separately certified; unramifiedness alone does not prove purity.

This shrinking is made prime by prime and only with the stated local comparison. It is not a
formal consequence of a signed conductor sum. Let $S$ be $S_0$ with only those auxiliary primes
removed for which the common unramified polynomial and its weight-one purity have both been
certified. The common support ledger may be smaller than $S$, but this convention avoids
claiming a pure polynomial outside the range proved by the packet input.

There is a sharper source-facing conductor input which should be separated from this
prime-by-prime construction. Let $B_{\mathrm{gen}}$ be a common finite bad-place set for the
actual genuine rank-two realization, with the property that for every coefficient place
$\lambda$ the representation $r_\lambda$ is unramified at every rational prime
$q\notin B_{\mathrm{gen}}$ with $q\ne q_\lambda$. The additional arithmetic assertion is

$$
(\mathrm{Cond}_2)\qquad B_{\mathrm{gen}}\subseteq\{2\}.
\tag{Cond2}
$$

This assertion is stronger than weak compatibility: weak compatibility supplies some common
finite set, whereas $(\mathrm{Cond}_2)$ proves that every displayed auxiliary prime cancels in
the actual genuine representation.

For the restricted construction without $(\mathrm{AI}_2)$, the same definition and argument
are used only for the already constructed places $\lambda\nmid2$. Nothing in the reduction
below constructs or quantifies over a missing base-field member above two.

**Proposition 8.1 (support-at-two reduction).** Assume $(\mathrm{Cond}_2)$. Then every member
$r_\lambda$ is unramified at every rational prime outside
$\{2,q_\lambda\}$. In particular, for every selected place $\nu\mid3$,

$$
r_\nu\text{ is unramified outside }\{2,3\}.
\tag{U}
$$

**Proof.** Let $q\ne2,q_\lambda$. The first inequality and $(\mathrm{Cond}_2)$ give
$q\notin B_{\mathrm{gen}}$; the second puts $q$ away from the coefficient characteristic.
The defining specialization property of $B_{\mathrm{gen}}$ therefore says that inertia at
$q$ acts trivially on $r_\lambda$. Taking $\lambda=\nu$ gives $(\mathrm U)$. No Frobenius-density,
Chebotarev, or Brauer--Nesbitt argument occurs. $\square$

The exact finite replacement for the source-facing theorem is useful enough to name.  Keep
the distinguished place $\lambda_0\mid\ell$ and fix $\nu\mid3$.  Let
$S_{\mathrm{aux}}(\nu)$ be the subset of $S_0\setminus\{2,3\}$ at which Sections 7.2 and
8.3 have not already proved $r_\nu$ unramified, and let $S_{\mathrm{rem}}\subseteq S_0$ be
the analogous residual common bad set after every already certified family-level removal.

The **selected auxiliary comparison certificate** $(\mathrm{AUX}_\nu)$ consists of the
following finite data.

- For every $q\in S_{\mathrm{aux}}(\nu)\setminus\{\ell\}$, the algebraic packet pairs defining $D_q$
  exist and (8.6) holds both at $\lambda_0$ and at $\nu$.
- If $\ell\in S_{\mathrm{aux}}(\nu)$, the local packet factors entering the positive display
  at every place above $\ell$ are spherical, the finite quotient characters are locally
  trivial, the resulting algebraic complement $D_\ell$ is unramified, and (8.6) holds at
  $\nu$.

The **family auxiliary comparison certificate** $(\mathrm{AUX}_{\mathrm{all}})$ requires,
for every $q\in S_{\mathrm{rem}}\setminus\{2\}$, an algebraic $D_q$ for which (8.6) holds at every
already constructed coefficient place $\lambda$ with $q_\lambda\ne q$.  It also requires an
unramified tester: at $q\ne\ell$ this is the distinguished member at $\lambda_0$, and at
$q=\ell$ it is the spherical algebraic packet calculation just described.

**Proposition 8.2 (finite auxiliary reduction).** The certificate
$(\mathrm{AUX}_\nu)$ proves $(\mathrm U)$ for $r_\nu$.  The certificate
$(\mathrm{AUX}_{\mathrm{all}})$ proves $(\mathrm{Cond}_2)$.

**Proof.** Let $q\in S_{\mathrm{aux}}(\nu)\setminus\{\ell\}$.  By (1.3), the distinguished realization
$r_{\lambda_0}\simeq\rho$ is unramified at $q$.  Its comparison with $D_q$ forces the finite
inertia matrices of $D_q$ to be the identity and its monodromy matrix to be zero.  The
comparison at $\nu$ then makes $r_\nu$ unramified at $q$.  If $\ell$ belongs to
$S_{\mathrm{aux}}(\nu)$, the second clause of
$(\mathrm{AUX}_\nu)$ says directly that $D_\ell$ is unramified, and its comparison at $\nu$
gives the same conclusion.  Every other prime was excluded from
$S_{\mathrm{aux}}(\nu)$ precisely because its unramifiedness was already proved.  The prime
$3$ is the selected coefficient characteristic and is excluded from $(\mathrm U)$.
This proves the first assertion.

For $(\mathrm{AUX}_{\mathrm{all}})$, use the same test at every
$q\in S_{\mathrm{rem}}\setminus\{2,\ell\}$.  Notice that it also handles $q=3$ when that
prime remains, since
$\lambda_0\mid\ell$ and $\ell\ne3$.  At $q=\ell$ use the supplied spherical calculation.
Thus every remaining $D_q$ with $q\ne2$ is unramified.  Equation (8.6) then makes every member away
from its own coefficient characteristic unramified at $q$; primes outside
$S_{\mathrm{rem}}$ were already certified.  Shrinking the defining common bad set to
$\{2\}$ gives $(\mathrm{Cond}_2)$. $\square$

The two certificates identify the first missing local theorem precisely.  At a spherical
place it is the complete good-place comparison, including the integral model, component, and
hyperspecial ledger.  At a tame principal or dihedral place it is the actual finite descent
complex with its type projector, trivial wild inertia, zero-monodromy calculation, character
or exchange lines, and Frobenius return maps.  Those are the geometric hypotheses of the recognition theorems of
Books 128 and 168; Book 128, Lemma 3.2 then supplies raw-to-global passage formally from
$N=0$. Neither the automorphic type name nor the global Brauer cancellation supplies the
geometric inputs. This is exactly Book 182, Required Theorem 7.3; its first clause is the
fine tame-level model carrying the equivariant packet and type projectors.

It is not possible to replace these finite checks by the claim that every auxiliary place is
spherical.  A rational prime ramified in the nontrivial controlled top cannot split completely
there.  At a nonsplit cyclic descent, an extension of a spherical top parameter can be a tame
principal-series or selected tame-dihedral parameter, and a quotient-character correction can
also be ramified.  Local Mackey induction then retains that ramification in the positive and
negative displaying terms.  Only the genuine rank-two complement is expected to cancel it.

Nor does equality of the good Frobenius polynomials prove the missing comparisons.  The
exceptional prime $q$ is absent from that polynomial ledger, so the ledger contains no matrix
for its inertia or monodromy.  Chebotarev and Brauer--Nesbitt compare two already existing
semisimple representations over one coefficient topology.  Here the $\lambda_0$-adic and
$\nu$-adic trace functions take limits in different completions; equality of their algebraic
values on a dense set of Frobenius elements supplies no common continuous trace function on
all of $G_{\mathbf Q}$.  Even after finite inertia is known, an inertial type or a Frobenius
semisimplification does not recover the monodromy operator.  Thus
$(\mathrm{AUX}_\nu)$ is a finite all-required-primes local theorem, while
$(\mathrm{AUX}_{\mathrm{all}})$ is its family-wide form; the current packet input proves
neither one.  This is not a new post-assembly topic.  Book 182, Proposition 7.2A supplies the
basic rational carriers and attachment of the candidate cyclic descents, but its controlled
top datum must already include the raw principal/dihedral descent complexes, type and exchange
lines, trivial-wild-inertia and zero-monodromy calculations, and Frobenius return maps for the
retained auxiliary primes.
No separate ambient-semisimplicity or raw-to-global hypothesis remains in these $N=0$ rows.
Proposition 8.2 is the formal cancellation after that local-geometric clause has been supplied.

### 8.4 The common special pair

The prime $2$ splits completely in $M$. Hence it splits completely in every $F_H$, every
completion above it is $\mathbf Q_2$, and every character inflated from an elementary quotient
is locally trivial. Book 183 supplies one algebraic SP pair

$$
D_2=(r_2,N_2)
\tag{8.7}
$$

over the common coefficient field. Its finite Weil inertia is trivial, and

$$
N_2^2=0,
\qquad
N_2\ne0,
\qquad
\operatorname{rank}N_2=1.
\tag{8.8}
$$

Arithmetic Frobenius $F_2$ satisfies

$$
r_2(F_2)N_2r_2(F_2)^{-1}=2N_2.
\tag{8.9}
$$

Every local packet term in (8.1) is a copy of (8.7). If

$$
a=\sum_i n_i^+[\Gamma:H_i],
\qquad
b=\sum_i n_i^-[\Gamma:H_i],
\tag{8.10}
$$

then local Mackey decomposition gives $a$ copies on the positive side and $b$ copies on the
negative side. The rank identity (7.9) says $a-b=1$. Thus (8.5) at $2$ has complement exactly
one copy of $D_2$. For every $\lambda\nmid2$,

$$
\boxed{
\operatorname{WD}_2(r_\lambda)^{\mathrm{F\text{-}ss}}
\simeq D_2\otimes_EE_\lambda.}
\tag{8.11}
$$

This is the SP branch. It has nonzero monodromy and trivial finite inertia. No nontrivial
finite tame type occurs in (8.7)--(8.11).

### 8.5 Monodromy line, sign, and conductor

Since $N_2$ is nonzero nilpotent of rank one on a two-dimensional space,

$$
\mathscr L_2=\ker N_2=\operatorname{im}N_2
\tag{8.12}
$$

is an $E$-line. Equation (8.9) makes it stable under the Weil group. The controlled SP datum
includes one sign $\varepsilon_2\in\{1,-1\}$ such that arithmetic Frobenius acts on the
quotient by $\varepsilon_2$ and on $\mathscr L_2$ by $2\varepsilon_2$:

$$
\left(
F_2\mid D_2/\mathscr L_2,
F_2\mid\mathscr L_2
\right)
=
(\varepsilon_2,2\varepsilon_2).
\tag{8.13}
$$

The product of these eigenvalues is $2$, in agreement with the cyclotomic determinant. The
order in (8.13) matters: the line is the cyclotomic side of the special filtration.

Finite Weil inertia is trivial, but the associated adic representation has nontrivial
unipotent tame inertia because $N_2\ne0$. Its inertia-fixed space is precisely
$\mathscr L_2$. The Swan conductor is zero, and the Weil--Deligne conductor formula gives

$$
\begin{aligned}
a_2(D_2)
&=a(r_2)+\dim D_2^{I_2}-\dim(\ker N_2)^{I_2}\\
&=0+2-1=1.
\end{aligned}
\tag{8.14}
$$

Thus every $r_\lambda$ with $\lambda\nmid2$ carries the complete rational record

$$
N_2\ne0,
\qquad
\mathscr L_2,
\qquad
\varepsilon_2,
\qquad
a_2=1.
\tag{8.15}
$$

Conductor one is a consequence of the pair, not a substitute for it. At a coefficient place
above $2$, prime-to-coefficient Weil--Deligne comparison is unavailable and no assertion is
made by (8.11).

### 8.6 Identification of the chosen SP member

At the distinguished embedding, Book 183's tensor identity gives

$$
[R_{\mathfrak B,\lambda_0}^+]-[R_{\mathfrak B,\lambda_0}^-]=[\rho]
\tag{8.16}
$$

after embedding $E_{\lambda_0}$ and $L_0$ in one finite extension $C/\mathbf Q_\ell$.
Both sides are effective and absolutely irreducible. Uniqueness of the constituent therefore
gives

$$
\boxed{
r_{\lambda_0}\otimes_{E_{\lambda_0}}C
\simeq
\rho\otimes_{L_0}C.}
\tag{8.17}
$$

This identifies the chosen representation itself, not merely its good Frobenius
semisimplification. Because $2\ne\ell$, equation (8.11) applies to the distinguished member;
the local pair in (8.17) is the chosen SP pair with the same line and sign.

No lattice is needed for this identification. In particular, the chosen member is not replaced
by a lattice cut out of the positive induced representation.

### 8.7 The integral boundary

The output through Section 8.6 is entirely characteristic zero. It provides the rational
representation at every coefficient place and the rational SP line at $2$. It does not choose
an $\mathcal O_{E_\lambda}$-lattice in any member, does not intersect a lattice with
$\mathscr L_2$, and does not measure an integral monodromy thickness.

The cancellation

$$
R_{\mathfrak B,\lambda}^+
\simeq r_\lambda\oplus R_{\mathfrak B,\lambda}^-
\tag{8.18}
$$

can use denominators. Even after stable lattices are chosen in all three rational summands, the
chosen lattices need not form an integral direct sum, and reduction need not preserve the
decomposition.  The contraction of an ambient lattice with the rational summand is saturated,
but this book has supplied no finite-flat tower on the ambient positive lattice from which its
closures could be taken.  Modular representations of the finite quotient can have nonsplit
extensions.

Accordingly, no finite-flat quotient, compatible transition map, integral special line, or
residual conductor is asserted here. The fixed-three integral theory selects its own stable
lattice after the three-adic member and, on the geometric route, finite-flat positive ambient
towers have been supplied. Rational nonzero monodromy survives coefficient extension; its
reduction modulo a chosen lattice is a separate question.

## 9. The complete base-field assembly theorem

### 9.1 Statement

We can now collect the construction without reference to a chosen Brauer presentation.

**Theorem 9.1 (coefficient-descended compatible system over the base field).** Let
(1.2)--(1.8) be the controlled SP packet-array datum of Book 183, and let Book 184's
embedding-indexed effectivity theorem be applied to its integral Brauer classes. Assume
$(\mathrm{AI}_2)$ as stated in Section 1.2, and assume no base-field compatible family as part
of the input.

Then there are a finite Galois number field $E$, a place $\lambda_0\mid\ell$, a finite set
$S$ of rational primes, and representations

$$
r_\lambda:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\lambda)
\qquad
(\lambda\in\operatorname{Pl}_f(E))
\tag{9.1}
$$

with the following properties.

1. **Existence over completions.** Every $r_\lambda$ is continuous and absolutely
   irreducible. Its scalar extension under any embedding inducing $\lambda$ is the effective
   embedding-indexed member of Book 184.
2. **Coefficient descent.** The Schur class and the scalar descent cocycle of that effective
   member vanish. The descended $E_\lambda$-model is the multiplicity-one complement in an
   actual signed expression defined over $E_\lambda$.
3. **Brauer independence.** The $E_\lambda$-isomorphism class is independent of the integral
   Brauer relation, its positive-minus-negative presentation, conjugation of a term, coset
   representatives, packet coordinates, the embedding used to display $E_\lambda$, and
   harmless finite coefficient enlargement.
4. **Weak compatibility.** For every $p\notin S$ there is

   $$
   P_p(X)=X^2-a_pX+p\in E[X]
   \tag{9.2}
   $$

   such that, whenever $p\ne q_\lambda$, the member $r_\lambda$ is unramified at $p$ and

   $$
   \det(X-r_\lambda(\operatorname{Frob}_p))=P_p(X).
   \tag{9.3}
   $$

5. **Determinant and purity.** For every $\lambda$,

   $$
   \det r_\lambda=\chi_{q_\lambda},
   \qquad
   r_\lambda^\vee\simeq r_\lambda\otimes\chi_{q_\lambda}^{-1}.
   \tag{9.4}
   $$

   Every root of every $P_p$, under every complex embedding, has absolute value $p^{1/2}$.
6. **Restriction recovery.** For every elementary $H\leq\Gamma$,

   $$
   r_\lambda|_{G_{F_H}}\simeq r_{H,\lambda}.
   \tag{9.5}
   $$

   In particular, restriction to $G_M$ recovers the selected top packet member.
7. **Conjugation.** Field conjugation transports (9.5) to the conjugate elementary fixed
   field. Coefficient conjugation carries the system to the coefficient-conjugate system,
   sending $P_p$ to $P_p^\sigma$ and commuting with field conjugation.
8. **Strong local records in the proved range.** For every finite $v$ in the local--global
   comparison range of the elementary packet array, there is an algebraic
   Frobenius-semisimple Weil--Deligne pair $D_v$ such that

   $$
   \operatorname{WD}_v(r_\lambda)^{\mathrm{F\text{-}ss}}
   \simeq D_v\otimes_EE_\lambda
   \qquad(v\ne q_\lambda).
   \tag{9.6}
   $$

   This comparison can certify an auxiliary prime absent from the common support. It is removed
   from $S$ only when its common unramified Frobenius polynomial and weight-one purity are also
   certified. No place outside the proved range is inserted by a density argument.
9. **The SP place.** The place $2$ lies in the range of clause 8. The pair $D_2=(r_2,N_2)$
   has trivial finite inertia,

   $$
   N_2^2=0,
   \quad
   \operatorname{rank}N_2=1,
   \quad
   \ker N_2=\operatorname{im}N_2=\mathscr L_2,
   \tag{9.7}
   $$

   and arithmetic Frobenius acts by $\varepsilon_2$ on the quotient and by
   $2\varepsilon_2$ on $\mathscr L_2$. Its Artin conductor exponent is one. These statements
   hold for every $r_\lambda$ with $\lambda\nmid2$ after scalar extension.
10. **Chosen member and integral boundary.** In one finite common $\ell$-adic overfield $C$,

    $$
    r_{\lambda_0}\otimes C\simeq\rho\otimes C.
    \tag{9.8}
    $$

    No stable lattice, integral projector, finite-flat quotient, transition tower, or residual
    local extension is part of the construction.

The collection (9.1), together with (9.2) and the local objects in their declared range, is the
coefficient-descended compatible system over $\mathbf Q$.

Without $(\mathrm{AI}_2)$, the same construction and conclusions hold place by place for
$\lambda\nmid2$, including at every $\nu\mid3$, but no effective base-field member above $2$
is thereby constructed. The elementary top-packet member above two still exists, as explained
in Section 1.2; it is not the desired Brauer complement over $\mathbf Q$. That restricted
collection is not the all-finite-place compatible system asserted in this theorem.

### 9.2 Proof

Choose the common finite Galois coefficient field of Chapter 2. It simultaneously realizes all
elementary packet systems, elementary intersection packets, finite characters, and the finitely
many bad local objects. For a Brauer relation, finite Galois induction constructs the
semisimple positive and negative representations $R_{\mathfrak B,\lambda}^\pm$ over every
completion.

Under $(\mathrm{AI}_2)$, Book 184's norm-one theorem gives the signed equality (2.7) over an
algebraic closure at every coefficient place. Theorem 3.2 applies because the surviving
constituent has multiplicity one. Its Galois orbit is a singleton and its Schur multiplicity is
one, so it descends to $E_\lambda$ and actual cancellation holds there. The cocycle
interpretation in Section 3.4 proves clause 2. The constituent is a closed invariant summand of
a continuous representation and is absolutely irreducible after scalar extension, proving
clause 1.

For two Brauer relations, combine their induced lists. The exact elementary-overlap theorem and
the automorphic self-twist test make every entry of the combined Mackey Gram matrix embedding
independent. At the distinguished embedding the two expressions are both $[\rho]$, so their
difference has norm zero. Positivity makes the two scalar-extended classes equal, and Hom base
change descends the isomorphism. The remaining presentation and coordinate choices change no
induced isomorphism class. This proves clause 3.

For primes outside $S_0$, the cyclic-block calculation gives the algebraic rational function
(7.3). At the distinguished embedding it is the quadratic characteristic series of $\rho$, and
injectivity makes it the polynomial (9.2) over $E$. Actual cancellation gives both
unramifiedness and (9.3). At an auxiliary prime removed from $S_0$, the algebraic local
complement supplies the common unramified polynomial, and removal from $S$ includes the
separate purity certificate required in Section 8.3. The determinant-transfer calculation
becomes the actual identity (9.4). Restriction to the pure top packet and the residue-degree
power calculation give purity on the original good set. These arguments and the declared
certificates prove clauses 4--5.

Restrict a signed presentation to $G_{F_H}$. Mackey decomposition, Book 183's overlap theorem,
and the tensor identity factor out $r_{H,\lambda}$; the restricted finite-group Brauer relation
is $1_H$. Thus the restricted class is $[r_{H,\lambda}]$. Semisimplicity and faithful Hom
descent give the actual isomorphism (9.5). The two conjugation laws then follow from packet
conjugation and scalar transport, proving clauses 6--7.

For local compatibility, form the algebraic local Mackey objects (8.1). Global cancellation
restricts to decomposition groups. Weil--Deligne functoriality gives (8.3), and
Krull--Schmidt cancellation extracts the algebraic rank-two complement after one harmless
finite enlargement. This proves clause 8 without extending the local range beyond the packet
input. Complete splitting at $2$ makes every local term one copy of the selected SP pair; the
rank identity leaves exactly one copy. Equations (8.12)--(8.14) prove clause 9.

Finally, at the distinguished embedding the tensor identity is $[\rho]$. Uniqueness of the
effective constituent proves (9.8). Section 8.7 proves the integral boundary. All clauses
follow. $\square$

### 9.3 The exact interface to prime switching

The rational operation of changing coefficient prime can now begin without adding a family
hypothesis. Choose an actual place $\nu\mid3$ of the final coefficient field $E$ and set

$$
V=r_\nu:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(E_\nu).
\tag{9.9}
$$

This is selection of a member of (9.1), not a tensor product of the distinguished
$\ell$-adic member with $E_\nu$. The theorem supplies

$$
\det V=\chi_3,
\qquad
\operatorname{WD}_2(V)^{\mathrm{F\text{-}ss}}
\simeq D_2\otimes_EE_\nu,
\tag{9.10}
$$

so $V$ has the same rational rank-one monodromy, line, sign, and conductor-one record at $2$.
It also receives the common unramified local records at every prime certified by clause 8.

This handoff does not by itself imply the stronger minimal-support hypothesis used in Book 186,
Section 2.3. To assert that $V$ is unramified outside $\{2,3\}$, every prime in the finite
auxiliary set left by clause 8 must first be certified and removed. This is the same
clean-support boundary denoted $(\mathrm U)$ in Book 187.

No statement at the coefficient-prime place $3$ follows from (9.10). Crystallinity, Hodge
type, finite flatness, and the choice of a globally stable lattice are separate inputs or
constructions for the fixed-three integral theory. Likewise, rational nonzero $N_2$ does not
by itself determine the reduction of tame monodromy on a future lattice.

## 10. Dependency, hostile, and final audits

### 10.1 Dependency audit

The direct dependency row is

$$
\boxed{185\mid168,\ 180,\ 182,\ 183,\ 184.}
$$

| Source | Input used here | Strengthening not made |
|---|---|---|
| Book 168 | coefficient systems and algebraic local objects attached to the already constructed weight-two packets, including determinant, purity, and coefficient transport | no base-field family, canonical lattice, or moving-prime integral conclusion |
| Book 180 | multiplicity-one coefficient descent, coefficient cocycle effectivity, presentation comparison, induction/Mackey/tensor formulas, and Brauer--Nesbitt recognition | no packet overlap, positivity verification, or SP local object is imported |
| Book 182 | the conditional controlled SP top datum, the split evaluated packets at $2,3,\ell$, parity-complete basic attachment of candidate elementary descents, and its explicit controlled-seed and bridge-readiness boundaries | it does not construct the raw SP carrier, the auxiliary descent/type/return-map geometry, or the ambient semisimplicity needed only for uniform nonzero-monodromy SP preservation, and this book does not make that datum unconditional |
| Book 183 | selected elementary packets, exact elementary and conjugate-intersection identities, integral Brauer classes, determinant and local Mackey formulas, common virtual polynomials, purity, and the algebraic SP pair with its prior local-preservation certificate | no virtual class is called effective, no inadmissible automorphic transfer is inserted, and the later assembly is not a proof of raw packet preservation |
| Book 184 | under the explicit additional hypothesis $(\mathrm{AI}_2)$, the application-specific coefficient-independent Gram matrix, all-place norm-one positivity, actual characteristic-zero cancellation, coefficient covariance, and scalar relation independence | no completion-valued model or assembled family is imported; without $(\mathrm{AI}_2)$ only coefficient places away from two are available |

The work retained here is the assembly itself. Chapter 2 places every finite packet and character
in one algebraic ledger. Chapters 3--5 instantiate Book 180's coefficient-descent criterion over
each actual completion and prove completion-level relation independence. Chapters 6--8 recover
every elementary restriction, construct common Frobenius polynomials, determinant and purity,
and cancel the full algebraic local Mackey class, including the nonzero SP monodromy line, sign,
and conductor. None of those application-specific conclusions is delegated to the abstract
toolkit.

No changing-prime or fixed-three theorem enters the proof. The assembled family exports rational
SP data and the exact boundary at the coefficient prime; it does not manufacture crystallinity,
finite flatness, or a coherent lattice. Recognition by traces is used only after the relevant
representations exist, and density is never used to manufacture effectivity or a coefficient
cocycle.

### 10.2 Hostile mathematical audit

The construction withstands the following failure tests.

**Coefficient-two effectivity is not silently imported.** The all-place theorem assumes
$(\mathrm{AI}_2)$, exactly as Book 184 does. Without that hypothesis, Sections 2--8 assemble
only the members with $q_\lambda\ne2$; they do not manufacture a place above two from trace
data or from a coefficient-prime SP statement that Book 183 never supplied.

**Rational irreducibility is not coefficient-prime compatibility.** Even under
$(\mathrm{AI}_2)$, the member at $\lambda\mid2$ receives no semistable, de Rham, Hodge--Tate,
crystalline, finite-flat, or SP assertion at the rational place $2$. Once effectivity and
completion descent have produced the continuous representation, compactness supplies some
stable lattice. That lattice is not canonical, no signed integral cancellation has been
proved, and its characteristic-two reduction is not asserted to be irreducible or to retain
nonzero monodromy.

If the stronger $(\mathrm{CP\!\!-SP}_2)$ theorem were supplied, it would do two jobs. Book
184's reduction would use its nonzero monodromy to prove $(\mathrm{AI}_2)$ and hence
effectivity. After assembly, restriction recovery over $M$ and complete splitting of $2$ in
$M/\mathbf Q$ would identify the selected dyadic decomposition group with
$G_{\mathbf Q_2}$, transporting that coefficient-prime SP comparison to the assembled
two-adic member. This extra local conclusion would come from $(\mathrm{CP\!\!-SP}_2)$, not
from $(\mathrm{AI}_2)$, weak compatibility, or the assembly formalism.

**A trace field is not silently called a field of definition.** The coefficient ledger first
splits the finite realization algebras of the elementary terms. The new rank-two constituent is
then descended by Theorem 3.2. Its Schur obstruction is killed by multiplicity one, not by
trace containment.

**An invariant isomorphism class is not mistaken for an effective cocycle.** Section 3.4
exhibits the scalar two-cocycle and identifies its Brauer class with the division-algebra
obstruction. Coefficient one forces index one and makes the cocycle a coboundary.

**Two coefficient displays are compared on their overlap.** Hom base change descends a
nonzero intertwiner from a common overfield. The member is indexed by $\lambda$, not by an
unnamed embedding into an algebraic closure.

**Top-field agreement is not substituted for intersection agreement.** The norm and
restriction calculations use Book 183's theorem over
$M^{H\cap xJx^{-1}}$. A possible quotient character is retained as the explicit ratio
$\beta\alpha^{-1}$.

**A group-theoretic tower is not declared automorphically admissible.** No prime-cyclic descent
is performed in this book. Exact semisimple overlaps are imported from the theorem that proved
them by algebraic Frobenius comparison when automorphic ascent was unavailable.

**Virtual rank and polynomiality are not called existence.** Book 184's character norm supplies
the actual algebraically closed constituent. The present multiplicity-one theorem then supplies
the completion model. Each step has a different conclusion.

**Relation-independent polynomials are not substituted for relation-independent
representations.** Two relations are compared by the combined Gram norm. Norm zero gives
equality of their full semisimple classes, and Hom descent gives an isomorphism over
$E_\lambda$.

**Restriction recovery retains quotient information.** The proof of (6.7) restricts the
finite-group Brauer identity to $H$ and uses every Mackey double coset. The weaker top
restriction (6.8) is recorded only afterward.

**Purity is not inferred from the determinant.** It comes from residue-degree powers in the
pure top packet and is checked under every coefficient conjugation.

**The SP record is not replaced by a finite tame type.** The common pair has trivial finite
inertia and nonzero rank-one $N$. Its line and sign are named before the conductor-one formula
is calculated. No zero-monodromy finite-type branch occurs in the theorem.

**Final-family assembly is not used to prove a packet input.** Local Krull--Schmidt
cancellation begins with the actual packet pairs in (8.2). The existence, irreducibility, or
SP record of the resulting base-field member cannot certify those premises retroactively;
Book 183's independent raw-to-global certificate must already be in force.

**Prime-to-coefficient local theory is not applied at the coefficient prime.** Equation (8.11)
excludes $\lambda\mid2$. The prime-switch interface makes no claim at the new base place $3$
from a Weil--Deligne statement at $2$.

**A common finite bad set is not conductor support at two.** The weakly compatible family is
actually unramified outside $S_0$ away from coefficient characteristic, but this does not
prove $(\mathrm{Cond}_2)$. Proposition 8.1 uses the stronger support theorem only after it is
supplied, while Proposition 8.2 requires the actual finite local comparisons. Neither removes
a prime from almost-all Frobenius equality.

**The auxiliary packet factors are not all spherical.** A prime ramified in the controlled
top cannot split completely there, and nonsplit cyclic descent can produce tame principal or
dihedral factors from a spherical top factor.  The positive and negative local Mackey terms
may therefore remain ramified even when their genuine complement is unramified.

**Frobenius density does not compare different coefficient-adic limits.** Brauer--Nesbitt
applies to two existing semisimple representations in one coefficient topology.  Algebraic
agreement on the common good Frobenius set does not provide one continuous trace function on
inertia simultaneously valued in $E_{\lambda_0}$ and $E_\nu$, and it contains no monodromy
matrix at an exceptional prime.

**Rational cancellation is not reduced integrally.** No lattice or quotient tower is part of
Theorem 9.1. The rational line $\mathscr L_2$ is not declared saturated in an as-yet unchosen
lattice, and rational nonzero monodromy is not declared residually nonzero.

### 10.3 Scope and format audit

The manuscript proves the catalogued assembly: coefficient descent, Brauer independence,
continuity, common Frobenius polynomials, determinant, purity, restriction recovery,
conjugation, the distinguished member, and the global place-indexed compatible system. The SP
record at $2$ is carried as a full Weil--Deligne pair with nonzero rank-one monodromy, line,
sign, and conductor one. Proposition 8.2 proves the finite selected-member and family-wide
auxiliary support reductions without claiming their local-comparison premises. Integral
refinement is excluded explicitly.

Every substantial premise is either the conditional controlled SP top datum of Book 182, the
explicit additional hypothesis $(\mathrm{AI}_2)$, the abstract representation-theoretic toolkit
of Book 180, or an exact theorem of Books 168, 183, or 184. No conclusion of this book and no
later consumer is used as a premise. Arithmetic
Frobenius, induction, determinant, character
ratio, residue-degree, duality, and conductor conventions are consistent throughout. The table
of contents matches the heading structure, every displayed reference resolves within the
manuscript, and the narrative ends with the constructed mathematical package rather than with
future work.

### 10.4 Conclusion

The passage from potential automorphy to a family over the ground field has three genuinely
different obstructions. Brauer induction first replaces unavailable nonsolvable descent by a
signed expression assembled from elementary-field packets. Mackey theory then exposes the
intersection fields on which those signs can be tested. The exact overlap theorem and the
self-twist calculation make the signed character norm independent of the coefficient
embedding, and norm one makes the virtual rank-two class effective.

Effectivity still leaves a coefficient obstruction. An absolutely irreducible representation
over an algebraic closure can carry a nontrivial Schur class even when all of its traces lie in
the smaller field. Here the effective constituent occurs once in a difference already defined
over the completion. Galois orbits and Schur indices would repeat that occurrence. Since one
cannot be repeated nontrivially, the orbit is a singleton, the Schur index is one, and the
descent cocycle is effective. The constituent therefore has an honest model over every
$E_\lambda$.

The resulting members are independent of the Brauer relation and recover every elementary
packet after restriction. Their common arithmetic-Frobenius polynomials are quadratic with
cyclotomic constant term, their determinant is cyclotomic as a character, and their roots are
pure of weight one. Field conjugation organizes the elementary fixed fields; coefficient
conjugation transports the algebraic eigenvalues; the two actions commute without being
conflated.

At the distinguished coefficient place, the family contains the chosen representation
$\rho$. At the rational prime $2$, every member away from coefficient characteristic two has
the same SP object: nonzero rank-one monodromy, the line
$\ker N_2=\operatorname{im}N_2$, the selected Frobenius sign, and conductor exponent one.
These are the precise rational data needed for a later coefficient-prime selection.

Thus the elementary systems have been assembled into one coherent compatible system over
$\mathbf Q$:

$$
\boxed{
\mathcal R_E=\{r_\lambda\}_{\lambda\in\operatorname{Pl}_f(E)},
\qquad
\det r_\lambda=\chi_{q_\lambda},
\qquad
P_p(X)=X^2-a_pX+p.}
\tag{10.1}
$$

Conditional on both the controlled SP top datum and $(\mathrm{AI}_2)$, the all-place assembly is
complete at the rational level. Its final boundary is exact: the SP line exists over the
coefficient field, but no integral lattice, finite-flat quotient, or transition tower has been
chosen or inferred. Nor has the conductor-support premise $(\mathrm{Cond}_2)$ been proved;
Proposition 8.1 proves that it implies the selected-member support statement, and Proposition
8.2 reduces the selected and family-wide support conclusions to the exact finite auxiliary
local-comparison certificates $(\mathrm{AUX}_\nu)$ and $(\mathrm{AUX}_{\mathrm{all}})$.
Those certificates remain unproved. Their first missing theorem is the auxiliary-local clause
of the already-required controlled all-elementary attachment geometry, not an additional
Brauer-effectivity or post-assembly theorem.

The missing upstream construction of the controlled seed and the separate bridge-readiness
data, as well as the separate coefficient-two irreducibility hypothesis, remain outside this
theorem. Without $(\mathrm{AI}_2)$, only the partial assembly away from coefficient
characteristic two is proved.
