# Weil--Deligne Representations and Local Constants

## Contents

1. [Why a local parameter has two pieces](#1-why-a-local-parameter-has-two-pieces)
   - [The information to be separated](#11-the-information-to-be-separated)
   - [Standing conventions](#12-standing-conventions)
   - [A normalization ledger](#13-a-normalization-ledger)
2. [The local Weil group](#2-the-local-weil-group)
   - [From a profinite quotient to a discrete Frobenius direction](#21-from-a-profinite-quotient-to-a-discrete-frobenius-direction)
   - [The topology](#22-the-topology)
   - [Frobenius, tame inertia, and conjugation](#23-frobenius-tame-inertia-and-conjugation)
   - [Finite extensions and relative degree](#24-finite-extensions-and-relative-degree)
   - [Reciprocity normalization](#25-reciprocity-normalization)
3. [Linear representations of the Weil group](#3-linear-representations-of-the-weil-group)
   - [Continuity and finite inertia](#31-continuity-and-finite-inertia)
   - [Changing a Frobenius lift](#32-changing-a-frobenius-lift)
   - [Semisimplicity and what can fail](#33-semisimplicity-and-what-can-fail)
   - [Frobenius semisimplification](#34-frobenius-semisimplification)
4. [Weil--Deligne representations](#4-weil--deligne-representations)
   - [Why monodromy is an operator](#41-why-monodromy-is-an-operator)
   - [Definitions and elementary consequences](#42-definitions-and-elementary-consequences)
   - [Special blocks](#43-special-blocks)
   - [Classification of indecomposable objects](#44-classification-of-indecomposable-objects)
   - [Duals, determinants, and tensor products](#45-duals-determinants-and-tensor-products)
5. [The monodromy theorem and its dictionary](#5-the-monodromy-theorem-and-its-dictionary)
   - [Quasi-unipotence on inertia](#51-quasi-unipotence-on-inertia)
   - [Extracting the nilpotent operator](#52-extracting-the-nilpotent-operator)
   - [Reconstruction and dependence on choices](#53-reconstruction-and-dependence-on-choices)
   - [Examples and failure boundaries](#54-examples-and-failure-boundaries)
6. [Inertial types and ramification breaks](#6-inertial-types-and-ramification-breaks)
   - [What an inertial type remembers](#61-what-an-inertial-type-remembers)
   - [Break decomposition](#62-break-decomposition)
   - [Tame, wild, and unramified types](#63-tame-wild-and-unramified-types)
   - [Induced and dihedral types](#64-induced-and-dihedral-types)
7. [Artin, Swan, and monodromy conductors](#7-artin-swan-and-monodromy-conductors)
   - [The finite-inertia conductor](#71-the-finite-inertia-conductor)
   - [The monodromy correction](#72-the-monodromy-correction)
   - [Additivity, duality, and twists](#73-additivity-duality-and-twists)
   - [Induction and the different](#74-induction-and-the-different)
   - [A table of basic calculations](#75-a-table-of-basic-calculations)
8. [Additive characters and self-dual measure](#8-additive-characters-and-self-dual-measure)
   - [The conductor of an additive character](#81-the-conductor-of-an-additive-character)
   - [Annihilator lattices and self-duality](#82-annihilator-lattices-and-self-duality)
   - [Fourier inversion](#83-fourier-inversion)
   - [Scaling and trace](#84-scaling-and-trace)
9. [Rank-one local factors and Gauss sums](#9-rank-one-local-factors-and-gauss-sums)
   - [Multiplicative characters and zeta integrals](#91-multiplicative-characters-and-zeta-integrals)
   - [The local functional equation](#92-the-local-functional-equation)
   - [Exact Gauss-sum formula](#93-exact-gauss-sum-formula)
   - [Magnitude, quadratic sums, and examples](#94-magnitude-quadratic-sums-and-examples)
10. [Local factors for general parameters](#10-local-factors-for-general-parameters)
    - [The Euler factor](#101-the-euler-factor)
    - [The epsilon factor without monodromy](#102-the-epsilon-factor-without-monodromy)
    - [Deligne's monodromy correction](#103-delignes-monodromy-correction)
    - [Gamma factors](#104-gamma-factors)
    - [Special blocks and two-dimensional examples](#105-special-blocks-and-two-dimensional-examples)
11. [Duality, twists, and induction](#11-duality-twists-and-induction)
    - [Change of additive character and Haar measure](#111-change-of-additive-character-and-haar-measure)
    - [Unramified twists](#112-unramified-twists)
    - [Duality](#113-duality)
    - [Induction and the lambda constant](#114-induction-and-the-lambda-constant)
    - [Restriction and base change](#115-restriction-and-base-change)
12. [Functional equations and a normalization audit](#12-functional-equations-and-a-normalization-audit)
    - [The rank-one equation revisited](#121-the-rank-one-equation-revisited)
    - [The general local equation](#122-the-general-local-equation)
    - [Root numbers](#123-root-numbers)
    - [Consistency tests](#124-consistency-tests)
    - [Conclusion](#125-conclusion)

## 1. Why a local parameter has two pieces

### 1.1 The information to be separated

A finite extension of a nonarchimedean local field has two kinds of motion. Inertia moves points without changing the residue field, while Frobenius advances along the residue-field tower. A linear representation should remember both, but they have very different topological behavior. Inertia is compact and is detected at finite depth. The Frobenius direction is infinite cyclic and should admit arbitrary nonzero eigenvalues.

There is a second separation. An action may become unipotent on a sufficiently small subgroup of inertia. Its semisimple part is then finite, but the logarithm of the unipotent part carries essential information. Compressing that logarithm into a nilpotent operator produces a Weil--Deligne representation. This compression is not cosmetic: the ordinary finite-inertia action alone cannot distinguish a special parameter from a direct sum with the same semisimplified inertia.

Local factors provide the numerical tests of the package. The Euler factor sees Frobenius only on the subspace fixed by inertia and killed by monodromy. The Artin conductor measures the depth and size of the ramified action. The epsilon factor also sees an additive character, a Haar measure, Gauss sums, and the determinant of monodromy on a quotient. A correct theory must therefore keep a visible normalization ledger from the beginning.

This volume develops that ledger and proves the structural formulas used later for principal, special, and induced local parameters. The base field is always nonarchimedean once local constants enter. Archimedean parameters require different groups and gamma functions and are not part of the present subject.

### 1.2 Standing conventions

Let $K$ be a nonarchimedean local field, with normalized valuation, ring of integers, maximal ideal, uniformizer, and residue cardinality denoted by

$$
v_K,\qquad \mathcal O_K,\qquad \mathfrak p_K,\qquad \varpi_K,\qquad q.
$$

Thus

$$
|\varpi_K|_K=q^{-1},\qquad |x|_K=q^{-v_K(x)}.
$$

Fix a separable closure $\overline K$. Write $G_K$ for its group of $K$-automorphisms, $I_K$ for inertia, and $P_K$ for wild inertia. The residue quotient is canonically

$$
G_K/I_K\simeq\widehat{\mathbf Z}.
$$

Arithmetic Frobenius on the algebraic closure of the residue field is $x\mapsto x^q$. Our **geometric Frobenius** is its inverse. Choose a lift $\Phi\in G_K$ of geometric Frobenius. We normalize local reciprocity so that a uniformizer maps to geometric Frobenius. This convention is held fixed everywhere below.

For the algebraic theory, coefficients lie in an algebraically closed field $E$ of characteristic zero. When absolute values, Fourier transforms, and root numbers are discussed, $E=\mathbf C$. All representations are finite-dimensional. A representation of $W_K$ is continuous for the topology defined in Chapter 2 and the usual topology on the coefficient field.

### 1.3 A normalization ledger

The following five choices govern every formula:

$$
\begin{array}{c|c}
\text{object}&\text{choice}\\ \hline
\text{Frobenius}&\Phi=(x\mapsto x^q)^{-1}\text{ on residues}\\
\text{reciprocity}&\operatorname{rec}_K(\varpi_K)=\Phi\\
\text{absolute value}&|\varpi_K|=q^{-1}\\
\text{Weil norm}&|w|=q^{-\nu(w)},\quad \nu(\Phi)=1\\
\text{Fourier transform}&\widehat f(y)=\int_K f(x)\psi(xy)\,dx
\end{array}
$$

The first and second rows are a convention, not a theorem. Replacing geometric Frobenius by its inverse reciprocates unramified eigenvalues. Replacing reciprocity by its inverse has the same effect on characters. Either alternative supports a coherent theory; mixing them does not.

A useful test is the unramified character corresponding to $|\cdot|_K$. Under our reciprocity convention its value at $\Phi$ is $q^{-1}$. Accordingly, the defining monodromy relation will be

$$
r(w)Nr(w)^{-1}=|w|N,
$$

and in particular $r(\Phi)Nr(\Phi)^{-1}=q^{-1}N$.

## 2. The local Weil group

### 2.1 From a profinite quotient to a discrete Frobenius direction

The quotient $G_K/I_K$ is compact. A continuous complex character of that quotient is consequently constrained by compactness. Yet an unramified character of $K^\times$ is determined by an arbitrary nonzero value on $\varpi_K$. To make the two character theories match, one changes the topology in the Frobenius direction.

The **local Weil group** is the inverse image of the ordinary cyclic subgroup generated by geometric Frobenius:

$$
W_K=\{g\in G_K:g\bmod I_K\in\langle\Phi\rangle\}.
$$

There is an exact sequence

$$
1\longrightarrow I_K\longrightarrow W_K
\xrightarrow{\nu_K}\mathbf Z\longrightarrow0,
\qquad \nu_K(\Phi)=1.
\tag{2.1}
$$

Every $w\in W_K$ has a unique expression $w=i\Phi^n$ with $i\in I_K$ and $n\in\mathbf Z$ once the lift $\Phi$ has been chosen. The expression is not multiplicative as a direct product because Frobenius conjugates inertia.

The homomorphism

$$
|\cdot|:W_K\longrightarrow q^{\mathbf Z},
\qquad |w|=q^{-\nu_K(w)},
\tag{2.2}
$$

will be called the Weil norm. It is the character corresponding to the normalized absolute value under reciprocity.

### 2.2 The topology

As a set, $W_K$ is a dense subgroup of $G_K$. It does not carry the subspace topology. Its topology is characterized by the requirements that $I_K$ be open, retain its profinite topology, and that every coset $I_K\Phi^n$ be open. Equivalently,

$$
W_K=\coprod_{n\in\mathbf Z}I_K\Phi^n
$$

is a disjoint union of copies of $I_K$.

This topology makes $W_K$ locally compact and totally disconnected. It is not compact, because its quotient $\mathbf Z$ is discrete and infinite. A subgroup of $W_K$ is open precisely when its intersection with $I_K$ is open in $I_K$; no restriction is imposed by the discrete Frobenius coordinate.

Compact subsets have a simple description. A subset $C\subseteq W_K$ is relatively compact exactly when $\nu_K(C)$ is finite and its intersection with each relevant inertia coset is relatively compact. Since inertia is compact, every compactly supported locally constant function is supported on finitely many Frobenius degrees and is constant on cosets of some open subgroup of inertia. Integration therefore reduces to a finite sum of integrals on a profinite group.

After giving $I_K$ volume one, a left Haar measure is

$$
\int_{W_K}f(w)\,dw
=\sum_{n\in\mathbf Z}\int_{I_K}f(i\Phi^n)\,di.
\tag{2.2a}
$$

Conjugation by $\Phi$ is an automorphism of the compact group $I_K$ and preserves its normalized Haar measure. Hence $W_K$ is unimodular. This matters for induction: no modular correction is hidden in finite-index induction from $W_L$.

The group is neither discrete nor profinite. Its compact open subgroups are exactly the open subgroups of inertia. Thus compact-open level detects inertial depth, while the already discrete Frobenius direction imposes no boundedness on an unramified eigenvalue.

The distinction from the subspace topology is decisive. If $c\in\mathbf C^\times$, the rule

$$
I_K\mapsto1,\qquad \Phi\mapsto c
$$

defines a continuous character of $W_K$ for every $c$. It generally does not extend continuously to the compact quotient $\widehat{\mathbf Z}$. Thus the Weil group retains the algebraic relation between inertia and Frobenius while freeing the unramified eigenvalue.

### 2.3 Frobenius, tame inertia, and conjugation

The tame quotient of inertia has the form

$$
I_K/P_K\simeq\prod_{\ell\ne p}\mathbf Z_\ell(1),
$$

where $p$ is the residue characteristic. If $\tau$ denotes a compatible tame generator, geometric Frobenius satisfies

$$
\Phi\tau\Phi^{-1}=\tau^{q^{-1}}.
\tag{2.3}
$$

Here $q^{-1}$ means the inverse of $q$ in every prime-to-$p$ component of the tame quotient. This formula explains the scaling of monodromy. On a sufficiently small tame subgroup, a unipotent representation has the form $\exp(t(\sigma)N)$. Conjugating by $\Phi$ multiplies the tame coordinate by $q^{-1}=|\Phi|$, forcing the factor $q^{-1}$ in the monodromy relation.

A lift of Frobenius is never canonical in a ramified situation: every other lift has the form $i\Phi$ for $i\in I_K$. Statements about a Frobenius operator must therefore either be conjugacy-invariant or take place on inertia invariants, where $i$ acts trivially.

### 2.4 Finite extensions and relative degree

Let $L/K$ be finite separable, embedded in $\overline K$, and let $f=f(L/K)$. Then $W_L$ identifies with a subgroup of $W_K$. The degree maps satisfy

$$
\nu_K(w)=f\nu_L(w)\qquad(w\in W_L),
\tag{2.4}
$$

because geometric Frobenius over $L$ is the inverse of the $q^f$-power map. Consequently

$$
|w|_K=|w|_L\qquad(w\in W_L),
$$

since $q_L=q^f$. This identity is the reason restriction preserves the monodromy relation without any rescaling of $N$.

The index is

$$
[W_K:W_L]=[L:K].
\tag{2.5}
$$

To see this, choose a finite Galois extension containing the normal closure of $L$. Cosets of $W_L$ in $W_K$ act transitively on the $K$-embeddings of $L$, and the stabilizer of the distinguished embedding is $W_L$. The number of embeddings is $[L:K]$. This also shows that induction from $W_L$ to $W_K$ is finite-dimensional.

### 2.5 Reciprocity normalization

Local reciprocity gives a topological isomorphism

$$
\operatorname{rec}_K:K^\times\xrightarrow{\sim}W_K^{\mathrm{ab}}
$$

with our normalization $\operatorname{rec}_K(\varpi_K)=\Phi$. Units map onto the image of inertia, and $1+\mathfrak p_K^m$ maps into progressively deeper ramification groups. Hence a character $\chi$ of $W_K$ corresponds to

$$
\chi_K(x)=\chi(\operatorname{rec}_K(x)).
$$

We use the same letter for the two characters when no confusion can arise. In particular,

$$
\chi(\Phi)=\chi_K(\varpi_K).
\tag{2.6}
$$

Under a finite extension $L/K$, the inclusion $W_L^{\mathrm{ab}}\to W_K^{\mathrm{ab}}$ corresponds to the norm $N_{L/K}:L^\times\to K^\times$. Thus restriction of a character from $W_K$ to $W_L$ corresponds to composition with the norm. This compatibility will control twists under base change.

## 3. Linear representations of the Weil group

### 3.1 Continuity and finite inertia

A **Weil representation** over $E$ is a continuous homomorphism

$$
r:W_K\longrightarrow\operatorname{GL}_E(V)
$$

whose restriction to inertia has open kernel. Since $I_K$ is compact, an open kernel has finite index, and therefore $r(I_K)$ is finite. Conversely, if $r(I_K)$ is finite and the restriction is continuous, its kernel is open. The condition leaves $r(\Phi)$ entirely unrestricted except for its conjugation action on the finite group $r(I_K)$.

If $E$ is given the discrete topology, continuity already forces every vector to have an open stabilizer; finite dimensionality then gives one open subgroup fixing all of $V$. With the usual topology on $\mathbf C$ or an $\ell$-adic coefficient field, compactness alone need not force finite image. The finite-inertia condition is therefore part of the definition, not a consequence of finite dimension.

Every irreducible Weil representation has finite inertia automatically once it is admissible in the preceding sense. It can still have infinite image because an eigenvalue of Frobenius can have infinite order.

### 3.2 Changing a Frobenius lift

Let $\Phi'=i\Phi$ with $i\in I_K$. On $V^{I_K}$,

$$
r(\Phi')=r(\Phi).
$$

Thus the characteristic polynomial of Frobenius on inertia invariants is canonical. On the whole of $V$, $r(\Phi')$ can have different eigenvalues; the invariant-space restriction is essential.

More generally, if $U\subseteq V$ is stable under $W_K$ and inertia acts trivially on $U$, then the operator $r(\Phi)|_U$ is independent of the lift. The spaces $V^{I_K}$ and $(\ker N)^{I_K}$ used later have exactly this property.

### 3.3 Semisimplicity and what can fail

Because $r(I_K)$ is finite and the coefficient characteristic is zero, the restriction $r|_{I_K}$ is semisimple. The whole representation need not be semisimple. The simplest counterexample is unramified: take inertia to act trivially and let

$$
r(\Phi)=
\begin{pmatrix}
1&1\\0&1
\end{pmatrix}.
$$

This is a continuous Weil representation with a nonsplit invariant line. Inertia supplies no obstruction because the Frobenius quotient is infinite cyclic, whose representations need not be semisimple.

For irreducible representations the issue disappears, but extension data can occur in reducible ones. Local Euler factors depend only on the characteristic polynomial on a canonical subspace and therefore ignore the unipotent part of Frobenius. This motivates a controlled semisimplification that does not alter inertia or monodromy.

### 3.4 Frobenius semisimplification

Choose a Frobenius lift and write the multiplicative Jordan decomposition

$$
r(\Phi)=su=us,
$$

with $s$ semisimple and $u$ unipotent. After replacing $\Phi$ by a positive power, its conjugation action on the finite group $r(I_K)$ is trivial. It follows that the unipotent part $u$ commutes with $r(I_K)$. The same conclusion for the original lift follows from uniqueness of Jordan decomposition. Thus $u$ commutes with all of $r(W_K)$.

Define

$$
r^{\mathrm{F\!-!ss}}(w)=r(w)u^{-\nu_K(w)}.
\tag{3.1}
$$

This is a representation because $u$ is central in the image. It agrees with $r$ on inertia and sends $\Phi$ to $s$. A different Frobenius lift gives an isomorphic representation, so the isomorphism class is canonical.

If $(r,N)$ is a Weil--Deligne representation, then $u$ also commutes with $N$. Indeed, conjugation by $r(\Phi)$ sends $N$ to the eigenvector $q^{-1}N$; in the Jordan decomposition of this conjugation operator, its unipotent part must fix every genuine eigenvector. Hence $(r^{\mathrm{F\!-\!ss}},N)$ still satisfies (4.1). Frobenius semisimplification therefore retains monodromy without alteration.

**Proposition 3.1.** Frobenius semisimplification is exact on direct sums, commutes with duality and restriction to finite extensions, preserves the characteristic polynomial on $V^{I_K}$, and is idempotent.

**Proof.** Direct sums and duals preserve multiplicative Jordan components. On restriction to $W_L$, a Frobenius over $L$ has degree $f$ in $W_K$ and may have the form $i\Phi^f$. The central unipotent factor in its image is $u^f$. After removing it, a positive power of the remaining operator is a product of commuting semisimple operators from a finite inertial image and a power of $s$; it is semisimple. In characteristic zero an operator whose positive power is semisimple is itself semisimple. Thus formula (3.1) agrees with Frobenius semisimplification after restriction, even when the Frobenius lift carries an inertial correction. The invariant space is unchanged because inertia is unchanged, and removing a commuting unipotent factor preserves the characteristic polynomial. Applying the construction twice does nothing. $\square$

Frobenius semisimplification is not ordinary semisimplification of the whole representation. It retains the finite inertial representation exactly. That distinction will matter for inertial types.

For the unramified Jordan block of Section 3.3, the construction replaces Frobenius by the identity and turns the nonsplit extension into $1\oplus1$. By contrast, if inertia acts through two distinct characters exchanged by Frobenius, semisimplification retains that exchange; it does not diagonalize inertia and Frobenius simultaneously. It also never changes $N$. A special block therefore remains indecomposable, because its extension data reside in monodromy rather than in a unipotent Frobenius matrix.

## 4. Weil--Deligne representations

### 4.1 Why monodromy is an operator

Suppose a continuous action becomes unipotent on an open subgroup of inertia. On a sufficiently small subgroup every matrix is close to the identity, so logarithms turn multiplication into addition. The tame quotient is one-dimensional in each prime-to-$p$ direction; consequently all logarithms are scalar multiples of one nilpotent matrix. Recording that matrix is more efficient than retaining the entire unipotent subgroup.

Frobenius rescales the tame coordinate. The nilpotent matrix must therefore transform by the inverse scale. This is the source of the relation $r(w)Nr(w)^{-1}=|w|N$. It is forced by conjugation, not appended as an analogy.

### 4.2 Definitions and elementary consequences

A **Weil--Deligne representation** over $E$ is a pair $D=(r,N)$ consisting of a Weil representation $r$ on $V$ and a nilpotent endomorphism $N$ satisfying

$$
r(w)Nr(w)^{-1}=|w|N\qquad(w\in W_K).
\tag{4.1}
$$

A morphism intertwines both $r$ and $N$. The object is Frobenius-semisimple if $r(\Phi)$ is semisimple. We usually replace a parameter by its Frobenius semisimplification before computing its isomorphism class.

Several consequences are immediate but important. Since $|i|=1$ for $i\in I_K$, the operator $N$ commutes with inertia. Hence $\ker N$, $\operatorname{im}N$, and every step of the monodromy filtration are inertia-stable. For Frobenius,

$$
r(\Phi)N=q^{-1}Nr(\Phi).
\tag{4.2}
$$

Thus if $v$ is a Frobenius eigenvector of eigenvalue $\alpha$, then $Nv$, when nonzero, has eigenvalue $q^{-1}\alpha$. Nonzero monodromy therefore organizes eigenvalues into $q^{-1}$-strings.

If $r$ is irreducible, then $N=0$. Indeed, $\ker N$ is nonzero because $N$ is nilpotent, and it is $W_K$-stable by (4.1). Irreducibility forces $\ker N=V$, hence $N=0$. Nonzero monodromy belongs to indecomposable but reducible underlying Weil representations.

The nilpotent operator carries a canonical increasing **monodromy filtration** $M_\bullet V$, characterized by

$$
N(M_jV)\subseteq M_{j-2}V
$$

and isomorphisms

$$
N^j:\operatorname{gr}_j^M V\xrightarrow{\sim}
\operatorname{gr}_{-j}^M V
\qquad(j\geq0).
\tag{4.2a}
$$

For a Jordan block of length $m$, center the basis so that $e_j$ has filtration index $2j-(m-1)$. Then $N e_j=e_{j-1}$ lowers the index by two. Direct sums of blocks define the filtration in general. Uniqueness follows because the primitive subspaces recover the starting vectors and lengths of all Jordan blocks. Relation (4.1) makes the filtration $W_K$-stable: conjugating $N$ by a nonzero scalar does not change its Jordan filtration.

The filtration remembers more than the rank of $N$. In dimension four, blocks of sizes $3+1$ and $2+2$ both give rank two, but their graded dimensions differ. Their conductors happen to have the same monodromy correction when inertia is trivial, since both have two blocks, yet tensor powers distinguish them. Neither rank nor conductor determines monodromy.

### 4.3 Special blocks

For $m\geq1$, define $\operatorname{Sp}_m$ on a basis $e_0,\dots,e_{m-1}$ by

$$
Ne_0=0,\qquad Ne_j=e_{j-1}\quad(j\geq1),
$$

and

$$
r(w)e_j=|w|^{(m-1)/2-j}e_j.
\tag{4.3}
$$

The half-powers are unambiguous over an algebraically closed coefficient field after choosing $q^{1/2}$; $|w|^{1/2}=q^{-\nu(w)/2}$. Equation (4.1) follows because the exponent on $e_{j-1}$ exceeds that on $e_j$ by one.

For any Weil representation $\rho$, put

$$
\operatorname{Sp}_m(\rho)=\rho\otimes\operatorname{Sp}_m,
$$

with monodromy $1\otimes N$. If $\rho$ is irreducible, this is indecomposable. Its kernel of monodromy is $\rho\otimes Ee_0$, on which Frobenius acts as

$$
\rho(\Phi)q^{-(m-1)/2}.
\tag{4.4}
$$

The centered exponents make $\det(\operatorname{Sp}_m)$ trivial and give

$$
\det\operatorname{Sp}_m(\rho)=(\det\rho)^m.
$$

An uncentered convention is also common, but it shifts every Euler factor. Formula (4.3) fixes our choice exactly.

### 4.4 Classification of indecomposable objects

**Theorem 4.1.** Every Frobenius-semisimple Weil--Deligne representation over an algebraically closed field of characteristic zero is a direct sum, uniquely up to order, of objects

$$
\operatorname{Sp}_m(\rho),
$$

where $m\geq1$ and $\rho$ is an irreducible Weil representation. Each displayed object is indecomposable.

**Proof strategy.** Regard $N$ as a map from $r$ to $r\otimes|\cdot|^{-1}$. Decompose the semisimple Weil representation into irreducibles and follow the strings linked by $N$. Nilpotence makes every string finite; ordinary Jordan theory supplies the length, and Schur's lemma makes each nonzero link unique up to a scalar.

**Proof.** Frobenius semisimplicity and finite inertial image imply semisimplicity of $r$: a $W_K$-stable complement can be constructed on each finite inertia-isotypic orbit, where a power of Frobenius is semisimple and central. Decompose $V$ into irreducible constituents. Relation (4.1) says that $N$ carries a constituent isomorphic to $\sigma$ into one isomorphic to $\sigma\otimes|\cdot|$. Hence constituents split into finite chains under twisting by $|\cdot|$.

On a fixed chain, choose a terminal constituent in $\ker N$ and lift it successively through the images of powers of $N$. Schur's lemma says each nonzero map between matching irreducibles is scalar; rescaling the lifts makes those scalars one. This produces a block with the form (4.3), tensored with the centered irreducible representation $\rho$. Jordan block lengths are recovered from the dimensions of $\ker N^j$, so the multiset of blocks is unique. A block has no nontrivial idempotent commuting with both its irreducible coefficient action and its single Jordan chain, hence is indecomposable. $\square$

The theorem is a classification of pairs. The underlying Weil representation of a special block is a direct sum; its indecomposability is carried by $N$.

### 4.5 Duals, determinants, and tensor products

The dual is

$$
(r,N)^\vee=(r^\vee,-{}^tN).
\tag{4.5}
$$

The minus sign is forced by differentiating the invariant evaluation pairing. It does not change the isomorphism class of a single Jordan block. In fact

$$
\operatorname{Sp}_m(\rho)^\vee\simeq\operatorname{Sp}_m(\rho^\vee).
$$

For two parameters, define

$$
(r_1,N_1)\otimes(r_2,N_2)
=\bigl(r_1\otimes r_2,\ N_1\otimes1+1\otimes N_2\bigr).
\tag{4.6}
$$

The two summands commute and are nilpotent, and relation (4.1) holds. Direct sums use block-diagonal monodromy. Exterior and symmetric powers inherit the differentiated operator in the same manner.

The determinant has no monodromy: the induced operator on the top exterior power is $\operatorname{tr}(N)=0$. Thus $\det D$ is the Weil character $\det r$. This determinant, transported through reciprocity, is the character appearing when the additive character is rescaled.

## 5. The monodromy theorem and its dictionary

### 5.1 Quasi-unipotence on inertia

The pair $(r,N)$ is designed to encode a continuous representation whose inertia is not finite but is potentially unipotent. Let $F$ be a finite extension of $\mathbf Q_\ell$, where $\ell\ne p$, and let

$$
\rho:G_K\longrightarrow\operatorname{GL}_F(V)
$$

be continuous. The local monodromy theorem states that some open subgroup $J\subseteq I_K$ acts unipotently.

**Theorem 5.1 (local monodromy).** Under the preceding hypotheses, there is an open subgroup $J\subseteq I_K$ such that every eigenvalue of $\rho(\sigma)$ is $1$ for $\sigma\in J$. Equivalently, $\rho|_{I_K}$ is quasi-unipotent.

**Proof strategy.** Wild inertia is pro-$p$, whereas sufficiently small neighborhoods of the identity in $\operatorname{GL}_n(F)$ are pro-$\ell$; their intersection is trivial. Thus wild inertia has finite image after shrinking. The remaining tame image is controlled by a pro-$\ell$ cyclic quotient. Geometric Frobenius conjugation sends a tame generator to its $q^{-1}$-power. This forces every eigenvalue of the tame generator to have finite-order semisimple part; after passing to an open subgroup only the unipotent part remains.

**Decisive details.** Choose a stable lattice and a sufficiently deep principal congruence subgroup $C$, which is pro-$\ell$ and torsion-free after further shrinking. The image of an open subgroup of wild inertia in $C$ is both pro-$p$ and pro-$\ell$, hence trivial. The tame quotient that can meet $C$ is therefore its $\ell$-primary factor $\mathbf Z_\ell(1)$. Let $T$ be the image of a topological generator. Conjugating by inverse Frobenius shows that $T$ and $T^q$ are conjugate, so their eigenvalue multisets agree. Iteration and finite dimension make every semisimple eigenvalue periodic under $z\mapsto z^q$, hence a root of unity. Raising $T$ to a common multiple kills all these roots of unity, leaving a unipotent matrix. The corresponding subgroup is open. $\square$

The restriction $\ell\ne p$ is essential to this argument. At the residue characteristic, inertia can carry much richer analytic variation and need not become unipotent in this simple form.

### 5.2 Extracting the nilpotent operator

Choose a nonzero continuous tame coordinate

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell
$$

that vanishes on wild inertia and is normalized so that

$$
t_\ell(w\sigma w^{-1})=|w|t_\ell(\sigma)
\tag{5.1}
$$

for $w\in W_K$ and $\sigma$ in a sufficiently small inertial subgroup. This normalization matches the chosen geometric Frobenius.

On an open subgroup $J$ where $\rho$ is unipotent, the logarithm is a finite sum. Since $J$ maps into a one-dimensional tame quotient, there is a unique nilpotent $N$ such that

$$
\rho(\sigma)=\exp\bigl(t_\ell(\sigma)N\bigr)
\qquad(\sigma\in J).
\tag{5.2}
$$

Conjugating (5.2) by $\rho(w)$ and using (5.1) gives

$$
\rho(w)N\rho(w)^{-1}=|w|N.
$$

Define, first on $J$ and then uniquely on $W_K$, the finite-inertia part by removing this exponential. The resulting representation $r$ has finite image on inertia and satisfies the same scaling relation with $N$. Thus $\rho$ determines a Weil--Deligne representation.

The uniqueness in (5.2) follows because $t_\ell(J)$ contains a nonzero open subgroup of $\mathbf Z_\ell$: evaluating at one element with nonzero coordinate determines $N$, and the homomorphism law makes every other logarithm proportional to it.

### 5.3 Reconstruction and dependence on choices

Conversely, let $(r,N)$ be a Weil--Deligne representation over $F$. On a sufficiently small subgroup of inertia on which $r$ is trivial, set

$$
\rho(\sigma)=\exp\bigl(t_\ell(\sigma)N\bigr).
\tag{5.3}
$$

Together with $r$ on a choice of coset representatives, relation (4.1) makes this into a continuous action after a finite extension of $K$. The constructions in (5.2) and (5.3) are inverse up to isomorphism.

Scaling $t_\ell$ by $c\in\mathbf Z_\ell^\times$ scales $N$ by $c^{-1}$. The pairs are isomorphic after the corresponding change of chosen coordinate in the reconstruction; properties such as $N=0$, its ranks, conductor, and special-block lengths are independent of the choice. Choosing a different Frobenius lift changes representatives but not the isomorphism class.

The precise categorical statement is therefore an equivalence between continuous representations with quasi-unipotent inertia and Weil--Deligne representations after fixing a tame coordinate, with Frobenius semisimplification on the latter side when only semisimplified local data are retained.

The removal of the exponential can be made explicit. Extend the tame coordinate from a small subgroup by choosing a function $t:W_K\to F$ satisfying

$$
t(w_1w_2)=t(w_1)|w_2|^{-1}+t(w_2)
\tag{5.3a}
$$

on the subgroup generated by that inertia and Frobenius. Then

$$
r(w)=\rho(w)\exp\bigl(-t(w)N\bigr)
\tag{5.3b}
$$

is multiplicative: the crossed-homomorphism rule (5.3a) and the conjugation rule for $N$ cancel the exponential terms. On small inertia, (5.3b) removes (5.2), so $r$ is trivial there and has finite inertial image. A different extension of $t$ changes the resulting pair by an isomorphism.

This calculation also identifies a common mistake. One cannot put $r=\rho\exp(-t_\ell N)$ on all of $W_K$ without extending $t_\ell$ by the crossed rule. An ordinary homomorphism on the whole group would be incompatible with Frobenius conjugation.

### 5.4 Examples and failure boundaries

An unramified action has $N=0$ and trivial finite inertia. A finite ramified action also has $N=0$; all its inertia is stored in $r$. A nontrivial extension with matrices

$$
\rho(\sigma)=
\begin{pmatrix}
1&t_\ell(\sigma)\\0&1
\end{pmatrix}
$$

has trivial finite inertia and rank-one $N$. It is the basic special block.

Finite inertia and nonzero monodromy can coexist. If a finite character $\theta$ of inertia extends to $W_K$, tensoring the preceding example by $\theta$ leaves $N$ nonzero while changing the inertial type. Thus “nonzero monodromy” does not mean “unramified parameter.”

Finally, a representation with infinite semisimple inertial image is not encoded by the present finite-inertia definition. The monodromy theorem rules this out in the prime-to-$p$ situation above, but it must not be assumed for arbitrary coefficient topology or residue-characteristic coefficients.

## 6. Inertial types and ramification breaks

### 6.1 What an inertial type remembers

An **inertial type** is an isomorphism class of finite-image representations

$$
\tau:I_K\longrightarrow\operatorname{GL}_E(V)
$$

that extend to a Weil representation. The extension condition is substantive: conjugation by Frobenius must carry $\tau$ to an isomorphic representation. Equivalently,

$$
\tau^\Phi(i)=\tau(\Phi i\Phi^{-1})
$$

must be isomorphic to $\tau$.

For $D=(r,N)$, its inertial type is $r|_{I_K}$. It does not remember the eigenvalues of Frobenius and it does not remember $N$. Consequently infinitely many unramified twists have the same inertial type, and the split object $1\oplus|\cdot|^{-1}$ with $N=0$ has the same inertial type as a special block with $N\ne0$. This is the central counterexample to treating type as a complete parameter.

### 6.2 Break decomposition

Because inertia has finite image under $r$, the upper ramification filtration acts through a finite quotient. There is a canonical decomposition

$$
V=\bigoplus_{u\geq0}V(u)
\tag{6.1}
$$

over the finitely many breaks, characterized by

$$
V(u)^{I_K^v}=
\begin{cases}
0,&0<v\leq u,\\
V(u),&v>u,
\end{cases}
$$

for $u>0$, while $V(0)$ is the tame part. One constructs (6.1) from the commuting averaging projectors attached to the finite upper ramification groups. Exactness of invariants in characteristic zero makes the successive complements canonical.

Frobenius preserves each break because it normalizes every upper ramification group. The nilpotent operator also preserves each break because it commutes with inertia. Thus conductor and monodromy can be computed break by break.

The Swan conductor is the weighted depth

$$
\operatorname{Sw}(r)=\sum_{u>0}u\dim V(u).
\tag{6.2}
$$

Although the breaks of a nonabelian representation may be rational, the total is a nonnegative integer. That integrality is inherited from the Artin character, not from termwise integrality.

At finite level the decomposition can be constructed from averaging projectors. Let $0<u_1<\cdots<u_t$ be the positive jumps of the image filtration. Averaging over the normal groups $I^{u_j+}$ gives commuting idempotents with nested images. Their successive differences project onto the spaces $V(u_j)$, while depth zero is split off from the tame quotient. The fixed-space characterization shows that the result is independent of the finite quotient used. It also gives

$$
\operatorname{codim}V^{I^v}
=\sum_{u\geq v}\dim V(u),
$$

and integrating over $v>0$ proves (6.2).

Breaks behave well under direct sums and duals, but not under arbitrary tensor products. A wild character and its inverse have the same positive break, while their tensor product is trivial. This is the simplest warning against replacing an inertial type by a multiset of break numbers without retaining the characters themselves.

### 6.3 Tame, wild, and unramified types

The type is **unramified** if inertia acts trivially, **tame** if wild inertia acts trivially, and **wild** otherwise. For a tame type, every positive break vanishes. Its ramification is measured entirely by the codimension of inertia invariants.

A nontrivial tame character has conductor one. A direct sum of $d$ nontrivial tame characters with no invariant line has conductor $d$. By contrast, a character with unique positive break $u$ has Swan conductor $u$ and Artin conductor $u+1$.

There is no formula for the conductor of a tensor product using only the two conductor integers. If characters $\chi_1$ and $\chi_2$ have the same deepest restriction, their product may cancel there; if their deepest restrictions differ, the larger break survives. The full break decomposition, not just its weighted sum, controls twisting.

### 6.4 Induced and dihedral types

Let $L/K$ be finite separable and let $\theta$ be a character of $W_L$. The induced representation

$$
\rho=\operatorname{Ind}_{W_L}^{W_K}\theta
$$

has dimension $[L:K]$. For a quadratic extension, it is irreducible exactly when $\theta$ is not fixed by the nontrivial $K$-automorphism of $L$. In that case its restriction to $W_L$ is

$$
\theta\oplus\theta^\sigma,
$$

and its inertial type is obtained by the same restriction-and-induction process on inertia, with separate behavior according as $L/K$ is unramified or ramified.

If $L/K$ is unramified quadratic, $I_L=I_K$, so the type is simply $\theta|_I\oplus\theta^\sigma|_I$. If $L/K$ is ramified quadratic, $I_L$ has index two in $I_K$, and the type is induced from $I_L$. These two types can have the same dimension and comparable conductor but different restriction structure. The distinction is visible to induction constants and Gauss sums.

## 7. Artin, Swan, and monodromy conductors

### 7.1 The finite-inertia conductor

Let $r$ be a Weil representation with finite inertia. Choose a finite Galois quotient through which inertia acts, with lower ramification groups $G_i$. Define

$$
a_K(r)=\sum_{i\geq0}\frac{|G_i|}{|G_0|}
\operatorname{codim}V^{G_i},
\tag{7.1}
$$

and

$$
\operatorname{Sw}_K(r)=\sum_{i\geq1}\frac{|G_i|}{|G_0|}
\operatorname{codim}V^{G_i}.
\tag{7.2}
$$

Then

$$
a_K(r)=\operatorname{codim}V^{I_K}+\operatorname{Sw}_K(r).
\tag{7.3}
$$

Upper-numbering compatibility with quotients proves independence of the chosen finite extension. The break decomposition gives the equivalent formula (6.2). These conductors are nonnegative integers and are additive in direct sums and short exact sequences.

### 7.2 The monodromy correction

The finite-inertia conductor does not see $N$. The correct conductor of $D=(r,N)$ is

$$
\boxed{
a_K(D)=a_K(r)+\dim V^{I_K}-\dim(\ker N)^{I_K}.}
\tag{7.4}
$$

Because $N$ commutes with inertia, $(\ker N)^{I_K}=\ker(N|_{V^{I_K}})$. Hence

$$
a_K(D)=\operatorname{Sw}_K(r)+\dim V-\dim(\ker N)^{I_K}.
\tag{7.5}
$$

Formula (7.5) separates wild depth from the total defect of the Euler-factor space.

For an unramified special block $\operatorname{Sp}_m(\chi)$ with $\chi$ unramified, $a(r)=0$, $\dim V^I=m$, and $\dim(\ker N)^I=1$. Therefore

$$
a\bigl(\operatorname{Sp}_m(\chi)\bigr)=m-1.
\tag{7.6}
$$

For a ramified character $\chi$, no line has inertia invariants and the monodromy correction vanishes. Since the underlying representation is the direct sum of $m$ unramified twists of $\chi$,

$$
a\bigl(\operatorname{Sp}_m(\chi)\bigr)=m\,a(\chi).
\tag{7.7}
$$

This jump is not a discontinuity in the definition: it reflects the disappearance of the entire invariant space after a ramified twist.

More generally, let $\rho$ be irreducible. If $\rho$ is ramified, then $\rho^I=0$ and

$$
a\bigl(\operatorname{Sp}_m(\rho)\bigr)=m\,a(\rho).
\tag{7.7a}
$$

If $\rho$ is unramified, irreducibility forces $\dim\rho=1$, giving (7.6). Hence (7.6) and (7.7a) calculate every indecomposable block from Theorem 4.1, and additivity calculates every Frobenius-semisimple parameter.

This also proves that $a(D)=0$ exactly when $N=0$ and inertia acts trivially. Every unramified block of length $m$ contributes $m-1$; every ramified block contributes the positive integer $m a(\rho)$.

### 7.3 Additivity, duality, and twists

The conductor is additive on direct sums. It is also invariant under duality:

$$
a(D^\vee)=a(D),\qquad \operatorname{Sw}(r^\vee)=\operatorname{Sw}(r).
\tag{7.8}
$$

Indeed, finite-group fixed-space codimensions agree for a representation and its dual, and the Jordan block lengths of $N$ and $-{}^tN$ agree.

An unramified twist changes neither inertia nor $N$, so

$$
a(D\otimes\chi)=a(D)
\tag{7.9}
$$

when $\chi$ is unramified. A ramified twist can create or destroy inertia invariants and can cancel wild characters. No general equality in terms of $a(D)$ and $a(\chi)$ alone is valid.

Tensor products are controlled by breaks. If $r_1$ has one break $u_1$ and $r_2$ one break $u_2$ with $u_1\ne u_2$, then $r_1\otimes r_2$ has break $\max(u_1,u_2)$. When the breaks coincide, cancellation may lower the result. This explains exactly why equal-depth twists require character-level information.

### 7.4 Induction and the different

Let $L/K$ be finite separable, with residue degree $f$, ramification index $e$, and different exponent $d=v_L(\mathfrak D_{L/K})$. For a finite-inertia Weil representation $U$ of $W_L$,

$$
\boxed{
a_K\bigl(\operatorname{Ind}_{W_L}^{W_K}U\bigr)
=f\bigl(a_L(U)+d\dim U\bigr).}
\tag{7.10}
$$

The first term transports the old ramification scale; the second is the cost of permuting the embeddings of $L$. For $U=1$, this gives $fd$, the discriminant exponent over $K$.

**Proof strategy.** Realize the representation in a common finite Galois extension. Restrict the Artin character over $K$ to the subgroup over $L$. The displacement functions agree away from the identity after the residue-degree factor $f$ is inserted. At the identity, transitivity of the different leaves $fd$ copies of the regular character. Frobenius reciprocity then pairs the first part with $a_L(U)$ and the regular part with $\dim U$, giving (7.10).

For a Weil--Deligne representation, induction carries $N$ pointwise on the induced function space. The same formula remains true with $a(U)$ interpreted by (7.4). One way to verify the monodromy term is to compute inertia invariants by Mackey decomposition: inertia has $f$ orbits on the embeddings of $L$, and each orbit contributes one copy of the corresponding $I_L$-invariant kernel. The resulting correction is exactly the one already included in (7.10).

### 7.5 A table of basic calculations

With all characters viewed as Weil characters through reciprocity:

$$
\begin{array}{c|c|c|c}
D&\dim(\ker N)^I&\operatorname{Sw}(D)&a(D)\\ \hline
\text{unramified }\chi&1&0&0\\
\text{nontrivial tame }\chi&0&0&1\\
\chi\text{ of unique break }u>0&0&u&u+1\\
\operatorname{Sp}_m(\chi),\ \chi\text{ unramified}&1&0&m-1\\
\operatorname{Sp}_m(\chi),\ \chi\text{ ramified}&0&m\operatorname{Sw}(\chi)&m a(\chi)\\
\operatorname{Ind}_{W_L}^{W_K}1&\text{depends on }L/K&f(d-e+1)&fd
\end{array}
$$

The final Swan entry follows by subtracting the tame codimension $f(e-1)$ from $fd$. It vanishes exactly for a tame extension. The table is also a set of normalization tests: omitting $f$ in induction or the monodromy correction in a special block immediately gives a false row.

## 8. Additive characters and self-dual measure

### 8.1 The conductor of an additive character

Let $\psi:K\to\mathbf C^\times$ be a nontrivial continuous additive character. Its **conductor exponent** $n(\psi)$ is the unique integer such that the largest fractional ideal on which $\psi$ is trivial is

$$
\mathfrak p_K^{-n(\psi)}.
\tag{8.1}
$$

Thus conductor zero means that $\psi$ is trivial on $\mathcal O_K$ but not on $\varpi_K^{-1}\mathcal O_K$. This sign convention is chosen so that, for $\psi_a(x)=\psi(ax)$,

$$
n(\psi_a)=n(\psi)+v_K(a).
\tag{8.2}
$$

A positive value means a less oscillatory character with a larger kernel. Some accounts attach the opposite integer to the same kernel; formula (8.1) removes the ambiguity.

Every nontrivial additive character is $\psi_a$ for a unique $a\in K^\times$ once one base character has been fixed. This follows from self-duality of the additive group of $K$.

### 8.2 Annihilator lattices and self-duality

For a fractional ideal $A$, define

$$
A^\perp=\{y\in K:\psi(xy)=1\text{ for all }x\in A\}.
$$

From (8.1),

$$
(\mathfrak p_K^m)^\perp=\mathfrak p_K^{-m-n(\psi)}.
\tag{8.3}
$$

A Haar measure $dx$ is **self-dual for $\psi$** if the Fourier transform

$$
\widehat f(y)=\int_Kf(x)\psi(xy)\,dx
\tag{8.4}
$$

satisfies Fourier inversion with no scalar. Such a measure is unique. Applying (8.4) to the characteristic function of a lattice shows that

$$
\widehat{\mathbf1_A}(y)=\operatorname{vol}(A)\mathbf1_{A^\perp}(y).
\tag{8.5}
$$

Fourier inversion forces $\operatorname{vol}(A)\operatorname{vol}(A^\perp)=1$. Taking $A=\mathcal O_K$ and using (8.3) gives

$$
\boxed{\operatorname{vol}_\psi(\mathcal O_K)=q^{-n(\psi)/2}.}
\tag{8.6}
$$

This half-power is the first place where the sign of $n(\psi)$ becomes detectable.

### 8.3 Fourier inversion

Let $\mathcal S(K)$ be the space of compactly supported locally constant complex functions. With the self-dual measure,

$$
\widehat{\widehat f}(x)=f(-x).
\tag{8.7}
$$

**Proof.** It suffices to check characteristic functions of cosets of fractional ideals, since they span $\mathcal S(K)$. Translation contributes a character factor, while (8.5) exchanges a lattice with its annihilator. Applying the transform twice multiplies the two reciprocal volumes and changes the translation sign. Formula (8.3) gives $(A^\perp)^\perp=A$, so the result is $f(-x)$. $\square$

If $dx$ is replaced by $c\,dx$, the double transform is multiplied by $c^2$. Thus the measure is part of the functional equation and cannot be suppressed unless self-duality has been declared.

Two standard fields illustrate the convention. On $\mathbf Q_p$, take the character induced from $\mathbf Q_p/\mathbf Z_p\to\mathbf C^\times$, $x\mapsto e^{2\pi i x}$. It is trivial exactly on $\mathbf Z_p$, so $n(\psi)=0$ and the self-dual volume of $\mathbf Z_p$ is one. On $\mathbf F_q((t))$, choose a nontrivial character of $\mathbf F_q$ and apply it to the coefficient of $t^{-1}$. Again the integer ring is the largest fractional ideal in the kernel.

Scaling either example by a uniformizer gives conductor exponent one. The kernel becomes $\mathfrak p^{-1}$ and the self-dual volume of the integer ring becomes $q^{-1/2}$. Scaling by the inverse uniformizer gives exponent $-1$, kernel $\mathfrak p$, and volume $q^{1/2}$. These cases make the sign in (8.6) concrete.

### 8.4 Scaling and trace

If $dx$ is self-dual for $\psi$, then

$$
dx_a=|a|_K^{1/2}dx
\tag{8.8}
$$

is self-dual for $\psi_a$. Indeed, substituting $ax$ in one Fourier transform and applying it twice yields the factor $|a|^{-1}$, which (8.8) cancels.

Now let $L/K$ be finite separable and put $\psi_L=\psi\circ\operatorname{Tr}_{L/K}$. If $d=v_L(\mathfrak D_{L/K})$ and $e=e(L/K)$, trace duality gives

$$
n(\psi_L)=e\,n(\psi)+d.
\tag{8.9}
$$

Indeed, the trace-dual of $\mathcal O_L$ is $\mathfrak D_{L/K}^{-1}$. Requiring $\operatorname{Tr}(x\mathcal O_L)$ to lie in $\mathfrak p_K^{-n(\psi)}$ therefore gives the kernel lattice

$$
\mathfrak p_K^{-n(\psi)}\mathfrak D_{L/K}^{-1}
=\mathfrak p_L^{-en(\psi)-d}.
$$

Thus trace-compatible characters are generally not both of conductor zero. The different shift in (8.9) is exactly what later makes the induction constant independent of $s$.

## 9. Rank-one local factors and Gauss sums

### 9.1 Multiplicative characters and zeta integrals

Rank one is the analytic source of the entire theory. Let $\chi:K^\times\to\mathbf C^\times$ be a continuous quasicharacter. Its conductor exponent $a(\chi)$ is the least integer $a\geq0$ such that

$$
\chi|_{1+\mathfrak p_K^a}=1,
\tag{9.1}
$$

where $1+\mathfrak p_K^0$ is interpreted as $\mathcal O_K^\times$. Thus $a(\chi)=0$ exactly when $\chi$ is unramified.

Normalize multiplicative Haar measure by

$$
\operatorname{vol}^{\times}(\mathcal O_K^\times)=1.
$$

In terms of the self-dual additive measure, it is

$$
d^\times x=
\frac{|x|^{-1}\,dx}
{(1-q^{-1})\operatorname{vol}_\psi(\mathcal O_K)}.
\tag{9.2}
$$

For $f\in\mathcal S(K)$, define

$$
Z(f,\chi,s)=\int_{K^\times}f(x)\chi(x)|x|^s\,d^\times x.
\tag{9.3}
$$

The integral converges for $\operatorname{Re}(s)$ sufficiently large after separating the real power contained in $\chi$, and it continues to a rational function of $q^{-s}$.

The rank-one Euler factor is

$$
L(s,\chi)=
\begin{cases}
(1-\chi(\varpi_K)q^{-s})^{-1},&a(\chi)=0,\\
1,&a(\chi)>0.
\end{cases}
\tag{9.4}
$$

For example, with $f=\mathbf1_{\mathcal O_K}$ and unramified $\chi$,

$$
Z(f,\chi,s)=\sum_{m\geq0}\chi(\varpi_K)^m q^{-ms}
=L(s,\chi).
$$

If $\chi$ is ramified, the integral of $\chi$ over the unit group vanishes, so this same test function gives zero. The Euler factor is then $1$, not because the character has no local information, but because no inertia-fixed vector remains. Its conductor and Gauss sum retain the missing information.

### 9.2 The local functional equation

**Theorem 9.1 (rank-one local functional equation).** For every quasicharacter $\chi$ and nontrivial additive character $\psi$, there is a unique rational function $\gamma(s,\chi,\psi)$ such that

$$
Z(\widehat f,\chi^{-1},1-s)
=\gamma(s,\chi,\psi)Z(f,\chi,s)
\tag{9.5}
$$

for every $f\in\mathcal S(K)$. With self-dual additive measure, define $\epsilon(s,\chi,\psi)$ by

$$
\gamma(s,\chi,\psi)
=\epsilon(s,\chi,\psi)
\frac{L(1-s,\chi^{-1})}{L(s,\chi)}.
\tag{9.6}
$$

**Proof strategy.** Decompose $K^\times$ into valuation shells. On each shell, local constancy makes the integral finite. Fourier transform exchanges compact support with bounded level, so both sides become rational functions. The quotient in (9.5) is independent of $f$ because multiplicative translates of one nonzero zeta distribution span the one-dimensional space of distributions transforming by $\chi^{-1}|\cdot|^{1-s}$. A direct shell calculation proves that this space is one-dimensional.

For uniqueness, choose $f$ with $Z(f,\chi,s)\ne0$. Existence reduces first to characters of the finite quotient $\mathcal O_K^\times/(1+\mathfrak p_K^a)$ and then to a finite Fourier transform. The unramified shells contribute exactly the quotient of the two Euler factors in (9.6); the remaining finite transform is the epsilon factor. This reduction also proves the explicit formulas below. $\square$

The measure in (9.5) is the self-dual measure for the displayed $\psi$. If an arbitrary additive Haar measure is used, the gamma and epsilon factors acquire its scale. Equation (9.5), rather than an isolated Gauss-sum formula, is the definition that survives every change of convention.

### 9.3 Exact Gauss-sum formula

Put $a=a(\chi)$ and $n=n(\psi)$. If $a>0$, choose $c\in K^\times$ with

$$
v_K(c)=a+n.
\tag{9.7}
$$

Define the finite Gauss sum

$$
\tau(\chi,\psi;c)
=\sum_{u\in\mathcal O_K^\times/(1+\mathfrak p_K^a)}
\chi(u)^{-1}\psi(u/c).
\tag{9.8}
$$

It is well-defined: replacing $u$ by $u(1+z)$ with $z\in\mathfrak p_K^a$ changes $u/c$ by an element of $\mathfrak p_K^{-n}$, on which $\psi$ is trivial.

The exact formula is

$$
\boxed{
\epsilon(s,\chi,\psi)
=\chi(c)q^{-a/2}\tau(\chi,\psi;c)
q^{-(a+n)(s-1/2)}.}
\tag{9.9}
$$

The right side is independent of the choice of $c$ with valuation $a+n$. Indeed, if $c'=cu_0$ with $u_0\in\mathcal O_K^\times$, substitution $u=v u_0$ in (9.8) gives

$$
\tau(\chi,\psi;c')=\chi(u_0)^{-1}\tau(\chi,\psi;c),
$$

which cancels the change in $\chi(c)$.

For $a=0$, choose $c$ with $v(c)=n$. Then

$$
\boxed{
\epsilon(s,\chi,\psi)=\chi(c)q^{-n(s-1/2)}.}
\tag{9.10}
$$

In particular, an unramified character and a conductor-zero additive character have epsilon factor $1$.

To derive (9.9), take a test function supported on $c^{-1}\mathcal O_K^\times$ with the inverse character on its unit coordinate. Its original zeta integral is a single valuation shell. Formula (8.5), subdivided into the unit cosets modulo $1+\mathfrak p^a$, evaluates its Fourier transform as the sum (9.8). The additive volume of each coset contributes $q^{-a}\operatorname{vol}_\psi(\mathcal O_K)$, the conversion (9.2) removes $(1-q^{-1})\operatorname{vol}_\psi(\mathcal O_K)$, and the self-dual volume (8.6) supplies the remaining half-power. Cancelling the two shell integrals gives precisely $q^{-a/2}$ and the exponent in (9.9). This calculation is where all three integers $a$, $n$, and $v(c)$ must be retained.

### 9.4 Magnitude, quadratic sums, and examples

Assume $\chi$ is unitary and $a>0$. Then

$$
|\tau(\chi,\psi;c)|=q^{a/2}.
\tag{9.11}
$$

**Proof.** Expand $|\tau|^2$ and put one unit variable equal to the other times $z$. The inner sum over a unit quotient is an additive-character sum. Orthogonality makes it vanish unless $z\equiv1\pmod{\mathfrak p^a}$; the surviving diagonal contributes exactly $q^a$. The count includes the missing zero residue through the cancellation of the nonunit cosets, so the answer is $q^a$, not the cardinality $(q-1)q^{a-1}$ of the unit quotient. $\square$

Consequently the central value

$$
W(\chi,\psi)=\epsilon(1/2,\chi,\psi)
$$

has absolute value one for unitary $\chi$.

Suppose $a=1$, $n=0$, and $c=\varpi_K$. The character descends to a nontrivial character $\bar\chi$ of $k^\times$, while $u\mapsto\psi(u/\varpi_K)$ descends to a nontrivial additive character $\bar\psi$ of $k$. Formula (9.8) becomes the classical finite-field sum

$$
\tau(\bar\chi,\bar\psi)
=\sum_{x\in k^\times}\bar\chi(x)^{-1}\bar\psi(x).
\tag{9.12}
$$

If $q$ is odd and $\bar\chi$ is quadratic, then

$$
\tau(\bar\chi,\bar\psi)^2=\bar\chi(-1)q.
\tag{9.13}
$$

To prove this, square the sum, substitute $y=tx$, and evaluate the inner quadratic character sum after completing the square. All $t\ne-1$ cancel in pairs, while $t=-1$ supplies $\bar\chi(-1)q$. The sign of the square root depends on the additive character; equation (9.13), not a chosen square root, is canonical.

Gauss sums obey a useful scaling law. If $b\in\mathcal O_K^\times$, replacing $\psi$ by $\psi_b$ in (9.8) and substituting $u\mapsto b^{-1}u$ gives

$$
\tau(\chi,\psi_b;c)=\chi(b)^{-1}\tau(\chi,\psi;c).
\tag{9.13a}
$$

The factor $\chi(c)$ in (9.9) turns this inverse into the direct determinant factor in (11.1), because the compatible choice for the scaled character is $bc$. Scaling the phase inside a fixed finite sum and scaling the complete local constant are therefore distinct operations.

If one computes at a level deeper than the actual conductor of $\chi$, the analogous finite sum vanishes. Sum first along the extra kernel on which $\chi$ is trivial; the additive character is nontrivial there, and orthogonality gives zero. The nonzero primitive Gauss sum occurs at exactly $a(\chi)$. This is the finite Fourier reason that the conductor, rather than an arbitrarily chosen level, is the exponent of the epsilon factor.

For a tamely ramified quadratic character,

$$
W(\chi,\psi)=\chi(\varpi_K)q^{-1/2}
\tau(\bar\chi,\bar\psi).
$$

Thus even at conductor one the root number depends on both the extension of the residue character to $K^\times$ and the chosen additive character.

## 10. Local factors for general parameters

### 10.1 The Euler factor

Let $D=(r,N)$ on $V$, and put

$$
V_N^I=(\ker N)^{I_K}.
\tag{10.1}
$$

The local Euler factor is

$$
\boxed{
L(s,D)=\det\left(1-q^{-s}r(\Phi)\mid V_N^I\right)^{-1}.}
\tag{10.2}
$$

This is independent of the Frobenius lift because inertia acts trivially on $V_N^I$. It is unchanged by Frobenius semisimplification because determinants see the same eigenvalues. It is multiplicative under direct sums.

It is not multiplicative in arbitrary short exact sequences of Weil--Deligne representations. The special block $\operatorname{Sp}_2(1)$ has a one-dimensional subobject and quotient, both with zero monodromy, but its Euler factor has only the kernel-of-monodromy factor rather than the product of both constituent factors. Monodromy couples the two constituents. Multiplicativity in short exact sequences remains valid for Weil representations with $N=0$, where inertia invariants are exact in characteristic zero.

For $N=0$, formula (10.2) reduces to the usual determinant on $V^I$. For a ramified character, $V^I=0$ and $L=1$. For an irreducible representation of dimension greater than one, $V^I=0$: a nonzero invariant vector would generate a nonzero unramified subrepresentation, forcing irreducibility to make the whole representation unramified and hence one-dimensional.

For a special block, (4.4) gives

$$
L\bigl(s,\operatorname{Sp}_m(\rho)\bigr)
=L\left(s+\frac{m-1}{2},\rho\right).
\tag{10.3}
$$

This shift records the centered normalization of the block. In particular, for unramified $\chi$ with $\alpha=\chi(\Phi)$,

$$
L\bigl(s,\operatorname{Sp}_2(\chi)\bigr)
=\frac1{1-\alpha q^{-s-1/2}}.
$$

### 10.2 The epsilon factor without monodromy

The rank-one epsilon factor extends uniquely to finite-inertia Weil representations.

**Theorem 10.1.** There is a unique assignment

$$
(r,\psi,dx)\longmapsto\epsilon(s,r,\psi,dx)
$$

with the following properties:

1. it agrees with Chapter 9 in dimension one;
2. it is multiplicative in short exact sequences;
3. it is compatible with induction as in Section 11.4;
4. for the zero representation it equals $1$.

With the self-dual measure suppressed from the notation,

$$
\epsilon(s,r,\psi)
=W(r,\psi)q^{-[a(r)+n(\psi)\dim V](s-1/2)}.
\tag{10.4}
$$

**Proof strategy.** Every finite inertial action factors through a finite local quotient. Character induction expresses its character as an integral combination of characters induced from one-dimensional characters of subgroups. Apply the rank-one construction and the induction rule. Relations among induced characters give no ambiguity because the finite Fourier functional equation is additive on virtual characters. Nonnegativity is not needed: one first defines the factor on the character group and then restricts to actual representations. Formula (10.4) follows from the conductor induction formula and (8.9). $\square$

There are two points inside the uniqueness assertion. Induction must come from subgroups arising from finite separable extensions, so that trace characters and differents are available. Moreover, every relation among induced characters must yield local constant one. Pairing such a relation with the Artin character kills its monomial exponent, while the corresponding product of finite Fourier transforms kills its central scalar. Both parts are therefore independent of the chosen induction expression.

Finite inertia does not mean finite total image, so one further reduction is required. For an irreducible $r$, a positive power of Frobenius centralizes the finite inertial image and hence acts by a scalar. Twisting by a suitable unramified character makes that scalar finite order. The twisted representation then has finite image and is covered by character induction. The unramified-twist formula of Section 11.2 restores the original representation. This proves existence for arbitrary Frobenius eigenvalues rather than only for finite-image representations.

For the Weil representation $r$ considered in this section, short exact sequences cause no hidden extension term. On the finite inertial image, characteristic zero makes invariants exact. Frobenius may still carry extension data, but Frobenius semisimplification preserves every relevant characteristic polynomial and determinant. After monodromy is added, only direct-sum multiplicativity survives, as the special-block counterexample in Section 10.1 shows.

When $r$ is unitary, $|W(r,\psi)|=1$. For a general $r$, the notation $W$ still means the value at $s=1/2$, but it need not be a complex number of absolute value one.

### 10.3 Deligne's monodromy correction

The epsilon factor of $D=(r,N)$ is

$$
\boxed{
\epsilon(s,D,\psi)
=\epsilon(s,r,\psi)
\det\left(-q^{-s}r(\Phi)\mid
V^{I_K}/V_N^I\right).}
\tag{10.5}
$$

The quotient is Frobenius-stable because $N$ commutes with inertia and satisfies (4.2). Changing the Frobenius lift does not change its action on either invariant space. The exponent of $q^{-s}$ contributed by the determinant is

$$
\dim V^I-\dim V_N^I.
$$

Combining this with (10.4) and (7.4) shows that

$$
\epsilon(s,D,\psi)
=W(D,\psi)q^{-[a(D)+n(\psi)\dim V](s-1/2)}.
\tag{10.6}
$$

The extra factor $q^{-d/2}$ absorbed into $W(D,\psi)$, where $d=\dim V^I-\dim V_N^I$, is essential. Replacing $-q^{-s}r(\Phi)$ by $-r(\Phi)$ would give the wrong conductor exponent.

Formula (10.5) also explains why monodromy affects epsilon factors even when the finite inertia representation is unramified. The determinant is taken on precisely the invariant directions removed from the Euler factor by $N$.

### 10.4 Gamma factors

Define

$$
\boxed{
\gamma(s,D,\psi)
=\epsilon(s,D,\psi)
\frac{L(1-s,D^\vee)}{L(s,D)}.}
\tag{10.7}
$$

For rank one, this is exactly the constant in the Fourier functional equation (9.5). For a direct sum it is the product of the gamma factors. The indecomposable decomposition of Theorem 4.1, together with induction for the irreducible Weil pieces, therefore determines the general factor. One must not impose relations coming from arbitrary short exact sequences of objects with monodromy.

The three factors record complementary data. The Euler factor sees only $V_N^I$ and Frobenius. The conductor exponent in epsilon sees every break and the monodromy defect. The central scalar sees finite Fourier phases that neither dimensions nor characteristic polynomials recover. Equal Euler factors and equal conductors do not force equal epsilon factors.

### 10.5 Special blocks and two-dimensional examples

Let $\chi$ be unramified, put $\alpha=\chi(\Phi)$, assume $n(\psi)=0$, and use the self-dual measure. The underlying Weil representation of $\operatorname{Sp}_m(\chi)$ is a direct sum of unramified characters, so its epsilon factor before monodromy is $1$. On the quotient $V^I/V_N^I$, the basis classes are $e_1,\dots,e_{m-1}$. Formula (10.5) gives

$$
\boxed{
\epsilon\bigl(s,\operatorname{Sp}_m(\chi),\psi\bigr)
=(-\alpha)^{m-1}q^{-(m-1)(s-1/2)}.}
\tag{10.8}
$$

The sum of the centered Frobenius exponents on $e_1,\dots,e_{m-1}$ is $(m-1)/2$, which supplies the central half-power in (10.8). For $m=2$, the root number is $-\alpha$.

Now consider two-dimensional Frobenius-semisimple parameters.

- If $D=\chi_1\oplus\chi_2$ and $N=0$, every factor is the product of the two character factors.
- If $D=\operatorname{Sp}_2(\chi)$, then $L(s,D)=L(s+1/2,\chi)$ and the conductor is $1$ for unramified $\chi$, but $2a(\chi)$ for ramified $\chi$.
- If $r$ is irreducible and $N=0$, then $L(s,D)=1$, while the conductor and epsilon factor can be nontrivial. An induced quadratic character provides the basic example.

These cases show why the determinant alone is insufficient. The split pair $\chi\oplus\chi^{-1}$, a special block with determinant one, and an irreducible induced representation with determinant one can share a determinant while having different Euler factors, conductors, and root numbers.

## 11. Duality, twists, and induction

### 11.1 Change of additive character and Haar measure

For $a\in K^\times$, let $\psi_a(x)=\psi(ax)$. Transport $\det r$ through reciprocity and write $\det D(a)$ for $\det r(\operatorname{rec}_K(a))$. With the self-dual measure for each displayed additive character,

$$
\boxed{
\epsilon(s,D,\psi_a)
=\det D(a)|a|^{\dim V(s-1/2)}
\epsilon(s,D,\psi).}
\tag{11.1}
$$

**Proof.** In rank one, choose $c$ as in (9.7). For $\psi_a$, use $ac$; the Gauss sum is unchanged, while $\chi(ac)$ contributes $\chi(a)$ and the valuation exponent contributes $|a|^{s-1/2}$. Direct sums and induction extend the formula to $r$. The monodromy determinant in (10.5) is independent of $\psi$, so the same formula holds for $D$. $\square$

If an additive Haar measure $dx$ is replaced by $b\,dx$ with $b>0$ while $\psi$ is fixed, then

$$
\epsilon(s,D,\psi,b\,dx)=b^{\dim V}\epsilon(s,D,\psi,dx).
\tag{11.2}
$$

Each rank-one Fourier transform contributes one factor $b$, and multiplicativity gives the dimension. Formula (11.2) is why “the epsilon factor” is incomplete notation until either a measure or the self-dual convention has been fixed.

### 11.2 Unramified twists

Let $\mu$ be unramified and put $\beta=\mu(\Phi)=\mu(\varpi_K)$. Twisting multiplies every Frobenius eigenvalue by $\beta$, so

$$
L(s,D\otimes\mu)
=\det\left(1-\beta q^{-s}r(\Phi)\mid V_N^I\right)^{-1}.
\tag{11.3}
$$

If $\mu=|\cdot|^t$, this simplifies to

$$
L(s,D\otimes|\cdot|^t)=L(s+t,D),
\tag{11.4}
$$

and similarly

$$
\epsilon(s,D\otimes|\cdot|^t,\psi)
=\epsilon(s+t,D,\psi).
\tag{11.5}
$$

For an arbitrary unramified $\mu$,

$$
\boxed{
\epsilon(s,D\otimes\mu,\psi)
=\beta^{a(D)+n(\psi)\dim V}
\epsilon(s,D,\psi).}
\tag{11.6}
$$

To verify the exponent, use (9.9) in rank one: the chosen $c$ has valuation $a+n$, so $\mu(c)=\beta^{a+n}$. Additivity and the monodromy correction replace $a(r)$ by $a(D)$. Formula (11.6) is a particularly sensitive check on the sign convention for $n(\psi)$.

### 11.3 Duality

Fourier inversion gives the exact duality identity

$$
\boxed{
\gamma(s,D,\psi)
\gamma(1-s,D^\vee,\psi^{-1})=1.}
\tag{11.7}
$$

For rank one, apply (9.5) first with $(\chi,\psi)$ and then with $(\chi^{-1},\psi^{-1})$. The second Fourier transform is the identity rather than reflection, because the additive character has been inverted. General duality follows by induction and multiplicativity.

Since the Euler factors in (10.7) cancel across the two terms, (11.7) is equivalent to

$$
\epsilon(s,D,\psi)
\epsilon(1-s,D^\vee,\psi^{-1})=1.
\tag{11.8}
$$

Using $\psi^{-1}=\psi_{-1}$ and (11.1), the same-character version is

$$
\gamma(s,D,\psi)
\gamma(1-s,D^\vee,\psi)=\det D(-1),
\tag{11.9}
$$

with the analogous identity for epsilon factors. The determinant at $-1$ is often lost when the distinction between $\psi$ and $\psi^{-1}$ is suppressed.

### 11.4 Induction and the lambda constant

Let $L/K$ be finite separable and set

$$
\psi_L=\psi_K\circ\operatorname{Tr}_{L/K}.
$$

Use the self-dual measure for each character. Define

$$
\boxed{
\lambda(L/K,\psi_K)
=\frac{\epsilon_K(s,\operatorname{Ind}_{W_L}^{W_K}1,\psi_K)}
{\epsilon_L(s,1,\psi_L)}.}
\tag{11.10}
$$

This quotient is independent of $s$. Indeed, by (7.10) the conductor of the induced trivial representation is $fd$, and its dimension is $ef$. Its exponent in (10.4) is therefore

$$
fd+n(\psi_K)ef
=f\bigl(d+en(\psi_K)\bigr).
$$

By (8.9), the exponent of the denominator relative to $q_L=q^f$ is the same number.

**Theorem 11.1 (induction formula).** For every Weil--Deligne representation $U$ of $W_L$,

$$
\boxed{
\epsilon_K\left(s,\operatorname{Ind}_{W_L}^{W_K}U,\psi_K\right)
=\lambda(L/K,\psi_K)^{\dim U}
\epsilon_L(s,U,\psi_L).}
\tag{11.11}
$$

Moreover,

$$
L_K\left(s,\operatorname{Ind}_{W_L}^{W_K}U\right)=L_L(s,U).
\tag{11.12}
$$

**Proof strategy.** For (11.12), inertia orbits on the embeddings of $L$ reduce the determinant over $K$ to the determinant of an $f$th power of Frobenius over $L$; $q_L^{-s}=q^{-fs}$ gives the same polynomial. For (11.11), first prove the statement for characters by comparing the two finite Fourier transforms under trace. The discrepancy for the trivial character is exactly (11.10). Multiplicativity and character induction then prove the general case. The operator $N$ is carried pointwise on induced functions; its determinant correction obeys the same orbit calculation as the Euler factor. $\square$

The lambda constant is not generally one. It is the root number of the permutation representation after the trace-compatible trivial factor is removed. For a split étale algebra it is one; for a ramified field it can be a nontrivial normalized Gauss sum.

Two examples locate the correction. If $L/K$ is unramified, then $d=0$ and a conductor-zero $\psi_K$ remains conductor zero after trace. The induced trivial representation is unramified, so

$$
\lambda(L/K,\psi_K)=1.
\tag{11.12a}
$$

If $L/K$ is tamely ramified quadratic with odd residue characteristic, then

$$
\operatorname{Ind}_{W_L}^{W_K}1=1\oplus\eta,
$$

where $\eta$ is the associated ramified quadratic character. For conductor-zero $\psi_K$, the denominator of (11.10) uses a character over $L$ of conductor exponent $d=1$. Formula (9.10) for that denominator and the quadratic Gauss sum for $\eta$ show that $\lambda$ is a fourth root of unity determined by $\eta(-1)$ and the residue additive character. It need not be one.

For a character $\theta$ of $W_L$, the quadratic formula reads

$$
\epsilon_K(s,\operatorname{Ind}\theta,\psi_K)
=\lambda(L/K,\psi_K)\epsilon_L(s,\theta,\psi_L),
\tag{11.12b}
$$

while its conductor is

$$
a_K(\operatorname{Ind}\theta)=f\bigl(a_L(\theta)+d\bigr).
$$

The extension thus contributes an integer through the different and a phase through $\lambda$. Knowing the conductor never determines that phase.

In a tower $M/L/K$, the constants satisfy

$$
\lambda(M/K,\psi_K)
=\lambda(L/K,\psi_K)^{[M:L]}
\lambda(M/L,\psi_K\circ\operatorname{Tr}_{L/K}).
\tag{11.13}
$$

This follows by applying (11.11) to induction in one step and in two steps. The exponent $[M:L]$ is forced by the dimension of the intermediate induced trivial representation.

### 11.5 Restriction and base change

For $D=(r,N)$ over $K$, restriction to $W_L$ is

$$
D|_{W_L}=(r|_{W_L},N).
$$

Equation (2.4) shows that the monodromy relation is preserved. The determinant restricts, which under reciprocity means composition with $N_{L/K}$. Duality, tensor products, and Frobenius semisimplification commute with restriction.

Conductors under restriction require the Herbrand transition. Under unramified base change, inertia and its upper filtration are unchanged, so

$$
a_L(D|_{W_L})=a_K(D).
\tag{11.14}
$$

Under tame base change of ramification index $e$, the positive-depth area is multiplied by $e$, but the tame fixed-space codimension must be recomputed. Under wild base change there is no degree-only formula.

Euler factors also need not remain unchanged. If $L/K$ is unramified of residue degree $f$, Frobenius over $L$ acts as $r(\Phi)^f$ and $q_L=q^f$, so

$$
L_L(s,D|_{W_L})
=\det\left(1-q^{-fs}r(\Phi)^f\mid V_N^I\right)^{-1}.
\tag{11.15}
$$

If $L/K$ is cyclic and $X_{L/K}$ is the character group of $K^\times/N_{L/K}L^\times$, induction and projection give

$$
\operatorname{Ind}_{W_L}^{W_K}(D|_{W_L})
\simeq\bigoplus_{\eta\in X_{L/K}}D\otimes\eta.
\tag{11.16}
$$

Combining (11.11) with (11.16) yields the exact epsilon-product identity

$$
\epsilon_L(s,D|_{W_L},\psi_L)
=\lambda(L/K,\psi_K)^{-\dim D}
\prod_{\eta\in X_{L/K}}
\epsilon_K(s,D\otimes\eta,\psi_K).
\tag{11.17}
$$

This formula simultaneously records the trace character, the different, and the induction constant. Choosing unrelated conductor-zero additive characters on the two fields would introduce the scaling factor from (11.1).

## 12. Functional equations and a normalization audit

### 12.1 The rank-one equation revisited

For a character, the complete statement consists of the Fourier transform, two Haar measures, and three local factors:

$$
\begin{aligned}
\widehat f(y)&=\int_Kf(x)\psi(xy)\,dx_\psi,\\
Z(f,\chi,s)&=\int_{K^\times}f(x)\chi(x)|x|^s\,d^\times x,\\
Z(\widehat f,\chi^{-1},1-s)
&=\epsilon(s,\chi,\psi)
\frac{L(1-s,\chi^{-1})}{L(s,\chi)}
Z(f,\chi,s).
\end{aligned}
\tag{12.1}
$$

Here $dx_\psi$ is self-dual and $d^\times x$ gives $\mathcal O_K^\times$ volume one. These normalizations are compatible but logically independent. The first changes with $\psi$; the second does not.

Equation (12.1) proves meromorphic continuation of the zeta integral because its two sides are rational in $q^{-s}$. It also proves uniqueness of the epsilon factor. The conductor is recovered as the degree of its monomial after the additive-character shift is removed:

$$
-\deg_{q^{-s}}\epsilon(s,\chi,\psi)
=a(\chi)+n(\psi).
$$

Thus the functional equation contains both ramification depth and Fourier normalization.

Applying (12.1) twice gives duality directly. The first transform uses $\psi$ and changes $(\chi,s)$ to $(\chi^{-1},1-s)$. The second uses $\psi^{-1}$, so

$$
\mathcal F_{\psi^{-1}}\mathcal F_\psi f=f
$$

with the respective self-dual measures. The zeta integral returns to its starting point, forcing the product of gamma factors to be one. If the second transform also uses $\psi$, Fourier inversion gives $f(-x)$; changing $x$ to $-x$ contributes $\chi(-1)$. This is the rank-one origin of the determinant in (11.9).

The poles match just as concretely. A pole of $L(s,\chi)$ occurs only for an unramified character and comes from the nonnegative valuation shells. Fourier transform carries them to the negative shells responsible for $L(1-s,\chi^{-1})$. For a ramified character both Euler factors are one, and the equation is a finite Gauss-sum identity multiplied by a monomial.

### 12.2 The general local equation

For a general parameter there need not be a single scalar zeta integral of the form (9.3). The local functional equation is the Artin-formal identity

$$
\boxed{
\gamma(s,D,\psi)
=\epsilon(s,D,\psi)
\frac{L(1-s,D^\vee)}{L(s,D)},}
\tag{12.2}
$$

together with direct-sum multiplicativity, induction, and the rank-one Fourier equation. These properties determine all three factors after decomposition into special blocks. For the underlying Weil representations, ordinary character-group relations may be used; relations from nonsplit monodromy extensions may not.

The decisive compatibility is induction. If $D$ is induced from $L$, then (11.12) transports both Euler factors without correction, while (11.11) transports epsilon factors with $\lambda(L/K,\psi)^{\dim D}$. The same constant therefore appears in gamma factors. Omitting it would contradict the rank-one Fourier equation after composing the additive character with trace.

Duality supplies the involutive form

$$
\gamma(s,D,\psi)^{-1}
=\gamma(1-s,D^\vee,\psi^{-1}).
\tag{12.3}
$$

Twisting by $|\cdot|^t$ translates $s$ by $t$ in every term. Direct sums multiply every factor. These three operations reduce most calculations to characters and special blocks.

### 12.3 Root numbers

The **root number** is the central epsilon value

$$
W(D,\psi)=\epsilon(1/2,D,\psi).
\tag{12.4}
$$

If $D$ is unitary, then $|W(D,\psi)|=1$. This follows in rank one from Gauss-sum orthogonality, for finite-image representations from induction, and for special blocks from (10.5). A nonunitary parameter can be written as a unitary parameter times a real power of $|\cdot|$; its central value need not lie on the unit circle unless the center is shifted accordingly.

Changing the additive character gives

$$
W(D,\psi_a)=\det D(a)W(D,\psi).
\tag{12.5}
$$

Thus a root number is not an invariant of $D$ alone. If $D\simeq D^\vee$, then (11.8) gives

$$
W(D,\psi)W(D,\psi^{-1})=1,
$$

while (11.9) gives

$$
W(D,\psi)^2=\det D(-1)
\tag{12.6}
$$

when the chosen self-duality identifies the two factors and the same additive character is used. In the orthogonal determinant-one case this forces a sign. Without self-duality or determinant one, calling the root number a sign is incorrect.

### 12.4 Consistency tests

The theory can be audited through a short chain of computations.

**Unramified character.** If $\chi$ and $\psi$ both have conductor zero, then

$$
L(s,\chi)=(1-\chi(\Phi)q^{-s})^{-1},
\qquad \epsilon(s,\chi,\psi)=1.
$$

Replacing $\psi$ by $\psi_a$ gives $\chi(a)|a|^{s-1/2}$, exactly as (11.1) requires.

**Tame character.** If $a(\chi)=1$ and $n(\psi)=0$, then $L=1$ and

$$
\epsilon(s,\chi,\psi)
=\chi(\varpi)q^{-1/2}\tau(\bar\chi,\bar\psi)
q^{-(s-1/2)}.
$$

The monomial degree is one, equal to the Artin conductor.

**Special block.** For unramified $\chi$,

$$
L(s,\operatorname{Sp}_m(\chi))
=L(s+(m-1)/2,\chi),
$$

and (10.8) has monomial degree $m-1$, equal to the monodromy conductor. The underlying finite-inertia representation has conductor zero, so this test detects any omitted correction.

**Trace to an extension.** For $L/K$ with different exponent $d$,

$$
n(\psi\circ\operatorname{Tr}_{L/K})=en(\psi)+d.
$$

Together with $q_L=q^f$, this makes the numerator and denominator of (11.10) have the same $s$-degree. A sign error in the additive conductor makes the lambda constant falsely depend on $s$.

**Induced trivial representation.** Its conductor is $fd$. If one uses $d$ without the residue-degree factor, transitivity in a tower fails. If one uses the discriminant exponent $fd$ inside the parentheses of (7.10), the factor is counted twice.

**Duality.** Using $\psi^{-1}$ gives product one; using the same $\psi$ gives $\det D(-1)$. This test catches the missing reflection in Fourier inversion.

### 12.5 Conclusion

The local parameter is now a coherent object rather than a list of invariants. The Weil group separates compact inertia from unrestricted Frobenius. Frobenius semisimplification removes only an unobservable unipotent extension in the Frobenius direction. The nilpotent operator records potential unipotence of inertia and organizes Frobenius eigenvalues into norm-spaced strings. Inertial types retain finite ramification but deliberately forget both unramified eigenvalues and monodromy.

Conductors measure two losses: upper-depth motion in the finite inertial action and invariant directions removed by monodromy. Euler factors inspect the surviving space $(\ker N)^I$. Epsilon factors restore everything the Euler factor omits: ramification depth, determinant data, finite Fourier phases, the additive-character lattice, and the self-dual measure. Gauss sums give the rank-one calculation; induction and the lambda constant propagate it to every finite-inertia parameter.

The normalization ledger closes consistently. Geometric Frobenius corresponds to a uniformizer, $|\Phi|=q^{-1}$, special blocks use centered norm powers, additive conductor $n$ means kernel $\mathfrak p^{-n}$, and trace raises that exponent by the different. With those choices fixed, duality, twisting, induction, restriction, and functional equations agree without hidden inversions or missing powers of $q$. That agreement is the practical value of the theory: every local invariant can be calculated separately, and each calculation checks the others.
