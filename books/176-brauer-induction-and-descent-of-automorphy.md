# Brauer Induction and Descent of Automorphy

## Contents

1. [The descent problem and its exact endpoint](#1-the-descent-problem-and-its-exact-endpoint)
   - [Potential automorphy is an upstairs theorem](#11-potential-automorphy-is-an-upstairs-theorem)
   - [The input package](#12-the-input-package)
   - [Three meanings of descent](#13-three-meanings-of-descent)
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
4. [The intersection-field repair](#4-the-intersection-field-repair)
   - [Subgroups of elementary groups are subnormal](#41-subgroups-of-elementary-groups-are-subnormal)
   - [Prime-cyclic towers to every overlap](#42-prime-cyclic-towers-to-every-overlap)
   - [The overlap theorem](#43-the-overlap-theorem)
   - [Why top-field agreement is not enough](#44-why-top-field-agreement-is-not-enough)
5. [The arithmetic Brauer datum](#5-the-arithmetic-brauer-datum)
   - [Coefficient fields and character avatars](#51-coefficient-fields-and-character-avatars)
   - [Termwise Galois and automorphic operations](#52-termwise-galois-and-automorphic-operations)
   - [The virtual base-field family](#53-the-virtual-base-field-family)
   - [Rank and determinant](#54-rank-and-determinant)
6. [Frobenius polynomials and local records](#6-frobenius-polynomials-and-local-records)
   - [The unramified cyclic-block calculation](#61-the-unramified-cyclic-block-calculation)
   - [Common quadratic polynomials](#62-common-quadratic-polynomials)
   - [Local types and monodromy](#63-local-types-and-monodromy)
   - [Sensitive places and lattices](#64-sensitive-places-and-lattices)
7. [Character norm and effectivity](#7-character-norm-and-effectivity)
   - [The Hom inner product](#71-the-hom-inner-product)
   - [The Mackey Gram matrix](#72-the-mackey-gram-matrix)
   - [Self-twists on overlap fields](#73-self-twists-on-overlap-fields)
   - [Embedding independence](#74-embedding-independence)
   - [Norm one forces positive rank two](#75-norm-one-forces-positive-rank-two)
8. [The descent theorem](#8-the-descent-theorem)
   - [The effective members](#81-the-effective-members)
   - [Compatibility and independence](#82-compatibility-and-independence)
   - [Actual local consequences](#83-actual-local-consequences)
   - [The distinguished member](#84-the-distinguished-member)
9. [What remains for coherent family assembly](#9-what-remains-for-coherent-family-assembly)
   - [What this book proves](#91-what-this-book-proves)
   - [What Book 189 must still construct](#92-what-book-189-must-still-construct)
   - [Automorphy over the base field](#93-automorphy-over-the-base-field)
10. [Hostile audit and conclusion](#10-hostile-audit-and-conclusion)
    - [Dependency closure](#101-dependency-closure)
    - [Nine possible failure points](#102-nine-possible-failure-points)
    - [Final theorem package](#103-final-theorem-package)
    - [Conclusion](#104-conclusion)

## 1. The descent problem and its exact endpoint

### 1.1 Potential automorphy is an upstairs theorem

Let \(F\) be a totally real number field and let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(E)
\tag{1.1}
$$

be the chosen absolutely irreducible representation, where \(E\) is a finite extension of
\(\mathbf Q_\ell\). Potential automorphy gives a totally real extension \(M/F\) and a
parallel-weight-two cuspidal representation \(\pi_M\) such that

$$
\rho|_{G_M}\simeq r_{\pi_M,\lambda_0}.
\tag{1.2}
$$

This is automorphy over \(M\), not over \(F\). If \(M/F\) were solvable, the solvable descent
theorem could move \(\pi_M\) down a prime-cyclic tower, with the extending representation
\(\rho\) selecting the required twists. The controlled top used on the critical spine is
instead Galois with a nonsolvable group, in the application

$$
\Gamma=\operatorname{Gal}(M/F)\simeq S_d\times C_2,\qquad d\geq5.
\tag{1.3}
$$

There is no permitted nonsolvable base-change or descent theorem that takes \(\pi_M\) directly
to \(F\).

Brauer induction changes the shape of the problem. It replaces the impossible single descent
through \(\Gamma\) by finitely many descents through elementary subgroups \(H\leq\Gamma\).
The fixed field \(F_H=M^H\) need not be Galois over \(F\), but \(M/F_H\) has group \(H\),
which is solvable. One obtains actual automorphic packets over the \(F_H\), twists them by
finite-order characters, and induces their Galois realizations back to \(G_F\). The induced
terms have large rank and occur with signs. The central theorem of this book is that their
signed sum is nevertheless one honest irreducible representation of rank two at every
coefficient embedding.

That conclusion is an effectivity theorem for Galois representations over the base field.
It does not by itself construct a cuspidal automorphic representation over \(F\).

### 1.2 The input package

The preceding potential-automorphy and solvable-transfer books provide the following data.

1. The representation \(\rho\) in (1.1) has determinant \(\chi_\ell\), the \(\ell\)-adic
   cyclotomic character, and a named stable lattice. In the critical application it is
   unramified outside \(2\ell\), finite flat at \(\ell\), and has at \(2\) trivial wild
   inertia, zero monodromy, and primitive tame order-three type.
2. The extension \(M/F\) is finite, totally real, and Galois. Its local completions, residual
   image, avoidance fields, and conjugation action have already been controlled.
3. There is a parallel-weight-two cuspidal packet \(\pi_M\) satisfying (1.2).
4. For every elementary \(H\leq\Gamma\), there is a selected parallel-weight-two cuspidal
   packet \(\pi_H\) over \(F_H=M^H\) such that

   $$
   \operatorname{BC}_{M/F_H}(\pi_H)=\pi_M,
   \qquad
   r_{\pi_H,\lambda_0}\simeq\rho|_{G_{F_H}}.
   \tag{1.4}
   $$

   The selection is independent of a prime-cyclic descent tower and is compatible with field
   conjugation, coefficient conjugation, determinants, local types, and stable packet
   lattices.
5. Cyclic and solvable base change commute with coefficient conjugation and with the attached
   Galois representations. They restrict the full local parameter at every place in their
   proved range, not merely the unramified Hecke trace.

These are imported theorems, not axioms. The work here begins with this exact interface and
proves every passage from it to a base-field effective family.

### 1.3 Three meanings of descent

Three conclusions must remain distinct.

First, a **virtual descent** is a class in a Grothendieck group,

$$
\mathcal R_\tau=[R_\tau^+]-[R_\tau^-].
\tag{1.5}
$$

It has a trace, a determinant line, local virtual parameters, and a quotient of Euler
products. It need not be represented by a vector space.

Second, an **effective embedding-indexed descent** is a collection of actual representations

$$
r_\tau:G_F\longrightarrow\operatorname{GL}_2(\Omega_\tau)
\tag{1.6}
$$

for every coefficient embedding \(\tau\), with one common collection of algebraic Frobenius
polynomials and compatible local records. This is the endpoint of the present book. The
representations live on the base-field Galois group; subtraction has been eliminated.

Third, a **coherently assembled compatible system** chooses one number field of coefficients,
one model at every finite place of that field, coherent indexing under coefficient
conjugation, and compatible local models and comparison isomorphisms. That construction is the
work of Book 189. Pointwise existence over algebraic closures does not automatically supply it.

There is a fourth, stronger statement: a cuspidal automorphic representation over \(F\) whose
Galois system is the assembled family. It requires a separate automorphic descent theorem or a
converse theorem. Neither effectivity nor strong multiplicity one creates such an object.

### 1.4 Conventions

All Frobenius elements are arithmetic. Thus, at a good rational prime \(p\),

$$
\chi_\tau(\operatorname{Frob}_p)=p
\tag{1.7}
$$

and a weight-two rank-two polynomial is \(X^2-a_pX+p\). A characteristic series uses the
reciprocal variable:

$$
\det(1-r(\operatorname{Frob}_p)T)=1-a_pT+pT^2.
\tag{1.8}
$$

Representations are continuous and characteristic-zero. Equalities of Galois
representations are semisimple equalities unless a lattice or an extension is explicitly
named. Induction from an open subgroup is unnormalized finite induction. Automorphic twisting
by a Hecke character \(\psi\) means twisting through the determinant, so the central character
is multiplied by \(\psi^2\).

For a finite extension of local fields \(L/K\), \(f(L/K)\) is the residue degree and
\(d(L/K)\) the exponent in \(K\) of the discriminant ideal. Frobenius powers are governed by
\(f\), not by the ramification index or the global degree.

## 2. Elementary groups and integral Brauer relations

### 2.1 Elementary groups

For a prime \(p\), a finite group is \(p\)-elementary if it has the form

$$
H=C\times P,
\tag{2.1}
$$

where \(C\) is cyclic of order prime to \(p\) and \(P\) is a \(p\)-group. A group is
elementary if it is \(p\)-elementary for some \(p\).

Elementary groups are nilpotent. Indeed, \(C\) is the direct product of its Sylow subgroups,
as is \(P\), and all Sylow subgroups of \(C\times P\) are normal. They are therefore solvable.
The direct-product condition is essential: a semidirect product \(C\rtimes P\) need not be
elementary.

Every subgroup \(D\leq C\times P\) is elementary. To see this, let \(m=|C|\) and
\(|P|=p^a\). If \(d=(c,u)\in D\), choose integers \(r,s\) with

$$
r\equiv1\pmod m,\quad r\equiv0\pmod{p^a},
\qquad
s\equiv0\pmod m,\quad s\equiv1\pmod{p^a}.
$$

Then \(d^r=(c,1)\in D\) and \(d^s=(1,u)\in D\). Hence

$$
D=(D\cap C)\times(D\cap P),
\tag{2.2}
$$

and \(D\cap C\) is cyclic.

### 2.2 Monomiality

An irreducible character is monomial if it is induced from a linear character of a subgroup.

**Proposition 2.1.** Every irreducible character of an elementary group is monomial.

**Proof.** Let \(H=C\times P\). An irreducible representation is
\(\alpha\otimes\tau\), where \(\alpha\) is linear on \(C\) and \(\tau\) is irreducible on
\(P\). It is enough to prove that irreducible representations of finite \(p\)-groups are
monomial.

Proceed by induction on \(|P|\). Divide by the kernel of \(\tau\); an inducing character on
the quotient pulls back, so assume \(\tau\) faithful. Schur's lemma makes \(Z(P)\) act by
scalars, and faithfulness makes \(Z(P)\) cyclic. If \(P\) is abelian, \(\tau\) is linear.
Otherwise choose an abelian normal subgroup \(A\) properly containing \(Z(P)\): take the
inverse image in \(P\) of a central subgroup of order \(p\) in \(P/Z(P)\). Choose a linear
constituent \(\lambda\) of \(\tau|_A\), and let \(I<P\) be its stabilizer. The inequality is
strict, for if \(I=P\), then \(A\) acts by scalars and faithfulness forces
\([P,A]=1\), contradicting \(A\not\subseteq Z(P)\).

The sum of the conjugate \(\lambda\)-isotypic spaces is the whole representation, and the
action on one such space gives an irreducible representation \(\tau_0\) of \(I\) with

$$
\tau\simeq\operatorname{Ind}_I^P\tau_0.
$$

By induction, \(\tau_0=\operatorname{Ind}_J^I\mu\) for a linear \(\mu\). Transitivity gives
\(\tau=\operatorname{Ind}_J^P\mu\). Finally,

$$
\alpha\otimes\tau
\simeq\operatorname{Ind}_{C\times J}^{C\times P}(\alpha\otimes\mu),
$$

which is monomial. \(\square\)

### 2.3 The restriction criterion

The integrality step in Brauer induction is local at each rational prime. Write
\(\mathbf Z_{(p)}\) for the localization of \(\mathbf Z\) at \(p\).

**Lemma 2.2.** Let \(A\) be finite and \(P\) a Sylow \(p\)-subgroup. There is a
\(\mathbf Z_{(p)}\)-linear combination of permutation characters induced from \(p\)-subgroups
whose value is \(1\) on \(p\)-elements and \(0\) on all other elements.

**Proof.** Put \(u=\operatorname{Ind}_P^A1\). It counts fixed points on \(A/P\). If \(a\) is
not a \(p\)-element, it fixes no coset. If \(a\) is a \(p\)-element, the cyclic group
\(\langle a\rangle\) acts on \(A/P\), whose cardinality is prime to \(p\); its nontrivial
orbits have \(p\)-power cardinality, so

$$
u(a)\equiv[A:P]\not\equiv0\pmod p.
$$

Let \(b_1,\ldots,b_s\) be the nonzero values of \(u\) on \(p\)-elements and set

$$
Q(X)=1-\prod_{j=1}^s(1-X/b_j).
$$

Every \(b_j\) is a unit in \(\mathbf Z_{(p)}\), \(Q(0)=0\), and \(Q(b_j)=1\). Powers of \(u\)
are permutation characters of Cartesian powers of \(A/P\); their stabilizers are
intersections of conjugates of \(P\), hence \(p\)-groups. Expanding \(Q(u)\) proves the
claim. \(\square\)

**Theorem 2.3 (Brauer restriction criterion).** A rational linear combination \(\varphi\) of
irreducible characters of a finite group \(G\) is a generalized character if and only if its
restriction to every elementary subgroup is a generalized character.

**Proof.** Only the converse needs proof. Write

$$
\varphi=\sum_{\chi\in\operatorname{Irr}(G)}a_\chi\chi,\qquad a_\chi\in\mathbf Q.
$$

It is enough to prove \(a_\chi\in\mathbf Z_{(p)}\) for every \(p\), because the intersection
of these localizations is \(\mathbf Z\).

Fix \(p\). Split the inner product
\(a_\chi=\langle\varphi,\chi\rangle_G\) into \(p\)-sections according to the conjugacy class
of the prime-to-\(p\) part \(s\). In \(A=C_G(s)\), Lemma 2.2 replaces the indicator of
\(p\)-elements by a \(\mathbf Z_{(p)}\)-linear combination of permutation characters induced
from \(p\)-subgroups \(Q\leq A\). Fourier inversion on the cyclic group
\(\langle s\rangle\), whose order is prime to \(p\), rewrites each section as a linear
combination of inner products on

$$
\langle s\rangle\times Q.
$$

This group is elementary. By hypothesis the restriction of \(\varphi\) to it is a
generalized character, so all those inner products are integers. The only denominators are
the \(p\)-units from Lemma 2.2 and \(|\langle s\rangle|\). Thus
\(a_\chi\in\mathbf Z_{(p)}\). Since this holds for every \(p\), \(a_\chi\in\mathbf Z\).
\(\square\)

Here is the change of variables in that argument. The contribution of the section of \(s\)
is

$$
\frac1{|C_G(s)|}
\sum_{\substack{u\in C_G(s)\\u\text{ a }p\text{-element}}}
\varphi(su)\chi((su)^{-1}).
\tag{2.3a}
$$

Write the \(p\)-element indicator as
\(\sum_Qc_Q\operatorname{Ind}_Q^{C_G(s)}1\), with
\(c_Q\in\mathbf Z_{(p)}\). Expanding the induced character replaces the sum over \(u\) by
sums over conjugates \(xqx^{-1}\), \(q\in Q\). Since \(x\) centralizes \(s\), the product
\(sxqx^{-1}\) is conjugate to \(sq\). Now insert

$$
\mathbf 1_{\{s\}}(t)
=\frac1{|\langle s\rangle|}
\sum_{\alpha\in\widehat{\langle s\rangle}}
\alpha(ts^{-1})
\tag{2.3b}
$$

on the cyclic factor. The pairs \(tq\) run through
\(\langle s\rangle\times Q\), and the resulting sum is, up to a root of unity and the
displayed \(p\)-unit denominators, an inner product

$$
\left\langle
\varphi|_{\langle s\rangle\times Q},
\chi|_{\langle s\rangle\times Q}\otimes\alpha
\right\rangle.
\tag{2.3c}
$$

The roots of unity are integral. The calculation therefore places each section in the
localization of a cyclotomic integer ring at every prime above \(p\). The total
\(a_\chi\) is rational, so intersecting those localizations with \(\mathbf Q\) gives
\(\mathbf Z_{(p)}\). This supplies the arithmetic detail hidden by the phrase “Fourier
inversion rewrites.”

The proof has not used linear characters of a nonabelian \(p\)-group to separate its elements;
they cannot do so. Permutation characters provide the \(p\)-element projector, and
monomiality enters only afterward.

### 2.4 Integral Brauer induction

Let \(R(G)\) be the integral character lattice with its orthonormal basis
\(\operatorname{Irr}(G)\). Let \(X\) be the sublattice generated by

$$
\operatorname{Ind}_H^G\theta
\tag{2.3}
$$

for elementary \(H\) and linear \(\theta\).

**Theorem 2.4 (integral Brauer induction).** One has \(X=R(G)\). In particular, there are
elementary subgroups \(H_i\), linear characters \(\theta_i\), and integers \(n_i\) such that

$$
\boxed{1_G=\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i.}
\tag{2.4}
$$

**Proof.** Define the dual lattice

$$
X^\vee=\{\varphi\in R(G)\otimes\mathbf Q:
\langle\varphi,x\rangle_G\in\mathbf Z\text{ for all }x\in X\}.
$$

Take \(\varphi\in X^\vee\). If \(H\) is elementary and \(\xi\) is irreducible on \(H\),
Proposition 2.1 writes \(\xi=\operatorname{Ind}_D^H\theta\), where \(D\leq H\) is elementary.
Frobenius reciprocity gives

$$
\langle\operatorname{Res}_H^G\varphi,\xi\rangle_H
=\langle\varphi,\operatorname{Ind}_D^G\theta\rangle_G\in\mathbf Z.
$$

Thus every elementary restriction of \(\varphi\) is a generalized character.
Theorem 2.3 gives \(\varphi\in R(G)\), so \(X^\vee=R(G)\). The lattice \(R(G)\) is self-dual.
A proper full-rank sublattice has a strictly larger dual, while a lower-rank subgroup has a
nonlattice dual. Hence \(X=R(G)\). Apply this to \(1_G\). \(\square\)

Evaluating (2.4) at the identity gives the indispensable rank identity

$$
\sum_i n_i[G:H_i]=1.
\tag{2.5}
$$

The coefficients cannot all be nonnegative when \(G\) is not elementary. Otherwise (2.5)
would force a nonzero term with \(H_i=G\), contrary to the allowed subgroup class.

### 2.5 Two diagnostic relations

For \(S_3\), let \(C_2\) be generated by a transposition, let \(C_3=A_3\), and let
\(\omega\) be a nontrivial character of \(C_3\). On the classes
\(1,(12),(123)\),

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

with \(p\) odd and \(\theta_j(r)=\zeta_p^j\),

$$
1_{D_{2p}}=
\operatorname{Ind}_{\langle s\rangle}^{D_{2p}}1-
\sum_{j=1}^{(p-1)/2}
\operatorname{Ind}_{\langle r\rangle}^{D_{2p}}\theta_j.
\tag{2.7}
$$

At a reflection the first term has value one and the others vanish. At \(r^k\neq1\),
the sum of the induced characters is
\(\sum_{j=1}^{p-1}\zeta_p^{jk}=-1\). At the identity the right side is
\(p-(p-1)=1\). This proves the relation and displays both the negative signs and the required
cyclotomic coefficient field.

## 3. Induction, reciprocity, and Mackey theory

### 3.1 Finite-index induction

Let \(J\) be an open subgroup of a profinite group \(G\), and let \(W\) be a finite-dimensional
continuous representation of \(J\) over a characteristic-zero field \(L\). Define

$$
\operatorname{Ind}_J^GW=L[G]\otimes_{L[J]}W.
\tag{3.1}
$$

Only finitely many cosets occur. Choosing representatives identifies the induced space with
\([G:J]\) copies of \(W\); the \(G\)-action is a locally constant permutation of the copies
followed by the continuous \(J\)-action. Hence the induction is continuous and

$$
\dim\operatorname{Ind}_J^GW=[G:J]\dim W.
\tag{3.2}
$$

If \(W\) is semisimple and its restriction to a normal open subgroup \(N\subseteq J\) is
semisimple, then the induced representation is semisimple. Its restriction to \(N\) is a
finite direct sum of conjugates of \(W|_N\). Any \(N\)-equivariant projection onto a
\(G\)-stable subspace can be averaged over \(G/N\), in characteristic zero, to give a
\(G\)-equivariant projection.

### 3.2 The tensor identity and determinants

For a \(G\)-representation \(V\),

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

is well defined, \(G\)-equivariant, and has the evident inverse. This is the projection
formula that will recover the distinguished member.

For determinants, let \(r=\dim W\). Decompose the permutation of \(G/J\) made by \(g\) into
cycles. If a cycle has representative \(tJ\) and length \(d\), its internal product is
\(t^{-1}g^dt\in J\). A block determinant gives

$$
\det\operatorname{Ind}_J^GW
=\operatorname{sgn}_{G/J}^{\,r}\operatorname{Ver}_J^G(\det W),
\tag{3.4}
$$

where the transferred character is the product of the internal values over all cycles.
In particular, for a character \(\chi\) of \(G\),

$$
\operatorname{Ver}_J^G(\chi|_J)=\chi^{[G:J]}.
\tag{3.5}
$$

The same finite block proof applies to open subgroups of profinite groups.

### 3.3 Frobenius reciprocity

Evaluation at \(1\otimes W\) gives

$$
\operatorname{Hom}_G(\operatorname{Ind}_J^GW,V)
\simeq\operatorname{Hom}_J(W,V|_J).
\tag{3.6}
$$

The inverse sends a \(J\)-map \(a\) to \(g\otimes w\mapsto ga(w)\). At finite index,
induction and coinduction agree, so there is also

$$
\operatorname{Hom}_G(V,\operatorname{Ind}_J^GW)
\simeq\operatorname{Hom}_J(V|_J,W).
\tag{3.7}
$$

These adjunctions are the mechanism that converts the norm of a base-field induced
representation into Hom spaces over intersection fields.

### 3.4 Mackey decomposition

For open \(H,J\leq G\), choose representatives of \(H\backslash G/J\). Then

$$
\operatorname{Res}_H^G\operatorname{Ind}_J^GW
\simeq
\bigoplus_{x\in H\backslash G/J}
\operatorname{Ind}_{H\cap xJx^{-1}}^H
({}^xW)|_{H\cap xJx^{-1}}.
\tag{3.8}
$$

Indeed, decompose the \((H,J)\)-biset \(G\) into \(HxJ\). For
\(D=H\cap xJx^{-1}\), the map

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

Let \(M/F\) be finite Galois with group \(\Gamma\), and let \(F_H=M^H\). For
\(H,J\leq\Gamma\) and \(x\in\Gamma\),

$$
M^{H\cap xJx^{-1}}=F_H\,xF_J.
\tag{3.10}
$$

Thus the Mackey intersections are composita of conjugate fixed fields.

If \(v\) is a place of \(F\), choose a place \(\widetilde v\) of \(M\) and let
\(D_v\leq\Gamma\) be its decomposition group. The places \(w\) of \(F_H\) above \(v\) are
indexed by

$$
D_v\backslash\Gamma/H,
\tag{3.11}
$$

and for the place represented by \(x\),

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

## 4. The intersection-field repair

### 4.1 Subgroups of elementary groups are subnormal

The effectivity argument compares two induced terms on

$$
D=H_i\cap xH_jx^{-1}.
\tag{4.1}
$$

It needs the selected packet over \(F_D=M^D\) to be the base change of both packets reaching
it. The fact that \(D\) need not be normal in \(H_i\) does not obstruct this. Normality in
one step is unnecessary; a prime-cyclic subnormal tower suffices.

**Lemma 4.1.** Every subgroup of a finite elementary group admits a subnormal series to the
whole group with prime cyclic successive quotients.

**Proof.** First let \(Q\leq P\) for a finite \(p\)-group. A proper subgroup of a finite
\(p\)-group is properly contained in its normalizer unless it is the whole group. To prove
this normalizer condition, let \(Q\) act by left multiplication on the cosets \(P/Q\).
The fixed cosets are precisely \(N_P(Q)/Q\). The orbit congruence gives

$$
[P:Q]\equiv[N_P(Q):Q]\pmod p.
$$

If \(Q<P\), the left side is divisible by \(p\), and the identity coset is fixed; hence the
number of fixed cosets cannot be one and \(N_P(Q)>Q\). Iterating normalizers gives

$$
Q=Q_0\triangleleft Q_1\triangleleft\cdots\triangleleft Q_s=P.
$$

Refine each \(p\)-group quotient by a composition series to obtain prime-order cyclic
quotients.

Now let \(H=C\times P\) and \(D=C'\times Q\) as in (2.2). Enlarge \(C'\) to \(C\) through
its cyclic composition series while keeping \(Q\) fixed, then enlarge \(Q\) to \(P\) through
the series above while keeping \(C\) fixed. Centrality of \(C\) and normality at each
\(p\)-step give the required subnormal series. \(\square\)

### 4.2 Prime-cyclic towers to every overlap

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

Each step is cyclic Galois of prime degree. Therefore the solvable base-change theorem applies
to \(\pi_H\) along (4.3), provided the already established admissibility ledger is retained.
Its endpoint is independent of the chosen subnormal series and has, at every place, the
restriction of the local parameter of \(\pi_H\).

This is the exact repair required by Mackey theory. The false obstruction was to demand
\(D\triangleleft H\) and one Galois step. Elementary groups are nilpotent, so their arbitrary
subgroups still admit the tower needed by solvable base change.

### 4.3 The overlap theorem

**Theorem 4.2 (intersection-field overlap).** Let \(H\leq\Gamma\) be elementary and
\(D\leq H\). Then

$$
\boxed{\operatorname{BC}_{F_D/F_H}(\pi_H)\simeq\pi_D.}
\tag{4.4}
$$

Consequently, for every coefficient embedding \(\tau\),

$$
\boxed{r_{\pi_H,\tau}|_{G_{F_D}}^{\mathrm{ss}}
\simeq r_{\pi_D,\tau}.}
\tag{4.5}
$$

Both statements commute with conjugation in \(\Gamma\).

**Proof.** Lemma 4.1 and (4.3) construct an admissible prime-cyclic tower, so the left side of
(4.4) exists. Transitivity of solvable base change gives

$$
\operatorname{BC}_{M/F_D}
\bigl(\operatorname{BC}_{F_D/F_H}(\pi_H)\bigr)
\simeq\operatorname{BC}_{M/F_H}(\pi_H)
\simeq\pi_M.
\tag{4.6}
$$

At the distinguished coefficient place, compatibility of Galois realization with base change
gives

$$
r_{\operatorname{BC}_{F_D/F_H}(\pi_H),\lambda_0}
\simeq\rho|_{G_{F_D}}.
\tag{4.7}
$$

The left side is cuspidal. If it were a two-character isobaric sum, its associated
semisimple Galois representation would be a sum of two characters. But
\(\rho|_{G_{F_D}}\) is absolutely irreducible: the controlled top was chosen disjoint from
the residual-image field, so the residual restriction remains absolutely irreducible, and a
reducible characteristic-zero representation would have reducible residual semisimplification
after choosing a stable lattice. This contradiction proves cuspidality.

The selected packet \(\pi_D\) has the same realization by (1.4). Hence their good Hecke
polynomials agree. Both packets have the selected central character and lie in the same
transfer range. Strong multiplicity one identifies them, proving (4.4).

Compatibility of attached Galois representations with solvable base change now proves (4.5)
for every \(\tau\); no density theorem is needed. Conjugating the subgroup chain and every
packet proves the last assertion. \(\square\)

For two elementary groups \(H_i,H_j\), apply the theorem twice to
\(D=H_i\cap xH_jx^{-1}\), once inside \(H_i\) and once inside \(xH_jx^{-1}\). The two routes
to \(F_D\) therefore meet at the same selected packet \(\pi_D\).

### 4.4 Why top-field agreement is not enough

Suppose two irreducible representations of \(G_{F_D}\) have isomorphic restrictions to
\(G_M\). They can differ by a character of the finite quotient

$$
G_{F_D}/G_M\simeq D.
\tag{4.8}
$$

Thus equality only over \(M\) does not determine the Hom space in Mackey's formula. Theorem
4.2 removes precisely this quotient-character ambiguity before the Brauer twists are inserted.
It does so by actual solvable base change on the intersection field, not by assuming
effectivity over \(F\), and not by importing coherent family assembly.

## 5. The arithmetic Brauer datum

### 5.1 Coefficient fields and character avatars

Fix an integral Brauer relation

$$
\mathfrak B=\{(H_i,\theta_i,n_i)\}_{i=1}^t,
\qquad
1_\Gamma=\sum_i n_i\operatorname{Ind}_{H_i}^{\Gamma}\theta_i.
\tag{5.1}
$$

Choose one finite Galois number field \(K\) containing:

- all values of the \(\theta_i\);
- the Hecke fields, central-character values, and finite local-type values of the packets
  \(\pi_{H_i}\);
- the corresponding data for the finitely many Mackey intersection packets; and
- the coefficients of all good local polynomials used below.

Only finitely many groups, packets, double cosets, and finite character values occur, so one
such \(K\) exists.

Three coefficient fields should not be merged. The Hecke field of \(\pi_H\) is generated by
its unramified Hecke eigenvalues and central character. A field of definition for a Galois
realization can be larger because an irreducible representation with a given character can
have a nontrivial Schur index. A local-type field can also be larger because individual
inertial characters and intertwining operators need not lie in the symmetric trace field.
The field \(K\) is a common algebraic ledger containing all three kinds of value. It is not
asserted to be minimal.

For a finite place \(\lambda\) of \(K\), the realization of one packet may initially require a
finite extension \(C_{H,\lambda}/K_\lambda\). Since the Brauer datum and its intersection
list are finite, their compositum in \(\overline{\mathbf Q}_{q_\lambda}\) is still finite.
All termwise comparisons can therefore be made over one finite local field
\(C_\lambda\). Faithful scalar extension preserves ranks, determinant characters, Hom
dimensions after splitting, and equality of semisimple classes. This justifies enlarging local
fields during the proof without pretending that the enlarged field is a common global field of
matrix entries.

Inflation along

$$
G_{F_i}\twoheadrightarrow G_{F_i}/G_M\simeq H_i
\tag{5.2}
$$

turns \(\theta_i\) into a finite-image Galois character. Global class field theory gives its
finite-order Hecke avatar \(\psi_i\). In the arithmetic reciprocity convention,

$$
\psi_{i,\tau}(\operatorname{Frob}_w)
=\tau\bigl(\psi_i(\varpi_w)\bigr)
=\theta_{i,\tau}(\operatorname{Frob}_w)
\tag{5.3}
$$

at unramified places. All values are roots of unity, so the rank-one character has a stable
lattice over the integers of any containing local coefficient field.

Field conjugation and coefficient conjugation are different. For \(x\in\Gamma\),
\(F_H\) moves to \(xF_H=F_{xHx^{-1}}\). For
\(\sigma\in\operatorname{Gal}(K/\mathbf Q)\), the field remains fixed and the eigenvalues
move. The packet ledger makes these actions commute.

The twist affects every arithmetic ledger in a prescribed way. If
\(\omega_{\pi_{H_i}}\) is the central character, then

$$
\omega_{\pi_{H_i}\otimes\psi_i}
=\omega_{\pi_{H_i}}\psi_i^2,
\qquad
\det(r_{\pi_{H_i},\tau}\otimes\theta_{i,\tau})
=\det(r_{\pi_{H_i},\tau})\theta_{i,\tau}^2.
\tag{5.3a}
$$

At an unramified place it multiplies both Frobenius roots by
\(\theta_i(\operatorname{Frob}_w)\). At a ramified place it multiplies both inertial
characters by the same finite character and leaves monodromy unchanged. It can change the
conductor through cancellation on the last ramification layer, so there is no valid universal
formula replacing the conductor of a twist by the maximum of two conductor exponents.

The quotient characters also record the ambiguity in solvable descent. Two extensions of the
same absolutely irreducible top representation through one cyclic step differ by a character
of the cyclic quotient. The extending representation \(\rho\) selected the untwisted packet
\(\pi_H\); the independent \(\theta_i\) is then deliberately inserted by the Brauer relation.
These two uses of quotient characters must not be conflated. The first resolves a descent
torsor; the second is part of the signed induction identity.

### 5.2 Termwise Galois and automorphic operations

For an embedding

$$
\tau:K\hookrightarrow\Omega_\tau,
\tag{5.4}
$$

where \(\Omega_\tau\) is an algebraically closed nonarchimedean characteristic-zero field, put

$$
U_{i,\tau}=r_{\pi_{H_i},\tau}\otimes\theta_{i,\tau}
\tag{5.5}
$$

and

$$
A_{i,\tau}=
\operatorname{Ind}_{G_{F_i}}^{G_F}U_{i,\tau}.
\tag{5.6}
$$

This is actual finite Galois induction, of rank \(2[F_i:F]\).

On the automorphic side, \(\pi_{H_i}\otimes\psi_i\) is an actual cuspidal
\(\operatorname{GL}_2(\mathbf A_{F_i})\)-representation. Its attached Galois realization is
\(U_{i,\tau}\). At every place \(v\) of \(F\), the local parameter associated with the
Galois induction is

$$
\bigoplus_{w\mid v}
\operatorname{Ind}_{W_{(F_i)_w}}^{W_{F_v}}
\operatorname{rec}_{(F_i)_w}
\bigl((\pi_{H_i}\otimes\psi_i)_w\bigr).
\tag{5.7}
$$

Thus Galois induction and the automorphic local data agree term by term.

No general global automorphic induction of a rank-two packet from a possibly nonnormal
\(F_i/F\) is used or asserted. The phrase **formal automorphic induction** will mean the
collection of local parameters in (5.7), or equivalently the standard \(L\)-function identity

$$
L_F^S(A_{i,\tau},s)
=L_{F_i}^{S_{F_i}}(\pi_{H_i}\otimes\psi_i,s)
\tag{5.8}
$$

outside a sufficiently large finite set. Formula (5.8) follows from the local cyclic-block
calculation in Section 6.1. It is Artin formalism, not the construction of an automorphic
representation of \(\operatorname{GL}_{2[F_i:F]}(\mathbf A_F)\).

There are therefore three honest operations in each term:

1. solvable base change or selected descent relates \(\pi_{H_i}\) to \(\pi_M\);
2. automorphic twisting over \(F_i\) relates \(\pi_{H_i}\) to
   \(\pi_{H_i}\otimes\psi_i\); and
3. finite Galois induction carries the attached representation from \(G_{F_i}\) to \(G_F\).

Only the third crosses the generally nonsolvable bottom. Its automorphic shadow is (5.7)--(5.8).
This variance is exactly what the available transfer theorems justify.

### 5.3 The virtual base-field family

Define

$$
\mathcal R_{\mathfrak B,\tau}
=\sum_i n_i[A_{i,\tau}]
\tag{5.9}
$$

in the Grothendieck group of continuous semisimple representations of \(G_F\).
Writing \(n_i=n_i^+-n_i^-\) gives actual semisimple representations

$$
R_\tau^\pm=\bigoplus_i A_{i,\tau}^{\oplus n_i^\pm},
\qquad
\mathcal R_{\mathfrak B,\tau}=[R_\tau^+]-[R_\tau^-].
\tag{5.10}
$$

At the distinguished embedding \(\tau_0\), equations (1.4), (3.3), and (5.1) give

$$
\begin{aligned}
\mathcal R_{\mathfrak B,\tau_0}
&=\sum_i n_i
\left[\operatorname{Ind}_{G_{F_i}}^{G_F}
(\rho|_{G_{F_i}}\otimes\theta_i)\right]\\
&=[\rho]\cdot
\sum_i n_i[\operatorname{Ind}_{G_{F_i}}^{G_F}\theta_i]
=[\rho].
\end{aligned}
\tag{5.11}
$$

This is an equality of semisimple classes before any Frobenius-density argument.

### 5.4 Rank and determinant

By (2.5),

$$
\dim\mathcal R_{\mathfrak B,\tau}
=2\sum_i n_i[\Gamma:H_i]=2.
\tag{5.12}
$$

The determinant requires more than the rank identity. Apply determinant to the
one-dimensional relation (5.1). Formula (3.4) gives

$$
\prod_i
\left(\operatorname{sgn}_{\Gamma/H_i}
\operatorname{Ver}_{H_i}^{\Gamma}\theta_i\right)^{n_i}=1.
\tag{5.13}
$$

Squaring removes the permutation signs:

$$
\prod_i
\left(\operatorname{Ver}_{H_i}^{\Gamma}\theta_i\right)^{2n_i}=1.
\tag{5.14}
$$

Every \(r_{\pi_{H_i},\tau}\) has determinant
\(\chi_\tau|_{G_{F_i}}\). The twist contributes \(\theta_i^2\), and the permutation sign in
the induction of a rank-two representation occurs to the even power two. Using (3.4),
(3.5), (5.14), and (2.5),

$$
\begin{aligned}
\det\mathcal R_{\mathfrak B,\tau}
&=\chi_\tau^{\sum_i n_i[\Gamma:H_i]}
\prod_i(\operatorname{Ver}_{H_i}^{\Gamma}\theta_i)^{2n_i}\\
&=\boxed{\chi_\tau}.
\end{aligned}
\tag{5.15}
$$

At this stage (5.15) is an actual determinant line of a virtual class. It becomes the
determinant of an actual rank-two representation only after effectivity.

The \(S_3\) relation checks every exponent. The induction from \(C_2\) has index three, so a
rank-two representation of determinant \(\chi|_{C_2}\) induces with determinant \(\chi^3\);
the coset sign is squared. The induction from \(C_3\) has index two. After twisting by
\(\omega\), its determinant is

$$
\chi^2\operatorname{Ver}_{C_3}^{S_3}(\omega^2).
$$

For a rotation, the transfer pairs \(\omega(r)\) with \(\omega(r^{-1})\); for a reflection,
the length-two coset cycle contributes \(\omega(s^2)\). Both are one. Thus the signed
determinant is

$$
\chi^3(\chi^2)^{-1}=\chi.
\tag{5.16}
$$

The calculation shows why the permutation sign and the transferred square are different
issues. Omitting either can introduce a spurious quadratic character.

## 6. Frobenius polynomials and local records

### 6.1 The unramified cyclic-block calculation

Let \(v\) be a finite place of \(F\) at which \(F_i/F\), \(U_{i,\tau}\), and
\(\theta_i\) are unramified. For \(w\mid v\), let \(f_w=f(w/v)\), and let
\(\alpha_{i,w},\beta_{i,w}\) be the eigenvalues of arithmetic Frobenius on
\(U_{i,\tau}\) at \(w\).

On the coset blocks belonging to \(w\), \(\operatorname{Frob}_v\) acts in a cycle of length
\(f_w\). Its \(f_w\)-th power acts inside one block as \(\operatorname{Frob}_w\). On an
\(\alpha_{i,w}\)-eigenline the block has basis \(e_0,\ldots,e_{f_w-1}\) with

$$
\operatorname{Frob}_v e_j=e_{j+1},\qquad
\operatorname{Frob}_v e_{f_w-1}=\alpha_{i,w}e_0.
$$

Its characteristic series is \(1-\alpha_{i,w}T^{f_w}\). Therefore

$$
\det(1-\operatorname{Frob}_vT\mid A_{i,\tau})
=\prod_{w\mid v}
(1-\alpha_{i,w}T^{f_w})(1-\beta_{i,w}T^{f_w}).
\tag{6.1}
$$

If

$$
Q_{i,w}(X)=X^2-b_{i,w}X+q_w
$$

is the untwisted packet polynomial and
\(\zeta_{i,w}=\theta_i(\operatorname{Frob}_w)\), then (6.1) is the image under \(\tau\) of

$$
\prod_{w\mid v}
\left(
1-b_{i,w}\zeta_{i,w}T^{f_w}
\zeta_{i,w}^2q_wT^{2f_w}
\right).
\tag{6.2}
$$

For an inert quadratic place, the variable is \(T^2\), so the trace of
\(\operatorname{Frob}_v\) is zero. The trace \(b_{i,w}\) belongs to
\(\operatorname{Frob}_v^2\). This is the simplest test against a wrong Frobenius power.

The three splitting types in a non-Galois cubic field give a fuller test. If \(F_i/F\) has
degree three and \(v\) splits completely as \(w_1w_2w_3\), the induced rank-six factor is

$$
\prod_{j=1}^3
\left(1-b_{i,w_j}\zeta_{i,w_j}T+
\zeta_{i,w_j}^2q_vT^2\right).
\tag{6.2a}
$$

For splitting type \((1,2)\), it is

$$
\left(1-b_{i,w_1}\zeta_{i,w_1}T+\zeta_{i,w_1}^2q_vT^2\right)
\left(1-b_{i,w_2}\zeta_{i,w_2}T^2+\zeta_{i,w_2}^2q_v^2T^4\right).
\tag{6.2b}
$$

At an inert place of residue degree three, it is

$$
1-b_{i,w}\zeta_{i,w}T^3+\zeta_{i,w}^2q_v^3T^6.
\tag{6.2c}
$$

These formulas are not different conventions. They are the characteristic polynomials of
cycles of lengths \(1\), \(2\), and \(3\) on the coset set. In an \(S_3\) Brauer relation,
one of these rank-six factors is divided by a rank-four quadratic-field factor. The
distinguished member proves that their quotient is the quadratic expression (6.5); the degree
calculation \(6-4=2\) alone does not.

### 6.2 Common quadratic polynomials

For \(v\) outside one finite exceptional set, define in \(K(T)^\times\)

$$
D_{v,\mathfrak B}(T)=
\prod_i\prod_{w\mid v}
\left(
1-b_{i,w}\zeta_{i,w}T^{f_w}
\zeta_{i,w}^2q_wT^{2f_w}
\right)^{n_i}.
\tag{6.3}
$$

Negative \(n_i\) make this a rational function a priori. By (6.1), its image under \(\tau\)
is the virtual characteristic series of \(\mathcal R_{\mathfrak B,\tau}\).
At \(\tau_0\), equation (5.11) gives

$$
\tau_0(D_{v,\mathfrak B}(T))
=\det(1-\rho(\operatorname{Frob}_v)T).
\tag{6.4}
$$

The embedding \(K\hookrightarrow\Omega_{\tau_0}\) is injective. Hence the rational function
in (6.3) is already a degree-two polynomial in \(K[T]\). Write

$$
D_{v,\mathfrak B}(T)=1-a_vT+q_vT^2,
\qquad
P_v(X)=X^2-a_vX+q_v.
\tag{6.5}
$$

The constant term in the monic polynomial is forced by (5.15). For every \(\tau\),

$$
\det(1-\operatorname{Frob}_vT\mid\mathcal R_{\mathfrak B,\tau})
=1-\tau(a_v)T+q_vT^2.
\tag{6.6}
$$

Polynomial cancellation is not effectivity. Equation (6.6) is an identity of determinants of
positive and negative representations. It will become the characteristic polynomial of one
actual representation only in Chapter 7.

### 6.3 Local types and monodromy

At every finite place \(v\), local Mackey gives

$$
\mathcal R_{\mathfrak B,\tau}|_{G_{F_v}}
=\sum_i n_i\sum_{w\mid v}
\left[
\operatorname{Ind}_{G_{(F_i)_w}}^{G_{F_v}}
\left(r_{\pi_{H_i},\tau,w}\otimes\theta_{i,\tau,w}\right)
\right].
\tag{6.7}
$$

When \(v\) differs from the coefficient residue characteristic, the Weil--Deligne functor
commutes with direct sums, restriction, finite induction, and finite-order twisting. Thus
(6.7) records the full Weil action and monodromy operator. It does not reconstruct either
from the good-prime trace.

The common local cases behave as follows.

If \(L/K\) and the rank-two parameter are unramified, induction is unramified and Frobenius is
the cycle described in Section 6.1. If the parameter is unramified but \(L/K\) is ramified,
inertia permutes the embeddings of \(L\), so induction can be ramified even though its source
is not. This is the permutation-ramification contribution measured by the discriminant.

For a finite tame type with \(N=0\), an unramified field restriction preserves the inertia
group, while a scalar finite-order twist multiplies both inertial eigencharacters. Their ratio
is unchanged, but the actual type is changed unless the scalar character is trivial. At the
split dyadic place of the critical application the scalar characters are trivial, which is why
the primitive order-three pair survives literally.

For special or Steinberg type, \(N\) has rank one. A finite-order twist does not change \(N\),
restriction carries it to the restricted space, and induction places its conjugates on the
coset blocks. Thus a good-prime polynomial could never justify declaring \(N=0\). The
controlled packets happen to have \(N=0\), and that fact comes from their local ledger.

At a place above the coefficient residue characteristic, a Weil--Deligne parameter is not a
substitute for an integral \(p\)-adic Hodge condition. An unramified finite-order twist has
Hodge--Tate weight zero and preserves crystalline weights, but changes Frobenius and the
fixed-determinant component. A ramified finite-order twist can destroy crystallinity even
though its numerical Hodge--Tate weights are zero. For that reason all coefficient-prime
claims below are made member by member.

For a finite extension \(L/K\) and a finite-inertia Weil representation \(u\),

$$
a_K(\operatorname{Ind}_{W_L}^{W_K}u)
=\dim(u)d(L/K)+f(L/K)a_L(u).
\tag{6.8}
$$

To prove it, pass to a finite Galois extension through which inertia acts. The Artin character
\(\mathfrak a_{E/K}\) satisfies

$$
\operatorname{Res}_{\operatorname{Gal}(E/L)}^{\operatorname{Gal}(E/K)}
\mathfrak a_{E/K}
=f(L/K)\mathfrak a_{E/L}
+d(L/K)\operatorname{Reg}_{\operatorname{Gal}(E/L)}.
$$

Away from the identity this is the equality of lower-ramification contributions; at the
identity it is transitivity of the different. Pairing with the character of \(u\) and applying
Frobenius reciprocity proves (6.8). If a Weil--Deligne pair has nonzero monodromy, its usual
monodromy correction must be added. The critical-spine packets have \(N=0\), but the formula
(6.7) retains \(N\) rather than silently discarding it.

### 6.4 Sensitive places and lattices

In the critical application, \(2\) splits completely in \(M\). Therefore every completion
\((F_i)_w\) above \(2\) is \(F_2\), every quotient character \(\theta_i\) is locally trivial,
and every term carries the same primitive tame order-three parameter. Before effectivity this
is a virtual repetition of one block.

At the distinguished coefficient prime \(\ell\), the controlled completions are unramified.
The \(\theta_i\) are unramified there. They preserve Hodge--Tate weights and finite-flatness of
each individual lattice, but change its determinant by \(\theta_i^2\). Equation (5.14) cancels
those determinant translations only in the signed determinant line.

At a real place, every \(F_i\) is totally real and the local extension inside \(M\) is
\(\mathbf R/\mathbf R\). The quotient characters are trivial on real decomposition groups.
Every packet therefore contributes the same odd weight-two block

$$
1\oplus\operatorname{sgn}.
\tag{6.9}
$$

The induced term contains \([F_i:F]=[\Gamma:H_i]\) copies. Equation (2.5) reduces the signed
archimedean class to one copy. Equivalently, in arithmetic weight-two normalization, the signed
gamma factor is one \(\Gamma_{\mathbf C}(s)\). This local effectivity follows from identical
blocks and does not imply global effectivity.

Choose a finite set \(S_0\) containing the places above \(2\ell\), every place ramified in
\(M/F\), every place below the conductor of one of the finitely many packets or characters,
and every place excluded by the local comparison theorem. If \(\tau\) has residue
characteristic \(q\), put

$$
S_\tau=S_0\cup\{v:v\mid q\}.
\tag{6.10}
$$

Every \(A_{i,\tau}\), hence \(R_\tau^\pm\), is unramified outside \(S_\tau\).
After effectivity, the remaining direct summand is also unramified there. At places in
\(S_\tau\), the controlling invariant is the full local Mackey record (6.7), not an
extrapolation from the good polynomial.

Every actual induced summand admits a stable lattice. Indeed, the image of a profinite group is
compact. Starting from a lattice \(\Lambda_0\), all translates lie between
\(\varpi^m\Lambda_0\) and \(\varpi^{-m}\Lambda_0\) for one \(m\); their sum is a finitely
generated stable lattice. Hence \(R_\tau^+\) and \(R_\tau^-\) have lattices. There is no
canonical map from the negative lattice to the positive lattice, and the virtual difference
does not define a rank-two quotient. Characteristic-zero effectivity will yield a stable
lattice for the remaining constituent, but not integral cancellation or a preferred
finite-flat lattice at a new coefficient prime.

## 7. Character norm and effectivity

### 7.1 The Hom inner product

Over an algebraically closed characteristic-zero field, write a semisimple representation as
\(\bigoplus_\alpha S_\alpha^{m_\alpha}\). The semisimple Grothendieck group is free on the
irreducible classes. Define

$$
\langle[V],[W]\rangle_G=\dim\operatorname{Hom}_G(V,W)
\tag{7.1}
$$

and extend bilinearly. Schur's lemma gives

$$
\left\langle\sum_\alpha c_\alpha[S_\alpha],
\sum_\alpha d_\alpha[S_\alpha]\right\rangle_G
=\sum_\alpha c_\alpha d_\alpha.
\tag{7.2}
$$

The norm

$$
\|X\|_G^2=\langle X,X\rangle_G=\sum_\alpha c_\alpha^2
\tag{7.3}
$$

is a nonnegative integer. It is defined algebraically; no Haar averaging over an infinite
profinite group is involved.

**Lemma 7.1.** If \(\|X\|^2=1\), then \(X=[S]\) or \(X=-[S]\) for one irreducible \(S\).
If also \(\dim X=2\), then \(X=[S]\) and \(\dim S=2\).

**Proof.** Integral coefficients satisfying \(\sum c_\alpha^2=1\) have exactly one nonzero
entry, equal to \(1\) or \(-1\). Positive dimension excludes the negative sign. \(\square\)

This is where the integrality of Brauer induction is finally used. A rational virtual
character of norm one need not have a single integral coefficient.

There is also a structural reason all induced terms can be compared by one Gram matrix.
Let \(N\triangleleft G\) have finite index, and let \(T\) be an irreducible \(N\)-representation
whose isomorphism class is invariant under \(G\). If \(V\) is an irreducible
\(G\)-representation lying above \(T\), then

$$
V|_N\simeq T^{\oplus e}
\tag{7.3a}
$$

for some \(e\). Indeed, the \(G\)-translates of one irreducible constituent of \(V|_N\)
fill \(V\), and invariance makes all of them isomorphic to \(T\). The multiplicity space

$$
\operatorname{Hom}_N(T,V)
\tag{7.3b}
$$

carries a projective representation of \(G/N\). To see the projective factor, choose
intertwiners \(I_g:T\to{}^gT\). Schur's lemma gives scalars \(c(g,h)\) with

$$
I_gI_h=c(g,h)I_{gh}.
\tag{7.3c}
$$

Associativity makes \(c\) a \(2\)-cocycle. The multiplicity space has the inverse multiplier,
so its tensor product with \(T\) is an honest \(G\)-representation. No vanishing of this
cocycle is needed for effectivity.

In the application, \(N=G_M\), \(G=G_F\), and
\(T=r_{\pi_M,\tau}\). Every \(A_{i,\tau}\) restricts to

$$
A_{i,\tau}|_{G_M}
\simeq T^{\oplus[\Gamma:H_i]},
\tag{7.3d}
$$

because the quotient twist is trivial on \(G_M\) and the conjugate packet realizations are
identified. Hence every induced term belongs to the same Clifford block above \(T\).
Restriction of the signed class to \(G_M\) is

$$
\mathcal R_{\mathfrak B,\tau}|_{G_M}
=\left(\sum_i n_i[\Gamma:H_i]\right)[T]=[T].
\tag{7.3e}
$$

This check is necessary but not sufficient: different projective representations of
\(\Gamma\) can become the same multiple of \(T\) on \(G_M\). Mackey intersections retain the
quotient compatibility that restriction to \(G_M\) forgets. The norm calculation below is
therefore the numerical form of Clifford descent, not a redundant repetition of (7.3e).

### 7.2 The Mackey Gram matrix

Let

$$
G_\tau(i,j)=\langle A_{i,\tau},A_{j,\tau}\rangle_{G_F}.
\tag{7.4}
$$

Then

$$
\|\mathcal R_{\mathfrak B,\tau}\|^2
=\sum_{i,j}n_in_jG_\tau(i,j).
\tag{7.5}
$$

For \(x\in H_i\backslash\Gamma/H_j\), put

$$
D_{ij}(x)=H_i\cap xH_jx^{-1},
\qquad
L_{ij}(x)=M^{D_{ij}(x)},
\tag{7.6}
$$

and define characters on \(D_{ij}(x)\) by

$$
\alpha_{ij,x}=\theta_i|_{D_{ij}(x)},\qquad
\beta_{ij,x}=({}^x\theta_j)|_{D_{ij}(x)},\qquad
\delta_{ij,x}=\beta_{ij,x}\alpha_{ij,x}^{-1}.
\tag{7.7}
$$

Frobenius reciprocity and the Hom form of Mackey theory give

$$
\begin{aligned}
G_\tau(i,j)=
\sum_{x\in H_i\backslash\Gamma/H_j}
\dim\operatorname{Hom}_{G_{L_{ij}(x)}}\bigl(
&r_{\pi_{H_i},\tau}|_{G_{L_{ij}(x)}}\otimes\alpha_{ij,x,\tau},\\
&{}^xr_{\pi_{H_j},\tau}|_{G_{L_{ij}(x)}}\otimes\beta_{ij,x,\tau}
\bigr).
\end{aligned}
\tag{7.8}
$$

Theorem 4.2 identifies both untwisted representations with the selected overlap realization
\(r_{\pi_{D_{ij}(x)},\tau}\). Therefore

$$
G_\tau(i,j)=
\sum_x
\dim\operatorname{Hom}_{G_{L_{ij}(x)}}\left(
r_{\pi_D,\tau},
r_{\pi_D,\tau}\otimes\delta_{ij,x,\tau}
\right).
\tag{7.9}
$$

For the \(S_3\) relation, write \(A_\tau\) for the induction from the cubic fixed field and
\(B_\tau\) for the twisted induction from the quadratic fixed field. Then

$$
\|\mathcal R_\tau\|^2
=\langle A_\tau,A_\tau\rangle
+\langle B_\tau,B_\tau\rangle
-2\langle A_\tau,B_\tau\rangle.
\tag{7.9a}
$$

The cross term is not optional. Its double-coset intersections are trivial, so it is computed
over the full top compositum. The self-pairing of \(A_\tau\) also has the identity
\(C_2\)-intersection and a trivial intersection from the other double coset; the self-pairing
of \(B_\tau\) is organized by the normal subgroup \(C_3\). Each term asks whether one explicit
finite quotient character is a self-twist of the corresponding selected overlap packet.
Replacing (7.9a) by a difference of the two endomorphism dimensions would discard the
intertwining that makes cancellation possible.

### 7.3 Self-twists on overlap fields

We need two facts about the selected overlap packet.

**Proposition 7.2.** For every coefficient embedding \(\tau\), the realization
\(r_{\pi_D,\tau}\) is absolutely irreducible.

**Proof.** Suppose its semisimplification were \(\eta_1\oplus\eta_2\). The representation is
de Rham with integral labeled weights because it comes from a parallel-weight-two packet.
Rank-one reciprocity therefore makes each \(\eta_i\) the avatar of an algebraic Hecke
character \(\mu_i\). At almost every place the Hecke polynomial of \(\pi_D\) is then the
polynomial of \(\mu_1\boxplus\mu_2\). Strong multiplicity one identifies \(\pi_D\) with that
isobaric sum, contradicting cuspidality. \(\square\)

For a finite-order character \(\delta\), define

$$
\operatorname{ST}(\pi_D)=
\{\delta:\pi_D\otimes\delta\simeq\pi_D\}.
\tag{7.10}
$$

**Proposition 7.3.** For every \(\tau\),

$$
\dim\operatorname{Hom}_{G_{F_D}}
(r_{\pi_D,\tau},r_{\pi_D,\tau}\otimes\delta_\tau)
=
\begin{cases}
1,&\delta\in\operatorname{ST}(\pi_D),\\
0,&\delta\notin\operatorname{ST}(\pi_D).
\end{cases}
\tag{7.11}
$$

**Proof.** Proposition 7.2 and Schur's lemma make the Hom dimension zero or one. If
\(\pi_D\otimes\delta\simeq\pi_D\), compatibility of twisting with Galois realization gives
the isomorphism for every \(\tau\). Conversely, if the Galois realizations are isomorphic for
one \(\tau\), their good algebraic Frobenius polynomials agree after an injective embedding,
and hence agree before embedding. Strong multiplicity one gives
\(\pi_D\otimes\delta\simeq\pi_D\). \(\square\)

Taking determinants shows that a self-twist satisfies \(\delta^2=1\). The converse is false;
the Hom term cannot be replaced by the indicator that \(\delta\) is quadratic.

### 7.4 Embedding independence

By Proposition 7.3, each summand in (7.9) is the coefficient-independent number

$$
\varepsilon_{ij}(x)=
\begin{cases}
1,&\delta_{ij,x}\in\operatorname{ST}(\pi_{D_{ij}(x)}),\\
0,&\text{otherwise}.
\end{cases}
\tag{7.12}
$$

Hence

$$
G_\tau(i,j)=\sum_x\varepsilon_{ij}(x)
\tag{7.13}
$$

is independent of \(\tau\). The whole Mackey Gram matrix is fixed before a coefficient
embedding is chosen. Equation (7.5) therefore shows that
\(\|\mathcal R_{\mathfrak B,\tau}\|^2\) is independent of \(\tau\).

At \(\tau_0\), equation (5.11) and absolute irreducibility of \(\rho\) give

$$
\|\mathcal R_{\mathfrak B,\tau_0}\|^2
=\dim\operatorname{End}_{G_F}(\rho)=1.
\tag{7.14}
$$

Consequently

$$
\boxed{\|\mathcal R_{\mathfrak B,\tau}\|^2=1
\quad\text{for every }\tau.}
\tag{7.15}
$$

Nothing has been transported topologically from one completion to another. What propagates is
the integral Gram matrix, whose entries were independently identified as automorphic
self-twist indicators.

### 7.5 Norm one forces positive rank two

Combine (7.15), Lemma 7.1, and the virtual rank calculation (5.12).

**Theorem 7.4 (effectivity).** For every coefficient embedding \(\tau\), there is a unique
isomorphism class of continuous absolutely irreducible two-dimensional representation

$$
r_{\mathfrak B,\tau}:G_F\longrightarrow\operatorname{GL}_2(\Omega_\tau)
\tag{7.16}
$$

such that

$$
\mathcal R_{\mathfrak B,\tau}=[r_{\mathfrak B,\tau}].
\tag{7.17}
$$

Moreover,

$$
R_\tau^+\simeq r_{\mathfrak B,\tau}\oplus R_\tau^-.
\tag{7.18}
$$

**Proof.** Norm one gives one irreducible with coefficient \(1\) or \(-1\). Virtual
dimension two forces the positive sign and dimension two. Equality of semisimple
Grothendieck classes is equality of irreducible multiplicities, which gives the actual,
noncanonical cancellation (7.18). The remaining summand is a closed invariant subspace of
the continuous representation \(R_\tau^+\), so its action is continuous. \(\square\)

This proves characteristic-zero effectivity. It does not make (7.18) an isomorphism of chosen
integral lattices.

## 8. The descent theorem

### 8.1 The effective members

Substituting (7.17) into the virtual determinant and Frobenius identities gives

$$
\det r_{\mathfrak B,\tau}=\chi_\tau
\tag{8.1}
$$

and, for every good \(v\),

$$
\det(X-r_{\mathfrak B,\tau}(\operatorname{Frob}_v))
=X^2-\tau(a_v)X+q_v.
\tag{8.2}
$$

Thus the common algebraic polynomials from Chapter 6 are now characteristic polynomials of
actual rank-two representations. Each \(r_{\mathfrak B,\tau}\) has a model over some finite
extension of the completion of \(K\) selected by \(\tau\). To see this, place the finitely many
induced summands over one finite local extension \(L\). The image of \(L[G_F]\) in their
endomorphism algebra is finite dimensional. After a finite extension \(L'/L\), its semisimple
quotient is a product of matrix algebras and every simple module has an \(L'\)-model. The
isotypic component containing the constituent in (7.18) is a tensor product of that simple
module with a finite-dimensional multiplicity space. Choosing a rank-one projector on the
multiplicity space, equivalently an idempotent in the commutant of the group action, selects
one \(G_F\)-stable copy. Its image is an \(L'\)-model of
\(r_{\mathfrak B,\tau}\).

Compactness then supplies a stable rank-two lattice. Neither the finite field of definition nor
the stable lattice is canonical.

### 8.2 Compatibility and independence

The collection

$$
\{r_{\mathfrak B,\tau}\}_\tau
\tag{8.3}
$$

is an embedding-indexed weakly compatible family over \(F\): outside one finite set enlarged
by the residue characteristic of \(\tau\), its members are unramified and have the common
polynomials (8.2). They are actual representations, not virtual classes.

More explicitly, for each finite place \(\lambda\) of \(K\), choose an embedding
\(\tau_\lambda:K\hookrightarrow\overline{\mathbf Q}_{q_\lambda}\) inducing \(\lambda\).
Theorem 7.4 gives \(r_{\lambda}:=r_{\mathfrak B,\tau_\lambda}\). Section 8.1 places it over a
finite extension of \(K_\lambda\). For every finite \(v\notin S_0\) with residue
characteristic different from \(q_\lambda\),

$$
r_\lambda\text{ is unramified at }v,\qquad
\det(X-r_\lambda(\operatorname{Frob}_v))=\tau_\lambda(P_v(X)).
\tag{8.3a}
$$

This is the usual Frobenius compatibility condition. If another embedding induces the same
\(\lambda\), the two algebraically closed realizations have the same effective virtual class
after passage to a common algebraic closure, and hence are isomorphic. What has not yet been
chosen is one descended \(K_\lambda\)-model and a coherent system of these identifications.

The isomorphism class is independent of the positive-minus-negative presentation. It is also
independent, after scalar extension, of the Brauer relation. Indeed, for two relations
\(\mathfrak B,\mathfrak B'\), form their difference. Apply the Gram calculation to the union
of the two lists, with coefficient vector \((n_i,-n'_j)\). Every cross term is again computed
on an elementary intersection field and is embedding independent. At \(\tau_0\) both virtual
classes equal \([\rho]\), so the difference has norm zero. It therefore has norm zero for every
\(\tau\), and positive definiteness of (7.3) makes the two classes equal.

Conjugating a Brauer term changes neither its induction nor the effective member. Coefficient
conjugation sends all \(a_v\), packet values, and character values through the same embedding;
it transports the effective isomorphism class accordingly. These are isomorphism-class
statements after scalar extension, not a chosen semilinear cocycle.

For later recognition, we record why an actual semisimple representation is determined by its
character.

**Proposition 8.2 (Brauer--Nesbitt recognition).** Let \(V,W\) be finite-dimensional
representations of an arbitrary group \(G\) over a characteristic-zero field. If
\(\operatorname{tr}V(g)=\operatorname{tr}W(g)\) for every \(g\in G\), then

$$
V^{\mathrm{ss}}\simeq W^{\mathrm{ss}}.
\tag{8.3b}
$$

**Proof.** Extend scalars to an algebraic closure and let \(A\) be the image of the group
algebra in \(\operatorname{End}(V\oplus W)\). Although \(G\) may be infinite, \(A\) is
finite dimensional. Its Jacobson radical kills every semisimple module, and

$$
A/\operatorname{rad}(A)\simeq\prod_jM_{d_j}(L)
$$

after scalar extension. Let \(e_j\) be the central idempotent of the \(j\)-th factor. If the
simple \(j\)-th module occurs with multiplicity \(m_j\) in \(V^{\mathrm{ss}}\), then
\(\operatorname{tr}_V(e_j)=m_jd_j\), and similarly for \(W\). Equality of traces on group
elements extends linearly to \(A\), so all these numbers agree and all multiplicities agree.
\(\square\)

If \(G\) is profinite and the representations are continuous, equality on a dense subset
suffices because trace functions are continuous. The density of a Frobenius set, when used, is
a separate arithmetic input. This book does not use such density to prove effectivity or
relation independence; the Gram norm proves both before recognition is invoked.

### 8.3 Actual local consequences

Restrict (7.18) to \(G_{F_v}\). It remains an actual isomorphism:

$$
R_\tau^+|_{G_{F_v}}
\simeq
r_{\mathfrak B,\tau}|_{G_{F_v}}
\oplus R_\tau^-|_{G_{F_v}}.
\tag{8.4}
$$

Consequently the local class in (6.7) is represented by the actual local restriction of
\(r_{\mathfrak B,\tau}\). Away from the coefficient residue characteristic, applying
Weil--Deligne turns the virtual Mackey record into the actual rank-two Weil--Deligne parameter.
Artin conductors become nonnegative actual conductors, although their expression remains the
signed sum of the termwise conductors.

At a completely split dyadic place, every induced block is a copy of the same selected
two-dimensional type. The rank identity (2.5) and actual cancellation give that type for
\(r_{\mathfrak B,\tau}\) whenever the coefficient characteristic is not two:

$$
N=0,\qquad I_2^{\mathrm{wild}}=1,\qquad T^2+T+1=0.
\tag{8.5}
$$

At a coefficient-characteristic-two member, the exact Galois restriction still exists, but the
prime-to-\(p\) Weil--Deligne interpretation is unavailable without further \(2\)-adic Hodge
theory.

At a new coefficient prime \(q\), effectivity does not prove that an arbitrary stable lattice
is finite flat. It proves only the actual \(q\)-adic local representation and the local
characteristic-zero record obtained from (6.7). Integral refinement is separate.

### 8.4 The distinguished member

At \(\tau_0\), equations (5.11) and (7.17) give

$$
r_{\mathfrak B,\tau_0}\simeq\rho
\tag{8.6}
$$

after the fixed scalar extension. The named lattice of \(\rho\), its all-level finite-flat
quotients, and its dyadic type are retained exactly. They were inputs to the selected
potential-automorphy package and are not reconstructed by subtracting induced lattices.

We can now state the main result.

**Theorem 8.1 (effective Brauer descent of automorphy).** Let \(M/F\), \(\rho\), \(\pi_M\),
and the selected packets \(\pi_H\) satisfy the input package of Section 1.2. Assume the cyclic
and solvable base-change range includes the prime-cyclic towers inside the elementary
subgroups. Then:

1. every Mackey intersection packet satisfies the overlap theorem (4.4)--(4.5);
2. every integral elementary Brauer relation produces, for every coefficient embedding
   \(\tau\), one actual continuous absolutely irreducible rank-two representation
   \(r_{\mathfrak B,\tau}\) of \(G_F\);
3. its determinant is cyclotomic, its good Frobenius polynomial is (8.2), and its local
   characteristic-zero record is the effective member of the termwise automorphic and Galois
   Mackey sum;
4. the distinguished member is \(\rho\);
5. the isomorphism class is independent, after scalar extension, of the integral Brauer
   relation and is covariant under coefficient conjugation; and
6. the members form an actual embedding-indexed weakly compatible family over the base field.

**Proof.** Integral Brauer induction is Theorem 2.4. The overlap repair is Theorem 4.2.
The virtual construction, rank, determinant, Frobenius polynomials, and local records are
Chapters 5--6. Frobenius reciprocity, Mackey theory, overlap compatibility, and self-twist
rigidity make the Gram matrix independent of the coefficient embedding. Its value at the
distinguished embedding is one, so Theorem 7.4 proves effectivity. Chapters 7--8 prove the
remaining clauses. \(\square\)

The adjective “automorphy” in the theorem records that every term comes from an actual
cuspidal automorphic packet and that all comparison of twists, overlaps, and local parameters
is automorphic. The output itself is a Galois family over \(F\).

## 9. What remains for coherent family assembly

### 9.1 What this book proves

For every embedding of a common algebraic coefficient field into an algebraically closed local
field, this book constructs an honest rank-two representation of \(G_F\). These representations:

- share algebraic good Frobenius polynomials;
- have cyclotomic determinant;
- have actual local restrictions given by the effective Mackey record;
- include the original chosen representation;
- are independent of the Brauer relation after scalar extension; and
- transform correctly under coefficient conjugation.

This is enough to remove the only representation-theoretic obstruction left by signed Brauer
induction. There are no negative constituents.

### 9.2 What Book 189 must still construct

Book 189 starts from the effective isomorphism classes just obtained. It must choose one
coefficient field \(E_0\), index members by finite places \(\lambda\) of \(E_0\), and choose
models

$$
r_\lambda:G_F\longrightarrow\operatorname{GL}_2(E_{0,\lambda}')
\tag{9.1}
$$

over finite local extensions in a way compatible with coefficient descent. It must prove that
different embeddings above the same place give the same descended member, handle any
field-of-definition or Schur-index obstruction, organize coefficient-conjugation isomorphisms
coherently, and package the common ramification and local compatibility statements into one
base-field compatible-system object.

It must also identify the original member inside that coherent indexing and, where later books
need integral information, choose stable lattices and prove their local properties. None of
these choices follows from the existence of an irreducible summand over an algebraic closure.

Thus Book 176 proves pointwise effectivity and base-field descent; Book 189 proves coherent
coefficient and family assembly. The distinction is one of descent data, not of positivity.

### 9.3 Automorphy over the base field

The signed identity of standard \(L\)-functions is

$$
\prod_i
L_{F_i}^S(\pi_{H_i}\otimes\psi_i,s)^{n_i}
=
\prod_{v\notin S}
\det(1-r_{\mathfrak B,\tau}(\operatorname{Frob}_v)q_v^{-s})^{-1}.
\tag{9.2}
$$

Before effectivity the left side was merely a meromorphic quotient of automorphic
\(L\)-functions. After effectivity its good factors belong to an actual Galois
representation. This still does not produce a cuspidal representation of
\(\operatorname{GL}_2(\mathbf A_F)\). Negative global exponents can leave poles in the signed
product, and a converse theorem would require analytic hypotheses not proved here.

If an independent automorphic descent theorem later constructs a base-field packet, strong
multiplicity one identifies it from the common good polynomials. Strong multiplicity one is a
recognition theorem; it is not an existence theorem.

## 10. Hostile audit and conclusion

### 10.1 Dependency closure

The finite-group Brauer theorem, profinite Frobenius reciprocity, Mackey decomposition,
determinant transfer, overlap repair, character norm, and positivity argument were proved in
this book.

The imported arithmetic results are exactly the substantial prerequisites:

- finite-order Hecke characters, arithmetic reciprocity, twisting, and rank-one coefficient
  control;
- cyclic base change for \(\operatorname{GL}_2\), including all-place local compatibility and
  coefficient conjugation;
- solvable iteration, transitivity, tower independence, and descent selected by an extending
  representation;
- the controlled potential-automorphy top and the selected packets over elementary fixed
  fields;
- the continuity and finite coefficient-field language for profinite representations.

The intersection-field overlap is not assumed. Lemma 4.1 proves that a Mackey intersection is
subnormal inside each elementary parent; Theorem 4.2 applies the already available solvable
base change along the resulting prime-cyclic tower. This closes the exact 187--188 interface
without a density theorem and without Book 189.

No later-book theorem is used. In particular, no coherent base-field family, changing-prime
theorem, fixed-three integral theorem, or Schoof classification enters the proof.

**Dependency verdict: READY.**

### 10.2 Nine possible failure points

**A nonnormal overlap.** The argument never promotes \(F_D/F_H\) to one Galois extension.
It constructs a subnormal prime-cyclic tower using nilpotence of \(H\).

**Agreement only over the top.** Restriction to \(G_M\) would leave a character of \(D\)
undetermined. The overlap theorem identifies the packets already over \(F_D\).

**A rational Brauer relation.** Denominators would make the norm coefficients nonintegral and
would require fractional Euler factors. Theorem 2.4 gives an integral relation.

**Positive virtual dimension.** Rank two does not imply effectivity. Effectivity follows only
after the full Mackey Gram matrix is shown embedding independent and has norm one.

**A quadratic self-twist guess.** The equation \(\delta^2=1\) is necessary but not sufficient.
Every Hom entry uses the actual automorphic self-twist test.

**Polynomiality mistaken for existence.** The quadratic rational-function cancellation in
Chapter 6 precedes effectivity and is not used as a substitute for the norm calculation.

**A missing determinant sign.** Determinant induction includes both the coset permutation sign
and transfer. Rank two kills the former termwise; the determinant of the original
one-dimensional Brauer relation cancels the transferred squares.

**Wrong local induction.** Residue degrees produce the powers \(T^{f(w/v)}\). Ramification
enters inertia and the discriminant term in the conductor, not the Frobenius-cycle length.

**Integral cancellation.** The characteristic-zero isomorphism
\(R_\tau^+\simeq r_\tau\oplus R_\tau^-\) is not reduced modulo a coefficient prime as though
it were an isomorphism of selected lattices. New finite-flat claims are reserved for separate
integral work.

These checks also rule out circularity. Effectivity on the base field is never used to prove an
overlap packet, and coherent family assembly is never used to transport a member between
coefficient places.

### 10.3 Final theorem package

For the critical-spine application \(F=\mathbf Q\), let
\(\Gamma\simeq S_d\times C_2\) and let \(\rho\) be the chosen hardly ramified lift. Then the
selected automorphic packet over \(M\) and its elementary descents determine, at every
coefficient embedding, an actual irreducible representation

$$
r_\tau:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\Omega_\tau)
\tag{10.1}
$$

with

$$
\det r_\tau=\chi_\tau,
\qquad
\det(X-r_\tau(\operatorname{Frob}_p))
=X^2-\tau(a_p)X+p
\tag{10.2}
$$

outside one fixed finite bad set and the coefficient characteristic. Its local restriction is
the actual effective member of the termwise Mackey record. At the original coefficient place
it is the named lift \(\rho\), with its named lattice and local types. The isomorphism class is
independent of the Brauer relation after scalar extension.

This is descent to the base-field Galois group and effectivity of the automorphically sourced
family. It is exactly the input Book 189 needs for coherent assembly.

### 10.4 Conclusion

Brauer induction succeeds because it replaces a nonsolvable descent by finitely many solvable
ones, but it creates subtraction. The decisive problem is therefore not the formal identity of
Euler factors. It is the simultaneous cancellation of irreducible constituents.

Mackey theory locates that problem on intersection fields. The repaired interface is now
exact: an intersection subgroup of an elementary group is subnormal, so its fixed field is
reached by a prime-cyclic tower. Solvable base change identifies both routes to the same
selected packet. Frobenius reciprocity then reduces every entry of the base-field Gram matrix
to a finite-order self-twist of one irreducible overlap realization.

Those self-twist dimensions are automorphic and independent of the coefficient embedding. At
the distinguished embedding the signed class is the original irreducible representation, so
the common norm is one. Integrality and positive virtual dimension leave only one possibility:
one honest irreducible constituent of dimension two. The virtual cyclotomic determinant,
Frobenius polynomials, and local Mackey records thereby become invariants of actual
representations on the base-field Galois group.

The remaining work is coherent rather than effective. Models over one coefficient field,
place-by-place indexing, semilinear descent, coherent local comparison, and integral lattices
must still be assembled. Keeping that boundary visible completes the descent theorem proved
here without borrowing the family that Book 189 is designed to construct.
