# Local Langlands in the Principal, Special, and Dihedral Cases

## Contents

1. [The local matching problem](#1-the-local-matching-problem)
   - [Two languages for the same local data](#11-two-languages-for-the-same-local-data)
   - [Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
   - [The normalization ledger](#13-the-normalization-ledger)
   - [The selected range and its boundary](#14-the-selected-range-and-its-boundary)
2. [The parameter side in dimension two](#2-the-parameter-side-in-dimension-two)
   - [Three shapes](#21-three-shapes)
   - [Split parameters](#22-split-parameters)
   - [Special parameters](#23-special-parameters)
   - [Quadratic-induced parameters](#24-quadratic-induced-parameters)
   - [Why the three shapes are disjoint](#25-why-the-three-shapes-are-disjoint)
3. [The representation side](#3-the-representation-side)
   - [Normalized principal series](#31-normalized-principal-series)
   - [The reducible wall](#32-the-reducible-wall)
   - [Special representations](#33-special-representations)
   - [Tame dihedral supercuspidals](#34-tame-dihedral-supercuspidals)
   - [Classification in the selected range](#35-classification-in-the-selected-range)
4. [The correspondence table](#4-the-correspondence-table)
   - [Rank one as the anchor](#41-rank-one-as-the-anchor)
   - [The three assignments](#42-the-three-assignments)
   - [Well-definedness](#43-well-definedness)
   - [Bijectivity in the selected range](#44-bijectivity-in-the-selected-range)
5. [Unramified parameters and spherical representations](#5-unramified-parameters-and-spherical-representations)
   - [The spherical line](#51-the-spherical-line)
   - [Satake roots and Frobenius roots](#52-satake-roots-and-frobenius-roots)
   - [Equal roots and the reducibility counterexample](#53-equal-roots-and-the-reducibility-counterexample)
   - [Characterization by spherical data](#54-characterization-by-spherical-data)
6. [The special correspondence](#6-the-special-correspondence)
   - [Monodromy replaces a missing Euler root](#61-monodromy-replaces-a-missing-euler-root)
   - [Construction at the reducibility wall](#62-construction-at-the-reducibility-wall)
   - [The special matching theorem](#63-the-special-matching-theorem)
   - [Why semisimplification is insufficient](#64-why-semisimplification-is-insufficient)
7. [Quadratic induction and dihedral supercuspidals](#7-quadratic-induction-and-dihedral-supercuspidals)
   - [Regular characters and irreducible induction](#71-regular-characters-and-irreducible-induction)
   - [The determinant discrepancy](#72-the-determinant-discrepancy)
   - [The tame rectifier](#73-the-tame-rectifier)
   - [The dihedral matching theorem](#74-the-dihedral-matching-theorem)
   - [Depth-zero and positive-depth examples](#75-depth-zero-and-positive-depth-examples)
8. [Central characters, twists, and contragredients](#8-central-characters-twists-and-contragredients)
   - [Central characters and determinants](#81-central-characters-and-determinants)
   - [Twists](#82-twists)
   - [Contragredients](#83-contragredients)
   - [Self-duality tests](#84-self-duality-tests)
9. [Conductors](#9-conductors)
   - [Two definitions that must agree](#91-two-definitions-that-must-agree)
   - [Principal and special formulas](#92-principal-and-special-formulas)
   - [The quadratic conductor formula](#93-the-quadratic-conductor-formula)
   - [Twisting and conductor cancellation](#94-twisting-and-conductor-cancellation)
10. [Newvectors](#10-newvectors)
    - [The first fixed line](#101-the-first-fixed-line)
    - [Proof through the Kirillov model](#102-proof-through-the-kirillov-model)
    - [Essential Whittaker functions](#103-essential-whittaker-functions)
    - [Oldforms and the parameter conductor](#104-oldforms-and-the-parameter-conductor)
11. [Euler factors](#11-euler-factors)
    - [Definitions on both sides](#111-definitions-on-both-sides)
    - [Principal factorization](#112-principal-factorization)
    - [The special factor](#113-the-special-factor)
    - [The dihedral factor](#114-the-dihedral-factor)
12. [Epsilon and gamma factors](#12-epsilon-and-gamma-factors)
    - [Additive characters and measures](#121-additive-characters-and-measures)
    - [Principal factorization](#122-principal-factorization)
    - [The monodromy correction for Steinberg](#123-the-monodromy-correction-for-steinberg)
    - [Quadratic induction and the lambda factor](#124-quadratic-induction-and-the-lambda-factor)
    - [Duality and change of additive character](#125-duality-and-change-of-additive-character)
13. [Finite extension and base change](#13-finite-extension-and-base-change)
    - [Restriction as the definition](#131-restriction-as-the-definition)
    - [Principal and special base change](#132-principal-and-special-base-change)
    - [Mackey analysis of a dihedral parameter](#133-mackey-analysis-of-a-dihedral-parameter)
    - [Conductors and newvectors after extension](#134-conductors-and-newvectors-after-extension)
    - [Euler and epsilon identities](#135-euler-and-epsilon-identities)
    - [Transitivity and compatibility checks](#136-transitivity-and-compatibility-checks)
14. [Characterization and final synthesis](#14-characterization-and-final-synthesis)
    - [A recognition theorem](#141-a-recognition-theorem)
    - [A calculation protocol](#142-a-calculation-protocol)
    - [What the selected correspondence proves](#143-what-the-selected-correspondence-proves)
    - [Conclusion](#144-conclusion)

## 1. The local matching problem

### 1.1 Two languages for the same local data

The group $G=\operatorname{GL}_2(F)$ has several visibly different irreducible representations. Some are assembled from two characters of $F^\times$ through the upper triangular subgroup. Some occur at the reducibility boundary and retain a single nonzero nilpotent direction. Others are built from a character of a quadratic field and have matrix coefficients compact modulo the center. On their face these constructions have little in common.

The local parameter side has the same trichotomy in linear algebra. A two-dimensional parameter can split as two characters, can carry one Jordan block of monodromy, or can be irreducibly induced from a character of an index-two subgroup. The local Langlands correspondence in the range of this book says that the two trichotomies are identical after the normalizations are aligned.

This assertion is stronger than a classification by names. A successful matching must preserve the invariants that enter local and global arithmetic:

$$
\begin{array}{c|c}
\text{representation}&\text{parameter}\\ \hline
\text{central character}&\text{determinant}\\
\text{determinant twist}&\text{tensor product by a character}\\
\text{contragredient}&\text{dual}\\
\text{first newvector level}&\text{Artin--monodromy conductor}\\
\text{Whittaker Euler factor}&\text{Frobenius Euler factor}\\
\text{functional-equation constant}&\text{epsilon factor}.
\end{array}
$$

It must also behave predictably after replacing $F$ by a finite extension. These compatibilities are the real content of the correspondence. The construction table is short; proving that every row of this ledger agrees is the purpose of the book.

### 1.2 Standing hypotheses and notation

Throughout, $F$ is a nonarchimedean local field with finite residue field. Write

$$
\mathcal O=\mathcal O_F,\qquad \mathfrak p=(\varpi),\qquad
k=\mathcal O/\mathfrak p,\qquad |k|=q,
$$

and normalize

$$
v_F(\varpi)=1,\qquad |x|=q^{-v_F(x)}.
$$

Put $G=\operatorname{GL}_2(F)$, $K=\operatorname{GL}_2(\mathcal O)$, and let $B$ be the upper triangular subgroup. All representations of $G$ are smooth complex representations. The algebraic statements remain valid over an algebraically closed characteristic-zero field containing $q^{1/2}$; complex coefficients are used whenever absolute values, Haar measures, or the variable $s$ occur.

Fix a separable closure of $F$. Let $W_F$ be the local Weil group, $I_F$ inertia, and $\Phi_F$ a lift of geometric Frobenius. Thus

$$
1\longrightarrow I_F\longrightarrow W_F
\xrightarrow{\nu_F}\mathbf Z\longrightarrow0,
\qquad \nu_F(\Phi_F)=1.
$$

The Weil norm is

$$
|w|=q^{-\nu_F(w)}.
$$

A parameter means a Frobenius-semisimple two-dimensional Weil--Deligne representation $D=(r,N)$ over $\mathbf C$. Its monodromy relation is

$$
r(w)Nr(w)^{-1}=|w|N.
\tag{1.1}
$$

For a finite extension $E/F$, the nontrivial automorphism of a quadratic $E/F$ is denoted $\sigma$, its different exponent by

$$
d(E/F)=v_E(\mathfrak D_{E/F}),
$$

and its residue degree by $f(E/F)$. The associated quadratic character of $F^\times$ is $\omega_{E/F}$.

### 1.3 The normalization ledger

The local theory is unusually sensitive to inverses and half-powers. We fix all choices before making an assignment.

First, reciprocity is normalized geometrically:

$$
\operatorname{rec}_F(\varpi)=\Phi_F.
\tag{1.2}
$$

Earlier arithmetic reciprocity is converted by inversion. Thus a multiplicative character $\chi:F^\times\to\mathbf C^\times$ is also viewed as the unique Weil character whose value on the image of $\operatorname{rec}_F(x)$ in $W_F^{\mathrm{ab}}$ is $\chi(x)$. In particular,

$$
\chi(\Phi_F)=\chi(\varpi).
\tag{1.3}
$$

Second, parabolic induction is normalized. For characters $\chi_1,\chi_2$ of $F^\times$,

$$
I(\chi_1,\chi_2)=i_B^G(\chi_1\boxtimes\chi_2)
$$

consists of smooth functions satisfying

$$
f\left(\begin{pmatrix}a&b\\0&d\end{pmatrix}g\right)
=|a/d|^{1/2}\chi_1(a)\chi_2(d)f(g).
\tag{1.4}
$$

Third, the special block is centered. On a basis $e_0,e_1$ put

$$
r(w)e_0=|w|^{1/2}e_0,\qquad
r(w)e_1=|w|^{-1/2}e_1,
$$

$$
Ne_1=e_0,\qquad Ne_0=0.
\tag{1.5}
$$

This parameter is denoted $\operatorname{Sp}_2$. For a character $\mu$, write $\operatorname{Sp}_2(\mu)=\mu\otimes\operatorname{Sp}_2$.

Finally, choose a nontrivial additive character $\psi:F\to\mathbf C^\times$. Its conductor exponent $n(\psi)$ is defined by

$$
\ker\psi=\mathfrak p^{-n(\psi)}.
\tag{1.6}
$$

Every additive integral uses the self-dual measure for the displayed character, and multiplicative measure gives $\mathcal O^\times$ volume one. The common convenient case is $n(\psi)=0$.

These conventions pass a first consistency test. Since $|\Phi_F|=q^{-1}$, the monodromy relation sends the $e_1$-eigenvalue to $q^{-1}$ times itself. The surviving kernel line $\mathbf Ce_0$ has eigenvalue $q^{-1/2}$ in the untwisted special block. It will therefore produce $L(s+1/2,1)$, exactly the Euler factor of the unitary Steinberg representation.

### 1.4 The selected range and its boundary

The book treats precisely the following two-dimensional parameters:

1. split parameters $\chi_1\oplus\chi_2$ with $N=0$;
2. special parameters $\operatorname{Sp}_2(\mu)$;
3. irreducible parameters $\operatorname{Ind}_{W_E}^{W_F}\theta$ for a tame separable quadratic extension $E/F$ and an admissible character $\theta$.

On the representation side these correspond to irreducible principal series and their one-dimensional boundary constituents, twists of Steinberg, and tame quadratic-induced supercuspidals. Ramified quadratic extensions in residue characteristic two and primitive wild supercuspidals lie outside the selected range. They require different type constructions; no assertion below classifies them.

The one-dimensional boundary constituents deserve inclusion even though they are not generic. At the reducibility wall, the split Weil representation

$$
\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2}
$$

can carry either zero monodromy or nonzero monodromy. The zero-monodromy object corresponds to $\mu\circ\det$; the nonzero-monodromy object corresponds to $\operatorname{St}\otimes\mu$. Omitting the character constituent would hide the sharpest demonstration that monodromy is essential.

## 2. The parameter side in dimension two

### 2.1 Three shapes

The parameter classification should be understood before any representation is attached. It explains why the final table has exactly three rows and which hypotheses make those rows exclusive.

Let $D=(r,N)$ be a two-dimensional Frobenius-semisimple parameter. If $N\ne0$, then $N$ has rank one. If $N=0$, the Weil representation $r$ is either reducible or irreducible. Thus linear algebra first divides the problem into

$$
\begin{array}{c|c|c}
N=0,\ r\text{ reducible}&N\ne0&N=0,\ r\text{ irreducible}.
\end{array}
$$

In the first case semisimplicity makes $r$ a sum of two characters. In the second, relation (1.1) forces a centered norm-spaced pair. In the third, the selected irreducibles are those induced from a quadratic subgroup. This is the parameter-side trichotomy.

### 2.2 Split parameters

Suppose $N=0$ and $r$ is reducible. Frobenius semisimplicity and finite inertial image make $r$ semisimple, so

$$
D=\chi_1\oplus\chi_2
\tag{2.1}
$$

for Weil characters $\chi_i$, equivalently smooth characters of $F^\times$. The unordered pair $\{\chi_1,\chi_2\}$ is determined by $D$.

The determinant and dual are immediate:

$$
\det D=\chi_1\chi_2,
\qquad
D^\vee=\chi_1^{-1}\oplus\chi_2^{-1}.
\tag{2.2}
$$

Twisting by $\mu$ multiplies both characters. The conductor is additive,

$$
a(D)=a(\chi_1)+a(\chi_2),
\tag{2.3}
$$

and every local factor is a product of the two rank-one factors. These elementary identities are the model that all later compatibilities must extend.

### 2.3 Special parameters

Now suppose $N\ne0$. Choose $e_1$ with $Ne_1=e_0\ne0$. The line $\ker N=\mathbf Ce_0$ is stable under $W_F$, so it carries a character $\xi$. Relation (1.1) shows that the quotient line carries $\xi|\cdot|^{-1}$. Writing

$$
\mu=\xi|\cdot|^{-1/2}
$$

centers the two characters and gives

$$
D\simeq\operatorname{Sp}_2(\mu).
\tag{2.4}
$$

The character $\mu$ is unique. Indeed the action on $\ker N$ recovers $\mu|\cdot|^{1/2}$, and $|\cdot|^{1/2}$ is fixed by the normalization. Thus every two-dimensional parameter with nonzero monodromy is a unique special block.

Its basic invariants are

$$
\det\operatorname{Sp}_2(\mu)=\mu^2,
\qquad
\operatorname{Sp}_2(\mu)^\vee\simeq\operatorname{Sp}_2(\mu^{-1}).
\tag{2.5}
$$

The conductor is

$$
a(\operatorname{Sp}_2(\mu))=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0.
\end{cases}
\tag{2.6}
$$

For unramified $\mu$, the underlying Weil representation has conductor zero and monodromy removes one invariant direction, contributing one. For ramified $\mu$, neither character line has inertia invariants; the monodromy correction is then zero and the two character conductors add to $2a(\mu)$.

### 2.4 Quadratic-induced parameters

Let $E/F$ be separable quadratic and let $\theta$ be a character of $E^\times$, viewed as a character of $W_E$. Put

$$
D(E,\theta)=\operatorname{Ind}_{W_E}^{W_F}\theta.
\tag{2.7}
$$

The restriction to $W_E$ is

$$
D(E,\theta)|_{W_E}\simeq\theta\oplus\theta^\sigma.
\tag{2.8}
$$

**Proposition 2.1.** The representation $D(E,\theta)$ is irreducible if and only if $\theta\ne\theta^\sigma$. Moreover

$$
D(E,\theta)\simeq D(E',\theta')
$$

if and only if the pairs are carried to one another by an $F$-isomorphism; for fixed $E$, this means $\theta'=\theta$ or $\theta^\sigma$.

**Proof strategy.** Restriction to the index-two subgroup exposes the two conjugate characters. A stable line would have to select a character fixed by the other coset. Conversely an invariant character extends after choosing a square root of its value on a coset representative.

**Proof.** Choose $s\in W_F\setminus W_E$. In the standard induced basis, $W_E$ acts diagonally through $\theta$ and $\theta^\sigma$, while $s$ exchanges the two lines. If the characters are distinct, every $W_E$-stable line is one of the two eigenspaces, and neither is stable under $s$; hence the induction is irreducible. If the characters agree, the $W_E$-action is scalar and the matrix of $s$ is diagonalizable over $\mathbf C$, so the representation splits into two characters.

For equivalence, restriction recovers the unordered pair of characters and its index-two subgroup. In the selected quadratic class, the projective kernel recovers the quadratic extension. An equivalence therefore identifies $E$ with $E'$ and then identifies $\theta'$ with one of the two conjugates of $\theta$. The converse follows from conjugating the induced model. $\square$

The conductor induction formula gives

$$
\boxed{
a_F(D(E,\theta))
=f(E/F)\bigl(a_E(\theta)+d(E/F)\bigr).}
\tag{2.9}
$$

The factor $f(E/F)$ converts $E$-normalized depth to $F$-normalized depth; the different term is the cost of permuting the two embeddings. For an unramified quadratic extension this becomes $2a_E(\theta)$. For a tamely ramified quadratic extension it becomes $a_E(\theta)+1$.

### 2.5 Why the three shapes are disjoint

A split parameter is reducible as a Weil representation and has $N=0$. A special parameter is reducible as a Weil representation but indecomposable as a pair because $N\ne0$. A regular quadratic induction is irreducible as a Weil representation and necessarily has $N=0$: an irreducible Weil representation cannot admit nonzero nilpotent monodromy, since $\ker N$ would be a nonzero proper stable subspace.

Thus none of the three shapes can be confused with another. This is more robust than comparing conductors or determinants. For example, all three shapes can have determinant one, and a split parameter and a dihedral parameter can have the same conductor. Reducibility and monodromy are the decisive structural invariants.

## 3. The representation side

### 3.1 Normalized principal series

The split torus supplies the representation-side analogue of a split parameter. For smooth characters $\chi_1,\chi_2$ of $F^\times$, normalized induction is the representation $I(\chi_1,\chi_2)$ of (1.4). Its central character is $\chi_1\chi_2$, and

$$
I(\chi_1,\chi_2)\otimes(\mu\circ\det)
\simeq I(\chi_1\mu,\chi_2\mu).
\tag{3.1}
$$

The standard intertwining operator exchanges the two inducing characters. Its regularized form is invertible except when

$$
\chi_1\chi_2^{-1}=|\cdot|^{\pm1}.
\tag{3.2}
$$

Consequently $I(\chi_1,\chi_2)$ is irreducible away from (3.2), and then depends only on the unordered pair $\{\chi_1,\chi_2\}$. Equality $\chi_1=\chi_2$ is not exceptional: the ratio is $1$, not $|\cdot|^{\pm1}$.

The proof of reducibility is worth recalling conceptually. The flag variety has an open and a closed cell. A proper subrepresentation can occur only when an open-cell distribution extends across the boundary. Translation invariance makes the possible boundary functional one-dimensional, while dilation forces its exponent to be one of two values. Those values are exactly $|\cdot|$ and $|\cdot|^{-1}$. A pole of an unnormalized intertwining integral at some other point is removable and does not imply reducibility.

### 3.2 The reducible wall

At the exceptional pair there are two nonsplit exact sequences:

$$
0\longrightarrow \mu\circ\det
\longrightarrow I(\mu|\cdot|^{-1/2},\mu|\cdot|^{1/2})
\longrightarrow \operatorname{St}\otimes\mu
\longrightarrow0,
\tag{3.3}
$$

and

$$
0\longrightarrow \operatorname{St}\otimes\mu
\longrightarrow I(\mu|\cdot|^{1/2},\mu|\cdot|^{-1/2})
\longrightarrow \mu\circ\det
\longrightarrow0.
\tag{3.4}
$$

The two induced representations have the same two constituents but opposite extension structures. The one-dimensional constituent is nongeneric because the upper unipotent subgroup acts trivially. The special constituent is generic and has a unique Whittaker model.

These sequences explain why the correspondence is attached to irreducible constituents, not to a reducible induced representation as a whole. They also determine which constituent receives zero monodromy and which receives nonzero monodromy.

### 3.3 Special representations

Define the Steinberg representation by

$$
\operatorname{St}=I(|\cdot|^{-1/2},|\cdot|^{1/2})/\mathbf1.
$$

Every special representation is $\operatorname{St}\otimes\mu$. Its central character is $\mu^2$, its contragredient is $\operatorname{St}\otimes\mu^{-1}$, and it has one Jacquet exponent rather than the two of an irreducible principal series.

The projective-line model

$$
\operatorname{St}\simeq C^\infty(\mathbf P^1(F))/\mathbf C
$$

gives the right intuition. Constants account for the one-dimensional constituent; differences of residue balls survive in the quotient and carry nonzero Fourier oscillation. This single surviving asymptotic direction becomes the single line $\ker N$ on the parameter side.

### 3.4 Tame dihedral supercuspidals

Let $E/F$ be tame quadratic and let $\vartheta$ be an admissible character of $E^\times$. At depth zero, admissibility means that $E/F$ is unramified and the residue character is regular. At positive depth it means, after removing norm twists, that the leading character genuinely generates the quadratic field. The tame type construction produces an irreducible supercuspidal representation

$$
\pi(E,\vartheta).
$$

It satisfies

$$
\omega_{\pi(E,\vartheta)}=\vartheta|_{F^\times},
\tag{3.5}
$$

$$
\pi(E,\vartheta)^\vee\simeq\pi(E,\vartheta^{-1}),
\tag{3.6}
$$

and

$$
\pi(E,\vartheta)\otimes(\chi\circ\det)
\simeq\pi(E,\vartheta(\chi\circ N_{E/F})).
\tag{3.7}
$$

Equivalent pairs give isomorphic representations, and for fixed $E$ the only ambiguity is $\vartheta\leftrightarrow\vartheta^\sigma$. Matrix coefficients are compact modulo the center, so the Jacquet module vanishes. The Kirillov model is therefore exactly $C_c^\infty(F^\times)$.

### 3.5 Classification in the selected range

The representation-side classification now mirrors Chapter 2.

**Theorem 3.1.** Every irreducible representation in the selected range is exactly one of the following:

1. an irreducible $I(\chi_1,\chi_2)$ with $\chi_1\chi_2^{-1}\ne|\cdot|^{\pm1}$;
2. a character $\mu\circ\det$;
3. a special representation $\operatorname{St}\otimes\mu$;
4. a tame dihedral supercuspidal $\pi(E,\vartheta)$.

Within the first class, the unordered inducing pair is unique. Within the last class, the admissible pair is unique up to $F$-isomorphism. The four classes are mutually disjoint.

**Proof.** The principal-series reducibility theorem gives the first three possibilities and uniqueness of their data. The tame type classification gives the fourth and its uniqueness. A supercuspidal has zero Jacquet module, while the first three classes do not, so the fourth cannot meet them. A character is finite-dimensional and nongeneric; the other nonsupercuspidal infinite-dimensional classes are generic. Finally an irreducible principal series has two Jacquet exponents and a special representation has one, so those classes are distinct. $\square$

The theorem is intentionally restricted. It classifies the representations produced by the split Borel, the special boundary, and the tame quadratic types. It does not assert that every supercuspidal representation is dihedral.

## 4. The correspondence table

### 4.1 Rank one as the anchor

The table is anchored by reciprocity in dimension one. A smooth character $\chi:F^\times\to\mathbf C^\times$ is identified with a character of $W_F$ by (1.2). This identification preserves products, inverses, conductors, and rank-one local factors. Under a finite extension $L/F$, restriction to $W_L$ corresponds to

$$
\chi\longmapsto\chi\circ N_{L/F}.
\tag{4.1}
$$

Every higher-dimensional formula below is built from direct sum, special monodromy, or induction applied to this rank-one anchor.

### 4.2 The three assignments

Define $\operatorname{rec}_2$ on the selected irreducible representations by

$$
\boxed{
\begin{aligned}
\operatorname{rec}_2(I(\chi_1,\chi_2))
&=\chi_1\oplus\chi_2,
&&\chi_1\chi_2^{-1}\ne|\cdot|^{\pm1},\\
\operatorname{rec}_2(\mu\circ\det)
&=\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2},\\
\operatorname{rec}_2(\operatorname{St}\otimes\mu)
&=\operatorname{Sp}_2(\mu),\\
\operatorname{rec}_2(\operatorname{AI}_{E/F}(\theta))
&=\operatorname{Ind}_{W_E}^{W_F}\theta.
\end{aligned}}
\tag{4.2}
$$

The notation $\operatorname{AI}_{E/F}(\theta)$ will be defined precisely in Chapter 7. It is a rectified tame dihedral representation, not the uncorrected direct type $\pi(E,\theta)$.

The two middle rows share the same underlying semisimple Weil representation. Their distinction is exactly

$$
N=0\quad\text{versus}\quad N\ne0.
$$

This is the only place in the selected range where the same pair of Weil characters supports two different irreducible representations of $G$.

### 4.3 Well-definedness

For the first row, the standard intertwiner gives

$$
I(\chi_1,\chi_2)\simeq I(\chi_2,\chi_1),
$$

and direct sum is insensitive to order. Uniqueness of the unordered Jacquet exponents shows that no other pair gives the same representation.

The character and special rows are well-defined because $\mu$ is recovered from the central character together with the class: within each row, equality of representations forces equality of $\mu$.

For the dihedral row, replacing $\theta$ by $\theta^\sigma$ does not change either induction. An $F$-isomorphism of quadratic pairs conjugates both constructions. The rectifier is itself invariant under the same equivalence. Thus every assignment depends only on the isomorphism class of the representation.

### 4.4 Bijectivity in the selected range

**Theorem 4.1 (selected local Langlands correspondence).** The assignment (4.2) is a bijection between the selected irreducible smooth representations of $\operatorname{GL}_2(F)$ and the selected two-dimensional Frobenius-semisimple parameters.

**Proof strategy.** Compare the structural trichotomies rather than numerical invariants. Reducible zero-monodromy, nonzero monodromy, and irreducible quadratic induction correspond to principal boundary, special, and dihedral classes.

**Proof.** A split parameter $\chi_1\oplus\chi_2$ falls into two cases. If the ratio is not $|\cdot|^{\pm1}$, it comes from the irreducible principal series. At the exceptional unordered pair, it has the form

$$
\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2}
$$

and comes from the character $\mu\circ\det$. A parameter with $N\ne0$ is uniquely $\operatorname{Sp}_2(\mu)$ by Section 2.3 and comes from $\operatorname{St}\otimes\mu$. An irreducible selected parameter is $\operatorname{Ind}_{W_E}^{W_F}\theta$ with $\theta\ne\theta^\sigma$ and comes from the rectified dihedral representation.

Injectivity follows from the same cases. The number and shape of Weil constituents distinguish split, special, and induced parameters. Within a split parameter the unordered pair is recovered; within a special parameter $\mu$ is recovered from $\ker N$; within the dihedral class Proposition 2.1 recovers the quadratic pair. The representation-side uniqueness statements match each recovery. $\square$

The theorem constructs and classifies the correspondence. The remaining chapters prove that it is the correct correspondence by checking every invariant in the opening ledger.

## 5. Unramified parameters and spherical representations

### 5.1 The spherical line

Unramified local data are the first test of every normalization because both sides reduce to two eigenvalues. On the representation side the maximal compact subgroup produces a one-dimensional fixed space; on the parameter side inertia invariants are the whole two-dimensional space.

Let $\chi_1,\chi_2$ be unramified and put

$$
\alpha=\chi_1(\varpi),\qquad \beta=\chi_2(\varpi).
$$

The compact picture shows that

$$
\dim I(\chi_1,\chi_2)^K=1.
\tag{5.1}
$$

Indeed a $K$-fixed section is determined by its value at the identity. Its covariance under $B\cap K$ is consistent because both characters are trivial on $\mathcal O^\times$. Conversely, if one inducing character is ramified, covariance under a diagonal unit forces every $K$-fixed section to vanish. Thus an irreducible principal series is spherical exactly when both inducing characters are unramified.

Normalize the spherical vector $f^\circ$ by $f^\circ(1)=1$. Let

$$
T=\mathbf1_{K\left(\begin{smallmatrix}\varpi&0\\0&1\end{smallmatrix}\right)K},
\qquad
S=\mathbf1_{\varpi I_2K},
$$

with $K$ of volume one. The $q+1$ neighbors of the standard lattice give

$$
Tf^\circ=q^{1/2}(\alpha+\beta)f^\circ,
\qquad
Sf^\circ=\alpha\beta f^\circ.
\tag{5.2}
$$

The $q^{1/2}$ is the visible effect of normalized induction. Removing it without simultaneously changing the Hecke operator or the inducing convention would invert the later Frobenius comparison.

### 5.2 Satake roots and Frobenius roots

The parameter

$$
D=\chi_1\oplus\chi_2
$$

is unramified and satisfies

$$
r(\Phi_F)\sim
\begin{pmatrix}\alpha&0\\0&\beta\end{pmatrix}.
\tag{5.3}
$$

This follows directly from geometric reciprocity: a uniformizer maps to $\Phi_F$, not to its inverse. Equations (5.2) recover the elementary symmetric functions of the Frobenius roots:

$$
\alpha+\beta=q^{-1/2}\lambda_T,
\qquad
\alpha\beta=\lambda_S.
\tag{5.4}
$$

Consequently the spherical Euler polynomial is

$$
P_\pi(X)=1-q^{-1/2}\lambda_TX+\lambda_SX^2
=(1-\alpha X)(1-\beta X).
\tag{5.5}
$$

Setting $X=q^{-s}$ gives the local Euler factor. This calculation constructs the unramified correspondence without referring to any ramified theory: the fixed line determines the unordered Frobenius conjugacy class, and the unordered class determines the spherical principal series.

### 5.3 Equal roots and the reducibility counterexample

Take $\alpha=\beta$. Then $\chi_1=\chi_2$ because unramified characters are determined by their value at $\varpi$. The principal series $I(\chi_1,\chi_1)$ is nevertheless irreducible: its character ratio is $1$, whereas reducibility requires $|\cdot|^{\pm1}$.

Its normalized spherical Whittaker values satisfy

$$
W^\circ\!\left(\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\right)
=q^{-m/2}(m+1)\alpha^m
\qquad(m\ge0),
\tag{5.6}
$$

and its Euler factor is

$$
(1-\alpha q^{-s})^{-2}.
$$

Thus a repeated Frobenius root produces a double Euler root, not a reducible representation. The reducibility wall is instead

$$
\alpha/\beta=q^{\mp1},
$$

depending on the ordering. This example separates three notions that are sometimes conflated: equality of roots, reducibility of normalized induction, and nontrivial monodromy.

### 5.4 Characterization by spherical data

**Theorem 5.1 (unramified characterization).** Sending a spherical irreducible representation in the selected range to the conjugacy class of

$$
\begin{pmatrix}\alpha&0\\0&\beta\end{pmatrix}
$$

determined by (5.4) agrees with $\operatorname{rec}_2$. Conversely the spherical Hecke eigenvalues determine the representation unless the roots lie on the reducibility wall, in which case they determine the unique spherical irreducible constituent.

**Proof.** Away from the wall, the roots determine the two unramified characters, hence the irreducible principal series. At the wall, one of the two constituents is a character $\mu\circ\det$ and the other is a Steinberg twist. Only the character constituent is $K$-fixed; Steinberg has an Iwahori-fixed line but no $K$-fixed vector. Hence the spherical constituent is uniquely determined. Formula (4.2) assigns it the zero-monodromy split parameter with exactly those roots. $\square$

The last clause is essential. The semisimple Frobenius conjugacy class alone cannot see whether the special constituent is also present at the wall; the level of the fixed vector and the monodromy operator resolve the ambiguity.

## 6. The special correspondence

### 6.1 Monodromy replaces a missing Euler root

At the reducibility wall the two character lines remain visible in the semisimplified Weil action, but the generic constituent has only one Jacquet exponent and one Euler root. Monodromy explains the loss: the Euler factor is computed on $(\ker N)^{I_F}$ rather than on all inertia invariants.

For $D=\operatorname{Sp}_2(\mu)$, the underlying Weil representation is

$$
\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2},
$$

and $\ker N$ is the first line. If $\mu$ is unramified with $a=\mu(\varpi)$, Frobenius acts on that line by $aq^{-1/2}$. Hence

$$
L(s,D)=(1-aq^{-s-1/2})^{-1}.
\tag{6.1}
$$

The second root has not been discarded by convention. It lies outside $\ker N$ and reappears in the monodromy correction to the epsilon factor.

### 6.2 Construction at the reducibility wall

Consider the exact sequence (3.4). Its principal series has a Whittaker functional obtained from the open-cell Fourier integral. That functional vanishes on the quotient $\mu\circ\det$, because the upper unipotent subgroup acts trivially there. It therefore restricts nontrivially to the subrepresentation $\operatorname{St}\otimes\mu$.

The two Tate factors of the ambient principal series are

$$
\gamma(s,\mu|\cdot|^{1/2},\psi)
\gamma(s,\mu|\cdot|^{-1/2},\psi).
\tag{6.2}
$$

On passage to the generic constituent, one opposite Euler denominator cancels. What remains is the single factor (6.1) together with a monomial epsilon factor. This limiting calculation is the analytic shadow of turning on $N$.

The construction can therefore be read in either direction. Starting from the group, isolate the generic constituent at the wall and record the lost Jacquet exponent as monodromy. Starting from the parameter, take the unique nonzero map between the two norm-spaced character lines. Both routes give a unique object.

### 6.3 The special matching theorem

**Theorem 6.1.** For every smooth character $\mu$ of $F^\times$,

$$
\operatorname{rec}_2(\operatorname{St}\otimes\mu)
=\operatorname{Sp}_2(\mu)
$$

is the unique matching with all of the following properties:

$$
\omega_{\operatorname{St}\otimes\mu}=\det\operatorname{Sp}_2(\mu)=\mu^2,
\tag{6.3}
$$

$$
a(\operatorname{St}\otimes\mu)
=a(\operatorname{Sp}_2(\mu))
=\begin{cases}1,&a(\mu)=0,\\2a(\mu),&a(\mu)>0,
\end{cases}
\tag{6.4}
$$

and the Euler and epsilon factors agree for every additive character.

**Proof strategy.** The determinant follows from the centered exponents. The conductor and factors are computed first for unramified $\mu$, then for ramified $\mu$ by the two rank-one factors at the boundary.

**Proof.** Equation (6.3) follows because the norm powers in $\operatorname{Sp}_2$ multiply to one. If $\mu$ is unramified, Steinberg first has fixed vectors at level one, while monodromy contributes exactly one to the parameter conductor. Formula (6.1) agrees with the one Kirillov tail of Steinberg. The monodromy determinant on the quotient of inertia invariants is

$$
\det(-q^{-s}r(\Phi_F))=-\mu(\varpi)q^{1/2-s},
$$

which is the Steinberg epsilon factor.

If $\mu$ is ramified, both underlying character lines have conductor $a(\mu)$ and no inertia invariants. Thus the conductor is $2a(\mu)$, the Euler factor is one, and the monodromy determinant is trivial because $V^{I_F}=0$. On both sides the epsilon factor is the product of the rank-one factors for $\mu|\cdot|^{1/2}$ and $\mu|\cdot|^{-1/2}$. The construction in Section 6.2 proves the representation-side product, while the definition of the parameter factor gives the same product. Uniqueness follows from the unique character $\mu$ and the unique nonzero rank-one nilpotent map. $\square$

### 6.4 Why semisimplification is insufficient

The character $\mu\circ\det$ and $\operatorname{St}\otimes\mu$ share the semisimple Weil representation

$$
\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2}.
$$

Yet their behavior differs sharply. The first is nongeneric; the second is generic. For unramified $\mu$, the first is spherical and the second is not. Their Euler factors have two roots and one root respectively, and their conductors are $0$ and $1$ when $\mu$ is unramified. The nilpotent operator records every one of these differences.

This is the decisive counterexample to any attempted correspondence using only semisimple Weil representations. Frobenius semisimplification is legitimate because it removes a unipotent part of Frobenius while retaining $N$; erasing $N$ is not.

## 7. Quadratic induction and dihedral supercuspidals

### 7.1 Regular characters and irreducible induction

Quadratic induction is the first genuinely cuspidal case. Let $E/F$ be tame separable quadratic. A character $\theta$ of $E^\times$ is regular when

$$
\theta\ne\theta^\sigma.
\tag{7.1}
$$

For the tame type construction one imposes the slightly sharper admissibility condition: if $\theta/\theta^\sigma$ is trivial on $U_E^1$, then $E/F$ must be unramified. This removes the ramified valuation-only degeneracy that would create excess intertwining.

Regularity has identical effects on the two sides. Proposition 2.1 says that it makes $\operatorname{Ind}_{W_E}^{W_F}\theta$ irreducible. In the type construction it makes the quadratic torus the exact intertwining group and therefore makes compact induction irreducible and supercuspidal.

If regularity fails, $\theta$ factors through the norm after a character extension, and the induced parameter splits. The corresponding representation belongs to the principal part of the table rather than the dihedral supercuspidal class. Thus regularity is not a technical convenience; it is precisely the line separating elliptic induction from split induction.

### 7.2 The determinant discrepancy

The uncorrected tame type $\pi(E,\vartheta)$ has central character $\vartheta|_{F^\times}$. The determinant of the induced Weil representation has an extra quadratic factor:

$$
\boxed{
\det\operatorname{Ind}_{W_E}^{W_F}\theta
=\theta|_{F^\times}\,\omega_{E/F}.}
\tag{7.2}
$$

**Proof strategy.** Separate induction of the character from the sign of the permutation of the two cosets.

**Proof.** In an induced basis, an element of $W_E$ acts diagonally by $\theta$ and $\theta^\sigma$. An element outside $W_E$ exchanges the basis vectors, contributing the sign character of the quotient $W_F/W_E$. More invariantly,

$$
\det\operatorname{Ind}\theta
=\det\operatorname{Ind}1\cdot(\theta\circ\operatorname{Ver}_{W_F/W_E}).
$$

The first factor is the quadratic character $\omega_{E/F}$. Under reciprocity, transfer corresponds to the inclusion $F^\times\hookrightarrow E^\times$, so the second factor is $\theta|_{F^\times}$. This proves (7.2). $\square$

The discrepancy cannot be ignored: central character is one of the defining compatibilities. It is repaired by a canonical tame character.

### 7.3 The tame rectifier

Choose the tame rectifier $\Delta_{E/F,\theta}:E^\times\to\mathbf C^\times$ characterized by

$$
\Delta_{E/F,\theta}|_{F^\times}=\omega_{E/F}
\tag{7.3}
$$

and by the quadratic Gauss-sum normalization of the induction formula for epsilon factors. The notation allows the ramified rectifier to depend on the admissible character; this dependence is needed to keep duality exact. Concretely, if $E/F$ is unramified, the rectifier is independent of $\theta$, is unramified, and satisfies

$$
\Delta_{E/F,\theta}(\varpi)=-1.
$$

If $E/F$ is tamely ramified, it is tamely ramified and its remaining value on a uniformizer is fixed by the normalized quadratic Gauss sum attached to $\theta$. Uniqueness of that normalization and the rank-one duality and twist formulas give

$$
\Delta_{E/F,\theta^\sigma}=\Delta_{E/F,\theta}^\sigma,
\qquad
\Delta_{E/F,\theta(\chi\circ N_{E/F})}=\Delta_{E/F,\theta},
\qquad
\Delta_{E/F,\theta^{-1}}=\Delta_{E/F,\theta}^{-1}.
\tag{7.4}
$$

For the second identity, a norm twist multiplies both sides of the quadratic induction equation by the same rank-one twist factor, so the correcting Gauss quotient is unchanged. For the third, apply Fourier duality to that equation: inversion replaces the correcting character by its inverse. The first follows by changing the chosen embedding of $E$. Thus the rectifier is functorial under pair equivalence, norm twists, and inversion.

Define

$$
\boxed{
\operatorname{AI}_{E/F}(\theta)
=\pi(E,\theta\Delta_{E/F,\theta}).}
\tag{7.5}
$$

Because $\Delta_{E/F,\theta}$ has at most tame conductor, it does not alter the positive-depth conductor of an admissible character. In depth zero it changes the required sign without destroying residue regularity. Equation (7.3) and the fact that $\omega_{E/F}^2=1$ give

$$
\omega_{\operatorname{AI}_{E/F}(\theta)}
=\theta|_{F^\times}\omega_{E/F},
\tag{7.6}
$$

matching (7.2).

### 7.4 The dihedral matching theorem

**Theorem 7.1.** Let $E/F$ be tame separable quadratic and let $\theta$ be admissible. Then

$$
\operatorname{rec}_2(\operatorname{AI}_{E/F}(\theta))
=\operatorname{Ind}_{W_E}^{W_F}\theta
\tag{7.7}
$$

is well defined and has the following properties:

$$
\omega_{\operatorname{AI}_{E/F}(\theta)}
=\det\operatorname{Ind}_{W_E}^{W_F}\theta,
\tag{7.8}
$$

$$
a_F(\operatorname{AI}_{E/F}(\theta))
=f(E/F)\bigl(a_E(\theta)+d(E/F)\bigr),
\tag{7.9}
$$

and its local factors equal those of the induced parameter.

**Proof strategy.** Central characters are handled by the rectifier. Conductors reduce to trace duality. Local factors reduce the two-dimensional Fourier transform over $F$ to the one-dimensional transform over $E$.

**Proof.** Equation (7.8) is (7.2) and (7.6). The type conductor formula applied to $\theta\Delta_{E/F,\theta}$ gives

$$
v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta\Delta_{E/F,\theta}).
$$

For the unramified extension, the discriminant exponent is zero and the rectifier is unramified. For the tamely ramified extension, the discriminant exponent is one and admissibility forces $a_E(\theta)\ge2$, so a tame rectifier cannot change its conductor. Since $v_F(\mathfrak d_{E/F})=f(E/F)d(E/F)$, the result is (7.9).

For local factors, unfold the toric Whittaker function. The two-dimensional $F$-space underlying $E$ carries phase $\psi\circ\operatorname{Tr}_{E/F}$ and multiplicative character $\theta$. Fourier transformation over this space gives the rank-one local equation over $E$. The discrepancy between the two self-dual measures is the quadratic lambda factor, and the Gauss-sum normalization of $\Delta_{E/F,\theta}$ supplies exactly that factor. This proves equality of epsilon factors. The Euler factors are both one because the induced Weil representation is irreducible of dimension two and hence has no inertia-fixed vector; equivalently the supercuspidal Kirillov model is compactly supported. Gamma factors then agree by definition. $\square$

### 7.5 Depth-zero and positive-depth examples

Suppose $E/F$ is unramified quadratic and $\theta$ is trivial on $U_E^1$ with regular residue character. Then

$$
a_E(\theta)=1,
\qquad
a_F(\operatorname{AI}_{E/F}(\theta))=2.
$$

The parameter has tame inertia $\theta|_{I_F}\oplus\theta^\sigma|_{I_F}$ and no invariant line. The representation has no $K$-fixed vector but has a unique first newvector at level two. This example warns that depth zero does not mean conductor zero.

If $E/F$ is unramified and $a_E(\theta)=m\ge2$, then the conductor is $2m$. If $E/F$ is tamely ramified and $a_E(\theta)=m\ge2$, the conductor is $m+1$. Thus unramified quadratic induction naturally gives even conductor, while ramified tame induction begins at conductor three.

These parity patterns are useful but not absolute classifiers. A determinant twist can cancel the leading character and lower the conductor. The exact formula must always be applied to $\theta(\chi\circ N_{E/F})$, not inferred from the old conductor and $a(\chi)$ alone.

## 8. Central characters, twists, and contragredients

### 8.1 Central characters and determinants

The center is the quickest global consistency check, but the dihedral sign shows that it is not automatic. The correspondence satisfies

$$
\boxed{\omega_\pi=\det\operatorname{rec}_2(\pi)}
\tag{8.1}
$$

throughout the selected range.

For a principal series, both sides are $\chi_1\chi_2$. For $\mu\circ\det$, the central character is $\mu^2$, and the two norm powers in its split parameter cancel. For $\operatorname{St}\otimes\mu$, centered monodromy again gives determinant $\mu^2$. For quadratic induction, (8.1) is exactly the rectifier calculation (7.2), (7.3), and (7.6).

The proof also shows why a direct type cannot be matched to $\operatorname{Ind}\theta$ without correction. It would fail (8.1) by $\omega_{E/F}$ even if its conductor and many character values looked correct.

### 8.2 Twists

Let $\chi$ be any smooth character of $F^\times$. Then

$$
\boxed{
\operatorname{rec}_2(\pi\otimes(\chi\circ\det))
=\operatorname{rec}_2(\pi)\otimes\chi.}
\tag{8.2}
$$

**Proof.** For a principal series, (3.1) multiplies both inducing characters by $\chi$. For a character constituent,

$$
(\mu\circ\det)\otimes(\chi\circ\det)
=(\mu\chi)\circ\det.
$$

For a special representation, twisting multiplies the coefficient character of the special block:

$$
(\operatorname{St}\otimes\mu)\otimes\chi
=\operatorname{St}\otimes\mu\chi.
$$

For a dihedral representation, determinant on the embedded torus is the norm, so

$$
\operatorname{AI}_{E/F}(\theta)\otimes\chi
\simeq\operatorname{AI}_{E/F}(\theta(\chi\circ N_{E/F})).
$$

Here the norm-twist identity for the rectifier in (7.4) makes the two direct tame types identical after twisting.

On the parameter side, the tensor identity

$$
(\operatorname{Ind}_{W_E}^{W_F}\theta)\otimes\chi
\simeq\operatorname{Ind}_{W_E}^{W_F}
(\theta\,\chi|_{W_E})
$$

and rank-one functoriality identify $\chi|_{W_E}$ with $\chi\circ N_{E/F}$. $\square$

Taking determinants in (8.2) multiplies both central characters by $\chi^2$, as it must in dimension two.

### 8.3 Contragredients

The correspondence also satisfies

$$
\boxed{
\operatorname{rec}_2(\pi^\vee)
=\operatorname{rec}_2(\pi)^\vee.}
\tag{8.3}
$$

For irreducible principal series,

$$
I(\chi_1,\chi_2)^\vee
\simeq I(\chi_1^{-1},\chi_2^{-1}),
$$

up to the harmless Weyl exchange. The character and special formulas are

$$
(\mu\circ\det)^\vee=\mu^{-1}\circ\det,
$$

$$
(\operatorname{St}\otimes\mu)^\vee
=\operatorname{St}\otimes\mu^{-1}.
$$

For quadratic induction,

$$
\operatorname{AI}_{E/F}(\theta)^\vee
\simeq\operatorname{AI}_{E/F}(\theta^{-1}),
$$

because duality inverts the direct inducing character and (7.4) identifies the inverse rectifier with the rectifier attached to $\theta^{-1}$. On the parameter side,

$$
(\operatorname{Ind}_{W_E}^{W_F}\theta)^\vee
\simeq\operatorname{Ind}_{W_E}^{W_F}\theta^{-1}.
$$

The minus transpose in the dual monodromy operator does not alter the isomorphism class of a two-dimensional special block. This completes the proof of (8.3).

### 8.4 Self-duality tests

The preceding formulas give practical recognition criteria. An irreducible principal series is self-dual exactly when

$$
\{\chi_1,\chi_2\}=\{\chi_1^{-1},\chi_2^{-1}\}.
$$

A special representation $\operatorname{St}\otimes\mu$ is self-dual exactly when $\mu^2=1$. A dihedral representation is self-dual exactly when the pairs $(E,\theta)$ and $(E,\theta^{-1})$ are equivalent, that is,

$$
\theta^{-1}=\theta
\quad\text{or}\quad
\theta^{-1}=\theta^\sigma.
$$

The second alternative is the familiar conjugate-inverse condition; the first is generally excluded by tame admissibility but is retained in the exact equivalence criterion. Essential self-duality is obtained by allowing the same identities after a norm twist. These tests agree word for word on both sides of the correspondence because of (8.2) and (8.3).

## 9. Conductors

### 9.1 Two definitions that must agree

Conductors connect finite-level vectors to ramification depth. On the parameter side, for $D=(r,N)$ on $V$, define

$$
a(D)=a(r)+\dim V^{I_F}-\dim(\ker N)^{I_F}.
\tag{9.1}
$$

The first term is the Artin conductor of the finite-inertia Weil action; the second is the monodromy defect. On the representation side, if $\pi$ is irreducible and generic, put

$$
a(\pi)=\min\{n\ge0:\pi^{K_1(\mathfrak p^n)}\ne0\},
\tag{9.2}
$$

where

$$
K_1(\mathfrak p^n)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\operatorname{GL}_2(\mathcal O):
c\in\mathfrak p^n,\ d\equiv1\pmod{\mathfrak p^n}
\right\}.
\tag{9.3}
$$

Equivalently, $a(\pi)$ is the exponent of $q^{-(s-1/2)}$ in its epsilon factor after the additive-character shift is removed. This latter definition also applies to the nongeneric character constituents. For a ramified $\mu\circ\det$, the group in (9.3) contains $\operatorname{diag}(u,1)$ for every unit $u$, so there is no fixed vector at any level unless $\mu$ is unramified. This is why the fixed-vector definition is stated only for generic representations, while the epsilon-conductor definition covers every row of (4.2).

The compatibility to prove is

$$
\boxed{a(\pi)=a(\operatorname{rec}_2(\pi))}
\tag{9.4}
$$

with this distinction understood.

### 9.2 Principal and special formulas

**Proposition 9.1.** If $I(\chi_1,\chi_2)$ is irreducible, then

$$
a(I(\chi_1,\chi_2))=a(\chi_1)+a(\chi_2).
\tag{9.5}
$$

For the two boundary constituents,

$$
a(\mu\circ\det)=2a(\mu),
\tag{9.6}
$$

and

$$
a(\operatorname{St}\otimes\mu)=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0.
\end{cases}
\tag{9.7}
$$

**Proof strategy.** Factor the principal functional equation into two rank-one equations. At the special boundary, determine whether inertia invariants remain for the monodromy correction.

**Proof.** The epsilon factor of a principal series is the product of the factors of $\chi_1$ and $\chi_2$. Its monomial degree is therefore their conductor sum, proving (9.5). The character constituent is assigned the same split pair as the reducible principal series, and the two unramified norm powers do not change conductor, giving (9.6).

For Steinberg, the underlying Weil action has two copies of the inertia character of $\mu$. If $\mu$ is unramified, $a(r)=0$ and monodromy lowers the invariant dimension from two to one, giving one. If $\mu$ is ramified, $V^{I_F}=0$ and $a(r)=2a(\mu)$, so there is no monodromy correction. The representation-side boundary functional equation gives the same exponents. $\square$

The formula $\max\{1,2a(\mu)\}$ happens to encode (9.7), but the case distinction is more informative: conductor one comes from monodromy, while every ramified case comes entirely from the character on inertia.

### 9.3 The quadratic conductor formula

**Proposition 9.2.** For a tame admissible pair $(E,\theta)$,

$$
\boxed{
a_F(\operatorname{AI}_{E/F}(\theta))
=a_F(\operatorname{Ind}_{W_E}^{W_F}\theta)
=f(E/F)\bigl(a_E(\theta)+d(E/F)\bigr).}
\tag{9.8}
$$

**Proof.** The parameter formula is the conductor induction identity

$$
a_F(\operatorname{Ind}U)
=f(E/F)\bigl(a_E(U)+d(E/F)\dim U\bigr)
$$

with $U=\theta$. Its proof compares the Artin character over $F$ with its restriction over $E$: away from the identity the displacement functions differ by the residue-degree normalization, while at the identity transitivity of the different contributes the regular character with coefficient $f(E/F)d(E/F)$. Pairing with $\theta$ gives (9.8).

On the representation side, Mackey decomposition reduces $K_1$-fixed vectors to fixed vectors in the tame type. Before the integer in (9.8), the intersection contains a unit on which the leading simple character is nontrivial. At that integer, the congruence lattice first enters the trace annihilator; its fixed space in the finite Heisenberg representation is one-dimensional. The trace-dual shift contributes the discriminant exponent $f d$, and each character layer contributes $f a_E(\theta)$. The rectifier does not alter the relevant conductor, as shown in Section 7.4. Hence the first fixed level is the same integer. $\square$

The proof explains every term. The different measures the failure of $\mathcal O_E$ to be self-dual under trace. The character conductor counts the nontrivial unit layers. The residue degree converts their size to the base-field scale.

### 9.4 Twisting and conductor cancellation

Compatibility with twists gives exact formulas rather than a maximum rule. For principal series,

$$
a(I(\chi_1,\chi_2)\otimes\chi)
=a(\chi_1\chi)+a(\chi_2\chi).
\tag{9.9}
$$

For special representations, use (9.7) with $\mu\chi$. For a dihedral representation,

$$
a_F(\operatorname{AI}_{E/F}(\theta)\otimes\chi)
=f(E/F)\left(
a_E(\theta(\chi\circ N_{E/F}))+d(E/F)
\right).
\tag{9.10}
$$

These formulas retain cancellation on the last nontrivial unit layer. If $\chi_1=\chi^{-1}\eta$ with $a(\eta)<a(\chi)$, twisting by $\chi$ lowers the first principal contribution rather than replacing it by a maximum. Likewise a norm twist can make the leading term of $\theta$ cancel. Conductors alone do not determine conductors after twisting; the actual characters at the deepest common break are required.

## 10. Newvectors

### 10.1 The first fixed line

A conductor becomes representation-theoretically useful only when the first fixed space is controlled. In the generic selected cases, that space is always a line.

**Theorem 10.1 (newvector theorem).** Let $\pi$ be an irreducible generic principal, special, or tame dihedral representation, and put $n=a(\pi)$. Then

$$
\dim\pi^{K_1(\mathfrak p^r)}=
\begin{cases}
0,&r<n,\\
r-n+1,&r\ge n.
\end{cases}
\tag{10.1}
$$

In particular, $\pi^{K_1(\mathfrak p^n)}$ is one-dimensional.

The theorem is not asserted for $\mu\circ\det$, which is nongeneric and exhibits the obstruction noted after (9.3). For every infinite-dimensional selected representation, however, the parameter conductor is exactly the first newvector level by (9.4).

### 10.2 Proof through the Kirillov model

**Proof strategy for Theorem 10.1.** In the Kirillov model, upper-unipotent invariance controls the support of a function and lower-unipotent invariance controls the support of its Weyl transform. The functional equation reverses valuations and shifts them by the conductor. The overlap is an interval of $r-n+1$ shells.

**Proof.** Fix a conductor-zero additive character and realize $\pi$ in its Kirillov model. Upper unipotents act by

$$
(n(b)\phi)(y)=\psi(by)\phi(y).
$$

The upper-unipotent part of $K_1(\mathfrak p^r)$ therefore forces $\phi$ to be constant at the required unit precision and supported on one side of a valuation bound. The lower-unipotent part is conjugate to the upper part by the Weyl element. The local functional equation says that the Weyl transform reverses the valuation coordinate and shifts the bound by $n$, the exponent of the epsilon monomial.

After a harmless common translation of the valuation coordinate, the simultaneous conditions leave exactly the shells

$$
0\le j\le r-n.
\tag{10.2}
$$

For each integer $j$ in this interval, the characteristic function of $\varpi^j\mathcal O^\times$, modified by the required unit character when the central character is ramified, satisfies both invariance conditions. Their supports are disjoint, so they are independent. Finite Fourier inversion on the unit quotients shows that every invariant function is a linear combination of these shell functions. If $r<n$, the interval is empty; if $r\ge n$, it has $r-n+1$ integers. This proves (10.1). $\square$

The argument works uniformly because the class of the representation affects only the asymptotic tails and the Weyl shift. Principal series have two tails, special representations one, and supercuspidals none; the functional equation packages all three into the same conductor displacement.

### 10.3 Essential Whittaker functions

Choose a nonzero newvector and normalize its Whittaker function by

$$
W^{\mathrm{new}}(1)=1.
$$

For every generic selected $\pi$, the newvector may be chosen so that

$$
Z(s,W^{\mathrm{new}},1)=L(s,\pi),
\tag{10.3}
$$

where

$$
Z(s,W,1)=\int_{F^\times}
W\!\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
|y|^{s-1/2}\,d^\times y.
$$

For an unramified principal series this is the normalized spherical Whittaker vector. Its diagonal values satisfy the two-root recurrence and sum to the product of two Euler factors. For an unramified Steinberg twist, the single tail gives $L(s+1/2,\mu)$. For a dihedral supercuspidal, the first shell is

$$
W^{\mathrm{new}}\!\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
=\mathbf1_{\mathcal O^\times}(y),
\tag{10.4}
$$

so the integral is $1$, its Euler factor.

When a ramified character is inserted into the zeta integral, the same preferred vector can give zero by unit orthogonality. This does not change the zeta ideal or the local factor. A matching unit-character shell in the Kirillov core supplies the correct test vector. “The preferred integral equals the local factor” always includes a compatibility condition on the ramification of the test data.

### 10.4 Oldforms and the parameter conductor

If $v_0$ spans the newvector line, then for $r\ge n$ the vectors

$$
v_j=\pi\!\left(\begin{pmatrix}\varpi^{-j}&0\\0&1\end{pmatrix}\right)v_0,
\qquad 0\le j\le r-n,
\tag{10.5}
$$

form a basis of the level-$r$ fixed space, up to the common shift dictated by the action convention. In the Kirillov model they occupy the shells in (10.2). Passing from $r$ to $r+1$ retains all old vectors and adds one endpoint shell.

Together with (9.4), this gives the promised newvector compatibility:

$$
\boxed{
\min\{r:\pi^{K_1(\mathfrak p^r)}\ne0\}
=a(\operatorname{rec}_2(\pi)),
\qquad
\dim\pi^{K_1(\mathfrak p^{a(\operatorname{rec}_2(\pi))})}=1.}
\tag{10.6}
$$

The parameter does not itself contain a preferred vector. It contains the integer that cuts the Kirillov uncertainty interval down to one shell; the group action then supplies the line.

## 11. Euler factors

### 11.1 Definitions on both sides

Euler factors isolate the unramified directions that survive monodromy. For $D=(r,N)$ on $V$, define

$$
L(s,D)=
\det\left(1-q^{-s}r(\Phi_F)\mid(\ker N)^{I_F}\right)^{-1}.
\tag{11.1}
$$

This is independent of the lift of geometric Frobenius because inertia acts trivially on the displayed space.

For a generic representation, its Whittaker zeta integrals generate a principal fractional ideal in $\mathbf C[q^s,q^{-s}]$. The generator with constant term one is $L(s,\pi)$. For the nongeneric character constituent, define the factor through the split row of (4.2); equivalently it is the factor of its standard two-dimensional local datum. The compatibility statement is

$$
\boxed{L(s,\pi)=L(s,\operatorname{rec}_2(\pi)).}
\tag{11.2}
$$

### 11.2 Principal factorization

For a principal series,

$$
L(s,I(\chi_1,\chi_2))
=L(s,\chi_1)L(s,\chi_2).
\tag{11.3}
$$

**Proof.** Modulo compactly supported Kirillov functions, an irreducible principal series has tails

$$
|y|^{1/2}\chi_1(y),
\qquad
|y|^{1/2}\chi_2(y).
$$

Multiplication by $|y|^{s-1/2}$ turns these into the two rank-one Mellin series. A tail contributes a geometric denominator exactly when its character is unramified; otherwise unit orthogonality makes it a Laurent polynomial. The compactly supported core supplies enough numerators to make the generator precisely the product (11.3). On the parameter side, (11.1) is the determinant on the direct sum of the two inertia-invariant character lines, giving the same result. $\square$

The same product defines the factor of $\mu\circ\det$:

$$
L(s,\mu\circ\det)
=L(s,\mu|\cdot|^{1/2})L(s,\mu|\cdot|^{-1/2}).
\tag{11.4}
$$

### 11.3 The special factor

For a special representation,

$$
\boxed{
L(s,\operatorname{St}\otimes\mu)
=L(s+1/2,\mu).}
\tag{11.5}
$$

On the representation side the single Kirillov tail is $|y|\mu(y)$, which gives the shifted rank-one Mellin series. On the parameter side $\ker N$ is the $\mu|\cdot|^{1/2}$ line, producing the same shift. If $\mu$ is ramified, both sides are one.

This factor distinguishes the special representation from the character constituent even though their semisimple Weil actions agree. Equation (11.4) retains both roots; equation (11.5) retains only the root on $\ker N$.

### 11.4 The dihedral factor

For an admissible quadratic character,

$$
L_F(s,\operatorname{Ind}_{W_E}^{W_F}\theta)
=L_E(s,\theta).
\tag{11.6}
$$

The equality is the finite-index induction identity: Frobenius orbits on the two cosets turn the determinant over $F$ into the determinant of relative Frobenius over $E$, with $q_E=q^{f(E/F)}$.

In the admissible quadratic case both sides equal one. Indeed $\operatorname{Ind}\theta$ is irreducible of dimension two. A nonzero inertia-fixed vector would make the whole irreducible representation unramified, but an irreducible representation of the cyclic Frobenius quotient is one-dimensional. Hence there are no inertia invariants. Equivalently, admissibility forces $\theta$ to be ramified, and $L_E(s,\theta)=1$.

On the representation side the Kirillov model of a supercuspidal is $C_c^\infty(F^\times)$, so every zeta integral is a Laurent polynomial and the zeta ideal contains $1$. This proves (11.2) in the dihedral case.

## 12. Epsilon and gamma factors

### 12.1 Additive characters and measures

Euler factors see only surviving invariant directions. Epsilon factors restore ramification depth, Gauss-sum phase, determinant data, and monodromy. Their definition therefore depends on the nontrivial additive character $\psi$ and its self-dual Haar measure.

For a parameter $D=(r,N)$, first form the epsilon factor $\epsilon(s,r,\psi)$ of the finite-inertia Weil representation. Then set

$$
\epsilon(s,D,\psi)
=\epsilon(s,r,\psi)
\det\left(-q^{-s}r(\Phi_F)\mid
V^{I_F}/(\ker N)^{I_F}\right).
\tag{12.1}
$$

It has the form

$$
\epsilon(s,D,\psi)
=W(D,\psi)
q^{-[a(D)+n(\psi)\dim D](s-1/2)}.
\tag{12.2}
$$

Define

$$
\gamma(s,D,\psi)
=\epsilon(s,D,\psi)
\frac{L(1-s,D^\vee)}{L(s,D)}.
\tag{12.3}
$$

On the representation side, the Whittaker functional equation defines the same three factors for generic representations. For the character constituent, use the product attached to its split parameter. We will prove

$$
\boxed{
\epsilon(s,\pi,\psi)=\epsilon(s,\operatorname{rec}_2(\pi),\psi),
\qquad
\gamma(s,\pi,\psi)=\gamma(s,\operatorname{rec}_2(\pi),\psi).}
\tag{12.4}
$$

### 12.2 Principal factorization

**Theorem 12.1.** For a generic principal series,

$$
\gamma(s,I(\chi_1,\chi_2),\psi)
=\gamma(s,\chi_1,\psi)\gamma(s,\chi_2,\psi),
\tag{12.5}
$$

and the analogous product holds for epsilon factors.

**Proof strategy.** Unfold the Jacquet integral on the open Bruhat cell and apply the rank-one functional equation twice.

**Proof.** At a common compact-open level, a section on the two relevant affine coordinates is a finite sum of products

$$
\sum_j\Phi_{1,j}(x_1)\Phi_{2,j}(x_2).
$$

Unfolding its Whittaker zeta integral gives a finite sum of products of Tate integrals for $\chi_1$ and $\chi_2$. The transpose-inverse Weyl transform replaces each $\Phi_{i,j}$ by its Fourier transform and each character by its inverse on the $1-s$ side. The rank-one functional equation contributes the two gamma factors in (12.5). Such sections span, and rational continuation extends the equality to every section. Combining (12.5) with (11.3) gives the epsilon product. $\square$

This proves (12.4) for irreducible principal series and, by definition, for the one-dimensional boundary constituent. It also recovers (9.5) from the monomial degree.

### 12.3 The monodromy correction for Steinberg

Specialization of (12.5) at the reducibility wall gives

$$
\gamma(s,\operatorname{St}\otimes\mu,\psi)
=\gamma(s,\mu|\cdot|^{1/2},\psi)
\gamma(s,\mu|\cdot|^{-1/2},\psi).
\tag{12.6}
$$

The Whittaker functional kills the nongeneric constituent, so the specialization belongs to Steinberg. On the parameter side, formula (12.1) supplies exactly the factor lost when the second Euler root is removed.

If $\mu$ is unramified, $n(\psi)=0$, and $a=\mu(\varpi)$, the result is

$$
\boxed{
\epsilon(s,\operatorname{St}\otimes\mu,\psi)
=-a q^{1/2-s}.}
\tag{12.7}
$$

Indeed the underlying unramified Weil representation has epsilon factor one, while the quotient $V^{I_F}/(\ker N)^{I_F}$ is the $\mu|\cdot|^{-1/2}$ line. The determinant in (12.1) is $-q^{-s}a q^{1/2}$. If $\mu$ is ramified, the invariant quotient is zero and (12.6) is simply the product of the two ramified rank-one factors. This proves (12.4) for all special representations.

### 12.4 Quadratic induction and the lambda factor

Put

$$
\psi_E=\psi\circ\operatorname{Tr}_{E/F}.
$$

Its conductor exponent is

$$
n(\psi_E)=e(E/F)n(\psi)+d(E/F).
\tag{12.8}
$$

Define

$$
\lambda(E/F,\psi)
=\frac{
\epsilon_F(s,\operatorname{Ind}_{W_E}^{W_F}1,\psi)}
{\epsilon_E(s,1,\psi_E)}.
\tag{12.9}
$$

The conductor induction formula and (12.8) show that numerator and denominator have the same $s$-degree, so this quotient is independent of $s$.

**Theorem 12.2 (quadratic induction).** For every admissible $\theta$,

$$
\boxed{
\epsilon_F(s,\operatorname{AI}_{E/F}(\theta),\psi)
=\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E).}
\tag{12.10}
$$

The same formula holds for the induced parameter.

**Proof.** For the parameter, finite-index induction reduces the local Fourier constant to the rank-one constant over $E$; the discrepancy for the trivial character is, by definition, $\lambda(E/F,\psi)$. Multiplicativity on the character group proves (12.10).

For the representation, unfold the toric Whittaker function over the $F$-space $E$. Its Weyl transform is Fourier transformation with respect to $\psi_E$. The rank-one equation over $E$ contributes $\epsilon_E(s,\theta,\psi_E)$. Comparing the $F$-self-dual measure on the two-dimensional space with the $\psi_E$-self-dual measure contributes the normalized quadratic Gauss sum. The defining Gauss-sum normalization of the rectifier identifies that scalar with $\lambda(E/F,\psi)$. Thus the two sides give the identical expression. $\square$

For an unramified quadratic extension and conductor-zero $\psi$, the lambda factor is one. For a tamely ramified quadratic extension it is a normalized quadratic Gauss sum and need not be one. Its square is controlled by $\omega_{E/F}(-1)$. The conductor records the size of the finite sum; lambda records its phase.

### 12.5 Duality and change of additive character

The equality of epsilon factors respects every normalization change. For $c\in F^\times$, let $\psi_c(x)=\psi(cx)$ and use its self-dual measure. Then

$$
\boxed{
\epsilon(s,\pi,\psi_c)
=\omega_\pi(c)|c|^{2s-1}\epsilon(s,\pi,\psi).}
\tag{12.11}
$$

On the parameter side this is

$$
\det D(c)|c|^{\dim D(s-1/2)}\epsilon(s,D,\psi),
$$

and (8.1) makes the two formulas identical. In the dihedral case, the rank-one factor over $E$ contributes $\theta(c)|c|^{2s-1}$ and lambda contributes $\omega_{E/F}(c)$, giving the central character (7.6).

Fourier inversion gives the duality identity

$$
\gamma(s,\pi,\psi)
\gamma(1-s,\pi^\vee,\psi^{-1})=1,
\tag{12.12}
$$

and the same formula for parameters. With the same additive character in both factors, the right side becomes $\omega_\pi(-1)=\det D(-1)$. Finally, for an unramified character $\chi$ with $\chi(\varpi)=b$,

$$
\epsilon(s,D\otimes\chi,\psi)
=b^{a(D)+n(\psi)\dim D}\epsilon(s,D,\psi).
\tag{12.13}
$$

Twist compatibility (8.2) gives the identical representation formula. These identities complete the local-factor audit.

## 13. Finite extension and base change

### 13.1 Restriction as the definition

Replacing the ground field tests whether the correspondence is genuinely local or merely a collection of formulas over one field. The parameter operation is canonical: restrict the Weil action and leave monodromy unchanged. This determines base change on every case for which the restricted parameter remains in the selected range.

Let $L/F$ be finite separable. For $D=(r,N)$ put

$$
D_L=(r|_{W_L},N).
\tag{13.1}
$$

The equality

$$
|w|_L=|w|_F\qquad(w\in W_L)
\tag{13.2}
$$

shows that (13.1) still satisfies the monodromy relation. Define

$$
\boxed{
\operatorname{BC}_{L/F}(\pi)
=\operatorname{rec}_{2,L}^{-1}
\left(\operatorname{rec}_{2,F}(\pi)|_{W_L}\right)}
\tag{13.3}
$$

whenever the restricted parameter belongs to the selected classes over $L$. The formulas below show exactly what this means in the principal, special, and stable tame dihedral cases. Loss of quadratic regularity moves the parameter into the selected split class. If a resulting irreducible quadratic pair leaves the chosen tame type range, (13.3) still describes the parameter operation, but no assertion is made here about a representation outside the selected catalog.

Rank-one functoriality supplies the central rule:

$$
\chi|_{W_L}\longleftrightarrow\chi\circ N_{L/F}.
\tag{13.4}
$$

It follows at once that

$$
\omega_{\operatorname{BC}_{L/F}(\pi)}
=\omega_\pi\circ N_{L/F},
\tag{13.5}
$$

because determinant commutes with restriction and central character equals determinant.

### 13.2 Principal and special base change

Write

$$
\chi_{i,L}=\chi_i\circ N_{L/F},
\qquad
\mu_L=\mu\circ N_{L/F}.
$$

For an irreducible principal series,

$$
\operatorname{BC}_{L/F}(I(\chi_1,\chi_2))
=I(\chi_{1,L},\chi_{2,L})
\tag{13.6}
$$

provided the right side remains irreducible. If

$$
\chi_{1,L}\chi_{2,L}^{-1}=|\cdot|_L^{\pm1},
$$

the restricted parameter still has zero monodromy, so its inverse image is the character constituent

$$
\nu\circ\det
$$

for the unique $\nu$ satisfying

$$
\{\chi_{1,L},\chi_{2,L}\}
=\{\nu|\cdot|_L^{1/2},\nu|\cdot|_L^{-1/2}\}.
\tag{13.7}
$$

It is not the Steinberg constituent, because restriction cannot create monodromy.

For a character and a special representation,

$$
\operatorname{BC}_{L/F}(\mu\circ\det)
=\mu_L\circ\det,
\tag{13.8}
$$

$$
\boxed{
\operatorname{BC}_{L/F}(\operatorname{St}_F\otimes\mu)
=\operatorname{St}_L\otimes\mu_L.}
\tag{13.9}
$$

**Proof.** Restriction distributes over a direct sum, and (13.4) gives (13.6)--(13.8). For (13.9), the norm character $|\cdot|$ restricts unchanged by (13.2), while the nilpotent operator remains the same. Hence

$$
\operatorname{Sp}_{2,F}(\mu)|_{W_L}
=\operatorname{Sp}_{2,L}(\mu_L).
$$

Applying the inverse table gives the claim. $\square$

The special formula shows why centered half-powers are advantageous. An uncentered block would require a compensating residue-degree shift every time the base field changed.

### 13.3 Mackey analysis of a dihedral parameter

Quadratic base change can preserve cuspidality or destroy it. The distinction is whether the quadratic field remains a field after scalar extension.

Let $E/F$ be quadratic, let $\theta$ be admissible, and set

$$
D=\operatorname{Ind}_{W_E}^{W_F}\theta.
$$

First suppose $E\not\subseteq L$. Then $M=EL$ is quadratic over $L$, $E\cap L=F$, and Mackey theory has one double coset. Put

$$
\theta_L=\theta\circ N_{M/E}.
\tag{13.10}
$$

Then

$$
\boxed{
D|_{W_L}\simeq\operatorname{Ind}_{W_M}^{W_L}\theta_L.}
\tag{13.11}
$$

If $(M/L,\theta_L)$ remains admissible in the selected tame range, then

$$
\operatorname{BC}_{L/F}(\operatorname{AI}_{E/F}(\theta))
=\operatorname{AI}_{M/L}(\theta_L).
\tag{13.12}
$$

Now suppose $E\subseteq L$. Then the quadratic algebra splits:

$$
E\otimes_FL\simeq L\times L.
$$

Restriction of (2.8), together with (13.4) over $L/E$, gives

$$
\boxed{
D|_{W_L}\simeq
(\theta\circ N_{L/E})
\oplus
(\theta^\sigma\circ N_{L/E}).}
\tag{13.13}
$$

Thus base change becomes a principal-series parameter, or a boundary character parameter if the ratio becomes $|\cdot|_L^{\pm1}$. A dihedral supercuspidal can therefore cease to be supercuspidal after a field extension that contains its inducing quadratic field.

**Proof of (13.11)--(13.13).** Restrict the induced function model from $W_F$ to $W_L$. Mackey decomposition indexes summands by

$$
W_L\backslash W_F/W_E.
$$

If $E\not\subseteq L$, the product $W_LW_E$ is all of $W_F$ and the intersection is $W_M$, giving one induced summand. Restriction of $\theta$ to $W_M$ corresponds under reciprocity to $\theta\circ N_{M/E}$, proving (13.11). If $E\subseteq L$, there are two cosets and $W_L\subseteq W_E$; the two summands are the restrictions of $\theta$ and $\theta^\sigma$, giving (13.13). $\square$

Regularity is also transparent. In the field case, (13.11) remains irreducible exactly when $\theta_L\ne\theta_L^\tau$, where $\tau$ is the nontrivial automorphism of $M/L$. If equality occurs, the parameter splits and base change moves to the principal part of the table.

### 13.4 Conductors and newvectors after extension

Restriction does not admit a universal degree-only conductor formula. The correct statement uses the ramification filtration of $L/F$.

If $L/F$ is unramified, inertia and its upper numbering are unchanged. Therefore

$$
\boxed{a_L(D_L)=a_F(D).}
\tag{13.14}
$$

For every generic selected $\pi$, base change consequently has its newvector at the same exponent:

$$
\dim\operatorname{BC}_{L/F}(\pi)^{K_{1,L}(\mathfrak p_L^{a(\pi)})}=1.
\tag{13.15}
$$

The residue field is larger, so the subgroup and vector space are not literally the old ones; only the first exponent is preserved.

If $L/F$ is tamely ramified of ramification index $e$, positive upper depth is multiplied by $e$:

$$
\operatorname{Sw}_L(D_L)=e\operatorname{Sw}_F(D).
\tag{13.16}
$$

The tame term must be recomputed:

$$
a_L(D_L)=operatorname{codim}V^{I_L}
+e\operatorname{Sw}_F(D)
+\dim V^{I_L}-\dim(\ker N)^{I_L}.
\tag{13.17}
$$

The first and third terms have been left separate to show their origins: finite-inertia tame defect and monodromy defect. They may simplify in a particular case, but $I_L$ can kill a tame character and create invariant vectors. For wild $L/F$, the full Herbrand transition is required; no linear scaling is valid.

In the nonsplit dihedral case one may instead compute directly from (13.11):

$$
a_L(D_L)
=f(M/L)\bigl(a_M(\theta_L)+d(M/L)\bigr).
\tag{13.18}
$$

In the split case (13.13), the conductor is the sum of the conductors of the two displayed characters. Once this integer is known, Theorem 10.1 gives the first newvector line whenever the resulting representation is generic.

### 13.5 Euler and epsilon identities

For an unramified extension $L/F$ of residue degree $f$, geometric Frobenius over $L$ acts as $r(\Phi_F)^f$ and $q_L=q^f$. Hence

$$
\boxed{
L_L(s,D_L)=
\det\left(1-q^{-fs}r(\Phi_F)^f\mid(\ker N)^{I_F}\right)^{-1}.}
\tag{13.19}
$$

This is generally not equal to $L_F(s,D)$. It raises each unramified Frobenius root to the $f$th power and replaces $q^{-s}$ by $q^{-fs}$. For a principal series this is the product of the two rank-one base-changed factors; for a special representation it is $L_L(s+1/2,\mu_L)$.

There is a useful product identity when $L/F$ is cyclic. Let

$$
X_{L/F}=\operatorname{Hom}(F^\times/N_{L/F}L^\times,\mathbf C^\times).
$$

Projection from induction and restriction gives

$$
\operatorname{Ind}_{W_L}^{W_F}(D_L)
\simeq\bigoplus_{\eta\in X_{L/F}}D\otimes\eta.
\tag{13.20}
$$

The induction identity for Euler factors yields

$$
\boxed{
L_L(s,D_L)=
\prod_{\eta\in X_{L/F}}L_F(s,D\otimes\eta).}
\tag{13.21}
$$

For epsilon factors, put $\psi_L=\psi_F\circ\operatorname{Tr}_{L/F}$. Induction contributes the lambda constant, so

$$
\boxed{
\epsilon_L(s,D_L,\psi_L)
=\lambda(L/F,\psi_F)^{-\dim D}
\prod_{\eta\in X_{L/F}}
\epsilon_F(s,D\otimes\eta,\psi_F).}
\tag{13.22}
$$

**Proof.** Apply the Euler and epsilon induction formulas to the left side of (13.20), then use direct-sum multiplicativity on the right. The Euler induction formula has no scalar. The epsilon induction formula contributes $\lambda(L/F,\psi_F)^{\dim D}$, which moves to the denominator in (13.22). Trace compatibility of the additive characters is essential; unrelated conductor-zero characters would introduce the scaling factor (12.11). $\square$

Because local factors already match under $\operatorname{rec}_2$, equations (13.19)--(13.22) hold equally for the selected representation base changes.

### 13.6 Transitivity and compatibility checks

If $F\subseteq L\subseteq M$ are finite and every intermediate parameter stays in the selected range, restriction is transitive:

$$
\operatorname{BC}_{M/L}(\operatorname{BC}_{L/F}(\pi))
=\operatorname{BC}_{M/F}(\pi).
\tag{13.23}
$$

Norm transitivity proves the same statement character by character in (13.6), (13.9), and (13.10). Mackey decomposition in one step or two steps gives identical induced parameters. Lambda constants satisfy the corresponding tower identity, so epsilon factors also agree in one step and two.

Base change commutes with twists and contragredients:

$$
\operatorname{BC}_{L/F}(\pi\otimes\chi)
=\operatorname{BC}_{L/F}(\pi)\otimes(\chi\circ N_{L/F}),
\tag{13.24}
$$

$$
\operatorname{BC}_{L/F}(\pi^\vee)
=\operatorname{BC}_{L/F}(\pi)^\vee.
\tag{13.25}
$$

Both follow because restriction commutes with tensor products and duals. Equations (13.5), (13.14)--(13.18), and (13.21)--(13.22) then show that central characters, conductors, newvector levels, Euler factors, and epsilon factors transform exactly as their restricted parameters require.

## 14. Characterization and final synthesis

### 14.1 A recognition theorem

The preceding construction can now be compressed into a criterion that is useful in calculations. It also shows that the compatibilities are not an accidental list: together they identify the matching.

**Theorem 14.1 (recognition in the selected range).** Let $\pi$ be a selected irreducible representation of $\operatorname{GL}_2(F)$ and let $D$ be a selected two-dimensional Frobenius-semisimple parameter. Then

$$
D\simeq\operatorname{rec}_2(\pi)
$$

if and only if the following class-specific conditions hold.

1. If $\pi$ is an irreducible principal series, $D$ is split with zero monodromy and its unordered characters are the two normalized Jacquet exponents of $\pi$.
2. If $\pi=\mu\circ\det$, $D$ has zero monodromy and characters $\mu|\cdot|^{1/2}$ and $\mu|\cdot|^{-1/2}$.
3. If $\pi=\operatorname{St}\otimes\mu$, $D$ has nonzero monodromy and $W_F$ acts on $\ker N$ through $\mu|\cdot|^{1/2}$.
4. If $\pi$ is tame dihedral, write it uniquely as $\operatorname{AI}_{E/F}(\theta)$ up to equivalence of admissible pairs; then $D=\operatorname{Ind}_{W_E}^{W_F}\theta$.

**Proof strategy.** The structural condition locates the row. Within a row, Jacquet exponents, the action on the kernel of monodromy, or restriction to the quadratic subgroup recovers the character data.

**Proof.** The first assertion follows from uniqueness of the unordered normalized Jacquet exponents. The second is the zero-monodromy boundary row of (4.2). In the third case, Section 2.3 shows that a nonzero-monodromy parameter is determined by its action on $\ker N$, so the stated character forces $D=\operatorname{Sp}_2(\mu)$. In the fourth case, equivalence of admissible pairs on both sides gives exactly the same orbit $\{\theta,\theta^\sigma\}$. The converse in every row is the construction of Theorem 4.1. $\square$

The class-specific hypotheses matter. A determinant and a conductor do not distinguish the three parameter shapes, and even one untwisted gamma factor can coincide accidentally. Structural data such as Jacquet exponents, monodromy, or quadratic restriction are required. The twisted factor identities of Chapters 11 and 12 then provide stringent checks on the recognized pair rather than an extra unproved recognition principle.

### 14.2 A calculation protocol

The correspondence is most reliable when applied in a fixed order.

Start by deciding the structural class. For a representation, inspect its Jacquet module, genericity, and compactness of coefficients modulo the center. For a parameter, inspect reducibility of $r$ and whether $N$ vanishes.

Next recover the character data. A principal series gives an unordered pair. A special parameter gives $\mu$ from the action on $\ker N$. A dihedral parameter gives $E$ from its index-two projective kernel and gives $\{\theta,\theta^\sigma\}$ after restriction.

Then check the normalization ledger:

$$
\operatorname{rec}_F(\varpi)=\Phi_F,
\qquad
I(\chi_1,\chi_2)\text{ uses }\delta_B^{1/2},
\qquad
\operatorname{Sp}_2\text{ is centered}.
$$

In the dihedral case insert the rectifier before comparing central characters. Only then compute the conductor, Euler factor, and epsilon factor. Compute the conductor before the Gauss sum: it fixes the correct finite quotient and prevents a nonprimitive sum from vanishing unexpectedly. Finally, if the field is extended, restrict the parameter first and use the split/non-split Mackey analysis before attempting to name the resulting representation.

This order separates structural decisions from scalar phases. A uniformizer, additive character, or square root of $q$ can change a displayed formula; none may change the isomorphism class once all normalizations are transported consistently.

### 14.3 What the selected correspondence proves

For the principal, special, and tame dihedral classes, the correspondence is now constructed rather than postulated. It is a bijection, and it satisfies

$$
\omega_\pi=\det\operatorname{rec}_2(\pi),
$$

$$
\operatorname{rec}_2(\pi\otimes\chi)
=\operatorname{rec}_2(\pi)\otimes\chi,
$$

$$
\operatorname{rec}_2(\pi^\vee)
=\operatorname{rec}_2(\pi)^\vee,
$$

$$
a(\pi)=a(\operatorname{rec}_2(\pi)),
$$

and

$$
L(s,\pi)=L(s,\operatorname{rec}_2(\pi)),
\qquad
\epsilon(s,\pi,\psi)
=\epsilon(s,\operatorname{rec}_2(\pi),\psi).
$$

For every generic selected representation, the common conductor is its first newvector level and the first fixed space is one-dimensional. Under finite extension, restriction defines base change, preserves special monodromy, carries characters through norms, and transforms quadratic induction by Mackey decomposition. The exact cyclic product identities record the change in Euler and epsilon factors.

The boundary remains explicit. Primitive wild supercuspidals and the additional type theory needed for wildly ramified quadratic extensions in residue characteristic two are not included. Nor has an assertion about a selected quadratic pair after an extension been made when that pair leaves the selected tame range. These are limits of scope, not unproved cases hidden inside a theorem.

### 14.4 Conclusion

The local correspondence in dimension two is governed by a remarkably small structural choice. Two separate character lines produce a principal series. The same norm-spaced lines joined by a nilpotent arrow produce Steinberg. Two conjugate character lines visible only after passing to a quadratic field produce a dihedral supercuspidal. Reducibility and monodromy, not determinant or conductor alone, distinguish the three.

Every compatibility reflects that structure. Central characters become determinants because the split torus multiplies its two characters and quadratic induction contributes the sign of the two cosets. Determinant twists become tensor products because the determinant restricts to the quadratic norm. Contragredients invert every character. Conductors count lost invariant directions, with the different measuring the trace-dual defect under induction. Newvectors occur when the Kirillov support interval first contains one shell. Euler factors retain precisely the inertia-fixed kernel of monodromy, while epsilon factors restore the lost directions through Gauss sums and the monodromy determinant.

Finite extension does not disturb this picture. Norms restrict characters, centered monodromy survives unchanged, and Mackey theory decides whether a quadratic torus stays elliptic or splits. Conductors then follow ramification depth rather than a naive degree rule, and lambda factors record the phase invisible to the conductor.

The result is a coherent correspondence, not merely a table. Construction, classification, Fourier analysis, ramification, and finite extension all point to the same matching. In the principal, special, and tame dihedral cases, each side can therefore be used as a complete computational language for the other.
