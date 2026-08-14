# Hardly Ramified $3$-adic Representations

## Contents

1. [The signed-special endgame](#1-the-signed-special-endgame)
   - [The purpose and boundary of the theorem](#11-the-purpose-and-boundary-of-the-theorem)
   - [The exact input](#12-the-exact-input)
   - [The reusable theorem](#13-the-reusable-theorem)
   - [What is conditional upstream](#14-what-is-conditional-upstream)
   - [The minimal final chain and the blueprint](#15-the-minimal-final-chain-and-the-blueprint)
2. [The local signed-special calculation](#2-the-local-signed-special-calculation)
   - [Nonzero monodromy and the intrinsic line](#21-nonzero-monodromy-and-the-intrinsic-line)
   - [The saturated integral filtration](#22-the-saturated-integral-filtration)
   - [Every finite coefficient level](#23-every-finite-coefficient-level)
   - [Exponent-three subquotients](#24-exponent-three-subquotients)
3. [Finite-flat devissage and torsion fields](#3-finite-flat-devissage-and-torsion-fields)
   - [The modeled levels](#31-the-modeled-levels)
   - [Simple factors have exponent three](#32-simple-factors-have-exponent-three)
   - [The field cut out by an exponent-three factor](#33-the-field-cut-out-by-an-exponent-three-factor)
   - [Why the full tower is different](#34-why-the-full-tower-is-different)
4. [The exact root-discriminant ceiling](#4-the-exact-root-discriminant-ceiling)
   - [The contribution at three](#41-the-contribution-at-three)
   - [The contribution at two](#42-the-contribution-at-two)
   - [The global inequality and its numerical certificate](#43-the-global-inequality-and-its-numerical-certificate)
   - [The finite-image consequence](#44-the-finite-image-consequence)
5. [The class-field calculation](#5-the-class-field-calculation)
   - [Abelian subfields over the rationals](#51-abelian-subfields-over-the-rationals)
   - [The quadratic field and its ray groups](#52-the-quadratic-field-and-its-ray-groups)
   - [Solvability and the commutator](#53-solvability-and-the-commutator)
   - [The two simple factors](#54-the-two-simple-factors)
6. [Extensions and the ordered filtration](#6-extensions-and-the-ordered-filtration)
   - [The extension convention](#61-the-extension-convention)
   - [Pure extensions](#62-pure-extensions)
   - [The surviving Kummer direction](#63-the-surviving-kummer-direction)
   - [Vanishing in the reverse direction](#64-vanishing-in-the-reverse-direction)
   - [Sorting a composition series](#65-sorting-a-composition-series)
7. [The finite-coefficient identity](#7-the-finite-coefficient-identity)
   - [The canonical augmentation submodule](#71-the-canonical-augmentation-submodule)
   - [The cross relation](#72-the-cross-relation)
   - [Cayley--Hamilton and trace](#73-cayley--hamilton-and-trace)
   - [The residual orientation](#74-the-residual-orientation)
8. [The integral cyclotomic line](#8-the-integral-cyclotomic-line)
   - [Separated passage through all levels](#81-separated-passage-through-all-levels)
   - [Rank and saturation](#82-rank-and-saturation)
   - [The signed-special reducibility theorem](#83-the-signed-special-reducibility-theorem)
   - [Comparison with the local SP line](#84-comparison-with-the-local-sp-line)
9. [The optional certified Frobenius contradiction](#9-the-optional-certified-frobenius-contradiction)
   - [One certified good prime](#91-one-certified-good-prime)
   - [Transport to the algebraic coefficient field](#92-transport-to-the-algebraic-coefficient-field)
   - [Purity](#93-purity)
   - [The Frey endpoint](#94-the-frey-endpoint)
10. [Dependencies, hostile audit, and readiness](#10-dependencies-hostile-audit-and-readiness)
    - [Direct dependencies](#101-direct-dependencies)
    - [Exact upstream status](#102-exact-upstream-status)
    - [Hostile audit](#103-hostile-audit)
    - [Conclusion](#104-conclusion)

## 1. The signed-special endgame

### 1.1 The purpose and boundary of the theorem

The final three-adic step in the Frey argument starts after the compatible family and its
integral lattice have been constructed. It must not reconstruct either object. Its task is to
consume one precise all-level tower and show that the corresponding characteristic-zero
representation is reducible.

The dyadic member is on the signed-special, or **SP**, branch. Its Weil--Deligne monodromy
operator is nonzero of rank one. The associated adic representation has a unique inertia-fixed
line and nontrivial unipotent tame inertia. Thus the SP branch has conductor exponent one. It is
not a finite cubic inertial type, it does not have monodromy zero, and it does not have conductor
exponent two.

At the coefficient prime, this book uses only the integral output already isolated by Book 187:
every actual coefficient quotient of one globally stable lattice has a compatible
coefficient-linear finite-flat model over $\mathbf Z_3$, and, under clean support, those models
glue over $\mathbf Z[1/2]$. Rational crystallinity is the source of that output in Book 187, but
it is not reproved or used as a substitute for the tower here.

The proof has four stages:

$$
\begin{array}{c}
\text{SP square-zero inertia on exponent-three subquotients}
\\ \Downarrow
\operatorname{rd}<3^{3/2}2^{2/3}\text{ and degree at most }20
\\ \Downarrow
\text{constant and multiplicative simple factors, with ordered extensions}
\\ \Downarrow
0\to\mathcal O(1)\to T\to\mathcal O\to0.
\end{array}
\tag{1.1}
$$

The last sequence already contradicts the absolute irreducibility of the selected member.
It also gives a trace identity at every good Frobenius. That second endpoint is optional: a
prime is used only when the restricted away-from-two conclusion of Book 185 certifies both its
common algebraic polynomial and weight-one purity. There is no need to name the prime $5$.

### 1.2 The exact input

Let $K/\mathbf Q_3$ be finite, let $\mathcal O$ be its ring of integers, choose a uniformizer
$\varpi$, and put

$$
k=\mathcal O/\varpi\mathcal O,
\qquad
A_n=\mathcal O/\varpi^n\mathcal O.
\tag{1.2}
$$

Let

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_{\mathcal O}(T)
\tag{1.3}
$$

be continuous, where $T$ is free of rank two over $\mathcal O$, and put

$$
V=T\otimes_{\mathcal O}K,
\qquad
T_n=T/\varpi^nT.
\tag{1.4}
$$

The **Schoof-ready signed-special package** consists of the following data.

1. The determinant is exactly cyclotomic:
   $$
   \det\rho=\chi_3.
   \tag{1.5}
   $$
2. For every $n\ge1$, there is a finite locally free commutative group
   $$
   \mathcal G_n/\mathbf Z[1/2]
   \tag{1.6}
   $$
   of $3$-power order, with an $A_n$-action and a marking
   $$
   \mathcal G_n(\overline{\mathbf Q})\simeq T_n
   \tag{1.7}
   $$
   compatible with Galois and coefficients. The coefficient reductions and the exact
   multiplication sequences are modeled by the supplied tower.
3. At $2$, the rational member has the signed-special pair
   $$
   (r_2,N_2),
   \qquad
   N_2^2=0,
   \quad N_2\ne0,
   \quad\operatorname{rank}N_2=1,
   \tag{1.8}
   $$
   with trivial finite Weil inertia and
   $$
   r_2(F_2)N_2r_2(F_2)^{-1}=2N_2.
   \tag{1.9}
   $$
   If
   $$
   \mathscr L_2=\ker N_2=\operatorname{im}N_2,
   \tag{1.10}
   $$
   arithmetic Frobenius acts on $V/\mathscr L_2$ by a sign
   $\varepsilon_2\in\{1,-1\}$ and on $\mathscr L_2$ by $2\varepsilon_2$.

The existence of (1.6) already records clean support at every odd prime other than $3$.
Indeed a finite locally free $3$-primary group over $\mathbf Z_q$, for $q\ne3$, is finite
etale, so its generic module is unramified. No stronger support assertion will be inferred from
weak compatibility.

The tower (1.6) belongs to one chosen coefficient-three representation. No model for a member
at any other coefficient place is part of this package. Its fibers at every odd *base prime*
are localizations of this one tower, not instances of a family-wide integral-model record.

For the optional numerical contradiction, add a separate **certified good-prime record**. It
consists of a number field $E$, an embedding $\iota_\nu:E\hookrightarrow K$, and a prime
$q\ne2,3$ for which

$$
P_q(X)=X^2-a_qX+q\in E[X]
\tag{1.11}
$$

is the characteristic polynomial of $\rho(\operatorname{Frob}_q)$ after applying
$\iota_\nu$, and every root of $P_q$ has complex absolute value $\sqrt q$ under every
complex embedding. The restricted Book 185 conclusion supplies such records for every $q$
outside its finite certified exceptional set. Book 187's clean-support certificate is stronger:
it is needed for (1.6), not merely for choosing one $q$.

### 1.3 The reusable theorem

**Theorem 1.1 (signed-special hardly ramified three-adic endgame).** Assume the
Schoof-ready signed-special package of Section 1.2. Then there is a saturated
$G_{\mathbf Q}$-stable exact sequence

$$
\boxed{
0\longrightarrow\mathcal O(1)
\longrightarrow T
\longrightarrow\mathcal O
\longrightarrow0.
}
\tag{1.12}
$$

Consequently

$$
\boxed{
V^{\mathrm{ss}}\simeq K(1)\oplus K,
\qquad
\operatorname{tr}\rho(g)=1+\chi_3(g)
\quad(g\in G_{\mathbf Q}).
}
\tag{1.13}
$$

If $V$ is absolutely irreducible, (1.12) is already a contradiction. If instead the
certified good-prime record is supplied, then

$$
a_q=1+q,
\qquad
1+q\le2\sqrt q,
\tag{1.14}
$$

which is impossible because

$$
1+q-2\sqrt q=(\sqrt q-1)^2>0.
\tag{1.15}
$$

The theorem is reusable because its conclusion uses neither the provenance of the family nor a
preferred lattice construction. It needs the actual tower (1.6), the exact determinant, and the
SP local record. It does not need a residual nonzero-monodromy assertion for the chosen lattice.

### 1.4 What is conditional upstream

The restricted conclusion of Book 185, Theorem 9.1, conditionally supplies the actual
away-from-two collection, the cyclotomic determinant, the pure polynomials outside a finite
set, and the rational SP pair (1.8)--(1.10). Book 186 selects its member at $\nu\mid3$ and
records explicitly that this selection does not use $(\mathrm{AI}_2)$. Neither book supplies a
lattice or coefficient-prime finite flatness.

Book 187, Theorem 10.2, is stated from precisely that selected away-from-two member. Its proof
uses no coefficient place above two. Consequently Book 184's $(\mathrm{AI}_2)$ is not part of
the coefficient-three antecedent in this book; it is needed only for the stronger all-finite-
coefficient-place form of Book 185.

Book 187, Theorem 10.2, conditionally supplies (1.6)--(1.7). Its hypotheses include both the
coefficient-prime certificate $(\mathrm C_3)$ and the clean-support certificate $(\mathrm U)$.
This book consumes that theorem exactly as stated.  In its reusable abstract form those two
certificates are hypotheses; in the controlled-top application Book 187, Theorem 2.3 and
Proposition 2.1 prove $(\mathrm C_3)$, while Book 185, Proposition 8.3 proves
$(\mathrm U)$.  They are therefore not additional blockers on the preferred selected-three
chain.

Thus Theorem 1.1 is a complete conditional implication. The unconditional FLT chain remains
blocked upstream of its antecedent. The distinction will be recorded again in Section 10.2.

### 1.5 The minimal final chain and the blueprint

The final dependency chain is shorter than the strong spreading theorem stated in the FLT
blueprint and represented in its formal arithmetic core by `integralModelsAway`:

$$
\begin{array}{c}
\text{one absolutely irreducible rational member }V=r_\nu,\ \nu\mid3
\\ \Downarrow\quad\text{Book 187: one stable lattice and its all-level tower}
\\ \Downarrow\quad\text{Book 161: the finite-level Schoof identities}
\\ \Downarrow\quad\text{this book: }0\to K(1)\to V\to K\to0
\\ \Downarrow
\text{contradiction to absolute irreducibility.}
\end{array}
\tag{1.16}
$$

The blueprint packages integral models for every odd-coefficient member because its public
spreading theorem is family-wide, then uses the three-adic trace identity and compatibility
to return to the original residual representation. For (1.16), only the selected $\nu$-adic
tower is consumed. Clean support at all $q\ne2,3$ is still indispensable, since it is what
globalizes each level over $\mathbf Z[1/2]$.

Relative to the controlled rational family, the only genuinely new arithmetic datum is the
selected coefficient-three all-level finite-flat carrier used by Book 187. A compact stable
lattice without finite-flat models is insufficient, and a single mod-$3$ model is
insufficient. No condition $K=\mathbf Q_3$ or $k=\mathbf F_3$, no residual irreducibility,
no primitive residual monodromy, and no separately assumed conductor integer is used. The
full SP pair proves the required odd-tame dyadic behavior; its conductor exponent one is a
consequence, not a classification premise.

## 2. The local signed-special calculation

### 2.1 Nonzero monodromy and the intrinsic line

Let $D_2$ be a decomposition group at $2$. The pair (1.8)--(1.10) corresponds to an
unramified character

$$
\eta_2:D_2\longrightarrow\{1,-1\},
\qquad
\eta_2(F_2)=\varepsilon_2,
\tag{2.1}
$$

and an exact sequence

$$
0\longrightarrow K(1)\otimes\eta_2
\longrightarrow V|_{D_2}
\longrightarrow K\otimes\eta_2
\longrightarrow0.
\tag{2.2}
$$

The first line is the $K$-line $\mathscr L_2$ from the base-changed algebraic local pair. The
extension is nonsplit on inertia because $N_2\ne0$. Wild inertia is trivial, while tame inertia
acts unipotently. In particular

$$
\dim_KV^{I_2}=1,
\qquad
a_2(V)=2-1=1.
\tag{2.3}
$$

Equation (2.3) is a consequence, not the definition, of the SP branch. A conductor integer alone
would forget the line, the sign, and the nonzero monodromy.

The line in (2.2) is intrinsic. If a two-dimensional unipotent representation has nonzero
rank-one monodromy, then

$$
\ker N_2=\operatorname{im}N_2=V^{I_2}.
\tag{2.4}
$$

No second inertia-fixed line exists. This uniqueness will be used only after the global line has
been constructed.

### 2.2 The saturated integral filtration

Intersect the rational SP line with the already chosen global lattice:

$$
T_2^+=T\cap\mathscr L_2,
\qquad
T_2^-=T/T_2^+.
\tag{2.5}
$$

The intersection is a rank-one $\mathcal O$-lattice. It is saturated: if
$\varpi x\in T_2^+$ with $x\in T$, then $x$ belongs to the $K$-line $\mathscr L_2$, hence to
$T_2^+$. Therefore $T_2^-$ is torsion free of rank one and thus free. After choosing generators,

$$
0\longrightarrow\mathcal O(1)\otimes\eta_2
\longrightarrow T|_{D_2}
\longrightarrow\mathcal O\otimes\eta_2
\longrightarrow0
\tag{2.6}
$$

is exact.

Choose a normalized $3$-primary tame character

$$
t_3:I_2\twoheadrightarrow\mathbf Z_3.
\tag{2.7}
$$

In a basis adapted to (2.6), inertia acts as

$$
\rho(\sigma)=
\begin{pmatrix}
1&\alpha t_3(\sigma)\\
0&1
\end{pmatrix},
\qquad
\alpha\in\mathcal O\setminus\{0\}.
\tag{2.8}
$$

The coefficient $\alpha$ is integral because $T$ is stable, and it is nonzero because the
rational monodromy is nonzero. Its valuation can be positive. Therefore rational nonzero
monodromy need not remain nonzero in $T/\varpi T$.

### 2.3 Every finite coefficient level

Because the quotient in (2.6) is free, reduction modulo $\varpi^n$ remains exact:

$$
0\longrightarrow A_n(1)\otimes\eta_2
\longrightarrow T_n|_{D_2}
\longrightarrow A_n\otimes\eta_2
\longrightarrow0.
\tag{2.9}
$$

Both endpoint characters are trivial on inertia: $\eta_2$ is unramified, and the $3$-adic
cyclotomic character is unramified at $2$. Hence, for every $\sigma\in I_2$,

$$
(\rho_n(\sigma)-1)T_n
\subset A_n(1)\otimes\eta_2,
\qquad
(\rho_n(\sigma)-1)(A_n(1)\otimes\eta_2)=0.
\tag{2.10}
$$

Thus

$$
\boxed{(\rho_n(\sigma)-1)^2=0.}
\tag{2.11}
$$

Formula (2.8) gives the exact inertia size. If $e=v_\varpi(3)$ and
$s=v_\varpi(\alpha)$, its image on $T_n$ is cyclic of order

$$
3^{\max\{0,\lceil(n-s)/e\rceil\}}.
\tag{2.12}
$$

The image can therefore grow through the tower. The universal conclusion is that it is a cyclic
$3$-group, hence odd, and that (2.11) holds. No all-level order-three claim is made.

### 2.4 Exponent-three subquotients

Let $W$ be a subquotient of some $T_n$ which is killed by $3$. Saturated schematic closure and
represented quotient inside $\mathcal G_n$ give $W$ an actual finite-flat model over
$\mathbf Z[1/2]$. Relation (2.11) descends to $W$.

Write $u=\rho_W(\sigma)-1$. Then $u^2=0$, and in characteristic three

$$
(1+u)^3=1+3u+3u^2+u^3=1.
\tag{2.13}
$$

Tame inertia is procyclic. Hence its image on $W$ is either trivial or cyclic of order $3$.
Wild inertia is already trivial. We have proved the precise local statement used in every
residual discriminant calculation:

$$
\boxed{
W[3]=W
\quad\Longrightarrow\quad
\operatorname{im}(I_2\mid W)\in\{1,C_3\}.
}
\tag{2.14}
$$

This is where the SP filtration enters the classification. Characteristic-zero monodromy stays
nonzero, but a particular exponent-three subquotient is allowed to have trivial inertia.

## 3. Finite-flat devissage and torsion fields

Book 161 owns the Schoof category and its classification. Chapters 3--7 verify that the supplied
SP coefficient tower satisfies that theorem's hypotheses and then import its conclusions. They
do not repeat the root-discriminant, class-field, Ext, or filtration proofs.

### 3.1 The modeled levels

For every $n$, the supplied $\mathcal G_n/\mathbf Z[1/2]$ is finite locally free of $3$-power
order and has generic module $T_n$. It is unramified at every odd prime other than $3$; its marked
model at $3$ supplies the required finite-flat local datum. Section 2.3 shows that tame inertia
at $2$ has odd $3$-power image. Hence

$$
\boxed{\mathcal G_n\in\mathcal S}
\tag{3.1}
$$

for the Schoof category $\mathcal S$ of Book 161, Section 1.4. The $A_n$-action is part of the
marked model, the reduction maps are coefficient-linear, and $T_n$ is free of rank two over
$A_n$. This is the SP-specific tower verification needed before the classification may be cited.

### 3.2 Simple factors have exponent three

Book 161, Theorem 6.2 says that the simple objects of $\mathcal S$ are
$C=\underline{\mathbf Z/3\mathbf Z}$ and $M=\mu_3$. Thus every composition factor is killed by
$3$ and Section 2.4 supplies its exact dyadic inertia boundary. We do not apply a fixed-exponent
discriminant bound to the full fields $\mathbf Q(T_n)$.

### 3.3 The field cut out by an exponent-three factor

The field and local-model analysis of such a factor is Book 161, Chapters 4--6. It combines the
finite-flat bound at $3$, the trivial-or-cubic tame inertia alternative at $2$, and the certified
global degree cutoff. No independent torsion-field classification is performed here.

### 3.4 Why the full tower is different

The inertia image on $T_n$ can have order growing with $n$, and cyclotomic layers show that no
uniform root-discriminant ceiling exists for the full tower. Book 161 works with composition
factors and finite extensions instead; this book follows that fixed-exponent mechanism exactly.

## 4. The exact root-discriminant ceiling

### 4.1 The contribution at three

For an exponent-three subquotient, the finite-flat different bound is imported through Book 161,
Chapter 4 from Books 56 and 159 with the unramified base $\mathbf Q_3$.

### 4.2 The contribution at two

The only possibilities are trivial or cyclic cubic tame inertia by (2.14). Book 161 computes the
corresponding dyadic contribution without upgrading the trivial case to the cubic case.

### 4.3 The global inequality and its numerical certificate

The certified root-discriminant inequalities and degree cutoffs are Book 161, Chapter 4. Their
analytic certificate belongs to Books 7 and 159 and is not reproduced here.

### 4.4 The finite-image consequence

The consequence used by the category proof is exactly Book 161's bounded residual torsion-field
statement. It applies to killed-by-three factors, not to $\mathbf Q(T_n)$ for arbitrary $n$.

**Proposition 4.1 (two-prime exponent-three cutoff; compatibility alias).** This is Book 161,
Proposition 4.1 specialized to the trivial-or-cubic dyadic row: every modeled exponent-three
subquotient has cutout-field degree at most twenty.

## 5. The class-field calculation

### 5.1 Abelian subfields over the rationals

The exclusion of unwanted abelian subfields is imported from Book 161, Chapter 5.

### 5.2 The quadratic field and its ray groups

Book 161 performs the required exact ray calculation, including the local-unit quotient and the
distinction between ramification at $2$ and at $3$.

### 5.3 Solvability and the commutator

The degree cutoff and group-theoretic commutator argument are part of the same Book 161 proof.
No stronger solvability statement for the full coefficient tower is asserted.

### 5.4 The two simple factors

**Imported theorem 5.1.** Book 161, Theorem 6.2 identifies the only simple objects as $C$ and
$M$, exchanged by Cartier duality. This conclusion includes the global integral-model
identification, not merely the two generic characters.

## 6. Extensions and the ordered filtration

### 6.1 The extension convention

We retain Book 161's convention that $\operatorname{Ext}^1(B,A)$ classifies
$0\to A\to E\to B\to0$.

### 6.2 Pure extensions

The constant-by-constant and multiplicative-by-multiplicative calculations are Book 161,
Chapter 7. They allow larger constant or multiplicative blocks and do not imply semisimplicity.

### 6.3 The surviving Kummer direction

Book 161 identifies $\operatorname{Ext}^1(C,M)$ with the permitted Kummer direction generated by
$2$. The resulting extension need not split.

### 6.4 Vanishing in the reverse direction

Book 161 proves $\operatorname{Ext}^1(M,C)=0$ globally over $\mathbf Z[1/2]$; a local splitting
at $3$ alone would not justify the filtration exchange.

### 6.5 Sorting a composition series

**Imported theorem 6.1.** Book 161, Theorems 9.1--9.2 sort every object of $\mathcal S$ and give
the functorial canonical sequence

$$
0\longrightarrow G^{\rm m}\longrightarrow G\longrightarrow G^{\rm c}\longrightarrow0,
\tag{6.1}
$$

with multiplicative subgroup and constant quotient. The sequence is not claimed to split.

## 7. The finite-coefficient identity

### 7.1 The canonical augmentation submodule

For the $A_n$-module $T_n$, put

$$
N_n=\sum_{g\in G_{\mathbf Q}}(\rho_n(g)-1)T_n.
\tag{7.1}
$$

By (3.1), the coefficient action, and the determinant $\chi_3$, all hypotheses of Book 161,
Section 10.1 hold. The canonical filtration makes $G_{\mathbf Q}$ trivial on $T_n/N_n$ and
cyclotomic on $N_n$.

### 7.2 The cross relation

Book 161, equation (10.4), gives for all $g,h$

$$
(\rho_n(h)-\chi_3(h))(\rho_n(g)-1)=0.
\tag{7.5}
$$

This relation controls the extension and is stronger than an equality of semisimplified
characters.

### 7.3 Cayley--Hamilton and trace

**Imported theorem 7.1.** Book 161, Theorem 10.1 applies over the finite local coefficient ring
$A_n$ and proves

$$
\operatorname{tr}\rho_n(g)=1+\chi_3(g)
\qquad(g\in G_{\mathbf Q}).
\tag{7.6}
$$

The theorem requires no freeness of $N_n$ or of its quotient.

### 7.4 The residual orientation

Book 161 states its residual orientation paragraph over $\mathbf F_3$, but no residue-degree-one
hypothesis is needed here. Indeed $A_1=k$ is an arbitrary finite extension of $\mathbf F_3$,
and $N_1$ is a $k$-subspace of the two-dimensional $k$-space $T_1$. If $N_1=0$, the action on
$T_1$ is trivial, contradicting the cyclotomic determinant at complex conjugation. If
$N_1=T_1$, (7.5) makes the action cyclotomic scalar, whose determinant is
$\overline\chi_3^2=1$, giving the same contradiction. Hence $N_1$ is a $k$-line. Equations
(7.1)--(7.5) then give

$$
0\longrightarrow k(1)\longrightarrow T_1\longrightarrow k\longrightarrow0.
\tag{7.7}
$$

After restriction of scalars this need not be a two-dimensional $\mathbf F_3$-representation,
and no such descent is used. The extension may be nonsplit; its orientation, not residual
splitting or a primitive inertia class, is what the $\mathcal O$-adic passage needs.

## 8. The integral cyclotomic line

### 8.1 Separated passage through all levels

Define the algebraic augmentation submodule

$$
N=\sum_{g\in G_{\mathbf Q}}(\rho(g)-1)T\subseteq T.
\tag{8.1}
$$

No completion is hidden in this definition. Since $T$ is noetherian, finitely many augmentation
images generate $N$. It is finitely generated and therefore $\varpi$-adically closed. Its image
in $T_n$ is exactly $N_n$.

For fixed $g,h$, relation (7.5) says that the endomorphism

$$
D_{g,h}=(\rho(h)-\chi_3(h))(\rho(g)-1)
\tag{8.2}
$$

has image in $\varpi^nT$ for every $n$. The lattice is separated:

$$
\bigcap_{n\ge1}\varpi^nT=0.
\tag{8.3}
$$

Therefore

$$
\boxed{
(\rho(h)-\chi_3(h))(\rho(g)-1)=0
\qquad(g,h\in G_{\mathbf Q}).
}
\tag{8.4}
$$

It follows that Galois acts cyclotomically on $N$ and trivially on $T/N$.

### 8.2 Rank and saturation

The residual line $N_1$ is nonzero, so $N$ contains an element not divisible by $\varpi$ in
$T$. In particular $N\ne0$. As a submodule of the free $\mathcal O$-module $T$, it is torsion
free.

Its rank cannot be two. If it were, $N\otimes K=V$, and (8.4) would make every
$\rho(h)$ the scalar $\chi_3(h)$ on $V$. Its determinant would be $\chi_3(h)^2$, contrary to
$\det\rho=\chi_3$ at complex conjugation.

Thus $N$ has rank one. Let

$$
\mathcal L=(N\otimes_{\mathcal O}K)\cap T.
\tag{8.5}
$$

Then $\mathcal L$ is a saturated rank-one submodule. Relation (8.4) holds on the $K$-span of
$N$, so Galois acts on $\mathcal L$ by $\chi_3$. Every augmentation image lies in
$N\subseteq\mathcal L$, so Galois acts trivially on $T/\mathcal L$. Saturation makes the quotient
free of rank one.

Consequently

$$
\mathcal L\simeq\mathcal O(1),
\qquad
T/\mathcal L\simeq\mathcal O.
\tag{8.6}
$$

### 8.3 The signed-special reducibility theorem

Equations (8.5)--(8.6) prove (1.12). Taking traces gives, for every $g$,

$$
\operatorname{tr}\rho(g)=1+\chi_3(g),
\qquad
\det\rho(g)=\chi_3(g).
\tag{8.7}
$$

Tensoring with $K$ gives

$$
0\longrightarrow K(1)
\longrightarrow V
\longrightarrow K
\longrightarrow0,
\tag{8.8}
$$

and hence

$$
V^{\mathrm{ss}}\simeq K(1)\oplus K.
\tag{8.9}
$$

No semisimplicity hypothesis was used to construct the line. If $V$ is semisimple, (8.8) splits
over $K$. The integral sequence need not split, because the Kummer class of $2$ survives.

### 8.4 Comparison with the local SP line

The global line $\mathcal L\otimes K$ is inertia-fixed at $2$, since $\chi_3$ is unramified
there. By the uniqueness in (2.4), it equals the rational local SP line. The local Frobenius
character on that line is $\chi_3\eta_2$, whereas the global character is exactly $\chi_3$.
Therefore

$$
\eta_2=1,
\qquad
\varepsilon_2=1.
\tag{8.10}
$$

Thus a negative-sign input $\varepsilon_2=-1$ is already incompatible with the global
finite-flat conclusion. The main theorem does not rely on this shortcut: the good-prime trace
contradiction treats either input sign uniformly.

## 9. The optional certified Frobenius contradiction

### 9.1 One certified good prime

The restricted conclusion of Book 185, Theorem 9.1, supplies a finite exceptional set $S$ and,
for every prime $q\notin S$, a polynomial

$$
P_q(X)=X^2-a_qX+q\in E[X]
\tag{9.1}
$$

which is pure of weight one. Since $S\cup\{2,3\}$ is finite, there exists a prime

$$
q\notin S\cup\{2,3\}.
\tag{9.2}
$$

For the selected place $\nu\mid3$, weak compatibility certifies that $V$ is unramified at this
$q$ and that (9.1), after the embedding $\iota_\nu:E\hookrightarrow K$, is the characteristic
polynomial of arithmetic Frobenius.

This choice uses only the proved cofinite good set. If one wants to take $q=5$, one must first
verify $5\notin S$ or separately certify its local polynomial. No such verification is needed for
Theorem 1.1.

### 9.2 Transport to the algebraic coefficient field

Equation (8.7) gives

$$
\operatorname{tr}\rho(\operatorname{Frob}_q)=1+q
\tag{9.3}
$$

because arithmetic Frobenius satisfies

$$
\chi_3(\operatorname{Frob}_q)=q.
\tag{9.4}
$$

Compatibility gives the same trace as $\iota_\nu(a_q)$. Therefore

$$
\iota_\nu(a_q)=1+q.
\tag{9.5}
$$

The coefficient embedding is injective, so equality in the completion implies equality in the
algebraic coefficient field:

$$
\boxed{a_q=1+q\quad\text{in }E.}
\tag{9.6}
$$

No Chebotarev theorem is needed for this step. It compares one already constructed member with
its defining common polynomial at one certified prime.

### 9.3 Purity

Let $\alpha_q,\beta_q$ be the roots of $P_q$. Weight-one purity says that for every complex
embedding $\tau$ of a splitting field,

$$
|\tau(\alpha_q)|=|\tau(\beta_q)|=\sqrt q.
\tag{9.7}
$$

Hence

$$
|\tau(a_q)|
=|\tau(\alpha_q)+\tau(\beta_q)|
\le2\sqrt q.
\tag{9.8}
$$

But (9.6) is equality with the rational integer $1+q$, so every $\tau$ sends $a_q$ to
$1+q$. Thus

$$
1+q\le2\sqrt q,
\tag{9.9}
$$

contrary to (1.15). The determinant identity $\alpha_q\beta_q=q$ would not prove (9.7);
purity is a separate and indispensable compatible-family input.

### 9.4 The Frey endpoint

Book 164 supplies the residual signed-SP Frey datum and states the downstream contract. The
restricted Book 185 conclusion conditionally supplies an absolutely irreducible member at
$\nu\mid3$ with the rational SP record and pure good polynomials. Book 187 conditionally
supplies the all-level tower. Once those antecedents exist, Theorem 1.1 gives two
available endpoints:

1. the line in (8.8) contradicts absolute irreducibility; and
2. any certified prime (9.2) contradicts weight-one purity.

Only the first is used in the preferred chain. The second is an independent fallback and is
independent of a claim that the prime $5$ is good. The first endpoint does not need
semisimplicity or purity. Both use the actual characteristic-zero line, not merely a reducible
residual representation.

## 10. Dependencies, hostile audit, and readiness

### 10.1 Direct dependencies

The proof uses the following mathematical sources directly.

| Source | Exact input | Use here |
|---|---|---|
| Book 161, Theorems 6.2, 9.1--9.2, and 10.1 | the Schoof category, simple objects, Ext asymmetry, canonical multiplicative--constant filtration, and finite-level cross and trace identities | Chapters 3--7 and the input to the $\mathcal O$-adic passage |
| restricted conclusion of Book 185, Theorem 9.1 | absolute irreducibility, determinant, the rational SP pair, and, for the optional fallback, cofinite common good polynomials and purity at the selected place above three | the preferred contradiction and rational local record; Section 9 is optional, and no coefficient-two member is used |
| Book 187, Theorem 10.2 | the conditional clean-support, coefficient-linear all-level tower over $\mathbf Z[1/2]$ | the sole integral input at and away from $3$ |

Books 2--6, 17, 28--29, 34, 42, 51, and 159--160 enter transitively through Book 161's proved
classification package. Book 188 does not reopen their local discriminant, ray-class, Hopf-order,
or extension calculations.

Book 164 is the Frey provenance and downstream consumer contract, not a proof input to the
bounded representation-theoretic theorem. Books 40--41 concern descent and heights and are not
used here. Book 161 is the actual classification source, not comparative background.

The recommended direct dependency row is

$$
\boxed{
188\mid
161,185,187.
}
\tag{10.1}
$$

### 10.2 Exact upstream status

The bounded implication of Theorem 1.1 is complete. Relative to the controlled rational family,
Book 187 produces its remaining integral antecedent; the positive-carrier and clean-support
interfaces are closed. The preferred selected-three spine is dependency-closed.

1. **Controlled SP top.** Book 185, Theorem 9.1, assumes the controlled SP packet-array datum
   used by Books 183--184.  For the preferred final route, Book 182's split specialization,
   selected ascent and descent, ordinary attachment, and targetwise SP carriers are proved;
   Book 176, Theorem 1.1H and Corollary 1.1I prove the auxiliary and target instantiations of
   $({\rm CIAV}_P)$ separately. The uniform all-coefficient
   raw-to-global route still retains the smooth-proper Hodge--Tate comparison
   $(\mathrm{HT}_{\mathrm{curve}})$ isolated in Book 47, but the selected member at
   $\nu\mid3$ instead uses Book 183, Proposition 6.1A and therefore does not consume that
   theorem.
2. **Closed positive good carriers $(\mathrm{AVCar}_{3,\ell}^+)$.** Book 187 constructs these
   for every positive corrected packet.  Its sufficient $(\mathrm{Car}_3^+)$ uses the exact
   CM-unitary common-multiplier PEL datum, not the obstructed direct trace group.  The basic
   packet has trivial central character, so its level is first saturated by the central signs;
   Book 118 then identifies a common-adjoint component with a preliminary unitary component,
   rigidifies it at a fine level away from $3\ell$, and maps it finitely to the routed basic
   component over a field unramified at $3\ell$.  Book 121 gives the good model and Book 187,
   Proposition 2.2 transports the raw plane by rational pullback.  Theorem 2.3 constructs
   $(\mathrm{IC}_3)$ without an integral projector or an additional compatible-family
   arithmetic theorem.  Thus neither the positive carrier nor $(\mathrm{IC}_3)$ remains an
   independent blocker.  Ambient Tate-module semisimplicity is not needed for this fixed-three
   step, because Book 129 transfers the raw finite-flat tower to the semisimplification.
3. **Closed finite auxiliary comparison $(\mathrm{AUX}_\nu)$.** Book 185, Proposition 8.2 reduces
   clean support $(\mathrm U)$ to comparisons at the finite auxiliary set, using the
   distinguished unramified member away from $\ell$ and the spherical prime-to-$\ell$
   calculation at $q=\ell$.  The minimal certificate
   $(\mathrm{AVCar}_{3,\ell}^+)$ directly removes $q=\ell$ for the selected member by its
   good positive display; under the sufficient $(\mathrm{Car}_3^+)$ version, Book 187,
   Proposition 2.2 constructs that display.  Its family-wide form
   $(\mathrm{AUX}_{\mathrm{all}})$ proves $(\mathrm{Cond}_2)$, which also implies
   $(\mathrm U)$ by Proposition 8.1.  Weak compatibility does not supply the missing
   principal or dihedral descent model, type lines, trivial-wild and zero-monodromy
   calculations, exchange, or return maps.  Once those geometric data prove $N=0$, Book 128,
   Lemma 3.2 supplies raw-to-global passage formally.  Without $(\mathrm U)$, the local tower
   at $3$ cannot be glued over $\mathbf Z[1/2]$.

The omitted all-place hypothesis $(\mathrm{AI}_2)$ is deliberately not on this list: every
object used in Books 186--188 has coefficient characteristic three.

No additional blocker occurs inside Book 188 once Book 187, Theorem 10.2, and the selected
member's absolute irreducibility are supplied. One prime from Book 185's certified cofinite
good set is needed only for the optional Section 9 fallback.

### 10.3 Hostile audit

**SP type.** The dyadic object has $N_2\ne0$ of rank one, the intrinsic line
$\ker N_2=\operatorname{im}N_2$, the sign $\varepsilon_2$, and conductor exponent one. No
monodromy-zero or conductor-two language occurs.

**Integral thickness.** Rational nonzero monodromy does not imply nonzero residual monodromy for
an arbitrary global lattice. The proof uses only the saturated filtration and square-zero action;
it allows the first residual inertia image to be trivial.

**Higher dyadic inertia.** The image on $T_n$ can have order $3^r$ with $r>1$. The order-three
bound is used only after passing to a subquotient killed by $3$.

**Coefficient prime.** Crystallinity is not treated as finite flatness of an arbitrary lattice.
The only coefficient-prime input is the actual tower exported conditionally by Book 187,
Theorem 10.2. Every level is $\varpi^n$, not merely $3^n$.

**Coefficient field.** The finite-level theorem applies to $A_n=\mathcal O/\varpi^n$ even
when $K/\mathbf Q_3$ is ramified. Section 7.4 proves the residual orientation over the actual
residue field $k$. Neither $K=\mathbf Q_3$ nor $k=\mathbf F_3$ is assumed.

**Stable lattice.** Compactness gives a stable lattice but not the required finite-flat tower.
Book 187 constructs one lattice with compatible models at every level. No residual
irreducibility or uniqueness-up-to-homothety statement is used.

**Coefficient two.** No member at a coefficient place above two occurs. The rational base place
$2$ is compared with the selected three-adic member, so it lies in the prime-to-coefficient
range. The all-place hypothesis $(\mathrm{AI}_2)$ cannot affect this argument.

**Support.** A global model over $\mathbf Z[1/2]$ is used only under Book 187's clean-support
certificate. No auxiliary prime is removed from equality of almost all Frobenius traces.

**Conductor.** Book 161 consumes the global finite-flat model, cyclotomic determinant, and
odd-tame dyadic inertia. The integer $a_2(V)=1$ is derived from the SP pair and records its
Frey provenance; it is not an extra input to the classification. Residual conductor one and
primitive residual monodromy are not assumed.

**Discriminant normalization.** At $3$, $1/2$ is an upper-break cutoff and $3/2$ is a normalized
different bound. At $2$, the exact tame exponent is $2/3$. The global ceiling pays each factor
once and is applied only to exponent-three modeled objects.

**Numerics.** The logarithmic lower bound at degree $21$ is strictly larger than the logarithm
of the arithmetic ceiling. Monotonicity in the degree gives $[L:\mathbf Q]\le20$. No conditional
GRH table enters.

**Finite image.** Degree at most twenty does not imply reducibility. The proof separately uses
the abelian subfield calculation, the $\lambda$-ray groups of $\mathbf Q(\zeta_3)$, solvability,
and the normal-$3$-group fixed-vector argument.

**Extensions.** The $2$-Kummer extension survives in $\operatorname{Ext}^1(C,M)$. Only the
reverse group $\operatorname{Ext}^1(M,C)$ vanishes. Therefore the final integral sequence is not
declared split.

**Coefficient action.** The $A_n$-action is retained on every finite-flat model. It is what makes
Cayley--Hamilton a rank-two identity over $A_n$ and produces (7.6) for ramified coefficient
fields as well.

**Limit.** The proof does not lift a chosen residual vector. It passes the cross relation through
all separated coefficient levels, forms the algebraic augmentation submodule, and saturates its
rank-one $K$-span.

**Optional good prime.** The Section 9 prime lies in the restricted Book 185 conclusion's certified cofinite
good set. The argument does not assume that $5$ is outside the exceptional set. The inequality
is valid for every certified prime $q>1$. In particular, Book 164's illustrative downstream
choice of $5$ is not imported as an unproved local certificate.

### 10.4 Conclusion

The signed-special local record verifies that every supplied coefficient level lies in Book
161's Schoof category. Book 161 then supplies the fixed-exponent discriminant and class-field
classification, the constant and multiplicative simple objects, the asymmetric Ext calculation,
the ordered filtration, and the finite-level cross relation. The new argument here passes those
finite coefficient identities through the $\mathcal O$-adic tower, proves saturation, and matches
the resulting global cyclotomic line with the signed local SP line.

The resulting characteristic-zero cyclotomic line contradicts the absolute irreducibility of
the selected coefficient-three member. Optionally, at any prime in the certified pure good set,
the trace is simultaneously $1+q$ and bounded in absolute value by $2\sqrt q$, a second
impossibility. Thus the bounded conditional theorem of this book is

$$
\boxed{\textbf{READY}.}
\tag{10.2}
$$

The preferred selected-three FLT dependency spine is ready. The uniform all-coefficient
strengthening retains the optional Hodge--Tate input recorded in Section 10.2.
