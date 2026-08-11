# Hardly Ramified $3$-adic Representations

## Contents

1. [The endgame and its exact input](#1-the-endgame-and-its-exact-input)
   - [Why changing to three helps](#11-why-changing-to-three-helps)
   - [The companion supplied by the previous construction](#12-the-companion-supplied-by-the-previous-construction)
   - [The dyadic hypothesis that is actually available](#13-the-dyadic-hypothesis-that-is-actually-available)
   - [Four different conclusions](#14-four-different-conclusions)
   - [Logical architecture](#15-logical-architecture)
2. [Integral levels and torsion fields](#2-integral-levels-and-torsion-fields)
   - [Coefficient ideals and additive exponents](#21-coefficient-ideals-and-additive-exponents)
   - [Fields cut out by finite levels](#22-fields-cut-out-by-finite-levels)
   - [The residual dyadic block](#23-the-residual-dyadic-block)
   - [Subquotients and products](#24-subquotients-and-products)
   - [Why the full tower is not uniformly small](#25-why-the-full-tower-is-not-uniformly-small)
3. [The residual discriminant ceiling](#3-the-residual-discriminant-ceiling)
   - [The contribution at three](#31-the-contribution-at-three)
   - [The contribution at two](#32-the-contribution-at-two)
   - [The global root discriminant](#33-the-global-root-discriminant)
   - [The unconditional degree-twenty cutoff](#34-the-unconditional-degree-twenty-cutoff)
   - [What the cutoff does not classify](#35-what-the-cutoff-does-not-classify)
4. [The global finite-flat category](#4-the-global-finite-flat-category)
   - [Why the base is $\mathbf Z[1/2]$](#41-why-the-base-is-mathbf-z12)
   - [Gluing the local models](#42-gluing-the-local-models)
   - [Exact operations](#43-exact-operations)
   - [The precise categorical theorem](#44-the-precise-categorical-theorem)
5. [Classification of simple factors](#5-classification-of-simple-factors)
   - [Reduction to exponent three](#51-reduction-to-exponent-three)
   - [Abelian subfields](#52-abelian-subfields)
   - [Solvability and the commutator](#53-solvability-and-the-commutator)
   - [The two simple objects](#54-the-two-simple-objects)
   - [Why the discriminant argument alone is insufficient](#55-why-the-discriminant-argument-alone-is-insufficient)
6. [Extensions and filtration rearrangement](#6-extensions-and-filtration-rearrangement)
   - [The extension table](#61-the-extension-table)
   - [The surviving Kummer class](#62-the-surviving-kummer-class)
   - [Sorting a composition series](#63-sorting-a-composition-series)
   - [The canonical multiplicative--constant filtration](#64-the-canonical-multiplicative--constant-filtration)
7. [Finite coefficient levels](#7-finite-coefficient-levels)
   - [The coefficient action is indispensable](#71-the-coefficient-action-is-indispensable)
   - [The augmentation submodule](#72-the-augmentation-submodule)
   - [The cross relation](#73-the-cross-relation)
   - [The trace identity](#74-the-trace-identity)
   - [The residual representation](#75-the-residual-representation)
8. [Successive levels and the integral line](#8-successive-levels-and-the-integral-line)
   - [Compatibility across the tower](#81-compatibility-across-the-tower)
   - [Passage to the separated limit](#82-passage-to-the-separated-limit)
   - [Rank, saturation, and orientation](#83-rank-saturation-and-orientation)
   - [The integral reducibility theorem](#84-the-integral-reducibility-theorem)
9. [Semisimplification and characteristic zero](#9-semisimplification-and-characteristic-zero)
   - [The character identity](#91-the-character-identity)
   - [Semisimplification](#92-semisimplification)
   - [What semisimplicity adds](#93-what-semisimplicity-adds)
   - [The exact contradiction with the companion](#94-the-exact-contradiction-with-the-companion)
10. [The Frey contradiction](#10-the-frey-contradiction)
    - [The representation-theoretic form](#101-the-representation-theoretic-form)
    - [The Frobenius-trace form](#102-the-frobenius-trace-form)
    - [Why $p=5$ suffices](#103-why-p5-suffices)
    - [The precise endpoint](#104-the-precise-endpoint)
11. [Hostile mathematical audit](#11-hostile-mathematical-audit)
    - [Local-type audit](#111-local-type-audit)
    - [Discriminant audit](#112-discriminant-audit)
    - [Coefficient audit](#113-coefficient-audit)
    - [Filtration audit](#114-filtration-audit)
    - [Reducibility audit](#115-reducibility-audit)
12. [Conclusion](#12-conclusion)

## 1. The endgame and its exact input

### 1.1 Why changing to three helps

The final obstruction in the hardly ramified route is not that a two-dimensional Galois
representation has too much ramification in an informal sense. It is that, after changing the
coefficient prime to $3$, every finite coefficient quotient belongs to a remarkably small exact
category. At the coefficient prime, finite-flat geometry limits upper ramification. At the only
remaining bad prime, $2$, the primitive cubic tame type becomes a unipotent block modulo $3$.
These two local facts force the fields attached to exponent-three factors to have very small root
discriminant. The resulting degree cutoff makes the simple objects classifiable, and the exact
category then turns that classification into an integral invariant line.

The order of these ideas matters. A root-discriminant bound controls the size of a faithful
finite image, not its invariant subspaces. A list of simple factors controls semisimplification,
not extensions. A residual invariant line does not automatically lift through all coefficient
levels. Schoof's argument succeeds because the global finite-flat category addresses all three
problems in sequence:

$$
\text{small fields}
\Longrightarrow
\text{two simple factors}
\Longrightarrow
\text{sorted finite-flat filtration}
\Longrightarrow
\text{one integral line}.
$$

This book carries out that sequence for the exact companion constructed previously. It does not
replace the dyadic type by a Steinberg condition, a Tate-curve filtration, or a statement about
conductor alone. Those are different local hypotheses.

### 1.2 The companion supplied by the previous construction

Fix a place $\nu$ above $3$ in the coefficient field of the compatible family. Let

$$
E=E_\nu,qquad \mathcal O=\mathcal O_E,qquad
\mathfrak m=(\varpi),qquad k=\mathcal O/\mathfrak m,
$$

and let

$$
\rho:G_{\mathbf Q}\longrightarrow \operatorname{GL}_E(V)
$$

be the corresponding member. The changing-prime theorem supplies the following package.

1. $V$ is two-dimensional, continuous, semisimple, and absolutely irreducible.
2. Its determinant is exactly the $3$-adic cyclotomic character:
   $$
   \det\rho=\chi_3.
   $$
3. It is unramified at every prime outside $\{2,3\}$.
4. At $3$, it is crystalline of weights $\{0,1\}$, and there is a global stable free
   rank-two $\mathcal O$-lattice $T\subset V$ whose quotient by every open ideal of
   $\mathcal O$ has a compatible coefficient-linear finite-flat model over $\mathbf Z_3$.
5. Those local models glue to compatible finite locally free commutative group schemes over
   $\mathbf Z[1/2]$.
6. At $2$, wild inertia is trivial, monodromy is zero, and tame inertia acts in characteristic
   zero through a primitive cyclic group of order three.
7. The lattice may be chosen so that its first reduction has the nontrivial unipotent dyadic
   block and its decomposition-group-stable special line.
8. For $p\ne2,3$, the characteristic polynomial at arithmetic Frobenius is
   $$
   P_p(X)=X^2-a_pX+p,
   $$
   where the two complex roots have absolute value $\sqrt p$.

Every item in this ledger is needed, but at a different point. The finite-flat models enter the
discriminant estimate and the exact category. The primitive dyadic type supplies the tame cost at
$2$. The coefficient action permits the finite-level theorem to see a rank-two module over
$\mathcal O/\varpi^n$. Semisimplicity and absolute irreducibility are used only after the
categorical argument has produced the characteristic-zero constituents. Purity supplies a second,
numerical contradiction.

### 1.3 The dyadic hypothesis that is actually available

Let $t$ be a tame generator at $2$. On $V$ its operator $A=\rho(t)$ satisfies

$$
A^2+A+1=0,qquad A\ne1,qquad A^3=1.
\tag{1.1}
$$

Arithmetic Frobenius conjugates $A$ to $A^2$. Thus, after adjoining a primitive cube root of
unity, the two inertia characters are inverse primitive cubic characters and Frobenius exchanges
their eigenspaces. In particular,

$$
V^{I_2}=0,qquad a_2(V)=2.
$$

The monodromy operator is zero. This is a finite tame conductor-two type, not a rank-one special
or Steinberg type.

Choose a cyclic vector for $A$. In the resulting basis,

$$
A=
\begin{pmatrix}
0&-1\\
1&-1
\end{pmatrix}.
\tag{1.2}
$$

The characteristic polynomial becomes $(X-1)^2$ modulo $\mathfrak m$, while

$$
\det(A-1)=3.
$$

For the type-adapted lattice supplied by the changing-prime theorem, reduction is therefore not
the identity:

$$
(\overline A-1)^2=0,qquad \overline A-1\ne0.
\tag{1.3}
$$

Consequently

$$
\mathscr L_2=ker(\overline A-1)=\operatorname{im}(\overline A-1)
\tag{1.4}
$$

is a $k$-line stable under the full decomposition group. Relation (1.4) is a first-level fact.
It must not be promoted to a free rank-one fixed submodule at every higher coefficient level:
$A-1$ has determinant $3$, so its kernel and image at higher levels need not be free direct
summands.

This distinction is the most important boundary in the book. The actual input is primitive
cubic tame inertia in characteristic zero and one nontrivial unipotent block residually. No
integral dyadic sequence with two free rank-one endpoints has been established or will be used.

### 1.4 Four different conclusions

Four assertions that sound similar must be kept separate.

First, the residual semisimplification is

$$
(T/\varpi T)^{\mathrm{ss}}\simeq k\oplus k(1).
\tag{1.5}
$$

Second, the chosen residual module is oriented:

$$
0\longrightarrow k(1)\longrightarrow T/\varpi T
\longrightarrow k\longrightarrow0.
\tag{1.6}
$$

It is not split. The nontrivial dyadic block forces its class to be the nonzero Kummer direction
generated by $2$.

Third, there is an integral exact sequence

$$
0\longrightarrow \mathcal O(1)\longrightarrow T
\longrightarrow \mathcal O\longrightarrow0.
\tag{1.7}
$$

The existence and orientation of this sequence are stronger than residual reducibility. They are
obtained from the compatible finite-level cross relations, not by choosing unrelated lifts of the
residual line.

Fourth, after tensoring with $E$,

$$
V^{\mathrm{ss}}\simeq E(1)\oplus E.
\tag{1.8}
$$

Because the companion is semisimple, (1.8) becomes an actual direct sum. That contradicts its
absolute irreducibility. The contradiction does not require the integral extension (1.7) to split.

### 1.5 Logical architecture

The proof uses the dependencies through the following exact interfaces.

```text
Book 177:
coefficient-linear finite-flat tower over Z[1/2]
+ primitive C3 tame type at 2
+ determinant chi_3
                         |
                         v
Books 178--179:
residual rd < 3^(3/2) 2^(2/3)
+ unconditional degree <= 20
                         |
                         v
Book 181:
simple factors C and M
+ multiplicative--constant filtration
+ finite-coefficient cross relation
                         |
                         v
this book:
inverse limit -> O(1) line -> 1 + chi_3
                         |
              +----------+----------+
              v                     v
      absolute irreducibility       purity at p=5
      is impossible                 is impossible
```

Books 178 and 179 do not prove reducibility. Book 181 does not construct the companion. Book 177
does not classify its torsion factors. Each arrow uses only the theorem that precedes it.

## 2. Integral levels and torsion fields

### 2.1 Coefficient ideals and additive exponents

For $n\ge1$, put

$$
A_n=\mathcal O/\varpi^n\mathcal O,qquad
T_n=T/\varpi^nT.
$$

Then $T_n$ is free of rank two over $A_n$. If

$$
e_E=v_\varpi(3),
$$

the additive group of $A_n$ is killed by

$$
3^{m(n)},qquad m(n)=\left\lceil\frac n{e_E}\right\rceil.
\tag{2.1}
$$

This elementary coefficient calculation prevents a common normalization error. A quotient modulo
$\varpi^n$ is not generally killed by $3^n$. At the first level, however, $m(1)=1$, so the
residual module is always killed by $3$, independently of the ramification and residue degree of
$E/\mathbf Q_3$.

Let $\mathcal G_n/\mathbf Z[1/2]$ be the compatible coefficient-linear finite-flat model of
$T_n$. Forgetting its $A_n$-action leaves a finite locally free commutative group of $3$-power
order. Retaining the action is essential later: it is what lets one recover an $A_n$-linear
trace identity instead of merely a statement about a larger underlying $\mathbf Z/3^r$-module.

### 2.2 Fields cut out by finite levels

The finite action on $T_n$ cuts out a finite Galois field

$$
K_n=\overline{\mathbf Q}^{\ker(G_{\mathbf Q}\to\operatorname{Aut}_{A_n}(T_n))}.
\tag{2.2}
$$

Its Galois group is the faithful matrix image. The reduction maps give a tower

$$
K_1\subseteq K_2\subseteq\cdots.
$$

For $p\ne2,3$, inertia acts trivially on $T$, hence on every $T_n$. At $3$, the supplied model
over $\mathbf Z_3$ allows the finite-flat upper-break theorem to be applied to the full module,
including its extension data. At $2$, the action factors through the same cyclic group of order
three as the characteristic-zero action, though that group may act trivially on a particular
subquotient.

The last qualification matters. The field $K_1$ sees the nontrivial unipotent block and therefore
has dyadic inertia of order three. A simple factor of $T_1$ has trivial dyadic inertia because a
cyclic group of order three acts trivially on every simple module in characteristic three. Thus
the full residual field and its simple-factor fields have different local behavior even though all
belong to the same global category.

### 2.3 The residual dyadic block

Write $M=T_1$. Relation (1.3) shows that the image of $I_2$ on $M$ is precisely $C_3$. Since
$2\ne3$, this ramification is tame. The faithful local extension therefore has

$$
e_2=3,qquad d_2=e_2-1=2,qquad \frac{d_2}{e_2}=\frac23.
\tag{2.3}
$$

An unramified residue extension at $2$ changes neither the ramification index nor the normalized
ratio in (2.3). Nor is the factor multiplied by the dimension of $M$ or by the number of primes
above $2$; after taking the absolute degree root, the local contribution is exactly $2^{2/3}$.

The special line $\mathscr L_2$ does not yet determine the global orientation (1.6). Locally both
Jordan--Hölder factors are trivial on inertia. Global orientation uses the finite-flat endpoint at
$3$ and the asymmetric mixed extension groups in the Schoof category.

### 2.4 Subquotients and products

If $N\subseteq T_n$ is stable, its schematic closure in $\mathcal G_n$ is finite flat. The
represented quotient is finite flat as well. Thus every composition factor inherits an actual
integral model. This direction is valid because an ambient middle object is supplied. It would be
false to begin with abstract finite-flat models of two endpoints and infer that every extension
between them is finite flat.

Finite products behave equally well. If $X_1,\ldots,X_r$ are exponent-three subquotients, the
product of their models realizes the direct sum of their generic modules. At $3$, the upper-break
cutoff is the same maximum cutoff, not the sum of $r$ separate costs. At $2$, tame inertia is
procyclic, and each exponent-three image has order at most three. Hence the image on the direct
sum still has order at most three.

This product observation is what makes finite composita of exponent-three fields uniformly
small. A naive discriminant inequality for composita would count the same local ramification
repeatedly and destroy the sharp bound.

### 2.5 Why the full tower is not uniformly small

Applying the finite-flat estimate directly to $T_n$ gives a $3$-adic normalized different bound
that grows with $m(n)$. In the present two-prime situation one obtains the safe estimate

$$
\operatorname{rd}(K_n)
<3^{m(n)+1/2}2^{2/3}.
\tag{2.4}
$$

The exact dyadic factor is even independent of $n$, because the rational inertia already has
order three, but the coefficient-prime factor grows. There can be no level-independent bound:
the cyclotomic tower itself is finite flat at every level and has increasing root discriminant.

The later argument therefore never applies the residual degree-$20$ cutoff to $K_n$ for $n>1$.
It returns instead to simple factors and adjacent filtration exchanges killed by $3$ over the
fixed base. This is the legitimate stabilization mechanism.

The matrix kernels make the temptation especially strong. Reduction gives an injection

$$
\operatorname{Gal}(K_{n+1}/K_n)
\hookrightarrow
1+\varpi^nM_2(A_{n+1}),
$$

and the group on the right is additively controlled by a vector space over $k$. Thus the degree of
each step is uniformly bounded. But this is a statement about group order, not ramification depth.
The step is defined over the moving base $K_n$, and a finite-flat estimate there contains the
ramification index of $(K_n)_w$. After normalization through the tower, the old discriminant cost
returns. A bounded succession of step degrees can therefore have unbounded root discriminant.

The cyclotomic summand gives the exact counterexample inside the desired answer. For
$\mathbf Z_3(1)$, every quotient $\mu_{3^n}$ is finite flat, and

$$
\mathbf Q(\mu_3)\subset\mathbf Q(\mu_9)\subset\cdots
$$

has successive degrees at most three. Nevertheless its last ramification break and root
discriminant grow. Any proposed proof that the full tower stabilizes merely from bounded step
degree would eliminate the cyclotomic line that Schoof's theorem is supposed to produce.

There are two safe returns to exponent three. First, a simple factor in a composition series is
killed by three and inherits a model by saturated closure. Second, when adjacent factors are
exchanged, the two-step obstruction is itself an object killed by three with a supplied middle
model. Both live over $\mathbf Q$, not over $K_n$. The fixed-base discriminant ceiling therefore
applies to them uniformly. This is why exact-category devissage succeeds where a direct attack on
the torsion fields fails.

## 3. The residual discriminant ceiling

### 3.1 The contribution at three

Let $L_3/\mathbf Q_3$ be the local field cut out by the residual module $M$. Because $M$ is killed
by $3$ and has an actual finite-flat model over $\mathbf Z_3$, the finite-flat ramification theorem
gives

$$
G_{\mathbf Q_3}^u\text{ acts trivially on }M
\qquad(u>1/2).
\tag{3.1}
$$

If $e_3$ and $d_3$ are the ramification index and different exponent of $L_3/\mathbf Q_3$, the
upper-numbering form of Hilbert's different formula yields

$$
\frac{d_3}{e_3}<1+\frac12=\frac32.
\tag{3.2}
$$

The strict sign in (3.2) does not assert that a break at $1/2$ is impossible. It comes from the
finite terminal correction in the normalized different. Confusing the upper-break endpoint with
the strictness of the different estimate loses the exact constant.

It is useful to recall why finite flatness produces the cutoff. Let $B$ be the coordinate Hopf
algebra of a finite-flat group killed by $3$, and let $I$ be its augmentation ideal. The
multiplication-by-three map has linear term $3x$ at the identity, while modulo $3$ its terms of
degrees one and two disappear and the first possible nonlinear term has degree three. This forces
nonzero torsion points to stay outside a congruence ball of radius $1/2$. If an upper ramification
element with index greater than $1/2$ moved a point, the point and its translate would lie inside
that forbidden ball. Thus the element acts trivially. The argument controls the full modeled
module, including off-diagonal extension classes; separate estimates for its semisimple factors
would not suffice.

Now let $G^u$ be the upper ramification filtration of the faithful local image and let $e_3$ be
its inertia order. The upper form of Hilbert's formula is

$$
\frac{d_3}{e_3}
=1-\frac1{e_3}
+\int_0^\infty\left(1-\frac1{|G^u|}\right)du.
$$

The tame baseline is strictly less than one, and the positive-depth integral has support of length
at most $1/2$ and integrand at most one. This recovers (3.2). The endpoint $u=1/2$ has measure
zero and does not change the integral.

### 3.2 The contribution at two

By (2.3), the local field cut out by $M$ has tame inertia of order three at $2$. Hence its
normalized contribution is exactly $2/3$. If one passes to a quotient on which the dyadic block
becomes trivial, the contribution becomes zero; using $2/3$ remains a valid uniform upper bound.

No Artin-conductor shortcut is needed. The characteristic-zero conductor is two, while the
residual semisimplification has conductor zero. Neither integer by itself records the faithful
residual extension field. The actual tame inertia image does.

### 3.3 The global root discriminant

The field $K_1/\mathbf Q$ is Galois and unramified outside $\{2,3\}$. Combining (3.2) with the
exact tame term gives

$$
\boxed{
\operatorname{rd}(K_1)
<3^{3/2}2^{2/3}.
}
\tag{3.3}
$$

Numerically,

$$
3^{3/2}2^{2/3}=8.248377821991616\ldots.
$$

The same inequality holds for the field cut out by any finite direct sum of exponent-three
objects obtained from the tower. Products preserve the finite-flat model at $3$, and the common
tame generator still has image of order at most three at $2$.

### 3.4 The unconditional degree-twenty cutoff

The explicit-formula calculation established for this exact ceiling uses a compactly supported
test function with support parameter $6$. It proves for every number field $L$ of degree $n$

$$
\log\operatorname{rd}(L)>
\gamma+\log(8\pi)-\frac{12}{n}-1.10356.
\tag{3.4}
$$

At $n=21$, the right side exceeds

$$
2.126398521002197,
$$

whereas

$$
\log(3^{3/2}2^{2/3})<2.110016553375462.
$$

The lower bound in (3.4) increases with $n$. Thus (3.3) implies

$$
\boxed{[K_1:\mathbf Q]\le20.}
\tag{3.5}
$$

This comparison is unconditional and makes no assumption on signature. It also applies to every
finite compositum of the exponent-three subquotient fields described above. Since their degrees
are bounded and directed under compositum, they all lie in one finite maximal exponent-three
field. This finite arena justifies repeatedly returning to exponent-three obstruction objects.

### 3.5 What the cutoff does not classify

The bound (3.5) excludes faithful images of order at least $21$, including
$\operatorname{SL}_2(\mathbf F_3)$ and $\operatorname{GL}_2(\mathbf F_3)$, of orders $24$ and
$48$. It does not exclude a Borel image of order $12$, a nonsplit Cartan normalizer of order
$16$, or the residual Kummer field

$$
\mathbf Q(\zeta_3,\sqrt[3]{2})
$$

of degree six. In particular, the analytic estimate does not prove that $M$ splits, and it does
not identify its simple factors by itself.

The categorical classification supplies the missing group and ray-class arguments. The division
of labor is exact: discriminants create a finite range; arithmetic inside that range determines
the factors; extension theory then reconstructs the module.

## 4. The global finite-flat category

### 4.1 Why the base is $\mathbf Z[1/2]$

Let

$$
R=\mathbf Z[1/2].
$$

The prime $2$ is removed because the generic representation is genuinely ramified there. A finite
group scheme of $3$-power order over $\mathbf Z_2$ would be finite etale and hence have unramified
generic fiber. At every odd prime $q\ne3$, however, a group of $3$-power order is automatically
finite etale. Thus unramifiedness supplies a unique local model. At $3$, finite flatness is the
nontrivial integral condition.

The Schoof category $\mathcal S$ consists of finite locally free commutative $3$-primary group
schemes over $R$ whose generic modules have odd-tame inertia at $2$: wild inertia is trivial and
the finite tame inertia image has odd order. The objects $\mathcal G_n$ lie in $\mathcal S$ because
their dyadic inertia is a quotient of $C_3$.

The category is intentionally broader than the companion tower. Its inertia image may be any odd
cyclic group, not merely $C_3$. The sharper degree-$20$ estimate is invoked only for the particular
exponent-three direct sums for which the inertia image has order at most three.

### 4.2 Gluing the local models

Suppose a finite $3$-primary Galois module $W$ is unramified outside $\{2,3\}$ and has a chosen
finite-flat model over $\mathbf Z_3$. At every odd $q\ne3$, take the unique finite-etale Hopf order
corresponding to the unramified action. These orders agree with one spread-out rational Hopf algebra
away from finitely many primes. Their intersection inside the generic coordinate algebra is finite
projective over the Dedekind ring $R$ and is stable under multiplication, coproduct, counit, and
antipode. It therefore defines a finite locally free commutative group over $R$.

This gluing theorem is an existence theorem from marked local data. It does not say that a model
over a ramified extension of $\mathbf Q_3$ descends, nor that any abstract generic extension of two
modeled endpoints possesses a middle model.

Here are the algebraic details. Let $B_{\mathbf Q}$ be the coordinate algebra of the finite etale
generic group. Choose a rational basis containing $1$. After inverting one odd integer $N$, the
structure constants for multiplication, coproduct, counit, and antipode are integral in that basis.
After enlarging $N$, the trace discriminant is a unit, so the resulting order is finite etale over
$R[1/N]$. For every odd $q\nmid N$, henselian uniqueness identifies it with the unramified local
order. At the finitely many remaining odd primes, use the prescribed order, especially the
finite-flat one at $3$.

Define

$$
B=\{x\in B_{\mathbf Q}:x\in B_q\text{ for every odd prime }q\}.
\tag{4.2}
$$

Only finitely many conditions differ from the spread-out order. Thus $B$ is a finite torsion-free
$R$-module, hence projective because $R$ is Dedekind. Each Hopf operation preserves every $B_q$,
so it preserves their intersection. Localizing (4.2) recovers $B_q$ at each odd prime. This proves
the gluing theorem and shows exactly where dimension one of the base is used.

Uniqueness is deliberately local in scope. At an odd prime other than three the finite-etale order
is unique. At three, the chosen finite-flat order is retained. The global intersection is therefore
unique relative to those marked orders, but the same generic module can in principle admit a
different model at three.

### 4.3 Exact operations

Inside a chosen object, a stable generic subgroup has a saturated schematic closure. Over the
Dedekind base the closure is finite locally free, and the quotient is represented and finite flat.
Odd-tame inertia is stable under subobjects, quotients, products, extensions, and Cartier duality.
Consequently every object admits a composition series in the exact category.

The word saturated carries real content. An ordinary kernel on Hopf algebras can have torsion in
the quotient and fail to be flat. Saturation removes precisely that torsion. All later filtrations
are built with saturated closures and represented quotients; no vector-space filtration is simply
declared integral.

Concretely, if $A$ is a finite projective Hopf algebra and $I_{\mathbf Q}$ is the Hopf ideal of a
generic quotient, set

$$
I=A\cap I_{\mathbf Q}
$$

inside $A\otimes\mathbf Q$. Then $A/I$ is torsion free and therefore projective over $R$. The Hopf
identities hold after tensoring with $\mathbf Q$ and hence integrally because all relevant modules
are torsion free. This gives the saturated closure. The fppf quotient by that closed subgroup is
represented and finite flat. The generic-fiber functor is faithful, so equalities of morphisms may
be checked after tensoring with $\mathbf Q$.

For extensions, the local inertia assertion also needs proof. Suppose an exact sequence has
odd-order tame images on its two endpoints. The kernel of the middle inertia image in the product
of the endpoint images consists of filtration-lowering automorphisms. On a $3$-primary module that
kernel is a $3$-group. Hence the whole middle image has odd order. Wild inertia at $2$ is pro-$2$
and must act trivially. Thus the category is extension stable once a finite-flat middle object is
actually given.

### 4.4 The precise categorical theorem

The categorical classification established for $\mathcal S$ has four parts.

1. Its simple objects are
   $$
   C=\underline{\mathbf Z/3\mathbf Z}
   \qquad\text{and}\qquad
   M_3=\mu_3.
   $$
2. Every object $G$ has a canonical functorial sequence
   $$
   0\longrightarrow G^{\mathrm m}\longrightarrow G
   \longrightarrow G^{\mathrm c}\longrightarrow0,
   \tag{4.1}
   $$
   with multiplicative-type subobject and constant quotient.
3. The mixed extension in the reverse order vanishes, which makes (4.1) obtainable by sorting any
   composition series.
4. For a free rank-two module over a finite local coefficient ring, carrying its coefficient
   action in $\mathcal S$ and having determinant $\chi_3$, one has both a cross relation and the
   trace identity $\operatorname{tr}=1+\chi_3$.

The remainder of this book explains how these four conclusions meet the particular tower. The
classification itself already incorporates the discriminant bounds of the previous chapter and
the required ray-class calculations; it is not being assumed from a later result.

## 5. Classification of simple factors

### 5.1 Reduction to exponent three

Let $S$ be a nonzero simple object of $\mathcal S$. The closure of the generic kernel of
multiplication by $3$ is a nonzero subobject, hence all of $S$. Therefore $[3]_S=0$, and its
generic module is an irreducible $\mathbf F_3$-representation. Its faithful image $G$ cuts out an
exponent-three object and satisfies the relevant degree bound.

For the general odd-tame category the broad discriminant ceiling first gives $|G|\le33$. The
only exceptional group that survives the broad group-theoretic reduction has order $24$ and odd
inertia of order at most three; the refined ceiling then gives $|G|\le20$ and excludes it. For the
companion's own subquotients one may use the refined bound from the beginning.

### 5.2 Abelian subfields

Every abelian subfield of an exponent-three cutout field in $\mathcal S$ is either $\mathbf Q$ or

$$
K=\mathbf Q(\zeta_3).
\tag{5.1}
$$

Here is the arithmetic reason. At $2$, a tame abelian extension of $\mathbf Q_2$ has ramification
index dividing $2-1=1$, so it is unramified. At $3$, the finite-flat cutoff places every positive
upper break at most $1/2$. Hasse--Arf makes abelian upper breaks integers, hence there is no positive
break. The remaining tame inertia has order dividing $3-1=2$. The fixed field of inertia is
unramified at every finite prime and therefore trivial by Minkowski's discriminant bound. Thus the
degree is at most two; the only quadratic discriminant supported at $3$ is $-3$, giving (5.1).

Over $K$, the class number is one: its Minkowski class bound is $2\sqrt3/\pi<2$. If
$\lambda=1-\zeta_3$, the prime-to-$3$ quotient of
$(\mathcal O_K/\lambda^n)^\times$ is $\mathbf F_3^\times$, and the global unit $-1$ maps onto it.
Hence every $\lambda$-ray class group is a $3$-group. There is no hidden prime-to-three abelian
layer over $K$ supported only at $\lambda$.

### 5.3 Solvability and the commutator

The degree bound makes the faithful image solvable. Its abelianization is trivial or $C_2$ by the
preceding field calculation. In the nontrivial case put $H=[G,G]$. Ray-class exclusion shows that
$H^{\mathrm{ab}}$ has no prime divisor other than $3$. The small-order group analysis then makes
$H$ a $3$-group; the possible order-$12$ commutator would force an order-$24$ field and is excluded
by the refined degree-$20$ bound.

A normal $3$-subgroup acts trivially on a simple module in characteristic three. Indeed, a finite
$3$-group has a nonzero fixed vector: a central element of order three acts unipotently, and
induction on the group gives a common fixed vector. Normality makes the fixed space $G$-stable, so
simplicity makes it the whole module. Faithfulness therefore forces $H=1$.

Thus $G$ is trivial or $C_2$, and the simple generic representation is one-dimensional with
character $1$ or $\overline\chi_3$.

We record the small-group reduction in detail, because it is the point at which the broad and
refined discriminant estimates meet. The broad odd-tame ceiling is

$$
\operatorname{rd}(L)<2\cdot3^{3/2}.
$$

The certified explicit-formula comparison at degree $34$ makes $|G|\le33$. Every group of order
at most $33$ is solvable. One quick proof uses Sylow theory. A Sylow subgroup for the largest
prime divisor is normal except possibly at orders $12$, $24$, and $30$. At order $30$, assuming
that neither a Sylow $5$-subgroup nor a Sylow $3$-subgroup is normal would give six subgroups of
order five and ten subgroups of order three. Their nonidentity elements are disjoint, producing
$24+20>29$ nonidentity elements, an impossibility. At orders $12$ and $24$, conjugation on the
four possible Sylow $3$-subgroups maps the group into $S_4$; the image and the smaller kernel are
solvable. Induction on the order completes the proof.

If $G$ is nontrivial, solvability implies that $G^{\mathrm{ab}}$ is nontrivial. The abelian-field
lemma makes it $C_2$, so $H=[G,G]$ has index two and order at most sixteen. Suppose a prime
$r\ne3$ divides $H^{\mathrm{ab}}$. Choose a quotient $H\twoheadrightarrow C_r$. Its kernel need
not be normal in $G$, but intersecting it with its conjugate under a lift of the nontrivial element
of $G/H$ gives a normal subgroup of $G$ and a nontrivial elementary abelian $r$-extension of
$K=\mathbf Q(\zeta_3)$.

At the prime above $2$, the residue field of $K$ is $\mathbf F_4$, since $2$ is inert. A tame
abelian local ramification index divides $4-1=3$, so the $r$-extension is unramified there for
$r\ne3$. At the prime $\lambda$ above $3$, its prime-to-three quotient is at most tame. The ray
calculation of Section 5.2 has no prime-to-three quotient, a contradiction. Therefore
$H^{\mathrm{ab}}$ is a $3$-group.

If $H\ne1$, its solvability makes that abelianization nontrivial. The possible orders up to sixteen
with nontrivial $3$-primary abelianization reduce to $3,6,9,12,15$. Orders six and fifteen have an
abelianization with a nontrivial prime-to-three part. At order twelve, either a Sylow
$3$-subgroup is normal, giving a quotient of order four, or there are four Sylow
$3$-subgroups and the remaining three nonidentity elements form a normal Klein four group. The
latter case is $A_4$. It would make $|G|=24$. Every odd-order subgroup of a group of order $24$
has order at most three, so the refined cubic-inertia ceiling applies and forces $|G|\le20$, a
contradiction. Hence $H$ has order three or nine and is a $3$-group, as claimed.

Finally, the fixed-vector lemma for $3$-groups deserves its one-line induction. A nontrivial
finite $3$-group has a central element $z$ of order three. In characteristic three,

$$
(z-1)^3=z^3-1=0,
$$

so $\ker(z-1)$ is nonzero and stable under the whole group. Apply induction to the quotient by
$\langle z\rangle$. For a normal $3$-subgroup of $G$, the resulting fixed space is $G$-stable.
On a simple module it is the whole space. Faithfulness then annihilates the normal subgroup.

### 5.4 The two simple objects

It remains to identify the integral models at $3$. The order-three finite-flat classification over
$\mathbf Z_3$ has two endpoint valuation patterns. The etale endpoint is uniquely determined by
its unramified generic character and gives

$$
C=\underline{\mathbf Z/3\mathbf Z}.
$$

Cartier duality turns the other endpoint into the etale trivial object, so it is

$$
M_3=\mu_3.
$$

Their generic characters are respectively $1$ and $\overline\chi_3$, and their special fibers at
$3$ are respectively etale and connected. They are nonisomorphic and exchanged by Cartier
duality.

### 5.5 Why the discriminant argument alone is insufficient

The residual Kummer extension attached to $2$ has field
$\mathbf Q(\zeta_3,\sqrt[3]{2})$, Galois group $S_3$, and degree six. It obeys the same
root-discriminant ceiling. Its normal cubic subgroup acts trivially on every simple
characteristic-three module, so its simple factors are still $C$ and $M_3$.

This example is the permanent test case. Any argument claiming that the residual field must be
abelian, that the dyadic ramification disappears, or that the residual representation splits has
discarded a genuine object. Schoof's classification retains it and controls it through extension
theory.

## 6. Extensions and filtration rearrangement

### 6.1 The extension table

Use the convention that $\operatorname{Ext}^1(B,A)$ classifies
$0\to A\to E\to B\to0$. The calculated table is

$$
\begin{array}{c|cc}
\operatorname{Ext}^1(B,A)&B=C&B=M_3\\
\hline
A=C&\mathbf F_3[\underline{\mathbf Z/9}]&0\\
A=M_3&\mathbf F_3[E_2]&\mathbf F_3[\mu_9].
\end{array}
\tag{6.1}
$$

Same-type extensions merely build larger constant or multiplicative groups. The lower-left class
$E_2$ is the Kummer extension generated by the unit $2$. The upper-right group vanishes. This
asymmetry, rather than semisimplicity, is the engine of the filtration theorem.

We now justify every entry. Consider first an extension of $C$ by $C$. Over $\mathbf Z_3$ all
three terms are finite etale. Its generic action, after the named subgroup and quotient are fixed,
can only be a unipotent group of order three. A nontrivial action would cut out a cyclic cubic field
unramified at every odd prime and at most tamely ramified at $2$. An abelian tame extension of
$\mathbf Q_2$ is unramified, so this field would be unramified at every finite prime, contradicting
Minkowski. Thus the action is trivial. The middle abstract group is either
$\mathbf Z/3\times\mathbf Z/3$ or $\mathbf Z/9$, and Baer sum makes the second a generator of a
cyclic group of order three. Hence

$$
\operatorname{Ext}^1(C,C)\simeq\mathbf Z/3\mathbf Z.
\tag{6.2}
$$

Cartier duality exchanges $C$ and $M_3$ and reverses exact sequences. It therefore gives

$$
\operatorname{Ext}^1(M_3,M_3)\simeq\mathbf Z/3\mathbf Z,
\tag{6.3}
$$

generated by $0\to\mu_3\to\mu_9\to\mu_3\to0$.

For an extension

$$
0\longrightarrow M_3\longrightarrow E\longrightarrow C\longrightarrow0,
\tag{6.4}
$$

multiplication by three factors through a morphism $C\to M_3$. That morphism is zero on generic
characters, so $E$ is killed by three. Pulling (6.4) back along $1\in C(R)$ produces a
$\mu_3$-torsor, and the contracted third power is canonically trivial. Conversely such a torsor
reconstructs the extension. Since $\operatorname{Pic}(R)=0$, the fppf Kummer sequence gives

$$
\operatorname{Ext}^1(C,M_3)\simeq
H^1(R,\mu_3)\simeq R^\times/R^{\times3}\simeq\mathbf F_3[2].
\tag{6.5}
$$

There is no extra choice from roots of unity: $\mu_3(R)$ is trivial.

For the reverse extension

$$
0\longrightarrow C\longrightarrow E\longrightarrow M_3\longrightarrow0,
\tag{6.6}
$$

the connected--etale sequence over $\mathbf Z_3$ forces a splitting. Indeed, the connected
component $E^0$ has rank three. Its map to the connected quotient $M_3$ is nontrivial and hence
surjective; its kernel is both connected and contained in the etale subgroup $C$, so it is
trivial. Thus $E^0\to M_3$ is an isomorphism and supplies a section. The global generic class lies
in $H^1(\mathbf Q,\mathbf F_3(1))$ and is supported only at $2$ and $3$, hence is a combination
of $[2]$ and $[3]$. Local splitting at $3$ and their local independence kill both coefficients.
Therefore

$$
\operatorname{Ext}^1(M_3,C)=0.
\tag{6.7}
$$

### 6.2 The surviving Kummer class

The fppf Kummer sequence over $R=\mathbf Z[1/2]$ gives

$$
H^1(R,\mu_3)=R^\times/R^{\times3}\simeq\mathbf F_3[2].
\tag{6.8}
$$

The sign contributes nothing because $-1$ is a cube. The class of $2$ is finite flat at $3$
because $2$ is a $3$-adic unit, and it has tame cubic inertia at $2$. Hence it genuinely belongs
to $\mathcal S$.

In the reverse direction, a finite-flat extension of $M_3$ by $C$ splits over $\mathbf Z_3$ by
the connected--etale sequence. Globally its possible Kummer classes lie in the span of $[2]$ and
$[3]$. Their images in $\mathbf Q_3^\times/\mathbf Q_3^{\times3}$ are independent: $[3]$ is the
valuation direction, while $[2]=[-2]$ is a nonzero unit direction since $-2\equiv7\pmod9$ and a
cube congruent to $1$ modulo $3$ is $1$ modulo $9$. Local splitting kills both coefficients. This
proves the zero in (6.1).

### 6.3 Sorting a composition series

Suppose a composition series contains a constant factor immediately below a multiplicative factor.
The corresponding two-step quotient represents an element of
$\operatorname{Ext}^1(M_3,C)$, which is zero. It therefore splits, and the other direct factor
supplies a multiplicative subobject below the constant one. Taking saturated closures exchanges the
two adjacent factors inside the exact category.

Repeating this finite operation moves every multiplicative factor below every constant factor.
The process terminates because each exchange reduces the number of inversions in the finite word
of labels $M_3,C$.

### 6.4 The canonical multiplicative--constant filtration

The sorted filtration gives every $G\in\mathcal S$ an exact sequence

$$
0\longrightarrow G^{\mathrm m}\longrightarrow G
\longrightarrow G^{\mathrm c}\longrightarrow0,
\tag{6.3}
$$

where the lower block is of multiplicative type and the quotient is constant. Maximality makes
$G^{\mathrm m}$ canonical and functorial. In particular every coefficient endomorphism preserves
it. This last fact is what transports the categorical filtration to a coefficient-linear
submodule.

The sequence (6.3) need not split. The Kummer object $E_2$ is the basic nonsplit example. The
correct conclusion is an oriented filtration, not a product decomposition.

## 7. Finite coefficient levels

### 7.1 The coefficient action is indispensable

Fix $n$ and write $A=A_n$, $W=T_n$. The object $\mathcal G_n$ carries its $A$-action, $W$ is
free of rank two over $A$, and

$$
\det\rho_n=\chi_3\pmod{\varpi^n}.
\tag{7.1}
$$

These are precisely the hypotheses of the finite-coefficient Schoof theorem. Merely forgetting
to the underlying finite abelian group would not suffice: its rank over $\mathbf Z/3^r$ depends on
the coefficient degree and ramification, and the desired two-by-two Cayley--Hamilton identity is
an $A$-linear statement.

### 7.2 The augmentation submodule

Define

$$
N_n=\sum_{g\in G_{\mathbf Q}}(\rho_n(g)-1)T_n.
\tag{7.2}
$$

Because $T_n$ is noetherian, finitely many augmentation images generate this sum. It is stable
under $A$ and under Galois. The constant quotient in (6.3) shows that $T_n/N_n$ has trivial
action. The multiplicative block shows that Galois acts on $N_n$ through $\chi_3$.

No assertion that $N_n$ is free or a direct summand is needed. At an isolated finite level it can
have coefficient torsion. The proof deliberately avoids choosing a basis adapted to a nonexistent
free decomposition.

### 7.3 The cross relation

For all $g,h\in G_{\mathbf Q}$, the image of $\rho_n(g)-1$ lies in $N_n$, while
$\rho_n(h)$ acts on $N_n$ by $\chi_3(h)$. Hence

$$
\boxed{
(\rho_n(h)-\chi_3(h))(\rho_n(g)-1)=0.
}
\tag{7.3}
$$

This identity retains the extension structure. It is stronger than knowing the two
Jordan--Holder characters and is the exact finite-level input needed for line lifting.

### 7.4 The trace identity

Fix $g$ and put $f=\rho_n(g)$ and $d=\det f=\chi_3(g)$. Taking $h=g$ in (7.3) gives

$$
(f-d)(f-1)=0,
$$

or

$$
f^2-(1+d)f+d=0.
\tag{7.4}
$$

Cayley--Hamilton on the free rank-two $A$-module gives

$$
f^2-(\operatorname{tr}f)f+d=0.
\tag{7.5}
$$

Subtracting (7.4) from (7.5) and using that $f$ is invertible yields

$$
\boxed{
\operatorname{tr}\rho_n(g)=1+\chi_3(g)
\quad\text{in }A_n.
}
\tag{7.6}
$$

The determinant is used exactly here. Without it, multiplicative type still identifies the
cyclotomic action on $N_n$, but the scalar $d$ in Cayley--Hamilton would not be tied to that
character.

### 7.5 The residual representation

At $n=1$, $N_1$ is neither zero nor all of $M$. If it were zero, the action on $M$ would be
trivial and its determinant would be $1$, contrary to the nontrivial mod-$3$ cyclotomic
character. If it were all of $M$, every element would act as the scalar $\overline\chi_3$; the
matrix determinant would then be $\overline\chi_3^2=1$, again a contradiction at complex
conjugation.

Since $M$ has $k$-dimension two, $N_1$ is a line. Thus

$$
0\longrightarrow k(1)\longrightarrow M\longrightarrow k\longrightarrow0.
\tag{7.7}
$$

Global Kummer theory and finite flatness at $3$ restrict its class to

$$
[M]=a[2],\qquad a\in k.
\tag{7.8}
$$

The nontrivial dyadic block (1.3) forces $a\ne0$. After rescaling the cyclotomic line, $a$ may be
normalized to $1$. Hence the residual field is exactly the permitted $S_3$ field
$\mathbf Q(\zeta_3,\sqrt[3]{2})$ after the harmless scalar extension represented by $k$ is
forgotten. The conclusion is oriented reducibility, not splitting.

In a basis adapted to (7.7), the representation has the form

$$
\overline\rho(g)=
\begin{pmatrix}
\overline\chi_3(g)&c(g)\\
0&1
\end{pmatrix},
\tag{7.9}
$$

where $c$ is a $1$-cocycle with values in $k(1)$. Changing the lift of the quotient basis changes
$c$ by a coboundary; rescaling the cyclotomic basis rescales its cohomology class. Ramification
outside $\{2,3\}$ places the class in the $k$-span of $[2]$ and $[3]$. Finite flatness at three
removes the valuation class $[3]$ and retains the unit class $[2]$.

On dyadic inertia the diagonal characters in (7.9) are trivial. If $a=0$, the entire inertia
action would be trivial. If $a\ne0$, a tame generator maps to

$$
\begin{pmatrix}1&a\\0&1\end{pmatrix},
$$

which has order three. This recovers exactly the special line in (1.4). Complex conjugation maps
to a diagonalizable element with eigenvalues $-1$ and $1$, and it conjugates the cubic subgroup by
inversion. The image is therefore $C_3\rtimes C_2\simeq S_3$. The residual field calculation and
the local matrix calculation agree without forcing a split representation.

The same matrix also shows why the orientation is meaningful even though
$\overline\chi_3^{-1}=\overline\chi_3$. Reversing the extension would put the constant group below
the multiplicative group. That reverse integral extension is locally split at $3$ and globally
vanishes by (6.7). Equality of the abstract coefficient characters does not erase the connected
and etale endpoints of their finite-flat models.

## 8. Successive levels and the integral line

### 8.1 Compatibility across the tower

Reduction $T_{n+1}\twoheadrightarrow T_n$ carries $N_{n+1}$ onto $N_n$. Every generator upstairs
reduces to a generator downstairs, and every downstairs generator is the reduction of the
corresponding expression upstairs. Thus the finite-level augmentation submodules form a compatible
inverse system.

The group schemes themselves are compatible by the changing-prime input. Functoriality of the
canonical multiplicative subobject gives the same compatibility categorically. We therefore do
not choose unrelated filtrations at different levels.

### 8.2 Passage to the separated limit

Define the algebraic augmentation submodule

$$
N=\sum_{g\in G_{\mathbf Q}}(\rho(g)-1)T\subseteq T.
\tag{8.1}
$$

The noetherian property of $T$ makes $N$ finitely generated and therefore $\varpi$-adically
closed. Its image in $T_n$ is $N_n$. Consequently

$$
N\simeq\varprojlim_n N_n.
\tag{8.2}
$$

Passing (7.3) to the separated inverse limit gives

$$
\boxed{
(\rho(h)-\chi_3(h))(\rho(g)-1)=0
\qquad(g,h\in G_{\mathbf Q}).
}
\tag{8.3}
$$

Thus Galois acts trivially on $T/N$ and cyclotomically on $N$.

There are two inverse limits here, and separating them avoids a hidden completeness claim. The
first is the inverse limit of the ambient modules:

$$
T\simeq\varprojlim_n T/\varpi^nT.
$$

The second concerns the submodule generated by augmentations. Since $T$ is noetherian, finitely
many elements $g_1,\ldots,g_r$ suffice to generate

$$
N=\sum_{i=1}^r(\rho(g_i)-1)T.
$$

It is a finitely generated $\mathcal O$-module and hence complete and closed. Its reduction is

$$
N/(N\cap\varpi^nT)
=\sum_i(\rho_n(g_i)-1)T_n=N_n.
$$

Therefore no derived inverse-limit obstruction appears, and (8.2) is an ordinary completeness
statement for a closed submodule. This argument would fail for an arbitrary infinitely generated
subgroup of a topological module; noetherianity is the decisive input.

Passing the relation is now coefficientwise. For fixed $g,h$, the endomorphism

$$
D_{g,h}=(\rho(h)-\chi_3(h))(\rho(g)-1)
$$

has image contained in $\varpi^nT$ for every $n$ by (7.3). Krull intersection for the DVR gives
$\bigcap_n\varpi^nT=0$, so $D_{g,h}=0$. This proves (8.3) without choosing compatible bases or
lifting individual invariant vectors.

### 8.3 Rank, saturation, and orientation

The reduction $N_1$ is a nonzero line, so $N$ is nonzero and not contained in $\varpi T$. As a
submodule of the free $\mathcal O$-module $T$, it is torsion free. Its rank cannot be two: after
tensoring (8.3) with $E$, the entire representation would be the scalar character $\chi_3$, whose
determinant is $\chi_3^2$, not $\chi_3$.

Hence $N$ has rank one. Because it contains an element primitive in $T$, its saturation

$$
L=(N\otimes_\mathcal O E)\cap T
$$

is also rank one and primitive. Relation (8.3) shows that $L$ carries $\chi_3$: if
$\varpi^r x\in N$, torsion-freeness permits cancellation of $\varpi^r$ in the character
identity. The quotient $T/L$ is torsion free of rank one, and every augmentation difference maps
to zero there, so its character is trivial.

### 8.4 The integral reducibility theorem

We have proved the exact form of Schoof's conclusion needed here.

**Theorem 8.1 (integral Schoof conclusion).** Let $T$ be the lattice supplied by the
changing-prime theorem, with its compatible coefficient-linear finite-flat tower over
$\mathbf Z[1/2]$, primitive cubic tame inertia at $2$, and cyclotomic determinant. Then there is
a $G_{\mathbf Q}$-stable exact sequence of free $\mathcal O$-modules

$$
\boxed{
0\longrightarrow\mathcal O(1)\longrightarrow T
\longrightarrow\mathcal O\longrightarrow0.
}
\tag{8.4}
$$

For every $g\in G_{\mathbf Q}$,

$$
\boxed{
\operatorname{tr}\rho(g)=1+\chi_3(g),qquad
\det\rho(g)=\chi_3(g).
}
\tag{8.5}
$$

**Proof.** Sections 7.1--7.4 apply the finite-coefficient categorical theorem to every
$T_n$. Sections 8.1--8.3 pass its cross relation through the compatible separated tower and
construct the primitive cyclotomic line and trivial quotient. Taking traces gives (8.5), or
equivalently one may pass (7.6) to the limit. $\square$

The theorem uses only odd-tame categorical membership at $2$ together with the actual
coefficient-linear tower. It does not assume a rank-one local filtration at $2$, and it does not
claim that (8.4) splits integrally.

## 9. Semisimplification and characteristic zero

### 9.1 The character identity

Tensoring (8.4) with $E$ gives an exact sequence

$$
0\longrightarrow E(1)\longrightarrow V\longrightarrow E\longrightarrow0.
\tag{9.1}
$$

Thus the characteristic polynomial of every $g$ is

$$
X^2-(1+\chi_3(g))X+\chi_3(g)
=(X-1)(X-\chi_3(g)).
\tag{9.2}
$$

This is an identity in the coefficient field, not merely a congruence at all finite levels: the
intersection of the ideals $\varpi^n\mathcal O$ is zero.

### 9.2 Semisimplification

The two Jordan--Holder constituents of (9.1) are $E$ and $E(1)$. Therefore

$$
\boxed{
V^{\mathrm{ss}}\simeq E\oplus E(1),
\qquad
\rho^{\mathrm{ss}}\simeq1\oplus\chi_3.
}
\tag{9.3}
$$

One may also derive (9.3) from the character identity by the characteristic-zero
Brauer--Nesbitt theorem. The explicit line in (9.1) is stronger because it proves reducibility of
the actual representation, not only equality of semisimple characters.

### 9.3 What semisimplicity adds

A nonsplit extension in (9.1) is compatible with the trace and determinant identities. The
Kummer class of $2$ shows that such extensions are arithmetically real in the broader category.
Thus semisimplification $1\oplus\chi_3$ must not be rewritten as a direct sum without an
additional hypothesis.

The compatible-family member supplied previously is semisimple. Hence its extension (9.1) splits
over $E$:

$$
\boxed{V\simeq E\oplus E(1).}
\tag{9.4}
$$

No integral splitting is needed. Rational semisimplicity is exactly the hypothesis that changes
the extension into the direct sum (9.4).

### 9.4 The exact contradiction with the companion

The changing-prime theorem also says that $V$ is absolutely irreducible. Equation (9.1) already
exhibits a $G_{\mathbf Q}$-stable $E$-line, contradicting irreducibility; equation (9.4) makes the
contradiction even more explicit.

This is the precise reducibility statement required in the hardly ramified endgame:

> the particular $3$-adic companion has a cyclotomic invariant line and trivial one-dimensional
> quotient over its actual coefficient field.

Residual reducibility alone would not suffice, because an absolutely irreducible $3$-adic
representation can have reducible reduction. Equality of semisimplified residual characters would
be weaker still. The integral inverse-limit argument closes exactly that gap.

## 10. The Frey contradiction

### 10.1 The representation-theoretic form

The earlier construction begins from the hypothetical Frey data, produces the balanced hardly
ramified lift, embeds it in a compatible family, and changes coefficient prime to obtain the
companion of Section 1.2. That companion is absolutely irreducible. Theorem 8.1 makes it reducible.
Therefore the hypothetical Frey data cannot exist.

This formulation uses the irreducibility retained by the compatible-family construction. It does
not need a classification of elliptic curves, a field table, or a conditional discriminant bound.

### 10.2 The Frobenius-trace form

There is a second contradiction that uses only the common Frobenius polynomials and purity. At
every $p\ne2,3$, equations (8.5) and the compatible-family identity give

$$
a_p=1+p.
\tag{10.1}
$$

Indeed, the equality first holds in the completion $E_\nu$, and the embedding of the common
algebraic coefficient field into that completion is injective. Purity says that the two complex
roots of $X^2-a_pX+p$ have absolute value $\sqrt p$, so

$$
|a_p|\le2\sqrt p.
\tag{10.2}
$$

But for every prime $p>1$,

$$
1+p>2\sqrt p,
$$

because $(\sqrt p-1)^2>0$. Thus any good prime gives a contradiction.

### 10.3 Why $p=5$ suffices

The companion is unramified outside $\{2,3\}$, so $p=5$ is good. Equations (10.1)--(10.2)
become

$$
a_5=6,qquad |a_5|\le2\sqrt5,
$$

and

$$
6>2\sqrt5.
$$

This numerical endpoint is useful because it exposes any loss of unramifiedness in the
prime-switching step. The old coefficient prime and all auxiliary primes were removed by the
strict local compatibility theorem; otherwise one would have to choose another verified good
prime.

### 10.4 The precise endpoint

**Theorem 10.1 (hardly ramified $3$-adic classification in the FLT scope).** Let $V$, $T$, and
$\{\mathcal G_n\}$ be the companion package of Section 1.2, with the actual primitive cubic tame
type of Section 1.3. Then

$$
0\longrightarrow\mathcal O(1)\longrightarrow T
\longrightarrow\mathcal O\longrightarrow0,
$$

$$
V^{\mathrm{ss}}\simeq E(1)\oplus E,
$$

and the residual extension is the nonzero $2$-Kummer class

$$
0\longrightarrow k(1)\longrightarrow T/\varpi T
\longrightarrow k\longrightarrow0.
$$

In particular $V$ is reducible. Since the companion construction makes $V$ semisimple and
absolutely irreducible, no such companion exists. Equivalently, its pure compatible family would
have $a_5=6>2\sqrt5$. Hence the Frey input from which the companion was constructed is impossible.

**Proof.** Chapters 2--3 place every exponent-three devissage object under the exact
two-prime discriminant ceiling and unconditional degree cutoff. Chapters 4--6 invoke the global
finite-flat classification, whose hypotheses are verified by the glued tower. Chapter 7 gives
the finite-level cross relation and residual orientation. Chapter 8 passes compatibly to the
integral cyclotomic line. Chapter 9 gives semisimplification and reducibility, and Sections
10.1--10.3 give the two contradictions. $\square$

## 11. Hostile mathematical audit

### 11.1 Local-type audit

The dyadic type used in this book is

$$
P_2\text{ trivial},qquad N=0,qquad I_2\twoheadrightarrow C_3,
$$

with primitive cubic characteristic-zero eigencharacters exchanged by Frobenius. It is not
Steinberg and does not arise from a free rank-one Tate sequence. Only the first residual level has
the special line $\ker(A-1)=\operatorname{im}(A-1)$. Every application above uses either the
actual $C_3$ action or membership in the broader odd-tame category. No stronger local filtration
has been inserted.

### 11.2 Discriminant audit

At $3$, $1/2$ is an upper-break cutoff and $3/2$ is a normalized different exponent; they are not
the same invariant. At $2$, the exact tame exponent is $2/3$. The global ceiling is paid once:

$$
3^{3/2}2^{2/3},
$$

with no dimension factor and no factor for the number of primes. The degree-$20$ conclusion is
unconditional and follows from the certified degree-$21$ lower bound. It is applied only to
objects killed by $3$ and their finite products, never to the full $\varpi^n$-torsion field.

### 11.3 Coefficient audit

The residue field is allowed to be $\mathbf F_{3^f}$ and the coefficient field may be ramified.
The quotient $T/\varpi^nT$ is killed by $3^{\lceil n/e_E\rceil}$, not by $3^n$ in general. The
finite-coefficient theorem is applied over the actual ring $A_n=\mathcal O/\varpi^n$, using the
coefficient action furnished by the compatible models. No reduction to a rank-two
$\mathbf Z_3$-lattice is made.

### 11.4 Filtration audit

Subobjects and quotients inherit models only by closure inside a supplied ambient group. The
mixed reverse extension vanishes, but the forward Kummer extension $E_2$ survives. Therefore the
canonical sequence has multiplicative subobject and constant quotient and need not split. Its
functoriality, not arbitrary choices of composition series, makes the finite-level augmentation
submodules compatible.

### 11.5 Reducibility audit

The proof does not jump from residual semisimplification to characteristic-zero reducibility.
It establishes the cross relation modulo every $\varpi^n$, passes it through a separated inverse
limit, saturates the resulting rank-one augmentation submodule, and obtains the actual exact
sequence (8.4). Semisimplicity is invoked only afterward to split the rational extension. Absolute
irreducibility and purity then provide independent contradictions.

All dependency boundaries now align:

- the changing-prime theorem supplies precisely the global tower and primitive cubic local type;
- the discriminant books supply the residual ceiling, the growing higher-level warning, and the
  unconditional cutoff;
- the finite-flat category supplies simple factors, extension asymmetry, filtration, and the
  finite-coefficient cross relation;
- this book supplies the compatible inverse-limit passage and the exact FLT contradiction.

Several nearby statements fail and serve as final diagnostics. If only $M^{\mathrm{ss}}$ were
known, the off-diagonal Kummer cocycle could still cut out the cubic field and no higher line would
follow. If finite-flat models existed at each level but carried no compatible coefficient action,
the rank-two Cayley--Hamilton comparison over $A_n$ would be unavailable. If the models existed
only after a ramified extension of $\mathbf Q_3$, neither the root-discriminant constant over
$\mathbf Q_3$ nor the global Hopf-order gluing would follow. If one additional odd prime were
ramified, its local different factor and its new global Kummer generator would enlarge both the
analytic and extension ledgers.

Likewise, replacing the primitive cubic type by conductor exponent two would lose essential
information. A Steinberg representation can have the same conductor exponent but nonzero
monodromy and a rank-one invariant space in characteristic zero. The present representation has
zero monodromy and no inertia invariants in characteristic zero. Their reductions and torsion
fields behave differently. The proof is stable under the exact type, not under the conductor
integer alone.

Finally, dropping semisimplicity does not invalidate Theorem 8.1. It leaves a possibly nonsplit
extension of the trivial character by the cyclotomic character. Dropping purity also leaves the
integral reducibility conclusion intact. What changes is only the last contradiction. In the FLT
companion both semisimplicity, absolute irreducibility, and purity are already present, so two
independent endpoints are available.

## 12. Conclusion

The hardly ramified representation is trapped by an interaction of local geometry, global
arithmetic, and exact structure. Finite flatness at $3$ limits residual wild depth. Primitive
cubic tame inertia at $2$ contributes the exact factor $2^{2/3}$. The resulting root-discriminant
ceiling forces every relevant exponent-three field into degree at most twenty, but it deliberately
leaves the genuine $S_3$ Kummer field alive.

The global category over $\mathbf Z[1/2]$ explains what the discriminant estimate cannot. Its only
simple objects are the constant group of order three and $\mu_3$. Its asymmetric mixed extension
groups sort every composition series into a multiplicative subobject and constant quotient. With
the actual coefficient action retained, that filtration gives the cross relation at every finite
coefficient level.

Separated passage through the compatible tower converts those finite relations into a primitive
$\mathcal O(1)$-line in the lattice. Thus the characteristic-zero representation is reducible and
has semisimplification $1\oplus\chi_3$. For the semisimple companion it is the direct sum itself,
contradicting absolute irreducibility. At good Frobenius elements the same conclusion says
$a_p=1+p$, contradicting purity already at $p=5$.

That is Schoof's classification in the exact scope required by the Frey endgame. The residual
extension, successive torsion levels, discriminant constants, global finite-flat filtration,
coefficient field, and integral line all remain visible. No stronger dyadic hypothesis, uniform
full-tower discriminant bound, residual splitting assertion, or conditional analytic input is
used.
