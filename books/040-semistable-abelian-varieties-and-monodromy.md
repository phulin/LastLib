# Semistable Abelian Varieties and Monodromy

## Contents

1. [Degeneration seen by inertia](#1-degeneration-seen-by-inertia)
   - [The problem](#11-the-problem)
   - [Standing conventions](#12-standing-conventions)
   - [The three prerequisite interfaces](#13-the-three-prerequisite-interfaces)
   - [The shape of the answer](#14-the-shape-of-the-answer)
2. [The toric and abelian parts](#2-the-toric-and-abelian-parts)
   - [The connected special fiber](#21-the-connected-special-fiber)
   - [Characters and cocharacters](#22-characters-and-cocharacters)
   - [The two lattices supplied by duality](#23-the-two-lattices-supplied-by-duality)
   - [Products, isogenies, and scalar extension](#24-products-isogenies-and-scalar-extension)
3. [One-motives in the semistable range](#3-one-motives-in-the-semistable-range)
   - [Why a two-term object is necessary](#31-why-a-two-term-object-is-necessary)
   - [Torsion and Tate realization](#32-torsion-and-tate-realization)
   - [The weight filtration](#33-the-weight-filtration)
   - [Dual one-motives and their pairing](#34-dual-one-motives-and-their-pairing)
   - [The Raynaud one-motive](#35-the-raynaud-one-motive)
4. [Inertia invariants and the special fiber](#4-inertia-invariants-and-the-special-fiber)
   - [Reduction over the strict henselization](#41-reduction-over-the-strict-henselization)
   - [The fixed-part theorem](#42-the-fixed-part-theorem)
   - [The rank of the invariant submodule](#43-the-rank-of-the-invariant-submodule)
   - [What the formula does and does not say](#44-what-the-formula-does-and-does-not-say)
5. [Tame Kummer theory of periods](#5-tame-kummer-theory-of-periods)
   - [The tame character](#51-the-tame-character)
   - [The valuation Kummer lemma](#52-the-valuation-kummer-lemma)
   - [Tropicalization of the period lattice](#53-tropicalization-of-the-period-lattice)
   - [The inertial action formula](#54-the-inertial-action-formula)
6. [The monodromy operator](#6-the-monodromy-operator)
   - [A canonical operator with a twist](#61-a-canonical-operator-with-a-twist)
   - [Nilpotence and the monodromy filtration](#62-nilpotence-and-the-monodromy-filtration)
   - [Rank and the invariant subspace](#63-rank-and-the-invariant-subspace)
   - [Polarizations and adjointness](#64-polarizations-and-adjointness)
   - [Ramified base change](#65-ramified-base-change)
7. [The integral monodromy pairing](#7-the-integral-monodromy-pairing)
   - [The pairing between the two toric lattices](#71-the-pairing-between-the-two-toric-lattices)
   - [Construction from the Poincare biextension](#72-construction-from-the-poincare-biextension)
   - [Nondegeneracy and positivity](#73-nondegeneracy-and-positivity)
   - [Functoriality and duality](#74-functoriality-and-duality)
8. [Component groups as monodromy discriminants](#8-component-groups-as-monodromy-discriminants)
   - [The tropical component map](#81-the-tropical-component-map)
   - [The component exact sequences](#82-the-component-exact-sequences)
   - [The Grothendieck component pairing](#83-the-grothendieck-component-pairing)
   - [Polarized and principally polarized cases](#84-polarized-and-principally-polarized-cases)
   - [Semistable Jacobians](#85-semistable-jacobians)
9. [Potential semistable reduction](#9-potential-semistable-reduction)
   - [Semistability under isogeny](#91-semistability-under-isogeny)
   - [Producing a Jacobian cover](#92-producing-a-jacobian-cover)
   - [The semistable reduction theorem](#93-the-semistable-reduction-theorem)
   - [How much extension is being asserted](#94-how-much-extension-is-being-asserted)
10. [Galois criteria for reduction](#10-galois-criteria-for-reduction)
    - [The semistable reduction criterion](#101-the-semistable-reduction-criterion)
    - [The good reduction criterion](#102-the-good-reduction-criterion)
    - [Finite-level tests](#103-finite-level-tests)
    - [Independence of the auxiliary prime](#104-independence-of-the-auxiliary-prime)
11. [Quasi-unipotence](#11-quasi-unipotence)
    - [The theorem](#111-the-theorem)
    - [Finite descent and unipotent motion](#112-finite-descent-and-unipotent-motion)
    - [The sharp nilpotence bound](#113-the-sharp-nilpotence-bound)
    - [The Weil-Deligne form when the residue field is finite](#114-the-weil-deligne-form-when-the-residue-field-is-finite)
12. [Conductors of abelian varieties](#12-conductors-of-abelian-varieties)
    - [Artin and Swan conductors for a quasi-unipotent representation](#121-artin-and-swan-conductors-for-a-quasi-unipotent-representation)
    - [The tame codimension](#122-the-tame-codimension)
    - [The conductor formula](#123-the-conductor-formula)
    - [The semistable formula](#124-the-semistable-formula)
    - [Independence, additivity, and isogeny](#125-independence-additivity-and-isogeny)
13. [Exact examples](#13-exact-examples)
    - [Good reduction](#131-good-reduction)
    - [The Tate curve](#132-the-tate-curve)
    - [Nonsplit multiplicative reduction and products](#133-nonsplit-multiplicative-reduction-and-products)
    - [Jacobians and weighted graphs](#134-jacobians-and-weighted-graphs)
    - [Additive reduction](#135-additive-reduction)
14. [Functoriality and hypothesis control](#14-functoriality-and-hypothesis-control)
    - [Morphisms and monodromy](#141-morphisms-and-monodromy)
    - [Duality and component groups](#142-duality-and-component-groups)
    - [Base-change bookkeeping](#143-base-change-bookkeeping)
    - [A hypothesis ledger](#144-a-hypothesis-ledger)
15. [The monodromy package](#15-the-monodromy-package)
    - [The structural dictionary](#151-the-structural-dictionary)
    - [A calculation protocol](#152-a-calculation-protocol)
    - [Conclusion](#153-conclusion)

## 1. Degeneration seen by inertia

This opening chapter fixes the local conventions and identifies the bridge the rest of the book must construct. The central point is that a special-fiber torus, a valuation pairing on periods, and a unipotent inertial matrix are not parallel analogies: they are successive realizations of one integral map.

### 1.1 The problem

An abelian variety over a complete discretely valued field has two apparently different kinds of boundary data. Its Neron model has a special fiber, whose identity component may contain an abelian variety, a torus, and a unipotent group. Its prime-to-residue-characteristic Tate module has a continuous Galois action, whose restriction to inertia may be trivial, unipotent, or only quasi-unipotent. The aim of this book is to prove that these are two descriptions of the same degeneration.

The first nontrivial example already contains the entire mechanism. If $E$ is a Tate elliptic curve with parameter $q$, then

$$
E^{\mathrm{an}}\simeq \mathbf G_m^{\mathrm{an}}/q^{\mathbf Z}.
$$

Taking an $\ell^n$th root of a point means taking an $\ell^n$th root of a multiplicative coordinate and, when necessary, an $\ell^n$th root of the period $q$. Inertia fixes the roots of units after unramified extension, but it does not fix a root of an element of positive valuation. It therefore shears one rank-one part of $T_\ell E$ along another. In a suitable basis the action is

$$
\rho_\ell(\sigma)=
\begin{pmatrix}
1&v(q)t_\ell(\sigma)\\
0&1
\end{pmatrix}.
$$

The integer $v(q)$ is at once a period length, an entry of the monodromy pairing, and the order of the geometric component group. The matrix has square-zero logarithm, while the codimension of its invariant subspace is the toric rank, namely one.

The general theory preserves this picture but replaces the two copies of $\mathbf Z$ by two lattices, the multiplicative group by a torus, and the bounded part by an abelian variety with good reduction. A two-term object called a one-motive keeps all three layers together. Its Tate realization carries a weight filtration; the valuation of its periods gives a monodromy operator; and the same integral map presents the component group.

### 1.2 Standing conventions

Unless a statement says otherwise, $K$ is a complete discretely valued field with valuation ring $R$, maximal ideal $\mathfrak m$, residue field $k$ of characteristic exponent $p$, and normalized valuation

$$
v_K:K^\times\longrightarrow\mathbf Z.
$$

We fix a separable closure $K^s$, write $G_K=\operatorname{Gal}(K^s/K)$, and let $I_K\subseteq G_K$ be inertia. The maximal unramified extension inside $K^s$ is $K^{\mathrm{nr}}$, and its completion is denoted $\widehat K^{\mathrm{nr}}$. A prime $\ell$ is always different from $p$. We write

$$
T_\ell A=\varprojlim_n A[\ell^n](K^s),
\qquad V_\ell A=T_\ell A\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

For a torus $T$,

$$
X=X^*(T)=\operatorname{Hom}(T,\mathbf G_m),
\qquad X_*(T)=\operatorname{Hom}(\mathbf G_m,T)=X^\vee.
$$

All lattices are finite free abelian groups. The Tate twist is normalized by

$$
T_\ell\mathbf G_m=\mathbf Z_\ell(1).
$$

A bilinear valuation pairing takes values in $\mathbf Z$ only after a normalized discrete valuation has been chosen. Replacing $K$ by a ramified extension of index $e$ multiplies that integral pairing by $e$. The associated real pairing defined using a fixed absolute value does not change. This distinction will be kept visible.

Let $A/K$ be an abelian variety of dimension $g$, with Neron model $\mathcal A/R$. Over a perfect residue field its connected special fiber has canonical exact sequences

$$
0\longrightarrow L\longrightarrow\mathcal A_k^0
\longrightarrow B\longrightarrow0,
\qquad
0\longrightarrow U\longrightarrow L\longrightarrow T\longrightarrow0.
\tag{1.1}
$$

We put

$$
a=\dim B,\qquad t=\dim T,\qquad u=\dim U,
\qquad g=a+t+u.
\tag{1.2}
$$

When $k$ is imperfect, $B$ and the maximal smooth connected affine subgroup still exist, but the split description of the unipotent radical may require purely inseparable extension. Every result below that uses (1.1) only through dimensions remains valid after geometric base change. Statements requiring a torus over $R$ or classical ramification groups will carry their separability hypotheses explicitly.

### 1.3 The three prerequisite interfaces

Three earlier theories enter, and it is important to say exactly what each supplies.

First, ramification theory supplies lower and upper ramification groups, the tame character, and Artin and Swan conductors for finite inertial actions. Upper numbering is compatible with quotients, so a finite wild image has an intrinsic Swan conductor. We will extend the definition to the quasi-unipotent $\ell$-adic representations occurring here by observing that wild inertia has finite image.

Second, rigid uniformization supplies, for a semistable abelian variety, exact sequences

$$
0\longrightarrow T^{\mathrm{an}}\longrightarrow E
\longrightarrow B^{\mathrm{an}}\longrightarrow0,
\qquad
0\longrightarrow Y\xrightarrow{u}E
\longrightarrow A^{\mathrm{an}}\longrightarrow0.
\tag{1.3}
$$

Here $B$ has good reduction, $T$ is a torus of rank $t$, and $Y$ is a full period lattice of rank $t$. The positivity theory of the period data supplies algebraization, duality, and polarizations. In particular, the rank equality in (1.3) and nondegeneracy of tropicalization have already been proved; they will not be inferred from the component formula that we later deduce from them.

Third, Neron models supply the canonical smooth integral group, its identity component, its finite etale component group $\Phi_A$, and functorial extension of homomorphisms. For Jacobians, the prior graph theorem identifies the torus with graph homology and the component group with a weighted graph discriminant. The present book proves the corresponding lattice presentation for every semistable abelian variety.

We also use ordinary facts about abelian varieties already available in the preceding geometric foundation: duality and the Poincare bundle, Weil pairings, polarizations, quotients by finite subgroup schemes, Poincare complete reducibility, Bertini for sufficiently ample linear systems, and semistable reduction of proper smooth curves after finite separable extension. Whenever one of these facts bears the weight of a central argument, the needed form is restated and its application is proved.

### 1.4 The shape of the answer

For semistable $A$, the representation $T_\ell A$ has a three-step filtration

$$
0\subset W_{-2}\subset W_{-1}\subset W_0=T_\ell A
\tag{1.4}
$$

with graded pieces

$$
\operatorname{Gr}_{-2}=X_*(T)\otimes\mathbf Z_\ell(1),
\quad
\operatorname{Gr}_{-1}=T_\ell B,
\quad
\operatorname{Gr}_0=Y\otimes\mathbf Z_\ell.
\tag{1.5}
$$

Inertia acts trivially on the graded pieces over the maximal unramified field. All motion is an extension between weights $0$ and $-2$. It is measured by

$$
N:T_\ell A\longrightarrow T_\ell A(-1),
\qquad N^2=0,
\tag{1.6}
$$

and the action is

$$
\rho_\ell(\sigma)=1+t_\ell(\sigma)N.
\tag{1.7}
$$

The operator factors through $Y\otimes\mathbf Z_\ell$ and lands in $X_*(T)\otimes\mathbf Z_\ell$. Its integral source is the monodromy homomorphism

$$
Y\longrightarrow X_*(T),
\tag{1.8}
$$

or, in dual form, the pairing between the character lattices of the toric parts of $A$ and $A^\vee$. Its cokernel is $\Phi_A(k^s)$. These statements will be proved in that order: the period map first, the Galois formula second, and the component presentation third.

For arbitrary $A$, potential semistable reduction makes inertia quasi-unipotent. The connected special fiber gives

$$
\dim_{\mathbf Q_\ell}(V_\ell A)^{I_K}=2a+t,
\tag{1.9}
$$

and hence the conductor formula

$$
f_K(A)=t+2u+\operatorname{Sw}_K(V_\ell A).
\tag{1.10}
$$

For semistable reduction, $u=0$ and wild inertia is trivial, so $f_K(A)=t$. Formula (1.10) is the numerical synthesis of the book; the chapters before it establish every term geometrically.

## 2. The toric and abelian parts

Monodromy begins with the connected special fiber. We first separate its proper, multiplicative, and additive directions, then introduce the character lattices on which the integral theory lives. This geometric bookkeeping prevents later representation formulas from hiding a residue-field action or confusing a lattice with its dual.

### 2.1 The connected special fiber

The Neron model is not proper at bad reduction, and that failure of properness has structure. Assume first that $k$ is perfect. Chevalley's theorem applied to the smooth connected group $\mathcal A_k^0$ gives (1.1). Because the group is commutative, its connected affine part is an extension of a torus by a smooth connected unipotent group.

The three dimensions in (1.2) are intrinsic. The abelian part $B$ is the maximal proper quotient. The torus $T$ is the maximal multiplicative quotient of the affine part. The unipotent group $U$ is the obstruction to semistability. Thus

$$
A\text{ has semistable reduction}
\quad\Longleftrightarrow\quad u=0.
\tag{2.1}
$$

Good reduction is stronger: it requires $t=u=0$ and a trivial component group, equivalently that the entire Neron model be an abelian scheme. A connected multiplicative special fiber can have trivial component group, so neither $\Phi_A=0$ nor $u=0$ alone implies good reduction.

When $A$ is semistable, the special-fiber sequence

$$
0\longrightarrow T\longrightarrow\mathcal A_k^0
\longrightarrow B\longrightarrow0
\tag{2.2}
$$

is the reduction of the formal Raynaud extension in (1.3). The good-reduction abelian variety occurring in uniformization lifts $B$, and the generic torus is the unramified lift of $T$. This is why inertia acts trivially on their prime-to-$p$ Tate modules: after passage to $R^{\mathrm{sh}}$, both extend as smooth groups and all prime-to-$p$ torsion is etale over the base.

### 2.2 Characters and cocharacters

After passing to $k^s$, the torus in (2.2) is split. Put

$$
X_A=X^*(T_A),
\qquad X_A^\vee=X_*(T_A).
\tag{2.3}
$$

The residue Galois group acts on both lattices, contravariantly on characters and covariantly on cocharacters. Inertia acts trivially because the torus extends over the strict henselization; Frobenius or a more general residue Galois element need not act trivially. A nonsplit multiplicative elliptic curve illustrates the distinction: inertia sees the same unipotent shear as in the split case, while residue Frobenius acts by $-1$ on the rank-one character lattice.

For every $\ell\ne p$,

$$
T_\ell T_A=X_A^\vee\otimes\mathbf Z_\ell(1).
\tag{2.4}
$$

Indeed, after splitting $T_A\simeq\mathbf G_m^t$, this is the product of $t$ copies of $T_\ell\mathbf G_m$. The identification is independent of the splitting because a change of torus coordinates acts dually on characters and cocharacters.

If $A$ is semistable, the period lattice $Y_A$ in (1.3) is another rank-$t$ lattice. Tropicalization sends a period $y$ to the homomorphism

$$
\nu_A(y):X_A\longrightarrow\mathbf Z,
\qquad x\longmapsto v_K\bigl(x(u(y))\bigr),
\tag{2.5}
$$

in the pure toric case. For a general Raynaud extension the character evaluation is replaced by the normalized Poincare trivialization, but its valuation gives the same map to $X_A^\vee$. Fullness of the period lattice says

$$
\nu_A:Y_A\hookrightarrow X_A^\vee
\quad\text{has finite cokernel.}
\tag{2.6}
$$

This is stronger than equality of ranks and weaker than unimodularity. The finite cokernel is precisely where components will appear.

### 2.3 The two lattices supplied by duality

Dual uniformization exchanges characters and periods. If $A^\vee$ is the dual abelian variety, then

$$
Y_A\simeq X_{A^\vee},
\qquad
Y_{A^\vee}\simeq X_A.
\tag{2.7}
$$

These identifications arise from the Poincare biextension, not from a choice of polarization. A polarization supplies maps between the two sides; a principal polarization makes them isomorphic. Without a polarization there is no canonical identification $X_A\simeq Y_A$.

It is useful to rename

$$
Y=X_{A^\vee},\qquad X=X_A.
$$

The tropical map (2.6) is then adjoint to an integral bilinear pairing

$$
\mu_A:Y\times X\longrightarrow\mathbf Z,
\qquad
\mu_A(y,x)=\nu_A(y)(x).
\tag{2.8}
$$

Duality transposes it:

$$
\mu_{A^\vee}(x,y)=\mu_A(y,x).
\tag{2.9}
$$

Neither pairing is asserted symmetric. If $\lambda:A\to A^\vee$ is a polarization, its map on toric character lattices turns (2.8) into a symmetric positive-definite form on the appropriate period lattice. This is the integral shadow of the positive period form used in uniformization.

### 2.4 Products, isogenies, and scalar extension

Products behave componentwise:

$$
X_{A_1\times A_2}=X_{A_1}\oplus X_{A_2},
\quad
Y_{A_1\times A_2}=Y_{A_1}\oplus Y_{A_2},
\quad
\mu_{A_1\times A_2}=\mu_{A_1}\perp\mu_{A_2}.
\tag{2.10}
$$

An isogeny between semistable abelian varieties induces finite-index maps on both lattices and an isogeny on the good-reduction parts. Hence toric and abelian ranks are isogeny invariants. Integral discriminants and component groups need not be: changing either lattice by finite index changes the cokernel of the monodromy map.

Let $L/K$ have ramification index $e$. If $A$ is already semistable, its toric and abelian ranks do not change over $L$. With normalized integral valuations,

$$
\mu_{A_L}=e\mu_A.
\tag{2.11}
$$

Under an unramified extension $e=1$, only the residue Galois action changes. Under a ramified extension, the same geometric periods receive $e$ times their old integral length. Formula (2.11) will explain both the scaling of the monodromy operator and the growth of component groups.

## 3. One-motives in the semistable range

Uniformization contains a semiabelian group and a discrete period lattice, while the Tate module of the proper quotient remembers both. A one-motive is the smallest object that holds these two layers together. This chapter develops exactly the torsion, filtration, and duality needed here, so later monodromy calculations have a precise source rather than an ad hoc matrix model.

### 3.1 Why a two-term object is necessary

The analytic covering group $E$ in (1.3) is not proper, while the quotient kernel $Y$ is infinite and discrete. Neither alone has the correct torsion rank. Their two-term combination does.

A **one-motive in the semistable range** over a field $F$ is a complex

$$
M=[Y\xrightarrow{u}G]
\tag{3.1}
$$

in degrees $-1$ and $0$, where $Y$ is a lattice with continuous Galois action through a finite quotient and $G$ is a semiabelian variety fitting into

$$
0\longrightarrow T\longrightarrow G\longrightarrow B\longrightarrow0.
\tag{3.2}
$$

Here $T$ is a torus and $B$ is an abelian variety. We need only this two-term category, its torsion, duality, and realizations. No claim about a larger derived theory is required.

A morphism $[Y_1\to G_1]\to[Y_2\to G_2]$ is a pair of homomorphisms commuting with the two structure maps. Exactness below is exactness of fppf sheaves. This convention matters because torsion group schemes can be nonreduced when their order is not invertible, although our Tate realizations use only $\ell\ne p$.

### 3.2 Torsion and Tate realization

For a positive integer $n$, define $M[n]$ as follows. Its sections are equivalence classes of pairs $(y,g)$ satisfying

$$
y\in Y,\qquad g\in G,\qquad ng=u(y),
\tag{3.3}
$$

where

$$
(y,g)\sim(y+nz,g+u(z))
\qquad(z\in Y).
\tag{3.4}
$$

The projection to the class of $y$ gives an exact sequence

$$
0\longrightarrow G[n]\longrightarrow M[n]
\longrightarrow Y/nY\longrightarrow0.
\tag{3.5}
$$

To prove exactness, a class maps to zero precisely when $y=nz$; subtracting $(nz,u(z))$ gives a representative $(0,g-u(z))$ killed by $n$. Conversely every $n$-torsion point of $G$ gives $(0,g)$. Surjectivity is local for the fppf topology because multiplication by $n$ on a semiabelian variety is faithfully flat, so an $n$th root of $u(y)$ exists locally.

For $\ell$ invertible in $F$, the transition map $M[\ell^{n+1}]\to M[\ell^n]$ sends a class represented by $(y,g)$ to the class of $(y,\ell g)$ after reducing $y$ modulo $\ell^n$. Passing to inverse limits gives

$$
T_\ell M=\varprojlim_n M[\ell^n](F^s)
\tag{3.6}
$$

and an exact sequence of free $\mathbf Z_\ell$-modules

$$
0\longrightarrow T_\ell G\longrightarrow T_\ell M
\longrightarrow Y\otimes\mathbf Z_\ell\longrightarrow0.
\tag{3.7}
$$

Exactness on the right follows by choosing compatible roots successively. The obstruction at each stage lies in $G[\ell^n]$ and can be corrected because the transition maps on the Tate module are surjective. Freeness follows from (3.7) and the familiar freeness of the Tate modules of tori and abelian varieties.

Applying $T_\ell$ to (3.2) gives

$$
0\longrightarrow X_*(T)\otimes\mathbf Z_\ell(1)
\longrightarrow T_\ell G\longrightarrow T_\ell B
\longrightarrow0.
\tag{3.8}
$$

The ranks are therefore

$$
\operatorname{rank}T_\ell M
=\operatorname{rank}Y+\operatorname{rank}T+2\dim B.
\tag{3.9}
$$

For a Raynaud motive, the two lattice ranks are equal to $t$, so (3.9) is $2t+2\dim B=2\dim A$, as required.

### 3.3 The weight filtration

The two exact sequences define an increasing filtration

$$
0\subset W_{-2}\subset W_{-1}\subset W_0=T_\ell M,
\tag{3.10}
$$

where

$$
W_{-2}=T_\ell T,\qquad W_{-1}=T_\ell G.
$$

Its graded pieces are

$$
\operatorname{Gr}_{-2}=X_*(T)\otimes\mathbf Z_\ell(1),
\quad
\operatorname{Gr}_{-1}=T_\ell B,
\quad
\operatorname{Gr}_0=Y\otimes\mathbf Z_\ell.
\tag{3.11}
$$

The indices describe how far each layer is from proper abelian geometry. The torus contributes weight $-2$, the abelian variety weight $-1$, and the period lattice weight $0$. The numbering is not an assertion about Frobenius eigenvalues over an arbitrary residue field; it is the filtration compatible with duality and monodromy.

Every morphism of one-motives preserves (3.10). Strictness after tensoring with $\mathbf Q_\ell$ follows directly: the image of a torus is a torus, the induced map on abelian quotients is a homomorphism of abelian varieties, and the lattice map controls the top quotient. Integral strictness can fail by finite index, which is exactly why component groups are sensitive to isogeny.

### 3.4 Dual one-motives and their pairing

Let $M=[Y\to G]$ with torus character lattice $X$. Its dual has the form

$$
M^\vee=[X\longrightarrow G^\vee],
\tag{3.12}
$$

where $G^\vee$ is an extension of $B^\vee$ by the torus with character lattice $Y$. The construction is forced by the Poincare biextension. The extension $G$ is classified character by character by a map $X\to B^\vee$; the points $u(Y)$ project to $B$, and the Poincare bundle pairs those two maps. Transposing the biextension interchanges $X$ and $Y$ and constructs $G^\vee$ together with its map from $X$.

At level $n$ the biextension commutator gives a pairing

$$
M[n]\times M^\vee[n]\longrightarrow\mu_n.
\tag{3.13}
$$

It is perfect. One proof filters both sides by (3.5) and (3.8). On the abelian graded piece it is the perfect Weil pairing $B[n]\times B^\vee[n]\to\mu_n$. On the toric and lattice pieces it is evaluation

$$
(X_*(T)\otimes\mu_n)\times X/nX\longrightarrow\mu_n,
\qquad
(Y/nY)\times(Y^\vee\otimes\mu_n)\longrightarrow\mu_n.
$$

The annihilator of each filtration step is the complementary step on the other side. Perfectness on the graded pieces and a diagram chase prove perfectness of (3.13). Passing to inverse limits gives

$$
T_\ell M\times T_\ell M^\vee
\longrightarrow\mathbf Z_\ell(1),
\tag{3.14}
$$

again perfect and Galois equivariant.

A polarization $M\to M^\vee$ makes (3.14) alternating on the corresponding Tate module. Its restrictions pair weights $0$ and $-2$, while the abelian weight $-1$ piece receives the ordinary polarized Weil pairing. This orthogonality is the linear reason the monodromy operator lowers weight by two.

### 3.5 The Raynaud one-motive

Let $A/K$ have semistable reduction and Raynaud uniformization (1.3). Its **Raynaud one-motive** is

$$
M_A=[Y_A\xrightarrow{u}E].
\tag{3.15}
$$

Although $E$ is initially presented analytically, its prime-to-$p$ torsion and all finite root constructions are represented by the algebraic or formal semiabelian extension from which $E$ arises. Thus the preceding torsion construction applies.

There is a canonical isomorphism

$$
T_\ell M_A\xrightarrow{\sim}T_\ell A.
\tag{3.16}
$$

At finite level, the uniformization exact sequence and multiplication by $\ell^n$ give

$$
0\longrightarrow E[\ell^n]\longrightarrow A[\ell^n]
\longrightarrow Y_A/\ell^nY_A\longrightarrow0.
\tag{3.17}
$$

A point of $A[\ell^n]$ lifts to $g\in E$ with $\ell^ng=u(y)$ for some $y\in Y_A$; changing the lift by a period produces exactly relation (3.4). Hence (3.17) identifies $A[\ell^n]$ with $M_A[\ell^n]$, compatibly in $n$, proving (3.16).

Consequently (3.10) becomes the filtration (1.4)-(1.5). This is the precise sense in which a semistable abelian variety is represented, for prime-to-$p$ monodromy, by a one-motive.

## 4. Inertia invariants and the special fiber

Before assuming semistability, one can already determine the vectors fixed by inertia. The Neron mapping property turns unramified torsion points into sections, and smooth reduction identifies their compatible systems with torsion in the connected special fiber. The resulting fixed-part theorem is the geometric input for the general conductor formula.

### 4.1 Reduction over the strict henselization

Before using uniformization, we prove a statement valid for every reduction type. Replace $R$ by its strict henselization. Its residue field is separably closed, the Neron model base-changes without alteration, and

$$
A(K^{\mathrm{nr}})=\mathcal A(R^{\mathrm{sh}}).
\tag{4.1}
$$

For $\ell\ne p$, reduction is injective on $\ell$-power torsion. Indeed, a torsion section reducing to the identity lies in the formal completion of the smooth group along the identity. Multiplication by $\ell$ has invertible differential there, hence is an automorphism on every infinitesimal neighborhood. A compatible inverse-limit point killed by a power of $\ell$ must therefore be zero.

The converse lifting statement must be formulated for compatible systems. Multiplication by $\ell$ on a smooth connected commutative algebraic group over $k^s$ is surjective when its unipotent, toric, and abelian layers are considered separately: it is an automorphism on the unipotent layer, a finite etale surjection on the torus, and an isogeny on the abelian quotient. Hensel lifting then lifts every compatible system of special-fiber $\ell$-power torsion to a compatible system of sections.

The finite component group causes no Tate-module contribution. If $F$ is a finite abelian group, then

$$
T_\ell F=\varprojlim_n F[\ell^n]=0,
\tag{4.2}
$$

because a compatible sequence would be divisible by arbitrarily high powers of $\ell$ inside a finite group. Thus the Tate module of the whole special fiber equals that of its identity component.

### 4.2 The fixed-part theorem

The connected special fiber is geometric, whereas inertia invariants are representation-theoretic. The next theorem is the bridge between them; it will later turn a conductor codimension into the dimensions of the abelian, toric, and unipotent parts of the Neron fiber.

**Theorem 4.1 (fixed part).** Let $A/K$ be an abelian variety and $\ell\ne p$. There is a canonical isomorphism

$$
T_\ell(\mathcal A_{k^s}^0)
\xrightarrow{\sim}(T_\ell A)^{I_K}.
\tag{4.3}
$$

Here the Tate module of the smooth connected algebraic group means the inverse limit of its geometric $\ell^n$-torsion.

**Proof.** An $I_K$-fixed element of $T_\ell A$ is a compatible system $(P_n)$ with each $P_n$ rational over $K^{\mathrm{nr}}$. By the Neron mapping property, each $P_n$ extends to a section over some finite etale subextension of $R^{\mathrm{sh}}$. Reduction gives a compatible torsion system in $\mathcal A_{k^s}$. Injectivity of reduction on prime-to-$p$ torsion makes the resulting map injective.

Conversely, take a compatible system in $\mathcal A_{k^s}^0[\ell^n]$. Smoothness lifts its first term to an unramified section $Q$. The section $\ell Q$ lies in the formal kernel; divide it there uniquely by $\ell$ and subtract the quotient from $Q$. The corrected lift is killed by $\ell$. Suppose now that terms through level $n$ have been lifted compatibly. Lift the next special point arbitrarily. Its $\ell$-multiple differs from the chosen level-$n$ lift by a section reducing to zero. Multiplication by $\ell$ is an automorphism on the formal kernel, so alter the new lift uniquely by a formal point to remove that difference. It then has order dividing $\ell^{n+1}$. Induction produces a compatible unramified system. The two constructions are inverse.

Finally, (4.2) removes the components, so the source may be written with $\mathcal A_{k^s}^0$. $\square$

The proof uses no semistable reduction theorem and no monodromy formula. It is therefore safe to use (4.3) later in proving conductor and reduction criteria.

### 4.3 The rank of the invariant submodule

Over an algebraically closed field, a smooth connected unipotent group has no nonzero prime-to-$p$ Tate module. A torus of rank $t$ has Tate rank $t$, and an abelian variety of dimension $a$ has Tate rank $2a$. Applying these facts to (1.1) and Theorem 4.1 gives

$$
\boxed{
\operatorname{rank}_{\mathbf Z_\ell}(T_\ell A)^{I_K}=2a+t.}
\tag{4.4}
$$

Consequently

$$
\operatorname{codim}_{\mathbf Q_\ell}(V_\ell A)^{I_K}
=2g-(2a+t)=t+2u.
\tag{4.5}
$$

The right side is independent of $\ell$. Formula (4.5) is the tame part of the conductor formula. Notice that a unipotent geometric group contributes twice its dimension to the loss of invariants, even though it has no $\ell$-adic Tate module of its own: each unipotent dimension replaces one abelian dimension, thereby removing two Tate directions.

For semistable reduction, $u=0$, so the invariant rank is $2g-t$. Once the inertial action formula is known, this will agree with the fact that a rank-$t$ square-zero operator has kernel of codimension $t$.

### 4.4 What the formula does and does not say

Equation (4.4) computes the dimension of inertia invariants, not the entire inertia representation. Two abelian varieties can have the same values of $(a,t,u)$ but different finite inertial types or different Swan conductors. In particular, additive elliptic curves in small residue characteristic can have the same connected special fiber dimension data and different wild conductors.

Nor does (4.4) say that every invariant torsion point is already rational over $K$. It is rational over the maximal unramified extension and carries a residue Galois action. Frobenius can act nontrivially on the abelian and toric special-fiber torsion even when inertia is trivial.

Finally, the theorem concerns $\ell\ne p$. At the residue characteristic, the formal group contains substantial $p$-power torsion phenomena, multiplication by $p$ does not have invertible differential, and connected finite group schemes can have only one geometric point. The prime-to-$p$ proof cannot be transplanted there.

## 5. Tame Kummer theory of periods

The weight filtration says where inertia can act but not how. The missing calculation is Kummer-theoretic: dividing a period extracts roots of its unit part and of its valuation part, and only the latter is ramified over the maximal unramified field. Carrying out that calculation produces the exact inertial shear.

### 5.1 The tame character

Work over $K^{\mathrm{nr}}$ so the residue field is separably closed. Choose a uniformizer $\pi$. For each $n$, choose compatible $\ell^n$th roots $\pi^{1/\ell^n}$. For $\sigma\in I_K$ there is a unique element

$$
t_{\ell,n}(\sigma)\in\mu_{\ell^n}
$$

such that

$$
\sigma(\pi^{1/\ell^n})
=t_{\ell,n}(\sigma)\pi^{1/\ell^n}.
$$

Passing to the inverse limit gives the $\ell$-primary tame character

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell(1).
\tag{5.1}
$$

It kills wild inertia and induces a surjection from the $\ell$-primary quotient of tame inertia. Changing the compatible roots changes no character; changing the uniformizer to a unit times $\pi$ changes the chosen roots by roots of a unit, which are unramified and hence leaves the restriction to inertia unchanged.

After choosing a compatible generator of $\mathbf Z_\ell(1)$ one may regard $t_\ell$ as $\mathbf Z_\ell$-valued. We will use the canonical twisted form. Then a map $N:V\to V(-1)$ may be contracted with $t_\ell(\sigma)$ to give an ordinary endomorphism of $V$.

### 5.2 The valuation Kummer lemma

The next elementary lemma is the source of every monodromy formula in the semistable case.

**Lemma 5.1.** Let $a\in(K^{\mathrm{nr}})^\times$. Choose compatible $\ell^n$th roots $a_n$ with $a_n^{\ell^n}=a$. The Kummer cocycle

$$
\sigma\longmapsto\left(\frac{\sigma(a_n)}{a_n}\right)_n
\in\mathbf Z_\ell(1)
$$

equals $v_K(a)t_\ell(\sigma)$.

**Proof.** Write $a=\pi^m u$ with $m=v_K(a)$ and $u$ a unit. Since the residue field is separably closed and $\ell\ne p$, the map $z\mapsto z^{\ell^n}$ is surjective on residue-field units. Hensel's lemma lifts a compatible system of $\ell^n$th roots of $u$ inside an unramified extension. Inertia fixes those roots. The remaining factor is $(\pi^{1/\ell^n})^m$, whose Kummer cocycle is $m t_{\ell,n}$. Passing to the limit proves the formula. $\square$

The lemma explains why units do not enter the integral monodromy operator. They can change the multiplicative refinement of a period pairing and hence affect descent data, but inertia sees only their unramified roots. The normalized valuation retains exactly the ramified Kummer information.

### 5.3 Tropicalization of the period lattice

Let $A$ be semistable and use (1.3) over $K^{\mathrm{nr}}$, where $T$ is split. For $y\in Y$ and $x\in X$, evaluate the character part of the period. In a mixed Raynaud extension this evaluation is expressed through a rigidification of the pullback of the Poincare bundle; write it as $\tau(y,x)\in(K^{\mathrm{nr}})^\times$. The biextension law makes $\tau$ bilinear, and

$$
\mu_A(y,x)=v_K(\tau(y,x)).
\tag{5.2}
$$

Thus $y$ determines a cocharacter

$$
\nu_A(y)\in X^\vee,
\qquad
\langle x,\nu_A(y)\rangle=\mu_A(y,x).
\tag{5.3}
$$

A different rigidification multiplies $\tau$ by a unit-valued bilinear coboundary. Its valuation is zero, so $\nu_A$ is intrinsic. Fullness of uniformization proves that $\nu_A$ is injective with finite cokernel.

The abelian projection of a period does not create an additional inertial term. The good-reduction abelian scheme is divisible by $\ell^n$ etale-locally over the strict henselization, and its chosen roots are unramified. The only ramified obstruction to dividing $u(y)$ lies in the toric valuation (5.3).

### 5.4 The inertial action formula

Choose a lift $\widetilde y\in T_\ell A$ of $y\in Y\otimes\mathbf Z_\ell$ through (3.7). At finite level it is represented by an $\ell^n$th root of $u(y)$. For $\sigma\in I_K$, the difference $\sigma\widetilde y-\widetilde y$ lies in $T_\ell E$. Its image in $T_\ell B$ is zero because $B$ has good reduction. It therefore lies in

$$
T_\ell T=X^\vee\otimes\mathbf Z_\ell(1).
$$

Evaluating against every $x\in X$ and applying Lemma 5.1 gives

$$
\sigma\widetilde y-\widetilde y
=t_\ell(\sigma)\nu_A(y).
\tag{5.4}
$$

The expression is independent of the chosen lift: changing $\widetilde y$ by an element of $T_\ell E$ leaves both sides unchanged, because inertia acts trivially on $T_\ell T$ and $T_\ell B$ over $K^{\mathrm{nr}}$.

**Theorem 5.2 (semistable inertia formula).** On $T_\ell A$, inertia acts trivially on $W_{-1}$ and on $W_0/W_{-1}$. For $v\in T_\ell A$ with image $\bar v\in Y\otimes\mathbf Z_\ell$,

$$
(\rho_\ell(\sigma)-1)v
=t_\ell(\sigma)\nu_A(\bar v)
\in X^\vee\otimes\mathbf Z_\ell(1)\subset T_\ell A.
\tag{5.5}
$$

In particular,

$$
(\rho_\ell(\sigma)-1)^2=0
\qquad(\sigma\in I_K),
\tag{5.6}
$$

and wild inertia acts trivially.

**Proof.** Triviality on $T_\ell T$ and $T_\ell B$ follows from their smooth extension over the strict henselization; exactness of (3.8) gives triviality on $T_\ell E$. The quotient $Y\otimes\mathbf Z_\ell$ is constant under inertia. Formula (5.4) proves (5.5). Its image lies in $W_{-2}$, on which inertia is trivial, so applying $\rho_\ell(\sigma)-1$ again gives zero. Finally $t_\ell$ kills wild inertia. $\square$

This proof locates the unipotence exactly. It is not an abstract consequence of a matrix theorem: it is the Kummer class of the valuation of the periods.

## 6. The monodromy operator

The inertial action formula contains a universal group character and a geometric linear map. Separating them produces the monodromy operator. This chapter establishes its twist, nilpotence, rank, polarized adjointness, and normalization under base change—the features needed to use it without coordinate-dependent sign errors.

### 6.1 A canonical operator with a twist

Formula (5.5) is most useful when the dependence on $\sigma$ is separated from the geometry of $A$. Define

$$
N_A:T_\ell A\longrightarrow T_\ell A(-1)
\tag{6.1}
$$

as the composite

$$
T_\ell A\longrightarrow Y\otimes\mathbf Z_\ell
\xrightarrow{\nu_A}X^\vee\otimes\mathbf Z_\ell
\longrightarrow T_\ell A(-1).
\tag{6.2}
$$

The last arrow is the twist by $-1$ of the inclusion

$$
X^\vee\otimes\mathbf Z_\ell(1)=T_\ell T
\hookrightarrow T_\ell A.
$$

Then Theorem 5.2 becomes the canonical identity

$$
\boxed{
\rho_\ell(\sigma)=1+t_\ell(\sigma)N_A
\qquad(\sigma\in I_K).}
\tag{6.3}
$$

Here contraction of $\mathbf Z_\ell(1)$ with the target twist $(-1)$ is understood. If a compatible generator of $\mathbf Z_\ell(1)$ is chosen, $N_A$ becomes an ordinary nilpotent matrix and (6.3) becomes $\rho(\sigma)=\exp(t_\ell(\sigma)N_A)$; the exponential stops after its linear term because $N_A^2=0$.

The twist in (6.1) is essential. As a map $V_\ell A\to V_\ell A(-1)$, $N_A$ is Galois equivariant. If a basis of $\mathbf Q_\ell(1)$ is chosen and $N_0$ denotes the resulting ordinary endomorphism of $V_\ell A$, this equivariance becomes

$$
\rho_\ell(g)N_0\rho_\ell(g)^{-1}
=\chi_\ell(g)N_0.
\tag{6.4}
$$

For geometric Frobenius over $\mathbf F_q$, the scalar is $q^{-1}$; for arithmetic Frobenius it is $q$. Suppressing the twist would make the same operator appear to obey contradictory scalar conventions.

### 6.2 Nilpotence and the monodromy filtration

By construction,

$$
N_A(W_i)\subseteq W_{i-2}(-1),
\qquad N_A(W_{-1})=0,
\qquad N_A^2=0.
\tag{6.5}
$$

The induced map on the only possibly nonzero graded pieces is

$$
\operatorname{Gr}_0(T_\ell A)=Y\otimes\mathbf Z_\ell
\xrightarrow{\nu_A}
X^\vee\otimes\mathbf Z_\ell
=\operatorname{Gr}_{-2}(T_\ell A)(-1).
\tag{6.6}
$$

After tensoring with $\mathbf Q_\ell$, fullness makes (6.6) an isomorphism. Thus the weight filtration is also the monodromy filtration centered at weight $-1$: $N_A$ identifies the outer graded pieces after the required twist, and the middle piece is killed.

More explicitly, let $V=V_\ell A$. Since $N_A$ has rank $t$,

$$
0\subset\operatorname{im}N_A\subset\ker N_A\subset V
\tag{6.7}
$$

has dimensions

$$
\dim\operatorname{im}N_A=t,
\qquad
\dim\ker N_A=2g-t.
\tag{6.8}
$$

The quotient $\ker N_A/\operatorname{im}N_A$ is naturally the rational Tate module of the good-reduction abelian part $B$, of dimension $2(g-t)$. Thus monodromy removes two toric directions at a time from the central quotient while retaining one toric direction in the invariant kernel.

### 6.3 Rank and the invariant subspace

Because the image of $t_\ell:I_K\to\mathbf Z_\ell(1)$ is open and nonzero, (6.3) gives

$$
(T_\ell A)^{I_K}=\ker N_A.
\tag{6.9}
$$

Indeed, every element of the kernel is fixed. Conversely, if $v$ is fixed, then $t_\ell(\sigma)N_Av=0$ for every $\sigma$. The target is torsion-free and some $t_\ell(\sigma)$ is nonzero, so $N_Av=0$.

Combining (6.8) and (6.9) recovers the semistable case of the fixed-part formula:

$$
\operatorname{rank}(T_\ell A)^{I_K}=2g-t.
\tag{6.10}
$$

This agreement is an important noncircular check. Theorem 4.1 obtained the left side directly from the Neron model, while the present computation obtained it from periods. Their equality confirms that the torus in the connected special fiber and the lattice rank in uniformization are the same geometric invariant.

The following criteria are immediate for a semistable abelian variety:

$$
N_A=0
\Longleftrightarrow t=0
\Longleftrightarrow A\text{ has good reduction},
\tag{6.11}
$$

and

$$
\operatorname{rank}N_A=t.
\tag{6.12}
$$

The last equality is often the fastest way to read toric rank from a Tate representation.

### 6.4 Polarizations and adjointness

Let $e_\ell:T_\ell A\times T_\ell A^\vee\to\mathbf Z_\ell(1)$ be the perfect Tate-module pairing. Galois equivariance and (6.3) imply

$$
e_\ell(N_Av,w)+e_\ell(v,N_{A^\vee}w)=0
\tag{6.13}
$$

after the twists are contracted correctly. To prove it, substitute $1+tN$ in both variables of the equality

$$
e_\ell(\rho(\sigma)v,\rho^\vee(\sigma)w)=e_\ell(v,w).
$$

The linear coefficient is (6.13); the quadratic coefficient vanishes because each $N$ lowers weight by two and the outer isotropic pieces pair only with their complementary pieces.

If $\lambda:A\to A^\vee$ is a polarization, put

$$
\langle v,w\rangle_\lambda=e_\ell(v,\lambda w).
$$

Then $N_A$ is infinitesimally skew-adjoint:

$$
\langle N_Av,w\rangle_\lambda
+\langle v,N_Aw\rangle_\lambda=0.
\tag{6.14}
$$

On the outer graded pieces, the sign in (6.14) converts the alternating Weil pairing into the symmetric monodromy form. Concretely, pairing a weight-zero vector $y$ with $N_Ay'$ gives the valuation pairing $q_\lambda(y,y')$, and symmetry of the polarization makes

$$
q_\lambda(y,y')=q_\lambda(y',y).
$$

Positivity is geometric rather than linear-algebraic: it comes from ampleness of the polarization and was proved in the uniformization theory.

### 6.5 Ramified base change

Let $L/K$ have ramification index $e$, and suppose $A$ is semistable over $K$. Normalized valuations give

$$
\nu_{A_L}=e\nu_A,
\qquad N_{A_L}=eN_A.
\tag{6.15}
$$

There is no contradiction with restriction of the same Galois representation. If $t_{\ell,K}$ and $t_{\ell,L}$ are defined using uniformizers of $K$ and $L$, then

$$
t_{\ell,K}|_{I_L}=e\,t_{\ell,L}.
\tag{6.16}
$$

Indeed $\pi_K$ is a unit times $\pi_L^e$. Therefore

$$
t_{\ell,K}(\sigma)N_A
=t_{\ell,L}(\sigma)N_{A_L},
$$

so the action matrix itself is unchanged. Integral monodromy scales because the valuation scale changes; the actual restricted representation does not.

Under unramified base change $e=1$. The operator and pairing remain unchanged, though a nonsplit torus may split and its residue Galois module become easier to describe.

## 7. The integral monodromy pairing

The rational operator records the number of degenerating directions, but integral arithmetic also needs their lengths and mutual positions. Those data form a pairing between the toric character lattices of an abelian variety and its dual. The Poincare biextension supplies the pairing canonically, while polarizations supply symmetry and positivity.

### 7.1 The pairing between the two toric lattices

For semistable $A$, let

$$
X=X_A=X^*(T_A),
\qquad Y=X_{A^\vee}=X^*(T_{A^\vee}).
$$

The **integral monodromy pairing** is

$$
\mu_A:Y\times X\longrightarrow\mathbf Z.
\tag{7.1}
$$

It is characterized by the property that the associated map

$$
Y\longrightarrow X^\vee,
\qquad y\longmapsto(x\mapsto\mu_A(y,x))
\tag{7.2}
$$

is the tropical period map $\nu_A$. It is Galois equivariant for the residue Galois actions and nondegenerate over $\mathbf Q$.

The order of the variables is intentional. The first lattice is the character lattice of the torus of the dual variety; through dual uniformization it is the period lattice of $A$. Transposing gives

$$
\mu_{A^\vee}:X\times Y\to\mathbf Z,
\qquad
\mu_{A^\vee}(x,y)=\mu_A(y,x).
\tag{7.3}
$$

### 7.2 Construction from the Poincare biextension

We recall the construction in a form that proves independence of choices. Let

$$
0\to T_A\to E_A\to B_A\to0,
\qquad
0\to T_{A^\vee}\to E_{A^\vee}\to B_A^\vee\to0
\tag{7.4}
$$

be dual Raynaud extensions. The Poincare bundle on $B_A\times B_A^\vee$ pulls back to a biextension on $E_A\times E_{A^\vee}$. The two period maps trivialize it along

$$
Y\times X\longrightarrow E_A\times E_{A^\vee}.
$$

Comparing the two biextension laws yields a multiplicative pairing

$$
\tau_A:Y\times X\longrightarrow(K^{\mathrm{nr}})^\times.
\tag{7.5}
$$

Set

$$
\mu_A(y,x)=v_K(\tau_A(y,x)).
\tag{7.6}
$$

Bilinearity follows because valuation turns tensor product into addition. A different rigidification of the Poincare bundle changes $\tau_A$ by the product of a character in each variable whose values are units on the integral Raynaud extension. Hence its valuation is unchanged. A different splitting field transports both lattices and the pairing equivariantly, so descent gives (7.1) over $k$.

In the pure toric case $E_A=T_A^{\mathrm{an}}$ and (7.5) is simply

$$
\tau_A(y,x)=x(u(y)).
$$

For a semistable Jacobian, the Poincare construction reduces locally at a node $e$ to the smoothing factor $(\pi^{n_e}u_e)^{c_ec'_e}$, so its valuation is $n_ec_ec'_e$.

### 7.3 Nondegeneracy and positivity

The valuation construction would be too weak for component groups if it had a kernel or an uncontrolled sign. Nondegeneracy makes its cokernel finite, while positivity after polarization turns the pairing into a genuine integral length form.

**Proposition 7.1.** The maps

$$
Y\longrightarrow X^\vee,
\qquad
X\longrightarrow Y^\vee
\tag{7.7}
$$

induced by $\mu_A$ are injective with finite cokernel.

**Proof.** The first is the tropical period map. Its real extension is an isomorphism because the period lattice is full: injectivity is the discreteness condition, and surjectivity is forced by properness of $A^{\mathrm{an}}$. Since $X$ and $Y$ have the same finite rank, the integral map is injective with finite cokernel. The second map is its transpose and has the same nonzero determinant in dual bases. $\square$

Let $\lambda:A\to A^\vee$ be a polarization. It induces a finite-index map

$$
\lambda_Y:Y_A\longrightarrow X_A
$$

after identifying the lattices through dual uniformization. The polarized monodromy form is

$$
q_\lambda(y,y')=\mu_A(y,\lambda_Y(y')).
\tag{7.8}
$$

**Theorem 7.2.** The form $q_\lambda$ is symmetric and positive definite. If $\lambda$ is principal, $\lambda_Y$ is an isomorphism.

**Proof.** Pull the ample line bundle inducing $\lambda$ to the Raynaud covering. Its period descent cocycle is governed by the Poincare biextension. Commutativity of the cocycle in the two period directions gives symmetry of (7.8). For $0\ne y\in Y$, restrict the quotient and the line bundle to the one-dimensional analytic direction generated by $y$. Its closed period loop has degree a positive multiple of $q_\lambda(y,y)$. Ampleness makes that degree positive, so $q_\lambda(y,y)>0$. The principal assertion follows from the degree formula for a polarized Raynaud quotient: the polarization degree is the degree on the good-reduction abelian part times the square of the lattice index. Degree one forces both factors and the index to be one. $\square$

Nondegeneracy of $\mu_A$ does not depend on a polarization, but positivity does. Calling an arbitrary nonsymmetric pairing positive would be meaningless; positivity is a property of (7.8).

### 7.4 Functoriality and duality

Let $f:A\to C$ be a homomorphism of semistable abelian varieties. It induces covariant maps on period lattices and contravariant maps on torus characters. Write

$$
f_Y:Y_A\to Y_C,
\qquad f_X^*:X_C\to X_A.
$$

Functoriality of the Poincare bundle gives

$$
\mu_C(f_Yy,x)=\mu_A(y,f_X^*x).
\tag{7.9}
$$

Thus the square formed by the monodromy maps commutes. On Tate modules this is

$$
N_C\,T_\ell(f)=T_\ell(f)(-1)\,N_A.
\tag{7.10}
$$

Taking $f^\vee$ transposes (7.9), proving (7.3). If polarizations are chosen and $f^\dagger$ is the Rosati adjoint, then $f$ and $f^\dagger$ are adjoint for the polarized monodromy forms. This is the general source of the pullback--pushforward adjunction for graph pairings of Jacobians.

## 8. Component groups as monodromy discriminants

The component group is the finite obstruction to moving a point into the bounded identity neighborhood by a period. Tropicalization makes that sentence an exact cokernel. Once both an abelian variety and its dual are treated, ordinary lattice duality produces the perfect component pairing and explains the weighted graph formula for Jacobians.

### 8.1 The tropical component map

Work over $R^{\mathrm{sh}}$, so both tori split and all geometric components are visible. The tropicalization map on the Raynaud extension is

$$
\operatorname{trop}:E(K^{\mathrm{nr}})\longrightarrow X^\vee.
\tag{8.1}
$$

Its kernel is the subgroup reducing to the identity component of the integral semiabelian model. The map is onto: for each cocharacter of the split torus, a suitable power of the uniformizer gives a torus point with exactly that valuation, and the extension by the proper good-reduction part does not obstruct the lift.

Passing from $E$ to $A=E/Y$ identifies tropical vectors differing by $\nu_A(Y)$. Therefore (8.1) descends to

$$
A(K^{\mathrm{nr}})\longrightarrow X^\vee/\nu_A(Y).
\tag{8.2}
$$

The kernel consists precisely of points whose Neron sections meet $\mathcal A_{k^s}^0$. Indeed, a point has zero class if a period translate of a lift has bounded toric valuation; that translate lies in the formal identity neighborhood and reduces to the connected semiabelian group. Conversely every point reducing to the identity component has a bounded lift. Thus (8.2) is the Neron component map.

### 8.2 The component exact sequences

Tropicalization should measure precisely which Raynaud points land on the identity component of the Neron model. Making that assertion exact identifies the finite failure of the period lattice to fill the cocharacter lattice with the geometric component group.

**Theorem 8.1 (component presentation).** For a semistable abelian variety there are canonical residue-Galois-equivariant exact sequences

$$
0\longrightarrow Y\xrightarrow{\nu_A}X^\vee
\longrightarrow\Phi_A(k^s)\longrightarrow0,
\tag{8.3}
$$

and

$$
0\longrightarrow X\xrightarrow{\nu_{A^\vee}}Y^\vee
\longrightarrow\Phi_{A^\vee}(k^s)\longrightarrow0.
\tag{8.4}
$$

**Proof.** Injectivity and finite cokernel were proved in Proposition 7.1. Section 8.1 identifies the cokernel with the target of the geometric component map and its kernel with $A^0(K^{\mathrm{nr}})$. The Neron model gives a surjection onto geometric components over the separably closed residue field, proving (8.3). Apply the same argument to $A^\vee$ and use transposition of the pairing to obtain (8.4). Equivariance follows because tropicalization and the Poincare biextension are canonical. $\square$

This theorem generalizes the weighted graph exact sequence for Jacobians. It also explains why component groups can change under isogeny while toric rank does not: rank records the rational vector spaces in (8.3), whereas the component group records the integral index.

### 8.3 The Grothendieck component pairing

Let $\nu:Y\to X^\vee$ be an injective map of equal-rank lattices, and let $\nu^t:X\to Y^\vee$ be its transpose. There is a canonical pairing

$$
\operatorname{coker}(\nu)\times\operatorname{coker}(\nu^t)
\longrightarrow\mathbf Q/\mathbf Z.
\tag{8.5}
$$

For $\bar a\in X^\vee/\nu(Y)$ and $\bar b\in Y^\vee/\nu^t(X)$, choose lifts $a,b$. Since $\nu_\mathbf Q$ is an isomorphism, put

$$
\langle\bar a,\bar b\rangle
=b(\nu_\mathbf Q^{-1}a)\bmod\mathbf Z.
\tag{8.6}
$$

Changing $a$ by $\nu(y)$ changes the value by $b(y)\in\mathbf Z$. Changing $b$ by $\nu^t(x)$ changes it by

$$
\nu^t(x)(\nu_\mathbf Q^{-1}a)=a(x)\in\mathbf Z.
$$

Thus (8.6) is well defined.

**Proposition 8.2.** Pairing (8.5) is perfect.

**Proof.** Choose bases and put the integral matrix of $\nu$ in Smith normal form

$$
\operatorname{diag}(d_1,\ldots,d_t),
\qquad d_i>0,\quad d_i\mid d_{i+1}.
$$

Both cokernels are $\bigoplus_i\mathbf Z/d_i\mathbf Z$, and (8.6) is the orthogonal sum of

$$
(\bar r,\bar s)\longmapsto rs/d_i\bmod\mathbf Z.
$$

Each summand is perfect. $\square$

Using (8.3)-(8.4), this gives the **Grothendieck component pairing**

$$
\Phi_A(k^s)\times\Phi_{A^\vee}(k^s)
\longrightarrow\mathbf Q/\mathbf Z.
\tag{8.7}
$$

It is perfect and residue-Galois invariant for semistable abelian varieties. The semistable hypothesis is part of the assertion: outside it, construction of a pairing on components is subtler, and perfection cannot be inferred from (8.7).

### 8.4 Polarized and principally polarized cases

A polarization $\lambda:A\to A^\vee$ induces a map $\Phi_A\to\Phi_{A^\vee}$. Pulling (8.7) back along that map gives a pairing on $\Phi_A$, represented by the inverse of the polarized monodromy matrix modulo $\mathbf Z$. It is symmetric because $q_\lambda$ is symmetric.

If $\lambda$ is principal, the Neron models of $A$ and $A^\vee$ are isomorphic, and the lattice map $Y\to X$ is an isomorphism. Hence

$$
\Phi_A(k^s)\simeq Y^\vee/q_\lambda(Y)
\tag{8.8}
$$

and

$$
\langle\bar a,\bar b\rangle_\lambda
=b(q_{\lambda,\mathbf Q}^{-1}a)\bmod\mathbf Z.
\tag{8.9}
$$

Its order is the absolute determinant of a Gram matrix of $q_\lambda$. Unimodularity of $q_\lambda$, not merely existence of a principal polarization on the generic fiber, is equivalent to trivial component group in the toric directions.

### 8.5 Semistable Jacobians

Let $C/K$ have a split semistable model with weighted dual graph $(\Gamma,(n_e))$, and let $J=\operatorname{Jac}(C)$. The preceding curve and uniformization theories give

$$
X_J=Y_J=H_1(\Gamma,\mathbf Z),
$$

and the canonical principal polarization identifies the two. The monodromy form is

$$
q_\Gamma(c,c')=\sum_e n_ec_ec'_e.
\tag{8.10}
$$

Therefore

$$
0\longrightarrow H_1(\Gamma,\mathbf Z)
\xrightarrow{q_\Gamma}H_1(\Gamma,\mathbf Z)^\vee
\longrightarrow\Phi_J(k^s)\longrightarrow0.
\tag{8.11}
$$

This recovers the graph theorem from the general component presentation. It does not reprove that theorem circularly: (8.3) was obtained from tropical uniformization, while the graph calculation independently identifies its lattices and local pairing.

Blowing up or resolving a node subdivides an edge. A cycle has the same coefficient along every segment, so the unit-length sum on the subdivision equals the weighted term $n_ec_ec'_e$. Thus (8.10), the monodromy operator, and the component discriminant are invariant under the passage between a thick stable node and its regular semistable resolution.

## 9. Potential semistable reduction

All preceding monodromy formulas assume semistability over the ground field. To obtain quasi-unipotence for an arbitrary abelian variety, semistability must first be reached after finite extension. The proof here reduces the problem to the stable reduction theorem for curves by placing the abelian variety inside the isogeny category of a Jacobian.

### 9.1 Semistability under isogeny

The existence of a field over which $A$ is semistable is central: it will imply quasi-unipotence for every $T_\ell A$. We first establish the stability property needed in the proof.

**Proposition 9.1.** If $A$ and $C$ are isogenous abelian varieties over $K$, then $A$ has semistable reduction if and only if $C$ does.

**Proof strategy.** A finite quotient changes the integral lattices of a Raynaud datum but cannot create a unipotent direction. We make this precise on the analytic covering.

Suppose $A$ is semistable and let $f:A\to C$ be an isogeny with finite kernel $H$. Pull $H$ back through $E\to A^{\mathrm{an}}$. Its inverse image $\widetilde H$ is a finite union of cosets of $Y$, hence a discrete finitely generated abelian group. Let $F$ be its finite torsion subgroup. Then $Y'=\widetilde H/F$ is a lattice containing the image of $Y$ with finite index, and

$$
C^{\mathrm{an}}\simeq(E/F)/Y'.
$$

It remains to verify that $E/F$ is again a Raynaud extension. Choose $n$ killing $F$. The subgroup $F$ lies in the $n$-torsion of the integral semiabelian extension. Its schematic closure is finite because it lies in the finite locally free group $[n]^{-1}(0)$, and it is flat because schematic closure from the generic fiber is torsion-free over a DVR. The finite flat quotient is smooth and semiabelian: fiberwise, the quotient of the maximal torus by the toric part of $F$ is a torus, and the proper quotient by the remaining finite subgroup is an abelian scheme. Thus its analytic generic fiber yields

$$
0\to T'\to E'\to B'\to0,
\qquad
0\to Y'\to E'\to C^{\mathrm{an}}\to0,
\tag{9.1}
$$

with $B'$ of good reduction, $T'$ a torus, and $Y'$ a full lattice. Fullness is unchanged by finite-index enlargement and finite torus quotient. The polarization of $C$ pulls back to a polarization of $A$; conversely, norming a sufficiently high tensor power of an ample bundle on $A$ along $f$ supplies positive descent data for (9.1). Raynaud uniformization therefore shows that $C$ is semistable. This argument also covers isogenies divisible by $p$: finite flat quotient geometry, not a count of geometric kernel points, prevents a unipotent part from appearing.

The reverse implication follows from a quasi-inverse isogeny $g:C\to A$ with $gf=[n]$ and the same argument applied to $g$. $\square$

Products are semistable exactly when their factors are. One direction follows by taking products of the connected Neron fibers. Conversely, the unipotent radical of

$$
(\mathcal A\times\mathcal C)_k^0
=\mathcal A_k^0\times\mathcal C_k^0
$$

is $U_A\times U_C$; if the product is semistable, both factors vanish.

### 9.2 Producing a Jacobian cover

Semistable reduction is already available for curves, so the remaining geometric task is to connect an arbitrary abelian variety to a curve without losing it up to isogeny. A sufficiently ample curve inside the abelian variety provides exactly that connection through its Jacobian.

**Lemma 9.2.** After a finite separable extension of $K$, every abelian variety $A/K$ is an isogeny factor of the Jacobian of a smooth proper geometrically connected curve.

**Proof.** For the zero-dimensional abelian variety take $C=\mathbf P^1$, and for $g=1$ take $C=A$. Assume $g\ge2$. Choose a symmetric very ample line bundle on $A$. Select finitely many points and tangent vectors whose translates span the tangent space of $A$. A sufficiently high tensor power separates these first-order jets. Since a nontrivially valued field is infinite, Bertini with the prescribed finite jet conditions allows successive general hyperplane sections, after finite separable extension to secure rational choices, whose complete intersection

$$
C=H_1\cap\cdots\cap H_{g-1}\subset A
$$

is a smooth geometrically connected curve through the origin and has the selected tangent lines. If an invariant differential on $A$ vanishes on $C$, it vanishes on all those tangent vectors. Their translates span the tangent space, so the differential is zero. Hence restriction of invariant differentials to $C$ is injective.

The inclusion $i:C\to A$, based at the origin, induces by the Albanese property a homomorphism

$$
f:J(C)\longrightarrow A.
\tag{9.2}
$$

The dual of its tangent map is restriction

$$
H^0(A,\Omega_A^1)\longrightarrow H^0(C,\Omega_C^1),
$$

which is injective by construction. Hence $df$ is surjective. The image of a homomorphism of abelian varieties is an abelian subvariety whose tangent space contains the image of $df$; it therefore has dimension $g$ and equals $A$. Thus $f$ is surjective with connected-kernel identity component $D$.

Choose polarizations. The Rosati adjoint $f^\dagger:A\to J(C)$ is defined up to a positive integer denominator; multiplying clears that denominator. The composite $ff^\dagger$ is an isogeny of $A$: its kernel is finite because its polarized quadratic form is positive on every nonzero tangent direction. It follows that $f^\dagger(A)\cap D$ is finite and dimensions add. Therefore

$$
f^\dagger(A)\times D\longrightarrow J(C)
$$

is an isogeny. The first factor is isogenous to $A$, proving the lemma. $\square$

The argument is included to show that the reduction theorem for curves genuinely reaches arbitrary dimension rather than only Jacobians given in advance.

### 9.3 The semistable reduction theorem

The two preceding ingredients now fit together: Jacobians inherit semistable reduction from curves, and isogeny factors inherit it from Jacobians. This is the geometric source of every later quasi-unipotence statement.

**Theorem 9.3 (potential semistable reduction).** Every abelian variety over a complete discretely valued field acquires semistable reduction after a finite separable extension.

**Proof.** Apply Lemma 9.2 after a finite separable extension, obtaining a smooth proper curve $C$ whose Jacobian has $A$ as an isogeny factor. The semistable model theorem for curves gives a further finite separable extension $L/K$ over which $C$ has semistable reduction. The identity component of the Neron model of $J(C)_L$ is the generalized Jacobian of the nodal special fiber. It is an extension of the product of the Jacobians of the normalized components by the graph torus. Hence $J(C)_L$ is semistable.

By Poincare complete reducibility, $J(C)_L$ is isogenous to $A_L\times D_L$ for an abelian variety $D$. Proposition 9.1 makes the product semistable. The product criterion then makes $A_L$ semistable. All extensions used were finite and separable. $\square$

This proof deliberately separates the deep geometric input from the group-theoretic consequences. The only stable-reduction input is the theorem for curves. General abelian varieties enter through a Jacobian cover and isogeny stability.

### 9.4 How much extension is being asserted

The theorem does not claim semistability over the original field, nor does it claim that a chosen extension is minimal or Galois. Taking a finite Galois closure preserves semistability after further extension, so one may assume the semistable field is Galois whenever descent actions are studied.

Once semistability has been reached, every further finite extension preserves it and preserves toric rank. A ramified extension scales integral monodromy by its ramification index; an unramified extension may split the torus or components without changing their geometric ranks.

The theorem also does not say that good reduction is potentially attained. A Tate curve remains toric after every finite extension. Potential good reduction is the special case in which the toric rank after semistable extension is zero.

## 10. Galois criteria for reduction

Potential semistability turns the qualitative shape of inertia into a test for the original reduction type. A finite descent factor measures failure of semistable descent, while the unipotent factor measures the toric periods. Removing first the finite factor and then the monodromy operator yields the semistable and good reduction criteria.

### 10.1 The semistable reduction criterion

We now prove that semistability can be detected on one prime-to-$p$ Tate module.

**Theorem 10.1 (semistable criterion).** For an abelian variety $A/K$ and one, equivalently every, prime $\ell\ne p$, the following are equivalent:

1. $A$ has semistable reduction over $K$;
2. inertia acts unipotently on $V_\ell A$;
3. every $\sigma\in I_K$ satisfies
   $$
   (\rho_\ell(\sigma)-1)^2=0.
   $$

**Proof.** If $A$ is semistable, Theorem 5.2 gives condition 3, which implies 2.

Assume condition 2. By Theorem 9.3 choose a finite Galois extension $L/K$ over which $A$ is semistable. The descent group acts on the Raynaud data over $L$. The action on each graded piece in (1.5) factors through a finite group: on the character and period lattices it is an integral finite-order action, and on the good-reduction part its inertia descent action is finite.

For $\sigma\in I_K$, the semisimple part of $\rho_\ell(\sigma)$ is exactly this finite graded action; the remaining part is the Kummer unipotent shear from periods. A finite-order matrix over characteristic zero that is also unipotent is the identity, because its minimal polynomial divides both $X^m-1$, which is separable, and a power of $X-1$. Hence the finite descent action is trivial on every graded piece.

We use the semistable descent lemma: a semistable Raynaud model over a finite Galois extension descends to semistable reduction over the base if the finite inertial action on all three graded pieces of its one-motive is trivial. Here is the geometric proof. Choose a rational polyhedral decomposition for the toric formal charts and refine the finitely many Galois translates to obtain an invariant decomposition. The intrinsic descent action on $A_L$ then acts on the associated Raynaud formal model. On the identity chart it preserves

$$
0\longrightarrow\mathfrak T\longrightarrow\mathfrak E
\longrightarrow\mathfrak B\longrightarrow0.
$$

Triviality on $X$, $T_\ell B$, and $Y$ makes its finite action trivial respectively on the special torus, the special abelian quotient, and the group of chart translations. Faithfulness of the prime-to-$p$ Tate module for homomorphisms of abelian varieties is used in the middle assertion. An automorphism of the semiabelian special fiber that is the identity on its torus and abelian quotient is itself the identity: its difference from the identity would factor through a homomorphism from the proper abelian quotient to the affine torus, and such a homomorphism is zero.

Form the normalized quotient of the invariant formal model and smoothen it along the identity. On completed Hopf algebras, the preceding trivial action leaves the multiplicative character parameters and the formally smooth abelian parameters unchanged; ramification changes their coefficients but introduces no primitive additive parameter. Consequently the smooth identity special fiber of the quotient is still the extension of the descended abelian variety by the descended torus. The period translations descend because their finite action is trivial, and their positive pairing descends with them. The generic fiber of the quotient is the given $A/K$, so uniqueness of the Neron model identifies its smooth identity group with $\mathcal A^0$. It has no unipotent radical, proving semistable reduction. This proves the descent lemma without assuming the criterion under proof.

This proves 2 implies 1. Once 1 holds, condition 3 follows, completing the equivalence. The argument is independent of the chosen semistable field because Raynaud data are canonical after common extension. $\square$

The descent paragraph is where unipotence does geometric work. Merely knowing that each eigenvalue is a root of unity would give potential semistability, not semistability over $K$.

### 10.2 The good reduction criterion

Good reduction is the zero-monodromy endpoint of the semistable criterion. Once unipotence has supplied a semiabelian model, trivial inertia must rule out its toric part; conversely, a proper smooth group model has no inertial motion at all.

**Theorem 10.2 (Neron--Ogg--Shafarevich criterion).** For $\ell\ne p$, the following are equivalent:

1. $A$ has good reduction;
2. $T_\ell A$ is unramified;
3. $V_\ell A$ is unramified.

**Proof.** If $A$ extends to an abelian scheme, every $\ell^n$-torsion group is finite etale over $R$, so inertia acts trivially. Thus 1 implies 2, and 2 implies 3.

Assume 3. A trivial inertia action is unipotent, so Theorem 10.1 gives semistable reduction. Formula (6.3) and surjectivity of the tame character show that $N_A=0$. By (6.12), the toric rank is zero. A semistable connected special fiber with toric rank zero is an abelian variety. Moreover Theorem 8.1 has zero lattices, so its component group is zero. The Neron model is therefore proper, hence an abelian scheme. This proves good reduction. $\square$

The component argument can be shortened: in semistable uniformization, $t=0$ forces $Y=0$, $E=B$, and $A=B$ has good reduction. It is recorded above to show compatibility with the Neron-model criterion.

### 10.3 Finite-level tests

Triviality on $T_\ell A$ is an infinite condition, but a finite level can kill a finite semisimple inertial part. The relevant elementary matrix lemma is the following.

**Lemma 10.3.** For $\ell\ge3$, the kernel of

$$
\operatorname{GL}_n(\mathbf Z_\ell)
\longrightarrow\operatorname{GL}_n(\mathbf F_\ell)
$$

contains no nontrivial finite-order element. For $\ell=2$, the analogous assertion holds modulo $4$.

**Proof.** If $g=1+\ell^rM$ with $r\ge1$ minimal and $g$ has prime order $q$, expand $g^q$. If $q\ne\ell$, the first nonzero term is $q\ell^rM$ modulo $\ell^{r+1}$, impossible. If $q=\ell$, then

$$
(1+\ell^rM)^\ell
\equiv1+\ell^{r+1}M
\pmod{\ell^{r+2}}
$$

for odd $\ell$, again impossible. Every finite-order element has a prime-order power, proving the claim. For $\ell=2$, starting with $r\ge2$ makes the same binomial estimate work. $\square$

Suppose inertia acts trivially on $A[\ell]$ for $\ell\ge3$ or on $A[4]$ for $\ell=2$. Potential semistable reduction makes every inertial matrix a product of a finite semisimple part and a unipotent part. The finite semisimple part belongs to the compact closure of the cyclic group generated by the original integral matrix, so it preserves the Tate lattice and has the same congruence to the identity. Lemma 10.3 kills it. Therefore inertia acts unipotently and $A$ is semistable by Theorem 10.1.

This is a **semistable**, not a good-reduction, test. A Tate curve can have its finite semisimple inertia killed while retaining a nonzero unipotent shear at higher $\ell$-power levels. To force good reduction one needs triviality on the whole Tate module, or an additional argument that the monodromy map vanishes.

### 10.4 Independence of the auxiliary prime

The geometry now proves the expected independence statements without comparing matrices across coefficient fields.

- If $V_\ell A$ is unipotent on inertia for one $\ell\ne p$, Theorem 10.1 gives semistable reduction; Theorem 5.2 then gives unipotence for every $\ell'\ne p$.
- If $V_\ell A$ is unramified for one $\ell$, Theorem 10.2 gives good reduction; good reduction makes every $V_{\ell'}A$ unramified.
- In the semistable case, $\operatorname{rank}N_{A,\ell}=t$ for every $\ell$.
- The invariant dimension $2a+t$ is independent of $\ell$ by Theorem 4.1.

These are geometric independence results. They do not identify the integral modules $T_\ell A$ for different primes, which live over different coefficient rings and have no natural direct comparison.

## 11. Quasi-unipotence

We now return from semistable geometry to the original field. The finite extension of Chapter 9 leaves a finite descent action and a square-zero unipotent action. Their combination proves quasi-unipotence and gives the sharper block-size bound special to first cohomology of abelian varieties.

### 11.1 The theorem

A linear operator is **quasi-unipotent** if some positive power is unipotent. A continuous representation of inertia is quasi-unipotent if an open subgroup acts unipotently. In characteristic zero the two formulations agree for the compact inertial images considered here.

**Theorem 11.1 (monodromy theorem for abelian varieties).** Let $A/K$ be an abelian variety and $\ell\ne p$. There is an open subgroup $I'\subseteq I_K$ such that

$$
(\rho_\ell(\sigma)-1)^2=0
\qquad(\sigma\in I').
\tag{11.1}
$$

In particular, $I_K$ acts quasi-unipotently on $T_\ell A$ and $V_\ell A$.

**Proof.** By Theorem 9.3 choose a finite separable extension $L/K$ over which $A$ is semistable, and replace it by a finite Galois extension. Put $I'=I_L$. The semistable inertia formula over $L$ gives

$$
\rho_\ell(\sigma)=1+t_{\ell,L}(\sigma)N_{A_L}
$$

with $N_{A_L}^2=0$, proving (11.1). Since $I_L$ has finite index in $I_K$, it is open. $\square$

This proof is abelian-specific and geometric. Potential semistable reduction supplies the open subgroup, and Kummer theory of the periods supplies the exponent two. No general cohomological monodromy theorem is being assumed.

### 11.2 Finite descent and unipotent motion

Choose a finite Galois semistable field $L/K$. Over $L$, the Raynaud data carry an action of the finite descent group. The inertial representation has two logically different parts:

1. a finite action on the toric lattices, the good-reduction abelian part, and the period lattice;
2. the unipotent Kummer shear measured by $N_{A_L}$.

After extending scalars if necessary, every $\rho_\ell(\sigma)$ has a commuting Jordan decomposition

$$
\rho_\ell(\sigma)=\rho_{\mathrm{fin}}(\sigma)
\rho_{\mathrm{uni}}(\sigma),
\tag{11.2}
$$

where the first factor has finite order and the second is unipotent with square-zero logarithm. The decomposition is intrinsic because semisimple and unipotent parts are polynomials in the matrix over characteristic zero. It need not preserve an integral direct-sum decomposition of $T_\ell A$; it is a statement over $\overline{\mathbf Q}_\ell$.

Wild inertia acts trivially on the unipotent factor. Indeed, the tame character vanishes on wild inertia. Hence the wild image on $V_\ell A$ is finite. Tame inertia can contribute both a finite prime-to-$p$ descent action and the infinite pro-$\ell$ unipotent shear.

This separation prevents two common confusions. Quasi-unipotence does not mean that wild inertia is trivial over $K$: it can survive in the finite descent factor. Conversely, a representation with trivial wild inertia need not be unramified; a nonzero tame monodromy operator gives infinite unipotent tame inertia.

### 11.3 The sharp nilpotence bound

For any $\sigma\in I_K$, choose $m>0$ with $\sigma^m\in I'$. Then

$$
(\rho_\ell(\sigma)^m-1)^2=0.
\tag{11.3}
$$

Therefore every eigenvalue of $\rho_\ell(\sigma)$ is an $m$th root of unity, and every Jordan block has size at most two. The block-size assertion follows because taking a nonzero power in characteristic zero preserves the size of a Jordan block attached to a nonzero eigenvalue. Thus abelian varieties satisfy a stronger statement than bare quasi-unipotence:

$$
\text{finite-order eigenvalues, with nilpotent blocks of length at most two.}
\tag{11.4}
$$

The bound two is sharp. The Tate curve has a nontrivial $2\times2$ unipotent block. Good reduction has blocks of size one. Products show that arbitrarily many independent size-two blocks may occur, but no block can grow to size three.

For a semistable variety the number of nontrivial size-two blocks is exactly $t$, because $\operatorname{rank}N_A=t$. After a nonsemistable descent, finite eigenspaces can mix these blocks, so the toric rank should be read after reaching a semistable field.

### 11.4 The Weil-Deligne form when the residue field is finite

Assume now that $k$ is finite of order $q$. Let $W_K$ be the Weil group. Choose geometric Frobenius $F$, so $|F|=q^{-1}$. Quasi-unipotence permits the inertial action to be written as a finite representation together with a nilpotent operator:

$$
(r,N),
\qquad
r:W_K\longrightarrow\operatorname{GL}(V_\ell A),
\qquad
r(w)Nr(w)^{-1}=|w|N.
\tag{11.5}
$$

Here $r|_{I_K}$ has finite image and $N^2=0$. To construct it, pass to a semistable extension, choose a scalar coordinate on the tame character, and set on an open inertial subgroup

$$
r(\sigma)=\rho_\ell(\sigma)
\exp(-t_\ell(\sigma)N).
$$

The two factors cancel there, so $r$ has finite inertial image. Extend over $W_K$ using Frobenius; conjugation of the tame character gives the relation in (11.5). Changing the scalar coordinate conjugates the presentation in the usual way but not its isomorphism class.

For semistable reduction over $K$, $r$ is unramified and all inertia is carried by $N$. For potentially good reduction, $N=0$ after a finite extension and all inertial information is finite. In general both occur. Arithmetic Frobenius replaces $F$ by $F^{-1}$ and reverses the norm convention; formula (11.5) is stated with geometric Frobenius to fix the sign and scalar once and for all.

## 12. Conductors of abelian varieties

A conductor must count both the directions already lost at inertia level zero and the additional depth of wild motion. The fixed-part theorem computes the first number from the Neron special fiber; upper ramification computes the second. Their sum yields the conductor formula and makes its independence of the auxiliary prime transparent.

### 12.1 Artin and Swan conductors for a quasi-unipotent representation

The finite-image conductor of ramification theory must be adjusted only slightly. Let $V$ be a characteristic-zero $\ell$-adic representation of $G_K$ whose inertia action is quasi-unipotent. Assume the classical upper ramification filtration is available, for example that $k$ is perfect. Wild inertia has finite image in the representations arising from abelian varieties, so define

$$
\operatorname{Sw}_K(V)
=\int_{0}^{\infty}
\operatorname{codim}V^{G_K^u}\,du.
\tag{12.1}
$$

The integral is a finite sum in any finite quotient through which wild inertia acts. Upper-numbering compatibility makes it independent of that quotient. Define

$$
a_K(V)=\operatorname{codim}V^{I_K}
+\operatorname{Sw}_K(V).
\tag{12.2}
$$

The first term is called the tame or moderate part, even though it includes the loss of invariants from finite tame descent and from unipotent tame monodromy. The second term measures only positive-depth wild ramification.

For an abelian variety put

$$
f_K(A)=a_K(V_\ell A),
\qquad
\delta_K(A)=\operatorname{Sw}_K(V_\ell A).
\tag{12.3}
$$

The notation $\delta_K(A)$ here denotes the wild conductor of the abelian variety, not a field discriminant exponent. To avoid ambiguity in calculations we will usually write $\operatorname{Sw}_K(A)$.

The integral in (12.1) is an integer for these representations. One way to see this is to compute in the finite wild quotient and apply the Artin-character integrality theorem from ramification theory. The infinite unipotent tame part never enters the positive-depth sum.

### 12.2 The tame codimension

Theorem 4.1 and formula (4.5) immediately give

$$
\boxed{
\operatorname{codim}(V_\ell A)^{I_K}=t+2u.}
\tag{12.4}
$$

This formula is valid for every reduction type, with $(a,t,u)$ computed geometrically on the connected special fiber over $k^s$. Its proof did not require potential semistability, but potential semistability explains the representation-theoretic shape behind it.

Three cases are worth separating.

- Good reduction: $(a,t,u)=(g,0,0)$, so the tame codimension is zero.
- Semistable reduction: $(a,t,u)=(g-t,t,0)$, so it is $t$.
- Purely additive connected reduction: $(a,t,u)=(0,0,g)$, so it is $2g$.

The last line says that inertia has no fixed vector in $V_\ell A$, not that its action is necessarily wild. An elliptic curve with tame additive reduction has conductor two and Swan conductor zero.

### 12.3 The conductor formula

The conductor separates into a tame loss of fixed vectors and a wild depth. The fixed-part theorem has already computed the first summand geometrically, so the formula below assembles the two measurements without hiding either one.

**Theorem 12.1 (conductor formula).** Let $K$ have perfect residue field and let $A/K$ be an abelian variety. For every $\ell\ne p$,

$$
\boxed{
f_K(A)=t(A)+2u(A)+\operatorname{Sw}_K(A)
}
\tag{12.5}
$$

**Proof.** By definition,

$$
f_K(A)=\operatorname{codim}(V_\ell A)^{I_K}
+\operatorname{Sw}_K(V_\ell A).
$$

Formula (12.4) identifies the first term with $t+2u$. This gives (12.5). $\square$

The brevity of the final proof reflects the work already done. The fixed-part theorem translated inertia invariants into the connected Neron fiber, while ramification theory isolated the wild depth. Neither term has been guessed from examples.

One also obtains the bounds

$$
f_K(A)\ge t+2u,
\tag{12.6}
$$

with equality exactly when wild inertia acts trivially, and

$$
f_K(A)=0\Longleftrightarrow A\text{ has good reduction}.
\tag{12.7}
$$

For the reverse implication in (12.7), conductor zero makes inertia invariants have full dimension and Swan zero. The good reduction criterion then applies.

### 12.4 The semistable formula

If $A$ is semistable, then $u=0$ and Theorem 5.2 makes wild inertia trivial. Therefore

$$
\boxed{f_K(A)=t(A).}
\tag{12.8}
$$

Equivalently,

$$
f_K(A)=\operatorname{rank}N_A
=\operatorname{codim}(V_\ell A)^{I_K}.
\tag{12.9}
$$

This is the conductor formula most often used in semistable arithmetic. It says that the conductor counts toric directions, not component-group order and not the determinant of the monodromy pairing. A Tate curve with parameter of valuation $1$ and one with parameter of valuation $100$ both have conductor exponent one, although their component groups have orders $1$ and $100$.

Under a ramified extension, the monodromy pairing scales but toric rank does not. Thus a semistable conductor remains $t$ under every finite scalar extension even though the component group generally grows. Conductors measure the dimension and depth of moved directions; component groups measure an integral period index.

### 12.5 Independence, additivity, and isogeny

The terms $t$ and $u$ are geometric and independent of $\ell$. The Swan term is independent of $\ell$ as well.

**Proposition 12.2.** For an abelian variety over a field with perfect residue field, $\operatorname{Sw}_K(V_\ell A)$ and $f_K(A)$ are independent of $\ell\ne p$.

**Proof strategy.** Pass to a finite Galois extension $L/K$ where $A$ is semistable. Wild inertia acts through a finite $p$-group $H$ on the Raynaud one-motive over $L$. For $h\in H$, the trace on $V_\ell A$ is the sum of traces on the three rational graded pieces

$$
X^\vee\otimes\mathbf Q_\ell(1),
\qquad V_\ell B,
\qquad Y\otimes\mathbf Q_\ell.
\tag{12.10}
$$

The lattice traces are integral and independent of $\ell$. The trace of a finite-order automorphism $h$ on $V_\ell B$ is independent of $\ell$: its characteristic polynomial is recovered from the degrees

$$
\deg(n-h)=\det(n-h\mid V_\ell B)
$$

for sufficiently many integers $n$, and those degrees are geometric integers independent of $\ell$. Hence the character of $H$ on $V_\ell A$ is independent of $\ell$.

For every ramification subgroup $H^u$, averaging its character gives

$$
\dim(V_\ell A)^{H^u}
=\frac1{|H^u|}\sum_{h\in H^u}\operatorname{Tr}(h\mid V_\ell A),
$$

which is independent of $\ell$. The upper-depth integral (12.1) is therefore independent of $\ell$. Formula (12.5) gives the same conclusion for $f_K(A)$. $\square$

Products give direct sums of Tate representations and products of connected Neron fibers, so

$$
f_K(A\times C)=f_K(A)+f_K(C).
\tag{12.11}
$$

An isogeny induces an isomorphism $V_\ell A\simeq V_\ell C$ for every $\ell$ after tensoring with $\mathbf Q_\ell$, even when $\ell$ divides the isogeny degree. Hence

$$
f_K(A)=f_K(C),
\qquad
\operatorname{Sw}_K(A)=\operatorname{Sw}_K(C).
\tag{12.12}
$$

The conductor is therefore an isogeny invariant, while the component group is not. This contrast is one of the main reasons to keep the rational monodromy operator separate from its integral lattice map.

## 13. Exact examples

The abstract package is most reliable when its several invariants are checked independently. The examples below compare monodromy rank, integral period length, component discriminant, and conductor. They also show why none of these four quantities can be substituted blindly for another.

### 13.1 Good reduction

If $A$ extends to an abelian scheme, then $T=Y=0$ in Raynaud uniformization and $A=B$. The one-motive is $[0\to A]$, so

$$
W_{-2}=0,\qquad W_{-1}=W_0=T_\ell A,\qquad N_A=0.
$$

The monodromy and component pairings are zero-dimensional, inertia is trivial, and

$$
\Phi_A=0,\qquad f_K(A)=0.
$$

Frobenius can still act nontrivially when $k$ is finite. Good reduction means unramified, not trivial, Galois action.

### 13.2 The Tate curve

Let $E_q$ be the Tate curve with $0<|q|<1$. Then

$$
T=\mathbf G_m,\qquad B=0,\qquad X=Y=\mathbf Z,
$$

and

$$
\mu(1,1)=v_K(q)=n>0.
\tag{13.1}
$$

The Tate-module sequence is

$$
0\longrightarrow\mathbf Z_\ell(1)
\longrightarrow T_\ell E_q
\longrightarrow\mathbf Z_\ell\longrightarrow0.
\tag{13.2}
$$

Choose a basis $e_{-2},e_0$ compatible with this sequence. After choosing a scalar coordinate on $\mathbf Z_\ell(1)$,

$$
N(e_0)=n e_{-2},\qquad N(e_{-2})=0,
$$

and

$$
\rho_\ell(\sigma)=
\begin{pmatrix}
1&n t_\ell(\sigma)\\
0&1
\end{pmatrix}.
\tag{13.3}
$$

The component sequence is

$$
0\to\mathbf Z\xrightarrow{n}\mathbf Z
\to\Phi_{E_q}(k^s)\to0,
$$

so

$$
\Phi_{E_q}(k^s)\simeq\mathbf Z/n\mathbf Z,
\qquad f_K(E_q)=1.
\tag{13.4}
$$

The component pairing sends $(\bar a,\bar b)$ to $ab/n$ modulo $\mathbf Z$. Ramified base change of index $e$ replaces $n$ by $en$ and leaves the conductor equal to one.

### 13.3 Nonsplit multiplicative reduction and products

For nonsplit multiplicative reduction, $X\simeq\mathbf Z$ geometrically but residue Frobenius acts by $-1$. Inertia still acts by a rank-one unipotent shear, because the torus splits over an unramified quadratic extension. Thus

$$
t=1,\qquad f_K(E)=1,
$$

while the $k$-rational component group is the invariant subgroup of the geometric cyclic group under sign. Geometric monodromy and rational components must not be identified.

For a product of Tate curves with parameters $q_1,\ldots,q_r$, the monodromy matrix is diagonal in the product basis:

$$
\operatorname{diag}(v(q_1),\ldots,v(q_r)).
$$

Hence

$$
\Phi(k^s)\simeq
\bigoplus_{i=1}^r\mathbf Z/v(q_i)\mathbf Z,
\qquad
f_K(A)=r.
$$

An isogeny can replace this diagonal lattice by a non-diagonal finite-index lattice. Smith normal form, not the determinant alone, is then required to recover the component group.

### 13.4 Jacobians and weighted graphs

Let $J$ be the Jacobian of a split semistable curve with weighted dual graph $\Gamma$. Put

$$
r=b_1(\Gamma).
$$

Then

$$
\operatorname{rank}N_J=r,
\qquad
f_K(J)=r,
\tag{13.5}
$$

and the component group is the discriminant group of

$$
q_\Gamma(c,c')=\sum_en_ec_ec'_e.
$$

If $\Gamma$ is a tree, $r=0$: the curve can have a singular special fiber while its Jacobian has good reduction. If $\Gamma$ is one loop of total length $n$, then $J$ has one toric direction, conductor one, and component group $\mathbf Z/n\mathbf Z$. If every normalized component has genus zero, the Jacobian is totally degenerate and the middle graded piece $T_\ell B$ vanishes.

For two vertices joined by $r$ unit edges, the toric rank is $r-1$ and the graph component group is $\mathbf Z/r\mathbf Z$. The conductor is $r-1$, not $r$ and not the order of the component group.

### 13.5 Additive reduction

Let $E/K$ be an elliptic curve with additive reduction. Over $k^s$ its connected Neron fiber has

$$
(a,t,u)=(0,0,1).
$$

Thus

$$
\operatorname{codim}(V_\ell E)^{I_K}=2,
\qquad
f_K(E)=2+\operatorname{Sw}_K(E).
\tag{13.6}
$$

In residue characteristic at least five, the usual potentially good additive types are tamely ramified, so the Swan term is zero and the conductor is two. In residue characteristics two and three, wild inertia can act nontrivially and the conductor can be larger. Formula (13.6) isolates the source of the increase without relying on a list of fiber symbols.

After a finite extension, $E$ becomes good or multiplicative. In the first case the eventual monodromy operator is zero and the original inertia was finite. In the second case the eventual operator has rank one, while the original finite descent factor made the reduction additive. Thus the same additive connected fiber over $K$ can conceal either potentially good or potentially multiplicative behavior; one must inspect the semistable extension or the quasi-unipotent representation.

## 14. Functoriality and hypothesis control

Monodromy is useful only if it survives the ordinary operations on abelian varieties. This chapter records compatibility with morphisms, duality, isogeny, and scalar extension, then gathers the hypothesis boundaries that govern every formula. The goal is a reusable theory whose normalizations remain stable in later applications.

### 14.1 Morphisms and monodromy

Let $f:A\to C$ be a homomorphism. After one finite extension both varieties are semistable. Functoriality of Raynaud uniformization gives maps on tori, good-reduction parts, and periods, and equation (7.10) gives

$$
N_C\,V_\ell(f)=V_\ell(f)(-1)N_A.
\tag{14.1}
$$

Therefore kernels, images, and isogeny factors inherit their monodromy filtrations. If $f$ is an isogeny, $V_\ell(f)$ is an isomorphism and conjugates the rational monodromy operators. It need not identify the integral maps $Y\to X^\vee$, because its maps on lattices can have finite cokernel.

For a polarized correspondence, the transpose correspondence acts as the adjoint for the monodromy form. On semistable Jacobians this recovers the adjunction between harmonic graph pullback and pushforward. The generic homomorphism always extends to Neron models; reading its action on a chosen special-fiber graph additionally requires a controlled extension of the curve correspondence.

### 14.2 Duality and component groups

Duality exchanges $X$ and $Y$, transposes $N$, and preserves conductor:

$$
f_K(A^\vee)=f_K(A),
\qquad
\operatorname{Sw}_K(A^\vee)=\operatorname{Sw}_K(A).
\tag{14.2}
$$

The equalities follow either from the perfect Tate pairing, which identifies fixed-space codimensions and wild characters, or from the geometric equalities of abelian, toric, and unipotent ranks for dual reduction.

Component groups are related more subtly. They need not be isomorphic without a principal polarization, but in the semistable case they are perfect duals through (8.7). A polarization gives a map between them; a principal polarization identifies them and makes the induced discriminant pairing perfect and symmetric.

This is a finite pairing on geometric components. Rational component groups are residue-Galois invariants and need not be perfect duals as abstract groups of $k$-points; taking invariants is not an exact operation, and a component torsor can fail to have a rational point over a general residue field.

### 14.3 Base-change bookkeeping

Let $L/K$ be finite. The principal transformations are:

$$
\begin{array}{c|c}
\text{datum}&\text{behavior once }A/K\text{ is semistable}\\
\hline
a,t&\text{unchanged}\\
X,Y&\text{same lattices with restricted residue action}\\
\mu,N&\text{multiplied by }e(L/K)\text{ under integral normalization}\\
\Phi&\text{cokernel of the scaled lattice map}\\
f_L(A_L)=t&\text{the same toric-rank value over the new field}.
\end{array}
\tag{14.3}
$$

For unramified extension, $e=1$ and the geometric component group merely base-changes. For ramified extension, even when no lattice splits further,

$$
\Phi_{A_L}(k^s)\simeq X^\vee/e\nu_A(Y).
\tag{14.4}
$$

There is then an exact sequence

$$
0\longrightarrow \nu_A(Y)/e\nu_A(Y)
\longrightarrow X^\vee/e\nu_A(Y)
\longrightarrow X^\vee/\nu_A(Y)
\longrightarrow0.
\tag{14.5}
$$

The first term is canonically $Y/eY$ through the injective map $\nu_A$. Consequently

$$
|\Phi_{A_L}(k^s)|=e^t|\Phi_A(k^s)|
\tag{14.6}
$$

when the geometric lattices do not otherwise change. Sequence (14.5), rather than only (14.6), records how old invariant factors are enlarged.

If $A$ is not semistable over $K$, base change can remove a unipotent radical, change the finite inertial type, and reduce the Swan conductor. No formula involving only the old values of $(a,t,u)$ and the ramification index determines the new conductor.

### 14.4 A hypothesis ledger

The main statements are safe under the following boundaries.

**Valuation and residue field.** Completeness and discreteness are used for uniformization and normalized integral lengths. Classical upper ramification and Swan formulas are stated when finite residue extensions are separable; perfection of $k$ guarantees this. Finite $k$ is required only for a distinguished Frobenius and the Weil--Deligne formulation.

**The auxiliary prime.** Every Tate-module, fixed-part, and Kummer statement assumes $\ell\ne p$. At $\ell=p$, formal and connected finite group schemes require a different theory.

**Semistability.** The three-step Raynaud filtration, square-zero formula over all inertia, integral monodromy pairing, and component presentation (8.3) require semistable reduction over the field in question. For an arbitrary abelian variety they apply only after a finite semistable extension, with finite descent retained.

**Splitting.** Coordinate formulas use split tori over $K^{\mathrm{nr}}$. Over $K$, $X$ and $Y$ are residue-Galois lattices. Geometric component groups carry that action; their $k$-points are invariants, not automatically the whole group.

**Polarizations.** The basic pairing $\mu_A:Y\times X\to\mathbf Z$ is nonsymmetric. Symmetry and positivity arise only after a polarization. Principality identifies the lattices but does not force the monodromy matrix to be unimodular.

**Components versus conductors.** Component groups depend on the integral index of $Y\to X^\vee$. Conductors depend on invariant codimension and wild depth. Isogenies preserve the latter and can change the former.

**Finite-level tests.** Triviality modulo $\ell$ for $\ell\ge3$, or modulo $4$ for $\ell=2$, kills finite semisimple inertia and yields semistability. It does not kill the integral unipotent monodromy operator and therefore does not by itself prove good reduction.

## 15. The monodromy package

The final chapter assembles the geometric, integral, and Galois constructions into one dictionary. It also gives a calculation order that keeps rational monodromy, integral components, residue descent, and wild depth separate until the exact formulas legitimately join them.

### 15.1 The structural dictionary

For a semistable abelian variety, the theory may be summarized by one commutative package:

$$
\begin{array}{ccccccccc}
0&\to&T&\to&E&\to&B&\to&0\\
&&\downarrow&&\downarrow&&\downarrow&&\\
0&\to&Y&\to&E&\to&A^{\mathrm{an}}&\to&0,
\end{array}
$$

with the lower left arrow understood as the period embedding rather than a map into $T$ alone. Its realizations are

$$
0\subset X^\vee\otimes\mathbf Z_\ell(1)
\subset T_\ell E\subset T_\ell A,
\tag{15.1}
$$

$$
N_A:
T_\ell A\twoheadrightarrow Y\otimes\mathbf Z_\ell
\xrightarrow{\nu_A}X^\vee\otimes\mathbf Z_\ell
\hookrightarrow T_\ell A(-1),
\tag{15.2}
$$

and

$$
0\longrightarrow Y\xrightarrow{\nu_A}X^\vee
\longrightarrow\Phi_A(k^s)\longrightarrow0.
\tag{15.3}
$$

Thus the same map $\nu_A$ has three readings:

$$
\begin{array}{c|c}
\text{setting}&\text{meaning}\\
\hline
\text{analytic}&\text{valuation of a period}\\
\text{Galois}&\text{square-zero monodromy operator}\\
\text{integral geometry}&\text{presentation of the component group}.
\end{array}
\tag{15.4}
$$

Duality transposes $\nu_A$. A polarization turns it into a symmetric positive form. A principal polarization identifies its two lattices, while its discriminant remains the component group.

For arbitrary reduction, potential semistability gives quasi-unipotence, and the fixed-part theorem gives

$$
\dim(V_\ell A)^{I_K}=2a+t,
\qquad
f_K(A)=t+2u+\operatorname{Sw}_K(A).
\tag{15.5}
$$

These formulas recover good reduction, semistability, and wild additive degeneration from one representation without confusing their distinct causes.

### 15.2 A calculation protocol

Given an abelian variety over $K$, first determine the connected Neron special fiber and record $(a,t,u)$ together with the residue action on its torus. This immediately gives the dimension of inertia invariants and the tame conductor $t+2u$.

If the variety is semistable, construct or identify its Raynaud data. Determine the two lattices $X=X^*(T_A)$ and $Y=X^*(T_{A^\vee})$. Evaluate periods through characters or the Poincare trivialization and take normalized valuations to form

$$
\mu_A:Y\times X\to\mathbf Z.
$$

Check that its rational determinant is nonzero. The associated map $Y\to X^\vee$ gives the monodromy operator after tensoring with $\mathbf Z_\ell$, while its Smith normal form gives the geometric component group. Under a polarization, verify symmetry and positivity before treating the matrix as a quadratic form.

For the Tate representation, use

$$
\rho_\ell(\sigma)=1+t_\ell(\sigma)N_A.
$$

Its invariant kernel has codimension $t$, wild inertia is trivial, and the conductor is $t$. Under ramified base change, multiply the integral pairing and $N$ by the ramification index while changing the tame character in the inverse way.

If the original reduction is not semistable, pass to a finite Galois semistable field and retain the finite descent action. The open inertia subgroup has square-zero logarithm; the finite wild part contributes the Swan conductor. Do not compute the original conductor from the eventual toric rank alone: the finite descent action can contribute both invariant loss and wild depth.

### 15.3 Conclusion

Semistable degeneration of an abelian variety is controlled by two lattices around a good-reduction abelian core. The Raynaud extension supplies the torus and the bounded abelian part; the period lattice restores properness. Packaging the period map and the semiabelian group as a one-motive produces a three-step Tate-module filtration with toric, abelian, and lattice graded pieces.

Inertia is then explicit. Roots of unit parts of periods are unramified, while roots of their valuations are governed by the tame character. The resulting monodromy operator lowers the filtration by two, has square zero, and has rank equal to the toric rank. Its integral source is the monodromy pairing between the toric character lattices of $A$ and $A^\vee$. The cokernels of that pairing and its transpose are the two component groups, and elementary lattice duality makes their pairing perfect. Polarizations convert the nonsymmetric dual pairing into a symmetric positive form; semistable Jacobians recover the weighted cycle pairing of their reduction graphs.

Every abelian variety becomes semistable after a finite separable extension: a sufficiently ample curve makes it an isogeny factor of a Jacobian, semistable reduction of the curve makes that Jacobian semistable, and semistability survives isogeny factors. This geometric theorem yields quasi-unipotence of every prime-to-residue-characteristic Tate module, with Jordan blocks of size at most two. It also turns unipotent inertia into a criterion for semistable reduction and trivial inertia into the good reduction criterion.

Finally, the Neron fixed-part theorem identifies inertia invariants with the prime-to-residue-characteristic Tate module of the connected special fiber. The abelian and toric layers contribute rank $2a+t$, the unipotent layer contributes none, and ramification theory supplies the remaining wild depth. The conductor formula

$$
f_K(A)=t+2u+\operatorname{Sw}_K(A)
$$

therefore joins integral geometry and Galois ramification without collapsing their distinctions. For semistable reduction it becomes $f_K(A)=t$; at the same time, the full integral monodromy matrix retains the finer component and polarization data. This is the complete local monodromy package needed to pass from degeneration of abelian varieties to their Galois representations.
