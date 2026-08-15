# Parabolic Induction, Jacquet Modules, and Whittaker Models for $\mathrm{GL}_2$

## Contents

1. [The rank-one local machine](#1-the-rank-one-local-machine)
   - [The problem and its three coordinate systems](#11-the-problem-and-its-three-coordinate-systems)
   - [Standing hypotheses](#12-standing-hypotheses)
   - [The normalization ledger](#13-the-normalization-ledger)
   - [What will be proved](#14-what-will-be-proved)
2. [The geometry of the Borel](#2-the-geometry-of-the-borel)
   - [The four basic subgroups](#21-the-four-basic-subgroups)
   - [Iwasawa and Bruhat decompositions](#22-iwasawa-and-bruhat-decompositions)
   - [Coordinates on the open cell](#23-coordinates-on-the-open-cell)
   - [Measures under conjugation](#24-measures-under-conjugation)
3. [Normalized and unnormalized principal series](#3-normalized-and-unnormalized-principal-series)
   - [Why there are two conventions](#31-why-there-are-two-conventions)
   - [The induced and compact pictures](#32-the-induced-and-compact-pictures)
   - [Admissibility, central character, and twisting](#33-admissibility-central-character-and-twisting)
   - [Contragredients and the invariant pairing](#34-contragredients-and-the-invariant-pairing)
   - [First examples and a normalization counterexample](#35-first-examples-and-a-normalization-counterexample)
4. [The rank-one geometric lemma](#4-the-rank-one-geometric-lemma)
   - [Why cells should give a filtration](#41-why-cells-should-give-a-filtration)
   - [The open-cell model](#42-the-open-cell-model)
   - [Coinvariants of the two cells](#43-coinvariants-of-the-two-cells)
   - [The geometric lemma](#44-the-geometric-lemma)
   - [What the lemma does and does not imply](#45-what-the-lemma-does-and-does-not-imply)
5. [Jacquet functors and adjunction](#5-jacquet-functors-and-adjunction)
   - [Ordinary and twisted coinvariants](#51-ordinary-and-twisted-coinvariants)
   - [Exactness of the Jacquet functor](#52-exactness-of-the-jacquet-functor)
   - [Normalized Jacquet modules](#53-normalized-jacquet-modules)
   - [Frobenius reciprocity in Jacquet form](#54-frobenius-reciprocity-in-jacquet-form)
   - [Consequences for principal series](#55-consequences-for-principal-series)
6. [Standard intertwining operators](#6-standard-intertwining-operators)
   - [The convergent integral](#61-the-convergent-integral)
   - [Shells and rational continuation](#62-shells-and-rational-continuation)
   - [The spherical scalar](#63-the-spherical-scalar)
   - [Composition and Weyl symmetry](#64-composition-and-weyl-symmetry)
   - [Poles are not reducibility](#65-poles-are-not-reducibility)
7. [Reducibility and the special representation](#7-reducibility-and-the-special-representation)
   - [The boundary-functional calculation](#71-the-boundary-functional-calculation)
   - [The reducibility theorem](#72-the-reducibility-theorem)
   - [The two exceptional exact sequences](#73-the-two-exceptional-exact-sequences)
   - [The projective-line model](#74-the-projective-line-model)
   - [Jacquet modules of the constituents](#75-jacquet-modules-of-the-constituents)
8. [Whittaker functionals and uniqueness](#8-whittaker-functionals-and-uniqueness)
   - [Why ordinary coinvariants miss oscillation](#81-why-ordinary-coinvariants-miss-oscillation)
   - [Whittaker functionals and models](#82-whittaker-functionals-and-models)
   - [The rank-one distribution lemma](#83-the-rank-one-distribution-lemma)
   - [Uniqueness](#84-uniqueness)
   - [Existence for principal and special representations](#85-existence-for-principal-and-special-representations)
   - [Genericity and its boundary](#86-genericity-and-its-boundary)
9. [The Kirillov model](#9-the-kirillov-model)
   - [Restriction to the diagonal](#91-restriction-to-the-diagonal)
   - [The mirabolic action](#92-the-mirabolic-action)
   - [The compactly supported core](#93-the-compactly-supported-core)
   - [Jacquet modules as asymptotic data](#94-jacquet-modules-as-asymptotic-data)
   - [Principal, special, and cuspidal tails](#95-principal-special-and-cuspidal-tails)
10. [The Weyl transform](#10-the-weyl-transform)
    - [Why the missing generator matters](#101-why-the-missing-generator-matters)
    - [The contragredient Whittaker model](#102-the-contragredient-whittaker-model)
    - [Fourier behavior on compact Kirillov functions](#103-fourier-behavior-on-compact-kirillov-functions)
    - [Support exchanged with oscillation](#104-support-exchanged-with-oscillation)
11. [Spherical vectors and the rank-one Casselman--Shalika formula](#11-spherical-vectors-and-the-rank-one-casselman--shalika-formula)
    - [The spherical line](#111-the-spherical-line)
    - [The first Hecke operator](#112-the-first-hecke-operator)
    - [The Whittaker recurrence](#113-the-whittaker-recurrence)
    - [The closed formula and generating series](#114-the-closed-formula-and-generating-series)
    - [Degenerate and exceptional parameters](#115-degenerate-and-exceptional-parameters)
12. [One-dimensional local zeta integrals](#12-one-dimensional-local-zeta-integrals)
    - [Schwartz functions and Fourier transform](#121-schwartz-functions-and-fourier-transform)
    - [Tate integrals and their rationality](#122-tate-integrals-and-their-rationality)
    - [The local functional equation](#123-the-local-functional-equation)
    - [Unramified and ramified constants](#124-unramified-and-ramified-constants)
    - [Changing the additive character](#125-changing-the-additive-character)
13. [Whittaker zeta integrals for $\mathrm{GL}_2$](#13-whittaker-zeta-integrals-for-mathrmgl_2)
    - [The half-power in the integral](#131-the-half-power-in-the-integral)
    - [Rationality and the zeta ideal](#132-rationality-and-the-zeta-ideal)
    - [The local factor from Kirillov tails](#133-the-local-factor-from-kirillov-tails)
    - [Test vectors and a vanishing warning](#134-test-vectors-and-a-vanishing-warning)
14. [Functional equations for $\mathrm{GL}_2$](#14-functional-equations-for-mathrmgl_2)
    - [The transformed Whittaker function](#141-the-transformed-whittaker-function)
    - [The local functional equation](#142-the-local-functional-equation)
    - [Principal-series factorization](#143-principal-series-factorization)
    - [The special representation as a limiting case](#144-the-special-representation-as-a-limiting-case)
    - [Dependence on measures and additive characters](#145-dependence-on-measures-and-additive-characters)
15. [Worked local calculations](#15-worked-local-calculations)
    - [An unramified principal series](#151-an-unramified-principal-series)
    - [Equal Satake parameters](#152-equal-satake-parameters)
    - [The two reducible orderings](#153-the-two-reducible-orderings)
    - [A ramified character in one slot](#154-a-ramified-character-in-one-slot)
    - [An unramified special representation](#155-an-unramified-special-representation)
16. [A reusable rank-one dictionary](#16-a-reusable-rank-one-dictionary)

- [Geometry, quotients, and Fourier coefficients](#161-geometry-quotients-and-fourier-coefficients)
- [Normalization conversion table](#162-normalization-conversion-table)
- [Hypotheses that cannot be dropped](#163-hypotheses-that-cannot-be-dropped)
- [Conclusion](#164-conclusion)

## 1. The rank-one local machine

### 1.1 The problem and its three coordinate systems

The upper triangular subgroup of $\mathrm{GL}_2(F)$ is small enough to understand and large enough to generate most of the representations visible in rank one. Inducing a character of its diagonal torus produces a principal series. Dividing a representation by the action of its upper unipotent subgroup produces a Jacquet module. Taking a nontrivial Fourier coefficient along that same unipotent subgroup produces a Whittaker model. These operations look different, but they are three readings of the same two-cell geometry.

The first reading is geometric. The flag variety $B\backslash G$ has two $B$-orbits. The closed orbit remembers the inducing character in its original order; the open orbit remembers the Weyl-conjugate character. This is the rank-one geometric lemma.

The second reading is categorical. Ordinary unipotent coinvariants are exact and, after a half-modular twist, are adjoint to normalized induction. They therefore detect precisely when an irreducible representation can enter a principal series.

The third reading is Fourier-theoretic. Ordinary coinvariants retain the zero-frequency term along the unipotent group. Whittaker coinvariants retain a nonzero frequency. Passing from a Whittaker function to its values on the diagonal gives the Kirillov model, in which translations, dilations, asymptotic exponents, and local zeta integrals become one-variable calculations on $F^\times$.

The purpose of this book is to build that machine with every normalization visible. The reward is not merely a list of representations. It is a method: Bruhat cells give filtrations, Jacquet modules give exponents, Whittaker uniqueness gives canonical Fourier coordinates, and local functional equations describe the action of the Weyl element in those coordinates.

### 1.2 Standing hypotheses

Throughout, $F$ is a nonarchimedean local field. Write

$$
\mathcal O=\mathcal O_F,\qquad \mathfrak p=(\varpi),\qquad
k=\mathcal O/\mathfrak p,\qquad |k|=q,
$$

and normalize

$$
v(\varpi)=1,\qquad |x|=q^{-v(x)}.
$$

The structural representation theory is valid over an algebraically closed characteristic-zero field containing $q^{1/2}$. Whenever convergence, absolute values of Gauss sums, or a complex variable $s$ occurs, the coefficient field is $\mathbf C$. All multiplicative characters are smooth. In analytic statements they are written uniquely as a unitary character times $|\cdot|^u$ after a choice of logarithm for the unramified value.

Put

$$
G=\mathrm{GL}_2(F),\qquad K=\mathrm{GL}_2(\mathcal O).
$$

Representations are smooth left representations. In an induced function model the action is by right translation:

$$
(\pi(g_0)f)(g)=f(gg_0).
$$

This convention fixes the signs in the Jacquet integral and the location of inverses in the contragredient model.

We assume the general facts about smooth representations of totally disconnected locally compact groups: compact-open averaging in characteristic zero, exactness of compact-open invariants, smooth contragredients, Haar convolution, compact induction, and Frobenius reciprocity. Everything specific to the Borel of $G$ is proved here.

### 1.3 The normalization ledger

Choose once and for all a nontrivial additive character

$$
\psi:F\longrightarrow\mathbf C^\times
$$

that is trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$. Let $dx$ be the self-dual additive Haar measure for the pairing $(x,y)\mapsto\psi(xy)$. With this conductor convention,

$$
\operatorname{vol}_{dx}(\mathcal O)=1.
$$

Define multiplicative Haar measure by

$$
d^\times x=\frac{1}{1-q^{-1}}\frac{dx}{|x|}.
$$

Then

$$
\operatorname{vol}_{d^\times x}(\mathcal O^\times)=1,
\qquad
\operatorname{vol}_{d^\times x}(\varpi^m\mathcal O^\times)=1
$$

for every $m\in\mathbf Z$. Haar measure on $K$ is normalized by $\operatorname{vol}(K)=1$. The standard intertwining integral uses the displayed $dx$ on $N\cong F$.

The parabolic modulus is

$$
\delta_B\left(\begin{pmatrix}a&b\\0&d\end{pmatrix}\right)=|a/d|.
$$

This is the inverse of the group modular character of $B$ for left Haar measure. Normalized induction uses $\delta_B^{1/2}$, while the normalized Jacquet functor uses $\delta_B^{-1/2}$. These are not choices made independently: adjunction forces them to be inverse.

Whenever $X=q^{-s}$, a rational function of $q^{-s}$ means an element of $\mathbf C(X)$. Thus analytic continuation of a local integral is an elementary rational continuation in one variable.

### 1.4 What will be proved

The principal series will be treated in both conventions. The rank-one geometric lemma will compute its Jacquet module. Exactness and adjunction will explain why these modules govern subrepresentations and quotients. A shell-by-shell construction of the standard intertwiner will locate the reducibility points $|\cdot|^{\pm1}$ in normalized coordinates and $1,|\cdot|^2$ in unnormalized coordinates.

Whittaker uniqueness will be reduced to a distribution statement on the two Bruhat cells. The Jacquet integral will give existence for principal series and the special constituent; within the spectrum generated from the Borel, the rank-one Fourier argument will identify the one-dimensional representations as the obstruction to genericity. The Kirillov model will then turn the action of $B$ into translations and dilations on $F^\times$ and turn the Jacquet module into asymptotic data at zero.

Finally, spherical Whittaker functions and local zeta integrals will be calculated with the measures just fixed. The one-dimensional functional equation will be proved first. Two applications of it will give the principal-series functional equation, including the special representation at the reducibility boundary. No unexplained local constant will be smuggled into the notation: every gamma factor will either be defined by a displayed functional equation or reduced to an explicit Tate gamma factor.

## 2. The geometry of the Borel

### 2.1 The four basic subgroups

The line $Fe_1$ has stabilizer

$$
B=TN,
$$

where

$$
T=\left\{t(a,d)=\begin{pmatrix}a&0\\0&d\end{pmatrix}:a,d\in F^\times\right\},
\qquad
N=\left\{n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}:x\in F\right\}.
$$

The opposite unipotent group and a Weyl representative are

$$
\bar N=\left\{\bar n(y)=\begin{pmatrix}1&0\\y&1\end{pmatrix}:y\in F\right\},
\qquad
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

Conjugation by the torus reads

$$
t(a,d)n(x)t(a,d)^{-1}=n(ad^{-1}x).
$$

This one formula is responsible for both the modulus and the dilation action in the Kirillov model. The center consists of $zI_2$, so a torus character $\chi_1\boxtimes\chi_2$ restricts to the central character $\chi_1\chi_2$.

The quotient $B\backslash G$ is the projective line of one-dimensional quotients of $F^2$. Compactness of $\mathbf P^1(F)$ will ensure that ordinary and compact induction from $B$ coincide. The space is compact but not finite; its arbitrarily small balls are the source of infinite-dimensional principal series.

### 2.2 Iwasawa and Bruhat decompositions

Two decompositions answer different questions.

**Proposition 2.1 (Iwasawa decomposition).** One has

$$
G=BK.
$$

**Proof strategy.** Use an integral change of basis to simplify the bottom row.

**Proof.** Let $g\in G$. Its bottom row is a nonzero vector of $F^2$. After multiplying on the right by a matrix in $K$, elementary divisor reduction makes that row $(0,d)$. The resulting matrix is upper triangular, so $g=bk$. $\square$

Thus restriction to $K$ determines an induced function. The ambiguity in $g=bk$ is exactly $B\cap K$, which yields the compact picture in Chapter 3.

**Proposition 2.2 (Bruhat decomposition).** There is a disjoint union

$$
G=B\sqcup BwB=B\sqcup BwN.
$$

**Proof strategy.** The lower-left entry decides the cell.

**Proof.** If the lower-left entry of $g$ is zero, then $g\in B$. If it is nonzero, multiplication on the left and right by upper triangular matrices reduces $g$ to $w$. The two cases are disjoint because $B$ preserves $Fe_1$ and $w$ does not. Finally $BwB=BwN$ because $B=T N$ and $wTw^{-1}=T$. $\square$

The closed cell becomes one point in $B\backslash G$. The open cell becomes an affine line. That is why every rank-one calculation has one boundary term and one integral over $F$.

### 2.3 Coordinates on the open cell

The map

$$
F\longrightarrow B\backslash BwB,
\qquad x\longmapsto Bw n(x)
$$

is a bijection. If $Bwn(x)=Bwn(y)$, then $n(x-y)\in w^{-1}Bw\cap N=\{1\}$, so $x=y$. Surjectivity is the last equality in Proposition 2.2.

For an induced function $f$, define its open-cell coordinate

$$
\Phi_f(x)=f(wn(x)).
$$

Right translation by $n(b)$ becomes translation:

$$
\Phi_{\pi(n(b))f}(x)=\Phi_f(x+b).
$$

Right translation by $t(a,d)$ combines dilation with the inducing character. Since

$$
n(x)t(a,d)=t(a,d)n(da^{-1}x),
$$

and $wt(a,d)=t(d,a)w$, the exact multiplier can be read from the covariance law. This calculation will be repeated when normalization matters; its geometric content is simply that the torus scales the affine coordinate by $d/a$.

An open-cell function whose support is closed away from the missing boundary point corresponds to a compactly supported locally constant function on $F$. Functions that approach the boundary have tails on the shells $\varpi^{-m}\mathcal O^\times$. Those tails are where intertwiners can diverge and where Jacquet exponents live.

### 2.4 Measures under conjugation

Because $dx$ is additive Haar measure,

$$
d(cx)=|c|\,dx.
$$

Consequently conjugation by $t(a,d)$ acts on $N$ with Jacobian $|a/d|$. This proves

$$
\delta_B(t(a,d))=|a/d|.
$$

It is useful to verify the sign from first principles. If $B=T\ltimes N$ is equipped with left Haar measure, right translation by $t(a,d)$ changes the $N$-coordinate by $d/a$ and therefore scales measure by $|d/a|$. Thus the group modular character of $B$ is $|d/a|$, while the parabolic modulus is its inverse $|a/d|$ because $G$ itself is unimodular.

This distinction prevents two common errors. The first is to insert $|d/a|^{1/2}$ in normalized induction. The second is to use $|a/d|^{1/2}$ again in the Jacquet functor. Correct adjunction requires the former construction to use $\delta_B^{1/2}$ and the latter to use $\delta_B^{-1/2}$.

## 3. Normalized and unnormalized principal series

### 3.1 Why there are two conventions

Unnormalized induction is the direct categorical construction. For smooth characters $\rho_1,\rho_2:F^\times\to\mathbf C^\times$, set

$$
J(\rho_1,\rho_2)=\operatorname{Ind}_B^G(\rho_1\boxtimes\rho_2).
$$

Its functions satisfy

$$
f\left(\begin{pmatrix}a&b\\0&d\end{pmatrix}g\right)
=\rho_1(a)\rho_2(d)f(g).
$$

Normalized induction distributes the modulus symmetrically between the two diagonal entries. Define

$$
I(\chi_1,\chi_2)=i_B^G(\chi_1\boxtimes\chi_2)
$$

by the covariance law

$$
f\left(\begin{pmatrix}a&b\\0&d\end{pmatrix}g\right)
=|a/d|^{1/2}\chi_1(a)\chi_2(d)f(g).
$$

If $\nu=|\cdot|$, then

$$
I(\chi_1,\chi_2)
=J(\chi_1\nu^{1/2},\chi_2\nu^{-1/2}),
$$

or, equivalently,

$$
J(\rho_1,\rho_2)
=I(\rho_1\nu^{-1/2},\rho_2\nu^{1/2}).
$$

The two representations are the same after this change of variables. What changes is the coordinate used to state symmetry. Normalized reducibility occurs at $\chi_1\chi_2^{-1}=\nu^{\pm1}$; unnormalized reducibility occurs at $\rho_1\rho_2^{-1}=1$ or $\nu^2$. A theorem copied from one convention into the other without this conversion is false.

### 3.2 The induced and compact pictures

Since $B\backslash G$ is compact, no support condition distinguishes induction from compact induction here. Iwasawa decomposition identifies $I(\chi_1,\chi_2)$ with functions $F:K\to\mathbf C$ satisfying

$$
F(bk)=\chi_1(a)\chi_2(d)F(k)
$$

for

$$
b=\begin{pmatrix}a&*\\0&d\end{pmatrix}\in B\cap K.
$$

The modulus disappears on $B\cap K$ because $|a|=|d|=1$. This is the **compact picture**. It shows that the underlying $K$-representation depends only on the restrictions of $\chi_1$ and $\chi_2$ to $\mathcal O^\times$; the values at $\varpi$ enter through the action of elements outside $K$.

**Proposition 3.1.** Every principal series is admissible.

**Proof strategy.** At a fixed compact-open level, the compact picture becomes a function space on a finite double-coset set.

**Proof.** Let $K'\subseteq K$ be compact open. A $K'$-fixed function in the compact picture is determined on

$$
(B\cap K)\backslash K/K'.
$$

This set is finite because $K$ is compact and $K'$ is open. Each value lies in a one-dimensional inducing space and must satisfy only finite compatibility relations. Hence the fixed space is finite-dimensional.

Now let $H\subseteq G$ be any compact open subgroup. The orbit of the standard
lattice under $H$ is compact in the discrete set of lattices, hence finite. The
sum of those finitely many lattices is an $H$-stable lattice. After a change of
basis, $H$ is therefore contained in $K$. The preceding argument applies with
$K'=H$, and conjugation does not change the fixed-space dimension. $\square$

### 3.3 Admissibility, central character, and twisting

Scalar matrices have modulus one. Therefore

$$
\omega_{I(\chi_1,\chi_2)}=\chi_1\chi_2.
$$

If $\mu$ is a smooth character of $F^\times$, use the shorthand

$$
\pi\otimes\mu=\pi\otimes(\mu\circ\det).
$$

Then

$$
I(\chi_1,\chi_2)\otimes\mu
\cong I(\chi_1\mu,\chi_2\mu),
$$

and the central character is multiplied by $\mu^2$. Twisting both inducing characters does not change their ratio, so reducibility is invariant under determinant twists.

The compact picture also locates spherical vectors. If both $\chi_i$ are unramified, there is a unique $K$-fixed vector $f^\circ$ with $f^\circ(1)=1$, defined by

$$
f^\circ(bk)=\delta_B(b)^{1/2}\chi_1(a)\chi_2(d).
$$

If one $\chi_i$ is ramified, a $K$-fixed function would be constant on $K$, while covariance under $B\cap K$ would multiply it by a nontrivial unit character. Hence it must vanish. Thus

$$
\dim I(\chi_1,\chi_2)^K=
\begin{cases}
1,&\chi_1,\chi_2\text{ unramified},\\
0,&\text{otherwise}.
\end{cases}
$$

### 3.4 Contragredients and the invariant pairing

Normalization is designed so that duality does not introduce an extra modulus.

**Proposition 3.2.** There is a natural isomorphism

$$
I(\chi_1,\chi_2)^\vee
\cong I(\chi_1^{-1},\chi_2^{-1}).
$$

**Proof strategy.** Pair the two compact pictures and verify invariance by the quotient change-of-variables formula.

**Proof.** Normalize $dk$ by $\operatorname{vol}(K)=1$ and define

$$
\langle f,f'\rangle=\int_K f(k)f'(k)\,dk.
$$

The opposite inducing characters make the integrand invariant under the ambiguity from $B\cap K$. Under right translation by $g$, the quasi-invariant measure on $B\backslash G$ acquires a Radon--Nikodym factor. The two half-modular covariance factors multiply to its inverse, so

$$
\langle\pi(g)f,\pi^\vee(g)f'\rangle=\langle f,f'\rangle.
$$

At each compact-open level this is a nondegenerate pairing of finite-dimensional function spaces. Their union is the whole smooth representation, so the induced map into the smooth dual is an isomorphism. $\square$

For an irreducible principal series, the standard intertwiner will also identify the right side with $I(\chi_2^{-1},\chi_1^{-1})$. At a reducibility point the order should not be casually exchanged: contragredience reverses exact sequences, while the Weyl intertwiner changes which constituent is a subrepresentation.

### 3.5 First examples and a normalization counterexample

If $\chi_1=\chi_2=1$, normalized induction is not the space of functions on $\mathbf P^1(F)$ with the natural fractional-linear action. Its covariance contains $|a/d|^{1/2}$. Nevertheless $I(1,1)$ is irreducible: equality of the characters is not a reducibility condition in normalized coordinates.

The literal function space on $\mathbf P^1(F)$ is $J(1,1)$. Converting gives

$$
J(1,1)=I(\nu^{-1/2},\nu^{1/2}),
$$

which is reducible and contains the constant functions. This example is the fastest diagnostic for a misplaced half-power. If one asserts simultaneously that normalized $I(1,1)$ contains constants and that normalized reducibility occurs at $\nu^{\pm1}$, the two assertions contradict each other.

Another useful example is a ramified ratio. If $\chi_1\chi_2^{-1}$ is nontrivial on $\mathcal O^\times$, it cannot equal $\nu$ or $\nu^{-1}$. Such a principal series will be irreducible. Finite Fourier orthogonality on the unit group, rather than an analytic estimate, is what rules out an exceptional boundary functional.

## 4. The rank-one geometric lemma

### 4.1 Why cells should give a filtration

The Bruhat decomposition is not merely a partition of $G$. Support on unions of cells produces a filtration stable under the subgroup whose Jacquet module we want to compute. In rank one there are only two pieces, so the filtration can be written down without any abstract machinery.

Let $I=I(\chi_1,\chi_2)$. Define $I_{\mathrm{open}}$ to be the subspace of functions whose support is contained in $BwB$. Because the complement $B$ is closed and the open cell is open, such a smooth function is supported away from the boundary in every compact quotient. Under the coordinate $x\mapsto Bwn(x)$, it corresponds to $C_c^\infty(F)$.

The quotient $I/I_{\mathrm{open}}$ records the germ at the closed cell. Evaluation at $1$ identifies it, as a vector space, with the one-dimensional inducing space. The filtration

$$
0\longrightarrow I_{\mathrm{open}}
\longrightarrow I
\longrightarrow I_{\mathrm{closed}}
\longrightarrow0
$$

is stable under $B$, though not under all of $G$. That is enough because $N$-coinvariants retain a $T$-action.

### 4.2 The open-cell model

The map

$$
I_{\mathrm{open}}\longrightarrow C_c^\infty(F),
\qquad f\longmapsto\Phi_f,
\qquad \Phi_f(x)=f(wn(x)),
$$

is an isomorphism of vector spaces. Given $\Phi$, define $f$ on $BwN$ using covariance and set it to zero on $B$. Compact support of $\Phi$ makes the extension locally constant at the missing boundary point.

Under right $N$-translation,

$$
(n(b)\Phi)(x)=\Phi(x+b).
$$

Therefore the $N$-coinvariants of the open cell are the translation coinvariants of $C_c^\infty(F)$. Integration gives a map

$$
C_c^\infty(F)\longrightarrow\mathbf C,
\qquad \Phi\longmapsto\int_F\Phi(x)\,dx.
$$

It kills every translate difference. Conversely its kernel is spanned by translate differences. To see this, choose a compact open additive subgroup $U$ on whose cosets $\Phi$ is constant. The problem descends to finitely supported functions on the discrete group $F/U$. A finitely supported function of total sum zero is a finite sum of differences of point masses. Thus

$$
(I_{\mathrm{open}})_N\cong\mathbf C.
$$

This elementary observation is the open-cell heart of the geometric lemma.

### 4.3 Coinvariants of the two cells

The closed quotient is already trivial under $N$: evaluation at $1$ gives

$$
f\longmapsto f(1),
$$

and

$$
(\pi(t(a,d))f)(1)=f(t(a,d))
=|a/d|^{1/2}\chi_1(a)\chi_2(d)f(1).
$$

Thus its unnormalized $T$-character is

$$
\delta_B^{1/2}(\chi_1\boxtimes\chi_2).
$$

For the open cell, let

$$
\ell_{\mathrm{open}}(f)=\int_F f(wn(x))\,dx.
$$

A change of variables using $wt(a,d)=t(d,a)w$ gives

$$
\ell_{\mathrm{open}}(\pi(t(a,d))f)
=|a/d|^{1/2}\chi_2(a)\chi_1(d)
\ell_{\mathrm{open}}(f).
$$

The Jacobian from $x\mapsto da^{-1}x$ supplies precisely the factor needed to leave the same positive half-modulus. Therefore the second unnormalized coinvariant character is

$$
\delta_B^{1/2}(\chi_2\boxtimes\chi_1).
$$

The equality of half-powers on the two pieces is the payoff of normalized induction.

### 4.4 The geometric lemma

**Theorem 4.1 (rank-one geometric lemma).** The unnormalized Jacquet module $I(\chi_1,\chi_2)_N$ has a two-step $T$-stable filtration whose successive quotients are

$$
\delta_B^{1/2}(\chi_1\boxtimes\chi_2)
\quad\text{and}\quad
\delta_B^{1/2}(\chi_2\boxtimes\chi_1).
$$

Equivalently, for the normalized Jacquet functor

$$
r_N(V)=\delta_B^{-1/2}\otimes V_N,
$$

one has

$$
r_N(I(\chi_1,\chi_2))^{\mathrm{ss}}
\cong
(\chi_1\boxtimes\chi_2)
\oplus
(\chi_2\boxtimes\chi_1).
$$

**Proof strategy.** Apply coinvariants to the two-cell filtration and use the two calculations above.

**Proof.** We first record the exactness needed at this point, rather than use the
general theorem of Chapter 5 before it has been proved. Write

$$
N_m=n(\varpi^{-m}\mathcal O),\qquad m\geq0.
$$

Each $N_m$ is compact. Averaging identifies $N_m$-invariants with
$N_m$-coinvariants and makes the latter functor exact. Since $N=\bigcup_mN_m$,
the $N$-coinvariant functor is the filtered colimit of these exact functors and is
therefore exact on vector spaces. Applying it to the two-cell sequence gives

$$
0\longrightarrow (I_{\mathrm{open}})_N
\longrightarrow I_N
\longrightarrow (I_{\mathrm{closed}})_N
\longrightarrow0.
$$

Section 4.2 shows that the first term is one-dimensional, and Section 4.3
computes the $T$-characters on both outer terms. There are no further Bruhat
cells and hence no further subquotients. Twisting the entire sequence by
$\delta_B^{-1/2}$ removes the common half-modulus. $\square$

For unnormalized induction, substitute

$$
\chi_1=\rho_1\nu^{-1/2},
\qquad
\chi_2=\rho_2\nu^{1/2}.
$$

Then $J(\rho_1,\rho_2)_N$ has successive characters

$$
\rho_1\boxtimes\rho_2,
\qquad
(\rho_2\nu)\boxtimes(\rho_1\nu^{-1}).
$$

The asymmetry is not a different theorem; it is what the symmetric normalized statement becomes after changing coordinates.

### 4.5 What the lemma does and does not imply

If the two normalized torus characters are distinct, the filtration splits as a $T$-module. Choose $t\in T$ on which they have different values; the two eigenspaces of $t$ separate the pieces. If $\chi_1=\chi_2$, the two characters coincide and the Jacquet module can retain extension information. Its semisimplification is still the displayed sum.

The geometric lemma does not by itself prove that the principal series has length at most two. It computes a Jacquet module, not every possible subrepresentation. Nor does equality of the two Jacquet exponents imply reducibility: $I(\chi,\chi)$ is the basic counterexample. Reducibility is controlled by whether a boundary functional on the open cell is compatible with the action of the Weyl element. That additional calculation belongs to Chapter 7.

What the lemma does provide is a rigid fingerprint. Any isomorphism of irreducible principal series must preserve the multiset

$$
\{\chi_1\boxtimes\chi_2,\chi_2\boxtimes\chi_1\}.
$$

Thus, once Weyl symmetry has been supplied by an invertible intertwiner, the unordered pair $\{\chi_1,\chi_2\}$ is exactly the inducing datum remembered by the representation.

## 5. Jacquet functors and adjunction

### 5.1 Ordinary and twisted coinvariants

For a smooth $G$-representation $V$, define

$$
V_N=V/\langle n(x)v-v:x\in F,\ v\in V\rangle.
$$

Conjugation by $T$ preserves the relation space, so $V_N$ is a smooth $T$-representation. Ordinary coinvariants retain the constant term along $N$.

For $a\in F$, let $\psi_a(x)=\psi(ax)$ and define twisted coinvariants

$$
V_{N,\psi_a}
=V/\langle n(x)v-\psi(ax)v:x\in F,\ v\in V\rangle.
$$

Their duals are the corresponding equivariant functionals:

$$
\operatorname{Hom}_\mathbf C(V_{N,\psi_a},\mathbf C)
\cong\operatorname{Hom}_N(V,\psi_a)
$$

for the displayed relation $n(x)v-\psi_a(x)v$. Had the relation been written with
$\psi_a^{-1}$, the character on the right would also be inverted. In the
Whittaker chapters we define functionals directly to keep this sign visible.

Ordinary coinvariants are stable under all of $T$. A fixed nontrivial twisted quotient is stable only under the subgroup of $T$ preserving its character; general torus conjugation moves $\psi_a$ through the orbit of nonzero frequencies. Since every nonzero additive character of $F$ is $\psi_a$ for a unique $a\in F^\times$, there are exactly two torus orbits of frequencies: zero and nonzero.

### 5.2 Exactness of the Jacquet functor

Coinvariants by an arbitrary group are only right exact. The unipotent group $N\cong(F,+)$ has extra structure: it is the increasing union of compact open subgroups, and compact-open coinvariants are exact in characteristic zero.

**Theorem 5.1.** The functor $V\mapsto V_N$ is exact on smooth characteristic-zero representations of $G$. The same is true of $V\mapsto V_{N,\psi_a}$.

**Proof strategy.** Compute global coinvariants as a filtered colimit of exact compact-open coinvariants.

**Proof.** Put

$$
N_m=n(\varpi^{-m}\mathcal O),\qquad m\geq0.
$$

Then $N=\bigcup_mN_m$. For a compact group $N_m$, averaging with normalized Haar measure identifies invariants and coinvariants and makes either functor exact. Twisted averaging uses

$$
e_{m,a}v
=\int_{N_m}\psi_a(n)^{-1}nv\,dn
$$

whenever $\psi_a$ is viewed as a character of $N_m$; smoothness reduces this to a finite sum. The global relation space is the union of the relation spaces for the $N_m$, so

$$
V_N\cong\varinjlim_m V_{N_m},
\qquad
V_{N,\psi_a}\cong\varinjlim_m V_{N_m,\psi_a}.
$$

Filtered colimits of vector spaces preserve exact sequences. $\square$

Characteristic zero is essential. In residue characteristic coefficients, averaging over finite $p$-group quotients may require division by zero, and Jacquet exactness can fail.

### 5.3 Normalized Jacquet modules

Define

$$
r_N(V)=\delta_B^{-1/2}\otimes V_N.
$$

Explicitly, if $\bar v$ is the class of $v$ in $V_N$, then

$$
t(a,d)\cdot_{r_N}\bar v
=|a/d|^{-1/2}\,\overline{\pi(t(a,d))v}.
$$

The twist does not affect exactness. It aligns the exponents of an induced representation with the characters used to induce it, as Theorem 4.1 shows.

There is an opposite functor

$$
r_{\bar N}(V)=\delta_{\bar B}^{-1/2}\otimes V_{\bar N}.
$$

Conjugation by $w$ identifies $\bar N$ with $N$ and exchanges the two diagonal coordinates. Statements about a map into an induced representation naturally use $r_N$; statements about a map out of an induced representation naturally use the opposite functor. The Weyl conjugation is what reconciles the two orientations.

### 5.4 Frobenius reciprocity in Jacquet form

**Theorem 5.2 (normalized Jacquet adjunction).** For a smooth $G$-representation $V$ and a smooth $T$-representation $\sigma$,

$$
\operatorname{Hom}_G(V,i_B^G\sigma)
\cong
\operatorname{Hom}_T(r_N(V),\sigma).
$$

**Proof strategy.** Start from ordinary induction as the right adjoint to restriction, observe that $N$ acts trivially on $\sigma$, and move the half-modulus across the Hom space.

**Proof.** Since

$$
i_B^G\sigma=\operatorname{Ind}_B^G(\delta_B^{1/2}\sigma),
$$

ordinary Frobenius reciprocity gives

$$
\operatorname{Hom}_G(V,i_B^G\sigma)
\cong
\operatorname{Hom}_B(V,\delta_B^{1/2}\sigma).
$$

The target is trivial on $N$, so every $B$-map factors uniquely through $V_N$. Thus the right side is

$$
\operatorname{Hom}_T(V_N,\delta_B^{1/2}\sigma)
\cong
\operatorname{Hom}_T(\delta_B^{-1/2}V_N,\sigma).
$$

This is the stated isomorphism. $\square$

There is also a second-adjointness theorem relating maps _out of_ normalized
induction to the opposite Jacquet module. It requires the canonical pairing
between opposite Jacquet modules; it does not follow merely by writing down a
smooth contragredient. We neither assume nor use that theorem here. In the
concrete principal-series calculations below, maps out of an induced
representation are instead supplied by the explicitly constructed standard
intertwiner. This keeps the only adjunction used in proofs equal to the one just
proved.

### 5.5 Consequences for principal series

Suppose $I(\chi_1,\chi_2)$ and $I(\eta_1,\eta_2)$ are irreducible. If they are isomorphic, Theorem 4.1 forces equality of the two multisets of Jacquet exponents, hence

$$
\{\chi_1,\chi_2\}=\{\eta_1,\eta_2\}.
$$

The converse will follow from the standard intertwiner away from the exceptional ratios.

More generally, if an irreducible $V$ has $r_N(V)\ne0$ and its Jacquet module has a character quotient $\chi_1\boxtimes\chi_2$, adjunction produces a nonzero map

$$
V\longrightarrow I(\chi_1,\chi_2).
$$

It is injective by irreducibility. Thus Jacquet modules do not merely record an
invariant; a character quotient forces a representation into a principal
series. Once the reducible principal series have been analyzed, this classifies
every irreducible representation whose nonzero Jacquet module has such a
quotient. No finite-generation assertion for an arbitrary Jacquet module is
being assumed.

The zero Jacquet module is therefore the dividing line between representations
built from the Borel and cuspidal representations. Principal and special
representations are proved generic here, while determinant characters are not.
Generic cuspidal representations enter the Kirillov theory below only under the
explicit genericity hypothesis; their construction is not inferred from Jacquet
exactness.

## 6. Standard intertwining operators

### 6.1 The convergent integral

The Weyl element should exchange the two inducing characters. On the open cell, the candidate is forced:

$$
(M(\chi_1,\chi_2)f)(g)
=\int_F f(wn(x)g)\,dx.
$$

For complex characters, write $\eta=\chi_1\chi_2^{-1}$. The integral converges absolutely when

$$
|\eta(\varpi)|<1.
$$

Indeed the integrand is locally constant on a compact set; on the shells $|x|=q^m$ with $m>0$, covariance makes it a constant multiple of $\eta(\varpi)^m q^{-m}$, while the shell has additive volume $(1-q^{-1})q^m$. The remaining series is geometric in $\eta(\varpi)$.

**Proposition 6.1.** In the convergence chamber,

$$
M(\chi_1,\chi_2):I(\chi_1,\chi_2)
\longrightarrow I(\chi_2,\chi_1)
$$

is a $G$-homomorphism.

**Proof strategy.** Right translation commutes with the integral; covariance in the left variable follows from conjugation and change of variables.

**Proof.** The identity

$$
M(\pi(g_0)f)(g)=M(f)(gg_0)
$$

is immediate. For $t(a,d)\in T$, move $t$ through $w$, use $wt(a,d)=t(d,a)w$, and change $x$ by the dilation arising from conjugation. Its Jacobian changes the original half-modulus into the half-modulus with $a,d$ exchanged. The unipotent part of $B$ merely translates $x$. Hence $Mf$ has the covariance of $I(\chi_2,\chi_1)$. $\square$

### 6.2 Shells and rational continuation

The integral need not converge for fixed arbitrary characters, but every smooth vector has a rationally continuable integral.

Fix the unit restrictions of $\chi_1$ and $\chi_2$ and vary

$$
z=(\chi_1\chi_2^{-1})(\varpi).
$$

Choose a compact-open subgroup fixing $f$. On all sufficiently distant shells $\varpi^{-m}\mathcal O^\times$, the integrand is periodic on the unit coordinate and geometric in $m$. If the unit character in the shell average is nontrivial, the shell contributes zero. If it is trivial, the tail is

$$
\sum_{m\ge m_0}c_f z^m,
$$

with $c_f$ independent of $m$. Thus every value of $Mf$ is a finite sum plus a rational function with denominator $1-z$.

This gives an algebraic continuation of $M$ as a rational family. At a point where it has a pole, multiply by the smallest power of a local parameter that makes the family regular, then specialize. At a point where the specialization vanishes, divide by the largest common vanishing factor first. The resulting nonzero regularized intertwiner is determined up to scalar.

The argument uses no divergent integral: the integral is evaluated where it converges, the shell sum is identified with a rational function there, and that rational function is then evaluated elsewhere. This distinction matters because the symbol $\int_F$ alone does not assign a value to a divergent series.

### 6.3 The spherical scalar

Assume both characters are unramified and let $f^\circ(1)=1$. Put

$$
z=(\chi_1\chi_2^{-1})(\varpi).
$$

For $x\in\mathcal O$, both $w$ and $n(x)$ lie in $K$, so $f^\circ(wn(x))=1$. For $|x|=q^m$, $m\ge1$, an Iwasawa decomposition gives

$$
f^\circ(wn(x))=q^{-m}z^m.
$$

The shell has additive volume $(1-q^{-1})q^m$. Therefore

$$
M(\chi_1,\chi_2)f^\circ(1)
=1+(1-q^{-1})\sum_{m\ge1}z^m
=\frac{1-q^{-1}z}{1-z}.
$$

Since the target spherical line is one-dimensional,

$$
M(\chi_1,\chi_2)f^\circ
=c(\eta)f^{\circ,\mathrm{op}},
\qquad
c(\eta)=\frac{1-q^{-1}\eta(\varpi)}{1-\eta(\varpi)}.
$$

Every factor in this formula is tied to a normalization: $q^{-m}$ uses normalized induction, $(1-q^{-1})q^m$ uses $\operatorname{vol}(\mathcal O)=1$, and $f^\circ(1)=1$ fixes the vector.

### 6.4 Composition and Weyl symmetry

Where both rational families are regular, the composite

$$
M(\chi_2,\chi_1)M(\chi_1,\chi_2)
$$

is a $G$-endomorphism of $I(\chi_1,\chi_2)$. On a fixed finite-level space its
matrix entries are rational in $z$. When the two Jacquet exponents are distinct,
Theorems 4.1 and 5.2 identify the endomorphism space with the one-dimensional
Hom space from $r_N(I)$ to the inducing character. Since those parameters are
Zariski dense in the one-variable family, the composite is scalar as a rational
family. On the spherical line its scalar is

$$
c(\eta)c(\eta^{-1}).
$$

After dividing $M$ by $c(\eta)$ in the unramified family, one obtains a normalized operator carrying $f^\circ$ to $f^{\circ,\mathrm{op}}$ and satisfying the Weyl relation

$$
R(\chi_2,\chi_1)R(\chi_1,\chi_2)=1
$$

away from the exceptional specializations. For ramified unit data the normalizing scalar is defined by a nonzero finite-level vector rather than a spherical one; the same rational argument applies.

Consequently, away from parameters where the regularized map has a kernel or cokernel,

$$
I(\chi_1,\chi_2)\cong I(\chi_2,\chi_1).
$$

This is the representation-theoretic Weyl symmetry predicted by the geometric lemma.

### 6.5 Poles are not reducibility

The raw spherical scalar has a pole at $z=1$ and a zero at $z=q$. Yet $I(\chi,\chi)$, corresponding to $z=1$, is irreducible. Multiplying the operator by $1-z$ removes the pole and gives a nonzero invertible specialization. Thus a pole of one chosen integral is not an intrinsic reducibility point.

Conversely, a scalar rescaling can move a zero or pole without repairing a genuine rank drop. Reducibility means that every regularized intertwiner compatible with the rational family fails to be an isomorphism. The boundary-functional calculation in the next chapter identifies those intrinsic points as $z=q^{-1}$ and $z=q$, namely $\eta=\nu$ and $\nu^{-1}$.

This example is a general warning. Meromorphic normalizing factors are coordinates on an operator family. Kernels, images, and extension classes are representation-theoretic objects. They agree only after removable scalar singularities have been separated from genuine rank changes.

## 7. Reducibility and the special representation

### 7.1 The boundary-functional calculation

The two Bruhat cells do not alone bound the length of a principal series. The decisive fact is that only two dilation exponents allow open-cell data to meet the closed boundary in a $G$-stable way.

We isolate the elementary calculation. Let $\mathcal S=C_c^\infty(F)$. A
translation-invariant functional on $\mathcal S$ is a scalar multiple of

$$
\Phi\longmapsto\int_F\Phi(x)\,dx.
$$

Indeed translation coinvariants are one-dimensional by Section 4.2. Fourier
transform gives the complementary statement: away from the zero-frequency line,
translations and dilations act transitively on the nonzero characters. Thus, at
any fixed compact-open level, a stable subspace of the open-cell model is
determined by whether it contains the zero-frequency line and whether it contains
the nonzero-frequency summand. Refining the level preserves these two choices.

The Weyl element glues these choices to the missing point. To see the two possible
gluing exponents without suppressing a Jacobian, take the characteristic function
$\mathbf1_{\mathcal O}$ and translate it by

$$
a_m=\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}.
$$

Dilation of $x$ contributes $q^{-m}$ to its integral, while normalized covariance
contributes

$$
q^{m/2}(\chi_1\chi_2^{-1})(\varpi)^m.
$$

After inversion $x\mapsto x^{-1}$, the Jacobian $|x|^{-2}$ reverses the
dilation and gives the other boundary line. Put

$$
z=(\chi_1\chi_2^{-1})(\varpi).
$$

On successive shells the two boundary coefficients consequently have ratios
$qz$ and $q^{-1}z$. A coefficient can persist through every refinement only if
one of these ratios is $1$. Thus

$$
z=q^{-1}\quad\text{or}\quad z=q.
$$

Compatibility with unit dilations forces $\chi_1\chi_2^{-1}$ to be trivial on
$\mathcal O^\times$. Hence the only possibilities are

$$
\chi_1\chi_2^{-1}=\nu
\quad\text{or}\quad
\nu^{-1}.
$$

Here is the submodule conclusion contained in this computation. Choose a common
level $U\subseteq\mathcal O$ for a nonzero vector and decompose its open-cell
coordinate on the finite additive quotient into the zero-frequency line and the
sum of the nonzero-frequency lines. Translations isolate the individual Fourier
lines, and diagonal conjugation moves every nonzero line to every other one after
the level is refined. Consequently a nonzero proper $G$-submodule must omit
exactly one of the two boundary lines just calculated. Weyl stability says that
the omitted line must persist under all refinements, so one of $qz$ and
$q^{-1}z$ must equal $1$. Conversely, at either equality the compatible line is
obtained by the integral boundary functional in one Weyl ordering and its
inverted counterpart in the other. The compatible line is one-dimensional.

This proves the **boundary submodule lemma**: away from $z=q^{\pm1}$ the
principal series has no nonzero proper submodule; at either endpoint it has a
unique proper irreducible submodule and a unique irreducible quotient. In
particular its length is two there. Notice that the conclusion comes from the
Fourier decomposition plus Weyl gluing, not merely from counting Bruhat cells.

### 7.2 The reducibility theorem

**Theorem 7.1 (principal-series reducibility).** The normalized principal series $I(\chi_1,\chi_2)$ is reducible if and only if

$$
\chi_1\chi_2^{-1}=\nu^{\pm1}.
$$

At either exceptional ratio it has length two. Away from them it is irreducible and

$$
I(\chi_1,\chi_2)\cong I(\chi_2,\chi_1).
$$

**Proof strategy.** The boundary calculation proves irreducibility away from the two ratios and bounds the exceptional length. At each ratio an explicit determinant character supplies one constituent. The regularized intertwiner supplies the other and identifies kernel with image.

**Proof.** Section 7.1 shows that a nonzero proper subrepresentation can occur only at $\nu^{\pm1}$ and that at an exceptional point there can be at most two constituents. If

$$
(\chi_1,\chi_2)=(\mu\nu^{-1/2},\mu\nu^{1/2}),
$$

then the normalized covariance multiplier becomes

$$
|a/d|^{1/2}\mu(a)|a|^{-1/2}\mu(d)|d|^{1/2}
=\mu(ad).
$$

Thus

$$
f(g)=\mu(\det g)
$$

lies in the induced representation and spans a $G$-stable line. The quotient is nonzero and must be irreducible by the length bound.

For the reversed pair, the regularized standard intertwiner maps onto that determinant line; its kernel is nonzero and irreducible. Away from the exceptional values, the composite of opposite regularized intertwiners is a nonzero scalar, so each is invertible. $\square$

In unnormalized coordinates the theorem reads

$$
J(\rho_1,\rho_2)\text{ is reducible}
\quad\Longleftrightarrow\quad
\rho_1\rho_2^{-1}\in\{1,\nu^2\}.
$$

### 7.3 The two exceptional exact sequences

Define the Steinberg representation by

$$
\operatorname{St}
=I(\nu^{-1/2},\nu^{1/2})/\mathbf1.
$$

It is also the unique irreducible subrepresentation of $I(\nu^{1/2},\nu^{-1/2})$. Twisting gives the exact sequences

$$
0\longrightarrow\mu\circ\det
\longrightarrow I(\mu\nu^{-1/2},\mu\nu^{1/2})
\longrightarrow\operatorname{St}\otimes\mu
\longrightarrow0,
$$

and

$$
0\longrightarrow\operatorname{St}\otimes\mu
\longrightarrow I(\mu\nu^{1/2},\mu\nu^{-1/2})
\longrightarrow\mu\circ\det
\longrightarrow0.
$$

Neither sequence splits. If the first split, the special constituent would also embed in the first ordering; after applying the opposite intertwiner, both constituents would produce independent compatible boundary functionals. Section 7.1 shows that space is one-dimensional. The second sequence is dual to the first after replacing $\mu$ by $\mu^{-1}$, so it does not split either.

Ordering therefore matters exactly at reducibility. The two induced representations have the same Jordan--Hölder constituents and the same semisimplified Jacquet module, but opposite extension structures.

### 7.4 The projective-line model

Unnormalized $J(1,1)$ is the space $C^\infty(\mathbf P^1(F))$ of locally constant functions on the projective line. Constants form a $G$-stable line, and

$$
\operatorname{St}\cong C^\infty(\mathbf P^1(F))/\mathbf C.
$$

This model gives concrete intuition. A characteristic function of a residue ball represents a boundary direction; subtracting its average removes the constant part. Refining balls gives infinitely many independent classes, so Steinberg is infinite-dimensional.

The model also distinguishes compactness from finiteness. The projective line is compact, so induction needs no support condition. Yet it has infinitely many clopen refinements, so the induced representation is not finite-dimensional. A finite quotient appears only after fixing a compact-open subgroup.

Finally, the model makes genericity plausible. Constants have no oscillation along $N$. Their quotient retains differences of adjacent balls, and finite Fourier transform converts those differences into nonzero additive characters. The Jacquet integral in Chapter 8 makes this precise.

### 7.5 Jacquet modules of the constituents

Exactness of $r_N$ applied to the exceptional sequences determines the Jacquet modules. A determinant character has trivial $N$-action, so

$$
r_N(\mu\circ\det)
=\mu\nu^{-1/2}\boxtimes\mu\nu^{1/2}.
$$

The geometric lemma for the ambient principal series has the two exponents

$$
\mu\nu^{-1/2}\boxtimes\mu\nu^{1/2},
\qquad
\mu\nu^{1/2}\boxtimes\mu\nu^{-1/2}.
$$

Removing the determinant-character exponent leaves

$$
r_N(\operatorname{St}\otimes\mu)
=\mu\nu^{1/2}\boxtimes\mu\nu^{-1/2}.
$$

Thus Steinberg has one Jacquet exponent, while an irreducible principal series has two. This difference will reappear as one versus two noncompact tails in the Kirillov model and as one versus two Euler factors in the unramified zeta integral.

## 8. Whittaker functionals and uniqueness

### 8.1 Why ordinary coinvariants miss oscillation

The Jacquet module records the zero-frequency behavior of a representation along $N$. Automorphic Fourier expansions require a nonzero frequency. Fixing the conductor-zero character $\psi$, a Whittaker functional is a linear map that transforms by this frequency rather than killing all $N$-differences.

The distinction is visible on functions on $F$. Integration extracts the translation-invariant, zero-frequency quotient. Fourier evaluation at a nonzero point extracts a twisted quotient. The torus acts transitively on nonzero frequencies because

$$
t(a,1)n(x)t(a,1)^{-1}=n(ax).
$$

Thus there is essentially one nontrivial Whittaker theory, although its exact formulas depend on the chosen $\psi$ and its measure.

One-dimensional representations provide a boundary case. Since $N$ lies in the kernel of the determinant, $N$ acts trivially on every $\mu\circ\det$. Such a representation can support the zero frequency but no nonzero frequency. This is why the character constituent disappears from a Whittaker integral at reducibility.

### 8.2 Whittaker functionals and models

A **$\psi$-Whittaker functional** on a smooth representation $(\pi,V)$ is a linear map

$$
\lambda:V\longrightarrow\mathbf C
$$

satisfying

$$
\lambda(\pi(n(x))v)=\psi(x)\lambda(v).
$$

The representation is **generic** if such a nonzero functional exists. Every vector then gives a Whittaker function

$$
W_v(g)=\lambda(\pi(g)v),
$$

with

$$
W_v(n(x)g)=\psi(x)W_v(g),
\qquad
W_{\pi(h)v}(g)=W_v(gh).
$$

The second formula uses the right-translation convention for the function model. If $V$ is irreducible and $\lambda\ne0$, the map $v\mapsto W_v$ is injective: its kernel is a proper $G$-subrepresentation. Its image

$$
\mathcal W(\pi,\psi)
$$

is the Whittaker model.

Changing $\psi$ to $\psi_a(x)=\psi(ax)$ transports the model by $t(a,1)$. Hence genericity is independent of the nontrivial additive character. Numerical gamma factors are not independent of it; their scaling will be computed later.

### 8.3 The rank-one distribution lemma

Uniqueness rests on the following concrete form of the Gelfand--Kazhdan argument.

Put

$$
\tau(g)=j\,{}^tg\,j,
\qquad
j=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

This is an anti-involution and $\tau(n(x))=n(x)$.

**Lemma 8.1 (rank-one distribution lemma).** Let $D$ be a distribution on $G$
satisfying, for one fixed sign $\varepsilon\in\{1,-1\}$,

$$
D(L_{n(x)}R_{n(y)}f)
=\psi(\varepsilon x)\psi(\varepsilon y)D(f).
$$

Then

$$
D(f\circ\tau)=D(f).
$$

The assertion is invariance, not one-dimensionality of the full distribution
space; the torus variables leave many such distributions.

**Proof strategy.** On the open cell the anti-involution exchanges the two
unipotent coordinates and fixes the torus coordinates. On the closed cell,
stabilizer orthogonality removes every orbit except the locus fixed by the
anti-involution.

**Proof.** Every point of the open cell has a unique expression

$$
n(u)t(a,d)w n(v).
$$

A direct matrix multiplication gives

$$
\tau\bigl(n(u)t(a,d)w n(v)\bigr)
=n(v)t(a,d)w n(u).
$$

At a common compact-open level, Fourier projection in $u$ and $v$ says that the
prescribed equivariance extracts the tensor product of the
$\psi^\varepsilon$-line in the two additive variables. Exchanging the variables
fixes that tensor product. The remaining distribution in $(a,d)$ is untouched,
so the restriction of $D$ to the open cell is $\tau$-invariant.

On the closed cell, represent an $N\times N$-orbit by $t(a,d)$. Its stabilizer
contains the pairs with $x+(a/d)y=0$. Unless $a=d$, the character
$\psi(\varepsilon x)\psi(\varepsilon y)$ is nontrivial on a sufficiently large
finite quotient of this stabilizer, and averaging forces the corresponding
distribution to vanish. When $a=d$, the orbit lies in $ZN$ and is fixed pointwise
by $\tau$. Thus the closed-cell part is also invariant. The two-cell filtration
then proves the assertion on all of $G$. $\square$

The lemma is deliberately stated at the level needed here. Its decisive inputs
are visible: two cells, stabilizer orthogonality on the closed cell, and equal
Fourier characters in the two open-cell coordinates.

### 8.4 Uniqueness

**Theorem 8.2 (Whittaker uniqueness).** If $\pi$ is an irreducible admissible representation of $G$, then

$$
\dim\operatorname{Hom}_N(\pi,\psi)\le1.
$$

**Proof strategy.** Apply the distributional multiplicity-one criterion to the
anti-involution in Lemma 8.1.

**Proof.** We include the distributional criterion so that no duality assertion
is hidden. Let $H$ be a closed subgroup, let $\chi$ be a character, and let
$\tau$ be an anti-involution fixing $H$ and $\chi$. Suppose every distribution
that is $(\chi,\chi)$-equivariant under left and right $H$-translation is
$\tau$-invariant. Then every irreducible admissible representation $V$ satisfies

$$
\dim\operatorname{Hom}_H(V,\chi)\leq1.
$$

To prove the criterion, regularize an $H$-equivariant functional on both sides by
convolution with a test function bi-invariant under a sufficiently small compact
open subgroup $K$. The result is a matrix coefficient on the finite-dimensional
space $V^K$, and changing $K$ to a smaller common level does not change it.
Given two $H$-equivariant functionals, their two regularized coefficient kernels
differ by applying $\tau$. The assumed invariance makes the corresponding
finite-level operators commute with every integrated $G$-operator. Their union
therefore gives a $G$-endomorphism of $V$. Schur's lemma makes it scalar, so the
two functionals are proportional. This proves the criterion.

Apply it with $H=N$, $\chi=\psi$, and the anti-involution of Lemma 8.1. That
lemma supplies exactly the required invariance for the two possible signs
created by left and right regularization. Hence the Whittaker-functional space
has dimension at most one. $\square$

Uniqueness makes the Whittaker model canonical up to one scalar. It does not choose that scalar. Normalizations such as $W(1)=1$ are meaningful only after a vector with nonzero value at $1$ has been specified.

### 8.5 Existence for principal and special representations

Let $f\in I(\chi_1,\chi_2)$ have compactly supported open-cell coordinate. Define the Jacquet integral

$$
\lambda_\psi(f)
=\int_F f(wn(x))\psi(-x)\,dx.
$$

It is an ordinary finite Fourier integral on such vectors. For $b\in F$,

$$
\begin{aligned}
\lambda_\psi(\pi(n(b))f)
&=\int_F f(wn(x+b))\psi(-x)\,dx\\
&=\psi(b)\int_F f(wn(u))\psi(-u)\,du.
\end{aligned}
$$

The minus sign in $\psi(-x)$ is therefore forced by right translation.

Open-cell vectors generate every principal series under $G$. Equivalently, the
integral extends directly by stabilization: local constancy of $f$ at the closed
cell makes its restriction to every sufficiently distant shell constant on
cosets on which $x\mapsto\psi(-x)$ is nontrivial, so the integral over that shell
is zero by finite character orthogonality. Thus the integrals over expanding
balls are eventually constant; no value is assigned to a divergent integral.
The functional is nonzero because one may choose $\Phi_f$ with nonzero Fourier
transform at $1$. Hence every irreducible principal series is generic.

At a reducibility point, the functional vanishes on the determinant constituent: $N$ acts trivially there, whereas $\psi$ is nontrivial. Exactness and the two exceptional sequences show that it descends to or restricts to $\operatorname{St}\otimes\mu$. Thus every special representation is generic, and the character constituent is not.

### 8.6 Genericity and its boundary

The results proved so far determine genericity throughout the spectrum generated
from the Borel.

**Theorem 8.3.** Let $V$ be an irreducible admissible representation for which
$r_N(V)$ has a character quotient $\chi_1\boxtimes\chi_2$. Then $V$ is an
irreducible principal series, a special representation, or a determinant
character. It is nongeneric exactly in the last case.

**Proof.** The character quotient and Theorem 5.2 give a nonzero map

$$
V\longrightarrow I(\chi_1,\chi_2).
$$

Irreducibility makes it injective. The boundary submodule lemma of Section 7.1
says that an irreducible subrepresentation of a principal series is either the
whole irreducible principal series or the unique exceptional submodule. The two
exceptional submodules are a special representation in one ordering and a
determinant character in the other. Section 8.5 proves that the first two cases
are generic and that a determinant character is not. $\square$

No assertion about representations with $r_N(V)=0$ is needed for the present
book. Their construction and the existence of Whittaker functionals require
additional group-specific input; a finite Fourier decomposition of each compact
$N$-orbit by itself does not prove that a nonzero-frequency quotient survives a
direct limit. All Kirillov-model statements below therefore retain genericity as
an explicit hypothesis.

## 9. The Kirillov model

### 9.1 Restriction to the diagonal

A Whittaker function is determined by much less data than an arbitrary function on $G$. The subgroup generated by $N$, $T$, and the center is already large, and the remaining Weyl element acts as a Fourier transform. This suggests restricting a Whittaker function to the one-dimensional torus

$$
a(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix},
\qquad y\in F^\times.
$$

For $v\in V$, set

$$
\phi_v(y)=W_v(a(y)).
$$

The image of $V$ in $C^\infty(F^\times)$ is the **Kirillov model**

$$
\mathcal K(\pi,\psi).
$$

It is locally constant because $W_v$ is smooth. The claim that it determines the
entire Whittaker function is equivalent to injectivity of $v\mapsto\phi_v$; the
mirabolic cyclicity argument in the next paragraph proves that claim.

The injectivity deserves a proof because the diagonal is a small subset of $G$.
Let $\lambda$ denote the Whittaker functional and let $L$ be the span of its
$P$-translates in the algebraic dual of $V$. At any fixed compact-open level,
finite Fourier inversion on a sufficiently large quotient of $N$ expresses the
Weyl translate $w\lambda$ as a finite linear combination of translates
$a(y)n(x)\lambda$. This is the mirabolic cyclicity calculation: on the open cell
it is exactly the equal-character Fourier line in Lemma 8.1, while the only
relevant closed-cell term lies on $ZN$ and is already a $P$-translate. Passing
to finer levels preserves the identity. Hence $L$ is stable under $w$, and
therefore under $G$.

The annihilator $L^\perp\subseteq V$ is now a $G$-subrepresentation. It is
proper because $\lambda\ne0$, so irreducibility gives $L^\perp=0$. If
$\phi_v(y)=\lambda(\pi(a(y))v)$ vanishes for every $y$, upper-unipotent
equivariance makes every $P$-translate of $\lambda$ vanish on $v$. Thus
$v\in L^\perp=0$, proving injectivity.

The Kirillov model is therefore a model of the representation, not merely a collection of coefficients. Its advantage is that two of the three basic actions become elementary formulas.

### 9.2 The mirabolic action

Let $\omega=\omega_\pi$. Direct matrix multiplication gives

$$
(\pi(n(b))\phi)(y)=\psi(by)\phi(y).
$$

Indeed

$$
a(y)n(b)=n(yb)a(y).
$$

Similarly,

$$
\left(\pi\left(\begin{pmatrix}a&0\\0&d\end{pmatrix}\right)\phi\right)(y)
=\omega(d)\phi(ya/d).
$$

To see the central factor, write

$$
a(y)t(a,d)=dI_2\,a(ya/d).
$$

These formulas make the Kirillov model a local analogue of a Fourier expansion. Upper unipotents multiply by additive characters; the torus dilates the frequency variable; the center acts by its prescribed scalar.

The mirabolic subgroup

$$
P=\left\{\begin{pmatrix}a&b\\0&1\end{pmatrix}:a\in F^\times,b\in F\right\}
$$

is generated by $a(F^\times)$ and $N$. Thus its entire action is already explicit. Only the Weyl element remains mysterious.

### 9.3 The compactly supported core

The smallest natural $P$-stable function space is

$$
C_c^\infty(F^\times).
$$

Multiplication by $\psi(by)$ preserves support, and dilation moves compact sets to compact sets. Remarkably, this core occurs in every infinite-dimensional irreducible generic representation.

**Theorem 9.1 (Kirillov core).** If $\pi$ is infinite-dimensional, irreducible, admissible, and generic, then

$$
C_c^\infty(F^\times)\subseteq\mathcal K(\pi,\psi).
$$

**Proof strategy.** Finite Fourier projection produces a function supported in a prescribed additive-frequency coset. Torus dilation moves it to any valuation shell, and unit averaging isolates any locally constant function on that shell.

**Proof.** Choose $v$ with $W_v(1)\ne0$ after translating if necessary. Smoothness gives an integer $m$ such that $v$ is fixed by $n(\mathfrak p^m)$. Average $v$ over a larger compact subgroup $n(\varpi^{-r}\mathcal O)$ against a finite additive character. On the Kirillov side this multiplies $\phi_v(y)$ by the finite Fourier sum

$$
\int_{\varpi^{-r}\mathcal O}\psi(x(y-y_0))\,dx
=q^r\mathbf1_{y_0+\varpi^r\mathcal O}(y),
$$

where $y_0$ is chosen in a compact-open neighborhood on which $\phi_v$ is a
nonzero constant. Choosing $r$ so that
$y_0+\varpi^r\mathcal O$ lies in that neighborhood and normalizing therefore
gives its characteristic function.

Conjugation by $a(F^\times)$ moves that coset to any desired valuation shell and any desired center. Averaging under a finite quotient of $\mathcal O^\times$ projects to each unit-character component. Characteristic functions of compact-open subsets span $C_c^\infty(F^\times)$, proving the inclusion. $\square$

The infinite-dimensional hypothesis is necessary. A determinant character has no Whittaker model. More subtly, the theorem does not say that every Kirillov function is compactly supported; principal series have asymptotic tails.

### 9.4 Jacquet modules as asymptotic data

The relation between ordinary and twisted coinvariants becomes especially transparent near $y=0$. If $\phi(y)$ is evaluated for $y$ of very large positive valuation, then $\psi(by)=1$ for every $b$ in a fixed compact set. Thus sufficiently deep values become insensitive to a growing part of $N$. Their eventual behavior descends to the ordinary Jacquet module.

**Theorem 9.2 (asymptotic quotient).** Let $\pi$ be infinite-dimensional,
irreducible, admissible, and generic. Give

$$
\mathcal K(\pi,\psi)/C_c^\infty(F^\times)
$$

the normalized $T$-action obtained by multiplying its inherited action by
$\delta_B^{-1/2}$. Then the map $v\mapsto\phi_v$ induces a natural isomorphism

$$
r_N(\pi)\xrightarrow{\ \sim\ }
\mathcal K(\pi,\psi)/C_c^\infty(F^\times).
$$

Consequently $r_N(\pi)=0$ exactly when
$\mathcal K(\pi,\psi)=C_c^\infty(F^\times)$. When $r_N(\pi)$ has finite length,
each of its characters contributes a character-exponential tail as $y\to0$,
and a nonsemisimple repeated character contributes a polynomial in $v(y)$ times
that tail.

**Proof strategy.** Passing to germs at zero kills precisely the $N$-differences.
Theorem 9.1 identifies the functions with zero germ as the compactly supported
core.

**Proof.** If $u\in V$, then

$$
\phi_{\pi(n(b))u-u}(y)=(\psi(by)-1)\phi_u(y),
$$

which vanishes for all sufficiently small $y$. Thus $v\mapsto[\phi_v]$ factors
through $V_N$: smoothness under some $n(\mathfrak p^m)$ also bounds the support
toward $|y|=\infty$, so this difference is compactly supported. Surjectivity onto
the displayed quotient is immediate from the definition of the Kirillov model.

It is also injective. Suppose $\phi_v$ is compactly supported. Cover its support
by finitely many compact-open sets $C_i$ and choose $b_i\in F$ so that
$\psi(b_i y)-1$ is nonzero and constant on $C_i$. After subdividing, write
$\phi_v=\sum_i\phi_i$ with $\phi_i$ supported on $C_i$. By Theorem 9.1,

$$
\theta_i(y)=\frac{\phi_i(y)}{\psi(b_i y)-1}
$$

belongs to the Kirillov model. Hence each $\phi_i$ is the Kirillov function of
an $N$-difference. Injectivity of the Whittaker model then makes $v$ a sum of
$N$-differences, so its class in $V_N$ is zero.

The formula of Section 9.2 shows that the inherited action of $t(a,d)$ on a
germ is $\omega(d)\phi(ya/d)$. Multiplication by $|a/d|^{-1/2}$ therefore makes
the isomorphism exactly $T$-equivariant for $r_N$. If a Jacquet character is
$\chi_1\boxtimes\chi_2$, setting $d=1$ gives

$$
\phi(yc)=|c|^{1/2}\chi_1(c)\phi(y)
$$

on the eventual germ. This is the asserted character-exponential tail.
Generalized eigenspaces give powers of $v(y)$ by the elementary finite-difference
formula for a Jordan block. $\square$

The theorem is an asymptotic statement at $0$, not at both ends. Smooth Whittaker functions vanish for $v(y)$ sufficiently negative after a suitable level condition, while central translates can prevent compact support on $G$ itself.

### 9.5 Principal, special, and cuspidal tails

For $I(\chi_1,\chi_2)$, Theorem 4.1 gives two exponents. Modulo $C_c^\infty(F^\times)$, its Kirillov functions are generated by tails of the form

$$
y\longmapsto |y|^{1/2}\chi_1(y)
\quad\text{and}\quad
y\longmapsto |y|^{1/2}\chi_2(y)
$$

on sufficiently small $y$. If the two characters coincide and the Jacquet action is not semisimple, a second solution has the form

$$
v(y)|y|^{1/2}\chi_1(y).
$$

The valuation factor is the rank-one analogue of a logarithmic solution at a repeated root.

For $\operatorname{St}\otimes\mu$, only the exponent

$$
\mu\nu^{1/2}\boxtimes\mu\nu^{-1/2}
$$

survives. Its Kirillov tail is therefore a scalar multiple of

$$
|y|\mu(y)
$$

in the present representation normalization. When inserted into the zeta integral with $|y|^{s-1/2}$, this produces the factor $L(s+1/2,\mu)$.

If $r_N(\pi)=0$, the Kirillov model is exactly $C_c^\infty(F^\times)$. It is tempting to strengthen this to compact support of every Whittaker function on $G$, but that is false. The center is noncompact and

$$
W(zg)=\omega_\pi(z)W(g).
$$

The correct compactness is in the Kirillov coordinate, or modulo $ZN$ on the Whittaker quotient.

## 10. The Weyl transform

### 10.1 Why the missing generator matters

The formulas of Chapter 9 describe the action of the mirabolic subgroup, not all of $G$. Since $G$ is generated by $P$ and $w$, the representation is completed by one operator

$$
\mathcal F_{\pi,\psi}\phi=\pi(w)\phi.
$$

This is the **Weyl transform**. It is not the ordinary additive Fourier transform on $F$; its kernel depends on $\pi$. Nevertheless it exchanges small support with oscillation in a manner governed by one-dimensional Fourier transform. The local functional equation is the most transparent formula for this operator.

The Bruhat relation $w^2=-I_2$ gives

$$
\mathcal F_{\pi,\psi}^2=\omega_\pi(-1)
$$

on the Kirillov model. Any proposed formula for the Weyl transform must pass this test. A missing central sign often comes from replacing $w$ by a different antidiagonal representative.

### 10.2 The contragredient Whittaker model

For functional equations it is more convenient to use the symmetric antidiagonal matrix

$$
j=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

For $W\in\mathcal W(\pi,\psi)$ define

$$
\widetilde W(g)=W\left(j\,{}^tg^{-1}\right).
$$

Then $\widetilde W$ belongs to $\mathcal W(\pi^\vee,\psi^{-1})$. Indeed

$$
j\,{}^t n(x)^{-1}=n(-x)j,
$$

so

$$
\widetilde W(n(x)g)=\psi(-x)\widetilde W(g).
$$

The center acts by $\omega_\pi^{-1}$ because scalar inversion appears in the definition. The transpose-inverse automorphism preserves the group law in the correct order after the antidiagonal conjugation, and Whittaker uniqueness identifies the resulting representation with the smooth contragredient.

The distinction between $j$ and $w$ is harmless but useful. The matrix $w$ has determinant $1$ and satisfies $w^2=-I_2$; the matrix $j$ makes the dual Whittaker character exactly $\psi^{-1}$. Their ratio is diagonal, so translating between them only inserts an explicit torus and central factor.

### 10.3 Fourier behavior on compact Kirillov functions

Let $\phi=\mathbf1_{u(1+\mathfrak p^m)}$ be a compactly supported Kirillov function. Averaging it under $N$ against $\psi(-by_0)$ isolates the frequency coset containing $y_0$. Conjugating this projector by $w$ turns upper unipotent averaging into lower unipotent averaging. On a fixed compact-open quotient, the resulting matrix is a finite Fourier transform.

Thus $\mathcal F_{\pi,\psi}\phi$ can be computed level by level from Gauss sums. For an unramified vector, unit averaging leaves only the trivial unit character and the calculation becomes the second-order spherical recurrence of Chapter 11. For a ramified unit character, the first nonzero transform occurs at its conductor shell. This is the source of the Gauss sum in the ramified Tate gamma factor.

The calculation also explains why there is no representation-independent pointwise kernel on $F^\times$. The finite Fourier matrices depend on how lower unipotents act, and that action contains the representation's inducing characters or cuspidal data. What is representation-independent is the covariance and the scalar functional equation obtained after Mellin transform.

### 10.4 Support exchanged with oscillation

Fourier transform exchanges concentration with oscillation. In the Kirillov model the same principle appears in three forms:

- upper-unipotent invariance forces support into the annihilator of an additive subgroup;
- a nontrivial unit character forces cancellation until its conductor shell;
- the Weyl transform exchanges upper and lower congruence conditions.

This trichotomy is the engine behind newvector calculations, though no conductor theory is needed here. It also predicts the functional equation: Mellin transform diagonalizes dilation, while the Weyl transform reverses dilation. The spectral variable must therefore change from $s$ to $1-s$, and the discrepancy is a scalar gamma factor.

## 11. Spherical vectors and the rank-one Casselman--Shalika formula

### 11.1 The spherical line

Assume $\chi_1$ and $\chi_2$ are unramified and put

$$
\alpha=\chi_1(\varpi),\qquad
\beta=\chi_2(\varpi).
$$

The principal series has a unique $K$-fixed vector $f^\circ$ normalized by $f^\circ(1)=1$. If its generic constituent is spherical, Whittaker uniqueness gives a spherical Whittaker function $W^\circ$, unique after imposing

$$
W^\circ(1)=1.
$$

This normalization can fail on a badly chosen Whittaker functional, but rescaling the nonzero functional repairs it whenever the spherical vector is generic. At a reducibility point, the spherical constituent can be the nongeneric determinant character; then the generic special constituent has no $K$-fixed vector. The distinction will be visible in Section 11.5.

Write

$$
W_m=W^\circ\left(\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\right).
$$

Right invariance under $K$ and left $N$-equivariance force $W_m=0$ for $m<0$. For if $m<0$, choose $u\in\mathcal O$ such that $\psi(\varpi^m u)\ne1$. The matrix $n(u)$ lies in $K$, while

$$
a(\varpi^m)n(u)=n(\varpi^m u)a(\varpi^m).
$$

Thus $W_m=\psi(\varpi^m u)W_m$, forcing zero.

### 11.2 The first Hecke operator

Normalize $\operatorname{vol}(K)=1$ and let

$$
T=\mathbf1_{K a(\varpi)K}.
$$

The right-coset decomposition is

$$
K a(\varpi)K
=\coprod_{u\in\mathcal O/\mathfrak p}
\begin{pmatrix}\varpi&u\\0&1\end{pmatrix}K
\ \sqcup\
\begin{pmatrix}1&0\\0&\varpi\end{pmatrix}K.
$$

Evaluating the action on $f^\circ$ at $1$ gives

$$
Tf^\circ=q^{1/2}(\alpha+\beta)f^\circ.
$$

The first $q$ representatives each contribute $q^{-1/2}\alpha$, for a total $q^{1/2}\alpha$; the last contributes $q^{1/2}\beta$. The central double coset $\varpi I_2K$ acts by $\alpha\beta$.

The raw eigenvalue contains $q^{1/2}$ because $T$ is the characteristic function of the double coset and induction is normalized. Dividing $T$ by $q^{1/2}$ would remove it. Both conventions occur naturally; only an unannounced switch is problematic.

### 11.3 The Whittaker recurrence

Apply the same Hecke operator to $W^\circ$ and evaluate at $a(\varpi^m)$. The $q$ upper-triangular cosets produce the next term, while the last coset produces a central scalar times the preceding term. A direct multiplication gives, for $m\ge0$,

$$
q^{1/2}(\alpha+\beta)W_m
=qW_{m+1}+\alpha\beta W_{m-1},
$$

where $W_{-1}=0$ and $W_0=1$. Equivalently, after setting

$$
A_m=q^{m/2}W_m,
$$

one obtains

$$
A_{m+1}=(\alpha+\beta)A_m-\alpha\beta A_{m-1},
\qquad A_{-1}=0,\quad A_0=1.
$$

The characteristic polynomial is

$$
(X-\alpha)(X-\beta).
$$

This recurrence is the rank-one Casselman--Shalika calculation. It is also the point at which the spherical Hecke polynomial, Jacquet exponents, and Kirillov tails become literally the same two roots.

### 11.4 The closed formula and generating series

Solving the recurrence yields, for $m\ge0$ and $\alpha\ne\beta$,

$$
W_m=q^{-m/2}
\frac{\alpha^{m+1}-\beta^{m+1}}{\alpha-\beta}.
$$

If $\alpha=\beta$, take the limit:

$$
W_m=q^{-m/2}(m+1)\alpha^m.
$$

The factor $m+1$ is the polynomial multiplying an exponential at a repeated root, exactly as predicted by the Jacquet asymptotics.

The generating series is

$$
\sum_{m\ge0}W_mq^{m/2}X^m
=\frac{1}{(1-\alpha X)(1-\beta X)}.
$$

Because each valuation shell has multiplicative volume $1$, substituting $X=q^{-s}$ will turn this series directly into the spherical Whittaker zeta integral. This is why the half-power $|y|^{s-1/2}$ appears in that integral: it cancels the $q^{-m/2}$ imposed by normalized induction.

### 11.5 Degenerate and exceptional parameters

Equal parameters are not exceptional for reducibility. If $\alpha=\beta$, the principal series $I(\chi,\chi)$ remains irreducible and the formula with $(m+1)\alpha^m$ is valid.

At the pair

$$
(\chi_1,\chi_2)=(\mu\nu^{-1/2},\mu\nu^{1/2})
$$

with $\mu$ unramified, the induced representation contains the spherical determinant character and has special quotient. Exactness of $K$-invariants shows that the unique $K$-fixed line lies in the character constituent; the special representation has no $K$-fixed vector. In the reverse ordering, the special representation is a subrepresentation but the induced spherical line still maps to the character quotient. Thus reducibility never creates two spherical lines.

The special representation does have an Iwahori-fixed line. Its Whittaker values obey a first-order recurrence because only one Jacquet exponent survives. This loss of one root is precisely the loss of one Euler factor in its zeta integral.

## 12. One-dimensional local zeta integrals

### 12.1 Schwartz functions and Fourier transform

The functional equation for $\mathrm{GL}_2$ is built from the one-dimensional local functional equation, so we prove the latter with the same normalizations.

The Schwartz--Bruhat space $\mathcal S(F)$ is $C_c^\infty(F)$. Define

$$
\widehat\Phi(y)=\int_F\Phi(x)\psi(xy)\,dx.
$$

Because $dx$ is self-dual,

$$
\widehat{\widehat\Phi}(x)=\Phi(-x).
$$

Our conductor-zero choice gives

$$
\widehat{\mathbf1_{\mathcal O}}=\mathbf1_{\mathcal O}.
$$

Indeed the integral over $\mathcal O$ is $1$ when $y\in\mathcal O$ and zero otherwise by averaging a nontrivial character of the compact additive group. This identity simultaneously checks the conductor of $\psi$ and the volume of $\mathcal O$.

### 12.2 Tate integrals and their rationality

For a smooth character $\chi:F^\times\to\mathbf C^\times$, define

$$
Z(s,\chi,\Phi)
=\int_{F^\times}\Phi(x)\chi(x)|x|^s\,d^\times x.
$$

It converges for $\operatorname{Re}(s)$ sufficiently large after the unramified part of $\chi$ is included in the bound. Since $\Phi$ is compactly supported, only the tail $x\to0$ can be infinite.

**Proposition 12.1.** Every Tate integral is a rational function of $q^{-s}$. The fractional ideal generated by all such integrals in $\mathbf C[q^s,q^{-s}]$ is generated by

$$
L(s,\chi)=
\begin{cases}
(1-\chi(\varpi)q^{-s})^{-1},&\chi|_{\mathcal O^\times}=1,\\
1,&\chi|_{\mathcal O^\times}\ne1.
\end{cases}
$$

**Proof strategy.** Decompose into valuation shells and use unit orthogonality.

**Proof.** On each shell $\varpi^m\mathcal O^\times$, local constancy turns the integral into a finite unit sum times $\chi(\varpi)^mq^{-ms}$. For $m$ sufficiently large, $\Phi$ is constant near zero. If $\chi$ is ramified, the integral of its unit restriction is zero, so the tail vanishes and $Z$ is a Laurent polynomial. If $\chi$ is unramified, the tail is geometric with denominator $1-\chi(\varpi)q^{-s}$. Taking $\Phi=\mathbf1_{\mathcal O}$ gives exactly that denominator. In the ramified case a function supported on a small unit coset gives a nonzero constant, so the generated ideal is the whole Laurent ring. $\square$

The word “fractional” matters: $L(s,\chi)$ is generally not a Laurent polynomial. It is the distinguished generator with constant term $1$.

### 12.3 The local functional equation

**Theorem 12.2 (Tate local functional equation).** There is a unique rational function

$$
\gamma(s,\chi,\psi)\in\mathbf C(q^{-s})^\times
$$

such that, for every $\Phi\in\mathcal S(F)$,

$$
Z(1-s,\chi^{-1},\widehat\Phi)
=\gamma(s,\chi,\psi)Z(s,\chi,\Phi).
$$

**Proof strategy.** Both sides define homogeneous distributions on $F$. Away from zero, such a distribution is determined by its value on one unit coset. Fourier transform exchanges the two homogeneities. Shell rationality then extends the equality to all $s$.

**Proof.** First take $\Phi$ supported in $F^\times$. Then
$Z(s,\chi,\Phi)$ is a finite Laurent polynomial for every $s$, while the left
side converges for $\operatorname{Re}(s)$ sufficiently negative. Under
$\Phi(x)\mapsto\Phi(ax)$, a change of variables shows that the two sides have
the same homogeneity. On $F^\times$, a distribution with this homogeneity is
determined by its value on one sufficiently small unit coset: multiplicative
translation reaches every other coset, and unit-character projection leaves one
line. The two distributions are therefore proportional on functions supported
away from zero.

Their difference on $\mathcal S(F)$ is supported at $0$. A distribution on the
locally constant test functions supported at one point is a scalar multiple of
evaluation at that point. Its dilation character is trivial, whereas the
displayed homogeneous character depends on $s$; the two are incompatible for
all but a discrete set of values of $q^{-s}$. Thus the difference is zero for
generic $s$ in the convergence half-plane.

Choose $\Phi$ for which the right side is nonzero. Proposition 12.1 makes the
proportionality scalar a rational function of $q^{-s}$. The identity just proved
for generic $s$ therefore extends across the exceptional values as an identity
of rational functions. This also proves uniqueness. $\square$

Define

$$
\epsilon(s,\chi,\psi)
=\gamma(s,\chi,\psi)
\frac{L(s,\chi)}{L(1-s,\chi^{-1})}.
$$

The shell calculation below shows that this is a monomial in $q^{-s}$ times a nonzero constant. The separation

$$
\gamma=\epsilon\frac{L(1-s,\chi^{-1})}{L(s,\chi)}
$$

distinguishes the rational Euler factors from the finite Fourier constant.

### 12.4 Unramified and ramified constants

If $\chi$ is unramified, use $\Phi=\mathbf1_{\mathcal O}$. Since it is self-dual,

$$
Z(s,\chi,\mathbf1_{\mathcal O})=L(s,\chi),
$$

and therefore

$$
\gamma(s,\chi,\psi)
=\frac{L(1-s,\chi^{-1})}{L(s,\chi)},
\qquad
\epsilon(s,\chi,\psi)=1.
$$

Now suppose $\chi$ has conductor exponent $a\ge1$, meaning that $a$ is the least integer for which $\chi$ is trivial on $1+\mathfrak p^a$. Put

$$
\tau(\chi,\psi)
=\int_{\mathcal O^\times}
\chi(u)^{-1}\psi(\varpi^{-a}u)\,du,
$$

where $du$ is the restriction of additive measure, not multiplicative measure. Finite Fourier inversion shows $\tau(\chi,\psi)\ne0$; for unitary $\chi$ its absolute value is $q^{-a/2}$.

Take

$$
\Phi(x)=\chi(x)^{-1}\mathbf1_{\mathcal O^\times}(x).
$$

Then $Z(s,\chi,\Phi)=1$. Its Fourier transform is supported on $\varpi^{-a}\mathcal O^\times$, and for $v\in\mathcal O^\times$,

$$
\widehat\Phi(\varpi^{-a}v)=\chi(v)\tau(\chi,\psi).
$$

Substitution in the functional equation gives the exact formula

$$
\gamma(s,\chi,\psi)
=\epsilon(s,\chi,\psi)
=\chi(\varpi)^a q^{a(1-s)}\tau(\chi,\psi).
$$

For unitary $\chi$, its absolute value is $q^{a(1/2-\operatorname{Re}(s))}$, as expected from a conductor-$a$ Fourier transform. Replacing $\varpi$ changes the displayed Gauss sum and the factor $\chi(\varpi)^a$ inversely, so their product is intrinsic.

### 12.5 Changing the additive character

Let $c\in F^\times$ and $\psi_c(x)=\psi(cx)$. The self-dual measure for $\psi_c$ is

$$
dx_c=|c|^{1/2}dx.
$$

Indeed applying the new Fourier transform twice introduces $|c|^{-1}$ from the change of variables and $|c|$ from the two measure scalars.

A direct substitution in the functional equation gives

$$
\gamma(s,\chi,\psi_c)
=\chi(c)|c|^{s-1/2}\gamma(s,\chi,\psi).
$$

This formula assumes that each Fourier transform uses the self-dual measure for its displayed character. If one keeps $dx$ fixed while changing $\psi$, an additional measure scalar appears. Stating only the character and not the measure is therefore insufficient to determine a gamma factor.

## 13. Whittaker zeta integrals for $\mathrm{GL}_2$

### 13.1 The half-power in the integral

Let $\pi$ be an irreducible admissible generic representation with finite-length
$r_N(\pi)$ and Whittaker model $\mathcal W(\pi,\psi)$, and let $\xi$ be a smooth
character of $F^\times$. Define

$$
Z(s,W,\xi)
=\int_{F^\times}
W\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
\xi(y)|y|^{s-1/2}\,d^\times y.
$$

For $\operatorname{Re}(s)$ sufficiently large, the integral converges. The upper end is controlled by the support of a smooth Whittaker function at fixed level; the lower end is controlled by the finite list of Jacquet exponents.

The upper support assertion is elementary. If $v$ is fixed by
$n(\mathfrak p^m)$ and $\phi_v(y)\ne0$, then
$\psi(by)=1$ for every $b\in\mathfrak p^m$ by the formula of Section 9.2. Hence
$v(y)\geq-m$, so the Kirillov function vanishes toward $|y|=\infty$.

The exponent $s-1/2$ is forced by normalized induction. A principal-series tail is $|y|^{1/2}\chi_i(y)$, so multiplying by $|y|^{s-1/2}$ produces the ordinary Tate exponent $|y|^s$. With $|y|^s$ instead, every Euler factor would be shifted by $1/2$.

Twisting the representation by $\xi\circ\det$ has the same effect as inserting $\xi$ in the integral. Thus the notation $Z(s,W,\xi)$ is naturally associated with $\pi\otimes\xi$.

### 13.2 Rationality and the zeta ideal

**Theorem 13.1.** Every $Z(s,W,\xi)$ is rational in $q^{-s}$. As $W$ varies, these integrals generate a principal fractional ideal of $\mathbf C[q^s,q^{-s}]$. It has a unique generator of the form $P(q^{-s})^{-1}$ with $P(0)=1$, denoted

$$
L(s,\pi\otimes\xi).
$$

**Proof strategy.** Pass to the Kirillov function. Its compact part gives a Laurent polynomial; each asymptotic Jacquet exponent gives a geometric denominator.

**Proof.** Write $\phi(y)=W(a(y))$ and decompose $F^\times$ into shells. By Theorem 9.2, modulo a compactly supported function, $\phi$ is a finite sum of character-exponential tails, possibly multiplied by a polynomial in $v(y)$. Mellin transforming a compactly supported function gives a Laurent polynomial. Mellin transforming a tail gives a rational function with denominator a power of $1-cq^{-s}$.

The set of all integrals is stable under multiplication by $q^{\pm s}$ because translating $W$ by $a(\varpi^{\mp1})$ shifts the valuation index. It is therefore a fractional ideal in the principal ideal domain $\mathbf C[q^s,q^{-s}]$. The Kirillov core supplies the function

$$
\phi(y)=\xi(y)^{-1}\mathbf1_{\mathcal O^\times}(y),
$$

whose integral is $1$, so the ideal contains the Laurent ring. On the other
hand, the finitely many Jacquet tails give a common denominator
$D(q^{-s})$ with $D(0)=1$. Thus the ideal lies between the Laurent ring and
$D^{-1}$ times that ring. Its generator is consequently the reciprocal of a
divisor of $D$, uniquely normalized to have constant term $1$. $\square$

The definition uses only the representation, its Whittaker model, and the measure normalization. It does not require a parameter or a Frobenius convention.

### 13.3 The local factor from Kirillov tails

For an irreducible principal series,

$$
L(s,I(\chi_1,\chi_2)\otimes\xi)
=L(s,\chi_1\xi)L(s,\chi_2\xi).
$$

Indeed the two tails in Section 9.5 give precisely the two Tate denominators, while the compact core supplies enough Laurent polynomials to remove any common numerator.

For a special representation,

$$
L(s,(\operatorname{St}\otimes\mu)\otimes\xi)
=L(s+1/2,\mu\xi).
$$

There is only one tail, $|y|\mu(y)$, so the integrand has exponent $|y|^{s+1/2}$. If $\mu\xi$ is ramified, unit orthogonality kills the tail and the factor is $1$.

If $r_N(\pi)=0$, then $\mathcal K(\pi,\psi)=C_c^\infty(F^\times)$. All zeta integrals are Laurent polynomials, and the Kirillov core contains a function whose integral is $1$. Hence

$$
L(s,\pi\otimes\xi)=1
$$

for every such cuspidal representation and every $\xi$ in this standard degree-two zeta theory.

### 13.4 Test vectors and a vanishing warning

For an unramified irreducible principal series and the normalized spherical Whittaker function,

$$
Z(s,W^\circ,1)
=\sum_{m\ge0}W_mq^{-m(s-1/2)}
=\frac1{(1-\alpha q^{-s})(1-\beta q^{-s})}.
$$

Here shell volume is $1$, and the factor $q^{m/2}$ from $|\varpi^m|^{-1/2}$ cancels the $q^{-m/2}$ in $W_m$.

If $\xi$ is ramified, the same spherical vector gives zero:

$$
\int_{\mathcal O^\times}\xi(u)\,d^\times u=0
$$

on every valuation shell. This does not mean the zeta ideal is zero. The Kirillov core contains functions with the inverse unit character, and one of those is a test vector with nonzero integral. Thus “the spherical integral equals the local factor” is true only when all data in the integral are unramified.

This is a useful counterexample to a common shortcut. A canonical vector for one symmetry need not test a ramified twist. Test vectors must match the character being integrated.

## 14. Functional equations for $\mathrm{GL}_2$

### 14.1 The transformed Whittaker function

Recall

$$
\widetilde W(g)=W(j\,{}^tg^{-1}),
\qquad
j=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

Then $\widetilde W\in\mathcal W(\pi^\vee,\psi^{-1})$. On diagonal matrices,

$$
\widetilde W(a(y))
=W\left(\begin{pmatrix}0&1\\y^{-1}&0\end{pmatrix}\right).
$$

Thus the transformed zeta integral probes the Weyl transform and reverses the valuation direction. The substitution $y\mapsto y^{-1}$ changes $s$ to $1-s$ because the original integral contains $s-1/2$.

The central character enters implicitly in moving scalar matrices through $W$. Using $j$ rather than $w$ makes the additive character on the dual side exactly $\psi^{-1}$ and avoids an extra $\omega_\pi(-1)$ in the statement below.

### 14.2 The local functional equation

**Theorem 14.1 (Whittaker local functional equation).** Let $\pi$ be irreducible,
admissible, and generic, with finite-length $r_N(\pi)$. There is a unique rational function

$$
\gamma(s,\pi\otimes\xi,\psi)\in\mathbf C(q^{-s})^\times
$$

such that, for every $W\in\mathcal W(\pi,\psi)$,

$$
Z(1-s,\widetilde W,\xi^{-1})
=\gamma(s,\pi\otimes\xi,\psi)Z(s,W,\xi).
$$

**Proof strategy.** Both sides are homogeneous Mellin functionals on the Kirillov
model. Such a functional is unique for generic $s$; rationality then extends the
identity through the exceptional values.

**Proof.** On $C_c^\infty(F^\times)$, a functional satisfying

$$
\Lambda(\pi(a(c))\phi)
=\xi(c)^{-1}|c|^{1/2-s}\Lambda(\phi)
$$

is a scalar multiple of
$\int_{F^\times}\phi(y)\xi(y)|y|^{s-1/2}d^\times y$: its value on one compact
unit coset determines its values on all multiplicative translates, and unit
character projection leaves one line. By Theorem 9.2, the quotient of the
Kirillov model by this compact core is the finite-length module $r_N(\pi)$.
A second homogeneous functional can occur on that quotient only when its
character agrees with one of the finitely many Jacquet exponents, which is a
finite set of values of $q^{-s}$. Thus the homogeneous-functional space is
one-dimensional for generic $s$.

The right side of the proposed equation has the displayed homogeneity by
$y\mapsto yc$. Directly,

$$
j\,{}^ta(y)^{-1}a(c)=j\,{}^ta(y/c)^{-1}.
$$

Thus replacing $W$ by its right translate under $a(c)$ replaces the diagonal
argument of $\widetilde W$ by $y/c$. The change of variables $y=cu$ gives the
same homogeneity on the transformed $1-s$ side. Hence the two functionals are
proportional for generic $s$.
Chapter 13 makes both sides rational in $q^{-s}$, so the proportionality extends
as a rational identity. A compact Kirillov function with nonzero Mellin integral
proves uniqueness of the scalar. $\square$

Define

$$
\epsilon(s,\pi\otimes\xi,\psi)
=\gamma(s,\pi\otimes\xi,\psi)
\frac{L(s,\pi\otimes\xi)}
{L(1-s,\pi^\vee\otimes\xi^{-1})}.
$$

In the cases calculated below, this is a monomial in $q^{-s}$. Systematic conductor formulas for arbitrary representations require a broader theory; the functional equations used here need only the explicit principal and special cases.

### 14.3 Principal-series factorization

**Theorem 14.2.** For an irreducible principal series,

$$
\gamma(s,I(\chi_1,\chi_2)\otimes\xi,\psi)
=\gamma(s,\chi_1\xi,\psi)
\gamma(s,\chi_2\xi,\psi).
$$

**Proof strategy.** Unfold the Jacquet integral on the open cell. The resulting two one-dimensional integrations are Tate integrals; apply Theorem 12.2 twice.

**Proof.** Begin with a section whose open-cell coordinate and all relevant translates are compactly supported, so every integral is absolutely convergent and Fubini applies. Insert

$$
W_f(g)=\int_F f(wn(x)g)\psi(-x)\,dx
$$

into $Z(s,W_f,\xi)$. Bruhat coordinates separate the diagonal variable into the two diagonal characters of the inducing datum. After the elementary substitutions coming from $wt(a,d)=t(d,a)w$, the Weyl-transformed integral is obtained by Fourier transforming each of the two one-dimensional section variables.

Here is the finite decomposition that makes “separate” precise. At a common compact-open level, the compact part of the two Bruhat coordinates is a finite union of rectangles in $F\times F$. Its locally constant section is therefore a finite sum

$$
\sum_r \Phi_{1,r}(x_1)\Phi_{2,r}(x_2)
$$

with $\Phi_{i,r}\in\mathcal S(F)$. On the $r$th rectangle, covariance moves the two diagonal scalars to the left and gives the Mellin characters $\chi_1\xi$ and $\chi_2\xi$. Consequently the unfolded integral is a finite sum of products

$$
Z(s,\chi_1\xi,\Phi_{1,r})
Z(s,\chi_2\xi,\Phi_{2,r}).
$$

The transpose-inverse Weyl transform replaces both $\Phi_{i,r}$ by their Fourier transforms and replaces each character by its inverse on the $1-s$ side. No measure scalar appears because $dx$ is self-dual.

Theorem 12.2 contributes the scalars

$$
\gamma(s,\chi_1\xi,\psi)
\quad\text{and}\quad
\gamma(s,\chi_2\xi,\psi).
$$

Their product therefore gives the proportionality in Theorem 14.1 on a spanning set of compact open-cell sections. Smooth translates span the principal series, and rational continuation extends the identity to all sections and all $s$. $\square$

In the completely unramified case, $\epsilon=1$ and the theorem becomes

$$
\gamma(s,\pi,\psi)
=\frac{L(1-s,\pi^\vee)}{L(s,\pi)}.
$$

If one or both characters are ramified, the corresponding explicit Gauss factors from Section 12.4 replace the missing Euler factors.

### 14.4 The special representation as a limiting case

Let $\pi=\operatorname{St}\otimes\mu$. It is the generic constituent at

$$
(\chi_1,\chi_2)=(\mu\nu^{1/2},\mu\nu^{-1/2})
$$

in the ordering where Steinberg is a subrepresentation. The identity of Theorem
14.2 is an identity of rational families away from the reducibility point and
therefore has a well-defined specialization after the scalar cancellation
described in Chapter 6. The Whittaker functional vanishes on the determinant
subrepresentation in the opposite exact sequence and restricts nontrivially to
the special subrepresentation in this ordering. Consequently the specialized
functional equation belongs to the special constituent, and

$$
\gamma(s,\operatorname{St}\otimes\mu,\psi)
=\gamma(s,\mu\nu^{1/2},\psi)
\gamma(s,\mu\nu^{-1/2},\psi).
$$

Suppose $\mu$ is unramified and put $a=\mu(\varpi)$. The two Tate factors simplify to

$$
\gamma(s,\operatorname{St}\otimes\mu,\psi)
=-a q^{1/2-s}
\frac{1-aq^{-s-1/2}}
{1-a^{-1}q^{s-3/2}}.
$$

Since

$$
L(s,\operatorname{St}\otimes\mu)
=(1-aq^{-s-1/2})^{-1},
$$

this says

$$
\epsilon(s,\operatorname{St}\otimes\mu,\psi)
=-a q^{1/2-s}.
$$

The second Euler factor from the reducible principal series has not been arbitrarily discarded. It cancels against part of the opposite-side factor, leaving a monomial epsilon factor and the single Steinberg Euler factor. This calculation is the safest way to understand the limiting case.

### 14.5 Dependence on measures and additive characters

For $c\in F^\times$, change from $\psi$ to $\psi_c$ and use its self-dual measure. Applying the one-dimensional scaling law twice gives

$$
\gamma(s,I(\chi_1,\chi_2)\otimes\xi,\psi_c)
=(\chi_1\chi_2)(c)\xi(c)^2|c|^{2s-1}
\gamma(s,I(\chi_1,\chi_2)\otimes\xi,\psi).
$$

Since $(\chi_1\chi_2)\xi^2$ is the central character of $\pi\otimes\xi$, the intrinsic form is

$$
\gamma(s,\pi\otimes\xi,\psi_c)
=\omega_{\pi\otimes\xi}(c)|c|^{2s-1}
\gamma(s,\pi\otimes\xi,\psi)
$$

in the principal and special cases treated here.

Rescaling $d^\times y$ multiplies both sides of the $\mathrm{GL}_2$ functional equation by the same scalar and therefore leaves gamma unchanged. Rescaling the additive measure in the Jacquet and Fourier transforms does change intermediate Whittaker functionals; when the measure remains self-dual for the displayed additive character, the formulas above already contain the correct compensation.

## 15. Worked local calculations

### 15.1 An unramified principal series

Let $F=\mathbf Q_p$, $q=p$, and let $\chi_1,\chi_2$ be unramified with

$$
\chi_1(p)=A,
\qquad
\chi_2(p)=B,
\qquad
A/B\notin\{p,p^{-1}\}.
$$

Then $I(\chi_1,\chi_2)$ is irreducible and spherical. The raw spherical Hecke operator has eigenvalue

$$
p^{1/2}(A+B),
$$

the central coset has eigenvalue $AB$, and

$$
W_m=p^{-m/2}\frac{A^{m+1}-B^{m+1}}{A-B}.
$$

The standard zeta integral is

$$
Z(s,W^\circ,1)
=\frac1{(1-Ap^{-s})(1-Bp^{-s})}.
$$

The opposite-side functional equation has gamma factor

$$
\frac{(1-Ap^{-s})(1-Bp^{-s})}
{(1-A^{-1}p^{s-1})(1-B^{-1}p^{s-1})}.
$$

Every visible $p^{1/2}$ has a source: normalized induction in the Hecke eigenvalue, the diagonal Whittaker decay in $W_m$, and the compensating $s-1/2$ in the zeta integral.

### 15.2 Equal Satake parameters

Take $A=B$. The normalized principal series remains irreducible. The formula becomes

$$
W_m=p^{-m/2}(m+1)A^m,
$$

and

$$
Z(s,W^\circ,1)=(1-Ap^{-s})^{-2}.
$$

The double pole in the Euler factor reflects a repeated spherical root, not a reducible representation. This is the most transparent counterexample to the false rule “equal inducing characters imply reducibility.” Reducibility depends on the ratio being $|\cdot|^{\pm1}$, not $1$.

### 15.3 The two reducible orderings

Let $\mu$ be unramified. Then

$$
I(\mu\nu^{-1/2},\mu\nu^{1/2})
$$

contains $\mu\circ\det$ and has $\operatorname{St}\otimes\mu$ as quotient. Reversing the pair puts Steinberg in the subrepresentation and the determinant character in the quotient.

The two induced representations have identical semisimplified Jacquet modules:

$$
(\mu\nu^{-1/2}\boxtimes\mu\nu^{1/2})
\oplus
(\mu\nu^{1/2}\boxtimes\mu\nu^{-1/2}).
$$

Only the second exponent belongs to Steinberg. The spherical line belongs to the determinant character, while the Iwahori line in the generic constituent produces the single factor

$$
L(s+1/2,\mu).
$$

Thus semisimplified Jacquet data remembers the constituents but not their order in the extension.

### 15.4 A ramified character in one slot

Let $\chi$ have conductor exponent $a\ge1$ and let $\eta$ be unramified. Then

$$
I(\chi,\eta)
$$

is irreducible because $\chi\eta^{-1}$ is ramified and cannot equal $\nu^{\pm1}$. Its standard local factor is

$$
L(s,I(\chi,\eta))=L(s,\eta).
$$

The $\chi$-tail is present as a Jacquet exponent but disappears from the unit-averaged Mellin transform by character orthogonality. It reappears in the functional equation through the explicit Gauss factor

$$
\chi(\varpi)^a q^{a(1-s)}\tau(\chi,\psi).
$$

There is no $K$-fixed vector. A test vector must carry the inverse of the ramified unit character on the relevant Kirillov shell. This example separates three notions that are often conflated: a Jacquet exponent, an Euler denominator, and a nonzero test-vector integral.

### 15.5 An unramified special representation

Take $\pi=\operatorname{St}$ and $\psi$ of conductor $\mathcal O$. Then

$$
L(s,\pi)=(1-q^{-s-1/2})^{-1},
$$

and

$$
\epsilon(s,\pi,\psi)=-q^{1/2-s}.
$$

The representation has no $K$-fixed vector but has a one-dimensional Iwahori-fixed space. Its Kirillov model contains $C_c^\infty(F^\times)$ and one noncompact tail proportional to $|y|$. The sign in epsilon is the Weyl sign of the special constituent, while the power of $q$ records one unit of conductor in the present unitary normalization.

Twisting by an unramified $\mu$ multiplies the epsilon factor by $\mu(\varpi)$ and replaces the Euler root $q^{-1/2}$ by $\mu(\varpi)q^{-1/2}$. Twisting by a ramified character kills the Euler denominator but leaves a nontrivial Gauss-type functional equation.

## 16. A reusable rank-one dictionary

### 16.1 Geometry, quotients, and Fourier coefficients

The theory can be read as one chain of translations:

$$
\begin{array}{c}
B\backslash G/B=\{1,w\}\\
\Downarrow\\
\text{two-cell filtration of an induced representation}\\
\Downarrow\\
r_N(I(\chi_1,\chi_2))^{\mathrm{ss}}
=(\chi_1\boxtimes\chi_2)\oplus(\chi_2\boxtimes\chi_1)\\
\Downarrow\\
\text{two Kirillov tails}\\
\Downarrow\\
L(s,\chi_1)L(s,\chi_2).
\end{array}
$$

At reducibility, one constituent retains the zero-frequency constant behavior and the other retains the nonzero-frequency Whittaker behavior. The determinant character takes one Jacquet exponent and no Whittaker model. Steinberg takes the other Jacquet exponent, one Kirillov tail, and one Euler factor.

The standard intertwiner and the local functional equation are two manifestations of the Weyl element. The intertwiner exchanges inducing data before passing to a model. The functional equation describes the same exchange after Fourier restriction to the Kirillov coordinate.

### 16.2 Normalization conversion table

The following table gathers the conversions proved above.

| Object                      | Normalized convention                               | Unnormalized convention                                         |
| --------------------------- | --------------------------------------------------- | --------------------------------------------------------------- |
| Inducing law                | $\delta_B^{1/2}(\chi_1\boxtimes\chi_2)$             | $\rho_1\boxtimes\rho_2$                                         |
| Parameter conversion        | $\rho_1=\chi_1\nu^{1/2}$, $\rho_2=\chi_2\nu^{-1/2}$ | $\chi_1=\rho_1\nu^{-1/2}$, $\chi_2=\rho_2\nu^{1/2}$             |
| Reducibility ratios         | $\chi_1\chi_2^{-1}=\nu^{\pm1}$                      | $\rho_1\rho_2^{-1}=1,\nu^2$                                     |
| Jacquet functor             | $r_N(V)=\delta_B^{-1/2}V_N$                         | $V_N$                                                           |
| Principal Jacquet exponents | $\chi_1\boxtimes\chi_2$, $\chi_2\boxtimes\chi_1$    | $\rho_1\boxtimes\rho_2$, $(\rho_2\nu)\boxtimes(\rho_1\nu^{-1})$ |
| Spherical Hecke eigenvalue  | $q^{1/2}(\alpha+\beta)$ for raw $T$                 | obtained after the displayed parameter conversion               |
| Whittaker zeta power        | $                                                   | y                                                               |

The measure ledger is equally short:

$$
\operatorname{vol}_{dx}(\mathcal O)=1,
\qquad
d^\times x=(1-q^{-1})^{-1}|x|^{-1}dx,
\qquad
\operatorname{vol}(K)=1.
$$

These three equalities determine every raw scalar in the spherical, Gauss-sum, and zeta calculations.

### 16.3 Hypotheses that cannot be dropped

Several conclusions have sharp boundaries.

Characteristic zero is used to average over compact open subgroups and to make Jacquet functors exact. In coefficient characteristic equal to the residue characteristic, new extensions and reducibility phenomena occur.

Admissibility is used in Whittaker uniqueness to control finite-level duality and distributions. Smoothness alone does not make every compact-open fixed space finite-dimensional.

Irreducibility is used to turn a nonzero Whittaker functional into an injective model. A reducible principal series can have a Whittaker functional with a nonzero kernel, namely its determinant constituent.

The additive character and its self-dual measure are part of every functional equation. Changing one without recording the other changes gamma factors. Multiplicative Haar normalization does not change gamma when used consistently on both sides, but it does change the numerical value of each individual zeta integral.

Finally, the number of Bruhat cells does not by itself prove a length bound. The length-two theorem uses the boundary-functional calculation and its two exceptional dilation exponents. Omitting that step turns geometry into an unsupported slogan.

### 16.4 Conclusion

Rank one is the first setting in which induction, constant terms, Fourier coefficients, and local functional equations are all nontrivial, yet each can still be seen directly. The upper triangular subgroup supplies two inducing characters. The two Bruhat cells expose those characters in both Weyl orders. Exact Jacquet coinvariants retain their zero-frequency shadows, while Whittaker coinvariants retain a single nonzero-frequency orbit.

The resulting models explain one another. The geometric lemma predicts the exponents in the Kirillov model. The Kirillov tails predict the Euler factors. The Weyl element reverses those tails, and Mellin transform converts that reversal into $s\leftrightarrow1-s$. Two one-dimensional Fourier equations then give the principal-series gamma factor, while the reducibility boundary cancels one Euler root and leaves the special representation with its characteristic epsilon monomial.

Every normalization has played a structural role. The half-modulus makes Weyl symmetry and duality balanced. The inverse half-modulus makes Jacquet adjunction exact in the same coordinates. Self-dual additive measure makes Fourier inversion literal. Multiplicative volume one on $\mathcal O^\times$ makes valuation shells contribute without hidden constants. With these choices fixed, principal series, Jacquet modules, Whittaker models, Kirillov functions, spherical vectors, and local zeta integrals become parts of one coherent rank-one machine.
