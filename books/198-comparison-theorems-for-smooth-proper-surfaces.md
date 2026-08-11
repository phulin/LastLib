# Comparison Theorems for Smooth Proper Surfaces

## Contents

1. [One surface, several realizations](#1-one-surface-several-realizations)
2. [Coherent GAGA in the required form](#2-coherent-gaga-in-the-required-form)
3. [Betti cohomology of a complex surface](#3-betti-cohomology-of-a-complex-surface)
4. [Algebraic de Rham cohomology and periods](#4-algebraic-de-rham-cohomology-and-periods)
5. [Hodge decomposition and the integral boundary](#5-hodge-decomposition-and-the-integral-boundary)
6. [Finite Betti--étale comparison for surfaces](#6-finite-betti--étale-comparison-for-surfaces)
7. [Adic comparison, torsion, and Galois descent](#7-adic-comparison-torsion-and-galois-descent)
8. [Regular fundamental classes and span kernels](#8-regular-fundamental-classes-and-span-kernels)
9. [Proper pushforward, trace, and finite maps](#9-proper-pushforward-trace-and-finite-maps)
10. [Künneth formulas and kernels](#10-künneth-formulas-and-kernels)
11. [Correspondences and comparison](#11-correspondences-and-comparison)
12. [Projectors and the middle-degree summand](#12-projectors-and-the-middle-degree-summand)
13. [Lefschetz traces and projected Frobenius](#13-lefschetz-traces-and-projected-frobenius)
14. [Smooth proper families](#14-smooth-proper-families)
15. [Good specialization](#15-good-specialization)
16. [Semistable specialization](#16-semistable-specialization)
17. [The surface comparison theorem](#17-the-surface-comparison-theorem)

## 1. One surface, several realizations

A smooth proper algebraic surface over a subfield of the complex numbers has three cohomological descriptions that are indispensable for arithmetic geometry. Its complex points form a compact oriented real four-manifold and give integral Betti cohomology. Its algebraic differential forms give a filtered vector space over the field of definition. Its finite étale covers give finite and adic cohomology, and after descent the latter carries an arithmetic Galois action. The purpose of this book is to prove that these are compatible realizations of the same algebraic geometry, with enough functoriality to transport projectors built from oriented finite-flat spans and to identify their middle-degree summands.

The passage from curves to surfaces is not a change of indices. A surface can have torsion in integral cohomology, its algebraic de Rham complex has three terms, its Hodge decomposition has a genuine middle piece of type $(1,1)$, and a degree-zero finite span has a codimension-two regular-lci kernel on a four-dimensional product. A degeneration can have double curves and triple points, so semistable specialization retains a nilpotent operator with $N^3=0$ rather than a single graph transvection. Each of these differences will be kept visible.

### 1.1 Standing data

Let $K$ be a field of characteristic zero equipped with an embedding

$$
\sigma:K\hookrightarrow\mathbf C.
$$

Let $X/K$ be a smooth proper scheme of pure dimension two. Unless components are being discussed explicitly, $X$ is geometrically connected. Put

$$
X_\sigma=X\times_{K,\sigma}\mathbf C,
\qquad
X^{\mathrm{an}}=X_\sigma(\mathbf C)
$$

with its complex-analytic topology. The three constant-coefficient realizations are

$$
H_B^n(X,A)=H_{\mathrm{sing}}^n(X^{\mathrm{an}},A),
\tag{1.1}
$$

$$
H_{\mathrm{dR}}^n(X/K)
=\mathbb H^n(X,\Omega^\bullet_{X/K}),
\qquad
\Omega^\bullet_{X/K}=
\bigl[
\mathcal O_X\xrightarrow d\Omega^1_{X/K}
\xrightarrow d\Omega^2_{X/K}
\bigr],
\tag{1.2}
$$

and, after choosing an algebraic closure $\bar K$ and an extension
$\bar K\hookrightarrow\mathbf C$ of $\sigma$,

$$
H_{\mathrm{\acute et}}^n(X_{\bar K},\mathbf Z/\ell^m\mathbf Z),
\quad
H_{\mathrm{\acute et}}^n(X_{\bar K},\mathbf Z_\ell),
\quad
H_{\mathrm{\acute et}}^n(X_{\bar K},\mathbf Q_\ell).
\tag{1.3}
$$

The integral adic group in (1.3) means continuous cohomology of the normalized tower
$(\mathbf Z/\ell^m\mathbf Z)_m$, formed by derived inverse limit. It is not defined by putting an abstract discrete sheaf $\mathbf Z_\ell$ on the small étale site.

For a finite abelian group $A$ killed by $N$, regarded as a $\mathbf Z/N\mathbf Z$-module, write

$$
A(1)=\mu_N\otimes_{\mathbf Z/N\mathbf Z}A
$$

and, for $q\in\mathbf Z$, define $A(q)=\mu_N^{\otimes q}\otimes_{\mathbf Z/N\mathbf Z}A$, using the dual module for negative $q$. When $A$ is a finite commutative ring, its multiplication also supplies the usual pairings among twists. At the adic level,

$$
\mathbf Z_\ell(1)=\varprojlim_m\mu_{\ell^m},
\qquad
\mathbf Q_\ell(1)=\mathbf Z_\ell(1)\otimes\mathbf Q_\ell.
$$

At a finite field of cardinality $q$, geometric Frobenius acts on
$\mathbf Q_\ell(1)$ by $q^{-1}$. Consequently it acts on the untwisted top cohomology of a smooth proper surface by $q^2$.

### 1.2 The comparison diagram

The two comparison bridges meet at Betti cohomology:

$$
\begin{array}{ccc}
H_{\mathrm{dR}}^n(X/K)\otimes_{K,\sigma}\mathbf C
&\xrightarrow{\ \operatorname{comp}_{\mathrm{dR},B}\ }&
H_B^n(X,\mathbf Q)\otimes_{\mathbf Q}\mathbf C\\[4pt]
&&\uparrow\\[-2pt]
&&H_B^n(X,\mathbf Z)\otimes\mathbf Q\\[-2pt]
&&\downarrow\\[4pt]
&&H_B^n(X,\mathbf Z_\ell)\otimes\mathbf Q_\ell
\xrightarrow{\ \operatorname{comp}_{B,\mathrm{\acute et}}\ }
H_{\mathrm{\acute et}}^n(X_{\bar K},\mathbf Q_\ell).
\end{array}
\tag{1.4}
$$

There is no diagonal comparison between $\mathbf C$ and $\mathbf Q_\ell$. The common object is the rational Betti space, while de Rham cohomology remembers a filtration and étale cohomology remembers a continuous Galois action.

At finite and integral level the Betti--étale bridge is stronger:

$$
H_B^n(X,\mathbf Z/\ell^m\mathbf Z)
\xrightarrow{\sim}
H_{\mathrm{\acute et}}^n(X_{\mathbf C},
\mathbf Z/\ell^m\mathbf Z),
\tag{1.5}
$$

$$
H_B^n(X,\mathbf Z)\otimes\mathbf Z_\ell
\xrightarrow{\sim}
H_{\mathrm{\acute et}}^n(X_{\mathbf C},\mathbf Z_\ell).
\tag{1.6}
$$

Formula (1.6) does not assert freeness. If $H_B^n(X,\mathbf Z)$ has
$\ell$-primary torsion, the same torsion occurs on the right.

### 1.3 The functorial target

Let $X$ and $Y$ be smooth proper surfaces. The correspondence data treated in this book are finite spans

$$
X\xleftarrow{a}Z\xrightarrow{b}Y,
\tag{1.7}
$$

where $Z$ is a smooth proper surface and both legs are finite flat local-complete-intersection maps of constant degree. Their graph factorizations give the orientations used for trace. The action in every realization is

$$
T_{(a,b)}=b_*a^*.
\tag{1.8}
$$

Chapter 8 constructs from (1.7) a regular-lci cohomological kernel on $X\times Y$, without assigning a purity class to the possibly singular scheme-theoretic image of $Z$. Chapter 9 proves comparison for the two operations in (1.8). The kernel action and pull--push action agree, preserve cohomological degree, and have no residual Tate twist or period scalar.

The basic formalism is deliberately smaller than the category of all Chow correspondences. Linear combinations and polynomials in the operators (1.8) are allowed. A geometric composite is represented by the ordinary fiber-product span only when the middle square is Tor-independent and its carrier is again smooth; a clean regular excess square is allowed only with its explicit Euler class. No general nontransverse convolution on a six-dimensional triple product is asserted.

In particular, let $T_1,\ldots,T_s$ be endomorphisms of $X$ supplied by such spans and let

$$
e=P(T_1,\ldots,T_s),
\qquad P\in L\langle t_1,\ldots,t_s\rangle,
\tag{1.9}
$$

for a number field $L$, where the angle brackets allow an ordered noncommutative polynomial; for commuting operators one may use the ordinary polynomial ring. If its action on total Betti cohomology is idempotent, then its action is idempotent in every realization and

$$
eH^*(X)=\bigoplus_{i=0}^4eH^i(X)
\tag{1.10}
$$

in all of them. If an independent analytic argument proves

$$
eH_B^i(X,\mathbf C)=0\quad(i\ne2),
\tag{1.11}
$$

then the same vanishing holds in de Rham and étale cohomology. Thus the honest surface summand is

$$
eH_B^2,\qquad eH_{\mathrm{dR}}^2,\qquad
eH_{\mathrm{\acute et}}^2,
\tag{1.12}
$$

with equal ranks after the appropriate scalar extensions. This is an abstract projector-transport statement; constructing a particular geometric or spectral projector belongs downstream.

### 1.4 What must be qualified

Six boundaries will recur.

First, algebraic de Rham comparison is a characteristic-zero comparison after extension to $\mathbf C$. It does not identify an integral de Rham lattice with integral Betti cohomology.

Second, the Hodge decomposition is a decomposition over $\mathbf C$; the field-of-definition structure generally supplies only the Hodge filtration. Integral cohomology can contain torsion, which disappears after tensoring with $\mathbf C$.

Third, finite-coefficient Betti--étale comparison over $\mathbf C$ works for every prime. Arithmetic smooth proper specialization over a discrete valuation ring works only for coefficient primes different from the residue characteristic.

Fourth, a rational projector need not preserve the natural integral lattice. Its saturated intersection with that lattice is canonical, but it is a direct summand only under an integral idempotence condition.

Fifth, smooth proper specialization is an isomorphism. Semistable specialization is instead described by nearby cycles, finite inertia, Frobenius, and a nilpotent operator. Replacing the latter by an isomorphism with ordinary special-fiber cohomology would discard precisely the degeneration data one needs.

Sixth, the book proves comparison for the regular immersions, product projections, oriented finite-flat lci traces, and finite spans just specified. It does not construct a cycle-class map for every singular support or a functor on the full rational Chow-correspondence category.

## 2. Coherent GAGA in the required form

Algebraic de Rham cohomology is hypercohomology of coherent algebraic sheaves, while analytic de Rham theory begins with holomorphic or smooth forms. The first bridge is therefore coherent GAGA. We prove it in the strength needed here: cohomology, coherent objects, tensor operations, and proper morphisms.

### 2.1 Analytification and exactness

For a finite-type complex scheme $T$, analytification gives a morphism of locally ringed spaces

$$
\alpha:T^{\mathrm{an}}\longrightarrow T.
$$

For a coherent algebraic sheaf $\mathcal F$, put

$$
\mathcal F^{\mathrm{an}}
=\alpha^{-1}\mathcal F
\otimes_{\alpha^{-1}\mathcal O_T}\mathcal O_{T^{\mathrm{an}}}.
\tag{2.1}
$$

The analytic local ring at a complex point is flat over the algebraic local ring. One way to see the decisive finite-presentation statement is to choose an affine embedding near the point. A relation among finitely many polynomial germs that becomes solvable by convergent power series satisfies the local flatness criterion: after division by a Weierstrass polynomial, the question reduces to a finite free module over a smaller convergent power-series ring, and induction on the number of variables proves preservation of kernels. Thus (2.1) is exact on coherent sheaves.

It follows at once that analytification preserves finite tensor products, internal Hom from a locally free sheaf, closed immersions, and the de Rham differential. It also preserves fiber products:

$$
(T_1\times_ST_2)^{\mathrm{an}}
\simeq T_1^{\mathrm{an}}\times_{S^{\mathrm{an}}}T_2^{\mathrm{an}}.
\tag{2.2}
$$

### 2.2 The projective calculation

The seed is projective space. Cover $\mathbf P^N_\mathbf C$ by the standard opens
$D_+(x_i)$. Algebraically, the Čech complex for $\mathcal O(m)$ is the degree-$m$ part of the alternating complex of the localized polynomial rings. Analytically, refine the same cover by compact polycircular regions. A holomorphic cocycle has a convergent Laurent expansion there. Cauchy integration separates its Laurent monomials, and every monomial containing both an allowed positive and an avoidable negative direction is a Čech coboundary. The surviving monomials are exactly the algebraic ones in the usual projective-space cohomology calculation. Therefore

$$
H^q(\mathbf P^N,\mathcal O(m))
\xrightarrow{\sim}
H^q((\mathbf P^N)^{\mathrm{an}},\mathcal O(m)^{\mathrm{an}})
\tag{2.3}
$$

for all $m$ and $q$.

Let $\mathcal F$ be coherent on $\mathbf P^N$. Serre generation gives a surjection from a finite sum of negative twists to $\mathcal F$. Its kernel is coherent. Repeating through more steps than the cohomological dimension and applying the long exact cohomology sequences transfers (2.3) to $\mathcal F$. If $T\hookrightarrow\mathbf P^N$ is closed, pushforward along the closed immersion is exact and does not change cohomology. Hence

$$
H^q(T,\mathcal F)
\xrightarrow{\sim}
H^q(T^{\mathrm{an}},\mathcal F^{\mathrm{an}})
\tag{2.4}
$$

for every projective $T$.

The proof shows more than equality of dimensions. Connecting maps, products of Čech cocycles, and morphisms of coherent sheaves are carried to their analytic counterparts.

### 2.3 Passage from projective to proper

Let $T$ be proper over $\mathbf C$. Choose a projective modification

$$
\pi:T'\longrightarrow T
\tag{2.5}
$$

which is an isomorphism over a dense open. Such a modification follows from Chow's lemma. Replace $T'$ by a projective resolution over the regular locus when necessary. For a coherent $\mathcal F$, the kernel and cokernel of

$$
\mathcal F\longrightarrow\pi_*\pi^*\mathcal F
\tag{2.6}
$$

and all $R^j\pi_*\pi^*\mathcal F$ for $j>0$ are coherent and supported on the proper closed subset where $\pi$ is not an isomorphism.

Analytically, a proper holomorphic map has coherent higher direct images. Locally this is proved by covering the inverse image of a relatively compact polydisc by finitely many Weierstrass charts. Division turns the Čech complex into a bounded complex of finite modules over the polydisc algebra, so its kernels and cokernels remain coherent. For a projective morphism, these analytic higher direct images are the analytifications of the algebraic ones by the projective calculation.

Apply the algebraic and analytic Leray spectral sequences to (2.5). Comparison holds on $T'$ by (2.4). It holds for the error sheaves in (2.6) and for the positive higher direct images by noetherian induction on their support. The two Leray sequences and the long exact sequences of (2.6) then give comparison for $\mathcal F$ on $T$. The induction terminates because every error is supported on a proper closed subset.

We have proved:

**Theorem 2.1 (coherent GAGA).** If $T$ is proper of finite type over $\mathbf C$ and $\mathcal F$ is coherent, then

$$
H^q(T,\mathcal F)
\xrightarrow{\sim}
H^q(T^{\mathrm{an}},\mathcal F^{\mathrm{an}})
\tag{2.7}
$$

for every $q$. The isomorphism is functorial, compatible with exact sequences, tensor products, cup products, pullback, and the Leray maps for proper morphisms.

### 2.4 Algebraizing coherent objects and maps

Full faithfulness follows from (2.7) in degree zero. A finite presentation of $\mathcal F$ gives

$$
\mathcal H om_T(\mathcal F,\mathcal G)^{\mathrm{an}}
\simeq
\mathcal H om_{T^{\mathrm{an}}}
(\mathcal F^{\mathrm{an}},\mathcal G^{\mathrm{an}}),
\tag{2.8}
$$

and hence

$$
\operatorname{Hom}_T(\mathcal F,\mathcal G)
\xrightarrow{\sim}
\operatorname{Hom}_{T^{\mathrm{an}}}
(\mathcal F^{\mathrm{an}},\mathcal G^{\mathrm{an}}).
\tag{2.9}
$$

For essential surjectivity in the projective case, twist a coherent analytic sheaf sufficiently far so that it is generated by finitely many sections and its coherent kernel is again generated after a further twist. The resulting two-term presentation by sums of analytic $\mathcal O(-m)$ algebraizes by (2.9), and its algebraic cokernel analytifies to the original sheaf. A projective modification and noetherian induction on the exceptional support extend the argument to proper $T$.

Thus

$$
\operatorname{Coh}(T)\simeq\operatorname{Coh}(T^{\mathrm{an}}).
\tag{2.10}
$$

In particular,

$$
\operatorname{Pic}(T)\xrightarrow{\sim}
\operatorname{Pic}(T^{\mathrm{an}}).
\tag{2.11}
$$

A closed analytic subspace is defined by a coherent analytic ideal; (2.10) algebraizes the ideal and its multiplication. A holomorphic map from a proper algebraic $T$ to a separated quasi-projective algebraic $U$ is algebraic: its graph is a compact closed analytic subspace of
$T^{\mathrm{an}}\times\overline U^{\mathrm{an}}$, algebraizes there, and misses the boundary because its analytification does. This graph argument will algebraize finite topological covers in Chapter 6.

### 2.5 Relative coherent comparison

Let $f:T\to S$ be proper over $\mathbf C$ and $\mathcal F$ coherent. There is a natural derived morphism

$$
(Rf_*\mathcal F)^{\mathrm{an}}
\longrightarrow
Rf^{\mathrm{an}}_*(\mathcal F^{\mathrm{an}}).
\tag{2.12}
$$

It is an isomorphism. The assertion is local on $S^{\mathrm{an}}$; after a projective modification of $T$ it follows from the projective calculation, while the same smaller-support induction used in Section 2.3 handles the error terms. Equivalently, its geometric fiber maps are (2.7), and the finite coherent presentation of both sides makes fiberwise comparison effective.

If $f$ is smooth proper, the complexes

$$
Rf_*\Omega^p_{T/S}
\quad\text{and}\quad
Rf_*\Omega^\bullet_{T/S}
\tag{2.13}
$$

are perfect locally on $S$. Derived base change is always the correct statement. Ordinary formation of an individual $R^qf_*\Omega^p$ commutes with base change when the adjacent cohomology criterion makes it locally free. Over a characteristic-zero smooth proper family, Hodge theory will show that the relevant ranks are locally constant and will supply the ordinary relative Hodge bundles.

## 3. Betti cohomology of a complex surface

The complex topology supplies the integral object from which both characteristic-zero realizations are obtained. It also displays the torsion phenomenon that distinguishes surfaces from curves.

### 3.1 Orientation, finiteness, and the fundamental class

The analytification of a smooth complex surface is a smooth real four-manifold. In holomorphic coordinates

$$
z_1=x_1+iy_1,\qquad z_2=x_2+iy_2,
$$

its complex orientation is

$$
dx_1\wedge dy_1\wedge dx_2\wedge dy_2.
\tag{3.1}
$$

A proper complex algebraic variety admits a finite triangulation compatible with any prescribed finite family of algebraic subvarieties. One proves this by embedding a projective modification in projective space, triangulating a finite semialgebraic stratification, and descending along the proper modification after subdividing its exceptional strata. Consequently $X^{\mathrm{an}}$ has the homotopy type of a finite CW complex. Every $H_B^i(X,\mathbf Z)$ is therefore finitely generated.

For a geometrically connected $X$, the orientation gives

$$
[X]\in H_4(X^{\mathrm{an}},\mathbf Z),
\qquad
H_B^0(X,\mathbf Z)=\mathbf Z,
\qquad
H_B^4(X,\mathbf Z)=\mathbf Z.
\tag{3.2}
$$

The Betti trace is evaluation on the positive fundamental class:

$$
\operatorname{Tr}_B:
H_B^4(X,\mathbf Z)\longrightarrow\mathbf Z,
\qquad
u\longmapsto\langle u,[X]\rangle.
\tag{3.3}
$$

For several components, (3.2)--(3.3) hold componentwise and the total trace is their sum.

### 3.2 Poincaré duality

Cap product with $[X]$ gives isomorphisms

$$
H_B^i(X,\mathbf Z)
\xrightarrow{\sim}
H_{4-i}(X^{\mathrm{an}},\mathbf Z).
\tag{3.4}
$$

To prove (3.4), triangulate $X$ and choose the dual cell decomposition. An oriented
$i$-cochain assigns coefficients to codimension-$i$ primal faces. Intersecting with the dual cells gives a $(4-i)$-chain. The cellular coboundary and boundary matrices are transposes with the orientation signs, so this is a chain map. On a small oriented ball it identifies the unit local cohomology class with the local fundamental class. Mayer--Vietoris induction over the finite triangulation proves that it is a quasi-isomorphism.

Cup product followed by (3.3) gives

$$
\langle x,y\rangle_B
=\operatorname{Tr}_B(x\smile y):
H_B^i(X,\mathbf Z)\times H_B^{4-i}(X,\mathbf Z)
\longrightarrow\mathbf Z.
\tag{3.5}
$$

On the torsion-free quotients this is a perfect pairing. In middle degree it is symmetric because $(-1)^{2\cdot2}=1$:

$$
H_B^2(X,\mathbf Z)_{\mathrm{free}}
\times H_B^2(X,\mathbf Z)_{\mathrm{free}}
\longrightarrow\mathbf Z.
\tag{3.6}
$$

It is unimodular, but it need not be definite. Algebraic divisor classes and transcendental classes both participate.

### 3.3 The integral torsion correction

The ordinary pairing (3.5) kills torsion, so it is not the complete integral duality statement. Apply the coefficient sequence

$$
0\longrightarrow\mathbf Z
\longrightarrow\mathbf Q
\longrightarrow\mathbf Q/\mathbf Z
\longrightarrow0.
\tag{3.7}
$$

If $x\in H_B^i(X,\mathbf Z)$ is torsion, choose a lift
$\tilde x\in H_B^{i-1}(X,\mathbf Q/\mathbf Z)$ under the Bockstein. For torsion
$y\in H_B^{5-i}(X,\mathbf Z)$, define

$$
\lambda_X(x,y)
=\operatorname{Tr}_{\mathbf Q/\mathbf Z}(\tilde x\smile y)
\in\mathbf Q/\mathbf Z.
\tag{3.8}
$$

Changing the lift adds a rational class; its cup product with torsion is zero, so (3.8) is well defined. Dual-cell Poincaré duality with the injective coefficient group $\mathbf Q/\mathbf Z$ proves that

$$
\operatorname{Tor}H_B^i(X,\mathbf Z)
\times
\operatorname{Tor}H_B^{5-i}(X,\mathbf Z)
\longrightarrow\mathbf Q/\mathbf Z
\tag{3.9}
$$

is perfect. The degrees sum to five, not four.

For a surface the first relevant instance is

$$
\operatorname{Tor}H_B^2(X,\mathbf Z)
\times
\operatorname{Tor}H_B^3(X,\mathbf Z)
\longrightarrow\mathbf Q/\mathbf Z.
\tag{3.10}
$$

There is no torsion in $H_B^1(X,\mathbf Z)$ because the universal coefficient theorem identifies it with
$\operatorname{Hom}(H_1(X,\mathbf Z),\mathbf Z)$. There can be torsion in both degrees two and three, and (3.10) must not be replaced by a degree-two self-pairing.

### 3.4 Change of coefficients

Let $C^\bullet_B(X,\mathbf Z)$ be a finite cellular cochain model. For every ring $A$,

$$
R\Gamma_B(X,A)
\simeq C^\bullet_B(X,\mathbf Z)\otimes_{\mathbf Z}^L A.
\tag{3.11}
$$

For $A=\mathbf Z/\ell^m\mathbf Z$, this gives the universal-coefficient exact sequence

$$
0\longrightarrow
H_B^i(X,\mathbf Z)/\ell^m
\longrightarrow
H_B^i(X,\mathbf Z/\ell^m)
\longrightarrow
H_B^{i+1}(X,\mathbf Z)[\ell^m]
\longrightarrow0.
\tag{3.12}
$$

The last term is the finite-level shadow of the linking pairing. The sequence need not split canonically.

Since $\mathbf Z_\ell$ is flat over $\mathbf Z$ and the integral cohomology groups are finitely generated,

$$
H_B^i(X,\mathbf Z_\ell)
:=H^i(C^\bullet_B\otimes\mathbf Z_\ell)
\simeq
H_B^i(X,\mathbf Z)\otimes\mathbf Z_\ell.
\tag{3.13}
$$

Tensoring with $\mathbf Z_\ell$ does not kill finite $\ell$-primary torsion. Rationalization does:

$$
H_B^i(X,\mathbf Q_\ell)
\simeq H_B^i(X,\mathbf Z)_{\mathrm{free}}\otimes\mathbf Q_\ell.
\tag{3.14}
$$

The derived formulation (3.11) is what will match the normalized étale coefficient tower.

### 3.5 Two integral checks

For $\mathbf P^2(\mathbf C)$, let $h$ be the class of a projective line. Then

$$
H_B^*(\mathbf P^2,\mathbf Z)
=\mathbf Z[ h]/(h^3),
\qquad \deg h=2,
\qquad \int_{\mathbf P^2}h^2=1.
\tag{3.15}
$$

This is the torsion-free model behind the trace normalization. Blowing up one point replaces the middle lattice by
$\mathbf Zh\oplus\mathbf Ze$, with intersection matrix
$\operatorname{diag}(1,-1)$ when $e$ is the exceptional class. It already shows why the surface pairing is indefinite.

An Enriques surface gives the necessary warning. Its canonical line bundle is nontrivial of order two, and its first Chern class generates a $\mathbf Z/2$ subgroup of $H_B^2(X,\mathbf Z)$. Poincare duality and the universal coefficient theorem place a matching $\mathbf Z/2$ in $H_B^3(X,\mathbf Z)$; the two are paired by (3.10), not by the ordinary middle intersection form. Tensoring with $\mathbf C$ erases both classes, whereas tensoring with $\mathbf Z_2$ retains them. Thus the torsion qualifications above occur on classical smooth projective surfaces, not only on pathological examples.

## 4. Algebraic de Rham cohomology and periods

The first comparison is made at the level of complexes. This is essential: a comparison only between cohomology groups would not by itself control cup products, filtrations, or the action of a kernel on a product.

### 4.1 Base change to the complex numbers

Let $X/K$ be as in Section 1.1. Flat base change for coherent hypercohomology gives

$$
R\Gamma(X,\Omega^\bullet_{X/K})\otimes_{K,\sigma}\mathbf C
\xrightarrow{\sim}
R\Gamma(X_\sigma,\Omega^\bullet_{X_\sigma/\mathbf C}).
\tag{4.1}
$$

Here is a direct proof in the present bounded situation. Choose a finite affine cover of $X$ whose finite intersections are affine; separatedness supplies such a cover. Resolve each of the three locally free sheaves $\Omega^p_{X/K}$ by its alternating Cech complex. Every term is a finite product of modules of sections on an affine $K$-scheme. Tensoring this double complex with the flat $K$-algebra $\mathbf C$ commutes with its differentials, kernels, and finite totalization. The base-change map is therefore a quasi-isomorphism.

Coherent GAGA, applied term by term and then to the finite total complex, gives

$$
R\Gamma(X_\sigma,\Omega^\bullet_{X_\sigma/\mathbf C})
\xrightarrow{\sim}
R\Gamma(X^{\mathrm{an}},\Omega^\bullet_{X^{\mathrm{an}},\mathrm{hol}}).
\tag{4.2}
$$

Both arrows preserve the decreasing stupid filtration

$$
F^p\Omega^\bullet=\Omega^{\ge p}.
\tag{4.3}
$$

Thus the filtration transported to singular cohomology below is already present on the algebraic complex.

### 4.2 The holomorphic Poincare lemma

On a polydisc $D\subset\mathbf C^2$, the sequence of sheaves

$$
0\longrightarrow\mathbf C_D
\longrightarrow\mathcal O_D
\xrightarrow d\Omega^1_D
\xrightarrow d\Omega^2_D
\longrightarrow0
\tag{4.4}
$$

is exact. Contract the polydisc to its center by $h_t(z)=tz$. If a holomorphic $p$-form $\omega$ is closed and $p>0$, set

$$
K\omega=\int_0^1t^{p-1}\,\iota_E(h_t^*\omega)\,dt,
\qquad
E=\sum_i z_i\frac{\partial}{\partial z_i}.
\tag{4.5}
$$

The coefficients remain holomorphic, differentiation under the integral is legitimate on compact subpolydiscs, and Cartan's homotopy calculation gives

$$
dK+Kd=\operatorname{id}-h_0^*.
\tag{4.6}
$$

For positive-degree forms the last term is zero. In degree zero, a holomorphic function with zero differential is locally constant. Hence (4.4) is a resolution of the constant sheaf.

The analytic space $X^{\mathrm{an}}$ is paracompact and has the homotopy type of a finite CW complex. Taking derived global sections in (4.4), and comparing sheaf and singular cohomology of the constant sheaf, produces a multiplicative quasi-isomorphism

$$
R\Gamma(X^{\mathrm{an}},\Omega^\bullet_{\mathrm{hol}})
\xrightarrow{\sim}
R\Gamma_{\mathrm{sing}}(X^{\mathrm{an}},\mathbf C).
\tag{4.7}
$$

Concretely, integrate a holomorphic form over smooth singular simplices. Stokes' theorem makes integration a chain map. The shuffle subdivision of products of simplices shows that wedge product maps to singular cup product up to the standard chain homotopy. Thus (4.7) is an isomorphism of commutative algebra objects in the derived category.

### 4.3 Algebraic de Rham comparison

**Theorem 4.1 (filtered multiplicative de Rham comparison).** For every smooth proper surface $X/K$ and embedding $\sigma:K\hookrightarrow\mathbf C$, there is a natural filtered multiplicative isomorphism

$$
\operatorname{comp}_{\mathrm{dR},B}:
H^n_{\mathrm{dR}}(X/K)\otimes_{K,\sigma}\mathbf C
\xrightarrow{\sim}
H_B^n(X,\mathbf C).
\tag{4.8}
$$

It is natural for arbitrary morphisms of smooth proper varieties and compatible with exterior products and connecting maps of filtered complexes.

**Proof.** Compose (4.1), (4.2), and (4.7). A morphism pulls back algebraic forms, holomorphic forms, and singular cochains; integration satisfies

$$
\int_c f^*\omega=\int_{f_*c}\omega,
$$

so the three stages form a natural square. Multiplicativity was proved at the chain level after (4.7). Every map before integration preserves (4.3). $\square$

Properness is used for finite-dimensionality, GAGA, and the Hodge assertions of the next chapter. The local Poincare lemma itself needs only smoothness.

### 4.4 The period and trace normalization

We use the unscaled integration map (4.8). Let $L$ be a line bundle represented by transition functions $g_{ij}$. Its algebraic de Rham first Chern class is represented by the Cech cocycle

$$
\left(\frac{dg_{ij}}{g_{ij}}\right).
\tag{4.9}
$$

On a small loop around a simple zero of $g$, the argument principle gives

$$
\int\frac{dg}{g}=2\pi i.
\tag{4.10}
$$

Therefore

$$
\operatorname{comp}_{\mathrm{dR},B}
\bigl(c_1^{\mathrm{dR}}(L)\bigr)
=2\pi i\,c_1^B(L).
\tag{4.11}
$$

Multiplicativity implies that a codimension-$r$ regular complete-intersection class with $r\le2$ has comparison factor $(2\pi i)^r$; Chapter 8 glues this calculation for exactly those regular immersions. In particular, for a closed point $x$ of a connected complex surface,

$$
\operatorname{comp}_{\mathrm{dR},B}
\bigl(\operatorname{cl}_{\mathrm{dR}}(x)\bigr)
=(2\pi i)^2\operatorname{cl}_B(x).
\tag{4.12}
$$

Normalize algebraic trace by $\operatorname{Tr}_{\mathrm{dR},X}(\operatorname{cl}_{\mathrm{dR}}(x))=1$ and topological integration by $\int_{X^{\mathrm{an}}}\operatorname{cl}_B(x)=1$. Then

$$
\int_{X^{\mathrm{an}}}
\operatorname{comp}_{\mathrm{dR},B}(u)
=(2\pi i)^2\operatorname{Tr}_{\mathrm{dR},X}(u)
\qquad
(u\in H^4_{\mathrm{dR}}(X/K)).
\tag{4.13}
$$

For two smooth proper surfaces $S$ and $Y$, the class of a point
$(s,y)\in S\times Y$ is the exterior product of the two codimension-two
surface point classes. Multiplicativity of comparison and (4.12) therefore
give

$$
\int_{(S\times Y)^{\mathrm{an}}}\operatorname{comp}(v)
=(2\pi i)^4\operatorname{Tr}_{\mathrm{dR},S\times Y}(v).
\tag{4.14}
$$

This is the only fourfold trace normalization used below, and it invokes
no Gysin map of codimension greater than two. The proofs of base change,
GAGA, and the holomorphic Poincare lemma in this chapter work in every
dimension; only the later finite Betti--étale proof is specialized to
surfaces.


This equation fixes every later sign and scalar. If Betti Tate twists are written as $(2\pi i)\mathbf Q$, the visible powers of $2\pi i$ disappear.

## 5. Hodge decomposition and the integral boundary

The filtered comparison becomes geometrically useful only after the Hodge filtration is understood. For surfaces this requires the Kähler identities and not merely a dimension count.

### 5.1 Why the analytic surface is Kähler

Every smooth proper algebraic surface over $\mathbf C$ is projective. By Chow's lemma and resolution, there is a projective smooth surface $S$ with a birational morphism $\pi:S\to X$. A birational morphism between smooth surfaces factors into point blowups: negative definiteness of each exceptional fiber and adjunction produce a terminal exceptional $(-1)$-curve, Castelnuovo contraction removes it, and induction finishes the factorization. It remains to check that projectivity descends through the inverse of one point blowup.

Suppose $\pi:S=\operatorname{Bl}_P(T)\to T$, let $E$ be the exceptional curve, and choose an ample divisor $H$ on $S$. Put

$$
D=H+(H\cdot E)E.
\tag{5.1}
$$

Since $E^2=-1$, one has $D\cdot E=0$. The blowup formula $\operatorname{Pic}(S)=\pi^*\operatorname{Pic}(T)\oplus\mathbf Z[E]$ then gives $D=\pi^*D_0$. Moreover $D^2=H^2+(H\cdot E)^2>0$, and for every curve $C\ne E$ on $S$, both $H\cdot C$ and $E\cdot C$ are nonnegative, with the first positive. Hence $D_0^2>0$ and $D_0\cdot C_0>0$ for every curve $C_0\subset T$. The Nakai criterion makes $D_0$ ample. Descending one blowup at a time proves that $X$ is projective.

Choose an embedding $X_\sigma\hookrightarrow\mathbf P^N_{\mathbf C}$. The restriction of the Fubini--Study form is a Kähler form $\omega$ on $X^{\mathrm{an}}$.

### 5.2 Harmonic forms and type

Smooth complex-valued forms split as

$$
A^n(X^{\mathrm{an}},\mathbf C)
=\bigoplus_{p+q=n}A^{p,q},
\qquad d=\partial+\bar\partial.
\tag{5.2}
$$

The Kähler metric defines adjoints and Laplacians $\Delta_d$, $\Delta_\partial$, and $\Delta_{\bar\partial}$. If $L$ is wedge product by $\omega$ and $\Lambda$ its adjoint, a calculation in unitary coordinates gives

$$
[\Lambda,\partial]=i\bar\partial^*,
\qquad
[\Lambda,\bar\partial]=-i\partial^*.
\tag{5.3}
$$

Expanding the squares and using (5.3) cancels the cross terms:

$$
\Delta_d=2\Delta_\partial=2\Delta_{\bar\partial}.
\tag{5.4}
$$

Elliptic theory on the compact manifold supplies an orthogonal decomposition into harmonic, exact, and coexact forms, and every de Rham class has a unique harmonic representative. Equation (5.4) says that its type components are separately harmonic. Hence

$$
H_B^n(X,\mathbf C)
=\bigoplus_{p+q=n}H^{p,q}(X),
\tag{5.5}
$$

where $H^{p,q}$ can equally be described by $\bar\partial$-cohomology. Complex conjugation sends $H^{p,q}$ to $H^{q,p}$.

The Dolbeault resolution and GAGA identify

$$
H^{p,q}(X)\simeq H^q(X^{\mathrm{an}},\Omega^p_{\mathrm{hol}})
\simeq H^q(X_\sigma,\Omega^p_{X_\sigma/\mathbf C}).
\tag{5.6}
$$

The spectral sequence of (4.3) therefore degenerates at $E_1$, and

$$
F^pH^n_{\mathrm{dR}}(X/K)\otimes_{K,\sigma}\mathbf C
\xrightarrow{\operatorname{comp}_{\mathrm{dR},B}}
\bigoplus_{a\ge p}H^{a,n-a}(X).
\tag{5.7}
$$

For the middle cohomology of a surface,

$$
H_B^2(X,\mathbf C)=H^{2,0}\oplus H^{1,1}\oplus H^{0,2},
\tag{5.8}
$$

$$
F^2=H^{2,0},\qquad
F^1=H^{2,0}\oplus H^{1,1},\qquad
F^0=H_B^2(X,\mathbf C).
\tag{5.9}
$$

### 5.3 Pairings and Hodge orthogonality

The wedge-and-trace pairing

$$
H^n_{\mathrm{dR}}(X/K)\times H^{4-n}_{\mathrm{dR}}(X/K)
\longrightarrow K,
\qquad
(x,y)\longmapsto\operatorname{Tr}_{\mathrm{dR},X}(x\wedge y)
\tag{5.10}
$$

is perfect. After extension to $\mathbf C$, (4.13) identifies it with $(2\pi i)^{-2}$ times topological Poincare duality. It also follows algebraically from coherent duality applied to $\Omega^p$ and the perfect wedge maps $\Omega^p\otimes\Omega^{2-p}\to\Omega^2$.

Types pair only when their bidegrees add to $(2,2)$. Thus

$$
(F^pH^n_{\mathrm{dR}})^\perp
=F^{3-p}H^{4-n}_{\mathrm{dR}}.
\tag{5.11}
$$

For a divisor $D$, (4.11) puts its Betti class in

$$
H_B^2(X,\mathbf Z)\cap H^{1,1}.
\tag{5.12}
$$

Conversely, the exponential sequence

$$
0\to\mathbf Z\xrightarrow{\,2\pi i\,}\mathcal O_{X^{\mathrm{an}}}
\xrightarrow{\exp}\mathcal O_{X^{\mathrm{an}}}^*\to1
\tag{5.13}
$$

shows that an integral class of type $(1,1)$ is the first Chern class of a holomorphic line bundle: its image in $H^2(\mathcal O)$ is its $(0,2)$ component, hence vanishes. GAGA algebraizes the line bundle. Therefore

$$
c_1:\operatorname{Pic}(X_\sigma)\twoheadrightarrow
H_B^2(X,\mathbf Z)\cap H^{1,1}.
\tag{5.14}
$$

The intersection means the preimage in integral cohomology and can contain torsion. This is the surface Lefschetz $(1,1)$ theorem.

### 5.4 What the Hodge theorem does not say

The decomposition (5.5) is over $\mathbf C$. Over $K$ there is canonically the filtration $F^\bullet$, not a canonical splitting. Nor is $H^n_{\mathrm{dR}}(X/K)$ an integral Betti lattice: the period map contains transcendental periods, beginning with $2\pi i$. Finally, torsion in $H_B^n(X,\mathbf Z)$ maps to zero over $\mathbf C$ and is invisible to (5.5). It will reappear exactly in finite and $\ell$-adic comparison.

### 5.5 Two Hodge calculations

For $X=\mathbf P^2$, the class $h=c_1^B(\mathcal O(1))$ spans $H_B^2(X,\mathbf C)$ and has type $(1,1)$. If $\eta=c_1^{\mathrm{dR}}(\mathcal O(1))$, then

$$
\operatorname{comp}(\eta)=2\pi i\,h,
\qquad
\operatorname{comp}(\eta^2)=(2\pi i)^2h^2.
\tag{5.15}
$$

Thus the simplest surface already forces the two period factors in (4.13).

For $X=C\times D$, where $C$ and $D$ have genera $g$ and $h$, Künneth gives

$$
H_B^2(X)=
H_B^2(C)\oplus
\bigl(H_B^1(C)\otimes H_B^1(D)\bigr)
\oplus H_B^2(D).
\tag{5.16}
$$

Splitting each $H^1$ into types $(1,0)$ and $(0,1)$ yields

$$
h^{2,0}=gh,\qquad
h^{1,1}=2+2gh,\qquad
h^{0,2}=gh.
\tag{5.17}
$$

The two outer algebraic summands are divisor classes, while the tensor term contains both $(1,1)$ and transcendental $(2,0)$ and $(0,2)$ directions. This is the basic model for why a surface projector must be tracked on the full Hodge-filtered $H^2$, rather than only on divisor classes.

## 6. Finite Betti--étale comparison for surfaces

We now prove finite-coefficient comparison for a complex smooth proper surface. The proof deliberately uses the curve theorem only on actual curves. Its new surface step is a Lefschetz pencil together with a blowup calculation.

Throughout this chapter $A$ is a finite abelian group. One may work one primary summand at a time and take $A$ to be a finite $\mathbf Z/\ell^m\mathbf Z$-module. Since the ground field is $\mathbf C$, every coefficient prime is invertible. Cup-product compatibility is understood for specified pairings of coefficient modules; when $A$ is a finite commutative ring, the comparison is multiplicative.

### 6.1 Riemann existence in the required range

**Lemma 6.1 (finite covers).** If $T$ is a proper complex algebraic variety, analytification induces an equivalence between finite étale covers of $T$ and finite topological covering spaces of $T^{\mathrm{an}}$.

**Proof.** A finite étale algebraic cover analytifies to a local biholomorphism with finite fibers, hence to a topological cover. Conversely, let $V\to T^{\mathrm{an}}$ be finite topological. It has a unique analytic structure for which the map is locally a disjoint union of isomorphisms. The analytic algebra $f_*\mathcal O_V$ is finite locally free, with multiplication and unit.

If $T$ is proper, coherent GAGA algebraizes this module and its structure maps; faithfulness preserves their identities. The resulting finite algebra is étale because its relative differentials analytify to zero, and faithful flatness of analytic local rings forces the algebraic differentials to vanish.

This proves essential surjectivity in the proper case, and full faithfulness follows by algebraizing morphisms between the two finite coherent algebras. $\square$

Thus the algebraic and topological profinite fundamental groups agree in the proper case, together with their categories of finite continuous modules. For a smooth open complex curve the same statement is the open-curve form of Riemann existence proved in Book 27 by filling the finitely many punctures with branched discs. Those are the only nonproper spaces for which the result is used below.

### 6.2 The comparison morphism of sites

An étale morphism $U\to T$ analytifies to a local biholomorphism. This defines a morphism from the analytic site to the étale site and, for a finite constructible étale sheaf $\mathcal F$, a natural map

$$
R\Gamma_{\mathrm{ét}}(T,\mathcal F)
\longrightarrow
R\Gamma(T^{\mathrm{an}},\mathcal F^{\mathrm{an}}).
\tag{6.1}
$$

The direction will be reversed in our final notation. Its construction commutes formally with pullback, tensor product, and localization. A proper-direct-image comparison is not formal from this sentence: below it is proved for the Lefschetz-pencil map by comparing every stalk, and Chapters 8--9 prove the regular-Gysin, product-projection, and oriented finite-trace cases used for spans.

We need a one-dimensional constructible form of comparison.

**Lemma 6.2 (constructible comparison on a curve).** Let $C$ be an algebraic complex curve, not necessarily proper or smooth, and let $\mathcal F$ be a finite constructible étale sheaf. Then (6.1) is a quasi-isomorphism, both ordinarily and with compact supports.

**Proof.** Normalize a proper compactification of each irreducible component and stratify by smooth open curves and finitely many points. Localization triangles reduce the assertion to a finite lisse sheaf $\mathcal L$ on a smooth connected open curve $U$ and to skyscraper sheaves. The point case is immediate.

By the open-curve Riemann existence statement just recalled, $\mathcal L$ is the same finite representation of the algebraic and topological fundamental groups. Choose a finite étale Galois cover $V\to U$ trivializing it. The smooth-open-curve comparison theorem of Book 27 applies to the constant coefficient on every connected term of the Cech nerve of $V\to U$, and analytification preserves that nerve and all of its face maps. The two cohomological-descent spectral sequences are bounded in each total degree by the curve cohomological-dimension theorem and have identical pages, so they identify the abutments for $\mathcal L$.

For compact supports, place $U$ in its smooth compactification $j:U\hookrightarrow\bar U$. The cone of $j_!\mathcal L\to j_*\mathcal L$ is supported at the finite boundary and is computed by invariants and coinvariants of the same local monodromy operators in both topologies. Localization proves the compactly supported statement and then the result for the original stratification. $\square$

This argument invokes the curve comparison only for smooth curves and their finite covers. Singularities and arbitrary constructible sheaves have been handled here by normalization, localization, and descent.

### 6.3 A Lefschetz pencil

Let $X/\mathbf C$ be a smooth projective surface. After a sufficiently high Veronese embedding, a general pencil of hyperplanes has finite transverse base locus and every singular member has one ordinary double point. Blowing up the base points gives

$$
\pi:\widetilde X\longrightarrow X,
\qquad
f:\widetilde X\longrightarrow\mathbf P^1.
\tag{6.2}
$$

There is a finite $S\subset\mathbf P^1$ such that $f$ is a smooth proper family of curves over $U=\mathbf P^1\setminus S$, while each fiber above $S$ is a reduced nodal curve.

Here is the genericity argument. Form the incidence variety of pairs $(x,H)$ for which $x$ is singular on the hyperplane section. Bertini smoothness makes its projection generically finite along the discriminant. After a high Veronese embedding, the loci where the normal Hessian is degenerate or two singular points occur have codimension at least two. A line avoiding those loci and meeting the discriminant transversely yields the local equation $uv=t$.

Apply proper base change in the analytic and étale topologies. The stalks of $R^qf_*A$ are the cohomology groups of the fibers. Over $U$ they are lisse, and open-curve Riemann existence identifies their monodromy: a local section is parallel transport of the same finite covering data.

At $s\in S$, normalize the nodal fiber $C$:

$$
\nu:C^\nu\longrightarrow C.
$$

If $Q$ is the set of nodes and $Q^\nu$ its two-point preimage, both topologies have the normalization triangle

$$
A_C\longrightarrow R\nu_*A_{C^\nu}\oplus A_Q
\longrightarrow A_{Q^\nu}\longrightarrow.
\tag{6.3}
$$

Comparison for the smooth proper components of $C^\nu$ and for finite point sets proves comparison for $C$. Proper base change therefore identifies every stalk of

$$
(R^qf_*A)_{\mathrm{ét}}^{\mathrm{an}}
\longrightarrow (R^qf_*A)_{\mathrm{an}}.
\tag{6.4}
$$

A morphism of constructible sheaves that is an isomorphism on every geometric stalk is an isomorphism. The Leray spectral sequences

$$
E_2^{pq}=H^p(\mathbf P^1,R^qf_*A)
\Longrightarrow H^{p+q}(\widetilde X,A)
\tag{6.5}
$$

are mapped to one another by (6.1). Lemma 6.2 compares their $E_2$ pages. The comparison theorem for bounded spectral sequences yields

$$
H^n_{\mathrm{ét}}(\widetilde X,A)
\xrightarrow{\sim}H_B^n(\widetilde X,A)
\tag{6.6}
$$

for all $n$.

### 6.4 Descending through the blowup

Suppose $\pi:\operatorname{Bl}_P X\to X$ is the blowup at a complex point with exceptional curve $E\simeq\mathbf P^1$. Excision and the Thom isomorphism give, in either topology,

$$
H^n(\operatorname{Bl}_P X,A)
\simeq H^n(X,A)\oplus H^{n-2}(P,A)(-1).
\tag{6.7}
$$

The second summand maps $1$ to $[E]$. To prove this formula, compare the localization triangles for $P\subset X$ and $E\subset\operatorname{Bl}_P X$. Away from these closed sets the blowup is an isomorphism. Purity identifies the supported terms with $A(-2)[-4]$ and $R\Gamma(E,A(-1))[-2]$. The projective-line calculation splits the latter into the former and $A(-1)[-2]$. The excess normal line identifies the new generator with $[E]$. Every construction is compatible with (6.1).

Induction over the base points in (6.2), followed by the five lemma on these split triangles, descends (6.6) to $X$.

### 6.5 The finite comparison theorem

**Theorem 6.3 (surface Betti--étale comparison).** Let $X$ be a smooth proper surface over $\mathbf C$, and let $A$ be any finite abelian group. The natural comparison map is a quasi-isomorphism

$$
R\Gamma_{\mathrm{ét}}(X,A)
\xrightarrow{\sim}
R\Gamma_{\mathrm{sing}}(X^{\mathrm{an}},A).
\tag{6.8}
$$

It is natural in $X$ and in the finite abelian coefficient group $A$, compatible with pullback between smooth proper surfaces, localization in the pencil proof, and exterior products and cup products attached to arbitrary pairings $A\otimes B\to C$ of finite coefficient groups. For a finite commutative coefficient ring $A$, it is multiplicative. It carries the oriented point class and the normalized surface trace to their étale counterparts. No unrestricted proper-direct-image compatibility is part of this theorem.

**Proof.** The quasi-isomorphism was proved in Sections 6.3--6.4. Naturality and coefficient pairings hold for (6.1) itself and are preserved by the two bounded spectral-sequence comparisons. For the point normalization, choose local parameters $z_1,z_2$. The Betti orientation class is the exterior product of the two positive boundary circles, while the étale class is the exterior product of the Kummer boundaries of $w_i^N=z_i$. Proper Riemann existence identifies these local covers and their ordered generators. Evaluation on the resulting point class is therefore $1$ on both sides. This proves the stated trace normalization. The further Gysin and finite-trace compatibilities require the graph and product arguments of Chapters 8--9. $\square$

For $A=\mathbf Z/\ell^m\mathbf Z$, invert (6.8) and write

$$
\operatorname{comp}_{B,\mathrm{ét},m}:
H_B^n(X,\mathbf Z/\ell^m\mathbf Z)
\xrightarrow{\sim}
H^n_{\mathrm{ét}}(X,\mathbf Z/\ell^m\mathbf Z).
\tag{6.9}
$$

This works for every prime $\ell$, including $\ell=2$. Fix the twist comparison by

$$
1\longmapsto \exp(2\pi i/\ell^m)
\quad\text{in}\quad
\mu_{\ell^m}(\mathbf C).
\tag{6.10}
$$

Then the étale trace

$$
H^4_{\mathrm{ét}}(X,\mathbf Z/\ell^m(2))
\longrightarrow\mathbf Z/\ell^m
\tag{6.11}
$$

matches integration over the complex orientation exactly.

## 7. Adic comparison, torsion, and Galois descent

Finite comparison must pass through the coefficient tower in the derived category. Taking inverse limits of cohomology groups without controlling the derived limit could lose information.

### 7.1 The normalized tower

Fix a prime $\ell$. Define

$$
R\Gamma_{\mathrm{ét}}(X,\mathbf Z_\ell)
=R\varprojlim_mR\Gamma_{\mathrm{ét}}
(X,\mathbf Z/\ell^m\mathbf Z).
\tag{7.1}
$$

Choose a bounded complex $C_X$ of finitely generated free abelian groups computing singular cohomology; a finite CW structure supplies one. Then

$$
C_X\otimes^L\mathbf Z/\ell^m
=C_X\otimes\mathbf Z/\ell^m.
\tag{7.2}
$$

The transition maps in every degree are surjective. The tower is termwise Mittag--Leffler, so

$$
R\varprojlim_m(C_X\otimes\mathbf Z/\ell^m)
\simeq C_X\otimes\mathbf Z_\ell.
\tag{7.3}
$$

Finite comparison respects reduction. Taking its derived inverse limit gives a multiplicative quasi-isomorphism

$$
R\Gamma_{\mathrm{ét}}(X,\mathbf Z_\ell)
\xrightarrow{\sim}
C_X\otimes\mathbf Z_\ell.
\tag{7.4}
$$

Consequently

$$
H^n_{\mathrm{ét}}(X,\mathbf Z_\ell)
\simeq H_B^n(X,\mathbf Z)\otimes\mathbf Z_\ell,
\tag{7.5}
$$

and

$$
H^n_{\mathrm{ét}}(X,\mathbf Q_\ell)
\simeq H_B^n(X,\mathbf Q)\otimes\mathbf Q_\ell.
\tag{7.6}
$$

Equations (3.12) and (7.5) describe all torsion. In particular, (7.5) is not shorthand for tensoring the free quotient alone.

### 7.2 Integral duality

Under (7.4), topological Poincare duality becomes étale derived duality:

$$
R\Gamma_{\mathrm{ét}}(X,\mathbf Z_\ell)
\xrightarrow{\sim}
R\operatorname{Hom}_{\mathbf Z_\ell}
\bigl(R\Gamma_{\mathrm{ét}}(X,\mathbf Z_\ell(2)),
\mathbf Z_\ell[-4]\bigr).
\tag{7.7}
$$

The placement of the twist is equivalent to the trace normalization

$$
\operatorname{Tr}_{\mathrm{ét},X}:
H^4_{\mathrm{ét}}(X,\mathbf Z_\ell(2))
\xrightarrow{\sim}\mathbf Z_\ell.
\tag{7.8}
$$

On free quotients, (7.7) gives perfect pairings

$$
H^n_{\mathrm{ét}}(X,\mathbf Z_\ell)_{\mathrm{free}}
\times
H^{4-n}_{\mathrm{ét}}(X,\mathbf Z_\ell(2))_{\mathrm{free}}
\longrightarrow\mathbf Z_\ell.
\tag{7.9}
$$

It does not say that raw complementary groups pair perfectly in the presence of torsion. The torsion term of derived Hom gives instead

$$
H^n_{\mathrm{ét}}(X,\mathbf Z_\ell)_{\mathrm{tors}}
\times
H^{5-n}_{\mathrm{ét}}(X,\mathbf Z_\ell(2))_{\mathrm{tors}}
\longrightarrow\mathbf Q_\ell/\mathbf Z_\ell,
\tag{7.10}
$$

perfect on finite groups. This is the adic form of the linking pairing (3.9).

After rationalization one may move the twist to the target:

$$
H^n_{\mathrm{ét}}(X,\mathbf Q_\ell)
\times H^{4-n}_{\mathrm{ét}}(X,\mathbf Q_\ell)
\longrightarrow\mathbf Q_\ell(-2).
\tag{7.11}
$$

At a finite field, geometric Frobenius acts on the target by $q^2$.

### 7.3 Descent from $K$

Let $\bar K\hookrightarrow\mathbf C$ extend $\sigma$. Invariance under algebraically closed extension gives

$$
H^n_{\mathrm{ét}}(X_{\bar K},\mathbf Z/\ell^m)
\xrightarrow{\sim}
H^n_{\mathrm{ét}}(X_{\mathbf C},\mathbf Z/\ell^m).
\tag{7.12}
$$

For finite covers this is descent of finite presentation. In higher degree, descend a finite étale hypercover and its finite total complex to a common finitely generated subfield and use the same argument degree by degree. The normalized inverse limit gives the $\mathbf Z_\ell$ and $\mathbf Q_\ell$ statements.

The left side of (7.12) has a continuous action of $G_K=\operatorname{Gal}(\bar K/K)$. Betti cohomology has no natural $G_K$-action; the chosen embedding forgets it. Thus comparison identifies dimensions, the span operators constructed below, products, and pairings, but is not a $G_K$-equivariant isomorphism. What is $G_K$-equivariant is every étale pull--push operator whose maps and orientations are defined over $K$, because it is constructed before passage to $\mathbf C$.

## 8. Regular fundamental classes and span kernels

The operations needed for the surface comparison theorem have regular carriers: divisors and points on a smooth surface, graphs and diagonals of maps of smooth surfaces, and the graph presentation of a finite-flat span. This chapter constructs precisely those classes. It does not assign a purity class to an arbitrary singular support and does not construct a general Chow cycle-class map.

### 8.1 Regular closed immersions in the required range

Let $i:Z\hookrightarrow T$ be a regular closed immersion of codimension $r\le2$, with $Z$ and $T$ smooth in a neighborhood of $Z$. Throughout this chapter, $T$ is a smooth surface, a product of two smooth surfaces, or the regular model/stratum or rank-at-most-two bundle occurring in Sections 8.3 and 16.4. Thus $i$ is a divisor or point on a surface, a graph or diagonal of smooth surfaces inside their product, or one of the explicitly stated clean-excess zero sections. No arbitrary-dimensional immersion theorem is being asserted.

In Betti theory, a complex normal bundle has a canonical real orientation. Its Thom class gives

$$
i_*^B:H_B^n(Z,A)\longrightarrow H_B^{n+2r}(T,A).
\tag{8.1}
$$

In de Rham theory, local purity is represented in coordinates $z_1,\ldots,z_r$ cutting out $Z$ by the iterated residue symbol

$$
\frac{dz_1}{z_1}\wedge\cdots\wedge\frac{dz_r}{z_r}.
\tag{8.2}
$$

Changing a regular sequence multiplies (8.2) by the determinant of the conormal transition matrix, exactly the transition rule for $\det(N_{Z/T})$. The local symbols therefore glue in local cohomology and define

$$
i_*^{\mathrm{dR}}:
H_{\mathrm{dR}}^n(Z)\longrightarrow H_{\mathrm{dR}}^{n+2r}(T).
\tag{8.3}
$$

In étale theory, absolute purity identifies cohomology supported on $Z$ with a shifted Tate twist:

$$
Ri^!\mathbf Z/\ell^m
\simeq\mathbf Z/\ell^m(-r)[-2r].
\tag{8.4}
$$

The resulting Gysin map is

$$
i_*^{\mathrm{ét}}:
H_{\mathrm{ét}}^n(Z,\mathbf Z/\ell^m(j))
\longrightarrow
H_{\mathrm{ét}}^{n+2r}(T,\mathbf Z/\ell^m(j+r)).
\tag{8.5}
$$

The purity generator in codimension one is the boundary of the Kummer torsor $w^{\ell^m}=z$. Exterior product gives the generator in (8.4).

The local integral (4.10) and the choice (6.10) now prove

$$
\operatorname{comp}_{\mathrm{dR},B}(i_*^{\mathrm{dR}}x)
=(2\pi i)^r\,i_*^B\operatorname{comp}_{\mathrm{dR},B}(x),
\tag{8.6}
$$

and

$$
\operatorname{comp}_{B,\mathrm{ét}}(i_*^Bx)
=i_*^{\mathrm{ét}}\operatorname{comp}_{B,\mathrm{ét}}(x),
\tag{8.7}
$$

where the twist in (8.7) is read using (6.10). These are local identities, so they remain true after extension of algebraically closed fields and under family base changes that preserve the regular immersion and are Tor-independent; the clean excess alternative is stated separately in Section 8.3.

### 8.2 Graphs, diagonals, and finite-span kernels

If $f:Z\to Y$ is a morphism of smooth surfaces, its graph

$$
j_f:Z\hookrightarrow Z\times Y
$$

is a regular immersion of codimension two: it is a section of the smooth projection $Z\times Y\to Z$, whose relative dimension is two. Define its realization class by

$$
[\Gamma_f]_R=(j_f)_*^R(1).
\tag{8.8}
$$

The same construction gives $[\Delta_X]_R$. Equations (8.6)--(8.7) compare these classes, and Section 10.2 will check directly that the diagonal kernel acts as the identity.

Now let $X\xleftarrow{a}Z\xrightarrow{b}Y$ be a span of smooth proper surfaces with finite flat lci legs. Section 9.4 constructs the oriented finite trace and its product with an identity. Define the kernel carried by the smooth surface $Z$ as

$$
\kappa_R(a,b)
= (a\times 1_Y)_*[\Gamma_b]_R
\in H_R^4(X\times Y)(2),
\tag{8.9}
$$

with the Tate twist literal in étale theory and represented by the period normalization in Betti theory. The pushforward in (8.9) is only the product of the finite trace $a_*$ with $1_Y$; it is not an appeal to an arbitrary proper pushforward on fourfolds. Factoring through the transposed graph $[\Gamma_a]^t\subset X\times Z$ and $1_X\times b$ gives the same class. Indeed, testing either expression against $p_X^*u\smile p_Y^*v$ gives

$$
\operatorname{Tr}_Z(a^*u\smile b^*v).
\tag{8.10}
$$

More generally, adjunction for either allowed factorization shows that pairing
either expression against an arbitrary class $w$ on $X\times Y$ gives
$\operatorname{Tr}_Z((a,b)^*w)$. Poincare duality therefore identifies the
two kernels over a field and at finite coefficient level. At integral adic
level the same adjunction is an identity of morphisms between perfect
derived complexes; this is the required detection statement because an
ordinary degreewise pairing would miss torsion linking one degree later.
In particular, the argument does not assume that decomposable classes detect
the Kunneth $\operatorname{Tor}$ terms.

The graph contributes codimension two and the finite trace contributes no period factor. Consequently

$$
\operatorname{comp}_{\mathrm{dR},B}
(\kappa_{\mathrm{dR}}(a,b))
=(2\pi i)^2\kappa_B(a,b),
\tag{8.11}
$$

while Betti--étale comparison carries $\kappa_B(a,b)$ exactly to $\kappa_{\mathrm{ét}}(a,b)$. This construction remains valid even when the image of $(a,b):Z\to X\times Y$ is singular, because purity is applied to the regular graph $j_b$, not to that image.

### 8.3 Transverse intersections and the retained excess case

External products of the regular Thom classes above are Thom classes:

$$
[Z_1\times Z_2]=[Z_1]\boxtimes[Z_2].
\tag{8.12}
$$

If two regular immersions of codimension at most two meet transversely, their pulled-back regular sequences concatenate. The Koszul complexes therefore tensor without higher Tor and

$$
[Z_1\cap Z_2]=[Z_1]\smile[Z_2].
\tag{8.13}
$$

We retain one explicitly bounded nontransverse formula. Consider a Cartesian square

$$
\begin{array}{ccc}
Z'&\xrightarrow{g'}&Z\\
{\scriptstyle i'}\downarrow&&\downarrow{\scriptstyle i}\\
T'&\xrightarrow{g}&T
\end{array}
\tag{8.14}
$$

in which $i$ and $i'$ are regular immersions of codimension at most two, every scheme is regular along the displayed loci, and the map of normal bundles is injective with locally free cokernel

$$
E=g'^*N_{Z/T}/N_{Z'/T'},
\qquad \operatorname{rank}E\le2.
\tag{8.15}
$$

These are the **clean regular-excess hypotheses**. Only under them do we use

$$
g^*i_*(x)=i'_*\bigl(e(E)\smile g'^*x\bigr),
\tag{8.16}
$$

where $e(E)$ is the zero-section Euler class. Here is the proof in this range. Locally choose a regular sequence for $i$. After pullback, split off a regular sequence for $i'$; the remaining conormal quotient is the locally free module $E^\vee$. The pulled-back Koszul complex is the Koszul complex for $i'$ tensored with the exterior complex of $E^\vee$. Deforming the chosen sequence to its linear terms identifies the latter contribution with zero-section pullback followed by zero-section Gysin, which is the definition of $e(E)$. Changes of splitting are elementary row operations and give homotopic Koszul maps, so the local formulas glue. The Betti Thom, de Rham $d\log$, and étale Kummer constructions perform the same Koszul calculation; hence (8.16) compares in all three realizations.

If the square is Tor-independent, $E=0$ and (8.16) is ordinary base change. If regularity, the locally free excess quotient, or the complete list of components fails, this book makes no refined-intersection assertion. In particular (8.16) is not a construction of nontransverse convolution for arbitrary singular cycles on a triple product.

### 8.4 Ground fields and Galois invariance

If a regular immersion or finite span is defined over $K$, all its graph, Gysin, pullback, and oriented trace maps are defined before extension to $\bar K$. Thus

$$
g\,\kappa_{\mathrm{ét}}(a,b)
=\kappa_{\mathrm{ét}}(a,b)
\qquad(g\in G_K),
\tag{8.17}
$$

and the associated étale operator is $G_K$-equivariant. This conclusion uses no choice of resolution and no averaging of a singular support.

## 9. Proper pushforward, trace, and finite maps

The span formalism needs only three covariant operations: the trace of a smooth proper surface, integration along a projection whose fiber is such a surface, and the oriented trace of a finite flat lci map between smooth proper surfaces. Regular codimension-at-most-two Gysin maps were constructed in Chapter 8. We prove comparison for this closed list and make no claim here about arbitrary proper maps or arbitrary-dimensional targets.

### 9.1 The three pushforwards used below

First, the trace to a point is the map already normalized in (4.13), (6.11), and (7.8). Second, for smooth proper surfaces $S$ and $Y$, the projection

$$
p_Y:S\times Y\longrightarrow Y
$$

has integration along the $S$-factor. On exterior products it is

$$
p_{Y*}(u\boxtimes v)=\operatorname{Tr}_S(u)\,v,
\tag{9.1}
$$

with the expression zero unless $u$ has top degree. Derived Künneth makes (9.1) a map of perfect complexes, so it includes finite coefficients and torsion rather than merely rational decomposable classes. The product of a finite trace with an identity is defined in the same way; in particular

$$
(a\times1_Y)_*=a_*\boxtimes1_Y.
\tag{9.2}
$$

Third, let $f:X\to Y$ be finite flat lci of constant degree between smooth proper surfaces. Its graph $j_f:X\hookrightarrow X\times Y$ is regular of codimension two. Define its oriented finite trace by the graph--projection factorization

$$
f_*=(p_Y)_*\,(j_f)_*.
\tag{9.3}
$$

The codimension-two shift of $(j_f)_*$ and the relative-dimension-two shift of $(p_Y)_*$ cancel. Projection formula for the graph shows that this trace is characterized by

$$
\operatorname{Tr}_Y(f_*x\smile y)
=\operatorname{Tr}_X(x\smile f^*y).
\tag{9.4}
$$

At integral level (9.1)--(9.4) are maps and identities of derived perfect complexes. This is essential in the presence of torsion. Formula (9.3) also shows directly that the orientation is the regular-lci orientation; properness alone would not define an untwisted trace.

### 9.2 Comparison of pushforward

First let $f$ be a surface projection, with $r=2$, or an oriented finite map between surfaces, with $r=0$. Insert (4.13), and its product-fourfold form (4.14), into the adjoint identity (9.4). For $x\in H_{\mathrm{dR}}^n(X)$ and complementary $y\in H_{\mathrm{dR}}^*(Y)$,

$$
\begin{aligned}
\int_Y\operatorname{comp}(f_*^{\mathrm{dR}}x)\smile\operatorname{comp}(y)
&=(2\pi i)^{\dim Y}\operatorname{Tr}_Y(f_*x\smile y)\\
&=(2\pi i)^{\dim Y}\operatorname{Tr}_X(x\smile f^*y)\\
&=(2\pi i)^{-r}
\int_X\operatorname{comp}(x)\smile f^*\operatorname{comp}(y).
\end{aligned}
\tag{9.5}
$$

Topological adjunction and perfection imply

$$
\operatorname{comp}_{\mathrm{dR},B}(f_*^{\mathrm{dR}}x)
=(2\pi i)^{-r}f_*^B
\operatorname{comp}_{\mathrm{dR},B}(x).
\tag{9.6}
$$

For a retained closed immersion of codimension $c\le2$, equation (8.6) gives the same formula (9.6) with $r=-c$ directly from the local Thom calculation; no trace normalization in a higher-dimensional ambient variety is being invoked. For a projection of relative dimension two, the factor is $(2\pi i)^{-2}$. For a finite map between surfaces, $r=0$ and there is no period factor.

Betti--étale comparison carries the integral derived pairing and point trace to their étale counterparts. The same uniqueness argument gives an exactly commutative square

$$
\begin{array}{ccc}
H_B^n(X,\Lambda(j))&\xrightarrow{f_*}&
H_B^{n-2r}(Y,\Lambda(j-r))\\
\downarrow\wr&&\downarrow\wr\\
H_{\mathrm{ét}}^n(X,\Lambda(j))&\xrightarrow{f_*}&
H_{\mathrm{ét}}^{n-2r}(Y,\Lambda(j-r)).
\end{array}
\tag{9.7}
$$

The Betti twists in this diagram use (6.10) at finite level and its inverse limit. For a surface projection, the square is checked on exterior products using the surface comparison and then on the full derived tensor product. For a finite map, it is the composite of the codimension-two graph Gysin square and the surface-projection square. Thus (9.7) uses no comparison theorem for an arbitrary higher-dimensional proper map.

### 9.3 Projection, composition, and base change

For the retained maps, the graph calculation and the tensor description of projection yield the projection formula

$$
f_*(x\smile f^*y)=f_*x\smile y.
\tag{9.8}
$$

Finite oriented traces are transitive: for a tower of finite flat lci maps, both graph factorizations have the same pairing (9.4) with every test class. Consider a Cartesian square of retained maps between smooth schemes in the surface/product range,

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
{\scriptstyle f'}\downarrow&&\downarrow{\scriptstyle f}\\
Y'&\xrightarrow{g}&Y,
\end{array}
\tag{9.9}
$$

If either $f$ or $g$ is flat, the square is Tor-independent and the local graph Koszul complexes base-change exactly; in particular every base-change square formed from finite-flat span legs has this property. More generally we use

$$
g^*f_*=f'_*g'^*
\tag{9.10}
$$

only when Tor-independence is separately verified. Under the clean regular-excess hypotheses (8.14)--(8.15), the right side of (9.10) is replaced by the Euler-class expression (8.16). That correction is asserted only when the classical fiber product is regular along every component, the excess quotient is locally free of rank at most two, and all vertical components are included. No base-change or convolution identity is claimed outside these cases. These formulas hold at the derived finite-coefficient level and therefore retain torsion.

### 9.4 Finite pullback and trace

Let $f:X\to Y$ be finite flat lci of constant degree $d$ between smooth proper connected surfaces. Then

$$
f_*:H^n(X)\longrightarrow H^n(Y)
\tag{9.11}
$$

is the oriented cohomological trace. In characteristic zero, over the largest open on which $f$ is étale it is the sum over the $d$ sheets, and the graph-purity construction extends it across the branch divisor. In prime-to-characteristic étale theory the same regular-lci orientation also covers an inseparable finite-flat factor: scheme-theoretic degree, rather than the number of geometric points, is the normalization.

The projection formula gives

$$
f_*f^*=d\,\operatorname{id}.
\tag{9.12}
$$

If $f$ is finite étale, the other composite $f^*f_*$ is the sum of deck transformations after passage to a Galois closure. Equations (9.6)--(9.7) show that finite pullback and oriented trace commute exactly with every comparison map. This is the finite-span functoriality used in the remainder of the book.

## 10. Künneth formulas and kernels

A cohomological kernel on a product becomes an operator only after Künneth and Poincare duality are fixed, including their integral derived form.

### 10.1 Derived Künneth

For finite CW complexes the Eilenberg--Zilber shuffle map is a multiplicative chain homotopy equivalence

$$
C^\bullet_B(X\times Y,\mathbf Z)
\simeq
C^\bullet_B(X,\mathbf Z)\otimes_{\mathbf Z}^L
C^\bullet_B(Y,\mathbf Z).
\tag{10.1}
$$

For a finite coefficient ring $\Lambda$, proper Künneth identifies the product complex with the derived tensor product of the two factor complexes. The comparison morphism is compatible with exterior products; since Theorem 6.3 compares both surface factors, the Künneth square proves finite Betti--étale comparison for the fourfold $X\times Y$. Thus no unproved higher-dimensional comparison theorem is being inserted here.

Apply this finite formula to the normalized towers and take derived inverse limit. Perfectness of the complexes gives

$$
R\Gamma_{\mathrm{ét}}(X\times Y,\mathbf Z_\ell)
\simeq
R\Gamma_{\mathrm{ét}}(X,\mathbf Z_\ell)
\otimes_{\mathbf Z_\ell}^L
R\Gamma_{\mathrm{ét}}(Y,\mathbf Z_\ell).
\tag{10.2}
$$

This is carried to (10.1) by comparison. At cohomology level it produces short exact sequences with tensor terms and adjacent $\operatorname{Tor}_1$ terms; those terms must not be dropped when either factor has $\ell$-torsion.

For de Rham cohomology, the exterior product of forms gives a filtered quasi-isomorphism

$$
R\Gamma_{\mathrm{dR}}(X)\otimes_K^L R\Gamma_{\mathrm{dR}}(Y)
\xrightarrow{\sim}R\Gamma_{\mathrm{dR}}(X\times Y).
\tag{10.3}
$$

One proof resolves the factors by finite Cech complexes of locally free forms and filters the product double complex by form degree. On the associated graded, coherent Künneth follows from flat base change and the projection formula. The bounded spectral sequence then proves (10.3). Its filtration is the convolution filtration.

Over a field $E$ equal to $K$, $\mathbf Q$, $\mathbf C$, or $\mathbf Q_\ell$, the Tor terms vanish and

$$
H^n(X\times Y,E)
\simeq\bigoplus_{a+b=n}H^a(X,E)\otimes_EH^b(Y,E).
\tag{10.4}
$$

Every comparison map respects these decompositions.

### 10.2 The diagonal and the identity

Let $X$ be a smooth proper surface and choose a homogeneous basis $\{e_\alpha\}$ of $H^*(X,E)$ with the left Poincare-dual basis $\{e_\alpha^\vee\}$, normalized by

$$
\operatorname{Tr}_X(e_\alpha^\vee\smile e_\beta)=\delta_{\alpha\beta}.
$$

Under Künneth,

$$
\operatorname{cl}(\Delta_X)
=\sum_\alpha(-1)^{\deg e_\alpha}
e_\alpha^\vee\otimes e_\alpha,
\tag{10.5}
$$

with the sign dictated by moving a graded class past the first tensor factor. To verify (10.5), pair both sides with $p_1^*x\smile p_2^*y$. Restriction to the diagonal gives $\operatorname{Tr}_X(xy)$, while the right side gives the same value by dual-basis expansion. Perfection proves equality.

Consequently the diagonal kernel acts as the identity. Formula (10.5) is also the coevaluation element for the dualizable object $R\Gamma(X,E)$.

### 10.3 A codimension-two kernel

For smooth proper surfaces $X$ and $Y$, a class

$$
\gamma\in H^4(X\times Y,E)(2)
$$

where the twist is literal in étale theory, denotes the Betti Tate normalization in Betti theory, and is suppressed in de Rham notation. The class has Künneth components

$$
\gamma_{a,4-a}\in H^a(X,E)\otimes H^{4-a}(Y,E)(2).
\tag{10.6}
$$

After dualizing the first factor by Poincare duality, $\gamma_{4-n,n}$ is precisely a degree-preserving map

$$
H^n(X,E)\longrightarrow H^n(Y,E).
\tag{10.7}
$$

The other Künneth components act on the other cohomological degrees. Thus a single codimension-two cohomological kernel acts on total cohomology while preserving the grading. No algebraic Künneth projector is required to isolate its action on $H^2$; one simply restricts the graded operator.

### 10.4 Cohomological Künneth projectors

Decompose the diagonal class according to (10.4):

$$
\operatorname{cl}(\Delta_X)=\sum_{n=0}^4\pi_n^R,
\qquad
\pi_n^R\in
H^{4-n}(X,E)\otimes H^n(X,E)(2).
\tag{10.8}
$$

As a kernel, $\pi_n^R$ is the identity on $H^n(X,E)$ and zero on every other degree. Consequently

$$
\pi_m^R\circ\pi_n^R=\delta_{mn}\pi_n^R,
\qquad
\sum_n\pi_n^R=\operatorname{cl}(\Delta_X),
\qquad
(\pi_n^R)^t=\pi_{4-n}^R.
\tag{10.9}
$$

These identities follow either by applying the kernels to each graded piece or by contracting their Künneth tensors. Comparison carries $\pi_n^{\mathrm{dR}}$ to $\pi_n^B$ and $\pi_n^B$ to $\pi_n^{\mathrm{ét}}$.

The superscript $R$ matters. Künneth constructs these as cohomology classes; it does not prove that each $\pi_n^R$ has an algebraic representative. For the middle-degree tracking needed later, no such algebraicity is required. Every finite-span operator preserves the cohomological grading, hence commutes as an operator with every $\pi_n^R$. If $e$ vanishes outside degree two, then

$$
e_R=\pi_2^R e_R=e_R\pi_2^R
\tag{10.10}
$$

as an endomorphism of total cohomology. This is an operator identity, not an asserted equality of algebraic kernels.

## 11. Correspondences and comparison

We can now assemble the operations into the oriented finite-span formalism used by the comparison theorem.

### 11.1 Definition and action

Let $X$ and $Y$ be smooth proper surfaces over $K$. An **admissible span** is

$$
T=(X\xleftarrow{a}Z\xrightarrow{b}Y),
\tag{11.1}
$$

where $Z$ is a smooth proper surface and $a,b$ are finite flat lci maps of constant degree, equipped with the graph orientations of Chapter 9. Finite disjoint unions and formal linear combinations over a characteristic-zero field $E$ are allowed. In any $E$-linear realization define

$$
T_*x=b_*a^*x.
\tag{11.2}
$$

Both legs have virtual relative dimension zero, so (11.2) preserves degree and has no residual Tate twist. The kernel $\kappa_R(a,b)$ of (8.9) gives the equivalent formula

$$
T_*x=(p_Y)_*
\bigl(p_X^*x\smile\kappa_R(a,b)\bigr).
\tag{11.3}
$$

Indeed, apply the projection formula first to $a\times1_Y$ and then to the graph $j_b$; the result is $b_*a^*x$. This proves kernel--span agreement without assigning a class to the scheme-theoretic image of $(a,b)$.

For de Rham comparison, (8.11) contributes $(2\pi i)^2$, while (9.6) for $p_Y$ contributes $(2\pi i)^{-2}$. They cancel:

$$
\operatorname{comp}_{\mathrm{dR},B}(T_*^{\mathrm{dR}}x)
=T_*^B\operatorname{comp}_{\mathrm{dR},B}(x).
\tag{11.4}
$$

For Betti--étale comparison, graph Gysin (8.7), finite trace (9.7), and projection trace give

$$
\operatorname{comp}_{B,\mathrm{ét}}(T_*^Bx)
=T_*^{\mathrm{ét}}\operatorname{comp}_{B,\mathrm{ét}}(x).
\tag{11.5}
$$

Equations (11.4)--(11.5) are exact, with no scalar left over. The same is therefore true for every linear combination or polynomial in admissible span operators.

### 11.2 Finite maps, identity, and scalar extension

For a finite flat lci map $f:X\to Y$, the two admissible spans

$$
X\xleftarrow{1_X}X\xrightarrow{f}Y,
\qquad
Y\xleftarrow{f}X\xrightarrow{1_X}X
\tag{11.6}
$$

act as $f_*$ and $f^*$, respectively. Their kernels are the oriented graph class and its transpose. The identity span $X\xleftarrow{1_X}X\xrightarrow{1_X}X$ has kernel $[\Delta_X]$ and acts as the identity by Section 10.2.

No assertion is made here about the graph action of an arbitrary proper morphism. The only covariant graph operation used in degree zero is the oriented finite trace of Section 9.4. Extension from rational coefficients to a number field or one of its completions is ordinary scalar extension, so all identities in this section remain literal after changing coefficient fields.

### 11.3 Composition

Let

$$
T=(X\xleftarrow{a}Z\xrightarrow{b}Y),
\qquad
S=(Y\xleftarrow{c}W\xrightarrow{d}U)
$$

be admissible spans. Their operators can always be composed, and (11.4)--(11.5) immediately show that $S_*T_*$ is the same composite in all realizations. A geometric fiber-product description requires more.

Put $P=Z\times_YW$, with projections $r:P\to Z$ and $s:P\to W$. If the middle square is Tor-independent and $P$ is a smooth proper surface, the induced legs are again finite flat lci and the composite span is

$$
X\xleftarrow{a\circ r}P\xrightarrow{d\circ s}U.
\tag{11.7}
$$

Finite-flatness of either middle leg supplies Tor-independence, but smoothness of the classical carrier $P$ is still a separate requirement. Under these hypotheses, finite base change (9.10), transitivity, and projection give

$$
(d\circ s)_*(a\circ r)^*
=d_*s_*r^*a^*
=d_*c^*b_*a^*
=S_*T_*.
\tag{11.8}
$$

At the level of integral or semistable models one sometimes meets oriented regular-lci pull--push diagrams in which flatness of the relevant square is not available. Suppose such a middle square satisfies all clean regular-excess hypotheses of (8.14)--(8.15), including regularity of every component and a locally free excess bundle $E$ of rank at most two. Then the only nontransverse formula retained here is

$$
d_*s_*\bigl(e(E)\smile r^*a^*x\bigr).
\tag{11.9}
$$

Formula (11.9) is a decorated cohomological composite, not an undecorated finite span. Its comparison follows from the proved Euler-class calculation in Section 8.3. If the fiber product is singular, the excess quotient is not locally free, or a vertical component is missing, neither (11.7) nor (11.9) is asserted.

Operator composition is associative without any geometric assertion. A geometric iterated composite is identified with that operator only when every intermediate square in the chosen parenthesization satisfies the transverse/Tor-independent hypotheses above, or when compatible clean-excess data are supplied at every stage. This is the precise boundary that avoids an unproved nontransverse convolution on $X\times Y\times U$.

### 11.4 Transpose and adjoint

The transpose of $T=(X\xleftarrow{a}Z\xrightarrow{b}Y)$ is the admissible span $T^t=(Y\xleftarrow{b}Z\xrightarrow{a}X)$. The adjoint identity (9.4) twice gives

$$
\langle T_*x,y\rangle_Y
=\langle x,(T^t)_*y\rangle_X.
\tag{11.10}
$$

Thus transpose is cohomological adjoint in all three realizations.

If the coefficient field $E$ has an involution $a\mapsto a^\dagger$, define

$$
T^\dagger=\sum \alpha_i^\dagger T_i^t
\quad\text{when}\quad
T=\sum \alpha_iT_i.
\tag{11.11}
$$

With the corresponding sesquilinear pairing, $T^\dagger$ is the adjoint. Polynomials in span operators inherit this involution by reversing products.

The identity involution is the default. If a nontrivial coefficient involution is used after completion, it is assumed to extend continuously to that completion.

### 11.5 Filtration, Hodge type, and Galois action

A graph class has Hodge type $(2,2)$. Equivalently, pullback and oriented finite trace have filtered degree zero. Therefore every admissible span operator, and every polynomial in such operators, preserves the Hodge filtration and is a morphism of Hodge structures of type $(0,0)$ after comparison.

If the span is defined over $K$, both legs and their orientations are defined before geometric base change. Hence

$$
gT_*=T_*g
\qquad(g\in G_K).
\tag{11.12}
$$

Combining the preceding sections gives the exact absolute functoriality statement.

**Theorem 11.1 (comparison of oriented surface spans).** Let $X$ and $Y$ be smooth proper surfaces, and let $T$ be an $E$-linear combination of admissible finite-flat lci spans (11.1). Then de Rham--Betti and Betti--étale comparison intertwine $T_*$ exactly. They also intertwine every ordered polynomial in such operators, transpose, adjoint, cup and exterior products, Künneth, the regular codimension-at-most-two Gysin maps of Chapter 8, the product projections of Section 9.1, and oriented finite trace. Poincare pairings and normalized traces correspond. The graph factor $(2\pi i)^2$ and surface-projection factor $(2\pi i)^{-2}$ cancel in the kernel formula.

If two spans have a Tor-independent smooth fiber-product carrier, their geometric composite is (11.7) and realizes operator composition. For a model-level oriented regular-lci diagram satisfying the clean regular-excess hypotheses (8.14)--(8.15), the decorated formula (11.9) realizes the corresponding base-change correction and compares. No conclusion is claimed for an arbitrary singular support, an arbitrary rational Chow correspondence, or a nontransverse convolution lacking that explicit regular-excess datum.

**Proof.** For one span, Sections 8.2 and 9.4 construct the same kernel and pull--push operator; equations (11.4)--(11.5) prove comparison, including the period cancellation. Linearity and composition of intertwining maps give the polynomial assertion without any geometric convolution. Equation (9.10) proves the smooth Tor-independent fiber-product formula. The local Koszul proof of (8.16) proves the stated clean-excess alternative and its comparison, with no appeal to a general refined Chow theory. Finally (11.10) proves adjointness, while graph Gysin followed by product trace proves filtration and Galois compatibility. $\square$

## 12. Projectors and the middle-degree summand

We now formulate the statement needed when a projector is first constructed analytically or by interpolation in an algebra of admissible span operators.

### 12.1 Scalar coefficients

Let $L$ be a number field. Put

$$
H_B^i(X,L)=H_B^i(X,\mathbf Q)\otimes_{\mathbf Q}L,
$$

and for a finite place $\lambda\mid\ell$ put

$$
H_{\mathrm{ét}}^i(X_{\bar K},L_\lambda)
=H_{\mathrm{ét}}^i(X_{\bar K},\mathbf Q_\ell)
\otimes_{\mathbf Q_\ell}L_\lambda.
\tag{12.1}
$$

For de Rham coefficients put

$$
H_{\mathrm{dR}}^i(X,L)
=H_{\mathrm{dR}}^i(X/K)
\otimes_K(K\otimes_{\mathbf Q}L),
$$

interpreted component by component when $K\otimes_{\mathbf Q}L$ is not a field. An embedding $\tau:L\hookrightarrow\mathbf C$ selects the corresponding complex component. All comparison assertions are obtained by scalar extension from their rational forms.

Let $\mathscr A_L(X)$ be the $L$-subalgebra of endomorphisms of total cohomology generated by admissible span operators. An element is specified by one ordered polynomial expression in finitely many such spans; equivalently one may use the free associative algebra $L\langle t_1,\ldots,t_s\rangle$, and use the ordinary polynomial ring when the generators commute. Comparison evaluates the same expression in every realization. Let

$$
e=P(T_1,\ldots,T_s)\in\mathscr A_L(X).
\tag{12.2}
$$

It acts degree by degree in every realization. It is enough that its total Betti action be idempotent. Indeed, (11.4) makes $e_{\mathrm{dR}}^2-e_{\mathrm{dR}}$ zero after the faithfully flat extension to $\mathbf C$, and (11.5) does the same after extension to $L_\lambda$. Hence it was zero before extension. No equality of algebraic cycles is needed.

### 12.2 Tracking total cohomology and $H^2$

Write

$$
eH_R^*(X)=\bigoplus_{i=0}^4 eH_R^i(X).
\tag{12.3}
$$

Comparison restricts to isomorphisms on each image because it intertwines the idempotents:

$$
eH_{\mathrm{dR}}^i(X)\otimes\mathbf C
\simeq eH_B^i(X,\mathbf C),
\tag{12.4}
$$

$$
eH_B^i(X,L)\otimes_LL_\lambda
\simeq eH_{\mathrm{ét}}^i(X_{\bar K},L_\lambda).
\tag{12.5}
$$

Suppose an analytic calculation establishes

$$
eH_B^i(X,\mathbf C)=0\qquad(i\ne2).
\tag{12.6}
$$

Faithful scalar extension and (12.4)--(12.5) imply the same vanishing in all realizations. Therefore

$$
eH_R^*(X)=eH_R^2(X)
\tag{12.7}
$$

and the dimensions of the three middle summands agree. This argument uses the ordinary cohomological grading, not an algebraic Künneth decomposition of the diagonal.

The de Rham summand inherits the Hodge filtration, since $e$ is filtered. The Betti summand is a sub-Hodge structure. The étale summand is $G_K$-stable by (11.12). Thus a single span-algebra projector produces

$$
V_B=eH_B^2(X,L),\qquad
V_{\mathrm{dR}}=eH_{\mathrm{dR}}^2(X,L),\qquad
V_\lambda=eH_{\mathrm{ét}}^2(X_{\bar K},L_\lambda),
\tag{12.8}
$$

with exactly the extra structure expected in each realization.

### 12.3 The adjoint summand and duality

Let $e^\dagger$ be the adjoint projector of (11.11) and put

$$
V_\lambda^\dagger=e^\dagger
H_{\mathrm{ét}}^2(X_{\bar K},L_\lambda).
$$

The ambient trace pairing is

$$
H_{\mathrm{ét}}^2(X,L_\lambda)
\times H_{\mathrm{ét}}^2(X,L_\lambda)
\longrightarrow L_\lambda(-2).
\tag{12.9}
$$

Equation (11.10) shows that its restriction gives a perfect pairing

$$
V_\lambda\times V_\lambda^\dagger
\longrightarrow L_\lambda(-2).
\tag{12.10}
$$

For if $x\in eH^2$ pairs to zero with $e^\dagger H^2$, then
$\langle x,y\rangle=\langle ex,y\rangle=\langle x,e^\dagger y\rangle=0$ for every $y$; ambient perfection gives $x=0$. The same argument in the other factor and equality of ranks prove perfection. Equivalently,

$$
V_\lambda^\vee\simeq V_\lambda^\dagger(2).
\tag{12.11}
$$

At a good fiber over $\mathbf F_q$, geometric Frobenius acts on the target $L_\lambda(-2)$ by $q^2$. If $\alpha$ is an eigenvalue on $V_\lambda$ and $\beta$ is the eigenvalue on the paired line of $V_\lambda^\dagger$, Frobenius equivariance of (12.10) gives

$$
\alpha\beta=q^2.
$$

Thus the adjoint Frobenius polynomials are reciprocal with factor $q^2$, not $q^{-2}$.


If $e=e^\dagger$, the summand is self-dual up to twist. The identical argument applies to Betti and de Rham pairings, with the period normalization of (4.13).

### 12.4 Integral lattices and denominators

A rational projector does not act on torsion and need not preserve a chosen integral lattice. Let $\mathcal O_L$ be the integers of $L$, let

$$
\Lambda=H_B^2(X,\mathbf Z)_{\mathrm{free}}\otimes_{\mathbf Z}\mathcal O_L,
$$

and choose $N>0$ clearing the coefficients of the chosen polynomial expression for $e$. Since pullback and oriented finite trace act integrally, $Ne$ preserves the integral Betti complex after tensoring with $\mathcal O_L$. Inside $V_B=eH_B^2(X,L)$ define

$$
\Lambda_e=V_B\cap\Lambda.
\tag{12.12}
$$

It is a full lattice and is saturated in $\Lambda$: if $a x\in\Lambda_e$ for a nonzero $a\in\mathcal O_L$ and $x\in\Lambda$, then $x\in V_B$ because $V_B$ is an $L$-subspace. Saturation does not identify it with $e\Lambda$, and it does not supply a canonical complementary lattice.

At a finite place $\lambda\nmid N$, the coefficients of $e$ are integral, so $e$ preserves $\Lambda\otimes\mathcal O_{L_\lambda}$ and

$$
\Lambda\otimes\mathcal O_{L_\lambda}
=e\Lambda_\lambda\oplus(1-e)\Lambda_\lambda.
\tag{12.13}
$$

At $\lambda\mid N$, neither preservation nor direct-summand status follows. If integral idempotence is separately known, (12.13) holds there as well. No statement about the action of a merely rational $e$ on the torsion subgroup of $H_B^2(X,\mathbf Z)$ is meaningful without an integral lift.

### 12.5 Interpolated operators

Suppose $T_1,\ldots,T_s$ are commuting admissible span operators and a polynomial
$P\in L[t_1,\ldots,t_s]$ is chosen so that

$$
e=P(T_1,\ldots,T_s)
\tag{12.14}
$$

acts as the desired spectral projector on total Betti cohomology. Because comparison intertwines every $T_j$, it intertwines $P(T_1,\ldots,T_s)$. Thus all conclusions of Sections 12.1--12.4 hold without reconstructing $P$ in another realization. The primes dividing a chosen denominator of $P$ are the only primes potentially excluded by this integral argument; evaluation of the polynomial can still produce an integral idempotent at one of them.

### 12.6 A denominator visible on a lattice

The elementary lattice

$$
\Lambda=\mathbf Z^2,
\qquad
e=\frac12
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix}
\tag{12.15}
$$

models the integral issue exactly. Over $\mathbf Q$, $e^2=e$ and its image is the diagonal line. Yet $e(1,0)=(1/2,1/2)$, so $e$ does not preserve $\Lambda$. The saturated intersection is

$$
\operatorname{im}(e)\cap\Lambda=\mathbf Z(1,1).
\tag{12.16}
$$

After tensoring with $\mathbf Z_\ell$, the projector preserves and splits the lattice for every odd $\ell$, but not for $\ell=2$. Any interpolated span-algebra projector has the same behavior, with its interpolation denominator replacing $2$.

## 13. Lefschetz traces and projected Frobenius

The last absolute operation is trace. A kernel always has a cohomological trace. It has a literal geometric intersection-degree formula only under the transverse or clean regular-excess hypotheses proved above.

### 13.1 The kernel trace identity

Let $T=(X\xleftarrow{a}Z\xrightarrow{b}X)$ be an admissible endospan, or an $E$-linear combination of such spans. Its Lefschetz number is

$$
L(T)=\sum_{i=0}^4(-1)^i
\operatorname{Tr}\bigl(T_*\mid H^i(X,E)\bigr).
\tag{13.1}
$$

For its cohomological kernel $\kappa_R(T)$,

$$
L(T)=\operatorname{Tr}_X\bigl(\Delta_X^*\kappa_R(T)\bigr).
\tag{13.2}
$$

The fixed scheme of one span is $Z\times_{X\times X}X$, where $Z\to X\times X$ is $(a,b)$ and $X\to X\times X$ is the diagonal. If this square is transverse and its fixed scheme is finite, (13.2) is the sum of its scheme-theoretic local degrees; at a reduced transverse point the contribution is one. If the square satisfies (8.14)--(8.15), is proper, and has every component included, (13.2) is the trace of the explicit Euler-class expression (8.16). Outside those two cases we retain the cohomological scalar (13.2), but do not rename it the degree of a refined algebraic intersection.

**Proof.** Under Künneth and Poincare duality, $\kappa_R(T)$ is the kernel of $T_*$. Pullback to the diagonal contracts its two tensor factors. The Koszul sign in (10.5) makes that contraction the graded trace, and the normalized trace of $X$ gives (13.1). For one carrier map put $h=(a,b):Z\to X\times X$, but retain the allowed factorization

$$
\kappa_R(T)=(a\times1_X)_*(j_b)_*1.
$$

Let $q:Z\to Z\times X$ be $q(z)=(z,a(z))$. The Cartesian square formed by $\Delta_X$ and the finite-flat map $a\times1_X$ is Tor-independent. Finite-flat base change, followed by adjunction for the regular graph $j_b$, gives

$$
\operatorname{Tr}_X\bigl(\Delta_X^*\kappa_R(T)\bigr)
=\operatorname{Tr}_Z\bigl(q^*(j_b)_*1\bigr)
=\operatorname{Tr}_Z\bigl(h^*\Delta_{X*}1\bigr).
$$

Every pushforward in this calculation is therefore either the product of an oriented finite-flat trace with an identity, a regular codimension-two graph Gysin map, or a surface trace. In the transverse case, (8.13) identifies the last class with the fundamental classes of the finite fixed scheme. Under the stated clean-excess hypotheses, (8.16), applied to the pullback of the regular diagonal along $h$, inserts $e(E)$. These are exactly the two geometric identifications asserted. $\square$

This proof works in Betti, de Rham, and étale theory. In de Rham theory the codimension-two graph factor and the surface trace factor cancel; in étale theory the two Tate twists cancel. Thus the scalar is literally the same whenever the realizations are compared.

### 13.2 Frobenius convention

Let $X_0$ be a smooth proper surface over $\mathbf F_q$, let $\varphi:X_0\to X_0$ be the $q$-power morphism, and let $F$ denote cohomological geometric Frobenius, normalized to act on $L_\lambda(1)$ by $q^{-1}$. Under the correspondence convention (11.2), the transpose of the graph of $\varphi$ acts as $F$. Its fixed-point intersection with the diagonal gives

$$
\#X_0(\mathbf F_{q^m})
=\sum_i(-1)^i
\operatorname{Tr}\bigl(F^m\mid
H_{\mathrm{ét}}^i(X_{\overline{\mathbf F}_q},L_\lambda)\bigr).
\tag{13.3}
$$

The local intersection is one because the differential of $\varphi^m-\operatorname{id}$ is $-\operatorname{id}$. This proves the smooth proper Lefschetz trace formula directly from (13.2).

### 13.3 Projected traces

Let $e$ be a projector in the algebra generated by admissible spans defined over $\mathbf F_q$, and suppose it commutes with $F$. Its cohomological diagonal trace is always defined. For a geometric degree formula, assume in addition that the operator $e$ is represented by a finite $L$-linear combination $\sum_j\alpha_jT_j$ of admissible endospans with smooth carriers; this requires, for example, that every composition used to expand the chosen polynomial meet Section 11.3. If $T_j=(X\xleftarrow{a_j}Z_j\xrightarrow{b_j}X)$, its $m$th Frobenius-twisted fixed locus is the equalizer $b_j(z)=\varphi^m(a_j(z))$. Assume, for the values of $m$ under consideration, that each such locus is either finite and transverse or satisfies the clean regular-excess hypotheses of Section 8.3 with proper fixed locus and all components present. Let $I_m(e)\in L$ be the corresponding sum of scheme-theoretic degrees or Euler-class degrees, weighted by $\alpha_j$. Then

$$
\sum_i(-1)^i
\operatorname{Tr}\bigl(F^me\mid H_{\mathrm{ét}}^i(X,L_\lambda)\bigr)=
I_m(e).
\tag{13.4}
$$

The right side is defined by the same algebraic fixed-locus data for every coefficient prime and is therefore independent of $\lambda$. If the stated fixed-locus hypotheses are unavailable, the Lefschetz--Verdier theorem still expresses the left side as local cohomological terms, but this book does not turn those terms into an unproved algebraic intersection degree.

To extract the middle trace one needs **étale degree isolation**: for the chosen $\lambda$, the specialized operator must satisfy

$$
eH^i_{\mathrm{ét}}(X_{\overline{\mathbf F}_q},L_\lambda)=0
\qquad(i\ne2).
$$

This follows, for example, from Chapter 12 together with an extending span projector and good-specialization isomorphism; it is not inferred merely from a total Lefschetz number. Under this hypothesis the sign in degree two is positive and

$$
\operatorname{Tr}(F^m\mid V_\lambda)=
I_m(e).
\tag{13.5}
$$

Thus no algebraic degree-two Künneth projector is needed, but actual isolation of every other étale degree is indispensable.

### 13.4 Purity and characteristic polynomials

The purity theorem for smooth proper varieties over finite fields says that every eigenvalue of $F$ on $H^i$ has complex absolute value $q^{i/2}$ under every embedding into $\mathbf C$. Since $e$ commutes with $F$,

$$
H^2=eH^2\oplus(1-e)H^2
$$

is an $F$-stable decomposition. Every eigenvalue on $V_\lambda=eH^2$ is therefore an eigenvalue on ambient $H^2$ and has absolute value $q$.

Let $r=\dim_{L_\lambda}V_\lambda$, and assume the fixed-locus and étale degree-isolation hypotheses of Section 13.3 for $1\le m\le r$ at every coefficient prime being compared. The power sums

$$
s_m=\operatorname{Tr}(F^m\mid V_\lambda),
\qquad 1\le m\le r,
\tag{13.6}
$$

determine the characteristic polynomial by Newton's identities:

$$
k\,c_k+\sum_{j=1}^kc_{k-j}s_j=0,
\qquad c_0=1.
\tag{13.7}
$$

No semisimplicity hypothesis is used. By (13.5), the $s_m$ lie in $L$ and are independent of $\lambda$, so the same is true of the characteristic polynomial. If $e$ has denominators, its coefficients and traces need not be algebraic integers at the denominator primes; purity remains valid because it concerns eigenvalues of the ambient cohomology.

## 14. Smooth proper families

Comparison must vary in families, since good reduction and degeneration are statements about a model rather than an isolated complex fiber.

### 14.1 The three relative objects

Let $f:\mathcal X\to S$ be a smooth proper morphism of relative dimension two in characteristic zero. For the Hodge statements assume it is projective. There are three relative cohomology objects.

Over $\mathbf C$, the analytic map is a proper submersion. Ehresmann's theorem gives local differentiable trivializations, so

$$
\mathbb H_B^n=R^nf_*^{\mathrm{an}}\mathbf Z
\tag{14.1}
$$

is a local system of finitely generated abelian groups. It may contain a locally constant torsion subgroup.

Algebraically,

$$
\mathcal H_{\mathrm{dR}}^n
=R^nf_*\Omega^\bullet_{\mathcal X/S}
\tag{14.2}
$$

is a finite locally free $\mathcal O_S$-module with the Gauss--Manin connection

$$
\nabla:\mathcal H_{\mathrm{dR}}^n
\longrightarrow
\mathcal H_{\mathrm{dR}}^n\otimes\Omega_S^1.
\tag{14.3}
$$

Filter the absolute de Rham complex by the number of base differentials. The first connecting morphism of the resulting exact sequence is (14.3); the identity $d^2=0$ gives $\nabla^2=0$. The relative form filtration gives subbundles $F^p$, and the same filtered-complex calculation gives Griffiths transversality:

$$
\nabla F^p\subset F^{p-1}\otimes\Omega_S^1.
\tag{14.4}
$$

Why are these sheaves locally free and compatible with base change? On each complex fiber, Chapter 5 degenerates the Hodge-to-de Rham spectral sequence. The Betti numbers are locally constant by (14.1), while upper semicontinuity applies to every $H^q(\Omega^p)$. Constancy of their diagonal sums, beginning at the outer diagonals and proceeding inward, forces local constancy of the Hodge numbers. Cohomology and base change then makes the $R^qf_*\Omega^p$ locally free and proves fiberwise base change. Degeneration of the relative spectral sequence follows because its differentials vanish on every fiber. Faithfully flat descent carries the result from complex embeddings back to a characteristic-zero base.

For $\ell$ invertible on $S$,

$$
\mathbb H_{\ell,m}^n=R^nf_{\mathrm{ét},*}
\mathbf Z/\ell^m,
\qquad
\mathbb H_\ell^n=R\varprojlim_m\mathbb H_{\ell,m}^n
\tag{14.5}
$$

are lisse finite and lisse adic sheaves. The adic stalk can have finite $\ell$-torsion; lisse does not mean free.

### 14.2 Relative complex comparison

On a simply connected analytic open $V\subset S^{\mathrm{an}}$, choose an Ehresmann trivialization. Integrating relative forms over a flat family of cycles gives

$$
(\mathcal H_{\mathrm{dR}}^n)^{\mathrm{an}}\big|_V
\xrightarrow{\sim}
\mathbb H_B^n\big|_V\otimes_{\mathbf Z}\mathcal O_V.
\tag{14.6}
$$

Differentiating a period integral shows that the left Gauss--Manin connection corresponds to the connection for which the Betti sections are horizontal. This calculation is independent of the differentiable trivialization, so the local maps glue. Relative GAGA identifies the coherent algebraic direct images with their analytic direct images; hence (14.6) is the family version of Theorem 4.1. It respects cup products, the Hodge filtration, the relative surface trace, and the finite-flat span operations specified below.

For finite coefficients, the natural morphism

$$
(R^nf_{\mathrm{ét},*}\mathbf Z/\ell^m)^{\mathrm{an}}
\longrightarrow
R^nf_*^{\mathrm{an}}\mathbf Z/\ell^m
\tag{14.7}
$$

is a map of local systems. At every point its stalk is (6.9), so it is an isomorphism. Passing through the normalized tower gives the relative $\mathbf Z_\ell$ comparison. Thus the monodromy of a family is the same finite or adic monodromy on the Betti and étale sides.

### 14.3 Smooth proper base change

Consider a Cartesian square

$$
\begin{array}{ccc}
\mathcal X'&\xrightarrow{g'}&\mathcal X\\
{\scriptstyle f'}\downarrow&&\downarrow{\scriptstyle f}\\
S'&\xrightarrow{g}&S.
\end{array}
\tag{14.8}
$$

For a torsion coefficient ring $\Lambda$ whose order is invertible on $S$, smooth proper base change is the isomorphism

$$
g^*Rf_{\mathrm{ét},*}\Lambda
\xrightarrow{\sim}
Rf'_{\mathrm{ét},*}g'^*\Lambda.
\tag{14.9}
$$

The proof can be checked on geometric stalks. Replace $S$ by the strict henselization at a geometric point. Smoothness supplies étale local coordinates; on these coordinates, contraction along affine-space fibers proves local acyclicity of $\Lambda$. Properness lets local sections and their finite Cech relations extend from the closed fiber to a neighborhood. Hence restriction from the total space over the strict henselian base to either geometric fiber is a quasi-isomorphism. The two sides of (14.9) have the same stalks, proving the assertion.

For the normalized $\mathbf Z_\ell$ tower, take derived inverse limits in (14.9). Uniform finite cohomological dimension and the perfectness of smooth proper cohomology commute the limit with pullback:

$$
g^*Rf_{\mathrm{ét},*}\mathbf Z_\ell
\xrightarrow{\sim}
Rf'_{\mathrm{ét},*}\mathbf Z_\ell.
\tag{14.10}
$$

Rationalization gives the $\mathbf Q_\ell$ version.

In de Rham theory, flat base change gives

$$
g^*Rf_*\Omega^\bullet_{\mathcal X/S}
\xrightarrow{\sim}
Rf'_*\Omega^\bullet_{\mathcal X'/S'}.
\tag{14.11}
$$

For an arbitrary base change between smooth characteristic-zero bases, the local freeness proved above allows derived pullback in (14.11); fiberwise verification then proves the map is an isomorphism.

### 14.4 Relative operations and projectors

Let $\mathcal Z\to S$ be another smooth proper relative surface and let

$$
\mathcal X\xleftarrow{a}\mathcal Z\xrightarrow{b}\mathcal X
$$

be finite flat lci over $S$, with the relative graph orientations. Relative pullback and oriented finite trace define

$$
T_*=b_*a^*:R^nf_*\longrightarrow R^nf_*.
\tag{14.12}
$$

Equations (14.9)--(14.11) commute with (14.12). For pullback this is functoriality. For trace, factor each leg through its relative graph and the relative surface projection; graph purity commutes with the Tor-independent finite-flat base change, and the product trace commutes by (9.1). This proves precisely the relative operation required here, without invoking arbitrary relative cycle classes or arbitrary proper direct image.

If a polynomial $e$ in such relative span operators is idempotent on one complex fiber, horizontal transport and comparison show it is idempotent on every fiber of that connected component: $e^2-e$ is a horizontal endomorphism vanishing at one point. Its image is a sub-local system, a filtered subbundle with connection, and a lisse adic subsheaf after scalar extension. If it kills all degrees except $2$ on one fiber, local constancy and comparison give the same assertion throughout the family.

## 15. Good specialization

Let $R$ be a henselian discrete valuation ring with fraction field $K$, residue field $k$ of characteristic $p$, and geometric points $\bar\eta$ and $\bar s$ joined by a specialization. Let

$$
f:\mathcal X\longrightarrow\operatorname{Spec}R
$$

be smooth and proper of relative dimension two.

### 15.1 The specialization isomorphism

For $\ell\ne p$, smooth proper base change applied to the strict henselization gives

$$
R\Gamma_{\mathrm{ét}}(X_{\bar K},\mathbf Z/\ell^m)
\xrightarrow{\sim}
R\Gamma_{\mathrm{ét}}(X_{\bar k},\mathbf Z/\ell^m).
\tag{15.1}
$$

The arrow depends only on the chosen specialization of geometric points; two choices differ by the usual fundamental-group transport. It respects reduction in $m$. Derived inverse limit and rationalization give

$$
R\Gamma_{\mathrm{ét}}(X_{\bar K},\mathbf Z_\ell)
\xrightarrow{\sim}
R\Gamma_{\mathrm{ét}}(X_{\bar k},\mathbf Z_\ell),
\tag{15.2}
$$

$$
H_{\mathrm{ét}}^n(X_{\bar K},\mathbf Q_\ell)
\xrightarrow{\sim}
H_{\mathrm{ét}}^n(X_{\bar k},\mathbf Q_\ell).
\tag{15.3}
$$

These are derived integral statements and retain $\ell$-primary torsion.

If $R$ is strictly henselian, inertia acts trivially on the left of (15.2). In general, the $G_K$-representation is unramified and the quotient action through $G_K/I_K\simeq G_k$ agrees with the action on the special fiber. With the convention of Section 1.1, geometric Frobenius on the special fiber is the unramified geometric Frobenius on the generic representation.

No assertion here is made for $\ell=p$. The replacement at that prime requires a crystalline or semistable $p$-adic comparison theory, which is outside this coefficient interface.

### 15.2 Compatibility with operations

The maps (15.1)--(15.3) commute with cup product and normalized trace because these are maps of $Rf_*$ and relative duality. Suppose an admissible span on the generic fiber extends to a diagram

$$
\mathcal X\xleftarrow{a}\mathcal Z\xrightarrow{b}\mathcal X
$$

of finite flat lci maps over $R$, with $\mathcal Z/R$ smooth proper of relative dimension two and the graph orientations extending. Finite flat base change and oriented trace then give

$$
\operatorname{sp}\circ T_{\eta,*}
=T_{s,*}\circ\operatorname{sp}.
\tag{15.4}
$$

This is the entire correspondence-specialization assertion used here. A generic kernel whose closure is singular, nonflat, or has additional vertical components is not covered by (15.4).

Suppose an $L$-valued polynomial projector $e$ in these extending span operators has denominator $N$. For every $\lambda\mid\ell$ with $\ell\ne p$, specialization identifies

$$
eH_{\mathrm{ét}}^2(X_{\bar K},L_\lambda)
\xrightarrow{\sim}
e_sH_{\mathrm{ét}}^2(X_{\bar k},L_\lambda).
\tag{15.5}
$$

If $\lambda\nmid N$, the natural integral direct summands compare as well. At a denominator prime only the rational statement follows.

### 15.3 De Rham qualification at a mixed-characteristic prime

The generic fiber has its filtered de Rham cohomology over $K$. The relative complex
$Rf_*\Omega^\bullet_{\mathcal X/R}$ is perfect and base change holds wherever its cohomology modules are locally free. It therefore supplies an $R$-lattice in generic de Rham cohomology under that hypothesis. Integral degeneration of the Hodge-to-de Rham spectral sequence at the residue characteristic is an additional assertion and is not implied by smooth proper base change. Nor does algebraic de Rham cohomology of the special fiber compare directly with (15.2) at $\ell=p$.

Thus the good-prime interface used here is exact: Betti and de Rham compare on the characteristic-zero generic fiber; prime-to-$p$ étale cohomology specializes to the smooth special fiber; extending oriented finite-flat span operators commute with both bridges.

### 15.4 Frobenius on a projected good fiber

If $k=\mathbf F_q$, purity and (15.5) show that every Frobenius eigenvalue on the projected $H^2$ has absolute value $q$. If the specialized projector kills all other étale degrees and the fixed-locus hypotheses of Section 13.3 hold for the required powers, (13.5) computes its power traces by the stated transverse or clean-excess degrees. Under exactly those hypotheses the characteristic polynomial belongs to $L[t]$, is independent of $\lambda\ne p$, and describes the unramified Frobenius polynomial of the generic representation.

## 16. Semistable specialization

Good reduction makes nearby cycles constant. Semistable reduction does not, and the difference is recorded by monodromy.

### 16.1 Strictly semistable surfaces

Retain the trait $\operatorname{Spec}R$, but assume $\mathcal X$ is regular and proper and its special fiber

$$
Y=\bigcup_{i\in I}Y_i
$$

is a reduced simple-normal-crossing divisor. Étale locally, $\mathcal X$ has an equation

$$
x_1\cdots x_r=t,
\qquad 1\le r\le3,
\tag{16.1}
$$

where $t$ is a uniformizer. The bound $r\le3$ is the relative-surface bound: at most three components meet, at a point.

Let $j:X_{\bar\eta}\hookrightarrow\mathcal X_{\bar R}$ and
$i:Y_{\bar k}\hookrightarrow\mathcal X_{\bar R}$. For $\Lambda=\mathbf Z/\ell^m$, $\ell\ne p$, define

$$
R\Psi\Lambda=i^*Rj_*\Lambda.
\tag{16.2}
$$

Properness gives the fundamental nearby-cycle comparison

$$
R\Gamma_{\mathrm{ét}}(X_{\bar K},\Lambda)
\xrightarrow{\sim}
R\Gamma_{\mathrm{ét}}(Y_{\bar k},R\Psi\Lambda).
\tag{16.3}
$$

Indeed, both sides compute the geometric generic stalk of the proper direct image $Rf_*\Lambda$: insert (16.2), apply proper base change to $i$, and use adjunction. The isomorphism respects cup products, duality, and the inertia action carried by $R\Psi$.

It is generally false that the right side of (16.3) can be replaced by $R\Gamma(Y_{\bar k},\Lambda)$. The natural map $\Lambda_Y\to R\Psi\Lambda$ is an isomorphism precisely in the locally acyclic, in particular smooth, case.

### 16.2 The local calculation and the strata

At a point where $r$ components meet, take tame Kummer covers
$x_i^{1/n}=u_i$ with $n$ prime to $p$. Their single relation is imposed by $u_1\cdots u_r=t^{1/n}$. Put

$$
C_x=\operatorname{coker}\left(
\Lambda\xrightarrow{\,1\mapsto(1,\ldots,1)\,}\Lambda^r
\right).
$$

The tame deck group is the kernel of the corresponding summation map, while its degree-one character module is $C_x(-1)$; these two modules are dual and must not be identified integrally. Passing over all $n$ therefore gives

$$
(R^q\Psi\Lambda)_x\simeq\bigwedge^q C_x(-q).
\tag{16.4}
$$

Consequently $R^q\Psi\Lambda=0$ for $q>2$ on a semistable surface. The gluing maps among the local modules are alternating restriction and Gysin maps between strata.

Write $Y^{(a)}$ for the disjoint union of the $a$-fold intersections of distinct components. Thus $Y^{(1)}$ is a union of smooth proper surfaces, $Y^{(2)}$ a union of curves, and $Y^{(3)}$ a finite set. Filtering the logarithmic nearby-cycle complex by the number of local Kummer generators produces the weight spectral sequence

$$
E_1^{a,b}=
\bigoplus_{j\ge\max(0,-a)}
H^{b-2j}\bigl(Y^{(a+2j+1)},\mathbf Q_\ell(-j)\bigr)
\Longrightarrow
H^{a+b}(X_{\bar K},\mathbf Q_\ell).
\tag{16.5}
$$

Terms with an impossible stratum index are zero. The first differential is the alternating sum of restrictions and Gysin maps. Formula (16.5) follows directly from (16.4): resolve the union $Y$ by its alternating Cech complex, insert the exterior-degree filtration, and use purity to turn each residue generator into a twist and a shift by two.

For total degree two, only columns $-2,-1,0,1,2$ can occur. Their ingredients are, up to the indicated twists,

$$
\begin{array}{c|c}
a&\text{possible strata cohomology}\\ \hline
-2&H^0(Y^{(3)})(-2)\\
-1&H^1(Y^{(2)})(-1)\\
0&H^2(Y^{(1)})\ \oplus\ H^0(Y^{(3)})(-1)\\
1&H^1(Y^{(2)})\\
2&H^0(Y^{(3)}).
\end{array}
\tag{16.6}
$$

This table displays the surface contribution of components, double curves, and triple points.

### 16.3 Monodromy and the bound $N^3=0$

After a finite extension of $K$, tame inertia acts unipotently on rational cohomology. Choose the tame character
$t_\ell:I_t\to\mathbf Z_\ell(1)$. There is a nilpotent operator

$$
N:H^n(X_{\bar K},\mathbf Q_\ell)
\longrightarrow H^n(X_{\bar K},\mathbf Q_\ell)(-1)
\tag{16.7}
$$

such that

$$
\rho(\sigma)=\exp\bigl(t_\ell(\sigma)N\bigr)
\tag{16.8}
$$

on an open subgroup of inertia. A different compatible generator rescales $N$ and the Tate coordinate inversely, leaving the Weil--Deligne object unchanged.

On (16.5), $N$ moves two columns toward the right and twists by $-1$. In total degree two the nonzero columns lie between $-2$ and $2$. Three applications move beyond that range. Hence

$$
N^3=0\quad\text{on}\quad H^2(X_{\bar K},\mathbf Q_\ell).
\tag{16.9}
$$

This is not an imported curve statement: it follows from the three-level surface stratification (16.6). Curves have no triple stratum and yield the shorter monodromy pattern.

Since inertia preserves cup product and trace, differentiation of that identity gives

$$
\langle Nx,y\rangle+\langle x,Ny\rangle=0,
\tag{16.10}
$$

with twists placed as in (16.7). Thus monodromy is skew-adjoint for Poincare duality.

Integrally, $T-1$ is defined on the derived $\mathbf Z_\ell$ complex, but the logarithm and division by factorials in (16.8) are naturally rational. An integral monodromy filtration or splitting requires extra hypotheses. Torsion must remain in $R\Gamma(Y,R\Psi\mathbf Z_\ell)$ rather than be forced into a rational $N$-module.

### 16.4 Correspondences on nearby cycles

Suppose a finite correspondence span on the generic fiber extends to finite flat lci maps of semistable models, with the oriented pull--push degree zero, and suppose the maps meet every ordered semistable stratum transversely. Pullback and trace are then natural transformations of nearby cycles, so its action on (16.3) commutes with inertia, Frobenius, cup product, and duality. If transversality fails, the same conclusion is asserted here only when a proper cohomological correspondence on the model is separately supplied and every relevant square satisfies the clean regular-excess hypotheses (8.14)--(8.15), with its Euler class and every vertical component included. Proper finite extensions of the two legs alone do not supply this datum. If a stratum intersection is singular, its excess quotient is not locally free, or its vertical part is unknown, no action on the stratum spectral sequence is claimed.

Let $e$ be a polynomial projector in such extending span operators. Applying $e$ term by term to (16.5) gives a spectral sequence converging to the projected generic cohomology. Moreover,

$$
eN=Ne,
\qquad
N^3=0\ \text{on}\ eH^2.
\tag{16.11}
$$

The adjoint projector acts on the dual spectral sequence, and (12.11) remains compatible with monodromy.

If the span data are defined over $K$ but semistability is achieved only after a finite extension, replace it by a finite Galois extension $K'/K$. The nearby-cycle complex over $K'$ carries descent data from $\operatorname{Gal}(K'/K)$. Because the original maps and orientations are defined over $K$, their action commutes with that descent data. Taking descent recovers the original $G_K$-representation and its finite inertial part. One must not discard this finite descent datum after recording $N$.

### 16.5 The semistable interface

The output of semistable specialization is the Weil--Deligne package

$$
\bigl(eH_{\mathrm{ét}}^2(X_{\bar K},L_\lambda),
\rho_{\mathrm{fin}},N,F\bigr),
\tag{16.12}
$$

or equivalently the projected nearby-cycle complex with descent data. When the residue field is finite of cardinality $q$, Frobenius and $N$ satisfy

$$
FNF^{-1}=q^{-1}N
\tag{16.13}
$$

for geometric Frobenius and the twist convention of Section 1.1. Traces of $F$ on the total nearby complex obey the Lefschetz--Verdier trace formula; when $e$ annihilates every other étale degree, they are the traces on the projected surface summand.

In the smooth case, $\Lambda_Y\to R\Psi\Lambda$ is an isomorphism, $N=0$, and (16.3) reduces to Chapter 15. Thus good and semistable specialization are two branches of one nearby-cycle formalism, but only the good branch is ordinary special-fiber cohomology.

## 17. The surface comparison theorem

We collect the entire package in one theorem and then state an abstract projector corollary. The result is upstream: it assumes no particular moduli surface, coefficient field, or spectral isolation theorem.

### 17.1 Complete statement

**Theorem 17.1 (functorial comparison package for smooth proper surfaces).** Let $K$ be a characteristic-zero field with an embedding $\sigma:K\hookrightarrow\mathbf C$. Let $X$, $Y$, and $Z$ be smooth proper geometrically connected surfaces over $K$. Fix an algebraic closure $\bar K\hookrightarrow\mathbf C$ extending $\sigma$. For scalar projectors, let $L$ be a number field and let $\lambda\mid\ell$ be a finite place; the adjoint $e^\dagger$ uses the identity coefficient involution unless a nontrivial involution preserving $L_\lambda$ has explicitly been fixed.

The following assertions hold.

1. **Coherent GAGA.** For every proper complex scheme $T$, analytification is an equivalence on coherent sheaves and
   $H^q(T,\mathcal F)\simeq H^q(T^{\mathrm{an}},\mathcal F^{\mathrm{an}})$.
   It respects tensor operations, morphisms, proper direct images, and bounded coherent complexes. In particular it applies to each surface, every product of surfaces, every graph, and every coherent de Rham complex used below.

2. **Filtered de Rham comparison.** There is a natural multiplicative isomorphism

   $$
   H_{\mathrm{dR}}^n(X/K)\otimes_{K,\sigma}\mathbf C
   \xrightarrow{\sim}H_B^n(X,\mathbf C)
   \tag{17.1}
   $$

   carrying the Hodge filtration to
   $F^p=\bigoplus_{a\ge p}H^{a,n-a}$. In degree two,

   $$
   H_B^2=H^{2,0}\oplus H^{1,1}\oplus H^{0,2}.
   \tag{17.2}
   $$

   The same comparison applies to products and is compatible with Künneth. For a retained regular immersion $i$ of codimension $c\le2$ and for a retained oriented map $f$ of relative dimension $r$---a surface projection with $r=2$, a finite-flat lci trace with $r=0$, or a regular immersion with $r=-c$---the unscaled period conventions are

   $$
   \operatorname{comp}(i_*^{\mathrm{dR}}x)
   =(2\pi i)^{\operatorname{codim}i}i_*^B\operatorname{comp}(x),
   \qquad
   \operatorname{comp}(f_*^{\mathrm{dR}}x)
   =(2\pi i)^{-r}f_*^B\operatorname{comp}(x).
   \tag{17.3}
   $$

3. **Finite and adic Betti--étale comparison.** For every finite abelian group $A$ there is a natural surface comparison quasi-isomorphism, compatible with every coefficient pairing $A\otimes B\to C$; it is multiplicative when the coefficient is a finite commutative ring. In particular, for every prime $\ell$, every $m\ge1$, and every $n$, there are natural multiplicative isomorphisms

   $$
   H_B^n(X,\mathbf Z/\ell^m)
   \xrightarrow{\sim}
   H_{\mathrm{ét}}^n(X_{\bar K},\mathbf Z/\ell^m),
   \tag{17.4}
   $$

   $$
   H_B^n(X,\mathbf Z)\otimes\mathbf Z_\ell
   \xrightarrow{\sim}
   H_{\mathrm{ét}}^n(X_{\bar K},\mathbf Z_\ell),
   \tag{17.5}
   $$

   and their $\mathbf Q_\ell$ rationalizations. The integral assertion includes torsion and arises from a quasi-isomorphism of perfect derived complexes. The finite-level exact sequence is

   $$
   0\to H_B^n(X,\mathbf Z)/\ell^m
   \to H_B^n(X,\mathbf Z/\ell^m)
   \to H_B^{n+1}(X,\mathbf Z)[\ell^m]\to0.
   \tag{17.6}
   $$

   Tate twists are identified using $1\mapsto\exp(2\pi i/\ell^m)$. Over $\mathbf C$ there is no excluded coefficient prime.

4. **Duality and trace.** The complex orientation, algebraic de Rham trace, and étale trace are normalized by a closed point. Thus

   $$
   \int_X\operatorname{comp}(u)
   =(2\pi i)^2\operatorname{Tr}_{\mathrm{dR},X}(u),
   \tag{17.7}
   $$

   and

   $$
   \operatorname{Tr}_{\mathrm{ét},X}:
   H_{\mathrm{ét}}^4(X,\mathbf Z_\ell(2))
   \xrightarrow{\sim}\mathbf Z_\ell.
   \tag{17.8}
   $$

   Rationally the middle pairing has target $\mathbf Q_\ell(-2)$. Integrally, free quotients pair in complementary degrees, while torsion has the shifted perfect linking pairing into $\mathbf Q_\ell/\mathbf Z_\ell$.

5. **Functorial operations.** Pullback, cup and exterior products, derived Künneth, regular Gysin maps of codimension at most two in the surface/product configurations of Chapter 8, surface-product projection trace, oriented finite-flat lci trace, projection formulas, transpose, and adjunction commute with comparison, with exactly the factors in (17.3). Base change is asserted for Tor-independent squares. The only excess case retained is a regular Cartesian square satisfying (8.14)--(8.15), with locally free excess bundle of rank at most two and every component present; its correction is the proved Euler class (8.16). There is no assertion for arbitrary singular supports, arbitrary proper pushforward, or a general refined cycle class.

6. **Oriented finite spans.** Every admissible span

   $$
   T=(X\xleftarrow{a}Z\xrightarrow{b}Y)
   $$

   acts by

   $$
   T_*x=b_*a^*x
   =(p_Y)_*\bigl(p_X^*x\smile\kappa_R(a,b)\bigr).
   \tag{17.9}
   $$

   It commutes exactly with both comparisons, preserves cohomological degree and the Hodge filtration, and is $G_K$-equivariant when the span is defined over $K$. Linear combinations, ordered noncommutative polynomials, and transpose are allowed; ordinary polynomials suffice for commuting operators, and transpose is Poincare adjoint. A fiber-product span represents composition only when its carrier is smooth and the middle square is Tor-independent. A nontransverse model-level composite is asserted only with the clean regular-excess datum of part 5.

7. **Projectors and traces.** If $e$ is a polynomial in admissible span operators whose total Betti action is idempotent, it is idempotent in every realization. If it annihilates $H_B^i$ for $i\ne2$, then it annihilates those degrees everywhere and defines compatible middle summands. The étale summand pairs perfectly with the adjoint summand into $L_\lambda(-2)$, so

   $$
   (eH_{\mathrm{ét}}^2)^\vee
   \simeq e^\dagger H_{\mathrm{ét}}^2(2).
   \tag{17.10}
   $$

   Rational denominators are harmless for vector spaces but obstruct integral splitting at the denominator primes. The Lefschetz number is always the cohomological diagonal contraction (13.2). It is a geometric degree only for a finite transverse fixed locus or under the clean regular-excess hypotheses. If the specialized $e$ annihilates every étale degree other than two and those fixed-locus hypotheses hold for the first $\dim eH^2$ Frobenius powers, the projected traces lie in $L$, are coefficient-prime independent, and determine a coefficient-prime-independent characteristic polynomial.

8. **Families and specialization.** Cup product, trace, and oriented finite-flat span operations exist relatively and commute with smooth proper base change. For a smooth proper model over a henselian discrete valuation ring and $\ell$ different from the residue characteristic, generic and special étale cohomology are isomorphic, with inertia trivial and Frobenius compatible. An extending finite-flat lci span commutes with this isomorphism. For a strictly semistable surface model,

   $$
   R\Gamma(X_{\bar K},\Lambda)
   \simeq R\Gamma(Y_{\bar k},R\Psi\Lambda),
   \tag{17.11}
   $$

   for $\Lambda=\mathbf Z/\ell^m\mathbf Z$, compatibly with duality, inertia, and Frobenius; normalized inverse limit gives the adic statement. An extending oriented span acts on this complex when it is transverse to every ordered stratum; in the nontransverse case an independently supplied clean regular-excess cohomological correspondence including all vertical components is required. On $H^2$, $N^3=0$. If semistability requires a finite extension, the finite descent datum is retained.

Every assertion remains valid for a finite disjoint union of geometrically connected surfaces, with trace the sum over components and admissible spans allowed to route components.

### 17.2 Proof of the assembled theorem

Part 1 is the proper coherent comparison of Chapter 2. Its proof used projective Cech calculation, a projective modification, formal control along the exceptional locus, and noetherian induction; full faithfulness and essential surjectivity then yielded the categorical statement.

For part 2, flat scalar extension, coherent GAGA, and the holomorphic Poincare lemma gave the chain of multiplicative quasi-isomorphisms (4.1)--(4.7). The Kähler identities split harmonic forms by type and proved $E_1$ degeneration. The local integral of $d\log z$ fixed the regular-Gysin factor, while the point class fixed the trace factor. Although the notation began with a surface, the de Rham proof of Chapter 4 works on the products used here. The Hodge conclusion is needed only for the projective surface and its projective products.

Part 3 was not inferred from a curve theorem. A Lefschetz pencil reduced the blowup $\widetilde X$ to constructible cohomology on $\mathbf P^1$ with curve fibers. Comparison on smooth curve fibers stayed within the established curve range; normalization triangles handled nodal fibers, Lemma 6.2 handled constructible sheaves on the base, and the blowup triangle descended the result to $X$. Derived inverse limit of the compatible finite comparisons gave (17.5) without losing torsion.

Part 4 follows from cellular Poincare duality, its linking refinement, and the compatible purity generators. The point normalization removes any unit ambiguity. For parts 5 and 6, regular graph purity and the surface-product trace construct oriented finite trace; their comparison factors cancel in (17.9). The projection formula proves kernel--span agreement and transpose adjunction. Flat or Tor-independent base change proves the smooth fiber-product composition formula. In the sole retained excess case, the local regular-sequence calculation splits the pulled-back Koszul complex and produces the Euler class. Nothing in this proof assigns a class to an arbitrary singular support.

For part 7, an intertwining isomorphism carries kernels, images, and polynomial identities of operators. Faithful scalar extension descends idempotence and vanishing. Ambient Poincare duality and the transpose identity give (17.10). Künneth contracts a kernel along the diagonal to its graded trace. The transverse regular-sequence calculation, or the explicit clean-excess calculation, identifies that scalar with the stated geometric degree. After étale degree isolation, Newton identities recover the characteristic polynomial from the coefficient-independent projected power traces.

Finally, the stalk proof of smooth proper base change, followed by the normalized adic limit, proves the good-specialization statement. In the semistable case the local Kummer calculation (16.4) constructs nearby cycles and the restriction--Gysin spectral sequence. Only component surfaces, double curves, and triple points occur, so monodromy can cross at most three levels and $N^3=0$. Naturality of nearby cycles for oriented finite pullback and trace carries exactly the extending transverse spans, and the separately supplied clean-excess correspondences, through the construction. This proves part 8 and the theorem. $\square$

### 17.3 Abstract projector and specialization corollary

Let $X/K$ be a smooth proper surface, let $L$ be a number field, and let $T_1,\ldots,T_s$ be admissible endospans defined over $K$. Suppose

$$
e=P(T_1,\ldots,T_s),
\qquad P\in L\langle t_1,\ldots,t_s\rangle,
\tag{17.12}
$$

where an ordinary polynomial may be used if the $T_i$ commute. Suppose this operator has idempotent total Betti action and satisfies

$$
eH_B^i(X,\mathbf C)=0
\qquad(i\ne2).
\tag{17.13}
$$

Then comparison produces the three compatible middle summands

$$
V_B=eH_B^2(X,L),
\qquad
V_{\mathrm{dR}}=eH_{\mathrm{dR}}^2(X,L),
\qquad
V_\lambda=eH_{\mathrm{ét}}^2(X_{\bar K},L_\lambda).
\tag{17.14}
$$

Their ranks agree. The first is a Hodge substructure, the second is filtered, and the third is a continuous $G_K$-representation. With $e^\dagger$ formed as in Section 11.4, using the identity coefficient involution unless a nontrivial involution preserving $L_\lambda$ has been fixed,

$$
V_\lambda^\vee\simeq V_\lambda^\dagger(2).
\tag{17.15}
$$

Suppose $X$ and every span occurring in (17.12) extend to a smooth proper relative surface and finite flat lci span over a henselian discrete valuation ring with residue field $k$ of characteristic $p$. For $\lambda\mid\ell$, $\ell\ne p$, specialization gives

$$
V_\lambda\xrightarrow{\sim}
e_sH_{\mathrm{ét}}^2(X_{\bar k},L_\lambda),
\tag{17.16}
$$

so $V_\lambda$ is unramified. If $k=\mathbf F_q$, its geometric-Frobenius eigenvalues have absolute value $q$. The specialization also transports (17.13) to étale degree isolation. If, in addition, the transverse or clean regular-excess fixed-locus hypotheses of Section 13.3 hold for $1\le m\le\dim V_\lambda$, then

$$
\operatorname{Tr}(F^m\mid V_\lambda)=I_m(e_s),
\tag{17.17}
$$

and the resulting Frobenius polynomial lies in $L[t]$ and is independent of $\lambda$.

Suppose instead that a strictly semistable model is obtained after a finite extension, fix $\lambda\mid\ell$ with $\ell$ different from the residue characteristic, and assume that each span extends transversely to every ordered stratum or is accompanied by the complete clean regular-excess and vertical-component datum of Section 16.4. Then $e$ acts on the nearby-cycle complex, commutes with finite descent and monodromy, and

$$
eN=Ne,
\qquad
N^3=0\quad\text{on }V_\lambda.
\tag{17.18}
$$

When the residue field is finite of cardinality $q$, it also commutes with Frobenius and $FNF^{-1}=q^{-1}N$.

Finally, if $N_e$ clears the coefficients of the chosen polynomial (17.12), let $\Lambda_\lambda$ be the torsion-free integral cohomology lattice of Section 12.4 after extension to $\mathcal O_{L_\lambda}$. At $\lambda\nmid N_e$ it splits:

$$
\Lambda_\lambda=e\Lambda_\lambda\oplus(1-e)\Lambda_\lambda.
\tag{17.19}
$$

No integral splitting is asserted at $\lambda\mid N_e$. This corollary is entirely abstract: any downstream application must separately construct the spans, prove (17.13), and verify the good or semistable extension hypotheses.

### 17.4 Dependency and failure ledger

The logical dependency row for this book is:

| Book | Established inputs used | Output supplied |
|---|---|---|
| 198 | Books 8--11, 15, 18, 21--26; Book 27 only for the actual curves occurring in the Lefschetz-pencil argument | Functorial coherent, de Rham--Betti, and Betti--étale comparison for smooth proper surfaces, including projectors, traces, duality, and good/semistable specialization |

The uses are direct and upstream. Books 8--11 supply projective embeddings, curve divisor and trace calculations, normalization, blowups, and the regular arithmetic-surface intersection facts used by the pencil and model arguments. Books 15 and 18 supply coherent base change, formal control, and proper GAGA. Books 21--23 supply derived adic cohomology, proper/smooth base change, low-dimensional purity, oriented trace, and duality. Books 24--26 supply nearby cycles, trace formulas, and surface weights. Book 27 is invoked only on the smooth open and proper curves, and their finite covers, that occur in the Lefschetz pencil; it supplies no surface comparison theorem.

The most important hypothesis boundaries are recorded here.

| Claim | Required hypothesis | What fails without it |
|---|---|---|
| coherent algebraic and analytic categories agree | properness over $\mathbf C$ | holomorphic functions and bundles need not algebraize |
| Hodge decomposition used here | smooth projective complex fiber | a general compact complex manifold need not be Kähler |
| finite Betti--étale comparison for every $\ell$ | base field $\mathbf C$ | in positive characteristic the residue prime is not invertible |
| integral adic comparison | normalized derived tower | naive inverse limit can introduce or lose $\varprojlim^1$ data |
| raw complementary-degree perfectness | torsion-free cohomology | torsion instead pairs one degree later |
| exact de Rham span compatibility | graph-Gysin and surface-projection period factors both retained | a spurious $(2\pi i)^2$ remains |
| Galois-stable projected summand | every generating span defined over the ground field | conjugation can move the projector |
| integral direct summand | integral idempotent at $\lambda$ | a rational projector can miss the lattice |
| geometric composition of spans | smooth carrier and Tor-independent middle square | the fiber product can be singular and need not represent operator composition |
| clean excess correction | regular square, locally free excess bundle of rank at most two, all components present | an Euler class cannot be inserted formally |
| realization-level proper-direct-image comparison | Lefschetz-pencil map, surface-product projection, or oriented finite-flat lci trace proved here; coherent proper direct image is the separate GAGA statement of Chapter 2 | a general topological/étale proper-map slogan exceeds the proof |
| good specialization | smooth proper model and $\ell\ne p$ | inertia or $p$-adic phenomena intervene |
| ordinary special-fiber description | local acyclicity | semistable vanishing cycles are lost |
| $N^3=0$ | relative dimension two and semistability | higher-dimensional strata allow longer monodromy |
| coefficient-independent projected Frobenius polynomial | étale degree isolation plus the transverse or clean-excess fixed-locus hypotheses for enough powers | total Lefschetz traces do not isolate degree two, and general local terms need not be algebraic degrees |

### 17.5 Conclusion

For a smooth proper algebraic surface, the three cohomologies are not interchangeable copies of one vector space. Betti cohomology remembers an integral topology and its torsion, de Rham cohomology remembers a filtration and periods, and étale cohomology remembers Galois action and Tate twists. The comparison theorem succeeds by preserving those differences while proving that the regular-Gysin, product-trace, and oriented finite-span operations in its stated scope are the same operations in all three realizations.

The decisive surface calculation occurs twice. A codimension-two kernel contributes $(2\pi i)^2$ and a projection from a product of surfaces contributes its inverse, so correspondence actions compare without a scalar. In degeneration, components, double curves, and triple points give exactly three monodromy levels, so $N^3=0$. Between these two calculations lie the structures needed in arithmetic applications: integral torsion, normalized trace, Künneth kernels, adjoints, rational projector denominators, smooth specialization, and nearby cycles.

Consequently any idempotent polynomial in admissible spans that is recognized on total complex cohomology travels intact to filtered de Rham cohomology and to every $\ell$-adic realization. If it acts only in degree two, its arithmetic image is the honest surface $H^2$ summand, paired into the twist $(-2)$. At a verified good model it is pure and unramified; at a verified semistable model it retains finite descent and the full monodromy operator with $N^3=0$. These conclusions are precisely as strong as the geometric extension, transversality, excess, and degree-isolation hypotheses that make the projector act.
