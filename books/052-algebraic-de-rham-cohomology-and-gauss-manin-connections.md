# Algebraic de Rham Cohomology and Gauss--Manin Connections

## Contents

1. [Differentiating algebraic families](#1-differentiating-algebraic-families)
   - [The three questions](#11-the-three-questions)
   - [Standing conventions](#12-standing-conventions)
   - [What smoothness contributes](#13-what-smoothness-contributes)
2. [Differential forms and the de Rham complex](#2-differential-forms-and-the-de-rham-complex)
   - [Universal first derivatives](#21-universal-first-derivatives)
   - [Higher forms and signs](#22-higher-forms-and-signs)
   - [Relative and absolute differentials](#23-relative-and-absolute-differentials)
   - [Functoriality](#24-functoriality)
3. [Algebraic de Rham cohomology](#3-algebraic-de-rham-cohomology)
   - [Why hypercohomology is necessary](#31-why-hypercohomology-is-necessary)
   - [Definitions and affine computation](#32-definitions-and-affine-computation)
   - [The two hypercohomology spectral sequences](#33-the-two-hypercohomology-spectral-sequences)
   - [Products and graded commutativity](#34-products-and-graded-commutativity)
4. [First computations and characteristic boundaries](#4-first-computations-and-characteristic-boundaries)
   - [Affine space and the algebraic Poincare lemma](#41-affine-space-and-the-algebraic-poincare-lemma)
   - [The punctured line](#42-the-punctured-line)
   - [Projective space](#43-projective-space)
   - [Why characteristic matters](#44-why-characteristic-matters)
5. [The Hodge filtration](#5-the-hodge-filtration)
   - [Filtration by form degree](#51-filtration-by-form-degree)
   - [The Hodge-to-de Rham spectral sequence](#52-the-hodge-to-de-rham-spectral-sequence)
   - [Degeneration versus splitting](#53-degeneration-versus-splitting)
   - [Chern classes from logarithmic differentials](#54-chern-classes-from-logarithmic-differentials)
6. [Smooth proper curves](#6-smooth-proper-curves)
   - [The two-term relative complex](#61-the-two-term-relative-complex)
   - [Degeneration in every characteristic](#62-degeneration-in-every-characteristic)
   - [The Hodge exact sequence](#63-the-hodge-exact-sequence)
   - [Finiteness and arbitrary base change](#64-finiteness-and-arbitrary-base-change)
7. [Cup products and duality on curves](#7-cup-products-and-duality-on-curves)
   - [The de Rham trace](#71-the-de-rham-trace)
   - [The perfect pairing in degree one](#72-the-perfect-pairing-in-degree-one)
   - [The Hodge bundle is Lagrangian](#73-the-hodge-bundle-is-lagrangian)
   - [Maps of curves and adjointness](#74-maps-of-curves-and-adjointness)
8. [Connections as algebraic differentiation](#8-connections-as-algebraic-differentiation)
   - [Connections and horizontal sections](#81-connections-and-horizontal-sections)
   - [Curvature and integrability](#82-curvature-and-integrability)
   - [Tensor operations and de Rham complexes with coefficients](#83-tensor-operations-and-de-rham-complexes-with-coefficients)
   - [Change of base](#84-change-of-base)
9. [Constructing the Gauss--Manin connection](#9-constructing-the-gauss--manin-connection)
   - [Filtering the absolute de Rham complex](#91-filtering-the-absolute-de-rham-complex)
   - [The connection and its Leibniz rule](#92-the-connection-and-its-leibniz-rule)
   - [Integrability, functoriality, and products](#93-integrability-functoriality-and-products)
   - [Base change](#94-base-change)
10. [Transversality and variation of Hodge structure](#10-transversality-and-variation-of-hodge-structure)
    - [Griffiths transversality](#101-griffiths-transversality)
    - [The Kodaira--Spencer class](#102-the-kodaira--spencer-class)
    - [The Higgs map for a family of curves](#103-the-higgs-map-for-a-family-of-curves)
    - [Duality and the second fundamental form](#104-duality-and-the-second-fundamental-form)
11. [De Rham cohomology of abelian schemes](#11-de-rham-cohomology-of-abelian-schemes)
    - [Invariant forms and the first Hodge sequence](#111-invariant-forms-and-the-first-hodge-sequence)
    - [The exterior algebra theorem](#112-the-exterior-algebra-theorem)
    - [Gauss--Manin and the group law](#113-gauss--manin-and-the-group-law)
    - [The universal vector extension viewpoint](#114-the-universal-vector-extension-viewpoint)
12. [Dual abelian schemes, polarizations, and isogenies](#12-dual-abelian-schemes-polarizations-and-isogenies)
    - [The Poincare class and de Rham duality](#121-the-poincare-class-and-de-rham-duality)
    - [Polarization forms](#122-polarization-forms)
    - [Horizontality](#123-horizontality)
    - [Isogeny invariance](#124-isogeny-invariance)
13. [An explicit elliptic family](#13-an-explicit-elliptic-family)
    - [The Legendre family and a cohomology basis](#131-the-legendre-family-and-a-cohomology-basis)
    - [Reduction of differentials](#132-reduction-of-differentials)
    - [The connection matrix](#133-the-connection-matrix)
    - [The Picard--Fuchs equation](#134-the-picard--fuchs-equation)
14. [The de Rham package for later arithmetic geometry](#14-the-de-rham-package-for-later-arithmetic-geometry)
    - [A reusable theorem package](#141-a-reusable-theorem-package)
    - [Failure modes and hypothesis checks](#142-failure-modes-and-hypothesis-checks)
    - [Conclusion](#143-conclusion)

## 1. Differentiating algebraic families

Algebraic geometry can record variation without using analytic paths. A function varies through
its universal differential, a line bundle varies through its infinitesimal transition functions,
and a cohomology class in a smooth family varies through the Gauss--Manin connection. The aim of
this book is to build that chain from the ground up and to show that it is compatible with the
structures already available on curves and abelian schemes.

### 1.1 The three questions

Three questions organize the theory. First, given a smooth scheme $X$ over a base $S$, what
cohomology theory is obtained by placing functions, one-forms, and higher forms in one complex?
The answer is relative algebraic de Rham cohomology

$$
H^n_{\mathrm{dR}}(X/S)=
\mathbb H^n(X,\Omega^\bullet_{X/S}).
$$

Second, when $f:X\to S$ is proper and smooth, when do these groups form vector bundles on $S$ and
commute with changing the base? Proper coherent cohomology and the Hodge-to-de Rham spectral
sequence answer this question. For curves the answer is especially complete: the spectral
sequence degenerates for elementary reasons in every characteristic, producing a short exact
Hodge sequence.

Third, if $S$ itself varies over $T$, how does a relative class change along $S/T$? The absolute
complex $\Omega^\bullet_{X/T}$ contains forms pulled back from $S$. Filtering by the number of such
base differentials produces a first differential

$$
\nabla:H^n_{\mathrm{dR}}(X/S)
\longrightarrow
\Omega^1_{S/T}\otimes H^n_{\mathrm{dR}}(X/S).
$$

This is the Gauss--Manin connection. Its Leibniz rule, zero curvature, compatibility with products,
and transversality to the Hodge filtration all come from the single filtered complex that creates
it.

### 1.2 Standing conventions

All complexes are cohomological. For a morphism $f:X\to S$, $\Omega^p_{X/S}$ denotes the $p$th
exterior power of the sheaf of Kahler differentials. The relative de Rham complex begins in degree
zero:

$$
\Omega^\bullet_{X/S}=
[\mathcal O_X\xrightarrow d\Omega^1_{X/S}\xrightarrow d
\Omega^2_{X/S}\to\cdots].
$$

If $f$ is smooth of relative dimension $d$, each $\Omega^p_{X/S}$ is finite locally free and
vanishes for $p>d$. A **smooth proper curve** over $S$ means a smooth, proper, finitely presented
morphism of pure relative dimension one with geometrically connected fibers. An abelian scheme has
the meaning fixed in Book 38: it is a smooth proper finitely presented group scheme with connected
geometric fibers.

Most relative finiteness statements are made over a locally noetherian base. The connection is
constructed for a tower

$$
X\xrightarrow f S\xrightarrow g T
$$

in which $f$ is smooth and proper and $g$ is smooth, unless a weaker exactness assumption is
explicitly stated. Smoothness of $g$ ensures that base differentials are locally free and that the
cotangent sequence used in the construction is exact on the left. A field is never silently
assumed algebraically closed or perfect.

Books 9 and 15 supply relative duality and coherent base change for curves. Book 16 supplies
hypercohomology, filtered complexes, products, and convergence. Book 38 supplies dual abelian
schemes, the Poincare bundle, polarizations, and isogenies. We recall each interface when it enters
and prove the specifically de Rham assertions here.

### 1.3 What smoothness contributes

Smoothness is not decorative. It says that infinitesimal directions are represented by a vector
bundle $\Omega^1_{X/S}$, that exterior powers have the expected ranks, and that the de Rham complex
has length bounded by the relative dimension. It also gives the exact cotangent sequence for a
smooth tower:

$$
0\longrightarrow f^*\Omega^1_{S/T}
\longrightarrow\Omega^1_{X/T}
\longrightarrow\Omega^1_{X/S}\longrightarrow0. \tag{1.1}
$$

If $X/S$ is singular, $\Omega^1_{X/S}$ can have torsion and need not be the dualizing sheaf. Book 9
explained this at a node. The complex of ordinary differentials on a singular fiber is therefore
not a flat replacement for the smooth de Rham theory. Logarithmic, derived, or crystalline
constructions repair different aspects of that failure, but none is to be confused with the
smooth theory developed here.

Properness has a different role. It makes the coherent cohomology of every $\Omega^p$ finite over
the base. Smoothness without properness still defines de Rham cohomology, but its dimensions and
behavior in families can be much less controlled. The punctured affine line will be a useful
example: it has a genuine degree-one de Rham class, but no proper trace pairing.

## 2. Differential forms and the de Rham complex

The de Rham complex is forced by two demands: differentiation must satisfy the product rule, and a
second derivative must vanish. This chapter constructs the objects carrying those demands and
fixes the sign conventions needed later for products and connections.

### 2.1 Universal first derivatives

For a ring map $R\to A$, an $R$-derivation from $A$ to an $A$-module $M$ is an additive map
$D:A\to M$ satisfying

$$
D(ab)=aD(b)+bD(a),\qquad D(r)=0\quad(r\in R).
$$

There is an $A$-module $\Omega^1_{A/R}$ and a universal derivation $d:A\to\Omega^1_{A/R}$ such that

$$
\operatorname{Hom}_A(\Omega^1_{A/R},M)
\simeq\operatorname{Der}_R(A,M). \tag{2.1}
$$

One construction takes the free $A$-module on symbols $da$ and divides by the displayed relations.
Equivalently, if $I$ is the kernel of multiplication $A\otimes_RA\to A$, then

$$
\Omega^1_{A/R}\simeq I/I^2,
\qquad da=(1\otimes a-a\otimes1)\bmod I^2. \tag{2.2}
$$

The second description explains why differentials measure the first infinitesimal neighborhood of
the diagonal.

For $A=R[x_1,\ldots,x_m]$, the module is free on $dx_1,\ldots,dx_m$. If
$A=R[x_1,\ldots,x_m]/(F_1,\ldots,F_r)$, the conormal sequence gives

$$
(F_1,\ldots,F_r)/(F_1,\ldots,F_r)^2
\longrightarrow\bigoplus_iA\,dx_i
\longrightarrow\Omega^1_{A/R}\longrightarrow0,
$$

and the first arrow sends $F_j$ to $dF_j=\sum_i(\partial F_j/\partial x_i)dx_i$. These affine
constructions localize and glue to $\Omega^1_{X/S}$.

### 2.2 Higher forms and signs

Set $\Omega^p_{A/R}=\bigwedge_A^p\Omega^1_{A/R}$. There is a unique sequence of additive maps

$$
d:\Omega^p_{A/R}\longrightarrow\Omega^{p+1}_{A/R}
$$

extending the universal derivation and satisfying

$$
d(\alpha\wedge\beta)=d\alpha\wedge\beta
+(-1)^p\alpha\wedge d\beta,
\qquad \alpha\in\Omega^p. \tag{2.3}
$$

On a pure expression it is

$$
d(a_0\,da_1\wedge\cdots\wedge da_p)
=da_0\wedge da_1\wedge\cdots\wedge da_p. \tag{2.4}
$$

Formula (2.4) respects the relations defining exterior powers and immediately gives $d^2=0$.
Thus $\Omega^\bullet_{A/R}$ is a differential graded algebra. Its multiplication is graded
commutative:

$$
\alpha\wedge\beta=(-1)^{pq}\beta\wedge\alpha.
$$

The sheaf version gives $\Omega^\bullet_{X/S}$. On a smooth relative $d$-fold it ends at
$\Omega^d_{X/S}$. For a curve, it is only

$$
[\mathcal O_X\xrightarrow d\Omega^1_{X/S}]. \tag{2.5}
$$

The brevity of (2.5), combined with the fact that coherent cohomology on a proper curve occupies
degrees zero and one, is the source of the complete calculations in Chapters 6 and 7.

### 2.3 Relative and absolute differentials

For ring maps $T\to R\to A$, universality gives a right-exact sequence

$$
A\otimes_R\Omega^1_{R/T}\longrightarrow
\Omega^1_{A/T}\longrightarrow\Omega^1_{A/R}\longrightarrow0. \tag{2.6}
$$

If $R/T$ is smooth and $A$ is flat over $R$, the first arrow is injective locally in the smooth
situation relevant here. Sheafifying gives (1.1). It says that an absolute differential consists
of a base component and a relative component, although there is generally no canonical splitting.
Choosing a splitting would amount to choosing a horizontal distribution; the Gauss--Manin
connection will be canonical precisely because it is extracted without choosing one.

Wedge powers of (1.1) carry a filtration. If $F^a\Omega^n_{X/T}$ is the image of

$$
f^*\Omega^a_{S/T}\otimes\Omega^{n-a}_{X/T}
\longrightarrow\Omega^n_{X/T},
$$

then

$$
\operatorname{gr}^a_F\Omega^n_{X/T}
\simeq f^*\Omega^a_{S/T}\otimes\Omega^{n-a}_{X/S}. \tag{2.7}
$$

The absolute differential carries $F^a$ into $F^a$, so this is a filtration by subcomplexes. The
part of $d$ that raises $a$ by one will become differentiation on the base.

### 2.4 Functoriality

For a commutative square

$$
\begin{array}{ccc}
X'&\xrightarrow u&X\\
\downarrow&&\downarrow\\
S'&\xrightarrow v&S,
\end{array}
$$

there is a natural pullback map

$$
u^*\Omega^1_{X/S}\longrightarrow\Omega^1_{X'/S'}.
$$

It extends multiplicatively to a morphism of de Rham complexes. If the square is cartesian and
$S'\to S$ is arbitrary while $X/S$ is smooth, then

$$
u^*\Omega^p_{X/S}\xrightarrow{\sim}\Omega^p_{X'/S'} \tag{2.8}
$$

because differentials of a finitely presented smooth algebra commute with base change and exterior
powers commute with pullback of finite locally free modules.

Contravariance is important. A map $u:X'\to X$ produces

$$
u^*:H^n_{\mathrm{dR}}(X/S)\longrightarrow
H^n_{\mathrm{dR}}(X'/S)
$$

when both schemes lie over the same base. Composition and identities follow already on forms. If
$u$ varies in a family over $S/T$, the same construction will be horizontal for the Gauss--Manin
connections because it respects the filtration (2.7).

## 3. Algebraic de Rham cohomology

Taking only global closed forms misses gluing classes, while taking coherent cohomology term by
term misses the differential joining the terms. Hypercohomology retains both. This chapter makes
that assertion concrete and imports only the derived machinery established in Book 16.

### 3.1 Why hypercohomology is necessary

On an affine scheme, quasi-coherent sheaves have no higher cohomology, so the cohomology of global
forms is enough. On a proper curve, however, $H^1(X,\mathcal O_X)$ is usually nonzero. A degree-one
de Rham class may therefore arise either from a global one-form or from functions that glue only
up to differentials. A construction that remembers just one source cannot be correct.

The appropriate total object is derived global sections:

$$
R\Gamma(X,\Omega^\bullet_{X/S}).
$$

Locally on an affine base $S=\operatorname{Spec}R$, it is a complex of $R$-modules. Its cohomology
simultaneously accounts for the sheaf differential and for the Cech or derived differential that
measures gluing.

### 3.2 Definitions and affine computation

For an $S$-scheme $X$, define

$$
R\Gamma_{\mathrm{dR}}(X/S)=R\Gamma(X,\Omega^\bullet_{X/S}),
\qquad
H^n_{\mathrm{dR}}(X/S)=H^nR\Gamma_{\mathrm{dR}}(X/S). \tag{3.1}
$$

For a morphism $f:X\to S$, the relative derived de Rham pushforward is

$$
Rf_*\Omega^\bullet_{X/S},
$$

and its cohomology sheaves are denoted

$$
\mathcal H^n_{\mathrm{dR}}(X/S)
=R^nf_*\Omega^\bullet_{X/S}. \tag{3.2}
$$

The notation in (3.2) means hypercohomology sheaves, not $R^nf_*$ applied to one sheaf.

If $X=\operatorname{Spec}A$ and $S=\operatorname{Spec}R$, every $\Omega^p_{A/R}$ is quasi-coherent
and affine-acyclic. Hence

$$
H^n_{\mathrm{dR}}(X/S)
\simeq H^n(\Omega^\bullet_{A/R}). \tag{3.3}
$$

This follows from the termwise hypercohomology spectral sequence, which has only its zeroth
coherent-cohomology row. Formula (3.3) is useful for computations, but it should not be extended to
nonaffine schemes without justification.

### 3.3 The two hypercohomology spectral sequences

There are two complementary ways to approach (3.1). Filtering by the form degree gives

$$
E_1^{p,q}=H^q(X,\Omega^p_{X/S})
\Longrightarrow H^{p+q}_{\mathrm{dR}}(X/S), \tag{3.4}
$$

with $d_1$ induced by exterior differentiation. This is the Hodge-to-de Rham spectral sequence.
It is the main computational tool for proper smooth schemes because each $E_1$ term is coherent
cohomology.

Filtering a resolution through the cohomology sheaves of the de Rham complex gives

$$
E_2^{a,b}=H^a(X,\mathcal H^b(\Omega^\bullet_{X/S}))
\Longrightarrow H^{a+b}_{\mathrm{dR}}(X/S). \tag{3.5}
$$

On the small Zariski site in characteristic zero, local exactness of the de Rham complex is not an
algebraic Zariski Poincare lemma in general, so the sheaves in (3.5) need not collapse to constants.
Sequence (3.4), not an unjustified local-constancy assertion, is the reliable algebraic tool.

For a smooth proper $d$-fold over a noetherian ring, $p$ lies between $0$ and $d$, and coherent
cohomology vanishes in sufficiently high degree. Thus (3.4) is bounded and converges strongly.
Its limiting terms are the graded pieces of a filtration; they are not automatically direct
summands.

### 3.4 Products and graded commutativity

Wedge product is a morphism of complexes

$$
\Omega^\bullet_{X/S}\otimes\Omega^\bullet_{X/S}
\longrightarrow\Omega^\bullet_{X/S}.
$$

After derived global sections it produces cup products

$$
H^m_{\mathrm{dR}}(X/S)\otimes
H^n_{\mathrm{dR}}(X/S)
\longrightarrow H^{m+n}_{\mathrm{dR}}(X/S). \tag{3.6}
$$

The total sign combines the Cech degree and form degree. If a cochain has bidegree $(p,q)$, its
total degree is $p+q$; interchanging total cochains of degrees $m,n$ contributes $(-1)^{mn}$.
Consequently

$$
x\smile y=(-1)^{mn}y\smile x. \tag{3.7}
$$

The form-degree filtration is multiplicative:

$$
F^aH^m_{\mathrm{dR}}\smile F^bH^n_{\mathrm{dR}}
\subseteq F^{a+b}H^{m+n}_{\mathrm{dR}}. \tag{3.8}
$$

Every page of (3.4) therefore has a compatible product, and each differential is a derivation.
This compatibility will prove that polarization pairings are horizontal and that the cohomology
of an abelian scheme is an exterior algebra.

## 4. First computations and characteristic boundaries

Examples reveal both the strength and the limitations of algebraic differentiation. Affine space
is contractible in characteristic zero, the punctured line detects logarithmic forms, and positive
characteristic shows why one cannot transfer characteristic-zero intuition without checking
division by integers.

### 4.1 Affine space and the algebraic Poincare lemma

Let $R$ be a $\mathbf Q$-algebra and $A=R[x_1,\ldots,x_m]$. Then

$$
H^0(\Omega^\bullet_{A/R})=R,
\qquad H^n(\Omega^\bullet_{A/R})=0\quad(n>0). \tag{4.1}
$$

The proof is a contracting homotopy. Grade a monomial form

$$
x_1^{a_1}\cdots x_m^{a_m}
dx_{i_1}\wedge\cdots\wedge dx_{i_p}
$$

by total polynomial degree plus form degree, say $N=\sum a_i+p$. Let
$E=\sum x_i\partial/\partial x_i$ be the Euler vector field and $\iota_E$ contraction. Cartan's
direct calculation on monomials gives

$$
d\iota_E+\iota_Ed=N. \tag{4.2}
$$

For $N>0$, division by $N$ makes $N^{-1}\iota_E$ a homotopy from the identity to zero. Degree
zero consists exactly of $R$. This proves (4.1).

The same calculation proves homotopy invariance over a $\mathbf Q$-algebra:

$$
H^n_{\mathrm{dR}}(X\times\mathbf A^1/S)
\simeq H^n_{\mathrm{dR}}(X/S) \tag{4.3}
$$

whenever the product complex and hypercohomology comparison are defined with the usual
quasi-compact separated hypotheses. Expand forms polynomially in the affine coordinate and apply
the one-variable homotopy term by term. The need to divide by positive integers is explicit.

### 4.2 The punctured line

Let $k$ have characteristic zero and $A=k[t,t^{-1}]$. The de Rham complex is

$$
A\xrightarrow d A\,dt.
$$

Every Laurent one-form is a sum of $a_nt^n dt$. If $n\ne-1$, then

$$
t^n dt=d\left(\frac{t^{n+1}}{n+1}\right).
$$

The form $dt/t$ is not exact because an algebraic Laurent primitive would require a logarithm.
Therefore

$$
H^0_{\mathrm{dR}}(\mathbf G_m/k)=k,
\qquad H^1_{\mathrm{dR}}(\mathbf G_m/k)=k\,[dt/t], \tag{4.4}
$$

and higher groups vanish. For a split torus $\mathbf G_m^r$, tensoring the one-variable complexes
gives

$$
H^*_{\mathrm{dR}}(\mathbf G_m^r/k)
\simeq\bigwedge_k^*\langle d\log t_1,\ldots,d\log t_r\rangle. \tag{4.5}
$$

The class $d\log t$ is the local model for first Chern classes and for residues. Its existence also
shows why affine does not mean de Rham-acyclic.

### 4.3 Projective space

Let $k$ be any field. The coherent cohomology of differential forms on projective space gives

$$
H^q(\mathbf P^n_k,\Omega^p)=0\quad(p\ne q),
\qquad H^p(\mathbf P^n_k,\Omega^p)\simeq k. \tag{4.6}
$$

For completeness, one proves (4.6) from the Euler sequence

$$
0\to\Omega^1_{\mathbf P^n/k}
\to\mathcal O(-1)^{\oplus(n+1)}
\to\mathcal O\to0
$$

and its exterior powers. The standard cohomology of $\mathcal O(r)$, followed by induction on $p$,
leaves precisely the diagonal class. Since the $E_1$ page of (3.4) is supported on $p=q$, every
differential changes the two indices unequally and must vanish. Hence

$$
H^{2p}_{\mathrm{dR}}(\mathbf P^n_k/k)\simeq k
\quad(0\le p\le n),
\qquad H^{2p+1}_{\mathrm{dR}}=0. \tag{4.7}
$$

The generator in degree two is $c_1(\mathcal O(1))$, and its $p$th power generates degree $2p$.
Thus

$$
H^*_{\mathrm{dR}}(\mathbf P^n/k)
\simeq k[h]/(h^{n+1}),\qquad |h|=2. \tag{4.8}
$$

### 4.4 Why characteristic matters

Let $k$ have characteristic $p>0$. On $\mathbf A^1_k$,

$$
d(t^p)=0.
$$

Thus $t^p$ is a nonconstant element of $H^0(\Omega^\bullet_{k[t]/k})$, and
$t^{p-1}dt$ is not the derivative of a polynomial: the expected primitive $t^p/p$ does not exist.
The affine Poincare lemma (4.1) and homotopy invariance (4.3) fail for the naive de Rham complex in
positive characteristic.

This failure does not invalidate the smooth proper curve results below. Their degeneration proof
uses proper connected functions, residues, and duality rather than polynomial integration. Nor
does it mean that positive-characteristic de Rham cohomology is useless. It remains finite and
geometric in proper smooth families, but it carries phenomena related to Frobenius that are absent
in characteristic zero. A later cohomology theory will retain that Frobenius integrally. Here we
state every characteristic-dependent assertion at the point where it is used.

## 5. The Hodge filtration

The de Rham complex mixes forms of different degrees. The Hodge filtration remembers how far a
class can be represented toward the high-form end of the complex. It is the bridge between
coherent geometry and the flat bundle supplied by Gauss--Manin.

### 5.1 Filtration by form degree

Use the decreasing stupid filtration

$$
(F^p\Omega^\bullet_{X/S})^n=
\begin{cases}
0,&n<p,\\
\Omega^n_{X/S},&n\ge p.
\end{cases} \tag{5.1}
$$

Thus no shift is made: degrees below $p$ are zero and degrees at least $p$ are unchanged. Define

$$
F^pH^n_{\mathrm{dR}}(X/S)
=\operatorname{im}\left(
\mathbb H^n(X,F^p\Omega^\bullet_{X/S})
\to H^n_{\mathrm{dR}}(X/S)\right). \tag{5.2}
$$

It is finite:

$$
H^n_{\mathrm{dR}}=F^0\supseteq F^1\supseteq\cdots
\supseteq F^{d+1}=0
$$

for a smooth relative $d$-fold. Pullback preserves the filtration, and (3.8) makes it
multiplicative.

The associated graded complex is $\Omega^p_{X/S}[-p]$. Applying derived direct image to the
successive filtration triangles produces the spectral sequence (3.4). Thus the Hodge filtration
is not an extra structure placed on cohomology after the fact; it is the abutment filtration of a
specific filtered complex.

### 5.2 The Hodge-to-de Rham spectral sequence

For a smooth proper morphism $f:X\to S$ over a locally noetherian base,

$$
E_1^{p,q}=R^qf_*\Omega^p_{X/S}
\Longrightarrow\mathcal H^{p+q}_{\mathrm{dR}}(X/S). \tag{5.3}
$$

Every $E_1$ term is coherent by proper finiteness. If these sheaves are locally free and commute
with base change, then (5.3) can be checked on geometric fibers. When the spectral sequence
degenerates at $E_1$, there are canonical identifications

$$
\operatorname{gr}^p_F\mathcal H^n_{\mathrm{dR}}(X/S)
\simeq R^{n-p}f_*\Omega^p_{X/S}. \tag{5.4}
$$

Degeneration is a theorem, not part of the definition. For a general smooth proper scheme it
requires an additional argument not supplied by boundedness alone. For curves and abelian schemes
the group or dimension-one geometry supplies the direct proofs given below.

### 5.3 Degeneration versus splitting

Even when (5.3) degenerates, (5.4) determines only successive quotients. It does not canonically
identify

$$
\mathcal H^n_{\mathrm{dR}}
\quad\text{with}\quad
\bigoplus_pR^{n-p}f_*\Omega^p. \tag{5.5}
$$

For a curve, degree one gives an exact sequence

$$
0\to f_*\Omega^1_{X/S}\to
\mathcal H^1_{\mathrm{dR}}(X/S)\to
R^1f_*\mathcal O_X\to0. \tag{5.6}
$$

It may split locally as a sequence of vector bundles, but no splitting is generally compatible
with base change, cup product, and Gauss--Manin. In fact, the failure of the Hodge subbundle to be
horizontal measures genuine variation of the curve.

Over a field, every short exact sequence of vector spaces splits noncanonically. That elementary
fact should not be promoted to a canonical Hodge decomposition. The connection and the
Kodaira--Spencer map remember exactly the extension behavior discarded by such a choice.

### 5.4 Chern classes from logarithmic differentials

Let $L$ be a line bundle on $X$, trivialized on a cover $U_i$ with transition functions
$g_{ij}\in\mathcal O_X^\times(U_{ij})$. The forms

$$
d\log g_{ij}=g_{ij}^{-1}dg_{ij}
$$

form a Cech one-cocycle in $\Omega^1_{X/S}$ because
$d\log(g_{ij}g_{jk})=d\log g_{ij}+d\log g_{jk}$. Its class lies in
$H^1(X,\Omega^1_{X/S})$ and maps to a de Rham class

$$
c_1^{\mathrm{dR}}(L)\in H^2_{\mathrm{dR}}(X/S). \tag{5.7}
$$

Changing trivializations adds a Cech coboundary, so the class is well defined. Tensor product and
pullback give

$$
c_1(L\otimes M)=c_1(L)+c_1(M),
\qquad c_1(u^*L)=u^*c_1(L). \tag{5.8}
$$

It belongs to $F^1$. On projective space it is the class $h$ in (4.8). If a line bundle is pulled
back from the base, its relative first Chern class vanishes because its relative transition
functions have zero differential. This is why polarizations, which are defined up to base
line-bundle ambiguity, still determine unambiguous relative de Rham pairings.

## 6. Smooth proper curves

Curves are the first setting in which the whole relative theory can be proved without a general
degeneration theorem. There are only four possible $E_1$ terms, and duality controls the one
differential that is not visibly zero.

### 6.1 The two-term relative complex

Let $f:C\to S$ be a smooth proper curve. Since $\Omega^p_{C/S}=0$ for $p>1$,

$$
\Omega^\bullet_{C/S}=[\mathcal O_C\xrightarrow d\omega_{C/S}],
\qquad \omega_{C/S}=\Omega^1_{C/S}. \tag{6.1}
$$

The Hodge-to-de Rham page is

$$
\begin{array}{c|cc}
q=1&R^1f_*\mathcal O_C&R^1f_*\omega_{C/S}\\
q=0&f_*\mathcal O_C&f_*\omega_{C/S}\\
\hline
&p=0&p=1.
\end{array} \tag{6.2}
$$

Book 15 proves

$$
f_*\mathcal O_C\simeq\mathcal O_S,
\quad R^1f_*\omega_{C/S}\simeq\mathcal O_S,
\quad f_*\omega_{C/S}\simeq(R^1f_*\mathcal O_C)^\vee. \tag{6.3}
$$

The middle two bundles have rank equal to the genus $g$. Every term commutes with arbitrary base
change. Thus the spectral sequence is a finite spectral sequence of vector bundles whose
differentials may be tested fiberwise.

### 6.2 Degeneration in every characteristic

**Theorem 6.1.** For a smooth proper curve with geometrically connected fibers, the spectral
sequence (5.3) degenerates at $E_1$ over any locally noetherian base and in every characteristic.

**Proof.** There are two possible $d_1$ maps. The first is

$$
f_*\mathcal O_C\xrightarrow d f_*\omega_{C/S}.
$$

By (6.3), a relative global function is pulled back from $S$, so its relative differential is zero.

The second map is

$$
R^1f_*\mathcal O_C\xrightarrow dR^1f_*\omega_{C/S}. \tag{6.4}
$$

It suffices to show that (6.4) vanishes on every geometric fiber. The target on a fiber is
one-dimensional, and the trace is an isomorphism to the ground field. Represent a class in
$H^1(C,\mathcal O_C)$ by a Cech cocycle of functions $g_{ij}$. Its image is represented by
$dg_{ij}$. The trace of this class is computed by residues after passing to principal parts.
Every exact differential has residue zero, so the trace is zero. Since the trace is an
isomorphism, the image is zero. A morphism between finite locally free sheaves that vanishes on
every geometric fiber is zero.

No higher differential is possible: a $d_r$ with $r\ge2$ leaves the two-column range. Hence the
sequence degenerates. $\square$

The proof uses no division by the characteristic. It is therefore unaffected by the failure in
Section 4.4.

### 6.3 The Hodge exact sequence

Degeneration and (6.3) give

$$
\mathcal H^0_{\mathrm{dR}}(C/S)\simeq\mathcal O_S,
\qquad
\mathcal H^2_{\mathrm{dR}}(C/S)\simeq\mathcal O_S, \tag{6.5}
$$

and the canonical exact sequence

$$
0\longrightarrow\mathbb E
\longrightarrow\mathcal H^1_{\mathrm{dR}}(C/S)
\longrightarrow\mathbb E^\vee
\longrightarrow0,
\qquad \mathbb E=f_*\omega_{C/S}. \tag{6.6}
$$

Thus $\mathcal H^1_{\mathrm{dR}}$ has rank $2g$. Its Hodge filtration is

$$
F^0=\mathcal H^1_{\mathrm{dR}},
\qquad F^1=\mathbb E,
\qquad F^2=0. \tag{6.7}
$$

For a genus-zero curve the middle bundle vanishes. For an elliptic curve, (6.6) is an extension of
one line bundle by its dual. For a constant family $C_0\times S$, there is a natural tensor-product
description after choosing the ground field, but a varying family generally has no canonical
splitting.

### 6.4 Finiteness and arbitrary base change

**Theorem 6.2.** Under the hypotheses above, every
$\mathcal H^n_{\mathrm{dR}}(C/S)$ is finite locally free and, for every morphism $S'\to S$,

$$
\mathcal H^n_{\mathrm{dR}}(C/S)\otimes_{\mathcal O_S}\mathcal O_{S'}
\xrightarrow{\sim}
\mathcal H^n_{\mathrm{dR}}(C_{S'}/S'). \tag{6.8}
$$

**Proof.** The four $E_1$ terms in (6.2) are finite locally free and commute with arbitrary base
change by coherent base change and relative duality. The differentials vanish universally by
Theorem 6.1. The finite filtration on each abutment has finite locally free graded pieces. Locally
on $S$, successive short exact sequences of modules with projective quotient split, so the
abutments are finite locally free. Pulling the filtered complex to $S'$ identifies every graded
piece and every zero differential. Induction on the filtration length, using the five lemma on the
successive short exact sequences, proves (6.8). $\square$

The local splitting used in the proof establishes projectivity only. It does not select a
canonical splitting of (6.6).

## 7. Cup products and duality on curves

The Hodge sequence gives the rank of degree-one cohomology. Cup product explains its geometry: it
is a self-dual bundle, and the Hodge subbundle is exactly half-dimensional and isotropic. This is
the de Rham origin of the symplectic structures used in moduli problems.

### 7.1 The de Rham trace

By (6.5), the top de Rham cohomology is identified with $R^1f_*\omega_{C/S}$. Define

$$
\operatorname{Tr}_{\mathrm{dR}}:
\mathcal H^2_{\mathrm{dR}}(C/S)
\xrightarrow{\sim}R^1f_*\omega_{C/S}
\xrightarrow{\operatorname{tr}_f}\mathcal O_S. \tag{7.1}
$$

The second arrow is the relative duality trace of Book 9. It commutes with arbitrary base change.
On a geometric fiber it is the residue trace: a Cech class of differentials is evaluated by the
sum of its local residues.

Combining cup product with (7.1) gives

$$
\langle x,y\rangle_C
=\operatorname{Tr}_{\mathrm{dR}}(x\smile y):
\mathcal H^1_{\mathrm{dR}}\otimes\mathcal H^1_{\mathrm{dR}}
\longrightarrow\mathcal O_S. \tag{7.2}
$$

The pairing is alternating. Away from characteristic two this follows from graded commutativity.
In characteristic two one checks the stronger diagonal assertion on the two-step Cech--de Rham
model: the square of a total degree-one cocycle is the total differential of its product correction,
while the form--form term vanishes because $\Omega^2_{C/S}=0$. Thus $\langle x,x\rangle_C=0$ in
every characteristic.

### 7.2 The perfect pairing in degree one

**Theorem 7.1.** The pairing (7.2) is perfect.

**Proof strategy.** Filter both variables by the Hodge filtration. The product of two elements of
$F^1$ lies in $F^2\mathcal H^2=0$, so the upper-left graded pairing is zero. The quotient
$\mathcal H^1/F^1$ is $R^1f_*\mathcal O_C$, and multiplication gives the cross-pairing

$$
f_*\omega_{C/S}\otimes R^1f_*\mathcal O_C
\longrightarrow R^1f_*\omega_{C/S}
\xrightarrow{\operatorname{tr}}\mathcal O_S. \tag{7.3}
$$

This is exactly the perfect relative Serre-duality pairing of Book 9. The reverse cross-pairing is
its negative, with the total-complex sign.

Choose a local splitting of (6.6) only for the calculation. Relative to
$\mathbb E\oplus\mathbb E^\vee$, the matrix of (7.2) has off-diagonal blocks equal to the duality
isomorphisms. The lower-right block may depend on the splitting, but an alternating change of
splitting does not alter invertibility. The determinant is a unit because the off-diagonal blocks
are perfect. Therefore (7.2) is perfect independently of the chosen splitting. $\square$

### 7.3 The Hodge bundle is Lagrangian

A subbundle $L$ of a rank-$2g$ symplectic bundle is **Lagrangian** if it is isotropic and has rank
$g$. By (6.6), $\mathbb E$ has rank $g$, and by multiplicativity of the Hodge filtration,

$$
\mathbb E\smile\mathbb E\subseteq F^2\mathcal H^2=0.
$$

Hence the Hodge bundle is Lagrangian in $\mathcal H^1_{\mathrm{dR}}$. Perfection identifies the
quotient canonically with its dual:

$$
\mathcal H^1_{\mathrm{dR}}/\mathbb E\simeq\mathbb E^\vee,
$$

recovering (6.6) from the symplectic viewpoint.

This statement is stronger than a rank count. It says that holomorphic relative forms pair to
zero with one another, while every functional on them is represented by a de Rham class. In a
varying family the Lagrangian subbundle moves inside a flat symplectic bundle; the infinitesimal
motion is the Higgs map of Chapter 10.

### 7.4 Maps of curves and adjointness

Let $u:C\to D$ be a finite locally free morphism between smooth proper curves over $S$. Pullback
of forms gives $u^*$ on de Rham cohomology. Relative duality supplies a trace on differentials,
and trace on functions is defined by the finite locally free algebra. Compatibility
$d\,\operatorname{Tr}(a)=\operatorname{Tr}(da)$ makes these maps a morphism of de Rham complexes
and gives

$$
u_*:\mathcal H^n_{\mathrm{dR}}(C/S)
\longrightarrow\mathcal H^n_{\mathrm{dR}}(D/S).
$$

Residue compatibility proves the projection formula

$$
u_*(u^*x\smile y)=x\smile u_*y. \tag{7.4}
$$

Consequently pullback and trace are adjoint for (7.2). If $u$ is finite locally free of degree
$d$, then

$$
u_*u^*=d \tag{7.5}
$$

on de Rham cohomology. The equality is checked on the de Rham complex: trace of multiplication by
a pulled-back section is $d$ times that section, and compatibility with differentials passes it to
hypercohomology. If $d$ is invertible on $S$, pullback is a split injection.

## 8. Connections as algebraic differentiation

A vector bundle does not by itself say how sections at neighboring points should be compared. A
connection supplies the infinitesimal comparison. Its curvature measures whether comparisons
depend on the order of two infinitesimal moves.

### 8.1 Connections and horizontal sections

Let $g:S\to T$ be a morphism and $E$ an $\mathcal O_S$-module. A $T$-connection is an additive map

$$
\nabla:E\longrightarrow\Omega^1_{S/T}\otimes E \tag{8.1}
$$

satisfying the Leibniz rule

$$
\nabla(ae)=da\otimes e+a\nabla(e). \tag{8.2}
$$

A section $e$ is **horizontal** if $\nabla(e)=0$. A morphism
$\varphi:(E,\nabla_E)\to(F,\nabla_F)$ is horizontal if

$$
\nabla_F\varphi=(1\otimes\varphi)\nabla_E.
$$

The structure sheaf has its tautological connection $d:\mathcal O_S\to\Omega^1_{S/T}$. A free
bundle with basis $e_1,\ldots,e_r$ acquires the connection for which the basis is horizontal; after
a change of basis by a matrix $G$, its connection matrix changes to

$$
A' =G^{-1}AG+G^{-1}dG. \tag{8.3}
$$

The inhomogeneous term shows why a connection matrix is not a tensor. The connection itself is
independent of the chosen frame.

### 8.2 Curvature and integrability

Extend $\nabla$ to

$$
\nabla:\Omega^p_{S/T}\otimes E
\longrightarrow\Omega^{p+1}_{S/T}\otimes E
$$

by

$$
\nabla(\alpha\otimes e)=d\alpha\otimes e+(-1)^p\alpha\wedge\nabla(e). \tag{8.4}
$$

The curvature is the $\mathcal O_S$-linear map

$$
R_\nabla=\nabla^2:E\to\Omega^2_{S/T}\otimes E. \tag{8.5}
$$

Linearity follows by expanding $\nabla^2(ae)$ and observing that the two $da\wedge\nabla(e)$ terms
cancel. The connection is **integrable** if $R_\nabla=0$. In a frame with connection matrix $A$,

$$
R_\nabla=dA+A\wedge A. \tag{8.6}
$$

On a one-dimensional smooth base, $\Omega^2_{S/T}=0$, so every connection is automatically
integrable. In higher dimension zero curvature is a real condition.

If $\nabla$ is integrable, (8.4) forms a complex

$$
E\xrightarrow\nabla\Omega^1_{S/T}\otimes E
\xrightarrow\nabla\Omega^2_{S/T}\otimes E\to\cdots, \tag{8.7}
$$

the de Rham complex of $E$ with coefficients in the connection.

### 8.3 Tensor operations and de Rham complexes with coefficients

Connections behave as differentiation should. On a tensor product,

$$
\nabla(e\otimes f)=\nabla_E(e)\otimes f+e\otimes\nabla_F(f). \tag{8.8}
$$

On the dual bundle,

$$
d\langle\lambda,e\rangle
=\langle\nabla_{E^\vee}\lambda,e\rangle
+\langle\lambda,\nabla_Ee\rangle. \tag{8.9}
$$

Exterior and symmetric powers inherit connections by the same Leibniz rule. Curvature is additive
under tensor products, so these constructions preserve integrability.

A pairing $b:E\otimes E\to\mathcal O_S$ is horizontal precisely when

$$
d\,b(x,y)=b(\nabla x,y)+b(x,\nabla y). \tag{8.10}
$$

If $b$ is perfect and horizontal, the induced isomorphism $E\simeq E^\vee$ is horizontal. Thus a
flat symplectic bundle is a vector bundle with an integrable connection and a perfect alternating
horizontal form. The curve bundle of Chapter 7 will have exactly this structure.

### 8.4 Change of base

Given $h:S'\to S$ over $T$, a connection pulls back to

$$
h^*E\longrightarrow\Omega^1_{S'/T}\otimes h^*E
$$

by first pulling (8.1) into $h^*\Omega^1_{S/T}\otimes h^*E$ and then using
$h^*\Omega^1_{S/T}\to\Omega^1_{S'/T}$. The Leibniz rule follows from functoriality of universal
differentials, and curvature pulls back. Hence integrability is preserved.

If instead $S'\to S$ is regarded as a new base direction and one wants a connection relative to
$T'$, the comparison involves the map $\Omega^1_{S/T}\to\Omega^1_{S'/T'}$. We will always display
the base tower so that the direction of differentiation is unambiguous.

## 9. Constructing the Gauss--Manin connection

The Gauss--Manin connection is often introduced by differentiating periods. Algebraically, periods
are unnecessary: the connection is the first differential of the filtration of the absolute de
Rham complex by base forms. This construction proves all structural properties at once.

### 9.1 Filtering the absolute de Rham complex

Let

$$
X\xrightarrow f S\xrightarrow g T
$$

with $f$ smooth proper and $g$ smooth. Filter $\Omega^\bullet_{X/T}$ by the number of factors from
$f^*\Omega^1_{S/T}$ as in (2.7). The associated graded complex is

$$
\operatorname{gr}^a_F\Omega^\bullet_{X/T}
\simeq f^*\Omega^a_{S/T}\otimes
\Omega^{\bullet-a}_{X/S}[-a]. \tag{9.1}
$$

Apply $Rf_*$. If $\Omega^a_{S/T}$ is finite locally free, the projection formula gives

$$
Rf_*\operatorname{gr}^a_F\Omega^\bullet_{X/T}
\simeq\Omega^a_{S/T}\otimes
Rf_*\Omega^\bullet_{X/S}[-a]. \tag{9.2}
$$

The spectral sequence of the filtered object therefore begins with

$$
E_1^{a,n}=\Omega^a_{S/T}\otimes
\mathcal H^n_{\mathrm{dR}}(X/S), \tag{9.3}
$$

where the second index has been arranged to record relative de Rham degree. The differential
$d_1$ raises $a$ by one and preserves $n$.

### 9.2 The connection and its Leibniz rule

Define

$$
\nabla_{\mathrm{GM}}=d_1^{0,n}:
\mathcal H^n_{\mathrm{dR}}(X/S)
\longrightarrow
\Omega^1_{S/T}\otimes\mathcal H^n_{\mathrm{dR}}(X/S). \tag{9.4}
$$

**Theorem 9.1.** If the relative de Rham sheaf in (9.4) is finite locally free and its formation is
compatible with the local base changes used above, then (9.4) is a $T$-connection.

**Proof.** The filtered complex is a module over $\Omega^\bullet_{S/T}$ by pullback and wedge
product. On the associated graded, the absolute differential applied to $f^*a\cdot\alpha$ is

$$
f^*(da)\wedge\alpha+f^*a\,d\alpha.
$$

The first term raises the base-form filtration by one; the second contains the relative
differential and the derivative of $\alpha$. Passing to relative de Rham cohomology yields

$$
d_1(a[\alpha])=da\otimes[\alpha]+a,d_1[\alpha],
$$

which is the Leibniz rule. Independence of representatives follows because $d_1$ is a spectral
sequence differential. $\square$

The construction makes no choice of local coordinates or splitting of (1.1). A splitting can be
used to calculate the connection, but changing it changes representatives by a relative homotopy
and leaves (9.4) unchanged.

### 9.3 Integrability, functoriality, and products

The later $d_1$ maps in (9.3) are precisely the extension (8.4) of $\nabla_{\mathrm{GM}}$ to base
forms. Since $d_1^2=0$, we obtain

$$
\nabla_{\mathrm{GM}}^2=0. \tag{9.5}
$$

Thus the Gauss--Manin connection is integrable.

A map of smooth proper families over $S$ induces a morphism of absolute de Rham complexes that
respects the base-form filtration. The resulting map on relative de Rham cohomology is therefore
horizontal. The same argument applies to trace maps when they are constructed from duality
compatibly with differentials.

Wedge product also respects the filtration, and the spectral differential is a derivation. Hence

$$
\nabla(x\smile y)=\nabla x\smile y+x\smile\nabla y, \tag{9.6}
$$

with the evident placement of the base one-form. In particular, the de Rham trace for a curve is
horizontal: under $\mathcal H^2_{\mathrm{dR}}\simeq\mathcal O_S$, its connection is the ordinary
$d$ on $\mathcal O_S$. Combining this with (9.6) proves that the symplectic pairing (7.2) is
horizontal.

### 9.4 Base change

Consider a cartesian diagram over $T$

$$
\begin{array}{ccc}
X'&\longrightarrow&X\\
\downarrow&&\downarrow\\
S'&\longrightarrow&S.
\end{array}
$$

Assume $S'$ is smooth over $T$ and that relative de Rham cohomology commutes with this base change.
Pullback identifies the relative de Rham complexes by (2.8) and maps the base-form filtration for
$X/T$ to that for $X'/T$. Naturality of spectral sequences gives a horizontal isomorphism

$$
h^*\mathcal H^n_{\mathrm{dR}}(X/S)
\xrightarrow{\sim}\mathcal H^n_{\mathrm{dR}}(X'/S'). \tag{9.7}
$$

For smooth proper curves, the needed base-change hypothesis is Theorem 6.2, so (9.7) holds for
every base change for which the displayed connection directions are defined. For general smooth
proper families, finite local freeness and derived base change must be established before (9.7)
is asserted. Coherence alone is insufficient: torsion in neighboring coherent cohomology can
create new classes after reduction.

## 10. Transversality and variation of Hodge structure

The Hodge filtration is generally not horizontal. Its failure to be horizontal is controlled: one
differentiation can lower form degree by at most one. For curves, the resulting map is the cup
product with the Kodaira--Spencer class and measures the infinitesimal variation of complex
structure in purely algebraic terms.

### 10.1 Griffiths transversality

**Theorem 10.1.** Suppose the Hodge filtration on
$\mathcal H^n_{\mathrm{dR}}(X/S)$ is by subbundles and the relevant Hodge-to-de Rham sequence
degenerates. Then

$$
\nabla_{\mathrm{GM}}(F^p)
\subseteq\Omega^1_{S/T}\otimes F^{p-1}. \tag{10.1}
$$

**Proof.** Represent a class in $F^p$ by relative forms of degree at least $p$. Lift those forms
locally to absolute forms. The absolute differential has a relative part, which preserves the
relative form degree, and a base part, which contributes one base differential while removing at
most one relative differential. Modulo relative boundaries, the connection term therefore has
relative form degree at least $p-1$. This representative calculation is exactly the compatibility
between the base-form filtration of Chapter 9 and the form-degree filtration of Chapter 5. It
descends to (10.1). $\square$

Passing to graded pieces gives the Higgs operators

$$
\theta^{p,q}:R^qf_*\Omega^p_{X/S}
\longrightarrow
\Omega^1_{S/T}\otimes R^{q+1}f_*\Omega^{p-1}_{X/S}. \tag{10.2}
$$

Integrability implies $\theta\wedge\theta=0$ on the associated graded.

### 10.2 The Kodaira--Spencer class

The cotangent sequence (1.1) is an extension of $\Omega^1_{X/S}$ by $f^*\Omega^1_{S/T}$. Its class is

$$
\kappa_{X/S/T}\in
\operatorname{Ext}^1_X(\Omega^1_{X/S},f^*\Omega^1_{S/T}). \tag{10.3}
$$

When $f$ is smooth, $\Omega^1_{X/S}$ is locally free, so

$$
\operatorname{Ext}^1_X(\Omega^1_{X/S},f^*\Omega^1_{S/T})
\simeq H^1(X,T_{X/S}\otimes f^*\Omega^1_{S/T}).
$$

Adjunction yields the Kodaira--Spencer map

$$
\operatorname{KS}:T_{S/T}
\longrightarrow R^1f_*T_{X/S}. \tag{10.4}
$$

To see its deformation meaning, take a tangent vector $v$ on $S$. Pull (1.1) back along the
first-order map defined by $v$. The resulting extension of $\Omega^1$ is the first-order
deformation class of the fiber in direction $v$. If the family is a product, (1.1) splits
canonically by the product decomposition and $\operatorname{KS}=0$. The converse requires an
effectivity and rigidity theorem and is not asserted merely from the vanishing of one class.

### 10.3 The Higgs map for a family of curves

For a smooth proper curve, only one nonzero graded Gauss--Manin map can occur:

$$
\theta:\mathbb E=f_*\omega_{C/S}
\longrightarrow\Omega^1_{S/T}\otimes R^1f_*\mathcal O_C
=\Omega^1_{S/T}\otimes\mathbb E^\vee. \tag{10.5}
$$

**Proposition 10.2.** The map (10.5) is cup product with the Kodaira--Spencer class. More precisely,
for a vector field $v$ and a relative one-form $\omega$,

$$
\theta_v(\omega)=\operatorname{KS}(v)\smile\omega
\in H^1(C,\mathcal O_C). \tag{10.6}
$$

**Proof.** Choose local splittings of (1.1). On overlaps their differences are homomorphisms
$\Omega^1_{C/S}\to f^*\Omega^1_{S/T}$, forming a Cech cocycle representing (10.3). Lift $\omega$
using each splitting and apply the absolute differential. The relative part vanishes because a
one-form on a relative curve is top degree. The differences of the base parts on overlaps are the
chosen cocycle evaluated on $\omega$. Contracting the base one-form with $v$ gives exactly the Cech
cup product in (10.6). $\square$

Thus the motion of the Hodge line or bundle is the infinitesimal deformation of the curve paired
with its differentials.

### 10.4 Duality and the second fundamental form

Because the symplectic pairing is horizontal and $\mathbb E$ is Lagrangian, differentiating
$\langle\omega,\eta\rangle=0$ for $\omega,\eta\in\mathbb E$ gives

$$
\langle\theta(\omega),\eta\rangle
=\langle\theta(\eta),\omega\rangle. \tag{10.7}
$$

Hence the bilinear form

$$
(\omega,\eta)\longmapsto
\langle\theta(\omega),\eta\rangle
\in\Omega^1_{S/T} \tag{10.8}
$$

is symmetric. Equivalently, the second fundamental form of the Hodge Lagrangian lies in

$$
\Omega^1_{S/T}\otimes\operatorname{Sym}^2(\mathbb E^\vee).
$$

For curves this is also visible from (10.6): under Serre duality, the tangent space
$H^1(T_C)$ pairs with quadratic differentials $H^0(\omega_C^{\otimes2})$, and

$$
\langle\theta_v(\omega),\eta\rangle
=\langle\operatorname{KS}(v),\omega\eta\rangle. \tag{10.9}
$$

The product $\omega\eta$ is symmetric, proving (10.7) without choosing a symplectic frame.

## 11. De Rham cohomology of abelian schemes

On an abelian scheme, translation reduces differential forms to their values at the identity, and
the group law turns cohomology into a Hopf algebra. These two facts force the whole de Rham algebra
to be generated in degree one.

### 11.1 Invariant forms and the first Hodge sequence

Let $p:A\to S$ be an abelian scheme of relative dimension $g$, with identity $e$. Set

$$
\omega_A=e^*\Omega^1_{A/S}.
$$

Translation gives the canonical isomorphisms established in Book 15:

$$
\Omega^1_{A/S}\simeq p^*\omega_A,
\qquad
\Omega^a_{A/S}\simeq p^*\bigwedge^a\omega_A. \tag{11.1}
$$

The coherent exterior algebra theorem gives

$$
R^bp_*\mathcal O_A\simeq\bigwedge^bR^1p_*\mathcal O_A. \tag{11.2}
$$

In degree one the Hodge-to-de Rham differentials vanish. The map
$p_*\mathcal O_A\to p_*\Omega^1$ kills constants. For
$R^1p_*\mathcal O_A\to R^1p_*\Omega^1$, use translation and the group law: a coherent
degree-one class is primitive under addition, while exterior differentiation commutes with
addition. Its image would be simultaneously primitive in the cohomological factor and divisible
by a nonzero invariant one-form factor; comparing the two Kunneth components forces it to vanish.
Fiberwise this is an equality of finite-dimensional spaces, and coherent base change makes it
relative. Thus

$$
0\longrightarrow\omega_A
\longrightarrow\mathcal H^1_{\mathrm{dR}}(A/S)
\longrightarrow R^1p_*\mathcal O_A
\longrightarrow0. \tag{11.3}
$$

Book 38 identifies $R^1p_*\mathcal O_A\simeq\omega_{A^\vee}^\vee$, so (11.3) becomes

$$
0\to\omega_A\to\mathcal H^1_{\mathrm{dR}}(A/S)
\to\omega_{A^\vee}^\vee\to0. \tag{11.4}
$$

### 11.2 The exterior algebra theorem

**Theorem 11.1.** For an abelian scheme over a locally noetherian base, the Hodge-to-de Rham
spectral sequence degenerates at $E_1$, every de Rham cohomology sheaf is finite locally free and
commutes with arbitrary base change, and cup product induces

$$
\bigwedge^n\mathcal H^1_{\mathrm{dR}}(A/S)
\xrightarrow{\sim}\mathcal H^n_{\mathrm{dR}}(A/S). \tag{11.5}
$$

In particular, $\mathcal H^n_{\mathrm{dR}}$ has rank $\binom{2g}{n}$.

**Proof strategy and proof.** Addition and the diagonal make
$R p_*\Omega^\bullet_{A/S}$ a commutative Hopf object. The primitive part in degree one is all of
$\mathcal H^1_{\mathrm{dR}}$: on the Hodge graded pieces this follows from (11.1), (11.2), and the
fact that invariant one-forms and $H^1(\mathcal O_A)$ are primitive. Cup product therefore gives
the Hopf morphism (11.5).

We prove it is an isomorphism by filtering both sides. The filtration induced on the left by
(11.3) has graded pieces

$$
\bigwedge^a\omega_A\otimes
\bigwedge^bR^1p_*\mathcal O_A,
\qquad a+b=n. \tag{11.6}
$$

By the projection formula, (11.1), and (11.2), these are exactly

$$
R^bp_*\Omega^a_{A/S}, \tag{11.7}
$$

the terms of total degree $n$ on the Hodge page.

It remains to rule out differentials and extension losses. On the $E_1$ page, (11.6)--(11.7) show
that the algebra is the exterior algebra on the two total-degree-one pieces
$\omega_A$ and $R^1p_*\mathcal O_A$. The differential $d_1$ vanishes on those generators by the
argument preceding (11.3), hence vanishes everywhere by the derivation rule.

Every later page retains the Hopf structure induced by addition. Its differential is both a
derivation and compatible with the coproduct. A primitive degree-one generator can only map to a
primitive element of total degree two. But the exterior Hopf algebra on primitive generators has
no primitive elements in degree two: expanding
$\Delta(x\wedge y)$ produces the nonzero mixed terms
$x\otimes y-y\otimes x$, and a basis expansion shows that no nonzero linear combination cancels
all mixed terms. This calculation remains valid in characteristic two, where the two ordered mixed
terms are still distinct basis tensors. Hence every later differential vanishes on the
degree-one generators and therefore on the algebra they generate. Induction on the page proves
degeneration at $E_1$.

Thus (11.7) are the associated graded pieces of both sides of (11.5), and the induced graded map is
the identity under the coherent exterior-algebra identifications. Finite filtered comparison makes
(11.5) an isomorphism. Since the graded pieces are finite locally free and commute with base
change, the same filtration argument as in Theorem 6.2 proves local freeness and arbitrary base
change for the abutment. $\square$

The proof uses the full group law. A general smooth proper variety need not have de Rham
cohomology generated in degree one.

### 11.3 Gauss--Manin and the group law

Suppose $A\to S\to T$ lies in the smooth tower of Chapter 9. Addition, inversion, the identity,
and multiplication by $n$ are maps of families. Their actions on de Rham cohomology are therefore
horizontal. Since (11.5) is induced by cup product, it is an isomorphism of bundles with
integrable connection:

$$
(\mathcal H^*_{\mathrm{dR}}(A/S),\nabla)
\simeq
\bigwedge^*(\mathcal H^1_{\mathrm{dR}}(A/S),\nabla). \tag{11.8}
$$

Multiplication acts on degree one by $n$. To prove this, check the Hodge graded pieces: pullback by
$[n]$ multiplies invariant one-forms by $n$, and it multiplies
$R^1p_*\mathcal O_A$ by $n$ under the coherent exterior theorem. Filtered comparison gives
$[n]^*=n$ on $\mathcal H^1_{\mathrm{dR}}$, hence

$$
[n]^*=n^r\quad\text{on }\mathcal H^r_{\mathrm{dR}}. \tag{11.9}
$$

No invertibility of $n$ is needed for the equality. If an isogeny has invertible degree on $S$,
trace and pullback show that it induces an isomorphism on de Rham cohomology; Section 12.4 sharpens
the statement in degree one.

### 11.4 The universal vector extension viewpoint

The bundle in (11.4) also has a moduli interpretation. Consider the universal vector extension of
the dual abelian scheme:

$$
0\longrightarrow V(\omega_A)
\longrightarrow E(A^\vee)\longrightarrow A^\vee\longrightarrow0, \tag{11.10}
$$

where our convention is that the vector group $V(M)$ has Lie algebra $M$. Then there is a canonical
identification

$$
\operatorname{Lie}(E(A^\vee)/S)
\simeq\mathcal H^1_{\mathrm{dR}}(A/S). \tag{11.11}
$$

Here is the construction. An $S$-point of $A^\vee$ is a rigidified algebraically trivial line
bundle on $A$. Lifting it to $E(A^\vee)$ amounts to equipping that line bundle with an integrable
relative connection. Two such connections differ by a global invariant one-form on $A$, so the
fiber of $E(A^\vee)\to A^\vee$ is the vector group with Lie algebra $\omega_A$. Infinitesimally,
the tangent sequence of (11.10) is

$$
0\to\omega_A\to\operatorname{Lie}(E(A^\vee)/S)
\to\operatorname{Lie}(A^\vee/S)\to0.
$$

Since $\operatorname{Lie}(A^\vee/S)=R^1p_*\mathcal O_A=\omega_{A^\vee}^\vee$, this has the same
graded terms as (11.4). The Cech description of a line bundle with connection identifies its
extension class with the de Rham extension class, proving (11.11).

This viewpoint explains why $\mathcal H^1_{\mathrm{dR}}$ is the natural linear realization of an
abelian scheme: it simultaneously records invariant differentials on $A$ and infinitesimal line
bundles on $A^\vee$.

## 12. Dual abelian schemes, polarizations, and isogenies

Book 38 constructed the Poincare bundle and used it to pair finite torsion. Its de Rham first Chern
class gives the corresponding pairing of vector bundles. Polarizations turn that duality into a
symplectic form, and functoriality makes the form horizontal.

### 12.1 The Poincare class and de Rham duality

Let $\mathcal P$ be the normalized Poincare bundle on $A\times_SA^\vee$. Its first Chern class lies
in

$$
c_1^{\mathrm{dR}}(\mathcal P)
\in\mathcal H^2_{\mathrm{dR}}(A\times A^\vee/S). \tag{12.1}
$$

The Kunneth decomposition from Theorem 11.1 places the normalized class entirely in

$$
\mathcal H^1_{\mathrm{dR}}(A/S)
\otimes\mathcal H^1_{\mathrm{dR}}(A^\vee/S). \tag{12.2}
$$

Indeed normalization makes its restrictions to $A\times e$ and $e\times A^\vee$ trivial, killing
the degree-two classes from either factor. Put
$V=\mathcal H^1_{\mathrm{dR}}(A/S)$ and
$W=\mathcal H^1_{\mathrm{dR}}(A^\vee/S)$. A tensor in (12.2) is equivalently a map from the dual of
either factor to the other. The Poincare tensor gives

$$
t_{\mathcal P}:V^\vee\longrightarrow W. \tag{12.3}
$$

**Theorem 12.1.** The map (12.3) is an isomorphism. Its inverse identifies $W$ with $V^\vee$ and
therefore gives a perfect evaluation pairing between the degree-one de Rham bundles of $A$ and
$A^\vee$.

**Proof.** On Hodge graded pieces, the biextension interpretation of $\mathcal P$ gives the
evaluation pairings

$$
\omega_A\otimes R^1p^\vee_*\mathcal O_{A^\vee}\to\mathcal O_S,
\qquad
R^1p_*\mathcal O_A\otimes\omega_{A^\vee}\to\mathcal O_S. \tag{12.4}
$$

They are perfect because $R^1p_*\mathcal O_A=\omega_{A^\vee}^\vee$ and its dual counterpart holds
after biduality. Thus the associated graded map of (12.3) is an isomorphism. Finite filtered
comparison proves that (12.3) itself is an isomorphism. $\square$

### 12.2 Polarization forms

Let $\lambda:A\to A^\vee$ be a polarization and retain the notation $V,W$ of Section 12.1.
Contravariance gives

$$
\lambda^*: \mathcal H^1_{\mathrm{dR}}(A^\vee/S)
\longrightarrow V.
$$

After identifying $W$ with $V^\vee$ by $t_{\mathcal P}^{-1}$, this is a map $V^\vee\to V$. If
$\lambda$ is principal, it is an isomorphism; define

$$
\psi_\lambda(x,y)=\bigl((\lambda^*)^{-1}x\bigr)(y):
V\otimes V\longrightarrow\mathcal O_S. \tag{12.5}
$$

The symmetry condition $\lambda^\vee\delta_A=\lambda$ and antisymmetry of the Poincare
biextension imply that (12.5) is alternating. It is perfect by construction. More generally, the
same formula defines a perfect pairing after inverting $\deg\lambda$: a quasi-inverse to the
isogeny shows that $\lambda^*$ becomes invertible there. Before that degree is inverted, it is
safer to retain the integral map $V^\vee\to V$ rather than claim a perfect form.

The Hodge bundle $\omega_A$ is isotropic. On the Hodge graded pairing, it pairs only with the
quotient $R^1p_*\mathcal O_A$, not with itself. Under a principal polarization it is a rank-$g$
Lagrangian subbundle of the rank-$2g$ symplectic de Rham bundle.

For an elliptic scheme, the canonical principal polarization identifies this construction with
the curve pairing of Chapter 7. Both are induced by the diagonal divisor and have the same
restriction to the Hodge graded pieces, so perfection and normalization force equality.

### 12.3 Horizontality

The Poincare bundle is defined over $S$, and its relative first Chern class is horizontal. To see
this directly, represent it by transition functions $g_{ij}$. In the absolute de Rham complex,
$d(d\log g_{ij})=0$; under the base-form filtration this says precisely that the Gauss--Manin
derivative of the relative class vanishes. Thus (12.3) is horizontal.

If $\lambda$ is a homomorphism of abelian schemes over $S$, pullback by $\lambda$ is horizontal by
functoriality. Therefore

$$
d\psi_\lambda(x,y)
=\psi_\lambda(\nabla x,y)+\psi_\lambda(x,\nabla y). \tag{12.6}
$$

A principally polarized abelian scheme consequently determines a flat symplectic bundle with a
Lagrangian Hodge subbundle. Its second fundamental form is symmetric, just as in (10.7). This is
the linear algebra underlying the Hodge conditions in polarized moduli spaces.

### 12.4 Isogeny invariance

Let $u:A\to B$ be an isogeny. Duality of the Poincare bundles gives

$$
\langle u^*x,y\rangle_A
=\langle x,(u^\vee)^*y\rangle_B. \tag{12.7}
$$

The trace map satisfies $u_*u^*=(\deg u)$ on de Rham cohomology. Hence, if $\deg u$ is invertible
on $S$,

$$
u^*: \mathcal H^1_{\mathrm{dR}}(B/S)
\xrightarrow{\sim}\mathcal H^1_{\mathrm{dR}}(A/S) \tag{12.8}
$$

with inverse $(\deg u)^{-1}u_*$. It is horizontal and strictly compatible with the Hodge
filtration because pullback of invariant forms is the cotangent map at the identity and the same
is true on the coherent quotient.

Without invertibility, (12.8) can fail. In characteristic $p$, the differential of a purely
inseparable $p$-isogeny may vanish on invariant forms. The group schemes still have the same
dimension and the isogeny remains finite locally free, but integral de Rham lattices need not be
identified. Thus isogeny invariance must state which degree is inverted.

## 13. An explicit elliptic family

An explicit calculation shows how the abstract connection becomes a differential equation. The
Legendre family is simple enough for reduction by exact differentials and rich enough to have
nonzero Kodaira--Spencer class.

### 13.1 The Legendre family and a cohomology basis

Let

$$
S=\operatorname{Spec}
\mathbf Z\left[\frac12,\lambda,
\frac1{\lambda(1-\lambda)}\right]
$$

and let $E\to S$ be the smooth projective elliptic curve whose affine equation is

$$
y^2=x(x-1)(x-\lambda). \tag{13.1}
$$

The inversions exclude characteristic two and the singular parameters $0,1,\infty$. Put

$$
\omega=\frac{dx}{y},
\qquad \eta=\frac{x\,dx}{y}. \tag{13.2}
$$

The form $\omega$ extends regularly across the point at infinity and generates the Hodge line.
The class of $\eta$ is a differential of the second kind: it may be represented on the affine
chart and has zero residue at infinity. The two classes form a basis of
$\mathcal H^1_{\mathrm{dR}}(E/S)$. Indeed the first lies in $F^1$, while the image of the second in
$R^1f_*\mathcal O_E$ is nonzero; the Hodge exact sequence has rank two, so they form a basis after
the displayed discriminant is inverted.

### 13.2 Reduction of differentials

Write

$$
P=x(x-1)(x-\lambda),\qquad y^2=P.
$$

Differentiating with respect to $\lambda$ while holding $x$ fixed gives

$$
\partial_\lambda\omega
=\frac{x(x-1)}{2y^3}\,dx,
\qquad
\partial_\lambda\eta
=\frac{x^2(x-1)}{2y^3}\,dx. \tag{13.3}
$$

To reduce a numerator $N(x)dx/y^3$ modulo exact forms, use

$$
d\left(\frac{Q(x)}y\right)
=\frac{Q'P-\frac12QP'}{y^3}\,dx. \tag{13.4}
$$

Solving polynomial identities in (13.4) gives

$$
\frac{x(x-1)}{2y^3}dx
\equiv\frac{\lambda\omega-\eta}
{2\lambda(1-\lambda)}, \tag{13.5}
$$

and

$$
\frac{x^2(x-1)}{2y^3}dx
\equiv\frac{\omega-\eta}{2(1-\lambda)} \tag{13.6}
$$

in de Rham cohomology. For example, in (13.5) one may take

$$
Q=\frac{x^2-x}{\lambda(1-\lambda)};
$$

substitution into (13.4) verifies the identity after moving the indicated combination of
$\omega,\eta$ to the other side. For (13.6), take
$Q=(x^2-x)/(1-\lambda)$. Thus the reduction uses only exact differentials and is valid over the
chosen base ring.

### 13.3 The connection matrix

Equations (13.3)--(13.6) give

$$
\nabla\omega=
\frac{d\lambda}{2\lambda(1-\lambda)}
(\lambda\omega-\eta), \tag{13.7}
$$

$$
\nabla\eta=
\frac{d\lambda}{2\lambda(1-\lambda)}
(\lambda\omega-\lambda\eta). \tag{13.8}
$$

With columns recording the derivatives of the ordered basis $(\omega,\eta)$, the matrix is

$$
\nabla=d+
\frac{d\lambda}{2\lambda(1-\lambda)}
\begin{pmatrix}
\lambda&\lambda\\
-1&-\lambda
\end{pmatrix}. \tag{13.9}
$$

The first column of (13.9) has a nonzero component modulo the Hodge line, so $F^1$ is not
horizontal. That component is the Higgs map and witnesses the nontrivial Kodaira--Spencer class of
the Legendre family. The only poles of the matrix occur at the omitted degenerations
$0,1,\infty$; on the open smooth base it is regular.

### 13.4 The Picard--Fuchs equation

Let a horizontal functional on the dual de Rham bundle assign

$$
Y=I(\omega),\qquad Z=I(\eta).
$$

Horizontality and (13.7)--(13.8) give

$$
Y'=\frac{\lambda Y-Z}{2\lambda(1-\lambda)},
\qquad
Z'=\frac{Y-Z}{2(1-\lambda)}. \tag{13.10}
$$

Eliminating $Z$ yields

$$
\lambda(1-\lambda)Y''+(1-2\lambda)Y'
-\frac14Y=0. \tag{13.11}
$$

This is the Picard--Fuchs equation of the family. Over the complex numbers, integrating $\omega$
over a locally constant topological cycle produces a solution, but equation (13.11) was obtained
entirely from algebraic differential reduction. Its regular singularities occur exactly at the
three parameters where the elliptic curve degenerates.

## 14. The de Rham package for later arithmetic geometry

The constructions now fit into one reusable package. This final chapter records both the positive
results and the checks that prevent them from being applied outside their hypotheses.

### 14.1 A reusable theorem package

**Relative de Rham theory.** For a smooth morphism $X\to S$, the finite complex
$\Omega^\bullet_{X/S}$ is functorial and compatible with arbitrary base change term by term. Its
hypercohomology carries a multiplicative Hodge filtration and cup products. Properness makes the
Hodge-page terms coherent; local freeness and base change of the abutment require degeneration or
another perfectness argument.

**Curves.** For a smooth proper geometrically connected curve of genus $g$ over a locally
noetherian base, the Hodge-to-de Rham sequence degenerates in every characteristic. There is a
base-change-compatible exact sequence

$$
0\to f_*\omega_{C/S}\to\mathcal H^1_{\mathrm{dR}}(C/S)
\to R^1f_*\mathcal O_C\to0,
$$

whose terms have ranks $g,2g,g$. Cup product and trace give a perfect alternating pairing, and the
Hodge bundle is Lagrangian.

**Gauss--Manin.** For a smooth tower $X\to S\to T$, once relative de Rham cohomology is a
base-change-compatible vector bundle, the base-form filtration on $\Omega^\bullet_{X/T}$ gives a
canonical integrable connection. It is functorial, compatible with cup products and trace, and
satisfies Griffiths transversality. On curves its graded map is cup product with the
Kodaira--Spencer class.

**Abelian schemes.** De Rham cohomology is the exterior algebra on degree one, is finite locally
free, and commutes with arbitrary base change. Degree one fits into

$$
0\to\omega_A\to\mathcal H^1_{\mathrm{dR}}(A/S)
\to\omega_{A^\vee}^\vee\to0.
$$

The Poincare class pairs the degree-one bundles of $A$ and $A^\vee$ perfectly. A principal
polarization gives a horizontal perfect alternating form with Lagrangian Hodge subbundle.

### 14.2 Failure modes and hypothesis checks

Before using the package, the following distinctions must be checked.

- Smoothness is needed for locally free differential forms and for the cotangent filtration.
  Ordinary differentials on a nodal curve are not a substitute for the smooth de Rham complex.

- Properness is needed for coherent finiteness, traces, and the perfect global pairings used here.
  Nonproper de Rham cohomology exists but has different boundary behavior.

- Hodge-to-de Rham degeneration is not automatic from boundedness. It was proved directly for
  curves and abelian schemes; a general smooth proper family needs its own degeneration theorem.

- Degeneration identifies graded pieces, not a canonical direct sum. The Hodge exact sequence of
  a varying curve usually has no horizontal splitting.

- Characteristic-zero polynomial integration cannot be used in characteristic $p$. The identity
  $d(t^p)=0$ is the basic counterexample.

- A connection requires a specified direction $S/T$. The relative cohomology bundle over $S$ does
  not determine which differentials count as base differentials until $T$ is fixed.

- Arbitrary coefficient change requires finite local freeness or a derived base-change theorem.
  Coherence by itself does not eliminate Tor from neighboring degrees.

- An isogeny identifies de Rham cohomology by pullback only after its degree is invertible, unless
  a stronger argument is supplied. In residue characteristic its cotangent map can be singular.

These checks are part of the mathematical content: each prevents a real counterexample rather
than a merely formal inconvenience.

### 14.3 Conclusion

Algebraic de Rham cohomology begins with the universal derivative and ends with a flat geometric
object. Hypercohomology joins local differential forms to global gluing classes. The Hodge
filtration remembers their form degrees, while proper coherent cohomology makes its layers finite.
For curves, residues and duality force degeneration and turn degree one into a symplectic bundle.
For abelian schemes, translation and the Hopf structure force every degree to be an exterior power
of degree one.

When the base itself moves, the absolute de Rham complex records that motion. Filtering it by base
forms produces the Gauss--Manin connection; the equality $d^2=0$ becomes integrability, the product
rule becomes horizontality of cup products, and the interaction of two filtrations becomes
Griffiths transversality. The Kodaira--Spencer class then identifies the derivative of the Hodge
bundle with the infinitesimal deformation of the family. For a polarized abelian scheme, the
Poincare class makes the resulting flat bundle symplectic.

The final package is therefore one continuous chain:

$$
\text{universal differentials}
\longrightarrow\text{de Rham hypercohomology}
\longrightarrow\text{Hodge filtration}
\longrightarrow\text{Gauss--Manin connection}
\longrightarrow\text{polarized variation}.
$$

It supplies the degree-one linear algebra, functoriality, base change, cup products, and
connections needed to compare smooth curves and abelian schemes with the integral cohomology
theories that follow.
