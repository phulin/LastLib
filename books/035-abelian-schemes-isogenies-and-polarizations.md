# Abelian Schemes, Isogenies, and Polarizations

## Contents

1. [The geometry carried by a proper group](#1-the-geometry-carried-by-a-proper-group)
   - [The organizing questions](#11-the-organizing-questions)
   - [Conventions and standing hypotheses](#12-conventions-and-standing-hypotheses)
   - [Rigidity and its first consequences](#13-rigidity-and-its-first-consequences)
   - [Fibers, dimension, and base change](#14-fibers-dimension-and-base-change)
2. [Line bundles on an abelian scheme](#2-line-bundles-on-an-abelian-scheme)
   - [Why translation is the correct probe](#21-why-translation-is-the-correct-probe)
   - [Rigidification and the theorem of the square](#22-rigidification-and-the-theorem-of-the-square)
   - [The theorem of the cube](#23-the-theorem-of-the-cube)
   - [Symmetry and pullback by multiplication](#24-symmetry-and-pullback-by-multiplication)
   - [Algebraic triviality and numerical triviality](#25-algebraic-triviality-and-numerical-triviality)
3. [The dual abelian scheme](#3-the-dual-abelian-scheme)
   - [The moduli problem](#31-the-moduli-problem)
   - [Representability and the Poincare bundle](#32-representability-and-the-poincare-bundle)
   - [The biextension laws](#33-the-biextension-laws)
   - [Functoriality and biduality](#34-functoriality-and-biduality)
   - [Products and examples](#35-products-and-examples)
4. [Homomorphisms and isogenies](#4-homomorphisms-and-isogenies)
   - [Rigidity of maps](#41-rigidity-of-maps)
   - [Equivalent definitions of an isogeny](#42-equivalent-definitions-of-an-isogeny)
   - [Multiplication maps and torsion](#43-multiplication-maps-and-torsion)
   - [Degree and composition](#44-degree-and-composition)
   - [Dual homomorphisms and dual isogenies](#45-dual-homomorphisms-and-dual-isogenies)
5. [Quotients by finite subgroup schemes](#5-quotients-by-finite-subgroup-schemes)
   - [Why a sheaf quotient is unavoidable](#51-why-a-sheaf-quotient-is-unavoidable)
   - [Construction of the quotient](#52-construction-of-the-quotient)
   - [The quotient theorem](#53-the-quotient-theorem)
   - [Universal properties and base change](#54-universal-properties-and-base-change)
   - [Successive quotients](#55-successive-quotients)
   - [The Serre tensor construction](#56-the-serre-tensor-construction)
6. [Kernels and duality](#6-kernels-and-duality)
   - [The character hidden in a trivialized pullback](#61-the-character-hidden-in-a-trivialized-pullback)
   - [Kernel of the dual isogeny](#62-kernel-of-the-dual-isogeny)
   - [Annihilators and exact sequences](#63-annihilators-and-exact-sequences)
   - [The dual-isogeny identities](#64-the-dual-isogeny-identities)
7. [Weil pairings](#7-weil-pairings)
   - [Construction from the Poincare bundle](#71-construction-from-the-poincare-bundle)
   - [Bilinearity, functoriality, and base change](#72-bilinearity-functoriality-and-base-change)
   - [Perfectness in every characteristic](#73-perfectness-in-every-characteristic)
   - [Compatibility through levels](#74-compatibility-through-levels)
   - [The prime-to-characteristic pointwise picture](#75-the-prime-to-characteristic-pointwise-picture)
   - [Prime-adic Tate modules](#76-prime-adic-tate-modules)
8. [Polarizations](#8-polarizations)
   - [From an ample line bundle to a homomorphism](#81-from-an-ample-line-bundle-to-a-homomorphism)
   - [Intrinsic characterization](#82-intrinsic-characterization)
   - [Symmetry, type, and degree](#83-symmetry-type-and-degree)
   - [Principal polarizations](#84-principal-polarizations)
   - [The induced alternating pairing](#85-the-induced-alternating-pairing)
   - [Vanishing and the rank of the pushforward](#86-vanishing-and-the-rank-of-the-pushforward)
9. [Polarized isogenies and isotropic kernels](#9-polarized-isogenies-and-isotropic-kernels)
   - [Pulling back a polarization](#91-pulling-back-a-polarization)
   - [Descent across a quotient](#92-descent-across-a-quotient)
   - [Orthogonal kernels](#93-orthogonal-kernels)
   - [Maximal isotropic quotients](#94-maximal-isotropic-quotients)
     9A. [Theta groups in standard form](#9a-theta-groups-in-standard-form)
   - [Why a standard form is needed and what it can say](#9a1-why-a-standard-form-is-needed-and-what-it-can-say)
   - [The standard Heisenberg group scheme](#9a2-the-standard-heisenberg-group-scheme)
   - [The commutator pairing and its normal form](#9a3-the-commutator-pairing-and-its-normal-form)
   - [Rigidity of central extensions and the existence of theta structures](#9a4-rigidity-of-central-extensions-and-the-existence-of-theta-structures)
   - [The automorphism group and the torsor of theta structures](#9a5-the-automorphism-group-and-the-torsor-of-theta-structures)
   - [The Schrödinger representation and Stone–von Neumann](#9a6-the-schrödinger-representation-and-stonevon-neumann)
   - [Theta coordinates on the space of sections](#9a7-theta-coordinates-on-the-space-of-sections)
   - [What the standard form gives](#9a8-what-the-standard-form-gives)
10. [Extension over normal bases](#10-extension-over-normal-bases)
    - [Why normality is the threshold](#101-why-normality-is-the-threshold)
    - [Extension of homomorphisms](#102-extension-of-homomorphisms)
    - [Extension of isogenies](#103-extension-of-isogenies)
    - [Extension of finite kernels and quotients](#104-extension-of-finite-kernels-and-quotients)
    - [Extension of polarizations](#105-extension-of-polarizations)
    - [What normality does not guarantee](#106-what-normality-does-not-guarantee)
11. [Two-torsion under odd isogenies](#11-two-torsion-under-odd-isogenies)
    - [The Bezout mechanism](#111-the-bezout-mechanism)
    - [Preservation of the full two-torsion group scheme](#112-preservation-of-the-full-two-torsion-group-scheme)
    - [Rational full two-torsion over a field](#113-rational-full-two-torsion-over-a-field)
    - [Elliptic curves and the Frey configuration](#114-elliptic-curves-and-the-frey-configuration)
    - [Limits of the statement](#115-limits-of-the-statement)
12. [A structural synthesis](#12-a-structural-synthesis)
    - [The exact dictionary](#121-the-exact-dictionary)
    - [A safe workflow](#122-a-safe-workflow)
    - [Conclusion](#123-conclusion)

## 1. The geometry carried by a proper group

An abelian scheme is simultaneously a family of projective varieties, a commutative group, and a source of finite flat group schemes. None of these aspects may be discarded. Properness supplies extension and finiteness; smoothness supplies uniform tangent geometry; connected fibers prevent hidden discrete quotients; the group law turns line bundles into homomorphisms. The purpose of this chapter is to fix the language and isolate the rigidity principle that lets information at the identity control the whole family.

### 1.1 The organizing questions

For a smooth proper family $A\to S$, a line bundle can be translated by every point of $A$. The discrepancy between a bundle and its translate is often algebraically trivial, and that discrepancy varies homomorphically. This observation leads to the dual abelian scheme $A^\vee$. Once the dual exists, four constructions fit together:

$$
\begin{array}{ccc}
\text{line bundles}&\longrightarrow&\text{homomorphisms }A\to A^\vee\\
&&\downarrow\\
\text{finite subgroup schemes}&\longleftarrow&\text{isogeny kernels}.
\end{array}
$$

The Poincaré bundle on $A\times_SA^\vee$ joins the two rows. Its restriction to torsion gives Weil pairings; its pullback along an ample class gives a polarization; descent along a finite subgroup constructs quotient abelian schemes. Our aim is not merely to list these constructions, but to prove that they commute with base change and remain valid when torsion is nonreduced.

### 1.2 Conventions and standing hypotheses

An **abelian scheme** over $S$ is a smooth, proper, finitely presented group scheme $p:A\to S$ whose geometric fibers are connected. Its relative dimension is locally constant; when it equals $g$ we write $\dim(A/S)=g$. The identity is $e:S\to A$, inversion is $[-1]$, multiplication by $n$ is $[n]$, and translation by a $T$-point $a$ is $t_a:A_T\to A_T$.

All group schemes in this book are commutative. A finite flat group will always mean finite locally free; its order is its locally constant rank. Exactness of finite group schemes means exactness as fppf sheaves, so a quotient arrow is faithfully flat. This qualification matters in residue characteristic: geometric point sets can omit an entire connected infinitesimal kernel.

The dual symbol $A^\vee$ refers to an abelian scheme. The Cartier dual $G^D$ is defined only for a finite locally free commutative group scheme $G$. These operations meet in the formula

$$
A[n]^D\simeq A^\vee[n],
$$

but they are not the same construction.

### 1.3 Rigidity and its first consequences

The group law is useful because maps from a proper connected family into a separated group cannot vary independently in two directions.

**Rigidity lemma.** Let $X\to S$ be proper, flat, and of finite presentation with geometrically connected fibers and $p_*\mathcal O_X=\mathcal O_S$. Let $Y\to S$ be separated. If the restriction of $f:X\to Y$ to one geometric fiber $X_s$ factors as a morphism through a point $y\in Y_s$, then, after shrinking $S$ around $s$, $f$ factors through $S$.

**Proof.** Because $Y$ is separated, the graph of $f$ is closed in $X\times_SY$. Choose an affine neighborhood $V$ of $y$ in $Y$ and let $Z=X\setminus f^{-1}(V)$. Properness makes the image of $Z$ closed in $S$; it misses $s$, so after shrinking, $f$ lands in $V=\operatorname{Spec}_S\mathcal B$. A map $X\to V$ is an $\mathcal O_S$-algebra map $\mathcal B\to p_*\mathcal O_X=\mathcal O_S$, hence factors through a section of $V\to S$. $\square$

For an abelian scheme, $p_*\mathcal O_A=\mathcal O_S$: this holds on geometric fibers because a proper connected reduced variety has only constant functions, and coherent base change promotes the fiber statement to the family. Thus rigidity applies.

**Corollary 1.1 (homomorphism lemma).** If $A,B$ are abelian schemes and $f:A\to B$ is an $S$-morphism with $f(e_A)=e_B$, then $f$ is a homomorphism.

**Proof.** On $A\times_SA$ consider

$$
d(x,y)=f(x+y)-f(x)-f(y).
$$

It vanishes on $A\times e$ and $e\times A$. Apply rigidity first in the $x$-direction and then in the $y$-direction: $d$ is pulled back from the base and its value at $(e,e)$ is zero. Hence $d=0$. $\square$

The same argument proves that a morphism $A\to B$ is a translation of a homomorphism: subtract the section $f(e_A)$. It also proves uniqueness statements. Two homomorphisms equal on one fiber agree near that fiber if their equalizer contains that fiber; on a connected base, equality on a schematically dense open implies equality everywhere because the target is separated and the source is flat.

### 1.4 Fibers, dimension, and base change

Every base change $S'\to S$ carries $A$ to an abelian scheme $A_{S'}$. Smoothness, properness, finite presentation, the group laws, and geometric connectedness all survive. Conversely these properties may be tested after a faithfully flat quasi-compact base change. Thus arguments may pass to geometric fibers or to covers where line bundles are represented, provided the resulting data are descended.

Translation identifies all relative tangent spaces. If

$$
\omega_A=e^*\Omega^1_{A/S},
$$

then $\Omega^1_{A/S}\simeq p^*\omega_A$, and $\omega_A$ is locally free of rank $g$. Hence every fiber has the same dimension on each connected component of $S$. The identity section is not merely a marked point: it is the location where differentials, rigidifications, and normalization conditions are recorded.

Smoothness is indispensable here. A proper finite group scheme such as $\mu_p$ in characteristic $p$ is connected and carries a group law, but it is not an abelian scheme: its cotangent space jumps away from the geometry of a positive-dimensional smooth fiber. Geometric connectedness is equally important. The disjoint union $A\times\underline{\mathbf Z/2\mathbf Z}$ is smooth and proper, but its component group contributes functions and defeats the assertion $p_*\mathcal O=\mathcal O_S$.

The definition is insensitive to nilpotents in the base. A square-zero thickening changes the deformation problem but not the geometric-fiber condition. This is why arbitrary base change, rather than only extension of fields, is built into every theorem below.

We will repeatedly choose a relatively ample line bundle. This is justified by the polarized projective-embedding theorem: projectivity is fpqc-local for an abelian scheme, norms carry relatively ample bundles through finite locally free descent, and a sufficiently high power gives a closed immersion into a projective bundle. These are the projectivity and descent results proved in the earlier projective-geometry and descent volumes. Thus an abelian scheme is projective over $S$. All later uses of an ample bundle are local on $S$ and independent of the choice. Replacing $L$ by $L\otimes[-1]^*L$ makes it symmetric while preserving ampleness.

## 2. Line bundles on an abelian scheme

On a general projective variety, translation is unavailable and the tensor relation among pullbacks of a line bundle has no reason to simplify. On an abelian scheme, repeated addition forces a cubic identity. This identity is the engine behind duality, the finiteness of multiplication, and the quadratic behavior of polarizations.

### 2.1 Why translation is the correct probe

Let $L$ be a line bundle on $A$. For a $T$-point $a$ define

$$
\Delta_L(a)=t_a^*L\otimes L^{-1}.
$$

The bundle $\Delta_L(a)$ measures the failure of $L$ to be translation-invariant. It is insensitive to tensoring $L$ by a bundle pulled back from $S$. More importantly, the square theorem will show that $a\mapsto\Delta_L(a)$ is a homomorphism into the degree-zero Picard functor.

A **rigidification** of $L$ is an isomorphism $e^*L\simeq\mathcal O_S$. Any line bundle becomes rigidified after tensoring by $p^*(e^*L)^{-1}$. Rigidification removes the scalar ambiguity in automorphisms of a line bundle and makes canonical isomorphisms genuinely unique.

### 2.2 Rigidification and the theorem of the square

Write $m:A\times A\to A$ for addition and $p_1,p_2$ for projection. For a rigidified $L$ and $a,b\in A(T)$, the **theorem of the square** gives a canonical rigidified isomorphism

$$
t_{a+b}^*L\otimes L
\simeq t_a^*L\otimes t_b^*L
$$

for every $L$. Equivalently, $a\mapsto\Delta_L(a)$ is additive as a map to the degree-zero Picard functor. In universal form,

$$
m^*L\otimes p_1^*L^{-1}\otimes p_2^*L^{-1}
$$

is multiplicative separately after its normalization along the axes.

Here is the rigidity proof of additivity. On $A^3$ compare the two ways of translating $L$ successively by $x$ and $y$. Their quotient is a line bundle trivial on every coordinate plane. The relative Picard class of that quotient defines a map from one factor to a separated group and is zero at the identity. Rigidity forces it to be zero. Rigidifications then turn equality of classes into a unique isomorphism, and evaluating on the coordinate axes verifies the cocycle. Consequently

$$
\Delta_L(a+b)\simeq\Delta_L(a)\otimes\Delta_L(b).
$$

This is the first appearance of a recurring method: prove an identity fiberwise along the axes, use rigidity to make it global, and use rigidification to remove units from the base.

### 2.3 The theorem of the cube

The full cubic relation is more symmetric. For nonempty $I\subseteq\{1,2,3\}$ let $m_I:A^3\to A$ add the coordinates indexed by $I$. Define

$$
\Theta(L)=
\bigotimes_{\varnothing\ne I\subseteq\{1,2,3\}}
m_I^*L^{\otimes(-1)^{3-|I|}}.
$$

**Theorem 2.1 (the cube).** If $L$ is rigidified, $\Theta(L)$ has a unique trivialization compatible with the induced trivializations on the three coordinate hyperplanes. The trivialization is functorial in $L$ and stable under arbitrary base change.

**Proof.** We use only the preliminary relative Picard space supplied by the Hilbert-scheme construction for projective proper families; the identification of its degree-zero component as the dual abelian scheme is proved in Chapter 3. Regard $\Theta(L)$ as a family of rigidified line bundles on the first copy of $A$, parametrized by the last two. Its restriction when either parameter is zero is trivial by cancellation. Its class therefore defines a morphism $c:A\times A\to\operatorname{Pic}_{A/S}$ vanishing on both axes. The homomorphism lemma in each variable makes $c$ bilinear and places its image in the degree-zero component. For fixed $y$, the map $x\mapsto c(x,y)$ is a homomorphism. As $y$ varies, its class defines a map from the connected proper group $A$ into the unramified, hence discrete, space of homomorphisms. The unramified assertion follows directly: an infinitesimal variation would be a homomorphism from $A$ to a vector group, and properness makes all its coordinate functions constant, hence zero. The class is therefore constant in $y$; at $y=0$ it is zero. Thus $c=0$.

The vanishing of the relative Picard class says that $\Theta(L)$ is pulled back from the parameter base. The coordinate rigidification identifies that pullback with the trivial bundle. Two such trivializations differ by a unit on $A^3$; proper connected fibers make the unit come from $S$, and its value on an axis is $1$. This proves uniqueness and forces all cocycle compatibilities. $\square$

The theorem of the square follows by restricting the cube identity. Conversely, the cube is the coherent three-variable form needed to ensure that the Poincare bundle is a biextension rather than merely a collection of line bundles.

### 2.4 Symmetry and pullback by multiplication

A rigidified line bundle is **symmetric** if $[-1]^*L\simeq L$ compatibly with rigidification. The cube theorem yields, by induction on $n$,

$$
[n]^*L\simeq
L^{\otimes n(n+1)/2}\otimes[-1]^*L^{\otimes n(n-1)/2}. \tag{2.1}
$$

For the induction, restrict the cube identity to $(x,nx,-x)$ and cancel the already known terms; the rigidifications make the resulting isomorphisms coherent. If $L$ is symmetric, (2.1) becomes

$$
[n]^*L\simeq L^{\otimes n^2}. \tag{2.2}
$$

Every $L$ has a symmetric companion $L\otimes[-1]^*L$. If $L$ is relatively ample, so is this companion: inversion preserves ampleness and tensor products of ample bundles are ample. Thus no polarization argument loses generality by first choosing a symmetric ample bundle.

### 2.5 Algebraic triviality and numerical triviality

A rigidified bundle $M$ is **algebraically trivial** if each geometric-fiber class belongs to the identity component of the Picard scheme. Equivalently, fppf locally on the base it occurs as the difference of two fibers in a connected family of line bundles. Such bundles satisfy $\Delta_M(a)=0$ for all $a$, so translation preserves their class.

On an abelian variety over an algebraically closed field, algebraic and numerical triviality agree. One direction is immediate because intersection numbers are constant in connected families. Conversely, if $M$ is numerically trivial and $L$ is ample, then $L^r\otimes M$ has the same Hilbert polynomial as $L^r$. For $r$ large, cohomology and base change put these twists in one connected Hilbert parameter space; subtracting a fixed divisor joins $M$ to the identity in the Picard scheme. The relative statement is fiberwise. This criterion will let positivity be recognized through the homomorphism $\lambda_L$ rather than through a chosen divisor.

Two examples clarify the distinction. On an elliptic curve, $\mathcal O(P-Q)$ is algebraically trivial for any two points $P,Q$; translation changes its divisor but not its degree-zero class. By contrast, $\mathcal O(ne)$ has positive degree $n$ and is ample, so its translation discrepancy varies nontrivially with the translating point. On $E\times E$, the divisor $E\times\{e\}$ is nef but not ample: its restriction to the first factor is trivial. Its associated homomorphism has a positive-dimensional kernel, exactly detecting the failure of ampleness.

## 3. The dual abelian scheme

The phrase “dual abelian scheme” does not mean a linear dual. It means a space representing translation-invariant line bundles, with tensor product as its group law. The universal bundle then encodes every such line bundle at once and supplies all later pairings.

### 3.1 The moduli problem

For an $S$-scheme $T$, let $\operatorname{Pic}^0_{A/S}(T)$ be the group of isomorphism classes of line bundles $M$ on $A_T$ that are rigidified along $e_T$ and algebraically trivial on every geometric fiber. Descent of line bundles makes this an fppf sheaf. Rigidification is essential: without it, automorphisms by units on $T$ prevent a universal line bundle from existing in this direct form.

Tensor product gives the group operation and dualization gives inversion. The cube theorem ensures that algebraic triviality and the rigidified group laws commute with every base change.

### 3.2 Representability and the Poincare bundle

**Theorem 3.1 (dual representability).** The sheaf $\operatorname{Pic}^0_{A/S}$ is represented by an abelian scheme $A^\vee/S$ of relative dimension $g$. Formation of $A^\vee$ commutes with arbitrary base change. There is a universal rigidified line bundle

$$
\mathcal P_A\quad\text{on}\quad A\times_SA^\vee,
$$

trivialized along both zero sections.

**Proof.** This is the dual-representability theorem proved in the earlier volume on coherent cohomology and dual abelian schemes. We recall its construction and the precise interface used here. Choose a relatively ample symmetric line bundle $L$ on $A$. For $r$ sufficiently large on each quasi-compact parameter chart, every $L^r\otimes M$ with $M$ algebraically trivial has vanishing higher cohomology, is generated by sections, and has a fixed Hilbert polynomial on each connected component of $S$. Uniformity follows from projective boundedness and coherent base change. Effective divisors in these bundles therefore occupy an open part of one relative Hilbert scheme.

Pairs of such divisors represent the difference $M$; equality of differences is the equivalence relation cut out by a principal divisor. Descent for line bundles and projective schemes makes the quotient an algebraic space, while the cubical group law and the ample embedding produce invariant affine neighborhoods, so the quotient is a scheme. Rigidification kills the remaining scalar stabilizer. The identity component is separated and of finite presentation.

Properness follows from the valuative criterion. Over a valuation ring, extend a generic divisor after adding a sufficiently ample divisor; two extensions differ by a vertical divisor. Translation invariance and rigidification force that vertical difference to be pulled back from the base and hence trivial as a rigidified class. Smoothness is the substantive deformation step in the cited theorem: the tangent space at the identity is $R^1p_*\mathcal O_A$, locally free of rank $g$, and the normalized cube structure makes the obstruction cocycle for a square-zero lift vanish. Consequently the identity component is formally smooth; finite presentation turns this into smoothness of relative dimension $g$. Its geometric fibers are connected by construction, so it is an abelian scheme.

The universal element of the represented functor is $\mathcal P_A$. Normalizing it on both axes is possible because it is already rigidified on the first; tensoring by a pullback from $A^\vee$ supplies the second normalization. Universality makes the normalization unique. Every step commutes with base change: Hilbert schemes, coherent base change, descent, identity components in this smooth proper family, and the universal rigidification do. $\square$

There are two points of the proof worth retaining. First, the full relative Picard functor need not be proper: components corresponding to different numerical classes form a discrete, often infinite, group. The degree-zero component is proper because translation-invariant classes have no direction in which their numerical degree can escape. Second, smoothness of $A^\vee$ is not a formal consequence of representability. The cubical identity removes the higher obstruction that a general higher-dimensional projective variety can possess.

Infinitesimally, the construction gives

$$
\operatorname{Lie}(A^\vee)\simeq R^1p_*\mathcal O_A.
$$

Indeed a line bundle on $A\times\operatorname{Spec}(R[\epsilon]/\epsilon^2)$ trivial modulo $\epsilon$ is represented by a Cech cocycle $1+\epsilon a_{ij}$; tensor product adds the classes $[a_{ij}]$. Rigidification removes the class pulled back from the base. This calculation explains both the tangent rank $g$ and the contravariance of differentials under $f^\vee$.

### 3.3 The biextension laws

The Poincare bundle is additive in each variable. On $A\times A\times A^\vee$ there is a canonical isomorphism

$$
(m_A\times1)^*\mathcal P_A
\simeq p_{13}^*\mathcal P_A\otimes p_{23}^*\mathcal P_A, \tag{3.1}
$$

and on $A\times A^\vee\times A^\vee$,

$$
(1\times m_{A^\vee})^*\mathcal P_A
\simeq p_{12}^*\mathcal P_A\otimes p_{13}^*\mathcal P_A. \tag{3.2}
$$

For (3.2), tensor product is literally the group law represented by $A^\vee$. For (3.1), the theorem of the square says that an algebraically trivial bundle is additive under pullback along addition. Both isomorphisms are normalized on the axes, so rigidity makes them unique and forces associativity and compatibility. This pair of coherent laws is called the **biextension structure**.

### 3.4 Functoriality and biduality

If $f:A\to B$ is a homomorphism, pullback of rigidified algebraically trivial bundles defines

$$
f^\vee:B^\vee\longrightarrow A^\vee. \tag{3.3}
$$

Thus duality is contravariant, $(gf)^\vee=f^\vee g^\vee$, and it commutes with base change. Universality also gives an evaluation morphism

$$
\delta_A:A\longrightarrow A^{\vee\vee}. \tag{3.4}
$$

**Theorem 3.2 (biduality).** The map $\delta_A$ is an isomorphism, natural in $A$, and $\delta_{A^\vee}$ is dual to $\delta_A$.

**Proof.** The assertion is stable under base change, so work fiberwise over an algebraically closed field and choose an ample $L$. Translation defines

$$
\lambda_L:A\to A^\vee,\qquad a\mapsto t_a^*L\otimes L^{-1}.
$$

The square theorem makes this a homomorphism. Ampleness implies its kernel is finite: if the connected stabilizer were positive-dimensional, $L$ would restrict to a translation-invariant, hence numerically trivial, bundle there, contradicting ampleness. Its image has dimension $g$ and is therefore all of $A^\vee$; so $\lambda_L$ is an isogeny.

Applying the universal property twice gives

$$
\lambda_L^\vee\circ\delta_A=\lambda_L. \tag{3.5}
$$

The degree of $\lambda_L$ equals the degree of $\lambda_L^\vee$: both are the square of the top self-intersection $c_1(L)^g/g!$. Taking degrees in (3.5) gives $\deg\delta_A=1$. A finite degree-one map between smooth varieties is an isomorphism. Fiberwise isomorphism plus finite presentation proves that (3.4) is an isomorphism over $S$. Naturality follows from the universal bundle. $\square$

### 3.5 Products and examples

The universal property gives

$$
(A\times_SB)^\vee\simeq A^\vee\times_SB^\vee;
$$

a rigidified algebraically trivial bundle on a product is the tensor product of its restrictions, with the possible mixed term killed by normalization and the cube relation.

For an elliptic scheme $E/S$, the divisor of the zero section defines

$$
E\xrightarrow{\sim}E^\vee,\qquad
P\longmapsto\mathcal O_E(P-e),
$$

the canonical principal polarization. For a product $E_1\times E_2$, the product polarization is principal, though additional homomorphisms $E_1\to E_2$ can produce non-product line-bundle classes. A Jacobian carries its theta polarization, but its construction belongs to the geometry of curves; the present theory needs only that it is an ample symmetric class inducing an isomorphism with the dual.

## 4. Homomorphisms and isogenies

An isogeny is the finite change of coordinates natural to abelian geometry. It retains dimension and replaces the group by a finite quotient. Over a field one often defines it as a surjective homomorphism with finite kernel. Over a base, surjectivity must be sheaf-theoretic and flatness cannot be omitted. This chapter establishes the equivalent safe formulations.

### 4.1 Rigidity of maps

For abelian schemes $A,B/S$, the functor $\underline{\operatorname{Hom}}_S(A,B)$ is unramified and separated over $S$. The infinitesimal statement is elementary. If two homomorphisms agree modulo a square-zero ideal, their difference lands infinitesimally at the identity; it is represented by a global homomorphism from the proper group $A$ to the vector group attached to $\operatorname{Lie}(B)$. Every regular function on $A$ comes from $S$, and a constant homomorphism taking the identity to zero is zero. Thus there are no nonzero infinitesimal deformations of a homomorphism.

Consequently a homomorphism is determined by any schematically dense restriction. This rigidity will turn generic-fiber maps over normal bases into global maps once existence is proved.

### 4.2 Equivalent definitions of an isogeny

A homomorphism $f:A\to B$ is an **isogeny** if it is finite locally free and faithfully flat. Its degree is its locally constant rank.

**Proposition 4.1.** Suppose $S$ is connected and $A,B$ have the same relative dimension. The following are equivalent:

1. $f$ is an isogeny;
2. $f$ is finite and fiberwise surjective;
3. $\ker f$ is finite locally free and every geometric-fiber image has dimension $\dim B_s$;
4. $f$ is an fppf quotient by the finite locally free subgroup $\ker f$.

**Proof.** An isogeny has finite locally free kernel by base change along $e_B$ and is fiberwise surjective. Moreover the difference map gives an isomorphism

$$
(\ker f)\times_SA\xrightarrow{\sim}A\times_BA,
\qquad(h,a)\longmapsto(a+h,a).
$$

Since $f$ is faithfully flat, this identifies $B$ with the fppf quotient by $\ker f$. Thus $1$ implies $2$--$4$.

If $f$ is finite and fiberwise surjective, each fiber map is finite between smooth equidimensional varieties. The source is Cohen--Macaulay and the target regular; miracle flatness gives fiberwise flatness. Since both schemes are flat over $S$, the fiberwise criterion gives flatness of $f$. A finite flat morphism of finite presentation is locally free, and fiberwise surjectivity makes it faithful. This proves $2\Rightarrow1$.

Assume $3$ and put $H=\ker f$. On a geometric fiber, every nonempty fiber of $f_s$ is a translate of $H_s$, hence finite. Thus $f$ is quasi-finite; properness makes it finite. Its geometric-fiber image is a closed subgroup of full dimension in the connected abelian variety $B_s$, so it is all of $B_s$. Hence $3\Rightarrow2$. Finally, under $4$ the quotient map is an $H$-torsor. Finite local freeness and positive rank can be checked after this faithfully flat cover, where the map becomes the projection $H\times A\to A$. Thus $4\Rightarrow1$. $\square$

Over a field, “surjective with finite kernel” is therefore safe. Over a general base, it is safer to say finite locally free and faithfully flat, because a finite closed kernel of a map of finite-flat groups need not itself be flat without additional geometry.

### 4.3 Multiplication maps and torsion

**Theorem 4.2.** If $A/S$ has relative dimension $g$ and $n\ge1$, then

$$
[n]:A\to A
$$

is an isogeny of degree $n^{2g}$. Hence

$$
A[n]=\ker[n]
$$

is finite locally free of order $n^{2g}$, compatibly with arbitrary base change.

**Proof.** Choose a symmetric relatively ample $L$. Formula (2.2) gives $[n]^*L\simeq L^{n^2}$. If a geometric fiber of $[n]$ contained a positive-dimensional closed subscheme, the pullback of $L$ would be trivial there because the map is constant, while $L^{n^2}$ is ample there, a contradiction. Thus $[n]$ is quasi-finite; properness makes it finite. Its fiberwise image is a closed connected subgroup of the same dimension as $A_s$, hence all of $A_s$.

On a geometric fiber, the projection formula for top intersections gives

$$
\deg([n])\,c_1(L)^g=c_1([n]^*L)^g=n^{2g}c_1(L)^g.
$$

The positive number $c_1(L)^g$ cancels. Proposition 4.1 proves finite local freeness. The kernel is its base change along the identity and has the same rank. $\square$

If $n$ is invertible on $S$, the differential of $[n]$ is multiplication by $n$, so $[n]$ is etale and $A[n]$ is finite etale. No such claim holds when a residue characteristic divides $n$: $A[n]$ can be connected and nonreduced, but its scheme-theoretic order remains $n^{2g}$.

For an elliptic curve over an algebraically closed field of characteristic different from $p$, this recovers

$$
E[p]\simeq\underline{\mathbf Z/p\mathbf Z}^2.
$$

In characteristic $p$, an ordinary elliptic curve has an exact connected--etale sequence

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\underline{\mathbf Z/p\mathbf Z}\longrightarrow0,
$$

while a supersingular elliptic curve has connected $E[p]$ of order $p^2$. Neither case contradicts the degree theorem. The first can have only $p$ geometric points and the second only the identity, while both kernels have scheme-theoretic length $p^2$. This is the basic reason every later kernel and orthogonal is kept as a group scheme.

### 4.4 Degree and composition

If $f:A\to B$ and $g:B\to C$ are isogenies, then $gf$ is an isogeny and

$$
\deg(gf)=\deg(g)\deg(f).
$$

This is multiplication of ranks for finite locally free morphisms. There is an exact sequence

$$
0\longrightarrow\ker f\longrightarrow\ker(gf)
\xrightarrow{f}\ker g\longrightarrow0, \tag{4.1}
$$

where the last arrow is fppf-surjective. Indeed a point of $\ker g$ lifts fppf-locally through the torsor $A\to B$, and any lift lies in $\ker(gf)$. Rank multiplicativity in (4.1) gives the same degree formula without counting geometric points.

### 4.5 Dual homomorphisms and dual isogenies

Pullback gives $f^\vee:B^\vee\to A^\vee$. Biduality implies

$$
(f^\vee)^\vee=f
$$

after the canonical identifications. Moreover $([n]_A)^\vee=[n]_{A^\vee}$ because pulling a line-bundle class back by $[n]$ multiplies that class by $n$.

If $f$ is an isogeny, then $f^\vee$ is an isogeny of the same degree. One proof uses the finite kernel calculation of Chapter 6. A preliminary degree argument also works: choose ample bundles on both sides and compare the top intersection of pullbacks under $f$; the transpose correspondence gives equal determinant indices. The kernel proof is stronger, because it canonically identifies

$$
\ker(f^\vee)\simeq(\ker f)^D
$$

and hence proves equal degree in every characteristic.

## 5. Quotients by finite subgroup schemes

The quotient $A/H$ should identify points differing by translation by $H$. On ordinary point sets this prescription is inadequate: an $H$-torsor need not have a section, so a quotient point may acquire a representative only after an fppf cover. The correct object is therefore a sheaf quotient, and its representability is a geometric theorem.

### 5.1 Why a sheaf quotient is unavoidable

Let $H\hookrightarrow A$ be a finite locally free subgroup. Define the fppf sheaf

$$
(A/H)(T)=A(T)/H(T)
$$

only after sheafification. The resulting map $A\to A/H$ is intended to be an $H$-torsor. For example, multiplication $\mathbf G_m\to\mathbf G_m$ is fppf-surjective even when not every unit of a ring has an $n$th root. Abelian quotients have the same local-lifting feature.

Because $A$ is proper rather than affine, the invariant-ring construction for finite affine groups cannot be applied globally. Projectivity and descent supply the missing construction.

### 5.2 Construction of the quotient

Choose a symmetric relatively ample line bundle $L$ on $A$. The naive tensor product of translates

$$
L_H=\bigotimes_{h\in H}t_h^*L
$$

makes sense only when $H$ is a disjoint union of sections. Scheme-theoretically it is replaced by the norm along the finite locally free projection $q:H\times_SA\to A$:

$$
N_q(m^*L)=\det q_*(m^*L)\otimes(\det q_*\mathcal O_{H\times A})^{-1}. \tag{5.1}
$$

The norm commutes with base change. Translation by $H$ on its first factor acts on the norm functor, and functoriality of determinant under composition gives $L_H$ a canonical $H$-linearization; the cocycle identity is the associativity of translation. No decomposition of $H$ into sections is being assumed. The bundle remains relatively ample by norm-ampleness for finite locally free morphisms, applied after the automorphism $(h,a)\mapsto(h,h+a)$ identifies the action map with the projection.

A sufficiently high power supplies invariant affine nonvanishing neighborhoods. On each such chart the finite locally free affine-quotient theorem represents the orbit sheaf and proves both faithful flatness and the torsor identity. These affine quotients glue because their overlap maps are invariant and the relation

$$
H\times_SA\rightrightarrows A,
\qquad(h,a)\mapsto a, a+h,
$$

is finite locally free. The descended ample bundle makes the glued quotient projective over $S$. Call it $B$. This construction is the nonaffine quotient theorem proved for abelian schemes in the finite-flat volume; the norm argument is precisely what reduces it to the affine quotient theorem without assuming that $H$ is étale.

The construction is independent of the chosen $L$ and power: its quotient map represents the same fppf sheaf, and a representing object is unique. Addition and inversion on $A$ respect $H$-orbits and descend to $B$. The image of $e_A$ is the identity.

### 5.3 The quotient theorem

**Theorem 5.1.** Let $A/S$ be an abelian scheme and $H\hookrightarrow A$ a finite locally free subgroup. Then the fppf quotient $A/H$ is represented by an abelian scheme $B/S$. The quotient map

$$
q:A\longrightarrow B
$$

is an isogeny with kernel $H$, is an $H$-torsor, and has degree $|H|$.

**Proof.** The construction above gives a projective group scheme $B$. Pulling $q$ back along itself, two lifts differ uniquely by a point of $H$, so the torsor map

$$
H\times_SA\longrightarrow A\times_BA,\qquad(h,a)\mapsto(a+h,a), \tag{5.2}
$$

is an isomorphism. The affine construction already proves that $q$ is faithfully flat. After this cover, its pullback is $H\times A\to A$, so finite local freeness descends and its rank is $|H|$. Smoothness of $B/S$ descends through the same cover. Properness follows from projectivity, finite presentation from the construction, and geometric connectedness follows because each $A_{\bar s}\to B_{\bar s}$ is surjective from a connected space. Thus $B$ is an abelian scheme. Equation (5.2) identifies the kernel with $H$. $\square$

Conversely, every isogeny $f:A\to B$ exhibits $B\simeq A/\ker f$ by Proposition 4.1. Finite flat subgroup schemes and isogenies are therefore equivalent presentations of the same operation.

### 5.4 Universal properties and base change

If $u:A\to C$ is a homomorphism trivial on $H$, then it is constant on the two arrows of the quotient relation and descends uniquely to $\bar u:A/H\to C$. Hence

$$
\operatorname{Hom}(A/H,C)
\simeq\{u\in\operatorname{Hom}(A,C):u|_H=0\}. \tag{5.3}
$$

Uniqueness follows because $q$ is faithfully flat. The descended map preserves the identity and is therefore a homomorphism by rigidity.

For every $S'\to S$,

$$
(A/H)_{S'}\simeq A_{S'}/H_{S'}. \tag{5.4}
$$

Indeed both sides represent the base-changed fppf quotient; alternatively, the construction by norms, descent, and invariant affine charts commutes with base change. No flatness of $S'\to S$ is needed because the torsor identity (5.2) does.

### 5.5 Successive quotients

If $H\subseteq K\subseteq A$ are finite locally free subgroup schemes and $K/H$ is finite locally free, then its image in $A/H$ is a finite locally free subgroup and

$$
(A/H)/(K/H)\simeq A/K. \tag{5.5}
$$

Both sides represent the sheaf sending $T$ to points of $A$ modulo local translation by $K$. Degrees give

$$
|K|=|H|\,|K/H|.
$$

One must retain the flatness hypotheses. A raw scheme-theoretic intersection or image of finite subgroup schemes over a higher-dimensional base can fail to be flat, in which case it is not an admissible isogeny kernel until flatness is separately proved.

Over a field of characteristic prime to $n$, the quotient theorem recovers the familiar construction from a Galois-stable subgroup $H\subset A[n](k^s)$: finite etale descent turns $H$ into a subgroup scheme, and $A/H$ is defined over $k$. In characteristic dividing $n$, a subgroup of geometric points records only the etale part. The connected subgroup $\mu_p\subset E[p]$ of an ordinary elliptic curve can be a valid isogeny kernel even though its geometric point set is trivial. Thus “quotient by the rational points of the kernel” is not an adequate construction in mixed or positive characteristic.

### 5.6 The Serre tensor construction

The quotient theorem manufactures a new abelian scheme by dividing an old one by a finite subgroup. There is a complementary manufacturing process, and it is the one demanded by every situation in which an abelian scheme carries more endomorphisms than the integers. Suppose a commutative ring $\mathcal O$ acts on $A$, meaning that a ring homomorphism

$$
\iota:\mathcal O\longrightarrow\operatorname{End}_S(A)
$$

has been fixed. Then $A(T)$ is an $\mathcal O$-module for every $S$-scheme $T$, functorially in $T$, and every $\mathcal O$-module $M$ produces a candidate for a new family of groups,

$$
F_M:T\longmapsto A(T)\otimes_{\mathcal O}M. \tag{5.6}
$$

For $M=\mathcal O$ this is $A$ itself; for $M=\mathcal O^n$ it is $A^n$. The question is whether $F_M$ is again an abelian scheme for more interesting $M$, and the answer is that finite projectivity of $M$ is exactly the right condition.

Two remarks explain why one should not hope for more. First, tensoring with a projective module is an exact operation that turns direct-sum decompositions into decompositions and idempotents into idempotents; this is precisely the structure that geometry can follow. Second, without projectivity the functor loses its content. Take $\mathcal O=\mathbf Z$ and $M=\mathbf Z/n\mathbf Z$. Then $F_M(T)=A(T)/nA(T)$, and since $[n]$ is an epimorphism of fppf sheaves the sheafification of $F_M$ is the zero sheaf. The presheaf (5.6) is nonzero and its sheafification is trivial: no scheme can record what has been destroyed. Projectivity is not a convenience of the proof; it is the exact boundary of the construction.

The motivating example is arithmetic. Let $\mathcal O=\mathcal O_F$ be the ring of integers of a number field acting on $A$, and let $\mathfrak c$ be a fractional ideal, a projective $\mathcal O_F$-module of rank one. Then the construction below produces an abelian scheme $A\otimes_{\mathcal O_F}\mathfrak c$ of the same relative dimension as $A$, with $A\otimes\mathcal O_F\simeq A$ and $(A\otimes\mathfrak a)\otimes\mathfrak b\simeq A\otimes\mathfrak a\mathfrak b$, and its dual is $A^\vee\otimes\mathfrak c^{-1}$. Polarization data in the presence of an $\mathcal O_F$-action are naturally homomorphisms $A\otimes_{\mathcal O_F}\mathfrak c\to A^\vee$ rather than $A\to A^\vee$, and the present section is what gives that phrase a meaning.

The strategy is to convert projectivity into an idempotent and then to do geometry with the idempotent. Choose $N$ and an isomorphism $M\oplus N\simeq\mathcal O^n$, and let $e\in\operatorname{End}_{\mathcal O}(\mathcal O^n)=M_n(\mathcal O)$ be the resulting projector onto $M$, so $e^2=e$, $\operatorname{im}(e)\simeq M$ and $\operatorname{im}(1-e)\simeq N$. Applying $\iota$ entrywise turns $e$ into an idempotent endomorphism

$$
\varepsilon=\iota(e)\in\operatorname{End}_S(A^n)=M_n(\operatorname{End}_S(A)).
$$

The first lemma says that the functor (5.6) is nothing but the kernel of $1-\varepsilon$.

**Lemma 5.2.** Let $P$ be any $\mathcal O$-module. There is an isomorphism

$$
P\otimes_{\mathcal O}M\;\simeq\;\ker\bigl(1-e:P^n\to P^n\bigr)=\operatorname{im}\bigl(e:P^n\to P^n\bigr),
$$

natural in $P$.

**Proof.** Tensoring the decomposition $M\oplus N\simeq\mathcal O^n$ with $P$ gives $(P\otimes M)\oplus(P\otimes N)\simeq P^n$, and under this identification $\operatorname{id}_P\otimes e$ is the projector onto the first summand, which is the matrix $e$ acting on $P^n$. For an idempotent endomorphism of an abelian group the image and the kernel of the complementary idempotent coincide: if $x=ey$ then $(1-e)x=(e-e^2)y=0$, and if $(1-e)x=0$ then $x=ex$. Naturality in $P$ is clear because the identification uses only the fixed matrix $e$. $\square$

Applying Lemma 5.2 with $P=A(T)$ identifies the presheaf (5.6) with $T\mapsto\ker\bigl((1-\varepsilon)(T)\bigr)$, which is the functor of points of the scheme-theoretic kernel of $1-\varepsilon$. In particular the presheaf (5.6) is already an fppf sheaf; no sheafification is needed, and this is a first sign that projectivity has changed the nature of the problem.

**Theorem 5.3 (Serre tensor construction).** Let $A/S$ be an abelian scheme of relative dimension $g$ with an action $\iota$ of a commutative ring $\mathcal O$, and let $M$ be a finitely generated projective $\mathcal O$-module. Then the functor (5.6) is represented by an abelian scheme

$$
A\otimes_{\mathcal O}M\longrightarrow S,
$$

namely by the closed subgroup scheme $\ker(1-\varepsilon)\subseteq A^n$ attached to any presentation of $M$ as a direct summand of $\mathcal O^n$. Its formation commutes with arbitrary base change, and if $M$ has constant rank $r$ then $A\otimes_{\mathcal O}M$ has relative dimension $rg$.

**Proof strategy.** Representability is Lemma 5.2 together with the observation that a kernel is a closed subgroup scheme. The substance is that this kernel is again an abelian scheme, and there the idempotent does all the work: it exhibits $A\otimes_{\mathcal O}M$ simultaneously as a closed subscheme of the proper $A^n$ (whence properness), as a retract of the smooth $A^n$ (whence smoothness), and as a direct factor of $A^n$ (whence connected fibers). Only the relative dimension needs a separate computation, and that is a statement about the Lie algebra.

**Proof.** Let $K=\ker(1-\varepsilon)$, the fiber product of $1-\varepsilon:A^n\to A^n$ with the identity section. Since $A^n\to S$ is separated and of finite presentation, its identity section is a closed immersion of finite presentation, so $K\to A^n$ is a closed immersion of finite presentation and $K$ is a closed subgroup scheme of $A^n$. It is proper over $S$, being a closed subscheme of a proper $S$-scheme, and of finite presentation over $S$. By Lemma 5.2 it represents (5.6).

_Retraction and smoothness._ Because $(1-\varepsilon)\circ\varepsilon=0$, the endomorphism $\varepsilon$ factors uniquely through $K$: there is $\pi:A^n\to K$ with $j\circ\pi=\varepsilon$, where $j:K\hookrightarrow A^n$ is the inclusion. On points, $\pi(x)=\varepsilon(x)$ and $\varepsilon(x)=x$ for $x\in K(T)$, so $\pi\circ j=\operatorname{id}_K$. Thus $K$ is a retract of $A^n$ over $S$. Smoothness now follows from the infinitesimal lifting criterion, which the retraction transports: let $T_0\subseteq T$ be a square-zero closed immersion of affine $S$-schemes and $x_0\in K(T_0)$. Smoothness of $A^n$ lifts $j(x_0)$ to some $y\in A^n(T)$, and $x=\pi(y)\in K(T)$ restricts to $\pi(j(x_0))=x_0$. Hence $K\to S$ is formally smooth, and being of finite presentation it is smooth.

_Fibers._ Let $K'=\ker(\varepsilon)$, which is a closed subgroup scheme of $A^n$ by the same argument. For every $T$ the idempotent endomorphism $\varepsilon$ of the abelian group $A^n(T)$ gives a decomposition $A^n(T)=\varepsilon A^n(T)\oplus(1-\varepsilon)A^n(T)=K(T)\oplus K'(T)$, natural in $T$. By Yoneda the addition map

$$
K\times_SK'\longrightarrow A^n
$$

is therefore an isomorphism of $S$-group schemes. Fix a geometric point $\bar s$ of $S$. Then $A^n_{\bar s}\simeq K_{\bar s}\times K'_{\bar s}$ with both factors nonempty, since both contain the identity. If $K_{\bar s}$ were disconnected, say $K_{\bar s}=U_1\sqcup U_2$ with both parts nonempty and open, then $A^n_{\bar s}=(U_1\times K'_{\bar s})\sqcup(U_2\times K'_{\bar s})$ would be a nontrivial decomposition of the connected scheme $A^n_{\bar s}$. Hence every geometric fiber of $K$ is connected. Being smooth, proper, of finite presentation, with geometrically connected fibers, and a commutative group scheme, $K$ is an abelian scheme.

_Base change._ For $S'\to S$ the endomorphism ring receives $\operatorname{End}_S(A)\to\operatorname{End}_{S'}(A_{S'})$, so $A_{S'}$ inherits the action of $\mathcal O$; the same presentation of $M$ gives the same idempotent matrix, and the formation of a kernel commutes with base change. Thus $(A\otimes_{\mathcal O}M)_{S'}\simeq A_{S'}\otimes_{\mathcal O}M$. Alternatively, both sides represent the same functor on $S'$-schemes.

_Relative dimension._ The relative dimension of a smooth group scheme is the rank of its Lie algebra, and the Lie algebra functor is left exact, being the kernel of the reduction map on dual-number points. Hence

$$
\operatorname{Lie}(A\otimes_{\mathcal O}M)
=\ker\bigl(1-e\mid\operatorname{Lie}(A)^n\bigr)
\simeq\operatorname{Lie}(A)\otimes_{\mathcal O}M,
$$

the last isomorphism by Lemma 5.2 applied to the $\mathcal O$-module $\operatorname{Lie}(A)$, on which $\mathcal O$ acts through $\iota$ by $\mathcal O_S$-linear endomorphisms. Rank may be computed at each point $s\in S$, and the idempotent description is compatible with the base change to $\kappa(s)$, so it suffices to prove that $V\otimes_{\mathcal O}M$ has dimension $rg$ where $V=\operatorname{Lie}(A_s)$, a $\kappa(s)$-vector space of dimension $g$ with an $\mathcal O$-action by $\kappa(s)$-linear maps. Let $B$ be the image of $\mathcal O\otimes_{\mathbf Z}\kappa(s)$ in $\operatorname{End}_{\kappa(s)}(V)$. It is a commutative $\kappa(s)$-algebra of finite dimension, $V$ is a $B$-module, and $V\otimes_{\mathcal O}M\simeq V\otimes_B M_B$ with $M_B=B\otimes_{\mathcal O}M$ finitely generated projective of constant rank $r$ over $B$. A finite-dimensional commutative algebra over a field is artinian, hence a finite product $B=\prod_iB_i$ of artinian local rings; a finitely generated projective module of constant rank $r$ over a local ring is free of rank $r$, so $M_B=\prod_iM_i$ with $M_i\simeq B_i^r$. Decomposing $V=\bigoplus_iV_i$ accordingly gives

$$
V\otimes_BM_B=\bigoplus_iV_i\otimes_{B_i}B_i^{\,r}\simeq\bigoplus_iV_i^{\,r},
$$

of dimension $r\dim_{\kappa(s)}V=rg$. $\square$

Because the functor (5.6) is defined without reference to a presentation, Yoneda makes the abelian scheme $A\otimes_{\mathcal O}M$ independent of every choice: two presentations produce two schemes representing the same functor, hence a unique isomorphism between them compatible with the identifications of the functors. This is worth emphasizing, since the idempotent is highly non-unique while its geometric output is not.

**Proposition 5.4 (functoriality).** The construction $M\mapsto A\otimes_{\mathcal O}M$ is an additive functor from finitely generated projective $\mathcal O$-modules to abelian schemes over $S$ with $\mathcal O$-action: an $\mathcal O$-linear map $u:M\to M'$ induces a homomorphism $A\otimes u$, compatibly with composition, and

$$
A\otimes_{\mathcal O}\mathcal O\simeq A,\qquad
A\otimes_{\mathcal O}(M\oplus M')\simeq(A\otimes_{\mathcal O}M)\times_S(A\otimes_{\mathcal O}M').
$$

Moreover an $\mathcal O$-equivariant homomorphism $f:A\to B$ of abelian schemes with $\mathcal O$-action induces $f\otimes M:A\otimes_{\mathcal O}M\to B\otimes_{\mathcal O}M$, and all of this commutes with arbitrary base change.

**Proof.** Each assertion is a statement about the functors of points, where it is the corresponding elementary property of $\otimes_{\mathcal O}$: $u$ induces $A(T)\otimes M\to A(T)\otimes M'$ naturally in $T$, tensoring commutes with finite direct sums, $A(T)\otimes\mathcal O=A(T)$, and $f(T)$ is $\mathcal O$-linear. Yoneda converts natural transformations of representable functors into morphisms of schemes, and these are homomorphisms because they are additive on points. Base-change compatibility is Theorem 5.3 together with the fact that all identifications were made on points. $\square$

The duality statement requires one preliminary that is used nowhere else in this book and deserves to be isolated.

**Lemma 5.5 (additivity of duality).** For abelian schemes $A,B$ over $S$ the map $\operatorname{Hom}_S(A,B)\to\operatorname{Hom}_S(B^\vee,A^\vee)$, $f\mapsto f^\vee$, is additive. Under the canonical identification $(A^n)^\vee\simeq(A^\vee)^n$ of Section 3.5, the dual of an endomorphism of $A^n$ given by a matrix $(f_{ij})$ is the endomorphism of $(A^\vee)^n$ given by the transposed matrix $(f_{ji}^\vee)$.

**Proof.** Let $M$ be a rigidified algebraically trivial bundle on $B$, that is, a point of $B^\vee$. The biextension law (3.1), pulled back along $(f,g):A\to B\times_SB$, gives $(f+g)^*M\simeq f^*M\otimes g^*M$ compatibly with rigidifications, since $f+g=m_B\circ(f,g)$. As $f^\vee$ is by definition pullback of such bundles and the group law of $A^\vee$ is tensor product, this says exactly $(f+g)^\vee=f^\vee+g^\vee$. For the matrix statement, write $\varepsilon=\sum_{i,j}\mathrm{in}_i\circ f_{ij}\circ\mathrm{pr}_j$ and dualize; additivity converts the sum into a sum, and the identification of Section 3.5 exchanges $\mathrm{pr}_j^\vee$ with $\mathrm{in}_j$ and $\mathrm{in}_i^\vee$ with $\mathrm{pr}_i$, because a rigidified algebraically trivial bundle on a product is the tensor product of its restrictions. The result is $\sum_{i,j}\mathrm{in}_j\circ f_{ij}^\vee\circ\mathrm{pr}_i$. $\square$

Now let $M^\vee=\operatorname{Hom}_{\mathcal O}(M,\mathcal O)$, again finitely generated projective, of constant rank $r$ if $M$ has constant rank $r$, with $M^{\vee\vee}=M$. Since $\mathcal O$ is commutative, $a\mapsto\iota(a)^\vee$ is a ring homomorphism $\mathcal O\to\operatorname{End}_S(A^\vee)$, so $A^\vee$ carries an $\mathcal O$-action and $A^\vee\otimes_{\mathcal O}M^\vee$ is defined.

**Theorem 5.6 (duality).** There is an isomorphism of abelian schemes with $\mathcal O$-action

$$
\Phi_M:A^\vee\otimes_{\mathcal O}M^\vee\xrightarrow{\ \sim\ }(A\otimes_{\mathcal O}M)^\vee,
$$

natural in $M$ and in $A$, and compatible with arbitrary base change.

**Proof strategy.** We first write down a canonical map, without choosing a presentation, out of nothing but the functoriality of Proposition 5.4 and of duality. Then we check that it is an isomorphism, and for that a presentation may be chosen, because the map is additive in $M$ and is the identity for $M=\mathcal O$.

**Proof.** For $\varphi\in M^\vee$ Proposition 5.4 gives a homomorphism $A\otimes\varphi:A\otimes_{\mathcal O}M\to A\otimes_{\mathcal O}\mathcal O=A$, whose dual is a homomorphism $A^\vee\to(A\otimes_{\mathcal O}M)^\vee$. Sending a pair $(y,\varphi)$ with $y\in A^\vee(T)$ to $(A\otimes\varphi)^\vee(y)$ is additive in each variable, and it is $\mathcal O$-balanced: for $a\in\mathcal O$ the map $A\otimes(a\varphi)$ equals $\iota(a)\circ(A\otimes\varphi)$, so its dual is $(A\otimes\varphi)^\vee\circ\iota(a)^\vee$, which sends $y$ to the image of $\iota(a)^\vee y$. Hence the assignment factors through $A^\vee(T)\otimes_{\mathcal O}M^\vee$ and defines a natural transformation $\Phi_M$, which is a homomorphism of abelian schemes by Yoneda. It is natural in $M$: for $u:M\to M'$ one has $A\otimes(\varphi\circ u)=(A\otimes\varphi)\circ(A\otimes u)$, and dualizing gives the required commuting square with $(A\otimes u)^\vee$.

For $M=\mathcal O$ we have $M^\vee=\mathcal O$ and $\varphi=\operatorname{id}$ corresponds to $A\otimes\varphi=\operatorname{id}_A$, so $\Phi_{\mathcal O}$ is the identity of $A^\vee$. Naturality applied to the inclusions and projections of a direct sum, together with the product decompositions of Proposition 5.4 and $(M\oplus N)^\vee=M^\vee\oplus N^\vee$, identifies $\Phi_{M\oplus N}$ with $\Phi_M\times\Phi_N$. Choosing $N$ with $M\oplus N\simeq\mathcal O^n$, the map $\Phi_M\times\Phi_N=\Phi_{\mathcal O^n}$ is an isomorphism, hence so is each factor: a factor of an isomorphism of products is an isomorphism, since it is a retract of one. Naturality in $A$ and compatibility with base change hold because every ingredient — the functor $A\otimes_{\mathcal O}(-)$, duality, and the identifications above — has those properties. $\square$

It is instructive to see the same isomorphism through the idempotent. With $\varepsilon=j\pi$ and $\pi j=\operatorname{id}$ as in the proof of Theorem 5.3, dualizing gives $\varepsilon^\vee=\pi^\vee j^\vee$ with $j^\vee\pi^\vee=\operatorname{id}$, so $\pi^\vee$ identifies $(A\otimes_{\mathcal O}M)^\vee$ with $\ker(1-\varepsilon^\vee)$. By Lemma 5.5, $\varepsilon^\vee$ is the endomorphism of $(A^\vee)^n$ attached to the transposed idempotent $e^{\mathrm t}\in M_n(\mathcal O)$, and the transpose of a projector onto $M$ is a projector onto $M^\vee$, because applying $\operatorname{Hom}_{\mathcal O}(-,\mathcal O)$ to $\mathcal O^n=M\oplus N$ gives $\mathcal O^n=M^\vee\oplus N^\vee$. So the dual is $A^\vee\otimes_{\mathcal O}M^\vee$, computed with the transposed presentation. The presentation-free argument was given first only because it produces a canonical map rather than a family of comparisons.

Return to the arithmetic example. If $\mathcal O=\mathcal O_F$ acts on $A$ and $\mathfrak a,\mathfrak b$ are fractional ideals, then $\mathfrak a$ is projective of rank one, so $A\otimes\mathfrak a$ has the same relative dimension $g$ as $A$; the multiplication isomorphism $\mathfrak a\otimes_{\mathcal O_F}\mathfrak b\simeq\mathfrak a\mathfrak b$ and Proposition 5.4 give $(A\otimes\mathfrak a)\otimes\mathfrak b\simeq A\otimes\mathfrak a\mathfrak b$; and $\mathfrak c^\vee\simeq\mathfrak c^{-1}$, so Theorem 5.6 reads

$$
(A\otimes_{\mathcal O_F}\mathfrak c)^\vee\simeq A^\vee\otimes_{\mathcal O_F}\mathfrak c^{-1}.
$$

A homomorphism $\lambda:A\otimes_{\mathcal O_F}\mathfrak c\to A^\vee$ is therefore self-dual in the sense appropriate to this setting when its dual, an arrow $A\to A^\vee\otimes\mathfrak c^{-1}$, agrees with $\lambda$ after tensoring by $\mathfrak c$ and using biduality. Nothing here depends on the class of $\mathfrak c$ being trivial, which is exactly why the construction is needed: an ideal class that is not principal cannot be absorbed by an isomorphism $A\otimes\mathfrak c\simeq A$.

Finally, commutativity of $\mathcal O$ entered only in the bookkeeping of sides. For an arbitrary associative unital ring $\mathcal O$, the homomorphism $\iota$ makes each $A(T)$ a left $\mathcal O$-module; if $M$ is a finitely generated projective right $\mathcal O$-module, then $M\oplus N\simeq\mathcal O^n$ as right modules, $\operatorname{End}_{\mathcal O}(\mathcal O^n)=M_n(\mathcal O)$ acting on the left, and the projector onto $M$ is again an idempotent matrix. Lemma 5.2 and Theorem 5.3 hold verbatim for the functor $T\mapsto M\otimes_{\mathcal O}A(T)$, and Proposition 5.4 holds with $M$ varying among right modules. Only the duality statement needs the sides changed, since $\operatorname{Hom}_{\mathcal O}(M,\mathcal O)$ is then a left module and the dual abelian scheme carries the opposite action. All uses in this book have $\mathcal O$ commutative, and the statements above are phrased for that case.

## 6. Kernels and duality

Duality reverses an isogeny because a line bundle on the quotient becomes trivial after pullback precisely when its descent datum is a character of the kernel. This converts geometric descent into Cartier duality and is the conceptual source of the Weil pairing.

### 6.1 The character hidden in a trivialized pullback

Let $q:A\to B=A/H$. A $T$-point of $\ker(q^\vee)$ is represented by a rigidified algebraically trivial bundle $M$ on $B_T$ together with the assertion that $q_T^*M$ is trivial as a rigidified bundle. Choose such a trivialization fppf-locally on $T$.

For $h\in H(T')$, translation by $h$ preserves $q^*M$. Comparing the chosen trivialization with its translate gives a unit $\chi(h)\in\mathbf G_m(T')$. Compatibility for two translations gives

$$
\chi(h+h')=\chi(h)\chi(h').
$$

Thus $\chi:H_{T'}\to\mathbf G_m$ is a character. Changing the trivialization by a unit from $T'$ changes neither comparison nor character.

Conversely, a character $\chi$ twists the canonical $H$-linearization of the trivial bundle on $A_T$. Faithfully flat descent along the $H$-torsor $q$ produces a rigidified line bundle $M_\chi$ on $B_T$ whose pullback is trivial. The descended bundle is algebraically trivial because its pullback along a finite surjective map is numerically trivial, and numerical triviality is equivalent to algebraic triviality on geometric abelian fibers.

These operations are inverse, functorial in $T$, and compatible with base change.

### 6.2 Kernel of the dual isogeny

**Theorem 6.1.** For an isogeny $f:A\to B$ with kernel $H$, the dual map is an isogeny and there is a canonical isomorphism

$$
\ker(f^\vee)\simeq H^D. \tag{6.1}
$$

In particular $\deg(f^\vee)=\deg(f)$.

**Proof.** Replace $B$ by $A/H$ using the quotient theorem. Section 6.1 identifies the functor of points of $\ker(f^\vee)$ with the character functor of $H$, which is represented by $H^D$. Thus (6.1) is an isomorphism of finite locally free group schemes. The dimensions of $A^\vee$ and $B^\vee$ agree, and a homomorphism with finite locally free kernel and full-dimensional image is an isogeny. Cartier duality preserves rank, so the degrees agree. $\square$

The evaluation pairing becomes a canonical perfect pairing

$$
\ker f\times_S\ker f^\vee\longrightarrow\mathbf G_m. \tag{6.2}
$$

This statement is schematic. In characteristic $p$, both sides can have far fewer geometric points than their common order.

Taking $f=[n]_A$ gives $A[n]^D\simeq A^\vee[n]$. Taking a quotient $q:A\to A/H$ shows that the dual quotient has kernel $H^D$. Constant and multiplicative kernels are therefore interchanged. For example, if an elliptic $p$-isogeny in characteristic $p$ has kernel $\mu_p$, the dual isogeny has constant etale kernel $\underline{\mathbf Z/p\mathbf Z}$; if the original kernel is $\alpha_p$, its dual kernel is again $\alpha_p$. This distinction is invisible if one records only geometric kernel points.

### 6.3 Annihilators and exact sequences

Suppose $H\subseteq A[n]$ is finite locally free. Under the perfect pairing between $A[n]$ and $A^\vee[n]$ constructed in Chapter 7, define

$$
H^\perp=\ker\bigl(A^\vee[n]\longrightarrow H^D\bigr). \tag{6.3}
$$

Cartier exactness gives

$$
0\longrightarrow H^\perp\longrightarrow A^\vee[n]
\longrightarrow H^D\longrightarrow0, \tag{6.4}
$$

and hence

$$
|H^\perp|=\frac{n^{2g}}{|H|},
\qquad (H^\perp)^\perp=H. \tag{6.5}
$$

These are rank identities, not point counts. If $q:A\to B=A/H$ and $H\subseteq A[n]$, the multiplication-by-$n$ diagram for

$$
0\longrightarrow H^D\longrightarrow B^\vee
\xrightarrow{q^\vee}A^\vee\longrightarrow0
$$

gives the precise torsion sequence

$$
0\longrightarrow H^D\longrightarrow B^\vee[n]
\xrightarrow{q^\vee}H^\perp\longrightarrow0. \tag{6.6a}
$$

The last term is the kernel of the connecting map $A^\vee[n]\to H^D$, which is evaluation on $H$ and hence is exactly the annihilator (6.3). More generally, dualizing a finite-flat exact sequence reverses it.

### 6.4 The dual-isogeny identities

Let $f:A\to B$ have degree $d$. Since $H=\ker f$ is killed by its order $d$, multiplication $[d]_A$ is zero on $H$. The universal property of $A/H$ gives a unique homomorphism

$$
f':B\longrightarrow A
$$

such that

$$
f'f=[d]_A. \tag{6.6}
$$

Because $f$ is faithfully flat, composing and comparing after $f$ gives

$$
ff'=[d]_B. \tag{6.7}
$$

The integer $d$ is a uniform but not always minimal choice; the exponent of $H$ suffices. Dualizing (6.6)--(6.7) gives the corresponding identities for $f^\vee$. These formulas show directly that an isogeny becomes invertible after tensoring the Hom group with $\mathbf Q$.

For elliptic curves, a sharper normalization is customary: there is a unique dual isogeny $\widehat f:B\to A$ with

$$
\widehat f f=[d]_A,
\qquad f\widehat f=[d]_B,
$$

and under the canonical principal polarizations it is precisely $f^\vee$. In higher dimension the same notation requires chosen polarizations to identify each scheme with its dual.

## 7. Weil pairings

The finite kernel pairing (6.2) becomes especially useful for multiplication. It packages the cyclotomic twist, duality of torsion, and symplectic linear algebra in a form valid before taking geometric points.

### 7.1 Construction from the Poincare bundle

Restrict the Poincare bundle to $A[n]\times A^\vee[n]$. Its biextension law says that it is multiplicative in each variable. Since both variables are killed by $n$, the biextension commutator has $n$th power one. It therefore defines

$$
e_n:A[n]\times_SA^\vee[n]\longrightarrow\mu_n, \tag{7.1}
$$

the **Weil pairing**.

Concretely, a point $y\in A^\vee[n](T)$ is a rigidified algebraically trivial bundle $M_y$ whose $n$th tensor power is trivial in the Picard group. Along $x\in A[n](T)$, compare the two orders of applying the translation trivialization by $x$ and the $n$-fold tensor trivialization. Their ratio is a unit. Reversing either operation shows its $n$th power is $1$. Changes of local trivialization cancel in the commutator, so the unit descends. The universal version is (7.1).

There is a complementary divisor description over a field. Choose rational functions whose divisors are $n(P)-n(0)$ and $n(Q)-n(0)$ after translating representatives to have disjoint support. Comparing the value of the first function along the divisor of the second with the reverse comparison gives a root of unity; Weil reciprocity proves independence of all auxiliary choices. This is the classical commutator formula. The Poincare construction is preferable in families because it requires neither disjoint divisors nor rational functions and therefore survives nonreduced torsion.

### 7.2 Bilinearity, functoriality, and base change

The two biextension laws immediately give

$$
e_n(x+x',y)=e_n(x,y)e_n(x',y),
\qquad
e_n(x,y+y')=e_n(x,y)e_n(x,y'). \tag{7.2}
$$

For a homomorphism $f:A\to B$ and its dual $f^\vee:B^\vee\to A^\vee$,

$$
e_n^B(fx,y)=e_n^A(x,f^\vee y). \tag{7.3}
$$

Indeed $(f\times1)^*\mathcal P_B$ and $(1\times f^\vee)^*\mathcal P_A$ represent the same family of pulled-back line bundles and have the same rigidifications, so universality identifies them. Their commutators agree.

All constructions in (7.1)--(7.3) commute with arbitrary base change. In particular, the formula does not require $n$ to be invertible.

### 7.3 Perfectness in every characteristic

**Theorem 7.1.** The Weil pairing is perfect. Equivalently, its adjoint is a canonical isomorphism

$$
A^\vee[n]\xrightarrow{\sim}A[n]^D. \tag{7.4}
$$

**Proof.** Apply Theorem 6.1 to $[n]_A$. Its dual is $[n]_{A^\vee}$, so

$$
(\ker[n]_A)^D\simeq\ker[n]_{A^\vee}.
$$

Under the character construction of Section 6.1, evaluation is exactly the Poincare commutator used in Section 7.1. Thus the displayed isomorphism is the adjoint of $e_n$. $\square$

When $n$ is divisible by a residue characteristic, “perfect” cannot be tested on geometric points. For example, $\mu_p$ has only one geometric point over an algebraically closed field of characteristic $p$, yet its Cartier pairing with the constant group of order $p$ is perfect. The same schematic discipline is essential for abelian $p$-torsion.

### 7.4 Compatibility through levels

If $m,n\ge1$, $x\in A[mn]$, and $y\in A^\vee[mn]$, bilinearity and functoriality of the Poincare bundle give

$$
e_{mn}(x,y)^m=e_n(mx,my). \tag{7.5}
$$

Equivalently, the pairings commute with transition maps in the inverse systems of prime-power torsion. If a prime $\ell$ is invertible on $S$, passing to inverse limits on geometric fibers yields a perfect pairing

$$
T_\ell A\times T_\ell A^\vee\longrightarrow\mathbf Z_\ell(1). \tag{7.6}
$$

The Tate twist appears because the finite target is $\mu_{\ell^r}$, not a canonically constant cyclic group.

### 7.5 The prime-to-characteristic pointwise picture

Over a field $k$ with $n$ invertible, $A[n]$ is finite etale and

$$
A[n](k^s)\simeq(\mathbf Z/n\mathbf Z)^{2g}.
$$

The pairing (7.1) becomes a perfect Galois-equivariant pairing of finite modules. After a principal polarization it is alternating and symplectic. If $g=1$ and $P,Q$ is a symplectic basis, then

$$
e_n(\sigma P,\sigma Q)
=e_n(P,Q)^{\det\rho_n(\sigma)}
=e_n(P,Q)^{\chi_n(\sigma)},
$$

so $\det\rho_n=\chi_n$. This familiar pointwise result is a shadow of the group-scheme pairing, not its definition.

For an elliptic scheme with its canonical principal polarization, alternation can also be seen directly. A bundle corresponding to $Q\in E[n]$ has divisor class $(Q)-(0)$. Interchanging $P$ and $Q$ reverses the translation commutator, while setting $P=Q$ makes the two orders identical. If $n$ is invertible, any point $P$ of exact order $n$ admits $Q$ for which $e_n(P,Q)$ is primitive; otherwise $P$ would lie in the radical. In residue characteristic, the corresponding statement is the existence of a character fppf-locally, not necessarily a second geometric point.

### 7.6 Prime-adic Tate modules

Section 7.4 observed that the torsion groups $A[\ell^m]$ form an inverse system and that the Weil pairings are compatible along it. Section 7.5 computed each level over a separably closed field. What is still missing is the object that assembles all levels at once. The reason for wanting it is not economy of notation. A single finite level records a representation of automorphisms or of a Galois group with coefficients in $\mathbf Z/\ell^m\mathbf Z$, and such representations cannot be compared across levels or have characteristic polynomials with integer coefficients. The inverse limit turns the whole tower into one free module of rank $2g$ over a principal ideal domain of characteristic zero, and thereby converts arithmetic questions about torsion into linear algebra over $\mathbf Z_\ell$. The polarization-locus lemma of Section 10.5 already uses this language, and later theories of monodromy and of endomorphism algebras are unusable without it.

Throughout this section $k$ is a separably closed field, $\ell$ a prime invertible in $k$, and $A/k$ an abelian variety of dimension $g$. Nothing is lost by allowing $k$ merely separably closed rather than algebraically closed, because everything in sight is finite étale.

We begin by recording the two facts about the tower that make the limit tractable. Both were established above; we recall the arguments because they are what the limit argument consumes.

First, each level is free of the expected rank:

$$
A[\ell^m](k)\simeq(\mathbf Z/\ell^m\mathbf Z)^{2g}. \tag{7.7}
$$

Indeed $A[\ell^m]$ is finite étale of order $\ell^{2mg}$ by Theorem 4.2, and a finite étale scheme over a separably closed field is a disjoint union of copies of $\operatorname{Spec}k$, so $A[\ell^m](k)$ is an abelian group of order $\ell^{2mg}$ killed by $\ell^m$. The same statement at level $j\le m$ says that its subgroup of $\ell^j$-torsion has order $\ell^{2jg}$. Writing the group as $\bigoplus_i\mathbf Z/\ell^{a_i}\mathbf Z$ with $a_i\le m$, the $\ell$-torsion subgroup has order $\ell^{\#\{i\}}$, so there are exactly $2g$ summands, and comparing total orders forces every $a_i=m$. This is (7.7).

Second, the transition maps are surjective. The transition map from level $m+1$ to level $m$ is multiplication by $\ell$, and it is surjective on $k$-points: given $x\in A[\ell^m](k)$, the fiber $[\ell]^{-1}(x)$ is a nonempty finite étale $k$-scheme, because $[\ell]$ is a finite étale surjective isogeny when $\ell$ is invertible, and therefore has a $k$-point $y$; then $\ell^{m+1}y=\ell^m x=0$. This is the divisibility of $A(k)$ in the only form we need.

**Definition.** The **$\ell$-adic Tate module** of $A$ is

$$
T_\ell A=\varprojlim_mA[\ell^m](k),
$$

the limit taken along multiplication by $\ell$.

Each $A[\ell^m](k)$ is a module over $\mathbf Z/\ell^m\mathbf Z$, the transition maps are compatible with the ring maps $\mathbf Z/\ell^{m+1}\mathbf Z\to\mathbf Z/\ell^m\mathbf Z$, and so the limit is a module over $\mathbf Z_\ell=\varprojlim\mathbf Z/\ell^m\mathbf Z$. The content of the following lemma is that no information is lost or created in the limit; it is the abstract statement behind every appearance of the Tate module.

**Lemma 7.2 (limits of free modules).** Let $(M_m)_{m\ge1}$ be an inverse system of abelian groups such that $M_m$ is a free $\mathbf Z/\ell^m\mathbf Z$-module of rank $r$, the transition map $\pi_m:M_{m+1}\to M_m$ is surjective and additive, and $\pi_m$ is semilinear over $\mathbf Z/\ell^{m+1}\mathbf Z\to\mathbf Z/\ell^m\mathbf Z$. Then $T=\varprojlim M_m$ is a free $\mathbf Z_\ell$-module of rank $r$, and for every $m$ the projection $T\to M_m$ is surjective with kernel $\ell^mT$, so that $T/\ell^mT\simeq M_m$.

**Proof strategy.** One constructs a basis of $T$ by choosing bases at each level that are compatible with the transitions. The engine is Nakayama's lemma over the local ring $\mathbf Z/\ell^{m}\mathbf Z$, in which $\ell$ is nilpotent, so that generation may be tested modulo $\ell$.

**Proof.** First identify the kernels. Since $\ell^mM_{m+1}$ is killed by $\pi_m$, being carried into $\ell^mM_m=0$, and since $|\ker\pi_m|=\ell^{r(m+1)}/\ell^{rm}=\ell^r=|\ell^mM_{m+1}|$, we get $\ker\pi_m=\ell^mM_{m+1}$ and hence $M_m\simeq M_{m+1}/\ell^mM_{m+1}$.

Now construct compatible bases by induction. Choose any basis $e^{(1)}_1,\dots,e^{(1)}_r$ of the $r$-dimensional $\mathbf F_\ell$-vector space $M_1$. Given a basis $e^{(m)}_1,\dots,e^{(m)}_r$ of $M_m$, lift each $e^{(m)}_i$ through the surjection $\pi_m$ to some $x_i\in M_{m+1}$. Reducing modulo $\ell$ and using $M_{m+1}/\ell M_{m+1}\simeq M_m/\ell M_m$, the images of the $x_i$ form a basis of the $r$-dimensional $\mathbf F_\ell$-vector space $M_{m+1}/\ell M_{m+1}$. As $\ell$ is nilpotent in $\mathbf Z/\ell^{m+1}\mathbf Z$, Nakayama's lemma makes $x_1,\dots,x_r$ generate $M_{m+1}$; the resulting surjection $(\mathbf Z/\ell^{m+1}\mathbf Z)^r\to M_{m+1}$ is a surjection between finite sets of the same cardinality $\ell^{r(m+1)}$, hence bijective. So the $x_i$ form a basis, and we set $e^{(m+1)}_i=x_i$.

Define $\phi:\mathbf Z_\ell^r\to T$ by sending the $i$-th standard vector to the compatible system $(e^{(m)}_i)_m$; this is $\mathbf Z_\ell$-linear. If $\phi(a_1,\dots,a_r)=0$ then at each level $\sum_ia_i^{(m)}e^{(m)}_i=0$ with $a_i^{(m)}=a_i\bmod\ell^m$, so freeness gives $a_i\equiv0$ modulo $\ell^m$ for every $m$, whence $a_i=0$. Conversely let $t=(t_m)\in T$ and write $t_m=\sum_ic_{i,m}e^{(m)}_i$ with unique $c_{i,m}\in\mathbf Z/\ell^m\mathbf Z$. Applying $\pi_m$ to $t_{m+1}=t_m$ and using $\pi_m(e^{(m+1)}_i)=e^{(m)}_i$ gives $c_{i,m+1}\equiv c_{i,m}$ modulo $\ell^m$, so the $c_{i,m}$ define $a_i\in\mathbf Z_\ell$ with $\phi(a)=t$. Thus $\phi$ is an isomorphism.

Finally, under $\phi$ the projection $T\to M_m$ becomes the reduction $\mathbf Z_\ell^r\to(\mathbf Z/\ell^m\mathbf Z)^r$, which is surjective with kernel $\ell^m\mathbf Z_\ell^r$. $\square$

**Theorem 7.3.** For $A/k$ of dimension $g$ with $\ell$ invertible in $k$, the Tate module $T_\ell A$ is a free $\mathbf Z_\ell$-module of rank $2g$, and $T_\ell A/\ell^mT_\ell A\simeq A[\ell^m](k)$ for every $m$. The construction is a functor: a homomorphism $f:A\to B$ induces a $\mathbf Z_\ell$-linear map $T_\ell f$, with $T_\ell(fg)=T_\ell(f)T_\ell(g)$, $T_\ell([n])=n$, and $T_\ell(A\times B)=T_\ell A\oplus T_\ell B$. In particular an automorphism of $A$ acts on $T_\ell A$ through $\operatorname{GL}_{2g}(\mathbf Z_\ell)$ once a basis is fixed.

**Proof.** The system $M_m=A[\ell^m](k)$ satisfies the requirements of Lemma 7.2 with $r=2g$ by (7.7) and the surjectivity established above, so the first two assertions follow. A homomorphism $f$ commutes with multiplication by $\ell$ and therefore maps $A[\ell^m]$ to $B[\ell^m]$ compatibly with the transition maps; passing to the limit gives $T_\ell f$, which is $\mathbf Z_\ell$-linear because it is additive and compatible with the $\mathbf Z/\ell^m\mathbf Z$-structures. Functoriality and the values on $[n]$ and on products are inherited level by level. An automorphism thus acts by a $\mathbf Z_\ell$-linear automorphism of a free module of rank $2g$. $\square$

If $k_0$ is any field with $\ell$ invertible and $k=k_0^s$, then $\operatorname{Gal}(k_0^s/k_0)$ acts on each $A[\ell^m](k)$ compatibly with the transitions, hence acts $\mathbf Z_\ell$-linearly on $T_\ell A$, giving a representation $\rho_\ell:\operatorname{Gal}(k_0^s/k_0)\to\operatorname{GL}_{2g}(\mathbf Z_\ell)$ whose reduction modulo $\ell^m$ is the action on $A[\ell^m](k)$. The same applies to any group of automorphisms of $A$ defined over $k_0$, since the construction is functorial.

It remains to record what happens to the pairing. Let

$$
\mathbf Z_\ell(1)=\varprojlim_m\mu_{\ell^m}(k),
$$

the limit along $\zeta\mapsto\zeta^\ell$. Each $\mu_{\ell^m}(k)$ is cyclic of order $\ell^m$, since $\mu_{\ell^m}$ is finite étale of order $\ell^m$ over the separably closed $k$; and the transition maps are surjective because $X^\ell-\zeta$ is a separable polynomial over $k$. So Lemma 7.2 with $r=1$ makes $\mathbf Z_\ell(1)$ a free $\mathbf Z_\ell$-module of rank one. It is not canonically $\mathbf Z_\ell$: a generator is a compatible system of primitive $\ell^m$-th roots of unity, and no such system is preferred. This is the Tate twist already flagged after display (7.6).

**Proposition 7.4.** The Weil pairings induce a $\mathbf Z_\ell$-bilinear pairing

$$
e:T_\ell A\times T_\ell A^\vee\longrightarrow\mathbf Z_\ell(1)
$$

which is perfect: its adjoint $T_\ell A^\vee\to\operatorname{Hom}_{\mathbf Z_\ell}(T_\ell A,\mathbf Z_\ell(1))$ is an isomorphism of free $\mathbf Z_\ell$-modules of rank $2g$. It is functorial in $A$ in the sense of (7.3), and equivariant for automorphisms and for Galois when $k$ is a separable closure.

**Proof.** Compatibility through levels, display (7.5), says $e_{\ell^{m+1}}(x,y)^\ell=e_{\ell^m}(\ell x,\ell y)$, which is exactly the statement that the pairings $e_{\ell^m}$ on $k$-points are compatible with the transition maps of the three inverse systems. Hence they define $e$ on the limits, and bilinearity passes to the limit.

For perfectness, fix $m$. Theorem 7.1 gives an isomorphism $A^\vee[\ell^m]\simeq A[\ell^m]^D$ of finite group schemes; taking $k$-points over the separably closed $k$, where both sides are finite étale hence constant, identifies $A^\vee[\ell^m](k)$ with the group of homomorphisms $A[\ell^m](k)\to\mu_{\ell^m}(k)$, the adjoint of $e_{\ell^m}$ being this identification. Now compute the target of the limit adjoint. Since $T_\ell A$ is free of rank $2g$ with $T_\ell A/\ell^m\simeq A[\ell^m](k)$ and $\mathbf Z_\ell(1)$ is free of rank one with $\mathbf Z_\ell(1)/\ell^m\simeq\mu_{\ell^m}(k)$,

$$
\operatorname{Hom}_{\mathbf Z_\ell}(T_\ell A,\mathbf Z_\ell(1))
\simeq\varprojlim_m\operatorname{Hom}(T_\ell A/\ell^m,\mathbf Z_\ell(1)/\ell^m)
\simeq\varprojlim_m\operatorname{Hom}\bigl(A[\ell^m](k),\mu_{\ell^m}(k)\bigr),
$$

the first isomorphism because a homomorphism into a module that is the limit of its own reductions is the same as a compatible system of homomorphisms of the reductions. Under these identifications the limit adjoint is the limit of the level adjoints, each an isomorphism, hence an isomorphism. Functoriality and equivariance hold at each level and therefore in the limit. $\square$

If $\lambda:A\to A^\vee$ is a polarization, composing with $T_\ell\lambda$ gives a pairing $e^\lambda$ on $T_\ell A$; it is alternating at every level by the identity (8.7) proved in the next chapter, and it is perfect precisely when the level pairings are, which the criterion of Section 8.5 will identify as the condition that $\lambda$ have degree prime to $\ell$. A principal polarization always gives a perfect alternating form. Choosing a basis of $T_\ell A$ and a generator of $\mathbf Z_\ell(1)$ then exhibits the automorphisms preserving $\lambda$ as a subgroup of the symplectic similitude group over $\mathbf Z_\ell$. For $g=1$ and the canonical principal polarization of an elliptic curve, the module $T_\ell E$ is free of rank two, an automorphism acts through $\operatorname{GL}_2(\mathbf Z_\ell)$, and the determinant of a Galois element is the $\ell$-adic cyclotomic character, since that identity holds at every finite level by Section 7.5.

A caution closes the section. Everything above required $\ell$ to be invertible. In residue characteristic the groups $A[p^m]$ have too few geometric points, their inverse limit is not free of rank $2g$, and the correct replacement is a limit of group schemes rather than of point groups. The pointwise Tate module is the right object exactly in the range where torsion is étale.

## 8. Polarizations

An abelian scheme is projective, but projectivity alone does not choose a geometry on its torsion. A polarization is the extra positive self-duality that turns the canonical pairing between $A$ and $A^\vee$ into a bilinear form on $A$ itself.

### 8.1 From an ample line bundle to a homomorphism

For a line bundle $L$ define

$$
\lambda_L:A\longrightarrow A^\vee,
\qquad a\longmapsto t_a^*L\otimes L^{-1}. \tag{8.1}
$$

The square theorem proves that this is a homomorphism. Tensor products and pullbacks satisfy

$$
\lambda_{L\otimes M}=\lambda_L+\lambda_M,
\qquad
\lambda_{f^*L}=f^\vee\lambda_Lf. \tag{8.2}
$$

If $L$ is algebraically trivial then $\lambda_L=0$; conversely, a rigidified $L$ with $\lambda_L=0$ is algebraically trivial. Thus (8.1) factors through the Neron--Severi group, the quotient of line-bundle classes by algebraic equivalence.

If $L$ is relatively ample, $\lambda_L$ is an isogeny. Fiberwise, its kernel is the translation stabilizer of $L$. A positive-dimensional stabilizer would make $L$ numerically trivial on that subgroup, contradicting ampleness. The image has dimension $g$, hence is all of $A^\vee$; Proposition 4.1 supplies flatness over the base.

### 8.2 Intrinsic characterization

A **polarization** of $A/S$ is a homomorphism $\lambda:A\to A^\vee$ such that fppf locally on $S$ it equals $\lambda_L$ for a relatively ample line bundle $L$. It is **principal** if it is an isomorphism.

The local wording is deliberate. A polarization homomorphism may be globally defined even when no single global ample bundle induces it; the obstruction is a descent class. Positivity is nevertheless fppf-local, while the homomorphism is genuine global data.

**Proposition 8.1.** A homomorphism $\lambda:A\to A^\vee$ is a polarization if and only if:

1. $\lambda$ is symmetric, meaning $\lambda^\vee\delta_A=\lambda$; and
2. on every geometric fiber there is an ample bundle $L_s$ with $\lambda_s=\lambda_{L_s}$.

It suffices to check condition 2 on one geometric fiber of every connected component.

**Proof.** A bundle-induced map is symmetric by the cube theorem: the two pullbacks of the Poincare bundle representing $\lambda_L$ and its transpose have the same normalized cubical structure. Positivity persists under base change.

Conversely, the biextension descent theorem identifies symmetric homomorphisms fppf-locally with maps $\lambda_L$. Indeed, pull $\mathcal P_A$ back along $1\times\lambda$ to obtain a biextension on $A\times A$. Symmetry identifies it with its transpose; the two biextension laws supply a cubical descent datum along the diagonal. After an fppf cover that trivializes the residual line bundle from the base, this datum is the square construction of a rigidified $L$ and gives $\lambda_L=\lambda$. Once one inducing bundle $L_0$ is chosen, every other differs from it by an algebraically trivial bundle and a pullback from the base; if symmetric rigidifications are required, the remaining ambiguity is a torsor under $A^\vee[2]$.

Choose such a local $L$. Fiberwise ampleness is open in a proper finitely presented family. On an abelian scheme the numerical class of $L$ is locally constant, because intersection numbers with translation-invariant cycles and the associated isogeny degree are locally constant. If $L$ is ample on one fiber of a connected component, the Nakai criterion on abelian fibers makes it ample on every fiber, hence relatively ample. This proves the local characterization. $\square$

### 8.3 Symmetry, type, and degree

Over an algebraically closed field, the kernel of a polarization has square order. If the characteristic of the field does not divide the degree, there are unique integers

$$
d_1\mid d_2\mid\cdots\mid d_g
$$

such that

$$
\ker\lambda(\bar k)\simeq
\prod_{i=1}^g(\mathbf Z/d_i\mathbf Z)^2. \tag{8.3}
$$

The tuple $(d_1,\ldots,d_g)$ is the **type**, and

$$
\deg\lambda=(d_1\cdots d_g)^2. \tag{8.4}
$$

In arbitrary characteristic, (8.4) remains the rank formula but (8.3) must be replaced by the finite-flat kernel and its perfect alternating commutator pairing. The elementary-divisor description is valid on the prime-to-characteristic etale part; connected primary factors require group schemes rather than point modules.

For an ample $L$ on a geometric fiber,

$$
\deg\lambda_L=\left(\frac{c_1(L)^g}{g!}\right)^2. \tag{8.5}
$$

To prove this, apply Riemann--Roch on the abelian variety, where the Todd class is $1$ because the tangent bundle is trivial, to obtain $\chi(L)=c_1(L)^g/g!$. The theta group of $L$ identifies the coordinate algebra of the stabilizer with the endomorphisms of the translation representation on cohomology, giving $|\ker\lambda_L|=\chi(L)^2$. For a high power, higher cohomology vanishes and this is ordinary representation rank; polynomiality in tensor powers yields the formula for $L$. This also proves that polarization degree is a square.

The simplest numerical examples are useful checks. On an elliptic curve, a line bundle of degree $d>0$ induces an isogeny of degree $d^2$ and type $(d)$. On $E_1\times E_2$, an external tensor product of positive-degree bundles is ample in both directions. The divisor $E_1\times\{0\}$ alone is trivial along the first direction; its associated homomorphism has a positive-dimensional kernel and is not a polarization. Positivity must occur in every abelian direction.

### 8.4 Principal polarizations

A principal polarization identifies $A$ with $A^\vee$, but it is additional structure. Biduality identifies $A$ with $A^{\vee\vee}$ and does not supply such a self-duality.

An elliptic scheme has the canonical principal polarization from the zero divisor. A product of principally polarized schemes has the product principal polarization. A Jacobian has the theta principal polarization. In contrast, an arbitrary abelian variety need not carry a specified principal polarization, and two principal polarizations on the same underlying variety can be inequivalent.

A principal polarization may be represented fppf-locally by an ample $L$ with $\chi(L)=1$. The associated complete linear system can be small; it is the polarization homomorphism, not a chosen theta divisor, that descends canonically.

### 8.5 The induced alternating pairing

Compose the Weil pairing with a polarization:

$$
e_n^\lambda(x,y)=e_n(x,\lambda(y)):
A[n]\times A[n]\longrightarrow\mu_n. \tag{8.6}
$$

Symmetry of $\lambda$ and antisymmetry of the Poincare commutator give

$$
e_n^\lambda(y,x)=e_n^\lambda(x,y)^{-1},
\qquad e_n^\lambda(x,x)=1. \tag{8.7}
$$

The second identity is genuine alternation, including when $2$ is not invertible; it follows from the canonical diagonal trivialization of the commutator, not merely from skew-symmetry.

The radical is $\ker(\lambda|_{A[n]})$. Hence $e_n^\lambda$ is perfect exactly when

$$
\lambda[n]:A[n]\longrightarrow A^\vee[n]
$$

is an isomorphism. This holds for every $n$ under a principal polarization, and more generally whenever $n$ is relatively prime to $\deg\lambda$. Indeed choose integers $a,b$ with $an+b\deg\lambda=1$ and use an isogeny quasi-inverse to $\lambda$ to prove that its kernel meets $A[n]$ trivially; equal ranks then give an isomorphism.

### 8.6 Vanishing and the rank of the pushforward

Formula (8.5) computed the degree of a polarization from an Euler characteristic. For most purposes that is enough. But an ample bundle is not only a numerical invariant: it is a supply of sections, and a family of abelian schemes with a chosen ample bundle should come with a family of vector spaces of sections that varies as well as possible. This section proves that on an abelian variety an ample bundle has no higher cohomology at all, so that the Euler characteristic is the honest number of independent sections, and that in a family the sections assemble into a vector bundle whose formation commutes with every base change. The result is the technical foundation of every coordinate system built from theta functions, and it is used systematically in Chapter 9A.

The proof of vanishing is short once one knows how to move an ample bundle around. Two mechanisms are available and both have already been established. The first is that the degree-zero twists of $L$ are exactly the translates of $L$: since $\lambda_L$ is surjective on geometric points, every $M\in\operatorname{Pic}^0$ is of the form $t_x^*L\otimes L^{-1}$, so $L\otimes M\simeq t_x^*L$ has the same cohomology as $L$. The second is that pulling back along $[n]$ multiplies $L$ into a high power of itself, where Serre vanishing applies, while simultaneously spreading it over all its degree-zero twists. Combining the two mechanisms sandwiches $H^i(A,L)$ inside a group that vanishes for trivial reasons.

**Lemma 8.2.** Let $q:A\to B$ be an isogeny of abelian varieties over an algebraically closed field $k$, with kernel $H$ of order $N$ invertible in $k$. Then

$$
q_*\mathcal O_A\simeq\bigoplus_{y\in\ker(q^\vee)(k)}M_y, \tag{8.8}
$$

where $M_y$ denotes the degree-zero line bundle on $B$ classified by $y\in B^\vee(k)$.

**Proof.** Since $N$ is invertible, $H$ is finite étale, hence constant, and $H(k)$ has order $N$; because $N$ is invertible in the algebraically closed $k$, the character group $\widehat H=\operatorname{Hom}(H(k),k^\times)$ also has order $N$ and the averaging operators

$$
\mathrm e_\chi=\frac1N\sum_{h\in H(k)}\chi(h)^{-1}h
$$

are a complete orthogonal family of idempotents. They act on $q_*\mathcal O_A$ through the translation action of $H$ and decompose it as $\bigoplus_{\chi\in\widehat H}\mathcal F_\chi$. Étale-locally on $B$ the torsor $q$ is trivial, so $q_*\mathcal O_A$ becomes the regular representation of $H(k)$ over the structure sheaf, in which every character occurs exactly once; hence each $\mathcal F_\chi$ is a line bundle.

To identify $\mathcal F_\chi$, recall the character construction of Section 6.1: the bundle $M_\chi$ on $B$ is obtained by descending $\mathcal O_A$ equipped with the linearization twisted by $\chi$. Descent identifies $M_\chi$ with the subsheaf of $q_*\mathcal O_A$ on which $H$ acts through $\chi^{-1}$, that is, with $\mathcal F_{\chi^{-1}}$. By Theorem 6.1 the assignment $\chi\mapsto M_\chi$ identifies $\widehat H$ with $\ker(q^\vee)(k)$, and inversion is a bijection of $\widehat H$, so summing over $\chi$ is the same as summing over $y\in\ker(q^\vee)(k)$. $\square$

**Theorem 8.3 (vanishing).** Let $A$ be an abelian variety over an algebraically closed field $k$ and $L$ an ample line bundle on $A$. Then

$$
H^i(A,L)=0\quad\text{for }i>0,
\qquad
\dim_kH^0(A,L)=\chi(L). \tag{8.9}
$$

**Proof.** We may rigidify $L$, which changes nothing. Since $\lambda_{[-1]^*L}=\lambda_L$, the rigidified bundle $[-1]^*L\otimes L^{-1}$ has vanishing associated homomorphism and is therefore algebraically trivial by Section 8.1: $[-1]^*L\simeq L\otimes M_z$ for some $z\in A^\vee(k)$. Substituting into (2.1) gives, for every $n\ge1$,

$$
[n]^*L\simeq L^{\otimes n^2}\otimes M_{z'},\qquad z'=\tfrac{n(n-1)}2\,z .
$$

Now fix $x\in A(k)$ with $\lambda_L(x)=y$; such $x$ exists for every $y$ because $\lambda_L$ is an isogeny, hence surjective on $k$-points. Then $L\otimes M_y\simeq t_x^*L$, and more generally $L^{\otimes m}\otimes M_y\simeq t_x^*(L^{\otimes m})$ for a suitable $x$ because $\lambda_{L^{\otimes m}}=m\lambda_L$ is again an isogeny. Since translation is an automorphism of $A$, tensoring an arbitrary power of $L$ by a degree-zero bundle does not change its cohomology.

Choose a prime $\ell\ne\operatorname{char}k$ and put $n=\ell^r$. Applying Lemma 8.2 to $q=[n]$, whose kernel $A[n]$ has order $n^{2g}$ invertible in $k$ and whose dual kernel is $A^\vee[n]$, together with the projection formula and the finiteness of $[n]$,

$$
H^i(A,[n]^*L)\simeq H^i\bigl(A,L\otimes[n]_*\mathcal O_A\bigr)
\simeq\bigoplus_{y\in A^\vee[n](k)}H^i(A,L\otimes M_y)
\simeq H^i(A,L)^{\oplus n^{2g}} ,
$$

the last step by the translation argument. On the other hand $[n]^*L\simeq L^{\otimes n^2}\otimes M_{z'}$ has the cohomology of $L^{\otimes n^2}$, which vanishes in positive degrees as soon as $n^2$ is large, by Serre vanishing for the ample $L$. Taking $r$ large gives $H^i(A,L)^{\oplus n^{2g}}=0$, hence $H^i(A,L)=0$ for $i>0$. The second assertion of (8.9) is then the definition of the Euler characteristic. $\square$

The argument used ampleness twice, in Serre vanishing and in the surjectivity of $\lambda_L$, and it used no positivity beyond that. It also shows, as a byproduct, that $h^i(L^{\otimes n^2})=n^{2g}h^i(L)$ for every $i$ and every $n$ invertible in $k$, which is the cohomological shadow of the degree formula for $[n]$.

**Theorem 8.4 (the pushforward of an ample bundle).** Let $\pi:A\to S$ be an abelian scheme and $L$ a relatively ample line bundle on $A$ whose associated polarization has degree $d^2$ with $d$ a positive integer, constant on $S$. Then

$$
R^i\pi_*L=0\ (i>0),
\qquad
\pi_*L\ \text{is locally free of rank }d,
$$

and the formation of $\pi_*L$ commutes with arbitrary base change $S'\to S$.

**Proof.** Every geometric fiber $L_{\bar s}$ is ample on the abelian variety $A_{\bar s}$, so Theorem 8.3 gives $H^i(A_{\bar s},L_{\bar s})=0$ for $i>0$, and cohomology over a field is insensitive to extension of the base field, so the same vanishing holds on every fiber. Descending induction on $i$ in the cohomology-and-base-change theorem for proper flat families, proved in the coherent-cohomology volume, Book 15 §5.2, now gives $R^i\pi_*L=0$ for $i>0$, that $\pi_*L$ is locally free, and that its formation commutes with arbitrary base change: at the top degree the base-change map is trivially surjective, each vanishing propagates one degree down, and in degree zero the surjectivity of the base-change map in degree one yields local freeness together with universal base change.

For the rank, formula (8.5) and its accompanying identity give $\deg\lambda_L=\chi(L_{\bar s})^2=d^2$ on each geometric fiber, so $\chi(L_{\bar s})=\pm d$. By the vanishing just proved, $\chi(L_{\bar s})=h^0(A_{\bar s},L_{\bar s})\ge0$, and it is nonzero because $d>0$. Hence $\chi(L_{\bar s})=d$ and the rank of $\pi_*L$ is $d$. $\square$

The theorem is exactly the statement one needs to build coordinates. It says that a relatively ample bundle of polarization type with $d_1\cdots d_g=d$ furnishes a rank-$d$ vector bundle of sections on the base, stable under every base change, so that a trivialization of that bundle is a genuine system of coordinates for the family and not an artifact of one fiber. What is still missing is a canonical way to trivialize it. Nothing in the present chapter selects a basis of $\pi_*L$, and indeed no such basis exists without further structure. Chapter 9A supplies the missing structure: the theta group acts on $\pi_*L$, and once that action is put in a standard form the choice of basis is reduced to a single scalar.

## 9. Polarized isogenies and isotropic kernels

Quotienting an abelian scheme always produces another abelian scheme, but a chosen polarization does not automatically descend. The obstruction is measured exactly by the commutator pairing on the kernel. This chapter makes the relation precise and explains why maximal isotropic subgroups are the correct kernels for constructing principally polarized quotients.

### 9.1 Pulling back a polarization

Let $f:A\to B$ be a homomorphism and let $M$ be a line bundle on $B$. Formula (8.2) says

$$
\lambda_{f^*M}=f^\vee\lambda_Mf. \tag{9.1}
$$

If $f$ is an isogeny and $M$ is ample, then $f^*M$ is ample, so the right side is a polarization. Thus the pullback of a polarization $\mu:B\to B^\vee$ is

$$
f^*\mu:=f^\vee\mu f:A\to A^\vee. \tag{9.2}
$$

Degrees satisfy

$$
\deg(f^*\mu)=(\deg f)^2\deg\mu. \tag{9.3}
$$

This follows from multiplicativity and $\deg f^\vee=\deg f$. Equation (9.3) is a useful numerical check, but it does not by itself prove descent of a polarization.

### 9.2 Descent across a quotient

Let $q:A\to B=A/H$ and let $L$ be a rigidified line bundle on $A$. To descend $L$, one needs an $H$-linearization: isomorphisms

$$
\alpha_h:t_h^*L\xrightarrow{\sim}L
$$

whose compositions satisfy $\alpha_{h+h'}=\alpha_h\circ t_h^*\alpha_{h'}$. The possible lifts of translations form the **theta group** $\mathcal G(L)$ in an exact sequence

$$
1\longrightarrow\mathbf G_m\longrightarrow\mathcal G(L)
\longrightarrow K(L)\longrightarrow1,
\qquad K(L)=\ker\lambda_L. \tag{9.4}
$$

Its commutator is an alternating pairing

$$
c_L:K(L)\times K(L)\longrightarrow\mathbf G_m. \tag{9.5}
$$

An $H$-linearization is precisely a splitting of (9.4) over $H$. A necessary condition is therefore $c_L|_{H\times H}=1$. Fppf locally on the base it is also sufficient. This is the theta-group splitting lemma: when the commutator vanishes, the restricted extension is commutative; its sheaf of splittings is acted on simply transitively by

$$
H^D=\underline{\operatorname{Hom}}(H,\mathbf G_m).
$$

The assertion can be checked after passing to geometric fibers. There the underlying invertible sheaf of the extension is trivial on the finite scheme $H$ after a faithfully flat field extension, and the commutative multiplication cocycle is a coboundary precisely because its alternating commutator is trivial. Choosing that coboundary gives a splitting. The splitting equations are finitely many equations in the finite locally free coordinate algebra of $H$, so their solution scheme is an fppf $H^D$-torsor and hence becomes nonempty after an fppf cover of the base. Descent of line bundles along the $H$-torsor then gives $M$ on $B$ with $q^*M\simeq L$. Ampleness descends along the finite faithfully flat map $q$.

The local qualification cannot simply be erased. Even when the commutator vanishes, the torsor of splittings can have no global section. The descended polarization homomorphism, however, is global whenever the symmetric homomorphism factors through $q$ and $q^\vee$ as below.

### 9.3 Orthogonal kernels

Assume $\lambda$ is a principal polarization on $A$. The pairing $e_n^\lambda$ is perfect on $A[n]$. For finite locally free $H\subseteq A[n]$, define

$$
H^\perp=\{x\in A[n]:e_n^\lambda(x,H)=1\}.
$$

Then

$$
|H|\,|H^\perp|=n^{2g},
\qquad (H^\perp)^\perp=H. \tag{9.6}
$$

The subgroup is **isotropic** if $H\subseteq H^\perp$, and **maximal isotropic** or **Lagrangian** if equality holds. A Lagrangian has order $n^g$.

Let $q:A\to B=A/H$. Work fppf-locally where $\lambda=\lambda_L$ for a symmetric ample bundle $L$. Then $n\lambda=\lambda_{L^n}$ and $H\subseteq A[n]\subseteq K(L^n)$. The commutator pairing of the theta group $\mathcal G(L^n)$ restricts on $A[n]$ to $e_n^\lambda$. Isotropy therefore says exactly that this commutator vanishes on $H$. By Section 9.2, after a further fppf cover $L^n$ admits an $H$-linearization and descends to an ample bundle $M$ on $B$. Formula (9.1) now gives a symmetric homomorphism $\mu=\lambda_M$ satisfying

$$
\mu:B\longrightarrow B^\vee
$$

such that

$$
q^\vee\mu q=n\lambda. \tag{9.7}
$$

Two local choices of linearization differ by a character of $H$, so their descended bundles can differ by an algebraically trivial class. Their associated homomorphisms are therefore equal. Descent for morphisms glues the local maps $\mu$ to a global polarization. This construction also explains why the homomorphism can descend even when no preferred global inducing bundle does.

### 9.4 Maximal isotropic quotients

**Theorem 9.1.** Let $(A,\lambda)$ be principally polarized of relative dimension $g$, and let $H\subseteq A[n]$ be finite locally free and Lagrangian for $e_n^\lambda$. Then $B=A/H$ carries a unique polarization $\mu$ satisfying (9.7), and $\mu$ is principal.

**Proof.** Existence and positivity were proved in Section 9.3. For uniqueness, let $\mu_1,\mu_2$ satisfy (9.7). Since $q$ is an epimorphism of fppf sheaves,

$$
q^\vee(\mu_1-\mu_2)=0.
$$

Thus $\mu_1-\mu_2:B\to B^\vee$ factors through the finite affine group $\ker q^\vee=H^D$. A map from the proper geometrically connected group $B$ to a finite affine group is constant because its coordinate functions come from the base; as a homomorphism it is therefore zero. Hence $\mu_1=\mu_2$.

Taking degrees in (9.7), and using $\deg(n\lambda)=n^{2g}$ because $\lambda$ is principal, gives

$$
(\deg q)^2\deg\mu=n^{2g}.
$$

Since $\deg q=|H|=n^g$, we obtain $\deg\mu=1$. A degree-one isogeny is an isomorphism, so $\mu$ is principal. $\square$

If $H$ is merely isotropic, the same construction gives a polarization whose degree is

$$
\deg\mu=\frac{n^{2g}}{|H|^2}.
$$

This formula explains why half-dimensional isotropic kernels, not arbitrary finite kernels, preserve principality.

For an elliptic curve and $H\subset E[n]$ finite locally free of order $n$, alternation makes a genuinely cyclic prime-to-characteristic subgroup isotropic. Since $|E[n]|=n^2$, it is Lagrangian, and $E/H$ receives its canonical principal polarization. At the residue characteristic the word “cyclic” has competing meanings: $\mu_p$, the constant group, and local group schemes all have order $p$. The safe input is the displayed isotropy condition, which the commutator pairing can test scheme-theoretically.

## 9A. Theta groups in standard form

Section 9.2 attached to a relatively ample rigidified bundle $L$ its theta group $\mathcal G(L)$, a central extension of the finite group scheme $K(L)$ by $\mathbf G_m$, and used the vanishing of its commutator as the criterion for descending $L$ along an isogeny. That is a qualitative use of the extension. This chapter extracts the quantitative content: the extension has, locally on the base, a completely explicit normal form; the discrepancy between $\mathcal G(L)$ and that normal form is a torsor under a finite group scheme; and the normal form has essentially only one representation, so that the sections of $L$ acquire a distinguished basis. These three statements are the mechanism by which an abelian scheme with a polarization of fixed type acquires coordinates, and they are what makes polarized families rigid enough to be classified.

### 9A.1 Why a standard form is needed and what it can say

Consider the difficulty. The extension

$$
1\longrightarrow\mathbf G_m\longrightarrow\mathcal G(L)\longrightarrow K(L)\longrightarrow1
$$

is never split when $L$ is ample and $K(L)$ is nontrivial, because a splitting over $K(L)$ would force the commutator pairing to vanish, whereas we prove below that the commutator is perfect. So the extension carries no preferred set of elements, and there is no way to name a lift of a translation without making a choice. On the other hand, the extension carries almost no information either: its commutator pairing is a perfect alternating pairing on a finite group scheme, and such a pairing has, up to isomorphism, only the discrete invariant recorded by the type $\delta=(d_1\mid d_2\mid\cdots\mid d_g)$ of Section 8.3. The tension between "no canonical choice" and "no information" is exactly the situation in which a torsor appears: the set of identifications with a fixed standard model is nonempty locally, and is acted on simply transitively by the automorphisms of the model.

This is worth doing because of what happens on the other side. The theta group acts on the sections of $L$, and the central $\mathbf G_m$ acts by scalars. Among all modules with that property there is, locally on the base, exactly one of rank $d=d_1\cdots d_g$, namely the module of functions on the finite group $K(\delta)=\bigoplus_i\mathbf Z/d_i\mathbf Z$; this is the algebraic form of the Stone–von Neumann uniqueness theorem. Since Theorem 8.4 says that $\pi_*L$ has rank exactly $d$, a choice of identification of $\mathcal G(L)$ with the standard model forces $\pi_*L$ to be the standard module, and the standard module has an evident basis indexed by $K(\delta)$. In one stroke the sections of $L$ become coordinates, canonically up to a single scalar, and compatibly with every base change.

Two limitations must be stated at the outset, and they explain the standing convention of this chapter. First, the classification of perfect alternating pairings by elementary divisors is a statement about finite abelian groups, and it applies to $K(L)$ only when $K(L)$ is étale, so that it is a group of points after a small cover. When a residue characteristic divides the degree of the polarization, $K(L)$ can be connected and nonreduced, and the local models are then genuinely more numerous. Second, the averaging that produces the eigenspace decomposition of a representation requires the relevant orders to be invertible if one insists on writing idempotents. We therefore fix throughout this chapter a type

$$
\delta=(d_1\mid d_2\mid\cdots\mid d_g),\qquad d_1\mid d_2\mid\cdots\mid d_g,\qquad d=d_1\cdots d_g,
$$

and a base scheme $S$ on which $d$ is invertible. Every theorem below is stated in that range, which is the range in which the moduli applications operate; no statement is made about the case where a residue characteristic divides $d$.

### 9A.2 The standard Heisenberg group scheme

The model to aim at is dictated by the shape of the answer. The commutator pairing of a theta group is perfect and alternating, so its group must split, after a small cover, into a Lagrangian and a complementary Lagrangian dual to it. Book 34 §15.2 already isolates the resulting pairing: on a group $\underline M\times D(M)$ the formula $\bigl((m,\chi),(m',\chi')\bigr)\mapsto\chi'(m)\chi(m')^{-1}$ is perfect and alternating, and both factors are Lagrangian. The standard theta group is the canonical central extension realizing that pairing.

Write

$$
K(\delta)=\bigoplus_{i=1}^g\underline{\mathbf Z/d_i\mathbf Z},
\qquad
K(\delta)^D=\bigoplus_{i=1}^g\mu_{d_i},
$$

the second being the Cartier dual of the first by Book 34 §§3.5, 5.4. Both are finite étale of order $d$ over $S$, since $d$ is invertible. Write $\langle\chi,x\rangle=\chi(x)$ for the evaluation pairing $K(\delta)^D\times K(\delta)\to\mathbf G_m$, which is perfect.

**Definition.** The **standard Heisenberg group scheme** of type $\delta$ is the $S$-scheme

$$
\mathcal G(\delta)=\mathbf G_m\times_SK(\delta)\times_SK(\delta)^D
$$

with the multiplication

$$
(\alpha,x,\chi)\cdot(\alpha',x',\chi')=\bigl(\alpha\alpha'\chi'(x),\,x+x',\,\chi\chi'\bigr). \tag{9A.1}
$$

**Lemma 9A.1.** Formula (9A.1) defines a group scheme structure on $\mathcal G(\delta)$, flat and affine of finite presentation over $S$ and compatible with arbitrary base change. The subgroup $\mathbf G_m=\{(\alpha,0,1)\}$ is central and the projection to $K(\delta)\times K(\delta)^D$ is faithfully flat with kernel $\mathbf G_m$, so that

$$
1\longrightarrow\mathbf G_m\longrightarrow\mathcal G(\delta)\longrightarrow K(\delta)\times K(\delta)^D\longrightarrow1 \tag{9A.2}
$$

is a central extension. Its commutator pairing is

$$
e_\delta\bigl((x,\chi),(x',\chi')\bigr)=\chi'(x)\,\chi(x')^{-1}, \tag{9A.3}
$$

which is alternating and perfect. In particular the center of $\mathcal G(\delta)$ is exactly $\mathbf G_m$.

**Proof.** Associativity is the cocycle identity for $\psi\bigl((x,\chi),(x',\chi')\bigr)=\chi'(x)$: computing both bracketings of a triple product, the accumulated scalars are $\chi'(x)\chi''(x+x')$ and $\chi''(x')\chi'(x)\chi''(x)$, which agree. The element $(1,0,1)$ is a two-sided identity and $(\alpha^{-1}\chi(x),-x,\chi^{-1})$ inverts $(\alpha,x,\chi)$ on both sides, as one checks by multiplying out; all these formulas are morphisms of schemes, so $\mathcal G(\delta)$ is a group scheme, evidently affine, flat, of finite presentation, and formed compatibly with base change. Centrality of $\mathbf G_m$ and exactness of (9A.2) are immediate from the product decomposition, the projection being a trivial $\mathbf G_m$-torsor.

For the commutator, in any central extension with normalized cocycle $\psi$ the commutator of lifts of $a$ and $b$ is $\psi(a,b)\psi(b,a)^{-1}$; with $a=(x,\chi)$ and $b=(x',\chi')$ this is $\chi'(x)\chi(x')^{-1}$, which is (9A.3). Setting $(x',\chi')=(x,\chi)$ gives $1$, so the pairing is alternating. Its adjoint sends $(x,\chi)$ to the character $(x',\chi')\mapsto\chi'(x)\chi(x')^{-1}$ of $K(\delta)\times K(\delta)^D$, that is, to the pair $(\chi^{-1},x)$ inside $K(\delta)^D\times K(\delta)^{DD}=\bigl(K(\delta)\times K(\delta)^D\bigr)^D$, using Cartier biduality and the duality of a product. This is an isomorphism, so $e_\delta$ is perfect, and the center of the extension, which is the preimage of the radical of the commutator, is $\mathbf G_m$. $\square$

Two features of the model deserve emphasis. Both $K(\delta)$ and $K(\delta)^D$ are Lagrangian in the sense of Section 9.3: each is isotropic, because (9A.3) vanishes when both arguments lie in the same factor, and each has order $d$, the square root of the order of $K(\delta)\times K(\delta)^D$. Moreover each of them lifts to a subgroup of $\mathcal G(\delta)$, since the cocycle $\chi'(x)$ is trivial when both arguments lie in the same factor; these two liftings are what the Schrödinger model of Section 9A.6 uses, one to translate and one to multiply by a character.

For $g=1$ and $\delta=(n)$ the group is $\mathcal G(n)=\mathbf G_m\times\underline{\mathbf Z/n\mathbf Z}\times\mu_n$ with $(\alpha,a,\zeta)(\alpha',a',\zeta')=(\alpha\alpha'\zeta'^a,a+a',\zeta\zeta')$: the classical Heisenberg group of level $n$, generated by a shift and a multiplication operator that commute up to an $n$-th root of unity.

**Definition.** Let $L$ be a relatively ample rigidified line bundle on an abelian scheme $A/S$. A **theta structure of type $\delta$** on $(A,L)$ is an isomorphism of $S$-group schemes

$$
\Theta:\mathcal G(\delta)\xrightarrow{\ \sim\ }\mathcal G(L)
$$

whose restriction to the central $\mathbf G_m$ is the identity. Such a $\Theta$ induces an isomorphism $\bar\Theta:K(\delta)\times K(\delta)^D\to K(L)$ carrying $e_\delta$ to $c_L$, because a homomorphism of central extensions inducing the identity on the centers preserves commutators.

### 9A.3 The commutator pairing and its normal form

Before a normal form can be sought, the pairing $c_L$ of (9.5) must be known to be perfect. This is the point at which the duality theory of Chapter 6 enters, and the mechanism is worth displaying because it explains why the theta group deserves to be considered a duality-theoretic object.

**Proposition 9A.2.** Let $L$ be relatively ample and rigidified. Then the commutator pairing

$$
c_L:K(L)\times_SK(L)\longrightarrow\mathbf G_m
$$

is perfect: its adjoint $K(L)\to K(L)^D$ is an isomorphism of finite locally free group schemes.

**Proof.** Consider on $A\times_SA$ the bundle

$$
\Lambda(L)=m^*L\otimes p_1^*L^{-1}\otimes p_2^*L^{-1},
$$

rigidified along both axes. Viewed as a family, parametrized by the second factor, of rigidified line bundles on the first factor, its member over a point $a$ is $t_a^*L\otimes L^{-1}$, which is algebraically trivial with class $\lambda_L(a)$. By the universal property of $A^\vee$ in Theorem 3.1, the classifying morphism of this family is $\lambda_L$, so there is a canonical isomorphism

$$
\Lambda(L)\simeq(1\times\lambda_L)^*\mathcal P_A. \tag{9A.4}
$$

Now let $x$ be a point of $K(L)$. Under biduality, $x$ classifies a rigidified algebraically trivial bundle $N_x$ on $A^\vee$, namely the restriction of the Poincaré bundle to $\{x\}\times A^\vee$. Restricting (9A.4) to $\{x\}\times A$ and using the rigidification along the first axis identifies

$$
\lambda_L^*N_x\simeq t_x^*L\otimes L^{-1},
$$

which is trivial precisely because $x\in K(L)$; and a trivialization of it is the same thing as an isomorphism $t_x^*L\xrightarrow{\sim}L$, that is, a lift of $x$ to the theta group $\mathcal G(L)$.

Section 6.1 computes the canonical pairing $\ker f\times\ker f^\vee\to\mathbf G_m$ of (6.2) for an isogeny $f$ by exactly this recipe: given a point of $\ker f^\vee$, presented as a bundle whose pullback along $f$ is trivial, and a chosen trivialization, the pairing with a point of $\ker f$ is the ratio between the trivialization and its translate. Applying this to $f=\lambda_L$ and unwinding the multiplication law of $\mathcal G(L)$, that ratio is precisely the commutator $\tilde x\tilde y\tilde x^{-1}\tilde y^{-1}$ of two lifts, since translating a trivialization by $y$ is conjugation by any lift $\tilde y$. Hence $c_L$ agrees, up to the harmless inversion coming from the order of the two arguments, with the pairing (6.2) attached to $\lambda_L$, under the identification of $\ker\lambda_L^\vee$ with $\ker\lambda_L$ furnished by the symmetry $\lambda_L^\vee\delta_A=\lambda_L$ of Proposition 8.1. Theorem 6.1 says that pairing is perfect. $\square$

The classification of pairings on the point level is elementary but must be proved rather than quoted, since it is what produces the type.

**Lemma 9A.3 (symplectic normal form).** Let $K_0$ be a finite abelian group of exponent $N$, let $C$ be a cyclic group of order $N$, and let $c:K_0\times K_0\to C$ be a pairing that is alternating, $c(z,z)=1$, and perfect, in the sense that $z\mapsto c(z,-)$ is an isomorphism $K_0\to\operatorname{Hom}(K_0,C)$. Then there are integers $d_1\mid d_2\mid\cdots\mid d_g$ with $d_g=N$, uniquely determined by $K_0$, and an isomorphism

$$
K_0\simeq H\oplus\operatorname{Hom}(H,C),\qquad H=\bigoplus_{i=1}^g\mathbf Z/d_i\mathbf Z,
$$

under which $c\bigl((x,\chi),(x',\chi')\bigr)=\chi'(x)\chi(x')^{-1}$. In particular $|K_0|=(d_1\cdots d_g)^2$.

**Proof strategy.** One peels off a hyperbolic plane at a time, always choosing the plane spanned by an element of maximal order, and one checks that the orthogonal complement inherits a perfect alternating pairing of smaller size. The only step requiring care is the production of a partner for a given element, and there perfectness is used exactly once.

**Proof.** Induct on $|K_0|$, the trivial group being the base case. Let $x\in K_0$ have order $N$. Let $m$ be the exponent of the image of $c(x,-)$, a subgroup of the cyclic $C$. Then $c(mx,z)=c(x,z)^m=1$ for all $z$, so perfectness gives $mx=0$ and hence $N\mid m$; thus $c(x,-)$ is surjective onto $C$ and there is $y$ with $c(x,y)=\zeta$ a generator of $C$, of order $N$. Then $y$ has order divisible by $N$, hence exactly $N$.

Let $P=\langle x\rangle+\langle y\rangle$. If $ax=by$ then pairing with $x$ and using alternation gives $1=c(by,x)=\zeta^{-b}$, so $N\mid b$ and $by=0$; thus $P=\langle x\rangle\oplus\langle y\rangle\simeq(\mathbf Z/N\mathbf Z)^2$. The restriction of $c$ to $P$ has trivial radical: if $z=ax+by$ pairs trivially with $x$ and with $y$, then $\zeta^{b}=1$ and $\zeta^{a}=1$, so $z=0$. A pairing on a finite abelian group of exponent dividing $N$ with trivial radical is perfect, since its adjoint is an injection between groups of the same order, $|\operatorname{Hom}(P,C)|=|P|$.

Let $P^\perp=\{z:c(z,P)=1\}$. Perfectness of $c|_P$ implies $K_0=P\oplus P^\perp$: given $z$, the character $c(z,-)|_P$ is $c(p,-)|_P$ for a unique $p\in P$, and then $z-p\in P^\perp$; and $P\cap P^\perp=0$ by nondegeneracy on $P$. The restriction of $c$ to $P^\perp$ is again perfect: if $z\in P^\perp$ pairs trivially with $P^\perp$, it pairs trivially with $P\oplus P^\perp=K_0$, hence vanishes. It is alternating, and its exponent $N'$ divides $N$. The induction is applied to $P^\perp$ with $C$ replaced by its subgroup of order $N'$, which changes nothing: a homomorphism from a group of exponent $N'$ into $C$ lands in that subgroup, so the two perfectness statements and the two groups $\operatorname{Hom}(-,C)$ coincide. By induction $P^\perp\simeq H'\oplus\operatorname{Hom}(H',C)$ in standard form with $H'=\bigoplus_{i<g}\mathbf Z/d_i\mathbf Z$ and $d_1\mid\cdots\mid d_{g-1}$, all dividing $N$. Setting $d_g=N$ and identifying $\langle y\rangle$ with $\operatorname{Hom}(\langle x\rangle,C)$ by $y\mapsto(x\mapsto\zeta)$ puts $c$ on $P$ into the stated shape, since

$$
c(ax+by,\,a'x+b'y)=\zeta^{ab'-a'b}
$$

is exactly $\chi'(x)\chi(x')^{-1}$ in those coordinates. Direct sums of standard forms are standard, which completes the induction. Uniqueness of the $d_i$ holds because $K_0\simeq\bigoplus_i(\mathbf Z/d_i\mathbf Z)^2$ determines its own elementary divisors. $\square$

**Theorem 9A.4 (normal form for $K(L)$).** Let $A/S$ be an abelian scheme and $L$ relatively ample and rigidified with $\deg\lambda_L=d^2$, $d$ invertible on $S$. Then $K(L)$ is finite étale of order $d^2$, and there is a locally constant type $\delta=(d_1\mid\cdots\mid d_g)$ with $d_1\cdots d_g=d$ such that, étale-locally on $S$, there is an isomorphism

$$
K(L)\simeq K(\delta)\times_SK(\delta)^D
$$

carrying $c_L$ to the standard pairing $e_\delta$ of (9A.3).

**Proof.** The group $K(L)$ is finite locally free of order $d^2$, and it is killed by its order, which is invertible on $S$; a finite locally free commutative group scheme killed by an integer invertible on the base is finite étale, by Book 28 §4.5. Étale-locally on $S$ we may therefore assume $S$ strictly henselian local, where $K(L)$ is constant, equal to $\underline{K_0}$ for a finite abelian group $K_0$ of order $d^2$ (Book 17 §3.2). Let $N$ be the exponent of $K_0$; it divides $d^2$ and hence is invertible, so $\mu_N$ is finite étale, hence constant over the strictly henselian base, and its group of sections is identified with the group of $N$-th roots of unity in the separably closed residue field, cyclic of order $N$. The commutator pairing takes values in $\mu_N$ because $K_0$ is killed by $N$, and on sections it is a pairing $c:K_0\times K_0\to\mu_N(S)$, alternating by (9.5) and perfect by Proposition 9A.2; here perfectness of the pairing of group schemes becomes perfectness of the pairing of groups because the sections of the Cartier dual of a constant group are exactly its characters, by Book 34 §5.2. Lemma 9A.3 now supplies the type and the standard form, and the isomorphism of constant group schemes it produces is the required one. That the resulting $\delta$ agrees with the type of Section 8.3 is the identity $K_0\simeq\bigoplus_i(\mathbf Z/d_i\mathbf Z)^2$ read in (8.3), and $d_1\cdots d_g=d$ follows from $|K_0|=d^2$. Finally, since $K(L)$ is finitely presented, the isomorphism obtained over the strict henselization, which is the filtered colimit of the coordinate rings of étale neighborhoods, is already defined over one such neighborhood; this is the same spreading-out used in Book 17 §3.3 to split a finite étale cover over a single small étale neighborhood. The type is locally constant because it is determined by the isomorphism class of the fibers of a finite étale group scheme. $\square$

### 9A.4 Rigidity of central extensions and the existence of theta structures

The normal form for the pairing is not yet a normal form for the extension. What closes the gap is that a central extension of a finite étale group of invertible order by $\mathbf G_m$ is determined, locally, by its commutator alone. This is the technical heart of the chapter, and it is where invertibility of the order is genuinely consumed: the argument needs roots of unity to be present and units to be divisible.

**Theorem 9A.5 (rigidity of central extensions).** Let $S$ be a scheme and $K$ a finite étale commutative $S$-group scheme killed by an integer $N$ invertible on $S$. Let

$$
1\to\mathbf G_m\to\mathcal G\to K\to1,
\qquad
1\to\mathbf G_m\to\mathcal G'\to K\to1
$$

be central extensions with the same commutator pairing $K\times K\to\mathbf G_m$. Then étale-locally on $S$ there is an isomorphism $\mathcal G\simeq\mathcal G'$ inducing the identity on $\mathbf G_m$ and on $K$.

**Proof strategy.** Over a strictly henselian local base, $K$ becomes constant and the underlying $\mathbf G_m$-torsors become trivial, so each extension is described by a normalized $2$-cocycle with values in the units of the base ring. Two cocycles with the same commutator differ by a symmetric cocycle, and a symmetric cocycle is the same thing as a commutative extension of $K$ by the units; such an extension splits because the units are divisible by $N$. A splitting is a coboundary, and adjusting the chosen lifts by it makes the two cocycles equal.

**Proof.** Both $\mathcal G$ and $\mathcal G'$ are affine of finite presentation over $S$, being $\mathbf G_m$-torsors over the finite $K$. By the spreading-out already used in Theorem 9A.4, it suffices to construct the isomorphism after base change to $R=\mathcal O^{sh}_{S,\bar s}$ for each geometric point, so assume $S=\operatorname{Spec}R$ with $R$ strictly henselian local.

Then $K=\underline{K_0}$ is constant, so $K$ is a disjoint union of copies of $S$ indexed by $K_0$, and $\mathcal G\to K$ restricts over each copy to a $\mathbf G_m$-torsor over $\operatorname{Spec}R$. Such a torsor is classified by $\operatorname{Pic}(R)=0$, so it is trivial: choose sections $s_k$ of $\mathcal G$ over $k\in K_0$, normalized by $s_0=1$. The group law becomes

$$
s_ks_{k'}=\psi(k,k')\,s_{k+k'},\qquad \psi(k,k')\in R^\times,
$$

with $\psi$ normalized, $\psi(k,0)=\psi(0,k)=1$, and satisfying the $2$-cocycle identity, which is precisely associativity. Thus $\mathcal G\simeq\mathbf G_m\times\underline{K_0}$ with multiplication twisted by $\psi$; do the same for $\mathcal G'$ with a cocycle $\psi'$. The commutator of lifts of $k,k'$ is $\psi(k,k')\psi(k',k)^{-1}$ and likewise for $\psi'$, so the hypothesis says that $\beta=\psi/\psi'$, again a normalized $2$-cocycle, is symmetric.

Attach to $\beta$ the group $E=R^\times\times K_0$ with $(u,k)(u',k')=(uu'\beta(k,k'),k+k')$. The cocycle identity makes it a group, symmetry makes it abelian, and it is an extension of $K_0$ by $R^\times$. Write $K_0=\bigoplus_i\mathbf Z/n_i\mathbf Z$ with generators $g_i$, each $n_i$ dividing $N$ and hence invertible in $R$. Lift $g_i$ to $\tilde g_i=(1,g_i)\in E$; then $\tilde g_i^{\,n_i}$ lies in $R^\times$. The group $R^\times$ is $n_i$-divisible: for $u\in R^\times$ the algebra $R[X]/(X^{n_i}-u)$ is finite étale over $R$, since on it $X$ is a unit and $n_iX^{n_i-1}$ is therefore invertible, so it is a product of copies of $R$ and $u$ has an $n_i$-th root in $R$. Choose $u_i$ with $u_i^{n_i}=\tilde g_i^{\,n_i}$ and set $f_i=\tilde g_i u_i^{-1}$, an element of order dividing $n_i$. Since $E$ is abelian, $g_i\mapsto f_i$ defines a homomorphism $\sigma:K_0\to E$ splitting the projection. Writing $\sigma(k)=(b(k)^{-1},k)$, the multiplicativity of $\sigma$ says exactly

$$
\beta(k,k')=b(k)b(k')b(k+k')^{-1},
$$

so $\beta$ is a coboundary. Replacing the chosen lifts $s_k$ by $b(k)^{-1}s_k$ multiplies $\psi$ by $\beta^{-1}$ and turns it into $\psi'$. The identity map of $\mathbf G_m\times\underline{K_0}$ is then an isomorphism $\mathcal G\to\mathcal G'$ of extensions inducing the identity on $\mathbf G_m$ and on $K$. $\square$

**Theorem 9A.6 (existence of theta structures).** Let $A/S$ be an abelian scheme and $L$ relatively ample and rigidified, with $\deg\lambda_L=d^2$ and $d$ invertible on $S$, of constant type $\delta$. Then theta structures of type $\delta$ on $(A,L)$ exist étale-locally on $S$.

**Proof.** By Theorem 9A.4 we may, after an étale cover, identify $K(L)$ with $K(\delta)\times K(\delta)^D$ so that $c_L$ becomes $e_\delta$. Then $\mathcal G(L)$ and $\mathcal G(\delta)$ are two central extensions of the same finite étale group scheme, of order $d^2$ invertible on $S$, by $\mathbf G_m$, with the same commutator pairing by Lemma 9A.1. Theorem 9A.5, applied after a further étale cover, produces an isomorphism between them which is the identity on $\mathbf G_m$; that is a theta structure. $\square$

It should be noted where each hypothesis was spent. Invertibility of $d$ was used three times: to know that $K(L)$ is étale, so that a normal form exists at all; to know that the base has enough roots of unity, so that the character group of $K_0$ is large enough to detect it; and to know that units are divisible, so that symmetric cocycles split. None of the three survives when a residue characteristic divides $d$, and no claim is made there.

### 9A.5 The automorphism group and the torsor of theta structures

Theta structures exist locally and are never unique. The failure of uniqueness is governed by the automorphisms of the model, and these can be computed exactly.

Let $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ denote the fppf sheaf on $S$-schemes whose $T$-points are the automorphisms of $\mathcal G(\delta)_T$ restricting to the identity on the central $\mathbf G_m$. Every such automorphism descends to an automorphism of $K=K(\delta)\times K(\delta)^D$ preserving $e_\delta$, giving a homomorphism to the sheaf $\operatorname{Sp}(\delta)$ of automorphisms of $K$ preserving $e_\delta$.

**Theorem 9A.7.** With $d$ invertible on $S$:

1. There is an exact sequence of sheaves of groups on $S$
   $$
1\longrightarrow K^D\longrightarrow\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))\longrightarrow\operatorname{Sp}(\delta)\longrightarrow1, \tag{9A.5}
$$
   in which $K^D=\underline{\operatorname{Hom}}(K,\mathbf G_m)$ consists of the automorphisms inducing the identity on $K$, and these are exactly the inner automorphisms of $\mathcal G(\delta)$.
2. $\operatorname{Sp}(\delta)$ and $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ are finite étale over $S$, of orders $|\!\operatorname{Sp}(\delta)|$ and $d^2\,|\!\operatorname{Sp}(\delta)|$, where $|\!\operatorname{Sp}(\delta)|$ is the number of automorphisms of the finite symplectic group $\bigoplus_i(\mathbf Z/d_i\mathbf Z)^2$ preserving its standard pairing.
3. For $(A,L)$ as in Theorem 9A.6 the sheaf $\underline{\Theta}_\delta(A,L)$ of theta structures is a torsor under $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ for the étale topology, and is represented by a finite étale $S$-scheme of the same rank $d^2|\!\operatorname{Sp}(\delta)|$.

**Proof.** (1) Let $\varphi$ be an automorphism inducing the identity on $K$ and on $\mathbf G_m$. Then $\varphi(g)=\gamma(\bar g)g$ for a unique morphism $\gamma:K\to\mathbf G_m$, since $\varphi(g)$ and $g$ have the same image in $K$ and the fiber is a $\mathbf G_m$-orbit. Multiplicativity of $\varphi$ reads $\gamma(\bar g\bar h)gh=\gamma(\bar g)\gamma(\bar h)gh$, so $\gamma$ is a character, and conversely every character defines such an automorphism. This identifies the kernel of (9A.5) with $K^D$. Conjugation by $g\in\mathcal G(\delta)$ acts on $\mathcal G(\delta)$ by $h\mapsto e_\delta(\bar g,\bar h)h$, hence corresponds to the character $e_\delta(\bar g,-)$; since $e_\delta$ is perfect, every character arises this way, so the kernel consists precisely of the inner automorphisms.

For the surjectivity of the second arrow, let $\sigma$ be a $T$-point of $\operatorname{Sp}(\delta)$. The pullback extension $\sigma^*\mathcal G(\delta)$, that is, the fiber product of $\mathcal G(\delta)\to K$ along $\sigma$, is a central extension of $K$ by $\mathbf G_m$ whose commutator is $e_\delta(\sigma-,\sigma-)=e_\delta$. By Theorem 9A.5 it is isomorphic to $\mathcal G(\delta)$, étale-locally on $T$, by an isomorphism trivial on $\mathbf G_m$ and on $K$; such an isomorphism is the same as an automorphism of $\mathcal G(\delta)$ lifting $\sigma$. So the map is an epimorphism of étale sheaves, which is the meaning of exactness at the right of (9A.5).

(2) Étale-locally $K$ becomes constant, and for constant groups a homomorphism $\underline{M}_T\to\underline{M'}_T$ is a locally constant function $T\to\operatorname{Hom}(M,M')$; so $\operatorname{Sp}(\delta)$ is étale-locally the constant group scheme on the finite symplectic automorphism group of $K_0=\bigoplus_i(\mathbf Z/d_i\mathbf Z)^2$, and by descent it is finite étale of that order. Likewise $K^D$ is finite étale of order $d^2$. By (1) the sheaf $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ is, over $\operatorname{Sp}(\delta)$, a torsor under the finite étale group $K^D$; a torsor under a finite locally free group scheme is represented by a scheme finite locally free of the same rank over its base, so $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ is finite locally free over $\operatorname{Sp}(\delta)$ and hence over $S$, of rank $d^2|\!\operatorname{Sp}(\delta)|$. It is étale: being a torsor under an étale group scheme it is étale over $\operatorname{Sp}(\delta)$, which is étale over $S$. Over a strictly henselian local base it is therefore a disjoint union of copies of the base, that is, constant.

(3) Precomposition makes $\operatorname{Aut}_{\mathbf G_m}(\mathcal G(\delta))$ act on $\underline{\Theta}_\delta(A,L)$ simply transitively: two theta structures differ by an automorphism of the model, uniquely. By Theorem 9A.6 the sheaf is nonempty étale-locally. Hence it is an étale torsor, and it is represented by a finite étale scheme of the stated rank by the same representability of torsors under a finite locally free group. $\square$

The exact sequence (9A.5) is the precise form of the statement that a theta structure records two independent pieces of data: a symplectic identification of $K(L)$ with the standard model $K(\delta)\times K(\delta)^D$, and a lift of that identification to the extension, the lifts forming a torsor under the characters of $K$.

### 9A.6 The Schrödinger representation and Stone–von Neumann

We now turn to representations. The standard module is the module of functions on the finite group $K(\delta)$:

$$
V(\delta)=\bigoplus_{y\in K(\delta)}\mathcal O_S\cdot\delta_y,
$$

free of rank $d$, where $\delta_y$ is the characteristic function of $y$ and the sum is over the $d$ sections of the constant group scheme $K(\delta)$. Let $\mathcal G(\delta)$ act by

$$
\bigl((\alpha,x,\chi)\cdot f\bigr)(y)=\alpha\,\chi(y)\,f(y+x),
\qquad\text{equivalently}\qquad
(\alpha,x,\chi)\cdot\delta_y=\alpha\,\chi(y-x)\,\delta_{y-x}. \tag{9A.6}
$$

A direct computation with (9A.1) shows this is an action: applying $(\alpha,x,\chi)$ after $(\alpha',x',\chi')$ produces the scalar $\alpha\alpha'\chi(y)\chi'(y)\chi'(x)$ and the shift by $x+x'$, which is what $(\alpha,x,\chi)(\alpha',x',\chi')$ prescribes. The central $\mathbf G_m$ acts by scalars. This is the **Schrödinger representation**: the subgroup $K(\delta)$ translates the argument and the subgroup $K(\delta)^D$ multiplies by a character, and the two operations commute only up to the value of the character, which is exactly (9A.3).

Call a **$\mathcal G(\delta)$-module of central character one** a finite locally free $\mathcal O_S$-module $W$ together with a homomorphism of group functors $\mathcal G(\delta)\to\operatorname{GL}(W)$ such that the central $\mathbf G_m$ acts through $\alpha\mapsto\alpha\cdot\operatorname{id}$. The Schrödinger representation is one, of rank $d$.

**Theorem 9A.8 (Stone–von Neumann).** Let $W$ be a $\mathcal G(\delta)$-module of central character one. Let $W_0=W^{K(\delta)^D}$ be the submodule of invariants under the subgroup $\{(1,0,\chi)\}\simeq K(\delta)^D$. Then $W_0$ is a direct summand of $W$, hence finite locally free, and the map

$$
\Phi:V(\delta)\otimes_{\mathcal O_S}W_0\longrightarrow W,
\qquad
\delta_y\otimes w\longmapsto(1,-y,1)\cdot w, \tag{9A.7}
$$

is an isomorphism of $\mathcal G(\delta)$-modules, where $\mathcal G(\delta)$ acts on the source through $V(\delta)$ alone. In particular $\operatorname{rank}W=d\cdot\operatorname{rank}W_0$, and if $\operatorname{rank}W=d$ then $W_0$ is a line bundle, $W\simeq V(\delta)\otimes_{\mathcal O_S}W_0$, and $W$ is isomorphic to $V(\delta)$ Zariski-locally on $S$.

**Proof strategy.** The subgroup $K(\delta)^D$ is diagonalizable, so a representation of it is nothing but a grading by its character group $K(\delta)$; this replaces the averaging idempotents of the classical argument by an operation available over any base. The subgroup $K(\delta)$ then permutes the graded pieces simply transitively, because the commutation relation in the Heisenberg group is exactly a shift of weights. A module with a transitive shift on its grading is induced from its weight-zero piece, which is the assertion.

**Proof.** The homomorphism $\chi\mapsto(1,0,\chi)$ is a closed immersion of group schemes $K(\delta)^D\hookrightarrow\mathcal G(\delta)$, since the cocycle in (9A.1) is trivial on that subgroup. The group $K(\delta)^D$ is the Cartier dual of the constant group $K(\delta)$, hence diagonalizable with character group $K_0=\bigoplus_i\mathbf Z/d_i\mathbf Z$, and a representation of a diagonalizable group scheme on a module is precisely a grading of that module by its character group, the invariants being the piece of weight zero (Book 27 §19.4). So

$$
W=\bigoplus_{y\in K_0}W_y,
\qquad
(1,0,\chi)\cdot w=\chi(y)\,w\ \ \text{for }w\in W_y,
$$

with each $W_y$ a direct summand, hence finite locally free, and $W_0$ the invariants.

Next, the identity $(1,0,\chi)(1,x,1)=\chi(x)^{-1}(1,x,1)(1,0,\chi)$, which is a direct consequence of (9A.1), shows that for $w\in W_y$ the element $(1,x,1)\cdot w$ satisfies $(1,0,\chi)\cdot\bigl((1,x,1)w\bigr)=\chi(y-x)(1,x,1)w$; that is,

$$
(1,x,1):W_y\xrightarrow{\ \sim\ }W_{y-x},
$$

an isomorphism because $(1,-x,1)$ is inverse to it, the product $(1,x,1)(1,-x,1)$ being the identity of $\mathcal G(\delta)$. In particular all graded pieces are isomorphic to $W_0$ and $\operatorname{rank}W=d\cdot\operatorname{rank}W_0$.

The map (9A.7) carries $\delta_y\otimes W_0$ isomorphically onto $W_y$, hence is an isomorphism of $\mathcal O_S$-modules. It is equivariant. Indeed, for $w\in W_0$,

$$
(\alpha,x,\chi)\cdot\delta_y=\alpha\chi(y-x)\delta_{y-x}
\ \longmapsto\
\alpha\chi(y-x)\,(1,x-y,1)\cdot w,
$$

while on the other side $(\alpha,x,\chi)(1,-y,1)=(\alpha,x-y,\chi)$ and $(1,x-y,\chi)=\chi(x-y)^{-1}(1,x-y,1)(1,0,\chi)$, so that, using $(1,0,\chi)w=w$,

$$
(\alpha,x,\chi)\cdot\bigl((1,-y,1)w\bigr)=\alpha\,\chi(x-y)^{-1}(1,x-y,1)\cdot w,
$$

which is the same element. The last assertions are immediate: a module of rank $d$ forces $\operatorname{rank}W_0=1$, and a line bundle is trivial Zariski-locally. $\square$

**Corollary 9A.9 (irreducibility and uniqueness).** $\operatorname{End}_{\mathcal G(\delta)}(V(\delta))=\mathcal O_S$, and for any $\mathcal G(\delta)$-module $W$ of central character one the natural map $\operatorname{Hom}_{\mathcal G(\delta)}(V(\delta),W)\to W_0$, $u\mapsto u(\delta_0)$, is an isomorphism. Two $\mathcal G(\delta)$-modules of central character one and of rank $d$ differ by tensoring with a line bundle, and are locally isomorphic; the isomorphism is unique up to a scalar.

**Proof.** An equivariant $u:V(\delta)\to W$ commutes with $K(\delta)^D$, hence preserves weights, so $u(\delta_0)\in W_0$; and it commutes with $K(\delta)$, so $u(\delta_y)=u((1,-y,1)\delta_0)=(1,-y,1)u(\delta_0)$ is determined by $u(\delta_0)$. Conversely $\Phi$ of (9A.7) turns an element of $W_0$ into an equivariant map. Taking $W=V(\delta)$, whose weight-zero part is $\mathcal O_S\delta_0$, gives $\operatorname{End}_{\mathcal G(\delta)}(V(\delta))=\mathcal O_S$. If $W$ and $W'$ both have rank $d$ then $W\simeq V(\delta)\otimes W_0$ and $W'\simeq V(\delta)\otimes W'_0$ with $W_0,W'_0$ line bundles, whence $W'\simeq W\otimes(W_0^{-1}\otimes W'_0)$; and an isomorphism between them is an element of $\operatorname{Hom}_{\mathcal G(\delta)}(W,W')$, which is the line bundle $W_0^{-1}\otimes W_0'$, so any two differ by a unit. $\square$

The classical form of the argument uses the idempotents $\frac1d\sum_\chi\chi(y)^{-1}\rho(\chi)$ to project onto the weight spaces, and this is legitimate here precisely because $d$ is invertible; the proof above replaces them by the grading attached to a diagonalizable group, which is the same operation stated in a way that needs no division and no enumeration of the characters.

### 9A.7 Theta coordinates on the space of sections

Everything is now in place. The theta group acts on the sections of $L$, and Theorem 8.4 has already measured the rank of that module.

**Theorem 9A.10 (theta coordinates).** Let $\pi:A\to S$ be an abelian scheme and $L$ a relatively ample rigidified line bundle with $\deg\lambda_L=d^2$ of constant type $\delta$, $d$ invertible on $S$. Then:

1. $\pi_*L$ is locally free of rank $d$, its formation commutes with arbitrary base change, and $R^i\pi_*L=0$ for $i>0$.
2. The theta group acts on $\pi_*L$ by
   $$
(x,\varphi)\cdot s=\varphi\bigl(t_x^*s\bigr), \tag{9A.8}
$$
   a $\mathcal G(L)$-module structure whose central $\mathbf G_m$ acts by scalars.
3. Given a theta structure $\Theta:\mathcal G(\delta)\to\mathcal G(L)$, the module $\pi_*L$ becomes a $\mathcal G(\delta)$-module of central character one and of rank $d$, so there is a canonical isomorphism
   $$
\pi_*L\simeq V(\delta)\otimes_{\mathcal O_S}\mathcal N,
\qquad\mathcal N=(\pi_*L)^{\Theta(K(\delta)^D)},
$$
   with $\mathcal N$ a line bundle. Over any open on which $\mathcal N$ is trivialized, the resulting sections $\theta_x$, indexed by $x\in K(\delta)$, form a basis of $\pi_*L$ satisfying
   $$
\Theta(1,x,1)\cdot\theta_y=\theta_{y-x},
\qquad
\Theta(1,0,\chi)\cdot\theta_y=\chi(y)\,\theta_y, \tag{9A.9}
$$
   and they are unique up to multiplication by one common unit.
4. All of this is compatible with base change: for $S'\to S$, the theta structure, the line bundle $\mathcal N$, and the basis pull back to the corresponding data for $(A_{S'},L_{S'})$.

**Proof.** Assertion 1 is Theorem 8.4, the rank being $d$ because the polarization has degree $d^2$.

For assertion 2, let $(x,\varphi)$ be a $T$-point of $\mathcal G(L)$, so $x\in K(L)(T)$ and $\varphi:t_x^*L_T\xrightarrow{\sim}L_T$. Since $t_x$ is an automorphism of $A_T$ over $T$, pullback along it is an isomorphism $\pi_{T*}L_T\to\pi_{T*}t_x^*L_T$, and composing with $\varphi$ gives an $\mathcal O_T$-linear automorphism of $\pi_{T*}L_T=(\pi_*L)\otimes\mathcal O_T$, using the base-change compatibility from assertion 1. This is (9A.8). It is an action: with the multiplication $(x,\varphi)(y,\psi)=(x+y,\varphi\circ t_x^*\psi)$ of the theta group and $t_x^*t_y^*=t_{x+y}^*$,

$$
(x,\varphi)\cdot\bigl((y,\psi)\cdot s\bigr)
=\varphi\bigl(t_x^*\psi(t_x^*t_y^*s)\bigr)
=\bigl(\varphi\circ t_x^*\psi\bigr)\bigl(t_{x+y}^*s\bigr),
$$

which is the action of the product. A central element is a pair $(0,\alpha)$ with $\alpha\in\mathbf G_m$ acting on $L$ by multiplication, and it sends $s$ to $\alpha s$.

Assertion 3 follows: transporting the action along $\Theta$ makes $\pi_*L$ a $\mathcal G(\delta)$-module of central character one, of rank $d$ by assertion 1, and Theorem 9A.8 and Corollary 9A.9 give the canonical isomorphism with $V(\delta)\otimes\mathcal N$, with $\mathcal N$ of rank one. Setting $\theta_y=\Phi(\delta_y\otimes\nu)$ for a generator $\nu$ of $\mathcal N$ yields a basis, and the relations (9A.9) are the formulas (9A.6) for the standard module. Two generators of $\mathcal N$ differ by a unit, whence the stated uniqueness.

Assertion 4 holds because each ingredient commutes with base change: $\pi_*L$ by assertion 1, the theta group and its action by their construction from $L$ and translations, the theta structure by pullback, and the weight decomposition of Theorem 9A.8, which is the base change of a decomposition into direct summands. $\square$

For $g=1$, $\delta=(n)$ with $n\ge3$ invertible, and $L$ the $n$-th power of the bundle attached to the zero section, this produces $n$ sections $\theta_0,\dots,\theta_{n-1}$ of $\pi_*L$, permuted cyclically by the standard $\mathbf Z/n\mathbf Z$ and scaled by $n$-th roots of unity by $\mu_n$: precisely the classical theta functions of level $n$ and the classical Heisenberg relations among them. The content of Theorem 9A.10 is that they exist in a family over any base on which $n$ is invertible, that they are canonical once the theta structure is chosen, and that they are compatible with base change without any further verification.

### 9A.8 What the standard form gives

Three statements should be separated, since they are used differently.

The first is a normal form: over a base on which the degree is invertible, the pair consisting of $K(L)$ and its commutator pairing has, étale-locally, exactly one shape for each type $\delta$, and the theta group itself has exactly one shape (Theorems 9A.4, 9A.5, 9A.6). Nothing beyond the type is remembered by the extension.

The second is a torsor: the identifications with the standard shape form a torsor under a finite étale group scheme of order $d^2|\!\operatorname{Sp}(\delta)|$, extending the symplectic automorphisms of the type by the inner automorphisms of the extension (Theorem 9A.7). Adding a theta structure to a polarized abelian scheme is therefore a finite étale operation: it adds no moduli and destroys no information, and it can always be undone by descending along the torsor.

The third is a rigidity statement for representations: a module on which the theta group acts with the central character normalized is determined by its weight-zero part (Theorem 9A.8, Corollary 9A.9), so a module of rank $d$ is the standard one up to a line bundle. Applied to $\pi_*L$, whose rank was computed to be $d$ in Theorem 8.4, this converts a theta structure into a basis of sections, well defined up to a single global unit and compatible with base change (Theorem 9A.10).

The boundaries are as sharp as the statements. If the type is not constant, one works component by component. If the degree is not invertible on the base, $K(L)$ may fail to be étale, the classification of pairings by elementary divisors is unavailable, and the local model is not unique; the theta group of Section 9.2 and its commutator remain defined, and the descent criterion of Section 9.2 remains valid, but nothing in this chapter applies. Finally, the theta structure is genuinely extra data: two theta structures differing by a nontrivial automorphism give bases of $\pi_*L$ that differ by more than a scalar, and it is the torsor of Theorem 9A.7, not any canonical choice, that measures the difference.

## 10. Extension over normal bases

Arithmetic applications often begin with a homomorphism or polarization on the generic fiber and need it on an integral family. Properness alone extends points over valuation rings, but a rational map from a higher-dimensional normal scheme to a proper scheme can still have codimension-two indeterminacy. The group law and rigidity are what remove that indeterminacy for homomorphisms of abelian schemes.

Throughout this chapter, $S$ is a connected normal noetherian integral scheme with generic point $\eta$, and $A,B$ are abelian schemes over $S$. These hypotheses are stated explicitly because weaker bases require separate extension theorems.

### 10.1 Why normality is the threshold

For a normal noetherian integral scheme,

$$
\mathcal O_S=\bigcap_{s\in S^{(1)}}\mathcal O_{S,s}
$$

inside its function field, and a finite module is controlled by its behavior at codimension-one points together with reflexivity. A homomorphism of abelian schemes has a graph stable under addition, so its closure inherits far more structure than the graph of an arbitrary rational map. Codimension-one extension plus this group structure is the normal-base mechanism.

Normality is also close to necessary. Over a nonnormal base, two branches can carry generic extensions that agree on the common generic point but disagree at the conductor, and a morphism need not descend to the pinched base.

### 10.2 Extension of homomorphisms

**Theorem 10.1 (extension theorem).** Restriction to the generic fiber is an isomorphism

$$
\operatorname{Hom}_S(A,B)
\xrightarrow{\sim}
\operatorname{Hom}_\eta(A_\eta,B_\eta). \tag{10.1}
$$

**Proof strategy.** Uniqueness follows from separatedness and density. For existence, first extend over every height-one local ring, then show that the resulting rational map has no codimension-two indeterminacy. The decisive extra fact is that its graph is a subgroup.

We use two standard consequences of rigidity and spell out why their hypotheses apply.

**DVR extension lemma.** If $R$ is a DVR with fraction field $K$ and $X,Y$ are abelian schemes over $R$, then every homomorphism $X_K\to Y_K$ extends uniquely over $R$.

To prove the lemma, pass faithfully flatly to the strict henselization. Smoothness lifts every special-fiber point of $X$ to a section after an étale localization, while properness extends the image of the generic point of each such section uniquely to a section of $Y$. Apply the same construction after every infinitesimal thickening and on overlaps. The difference between two local extensions is a map from a proper connected group to the vector group attached to $\operatorname{Lie}(Y)$; rigidity makes it zero. Hence the local maps agree and glue. Their additivity holds on the generic fiber, and separatedness extends that equality over $R$. Faithfully flat descent returns the unique map over the original DVR.

The second consequence is the **relative Weil extension lemma**: for abelian schemes $X,Y$ over a normal noetherian integral base, a rational homomorphism $X\dashrightarrow Y$ that is defined over the generic point of the base and over every height-one localization extends everywhere. Here is a convenient proof that does not assume extension for arbitrary proper targets. Fix relative projective embeddings locally on the base. Graphs with the Hilbert polynomial of the generic graph form a locally finite type separated subscheme $\mathscr H$ of the relative Hilbert scheme; the conditions that the first projection be an isomorphism, that the graph contain $(e_X,e_Y)$, and that it be stable under addition are locally closed. Rigidity makes $\mathscr H\to S$ unramified. The DVR extension lemma gives the valuative existence and uniqueness criterion for the closure $Z$ of the generic graph point in $\mathscr H$. Thus $Z\to S$ is proper and quasi-finite, hence finite, and it is birational. Normality of $S$ makes every finite birational map to $S$ an isomorphism. The resulting section of $\mathscr H$ is precisely the required global graph. Notice where the group structure enters: it cuts out the unramified homomorphism locus inside the Hilbert scheme; the analogous locus of arbitrary rational maps need not satisfy the valuative criterion.

Now apply the DVR lemma to $u_\eta$ over every local ring $\mathcal O_{S,s}$ with $s\in S^{(1)}$, and apply the relative Weil extension lemma. This produces $u:A\to B$. The homomorphism identity already holds on the dense generic fiber and therefore holds globally because $B$ is separated and $A\times_SA$ is flat over the integral base. Uniqueness follows in the same way. This proves (10.1). $\square$

The same proof works componentwise if $S$ is normal noetherian with several connected components. It is false that every generic morphism between arbitrary proper smooth schemes extends; translation invariance is essential.

### 10.3 Extension of isogenies

Let $f_\eta:A_\eta\to B_\eta$ be an isogeny of degree $d$. Extend it to $f:A\to B$ by Theorem 10.1. Construct on the generic fiber a quasi-inverse $f'_\eta$ with

$$
f'_\eta f_\eta=[d],
\qquad f_\eta f'_\eta=[d].
$$

Extend $f'_\eta$ as well. Uniqueness gives the same identities over $S$. Hence

$$
\ker f\subseteq A[d].
$$

It follows that $\ker f$ is finite. Every geometric fiber of $f$ is either empty or a translate of the corresponding finite kernel, so $f$ is quasi-finite; properness makes it finite. On every geometric fiber, the identities force the image of $f$ to contain $[d]B_s=B_s$, so $f_s$ is surjective. Proposition 4.1 now supplies flatness and proves:

**Corollary 10.2.** A generic-fiber isogeny between abelian schemes over $S$ extends uniquely to an isogeny. Its degree is constant and equals its generic degree.

The kernel is consequently finite locally free; flatness is a conclusion of the abelian-scheme argument, not a formal property of the schematic closure of an arbitrary finite generic subgroup.

### 10.4 Extension of finite kernels and quotients

Suppose $H_\eta\subseteq A_\eta$ is the kernel of an isogeny to the generic fiber of an abelian scheme $B/S$. Extending the isogeny and taking its kernel gives a unique finite locally free subgroup $H\subseteq A$ with generic fiber $H_\eta$. The quotient theorem identifies

$$
A/H\simeq B.
$$

Over a DVR, one needs no preselected $B$: choose $n$ killing $H_\eta$, close $H_\eta$ inside the finite flat group $A[n]$, and saturate the defining Hopf ideal. Torsion-free finite modules over a DVR are free, so the closure is finite flat. Then $A/H$ is an abelian scheme extending the generic quotient.

Over a higher-dimensional normal base, the raw closure inside $A[n]$ is finite and torsion-free but need not be locally free. Normality alone does not turn every closure into an admissible finite flat subgroup. Corollary 10.2 avoids this problem when the target abelian scheme already exists; otherwise one must prove flatness of the closure separately.

### 10.5 Extension of polarizations

Let $\lambda_\eta:A_\eta\to A_\eta^\vee$ be a polarization. Dual formation commutes with base change, so Theorem 10.1 extends it uniquely to $\lambda:A\to A^\vee$. Symmetry extends because

$$
\lambda^\vee\delta_A=\lambda
$$

holds on the dense generic fiber. The generic map is an isogeny, so Corollary 10.2 makes $\lambda$ an isogeny.

It remains to retain positivity; a symmetric isogeny need not be a polarization. We use the following polarization-locus lemma.

**Polarization-locus lemma.** Let $T$ be connected and let $v:C\to C^\vee$ be a symmetric isogeny of abelian schemes over $T$. If one geometric fiber of $v$ is a polarization, then every geometric fiber is a polarization.

**Proof.** The assertion is local on $T$, so choose a relatively ample bundle $L_0$ and put $v_0=\lambda_{L_0}$. The quasi-endomorphism

$$
\alpha=v_0^{-1}v\in\operatorname{End}(C)\otimes\mathbf Q
$$

is self-adjoint for the Rosati involution defined by $v_0$. On each geometric fiber its roots are real, and $v$ is a polarization exactly when all of them are positive. After multiplying by one integer, $\alpha$ is an actual endomorphism. On every open $T[1/\ell]$, its characteristic polynomial on the $\ell$-adic Tate module has integral coefficients and is locally constant: the endomorphism is global and the Tate module is a locally constant sheaf. These opens, as $\ell$ varies, cover $T$, and the polynomials agree on overlaps because they are the reduced characteristic polynomial of the same endomorphism. The polynomial, and hence its multiset of real roots, is therefore constant on the connected base. None of the roots is zero because $v$ is an isogeny. Their signs cannot change, and positivity on one fiber implies positivity on all fibers. $\square$

Apply the lemma to the extended symmetric isogeny $\lambda$. Its generic fiber lies in the positive chamber, so every fiber does. Proposition 8.1 now proves:

**Corollary 10.3.** A generic polarization extends uniquely as a polarization of $A/S$. A generic principal polarization extends uniquely as a principal polarization.

For the last assertion, the extended degree is the constant generic degree $1$, so the polarization is an isomorphism.

### 10.6 What normality does not guarantee

Three boundaries prevent overuse of the extension theorem.

First, a particular ample line bundle inducing $\lambda_\eta$ need not extend globally. Its polarization homomorphism extends, while the bundle can carry a Picard or Brauer descent obstruction. Fppf locally an inducing ample bundle exists.

Second, a finite generic subgroup inside $A_\eta[n]$ need not have a finite locally free closure over an arbitrary higher-dimensional normal base. A quotient abelian scheme or a separate flatness argument repairs the gap.

Third, if the generic abelian variety has no abelian-scheme model—because it has bad or only semistable reduction—the theorem does not manufacture one. Neron models and semiabelian reduction solve a different extension problem.

## 11. Two-torsion under odd isogenies

The Frey argument uses elliptic curves with three visible nonzero points of order two and then moves within an isogeny class of odd degree. The needed fact is stronger and cleaner than a point count: an odd-degree isogeny identifies the entire two-torsion group schemes. The proof is a Bezout identity inside the isogeny category.

### 11.1 The Bezout mechanism

Let $f:A\to B$ be an isogeny of constant odd degree $d$. Section 6.4 supplies $f':B\to A$ with

$$
f'f=[d]_A,
\qquad ff'=[d]_B. \tag{11.1}
$$

On any group scheme killed by $2$, multiplication by odd $d$ equals the identity because $d=1+2r$ gives

$$
[d]=[1]+[2r]=[1]. \tag{11.2}
$$

Restricting (11.1) to two-torsion therefore makes $f'[2]$ a two-sided inverse to $f[2]$.

The use of $d=\deg f$ is convenient rather than optimal. It suffices that the kernel be killed by some odd integer $m$, for then a quasi-inverse satisfying $f'f=[m]$ gives the same proof.

### 11.2 Preservation of the full two-torsion group scheme

**Theorem 11.1 (odd-isogeny invariance).** For an odd-degree isogeny $f:A\to B$ of abelian schemes over any base,

$$
f[2]:A[2]\xrightarrow{\sim}B[2] \tag{11.3}
$$

is an isomorphism of finite locally free group schemes. The isomorphism is compatible with arbitrary base change and Galois actions on geometric fibers.

**Proof.** Multiplication by $2$ commutes with every homomorphism, so $f$ restricts to $A[2]\to B[2]$, and similarly for $f'$. Equations (11.1)--(11.2) show

$$
f'[2]f[2]=1_{A[2]},
\qquad f[2]f'[2]=1_{B[2]}.
$$

Thus the restrictions are inverse. All ingredients commute with base change. $\square$

This proof includes characteristic two. There $A[2]$ may be connected or nonreduced, so preservation as a group scheme is strictly stronger than any assertion about geometric points.

### 11.3 Rational full two-torsion over a field

Let $K$ be a field of characteristic different from $2$. An abelian variety has **full rational two-torsion** if $A[2]$ is the constant group scheme

$$
\underline{(\mathbf Z/2\mathbf Z)^{2g}}.
$$

Equivalently, every geometric two-torsion point is $K$-rational. If $f:A\to B$ is defined over $K$ and has odd degree, (11.3) is defined over $K$, so $A$ has full rational two-torsion if and only if $B$ does.

In characteristic two, the phrase cannot be defined by demanding $2^{2g}$ rational geometric points: even an ordinary elliptic curve has connected two-torsion. The invariant statement remains the group-scheme isomorphism (11.3).

### 11.4 Elliptic curves and the Frey configuration

Suppose $\operatorname{char}K\ne2$ and

$$
E:y^2=x(x-a)(x+b),
$$

with $0,-b,a$ distinct. Then

$$
O,\quad (0,0),\quad(a,0),\quad(-b,0)
$$

are exactly $E[2](K)$. They form a constant group scheme of order four. If $f:E\to E'$ is any $K$-rational isogeny of odd degree, their images are distinct and exhaust $E'[2](K)$ by (11.3). Thus every elliptic curve reached from this Frey curve by odd isogenies retains full rational two-torsion.

The argument uses neither a Weierstrass equation for $E'$ nor separability of the odd isogeny. In positive characteristic an odd degree can still be divisible by the characteristic, but its kernel is of odd order and remains disjoint from two-torsion in the scheme-theoretic Bezout sense.

### 11.5 Limits of the statement

Even-degree isogenies need not preserve two-torsion. The quotient of an elliptic curve by a rational subgroup of order two kills one nonzero two-torsion point, and the target's remaining two-torsion can acquire a different Galois action. The obstruction is exactly the nontrivial intersection of the kernel with $E[2]$.

Odd isogenies preserve the group scheme $A[2]$, but not a chosen labeling of its nonzero points unless the isogeny is included in the data. Nor do they automatically preserve a chosen principal polarization: the pulled-back polarization changes by the square of the isogeny degree as in (9.3). These distinctions matter in polarized moduli problems even when the underlying two-torsion is unchanged.

## 12. A structural synthesis

The theory developed here turns three kinds of data—line bundles, homomorphisms, and finite group schemes—into interchangeable descriptions when their hypotheses match. The value of the package lies as much in its boundaries as in its formulas: positivity is not mere symmetry, finite is not automatically flat, and geometric points are not a substitute for a group scheme in residue characteristic.

### 12.1 The exact dictionary

For an abelian scheme $A/S$ of relative dimension $g$:

$$
\begin{array}{c|c}
\text{geometric datum}&\text{structural consequence}\\
\hline
\text{rigidified algebraically trivial bundles}&A^\vee\\
\text{Poincare biextension}&A[n]^D\simeq A^\vee[n]\\
\text{relatively ample }L&\lambda_L:A\to A^\vee\text{ a polarization}\\
\text{finite locally free }H\subset A&A/H\text{ and an isogeny}\\
f:A\to B\text{ an isogeny}&\ker f^\vee\simeq(\ker f)^D\\
\text{principal }\lambda&e_n^\lambda\text{ perfect alternating}\\
H\subset A[n]\text{ Lagrangian}&A/H\text{ principally polarized}\\
\mathcal O\text{-action, }M\text{ finite projective}&A\otimes_{\mathcal O}M\text{ an abelian scheme}\\
\ell\text{ invertible, }k\text{ separably closed}&T_\ell A\text{ free of rank }2g\\
L\text{ ample of type }\delta,\ d\text{ invertible}&\pi_*L\text{ the Heisenberg module of rank }d.
\end{array}
$$

The numerical companion is

$$
|A[n]|=n^{2g},\qquad
\deg f=|\ker f|=\deg f^\vee,
$$

$$
\deg(f^*\mu)=(\deg f)^2\deg\mu,
\qquad
|H|\,|H^\perp|=n^{2g}.
$$

Every equality of orders means equality of finite locally free ranks. It remains meaningful when the corresponding geometric point sets are small.

### 12.2 A safe workflow

Given a homomorphism of abelian schemes, first determine whether its kernel is finite. If it is, use the quotient theorem or the fiberwise criterion to establish faithful flatness; do not infer flatness from closedness alone. Given a torsion pairing, identify its adjoint map into a Cartier dual and prove that map is an isomorphism; do not test only geometric points. Given a symmetric homomorphism to the dual, verify positivity before calling it a polarization. Given generic data over a normal base, extend the homomorphism first, then deduce finiteness and positivity; do not assume a chosen inducing line bundle extends.

Given a ring acting on an abelian scheme and a module of coefficients, check that the module is finitely generated projective before writing a tensor product; without projectivity the functor of points is not a sheaf of the right size, and the construction of Section 5.6 has nothing to represent. Given a chosen ample bundle and a desire for coordinates, first check that the degree of its polarization is invertible on the base; only then are the torsion kernel étale, the theta group in standard form, and the sections a Heisenberg module, as in Chapter 9A. Given a tower of prime-power torsion, pass to the limit only where the prime is invertible; in residue characteristic the limit of point groups is the wrong object.

For two-torsion under an odd isogeny, the shortest reliable route is the quasi-inverse relation $f'f=[d]$. On a group killed by two, odd multiplication is the identity, so the restriction is automatically an isomorphism. This argument is insensitive to reduction type and avoids every point-counting trap.

### 12.3 Conclusion

An abelian scheme carries its dual through algebraically trivial rigidified line bundles, and the Poincare bundle makes that duality bilinear. Finite subgroup schemes produce quotient abelian schemes; duality reverses their isogenies and identifies the opposite kernel with the Cartier dual. Multiplication kernels inherit perfect Weil pairings in every characteristic. Ample classes turn these pairings into polarizations, while isotropic descent explains which quotients retain principality. Over a normal noetherian integral base, rigidity extends generic homomorphisms, isogenies, and polarizations without pretending that every line bundle or subgroup closure is automatically well behaved. Odd isogenies identify full two-torsion as a group scheme, providing exactly the stable structure required in the Frey setting.

Three further constructions extend the same principles beyond the core dictionary. A ring acting on an abelian scheme allows its coefficients to be changed: a finitely generated projective module is a direct factor of a free one, the corresponding idempotent cuts a retract out of a power of the abelian scheme, and the retract is again an abelian scheme, dual to the retract cut by the transposed idempotent. Away from a prime that is invertible, the tower of torsion assembles into a free module of rank twice the dimension over the prime-adic integers, on which endomorphisms and Galois act linearly and the Weil pairing remains perfect. And when the degree of a polarization is invertible, its theta group has a single local model, the Heisenberg extension attached to the type; the identifications with that model form a torsor under a finite étale group, the model has essentially one representation, and the sections of the ample bundle are forced to be that representation. Positivity, which began as a property of line bundles, ends as a system of coordinates.
